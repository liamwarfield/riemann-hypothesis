module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwisted

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.WittLow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem exists_repr (hnd : h.Nondegenerate) (f : V →ₗ[K] K) : ∃ w, h w = f := by
  have h0 : (LinearMap.range h).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact hnd.2 v fun x => hv _ ⟨x, rfl⟩
  have h1 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h)
  rw [h0, Submodule.dualAnnihilator_bot] at h1
  have : f ∈ LinearMap.range h := by rw [← h1]; trivial
  exact this

theorem mem_of_orth (hs : h.IsSymm) (hnd : h.Nondegenerate) (I : Submodule K V) (v : V)
    (hv : ∀ x, (∀ y ∈ I, h y x = 0) → h x v = 0) : v ∈ I := by
  by_contra hn
  obtain ⟨f, hf, hI⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨w, rfl⟩ := exists_repr hnd f
  refine hf (hv w fun y hy => ?_)
  have : h w y = 0 := by
    have : h w y ∈ I.map (h w) := ⟨y, hy, rfl⟩
    rwa [hI] at this
  rw [← hs.eq w y, this, map_zero]

theorem finrank_orth (hs : h.IsSymm) (hnd : h.Nondegenerate) {i : ℕ} (e : Fin i → V) (he : LinearIndependent K e) :
    i + Module.finrank K (LinearMap.ker (LinearMap.pi fun j => h (e j))) = Module.finrank K V := by
  have hsurj : LinearMap.range (LinearMap.pi fun j => h (e j)) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨f, hf⟩ := LinearMap.exists_extend ((Module.Basis.span he).constr K fun j => star (c j))
    obtain ⟨w, rfl⟩ := exists_repr hnd f
    refine ⟨w, funext fun j => ?_⟩
    have h1 := LinearMap.congr_fun hf (Module.Basis.span he j)
    rw [Module.Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply] at h1
    rw [LinearMap.pi_apply, ← hs.eq w (e j), h1]
    exact star_star _
  have := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun j => h (e j))
  rw [hsurj, finrank_top] at this
  simpa using this

end Lin

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E]


omit [NumberField E] in
theorem mem_dual {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 E) E) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem exists_lower (hst : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (V : HSpace E) {i : ℕ} (e : Fin i → V.V)
    (he : LinearIndependent E e) (hiso : ∀ a b, V.hT (e a) (e b) = 0) :
    ∃ (V' : HSpace E) (ι : V'.V →ₗ[E] V.V), V'.rank + 2 * i = V.rank ∧ HSpace.IsIsomEmb V' V ι ∧
      ∀ x a, V.hT (ι x) (e a) = 0 := by
  have hs := V.herm
  have hnd := V.nondeg
  have hfg : V.L0.FG := V.standardTuple_isLattice.fg
  have hst1 : ∀ x : E, x ∈ (1 : Submodule (𝓞 E) E) → star x ∈ (1 : Submodule (𝓞 E) E) := by
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
    exact Submodule.mem_one.2 ⟨⟨_, hst _ r.2⟩, rfl⟩
  have hL : ∀ x, x ∈ V.L0 ↔ ∀ y ∈ V.L0, V.hT y x ∈ (1 : Submodule (𝓞 E) E) := fun x => by
    rw [← mem_dual, V.baseLattice_isUnimodular]
  have hsp : Submodule.span E (V.L0 : Set V.V) = ⊤ := by
    by_contra hn
    obtain ⟨v, hv⟩ : ∃ v : V.V, v ∉ Submodule.span E (V.L0 : Set V.V) := by
      by_contra h
      apply hn
      apply eq_top_iff.mpr
      intro x _
      exact not_not.mp (fun hx => h ⟨x, hx⟩)
    obtain ⟨f, hf, hfL⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
    obtain ⟨w, hw⟩ := exists_repr hnd f
    have hw0 : w ≠ 0 := by
      intro h
      apply hf
      rw [← hw, h, map_zero]
      rfl
    have hsmul (a : E) : a • w ∈ V.L0 := by
      rw [hL]
      intro y hy
      have hy0 : f y = 0 := by
        have : f y ∈ (Submodule.span E (V.L0 : Set V.V)).map f :=
          ⟨y, Submodule.subset_span hy, rfl⟩
        simpa [hfL] using this
      rw [map_smul, ← hs.eq w y, hw, hy0, map_zero, smul_zero]
      exact Submodule.zero_mem _
    let j : E →ₗ[𝓞 E] V.L0 :=
      ((LinearMap.toSpanSingleton E V.V w).restrictScalars (𝓞 E)).codRestrict V.L0 hsmul
    letI : Module.Finite (𝓞 E) V.L0 := Module.Finite.iff_fg.mpr hfg
    letI : Module.Finite (𝓞 E) E := Module.Finite.of_injective j fun a b hab =>
      smul_left_injective E hw0 (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  set I : Submodule E V.V := Submodule.span E (Set.range e) with hI
  set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (e j)) with hPdef
  have hP : ∀ x, x ∈ P ↔ ∀ y ∈ I, V.hT y x = 0 := by
    intro x
    constructor
    · intro hx y hy
      have : I ≤ LinearMap.ker (V.hT.flip x) := by
        rw [hI, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact congrFun hx j
      exact this hy
    · intro hx
      exact funext fun j => hx _ (Submodule.subset_span ⟨j, rfl⟩)
  have hIP : I ≤ P := by
    rw [hI, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact funext fun a => hiso a j
  have hPI : ∀ x ∈ P, ∀ y ∈ I, V.hT x y = 0 := fun x hx y hy => by
    rw [← hs.eq y x, (hP x).1 hx y hy, map_zero]
  obtain ⟨σ, σI, σid, σL⟩ := GlobalTheory.ColPeriodCompare.exists_proj V.L0 hfg hsp I
  obtain ⟨π, πP, πid, πL⟩ := GlobalTheory.ColPeriodCompare.exists_proj V.L0 hfg hsp P
  set W : Submodule E V.V := P ⊓ LinearMap.ker σ with hW
  have hsub : ∀ z ∈ P, z - σ z ∈ W := fun z hz =>
    ⟨P.sub_mem hz (hIP (σI z)), by
      change σ (z - σ z) = 0
      rw [map_sub, σid _ (σI z), sub_self]⟩
  have hsup : I ⊔ W = P := by
    refine le_antisymm (sup_le hIP inf_le_left) fun z hz => ?_
    rw [← add_sub_cancel (σ z) z]
    exact Submodule.add_mem_sup (σI z) (hsub z hz)
  have hinf : I ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨h1, -, h2⟩
    rw [Submodule.mem_bot, ← σid z h1]
    exact h2
  have hrk : Module.finrank E W + 2 * i = V.rank := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq I W
    have h2 := finrank_orth hs hnd e he
    have h3 : Module.finrank E I = i := by rw [hI, finrank_span_eq_card he, Fintype.card_fin]
    rw [hsup, hinf, finrank_bot, h3] at h1
    rw [← hPdef, V.rank_eq] at h2
    omega

  have hWz : ∀ v ∈ W, ∀ z ∈ P, V.hT z v = V.hT (z - σ z) v := fun v hv z hz => by
    rw [map_sub, LinearMap.sub_apply, (hP v).1 hv.1 _ (σI z), sub_zero]
  have hrad : ∀ v : W, (∀ y : W, V.hT y v = 0) → v = 0 := by
    intro v hv
    have : (v : V.V) ∈ I := mem_of_orth hs hnd I v fun x hx => by
      rw [hWz v v.2 x ((hP x).2 hx)]
      exact hv ⟨_, hsub x ((hP x).2 hx)⟩
    have h2 : (v : V.V) ∈ I ⊓ W := ⟨this, v.2⟩
    rw [hinf] at h2
    exact Subtype.ext h2
  have hden : ∀ v : V.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ V.L0 := by
    intro v
    have hv : v ∈ Submodule.span E (V.L0 : Set V.V) := by rw [hsp]; trivial
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (V.L0 : Set V.V) v hv
    rw [Submodule.span_eq] at hd
    exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩
  let h' : W →ₗ⋆[E] W →ₗ[E] E := V.hT.domRestrict₁₂ W W
  have hh : ∀ x y : W, h' x y = V.hT x y := fun _ _ => rfl
  let j : W →ₗ[𝓞 E] V.V := W.subtype.restrictScalars (𝓞 E)
  let L' : Submodule (𝓞 E) W := V.L0.comap j
  have hL' : ∀ x : W, x ∈ L' ↔ (x : V.V) ∈ V.L0 := fun _ => Iff.rfl
  have hlat : Submodule.IsLattice E L' := by
    apply Submodule.IsLattice.of_fg E
    refine Submodule.fg_of_fg_map_injective j Subtype.val_injective ?_
    exact hfg.of_le (Submodule.map_comap_le _ _)
  have hun : Formalism.HermitianLatticesTheory.IsUnimodular h' L' := by
    ext v
    rw [mem_dual]
    refine ⟨fun hv => ?_, fun hv y hy => (hL _).1 hv _ hy⟩
    obtain ⟨w, hw⟩ := exists_repr hnd (V.hT v ∘ₗ π)
    have hw' : ∀ z, V.hT w z = V.hT v (π z) := fun z => LinearMap.congr_fun hw z
    have hwL : w ∈ V.L0 := by
      rw [hL]
      intro y hy
      rw [← hs.eq w y, hw', starRingEnd_apply, ← starRingEnd_apply, hs.eq, hWz v v.2 _ (πP y)]
      exact hv ⟨_, hsub _ (πP y)⟩ (V.L0.sub_mem (πL y hy) (σL _ (πL y hy)))
    have hwv : w - v ∈ I := mem_of_orth hs hnd I _ fun x hx => by
      rw [← hs.eq, map_sub, LinearMap.sub_apply, hw', πid x ((hP x).2 hx), sub_self, map_zero]
    have h1 := σid _ hwv
    rw [map_sub, show σ v = 0 from v.2.2, sub_zero] at h1
    rw [hL', show (v : V.V) = w - σ w by rw [h1]; abel]
    exact V.L0.sub_mem hwL (σL w hwL)
  have hs' : h'.IsSymm := ⟨fun x y => hs.eq _ _⟩
  have hnd' : h'.Nondegenerate := ⟨fun x hx => hrad x fun y => by
    rw [← hs.eq, ← hh, hx, map_zero], fun x hx => hrad x hx⟩
  exact ⟨⟨W, h', hs', hnd', Module.finrank E W, rfl, Module.finBasis E W, fun _ => (0, 0), L', hlat, hun⟩, W.subtype,
    hrk, fun _ _ => rfl, fun x a => hPI _ x.2.1 _ (Submodule.subset_span ⟨a, rfl⟩)⟩

end Lat

variable {D : D7}

theorem exists_sig (V : HSp D) (τ : D.host.E →+* ℂ) : ∃ s : ℕ × ℕ, Formalism.UG.HasSignature (V.gram.map τ) s.1 s.2 := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ (V.gram.map τ) (by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, HSpace.gram]
    rw [← hτ]
    exact congrArg τ (V.herm.eq _ _)) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero]
    exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))
  exact ⟨(p, q), h⟩

theorem wittLowEx : ∀ D : D7, WittLowEx D := by
  rintro D V i ⟨C, hC⟩
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj V C
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp V.frame.equivFun.toLinearMap hC.1
  have hiso : ∀ a b, V.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hC.2]; rfl
  obtain ⟨V', ι, h1, h2, h3⟩ := exists_lower Examples₂.star_isIntegral V e he hiso
  choose s hs using exists_sig (D := D) V'
  refine ⟨{ V' with sig := s }, ⟨h1, ι, h2, _, hC, ?_⟩, hs⟩
  refine Matrix.ext fun a b => ?_
  rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
  exact h3 _ _

end GlobalTheory.WittLow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdAdelicChar

section General

variable (F : Type) [Field F] [NumberField F]

def ratChar (x : F) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))

theorem ratChar_add (x y : F) : ratChar F (x + y) = ratChar F x * ratChar F y := by
  rw [ratChar, ratChar, ratChar, ← Complex.exp_add, map_add (f := _)]
  congr 1
  push_cast
  ring

theorem ratChar_zero : ratChar F 0 = 1 := by simp [ratChar]

theorem norm_ratChar (x : F) : ‖ratChar F x‖ = 1 := by
  have := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((Algebra.trace ℚ F x : ℚ) : ℝ))
  rw [← this, ratChar]
  congr 2
  push_cast
  ring

theorem ratChar_integer (r : 𝓞 F) : ratChar F (r : F) = 1 := by
  have h : IsIntegral ℤ (Algebra.trace ℚ F (r : F)) := Algebra.isIntegral_trace r.isIntegral_coe
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [ratChar, ← hk, eq_intCast, Rat.cast_intCast, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem ratChar_of_integral (x : F)
    (h : ∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F) : ratChar F x = 1 := by
  have hx := (GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h
  rw [GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F),
    FractionalIdeal.mem_one_iff] at hx
  obtain ⟨r, rfl⟩ := hx
  exact ratChar_integer F r

theorem exists_finChar : ∃ χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ, Continuous χ ∧ (∀ y, ‖χ y‖ = 1) ∧
    ∀ x : F, χ (algebraMap F _ x) = ratChar F x := by
  choose e s hs he using GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos
  simp only [one_smul] at he
  have key : ∀ (y : FiniteAdeleRing (𝓞 F) F) (a : F) (w : FiniteAdeleRing (𝓞 F) F),
      (∀ v, w v ∈ v.adicCompletionIntegers F) → y = algebraMap F _ a + w → ratChar F (e y) = ratChar F a := by
    intro y a w hw h
    have h2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (e y - a) = w - s y := by
      rw [map_sub]
      linear_combination h - he y
    have h3 := ratChar_of_integral F (e y - a) fun v => by
      rw [h2]; exact sub_mem (hw v) (hs y v)
    rw [show e y = a + (e y - a) by ring, ratChar_add, h3, mul_one]
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    { toFun := fun y => ratChar F (e y)
      map_zero_eq_one' := (key 0 0 0 (fun v => zero_mem _) (by simp)).trans (ratChar_zero F)
      map_add_eq_mul' := fun x y => by
        rw [← ratChar_add]
        refine key _ _ (s x + s y) (fun v => add_mem (hs x v) (hs y v)) ?_
        rw [map_add (f := _)]
        linear_combination he x + he y }
  refine ⟨χ, ?_, fun y => norm_ratChar F _, fun x => key _ x 0 (fun v => zero_mem _) (add_zero _).symm⟩
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hc : Continuous fun z : FiniteAdeleRing (𝓞 F) F => z - y := continuous_id.sub continuous_const
  have hU := ((GlobalTheory.AdLat.OpenLat.isOpen_integral F).preimage hc).mem_nhds (x := y) (by
    intro v
    simp only [sub_self]
    exact zero_mem _)
  refine (continuousAt_const (y := χ y)).congr (Filter.mem_of_superset hU fun z hz => ?_)
  refine (key z (e y) (s y + (z - y)) (fun v => add_mem (hs y v) (hz v)) ?_).symm
  linear_combination he y

theorem exists_char_of_trace (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ)) :
    ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
      ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) := by
  obtain ⟨χ, hc, hn, hr⟩ := exists_finChar F
  have him : ∀ x, (L x).im = 0 := by
    have : (fun x => (L x).im) = fun _ => (0 : ℝ) := by
      refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer (Complex.continuous_im.comp hL)
        continuous_const ?_
      funext x
      show (L (algebraMap F _ x)).im = 0
      rw [hT, Complex.ratCast_im]
    exact congrFun this
  let ψ : AddChar (AF F) ℂ :=
    { toFun := fun a => Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F a)) * χ (sndA F a)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by
        rw [map_add (f := _), map_add (f := _), map_add (f := _), mul_add, Complex.exp_add, AddChar.map_add_eq_mul]
        ring }
  have hinf : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) := fun x => by
    show Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) * χ 0 = _
    rw [AddChar.map_zero_eq_one, mul_one]
  refine ⟨ψ, ⟨?_, fun a => ?_, fun a => ?_, ?_⟩, hinf⟩
  · exact (Complex.continuous_exp.comp (continuous_const.mul (hL.comp continuous_fst))).mul
      (hc.comp continuous_snd)
  · show ‖Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F a)) * χ (sndA F a)‖ = 1
    rw [norm_mul, hn, mul_one, Complex.norm_exp]
    simp [him]
  · show Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F (algebraMap F _ a))) *
      χ (sndA F (algebraMap F _ a)) = 1
    rw [AlgHom.commutes, AlgHom.commutes, hT, hr, ratChar, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  · have hd : ((Module.finrank ℚ F : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    refine ⟨pairA F (algebraMap F _ (algebraMap ℚ F (-(1 / 2) / (Module.finrank ℚ F : ℚ)))) 0, ?_⟩
    have h := hinf (algebraMap F _ (algebraMap ℚ F (-(1 / 2) / (Module.finrank ℚ F : ℚ))))
    rw [hT, Algebra.trace_algebraMap, nsmul_eq_mul, mul_div_cancel₀ _ hd, psiInf] at h
    have e : 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ((-(1 / 2) : ℚ) : ℂ) = Real.pi * Complex.I := by
      push_cast
      ring
    rw [h, e, Complex.exp_pi_mul_I]
    norm_num

end General

theorem exists_isStdChar : ∀ D : D7, ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) := by
  intro D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let L : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))) fun a b => by
    simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
  obtain ⟨ψ, h1, h2⟩ := exists_char_of_trace D.host.F L (continuous_finsetSum _ fun ρ _ => (hθ ρ).2) fun x => by
    show ∑ ρ, θ ρ (algebraMap D.host.F (Ainf D.host.F) x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace]
  refine ⟨ψ, h1, ⟨θ, hθ⟩, fun θ' hθ' x => ?_⟩
  rw [h2, GlobalTheory.DualPairCompare.sum_infFam θ' hθ', ← GlobalTheory.DualPairCompare.sum_infFam θ hθ]
  rfl

end GlobalTheory.StdAdelicChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.HeckeExp

variable {D : D7}


open Classical in
theorem exists_idele_at {θ : InfF D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1,
      by rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := by
    rw [← sub_eq_zero]
    refine hσ.ext _ (by rw [RingHom.map_sub, RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul, sub_self]) fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one,
      sub_eq_zero]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem arg_ne_zero (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : (AE D)ˣ) :
    θ (infPart D (x : AE D)) / (‖θ (infPart D (x : AE D))‖ : ℂ) ≠ 0 := by
  have h : θ (infPart D (x : AE D)) ≠ 0 := ((x.isUnit.map (infPart D)).map θ).ne_zero
  exact div_ne_zero h (by exact_mod_cast norm_ne_zero_iff.2 h)

theorem eq_of_zpow_eq {n m : ℤ} (h : ∀ w : ℂ, ‖w‖ = 1 → w ^ n = w ^ m) : n = m := by
  by_contra hne
  have hd : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have h1 := h (Complex.exp ((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I _)
  have h2 : Complex.exp ((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) * Complex.I) ^ (n - m) = 1 := by
    rw [zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  have hd' : ((n - m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have e : ((n - m : ℤ) : ℂ) * (((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
    rw [Complex.ofReal_div, Complex.ofReal_intCast]; field_simp
  rw [← Complex.exp_int_mul, e, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem hasInfExp_unique {χ : IdC D} {τ : D.what₂.Tau} {a a' : ℚ} (h : HasInfExp D χ τ a) (h' : HasInfExp D χ τ a') :
    a = a' := by
  obtain ⟨n, hn, ⟨θ, hθ⟩, h1⟩ := h
  obtain ⟨m, hm, -, h2⟩ := h'
  have e : n = m := eq_of_zpow_eq fun w hw => by
    obtain ⟨x, hx1, hx2⟩ := exists_idele_at hθ τ w (by rintro rfl; simp at hw)
    have ho : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' hτ => by rw [hx2, if_neg hτ]
    have e1 := h1 θ hθ x hx1 ho
    have e2 := h2 θ hθ x hx1 ho
    rw [hx2, if_pos rfl, hw, Complex.ofReal_one, div_one] at e1 e2
    exact e1.symm.trans e2
  subst e
  linarith

theorem hasInfExp_mul {χ χ' : IdC D} {τ : D.what₂.Tau} {a a' : ℚ} (h : HasInfExp D χ τ a) (h' : HasInfExp D χ' τ a') :
    HasInfExp D (χ * χ') τ (a + a') := by
  obtain ⟨n, hn, h0, h1⟩ := h
  obtain ⟨m, hm, -, h2⟩ := h'
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, h0, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h1 θ hθ x hx hτ, h2 θ hθ x hx hτ, zpow_add₀ (arg_ne_zero _ x)]

theorem hasInfExp_inv {χ : IdC D} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ τ a) : HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, h0, h1⟩ := h
  refine ⟨-n, by push_cast; rw [hn]; ring, h0, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, h1 θ hθ x hx hτ, _root_.zpow_neg]

def hcSubgroup (D : D7) : Subgroup (IdC D) where
  carrier := {χ | IsHC D χ}
  one_mem' := isHC_one D
  mul_mem' := fun {χ χ'} h h' =>
    ⟨⟨h.1.1.mul h'.1.1, fun x => by rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]⟩, fun τ =>
      (h.2 τ).elim fun _ ha => (h'.2 τ).elim fun _ ha' => ⟨_, hasInfExp_mul ha ha'⟩⟩
  inv_mem' := fun {χ} h =>
    ⟨⟨h.1.1.inv, fun x => by rw [MonoidHom.inv_apply, h.1.2, inv_one]⟩, fun τ =>
      (h.2 τ).elim fun _ ha => ⟨_, hasInfExp_inv ha⟩⟩

theorem hecke_exp_laws : ∀ D : D7, (∃ C : Subgroup (IdC D), ∀ χ, χ ∈ C ↔ IsHC D χ) ∧
    (∀ (χ : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ τ a' → a = a') ∧
    ∀ (χ χ' : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ' τ a' → HasInfExp D (χ * χ') τ (a + a') :=
  fun D => ⟨⟨hcSubgroup D, fun _ => Iff.rfl⟩, fun _ _ _ _ => hasInfExp_unique, fun _ _ _ _ _ => hasInfExp_mul⟩

end GlobalTheory.Mem.HeckeExp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_infinityExponent_group_laws : ∀ D : D7, (∃ C : Subgroup (IdC D), ∀ χ, χ ∈ C ↔ IsHC D χ) ∧ (∀ (χ : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ τ a' → a = a') ∧ ∀ (χ χ' : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ' τ a' → HasInfExp D (χ * χ') τ (a + a') := by
  first | exact @GlobalTheory.Mem.HeckeExp.hecke_exp_laws | exact GlobalTheory.Mem.HeckeExp.hecke_exp_laws | (intros; apply GlobalTheory.Mem.HeckeExp.hecke_exp_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.AdeleCharTwist

theorem exists_eq_exp (g : ℝ → ℂ) (hc : Continuous g) (hn : ∀ t, ‖g t‖ = 1) (h0 : g 0 = 1)
    (hadd : ∀ s t, g (s + t) = g s * g t) :
    ∃ c : ℝ, ∀ t : ℝ, g t = Complex.exp (2 * Real.pi * Complex.I * ((c * t : ℝ) : ℂ)) := by
  have hm : ∀ a, g a ∈ Submonoid.unitSphere ℂ := fun a => by simpa [Submonoid.unitSphere] using hn a
  let χ : C(ℝ, Circle) := ⟨fun a => ⟨g a, hm a⟩, hc.subtype_mk hm⟩
  have hχ : ∀ s t, χ (s + t) = χ s * χ t := fun s t => Subtype.ext (hadd s t)
  obtain ⟨L, ⟨hL0, hL⟩, hu⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts χ 0 0
    (by rw [Circle.exp_zero]; exact Subtype.ext h0.symm)
  have hL' : ∀ t, Circle.exp (L t) = χ t := congrFun hL
  have hLa : ∀ s t, L (s + t) = L s + L t := fun s t => by
    have := hu ⟨fun t => L (s + t) - L s, by fun_prop⟩ ⟨by simp, by
      funext t
      show Circle.exp (L (s + t) - L s) = χ t
      rw [Circle.exp_sub, hL', hL', hχ, mul_div_cancel_left]⟩
    have h2 : L (s + t) - L s = L t := DFunLike.congr_fun this t
    linarith
  let l : ℝ →+ ℝ := AddMonoidHom.mk' L hLa
  refine ⟨L 1 / (2 * Real.pi), fun t => ?_⟩
  have h3 : L t = t * L 1 := by
    have := map_real_smul l L.continuous t 1
    simpa [l] using this
  have h4 : g t = (Circle.exp (L t) : ℂ) := by rw [hL']; rfl
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h4, Circle.coe_exp, h3]
  congr 1
  push_cast
  field_simp

variable {F : Type} [Field F] [NumberField F]

theorem pairA_add (x x' : Ainf F) (y y' : Af F) :
    pairA F (x + x') (y + y') = pairA F x y + pairA F x' y' := rfl

theorem algebraMap_eq_pairA (x : F) :
    algebraMap F (AF F) x = pairA F (algebraMap F _ x) 0 + pairA F 0 (algebraMap F _ x) := by
  rw [← pairA_add, add_zero, zero_add]
  rfl

theorem denseRange_fin : DenseRange (algebraMap F (Af F)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hc : Continuous fun z : Af F => y - z := continuous_const.sub continuous_id
  have hV : (fun z : Af F => y - z) ⁻¹' U ∈ 𝓝 (0 : Af F) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y
  refine ⟨y - N • β, hNU β hβ, a, ?_⟩
  rw [e, add_sub_cancel_right]

theorem ext_of_inf {ψ ψ' : AF F → ℂ} (hc : Continuous ψ) (hc' : Continuous ψ')
    (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (ha' : ∀ x y, ψ' (x + y) = ψ' x * ψ' y)
    (hr : ∀ a : F, ψ (algebraMap F _ a) = 1) (hr' : ∀ a : F, ψ' (algebraMap F _ a) = 1)
    (h : ∀ a : F, ψ (pairA F (algebraMap F _ a) 0) = ψ' (pairA F (algebraMap F _ a) 0)) (x : AF F) :
    ψ x = ψ' x := by
  have h1 : (fun z => ψ (pairA F z 0)) = fun z => ψ' (pairA F z 0) :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      (hc.comp (continuous_id.prodMk continuous_const)) (hc'.comp (continuous_id.prodMk continuous_const))
      (funext h)
  have h2 : (fun z => ψ (pairA F 0 z)) = fun z => ψ' (pairA F 0 z) :=
    denseRange_fin.equalizer
      (hc.comp (continuous_const.prodMk continuous_id)) (hc'.comp (continuous_const.prodMk continuous_id))
      (funext fun a => by
        have e := hr a
        have e' := hr' a
        rw [algebraMap_eq_pairA, ha, h] at e
        rw [algebraMap_eq_pairA, ha'] at e'
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e) (e.trans e'.symm))
  have e : x = pairA F x.1 0 + pairA F 0 x.2 := by
    rw [← pairA_add, add_zero, zero_add]
    rfl
  rw [e, ha, ha', congrFun h1, congrFun h2]

theorem exists_nsmul_inf {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ N : ℕ, 0 < N ∧ ∀ r : 𝓞 F, ψ (pairA F (algebraMap F _ ((N : F) * r)) 0) = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (GlobalTheory.FinTranslate.ker_mem_nhds hψ.1 hψ.2.1)
  refine ⟨N, hN, fun r => ?_⟩
  have h1 : ψ (pairA F 0 (N • algebraMap F (Af F) r)) = 1 :=
    h _ fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v r
  have h2 := hψ.2.2.1 ((N : F) * r)
  rw [nsmul_eq_mul, ← map_natCast (algebraMap F (Af F)), ← map_mul] at h1
  rwa [algebraMap_eq_pairA, AddChar.map_add_eq_mul, h1, mul_one] at h2

theorem exists_realHom [IsTotallyReal F] : ∃ ρ : ℝ →+* Ainf F, Continuous ρ := by
  let e : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  exact ⟨Pi.ringHom fun w => (e w).symm.toRingHom, continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous⟩

theorem exists_trace [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ a : F, ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ)) := by
  classical
  obtain ⟨N, hN, hNr⟩ := exists_nsmul_inf hψ
  obtain ⟨ρ, hρ⟩ := exists_realHom (F := F)
  have hρq : ∀ q : ℚ, ρ (q : ℝ) = algebraMap F (Ainf F) (q : F) := fun q =>
    RingHom.congr_fun (RingHom.ext_rat (ρ.comp (Rat.castHom ℝ)) ((algebraMap F (Ainf F)).comp (Rat.castHom F))) q
  have hadd : ∀ x y : Ainf F, ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0) := fun x y => by
    rw [← AddChar.map_add_eq_mul, ← pairA_add, add_zero]
  have h0 : ψ (pairA F 0 0) = 1 := ψ.map_zero_eq_one
  have key : ∀ r : 𝓞 F, ∃ c : ℚ, ∀ q : ℚ, ψ (pairA F (algebraMap F _ (q • (r : F))) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((q * c : ℚ) : ℂ)) := fun r => by
    obtain ⟨c, hc⟩ := exists_eq_exp (fun t => ψ (pairA F (ρ t * algebraMap F _ (r : F)) 0))
      (hψ.1.comp ((hρ.mul continuous_const).prodMk continuous_const)) (fun t => hψ.2.1 _)
      (by simp only [map_zero, zero_mul, h0]) (fun s t => by simp only [map_add (f := _), add_mul, hadd])
    have hq : ∀ q : ℚ, ψ (pairA F (algebraMap F _ ((q : F) * (r : F))) 0) =
        Complex.exp (2 * Real.pi * Complex.I * ((c * q : ℝ) : ℂ)) := fun q => by
      rw [← hc, hρq, map_mul]
    have h1 := hq N
    rw [Rat.cast_natCast, hNr, eq_comm, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero] at hn
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    refine ⟨n / N, fun q => ?_⟩
    rw [Rat.smul_def, hq]
    congr 2
    push_cast at hn ⊢
    rw [← hn]
    field_simp
  choose c hc using key
  let b := integralBasis F
  let φ : F →ₗ[ℚ] ℚ := b.constr ℚ fun i => c (RingOfIntegers.basis F i)
  obtain ⟨a, ha⟩ := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).surjective φ
  have ha' : ∀ x, Algebra.trace ℚ F (a * x) = φ x := fun x => by
    rw [← ha]; rfl
  refine ⟨a, fun x => ?_⟩
  rw [ha', ← b.sum_repr x]
  refine Finset.sum_induction _ (fun y : F => ψ (pairA F (algebraMap F _ y) 0) =
    Complex.exp (2 * Real.pi * Complex.I * ((φ y : ℚ) : ℂ))) (fun y z hy hz => ?_) ?_ fun i _ => ?_
  · rw [map_add (f := _), hadd, hy, hz, map_add (f := _), ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [map_zero, h0, Rat.cast_zero, mul_zero, Complex.exp_zero]
  · rw [map_smul φ, Module.Basis.constr_basis, smul_eq_mul, ← hc, integralBasis_apply]

theorem trace_mul_ne_zero {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) {a : F}
    (h : ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ))) : a ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hψ.2.2.2
  refine hx (ext_of_inf (ψ' := fun _ => 1) hψ.1 continuous_const ψ.map_add_eq_mul (fun _ _ => by simp)
    hψ.2.2.1 (fun _ => rfl) (fun y => by simp [h]) x)

theorem exists_mul_eq : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ ψ' : AddChar (AF F) ℂ), IsCharAF F ψ → IsCharAF F ψ' → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  intro F _ _ _ ψ ψ' hψ hψ'
  obtain ⟨a, ha⟩ := exists_trace hψ
  obtain ⟨a', ha'⟩ := exists_trace hψ'
  have h0 := trace_mul_ne_zero hψ ha
  refine ⟨a' / a, div_ne_zero (trace_mul_ne_zero hψ' ha') h0, ?_⟩
  refine ext_of_inf hψ'.1 (hψ.1.comp (continuous_const.mul continuous_id)) ψ'.map_add_eq_mul
    (fun x y => by rw [mul_add, ψ.map_add_eq_mul]) hψ'.2.2.1 (fun x => by rw [← map_mul, hψ.2.2.1]) fun x => ?_
  have e : algebraMap F (AF F) (a' / a) * pairA F (algebraMap F _ x) 0 =
      pairA F (algebraMap F _ (a' / a * x)) 0 :=
    Prod.ext (map_mul (algebraMap F (Ainf F)) _ _).symm (mul_zero _)
  rw [e, ha, ha', ← mul_assoc, mul_div_cancel₀ _ h0]

end GlobalTheory.AdeleCharTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyRealStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ ψ' : AddChar (AF F) ℂ), IsCharAF F ψ → IsCharAF F ψ' → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  first | exact @GlobalTheory.AdeleCharTwist.exists_mul_eq | exact GlobalTheory.AdeleCharTwist.exists_mul_eq | (intros; apply GlobalTheory.AdeleCharTwist.exists_mul_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.Mem.ThetaClosed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilTieCheck GlobalTheory.FockCompare

variable {D : D7}

theorem exists_open_ker {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {ψ : AddChar (AF D.host.F) ℂ} (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (φ : G →+ AF D.host.F)
    (hφ : Continuous φ) :
    ∃ K : AddSubgroup G, IsOpen (K : Set G) ∧ ∀ w ∈ K, fstA D.host.F (φ w) = 0 → ψ (φ w) = 1 := by
  let q : G →+ AF D.host.F :=
    (AddMonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp ((AddMonoidHom.snd (Ainf D.host.F) (Af D.host.F)).comp φ)
  let K : AddSubgroup G :=
    { carrier := {w | ψ (q w) = 1}
      zero_mem' := by
        show ψ _ = 1
        rw [map_zero, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb => by
        have ha' : ψ _ = 1 := ha
        have hb' : ψ _ = 1 := hb
        show ψ _ = 1
        rw [map_add (f := _), AddChar.map_add_eq_mul, ha', hb', one_mul]
      neg_mem' := fun {a} ha => by
        have ha' : ψ _ = 1 := ha
        show ψ _ = 1
        have := AddChar.map_add_eq_mul ψ (q a) (q (-a))
        rw [← map_add (f := _), add_neg_cancel, map_zero, ψ.map_zero_eq_one, ha', one_mul] at this
        exact this.symm }
  refine ⟨K, K.isOpen_of_mem_nhds (g := 0) ?_, fun w hw h0 => ?_⟩
  · have h1 : Continuous fun w : G => (φ w).2 := continuous_snd.comp hφ
    exact h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA D.host.F 0 a) = 1})
      (by rw [map_zero]; exact GlobalTheory.FinTranslate.ker_mem_nhds hc hn)
  · have h4 : φ w = q w := Prod.ext h0 rfl
    rw [h4]
    exact hw

theorem isThetaFun_heis {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {f : WA V W → ℂ}
    (hf : IsThetaFun ψ V W f) (u : WA V W) : IsThetaFun ψ V W (Heisenberg₂ ψ V W u f) := by
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  have hc : Continuous ψ := hψ.1.1
  let φ₁ : WA V W →+ AF D.host.F := AddMonoidHom.mk' (fun w => symplH V W w u) fun a b => symplH_add_left V W a b u
  let φ₂ : WA V W →+ AF D.host.F := AddMonoidHom.mk' (fun w => symplH V W u w) fun a b => symplH_add_right V W u a b
  have c₁ : Continuous φ₁ := ThetaCont.continuous_symplH V W continuous_id continuous_const
  have c₂ : Continuous φ₂ := ThetaCont.continuous_symplH V W continuous_const continuous_id
  refine ⟨heis_quasi ψ V W u f hf.quasi, ?_, (hc.comp c₁).mul (hf.cont.comp (continuous_id.add continuous_const)),
    fun k L hL hLf w => ?_⟩
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨K₁, hK₁, h₁⟩ := exists_open_ker hc hψ.1.2.1 φ₁ c₁
    obtain ⟨K₂, hK₂, h₂⟩ := exists_open_ker hc hψ.1.2.1 φ₂ c₂
    refine ⟨U ⊓ (K₁ ⊓ K₂), hU.inter (hK₁.inter hK₂), fun w hw hw' => ?_⟩
    have e₁ : ψ (symplH V W w u) = 1 := h₁ w hw.2.1 (by
      show fstA D.host.F (_ * sympl V W w u) = 0
      rw [map_mul, (sympl_parts D V W w u).2 (Or.inl hw'), mul_zero])
    have e₂ : ψ (symplH V W u w) = 1 := h₂ w hw.2.2 (by
      show fstA D.host.F (_ * sympl V W u w) = 0
      rw [map_mul, (sympl_parts D V W u w).2 (Or.inr hw'), mul_zero])
    conv_rhs => rw [← hUf w hw.1 hw']
    rw [heis_heis, heis_heis, e₁, e₂, add_comm]
  · obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
    let χ : (Fin k → ℝ) →+ ℂ := lam.comp (φ₁.comp L)
    have hχ : ContDiff ℝ ∞ χ := GlobalTheory.WeilVacMove.contDiff_additive χ (hl.comp (c₁.comp hL))
    have : (fun t => Heisenberg₂ ψ V W u f (w + L t)) =
        fun t => ψ (symplH V W w u) * Complex.exp (χ t) * f (w + u + L t) := by
      funext t
      have e : ψ (symplH V W (L t) u) = Complex.exp (χ t) := hlam _ (by
        show sndA D.host.F (_ * sympl V W (L t) u) = 0
        rw [map_mul, (sympl_parts D V W (L t) u).1 (Or.inl (hLf t)), mul_zero])
      rw [Heisenberg₂, symplH_add_left, AddChar.map_add_eq_mul, e, add_right_comm]
    rw [this]
    exact (contDiff_const.mul hχ.cexp).mul (hf.smooth k L hL hLf (w + u))

theorem thetaFun_closed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (f : WA V W → ℂ), (f ∈ ThS ψ V W ↔ IsThetaFun ψ V W f) ∧ (IsThetaFun ψ V W f → ∀ w₀, IsThetaFun ψ V W (Heisenberg₂ ψ V W w₀ f)) ∧ (V.rank ≠ W.rank → IsThetaFun ψ V W f → IsThetaFun ψ W V (fun x => f x.transpose)) := by
  intro D ψ hψ V W f
  refine ⟨⟨fun h => ?_, fun h => Submodule.subset_span h⟩, fun hf u => isThetaFun_heis hψ hf u,
    fun hne hf => isThetaFun_transpose ψ V W hne f hf⟩
  obtain ⟨M, hM⟩ := exists_thetaSubmodule D ψ V W
  exact (hM f).1 (Submodule.span_le.2 (fun g hg => (hM g).2 hg) h)

end GlobalTheory.Mem.ThetaClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.VolMeasure

theorem existsUnique_isVolMeasG : ∀ (D : D7) (V : HSp D), V.SigOK →
    ∃! μ, IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ := by
  intro D V hV
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.CMTypePlaces.mk_tauE_bijective D
  obtain ⟨μ, hμ⟩ := GlobalTheory.Mem.VolExists.exists_isVolMeasF _ _ D.sp.cm _ (tauE D) D.cd V hτ hV
  exact ⟨μ, hμ, fun ν hν =>
    GlobalTheory.Mem.VolUnique.volMeas_unique _ _ D.sp.cm _ (tauE D) D.cd V hτ hV ν μ hν hμ⟩

end GlobalTheory.Mem.VolMeasure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_normalizedHaarMeasure_adelicUnitary : ∀ (D : D7) (V : HSp D), V.SigOK → ∃! μ, IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ := by
  first | exact @GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG | exact GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG | (intros; apply GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfFam
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.InfFamUnique

theorem existsUnique_infFam : ∀ D : D7, ∃! θ : InfF D, IsInfFam θ := by
  intro D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  exact ⟨θ, hθ, fun θ' h' => funext fun ρ =>
    GlobalTheory.Mem.VolEmb.infEmb_unique (tauE D ρ) (θ' ρ) (θ ρ) (h' ρ) (hθ ρ)⟩

end GlobalTheory.Mem.InfFamUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabiliserSubgroupOutsidePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabiliserSubgroupOutsidePlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Ksph

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_subgroup_ksph : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    ∃ K : Subgroup (GA D V), (K : Set (GA D V)) = KsphC V S ∧ ∀ S', S ⊆ S' → KsphC V S' ⊆ KsphC V S :=
  fun _ V S => ⟨_, (GlobalTheory.AutFunCompare.KsphC_eq V S).symm,
    fun _ hS _ hg => ⟨hg.1, hg.2.1, fun v hv => hg.2.2 v (hS hv)⟩⟩

end GlobalTheory.Mem.Ksph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabiliserSubgroupOutsidePlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_stabiliser_subgroup_outside_places : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ K : Subgroup (GA D V), (K : Set (GA D V)) = KsphC V S ∧ ∀ S', S ⊆ S' → KsphC V S' ⊆ KsphC V S := by
  first | exact @GlobalTheory.Mem.Ksph.exists_subgroup_ksph | exact GlobalTheory.Mem.Ksph.exists_subgroup_ksph | (intros; apply GlobalTheory.Mem.Ksph.exists_subgroup_ksph <;> assumption)
end
end
