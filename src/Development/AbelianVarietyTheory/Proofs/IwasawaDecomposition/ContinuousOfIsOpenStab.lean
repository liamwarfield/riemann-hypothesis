module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Topology Matrix

namespace GlobalTheory.CuspRep.ContAut

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_map_pFin :
    Continuous (GeneralLinearGroup.map (pFin E) : GA E a → GL (Fin a) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pFin E))

theorem continuous_map_pInf :
    Continuous (GeneralLinearGroup.map (pInf E) : GA E a → GL (Fin a) (Cinf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pInf E))

theorem continuous_of_isOpen_stab : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsOpen {k | finRep E a k φ = φ} → Continuous φ.1 := by
  intro E _ _ _ a φ hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : Continuous fun x : GA E a => g⁻¹ * x := continuous_const.mul continuous_id
  have h1 : Continuous fun x : GA E a => toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((continuous_map_pInf E a).comp hm)
  have h2 : ContinuousAt (fun x : GA E a => chart φ.1 g (toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)) g :=
    ContinuousAt.comp (f := fun x : GA E a => toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)
      (contDiffAt_chart φ.2 g (val_mem_invSet _)).continuousAt h1.continuousAt
  refine h2.congr ?_
  have h3 : {x : GA E a | finRep E a (GeneralLinearGroup.map (pFin E) (g⁻¹ * x)) φ = φ} ∈ 𝓝 g :=
    (hφ.preimage ((continuous_map_pFin E a).comp hm)).mem_nhds (by simp)
  filter_upwards [h3] with x hx
  rw [chart_val]
  conv_lhs => rw [← hx]
  change φ.1 (g * infGL E a _ * finGL E a _) = _
  rw [mul_assoc, infGL_mul_finGL, mul_inv_cancel_left]

end GlobalTheory.CuspRep.ContAut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.InfType

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def diagInf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : E →+* Cinf E :=
  (pInf E).comp (algebraMap E (Ad E))

theorem infDiag_eq (k : Eˣ) : infDiag k = infId E (Units.map (diagInf E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - infEq E 1 + infEq E ((infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

theorem denseRange_diagInf : DenseRange (diagInf E) := by
  have hc : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact (infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

theorem denseRange_units : DenseRange (Units.map (diagInf E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagInf.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem coord_expU (τ : E →+* ℂ) (x : Cinf E) : coord τ (expU x : (Cinf E)ˣ) = Complex.exp (coord τ x) := by
  unfold coord
  split_ifs
  · rfl
  · exact (Complex.exp_conj _).symm


omit [NumberField E] in
theorem conj_ne (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))


open Classical in
theorem coord_atEmb' (σ τ : E →+* ℂ) (z : ℂ) : coord σ (atEmb τ z) =
    (if σ = τ then z else 0) + (if σ = ComplexEmbedding.conjugate τ then starRingEnd ℂ z else 0) := by
  by_cases h1 : σ = τ
  · subst h1
    rw [if_pos rfl, if_neg (conj_ne σ).symm, add_zero, coord_atEmb]
  by_cases h2 : σ = ComplexEmbedding.conjugate τ
  · subst h2
    rw [if_neg h1, if_pos rfl, zero_add]
    have := atEmb_conj τ (starRingEnd ℂ z)
    rw [Complex.conj_conj] at this
    rw [← this, coord_atEmb]
  · have h : InfinitePlace.mk σ ≠ InfinitePlace.mk τ := fun h => by
      rcases InfinitePlace.mk_eq_iff.1 h with h | h
      · exact h1 h
      · exact h2 (by rw [← h]; ext; simp)
    rw [if_neg h1, if_neg h2, add_zero]
    unfold coord atEmb
    by_cases h3 : (InfinitePlace.mk σ).embedding = σ
    · rw [if_pos h3]; simp [h]
    · rw [if_neg h3]; simp [h]

theorem chiInf_eq (χ : HChar E) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (f : I → ℂ → ℂ)
    (hf : ∀ i z, z ≠ 0 → ContinuousAt (f i) z)
    (h : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, f i (φ i k)) (u : (Cinf E)ˣ) :
    ((chiInf χ u : ℂˣ) : ℂ) = ∏ i, f i (coord (φ i) u) := by
  refine congrFun (denseRange_units.equalizer (g := fun u => ((chiInf χ u : ℂˣ) : ℂ))
    (h := fun u : (Cinf E)ˣ => ∏ i, f i (coord (φ i) u)) (Units.continuous_val.comp (continuous_chiInf χ))
    (continuous_finsetProd _ fun i _ => continuous_iff_continuousAt.2 fun v => ?_) (funext fun k => ?_)) u
  · exact ContinuousAt.comp (g := f i) (f := fun u : (Cinf E)ˣ => coord (φ i) u)
      (hf i _ (v.isUnit.map (coord (φ i))).ne_zero)
      ((continuous_coord (φ i)).comp Units.continuous_val).continuousAt
  · have e := h k
    simp only [← coord_algebraMap (φ _) (k : E)] at e
    rw [HChar.inf, MonoidHom.comp_apply, infDiag_eq] at e
    exact e


open Classical in
theorem expo_eq_sum (χ : HChar E) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (f : I → ℂ → ℂ) (a b : I → ℂ)
    (hf : ∀ i z, z ≠ 0 → ContinuousAt (f i) z)
    (he : ∀ i z, f i (Complex.exp z) = Complex.exp (a i * z + b i * starRingEnd ℂ z))
    (h : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, f i (φ i k)) (τ : E →+* ℂ) :
    expo χ τ = ∑ i, ((if φ i = τ then a i else 0) + (if φ i = ComplexEmbedding.conjugate τ then b i else 0)) := by
  refine expo_eq_of_exp χ τ _
    (∑ i, ((if φ i = τ then b i else 0) + (if φ i = ComplexEmbedding.conjugate τ then a i else 0))) fun z => ?_
  rw [chiInf_eq χ φ f hf h]
  simp only [coord_expU, he, coord_atEmb']
  rw [← Complex.exp_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  split_ifs <;> simp <;> ring

theorem expo_of_infType : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E), (∀ n : (E →+* ℂ) → ℤ, χ.IsAlg n → ∀ τ, expo χ τ = n τ) ∧ (∀ s : ℝ, χ.IsAbsPow s → ∀ τ, expo χ τ = s) ∧ ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ), Function.Injective (fun i => InfinitePlace.mk (φ i)) → χ.HasInf φ n → ∀ i, expo χ (φ i) = (n i : ℂ) / 2 ∧ expo χ (ComplexEmbedding.conjugate (φ i)) = -(n i : ℂ) / 2 := by
  intro E _ _ _ χ
  classical
  refine ⟨fun n h τ => ?_, fun s h τ => ?_, fun I _ φ n hφ h i => ?_⟩
  · rw [expo_eq_sum χ (fun σ => σ) (fun σ z => z ^ n σ) (fun σ => n σ) (fun _ => 0)
      (fun σ z hz => continuousAt_zpow₀ z _ (Or.inl hz)) (fun σ z => by simp [Complex.exp_int_mul]) h τ]
    simp
  · rw [expo_eq_sum χ (fun σ => σ) (fun σ z => ((‖z‖ : ℝ) : ℂ) ^ (s : ℂ)) (fun _ => s / 2) (fun _ => s / 2)
      (fun σ z hz => ?_) (fun σ z => ?_) h.2.2 τ]
    · simp [Finset.sum_add_distrib]
    · refine ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_norm).continuousAt continuousAt_const ?_
      exact Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 hz)
    · rw [← Complex.ofReal_cpow (norm_nonneg _), Complex.norm_exp, ← Real.exp_mul, Complex.ofReal_exp]
      congr 1
      rw [← mul_add, Complex.add_conj]
      push_cast
      ring
  · have key := expo_eq_sum χ φ (fun i z => (z / ((‖z‖ : ℝ) : ℂ)) ^ n i) (fun i => n i / 2) (fun i => -(n i : ℂ) / 2)
      (fun i z hz => ?_) (fun i z => ?_) h
    · have h1 : ∀ j, φ j = φ i ↔ j = i := fun j =>
        ⟨fun e => hφ (congrArg InfinitePlace.mk e), fun e => by rw [e]⟩
      have h2 : ∀ j, φ j ≠ ComplexEmbedding.conjugate (φ i) := fun j e => by
        have : j = i := hφ ((congrArg InfinitePlace.mk e).trans (InfinitePlace.mk_conjugate_eq _))
        subst this
        exact conj_ne _ e.symm
      have h3 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ i)) = φ i := by ext; simp
      rw [key, key]
      simp [h1, h2, h3]
    · have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz
      exact (continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt hn).zpow₀ _
        (Or.inl (div_ne_zero hz hn))
    · rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub, ← Complex.exp_int_mul]
      congr 1
      have := Complex.add_conj z
      push_cast at this
      linear_combination ((n i : ℂ) / 2) * this

end GlobalTheory.CuspRep.InfType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityTypeStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_exponent_of_infinityType : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E), (∀ n : (E →+* ℂ) → ℤ, χ.IsAlg n → ∀ τ, expo χ τ = n τ) ∧ (∀ s : ℝ, χ.IsAbsPow s → ∀ τ, expo χ τ = s) ∧ ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ), Function.Injective (fun i => InfinitePlace.mk (φ i)) → χ.HasInf φ n → ∀ i, expo χ (φ i) = (n i : ℂ) / 2 ∧ expo χ (ComplexEmbedding.conjugate (φ i)) = -(n i : ℂ) / 2 := by
  first | exact @GlobalTheory.CuspRep.InfType.expo_of_infType | exact GlobalTheory.CuspRep.InfType.expo_of_infType | (intros; apply GlobalTheory.CuspRep.InfType.expo_of_infType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.CuspRep.LocUniq

theorem equiv_of_iSup_range {R M S S' : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [AddCommGroup S'] [Module R S'] [IsSimpleModule R S] [IsSimpleModule R S']
    (h : ∀ x : M, x ∈ ⨆ f : S →ₗ[R] M, LinearMap.range f) (g : S' →ₗ[R] M) (hg : Function.Injective g) :
    Nonempty (S ≃ₗ[R] S') := by
  let s : Set (Submodule R M) := {m | Nonempty (m ≃ₗ[R] S)}
  have : ∀ m : s, IsSimpleModule R m := fun m => m.2.elim fun e => IsSimpleModule.congr e
  have e0 := LinearEquiv.ofInjective g hg
  have : IsSimpleModule R (LinearMap.range g) := IsSimpleModule.congr e0.symm
  have hle : LinearMap.range g ≤ sSup s := fun x _ => by
    refine (iSup_le (a := sSup s) fun f => ?_) (h x)
    rcases LinearMap.injective_or_eq_zero f with hf | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective f hf).symm⟩
    · simp
  obtain ⟨m, ⟨e⟩, ⟨e'⟩⟩ := (LinearMap.range g).linearEquiv_of_le_sSup s hle
  exact ⟨(e0.trans (e'.trans e)).symm⟩

section Rep

variable {G V W W' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def isoPart (σ : Representation ℂ G W) (ρ : Representation ℂ G V) : Submodule ℂ V :=
  ⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap

theorem isoPart_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V} (hx : x ∈ isoPart σ ρ) :
    ρ g x ∈ isoPart σ ρ := by
  refine (iSup_le (a := (isoPart σ ρ).comap (ρ g)) fun f => ?_) hx
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩

theorem isoPart_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V} (hx : x ∈ isoPart σ ρ) : T x ∈ isoPart σ ρ := by
  refine (iSup_le (a := (isoPart σ ρ).comap T) fun f => ?_) hx
  rintro _ ⟨v, rfl⟩
  refine Submodule.mem_iSup_of_mem (⟨T ∘ₗ f.toLinearMap, fun g => LinearMap.ext fun u => ?_⟩ : σ.IntertwiningMap ρ)
    ⟨v, rfl⟩
  exact (congrArg T (LinearMap.congr_fun (f.isIntertwining' g) u)).trans (hT g _)

theorem equiv_of_isoPart (σ : Representation ℂ G W) (σ' : Representation ℂ G W') (ρ : Representation ℂ G V)
    [σ.IsIrreducible] [σ'.IsIrreducible] (h : isoPart σ ρ = ⊤) (f' : σ'.IntertwiningMap ρ) (hf' : f' ≠ 0) :
    Nonempty (σ.Equiv σ') := by
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f').resolve_right hf'
  obtain ⟨e⟩ := equiv_of_iSup_range (R := MonoidAlgebra ℂ G) (S := σ.asModule) (M := ρ.asModule) (fun x => by
    have hx : ρ.asModuleEquiv x ∈ isoPart σ ρ := h ▸ Submodule.mem_top
    have hle : isoPart σ ρ ≤ ((⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule,
        LinearMap.range f).restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      have : Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f (σ.asModuleEquiv.symm v) ∈
          ⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule, LinearMap.range f :=
        Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f) ⟨_, rfl⟩
      exact this
    exact hle hx) (Representation.IntertwiningMap.equivLinearMapAsModule σ' ρ f') hi
  exact ⟨((Representation.IntertwiningMap.equivLinearMapAsModule σ σ').symm e.toLinearMap).ofBijective e.bijective⟩

end Rep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ v, GeneralLinearGroup.map (pLoc E v) g = GeneralLinearGroup.map (pLoc E v) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext E fun v => ?_)
  exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x.val i j) (H v)

theorem comm_locGL (w : HeightOneSpectrum (𝓞 E)) {k : GL (Fin a) (Af E)}
    (hk : GeneralLinearGroup.map (pLoc E w) k = 1) (g : GL (Fin a) (w.adicCompletion E)) :
    k * locGL E a w g = locGL E a w g * k := by
  refine gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases h : v = w
  · subst h; rw [hk, one_mul, mul_one]
  · rw [pLoc_locGL_of_ne h, one_mul, mul_one]

theorem isoPart_fin {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin a) (Af E)) V)
    (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (k : GL (Fin a) (Af E)) {x : V}
    (hx : x ∈ isoPart σ (τ.comp (locGL E a w))) : τ k x ∈ isoPart σ (τ.comp (locGL E a w)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = GeneralLinearGroup.map (pLoc E w) k := ⟨_, rfl⟩
  have hk : GeneralLinearGroup.map (pLoc E w) ((locGL E a w g)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, pLoc_locGL, hg, inv_mul_cancel]
  have h1 := isoPart_act σ _ g (isoPart_comm σ _ (τ ((locGL E a w g)⁻¹ * k)) (fun g' y => by
    simp only [MonoidHom.comp_apply]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, comm_locGL w hk]) hx)
  rwa [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1

variable [_root_.NumberField.IsTotallyComplex E]

theorem isoPart_op (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (o : Op E a) {x : π.V}
    (hx : x ∈ isoPart σ (π.locRep w)) : π.op o x ∈ isoPart σ (π.locRep w) := by
  cases o with
  | fin k =>
    exact isoPart_fin π.finPart w σ k hx
  | cpt k =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem isLocComp_unique (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))) (h : π.IsLocComp w σ) (h' : π.IsLocComp w σ') :
    Nonempty (σ.ρ.Equiv σ'.ρ) := by
  obtain ⟨f, h0, hf⟩ := h
  obtain ⟨f', h0', hf'⟩ := h'
  have := σ.irred
  have := σ'.irred
  refine equiv_of_isoPart σ.ρ σ'.ρ (π.locRep w) ?_ ⟨f', fun g => LinearMap.ext (hf' g)⟩
    fun e => h0' (congrArg Representation.IntertwiningMap.toLinearMap e)
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred ((isoPart σ.ρ (π.locRep w)).map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, isoPart_op π w σ.ρ o hx, rfl⟩) with h1 | h1
  · refine absurd (LinearMap.ext fun v => ?_) h0
    have h2 : isoPart σ.ρ (π.locRep w) = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    have h3 : f v ∈ isoPart σ.ρ (π.locRep w) :=
      Submodule.mem_iSup_of_mem (⟨f, fun g => LinearMap.ext (hf g)⟩ : σ.ρ.IntertwiningMap (π.locRep w)) ⟨v, rfl⟩
    rw [h2] at h3
    exact h3
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)

end GlobalTheory.CuspRep.LocUniq

theorem GlobalTheory.CuspRep.CG.IsLoc.unique : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) (σ σ' : Irr (GL (Fin a) (w.adicCompletion E))), π.IsLoc w σ → π.IsLoc w σ' → σ = σ' := by
  intro E _ _ _ a π w σ σ' h h'
  induction π using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  induction σ' using Quotient.inductionOn
  exact Quotient.sound (GlobalTheory.CuspRep.LocUniq.isLocComp_unique _ w _ _ h h')
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Topology Matrix Filter

namespace GlobalTheory.CuspRep.LocSph

theorem exists_fixed_of_mem_iSup {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (φ : V) (h0 : φ ≠ 0) (hK : ∀ k ∈ K, ρ k φ = φ)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun k hk => ?_⟩
        have h4 : σ k v - v ∈ W.comap (f i) := by
          have h5 := hK k hk
          rw [← e, map_add (f := _)] at h5
          have h6 : f i (σ k v - v) = x - ρ k x := by
            rw [map_sub, hf]; linear_combination (norm := module) h5
          rw [Submodule.mem_comap, h6]
          exact sub_mem hx (hW k x hx)
        rw [hc, Submodule.mem_bot] at h4
        exact sub_eq_zero.1 h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _), ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {x y : GL (Fin a) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) : x = y := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun g : GL (Fin a) (v.adicCompletion E) => g.val i j) (h v)

theorem comm_locGL (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (hk : GeneralLinearGroup.map (pLoc E w) k = 1) (g : GL (Fin a) (w.adicCompletion E)) :
    k * locGL E a w g = locGL E a w g * k := by
  refine gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases h : v = w
  · subst h; rw [hk, one_mul, mul_one]
  · rw [pLoc_locGL_of_ne h, one_mul, mul_one]

theorem tendsto_sLoc (y : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E)
    (hy : ∀ v, y v ∈ v.adicCompletionIntegers E) : Tendsto (fun v => sLoc E v (y v)) cofinite (𝓝 0) := by
  classical
  have h := (GlobalTheory.Mem.UnrAe.tendsto_finSingle y hy).sub
    (GlobalTheory.Mem.UnrAe.tendsto_finSingle (L := E) (fun _ => 0) fun _ => by simp)
  rw [sub_self] at h
  refine h.congr fun w => ?_
  refine FiniteAdeleRing.ext _ fun v => ?_
  change Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w (y w) v -
      Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w 0 v =
      (Pi.single w (y w) : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E) v
  by_cases h : v = w
  · subst h; simp
  · simp [h]

theorem tendsto_corner (y : ∀ v : HeightOneSpectrum (𝓞 E), Matrix (Fin a) (Fin a) (v.adicCompletionIntegers E)) :
    Tendsto (fun v => corner (matN a (sLoc E v)) ((y v).map (v.adicCompletionIntegers E).subtype)) cofinite (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := ((tendsto_const_nhds (x := (1 : Matrix (Fin a) (Fin a) (Af E)) i j)).sub
    (tendsto_sLoc (E := E) (fun v => (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) fun v => by
      rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _])).add
    (tendsto_sLoc (fun v => (y v i j : v.adicCompletion E)) fun v => (y v i j).2)
  rw [sub_zero, add_zero] at h
  exact h

theorem tendsto_locGL (y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin a) (v.adicCompletionIntegers E)) :
    Tendsto (fun v => locGL E a v (GeneralLinearGroup.map (v.adicCompletionIntegers E).subtype (y v))) cofinite (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact (tendsto_corner fun v => (y v).val).prodMk_nhds
    ((MulOpposite.continuous_op.tendsto _).comp (tendsto_corner fun v => ((y v)⁻¹).val))

theorem eventually_mem {U : Set (GL (Fin a) (Af E))} (hU : U ∈ 𝓝 1) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ U := by
  have h : ∀ w : HeightOneSpectrum (𝓞 E), ∃ y : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype y) ∈ U →
      ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
        locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ U := fun w => by
    by_contra hc
    push Not at hc
    obtain ⟨-, g, hg⟩ := hc 1
    exact hg (hc g).1
  choose y hy using h
  exact ((tendsto_locGL y).eventually_mem hU).mono fun w hw => hy w hw

variable [_root_.NumberField.IsTotallyComplex E]

def Maps (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E a // (∀ v, f v ∈ π.V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)}

theorem iSup_range_eq (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : π.IsLocComp w σ) : ⨆ f : Maps π w σ, LinearMap.range f.1 = π.V := by
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ (f : Maps π w σ) v, act o (f.1 v) ∈ ⨆ f : Maps π w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => π.stable o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : Maps π w σ) ⟨v, rfl⟩
  refine (π.irred _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : Maps π w σ, LinearMap.range f.1) ≤ (⨆ f : Maps π w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
          change finRep E a _ * _ = _ * finRep E a _
          rw [← map_mul, ← map_mul, comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v
    exact this hφ
  · obtain ⟨f, h0, hf⟩ := h
    refine h0 (LinearMap.ext fun v => Subtype.ext ?_)
    have : (f v).1 ∈ ⨆ f : Maps π w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨π.V.subtype ∘ₗ f, fun v => (f v).2, fun g v => congrArg Subtype.val (hf g v)⟩ :
        Maps π w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact this

theorem locComp_spherical : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ → ∃ v : σ.V, v ≠ 0 ∧ ∀ g : GL (Fin a) (w.adicCompletionIntegers E), σ.ρ (Matrix.GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) v = v := by
  intro E _ _ _ a π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  filter_upwards [eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw σ hσ
  obtain ⟨v, h1, h2⟩ := exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a w)) σ.ρ σ.irred
    (fun f : Maps π w σ => f.1) (fun f => f.2.2)
    (Set.range (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype)) φ h0
    (by rintro _ ⟨g, rfl⟩; exact hw g) (by rw [iSup_range_eq π w σ hσ]; exact hφ)
  exact ⟨v, h1, fun g => h2 _ ⟨g, rfl⟩⟩

end GlobalTheory.CuspRep.LocSph
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem commute_cap_of_commute_Eop (τ : E →+* ℂ) (u : ℂ) (z : Module.End ℂ (Sm E a))
    (h : ∀ i j, Commute (Eop τ i j) z) : Commute (cap τ u) z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {z}
  have hS : ∀ x, x ∈ S ↔ Commute x z := fun x => by
    simp only [S, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => (hS _).2 (h i j)
  refine (hS _).1 ?_
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem commute_cap_Eop (τ τ' : E →+* ℂ) (u : ℂ) (i j : Fin a) : Commute (cap τ u) (Eop τ' i j) := by
  by_cases h : τ = τ'
  · subst h; exact cap_comm τ u i j
  · exact commute_cap_of_commute_Eop τ u _ fun k l => Eop_comm h k l i j

theorem lieS_atEmb_one (τ : E →+* ℂ) (i j : Fin a) :
    lieS E a i j (atEmb τ 1) = Eop τ i j + Eop (ComplexEmbedding.conjugate τ) i j := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  match_scalars <;> ring

theorem lieS_atEmb_I (τ : E →+* ℂ) (i j : Fin a) :
    lieS E a i j (atEmb τ Complex.I) = Complex.I • (Eop τ i j - Eop (ComplexEmbedding.conjugate τ) i j) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  match_scalars <;> ring_nf <;> simp

theorem commute_cap_lieS (τ : E →+* ℂ) (u : ℂ) (i j : Fin a) (x : Cinf E) : Commute (cap τ u) (lieS E a i j x) := by
  classical
  have hx : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  refine Commute.sum_right _ _ _ fun w _ => ?_
  rw [atEmb_eq, map_add (f := _), map_smul, map_smul, lieS_atEmb_one, lieS_atEmb_I]
  exact (((commute_cap_Eop τ _ u i j).add_right (commute_cap_Eop τ _ u i j)).smul_right _).add_right
    ((((commute_cap_Eop τ _ u i j).sub_right (commute_cap_Eop τ _ u i j)).smul_right _).smul_right _)

theorem commute_cap_lie (τ : E →+* ℂ) (u : ℂ) (X : Lie E a) : Commute (cap τ u) (lie E a X) := by
  have hX : lie E a X = ∑ i, ∑ j, lieS E a i j (X i j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.matrix_eq_sum_single (Matrix.of X))
  rw [hX]
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => commute_cap_lieS τ u i j _

theorem commute_cap_finRep (τ : E →+* ℂ) (u : ℂ) (k : GL (Fin a) (Af E)) : Commute (cap τ u) (finRep E a k) := by
  have h : ∀ i j x, Commute (lieS E a i j x) (finRep E a k) := fun i j x => lie_rt_fin _ k
  exact commute_cap_of_commute_Eop τ u _ fun i j =>
    ((h i j _).sub_left ((h i j _).smul_left _)).smul_left _

end GlobalTheory.CuspRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstFaithful

theorem exists_idem {LL U D R : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D]
    (m : U →+* End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)
    [CommRing R] [IsSemisimpleRing R] (α : R →+* End LL D) (π : R →+* F) (iL : LL → R) (iU : U → R)
    (h1 : ∀ a, α (iL a) = algebraMap LL (End LL D) a) (h2 : ∀ c, α (iU c) = m c)
    (h3 : ∀ a, π (iL a) = algebraMap LL F a) (h4 : ∀ c, π (iU c) = τ c) :
    ∃ e : R, π e = 1 ∧ ∀ x, letterMk m F τ x = 0 → α e x = 0 := by
  let : Algebra R F := π.toAlgebra
  obtain ⟨q, hq⟩ := exists_isCompl (RingHom.ker π)
  have h1q : (1 : R) ∈ RingHom.ker π ⊔ q := by rw [hq.sup_eq_top]; trivial
  obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 h1q
  have hπe : π e = 1 := by
    have := congrArg π hae
    rwa [map_add, RingHom.mem_ker.1 ha, zero_add, map_one] at this
  have hinj : Function.Injective ((Algebra.linearMap R F) ∘ₗ q.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have : (y : R) ∈ RingHom.ker π ⊓ q := ⟨hy, y.2⟩
    rw [hq.inf_eq_bot] at this
    exact Subtype.ext this
  obtain ⟨Λ, hΛ⟩ := IsSemisimpleModule.extension_property _ hinj q.subtype
  have hΛ1 : Λ 1 = e := by
    rw [← hπe]; exact LinearMap.congr_fun hΛ ⟨e, he⟩
  have hΛm : ∀ r f, Λ (π r * f) = r * Λ f := fun r f => Λ.map_smul r f
  let β : F →ₗ[LL] End LL D :=
    { toFun := fun f => α (Λ f)
      map_add' := fun f g => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun a f => by
        rw [Algebra.smul_def, ← h3, hΛm, map_mul, h1, ← Algebra.smul_def]; rfl }
  have hβ : ∀ f x, TensorProduct.lift β (f ⊗ₜ x) = α (Λ f) x := fun _ _ => rfl
  have hker : ∀ y ∈ letterKer m F τ, TensorProduct.lift β y = 0 := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => TensorProduct.lift β y = 0) hy ?_ ?_ ?_
    · rintro c _ ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f x =>
        rw [LinearMap.sub_apply, map_sub, LinearMap.baseChange_tmul, LinearMap.smul_apply,
          LinearMap.id_apply, smul_tmul', hβ, hβ, smul_eq_mul, ← h4, hΛm, mul_comm, map_mul, h2,
          End.mul_apply, sub_self]
      | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, add_zero]
    · exact map_zero _
    · intro y z hy hz
      rw [map_add (f := _), hy, hz, add_zero]
  refine ⟨e, hπe, fun x hx => ?_⟩
  rw [letterMk, ← LinearMap.mem_ker, ker_letterQ] at hx
  rw [← hΛ1, ← hβ]
  exact hker _ hx

variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)

theorem exists_level_tensor (r : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
    ∀ f : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l), (∀ c : ↥(MaximalUnramifiedExtension l), c ^ m = 1 → f c = c) →
      Algebra.TensorProduct.map f (AlgHom.id ℚ_[l] ↥LL.1) r = r := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, hl.out.not_dvd_one, fun f _ => map_zero _⟩
  | tmul c a =>
    obtain ⟨m, hm, hlm, H⟩ := MemLoc.FrobLaws.exists_level c.2
    refine ⟨m, hm, hlm, fun f hf => ?_⟩
    obtain ⟨g, hg⟩ := MemLoc.FrobLaws.exists_ext f
    have h := H g 1 fun ζ hζ => by
      let z : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
      exact (hg z).trans (congrArg Subtype.val (hf z (Subtype.ext hζ)))
    have h' : f c = c := Subtype.ext ((hg c).symm.trans h)
    rw [Algebra.TensorProduct.map_tmul, h', AlgHom.id_apply]
  | add x y hx hy =>
    obtain ⟨m, hm, hlm, ha⟩ := hx
    obtain ⟨n, hn, hln, hb⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, fun hd => ((hl.out.dvd_mul).1 hd).elim hlm hln, fun f H => ?_⟩
    rw [map_add (f := _), ha f fun ζ hζ => H ζ (by rw [pow_mul, hζ, one_pow]),
      hb f fun ζ hζ => H ζ (by rw [mul_comm, pow_mul, hζ, one_pow])]

theorem exists_algHom_ker (U R Ω : Type) [Field U] [CommRing R] [Algebra U R] [Module.Finite U R] [Field Ω]
    [IsAlgClosed Ω] [Algebra U Ω] (I : Ideal R) (hI : I ≠ ⊤) : ∃ ψ : R →ₐ[U] Ω, ∀ r ∈ I, ψ r = 0 := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  let := Ideal.Quotient.field M
  let ψ₀ : (R ⧸ M) →ₐ[U] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ₀.comp (Ideal.Quotient.mkₐ _ M), fun r hr => ?_⟩
  have : Ideal.Quotient.mkₐ U M r = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hIM hr)
  rw [AlgHom.comp_apply, this, map_zero]

theorem exists_restrict (g : GQ l) : ∃ t : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l), ∀ c, (t c : Om l) = g c := by
  have hle : (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  exact ⟨((g : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict
    (MaximalUnramifiedExtension l).toSubalgebra (fun x => hle ⟨x, x.2, rfl⟩), fun _ => rfl⟩

theorem exists_extend (f : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ∃ g : GQ l, ∀ a : ↥LL.1, g a = f a :=
  ⟨AlgEquiv.ofBijective (f.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _),
    fun a => f.liftNormal_commutes (Om l) a⟩

theorem exists_translate (I : Ideal (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1)) (hI : I ≠ ⊤)
    (e : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) (he : Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val e ≠ 0) :
    ∃ (n : ℕ) (r : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1), r ∉ I ∧
      Algebra.TensorProduct.map (frobUr l ^ n) (AlgHom.id ℚ_[l] ↥LL.1) r = e := by
  have := LL.2
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker ↥(MaximalUnramifiedExtension l) _ (Om l) I hI
  obtain ⟨g, hg'⟩ := exists_extend LL
    ((ψ.restrictScalars ℚ_[l]).comp Algebra.TensorProduct.includeRight)
  have hg : ∀ a : ↥LL.1, g a = ψ (1 ⊗ₜ a) := hg'
  obtain ⟨t, ht⟩ := exists_restrict g
  have key : ∀ r, ψ (Algebra.TensorProduct.map t (AlgHom.id ℚ_[l] ↥LL.1) r) =
      g (Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val r) := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c a =>
      have e1 : t c ⊗ₜ[ℚ_[l]] a = t c • ((1 : ↥(MaximalUnramifiedExtension l)) ⊗ₜ[ℚ_[l]] a) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, e1, map_smul, ← hg,
        Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      exact congrArg (· * g a) (ht c)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  obtain ⟨m, hm, hlm, H⟩ := exists_level_tensor LL e
  obtain ⟨n, hn⟩ := MemLoc.FrobLaws.gal_root g⁻¹ hm hlm
  refine ⟨n, Algebra.TensorProduct.map t (AlgHom.id ℚ_[l] ↥LL.1) e, fun h => he ?_, ?_⟩
  · have h0 := hψ _ h
    rw [key] at h0
    exact g.injective (h0.trans (map_zero g).symm)
  · rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
    refine H _ fun c hc => ?_
    have hc' : t c ^ m = 1 := by rw [← map_pow, hc, map_one]
    rw [AlgHom.comp_apply, frobUr_pow_root n _ m hm hlm hc', ← map_pow]
    apply Subtype.ext
    rw [ht]
    have := hn c (congrArg Subtype.val hc)
    rw [SubmonoidClass.coe_pow, ← this, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem exists_action {k L U D : Type} [Field k] [Field L] [Field U] [Algebra k L] [Algebra k U]
    [AddCommGroup D] [Module L D] (m : U →+* End L D)
    (hm : ∀ c : k, m (algebraMap k U c) = algebraMap L _ (algebraMap k L c)) :
    ∃ α : U ⊗[k] L →+* End L D, ∀ c a, α (c ⊗ₜ a) = m c * algebraMap L _ a := by
  let : Module k D := Module.compHom D (algebraMap k L)
  have : IsScalarTower k L D := .of_algebraMap_smul fun _ _ => rfl
  let mU : U →ₐ[k] End L D := { m with commutes' := hm }
  exact ⟨(Algebra.TensorProduct.lift mU (IsScalarTower.toAlgHom k L (End L D))
    fun c a => (Algebra.commutes a (m c)).symm).toRingHom, fun _ _ => rfl⟩

theorem eq_zero_of_translate {k L U D : Type} [Field k] [Field L] [Field U] [Algebra k L] [Algebra k U]
    [AddCommGroup D] [Module L D] {m : U →+* End L D} (α : U ⊗[k] L →+* End L D)
    (hα : ∀ c a, α (c ⊗ₜ a) = m c * algebraMap L _ a) (σ : ℕ → U →ₐ[k] U) (φ : ℕ → End L D)
    (hinj : ∀ n, Function.Injective (φ n)) (hφ : ∀ n c, φ n * m c = m (σ n c) * φ n) (e : U ⊗[k] L) (x : D)
    (hx : ∀ n, α e (φ n x) = 0)
    (he : ∀ I : Ideal (U ⊗[k] L), I ≠ ⊤ →
      ∃ n r, r ∉ I ∧ Algebra.TensorProduct.map (σ n) (AlgHom.id k L) r = e) : x = 0 := by
  let I : Ideal (U ⊗[k] L) :=
    { carrier := {r | α r x = 0}
      add_mem' := fun {a b} (ha : α a x = 0) (hb : α b x = 0) => show α (a + b) x = 0 by
        rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
      zero_mem' := show α 0 x = 0 by rw [map_zero, LinearMap.zero_apply]
      smul_mem' := fun a b (hb : α b x = 0) => show α (a * b) x = 0 by
        rw [map_mul, End.mul_apply, hb, map_zero] }
  by_contra h0
  have hI : I ≠ ⊤ := fun h => h0 (by
    have : α 1 x = 0 := (Ideal.eq_top_iff_one I).1 h
    rwa [map_one] at this)
  obtain ⟨n, r, hr, hre⟩ := he I hI
  have semi : ∀ s, φ n * α s = α (Algebra.TensorProduct.map (σ n) (AlgHom.id k L) s) * φ n := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hα, hα, ← mul_assoc, hφ, mul_assoc,
        mul_assoc, Algebra.commutes]
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), mul_add, add_mul, hy, hz]
  refine hr (?_ : α r x = 0)
  have h1 := LinearMap.congr_fun (semi r) x
  rw [End.mul_apply, End.mul_apply, hre] at h1
  exact hinj n (h1.trans ((hx n).trans (map_zero _).symm))

theorem isSemisimpleRing_tensor : IsSemisimpleRing (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) := by
  have := LL.2
  have : Algebra.FormallyUnramified ℚ_[l] ↥LL.1 := Algebra.FormallyUnramified.of_isSeparable _ _
  have : IsReduced (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) :=
    Algebra.FormallyUnramified.isReduced_of_field ↥(MaximalUnramifiedExtension l) _
  have : IsArtinianRing (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) := IsArtinianRing.of_finite ↥(MaximalUnramifiedExtension l) _
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem eq_zero_of_wdMk_phiD_pow (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (K LL : FinExt l)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) (x : ↥(Dpst P ρ))
    (hx : ∀ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x) = 0) : x = 0 := by
  have := isSemisimpleRing_tensor LL
  obtain ⟨α, hα⟩ := exists_action (k := ℚ_[l]) (mulD P ρ) fun c =>
    LinearMap.ext fun y => Subtype.ext (by
      have : mulV P ↥LL.1 V (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) =
          algebraMap ↥LL.1 _ (algebraMap ℚ_[l] ↥LL.1 c) :=
        end_ext P fun v b => by
          rw [mulV_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul,
            Module.algebraMap_end_apply, algebraMap_smul]
      exact LinearMap.congr_fun this y.1)
  let π₀ := Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val
  have hπ₀ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (a : ↥LL.1), π₀ (c ⊗ₜ a) = (c : Om l) * a := fun _ _ => rfl
  let := algC ι LL
  obtain ⟨e, he, hk⟩ := exists_idem (mulD P ρ) ℂ (urC ι) α (ι.toRingHom.comp π₀.toRingHom)
    (fun a => 1 ⊗ₜ a) (fun c => c ⊗ₜ 1) (fun a => (hα 1 a).trans (by rw [map_one, one_mul]))
    (fun c => (hα c 1).trans (by rw [map_one, mul_one]))
    (fun a => congrArg ι ((hπ₀ 1 a).trans (one_mul (a : Om l))))
    (fun c => congrArg ι ((hπ₀ c 1).trans (mul_one (c : Om l))))
  have he0 : π₀ e ≠ 0 := fun h => by
    have h' : ι (π₀ e) = 1 := he
    rw [h, map_zero] at h'
    exact zero_ne_one h'
  refine eq_zero_of_translate α hα (fun n => frobUr l ^ n) (fun n => phiD P ρ ^ n) (fun n => ?_)
    (phiD_pow_mulD P ρ) e x (fun n => hk _ (hx n)) fun I hI => exists_translate LL I hI e he0
  rw [End.coe_pow]
  exact (phiD_injective P ρ).iterate n

end GlobalTheory.PstFaithful
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
open Formalism.IndefR Formalism.L2.DIV

namespace GlobalTheory

theorem classPres_extMem_extBij_isom : ∀ (G Γ : Type) [Group G] [Group Γ] (ι : Γ →* G) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ), P.ExtMem ∧ P.ExtBij ∧ P.Isom := by
  intro G Γ _ _ ι W _ _ K _ _ _ S σ ρ J χ P
  obtain ⟨h1, h2, h3, -⟩ := classPres_basic ι S σ ρ J χ P
  exact ⟨h1, h3, h2⟩

end GlobalTheory
end
