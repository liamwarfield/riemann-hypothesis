module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaProdEqOfEverywhereNormDiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitude
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralWittTheoremAlmostAllPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDual
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct Topology

namespace GlobalTheory.IdeleNormChar

open GlobalTheory.QuadSymbol

variable {K : Type} [Field K] [NumberField K]

def finEval (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infEval (w : InfinitePlace K) : AdeleRing (𝓞 K) K →* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl

def finComp : (AdeleRing (𝓞 K) K)ˣ →* FinFam K :=
  MonoidHom.pi fun v => Units.map (finEval v)

def infComp : (AdeleRing (𝓞 K) K)ˣ →* InfFam K :=
  MonoidHom.pi fun w => Units.map (infEval w)

theorem finComp_toUnits (t : Kˣ) : finComp (toUnits K (AdeleRing (𝓞 K) K) t) = finDiag K t :=
  funext fun _ => Units.ext rfl

theorem infComp_toUnits (t : Kˣ) : infComp (toUnits K (AdeleRing (𝓞 K) K) t) = infDiag K t :=
  funext fun _ => Units.ext rfl

theorem eventually_valued_eq_one (a : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  filter_upwards [(a : AdeleRing (𝓞 K) K).2.2, ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2.2]
    with v h3 h4
  have hmul : (a : AdeleRing (𝓞 K) K).2 v *
      ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
    congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one] at hm
  change Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1
  refine le_antisymm h3 ?_
  rw [← hm]
  exact mul_le_of_le_one_right' h4

theorem eventually_integral_form (δ : K) (hδ : δ ≠ 0) (a : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
        ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 := by
  filter_upwards [eventually_valued_eq_one a,
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 2 two_ne_zero)).compl_mem_cofinite,
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 δ hδ)).compl_mem_cofinite] with v ha h2 hd
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not, Units.val_mk0] at h2 hd
  have key : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  exact GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit K v (algebraMap K _ δ) _
    (by rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]; exact (key _).trans h2)
    (by rw [key, hd]) ha

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L]


omit [NumberField L] in
theorem almostNorm_finComp (a : (AdeleRing (𝓞 K) K)ˣ) : AlmostNorm K L (finComp a) := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  refine Filter.eventually_cofinite.1 ((eventually_integral_form δ hδ0 a).mono ?_)
  rintro v ⟨x, -, y, -, h⟩
  exact (mem_normGroup_iff_form b h0 h1).2 ⟨x, y, h⟩


omit [NumberField L] in
theorem mem_normGroup_iff_everywhereNorm (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ normGroup K L (AdeleRing (𝓞 K) K) ↔ EverywhereNorm K L (finComp a) (infComp a) := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  rw [mem_normGroup_iff_form b h0 h1]
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨fun v => (mem_normGroup_iff_form b h0 h1).2
        ⟨x.2 v, y.2 v, congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) h⟩,
      fun w => (mem_normGroup_iff_form b h0 h1).2
        ⟨x.1 w, y.1 w, congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) h⟩⟩
  · rintro ⟨hf, hi⟩
    have hc := eventually_integral_form δ hδ0 a
    have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K,
        ((∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
          ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2) →
          x ∈ v.adicCompletionIntegers K ∧ y ∈ v.adicCompletionIntegers K) ∧
        ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 := by
      intro v
      by_cases hv : ∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
          ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2
      · obtain ⟨x, hx, y, hy, h⟩ := hv
        exact ⟨x, y, fun _ => ⟨hx, hy⟩, h⟩
      · obtain ⟨x, y, h⟩ := (mem_normGroup_iff_form b h0 h1).1 (hf v)
        exact ⟨x, y, fun h' => absurd h' hv, h⟩
    choose x y hxy h using hloc
    choose r s hr using fun w => (mem_normGroup_iff_form b h0 h1).1 (hi w)
    let X : FiniteAdeleRing (𝓞 K) K := ⟨x, hc.mono fun v hv => (hxy v hv).1⟩
    let Y : FiniteAdeleRing (𝓞 K) K := ⟨y, hc.mono fun v hv => (hxy v hv).2⟩
    refine ⟨((r : InfiniteAdeleRing K), X), ((s : InfiniteAdeleRing K), Y), Prod.ext ?_ ?_⟩
    · funext w
      exact hr w
    · exact FiniteAdeleRing.ext K fun v => h v

def normSign : (AdeleRing (𝓞 K) K)ˣ →* ℤˣ :=
  MonoidHom.mk' (fun a => etaProd K L (finComp a) (infComp a)) fun a b => by
    obtain ⟨h1, h2⟩ := localCharacters K L
    unfold etaProd
    simp only [map_mul, Pi.mul_apply, h1, h2]
    rw [finprod_mul_distrib (almostNorm_finComp L a).finite_mulSupport
      (almostNorm_finComp L b).finite_mulSupport, Finset.prod_mul_distrib, mul_mul_mul_comm]

theorem normSign_eq_one_iff (a : (AdeleRing (𝓞 K) K)ˣ) :
    normSign L a = 1 ↔ ∃ t : Kˣ, a / toUnits K (AdeleRing (𝓞 K) K) t ∈ normGroup K L (AdeleRing (𝓞 K) K) := by
  refine ((exactSequence K L).2.2.1 _ _ (almostNorm_finComp L a)).symm.trans (exists_congr fun t => ?_)
  rw [mem_normGroup_iff_everywhereNorm, map_div, map_div, finComp_toUnits, infComp_toUnits]

theorem normSign_of_mem {a : (AdeleRing (𝓞 K) K)ˣ} (h : a ∈ normGroup K L (AdeleRing (𝓞 K) K)) :
    normSign L a = 1 :=
  (normSign_eq_one_iff L a).2 ⟨1, by rwa [map_one, div_one]⟩

theorem normSign_toUnits (t : Kˣ) : normSign L (toUnits K (AdeleRing (𝓞 K) K) t) = 1 :=
  (normSign_eq_one_iff L _).2 ⟨t, by rw [div_self']; exact one_mem _⟩

theorem exists_normSign_ne_one : ∃ a : (AdeleRing (𝓞 K) K)ˣ, normSign L a ≠ 1 := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  obtain ⟨a, ha⟩ := GlobalTheory.QNorm.exists_idele_not_mul_norm K δ hδ
  refine ⟨a, fun h => ?_⟩
  obtain ⟨t, ht⟩ := (normSign_eq_one_iff L a).1 h
  obtain ⟨x, y, e⟩ := (mem_normGroup_iff_form b h0 h1).1 ht
  refine ha t x y ?_
  rw [← e]
  exact (congrArg Units.val (mul_div_cancel (toUnits K (AdeleRing (𝓞 K) K) t) a)).symm

theorem eventually_normSign : ∀ᶠ a in 𝓝 (1 : (AdeleRing (𝓞 K) K)ˣ), normSign L a = 1 := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  filter_upwards [GlobalTheory.QNorm.norm_form_mem_nhds_one K δ hδ0] with a ha
  exact normSign_of_mem L ((mem_normGroup_iff_form b h0 h1).2 ha)

def signToCircle : ℤˣ →* Circle where
  toFun u := if u = 1 then 1 else -1
  map_one' := if_pos rfl
  map_mul' u u' := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or u' with rfl | rfl <;> simp

theorem circle_neg_one_ne_one : (-1 : Circle) ≠ 1 := fun h => by
  have := congrArg (fun z : Circle => (z : ℂ)) h
  norm_num at this

theorem eq_signToCircle_comp {G : Type} [Group G] (ε : G →* ℤˣ) (η : G →* Circle)
    (h : ∀ a, ε a = 1 → η a = 1) (hη : η ≠ 1) : η = signToCircle.comp ε := by
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push Not at hh
    exact hη (MonoidHom.ext hh)
  have hεb : ε b = -1 := (Int.units_eq_one_or _).resolve_left fun e => hb (h b e)
  refine MonoidHom.ext fun a => ?_
  rcases Int.units_eq_one_or (ε a) with e | e
  · rw [MonoidHom.comp_apply, e, map_one, h a e]
  · have h1 : η a * η b = 1 := by rw [← map_mul]; exact h _ (by rw [map_mul, e, hεb]; simp)
    have h2 : η a * η a = 1 := by rw [← map_mul]; exact h _ (by rw [map_mul, e]; simp)
    have h3 : (η a : ℂ) * η a = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h2
    rw [MonoidHom.comp_apply, e]
    change η a = if (-1 : ℤˣ) = 1 then 1 else -1
    rw [if_neg (by decide)]
    rcases mul_self_eq_one_iff.1 h3 with h4 | h4
    · have h5 : η a = 1 := Circle.ext h4
      rw [h5, one_mul] at h1
      exact absurd h1 hb
    · exact Circle.ext h4

theorem globalNormIndexTwo : Formalism.D.Classical.GlobalNormIndexTwo := by
  intro F E _ _ _ _ _ h2
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  refine ⟨signToCircle.comp (normSign E), ⟨?_, fun a => ?_, fun x => ?_, fun e => ?_⟩, ?_⟩
  · refine continuous_of_continuousAt_one _ ((continuousAt_const (y := (1 : Circle))).congr ?_)
    filter_upwards [eventually_normSign (K := F) E] with a ha
    rw [MonoidHom.comp_apply, ha, map_one]
  · exact (congrArg signToCircle (normSign_toUnits E a)).trans (map_one _)
  · exact (congrArg signToCircle (normSign_of_mem E ⟨x, rfl⟩)).trans (map_one _)
  · obtain ⟨a, ha⟩ := exists_normSign_ne_one (K := F) E
    have h : signToCircle (normSign E a) = 1 := DFunLike.congr_fun e a
    exact circle_neg_one_ne_one ((if_neg ha).symm.trans h)
  · rintro η ⟨-, h1, h3, h4⟩
    refine eq_signToCircle_comp _ η (fun a ha => ?_) h4
    obtain ⟨t, x, hx⟩ := (normSign_eq_one_iff E a).1 ha
    rw [← div_mul_cancel a (toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h3 x, one_mul]
    exact h1 t

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta in
theorem existsUnique_isEta : ∀ D : D7, ∃! η : (AF D.host.F)ˣ →* Circle, IsEta D η := fun D =>
  globalNormIndexTwo D.host.F D.host.E D.sp.cm.deg2

end GlobalTheory.IdeleNormChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoordSymm
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.OrientedCoord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mul_gramInv (V : HSp D) : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedSmall.gramInv_mul V)

def coord (S T : HSp D) : WO S T ≃+ WA S T where
  toFun := toTWsmall S T
  invFun y := HMul.hMul (y : Matrix (Fin S.rank) (Fin T.rank) (AE D))ᵀ (S.gram.map (incA D))
  left_inv x := by
    simp only [toTWsmall, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc, GlobalTheory.OrientedSmall.gramInv_mul, Matrix.mul_one]
  right_inv y := by
    simp only [toTWsmall]
    rw [Matrix.mul_assoc, mul_gramInv, Matrix.mul_one, Matrix.transpose_transpose]
  map_add' x y := by
    simp only [toTWsmall]
    rw [Matrix.add_mul, Matrix.transpose_add]

theorem coord_apply (S T : HSp D) (x : WO S T) :
    coord S T x = (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) ((S.gram⁻¹).map (incA D)))ᵀ := rfl

theorem coord_symm_apply (S T : HSp D) (y : WA S T) :
    (coord S T).symm y = HMul.hMul (y : Matrix (Fin S.rank) (Fin T.rank) (AE D))ᵀ (S.gram.map (incA D)) := rfl

theorem continuous_coord (S T : HSp D) : Continuous (coord S T) :=
  (continuous_id.matrix_mul continuous_const).matrix_transpose

theorem continuous_coord_symm (S T : HSp D) : Continuous (coord S T).symm :=
  continuous_id.matrix_transpose.matrix_mul continuous_const

theorem coord_ratW (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    coord S T (ratW T S γ) = ratW S T (γ * S.gram⁻¹)ᵀ := by
  rw [coord_apply]
  unfold ratW
  rw [← Matrix.map_mul, Matrix.transpose_map]

theorem coord_symm_ratW (S T : HSp D) (γ : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    (coord S T).symm (ratW S T γ) = ratW T S (γᵀ * S.gram) := by
  rw [coord_symm_apply]
  unfold ratW
  rw [Matrix.map_mul, Matrix.transpose_map]

theorem coord_map_zero (S T : HSp D) {R : Type} [CommRing R] (φ : AE D →+* R) (x : WO S T) (h : x.map φ = 0) :
    (coord S T x).map φ = 0 := by
  rw [coord_apply, Matrix.transpose_map, Matrix.map_mul, h, Matrix.zero_mul, Matrix.transpose_zero]

theorem coord_symm_map_zero (S T : HSp D) {R : Type} [CommRing R] (φ : AE D →+* R) (y : WA S T) (h : y.map φ = 0) :
    ((coord S T).symm y).map φ = 0 := by
  rw [coord_symm_apply, Matrix.map_mul, Matrix.transpose_map, h, Matrix.transpose_zero, Matrix.zero_mul]

theorem symplOH_eq (S T : HSp D) (hr : S.rank ≤ T.rank) (x y : WO S T) :
    symplOH S T x y = symplH S T (coord S T x) (coord S T y) := by
  unfold symplOH symplH
  rw [(GlobalTheory.OrientedSmall.bridgeSmall D S T hr).1 x y]
  rfl

theorem heisO_coord (S T : HSp D) (hr : S.rank ≤ T.rank) (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WA S T → ℂ) :
    heisO ψ S T w (fun x => f (coord S T x)) = fun x => Heisenberg₂ ψ S T (coord S T w) f (coord S T x) := by
  funext x
  simp only [heisO, Formalism.L2.Theta.Heisenberg₂, map_add (f := _), symplOH_eq S T hr]

theorem isThetaFunO_coord (S T : HSp D) (hr : S.rank ≤ T.rank) (ψ : AddChar (AF D.host.F) ℂ) (f : WA S T → ℂ) :
    IsThetaFunO ψ S T (fun x => f (coord S T x)) ↔ IsThetaFun ψ S T f := by
  have c1 := continuous_coord S T
  have c2 := continuous_coord_symm S T
  refine ⟨fun hf => ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩,
    fun hf => ⟨fun γ w => ?_, ?_, hf.cont.comp c1, fun k L hL h0 w => ?_⟩⟩
  · have := hf.quasi (γᵀ * S.gram) ((coord S T).symm w)
    rw [← coord_symm_ratW, symplOH_eq S T hr] at this
    simpa only [map_add (f := _), AddEquiv.apply_symm_apply] using this
  · obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (coord S T).symm.toAddMonoidHom, hU.preimage c2, fun u hu h0 => ?_⟩
    have := hfix ((coord S T).symm u) hu (coord_symm_map_zero S T _ u h0)
    rw [heisO_coord S T hr] at this
    funext y
    simpa only [AddEquiv.apply_symm_apply] using congrFun this ((coord S T).symm y)
  · simpa only [Function.comp_def, AddEquiv.apply_symm_apply] using hf.cont.comp c2
  · have := hf.smooth k ((coord S T).symm.toAddMonoidHom.comp L) (c2.comp hL)
      (fun t => coord_symm_map_zero S T _ _ (h0 t)) ((coord S T).symm w)
    simpa only [map_add (f := _), AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply] using this
  · have := hf.quasi (γ * S.gram⁻¹)ᵀ (coord S T w)
    rw [← coord_ratW, ← symplOH_eq S T hr] at this
    simpa only [map_add (f := _)] using this
  · obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (coord S T).toAddMonoidHom, hU.preimage c1, fun u hu h0 => ?_⟩
    rw [heisO_coord S T hr, hfix (coord S T u) hu (coord_map_zero S T _ u h0)]
  · have := hf.smooth k ((coord S T).toAddMonoidHom.comp L) (c1.comp hL)
      (fun t => coord_map_zero S T _ _ (h0 t)) (coord S T w)
    simpa only [map_add (f := _), AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe] using this

theorem coord_gen (S T : HSp D) (β : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    coord S T (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * star (s i) * t j) := by
  rw [← AddEquiv.eq_symm_apply, coord_symm_apply]
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : incA D (S.gram k j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j := rfl
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  ring

theorem coord_mem_latVWS (S T : HSp D) (hr : S.rank ≤ T.rank) (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z)) : coord S T u ∈ latVWS S T Z := by
  have : latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z) ≤ (latVWS S T Z).comap (coord S T).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, fun v hv => h0 v (not_not.2 hv), a, ha, s, hs, t, ht, ?_⟩
    simp only [if_pos hr]
    exact coord_gen S T _ a s t
  exact this hu

theorem exists_coord : ∀ (D : D7) (S T : HSp D), S.rank ≤ T.rank → ∃ e : WO S T ≃+ WA S T, Continuous e ∧ Continuous e.symm ∧ (∀ x, e x = toTWsmall S T x) ∧ (∀ x, e x ∈ ratL S T ↔ x ∈ ratL T S) ∧ (∀ (a : AE D) (x : WO S T), e (a • x) = a • e x) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WA S T → ℂ), heisO ψ S T w (fun x => f (e x)) = fun x => Heisenberg₂ ψ S T (e w) f (e x)) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (f : WA S T → ℂ), IsThetaFunO ψ S T (fun x => f (e x)) ↔ IsThetaFun ψ S T f) ∧ ∀ (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T), u ∈ latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z) → e u ∈ latVWS S T Z := by
  intro D S T hr
  refine ⟨coord S T, continuous_coord S T, continuous_coord_symm S T, fun _ => rfl, fun x => ⟨?_, ?_⟩, fun a x => ?_,
    heisO_coord S T hr, isThetaFunO_coord S T hr, coord_mem_latVWS S T hr⟩
  · rintro ⟨γ, hγ⟩
    have hγ' : ratW S T γ = coord S T x := hγ
    refine ⟨γᵀ * S.gram, ?_⟩
    change ratW T S _ = x
    rw [← coord_symm_ratW, hγ', AddEquiv.symm_apply_apply]
  · rintro ⟨γ, rfl⟩
    exact ⟨(γ * S.gram⁻¹)ᵀ, (coord_ratW S T γ).symm⟩
  · rw [coord_apply, coord_apply, Matrix.smul_mul, Matrix.transpose_smul]

end GlobalTheory.OrientedCoord

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsResOfTameAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameResidue

open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E]

theorem locK_eq_of_congr (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : χ.TameAt P)
    (a b : 𝓞 E) (k l : Eˣ) (hk : (k : E) = a) (hl : (l : E) = b) (hb : b ∉ P.asIdeal)
    (hab : a - b ∈ P.asIdeal) : χ.locK P k = χ.locK P l := by
  have ha : a ∉ P.asIdeal := fun ha => hb (by simpa using P.asIdeal.sub_mem ha hab)
  have hva : P.valuation E (k : E) = 1 := by
    rw [hk]; exact (P.valuation_eq_one_iff_notMem (K := E)).2 ha
  have hvb : P.valuation E (l : E) = 1 := by
    rw [hl]; exact (P.valuation_eq_one_iff_notMem (K := E)).2 hb
  have hvd : P.valuation E ((k : E) - l) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : (k : E) - l = algebraMap (𝓞 E) E (a - b) := by rw [hk, hl, map_sub]
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_le_pow_iff_mem (a - b) 1).2 (by simpa using hab)
  have key : χ.locK P (k * l⁻¹) = 1 := by
    refine h (atFin P (k * l⁻¹)) ?_ ?_
    · show Valued.v ((((k * l⁻¹ : Eˣ) : E)) : P.adicCompletion E) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Units.val_mul, Units.val_inv_eq_inv_val, map_mul,
        map_inv₀, hva, hvb]
      simp
    · have e : ((atFin P (k * l⁻¹) : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1
          = algebraMap E (P.adicCompletion E) (((k : E) - l) * (l : E)⁻¹) := by
        have e2 : ((k : E) - l) * (l : E)⁻¹ = ((k * l⁻¹ : Eˣ) : E) - 1 := by
          rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ l.ne_zero]
        rw [e2, map_sub, map_one]
        rfl
      rw [e]
      show Valued.v (((((k : E) - l) * (l : E)⁻¹ : E)) : P.adicCompletion E) ≤ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_mul, map_inv₀, hvb]
      simpa using hvd
  rwa [map_mul, map_inv, mul_inv_eq_one] at key

theorem exists_lift (P : HeightOneSpectrum (𝓞 E)) (u : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ p : 𝓞 E × Eˣ, (p.2 : E) = p.1 ∧ (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ p.1 ∧ p.1 ∉ P.asIdeal := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 E ⧸ P.asIdeal)
  haveI : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have hn : a ∉ P.asIdeal := fun h => u.ne_zero (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
  have h0 : (a : E) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    exact hn (this ▸ P.asIdeal.zero_mem)
  exact ⟨(a, Units.mk0 (a : E) h0), rfl, ha.symm, hn⟩

theorem exists_res (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : χ.TameAt P) :
    ∃ c : (𝓞 E ⧸ P.asIdeal)ˣ →* ℂˣ, ∀ (a : 𝓞 E) (k : Eˣ) (u : (𝓞 E ⧸ P.asIdeal)ˣ), (k : E) = a →
      (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ a → c u = χ.locK P k := by
  choose f hf1 hf2 hf3 using exists_lift P
  have main : ∀ (a : 𝓞 E) (k : Eˣ) (u : (𝓞 E ⧸ P.asIdeal)ˣ), (k : E) = a →
      (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ a → χ.locK P (f u).2 = χ.locK P k := by
    intro a k u hk hu
    refine (locK_eq_of_congr χ P h a (f u).1 k (f u).2 hk (hf1 u) (hf3 u) ?_).symm
    rw [← Ideal.Quotient.eq, ← hu, ← hf2 u]
  refine ⟨MonoidHom.mk' (fun u => χ.locK P (f u).2) ?_, main⟩
  intro u v
  rw [← map_mul]
  refine main ((f u).1 * (f v).1) _ _ ?_ ?_
  · rw [Units.val_mul, hf1, hf1]; simp
  · rw [Units.val_mul, map_mul, ← hf2, ← hf2]

end GlobalTheory.TameResidue

theorem GlobalTheory.exists_isRes_of_tameAt : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (P : Pl D.host.E),
    χ.TameAt P → ∃ c, IsRes χ P c :=
  fun _ χ P h => GlobalTheory.TameResidue.exists_res χ P h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotForallNonemptyLocP
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.KudlaSiegelWeil

namespace GlobalTheory.SmallThetaModules

section Restricted

variable {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]

def AdmFun (s : ∀ i, N i) : Type := {l : ∀ i, N i →ₗ[ℂ] ℂ // {i | l i (s i) ≠ 1}.Finite}

def evFam (s : ∀ i, N i) (ξ : ∀ i, N i) : AdmFun s → ℂ := fun l => ∏ᶠ i, l.1 i (ξ i)

def RTens (s : ∀ i, N i) : Submodule ℂ (AdmFun s → ℂ) :=
  Submodule.span ℂ {z | ∃ ξ, Restr s ξ ∧ z = evFam s ξ}


open Classical in
def pureT (s : ∀ i, N i) (ξ : ∀ i, N i) : RTens s :=
  if h : Restr s ξ then ⟨evFam s ξ, Submodule.subset_span ⟨ξ, h, rfl⟩⟩ else 0

theorem coe_pureT {s ξ : ∀ i, N i} (h : Restr s ξ) : (pureT s ξ : AdmFun s → ℂ) = evFam s ξ := by
  unfold pureT; rw [dite_eq_left h]

omit [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] in
theorem restr_update [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (v : ι) (x : N v) :
    Restr s (Function.update ξ v x) := by
  refine (h.insert v).subset fun i hi => ?_
  by_cases hv : i = v
  · exact Or.inl hv
  · right
    simpa [Function.update_of_ne hv] using hi

theorem mulSupport_fin {s ξ : ∀ i, N i} (h : Restr s ξ) (l : AdmFun s) :
    (Function.mulSupport fun i => l.1 i (ξ i)).Finite := by
  refine (Set.Finite.union h l.2).subset fun i hi => ?_
  by_cases e : ξ i = s i
  · right
    simpa [e] using hi
  · exact Or.inl e

theorem evFam_update [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (l : AdmFun s) (v : ι) (x : N v) :
    evFam s (Function.update ξ v x) l = l.1 v x * ∏ᶠ (i) (_ : i ≠ v), l.1 i (ξ i) := by
  unfold evFam
  rw [← mul_finprod_cond_ne v (mulSupport_fin (restr_update h v x) l), Function.update_self]
  congr 1
  refine finprod_congr fun i => finprod_congr fun hi => ?_
  rw [Function.update_of_ne hi]

theorem pureT_mlin [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (v : ι) (c : ℂ) (x y : N v) :
    pureT s (Function.update ξ v (c • x + y)) =
      c • pureT s (Function.update ξ v x) + pureT s (Function.update ξ v y) := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, coe_pureT (restr_update h v _), coe_pureT (restr_update h v _),
    coe_pureT (restr_update h v _)]
  funext l
  simp only [Pi.add_apply, Pi.smul_apply, evFam_update h, map_add (f := _), map_smul, smul_eq_mul]
  ring

theorem pureT_span (s : ∀ i, N i) :
    Submodule.span ℂ {z | ∃ ξ, Restr s ξ ∧ z = pureT s ξ} = ⊤ := by
  apply Submodule.map_injective_of_injective (RTens s).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  change _ = Submodule.span ℂ _
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨ξ, h, rfl⟩, rfl⟩
    exact ⟨ξ, h, coe_pureT h⟩
  · rintro ⟨ξ, h, rfl⟩
    exact ⟨_, ⟨ξ, h, rfl⟩, coe_pureT h⟩

theorem pureT_sep (s : ∀ i, N i) (l : ∀ i, N i →ₗ[ℂ] ℂ) (hl : {i | l i (s i) ≠ 1}.Finite) :
    ∃ Λ : RTens s →ₗ[ℂ] ℂ, ∀ ξ, Restr s ξ → Λ (pureT s ξ) = ∏ᶠ i, l i (ξ i) :=
  ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : AdmFun s => ℂ) (show AdmFun s from ⟨l, hl⟩)).comp (RTens s).subtype,
    fun _ h => congrFun (coe_pureT h) (show AdmFun s from ⟨l, hl⟩)⟩

theorem exists_lift {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (m : ∀ i, M i)
    {S : Type} [AddCommGroup S] [Module ℂ S] (pu : (∀ i, M i) → S)
    (hsep : ∀ l : ∀ i, M i →ₗ[ℂ] ℂ, {i | l i (m i) ≠ 1}.Finite →
      ∃ Λ : S →ₗ[ℂ] ℂ, ∀ φ, Restr m φ → Λ (pu φ) = ∏ᶠ i, l i (φ i))
    (s : ∀ i, N i) (p : ∀ i, M i →ₗ[ℂ] N i) :
    ∃ P : S →ₗ[ℂ] RTens s, ∀ φ, Restr m φ → P (pu φ) = pureT s fun i => p i (φ i) := by
  by_cases hp : {i | p i (m i) ≠ s i}.Finite
  · have h1 : ∀ l : AdmFun s, ∃ Λ : S →ₗ[ℂ] ℂ, ∀ φ, Restr m φ → Λ (pu φ) = ∏ᶠ i, l.1 i (p i (φ i)) := by
      intro l
      refine hsep (fun i => (l.1 i).comp (p i)) ((hp.union l.2).subset fun i hi => ?_)
      by_cases e : p i (m i) = s i
      · right
        simpa [e] using hi
      · exact Or.inl e
    choose Λ hΛ using h1
    obtain ⟨r, hr⟩ := (RTens s).subtype.exists_leftInverse_of_injective (RTens s).ker_subtype
    refine ⟨r.comp (LinearMap.pi Λ), fun φ hφ => ?_⟩
    have h2 : Restr s fun i => p i (φ i) := by
      refine (Set.Finite.union hφ hp).subset fun i hi => ?_
      by_cases e : φ i = m i
      · right
        simpa [e] using hi
      · exact Or.inl e
    have h3 : LinearMap.pi Λ (pu φ) = (RTens s).subtype (pureT s fun i => p i (φ i)) := by
      rw [Submodule.subtype_apply, coe_pureT h2]
      funext l
      exact hΛ l φ hφ
    rw [LinearMap.comp_apply, h3, ← LinearMap.comp_apply, hr, LinearMap.id_apply]
  · refine ⟨0, fun φ hφ => ?_⟩
    have h2 : ¬ Restr s fun i => p i (φ i) := by
      intro h
      refine hp ((Set.Finite.union hφ h).subset fun i hi => ?_)
      by_cases e : φ i = m i
      · right
        simpa [e] using hi
      · exact Or.inl e
    unfold pureT
    rw [dite_eq_right h2, LinearMap.zero_apply]

end Restricted

variable {D : D7} {X : ThetaX D}

section Collapse

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Collapse

end GlobalTheory.SmallThetaModules

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVector
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVector
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.AdelicWitt

theorem qR_ratTup {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (b : Module.Basis (Fin 2) F E) (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F)
    (h : hE σ J (x 0) (x 0) = algebraMap F E β) :
    qR R σ J (ratTup (F := F) R x 0) = algebraMap F R β := by
  have h1 : hR R σ J (ratTup (F := F) R x 0) (ratTup (F := F) R x 0) =
      inclR (F := F) R (hE σ J (x 0) (x 0)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, hE, Formalism.UG.hform, map_sum, map_mul, ratTup, JR, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
  have h2 : inclR (F := F) R (algebraMap F E β) = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  rw [qR, h1, h, h2, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b),
    Fintype.card_fin, ← map_nsmul, ← map_mul]
  congr 1
  rw [nsmul_eq_mul]; push_cast; field_simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem prInf_sigR (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    prInf (sigR (AF F) σ z) = sigR (Ainf F) σ (prInf z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add a c ha hc => simp only [map_add (f := _), ha, hc]

omit [NumberField E] in
theorem prV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    prV v (sigR (AF F) σ z) = sigR (Fv F v) σ (prV v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add a c ha hc => simp only [map_add (f := _), ha, hc]

omit [NumberField E] in
theorem prInf_inclR (e : E) : prInf (inclR (F := F) (AF F) e) = inclR (F := F) (Ainf F) e := by
  simp [prInf, inclR]

omit [NumberField E] in
theorem prV_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV v (inclR (F := F) (AF F) e) = inclR (F := F) (Fv F v) e := by
  simp [prV, inclR]

theorem ext_comp {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ} (X Y : Fin n → Fin M → AF F ⊗[F] E)
    (hi : ∀ a i, prInf (X a i) = prInf (Y a i))
    (hv : ∀ (v : HeightOneSpectrum (𝓞 F)) a i, prV v (X a i) = prV v (Y a i)) : X = Y := by
  apply (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M).1.injective
  refine Prod.ext ?_ ?_
  · funext a i; exact hi a i
  · funext v a i; exact hv v a i

theorem mat_ext {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (X Y : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    (hi : X.map prInf = Y.map prInf)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), X.map (prV v) = Y.map (prV v)) : X = Y :=
  ext_comp b X Y (fun a i => congrFun (congrFun hi a) i) (fun v a i => congrFun (congrFun (hv v) a) i)

theorem exists_mat {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (Xi : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E))
    (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, Xv v i j ∈ intV b v) :
    ∃ X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E), X.map prInf = Xi ∧ ∀ v, X.map (prV v) = Xv v := by
  have := ((Set.ext_iff.1 (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b M M).2.1) (Xi, Xv)).2 h
  obtain ⟨X, hX⟩ := this
  exact ⟨X, congrArg Prod.fst hX, fun v => congrFun (congrArg Prod.snd hX) v⟩

theorem map_unit {A B : Type} [CommRing A] [CommRing B] {M : ℕ} (φ : A →+* B) (s : A →+* A)
    (t : B →+* B) (h : ∀ z, φ (s z) = t (φ z)) (X J : Matrix (Fin M) (Fin M) A) :
    (Formalism.UG.cT s X * J * X).map φ = Formalism.UG.cT t (X.map φ) * J.map φ * X.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  exact h _

theorem exists_HA {d : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (gi : HA (Ainf F) σ J)
    (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j,
      (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧
        (HA.mat (Fv F v) σ J (gv v)⁻¹).val i j ∈ intV b v) :
    ∃ g : HA (AF F) σ J, (HA.mat (AF F) σ J g).val.map prInf = (HA.mat (Ainf F) σ J gi).val ∧
      ∀ v, (HA.mat (AF F) σ J g).val.map (prV v) = (HA.mat (Fv F v) σ J (gv v)).val := by
  obtain ⟨X, hXi, hXv⟩ := exists_mat b (HA.mat (Ainf F) σ J gi).val
    (fun v => (HA.mat (Fv F v) σ J (gv v)).val) (h.mono fun v hv i j => (hv i j).1)
  obtain ⟨Y, hYi, hYv⟩ := exists_mat b (HA.mat (Ainf F) σ J gi).inv
    (fun v => (HA.mat (Fv F v) σ J (gv v)).inv) (h.mono fun v hv i j => (hv i j).2)
  have hXY : X * Y = 1 := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [Matrix.map_mul, hXi, hYi, Units.val_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hXv, hYv, Units.val_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hYX : Y * X = 1 := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [Matrix.map_mul, hXi, hYi, Units.inv_val, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hXv, hYv, Units.inv_val, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJi : (JR (F := F) (AF F) J).map prInf = JR (F := F) (Ainf F) J := by
    ext i j; exact prInf_inclR _
  have hJv : ∀ v, (JR (F := F) (AF F) J).map (prV v) = JR (F := F) (Fv F v) J := by
    intro v; ext i j; exact prV_inclR v _
  have hU : Formalism.UG.cT (sigR (AF F) σ) X * JR (F := F) (AF F) J * X = JR (F := F) (AF F) J := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [map_unit _ _ _ (prInf_sigR σ), hXi, hJi]
      exact (show HR (Ainf F) σ J from gi).2
    · rw [map_unit _ _ _ (prV_sigR σ v), hXv, hJv]
      exact (show HR (Fv F v) σ J from gv v).2
  exact ⟨(show HR (AF F) σ J from ⟨⟨X, Y, hXY, hYX⟩, hU⟩), hXi, hXv⟩

theorem witt_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ y : (Fin 1 → Fin M → AF F ⊗[F] E), qR (AF F) σ J (y 0) = algebraMap F (AF F) β → ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y := by
  intro F E _ _ _ _ _ σ hCM M J x β hJ hβ hx y hy
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hCM.2.2.1
  obtain ⟨hyi, hyv⟩ := ((GlobalTheory.T.hermitianQuadratic_unitary_local_components F E σ M J).1 (y 0) β).1 hy
  have hu : IsUnit β := hβ.isUnit
  obtain ⟨gi, hgi⟩ := GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq F E σ hCM (Ainf F) (GlobalTheory.T.isNiceLocalFieldProductRing_infiniteAdeles_completions F).1 M J hJ
    (algebraMap F _ β) (ratTup (F := F) (Ainf F) x) (projInf y) (hu.map _)
    (qR_ratTup b _ σ J x β hx) hyi
  have hlat : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, projV v (projFin y) ∈ latV b v := by
    have h := (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E 2 b 1 M).2.1 ▸ Set.mem_range_self (f := fun X : (Fin 1 → Fin M → AF F ⊗[F] E) =>
      (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) y
    exact h
  have hae := GlobalTheory.T.integral_witt_theorem_almost_all_places F E σ hCM 2 b M J x β hJ hβ hx
  let P : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J → Prop := fun v g => ∀ i j,
      (HA.mat (Fv F v) σ J g).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J g⁻¹).val i j ∈ intV b v
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : HA (Fv F v) σ J,
      g • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧
      ((∃ g' : HA (Fv F v) σ J, g' • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧ P v g') →
        P v g) := by
    intro v
    by_cases h : ∃ g' : HA (Fv F v) σ J,
        g' • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧ P v g'
    · obtain ⟨g, h1, h2⟩ := h
      exact ⟨g, h1, fun _ => h2⟩
    · obtain ⟨g, hg⟩ := GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq F E σ hCM (Fv F v) ((GlobalTheory.T.isNiceLocalFieldProductRing_infiniteAdeles_completions F).2 v) M J hJ
        (algebraMap F _ β) (ratTup (F := F) (Fv F v) x) (projV v (projFin y)) (hu.map _)
        (qR_ratTup b _ σ J x β hx) (hyv v)
      exact ⟨g, hg, fun h' => absurd h' h⟩
  choose gv hgv hP using hloc
  obtain ⟨g, hi, hv⟩ := exists_HA b σ J gi gv (by
    filter_upwards [hlat, hae] with v h1 h2
    exact hP v (h2 _ h1 (hyv v)))
  refine ⟨g, ext_comp b _ _ (fun a i => ?_) (fun v a i => ?_)⟩
  · have h1 := congrFun (congrFun hgi a) i
    rw [projInf_apply] at h1
    rw [← h1]
    show prInf ((HA.mat (AF F) σ J g).val.mulVec (ratTup (F := F) (AF F) x a) i) =
      (HA.mat (Ainf F) σ J gi).val.mulVec (ratTup (F := F) (Ainf F) x a) i
    rw [RingHom.map_mulVec, hi]
    exact congrArg (fun w => (HA.mat (Ainf F) σ J gi).val.mulVec w i)
      (funext fun k => prInf_inclR (x a k))
  · have h1 := congrFun (congrFun (hgv v) a) i
    rw [projV_apply] at h1
    rw [← h1]
    show prV v ((HA.mat (AF F) σ J g).val.mulVec (ratTup (F := F) (AF F) x a) i) =
      (HA.mat (Fv F v) σ J (gv v)).val.mulVec (ratTup (F := F) (Fv F v) x a) i
    rw [RingHom.map_mulVec, hv]
    exact congrArg (fun w => (HA.mat (Fv F v) σ J (gv v)).val.mulVec w i)
      (funext fun k => prV_inclR v (x a k))

end GlobalTheory.AdelicWitt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVectorStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_theorem_adelic_one_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ y : (Fin 1 → Fin M → AF F ⊗[F] E), qR (AF F) σ J (y 0) = algebraMap F (AF F) β → ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y := by
  first | exact @GlobalTheory.AdelicWitt.witt_adelic | exact GlobalTheory.AdelicWitt.witt_adelic | (intros; apply GlobalTheory.AdelicWitt.witt_adelic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendLineBundleFactorial
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ExtendLineBundleComponents

theorem exists_integral_components (X : Scheme.{0}) [IsLocallyNoetherian X] [CompactSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) :
    ∃ (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) ∧ (∀ x, ∃ a, x ∈ V a) ∧
      ∀ a, IsIntegral (V a).toScheme ∧ CompactSpace (V a).toScheme := by
  have : IsNoetherian X := {}
  have hfin := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X))
  have heq : ∀ (x : X) (Z W : Set X), Z ∈ irreducibleComponents X → W ∈ irreducibleComponents X →
      x ∈ Z → x ∈ W → Z = W := by
    intro x Z W hZ hW hxZ hxW
    have := hX x
    exact GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents_of_isDomain hZ hW hxZ hxW
  have hopen : ∀ Z ∈ irreducibleComponents X, IsOpen Z := fun Z hZ => by
    have e : Zᶜ = ⋃ W ∈ irreducibleComponents X \ {Z}, W := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
      constructor
      · intro hx
        refine ⟨_, ⟨irreducibleComponent_mem_irreducibleComponents x, fun h ↦ hx ?_⟩,
          mem_irreducibleComponent⟩
        exact (show irreducibleComponent x = Z from h) ▸ mem_irreducibleComponent
      · rintro ⟨W, ⟨hW, hne⟩, hxW⟩ hxZ
        exact hne (heq x W Z hW hZ hxW hxZ)
    rw [← isClosed_compl_iff, e]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have : IsReduced X := isReduced_of_isReduced_stalk _
  let V : irreducibleComponents X → X.Opens := fun Z => ⟨Z.1, hopen Z.1 Z.2⟩
  refine ⟨irreducibleComponents X, V, fun a b x ha hb => Subtype.ext (heq x a b a.2 b.2 ha hb),
    fun x => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent⟩,
    fun a => ?_⟩
  have : IrreducibleSpace (V a).toScheme := Subtype.irreducibleSpace a.2.1
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
  exact isCompact_iff_compactSpace.mp (isClosed_of_mem_irreducibleComponents a.1 a.2).isCompact

theorem uniqueFactorizationMonoid_stalk_toScheme (X : Scheme.{0}) (U : X.Opens)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (y : U.toScheme) :
    UniqueFactorizationMonoid (U.toScheme.presheaf.stalk y) :=
  MulEquiv.uniqueFactorizationMonoid
    (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv (hX _)

end GlobalTheory.ExtendLineBundleComponents


open GlobalTheory.ExtendLineBundleComponents GlobalTheory.GenSpread in
theorem GlobalTheory.exists_lineBundle_extension_of_isDomain : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X]
    [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, IsDomain (X.presheaf.stalk x)) →
    (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB →
    ∃ L' : LB X, L'.IsLB ∧ LBIso (L'.pull j) L := by
  intro X Y _ _ j hj hdom hufm L hL
  obtain ⟨A, V, hd, hc, hV⟩ := exists_integral_components X hdom
  have key : ∀ a, ∃ M : LB (V a).toScheme, M.IsLB ∧
      LBIso (M.pull (j ∣_ V a)) (L.pull (j ⁻¹ᵁ V a).ι) := by
    intro a
    have := (hV a).1
    have := (hV a).2
    obtain ⟨M, hM, φ, hφ⟩ := GlobalTheory.exists_lineBundle_extension (V a).toScheme (j ⁻¹ᵁ V a).toScheme
      (j ∣_ V a) inferInstance (uniqueFactorizationMonoid_stalk_toScheme X (V a) hufm)
      (L.pull (j ⁻¹ᵁ V a).ι) (pull_isLB hL _)
    exact ⟨M, hM, φ, hφ⟩
  choose M hM hML using key
  obtain ⟨N, hN, hNM⟩ := GlobalTheory.T.exists_lineBundle_glue_disjoint_cover X A V hd hc M hM
  refine ⟨N, hN, GlobalTheory.T.lbIso_of_lbIso_on_disjoint_cover Y A (fun a => j ⁻¹ᵁ V a) (fun a b y ha hb => hd a b _ ha hb)
    (fun y => hc (j y)) _ _ (pull_isLB hN j) hL fun a => ?_⟩
  have e1 : LBIso ((N.pull j).pull (j ⁻¹ᵁ V a).ι) ((N.pull (V a).ι).pull (j ∣_ V a)) :=
    LBIso.trans (pull_isLB (pull_isLB hN j) _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hN _ rfl).symm (lbIso_pull_pull hN _ (morphismRestrict_ι j (V a)).symm)
  have e2 : LBIso ((N.pull (V a).ι).pull (j ∣_ V a)) ((M a).pull (j ∣_ V a)) :=
    lbIso_pullback (hNM a) _
  exact LBIso.trans (pull_isLB (pull_isLB hN j) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hL _) e1
    (LBIso.trans (pull_isLB (pull_isLB hN _) _) (pull_isLB (hM a) _) (pull_isLB hL _) e2 (hML a))
end
end
