module

public import GroundTheory.GlobalFields.TateThesis.TateMain
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite

@[expose] public section

section -- merged from GroundTheory.GlobalFields.TateThesis.HeckeTheoremTrivial
section -- merged from GroundTheory.GlobalFields.TateThesis.HeckeTheoremConj
section -- merged from GroundTheory.GlobalFields.TateThesis.HeckeTheoremScaling
section -- merged from GroundTheory.GlobalFields.TateThesis.TateMainUnique
open NumberField Topology Filter _root_.Complex Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem eqOn_of_differentiableOn_of_eq_globalZeta {F : 𝔸[K] → ℂ} {χ : HeckeCharacter K}
    {S : Set ℂ} (hS : S.Finite) (hSre : ∀ z ∈ S, z.re ≤ 1) {G H : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G Sᶜ) (hH : DifferentiableOn ℂ H Sᶜ)
    (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s)
    (hHZ : ∀ s : ℂ, 1 < s.re → H s = globalZeta F χ s) : EqOn G H Sᶜ := by
  have hopen : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  have hU : IsPreconnected Sᶜ :=
    (hS.countable.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have h2 : (2 : ℂ) ∈ Sᶜ := fun h ↦ by
    have := hSre 2 h
    norm_num at this
  have heq : G =ᶠ[𝓝 (2 : ℂ)] H :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)) fun s hs ↦ (hGZ s hs).trans (hHZ s hs).symm
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hopen)
    (hH.analyticOnNhd hopen) hU h2 heq

theorem eq_tateZeta_of_differentiable {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {χ : HeckeCharacter K} (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s) :
    G = tateZeta F χ := by
  have h := eqOn_of_differentiableOn_of_eq_globalZeta (S := ∅) finite_empty (by simp)
    hG.differentiableOn (differentiable_tateZeta hF hχ).differentiableOn hGZ
    fun s hs ↦ tateZeta_eq_globalZeta hF χ hs
  funext s
  exact h (by simp)

theorem eqOn_tateZeta_of_differentiableOn {χ : HeckeCharacter K} {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G {-((τ : ℂ) * I), 1 - (τ : ℂ) * I}ᶜ)
    (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s) :
    EqOn G (tateZeta F χ) {-((τ : ℂ) * I), 1 - (τ : ℂ) * I}ᶜ := by
  refine eqOn_of_differentiableOn_of_eq_globalZeta (toFinite _) ?_ hG ?_ hGZ
    fun s hs ↦ tateZeta_eq_globalZeta hF χ hs
  · intro z hz
    rcases hz with rfl | rfl <;> simp
  · intro s hs
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
    exact (differentiableAt_tateZeta hτ hF hs.1 hs.2).differentiableWithinAt

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.TateThesis.EulerFactorsFourier
open NumberField InfinitePlace IsDedekindDomain MeasureTheory _root_.Complex WithZero
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem differentIdeal_ne_bot : differentIdeal ℤ (𝓞 K) ≠ ⊥ :=
  FractionalIdeal.coeIdeal_ne_zero.1 coe_differentIdeal_ne_zero

def differentUnit : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  idealUnit (differentIdeal ℤ (𝓞 K)) differentIdeal_ne_bot

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem exists_ofFinite_toFractionalIdeal_eq :
    ∃ δ : (FiniteAdeleRing (𝓞 K) K)ˣ, toFractionalIdeal (ofFinite δ) =
      idealUnit χ.conductor χ.conductor_ne_bot * differentUnit := by
  obtain ⟨x, hx⟩ := toFractionalIdeal_surjective (K := K)
    (idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
  refine ⟨toFinite K x, ?_⟩
  rw [← hx, toFractionalIdeal_eq_iff]
  intro v
  rw [count_toFractionalIdeal]
  rfl

theorem valued_of_toFractionalIdeal_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((δ : FiniteAdeleRing (𝓞 K) K) v) = WithZero.exp (-(χ.condExp v + differentExp v)) := by
  rw [valued_eq_exp_ord, ← count_toFractionalIdeal, hδ, Units.val_mul,
    FractionalIdeal.count_mul K v (idealUnit χ.conductor χ.conductor_ne_bot).ne_zero
      (differentUnit (K := K)).ne_zero]
  rfl

def fourierConst (δ : (FiniteAdeleRing (𝓞 K) K)ˣ) : ℂ :=
  (∏ w, (-I) ^ (χ.infiniteWeight w).natAbs) *
    finiteFourier K χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)

theorem fourierConst_ne_zero {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    χ.fourierConst δ ≠ 0 :=
  mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ ↦ pow_ne_zero _ (neg_ne_zero.2 I_ne_zero))
    (χ.finiteFourier_finiteTestFun_ne_zero δ (χ.valued_of_toFractionalIdeal_eq hδ))

theorem adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (y : 𝔸[K]) :
    adelicFourier K χ.testFunction y = χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y) := by
  have hy1 : (ofFinite δ • y).1 = y.1 := by
    change (1 : InfiniteAdeleRing K) * y.1 = y.1
    exact one_mul _
  have hy2 : (ofFinite δ • y).2 = (δ : FiniteAdeleRing (𝓞 K) K) * y.2 := rfl
  rw [testFunction, adelicFourier_schwartzBruhatTensor, schwartzBruhatTensor,
    mixedFourierSchwartz_apply, χ.mixedFourier_infiniteSchwartz,
    χ.finiteFourier_finiteTestFun δ (χ.valued_of_toFractionalIdeal_eq hδ) y.2, testFunction,
    schwartzBruhatTensor, hy1, hy2, fourierConst]
  ring

end HeckeCharacter

end

end GroundTheory.Global
end

open NumberField InfinitePlace IsDedekindDomain MeasureTheory _root_.Complex Topology Filter Set
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem ofReal_inv_cpow_of_pos {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ s = (r : ℂ) ^ (-s) := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne), cpow_neg]

theorem globalZeta_comp_smul (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (a : IdeleGroup K) (s : ℂ) :
    globalZeta (fun y ↦ F (a • y)) χ s =
      (χ.toIdele a : ℂ)⁻¹ * ((ideleModule K a : ℝ) : ℂ) ^ (-s) * globalZeta F χ s := by
  unfold globalZeta
  have h := integral_mul_left_eq_self (μ := ideleMeasure K)
    (fun x : IdeleGroup K ↦ F (a • (x : 𝔸[K])) * (χ.toIdele x : ℂ) *
      ((ideleModule K x : ℝ) : ℂ) ^ s) a⁻¹
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  have h1 : a • ((a⁻¹ * x : IdeleGroup K) : 𝔸[K]) = (x : 𝔸[K]) := by
    rw [Units.smul_def, smul_eq_mul, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  have h2 : ((ideleModule K (a⁻¹ * x) : ℝ) : ℂ) ^ s =
      ((ideleModule K a : ℝ) : ℂ) ^ (-s) * ((ideleModule K x : ℝ) : ℂ) ^ s := by
    rw [map_mul, map_inv, Positive.val_mul, Positive.coe_inv, ofReal_mul,
      mul_cpow_ofReal_nonneg (inv_nonneg.2 (ideleModule K a).2.le) (ideleModule K x).2.le,
      ofReal_inv_cpow_of_pos (ideleModule K a).2]
  beta_reduce
  rw [h1, h2]
  simp only [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
  ring

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def discrNormConductor : ℝ := |(discr K : ℝ)| * (Ideal.absNorm χ.conductor : ℝ)

theorem discrNormConductor_pos : 0 < χ.discrNormConductor := by
  refine mul_pos (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))) (Nat.cast_pos.2 ?_)
  exact Nat.pos_of_ne_zero fun h ↦ χ.conductor_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem discrNormConductor_inv : χ⁻¹.discrNormConductor = χ.discrNormConductor := by
  rw [discrNormConductor, discrNormConductor, conductor_inv]

theorem ideleModule_ofFinite_of_toFractionalIdeal_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    (ideleModule K (ofFinite δ) : ℝ) = χ.discrNormConductor⁻¹ := by
  have hI : χ.conductor * differentIdeal ℤ (𝓞 K) ≠ ⊥ :=
    mul_ne_zero χ.conductor_ne_bot differentIdeal_ne_bot
  have hunit : idealUnit χ.conductor χ.conductor_ne_bot * differentUnit = idealUnit _ hI := by
    ext
    simp [idealUnit, differentUnit, FractionalIdeal.coeIdeal_mul]
  have hpos : ∀ v, 0 ≤ ord v (ofFinite δ) := fun v ↦ by
    rw [← count_toFractionalIdeal, hδ, hunit]
    change 0 ≤ FractionalIdeal.count K v
      (((χ.conductor * differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K))) : FractionalIdeal (𝓞 K)⁰ K)
    rw [count_coeIdeal_eq_multiplicity v hI]
    positivity
  have hideal : idealOfExponents (ordFinsupp K (ofFinite δ)) =
      χ.conductor * differentIdeal ℤ (𝓞 K) := by
    have h1 : toFractionalIdeal (ofFinite δ) =
        idealUnit _ (idealOfExponents_ne_bot (K := K) (n := ordFinsupp K (ofFinite δ)) hpos) := by
      rw [toFractionalIdeal_eq_iff]
      intro v
      exact (count_idealOfExponents (n := ordFinsupp K (ofFinite δ)) hpos v).symm
    rw [hδ, hunit] at h1
    exact FractionalIdeal.coeIdeal_injective (K := K) (congrArg Units.val h1).symm
  have hinf : infiniteModule (ofFinite δ) = 1 := by
    have e : ((ofFinite δ : IdeleGroup K) : 𝔸[K]).1 = 1 := by
      change ((toInfinite K (ofFinite δ) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1
      rw [toInfinite_ofFinite, Units.val_one]
    simp only [infiniteModule, e]
    exact Finset.prod_eq_one fun w _ ↦ by
      rw [show (1 : InfiniteAdeleRing K) w = 1 from rfl, norm_one, one_pow]
  rw [ideleModule_apply, hinf, one_mul, finiteModule_ofFinite_eq hpos, hideal, map_mul,
    absNorm_differentIdeal K (𝓞 K), discrNormConductor, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs,
    mul_comm]

theorem globalZeta_adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (s : ℂ) :
    globalZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        globalZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hf : adelicFourier K χ.testFunction =
      fun y ↦ χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y) :=
    funext (χ.adelicFourier_testFunction hδ)
  have h1 : globalZeta (fun y ↦ χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y)) χ⁻¹ s =
      χ.fourierConst δ * globalZeta (fun y ↦ (χ⁻¹).testFunction (ofFinite δ • y)) χ⁻¹ s := by
    unfold globalZeta
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hf, h1, globalZeta_comp_smul, χ.ideleModule_ofFinite_of_toFractionalIdeal_eq hδ,
    ofReal_inv_cpow_of_pos χ.discrNormConductor_pos, neg_neg, χ.inv_toIdele, Circle.coe_inv, inv_inv]
  ring

theorem exists_inv_ne_one (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) :
    ∃ v : normOneSubgroup K, χ⁻¹.toIdele (v : IdeleGroup K) ≠ 1 := by
  obtain ⟨v, hv⟩ := hχ
  exact ⟨v, by rw [χ.inv_toIdele, ne_eq, inv_eq_one]; exact hv⟩

theorem inv_eq_cpow_of_forall {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    ∀ x : IdeleGroup K,
      ((χ⁻¹).toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ (((-τ : ℝ) : ℂ) * I) := fun x ↦ by
  rw [χ.inv_toIdele, Circle.coe_inv, hτ, ← cpow_neg]
  push_cast
  ring_nf

theorem differentiable_const_cpow_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) {r : ℝ}
    (hr : 0 < r) : Differentiable ℂ fun s ↦ c * (r : ℂ) ^ s * f s :=
  ((differentiable_const c).mul
    (differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.2 hr.ne')))).mul hf

theorem tateZeta_adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) (s : ℂ) :
    tateZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        tateZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hχ' := χ.exists_inv_ne_one hχ
  have h := eq_tateZeta_of_differentiable (adelicFourier_mem_schwartzBruhat χ.testFunction_mem) hχ'
    (G := fun s ↦ χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
      tateZeta (χ⁻¹).testFunction χ⁻¹ s)
    (differentiable_const_cpow_mul (differentiable_tateZeta (χ⁻¹).testFunction_mem hχ') _
      χ.discrNormConductor_pos)
    fun s hs ↦ by
      rw [tateZeta_eq_globalZeta (χ⁻¹).testFunction_mem _ hs,
        χ.globalZeta_adelicFourier_testFunction hδ]
  exact (congrFun h s).symm

theorem tateZeta_adelicFourier_testFunction_of_forall {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {s : ℂ} (hs₀ : s ≠ (τ : ℂ) * I) (hs₁ : s ≠ 1 + (τ : ℂ) * I) :
    tateZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        tateZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hτ' := χ.inv_eq_cpow_of_forall hτ
  have hpole : ∀ z : ℂ, z ≠ (τ : ℂ) * I → z ≠ 1 + (τ : ℂ) * I →
      z ≠ -(((-τ : ℝ) : ℂ) * I) ∧ z ≠ 1 - ((-τ : ℝ) : ℂ) * I := fun z h0 h1 ↦ by
    push_cast
    constructor
    · rw [neg_mul, neg_neg]; exact h0
    · rw [neg_mul, sub_neg_eq_add]; exact h1
  have hmem : s ∈ ({-(((-τ : ℝ) : ℂ) * I), 1 - ((-τ : ℝ) : ℂ) * I} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact hpole s hs₀ hs₁
  have h := eqOn_tateZeta_of_differentiableOn hτ'
    (adelicFourier_mem_schwartzBruhat χ.testFunction_mem)
    (G := fun s ↦ χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
      tateZeta (χ⁻¹).testFunction χ⁻¹ s)
    (fun z hz ↦ by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
      refine DifferentiableAt.differentiableWithinAt ?_
      exact ((differentiableAt_const _).mul ((differentiableAt_id).const_cpow
        (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')))).mul
        (differentiableAt_tateZeta hτ' (χ⁻¹).testFunction_mem hz.1 hz.2))
    fun s hs ↦ by
      rw [tateZeta_eq_globalZeta (χ⁻¹).testFunction_mem _ hs,
        χ.globalZeta_adelicFourier_testFunction hδ]
  exact (h hmem).symm

end HeckeCharacter

end

end GroundTheory.Global
end

open NumberField InfinitePlace IsDedekindDomain MeasureTheory _root_.Complex Topology Filter Set
open scoped NumberField.AdeleRing ComplexConjugate Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos hs)
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero))

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem infiniteGamma_ne_zero (w : InfinitePlace K) {s : ℂ} (hs : 0 < s.re) :
    χ.infiniteGamma w s ≠ 0 := by
  unfold infiniteGamma
  split_ifs with hw
  · refine Gammaℝ_ne_zero_of_re_pos ?_
    have := (χ.infiniteWeight_of_isReal hw).1
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, intCast_re]
    have h0 : (0 : ℝ) ≤ (χ.infiniteWeight w : ℝ) := by exact_mod_cast this
    linarith
  · refine Gammaℂ_ne_zero_of_re_pos ?_
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, div_ofNat_re, natCast_re]
    positivity

theorem gammaFactor_ne_zero {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ ↦ χ.infiniteGamma_ne_zero w hs

theorem differentiable_gammaFactor_inv : Differentiable ℂ fun s ↦ (χ.gammaFactor s)⁻¹ := by
  have h : (fun s ↦ (χ.gammaFactor s)⁻¹) = fun s ↦ ∏ w, (χ.infiniteGamma w s)⁻¹ := by
    funext s
    rw [gammaFactor, Finset.prod_inv_distrib]
  rw [h]
  refine Differentiable.fun_finsetProd fun w _ ↦ ?_
  unfold infiniteGamma
  split_ifs
  · exact differentiable_Gammaℝ_inv.comp ((differentiable_id.add_const _).add_const _)
  · exact differentiable_Gammaℂ_inv.comp ((differentiable_id.add_const _).add_const _)

end HeckeCharacter

end

end GroundTheory.Global
end

open NumberField InfinitePlace IsDedekindDomain MeasureTheory _root_.Complex
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup


variable (K) in
theorem normOneClassMeasure_univ_ne_zero : normOneClassMeasure K Set.univ ≠ 0 := by
  rw [normOneClassMeasure_univ]
  exact (isFundamentalDomain_normOneFundamentalDomain K (normOneMeasure K)).measure_ne_zero
    (NeZero.ne _)


variable (K) in
theorem normOneClassMeasure_univ_toReal_ne_zero : (normOneClassMeasure K Set.univ).toReal ≠ 0 :=
  ENNReal.toReal_ne_zero.2 ⟨normOneClassMeasure_univ_ne_zero K, measure_ne_top _ _⟩

namespace HeckeCharacter

variable {χ : HeckeCharacter K} {τ : ℝ}
  (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
include hτ

theorem conductor_eq_top_of_forall : χ.conductor = ⊤ := by
  have h : ∀ v, IdeleGroup.conductorExponentAt (χ.toIdele.comp IdeleGroup.ofFinite) v = 0 := fun v ↦
    (IdeleGroup.conductorExponentAt_eq_zero_iff Circle.noSmallSubgroups _
      (χ.continuous_toIdele.comp IdeleGroup.continuous_ofFinite) v).2 fun x hx ↦ by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
          ofFinite_finiteUnitsSingle]
        refine Circle.ext ?_
        rw [hτ, ideleModule_finiteEmbedding, norm_eq_one_of_mul_eq_one x.mul_inv
          ((Submonoid.mem_units_iff _ _).1 hx).1 ((Submonoid.mem_units_iff _ _).1 hx).2]
        simp
  rw [conductor, IdeleGroup.conductor]
  simp only [h, pow_zero]
  rw [finprod_one, Ideal.one_eq_top]

theorem infiniteParams_of_forall (w : InfinitePlace K) : χ.infiniteParams w = (0, τ) := by
  refine (χ.infiniteParams_unique w (p := (0, τ)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
  dsimp only
  rw [infiniteComponent_apply, hτ, ideleModule_infiniteEmbedding, zpow_zero, one_mul]

theorem infiniteWeight_of_forall (w : InfinitePlace K) : χ.infiniteWeight w = 0 := by
  rw [infiniteWeight, infiniteParams_of_forall hτ]

theorem infiniteTau_of_forall (w : InfinitePlace K) : χ.infiniteTau w = τ := by
  rw [infiniteTau, infiniteParams_of_forall hτ]

theorem infiniteSchwartz_zero_of_forall : χ.infiniteSchwartz 0 = 1 := by
  rw [infiniteSchwartz_apply]
  simp [infinitePoly, infiniteWeight_of_forall hτ]

theorem finiteTestFun_zero_of_forall : χ.finiteTestFun 0 = 1 := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ χ.conductor := fun v h ↦ by
    rw [conductor_eq_top_of_forall hτ, Ideal.dvd_iff_le, top_le_iff] at h
    exact v.isPrime.ne_top h
  unfold finiteTestFun
  exact (finprod_congr fun v ↦ χ.finiteTest_eq_one (hv v) (by
    rw [show (0 : FiniteAdeleRing (𝓞 K) K) v = 0 from rfl, map_zero]; exact zero_le)).trans finprod_one

theorem testFunction_zero_of_forall : χ.testFunction 0 = 1 := by
  show χ.infiniteSchwartz (homeomorphMixedSpace K 0) * χ.finiteTestFun 0 = 1
  rw [homeomorphMixedSpace_apply, map_zero, infiniteSchwartz_zero_of_forall hτ,
    finiteTestFun_zero_of_forall hτ, one_mul]

end HeckeCharacter

end

end GroundTheory.Global
end

open NumberField InfinitePlace IsDedekindDomain MeasureTheory _root_.Complex Topology Filter Set
open scoped NumberField.AdeleRing ComplexConjugate Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def completedLFunction (s : ℂ) : ℂ :=
  ((π : ℂ) ^ nrComplexPlaces K)⁻¹ * (χ.discrNormConductor : ℂ) ^ (s / 2) *
    tateZeta χ.testFunction χ s

theorem discrNormConductor_cpow_ne_zero (s : ℂ) : (χ.discrNormConductor : ℂ) ^ s ≠ 0 := by
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')

theorem completedLFunction_eq {s : ℂ} (hs : 1 < s.re) :
    χ.completedLFunction s =
      (χ.discrNormConductor : ℂ) ^ (s / 2) * χ.gammaFactor s * χ.LFunction s := by
  rw [completedLFunction, tateZeta_eq_globalZeta χ.testFunction_mem χ hs,
    χ.globalZeta_testFunction hs]
  have hπ := pi_pow_nrComplexPlaces_ne_zero (K := K)
  field_simp

theorem differentiable_const_mul_cpow_half {f : ℂ → ℂ} {s : ℂ} (hf : DifferentiableAt ℂ f s) :
    DifferentiableAt ℂ (fun s ↦ ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
      (χ.discrNormConductor : ℂ) ^ (s / 2) * f s) s :=
  ((differentiableAt_const _).mul ((differentiableAt_id.div_const 2).const_cpow
    (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')))).mul hf

def conductorDifferentIdele : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  χ.exists_ofFinite_toFractionalIdeal_eq.choose

theorem toFractionalIdeal_conductorDifferentIdele :
    toFractionalIdeal (ofFinite χ.conductorDifferentIdele) =
      idealUnit χ.conductor χ.conductor_ne_bot * differentUnit :=
  χ.exists_ofFinite_toFractionalIdeal_eq.choose_spec

def rootNumber : ℂ :=
  χ.fourierConst χ.conductorDifferentIdele * (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) *
    (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ)

theorem completedLFunction_eq_rootNumber_mul_of_eq {s : ℂ}
    (h : tateZeta (adelicFourier K χ.testFunction) χ⁻¹ (1 - s) =
      χ.fourierConst χ.conductorDifferentIdele *
        (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) *
        (χ.discrNormConductor : ℂ) ^ (1 - s) * tateZeta (χ⁻¹).testFunction χ⁻¹ (1 - s)) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) := by
  have hA : (χ.discrNormConductor : ℂ) ≠ 0 := ofReal_ne_zero.2 χ.discrNormConductor_pos.ne'
  rw [completedLFunction, tateZeta_eq_tateZeta_one_sub χ.testFunction_mem, h, rootNumber,
    completedLFunction, discrNormConductor_inv]
  have hc : (χ.discrNormConductor : ℂ) ^ (s / 2) * (χ.discrNormConductor : ℂ) ^ (1 - s) =
      (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ) * (χ.discrNormConductor : ℂ) ^ ((1 - s) / 2) := by
    rw [← cpow_add _ _ hA, ← cpow_add _ _ hA]
    congr 1
    ring
  linear_combination (((π : ℂ) ^ nrComplexPlaces K)⁻¹ * χ.fourierConst χ.conductorDifferentIdele *
    (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) * tateZeta (χ⁻¹).testFunction χ⁻¹ (1 - s)) * hc

theorem completedLFunction_eq_rootNumber_mul {s : ℂ}
    (hs : ∀ τ : ℝ, (∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) →
        s ≠ -((τ : ℂ) * I) ∧ s ≠ 1 - (τ : ℂ) * I) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) := by
  refine χ.completedLFunction_eq_rootNumber_mul_of_eq ?_
  by_cases hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1
  · exact χ.tateZeta_adelicFourier_testFunction χ.toFractionalIdeal_conductorDifferentIdele hχ _
  · push Not at hχ
    obtain ⟨τ, hτ⟩ := (forall_normOne_eq_one_iff χ).1 hχ
    obtain ⟨h0, h1⟩ := hs τ hτ
    refine χ.tateZeta_adelicFourier_testFunction_of_forall
      χ.toFractionalIdeal_conductorDifferentIdele hτ (fun h ↦ h1 ?_) (fun h ↦ h0 ?_)
    · linear_combination -h
    · linear_combination -h

theorem completedLFunction_eq_rootNumber_mul_of_not
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) (s : ℂ) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) :=
  χ.completedLFunction_eq_rootNumber_mul fun τ hτ ↦ absurd ⟨τ, hτ⟩ hχ

theorem two_ne_pole (τ : ℝ) : (2 : ℂ) ≠ -((τ : ℂ) * I) ∧ (2 : ℂ) ≠ 1 - (τ : ℂ) * I := by
  constructor <;> intro h <;> have := congrArg re h <;> simp at this

theorem neg_one_ne_pole (τ : ℝ) :
    (-1 : ℂ) ≠ -((τ : ℂ) * I) ∧ (-1 : ℂ) ≠ 1 - (τ : ℂ) * I := by
  constructor <;> intro h <;> have := congrArg re h <;> simp at this <;> norm_num at this

theorem completedLFunction_two_ne_zero : χ.completedLFunction 2 ≠ 0 := by
  rw [χ.completedLFunction_eq (by norm_num)]
  exact mul_ne_zero (mul_ne_zero (χ.discrNormConductor_cpow_ne_zero _)
    (χ.gammaFactor_ne_zero (by norm_num))) (χ.LFunction_ne_zero (by norm_num))

theorem rootNumber_mul_rootNumber_inv : χ.rootNumber * χ⁻¹.rootNumber = 1 := by
  have h1 := χ.completedLFunction_eq_rootNumber_mul (s := 2) fun τ _ ↦ two_ne_pole τ
  have h2 := χ⁻¹.completedLFunction_eq_rootNumber_mul (s := -1) fun τ _ ↦ neg_one_ne_pole τ
  rw [inv_inv, show (1 : ℂ) - -1 = 2 by norm_num] at h2
  rw [show (1 : ℂ) - 2 = -1 by norm_num, h2, ← mul_assoc] at h1
  exact mul_right_cancel₀ χ.completedLFunction_two_ne_zero (h1.symm.trans (one_mul _).symm)

end HeckeCharacter

end

end GroundTheory.Global
