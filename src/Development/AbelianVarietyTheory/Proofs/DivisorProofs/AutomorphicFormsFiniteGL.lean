module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingLaplacianPolySoluti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalRapidDecayOneSimpleRootStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsUniformlySmallOutsideCompactBand
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsSpanLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlphaSmoothingFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessTotallyComplexGLProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsFixedLevelKtypes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspidalFormsGLTotallyComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalHarishChandraFiniteFormBoundedDetNormBan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingFormsGl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingFormsGl
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HCSmoothGL

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem isAddHaarMeasure_volume_Lie : (volume : Measure (Lie E a)).IsAddHaarMeasure := by
  haveI : SigmaFinite (volume : Measure (InfinitePlace E → ℂ)) := inferInstance
  haveI : (volume : Measure (Fin a → InfinitePlace E → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : SigmaFinite (volume : Measure (Fin a → InfinitePlace E → ℂ)) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

variable [_root_.NumberField.IsTotallyComplex E]


theorem exists_smooth_beta : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ β : Lie E a → ℂ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ invSet E a ∧ ∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  intro E _ _ _ a L W hW X hX N
  have hν := isAddHaarMeasure_volume_Lie (E := E) (a := a)
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite E a L W hW X hX N
  obtain ⟨α, hα, h⟩ := GlobalTheory.T.exists_testFunction_reproducing_laplacianPoly_solutions E a volume hν p hp0
  refine ⟨α, hα.1, hα.2.1, hα.2.2, fun φ hφm x => ?_⟩
  have hφ := hp φ hφm
  have h1 := h (chart φ.1 x) (φ.2 x) (fun y hy => by
    rw [Polynomial.aeval_eq_sum_range] at hφ
    have e := congrArg (fun ψ : Sm E a => chart ψ.1 x y) hφ
    rw [LinearMap.sum_apply] at e
    simp only [LinearMap.smul_apply] at e
    rw [GlobalTheory.HCFiniteSm.chart_sum' _ _ (fun k => (GlobalTheory.HCAlpha.lapOp E a ^ k) φ) _ hy] at e
    have e0 : chart (0 : Sm E a).1 x y = 0 := by simp [chart]
    rw [e0] at e
    rw [← e, GlobalTheory.HCAlpha.polyF, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.HCAlpha.chart_lapOp_pow E a φ x k y hy])
  simp only [mul_comm (chart φ.1 x _)]
  rw [h1]
  have := chart_val φ.1 x 1
  simpa using this

end GlobalTheory.HCSmoothGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingFormsGlStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_function_reproducing_forms_gl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ β : Lie E a → ℂ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ invSet E a ∧ ∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  first | exact @GlobalTheory.HCSmoothGL.exists_smooth_beta | exact GlobalTheory.HCSmoothGL.exists_smooth_beta | (intros; apply GlobalTheory.HCSmoothGL.exists_smooth_beta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumAddInvLeOfConsecutiveRatioBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumAddInvLeOfConsecutiveRatioBounds
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

namespace GlobalTheory.RatioIneq

theorem chain_bound (a : ℕ) (t ρ : ℝ) (ht : 0 < t) (hρ : 1 ≤ ρ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i)
    (hlo : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hhi : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) :
    ∀ n : ℕ, ∀ i k : Fin a, (i : ℕ) + n = k →
      r i ≤ (max 1 t⁻¹ * ρ) ^ n * r k ∧ r k ≤ (max 1 t⁻¹ * ρ) ^ n * r i := by
  have hM1 : (1:ℝ) ≤ max 1 t⁻¹ := le_max_left _ _
  have hBρ : ρ ≤ max 1 t⁻¹ * ρ := le_mul_of_one_le_left (by linarith) hM1
  have hBt : t⁻¹ ≤ max 1 t⁻¹ * ρ :=
    (le_max_right 1 t⁻¹).trans (le_mul_of_one_le_right (by linarith) hρ)
  intro n
  induction n with
  | zero =>
    intro i k h
    have : i = k := Fin.ext (by simpa using h)
    subst this; simp
  | succ n ih =>
    intro i k h
    have hk' : (i : ℕ) + n < a := by have := k.isLt; omega
    obtain ⟨h1, h2⟩ := ih i ⟨i + n, hk'⟩ rfl
    have hkk : (k : ℕ) = ((⟨i + n, hk'⟩ : Fin a) : ℕ) + 1 := by simp; omega
    have n1 : r ⟨i + n, hk'⟩ ≤ (max 1 t⁻¹ * ρ) * r k :=
      (hhi _ k hkk).trans (mul_le_mul_of_nonneg_right hBρ (hr k).le)
    have n2 : r k ≤ (max 1 t⁻¹ * ρ) * r ⟨i + n, hk'⟩ := by
      have hl := hlo _ k hkk
      have : r k ≤ t⁻¹ * r ⟨i + n, hk'⟩ := by
        calc r k = t⁻¹ * (t * r k) := by rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
          _ ≤ t⁻¹ * r ⟨i + n, hk'⟩ := mul_le_mul_of_nonneg_left hl (inv_nonneg.2 ht.le)
      exact this.trans (mul_le_mul_of_nonneg_right hBt (hr _).le)
    have hB0 : 0 ≤ (max 1 t⁻¹ * ρ) := by linarith
    have hBn : 0 ≤ (max 1 t⁻¹ * ρ) ^ n := pow_nonneg hB0 n
    constructor
    · calc r i ≤ (max 1 t⁻¹ * ρ) ^ n * r ⟨i + n, hk'⟩ := h1
        _ ≤ (max 1 t⁻¹ * ρ) ^ n * ((max 1 t⁻¹ * ρ) * r k) := mul_le_mul_of_nonneg_left n1 hBn
        _ = (max 1 t⁻¹ * ρ) ^ (n+1) * r k := by ring
    · calc r k ≤ (max 1 t⁻¹ * ρ) * r ⟨i + n, hk'⟩ := n2
        _ ≤ (max 1 t⁻¹ * ρ) * ((max 1 t⁻¹ * ρ) ^ n * r i) := mul_le_mul_of_nonneg_left h2 hB0
        _ = (max 1 t⁻¹ * ρ) ^ (n+1) * r i := by ring

theorem pair_bound (a : ℕ) (t ρ : ℝ) (ht : 0 < t) (hρ : 1 ≤ ρ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i)
    (hlo : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hhi : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) (i k : Fin a) :
    r i ≤ (max 1 t⁻¹ * ρ) ^ a * r k := by
  have hB1 : 1 ≤ max 1 t⁻¹ * ρ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hρ
  have hi := i.isLt
  have hk := k.isLt
  rcases le_total (i : ℕ) k with h | h
  · obtain ⟨h1, -⟩ := chain_bound a t ρ ht hρ r hr hlo hhi (k - i) i k (by omega)
    exact h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (hr k).le)
  · obtain ⟨-, h2⟩ := chain_bound a t ρ ht hρ r hr hlo hhi (i - k) k i (by omega)
    exact h2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (hr k).le)

theorem le_max_one_of_pow_le {x c : ℝ} {a : ℕ} (ha : a ≠ 0) (h : x ^ a ≤ c) : x ≤ max 1 c := by
  rcases le_total x 1 with h1 | h1
  · exact h1.trans (le_max_left _ _)
  · exact (le_self_pow₀ h1 ha).trans (h.trans (le_max_right _ _))

end GlobalTheory.RatioIneq

namespace GlobalTheory.RatioIneq

theorem sum_add_inv_le_of_ratio_bounds :
    ∀ (a : ℕ) (t c₁ c₂ : ℝ), 0 < t → 0 < c₁ → ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ r : Fin a → ℝ,
      (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      c₁ ≤ ∏ i, r i → ∏ i, r i ≤ c₂ → ∀ ρ : ℝ, 1 ≤ ρ →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) →
      ∑ i, (r i + (r i)⁻¹) ≤ C * ρ ^ K := by
  intro a t c₁ c₂ ht hc₁
  refine ⟨a * (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹) ^ a, a, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ max 1 c₂ := (zero_le_one.trans (le_max_left _ _))
    have h2 : (0:ℝ) ≤ max 1 c₁⁻¹ := (zero_le_one.trans (le_max_left _ _))
    have h3 : (0:ℝ) ≤ max 1 t⁻¹ := (zero_le_one.trans (le_max_left _ _))
    positivity
  intro r hr hlo hP1 hP2 ρ hρ hhi
  have hB1 : 1 ≤ max 1 t⁻¹ * ρ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hρ
  have hBa : 0 < (max 1 t⁻¹ * ρ) ^ a := pow_pos (by linarith) a
  have pb := pair_bound a t ρ ht hρ r hr hlo hhi
  have hup : ∀ i, r i ≤ max 1 c₂ * (max 1 t⁻¹ * ρ) ^ a := by
    intro i
    have ha : a ≠ 0 := by have := i.isLt; omega
    have hx : ∀ k, r i / (max 1 t⁻¹ * ρ) ^ a ≤ r k := fun k => by
      rw [div_le_iff₀ hBa, mul_comm]; exact pb i k
    have hprod : (r i / (max 1 t⁻¹ * ρ) ^ a) ^ a ≤ ∏ k, r k := by
      have := Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun _ : Fin a => r i / (max 1 t⁻¹ * ρ) ^ a) (g := r)
        (fun _ _ => (div_pos (hr i) hBa).le) (fun k _ => hx k)
      rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    have := le_max_one_of_pow_le ha (hprod.trans hP2)
    rwa [div_le_iff₀ hBa] at this
  have hdown : ∀ i, (r i)⁻¹ ≤ max 1 c₁⁻¹ * (max 1 t⁻¹ * ρ) ^ a := by
    intro i
    have ha : a ≠ 0 := by have := i.isLt; omega
    have hy : 0 < (max 1 t⁻¹ * ρ) ^ a * r i := mul_pos hBa (hr i)
    have hprod : ∏ k, r k ≤ ((max 1 t⁻¹ * ρ) ^ a * r i) ^ a := by
      have := Finset.prod_le_prod₀ (s := Finset.univ) (f := r)
        (g := fun _ : Fin a => (max 1 t⁻¹ * ρ) ^ a * r i)
        (fun k _ => (hr k).le) (fun k _ => pb k i)
      simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this
    have hc : ((max 1 t⁻¹ * ρ) ^ a * r i)⁻¹ ^ a ≤ c₁⁻¹ := by
      rw [inv_pow]; exact inv_anti₀ hc₁ (hP1.trans hprod)
    have := le_max_one_of_pow_le ha hc
    have heq : (r i)⁻¹ = (max 1 t⁻¹ * ρ) ^ a * ((max 1 t⁻¹ * ρ) ^ a * r i)⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hBa.ne', one_mul]
    rw [heq, mul_comm (max 1 c₁⁻¹)]
    exact mul_le_mul_of_nonneg_left this hBa.le
  calc ∑ i, (r i + (r i)⁻¹)
      ≤ ∑ _i : Fin a, (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹ * ρ) ^ a :=
        Finset.sum_le_sum fun i _ => by rw [add_mul]; exact add_le_add (hup i) (hdown i)
    _ = a * (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹) ^ a * ρ ^ a := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_pow]; ring

end GlobalTheory.RatioIneq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumAddInvLeOfConsecutiveRatioBoundsStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_add_inv_le_of_consecutiveRatio_bounds : ∀ (a : ℕ) (t c₁ c₂ : ℝ), 0 < t → 0 < c₁ → ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → c₁ ≤ ∏ i, r i → ∏ i, r i ≤ c₂ → ∀ ρ : ℝ, 1 ≤ ρ → (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) → ∑ i, (r i + (r i)⁻¹) ≤ C * ρ ^ K := by
  first | exact @GlobalTheory.RatioIneq.sum_add_inv_le_of_ratio_bounds | exact GlobalTheory.RatioIneq.sum_add_inv_le_of_ratio_bounds | (intros; apply GlobalTheory.RatioIneq.sum_add_inv_le_of_ratio_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetReductionAdelicDetNormBand
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetReductionAdelicDetNormBand
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.HCF

theorem exists_siegel_band : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ Ω : Set (GA E a), IsCompact Ω ∧ Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) ∧ ∃ t c₁ c₂ : ℝ, 0 < t ∧ 0 < c₁ ∧ ∀ g ∈ band E a, ∃ γ : GL (Fin a) E, ∃ b ∈ Ω, ∃ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧ c₁ ≤ ∏ i, r i ∧ ∏ i, r i ≤ c₂ ∧ ∃ k ∈ (maxCompact : Subgroup (GA E a)), ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k := by
  intro E _ _ a
  obtain ⟨W0, hW, hWB, t, ht, h⟩ := exists_siegelSet (K := E) a
  obtain ⟨B₁, B₂, hB₁, hB₁₂, hB⟩ := exists_pos_bounds hW
    (f := fun b => (ideleModule E (AdelicGLn.det E a b) : ℝ))
    (continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a)))
    (fun b _ => (ideleModule E (AdelicGLn.det E a b)).2)
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have hB₂ : 0 < B₂ := hB₁.trans_le hB₁₂
  set X₁ : ℝ := min 1 B₂⁻¹ with hX₁def
  set X₂ : ℝ := max 1 (2 / B₁) with hX₂def
  have hX₁ : 0 < X₁ := lt_min one_pos (inv_pos.2 hB₂)
  refine ⟨W0, hW, hWB, t, X₁, X₂, ht, hX₁, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := h g
  obtain ⟨b, hbW, _, ⟨r, hr, hrat, rfl⟩, k, hk, hgeq⟩ := hγ
  have hgmod : (ideleModule E (AdelicGLn.det E a g) : ℝ) = absDetA g := (adeleAbs_units _).symm
  have hmod := congrArg (fun x => (ideleModule E (AdelicGLn.det E a x) : ℝ)) hgeq
  rw [det_mul_mul, ideleModule_det_diagUnits_posIdele r hr,
    mem_normOneGL.1 (maxCompact_le_normOneGL hk), mul_one, map_mul, map_mul, Positive.val_mul,
    mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩), one_mul, hgmod] at hmod
  set X : ℝ := ∏ i, r i with hX
  have hXpos : 0 < X := Finset.prod_pos fun i _ => hr i
  have hb := hB b hbW
  obtain ⟨h1, h2⟩ := hg
  have hXd1 : X ^ d ≤ 2 / B₁ := by
    rw [le_div_iff₀ hB₁]
    calc X ^ d * B₁ ≤ X ^ d * (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
          mul_le_mul_of_nonneg_left hb.1 (pow_nonneg hXpos.le _)
      _ = absDetA g := by rw [mul_comm, hmod]
      _ ≤ 2 := h2
  have hXd2 : B₂⁻¹ ≤ X ^ d := by
    rw [inv_le_iff_one_le_mul₀' hB₂]
    calc (1 : ℝ) ≤ _ := h1
      _ = (ideleModule E (AdelicGLn.det E a b) : ℝ) * X ^ d := hmod
      _ ≤ B₂ * X ^ d := mul_le_mul_of_nonneg_right hb.2 (pow_nonneg hXpos.le _)
  have hratGL : ratGL E a γ = AdelicGLn.diagonal E a γ := rfl
  refine ⟨γ, b, hbW, r, hr, hrat, ?_, ?_, k, hk, by rw [hratGL]; exact hgeq⟩
  · rcases le_or_gt 1 X with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (hXd2.trans (pow_le_of_le_one hXpos.le h.le hd0.ne'))
  · rcases le_or_gt X 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (le_self_pow₀ h.le hd0.ne').trans (hXd1.trans (le_max_right _ _))
end GlobalTheory.HCF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetReductionAdelicDetNormBandStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelSet_reduction_adelicDetNormBand : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ Ω : Set (GA E a), IsCompact Ω ∧ Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) ∧ ∃ t c₁ c₂ : ℝ, 0 < t ∧ 0 < c₁ ∧ ∀ g ∈ band E a, ∃ γ : GL (Fin a) E, ∃ b ∈ Ω, ∃ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧ c₁ ≤ ∏ i, r i ∧ ∏ i, r i ≤ c₂ ∧ ∃ k ∈ (maxCompact : Subgroup (GA E a)), ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k := by
  first | exact @GlobalTheory.HCF.exists_siegel_band | exact GlobalTheory.HCF.exists_siegel_band | (intros; apply GlobalTheory.HCF.exists_siegel_band <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalHarishChandraFiniteFormBoundedDetNormBan
namespace GlobalTheory.HCF

open NumberField MeasureTheory GlobalTheory.CuspRep Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

theorem bounded_on_band_of_cuspidal : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∃ M : ℝ, ∀ g ∈ band E a, ‖φ.1 g‖ ≤ M := by
  intro E _ _ _ a L hL W hW X hX N φ hφ hcusp
  have hleft : ∀ ψ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g := by
    intro ψ hψ γ g
    induction hψ using Submodule.span_induction with
    | mem x hx => exact hx.1.left γ g
    | zero => rfl
    | add x y _ _ hx hy =>
      change x.1 (ratGL E a γ * g) + y.1 (ratGL E a γ * g) = x.1 g + y.1 g
      rw [hx, hy]
    | smul c x _ hx =>
      change c * x.1 (ratGL E a γ * g) = c * x.1 g
      rw [hx]
  obtain ⟨Ω, hΩc, hΩB, t, c₁, c₂, ht, hc₁, hred⟩ := GlobalTheory.T.exists_siegelSet_reduction_adelicDetNormBand E a
  obtain ⟨C₀, N₀, hC₀, hpoly⟩ := GlobalTheory.T.moderateGrowth_span_harishChandraFiniteForms E a L hL W X N φ hφ Ω hΩc
  obtain ⟨β, hβ, hβc, hβs, hrep⟩ := GlobalTheory.T.exists_test_function_reproducing_forms_gl E a L W hW X hX N
  obtain ⟨C', K, hC', hineq⟩ := GlobalTheory.T.sum_add_inv_le_of_consecutiveRatio_bounds a t c₁ c₂ ht hc₁
  obtain ⟨Cm, hCm, hdec⟩ := GlobalTheory.T.cuspidal_rapidDecay_one_simpleRoot E a L hL W X N β hβ hβc hβs hrep φ hφ hcusp Ω hΩc hΩB t C₀ N₀ ht hpoly (K * N₀)
  refine ⟨max (C₀ * C' ^ N₀ * height (1 : GL (Fin a) (Cinf E)) ^ N₀) (Cm * C' ^ N₀), fun g hg => ?_⟩
  obtain ⟨γ, b, hb, r, hr, hrat, hp1, hp2, k, hk, hg'⟩ := hred g hg
  rw [← hleft φ hφ γ g, hg']
  have hs0 : 0 ≤ ∑ i, (r i + (r i)⁻¹) := Finset.sum_nonneg fun i _ => by have := hr i; positivity
  by_cases hP : ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ 1 ≤ r i / r j
  · obtain ⟨i₀, j₀, hij₀, h1⟩ := hP
    obtain ⟨p, hpP, hpmax⟩ := ((Finset.univ : Finset (Fin a × Fin a)).filter
      (fun p => (p.2 : ℕ) = p.1 + 1)).exists_max_image (fun p => r p.1 / r p.2)
      ⟨(i₀, j₀), by simp [hij₀]⟩
    have hpP' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.1 hpP).2
    have hρ1 : 1 ≤ r p.1 / r p.2 := le_trans h1 (hpmax (i₀, j₀) (by simp [hij₀]))
    have hρ0 : 0 < r p.1 / r p.2 := by linarith
    have hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ (r p.1 / r p.2) * r j := fun i j hij => by
      have := hpmax (i, j) (by simp [hij])
      rwa [div_le_iff₀ (hr j)] at this
    have hsle := hineq r hr hrat hp1 hp2 _ hρ1 hall
    have hd := hdec b hb r hr hrat k hk p.1 p.2 hpP'
    refine le_trans hd (le_trans ?_ (le_max_right _ _))
    have e : r p.2 / r p.1 = (r p.1 / r p.2)⁻¹ := by rw [inv_div]
    rw [e]
    calc Cm * (r p.1 / r p.2)⁻¹ ^ (K * N₀) * (∑ i, (r i + (r i)⁻¹)) ^ N₀
        ≤ Cm * (r p.1 / r p.2)⁻¹ ^ (K * N₀) * (C' * (r p.1 / r p.2) ^ K) ^ N₀ := by
          gcongr
      _ = Cm * C' ^ N₀ := by
          rw [mul_pow, ← pow_mul, inv_pow]
          field_simp
  · push_neg at hP
    have hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ 1 * r j := fun i j hij => by
      have := (hP i j hij).le
      rwa [div_le_iff₀ (hr j)] at this
    have hsle := hineq r hr hrat hp1 hp2 1 le_rfl hall
    rw [one_pow, mul_one] at hsle
    have hb' := hpoly b hb r hr k hk 1
    rw [map_one, mul_one] at hb'
    refine le_trans hb' (le_trans ?_ (le_max_left _ _))
    have hh : 0 ≤ height (1 : GL (Fin a) (Cinf E)) := le_trans zero_le_one (one_le_height _)
    gcongr

end GlobalTheory.HCF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalHarishChandraFiniteFormBoundedDetNormBanStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_harishChandraFiniteForm_bounded_detNormBand : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∃ M : ℝ, ∀ g ∈ band E a, ‖φ.1 g‖ ≤ M := by
  first | exact @GlobalTheory.HCF.bounded_on_band_of_cuspidal | exact GlobalTheory.HCF.bounded_on_band_of_cuspidal | (intros; apply GlobalTheory.HCF.bounded_on_band_of_cuspidal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfTotallyBoundedSupNormBall
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfTotallyBoundedSupNormBall
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem finiteDimensional_of_totallyBounded_supBall :
    ∀ (T : Type) (V : Submodule ℂ (T → ℂ)) (B : Set T), (∀ φ ∈ V, (∀ x ∈ B, φ x = 0) → φ = 0) →
      (∀ φ ∈ V, ∃ M : ℝ, ∀ x ∈ B, ‖φ x‖ ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ F : Finset (T → ℂ), ∀ φ ∈ V, (∀ x ∈ B, ‖φ x‖ ≤ 1) →
        ∃ ψ ∈ F, ∀ x ∈ B, ‖φ x - ψ x‖ ≤ ε) → FiniteDimensional ℂ V := by
  intro T V B hinj hbdd htb
  classical
  have hmem : ∀ φ : V, Memℓp (fun x : B => (φ : T → ℂ) x) (⊤ : ENNReal) := by
    intro φ
    obtain ⟨M, hM⟩ := hbdd φ φ.2
    apply memℓp_infty
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hM x x.2
  let L : V →ₗ[ℂ] lp (fun _ : B => ℂ) (⊤ : ENNReal) :=
    { toFun := fun φ => ⟨fun x : B => (φ : T → ℂ) x, hmem φ⟩
      map_add' := fun φ ψ => lp.ext (funext fun _ => rfl)
      map_smul' := fun c φ => lp.ext (funext fun _ => rfl) }
  have hLapp : ∀ (φ : V) (x : B), (L φ) x = (φ : T → ℂ) x := fun _ _ => rfl
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun φ hφ => ?_
    have h0 : ∀ x ∈ B, (φ : T → ℂ) x = 0 := by
      intro x hx
      rw [← hLapp φ ⟨x, hx⟩, hφ]
      rfl
    exact Subtype.ext (hinj φ φ.2 h0)
  haveI : FiniteDimensional ℂ (LinearMap.range L) := by
    by_contra hfin
    obtain ⟨R, f, hR, hfR, hsep⟩ := exists_seq_norm_le_one_le_norm_sub hfin
    have hRpos : 0 < R := by linarith
    obtain ⟨F, hF⟩ := htb (1 / (3 * R)) (by positivity)
    have hpre : ∀ n, ∃ φ : V, L φ = (f n : lp (fun _ : B => ℂ) (⊤ : ENNReal)) := fun n => (f n).2
    choose φ hφ using hpre
    have hφle : ∀ n, ∀ x ∈ B, ‖(φ n : T → ℂ) x‖ ≤ R := by
      intro n x hx
      rw [← hLapp (φ n) ⟨x, hx⟩, hφ n]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _).trans (hfR n)
    have hball : ∀ n, ∀ x ∈ B, ‖((R : ℂ)⁻¹ • (φ n : T → ℂ)) x‖ ≤ 1 := by
      intro n x hx
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hRpos.le]
      rw [inv_mul_le_iff₀ hRpos, mul_one]
      exact hφle n x hx
    have hch : ∀ n, ∃ ψ ∈ F, ∀ x ∈ B, ‖((R : ℂ)⁻¹ • (φ n : T → ℂ)) x - ψ x‖ ≤ 1 / (3 * R) :=
      fun n => hF _ (V.smul_mem _ (φ n).2) (hball n)
    choose ψ hψF hψ using hch
    obtain ⟨m, n, hmn, hmn'⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (⟨ψ k, hψF k⟩ : F))
    have hψeq : ψ m = ψ n := congrArg Subtype.val hmn'
    have hpt : ∀ x ∈ B, ‖(φ m : T → ℂ) x - (φ n : T → ℂ) x‖ ≤ 2 / 3 := by
      intro x hx
      have h1 := hψ m x hx
      have h2 := hψ n x hx
      rw [hψeq] at h1
      have h3 : ‖((R : ℂ)⁻¹ • (φ m : T → ℂ)) x - ((R : ℂ)⁻¹ • (φ n : T → ℂ)) x‖ ≤ 2 / (3 * R) := by
        calc _ = ‖(((R : ℂ)⁻¹ • (φ m : T → ℂ)) x - ψ n x) - (((R : ℂ)⁻¹ • (φ n : T → ℂ)) x - ψ n x)‖ := by
                congr 1; ring
          _ ≤ _ := norm_sub_le _ _
          _ ≤ 1 / (3 * R) + 1 / (3 * R) := add_le_add h1 h2
          _ = 2 / (3 * R) := by ring
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg hRpos.le] at h3
      rw [inv_mul_le_iff₀ hRpos] at h3
      calc _ ≤ R * (2 / (3 * R)) := h3
        _ = 2 / 3 := by field_simp
    have hnorm : ‖f m - f n‖ ≤ 2 / 3 := by
      show ‖((f m : lp (fun _ : B => ℂ) (⊤ : ENNReal)) - (f n : lp (fun _ : B => ℂ) (⊤ : ENNReal)))‖ ≤ 2 / 3
      rw [← hφ m, ← hφ n]
      refine lp.norm_le_of_forall_le (by norm_num) fun x => ?_
      rw [lp.coeFn_sub, Pi.sub_apply, hLapp, hLapp]
      exact hpt x x.2
    have := hsep hmn
    linarith
  exact LinearEquiv.finiteDimensional (LinearEquiv.ofInjective L hL).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfTotallyBoundedSupNormBallStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_totallyBounded_supNormBall : ∀ (T : Type) (V : Submodule ℂ (T → ℂ)) (B : Set T), (∀ φ ∈ V, (∀ x ∈ B, φ x = 0) → φ = 0) → (∀ φ ∈ V, ∃ M : ℝ, ∀ x ∈ B, ‖φ x‖ ≤ M) → (∀ ε : ℝ, 0 < ε → ∃ F : Finset (T → ℂ), ∀ φ ∈ V, (∀ x ∈ B, ‖φ x‖ ≤ 1) → ∃ ψ ∈ F, ∀ x ∈ B, ‖φ x - ψ x‖ ≤ ε) → FiniteDimensional ℂ V := by
  first | exact @GlobalTheory.finiteDimensional_of_totallyBounded_supBall | exact GlobalTheory.finiteDimensional_of_totallyBounded_supBall | (intros; apply GlobalTheory.finiteDimensional_of_totallyBounded_supBall <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyBoundedSupOfEquicontinuousInvariantTails
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyBoundedSupOfEquicontinuousInvariantTails
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem totallyBounded_sup_of_equicontinuous_tails
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S B : Set G)
    (Φ : Set (G → ℂ))
    (hinv : ∀ φ ∈ Φ, ∀ s ∈ S, ∀ g, φ (s * g) = φ g)
    (hbd : ∀ φ ∈ Φ, ∀ g ∈ B, ‖φ g‖ ≤ 1)
    (heq : ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : G), ∀ φ ∈ Φ, ∀ g ∈ B, ∀ u ∈ U, g * u ∈ B →
      ‖φ (g * u) - φ g‖ ≤ ε)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧
      ∀ g ∈ B, (∃ s ∈ S, s * g ∈ C) ∨ ∀ φ ∈ Φ, ‖φ g‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ F : Finset (G → ℂ), ∀ φ ∈ Φ, ∃ ψ ∈ F, ∀ g ∈ B, ‖φ g - ψ g‖ ≤ ε := by
  classical
  intro ε hε
  have hδpos : 0 < ε / 4 := by positivity
  obtain ⟨U, hU, hUeq⟩ := heq (ε / 4) hδpos
  obtain ⟨C, hCc, hCB, hCt⟩ := htail (ε / 4) hδpos
  obtain ⟨t, htC, hCcov⟩ := hCc.elim_nhds_subcover (fun x => (fun h => x⁻¹ * h) ⁻¹' U) (by
    intro x _
    have hc : Continuous (fun h : G => x⁻¹ * h) := continuous_const.mul continuous_id
    apply hc.continuousAt.preimage_mem_nhds
    simpa using hU)
  let T : (G → ℂ) → (t → ℂ) := fun φ i => φ i
  have hTb : T '' Φ ⊆ Metric.closedBall 0 1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    exact hbd φ hφ i (hCB (htC i i.2))
  have htb : TotallyBounded (T '' Φ) :=
    ((isCompact_closedBall (0 : t → ℂ) 1).totallyBounded).subset hTb
  obtain ⟨s, hsT, hsf, hscov⟩ := Metric.finite_approx_of_totallyBounded htb (ε / 4) hδpos
  let c : (t → ℂ) → (G → ℂ) := fun y => if h : ∃ φ ∈ Φ, T φ = y then h.choose else 0
  have hc : ∀ y ∈ s, c y ∈ Φ ∧ T (c y) = y := by
    intro y hy
    have h : ∃ φ ∈ Φ, T φ = y := hsT hy
    simp only [c, dif_pos h]
    exact h.choose_spec
  refine ⟨hsf.toFinset.image c, fun φ hφ => ?_⟩
  obtain ⟨y, hy, hdist⟩ : ∃ y ∈ s, dist (T φ) y < ε / 4 := by
    have := hscov ⟨φ, hφ, rfl⟩
    simpa using this
  obtain ⟨hψ, hTψ⟩ := hc y hy
  refine ⟨c y, Finset.mem_image.2 ⟨y, hsf.mem_toFinset.2 hy, rfl⟩, fun g hg => ?_⟩
  rcases hCt g hg with ⟨s', hs', hsg⟩ | hsmall
  · obtain ⟨x, hxt, hxU⟩ : ∃ x ∈ t, x⁻¹ * (s' * g) ∈ U := by
      have := hCcov hsg
      simpa using this
    have hxB : x ∈ B := hCB (htC x hxt)
    have hmul : x * (x⁻¹ * (s' * g)) = s' * g := mul_inv_cancel_left x _
    have hsgB : s' * g ∈ B := hCB hsg
    have h1 := hUeq φ hφ x hxB _ hxU (by rw [hmul]; exact hsgB)
    have h2 := hUeq (c y) hψ x hxB _ hxU (by rw [hmul]; exact hsgB)
    rw [hmul] at h1 h2
    have h3 : ‖φ x - c y x‖ ≤ ε / 4 := by
      calc ‖φ x - c y x‖ = dist (T φ ⟨x, hxt⟩) (T (c y) ⟨x, hxt⟩) := (dist_eq_norm _ _).symm
        _ ≤ dist (T φ) (T (c y)) := dist_le_pi_dist _ _ _
        _ = dist (T φ) y := by rw [hTψ]
        _ ≤ ε / 4 := hdist.le
    rw [← hinv φ hφ s' hs' g, ← hinv (c y) hψ s' hs' g]
    calc ‖φ (s' * g) - c y (s' * g)‖
        = ‖(φ (s' * g) - φ x) + (φ x - c y x) - (c y (s' * g) - c y x)‖ := by congr 1; ring
      _ ≤ ‖φ (s' * g) - φ x‖ + ‖φ x - c y x‖ + ‖c y (s' * g) - c y x‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ε / 4 + ε / 4 + ε / 4 := by gcongr
      _ ≤ ε := by linarith
  · exact (norm_sub_le _ _).trans (by linarith [hsmall φ hφ, hsmall (c y) hψ])

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyBoundedSupOfEquicontinuousInvariantTailsStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totallyBounded_sup_of_equicontinuous_invariant_tails : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S B : Set G) (Φ : Set (G → ℂ)), (∀ φ ∈ Φ, ∀ s ∈ S, ∀ g, φ (s * g) = φ g) → (∀ φ ∈ Φ, ∀ g ∈ B, ‖φ g‖ ≤ 1) → (∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : G), ∀ φ ∈ Φ, ∀ g ∈ B, ∀ u ∈ U, g * u ∈ B → ‖φ (g * u) - φ g‖ ≤ ε) → (∀ ε : ℝ, 0 < ε → ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g ∈ B, (∃ s ∈ S, s * g ∈ C) ∨ ∀ φ ∈ Φ, ‖φ g‖ ≤ ε) → ∀ ε : ℝ, 0 < ε → ∃ F : Finset (G → ℂ), ∀ φ ∈ Φ, ∃ ψ ∈ F, ∀ g ∈ B, ‖φ g - ψ g‖ ≤ ε := by
  first | exact @GlobalTheory.totallyBounded_sup_of_equicontinuous_tails | exact GlobalTheory.totallyBounded_sup_of_equicontinuous_tails | (intros; apply GlobalTheory.totallyBounded_sup_of_equicontinuous_tails <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspidalFormsGLTotallyComplex
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem finiteDimensional_cuspGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ V : Submodule ℂ (Sm E a), V ≤ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) → (∀ φ ∈ V, IsCuspidal φ.1) → FiniteDimensional ℂ V := by
  intro E _ _ _ a L hL W hW X hX N V hV hc
  have hleft : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ (γ : GL (Fin a) E) (g : GA E a),
      φ.1 (ratGL E a γ * g) = φ.1 g := by
    intro φ hφ γ g
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.1.left γ g
    | zero => rfl
    | add x y _ _ hx hy =>
      change x.1 (ratGL E a γ * g) + y.1 (ratGL E a γ * g) = x.1 g + y.1 g
      rw [hx, hy]
    | smul c x _ hx =>
      change c * x.1 (ratGL E a γ * g) = c * x.1 g
      rw [hx]
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hfin : FiniteDimensional ℂ V' := by
    refine GlobalTheory.T.finiteDimensional_of_totallyBounded_supNormBall (GA E a) V' (band E a) ?_ ?_ ?_
    · rintro _ ⟨φ, hφ, rfl⟩ h0
      funext g
      obtain ⟨C, hC⟩ := GlobalTheory.T.norm_le_sup_wider_band_genCentralEigenforms E a L hL W hW X hX N (max 1 (max (absDetA g) (absDetA g)⁻¹)) (le_max_left _ _)
      have hp := absDetA_pos g
      have h1 : (max 1 (max (absDetA g) (absDetA g)⁻¹))⁻¹ ≤ absDetA g := by
        rw [inv_le_comm₀ (by positivity) hp]
        exact (le_max_right _ _).trans (le_max_right _ _)
      have h2 : absDetA g ≤ 2 * max 1 (max (absDetA g) (absDetA g)⁻¹) := by
        have := (le_max_left (absDetA g) (absDetA g)⁻¹).trans (le_max_right 1 _)
        have := le_max_left 1 (max (absDetA g) (absDetA g)⁻¹)
        linarith
      have := hC φ (hV hφ) 0 (fun h hh => by rw [show φ.1 h = 0 from h0 h hh, norm_zero]) g h1 h2
      simpa using this
    · rintro _ ⟨φ, hφ, rfl⟩
      exact GlobalTheory.T.cuspidal_harishChandraFiniteForm_bounded_detNormBand E a L hL W hW X hX N φ (hV hφ) (hc φ hφ)
    · intro ε hε
      obtain ⟨F, hF⟩ := GlobalTheory.T.totallyBounded_sup_of_equicontinuous_invariant_tails (GA E a) (Set.range (ratGL E a)) (band E a)
        {f | ∃ φ ∈ V, φ.1 = f ∧ ∀ x ∈ band E a, ‖f x‖ ≤ 1}
        (by rintro f ⟨φ, hφ, rfl, -⟩ s ⟨γ, rfl⟩ g; exact hleft φ (hV hφ) γ g)
        (by rintro f ⟨φ, -, rfl, hb⟩; exact hb)
        (by
          intro ε hε
          obtain ⟨U, hU, h⟩ := GlobalTheory.T.harishChandraForms_equicontinuous_on_band E a L hL W hW X hX N ε hε
          refine ⟨U, hU, ?_⟩
          rintro f ⟨φ, hφ, rfl, hb⟩ g hg u hu hgu
          simpa using h φ (hV hφ) 1 hb g hg u hu hgu)
        (by
          intro ε hε
          obtain ⟨C, hC, hCB, h⟩ := GlobalTheory.T.cuspForms_uniformly_small_outside_compact_band E a L hL W hW X hX N ε hε
          refine ⟨C, hC, hCB, fun g hg => ?_⟩
          rcases h g hg with ⟨γ, hγ⟩ | h'
          · exact Or.inl ⟨_, ⟨γ, rfl⟩, hγ⟩
          · refine Or.inr ?_
            rintro f ⟨φ, hφ, rfl, hb⟩
            simpa using h' φ (hV hφ) (hc φ hφ) 1 hb) ε hε
      refine ⟨F, ?_⟩
      rintro _ ⟨φ, hφ, rfl⟩ hb
      exact hF _ ⟨φ, hφ, rfl, hb⟩
  exact (Submodule.equivMapOfInjective (Sm E a).subtype Subtype.val_injective V).symm.finiteDimensional

end GlobalTheory.HCF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspidalFormsGLTotallyComplexStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_cuspidalForms_GL_totallyComplex : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ V : Submodule ℂ (Sm E a), V ≤ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) → (∀ φ ∈ V, IsCuspidal φ.1) → FiniteDimensional ℂ V := by
  first | exact @GlobalTheory.HCF.finiteDimensional_cuspGL | exact GlobalTheory.HCF.finiteDimensional_cuspGL | (intros; apply GlobalTheory.HCF.finiteDimensional_cuspGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsFixedLevelKtypes
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory Topology

noncomputable section

namespace GlobalTheory.HCFCusp

theorem finiteDimensional_cuspSpan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ α : Lie E a → ℂ, IsTest (invSet E a) α → (∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1) → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ formsGL E a L W {χ} N ∧ IsCuspidal φ.1}) := by
  intro E _ _ _ a L hL W _ χ N ν _ α _ _
  have hopen : ∀ φ : Sm E a, (∀ k ∈ L, finRep E a k φ = φ) → IsOpen {k | finRep E a k φ = φ} := by
    intro φ hφ
    rw [isOpen_iff_forall_mem_open]
    intro k hk
    refine ⟨(k * ·) '' (L : Set (GL (Fin a) (Af E))), ?_, isOpenMap_mul_left k _ hL, ⟨1, L.one_mem, mul_one k⟩⟩
    rintro _ ⟨l, hl, rfl⟩
    change finRep E a (k * l) φ = φ
    rw [map_mul, Module.End.mul_apply, hφ l hl]
    exact hk
  refine GlobalTheory.T.finiteDimensional_cuspidalForms_GL_totallyComplex E a L hL W ‹_› {χ} (Set.finite_singleton χ) N _
    (Submodule.span_mono fun φ hφ => hφ.1) ?_
  intro φ hφ
  have P : (∀ k ∈ L, finRep E a k φ = φ) ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsCuspidal φ.1 := by
    induction hφ using Submodule.span_induction with
    | mem x hx => exact ⟨hx.1.2.1, hx.1.1.left, hx.2⟩
    | zero =>
      refine ⟨fun k _ => map_zero _, fun _ _ => rfl, fun r _ _ _ _ μ 𝓕 _ _ g => ?_⟩
      change ∫ z in 𝓕, (0 : ℂ) ∂μ = 0
      exact integral_zero _ _
    | add x y _ _ hx hy =>
      refine ⟨fun k hk => by rw [map_add (f := _), hx.1 k hk, hy.1 k hk], fun γ g => ?_, fun r h0 h1 _ _ μ 𝓕 hμ h𝓕 g => ?_⟩
      · change x.1 _ + y.1 _ = x.1 g + y.1 g
        rw [hx.2.1, hy.2.1]
      · haveI := hμ
        have ix := GlobalTheory.CuspRep.CuspidalL2GL.integrableOn_unip
          (ContAut.continuous_of_isOpen_stab E a x (hopen x hx.1)) hx.2.1 μ h𝓕 g
        have iy := GlobalTheory.CuspRep.CuspidalL2GL.integrableOn_unip
          (ContAut.continuous_of_isOpen_stab E a y (hopen y hy.1)) hy.2.1 μ h𝓕 g
        change ∫ z in 𝓕, (x.1 (unip z * g) + y.1 (unip z * g)) ∂μ = 0
        rw [integral_add ix iy, hx.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, hy.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, add_zero]
    | smul c x _ hx =>
      refine ⟨fun k hk => by rw [map_smul, hx.1 k hk], fun γ g => ?_, fun r h0 h1 _ _ μ 𝓕 hμ h𝓕 g => ?_⟩
      · change c * x.1 _ = c * x.1 g
        rw [hx.2.1]
      · change ∫ z in 𝓕, c * x.1 (unip z * g) ∂μ = 0
        rw [integral_const_mul, hx.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, mul_zero]
  exact P.2.2

end GlobalTheory.HCFCusp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsFixedLevelKtypesStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_cuspForms_fixedLevel_Ktypes : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ α : Lie E a → ℂ, IsTest (invSet E a) α → (∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1) → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ formsGL E a L W {χ} N ∧ IsCuspidal φ.1}) := by
  first | exact @GlobalTheory.HCFCusp.finiteDimensional_cuspSpan | exact GlobalTheory.HCFCusp.finiteDimensional_cuspSpan | (intros; apply GlobalTheory.HCFCusp.finiteDimensional_cuspSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraUniformSmoothingTestFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEllipticReproducingTestFunctionLaplacian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEllipticReproducingTestFunctionLaplacian
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

noncomputable section
namespace GlobalTheory.HCParam

section Local
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

end Local
end GlobalTheory.HCParam

noncomputable section
namespace GlobalTheory.HCParam

section Degenerate
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

end Degenerate
end GlobalTheory.HCParam

noncomputable section
namespace GlobalTheory.HCParam

section Transpose
variable {E : Type} [Field E] [NumberField E] {a : ℕ} (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure]

end Transpose

end GlobalTheory.HCParam

noncomputable section
namespace GlobalTheory.HCParam

theorem reproduce : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∀ p : Polynomial ℂ, p ≠ 0 → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) →
        ∫ y, α y * f y ∂ν = f (oneL E a) :=
  GlobalTheory.T.exists_testFunction_reproducing_laplacianPoly_solutions

end GlobalTheory.HCParam
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEllipticReproducingTestFunctionLaplacianStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ellipticReproducing_testFunction_laplacian : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∀ p : Polynomial ℂ, p ≠ 0 → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) →
        ∫ y, α y * f y ∂ν = f (oneL E a) := by
  first | exact @GlobalTheory.HCParam.reproduce | exact GlobalTheory.HCParam.reproduce | (intros; apply GlobalTheory.HCParam.reproduce <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraUniformSmoothingTestFunction
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

namespace GlobalTheory.HCAlphaEll

theorem chart_sum {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (s : Finset ℕ) (c : ℕ → ℂ)
    (ψ : ℕ → Sm E a) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    chart (∑ k ∈ s, c k • ψ k).1 g y = ∑ k ∈ s, c k * chart (ψ k).1 g y := by
  have hy' : IsUnit (Matrix.of y) := hy
  simp only [chart, dif_pos hy', Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem reproduce_of_lap : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∀ p : Polynomial ℂ, p ≠ 0 → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ φ : Sm E a, Polynomial.aeval (lapOp E a) p φ = 0 → smoothing ν α φ.1 = φ.1 := by
  intro E _ _ _ a ν hν p hp
  obtain ⟨α, hα, h⟩ := GlobalTheory.T.exists_ellipticReproducing_testFunction_laplacian E a ν hν p hp
  refine ⟨α, hα, fun φ hφ => funext fun x => ?_⟩
  have h1 := h (chart φ.1 x) (φ.2 x) (fun y hy => by
    rw [Polynomial.aeval_eq_sum_range] at hφ
    have e := congrArg (fun ψ : Sm E a => chart ψ.1 x y) hφ
    rw [LinearMap.sum_apply] at e
    simp only [LinearMap.smul_apply] at e
    rw [chart_sum _ _ (fun k => (lapOp E a ^ k) φ) _ hy] at e
    have e0 : chart (0 : Sm E a).1 x y = 0 := by simp [chart]
    rw [e0] at e
    rw [← e, polyF, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.T.chart_leftInvariantLaplacianOp_pow_eq_iterate E a φ x k y hy])
  rw [smoothing, h1]
  have := chart_val φ.1 x 1
  simpa using this

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem commute_lieS {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) (i j : Fin a) (x : Cinf E) :
    Commute z (lieS E a i j x) := by
  rw [lieS_apply]; exact hz _

theorem commute_casKOp {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) :
    Commute z (casKOp E a) := by
  unfold casKOp
  refine Commute.sum_right _ _ _ fun τ _ => Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  refine Commute.smul_right (Commute.add_right (Commute.pow_right ?_ 2) (Commute.pow_right ?_ 2)) _
  · exact (commute_lieS hz _ _ _).sub_right (commute_lieS hz _ _ _)
  · exact (commute_lieS hz _ _ _).add_right (commute_lieS hz _ _ _)

theorem commute_cas {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) (τ : E →+* ℂ) :
    Commute z (Formalism.REAL.Cas (Eop (a := a) τ)) := by
  have hE : ∀ i j, Commute z (Eop τ i j) := fun i j =>
    Commute.smul_right ((commute_lieS hz _ _ _).sub_right ((commute_lieS hz _ _ _).smul_right _)) _
  unfold Formalism.REAL.Cas
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => (hE i j).mul_right (hE j i)

theorem commute_lie_of_mem {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (X : Lie E a) :
    Commute z (lie E a X) := Zalg_mul_lie E a X z hz

theorem foldr_replicate (z : Module.End ℂ (Sm E a)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (φ : Sm E a) :
    (List.replicate N z).foldr (fun z f => z f - χ z • f) φ =
      Polynomial.aeval z ((Polynomial.X - Polynomial.C (χ z)) ^ N) φ := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', map_mul, Module.End.mul_apply]
    simp [sub_smul, Polynomial.aeval_X, Polynomial.aeval_C]

theorem exists_alpha_smoothing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ),
    FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1 := by
  intro E _ _ _ a L _ W hW χ N ν hν
  obtain ⟨q, hq0, hq⟩ := GlobalTheory.T.exists_poly_maximalCompactCasimir_kills_KType E a W hW
  let A : Option (E →+* ℂ) → Module.End ℂ (Sm E a) := fun o => o.elim (casKOp E a) fun τ => Formalism.REAL.Cas (Eop τ)
  let c : Option (E →+* ℂ) → ℂ := fun o => o.elim 2 fun _ => 4
  let P : Option (E →+* ℂ) → Polynomial ℂ := fun o =>
    o.elim q fun τ => (Polynomial.X - Polynomial.C (χ (Formalism.REAL.Cas (Eop (a := a) τ)))) ^ N
  have hZ : ∀ τ : E →+* ℂ, ∀ X, Commute (Formalism.REAL.Cas (Eop (a := a) τ)) (lie E a X) := fun τ =>
    commute_lie_of_mem (GlobalTheory.T.casimir_glFactor_embedding_mem_capelliAlgebra E a τ)
  have hc : ∀ i j, Commute (A i) (A j) := by
    rintro (_ | τ) (_ | τ')
    · exact Commute.refl _
    · exact (commute_casKOp (hZ τ')).symm
    · exact commute_casKOp (hZ τ)
    · exact commute_cas (hZ τ) τ'
  have hP : ∀ i, P i ≠ 0 := by
    rintro (_ | τ)
    · exact hq0
    · exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.T.exists_poly_annihilates_commuting_linear_combination A hc c P hP
  obtain ⟨α, hα, hsm⟩ := reproduce_of_lap E a ν hν p hp0
  refine ⟨α, hα, fun φ hφ => hsm φ ?_⟩
  have e : ∑ i, c i • A i = lapOp E a := by
    rw [GlobalTheory.T.leftInvariantLaplacian_eq_casimir_decomposition E a, Fintype.sum_option]; rfl
  rw [← e]
  refine hp φ ?_
  rintro (_ | τ)
  · exact hq φ hφ.2.2.1
  · obtain ⟨χ', hχ', hN⟩ := hφ.2.2.2
    rw [Set.mem_singleton_iff] at hχ'
    subst hχ'
    have h := hN (List.replicate N (Formalism.REAL.Cas (Eop τ))) (List.length_replicate ..)
      (fun z hz => (List.eq_of_mem_replicate hz) ▸ GlobalTheory.T.casimir_glFactor_embedding_mem_capelliAlgebra E a τ)
    rw [foldr_replicate] at h
    exact h

end GlobalTheory.HCAlphaEll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraUniformSmoothingTestFunctionStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory
theorem _root_.GlobalTheory.T.harishChandra_uniform_smoothing_test_function : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧ ∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1 := by
  first | exact @GlobalTheory.HCAlphaEll.exists_alpha_smoothing | exact GlobalTheory.HCAlphaEll.exists_alpha_smoothing | (intros; apply GlobalTheory.HCAlphaEll.exists_alpha_smoothing <;> assumption) | exact @GlobalTheory.HCAlphaEll.foldr_replicate | exact GlobalTheory.HCAlphaEll.foldr_replicate | (intros; apply GlobalTheory.HCAlphaEll.foldr_replicate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessTotallyComplexGLProof
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory

namespace GlobalTheory.HCFGL

theorem finiteDimensional_single (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ih : ∀ b < a, ∀ L : Subgroup (GL (Fin b) (Af E)), IsOpen (L : Set (GL (Fin b) (Af E))) →
      ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite →
      ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (formsGL E b L W X N)))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) :
    FiniteDimensional ℂ (Submodule.span ℂ (formsGL E a L W {χ} N)) := by
  obtain ⟨n, T, hT⟩ := GlobalTheory.T.finiteDimensional_forms_span_level E a ih L hL W hW χ N
  obtain ⟨α, hα, hrep⟩ := GlobalTheory.T.harishChandra_uniform_smoothing_test_function E a L hL W hW χ N (MeasureTheory.Measure.addHaar) inferInstance
  have hQ := GlobalTheory.T.finiteDimensional_cuspForms_fixedLevel_Ktypes E a L hL W hW χ N MeasureTheory.Measure.addHaar inferInstance α hα hrep
  set P := Submodule.span ℂ (formsGL E a L W {χ} N)
  set Q := Submodule.span ℂ {φ | φ ∈ formsGL E a L W {χ} N ∧ IsCuspidal φ.1}
  have h1 : (P.map T).FG := IsNoetherian.noetherian _
  have h2 : (P ⊓ LinearMap.ker T).FG := by
    have hle : P ⊓ LinearMap.ker T ≤ Q := by
      intro φ hφ
      have hS := GlobalTheory.T.harishChandraFiniteFormsGL_single_char_span_mem E a L W χ N φ hφ.1
      exact Submodule.subset_span ⟨hS, hT φ hS hφ.2⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  exact Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_of_fg_inf_ker T h1 h2)

theorem coreFiniteGL : CoreFiniteGL := by
  intro E _ _ _ a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro L hL W hW X hX N
  have hle : Submodule.span ℂ (formsGL E a L W X N) ≤
      hX.toFinset.sup fun χ => Submodule.span ℂ (formsGL E a L W {χ} N) := by
    rw [Submodule.span_le]
    rintro φ ⟨h1, h2, h3, χ, hχ, h4⟩
    have hmem : Submodule.span ℂ (formsGL E a L W {χ} N) ≤
        hX.toFinset.sup fun χ => Submodule.span ℂ (formsGL E a L W {χ} N) :=
      Finset.le_sup (f := fun χ => Submodule.span ℂ (formsGL E a L W {χ} N)) (hX.mem_toFinset.2 hχ)
    exact hmem (Submodule.subset_span ⟨h1, h2, h3, χ, rfl, h4⟩)
  have hs : ∀ χ, FiniteDimensional ℂ (Submodule.span ℂ (formsGL E a L W {χ} N)) := fun χ =>
    finiteDimensional_single E a (fun b hb => ih b hb) L hL W hW χ N
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.HCFGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessTotallyComplexGLProofStatement
theorem _root_.GlobalTheory.T.harishChandraFinitenessTotallyComplexGL_proof : GlobalTheory.HCF.CoreFiniteGL := by
  first | exact @GlobalTheory.HCFGL.coreFiniteGL | exact GlobalTheory.HCFGL.coreFiniteGL | (intros; apply GlobalTheory.HCFGL.coreFiniteGL <;> assumption) | exact @GlobalTheory.HCFGL.finiteDimensional_single | exact GlobalTheory.HCFGL.finiteDimensional_single | (intros; apply GlobalTheory.HCFGL.finiteDimensional_single <;> assumption)
end
end

namespace GlobalTheory

theorem automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL :=
  GlobalTheory.T.harishChandra_finiteness_automorphic_GL_of_eigen GlobalTheory.T.harishChandraFinitenessTotallyComplexGL_proof

end GlobalTheory
