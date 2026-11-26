module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveExpansionQuotientLevelOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStable
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStable
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem modGrowth_pow_bounds (y : ℝ) (hy : 0 < y) (A : ℕ) :
    max y y⁻¹ ^ A ≤ y ^ A + (y ^ A)⁻¹ ∧ y ^ A + (y ^ A)⁻¹ ≤ 2 * max y y⁻¹ ^ A := by
  rw [← inv_pow]
  have h1 : 0 < y ^ A := pow_pos hy A
  have h2 : 0 < y⁻¹ ^ A := pow_pos (inv_pos.mpr hy) A
  rcases le_total y y⁻¹ with h | h
  · rw [max_eq_right h]
    have : y ^ A ≤ y⁻¹ ^ A := pow_le_pow_left₀ hy.le h A
    constructor <;> linarith
  · rw [max_eq_left h]
    have : y⁻¹ ^ A ≤ y ^ A := pow_le_pow_left₀ (inv_pos.mpr hy).le h A
    constructor <;> linarith

theorem one_le_max_inv (y : ℝ) (hy : 0 < y) : 1 ≤ max y y⁻¹ := by
  rcases le_total 1 y with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hy).mpr h)

theorem mod_of_bound (F : ℍ → ℂ) (C : ℝ) (A : ℕ) (h : ∀ τ : ℍ, ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A) :
    Mod F := by
  refine ⟨max C 0, A, fun τ => ?_⟩
  obtain ⟨b1, _⟩ := modGrowth_pow_bounds τ.im τ.im_pos A
  have hM : 0 ≤ max τ.im τ.im⁻¹ ^ A :=
    pow_nonneg (le_trans zero_le_one (one_le_max_inv _ τ.im_pos)) A
  calc ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A := h τ
    _ ≤ max C 0 * max τ.im τ.im⁻¹ ^ A := mul_le_mul_of_nonneg_right (le_max_left _ _) hM
    _ ≤ _ := mul_le_mul_of_nonneg_left b1 (le_max_right _ _)

theorem bound_of_mod (F : ℍ → ℂ) (hF : Mod F) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ τ : ℍ, ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A := by
  obtain ⟨C, A, h⟩ := hF
  refine ⟨2 * max C 0, A, by positivity, fun τ => ?_⟩
  obtain ⟨_, b2⟩ := modGrowth_pow_bounds τ.im τ.im_pos A
  have hh : 0 ≤ τ.im ^ A + (τ.im ^ A)⁻¹ :=
    add_nonneg (pow_pos τ.im_pos A).le (inv_pos.mpr (pow_pos τ.im_pos A)).le
  calc ‖F τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) := h τ
    _ ≤ max C 0 * (τ.im ^ A + (τ.im ^ A)⁻¹) := mul_le_mul_of_nonneg_right (le_max_left _ _) hh
    _ ≤ max C 0 * (2 * max τ.im τ.im⁻¹ ^ A) := mul_le_mul_of_nonneg_left b2 (le_max_right _ _)
    _ = _ := by ring

theorem mod_add (F G : ℍ → ℂ) (hF : Mod F) (hG : Mod G) : Mod (fun τ => F τ + G τ) := by
  obtain ⟨C, A, hC, h1⟩ := bound_of_mod F hF
  obtain ⟨D, B, hD, h2⟩ := bound_of_mod G hG
  refine mod_of_bound _ (C + D) (A + B) fun τ => ?_
  have hM := one_le_max_inv _ τ.im_pos
  have eA : max τ.im τ.im⁻¹ ^ A ≤ max τ.im τ.im⁻¹ ^ (A + B) := pow_le_pow_right₀ hM (Nat.le_add_right A B)
  have eB : max τ.im τ.im⁻¹ ^ B ≤ max τ.im τ.im⁻¹ ^ (A + B) := pow_le_pow_right₀ hM (Nat.le_add_left B A)
  calc ‖F τ + G τ‖ ≤ ‖F τ‖ + ‖G τ‖ := norm_add_le _ _
    _ ≤ C * max τ.im τ.im⁻¹ ^ A + D * max τ.im τ.im⁻¹ ^ B := add_le_add (h1 τ) (h2 τ)
    _ ≤ C * max τ.im τ.im⁻¹ ^ (A + B) + D * max τ.im τ.im⁻¹ ^ (A + B) :=
        add_le_add (mul_le_mul_of_nonneg_left eA hC) (mul_le_mul_of_nonneg_left eB hD)
    _ = _ := by ring

theorem mod_mul (F G : ℍ → ℂ) (hF : Mod F) (hG : Mod G) : Mod (fun τ => F τ * G τ) := by
  obtain ⟨C, A, hC, h1⟩ := bound_of_mod F hF
  obtain ⟨D, B, hD, h2⟩ := bound_of_mod G hG
  refine mod_of_bound _ (C * D) (A + B) fun τ => ?_
  have hM := le_trans zero_le_one (one_le_max_inv _ τ.im_pos)
  calc ‖F τ * G τ‖ = ‖F τ‖ * ‖G τ‖ := norm_mul _ _
    _ ≤ (C * max τ.im τ.im⁻¹ ^ A) * (D * max τ.im τ.im⁻¹ ^ B) :=
        mul_le_mul (h1 τ) (h2 τ) (norm_nonneg _) (mul_nonneg hC (pow_nonneg hM A))
    _ = _ := by ring

theorem mod_const (c : ℂ) : Mod fun _ => c :=
  mod_of_bound _ ‖c‖ 0 fun τ => by simp

theorem im_slz_arg (δ : M2) (hc : δ 1 0 = 0) (τ : ℍ) :
    (((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)))).im
      = (δ 0 0 : ℝ) / (δ 1 1 : ℝ) * τ.im := by
  rw [hc]
  simp [Complex.div_im]
  rcases eq_or_ne ((δ 1 1 : ℤ) : ℝ) 0 with h | h
  · simp [h]
  · field_simp

theorem max_inv_mul_le (r y : ℝ) (hr : 0 < r) (hy : 0 < y) :
    max (r * y) (r * y)⁻¹ ≤ max r r⁻¹ * max y y⁻¹ := by
  have h1 := one_le_max_inv r hr
  have h2 := one_le_max_inv y hy
  rw [mul_inv]
  apply max_le
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) hy.le (by linarith)
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (inv_pos.mpr hy).le (by linarith)

theorem mod_slz (F : ℍ → ℂ) (k : ℕ) (δ : M2) (hdet : 0 < δ.det) (hc : δ 1 0 = 0) (hF : Mod F) :
    Mod (slz k δ F) := by
  obtain ⟨C, A, hC0, hC⟩ := bound_of_mod F hF
  have hdet' : δ.det = δ 0 0 * δ 1 1 := by rw [Matrix.det_fin_two, hc]; ring
  have had : (0 : ℝ) < (δ 0 0 : ℝ) * (δ 1 1 : ℝ) := by
    have : (0 : ℤ) < δ 0 0 * δ 1 1 := hdet' ▸ hdet
    exact_mod_cast this
  have hd : (δ 1 1 : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at had; exact lt_irrefl _ had
  have hrpos : (0 : ℝ) < (δ 0 0 : ℝ) / (δ 1 1 : ℝ) := by
    have : (δ 0 0 : ℝ) / (δ 1 1 : ℝ) = (δ 0 0 : ℝ) * δ 1 1 / ((δ 1 1 : ℝ) ^ 2) := by
      field_simp
    rw [this]; exact div_pos had (by positivity)
  set r : ℝ := (δ 0 0 : ℝ) / (δ 1 1 : ℝ) with hr
  set K : ℝ := ‖((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹‖ with hK
  set R : ℝ := max r r⁻¹ with hR
  have hR1 : 1 ≤ R := one_le_max_inv r hrpos
  refine mod_of_bound _ (K * (C * R ^ A)) A fun τ => ?_
  have him := im_slz_arg δ hc τ
  rw [← hr] at him
  have hz : 0 < (((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)))).im := by
    rw [him]; exact mul_pos hrpos τ.im_pos
  set w : ℍ := ofComplex ((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ))) with hw
  have hwim : w.im = r * τ.im := by
    rw [hw, ofComplex_apply_of_im_pos hz]; exact him
  have hMw : max w.im w.im⁻¹ ^ A ≤ R ^ A * max τ.im τ.im⁻¹ ^ A := by
    rw [← mul_pow, hwim]
    exact pow_le_pow_left₀ (le_trans zero_le_one (one_le_max_inv _ (mul_pos hrpos τ.im_pos)))
      (max_inv_mul_le r τ.im hrpos τ.im_pos) A
  have hslz : slz k δ F τ = (((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹) * F w := by
    rw [slz, hw]; simp [hc]
  rw [hslz, norm_mul, ← hK]
  have hK0 : 0 ≤ K := norm_nonneg _
  calc K * ‖F w‖ ≤ K * (C * max w.im w.im⁻¹ ^ A) := mul_le_mul_of_nonneg_left (hC w) hK0
    _ ≤ K * (C * (R ^ A * max τ.im τ.im⁻¹ ^ A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMw hC0) hK0
    _ = _ := by ring

theorem mod_algebra : (∀ F G : ℍ → ℂ, Mod F → Mod G → Mod (fun τ => F τ + G τ) ∧ Mod (fun τ => F τ * G τ)) ∧ (∀ c : ℂ, Mod fun _ => c) ∧ (∀ (F : ℍ → ℂ) (k : ℕ) (δ : M2), 0 < δ.det → δ 1 0 = 0 → Mod F → Mod (slz k δ F)) :=
  ⟨fun F G hF hG => ⟨mod_add F G hF hG, mod_mul F G hF hG⟩, mod_const,
    fun F k δ hdet hc hF => mod_slz F k δ hdet hc hF⟩

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStableStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasModerateGrowth_algebra_slash_stable : (∀ F G : ℍ → ℂ, Mod F → Mod G → Mod (fun τ => F τ + G τ) ∧ Mod (fun τ => F τ * G τ)) ∧ (∀ c : ℂ, Mod fun _ => c) ∧ (∀ (F : ℍ → ℂ) (k : ℕ) (δ : M2), 0 < δ.det → δ 1 0 = 0 → Mod F → Mod (slz k δ F)) := by
  first | exact @GlobalTheory.EisM.mod_algebra | exact GlobalTheory.EisM.mod_algebra | (intros; apply GlobalTheory.EisM.mod_algebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFormCoeffSeqDirichletTwistLevelMulSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFormCoeffSeqDirichletTwistLevelMulSq
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.CharTwist

lemma exists_coeffs {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) :
    ∃ c : ZMod M → ℂ, (∀ n : ZMod M, ∑ u, c u * ZMod.stdAddChar (u * n) = ψ n) ∧
      ∀ d u : ZMod M, IsUnit d → c u = ψ d * c (d * u) := by
  refine ⟨fun u => (M : ℂ)⁻¹ * ZMod.dft (fun j => ψ j) u, fun n => ?_, fun d u hd => ?_⟩
  · have h := ZMod.invDFT_apply (ZMod.dft (fun j => ψ j)) n
    rw [LinearEquiv.symm_apply_apply] at h
    rw [h, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]; ring
  · obtain ⟨d, rfl⟩ := hd
    have h := ZMod.dft_comp_unitMul (fun j => ψ j) d (d * u)
    simp only [map_mul] at h
    rw [ZMod.dft_const_mul, Units.inv_mul_cancel_left] at h
    simp only [← h]; ring

lemma summable_of_polyB {a : ℕ → ℂ} (h : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) := by
  obtain ⟨C, A, hC⟩ := h
  set q : ℂ := cexp (2 * π * Complex.I * τ) with hq
  have hq1 : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hq0 : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 (Complex.exp_ne_zero _)
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ A * ‖q‖ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rwa [norm_norm])
  have h2 := ((summable_nat_add_iff 1).2 h1).mul_left (C * ‖q‖⁻¹)
  refine Summable.of_norm_bounded h2 fun n => ?_
  have e : cexp (2 * π * Complex.I * n * τ) = q ^ n := by
    rw [hq, ← Complex.exp_nat_mul]; congr 1; ring
  rw [e, norm_mul, norm_pow]
  calc ‖a n‖ * ‖q‖ ^ n ≤ C * ((n : ℝ) + 1) ^ A * ‖q‖ ^ n :=
        mul_le_mul_of_nonneg_right (hC n) (by positivity)
    _ = _ := by push_cast; field_simp; ring

lemma qs_twist {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) {c : ZMod M → ℂ}
    (hc : ∀ n : ZMod M, ∑ u, c u * ZMod.stdAddChar (u * n) = ψ n) {g : ℕ → ℂ} (hg : PolyB g) (τ : ℍ) :
    qs (fun n => ψ n * g n) τ = ∑ u : ZMod M, c u * qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ) := by
  have a := hasSum_sum (s := Finset.univ) fun (u : ZMod M) _ =>
    (summable_of_polyB hg ((((u.val : ℤ) : ℝ) / M) +ᵥ τ)).hasSum.mul_left (c u)
  unfold qs
  rw [← a.tsum_eq]
  refine tsum_congr fun m => ?_
  beta_reduce
  rw [← hc, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  have : u * (m : ZMod M) = ((u.val * m : ℤ) : ZMod M) := by simp
  have e2 : ZMod.stdAddChar (u * (m : ZMod M)) * cexp (2 * π * Complex.I * m * τ) =
      cexp (2 * π * Complex.I * m * (((((u.val : ℤ) : ℝ) / M) +ᵥ τ : ℍ) : ℂ)) := by
    rw [this, ZMod.stdAddChar_coe, ← Complex.exp_add, coe_vadd]
    congr 1
    push_cast
    ring
  rw [← e2]
  ring

lemma vadd_smul {N M : ℕ} [NeZero M] (γ : SL(2, ℤ)) (hγ : ((N * M ^ 2 : ℕ) : ℤ) ∣ γ 1 0) (u v : ℤ)
    (h : (v : ZMod M) = ((γ 1 1 : ℤ) : ZMod M) ^ 2 * u) (τ : ℍ) :
    ∃ δ : SL(2, ℤ), (N : ℤ) ∣ δ 1 0 ∧ ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ∧
      ((u : ℝ) / M) +ᵥ (γ • τ) = δ • (((v : ℝ) / M) +ᵥ τ) ∧
      ((δ 1 0 : ℤ) : ℂ) * ((((v : ℝ) / M) +ᵥ τ : ℍ) : ℂ) + ((δ 1 1 : ℤ) : ℂ) =
        ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
  obtain ⟨c, hc⟩ := hγ
  push_cast at hc
  have hd := γ.det_coe
  rw [Matrix.det_fin_two, hc] at hd
  have hd' := congrArg (Int.cast : ℤ → ZMod M) hd
  push_cast at hd'
  rw [ZMod.natCast_self] at hd'
  have h1 : (M : ℤ) ∣ u * γ 1 1 - v * γ 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]
    linear_combination (-(u : ZMod M) * ((γ 1 1 : ℤ) : ZMod M)) * hd'
  obtain ⟨e, he⟩ := h1
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  obtain ⟨δ, d00, d01, d10, d11⟩ : ∃ δ : SL(2, ℤ), δ 0 0 = γ 0 0 + u * N * c * M ∧
      δ 0 1 = γ 0 1 + e - u * v * N * c ∧ δ 1 0 = N * M ^ 2 * c ∧ δ 1 1 = γ 1 1 - N * c * v * M := by
    refine ⟨⟨!![γ 0 0 + u * N * c * M, γ 0 1 + e - u * v * N * c; N * M ^ 2 * c, γ 1 1 - N * c * v * M], ?_⟩,
      rfl, rfl, rfl, rfl⟩
    rw [Matrix.det_fin_two_of]
    linear_combination hd + N * M * c * he
  have hden : ((δ 1 0 : ℤ) : ℂ) * ((((v : ℝ) / M) +ᵥ τ : ℍ) : ℂ) + ((δ 1 1 : ℤ) : ℂ) =
        ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    rw [d10, d11, hc, coe_vadd]
    push_cast
    field_simp
    ring
  refine ⟨δ, ⟨M ^ 2 * c, by rw [d10]; ring⟩, by rw [d11]; simp, ?_, hden⟩
  apply UpperHalfPlane.ext
  have e1 := UpperHalfPlane.coe_specialLinearGroup_apply γ τ
  have e2 := UpperHalfPlane.coe_specialLinearGroup_apply δ (((v : ℝ) / M) +ᵥ τ)
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at e1 e2
  have hz := UpperHalfPlane.denom_ne_zero γ τ
  rw [UpperHalfPlane.denom] at hz
  simp at hz
  have he' : (u : ℂ) * (γ 1 1 : ℤ) - v * (γ 0 0 : ℤ) = M * e := by exact_mod_cast he
  have hc' : ((γ 1 0 : ℤ) : ℂ) = N * M ^ 2 * c := by exact_mod_cast hc
  rw [coe_vadd, e1, e2, hden, eq_div_iff hz, add_mul, div_mul_cancel₀ _ hz, d00, d01, coe_vadd, hc']
  push_cast
  field_simp
  linear_combination he'

theorem cf_twist : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ), 0 < M →
    CF k N (ch χ) g → CF k (N * M ^ 2) (fun d => ch χ d * ch φ d ^ 2) (fun n => φ n * g n) := by
  intro k N M χ φ g hM ⟨⟨hp, hi⟩, B, hB⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨c, hc1, hc2⟩ := exists_coeffs φ
  refine ⟨⟨?_, ?_⟩, (∑ u, ‖c u‖ ^ 2) * ∑ _u : ZMod M, B, fun τ => ?_⟩
  · obtain ⟨C, A, hC⟩ := hp
    refine ⟨C, A, fun n => le_trans ?_ (hC n)⟩
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one φ _)
  · intro γ hγ τ
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod M) := by
      obtain ⟨e, he⟩ := hγ
      have dγ := congrArg (Int.cast : ℤ → ZMod M) (γ.det_coe)
      rw [Matrix.det_fin_two, he] at dγ
      push_cast at dγ
      rw [ZMod.natCast_self] at dγ
      exact IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod M) (by linear_combination dγ)
    have hb : Function.Bijective fun u : ZMod M => ((γ 1 1 : ℤ) : ZMod M) ^ 2 * u :=
      ((hu.pow 2).unit.mulLeft).bijective
    rw [qs_twist φ hc1 hp, qs_twist φ hc1 hp,
      ← hb.sum_comp fun u : ZMod M => c u * qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    obtain ⟨δ, h0, h1, h2, h3⟩ := vadd_smul γ hγ (u.val : ℤ) ((((γ 1 1 : ℤ) : ZMod M) ^ 2 * u).val : ℤ)
      (by simp) τ
    rw [h2, hi δ h0, h3, hc2 _ u (hu.pow 2)]
    simp only [ch, h1, map_pow]
    ring
  · rw [qs_twist φ hc1 hp]
    have hy : 0 ≤ τ.im ^ k := pow_nonneg τ.im_pos.le k
    set x : ZMod M → ℂ := fun u => qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ) with hx
    have h1 : ‖∑ u, c u * x u‖ ≤ ∑ u, ‖c u‖ * ‖x u‖ :=
      (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun u _ => norm_mul _ _)
    have h2 : ‖∑ u, c u * x u‖ ^ 2 ≤ (∑ u, ‖c u‖ ^ 2) * ∑ u, ‖x u‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    refine (mul_le_mul_of_nonneg_right h2 hy).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun u _ => sq_nonneg _)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun u _ => ?_
    have := hB ((((u.val : ℤ) : ℝ) / M) +ᵥ τ)
    rwa [vadd_im] at this

end GlobalTheory.EisM.CharTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFormCoeffSeqDirichletTwistLevelMulSqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFormCoeffSeq_dirichletTwist_level_mul_sq : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ), 0 < M → CF k N (ch χ) g → CF k (N * M ^ 2) (fun d => ch χ d * ch φ d ^ 2) (fun n => φ n * g n) := by
  first | exact @GlobalTheory.EisM.CharTwist.cf_twist | exact GlobalTheory.EisM.CharTwist.cf_twist | (intros; apply GlobalTheory.EisM.CharTwist.cf_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongr
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.Glue.DlPow

theorem _root_.GlobalTheory.Glue.DlPow.isAlgebraic_of_tower {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) :
    Algebra.IsAlgebraic ℚ Ω := by
  refine ⟨fun c => ?_⟩
  obtain ⟨D, hD, hint⟩ := X.bdd (algebraMap Ω X.K c)
  obtain ⟨k, hk⟩ := hint 0
  have hc : (algebraMap Ω (HahnSeries ℚ Ω) c).coeff 0 = c := by
    rw [HahnSeries.algebraMap_apply']
    simp
  rw [AlgHom.commutes, hc] at hk
  have h1 : IsAlgebraic ℚ ((D : Ω) ^ k * c) := (hk.tower_top (A := ℚ)).isAlgebraic
  have hD' : ((D : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hD.ne')
  have hc' : c = algebraMap ℚ Ω (((D : ℚ) ^ k)⁻¹) * ((D : Ω) ^ k * c) := by
    rw [← mul_assoc, ← map_natCast (algebraMap ℚ Ω), ← map_pow, ← map_mul, inv_mul_cancel₀ hD',
      map_one, one_mul]
  rw [hc']
  exact (isAlgebraic_algebraMap _).mul h1

private lemma prim_pow_succ {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
    {P : HahnSeries ℚ Ω} (hP : _root_.GlobalTheory.Glue.Prim A P) (k : ℕ) :
    _root_.GlobalTheory.Glue.Prim A (P ^ (k + 1)) := by
  induction k with
  | zero => rwa [zero_add, pow_one]
  | succ k ih =>
    rw [pow_succ]
    exact _root_.GlobalTheory.Glue.Prim.mul A _ _ ih hP

private lemma theta_pow_succ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ)
    (P : HahnSeries ℚ Ω) (k : ℕ) :
    _root_.GlobalTheory.Glue.theta s (P ^ (k + 1)) =
      HahnSeries.C ((k + 1 : ℕ) : Ω) * P ^ k * _root_.GlobalTheory.Glue.theta s P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, (_root_.GlobalTheory.Glue.theta_leibniz_add_const s _ _).1, ih]
    push_cast
    simp only [map_add (f := _), map_natCast, map_one]
    ring

private lemma theta_one_coeff_mem_of_integral_den_one {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω) {P : HahnSeries ℚ Ω} (hP : ∀ r, P.coeff r ∈ A)
    (hden : ∀ r, P.coeff r ≠ 0 → r.den = 1) (r : ℚ) :
    (_root_.GlobalTheory.Glue.theta 1 P).coeff r ∈ A := by
  show algebraMap ℚ Ω (1 * r) * P.coeff r ∈ A
  by_cases h : P.coeff r = 0
  · rw [h, mul_zero]
    exact zero_mem A
  · refine mul_mem ?_ (hP r)
    rw [one_mul, ← Rat.coe_int_num_of_den_eq_one (hden r h), map_intCast]
    exact intCast_mem A _

private lemma hahnSeries_coeff_mul_mem_valuationSubring {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) :
    (x * y).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact sum_mem fun ij _ => mul_mem (hx _) (hy _)

private lemma hahnSeries_coeff_pow_mem_valuationSubring {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {x : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (k : ℕ) (r : ℚ) : (x ^ k).coeff r ∈ A := by
  induction k generalizing r with
  | zero =>
    rw [pow_zero, HahnSeries.coeff_one]
    split_ifs
    · exact one_mem A
    · exact zero_mem A
  | succ k ih =>
    rw [pow_succ]
    exact hahnSeries_coeff_mul_mem_valuationSubring A ih hx r

theorem _root_.GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime], (l : Ω) ∈ A.nonunits →
    ∀ (n : ℕ) (f u : X.K), f ≠ 0 → u ≠ 0 →
      X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) u = u →
      ∀ φ φ' : HahnSeries ℚ Ω, _root_.GlobalTheory.Glue.IsDl X A l n 1 f φ →
        _root_.GlobalTheory.Glue.IsDl X A l n 1 (f * u ^ (l ^ n)) φ' →
          ∀ r, _root_.GlobalTheory.Glue.CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A l _ hl n f u hf hu hT φ φ' hφ hφ' r
  have hj : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g _root_.GlobalTheory.KZ.Hs ∧
      X.an X.jK = ↑g := by
    obtain ⟨g, h1, h2⟩ := X.j_hol
    exact ⟨g, h2, h1⟩
  have hden : ∀ x : X.K,
      X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) x = x →
        ∀ s, (X.exp x).coeff s ≠ 0 → s.den = 1 := by
    intro x hx s hs
    have hmem : x ∈ _root_.GlobalTheory.Glue.KT X 1 := by
      rw [_root_.GlobalTheory.Glue.KT.mem_def, pow_one]
      exact hx
    simpa using (_root_.GlobalTheory.Glue.KTExp.mem_KT_iff ε X 1 one_pos x).1 hmem s hs
  have hu0 : _root_.GlobalTheory.Glue.IsDl X A l n 1 (u ^ (l ^ n)) 0 := by
    obtain ⟨a, b, κ, S, hκ, hab, hPa, hPb, hb, -⟩ :=
      _root_.GlobalTheory.exists_prim_frac_level_one ε X hj l A hl u hu
    have hbT := hb ModularGroup.T
    have haT : X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) a = a := by
      have h1 := congrArg (X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T)) hab
      rw [map_mul, map_mul, hT, hbT, AlgEquiv.commutes, hab] at h1
      exact (mul_left_cancel₀ ((map_ne_zero _).2 hκ) h1).symm
    obtain ⟨k, hk⟩ : ∃ k, l ^ n = k + 1 :=
      ⟨l ^ n - 1, (Nat.succ_pred_eq_of_pos (pow_pos (Fact.out : l.Prime).pos n)).symm⟩
    have hl' : (l : Ω) ^ n = ((k + 1 : ℕ) : Ω) := by rw [← Nat.cast_pow, hk]
    have hPaA := hPa.1
    have hPbA := hPb.1
    unfold _root_.GlobalTheory.Glue.IsDl
    refine ⟨fun s => by simpa using zero_mem A, a ^ (l ^ n), b ^ (l ^ n), κ ^ (l ^ n),
      pow_ne_zero _ hκ, by rw [map_pow, ← mul_pow, ← mul_pow, hab], ?_, ?_, fun s => ?_⟩
    · rw [map_pow, hk]
      exact prim_pow_succ hPa k
    · rw [map_pow, hk]
      exact prim_pow_succ hPb k
    · rw [map_pow, map_pow, hk, theta_pow_succ, theta_pow_succ]
      set P := X.exp a
      set Q := X.exp b
      set W := P ^ k * Q ^ k *
        (_root_.GlobalTheory.Glue.theta 1 P * Q - P * _root_.GlobalTheory.Glue.theta 1 Q)
      have hW : W.coeff s ∈ A := by
        have hθP := theta_one_coeff_mem_of_integral_den_one A hPaA (hden a haT)
        have hθQ := theta_one_coeff_mem_of_integral_den_one A hPbA (hden b hbT)
        refine hahnSeries_coeff_mul_mem_valuationSubring A
          (hahnSeries_coeff_mul_mem_valuationSubring A (hahnSeries_coeff_pow_mem_valuationSubring A hPaA k)
            (hahnSeries_coeff_pow_mem_valuationSubring A hPbA k)) (fun t => ?_) s
        rw [HahnSeries.coeff_sub]
        exact sub_mem (hahnSeries_coeff_mul_mem_valuationSubring A hθP hPbA t)
          (hahnSeries_coeff_mul_mem_valuationSubring A hPaA hθQ t)
      have hexp : HahnSeries.C ((k + 1 : ℕ) : Ω) * P ^ k * _root_.GlobalTheory.Glue.theta 1 P *
          Q ^ (k + 1) -
          P ^ (k + 1) * (HahnSeries.C ((k + 1 : ℕ) : Ω) * Q ^ k * _root_.GlobalTheory.Glue.theta 1 Q) =
          HahnSeries.C ((k + 1 : ℕ) : Ω) * W := by
        simp only [W]
        ring
      unfold _root_.GlobalTheory.Glue.CgA
      refine ⟨-W.coeff s, neg_mem hW, ?_⟩
      rw [hexp, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, zero_mul, zero_mul,
        HahnSeries.coeff_zero, hl', smul_eq_mul]
      ring
  have h := (_root_.GlobalTheory.Glue.isDl_calc ε X hj l A hl n 1 f (u ^ (l ^ n)) φ 0).1
    hφ hu0
  simpa using _root_.GlobalTheory.Glue.isDl_unique ε X hj l A hl n 1 _ _ _ h hφ' r

end GlobalTheory.Glue.DlPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongrStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDerivQExpansion_mul_primePow_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime], (l : Ω) ∈ A.nonunits → ∀ (n : ℕ) (f u : X.K), f ≠ 0 → u ≠ 0 → X.sl (ofSL ModularGroup.T) u = u → ∀ φ φ' : HahnSeries ℚ Ω, IsDl X A l n 1 f φ → IsDl X A l n 1 (f * u ^ (l ^ n)) φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  exact @GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong Ω _ _ _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearFunctionalEqCoeffLinearCombinationFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearFunctionalEqCoeffLinearCombinationFinite
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem func_eq_lam : ∀ (S : Set (ℕ → ℂ)) (B : ℕ) (φ : (ℕ → ℂ) → ℂ), 0 ∈ S → (∀ a ∈ S, ∀ b ∈ S, a + b ∈ S ∧ φ (a + b) = φ a + φ b) → (∀ c : ℂ, ∀ a ∈ S, c • a ∈ S ∧ φ (c • a) = c * φ a) → (∀ a ∈ S, (∀ n < B, a n = 0) → a = 0) → ∃ c : ℕ → ℂ, ∀ a ∈ S, φ a = lam B c a := by
  intro S B φ h0 hadd hsmul hdet
  classical
  let W : Submodule ℂ (ℕ → ℂ) :=
    { carrier := S
      add_mem' := fun {a b} ha hb => (hadd a ha b hb).1
      zero_mem' := h0
      smul_mem' := fun c a ha => (hsmul c a ha).1 }
  let φW : W →ₗ[ℂ] ℂ :=
    { toFun := fun a => φ a
      map_add' := fun a b => (hadd a a.2 b b.2).2
      map_smul' := fun c a => (hsmul c a a.2).2 }
  let r : W →ₗ[ℂ] (Fin B → ℂ) :=
    { toFun := fun a i => (a : ℕ → ℂ) i
      map_add' := fun a b => by ext i; rfl
      map_smul' := fun c a => by ext i; rfl }
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    apply Subtype.ext
    refine hdet a a.2 (fun n hn => ?_)
    have := congrFun ha ⟨n, hn⟩
    simpa [r] using this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective r hr
  let ψ : (Fin B → ℂ) →ₗ[ℂ] ℂ := φW.comp g
  refine ⟨fun n => if h : n < B then ψ (Pi.single ⟨n, h⟩ 1) else 0, fun a ha => ?_⟩
  have h1 : φ a = ψ (r ⟨a, ha⟩) := by
    show φW ⟨a, ha⟩ = φW (g (r ⟨a, ha⟩))
    rw [← LinearMap.comp_apply g r, hg, LinearMap.id_apply]
  rw [h1, LinearMap.pi_apply_eq_sum_univ ψ (r ⟨a, ha⟩), EisM.lam,
    Finset.sum_range (fun n => (if h : n < B then ψ (Pi.single ⟨n, h⟩ 1) else 0) * a n)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [i.2, dif_pos, Fin.eta, r, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  have hs : (fun j : Fin B => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [hs, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearFunctionalEqCoeffLinearCombinationFiniteStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearFunctional_eq_coeffLinearCombinationFinite : ∀ (S : Set (ℕ → ℂ)) (B : ℕ) (φ : (ℕ → ℂ) → ℂ), 0 ∈ S → (∀ a ∈ S, ∀ b ∈ S, a + b ∈ S ∧ φ (a + b) = φ a + φ b) → (∀ c : ℂ, ∀ a ∈ S, c • a ∈ S ∧ φ (c • a) = c * φ a) → (∀ a ∈ S, (∀ n < B, a n = 0) → a = 0) → ∃ c : ℕ → ℂ, ∀ a ∈ S, φ a = lam B c a := by
  first | exact @GlobalTheory.func_eq_lam | exact GlobalTheory.func_eq_lam | (intros; apply GlobalTheory.func_eq_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootsNormLeOfBoundedTwoStepRecurrence
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootsNormLeOfBoundedTwoStepRecurrence
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem norm_le_of_bounded_two_step_recursion (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ) (hR : 0 ≤ R)
    (h0 : c 0 = 1) (h1 : c 1 = x + y)
    (hrec : ∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r)
    (hb : ∀ r, ‖c r‖ ≤ C * R ^ r) : ‖x‖ ≤ R := by
  have hd : ∀ r : ℕ, c (r + 1) - y * c r = x ^ (r + 1) := by
    intro r
    induction r with
    | zero => simp [h0, h1]
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by ring]
      linear_combination hrec n + x * ih
  have key : ∀ r : ℕ, ‖x‖ ^ (r + 1) ≤ C * (R + ‖y‖) * R ^ r := by
    intro r
    calc ‖x‖ ^ (r + 1) = ‖c (r + 1) - y * c r‖ := by rw [hd r, norm_pow]
      _ ≤ ‖c (r + 1)‖ + ‖y‖ * ‖c r‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ C * R ^ (r + 1) + ‖y‖ * (C * R ^ r) :=
          add_le_add (hb _) (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
      _ = C * (R + ‖y‖) * R ^ r := by ring
  by_contra hlt
  push_neg at hlt
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hlt
  have hq0 : 0 ≤ R / ‖x‖ := div_nonneg hR hxpos.le
  have hq1 : R / ‖x‖ < 1 := (div_lt_one hxpos).2 hlt
  have ht : Tendsto (fun r : ℕ => C * (R + ‖y‖) * (R / ‖x‖) ^ r) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (C * (R + ‖y‖))
  have hle : ∀ r : ℕ, ‖x‖ ≤ C * (R + ‖y‖) * (R / ‖x‖) ^ r := by
    intro r
    have hpos : 0 < ‖x‖ ^ r := pow_pos hxpos r
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hpos, ← pow_succ']
    exact key r
  have : ‖x‖ ≤ 0 := ge_of_tendsto' ht hle
  linarith

theorem roots_norm_le_of_bounded_two_step_recursion :
    ∀ (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ), 0 ≤ R → c 0 = 1 → c 1 = x + y →
      (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∀ r, ‖c r‖ ≤ C * R ^ r) →
      ‖x‖ ≤ R ∧ ‖y‖ ≤ R := by
  intro x y c C R hR h0 h1 hrec hb
  refine ⟨norm_le_of_bounded_two_step_recursion x y c C R hR h0 h1 hrec hb,
    norm_le_of_bounded_two_step_recursion y x c C R hR h0 (by rw [h1, add_comm]) ?_ hb⟩
  intro r
  rw [hrec r]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootsNormLeOfBoundedTwoStepRecurrenceStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_norm_le_of_bounded_two_step_recurrence : ∀ (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ), 0 ≤ R → c 0 = 1 → c 1 = x + y → (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∀ r, ‖c r‖ ≤ C * R ^ r) → ‖x‖ ≤ R ∧ ‖y‖ ≤ R := by
  first | exact @GlobalTheory.roots_norm_le_of_bounded_two_step_recursion | exact GlobalTheory.roots_norm_le_of_bounded_two_step_recursion | (intros; apply GlobalTheory.roots_norm_le_of_bounded_two_step_recursion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CharElementary
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem qs_coef_of_mfc {k M : ℕ} [NeZero M] {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma1 M) (k : ℤ)] (f : F) : qs (coef f) = ⇑f := by
  funext τ
  have h := ModularForm.hasSum_qExpansion f one_pos (by simp) τ
  rw [qs, ← h.tsum_eq]
  congr 1
  funext n
  rw [coef, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem polyB_of_isBigO {a : ℕ → ℂ} {k : ℕ}
    (h : (fun n => a n) =O[atTop] fun n : ℕ => (n : ℝ) ^ k) : PolyB a := by
  obtain ⟨c, hc⟩ := h.bound
  rw [eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  have hS : 0 ≤ ∑ n ∈ Finset.range N, ‖a n‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨|c| + ∑ n ∈ Finset.range N, ‖a n‖, k, fun n => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := one_le_pow₀ (by linarith)
  by_cases hn : N ≤ n
  · have h2 := hN n hn
    rw [Real.norm_of_nonneg (by positivity)] at h2
    calc ‖a n‖ ≤ c * (n : ℝ) ^ k := h2
      _ ≤ |c| * ((n : ℝ) + 1) ^ k :=
          mul_le_mul (le_abs_self c) (pow_le_pow_left₀ hn0 (by linarith) k) (by positivity) (abs_nonneg c)
      _ ≤ (|c| + ∑ n ∈ Finset.range N, ‖a n‖) * ((n : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have h2 : ‖a n‖ ≤ ∑ n ∈ Finset.range N, ‖a n‖ :=
      Finset.single_le_sum (f := fun n => ‖a n‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
    calc ‖a n‖ ≤ |c| + ∑ n ∈ Finset.range N, ‖a n‖ := by linarith [abs_nonneg c]
      _ ≤ (|c| + ∑ n ∈ Finset.range N, ‖a n‖) * ((n : ℝ) + 1) ^ k :=
          le_mul_of_one_le_right (by positivity) h1

theorem inv_of_hasChar {k M : ℕ} (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) (hf : HasChar k χ f) :
    Inv k M (ch χ) f := by
  intro γ hγ τ
  have hmem : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hγ
  have h := congrFun (hf γ hmem) τ
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul] at h
  have hd : denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom]
  have hne : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  rw [← hd, ch]
  rw [zpow_neg, zpow_natCast] at h
  have hk : denom (γ : GL (Fin 2) ℝ) τ ^ k ≠ 0 := pow_ne_zero _ hne
  field_simp at h
  rw [h]
  ring

theorem mf_of_mfc {k M : ℕ} [NeZero M] {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma1 M) (k : ℤ)] (χ : DirichletCharacter ℂ M) (f : F) (hf : HasChar k χ f) :
    qs (coef f) = ⇑f ∧ MF k M (ch χ) (coef f) := by
  have hq := qs_coef_of_mfc (k := k) f
  refine ⟨hq, ?_, ?_⟩
  · have h := ModularFormClass.qExpansion_isBigO (Int.natCast_nonneg k) f
    simp only [strictWidthInfty_Gamma1, zpow_natCast] at h
    exact polyB_of_isBigO h
  · rw [hq]; exact inv_of_hasChar χ f hf

theorem gamma1_char_elementary : ∀ (k M : ℕ) (χ : DirichletCharacter ℂ M), 0 < M →
    (∀ f : ModularForm (Gamma1 M) (k : ℤ), HasChar k χ f → qs (coef f) = ⇑f ∧ MF k M (ch χ) (coef f)) ∧
    ∀ f : CuspForm (Gamma1 M) (k : ℤ), HasChar k χ f → qs (coef f) = ⇑f ∧ CF k M (ch χ) (coef f) := by
  intro k M χ hM
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨fun f hf => mf_of_mfc χ f hf, fun f hf => ?_⟩
  obtain ⟨hq, hmf⟩ := mf_of_mfc χ f hf
  refine ⟨hq, hmf, ?_⟩
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (Gamma1 M) f f
  refine ⟨C, fun τ => ?_⟩
  have h := hC τ
  rw [hq]
  simp only [petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real,
    zpow_natCast, norm_pow, Real.norm_of_nonneg τ.im_pos.le] at h
  calc ‖f τ‖ ^ 2 * τ.im ^ k = ‖f τ‖ * ‖f τ‖ * τ.im ^ k := by ring
    _ ≤ C := h

end GlobalTheory.EisM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmul
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

def rowZ (γ : SL(2, ℤ)) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun x := (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1)
  invFun x := (x.1 * γ 1 1 - x.2 * γ 1 0, -(x.1 * γ 0 1) + x.2 * γ 0 0)
  left_inv x := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    ext
    · simp only; linear_combination x.1 * h
    · simp only; linear_combination x.2 * h
  right_inv x := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    ext
    · simp only; linear_combination x.1 * h
    · simp only; linear_combination x.2 * h

theorem rowZ_apply (γ : SL(2, ℤ)) (x : ℤ × ℤ) :
    rowZ γ x = (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) := rfl

theorem rowZ_add_smul (γ : SL(2, ℤ)) (x v : ℤ × ℤ) (r : ℤ) :
    rowZ γ (x + r • v) = rowZ γ x + r • rowZ γ v := by
  simp only [rowZ_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.mk_add_mk, Prod.smul_mk]
  ext <;> simp only <;> ring

theorem dif_comp_rowZ (L : ℕ) (γ : SL(2, ℤ)) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => F (rowZ γ y)) = fun x => dif L (rowZ γ v) F (rowZ γ x) := by
  funext x
  simp only [dif, rowZ_add_smul]

theorem dif_const_mul (L : ℕ) (v : ℤ × ℤ) (c : ℂ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => c * F y) = fun x => c * dif L v F x := by
  funext x
  simp only [dif, ← Finset.mul_sum]
  ring

theorem lat_smul (j L : ℕ) (v : ℤ × ℤ) (Φ Φ' : ℤ × ℤ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ)
    (hΦ : ∀ x : ℤ × ℤ, Φ' (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x) :
    lat j 0 L v Φ (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ j *
      lat j 0 L (v.1 * γ 0 0 + v.2 * γ 1 0, v.1 * γ 0 1 + v.2 * γ 1 1) Φ' τ := by
  set D : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hD
  have hD0 : D ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ τ
    simpa [UpperHalfPlane.denom, hD] using this
  have hcoe : ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / D := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp [hD]
  set H : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hH
  have hG : (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + y.2)) =
      fun y => D ^ j * H (rowZ γ y) := by
    funext y
    simp only [hH, trm, rowZ_apply, hcoe, mul_zero, neg_mul, Real.rpow_zero, Complex.ofReal_one, mul_one]
    have : (y.1 : ℂ) * ((((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / D) + y.2 =
        ((((y.1 * γ 0 0 + y.2 * γ 1 0 : ℤ)) : ℂ) * τ + ((y.1 * γ 0 1 + y.2 * γ 1 1 : ℤ) : ℂ)) / D := by
      field_simp
      push_cast
      ring
    rw [this, div_pow, inv_div]
    ring_nf
  have hdd : ∀ x, dif L v (dif L v fun y => trm j 0 ((y.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + y.2)) x =
      D ^ j * dif L (rowZ γ v) (dif L (rowZ γ v) H) (rowZ γ x) := by
    intro x
    rw [hG, dif_const_mul, dif_const_mul]
    simp only
    rw [dif_comp_rowZ]
    rw [show (fun x => dif L (rowZ γ v) H (rowZ γ x)) = fun x => (dif L (rowZ γ v) H) (rowZ γ x) from rfl,
      dif_comp_rowZ]
  unfold lat
  simp_rw [hdd]
  have hΦ' : ∀ x, Φ x = Φ' (rowZ γ x) := fun x => (hΦ x).symm
  simp_rw [hΦ']
  rw [Equiv.tsum_eq (rowZ γ) (fun z => Φ' z * (D ^ j * dif L (rowZ γ v) (dif L (rowZ γ v) H) z)),
    ← tsum_mul_left]
  congr 1
  funext x
  rw [hH]
  simp only [rowZ_apply]
  ring

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmulStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_slTwo_smul : ∀ (j L : ℕ) (v : ℤ × ℤ) (Φ Φ' : ℤ × ℤ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ), (∀ x : ℤ × ℤ, Φ' (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x) → lat j 0 L v Φ (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ j * lat j 0 L (v.1 * γ 0 0 + v.2 * γ 1 0, v.1 * γ 0 1 + v.2 * γ 1 1) Φ' τ := by
  first | exact @GlobalTheory.EisM.lat_smul | exact GlobalTheory.EisM.lat_smul | (intros; apply GlobalTheory.EisM.lat_smul <;> assumption)
end
end
