module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableCardDivisorsSqDivOneAddRpow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableCardDivisorsSqDivOneAddRpow
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.DivSq

theorem four_factors {n x y : ℕ} (hx : x ∣ n) (hy : y ∣ n) (hn : n ≠ 0) :
    ∃ a b c e : ℕ, a * b * c * e = n ∧ a * b = x ∧ a * c = y := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hn (by simpa using hx)
  obtain ⟨e, he⟩ := Nat.lcm_dvd hx hy
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_left x y
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_right x y
  refine ⟨Nat.gcd x y, b, c, e, ?_, hb.symm, hc.symm⟩
  have hg : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hx0)
  have h1 := Nat.gcd_mul_lcm x y
  have h2 : Nat.gcd x y * b * c = Nat.lcm x y := by
    apply Nat.eq_of_mul_eq_mul_left hg
    rw [h1]
    calc Nat.gcd x y * (Nat.gcd x y * b * c) = (Nat.gcd x y * b) * (Nat.gcd x y * c) := by ring
      _ = x * y := by rw [← hb, ← hc]
  rw [h2, ← he]

theorem inv_rpow_natCast_mul (p : ℝ) (a b : ℕ) :
    ((((a * b : ℕ)) : ℝ) ^ p)⁻¹ = ((a : ℝ) ^ p)⁻¹ * ((b : ℝ) ^ p)⁻¹ := by
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), mul_inv]

theorem sum_range_le_pow (p : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ p
      ≤ (∑ n ∈ Finset.range N, ((n : ℝ) ^ p)⁻¹) ^ 4 := by
  classical
  set I := Finset.range N with hI
  let φ : ℕ × ℕ × ℕ × ℕ → (Σ _ : ℕ, ℕ × ℕ) :=
    fun q => ⟨q.1 * q.2.1 * q.2.2.1 * q.2.2.2, q.1 * q.2.1, q.1 * q.2.2.1⟩
  let w : (Σ _ : ℕ, ℕ × ℕ) → ℝ := fun s => ((s.1 : ℝ) ^ p)⁻¹
  have hw : ∀ s, 0 ≤ w s := fun s => by simp only [w]; positivity
  have h1 : ∑ n ∈ I, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ p
      = ∑ s ∈ I.sigma (fun n => n.divisors ×ˢ n.divisors), w s := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [w, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast
    ring
  have h2 : I.sigma (fun n => n.divisors ×ˢ n.divisors) ⊆ (I ×ˢ I ×ˢ I ×ˢ I).image φ := by
    rintro ⟨n, x, y⟩ hs
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisors, hI, Finset.mem_range] at hs
    obtain ⟨hnN, ⟨hx, hn⟩, hy, -⟩ := hs
    obtain ⟨a, b, c, e, rfl, rfl, rfl⟩ := four_factors hx hy hn
    have key : ∀ d, d ∣ a * b * c * e → d ∈ I := fun d hd => by
      rw [hI, Finset.mem_range]
      exact lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hnN
    refine Finset.mem_image.2 ⟨(a, b, c, e), ?_, rfl⟩
    simp only [Finset.mem_product]
    exact ⟨key _ ⟨b * c * e, by ring⟩, key _ ⟨a * c * e, by ring⟩, key _ ⟨a * b * e, by ring⟩,
      key _ ⟨a * b * c, by ring⟩⟩
  have h3 : ∑ s ∈ (I ×ˢ I ×ˢ I ×ˢ I).image φ, w s ≤ ∑ q ∈ I ×ˢ I ×ˢ I ×ˢ I, w (φ q) :=
    Finset.sum_image_le_of_nonneg (fun s _ => hw s)
  have h4 : ∑ q ∈ I ×ˢ I ×ˢ I ×ˢ I, w (φ q) = (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) ^ 4 := by
    have : (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) ^ 4 = (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) *
      ((∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) * ((∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) * (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹))) := by
      ring
    rw [this]
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [w, φ]
    rw [inv_rpow_natCast_mul, inv_rpow_natCast_mul, inv_rpow_natCast_mul]
    ring
  rw [h1, ← h4]
  exact (Finset.sum_le_sum_of_subset_of_nonneg h2 fun s _ _ => hw s).trans h3

theorem summable_card_divisors_sq_div_rpow :
    ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro s hs
  have hz : Summable fun n : ℕ => ((n : ℝ) ^ (1 + s))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine summable_of_sum_range_le (c := (∑' n : ℕ, ((n : ℝ) ^ (1 + s))⁻¹) ^ 4)
    (fun n => by positivity) fun N => ?_
  refine (sum_range_le_pow (1 + s) N).trans ?_
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => by positivity)
    (hz.sum_le_tsum _ fun n _ => by positivity) 4

end GlobalTheory.DivSq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableCardDivisorsSqDivOneAddRpowStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_card_divisors_sq_div_one_add_rpow : ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ (1 + s) := by
  first | exact @GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow | exact GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow | (intros; apply GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormConjugateCoefficientsInvChar
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormConjugateCoefficientsInvChar
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.ConjForm

def refl (τ : ℍ) : ℍ := ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩

@[simp] lemma coe_refl (τ : ℍ) : ((refl τ : ℍ) : ℂ) = -conj (τ : ℂ) := rfl

@[simp] lemma im_refl (τ : ℍ) : (refl τ).im = τ.im := by
  change (-conj (τ : ℂ)).im = τ.im
  simp [UpperHalfPlane.coe_im]

lemma qs_conj (g : ℕ → ℂ) (τ : ℍ) : qs (fun n => conj (g n)) τ = conj (qs g (refl τ)) := by
  unfold qs
  rw [Complex.conj_tsum]
  congr 1
  funext n
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp [coe_refl, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]

def twist (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linarith⟩

lemma refl_smul (γ : SL(2, ℤ)) (τ : ℍ) : refl (γ • τ) = twist γ • refl τ := by
  apply UpperHalfPlane.ext
  have e := UpperHalfPlane.coe_specialLinearGroup_apply γ τ
  have e2 := UpperHalfPlane.coe_specialLinearGroup_apply (twist γ) (refl τ)
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at e e2
  have hd := UpperHalfPlane.denom_ne_zero γ τ
  rw [UpperHalfPlane.denom] at hd
  simp at hd
  rw [coe_refl, e, e2, coe_refl, map_div₀]
  have hd' : conj (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ≠ 0 := (map_ne_zero _).2 hd
  have hd'' : ((twist γ 1 0 : ℤ) : ℂ) * (-conj (τ : ℂ)) + ((twist γ 1 1 : ℤ) : ℂ) =
      conj (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
    simp [twist, map_add (f := _), map_mul, map_intCast]
  rw [hd'', neg_div', div_left_inj' hd']
  simp [twist, map_add (f := _), map_mul, map_intCast]
  ring

lemma conj_ch {N : ℕ} (χ : DirichletCharacter ℂ N) (d : ℤ) : conj (ch χ d) = ch χ⁻¹ d := by
  unfold ch
  exact MulChar.star_apply' χ _

end GlobalTheory.EisM.ConjForm

namespace GlobalTheory.EisM.ConjForm

lemma polyB_conj {g : ℕ → ℂ} (h : PolyB g) : PolyB (fun n => conj (g n)) := by
  obtain ⟨C, A, hC⟩ := h
  exact ⟨C, A, fun n => by simpa using hC n⟩

lemma inv_conj {k L : ℕ} {χ : DirichletCharacter ℂ L} {g : ℕ → ℂ} (h : Inv k L (ch χ) (qs g)) :
    Inv k L (ch χ⁻¹) (qs (fun n => conj (g n))) := by
  intro γ hc τ
  have h1 := h (twist γ) (by simpa [twist] using hc) (refl τ)
  rw [qs_conj, qs_conj, refl_smul, h1, map_mul, map_mul, map_pow, conj_ch]
  congr 2
  simp [twist, map_add (f := _), map_mul, map_intCast]

lemma cf_conj {k N : ℕ} {χ : DirichletCharacter ℂ N} {g : ℕ → ℂ} (h : CF k N (ch χ) g) :
    CF k N (ch χ⁻¹) (fun n => conj (g n)) := by
  obtain ⟨⟨hp, hi⟩, C, hC⟩ := h
  refine ⟨⟨polyB_conj hp, inv_conj hi⟩, C, fun τ => ?_⟩
  have := hC (refl τ)
  rw [im_refl] at this
  rwa [qs_conj, Complex.norm_conj]

theorem conj_form : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ),
    (CF k N (ch χ) g → CF k N (ch χ⁻¹) (fun n => conj (g n))) ∧
    (Prim k N χ g → Prim k N χ⁻¹ (fun n => conj (g n))) := by
  intro k N χ g
  refine ⟨cf_conj, fun h => ⟨cf_conj h.cf, by simp [h.one], fun n hn => by simp [h.zero n hn], ?_⟩⟩
  intro q hq hqN
  funext n
  have e := congrFun (h.eig q hq hqN) n
  have e' := congrArg conj e
  simp only [To, Vo, map_add (f := _), map_mul, map_pow, map_natCast, conj_ch] at e'
  simp only [To, Vo]
  rw [← e']
  congr 2
  split_ifs <;> simp

end GlobalTheory.EisM.ConjForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormConjugateCoefficientsInvCharStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), (CF k N (ch χ) g → CF k N (ch χ⁻¹) (fun n => conj (g n))) ∧ (Prim k N χ g → Prim k N χ⁻¹ (fun n => conj (g n))) := by
  first | exact @GlobalTheory.EisM.ConjForm.conj_form | exact GlobalTheory.EisM.ConjForm.conj_form | (intros; apply GlobalTheory.EisM.ConjForm.conj_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqEqOfPosCoeffEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqEqOfPosCoeffEq
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma summable_norm_qterm_of_polyB (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := by
  obtain ⟨C, A, hC⟩ := ha
  set r : ℝ := Real.exp (-2 * π * τ.im) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero, Real.exp_lt_exp]
    have := τ.im_pos
    nlinarith [Real.pi_pos]
  have hnorm : ∀ n : ℕ, ‖cexp (2 * π * Complex.I * n * τ)‖ = r ^ n := by
    intro n
    rw [Complex.norm_exp, hr, ← Real.exp_nat_mul]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hg : Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r ^ n := by
    have h0 : Summable fun n : ℕ => (n : ℝ) ^ A * r ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    have h1 := (summable_nat_add_iff 1).mpr h0
    have h2 := h1.mul_left r⁻¹
    refine h2.congr fun n => ?_
    push_cast
    rw [pow_succ]
    field_simp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hg.mul_left C)
  rw [norm_mul, hnorm n, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hr0.le n)

end GlobalTheory.EisM

namespace GlobalTheory.EisM

lemma qs_sub_eq_const (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) (hab : ∀ n, n ≠ 0 → a n = b n) (τ : ℍ) :
    qs a τ - qs b τ = a 0 - b 0 := by
  unfold qs
  rw [← (summable_norm_qterm_of_polyB a ha τ).of_norm.tsum_sub (summable_norm_qterm_of_polyB b hb τ).of_norm]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    rw [hab n hn, sub_self]

theorem eq_of_coeff_pos_eq : ∀ (k L : ℕ) (χ : ℤ → ℂ) (a b : ℕ → ℂ), 1 ≤ k → 0 < L → MF k L χ a → MF k L χ b →
    (∀ n, n ≠ 0 → a n = b n) → a = b := by
  intro k L χ a b hk hL ha hb hab
  set c : ℂ := a 0 - b 0 with hc
  have hconst := qs_sub_eq_const a b ha.1 hb.1 hab
  let γ : SL(2, ℤ) := ⟨!![1, 0; (L : ℤ), 1], by simp [Matrix.det_fin_two]⟩
  have hγ10 : γ 1 0 = (L : ℤ) := rfl
  have hγ11 : γ 1 1 = 1 := rfl
  have key : ∀ τ : ℍ, c = χ 1 * ((L : ℂ) * τ + 1) ^ k * c := by
    intro τ
    have h1 := ha.2 γ (by rw [hγ10]) τ
    have h2 := hb.2 γ (by rw [hγ10]) τ
    rw [hγ10, hγ11] at h1 h2
    have e1 := hconst (γ • τ)
    rw [h1, h2, ← mul_sub, hconst τ, ← hc] at e1
    push_cast at e1
    exact e1.symm
  by_contra hne
  have hc0 : c ≠ 0 := by
    intro h0
    apply hne
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · exact sub_eq_zero.mp h0
    · exact hab n hn
  have hone : ∀ τ : ℍ, ‖χ 1‖ * ‖(L : ℂ) * τ + 1‖ ^ k = 1 := by
    intro τ
    have h := key τ
    have h' : χ 1 * ((L : ℂ) * τ + 1) ^ k = 1 := by
      have : (χ 1 * ((L : ℂ) * τ + 1) ^ k - 1) * c = 0 := by rw [sub_mul, ← h]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc0)
    rw [← norm_pow, ← norm_mul, h', norm_one]
  let τ₁ : ℍ := ⟨Complex.I, by simp⟩
  let τ₂ : ℍ := ⟨2 * Complex.I, by simp⟩
  have e1 := hone τ₁
  have e2 := hone τ₂
  have hχ : ‖χ 1‖ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e1; exact zero_ne_one e1
  have heq : ‖(L : ℂ) * τ₁ + 1‖ ^ k = ‖(L : ℂ) * τ₂ + 1‖ ^ k :=
    mul_left_cancel₀ hχ (e1.trans e2.symm)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hlt : ‖(L : ℂ) * τ₁ + 1‖ < ‖(L : ℂ) * τ₂ + 1‖ := by
    have s1 : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 = 1 + (L : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [τ₁, UpperHalfPlane.coe_mk]
      ring
    have s2 : ‖(L : ℂ) * τ₂ + 1‖ ^ 2 = 1 + 4 * (L : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [τ₂, UpperHalfPlane.coe_mk]
      ring
    have : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 < ‖(L : ℂ) * τ₂ + 1‖ ^ 2 := by
      rw [s1, s2]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
  have := pow_lt_pow_left₀ hlt (norm_nonneg _) (by omega : k ≠ 0)
  exact absurd heq (ne_of_lt this)

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqEqOfPosCoeffEqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFormCoeffSeq_eq_of_pos_coeff_eq : ∀ (k L : ℕ) (χ : ℤ → ℂ) (a b : ℕ → ℂ), 1 ≤ k → 0 < L → MF k L χ a → MF k L χ b → (∀ n, n ≠ 0 → a n = b n) → a = b := by
  first | exact @GlobalTheory.EisM.eq_of_coeff_pos_eq | exact GlobalTheory.EisM.eq_of_coeff_pos_eq | (intros; apply GlobalTheory.EisM.eq_of_coeff_pos_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedQExpansionDouble
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedQExpansionDouble
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eis_norm_le (j : ℕ) (c : ℂ) (a b : ℤ → ℂ) (Ca Cb : ℝ) (ha : ∀ x, ‖a x‖ ≤ Ca)
    (hb : ∀ x, ‖b x‖ ≤ Cb) (n : ℕ) (hn : n ≠ 0) :
    ‖eis j c a b n‖ ≤ Ca * Cb * n.divisors.card * (n : ℝ) ^ (j - 1) := by
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans (ha 0)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hb 0)
  simp only [eis, if_neg hn]
  refine (norm_sum_le _ _).trans ?_
  have hcard : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  have key : ∀ p ∈ n.divisorsAntidiagonal,
      ‖a p.1 * (p.1 : ℂ) ^ (j - 1) * b p.2‖ ≤ Ca * Cb * (n : ℝ) ^ (j - 1) := by
    intro p hp
    have hle : p.1 ≤ n := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have h1 : (p.1 : ℝ) ^ (j - 1) ≤ (n : ℝ) ^ (j - 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) _
    calc ‖a p.1‖ * (p.1 : ℝ) ^ (j - 1) * ‖b p.2‖ ≤ Ca * (n : ℝ) ^ (j - 1) * Cb :=
          mul_le_mul (mul_le_mul (ha _) h1 (by positivity) hCa) (hb _) (norm_nonneg _) (by positivity)
      _ = Ca * Cb * (n : ℝ) ^ (j - 1) := by ring
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  ring

theorem eis_qseries : ∀ (j : ℕ) (c : ℂ) (a b : ℤ → ℂ), (∃ C : ℝ, ∀ x, ‖a x‖ ≤ C) → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) → PolyB (eis j c a b) ∧ (∃ C : ℝ, ∀ n, n ≠ 0 → ‖eis j c a b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (j - 1)) ∧ ∀ τ : ℍ, HasSum (fun y : ℕ => b (y + 1 : ℕ) * ∑' x : ℕ, ((x + 1 : ℕ) : ℂ) ^ (j - 1) * a (x + 1 : ℕ) * cexp (2 * π * Complex.I * (x + 1 : ℕ) * ((y + 1 : ℕ) * τ))) (qs (eis j c a b) τ - c) := by
  intro j c a b ⟨Ca, ha⟩ ⟨Cb, hb⟩
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans (ha 0)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hb 0)
  have hB := eis_norm_le j c a b Ca Cb ha hb
  refine ⟨?_, ⟨Ca * Cb, hB⟩, ?_⟩
  · refine ⟨max ‖c‖ (Ca * Cb), j + 1, fun n => ?_⟩
    rcases eq_or_ne n 0 with rfl | hn
    · simp [eis]
    · refine (hB n hn).trans ?_
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : (n.divisors.card : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.card_divisors_le_self n
        have : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast this
        linarith
      have h2 : (n : ℝ) ^ (j - 1) ≤ ((n : ℝ) + 1) ^ j :=
        (pow_le_pow_left₀ hn0 (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (Nat.sub_le j 1))
      have h3 : Ca * Cb ≤ max ‖c‖ (Ca * Cb) := le_max_right _ _
      have h4 : 0 ≤ Ca * Cb := mul_nonneg hCa hCb
      calc Ca * Cb * n.divisors.card * (n : ℝ) ^ (j - 1)
          ≤ max ‖c‖ (Ca * Cb) * ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ j := by
            apply mul_le_mul (mul_le_mul h3 h1 (by positivity) (by positivity)) h2 (by positivity) (by positivity)
        _ = max ‖c‖ (Ca * Cb) * ((n : ℝ) + 1) ^ (j + 1) := by ring
  · intro τ
    set q : ℂ := cexp (2 * π * Complex.I * τ) with hqdef
    have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
    have hE : ∀ m : ℕ, cexp (2 * π * Complex.I * m * τ) = q ^ m := fun m => by
      rw [hqdef, ← Complex.exp_nat_mul]; ring_nf
    have hE2 : ∀ m l : ℕ, cexp (2 * π * Complex.I * (m : ℂ) * ((l : ℂ) * τ)) = q ^ (m * l) := fun m l => by
      rw [hqdef, ← Complex.exp_nat_mul]; push_cast; ring_nf
    set H : ℕ+ × ℕ+ → ℂ := fun d => a ((d.1 : ℕ) : ℤ) * (((d.1 : ℕ) : ℂ)) ^ (j - 1) * b ((d.2 : ℕ) : ℤ) *
      q ^ ((d.1 : ℕ) * (d.2 : ℕ)) with hHdef
    have hHs : Summable H := by
      refine Summable.of_norm_bounded ((summable_prod_mul_pow (j - 1) hq).prod_symm.norm.mul_left (Ca * Cb)) fun d => ?_
      simp only [hHdef, norm_mul, norm_pow, Complex.norm_natCast, Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm ((d.2 : ℕ)) (d.1 : ℕ)]
      refine (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (ha _) (by positivity)) (hb _)
        (norm_nonneg _) (by positivity)) le_rfl (by positivity) (by positivity)).trans (le_of_eq ?_)
      ring
    have h2 := sigmaAntidiagonalEquivProd.hasSum_iff.2 hHs.hasSum
    have h3 : HasSum (fun n : ℕ+ => eis j c a b n * q ^ (n : ℕ)) (∑' d, H d) := by
      refine h2.sigma fun n => ?_
      refine (congrArg (HasSum _) ?_).mpr (hasSum_fintype _)
      simp only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe,
        Equiv.coe_fn_mk, Finset.univ_eq_attach, hHdef]
      rw [(n : ℕ).divisorsAntidiagonal.sum_attach (fun y : ℕ × ℕ => a (y.1 : ℤ) * ((y.1 : ℕ) : ℂ) ^ (j - 1) * b (y.2 : ℤ) * q ^ (y.1 * y.2))]
      simp only [eis, if_neg n.ne_zero, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Nat.mem_divisorsAntidiagonal.1 hp).1]
    have h4 : HasSum (fun n : ℕ => eis j c a b n * q ^ n) (c + ∑' d, H d) := by
      have h5 := (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ => eis j c a b n * q ^ n)).1 h3
      have h6 := HasSum.zero_add (f := fun n : ℕ => eis j c a b n * q ^ n) h5
      have h7 : eis j c a b 0 * q ^ 0 = c := by simp [eis]
      rw [h7] at h6
      exact h6
    have hqs : qs (eis j c a b) τ = c + ∑' d, H d := by
      unfold qs
      rw [← h4.tsum_eq]
      exact tsum_congr fun n => by rw [hE]
    rw [hqs, add_sub_cancel_left]
    let e : ℕ × ℕ ≃ ℕ+ × ℕ+ := (Equiv.prodComm ℕ ℕ).trans (Equiv.pnatEquivNat.symm.prodCongr Equiv.pnatEquivNat.symm)
    set F : ℕ × ℕ → ℂ := fun p => b (p.1 + 1 : ℕ) * (((p.2 + 1 : ℕ) : ℂ) ^ (j - 1) * a (p.2 + 1 : ℕ) *
      cexp (2 * π * Complex.I * (p.2 + 1 : ℕ) * ((p.1 + 1 : ℕ) * τ))) with hFdef
    have hFe : F = H ∘ e := by
      funext p
      simp only [hFdef, hHdef, Function.comp, e, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap,
        Prod.snd_swap, Equiv.prodCongr_apply, Prod.map, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Nat.succ_eq_add_one]
      rw [hE2, mul_comm (p.2 + 1) (p.1 + 1)]
      ring
    have hFs : Summable F := by rw [hFe]; exact e.summable_iff.2 hHs
    have hF : HasSum F (∑' d, H d) := by rw [hFe]; exact e.hasSum_iff.2 hHs.hasSum
    refine hF.prod_fiberwise fun y => ?_
    rw [← tsum_mul_left]
    exact (hFs.prod_factor y).hasSum

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedQExpansionDoubleStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffEisensteinSeriesTwisted_qExpansion_double : ∀ (j : ℕ) (c : ℂ) (a b : ℤ → ℂ), (∃ C : ℝ, ∀ x, ‖a x‖ ≤ C) → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) → PolyB (eis j c a b) ∧ (∃ C : ℝ, ∀ n, n ≠ 0 → ‖eis j c a b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (j - 1)) ∧ ∀ τ : ℍ, HasSum (fun y : ℕ => b (y + 1 : ℕ) * ∑' x : ℕ, ((x + 1 : ℕ) : ℂ) ^ (j - 1) * a (x + 1 : ℕ) * cexp (2 * π * Complex.I * (x + 1 : ℕ) * ((y + 1 : ℕ) * τ))) (qs (eis j c a b) τ - c) := by
  first | exact @GlobalTheory.EisM.eis_qseries | exact GlobalTheory.EisM.eis_qseries | (intros; apply GlobalTheory.EisM.eis_qseries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeULeftRepresentativesLevelChange
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeULeftRepresentativesLevelChange
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lrep_repU_of_dvd (M l : ℕ) (hl : l.Prime) (hlM : l ∣ M) :
    LRep M {δ : M2 | δ.det = l ∧ (M : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0} (repU l) := by
  have hlM' : (l : ℤ) ∣ (M : ℤ) := by exact_mod_cast hlM
  have hpZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have key : ∀ γ : SL(2, ℤ), (M : ℤ) ∣ (γ : M2) 1 0 → ¬ (l : ℤ) ∣ (γ : M2) 0 0 := by
    intro γ hc ha
    have hdet : (γ : M2).det = 1 := γ.2
    rw [Matrix.det_fin_two] at hdet
    have : (l : ℤ) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right (hlM'.trans hc) _)
    exact hpZ.not_dvd_one this
  have ent : ∀ (A : M2) (j : Fin l), (A * repU l j) 0 0 = A 0 0 ∧ (A * repU l j) 1 0 = A 1 0 ∧
      (A * repU l j) 0 1 = A 0 0 * (j : ℕ) + A 0 1 * l ∧
      (A * repU l j) 1 1 = A 1 0 * (j : ℕ) + A 1 1 * l := by
    intro A j
    simp [repU, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨γ, hγ⟩, j⟩ -
    have hc : (M : ℤ) ∣ (γ : M2) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨e1, e2, -, -⟩ := ent (γ : M2) j
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.det_mul, repU, Matrix.det_fin_two_of]
      rw [show (γ : M2).det = 1 from γ.2]
      simp
    · simpa [e2] using hc
    · simpa [e1] using key γ hc
  · rintro ⟨⟨γ, hγ⟩, j⟩ - ⟨⟨γ', hγ'⟩, j'⟩ - h
    simp only at h
    have hc : (M : ℤ) ∣ (γ : M2) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨e1, e2, e3, e4⟩ := ent (γ : M2) j
    obtain ⟨f1, f2, f3, f4⟩ := ent (γ' : M2) j'
    have h00 : (γ : M2) 0 0 = (γ' : M2) 0 0 := by rw [← e1, ← f1, h]
    have h10 : (γ : M2) 1 0 = (γ' : M2) 1 0 := by rw [← e2, ← f2, h]
    have h01 : (γ : M2) 0 0 * (j : ℕ) + (γ : M2) 0 1 * l = (γ' : M2) 0 0 * (j' : ℕ) + (γ' : M2) 0 1 * l := by
      rw [← e3, ← f3, h]
    have h11 : (γ : M2) 1 0 * (j : ℕ) + (γ : M2) 1 1 * l = (γ' : M2) 1 0 * (j' : ℕ) + (γ' : M2) 1 1 * l := by
      rw [← e4, ← f4, h]
    have hdiv : (l : ℤ) ∣ (γ : M2) 0 0 * (((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ)) :=
      ⟨(γ' : M2) 0 1 - (γ : M2) 0 1, by rw [h00] at h01 ⊢; linear_combination h01⟩
    have hd2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ) :=
      (hpZ.dvd_or_dvd hdiv).resolve_left (key γ hc)
    have hjj : j = j' := by
      have hj := j.2
      have hj' := j'.2
      obtain ⟨k, hk⟩ := hd2
      have hk0 : k = 0 := by
        rcases lt_trichotomy k 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      subst hk0
      ext
      omega
    subst hjj
    have g01 : (γ : M2) 0 1 = (γ' : M2) 0 1 := by
      apply mul_right_cancel₀ hl0; rw [h00] at h01; linarith
    have g11 : (γ : M2) 1 1 = (γ' : M2) 1 1 := by
      apply mul_right_cancel₀ hl0; rw [h10] at h11; linarith
    have : γ = γ' := by
      ext i k; fin_cases i <;> fin_cases k <;> simp [h00, h10, g01, g11]
    subst this
    rfl
  · rintro δ ⟨hdet, hc, ha⟩
    haveI : Fact l.Prime := ⟨hl⟩
    have hlc : (l : ℤ) ∣ δ 1 0 := hlM'.trans hc
    rw [Matrix.det_fin_two] at hdet
    have hld : (l : ℤ) ∣ δ 1 1 := by
      have : (l : ℤ) ∣ δ 0 0 * δ 1 1 := ⟨1 + (δ 0 1) * ((δ 1 0) / l), by
        obtain ⟨t, ht⟩ := hlc
        rw [ht, Int.mul_ediv_cancel_left _ hl0]
        linear_combination hdet + (δ 0 1) * ht⟩
      exact (hpZ.dvd_or_dvd this).resolve_left ha
    have haZ : ((δ 0 0 : ℤ) : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ha
    let j : Fin l := ⟨(((δ 0 1 : ℤ) : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹).val, ZMod.val_lt _⟩
    have hjZ : ((j : ℕ) : ZMod l) = ((δ 0 1 : ℤ) : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹ :=
      ZMod.natCast_zmod_val _
    have hb : (l : ℤ) ∣ δ 0 1 - δ 0 0 * (j : ℕ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hjZ]
      field_simp
      ring
    have hdd : (l : ℤ) ∣ δ 1 1 - δ 1 0 * (j : ℕ) := dvd_sub hld (dvd_mul_of_dvd_left hlc _)
    obtain ⟨e, he⟩ := hb
    obtain ⟨f, hf⟩ := hdd
    have hγdet : (!![δ 0 0, e; δ 1 0, f] : M2).det = 1 := by
      rw [Matrix.det_fin_two_of]
      apply mul_left_cancel₀ hl0
      linear_combination -(δ 0 0) * hf + (δ 1 0) * he + hdet
    let γ : SL(2, ℤ) := ⟨!![δ 0 0, e; δ 1 0, f], hγdet⟩
    have hγ : γ ∈ Gamma0 M := by
      rw [Gamma0_mem]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa [γ] using hc)
    refine ⟨(⟨γ, hγ⟩, j), Set.mem_univ _, ?_⟩
    obtain ⟨e1, e2, e3, e4⟩ := ent (γ : M2) j
    ext i k; fin_cases i <;> fin_cases k
    · simpa [γ] using e1
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e3 ⊢
      rw [e3]; simp [γ]; linarith
    · simpa [γ] using e2
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e4 ⊢
      rw [e4]; simp [γ]; linarith

theorem lrep_repU (L l : ℕ) (hl : l.Prime) :
    (l ∣ L → LRep L (DU L l) (repU l)) ∧
      (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) := by
  refine ⟨fun h => lrep_repU_of_dvd L l hl h, fun _ => ?_⟩
  have hs : {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} =
      {δ : M2 | δ.det = l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0} := by
    ext δ
    simp only [DU, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩; exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h4, h3⟩
      exact ⟨⟨h1, (Int.natCast_dvd_natCast.mpr (dvd_mul_right L l)).trans h4, h3⟩, h4⟩
  rw [hs]
  exact lrep_repU_of_dvd (L * l) l hl (dvd_mul_left l L)

theorem zrepU : ∀ L l : ℕ, l.Prime → (l ∣ L → LRep L (DU L l) (repU l)) ∧
    (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) :=
  fun L l hl => lrep_repU L l hl

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeULeftRepresentativesLevelChangeStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeU_leftRepresentatives_level_change : ∀ L l : ℕ, l.Prime → (l ∣ L → LRep L (DU L l) (repU l)) ∧ (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) := by
  first | exact @GlobalTheory.EisM.zrepU | exact GlobalTheory.EisM.zrepU | (intros; apply GlobalTheory.EisM.zrepU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIterated
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIterated
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

def ptXY (p : ℝ × ℝ) : ℍ := ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)

theorem measurable_ofComplex_hp : Measurable (ofComplex : ℂ → ℍ) := by
  classical
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have h : (UpperHalfPlane.coe ∘ (ofComplex : ℂ → ℍ)) =
      fun w : ℂ => if 0 < w.im then w else ((ofComplex 0 : ℍ) : ℂ) := by
    funext w
    by_cases hw : 0 < w.im
    · simp [hw, ofComplex_apply_of_im_pos hw]
    · simp only [Function.comp, hw, if_false]
      rw [ofComplex_apply_of_im_nonpos (not_lt.mp hw),
        ofComplex_apply_of_im_nonpos (le_refl _ : (0 : ℂ).im ≤ 0)]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id
    measurable_const

theorem ptXY_eq (p : ℝ × ℝ) : ptXY p = ofComplex (Complex.measurableEquivRealProd.symm p) := by
  unfold ptXY
  congr 1
  apply Complex.ext <;> simp

theorem measurable_ptXY : Measurable ptXY := by
  simp only [funext ptXY_eq]
  exact measurable_ofComplex_hp.comp Complex.measurableEquivRealProd.symm.measurable

theorem volume_eq_map_ptXY : (volume : Measure ℍ) = Measure.map ptXY
    (((volume : Measure ℝ).prod (volume.restrict (Set.Ioi 0))).withDensity
      fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  have hm := measurable_ptXY
  ext s hs
  have hp : (volume : Measure ℝ).prod (volume.restrict (Set.Ioi (0 : ℝ))) =
      (volume : Measure (ℝ × ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hset : ptXY ⁻¹' s ∩ Set.univ ×ˢ Set.Ioi 0 =
      Complex.measurableEquivRealProd.symm ⁻¹' (UpperHalfPlane.coe '' s) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ioi, Set.mem_image, ptXY_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by simpa using h2
      refine ⟨_, h1, ?_⟩
      rw [ofComplex_apply_of_im_pos h3]
    · rintro ⟨z, hz, hzp⟩
      refine ⟨?_, ?_⟩
      · rw [← hzp, ofComplex_apply]; exact hz
      · have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by
          rw [← hzp]; exact z.im_pos
        simpa using h3
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), hp, Measure.restrict_restrict (hm hs), hset,
    volume_eq_lintegral,
    ← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp

theorem measurableSet_strip : MeasurableSet strip := by
  have h : strip = (fun z : ℍ => z.re) ⁻¹' (Set.Ico 0 1) := rfl
  rw [h]
  exact UpperHalfPlane.continuous_re.measurable measurableSet_Ico

theorem ptXY_re (x y : ℝ) (hy : 0 < y) : (ptXY (x, y)).re = x := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ptXY, ofComplex_apply_of_im_pos h]
  simp [UpperHalfPlane.re]

theorem restrict_strip_eq_map : (volume : Measure ℍ).restrict strip = Measure.map ptXY
    ((((volume : Measure ℝ).restrict (Set.Ico 0 1)).prod (volume.restrict (Set.Ioi 0))).withDensity
      fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  have hm := measurable_ptXY
  have hS := hm measurableSet_strip
  have h1 : ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have h2 : ptXY ⁻¹' strip ∩ Set.univ ×ˢ Set.Ioi 0 = Set.Ico 0 1 ×ˢ Set.Ioi 0 := by
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ioi, Set.mem_Ico, strip, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [ptXY_re x y hy] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [ptXY_re x y hy]
      exact ⟨h, hy⟩
  rw [volume_eq_map_ptXY, Measure.restrict_map hm measurableSet_strip, restrict_withDensity hS, h1,
    Measure.restrict_restrict hS, h2, Measure.prod_restrict]

theorem strip_iterated :
    (∀ F : ℍ → ENNReal, Measurable F → ∫⁻ τ in strip, F τ = ∫⁻ y in Set.Ioi (0 : ℝ),
      (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) * ENNReal.ofReal (1 / y ^ 2)) ∧
    ∀ F : ℍ → ℂ, IntegrableOn F strip → ∫ τ in strip, F τ = ∫ y in Set.Ioi (0 : ℝ),
      (∫ x in (0 : ℝ)..1, F (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
  have hm := measurable_ptXY
  have hd : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) := by fun_prop
  refine ⟨fun F hF => ?_, fun H hH => ?_⟩
  · rw [restrict_strip_eq_map, lintegral_map hF hm, lintegral_withDensity_eq_lintegral_mul _ hd (g := fun a => F (ptXY a)) (hF.comp hm)]
    simp only [Pi.mul_apply]
    rw [lintegral_prod_symm (fun a => ENNReal.ofReal (1 / a.2 ^ 2) * F (ptXY a))
      ((hd.mul (hF.comp hm)).aemeasurable)]
    refine lintegral_congr fun y => ?_
    rw [lintegral_const_mul (ENNReal.ofReal (1 / y ^ 2)) (f := fun x : ℝ => F (ptXY (x, y)))
      (hF.comp (hm.comp (measurable_id.prodMk measurable_const))), mul_comm]
    rfl
  · unfold IntegrableOn at hH
    rw [restrict_strip_eq_map] at hH ⊢
    have hI := (integrable_map_measure hH.1 hm.aemeasurable).1 hH
    rw [integral_map hm.aemeasurable hH.1,
      integral_withDensity_eq_integral_toReal_smul hd (by simp)]
    rw [integrable_withDensity_iff_integrable_smul' hd (by simp)] at hI
    have key : ∀ y : ℝ, ∫ x in Set.Ico (0 : ℝ) 1, (ENNReal.ofReal (1 / y ^ 2)).toReal • (H ∘ ptXY) (x, y) =
        (∫ x in (0 : ℝ)..1, H (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
      intro y
      rw [integral_smul, ENNReal.toReal_ofReal (by positivity), intervalIntegral.integral_of_le zero_le_one,
        integral_Ico_eq_integral_Ioc, Complex.real_smul]
      simp only [Function.comp_apply, ptXY]
      push_cast
      ring
    refine (integral_prod_symm _ hI).trans ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => key y)

end GlobalTheory.EisM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIteratedStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitStrip_integral_eq_iterated : (∀ F : ℍ → ENNReal, Measurable F → ∫⁻ τ in strip, F τ = ∫⁻ y in Set.Ioi (0 : ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) * ENNReal.ofReal (1 / y ^ 2)) ∧ ∀ F : ℍ → ℂ, IntegrableOn F strip → ∫ τ in strip, F τ = ∫ y in Set.Ioi (0 : ℝ), (∫ x in (0 : ℝ)..1, F (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
  first | exact @GlobalTheory.EisM.strip_iterated | exact GlobalTheory.EisM.strip_iterated | (intros; apply GlobalTheory.EisM.strip_iterated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermiteRightFactorOfPrimeDvdDet
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermiteRightFactorOfPrimeDvdDet
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory

theorem hermite_right_factor_prime_det : ∀ (p : ℕ), p.Prime → ∀ (m : Matrix (Fin 2) (Fin 2) ℤ), (p : ℤ) ∣ m.det → (∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![(p : ℤ), 0; 0, 1]) ∨ ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
  intro p hp m hdet
  haveI := Fact.mk hp
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℤ, m = !![a, b; c, d] :=
    ⟨m 0 0, m 0 1, m 1 0, m 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  rw [Matrix.det_fin_two_of] at hdet
  have hdetZ : (a : ZMod p) * d = b * c := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a * d - b * c) p).2 hdet
    push_cast at this
    linear_combination this
  have fin : ∀ k : ℕ, k < p → (k : ZMod p) * a = b → (k : ZMod p) * c = d →
      ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, !![a, b; c, d] = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
    intro k hk h1 h2
    obtain ⟨u, hu⟩ : (p : ℤ) ∣ b - k * a := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h1]; ring
    obtain ⟨v, hv⟩ : (p : ℤ) ∣ d - k * c := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h2]; ring
    refine ⟨k, hk, !![a, u; c, v], ?_⟩
    rw [Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  by_cases ha : (a : ZMod p) = 0
  · by_cases hc : (c : ZMod p) = 0
    · left
      obtain ⟨a', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 ha
      obtain ⟨c', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).1 hc
      refine ⟨!![a', b; c', d], ?_⟩
      rw [Matrix.mul_fin_two]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
    · right
      refine fin ((d : ZMod p) * (c : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_
      · rw [ZMod.natCast_zmod_val]
        calc (d : ZMod p) * (c : ZMod p)⁻¹ * a = (a * d) * (c : ZMod p)⁻¹ := by ring
          _ = b * c * (c : ZMod p)⁻¹ := by rw [hdetZ]
          _ = b := by rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
      · rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · right
    refine fin ((b : ZMod p) * (a : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_
    · rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    · rw [ZMod.natCast_zmod_val]
      calc (b : ZMod p) * (a : ZMod p)⁻¹ * c = (b * c) * (a : ZMod p)⁻¹ := by ring
        _ = (a * d) * (a : ZMod p)⁻¹ := by rw [hdetZ]
        _ = d := by rw [mul_comm (a : ZMod p) d, mul_assoc, mul_inv_cancel₀ ha, mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermiteRightFactorOfPrimeDvdDetStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermite_right_factor_of_prime_dvd_det : ∀ (p : ℕ), p.Prime → ∀ (m : Matrix (Fin 2) (Fin 2) ℤ), (p : ℤ) ∣ m.det → (∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![(p : ℤ), 0; 0, 1]) ∨ ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
  first | exact @GlobalTheory.hermite_right_factor_prime_det | exact GlobalTheory.hermite_right_factor_prime_det | (intros; apply GlobalTheory.hermite_right_factor_prime_det <;> assumption)
end
end
