module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinNonconstantTermsHasSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesLatticeDifferentiableOn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesLatticeDifferentiableOn
open scoped nonZeroDivisors
open Metric Complex

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem eisTerm_at_zero_eq {F : Type} [Field F] [NumberField F] (k : ℕ) (z : Emb F → ℂ) (p : F × F) :
    eisTerm k 0 z p = (∏ τ, latPt z p τ)⁻¹ ^ k := by
  simp [eisTerm]

theorem norm_latPt_le_two_mul_of_near {F : Type} [Field F] [NumberField F] {z z₀ : Emb F → ℂ} {r : ℝ}
    (hr : ∀ τ, 2 * r ≤ (z₀ τ).im) (hz : ‖z - z₀‖ < r) (p : F × F) (τ : Emb F) :
    ‖latPt z₀ p τ‖ ≤ 2 * ‖latPt z p τ‖ := by
  have h1 : ‖z τ - z₀ τ‖ < r := lt_of_le_of_lt (norm_le_pi_norm (z - z₀) τ) hz
  have h2 : r ≤ (z τ).im := by
    have h3 := abs_im_le_norm (z τ - z₀ τ)
    rw [sub_im] at h3
    have h4 := (abs_le.1 (h3.trans h1.le)).1
    linarith [hr τ]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have e : latPt z₀ p τ = latPt z p τ + 2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ) := by
    simp only [latPt]; ring
  have hn : ∀ w : ℂ, ‖2 * (Real.pi : ℂ) * I * w‖ = 2 * Real.pi * ‖w‖ := by
    intro w
    rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    norm_num
  have hlow : 2 * Real.pi * (|τ p.2| * r) ≤ ‖latPt z p τ‖ := by
    rw [latPt, hn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ (abs_im_le_norm _)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add]
    rw [abs_mul, abs_of_pos (lt_of_lt_of_le (lt_of_le_of_lt (norm_nonneg _) hz) h2)]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hup : ‖2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ)‖ ≤ 2 * Real.pi * (|τ p.2| * r) := by
    rw [show 2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ) = 2 * (Real.pi : ℂ) * I * (((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ)) by ring, hn, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)) (by positivity)
  rw [e]
  linarith [norm_add_le (latPt z p τ) (2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ))]

theorem norm_eisTerm_zero_le_of_near {F : Type} [Field F] [NumberField F] {z z₀ : Emb F → ℂ} {r : ℝ}
    (hz₀ : z₀ ∈ upperHalf F) (hr : ∀ τ, 2 * r ≤ (z₀ τ).im) (hz : ‖z - z₀‖ < r) (k : ℕ) {p : F × F} (hp : p ≠ 0) :
    ‖eisTerm k 0 z p‖ ≤ (2 ^ Fintype.card (Emb F)) ^ k * ‖eisTerm k 0 z₀ p‖ := by
  rw [eisTerm_at_zero_eq, eisTerm_at_zero_eq, norm_pow, norm_pow, norm_inv, norm_inv, norm_prod, norm_prod, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  have hA : 0 < ∏ τ, ‖latPt z₀ p τ‖ :=
    Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz₀ hp τ)
  have hAB : ∏ τ, ‖latPt z₀ p τ‖ ≤ 2 ^ Fintype.card (Emb F) * ∏ τ, ‖latPt z p τ‖ := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun τ _ => norm_nonneg _) fun τ _ => norm_latPt_le_two_mul_of_near hr hz p τ
  have h2 : (0 : ℝ) < 2 ^ Fintype.card (Emb F) := by positivity
  have hB : 0 < ∏ τ, ‖latPt z p τ‖ := by
    by_contra h
    push_neg at h
    nlinarith
  rw [inv_le_comm₀ hB (by positivity), mul_inv, inv_inv]
  calc (2 ^ Fintype.card (Emb F))⁻¹ * ∏ τ, ‖latPt z₀ p τ‖ ≤ (2 ^ Fintype.card (Emb F))⁻¹ * (2 ^ Fintype.card (Emb F) * ∏ τ, ‖latPt z p τ‖) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
    _ = ∏ τ, ‖latPt z p τ‖ := by field_simp

theorem eisSum_zero_differentiableOn :
    ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F) (k : ℕ),
      (∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 k 0 z)) →
      DifferentiableOn ℂ (eisSum 𝔞 𝔟 k 0) (upperHalf F) := by
  intro F _ _ _ 𝔞 𝔟 k hs z₀ hz₀
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ ∀ τ, 2 * r ≤ (z₀ τ).im := by
    rcases isEmpty_or_nonempty (Emb F) with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · refine ⟨(Finset.univ.inf' Finset.univ_nonempty fun τ => (z₀ τ).im) / 2, ?_, fun τ => ?_⟩
      · exact half_pos ((Finset.lt_inf'_iff _).2 fun τ _ => hz₀ τ)
      · have := Finset.inf'_le (fun τ => (z₀ τ).im) (Finset.mem_univ τ)
        linarith
  have hsub : ball z₀ r ⊆ upperHalf F := by
    intro z hz τ
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : ‖z τ - z₀ τ‖ < r := lt_of_le_of_lt (norm_le_pi_norm (z - z₀) τ) hz
    have h3 := abs_im_le_norm (z τ - z₀ τ)
    rw [sub_im] at h3
    have h4 := (abs_le.1 (h3.trans h1.le)).1
    linarith [hr τ]
  have hdiff : ∀ c : Quotient (latRel 𝔞 𝔟), DifferentiableOn ℂ (fun z => eisClass 𝔞 𝔟 k 0 z c) (ball z₀ r) := by
    intro c z hz
    have hp : c.out.1 ≠ 0 := c.out.2.2.2
    have e : (fun z => eisClass 𝔞 𝔟 k 0 z c) = fun z => (∏ τ, latPt z c.out.1 τ)⁻¹ ^ k := by
      funext z; exact eisTerm_at_zero_eq k z c.out.1
    rw [e]
    have hP : Differentiable ℂ (fun z : Emb F → ℂ => ∏ τ, latPt z c.out.1 τ) := by
      unfold latPt; fun_prop
    have hne : ∏ τ, latPt z c.out.1 τ ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ => latPt_ne_zero (hsub hz) hp τ
    exact ((hP z).inv hne).pow k |>.differentiableWithinAt
  have hbd : ∀ c : Quotient (latRel 𝔞 𝔟), ∀ z ∈ ball z₀ r,
      ‖eisClass 𝔞 𝔟 k 0 z c‖ ≤ (2 ^ Fintype.card (Emb F)) ^ k * ‖eisClass 𝔞 𝔟 k 0 z₀ c‖ := by
    intro c z hz
    rw [mem_ball, dist_eq_norm] at hz
    exact norm_eisTerm_zero_le_of_near hz₀ hr hz k c.out.2.2.2
  have hsum : Summable fun c => (2 ^ Fintype.card (Emb F) : ℝ) ^ k * ‖eisClass 𝔞 𝔟 k 0 z₀ c‖ :=
    (summable_norm_iff.2 (hs z₀ hz₀)).mul_left _
  have h := GlobalTheory.differentiableOn_tsum_of_norm_le (Emb F → ℂ) (Quotient (latRel 𝔞 𝔟)) (ball z₀ r)
    (fun c z => eisClass 𝔞 𝔟 k 0 z c) _ isOpen_ball hdiff hsum hbd
  exact (h.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr0))).differentiableWithinAt

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesLatticeDifferentiableOnStatement
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ),
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  DifferentiableOn ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 k 0) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  first | exact @GlobalTheory.eisSum_zero_differentiableOn | exact GlobalTheory.eisSum_zero_differentiableOn | (intros; apply GlobalTheory.eisSum_zero_differentiableOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinConstantTermPartialZeta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinConstantTermPartialZeta
open scoped nonZeroDivisors
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory.EisConstTerm

theorem eisTerm_pair_zero (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℕ) (z : Emb F → ℂ) (a : F) :
    eisTerm (2 * s) 0 z (a, 0) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
      ((|((Algebra.norm ℚ a : ℚ) : ℝ)| : ℝ) : ℂ)⁻¹ ^ (2 * s) := by
  have hcard : Fintype.card (Emb F) = Module.finrank ℚ F := by
    rw [← NumberField.Embeddings.card F ℂ]
    refine Fintype.card_of_bijective (f := fun τ : Emb F => (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
    · intro τ τ' hτ
      ext y
      have := DFunLike.congr_fun hτ y
      simpa using this
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
      exact ⟨hr.embedding, by ext y; simp⟩
  have hprod : ∏ τ, latPt z (a, 0) τ = (2 * (Real.pi : ℂ) * Complex.I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
    rw [← prod_emb, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [latPt]
  unfold eisTerm
  rw [hprod, mul_zero, Complex.cpow_zero, mul_one, mul_inv, mul_pow, inv_pow ((2 * (Real.pi : ℂ) * Complex.I) ^ Module.finrank ℚ F), ← pow_mul, mul_comm (Module.finrank ℚ F)]
  congr 1
  rw [← Complex.ofReal_ratCast, inv_pow, inv_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, (even_two_mul s).pow_abs]

theorem spanSingleton_mul_le_one (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F) (ha : a ∈ latM 𝔞) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
      (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 := by
  set cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have h := FractionalIdeal.spanSingleton_le_iff_mem.2 ha
  calc _ ≤ latM 𝔞 * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by gcongr
    _ = (cD⁻¹ * cD) * (((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * 𝔞) := by rw [latM]; ring
    _ = 1 := by rw [inv_mul_cancel₀ hcD, Units.inv_mul, one_mul]

theorem mem_latM_of_le_one (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F)
    (ha : FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
      (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≤ 1) : a ∈ latM 𝔞 := by
  set cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  calc FractionalIdeal.spanSingleton (𝓞 F)⁰ a
      = FractionalIdeal.spanSingleton (𝓞 F)⁰ a * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * latM 𝔞 := by
        rw [latM, show ∀ X : FractionalIdeal (𝓞 F)⁰ F, X * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (cD⁻¹ * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)) =
          X * (cD * cD⁻¹) * ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)) from fun X => by ring,
          mul_inv_cancel₀ hcD, Units.mul_inv, mul_one, mul_one]
    _ ≤ 1 * latM 𝔞 := by gcongr
    _ = latM 𝔞 := one_mul _

theorem absNorm_of_spanSingleton (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F) (J : Ideal (𝓞 F))
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a *
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    (Ideal.absNorm J : ℝ) = |((Algebra.norm ℚ a : ℚ) : ℝ)| * (dF F * nrm 𝔞) := by
  have h := congrArg FractionalIdeal.absNorm hJ
  have e1 : FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) = Ideal.absNorm J := FractionalIdeal.coeIdeal_absNorm J
  have e2 : FractionalIdeal.absNorm ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = Ideal.absNorm (differentIdeal ℤ (𝓞 F)) :=
    FractionalIdeal.coeIdeal_absNorm _
  rw [e1, map_mul, map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 F), e2, absNorm_differentIdeal F (𝓞 F)] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_abs] at h'
  rw [h', dF, nrm, mul_assoc]
  congr 2
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem mk0_eq_of_spanSingleton (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (D : (Ideal (𝓞 F))⁰) (a : F) (ha : a ≠ 0)
    (J : (Ideal (𝓞 F))⁰) (hJ : ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ClassGroup.mk0 J = ClassGroup.mk0 D * ClassGroup.mk F 𝔞 := by
  have hu : FractionalIdeal.mk0 F J = toPrincipalIdeal (𝓞 F) F (Units.mk0 a ha) * FractionalIdeal.mk0 F D * 𝔞 := by
    apply Units.ext
    simp only [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, Units.val_mk0]
    exact hJ
  have hp : ClassGroup.mk F (toPrincipalIdeal (𝓞 F) F (Units.mk0 a ha)) = 1 :=
    ClassGroup.mk_eq_one_iff.2 ⟨⟨a, by rw [coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.coe_spanSingleton]⟩⟩
  rw [← ClassGroup.mk_mk0 F, hu, map_mul, map_mul, hp, one_mul, ClassGroup.mk_mk0]

theorem exists_spanSingleton_of_mk0_eq (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (D : (Ideal (𝓞 F))⁰)
    (J : (Ideal (𝓞 F))⁰) (hJ : ClassGroup.mk0 J = ClassGroup.mk0 D * ClassGroup.mk F 𝔞) :
    ∃ a : F, a ≠ 0 ∧ ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  set u := FractionalIdeal.mk0 F J * (FractionalIdeal.mk0 F D * 𝔞)⁻¹ with hu_def
  have h1 : ClassGroup.mk F u = 1 := by
    rw [hu_def, map_mul, map_inv, map_mul, ClassGroup.mk_mk0, ClassGroup.mk_mk0, hJ, mul_inv_cancel]
  obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.1 h1
  have hu : (u : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((u : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) = ((FractionalIdeal.spanSingleton (𝓞 F)⁰ x : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)
    rw [FractionalIdeal.coe_spanSingleton]
    exact hx
  have hx0 : x ≠ 0 := by
    intro h; apply Units.ne_zero u; rw [hu, h, FractionalIdeal.spanSingleton_zero]
  refine ⟨x, hx0, ?_⟩
  have e : FractionalIdeal.mk0 F J = u * (FractionalIdeal.mk0 F D * 𝔞) := by
    rw [hu_def, inv_mul_cancel_right]
  have e' := congrArg Units.val e
  simp only [Units.val_mul, FractionalIdeal.coe_mk0] at e'
  rw [e', hu, mul_assoc]

theorem hasSum_constTerm : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (s : ℕ), 1 ≤ s →
  ∀ (D : (Ideal (NumberField.RingOfIntegers F))⁰), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) →
  ∀ Z : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) Z →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 = 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 (2 * s) 0 z c)
      (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F * GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) * Z ((2 * s : ℕ) : ℂ)) := by
  intro F _ _ _ 𝔞 𝔟 s hs D hD Z hZ z hz
  classical
  set C := ClassGroup.mk0 D * ClassGroup.mk F 𝔞 with hC
  let S := {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 = 0}
  let T := {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C}
  let cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  let Jf : F → FractionalIdeal (𝓞 F)⁰ F := fun a => FractionalIdeal.spanSingleton (𝓞 F)⁰ a * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hX : cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := mul_ne_zero hcD (Units.ne_zero 𝔞)
  have hne : ∀ c : S, c.1.out.1.1 ≠ 0 := fun c h => c.1.out.2.2.2 (Prod.ext h c.2)
  have hle : ∀ c : S, Jf c.1.out.1.1 ≤ 1 := fun c => spanSingleton_mul_le_one F 𝔞 _ c.1.out.2.1
  let Jof : S → Ideal (𝓞 F) := fun c => Classical.choose (FractionalIdeal.le_one_iff_exists_coeIdeal.1 (hle c))
  have hJof : ∀ c : S, ((Jof c : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = Jf c.1.out.1.1 := fun c =>
    Classical.choose_spec (FractionalIdeal.le_one_iff_exists_coeIdeal.1 (hle c))
  have hJnz : ∀ c : S, Jof c ∈ (Ideal (𝓞 F))⁰ := by
    intro c
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    have := hJof c
    rw [h0, Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot] at this
    simp only [Jf, mul_assoc] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact hne c (FractionalIdeal.spanSingleton_eq_zero_iff.1 h)
    · exact hX h
  have hDc : ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = cD := by simp only [cD, hD]
  let f : S → T := fun c => ⟨⟨Jof c, hJnz c⟩, mk0_eq_of_spanSingleton F 𝔞 D _ (hne c) _ (by rw [hDc]; exact hJof c)⟩
  have hsp : ∀ (a : F) (ε : (𝓞 F)ˣ), FractionalIdeal.spanSingleton (𝓞 F)⁰ (((ε : 𝓞 F) : F) * a) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a := by
    intro a ε
    refine (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨ε, ?_⟩).symm
    rw [Units.smul_def, Algebra.smul_def]
  have hf : Function.Bijective f := by
    constructor
    · intro c c' h
      have h1 : Jof c = Jof c' := congrArg (fun J : T => (J.1 : Ideal (𝓞 F))) h
      have h2 : Jf c.1.out.1.1 = Jf c'.1.out.1.1 := by rw [← hJof, ← hJof, h1]
      have h3 : FractionalIdeal.spanSingleton (𝓞 F)⁰ c.1.out.1.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ c'.1.out.1.1 := by
        simp only [Jf, mul_assoc] at h2
        exact mul_right_cancel₀ hX h2
      obtain ⟨ε, hε⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h3
      apply Subtype.ext
      rw [← Quotient.out_eq c.1, ← Quotient.out_eq c'.1]
      apply Quotient.sound
      refine ⟨ε, ?_, ?_⟩
      · rw [← hε, Units.smul_def, Algebra.smul_def]
      · rw [c.2, c'.2, mul_zero]
    · rintro ⟨J, hJ⟩
      obtain ⟨a, ha, hJa⟩ := exists_spanSingleton_of_mk0_eq F 𝔞 D J hJ
      have hJle : Jf a ≤ 1 := by
        have h := FractionalIdeal.coeIdeal_le_one (I := (J : Ideal (𝓞 F))) (S := (𝓞 F)⁰) (P := F)
        rwa [hJa, hDc] at h
      let p : LatPair 𝔞 𝔟 := ⟨(a, 0), mem_latM_of_le_one F 𝔞 a hJle, Submodule.zero_mem _, fun h => ha (congrArg Prod.fst h)⟩
      obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r p (Quotient.mk (latRel 𝔞 𝔟) p).out := Quotient.exact (Quotient.out_eq _).symm
      have h2' : (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2 = 0 := by rw [h2]; simp [p]
      refine ⟨⟨Quotient.mk _ p, h2'⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show Jof _ = (J : Ideal (𝓞 F))
      refine FractionalIdeal.coeIdeal_injective (K := F) ?_
      show ((Jof _ : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
      rw [hJof, hJa, hDc]
      show Jf (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1 = Jf a
      rw [h1]
      simp only [Jf, hsp]
      rfl
  let e : S ≃ T := Equiv.ofBijective f hf
  have hZ2 := hZ.2 ((2 * s : ℕ) : ℂ) (by simp; norm_cast; omega)
  rw [← e.hasSum_iff] at hZ2
  have key : (fun c : S => eisClass 𝔞 𝔟 (2 * s) 0 z c.1) = fun c => (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((dF F * nrm 𝔞 : ℝ) : ℂ) ^ (2 * s)) * ((fun J : T => ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-((2 * s : ℕ) : ℂ))) ∘ e) c := by
    funext c
    have hN := absNorm_of_spanSingleton F 𝔞 c.1.out.1.1 (Jof c) (hJof c)
    simp only [Function.comp_apply, e, Equiv.ofBijective_apply, f]
    unfold eisClass
    rw [← Prod.mk.eta (p := c.1.out.1), c.2, eisTerm_pair_zero, Complex.cpow_neg, Complex.cpow_natCast]
    have hX0 : ((dF F * nrm 𝔞 : ℝ) : ℂ) ≠ 0 := by
      have h1 : dF F ≠ 0 := by
        unfold dF; rw [abs_ne_zero]; exact_mod_cast NumberField.discr_ne_zero F
      have h2 : nrm 𝔞 ≠ 0 := by
        unfold nrm; rw [Rat.cast_ne_zero, ne_eq, FractionalIdeal.absNorm_eq_zero_iff]; exact Units.ne_zero 𝔞
      exact_mod_cast mul_ne_zero h1 h2
    rw [← Complex.ofReal_natCast, hN, Complex.ofReal_mul (|_|)]
    have gen : ∀ (K y X : ℂ) (n : ℕ), X ≠ 0 → K * y⁻¹ ^ n = K * X ^ n * ((y * X) ^ n)⁻¹ := by
      intro K y X n hX
      rw [mul_pow, mul_inv, inv_pow, mul_assoc K, mul_comm ((y ^ n)⁻¹), ← mul_assoc (X ^ n), mul_inv_cancel₀ (pow_ne_zero _ hX), one_mul]
    exact gen _ _ _ _ hX0
  rw [key]
  exact hZ2.mul_left _

end GlobalTheory.EisConstTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinConstantTermPartialZetaStatement
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_hilbertEisenstein_constantTerm_partialZeta : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (s : ℕ), 1 ≤ s →
  ∀ (D : (Ideal (NumberField.RingOfIntegers F))⁰), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) →
  ∀ Z : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) Z →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 = 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 (2 * s) 0 z c)
      (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F * GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) * Z ((2 * s : ℕ) : ℂ)) := by
  first | exact @GlobalTheory.EisConstTerm.hasSum_constTerm | exact GlobalTheory.EisConstTerm.hasSum_constTerm | (intros; apply GlobalTheory.EisConstTerm.hasSum_constTerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaRealFunctionalEquationConstantEvenInteger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaRealFunctionalEquationConstantEvenInteger
namespace GlobalTheory

theorem gammaℝ_functional_constant_even :
    ∀ (d : ℝ), 0 < d → ∀ (f s : ℕ), 1 ≤ s → ∀ A B : ℂ,
      (d : ℂ) ^ (((2 * s : ℕ) : ℂ) / 2) * Complex.Gammaℝ ((2 * s : ℕ) : ℂ) ^ f * A =
        (d : ℂ) ^ ((1 - ((2 * s : ℕ) : ℂ)) / 2) * Complex.Gammaℝ (1 - ((2 * s : ℕ) : ℂ)) ^ f * B →
      (((2 * s - 1).factorial : ℕ) : ℂ) ^ f * ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) *
        ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f))⁻¹ * A = (2 : ℂ)⁻¹ ^ f * B := by
  intro d hd f s hs A B hAB
  set k : ℂ := ((2 * s : ℕ) : ℂ) with hk
  have hk' : k = 2 * (s : ℂ) := by rw [hk]; push_cast; ring
  have hh : Complex.Gammaℝ (1 - k) ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have h1 : ((1 : ℤ) : ℂ) = ((2 * s - 2 * n : ℤ) : ℂ) := by
      push_cast; rw [hk'] at hn; linear_combination hn
    have h2 := Int.cast_injective h1
    omega
  have hodd : ∀ n : ℕ, k ≠ -(2 * n + 1) := by
    intro n hn
    have h1 : ((2 * s : ℤ) : ℂ) = ((-(2 * n + 1) : ℤ) : ℂ) := by
      push_cast; rw [← hk']; exact hn
    have h2 := Int.cast_injective h1
    omega
  have hratio := Complex.Gammaℝ_div_Gammaℝ_one_sub hodd
  have hΓ : Complex.Gamma k = (((2 * s - 1).factorial : ℕ) : ℂ) := by
    have : k = ((2 * s - 1 : ℕ) : ℂ) + 1 := by
      rw [hk]; norm_cast; omega
    rw [this, Complex.Gamma_nat_eq_factorial]
  have hcos : Complex.cos ((Real.pi : ℂ) * k / 2) = (-1) ^ s := by
    rw [hk', show (Real.pi : ℂ) * (2 * s) / 2 = (s : ℂ) * Real.pi by ring]
    rw [show (s : ℂ) * Real.pi = (((s : ℝ) * Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
    push_cast; ring
  have hpow : (2 * (Real.pi : ℂ)) ^ (-k) = ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ := by
    rw [Complex.cpow_neg, hk, Complex.cpow_natCast]
  have hg : Complex.Gammaℝ k = Complex.Gammaℝ (1 - k) *
      (2 * ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ * (((2 * s - 1).factorial : ℕ) : ℂ) * (-1) ^ s) := by
    rw [div_eq_iff hh, Complex.Gammaℂ_def, hΓ, hcos, hpow] at hratio
    rw [hratio]; ring
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hE : ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) = (d : ℂ) ^ (k - 1 / 2) := by
    rw [Complex.ofReal_cpow hd.le]; congr 1; rw [hk]; push_cast; ring
  have hD : (d : ℂ) ^ (k / 2) = (d : ℂ) ^ ((1 - k) / 2) * (d : ℂ) ^ (k - 1 / 2) := by
    rw [← Complex.cpow_add _ _ hd0]; congr 1; ring
  have hD2 : (d : ℂ) ^ ((1 - k) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hB : B = (d : ℂ) ^ (k - 1 / 2) *
      (2 * ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ * (((2 * s - 1).factorial : ℕ) : ℂ) * (-1) ^ s) ^ f * A := by
    rw [hD, hg, mul_pow] at hAB
    have hne : (d : ℂ) ^ ((1 - k) / 2) * Complex.Gammaℝ (1 - k) ^ f ≠ 0 :=
      mul_ne_zero hD2 (pow_ne_zero _ hh)
    apply mul_left_cancel₀ hne
    rw [← hAB]; ring
  rw [hE, hB]
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f) =
      ((2 * (Real.pi : ℂ)) ^ (2 * s)) ^ f * ((-1 : ℂ) ^ s) ^ f := by
    rw [pow_mul, ← mul_pow, mul_pow (2 * (Real.pi : ℂ)) Complex.I, pow_mul Complex.I 2 s, Complex.I_sq]
  have hm : (((-1 : ℂ) ^ s) ^ f)⁻¹ = ((-1 : ℂ) ^ s) ^ f := by
    rw [← inv_pow, ← inv_pow, inv_neg_one]
  rw [hI, mul_inv, hm, ← inv_pow]
  have h2 : (2 : ℂ)⁻¹ ^ f * (2 : ℂ) ^ f = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  linear_combination (-((((2 * s - 1).factorial : ℕ) : ℂ) ^ f * (d : ℂ) ^ (k - 1 / 2) *
    (((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹) ^ f * ((-1 : ℂ) ^ s) ^ f * A)) * h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaRealFunctionalEquationConstantEvenIntegerStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaReal_functionalEquation_constant_even_integer : ∀ (d : ℝ), 0 < d → ∀ (f s : ℕ), 1 ≤ s → ∀ A B : ℂ,
  (d : ℂ) ^ (((2 * s : ℕ) : ℂ) / 2) * Complex.Gammaℝ ((2 * s : ℕ) : ℂ) ^ f * A =
    (d : ℂ) ^ ((1 - ((2 * s : ℕ) : ℂ)) / 2) * Complex.Gammaℝ (1 - ((2 * s : ℕ) : ℂ)) ^ f * B →
  (((2 * s - 1).factorial : ℕ) : ℂ) ^ f * ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) *
    ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f))⁻¹ * A = (2 : ℂ)⁻¹ ^ f * B := by
  first | exact @GlobalTheory.gammaℝ_functional_constant_even | exact GlobalTheory.gammaℝ_functional_constant_even | (intros; apply GlobalTheory.gammaℝ_functional_constant_even <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZeta
noncomputable section

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.LatVal GlobalTheory.LatJet
open scoped nonZeroDivisors

namespace GlobalTheory.HilbertEis

theorem eisClass_summable_of_hecke (hH : HeckeWeightTwo) {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (hf : 2 ≤ Module.finrank ℚ F) (𝔞 𝔟 : Frac F) {s : ℕ} (hs : 2 ≤ s) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) :
    Summable (eisClass 𝔞 𝔟 (2 * s) 0 z) := by
  obtain ⟨G, hG, -, -⟩ := hH F hf 𝔞 𝔟
  have hre : 0 < ((s : ℂ) - 1).re := by
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, sub_pos]
    exact_mod_cast (by omega : 1 < s)
  have h1 := (hG.1 ((s : ℂ) - 1) hre z hz).1
  have h2 : Summable fun c => ‖eisClass 𝔞 𝔟 2 ((s : ℂ) - 1) z c‖ := summable_norm_iff.mpr h1
  refine Summable.of_norm (h2.congr fun c => ?_)
  have hP : ∏ τ, latPt z c.out.1 τ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => latPt_ne_zero hz c.out.2.2.2 τ
  have hn : 0 < ‖∏ τ, latPt z c.out.1 τ‖ := norm_pos_iff.2 hP
  have hr : (-2 * ((s : ℂ) - 1)).re = -((2 * (s - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ s)]
    simp
  simp only [eisClass, eisTerm, norm_mul, norm_pow, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hn, hr,
    mul_zero, Complex.zero_re, Real.rpow_zero, mul_one, Real.rpow_neg hn.le, Real.rpow_natCast, ← inv_pow, ← pow_add]
  congr 1
  omega

theorem dF_pos (F : Type) [Field F] [NumberField F] : 0 < dF F :=
  abs_pos.2 (by exact_mod_cast discr_ne_zero F)

theorem nrm_pos {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) : 0 < nrm 𝔞 := by
  have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
  unfold nrm
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm

theorem const_eq (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (k : ℕ) :
    cK F k * (dF F * nrm 𝔞) ^ k / omegaFactor 𝔞 ^ k =
      ((k - 1).factorial : ℝ) ^ Module.finrank ℚ F * dF F ^ ((k : ℝ) - 1 / 2) := by
  have hd := dF_pos F
  have hn := nrm_pos 𝔞
  unfold cK omegaFactor
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (dF F ^ _), ← Real.rpow_mul hd.le, ← Real.rpow_natCast (dF F) k]
  have h1 : dF F ^ ((1 : ℝ) / 2 * k) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  have h2 : nrm 𝔞 ^ k ≠ 0 := pow_ne_zero _ hn.ne'
  field_simp
  rw [← Real.rpow_add hd, ← Real.rpow_add hd]
  congr 1
  ring

theorem eisExp : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz → HeckeWeightTwo → GlobalTheory.Published.PartialZetaFunctionalEquation → EisExp := by
  intro hL hH hP F _ _ _ hf 𝔞 𝔟 s hs
  rcases Nat.lt_or_ge s 2 with h1 | h2
  · obtain rfl : s = 1 := by omega
    obtain ⟨G, hG, hd, he⟩ := hH F hf 𝔞 𝔟
    exact ⟨G 0, ⟨fun h => absurd rfl h, fun _ => ⟨G, hG, rfl⟩⟩, hd, he⟩
  have hsum : ∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 (2 * s) 0 z) := fun z hz =>
    eisClass_summable_of_hecke hH hf 𝔞 𝔟 h2 hz
  refine ⟨eisSum 𝔞 𝔟 (2 * s) 0, ⟨fun _ z hz => (hsum z hz).hasSum, fun h => by omega⟩,
    GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn F 𝔞 𝔟 _ hsum, ?_⟩
  let D : (Ideal (𝓞 F))⁰ := ⟨differentIdeal ℤ (𝓞 F), mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ))⟩
  obtain ⟨Z, Z', hZ, hZ', hfe⟩ := hP F (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) (ClassGroup.mk F 𝔞)⁻¹ D rfl
    (by rw [mul_assoc, mul_inv_cancel, mul_one])
  refine ⟨Z', hZ', fun z hz => ?_⟩
  obtain ⟨hq, h3⟩ := GlobalTheory.T.hilbertEisenstein_nonconstant_terms_hasSum F hL 𝔞 𝔟 (2 * s) (by omega) (even_two_mul s) hsum z hz
  have h0 := GlobalTheory.T.hasSum_hilbertEisenstein_constantTerm_partialZeta F 𝔞 𝔟 s (by omega) D rfl Z hZ z hz
  have hfe' := hfe ((2 * s : ℕ) : ℂ) (fun n h => by
      have h' : ((2 * s : ℕ) : ℤ) = -2 * n := by exact_mod_cast h
      omega) (fun n h => by
      have h' : (1 - ((2 * s : ℕ) : ℤ)) = -2 * n := by exact_mod_cast h
      omega)
  have hc := GlobalTheory.T.gammaReal_functionalEquation_constant_even_integer (dF F) (dF_pos F) (Module.finrank ℚ F) s (by omega) _ _ hfe'
  refine ⟨hq, ?_⟩
  have hG := (HasSum.add_compl (f := eisClass 𝔞 𝔟 (2 * s) 0 z) (s := {c : Quotient (latRel 𝔞 𝔟) | c.out.1.2 = 0}) h0 h3).tsum_eq
  rw [show eisSum 𝔞 𝔟 (2 * s) 0 z = ∑' c, eisClass 𝔞 𝔟 (2 * s) 0 z c from rfl, hG]
  have hk := const_eq F 𝔞 (2 * s)
  have hω : (omegaFactor 𝔞 : ℂ) ≠ 0 := by
    unfold omegaFactor
    exact_mod_cast (mul_pos (Real.rpow_pos_of_pos (dF_pos F) _) (nrm_pos 𝔞)).ne'
  have hcK : (cK F (2 * s) : ℂ) ≠ 0 := by
    have : 0 < cK F (2 * s) := by
      unfold cK
      exact mul_pos (pow_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) _) (Real.rpow_pos_of_pos (dF_pos F) _)
    exact_mod_cast this.ne'
  have hk' : (cK F (2 * s) : ℂ) * ((dF F * nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) / (omegaFactor 𝔞 : ℂ) ^ (2 * s) =
      (((2 * s - 1).factorial : ℕ) : ℂ) ^ Module.finrank ℚ F * ((dF F ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) := by
    exact_mod_cast hk
  rw [← hc, ← hk']
  field_simp

end GlobalTheory.HilbertEis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZetaStatement
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.Published.PartialZetaFunctionalEquation → EisExp := by
  first | exact @GlobalTheory.HilbertEis.eisExp | exact GlobalTheory.HilbertEis.eisExp | (intros; apply GlobalTheory.HilbertEis.eisExp <;> assumption)
end
