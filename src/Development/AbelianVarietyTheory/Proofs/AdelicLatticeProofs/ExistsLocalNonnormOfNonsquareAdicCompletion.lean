module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvenOrderNormsOneAddFourMulOfNoRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvenOrderNormsOneAddFourMulOfNoRoot
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private lemma exists_exp_two_mul_of_eq_sq {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {u y : K}
    (hy : y ≠ 0) (h : w u = w (y ^ 2)) : ∃ n : ℤ, w u = WithZero.exp (2 * n) := by
  refine ⟨WithZero.log (w y), ?_⟩
  rw [h, map_pow, two_mul, WithZero.exp_add, WithZero.exp_log ((Valuation.ne_zero_iff w).mpr hy),
    sq]

theorem _root_.GlobalTheory.QNorm.evenNorms_one_add_four_mul :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (ρ : K), (2 : K) ≠ 0 → w ρ ≤ 1 →
      (∀ x : K, w x ≤ 1 → w (x ^ 2 + x - ρ) = 1) →
        _root_.GlobalTheory.QNorm.EvenNorms w (1 + 4 * ρ) := by
  intro K _ w ρ h2 hρ hroot a b hab
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := hab.resolve_right (not_not.mpr rfl)
    exact exists_exp_two_mul_of_eq_sq w ha (by congr 1; ring)
  · set t := (a - b) / (2 * b) with ht_def
    have hfac : a ^ 2 - (1 + 4 * ρ) * b ^ 2 = (2 * b) ^ 2 * (t ^ 2 + t - ρ) := by
      rw [ht_def]
      field_simp
      ring
    by_cases ht : w t ≤ 1
    · exact exists_exp_two_mul_of_eq_sq w (mul_ne_zero h2 hb)
        (by rw [hfac, map_mul, hroot t ht, mul_one])
    · push_neg at ht
      have ht0 : t ≠ 0 := by
        rintro h
        rw [h, map_zero] at ht
        exact not_lt_of_ge zero_le' ht
      have hlt : w (t - ρ) < w (t ^ 2) := by
        calc w (t - ρ) ≤ max (w t) (w ρ) := Valuation.map_sub w t ρ
          _ = w t := max_eq_left (hρ.trans ht.le)
          _ < w t * w t := lt_mul_self ht
          _ = w (t ^ 2) := by rw [map_pow, sq]
      have hval : w (t ^ 2 + t - ρ) = w (t ^ 2) := by
        rw [add_sub_assoc]
        exact Valuation.map_add_eq_of_lt_left w hlt
      refine exists_exp_two_mul_of_eq_sq w (y := 2 * b * t) (mul_ne_zero (mul_ne_zero h2 hb) ht0) ?_
      rw [hfac, map_mul, hval, ← map_mul]
      congr 1
      ring

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvenOrderNormsOneAddFourMulOfNoRootStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (ρ : K), (2 : K) ≠ 0 → w ρ ≤ 1 → (∀ x : K, w x ≤ 1 → w (x ^ 2 + x - ρ) = 1) → EvenNorms w (1 + 4 * ρ) := by
  first | exact @GlobalTheory.QNorm.evenNorms_one_add_four_mul | exact GlobalTheory.QNorm.evenNorms_one_add_four_mul | (intros; apply GlobalTheory.QNorm.evenNorms_one_add_four_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormalFormNonsquareAdicCompletion
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

namespace Defect

variable {K : Type} [Field K] (w : Valuation K ℤᵐ⁰)

theorem exists_exp {x : K} (hx : x ≠ 0) : ∃ n : ℤ, w x = WithZero.exp n :=
  ⟨WithZero.log (w x), (WithZero.exp_log ((Valuation.ne_zero_iff w).2 hx)).symm⟩

theorem map_two_le : w 2 ≤ 1 := by
  rw [← one_add_one_eq_two]
  exact w.map_add_le (by simp) (by simp)

theorem map_four_le : w 4 ≤ 1 := by
  have : (4 : K) = 2 + 2 := by norm_num
  rw [this]
  exact w.map_add_le (map_two_le w) (map_two_le w)

theorem evenNorms_of_le_four (h2 : (2 : K) ≠ 0)
    (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x) (δ : K) (hδ : w δ = 1) (hns : ¬ IsSquare δ)
    (h : w (δ - 1) ≤ w 4) : EvenNorms w δ := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hw4 : 0 < w 4 := zero_lt_iff.2 ((Valuation.ne_zero_iff w).2 h4)
  set ρ : K := (δ - 1) / 4 with hρ
  have hδρ : δ = 1 + 4 * ρ := by rw [hρ]; field_simp; ring
  have hρ1 : w ρ ≤ 1 := by rw [hρ, map_div₀]; exact div_le_one_of_le₀ h zero_le'
  rw [hδρ]
  refine GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root K w ρ h2 hρ1 fun x hx => ?_
  have hle : w (x ^ 2 + x - ρ) ≤ 1 := by
    refine w.map_sub_le (w.map_add_le ?_ hx) hρ1
    rw [map_pow]; exact pow_le_one₀ zero_le' hx
  refine le_antisymm hle (not_lt.1 fun hlt => hns ?_)
  have e1 : δ - (1 + 2 * x) ^ 2 = -(4 * (x ^ 2 + x - ρ)) := by rw [hδρ]; ring
  have l1 : w (δ - (1 + 2 * x) ^ 2) < w 4 := by
    rw [e1, Valuation.map_neg, map_mul]
    exact mul_lt_of_lt_one_right hw4 hlt
  have l2 : w ((1 + 2 * x) ^ 2) = 1 := by
    rw [← hδ]
    refine w.map_eq_of_sub_lt ?_
    rw [Valuation.map_sub_swap, hδ]
    exact l1.trans_le (map_four_le w)
  have hy : (1 + 2 * x) ^ 2 ≠ 0 := by
    intro h0; rw [h0] at l2; simp at l2
  have hs : IsSquare (δ / (1 + 2 * x) ^ 2) := by
    refine hsq _ ?_
    rw [div_sub_one hy, map_div₀, l2, div_one]; exact l1
  have : δ = δ / (1 + 2 * x) ^ 2 * (1 + 2 * x) ^ 2 := (div_mul_cancel₀ _ hy).symm
  rw [this]
  exact hs.mul (IsSquare.sq _)

end Defect

private theorem evenNorms_of_valuation_sub_one_le_four (F : Type) [Field F]
    [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : v.adicCompletion F)
    (he : Valued.v e = 1) (hns : ¬ IsSquare e)
    (hle : Valued.v (e - 1) ≤ Valued.v (4 : v.adicCompletion F)) :
    _root_.GlobalTheory.QNorm.EvenNorms Valued.v e := by
  have h4 : (4 : v.adicCompletion F) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 4]
    exact (map_ne_zero _).mpr (by norm_num)
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2]
    exact (map_ne_zero _).mpr (by norm_num)
  have hw4 : 0 < Valued.v (4 : v.adicCompletion F) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h4)
  have hw4le : Valued.v (4 : v.adicCompletion F) ≤ 1 := by
    rw [show (4 : v.adicCompletion F) = 1 + 1 + 1 + 1 by norm_num]
    exact Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _
      (Valuation.map_one _).le (Valuation.map_one _).le) (Valuation.map_one _).le) (Valuation.map_one _).le
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : v.adicCompletion F, ρ = (e - 1) / 4 := ⟨_, rfl⟩
  have heρ : e = 1 + 4 * ρ := by rw [hρ_def]; field_simp; ring
  have hρ : Valued.v ρ ≤ 1 := by
    rw [hρ_def, map_div₀]
    exact div_le_one_of_le₀ hle zero_le'
  rw [heρ]
  refine _root_.GlobalTheory.QNorm.evenNorms_one_add_four_mul _ Valued.v ρ h2 hρ ?_
  intro x hx
  have hint : Valued.v (x ^ 2 + x - ρ) ≤ 1 :=
    Valuation.map_sub_le _ (Valuation.map_add_le _ (by rw [map_pow]; exact pow_le_one₀ zero_le' hx) hx) hρ
  refine le_antisymm hint ?_
  by_contra hlt
  push_neg at hlt
  apply hns
  obtain ⟨s, hs_def⟩ : ∃ s : v.adicCompletion F, s = 1 + 2 * x := ⟨_, rfl⟩
  have hdiff : e - s ^ 2 = -(4 * (x ^ 2 + x - ρ)) := by rw [heρ, hs_def]; ring
  have hdiff_lt : Valued.v (e - s ^ 2) < Valued.v (4 : v.adicCompletion F) := by
    rw [hdiff, Valuation.map_neg, map_mul]
    exact mul_lt_of_lt_one_right hw4 hlt
  have hs2 : Valued.v (s ^ 2) = 1 := by
    rw [show s ^ 2 = e - (e - s ^ 2) by ring,
      Valuation.map_sub_eq_of_lt_left _ (by rw [he]; exact lt_of_lt_of_le hdiff_lt hw4le), he]
  have hs : Valued.v s = 1 := by rw [map_pow] at hs2; exact sq_eq_one.mp hs2
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v (e * s⁻¹ ^ 2) (by
    rw [show e * s⁻¹ ^ 2 - 1 = (e - s ^ 2) * s⁻¹ ^ 2 by field_simp, map_mul, map_pow, map_inv₀,
      hs, inv_one, one_pow, mul_one]
    exact hdiff_lt)
  refine ⟨r * s, ?_⟩
  have : e = (e * s⁻¹ ^ 2) * s ^ 2 := by field_simp
  rw [this, hr]; ring

private theorem exists_normalForm_nonsquare_unit_lemma (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (π : v.adicCompletion F) (hπ : Valued.v π = WithZero.exp (-1))
    (hsq : Valued.v (2 : v.adicCompletion F) < 1 → ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
      ∃ y : v.adicCompletion F, Valued.v y ≤ 1 ∧ Valued.v (x - y ^ 2) < 1)
    (a : ℤ) (ha : Valued.v (4 : v.adicCompletion F) = WithZero.exp a) (n : ℕ) :
    ∀ e : v.adicCompletion F, Valued.v e = 1 → ¬ IsSquare e → ∀ j : ℤ,
      Valued.v (e - 1) = WithZero.exp j → j ≤ a + n →
      ∃ c : v.adicCompletion F, c ≠ 0 ∧ ((Valued.v (e * c ^ 2) = 1 ∧
        Valued.v (4 : v.adicCompletion F) < Valued.v (e * c ^ 2 - 1) ∧
        ∃ m : ℤ, Valued.v (e * c ^ 2 - 1) = WithZero.exp (2 * m + 1)) ∨
        _root_.GlobalTheory.QNorm.EvenNorms Valued.v (e * c ^ 2)) := by
  induction n with
  | zero =>
    intro e he hns j hj hja
    refine ⟨1, one_ne_zero, Or.inr ?_⟩
    rw [one_pow, mul_one]
    refine evenNorms_of_valuation_sub_one_le_four F v e he hns ?_
    rw [hj, ha, WithZero.exp_le_exp]
    simpa using hja
  | succ n ih =>
    intro e he hns j hj hja
    by_cases hle : j ≤ a + n
    · exact ih e he hns j hj hle
    have h4lt : Valued.v (4 : v.adicCompletion F) < Valued.v (e - 1) := by
      rw [ha, hj, WithZero.exp_lt_exp]; omega
    have he1 : Valued.v (e - 1) ≤ 1 :=
      Valuation.map_sub_le _ he.le (Valuation.map_one _).le
    rcases Int.even_or_odd j with ⟨i, hi⟩ | ⟨m, hm⟩
    · have hj0 : j ≤ 0 := by
        rw [hj, ← WithZero.exp_zero, WithZero.exp_le_exp] at he1; exact he1
      have h2 : Valued.v (2 : v.adicCompletion F) < 1 := by
        by_contra hge
        push_neg at hge
        have : 1 ≤ Valued.v (4 : v.adicCompletion F) := by
          rw [show (4 : v.adicCompletion F) = 2 ^ 2 by norm_num, map_pow]
          exact one_le_pow₀ hge
        exact absurd (lt_of_lt_of_le h4lt he1) (not_lt.mpr this)
      obtain ⟨c, hc, hlt⟩ := _root_.GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt _ Valued.v e π (-i).toNat hπ
        (hsq h2) he h4lt (by rw [hj]; congr 1; omega)
      have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      have he' : Valued.v (e * c ^ 2) = 1 := by rw [map_mul, map_pow, he, hc, one_pow, mul_one]
      have hns' : ¬ IsSquare (e * c ^ 2) := by
        rintro ⟨r, hr⟩
        apply hns
        refine ⟨r / c, ?_⟩
        have : e = (e * c ^ 2) / c ^ 2 := by field_simp
        rw [this, hr]; ring
      have hne : e * c ^ 2 - 1 ≠ 0 := by
        intro h
        apply hns'
        exact ⟨1, by rw [sub_eq_zero] at h; rw [h, mul_one]⟩
      have hv0 : Valued.v (e * c ^ 2 - 1) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
      obtain ⟨j', hj'⟩ : ∃ j' : ℤ, Valued.v (e * c ^ 2 - 1) = WithZero.exp j' :=
        ⟨WithZero.log _, (WithZero.exp_log hv0).symm⟩
      have hj'lt : j' < j := by rw [hj', hj, WithZero.exp_lt_exp] at hlt; exact hlt
      obtain ⟨c', hc'0, hc'⟩ := ih (e * c ^ 2) he' hns' j' hj' (by push_cast at hja; omega)
      refine ⟨c * c', mul_ne_zero hc0 hc'0, ?_⟩
      rw [show e * (c * c') ^ 2 = e * c ^ 2 * c' ^ 2 by ring]
      exact hc'
    · refine ⟨1, one_ne_zero, Or.inl ⟨by rw [one_pow, mul_one, he], by rwa [one_pow, mul_one],
        m, by rw [one_pow, mul_one, hj, hm]⟩⟩

private theorem exists_sq_near_of_valuation_two_lt_one {K : Type} [Field K] (w : Valuation K ℤᵐ⁰)
    (R : Finset K) (hR : ∀ r ∈ R, w r ≤ 1) (hcov : ∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1)
    (h2 : w 2 < 1) (x : K) (hx : w x ≤ 1) : ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1 := by
  let S : Setoid {a : K // w a ≤ 1} :=
    { r := fun a b => w (a.1 - b.1) < 1
      iseqv :=
        { refl := fun a => by simp
          symm := fun {a b} h => by rwa [← Valuation.map_neg, neg_sub]
          trans := fun {a b c} hab hbc => by
            have : a.1 - c.1 = (a.1 - b.1) + (b.1 - c.1) := by ring
            rw [this]; exact Valuation.map_add_lt w hab hbc } }
  let sq : {a : K // w a ≤ 1} → {a : K // w a ≤ 1} :=
    fun a => ⟨a.1 ^ 2, by rw [map_pow]; exact pow_le_one₀ zero_le' a.2⟩
  have hsq : ∀ a b, S.r a b → S.r (sq a) (sq b) := by
    intro a b hab
    show w (a.1 ^ 2 - b.1 ^ 2) < 1
    rw [show a.1 ^ 2 - b.1 ^ 2 = (a.1 - b.1) * (a.1 + b.1) by ring, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le' (Valuation.map_add_le w a.2 b.2)) hab
  let g : Quotient S → Quotient S := Quotient.map sq hsq
  have hfin : Finite (Quotient S) := by
    refine Finite.of_surjective (fun r : R => Quotient.mk S ⟨r.1, hR r.1 r.2⟩) ?_
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      obtain ⟨r, hr, har⟩ := hcov a.1 a.2
      exact ⟨⟨r, hr⟩, Quotient.sound (by
        show w (r - a.1) < 1
        rwa [← Valuation.map_neg, neg_sub])⟩
  have hinj : Function.Injective g := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | h a =>
    induction q using Quotient.inductionOn with
    | h b =>
    have hab : w (a.1 ^ 2 - b.1 ^ 2) < 1 := Quotient.exact hpq
    apply Quotient.sound
    show w (a.1 - b.1) < 1
    have hsq2 : w ((a.1 - b.1) ^ 2) < 1 := by
      rw [show (a.1 - b.1) ^ 2 = (a.1 ^ 2 - b.1 ^ 2) + -(2 * b.1 * (a.1 - b.1)) by ring]
      refine Valuation.map_add_lt w hab ?_
      rw [Valuation.map_neg, map_mul, map_mul]
      refine lt_of_le_of_lt ?_ h2
      rw [mul_assoc]
      exact mul_le_of_le_one_right zero_le'
        (mul_le_one' b.2 (Valuation.map_sub_le w a.2 b.2))
    by_contra hge
    push_neg at hge
    rw [map_pow] at hsq2
    exact absurd hsq2 (not_lt.mpr (one_le_pow₀ hge))
  have hsurj : Function.Surjective g := Finite.injective_iff_surjective.mp hinj
  obtain ⟨q, hq⟩ := hsurj (Quotient.mk S ⟨x, hx⟩)
  induction q using Quotient.inductionOn with
  | h y =>
  have hyx : w (y.1 ^ 2 - x) < 1 := Quotient.exact hq
  exact ⟨y.1, y.2, by rwa [← Valuation.map_neg, neg_sub]⟩

theorem _root_.GlobalTheory.QNorm.exists_normal_form_of_not_isSquare : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ : v.adicCompletion F), δ ≠ 0 → ¬ IsSquare δ → ∃ c : v.adicCompletion F, c ≠ 0 ∧ ((∃ n : ℤ, Valued.v (δ * c ^ 2) = WithZero.exp (2 * n + 1)) ∨ (Valued.v (δ * c ^ 2) = 1 ∧ Valued.v (4 : v.adicCompletion F) < Valued.v (δ * c ^ 2 - 1) ∧ ∃ n : ℤ, Valued.v (δ * c ^ 2 - 1) = WithZero.exp (2 * n + 1)) ∨ _root_.GlobalTheory.QNorm.EvenNorms Valued.v (δ * c ^ 2)) := by
  intro F _ _ v δ hδ0 hδsq
  obtain ⟨⟨π₀, -, hπ⟩, -, -, R, -, hR, hcov⟩ := _root_.GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v
  obtain ⟨π, hπ_def⟩ : ∃ π : v.adicCompletion F, π = algebraMap F (v.adicCompletion F) π₀ :=
    ⟨_, rfl⟩
  rw [← hπ_def] at hπ
  have hπ0 : π ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hπ]; exact WithZero.exp_ne_zero)
  have hvδ : Valued.v δ ≠ 0 := (Valuation.ne_zero_iff _).mpr hδ0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v δ = WithZero.exp m := ⟨_, (WithZero.exp_log hvδ).symm⟩
  rcases Int.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
  · obtain ⟨c₀, hc₀_def⟩ : ∃ c₀ : v.adicCompletion F, c₀ = π ^ n := ⟨_, rfl⟩
    have hc₀0 : c₀ ≠ 0 := by rw [hc₀_def]; exact zpow_ne_zero _ hπ0
    have hvc₀ : Valued.v c₀ = WithZero.exp (-n) := by
      rw [hc₀_def, map_zpow₀, hπ, ← WithZero.exp_zsmul, zsmul_eq_mul]; congr 1; simp
    obtain ⟨e, he_def⟩ : ∃ e : v.adicCompletion F, e = δ * c₀ ^ 2 := ⟨_, rfl⟩
    have he : Valued.v e = 1 := by
      rw [he_def, map_mul, map_pow, hm, hvc₀, ← WithZero.exp_nsmul, ← WithZero.exp_add,
        ← WithZero.exp_zero]
      congr 1; rw [hn]; simp; ring
    have hns : ¬ IsSquare e := by
      rintro ⟨r, hr⟩
      apply hδsq
      refine ⟨r / c₀, ?_⟩
      have : δ = e / c₀ ^ 2 := by rw [he_def]; field_simp
      rw [this, hr]; ring
    have h4 : (4 : v.adicCompletion F) ≠ 0 := by
      rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 4]
      exact (map_ne_zero _).mpr (by norm_num)
    have hv4 : Valued.v (4 : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr h4
    have he1 : e - 1 ≠ 0 := by
      intro h
      apply hns
      exact ⟨1, by rw [sub_eq_zero] at h; rw [h, mul_one]⟩
    have hve1 : Valued.v (e - 1) ≠ 0 := (Valuation.ne_zero_iff _).mpr he1
    obtain ⟨c, hc0, hc⟩ := exists_normalForm_nonsquare_unit_lemma F v π hπ
      (fun h2 => exists_sq_near_of_valuation_two_lt_one Valued.v R hR hcov h2)
      (WithZero.log (Valued.v (4 : v.adicCompletion F))) (WithZero.exp_log hv4).symm
      (WithZero.log (Valued.v (e - 1)) - WithZero.log (Valued.v (4 : v.adicCompletion F))).toNat
      e he hns (WithZero.log (Valued.v (e - 1))) (WithZero.exp_log hve1).symm (by omega)
    refine ⟨c₀ * c, mul_ne_zero hc₀0 hc0, Or.inr ?_⟩
    rw [show δ * (c₀ * c) ^ 2 = e * c ^ 2 by rw [he_def]; ring]
    exact hc
  · exact ⟨1, one_ne_zero, Or.inl ⟨n, by rw [one_pow, mul_one, hm, hn]⟩⟩

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitEvenOrderQuadraticNormValuesOneModFour
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_not_mem_sq_add_sub (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ρ : 𝓞 F, ∀ a : 𝓞 F, a ^ 2 + a - ρ ∉ v.asIdeal := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  let f : 𝓞 F ⧸ v.asIdeal → 𝓞 F ⧸ v.asIdeal := fun x => x ^ 2 + x
  have hni : ¬ Function.Injective f := by
    intro h
    have h0 : (0 : 𝓞 F ⧸ v.asIdeal) = -1 := h (by simp [f])
    exact one_ne_zero (neg_eq_zero.mp h0.symm)
  have hns : ¬ Function.Surjective f := fun hs => hni (Finite.injective_iff_surjective.mpr hs)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨r, hr⟩ := hns
  obtain ⟨ρ, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨ρ, fun a ha => hr (Ideal.Quotient.mk _ a) ?_⟩
  have h := (Ideal.Quotient.eq_zero_iff_mem).mpr ha
  simp only [map_sub, map_add (f := _), map_pow] at h
  exact sub_eq_zero.mp h

theorem exists_evenNorms_unit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), ∃ Δ : v.adicCompletion F, EvenNorms Valued.v Δ ∧ Valued.v Δ = 1 ∧ Valued.v (Δ - 1) ≤ Valued.v (4 : v.adicCompletion F) := by
  intro F _ _ v
  obtain ⟨_, hval, hrep, -⟩ := GlobalTheory.T.exists_global_uniformizer_residue_representatives F v
  obtain ⟨ρ, hρ⟩ := exists_not_mem_sq_add_sub F v
  set r : v.adicCompletion F := algebraMap F (v.adicCompletion F) (ρ : F) with hr
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have h := (map_ne_zero (algebraMap F (v.adicCompletion F))).mpr (two_ne_zero (α := F))
    rwa [map_ofNat] at h
  have hint : ∀ a : 𝓞 F, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1 := fun a => by
    rw [hval]; exact v.valuation_le_one a
  have hone : ∀ a : 𝓞 F, a ∉ v.asIdeal →
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 := fun a ha => by
    rw [hval]; exact v.valuation_eq_one_iff_notMem.mpr ha
  have key : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → Valued.v (x ^ 2 + x - r) = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := hrep x hx
    set b : v.adicCompletion F := algebraMap F (v.adicCompletion F) (a : F) with hb_def
    have hb : Valued.v b ≤ 1 := hint a
    have hab : Valued.v (b ^ 2 + b - r) = 1 := by
      have h := hone (a ^ 2 + a - ρ) (hρ a)
      push_cast at h
      simpa [hb_def, hr] using h
    have h3 : Valued.v (x + b + 1) ≤ 1 :=
      Valuation.map_add_le _ (Valuation.map_add_le _ hx hb) (by simp)
    have hsmall : Valued.v ((x - b) * (x + b + 1)) < Valued.v (b ^ 2 + b - r) := by
      rw [hab, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h3) ha
    have e : x ^ 2 + x - r = (x - b) * (x + b + 1) + (b ^ 2 + b - r) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ hsmall, hab]
  refine ⟨1 + 4 * r, GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root _ Valued.v r h2 (hint ρ) key, ?_, ?_⟩
  · have h2le : Valued.v (2 : v.adicCompletion F) ≤ 1 := by
      rw [← one_add_one_eq_two]
      exact Valuation.map_add_le _ (by simp) (by simp)
    have h4 : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
    by_cases h2v : Valued.v (2 : v.adicCompletion F) = 1
    · have hx : Valued.v (-(2 : v.adicCompletion F)⁻¹) = 1 := by
        rw [Valuation.map_neg, map_inv₀, h2v, inv_one]
      have hk := key (-(2 : v.adicCompletion F)⁻¹) hx.le
      have h22 : (2 : v.adicCompletion F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      have e : 1 + 4 * r = -(2 * 2) *
          ((-(2 : v.adicCompletion F)⁻¹) ^ 2 + (-(2 : v.adicCompletion F)⁻¹) - r) := by
        linear_combination (2 * (2 : v.adicCompletion F)⁻¹ - 1) * h22
      rw [e, map_mul, hk, mul_one, Valuation.map_neg, map_mul, h2v, mul_one]
    · have h2lt : Valued.v (2 : v.adicCompletion F) < 1 := lt_of_le_of_ne h2le h2v
      have h4r : Valued.v (4 * r) < Valued.v (1 : v.adicCompletion F) := by
        rw [map_one, map_mul, h4, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint ρ))
          (lt_of_le_of_lt (mul_le_of_le_one_right' h2le) h2lt)
      rw [Valuation.map_add_eq_of_lt_left _ h4r, map_one]
  · rw [add_sub_cancel_left, map_mul]
    exact mul_le_of_le_one_right' (hint ρ)

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLocalNonnormOfNonsquareAdicCompletion
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem exists_even_valuation_of_mul_sq_eq_norm {K : Type} [Field K]
    (w : Valuation K (WithZero (Multiplicative ℤ))) (Δ y s p q : K)
    (hΔ : _root_.GlobalTheory.QNorm.EvenNorms w Δ) (hs : s ≠ 0) (hy : y ≠ 0)
    (h : y * s ^ 2 = p ^ 2 - Δ * q ^ 2) : ∃ n : ℤ, w y = WithZero.exp (2 * n) := by
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_self,
      mul_eq_zero, pow_eq_zero_iff] at h
    tauto
  obtain ⟨n, hn⟩ := hΔ p q hpq
  rw [← h, map_mul, map_pow] at hn
  have hws : w s = WithZero.exp (w s).log :=
    (WithZero.exp_log ((Valuation.ne_zero_iff w).mpr hs)).symm
  rw [hws, ← WithZero.exp_nsmul] at hn
  refine ⟨n - (w s).log, ?_⟩
  have key : w y = WithZero.exp (2 * n) * WithZero.exp (-(2 • (w s).log)) := by
    rw [← hn, mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, mul_one]
  rw [key, ← WithZero.exp_add]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

private theorem not_norm_of_odd_valuation_of_norm_mul {K : Type} [Field K]
    (w : Valuation K (WithZero (Multiplicative ℤ))) (δ Δ y c d : K) (hδ : δ ≠ 0)
    (hΔ : _root_.GlobalTheory.QNorm.EvenNorms w Δ) (hy : y ≠ 0)
    (hodd : ∀ n : ℤ, w y ≠ WithZero.exp (2 * n)) (hc : y = c ^ 2 - δ * Δ * d ^ 2) :
    ¬ ∃ a b : K, y = a ^ 2 - δ * b ^ 2 := by
  rintro ⟨a, b, hab⟩
  have main : ∀ e : K, e ^ 2 = c ^ 2 → a + e ≠ 0 → False := by
    intro e he hs
    have hc2 : y = e ^ 2 - δ * Δ * d ^ 2 := by rw [he]; exact hc
    obtain ⟨n, hn⟩ := exists_even_valuation_of_mul_sq_eq_norm w Δ y (a + e) (a * e + y) (δ * b * d)
      hΔ hs hy (by linear_combination (e ^ 2 - y) * hab + δ * b ^ 2 * hc2)
    exact hodd n hn
  by_cases h1 : a + c = 0
  · by_cases h2 : a + -c = 0
    · have hca : c = -a := by linear_combination h1
      have hb : δ * b ^ 2 = δ * (Δ * d ^ 2) := by
        rw [hca] at hc
        linear_combination hab - hc
      have hb' : b ^ 2 = Δ * d ^ 2 := mul_left_cancel₀ hδ hb
      by_cases hd : d = 0
      · rw [hd] at hb'
        have hb0 : b = 0 := by simpa using hb'
        rw [hb0] at hab
        obtain ⟨n, hn⟩ := exists_even_valuation_of_mul_sq_eq_norm w Δ y 1 a 0 hΔ one_ne_zero hy
          (by rw [hab]; ring)
        exact hodd n hn
      · obtain ⟨n, hn⟩ := hΔ (b / d) 1 (Or.inr one_ne_zero)
        have hz : (b / d) ^ 2 - Δ * 1 ^ 2 = 0 := by
          rw [div_pow, hb']
          field_simp
          ring
        rw [hz, map_zero] at hn
        exact WithZero.exp_ne_zero hn.symm
    · exact main (-c) (by ring) h2
  · exact main c rfl h1

theorem _root_.GlobalTheory.QNorm.exists_local_nonnorm : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (δ : v.adicCompletion F), δ ≠ 0 → ¬ IsSquare δ →
    ∃ x : v.adicCompletion F, x ≠ 0 ∧ ¬ ∃ a b : v.adicCompletion F, x = a ^ 2 - δ * b ^ 2 := by
  intro F _ _ v δ hδ hns
  obtain ⟨c, hc0, hcases⟩ := _root_.GlobalTheory.QNorm.exists_normal_form_of_not_isSquare F v δ hδ hns
  have hδ' : δ * c ^ 2 ≠ 0 := mul_ne_zero hδ (pow_ne_zero 2 hc0)
  suffices h : ∃ x : v.adicCompletion F, x ≠ 0 ∧
      ¬ ∃ a b : v.adicCompletion F, x = a ^ 2 - δ * c ^ 2 * b ^ 2 by
    obtain ⟨x, hx0, hx⟩ := h
    refine ⟨x, hx0, ?_⟩
    rintro ⟨a, b, hab⟩
    refine hx ⟨a, b / c, ?_⟩
    rw [hab]
    field_simp
  obtain ⟨Δ, hΔ, hΔ1, hΔ4⟩ := _root_.GlobalTheory.QNorm.exists_evenNorms_unit F v
  have hΔ0 : Δ ≠ 0 := by
    intro h
    rw [h, map_zero] at hΔ1
    exact zero_ne_one hΔ1
  rcases hcases with ⟨n, hn⟩ | ⟨h1, h4, n, hn⟩ | hE
  · refine ⟨-(δ * c ^ 2 * Δ), neg_ne_zero.mpr (mul_ne_zero hδ' hΔ0),
      not_norm_of_odd_valuation_of_norm_mul Valued.v (δ * c ^ 2) Δ _ 0 1 hδ' hΔ
        (neg_ne_zero.mpr (mul_ne_zero hδ' hΔ0)) ?_ (by ring)⟩
    intro m hm
    rw [Valuation.map_neg, map_mul, hn, hΔ1, mul_one, WithZero.exp_inj] at hm
    omega
  · have hy : (1 : v.adicCompletion F) - δ * c ^ 2 * Δ =
        -((δ * c ^ 2 - 1) + δ * c ^ 2 * (Δ - 1)) := by
      ring
    have hwy : Valued.v ((1 : v.adicCompletion F) - δ * c ^ 2 * Δ) =
        WithZero.exp (2 * n + 1) := by
      rw [hy, Valuation.map_neg, Valuation.map_add_eq_of_lt_left _
        (by rw [map_mul, h1, one_mul]; exact lt_of_le_of_lt hΔ4 h4), hn]
    have hy0 : (1 : v.adicCompletion F) - δ * c ^ 2 * Δ ≠ 0 := by
      intro h
      rw [h, map_zero] at hwy
      exact WithZero.exp_ne_zero hwy.symm
    refine ⟨_, hy0, not_norm_of_odd_valuation_of_norm_mul Valued.v (δ * c ^ 2) Δ _ 1 1 hδ' hΔ hy0 ?_
      (by ring)⟩
    intro m hm
    rw [hwy, WithZero.exp_inj] at hm
    omega
  · obtain ⟨⟨π, -, hπ⟩, -⟩ := _root_.GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v
    have hx0 : algebraMap F (v.adicCompletion F) π ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    refine ⟨_, hx0, ?_⟩
    rintro ⟨a, b, hab⟩
    have hab' : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      rw [h.1, h.2] at hab
      apply hx0
      rw [hab]
      ring
    obtain ⟨m, hm⟩ := hE a b hab'
    rw [← hab, hπ, WithZero.exp_inj] at hm
    omega

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLocalNonnormOfNonsquareAdicCompletionStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_nonnorm_of_nonsquare_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ : v.adicCompletion F), δ ≠ 0 → ¬ IsSquare δ → ∃ x : v.adicCompletion F, x ≠ 0 ∧ ¬ ∃ a b : v.adicCompletion F, x = a ^ 2 - δ * b ^ 2 := by
  first | exact @GlobalTheory.QNorm.exists_local_nonnorm | exact GlobalTheory.QNorm.exists_local_nonnorm | (intros; apply GlobalTheory.QNorm.exists_local_nonnorm <;> assumption)
end
