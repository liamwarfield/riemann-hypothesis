module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesSubringCoeffMulInvMem
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesSubringCoeffMulInvMem
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HahnSub

theorem coeff_mul_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h h' : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hh' : ∀ r, h'.coeff r ∈ A) (r : ℚ) : (h * h').coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact A.sum_mem fun ij _ => A.mul_mem (hh ij.1) (hh' ij.2)

theorem coeff_inv_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hl : h.leadingCoeff⁻¹ ∈ A) (r : ℚ) : (h⁻¹).coeff r ∈ A := by
  by_cases h0 : h = 0
  · subst h0
    simp

  let g : HahnSeries ℚ A :=
    { coeff := fun s => ⟨h.coeff s, hh s⟩
      isPWO_support' := h.isPWO_support.mono fun s hs e => hs (Subtype.ext e) }
  have hg : ∀ s, (g.coeff s : Ω) = h.coeff s := fun s => rfl
  have hg0 : g ≠ 0 := by
    intro e
    apply h0
    ext s
    rw [← hg, e]
    rfl
  have hord : g.order = h.order := by
    apply le_antisymm
    · apply HahnSeries.order_le_of_coeff_ne_zero
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 h0
      rw [HahnSeries.leadingCoeff_eq, ← hg, e]
      rfl
    · apply HahnSeries.order_le_of_coeff_ne_zero
      rw [← hg]
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 hg0
      rw [HahnSeries.leadingCoeff_eq]
      exact Subtype.ext e
  have hlead : (g.leadingCoeff : Ω) = h.leadingCoeff := by
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hg, hord]
  have hunit : IsUnit g.leadingCoeff := by
    refine IsUnit.of_mul_eq_one (⟨h.leadingCoeff⁻¹, hl⟩ : A) ?_
    apply Subtype.ext
    show (g.leadingCoeff : Ω) * h.leadingCoeff⁻¹ = 1
    rw [hlead]
    exact mul_inv_cancel₀ (HahnSeries.leadingCoeff_ne_zero.2 h0)
  obtain ⟨v, hv⟩ := (HahnSeries.isUnit_iff.2 hunit).exists_right_inv
  let f : A →ₙ+* Ω := A.subtype.toNonUnitalRingHom
  have hgf : g.map f = h := by
    ext s
    rfl
  have hone : (1 : HahnSeries ℚ A).map f = 1 := by
    ext s
    rw [HahnSeries.map_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> rfl
  have key : h * v.map f = 1 := by
    rw [← hgf, ← HahnSeries.map_mul, hv, hone]
  rw [inv_eq_of_mul_eq_one_right key, HahnSeries.map_coeff]
  exact (v.coeff r).2

theorem coeff_mul_inv_mem : ∀ (Ω : Type) [Field Ω] (A : Subring Ω), (∀ h h' : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → (∀ r, h'.coeff r ∈ A) → ∀ r, (h * h').coeff r ∈ A) ∧ ∀ h : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → h.leadingCoeff⁻¹ ∈ A → ∀ r, (h⁻¹).coeff r ∈ A := by
  intro Ω _ A
  exact ⟨fun h h' hh hh' r => coeff_mul_mem A h h' hh hh' r,
    fun h hh hl r => coeff_inv_mem A h hh hl r⟩

end GlobalTheory.HahnSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesSubringCoeffMulInvMemStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem : ∀ (Ω : Type) [Field Ω] (A : Subring Ω), (∀ h h' : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → (∀ r, h'.coeff r ∈ A) → ∀ r, (h * h').coeff r ∈ A) ∧ ∀ h : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → h.leadingCoeff⁻¹ ∈ A → ∀ r, (h⁻¹).coeff r ∈ A := by
  first | exact @GlobalTheory.HahnSub.coeff_mul_inv_mem | exact GlobalTheory.HahnSub.coeff_mul_inv_mem | (intros; apply GlobalTheory.HahnSub.coeff_mul_inv_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffMemFinitelyGeneratedSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffsMemFinitelyGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinAlgebraicPowerSeriesCoeffClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinAlgebraicPowerSeriesCoeffClosure
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgPowerSeries

theorem mem_range_map_iff {L : Type} [CommRing L] (B : Subring L) (f : PowerSeries L) :
    f ∈ (PowerSeries.map B.subtype).range ↔ ∀ k, PowerSeries.coeff k f ∈ B := by
  constructor
  · rintro ⟨g, rfl⟩ k
    rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff k g).2
  · intro h
    refine ⟨PowerSeries.mk fun k => ⟨PowerSeries.coeff k f, h k⟩, ?_⟩
    ext k; simp [PowerSeries.coeff_map]

theorem exists_finset_coeff_mem_closure :
    ∀ (L : Type) [Field L] [CharZero L] (A : Subring L) (b : PowerSeries L)
      (Q : Polynomial (PowerSeries L)), Q ≠ 0 →
      (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A) → Q.eval b = 0 →
      ∃ S : Finset L, ∀ k, PowerSeries.coeff k b ∈ Subring.closure ((A : Set L) ∪ S) := by
  classical
  intro L _ _ A b Q hQ hA hb
  obtain ⟨RA, hRAdef⟩ : ∃ RA : Subring (PowerSeries L), RA = (PowerSeries.map A.subtype).range :=
    ⟨_, rfl⟩
  have hex : ∃ d, ∃ R : Polynomial (PowerSeries L), R ≠ 0 ∧ (∀ i, R.coeff i ∈ RA) ∧
      R.eval b = 0 ∧ R.natDegree = d :=
    ⟨Q.natDegree, Q, hQ, fun i => hRAdef ▸ (mem_range_map_iff A _).2 (hA i), hb, rfl⟩
  obtain ⟨R, hR0, hRA', hRb, hRd⟩ := Nat.find_spec hex
  have hmin : ∀ R' : Polynomial (PowerSeries L), R' ≠ 0 → (∀ i, R'.coeff i ∈ RA) →
      R'.natDegree < R.natDegree → R'.eval b ≠ 0 := by
    intro R' h0 hc hlt he
    exact Nat.find_min hex (by omega) ⟨R', h0, hc, he, rfl⟩
  have hdeg : R.natDegree ≠ 0 := by
    intro h
    rw [Polynomial.eq_C_of_natDegree_eq_zero h, Polynomial.eval_C] at hRb
    apply hR0; rw [Polynomial.eq_C_of_natDegree_eq_zero h, hRb, map_zero]
  obtain ⟨D, hD⟩ : ∃ D, D = Polynomial.derivative R := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := by
    haveI : HasUniqueDiv (PowerSeries L) := IsAddTorsionFree.of_isTorsionFree L _
    intro h; rw [hD] at h; exact hdeg (Polynomial.natDegree_eq_zero_of_derivative_eq_zero h)
  have hDc : ∀ i, D.coeff i ∈ RA := by
    intro i; rw [hD, Polynomial.coeff_derivative]
    exact RA.mul_mem (hRA' _) (RA.add_mem (natCast_mem RA _) RA.one_mem)
  have hDb : D.eval b ≠ 0 :=
    hmin D hD0 hDc (hD ▸ Polynomial.natDegree_derivative_lt hdeg)
  obtain ⟨F, hF⟩ : ∃ F, F = D.eval b := ⟨_, rfl⟩
  have hex2 : ∃ m, PowerSeries.coeff m F ≠ 0 := by
    by_contra h; push_neg at h; exact hDb (hF ▸ PowerSeries.ext fun k => by simpa using h k)
  obtain ⟨m, hc, hlow⟩ : ∃ m, PowerSeries.coeff m F ≠ 0 ∧ ∀ i < m, PowerSeries.coeff i F = 0 :=
    ⟨Nat.find hex2, Nat.find_spec hex2, fun i hi => not_not.mp (Nat.find_min hex2 hi)⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = PowerSeries.coeff m F := ⟨_, rfl⟩
  rw [← hcdef] at hc
  refine ⟨insert c⁻¹ ((Finset.range (m+1)).image fun i => PowerSeries.coeff i b), ?_⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = Subring.closure ((A : Set L) ∪
      ↑(insert c⁻¹ ((Finset.range (m+1)).image fun i => PowerSeries.coeff i b))) := ⟨_, rfl⟩
  rw [← hBdef]
  have hAB : ∀ x ∈ A, x ∈ B := fun x hx => hBdef ▸ Subring.subset_closure (Or.inl hx)
  have hcB : c⁻¹ ∈ B := hBdef ▸ Subring.subset_closure (Or.inr (by simp))
  have hbB : ∀ i ≤ m, PowerSeries.coeff i b ∈ B := fun i hi =>
    hBdef ▸ Subring.subset_closure (Or.inr (by simp; exact Or.inr ⟨i, by omega, rfl⟩))
  obtain ⟨RB, hRBdef⟩ : ∃ RB : Subring (PowerSeries L), RB = (PowerSeries.map B.subtype).range :=
    ⟨_, rfl⟩
  have hRARB : ∀ f ∈ RA, f ∈ RB := fun f hf => by
    rw [hRBdef]; rw [hRAdef] at hf
    exact (mem_range_map_iff B f).2 fun k => hAB _ ((mem_range_map_iff A f).1 hf k)
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases le_or_gt n m with hnm | hmn
  · exact hbB n hnm
  obtain ⟨u, hu⟩ : ∃ u : PowerSeries L,
      u = PowerSeries.mk fun k => if k < n then PowerSeries.coeff k b else 0 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : PowerSeries L,
      v = PowerSeries.mk fun k => PowerSeries.coeff (n + k) b := ⟨_, rfl⟩
  have hbuv : b = u + PowerSeries.X ^ n * v := by
    ext k
    rw [map_add (f := _), PowerSeries.coeff_X_pow_mul', hu, hv]
    simp only [PowerSeries.coeff_mk]
    by_cases h1 : k < n
    · rw [if_pos h1, if_neg (by omega), add_zero]
    · rw [if_neg h1, if_pos (by omega), zero_add, show n + (k - n) = k by omega]
  have huB : u ∈ RB := by
    rw [hRBdef]
    refine (mem_range_map_iff B u).2 fun k => ?_
    rw [hu, PowerSeries.coeff_mk]; split_ifs with h
    · exact ih k h
    · exact B.zero_mem
  have hRu : R.eval u ∈ RB := by
    rw [Polynomial.eval_eq_sum_range]
    exact RB.sum_mem fun i _ => RB.mul_mem (hRARB _ (hRA' i)) (RB.pow_mem huB _)
  have hdvd : PowerSeries.X ^ n ∣ F - D.eval u := by
    have h1 := Polynomial.sub_dvd_eval_sub b u D
    have h2 : b - u = PowerSeries.X ^ n * v := by rw [hbuv]; ring
    rw [h2, ← hF] at h1
    exact (dvd_mul_right _ _).trans h1
  obtain ⟨w, hw⟩ := hdvd
  obtain ⟨k, hk⟩ := R.binomExpansion u (PowerSeries.X ^ n * v)
  rw [← hbuv, hRb, ← hD] at hk
  have hDu : D.eval u = F - PowerSeries.X ^ n * w := by rw [← hw]; ring
  rw [hDu] at hk
  have key : 0 = R.eval u + PowerSeries.X ^ n * (F * v) +
      PowerSeries.X ^ (n + n) * (k * v ^ 2 - w * v) := by
    rw [hk]; ring
  have hc2 := congrArg (PowerSeries.coeff (n + m)) key
  rw [map_zero, map_add (f := _), map_add (f := _), PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    if_pos (by omega), if_neg (by omega), add_zero, Nat.add_sub_cancel_left] at hc2
  have hFv : PowerSeries.coeff m (F * v) = c * PowerSeries.coeff n b := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (m, 0)]
    · rw [← hcdef, hv, PowerSeries.coeff_mk, add_zero]
    · rintro ⟨i, j⟩ hij hne
      have hij' : i + j = m := by simpa using hij
      have him : i < m := by
        rcases Nat.lt_or_ge i m with h | h
        · exact h
        · exfalso; apply hne; simp only [Prod.mk.injEq]; omega
      rw [hlow i him, zero_mul]
    · intro h; exfalso; exact h (by simp)
  have hcn : c * PowerSeries.coeff n b ∈ B := by
    have e : c * PowerSeries.coeff n b = - PowerSeries.coeff (n + m) (R.eval u) := by
      linear_combination -hc2 - hFv
    rw [e]
    rw [hRBdef] at hRu
    exact B.neg_mem ((mem_range_map_iff B _).1 hRu _)
  have e2 : PowerSeries.coeff n b = c⁻¹ * (c * PowerSeries.coeff n b) := by
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [e2]; exact B.mul_mem hcB hcn

end GlobalTheory.AlgPowerSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinAlgebraicPowerSeriesCoeffClosureStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_algebraic_powerSeries_coeff_closure : ∀ (L : Type) [Field L] [CharZero L] (A : Subring L) (b : PowerSeries L) (Q : Polynomial (PowerSeries L)), Q ≠ 0 → (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A) → Q.eval b = 0 → ∃ S : Finset L, ∀ k, PowerSeries.coeff k b ∈ Subring.closure ((A : Set L) ∪ S) := by
  first | exact @GlobalTheory.AlgPowerSeries.exists_finset_coeff_mem_closure | exact GlobalTheory.AlgPowerSeries.exists_finset_coeff_mem_closure | (intros; apply GlobalTheory.AlgPowerSeries.exists_finset_coeff_mem_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffsMemFinitelyGenerated
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

def clearCoeff (n M w : ℕ) (c : Fin n → Polynomial ℂ) (i : ℕ) (τ : ℍ) : ℂ :=
  if h : i < n then
    DD τ ^ (w * (n - i)) * ∑ k ∈ Finset.range (M + 1), (c ⟨i, h⟩).coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k))
  else DD τ ^ M

theorem dd_pow_mul_eval_jT (p : Polynomial ℂ) (M : ℕ) (hp : p.natDegree ≤ M) (τ : ℍ) :
    DD τ ^ M * p.eval (jT τ) =
      ∑ k ∈ Finset.range (M + 1), p.coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k)) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hD := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  have hsplit : DD τ ^ M = DD τ ^ (M - k) * DD τ ^ k := by rw [← pow_add, Nat.sub_add_cancel hk']
  rw [hsplit]
  simp only [ReciprocityTheory.ChartRestriction.L1.jT, ReciprocityTheory.ChartRestriction.L1.AA]
  rw [div_pow, pow_mul]
  field_simp

theorem sum_clearCoeff_eq_zero (n M w : ℕ) (c : Fin n → Polynomial ℂ) (hM : ∀ i, (c i).natDegree ≤ M)
    (f : ℍ → ℂ) (h : ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0) (τ : ℍ) :
    ∑ i ∈ Finset.range (n + 1), clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i = 0 := by
  have key : ∑ i ∈ Finset.range (n + 1), clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i =
      DD τ ^ (w * n + M) * (f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ)) := by
    rw [Finset.sum_range_succ, Finset.sum_range (fun i => clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i),
      mul_add, Finset.mul_sum, add_comm]
    congr 1
    · simp only [clearCoeff, lt_irrefl, dite_false]
      rw [mul_pow, ← pow_mul, pow_add]
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [clearCoeff, Fin.is_lt, dite_true, Fin.eta]
      rw [← dd_pow_mul_eval_jT _ M (hM i), mul_pow, ← pow_mul]
      have e : w * (n - i) + M + w * i = w * n + M := by
        rw [add_right_comm, ← mul_add, Nat.sub_add_cancel i.isLt.le]
      rw [← e, pow_add, pow_add]
      ring
  rw [key, h τ, mul_zero]

theorem qall_clearCoeff (R : Subring ℂ) (N : ℕ) (hN : 0 < N) (n M w : ℕ) (c : Fin n → Polynomial ℂ)
    (hc : ∀ (i : Fin n) (k : ℕ), k ≤ M → (c i).coeff k ∈ R) (i : ℕ) :
    QAll (· ∈ R) N (clearCoeff n M w c i) := by
  obtain ⟨hcst, -, -, hmul, hpow, hsum⟩ := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed R N hN
  have hDD : QAll (· ∈ R) N DD := ((GlobalTheory.T.eisenstein_delta_qExpansion_integrality N hN DD (Or.inr (Or.inr rfl))).2.1) R
  have hE : QAll (· ∈ R) N ⇑E₄ := ((GlobalTheory.T.eisenstein_delta_qExpansion_integrality N hN ⇑E₄ (Or.inl rfl)).2.1) R
  by_cases h : i < n
  · have hf : clearCoeff n M w c i = fun τ => DD τ ^ (w * (n - i)) *
        ∑ k ∈ Finset.range (M + 1), (c ⟨i, h⟩).coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k)) := by
      funext τ; simp [clearCoeff, h]
    rw [hf]
    refine hmul _ _ (hpow _ _ hDD) ?_
    refine (hsum ℕ (Finset.range (M + 1)) _ fun k hk => ?_).1
    exact hmul _ _ (hcst _ (hc _ k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))))
      (hmul _ _ (hpow _ _ hE) (hpow _ _ hDD))
  · have hf : clearCoeff n M w c i = fun τ => DD τ ^ M := by funext τ; simp [clearCoeff, h]
    rw [hf]
    exact hpow _ _ hDD

theorem powerSeries_map_mk {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (g : ℕ → Ω) :
    PowerSeries.map ε (PowerSeries.mk g) = PowerSeries.mk fun k => ε (g k) := by
  ext k; simp [PowerSeries.coeff_map]

theorem qcoeff_finitelyGenerated : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N w : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω),
    0 < N → Lv ε.range N w f → HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) →
      ∃ S : Finset Ω, ∀ k, a k ∈ Subring.closure (S : Set Ω) := by
  intro Ω _ ε N w f a hN hLv hF
  classical
  haveI : CharZero Ω := ε.charZero
  obtain ⟨n, c, hc, hrel⟩ := GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver ε.range f ⟨N, w, hN, hLv⟩
  set M := ∑ i, (c i).natDegree with hMdef
  have hM : ∀ i, (c i).natDegree ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => (c i).natDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpre : ∀ (i : Fin n) (k : ℕ), ∃ x : Ω, ε x = (c i).coeff k := fun i k => RingHom.mem_range.1 (hc i k)
  choose e he using hpre
  set S₀ : Finset Ω := Finset.univ.image (fun p : Fin n × Fin (M + 1) => e p.1 p.2) with hS₀
  set A : Subring Ω := Subring.closure (S₀ : Set Ω) with hA
  set R : Subring ℂ := A.map ε with hR
  have hcR : ∀ (i : Fin n) (k : ℕ), k ≤ M → (c i).coeff k ∈ R := fun i k hk =>
    Subring.mem_map.2 ⟨e i k, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_image.2
      ⟨(i, ⟨k, Nat.lt_succ_of_le hk⟩), Finset.mem_univ _, rfl⟩)), he i k⟩
  have hP : ∀ i, QAll (· ∈ R) N (clearCoeff n M w c i) := qall_clearCoeff R N hN n M w c hcR
  choose c' hc'Q hc'R using hP
  have hser := GlobalTheory.T.polynomial_relation_passes_to_qExpansions N n (fun τ => DD τ ^ w * f τ) (fun k => ε (a k)) (clearCoeff n M w c) c' hN hF hc'Q
    (sum_clearCoeff_eq_zero n M w c hM f hrel)
  have hpre2 : ∀ i k, ∃ x ∈ A, ε x = c' i k := fun i k => Subring.mem_map.1 (hc'R i k)
  choose d hdA hd using hpre2
  set Q : Polynomial (PowerSeries Ω) :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (d i)) with hQdef
  have hmap : PowerSeries.map ε (Q.eval (PowerSeries.mk a)) =
      (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c' i))).eval
        (PowerSeries.mk fun k => ε (a k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hQdef, Polynomial.eval_finsetSum, Polynomial.eval_monomial, map_sum, map_mul, map_pow,
      powerSeries_map_mk, hd]
  rw [hser] at hmap
  have hQ : Q.eval (PowerSeries.mk a) = 0 := by
    ext k
    have := congrArg (PowerSeries.coeff k) hmap
    simpa [PowerSeries.coeff_map] using this
  have hcoef : ∀ i, Q.coeff i = if i ∈ Finset.range (n + 1) then PowerSeries.mk (d i) else 0 := fun i => by
    simp only [hQdef, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    simp [Finsupp.single_apply]
  have hQne : Q ≠ 0 := by
    intro h0
    have hn := hcoef n
    rw [h0, Polynomial.coeff_zero, if_pos (Finset.self_mem_range_succ n)] at hn
    have hc0 : c' n = 0 := funext fun k => by
      have h1 := congrArg (PowerSeries.coeff k) hn
      rw [PowerSeries.coeff_mk, map_zero] at h1
      rw [← hd n k, ← h1, map_zero]; rfl
    have hq := hc'Q n
    have hPn : clearCoeff n M w c n = fun τ => DD τ ^ M := by funext τ; simp [clearCoeff]
    rw [hPn, hc0] at hq
    have hz : HasQ N (fun _ : ℍ => (0 : ℂ)) (0 : ℕ → ℂ) := fun τ => by simpa using hasSum_zero
    have := (GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique).2 N _ _ 0 hq hz
    exact pow_ne_zero M (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero UpperHalfPlane.I) (congrFun this UpperHalfPlane.I)
  have hcA : ∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A := fun i k => by
    rw [hcoef i]
    split_ifs
    · rw [PowerSeries.coeff_mk]; exact hdA i k
    · simp
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.eisenstein_algebraic_powerSeries_coeff_closure Ω A (PowerSeries.mk a) Q hQne hcA hQ
  refine ⟨S₀ ∪ S₁, fun k => ?_⟩
  have hk := hS₁ k
  rw [PowerSeries.coeff_mk] at hk
  refine (Subring.closure_le.2 ?_) hk
  rintro x (hx | hx)
  · exact Subring.closure_mono (by simp [Finset.coe_union]) hx
  · exact Subring.subset_closure (by simp [hx])

end GlobalTheory.FN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffsMemFinitelyGeneratedStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_coeffs_mem_finitelyGenerated : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N w : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω), 0 < N → Lv ε.range N w f → HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) → ∃ S : Finset Ω, ∀ k, a k ∈ Subring.closure (S : Set Ω) := by
  first | exact @GlobalTheory.FN.qcoeff_finitelyGenerated | exact GlobalTheory.FN.qcoeff_finitelyGenerated | (intros; apply GlobalTheory.FN.qcoeff_finitelyGenerated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffMemFinitelyGeneratedSubring
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem coeff_fg : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ) (h : HahnSeries ℚ Ω),
    InR ε.range f → IsExp ε f h → ∃ S : Finset Ω, ∀ r, h.coeff r ∈ Subring.closure (S : Set Ω) := by
  intro Ω _ ε f h hf hh
  obtain ⟨N, w, hN, hLv⟩ := hf
  obtain ⟨b, hb, hbE⟩ := hLv.2 1
  have hb' : HasQ N (fun τ => DD τ ^ w * f τ) b := by
    simpa only [one_smul] using hb
  choose a ha using fun n => (hbE n : b n ∈ ε.range)
  have hb'' : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) := by
    have : (fun n => ε (a n)) = b := funext ha
    rw [this]; exact hb'
  obtain ⟨S, hS⟩ := GlobalTheory.T.qExpansion_coeffs_mem_finitelyGenerated Ω ε N w f a hN hLv hb''
  obtain ⟨H, hH, hHa, hH0⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N (fun τ => DD τ ^ w * f τ) a hN hb''
  obtain ⟨hD, hDe, hD0, hDl, hDz⟩ := GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε
  obtain ⟨hops, huniq, hC, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨hmul, hinv⟩ := GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem Ω (Subring.closure (S : Set Ω))
  set A := Subring.closure (S : Set Ω)

  have hpow : ∀ k : ℕ, IsExp ε (fun τ => DD τ ^ k) (hD ^ k) := by
    intro k
    induction k with
    | zero =>
      have := hC 1
      simpa [map_one] using this
    | succ k ih =>
      have e : (fun τ => DD τ ^ (k + 1)) = (fun τ => DD τ ^ k) * DD := by
        funext τ; simp [pow_succ]
      rw [e, pow_succ]
      exact (hops _ _ _ _ ih hDe).2.2
  have hprod : IsExp ε (fun τ => DD τ ^ w * f τ) (hD ^ w * h) := (hops _ _ _ _ (hpow w) hh).2.2
  have hEq : hD ^ w * h = H := huniq _ _ _ hprod hH
  have hDw0 : hD ^ w ≠ 0 := pow_ne_zero _ hD0
  have hEq' : h = H * (hD⁻¹) ^ w := by
    rw [← hEq, inv_pow, mul_comm (hD ^ w) h, mul_assoc, mul_inv_cancel₀ hDw0, mul_one]

  have hHA : ∀ r, H.coeff r ∈ A := by
    intro r
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr
      rw [hHa k]; exact hS k
    · push_neg at hr
      rw [hH0 r hr]; exact A.zero_mem
  have hDA : ∀ r, hD.coeff r ∈ A := by
    intro r
    obtain ⟨n, hn⟩ := hDz r
    rw [hn]; exact intCast_mem A n
  have hDiA : ∀ r, (hD⁻¹).coeff r ∈ A := hinv hD hDA (by rw [hDl, inv_one]; exact A.one_mem)
  have hpA : ∀ k : ℕ, ∀ r, ((hD⁻¹) ^ k).coeff r ∈ A := by
    intro k
    induction k with
    | zero =>
      intro r
      rw [pow_zero]
      by_cases hr : r = 0
      · subst hr; simpa using A.one_mem
      · simpa [hr] using A.zero_mem
    | succ k ih =>
      intro r
      rw [pow_succ]
      exact hmul _ _ ih hDiA r
  refine ⟨S, fun r => ?_⟩
  rw [hEq']
  exact hmul _ _ hHA (hpA w) r

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffMemFinitelyGeneratedSubringStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspExpansion_coeff_mem_finitelyGenerated_subring : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ) (h : HahnSeries ℚ Ω), InR ε.range f → IsExp ε f h → ∃ S : Finset Ω, ∀ r, h.coeff r ∈ Subring.closure (S : Set Ω) := by
  first | exact @GlobalTheory.FN.coeff_fg | exact GlobalTheory.FN.coeff_fg | (intros; apply GlobalTheory.FN.coeff_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicSubringClosureCommonDenominator
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicSubringClosureCommonDenominator
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem finite_subring_common_denominator :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (S : Finset Ω),
      ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Subring.closure (S : Set Ω),
        ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x) := by
  intro Ω _ _ _ S
  have hZQ : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hZ : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ ℚ Ω
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples (R := ℤ) S
  set D : ℕ := y.natAbs with hDdef
  refine ⟨D, Int.natAbs_pos.mpr hy0, ?_⟩
  have hDint : ∀ j : ℕ, IsIntegral ℤ ((D : Ω) ^ j) := by
    intro j
    have h : ((D : Ω) ^ j) = algebraMap ℤ Ω ((D : ℤ) ^ j) := by simp
    rw [h]
    exact isIntegral_algebraMap
  let T : Subring Ω :=
    { carrier := {x | ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x)}
      mul_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        have : (D : Ω) ^ (i + j) * (a * b) = ((D : Ω) ^ i * a) * ((D : Ω) ^ j * b) := by ring
        rw [this]; exact hi.mul hj
      one_mem' := ⟨0, by simpa using (isIntegral_one : IsIntegral ℤ (1 : Ω))⟩
      add_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        have : (D : Ω) ^ (i + j) * (a + b) =
            (D : Ω) ^ j * ((D : Ω) ^ i * a) + (D : Ω) ^ i * ((D : Ω) ^ j * b) := by ring
        rw [this]; exact ((hDint j).mul hi).add ((hDint i).mul hj)
      zero_mem' := ⟨0, by simpa using (isIntegral_zero : IsIntegral ℤ (0 : Ω))⟩
      neg_mem' := by
        rintro a ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have : (D : Ω) ^ i * -a = -((D : Ω) ^ i * a) := by ring
        rw [this]; exact hi.neg }
  have hST : (S : Set Ω) ⊆ T := by
    intro x hx
    refine ⟨1, ?_⟩
    have hx' := hy x hx
    rw [pow_one]
    rcases Int.natAbs_eq y with h | h
    · have e : y • x = (D : Ω) * x := by
        rw [zsmul_eq_mul]; congr 1; rw [h]; simp [hDdef]
      rw [← e]; exact hx'
    · have e : y • x = -((D : Ω) * x) := by
        rw [zsmul_eq_mul, h]; simp [hDdef]
      have := hx'.neg
      rw [e, neg_neg] at this
      exact this
  intro x hx
  exact (Subring.closure_le.mpr hST) hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicSubringClosureCommonDenominatorStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_subring_closure_common_denominator : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (S : Finset Ω), ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Subring.closure (S : Set Ω), ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x) := by
  first | exact @GlobalTheory.finite_subring_common_denominator | exact GlobalTheory.finite_subring_common_denominator | (intros; apply GlobalTheory.finite_subring_common_denominator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominators
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_bdd_den : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K),
    ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (T.exp f).coeff r) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hexpS : ∀ c : ring ε.range, ∃ S : Finset Ω, ∀ r, (T.exp (T.io c)).coeff r ∈ Subring.closure (S : Set Ω) := by
    intro c
    have hc : InR ε.range (c : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 c).1 c.2
    exact GlobalTheory.T.cuspExpansion_coeff_mem_finitelyGenerated_subring Ω ε c _ hc (T.exp_io c)
  obtain ⟨Sa, hSa⟩ := hexpS a
  obtain ⟨Sb, hSb⟩ := hexpS b
  have hiob : T.io b ≠ 0 := by
    intro h
    apply hb
    apply T.io_inj
    rw [h, map_zero]
  have hexpb : T.exp (T.io b) ≠ 0 := by
    intro h
    apply hiob
    exact (injective_iff_map_eq_zero (T.exp : T.K →+* HahnSeries ℚ Ω)).1
      (T.exp : T.K →+* HahnSeries ℚ Ω).injective _ h
  have hf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹ := by
    rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ hexpb, mul_one]
  classical
  let S : Finset Ω := Sa ∪ Sb ∪ {(T.exp (T.io b)).leadingCoeff⁻¹}
  let A : Subring Ω := Subring.closure (S : Set Ω)
  have hA_a : ∀ r, (T.exp (T.io a)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSa r)
  have hA_b : ∀ r, (T.exp (T.io b)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSb r)
  have hA_l : (T.exp (T.io b)).leadingCoeff⁻¹ ∈ A := Subring.subset_closure (by simp [S])
  have hP := GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem Ω A
  have hA_inv := hP.2 _ hA_b hA_l
  have hA_f : ∀ r, (T.exp f).coeff r ∈ A := by
    intro r
    rw [hf]
    exact hP.1 _ _ hA_a hA_inv r
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨D, hD, hDk⟩ := GlobalTheory.T.algebraic_subring_closure_common_denominator Ω S
  exact ⟨D, hD, fun r => hDk _ (hA_f r)⟩

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominatorsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_bounded_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (T.exp f).coeff r) := by
  first | exact @GlobalTheory.FN.frac_bdd_den | exact GlobalTheory.FN.frac_bdd_den | (intros; apply GlobalTheory.FN.frac_bdd_den <;> assumption)
end
