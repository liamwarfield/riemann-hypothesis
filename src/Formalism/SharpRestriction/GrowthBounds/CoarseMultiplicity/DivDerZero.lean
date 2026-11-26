module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TopOddNeEnd
public import Formalism.SharpRestriction.GrowthBounds.PolBridge

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CthMonomial
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Cth

variable {K : Type} [Field K] {σ : Type}

def cth (v : σ) (n : ℕ) (F : MvPolynomial σ K) : MvPolynomial σ K :=
  monomial (Finsupp.single v n) (1 : K) * divDer (Finsupp.single v n) F

theorem coeff_cth (v : σ) (n : ℕ) (F : MvPolynomial σ K) (μ : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (cth v n F) μ = AddMonoidAlgebra.coeff F μ * (((μ v).choose n : ℕ) : K) := by
  unfold cth
  rw [eig_one]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Finsupp.prod_single_index (by simp)]

theorem cth_add (v : σ) (n : ℕ) (F G : MvPolynomial σ K) : cth v n (F + G) = cth v n F + cth v n G := by
  ext μ
  simp only [coeff_cth, MvPolynomial.coeff_add, add_mul]

theorem cth_smul (v : σ) (n : ℕ) (c : K) (F : MvPolynomial σ K) : cth v n (c • F) = c • cth v n F := by
  ext μ
  simp only [coeff_cth, coeff_smul, smul_eq_mul, mul_assoc]

def cthL (v : σ) (n : ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K where
  toFun := cth v n
  map_add' := cth_add v n
  map_smul' := cth_smul v n

theorem cth_monomial (v : σ) (n : ℕ) (e : σ →₀ ℕ) (c : K) :
    cth v n (monomial e c) = monomial e (c * (((e v).choose n : ℕ) : K)) := by
  classical
  ext μ
  rw [coeff_cth, coeff_monomial, coeff_monomial]
  split_ifs with h
  · rw [h]
  · rw [zero_mul]

theorem cth_zero (v : σ) (F : MvPolynomial σ K) : cth v 0 F = F := by
  ext μ
  simp [coeff_cth]

theorem cth_mul (v : σ) (n : ℕ) (F G : MvPolynomial σ K) :
    cth v n (F * G) = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, cth v ab.1 F * cth v ab.2 G := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add F F' hF hF' =>
    rw [add_mul, cth_add, hF, hF', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ab _ => by rw [cth_add, add_mul]
  | monomial e c =>
    induction G using MvPolynomial.induction_on' with
    | add G G' hG hG' =>
      rw [mul_add, cth_add, hG, hG', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ab _ => by rw [cth_add, mul_add]
    | monomial e' c' =>
      set_option synthInstance.maxHeartbeats 100000 in
        rw [monomial_mul, cth_monomial, Finsupp.add_apply, Nat.add_choose_eq, Nat.cast_sum, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [cth_monomial, cth_monomial, monomial_mul]
      congr 1
      push_cast
      ring

theorem cth_free (v : σ) {F : MvPolynomial σ K} (hF : ∀ μ ∈ F.support, μ v = 0) {n : ℕ} (hn : n ≠ 0) :
    cth v n F = 0 := by
  ext μ
  rw [coeff_cth]
  change F.coeff μ * (((μ v).choose n : ℕ) : K) = 0
  by_cases h : μ ∈ F.support
  · rw [hF μ h, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hn)]
    simp
  · rw [notMem_support_iff.1 h, zero_mul]

theorem cth_mul_free (v : σ) (n : ℕ) {F : MvPolynomial σ K} (hF : ∀ μ ∈ F.support, μ v = 0) (G : MvPolynomial σ K) :
    cth v n (F * G) = F * cth v n G := by
  classical
  rw [cth_mul, Finset.sum_eq_single (0, n)]
  · rw [cth_zero]
  · rintro ⟨a, b⟩ hab hne
    have ha : a ≠ 0 := by
      rintro rfl
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      simp only [zero_add] at hab
      exact hne (by rw [hab])
    rw [cth_free v hF ha, zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h

theorem cth_pow (v : σ) {E m : MvPolynomial σ K} (h1 : cth v 1 E = m) (h2 : ∀ a, 2 ≤ a → cth v a E = 0) (j l : ℕ) :
    cth v l (E ^ j) = ((j.choose l : ℕ) : K) • (E ^ (j - l) * m ^ l) := by
  classical
  induction j generalizing l with
  | zero =>
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [cth_zero]
    · rw [pow_zero, Nat.choose_eq_zero_of_lt hl, Nat.cast_zero, zero_smul]
      refine cth_free v ?_ hl.ne'
      intro μ hμ
      have : μ = 0 := by
        by_contra hne
        rw [mem_support_iff, coeff_one, if_neg (Ne.symm hne)] at hμ
        exact hμ rfl
      rw [this]; rfl
  | succ j ih =>
    rw [pow_succ, cth_mul]
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [cth_zero, pow_succ]
    · obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
      have hsub : ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal (l' + 1), ab ≠ (l' + 1, 0) → ab ≠ (l', 1) →
          cth v ab.1 (E ^ j) * cth v ab.2 E = 0 := by
        rintro ⟨a, b⟩ hab hn1 hn2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
        simp only at hab
        have hb : 2 ≤ b := by
          by_contra hb
          have : b = 0 ∨ b = 1 := by omega
          rcases this with rfl | rfl
          · exact hn1 (by simp at hab; rw [hab])
          · exact hn2 (by have : a = l' := by omega
                          rw [this])
        rw [h2 b hb, mul_zero]
      have hne : ((l' + 1, 0) : ℕ × ℕ) ≠ (l', 1) := by simp
      rw [← Finset.sum_subset (s₁ := {(l' + 1, 0), (l', 1)})
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [Finset.HasAntidiagonal.mem_antidiagonal])
        (by
          intro x hx hx'
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
          exact hsub x hx hx'.1 hx'.2),
        Finset.sum_pair hne]
      simp only
      rw [ih, ih, cth_zero, h1, Nat.choose_succ_succ' j l']
      by_cases hlj : l' + 1 ≤ j
      · have e1 : j + 1 - (l' + 1) = (j - (l' + 1)) + 1 := by omega
        have e2 : j - l' = (j - (l' + 1)) + 1 := by omega
        rw [e1, e2]
        push_cast
        simp only [smul_eq_C_mul, pow_succ, map_add (f := _)]
        ring
      · have e0 : j.choose (l' + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have e1 : j + 1 - (l' + 1) = j - l' := by omega
        rw [e0, e1]
        simp only [Nat.cast_zero, zero_smul, zero_mul, zero_add, add_zero, smul_eq_C_mul, pow_succ]
        ring

end Cth

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section Y

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem ycond_op (D : Formalism.BasicNotions.D7) (LL LL' : ChainLetters N) (hv : LL'.vec = LL.vec) (j : ℕ) {M M' : WithTop ℤ} (n : ℕ)
    (hM : M + ((n : ℤ) : WithTop ℤ) ≤ M') (al be : Fin N × Fin r →₀ ℕ)
    (hn : vecDeg (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} al +
      covDeg (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} be ≤ n)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YCond (KK O) (r := r) LL j M) :
    monomial al 1 * divDer be y ∈ YCond (KK O) (r := r) LL' j M' := by
  cases M' with
  | top => rw [PolBridge.ycond_top]; exact Submodule.mem_top
  | coe M' =>
    cases M with
    | top => simp at hM
    | coe M =>
      rw [PolBridge.mem_ycond_iff D] at hy ⊢
      rw [hv]
      have h1 := flt_op_lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} y al be n hn
      refine h1.trans ?_
      have h2 : M + (n : ℤ) ≤ M' := by exact_mod_cast hM
      calc lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} y + ((n : ℤ) : WithBot ℤ)
          ≤ ((M : ℤ) : WithBot ℤ) + ((n : ℤ) : WithBot ℤ) := by gcongr
        _ = ((M + (n : ℤ) : ℤ) : WithBot ℤ) := by norm_cast
        _ ≤ _ := by exact_mod_cast h2

theorem divDer_zero {R : Type} [CommSemiring R] {σ : Type} (F : MvPolynomial σ R) : divDer 0 F = F := by
  unfold divDer
  conv_rhs => rw [F.as_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp

theorem intPol_cth {σ : Type} (v : σ) (n : ℕ) {y : MvPolynomial σ (KK O)} (hy : y ∈ IntPol O σ) :
    cth v n y ∈ IntPol O σ := by
  rw [mem_integral_poly_iff_coeff] at hy ⊢
  intro m
  obtain ⟨o, ho⟩ := hy m
  exact ⟨o * (((m v).choose n : ℕ) : O), by rw [coeff_cth, ho, map_mul, map_natCast]⟩

theorem intPol_mul {σ : Type} {x y : MvPolynomial σ (KK O)} (hx : x ∈ IntPol O σ) (hy : y ∈ IntPol O σ) :
    x * y ∈ IntPol O σ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by simp⟩

theorem intPol_X {σ : Type} (v : σ) : (X v : MvPolynomial σ (KK O)) ∈ IntPol O σ := ⟨X v, by simp⟩

theorem yjtZ_cth (D : Formalism.BasicNotions.D7) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) {thr thr' : Fin q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) (v : Fin N × Fin r)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) LL J thr) :
    cth v n y ∈ YjtZ O (r := r) LL J thr' := by
  classical
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  refine ⟨⟨?_, ?_⟩, intPol_cth v n hy3⟩
  · unfold chPol Formalism.MainNotions.G.Pol at hy1 ⊢
    rw [SetLike.mem_coe, mem_restrictSupport_iff] at hy1 ⊢
    intro m hm
    apply hy1
    rw [Finset.mem_coe, mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [coeff_cth, h0, zero_mul])
  · rw [SetLike.mem_coe, Submodule.mem_iInf] at hy2 ⊢
    intro k
    refine ycond_op D LL LL rfl (J k) n (hthr k) _ _ ?_ (hy2 k)
    by_cases hn : n = 0
    · subst hn; simp [vecDeg, covDeg]
    · simp only [vecDeg, covDeg, Finsupp.support_single_ne_zero _ hn, Finset.sum_singleton, Finsupp.single_eq_same]
      split_ifs with h1 h2 <;> first | omega | (exfalso; simp_all)

theorem yjtZ_X (D : Formalism.BasicNotions.D7) (LL LL' : ChainLetters N) (hv : LL'.vec = LL.vec) (a : Fin N) (c : Fin r)
    (hd : ∀ i, LL'.deg i = LL.deg i + if i = a then 1 else 0)
    {q : ℕ} (J : Fin q → ℕ) {thr thr' : Fin q → WithTop ℤ} (n : ℕ) (hn : LL.vec a = true → 1 ≤ n)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) LL J thr) :
    X (a, c) * y ∈ YjtZ O (r := r) LL' J thr' := by
  classical
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  refine ⟨⟨?_, ?_⟩, intPol_mul (intPol_X _) hy3⟩
  · unfold chPol Formalism.MainNotions.G.Pol at hy1 ⊢
    rw [SetLike.mem_coe, mem_restrictSupport_iff] at hy1 ⊢
    intro m hm
    rw [Finset.mem_coe, support_X_mul, Finset.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    have h0 := hy1 hm0
    intro i
    have h1 := h0 i
    simp only [multideg, addLeftEmbedding_apply, Finsupp.add_apply] at h1 ⊢
    rw [Finset.sum_add_distrib, h1, hd i, add_comm]
    congr 1
    by_cases hi : i = a
    · subst hi
      simp [Finsupp.single_apply]
    · have : ∀ x : Fin r, (Finsupp.single (a, c) 1 : Fin N × Fin r →₀ ℕ) (i, x) = 0 := by
        intro x
        rw [Finsupp.single_apply, if_neg]
        intro h
        exact hi (congrArg Prod.fst h).symm
      simp [this, hi]
  · rw [SetLike.mem_coe, Submodule.mem_iInf] at hy2 ⊢
    intro k
    have h := ycond_op D LL LL' hv (J k) n (hthr k) (Finsupp.single (a, c) 1) 0 ?_ (hy2 k)
    · rwa [divDer_zero] at h
    · simp only [vecDeg, covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
        Finsupp.single_eq_same, Finsupp.support_zero, Finset.sum_empty, add_zero]
      split_ifs with h1
      · exact hn h1.2
      · omega

end Y

end Formalism.MainNotions.ColumnSystems.Pf
