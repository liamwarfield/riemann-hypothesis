module

public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula
public import Development.WeilBound.CoreStatements.FlagImmersions.SumChooseLe

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.RestDegreePowerBound
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.AltEqZero
noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.M5

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def lower (a : Ψ → Fin N → ℕ) (τ : Ψ) (l : Fin N) (m : ℕ) : Ψ → Fin N → ℕ :=
  fun τ' c => if τ' = τ ∧ c = l then a τ' c - m else a τ' c

theorem alt_pk (a : Ψ → Fin N → ℕ) (τ : Ψ) (m : ℕ) (G : RP Ψ N) :
    alt a (pk τ m * G) = ∑ l, if m ≤ a τ l then alt (lower a τ l m) G else 0 := by
  have h1 : ∀ σ : Ψ → Equiv.Perm (Fin N), (pk τ m * G).coeff (expo a σ) =
      ∑ l, if m ≤ a τ l then G.coeff (expo (lower a τ l m) σ) else 0 := by
    intro σ
    rw [← Equiv.sum_comp (σ τ), pk, Finset.sum_mul, coeff_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [X_pow_eq_monomial, coeff_monomial_mul', one_mul]
    have e1 : (Finsupp.single (τ, i) m ≤ expo a σ) ↔ m ≤ a τ (σ τ i) := by
      rw [Finsupp.single_le_iff]; simp [expo]
    have e2 : expo a σ - Finsupp.single (τ, i) m = expo (lower a τ (σ τ i) m) σ := by
      ext ⟨t, b⟩
      simp only [expo, lower, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.equivFunOnFinite_symm_apply_apply,
        Finsupp.single_apply, Prod.mk.injEq]
      by_cases ht : t = τ
      · subst ht
        by_cases hb : b = i
        · subst hb; simp
        · have : ¬ i = b := fun h => hb h.symm
          simp [hb, this]
      · have : ¬ τ = t := fun h => ht h.symm
        simp [ht, this]
    rw [e2]
    by_cases h : m ≤ a τ (σ τ i)
    · rw [if_pos (e1.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e1.mp h')), if_neg h]
  simp only [alt, h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem alt_perm (a : Ψ → Fin N → ℕ) (π : Ψ → Equiv.Perm (Fin N)) (G : RP Ψ N) :
    alt a G = (∏ τ, ((Equiv.Perm.sign (π τ) : ℤ) : ℝ)) * alt (fun τ c => a τ (π τ c)) G := by
  unfold alt
  rw [← Equiv.sum_comp (Equiv.mulLeft π), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    simp

theorem alt_swap (a b : Ψ → Fin N → ℕ) (τ : Ψ) (p q : Fin N) (hpq : p ≠ q) (G : RP Ψ N)
    (h1 : ∀ c, b τ c = a τ (Equiv.swap p q c)) (h2 : ∀ t, t ≠ τ → b t = a t) :
    alt a G = - alt b G := by
  rw [alt_perm a (Function.update 1 τ (Equiv.swap p q)) G]
  have e : (fun t c => a t (Function.update (1 : Ψ → Equiv.Perm (Fin N)) τ (Equiv.swap p q) t c)) = b := by
    funext t c
    by_cases ht : t = τ
    · subst ht; simp [h1]
    · simp [ht, h2 t ht]
  rw [e, Finset.prod_eq_single τ]
  · simp [Equiv.Perm.sign_swap hpq]
  · intro t _ ht; simp [ht]
  · simp

theorem alt_eq_zero (a : Ψ → Fin N → ℕ) (τ : Ψ) (p q : Fin N) (hpq : p ≠ q) (h : a τ p = a τ q)
    (G : RP Ψ N) : alt a G = 0 := by
  have := alt_swap a a τ p q hpq G (fun c => by
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, h]
    · rw [h2, h]
    · rfl) (fun _ _ => rfl)
  linarith

theorem alt_pk_zero (a : Ψ → Fin N → ℕ) (τ : Ψ) (ha : ∀ c : Fin N, a τ c = N - 1 - (c : ℕ)) (m : ℕ) (hm : 1 ≤ m)
    (G : RP Ψ N) : alt a (pk τ m * G) = 0 := by
  rw [alt_pk]
  refine Finset.sum_eq_zero fun l _ => ?_
  split_ifs with h
  · rw [ha] at h
    have hl := l.isLt
    have hne : l ≠ ⟨l + m, by omega⟩ := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    refine alt_eq_zero _ τ l ⟨l + m, by omega⟩ hne ?_ G
    simp only [lower, true_and, if_true, if_neg hne.symm, ha]
    omega
  · rfl

theorem alt_rho_pk (τ : Ψ) (m : ℕ) (hm : 1 ≤ m) (G : RP Ψ N) : alt rho (pk τ m * G) = 0 :=
  alt_pk_zero rho τ (fun _ => rfl) m hm G

theorem col_sum (τ : Ψ) (k m : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hm : 1 ≤ m) (G : RP Ψ N) (l : Fin N) :
    (∑ c, if m ≤ bump τ c k τ l then alt (lower (bump τ c k) τ l m) G else 0) =
      if (l : ℕ) + m < N then 0 else if m = k then alt rho G else 0 := by
  have hl := l.isLt
  split_ifs with h1 h2
  · set l' : Fin N := ⟨l + m, h1⟩ with hl'
    have hv : (l' : ℕ) = l + m := rfl
    have hne : l ≠ l' := fun e => by
      have := congrArg Fin.val e; omega
    rw [Finset.sum_eq_add l l' hne]
    · rw [if_pos (by simp [bump]; omega), if_pos (by simp [bump]; omega)]
      rw [alt_swap (lower (bump τ l k) τ l m) (lower (bump τ l' k) τ l m) τ l l' hne G]
      · ring
      · intro c
        rw [Equiv.swap_apply_def]
        split_ifs with c1 c2
        · subst c1
          simp [lower, bump, hne, hne.symm]; omega
        · subst c2
          simp [lower, bump, hne, hne.symm]; omega
        · simp [lower, bump, c1, c2]
      · intro t ht
        funext c
        simp [lower, bump, ht]
    · intro c _ hc
      split_ifs with h
      · refine alt_eq_zero _ τ l l' hne ?_ G
        simp [lower, bump, hne.symm, hc.1.symm, hc.2.symm]; omega
      · rfl
    · simp
    · simp
  · subst h2
    rw [Finset.sum_eq_single l]
    · rw [if_pos (by simp [bump])]
      congr 1
      funext t c
      simp only [lower, bump, rho]
      split_ifs <;> omega
    · intro c _ hc
      rw [if_neg]
      simp [bump, hc.symm]; omega
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with h
    · by_cases hc : l = c
      · subst hc
        simp only [bump, true_and, if_true] at h
        set q : Fin N := ⟨N - 1 - (N - 1 - l + k - m), by omega⟩ with hq
        have hv : (q : ℕ) = N - 1 - (N - 1 - l + k - m) := rfl
        have hne : l ≠ q := fun e => by
          have := congrArg Fin.val e; omega
        refine alt_eq_zero _ τ l q hne ?_ G
        simp only [lower, bump, true_and, if_true, if_neg hne.symm]
        omega
      · exfalso
        simp [bump, hc] at h; omega
    · rfl

theorem lam_pk (τ τ' : Ψ) (k m : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N) (G : RP Ψ N) :
    lam τ k (pk τ' m * G) = if τ' = τ ∧ m = k then (k : ℝ) * alt rho G else 0 := by
  by_cases ht : τ' = τ
  · subst ht
    simp only [lam, alt_pk, true_and]
    rw [Finset.sum_comm]
    simp only [col_sum τ' k m hk hkN hm G]
    by_cases h : m = k
    · subst h
      simp only [if_true]
      rw [Fin.sum_univ_eq_sum_range (fun l => if l + m < N then 0 else alt rho G) N, Finset.sum_ite,
        Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
      have : (Finset.range N).filter (fun l => ¬ l + m < N) = Finset.Ico (N - m) N := by
        ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [this, Nat.card_Ico]
      congr 2; omega
    · simp [h]
  · rw [if_neg (fun h => ht h.1)]
    refine Finset.sum_eq_zero fun c _ => alt_pk_zero _ τ' (fun c' => ?_) m hm G
    simp [bump, ht]

end RootFieldNumerics.M5
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.CoeffShift
noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.M5

theorem coeff_lin {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (a : ι →₀ ℕ) (n : ℕ) (h : ∑ x, a x = n) :
    AddMonoidAlgebra.coeff ((∑ x, w x • (X x : MvPolynomial ι ℝ)) ^ n) a =
      (n.factorial : ℝ) * ∏ x, (((a x).factorial : ℝ)⁻¹ * w x ^ a x) := by
  rw [MvPolynomial.coeff_linearCombination_X_pow_of_fintype,
    Finsupp.sum_fintype a (fun _ m => m) (fun _ => rfl)]
  rw [if_pos h, Finsupp.prod_fintype a (fun r m => w r ^ m) (fun _ => pow_zero _),
    ← Finsupp.multinomial_of_support_subset (Finset.subset_univ _),
    Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hpos : (∏ x, ((a x).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hspec : (∏ x, ((a x).factorial : ℝ)) * (Nat.multinomial Finset.univ a : ℝ) =
      (n.factorial : ℝ) := by
    rw [← h]
    exact_mod_cast Nat.multinomial_spec Finset.univ a
  rw [← hspec]
  generalize (∏ x, ((a x).factorial : ℝ)) = F at hpos ⊢
  generalize (Nat.multinomial Finset.univ a : ℝ) = M
  generalize (∏ x, w x ^ a x) = P
  calc M * P = (F * F⁻¹) * (M * P) := by rw [mul_inv_cancel₀ hpos, one_mul]
    _ = F * M * (F⁻¹ * P) := by ring

theorem coeff_shift {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (x0 : ι) (s n : ℕ) (a : ι →₀ ℕ)
    (h : ∑ x, a x = n + s) :
    AddMonoidAlgebra.coeff (X x0 ^ s * (∑ x, (-w x) • (X x : MvPolynomial ι ℝ)) ^ n) a =
      (-1) ^ n * (n.factorial : ℝ) * (s.factorial : ℝ) *
        (∏ x, (Polynomial.C (((a x).factorial : ℝ)⁻¹) *
          (Polynomial.C (w x) + if x = x0 then Polynomial.X else 0) ^ a x)).coeff s := by
  have hrhs : (∏ x, (Polynomial.C (((a x).factorial : ℝ)⁻¹) *
      (Polynomial.C (w x) + if x = x0 then Polynomial.X else 0) ^ a x)).coeff s =
      (∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x)) *
        (((a x0).factorial : ℝ)⁻¹ * (w x0 ^ (a x0 - s) * ((a x0).choose s : ℝ))) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x0)]
    have hrest : ∏ x ∈ Finset.univ.erase x0, (Polynomial.C (((a x).factorial : ℝ)⁻¹) *
        (Polynomial.C (w x) + if x = x0 then Polynomial.X else 0) ^ a x) =
        Polynomial.C (∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [if_neg (Finset.ne_of_mem_erase hx), add_zero, map_mul, map_pow]
    rw [hrest, Polynomial.coeff_mul_C, if_pos (rfl : x0 = x0), add_comm, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_add_C_pow]
    ring
  rw [hrhs, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul']
  by_cases hs : s ≤ a x0
  · rw [if_pos (Finsupp.single_le_iff.mpr hs), one_mul]
    have e4 : (a - Finsupp.single x0 s) x0 = a x0 - s := by
      rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
    have e3 : ∀ x ∈ Finset.univ.erase x0, (a - Finsupp.single x0 s) x = a x := by
      intro x hx
      rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
        if_neg (Finset.ne_of_mem_erase hx).symm, tsub_zero]
    have e1 := Finset.add_sum_erase Finset.univ (fun x => a x) (Finset.mem_univ x0)
    have e2 := Finset.add_sum_erase Finset.univ (fun x => (a - Finsupp.single x0 s) x)
      (Finset.mem_univ x0)
    have e3' : ∑ x ∈ Finset.univ.erase x0, (a - Finsupp.single x0 s) x =
        ∑ x ∈ Finset.univ.erase x0, a x := Finset.sum_congr rfl e3
    rw [e4, e3'] at e2
    have hsum : ∑ x, (a - Finsupp.single x0 s) x = n := by omega
    rw [RootFieldNumerics.M5.coeff_lin (fun x => -w x) _ n hsum,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ x0), e4]
    have hrest : ∏ x ∈ Finset.univ.erase x0,
        ((((a - Finsupp.single x0 s) x).factorial : ℝ)⁻¹ * (-w x) ^ (a - Finsupp.single x0 s) x) =
        (-1) ^ (∑ x ∈ Finset.univ.erase x0, a x) *
          ∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [e3 x hx, neg_pow (w x)]
      ring
    rw [hrest]
    have hsign : ((-1 : ℝ)) ^ n = (-1) ^ (a x0 - s) * (-1) ^ (∑ x ∈ Finset.univ.erase x0, a x) := by
      rw [← pow_add]
      congr 1
      omega
    have hfac : (s.factorial : ℝ) * (((a x0).factorial : ℝ)⁻¹ * ((a x0).choose s : ℝ)) =
        ((a x0 - s).factorial : ℝ)⁻¹ := by
      have hA : ((a x0).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hB : (s.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hD : ((a x0 - s).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [Nat.cast_choose ℝ hs]
      field_simp <;> ring
    rw [hsign, neg_pow (w x0)]
    linear_combination (-((-1 : ℝ) ^ (a x0 - s) * (-1) ^ (∑ x ∈ Finset.univ.erase x0, a x) *
      (n.factorial : ℝ) * (∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x)) *
      w x0 ^ (a x0 - s))) * hfac
  · rw [if_neg fun h' => hs (Finsupp.single_le_iff.mp h'), Nat.choose_eq_zero_of_lt (not_le.mp hs)]
    simp

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def vv (u : Wt Ψ N) (x0 : Ψ × Fin N) (τ : Ψ) (b : Fin N) : Polynomial ℝ :=
  Polynomial.C (u τ b) + if (τ, b) = x0 then Polynomial.X else 0

theorem linRoot_eq (u : Wt Ψ N) : linRoot u = ∑ x : Ψ × Fin N, (-u x.1 x.2) • (X x : RP Ψ N) := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.linRoot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_neg, neg_mul]

theorem alt_pow (a : Ψ → Fin N → ℕ) (u : Wt Ψ N) (x0 : Ψ × Fin N) (s n : ℕ) (h : ∑ τ, ∑ c, a τ c = n + s) :
    alt a (X x0 ^ s * linRoot u ^ n) =
      (-1) ^ n * (n.factorial : ℝ) * (s.factorial : ℝ) * (∏ τ, gdet (a τ) (vv u x0 τ)).coeff s := by
  have hdet : ∀ τ, RootFieldNumerics.M5.gdet (a τ) (RootFieldNumerics.M5.vv u x0 τ) =
      ∑ π : Equiv.Perm (Fin N), Polynomial.C ((Equiv.Perm.sign π : ℤ) : ℝ) *
        ∏ c, (Polynomial.C (((a τ (π c)).factorial : ℝ)⁻¹) *
          RootFieldNumerics.M5.vv u x0 τ c ^ a τ (π c)) := by
    intro τ
    unfold RootFieldNumerics.M5.gdet
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [Matrix.of_apply, map_intCast]
  have hsum : ∀ σ : Ψ → Equiv.Perm (Fin N), ∑ x : Ψ × Fin N, RootFieldNumerics.M5.expo a σ x = n + s := by
    intro σ
    rw [← h, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [RootFieldNumerics.M5.expo, Finsupp.equivFunOnFinite_symm_apply_apply]
    exact Equiv.sum_comp (σ τ) (a τ)
  have hq : ∀ σ : Ψ → Equiv.Perm (Fin N),
      (∏ x : Ψ × Fin N, Polynomial.C (((RootFieldNumerics.M5.expo a σ x).factorial : ℝ)⁻¹) *
        (Polynomial.C (u x.1 x.2) + if x = x0 then Polynomial.X else 0) ^ RootFieldNumerics.M5.expo a σ x) =
      ∏ τ, ∏ c, (Polynomial.C (((a τ (σ τ c)).factorial : ℝ)⁻¹) *
        RootFieldNumerics.M5.vv u x0 τ c ^ a τ (σ τ c)) := by
    intro σ
    rw [Fintype.prod_prod_type]
    simp only [RootFieldNumerics.M5.expo, Finsupp.equivFunOnFinite_symm_apply_apply,
      RootFieldNumerics.M5.vv]
  rw [RootFieldNumerics.M5.linRoot_eq]
  unfold RootFieldNumerics.M5.alt
  simp only [hdet]
  rw [Fintype.prod_sum, Polynomial.finsetSum_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [RootFieldNumerics.M5.coeff_shift (fun x : Ψ × Fin N => u x.1 x.2) x0 s n
      (RootFieldNumerics.M5.expo a σ) (hsum σ), hq σ, Finset.prod_mul_distrib,
    show (∏ τ, Polynomial.C ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) =
      Polynomial.C (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) from (map_prod Polynomial.C _ _).symm,
    Polynomial.coeff_C_mul]
  ring

theorem sum_rho : ∑ τ : Ψ, ∑ c : Fin N, rho τ c = dimFl Ψ N := by
  have hinner : ∀ τ : Ψ, ∑ c : Fin N, RootFieldNumerics.M5.rho τ c = N * (N - 1) / 2 := by
    intro τ
    simp only [RootFieldNumerics.M5.rho]
    rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N,
      Finset.sum_range_reflect (fun i => i) N, Finset.sum_range_id]
  unfold GlobalTheory.CompanionTheory.Ar.Top.dimFl
  rw [Finset.sum_congr rfl fun τ _ => hinner τ, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem sum_bump (τ : Ψ) (c : Fin N) (k : ℕ) : ∑ τ' : Ψ, ∑ c' : Fin N, bump τ c k τ' c' = dimFl Ψ N + k := by
  have hsplit : ∀ τ' c', RootFieldNumerics.M5.bump τ c k τ' c' =
      RootFieldNumerics.M5.rho τ' c' + if τ' = τ ∧ c' = c then k else 0 := fun _ _ => rfl
  simp only [hsplit, Finset.sum_add_distrib, RootFieldNumerics.M5.sum_rho, add_right_inj]
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp),
    Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
  simp

end RootFieldNumerics.M5
end
end

noncomputable section

namespace RootFieldNumerics.M5

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem maj_lin (r e c A : ℝ) (hA : 0 ≤ A) (hr : |r| ≤ c) (he : |e| ≤ c * A) :
    Maj (Polynomial.C r + Polynomial.C e * Polynomial.X) c A := by
  have hc : 0 ≤ c := (abs_nonneg r).trans hr
  intro s
  rcases s with _ | _ | s
  · simpa using hr
  · simpa using he
  · have : (Polynomial.C r + Polynomial.C e * Polynomial.X).coeff (s + 1 + 1) = 0 := by
      simp [Polynomial.coeff_X, Polynomial.coeff_C]
    rw [this, abs_zero]
    positivity

theorem maj_C (r : ℝ) : Maj (Polynomial.C r) |r| 0 := by
  simpa using maj_lin r 0 |r| 0 le_rfl le_rfl (by simp)

theorem maj_rho (u : Wt Ψ N) (τ' : Ψ) (i : Fin N) (g : ℝ) (hg : 0 < g)
    (hsep : ∀ b, i ≠ b → g ≤ |u τ' i - u τ' b|) :
    Maj (∏ τ, gdet (rho τ) (vv u (τ', i) τ)) |(∏ τ, gdet (rho τ) (vv u (τ', i) τ)).coeff 0| (N / g) := by
  obtain ⟨c, hc⟩ := gdet_rho N
  have hP : (∏ τ, gdet (rho τ) (vv u (τ', i) τ)) =
      ∏ τ, (Polynomial.C c * ∏ a, ∏ b ∈ Finset.Ioi a, (vv u (τ', i) τ b - vv u (τ', i) τ a)) :=
    Finset.prod_congr rfl fun τ _ => hc _
  have h0 : |(∏ τ, gdet (rho τ) (vv u (τ', i) τ)).coeff 0| =
      ∏ τ, (|c| * ∏ a, ∏ b ∈ Finset.Ioi a, |u τ b - u τ a|) := by
    rw [hP, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod, Finset.abs_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul, Polynomial.eval_prod, Finset.abs_prod]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Polynomial.eval_prod, Finset.abs_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    congr 1
    simp only [vv, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_C]
    split_ifs <;> simp
  let w : Ψ → Fin N → ℝ := fun τ a => if (τ, a) = (τ', i) then 1 / g else 0
  have hw : ∀ τ a, 0 ≤ w τ a := fun τ a => by
    simp only [w]; split_ifs <;> positivity
  have hfac : ∀ τ a, ∀ b ∈ Finset.Ioi a,
      Maj (vv u (τ', i) τ b - vv u (τ', i) τ a) |u τ b - u τ a| (w τ a + w τ b) := by
    intro τ a b hb
    have hab : a < b := Finset.mem_Ioi.mp hb
    have hA := add_nonneg (hw τ a) (hw τ b)
    by_cases ha : (τ, a) = (τ', i)
    · have hb' : (τ, b) ≠ (τ', i) := fun h => hab.ne (by rw [← h] at ha; exact (Prod.mk.inj ha).2)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
      have : vv u (τ, a) τ b - vv u (τ, a) τ a =
          Polynomial.C (u τ b - u τ a) + Polynomial.C (-1) * Polynomial.X := by
        simp only [vv, if_neg hb', if_true, map_sub, map_neg, map_one]; ring
      rw [this]
      refine maj_lin _ _ _ _ hA le_rfl ?_
      have h1 := hsep b hab.ne
      simp only [w, if_neg hb', if_true, add_zero, abs_neg, abs_one]
      rw [abs_sub_comm, mul_one_div, one_le_div hg]
      exact h1
    · by_cases hb' : (τ, b) = (τ', i)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hb'
        have : vv u (τ, b) τ b - vv u (τ, b) τ a =
            Polynomial.C (u τ b - u τ a) + Polynomial.C 1 * Polynomial.X := by
          simp only [vv, if_neg ha, if_true, map_sub, map_one]; ring
        rw [this]
        refine maj_lin _ _ _ _ hA le_rfl ?_
        have h1 := hsep a hab.ne'
        simp only [w, if_neg ha, if_true, zero_add, abs_one]
        rw [mul_one_div, one_le_div hg]
        exact h1
      · have : vv u (τ', i) τ b - vv u (τ', i) τ a =
            Polynomial.C (u τ b - u τ a) + Polynomial.C 0 * Polynomial.X := by
          simp only [vv, if_neg ha, if_neg hb', map_sub, map_zero]; ring
        rw [this]
        refine maj_lin _ _ _ _ hA le_rfl ?_
        rw [abs_zero]
        exact mul_nonneg (abs_nonneg _) hA
  have hin : ∀ τ a, 0 ≤ ∑ b ∈ Finset.Ioi a, (w τ a + w τ b) := fun τ a =>
    Finset.sum_nonneg fun b _ => add_nonneg (hw τ a) (hw τ b)
  have hM := Maj.prod Finset.univ
    (fun τ => Polynomial.C c * ∏ a, ∏ b ∈ Finset.Ioi a, (vv u (τ', i) τ b - vv u (τ', i) τ a))
    (fun τ => |c| * ∏ a, ∏ b ∈ Finset.Ioi a, |u τ b - u τ a|)
    (fun τ => 0 + ∑ a, ∑ b ∈ Finset.Ioi a, (w τ a + w τ b))
    (fun τ _ => Maj.mul (maj_C c)
      (Maj.prod Finset.univ _ _ _
        (fun a _ => Maj.prod (Finset.Ioi a) _ _ _ (hfac τ a) (fun b _ => add_nonneg (hw τ a) (hw τ b)))
        (fun a _ => hin τ a)) le_rfl (Finset.sum_nonneg fun a _ => hin τ a))
    (fun τ _ => by rw [zero_add]; exact Finset.sum_nonneg fun a _ => hin τ a)
  rw [h0, hP]
  refine hM.mono (Finset.sum_nonneg fun τ _ => by
    rw [zero_add]; exact Finset.sum_nonneg fun a _ => hin τ a) le_rfl ?_
  rw [Finset.sum_eq_single τ' (fun τ _ hτ => by simp [w, hτ]) (by simp), zero_add]
  have hw' : ∀ a, w τ' a = if a = i then 1 / g else 0 := fun a => by simp [w]
  simp only [hw', Finset.sum_add_distrib]
  have e1 : ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, (if a = i then 1 / g else 0) = ((Finset.Ioi i).card : ℝ) * (1 / g) := by
    rw [Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have e2 : ∑ a : Fin N, ∑ b ∈ Finset.Ioi a, (if b = i then 1 / g else 0) = ((Finset.Iio i).card : ℝ) * (1 / g) := by
    simp only [Finset.sum_ite_eq', Finset.mem_Ioi]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 2
    congr 1
    ext a
    simp
  rw [e1, e2, ← add_mul, mul_one_div]
  refine div_le_div_of_nonneg_right ?_ hg.le
  rw [Fin.card_Ioi, Fin.card_Iio]
  have := i.2
  exact_mod_cast (by omega : N - 1 - (i : ℕ) + (i : ℕ) ≤ N)

theorem flagDeg_coeff (u : Wt Ψ N) (x0 : Ψ × Fin N) :
    flagDeg u = ((dimFl Ψ N).factorial : ℝ) * (∏ τ, gdet (rho τ) (vv u x0 τ)).coeff 0 := by
  have h := alt_pow (rho : Ψ → Fin N → ℕ) u x0 0 (dimFl Ψ N) (by rw [sum_rho]; rfl)
  rw [pow_zero, one_mul] at h
  rw [flagDeg, degFl_eq, h]
  have h1 : ((-1 : ℝ) ^ dimFl Ψ N) * (-1) ^ dimFl Ψ N = 1 := by
    rw [← mul_pow]; norm_num
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one]
  linear_combination (((dimFl Ψ N).factorial : ℝ) * (∏ τ, gdet (rho τ) (vv u x0 τ)).coeff 0) * h1

theorem lam_bound (u : Wt Ψ N) (τ τ' : Ψ) (i : Fin N) (g U : ℝ) (hg : 0 < g) (hU : 0 < U)
    (hsep : ∀ b, i ≠ b → g ≤ |u τ' i - u τ' b|) (hu : ∀ b, |u τ b| ≤ U) (k : ℕ) (hk : 1 ≤ k) :
    |lam τ k (X (τ', i) ^ (k - 1) * linRoot u ^ (dimFl Ψ N + 1))| ≤
      ((dimFl Ψ N : ℝ) + 1) * |flagDeg u| * (2 ^ (k - 1) / (k.factorial : ℝ) * U * (k + N * U / g) ^ (k - 1)) := by
  have hv : ∀ b, Maj (vv u (τ', i) τ b) U (1 / U) := by
    intro b
    by_cases h : (τ, b) = (τ', i)
    · have : vv u (τ', i) τ b = Polynomial.C (u τ b) + Polynomial.C 1 * Polynomial.X := by simp [vv, h]
      rw [this]
      exact maj_lin _ _ _ _ (by positivity) (hu b) (by rw [mul_one_div_cancel hU.ne', abs_one])
    · have : vv u (τ', i) τ b = Polynomial.C (u τ b) + Polynomial.C 0 * Polynomial.X := by
        simp only [vv, if_neg h, map_zero, zero_mul]
      rw [this]
      exact maj_lin _ _ _ _ (by positivity) (hu b) (by rw [abs_zero]; positivity)
  obtain ⟨r, hr, hre⟩ := gdet_bump k hk U hU (vv u (τ', i) τ) hv
  have hsum : ∑ c, ∏ τ'', gdet (bump τ c k τ'') (vv u (τ', i) τ'') =
      r * ∏ τ'', gdet (rho τ'') (vv u (τ', i) τ'') := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ← mul_assoc]
    have hre' : ∑ c, gdet (bump τ c k τ) (vv u (τ', i) τ) = r * gdet (rho τ) (vv u (τ', i) τ) := by
      refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) hre
      congr 1
      funext c'
      simp [bump]
    rw [← hre', Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
    congr 1
    refine Finset.prod_congr rfl fun τ'' h => ?_
    congr 1
    funext c'
    simp [bump, rho, Finset.ne_of_mem_erase h]
  have hl : lam τ k (X (τ', i) ^ (k - 1) * linRoot u ^ (dimFl Ψ N + 1)) =
      (-1) ^ (dimFl Ψ N + 1) * ((dimFl Ψ N + 1).factorial : ℝ) * ((k - 1).factorial : ℝ) *
        (r * ∏ τ'', gdet (rho τ'') (vv u (τ', i) τ'')).coeff (k - 1) := by
    rw [← hsum, Polynomial.finsetSum_coeff, Finset.mul_sum, lam]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact alt_pow _ _ _ _ _ (by rw [sum_bump]; omega)
  have hM := (hr.mul (maj_rho u τ' i g hg hsep) (by positivity) (by positivity)) (k - 1)
  have hF : |flagDeg u| = ((dimFl Ψ N).factorial : ℝ) * |(∏ τ, gdet (rho τ) (vv u (τ', i) τ)).coeff 0| := by
    rw [flagDeg_coeff u (τ', i), abs_mul, Nat.abs_cast]
  rw [hl, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, Nat.abs_cast, hF]
  refine (mul_le_mul_of_nonneg_left hM (by positivity)).trans (le_of_eq ?_)
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 1 := ⟨k - 1, by omega⟩
  have h2 : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : ((s + 1 : ℕ) : ℝ) + N * U / g = U * (((s + 1 : ℕ) : ℝ) / U + N / g) := by field_simp
  rw [h3, mul_pow, Nat.factorial_succ (dimFl Ψ N), Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

theorem lam_decomp {F : RP Ψ N} {Q : Ψ → ℕ → RP Ψ N} (hQ : IsDecomp F Q) (τ : Ψ) (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N)
    (γ : RP Ψ N) : lam τ k (γ * F) = k * alt rho (γ * Q τ k) := by
  rw [hQ.2, Finset.mul_sum, lam_sum]
  simp only [Finset.mul_sum, lam_sum]
  have : ∀ τ', ∀ m ∈ Finset.Icc 1 N, lam τ k (γ * (pk τ' m * Q τ' m)) =
      if τ' = τ ∧ m = k then (k : ℝ) * alt rho (γ * Q τ' m) else 0 := by
    intro τ' m hm
    rw [mul_left_comm]
    exact lam_pk τ τ' k m hk hkN (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2 _
  rw [Finset.sum_congr rfl fun τ' _ => Finset.sum_congr rfl (this τ'),
    Finset.sum_eq_single τ (fun τ' _ h => by simp [h]) (by simp),
    Finset.sum_eq_single k (fun m _ h => by simp [h]) (fun h => absurd (Finset.mem_Icc.mpr ⟨hk, hkN⟩) h)]
  simp

theorem lam_shift (u : Wt Ψ N) (τ : Ψ) (a : ℝ) (k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) (γ : RP Ψ N) (n : ℕ) :
    lam τ k (γ * linRoot (fun σ b => u σ b - if σ = τ then a else 0) ^ n) = lam τ k (γ * linRoot u ^ n) := by
  have h : linRoot (fun σ b => u σ b - if σ = τ then a else 0) - linRoot u = pk τ 1 * C a := by
    simp only [linRoot, pk, pow_one, map_sub, sub_mul, Finset.sum_sub_distrib]
    have : ∑ x : Ψ × Fin N, (C (if x.1 = τ then a else 0) * X x : RP Ψ N) = (∑ i : Fin N, X (τ, i)) * C a := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun σ _ h => by simp [h]) (by simp), Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_comm]
    rw [this]; ring
  obtain ⟨G, hG⟩ := sub_dvd_pow_sub_pow (linRoot (fun σ b => u σ b - if σ = τ then a else 0)) (linRoot u) n
  rw [h, sub_eq_iff_eq_add] at hG
  rw [hG, mul_add, lam_add, show γ * (pk τ 1 * C a * G) = pk τ 1 * (γ * C a * G) by ring,
    lam_pk τ τ k 1 (by omega) hkN le_rfl (by omega), if_neg (by omega), zero_add]

theorem one_bound (j : ℕ) (u : Wt Ψ N) (g : ℝ) (Q : Ψ → ℕ → RP Ψ N) (hW : WeightHyp j u g)
    (hQ : IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q) (τ τ' : Ψ) (k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) (i : Fin N)
    (hi : InSmall j i) :
    |k * alt rho (X (τ', i) ^ (k - 1) * Q τ k)| ≤ ((dimFl Ψ N : ℝ) + 1) * flagDeg u *
      ((2 ^ (k - 1) / (k.factorial : ℝ)) * ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
  obtain ⟨hg, hreg, -, hsep⟩ := hW
  haveI : Nonempty (Fin N) := ⟨i⟩
  have hle : ∀ b, u τ b ≤ ⨆ i, u τ i := fun b => le_ciSup (Set.finite_range _).bddAbove b
  have hge : ∀ b, (⨅ i, u τ i) ≤ u τ b := fun b => ciInf_le (Set.finite_range _).bddBelow b
  have hn : ∀ b, |u τ b| ≤ ‖u‖ := fun b =>
    (norm_le_pi_norm (u τ) b).trans (norm_le_pi_norm u τ)
  have hs : (⨆ i, u τ i) ≤ ‖u‖ := ciSup_le fun b => (abs_le.mp (hn b)).2
  have hI : -‖u‖ ≤ ⨅ i, u τ i := le_ciInf fun b => (abs_le.mp (hn b)).1
  set U := (⨆ i, u τ i) - ⨅ i, u τ i with hUd
  have hU : 0 < U := by
    have := hreg τ ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
    have h1 := hle ⟨0, by omega⟩
    have h2 := hge ⟨1, by omega⟩
    linarith
  have hpos : 0 < flagDeg u := (GlobalTheory.T.flag_degree_weight_formula Ψ N u).2.1 hreg
  have hfl : flagDeg (fun σ b => u σ b - if σ = τ then ⨅ i, u τ i else 0) = flagDeg u := by
    rw [(GlobalTheory.T.flag_degree_weight_formula Ψ N u).1, (GlobalTheory.T.flag_degree_weight_formula Ψ N _).1]
    simp only [sub_sub_sub_cancel_right]
  have hb := lam_bound (fun σ b => u σ b - if σ = τ then ⨅ i, u τ i else 0) τ τ' i g U hg hU
    (fun b hb => by rw [sub_sub_sub_cancel_right]; exact hsep τ' i b hi hb)
    (fun b => by
      rw [if_pos rfl, abs_of_nonneg (sub_nonneg.mpr (hge b))]
      linarith [hle b]) k (by omega)
  rw [lam_shift u τ _ k hk hkN, lam_decomp hQ τ k (by omega) hkN, hfl, abs_of_pos hpos] at hb
  refine hb.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity)) (by positivity))
  have h1 : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have h2 : U / g ≤ 2 * (‖u‖ / g) := by
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hg.le
  have h3 : (N : ℝ) * (U / g) ≤ N * (2 * (‖u‖ / g)) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  rw [mul_div_assoc]
  linarith

theorem small_block (j : ℕ) (hj : j < N) (σ : Ψ ⊕ Ψ) (m : ℕ) (hm : 1 ≤ m) (G : RP Ψ N) :
    ∃ (τ' : Ψ) (I : Finset (Fin N)), I.card = min j (N - j) ∧ (∀ i ∈ I, InSmall j i) ∧
      |alt rho (pLie j m σ * G)| = |∑ i ∈ I, alt rho (X (τ', i) ^ m * G)| := by
  have cL : (Finset.univ.filter fun i : Fin N => (i : ℕ) < j).card = j := by
    rw [Fin.card_filter_val_lt]; omega
  have cH : (Finset.univ.filter fun i : Fin N => j ≤ (i : ℕ)).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)
    simp only [not_lt, cL, Finset.card_univ, Fintype.card_fin] at this
    omega
  have key : ∀ τ' : Ψ, |∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), alt rho (X (τ', i) ^ m * G)| =
      |∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), alt rho (X (τ', i) ^ m * G)| := by
    intro τ'
    have h := alt_rho_pk τ' m hm G
    rw [pk, Finset.sum_mul, alt_sum,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j)] at h
    simp only [not_lt] at h
    rw [eq_neg_of_add_eq_zero_left h, abs_neg]
  have base : ∃ τ' : Ψ, |alt rho (pLie j m σ * G)| =
      |∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), alt rho (X (τ', i) ^ m * G)| := by
    rcases σ with τ' | τ'
    · exact ⟨τ', by rw [pLie, pkLow, Finset.sum_mul, alt_sum]⟩
    · refine ⟨τ', ?_⟩
      rw [key, pLie, Finset.sum_mul, alt_sum,
        Finset.sum_congr rfl (g := fun i => (-1 : ℝ) ^ m * alt rho (X (τ', i) ^ m * G)) (fun i _ => by
          rw [← alt_C_mul, neg_pow, mul_assoc]; simp),
        ← Finset.mul_sum, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  obtain ⟨τ', h⟩ := base
  by_cases hc : j ≤ N - j
  · exact ⟨τ', _, by rw [cL, min_eq_left hc], fun i hi => by
      rw [InSmall, if_pos hc]; exact (Finset.mem_filter.mp hi).2, h⟩
  · exact ⟨τ', _, by rw [cH, min_eq_right (not_le.mp hc).le], fun i hi => by
      rw [InSmall, if_neg hc]; exact (Finset.mem_filter.mp hi).2, h.trans (key τ')⟩

end RootFieldNumerics.M5

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LieTermFlagBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem kappa_bound_of_decomp : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (u : Wt Ψ N) (g : ℝ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → ∀ (τ : Ψ) (σ : Ψ ⊕ Ψ) (k : ℕ), 2 ≤ k → k ≤ N → |k * degFl (pLie j (k - 1) σ * Q τ k)| ≤ ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) * ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
  intro Ψ _ _ N j u g Q _ hjN hW hD τ σ k hk2 hkN
  obtain ⟨τ', I, hcard, hsmall, heq⟩ :=
    RootFieldNumerics.M5.small_block j hjN σ (k - 1) (by omega) (Q τ k)
  have hbound : ∀ i ∈ I,
      |(k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| ≤
        ((dimFl Ψ N : ℝ) + 1) * flagDeg u *
          (2 ^ (k - 1) / (k.factorial : ℝ) * ((⨆ i, u τ i) - ⨅ i, u τ i) *
            (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) :=
    fun i hi => RootFieldNumerics.M5.one_bound j u g Q hW hD τ τ' k hk2 hkN i (hsmall i hi)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc |(k : ℝ) * degFl (pLie j (k - 1) σ * Q τ k)|
      = (k : ℝ) * |RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (pLie j (k - 1) σ * Q τ k)| := by
        rw [RootFieldNumerics.M5.degFl_eq, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg hk0]
    _ = (k : ℝ) * |∑ i ∈ I, RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| := by
        rw [heq]
    _ = |∑ i ∈ I, (k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| := by
        rw [← Finset.mul_sum, abs_mul, abs_of_nonneg hk0]
    _ ≤ ∑ i ∈ I, |(k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, ((dimFl Ψ N : ℝ) + 1) * flagDeg u *
          (2 ^ (k - 1) / (k.factorial : ℝ) * ((⨆ i, u τ i) - ⨅ i, u τ i) *
            (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) :=
        Finset.sum_le_sum hbound
    _ = ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) *
          ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LieTermFlagBoundStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_term_flag_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (u : Wt Ψ N) (g : ℝ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → ∀ (τ : Ψ) (σ : Ψ ⊕ Ψ) (k : ℕ), 2 ≤ k → k ≤ N → |k * degFl (pLie j (k - 1) σ * Q τ k)| ≤ ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) * ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.kappa_bound_of_decomp | exact GlobalTheory.CompanionTheory.Ar.Top.kappa_bound_of_decomp | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.kappa_bound_of_decomp <;> assumption)
end
