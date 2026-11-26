module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.MinkSat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SatDegLe

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UpSiegel
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PolyL2EqSqrtCoeffSum
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HupsTwCoeffCoeff
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UpMkApplyInl
namespace ReciprocityTheory.ChartRestriction.G.T0

noncomputable def upMk {D N : ℕ} (ab : (Fin (D + 2) →₀ ℕ) × (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ)) :
    UXVar D N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun p => ab.2 (some p)) (fun i => ab.1 i))

noncomputable def upMono (D N n n' : ℕ) : Finset (UXVar D N →₀ ℕ) :=
  ((Finset.univ : Finset (Fin (D + 2))).finsuppAntidiag n ×ˢ
    (Finset.univ : Finset (Option (Fin (D + 2) × Fin (N + 1)))).finsuppAntidiag n').image upMk

theorem upMk_apply_inl {D N : ℕ} (ab : (Fin (D + 2) →₀ ℕ) × (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ))
    (p : Fin (D + 2) × Fin (N + 1)) : upMk ab (Sum.inl p) = ab.2 (some p) := rfl

theorem upMk_apply_inr {D N : ℕ} (ab : (Fin (D + 2) →₀ ℕ) × (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ))
    (i : Fin (D + 2)) : upMk ab (Sum.inr i) = ab.1 i := rfl

theorem mem_upMono {D N n n' : ℕ} {s : UXVar D N →₀ ℕ} :
    s ∈ upMono D N n n' ↔ xDeg s = n ∧ uDeg s ≤ n' := by
  classical
  unfold upMono
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [Finset.mem_product, Finset.mem_finsuppAntidiag, Finset.mem_finsuppAntidiag] at hab
    obtain ⟨⟨ha, -⟩, ⟨hb, -⟩⟩ := hab
    try dsimp only at ha hb
    rw [Fintype.sum_option] at hb
    constructor
    · unfold xDeg
      simpa only [upMk_apply_inr] using ha
    · unfold uDeg
      simp only [upMk_apply_inl]
      omega
  · rintro ⟨hx, hu⟩
    refine ⟨(Finsupp.equivFunOnFinite.symm (fun i => s (Sum.inr i)),
      Finsupp.equivFunOnFinite.symm (fun o => Option.elim o (n' - uDeg s) (fun p => s (Sum.inl p)))), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_finsuppAntidiag, Finset.mem_finsuppAntidiag]
      refine ⟨⟨?_, Finset.subset_univ _⟩, ⟨?_, Finset.subset_univ _⟩⟩
      · simpa [xDeg] using hx
      · rw [Fintype.sum_option]
        simp only [Finsupp.coe_equivFunOnFinite_symm, Option.elim]
        unfold uDeg at hu ⊢
        omega
    · ext x
      cases x <;> simp [upMk]

theorem card_upMono (D N n n' : ℕ) : (upMono D N n n').card = cardUX D N n n' := by
  classical
  unfold upMono cardUX
  rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Finset.card_univ, Fintype.card_fin,
    Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · congr 1
    · rw [show D + 2 + n - 1 = n + (D + 1) by omega, Nat.choose_symm_add, Nat.add_assoc]
    · rw [show (D + 2) * (N + 1) + 1 + n' - 1 = n' + (D + 2) * (N + 1) by omega, Nat.choose_symm_add]
  · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_finsuppAntidiag] at hab hab'
    have h1 : ∀ i, a i = a' i := fun i => by
      have := congrArg (fun s => s (Sum.inr i)) h
      simpa [upMk] using this
    have h2 : ∀ p, b (some p) = b' (some p) := fun p => by
      have := congrArg (fun s => s (Sum.inl p)) h
      simpa [upMk] using this
    have hb := hab.2.1
    have hb' := hab'.2.1
    rw [Fintype.sum_option] at hb hb'
    have hs : ∑ p, b (some p) = ∑ p, b' (some p) := Finset.sum_congr rfl fun p _ => h2 p
    have h3 : b none = b' none := by omega
    refine Prod.ext (Finsupp.ext h1) (Finsupp.ext fun o => ?_)
    cases o
    · exact h3
    · exact h2 _

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0


open Polynomial in
noncomputable def hupsTw {σ R : Type*} [CommRing R] (w : σ → ℕ) :
    MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  MvPolynomial.aeval fun v => Polynomial.C (MvPolynomial.X v) * Polynomial.X ^ (w v)

def hupsWt {σ : Type*} (w : σ → ℕ) (s : σ →₀ ℕ) : ℕ := s.sum fun v k => k * w v

theorem hupsTw_monomial {σ R : Type*} [CommRing R] (w : σ → ℕ) (s : σ →₀ ℕ) (a : R) :
    hupsTw w (MvPolynomial.monomial s a) =
      Polynomial.C (MvPolynomial.monomial s a) * Polynomial.X ^ hupsWt w s := by
  rw [hupsTw, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, hupsWt, Finsupp.prod, Finsupp.sum, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]
  simp only [mul_comm (w _) _]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem hupsTw_eq {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R) :
    hupsTw w p = ∑ s ∈ p.support,
      Polynomial.C (MvPolynomial.monomial s (p.coeff s)) * Polynomial.X ^ hupsWt w s := by
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [hupsTw_monomial]

theorem hupsTw_coeff_coeff {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R)
    (j : ℕ) (s : σ →₀ ℕ) :
    ((hupsTw w p).coeff j).coeff s = if hupsWt w s = j then p.coeff s else 0 := by
  classical
  rw [hupsTw_eq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [MvPolynomial.coeff_sum]
  simp only [apply_ite (AddMonoidAlgebra.coeff · s), MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]
  rw [Finset.sum_eq_single s]
  · by_cases h : hupsWt w s = j
    · rw [if_pos h.symm, if_pos h, if_pos rfl]
    · simp [h, Ne.symm h]
  · intro t _ hts
    simp [hts, MvPolynomial.coeff_monomial]
  · intro hs
    rw [MvPolynomial.mem_support_iff, not_not] at hs
    simp [hs]

theorem hupsTw_ne_zero {σ R : Type*} [CommRing R] (w : σ → ℕ) {p : MvPolynomial σ R}
    {s : σ →₀ ℕ} (hs : s ∈ p.support) : (hupsTw w p).coeff (hupsWt w s) ≠ 0 := by
  intro h
  have e := hupsTw_coeff_coeff w p (hupsWt w s) s
  rw [h, MvPolynomial.coeff_zero, if_pos rfl] at e
  exact (MvPolynomial.mem_support_iff.mp hs) e.symm

theorem hupsTw_hom {σ R : Type*} [CommRing R] (w : σ → ℕ) {p : MvPolynomial σ R} {a : ℕ}
    (hp : ∀ s ∈ p.support, hupsWt w s = a) :
    hupsTw w p = Polynomial.C p * Polynomial.X ^ a := by
  ext j s
  rw [hupsTw_coeff_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases hs : s ∈ p.support
  · rw [hp s hs]
    by_cases hj : j = a
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  · rw [MvPolynomial.mem_support_iff, not_not] at hs
    split_ifs <;> simp [hs]

theorem hups_hom_of_mul {σ R : Type*} [CommRing R] [IsDomain R] (w : σ → ℕ)
    {F P : MvPolynomial σ R} (hF : F ≠ 0) {a n : ℕ} (hFa : ∀ s ∈ F.support, hupsWt w s = a)
    (hFP : ∀ s ∈ (F * P).support, hupsWt w s = n) {s0 : σ →₀ ℕ} (hs0 : s0 ∈ P.support) :
    hupsWt w s0 + a = n := by
  have h1 : hupsTw w (F * P) = Polynomial.C (F * P) * Polynomial.X ^ n := hupsTw_hom w hFP
  have h2 : hupsTw w F = Polynomial.C F * Polynomial.X ^ a := hupsTw_hom w hFa
  rw [map_mul, h2, map_mul] at h1
  have hCF : (Polynomial.C F : Polynomial (MvPolynomial σ R)) ≠ 0 := Polynomial.C_ne_zero.mpr hF
  have h3 : Polynomial.X ^ a * hupsTw w P = Polynomial.C P * Polynomial.X ^ n := by
    apply mul_left_cancel₀ hCF
    rw [← mul_assoc, ← mul_assoc]
    exact h1
  have h4 := congrArg (fun q => q.coeff (hupsWt w s0 + a)) h3
  simp only [Polynomial.coeff_X_pow_mul, Polynomial.coeff_C_mul_X_pow] at h4
  by_contra hne
  rw [if_neg hne] at h4
  exact hupsTw_ne_zero w hs0 h4

theorem hups_deg_of_mul {σ R : Type*} [CommRing R] [IsDomain R] (w : σ → ℕ)
    {F P : MvPolynomial σ R} {u n : ℕ} {sF : σ →₀ ℕ} (hsF : sF ∈ F.support)
    (hFu : hupsWt w sF = u)
    (hFP : ∀ s ∈ (F * P).support, hupsWt w s ≤ n) {s0 : σ →₀ ℕ} (hs0 : s0 ∈ P.support) :
    hupsWt w s0 + u ≤ n := by
  have hTF : (hupsTw w F).coeff u ≠ 0 := by
    rw [← hFu]
    exact hupsTw_ne_zero w hsF
  have hTP : (hupsTw w P).coeff (hupsWt w s0) ≠ 0 := hupsTw_ne_zero w hs0
  have hF0 : hupsTw w F ≠ 0 := fun h => hTF (by rw [h, Polynomial.coeff_zero])
  have hP0 : hupsTw w P ≠ 0 := fun h => hTP (by rw [h, Polynomial.coeff_zero])
  have hdeg : (hupsTw w (F * P)).natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    ext s
    rw [hupsTw_coeff_coeff, MvPolynomial.coeff_zero]
    split_ifs with h
    · by_contra hc
      have := hFP s (MvPolynomial.mem_support_iff.mpr hc)
      omega
    · rfl
  rw [map_mul, Polynomial.natDegree_mul hF0 hP0] at hdeg
  have h1 := Polynomial.le_natDegree_of_ne_zero hTF
  have h2 := Polynomial.le_natDegree_of_ne_zero hTP
  omega

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HupsChooseRatio
namespace ReciprocityTheory.ChartRestriction.G.T0

theorem hups_choose_ratio (n p : ℕ) (hp : p ≤ n) : ∀ a : ℕ,
    (((n + a).choose a : ℕ) : ℝ) * ((p : ℝ) + 1) ^ a ≤
      (((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have hA := Nat.add_one_mul_choose_eq (n + a) a
    have hB := Nat.add_one_mul_choose_eq (p + a) a
    have eA : n + (a + 1) = (n + a + 1) := by omega
    have eB : p + (a + 1) = (p + a + 1) := by omega
    rw [eA, eB]
    have hA' : (((n + a + 1).choose (a + 1) : ℕ) : ℝ) * ((a : ℝ) + 1) =
        ((n : ℝ) + a + 1) * (((n + a).choose a : ℕ) : ℝ) := by
      have := congrArg (fun t : ℕ => (t : ℝ)) hA
      simp only [Nat.cast_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at this
      linarith
    have hB' : (((p + a + 1).choose (a + 1) : ℕ) : ℝ) * ((a : ℝ) + 1) =
        ((p : ℝ) + a + 1) * (((p + a).choose a : ℕ) : ℝ) := by
      have := congrArg (fun t : ℕ => (t : ℝ)) hB
      simp only [Nat.cast_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at this
      linarith
    have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hpn : (p : ℝ) ≤ n := by exact_mod_cast hp
    have hkey : ((n : ℝ) + a + 1) * ((p : ℝ) + 1) ≤ ((p : ℝ) + a + 1) * ((n : ℝ) + 1) := by
      nlinarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]
    have hX : 0 ≤ (((n + a).choose a : ℕ) : ℝ) * ((p : ℝ) + 1) ^ a := by positivity
    have hY : 0 ≤ (((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a := by positivity
    rw [← mul_le_mul_iff_of_pos_right ha1]
    calc (((n + a + 1).choose (a + 1) : ℕ) : ℝ) * ((p : ℝ) + 1) ^ (a + 1) * ((a : ℝ) + 1)
        = (((n : ℝ) + a + 1) * ((p : ℝ) + 1)) *
            ((((n + a).choose a : ℕ) : ℝ) * ((p : ℝ) + 1) ^ a) := by
          rw [pow_succ]; linear_combination ((p : ℝ) + 1) ^ a * ((p : ℝ) + 1) * hA'
      _ ≤ (((p : ℝ) + a + 1) * ((n : ℝ) + 1)) *
            ((((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a) :=
          mul_le_mul hkey ih hX (by positivity)
      _ = (((p + a + 1).choose (a + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (a + 1) * ((a : ℝ) + 1) := by
          rw [pow_succ]; linear_combination -(((n : ℝ) + 1) ^ a * ((n : ℝ) + 1)) * hB'

theorem hups_pow_exp (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : (1 + x) ^ k ≤ Real.exp (k * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) k

theorem hups_choose_exp (n p a : ℕ) (hp : p ≤ n) :
    (((n + a).choose a : ℕ) : ℝ) ≤
      (((p + a).choose a : ℕ) : ℝ) * Real.exp (a * (((n - p : ℕ) : ℝ) / ((p : ℝ) + 1))) := by
  have h1 := hups_choose_ratio n p hp a
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hcast : (((n - p : ℕ) : ℝ)) = (n : ℝ) - p := by rw [Nat.cast_sub hp]
  have hx : 0 ≤ (((n - p : ℕ) : ℝ)) / ((p : ℝ) + 1) := by positivity
  have h2 := hups_pow_exp _ hx a
  have e : 1 + (((n - p : ℕ) : ℝ)) / ((p : ℝ) + 1) = ((n : ℝ) + 1) / ((p : ℝ) + 1) := by
    rw [hcast]; field_simp; ring
  rw [e, div_pow] at h2
  have hpa : (0 : ℝ) < ((p : ℝ) + 1) ^ a := by positivity
  have hB : (0 : ℝ) ≤ (((p + a).choose a : ℕ) : ℝ) := by positivity
  have h3 : (((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a / ((p : ℝ) + 1) ^ a ≤
      (((p + a).choose a : ℕ) : ℝ) * Real.exp (a * (((n - p : ℕ) : ℝ) / ((p : ℝ) + 1))) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h2 hB
  refine le_trans ?_ h3
  rw [le_div_iff₀ hpa]
  exact h1


set_option maxHeartbeats 1000000 in
theorem hups_ratio (D N n n' deF u del : ℕ) (h1 : 1 ≤ deF) (hdel : deF ≤ del)
    (hu : u ≤ (D + 1) * del) (hn : 8 * ((D + 2) * (N + 1)) ^ 2 * (D + 1) * del ≤ n)
    (hn' : n' = 8 * n * ((D + 2) * (N + 1)) * (D + 1) * del) :
    (n : ℝ) * cardUX D N n n' ≤ ((n : ℝ) + (D + 2) * deF) * cardUX D N (n - deF) (n' - u) := by
  have hdel1 : 1 ≤ del := le_trans h1 hdel
  have hM1 : D + 2 ≤ (D + 2) * (N + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos N)
  have hbig : del ≤ n := by
    have : 1 ≤ 8 * ((D + 2) * (N + 1)) ^ 2 * (D + 1) := Nat.succ_le_of_lt (by positivity)
    calc del = 1 * del := (one_mul _).symm
      _ ≤ 8 * ((D + 2) * (N + 1)) ^ 2 * (D + 1) * del := Nat.mul_le_mul_right _ this
      _ ≤ n := hn
  have haN : deF ≤ n := le_trans hdel hbig
  have huN : u ≤ n' := by
    have hn1 : 1 ≤ n := le_trans hdel1 hbig
    have : 1 ≤ 8 * n * ((D + 2) * (N + 1)) :=
      Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by positivity))
    rw [hn']
    calc u ≤ (D + 1) * del := hu
      _ = 1 * ((D + 1) * del) := (one_mul _).symm
      _ ≤ 8 * n * ((D + 2) * (N + 1)) * ((D + 1) * del) := Nat.mul_le_mul_right _ this
      _ = 8 * n * ((D + 2) * (N + 1)) * (D + 1) * del := by ring
  have hA := hups_choose_exp n (n - deF) (D + 1) (Nat.sub_le n deF)
  have hB := hups_choose_exp n' (n' - u) ((D + 2) * (N + 1)) (Nat.sub_le n' u)
  rw [Nat.sub_sub_self haN] at hA
  rw [Nat.sub_sub_self huN] at hB
  have hc1 : (cardUX D N n n' : ℝ) = (((n + (D + 1)).choose (D + 1) : ℕ) : ℝ) *
      (((n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) : ℝ) := by
    simp only [cardUX, Nat.cast_mul]
    rw [show n + D + 1 = n + (D + 1) by omega]
  have hc2 : (cardUX D N (n - deF) (n' - u) : ℝ) = (((n - deF + (D + 1)).choose (D + 1) : ℕ) : ℝ) *
      (((n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) : ℝ) := by
    simp only [cardUX, Nat.cast_mul]
    rw [show n - deF + D + 1 = n - deF + (D + 1) by omega]
  set K : ℝ := ((D + 1 : ℕ) : ℝ) with hK
  set Mr : ℝ := (((D + 2) * (N + 1) : ℕ) : ℝ) with hMr
  set a : ℝ := (deF : ℝ) with ha
  set nr : ℝ := (n : ℝ) with hnr
  set dl : ℝ := (del : ℝ) with hdl
  set ur : ℝ := (u : ℝ) with hur
  set n'r : ℝ := (n' : ℝ) with hn'r
  have hK1 : 1 ≤ K := by rw [hK]; exact_mod_cast Nat.le_add_left 1 D
  have hMK : K + 1 ≤ Mr := by
    rw [hK, hMr]; exact_mod_cast (show D + 1 + 1 ≤ (D + 2) * (N + 1) by omega)
  have ha1 : 1 ≤ a := by rw [ha]; exact_mod_cast h1
  have had : a ≤ dl := by rw [ha, hdl]; exact_mod_cast hdel
  have hud : ur ≤ K * dl := by rw [hur, hK, hdl]; exact_mod_cast hu
  have hnbig : 8 * Mr ^ 2 * K * dl ≤ nr := by
    rw [hnr, hMr, hK, hdl]; exact_mod_cast hn
  have hn'eq : n'r = 8 * nr * Mr * K * dl := by
    rw [hn'r, hnr, hMr, hK, hdl, hn']; push_cast; ring
  have hsub1 : (((n - deF : ℕ) : ℝ)) = nr - a := by rw [Nat.cast_sub haN]
  have hsub2 : (((n' - u : ℕ) : ℝ)) = n'r - ur := by rw [Nat.cast_sub huN]
  rw [hsub1] at hA
  rw [hsub2] at hB
  have hK0 : 0 ≤ K := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hdl1 : 1 ≤ dl := by linarith
  have hMr1 : 1 ≤ Mr := by linarith
  have hur0 : 0 ≤ ur := by rw [hur]; exact Nat.cast_nonneg u
  have hnr_ge : 8 * (K + 1) ^ 2 * K * a ≤ nr := by
    have hsq : (K + 1) ^ 2 ≤ Mr ^ 2 := pow_le_pow_left₀ (by linarith) hMK 2
    have h8 : 8 * (K + 1) ^ 2 * K * a ≤ 8 * Mr ^ 2 * K * dl := by
      calc 8 * (K + 1) ^ 2 * K * a ≤ 8 * Mr ^ 2 * K * a := by gcongr
        _ ≤ 8 * Mr ^ 2 * K * dl := by gcongr
    linarith
  have hKa_le : (K + 1) * a ≤ nr := by
    have h8 : 1 ≤ 8 * (K + 1) * K := by nlinarith
    have : (K + 1) * a ≤ 8 * (K + 1) ^ 2 * K * a := by
      calc (K + 1) * a = 1 * ((K + 1) * a) := (one_mul _).symm
        _ ≤ (8 * (K + 1) * K) * ((K + 1) * a) :=
            mul_le_mul_of_nonneg_right h8 (mul_nonneg (by linarith) ha0)
        _ = 8 * (K + 1) ^ 2 * K * a := by ring
    linarith
  have hnr1 : 1 ≤ nr := by nlinarith
  set y1 : ℝ := K * (a / (nr - a + 1)) with hy1
  set y2 : ℝ := Mr * (ur / (n'r - ur + 1)) with hy2
  set S : ℝ := nr + (K + 1) * a with hS
  have hKa_pos : 0 < (K + 1) * a := mul_pos (by linarith) (by linarith)
  have hSpos : 0 < S := by rw [hS]; linarith
  have hd1 : 0 < nr - a + 1 := by nlinarith
  have hnrMr : 1 ≤ nr * Mr := by nlinarith
  have hKdl0 : 0 ≤ K * dl := mul_nonneg hK0 (by linarith)
  have hq : K * dl ≤ nr * Mr * K * dl := by
    calc K * dl = 1 * (K * dl) := (one_mul _).symm
      _ ≤ (nr * Mr) * (K * dl) := mul_le_mul_of_nonneg_right hnrMr hKdl0
      _ = nr * Mr * K * dl := by ring
  have hd2 : 0 < n'r - ur + 1 := by rw [hn'eq]; nlinarith
  have hpoly : K * (K + 2) + 3 / 16 ≤ 3 / 2 * (K + 1) ^ 2 * K := by
    nlinarith [mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hK1),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hK1)) (sub_nonneg.2 hK1)]
  have e1 : K * (K + 2) * a + 3 * a / 16 ≤ 3 * nr / 16 := by
    have := mul_le_mul_of_nonneg_right hpoly ha0
    nlinarith
  have hy1S : y1 * S ≤ K * a + 3 * a / 16 := by
    have : y1 * S = K * a * S / (nr - a + 1) := by
      rw [hy1, ← mul_div_assoc, div_mul_eq_mul_div]
    rw [this, div_le_iff₀ hd1, hS]
    have h2 := mul_le_mul_of_nonneg_left e1 ha0
    nlinarith
  have hy2S : y2 * S ≤ 1 / 2 := by
    have : y2 * S = Mr * ur * S / (n'r - ur + 1) := by
      rw [hy2, ← mul_div_assoc, div_mul_eq_mul_div]
    rw [this, div_le_iff₀ hd2, hn'eq]
    have hS2 : S ≤ 2 * nr := by rw [hS]; linarith
    have p1 : Mr * ur * S ≤ Mr * (K * dl) * (2 * nr) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hud (by linarith)) hS2 hSpos.le
        (mul_nonneg (by linarith) hKdl0)
    have e2 : Mr * (K * dl) * (2 * nr) = 2 * (nr * Mr * K * dl) := by ring
    have e3 : 8 * nr * Mr * K * dl = 8 * (nr * Mr * K * dl) := by ring
    rw [e2] at p1
    rw [e3]
    linarith
  have hyS : (y1 + y2) * S ≤ (K + 1) * a := by
    have e4 : (K + 1) * a = K * a + a := by ring
    rw [add_mul, e4]; linarith
  have hny : nr ≤ S * (1 - (y1 + y2)) := by
    have : S * (1 - (y1 + y2)) = S - (y1 + y2) * S := by ring
    rw [this]; linarith
  have hexp : Real.exp (y1 + y2) * (1 - (y1 + y2)) ≤ 1 := by
    have h0 := Real.add_one_le_exp (-(y1 + y2))
    have h2 : Real.exp (y1 + y2) * Real.exp (-(y1 + y2)) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (y1 + y2) * (1 - (y1 + y2)) ≤ Real.exp (y1 + y2) * Real.exp (-(y1 + y2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := h2
  have hmain : nr * Real.exp (y1 + y2) ≤ S := by
    calc nr * Real.exp (y1 + y2) ≤ (S * (1 - (y1 + y2))) * Real.exp (y1 + y2) :=
          mul_le_mul_of_nonneg_right hny (Real.exp_pos _).le
      _ = S * (Real.exp (y1 + y2) * (1 - (y1 + y2))) := by ring
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left hexp hSpos.le
      _ = S := mul_one S
  have hX0 : 0 ≤ (cardUX D N (n - deF) (n' - u) : ℝ) := Nat.cast_nonneg _
  have hprod : (cardUX D N n n' : ℝ) ≤
      (cardUX D N (n - deF) (n' - u) : ℝ) * Real.exp (y1 + y2) := by
    rw [hc1, hc2, Real.exp_add]
    calc _ ≤ ((((n - deF + (D + 1)).choose (D + 1) : ℕ) : ℝ) * Real.exp y1) *
          ((((n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) : ℝ) * Real.exp y2) :=
          mul_le_mul hA hB (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
      _ = _ := by ring
  have hnr0 : 0 ≤ nr := by linarith
  calc (n : ℝ) * cardUX D N n n' ≤ nr * ((cardUX D N (n - deF) (n' - u) : ℝ) * Real.exp (y1 + y2)) :=
        mul_le_mul_of_nonneg_left hprod hnr0
    _ = (cardUX D N (n - deF) (n' - u) : ℝ) * (nr * Real.exp (y1 + y2)) := by ring
    _ ≤ (cardUX D N (n - deF) (n' - u) : ℝ) * S := mul_le_mul_of_nonneg_left hmain hX0
    _ = ((n : ℝ) + (D + 2) * deF) * cardUX D N (n - deF) (n' - u) := by
        rw [hS, hK, ha, hnr]; push_cast; ring

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

def hupsWx (D N : ℕ) : UXVar D N → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

def hupsWu (D N : ℕ) : UXVar D N → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

theorem hups_xDeg_eq {D N : ℕ} (s : UXVar D N →₀ ℕ) : xDeg s = hupsWt (hupsWx D N) s := by
  unfold hupsWt xDeg
  rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  simp [hupsWx]

theorem hups_uDeg_eq {D N : ℕ} (s : UXVar D N →₀ ℕ) : uDeg s = hupsWt (hupsWu D N) s := by
  unfold hupsWt uDeg
  rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  simp [hupsWu]

theorem hups_xDeg_add {D N : ℕ} (s t : UXVar D N →₀ ℕ) : xDeg (s + t) = xDeg s + xDeg t := by
  unfold xDeg; simp [Finset.sum_add_distrib]

theorem hups_uDeg_add {D N : ℕ} (s t : UXVar D N →₀ ℕ) : uDeg (s + t) = uDeg s + uDeg t := by
  unfold uDeg; simp [Finset.sum_add_distrib]

theorem hups_cofactor {R : Type*} [CommRing R] [IsDomain R] {D N : ℕ}
    {F P : MvPolynomial (UXVar D N) R} (hF : F ≠ 0) {deF u n n' : ℕ} (hFx : XHom deF F)
    {sF : UXVar D N →₀ ℕ} (hsF : sF ∈ F.support) (hsFu : uDeg sF = u)
    (hx : XHom n (F * P)) (hu : UDegLE n' (F * P)) :
    ∀ s ∈ P.support, s ∈ upMono D N (n - deF) (n' - u) := by
  intro s hs
  rw [mem_upMono]
  have h1 := hups_hom_of_mul (hupsWx D N) hF (a := deF) (n := n)
    (fun t ht => (hups_xDeg_eq t).symm.trans (hFx t ht))
    (fun t ht => (hups_xDeg_eq t).symm.trans (hx t ht)) hs
  have h2 := hups_deg_of_mul (hupsWu D N) (u := u) (n := n') hsF ((hups_uDeg_eq sF).symm.trans hsFu)
    (fun t ht => (hups_uDeg_eq t) ▸ hu t ht) hs
  rw [← hups_xDeg_eq] at h1
  rw [← hups_uDeg_eq] at h2
  omega

theorem hups_span_transfer {K : Type} [Field K] (σ : K →+* ℂ) {α β : Type} [Fintype α] [Fintype β]
    {r : ℕ} (u : α → Fin r → K) (v : β → Fin r → K)
    (h : ∀ a, u a ∈ Submodule.span K (Set.range v)) (z : α → ℂ) :
    ∃ y : β → ℂ, ∀ i, ∑ a, z a * σ (u a i) = ∑ b, y b * σ (v b i) := by
  choose c hc using fun a => (Submodule.mem_span_range_iff_exists_fun K).1 (h a)
  refine ⟨fun b => ∑ a, z a * σ (c a b), fun i => ?_⟩
  have hu : ∀ a, u a i = ∑ b, c a b * v b i := fun a => by
    rw [← hc a, Finset.sum_apply]; simp [smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hu, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

theorem hups_coeff_mul_of_supp {σ R : Type*} [CommRing R] (F P : MvPolynomial σ R)
    (S : Finset (σ →₀ ℕ)) (hP : P.support ⊆ S) (t : σ →₀ ℕ) :
    (F * P).coeff t = ∑ m : S, P.coeff m * (F * MvPolynomial.monomial (m : σ →₀ ℕ) 1).coeff t := by
  classical
  have hPs : P = ∑ m ∈ S, MvPolynomial.monomial m (P.coeff m) := by
    conv_lhs => rw [P.as_sum]
    exact Finset.sum_subset hP fun m _ hm => by simp [MvPolynomial.notMem_support_iff.1 hm]
  conv_lhs => rw [hPs]
  rw [Finset.mul_sum, MvPolynomial.coeff_sum, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show MvPolynomial.monomial (m : σ →₀ ℕ) (P.coeff m) =
      MvPolynomial.C (P.coeff m) * MvPolynomial.monomial (m : σ →₀ ℕ) 1 by
    rw [MvPolynomial.C_mul_monomial, mul_one]]
  rw [mul_left_comm, MvPolynomial.coeff_C_mul]

theorem polyL2_eq_sqrt_coeff_sum {σ : Type*} (f : MvPolynomial σ ℂ) (V : Finset (σ →₀ ℕ)) {r : ℕ}
    (e : V ≃ Fin r) (hf : f.support ⊆ V) :
    ReciprocityTheory.MultiplicativeHeights.polyL2 f = Real.sqrt (∑ i, ‖f.coeff (e.symm i : σ →₀ ℕ)‖ ^ 2) := by
  unfold ReciprocityTheory.MultiplicativeHeights.polyL2
  congr 1
  rw [Finset.sum_subset hf fun s _ hs => by simp [MvPolynomial.notMem_support_iff.1 hs],
    ← Finset.sum_coe_sort V]
  exact (Equiv.sum_comp e.symm (fun x : V => ‖f.coeff (x : σ →₀ ℕ)‖ ^ 2)).symm

theorem hups_choose_strict (D : ℕ) : StrictMono fun m : ℕ => (m + D + 1).choose (D + 1) := by
  refine strictMono_nat_of_lt_succ fun m => ?_
  show (m + D + 1).choose (D + 1) < (m + 1 + D + 1).choose (D + 1)
  rw [show m + 1 + D + 1 = (m + D + 1) + 1 by omega, Nat.choose_succ_succ' (m + D + 1) D]
  have := Nat.choose_pos (show D ≤ m + D + 1 by omega)
  omega

theorem hups_cardUX_lt (D N n n' deF u : ℕ) (h1 : 1 ≤ deF) (hn : deF ≤ n) :
    cardUX D N (n - deF) (n' - u) < cardUX D N n n' := by
  unfold cardUX
  have ha : (n - deF + D + 1).choose (D + 1) < (n + D + 1).choose (D + 1) :=
    hups_choose_strict D (show n - deF < n by omega)
  have hb : (n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) ≤
      (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) :=
    Nat.choose_le_choose _ (by omega)
  have hb0 : 0 < (n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) :=
    Nat.choose_pos (by omega)
  calc _ < (n + D + 1).choose (D + 1) * (n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) :=
        Nat.mul_lt_mul_of_pos_right ha hb0
    _ ≤ _ := Nat.mul_le_mul_left _ hb

theorem hups_log_rd_nonneg (K : Type) [Field K] [NumberField K] :
    0 ≤ Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) := by
  apply Real.log_nonneg
  apply Real.one_le_rpow _ (by positivity)
  have h := NumberField.discr_ne_zero K
  have : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs h
  have : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast this
  simpa [Int.cast_abs] using this

theorem polyL2_nonneg {σ : Type*} (f : MvPolynomial σ ℂ) : 0 ≤ ReciprocityTheory.MultiplicativeHeights.polyL2 f := by
  unfold ReciprocityTheory.MultiplicativeHeights.polyL2; exact Real.sqrt_nonneg _

theorem hups_qnorm_eq {K : Type} [Field K] [NumberField K] {D N : ℕ} (σ : K →+* ℂ)
    (F1 : MvPolynomial (UXVar D N) K) {n n' : ℕ} (V S : Finset (UXVar D N →₀ ℕ))
    (hVd : ∀ s ∈ V, xDeg s = n ∧ uDeg s ≤ n')
    (hadd : ∀ a ∈ F1.support, ∀ m ∈ S, a + m ∈ V)
    (hcof : ∀ P : MvPolynomial (UXVar D N) ℂ, XHom n (MvPolynomial.map σ F1 * P) →
      UDegLE n' (MvPolynomial.map σ F1 * P) → P.support ⊆ S)
    {r k : ℕ} (e : V ≃ Fin r) (b : Fin k → Fin r → K)
    (hspan : Submodule.span K (Set.range b) =
      Submodule.span K (Set.range fun m : S =>
        fun i => (F1 * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
          (e.symm i : UXVar D N →₀ ℕ)))
    (Q : MvPolynomial (UXVar D N) (𝓞 K)) (hQsupp : Q.support ⊆ V) :
    qnorm σ F1 n n' Q = qdist σ b (fun i => ((Q.coeff (e.symm i : UXVar D N →₀ ℕ) : 𝓞 K) : K)) := by
  classical
  unfold qnorm qdist
  beta_reduce
  have hc : ∀ m : S, (fun i => (F1 * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
      (e.symm i : UXVar D N →₀ ℕ)) ∈ Submodule.span K (Set.range b) := fun m => by
    rw [hspan]; exact Submodule.subset_span ⟨m, rfl⟩
  have hbc : ∀ j, b j ∈ Submodule.span K (Set.range fun m : S =>
      fun i => (F1 * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
        (e.symm i : UXVar D N →₀ ℕ)) := fun j => by
    rw [← hspan]; exact Submodule.subset_span ⟨j, rfl⟩
  generalize hcdef : (fun m : S => fun i => (F1 * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
      (e.symm i : UXVar D N →₀ ℕ)) = c at hc hbc
  have hcv : ∀ (m : S) i, c m i = (F1 * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
      (e.symm i : UXVar D N →₀ ℕ) := fun m i => by rw [← hcdef]
  have hFσs : (MvPolynomial.map σ F1).support = F1.support :=
    MvPolynomial.support_map_of_injective _ σ.injective
  generalize hFσ : MvPolynomial.map σ F1 = Fσ at hcof hFσs ⊢
  generalize hQσ : MvPolynomial.map (σ.comp (algebraMap (𝓞 K) K)) Q = Qσ
  have hQσs : Qσ.support ⊆ V := hQσ ▸ (MvPolynomial.support_map_subset _ _).trans hQsupp
  have hQσc : ∀ i, Qσ.coeff (e.symm i : UXVar D N →₀ ℕ) =
      σ ((Q.coeff (e.symm i : UXVar D N →₀ ℕ) : 𝓞 K) : K) := fun i => by
    rw [← hQσ, MvPolynomial.coeff_map]; rfl
  have hcσ : ∀ (m : S) i, (Fσ * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
      (e.symm i : UXVar D N →₀ ℕ) = σ (c m i) := by
    intro m i
    rw [hcv, ← hFσ, show (1 : ℂ) = σ 1 from σ.map_one.symm, ← MvPolynomial.map_monomial, ← map_mul,
      MvPolynomial.coeff_map]
  have hmulV : ∀ P : MvPolynomial (UXVar D N) ℂ, P.support ⊆ S → (Fσ * P).support ⊆ V := by
    intro P hP s hs
    obtain ⟨a, ha, m, hm, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul Fσ P hs)
    exact hadd a (hFσs ▸ ha) m (hP hm)
  have hval : ∀ P : MvPolynomial (UXVar D N) ℂ, P.support ⊆ S →
      ReciprocityTheory.MultiplicativeHeights.polyL2 (Qσ + Fσ * P) =
        Real.sqrt (∑ i, ‖σ ((Q.coeff (e.symm i : UXVar D N →₀ ℕ) : 𝓞 K) : K) +
          ∑ m : S, P.coeff m * σ (c m i)‖ ^ 2) := by
    intro P hP
    rw [polyL2_eq_sqrt_coeff_sum _ V e (MvPolynomial.support_add.trans (Finset.union_subset hQσs (hmulV P hP)))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.coeff_add, hQσc, hups_coeff_mul_of_supp Fσ P S hP]
    simp only [hcσ]
  have hbdd1 : BddBelow (Set.range fun P : {P : MvPolynomial (UXVar D N) ℂ //
      XHom n (Fσ * P) ∧ UDegLE n' (Fσ * P)} => ReciprocityTheory.MultiplicativeHeights.polyL2 (Qσ + Fσ * P.1)) :=
    ⟨0, by rintro _ ⟨P, rfl⟩; exact polyL2_nonneg _⟩
  have hbdd2 : BddBelow (Set.range fun z : Fin k → ℂ =>
      Real.sqrt (∑ i, ‖σ ((Q.coeff (e.symm i : UXVar D N →₀ ℕ) : 𝓞 K) : K) +
        ∑ j, z j * σ (b j i)‖ ^ 2)) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact Real.sqrt_nonneg _⟩
  apply le_antisymm
  · apply le_ciInf
    intro z
    obtain ⟨y, hy⟩ := hups_span_transfer σ b c hbc z
    obtain ⟨P, hP⟩ : ∃ P : MvPolynomial (UXVar D N) ℂ,
        P = ∑ m : S, MvPolynomial.monomial (m : UXVar D N →₀ ℕ) (y m) := ⟨_, rfl⟩
    have hPc : ∀ m : S, P.coeff m = y m := fun m => by
      rw [hP, MvPolynomial.coeff_sum, Fintype.sum_eq_single m]
      · simp
      · intro m' hm'
        rw [MvPolynomial.coeff_monomial, if_neg]
        exact fun h => hm' (Subtype.ext h)
    have hPS : P.support ⊆ S := by
      intro s hs
      by_contra h
      rw [MvPolynomial.mem_support_iff, hP, MvPolynomial.coeff_sum] at hs
      apply hs
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [MvPolynomial.coeff_monomial, if_neg]
      exact fun h' => h (h' ▸ m.2)
    have hPV := hmulV P hPS
    have hadm : XHom n (Fσ * P) ∧ UDegLE n' (Fσ * P) :=
      ⟨fun s hs => (hVd s (hPV hs)).1, fun s hs => (hVd s (hPV hs)).2⟩
    refine (ciInf_le hbdd1 ⟨P, hadm⟩).trans (le_of_eq ?_)
    show ReciprocityTheory.MultiplicativeHeights.polyL2 (Qσ + Fσ * P) = _
    rw [hval P hPS]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hy i]
    simp only [hPc]
  · have : Nonempty {P : MvPolynomial (UXVar D N) ℂ // XHom n (Fσ * P) ∧ UDegLE n' (Fσ * P)} :=
      ⟨⟨0, by simp [XHom], by simp [UDegLE]⟩⟩
    apply le_ciInf
    rintro ⟨P, hPx, hPu⟩
    have hPS : P.support ⊆ S := hcof P hPx hPu
    obtain ⟨z, hz⟩ := hups_span_transfer σ c b (fun m => by rw [← hcdef]; exact hc m) (fun m => P.coeff m)
    refine (ciInf_le hbdd2 z).trans (le_of_eq ?_)
    show _ = ReciprocityTheory.MultiplicativeHeights.polyL2 (Qσ + Fσ * P)
    rw [hval P hPS]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz i]

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem up_siegel (hd : d.AxH 𝒜) (F1 : MvPolynomial (UXVar d.D d.N) K) (deF : ℕ)
    (h1 : 1 ≤ deF) (hle : deF ≤ d.del) (hirr : Irreducible F1) (hx : XHom deF F1)
    (hu : UDegLE ((d.D + 1) * d.del) F1) (hpos : 0 < hT F1) :
    ∃ Q : MvPolynomial (UXVar d.D d.N) (𝓞 K), XHom d.n96 (mapK Q) ∧ UDegLE d.n96' (mapK Q) ∧
      ¬ F1 ∣ mapK Q ∧
      meanK (fun σ => Real.log (qnorm σ F1 d.n96 d.n96' Q)) ≤
        -(d.n96 * hT F1 / ((d.D + 2) * deF)) +
          1 / 2 * Real.log (cardUX d.D d.N d.n96 d.n96') + d.PO := by
  classical
  have hF1 : F1 ≠ 0 := hirr.ne_zero
  obtain ⟨sF, hsF, hsFu⟩ := Finset.exists_mem_eq_sup F1.support
    (Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.1 hF1)) uDeg
  generalize hudef : F1.support.sup uDeg = u at hsFu
  have hule : u ≤ (d.D + 1) * d.del := hsFu ▸ hu sF hsF
  have hn96 : d.n96 = 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del * (1 + ⌈d.PO⌉₊) := rfl
  have hn : 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del ≤ d.n96 := by
    rw [hn96]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hdeln : d.del ≤ d.n96 := by
    refine le_trans ?_ hn
    rw [show 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del =
      (8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1)) * d.del by ring]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hdn : deF ≤ d.n96 := le_trans hle hdeln
  have hn' : d.n96' = 8 * d.n96 * ((d.D + 2) * (d.N + 1)) * (d.D + 1) * d.del := rfl
  have hun' : u ≤ d.n96' := by
    have : (d.D + 1) * d.del ≤ d.n96' := by
      rw [hn', show 8 * d.n96 * ((d.D + 2) * (d.N + 1)) * (d.D + 1) * d.del =
        (8 * d.n96 * ((d.D + 2) * (d.N + 1))) * ((d.D + 1) * d.del) by ring]
      have : 0 < d.n96 := by omega
      exact Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hadd : ∀ a ∈ F1.support, ∀ m ∈ upMono d.D d.N (d.n96 - deF) (d.n96' - u),
      a + m ∈ upMono d.D d.N d.n96 d.n96' := by
    intro a ha m hm
    rw [mem_upMono] at hm
    rw [mem_upMono, hups_xDeg_add, hups_uDeg_add, hx a ha]
    have : uDeg a ≤ u := hudef ▸ Finset.le_sup ha
    omega
  have hST : ∀ m ∈ upMono d.D d.N (d.n96 - deF) (d.n96' - u),
      (F1 * MvPolynomial.monomial m 1).support ⊆ upMono d.D d.N d.n96 d.n96' := by
    intro m hm s hs
    obtain ⟨a, ha, m', hm', rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ hs)
    have : m' = m := Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm')
    subst this
    exact hadd a ha m' hm
  obtain ⟨b, hbL, hbli, hspan, hdeg⟩ := satDeg_le K F1 hF1 (upMono d.D d.N d.n96 d.n96')
    (upMono d.D d.N (d.n96 - deF) (d.n96' - u)) (upMono d.D d.N d.n96 d.n96').equivFin hST
  have hk : (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card < (upMono d.D d.N d.n96 d.n96').card := by
    rw [card_upMono, card_upMono]; exact hups_cardUX_lt _ _ _ _ _ _ h1 hdn
  obtain ⟨q, hqnot, hmean⟩ := mink_sat K _ _ b hbli hbL hk
  set e := (upMono d.D d.N d.n96 d.n96').equivFin with he
  obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial (UXVar d.D d.N) (𝓞 K),
      Q = ∑ i, MvPolynomial.monomial (e.symm i : UXVar d.D d.N →₀ ℕ) (q i) := ⟨_, rfl⟩
  have hQc : ∀ i, Q.coeff (e.symm i : UXVar d.D d.N →₀ ℕ) = q i := fun i => by
    rw [hQ, MvPolynomial.coeff_sum, Fintype.sum_eq_single i]
    · simp
    · intro j hj
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      exact hj (e.symm.injective (Subtype.ext h))
  have hQs : Q.support ⊆ upMono d.D d.N d.n96 d.n96' := by
    intro s hs
    by_contra h
    rw [MvPolynomial.mem_support_iff, hQ, MvPolynomial.coeff_sum] at hs
    apply hs
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun h' => h (h' ▸ (e.symm i).2)
  have hQKs : (mapK Q).support ⊆ upMono d.D d.N d.n96 d.n96' :=
    (MvPolynomial.support_map_subset _ _).trans hQs
  have hQx : XHom d.n96 (mapK Q) := fun s hs => (mem_upMono.1 (hQKs hs)).1
  have hQu : UDegLE d.n96' (mapK Q) := fun s hs => (mem_upMono.1 (hQKs hs)).2
  have hqQ : (fun i => ((q i : 𝓞 K) : K)) =
      fun i => ((Q.coeff (e.symm i : UXVar d.D d.N →₀ ℕ) : 𝓞 K) : K) :=
    funext fun i => by rw [hQc]
  refine ⟨Q, hQx, hQu, ?_, ?_⟩
  · rintro ⟨P, hP⟩
    have hPS : P.support ⊆ upMono d.D d.N (d.n96 - deF) (d.n96' - u) := fun s hs =>
      hups_cofactor hF1 hx hsF hsFu.symm (hP ▸ hQx) (hP ▸ hQu) s hs
    apply hqnot
    rw [hspan, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun m => P.coeff m, funext fun i => ?_⟩
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hups_coeff_mul_of_supp F1 P _ hPS, ← hP, MvPolynomial.coeff_map, hQc]
  · have hqn : ∀ σ : K →+* ℂ, qnorm σ F1 d.n96 d.n96' Q = qdist σ b (fun i => ((q i : 𝓞 K) : K)) :=
      fun σ => by
        rw [hqQ]
        refine hups_qnorm_eq σ F1 _ _ (fun s hs => mem_upMono.1 hs) hadd ?_ e b hspan Q hQs
        intro P hPx hPu s hs
        have hFσs : (MvPolynomial.map σ F1).support = F1.support :=
          MvPolynomial.support_map_of_injective _ σ.injective
        have hFσ0 : MvPolynomial.map σ F1 ≠ 0 := by
          intro h; apply hF1
          rw [← MvPolynomial.support_eq_empty, ← hFσs, h, MvPolynomial.support_zero]
        exact hups_cofactor hFσ0 (fun t ht => hx t (hFσs ▸ ht)) (hFσs ▸ hsF) hsFu.symm hPx hPu s hs
    simp_rw [hqn]
    refine hmean.trans ?_
    have e4 := hd.rd_le
    have e5 := hups_log_rd_nonneg K
    have hratio := hups_ratio d.D d.N d.n96 d.n96' deF u d.del h1 hle hule hn rfl
    have hdK : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    have hkr : (((upMono d.D d.N d.n96 d.n96').card - (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card
        : ℕ) : ℝ) = ((upMono d.D d.N d.n96 d.n96').card : ℝ) -
          (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card := Nat.cast_sub hk.le
    have hR : (0 : ℝ) < (((upMono d.D d.N d.n96 d.n96').card -
        (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card : ℕ) : ℝ) :=
      Nat.cast_pos.2 (Nat.sub_pos_of_lt hk)
    generalize ReciprocityTheory.MultiplicativeHeights.latDeg (K := K) (fun _ => 1)
      (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K (upMono d.D d.N d.n96 d.n96').card) b) b = Ld at hdeg ⊢
    simp only [card_upMono] at hkr hR hdeg ⊢
    generalize ((cardUX d.D d.N d.n96 d.n96' - cardUX d.D d.N (d.n96 - deF) (d.n96' - u) : ℕ) : ℝ) = R
      at hkr hR ⊢
    generalize (cardUX d.D d.N d.n96 d.n96' : ℝ) = rr at hkr hratio ⊢
    generalize (cardUX d.D d.N (d.n96 - deF) (d.n96' - u) : ℝ) = kk at hkr hratio hdeg ⊢
    generalize (Module.finrank ℚ K : ℝ) = dK at hdK hdeg e4 e5 ⊢
    generalize hT F1 = h at hpos hdeg ⊢
    have hc : (0 : ℝ) < (d.D + 2) * deF := by positivity
    have e1 : Ld / (dK * R) ≤ -(kk * h) / R := by
      rw [div_le_div_iff₀ (by positivity) hR]
      calc Ld * R ≤ -(kk * dK * h) * R := mul_le_mul_of_nonneg_right hdeg hR.le
        _ = _ := by ring
    have e2 : -(kk * h) / R ≤ -(d.n96 * h / ((d.D + 2) * deF)) := by
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ hc hR]
      have h' : (d.n96 : ℝ) * R ≤ (d.D + 2) * deF * kk := by rw [hkr]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h' hpos.le]
    have e3 : Real.log R ≤ Real.log rr := Real.log_le_log hR (by
      have : (0 : ℝ) ≤ kk := by
        by_contra hneg
        rw [not_le] at hneg
        nlinarith
      linarith)
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem upB_nonneg (hd : d.AxH 𝒜) : 0 ≤ d.upB := by
  have h1 := hd.P_ge.2.2.2.1
  have h2 := hd.size_L
  have h3 : 0 ≤ Real.log (d.N + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos _)
  have h4 : 0 ≤ max 0 d.laW := le_max_left _ _
  unfold upB
  nlinarith

theorem delc_le_del (c : ι) : d.delc c ≤ d.del :=
  Finset.single_le_sum (f := d.delc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

theorem up_comp (hd : d.AxH 𝒜) (h : d.S1) (hLAM : d.HtLAM) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) (c : ι) :
    ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ (d.D + 2) * d.delc c * d.upB := by
  have hB := d.upB_nonneg hd
  by_cases hpos : ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ 0
  · exact hpos.trans (by positivity)
  replace hpos := not_le.mp hpos
  obtain ⟨F1, m, deF, hm, hdeF, hmd, hirr, hx, hu, hle, hker⟩ := d.irreducible_factor_height_bound hd h F hF c hpos
  have hcd := d.delc_le_del c
  have hdel : 1 ≤ d.del := by
    have : 1 ≤ m * deF := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT0 : 0 < hT F1 := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have : (m : ℝ) * hT F1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
    linarith
  have hu' : UDegLE ((d.D + 1) * d.del) F1 := fun s hs =>
    (hu s hs).trans (Nat.mul_le_mul_left _ hcd)
  obtain ⟨Q, hQx, hQu, hQ, hS⟩ := d.up_siegel hd F1 deF hdeF
    ((Nat.le_mul_of_pos_left deF (by omega)).trans (hmd.trans hcd)) hirr hx hu' hT0
  obtain ⟨g, hg, hgc, hC⟩ := d.up_cauchy hd hdel c F1 deF hx hker Q hQx hQu hQ
  have hL := hLAM c g hg hgc
  have hN := d.up_count hd hdel
  have hn : (0 : ℝ) < d.n96 := by
    have : 0 < d.n96 := by
      unfold n96
      have : 0 < (d.N + 1) := Nat.succ_pos _
      positivity
    exact_mod_cast this
  have hDF : (0 : ℝ) < (d.D + 2) * deF := by
    have : (1 : ℝ) ≤ deF := by exact_mod_cast hdeF
    positivity
  have hlaw : d.laW ≤ max 0 d.laW := le_max_right _ _

  have key : d.n96 * hT F1 / ((d.D + 2) * deF) ≤ d.n96 * d.upB := by
    unfold upB
    nlinarith
  have key2 : hT F1 ≤ (d.D + 2) * deF * d.upB := by
    rw [div_le_iff₀ hDF] at key
    have : d.n96 * hT F1 ≤ d.n96 * ((d.D + 2) * deF * d.upB) := by nlinarith
    exact le_of_mul_le_mul_left this hn
  have hmdR : (m : ℝ) * deF ≤ d.delc c := by exact_mod_cast hmd
  calc ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ m * hT F1 := hle
    _ ≤ m * ((d.D + 2) * deF * d.upB) := by gcongr
    _ = (d.D + 2) * (m * deF) * d.upB := by ring
    _ ≤ (d.D + 2) * d.delc c * d.upB := by gcongr

theorem sum_logHeight_upper_bound (hd : d.AxH 𝒜) (h : d.S1) (hLAM : d.HtLAM) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) :
    ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤
      (d.D + 2) * d.del * (d.PP0' * d.wsize d.wL +
        max 0 (meanK fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j))) +
        Real.log (d.N + 1 : ℕ) + 1) := by
  calc ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ ∑ c, ((d.D : ℝ) + 2) * d.delc c * d.upB :=
        Finset.sum_le_sum fun c _ => d.up_comp hd h hLAM F hF c
    _ = ((d.D : ℝ) + 2) * d.del * d.upB := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        simp [Data.del, Nat.cast_sum]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
