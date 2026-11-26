module

public import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.GramWindow2

@[expose] public section

section -- merged from Formalism.PolynomialDimension.ChangeLatticeGoodRank
section -- merged from Formalism.PolynomialDimension.MultinomialDepth.SegmentBoundThreeHolds
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

theorem det_leading_diagonal : DetLeadDiag := by
  intro K _ n J A d hdeg hcoeff
  have hprod : ∀ σ : Equiv.Perm (Fin n), (∏ i, A (σ i) i).coeff (n * J) = ∏ i, (A (σ i) i).coeff J := by
    intro σ
    have h1 := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ) (fun i => A (σ i) i) J
      (fun i _ => hdeg (σ i) i)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  rw [Matrix.det_apply']
  constructor
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro σ _
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_intCast, zero_add]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ i, (A (σ i) i).natDegree ≤ ∑ _i : Fin n, J := Finset.sum_le_sum fun i _ => hdeg (σ i) i
      _ = n * J := by simp
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 1]
    · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hprod]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply]
      exact Finset.prod_congr rfl fun i _ => by rw [hcoeff]; simp
    · intro σ _ hσ
      rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hprod]
      obtain ⟨i, hi⟩ := not_forall.mp (mt Equiv.ext hσ)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hcoeff, if_neg (by simpa using hi)]), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end Formalism.CountingSumsFrames
end
end

namespace Formalism.CountingSumsFrames.Top

theorem detLeadDiag : Formalism.CountingSumsFrames.DetLeadDiag := Formalism.CountingSumsFrames.det_leading_diagonal

end Formalism.CountingSumsFrames.Top
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.FockGramWindow.NeglogPowMul
section -- merged from Formalism.SharpRestriction.GrowthBounds.FockGramWindow.BinMatNatDegreeLe
section -- merged from Formalism.SharpRestriction.GrowthBounds.FockGramWindow.PhiPair
noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM

section Alg

variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ} (w e : Fin r → σ)

def mX (J l : ℕ) (u v : MvPolynomial σ ℚ_[p]) : ℚ_[p] :=
  M.fockK (((tieE w e) ^ l) (((tieF w e) ^ l) u)) v / (((l.factorial : ℚ_[p]) ^ 2) * (J.choose l : ℚ_[p]))

theorem phi_pair (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (hr : 1 ≤ r)
    (o n z : ℕ) (u v : MvPolynomial σ ℚ_[p]) (hv : BiHom w e o n v) :
    ((o + n + r + z - 1).choose (min o n) : ℚ_[p]) * M.fockK (tiePhi w e o n z u) v =
      ∑ l ∈ range (min o n + 1), (-1 : ℚ_[p]) ^ l * ((o + n + r + z - 1 - l).choose (min o n - l) : ℚ_[p]) *
        mX w e (min o n) l u v := by
  have hz := Formalism.InvariantFactorPaths.KP.LL.tieF_pow_apply_eq_zero_of_min_lt w e hw he hwe hv
  unfold tiePhi
  rw [LinearMap.sum_apply, ProjS.fockK_sum_left, Finset.mul_sum]
  have hsub : range (min o n + 1) ⊆ range (o + 1) := by
    intro l hl; simp only [mem_range] at hl ⊢; omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ min o n := by simp only [mem_range] at hl; omega
    have hJM : min o n ≤ o + n + r + z - 1 := by omega
    have hch := Nat.choose_mul (n := o + n + r + z - 1) hl'
    have hch' : ((o + n + r + z - 1).choose (min o n) : ℚ_[p]) * ((min o n).choose l : ℚ_[p]) =
        ((o + n + r + z - 1).choose l : ℚ_[p]) * ((o + n + r + z - 1 - l).choose (min o n - l) : ℚ_[p]) := by
      exact_mod_cast hch
    have h1 : ((min o n).choose l : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos hl').ne'
    have h2 : ((o + n + r + z - 1).choose l : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hl'.trans hJM)).ne'
    have h3 : (l.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast l.factorial_ne_zero
    rw [LinearMap.smul_apply, ProjS.fockK_smul_left, LinearMap.comp_apply]
    unfold mX
    field_simp
    linear_combination (M.fockK (((tieE w e) ^ l) (((tieF w e) ^ l) u)) v) * hch'
  · intro l _ hl
    have hl' : min o n < l := by simp only [mem_range] at hl; omega
    rw [LinearMap.smul_apply, ProjS.fockK_smul_left, LinearMap.comp_apply, ProjS.fockK_tieE_pow, hz l hl',
      ProjS.fockK_zero_right, mul_zero, mul_zero]

end Alg

def cW {K : Type} [Field K] (q J : ℕ) (mm : ℕ → K) (i : ℕ) : K :=
  ∑ l ∈ range (J + 1), if i + l ≤ J then (-1 : K) ^ l * ((q - l).choose (J - l - i) : K) * mm l else 0

theorem cW_sum {K : Type} [Field K] (q J z : ℕ) (hq : J ≤ q) (mm : ℕ → K) :
    ∑ i ∈ range (J + 1), cW q J mm i * (z.choose i : K) =
      ∑ l ∈ range (J + 1), (-1 : K) ^ l * ((q + z - l).choose (J - l) : K) * mm l := by
  unfold cW
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ J := by simp only [mem_range] at hl; omega
  have hv : (q + z - l).choose (J - l) = ∑ i ∈ range (J - l + 1), z.choose i * (q - l).choose (J - l - i) := by
    rw [show q + z - l = z + (q - l) by omega, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [hv]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  have hsub : range (J - l + 1) ⊆ range (J + 1) := by
    intro i hi; simp only [mem_range] at hi ⊢; omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have : i + l ≤ J := by simp only [mem_range] at hi; omega
    rw [if_pos this]; ring
  · intro i _ hi
    have : ¬ (i + l ≤ J) := by simp only [mem_range] at hi; omega
    rw [if_neg this, zero_mul]

theorem cW_top {K : Type} [Field K] (q J : ℕ) (mm : ℕ → K) : cW q J mm J = mm 0 := by
  unfold cW
  rw [Finset.sum_eq_single 0]
  · simp
  · intro l _ hl
    rw [if_neg (by omega)]
  · intro h; simp at h

theorem cW_norm {p : ℕ} [Fact p.Prime] (q J : ℕ) (mm : ℕ → ℚ_[p]) (h : ∀ l ≤ J, ‖mm l‖ ≤ 1) (i : ℕ) :
    ‖cW q J mm i‖ ≤ 1 := by
  unfold cW
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l hl => ?_
  have hl' : l ≤ J := by simp only [mem_range] at hl; omega
  split_ifs
  · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h1 : ‖(((q - l).choose (J - l - i) : ℕ) : ℚ_[p])‖ ≤ 1 := by
      rw [← PadicInt.coe_natCast, ← PadicInt.norm_def]; exact PadicInt.norm_le_one _
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul h1 (h l hl') (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · simp

end Formalism.MainNotions.G.GramWindowAlt

end
end

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open Polynomial Finset Formalism.GM

section
variable (K : Type) [Field K] [CharZero K]

theorem binK_natDegree (k : ℕ) : (binK K k).natDegree = k := by
  unfold binK
  have h : ((k.factorial : K))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast k.factorial_ne_zero)
  rw [natDegree_C_mul h, descPochhammer_natDegree]

theorem binK_coeff_top (k : ℕ) : (binK K k).coeff k = ((k.factorial : K))⁻¹ := by
  unfold binK
  rw [coeff_C_mul]
  have h := (monic_descPochhammer K k).coeff_natDegree
  rw [descPochhammer_natDegree] at h
  rw [h, mul_one]

theorem binMat_natDegree_le {n : ℕ} (J : ℕ) (c : Fin n → Fin n → ℕ → K) (a b : Fin n) :
    (binMatK K J c a b).natDegree ≤ J := by
  unfold binMatK
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [binK_natDegree]
  simp only [mem_range] at hk; omega

theorem binMat_coeff_top {n : ℕ} (J : ℕ) (c : Fin n → Fin n → ℕ → K) (a b : Fin n) :
    (binMatK K J c a b).coeff J = c a b J * ((J.factorial : K))⁻¹ := by
  unfold binMatK
  rw [finsetSum_coeff, Finset.sum_eq_single J]
  · rw [coeff_C_mul, binK_coeff_top]
  · intro k hk hne
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [binK_natDegree]
    simp only [mem_range] at hk; omega
  · intro h; simp at h

end

theorem lead_bound (p : ℕ) [hp : Fact p.Prime] (n J : ℕ) (c : Fin n → Fin n → ℕ → ℚ_[p]) (d : Fin n → ℚ_[p])
    (hc : ∀ a b, c a b J = if a = b then d a else 0) (R Λ : ℝ) (hd : ∀ a, d a ≠ 0 ∧ -Real.logb p ‖d a‖ ≤ R)
    (hV : (J : ℝ) / ((p : ℝ) - 1) - padicValNat p J.factorial ≤ Λ) :
    (binMatK ℚ_[p] J c).det ≠ 0 ∧
      -Real.logb p ‖(binMatK ℚ_[p] J c).det.leadingCoeff‖ +
        ((binMatK ℚ_[p] J c).det.natDegree : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * (R + Λ) := by
  have hJ0 : ((J.factorial : ℚ_[p])) ≠ 0 := by exact_mod_cast J.factorial_ne_zero
  obtain ⟨h1, h2⟩ := Formalism.CountingSumsFrames.Top.detLeadDiag ℚ_[p] n J (binMatK ℚ_[p] J c) (fun a => d a * ((J.factorial : ℚ_[p]))⁻¹)
    (binMat_natDegree_le ℚ_[p] J c) (fun a b => by
      rw [binMat_coeff_top, hc]; split_ifs <;> simp)
  have hne : ∏ a, d a * ((J.factorial : ℚ_[p]))⁻¹ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => mul_ne_zero (hd a).1 (inv_ne_zero hJ0)
  have hdet : (binMatK ℚ_[p] J c).det ≠ 0 := by
    intro h0; rw [h0, coeff_zero] at h2; exact hne h2.symm
  have hdeg : (binMatK ℚ_[p] J c).det.natDegree = n * J :=
    le_antisymm h1 (le_natDegree_of_ne_zero (by rw [h2]; exact hne))
  have hlead : (binMatK ℚ_[p] J c).det.leadingCoeff = ∏ a, d a * ((J.factorial : ℚ_[p]))⁻¹ := by
    rw [leadingCoeff, hdeg, h2]
  refine ⟨hdet, ?_⟩
  rw [hlead, hdeg, norm_prod, Real.logb_prod _ _ (fun a _ => norm_ne_zero_iff.2 (mul_ne_zero (hd a).1 (inv_ne_zero hJ0)))]
  have hterm : ∀ a, Real.logb p ‖d a * ((J.factorial : ℚ_[p]))⁻¹‖ =
      Real.logb p ‖d a‖ + padicValNat p J.factorial := by
    intro a
    rw [norm_mul, norm_inv, Real.logb_mul (norm_ne_zero_iff.2 (hd a).1) (inv_ne_zero (norm_ne_zero_iff.2 hJ0)),
      Real.logb_inv, Formalism.GM.MeanGammaLemmas.neglog_nat p _ J.factorial_ne_zero]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : -∑ a, Real.logb p ‖d a‖ ≤ n * R := by
    rw [← Finset.sum_neg_distrib]
    calc ∑ a, -Real.logb p ‖d a‖ ≤ ∑ _a : Fin n, R := Finset.sum_le_sum fun a _ => (hd a).2
      _ = n * R := by simp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := mul_le_mul_of_nonneg_left hV hn
  push_cast
  have e1 : (n : ℝ) * J / ((p : ℝ) - 1) = n * ((J : ℝ) / ((p : ℝ) - 1)) := by ring
  rw [e1]
  nlinarith

end Formalism.MainNotions.G.GramWindowAlt

end
end

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type} {r : ℕ} (w e : Fin r → σ)

theorem mX_zero (J : ℕ) (u v : MvPolynomial σ ℚ_[p]) : mX w e J 0 u v = M.fockK u v := by
  unfold mX; simp

theorem neglog_pow_mul (x0 : ℕ) (c : ℚ_[p]) (hc : c ≠ 0) :
    -Real.logb p ‖(p : ℚ_[p]) ^ x0 * c‖ = (x0 : ℝ) + c.valuation := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [norm_mul, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hc,
    Real.logb_mul (pow_ne_zero _ (inv_ne_zero (by linarith))) (zpow_ne_zero _ (by linarith)), Real.logb_pow,
    Real.logb_inv, Real.logb_self_eq_one hp1, neg_add, Formalism.GM.MeanGammaLemmas.neglog_zpow]
  ring

theorem win_abs (hGW : GramWindow2) (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (hr : 1 ≤ r) (o n : ℕ) (T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) (dF : ℚ_[p])
    (n₁ : ℕ) (f : Fin n₁ → MvPolynomial σ ℚ_[p]) (hli : LinearIndependent ℤ_[p] f)
    (hbi : ∀ b, BiHom w e o n (f b)) (x0 : ℕ)
    (hint : ∀ l ≤ min o n, ∀ a b, ‖(p : ℚ_[p]) ^ x0 * (mX w e (min o n) l (T (f a)) (f b) / dF)‖ ≤ 1)
    (horth : ∀ a b, a ≠ b → M.fockK (T (f a)) (f b) / dF = 0) (D1z : ℤ)
    (hsmall : ∀ a, M.fockK (T (f a)) (f a) / dF ≠ 0 ∧ (M.fockK (T (f a)) (f a) / dF).valuation ≤ D1z)
    (Λ : ℝ) (hV : ((min o n : ℕ) : ℝ) / ((p : ℝ) - 1) - padicValNat p (min o n).factorial ≤ Λ)
    (z0 W h : ℕ) (k : ℤ) (hk : 0 ≤ k) (hW : 0 < W) (hWh : W ≤ p ^ h) (hJh : min o n + 1 ≤ p ^ h) :
    (∑ i ∈ Finset.range W, (M.bad p (fun u v => M.fockK (tiePhi w e o n (z0 + i) (T u)) v / dF)
        (Submodule.span ℤ_[p] (Set.range f)) k : ℝ)) ≤
      (W : ℝ) * ((n₁ : ℝ) * (((min o n : ℕ) : ℝ) / W +
        (((x0 : ℝ) + D1z + Λ) + ((min o n : ℕ) : ℝ) * h / W) / ((k : ℝ) + 1))) := by
  set J := min o n with hJ
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set c : Fin n₁ → Fin n₁ → ℕ → ℚ_[p] := fun a b =>
    cW (o + n + r - 1) J (fun l => (p : ℚ_[p]) ^ x0 * (mX w e J l (T (f a)) (f b) / dF)) with hc
  have hlb := lead_bound p n₁ J c (fun a => (p : ℚ_[p]) ^ x0 * (M.fockK (T (f a)) (f a) / dF))
    (fun a b => by
      simp only [hc]
      rw [cW_top, mX_zero]
      split_ifs with hab
      · rw [hab]
      · rw [horth a b hab, mul_zero])
    ((x0 : ℝ) + D1z) Λ
    (fun a => ⟨mul_ne_zero (pow_ne_zero _ hp0) (hsmall a).1, by
      rw [neglog_pow_mul x0 _ (hsmall a).1]
      have : ((M.fockK (T (f a)) (f a) / dF).valuation : ℝ) ≤ (D1z : ℝ) := by exact_mod_cast (hsmall a).2
      linarith⟩) hV
  refine hGW p σ n₁ J h W k ((x0 : ℝ) + D1z + Λ) z0
    (fun i u v => M.fockK (tiePhi w e o n (z0 + i) (T u)) v / dF) f
    (fun i => (p : ℚ_[p]) ^ x0 * ((o + n + r + (z0 + i) - 1).choose J : ℚ_[p])) c hli
    (fun i a u v => by
      show M.fockK (tiePhi w e o n (z0 + i) (T (a • u))) v / dF = _
      rw [map_smul, map_smul, ProjS.fockK_smul_left, mul_div_assoc])
    (fun i u u' v => by
      show M.fockK (tiePhi w e o n (z0 + i) (T (u + u'))) v / dF = _
      rw [map_add (f := _), map_add (f := _), ProjS.fockK_add_left, add_div])
    (fun i a u v => by
      show M.fockK (tiePhi w e o n (z0 + i) (T u)) (a • v) / dF = _
      rw [ProjS.fockK_smul_right, mul_div_assoc])
    (fun i u v v' => by
      show M.fockK (tiePhi w e o n (z0 + i) (T u)) (v + v') / dF = _
      rw [ProjS.fockK_add_right, add_div])
    hW hWh hJh hk (fun a b i => cW_norm _ _ _ (fun l hl => hint l hl a b) i) hlb.1 hlb.2 ?_
  intro i _
  have hJM : J ≤ o + n + r + (z0 + i) - 1 := by omega
  refine ⟨mul_ne_zero (pow_ne_zero _ hp0) (by exact_mod_cast (Nat.choose_pos hJM).ne'), ?_, fun a b => ?_⟩
  · rw [norm_mul, norm_pow, Padic.norm_p]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    have h1 : ‖(((o + n + r + (z0 + i) - 1).choose J : ℕ) : ℚ_[p])‖ ≤ 1 := by
      rw [← PadicInt.coe_natCast, ← PadicInt.norm_def]; exact PadicInt.norm_le_one _
    have h2 : ((p : ℝ)⁻¹) ^ x0 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [Matrix.map_apply, Formalism.GM.MeanGammaLemmas.binMatK_eval_nat]
    simp only [hc]
    rw [cW_sum (o + n + r - 1) J (z0 + i) (by omega)]
    have hpp := phi_pair w e hw he hwe hr o n (z0 + i) (T (f a)) (f b) (hbi b)
    rw [← hJ] at hpp
    calc (p : ℚ_[p]) ^ x0 * ((o + n + r + (z0 + i) - 1).choose J : ℚ_[p]) *
          (M.fockK (tiePhi w e o n (z0 + i) (T (f a))) (f b) / dF)
        = (p : ℚ_[p]) ^ x0 * ((((o + n + r + (z0 + i) - 1).choose J : ℚ_[p]) *
          M.fockK (tiePhi w e o n (z0 + i) (T (f a))) (f b)) / dF) := by ring
      _ = _ := by
        rw [hpp, Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l hl => ?_
        have hl' : l ≤ J := by simp only [mem_range] at hl; omega
        rw [show o + n + r - 1 + (z0 + i) - l = o + n + r + (z0 + i) - 1 - l by omega]
        ring

end Formalism.MainNotions.G.GramWindowAlt

end
end

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.MainNotions.G.SymmetricFormBlocks

abbrev setZ {N : ℕ} (G : M.BlockData N) (z : ℕ) : M.BlockData N := ⟨G.LL, G.T, G.uPos, G.B, z⟩

def lgN (p A r : ℕ) : ℕ := Nat.log p (8 * A + r) + 1

def x0N (p A r N t : ℕ) : ℕ := ((t + 1) * (r + 1) + ((N + 1) * r + (t + 1) * 2)) * lgN p A r

def JN {N : ℕ} (G : M.BlockData N) (jp : ℕ) : ℕ := min (G.LL.deg G.uPos - jp) (G.B - jp)

def WinLvl : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (G : M.BlockData N), G.BlockOK →
    ∀ (j : Fin G.T.t → ℕ) (jp : ℕ), G.LevelOK j jp → ∀ (A : ℕ), 1 ≤ A → (∀ x, G.LL.deg x ≤ 2 * A) → G.B ≤ 2 * A →
    (∀ i, G.T.z i ≤ 2 * A) →
    ∀ (n₁ : ℕ) (f : Fin n₁ → MvPolynomial (M.BVar N r G.T.t) ℚ_[p]),
      (∀ a, f a ∈ Ljj p (r := r) G j jp) → LinearIndependent ℤ_[p] f →
      (∀ a b, a ≠ b → bePhi p (r := r) G j jp (f a) (f b) = 0) →
      ∀ D : ℤ, (∀ a, bePhi p (r := r) G j jp (f a) (f a) ≠ 0 ∧ (bePhi p (r := r) G j jp (f a) (f a)).valuation ≤ D) →
      ∀ (z0 W h : ℕ) (k : ℤ), 0 ≤ k → 0 < W → W ≤ p ^ h → JN G jp + 1 ≤ p ^ h →
        (∑ i ∈ Finset.range W, (M.bad p (bejj p (r := r) (setZ G (z0 + i)) j jp)
            (Submodule.span ℤ_[p] (Set.range f)) k : ℝ)) ≤
          (W : ℝ) * ((n₁ : ℝ) * ((JN G jp : ℝ) / W +
            (((x0N p A r N G.T.t : ℝ) + D + lgN p A r) + (JN G jp : ℝ) * h / W) / ((k : ℝ) + 1)))

end Formalism.MainNotions.G.GramWindowAlt

end
