module

public import Formalism.GaussJetBounds.OneLetterRadius
public import Formalism.GaussJetBounds.StatementM

@[expose] public section

section -- merged from Formalism.GaussJetBounds.GaussJetProofs.LemmaRA
noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem factValA {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ}
    (hl : l.Prime) (hlt : ‖(l : K)‖ < 1) {ι : Type v} [Fintype ι] (κ : ι →₀ ℕ) {a : ℕ}
    (ha : 1 ≤ a) (hκa : ∀ i, κ i ≤ a) :
    ‖((mfact κ : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
        (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) := by
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  set L : ℝ := Real.logb l (a : ℝ) + 1 with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.logb l (a : ℝ) := Real.logb_nonneg hl1 (by exact_mod_cast ha)
    linarith
  have hcoord : ∀ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖ ≤
      ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) := by
    intro i hi
    have hki : 1 ≤ κ i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have hb := (Formalism.IncomingBounds.padicValFactorialBounds l hl (κ i) hki).1
    have hlog : Real.logb l (κ i : ℝ) ≤ Real.logb l (a : ℝ) :=
      Real.logb_le_logb_of_le hl1 (by exact_mod_cast hki) (by exact_mod_cast hκa i)
    rw [norm_natCast_eq_pow_padicValNat hl hlt (Nat.factorial_ne_zero _), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by rw [hL]; linarith)
  have hmf : ((mfact κ : ℕ) : K) = ∏ i ∈ κ.support, (((κ i).factorial : ℕ) : K) := by
    rw [mfact, Finsupp.prod, Nat.cast_prod]
  rw [hmf, norm_prod]
  calc ∏ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖
      ≤ ∏ i ∈ κ.support, ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hcoord
    _ = ‖(l : K)‖ ^ (∑ i ∈ κ.support, ((κ i : ℝ) / ((l : ℝ) - 1) - L)) :=
        (Real.rpow_sum_of_pos hpi0 _ _).symm
    _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - (Fintype.card ι : ℝ) * L) := by
        apply Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        have hsum : ∑ i ∈ κ.support, (κ i : ℝ) / ((l : ℝ) - 1) =
            ∑ i, (κ i : ℝ) / ((l : ℝ) - 1) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          rw [Finsupp.notMem_support_iff.mp hi]; simp
        have hcard : (κ.support.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast Finset.card_le_univ _
        rw [hsum]
        nlinarith

theorem lemmaRA_of (hS : LemmaS.{u}) (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u})
    (hW1 : SubstWt.{u, 0, v}) (hW0 : SubstWt.{u, 0, 0}) (hRM : RadMono.{u, v})
    (hMW : MulWtLe.{u, v}) (hE : ExpWtLe.{u, v})
    (hP : PureCross.{u, v}) : LemmaRA.{u, v} := by
  intro K _ _ _ l d N0 N1 _ hl hodd hd hde hpi K0 hK0 ζ hζ be hbe ι _ _ lt M hM1 hMlt g hg0 hg
    U hU ε hε sig hsig κ a ha hκa hκ
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have h1 : ‖(l : K)‖ ≤ 1 := hpi.le
  have hrho : 0 ≤ rho l := by
    unfold rho
    apply div_nonneg zero_le_one
    nlinarith
  have hrg : gam l = 1 / ((l : ℝ) - 1) - rho l := by
    have ha : (l : ℝ) - 1 ≠ 0 := by linarith
    have hb : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    unfold gam rho
    field_simp
    ring
  obtain ⟨hS1, hS2⟩ := hS K l d hl hodd hd hde hpi K0 hK0 ζ hζ be hbe
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra h
    have h' : MvPowerSeries.coeff 0 be ≠ 0 := by
      rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have := (hbe.2.2.1 0 h').1
    simp [degE] at this
  obtain ⟨hP1, hP2⟩ := hP K l d N0 N1 hl hpi ι M hM1 be hbe0 hS1 hS2
  have hlin0 : ∀ x, MvPowerSeries.constantCoeff (linSub M x) = 0 := by
    intro x
    simp [linSub]
  have hbS0 : MvPowerSeries.constantCoeff (bSum M be) = 0 := by
    unfold bSum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun ab _ => ?_
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => hlin0 _) (fun s => hlin0 _) hbe0
  have hr : ∀ i, (fun _ : ι => rho l) i ≤ (fun i => rho l + sig i) i := fun i => by
    simp only
    linarith [hsig i]

  have hBw : WtGeLe ‖(l : K)‖ (fun i => rho l + sig i) (1 / ((l : ℝ) - 1)) κ
      (ε • bSum M be) := by
    intro n hn
    have hεn : ‖ε‖ = 1 := by rcases hε with h | h <;> simp [h]
    have hc : MvPowerSeries.coeff n (ε • bSum M be) = ε * MvPowerSeries.coeff n (bSum M be) := by
      rw [map_smul, smul_eq_mul]
    rw [monoWtGe_iff, hc, norm_mul, hεn, one_mul]
    by_cases hp : ∃ (i j : ι) (α β : ℕ), n = pureMon l i j α β
    · obtain ⟨i, j, α, β, rfl⟩ := hp
      by_cases hw : MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
          (MvPowerSeries.coeff (pureMon l i j α β) (bSum M be))
      · exact asmR_monoWtGe_rad h0 h1 hr hw
      · have hs1 := hκ i j α β hn hw
        have hlow := hP1 (pureMon l i j α β)
        rw [monoWtGe_iff] at hlow
        refine le_trans hlow (Real.rpow_le_rpow_of_exponent_ge h0 h1 ?_)
        rw [asmR_dot_add_right, asmR_dot_pureMon l i j α β sig]
        linarith
    · exact asmR_monoWtGe_rad h0 h1 hr (hP2 n hp)
  have hBc : MvPowerSeries.constantCoeff (ε • bSum M be) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_smul,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hbS0, smul_zero]
  have hExp := hE K l hl hpi ι (fun i => rho l + sig i) κ (ε • bSum M be) hBc hBw

  have hU0 : WtGe ‖(l : K)‖ (fun _ : ZV d N0 N1 => rho l) 0 U := by
    intro n
    rw [monoWtGe_iff]
    refine le_trans (hU n) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 ?_)
    linarith [asmR_dot_nonneg n (r := fun _ : ZV d N0 N1 => rho l) fun _ => hrho]
  have hg' : ∀ x, MvPowerSeries.subst g (genLog (K := K) l
      (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) x) = MvPowerSeries.X x := by
    intro x
    rw [← (hB K l d N0 N1).2.1 x]
    exact hg x
  have hgw := hG K l hl hpi (ZV d N0 N1) (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) g hg0 hg'
  have hgU : WtGe ‖(l : K)‖ (fun _ : ZV d N0 N1 => rho l) 0 (MvPowerSeries.subst g U) :=
    hW0 K ‖(l : K)‖ h0 hpi (ZV d N0 N1) (ZV d N0 N1) g (fun _ => rho l) (fun _ => rho l) 0 U
      hg0 hgw hU0
  have hlinw : ∀ x, WtGe ‖(l : K)‖ (fun _ : ι => rho l) (rho l) (linSub M x) := by
    intro x n
    rw [monoWtGe_iff]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [linSub, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
      fun i _ => ?_
    split_ifs with h
    · subst h
      rw [mul_one, asmR_dot_single]
      simpa using hM1 x i
    · simpa using Real.rpow_nonneg h0.le _
  have hY : WtGe ‖(l : K)‖ (fun _ : ι => rho l) 0
      (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U)) :=
    hW1 K ‖(l : K)‖ h0 hpi (ZV d N0 N1) ι (linSub M) (fun _ => rho l) (fun _ => rho l) 0 _
      hlin0 hlinw hgU
  have hY1 : WtGeLe ‖(l : K)‖ (fun i => rho l + sig i) 0 κ
      (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U)) :=
    (hRM K ‖(l : K)‖ h0 hpi ι (fun _ => rho l) (fun i => rho l + sig i) 0 hr).2 κ _
      fun n _ => hY n
  have hk := hMW K ‖(l : K)‖ h0 ι (fun i => rho l + sig i) 0 0 κ _ _ hY1 hExp κ le_rfl
  rw [monoWtGe_iff] at hk
  have hf := factValA (K := K) hl hpi κ ha hκa
  rw [norm_mul]
  calc _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
          (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) *
        ‖(l : K)‖ ^ (0 + 0 - dot κ (fun i => rho l + sig i)) :=
        mul_le_mul hf hk (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = _ := by
      rw [← Real.rpow_add h0]
      congr 1
      rw [asmR_dot_fintype, hrg]
      have key : ∑ i, (κ i : ℝ) * (1 / ((l : ℝ) - 1) - rho l - sig i) =
          (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * (rho l + sig i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith

theorem lemma_R_log_loss : LemmaRA.{u, v} :=
  lemmaRA_of lemmaS generalized_log_weight logarithm_weight_comparison substitution_weight_bound substitution_weight_bound radical_weight_monotone
    multiplicative_weight_le exponential_weight_le pure_cross_term_weight

end Formalism.DworkPowerSeriesWeights
end
end

section -- merged from Formalism.GaussJetBounds.GaussJetProofs.GField
noncomputable section
open scoped BigOperators NNReal

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial

section Gauss

variable {F : Type} [NormedField F] {σ : Type}

def gN (P : MvPolynomial σ F) : ℝ := ⨆ n : σ →₀ ℕ, ‖AddMonoidAlgebra.coeff P n‖

lemma gN_bdd (P : MvPolynomial σ F) : BddAbove (Set.range fun n : σ →₀ ℕ => ‖AddMonoidAlgebra.coeff P n‖) := by
  refine ⟨∑ n ∈ P.support, ‖AddMonoidAlgebra.coeff P n‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n ∈ P.support
  · exact Finset.single_le_sum (f := fun n => ‖AddMonoidAlgebra.coeff P n‖) (fun _ _ => norm_nonneg _) hn
  · show ‖AddMonoidAlgebra.coeff P n‖ ≤ _
    rw [notMem_support_iff.mp hn, norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma le_gN (P : MvPolynomial σ F) (n : σ →₀ ℕ) : ‖AddMonoidAlgebra.coeff P n‖ ≤ gN P :=
  le_ciSup (gN_bdd P) n

lemma gN_nonneg (P : MvPolynomial σ F) : 0 ≤ gN P := (norm_nonneg _).trans (le_gN P 0)

lemma gN_le {P : MvPolynomial σ F} {c : ℝ} (h : ∀ n, ‖AddMonoidAlgebra.coeff P n‖ ≤ c) : gN P ≤ c :=
  ciSup_le h

lemma gN_zero : gN (0 : MvPolynomial σ F) = 0 :=
  le_antisymm (gN_le fun n => by simp) (gN_nonneg _)

lemma gN_pos {P : MvPolynomial σ F} (hP : P ≠ 0) : 0 < gN P := by
  obtain ⟨n, hn⟩ := ne_zero_iff.mp hP
  exact (norm_pos_iff.mpr hn).trans_le (le_gN P n)

lemma gN_eq_zero {P : MvPolynomial σ F} : gN P = 0 ↔ P = 0 := by
  constructor
  · intro h
    by_contra hP
    exact (gN_pos hP).ne' h
  · rintro rfl
    exact gN_zero

lemma gN_C (z : F) : gN (C z : MvPolynomial σ F) = ‖z‖ := by
  classical
  apply le_antisymm
  · refine gN_le fun n => ?_
    rw [coeff_C]
    split_ifs
    · exact le_rfl
    · simp
  · simpa using le_gN (C z : MvPolynomial σ F) 0

lemma exists_min_gN [LinearOrder σ] {P : MvPolynomial σ F} (hP : P ≠ 0) :
    ∃ i : σ →₀ ℕ, ‖AddMonoidAlgebra.coeff P i‖ = gN P ∧ ∀ k : σ →₀ ℕ, toLex k < toLex i → ‖AddMonoidAlgebra.coeff P k‖ < gN P := by
  classical
  have hne : P.support.Nonempty := support_nonempty.mpr hP
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image P.support (fun n => ‖AddMonoidAlgebra.coeff P n‖) hne
  have hmg : ‖AddMonoidAlgebra.coeff P m‖ = gN P := by
    refine le_antisymm (le_gN P m) (gN_le fun n => ?_)
    by_cases hn : n ∈ P.support
    · exact hmax n hn
    · rw [notMem_support_iff.mp hn, norm_zero]
      exact norm_nonneg _
  let S := P.support.filter fun n => ‖AddMonoidAlgebra.coeff P n‖ = gN P
  have hS : S.Nonempty := ⟨m, Finset.mem_filter.mpr ⟨hm, hmg⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S (fun n => toLex n) hS
  refine ⟨i, (Finset.mem_filter.mp hi).2, fun k hk => lt_of_le_of_ne (le_gN P k) fun hkg => ?_⟩
  have hkS : k ∈ S := by
    refine Finset.mem_filter.mpr ⟨?_, hkg⟩
    rw [mem_support_iff]
    intro h0
    rw [h0, norm_zero] at hkg
    exact (gN_pos hP).ne hkg
  exact absurd (hmin k hkS) (not_le.mpr hk)

variable [IsUltrametricDist F]

lemma gN_add_le (P Q : MvPolynomial σ F) : gN (P + Q) ≤ max (gN P) (gN Q) := by
  refine gN_le fun n => ?_
  rw [MvPolynomial.coeff_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (le_gN P n) (le_gN Q n))

lemma gN_mul_le (P Q : MvPolynomial σ F) : gN (P * Q) ≤ gN P * gN Q := by
  classical
  refine gN_le fun n => ?_
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (gN_nonneg P) (gN_nonneg Q)) fun p _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_gN P _) (le_gN Q _) (norm_nonneg _) (gN_nonneg P)

lemma gN_mul (P Q : MvPolynomial σ F) : gN (P * Q) = gN P * gN Q := by
  classical
  by_cases hP : P = 0
  · simp [hP, gN_zero]
  by_cases hQ : Q = 0
  · simp [hQ, gN_zero]
  refine le_antisymm (gN_mul_le P Q) ?_
  obtain ⟨_, _⟩ := exists_wellFoundedLT σ
  obtain ⟨i, hi, hi'⟩ := exists_min_gN hP
  obtain ⟨j, hj, hj'⟩ := exists_min_gN hQ
  have key : ‖AddMonoidAlgebra.coeff (P * Q) (i + j)‖ = ‖AddMonoidAlgebra.coeff P i * AddMonoidAlgebra.coeff Q j‖ := by
    rw [coeff_mul]
    refine IsNonarchimedean.apply_sum_eq_of_lt (f := fun x : F => ‖x‖)
      (g := fun p : (σ →₀ ℕ) × (σ →₀ ℕ) => AddMonoidAlgebra.coeff P p.1 * AddMonoidAlgebra.coeff Q p.2) (k := (i, j))
      IsUltrametricDist.isNonarchimedean_norm (fun a => norm_neg a)
      (by simp) ?_
    rintro ⟨a, b⟩ hab hne
    replace hab : a + b = i + j := by simpa using hab
    simp only [norm_mul, hi, hj]
    have hcase : toLex a < toLex i ∨ toLex b < toLex j := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hsum : toLex a + toLex b = toLex i + toLex j := by
        rw [← toLex_add, ← toLex_add]
        exact congrArg toLex hab
      rcases h1.lt_or_eq with h1 | h1
      · exact absurd hsum (add_lt_add_of_lt_of_le h1 h2).ne'
      rcases h2.lt_or_eq with h2 | h2
      · exact absurd hsum (add_lt_add_of_le_of_lt h1.le h2).ne'
      exact hne (Prod.ext (toLex.injective h1.symm) (toLex.injective h2.symm))
    rcases hcase with h | h
    · exact (mul_le_mul_of_nonneg_left (le_gN Q b) (norm_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_right (hi' a h) (gN_pos hQ))
    · exact (mul_le_mul_of_nonneg_right (le_gN P a) (norm_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_left (hj' b h) (gN_pos hP))
  calc gN P * gN Q = ‖AddMonoidAlgebra.coeff P i * AddMonoidAlgebra.coeff Q j‖ := by rw [norm_mul, hi, hj]
    _ = ‖AddMonoidAlgebra.coeff (P * Q) (i + j)‖ := key.symm
    _ ≤ gN (P * Q) := le_gN _ _

def gNN (P : MvPolynomial σ F) : ℝ≥0 := Real.toNNReal (gN P)

omit [IsUltrametricDist F] in
lemma coe_gNN (P : MvPolynomial σ F) : ((gNN P : ℝ≥0) : ℝ) = gN P :=
  Real.coe_toNNReal _ (gN_nonneg P)

def gVal (F σ : Type) [NormedField F] [IsUltrametricDist F] : Valuation (MvPolynomial σ F) ℝ≥0 where
  toFun P := gNN P
  map_zero' := by
    apply NNReal.coe_injective
    rw [coe_gNN, gN_zero, NNReal.coe_zero]
  map_one' := by
    apply NNReal.coe_injective
    have := gN_C (σ := σ) (1 : F)
    rw [coe_gNN, NNReal.coe_one]
    simpa using this
  map_mul' P Q := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, coe_gNN, coe_gNN, coe_gNN, gN_mul]
  map_add_le_max' P Q := by
    rw [← NNReal.coe_le_coe, NNReal.coe_max, coe_gNN, coe_gNN, coe_gNN]
    exact gN_add_le P Q

lemma gVal_coe (P : MvPolynomial σ F) : ((gVal F σ P : ℝ≥0) : ℝ) = gN P := coe_gNN P

lemma gVal_supp : nonZeroDivisors (MvPolynomial σ F) ≤ (gVal F σ).supp.primeCompl := by
  intro P hP hmem
  rw [SetLike.mem_coe, Valuation.mem_supp_iff] at hmem
  have h0 : gN P = 0 := by rw [← gVal_coe, hmem]; rfl
  exact nonZeroDivisors.ne_zero hP (gN_eq_zero.mp h0)

abbrev GK (F σ : Type) [NormedField F] : Type := FractionRing (MvPolynomial σ F)

def gValK (F σ : Type) [NormedField F] [IsUltrametricDist F] : Valuation (GK F σ) ℝ≥0 :=
  (gVal F σ).extendToLocalization gVal_supp (GK F σ)

lemma gValK_algebraMap (P : MvPolynomial σ F) :
    ((gValK F σ (algebraMap _ (GK F σ) P) : ℝ≥0) : ℝ) = gN P := by
  rw [gValK, Valuation.extendToLocalization_apply_map_apply, gVal_coe]

def gAbs (F σ : Type) [NormedField F] [IsUltrametricDist F] : AbsoluteValue (GK F σ) ℝ where
  toFun x := (gValK F σ x : ℝ≥0)
  map_mul' x y := by simp
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by simp
  add_le' x y := by
    have h := (gValK F σ).map_add x y
    rw [← NNReal.coe_le_coe, NNReal.coe_max] at h
    exact h.trans (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

lemma gAbs_add_le_max (x y : GK F σ) : gAbs F σ (x + y) ≤ max (gAbs F σ x) (gAbs F σ y) := by
  have h := (gValK F σ).map_add x y
  rw [← NNReal.coe_le_coe, NNReal.coe_max] at h
  exact h

lemma gAbs_algebraMap (P : MvPolynomial σ F) : gAbs F σ (algebraMap _ (GK F σ) P) = gN P :=
  gValK_algebraMap P

end Gauss

lemma norm_intCast_padicComplex (l : ℕ) [Fact l.Prime] (z : ℤ) :
    ‖(z : ℂ_[l])‖ = ‖(z : ℚ_[l])‖ := by
  rw [← map_intCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']

lemma gN_map_int (l : ℕ) [Fact l.Prime] {σ : Type} (P : MvPolynomial σ ℤ)
    (hP : MvPolynomial.map (Int.castRingHom (ZMod l)) P ≠ 0) :
    gN (MvPolynomial.map (Int.castRingHom ℂ_[l]) P) = 1 := by
  apply le_antisymm
  · refine gN_le fun n => ?_
    rw [coeff_map, eq_intCast, norm_intCast_padicComplex]
    exact Padic.norm_int_le_one _
  · obtain ⟨n, hn⟩ := ne_zero_iff.mp hP
    rw [coeff_map, eq_intCast] at hn
    have hnd : ¬ (l : ℤ) ∣ AddMonoidAlgebra.coeff P n := fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
    have h1 : ‖((AddMonoidAlgebra.coeff P n : ℤ) : ℚ_[l])‖ = 1 :=
      le_antisymm (Padic.norm_int_le_one _)
        (not_lt.mp fun h => hnd (Padic.norm_intCast_lt_one_iff.mp h))
    have := le_gN (MvPolynomial.map (Int.castRingHom ℂ_[l]) P) n
    rwa [coeff_map, eq_intCast, norm_intCast_padicComplex, h1] at this

lemma eval₂_ringHom_eq {σ A K : Type} [CommRing A] [CommRing K] (ι : MvPolynomial σ A →+* K)
    (P : MvPolynomial σ A) : eval₂ (ι.comp C) (fun i => ι (X i)) P = ι P := by
  have := eval₂_comp_left ι (C : A →+* MvPolynomial σ A) X P
  rw [eval₂_eta] at this
  exact this.symm

lemma aeval_int_eq {σ A K : Type} [CommRing A] [CommRing K] [Algebra ℤ K]
    (ι : MvPolynomial σ A →+* K) (P : MvPolynomial σ ℤ) :
    aeval (fun i => ι (X i)) P = ι (MvPolynomial.map (Int.castRingHom A) P) := by
  rw [aeval_def, ← eval₂_ringHom_eq, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem residuallyGenericExists : GenericExists := by
  intro l _ σ _
  let inst : NormedField (GK ℂ_[l] σ) := (gAbs ℂ_[l] σ).toNormedField
  let ι : MvPolynomial σ ℂ_[l] →+* GK ℂ_[l] σ := algebraMap _ _
  have hι : ∀ P, ‖ι P‖ = gN P := fun P => gAbs_algebraMap P
  have hev : ∀ P, eval₂ (ι.comp C) (fun i => ι (X i)) P = ι P := eval₂_ringHom_eq ι
  refine ⟨GK ℂ_[l] σ, inst, ?_, ?_, ι.comp C, fun i => ι (X i), ?_, ?_, ?_⟩
  · exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      fun x y => gAbs_add_le_max x y
  · exact charZero_of_injective_ringHom (ι.comp C).injective
  · intro z
    rw [RingHom.comp_apply, hι, gN_C]
  · intro P
    rw [hev, hι]
    rfl
  · intro P hP
    refine (congrArg norm (@aeval_int_eq σ ℂ_[l] (GK ℂ_[l] σ) _ _ (Ring.toIntAlgebra _) ι P)).trans ?_
    rw [hι]
    exact gN_map_int l P hP

end Formalism.DworkPowerSeriesWeights
end
end
