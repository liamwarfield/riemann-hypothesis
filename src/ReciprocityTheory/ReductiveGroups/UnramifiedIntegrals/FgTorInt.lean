module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnWp
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgIsoU
section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnIso
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

section MapLemmas

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem anIso_map_dblInt (e : PowerSeries K) :
    PowerSeries.map φ (C.dblInt e) = C.dblInt (PowerSeries.map φ e) := by
  ext n
  simp only [C.dblInt, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs
  · simp
  · simp [map_div₀]

theorem anIso_constantCoeff_dblInt (e : PowerSeries K) :
    PowerSeries.constantCoeff (C.dblInt e) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [C.dblInt]

theorem anIso_map_lam (e : PowerSeries K) (s2 : K) :
    PowerSeries.map φ (C.lam e s2) = C.lam (PowerSeries.map φ e) (φ s2) := by
  simp only [C.lam, map_add (f := _), map_mul, map_pow, anIso_map_dblInt, PowerSeries.map_C, PowerSeries.map_X,
    map_div₀, map_ofNat]

theorem anIso_constantCoeff_lam (e : PowerSeries K) (s2 : K) :
    PowerSeries.constantCoeff (C.lam e s2) = 0 := by
  simp [C.lam, anIso_constantCoeff_dblInt]

theorem anIso_map_sgStar [CharZero K] [CharZero K'] (e : PowerSeries K) (s2 : K) :
    PowerSeries.map φ (C.sgStar e s2) = C.sgStar (PowerSeries.map φ e) (φ s2) := by
  have h0 : PowerSeries.constantCoeff (-(C.lam e s2)) = 0 := by
    simp [anIso_constantCoeff_lam]
  have h1 : PowerSeries.map φ (C.mvExp (-(C.lam e s2)))
      = C.mvExp (-(C.lam (PowerSeries.map φ e) (φ s2))) := by
    unfold C.mvExp
    have := PowerSeries.map_subst (h := φ) (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
      (PowerSeries.exp K)
    rw [PowerSeries.map_exp] at this
    rw [← anIso_map_lam, ← map_neg]
    exact this
  rw [C.sgStar, map_mul, PowerSeries.map_X, h1, C.sgStar]

theorem anIso_map_wpShift (e : PowerSeries K) (c : K) :
    PowerSeries.map φ (C.wpShift e c) = C.wpShift (PowerSeries.map φ e) (φ c) := by
  simp only [C.wpShift, map_add (f := _), map_one, map_mul, map_pow, map_sub, PowerSeries.map_C,
    PowerSeries.map_X]

end MapLemmas

theorem isogenyFormula_map {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
    (φ : K →+* K') (e : PowerSeries K) (s2 : K) {κ : Type} [Fintype κ] (c : κ → K) (al : K)
    (h : C.IsogenyFormula e s2 c al) :
    C.IsogenyFormula (PowerSeries.map φ e) (φ s2) (fun P => φ (c P)) (φ al) := by
  have h' := congrArg (PowerSeries.map φ) h
  unfold C.IsogenyFormula
  simp only [map_mul, map_pow, map_prod, PowerSeries.map_X, PowerSeries.map_C, anIso_map_wpShift,
    anIso_map_sgStar, ← PowerSeries.rescale_map] at h'
  rw [map_pow]
  exact h'

theorem iso_formula (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : F.MulStable L α) (hS : F.IsKerReps L α S) :
    C.IsogenyFormula (A.wpReg (A.shortW (ι L.g₂) (ι L.g₃))) (ι (F.s2 L))
      (fun P : S => ι (L.weierstrassP (P : ℂ))) (ι α) := by
  rw [wp_bridge]
  exact isogenyFormula_map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) (F.s2 L)
    (fun P : S => L.weierstrassP (P : ℂ)) α (F.isogenyFormulaInstance L α S hα hst hS)

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgPhInt
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem phNorm_int {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hF : C.Frame R l linv ph) (h1 : C.F1 R l linv ph) (hneg : C.PhNormAt R l linv ph (-1) (-1))
    (h2 : (2 : K)⁻¹ ∈ R) (n : ℤ) : C.PhNormAt R l linv ph (n : K) (n : K) := by
  have hl : C.IsLogPair l linv := hF.1
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have hXpt : C.IsPt R (PowerSeries.X : MvPowerSeries Unit K) := C.Pts.isPt_X

  set q : K → MvPowerSeries Unit K :=
    fun a => PowerSeries.subst (C.fmul l linv a (PowerSeries.X : MvPowerSeries Unit K)) ph with hq
  set B : MvPowerSeries Unit K :=
    C.be0 l linv ph (PowerSeries.X : MvPowerSeries Unit K) (PowerSeries.X : MvPowerSeries Unit K)
    with hB
  have hphX : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) ph = ph :=
    PowerSeries.X_subst ph

  have hE : ∀ m : ℤ, C.LG R (q (1 + (m : K)) - ph - q (m : K) - (m : K) • B) := by
    intro m
    have h := C.zLinInt K R l linv ph hF h1 m Unit _ _ hXpt hXpt
    unfold C.Cong at h
    rw [C.be0] at h
    have e : C.fadd l linv (PowerSeries.X : MvPowerSeries Unit K)
        (C.fmul l linv (m : K) (PowerSeries.X : MvPowerSeries Unit K)) =
        C.fmul l linv (1 + (m : K)) (PowerSeries.X : MvPowerSeries Unit K) := by
      rw [C.Pts.fmul_add hl 1 (m : K) hX, C.Pts.fmul_one hl hX]
    rw [e, hphX] at h
    exact h
  have hq0 : q 0 = 0 := by
    simp only [hq]
    rw [C.Pts.fmul_zero_left hl, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2]
  have hN : C.LG R (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K))) := by
    have h := hneg
    unfold C.PhNormAt C.Cong at h
    rw [C.Pts.mulBy_eq_fmul] at h
    exact h

  have hG : C.LG R (B - (2 : K) • (ph : MvPowerSeries Unit K)) := by
    have h := C.Calc.lg_add (hE (-1)) hN
    have e : (q (1 + ((-1 : ℤ) : K)) - ph - q ((-1 : ℤ) : K) - ((-1 : ℤ) : K) • B) +
        (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K))) =
        B - (2 : K) • (ph : MvPowerSeries Unit K) := by
      have e0 : (1 : K) + ((-1 : ℤ) : K) = 0 := by push_cast; ring
      have e1 : (((-1 : ℤ) : K)) = -1 := by push_cast; ring
      rw [e0, hq0, e1]
      module
    rwa [e] at h
  have hstep : ∀ m : ℤ, C.LG R ((q (((m + 1 : ℤ)) : K) -
      ((((m + 1 : ℤ)) : K) * (((m + 1 : ℤ)) : K)) • (ph : MvPowerSeries Unit K)) -
      (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K))) := by
    intro m
    have h := C.Calc.lg_add (hE m) (C.lGBinom K R Unit (m : K) (C.intBinomScalar K R m) _ hG)
    have e1 : (((m + 1 : ℤ)) : K) = 1 + (m : K) := by push_cast; ring
    rw [e1]
    convert h using 1
    module
  have main : ∀ m : ℤ, C.LG R (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K)) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      have : q ((0 : ℤ) : K) - (((0 : ℤ) : K) * ((0 : ℤ) : K)) • (ph : MvPowerSeries Unit K) = 0 := by
        rw [Int.cast_zero, hq0]; simp
      rw [this]; exact C.Calc.lg_zero
    | succ i ih =>
      have h := C.Calc.lg_add (hstep i) ih
      rwa [sub_add_cancel] at h
    | pred i ih =>
      have h := C.Calc.lg_add (C.Calc.lg_neg (hstep (-(i : ℤ) - 1))) ih
      rw [sub_add_cancel] at h
      convert h using 1
      abel
  have h := main n
  unfold C.PhNormAt C.Cong
  rw [C.Pts.mulBy_eq_fmul]
  exact h

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem exists_powerSeries_square_formula {K : Type} [Field K] [CharZero K] (R : Subring K) (M a ph G : PowerSeries K)
    (c : ℕ) (m : K) (ha : constantCoeff a = 0) (hph : constantCoeff ph = 0)
    (hc : (c : K) + 1 = m)
    (hiso : M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c) =
      G * X ^ (2 * (c + 1)) * C.mvExp (-((2 * ((c : K) + 1)) • ph)))
    (hcong : C.Cong R a (m • ph)) :
    ∃ U : PowerSeries K, constantCoeff U = 1 ∧ C.IntPS R U ∧ M ^ 2 = X ^ 2 * U * G := by
  obtain ⟨h0, h1, hadd, -⟩ := C.mvExpLaws K Unit
  obtain ⟨-, hLadd, -⟩ := C.lGSubgroup K R Unit
  have hD : C.LG R ((a - m • ph) + (a - m • ph)) := hLadd _ _ hcong hcong
  have ha' : MvPowerSeries.constantCoeff a = 0 := ha
  have hph' : MvPowerSeries.constantCoeff ph = 0 := hph
  have c1 : MvPowerSeries.constantCoeff (-((2 : K) • a)) = 0 := by
    rw [map_neg, MvPowerSeries.smul_eq_C_mul, map_mul, ha', mul_zero, neg_zero]
  have c2 : MvPowerSeries.constantCoeff ((2 : K) • a) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, ha', mul_zero]
  have c3 : MvPowerSeries.constantCoeff (-((2 * ((c : K) + 1)) • ph)) = 0 := by
    rw [map_neg, MvPowerSeries.smul_eq_C_mul, map_mul, hph', mul_zero, neg_zero]
  refine ⟨C.mvExp ((a - m • ph) + (a - m • ph)), h1 _ hD.1, fun n => hD.2 _, ?_⟩
  have e1 : C.mvExp (-((2 : K) • a)) * C.mvExp ((2 : K) • a) = 1 := by
    rw [← hadd _ _ c1 c2, neg_add_cancel, h0]
  have e2 : C.mvExp (-((2 * ((c : K) + 1)) • ph)) * C.mvExp ((2 : K) • a)
      = C.mvExp ((a - m • ph) + (a - m • ph)) := by
    rw [← hadd _ _ c3 c2, hc]
    congr 1
    rw [mul_smul, two_smul, two_smul]
    abel
  have hX : (X : PowerSeries K) ^ (2 * c) ≠ 0 := pow_ne_zero _ X_ne_zero
  apply mul_right_cancel₀ hX
  calc M ^ 2 * X ^ (2 * c)
      = (M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c)) * C.mvExp ((2 : K) • a) := by
        rw [show M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c) * C.mvExp ((2 : K) • a)
          = M ^ 2 * X ^ (2 * c) * (C.mvExp (-((2 : K) • a)) * C.mvExp ((2 : K) • a)) by ring,
          e1, mul_one]
    _ = G * X ^ (2 * (c + 1)) *
          (C.mvExp (-((2 * ((c : K) + 1)) • ph)) * C.mvExp ((2 : K) • a)) := by
        rw [hiso]; ring
    _ = X ^ 2 * C.mvExp ((a - m • ph) + (a - m • ph)) * G * X ^ (2 * c) := by
        rw [e2]; ring

theorem sq_formula (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (n : ℕ) (hn : 0 < n) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) :
    ∃ U : PowerSeries ℂ_[l], constantCoeff U = 1 ∧ IntegralPS U ∧
      ((uSer g2 g3).subst (C (n : ℂ_[l]) * lgS g2 g3)) ^ 2 =
        X ^ 2 * U * (C ((n : ℂ_[l]) ^ 2) *
          ∏ P ∈ S, (A.xS (A.shortW g2 g3) - C (ι (L.weierstrassP P)) * X ^ 2)) := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have : ¬ l ∣ 2 := fun hd => hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
    exact_mod_cast norm_natCast_Cl_of_not_dvd l this
  have h2R : (2 : ℂ_[l])⁻¹ ∈ unitBall ℂ_[l] := by
    change ‖(2 : ℂ_[l])⁻¹‖ ≤ 1
    rw [norm_inv, h2, inv_one]
  have h4 : ‖(4 : ℂ_[l])‖ = 1 := by
    have : (4 : ℂ_[l]) = 2 * 2 := by norm_num
    rw [this, norm_mul, h2, one_mul]
  set W := A.shortW g2 g3 with hW
  have hco : C.CoeffIn (unitBall ℂ_[l]) W := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (unitBall ℂ_[l]).zero_mem
    · exact (unitBall ℂ_[l]).zero_mem
    · exact (unitBall ℂ_[l]).zero_mem
    · change ‖-g2 / 4‖ ≤ 1
      rw [norm_div, norm_neg, h4, div_one]; exact hM.n2
    · change ‖-g3 / 4‖ ≤ 1
      rw [norm_div, norm_neg, h4, div_one]; exact hM.n3
  have hb2 : W.b₂ / 12 = 0 := by
    rw [(A.shortInv ℂ_[l] g2 g3).1, zero_div]
  obtain ⟨hLP, hXW, -, hFG, -⟩ := C.curveFrame ℂ_[l] (unitBall ℂ_[l]) W hco
  set s2 : ℂ_[l] := ι (F.s2 L) with hs2
  set ph := B.phO s2 (A.wpReg W) (A.logSer W) with hph
  have hPh : C.IsPh (A.wpReg W) s2 (A.logSer W) ph :=
    (C.phOIsPh ℂ_[l] (A.wpReg W) (A.logSer W) s2 hLP.1 hLP.2.1).2
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hst : F.MulStable L (n : ℂ) := by
    intro ω hω
    have := L.lattice.nsmul_mem hω n
    rwa [nsmul_eq_mul] at this
  have hIF := iso_formula l L ι (n : ℂ) S hn0 hst hS
  rw [← hM.eq2, ← hM.eq3, map_natCast] at hIF
  have hcard : ((Fintype.card S : ℕ) : ℂ_[l]) + 1 = (n : ℂ_[l]) * (n : ℂ_[l]) := by
    have h := F.kerRepsCard L (n : ℂ) S hn0 hst hS
    rw [Complex.normSq_natCast] at h
    have h' : S.card + 1 = n * n := by exact_mod_cast h
    rw [Fintype.card_coe]
    exact_mod_cast h'
  have hU := C.isogenyU ℂ_[l] (A.wpReg W) s2 (A.logSer W) (A.expSer W) ph (A.xS W) (W.b₂ / 12) S
    (fun P : S => ι (L.weierstrassP (P : ℂ))) (n : ℂ_[l]) hLP hPh hXW
    (by simpa only [hb2, add_zero] using hIF)
  have hFr : C.Frame (unitBall ℂ_[l]) (A.logSer W) (A.expSer W) ph := ⟨hLP, hFG, hPh.1⟩
  have hN := phNorm_int (unitBall ℂ_[l]) (A.logSer W) (A.expSer W) ph hFr
    (G.weierstrass_biadditive_mod_equiv ℂ_[l] W hco h2 s2) (G.curveNegNorm ℂ_[l] (unitBall ℂ_[l]) W hco h2R s2) h2R (n : ℤ)
  rw [Int.cast_natCast] at hN
  have hMul : (uSer g2 g3).subst (C (n : ℂ_[l]) * lgS g2 g3)
      = C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l]) := by
    rw [lgS_eq_logSer, A.uSerEq ℂ_[l] g2 g3]; rfl
  have hM0 : constantCoeff (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) = 0 := by
    rw [← hMul]; exact mult_const g2 g3 _
  have ha : constantCoeff (PowerSeries.subst (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) ph) = 0 :=
    constantCoeff_subst_eq_zero hM0 _ hPh.1
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_powerSeries_square_formula (unitBall ℂ_[l])
    (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l]))
    (PowerSeries.subst (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) ph) ph
    (C ((n : ℂ_[l]) ^ 2) * ∏ P : S, (A.xS W - C (ι (L.weierstrassP (P : ℂ))) * X ^ 2))
    (Fintype.card S) ((n : ℂ_[l]) * (n : ℂ_[l])) ha hPh.1 hcard
    (by rw [hU]; ring) hN
  refine ⟨U, hU1, hU2, ?_⟩
  rw [hMul, hU3, Finset.prod_coe_sort S
    (fun P => A.xS W - C (ι (L.weierstrassP P)) * X ^ 2)]

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgGauss
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def LeadAt (f : PowerSeries K) (r : ℝ) (i : ℕ) : Prop :=
  0 < r ∧ (∀ n, ‖coeff n f‖ ≤ r) ∧ (∀ n, n < i → ‖coeff n f‖ < r) ∧ ‖coeff i f‖ = r

theorem gauss_norm_add_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem gauss_norm_sum_lt {α : Type} (s : Finset α) (f : α → K) {r : ℝ} (hr : 0 < r)
    (h : ∀ a ∈ s, ‖f a‖ < r) : ‖∑ a ∈ s, f a‖ < r := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hr
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
    exact hle.trans_lt (h i hi)

theorem LeadAt.mul {f g : PowerSeries K} {r s : ℝ} {i j : ℕ} (hf : LeadAt f r i) (hg : LeadAt g s j) :
    LeadAt (f * g) (r * s) (i + j) := by
  obtain ⟨hr, hf1, hf2, hf3⟩ := hf
  obtain ⟨hs, hg1, hg2, hg3⟩ := hg
  have small : ∀ p q : ℕ, (p < i ∨ q < j) → ‖coeff p f * coeff q g‖ < r * s := by
    intro p q hpq
    rw [norm_mul]
    rcases hpq with hp | hq
    · calc ‖coeff p f‖ * ‖coeff q g‖ ≤ ‖coeff p f‖ * s :=
            mul_le_mul_of_nonneg_left (hg1 q) (norm_nonneg _)
        _ < r * s := mul_lt_mul_of_pos_right (hf2 p hp) hs
    · calc ‖coeff p f‖ * ‖coeff q g‖ ≤ r * ‖coeff q g‖ :=
            mul_le_mul_of_nonneg_right (hf1 p) (norm_nonneg _)
        _ < r * s := mul_lt_mul_of_pos_left (hg2 q hq) hr
  refine ⟨mul_pos hr hs, fun n => ?_, fun n hn => ?_, ?_⟩
  · rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_pos hr hs).le fun x _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hf1 _) (hg1 _) (norm_nonneg _) hr.le
  · rw [coeff_mul]
    refine gauss_norm_sum_lt _ _ (mul_pos hr hs) fun x hx => small _ _ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    omega
  · have hmem : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have hlt : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i + j)).erase (i, j), coeff x.1 f * coeff x.2 g‖ < r * s := by
      refine gauss_norm_sum_lt _ _ (mul_pos hr hs) fun x hx => small _ _ ?_
      obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      by_contra hc
      push Not at hc
      exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
    have hij : ‖coeff i f * coeff j g‖ = r * s := by rw [norm_mul, hf3, hg3]
    rw [gauss_norm_add_of_lt (by rwa [hij]), hij]

theorem leadAt_one : LeadAt (1 : PowerSeries K) 1 0 := by
  refine ⟨one_pos, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), by simp⟩
  rw [coeff_one]
  split_ifs <;> simp

theorem leadAt_C {c : K} (hc : c ≠ 0) : LeadAt (C c : PowerSeries K) ‖c‖ 0 := by
  refine ⟨norm_pos_iff.mpr hc, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), by simp⟩
  rw [coeff_C]
  split_ifs <;> simp

theorem leadAt_factor {A : PowerSeries K} (hA : IntegralPS A) (hA0 : constantCoeff A = 1) (x : K) :
    ∃ i, i ≤ 2 ∧ LeadAt (A - C x * X ^ 2) (max 1 ‖x‖) i := by
  have hc : ∀ n, coeff n (A - C x * X ^ 2) = coeff n A - if n = 2 then x else 0 := by
    intro n
    rw [map_sub, coeff_C_mul_X_pow]
  by_cases hx : ‖x‖ ≤ 1
  · refine ⟨0, by norm_num, ?_⟩
    rw [max_eq_left hx]
    refine ⟨one_pos, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), ?_⟩
    · rw [hc]
      split_ifs
      · rw [sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA n) (by rw [norm_neg]; exact hx))
      · rw [sub_zero]; exact hA n
    · rw [hc, if_neg (by norm_num), sub_zero, coeff_zero_eq_constantCoeff_apply, hA0, norm_one]
  · push Not at hx
    refine ⟨2, le_rfl, ?_⟩
    rw [max_eq_right hx.le]
    have h2 : ‖coeff 2 A - x‖ = ‖x‖ := by
      rw [sub_eq_neg_add, gauss_norm_add_of_lt (by rw [norm_neg]; exact (hA 2).trans_lt hx), norm_neg]
    refine ⟨one_pos.trans hx, fun n => ?_, fun n hn => ?_, ?_⟩
    · rw [hc]
      split_ifs with h
      · subst h; exact h2.le
      · rw [sub_zero]; exact (hA n).trans hx.le
    · rw [hc, if_neg (by omega), sub_zero]
      exact (hA n).trans_lt hx
    · rw [hc, if_pos rfl, h2]

theorem leadAt_prod {α : Type} (S : Finset α) (x : α → K) {A : PowerSeries K} (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) :
    ∃ i, i ≤ 2 * S.card ∧ LeadAt (∏ P ∈ S, (A - C (x P) * X ^ 2)) (∏ P ∈ S, max 1 ‖x P‖) i := by
  classical
  refine Finset.induction_on S ⟨0, le_rfl, by simpa using leadAt_one⟩ ?_
  intro a T ha ih
  obtain ⟨i, hi, h⟩ := ih
  obtain ⟨j, hj, h'⟩ := leadAt_factor hA hA0 (x a)
  refine ⟨j + i, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem ha]; omega
  · rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact h'.mul h

theorem gauss_bound {α : Type} (S : Finset α) (x : α → K) (A : PowerSeries K) (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) (c : K)
    (hG : IntegralPS (C c * ∏ P ∈ S, (A - C (x P) * X ^ 2))) :
    ‖c‖ * ∏ P ∈ S, max 1 ‖x P‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨i, -, h⟩ := leadAt_prod S x hA hA0
  have hl := (leadAt_C hc).mul h
  rw [← hl.2.2.2]
  exact hG _

theorem gauss_unit {α : Type} (S : Finset α) (x : α → K) (A : PowerSeries K) (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) (c : K) (hc : ‖c‖ * ∏ P ∈ S, max 1 ‖x P‖ = 1) :
    ∃ i, i ≤ 2 * S.card ∧ ‖coeff i (C c * ∏ P ∈ S, (A - C (x P) * X ^ 2))‖ = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨i, hi, h⟩ := leadAt_prod S x hA hA0
  have hl := (leadAt_C hc0).mul h
  exact ⟨0 + i, by omega, hl.2.2.2.trans hc⟩

theorem leadAt_first_unit {g : PowerSeries K} (hg : IntegralPS g) (h : ∃ i, ‖coeff i g‖ = 1) :
    ∃ i₀, (∀ i, ‖coeff i g‖ = 1 → i₀ ≤ i) ∧ LeadAt g 1 i₀ := by
  classical
  refine ⟨Nat.find h, fun i hi => Nat.find_min' h hi, one_pos, hg,
    fun n hn => lt_of_le_of_ne (hg n) (Nat.find_min h hn), Nat.find_spec h⟩

theorem unit_coeff_mul {f g : PowerSeries K} (hf : IntegralPS f) (hg : IntegralPS g)
    (hf0 : ‖constantCoeff f‖ = 1) (N : ℕ) (h : ∃ i, i ≤ N ∧ ‖coeff i g‖ = 1) :
    ∃ i, i ≤ N ∧ ‖coeff i (f * g)‖ = 1 := by
  obtain ⟨i, hiN, hi⟩ := h
  obtain ⟨i₀, hmin, hl⟩ := leadAt_first_unit hg ⟨i, hi⟩
  have hf' : LeadAt f 1 0 := ⟨one_pos, hf, fun n hn => absurd hn (Nat.not_lt_zero _),
    by rw [coeff_zero_eq_constantCoeff_apply, hf0]⟩
  have hm := hf'.mul hl
  refine ⟨0 + i₀, by have := hmin i hi; omega, ?_⟩
  rw [hm.2.2.2, one_mul]

theorem unit_coeff_of_sq {e : PowerSeries K} (he : IntegralPS e) (N : ℕ)
    (h : ∃ i, i ≤ 2 * N ∧ ‖coeff i (e ^ 2)‖ = 1) : ∃ i, i ≤ N ∧ ‖coeff i e‖ = 1 := by
  obtain ⟨i, hiN, hi⟩ := h
  have hex : ∃ j, ‖coeff j e‖ = 1 := by
    by_contra hno
    push Not at hno
    have hlt : ∀ n, ‖coeff n e‖ < 1 := fun n => lt_of_le_of_ne (he n) (hno n)
    have : ‖coeff i (e ^ 2)‖ < 1 := by
      rw [sq, coeff_mul]
      refine gauss_norm_sum_lt _ _ one_pos fun x _ => ?_
      rw [norm_mul]
      calc ‖coeff x.1 e‖ * ‖coeff x.2 e‖ ≤ ‖coeff x.1 e‖ * 1 :=
            mul_le_mul_of_nonneg_left (he _) (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hlt _
    exact this.ne hi
  obtain ⟨j, -, hl⟩ := leadAt_first_unit he hex
  have hm := hl.mul hl
  rw [one_mul, ← sq] at hm
  refine ⟨j, ?_, hl.2.2.2⟩
  by_contra hc
  push Not at hc
  exact (hm.2.2.1 i (by omega)).ne hi

theorem integral_of_sq_eq {e U G : PowerSeries K} (he : IntegralPS e) (he0 : constantCoeff e = 0)
    (hU : IntegralPS U) (hU0 : constantCoeff U = 1) (h : e ^ 2 = X ^ 2 * U * G) : IntegralPS G := by
  obtain ⟨e', rfl⟩ := (PowerSeries.X_dvd_iff).mpr he0
  have he' : IntegralPS e' := fun n => by
    have := he (n + 1)
    rwa [coeff_succ_X_mul] at this
  have h2 : e' ^ 2 = U * G := by
    have hX : (X : PowerSeries K) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [← mul_assoc, ← h]
    ring
  have hUi : IntegralPS U⁻¹ := integralPS_inv hU (by rw [hU0, norm_one])
  have hG : G = U⁻¹ * e' ^ 2 := by
    rw [h2, ← mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [hU0]; exact one_ne_zero), one_mul]
  rw [hG]
  exact integralPS_mul hUi (integralPS_pow he' 2)

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem le_one_of_prod_max_le_one {α : Type} (S : Finset α) (f : α → ℝ)
    (h : ∏ P ∈ S, max 1 (f P) ≤ 1) (Q : α) (hQ : Q ∈ S) : f Q ≤ 1 := by
  classical
  rw [← Finset.mul_prod_erase S _ hQ] at h
  have h1 : (1 : ℝ) ≤ ∏ P ∈ S.erase Q, max 1 (f P) :=
    Finset.one_le_prod₀ fun P _ => le_max_left _ _
  have h2 : max 1 (f Q) ≤ max 1 (f Q) * ∏ P ∈ S.erase Q, max 1 (f P) := by
    calc
      max 1 (f Q) = max 1 (f Q) * 1 := (mul_one _).symm
      _ ≤ max 1 (f Q) * ∏ P ∈ S.erase Q, max 1 (f P) :=
        mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one (le_max_left _ _))
  exact (le_max_right _ _).trans (h2.trans h)

theorem tor_integral (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (n : ℕ) (hn : 0 < n) (hln : ¬ l ∣ n) (P : ℂ)
    (hP : (n : ℂ) * P ∈ L.lattice) (hP' : P ∉ L.lattice) :
    ‖ι (L.weierstrassP P)‖ ≤ 1 ∧ ‖ι (L.derivWeierstrassP P)‖ ≤ 1 := by
  have hlp : l.Prime := Fact.out
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := norm_natCast_Cl_of_not_dvd l (n := 2)
      (fun h => hl ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 h))
    simpa using this
  have hnn : ‖(n : ℂ_[l])‖ = 1 := norm_natCast_Cl_of_not_dvd l hln
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hst : F.MulStable L (n : ℂ) := fun ω hω => by
    have := L.lattice.nsmul_mem hω n
    rwa [nsmul_eq_mul] at this
  obtain ⟨S, hS⟩ := F.kerRepsExist L (n : ℂ) hn0 hst
  obtain ⟨U, hU0, hUi, hsq⟩ := sq_formula l hl L ι g2 g3 hM n hn S hS
  obtain ⟨e, he0, hei, hel⟩ := mulN_integral (curve_law g2 g3 hM.n2 hM.n3 h2) n
  have hee := mult_unique g2 g3 (n : ℂ_[l]) e he0 hel
  rw [← hee] at hsq
  have hG := integral_of_sq_eq hei he0 hUi hU0 hsq
  obtain ⟨hxi, hx0, -, -⟩ := A.bridgeCurve ℂ_[l] (A.shortW g2 g3)
    (shortW_intModel g2 g3 hM.n2 hM.n3 h2)
  have hxi' : IntegralPS (A.xS (A.shortW g2 g3)) := (integralPS_iff_mv _).2 hxi
  have hb := gauss_bound S (fun P => ι (L.weierstrassP P)) _ hxi' hx0 _ hG
  rw [norm_pow, hnn, one_pow, one_mul] at hb
  obtain ⟨Q, hQ, hPQ⟩ := hS.2.2 P hP hP'
  have hxQ : ‖ι (L.weierstrassP Q)‖ ≤ 1 :=
    le_one_of_prod_max_le_one S (fun P => ‖ι (L.weierstrassP P)‖) hb Q hQ
  have hPQ' : L.weierstrassP P = L.weierstrassP Q := by
    have := L.weierstrassP_add_coe Q ⟨P - Q, hPQ⟩
    simpa using this
  have hx : ‖ι (L.weierstrassP P)‖ ≤ 1 := by rw [hPQ']; exact hxQ
  refine ⟨hx, ?_⟩
  have hrel := congrArg ι (L.derivWeierstrassP_sq P hP')
  simp only [map_pow, map_sub, map_mul, ← hM.eq2, ← hM.eq3] at hrel
  have h4 : ‖ι (4 : ℂ)‖ ≤ 1 := by
    have : ι (4 : ℂ) = ((4 : ℕ) : ℂ_[l]) := by
      rw [← map_natCast ι 4]; norm_num
    rw [this]
    exact IsUltrametricDist.norm_natCast_le_one ℂ_[l] 4
  have hy2 : ‖ι (L.derivWeierstrassP P)‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, hrel]
    refine (norm_sub_le_max_Cl l _ _).trans (max_le ?_ hM.n3)
    refine (norm_sub_le_max_Cl l _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ h4 (by positivity) (pow_le_one₀ (norm_nonneg _) hx)
    · rw [norm_mul]
      exact mul_le_one₀ hM.n2 (norm_nonneg _) hx
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hy2

end ReciprocityTheory.ChartRestriction.L1
