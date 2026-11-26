module

public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NotSingularOfCentral
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.MeanNum
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeSumNumericFacts
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.ThirdEstimateOfNumericFacts
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarFam

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.LatticeChainSuccOfPartial
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

theorem mul_bound {s B c R : ℝ} (hs : s ≤ B) (hc : 0 ≤ c) (hBc : B * c ≤ R) : s * c ≤ R :=
  le_trans (mul_le_mul_of_nonneg_right hs hc) hBc

theorem rpow_neg_le_inv (s : Scale) (u : ℝ) (hu : u ≤ -1) : s.x ^ u ≤ 1 / s.x := by
  have h := Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le hu
  rwa [Real.rpow_neg_one, ← one_div] at h

theorem rpow_le_inv_of_le_neg_two (s : Scale) (h : 120 ≤ s.x) (u : ℝ) (hu : u ≤ -2) : s.x ^ u ≤ 1 / s.x / 120 := by
  have h1 := Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le hu
  have hx := sc_x_pos s
  have h2 : s.x ^ (-2 : ℝ) = 1 / s.x / s.x := by
    rw [Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  rw [h2] at h1
  refine le_trans h1 ?_
  exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h

theorem sum_low (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    {a b : HH D → ℤ} (h : InWin L a b) (hG : GainBoundAt X K C bo a b)
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p)
    {A3 A4 PS : Finset ℕ} {badf : ℕ → ℝ} (T : Sets X K A3 A4 PS badf)
    (hZZ : WReq X K a b) (N : PrimeSumNumericFacts D L K C bo)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ IsResidueClassZero D p ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :
    ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤
      47 / 10 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) := by
  have ha := sc_one_lt_a L.sc
  have hx := sc_x_pos L.sc
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) := mul_nonneg hm hN
  have hA : 0 ≤ L.sc.a / L.sc.x := div_nonneg (by linarith) hx.le
  have hX'' : 0 ≤ L.sc.X'' D.R.n := by
    have := X'_le_X'' L.sc D.R.n (n_pos D); have := one_le_X' L.sc; linarith
  have hc1 := first_constant_nonneg L C hC
  have hc2 := second_constant_nonneg L C hC
  have hc3 := third_constant_nonneg L C bo hC hbo
  have hc4 := fourth_constant_nonneg K hK.1 L C hC
  have hcfl := cfl_nonneg D L.sc C hC
  refine le_trans (Finset.sum_le_sum (fun p hp =>
    low_le X K hK P C bo hC hbo h hG hSig T p (hS p hp).1 (hS p hp).2.1 (hS p hp).2.2)) ?_
  unfold E1
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  have b1 : ∑ p ∈ S, (if p ∈ prB (L.sc.X'' D.R.n + 1) then (1 : ℝ) else 0) ≤ L.sc.X'' D.R.n + 2 := by
    refine le_trans (sum_ite_mem_le (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)) ?_
    have := card_prB_le (L.sc.X'' D.R.n + 1) (by linarith)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  have b2 : ∑ p ∈ S, (if p ∈ prB (L.sc.p0 D.R.k) then Real.log p else 0) ≤ Real.log 4 * L.sc.p0 D.R.k :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p) (fun p _ => Real.log_natCast_nonneg p))
      (sum_log_prB _ (p0_pos D L.sc).le)
  have b3 : ∑ p ∈ S, (if p ∈ prB L.sc.X' then Real.log p else 0) ≤ Real.log 4 * L.sc.X' :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p) (fun p _ => Real.log_natCast_nonneg p))
      (sum_log_prB _ (by have := one_le_X' L.sc; linarith))
  have b4 : ∑ p ∈ S, (if p ∈ prB L.sc.X' then Real.log p / p else 0) ≤ lX L.sc :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (sum_logdiv_prB _ (one_le_X' L.sc))
  have b5 : ∑ p ∈ S, (if p ∈ A3 then Real.log p / p else 0) ≤ 1 / L.sc.x / 120 :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (le_trans T.s3 (rpow_le_inv_of_le_neg_two _ N.n5 _ (by unfold Formalism.MainNotions.G.hG; have := L.sc.eps_pos; linarith)))
  have b6 : ∑ p ∈ S, (if p ∈ A4 then Real.log p / p else 0) ≤ 1 / L.sc.x :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (le_trans T.s4 (rpow_neg_le_inv _ _ le_rfl))
  have b7 : ∑ p ∈ S, (if p ∈ PS then Real.log p / p * badf p else 0) ≤
      (D.host.TT.card : ℝ) * (1 / L.sc.x / 120) :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p * badf p)
      (fun p _ => mul_nonneg (lp_nonneg p) (T.hbad0 p)))
      (le_trans T.s2 (mul_le_mul_of_nonneg_left N.n7 hN))
  have b8 : ∑ p ∈ S, (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) ≤
      1 / L.sc.x / 120 := by
    refine le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p))
      (fun p hp => mul_nonneg (lp_nonneg p)
        (add_nonneg (mul_nonneg (by norm_num) (dropI_nonneg X K a b p))
          (mul_nonneg (by norm_num) (hSig p (cand_of_mem hp)))))) ?_
    exact le_trans ((WReq_iff X K a b).1 hZZ) (rpow_le_inv_of_le_neg_two L.sc N.n5 (-9) (by norm_num))
  have q1 := mul_bound b1 (add_nonneg (mul_nonneg hM hc1) (mul_nonneg hm hcfl))
    (R := 1 / 20 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n1 hM
      have e2 := mul_le_mul_of_nonneg_left N.n1' hm
      have e3 : (D.R.m : ℝ) * (L.sc.a / L.sc.x) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x) := by
        have := mul_le_mul_of_nonneg_left N.one_le_card_tops (mul_nonneg hm hA)
        nlinarith
      nlinarith)
  have q2 := mul_bound b2 (mul_nonneg hM hc2)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n2 hM
      linarith)
  have q3 := mul_bound b3 (mul_nonneg hM hc3)
    (R := 3 / 2 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n3 hM
      linarith)
  have q4 := mul_bound b4 (mul_nonneg hM hc4)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n4 hM
      linarith)
  have hMa : 0 ≤ 3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a := by positivity
  have q5 := mul_bound b5 hMa
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q6 := mul_bound b6 hMa
    (R := 3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q7 := mul_bound b7 (by positivity : (0 : ℝ) ≤ 3 * (D.R.m : ℝ) * L.sc.a)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q8 := mul_bound b8 (by positivity : (0 : ℝ) ≤ 4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a)
    (R := 1 / 30 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have hU : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x) := mul_nonneg hM hA
  linarith

theorem sum_high (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (C bo : ℝ) {a b : HH D → ℤ} (h : InWin L a b)
    (N : PrimeSumNumericFacts D L K C bo) (S : Finset ℕ) (hS : ∀ p ∈ S, L.sc.X'' D.R.n < (p : ℝ)) :
    ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤
      1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) := by
  obtain ⟨hS1, hS2⟩ := Sc_facts P
  obtain ⟨hth0, hth1⟩ := thS_bounds P
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) := mul_nonneg hm hN
  have hX1 : 1 ≤ L.sc.X'' D.R.n := by
    have := X'_le_X'' L.sc D.R.n (n_pos D); have := one_le_X' L.sc; linarith
  obtain ⟨ht0, ht1⟩ := thW_bounds D L.sc
  have hw := sc_w''_pos L.sc D.R.n (n_pos D)
  have hl2 : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) *
      ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) := by positivity
  set R9 : Finset ℕ := Finset.Ioc ⌊L.sc.X'' D.R.n⌋₊ ⌈L.sc.X'' D.R.n * (1 + thS L)⌉₊ with hR9
  have hpt : ∀ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤ (if p ∈ R9 then (1 : ℝ) else 0) *
      (Real.log (2 * L.sc.X'' D.R.n) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc))) := by
    intro p hp
    have hpX := hS p hp
    have hd := dfc_high P X K h p hpX
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    by_cases hlt : (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L)
    · rw [if_pos hlt] at hd
      have hmem : p ∈ R9 := by
        rw [hR9]
        refine Finset.mem_Ioc.2 ⟨(Nat.floor_lt (by linarith)).2 hpX, ?_⟩
        exact_mod_cast le_trans hlt.le (Nat.le_ceil _)
      rw [if_pos hmem, one_mul]
      have h1 : max 0 (Dfc X K a b p) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc) :=
        max_le (by positivity) (by linarith)
      have h2 : Real.log p ≤ Real.log (2 * L.sc.X'' D.R.n) :=
        Real.log_le_log (by linarith) (by nlinarith)
      exact mul_le_mul h2 h1 (le_max_left _ _) hl2
    · rw [if_neg hlt] at hd
      have h1 : max 0 (Dfc X K a b p) = 0 := max_eq_left (by linarith)
      rw [h1, mul_zero]
      split_ifs
      · rw [one_mul]; exact hcoef
      · rw [zero_mul]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [← Finset.sum_mul]
  have b9 : ∑ p ∈ S, (if p ∈ R9 then (1 : ℝ) else 0) ≤ L.sc.X'' D.R.n * thS L + 2 := by
    refine le_trans (sum_ite_mem_le (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)) ?_
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hR9, Nat.card_Ioc]
    have hle : ⌊L.sc.X'' D.R.n⌋₊ ≤ ⌈L.sc.X'' D.R.n * (1 + thS L)⌉₊ :=
      le_trans (Nat.floor_le_floor (by nlinarith)) (Nat.floor_le_ceil _)
    rw [Nat.cast_sub hle]
    have h1 := Nat.ceil_lt_add_one (mul_nonneg (by linarith) (by linarith) : 0 ≤ L.sc.X'' D.R.n * (1 + thS L))
    have h2 := Nat.lt_floor_add_one (L.sc.X'' D.R.n)
    linarith
  refine mul_bound b9 hcoef ?_
  have e1 := mul_le_mul_of_nonneg_left N.n9 hM
  linarith

theorem inWin_of_box {K : Consts} {a b : HH D → ℤ} (ha : a ∈ box D (winA D L.sc)) (hb : b ∈ box D (winB D K L.sc)) :
    InWin L a b := by
  classical
  intro t ht
  unfold box at ha hb
  have h1 := Fintype.mem_piFinset.1 ha t
  have h2 := Fintype.mem_piFinset.1 hb t
  rw [if_pos ht] at h1 h2
  unfold winA at h1
  unfold winB at h2
  obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.1 h1
  obtain ⟨h2a, _⟩ := Finset.mem_Icc.1 h2
  exact ⟨Int.ceil_le.1 h1a, Int.le_floor.1 h1b, Int.ceil_le.1 h2a⟩

theorem latticeChain_succ_of_partial (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    (hG : GainBoundAll X K C bo) (hSig0 : ∀ a b p, Cand D L K p → 0 ≤ Sig X K a b p) (h2 : adm2 D L X) (h3 : adm3 D L)
    (h4 : ArchimedeanSignatureMatching D L K) (N : PrimeSumNumericFacts D L K C bo) : PointsLemma D L X K := by
  classical
  intro a ha b hb hZZ
  have hW := inWin_of_box ha hb
  have hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p := fun p hp => hSig0 a b p hp
  have hXX := X'_le_X'' L.sc D.R.n (n_pos D)
  have h2' := h2.2
  unfold BTT at h2'
  unfold adm3 at h3
  have h4' := h4.2.2.2.2
  have T : Sets X K _ _ _ (fun p => ((D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t))).card : ℝ)) :=
    { hA3 := fun p hp hc hX ho => Finset.mem_filter.2 ⟨by
          unfold primesResidueBelow
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 (by linarith)), hp, by linarith, hc⟩, ho⟩
      hA4 := fun p hp hX hB => Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 hX), hp, hB⟩
      hPS := fun p hC => Finset.mem_filter.2 ⟨by
          unfold primesResidueBelow
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 hC.2.1), hC.1, hC.2.1, hC.2.2.1⟩, hC.2.2.2.1⟩
      hPSsub := fun p hp => by
          have h1 := (Finset.mem_filter.1 hp).1
          unfold primesResidueBelow at h1
          have h2 := (Finset.mem_filter.1 h1).2
          exact mem_prB.2 ⟨h2.1, h2.2.1⟩
      hbad := fun p _ => by
          have : (D.host.TT \ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)) ⊆
              D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t)) := by
            intro t ht
            obtain ⟨ht1, ht2⟩ := Finset.mem_sdiff.1 ht
            refine Finset.mem_filter.2 ⟨ht1, fun hg => ht2 (Finset.mem_filter.2 ⟨ht1, ?_⟩)⟩
            unfold goodReps reps
            exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hg⟩
          exact_mod_cast Finset.card_le_card this
      hbad0 := fun p => Nat.cast_nonneg _
      s3 := h3
      s4 := h4'
      s2 := h2' }
  refine ⟨?_, ?_⟩
  · intro S hS
    have hsplit := Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ L.sc.X'' D.R.n)
      (fun p : ℕ => Real.log p * max 0 (Dfc X K a b p))
    have l1 := sum_low X K hK P C bo hC hbo hW (hG a b hW) hSig T hZZ N
      (S.filter (fun p : ℕ => (p : ℝ) ≤ L.sc.X'' D.R.n))
      (fun p hp => ⟨(hS p (Finset.mem_filter.1 hp).1).1, (hS p (Finset.mem_filter.1 hp).1).2, (Finset.mem_filter.1 hp).2⟩)
    have l2 := sum_high P X K C bo hW N (S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ L.sc.X'' D.R.n))
      (fun p hp => not_le.1 (Finset.mem_filter.1 hp).2)
    have hMA : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x) := by
      have := sc_one_lt_a L.sc
      have := sc_x_pos L.sc
      positivity
    have e : 5 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / L.sc.x =
        5 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) := by ring
    rw [e]
    change ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤ _
    linarith
  · intro S _
    have hMa : 0 ≤ ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a := by
      have := sc_one_lt_a L.sc
      positivity
    refine le_trans (Finset.sum_le_sum (fun p _ => io_le X K hK P hW hSig p)) ?_
    rw [← Finset.sum_mul]
    have b8 : ∑ p ∈ S, (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) ≤
        L.sc.x ^ (-9 : ℝ) := by
      refine le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p))
        (fun p hp => mul_nonneg (lp_nonneg p)
          (add_nonneg (mul_nonneg (by norm_num) (dropI_nonneg X K a b p))
            (mul_nonneg (by norm_num) (hSig p (cand_of_mem hp)))))) ?_
      exact (WReq_iff X K a b).1 hZZ
    exact mul_bound b8 hMa (le_of_eq (by ring))

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.As

variable {D : D7} {L : SizeData₂ D}

theorem shift_ge (p y κ : ℝ) (hp : 2 ≤ p) (hκ : 0 ≤ κ) (hy0 : 0 ≤ y)
    (w : ℕ → ℝ) (hw : ∀ e, 0 ≤ w e) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) ≤
      ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : 1 / p < 1 := by rw [div_lt_one hp0]; linarith
  have hg : Summable (fun e : ℕ => y * (1 / p) ^ e) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left y
  have hs : ∀ c : ℕ → ℝ, (∀ e, 0 ≤ c e) →
      Summable (fun e => if Q e then max 0 (y / p ^ e - c e) else 0) := by
    intro c hc
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hg
    · split_ifs
      · exact le_max_left _ _
      · exact le_rfl
    · have hpe : y / p ^ e = y * (1 / p) ^ e := by rw [one_div_pow, div_eq_mul_one_div]
      split_ifs
      · exact max_le (mul_nonneg hy0 (by positivity)) (by rw [← hpe]; linarith [hc e])
      · exact mul_nonneg hy0 (by positivity)
  refine Summable.tsum_le_tsum (fun e => ?_) (hs _ fun e => by linarith [hw e]) (hs _ hw)
  split_ifs
  · exact max_le_max le_rfl (by linarith)
  · exact le_rfl

theorem shift_le (p y κ A : ℝ) (hp : 2 ≤ p) (hκ : 0 ≤ κ) (hy0 : 0 ≤ y) (hyA : y ≤ A) (hA : 1 ≤ A)
    (w : ℕ → ℝ) (hw : ∀ e, 1 ≤ w e) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e → Odd e) :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤
      ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * Real.logb p A := by
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : 1 / p < 1 := by rw [div_lt_one hp0]; linarith
  have hg : Summable (fun e : ℕ => y * (1 / p) ^ e) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left y
  have hs : ∀ c : ℕ → ℝ, (∀ e, 0 ≤ c e) →
      Summable (fun e => if Q e then max 0 (y / p ^ e - c e) else 0) := by
    intro c hc
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hg
    · split_ifs
      · exact le_max_left _ _
      · exact le_rfl
    · have hpe : y / p ^ e = y * (1 / p) ^ e := by rw [one_div_pow, div_eq_mul_one_div]
      split_ifs
      · exact max_le (mul_nonneg hy0 (by positivity)) (by rw [← hpe]; linarith [hc e])
      · exact mul_nonneg hy0 (by positivity)
  have hL0 : 0 ≤ Real.logb p A := Real.logb_nonneg hp1 hA
  set n := ⌊Real.logb p A⌋₊ with hn
  set ind : ℕ → ℝ := fun e => if Q e ∧ (p : ℝ) ^ e < A then 1 else 0 with hind
  have hlog : ∀ e : ℕ, (p : ℝ) ^ e < A → e ≤ n := by
    intro e he
    apply Nat.le_floor
    have h1 : Real.logb p ((p : ℝ) ^ e) = e := by
      rw [Real.logb_pow, Real.logb_self_eq_one hp1, mul_one]
    rw [← h1]
    exact (Real.logb_lt_logb hp1 (by positivity) he).le
  have hsupp : ∀ e ∉ Finset.range (n + 1), ind e = 0 := by
    intro e he
    simp only [hind]
    rw [if_neg]
    rintro ⟨_, h⟩
    exact he (Finset.mem_range.2 (Nat.lt_succ_of_le (hlog e h)))
  have hind_sum : Summable ind := summable_of_ne_finset_zero hsupp
  have hcount : ∑' e, ind e ≤ Real.logb p A := by
    rw [tsum_eq_sum hsupp]
    have hsub : ∑ e ∈ Finset.range (n + 1), ind e ≤
        (((Finset.range (n + 1)).filter Odd).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_le_sum fun e _ => ?_
      simp only [hind]
      split_ifs with h1 h2 <;> first | exact absurd (hQ e h1.1) h2 | norm_num
    have hodd : ((Finset.range (n + 1)).filter Odd).card ≤ n := by
      have h := Finset.card_le_card_of_injOn (fun e => e / 2) (s := (Finset.range (n + 1)).filter Odd) (t := Finset.range ((n + 1) / 2))
        (by
          intro e he
          have he' : e ≤ n ∧ Odd e := by simpa using he
          obtain ⟨h1, k, rfl⟩ := he'
          simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range]
          omega)
        (by
          intro e1 he1 e2 he2 heq
          have he1' : e1 ≤ n ∧ Odd e1 := by simpa using he1
          have he2' : e2 ≤ n ∧ Odd e2 := by simpa using he2
          obtain ⟨_, k1, rfl⟩ := he1'
          obtain ⟨_, k2, rfl⟩ := he2'
          simp only at heq
          omega)
      rw [Finset.card_range] at h
      omega
    calc ∑ e ∈ Finset.range (n + 1), ind e ≤ (((Finset.range (n + 1)).filter Odd).card : ℝ) := hsub
      _ ≤ (n : ℝ) := by exact_mod_cast hodd
      _ ≤ Real.logb p A := Nat.floor_le hL0
  have hterm : ∀ e, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤
      (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * ind e := by
    intro e
    simp only [hind]
    by_cases hq : Q e
    · by_cases hu : 0 < y / p ^ e - w e
      · have hpA : (p : ℝ) ^ e < A := by
          have h1 : 1 < y / p ^ e := lt_of_le_of_lt (hw e) (by linarith)
          rw [lt_div_iff₀ (by positivity)] at h1
          linarith
        rw [if_pos hq, if_pos hq, if_pos ⟨hq, hpA⟩, max_eq_right hu.le]
        have := le_max_right 0 (y / p ^ e - (w e + κ))
        linarith
      · rw [if_pos hq, if_pos hq, max_eq_left (not_lt.1 hu)]
        have h1 := le_max_left 0 (y / p ^ e - (w e + κ))
        have h2 : 0 ≤ κ * (if Q e ∧ (p : ℝ) ^ e < A then (1 : ℝ) else 0) :=
          mul_nonneg hκ (by split_ifs <;> norm_num)
        linarith
    · rw [if_neg hq, if_neg hq, if_neg (fun h => hq h.1)]
      simp
  have hsκ := hs (fun e => w e + κ) (fun e => by linarith [hw e])
  calc ∑' e, (if Q e then max 0 (y / p ^ e - w e) else 0)
      ≤ ∑' e, ((if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * ind e) :=
        Summable.tsum_le_tsum hterm (hs _ fun e => by linarith [hw e]) (hsκ.add (hind_sum.mul_left κ))
    _ = ∑' e, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * ∑' e, ind e := by
        rw [Summable.tsum_add hsκ (hind_sum.mul_left κ), tsum_mul_left]
    _ ≤ ∑' e, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * Real.logb p A :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hcount hκ)

theorem n_pos (D : D7) : 1 ≤ D.R.n := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  unfold Formalism.BasicNotions.Ranks.n
  omega

theorem fill_ge (X : Inst D L) (b : HH D → ℤ) (hb : ∀ t ∈ D.host.TT, (0 : ℝ) ≤ (b t : ℝ)) (j : ℕ)
    (z : Bool × HH D) : L.sc.w'' D.R.n ≤ fill X b j z := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  have hX1 : 1 ≤ L.sc.X' := by
    show 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ L.sc.b' := by
    show 0 ≤ L.sc.a / L.sc.X'
    exact div_nonneg (by linarith) (by linarith)
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast n_pos D
  have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    show L.sc.b' / (L.sc.x * D.R.n) ≤ L.sc.b' / L.sc.x
    exact div_le_div_of_nonneg_left hb'0 (by linarith) (by nlinarith)
  have hw2 : L.sc.w'' D.R.n ≤ L.sc.b := by
    calc L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := hw1
      _ = L.sc.b / L.sc.X' := by
        show L.sc.x * L.sc.b / L.sc.X' / L.sc.x = L.sc.b / L.sc.X'
        field_simp
      _ ≤ L.sc.b := div_le_self (by linarith) hX1
  unfold fill
  by_cases htop : IsTopPl D z
  · rw [if_pos (show z.1 = false ∧ z.2 ∈ D.host.TT from htop)]
    linarith [hb z.2 htop.2, (X.off_top j z htop).1]
  · rw [if_neg (show ¬(z.1 = false ∧ z.2 ∈ D.host.TT) from htop), zero_add]
    by_cases hthick : IsThickPl D z
    · linarith [(X.off_thick j z hthick).1]
    · exact (X.off_thin j z ⟨htop, hthick⟩).1

theorem kaJ_bounds (D : D7) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : 0 ≤ kaJ D j ∧ kaJ D j ≤ Nm D := by
  simp only [Formalism.BasicNotions.SizeData₂.lifts, Finset.mem_Icc] at hj
  obtain ⟨h1, h2⟩ := hj
  have h1' : (1 : ℝ) ≤ j := by exact_mod_cast h1
  have h2' : (j : ℝ) ≤ D.R.m := by exact_mod_cast h2
  have ht : (0 : ℝ) ≤ D.R.t + 1 := by positivity
  have hk : (0 : ℝ) ≤ D.R.k := by positivity
  unfold kaJ Nm Formalism.BasicNotions.Ranks.N
  push_cast
  constructor
  · apply div_nonneg _ (by norm_num)
    nlinarith
  · rw [div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right (show 2 * (j : ℝ) - 1 ≤ 2 * D.R.m by linarith) ht]

theorem asksAll_of (X : Inst D L) (hSz : Nm D + 1 ≤ L.sc.w'' D.R.n) : RequiresAll X := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  have hX1 : 1 ≤ L.sc.X' := by
    show 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ L.sc.b' := by
    show 0 ≤ L.sc.a / L.sc.X'
    exact div_nonneg (by linarith) (by linarith)
  intro a b ha hb p hp j hj s hs
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨hk0, hkN⟩ := kaJ_bounds D j hj
  have hNm0 : (0 : ℝ) ≤ Nm D := by unfold Nm; positivity
  have hwG : ∀ e, 1 ≤ fillG X b j (partner D p s e) := by
    intro e
    have := fill_ge X b hb j (partner D p s e)
    unfold fillG
    linarith
  have hw0 : ∀ e, 0 ≤ fillG X b j (partner D p s e) := fun e => by linarith [hwG e]
  have hwF : ∀ e, 0 ≤ fill X b j (partner D p s e) := fun e => by
    have := fill_ge X b hb j (partner D p s e)
    linarith
  have hA : 1 ≤ 2 * L.sc.a := by linarith
  have hlog : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg (by linarith) hA
  by_cases hy : 0 ≤ (a s : ℝ)
  · have h1 := shift_ge (p : ℝ) (a s) (kaJ D j) hp2 hk0 hy
      (fun e => fillG X b j (partner D p s e)) hw0 Odd
    have h2 := shift_le (p : ℝ) (a s) (kaJ D j) (2 * L.sc.a) hp2 hk0 hy (ha s hs) hA
      (fun e => fillG X b j (partner D p s e)) hwG Odd (fun e h => h)
    simp only [fillG, sub_add_cancel] at h1 h2
    unfold askP askG fillG
    refine ⟨h1, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right hkN hlog]
  · have hz : ∀ c : ℕ → ℝ, (∀ e, 0 ≤ c e) →
        ∑' e : ℕ, (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e - c e) else 0) = 0 := by
      intro c hc
      refine (tsum_congr fun e => ?_).trans tsum_zero
      split_ifs
      · apply max_eq_left
        have : (a s : ℝ) / (p : ℝ) ^ e ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        linarith [hc e]
      · rfl
    have e1 := hz (fun e => fill X b j (partner D p s e)) hwF
    have e2 := hz (fun e => fillG X b j (partner D p s e)) hw0
    beta_reduce at e1 e2
    unfold askP askG
    rw [e1, e2]
    exact ⟨le_rfl, by rw [zero_add]; exact mul_nonneg hNm0 hlog⟩

theorem lo_succ (K : Consts) (hLa : 0 ≤ K.La) (L : SizeData₂ D) (C bo : ℝ) (p : ℕ) (hp : p.Prime) :
    lo K L C bo p + (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) ≤ lo K L (C + 1) bo p := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  have hX1 : 1 ≤ L.sc.X' := by
    show 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ L.sc.b' := by
    show 0 ≤ L.sc.a / L.sc.X'
    exact div_nonneg (by linarith) (by linarith)
  have hlogx : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hw : 0 ≤ L.sc.w'' D.R.n := by
    show 0 ≤ L.sc.b' / (L.sc.x * D.R.n)
    exact div_nonneg hb'0 (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have hd1 : 0 < L.sc.delta1 := by
    show 0 < L.sc.x ^ (-(L.sc.eps / 8))
    exact Real.rpow_pos_of_pos (by linarith) _
  have hLaS : 0 ≤ La K L.sc := by
    unfold La
    exact mul_nonneg (mul_nonneg hLa (by positivity)) (Real.log_nonneg ha1)
  have g1 : 0 ≤ (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hb'0) hlogx
  have g2 : 0 ≤ L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 :=
    div_nonneg (mul_nonneg hw hlogx) hd1.le
  have g3 : 0 ≤ La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) :=
    div_nonneg (mul_nonneg hLaS (by linarith)) (mul_nonneg hp0 (Nat.cast_nonneg _))
  have g4 : 0 ≤ L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hp0 _)
  have g5 : 0 ≤ L.sc.a / (p : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
  have g6 := mul_nonneg hlogx (add_nonneg g3 g4)
  have g7 := mul_nonneg hlogx (add_nonneg g3 g5)
  obtain ⟨α, β, hform, hα⟩ : ∃ α β : ℝ, (∀ C' : ℝ, lo K L C' bo p = C' * α + β) ∧
      (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) ≤ α :=
    ⟨(cG L + L.etaSz) * Real.logb p (2 * L.sc.a) +
        (if IsResidueClassZero D p then (if (p : ℝ) < L.sc.p0 D.R.k then (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x
          else if (p : ℝ) < L.sc.X' then L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 else 0)
          else 0) +
        (if IsResidueClassZero D p ∧ (p : ℝ) < L.sc.X' then Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) +
          (if (p : ℝ) < L.sc.p0 D.R.k then L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))
            else L.sc.a / (p : ℝ) ^ 2)) else 0),
      (if IsResidueClassZero D p then (if (p : ℝ) < L.sc.p0 D.R.k then 0
        else if (p : ℝ) < L.sc.X' then L.sc.b' / L.sc.x + L.etaSz + bo else 0) else 0),
      fun C' => by
        simp only [lo]
        split_ifs <;> ring,
      by split_ifs <;> linarith [g1, g2, g6, g7]⟩
  rw [hform, hform]
  have e : (C + 1) * α + β = C * α + β + α := by ring
  rw [e]
  linarith

theorem fl_succ (D : D7) (s : Scale) (C : ℝ) (p : ℕ) (hp : p.Prime) : fl D s C p ≤ fl D s (C + 1) p := by
  have hx1 : 1 < s.x := s.one_lt_alt
  have hL0 : 0 ≤ s.L := by
    show 0 ≤ s.x ^ s.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ s.b := by
    show 1 ≤ Real.exp s.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ s.a := by
    show 1 ≤ s.x * s.b
    nlinarith
  have hX1 : 1 ≤ s.X' := by
    show 1 ≤ Real.exp (s.x ^ (s.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ s.b' := by
    show 0 ≤ s.a / s.X'
    exact div_nonneg (by linarith) (by linarith)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hl : 0 ≤ Real.logb p s.a := Real.logb_nonneg hp1 ha1
  have h1 : 0 ≤ (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p s.a := mul_nonneg (by positivity) hl
  have h2 : 0 ≤ (D.R.f : ℝ) * Real.logb p s.a ^ 2 := by positivity
  unfold fl
  nlinarith [h1, h2]

theorem TTP_subset₂ (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : TTP X K a b p ⊆ D.host.TT := by
  unfold TTP
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.filter_subset _ _

theorem gainBoundAll_add_one_of_gainBoundAllRequired (X : Inst D L) (K : Consts) (hLa : 0 ≤ K.La) (C bo : ℝ) (hA : RequiresAll X) (hNc : Nm D ≤ cG L)
    (h : GainBoundAllUniform X K C bo) : GainBoundAll X K (C + 1) bo := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  have hX1 : 1 ≤ L.sc.X' := by
    show 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ L.sc.b' := by
    show 0 ≤ L.sc.a / L.sc.X'
    exact div_nonneg (by linarith) (by linarith)
  intro a b hwin p hp hcls hX
  obtain ⟨hgain, hsum⟩ := h a b hwin p hp hcls hX
  refine ⟨hgain, ?_⟩
  have hlo := lo_succ K hLa L C bo p hp
  have hfl := fl_succ D L.sc C p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have heta := L.etaSz_pos
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hxA : 1 ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)
  have ha2 : ∀ t ∈ D.host.TT, (a t : ℝ) ≤ 2 * L.sc.a := by
    intro t ht
    have h1 := (hwin t ht).2.1
    have h2 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
      div_le_self (by linarith) (one_le_mul_of_one_le_of_one_le hk1 hxA)
    linarith
  have hb0 : ∀ t ∈ D.host.TT, (0 : ℝ) ≤ (b t : ℝ) := fun t ht => by
    linarith [(hwin t ht).2.2]
  have hterm : ∀ j ∈ SizeData₂.lifts D, ∀ s ∈ TTP X K a b p,
      askG X a b p j s - lo K L (C + 1) bo p ≤ askP X a b p j s - lo K L C bo p := by
    intro j hj s hs
    have hA := (hA a b ha2 hb0 p hp j hj s (TTP_subset₂ X K a b p hs)).2
    have h3 : Nm D * Real.logb p (2 * L.sc.a) ≤ (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) :=
      mul_le_mul_of_nonneg_right (by linarith) hlog
    linarith
  have hsum2 : (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K a b p, (askG X a b p j s - lo K L (C + 1) bo p)) ≤
      ∑ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K a b p, (askP X a b p j s - lo K L C bo p) :=
    Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun s hs => hterm j hj s hs
  have hm : 0 ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hfl hm]

end Formalism.MainNotions.AuxBlock8.Pf.As

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf

def FamilyAskBounds {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RequiresAll (X x i)

def RemainingCountingStatement {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        GainBoundAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2))))

def FamilyFourthBound {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i) (Fm.L x i) (X x i) K

def RestW {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightVectorExists (Fm.D x i) (Fm.L x i) (X x i) K

def FamilyFifthBound {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm → ∀ C : ℝ, 0 ≤ C →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        GainBoundAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) → PointsLemma (Fm.D x i) (Fm.L x i) (X x i) K

def RestT {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm → ∀ C : ℝ, 0 ≤ C →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightedPrimeSumBound (Fm.D x i) (Fm.L x i) (X x i) K C

theorem eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

theorem stmtEF_of {eps : ℝ} (Fm : FamP eps) (h0 : FamilyAskBounds Fm) (h1 : RemainingCountingStatement Fm) (h2 : FamilyFourthBound Fm) (hW : RestW Fm)
    (h3 : FamilyFifthBound Fm) (hT : RestT Fm) : FamilyClosedForm Fm := by
  intro K hK C31 Ce Cm hC31 hCe hCm
  obtain ⟨C, hC, hG⟩ := h1 K hK C31 Ce Cm hC31 hCe hCm
  refine ⟨C, hC, fun X Y hA => ?_⟩
  obtain ⟨a0, ha0⟩ := h0 K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨a1, ha1⟩ := hG X Y hA
  obtain ⟨a2, ha2⟩ := h2 K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨aW, haW⟩ := hW K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨a3, ha3⟩ := h3 K hK C31 Ce Cm hC31 hCe hCm C hC X Y hA
  obtain ⟨aT, haT⟩ := hT K hK C31 Ce Cm hC31 hCe hCm C hC X Y hA
  refine ⟨fun x => x ^ (-(eps / 2)), ?_, max a0 (max a1 (max a2 (max aW (max a3 aT)))), fun x hx i => ?_⟩
  · exact tendsto_rpow_neg_atTop (half_pos (eps_pos Fm))
  · simp only [ge_iff_le, max_le_iff] at hx
    obtain ⟨e0, e1, e2, eW, e3, eT⟩ := hx
    have g0 := ha0 x e0 i
    have g1 := ha1 x e1 i
    have g2 := ha2 x e2 i
    have gW := haW x eW i
    have g3 := ha3 x e3 i g1
    have gT := haT x eT i
    have g1' := g1 (aL (Fm.L x i)) (bL (Fm.L x i))
    refine ⟨g1' ?_, g2, g3, gW, fun a b ha hb p hp _ => g0 a b ha hb p hp, gT⟩

    intro t ht
    unfold aL bL
    simp only [dif_pos ht]
    exact ⟨((Fm.L x i).aT_win ⟨t, ht⟩).1, ((Fm.L x i).aT_win ⟨t, ht⟩).2, (Fm.L x i).bT_ge ⟨t, ht⟩⟩

theorem stmtF_of_stmtEF {eps : ℝ} (Fm : FamP eps) (h : FamilyClosedForm Fm) : KudlaFamilyStatement Fm := by
  intro K hK X Y hA
  obtain ⟨C31, Ce, Cm, hC31, hCe, hCm, hA'⟩ := hA
  obtain ⟨C, hC, hP⟩ := h K hK C31 Ce Cm hC31 hCe hCm
  exact ⟨C, hP X Y hA'⟩

end Formalism.MainNotions.AuxBlock8.Pf

end
end

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf

def RestStar {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C ≥ C0,
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        StarAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2))))

theorem bo_nonneg (s : Scale) (y : ℝ) : 0 ≤ s.b ^ y := Real.rpow_nonneg (Real.exp_pos s.L).le y

private theorem eventually_adm_of_admFam {eps : ℝ} (Fm : FamP eps) {K : Consts}
    {X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)} {Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)}
    {C31 Ce Cm : ℝ} (hA : AdmFam Fm K X Y C31 Ce Cm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x ∧
      ∀ i : Fm.Ix x, admitted (Fm.D x i) (Fm.L x i) (X x i) (Y x i) K ⟨C31, Ce, Cm, 1⟩ := by
  obtain ⟨x0, -, h⟩ := hA 1 one_pos
  refine ⟨max x0 (Fm.x1 + 1), fun x hx => ⟨?_, h x (le_trans (le_max_left _ _) hx)⟩⟩
  have := le_trans (le_max_right _ _) hx
  linarith

theorem rest0 {eps : ℝ} (Fm : FamP eps) : FamilyAskBounds Fm := by
  intro K _ C31 Ce Cm _ _ _ X Y hA
  obtain ⟨x0, h⟩ := eventually_adm_of_admFam Fm hA
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSz⟩ := (h x hx).2 i
  exact As.asksAll_of (X x i) hSz.2.2

theorem remainingCountingStatement_of_restStar {eps : ℝ} (Fm : FamP eps) (hS : RestStar Fm) : RemainingCountingStatement Fm := by
  intro K hK C31 Ce Cm hC31 hCe _
  obtain ⟨C0, hC0, hS'⟩ := hS K hK C31 Ce Cm hC31
  obtain ⟨C1, hC01, h3, hd1, hd2⟩ : ∃ C1 : ℝ, C0 ≤ C1 ∧ 3 ≤ C1 ∧ 2 * K.dl1 + (Ce + 1) ≤ C1 ∧
      4 * K.dl2 ≤ C1 :=
    ⟨max C0 (max 3 (max (2 * K.dl1 + (Ce + 1)) (4 * K.dl2))), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _),
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)⟩
  refine ⟨C1 + 1, by linarith, fun X Y hA => ?_⟩
  obtain ⟨x1, h1⟩ := hS' C1 hC01 X Y hA
  obtain ⟨x2, h2⟩ := eventually_adm_of_admFam Fm hA
  refine ⟨max x1 x2, fun x hx i => ?_⟩
  obtain ⟨hxp, hadm⟩ := h2 x (le_trans (le_max_right _ _) hx)
  obtain ⟨-, -, -, -, -, -, -, -, a9, -, -, aSz⟩ := hadm i
  have hN : GainBoundConstants K (Ce + 1) C1 ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) :=
    ⟨h3, hd1, hd2, bo_nonneg _ _⟩
  have hP := gain_bound_all_of_star (Fm.params x hxp i) (X x i) K hK Ce C1 _ hCe hN a9
    (h1 x (le_trans (le_max_left _ _) hx) i)
  have hNc : Nm (Fm.D x i) ≤ cG (Fm.L x i) :=
    (basics (Fm.params x hxp i)).2.1.trans (St.base (Fm.params x hxp i)).2.2.2.2
  exact As.gainBoundAll_add_one_of_gainBoundAllRequired (X x i) K hK.1 C1 _ (As.asksAll_of (X x i) aSz.2.2) hNc hP

theorem rest2 {eps : ℝ} (Fm : FamP eps) : FamilyFourthBound Fm := by
  intro K hK C31 Ce Cm _ _ hCm X Y hA
  obtain ⟨x0, h⟩ := second_estimate_and_mean_along_family Fm K hK C31 Ce Cm hCm X Y hA
  exact ⟨x0, fun x hx i => (h x hx i).1⟩

theorem restW {eps : ℝ} (Fm : FamP eps) : RestW Fm := by
  intro K hK C31 Ce Cm _ _ hCm X Y hA
  obtain ⟨x0, h⟩ := second_estimate_and_mean_along_family Fm K hK C31 Ce Cm hCm X Y hA
  exact ⟨x0, fun x hx i => weight_condition_of_mean_excess (X x i) K (h x hx i).2⟩

theorem rest3 {eps : ℝ} (Fm : FamP eps) : FamilyFifthBound Fm := by
  intro K hK C31 Ce Cm _ _ hCm C hC X Y hA
  obtain ⟨x1, h1⟩ := eventually_adm_of_admFam Fm hA
  obtain ⟨x2, h2⟩ := second_estimate_and_mean_along_family Fm K hK C31 Ce Cm hCm X Y hA
  obtain ⟨x3, h3⟩ := G5.prime_sum_facts_along_family Fm K hK C31 Ce Cm C hC X Y hA
  refine ⟨max x1 (max x2 x3), fun x hx i hG => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hxp, hadm⟩ := h1 x hx1
  obtain ⟨-, a2, a3, a4, -⟩ := hadm i
  exact G5.latticeChain_succ_of_partial (X x i) K hK (Fm.params x hxp i) C _ hC (bo_nonneg _ _) hG (h2 x hx2 i).2.1
    a2 a3 a4 (h3 x hx3 i)

theorem restT {eps : ℝ} (Fm : FamP eps) : RestT Fm := by
  intro K hK C31 Ce Cm _ _ _ C hC X Y hA
  exact G5.third_estimate_along_family Fm K hK C31 Ce Cm C hC X Y hA

theorem restStar {eps : ℝ} (Fm : FamP eps) : RestStar Fm := by
  intro K hK C31 Ce Cm hC31
  exact St.star_fam Fm K hK C31 Ce Cm hC31

theorem stmtEF {eps : ℝ} (Fm : FamP eps) : FamilyClosedForm Fm :=
  stmtEF_of Fm (rest0 Fm) (remainingCountingStatement_of_restStar Fm (restStar Fm)) (rest2 Fm) (restW Fm) (rest3 Fm) (restT Fm)

theorem stmtF {eps : ℝ} (Fm : FamP eps) : KudlaFamilyStatement Fm :=
  stmtF_of_stmtEF Fm (stmtEF Fm)

end Formalism.MainNotions.AuxBlock8.Pf

end
