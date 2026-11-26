module

public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliLeftComatrix
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolynomialTorsionCharacterLevelStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsoMultiplicative
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupHeightOneTorsionTower
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRootOpenDiscOfWeierstrassDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRootOpenDiscOfWeierstrassDegree
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.DiscRoot

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_span_pow (p x : ball K) (n : ℕ) :
    x ∈ Ideal.span {p} ^ n ↔ ‖(x : K)‖ ≤ ‖(p : K)‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    have ha : ‖(a : K)‖ ≤ 1 := a.2
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) ha
  · intro h
    by_cases hp : (p : K) ^ n = 0
    · rw [← norm_pow, hp, norm_zero, norm_le_zero_iff] at h
      exact ⟨0, Subtype.ext (by simp [h])⟩
    · refine ⟨⟨x / p ^ n, ?_⟩, Subtype.ext ?_⟩
      · change ‖(x : K) / p ^ n‖ ≤ 1
        rw [norm_div, norm_pow]
        exact div_le_one_of_le₀ h (by positivity)
      · simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
        exact div_mul_cancel₀ _ hp

theorem smod_iff (p x y : ball K) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule (ball K) (ball K))] ↔
      ‖(x : K) - y‖ ≤ ‖(p : K)‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow]
  rfl

theorem adicComplete [CompleteSpace K] (p : ball K) (hp : ‖(p : K)‖ < 1) :
    IsAdicComplete (Ideal.span {p}) (ball K) := by
  have ht : Filter.Tendsto (fun n : ℕ => ‖(p : K)‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp
  have hH : IsHausdorff (Ideal.span {p}) (ball K) := ⟨fun x hx => by
    have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' ht fun n => by
      simpa using (smod_iff p x 0 n).1 (hx n)
    exact Subtype.ext (by simpa using this)⟩
  have hP : IsPrecomplete (Ideal.span {p}) (ball K) := ⟨fun f hf => by
    have hc : CauchySeq fun n => (f n : K) := by
      refine cauchySeq_of_le_tendsto_0' (fun n => ‖(p : K)‖ ^ n) (fun n m hnm => ?_) ht
      rw [dist_eq_norm]
      exact (smod_iff p _ _ n).1 (hf hnm)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => (f n).2
    refine ⟨⟨L, hL1⟩, fun n => (smod_iff p _ _ n).2 ?_⟩
    refine le_of_tendsto ((tendsto_const_nhds (x := (f n : K))).sub hL).norm ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact (smod_iff p _ _ n).1 (hf hm)⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

theorem division [CompleteSpace K] (h : PowerSeries K) (d : ℕ) (hd : 0 < d)
    (hi : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) (h1 : ‖PowerSeries.coeff d h‖ = 1)
    (hl : ∀ k < d, ‖PowerSeries.coeff k h‖ < 1) :
    ∃ (q : PowerSeries K) (r : Polynomial K), (∀ n, ‖PowerSeries.coeff n q‖ ≤ 1) ∧
      ‖PowerSeries.coeff 0 q‖ = 1 ∧ r.degree < d ∧ (∀ n, ‖r.coeff n‖ < 1) ∧
      PowerSeries.X ^ d = h * q + (r : PowerSeries K) := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range d)
    (fun k => ‖PowerSeries.coeff k h‖) ⟨0, Finset.mem_range.2 hd⟩
  let g : PowerSeries (ball K) := PowerSeries.mk fun n => ⟨PowerSeries.coeff n h, hi n⟩
  have hg : ∀ n, ((PowerSeries.coeff n g : ball K) : K) = PowerSeries.coeff n h := fun n => by
    simp [g]
  let p : ball K := PowerSeries.coeff k g
  have hp : ‖(p : K)‖ < 1 := by rw [hg]; exact hl k (Finset.mem_range.1 hk)
  set I : Ideal (ball K) := Ideal.span {p} with hI
  have hmem : ∀ x : ball K, x ∈ I ↔ ‖(x : K)‖ ≤ ‖(p : K)‖ := fun x => by
    simpa using mem_span_pow p x 1
  have hlow : ∀ j < d, PowerSeries.coeff j g ∈ I := fun j hj => by
    rw [hmem, hg, hg]; exact hmax j (Finset.mem_range.2 hj)
  have hord : (g.map (Ideal.Quotient.mk I)).order = d := by
    rw [PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [PowerSeries.coeff_map, Ne, Ideal.Quotient.eq_zero_iff_mem, hmem, hg, h1]
      exact not_le.2 hp
    · rw [PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
      exact hlow i hi
  have hord' : (g.map (Ideal.Quotient.mk I)).order.toNat = d := by rw [hord]; rfl
  have H : g.IsWeierstrassDivisorAt I := by
    rw [PowerSeries.IsWeierstrassDivisorAt, hord']
    have h0 : PowerSeries.coeff d h ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff d h)⁻¹, ?_⟩ (Subtype.ext ?_)
    · change ‖(PowerSeries.coeff d h)⁻¹‖ ≤ 1
      rw [norm_inv, h1, inv_one]
    · rw [Subring.coe_mul, hg]
      exact mul_inv_cancel₀ h0
  haveI := adicComplete p hp
  have HD := H.isWeierstrassDivisionAt_div_mod (PowerSeries.X ^ d)
  set q := H.div (PowerSeries.X ^ d)
  set r := H.mod (PowerSeries.X ^ d)
  have hdeg : r.degree < d := hord' ▸ HD.degree_lt
  have hgh : g.map (ball K).subtype = h := by
    ext n; simp [hg]
  refine ⟨q.map (ball K).subtype, r.map (ball K).subtype, fun n => ?_, ?_,
    lt_of_le_of_lt (Polynomial.degree_map_le) hdeg, fun n => ?_, ?_⟩
  · rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff n q).2
  · have e := congrArg (PowerSeries.coeff d) HD.eq_mul_add
    rw [g.eq_X_pow_mul_shift_add_trunc d, add_mul, mul_assoc, map_add (f := _), map_add (f := _),
      PowerSeries.coeff_X_pow_self, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_degree_lt hdeg, add_zero, PowerSeries.coeff_X_pow_mul',
      if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_mul] at e
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton] at e
    have e2 : PowerSeries.coeff d (((g.trunc d : Polynomial (ball K)) : PowerSeries (ball K)) * q) ∈ I := by
      refine PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) d
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hh
      · exact hlow i hh
      · exact zero_mem _
    have e3 := ((hmem _).1 e2).trans_lt hp
    have e4 := congrArg (fun z : ball K => (z : K)) e
    simp only [PowerSeries.coeff_mk, zero_add, Subring.coe_add, Subring.coe_mul, hg, OneMemClass.coe_one] at e4
    rw [PowerSeries.coeff_map]
    refine le_antisymm (PowerSeries.coeff 0 q).2 (not_lt.1 fun hlt => ?_)
    have e5 := congrArg norm e4
    rw [norm_one] at e5
    refine absurd (e5.le.trans (IsUltrametricDist.norm_add_le_max _ _)) (not_le.2 (max_lt ?_ e3))
    rw [norm_mul, h1, one_mul]
    exact hlt
  · rw [Polynomial.coeff_map]
    by_cases hn : n < d
    · have := HD.coeff_f_sub_r_mem (i := n) (hord'.symm ▸ hn)
      rw [map_sub, PowerSeries.coeff_X_pow, if_neg hn.ne, zero_sub, neg_mem_iff,
        Polynomial.coeff_coe] at this
      exact ((hmem _).1 this).trans_lt hp
    · rw [Polynomial.coeff_eq_zero_of_degree_lt (hdeg.trans_le (by exact_mod_cast not_lt.1 hn))]
      simp
  · have := congrArg (PowerSeries.map (ball K).subtype) HD.eq_mul_add
    rw [map_pow, PowerSeries.map_X, map_add (f := _), map_mul, hgh] at this
    rw [this, Polynomial.polynomial_map_coe]

theorem root_small [IsAlgClosed K] (r : Polynomial K) (d : ℕ) (hd : 0 < d) (hr : r.degree < d)
    (hc : ∀ n, ‖r.coeff n‖ < 1) : ∃ x : K, ‖x‖ < 1 ∧ (Polynomial.X ^ d - r).eval x = 0 := by
  have hdeg : (Polynomial.X ^ d - r).degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Polynomial.X ^ d - r)
    (by rw [hdeg]; exact_mod_cast hd.ne')
  refine ⟨x, not_le.1 fun h1 => ?_, hx⟩
  have e : x ^ d = ∑ i ∈ Finset.range d, r.coeff i * x ^ i := by
    have := hx.eq_zero
    rw [Polynomial.eval_sub, sub_eq_zero, Polynomial.eval_pow, Polynomial.eval_X] at this
    rw [this]
    by_cases h0 : r = 0
    · simp [h0]
    exact Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_lt_iff_degree_lt h0).2 hr) x
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (t := Finset.range d) ⟨0, Finset.mem_range.2 hd⟩ (fun i => r.coeff i * x ^ i)
  rw [← e, norm_mul, norm_pow, norm_pow] at hle
  have h2 : ‖x‖ ^ i ≤ ‖x‖ ^ d := pow_le_pow_right₀ h1 (Finset.mem_range.1 hi).le
  have h3 : 0 < ‖x‖ ^ i := by positivity
  have h4 := hc i
  nlinarith

end GlobalTheory.ConvSer.DiscRoot

theorem GlobalTheory.ConvSer.exists_root_of_weierstrassDegree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] (h : PowerSeries K) (d : ℕ), 0 < d → Intg h → ‖PowerSeries.coeff d h‖ = 1 → (∀ k < d, ‖PowerSeries.coeff k h‖ < 1) → ∃ x : K, ‖x‖ < 1 ∧ ev1 h x = 0 := by
  intro K _ _ _ _ h d hd hi h1 hl
  obtain ⟨-, -, hA, -, -, -, -, -, -, hB⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  obtain ⟨q, r, hq, hq0, hr, hrc, e⟩ := DiscRoot.division h d hd ((hB h).1.1 hi) h1 hl
  obtain ⟨x, hx, hx0⟩ := DiscRoot.root_small r d hd hr hrc
  refine ⟨x, hx, ?_⟩
  obtain ⟨-, hmul, -, -, hP, -, hI, -⟩ := GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  have hq' : Intg q := (hB q).1.2 hq
  have e2 : ((Polynomial.X ^ d - r : Polynomial K) : PowerSeries K) = h * q := by
    rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, e]; ring
  have e3 := (hP (Polynomial.X ^ d - r)).2
  rw [hx0, e2, (hmul h q ((hA h 0).2.2 hi) ((hA q 0).2.2 hq')).2.2] at e3
  refine (mul_eq_zero.1 e3).resolve_right fun h0 => ?_
  have := (hI q hq').2.1
  rw [h0, zero_sub, norm_neg, hq0] at this
  exact absurd hx (not_lt.2 this)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRootOpenDiscOfWeierstrassDegreeStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] (h : PowerSeries K) (d : ℕ), 0 < d → Intg h → ‖PowerSeries.coeff d h‖ = 1 → (∀ k < d, ‖PowerSeries.coeff k h‖ < 1) → ∃ x : K, ‖x‖ < 1 ∧ ev1 h x = 0 := by
  first | exact @GlobalTheory.ConvSer.exists_root_of_weierstrassDegree | exact GlobalTheory.ConvSer.exists_root_of_weierstrassDegree | (intros; apply GlobalTheory.ConvSer.exists_root_of_weierstrassDegree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupHeightOneTorsionTower
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem intg_nMul_of_intg (K : Type) [NormedField K] [IsUltrametricDist K] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (n : ℕ) : Intg (nMul F n) := by
  obtain ⟨-, -, -, -, hX, -, hsub, -⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  induction n with
  | zero =>
    rw [nMul_zero]
    intro ν
    simp
  | succ n ih =>
    rw [nMul_succ]
    have hc : PowerSeries.constantCoeff (nMul F n) = 0 := ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 n).1
    refine (hsub (Fin 2) ![nMul F n, PowerSeries.X] F.toPowerSeries ?_ ?_).1 hF
    · intro j
      fin_cases j
      · exact ih
      · exact (hX ()).1
    · intro j
      fin_cases j
      · exact hc
      · exact PowerSeries.constantCoeff_X

theorem exists_torsion_tower (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (hp : ‖PowerSeries.coeff p (nMul F p)‖ = 1)
    (hlt : ∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) :
    ∃ t : ℕ → K, (∀ n, ‖t n‖ < 1) ∧ t 0 = 0 ∧ t 1 ≠ 0 ∧
      ∀ n, ev1 (nMul F p) (t (n + 1)) = t n := by
  classical
  have hpr : p.Prime := Fact.out
  have hI := intg_nMul_of_intg K F hF p
  set h := nMul F p with hh
  obtain ⟨-, -, hpow, -, -, -, -, -, -, hiff⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  have hev := fun (x : K) (hx : ‖x‖ < 1) => GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  have hbdd : ∀ f : PowerSeries K, Intg f → Bdd f := fun f hf => (hpow f 0).2.2 hf
  have hcoef : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1 := (hiff h).1.1 hI
  have h0 : PowerSeries.coeff 0 h = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).1
  have h0c : PowerSeries.constantCoeff h = 0 := ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).1
  have h1 : PowerSeries.coeff 1 h = (p : K) := ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).2
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  have hz : ‖(0 : K)‖ < 1 := by simp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hzero⟩ := hev 0 hz

  have hstep : ∀ c : {c : K // ‖c‖ < 1}, ∃ y : {y : K // ‖y‖ < 1}, ev1 h y = c := by
    rintro ⟨c, hc⟩
    have hIc : Intg (h - PowerSeries.C c) := by
      rw [(hiff _).1]
      intro n
      rcases n with _ | n
      · simp [h0c, hc.le]
      · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n), sub_zero]
        exact hcoef _
    obtain ⟨y, hy, hy0⟩ := GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree K (h - PowerSeries.C c) p hpr.pos hIc (by
        rw [map_sub, PowerSeries.coeff_C, if_neg hpr.ne_zero, sub_zero]
        exact hp) (by
        intro k hk
        rcases k with _ | k
        · simpa [h0, h0c] using hc
        · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero k), sub_zero]
          exact hlt _ hk)
    refine ⟨⟨y, hy⟩, ?_⟩
    obtain ⟨-, hops, hCe, -⟩ := hev y hy
    have hCI : Intg (PowerSeries.C c) := by
      rw [(hiff _).1]
      intro n
      rw [PowerSeries.coeff_C]
      split_ifs
      · exact hc.le
      · simp
    have e := (hops h (PowerSeries.C c) (hbdd h hI) (hbdd _ hCI)).2.1
    rw [hy0, hCe] at e
    simp only
    linear_combination -e

  set g : PowerSeries K := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) h with hg
  have hgI : Intg g := by
    rw [(hiff _).1]
    intro n
    rw [hg, PowerSeries.coeff_mk]
    exact hcoef _
  have hp1 : 0 < p - 1 := by have := hpr.two_le; omega
  obtain ⟨x, hx, hx0⟩ := GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree K g (p - 1) hp1 hgI (by
      rw [hg, PowerSeries.coeff_mk, Nat.sub_add_cancel hpr.one_lt.le]
      exact hp) (by
      intro k hk
      rw [hg, PowerSeries.coeff_mk]
      exact hlt _ (by omega))
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [hzero, hg, PowerSeries.coeff_mk, h1] at hx0
    exact hp0 hx0
  have hXI : Intg (PowerSeries.X : PowerSeries K) := by
    rw [(hiff _).1]
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs <;> simp
  have hXg : h = PowerSeries.X * g := by
    ext n
    rcases n with _ | n
    · simp [h0]
    · rw [PowerSeries.coeff_succ_X_mul, hg, PowerSeries.coeff_mk]
  have hxroot : ev1 h x = 0 := by
    obtain ⟨-, hops, -, hXe, -⟩ := hev x hx
    rw [hXg, ((hops _ _ (hbdd _ hXI) (hbdd _ hgI)).2.2), hXe, hx0, mul_zero]
  choose f hf using hstep
  let x0 : {y : K // ‖y‖ < 1} := ⟨x, hx⟩
  refine ⟨fun n => if n = 0 then 0 else ((f^[n - 1] x0 : {y : K // ‖y‖ < 1}) : K), ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs
    · exact hz
    · exact (f^[n - 1] x0).2
  · simp
  · simpa [x0] using hxne
  · intro n
    rcases n with _ | m
    · simpa [x0] using hxroot
    · simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _), Function.iterate_succ_apply']
      exact hf _

end GlobalTheory.ConvSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupHeightOneTorsionTowerStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalGroup_heightOne_torsion_tower : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ‖PowerSeries.coeff p (nMul F p)‖ = 1 → (∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) → ∃ t : ℕ → K, (∀ n, ‖t n‖ < 1) ∧ t 0 = 0 ∧ t 1 ≠ 0 ∧ ∀ n, ev1 (nMul F p) (t (n + 1)) = t n := by
  first | exact @GlobalTheory.ConvSer.exists_torsion_tower | exact GlobalTheory.ConvSer.exists_torsion_tower | (intros; apply GlobalTheory.ConvSer.exists_torsion_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralMvPowerSeriesTwoEqZeroOfVanishOnSquares
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralMvPowerSeriesTwoEqZeroOfVanishOnSquares
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

private theorem intg_of_norm_coeff_le_one {K : Type} [NormedField K] (f : PowerSeries K)
    (h : ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) : Intg f := by
  intro ν
  have h1 := h (ν ())
  have h2 : ν = Finsupp.single () (ν ()) := Finsupp.unique_single ν
  rw [h2]
  exact h1

theorem integralPowerSeries_eq_zero_of_vanish_on_points (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : ℕ → Finset K) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hG : ∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1)
    (hT : Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0))
    (h : PowerSeries K) (hh : Intg h) (m : ℕ)
    (hz : ∀ n, m ≤ n → ∀ x ∈ G n, ev1 h x = 0) : h = 0 := by
  ext k
  have key : ‖PowerSeries.coeff k h‖ * r ^ k ≤ 0 := by
    refine ge_of_tendsto hT ?_
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    exact (GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros K h (G n) hh (fun x hx => ⟨(hG n x hx).2, hz n hn x hx⟩)).1 r hr hr1
      (fun x hx => (hG n x hx).1) k
  have hp : 0 < r ^ k := pow_pos hr k
  have h0 : ‖PowerSeries.coeff k h‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hc hp
    linarith
  simpa using norm_le_zero_iff.mp h0

theorem eq_zero_of_ev_vanish : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ H : MvPowerSeries (Fin 2) K, Intg H → (∀ n, ∀ x ∈ G n, ∀ y ∈ G n, ev H ![x, y] = 0) → H = 0 := by
  intro K _ _ _ G r hr hr1 hmono hG hT H hH hz
  have hS : ∀ (x y : K), ‖x‖ < 1 → ‖y‖ < 1 →
      Intg (shift1 H y) ∧ ev1 (shift1 H y) x = ev H ![x, y] := fun x y hx hy =>
    (GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx).2.2.2.2.2.2.2.2.2.1 H y hy hH
  have h1 : ∀ m, ∀ y ∈ G m, shift1 H y = 0 := by
    intro m y hy
    have hy1 := (hG m y hy).2
    refine integralPowerSeries_eq_zero_of_vanish_on_points K G r hr hr1 hG hT _ (hS 0 y (by simp) hy1).1 m ?_
    intro n hn x hx
    rw [(hS x y (hG n x hx).2 hy1).2]
    exact hz n x hx y (hmono hn hy)
  have h2 : ∀ a b : ℕ,
      MvPowerSeries.coeff (Finsupp.single 0 a + Finsupp.single 1 b) H = 0 := by
    intro a b
    have h3 : (PowerSeries.mk fun b : ℕ =>
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b) H) = 0 := by
      refine integralPowerSeries_eq_zero_of_vanish_on_points K G r hr hr1 hG hT _ (intg_of_norm_coeff_le_one _ ?_) 0 ?_
      · intro n
        rw [PowerSeries.coeff_mk]
        exact hH _
      · intro n _ y hy
        have h4 := congrArg (PowerSeries.coeff a) (h1 n y hy)
        rw [shift1, PowerSeries.coeff_mk, map_zero] at h4
        simpa [ev1, PowerSeries.coeff_mk] using h4
    have h5 := congrArg (PowerSeries.coeff b) h3
    rwa [PowerSeries.coeff_mk, map_zero] at h5
  ext ν
  have hν : ν = Finsupp.single 0 (ν 0) + Finsupp.single 1 (ν 1) := by
    ext i
    fin_cases i <;> simp
  rw [hν, h2]
  simp

end GlobalTheory.ConvSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralMvPowerSeriesTwoEqZeroOfVanishOnSquaresStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralMvPowerSeries_two_eq_zero_of_vanish_on_squares : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ H : MvPowerSeries (Fin 2) K, Intg H → (∀ n, ∀ x ∈ G n, ∀ y ∈ G n, ev H ![x, y] = 0) → H = 0 := by
  first | exact @GlobalTheory.ConvSer.eq_zero_of_ev_vanish | exact GlobalTheory.ConvSer.eq_zero_of_ev_vanish | (intros; apply GlobalTheory.ConvSer.eq_zero_of_ev_vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLimitPowerSeriesAgreeOnAnnulusPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLimitPowerSeriesAgreeOnAnnulusPoints
open GlobalTheory.ConvSer Filter Topology

namespace GlobalTheory.ConvSer

theorem intg_iff_coeff_one_var {K : Type} [NormedField K] (f : PowerSeries K) :
    Intg f ↔ ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1 := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h ν
    have hν : ν = Finsupp.single () (ν ()) := by
      ext; simp
    rw [hν]
    exact h (ν ())

theorem norm_coeff_mul_pow_le_of_intg {K : Type} [NormedField K] {f : PowerSeries K}
    (hf : Intg f) (x : K) (k : ℕ) : ‖PowerSeries.coeff k f * x ^ k‖ ≤ ‖x‖ ^ k := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) ((intg_iff_coeff_one_var f).1 hf k)

theorem summable_coeff_mul_pow_of_intg {K : Type} [NormedField K] [CompleteSpace K]
    {f : PowerSeries K} (hf : Intg f) {x : K} (hx : ‖x‖ < 1) :
    Summable fun k : ℕ => PowerSeries.coeff k f * x ^ k :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg x) hx)
    (norm_coeff_mul_pow_le_of_intg hf x)

theorem exists_tendsto_of_sub_tendsto_zero_ultra {K : Type} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (a : ℕ → K) (h : Tendsto (fun n => a (n + 1) - a n) atTop (𝓝 0)) :
    ∃ l, Tendsto a atTop (𝓝 l) := by
  have hs : Summable fun n => a (n + 1) - a n :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by rwa [Nat.cofinite_eq_atTop])
  have h1 := hs.hasSum.tendsto_sum_nat
  simp only [Finset.sum_range_sub] at h1
  refine ⟨_, (h1.add_const (a 0)).congr fun n => ?_⟩
  simp

theorem exists_limit_of_agree_on_points : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ g : ℕ → PowerSeries K, (∀ n, Intg (g n)) → (∀ n, ∀ x ∈ G n, ev1 (g (n + 1)) x = ev1 (g n) x) → ∃ f : PowerSeries K, Intg f ∧ (∀ k, Filter.Tendsto (fun n => PowerSeries.coeff k (g n)) Filter.atTop (nhds (PowerSeries.coeff k f))) ∧ ∀ n, ∀ x ∈ G n, ev1 f x = ev1 (g n) x := by
  intro K _ _ _ G r hr hr1 hG hx hprod g hg hagree
  have hcoef : ∀ n k, ‖PowerSeries.coeff k (g (n + 1)) - PowerSeries.coeff k (g n)‖ ≤
      (∏ x ∈ G n, ‖x‖) / r ^ k := by
    intro n k
    have hI : Intg (g (n + 1) - g n) := by
      rw [intg_iff_coeff_one_var]
      intro j
      rw [map_sub, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact (intg_iff_coeff_one_var _).1 (hg _) j
      · rw [norm_neg]; exact (intg_iff_coeff_one_var _).1 (hg _) j
    have hz : ∀ x ∈ G n, ‖x‖ < 1 ∧ ev1 (g (n + 1) - g n) x = 0 := by
      intro x hxn
      refine ⟨(hx n x hxn).2, ?_⟩
      have h1 := summable_coeff_mul_pow_of_intg (hg (n + 1)) (hx n x hxn).2
      have h2 := summable_coeff_mul_pow_of_intg (hg n) (hx n x hxn).2
      have h3 := hagree n x hxn
      unfold ev1 at h3 ⊢
      simp only [map_sub, sub_mul]
      rw [h1.tsum_sub h2, h3, sub_self]
    have := (GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros K _ (G n) hI hz).1 r hr hr1 (fun x hxn => (hx n x hxn).1) k
    rw [map_sub] at this
    rwa [le_div_iff₀ (by positivity)]
  have hlim : ∀ k, ∃ l, Tendsto (fun n => PowerSeries.coeff k (g n)) atTop (𝓝 l) := by
    intro k
    apply exists_tendsto_of_sub_tendsto_zero_ultra
    refine squeeze_zero_norm (fun n => hcoef n k) ?_
    simpa using hprod.div_const (r ^ k)
  choose c hc using hlim
  have hfI : Intg (PowerSeries.mk c) := by
    rw [intg_iff_coeff_one_var]
    intro k
    rw [PowerSeries.coeff_mk]
    exact le_of_tendsto' (hc k).norm fun n => (intg_iff_coeff_one_var _).1 (hg n) k
  refine ⟨PowerSeries.mk c, hfI, fun k => by simpa using hc k, ?_⟩
  intro n x hxn
  have hx1 := (hx n x hxn).2
  have hconst : ∀ m, n ≤ m → ev1 (g m) x = ev1 (g n) x := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [hagree m x (hG hm hxn), ih]
  have ht : Tendsto (fun m => ev1 (g m) x) atTop (𝓝 (ev1 (PowerSeries.mk c) x)) := by
    unfold ev1
    refine tendsto_tsum_of_dominated_convergence (bound := fun k => ‖x‖ ^ k)
      (summable_geometric_of_lt_one (norm_nonneg x) hx1) (fun k => ?_)
      (Eventually.of_forall fun m k => norm_coeff_mul_pow_le_of_intg (hg m) x k)
    rw [PowerSeries.coeff_mk]
    exact (hc k).mul_const _
  have ht2 : Tendsto (fun m => ev1 (g m) x) atTop (𝓝 (ev1 (g n) x)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop n).mono fun m hm => (hconst m hm).symm)
  exact tendsto_nhds_unique ht ht2

end GlobalTheory.ConvSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLimitPowerSeriesAgreeOnAnnulusPointsStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_powerSeries_agree_on_annulus_points : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ g : ℕ → PowerSeries K, (∀ n, Intg (g n)) → (∀ n, ∀ x ∈ G n, ev1 (g (n + 1)) x = ev1 (g n) x) → ∃ f : PowerSeries K, Intg f ∧ (∀ k, Filter.Tendsto (fun n => PowerSeries.coeff k (g n)) Filter.atTop (nhds (PowerSeries.coeff k f))) ∧ ∀ n, ∀ x ∈ G n, ev1 f x = ev1 (g n) x := by
  first | exact @GlobalTheory.ConvSer.exists_limit_of_agree_on_points | exact GlobalTheory.ConvSer.exists_limit_of_agree_on_points | (intros; apply GlobalTheory.ConvSer.exists_limit_of_agree_on_points <;> assumption)
end
end

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.HeightOne

theorem exists_root_tower (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (p : ℕ)
    [hp : Fact p.Prime] :
    ∃ ζ : ℕ → K, ζ 0 = 1 ∧ IsPrimitiveRoot (ζ 1) p ∧ (∀ n, ζ (n + 1) ^ p = ζ n) ∧
      ∀ n, ζ n ^ p ^ n = 1 := by
  have hp0 : 0 < p := hp.out.pos
  have : NeZero p := ⟨hp0.ne'⟩
  obtain ⟨z, hz⟩ : ∃ z : K, IsPrimitiveRoot z p := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  choose r hr using fun x : K => IsAlgClosed.exists_pow_nat_eq x hp0
  have h : ∀ n, (fun n : ℕ => Nat.casesOn (motive := fun _ => K) n 1 fun m => r^[m] z) (n + 1) ^ p
      = (fun n : ℕ => Nat.casesOn (motive := fun _ => K) n 1 fun m => r^[m] z) n := by
    intro n
    cases n with
    | zero => exact hz.pow_eq_one
    | succ m =>
      show (r^[m + 1] z) ^ p = r^[m] z
      rw [Function.iterate_succ_apply', hr]
  refine ⟨fun n : ℕ => Nat.casesOn (motive := fun _ => K) n 1 fun m => r^[m] z, rfl, hz, h, ?_⟩
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, h n]; exact ih

theorem norm_le_pow_of_primitive {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) {z : K} (hz : IsPrimitiveRoot z p) :
    ‖(p : K)‖ ≤ ‖z - 1‖ ^ (p - 1) := by
  have hz1 : ‖z‖ = 1 := by
    have h := congrArg norm hz.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 h
  have hle : ∀ j : ℕ, ‖1 - z ^ j‖ ≤ ‖z - 1‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have : 1 - z ^ (j + 1) = (1 - z ^ j) + -(z ^ j * (z - 1)) := by ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
      rw [norm_neg, norm_mul, norm_pow, hz1, one_pow, one_mul]
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have h := hz.prod_one_sub_pow_eq_order
  have h2 : ((m + 1 : ℕ) : K) = ∏ k ∈ Finset.range m, (1 - z ^ (k + 1)) := by
    rw [h]; push_cast; ring
  rw [h2, norm_prod, Nat.add_sub_cancel]
  calc ∏ k ∈ Finset.range m, ‖1 - z ^ (k + 1)‖ ≤ ∏ _k ∈ Finset.range m, ‖z - 1‖ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hle _)
    _ = _ := by simp

theorem exists_iso_multiplicative (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]
    (F : FormalGroup K) (hF : Intg F.toPowerSeries)
    (h1 : ‖PowerSeries.coeff p (nMul F p)‖ = 1)
    (h2 : ∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) :
    ∃ f : PowerSeries K, Intg f ∧ PowerSeries.constantCoeff f = 0 ∧ ‖PowerSeries.coeff 1 f‖ = 1 ∧
      f.subst F.toPowerSeries = f.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) +
        f.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) +
        f.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) *
          f.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
  classical
  obtain ⟨t, ht1, ht0, htne, htp⟩ := GlobalTheory.T.exists_formalGroup_heightOne_torsion_tower K p F hF h1 h2
  obtain ⟨ζ, hζ0, hζ1, hζp, hζn⟩ := exists_root_tower K p
  obtain ⟨-, hpt⟩ := GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties K F hF
  obtain ⟨ho1, -, ho3⟩ := GlobalTheory.T.formalGroup_torsionTower_exact_order K p F hF t ht1 ht0 htne htp
  obtain ⟨hn1, hn2, hn3, hn4⟩ := GlobalTheory.T.norm_formalGroup_heightOne_torsion_tower K p F hF h1 h2 t ht1 ht0 htne htp
  choose g hgI hgv using fun n => GlobalTheory.T.exists_integral_polynomial_torsion_character_level K p F hF t ht1 ht0 htne htp n (ζ n) (hζn n)
  obtain ⟨bI, -, bP, bC, bX, -, -, bS, -, bf⟩ := GlobalTheory.BddAlg.bdd_alg K (Fin 2)
  obtain ⟨bI1, -, bP1, bC1, -⟩ := GlobalTheory.BddAlg.bdd_alg K Unit
  set P : ℕ → ℕ → K := fun n j => ev1 (nMul F j) (t n) with hP
  have hP0 : ∀ n, P n 0 = 0 := fun n => (hpt _ (ht1 n)).1
  have hPlt : ∀ n j, ‖P n j‖ < 1 := fun n j =>
    (((hpt _ (ht1 n)).2.2.1 j).1).trans_lt (ht1 n)
  set G : ℕ → Finset K := fun n => (Finset.Ico 1 (p ^ n)).image (P n) with hG
  have hpn : ∀ n, 0 < p ^ n := fun n => pow_pos hp.out.pos n
  have hmem : ∀ n x, x ∈ G n ↔ ∃ j, ¬ p ^ n ∣ j ∧ P n j = x := by
    intro n x
    simp only [hG, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      exact ⟨j, Nat.not_dvd_of_pos_of_lt hj1 hj2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j % p ^ n, ⟨?_, Nat.mod_lt _ (hpn n)⟩, (ho3 n _ _).2 (Nat.mod_modEq _ _)⟩
      exact Nat.pos_of_ne_zero fun h => hj (Nat.dvd_of_mod_eq_zero h)
  have hmono : Monotone G := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    obtain ⟨j, hj, rfl⟩ := (hmem n x).1 hx
    refine (hmem _ _).2 ⟨p * j, fun h => hj ?_, ho1 n j⟩
    rw [pow_succ'] at h
    exact Nat.dvd_of_mul_dvd_mul_left hp.out.pos h
  have hr0 : 0 < ‖t 1‖ := norm_pos_iff.2 htne
  have hGr : ∀ n, ∀ x ∈ G n, ‖t 1‖ ≤ ‖x‖ ∧ ‖x‖ < 1 := by
    intro n x hx
    obtain ⟨j, hj, rfl⟩ := (hmem n x).1 hx
    exact ⟨hn3 n j hj, hPlt n j⟩
  have hlim : Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) := by
    have : (fun n => ∏ x ∈ G n, ‖x‖) = fun n => ‖(p : K)‖ ^ n := by
      funext n
      rw [← hn4 n, hG]
      refine Finset.prod_image ?_
      intro i hi j hj hij
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
      exact Nat.ModEq.eq_of_lt_of_lt ((ho3 n i j).1 hij) hi.2 hj.2
    rw [this]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hn2
  have hgev : ∀ n m j k, P m k = P n j → ev1 (g m : PowerSeries K) (P n j) = ζ m ^ k := by
    intro n m j k h
    rw [((GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K _ (hPlt n j)).2.2.2.2.1 (g m)).2, ← h]
    exact hgv m k
  obtain ⟨φ, hφI, hφc, hφv⟩ := GlobalTheory.T.exists_limit_powerSeries_agree_on_annulus_points K G ‖t 1‖ hr0 (ht1 1).le hmono hGr hlim
    (fun n => (g n : PowerSeries K))
    (fun n => (bf _).1.2 fun k => by rw [Polynomial.coeff_coe]; exact hgI n k)
    (by
      intro n x hx
      obtain ⟨j, -, rfl⟩ := (hmem n x).1 hx
      rw [hgev n (n + 1) j (p * j) (ho1 n j), hgev n n j j rfl, pow_mul, hζp])
  have hφ0 : PowerSeries.coeff 0 φ = 1 := by
    have h := hφc 0
    have : (fun n => PowerSeries.coeff 0 (g n : PowerSeries K)) = fun _ => (1 : K) := by
      funext n
      have h3 := hgv n 0
      change (g n).eval (P n 0) = _ at h3
      rw [hP0, pow_zero] at h3
      rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, h3]
    rw [this] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hz : ‖(0 : K)‖ < 1 := by simp
  have hφP : ∀ n j, ev1 φ (P n j) = ζ n ^ j := by
    intro n j
    by_cases hj : p ^ n ∣ j
    · have : P n j = 0 := by
        rw [← hP0 n]
        exact (ho3 n _ _).2 ((Nat.modEq_zero_iff_dvd).2 hj)
      rw [this, (GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K 0 hz).2.2.2.2.2.2.2.2.2.2 φ, hφ0]
      obtain ⟨c, rfl⟩ := hj
      rw [pow_mul, hζn, one_pow]
    · rw [hφv n _ ((hmem _ _).2 ⟨j, hj, rfl⟩)]
      exact hgev n n j j rfl
  have hC1 : Intg (PowerSeries.C (1 : K) : PowerSeries K) := (bC1 1).2.1 (by simp)
  set f : PowerSeries K := φ - PowerSeries.C 1 with hf
  have hfI : Intg f := (bI1 _ _ hφI hC1).2.1
  have hfB : Bdd f := (bP1 _ 0).2.2 hfI
  have hf0 : PowerSeries.coeff 0 f = 0 := by
    rw [hf, map_sub, hφ0]; simp
  have hfP : ∀ n j, ev1 f (P n j) = ζ n ^ j - 1 := by
    intro n j
    have h := GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K _ (hPlt n j)
    rw [hf, (h.2.1 φ _ ((bP1 _ 0).2.2 hφI) ((bP1 _ 0).2.2 hC1)).2.1, h.2.2.1, hφP]
  refine ⟨f, hfI, by simpa using hf0, ?_, ?_⟩
  · by_contra hne
    have hlt : ‖PowerSeries.coeff 1 f‖ < 1 := lt_of_le_of_ne ((bf f).1.1 hfI 1) hne
    have hv : ev1 f (t 1) = ζ 1 - 1 := by
      have h := hfP 1 1
      rw [pow_one] at h
      rw [← h]
      congr 1
      exact ((hpt _ (ht1 1)).2.1).symm
    have he := ((GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K _ (ht1 1)).2.2.2.2.2.2.1 f hfI).2.2
    rw [hv, hf0, sub_zero] at he
    have hlt2 : ‖ζ 1 - 1‖ < ‖t 1‖ := by
      have : ζ 1 - 1 = (ζ 1 - 1 - PowerSeries.coeff 1 f * t 1) + PowerSeries.coeff 1 f * t 1 := by
        ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (he.trans_lt ?_) ?_)
      · have := ht1 1
        nlinarith
      · rw [norm_mul]
        nlinarith
    have h3 := norm_le_pow_of_primitive hp.out hζ1
    have h4 : ‖ζ 1 - 1‖ ^ (p - 1) < ‖t 1‖ ^ (p - 1) :=
      pow_lt_pow_left₀ hlt2 (norm_nonneg _) (Nat.sub_ne_zero_of_lt hp.out.one_lt)
    linarith
  · have hF0 : MvPowerSeries.constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
    have hX : ∀ i : Fin 2, Intg (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
      fun i => (bX i).1
    have hX0 : ∀ i : Fin 2,
        MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
      fun i => MvPowerSeries.constantCoeff_X i
    have iF := (bS _ f hF hF0).1 hfI
    have i0 := (bS _ f (hX 0) (hX0 0)).1 hfI
    have i1 := (bS _ f (hX 1) (hX0 1)).1 hfI
    have i01 := (bI _ _ i0 i1).1
    have i01' := (bI _ _ i0 i1).2.2
    have iR := (bI _ _ i01 i01').1
    have bd : ∀ S : MvPowerSeries (Fin 2) K, Intg S → Bdd S := fun S h => (bP S 0).2.2 h
    rw [← sub_eq_zero]
    refine GlobalTheory.T.integralMvPowerSeries_two_eq_zero_of_vanish_on_squares K G ‖t 1‖ hr0 (ht1 1).le hmono hGr hlim _ (bI _ _ iF iR).2.1 ?_
    intro n x hx y hy
    obtain ⟨i, -, rfl⟩ := (hmem n x).1 hx
    obtain ⟨j, -, rfl⟩ := (hmem n y).1 hy
    obtain ⟨-, eA, -, eX, -, -, -, eS⟩ := GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties K (Fin 2) ![P n i, P n j]
      (Fin.forall_fin_two.2 ⟨hPlt n i, hPlt n j⟩)
    have hs : ev F.toPowerSeries ![P n i, P n j] = P n (i + j) := (hpt _ (ht1 n)).2.2.2.1 i j
    rw [(eA _ _ (bd _ iF) (bd _ iR)).2.1, (eA _ _ (bd _ i01) (bd _ i01')).1,
      (eA _ _ (bd _ i0) (bd _ i1)).1, (eA _ _ (bd _ i0) (bd _ i1)).2.2,
      eS _ f hF hF0 hfB, eS _ f (hX 0) (hX0 0) hfB, eS _ f (hX 1) (hX0 1) hfB, eX, eX, hs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hfP, hfP, hfP]
    ring

end GlobalTheory.ConvSer.HeightOne
end

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.HeightOneInt

theorem mulN_eq_nMul {R : Type} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    JetMomFound.mulN F n = nMul F n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [JetMomFound.mulN, nMul_succ, ih]

theorem mem_int_iff {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem isIsoGm_of_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (F : FormalGroup R) (f : PowerSeries R)
    (h0 : PowerSeries.constantCoeff f = 0) (h1 : IsUnit (PowerSeries.coeff 1 f))
    (h : (f.map φ).subst (F.map φ).toPowerSeries =
      (f.map φ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) +
        (f.map φ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S) +
        (f.map φ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) *
          (f.map φ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S)) :
    JetMomFound.IsIsoGm F f := by
  refine ⟨h0, h1, ?_⟩
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hc : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) f) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) f h0
  have hs : MvPowerSeries.HasSubst
      ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by
      intro s; fin_cases s <;> simp [hc])
  rw [FormalGroup.𝔾ₘ_toPowerSeries, MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs,
    MvPowerSeries.subst_mul hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin 2) φ) := by
    intro a b hab
    ext ν
    apply hφ
    rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, hab]
  apply hinj
  rw [map_add (f := _), map_add (f := _), map_mul, PowerSeries.map_subst hF, PowerSeries.map_subst (hX 0),
    PowerSeries.map_subst (hX 1), MvPowerSeries.map_X, MvPowerSeries.map_X]
  exact h

theorem htOneIsGm : JetMomFound.HtOneIsGm := by
  intro p _ F _ hH
  let φ : 𝓞_ℂ_[p] →+* ℂ_[p] := (𝓞_ℂ_[p]).subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have hI : Intg (F.map φ).toPowerSeries := by
    intro ν
    rw [FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map]
    exact (mem_int_iff _).1 (MvPowerSeries.coeff ν F.toPowerSeries).2
  have hn : ∀ k, PowerSeries.coeff k (nMul (F.map φ) p) =
      ((PowerSeries.coeff k (JetMomFound.mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    intro k
    rw [← (nMul_props _ F).2.2.2.2 _ φ p, PowerSeries.coeff_map, mulN_eq_nMul]
    rfl
  obtain ⟨f, hfI, hf0, hf1, hf⟩ := HeightOne.exists_iso_multiplicative ℂ_[p] p (F.map φ) hI
    (by rw [hn]; exact hH.1) (fun k hk => by rw [hn]; exact hH.2 k hk)
  let f₀ : PowerSeries 𝓞_ℂ_[p] := PowerSeries.mk fun n =>
    ⟨PowerSeries.coeff n f, (mem_int_iff _).2 (hfI (Finsupp.single () n))⟩
  have hc : ∀ n, φ (PowerSeries.coeff n f₀) = PowerSeries.coeff n f := by
    intro n
    simp only [f₀, PowerSeries.coeff_mk]
    rfl
  have hm : f₀.map φ = f := by
    ext n
    rw [PowerSeries.coeff_map, hc]
  refine ⟨f₀, isIsoGm_of_map φ hφ F f₀ ?_ ?_ (by rw [hm]; exact hf)⟩
  · apply hφ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc, map_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]
  · have hne : PowerSeries.coeff 1 f ≠ 0 := by
      intro h
      rw [h, norm_zero] at hf1
      exact zero_ne_one hf1
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff 1 f)⁻¹, (mem_int_iff _).2 ?_⟩ ?_
    · rw [norm_inv, hf1, inv_one]
    · apply hφ
      rw [map_mul, hc, map_one]
      exact mul_inv_cancel₀ hne

end GlobalTheory.ConvSer.HeightOneInt
