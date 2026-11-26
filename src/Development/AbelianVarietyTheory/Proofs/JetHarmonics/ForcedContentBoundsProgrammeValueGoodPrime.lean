module

public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.OrbitLabellings.FnumEqRhoMulSumOfDemandRatioLe
open scoped BigOperators
open Formalism.IncomingBounds

namespace UpperTheory.AlternatingNumberFlow

section Helpers

variable {l d : ℕ} [NeZero d]

private lemma oddLevels_one_le {d i : ℕ} (hi : i ∈ oddLevels d) : 1 ≤ i :=
  (Finset.mem_filter.1 hi).2.pos

private lemma one_mem_oddLevels {d : ℕ} (hd : 2 ≤ d) : 1 ∈ oddLevels d :=
  Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), odd_one⟩

private lemma gam_sub_inv (hl : 2 ≤ l) : gam l - 1 / ((l : ℝ) + 1) = rho l := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (l : ℝ) + 1 ≠ 0 := by linarith
  unfold gam rho
  field_simp
  ring

private lemma sum_incoming (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun s => x s i)

private lemma flowVal_mul_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    ((l : ℝ) + 1) * flowVal d x ≤ ∑ s, D s := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : ∑ s : ZMod d, ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
      ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i) ≤ ∑ s, D s :=
    Finset.sum_le_sum fun s _ => hx.2 s
  rw [Finset.sum_add_distrib, sum_incoming] at h1
  refine le_trans ?_ h1
  unfold flowVal
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hx0 := hx.1 s i
  have hli : (l : ℝ) ≤ (l : ℝ) ^ i := by
    calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hl' (oddLevels_one_le hi)
  nlinarith [mul_nonneg (sub_nonneg.2 hli) hx0]

private lemma zero_isFlow {D : ZMod d → ℝ} (hD : 0 ≤ D) : IsFlow l d D (0 : ZMod d → ℕ → ℝ) :=
  ⟨fun _ _ => le_refl _, fun s => by simpa using hD s⟩

private lemma maxFlow_le (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    maxFlow l d D ≤ (∑ s, D s) / ((l : ℝ) + 1) := by
  have hpos : (0 : ℝ) < l + 1 := by positivity
  apply csSup_le
  · exact ⟨0, (0 : ZMod d → ℕ → ℝ), zero_isFlow hD, by simp [flowVal]⟩
  · rintro t ⟨x, hx, rfl⟩
    rw [le_div_iff₀ hpos]
    linarith [flowVal_mul_le hl hx]

private lemma le_maxFlow (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ maxFlow l d D := by
  have hpos : (0 : ℝ) < l + 1 := by positivity
  apply le_csSup
  · refine ⟨(∑ s, D s) / ((l : ℝ) + 1), ?_⟩
    rintro t ⟨y, hy, rfl⟩
    rw [le_div_iff₀ hpos]
    linarith [flowVal_mul_le hl hy]
  · exact ⟨x, hx, rfl⟩

private noncomputable def altNum (l d : ℕ) (D : ZMod d → ℝ) (s : ZMod d) : ℝ :=
  ∑ r ∈ Finset.range (2 * d), (-1 : ℝ) ^ r * ((l : ℝ) ^ (r + 1))⁻¹ * D (s - (r : ZMod d))

private lemma altNum_rec (hl : 1 ≤ l) (D : ZMod d → ℝ) (s : ZMod d) :
    (l : ℝ) * altNum l d D s + altNum l d D (s - 1) = (1 - ((l : ℝ) ^ (2 * d))⁻¹) * D s := by
  have hl0 : (l : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  set a : ℕ → ℝ := fun r => (-1 : ℝ) ^ r * ((l : ℝ) ^ r)⁻¹ * D (s - (r : ZMod d)) with ha
  have h1 : (l : ℝ) * altNum l d D s = ∑ r ∈ Finset.range (2 * d), a r := by
    unfold altNum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [ha]
    rw [pow_succ]
    field_simp
  have h2 : altNum l d D (s - 1) = -∑ r ∈ Finset.range (2 * d), a (r + 1) := by
    unfold altNum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [ha]
    have : s - 1 - (r : ZMod d) = s - ((r + 1 : ℕ) : ZMod d) := by push_cast; ring
    rw [this, pow_succ (-1 : ℝ) r]
    ring
  rw [h1, h2, ← sub_eq_add_neg, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have h3 : ((2 * d : ℕ) : ZMod d) = 0 := by rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
  simp only [ha, pow_zero, inv_one, Nat.cast_zero, sub_zero, h3, (even_two_mul d).neg_one_pow]
  ring

private lemma sum_range_two_mul (f : ℕ → ℝ) (m : ℕ) :
    ∑ r ∈ Finset.range (2 * m), f r = ∑ u ∈ Finset.range m, (f (2 * u) + f (2 * u + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

private lemma altNum_nonneg (hl : 1 ≤ l) {D : ZMod d → ℝ}
    (hr : ∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s) (s : ZMod d) : 0 ≤ altNum l d D s := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  unfold altNum
  rw [sum_range_two_mul]
  refine Finset.sum_nonneg fun u _ => ?_
  have hB := hr (s - ((2 * u : ℕ) : ZMod d)) (s - ((2 * u + 1 : ℕ) : ZMod d))
  have hP : 0 < ((l : ℝ) ^ (2 * u + 1))⁻¹ := by positivity
  rw [(show Even (2 * u) from ⟨u, by ring⟩).neg_one_pow,
    (show Odd (2 * u + 1) from ⟨u, rfl⟩).neg_one_pow, pow_succ (l : ℝ) (2 * u + 1), mul_inv]
  have key : ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ * D (s - ((2 * u + 1 : ℕ) : ZMod d)) ≤
      ((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)) := by
    calc ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ * D (s - ((2 * u + 1 : ℕ) : ZMod d))
        ≤ ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ * ((l : ℝ) * D (s - ((2 * u : ℕ) : ZMod d))) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = ((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)) := by
          field_simp
  linarith

end Helpers

end UpperTheory.AlternatingNumberFlow

open UpperTheory.AlternatingNumberFlow in
theorem UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le :
    ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → ∀ D : ZMod d → ℝ, 0 ≤ D →
    (∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s) → Fnum l d D = rho l * (∑ s : ZMod d, D s) := by
  intro l d _ hl hd D hD0 hr
  have hD : 0 ≤ D := fun a => hD0 a
  have hr' : ∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s := fun s s' => hr s s'
  have hl1 : 1 ≤ l := by omega
  have hl' : (1 : ℝ) < l := by exact_mod_cast (show 1 < l by omega)
  have hlpos : (0 : ℝ) < l + 1 := by linarith
  have hden : 0 < 1 - ((l : ℝ) ^ (2 * d))⁻¹ := by
    have : 1 < (l : ℝ) ^ (2 * d) := one_lt_pow₀ hl' (by omega)
    have : ((l : ℝ) ^ (2 * d))⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith
  set c := 1 - ((l : ℝ) ^ (2 * d))⁻¹ with hc
  set y : ZMod d → ℝ := fun s => altNum l d D s / c with hy
  set x : ZMod d → ℕ → ℝ := fun s i => if i = 1 then y s else 0 with hx
  have hyrec : ∀ s, (l : ℝ) * y s + y (s - 1) = D s := by
    intro s
    simp only [hy]
    have := altNum_rec hl1 D s
    field_simp
    linarith
  have h1mem := one_mem_oddLevels hd
  have hflow : IsFlow l d D x := by
    refine ⟨fun s i => ?_, fun s => ?_⟩
    · simp only [hx]
      split_ifs
      · exact div_nonneg (altNum_nonneg hl1 hr' s) hden.le
      · exact le_refl _
    · simp only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', if_pos h1mem, pow_one, Nat.cast_one]
      rw [hyrec s]
  have hval : ((l : ℝ) + 1) * flowVal d x = ∑ s, D s := by
    have hfv : flowVal d x = ∑ s, y s := by
      unfold flowVal
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [hx, Finset.sum_ite_eq', if_pos h1mem]
    have hsh : ∑ s, y (s - 1) = ∑ s, y s := Equiv.sum_comp (Equiv.subRight (1 : ZMod d)) y
    rw [hfv, ← Finset.sum_congr rfl fun s _ => hyrec s, Finset.sum_add_distrib, hsh,
      ← Finset.mul_sum]
    ring
  have hmax : maxFlow l d D = (∑ s, D s) / ((l : ℝ) + 1) := by
    apply le_antisymm (maxFlow_le hl1 hD)
    rw [← hval, mul_div_cancel_left₀ _ hlpos.ne']
    exact le_maxFlow hl1 hflow
  unfold Fnum
  rw [hmax, ← gam_sub_inv (by omega)]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ForcedContentBoundsProgrammeValueGoodPrime
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ContentValue

lemma lpF_nonneg (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (hl : 2 ≤ l) (hD : ∀ a, 0 ≤ D a) : 0 ≤ lpF l d D := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hS : 0 ≤ ∑ a, D a := Finset.sum_nonneg fun a _ => hD a
  have hq : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hg : 0 ≤ (l : ℝ) / ((l : ℝ) ^ 2 - 1) * ∑ a, D a := by positivity
  unfold lpF
  rw [sub_nonneg]
  refine Real.sSup_le ?_ hg
  rintro t ⟨x, h0, h1, h2, rfl⟩
  have := (GlobalTheory.FlowProgramme.duality l d D hl x ⟨h0, fun a i h => ?_, h2⟩).1
  · have ht : 0 ≤ ∑ s, ∑ i ∈ Finset.range d, x s i :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => h0 s i
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    nlinarith [mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ l - 1 by linarith)]
  · by_contra hc
    refine h (h1 a i ?_)
    by_cases ho : Odd i
    · exact Or.inr (not_lt.1 fun hh => hc ⟨ho, hh⟩)
    · exact Or.inl ho

lemma two_le_ordP (N : NumDatum) (l : ℕ) (hc : Inert N l) (hn : ¬ PhiC N l) : 2 ≤ N.ordP l := by
  unfold NumDatum.ordP
  split
  · have := addOrderOf_pos (2 • N.hP l)
    omega
  · rename_i hs
    have h0 : N.hP l ≠ 0 := fun h => hn ⟨Or.resolve_right hc hs, h⟩
    have h1 : addOrderOf (N.hP l) ≠ 1 := fun h => h0 (AddMonoid.addOrderOf_eq_one_iff.1 h)
    have := addOrderOf_pos (N.hP l)
    omega

lemma rho_bound (k w l : ℝ) (hk : 1 ≤ k) (hw : 0 ≤ w) (hl : 2 ≤ l) :
    (k - 1) * w / (l ^ 2 - 1) ≤ 2 * (k * w / l ^ 2) := by
  have h4 : 4 ≤ l ^ 2 := by nlinarith
  rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : 0 ≤ k * w := by positivity
  nlinarith [mul_nonneg h1 (show 0 ≤ l ^ 2 - 2 by linarith), mul_nonneg hw (show 0 ≤ l ^ 2 by linarith)]

theorem main : ∀ (N : NumDatum) (j l : ℕ), l.Prime → l ∉ N.H.small → l ≠ N.q → l ≠ N.d → l ≠ N.g 0 → l ≠ N.g 1 → (∀ z, 0 ≤ N.w j z) → (∀ z z', N.w j z' ≤ N.sc.X'' N.R.n * N.w j z) →
  0 ≤ N.FjP j l ∧ (Inert N l ∨ N.cls l = PrimeClass.splitK) ∧ ParOK (parOf N j l) ∧
  (PhiC N l → ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ∧
  (Inert N l → ¬ PhiC N l → ∀ Z : Finset (RPl N.R), RF.IsReps (parOf N j l) Z →
    (∑ z ∈ Z, Fnum l (N.ordP l) fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos l z s.val)) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) := by
  classical
  intro N j l hp h2 hq hd hg0 hg1 hw hr
  have hl : 2 ≤ l := hp.two_le
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hk : (1 : ℝ) ≤ N.R.k := by
    have := N.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ N.R.k)
  have hq2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hS : 0 ≤ ∑ z, N.w j z := Finset.sum_nonneg fun z _ => hw z
  have hcls : Inert N l ∨ N.cls l = PrimeClass.splitK := by
    unfold Inert NumDatum.cls primeClass
    rw [if_neg h2, if_neg hq, if_neg hd]
    split_ifs <;> simp
  have hnd : N.cls l ≠ PrimeClass.ramD := by
    rcases hcls with (h | h) | h <;> rw [h] <;> simp
  have hF : N.FjP j l = if Inert N l ∧ (l : ℝ) ≤ N.sc.X'' N.R.n then N.FInert j l else 0 := by
    unfold NumDatum.FjP
    rw [if_neg (by tauto), if_neg hnd]
    by_cases h : Inert N l ∧ (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [if_pos h]; exact if_pos h
    · rw [if_neg h]; exact if_neg h
  have hD : ∀ z, 0 ≤ ((N.R.k : ℝ) - 1) * N.w j z := fun z => mul_nonneg (by linarith) (hw z)
  have hI : 0 ≤ N.FInert j l := by
    unfold NumDatum.FInert
    split_ifs
    · exact Finset.sum_nonneg fun z _ => div_nonneg (hD z) hq2.le
    · exact div_nonneg (Finset.sum_nonneg fun z _ => lpF_nonneg _ _ _ hl fun a => hD _) (Nat.cast_nonneg _)
  have hb := rho_bound N.R.k _ l hk hS hl'
  refine ⟨?_, hcls, ?_, ?_, ?_⟩
  · rw [hF]
    split_ifs
    · exact hI
    · exact le_rfl
  · have h3 := N.R.m_add_three_le_k
    have h4 := N.R.two_le_m
    refine ⟨?_, ?_, h3, ?_, ?_⟩
    · show Fintype.card (RPl N.R) = N.R.f
      have := Formalism.HC.Frame.card_A N.R.toFrame
      simpa [Ranks.f, Ranks.n] using this
    · show 1 ≤ N.R.m
      omega
    · show N.R.r = N.R.k - 1 + N.R.m
      unfold Ranks.r
      omega
    · show 0 ≤ N.Sc + N.eta
      unfold NumDatum.Sc NumDatum.eta
      positivity
  · intro hc
    have hi : Inert N l := Or.inl hc.1
    by_cases hX : (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [hF, if_pos ⟨hi, hX⟩, if_neg (not_lt.2 hX), add_zero]
      unfold NumDatum.FInert
      rw [if_pos (show N.cls l = PrimeClass.inertClass ∧ N.hP l = 0 from hc), ← Finset.sum_div, ← Finset.mul_sum]
    · rw [hF, if_neg (fun h => hX h.2), if_pos (not_le.1 hX), zero_add]
      exact hb
  · intro hi hc Z hZ
    have hZ' : Formalism.L2.FormalSeriesBounds.IsReps N l Z := hZ
    by_cases hX : (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [hF, if_pos ⟨hi, hX⟩, if_neg (not_lt.2 hX), add_zero]
      exact (GlobalTheory.LevelsOrbits.fInertReps N j l Z hZ' hi hc).1.ge
    · rw [hF, if_neg (fun h => hX h.2), if_pos (not_le.1 hX), zero_add]
      refine le_trans (le_of_eq ?_) hb
      have ho2 := two_le_ordP N l hi hc
      have hl3 : 3 ≤ l := by
        have := ne_two_of_not_small h2
        omega
      have hbal : ∀ z z', N.w j z' ≤ l * N.w j z := fun z z' =>
        (hr z z').trans (mul_le_mul_of_nonneg_right (not_le.1 hX).le (hw z))
      rw [GlobalTheory.LevelsOrbits.sum_reps N l Z hZ' (N.w j), Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le l (N.ordP l) hl3 ho2 _ (fun a => hD _) (fun a a' => ?_), ← Finset.mul_sum]
      · unfold Formalism.IncomingBounds.rho
        ring
      · have := mul_le_mul_of_nonneg_left (hbal (N.pos l z a.val) (N.pos l z a'.val))
          (show (0 : ℝ) ≤ N.R.k - 1 by linarith)
        linarith

end GlobalTheory.ContentValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ForcedContentBoundsProgrammeValueGoodPrimeStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forcedContent_bounds_programmeValue_goodPrime : ∀ (N : NumDatum) (j l : ℕ), l.Prime → l ∉ N.H.small → l ≠ N.q → l ≠ N.d → l ≠ N.g 0 → l ≠ N.g 1 → (∀ z, 0 ≤ N.w j z) → (∀ z z', N.w j z' ≤ N.sc.X'' N.R.n * N.w j z) →
  0 ≤ N.FjP j l ∧ (Inert N l ∨ N.cls l = PrimeClass.splitK) ∧ ParOK (parOf N j l) ∧
  (PhiC N l → ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ∧
  (Inert N l → ¬ PhiC N l → ∀ Z : Finset (RPl N.R), RF.IsReps (parOf N j l) Z →
    (∑ z ∈ Z, Fnum l (N.ordP l) fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos l z s.val)) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) := by
  first | exact @GlobalTheory.ContentValue.main | exact GlobalTheory.ContentValue.main | (intros; apply GlobalTheory.ContentValue.main <;> assumption)
end
