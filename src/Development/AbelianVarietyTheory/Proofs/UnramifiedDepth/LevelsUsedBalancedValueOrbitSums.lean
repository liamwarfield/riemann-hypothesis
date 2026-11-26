module

public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
public import Formalism.LocalRingCardinality.DataForced
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CyclicSolvable
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.FlowProgramme

lemma sum_shift (d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) (s : Finset ℕ) :
    ∑ a : ZMod d, ∑ i ∈ s, x (a - i) i = ∑ a, ∑ i ∈ s, x a i := by
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => x a i)

lemma duality (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (x : ZMod d → ℕ → ℝ)
    (hx : ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a)) :
    ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i ≤ ∑ a, X a ∧
      ∀ i₀ : ℕ, ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i ≤ ((l : ℝ) ^ i₀)⁻¹ * ∑ a, X a := by
  obtain ⟨h0, h1, h2⟩ := hx
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) ≤ l := by linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) fun a _ => h2 a
  rw [Finset.sum_add_distrib, sum_shift] at hs
  have hT : 0 ≤ ∑ a, ∑ i ∈ Finset.range d, x a i :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => h0 a i
  constructor
  · have : (l : ℝ) * ∑ a, ∑ i ∈ Finset.range d, x a i
        ≤ ∑ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h : x a i = 0
      · simp [h]
      · have hi : i ≠ 0 := by
          rintro rfl
          exact absurd (h1 a 0 h).1 (by decide)
        exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi) (h0 a i)
    linarith
  · intro i₀
    have hp : (0 : ℝ) < (l : ℝ) ^ i₀ := by positivity
    rw [le_inv_mul_iff₀ hp]
    have : (l : ℝ) ^ i₀ * ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i
        ≤ ∑ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      calc ∑ i ∈ Finset.Ico i₀ d, (l : ℝ) ^ i₀ * x a i
          ≤ ∑ i ∈ Finset.Ico i₀ d, (l : ℝ) ^ i * x a i :=
            Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 (Finset.mem_Ico.1 hi).1) (h0 a i)
        _ ≤ _ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
              mul_nonneg (by positivity) (h0 a i)
            intro i hi
            exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
    linarith

lemma cyclic_nonneg (l : ℝ) (d : ℕ) [NeZero d] (X y : ZMod d → ℝ) (hl : 2 ≤ l)
    (hX : ∀ a b, X a ≤ l * X b) (hy : ∀ a, l * y a + y (a - 1) = X a) (a : ZMod d) :
    0 ≤ y a := by
  obtain ⟨a₀, h₀⟩ := Finite.exists_min y
  obtain ⟨a₁, h₁⟩ := Finite.exists_max y
  refine le_trans ?_ (h₀ a)
  have e0 := hy a₀
  have e1 := hy a₁
  have f0 := h₁ (a₀ - 1)
  have f1 := h₀ (a₁ - 1)
  have g := hX a₁ a₀
  have k : l * y (a₀ - 1) ≤ l * y a₁ := mul_le_mul_of_nonneg_left f0 (by linarith)
  have k2 : 0 ≤ (l * l - 1) * y a₀ := by rw [← e0] at g; nlinarith
  have k3 : 0 < l * l - 1 := by nlinarith
  exact (mul_nonneg_iff_of_pos_left k3).1 k2

lemma cyclic_solvable (l : ℝ) (d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) :
    ∃ y : ZMod d → ℝ, ∀ a, l * y a + y (a - 1) = X a := by
  let T : (ZMod d → ℝ) →ₗ[ℝ] (ZMod d → ℝ) :=
    { toFun := fun y a => l * y a + y (a - 1)
      map_add' := fun y z => by ext a; simp; ring
      map_smul' := fun c y => by ext a; simp; ring }
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have hy' : ∀ a, l * y a + y (a - 1) = 0 := fun a => congrFun hy a
    ext a
    have h1 := cyclic_nonneg l d (fun _ => 0) y hl (by simp) hy' a
    have h2 := cyclic_nonneg l d (fun _ => 0) (fun a => - y a) hl (by simp)
      (fun a => by have := hy' a; linarith) a
    simp only [Pi.zero_apply]
    linarith
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.1 hinj X
  exact ⟨y, fun a => congrFun hy a⟩

lemma balanced (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (hd : 2 ≤ d)
    (hX : ∀ a b, X a ≤ l * X b) :
    ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧
      ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i = ∑ a, X a := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨y, hy⟩ := cyclic_solvable l d X hl'
  have hpos := cyclic_nonneg l d X y hl' hX hy
  have h1 : 1 ∈ Finset.range d := Finset.mem_range.2 (by omega)
  refine ⟨fun a i => if i = 1 then y a else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a i
    dsimp only
    split_ifs
    · exact hpos a
    · exact le_rfl
  · intro a i h
    dsimp only at h
    split_ifs at h with hi
    · subst hi
      exact ⟨odd_one, by omega⟩
    · exact absurd rfl h
  · intro a
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', h1, if_true, pow_one, Nat.cast_one]
    exact (hy a).le
  · simp only [Finset.sum_ite_eq', h1, if_true]
    have : ∑ a, y (a - 1) = ∑ a, y a := Equiv.sum_comp (Equiv.subRight (1 : ZMod d)) y
    rw [← Finset.sum_congr rfl fun a _ => hy a, Finset.sum_add_distrib, this, ← Finset.mul_sum]
    ring

end GlobalTheory.FlowProgramme
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
open Formalism.L2.FormalSeriesBounds Formalism.L2.DIV Formalism.BasicNotions Formalism.UnitaryBoundIntegral

namespace GlobalTheory.LevelsOrbits

lemma levels_nonempty (k l : ℕ) (hl : 2 ≤ l) :
    {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i}.Nonempty := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((k : ℝ) ^ ((3 : ℝ) / 2)) (show (1 : ℝ) < l by linarith)
  refine ⟨2 * n + 3, ⟨n + 1, by ring⟩, by omega, hn.trans_le ?_⟩
  exact pow_le_pow_right₀ (by linarith) (by omega)

theorem thlEq : ThlEq := by
  intro k l _ hl
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hm := Nat.sInf_mem (levels_nonempty k l hl)
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  unfold thl
  refine IsGreatest.csSup_eq ⟨⟨_, hm.1, hm.2.1, hm.2.2, rfl⟩, ?_⟩
  rintro t ⟨i, h1, h2, h3, rfl⟩
  have hi : i0 k l ≤ i := Nat.sInf_le ⟨h1, h2, h3⟩
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) hi)

theorem levelBound : LevelBound := by
  intro k l hk hl
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk'
  obtain ⟨⟨r, hr⟩, h3, -, -⟩ := thlEq k l hk (by omega)
  by_cases h : i0 k l = 3
  · rw [h]; push_cast; linarith
  · obtain ⟨j, hj⟩ : ∃ j, i0 k l = j + 2 := ⟨i0 k l - 2, by omega⟩
    have hn : j ∉ {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i} :=
      Nat.notMem_of_lt_sInf (show j < i0 k l by omega)
    have hle : (l : ℝ) ^ j ≤ (k : ℝ) ^ ((3 : ℝ) / 2) := by
      by_contra hc
      exact hn ⟨⟨r - 1, by omega⟩, by omega, not_le.1 hc⟩
    have h1 := Real.log_le_log (by positivity) hle
    rw [Real.log_pow, Real.log_rpow (by linarith)] at h1
    have h2 : 1 ≤ Real.log l := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have h4 : (j : ℝ) ≤ j * Real.log l := le_mul_of_one_le_right (by positivity) h2
    rw [hj]; push_cast; linarith

lemma sum_range_ite (d : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range d, (if Odd i ∧ i < d then f i else 0) = ∑ i ∈ Formalism.IncomingBounds.oddLevels d, f i := by
  unfold Formalism.IncomingBounds.oddLevels
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [Finset.mem_range.1 hi]

lemma sum_range_eq (d : ℕ) (f : ℕ → ℝ) (hf : ∀ i, ¬ Odd i → f i = 0) :
    ∑ i ∈ Finset.range d, f i = ∑ i ∈ Formalism.IncomingBounds.oddLevels d, f i := by
  unfold Formalism.IncomingBounds.oddLevels
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · exact hf i h

lemma lpFeasible_eq (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) :
    lpFeasible l d D = {t : ℝ | ∃ x, Formalism.IncomingBounds.IsFlow l d D x ∧ Formalism.IncomingBounds.flowVal d x = t} := by
  ext t
  constructor
  · rintro ⟨x, h0, h1, h2, rfl⟩
    have e : ∀ s, ∑ i ∈ Finset.range d, x s i = ∑ i ∈ Formalism.IncomingBounds.oddLevels d, x s i :=
      fun s => sum_range_eq d _ fun i hi => h1 s i (Or.inl hi)
    refine ⟨x, ⟨h0, fun s => ?_⟩, ?_⟩
    · have := h2 s
      rwa [sum_range_eq d _ fun i hi => by rw [h1 s i (Or.inl hi), mul_zero],
        sum_range_eq d (fun i => x (s - (i : ZMod d)) i) fun i hi => h1 _ i (Or.inl hi)] at this
    · simp only [Formalism.IncomingBounds.flowVal, e]
  · rintro ⟨x, ⟨h0, h2⟩, rfl⟩
    refine ⟨fun s i => if Odd i ∧ i < d then x s i else 0, ?_, ?_, ?_, ?_⟩
    · intro s i
      dsimp only
      split_ifs
      · exact h0 s i
      · exact le_rfl
    · intro s i h
      have : ¬ (Odd i ∧ i < d) := by
        rintro ⟨a, b⟩
        rcases h with h | h
        · exact h a
        · omega
      simp only [this, if_false]
    · intro s
      simp only [mul_ite, mul_zero]
      rw [sum_range_ite, sum_range_ite]
      exact h2 s
    · simp only [Formalism.IncomingBounds.flowVal, sum_range_ite]

lemma lpF_eq (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) : lpF l d D = Formalism.IncomingBounds.Fnum l d D := by
  unfold lpF Formalism.IncomingBounds.Fnum Formalism.IncomingBounds.maxFlow Formalism.IncomingBounds.gam
  rw [lpFeasible_eq]

theorem lemmaFe : LemmaFe := by
  intro l d _ hl hd _ D _ hD
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hp : (0 : ℝ) < l + 1 := by linarith
  have hg : IsGreatest (lpFeasible l d D) ((∑ a, D a) / ((l : ℝ) + 1)) := by
    constructor
    · obtain ⟨x, ⟨h0, h1, h2⟩, h3⟩ :=
        GlobalTheory.FlowProgramme.balanced l d D hl hd (fun a b => hD b a)
      refine ⟨x, h0, fun s i h => ?_, h2, ?_⟩
      · by_contra hc
        obtain ⟨a, b⟩ := h1 s i hc
        rcases h with h | h
        · exact h a
        · omega
      · rw [← h3]; field_simp
    · rintro t ⟨x, h0, h1, h2, rfl⟩
      have := (GlobalTheory.FlowProgramme.duality l d D hl x ⟨h0, fun a i h => ?_, h2⟩).1
      · rw [le_div_iff₀ hp]; linarith
      · by_contra hc
        refine h (h1 a i ?_)
        by_cases ho : Odd i
        · exact Or.inr (not_lt.1 fun hh => hc ⟨ho, hh⟩)
        · exact Or.inl ho
  rw [← lpF_eq]
  unfold lpF
  rw [hg.csSup_eq]
  have h1 : (l : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (l : ℝ) ^ 2 - 1 = (l - 1) * (l + 1) := by ring
  show _ = 1 / ((l : ℝ) ^ 2 - 1) * _
  rw [h2]
  field_simp
  ring

lemma pos_add (N : NumDatum) (l : ℕ) (z : RPl N.R) (s t : ℕ) :
    N.pos l (N.pos l z s) t = N.pos l z (s + t) := by
  unfold NumDatum.pos
  refine Prod.ext ?_ ?_
  · dsimp only
    by_cases h : N.cls l = PrimeClass.signal <;> by_cases hs : Odd s <;> by_cases ht : Odd t <;>
      simp [h, hs, ht, Nat.odd_add, ← Nat.not_odd_iff_even]
  · dsimp only
    rw [add_smul, add_assoc]

lemma pos_mul_period (N : NumDatum) (l : ℕ) (z : RPl N.R) (c : ℕ) :
    N.pos l z (N.ordP l * c) = z := by
  unfold NumDatum.pos NumDatum.ordP
  by_cases h : N.cls l = PrimeClass.signal
  · rw [if_pos h]
    refine Prod.ext ?_ ?_
    · have : ¬ Odd (2 * addOrderOf (2 • N.hP l) * c) := by
        rw [Nat.not_odd_iff_even, mul_assoc]; exact even_two_mul _
      dsimp only
      rw [decide_eq_false (fun hh => this hh.2), Bool.xor_false]
    · dsimp only
      rw [show 2 * addOrderOf (2 • N.hP l) * c = c * addOrderOf (2 • N.hP l) * 2 by ring,
        mul_smul, mul_smul, addOrderOf_nsmul_eq_zero, smul_zero, add_zero]
  · rw [if_neg h]
    refine Prod.ext ?_ ?_
    · simp [h]
    · dsimp only
      rw [mul_comm, mul_smul, addOrderOf_nsmul_eq_zero, smul_zero, add_zero]

lemma pos_mod (N : NumDatum) (l : ℕ) (z : RPl N.R) (e : ℕ) :
    N.pos l z (e % N.ordP l) = N.pos l z e := by
  conv_rhs => rw [← Nat.div_add_mod e (N.ordP l), ← pos_add, pos_mul_period]

lemma FOrb_step (N : NumDatum) (j l : ℕ) (z : RPl N.R) (c : ZMod (N.ordP l)) :
    N.FOrb j l (N.pos l z c.val) = N.FOrb j l z := by
  unfold NumDatum.FOrb
  rw [← lpF_shift l (N.ordP l) (fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos l z s.val)) c]
  congr 1
  funext s
  rw [pos_add, ZMod.val_add, pos_mod, add_comm]

lemma sum_reps (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) (hZ : IsReps N l Z)
    (f : RPl N.R → ℝ) :
    ∑ z, f z = ∑ z ∈ Z, ∑ s : ZMod (N.ordP l), f (N.pos l z s.val) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => N.pos l p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro p hp q hq h
    exact (hZ _).unique ⟨(Finset.mem_product.1 hp).1, h⟩ ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := hZ z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

theorem fInertReps : FInertReps := by
  intro N j l Z hZ hc hn
  constructor
  · unfold NumDatum.FInert
    rw [if_neg hn, sum_reps N l Z hZ]
    have hd : (N.ordP l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
    simp only [FOrb_step, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hd]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold NumDatum.FOrb alongOrb
    exact lpF_eq _ _ _
  · intro h0 h1 hX
    unfold NumDatum.FjP
    have hr : N.cls l ≠ PrimeClass.ramD := by
      rcases hc with h | h <;> rw [h] <;> simp
    rw [if_neg (by tauto), if_neg hr, if_pos ⟨hc, hX⟩]

theorem main : ThlEq ∧ LevelBound ∧ LemmaFe ∧ FInertReps :=
  ⟨thlEq, levelBound, lemmaFe, fInertReps⟩

end GlobalTheory.LevelsOrbits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSumsStatement
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelsUsed_balancedValue_orbitSums : ThlEq ∧ LevelBound ∧ LemmaFe ∧ FInertReps := by
  first | exact @GlobalTheory.LevelsOrbits.main | exact GlobalTheory.LevelsOrbits.main | (intros; apply GlobalTheory.LevelsOrbits.main <;> assumption)
end
