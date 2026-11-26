module

public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.LocalRingCardinality.DataParams

@[expose] public section

section -- merged from Formalism.LocalRingCardinality.DataForced
noncomputable section

namespace Formalism.BasicNotions

open Formalism.FrobeniusOrbits Formalism.MainNotions.G
open scoped BigOperators

theorem plGG_mem_Psi (D : D7) (z : Bool × HH D) : plGG D z ∈ D.R.Psi := by
  unfold plGG
  split <;> exact (Formalism.HC.Frame.mem_Psi_iff _).2 rfl

def tauPl (D : D7) (z : Bool × HH D) : D.what₂.Tau := D.eTau.symm ⟨plGG D z, plGG_mem_Psi D z⟩

def wPl (D : D7) (j : ℕ) (z : Bool × HH D) : ℝ := wj D j (tauPl D z)

def posPl (D : D7) (p : ℕ) (z : Bool × HH D) (e : ℕ) : Bool × HH D :=
  (xor z.1 (partner D p z.2 e).1, (partner D p z.2 e).2)

theorem positionPlace_conjugate_partner (D : D7) (p : ℕ) (t : HH D) (e : ℕ) : posPl D p (false, t) e = partner D p t e := by
  simp [posPl]

theorem posPl_zero (D : D7) (p : ℕ) (z : Bool × HH D) : posPl D p z 0 = z := by
  simp [posPl, partner]

theorem posPl_add (D : D7) (p : ℕ) (z : Bool × HH D) (a b : ℕ) :
    posPl D p (posPl D p z a) b = posPl D p z (a + b) := by
  unfold posPl partner
  refine Prod.ext ?_ ?_
  · show xor (xor z.1 (decide (IsSg D p ∧ Odd a))) (decide (IsSg D p ∧ Odd b)) =
      xor z.1 (decide (IsSg D p ∧ Odd (a + b)))
    rw [Bool.xor_assoc]
    congr 1
    by_cases hs : IsSg D p
    · have h : ∀ e : ℕ, decide (IsSg D p ∧ Odd e) = decide (Odd e) :=
        fun e => decide_eq_decide.2 ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
      simp only [h]
      by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [ha, hb, Nat.odd_add, ← Nat.not_odd_iff_even]
    · have h : ∀ e : ℕ, decide (IsSg D p ∧ Odd e) = false := fun e => decide_eq_false (fun h => hs h.1)
      simp only [h, Bool.xor_false]
  · show z.2 + a • hP D p + b • hP D p = z.2 + (a + b) • hP D p
    rw [add_smul, add_assoc]

instance nP_neZero (D : D7) (p : ℕ) : NeZero (nP D p) := by
  refine ⟨?_⟩
  unfold nP
  split
  · exact (Nat.mul_pos two_pos (addOrderOf_pos _)).ne'
  · exact (addOrderOf_pos _).ne'

theorem posPl_period (D : D7) (p : ℕ) (z : Bool × HH D) : posPl D p z (nP D p) = z := by
  have key : ¬ (IsSg D p ∧ Odd (nP D p)) ∧ nP D p • hP D p = 0 := by
    by_cases hs : IsSg D p
    · have hn : nP D p = 2 * addOrderOf (2 • hP D p) := if_pos hs
      rw [hn]
      refine ⟨fun h => (Nat.not_odd_iff_even.2 (even_two_mul _)) h.2, ?_⟩
      rw [mul_comm, mul_smul]
      exact addOrderOf_nsmul_eq_zero _
    · have hn : nP D p = addOrderOf (hP D p) := if_neg hs
      rw [hn]
      exact ⟨fun h => hs h.1, addOrderOf_nsmul_eq_zero _⟩
  refine Prod.ext ?_ ?_
  · show xor z.1 (decide (IsSg D p ∧ Odd (nP D p))) = z.1
    rw [decide_eq_false key.1, Bool.xor_false]
  · show z.2 + nP D p • hP D p = z.2
    rw [key.2, add_zero]

theorem posPl_mul_period (D : D7) (p : ℕ) (z : Bool × HH D) (c : ℕ) : posPl D p z (nP D p * c) = z := by
  induction c with
  | zero => simpa using posPl_zero D p z
  | succ c ih => rw [Nat.mul_succ, ← posPl_add, ih, posPl_period]

theorem posPl_mod (D : D7) (p : ℕ) (z : Bool × HH D) (e : ℕ) : posPl D p z (e % nP D p) = posPl D p z e := by
  conv_rhs => rw [← Nat.div_add_mod e (nP D p), ← posPl_add, posPl_mul_period]

theorem lpFeasible_shift_sub (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (c : ZMod d) :
    lpFeasible l d (fun s => Ds (s + c)) ⊆ lpFeasible l d Ds := by
  rintro y ⟨xs, h0, hs, hc, rfl⟩
  refine ⟨fun s i => xs (s - c) i, fun s i => h0 _ _, fun s i h => hs _ _ h, fun s => ?_, ?_⟩
  · have h := hc (s - c)
    have e : ∀ i : ℕ, s - (i : ZMod d) - c = s - c - (i : ZMod d) := fun i => sub_right_comm _ _ _
    simp only [sub_add_cancel] at h
    simp only [e]
    exact h
  · exact (Equiv.sum_comp (Equiv.subRight c) (fun s => ∑ i ∈ Finset.range d, xs s i)).symm

theorem lpF_shift (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (c : ZMod d) :
    lpF l d (fun s => Ds (s + c)) = lpF l d Ds := by
  have hset : lpFeasible l d (fun s => Ds (s + c)) = lpFeasible l d Ds := by
    refine Set.Subset.antisymm (lpFeasible_shift_sub l d Ds c) ?_
    have h := lpFeasible_shift_sub l d (fun s => Ds (s + c)) (-c)
    simpa using h
  have hsum : ∑ s, Ds (s + c) = ∑ s, Ds s := Equiv.sum_comp (Equiv.addRight c) Ds
  unfold lpF
  rw [hset, hsum]

def FOrb (D : D7) (j p : ℕ) (z : Bool × HH D) : ℝ :=
  lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val))

theorem FOrb_step (D : D7) (j p : ℕ) (z : Bool × HH D) (e : ℕ) : FOrb D j p (posPl D p z e) = FOrb D j p z := by
  unfold FOrb
  rw [← lpF_shift p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val)) (e : ZMod (nP D p))]
  congr 1
  funext s
  rw [posPl_add, ZMod.val_add, ZMod.val_natCast, posPl_mod, ← posPl_add D p z s.val, posPl_mod, posPl_add,
    add_comm]


open Classical in
def FInert (D : D7) (j p : ℕ) : ℝ :=
  if IsResidueClassZero D p ∧ hP D p = 0 then ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ / ((p : ℝ) ^ 2 - 1)
  else (∑ z : Bool × HH D, FOrb D j p z) / (nP D p : ℝ)

def FRamD (D : D7) (j : ℕ) : ℝ :=
  -(((D.R.k : ℝ) - 1) / 2) * ∑ t : HH D, min (wPl D j (false, t)) (wPl D j (true, t))

def fockDeg (D : D7) (j : ℕ) : ℤ :=
  ∑ τ : D.what₂.Tau, ((∑ a, |D.what₂.kaBig j τ a|) + ∑ a, |D.what₂.kaSmall j τ a|)

def FTypeG (D : D7) (j : ℕ) : ℝ := -((fockDeg D j : ℝ)) / 2


open Classical in
def FvalP {D : D7} (L : SizeData₂ D) (j p : ℕ) : ℝ :=
  if p ∈ L.gTypes then FTypeG D j
  else if D.host.cls p = PrimeClass.ramD then FRamD D j
  else if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then FInert D j p
  else 0

def Fval {D : D7} (L : SizeData₂ D) (j : ℕ) (w : D.what₂.places.Pl) : ℝ := FvalP L j (D.what₂.places.resChar w)

def SizeData₂.FDef {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, L.F j w = Fval L j w

theorem posPl_fix (D : D7) (p : ℕ) (y : Bool × HH D) (c : ℕ) (h : posPl D p y c = y) : nP D p ∣ c := by
  have h1 : xor y.1 (decide (IsSg D p ∧ Odd c)) = y.1 := congrArg Prod.fst h
  have h2 : y.2 + c • hP D p = y.2 := congrArg Prod.snd h
  have h2' : c • hP D p = 0 := by simpa using h2
  have h1' : ¬ (IsSg D p ∧ Odd c) := by
    intro hc
    rw [decide_eq_true hc] at h1
    cases hy : y.1 <;> simp [hy] at h1
  by_cases hs : IsSg D p
  · have hn : nP D p = 2 * addOrderOf (2 • hP D p) := if_pos hs
    have hev : Even c := Nat.not_odd_iff_even.1 (fun ho => h1' ⟨hs, ho⟩)
    obtain ⟨a, rfl⟩ := hev
    have h3 : a • (2 • hP D p) = 0 := by
      rw [← mul_smul, mul_two]; exact h2'
    rw [hn, ← two_mul]
    exact Nat.mul_dvd_mul_left 2 (addOrderOf_dvd_of_nsmul_eq_zero h3)
  · have hn : nP D p = addOrderOf (hP D p) := if_neg hs
    rw [hn]
    exact addOrderOf_dvd_of_nsmul_eq_zero h2'

theorem posPl_inj (D : D7) (p : ℕ) (z : Bool × HH D) (a b : ℕ) (ha : a < nP D p) (hb : b < nP D p)
    (h : posPl D p z a = posPl D p z b) : a = b := by
  have key : ∀ a b : ℕ, a ≤ b → b < nP D p → posPl D p z a = posPl D p z b → a = b := by
    intro a b hab hb h
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [← posPl_add] at h
    have hd := posPl_fix D p _ c h.symm
    have hc : c = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  rcases le_total a b with hab | hab
  · exact key a b hab hb h
  · exact (key b a hab ha h.symm).symm

theorem sum_orbits (D : D7) (j p : ℕ) (T : Finset (Bool × HH D))
    (hT : ∀ z, ∃! r, r ∈ T ∧ ∃ e : ℕ, posPl D p r e = z) :
    (∑ z : Bool × HH D, FOrb D j p z) / (nP D p : ℝ) = ∑ r ∈ T, FOrb D j p r := by
  have hn : (nP D p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
  have hpos : 0 < nP D p := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 : ∑ x ∈ T ×ˢ Finset.range (nP D p), FOrb D j p (posPl D p x.1 x.2) =
      ∑ z : Bool × HH D, FOrb D j p z := by
    refine Finset.sum_bij (fun x _ => posPl D p x.1 x.2) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨r, a⟩ hx ⟨r', b⟩ hx' h
      rw [Finset.mem_product, Finset.mem_range] at hx hx'
      have hr : r = r' := (hT (posPl D p r a)).unique ⟨hx.1, a, rfl⟩ ⟨hx'.1, b, h.symm⟩
      subst hr
      rw [posPl_inj D p r a b hx.2 hx'.2 h]
    · intro z _
      obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hT z
      exact ⟨(r, e % nP D p), Finset.mem_product.2 ⟨hr, Finset.mem_range.2 (Nat.mod_lt _ hpos)⟩,
        by rw [posPl_mod, he]⟩
  rw [← h1, Finset.sum_product]
  simp only [FOrb_step, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hn]

theorem cls_ramD {D : D7} {p : ℕ} (h : D.host.cls p = PrimeClass.ramD) : p = D.host.d := by
  unfold Host.cls primeClass at h
  split_ifs at h <;> simp_all

section Cases

variable {D : D7} (L : SizeData₂ D) (j : ℕ) {p : ℕ}

theorem FvalP_above (hX : L.sc.X'' D.R.n < (p : ℝ)) (hg : p ∉ L.gTypes) (hd : p ≠ D.host.d) : FvalP L j p = 0 := by
  unfold FvalP
  rw [if_neg hg, if_neg (fun h => hd (cls_ramD h)), if_neg (fun h => absurd h.2 (not_le.2 hX))]

end Cases

theorem addVal_natCast_nonneg {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact le_trans (le_min ih (by rw [v.map_one])) (v.map_add _ _)

theorem resChar_conj (D : D7) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar (D.what₂.places.conj w) = D.what₂.places.resChar w := by
  by_contra hne
  set v := D.what₂.places.val (D.what₂.places.conj w) with hv
  set q := D.what₂.places.resChar (D.what₂.places.conj w) with hq
  set p := D.what₂.places.resChar w with hp
  have hqpr : q.Prime := D.what₂.places.resChar_prime _
  have hppr : p.Prime := D.what₂.places.resChar_prime _
  have hvq : 0 < v (q : D.what₂.LL) := by
    rw [hv, hq, D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos _
  have hvp : 0 < v (p : D.what₂.LL) := by
    rw [hv, D.conj_val, star_natCast, hp, D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos _
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime ((Nat.coprime_primes hppr hqpr).2 (fun h => hne h.symm)) hqpr.one_lt
  have h1 : ((p * c : ℕ) : D.what₂.LL) - ((q * (p * c / q) : ℕ) : D.what₂.LL) = 1 := by
    have := Nat.div_add_mod (p * c) q
    rw [hc] at this
    rw [sub_eq_iff_eq_add, add_comm]
    exact_mod_cast this.symm
  have h2 : 0 < v ((p * c : ℕ) : D.what₂.LL) := by
    rw [Nat.cast_mul, v.map_mul]
    exact add_pos_of_pos_of_nonneg hvp (addVal_natCast_nonneg v c)
  have h3 : 0 < v ((q * (p * c / q) : ℕ) : D.what₂.LL) := by
    rw [Nat.cast_mul, v.map_mul]
    exact add_pos_of_pos_of_nonneg hvq (addVal_natCast_nonneg v _)
  have h4 := v.map_sub ((p * c : ℕ) : D.what₂.LL) ((q * (p * c / q) : ℕ) : D.what₂.LL)
  rw [h1, v.map_one] at h4
  exact absurd (lt_of_lt_of_le (lt_min h2 h3) h4) (lt_irrefl _)

theorem Fval_conj {D : D7} (L : SizeData₂ D) (j : ℕ) (w : D.what₂.places.Pl) :
    Fval L j (D.what₂.places.conj w) = Fval L j w := by
  unfold Fval
  rw [resChar_conj]

def FInertGe (D : D7) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ p : ℕ, p.Prime → (IsResidueClassZero D p ∨ IsSg D p) → (∀ τ : D.what₂.Tau, 0 ≤ wj D j τ) →
    ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ / ((p : ℝ) ^ 2 - 1) ≤ FInert D j p

end Formalism.BasicNotions

end
end

section -- merged from Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
open Formalism.MainNotions.G Formalism.FrobeniusOrbits

noncomputable section

namespace Formalism.BasicNotions

namespace Scale

variable (s : Scale)

theorem x_pos : 0 < s.x := lt_trans one_pos s.one_lt_alt

theorem a_pos : 0 < s.a := mul_pos s.x_pos (Real.exp_pos _)

theorem one_le_X' : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg s.x_pos.le _)

theorem b'_pos : 0 < s.b' := div_pos s.a_pos (lt_of_lt_of_le one_pos s.one_le_X')

theorem b'_le_a : s.b' ≤ s.a := div_le_self s.a_pos.le s.one_le_X'

theorem w''_le_b' (n : ℕ) (hn : 1 ≤ n) : s.w'' n ≤ s.b' := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (1 : ℝ) ≤ s.x * n := by nlinarith [s.one_lt_alt]
  exact div_le_self s.b'_pos.le h2

theorem w''_le_a (n : ℕ) (hn : 1 ≤ n) : s.w'' n ≤ s.a := (s.w''_le_b' n hn).trans s.b'_le_a

end Scale

theorem Ranks.one_le_n (R : Ranks) : 1 ≤ R.n := R.ord_pos

theorem Ranks.five_le_k (R : Ranks) : 5 ≤ R.k := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  omega

namespace ParameterChoice'

variable {D : D7} {L : SizeData₂ D}

theorem five_le_k (_P : ParameterChoice' D L) : (5 : ℝ) ≤ D.R.k := by exact_mod_cast D.R.five_le_k

theorem LaG_pos (P : ParameterChoice' D L) : 0 < L.LaG := by
  have hk : (0 : ℝ) < D.R.k := by linarith [P.five_le_k]
  have h1 : 0 < L.LaG * L.sc.b' / D.R.k := by linarith [P.S_le, L.Sc_pos]
  have h2 : 0 < L.LaG * L.sc.b' := by
    have := mul_pos h1 hk
    rwa [div_mul_cancel₀ _ hk.ne'] at this
  exact (pos_iff_pos_of_mul_pos h2).mpr L.sc.b'_pos

theorem Sc_ge (P : ParameterChoice' D L) : 4096 * (D.R.k : ℝ) ^ 2 ≤ L.Sc := by
  have hk := P.five_le_k
  have hD := P.Del_ge.2.2.2
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hm10 : (1024 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := by
    calc (1024 : ℝ) = 2 ^ 10 := by norm_num
      _ ≤ (D.R.m : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hm 10
  have hN : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have h1 : (D.R.k : ℝ) * 1024 ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 :=
    mul_le_mul hN hm10 (by norm_num) (by linarith)
  rw [L.Sc_eq]
  nlinarith

theorem kSc_le_a (P : ParameterChoice' D L) : (D.R.k : ℝ) * L.Sc ≤ L.sc.a :=
  P.kS_le.trans (L.sc.w''_le_a _ D.R.one_le_n)

theorem Sc_le (P : ParameterChoice' D L) : 5 * L.Sc ≤ L.sc.a := by
  have := P.kSc_le_a
  nlinarith [P.five_le_k, L.Sc_pos]

theorem k_le_a (P : ParameterChoice' D L) : (D.R.k : ℝ) ≤ L.sc.a := by
  have h1 := P.kSc_le_a
  have h2 := P.Sc_ge
  have h3 := P.five_le_k
  nlinarith

theorem four_le_a (P : ParameterChoice' D L) : 4 ≤ L.sc.a := by linarith [P.k_le_a, P.five_le_k]

theorem bT_le' (P : ParameterChoice' D L) (t : D.host.TT) : (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  have hk : (0 : ℝ) < D.R.k := by linarith [P.five_le_k]
  have hx := L.sc.one_lt_alt
  have hlog : 0 < Real.log L.sc.x := Real.log_pos hx
  have h2 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg P.Crho_pos.le hlog.le) P.LaG_pos.le) hk.le
  have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  have h4 := P.rho_le
  unfold LevelStarExponents.rhoP at h4
  have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
      4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h7 := P.bT_le t
  rw [h6] at h7
  nlinarith [L.sc.b'_pos]

end ParameterChoice'

theorem SizeData₂.aT_le' {D : D7} (L : SizeData₂ D) (t : D.host.TT) : (L.aT t : ℝ) ≤ 6 / 5 * L.sc.a := by
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast D.R.five_le_k
  have hx : (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
  have h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by nlinarith
  have h1 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 :=
    div_le_div_of_nonneg_left L.sc.a_pos.le (by norm_num) h5
  linarith [(L.aT_win t).2]

section Spread

variable {D : D7}

def lamFst (D : D7) : Fin (D.R.N 0) := ⟨0, by have := D.R.five_le_k; simp only [Ranks.N]; omega⟩

def lamLst (D : D7) : Fin (D.R.N 0) := ⟨D.R.k - 1, by have := D.R.five_le_k; simp only [Ranks.N]; omega⟩

theorem columnWeight_spread_eq (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ((((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) : ℤ) : ℝ) =
      (((D.hc τ).u ⟨0, by have := D.R.five_le_k; omega⟩ : ℚ) : ℝ) -
        (((D.hc τ).u ⟨D.R.k - 1, by have := D.R.five_le_k; omega⟩ : ℚ) : ℝ) - ((D.R.k : ℝ) - 1) := by
  have hk := D.R.five_le_k
  have h0 := (D.fm u).lam_eq 0 (Nat.zero_le _) τ (lamFst D)
  have h1 := (D.fm u).lam_eq 0 (Nat.zero_le _) τ (lamLst D)
  have c0 : (lamFst D).1 < D.R.k := by simp only [lamFst]; omega
  have c1 : (lamLst D).1 < D.R.k := by simp only [lamLst]; omega
  rw [dite_eq_left c0] at h0
  rw [dite_eq_left c1] at h1
  simp only [hcToWeightQ, rhoVec, lamFst, lamLst] at h0 h1
  rw [D.hcW_first u τ (by omega)] at h0
  rw [D.hcW_last u τ (by omega)] at h1
  have hc : ((D.R.k - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hc] at h1
  have hq : ((((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) : ℤ) : ℚ) =
      (D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).u ⟨D.R.k - 1, by omega⟩ - ((D.R.k : ℚ) - 1) := by
    push_cast
    simp only [lamFst, lamLst]
    rw [h0, h1]
    push_cast
    ring
  have := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at this ⊢
  linarith

variable {L : SizeData₂ D}

theorem columnWeight_spread_at_top (L : SizeData₂ D) (u : D.what₂.Word) (τ : D.what₂.Tau) (t : D.host.TT)
    (ht : (D.eTau τ : D.R.GG) = D.R.tau1 t) :
    ((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) = L.aT t + L.bT t := by
  have h := columnWeight_spread_eq u τ
  obtain ⟨h1, h2⟩ := L.top_u τ t (by have := D.R.five_le_k; omega) ht
  rw [h1, h2] at h
  have : ((((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) : ℤ) : ℝ) = ((L.aT t + L.bT t : ℤ) : ℝ) := by
    rw [h]; push_cast; ring
  exact_mod_cast this

theorem columnWeight_spread_off_top (P : ParameterChoice' D L) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (ht : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces) :
    ((((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) : ℤ) : ℝ) ≤ 3 * L.Sc := by
  have hk := D.R.five_le_k
  have hkR := P.five_le_k
  rw [columnWeight_spread_eq u τ]
  have h1 := P.cloud_place_bound τ (by omega) ht
  have h2 := P.uk_extreme τ (by omega) ht
  have h3 := (L.cloud_v τ ⟨0, by omega⟩).2
  have h4 := (L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
  rw [h2]
  push_cast at h1 ⊢
  linarith

theorem columnWeight_spread_le (P : ParameterChoice' D L) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ((((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) : ℤ) : ℝ) ≤ 3 * L.sc.a := by
  by_cases ht : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, htT, hte⟩ := Finset.mem_image.mp ht
    rw [columnWeight_spread_at_top L u τ ⟨t, htT⟩ hte.symm]
    have h1 := L.aT_le' ⟨t, htT⟩
    have h2 := P.bT_le' ⟨t, htT⟩
    have h3 := L.sc.b'_le_a
    push_cast
    linarith [L.sc.a_pos]
  · have h1 := columnWeight_spread_off_top P u τ ht
    have h2 := P.Sc_le
    linarith [L.Sc_pos]

theorem gat_ell_le (P : ParameterChoice' D L) (T : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w h).P.nV)
    (s : Fin ((D.gat u w h).P.n' v)) :
    (((D.gat u w h).P.lam0 v s 0 - (D.gat u w h).P.lam0 v s (Fin.last _) : ℤ) : ℝ) ≤ 3 * L.sc.a := by
  have hk := T.gat_k u w h
  rw [T.gat_lam u w h v s 0, T.gat_lam u w h v s (Fin.last _)]
  have e0 : (⟨(0 : Fin ((D.gat u w h).P.m + 1)).1, by
      have h1 := T.gat_k u w h; simp only [Ranks.N]; simp; omega⟩ : Fin (D.R.N 0)) = lamFst D := rfl
  have e1 : (⟨(Fin.last (D.gat u w h).P.m).1, by
      have h1 := T.gat_k u w h; simp only [Ranks.N]; simp; omega⟩ : Fin (D.R.N 0)) = lamLst D := by
    apply Fin.ext
    simp only [lamLst, Fin.val_last]
    omega
  rw [e0, e1]
  exact columnWeight_spread_le P u _

theorem gat_ellWt_le (P : ParameterChoice' D L) (T : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w h).P.nV)
    (s : Fin ((D.gat u w h).P.n' v)) :
    (ellWt ((D.gat u w h).P.lam0 v s) : ℝ) ≤ 3 * L.sc.a := by
  have h1 := gat_ell_le P T u w h v s
  have h2 : 0 ≤ (D.gat u w h).P.lam0 v s 0 - (D.gat u w h).P.lam0 v s (Fin.last _) := by
    have := (D.gat u w h).P.dom v s (Fin.zero_le (Fin.last _))
    omega
  have h3 : lastIdx ((D.gat u w h).P.m + 1) = Fin.last _ := rfl
  unfold ellWt
  rw [h3]
  have h4 : ((((D.gat u w h).P.lam0 v s 0 - (D.gat u w h).P.lam0 v s (Fin.last _)).toNat : ℕ) : ℝ) =
      (((D.gat u w h).P.lam0 v s 0 - (D.gat u w h).P.lam0 v s (Fin.last _) : ℤ) : ℝ) := by
    have := Int.toNat_of_nonneg h2
    exact_mod_cast this
  rw [h4]
  exact h1

theorem ellWt_lamAt {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    ellWt (lamAt lam0 s) = ellWt (lam0 s) := by
  have h3 : lastIdx (m + 1) = Fin.last _ := rfl
  unfold ellWt lamAt
  rw [h3]
  split_ifs
  · rfl
  · simp only [Fin.rev_zero, Fin.rev_last]
    congr 1
    ring

theorem gat_ellWt_lamAt_le (P : ParameterChoice' D L) (T : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w h).P.nV)
    (s : Fin ((D.gat u w h).P.n' v)) :
    (ellWt (lamAt ((D.gat u w h).P.lam0 v) s) : ℝ) ≤ 3 * L.sc.a := by
  rw [ellWt_lamAt]
  exact gat_ellWt_le P T u w h v s

end Spread

end Formalism.BasicNotions

end
end
