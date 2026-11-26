module

public import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian
public import Formalism.LocalToGlobal.CharacterGerms.FirstVanishingAt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.TripleMultiplicationConstantCoeff
section -- merged from Formalism.LocalToGlobal.CharacterGerms.IndexRaiseFirst
section -- merged from Formalism.LocalToGlobal.CharacterGerms.ConstantZeroRestrictPoints
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def up (m : ℕ) : Fin m × Fin dd → Fin (m + 1) × Fin dd := fun p => (p.1.succ, p.2)

theorem up_inj (m : ℕ) : Function.Injective (up (dd := dd) m) := by
  intro a b h
  simp only [up, Prod.mk.injEq, Fin.succ_inj] at h
  exact Prod.ext h.1 h.2

def rz (m : ℕ) : Fin (m + 1) → Pt C m dd := Fin.cons 0 (fun k => pt C dd k)

theorem constant_zero_restrict_points (m : ℕ) : Z0 (rz (C := C) (dd := dd) m) := by
  intro k i
  refine Fin.cases ?_ (fun k => ?_) k
  · show MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin m × Fin dd) C) = 0
    simp
  · exact MvPowerSeries.constantCoeff_X (R := C) (k, i)

theorem rz_zero (m : ℕ) (i : Fin dd) : rz (C := C) (dd := dd) m 0 i = 0 := rfl

theorem up_ne_zero (m : ℕ) (i : Fin dd) : ((0 : Fin (m + 1)), i) ∉ Set.range (up (dd := dd) m) := by
  rintro ⟨p, hp⟩
  exact Fin.succ_ne_zero _ (congrArg Prod.fst hp)

theorem coeff_rz (m : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) f) = coeff (ν.mapDomain (up m)) f := by
  unfold ev
  rw [coeff_subst (hasSubst_ev (constant_zero_restrict_points m)), finsum_eq_single _ (ν.mapDomain (up m))]
  · rw [Finsupp.prod_mapDomain_index_inj (up_inj m)]
    have e : (ν.prod fun t e => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ e) =
        monomial ν (1 : C) := by
      have h1 := monomial_eq (R := C) ν (fun _ => (1 : C))
      simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
      rw [Finsupp.prod, h1]
      rfl
    rw [e, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    by_cases hx : ∃ j, d ((0 : Fin (m + 1)), j) ≠ 0
    · obtain ⟨j, hj⟩ := hx
      rw [Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (m + 1)), j)) (Finsupp.mem_support_iff.2 hj)
        (by show (rz (C := C) (dd := dd) m 0 j) ^ _ = 0; rw [rz_zero]; exact zero_pow hj),
        map_zero, smul_zero]
    · push_neg at hx
      have hsub : ↑d.support ⊆ Set.range (up (dd := dd) m) := by
        intro s hs
        obtain ⟨s1, s2⟩ := s
        have hs1 : s1 ≠ 0 := by
          rintro rfl
          exact (Finsupp.mem_support_iff.1 hs) (hx s2)
        exact ⟨(s1.pred hs1, s2), by simp [up, Fin.succ_pred]⟩
      set e := Finsupp.comapDomain (up m) d ((up_inj m).injOn) with he
      have hde : e.mapDomain (up m) = d := Finsupp.mapDomain_comapDomain _ (up_inj m) d hsub
      have hne : e ≠ ν := by
        intro h; apply hd; rw [← hde, h]
      rw [← hde, Finsupp.prod_mapDomain_index_inj (up_inj m)]
      have e2 : (e.prod fun t k => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ k) =
          monomial e (1 : C) := by
        have h1 := monomial_eq (R := C) e (fun _ => (1 : C))
        simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
        rw [Finsupp.prod, h1]
        rfl
      rw [e2, coeff_monomial, if_neg (Ne.symm hne), smul_zero]

theorem coeff_iter_pderiv {σ : Type} (q : σ) (L : ℕ) (f : MvPowerSeries σ C) (n : σ →₀ ℕ) :
    coeff n ((pderiv (R := C) q)^[L] f) =
      coeff (n + L • Finsupp.single q 1) f * ∏ r ∈ Finset.range L, ((n q : C) + r + 1) := by
  induction L generalizing f with
  | zero => simp
  | succ L ih =>
    have h1 : n + (L + 1) • Finsupp.single q 1 = n + L • Finsupp.single q 1 + Finsupp.single q 1 := by
      rw [add_smul, one_smul, add_assoc]
    rw [Function.iterate_succ_apply, ih, coeff_pderiv, Finset.prod_range_succ, h1]
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    ring

theorem coeff_rz_iter (m : ℕ) (i : Fin dd) (L : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) ((pderiv (R := C) ((0 : Fin (m + 1)), i))^[L] f)) =
      (L.factorial : C) * coeff (Finsupp.single ((0 : Fin (m + 1)), i) L + ν.mapDomain (up m)) f := by
  rw [coeff_rz, coeff_iter_pderiv, Finsupp.mapDomain_notin_range _ _ (up_ne_zero m i)]
  simp only [Nat.cast_zero, zero_add]
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, Finsupp.smul_single_one,
    add_comm (Finsupp.mapDomain (up m) ν)]
  push_cast
  ring

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C}

def ix (i : Fin dd) (L : ℕ) (γ : Fin 2 × Fin dd →₀ ℕ) : Fin 3 × Fin dd →₀ ℕ :=
  Finsupp.single ((0 : Fin 3), i) L + γ.mapDomain (up 2)

theorem index_raise_first (i : Fin dd) (L : ℕ) (γ : Fin 2 × Fin dd →₀ ℕ) (j : Fin dd) :
    ix i L γ ((0 : Fin 3), j) = if j = i then L else 0 := by
  have hn : ((0 : Fin 3), j) ∉ Set.range (up (dd := dd) 2) := by
    rintro ⟨q, hq⟩
    simp only [up, Prod.mk.injEq] at hq
    exact Fin.succ_ne_zero _ hq.1
  simp only [ix, Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ hn, add_zero, Finsupp.single_apply,
    Prod.mk.injEq, true_and]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

def FrobX (V : VF C) (f : PS C 3 dd) : Prop :=
  ∀ p : Fin 3 × Fin dd →₀ ℕ, (∃ j, ¬ V.l ∣ p ((0 : Fin 3), j)) → V.MM (coeff p f)

def FrobD (V : VF C) (f : PS C 3 dd) : Prop := ∀ j : Fin dd, MaximalIdealCongruence.MMS V (MvPowerSeries.pderiv ((0 : Fin 3), j) f)

private theorem v_natCast_nonneg_of_vf (V : VF C) (m : ℕ) : 0 ≤ V.v (m : C) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ m ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (AddValuation.map_add _ _ _)
    rw [AddValuation.map_one]

private theorem v_intCast_nonneg' (V : VF C) (a : ℤ) : 0 ≤ V.v (a : C) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · rw [Int.cast_natCast]
    exact v_natCast_nonneg_of_vf V m
  · rw [Int.cast_neg, Int.cast_natCast, AddValuation.map_neg]
    exact v_natCast_nonneg_of_vf V m

private theorem v_natCast_nonpos_of_not_dvd (V : VF C) (n : ℕ) (hn : ¬ V.l ∣ n) : V.v (n : C) ≤ 0 := by
  by_contra hlt
  push_neg at hlt
  have hcop : Nat.Coprime n V.l :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd V.l_prime).mpr hn)
  have hb := Nat.gcd_eq_gcd_ab n V.l
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have h1 : (1 : C) = (n : C) * (Nat.gcdA n V.l : C) + (V.l : C) * (Nat.gcdB n V.l : C) := by
    have := congrArg (fun z : ℤ => (z : C)) hb
    exact_mod_cast this
  have h01 : (0 : WithTop ℝ) < 1 := by
    rw [← WithTop.coe_zero, ← WithTop.coe_one, WithTop.coe_lt_coe]
    exact one_pos
  have ha : 0 < V.v ((n : C) * (Nat.gcdA n V.l : C)) := by
    rw [AddValuation.map_mul]
    exact add_pos_of_pos_of_nonneg hlt (v_intCast_nonneg' V _)
  have hb' : 0 < V.v ((V.l : C) * (Nat.gcdB n V.l : C)) := by
    rw [AddValuation.map_mul, V.v_l]
    exact add_pos_of_pos_of_nonneg h01 (v_intCast_nonneg' V _)
  have := lt_of_lt_of_le (lt_min ha hb') (AddValuation.map_add _ _ _)
  rw [← h1, AddValuation.map_one] at this
  exact lt_irrefl _ this

theorem frobX_of {f : PS C 3 dd} (hi : IntS V f) (hd : FrobD V f) : FrobX V f := by
  unfold FrobD MaximalIdealCongruence.MMS at hd
  rintro p ⟨j, hj⟩
  have hp0 : p ((0 : Fin 3), j) ≠ 0 := by
    intro h
    rw [h] at hj
    exact hj (dvd_zero _)
  have h := hd j (p - Finsupp.single ((0 : Fin 3), j) 1)
  have hle : Finsupp.single ((0 : Fin 3), j) 1 ≤ p := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hp0
  rw [MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle] at h
  have hn : ((((p - Finsupp.single ((0 : Fin 3), j) 1 : Fin 3 × Fin dd →₀ ℕ) ((0 : Fin 3), j)) : ℕ) : C) + 1 =
      (p ((0 : Fin 3), j) : C) := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp0)
  rw [hn] at h
  unfold VF.MM at h ⊢
  rw [AddValuation.map_mul] at h
  by_contra hc
  push_neg at hc
  have := add_le_add hc (v_natCast_nonpos_of_not_dvd V _ hj)
  rw [add_zero] at this
  exact absurd h (not_lt.mpr this)

private theorem mm_add_of_mm_of_mm {V : VF C} {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)

private theorem mm_finset_sum_of_forall_mm {V : VF C} {ι : Type} (s : Finset ι) (a : ι → C) (h : ∀ i ∈ s, V.MM (a i)) :
    V.MM (∑ i ∈ s, a i) := by
  refine Finset.sum_induction a (fun x => V.MM x) (fun x y hx hy => mm_add_of_mm_of_mm hx hy) ?_ h
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

private theorem mms_mul_of_intS_of_mms {V : VF C} {σ : Type} {f h : MvPowerSeries σ C} (hf : IntS V f)
    (hh : MaximalIdealCongruence.MMS V h) : MaximalIdealCongruence.MMS V (f * h) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  apply mm_finset_sum_of_forall_mm
  intro x _
  have h1 := hf x.1
  have h2 := hh x.2
  unfold VF.Ge at h1
  unfold VF.MM at h2 ⊢
  rw [AddValuation.map_mul]
  have h1' : (0 : WithTop ℝ) ≤ V.v (coeff x.1 f) := by simpa using h1
  exact lt_of_lt_of_le h2 (le_add_of_nonneg_left h1')

theorem frobD_mul {f g : PS C 3 dd} (hf : IntS V f) (hg : IntS V g) (hf' : FrobD V f) (hg' : FrobD V g) :
    FrobD V (f * g) := by
  intro j
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  intro μ
  rw [map_add (f := _)]
  apply mm_add_of_mm_of_mm
  · exact mms_mul_of_intS_of_mms hf (hg' j) μ
  · exact mms_mul_of_intS_of_mms hg (hf' j) μ

theorem eq_up_of {p : Fin 3 × Fin dd →₀ ℕ} (hp : ∀ j, p ((0 : Fin 3), j) = 0) :
    (Finsupp.comapDomain (up 2) p ((up_inj 2).injOn)).mapDomain (up 2) = p := by
  ext ⟨k, j⟩
  induction k using Fin.cases with
  | zero =>
    rw [Finsupp.mapDomain_notin_range, hp]
    rintro ⟨q, hq⟩
    simp only [up, Prod.mk.injEq] at hq
    exact Fin.succ_ne_zero _ hq.1
  | succ k' =>
    have e : ((Fin.succ k', j) : Fin 3 × Fin dd) = up 2 (k', j) := rfl
    rw [e, Finsupp.mapDomain_apply_of_injective (up_inj 2), Finsupp.comapDomain_apply]

theorem coeff_free {f : PS C 3 dd} (h1 : ev (rz 2) f = 1) {p : Fin 3 × Fin dd →₀ ℕ}
    (hp : ∀ j, p ((0 : Fin 3), j) = 0) : coeff p f = if p = 0 then 1 else 0 := by
  classical
  have hs : MvPowerSeries.HasSubst (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) := by
    have hz : ∀ q : Fin 3 × Fin dd, constantCoeff (rz (C := C) (dd := dd) 2 q.1 q.2) = 0 := by
      rintro ⟨k, i⟩
      induction k using Fin.cases <;> simp [rz, pt]
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [hz q]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun q => by rw [hz q]; exact IsNilpotent.zero)
  have hmon : ∀ d' : Fin 2 × Fin dd →₀ ℕ,
      (d'.prod fun s n => (X s : PS C 2 dd) ^ n) = MvPowerSeries.monomial d' (1 : C) := by
    intro d'
    induction d' using Finsupp.induction with
    | zero => rw [Finsupp.prod_zero_index, MvPowerSeries.monomial_zero_one]
    | single_add a b g _ _ ih =>
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ih,
        Finsupp.prod_single_index (h := fun x n => (X x : PS C 2 dd) ^ n) (pow_zero _), MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
        one_mul]
  have inj : Function.Injective (Finsupp.mapDomain (M := ℕ) (up (dd := dd) 2)) :=
    Finsupp.mapDomain_injective (up_inj 2)
  have hprod : ∀ (d : Fin 3 × Fin dd →₀ ℕ) (e : Fin 2 × Fin dd →₀ ℕ),
      coeff e (d.prod fun s n => (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) s ^ n) =
        if d = e.mapDomain (up 2) then 1 else 0 := by
    intro d e
    by_cases hx : ∀ j, d ((0 : Fin 3), j) = 0
    · have hd := (eq_up_of hx).symm
      rw [hd, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      show coeff e ((Finsupp.comapDomain (up 2) d ((up_inj 2).injOn)).prod
        fun s n => (X s : PS C 2 dd) ^ n) = _
      rw [hmon, MvPowerSeries.coeff_monomial]
      by_cases he : e = Finsupp.comapDomain (up 2) d ((up_inj 2).injOn)
      · rw [if_pos he, if_pos (by rw [he])]
      · rw [if_neg he, if_neg (fun h => he (inj h).symm)]
    · push_neg at hx
      obtain ⟨j, hj⟩ := hx
      have h0 : (d.prod fun s n => (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) s ^ n) = 0 := by
        apply Finset.prod_eq_zero (i := ((0 : Fin 3), j))
        · exact Finsupp.mem_support_iff.mpr hj
        · show (rz (C := C) (dd := dd) 2 0 j) ^ (d ((0 : Fin 3), j)) = 0
          rw [show rz (C := C) (dd := dd) 2 0 j = 0 from rfl, zero_pow hj]
      rw [h0, map_zero, if_neg]
      intro h
      apply hj
      rw [h, Finsupp.mapDomain_notin_range]
      rintro ⟨q, hq⟩
      simp only [up, Prod.mk.injEq] at hq
      exact Fin.succ_ne_zero _ hq.1
  have key : ∀ e : Fin 2 × Fin dd →₀ ℕ,
      coeff e (ev (rz (C := C) (dd := dd) 2) f) = coeff (e.mapDomain (up 2)) f := by
    intro e
    show coeff e (MvPowerSeries.subst (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) f) = _
    rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ (e.mapDomain (up 2))]
    · rw [hprod, if_pos rfl, smul_eq_mul, mul_one]
    · intro d hd
      rw [hprod, if_neg hd, smul_zero]
  have h2 := key (Finsupp.comapDomain (up 2) p ((up_inj 2).injOn))
  rw [h1, eq_up_of hp, MvPowerSeries.coeff_one] at h2
  rw [← h2]
  by_cases hp0 : p = 0
  · subst hp0
    rw [if_pos rfl, if_pos]
    ext s
    rfl
  · rw [if_neg hp0, if_neg]
    intro h
    apply hp0
    rw [← eq_up_of hp, h, Finsupp.mapDomain_zero]

theorem x_le (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) {p : Fin 3 × Fin dd →₀ ℕ} (hp : p ≤ ix i V.l γ)
    (j : Fin dd) (hj : j ≠ i) : p ((0 : Fin 3), j) = 0 := by
  have h := hp ((0 : Fin 3), j)
  rw [index_raise_first, if_neg hj] at h
  exact Nat.le_zero.mp h

private theorem mm_zero' : V.MM (0 : C) := by
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

private theorem mm_mul_of_mm_of_ge_zero {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [AddValuation.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem coeff_mul_cong {f g : PS C 3 dd} (hf : IntS V f) (hg : IntS V g) (hfF : FrobX V f) (hgF : FrobX V g)
    (hf1 : ev (rz 2) f = 1) (hg1 : ev (rz 2) g = 1) (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) :
    V.MM (coeff (ix i V.l γ) (f * g) - coeff (ix i V.l γ) f - coeff (ix i V.l γ) g) := by
  classical
  unfold FrobX at hfF hgF
  set N := ix i V.l γ with hN
  have hN0 : N ≠ 0 := by
    intro h
    have h2 := congrArg (fun p => p ((0 : Fin 3), i)) h
    simp [hN, index_raise_first] at h2
    exact V.l_prime.ne_zero h2
  have hf0 : coeff 0 f = 1 := by
    have := coeff_free hf1 (p := 0) (fun j => rfl)
    simpa using this
  have hg0 : coeff 0 g = 1 := by
    have := coeff_free hg1 (p := 0) (fun j => rfl)
    simpa using this
  rw [MvPowerSeries.coeff_mul]
  have h1 : ((0 : Fin 3 × Fin dd →₀ ℕ), N) ∈ Finset.HasAntidiagonal.antidiagonal N := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp
  have h2 : (N, (0 : Fin 3 × Fin dd →₀ ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal N).erase (0, N) := by
    rw [Finset.mem_erase]
    refine ⟨fun h => hN0 (congrArg Prod.fst h), ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp
  rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ h2]
  dsimp only
  rw [hf0, hg0, one_mul, mul_one]
  have e : ∀ A B S : C, A + (B + S) - B - A = S := by
    intros
    ring
  rw [e]
  apply mm_finset_sum_of_forall_mm
  intro x hx
  obtain ⟨hne2, hx'⟩ := Finset.mem_erase.mp hx
  obtain ⟨hne1, hx''⟩ := Finset.mem_erase.mp hx'
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx''
  have ha : x.1 ≤ N := by
    rw [← hsum]
    exact le_self_add
  have hb : x.2 ≤ N := by
    rw [← hsum]
    exact le_add_self
  have ha0 : x.1 ≠ 0 := by
    intro h
    apply hne1
    refine Prod.ext h ?_
    show x.2 = N
    rw [← hsum, h, zero_add]
  have hb0 : x.2 ≠ 0 := by
    intro h
    apply hne2
    refine Prod.ext ?_ h
    show x.1 = N
    rw [← hsum, h, add_zero]
  have hxa : ∀ j, j ≠ i → x.1 ((0 : Fin 3), j) = 0 := fun j hj => x_le i γ ha j hj
  have hxb : ∀ j, j ≠ i → x.2 ((0 : Fin 3), j) = 0 := fun j hj => x_le i γ hb j hj
  have hti : x.1 ((0 : Fin 3), i) + x.2 ((0 : Fin 3), i) = V.l := by
    have h3 := congrArg (fun p => p ((0 : Fin 3), i)) hsum
    simp only [Finsupp.add_apply] at h3
    rw [h3, hN, index_raise_first, if_pos rfl]
  by_cases hd : V.l ∣ x.1 ((0 : Fin 3), i)
  · obtain ⟨q, hq⟩ := hd
    rcases q with _ | _ | q
    · have hfree : ∀ j, x.1 ((0 : Fin 3), j) = 0 := by
        intro j
        by_cases hj : j = i
        · rw [hj]
          simpa using hq
        · exact hxa j hj
      rw [coeff_free hf1 hfree, if_neg ha0, zero_mul]
      exact mm_zero'
    · have hfree : ∀ j, x.2 ((0 : Fin 3), j) = 0 := by
        intro j
        by_cases hj : j = i
        · rw [hj]
          simp at hq
          omega
        · exact hxb j hj
      rw [coeff_free hg1 hfree, if_neg hb0, mul_zero]
      exact mm_zero'
    · exfalso
      nlinarith [V.l_prime.pos]
  · exact mm_mul_of_mm_of_ge_zero (hfF x.1 ⟨i, hd⟩) (hg x.2)

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

abbrev p3 (k : Fin 3) : Pt C 3 dd := pt C (n := 3) dd k

theorem z0p3 (k : Fin 3) : ∀ j, constantCoeff ((p3 k : Pt C 3 dd) j) = 0 := by
  intro j
  simp [p3, pt]

theorem pderiv_eval_triple {n : ℕ} {a : Fin 3 → Pt C n dd} (ha : Z0 a) (f : PS C 3 dd) (q : Fin n × Fin dd) :
    pderiv (R := C) q (ev a f) = ∑ j, ev a (pderiv (R := C) ((0 : Fin 3), j) f) * pderiv (R := C) q (a 0 j) +
      ∑ j, ev a (pderiv (R := C) ((1 : Fin 3), j) f) * pderiv (R := C) q (a 1 j) +
      ∑ j, ev a (pderiv (R := C) ((2 : Fin 3), j) f) * pderiv (R := C) q (a 2 j) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 3 × Fin dd => a p.1 p.2) (fun p => ha p.1 p.2) f q,
    Fintype.sum_prod_type, Fin.sum_univ_three]

theorem d_ev_keep {f : PS C 2 dd} {B : Pt C 3 dd} (hB : ∀ j, constantCoeff (B j) = 0) (i : Fin dd)
    (hd : ∀ j, pderiv (R := C) ((0 : Fin 3), i) (B j) = 0) :
    pderiv (R := C) ((0 : Fin 3), i) (ev (n := 3) ![p3 0, B] f) =
      ev (n := 3) ![p3 0, B] (pderiv (R := C) ((0 : Fin 2), i) f) := by
  have hz : Z0 (![p3 0, B] : Fin 2 → Pt C 3 dd) := fun k j => by
    fin_cases k
    · exact z0p3 0 j
    · exact hB j
  have hchain := Formalism.G.LogCR.pderiv_subst
    (a := fun p : Fin 2 × Fin dd => (![p3 0, B] : Fin 2 → Pt C 3 dd) p.1 p.2)
    (fun p => hz p.1 p.2) f ((0 : Fin 3), i)
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at hchain
  refine hchain.trans ?_
  refine (congrArg₂ (· + ·) ?_ (Finset.sum_eq_zero fun j _ => ?_)).trans (add_zero _)
  · rw [Finset.sum_eq_single i (fun j _ hj => by
        show _ * pderiv (R := C) _ (pt C (n := 3) dd 0 j) = 0
        have hzero : pderiv (R := C) ((0 : Fin 3), i) (p3 0 j) = 0 :=
          pderiv_X_of_ne (fun h => hj (congrArg Prod.snd h))
        rw [hzero, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
    show _ * pderiv (R := C) _ (pt C (n := 3) dd 0 i) = _
    have hone : pderiv (R := C) ((0 : Fin 3), i) (p3 0 i) = 1 := pderiv_X_self
    rw [hone, mul_one]
    rfl
  · show _ * pderiv (R := C) _ (B j) = 0
    rw [hd j, mul_zero]

theorem d_ev_keep_iter {f : PS C 2 dd} {B : Pt C 3 dd} (hB : ∀ j, constantCoeff (B j) = 0) (i : Fin dd)
    (hd : ∀ j, pderiv (R := C) ((0 : Fin 3), i) (B j) = 0) (L : ℕ) :
    (pderiv (R := C) ((0 : Fin 3), i))^[L] (ev (n := 3) ![p3 0, B] f) =
      ev (n := 3) ![p3 0, B] ((pderiv (R := C) ((0 : Fin 2), i))^[L] f) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, d_ev_keep hB i hd]

def SS (G : FGLaw C dd) : Pt C 3 dd := addOf G.F (p3 1) (p3 2)

theorem triple_sum_constantCoeff (G : FGLaw C dd) (j : Fin dd) : constantCoeff (SS G j) = 0 :=
  const_ev (z0_pp 1 2) (G.const j)

theorem SS_int (G : FGLaw C dd) (hF : ∀ i, IntS V (G.F i)) (j : Fin dd) : IntS V (SS G j) :=
  intS_ev (z0_pp 1 2) (fun k m => by fin_cases k <;> exact intS_X _) (hF j)

theorem SS_d (G : FGLaw C dd) (i j : Fin dd) : pderiv (R := C) ((0 : Fin 3), i) (SS G j) = 0 := by
  show pderiv (R := C) ((0 : Fin 3), i) (ev (n := 3) ![p3 1, p3 2] (G.F j)) = 0
  have hz : Z0 (![p3 1, p3 2] : Fin 2 → Pt C 3 dd) := z0_pp 1 2
  have hchain := Formalism.G.LogCR.pderiv_subst
    (a := fun p : Fin 2 × Fin dd => (![p3 1, p3 2] : Fin 2 → Pt C 3 dd) p.1 p.2)
    (fun p => hz p.1 p.2) (G.F j) ((0 : Fin 3), i)
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at hchain
  refine hchain.trans ?_
  have hzero (k : Fin 3) (m : Fin dd) (hk : k ≠ 0) :
      pderiv (R := C) ((0 : Fin 3), i) (p3 k m) = 0 :=
    pderiv_X_of_ne (fun h => hk (congrArg Prod.fst h))
  refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun m _ => ?_) (Finset.sum_eq_zero fun m _ => ?_)).trans
    (add_zero 0)
  · show _ * pderiv (R := C) _ (pt C (n := 3) dd 1 m) = 0
    rw [hzero 1 m (by decide), mul_zero]
  · show _ * pderiv (R := C) _ (pt C (n := 3) dd 2 m) = 0
    rw [hzero 2 m (by decide), mul_zero]

theorem triple_point_pderiv_first_zero (k : Fin 3) (hk : k ≠ 0) (i j : Fin dd) :
    pderiv (R := C) ((0 : Fin 3), i) ((p3 k : Pt C 3 dd) j) = 0 :=
  pderiv_X_of_ne (fun h => hk (congrArg Prod.fst h))

def m3 (G : FGLaw C dd) (n : ℕ) : Pt C 3 dd := fun k => ev ![(p3 0 : Pt C 3 dd)] (mulL G.F n k)

theorem triple_multiplication_constantCoeff (G : FGLaw C dd) (n : ℕ) (k : Fin dd) : constantCoeff (m3 G n k) = 0 :=
  const_ev (z0_1 _ (z0p3 0)) (multiplication_constantCoeff_zero G n k)

theorem triple_multiplication_integral (G : FGLaw C dd) (hF : ∀ i, IntS V (G.F i)) (n : ℕ) (k : Fin dd) : IntS V (m3 G n k) :=
  intS_ev (z0_1 _ (z0p3 0)) (fun k' m => by fin_cases k'; exact intS_X _) (mulL_int G hF n k)

def UU (Y : FBChart C V O dd) (w : Pt C 3 dd) : PS C 3 dd := ev (n := 3) ![p3 0, w] Y.u1

def QQ (Y : FBChart C V O dd) : PS C 3 dd := ev (n := 3) ![m3 Y.B.G V.l, p3 1, p3 2] Y.B.ph2

theorem ex_nsmul {σ : Type} (f : MvPowerSeries σ C) (hf : constantCoeff f = 0) (n : ℕ) :
    ex (n • f) = ex f ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih =>
    rw [succ_nsmul, ex_add _ _ (by simp [hf]) hf, ih, pow_succ]

theorem height_at_zero_first (Y : FBChart C V O dd) {n : ℕ} (W : Pt C n dd) (hW : ∀ j, constantCoeff (W j) = 0) :
    ev (n := n) ![0, W] Y.h = 0 := by
  have h0 := Y.gauge.ax0
  have hz : Z0 (![(0 : Pt C 1 dd), pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) := fun k j => by
    fin_cases k
    · exact map_zero _
    · exact z0_pt 0 j
  have h1 := congrArg (ev ![W]) h0
  rw [ev_ev hz (z0_1 W hW), ev_zero (z0_1 W hW)] at h1
  rw [← h1]
  congr 1
  funext k j
  fin_cases k
  · exact (ev_zero (z0_1 W hW)).symm
  · exact (ev_X (z0_1 W hW) 0 j).symm

theorem restrict_triple_multiplication (G : FGLaw C dd) (n : ℕ) (j : Fin dd) : ev (rz 2) (m3 G n j) = 0 := by
  unfold m3
  rw [ev_ev (z0_1 _ (z0p3 0)) (constant_zero_restrict_points 2)]
  have e : (fun k m => ev (rz (C := C) (dd := dd) 2) ((![(p3 0 : Pt C 3 dd)] : Fin 1 → Pt C 3 dd) k m)) =
      ![(0 : Pt C 2 dd)] := by
    funext k m
    fin_cases k
    exact ev_X (constant_zero_restrict_points 2) 0 m
  rw [e, ev_zero_pt, multiplication_constantCoeff_zero, map_zero]

theorem constant_zero_two_points {w : Pt C 3 dd} (P : Pt C 3 dd) (hP : ∀ j, constantCoeff (P j) = 0)
    (hw : ∀ j, constantCoeff (w j) = 0) : Z0 (![P, w] : Fin 2 → Pt C 3 dd) := by
  intro i j
  fin_cases i
  · exact hP j
  · exact hw j

theorem ev_smulC {m n : ℕ} {a : Fin m → Pt C n dd} (ha : Z0 a) (c : C) (f : PS C m dd) :
    ev a (c • f) = c • ev a f := by
  rw [ev_eq_alg ha, map_smul, ← ev_eq_alg ha]

theorem UU_eq (Y : FBChart C V O dd) (w : Pt C 3 dd) (hw : ∀ j, constantCoeff (w j) = 0) :
    UU Y w = ex (ev (n := 3) ![m3 Y.B.G V.l, w] Y.h - (V.l : C) • ev (n := 3) ![p3 0, w] Y.h) := by
  have hz := constant_zero_two_points (p3 0) (z0p3 0) hw
  have hE0 : constantCoeff (gg Y V.l - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, h_const, mul_zero, sub_zero]
    exact height_multiple_constantCoeff Y V.l
  unfold UU
  rw [show Y.u1 = ex (gg Y V.l - (V.l : C) • Y.h) from rfl, ev_ex hz _ hE0, ev_sub hz, ev_smulC hz]
  congr 2
  unfold gg
  rw [ev_ev (constant_zero_double_multiplication_pair Y V.l) hz]
  congr 1
  funext k j
  fin_cases k
  · show ev ![p3 0, w] (ev ![pt C (n := 2) dd 0] (mulL Y.B.G.F V.l j)) = m3 Y.B.G V.l j
    rw [ev_ev (z0_1 _ (fun j => z0_pt 0 j)) hz]
    congr 1
    funext k' m
    fin_cases k'
    exact ev_X hz 0 m
  · exact ev_X hz 1 j

theorem hph2 (Y : FBChart C V O dd) : Y.B.ph2 = ex (ev (n := 3) ![p3 0, p3 1] Y.h + ev (n := 3) ![p3 0, p3 2] Y.h -
    ev (n := 3) ![p3 0, SS Y.B.G] Y.h) := by
  have := Y.gauge.ph2
  rwa [toK_self, FK_self] at this

theorem eval_height_constantCoeff (Y : FBChart C V O dd) {P w : Pt C 3 dd} (hP : ∀ j, constantCoeff (P j) = 0)
    (hw : ∀ j, constantCoeff (w j) = 0) : constantCoeff (ev (n := 3) ![P, w] Y.h) = 0 :=
  const_ev (constant_zero_two_points P hP hw) (h_const Y)

theorem QQ_eq (Y : FBChart C V O dd) : QQ Y = ex (ev (n := 3) ![m3 Y.B.G V.l, p3 1] Y.h +
    ev (n := 3) ![m3 Y.B.G V.l, p3 2] Y.h - ev (n := 3) ![m3 Y.B.G V.l, SS Y.B.G] Y.h) := by
  have ha : Z0 (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) := fun k j => by
    fin_cases k
    · exact triple_multiplication_constantCoeff _ _ j
    · exact z0p3 1 j
    · exact z0p3 2 j
  have hE0 : constantCoeff (ev (n := 3) ![p3 0, p3 1] Y.h + ev (n := 3) ![p3 0, p3 2] Y.h -
      ev (n := 3) ![p3 0, SS Y.B.G] Y.h) = 0 := by
    rw [map_sub, map_add (f := _), eval_height_constantCoeff Y (z0p3 0) (z0p3 1), eval_height_constantCoeff Y (z0p3 0) (z0p3 2), eval_height_constantCoeff Y (z0p3 0) (triple_sum_constantCoeff _)]
    simp
  unfold QQ
  rw [hph2, ev_ex ha _ hE0, ev_sub ha, ev_add ha, ev_ev (constant_zero_two_points _ (z0p3 0) (z0p3 1)) ha,
    ev_ev (constant_zero_two_points _ (z0p3 0) (z0p3 2)) ha, ev_ev (constant_zero_two_points _ (z0p3 0) (triple_sum_constantCoeff _)) ha]
  have e1 : (fun k j => ev ![m3 Y.B.G V.l, p3 1, p3 2] ((![p3 0, p3 1] : Fin 2 → Pt C 3 dd) k j)) =
      ![m3 Y.B.G V.l, p3 1] := by
    funext k j; fin_cases k
    · exact ev_X ha 0 j
    · exact ev_X ha 1 j
  have e2 : (fun k j => ev ![m3 Y.B.G V.l, p3 1, p3 2] ((![p3 0, p3 2] : Fin 2 → Pt C 3 dd) k j)) =
      ![m3 Y.B.G V.l, p3 2] := by
    funext k j; fin_cases k
    · exact ev_X ha 0 j
    · exact ev_X ha 2 j
  have e3 : (fun k j => ev ![m3 Y.B.G V.l, p3 1, p3 2] ((![p3 0, SS Y.B.G] : Fin 2 → Pt C 3 dd) k j)) =
      ![m3 Y.B.G V.l, SS Y.B.G] := by
    funext k j; fin_cases k
    · exact ev_X ha 0 j
    · show ev ![m3 Y.B.G V.l, p3 1, p3 2] (ev (n := 3) ![p3 1, p3 2] (Y.B.G.F j)) = SS Y.B.G j
      rw [ev_ev (z0_pp 1 2) ha]
      congr 1
      funext k' m; fin_cases k'
      · exact ev_X ha 1 m
      · exact ev_X ha 2 m
  rw [e1, e2, e3]

theorem ident (Y : FBChart C V O dd) :
    UU Y (SS Y.B.G) * QQ Y = UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l := by
  have hm := triple_multiplication_constantCoeff Y.B.G V.l
  set a := ev (n := 3) ![m3 Y.B.G V.l, SS Y.B.G] Y.h with ha
  set b1 := ev (n := 3) ![m3 Y.B.G V.l, p3 1] Y.h with hb1
  set b2 := ev (n := 3) ![m3 Y.B.G V.l, p3 2] Y.h with hb2
  set c0 := ev (n := 3) ![p3 0, SS Y.B.G] Y.h with hc0
  set c1 := ev (n := 3) ![p3 0, p3 1] Y.h with hc1
  set c2 := ev (n := 3) ![p3 0, p3 2] Y.h with hc2
  have za : constantCoeff a = 0 := eval_height_constantCoeff Y hm (triple_sum_constantCoeff _)
  have zb1 : constantCoeff b1 = 0 := eval_height_constantCoeff Y hm (z0p3 1)
  have zb2 : constantCoeff b2 = 0 := eval_height_constantCoeff Y hm (z0p3 2)
  have zc0 : constantCoeff c0 = 0 := eval_height_constantCoeff Y (z0p3 0) (triple_sum_constantCoeff _)
  have zc1 : constantCoeff c1 = 0 := eval_height_constantCoeff Y (z0p3 0) (z0p3 1)
  have zc2 : constantCoeff c2 = 0 := eval_height_constantCoeff Y (z0p3 0) (z0p3 2)
  have zs : ∀ (c : C) (f : PS C 3 dd), constantCoeff f = 0 → constantCoeff (c • f) = 0 := fun c f hf => by
    rw [show c • f = MvPowerSeries.C c * f from (MvPowerSeries.smul_eq_C_mul f c), map_mul, hf, mul_zero]
  have zE : constantCoeff (c1 + c2 - c0) = 0 := by rw [map_sub, map_add (f := _), zc1, zc2, zc0]; simp
  rw [UU_eq _ _ (triple_sum_constantCoeff _), UU_eq _ _ (z0p3 1), UU_eq _ _ (z0p3 2), QQ_eq, hph2, ← hc0, ← hc1, ← hc2, ← ha,
    ← hb1, ← hb2, ← ex_nsmul _ zE V.l,
    ← ex_add _ _ (by rw [map_sub, za, zs _ _ zc0, sub_zero]) (by rw [map_sub, map_add (f := _), zb1, zb2, za]; simp),
    ← ex_add _ _ (by rw [map_sub, zb1, zs _ _ zc1, sub_zero]) (by rw [map_sub, zb2, zs _ _ zc2, sub_zero]),
    ← ex_add _ _ (by rw [map_add (f := _), map_sub, map_sub, zb1, zb2, zs _ _ zc1, zs _ _ zc2]; simp)
      (by rw [map_nsmul, zE, nsmul_zero])]
  congr 1
  rw [Nat.cast_smul_eq_nsmul C, Nat.cast_smul_eq_nsmul C, Nat.cast_smul_eq_nsmul C]
  simp only [nsmul_sub, nsmul_add]
  abel

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem pderiv_first_unit_series_maximal (Y : FBChart C V O dd) (i : Fin dd) : MaximalIdealCongruence.MMS V (pderiv (R := C) ((0 : Fin 2), i) Y.u1) := by
  have hu : Y.u1 = FB.expS C (evl Y V.l Y.h - (V.l : C) • Y.h) := rfl
  have hE0 : constantCoeff (evl Y V.l Y.h - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, PartialDerivEval.h_const, mul_zero, sub_zero]
    exact FirstUnitSeriesIntegrality.height_multiple_constantCoeff Y V.l
  have hd : pderiv (R := C) ((0 : Fin 2), i) Y.u1 =
      (V.l : PS C 2 dd) * (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    rw [hu, PartialDerivEval.pderiv_expS hE0, dE, ← hu]; ring
  have hint : IntS V (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    refine PartialDerivEval.intS_mul (first_unit_series_integral C V O dd Y)
      (PartialDerivEval.intS_sum _ fun m _ => PartialDerivEval.intS_mul ?_ ?_)
    · have hP : IntS V (Pm Y m) := by
        refine PartialDerivEval.intS_ev constant_zero_lift_triple (fun k j => ?_) (PartialDerivEval.intS_pderiv Y.intPh1 _)
        fin_cases k
        · exact PartialDerivEval.intS_X _
        · exact PartialDerivEval.intS_zero
        · exact PartialDerivEval.intS_X _
      have hP' : IntS V (evl Y V.l (Pm Y m)) := by
        refine PartialDerivEval.intS_ev (constant_zero_double_multiplication Y V.l) (fun k j => ?_) hP
        fin_cases k
        · exact FirstUnitSeriesIntegrality.double_multiplication_integral Y.B.G Y.intF V.l j
        · exact PartialDerivEval.intS_X _
      rw [sub_eq_add_neg]
      exact PartialDerivEval.intS_add hP (PartialDerivEval.intS_neg hP')
    · refine PartialDerivEval.intS_ev (PartialDerivEval.z0_1 _ z0P0) (fun k j => ?_) (MulLFrob.JL_int Y m i)
      fin_cases k
      exact PartialDerivEval.intS_X _
  rw [hd]; exact MaximalIdealCongruence.mms_l_mul hint

theorem int_two {w : Pt C 3 dd} (P : Pt C 3 dd) (hP : ∀ j, IntS V (P j)) (hw : ∀ j, IntS V (w j)) :
    ∀ k j, IntS V ((![P, w] : Fin 2 → Pt C 3 dd) k j) := fun k j => by
  fin_cases k
  · exact hP j
  · exact hw j

theorem triple_coordinate_integral (k : Fin 3) (j : Fin dd) : IntS V ((p3 k : Pt C 3 dd) j) := intS_X _

theorem UU_int (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0)
    (hw : ∀ j, IntS V (w j)) : IntS V (UU Y w) :=
  intS_ev (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (first_unit_series_integral C V O dd Y)

theorem UU_frob (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0)
    (hw : ∀ j, IntS V (w j)) (hd : ∀ i j, pderiv (R := C) ((0 : Fin 3), i) (w j) = 0) : FrobD V (UU Y w) := by
  intro i
  unfold UU
  rw [d_ev_keep hw0 i (hd i)]
  exact MaximalIdealCongruence.MMS.ev_of (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (pderiv_first_unit_series_maximal Y i)

theorem UU_one (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0) :
    ev (rz 2) (UU Y w) = 1 := by
  have hz := constant_zero_two_points (p3 0) (z0p3 0) hw0
  have hw' : ∀ j, constantCoeff (ev (rz (C := C) (dd := dd) 2) (w j)) = 0 := fun j => const_ev (constant_zero_restrict_points 2) (hw0 j)
  have hE0 : constantCoeff (ev (n := 3) ![m3 Y.B.G V.l, w] Y.h - (V.l : C) • ev (n := 3) ![p3 0, w] Y.h) = 0 := by
    rw [map_sub, eval_height_constantCoeff Y (triple_multiplication_constantCoeff _ _) hw0, show (V.l : C) • ev (n := 3) ![p3 0, w] Y.h =
      MvPowerSeries.C (V.l : C) * ev (n := 3) ![p3 0, w] Y.h from MvPowerSeries.smul_eq_C_mul _ _, map_mul,
      eval_height_constantCoeff Y (z0p3 0) hw0, mul_zero, sub_zero]
  rw [UU_eq Y w hw0, ev_ex (constant_zero_restrict_points 2) _ hE0, ev_sub (constant_zero_restrict_points 2), ev_smulC (constant_zero_restrict_points 2),
    ev_ev (constant_zero_two_points _ (triple_multiplication_constantCoeff _ _) hw0) (constant_zero_restrict_points 2), ev_ev hz (constant_zero_restrict_points 2)]
  have e1 : (fun k j => ev (rz (C := C) (dd := dd) 2) ((![m3 Y.B.G V.l, w] : Fin 2 → Pt C 3 dd) k j)) =
      ![0, fun j => ev (rz 2) (w j)] := by
    funext k j; fin_cases k
    · exact restrict_triple_multiplication _ _ j
    · rfl
  have e2 : (fun k j => ev (rz (C := C) (dd := dd) 2) ((![p3 0, w] : Fin 2 → Pt C 3 dd) k j)) =
      ![0, fun j => ev (rz 2) (w j)] := by
    funext k j; fin_cases k
    · exact ev_X (constant_zero_restrict_points 2) 0 j
    · rfl
  rw [e1, e2, height_at_zero_first Y _ hw', smul_zero, sub_zero, ex_zero]

theorem constant_zero_triple_multiplication (Y : FBChart C V O dd) : Z0 (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) := fun k j => by
  fin_cases k
  · exact triple_multiplication_constantCoeff _ _ j
  · exact z0p3 1 j
  · exact z0p3 2 j

theorem QQ_int (Y : FBChart C V O dd) : IntS V (QQ Y) := by
  refine intS_ev (constant_zero_triple_multiplication Y) (fun k j => ?_) Y.intPh2
  fin_cases k
  · exact triple_multiplication_integral _ Y.intF _ j
  · exact intS_X _
  · exact intS_X _

theorem pderiv_triple_multiplication (Y : FBChart C V O dd) (k i : Fin dd) :
    pderiv (R := C) ((0 : Fin 3), i) (m3 Y.B.G V.l k) = ev ![(p3 0 : Pt C 3 dd)] (Jac (mulL Y.B.G.F V.l) k i) := by
  show pderiv (R := C) ((0 : Fin 3), i) (ev ![(p3 0 : Pt C 3 dd)] (mulL Y.B.G.F V.l k)) = _
  rw [pderiv_eval_single (P := (p3 0 : Pt C 3 dd)) (z0p3 0), Finset.sum_eq_single i (fun j _ hj => by
      show _ * pderiv (R := C) _ (pt C (n := 3) dd 0 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
  show _ * pderiv (R := C) _ (pt C (n := 3) dd 0 i) = _
  rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_pos rfl, mul_one]
  rfl

theorem pderiv_triple_multiplication_maximal (Y : FBChart C V O dd) (k i : Fin dd) : MaximalIdealCongruence.MMS V (pderiv (R := C) ((0 : Fin 3), i) (m3 Y.B.G V.l k)) := by
  rw [pderiv_triple_multiplication, jac_l, Matrix.smul_apply, ev_eq_alg (z0_1 _ (z0p3 0)), map_nsmul, ← ev_eq_alg (z0_1 _ (z0p3 0)),
    nsmul_eq_mul]
  refine MaximalIdealCongruence.mms_l_mul (intS_ev (z0_1 _ (z0p3 0)) (fun k' j => by fin_cases k'; exact intS_X _) ?_)
  rw [Matrix.mul_apply]
  refine intS_sum _ fun j _ => intS_mul ?_ (JL_int Y j i)
  refine intS_ev (z0_1 _ (multiplication_constantCoeff_zero Y.B.G V.l)) (fun k' j' => ?_) (JF_int Y k j)
  fin_cases k'
  exact mulL_int Y.B.G Y.intF V.l j'

theorem QQ_frob (Y : FBChart C V O dd) : FrobD V (QQ Y) := by
  intro i
  unfold QQ
  rw [pderiv_eval_triple (constant_zero_triple_multiplication Y)]
  have h1 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv (R := C) ((1 : Fin 3), j) Y.B.ph2) *
      pderiv (R := C) ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 1 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      show _ * pderiv (R := C) _ (pt C (n := 3) dd 1 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (1 : Fin 3) ≠ 0), mul_zero]
  have h2 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv (R := C) ((2 : Fin 3), j) Y.B.ph2) *
      pderiv (R := C) ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 2 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      show _ * pderiv (R := C) _ (pt C (n := 3) dd 2 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 0), mul_zero]
  rw [h1, h2, add_zero, add_zero]
  refine MaximalIdealCongruence.mms_sum _ fun j _ => MaximalIdealCongruence.MMS.mul_left ?_ (pderiv_triple_multiplication_maximal Y j i)
  refine intS_ev (constant_zero_triple_multiplication Y) (fun k m => ?_) (intS_pderiv Y.intPh2 _)
  fin_cases k
  · exact triple_multiplication_integral _ Y.intF _ m
  · exact intS_X _
  · exact intS_X _

theorem rz_eq : (rz (C := C) (dd := dd) 2) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by
  funext k j
  fin_cases k <;> rfl

theorem QQ_one (Y : FBChart C V O dd) : ev (rz 2) (QQ Y) = 1 := by
  unfold QQ
  rw [ev_ev (constant_zero_triple_multiplication Y) (constant_zero_restrict_points 2)]
  have e : (fun k j => ev (rz (C := C) (dd := dd) 2)
      ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) k j)) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by
    funext k j; fin_cases k
    · exact restrict_triple_multiplication _ _ j
    · exact ev_X (constant_zero_restrict_points 2) 1 j
    · exact ev_X (constant_zero_restrict_points 2) 2 j
  rw [e]
  exact Y.B.cocycleRight_zero_fst

theorem second_pairing_restrict_one (Y : FBChart C V O dd) : ev (rz 2) Y.B.ph2 = 1 := by
  rw [rz_eq]; exact Y.B.cocycleRight_zero_fst

theorem second_pairing_pow_restrict_one (Y : FBChart C V O dd) : ev (rz 2) (Y.B.ph2 ^ V.l) = 1 := by
  rw [ev_eq_alg (constant_zero_restrict_points 2), map_pow, ← ev_eq_alg (constant_zero_restrict_points 2), second_pairing_restrict_one, one_pow]

theorem second_pairing_pow_frobenius (Y : FBChart C V O dd) : FrobD V (Y.B.ph2 ^ V.l) := by
  intro i
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  exact MaximalIdealCongruence.mms_l_mul (intS_mul (intS_pow Y.intPh2 _) (intS_pderiv Y.intPh2 _))

end Formalism.L2.FormalSeriesBounds.FunEq
