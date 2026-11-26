module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThRestGcVOf

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThLinKConst
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThPosSubPosAdd
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lamF altF)

section CgCalc

variable {ι K : Type} [Field K] (R : Subring K) (pp : K)

def Cg (f g : MvPowerSeries ι K) : Prop := ∃ Y : MvPowerSeries ι K, IntR R Y ∧ f = g + MvPowerSeries.C pp * Y

variable {R pp}

theorem cg_refl (f : MvPowerSeries ι K) : Cg R pp f f := ⟨0, IntR_zero, by simp⟩

theorem cg_of_eq {f g : MvPowerSeries ι K} (h : f = g) : Cg R pp f g := h ▸ cg_refl f

theorem cg_trans {f g k : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp g k) : Cg R pp f k := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + Y', IntR_add hY hY', by rw [e, e']; ring⟩

theorem cg_add {f g f' g' : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp f' g') :
    Cg R pp (f + f') (g + g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + Y', IntR_add hY hY', by rw [e, e']; ring⟩

theorem cg_sum {α : Type} (s : Finset α) (F G : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Cg R pp (F a) (G a)) :
    Cg R pp (∑ a ∈ s, F a) (∑ a ∈ s, G a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact cg_refl _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact cg_add (h a (Finset.mem_insert_self _ _)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem cg_mul {f g f' g' : MvPowerSeries ι K} (hf' : IntR R f') (hg : IntR R g) (h1 : Cg R pp f g)
    (h2 : Cg R pp f' g') : Cg R pp (f * f') (g * g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  refine ⟨g * Y' + Y * f', IntR_add (IntR_mul hg hY') (IntR_mul hY hf'), ?_⟩
  rw [e]
  conv_lhs => rw [add_mul, e']
  conv_rhs => rw [e']
  ring

theorem cg_pow {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) (h : Cg R pp f g) (k : ℕ) :
    Cg R pp (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact cg_of_eq (by simp)
  | succ k ih => rw [pow_succ, pow_succ]; exact cg_mul hf (IntR_pow hg k) ih h

theorem cg_of_coeff {f g : MvPowerSeries ι K}
    (h : ∀ n, ∃ y ∈ R, MvPowerSeries.coeff n f = MvPowerSeries.coeff n g + pp * y) : Cg R pp f g := by
  choose y hy he using h
  let Y : MvPowerSeries ι K := fun n => y n
  have hYc : ∀ n, MvPowerSeries.coeff n Y = y n := fun _ => rfl
  refine ⟨Y, fun n => by rw [hYc]; exact hy n, ?_⟩
  ext n
  rw [map_add (f := _), MvPowerSeries.coeff_C_mul, he n, hYc]

theorem cg_coeff {f g : MvPowerSeries ι K} (h : Cg R pp f g) (n : ι →₀ ℕ) :
    ∃ y ∈ R, MvPowerSeries.coeff n f = MvPowerSeries.coeff n g + pp * y := by
  obtain ⟨Y, hY, e⟩ := h
  exact ⟨_, hY n, by rw [e, map_add (f := _), MvPowerSeries.coeff_C_mul]⟩

end CgCalc

section Pos

theorem th_posSub_posAdd {n' : ℕ} (s : Fin n') (d : ℕ) : posSub (posAdd s d) d = s := by
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by have := s.pos; omega⟩
  apply Fin.ext
  show ((s.val + d) % (m + 1) + (m + 1) * d - d) % (m + 1) = s.val
  have e : (s.val + d) % (m + 1) + (m + 1) * d - d = (s.val + d) % (m + 1) + m * d := by
    have : (m + 1) * d = m * d + d := by ring
    omega
  rw [e, Nat.mod_add_mod]
  have e2 : s.val + d + m * d = s.val + (m + 1) * d := by ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.isLt]

theorem th_posAdd_posSub {n' : ℕ} (t : Fin n') (d : ℕ) : posAdd (posSub t d) d = t := by
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by have := t.pos; omega⟩
  apply Fin.ext
  show ((t.val + (m + 1) * d - d) % (m + 1) + d) % (m + 1) = t.val
  have e : t.val + (m + 1) * d - d = t.val + m * d := by
    have : (m + 1) * d = m * d + d := by ring
    omega
  rw [e, Nat.mod_add_mod]
  have e2 : t.val + m * d + d = t.val + (m + 1) * d := by ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.isLt]

theorem th_odd_posAdd {n' : ℕ} (hev : Even n') (s : Fin n') (d : ℕ) :
    (posAdd s d).val % 2 = (s.val + d) % 2 := by
  show (s.val + d) % n' % 2 = _
  exact Nat.mod_mod_of_dvd _ hev.two_dvd

end Pos

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lamF altF)

variable {p : ℕ} [hp : Fact p.Prime] {n' r0 r1 : ℕ} (K' : Type) [Field K'] [Algebra (K0 p) K']

def Aw (w : WW p) (k : ℕ) : K' := wK' p K' ((sigW p)^[k] w)

def FrobSumH (p n' r0 r1 : ℕ) (K' : Type) [Field K'] (R : Subring K') : Prop :=
  ∀ (s : Finset (Fin n')) (x : Fin n' → MvPowerSeries (Zidx n' r0 r1) K'), (∀ i ∈ s, IntR R (x i)) →
    ∃ Y : MvPowerSeries (Zidx n' r0 r1) K', IntR R Y ∧
      (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + MvPowerSeries.C (p : K') * Y

def FrobWH (p : ℕ) [Fact p.Prime] : Prop := ∀ a : WW p, ∃ y : WW p, sigW p a = a ^ p + (p : WW p) * y

variable {K'} (vp : K')

theorem th_Aw_mem (w : WW p) (k : ℕ) : Aw K' w k ∈ Rp p K' vp := W_mem_Rp p K' vp _

theorem th_Aw_succ (hW : FrobWH p) (w : WW p) (k : ℕ) :
    ∃ y ∈ Rp p K' vp, Aw K' w (k + 1) = Aw K' w k ^ p + (p : K') * y := by
  obtain ⟨y, hy⟩ := hW ((sigW p)^[k] w)
  refine ⟨wK' p K' y, ?_, ?_⟩
  · have h1 := th_Aw_mem vp y 0
    simpa [Aw] using h1
  · simp only [Aw, wK', Function.iterate_succ_apply', hy, map_add (f := _), map_mul, map_pow, map_natCast]

theorem th_frob_lin (hF : FrobSumH p n' r0 r1 K' (Rp p K' vp)) (hW : FrobWH p) (w : WW p) (P : Finset (Fin n'))
    (e : Fin n' → ℕ) (x : Fin n' → MvPowerSeries (Zidx n' r0 r1) K') (hx : ∀ s, IntR (Rp p K' vp) (x s)) :
    Cg (Rp p K' vp) (p : K') ((∑ s ∈ P, MvPowerSeries.C (Aw K' w (e s)) * x s) ^ p)
      (∑ s ∈ P, MvPowerSeries.C (Aw K' w (e s + 1)) * x s ^ p) := by
  have hint : ∀ s ∈ P, IntR (Rp p K' vp) (MvPowerSeries.C (Aw K' w (e s)) * x s) :=
    fun s _ => IntR_mul (IntR_C (R := Rp p K' vp) (th_Aw_mem vp w _)) (hx s)
  obtain ⟨Y, hY, hEq⟩ := hF P (fun s => MvPowerSeries.C (Aw K' w (e s)) * x s) hint
  have h1 : Cg (Rp p K' vp) (p : K') ((∑ s ∈ P, MvPowerSeries.C (Aw K' w (e s)) * x s) ^ p)
      (∑ s ∈ P, (MvPowerSeries.C (Aw K' w (e s)) * x s) ^ p) := ⟨Y, hY, hEq⟩
  refine cg_trans h1 (cg_sum _ _ _ fun s _ => ?_)
  obtain ⟨z, hz, hzeq⟩ := th_Aw_succ vp hW w (e s)
  rw [mul_pow, ← map_pow]
  refine cg_mul (IntR_pow (hx s) p) (IntR_C (R := Rp p K' vp) (th_Aw_mem vp w _)) ?_ (cg_refl _)
  refine cg_of_coeff fun n => ?_
  by_cases hn : n = 0
  · subst hn
    refine ⟨-z, Subring.neg_mem _ hz, ?_⟩
    rw [MvPowerSeries.coeff_zero_C, MvPowerSeries.coeff_zero_C, hzeq]
    ring
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    rw [MvPowerSeries.coeff_C, MvPowerSeries.coeff_C, if_neg hn, if_neg hn]
    ring

def linK (K' : Type) [Field K'] [Algebra (K0 p) K'] (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1)
    (k : ℕ) : MvPowerSeries (Zidx n' r0 r1) K' :=
  ∑ s ∈ P, MvPowerSeries.C (Aw K' w (s.val + k)) * MvPowerSeries.X (s, a, b) ^ (p ^ k)

theorem th_linK_int (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1) (k : ℕ) :
    IntR (Rp p K' vp) (linK K' w P a b k) := by
  unfold linK
  exact IntR_sum _ _ fun s _ => IntR_mul (IntR_C (R := Rp p K' vp) (th_Aw_mem vp w _))
    (IntR_pow (IntR_X (R := Rp p K' vp) _) _)

theorem th_linK_const (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1) :
    MvPowerSeries.constantCoeff (linK K' w P a b 0) = 0 := by
  simp [linK]

theorem th_claimF (hF : FrobSumH p n' r0 r1 K' (Rp p K' vp)) (hW : FrobWH p) (w : WW p) (P : Finset (Fin n'))
    (a : Fin r0) (b : Fin r1) (k : ℕ) :
    Cg (Rp p K' vp) (p : K') (linK K' w P a b 0 ^ (p ^ k)) (linK K' w P a b k) := by
  induction k with
  | zero =>
    apply cg_of_eq
    simp only [pow_zero, pow_one]
  | succ k ih =>
    have hL : IntR (Rp p K' vp) (linK K' w P a b 0) := th_linK_int vp w P a b 0
    have h1 := cg_pow (IntR_pow hL (p ^ k)) (th_linK_int vp w P a b k) ih p
    rw [← pow_mul, ← pow_succ] at h1
    refine cg_trans h1 ?_
    have h2 := th_frob_lin vp hF hW w P (fun s => s.val + k) (fun s => MvPowerSeries.X (s, a, b) ^ (p ^ k))
      (fun s => IntR_pow (IntR_X (R := Rp p K' vp) _) _)
    simp only [← pow_mul, ← pow_succ] at h2
    exact h2

theorem th_coeff_linK (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1) (k : ℕ)
    (n : Zidx n' r0 r1 →₀ ℕ) :
    MvPowerSeries.coeff n (linK K' w P a b k) =
      ∑ s ∈ P, Aw K' w (s.val + k) * (if n = Finsupp.single (s, a, b) (p ^ k) then 1 else 0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linK, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow]

theorem th_reindex (w : WW p) (hper : (sigW p)^[n'] w = w) (P : Finset (Fin n'))
    (hPa : ∀ s ∈ P, ∀ d, posAdd s (2 * d) ∈ P) (hPs : ∀ s ∈ P, ∀ d, posSub s (2 * d) ∈ P)
    (a : Fin r0) (b : Fin r1) (n : Zidx n' r0 r1 →₀ ℕ) (l : ℕ) :
    (-1 : K') ^ l * ∑ s ∈ P, Aw K' w (s.val + 2 * l) *
        (if n = Finsupp.single (s, a, b) (p ^ (2 * l)) then 1 else 0) =
      ∑ t ∈ P, Aw K' w t.val *
        (if n = Finsupp.single (posSub t (2 * l), a, b) (p ^ (2 * l)) then (-1 : K') ^ l else 0) := by
  have hAw : ∀ s : Fin n', Aw K' w (posAdd s (2 * l)).val = Aw K' w (s.val + 2 * l) := by
    intro s
    simp only [Aw, posAdd]
    rw [Function.IsPeriodicPt.iterate_mod_apply hper]
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun t => posSub t (2 * l)) (fun s => posAdd s (2 * l)) (fun t ht => hPs t ht l)
    (fun s hs => hPa s hs l) (fun t _ => th_posAdd_posSub t _) (fun s _ => th_posSub_posAdd s _) (fun t _ => ?_)
  have h1 : Aw K' w t.val = Aw K' w ((posSub t (2 * l)).val + 2 * l) := by
    rw [← hAw, th_posAdd_posSub]
  rw [h1]
  split_ifs <;> ring

theorem th_claimM (hF : FrobSumH p n' r0 r1 K' (Rp p K' vp)) (hW : FrobWH p) (μ : PowerSeries K')
    (hT1 : ∀ n, ∃ y ∈ Rp p K' vp, PowerSeries.coeff n μ - PowerSeries.coeff n (altF K' p) = (p : K') * y)
    (w : WW p) (hper : (sigW p)^[n'] w = w) (P : Finset (Fin n'))
    (hPa : ∀ s ∈ P, ∀ d, posAdd s (2 * d) ∈ P) (hPs : ∀ s ∈ P, ∀ d, posSub s (2 * d) ∈ P)
    (a : Fin r0) (b : Fin r1) :
    Cg (Rp p K' vp) (p : K') (PowerSeries.subst (linK K' w P a b 0) μ)
      (∑ t ∈ P, MvPowerSeries.C (Aw K' w t.val) * sSer p K' t a b) := by
  have hL0 := th_linK_const (K' := K') w P a b
  have hsL : PowerSeries.HasSubst (linK K' w P a b 0) := PowerSeries.HasSubst.of_constantCoeff_zero hL0

  have h1 : Cg (Rp p K' vp) (p : K') (PowerSeries.subst (linK K' w P a b 0) μ)
      (PowerSeries.subst (linK K' w P a b 0) (altF K' p)) := by
    choose y hy he using hT1
    have e : μ = altF K' p + PowerSeries.C (p : K') * PowerSeries.mk y := by
      ext n
      rw [map_add (f := _), PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← he n]
      ring
    refine ⟨PowerSeries.subst (linK K' w P a b 0) (PowerSeries.mk y),
      IntR_psubst hL0 (th_linK_int vp w P a b 0) (fun n => by rw [PowerSeries.coeff_mk]; exact hy n), ?_⟩
    conv_lhs => rw [e]
    rw [PowerSeries.subst_add hsL, PowerSeries.subst_mul hsL, PowerSeries.subst_C]
  refine cg_trans h1 (cg_of_coeff fun n => ?_)
  rw [Formalism.InvariantFactorPaths.G7.TwoS.coeff_subst_altF hp.out.two_le hL0 n]
  choose y hy he using fun l => cg_coeff (th_claimF vp hF hW w P a b (2 * l)) n
  refine ⟨∑ l ∈ range (n.degree + 1), (-1 : K') ^ l * y l,
    Subring.sum_mem _ fun l _ => (Rp p K' vp).mul_mem ((Rp p K' vp).pow_mem ((Rp p K' vp).neg_mem
      (Rp p K' vp).one_mem) l) (hy l), ?_⟩
  have e2 : MvPowerSeries.coeff n (∑ t ∈ P, MvPowerSeries.C (Aw K' w t.val) * sSer p K' t a b) =
      ∑ l ∈ range (n.degree + 1), (-1 : K') ^ l * MvPowerSeries.coeff n (linK K' w P a b (2 * l)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [MvPowerSeries.coeff_C_mul, th_coeff_linK, th_reindex w hper P hPa hPs a b n]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]
    rfl
  rw [e2, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← pow_mul, he l]
  ring

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lamF altF)

def MuAltH (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∀ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X →
      ∀ n, ∃ y ∈ Rp p K' vp, PowerSeries.coeff n μ - PowerSeries.coeff n (altF K' p) = (p : K') * y

def DualH (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n' : ℕ) (B : OmBasis p n'), Even n' → ∀ a b : Fin n', a.val % 2 = b.val % 2 →
    ∑ r, (sigW p)^[a.val] (B.omS r) * (sigW p)^[b.val] (B.om r) = if a = b then 1 else 0

variable {p : ℕ} [hp : Fact p.Prime] {n' r0 r1 : ℕ} {K' : Type} [Field K'] [Algebra (K0 p) K']

theorem triple_sum_comm {α β γ M : Type} [AddCommMonoid M] [Fintype β] [Fintype γ] (s : Finset α) (f : α → β → γ → M) :
    ∑ x ∈ s, ∑ a, ∑ b, f x a b = ∑ a, ∑ b, ∑ x ∈ s, f x a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem th_sSer_int (R : Subring K') (t : Fin n') (a : Fin r0) (b : Fin r1) : IntR R (sSer p K' t a b) := by
  intro n
  show (∑ l ∈ range (n.degree + 1),
    if n = Finsupp.single (posSub t (2 * l), a, b) (p ^ (2 * l)) then ((-1 : K') ^ l) else 0) ∈ R
  refine Subring.sum_mem _ fun l _ => ?_
  split_ifs
  · exact R.pow_mem (R.neg_mem R.one_mem) l
  · exact R.zero_mem


set_option maxHeartbeats 200000 in
theorem th_sumR {ν : ℕ} (w1 w2 : Fin ν → WW p) (P Q : Finset (Fin n'))
    (hQ : ∀ t' ∈ Q, posAdd t' 1 ∈ P)
    (hD : ∀ t ∈ P, ∀ t' ∈ Q, ∑ r, Aw K' (w1 r) t.val * Aw K' (w2 r) (t'.val + 1) = if t = posAdd t' 1 then 1 else 0)
    (S : Fin n' → MvPowerSeries (Zidx n' r0 r1) K') :
    ∑ r, (∑ t ∈ P, MvPowerSeries.C (Aw K' (w1 r) t.val) * S t) *
        (∑ t' ∈ Q, MvPowerSeries.C (Aw K' (w2 r) (t'.val + 1)) * S t' ^ p) =
      ∑ t' ∈ Q, S t' ^ p * S (posAdd t' 1) := by
  have key : ∀ t' ∈ Q, ∑ t ∈ P, ∑ r, MvPowerSeries.C (Aw K' (w1 r) t.val) * S t *
      (MvPowerSeries.C (Aw K' (w2 r) (t'.val + 1)) * S t' ^ p) = S t' ^ p * S (posAdd t' 1) := by
    intro t' ht'
    have e : ∀ t ∈ P, ∑ r, MvPowerSeries.C (Aw K' (w1 r) t.val) * S t *
        (MvPowerSeries.C (Aw K' (w2 r) (t'.val + 1)) * S t' ^ p) =
        if t = posAdd t' 1 then S t' ^ p * S t else 0 := by
      intro t ht
      have h1 : ∀ r, MvPowerSeries.C (Aw K' (w1 r) t.val) * S t *
          (MvPowerSeries.C (Aw K' (w2 r) (t'.val + 1)) * S t' ^ p) =
          MvPowerSeries.C (Aw K' (w1 r) t.val * Aw K' (w2 r) (t'.val + 1)) * (S t' ^ p * S t) := by
        intro r
        rw [map_mul]
        ring
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl (fun r _ => h1 r), ← Finset.sum_mul, ← map_sum, hD t ht t' ht']
      split_ifs <;> simp
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' P (posAdd t' 1), if_pos (hQ t' ht')]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_comm]
  exact Finset.sum_congr rfl key

abbrev Pev (n' : ℕ) : Finset (Fin n') := univ.filter fun s : Fin n' => ¬ IsOddPos s

abbrev Pod (n' : ℕ) : Finset (Fin n') := univ.filter fun s : Fin n' => IsOddPos s

theorem th_par_add (hev : Even n') (s : Fin n') (d : ℕ) : IsOddPos (posAdd s (2 * d)) ↔ IsOddPos s := by
  show (s.val + 2 * d) % n' % 2 = 1 ↔ s.val % 2 = 1
  rw [Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hev)]
  omega

theorem th_par_sub (hev : Even n') (s : Fin n') (d : ℕ) : IsOddPos (posSub s (2 * d)) ↔ IsOddPos s := by
  show (s.val + n' * (2 * d) - 2 * d) % n' % 2 = 1 ↔ s.val % 2 = 1
  rw [Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hev)]
  have h2 : 2 * d ≤ n' * (2 * d) := Nat.le_mul_of_pos_left _ s.pos
  have h3 : n' * (2 * d) % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (dvd_mul_right 2 d) n')
  generalize n' * (2 * d) = m at h2 h3
  omega

theorem th_par_one (hev : Even n') (s : Fin n') : IsOddPos (posAdd s 1) ↔ ¬ IsOddPos s := by
  show (s.val + 1) % n' % 2 = 1 ↔ ¬ s.val % 2 = 1
  rw [Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hev)]
  omega

theorem th_coordZ_inl (B : OmBasis p n') (r : Fin (n' / 2)) (a : Fin r0) (b : Fin r1) :
    coordZ B K' 1 (Sum.inl (r, a, b)) = linK K' (B.omS r) (Pev n') a b 0 := by
  simp only [coordZ, linK, Aw, wK', one_mul, add_zero, pow_zero, pow_one]

theorem th_coordZ_inr (B : OmBasis p n') (r : Fin (n' / 2)) (a : Fin r0) (b : Fin r1) :
    coordZ B K' 1 (Sum.inr (r, a, b)) = linK K' (B.om r) (Pod n') a b 0 := by
  simp only [coordZ, linK, Aw, wK', one_mul, add_zero, pow_zero, pow_one]

theorem th_dual_K (hT2 : DualH p) (hev : Even n') (B : OmBasis p n') (a b : Fin n') (hab : a.val % 2 = b.val % 2) :
    ∑ r, Aw K' (B.omS r) a.val * Aw K' (B.om r) b.val = if a = b then 1 else 0 := by
  have := congrArg (wK' p K') (hT2 n' B hev a b hab)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [wK', map_sum, map_mul] at this
  rw [apply_ite (algebraMap (WW p) (K0 p)), apply_ite (algebraMap (K0 p) K')] at this
  simpa [Aw, wK'] using this

theorem th_Aw_posAdd {w : WW p} (hper : (sigW p)^[n'] w = w) (s : Fin n') (d : ℕ) :
    Aw K' w (posAdd s d).val = Aw K' w (s.val + d) := by
  unfold Aw
  congr 1
  exact Function.IsPeriodicPt.iterate_mod_apply hper _

private theorem intR_C_of_mem {ι F : Type} [Field F] (R : Subring F) {c : F} (hc : c ∈ R) :
    IntR R (MvPowerSeries.C c : MvPowerSeries ι F) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · exact R.zero_mem

private theorem intR_add' {ι F : Type} [Field F] (R : Subring F) {f g : MvPowerSeries ι F}
    (hf : IntR R f) (hg : IntR R g) : IntR R (f + g) := by
  intro n
  rw [map_add (f := _)]
  exact R.add_mem (hf n) (hg n)

private theorem intR_mul' {ι F : Type} [Field F] (R : Subring F) {f g : MvPowerSeries ι F}
    (hf : IntR R f) (hg : IntR R g) : IntR R (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact R.sum_mem fun x _ => R.mul_mem (hf _) (hg _)

private theorem intR_pow {ι F : Type} [Field F] (R : Subring F) {f : MvPowerSeries ι F}
    (hf : IntR R f) (k : ℕ) : IntR R (f ^ k) := by
  induction k with
  | zero =>
    classical
    intro n
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  | succ k ih =>
    rw [pow_succ]
    exact intR_mul' R ih hf

private theorem intR_sum' {ι F α : Type} [Field F] (R : Subring F) (s : Finset α)
    (f : α → MvPowerSeries ι F) (h : ∀ i ∈ s, IntR R (f i)) : IntR R (∑ i ∈ s, f i) := by
  intro n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact R.sum_mem fun i hi => h i hi n

private theorem cg_of_eq' {ι F : Type} [Field F] (R : Subring F) (pp : F)
    {f g : MvPowerSeries ι F} (h : f = g) : Cg R pp f g :=
  ⟨0, fun n => by rw [map_zero]; exact R.zero_mem, by rw [h, mul_zero, add_zero]⟩

private theorem cg_sub_multiset_valuation {ι F : Type} [Field F] (R : Subring F) (pp : F)
    {f g f' g' : MvPowerSeries ι F} (h : Cg R pp f g) (h' : Cg R pp f' g') :
    Cg R pp (f - f') (g - g') := by
  obtain ⟨Y, hY, rfl⟩ := h
  obtain ⟨Y', hY', rfl⟩ := h'
  refine ⟨Y - Y', fun n => ?_, by ring⟩
  rw [map_sub]
  exact R.sub_mem (hY n) (hY' n)

private theorem cg_trans' {ι F : Type} [Field F] (R : Subring F) (pp : F)
    {f g k : MvPowerSeries ι F} (h : Cg R pp f g) (h' : Cg R pp g k) : Cg R pp f k := by
  obtain ⟨Y, hY, rfl⟩ := h
  obtain ⟨Y', hY', rfl⟩ := h'
  exact ⟨Y' + Y, intR_add' R hY' hY, by ring⟩

private theorem cg_mul' {ι F : Type} [Field F] (R : Subring F) (pp : F) (hpp : pp ∈ R)
    {f g f' g' : MvPowerSeries ι F} (h : Cg R pp f g) (h' : Cg R pp f' g')
    (hg : IntR R g) (hf' : IntR R f') : Cg R pp (f * f') (g * g') := by
  obtain ⟨Y, hY, rfl⟩ := h
  obtain ⟨Y', hY', rfl⟩ := h'
  exact ⟨g * Y' + Y * (g' + MvPowerSeries.C pp * Y'),
    intR_add' R (intR_mul' R hg hY') (intR_mul' R hY hf'), by ring⟩

private theorem cg_pow' {ι F : Type} [Field F] (R : Subring F) (pp : F) (hpp : pp ∈ R)
    {f g : MvPowerSeries ι F} (h : Cg R pp f g) (hf : IntR R f) (hg : IntR R g) (k : ℕ) :
    Cg R pp (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact cg_of_eq' R pp (by rw [pow_zero, pow_zero])
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact cg_mul' R pp hpp ih h (intR_pow R hg k) hf

private theorem cg_sum' {ι F α : Type} [Field F] (R : Subring F) (pp : F) (s : Finset α)
    {f g : α → MvPowerSeries ι F} (h : ∀ i, Cg R pp (f i) (g i)) :
    Cg R pp (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  choose Y hY heq using h
  exact ⟨∑ i ∈ s, Y i, intR_sum' R s Y (fun i _ => hY i), by
    rw [Finset.sum_congr rfl (fun i _ => heq i), Finset.sum_add_distrib, Finset.mul_sum]⟩

private theorem cg_C_mul' {ι F : Type} [Field F] (R : Subring F) (pp : F) {c : F} (hc : c ∈ R)
    {f g : MvPowerSeries ι F} (h : Cg R pp f g) :
    Cg R pp (MvPowerSeries.C c * f) (MvPowerSeries.C c * g) := by
  obtain ⟨Y, hY, rfl⟩ := h
  exact ⟨MvPowerSeries.C c * Y, intR_mul' R (intR_C_of_mem R hc) hY, by ring⟩

private theorem intR_of_cg_of_intR {ι F : Type} [Field F] (R : Subring F) (pp : F) (hpp : pp ∈ R)
    {f g : MvPowerSeries ι F} (h : Cg R pp f g) (hg : IntR R g) : IntR R f := by
  obtain ⟨Y, hY, rfl⟩ := h
  exact intR_add' R hg (intR_mul' R (intR_C_of_mem R hpp) hY)

theorem restTwoSums_of (hT1 : MuAltH p) (hT2 : DualH p)
    (hF : ∀ (n' r0 r1 : ℕ) (K' : Type) [Field K'] (R : Subring K'), FrobSumH p n' r0 r1 K' R) (hW : FrobWH p) :
    TwoSumsCondition p := by
  intro hp5 c hc n r0 r1 h2 hev B L _ _ vp hvp μ hμ0 hμ
  have hpR : (p : L) ∈ Rp p L vp := natCast_mem (Rp p L vp) p
  have hFS := hF n r0 r1 L (Rp p L vp)
  have hM := hT1 L vp hvp μ hμ0 hμ
  have hc0 : wK' p L c ∈ Rp p L vp := th_Aw_mem vp c 0
  have hc1 : wK' p L (sigW p c) ∈ Rp p L vp := th_Aw_mem vp c 1
  have hsI : ∀ (t : Fin n) (a : Fin r0) (b : Fin r1), IntR (Rp p L vp) (sSer p L t a b) :=
    fun t a b => th_sSer_int _ t a b
  have hLin0 : ∀ (w : WW p) (P : Finset (Fin n)) (e : Fin n → ℕ) (a : Fin r0) (b : Fin r1),
      IntR (Rp p L vp) (∑ t ∈ P, MvPowerSeries.C (Aw L w (e t)) * sSer p L t a b) :=
    fun w P e a b => intR_sum' _ P _ fun t _ =>
      intR_mul' _ (intR_C_of_mem _ (th_Aw_mem vp w _)) (hsI t a b)
  have hEv1 : ∀ s ∈ Pev n, ∀ d, posAdd s (2 * d) ∈ Pev n := by
    intro s hs d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rwa [th_par_add hev]
  have hEv2 : ∀ s ∈ Pev n, ∀ d, posSub s (2 * d) ∈ Pev n := by
    intro s hs d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rwa [th_par_sub hev]
  have hOd1 : ∀ s ∈ Pod n, ∀ d, posAdd s (2 * d) ∈ Pod n := by
    intro s hs d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rwa [th_par_add hev]
  have hOd2 : ∀ s ∈ Pod n, ∀ d, posSub s (2 * d) ∈ Pod n := by
    intro s hs d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rwa [th_par_sub hev]
  have hX : ∀ (r : Fin (n / 2)) (a : Fin r0) (b : Fin r1),
      Cg (Rp p L vp) (p : L) (sOf B L μ (Sum.inl (r, a, b)))
        (∑ t ∈ Pev n, MvPowerSeries.C (Aw L (B.omS r) t.val) * sSer p L t a b) := by
    intro r a b
    have h := th_claimM vp hFS hW μ hM (B.omS r) (B.fixS r) (Pev n) hEv1 hEv2 a b
    rw [← th_coordZ_inl] at h
    exact h
  have hZ : ∀ (r : Fin (n / 2)) (a : Fin r0) (b : Fin r1),
      Cg (Rp p L vp) (p : L) (sOf B L μ (Sum.inr (r, a, b)))
        (∑ t ∈ Pod n, MvPowerSeries.C (Aw L (B.om r) t.val) * sSer p L t a b) := by
    intro r a b
    have h := th_claimM vp hFS hW μ hM (B.om r) (B.fix r) (Pod n) hOd1 hOd2 a b
    rw [← th_coordZ_inr] at h
    exact h
  have hT1' : ∀ (r : Fin (n / 2)) (a : Fin r0) (b : Fin r1),
      Cg (Rp p L vp) (p : L)
        (MvPowerSeries.C (wK' p L c) * (sOf B L μ (Sum.inl (r, a, b)) * sOf B L μ (Sum.inr (r, a, b)) ^ p))
        (MvPowerSeries.C (wK' p L c) *
          ((∑ t ∈ Pev n, MvPowerSeries.C (Aw L (B.omS r) t.val) * sSer p L t a b) *
            (∑ t ∈ Pod n, MvPowerSeries.C (Aw L (B.om r) (t.val + 1)) * sSer p L t a b ^ p))) := by
    intro r a b
    have hZi : IntR (Rp p L vp) (sOf B L μ (Sum.inr (r, a, b))) :=
      intR_of_cg_of_intR _ _ hpR (hZ r a b) (hLin0 (B.om r) (Pod n) (fun t => t.val) a b)
    have hZp := cg_pow' _ _ hpR (hZ r a b) hZi (hLin0 (B.om r) (Pod n) (fun t => t.val) a b) p
    have hF1 := th_frob_lin vp hFS hW (B.om r) (Pod n) (fun t => t.val) (fun t => sSer p L t a b)
      (fun t => hsI t a b)
    have hZB := cg_trans' _ _ hZp hF1
    have hXZ := cg_mul' _ _ hpR (hX r a b) hZB
      (hLin0 (B.omS r) (Pev n) (fun t => t.val) a b) (intR_pow _ hZi p)
    exact cg_C_mul' _ _ hc0 hXZ
  have hT2' : ∀ (r : Fin (n / 2)) (a : Fin r0) (b : Fin r1),
      Cg (Rp p L vp) (p : L)
        (MvPowerSeries.C (wK' p L (sigW p c)) *
          (sOf B L μ (Sum.inr (r, a, b)) * sOf B L μ (Sum.inl (r, a, b)) ^ p))
        (MvPowerSeries.C (wK' p L (sigW p c)) *
          ((∑ t ∈ Pod n, MvPowerSeries.C (Aw L (B.om r) t.val) * sSer p L t a b) *
            (∑ t ∈ Pev n, MvPowerSeries.C (Aw L (B.omS r) (t.val + 1)) * sSer p L t a b ^ p))) := by
    intro r a b
    have hXi : IntR (Rp p L vp) (sOf B L μ (Sum.inl (r, a, b))) :=
      intR_of_cg_of_intR _ _ hpR (hX r a b) (hLin0 (B.omS r) (Pev n) (fun t => t.val) a b)
    have hXp := cg_pow' _ _ hpR (hX r a b) hXi (hLin0 (B.omS r) (Pev n) (fun t => t.val) a b) p
    have hF2 := th_frob_lin vp hFS hW (B.omS r) (Pev n) (fun t => t.val) (fun t => sSer p L t a b)
      (fun t => hsI t a b)
    have hXA := cg_trans' _ _ hXp hF2
    have hZX := cg_mul' _ _ hpR (hZ r a b) hXA
      (hLin0 (B.om r) (Pod n) (fun t => t.val) a b) (intR_pow _ hXi p)
    exact cg_C_mul' _ _ hc1 hZX
  have hAll := cg_sum' _ _ (Finset.univ : Finset (Eidx n r0 r1))
    fun e : Eidx n r0 r1 => cg_sub_multiset_valuation _ _ (hT1' e.1 e.2.1 e.2.2) (hT2' e.1 e.2.1 e.2.2)
  obtain ⟨Y, hY, heq⟩ := hAll
  obtain ⟨u, hu_def⟩ : ∃ u : Fin n → L,
      u = fun s => if IsOddPos s then wK' p L c else -wK' p L (sigW p c) := ⟨_, rfl⟩
  have hu : ∀ s, u s ∈ Rp p L vp := by
    intro s
    rw [hu_def]
    dsimp only
    split_ifs
    · exact hc0
    · exact (Rp p L vp).neg_mem hc1
  refine ⟨u, hu, Y, hY, ?_⟩
  refine heq.trans ?_
  congr 1
  have hR : (hhS p L u : MvPowerSeries (Zidx n r0 r1) L) = ∑ a : Fin r0, ∑ b : Fin r1, ∑ s : Fin n,
      MvPowerSeries.C (u s) * (sSer p L s a b ^ p * sSer p L (posAdd s 1) a b) := by
    unfold hhS
    simp only [Finset.mul_sum]
    exact triple_sum_comm _ _
  have hQ1 : ∀ t' ∈ Pod n, posAdd t' 1 ∈ Pev n := by
    intro t' ht'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht' ⊢
    rw [th_par_one hev]
    exact not_not.mpr ht'
  have hQ2 : ∀ t' ∈ Pev n, posAdd t' 1 ∈ Pod n := by
    intro t' ht'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht' ⊢
    rw [th_par_one hev]
    exact ht'
  have hD1 : ∀ t ∈ Pev n, ∀ t' ∈ Pod n,
      ∑ r, Aw L (B.omS r) t.val * Aw L (B.om r) (t'.val + 1) = if t = posAdd t' 1 then 1 else 0 := by
    intro t ht t' ht'
    have hpar : t.val % 2 = (posAdd t' 1).val % 2 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsOddPos] at ht ht'
      rw [th_odd_posAdd hev]
      omega
    rw [← th_dual_K (K' := L) hT2 hev B t (posAdd t' 1) hpar]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [th_Aw_posAdd (K' := L) (B.fix r)]
  have hD2 : ∀ t ∈ Pod n, ∀ t' ∈ Pev n,
      ∑ r, Aw L (B.om r) t.val * Aw L (B.omS r) (t'.val + 1) = if t = posAdd t' 1 then 1 else 0 := by
    intro t ht t' ht'
    have hpar : (posAdd t' 1).val % 2 = t.val % 2 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsOddPos] at ht ht'
      rw [th_odd_posAdd hev]
      omega
    have h := th_dual_K (K' := L) hT2 hev B (posAdd t' 1) t hpar
    calc ∑ r, Aw L (B.om r) t.val * Aw L (B.omS r) (t'.val + 1)
        = ∑ r, Aw L (B.omS r) (posAdd t' 1).val * Aw L (B.om r) t.val := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [th_Aw_posAdd (K' := L) (B.fixS r), mul_comm]
      _ = if posAdd t' 1 = t then 1 else 0 := h
      _ = if t = posAdd t' 1 then 1 else 0 := by
          by_cases h1 : t = posAdd t' 1
          · rw [if_pos h1, if_pos h1.symm]
          · rw [if_neg h1, if_neg (Ne.symm h1)]
  rw [hR]
  simp only [Fintype.sum_prod_type]
  rw [triple_sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e1 := th_sumR (B.omS) (B.om) (Pev n) (Pod n) hQ1 hD1 (fun t => sSer p L t a b)
  have e2 := th_sumR (B.om) (B.omS) (Pod n) (Pev n) hQ2 hD2 (fun t => sSer p L t a b)
  beta_reduce at e1 e2
  rw [e1, e2]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => IsOddPos s)
    (fun s => MvPowerSeries.C (u s) * (sSer p L s a b ^ p * sSer p L (posAdd s 1) a b))]
  rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [hu_def]
    dsimp only
    rw [if_pos (Finset.mem_filter.mp hs).2]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [hu_def]
    dsimp only
    rw [if_neg (Finset.mem_filter.mp hs).2, map_neg, neg_mul]

end Formalism.MainNotions.FormalGroupSystem.Pf
