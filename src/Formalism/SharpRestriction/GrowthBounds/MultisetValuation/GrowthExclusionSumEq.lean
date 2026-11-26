module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrimeCastNeZero

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcIotaInj
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcCGNonneg
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LambdaIndexTwo
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcSummableMin
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem nc_geom (p : ℕ) (hp : 2 ≤ p) :
    HasSum (fun e : ℕ => (((p : ℝ)) ^ (2 * e + 1))⁻¹) (Formalism.MainNotions.FormalGroupSystem.gam p) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hq : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hr : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have h0 : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
  have := (hasSum_geometric_of_lt_one h0 hr).mul_left ((p : ℝ)⁻¹)
  have e1 : (fun e : ℕ => ((p : ℝ) ^ (2 * e + 1))⁻¹) = fun i : ℕ => (p : ℝ)⁻¹ * ((p : ℝ) ^ 2)⁻¹ ^ i := by
    funext e
    rw [pow_succ, pow_mul, mul_inv, inv_pow]
    ring
  have e2 : Formalism.MainNotions.FormalGroupSystem.gam p = (p : ℝ)⁻¹ * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
    rw [Formalism.MainNotions.FormalGroupSystem.gam]
    first
      | (field_simp; ring)
      | field_simp
  rw [e1, e2]
  exact this

theorem nc_geomc (p : ℕ) (hp : 2 ≤ p) (c : ℝ) :
    HasSum (fun e : ℕ => c / ((p : ℝ)) ^ (2 * e + 1)) (c * Formalism.MainNotions.FormalGroupSystem.gam p) := by
  have := (nc_geom p hp).mul_left c
  simpa [div_eq_mul_inv] using this

theorem nc_abs_min_le (a b : ℝ) (hb : 0 ≤ b) : |min a b| ≤ |a| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, abs_of_nonneg hb, abs_of_nonneg (hb.trans h)]
    exact h

theorem nc_summable_min (p : ℕ) (hp : 2 ≤ p) (y : ℝ) (z : ℕ → ℝ) (hz : ∀ e, 0 ≤ z e) :
    Summable fun e : ℕ => min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e) := by
  have hg : Summable (fun e : ℕ => |y| / ((p : ℝ)) ^ (2 * e + 1)) := (nc_geomc p hp |y|).summable
  have hb : ∀ e : ℕ, ‖min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e)‖ ≤ |y| / ((p : ℝ)) ^ (2 * e + 1) := by
    intro e
    have hq : (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
      positivity
    rw [Real.norm_eq_abs]
    calc |min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e)| ≤ |y / ((p : ℝ)) ^ (2 * e + 1)| := nc_abs_min_le _ _ (hz e)
      _ = |y| / ((p : ℝ)) ^ (2 * e + 1) := by rw [abs_div, abs_of_pos hq]
  first
    | exact Summable.of_norm_bounded hg hb
    | exact Summable.of_norm_bounded _ hg hb

theorem nc_min (p : ℕ) (hp : 2 ≤ p) (y yu : ℝ) (z zu : ℕ → ℝ) (hy : y ≤ yu) (hz : ∀ e, zu e ≤ z e)
    (hz0 : ∀ e, 0 ≤ zu e) :
    Formalism.MainNotions.FormalGroupSystem.gam p * y - ∑' e : ℕ, min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e) ≤
      Formalism.MainNotions.FormalGroupSystem.gam p * yu - ∑' e : ℕ, min (yu / ((p : ℝ)) ^ (2 * e + 1)) (zu e) := by
  have hs1 := nc_geomc p hp y
  have hs2 := nc_geomc p hp yu
  have m1 := nc_summable_min p hp y z (fun e => (hz0 e).trans (hz e))
  have m2 := nc_summable_min p hp yu zu hz0
  rw [mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p) y, mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p) yu, ← hs1.tsum_eq, ← hs2.tsum_eq]
  rw [← hs1.summable.tsum_sub m1, ← hs2.summable.tsum_sub m2]
  refine (hs1.summable.sub m1).tsum_le_tsum (fun e => ?_) (hs2.summable.sub m2)
  have hq : (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    positivity
  have ha : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy hq.le
  have hze := hz e
  simp only [Pi.sub_apply, min_def]
  split_ifs <;> linarith

theorem nc_pos (p : ℕ) (hp : 2 ≤ p) (y yu : ℝ) (z zu : ℕ → ℝ) (ex exu : ℕ → Prop) [DecidablePred ex]
    [DecidablePred exu] (hy : y ≤ yu) (hyu : 0 ≤ yu) (hz : ∀ e, zu e ≤ z e) (hz0 : ∀ e, 0 ≤ zu e)
    (hex : ∀ e, exu e → ex e) :
    ∑' e : ℕ, (if ex e then 0 else max 0 (y / ((p : ℝ)) ^ (2 * e + 1) - z e)) ≤
      ∑' e : ℕ, (if exu e then 0 else max (yu / ((p : ℝ)) ^ (2 * e + 1) - zu e) 0) := by
  have hq : ∀ e : ℕ, (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
    intro e
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    positivity
  have hS := (nc_geomc p hp yu).summable
  have hR : Summable (fun e : ℕ => if exu e then 0 else max (yu / ((p : ℝ)) ^ (2 * e + 1) - zu e) 0) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hS
    · split_ifs
      · exact le_rfl
      · exact le_max_right _ _
    · have h1 : 0 ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_nonneg hyu (hq e).le
      have h2 := hz0 e
      split_ifs
      · exact h1
      · exact max_le (by linarith) h1
  have hLs : Summable (fun e : ℕ => if ex e then 0 else max 0 (y / ((p : ℝ)) ^ (2 * e + 1) - z e)) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hS
    · split_ifs
      · exact le_rfl
      · exact le_max_left _ _
    · have h1 : 0 ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_nonneg hyu (hq e).le
      have h3 : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy (hq e).le
      have h2 := hz0 e
      have h4 := hz e
      split_ifs
      · exact h1
      · exact max_le h1 (by linarith)
  refine hLs.tsum_le_tsum (fun e => ?_) hR
  have h3 : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy (hq e).le
  have h4 := hz e
  by_cases he : ex e
  · rw [if_pos he]
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  · have heu : ¬ exu e := fun h => he (hex e h)
    rw [if_neg he, if_neg heu]
    exact max_le (le_max_right _ _) (le_trans (by linarith) (le_max_left _ _))

variable {n' k1 : ℕ}

theorem nc_gB_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (ya zc : Fin n' → ℝ) (dlv : ℝ) (h1 : ∀ s ∈ TT, ya s ≤ al TT lam0 s)
    (h2 : ∀ s, (cap t TT lam0 w j s : ℝ) ≤ zc s) (h3 : ∀ s, 0 ≤ cap t TT lam0 w j s)
    (hd : de p t TT lam0 w j ≤ dlv) :
    Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ TT, ya s -
              ∑ s ∈ TT.filter IsOddPos, ∑' e : ℕ,
                min (ya s / ((p : ℝ)) ^ (2 * e + 1)) (zc (Formalism.MainNotions.G.posAdd s (2 * e + 1))) - dlv ≤
      gB p t TT lam0 w j := by
  unfold gB
  have hg0 : 0 ≤ Formalism.MainNotions.FormalGroupSystem.gam p := (nc_geom p hp).nonneg fun e => by positivity
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not TT IsOddPos,
    ← Finset.sum_filter_add_sum_filter_not TT IsOddPos (fun s => Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ))]
  have hA : ∑ s ∈ TT.filter IsOddPos, (Formalism.MainNotions.FormalGroupSystem.gam p * ya s - ∑' e : ℕ,
        min (ya s / ((p : ℝ)) ^ (2 * e + 1)) (zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) ≤
      ∑ s ∈ TT.filter IsOddPos, (Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ) - ∑' e : ℕ,
        min ((al TT lam0 s : ℝ) / ((p : ℝ)) ^ (2 * e + 1)) (cap t TT lam0 w j (Formalism.MainNotions.G.posAdd s (2 * e + 1)) : ℝ)) := by
    apply Finset.sum_le_sum
    intro s hs
    exact nc_min p hp _ _ _ _ (h1 s (Finset.mem_filter.1 hs).1) (fun e => h2 _) (fun e => by exact_mod_cast h3 _)
  have hB : ∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), Formalism.MainNotions.FormalGroupSystem.gam p * ya s ≤
      ∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ) := by
    apply Finset.sum_le_sum
    intro s hs
    exact mul_le_mul_of_nonneg_left (h1 s (Finset.mem_filter.1 hs).1) hg0
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hA
  linarith

theorem nc_gA_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (ya zc : Fin n' → ℝ) (dlv : ℝ) (ex : Fin n' → ℕ → Prop) [∀ s, DecidablePred (ex s)]
    (h1 : ∀ s ∈ TT, ya s ≤ al TT lam0 s) (h0 : ∀ s, 0 ≤ al TT lam0 s)
    (h2 : ∀ s, (cap t TT lam0 w j s : ℝ) ≤ zc s) (h3 : ∀ s, 0 ≤ cap t TT lam0 w j s)
    (hex : ∀ s ∈ TT, ∀ e, 2 * e + 1 ∈ dSet TT s → ex s e)
    (hd : de p t TT lam0 w j ≤ dlv) :
    ∑ s ∈ TT, ∑' e : ℕ, (if ex s e then 0 else
        max 0 (ya s / ((p : ℝ)) ^ (2 * e + 1) - zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) - dlv ≤
      gA p t TT lam0 w j := by
  unfold gA
  have hA : ∑ s ∈ TT, ∑' e : ℕ, (if ex s e then 0 else
        max 0 (ya s / ((p : ℝ)) ^ (2 * e + 1) - zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) ≤
      ∑ s ∈ TT, ∑' e : ℕ, (if 2 * e + 1 ∈ dSet TT s then 0 else
        max ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1) -
          (cap t TT lam0 w j (Formalism.MainNotions.G.posAdd s (2 * e + 1)) : ℝ)) 0) := by
    apply Finset.sum_le_sum
    intro s hs
    exact nc_pos p hp _ _ _ _ (ex s) (fun e => 2 * e + 1 ∈ dSet TT s) (h1 s hs) (by exact_mod_cast h0 s)
      (fun e => h2 _) (fun e => by exact_mod_cast h3 _) (hex s hs)
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

def nc_ya (_X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : ℝ :=
  Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))

def nc_zc (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ)
    (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : ℝ :=
  Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) + Formalism.MainNotions.G.cG L


open Classical in
def nc_Loc (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts)
    (_hT : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  let p := D.what₂.places.resChar w
  let v := Y.vOf u w hg t0
  let Fl := Y.Fl u w hg
  Formalism.MainNotions.G.gU X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) p j t0 =
            Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s -
              ∑ s ∈ (Fl.TT v).filter IsOddPos, ∑' e : ℕ,
                min (nc_ya X Y u w hg t0 s / ((p : ℝ)) ^ (2 * e + 1)) (nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1))) -
              Formalism.MainNotions.G.dl X K p t0 ∧
  Formalism.MainNotions.G.g0 X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) p j t0 =
            ∑ s ∈ Fl.TT v, ∑' e : ℕ, (if Formalism.MainNotions.G.Excl D p (t0 + s.val • Formalism.MainNotions.G.hP D p) (2 * e + 1) then 0 else
              max 0 (nc_ya X Y u w hg t0 s / ((p : ℝ)) ^ (2 * e + 1) - nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) -
              Formalism.MainNotions.G.dl X K p t0 ∧
  (∀ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
  (∀ s, 0 ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
  (∀ s, (cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s : ℝ) ≤ nc_zc X Y u w hg t0 j s) ∧
  (∀ s, 0 ≤ cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s) ∧
  (∀ s ∈ Fl.TT v, ∀ e, 2 * e + 1 ∈ dSet (Fl.TT v) s → Formalism.MainNotions.G.Excl D p (t0 + s.val • Formalism.MainNotions.G.hP D p) (2 * e + 1))

def nc_De (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  de (D.what₂.places.resChar w) (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
      ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
    Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0

def nc_Need (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.dl1 → C₀ ≤ K.dl2 → C₀ ≤ K.Pr1 → (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        nc_Loc D L X Y K hT u w hg t0 j ∧ nc_De D L X Y K u w hg t0 j ∧
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

open Classical in
theorem stmtNumE_of (C₀ : ℝ) (h : nc_Need C₀) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform := by
  have two_le : ∀ (p : ℕ) (x : ℝ), 1 ≤ Real.logb (p : ℝ) x → 2 ≤ p := by
    intro p x hx
    by_contra hc
    have hp2 : p < 2 := by omega
    interval_cases p <;> simp [Real.logb] at hx <;> linarith
  have geom : ∀ p : ℕ, 2 ≤ p →
      HasSum (fun e : ℕ => 1 / (p : ℝ) ^ (2 * e + 1)) (Formalism.MainNotions.FormalGroupSystem.gam p) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    have hp0 : (0 : ℝ) < p := by linarith
    have hr0 : 0 ≤ (1 / (p : ℝ)) ^ 2 := by positivity
    have hr1 : (1 / (p : ℝ)) ^ 2 < 1 := by
      rw [div_pow, one_pow, div_lt_one (pow_pos hp0 2)]; nlinarith
    have hh := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 / (p : ℝ))
    have hf : (fun e : ℕ => 1 / (p : ℝ) ^ (2 * e + 1)) =
        fun i : ℕ => 1 / (p : ℝ) * ((1 / (p : ℝ)) ^ 2) ^ i := by
      funext e
      rw [← pow_mul, ← pow_succ', one_div_pow]
    have hv : Formalism.MainNotions.FormalGroupSystem.gam p = 1 / (p : ℝ) * (1 - (1 / (p : ℝ)) ^ 2)⁻¹ := by
      rw [show (1 : ℝ) - (1 / (p : ℝ)) ^ 2 = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 by
        rw [div_pow, one_pow, sub_div, div_self (pow_ne_zero 2 hp0.ne')], inv_div]
      unfold Formalism.MainNotions.FormalGroupSystem.gam
      rw [← mul_div_assoc, pow_two, ← mul_assoc, one_div_mul_cancel hp0.ne', one_mul]
    rw [hf, hv]
    exact hh
  have minsum : ∀ (p : ℕ), 2 ≤ p → ∀ (a b : ℝ) (C Z : ℕ → ℝ), b ≤ a → 0 ≤ a →
      (∀ e, 0 ≤ C e) → (∀ e, C e ≤ Z e) →
      ∑' e : ℕ, min (a / (p : ℝ) ^ (2 * e + 1)) (C e) -
        ∑' e : ℕ, min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) ≤ Formalism.MainNotions.FormalGroupSystem.gam p * (a - b) := by
    intro p hp a b C Z hba ha hC0 hCZ
    have hg := geom p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hq : ∀ e : ℕ, (0 : ℝ) < (p : ℝ) ^ (2 * e + 1) := fun e => pow_pos hp0 _
    have hsa : Summable (fun e : ℕ => a / (p : ℝ) ^ (2 * e + 1)) :=
      (hg.summable.mul_left a).congr (fun e => mul_one_div a _)
    have hsb : Summable (fun e : ℕ => b / (p : ℝ) ^ (2 * e + 1)) :=
      (hg.summable.mul_left b).congr (fun e => mul_one_div b _)
    have hf1 : Summable (fun e : ℕ => min (a / (p : ℝ) ^ (2 * e + 1)) (C e)) :=
      Summable.of_nonneg_of_le (fun e => le_min (div_nonneg ha (hq e).le) (hC0 e))
        (fun e => min_le_left _ _) hsa
    have hf2 : Summable (fun e : ℕ => min (b / (p : ℝ) ^ (2 * e + 1)) (Z e)) := by
      rcases le_or_gt 0 b with hb | hb
      · exact Summable.of_nonneg_of_le
          (fun e => le_min (div_nonneg hb (hq e).le) ((hC0 e).trans (hCZ e)))
          (fun e => min_le_left _ _) hsb
      · refine hsb.congr (fun e => ?_)
        have hneg : b / (p : ℝ) ^ (2 * e + 1) < 0 := div_neg_of_neg_of_pos hb (hq e)
        exact (min_eq_left (by linarith [hC0 e, hCZ e])).symm
    have hm := hg.mul_left (a - b)
    rw [mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p)]
    refine hasSum_le (fun e => ?_) (hf1.hasSum.sub hf2.hasSum) hm
    show min (a / (p : ℝ) ^ (2 * e + 1)) (C e) - min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) ≤
      (a - b) * (1 / (p : ℝ) ^ (2 * e + 1))
    have hbq : b / (p : ℝ) ^ (2 * e + 1) ≤ a / (p : ℝ) ^ (2 * e + 1) := by
      gcongr <;> exact hba
    have h1 : min (b / (p : ℝ) ^ (2 * e + 1)) (C e) ≤ min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) :=
      min_le_min_left _ (hCZ e)
    have h2 : min (a / (p : ℝ) ^ (2 * e + 1)) (C e) - min (b / (p : ℝ) ^ (2 * e + 1)) (C e) ≤
        a / (p : ℝ) ^ (2 * e + 1) - b / (p : ℝ) ^ (2 * e + 1) := by
      rcases le_total (b / (p : ℝ) ^ (2 * e + 1)) (C e) with hh | hh
      · rw [min_eq_left hh]; linarith [min_le_left (a / (p : ℝ) ^ (2 * e + 1)) (C e)]
      · rw [min_eq_right hh, min_eq_right (hh.trans hbq)]; linarith
    have h3 : a / (p : ℝ) ^ (2 * e + 1) - b / (p : ℝ) ^ (2 * e + 1) =
        (a - b) * (1 / (p : ℝ) ^ (2 * e + 1)) := by ring
    linarith
  have gBcmp : ∀ {n : ℕ} (p : ℕ), 2 ≤ p → ∀ (TT S1 S2 : Finset (Fin n)), S1 ⊆ TT → S2 = S1 →
      ∀ (A B : Fin n → ℝ) (C Z : Fin n → ℕ → ℝ) (dl de : ℝ),
      (∀ s ∈ TT, B s ≤ A s) → (∀ s, 0 ≤ A s) → (∀ s e, 0 ≤ C s e) → (∀ s e, C s e ≤ Z s e) →
      de ≤ dl →
      Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ TT, B s -
                ∑ s ∈ S1, ∑' e : ℕ, min (B s / (p : ℝ) ^ (2 * e + 1)) (Z s e) - dl ≤
        Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ TT, A s -
          ∑ s ∈ S2, ∑' e : ℕ, min (A s / (p : ℝ) ^ (2 * e + 1)) (C s e) - de := by
    intro n p hp TT S1 S2 hS hS21 A B C Z dl de hBA hA0 hC0 hCZ hde
    rw [hS21]
    have hg0 : 0 ≤ Formalism.MainNotions.FormalGroupSystem.gam p :=
      hasSum_le (fun e => div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg p) _))
        hasSum_zero (geom p hp)
    have key : ∑ s ∈ S1, (∑' e : ℕ, min (A s / (p : ℝ) ^ (2 * e + 1)) (C s e) -
        ∑' e : ℕ, min (B s / (p : ℝ) ^ (2 * e + 1)) (Z s e)) ≤
        ∑ s ∈ TT, Formalism.MainNotions.FormalGroupSystem.gam p * (A s - B s) :=
      (Finset.sum_le_sum (fun s hs => minsum p hp (A s) (B s) (C s) (Z s) (hBA s (hS hs))
        (hA0 s) (hC0 s) (hCZ s))).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hS
          (fun s hs _ => mul_nonneg hg0 (sub_nonneg.2 (hBA s hs))))
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, mul_sub] at key
    linarith
  have gAcmp : ∀ {n : ℕ} (p : ℕ), 2 ≤ p → ∀ (TT : Finset (Fin n)) (A B : Fin n → ℝ)
      (C Z : Fin n → ℕ → ℝ) (E F : Fin n → ℕ → Prop) (iE : ∀ s e, Decidable (E s e))
      (iF : ∀ s e, Decidable (F s e)) (dl de : ℝ),
      (∀ s ∈ TT, B s ≤ A s) → (∀ s, 0 ≤ A s) → (∀ s e, 0 ≤ C s e) → (∀ s e, C s e ≤ Z s e) →
      (∀ s ∈ TT, ∀ e, F s e → E s e) → de ≤ dl →
      ∑ s ∈ TT, ∑' e : ℕ, @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) -
          dl ≤
        ∑ s ∈ TT, ∑' e : ℕ, @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0) -
          de := by
    intro n p hp TT A B C Z E F iE iF dl de hBA hA0 hC0 hCZ hFE hde
    have hg := geom p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hq : ∀ e : ℕ, (0 : ℝ) < (p : ℝ) ^ (2 * e + 1) := fun e => pow_pos hp0 _
    have hsum : ∑ s ∈ TT, ∑' e : ℕ,
          @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) ≤
        ∑ s ∈ TT, ∑' e : ℕ,
          @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0) := by
      refine Finset.sum_le_sum (fun s hs => ?_)
      have hle : ∀ e : ℕ,
          @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) ≤
            @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0) := by
        intro e
        have hbq : B s / (p : ℝ) ^ (2 * e + 1) ≤ A s / (p : ℝ) ^ (2 * e + 1) := by
          gcongr <;> exact hBA s hs
        by_cases hF : F s e
        · simp only [if_pos (hFE s hs e hF), if_pos hF, le_refl]
        · rw [if_neg hF]
          split_ifs
          · exact le_max_right _ _
          · exact max_le (le_max_right _ _) (le_trans (by linarith [hCZ s e]) (le_max_left _ _))
      have h0 : ∀ e : ℕ,
          0 ≤ @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) := by
        intro e
        split_ifs
        · exact le_refl 0
        · exact le_max_left _ _
      have hR : Summable (fun e : ℕ =>
          @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0)) := by
        refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_)
          ((hg.summable.mul_left (A s)).congr (fun e => mul_one_div (A s) _))
        · split_ifs
          · exact le_refl 0
          · exact le_max_right _ _
        · split_ifs
          · exact div_nonneg (hA0 s) (hq e).le
          · exact max_le (by linarith [hC0 s e]) (div_nonneg (hA0 s) (hq e).le)
      exact hasSum_le hle (Summable.of_nonneg_of_le h0 hle hR).hasSum hR.hasSum
    linarith
  refine ⟨C₀, ?_⟩
  intro D L X Y K h1 h2 h3 hr hx hS hT hTied u w hg hlog t0 ht0 j hj
  obtain ⟨hLoc, hDe, hPr⟩ := h D L X Y K h1 h2 h3 ⟨hr, hx⟩ hS hT hTied u w hg hlog t0 ht0 j hj
  have hp := two_le _ _ hlog
  dsimp only [nc_Loc] at hLoc
  obtain ⟨hgU, hg0, hya, hal0, hcap, hcap0, hEx⟩ := hLoc
  refine ⟨?_, ?_, hPr⟩
  · rw [hgU]
    unfold Formalism.MainNotions.FormalGroupSystem.gB
    refine gBcmp _ hp _ _ _ ?_ ?_ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter] at hx
      exact hx.1
    · ext x
      simp only [Finset.mem_filter]
    · intro s hs
      exact hya s hs
    · intro s
      exact_mod_cast hal0 s
    · intro s e
      exact_mod_cast hcap0 _
    · intro s e
      exact hcap _
    · exact hDe
  · rw [hg0]
    unfold Formalism.MainNotions.FormalGroupSystem.gA
    refine gAcmp _ hp _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro s hs
      exact hya s hs
    · intro s
      exact_mod_cast hal0 s
    · intro s e
      exact_mod_cast hcap0 _
    · intro s e
      exact hcap _
    · intro s hs e he
      exact hEx s hs e he
    · exact hDe

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Local

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem lambda_index_one (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) : lamI (G.P.lam0 v) s 1 = G.P.lam0 v s ⟨0, by omega⟩ := by
  unfold lamI; rw [dite_eq_left ⟨le_rfl, by omega⟩]

theorem lambda_index_two (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) : lamI (G.P.lam0 v) s 2 = G.P.lam0 v s ⟨1, by omega⟩ := by
  unfold lamI; rw [dite_eq_left ⟨by omega, by omega⟩]

theorem nc_w_ge (s : Fin (G.P.n' v)) (j : ℕ) (hj : 1 ≤ j) : Fl.w v 1 s ≤ Fl.w v j s := by
  induction j, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ l hl ih => exact le_trans ih (Fl.w_mono v s l hl)

end Local

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nc_m_ge (hT : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : 2 ≤ (D.gat u w hg).P.m := by
  have h1 := hT.gat_k u w hg
  have h2 := D.R.m_add_three_le_k
  omega

theorem nc_cG_nonneg : 0 ≤ Formalism.MainNotions.G.cG L := by
  unfold Formalism.MainNotions.G.cG
  have h := L.Sc_pos
  linarith

private theorem liftWt_apply_of_lt_succ (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j i : ℕ)
    (hi : i < m + j * (t + 1) + 1) (h : i < m + 1) :
    Formalism.MainNotions.G.liftWt t m lam w j ⟨i, hi⟩ = lam ⟨i, h⟩ :=
  dif_pos h

private theorem lam_antitone_of_isDominant_liftWt {n' m : ℕ} (t : ℕ) (lam : Fin n' → Fin (m + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (hd : Formalism.MainNotions.G.IsDominant fun s => Formalism.MainNotions.G.liftWt t m (lam s) (fun i => w i s) 0)
    (s : Fin n') (i i' : ℕ) (hi : i < m + 1) (hi' : i' < m + 1) (hii : i ≤ i') :
    lam s ⟨i', hi'⟩ ≤ lam s ⟨i, hi⟩ := by
  unfold Formalism.MainNotions.G.IsDominant at hd
  have h1 := hd s (show (⟨i, by omega⟩ : Fin (m + 0 * (t + 1) + 1)) ≤ ⟨i', by omega⟩ from
    Fin.mk_le_mk.mpr hii)
  calc lam s ⟨i', hi'⟩ = Formalism.MainNotions.G.liftWt t m (lam s) (fun j => w j s) 0 ⟨i', by omega⟩ :=
        (liftWt_apply_of_lt_succ t m (lam s) (fun j => w j s) 0 i' (by omega) hi').symm
    _ ≤ Formalism.MainNotions.G.liftWt t m (lam s) (fun j => w j s) 0 ⟨i, by omega⟩ := h1
    _ = lam s ⟨i, hi⟩ := liftWt_apply_of_lt_succ t m (lam s) (fun j => w j s) 0 i (by omega) hi

private theorem lamI_one_eq_lam0_zero {n' k1 : ℕ} (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n') :
    Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 1 = lam0 s ⟨0, by omega⟩ :=
  dif_pos (show 1 ≤ 1 ∧ 1 ≤ k1 + 1 from ⟨le_refl 1, by omega⟩)

private theorem lamI_two_eq_lam0_one {n' k1 : ℕ} (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n')
    (hk : 1 ≤ k1) : Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 2 = lam0 s ⟨1, by omega⟩ :=
  dif_pos (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 from ⟨by omega, by omega⟩)

private theorem nu_one_eq_lamI_one_add_w {n' k1 : ℕ} (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ)
    (w : ℕ → Fin n' → ℤ) (j : ℕ) (s : Fin n') :
    Formalism.MainNotions.FormalGroupSystem.nu t lam0 w j s 1 = Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 1 + w j s :=
  if_pos (show 1 ≤ 1 ∧ 1 ≤ k1 + 1 from ⟨le_refl 1, by omega⟩)

private theorem nu_two_eq_lamI_two_add_w {n' k1 : ℕ} (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ)
    (w : ℕ → Fin n' → ℤ) (j : ℕ) (s : Fin n') (hk : 1 ≤ k1) :
    Formalism.MainNotions.FormalGroupSystem.nu t lam0 w j s 2 = Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 2 + w j s :=
  if_pos (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 from ⟨by omega, by omega⟩)

private theorem le_of_monotone_from_one (f : ℕ → ℤ) (h : ∀ j, 1 ≤ j → f j ≤ f (j + 1)) :
    ∀ j, 1 ≤ j → f 1 ≤ f j := by
  intro j hj
  induction j with
  | zero => exact absurd hj (by omega)
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with hn | hn
    · have hn0 : n = 0 := by omega
      subst hn0
      exact le_refl _
    · exact (ih hn).trans (h n hn)

private theorem le_and_neg_le_of_abs_le_of_le (x : ℤ) (c : ℕ) (g : ℝ) (hx : |x| ≤ (c : ℤ)) (hc : (c : ℝ) ≤ g) :
    (x : ℝ) ≤ g ∧ -(x : ℝ) ≤ g := by
  have h := abs_le.mp hx
  have h1 : (x : ℝ) ≤ (c : ℝ) := by exact_mod_cast h.2
  have h2 : -(c : ℝ) ≤ (x : ℝ) := by exact_mod_cast h.1
  constructor <;> linarith

theorem nc_ties (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    let v := Y.vOf u w hg t0
    let Fl := Y.Fl u w hg
    (∀ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
    (∀ s, 0 ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
    (∀ s, (cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s : ℝ) ≤ nc_zc X Y u w hg t0 j s) ∧
    (∀ s, 0 ≤ cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s) := by
  dsimp only
  unfold Formalism.MainNotions.G.LatTied at hL
  have hm : 2 ≤ (D.gat u w hg).P.m := nc_m_ge hT u w hg
  have hm1 : 1 ≤ (D.gat u w hg).P.m := by omega
  have hcG : (0 : ℝ) ≤ Formalism.MainNotions.G.cG L := nc_cG_nonneg
  obtain ⟨-, -, hc, -, -, -, hrep⟩ := hL u w hg
  obtain ⟨-, hs⟩ := hrep t0 ht0
  have hbase := (Y.Fl u w hg).base (Y.vOf u w hg t0)
  unfold Formalism.MainNotions.G.IsBaseWeight at hbase
  have hd := (Y.Fl u w hg).domJ 0 (Y.vOf u w hg t0)
  have hwge := (Y.Fl u w hg).w_ge (Y.vOf u w hg t0)
  have hwm := (Y.Fl u w hg).w_mono (Y.vOf u w hg t0)
  have h0 : 0 < (D.gat u w hg).P.m + 1 := by omega
  have h1 : 1 < (D.gat u w hg).P.m + 1 := by omega
  have hM : (D.gat u w hg).P.m < (D.gat u w hg).P.m + 1 := by omega
  have e0 : (0 : Fin ((D.gat u w hg).P.m + 1)) = ⟨0, h0⟩ := Fin.ext (by simp)
  have hA01 : ∀ s, (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨1, h1⟩ ≤
      (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨0, h0⟩ := fun s =>
    lam_antitone_of_isDominant_liftWt (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
      ((Y.Fl u w hg).w (Y.vOf u w hg t0)) hd s 0 1 h0 h1 (by omega)
  have hA1M : ∀ s, (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨(D.gat u w hg).P.m, hM⟩ ≤
      (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨1, h1⟩ := fun s =>
    lam_antitone_of_isDominant_liftWt (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
      ((Y.Fl u w hg).w (Y.vOf u w hg t0)) hd s 1 (D.gat u w hg).P.m h1 hM (by omega)
  have hTT1 : ∀ s, s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0) →
      |(D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨1, h1⟩| ≤ ((Y.Fl u w hg).c : ℤ) :=
    fun s hsT => ((hbase s).1 hsT).2.2 ⟨1, h1⟩ Nat.one_pos (show 1 < (D.gat u w hg).P.m by omega)
  have hA : ∀ s, s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0) →
      (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨0, h0⟩ = (Y.Fl u w hg).a (Y.vOf u w hg t0) s := by
    intro s hsT
    rw [← e0]
    exact ((hbase s).1 hsT).1
  have hN0 : ∀ s, s ∉ (Y.Fl u w hg).TT (Y.vOf u w hg t0) →
      |(D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨0, h0⟩| ≤ ((Y.Fl u w hg).c : ℤ) := by
    intro s hsT
    rw [← e0]
    exact (hbase s).2 hsT 0
  have hwZ : ∀ s, -(D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨(D.gat u w hg).P.m, hM⟩ ≤
      (Y.Fl u w hg).w (Y.vOf u w hg t0) 1 s := fun s => (le_max_right _ _).trans (hwge s)
  have hwj : ∀ s j, 1 ≤ j →
      (Y.Fl u w hg).w (Y.vOf u w hg t0) 1 s ≤ (Y.Fl u w hg).w (Y.vOf u w hg t0) j s :=
    fun s => le_of_monotone_from_one (fun j => (Y.Fl u w hg).w (Y.vOf u w hg t0) j s) (fun j hj => hwm s j hj)
  have hj1 : 1 ≤ j := by
    unfold Formalism.BasicNotions.SizeData₂.lifts at hj
    exact (Finset.mem_Icc.mp hj).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hsT
    have hA' := (hA s hsT).trans ((hs s).2.2.1 hsT).1
    have hB := (le_and_neg_le_of_abs_le_of_le _ _ _ (hTT1 s hsT) hc).1
    unfold Formalism.MainNotions.FormalGroupSystem.Pf.nc_ya Formalism.MainNotions.G.al Formalism.MainNotions.FormalGroupSystem.al
    simp only [hsT, ↓reduceIte]
    rw [lamI_one_eq_lam0_zero, lamI_two_eq_lam0_one _ _ hm1, hA']
    push_cast
    linarith
  · intro s
    unfold Formalism.MainNotions.FormalGroupSystem.al
    split_ifs with hsT
    · rw [lamI_one_eq_lam0_zero, lamI_two_eq_lam0_one _ _ hm1]
      linarith [hA01 s]
    · exact le_refl 0
  · intro s
    unfold Formalism.MainNotions.FormalGroupSystem.Pf.nc_zc Formalism.MainNotions.FormalGroupSystem.cap
    rw [← (hs s).2.2.2 j hj]
    split_ifs with hsT
    · rw [nu_two_eq_lamI_two_add_w _ _ _ _ _ hm1, lamI_two_eq_lam0_one _ _ hm1]
      have hB := (le_and_neg_le_of_abs_le_of_le _ _ _ (hTT1 s hsT) hc).1
      push_cast
      linarith
    · rw [nu_one_eq_lamI_one_add_w, lamI_one_eq_lam0_zero]
      have hB := (le_and_neg_le_of_abs_le_of_le _ _ _ (hN0 s hsT) hc).1
      push_cast
      linarith
  · intro s
    unfold Formalism.MainNotions.FormalGroupSystem.cap
    split_ifs with hsT
    · rw [nu_two_eq_lamI_two_add_w _ _ _ _ _ hm1, lamI_two_eq_lam0_one _ _ hm1]
      linarith [hA1M s, hwZ s, hwj s j hj1]
    · rw [nu_one_eq_lamI_one_add_w, lamI_one_eq_lam0_zero]
      linarith [hA01 s, hA1M s, hwZ s, hwj s j hj1]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nc_notSg {T p : ℕ} (hg : GIdx D.host T p) : ¬ Formalism.MainNotions.G.IsSg D p := by
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  unfold Formalism.MainNotions.G.IsSg at h
  rw [h1] at h
  exact absurd h (by decide)

theorem nc_step {T p : ℕ} (hg : GIdx D.host T p) : Formalism.MainNotions.G.stepP D p = Formalism.MainNotions.G.hP D p := by
  unfold Formalism.MainNotions.G.stepP; rw [if_neg (nc_notSg hg)]

theorem nc_bs_iter (X : Formalism.MainNotions.G.Inst D L) (h t : Formalism.MainNotions.G.HH D) (i : ℕ) : X.bs h (t + i • h) = X.bs h t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]

theorem nc_bs_rep (X : Formalism.MainNotions.G.Inst D L) (h t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Finset.univ.image (X.bs h)) :
    X.bs h t0 = t0 := by
  obtain ⟨t1, _, rfl⟩ := Finset.mem_image.1 ht0
  obtain ⟨i, hi⟩ := X.bs_orb h t1
  have := nc_bs_iter X h (X.bs h t1) i
  rw [hi] at this
  exact this.symm

theorem nc_partner {T p : ℕ} (hg : GIdx D.host T p) (t : Formalism.MainNotions.G.HH D) (e : ℕ) :
    Formalism.MainNotions.G.partner D p t e = (false, t + e • Formalism.MainNotions.G.hP D p) := by
  unfold Formalism.MainNotions.G.partner
  simp [nc_notSg hg]

theorem nc_tsum_odd (g : ℕ → ℝ) [DecidablePred (fun e : ℕ => Odd e)] :
    ∑' e : ℕ, (if Odd e then g e else 0) = ∑' e : ℕ, g (2 * e + 1) := by
  have hi : Function.Injective (fun e : ℕ => 2 * e + 1) := by
    intro a b h
    simp only at h
    omega
  have hs : Function.support (fun e : ℕ => if Odd e then g e else 0) ⊆ Set.range (fun e : ℕ => 2 * e + 1) := by
    intro e he
    by_cases ho : Odd e
    · obtain ⟨k, rfl⟩ := ho
      exact ⟨k, by ring⟩
    · exact (he (if_neg ho)).elim
  rw [← hi.tsum_eq hs]
  congr 1
  funext e
  exact if_pos (odd_two_mul_add_one e)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

abbrev nc_iota (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : Formalism.MainNotions.G.HH D :=
  t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)

include hL ht0 in
theorem nc_n_eq : (D.gat u w hg).P.n' (Y.vOf u w hg t0) = addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by
  have h0 := hL u w hg
  dsimp only at h0
  obtain ⟨-, -, -, -, -, -, h⟩ := h0
  exact (h t0 ht0).1

include hL ht0 in
theorem nc_iota_inj : Function.Injective (nc_iota Y u w hg t0) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  intro s s' hss
  have hs := lt_of_lt_of_eq s.isLt hn
  have hs' := lt_of_lt_of_eq s'.isLt hn
  exact Fin.ext (nsmul_injOn_Iio_addOrderOf hs hs' (add_left_cancel hss))

include hL ht0 in
theorem nc_topsOn : Formalism.MainNotions.G.topsOn X (D.what₂.places.resChar w) t0 =
    ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).image (nc_iota Y u w hg t0) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have h0 := hL u w hg
  dsimp only at h0
  obtain ⟨-, -, -, -, -, -, h⟩ := h0
  have hsg : ¬ G.IsSg D (D.what₂.places.resChar w) := by
    unfold G.IsSg
    rw [hg.2.2.1]
    decide
  have hst : G.stepP D (D.what₂.places.resChar w) = G.hP D (D.what₂.places.resChar w) := by
    unfold G.stepP
    exact ite_eq_right hsg
  let step := G.hP D (D.what₂.places.resChar w)
  have hiter (t : G.HH D) (i : ℕ) : X.bs step (t + i • step) = X.bs step t := by
    induction i with
    | zero => simp
    | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]
  have hr : t0 ∈ Finset.univ.image (X.bs step) := by
    simpa only [G.reps, hst] using ht0
  have hb : X.bs step t0 = t0 := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i, hi⟩ := X.bs_orb step t
    simpa only [hi] using (hiter (X.bs step t) i).symm
  have hpos : 0 < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := addOrderOf_pos _
  ext t
  simp only [Formalism.MainNotions.G.topsOn, Finset.mem_filter, Finset.mem_image, hst]
  constructor
  · rintro ⟨htT, hbt⟩
    obtain ⟨i, hi⟩ := X.bs_orb (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) t
    rw [hbt] at hi
    have hlt : i % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) <
        (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by
      rw [hn]; exact Nat.mod_lt _ hpos
    refine ⟨⟨_, hlt⟩, ?_, ?_⟩
    · rw [((h t0 ht0).2 _).2.1]
      simp only [mod_addOrderOf_nsmul, hi]
      exact htT
    · simp only [nc_iota, mod_addOrderOf_nsmul, hi]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨((h t0 ht0).2 s).2.1.1 hs, ?_⟩
    simp only [nc_iota]
    change X.bs step (t0 + s.val • step) = t0
    rw [hiter, hb]

include hL ht0 in
theorem nc_isV (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) :
    Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) ↔ ¬ IsOddPos s := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have hsg : ¬ G.IsSg D (D.what₂.places.resChar w) := by
    unfold G.IsSg
    rw [hg.2.2.1]
    decide
  have hst : G.stepP D (D.what₂.places.resChar w) = G.hP D (D.what₂.places.resChar w) := by
    unfold G.stepP
    exact ite_eq_right hsg
  let step := G.hP D (D.what₂.places.resChar w)
  have hiter (t : G.HH D) (i : ℕ) : X.bs step (t + i • step) = X.bs step t := by
    induction i with
    | zero => simp
    | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]
  have hr : t0 ∈ Finset.univ.image (X.bs step) := by
    simpa only [G.reps, hst] using ht0
  have hb : X.bs step t0 = t0 := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i, hi⟩ := X.bs_orb step t
    simpa only [hi] using (hiter (X.bs step t) i).symm
  have hnP : Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) =
      addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by
    simp only [Formalism.MainNotions.G.nP, ite_eq_right hsg]
  have hs := lt_of_lt_of_eq s.isLt hn
  have key : ¬ IsOddPos s ↔ Even s.val := by
    show ¬ (s.val % 2 = 1) ↔ _
    rw [← Nat.odd_iff, Nat.not_odd_iff_even]
  rw [key]
  have hbs : X.bs (G.hP D (D.what₂.places.resChar w))
      (t0 + s.val • G.hP D (D.what₂.places.resChar w)) = t0 := (hiter t0 s.val).trans hb
  simp only [Formalism.MainNotions.G.IsV, hst, hnP, nc_iota, hbs]
  constructor
  · rintro ⟨i, hi, hev, heq⟩
    have hi' := nsmul_injOn_Iio_addOrderOf hi hs (add_left_cancel heq)
    rw [← hi']
    exact hev
  · intro hev
    exact ⟨s.val, hs, hev, rfl⟩

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem nc_capU (j : ℕ) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (k : ℕ) :
    Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) k =
      nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s k) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.capU nc_zc
  rw [nc_partner hg]
  have key : ∀ a : ℕ, t0 + a • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) + k • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
      t0 + ((a + k) % (D.gat u w hg).P.n' (Y.vOf u w hg t0)) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) := by
    intro a
    rw [hn, mod_addOrderOf_nsmul, add_nsmul, add_assoc]
  exact congrArg (fun t => Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, t) + Formalism.MainNotions.G.cG L) (key s.val)

open Classical in
include hL ht0 in
theorem nc_gU_eq (K : Formalism.MainNotions.G.Consts) (j : ℕ) :
    Formalism.MainNotions.G.gU X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0 =
      Formalism.MainNotions.FormalGroupSystem.gam (D.what₂.places.resChar w) * ∑ s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0), nc_ya X Y u w hg t0 s -
        ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos, ∑' e : ℕ,
          min (nc_ya X Y u w hg t0 s / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (2 * e + 1))
            (nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1))) -
        Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0 := by
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.gU
  rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.sum_image (fun a _ b _ h => hinj h), Finset.filter_image,
    Finset.sum_image (fun a _ b _ h => hinj h)]
  have hf : ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter
      (fun a => ¬ Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 a)) =
      ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos := by
    apply Finset.filter_congr
    intro s _
    rw [nc_isV X Y hT hL u w hg t0 ht0 s, not_not]
  rw [hf]
  congr 2
  apply Finset.sum_congr rfl
  intro s _
  rw [nc_tsum_odd]
  apply tsum_congr
  intro e
  rw [nc_capU X Y hT hL u w hg t0 ht0]
  rfl

open Classical in
include hL ht0 in
theorem growth_exclusion_sum_eq (K : Formalism.MainNotions.G.Consts) (j : ℕ) :
    Formalism.MainNotions.G.g0 X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0 =
      ∑ s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0), ∑' e : ℕ,
        (if Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w)
            (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) (2 * e + 1) then 0 else
          max 0 (nc_ya X Y u w hg t0 s / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (2 * e + 1) -
            nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) -
        Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0 := by
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.g0
  rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.sum_image (fun a _ b _ h => hinj h)]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  have e1 : ∀ e : ℕ, (if Odd e ∧ ¬ Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e then
        max 0 (Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (nc_iota Y u w hg t0 s) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ e -
          Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) e) else 0) =
      (if Odd e then (if Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e then 0 else
        max 0 (Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (nc_iota Y u w hg t0 s) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ e -
          Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) e)) else 0) := by
    intro e
    by_cases h1 : Odd e <;> by_cases h2 : Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e <;>
      simp [h1, h2]
  rw [tsum_congr e1, nc_tsum_odd]
  apply tsum_congr
  intro e
  rw [nc_capU X Y hT hL u w hg t0 ht0]
  rfl

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
