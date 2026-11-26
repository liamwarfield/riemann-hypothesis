module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFibMem

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RoomOffGridSymmetric
namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt NumberField

theorem plusW_eq (ys : List ℝ) (w : List C.Letter) :
    KB.plusW ys w = ys.map (fun y => ((true, y) : C.Letter)) ++ w := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [KB.plusW, ih, List.map_cons, List.cons_append]

theorem minusW_eq (ys : List ℝ) (w : List C.Letter) :
    KB.minusW ys w = ys.map (fun y => ((false, y + 1) : C.Letter)) ++ w := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [KB.minusW, ih, List.map_cons, List.cons_append]

theorem cutWord_iff (P : M.Par) (l0 : ℕ) (L : List C.Letter) :
    KB.CutWord P l0 L ↔ (∀ x ∈ L, I.OnCut P.u P.u' l0 x.2) ∧ L.Pairwise (fun x y => 2 < |x.2 - y.2|) := by
  unfold KB.CutWord
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨a, rfl⟩ := List.mem_iff_get.1 hx
      exact h1 a
    · rw [List.pairwise_iff_get]
      intro i j hij
      exact h2 i j (ne_of_lt hij)
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => h1 _ (List.mem_iff_get.2 ⟨a, rfl⟩), fun a b hab => ?_⟩
    rw [List.pairwise_iff_get] at h2
    rcases lt_or_gt_of_ne hab with h | h
    · exact h2 a b h
    · rw [abs_sub_comm]; exact h2 b a h

theorem pick_one (lo hi : ℝ) (Q B : Finset ℝ) (h : 9 * ((Q.card : ℝ) + B.card) + 1 ≤ hi - lo) :
    ∃ y, lo ≤ y ∧ y + 1 ≤ hi ∧ y ∉ B ∧ y + 1 ∉ B ∧ ∀ q ∈ Q, 4 < |y - q| := by
  classical
  by_cases hn : Q.card + B.card = 0
  · have hQ : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    have hB : B = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hQ; subst hB
    simp only [Finset.card_empty, Nat.cast_zero, add_zero, mul_zero, zero_add] at h
    exact ⟨lo, le_refl _, by linarith, by simp, by simp, by simp⟩
  · have hn1 : (1 : ℝ) ≤ (Q.card : ℝ) + B.card := by
      have : 1 ≤ Q.card + B.card := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this
    by_contra hcon
    push_neg at hcon
    have hsub : Set.Icc lo (hi - 1) ⊆
        (⋃ q ∈ Q, Metric.closedBall q 4) ∪ ((B : Set ℝ) ∪ (fun b => b - 1) '' (B : Set ℝ)) := by
      intro y hy
      by_cases hyB : y ∈ B
      · exact Or.inr (Or.inl hyB)
      by_cases hyB' : y + 1 ∈ B
      · exact Or.inr (Or.inr ⟨y + 1, hyB', by ring⟩)
      obtain ⟨q, hq, hyq⟩ := hcon y hy.1 (by linarith [hy.2]) hyB hyB'
      refine Or.inl (Set.mem_biUnion hq ?_)
      rw [Metric.mem_closedBall, Real.dist_eq]
      exact hyq
    have hfin : ((B : Set ℝ) ∪ (fun b => b - 1) '' (B : Set ℝ)).Finite :=
      B.finite_toSet.union (B.finite_toSet.image _)
    have h1 := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub
    have h2 : MeasureTheory.volume ((⋃ q ∈ Q, Metric.closedBall q 4) ∪
        ((B : Set ℝ) ∪ (fun b => b - 1) '' (B : Set ℝ))) ≤
        ∑ q ∈ Q, MeasureTheory.volume (Metric.closedBall q (4 : ℝ)) := by
      refine (MeasureTheory.measure_union_le _ _).trans ?_
      rw [hfin.measure_zero, add_zero]
      exact MeasureTheory.measure_biUnion_finset_le _ _
    have h3 := h1.trans h2
    simp only [Real.volume_Icc, Real.volume_closedBall, Finset.sum_const, nsmul_eq_mul] at h3
    have h4 : ENNReal.ofReal (hi - 1 - lo) ≤ ENNReal.ofReal (8 * Q.card) := by
      refine h3.trans (le_of_eq ?_)
      rw [show (8 : ℝ) * Q.card = (Q.card : ℝ) * (2 * 4) by ring,
        ENNReal.ofReal_mul (p := (Q.card : ℝ)) (by positivity), ENNReal.ofReal_natCast]
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h4
    have : (0 : ℝ) ≤ Q.card := by positivity
    have : (0 : ℝ) ≤ B.card := by positivity
    linarith

theorem pick_many (lo hi : ℝ) (B : Finset ℝ) : ∀ (m : ℕ) (Q : Finset ℝ),
    9 * ((Q.card : ℝ) + m + B.card) + 1 ≤ hi - lo →
    ∃ ys : List ℝ, ys.length = m ∧
      (∀ y ∈ ys, lo ≤ y ∧ y + 1 ≤ hi ∧ y ∉ B ∧ y + 1 ∉ B ∧ ∀ q ∈ Q, 4 < |y - q|) ∧
      ys.Pairwise (fun y y' => 4 < |y - y'|) := by
  intro m
  induction m with
  | zero => exact fun _ _ => ⟨[], rfl, by simp, List.Pairwise.nil⟩
  | succ m ih =>
    intro Q h
    classical
    push_cast at h
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hpick : 9 * ((Q.card : ℝ) + B.card) + 1 ≤ hi - lo := by linarith
    obtain ⟨y, h1, h2, h3, h4, h5⟩ := pick_one lo hi Q B hpick
    have hc : ((insert y Q).card : ℝ) ≤ Q.card + 1 := by exact_mod_cast Finset.card_insert_le y Q
    obtain ⟨ys, hl, hys, hp⟩ := ih (insert y Q) (by linarith)
    refine ⟨y :: ys, by simp [hl], ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨h1, h2, h3, h4, h5⟩
      · obtain ⟨a, b, c, d, e⟩ := hys z hz
        exact ⟨a, b, c, d, fun q hq => e q (Finset.mem_insert_of_mem hq)⟩
    · refine List.Pairwise.cons (fun z hz => ?_) hp
      have := (hys z hz).2.2.2.2 y (Finset.mem_insert_self y Q)
      rwa [abs_sub_comm] at this

theorem two_lt_of_four_lt {y p : ℝ} (h : 4 < |y - p|) : 2 < |y + 1 - p| := by
  rcases lt_abs.mp h with h | h
  · exact lt_abs.mpr (Or.inl (by linarith))
  · exact lt_abs.mpr (Or.inr (by linarith))

def RoomOffGrid : Prop :=
  ∀ (P : M.Par) (l0 : ℕ) (lo hi : ℝ), (∀ Y, lo ≤ Y → Y ≤ hi → I.OnCut P.u P.u' l0 Y) →
    ∀ (w : List C.Letter) (m : ℕ) (B : Finset ℝ), KB.CutWord P l0 w →
      10 * ((w.length : ℝ) + m + B.card + 1) ≤ hi - lo →
      ∃ ys : List ℝ, ys.length = m ∧ (∀ y ∈ ys, lo ≤ y ∧ y + 1 ≤ hi ∧ y ∉ B ∧ y + 1 ∉ B) ∧
        ys.Pairwise (fun y y' => 4 < |y - y'|) ∧ KB.CutWord P l0 (KB.plusW ys w) ∧
        KB.CutWord P l0 (KB.minusW ys w)

theorem roomOffGrid : RoomOffGrid := by
  intro P l0 lo hi hOn w m B hw hlen
  classical
  obtain ⟨hw1, hw2⟩ := (cutWord_iff P l0 w).1 hw
  have hQ : (((w.map Prod.snd).toFinset).card : ℝ) ≤ w.length := by
    have := List.toFinset_card_le (w.map Prod.snd)
    rw [List.length_map] at this
    exact_mod_cast this
  obtain ⟨ys, hlen', hys, hpw⟩ := pick_many lo hi B m ((w.map Prod.snd).toFinset) (by
    have : (0 : ℝ) ≤ B.card := by positivity
    have : (0 : ℝ) ≤ m := by positivity
    linarith)
  have hfar : ∀ y ∈ ys, ∀ x ∈ w, 4 < |y - x.2| := fun y hy x hx =>
    (hys y hy).2.2.2.2 x.2 (List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩))
  refine ⟨ys, hlen', fun y hy => ⟨(hys y hy).1, (hys y hy).2.1, (hys y hy).2.2.1, (hys y hy).2.2.2.1⟩,
    hpw, ?_, ?_⟩
  · rw [plusW_eq, cutWord_iff]
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hOn y (hys y hy).1 (by linarith [(hys y hy).2.1])
      · exact hw1 x hx
    · rw [List.pairwise_append]
      refine ⟨?_, hw2, ?_⟩
      · rw [List.pairwise_map]
        exact hpw.imp fun h => by dsimp only; linarith
      · intro a ha b hb
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
        have := hfar y hy b hb
        dsimp only
        linarith
  · rw [minusW_eq, cutWord_iff]
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hOn (y + 1) (by linarith [(hys y hy).1]) (hys y hy).2.1
      · exact hw1 x hx
    · rw [List.pairwise_append]
      refine ⟨?_, hw2, ?_⟩
      · rw [List.pairwise_map]
        exact hpw.imp fun h => by dsimp only; rw [add_sub_add_right_eq_sub]; linarith
      · intro a ha b hb
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
        exact two_lt_of_four_lt (hfar y hy b hb)

end Formalism.FourierDecayAlt.P.PBD

theorem Formalism.FourierDecayAlt.P.room_off_grid : Formalism.FourierDecayAlt.P.PBD.RoomOffGrid := Formalism.FourierDecayAlt.P.PBD.roomOffGrid
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAIsAdj
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

section IsAdjProof

variable (P : M.Par)

def adjSub : Subalgebra ℂ (DQ P).Pr where
  carrier := {a | IsAdj a}
  mul_mem' {a b} ha hb := ((Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.1 a b ha hb).2
  add_mem' {a b} ha hb := ((Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.1 a b ha hb).1
  algebraMap_mem' z := by
    have h := (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.2.1 z 1 (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).1
    rw [Algebra.algebraMap_eq_smul_one]
    exact h

theorem adjSub_star {a : (DQ P).Pr} (ha : a ∈ adjSub P) : star a ∈ adjSub P :=
  (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.2.2 a ha

theorem gen_adj (hτ : 0 ≤ P.TT) {w : (DQ P).Pr} (hw : w ∈ (DQ P).gens P.TT) : w ∈ adjSub P :=
  Formalism.FourierDecayAlt.P.adjoint_generators P.r P.TT hτ w hw

abbrev MSa : Subalgebra ℂ (A P (DQ P)) := Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (adjSub P) (M.Ty P)

theorem sc_memMS (hτ : 0 ≤ P.TT) {w : (DQ P).Pr} (hw : w ∈ (DQ P).gens P.TT) : sc P (DQ P) w ∈ MSa P :=
  Formalism.FourierDecayAlt.P.MAx2.Jet.scalar_mem _ _ (gen_adj P hτ hw)

theorem star_memMS {a : A P (DQ P)} (ha : a ∈ MSa P) : star a ∈ MSa P := fun i j => by
  rw [Matrix.star_apply]; exact adjSub_star P (ha j i)

variable {P}

section Lv

variable (hτ : 0 ≤ P.TT) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hτ hL

theorem lv_p (l : Fin P.r) : L.p l ∈ MSa P := by
  rw [hL.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_pb (l : Fin P.r) : L.pb l ∈ MSa P := by
  rw [hL.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_c (l : Fin P.r) : L.c l ∈ MSa P := by
  rw [hL.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_ci (l : Fin P.r) : L.ci l ∈ MSa P := by
  rw [hL.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_cb (l : Fin P.r) : L.cb l ∈ MSa P := by
  rw [hL.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_cbi (l : Fin P.r) : L.cbi l ∈ MSa P := by
  rw [hL.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem zeta_mem_self_adjoint : L.ζ ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zi : L.ζi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zb : L.ζb ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zbi : L.ζbi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_gg : L.GG ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_ggi : L.GGi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_nab : L.nab ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => add_mem (gen_adj P hτ (by simp [DAlg.gens]))
    (Subalgebra.smul_mem _ (mul_mem (gen_adj P hτ (by simp [DAlg.gens])) (gen_adj P hτ (by simp [DAlg.gens]))) _)
theorem lv_nabs : L.nabs ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => add_mem (neg_mem (gen_adj P hτ (by simp [DAlg.gens])))
    (Subalgebra.smul_mem _ (mul_mem (gen_adj P hτ (by simp [DAlg.gens])) (gen_adj P hτ (by simp [DAlg.gens]))) _)

theorem lv_Dr : L.Dr ∈ MSa P := by
  unfold LevelData.Dr
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_c hτ hL l
theorem lv_Drb : L.Drb ∈ MSa P := by
  unfold LevelData.Drb
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_cb hτ hL l
theorem lv_Dri : L.Dri ∈ MSa P := by
  unfold LevelData.Dri
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_ci hτ hL l
theorem lv_Drbi : L.Drbi ∈ MSa P := by
  unfold LevelData.Drbi
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_cbi hτ hL l

theorem lv_Tprod (Y : ℂ) : L.Tprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (MSa P) (Fin 2) := by
  unfold LevelData.Tprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (Subalgebra.algebraMap_mem _ _) (lv_p hτ hL l)
  · exact neg_mem (lv_c hτ hL l)
  · exact lv_ci hτ hL l
  · exact zero_mem _

theorem lv_Tvprod (Y : ℂ) : L.Tvprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (MSa P) (Fin 2) := by
  unfold LevelData.Tvprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tvl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact sub_mem (Subalgebra.algebraMap_mem _ _) (lv_pb hτ hL l)
  · exact neg_mem (lv_cb hτ hL l)
  · exact lv_cbi hτ hL l
  · exact zero_mem _

theorem lv_hat {X : A P (DQ P)} (hX : X ∈ hatSet P L) : X ∈ MSa P := by
  have hl0 : ∀ Y, L.l0 Y ∈ MSa P := fun Y => by
    unfold LevelData.l0
    exact sub_mem (neg_mem (lv_nab hτ hL)) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (lv_zb hτ hL) (lv_ggi hτ hL)))
  have hm0 : ∀ Y, L.m0 Y ∈ MSa P := fun Y => by
    unfold LevelData.m0
    exact sub_mem (neg_mem (lv_nabs hτ hL)) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (zeta_mem_self_adjoint hτ hL) (lv_ggi hτ hL)))
  rcases hX with ((⟨Y, rfl⟩ | ⟨Y, rfl⟩) | ⟨Y, rfl⟩) | ⟨Y, rfl⟩
  · exact mul_mem (lv_Dr hτ hL) (lv_Tprod hτ hL Y 0 0)
  · exact mul_mem (mul_mem (lv_Drb hτ hL) (lv_gg hτ hL))
      (add_mem (mul_mem (hl0 Y) (lv_Tprod hτ hL Y 0 0)) (lv_Tprod hτ hL Y 1 0))
  · exact mul_mem (lv_Drb hτ hL) (lv_Tvprod hτ hL Y 0 0)
  · exact mul_mem (mul_mem (lv_Dr hτ hL) (lv_gg hτ hL))
      (add_mem (mul_mem (hm0 Y) (lv_Tvprod hτ hL Y 0 0)) (lv_Tvprod hτ hL Y 1 0))

theorem lv_SS (i : ℕ) : SS P (DQ P) i ∈ MSa P := fun a b => by
  simp only [SS, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact zero_mem _

theorem lv_kap (g : M.Ty P → ℂ) : kap P (DQ P) g ∈ MSa P := by
  have : kap P (DQ P) g = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (g π) := rfl
  rw [this]
  exact Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => Subalgebra.algebraMap_mem _ _

theorem lv_bdd {b : A P (DQ P)} (hb : b ∈ bddSet P L) : b ∈ MSa P := by
  have hD : L.D ∈ MSa P := mul_mem (lv_Dr hτ hL) (zeta_mem_self_adjoint hτ hL)
  have hDi : L.Di ∈ MSa P := mul_mem (lv_zi hτ hL) (lv_Dri hτ hL)
  have hDb : L.Db ∈ MSa P := mul_mem (lv_Drb hτ hL) (lv_zb hτ hL)
  have hDbi : L.Dbi ∈ MSa P := mul_mem (lv_zbi hτ hL) (lv_Drbi hτ hL)
  have hS : ∀ i, L.Drb * L.Dri * SS P (DQ P) i ∈ MSa P := fun i =>
    mul_mem (mul_mem (lv_Drb hτ hL) (lv_Dri hτ hL)) (lv_SS hτ hL i)
  rcases hb with ((h4 | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h4
    rcases h4 with rfl | rfl | rfl | rfl
    · exact lv_zi hτ hL
    · exact lv_zbi hτ hL
    · exact mul_mem hD hDbi
    · exact mul_mem hDb hDi
  · exact lv_kap hτ hL g
  · exact hS i
  · exact star_memMS P (hS i)

end Lv

theorem transfer_is_adjoint_holds : JAIsAdj := by
  intro P L hτ hL a ha
  have hsub : Submonoid.closure (hatSet P L ∪ bddSet P L) ≤ (MSa P).toSubmonoid :=
    Submonoid.closure_le.2 fun x hx => by
      rcases hx with hx | hx
      · exact lv_hat (le_of_lt hτ) hL hx
      · exact lv_bdd (le_of_lt hτ) hL hx
  intro π π'
  exact hsub ha π π'

end IsAdjProof

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalNormNonneg
open Finset Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt NumberField

section defeq
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)

end defeq

theorem extract_prob {ι X : Type} [Fintype ι] (U : Finset X) (θ : ℕ → ι → X → ℝ)
    (hθ : ∀ n A, TB.IsProb U (θ n A)) :
    ∃ (φ : ℕ → ℕ) (θ' : ι → X → ℝ), StrictMono φ ∧ (∀ A, TB.IsProb U (θ' A)) ∧
      ∀ A, ∀ x ∈ U, Tendsto (fun n => θ (φ n) A x) atTop (𝓝 (θ' A x)) := by
  classical
  let x : ℕ → (ι × U) → ℝ := fun n p => θ n p.1 p.2.1
  have hK : IsCompact (Set.Icc (0 : ι × U → ℝ) 1) := isCompact_Icc
  have hmem : ∀ n, x n ∈ Set.Icc (0 : ι × U → ℝ) 1 := by
    intro n
    refine ⟨fun p => (hθ n p.1).1 _, fun p => ?_⟩
    have h := Finset.single_le_sum (fun y _ => (hθ n p.1).1 y) p.2.2
    rw [(hθ n p.1).2.2] at h
    exact h
  obtain ⟨y, _, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hl : ∀ A z (h : z ∈ U), Tendsto (fun n => θ (φ n) A z) atTop (𝓝 (y (A, ⟨z, h⟩))) := fun A z h =>
    ((continuous_apply (A, (⟨z, h⟩ : U))).tendsto y).comp hlim
  refine ⟨φ, fun A z => if h : z ∈ U then y (A, ⟨z, h⟩) else 0, hφ, ?_, ?_⟩
  · intro A
    refine ⟨fun z => ?_, fun z hz => by simp [hz], ?_⟩
    · by_cases h : z ∈ U
      · simp only [h, dite_true]
        exact ge_of_tendsto' (hl A z h) fun n => (hθ (φ n) A).1 z
      · simp [h]
    · have hs : Tendsto (fun n => ∑ z ∈ U, θ (φ n) A z) atTop
          (𝓝 (∑ z ∈ U, if h : z ∈ U then y (A, ⟨z, h⟩) else 0)) := by
        apply tendsto_finsetSum
        intro z hz
        simp only [hz, dite_true]
        exact hl A z hz
      have h1 : (fun n => ∑ z ∈ U, θ (φ n) A z) = fun _ => (1 : ℝ) := funext fun n => (hθ (φ n) A).2.2
      rw [h1] at hs
      exact tendsto_nhds_unique hs tendsto_const_nhds
  · intro A z hz
    simp only [hz, dite_true]
    exact hl A z hz

section conv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)

theorem gram_withRR (n : ℕ) (ε : ℝ) (i : ℕ) (w : C.Word S.f) (p q : TB.Pt E) :
    (KB.withRR S (RR n)).gram ε i w p q = if i ≤ S.G.r + 1 then ∏ v, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G
      (C.loc (S.σ v) p)) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
        RR n v ε i (w v) (C.loc (S.σ v) p) (C.loc (S.σ v) q) else 0 := rfl

theorem gram_S (ε : ℝ) (i : ℕ) (w : C.Word S.f) (p q : TB.Pt E) :
    S.gram ε i w p q = if i ≤ S.G.r + 1 then ∏ v, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G
      (C.loc (S.σ v) p)) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
        (S.pd v).RR ε i (w v) (C.loc (S.σ v) p) (C.loc (S.σ v) q) else 0 := rfl

variable {S RR}

theorem gram_tendsto
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) (w : S.W) (p q : TB.Pt E) :
    Tendsto (fun n => (KB.withRR S (RR n)).gram ε i w.1 p q) atTop (𝓝 (S.gram ε i w.1 p q)) := by
  simp only [gram_withRR, gram_S]
  split_ifs
  · apply tendsto_finsetProd
    intro v _
    exact tendsto_const_nhds.mul (hconv v ε hε i _ ⟨w, rfl⟩ _ _)
  · exact tendsto_const_nhds

theorem nst_tendsto
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : E) :
    Tendsto (fun n => (KB.withRR S (RR n)).base.Nst ε i s w Y κ t t') atTop
      (𝓝 (S.base.Nst ε i s w Y κ t t')) := by
  have e1 : ∀ n, (KB.withRR S (RR n)).base.Nst ε i s w Y κ t t' = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * (KB.withRR S (RR n)).gram ε i w.1 (TB.join h s t) (TB.join h' s t')) / (S.base.wt w : ℂ) :=
    fun n => rfl
  have e2 : S.base.Nst ε i s w Y κ t t' = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * S.gram ε i w.1 (TB.join h s t) (TB.join h' s t')) / (S.base.wt w : ℂ) := rfl
  rw [e2]; simp only [e1]
  apply Tendsto.div_const
  apply tendsto_finsetSum; intro h _
  apply tendsto_finsetSum; intro h' _
  exact tendsto_const_nhds.mul (gram_tendsto hconv hε i w _ _)

theorem base_count_tendsto
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) :
    Tendsto (fun n => (KB.withRR S (RR n)).base.N0 ε k w Y κ) atTop (𝓝 (S.base.N0 ε k w Y κ)) := by
  have e1 : ∀ n, (KB.withRR S (RR n)).base.N0 ε k w Y κ = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * (KB.withRR S (RR n)).gram ε k w.1 h h').re / S.base.wt w := fun n => rfl
  have e2 : S.base.N0 ε k w Y κ = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε k w.1 h h').re / S.base.wt w := rfl
  rw [e2]; simp only [e1]
  apply Tendsto.div_const
  apply (Complex.continuous_re.tendsto _).comp
  apply tendsto_finsetSum; intro h _
  apply tendsto_finsetSum; intro h' _
  exact tendsto_const_nhds.mul (gram_tendsto hconv hε k w _ _)

theorem gram_psd {S : C.HidaSetting E Wp Wq} (hP : C.ThmPPos S) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W)
    (Y : Finset (TB.Pt E)) : TB.PSDOn Y (fun h h' => S.gram ε k w.1 h h') := by
  classical
  by_cases hk : k ≤ S.G.r + 1
  · have : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y
        (fun h h' => S.gramLoc v ε k (w.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h')) := by
      intro v _
      exact JCx1.decay.psd_pull (Y.image (C.loc (S.σ v))) _ (hP v ε hε k hk w _) Y _
        (fun h hh => Finset.mem_image_of_mem _ hh)
    refine Jx7.psd_congr ?_ (Jx7.psd_prod univ _ this)
    intro x _ y _
    simp only [C.HidaSetting.gram, hk, if_true]
  · refine Jx7.psd_congr ?_ (Jx7.psd_zero (F := Y))
    intro x _ y _
    simp only [C.HidaSetting.gram, hk, if_false]

theorem local_norm_nonneg_alt {S : C.HidaSetting E Wp Wq} (hP : C.ThmPPos S) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W)
    (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (hκ : TB.PSDOn Y κ) : 0 ≤ S.base.N0 ε k w Y κ := by
  have e2 : S.base.N0 ε k w Y κ = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε k w.1 h h').re / S.base.wt w := rfl
  rw [e2]
  apply div_nonneg (BaseGramNonnegativity.sum_re_nonneg Y κ _ hκ (gram_psd hP hε k w Y))
  show 0 ≤ C.Word.size S.P w.1
  unfold C.Word.size
  exact Finset.prod_nonneg fun v _ => List.prod_nonneg fun x hx => by
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _

end conv

theorem limit_closed : KB.LimitClosed := by
  intro E _ _ _ Wp Wq _ _ _ _ S RR hconv
  refine ⟨?_, ?_, ?_⟩
  · intro Λ hL ε hε i s hs hsi hir w hw hcnt
    choose θn hθn hbd using fun n => hL n ε hε i s hs hsi hir w hw hcnt
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob (ι := Finset (Fin S.f)) (X := S.W × S.W)
      (S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K)) (fun n => θn n) hθn
    refine ⟨θ, hθ, ?_⟩
    intro Y T κ hY hκ t ht t' ht' h0 h0' ho A
    have h1 : ∀ n, (∏ v ∈ A, S.base.av v (t⁻¹ - t'⁻¹) ^ S.base.K) *
        ‖(KB.withRR S (RR (φ n))).base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ ≤
        (∏ v ∈ A, Λ (i - s + 1) s v ^ S.base.K) *
          ∑ x ∈ S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K), θn (φ n) A x *
            ((((KB.withRR S (RR (φ n))).base.Nst ε i s x.1 Y (TB.blk κ s t t) t t).re +
              ((KB.withRR S (RR (φ n))).base.Nst ε i s x.2 Y (TB.blk κ s t' t') t' t').re) / 2) :=
      fun n => hbd (φ n) Y T κ hY hκ t ht t' ht' h0 h0' ho A
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact tendsto_const_nhds.mul ((nst_tendsto hconv hε i s w Y _ t t').comp hφ.tendsto_atTop).norm
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim A x hx).mul ?_)
      refine Tendsto.div_const (Tendsto.add ?_ ?_) _
      · exact (Complex.continuous_re.tendsto _).comp ((nst_tendsto hconv hε i s x.1 Y _ t t).comp hφ.tendsto_atTop)
      · exact (Complex.continuous_re.tendsto _).comp
          ((nst_tendsto hconv hε i s x.2 Y _ t' t').comp hφ.tendsto_atTop)
  · intro Λ' hL ε hε s hs hsr w hw hcnt
    choose θn hθn hbd using fun n => hL n ε hε s hs hsr w hw hcnt
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob (ι := Finset (Fin S.f)) (X := S.W)
      (S.base.Wb (S.base.cnt w + S.base.K)) (fun n => θn n) hθn
    refine ⟨θ, hθ, ?_⟩
    intro Y hY κ hκ t ht B
    have h1 : ∀ n, ((KB.withRR S (RR (φ n))).base.Nst ε (S.G.r + 1) s w Y κ t t).re ≤
        (∏ v ∈ B, (S.base.av v t * Λ' (S.G.r + 2 - s) s v) ^ (2 * S.base.K)) *
          ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K), θn (φ n) B w' *
            ((KB.withRR S (RR (φ n))).base.Nst ε (S.G.r + 1) s w' Y κ t t).re :=
      fun n => hbd (φ n) Y hY κ hκ t ht B
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε (S.G.r + 1) s w Y κ t t).comp hφ.tendsto_atTop)
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim B x hx).mul ?_)
      exact (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε (S.G.r + 1) s x Y κ t t).comp hφ.tendsto_atTop)
  · intro C₄ hP _ hSF ε hε i s hs hsi hir w hw hcnt hvol
    set Bd := C₄ ^ (S.base.f * s) * (∏ s' ∈ Ico 1 s, S.base.vol (i - s + 1) s')
    have H : ∀ n, ∃ θ : Unit → S.W → ℝ, (∀ u, TB.IsProb (S.base.Wb (S.base.cnt w + s * S.base.K)) (θ u)) ∧
        ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) → ∀ κ, TB.PSDOn Y κ →
          ∀ (t₀ : E) (T : Finset E), (∀ t ∈ T, t ≠ 0 ∧ t - t₀ ∈ S.base.La (i - s + 1) s) →
            ∑ t ∈ T, ((KB.withRR S (RR n)).base.Nst ε i s w Y κ t t).re ≤
              Bd * ∑ w' ∈ S.base.Wb (S.base.cnt w + s * S.base.K), θ () w' *
                (KB.withRR S (RR n)).base.N0 ε (i - s) w' Y κ := by
      intro n
      obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF n ε hε i s hs hsi hir w hw hcnt hvol
      refine ⟨fun _ => θ, fun _ => hθ, ?_⟩
      intro Y hY κ hκ t₀ T hT
      refine (hb Y hY κ hκ t₀ T hT).trans ?_
      apply mul_le_mul_of_nonneg_right hMv
      exact Finset.sum_nonneg fun w' _ => mul_nonneg (hθ.1 w') (local_norm_nonneg_alt (hP n) hε _ w' Y κ hκ)
    choose θn hθn hbd using H
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob _ θn hθn
    refine ⟨Bd, le_refl _, θ (), hθ (), ?_⟩
    intro Y hY κ hκ t₀ T hT
    have h1 : ∀ n, ∑ t ∈ T, ((KB.withRR S (RR (φ n))).base.Nst ε i s w Y κ t t).re ≤
        Bd * ∑ w' ∈ S.base.Wb (S.base.cnt w + s * S.base.K), θn (φ n) () w' *
          (KB.withRR S (RR (φ n))).base.N0 ε (i - s) w' Y κ := fun n => hbd (φ n) Y hY κ hκ t₀ T hT
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact tendsto_finsetSum _ fun t _ => (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε i s w Y κ t t).comp hφ.tendsto_atTop)
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim () x hx).mul ?_)
      exact (base_count_tendsto hconv hε (i - s) x Y κ).comp hφ.tendsto_atTop

end Formalism.FourierDecayAlt.P.PBA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLevelMinors
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma norm_le_gN (M : Mat k r) : ‖M‖ ≤ gN M := by
  have hg : gN M = Real.sqrt (∑ i, ∑ j, Complex.normSq (M i j)) := rfl
  rw [hg, Matrix.norm_le_iff (Real.sqrt_nonneg _)]
  intro i j
  have h2 : ‖M i j‖ ^ 2 ≤ ∑ i, ∑ j, Complex.normSq (M i j) := by
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (M i j) ≤ ∑ j', Complex.normSq (M i j') :=
          Finset.single_le_sum (f := fun j' => Complex.normSq (M i j'))
            (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', Complex.normSq (M i' j') :=
          Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (M i' j'))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  calc ‖M i j‖ = |‖M i j‖| := (abs_of_nonneg (norm_nonneg _)).symm
    _ ≤ _ := Real.abs_le_sqrt h2

lemma gN_unit {X : Mat k r} (hX : ∀ i j, ‖X i j‖ ≤ 1) : gN X ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
  have hg : gN X = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := rfl
  have h1 : ∀ i j, Complex.normSq (X i j) ≤ 1 := fun i j => by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hX i j, norm_nonneg (X i j)]
  have hs : (∑ i, ∑ j, Complex.normSq (X i j)) ≤
      ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    calc (∑ i, ∑ j, Complex.normSq (X i j))
        ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hg]
  calc Real.sqrt _ ≤ Real.sqrt (((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt hs
    _ = _ := Real.sqrt_mul_self (Nat.cast_nonneg _)

lemma gN_conjT (M : Mat k r) : gN Mᴴ = gN M := by
  show Real.sqrt _ = Real.sqrt _
  congr 1
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

private lemma gN_mul_le_hermitian_curvature (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  have hA : gN A = Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) := rfl
  have hB : gN B = Real.sqrt (∑ i, ∑ j, Complex.normSq (B i j)) := rfl
  have hAB : gN (A * B) = Real.sqrt (∑ i, ∑ j, Complex.normSq ((A * B) i j)) := rfl
  have hSA : 0 ≤ ∑ i, ∑ j, Complex.normSq (A i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have entry : ∀ i j, Complex.normSq (∑ l, A i l * B l j) ≤
      (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) := by
    intro i j
    rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l‖ * ‖B l j‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖A i l‖) (fun l => ‖B l j‖)
    have h3 : ∀ l, Complex.normSq (A i l) = ‖A i l‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    have h4 : ∀ l, Complex.normSq (B l j) = ‖B l j‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    simp only [h3, h4]
    have h5 : ‖∑ l, A i l * B l j‖ ^ 2 ≤ (∑ l, ‖A i l‖ * ‖B l j‖) ^ 2 := by
      have := norm_nonneg (∑ l, A i l * B l j)
      nlinarith
    exact h5.trans h2
  have hS : (∑ i, ∑ j, Complex.normSq ((A * B) i j)) ≤
      (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
   calc (∑ i, ∑ j, Complex.normSq ((A * B) i j))
      = ∑ i, ∑ j, Complex.normSq (∑ l, A i l * B l j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          congrArg Complex.normSq Matrix.mul_apply
    _ ≤ ∑ i, ∑ j, (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry i j
    _ = (∑ i, ∑ l, Complex.normSq (A i l)) * (∑ j, ∑ l, Complex.normSq (B l j)) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
        rw [Finset.sum_comm (f := fun j l => Complex.normSq (B l j))]
  rw [hA, hB, hAB]
  exact (Real.sqrt_le_sqrt hS).trans (le_of_eq (Real.sqrt_mul hSA _))

lemma gN_inv_le {g : Mat k r} (hg : g ∈ GV k r) : gN g⁻¹ ≤ gN (Hpk k r) ^ 2 * gN g := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  rw [Matrix.inv_eq_left_inv hl]
  have h0 : ∀ M : Mat k r, 0 ≤ gN M := fun M => Real.sqrt_nonneg _
  calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le_hermitian_curvature _ _
    _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) :=
        mul_le_mul_of_nonneg_right (gN_mul_le_hermitian_curvature _ _) (h0 _)
    _ = gN (Hpk k r) ^ 2 * gN g := by rw [gN_conjT]; ring

section vol

open Formalism.FourierDecayAlt.P.B2x6

variable {k r' : ℕ}

end vol

end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
end
end
