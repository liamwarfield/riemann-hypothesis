module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieGermI

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqM2
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqDer
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section Defs

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.dF (Y : FBChart C V O dd) (v : Fin dd → C) (j : Fin dd) : PS C 1 dd :=
  ∑ i, MvPowerSeries.C (v i) * ev (n := 1) ![pt C dd 0, 0] (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j))

def ExDerSt (Y : FBChart C V O dd) : Prop :=
  ∀ (v : Fin dd → C) (j : Fin dd),
    ∑ i, MvPowerSeries.C (v i) * MvPowerSeries.pderiv (R := C) ((0 : Fin 1), i) (Y.ex j) = ev (n := 1) ![Y.ex] (Y.dF v j)

def GermIIMSt (Y : FBChart C V O dd) : Prop :=
  ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    IntS V ((∑ j : Fin dd, (∑ i : Fin dd, MvPowerSeries.C (v i) *
        ev (n := 2) ![pt C dd 0, 0] (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j))) *
          MvPowerSeries.pderiv (R := C) ((0 : Fin 2), j) Y.h) + ev (n := 2) ![pt C dd 1] (Y.sgP v))

end Defs

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem dVar_eq {σ : Type} (w : σ) (F : MvPowerSeries σ C) : dVar w F = MvPowerSeries.pderiv (R := C) w F := by
  ext μ
  rw [MvPowerSeries.coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem pderiv_upG_same (g : Fin 2) (k : I g) (F : MvPowerSeries (I g) C) :
    MvPowerSeries.pderiv (R := C) (⟨g, k⟩ : WV I) (upG g F) = upG g (MvPowerSeries.pderiv (R := C) k F) := by
  unfold upG
  rw [Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _), Finset.sum_eq_single k]
  · rw [MvPowerSeries.pderiv_X_self, mul_one]
  · intro c _ hc
    rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
    intro h
    exact hc (eq_of_heq (Sigma.mk.inj h).2)
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem pderiv_upG_ne (g g' : Fin 2) (h : g' ≠ g) (k : I g) (F : MvPowerSeries (I g') C) :
    MvPowerSeries.pderiv (R := C) (⟨g, k⟩ : WV I) (upG g' F) = 0 := by
  unfold upG
  rw [Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _)]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
  intro he
  exact h (Sigma.mk.inj he).1

end RowTiePCEqDer

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem pderiv_uncurry (f : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.pderiv (R := C) i (un1 f) = un1 (MvPowerSeries.pderiv (R := C) ((0 : Fin 1), i) f) := by
  rw [uncurry_eq_subst, Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _),
    Finset.sum_eq_single ((0 : Fin 1), i), uncurry_eq_subst]
  · rw [show (((0 : Fin 1), i) : Fin 1 × Fin dd).2 = i from rfl, MvPowerSeries.pderiv_X_self, mul_one]
  · intro q _ hq
    rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
    intro h
    exact hq (Prod.ext (Subsingleton.elim _ _) h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem uncurry_linear_combination (r : Fin dd → C) (f : Fin dd → PS C 1 dd) :
    un1 (∑ i, MvPowerSeries.C (r i) * f i) = ∑ i, MvPowerSeries.C (r i) * un1 (f i) := by
  simp only [uncurry_eq_subst]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom hasSubst_snd, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C]

theorem ev_pt_dF (Y : FBChart C V O dd) (v : Fin dd → C) (g' : Fin 2) (j : Fin dd) :
    ev (n := 2) ![pt C dd g'] (Y.dF v j) =
      ∑ i, MvPowerSeries.C (v i) * ev (n := 2) ![pt C dd g', 0] (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j)) := by
  have hZ := z0_1 (pt C (n := 2) dd g') (z0_pt g')
  have hZ' : Z0 (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) := z0_p0 _ (z0_pt 0)
  unfold FBChart.dF
  rw [ev_sum hZ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_mul hZ, ev_C, ev_ev hZ' hZ]
  congr 2
  funext k j'
  fin_cases k
  · exact ev_X hZ 0 j'
  · exact ev_zero hZ

theorem pderiv_lin {κ : Type} [Fintype κ] (X : RawChart C d I κ) (g : Fin 2) (k : I g) (i : κ) :
    MvPowerSeries.pderiv (R := C) k (∑ c : I g, X.u g c i • (MvPowerSeries.X c : MvPowerSeries (I g) C)) =
      MvPowerSeries.C (X.u g k i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single k]
  · rw [Derivation.map_smul, MvPowerSeries.pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]
  · intro c _ hc
    rw [Derivation.map_smul, MvPowerSeries.pderiv_X_of_ne hc, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

end RowTiePCEqDer

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem subst_exp_eval_two {dd : ℕ} (X : RawChart C d I (Fin dd))
    (hE0 : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (X.expPt q.1 q.2) = 0) (g' : Fin 2) (f : PS C 1 dd) :
    MvPowerSeries.subst (fun q : Fin 2 × Fin dd => X.expPt q.1 q.2) (ev (n := 2) ![pt C dd g'] f) =
      MvPowerSeries.subst (X.expPt g') (un1 f) := by
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
  rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin 1 × Fin dd => pt C (n := 2) dd g' q.2)
      fun q => MvPowerSeries.constantCoeff_X _) hS,
    subst_singlePointUncurry (fun j => hE0 (g', j))]
  congr 1
  funext q
  rw [show (pt C (n := 2) dd g' q.2) = MvPowerSeries.X (g', q.2) from rfl, MvPowerSeries.subst_X hS]

end RowTiePCEqDer


end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

open PartialDerivEval

namespace RowTiePCEqM

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constant_zero_outer_points : Z0 ((![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)) := by
  intro k i; fin_cases k <;> simp [pt]

theorem integral_outer_points : ∀ k i, IntS V (((![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)) k i) := by
  intro k i; fin_cases k
  · exact intS_X _
  · exact intS_zero
  · exact intS_X _

theorem constant_zero_second_axis : Z0 ((![0, pt C dd 1] : Fin 2 → Pt C 2 dd)) := by
  intro k i; fin_cases k <;> simp [pt]

theorem integral_second_axis_points : ∀ k i, IntS V (((![0, pt C dd 1] : Fin 2 → Pt C 2 dd)) k i) := by
  intro k i; fin_cases k
  · exact intS_zero
  · exact intS_X _

theorem eval_outer_points_first (j : Fin dd) : ev (n := 2) ((![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)) (pt C (n := 3) dd 0 j) = pt C dd 0 j := by
  rw [show (pt C (n := 3) dd 0 j) = X ((0 : Fin 3), j) from rfl, ev_X constant_zero_outer_points]; rfl

theorem eval_outer_points_middle (j : Fin dd) : ev (n := 2) ((![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)) (pt C (n := 3) dd 1 j) = 0 := by
  rw [show (pt C (n := 3) dd 1 j) = X ((1 : Fin 3), j) from rfl, ev_X constant_zero_outer_points]; rfl

theorem eval_outer_points_last (j : Fin dd) : ev (n := 2) ((![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)) (pt C (n := 3) dd 2 j) = pt C dd 1 j := by
  rw [show (pt C (n := 3) dd 2 j) = X ((2 : Fin 3), j) from rfl, ev_X constant_zero_outer_points]; rfl

theorem group_law_zero_right (Y : FBChart C V O dd) {n : ℕ} (P : Pt C n dd) (hP : ∀ j, constantCoeff (P j) = 0) (j : Fin dd) :
    ev (n := n) ![P, 0] (Y.B.G.F j) = P j := by
  have hA : Z0 (![P, 0] : Fin 2 → Pt C n dd) := z0_p0 P hP
  conv_lhs => rw [← Y.B.G.comm j]
  rw [ev_ev (z0_pp 1 0) hA]
  have e1 : (fun k i => ev (n := n) (![P, 0] : Fin 2 → Pt C n dd) ((![pt C dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) k i)) =
      ![0, P] := by
    funext k i; fin_cases k
    · exact ev_X hA 1 i
    · exact ev_X hA 0 i
  rw [e1]
  have hB : Z0 (![P] : Fin 1 → Pt C n dd) := z0_1 P hP
  have hU : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := by
    intro k i; fin_cases k
    · simp
    · exact z0_pt 0 i
  have e2 : (![0, P] : Fin 2 → Pt C n dd) =
      fun k i => ev (n := n) (![P] : Fin 1 → Pt C n dd) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) k i) := by
    funext k i; fin_cases k
    · exact (ev_zero hB).symm
    · exact (ev_X hB 0 i).symm
  rw [e2, ← ev_ev hU hB, Y.B.G.unit j, ev_X hB]
  rfl

theorem pderiv_ev_fst {n : ℕ} (A B : Pt C n dd) (hA : ∀ j, constantCoeff (A j) = 0) (hB : ∀ j, constantCoeff (B j) = 0)
    (q : Fin n × Fin dd) (hBq : ∀ j, pderiv (R := C) q (B j) = 0) (f : PS C 2 dd) :
    pderiv (R := C) q (ev ![A, B] f) = ∑ j, ev ![A, B] (pderiv (R := C) ((0 : Fin 2), j) f) * pderiv (R := C) q (A j) := by
  have hZ : Z0 (![A, B] : Fin 2 → Pt C n dd) := by
    intro k i; fin_cases k
    · exact hA i
    · exact hB i
  rw [pderiv_eval_pair hZ]
  have e : ∑ j, ev ![A, B] (pderiv (R := C) ((1 : Fin 2), j) f) * pderiv (R := C) q ((![A, B] : Fin 2 → Pt C n dd) 1 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [show ((![A, B] : Fin 2 → Pt C n dd) 1 j) = B j from rfl, hBq j, mul_zero]
  rw [e, add_zero]
  rfl

theorem pderiv_ev_snd {n : ℕ} (A B : Pt C n dd) (hA : ∀ j, constantCoeff (A j) = 0) (hB : ∀ j, constantCoeff (B j) = 0)
    (q : Fin n × Fin dd) (hAq : ∀ j, pderiv (R := C) q (A j) = 0) (f : PS C 2 dd) :
    pderiv (R := C) q (ev ![A, B] f) = ∑ j, ev ![A, B] (pderiv (R := C) ((1 : Fin 2), j) f) * pderiv (R := C) q (B j) := by
  have hZ : Z0 (![A, B] : Fin 2 → Pt C n dd) := by
    intro k i; fin_cases k
    · exact hA i
    · exact hB i
  rw [pderiv_eval_pair hZ]
  have e : ∑ j, ev ![A, B] (pderiv (R := C) ((0 : Fin 2), j) f) * pderiv (R := C) q ((![A, B] : Fin 2 → Pt C n dd) 0 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [show ((![A, B] : Fin 2 → Pt C n dd) 0 j) = A j from rfl, hAq j, mul_zero]
  rw [e, zero_add]
  rfl

theorem sum_pderiv_pt {n : ℕ} (k : Fin n) (i : Fin dd) (a : Fin dd → PS C n dd) :
    ∑ j, a j * pderiv (R := C) (k, i) (pt C dd k j) = a i := by
  rw [Finset.sum_eq_single i]
  · rw [show (pt C dd k i) = X (k, i) from rfl, pderiv_X_self, mul_one]
  · intro j _ hj
    rw [show (pt C dd k j) = X (k, j) from rfl, pderiv_X_of_ne (fun h => hj (Prod.mk.inj h).2), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem pderiv_pt_ne {n : ℕ} {k k' : Fin n} (h : k' ≠ k) (i j : Fin dd) : pderiv (R := C) (k, i) (pt C dd k' j) = 0 :=
  pderiv_X_of_ne (fun e => h (Prod.mk.inj e).1)

end RowTiePCEqM

namespace RowTiePCEqM

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem hi1 (Y : FBChart C V O dd) (i : Fin dd) :
    ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (pderiv (R := C) ((1 : Fin 3), i) Y.B.ph1) =
      ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) (pderiv (R := C) ((0 : Fin 2), i) Y.h) -
        ∑ j, pderiv (R := C) ((0 : Fin 2), j) Y.h * ev (n := 2) ![pt C dd 0, 0] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j)) := by
  have hph : Y.B.ph1 = FB.expS C (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h + ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h -
      ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) := by
    have := Y.gauge.ph1; rwa [toK_self, FK_self] at this
  have hZ : Z0 (![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] : Fin 2 → Pt C 3 dd) := by
    intro k j
    fin_cases k
    · exact const_addOf Y 0 1 j
    · exact z0_pt 2 j
  have hg : constantCoeff (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h + ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h -
      ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) = 0 := by
    rw [map_sub, map_add (f := _), const_ev (z0_pp 0 2) (h_const Y),
      const_ev (z0_pp 1 2) (h_const Y), const_ev hZ (h_const Y)]
    simp
  have hd1 : ∀ k' : Fin 3, k' ≠ 1 → ∀ j, pderiv (R := C) ((1 : Fin 3), i) (pt C (n := 3) dd k' j) = 0 :=
    fun k' h j => pderiv_pt_ne h i j
  have hA : pderiv (R := C) ((1 : Fin 3), i) (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h) = 0 := by
    rw [pderiv_ev_fst _ _ (z0_pt 0) (z0_pt 2) _ (hd1 2 (by decide)) Y.h]
    exact Finset.sum_eq_zero fun j _ => by rw [hd1 0 (by decide) j, mul_zero]
  have hB : pderiv (R := C) ((1 : Fin 3), i) (ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h) =
      ev (n := 3) ![pt C dd 1, pt C dd 2] (pderiv (R := C) ((0 : Fin 2), i) Y.h) := by
    rw [pderiv_ev_fst _ _ (z0_pt 1) (z0_pt 2) _ (hd1 2 (by decide)) Y.h, sum_pderiv_pt]
  have hFa : ∀ j, pderiv (R := C) ((1 : Fin 3), i) (addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1) j) =
      ev (n := 3) ![pt C dd 0, pt C dd 1] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j)) := by
    intro j
    show pderiv (R := C) _ (ev (n := 3) ![pt C dd 0, pt C dd 1] (Y.B.G.F j)) = _
    rw [pderiv_ev_snd _ _ (z0_pt 0) (z0_pt 1) _ (hd1 0 (by decide)) _, sum_pderiv_pt]
  have hC : pderiv (R := C) ((1 : Fin 3), i) (ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) =
      ∑ j, ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] (pderiv (R := C) ((0 : Fin 2), j) Y.h) *
        ev (n := 3) ![pt C dd 0, pt C dd 1] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j)) := by
    rw [pderiv_ev_fst _ _ (const_addOf Y 0 1) (z0_pt 2) _ (hd1 2 (by decide)) Y.h]
    simp only [hFa]
  have hE1B : ∀ f : PS C 2 dd, ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (ev (n := 3) ![pt C dd 1, pt C dd 2] f) = ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) f := by
    intro f
    rw [ev_ev (z0_pp 1 2) constant_zero_outer_points]
    congr 1
    funext k j; fin_cases k
    · exact eval_outer_points_middle j
    · exact eval_outer_points_last j
  have hE1F : ∀ j, ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1) j) = pt C dd 0 j := by
    intro j
    show ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (ev (n := 3) ![pt C dd 0, pt C dd 1] (Y.B.G.F j)) = _
    rw [ev_ev (z0_pp 0 1) constant_zero_outer_points]
    have e : (fun k j' => ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) ((![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 3 dd) k j')) =
        ![pt C dd 0, 0] := by
      funext k j'; fin_cases k
      · exact eval_outer_points_first j'
      · exact eval_outer_points_middle j'
    rw [e, group_law_zero_right Y _ (z0_pt 0)]
  have hE1C : ∀ f : PS C 2 dd,
      ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] f) = f := by
    intro f
    rw [ev_ev hZ constant_zero_outer_points]
    have e : (fun k j => ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)
        ((![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] : Fin 2 → Pt C 3 dd) k j)) = ![pt C dd 0, pt C dd 1] := by
      funext k j; fin_cases k
      · exact hE1F j
      · exact eval_outer_points_last j
    rw [e, eval_points_two]
  have hE1D : ∀ f : PS C 2 dd, ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (ev (n := 3) ![pt C dd 0, pt C dd 1] f) =
      ev (n := 2) ![pt C dd 0, 0] f := by
    intro f
    rw [ev_ev (z0_pp 0 1) constant_zero_outer_points]
    congr 1
    funext k j; fin_cases k
    · exact eval_outer_points_first j
    · exact eval_outer_points_middle j
  rw [hph, pderiv_expS hg, ← hph, ev_mul constant_zero_outer_points, Y.B.cocycleLeft_zero_snd, one_mul, map_sub, map_add (f := _), ev_sub constant_zero_outer_points,
    ev_add constant_zero_outer_points, hA, ev_zero constant_zero_outer_points, zero_add, hB, hE1B, hC, ev_sum constant_zero_outer_points]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_mul constant_zero_outer_points, hE1C, hE1D]

theorem hs1 (Y : FBChart C V O dd) (i : Fin dd) :
    ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) (pderiv (R := C) ((0 : Fin 2), i) Y.B.sy) =
      ev (n := 2) ![pt C dd 1, 0] (pderiv (R := C) ((1 : Fin 2), i) Y.h) - ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) (pderiv (R := C) ((0 : Fin 2), i) Y.h) := by
  have hsy : Y.B.sy = FB.expS C (ev (n := 2) ![pt C dd 1, pt C dd 0] Y.h - Y.h) := by
    have := Y.gauge.sy; rwa [toK_self] at this
  have hg : constantCoeff (ev (n := 2) ![pt C dd 1, pt C dd 0] Y.h - Y.h) = 0 := by
    rw [map_sub, const_ev (z0_pp 1 0) (h_const Y), h_const Y, sub_zero]
  have h1 : ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) Y.B.sy = 1 := by
    have hB : Z0 (![pt C dd 1] : Fin 1 → Pt C 2 dd) := z0_1 _ (z0_pt 1)
    have hU : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := by
      intro k i; fin_cases k
      · simp
      · exact z0_pt 0 i
    have e : (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) = fun k j => ev (n := 2) (![pt C dd 1] : Fin 1 → Pt C 2 dd) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) k j) := by
      funext k j; fin_cases k
      · exact (ev_zero hB).symm
      · exact (ev_X hB 0 j).symm
    rw [e, ← ev_ev hU hB, Y.B.symmetry_zero_fst, ev_eq_alg hB, map_one]
  have hd : pderiv (R := C) ((0 : Fin 2), i) (ev (n := 2) ![pt C dd 1, pt C dd 0] Y.h) =
      ev (n := 2) ![pt C dd 1, pt C dd 0] (pderiv (R := C) ((1 : Fin 2), i) Y.h) := by
    rw [pderiv_ev_snd _ _ (z0_pt 1) (z0_pt 0) _ (fun j => pderiv_pt_ne (by decide) i j) Y.h, sum_pderiv_pt]
  have hE : ∀ f : PS C 2 dd, ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) (ev (n := 2) ![pt C dd 1, pt C dd 0] f) = ev (n := 2) ![pt C dd 1, 0] f := by
    intro f
    rw [ev_ev (z0_pp 1 0) constant_zero_second_axis]
    congr 1
    funext k j; fin_cases k
    · exact ev_X constant_zero_second_axis 1 j
    · exact ev_X constant_zero_second_axis 0 j
  rw [hsy, pderiv_expS hg, ← hsy, ev_mul constant_zero_second_axis, h1, one_mul, map_sub, ev_sub constant_zero_second_axis, hd, hE]

end RowTiePCEqM

open RowTiePCEqM

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem germIIM_holds (Y : FBChart C V O dd) : GermIIMSt Y := by
  intro v hv
  have key : (∑ j : Fin dd, (∑ i : Fin dd, MvPowerSeries.C (v i) *
        ev (n := 2) ![pt C dd 0, 0] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j))) * pderiv (R := C) ((0 : Fin 2), j) Y.h) +
        ev (n := 2) ![pt C dd 1] (Y.sgP v) =
      -(∑ i, MvPowerSeries.C (v i) * ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (pderiv (R := C) ((1 : Fin 3), i) Y.B.ph1)) +
        -∑ i, MvPowerSeries.C (v i) * ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) (pderiv (R := C) ((0 : Fin 2), i) Y.B.sy) := by
    rw [ev_sgP Y v _ (z0_pt 1)]
    simp only [hi1, hs1, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin dd))) (t := (Finset.univ : Finset (Fin dd)))]
    have e : ∀ i j, MvPowerSeries.C (v i) * ev (n := 2) ![pt C dd 0, 0] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j)) *
        pderiv (R := C) ((0 : Fin 2), j) Y.h = MvPowerSeries.C (v i) * (pderiv (R := C) ((0 : Fin 2), j) Y.h *
          ev (n := 2) ![pt C dd 0, 0] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j))) := fun i j => by ring
    simp only [e]
    ring
  rw [key]
  exact intS_add (intS_neg (intS_sum _ fun i _ => intS_C_mul (hv i) (intS_ev constant_zero_outer_points integral_outer_points (intS_pderiv Y.intPh1 _))))
    (intS_neg (intS_sum _ fun i _ => intS_C_mul (hv i) (intS_ev constant_zero_second_axis integral_second_axis_points (intS_pderiv Y.intSy _))))

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

open PartialDerivEval RowTiePCEqM

namespace RowTiePCEqEx

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem pderiv_eval_single {n : ℕ} {a : Fin 1 → Pt C n dd} (ha : Z0 a) (f : PS C 1 dd) (q : Fin n × Fin dd) :
    pderiv (R := C) q (ev a f) = ∑ j, ev a (pderiv (R := C) ((0 : Fin 1), j) f) * pderiv (R := C) q (a 0 j) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin dd => a p.1 p.2) (fun p => ha p.1 p.2) f q,
    Fintype.sum_prod_type, Fin.sum_univ_one]

theorem germEval_oneStandardPoint_self (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0] f = f := by
  unfold ev
  have : (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [this, subst_self]
  rfl

theorem constantCoeff_pderiv {σ : Type} (q : σ) (f : MvPowerSeries σ C) :
    constantCoeff (pderiv (R := C) q f) = coeff (Finsupp.single q 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
  simp

theorem ev_zero_pt {n : ℕ} (f : PS C 1 dd) : ev (n := n) (![0] : Fin 1 → Pt C n dd) f = MvPowerSeries.C (constantCoeff f) := by
  have hZ : Z0 (![0] : Fin 1 → Pt C n dd) := by
    intro k i; fin_cases k; simp
  have h1 : f = MvPowerSeries.C (constantCoeff f) + (f - MvPowerSeries.C (constantCoeff f)) := by ring
  conv_lhs => rw [h1]
  rw [ev_add hZ, ev_C]
  have h2 : ev (n := n) (![0] : Fin 1 → Pt C n dd) (f - MvPowerSeries.C (constantCoeff f)) = 0 := by
    unfold ev
    have e : (fun p : Fin 1 × Fin dd => (![0] : Fin 1 → Pt C n dd) p.1 p.2) = fun _ => 0 := by
      funext p
      obtain ⟨k, j⟩ := p
      fin_cases k
      rfl
    rw [e]
    exact RowTiePCEqSum.subst_zero_const _ (by simp)
  rw [h2, add_zero]

theorem ex_lin (Y : FBChart C V O dd) (i m : Fin dd) :
    constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (Y.ex m)) = if i = m then 1 else 0 := by
  have hZ : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd) := z0_1 _ Y.ex_const
  have h : constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (comp1 Y.lg Y.ex m)) =
      constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (pt C (n := 1) dd 0 m)) := by
    rw [Y.lg_ex]
  unfold comp1 at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pderiv_eval_single hZ, map_sum] at h
  simp only [map_mul, constantCoeff_ev hZ, constantCoeff_pderiv] at h
  have hl : ∀ k, coeff (Finsupp.single ((0 : Fin 1), k) 1) (Y.lg m) = if k = m then 1 else 0 := by
    intro k
    rw [Y.lg_lin m _ (by simp), coeff_X]
    by_cases hk : k = m
    · rw [if_pos hk, if_pos (by rw [hk])]
    · rw [if_neg hk, if_neg]
      intro e
      exact hk (Prod.mk.inj (Finsupp.single_left_injective one_ne_zero e)).2
  simp only [hl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [← constantCoeff_pderiv] at h
  change constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (Y.ex m)) =
    coeff (Finsupp.single ((0 : Fin 1), i) 1) (X ((0 : Fin 1), m) : PS C 1 dd) at h
  rw [h, coeff_X]
  by_cases him : i = m
  · rw [if_pos him, if_pos (by rw [him])]
  · rw [if_neg him, if_neg]
    intro e
    exact him (Prod.mk.inj (Finsupp.single_left_injective one_ne_zero e)).2

end RowTiePCEqEx

namespace RowTiePCEqEx

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem ex_add (Y : FBChart C V O dd) (j : Fin dd) :
    ev (n := 2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j) =
      ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] (Y.B.G.F j) := by
  have hA0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 0) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 0)) (Y.ex_const m)
  have hB0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 1) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 1)) (Y.ex_const m)
  have hAB : Z0 (![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) := by
    intro k i; fin_cases k
    · exact hA0 i
    · exact hB0 i
  have hZex : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd) := z0_1 _ Y.ex_const
  have hlgk : ∀ (k : Fin 2) m, ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd k)] (Y.lg m) = pt C dd k m := by
    intro k m
    have e : ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd k)] (Y.lg m) =
        ev (n := 2) ![pt C dd k] (ev (n := 1) ![Y.ex] (Y.lg m)) := by
      rw [ev_ev hZex (z0_1 _ (z0_pt k))]
      congr 1
      funext k' i
      fin_cases k'
      rfl
    rw [e, show ev (n := 1) ![Y.ex] (Y.lg m) = comp1 Y.lg Y.ex m from rfl, Y.lg_ex,
      show (pt C (n := 1) dd 0 m) = X ((0 : Fin 1), m) from rfl, ev_X (z0_1 _ (z0_pt k))]
    rfl
  set P : Pt C 2 dd := fun j => ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)]
    (Y.B.G.F j) with hP
  have hP0 : ∀ m, constantCoeff (P m) = 0 := fun m => const_ev hAB (Y.B.G.const m)
  have hZP : Z0 (![P] : Fin 1 → Pt C 2 dd) := z0_1 _ hP0
  have hPl : ∀ m, ev (n := 2) ![P] (Y.lg m) = pt C (n := 2) dd 0 m + pt C dd 1 m := by
    intro m
    have e1 : ev (n := 2) ![P] (Y.lg m) =
        ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)]
          (ev (n := 2) ![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1)] (Y.lg m)) := by
      rw [ev_ev (z0_1 _ (const_addOf Y 0 1)) hAB]
      congr 1
      funext k i
      fin_cases k
      show P i = _
      rw [hP]
      exact congrArg _ (addOf_pts Y.B.G.F i).symm
    rw [e1, Y.lg_add m, ev_add hAB, ev_ev (z0_1 _ (z0_pt 0)) hAB, ev_ev (z0_1 _ (z0_pt 1)) hAB]
    have e2 : ∀ k : Fin 2, (fun k' i => ev (n := 2)
        (![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd)
        ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) k' i)) = ![comp1 Y.ex (pt C (n := 2) dd k)] := by
      intro k
      funext k' i
      fin_cases k'
      show ev (n := 2) _ (X (k, i) : PS C 2 dd) = _
      rw [ev_X hAB]
      fin_cases k <;> rfl
    rw [e2 0, e2 1, hlgk 0, hlgk 1]
  have hPS : ∀ j, P j = ev (n := 2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j) := by
    intro j
    have e1 : ev (n := 2) ![P] (comp1 Y.ex Y.lg j) = P j := by
      rw [Y.ex_lg, show (pt C (n := 1) dd 0 j) = X ((0 : Fin 1), j) from rfl, ev_X hZP]
      rfl
    rw [← e1]
    unfold comp1
    rw [ev_ev (z0_1 _ Y.lg_const) hZP]
    congr 1
    funext k i
    fin_cases k
    exact hPl i
  exact (hPS j).symm

end RowTiePCEqEx


open RowTiePCEqEx in
theorem exDer_holds {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) : ExDerSt Y := by
  intro v j
  have hZex : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd) := z0_1 _ Y.ex_const
  have hQ : Z0 ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)) := z0_p0 _ (z0_pt 0)
  have hS0 : ∀ m, constantCoeff (pt C (n := 2) dd 0 m + pt C dd 1 m) = 0 := fun m => by
    rw [map_add (f := _), z0_pt, z0_pt, add_zero]
  have hZS : Z0 (![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) := z0_1 _ hS0
  have hA0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 0) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 0)) (Y.ex_const m)
  have hB0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 1) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 1)) (Y.ex_const m)
  have hAB : Z0 (![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) := by
    intro k i; fin_cases k
    · exact hA0 i
    · exact hB0 i
  have pderiv_pt_ne {k : Fin 2} (hk : k ≠ 1) (i m : Fin dd) :
      pderiv (R := C) ((1 : Fin 2), i) (pt C dd k m) = 0 :=
    pderiv_X_of_ne (fun e => hk (Prod.mk.inj e).1)
  have sum_pderiv_pt (i : Fin dd) (a : Fin dd → PS C 2 dd) :
      ∑ m, a m * pderiv (R := C) ((1 : Fin 2), i) (pt C dd 1 m) = a i := by
    rw [Finset.sum_eq_single i]
    · rw [show pt C dd 1 i = X ((1 : Fin 2), i) from rfl, pderiv_X_self, mul_one]
    · intro m _ hm
      rw [show pt C dd 1 m = X ((1 : Fin 2), m) from rfl,
        pderiv_X_of_ne (fun e => hm (Prod.mk.inj e).2), mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hdk : ∀ (k : Fin 2) (i m : Fin dd), pderiv (R := C) ((1 : Fin 2), i) (comp1 Y.ex (pt C (n := 2) dd k) m) =
      if k = 1 then ev (n := 2) ![pt C dd 1] (pderiv (R := C) ((0 : Fin 1), i) (Y.ex m)) else 0 := by
    intro k i m
    show pderiv (R := C) _ (ev (n := 2) ![pt C (n := 2) dd k] (Y.ex m)) = _
    rw [pderiv_eval_single (z0_1 _ (z0_pt k))]
    split_ifs with hk
    · subst hk
      exact sum_pderiv_pt i _
    · exact Finset.sum_eq_zero fun l _ => by
        rw [show ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) 0 l) = pt C dd k l from rfl, pderiv_pt_ne hk i l,
          mul_zero]
  have hpt1 : ∀ k : Fin 2, (fun k' l => ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) k' l)) =
      ![((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)) k] := by
    intro k
    funext k' l
    fin_cases k'
    exact ev_X hQ k l
  have hL : ∀ i, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (pderiv (R := C) ((1 : Fin 2), i)
      (ev (n := 2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j))) = pderiv (R := C) ((0 : Fin 1), i) (Y.ex j) := by
    intro i
    rw [pderiv_eval_single hZS]
    have e0 : ∀ m, pderiv (R := C) ((1 : Fin 2), i)
        ((![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) 0 m) =
        pderiv (R := C) ((1 : Fin 2), i) (pt C (n := 2) dd 1 m) := fun m => by
      show pderiv (R := C) _ (pt C (n := 2) dd 0 m + pt C dd 1 m) = _
      rw [map_add (f := _), pderiv_pt_ne (by decide) i m, zero_add]
    simp only [e0]
    rw [sum_pderiv_pt i, ev_ev hZS hQ]
    have e : (fun k m => ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
        ((![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) k m)) = ![pt C (n := 1) dd 0] := by
      funext k m
      fin_cases k
      show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((X ((0 : Fin 2), m) : PS C 2 dd) + X ((1 : Fin 2), m)) = pt C dd 0 m
      rw [ev_add hQ, ev_X hQ, ev_X hQ]
      show pt C dd 0 m + 0 = pt C dd 0 m
      rw [add_zero]
    rw [e, germEval_oneStandardPoint_self]
  have eB : ∀ g : PS C 1 dd, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 1] g) = MvPowerSeries.C (constantCoeff g) := by
    intro g
    rw [ev_ev (z0_1 _ (z0_pt 1)) hQ, hpt1 1]
    exact ev_zero_pt g
  have eAB : ∀ f : PS C 2 dd, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
      (ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] f) =
      ev (n := 1) ![Y.ex, 0] f := by
    intro f
    rw [ev_ev hAB hQ]
    congr 1
    funext k m
    fin_cases k
    · show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 0] (Y.ex m)) = Y.ex m
      rw [ev_ev (z0_1 _ (z0_pt 0)) hQ, hpt1 0]
      exact germEval_oneStandardPoint_self _
    · show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 1] (Y.ex m)) = 0
      rw [eB, Y.ex_const, map_zero]
  have hR : ∀ i, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (pderiv (R := C) ((1 : Fin 2), i)
      (ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] (Y.B.G.F j))) =
      ev (n := 1) ![Y.ex] (ev (n := 1) ![pt C dd 0, 0] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j))) := by
    intro i
    rw [pderiv_eval_pair hAB]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hdk,
      ite_eq_right (by decide : (0 : Fin 2) ≠ 1), ite_true,
      mul_zero, Finset.sum_const_zero, zero_add]
    rw [ev_sum hQ]
    simp only [ev_mul hQ, eAB, eB, ex_lin]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, map_one, mul_one, ev_ev (z0_p0 _ (z0_pt 0)) hZex]
      congr 1
      funext k m
      fin_cases k
      · exact (ev_X hZex 0 m).symm
      · exact (ev_zero hZex).symm
    · intro m _ hm
      rw [if_neg (Ne.symm hm), map_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : ∀ i, pderiv (R := C) ((0 : Fin 1), i) (Y.ex j) =
      ev (n := 1) ![Y.ex] (ev (n := 1) ![pt C dd 0, 0] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j))) := by
    intro i
    rw [← hL i, ex_add Y j, hR i]
  unfold FBChart.dF
  rw [ev_sum hZex]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_mul hZex, ev_C, key i]

end Formalism.L2.FormalSeriesBounds
