module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalLogEqSumOfMultiplicativeParam

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ChartInv

variable {k : Type} [CommRing k] {d : ℕ}

theorem formalComp_apply_eq_mvPowerSeries_subst (φ ψ : Pt k 1 d) (i : Fin d) :
    comp1 φ ψ i = (φ i).subst (fun p : Fin 1 × Fin d => ψ p.2) := by
  unfold comp1 ev
  congr 1
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  rfl

theorem linearPart_eq_submatrix (φ : Pt k 1 d) :
    GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2) =
      (dLin φ).submatrix (Equiv.uniqueProd (Fin d) (Fin 1)) (Equiv.uniqueProd (Fin d) (Fin 1)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  obtain rfl : b = 0 := Subsingleton.elim _ _
  rfl

theorem exists_isInvPair :
    ∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) →
      IsUnit (dLin φ).det → ∃ φi : Pt k 1 d, IsInvPair φ φi := by
  intro k _ d φ h0 hdet
  have hu : ∀ p : Fin 1 × Fin d, constantCoeff ((fun p : Fin 1 × Fin d => φ p.2) p) = 0 :=
    fun p => h0 p.2
  have hA : IsUnit (GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2)) := by
    rw [Matrix.isUnit_iff_isUnit_det, linearPart_eq_submatrix, Matrix.det_submatrix_equiv_self]
    exact hdet
  obtain ⟨v, hv, h1, h2⟩ := (GlobalTheory.FormalInv.exists_substInv_iff hu).2 hA
  have hvv : (fun p : Fin 1 × Fin d => v (0, p.2)) = v := by
    funext ⟨a, j⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  refine ⟨fun i => v (0, i), h0, fun i => hv _, ?_, ?_⟩
  · funext i
    rw [formalComp_apply_eq_mvPowerSeries_subst, hvv]
    exact h1 (0, i)
  · funext i
    rw [formalComp_apply_eq_mvPowerSeries_subst]
    exact h2 (0, i)

end GlobalTheory.ChartInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartTrans

variable {k : Type} [CommRing k] {d : ℕ}

theorem pderiv_ev {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (f : PS k m d)
    (v : Fin n × Fin d) :
    pderiv v (ev V f) = ∑ j : Fin m, ∑ l : Fin d, ev V (pderiv (j, l) f) * pderiv v (V j l) := by
  unfold ev
  rw [GlobalTheory.FormalCalc.pderiv_subst (gt_hasSubst V hV), Fintype.sum_prod_type]

theorem ev_sum {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) {α : Type} (s : Finset α)
    (f : α → PS k m d) : ev V (∑ a ∈ s, f a) = ∑ a ∈ s, ev V (f a) :=
  GlobalTheory.FormalCalc.subst_sum' (gt_hasSubst V hV) s f

theorem ev_C {m n : ℕ} (V : Fin m → Pt k n d) (r : k) : ev V (C r : PS k m d) = C r := by
  unfold ev
  rw [MvPowerSeries.subst_C]

theorem ev_C_mul {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (r : k) (f : PS k m d) :
    ev V (C r * f) = C r * ev V f := by
  rw [gt_ev_mul V hV, ev_C]

theorem vec1 {m n : ℕ} (V : Fin m → Pt k n d) (a : Pt k m d) :
    (fun j => evP V (![a] j)) = ![evP V a] := by
  funext j; fin_cases j; rfl

theorem ev_at_zero {n : ℕ} (f : PS k 1 d) : ev ![(0 : Pt k n d)] f = C (constantCoeff f) := by
  have e : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  conv_lhs => rw [e]
  rw [gt_ev_add _ (single_point_zero_constant gp_zero₂), ev_C]
  have h2 : ev ![(0 : Pt k n d)] (f - C (constantCoeff f)) = 0 := by
    change MvPowerSeries.subst (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) _ = 0
    have e : (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) = 0 := by
      funext p; simp
    rw [e]
    exact MvPowerSeries.subst_zero_of_constantCoeff_zero h0
  rw [h2, add_zero]

theorem axis_GP : ∀ j, GP ((![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) j) :=
  pair_points_zero_constant (gp_pt 0) gp_zero₂

theorem dof_eq (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof F u g = ∑ i, C (u i) *
      ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv ((1 : Fin 2), i) (ev (n := 2) ![F] g)) := by
  have hF1 : ∀ j, GP ((![F] : Fin 1 → Pt k 2 d) j) := single_point_zero_constant hF
  have hS : ∀ h : PS k 1 d, ev (n := 1) ![pt k (n := 1) d 0, 0] (ev (n := 2) ![F] h) = h := by
    intro h
    rw [gt_ev_ev' _ _ axis_GP hF1, vec1]
    have : evP ![pt k (n := 1) d 0, 0] F = pt k (n := 1) d 0 := funext hu
    rw [this, gt_ev_pt_self]
  unfold Dof
  simp only [pderiv_ev _ hF1, Fin.sum_univ_one, ev_sum _ axis_GP, gt_ev_mul _ axis_GP, hS,
    Finset.mul_sum, Finset.sum_mul, Matrix.cons_val_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pderiv_comp_pt (φ : Pt k 1 d) (a b : Fin 2) (i l : Fin d) :
    pderiv (a, i) (comp1 φ (pt k (n := 2) d b) l) =
      if a = b then ev ![pt k (n := 2) d b] (pderiv ((0 : Fin 1), i) (φ l)) else 0 := by
  change pderiv (a, i) (ev ![pt k (n := 2) d b] (φ l)) = _
  rw [pderiv_ev _ (single_point_zero_constant (gp_pt b)), Fin.sum_univ_one]
  simp only [Matrix.cons_val_zero, pt]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [pderiv_X_of_ne (by simpa using hj), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_X_of_ne (fun h' => h (congrArg Prod.fst h').symm), mul_zero]

theorem axis_pderiv_comp (φ : Pt k 1 d) (hφ : GP φ) (H : PS k 2 d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv ((1 : Fin 2), i)
      (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] H)) =
    ∑ l, C (dLin φ l i) *
      ev ![φ] (ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv ((1 : Fin 2), l) H)) := by
  have hΦ : ∀ j, GP (![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] j) :=
    pair_points_zero_constant (gp_comp1 φ _ hφ (gp_pt 0)) (gp_comp1 φ _ hφ (gp_pt 1))
  have hK : ∀ K : PS k 2 d, ev (n := 1) ![pt k (n := 1) d 0, 0]
      (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] K) =
      ev ![φ] (ev (n := 1) ![pt k (n := 1) d 0, 0] K) := by
    intro K
    rw [gt_ev_ev' _ _ axis_GP hΦ, eval_pair_points, evP_comp1 _ axis_GP φ _ (gp_pt 0),
      evP_comp1 _ axis_GP φ _ (gp_pt 1), evP_pt _ axis_GP, evP_pt _ axis_GP,
      gt_ev_ev' _ _ (single_point_zero_constant hφ) axis_GP, eval_pair_points, evP_pt _ (single_point_zero_constant hφ), evP_zero _ (single_point_zero_constant hφ)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [gt_comp1_pt_right, gt_comp1_zero φ hφ]
  have hL : ∀ l, ev (n := 1) ![pt k (n := 1) d 0, 0]
      (ev ![pt k (n := 2) d 1] (pderiv ((0 : Fin 1), i) (φ l))) = C (dLin φ l i) := by
    intro l
    rw [gt_ev_ev' _ _ axis_GP (single_point_zero_constant (gp_pt 1)), vec1, evP_pt _ axis_GP]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ev_at_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
    simp [dLin]
  rw [pderiv_ev _ hΦ, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_comp_pt]
  simp only [one_ne_zero, ite_false, ite_true, mul_zero, Finset.sum_const_zero, zero_add]
  rw [ev_sum _ axis_GP]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [gt_ev_mul _ axis_GP, hK, hL, mul_comm]

theorem dof_transF (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (φ φi : Pt k 1 d) (hinv : IsInvPair φ φi) (u : Fin d → k) (g : PS k 1 d) :
    Dof (transF F φ φi) u (ev (n := 1) ![φ] g) =
      ev (n := 1) ![φ] (Dof F ((dLin φ).mulVec u) g) := by
  have hφ : GP φ := hinv.1
  have hφi : GP φi := hinv.2.1
  have h0 : GP (comp1 φ (pt k (n := 2) d 0)) := gp_comp1 φ _ hφ (gp_pt 0)
  have h1 : GP (comp1 φ (pt k (n := 2) d 1)) := gp_comp1 φ _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have hA := gp_addOf F hF _ _ h0 h1
  have eF : transF F φ φi =
      comp1 φi (addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) := rfl
  have hF' : GP (transF F φ φi) := eF ▸ gp_comp1 φi _ hφi hA
  have hax : addOf F φ 0 = φ := by
    have e1 : addOf F (pt k (n := 1) d 0) 0 = pt k (n := 1) d 0 := funext hu
    have e2 := congrArg (evP ![φ]) e1
    rwa [evP_addOf _ (single_point_zero_constant hφ) _ _ _ (gp_pt 0) gp_zero₂, evP_pt _ (single_point_zero_constant hφ),
      evP_zero _ (single_point_zero_constant hφ)] at e2
  have hu' : evP ![pt k (n := 1) d 0, 0] (transF F φ φi) = pt k (n := 1) d 0 := by
    rw [eF, evP_comp1 _ axis_GP _ _ hA, evP_addOf _ axis_GP _ _ _ h0 h1,
      evP_comp1 _ axis_GP φ _ (gp_pt 0), evP_comp1 _ axis_GP φ _ (gp_pt 1),
      evP_pt _ axis_GP, evP_pt _ axis_GP]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [gt_comp1_pt_right, gt_comp1_zero φ hφ, hax, hinv.2.2.2]
  have key : ev (n := 2) ![transF F φ φi] (ev (n := 1) ![φ] g) =
      ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (ev (n := 2) ![F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF') (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF), vec1]
    have : evP ![transF F φ φi] φ = evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] F :=
      gt_comp_inv hinv _ hA
    rw [this]
  rw [dof_eq _ hF' (congrFun hu'), dof_eq F hF hu, key, ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp φ hφ, ev_C_mul _ (single_point_zero_constant hφ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem transPolySt : TransPolySt := by
  intro k _ d F hF hu φ φi hinv ι _ u P g
  have hφ : GP φ := hinv.1
  have hit : ∀ (v : Fin d → k) (n : ℕ) (g : PS k 1 d),
      (Dof (transF F φ φi) v)^[n] (ev (n := 1) ![φ] g) =
        ev (n := 1) ![φ] ((Dof F ((dLin φ).mulVec v))^[n] g) := by
    intro v n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dof_transF F hF hu φ φi hinv, ih]
  have hmon : ∀ m : ι →₀ ℕ, DmonOf (transF F φ φi) u m (ev (n := 1) ![φ] g) =
      ev (n := 1) ![φ] (DmonOf F (fun l => (dLin φ).mulVec (u l)) m g) := by
    intro m
    unfold DmonOf
    induction (Finset.univ : Finset ι).toList with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  unfold DpolyOf
  rw [ev_sum _ (single_point_zero_constant hφ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_C_mul _ (single_point_zero_constant hφ), hmon]

end GlobalTheory.ChartTrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermExpAddAndEvConst
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem germ_expS_add : G2.ExpAddZeroConstant :=
  fun _ _ _ _ _ f g hf hg => WickVanishing.gt_expS_add f g hf hg

theorem germ_constantCoeff_ev : G2.ConstantCoeffSubstitution :=
  fun _ _ _ _ _ a f ha => WickVanishing.gt_const_ev_eq a ha f

theorem germ_expAdd_and_evConst : G2.ExpAddZeroConstant ∧ G2.ConstantCoeffSubstitution :=
  ⟨germ_expS_add, germ_constantCoeff_ev⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeSubIsBiadd
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory

theorem canonGauge_sub_isBiadd : G2.CanonicalGaugeDiffBiadditive := by
  intro R _ d O _ _ k _ _ _ B h h' hh hh'
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hF : ∀ i, constantCoeff (B.FK k i) = 0 := fun i => by
    simp only [FB.FK, FGLaw.mapF, MvPowerSeries.constantCoeff_map, B.G.const i, map_zero]
  have hA : ∀ a, GP (B.actK k a) := fun a i => by
    simp only [FB.actK, MvPowerSeries.constantCoeff_map, B.A.const a i, map_zero]
  have h0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero] at this
  have h0' : constantCoeff h' = 0 := by
    have := congrArg constantCoeff hh'.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero] at this
  have inj : ∀ {n : ℕ} {a b : PS k n d}, constantCoeff a = 0 → constantCoeff b = 0 →
      FB.expS k a = FB.expS k b → a = b := fun ha hb e => exp_inj ha hb e
  refine ⟨?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_sub _ (pair_points_zero_constant hz (hp 0)), hh.ax0, hh'.ax0, sub_zero]
  · rw [gt_ev_sub _ (pair_points_zero_constant (hp 0) hz), hh.ax1, hh'.ax1, sub_zero]
  · have a1 := pair_points_zero_constant (hp (n := 3) 0) (hp 2)
    have a2 := pair_points_zero_constant (hp (n := 3) 1) (hp 2)
    have a3 := pair_points_zero_constant (gp_addOf _ hF _ _ (hp (n := 3) 0) (hp 1)) (hp 2)
    have e := inj
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp)
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp)
      (hh.ph1.symm.trans hh'.ph1)
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]
    linear_combination -e
  · have a1 := pair_points_zero_constant (hp (n := 3) 0) (hp 1)
    have a2 := pair_points_zero_constant (hp (n := 3) 0) (hp 2)
    have a3 := pair_points_zero_constant (hp (n := 3) 0) (gp_addOf _ hF _ _ (hp (n := 3) 1) (hp 2))
    have e := inj
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp)
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp)
      (hh.ph2.symm.trans hh'.ph2)
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]
    linear_combination -e
  · have a1 := pair_points_zero_constant (gp_comp1 _ _ (hA a) (hp (n := 2) 0)) (hp 1)
    have a2 := pair_points_zero_constant (hp (n := 2) 0) (gp_comp1 _ _ (hA (star a)) (hp (n := 2) 1))
    have e := inj
      (by rw [map_sub, gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, sub_zero])
      (by rw [map_sub, gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', sub_zero])
      ((hh.ad a).symm.trans (hh'.ad a))
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2]
    linear_combination -e

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.EqZeroOfAdditiveOfPderiv
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.AdditiveSeries

variable {k : Type} [CommRing k] {d : ℕ}

theorem gp_cons {m n : ℕ} {x : Pt k n d} {y : Fin m → Pt k n d} (hx : GP x) (hy : ∀ j, GP (y j)) :
    ∀ j, GP ((Fin.cons x y : Fin (m + 1) → Pt k n d) j) :=
  Fin.cases (by simpa using hx) (by simpa using hy)

theorem gp_pair {n : ℕ} {x y : Pt k n d} (hx : GP x) (hy : GP y) :
    ∀ j, GP ((![x, y] : Fin 2 → Pt k n d) j) := by
  intro j; fin_cases j; exacts [hx, hy]

theorem gp_single {n : ℕ} {x : Pt k n d} (hx : GP x) :
    ∀ j, GP ((![x] : Fin 1 → Pt k n d) j) := by
  intro j; fin_cases j; exact hx

theorem ev_pt {n : ℕ} (f : PS k n d) : ev (fun j => pt k d j) f = f :=
  congrFun subst_self f

theorem pderiv_ev_cons {m n : ℕ} {x : Pt k n d} {y : Fin m → Pt k n d} (hx : GP x)
    (hy : ∀ j, GP (y j)) (v : Fin n × Fin d) (hv : ∀ j i, pderiv (R := k) v (y j i) = 0)
    (g : PS k (m + 1) d) :
    pderiv (R := k) v (ev (Fin.cons x y) g) =
      ∑ l, ev (Fin.cons x y) (pderiv (R := k) ((0 : Fin (m + 1)), l) g) * pderiv (R := k) v (x l) := by
  unfold ev
  rw [FormalCalc.pderiv_subst'
    (fun p : Fin (m + 1) × Fin d => gp_cons hx hy p.1 p.2), Fintype.sum_prod_type,
    Fin.sum_univ_succ]
  simp [hv]

theorem ev_ev_cons {l m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, GP (V j)) {x : Pt k m d}
    {y : Fin l → Pt k m d} (hx : GP x) (hy : ∀ j, GP (y j)) (g : PS k (l + 1) d) :
    ev V (ev (Fin.cons x y) g) =
      ev (Fin.cons (fun i => ev V (x i)) fun j i => ev V (y j i)) g := by
  rw [gt_ev_ev V _ hV (gp_cons hx hy)]
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem ev_pt_apply {m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, GP (V j)) (j : Fin m)
    (i : Fin d) : ev V (pt k d j i) = V j i := gt_ev_X V hV j i

theorem ev_addOf {m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, GP (V j)) (F : Fin d → PS k 2 d)
    (a b : Fin m) (i : Fin d) :
    ev V (addOf F (pt k d a) (pt k d b) i) = addOf F (V a) (V b) i := by
  unfold addOf
  rw [gt_ev_ev V _ hV (gp_pair (gp_pt a) (gp_pt b))]
  congr 1
  funext j i
  fin_cases j <;> simp [ev_pt_apply hV]

theorem zero_addOf {n : ℕ} (G : FGLaw k d) {x : Pt k n d} (hx : GP x) : addOf G.F 0 x = x := by
  funext i
  have h := congrArg (ev ![x]) (G.unit i)
  rw [gt_ev_ev _ _ (gp_single hx) (gp_pair gp_zero₂ (gp_pt 0)),
    gt_ev_X _ (gp_single hx)] at h
  refine Eq.trans ?_ h
  unfold addOf
  congr 1
  funext j i
  fin_cases j <;> simp [ev_pt_apply (gp_single hx), gt_ev_zero _ (gp_single hx)]

theorem addOf_zero {n : ℕ} (G : FGLaw k d) {x : Pt k n d} (hx : GP x) : addOf G.F x 0 = x := by
  funext i
  have hz : GP (0 : Pt k n d) := gp_zero₂
  have h := congrArg (ev ![x, 0]) (G.comm i)
  rw [gt_ev_ev _ _ (gp_pair hx hz) (gp_pair (gp_pt 1) (gp_pt 0))] at h
  refine Eq.trans h.symm (Eq.trans ?_ (congrFun (zero_addOf G hx) i))
  unfold addOf
  congr 1
  funext j i
  fin_cases j <;> simp [ev_pt_apply (gp_pair hx hz)]

theorem pderiv_pt {n : ℕ} (a b : Fin n) (i l : Fin d) :
    pderiv (R := k) (a, i) (pt k d b l) = if b = a ∧ l = i then 1 else 0 := by
  simp [pt, FormalCalc.pderiv_X_ite]

theorem constantCoeff_pderiv_addOf {q : ℕ} (G : FGLaw k d) (i l : Fin d) :
    constantCoeff (pderiv (R := k) ((0 : Fin (q + 2)), i)
      (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1) l)) = if l = i then 1 else 0 := by
  have hx : GP (pt k d (0 : Fin 1)) := gp_pt 0
  have hy : ∀ j, GP ((fun _ => 0 : Fin (q + 1) → Pt k 1 d) j) := fun _ => gp_zero₂
  have h := pderiv_ev_cons hx hy ((0 : Fin 1), i) (by simp)
    (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1) l)
  rw [ev_addOf (gp_cons hx hy)] at h
  have e1 : (Fin.cons (pt k d (0 : Fin 1)) (fun _ => 0) : Fin (q + 2) → Pt k 1 d) 1 = 0 := rfl
  rw [e1, Fin.cons_zero, addOf_zero G hx] at h
  simp only [pderiv_pt, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  rw [← gt_const_ev_eq _ (gp_cons hx hy), ← h]
  split_ifs <;> simp

theorem eq_zero_of_additive_of_pderiv (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ)
    (G : FGLaw k d) (q : ℕ) (g : PS k (q + 1) d)
    (hadd : ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1))
        (fun j : Fin q => pt k d j.succ.succ)) g =
      ev (n := q + 2) (Fin.cons (pt k d 0) (fun j : Fin q => pt k d j.succ.succ)) g +
      ev (n := q + 2) (Fin.cons (pt k d 1) (fun j : Fin q => pt k d j.succ.succ)) g)
    (hlin : ∀ i, ev (n := q) (Fin.cons 0 (fun j : Fin q => pt k d j))
      (pderiv (R := k) ((0 : Fin (q + 1)), i) g) = 0) : g = 0 := by
  have : HasUniqueDiv k := HasUniqueDiv.of_module_rat k
  have hS : GP (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1)) :=
    gp_addOf _ G.const _ _ (gp_pt _) (gp_pt _)
  have hw : ∀ j : Fin q, GP (pt k d j.succ.succ) := fun _ => gp_pt _
  set V : Fin (q + 2) → Pt k (q + 1) d := Fin.cons 0 fun j => pt k d j with hVdef
  have hV : ∀ j, GP (V j) := gp_cons gp_zero₂ fun _ => gp_pt _
  have hV0 : V 0 = 0 := rfl
  have hV1 : V 1 = pt k d 0 := rfl
  have hVs : ∀ j : Fin q, V j.succ.succ = pt k d j.succ := fun _ => rfl
  have hid : (Fin.cons (pt k d 0) fun j : Fin q => pt k d j.succ :
      Fin (q + 1) → Pt k (q + 1) d) = fun j => pt k d j := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp

  have eS (f : PS k (q + 1) d) : ev V (ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1))
      (fun j : Fin q => pt k d j.succ.succ)) f) = f := by
    rw [ev_ev_cons hV hS hw]
    simp only [ev_addOf hV, ev_pt_apply hV, hV0, hV1, hVs, zero_addOf G (gp_pt _)]
    exact (congrArg (ev · f) hid).trans (ev_pt f)
  have e0 (f : PS k (q + 1) d) : ev V (ev (n := q + 2) (Fin.cons (pt k d 0)
      (fun j : Fin q => pt k d j.succ.succ)) f) =
      ev (Fin.cons 0 fun j : Fin q => pt k d j.succ) f := by
    rw [ev_ev_cons hV (gp_pt _) hw]
    simp only [ev_pt_apply hV, hV0, hVs]
  have e1 (f : PS k (q + 1) d) : ev V (ev (n := q + 2) (Fin.cons (pt k d 1)
      (fun j : Fin q => pt k d j.succ.succ)) f) = f := by
    rw [ev_ev_cons hV (gp_pt _) hw]
    simp only [ev_pt_apply hV, hV1, hVs]
    exact (congrArg (ev · f) hid).trans (ev_pt f)
  have hlin' (i : Fin d) : ev (Fin.cons 0 fun j : Fin q => pt k d j.succ)
      (pderiv (R := k) ((0 : Fin (q + 1)), i) g) = 0 := by
    have hU : ∀ j : Fin q, GP (pt k d j.succ) := fun _ => gp_pt _
    have h := congrArg (ev fun j : Fin q => pt k d j.succ) (hlin i)
    rw [ev_ev_cons hU gp_zero₂ (fun _ => gp_pt _), gt_ev_zero _ hU] at h
    simp only [ev_pt_apply hU, Pi.zero_apply, gt_ev_zero _ hU] at h
    exact h
  have hax : ev (Fin.cons 0 fun j : Fin q => pt k d j.succ) g = 0 := by
    have h := congrArg (ev V) hadd
    rw [gt_ev_add V hV, eS, e0, e1] at h
    simpa using h
  let J : Matrix (Fin d) (Fin d) (PS k (q + 1) d) := Matrix.of fun l i =>
    ev V (pderiv (R := k) ((0 : Fin (q + 2)), i) (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1) l))
  have hJ : IsUnit J := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff, RingHom.map_det]
    have : (constantCoeff : PS k (q + 1) d →+* k).mapMatrix J = 1 := by
      ext l i
      simp [J, gt_const_ev_eq V hV, constantCoeff_pderiv_addOf, Matrix.one_apply]
    rw [this, Matrix.det_one]
    exact isUnit_one
  have hD : Matrix.vecMul (fun l => pderiv (R := k) ((0 : Fin (q + 1)), l) g) J = 0 := by
    funext i
    have hv : ∀ (j : Fin q) (l : Fin d),
        pderiv (R := k) ((0 : Fin (q + 2)), i) (pt k d j.succ.succ l) = 0 := by
      intro j l
      rw [pderiv_pt, ite_eq_right fun h => Fin.succ_ne_zero _ h.1]
    have h := congrArg (pderiv (R := k) ((0 : Fin (q + 2)), i)) hadd
    rw [map_add (f := _), pderiv_ev_cons hS hw _ hv, pderiv_ev_cons (gp_pt _) hw _ hv,
      pderiv_ev_cons (gp_pt _) hw _ hv] at h
    simp only [pderiv_pt, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, one_ne_zero, false_and, ite_false, Finset.sum_const_zero,
      add_zero] at h
    have h2 := congrArg (ev V) h
    rw [e0, hlin'] at h2
    have hs : ∀ f : Fin d → PS k (q + 2) d, ev V (∑ l, f l) = ∑ l, ev V (f l) := fun f => by
      unfold ev
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← coe_substAlgHom (gt_hasSubst V hV), map_sum]
    simp only [hs, gt_ev_mul V hV, eS] at h2
    exact h2
  have hD0 : (fun l => pderiv (R := k) ((0 : Fin (q + 1)), l) g) = 0 := by
    obtain ⟨u, hu⟩ := hJ.exists_right_inv
    have h := congrArg (fun v => Matrix.vecMul v u) hD
    simpa [Matrix.vecMul_vecMul, hu] using h
  refine FormalCalc.ext_of_pderiv_of_subst (fun i : Fin d => ((0 : Fin (q + 1)), i))
    (b := fun p : Fin (q + 1) × Fin d =>
      (Fin.cons 0 fun j : Fin q => pt k d j.succ : Fin (q + 1) → Pt k (q + 1) d) p.1 p.2)
    (fun _ => rfl) ?_ (fun i => ?_) ?_
  · rintro ⟨j, i⟩ hj
    revert hj
    refine Fin.cases (fun hj => ?_) (fun j _ => rfl) j
    exact absurd ⟨i, rfl⟩ hj
  · simpa using congrFun hD0 i
  · exact hax.trans (gt_ev_zero _ (gp_cons gp_zero₂ fun _ => gp_pt _)).symm

end GlobalTheory.AdditiveSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGaugeOfSymmetry
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.SymGauge

variable {k : Type} [CommRing k] {d : ℕ}

theorem ev_C_mul {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (c : k) (f : PS k m d) :
    ev V (C c * f) = C c * ev V f := by
  rw [gt_ev_mul V hV]
  congr 1
  unfold ev
  rw [MvPowerSeries.subst_C]

theorem expS_inj [Algebra ℚ k] {n : ℕ} {f g : PS k n d} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) (h : FB.expS k f = FB.expS k g) : f = g := exp_inj hf hg h

theorem expS_zero [Algebra ℚ k] {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := exp_zero

theorem exists_gauge_of_symmetry :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → (∀ a, B.ad a = 1) → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ (∀ a : O, (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) = 0) ∧ B.sy = FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) := by
  intro k _ _ d O _ _ B h1 h2 had
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hF : ∀ i, constantCoeff (B.G.F i) = 0 := B.G.const
  have hsy1 : constantCoeff B.sy = 1 := by
    have := congrArg constantCoeff B.symmetry_zero_fst
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one] at this
  obtain ⟨s, hs0, hs⟩ : ∃ s : PS k 2 d, constantCoeff s = 0 ∧ FB.expS k s = B.sy :=
    ⟨_, constantCoeff_logS hsy1, exp_log hsy1⟩
  have E : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ev ![a, b] B.sy = FB.expS k (ev ![a, b] s) := by
    intro n a b ha hb
    rw [← hs, gt_ev_expS _ (pair_points_zero_constant ha hb) _ hs0]
  have c0 : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → constantCoeff (ev ![a, b] s) = 0 :=
    fun a b ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) _ hs0

  have anti0 : s + ev (n := 2) ![pt k d 1, pt k d 0] s = 0 := by
    have e := B.sy_inv
    rw [E _ _ (hp 1) (hp 0)] at e
    refine expS_inj (by rw [map_add (f := _), hs0, c0 _ _ (hp 1) (hp 0), add_zero]) (map_zero _) ?_
    rw [gt_expS_add _ _ hs0 (c0 _ _ (hp 1) (hp 0)), hs, e, expS_zero]
  have anti : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ev ![b, a] s = - ev ![a, b] s := by
    intro n a b ha hb
    have hV := pair_points_zero_constant ha hb
    have e := congrArg (ev ![a, b]) anti0
    rw [gt_ev_add _ hV, gt_ev_zero _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 0)), eval_pair_points,
      evP_pt _ hV, evP_pt _ hV] at e
    exact eq_neg_of_add_eq_zero_right e

  have add0 : ev (n := 3) ![pt k d 0, pt k d 1] s + ev (n := 3) ![pt k d 0, pt k d 2] s =
      ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] s := by
    have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    have e := B.sy_law
    rw [h1, h2, ev_one, one_mul, mul_one, E _ _ (hp 0) (hp 1), E _ _ (hp 0) (hp 2), E _ _ (hp 0) hA] at e
    refine expS_inj (by rw [map_add (f := _), c0 _ _ (hp 0) (hp 1), c0 _ _ (hp 0) (hp 2), add_zero])
      (c0 _ _ (hp 0) hA) ?_
    rw [gt_expS_add _ _ (c0 _ _ (hp 0) (hp 1)) (c0 _ _ (hp 0) (hp 2)), e]
  have add2 : ∀ {n : ℕ} (x y z : Pt k n d), GP x → GP y → GP z →
      ev ![x, y] s + ev ![x, z] s = ev ![x, addOf B.G.F y z] s := by
    intro n x y z hx hy hz'
    have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    have hV := triple_points_zero_constant hx hy hz'
    have e := congrArg (ev ![x, y, z]) add0
    rw [gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 1)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) hA), eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 1) (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at e
    exact e
  obtain ⟨c, hc⟩ : ∃ c : k, (C c : PS k 2 d) * 2 = -1 := by
    refine ⟨algebraMap ℚ k (-1 / 2), ?_⟩
    have e : algebraMap ℚ k (-1 / 2) * 2 = -1 := by
      rw [← map_ofNat (algebraMap ℚ k) 2, ← map_mul]
      norm_num
    have := congrArg (C (σ := Fin 2 × Fin d) (R := k)) e
    rwa [map_mul, map_neg, map_one, map_ofNat] at this
  refine ⟨C c * s, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e := B.symmetry_zero_fst
    rw [E _ _ hz (hp 0), ← expS_zero] at e
    rw [ev_C_mul _ (pair_points_zero_constant hz (hp 0)), expS_inj (c0 _ _ hz (hp 0)) (map_zero _) e, mul_zero]
  · have e := B.symmetry_zero_snd
    rw [E _ _ (hp 0) hz, ← expS_zero] at e
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) hz), expS_inj (c0 _ _ (hp 0) hz) (map_zero _) e, mul_zero]
  · have hA := gp_addOf _ hF _ _ (hp (n := 3) 0) (hp (n := 3) 1)
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 2)), ev_C_mul _ (pair_points_zero_constant (hp 1) (hp 2)), ev_C_mul _ (pair_points_zero_constant hA (hp 2)),
      anti _ _ (hp 2) (hp 0), anti _ _ (hp 2) (hp 1), anti _ _ (hp 2) hA,
      ← add2 _ _ _ (hp 2) (hp 0) (hp 1)]
    ring
  · have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 1)), ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 2)), ev_C_mul _ (pair_points_zero_constant (hp 0) hA),
      ← add0]
    ring
  · intro a
    have hx := gp_comp1 _ _ (B.A.const a) (hp (n := 2) 0)
    have hy := gp_comp1 _ _ (B.A.const (star a)) (hp (n := 2) 1)
    have e := B.ad_sy a
    rw [had, had, ev_one, one_mul, one_mul, E _ _ hx (hp 1), E _ _ (hp 0) hy] at e
    rw [ev_C_mul _ (pair_points_zero_constant hx (hp 1)), ev_C_mul _ (pair_points_zero_constant (hp 0) hy),
      expS_inj (c0 _ _ hx (hp 1)) (c0 _ _ (hp 0) hy) e, sub_self]
  · rw [ev_C_mul _ (pair_points_zero_constant (hp 1) (hp 0)), ← hs]
    congr 1
    linear_combination (-C c) * anti0 + s * hc

end GlobalTheory.SymGauge
end
end
