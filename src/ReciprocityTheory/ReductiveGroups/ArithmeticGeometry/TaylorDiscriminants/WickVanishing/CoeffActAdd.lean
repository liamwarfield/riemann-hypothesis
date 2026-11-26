module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.IntegralFamilyFirstZeroSecond

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FirstDerivativeShiftIntegral
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem const_actK' (B : FB R d O) (a : O) (l : Fin d) : constantCoeff (B.actK k a l) = 0 := by
  show constantCoeff (MvPowerSeries.map (algebraMap R k) (B.A.act a l)) = 0
  rw [MvPowerSeries.constantCoeff_map, B.A.const a l, map_zero]

theorem eval_first_axis_of_identity (g : PS k 2 d) (c : Fin d) (hg : ev (n := 1) ![pt k d 0, 0] g = X ((0 : Fin 1), c)) :
    ev (n := 2) ![pt k d 0, 0] g = X ((0 : Fin 2), c) := by
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (X ((0 : Fin 2), q.2) : PS k 2 d)) :=
    by
      first
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by simp)
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun q => by simp)
  have h1 : MvPowerSeries.HasSubst
      (fun p : Fin 2 × Fin d => (![pt k d 0, 0] : Fin 2 → Pt k 1 d) p.1 p.2) :=
    by
      first
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by rcases p with ⟨i, j⟩; fin_cases i <;> simp [pt])
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => by rcases p with ⟨i, j⟩; fin_cases i <;> simp [pt])
  have key : (fun p : Fin 2 × Fin d => (![pt k d 0, 0] : Fin 2 → Pt k 2 d) p.1 p.2) =
      fun p => MvPowerSeries.subst (fun q : Fin 1 × Fin d => (X ((0 : Fin 2), q.2) : PS k 2 d))
        ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) p.1 p.2) := by
    funext ⟨i, j⟩
    fin_cases i
    · show (X ((0 : Fin 2), j) : PS k 2 d) = MvPowerSeries.subst _ (X ((0 : Fin 1), j) : PS k 1 d)
      rw [MvPowerSeries.subst_X hb]
    · show (0 : PS k 2 d) = MvPowerSeries.subst _ (0 : PS k 1 d)
      rw [← MvPowerSeries.coe_substAlgHom hb, map_zero]
  unfold ev at hg ⊢
  rw [key, ← MvPowerSeries.subst_comp_subst_apply h1 hb, hg, MvPowerSeries.subst_X hb]

theorem first_derivative_shift_integral {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (b : Fin d) :
    ∑ c, pderiv (R := k) ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b) -
      ev (n := 2) ![0, pt k d 1] (pderiv (R := k) ((0 : Fin 2), b) h) ∈ Ig R k (Fin 2 × Fin d) := by
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (LogPf.cc_pt 0) (CZ.cons (LogPf.cc_pt 2) CZ.nil)
  have cA : CZ (![addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1), pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (constantCoeff_add_first_second B) (CZ.cons (LogPf.cc_pt 2) CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) = 0 := by
    rw [map_sub, map_add (f := _), cc_ev' c02, cc_ev' cz12, cc_ev' cA, cc_h hc]
    simp
  have hH := ig_dlog B.ph1 (constantCoeff_first_factor B) _ hH0 hc.ph1 ((1 : Fin 3), b)
  have h2 := ig_ev cz0z integral_family_first_zero_second hH
  have t1 : pderiv (R := k) ((1 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 2] h) = 0 :=
    pderiv_ev_zero c02 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  have dd : pderiv (R := k) ((1 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] h) =
      ev (n := 3) ![pt k d 1, pt k d 2] (pderiv (R := k) ((0 : Fin 2), b) h) := by
    rw [d2 cz12]; simp [pderiv_pt]
  have t2 : ev (n := 2) ![pt k d 0, 0, pt k d 1] (pderiv (R := k) ((1 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] h)) =
      ev (n := 2) ![0, pt k d 1] (pderiv (R := k) ((0 : Fin 2), b) h) := by
    rw [dd, LogPf.ev_ev cz0z cz12]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, LogPf.ev_X cz0z]
  have z2 : ∀ c, pderiv (R := k) ((1 : Fin 3), b) (pt k (n := 3) d 2 c) = 0 := fun c => by simp [pderiv_pt]
  have dA : ∀ c, pderiv (R := k) ((1 : Fin 3), b) (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) c) =
      ev (n := 3) ![pt k d 0, pt k d 1] (pderiv (R := k) ((1 : Fin 2), b) (B.FK k c)) := by
    intro c
    show pderiv (R := k) ((1 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k c)) = _
    rw [d2 cz01]
    simp [pderiv_pt]
  have eB : ∀ g : PS k 2 d, ev (n := 2) ![pt k d 0, 0, pt k d 1] (ev (n := 3) ![pt k d 0, pt k d 1] g) =
      ev (n := 2) ![pt k d 0, 0] g := by
    intro g
    rw [LogPf.ev_ev cz0z cz01]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, LogPf.ev_X cz0z]
  have eA : ∀ g : PS k 2 d, ev (n := 2) ![pt k d 0, 0, pt k d 1]
      (ev (n := 3) ![addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1), pt k d 2] g) = g := by
    intro g
    rw [LogPf.ev_ev cz0z cA]
    conv_rhs => rw [← LogPf.ev_pt g]
    congr 1
    funext j c
    fin_cases j
    · show ev (n := 2) ![pt k d 0, 0, pt k d 1] (ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k c)) = X ((0 : Fin 2), c)
      rw [eB]
      refine eval_first_axis_of_identity _ c ?_
      have := formalGroupLaw_ev_x_zero (lawK k B) c
      rwa [lawK_F] at this
    · simp [pt_apply, LogPf.ev_X cz0z]
  have t3 : ev (n := 2) ![pt k d 0, 0, pt k d 1] (pderiv (R := k) ((1 : Fin 3), b)
      (ev (n := 3) ![addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1), pt k d 2] h)) =
      ∑ c, pderiv (R := k) ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b) := by
    rw [d2 cA]
    simp only [z2, mul_zero, Finset.sum_const_zero, add_zero, dA]
    rw [ev_sum cz0z]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ev_mul cz0z, eA, eB, ← eval_first_axis_restrict]
    rfl
  rw [map_sub, map_add (f := _), ev_sub cz0z, ev_add cz0z, t1, ev_zero' cz0z, t2, t3] at h2
  have e : ∑ c, pderiv (R := k) ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b) -
      ev (n := 2) ![0, pt k d 1] (pderiv (R := k) ((0 : Fin 2), b) h) =
      -(0 + ev (n := 2) ![0, pt k d 1] (pderiv (R := k) ((0 : Fin 2), b) h) -
        ∑ c, pderiv (R := k) ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b)) := by ring
  rw [e]
  exact neg_mem h2

theorem rel_sy {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (b : Fin d) :
    ev (n := 2) ![pt k d 1] (sgOf k h b) + ev (n := 2) ![0, pt k d 1] (pderiv (R := k) ((0 : Fin 2), b) h) ∈
      Ig R k (Fin 2 × Fin d) := by
  have czSw : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) := CZ.cons (LogPf.cc_pt 1) (CZ.cons (LogPf.cc_pt 0) CZ.nil)
  have hH0 : constantCoeff (ev (n := 2) ![pt k d 1, pt k d 0] h - h) = 0 := by
    rw [map_sub, cc_ev' czSw, sub_self]
  have hH := ig_dlog B.sy (cc_sy B) _ hH0 hc.sy ((0 : Fin 2), b)
  have h2 := ig_ev zero_constant_zero_second ig_fam_0z hH
  have dd : pderiv (R := k) ((0 : Fin 2), b) (ev (n := 2) ![pt k d 1, pt k d 0] h) =
      ev (n := 2) ![pt k d 1, pt k d 0] (pderiv (R := k) ((1 : Fin 2), b) h) := by
    rw [d2 czSw]; simp [pderiv_pt]
  have es2 : ∀ g : PS k 2 d, ev (n := 2) ![0, pt k d 1] (ev (n := 2) ![pt k d 1, pt k d 0] g) =
      ev (n := 2) ![pt k d 1, 0] g := by
    intro g
    rw [LogPf.ev_ev zero_constant_zero_second czSw]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, LogPf.ev_X zero_constant_zero_second]
  rw [map_sub, ev_sub zero_constant_zero_second, dd, es2, ← formal_ev_second_point_of_x_zero] at h2
  have e : ev (n := 2) ![pt k d 1] (sgOf k h b) =
      -ev (n := 2) ![pt k d 1] (ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((1 : Fin 2), b) h)) := by
    rw [← ev_neg czY]; rfl
  rw [e]
  have := neg_mem h2
  convert this using 1
  ring

theorem rel_ad {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (a : O) (b : Fin d) :
    ∑ c, sgOf k h c * C (dAct k B (star a) c b) - ev (n := 1) ![B.actK k a] (sgOf k h b) ∈
      Ig R k (Fin 1 × Fin d) := by
  have cA0 : CZ (![comp1 (B.actK k a) (pt k (n := 2) d 0), pt k d 1] : Fin 2 → Pt k 2 d) :=
    CZ.cons (fun l => constantCoeff_ev zero_constant_first_point (const_actK' B a l)) (CZ.cons (LogPf.cc_pt 1) CZ.nil)
  have cA1 : CZ (![pt k (n := 2) d 0, comp1 (B.actK k (star a)) (pt k (n := 2) d 1)] : Fin 2 → Pt k 2 d) :=
    CZ.cons (LogPf.cc_pt 0) (CZ.cons (fun l => constantCoeff_ev czY (const_actK' B (star a) l)) CZ.nil)
  have cAk : CZ (![B.actK k a] : Fin 1 → Pt k 1 d) := CZ.cons (const_actK' B a) CZ.nil
  have hH0 : constantCoeff (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := by
    rw [map_sub, cc_ev' cA0, cc_ev' cA1, sub_self]
  have hH := ig_dlog (B.ad a) (cc_ad B a) _ hH0 (hc.ad a) ((1 : Fin 2), b)
  have h2 := ig_ev cz1 integral_family_point_zero hH
  have z0 : ∀ c, pderiv (R := k) ((1 : Fin 2), b) (comp1 (B.actK k a) (pt k (n := 2) d 0) c) = 0 := fun c =>
    pderiv_ev_zero zero_constant_first_point _ _ (fun j l => by fin_cases j; simp [pderiv_pt])
  have d1 : pderiv (R := k) ((1 : Fin 2), b) (ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), pt k d 1] h) =
      ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), pt k d 1] (pderiv (R := k) ((1 : Fin 2), b) h) := by
    rw [d2 cA0]; simp [z0, pderiv_pt]
  have e1 : ∀ g : PS k 2 d, ev (n := 1) ![pt k d 0, 0]
      (ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), pt k d 1] g) = ev (n := 1) ![B.actK k a, 0] g := by
    intro g
    rw [LogPf.ev_ev cz1 cA0]
    congr 1
    funext j c
    fin_cases j
    · show ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 0] (B.actK k a c)) = B.actK k a c
      rw [LogPf.ev_ev cz1 zero_constant_first_point]
      have : (fun j c => ev (n := 1) ![pt k d 0, 0] ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j c)) =
          (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) := by
        funext j c; fin_cases j; simp [pt_apply, LogPf.ev_X cz1]
      rw [this, gt_ev_pt_self]
    · simp [pt_apply, LogPf.ev_X cz1]
  have e2 : ∀ g : PS k 2 d, ev (n := 1) ![B.actK k a] (ev (n := 1) ![pt k d 0, 0] g) =
      ev (n := 1) ![B.actK k a, 0] g := by
    intro g
    rw [LogPf.ev_ev cAk cz1]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, LogPf.ev_X cAk, ev_zero' cAk]
  have z1 : ∀ c, pderiv (R := k) ((1 : Fin 2), b) (pt k (n := 2) d 0 c) = 0 := fun c => by simp [pderiv_pt]
  have zA : ∀ c, pderiv (R := k) ((1 : Fin 2), b) (comp1 (B.actK k (star a)) (pt k (n := 2) d 1) c) =
      ev (n := 2) ![pt k d 1] (pderiv (R := k) ((0 : Fin 1), b) (B.actK k (star a) c)) := fun c => d_y _ b
  have e3 : ∀ g : PS k 2 d, ev (n := 1) ![pt k d 0, 0]
      (ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k (n := 2) d 1)] g) = ev (n := 1) ![pt k d 0, 0] g := by
    intro g
    rw [LogPf.ev_ev cz1 cA1]
    congr 1
    funext j c
    fin_cases j
    · simp [pt_apply, LogPf.ev_X cz1]
    · show ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (B.actK k (star a) c)) = 0
      rw [ez_y, const_actK', map_zero]
  have e4 : ∀ c, ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (pderiv (R := k) ((0 : Fin 1), b)
      (B.actK k (star a) c))) = C (dAct k B (star a) c b) := fun c => by
    rw [ez_y, cc_pderiv']; rfl
  rw [map_sub, ev_sub cz1, d1, e1, d2 cA1] at h2
  simp only [z1, mul_zero, Finset.sum_const_zero, zero_add, zA, ev_sum cz1, ev_mul cz1, e3, e4] at h2
  have e5 : ev (n := 1) ![B.actK k a] (sgOf k h b) = -ev (n := 1) ![B.actK k a, 0] (pderiv (R := k) ((1 : Fin 2), b) h) := by
    rw [← e2, ← ev_neg cAk]; rfl
  rw [e5]
  simp only [sgOf]
  convert h2 using 1
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

theorem coeff_single_zero_F_eq_ite {K : Type} [CommRing K] {d : ℕ} (G : FGLaw K d) (c i : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1) (G.F c) = if c = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), i) 1)) (formalGroupLaw_ev_x_zero G c)
  rw [coeff_ev_zero_right, Finsupp.embDomain_single] at h
  rw [show (eXv d) ((0 : Fin 1), i) = ((0 : Fin 2), i) from rfl] at h
  rw [h, coeff_X]
  by_cases hci : c = i
  · subst hci; simp
  · rw [if_neg, if_neg hci]
    intro he
    exact hci (congrArg Prod.snd (Finsupp.single_left_injective one_ne_zero he)).symm

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem coeff_act_add (B : FB R d O) (a b : O) (i j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act (a + b) i) =
      coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act a i) + coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act b i) := by
  rw [B.A.add_act a b]
  show coeff _ (ev (n := 1) ![B.A.act a, B.A.act b] (B.G.F i)) = _
  have hab : CZ (![B.A.act a, B.A.act b] : Fin 2 → Pt R 1 d) := CZ.cons (B.A.const a) (CZ.cons (B.A.const b) CZ.nil)
  rw [← cc_pderiv', ← cc_pderiv' (B.A.act a i), ← cc_pderiv' (B.A.act b i), d2 hab]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, cc_ev' hab, cc_pderiv', coeff_single_zero_F_eq_ite, coeff_F_y, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem dAct_sum (B : FB R d O) (w0 : O) (hw : w0 + star w0 = 1) (i j : Fin d) :
    dAct k B w0 i j + dAct k B (star w0) i j = if i = j then 1 else 0 := by
  simp only [dAct, FB.actK, MvPowerSeries.coeff_map]
  rw [← map_add (f := _), ← coeff_act_add, hw, B.A.one_act]
  simp only [pt, MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · have h' : Finsupp.single ((0 : Fin 1), j) 1 ≠ Finsupp.single ((0 : Fin 1), i) 1 := by
      intro e
      rw [Finsupp.single_left_inj one_ne_zero] at e
      exact h (Prod.mk.inj e).2.symm
    simp [h, h']

theorem homK (B : FB R d O) (a : O) (c : Fin d) :
    ev (n := 2) ![(lawK k B).F] (B.actK k a c) =
      ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] (B.FK k c) := by
  have h := congrArg (fun P : Pt R 2 d => MvPowerSeries.map (algebraMap R k) (P c)) (B.A.hom a)
  simp only [comp1, FGLaw.add, addOf] at h
  have c01 : CZ (![pt R (n := 2) d 0, pt R d 1] : Fin 2 → Pt R 2 d) := CZ.cons (LogPf.cc_pt 0) (CZ.cons (LogPf.cc_pt 1) CZ.nil)
  have cL : CZ (![addOf B.G.F (pt R (n := 2) d 0) (pt R d 1)] : Fin 1 → Pt R 2 d) :=
    CZ.cons (fun i => constantCoeff_ev c01 (B.G.const i)) CZ.nil
  have cR : CZ (![comp1 (B.A.act a) (pt R (n := 2) d 0), comp1 (B.A.act a) (pt R (n := 2) d 1)] : Fin 2 → Pt R 2 d) :=
    CZ.cons (fun i => constantCoeff_ev zero_constant_first_point (B.A.const a i)) (CZ.cons (fun i => constantCoeff_ev czY (B.A.const a i)) CZ.nil)
  rw [map_ev _ cL, map_ev _ cR] at h
  have m1 : ∀ i, MvPowerSeries.map (algebraMap R k) (addOf B.G.F (pt R (n := 2) d 0) (pt R d 1) i) = B.FK k i := by
    intro i
    show MvPowerSeries.map (algebraMap R k) (ev (n := 2) ![pt R d 0, pt R d 1] (B.G.F i)) = _
    rw [map_ev _ c01]
    have : (fun j c => MvPowerSeries.map (algebraMap R k) ((![pt R (n := 2) d 0, pt R d 1] : Fin 2 → Pt R 2 d) j c)) =
        fun j => pt k (n := 2) d j := by
      funext j c; fin_cases j <;> simp [pt_apply]
    rw [this, LogPf.ev_pt]
    rfl
  have m2 : ∀ (l : Fin 2) (i : Fin d), MvPowerSeries.map (algebraMap R k) (comp1 (B.A.act a) (pt R (n := 2) d l) i) =
      comp1 (B.actK k a) (pt k (n := 2) d l) i := by
    intro l i
    show MvPowerSeries.map (algebraMap R k) (ev (n := 2) ![pt R d l] (B.A.act a i)) = ev (n := 2) ![pt k d l] (B.actK k a i)
    rw [map_ev _ (CZ.cons (LogPf.cc_pt l) CZ.nil)]
    congr 1
    funext j c; fin_cases j; simp [pt_apply]
  have fL : (fun j i => MvPowerSeries.map (algebraMap R k)
      ((![addOf B.G.F (pt R (n := 2) d 0) (pt R d 1)] : Fin 1 → Pt R 2 d) j i)) = ![(lawK k B).F] := by
    funext j i; fin_cases j; exact m1 i
  have fR : (fun j i => MvPowerSeries.map (algebraMap R k)
      ((![comp1 (B.A.act a) (pt R (n := 2) d 0), comp1 (B.A.act a) (pt R (n := 2) d 1)] : Fin 2 → Pt R 2 d) j i)) =
      ![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] := by
    funext j i; fin_cases j
    · exact m2 0 i
    · exact m2 1 i
  rw [fL, fR] at h
  exact h

theorem hom_rel (B : FB R d O) (a : O) (c b : Fin d) :
    ∑ j, pderiv (R := k) ((0 : Fin 1), j) (B.actK k a c) * Jac (lawK k B) j b =
      ∑ j, ev (n := 1) ![B.actK k a] (Jac (lawK k B) c j) * C (dAct k B a j b) := by
  have cP : CZ (![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] : Fin 2 → Pt k 2 d) :=
    CZ.cons (fun l => constantCoeff_ev zero_constant_first_point (const_actK' B a l)) (CZ.cons (fun l => constantCoeff_ev czY (const_actK' B a l)) CZ.nil)
  have cAk : CZ (![B.actK k a] : Fin 1 → Pt k 1 d) := CZ.cons (const_actK' B a) CZ.nil
  have h := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((1 : Fin 2), b) g)) (homK B a c)
  beta_reduce at h
  have z0 : ∀ j, pderiv (R := k) ((1 : Fin 2), b) (comp1 (B.actK k a) (pt k (n := 2) d 0) j) = 0 := fun j =>
    pderiv_ev_zero zero_constant_first_point _ _ (fun j l => by fin_cases j; simp [pderiv_pt])
  have zA : ∀ j, pderiv (R := k) ((1 : Fin 2), b) (comp1 (B.actK k a) (pt k (n := 2) d 1) j) =
      ev (n := 2) ![pt k d 1] (pderiv (R := k) ((0 : Fin 1), b) (B.actK k a j)) := fun j => d_y _ b
  have e1 : ∀ g : PS k 2 d, ev (n := 1) ![pt k d 0, 0]
      (ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] g) =
      ev (n := 1) ![B.actK k a] (ev (n := 1) ![pt k d 0, 0] g) := by
    intro g
    rw [LogPf.ev_ev cz1 cP, LogPf.ev_ev cAk cz1]
    congr 1
    funext j c
    fin_cases j
    · show ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 0] (B.actK k a c)) = _
      rw [LogPf.ev_ev cz1 zero_constant_first_point]
      have : (fun j c => ev (n := 1) ![pt k d 0, 0] ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j c)) =
          (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) := by
        funext j c; fin_cases j; simp [pt_apply, LogPf.ev_X cz1]
      rw [this, gt_ev_pt_self]
      simp [pt_apply, LogPf.ev_X cAk]
    · show ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (B.actK k a c)) = _
      rw [ez_y, const_actK', map_zero]
      simp [ev_zero' cAk]
  rw [d_F, d2 cP] at h
  simp only [z0, mul_zero, Finset.sum_const_zero, zero_add, zA, ev_sum cz1, ev_mul cz1, ezF, ez_dF, e1, ez_y,
    cc_pderiv'] at h
  rw [h]
  rfl

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
