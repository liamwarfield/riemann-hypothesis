module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeNabValBaseChange
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvGermEvThreePoints
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvRegaugedSecondLawFamily
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeOfLog
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsActionGauge
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ActionGauge

section Basic

variable {k : Type} [CommRing k] {d : ℕ}

def evAdd {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) : PS k m d →+ PS k n d :=
  AddMonoidHom.mk' (ev a) (gt_ev_add a ha)

theorem ev_ratSmul [Algebra ℚ k] {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (q : ℚ)
    (f : PS k m d) : ev a (q • f) = q • ev a f :=
  map_rat_smul (evAdd a ha) q f

theorem ev_pt_two (f : PS k 2 d) : ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] f = f := by
  change MvPowerSeries.subst
    (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k (n := 2) d 1] p.1) p.2) f = f
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k (n := 2) d 1] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl

theorem ev_ev_two {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a b : Pt k m d)
    (ha : GP a) (hb : GP b) (f : PS k 2 d) :
    ev V (ev ![a, b] f) = ev ![evP V a, evP V b] f := by
  rw [gt_ev_ev' V _ hV (pair_points_zero_constant ha hb), eval_pair_points]

theorem ev_left {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (a b : Pt k n d) (ha : GP a) (hb : GP b)
    (g : PS k 2 d) :
    ev ![a, b] (ev ![comp1 φ (pt k (n := 2) d 0), pt k (n := 2) d 1] g) = ev ![comp1 φ a, b] g := by
  have hV := pair_points_zero_constant ha hb
  rw [ev_ev_two _ hV _ _ (gp_comp1 _ _ hφ (gp_pt 0)) (gp_pt 1),
    evP_comp1 _ hV _ _ (gp_pt 0), evP_pt _ hV, evP_pt _ hV]
  rfl

theorem ev_right {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (a b : Pt k n d) (ha : GP a) (hb : GP b)
    (g : PS k 2 d) :
    ev ![a, b] (ev ![pt k (n := 2) d 0, comp1 φ (pt k (n := 2) d 1)] g) = ev ![a, comp1 φ b] g := by
  have hV := pair_points_zero_constant ha hb
  rw [ev_ev_two _ hV _ _ (gp_pt 0) (gp_comp1 _ _ hφ (gp_pt 1)),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV]
  rfl

end Basic

section Act

variable {k : Type} [CommRing k] {d : ℕ} {O : Type} [CommRing O] {G : FGLaw k d} (A : OAct O G)

theorem act_addOf (c : O) {n : ℕ} (x y : Pt k n d) (hx : GP x) (hy : GP y) :
    comp1 (A.act c) (addOf G.F x y) = addOf G.F (comp1 (A.act c) x) (comp1 (A.act c) y) := by
  have hV := pair_points_zero_constant hx hy
  have hc : GP (A.act c) := A.const c
  have h := congrArg (evP ![x, y]) (A.hom c)
  rw [evP_comp1 _ hV _ _ (gp_addOf _ G.const _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1),
    evP_addOf _ hV _ _ _ (gp_comp1 _ _ hc (gp_pt 0)) (gp_comp1 _ _ hc (gp_pt 1)),
    evP_comp1 _ hV _ _ (gp_pt 0), evP_comp1 _ hV _ _ (gp_pt 1),
    evP_pt _ hV, evP_pt _ hV] at h
  exact h

theorem add_act_apply (a b : O) {n : ℕ} (x : Pt k n d) (hx : GP x) :
    comp1 (A.act (a + b)) x = addOf G.F (comp1 (A.act a) x) (comp1 (A.act b) x) := by
  rw [A.add_act]
  exact evP_addOf ![x] (single_point_zero_constant hx) G.F _ _ (A.const a) (A.const b)

theorem mul_act_apply (a b : O) {n : ℕ} (x : Pt k n d) (hx : GP x) :
    comp1 (A.act (a * b)) x = comp1 (A.act a) (comp1 (A.act b) x) := by
  rw [A.mul_act]
  exact gt_comp1_comp1 _ _ (A.const b) x hx

theorem one_act_apply {n : ℕ} (x : Pt k n d) (hx : GP x) : comp1 (A.act 1) x = x := by
  rw [A.one_act]
  exact gt_comp1_pt x hx

end Act

section Biadd

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

def biadd (G : FGLaw k d) : Submodule ℚ (PS k 2 d) where
  carrier := {g | (∀ (n : ℕ) (b : Pt k n d), GP b → ev ![0, b] g = 0) ∧
    (∀ (n : ℕ) (a : Pt k n d), GP a → ev ![a, 0] g = 0) ∧
    (∀ (n : ℕ) (a a' b : Pt k n d), GP a → GP a' → GP b →
      ev ![addOf G.F a a', b] g = ev ![a, b] g + ev ![a', b] g) ∧
    (∀ (n : ℕ) (a b b' : Pt k n d), GP a → GP b → GP b' →
      ev ![a, addOf G.F b b'] g = ev ![a, b] g + ev ![a, b'] g)}
  zero_mem' := by
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · exact gt_ev_zero _ (pair_points_zero_constant gp_zero₂ hb)
    · exact gt_ev_zero _ (pair_points_zero_constant ha gp_zero₂)
    · rw [gt_ev_zero _ (pair_points_zero_constant (gp_addOf _ G.const _ _ ha ha') hb), gt_ev_zero _ (pair_points_zero_constant ha hb),
        gt_ev_zero _ (pair_points_zero_constant ha' hb), add_zero]
    · rw [gt_ev_zero _ (pair_points_zero_constant ha (gp_addOf _ G.const _ _ hb hb')), gt_ev_zero _ (pair_points_zero_constant ha hb),
        gt_ev_zero _ (pair_points_zero_constant ha hb'), add_zero]
  add_mem' := by
    rintro f g ⟨f1, f2, f3, f4⟩ ⟨g1, g2, g3, g4⟩
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [gt_ev_add _ (pair_points_zero_constant gp_zero₂ hb), f1 n b hb, g1 n b hb, add_zero]
    · rw [gt_ev_add _ (pair_points_zero_constant ha gp_zero₂), f2 n a ha, g2 n a ha, add_zero]
    · rw [gt_ev_add _ (pair_points_zero_constant (gp_addOf _ G.const _ _ ha ha') hb), gt_ev_add _ (pair_points_zero_constant ha hb),
        gt_ev_add _ (pair_points_zero_constant ha' hb), f3 n a a' b ha ha' hb, g3 n a a' b ha ha' hb]
      ring
    · rw [gt_ev_add _ (pair_points_zero_constant ha (gp_addOf _ G.const _ _ hb hb')), gt_ev_add _ (pair_points_zero_constant ha hb),
        gt_ev_add _ (pair_points_zero_constant ha hb'), f4 n a b b' ha hb hb', g4 n a b b' ha hb hb']
      ring
  smul_mem' := by
    rintro q f ⟨f1, f2, f3, f4⟩
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [ev_ratSmul _ (pair_points_zero_constant gp_zero₂ hb), f1 n b hb, smul_zero]
    · rw [ev_ratSmul _ (pair_points_zero_constant ha gp_zero₂), f2 n a ha, smul_zero]
    · rw [ev_ratSmul _ (pair_points_zero_constant (gp_addOf _ G.const _ _ ha ha') hb), ev_ratSmul _ (pair_points_zero_constant ha hb),
        ev_ratSmul _ (pair_points_zero_constant ha' hb), f3 n a a' b ha ha' hb, smul_add]
    · rw [ev_ratSmul _ (pair_points_zero_constant ha (gp_addOf _ G.const _ _ hb hb')), ev_ratSmul _ (pair_points_zero_constant ha hb),
        ev_ratSmul _ (pair_points_zero_constant ha hb'), f4 n a b b' ha hb hb', smul_add]

variable {O : Type} [CommRing O] {G : FGLaw k d} (A : OAct O G)

def leftMap (c : O) : Module.End ℚ (biadd G) where
  toFun g := ⟨ev ![comp1 (A.act c) (pt k (n := 2) d 0), pt k (n := 2) d 1] (g : PS k 2 d), by
    have hc : GP (A.act c) := A.const c
    obtain ⟨g, g1, g2, g3, g4⟩ := g
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [ev_left _ hc _ _ gp_zero₂ hb, gt_comp1_zero _ hc, g1 n b hb]
    · rw [ev_left _ hc _ _ ha gp_zero₂, g2 n _ (gp_comp1 _ _ hc ha)]
    · rw [ev_left _ hc _ _ (gp_addOf _ G.const _ _ ha ha') hb, ev_left _ hc _ _ ha hb,
        ev_left _ hc _ _ ha' hb, act_addOf A c _ _ ha ha',
        g3 n _ _ _ (gp_comp1 _ _ hc ha) (gp_comp1 _ _ hc ha') hb]
    · rw [ev_left _ hc _ _ ha (gp_addOf _ G.const _ _ hb hb'), ev_left _ hc _ _ ha hb,
        ev_left _ hc _ _ ha hb', g4 n _ _ _ (gp_comp1 _ _ hc ha) hb hb']⟩
  map_add' f g := Subtype.ext
    (gt_ev_add _ (pair_points_zero_constant (gp_comp1 _ _ (A.const c) (gp_pt 0)) (gp_pt 1)) _ _)
  map_smul' q f := Subtype.ext
    (ev_ratSmul _ (pair_points_zero_constant (gp_comp1 _ _ (A.const c) (gp_pt 0)) (gp_pt 1)) _ _)

def rightMap (c : O) : Module.End ℚ (biadd G) where
  toFun g := ⟨ev ![pt k (n := 2) d 0, comp1 (A.act c) (pt k (n := 2) d 1)] (g : PS k 2 d), by
    have hc : GP (A.act c) := A.const c
    obtain ⟨g, g1, g2, g3, g4⟩ := g
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [ev_right _ hc _ _ gp_zero₂ hb, g1 n _ (gp_comp1 _ _ hc hb)]
    · rw [ev_right _ hc _ _ ha gp_zero₂, gt_comp1_zero _ hc, g2 n a ha]
    · rw [ev_right _ hc _ _ (gp_addOf _ G.const _ _ ha ha') hb, ev_right _ hc _ _ ha hb,
        ev_right _ hc _ _ ha' hb, g3 n _ _ _ ha ha' (gp_comp1 _ _ hc hb)]
    · rw [ev_right _ hc _ _ ha (gp_addOf _ G.const _ _ hb hb'), ev_right _ hc _ _ ha hb,
        ev_right _ hc _ _ ha hb', act_addOf A c _ _ hb hb',
        g4 n _ _ _ ha (gp_comp1 _ _ hc hb) (gp_comp1 _ _ hc hb')]⟩
  map_add' f g := Subtype.ext
    (gt_ev_add _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (A.const c) (gp_pt 1))) _ _)
  map_smul' q f := Subtype.ext
    (ev_ratSmul _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (A.const c) (gp_pt 1))) _ _)

theorem leftMap_val (c : O) (g : biadd G) : (leftMap A c g : PS k 2 d) =
    ev ![comp1 (A.act c) (pt k (n := 2) d 0), pt k (n := 2) d 1] (g : PS k 2 d) := rfl

theorem rightMap_val (c : O) (g : biadd G) : (rightMap A c g : PS k 2 d) =
    ev ![pt k (n := 2) d 0, comp1 (A.act c) (pt k (n := 2) d 1)] (g : PS k 2 d) := rfl

def leftHom : O →+* Module.End ℚ (biadd G) :=
  RingHom.mk'
    { toFun := leftMap A
      map_one' := by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [leftMap_val, one_act_apply A _ (gp_pt 0), ev_pt_two]
        rfl
      map_mul' := fun a b => by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [Module.End.mul_apply, leftMap_val, leftMap_val, leftMap_val,
          ev_left _ (A.const b) _ _ (gp_comp1 _ _ (A.const a) (gp_pt 0)) (gp_pt 1),
          mul_comm a b, mul_act_apply A _ _ _ (gp_pt 0)] }
    (fun a b => by
      refine LinearMap.ext fun g => Subtype.ext ?_
      change (leftMap A (a + b) g : PS k 2 d) = leftMap A a g + leftMap A b g
      rw [leftMap_val, leftMap_val, leftMap_val, add_act_apply A _ _ _ (gp_pt 0)]
      exact g.2.2.2.1 _ _ _ _ (gp_comp1 _ _ (A.const a) (gp_pt 0))
        (gp_comp1 _ _ (A.const b) (gp_pt 0)) (gp_pt 1))

def rightHom : O →+* Module.End ℚ (biadd G) :=
  RingHom.mk'
    { toFun := rightMap A
      map_one' := by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [rightMap_val, one_act_apply A _ (gp_pt 1), ev_pt_two]
        rfl
      map_mul' := fun a b => by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [Module.End.mul_apply, rightMap_val, rightMap_val, rightMap_val,
          ev_right _ (A.const b) _ _ (gp_pt 0) (gp_comp1 _ _ (A.const a) (gp_pt 1)),
          mul_comm a b, mul_act_apply A _ _ _ (gp_pt 1)] }
    (fun a b => by
      refine LinearMap.ext fun g => Subtype.ext ?_
      change (rightMap A (a + b) g : PS k 2 d) = rightMap A a g + rightMap A b g
      rw [rightMap_val, rightMap_val, rightMap_val, add_act_apply A _ _ _ (gp_pt 1)]
      exact g.2.2.2.2 _ _ _ _ (gp_pt 0) (gp_comp1 _ _ (A.const a) (gp_pt 1))
        (gp_comp1 _ _ (A.const b) (gp_pt 1)))

theorem left_right_commute (a b : O) : Commute (leftHom A a) (rightHom A b) := by
  refine LinearMap.ext fun g => Subtype.ext ?_
  change (leftMap A a (rightMap A b g) : PS k 2 d) = rightMap A b (leftMap A a g)
  rw [leftMap_val, rightMap_val, rightMap_val, leftMap_val,
    ev_right _ (A.const b) _ _ (gp_comp1 _ _ (A.const a) (gp_pt 0)) (gp_pt 1),
    ev_left _ (A.const a) _ _ (gp_pt 0) (gp_comp1 _ _ (A.const b) (gp_pt 1))]

end Biadd

section Log

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (B : FB k d O)

theorem expS_inj {n : ℕ} {f g : PS k n d} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : FB.expS k f = FB.expS k g) : f = g := exp_inj hf hg h

omit [Algebra ℚ k] in
theorem ad_const (a : O) : constantCoeff (B.ad a) = 1 := by
  have h := congrArg constantCoeff (B.adjoint_zero_fst a)
  rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_one] at h

def logAd (a : O) : PS k 2 d := PowerSeries.subst (B.ad a - 1) (PowerSeries.log k)

theorem logAd_const (a : O) : constantCoeff (logAd B a) = 0 := constantCoeff_logS (ad_const B a)

theorem expS_logAd (a : O) : FB.expS k (logAd B a) = B.ad a := exp_log (ad_const B a)

theorem expS_ev_logAd (c : O) {n : ℕ} (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    FB.expS k (ev ![a, b] (logAd B c)) = ev ![a, b] (B.ad c) := by
  rw [← gt_ev_expS _ (pair_points_zero_constant ha hb) _ (logAd_const B c), expS_logAd]

theorem ev_logAd_const (c : O) {n : ℕ} (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    constantCoeff (ev ![a, b] (logAd B c)) = 0 :=
  gt_const_ev _ (pair_points_zero_constant ha hb) _ (logAd_const B c)

theorem logAd_mem (h1 : B.ph1 = 1) (h2 : B.ph2 = 1) (c : O) : logAd B c ∈ biadd B.G := by
  refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
    fun n a b b' ha hb hb' => ?_⟩
  · refine eq_zero_of_exp_eq_one (ev_logAd_const B c _ _ gp_zero₂ hb) ?_
    refine (expS_ev_logAd B c _ _ gp_zero₂ hb).trans ?_
    have h := congrArg (ev ![b]) (B.adjoint_zero_fst c)
    rw [ev_ev_two _ (single_point_zero_constant hb) _ _ gp_zero₂ (gp_pt 0), evP_zero _ (single_point_zero_constant hb),
      evP_pt _ (single_point_zero_constant hb), ev_one] at h
    exact h
  · refine eq_zero_of_exp_eq_one (ev_logAd_const B c _ _ ha gp_zero₂) ?_
    refine (expS_ev_logAd B c _ _ ha gp_zero₂).trans ?_
    have h := congrArg (ev ![a]) (B.adjoint_zero_snd c)
    rw [ev_ev_two _ (single_point_zero_constant ha) _ _ (gp_pt 0) gp_zero₂, evP_zero _ (single_point_zero_constant ha),
      evP_pt _ (single_point_zero_constant ha), ev_one] at h
    exact h
  · have hs := gp_addOf _ B.G.const _ _ ha ha'
    have hV := triple_points_zero_constant ha ha' hb
    refine expS_inj (ev_logAd_const B c _ _ hs hb)
      (by rw [map_add (f := _), ev_logAd_const B c _ _ ha hb, ev_logAd_const B c _ _ ha' hb, add_zero]) ?_
    rw [gt_expS_add _ _ (ev_logAd_const B c _ _ ha hb) (ev_logAd_const B c _ _ ha' hb),
      expS_ev_logAd B c _ _ hs hb, expS_ev_logAd B c _ _ ha hb, expS_ev_logAd B c _ _ ha' hb]
    have h := B.adjoint_compat_left c
    rw [h1, ev_one, ev_one, one_mul, mul_one] at h
    have h' := congrArg (ev ![a, a', b]) h
    rw [gt_ev_mul _ hV,
      ev_ev_two _ hV _ _ (gp_addOf _ B.G.const _ _ (gp_pt 0) (gp_pt 1)) (gp_pt 2),
      ev_ev_two _ hV _ _ (gp_pt 0) (gp_pt 2), ev_ev_two _ hV _ _ (gp_pt 1) (gp_pt 2),
      evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_pt _ hV, evP_pt _ hV,
      evP_pt _ hV] at h'
    exact h'
  · have hs := gp_addOf _ B.G.const _ _ hb hb'
    have hV := triple_points_zero_constant ha hb hb'
    refine expS_inj (ev_logAd_const B c _ _ ha hs)
      (by rw [map_add (f := _), ev_logAd_const B c _ _ ha hb, ev_logAd_const B c _ _ ha hb', add_zero]) ?_
    rw [gt_expS_add _ _ (ev_logAd_const B c _ _ ha hb) (ev_logAd_const B c _ _ ha hb'),
      expS_ev_logAd B c _ _ ha hs, expS_ev_logAd B c _ _ ha hb, expS_ev_logAd B c _ _ ha hb']
    have h := B.adjoint_compat_right c
    rw [h2, ev_one, ev_one, one_mul, mul_one] at h
    have h' := congrArg (ev ![a, b, b']) h
    rw [gt_ev_mul _ hV,
      ev_ev_two _ hV _ _ (gp_pt 0) (gp_addOf _ B.G.const _ _ (gp_pt 1) (gp_pt 2)),
      ev_ev_two _ hV _ _ (gp_pt 0) (gp_pt 1), ev_ev_two _ hV _ _ (gp_pt 0) (gp_pt 2),
      evP_addOf _ hV _ _ _ (gp_pt 1) (gp_pt 2), evP_pt _ hV, evP_pt _ hV,
      evP_pt _ hV] at h'
    exact h'

theorem logAd_add (h1 : B.ph1 = 1) (h2 : B.ph2 = 1) (a b : O) :
    logAd B (a + b) = logAd B a + logAd B b := by
  refine expS_inj (logAd_const B _) (by rw [map_add (f := _), logAd_const, logAd_const, add_zero]) ?_
  rw [gt_expS_add _ _ (logAd_const B a) (logAd_const B b), expS_logAd, expS_logAd, expS_logAd]
  have h := B.ad_add a b
  rwa [h1, h2, ev_one, ev_one, one_mul, mul_one] at h

theorem logAd_mul (a b : O) : logAd B (a * b) =
    ev ![comp1 (B.A.act b) (pt k (n := 2) d 0), pt k (n := 2) d 1] (logAd B a) +
      ev ![pt k (n := 2) d 0, comp1 (B.A.act (star a)) (pt k (n := 2) d 1)] (logAd B b) := by
  have hx : GP (comp1 (B.A.act b) (pt k (n := 2) d 0)) :=
    gp_comp1 _ _ (B.A.const b) (gp_pt 0)
  have hz : GP (comp1 (B.A.act (star a)) (pt k (n := 2) d 1)) :=
    gp_comp1 _ _ (B.A.const _) (gp_pt 1)
  have c1 := ev_logAd_const B a _ _ hx (gp_pt 1)
  have c2 := ev_logAd_const B b _ _ (gp_pt 0) hz
  refine expS_inj (logAd_const B _) (by rw [map_add (f := _), c1, c2, add_zero]) ?_
  rw [gt_expS_add _ _ c1 c2, expS_logAd, expS_ev_logAd B a _ _ hx (gp_pt 1),
    expS_ev_logAd B b _ _ (gp_pt 0) hz, B.ad_mul]

end Log

theorem exists_action_gauge :
    (∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V), (∀ a b, Commute (l a) (r b)) → ∀ δ : O →+ V, (∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) → ∃ v : V, ∀ a, δ a = l a v - r a v) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ ∀ a : O, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) := by
  intro H k _ _ d O _ _ _ _ _ B h1 h2
  let δ : O →+ biadd B.G := AddMonoidHom.mk' (fun a => ⟨logAd B a, logAd_mem B h1 h2 a⟩)
    (fun a b => Subtype.ext (logAd_add B h1 h2 a b))
  obtain ⟨v, hv⟩ := H O (biadd B.G) (leftHom B.A) ((rightHom B.A).comp (starRingEnd O))
    (fun a b => left_right_commute B.A a (star b)) δ (fun a b => Subtype.ext (logAd_mul B a b))
  refine ⟨v, ⟨v.2.1 _ _ (gp_pt 0), v.2.2.1 _ _ (gp_pt 0)⟩, ?_, ?_, fun a => ?_⟩
  · rw [v.2.2.2.1 _ _ _ _ (gp_pt 0) (gp_pt 1) (gp_pt 2), sub_self]
  · rw [v.2.2.2.2 _ _ _ _ (gp_pt 0) (gp_pt 1) (gp_pt 2), sub_self]
  · rw [← expS_logAd B a]
    exact congrArg (FB.expS k) (congrArg Subtype.val (hv a))

end GlobalTheory.ActionGauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeOfSteps
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.CanonGaugeAssembly

variable {k : Type} [CommRing k] {d : ℕ}

theorem const_of_ax {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) :
    constantCoeff h = 0 := by
  have := congrArg constantCoeff h0
  rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this

theorem cancel_expS [Algebra ℚ k] {n : ℕ} {p c : PS k n d} (hc : constantCoeff c = 0)
    (e : FB.expS k c = p * FB.expS k c) : p = 1 := by
  have u : FB.expS k c * FB.expS k (-c) = 1 := by
    rw [← gt_expS_add _ _ hc (by rw [map_neg, hc, neg_zero]), add_neg_cancel, nt_expS_zero]
  calc p = p * FB.expS k c * FB.expS k (-c) := by rw [mul_assoc, u, mul_one]
    _ = 1 := by rw [← e, u]

structure Cob {n : ℕ} (c : PS k 2 d → PS k n d) : Prop where
  add : ∀ f g, c (f + g) = c f + c g
  const : ∀ f, constantCoeff f = 0 → constantCoeff (c f) = 0

theorem cob_three {n : ℕ} (U V W : Fin 2 → Pt k n d) (hU : ∀ j, GP (U j)) (hV : ∀ j, GP (V j))
    (hW : ∀ j, GP (W j)) : Cob (fun h : PS k 2 d => ev U h + ev V h - ev W h) := by
  constructor
  · intro f g
    rw [gt_ev_add U hU, gt_ev_add V hV, gt_ev_add W hW]; ring
  · intro f hf
    rw [map_sub, map_add constantCoeff, gt_const_ev U hU f hf, gt_const_ev V hV f hf,
      gt_const_ev W hW f hf]; simp

theorem cob_two {n : ℕ} (U V : Fin 2 → Pt k n d) (hU : ∀ j, GP (U j)) (hV : ∀ j, GP (V j)) :
    Cob (fun h : PS k 2 d => ev U h - ev V h) := by
  constructor
  · intro f g
    rw [gt_ev_add U hU, gt_ev_add V hV]; ring
  · intro f hf
    rw [map_sub, gt_const_ev U hU f hf, gt_const_ev V hV f hf]; simp

theorem cob_swap (U : Fin 2 → Pt k 2 d) (hU : ∀ j, GP (U j)) :
    Cob (fun h : PS k 2 d => ev U h - h) := by
  constructor
  · intro f g
    rw [gt_ev_add U hU]; ring
  · intro f hf
    rw [map_sub, gt_const_ev U hU f hf, hf]; simp

theorem Cob.chain [Algebra ℚ k] {n : ℕ} {c : PS k 2 d → PS k n d} (hc : Cob c)
    {h₁ h₂ h₃ h₄ : PS k 2 d} (c₁ : constantCoeff h₁ = 0) (c₂ : constantCoeff h₂ = 0)
    (c₃ : constantCoeff h₃ = 0) (c₄ : constantCoeff h₄ = 0) {p₀ p₁ p₂ p₃ : PS k n d}
    (e₁ : p₀ = p₁ * FB.expS k (c h₁)) (e₂ : p₁ = p₂ * FB.expS k (c h₂))
    (e₃ : p₂ = p₃ * FB.expS k (c h₃)) (e₄ : p₃ = FB.expS k (c h₄)) :
    p₀ = FB.expS k (c (h₁ + h₂ + h₃ + h₄)) := by
  have k₁ := hc.const _ c₁
  have k₂ := hc.const _ c₂
  have k₃ := hc.const _ c₃
  have k₄ := hc.const _ c₄
  rw [hc.add, hc.add, hc.add, gt_expS_add _ _ (by simp [k₁, k₂, k₃]) k₄,
    gt_expS_add _ _ (by simp [k₁, k₂]) k₃, gt_expS_add _ _ k₁ k₂, e₁, e₂, e₃, e₄]
  ring

end GlobalTheory.CanonGaugeAssembly


open GlobalTheory.CanonGaugeAssembly in
theorem GlobalTheory.canonGauge_of_steps :
    (∀ (R k : Type) [CommRing R] [CommRing k] (f : R →+* k) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ B' : FB k d O, (∀ i, B'.G.F i = MvPowerSeries.map f (B.G.F i)) ∧ (∀ a i, B'.A.act a i = MvPowerSeries.map f (B.A.act a i)) ∧ B'.ph1 = MvPowerSeries.map f B.ph1 ∧ B'.ph2 = MvPowerSeries.map f B.ph2 ∧ B'.sy = MvPowerSeries.map f B.sy ∧ ∀ a, B'.ad a = MvPowerSeries.map f (B.ad a)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O) (h : PS k 2 d), (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) → ∃ B' : FB k d O, B'.G.F = B.G.F ∧ B'.A.act = B.A.act ∧ B.ph1 = B'.ph1 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) ∧ B.ph2 = B'.ph2 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) ∧ B.sy = B'.sy * FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) ∧ ∀ a : O, B.ad a = B'.ad a * FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ ∀ a : O, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → (∀ a, B.ad a = 1) → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ (∀ a : O, (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) = 0) ∧ B.sy = FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h)) → CanonGaugeSt := by
  intro hbc hrg s1 s2 s3 s4 R _ d O _ _ _ _ _ k _ _ _ B
  obtain ⟨B0, hF0, hA0, hp10, hp20, hsy0, had0⟩ := hbc R k (algebraMap R k) d O B
  have eF : B.FK k = B0.G.F := funext fun i => (hF0 i).symm
  have eA : ∀ a, B.actK k a = B0.A.act a := fun a => funext fun i => (hA0 a i).symm
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have C1 := cob_three (n := 3) ![pt k d 0, pt k d 2] ![pt k d 1, pt k d 2]
    ![addOf B0.G.F (pt k d 0) (pt k d 1), pt k d 2] (pair_points_zero_constant (hp _) (hp _)) (pair_points_zero_constant (hp _) (hp _))
    (pair_points_zero_constant (gp_addOf _ B0.G.const _ _ (hp _) (hp _)) (hp _))
  have C2 := cob_three (n := 3) ![pt k d 0, pt k d 1] ![pt k d 0, pt k d 2]
    ![pt k d 0, addOf B0.G.F (pt k d 1) (pt k d 2)] (pair_points_zero_constant (hp _) (hp _)) (pair_points_zero_constant (hp _) (hp _))
    (pair_points_zero_constant (hp _) (gp_addOf _ B0.G.const _ _ (hp _) (hp _)))
  have CS := cob_swap ![pt k d 1, pt k d 0] (pair_points_zero_constant (hp _) (hp _))
  have CA := fun a : O => cob_two (n := 2) ![comp1 (B0.A.act a) (pt k d 0), pt k d 1]
    ![pt k d 0, comp1 (B0.A.act (star a)) (pt k d 1)]
    (pair_points_zero_constant (gp_comp1 _ _ (B0.A.const a) (hp _)) (hp _))
    (pair_points_zero_constant (hp _) (gp_comp1 _ _ (B0.A.const (star a)) (hp _)))

  obtain ⟨h1, ax1, t1⟩ := s1 k d O B0
  have c1 := const_of_ax ax1.1
  obtain ⟨B1, F1, A1, p11, p21, sy1, ad1⟩ := hrg k d O B0 h1 ax1
  have q11 : B1.ph1 = 1 := cancel_expS (C1.const _ c1) (t1.symm.trans p11)

  obtain ⟨h2, ax2, z12, t2⟩ := s2 k d O B1 q11
  have c2 := const_of_ax ax2.1
  obtain ⟨B2, F2, A2, p12, p22, sy2, ad2⟩ := hrg k d O B1 h2 ax2
  have q12 : B2.ph1 = 1 := by
    rw [z12, nt_expS_zero, mul_one, q11] at p12; exact p12.symm
  rw [F1] at t2 p12 p22
  rw [A1] at ad2
  have q22 : B2.ph2 = 1 := cancel_expS (C2.const _ c2) (t2.symm.trans p22)

  obtain ⟨h3, ax3, z13, z23, t3⟩ := s3 k d O B2 q12 q22
  have c3 := const_of_ax ax3.1
  obtain ⟨B3, F3, A3, p13, p23, sy3, ad3⟩ := hrg k d O B2 h3 ax3
  have q13 : B3.ph1 = 1 := by
    rw [z13, nt_expS_zero, mul_one, q12] at p13; exact p13.symm
  have q23 : B3.ph2 = 1 := by
    rw [z23, nt_expS_zero, mul_one, q22] at p23; exact p23.symm
  rw [F2, F1] at p13 p23
  rw [A2, A1] at ad3 t3
  have qa3 : ∀ a, B3.ad a = 1 := fun a =>
    cancel_expS ((CA a).const _ c3) ((t3 a).symm.trans (ad3 a))

  obtain ⟨h4, ax4, z14, z24, za4, t4⟩ := s4 k d O B3 q13 q23 qa3
  have c4 := const_of_ax ax4.1
  rw [F3, F2, F1] at z14 z24
  rw [A3, A2, A1] at za4
  have g0 : ∀ j, GP ((![0, pt k d 0] : Fin 2 → Pt k 1 d) j) := pair_points_zero_constant gp_zero₂ (hp _)
  have g1 : ∀ j, GP ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j) := pair_points_zero_constant (hp _) gp_zero₂
  refine ⟨h1 + h2 + h3 + h4, ?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_add _ g0, gt_ev_add _ g0, gt_ev_add _ g0, ax1.1, ax2.1, ax3.1, ax4.1]; simp
  · rw [gt_ev_add _ g1, gt_ev_add _ g1, gt_ev_add _ g1, ax1.2, ax2.2, ax3.2, ax4.2]; simp
  · rw [eF]
    exact hp10.symm.trans (C1.chain c1 c2 c3 c4 p11 p12 p13 (by
      rw [q13, z14, nt_expS_zero]))
  · rw [eF]
    exact hp20.symm.trans (C2.chain c1 c2 c3 c4 p21 p22 p23 (by
      rw [q23, z24, nt_expS_zero]))
  · exact hsy0.symm.trans (CS.chain c1 c2 c3 c4 sy1 sy2 sy3 t4)
  · rw [eA, eA]
    exact (had0 a).symm.trans ((CA a).chain c1 c2 c3 c4 (ad1 a) (ad2 a) (ad3 a) (by
      rw [qa3 a, za4 a, nt_expS_zero]))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.DerivationInnerOfSeparabilityElement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem derivation_inner_of_separability_element (O : Type) [CommRing O] (N : ℕ)
    (e : TensorProduct ℤ O O) (hN : 0 < N) (he : Algebra.TensorProduct.lmul' ℤ e = (N : O))
    (hc : ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0)
    (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V)
    (hlr : ∀ a b, Commute (l a) (r b)) (δ : O →+ V)
    (hδ : ∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) :
    ∃ v : V, ∀ a, δ a = l a v - r a v := by
  let Φ : TensorProduct ℤ O O →ₗ[ℤ] V := TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun a b => l a (δ b))
      (fun a a' b => by simp) (fun n a b => by simp)
      (fun a b b' => by simp) (fun n a b => by rw [map_zsmul, map_zsmul]))
  have hΦ : ∀ a b, Φ (TensorProduct.tmul ℤ a b) = l a (δ b) := fun a b => TensorProduct.lift.tmul a b
  have h1 : ∀ (c : O) (t : TensorProduct ℤ O O),
      Φ (TensorProduct.tmul ℤ c (1 : O) * t) = l c (Φ t) := by
    intro c t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, hΦ]
    | add x y hx hy => simp [mul_add, hx, hy]
  have h2 : ∀ (c : O) (t : TensorProduct ℤ O O),
      Φ (TensorProduct.tmul ℤ (1 : O) c * t)
        = l (Algebra.TensorProduct.lmul' ℤ t) (δ c) + r c (Φ t) := by
    intro c t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have h := LinearMap.congr_fun (hlr a c).eq (δ b)
      simp only [Module.End.mul_apply] at h
      simp [Algebra.TensorProduct.tmul_mul_tmul, hΦ, hδ, h]
    | add x y hx hy =>
      simp only [mul_add, map_add (f := _), hx, hy, LinearMap.add_apply]
      abel
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨(N : ℚ)⁻¹ • Φ e, fun c => ?_⟩
  have h := congrArg Φ (hc c)
  rw [sub_mul, map_sub, h1, h2, he, map_zero, map_natCast, Module.End.natCast_apply] at h
  have h' : l c (Φ e) - r c (Φ e) = (N : ℚ) • δ c := by
    rw [Nat.cast_smul_eq_nsmul]
    rw [sub_eq_zero] at h
    rw [h]; abel
  rw [map_smul, map_smul, ← smul_sub, h', smul_smul, inv_mul_cancel₀ hN', one_smul]

theorem derivation_inner_of_reduced_order :
    (∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O], ∃ (N : ℕ) (e : TensorProduct ℤ O O), 0 < N ∧ Algebra.TensorProduct.lmul' ℤ e = (N : O) ∧ ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0) → ∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V), (∀ a b, Commute (l a) (r b)) → ∀ δ : O →+ V, (∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) → ∃ v : V, ∀ a, δ a = l a v - r a v := by
  intro H O _ _ _ _ V _ _ l r hlr δ hδ
  obtain ⟨N, e, hN, he, hc⟩ := H O
  exact derivation_inner_of_separability_element O N e hN he hc V l r hlr δ hδ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSeriesSubstPointsStandardThree
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Sum

namespace GlobalTheory.FormalCocycle

section Tools

variable {k : Type} [CommRing k] {d : ℕ} {μ ν : Type}

def evAt {m : ℕ} (a : Fin m → Fin d → MvPowerSeries μ k) (f : PS k m d) : MvPowerSeries μ k :=
  subst (fun p : Fin m × Fin d => a p.1 p.2) f

def Cen (u : Fin d → MvPowerSeries μ k) : Prop := ∀ i, constantCoeff (u i) = 0

theorem ev_eq {m n : ℕ} (a : Fin m → Pt k n d) (f : PS k m d) : ev a f = evAt a f := rfl

theorem cen1 {u : Fin d → MvPowerSeries μ k} (hu : Cen u) : ∀ j, Cen (![u] j) := by
  intro j; fin_cases j; exact hu

theorem cen2 {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) :
    ∀ j, Cen (![u, v] j) := by
  intro j; fin_cases j; exacts [hu, hv]

theorem cen3 {u v w : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w) :
    ∀ j, Cen (![u, v, w] j) := by
  intro j; fin_cases j; exacts [hu, hv, hw]

theorem cen4 {u v w t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w)
    (ht : Cen t) : ∀ j, Cen (![u, v, w, t] j) := by
  intro j; fin_cases j; exacts [hu, hv, hw, ht]

theorem cen_zero : Cen (0 : Fin d → MvPowerSeries μ k) := fun _ => by simp

theorem cen_X (g : Fin d → μ) : Cen (fun i => (X (g i) : MvPowerSeries μ k)) := fun _ => by simp

theorem cen_pt {n : ℕ} (j : Fin n) : Cen (pt k d j) := fun _ => by simp [pt]

theorem cen_add {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) : Cen (u + v) :=
  fun i => by simp [hu i, hv i]

theorem hasSubst_pts {m : ℕ} {a : Fin m → Fin d → MvPowerSeries μ k} (ha : ∀ j, Cen (a j)) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2

theorem cen_evAt {m : ℕ} {a : Fin m → Fin d → MvPowerSeries μ k} (ha : ∀ j, Cen (a j))
    {F : Fin d → PS k m d} (hF : ∀ i, constantCoeff (F i) = 0) : Cen fun i => evAt a (F i) :=
  fun i => constantCoeff_subst_eq_zero (hasSubst_pts ha) (fun p => ha p.1 p.2) (hF i)

theorem subst_evAt {m : ℕ} {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {a : Fin m → Fin d → MvPowerSeries μ k} (ha : ∀ j, Cen (a j)) (f : PS k m d) :
    subst b (evAt a f) = evAt (fun j i => subst b (a j i)) f :=
  subst_comp_subst_apply (hasSubst_pts ha) hb f

theorem subst_evAt1 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u : Fin d → MvPowerSeries μ k} (hu : Cen u) (f : PS k 1 d) :
    subst b (evAt ![u] f) = evAt ![fun i => subst b (u i)] f := by
  rw [subst_evAt hb (cen1 hu)]
  congr 1; funext j; fin_cases j; rfl

theorem subst_evAt2 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (f : PS k 2 d) :
    subst b (evAt ![u, v] f) = evAt ![fun i => subst b (u i), fun i => subst b (v i)] f := by
  rw [subst_evAt hb (cen2 hu hv)]
  congr 1; funext j; fin_cases j <;> rfl

theorem subst_evAt3 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u v w : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w) (f : PS k 3 d) :
    subst b (evAt ![u, v, w] f) =
      evAt ![fun i => subst b (u i), fun i => subst b (v i), fun i => subst b (w i)] f := by
  rw [subst_evAt hb (cen3 hu hv hw)]
  congr 1; funext j; fin_cases j <;> rfl

theorem subst_pt {m : ℕ} {a : Fin m → Fin d → MvPowerSeries μ k} (ha : ∀ j, Cen (a j))
    (j : Fin m) : (fun i => subst (fun p : Fin m × Fin d => a p.1 p.2) (pt k d j i)) = a j :=
  funext fun i => subst_X (hasSubst_pts ha) (j, i)

theorem subst_zero_pt {b : μ → MvPowerSeries ν k} (hb : HasSubst b) :
    (fun i => subst b ((0 : Fin d → MvPowerSeries μ k) i)) = (0 : Fin d → MvPowerSeries ν k) :=
  funext fun _ => GlobalTheory.FormalCalc.subst_zero' hb

def addAt (F : Fin d → PS k 2 d) (u v : Fin d → MvPowerSeries μ k) :
    Fin d → MvPowerSeries μ k := fun i => evAt ![u, v] (F i)

def mapAt (φ : Pt k 1 d) (u : Fin d → MvPowerSeries μ k) : Fin d → MvPowerSeries μ k :=
  fun i => evAt ![u] (φ i)

theorem cen_addAt {F : Fin d → PS k 2 d} (hF : ∀ i, constantCoeff (F i) = 0)
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) : Cen (addAt F u v) :=
  cen_evAt (cen2 hu hv) hF

theorem cen_mapAt {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0)
    {u : Fin d → MvPowerSeries μ k} (hu : Cen u) : Cen (mapAt φ u) :=
  cen_evAt (cen1 hu) hφ

theorem subst_addAt {b : μ → MvPowerSeries ν k} (hb : HasSubst b) (F : Fin d → PS k 2 d)
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) :
    (fun i => subst b (addAt F u v i)) =
      addAt F (fun i => subst b (u i)) fun i => subst b (v i) :=
  funext fun i => subst_evAt2 hb hu hv (F i)

theorem subst_mapAt {b : μ → MvPowerSeries ν k} (hb : HasSubst b) (φ : Pt k 1 d)
    {u : Fin d → MvPowerSeries μ k} (hu : Cen u) :
    (fun i => subst b (mapAt φ u i)) = mapAt φ fun i => subst b (u i) :=
  funext fun i => subst_evAt1 hb hu (φ i)

theorem mapAt_zero {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    mapAt φ (0 : Fin d → MvPowerSeries μ k) = 0 := by
  funext i
  change subst (fun p : Fin 1 × Fin d => (![(0 : Fin d → MvPowerSeries μ k)] p.1) p.2) (φ i) = 0
  have e : (fun p : Fin 1 × Fin d => (![(0 : Fin d → MvPowerSeries μ k)] p.1) p.2) = 0 := by
    funext p; simp
  rw [e]
  exact subst_zero_of_constantCoeff_zero (hφ i)

theorem mapAt_mapAt {φ ψ : Pt k 1 d} (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (h : comp1 φ ψ = pt k (n := 1) d 0) {u : Fin d → MvPowerSeries μ k} (hu : Cen u) :
    mapAt φ (mapAt ψ u) = u := by
  have hb := hasSubst_pts (cen1 hu)
  have h1 := subst_mapAt hb φ (u := ψ) hψ
  have h2 : mapAt φ ψ = pt k (n := 1) d 0 := h
  rw [h2, subst_pt (cen1 hu)] at h1
  exact h1.symm

theorem mapAt_addAt {ℓ : Pt k 1 d} (hℓ : ∀ i, constantCoeff (ℓ i) = 0)
    {F : Fin d → PS k 2 d} (hF : ∀ i, constantCoeff (F i) = 0)
    (h : comp1 ℓ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1))
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) :
    mapAt ℓ (addAt F u v) = mapAt ℓ u + mapAt ℓ v := by
  have ha := cen2 hu hv
  have hb := hasSubst_pts ha
  have h2 : mapAt ℓ (addAt F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      mapAt ℓ (pt k (n := 2) d 0) + mapAt ℓ (pt k (n := 2) d 1) := h
  have h1 := subst_mapAt hb ℓ (cen_addAt hF (cen_pt (n := 2) 0) (cen_pt 1))
  rw [h2, subst_addAt hb F (cen_pt 0) (cen_pt 1), subst_pt ha, subst_pt ha] at h1
  have h3 := subst_mapAt hb ℓ (cen_pt (k := k) (d := d) (n := 2) 0)
  have h4 := subst_mapAt hb ℓ (cen_pt (k := k) (d := d) (n := 2) 1)
  rw [subst_pt ha] at h3 h4
  refine h1.symm.trans (funext fun i => ?_)
  rw [Pi.add_apply, subst_add hb, congrFun h3 i, congrFun h4 i]
  rfl

theorem formalSeriesSubstPoints_standard_three (c : PS k 3 d) : evAt ![pt k (n := 3) d 0, pt k d 1, pt k d 2] c = c := by
  have e : (fun p : Fin 3 × Fin d => (![pt k (n := 3) d 0, pt k d 1, pt k d 2] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [evAt, e, subst_self]
  rfl

theorem axis_at {c : PS k 3 d} (h : ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0)
    {u t : Fin d → MvPowerSeries μ k} (hu : Cen u) (ht : Cen t) : evAt ![0, u, t] c = 0 := by
  have ha := cen2 hu ht
  have hb := hasSubst_pts ha
  have h1 := congrArg (subst (fun p : Fin 2 × Fin d => ![u, t] p.1 p.2)) h
  rw [ev_eq, subst_evAt3 hb cen_zero (cen_pt 0) (cen_pt 1), subst_zero_pt hb, subst_pt ha,
    subst_pt ha, GlobalTheory.FormalCalc.subst_zero' hb] at h1
  exact h1

theorem symm_at {c : PS k 3 d} (h : ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c)
    {u v t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (ht : Cen t) :
    evAt ![v, u, t] c = evAt ![u, v, t] c := by
  have ha := cen3 hu hv ht
  have hb := hasSubst_pts ha
  have h1 := congrArg (subst (fun p : Fin 3 × Fin d => ![u, v, t] p.1 p.2)) h
  rw [ev_eq, subst_evAt3 hb (cen_pt 1) (cen_pt 0) (cen_pt 2), subst_pt ha,
    subst_pt ha, subst_pt ha] at h1
  exact h1

theorem cocycle_at {F : Fin d → PS k 2 d} (hF : ∀ i, constantCoeff (F i) = 0) {c : PS k 3 d}
    (h : ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c +
        ev (n := 4) ![addOf F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c =
      ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c +
        ev (n := 4) ![pt k d 0, addOf F (pt k d 1) (pt k d 2), pt k d 3] c)
    {u v w t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w) (ht : Cen t) :
    evAt ![u, v, t] c + evAt ![addAt F u v, w, t] c =
      evAt ![v, w, t] c + evAt ![u, addAt F v w, t] c := by
  have ha := cen4 hu hv hw ht
  have hb := hasSubst_pts ha
  have h0 : evAt ![pt k (n := 4) d 0, pt k d 1, pt k d 3] c +
        evAt ![addAt F (pt k (n := 4) d 0) (pt k d 1), pt k d 2, pt k d 3] c =
      evAt ![pt k (n := 4) d 1, pt k d 2, pt k d 3] c +
        evAt ![pt k (n := 4) d 0, addAt F (pt k d 1) (pt k d 2), pt k d 3] c := h
  have h1 := congrArg (subst (fun p : Fin 4 × Fin d => ![u, v, w, t] p.1 p.2)) h0
  rw [subst_add hb, subst_add hb, subst_evAt3 hb (cen_pt 0) (cen_pt 1) (cen_pt 3),
    subst_evAt3 hb (cen_addAt hF (cen_pt 0) (cen_pt 1)) (cen_pt 2) (cen_pt 3),
    subst_evAt3 hb (cen_pt 1) (cen_pt 2) (cen_pt 3),
    subst_evAt3 hb (cen_pt 0) (cen_addAt hF (cen_pt 1) (cen_pt 2)) (cen_pt 3),
    subst_addAt hb F (cen_pt 0) (cen_pt 1), subst_addAt hb F (cen_pt 1) (cen_pt 2)] at h1
  simp only [subst_pt ha] at h1
  exact h1

theorem hasSubst_elim2 {u t : Fin d → MvPowerSeries μ k} (hu : Cen u) (ht : Cen t) :
    HasSubst (Sum.elim u t) :=
  hasSubst_of_constantCoeff_zero (by rintro (i | i); exacts [hu i, ht i])

theorem hasSubst_elim3 {u v t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (ht : Cen t) :
    HasSubst (Sum.elim u (Sum.elim v t)) :=
  hasSubst_of_constantCoeff_zero (by rintro (i | i | i); exacts [hu i, hv i, ht i])

theorem subst_elim2 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u t : Fin d → MvPowerSeries μ k} (hu : Cen u) (ht : Cen t)
    (K : MvPowerSeries (Fin d ⊕ Fin d) k) :
    subst b (subst (Sum.elim u t) K) =
      subst (Sum.elim (fun i => subst b (u i)) fun i => subst b (t i)) K := by
  rw [subst_comp_subst_apply (hasSubst_elim2 hu ht) hb, GlobalTheory.FormalCalc.subst_sumElim]

end Tools

theorem exists_coboundary_of_symm_cocycle :
    LogSt → (∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) → IsUnit (dLin φ).det → ∃ φi : Pt k 1 d, IsInvPair φ φi) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (c : PS k 3 d), ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 → ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c → ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c + ev (n := 4) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c = ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c + ev (n := 4) ![pt k d 0, addOf G.F (pt k d 1) (pt k d 2), pt k d 3] c → ∃ h : PS k 2 d, ev (n := 1) ![0, pt k d 0] h = 0 ∧ (∀ i, ev (n := 1) ![0, pt k d 0] (pderiv ((0 : Fin 2), i) h) = 0) ∧ c = (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2] h) := by
  intro hlog hinv k _ _ d G c hax hsy hco
  obtain ⟨ℓ, hℓ, hlin, hadd⟩ := hlog k d G
  obtain ⟨e, -, he, hle, hel⟩ := hinv k d ℓ hℓ (by rw [hlin, Matrix.det_one]; exact isUnit_one)
  have hF := G.const
  have hexp : ∀ {μ : Type} {u v : Fin d → MvPowerSeries μ k}, Cen u → Cen v →
      addAt G.F (mapAt e u) (mapAt e v) = mapAt e (u + v) := by
    intro μ u v hu hv
    have h1 := mapAt_addAt hℓ hF hadd (cen_mapAt he hu) (cen_mapAt he hv)
    rw [mapAt_mapAt he hle hu, mapAt_mapAt he hle hv] at h1
    rw [← h1, mapAt_mapAt hℓ hel (cen_addAt hF (cen_mapAt he hu) (cen_mapAt he hv))]
  obtain ⟨B, hB⟩ : ∃ B : MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) k,
      ∀ {μ : Type} {u v t : Fin d → MvPowerSeries μ k}, Cen u → Cen v → Cen t →
        subst (Sum.elim u (Sum.elim v t)) B = evAt ![mapAt e u, mapAt e v, t] c := by
    refine ⟨evAt ![mapAt e fun i => X (inl i), mapAt e fun i => X (inr (inl i)),
      fun i => X (inr (inr i))] c, ?_⟩
    intro μ u v t hu hv ht
    have hb := hasSubst_elim3 hu hv ht
    rw [subst_evAt3 hb (cen_mapAt he (cen_X _)) (cen_mapAt he (cen_X _)) (cen_X _),
      subst_mapAt hb e (cen_X _), subst_mapAt hb e (cen_X _)]
    simp only [subst_X hb, elim_inl, elim_inr]
  have hBX : B = evAt ![mapAt e fun i => X (inl i), mapAt e fun i => X (inr (inl i)),
      fun i => X (inr (inr i))] c := by
    rw [← hB (cen_X _) (cen_X _) (cen_X _), GlobalTheory.FormalCalc.subst_elim_elim_X]
  obtain ⟨K, ⟨hK0, hK1, hK⟩, -⟩ := GlobalTheory.FormalCalc.existsUnique_coboundary_param (B := B)
    (by
      have h1 := hB (μ := Fin d) (u := 0) (v := 0) (t := X) cen_zero cen_zero (cen_X id)
      rw [mapAt_zero he] at h1
      exact h1.trans (axis_at hax cen_zero (cen_X id)))
    (by
      rw [hB (cen_X _) (cen_X _) (cen_X _)]
      conv_rhs => rw [hBX]
      exact symm_at hsy (cen_mapAt he (cen_X _)) (cen_mapAt he (cen_X _)) (cen_X _))
    (by
      rw [hB (cen_X _) (cen_X _) (cen_X _), hB (cen_X _) (cen_X _) (cen_X _)]
      have h1 := hB (μ := Fin d ⊕ Fin d ⊕ Fin d ⊕ Fin d)
        (cen_add (cen_X fun i => inl i) (cen_X fun i => inr (inl i)))
        (cen_X fun i => inr (inr (inl i))) (cen_X fun i => inr (inr (inr i)))
      have h2 := hB (μ := Fin d ⊕ Fin d ⊕ Fin d ⊕ Fin d) (cen_X fun i => inl i)
        (cen_add (cen_X fun i => inr (inl i)) (cen_X fun i => inr (inr (inl i))))
        (cen_X fun i => inr (inr (inr i)))
      rw [← hexp (cen_X _) (cen_X _)] at h1 h2
      have h3 := cocycle_at hF hco (μ := Fin d ⊕ Fin d ⊕ Fin d ⊕ Fin d)
        (cen_mapAt he (cen_X fun i => inl i)) (cen_mapAt he (cen_X fun i => inr (inl i)))
        (cen_mapAt he (cen_X fun i => inr (inr (inl i)))) (cen_X fun i => inr (inr (inr i)))
      rw [← h1, ← h2] at h3
      exact h3)
  have hp : ∀ {n : ℕ} (j : Fin n), Cen (pt k d j) := cen_pt
  have hev : ∀ {n : ℕ} {u t : Pt k n d} (L : MvPowerSeries (Fin d ⊕ Fin d) k), Cen u → Cen t →
      ev ![u, t] (subst (Sum.elim (mapAt ℓ (pt k (n := 2) d 0)) (pt k d 1)) L) =
        subst (Sum.elim (mapAt ℓ u) t) L := by
    intro n u t L hu ht
    have ha := cen2 hu ht
    have hb := hasSubst_pts ha
    rw [ev, subst_elim2 hb (cen_mapAt hℓ (hp 0)) (hp 1), subst_mapAt hb ℓ (hp 0), subst_pt ha,
      subst_pt ha]
    rfl
  have hzero : ∀ L : MvPowerSeries (Fin d ⊕ Fin d) k,
      subst (Sum.elim (fun _ => 0) X : Fin d ⊕ Fin d → MvPowerSeries (Fin d) k) L = 0 →
      ev (n := 1) ![0, pt k d 0]
        (subst (Sum.elim (mapAt ℓ (pt k (n := 2) d 0)) (pt k d 1)) L) = 0 := by
    intro L hL
    rw [hev L cen_zero (hp 0), mapAt_zero hℓ]
    have hb : HasSubst (pt k (n := 1) d 0) := hasSubst_of_constantCoeff_zero (hp 0)
    have h1 := subst_elim2 hb (u := 0) (t := X) cen_zero (cen_X id) L
    rw [subst_zero_pt hb] at h1
    simp only [subst_X hb] at h1
    refine h1.symm.trans ?_
    exact (congrArg _ hL).trans (GlobalTheory.FormalCalc.subst_zero' hb)
  have hneg : ∀ {m n : ℕ} {a : Fin m → Pt k n d}, (∀ j, Cen (a j)) → ∀ f : PS k m d,
      ev a (-f) = - ev a f := by
    intro m n a ha f
    unfold ev
    rw [← coe_substAlgHom (hasSubst_pts ha), map_neg]
  refine ⟨-subst (Sum.elim (mapAt ℓ (pt k (n := 2) d 0)) (pt k d 1)) K, ?_, fun i => ?_, ?_⟩
  · rw [hneg (cen2 cen_zero (hp 0)), hzero K hK0, neg_zero]
  · have hb := hasSubst_pts (cen2 (cen_zero (μ := Fin 1 × Fin d)) (hp 0))
    rw [map_neg, hneg (cen2 cen_zero (hp 0)), neg_eq_zero,
      GlobalTheory.FormalCalc.pderiv_subst (hasSubst_elim2 (cen_mapAt hℓ (hp 0)) (hp 1)), Fintype.sum_sum_type]
    have h2 : ∀ j : Fin d, pderiv ((0 : Fin 2), i) (pt k (n := 2) d 1 j) = 0 := fun j =>
      pderiv_X_of_ne (by simp)
    simp only [elim_inl, elim_inr, h2, mul_zero, Finset.sum_const_zero, add_zero]
    rw [ev, GlobalTheory.FormalCalc.subst_sum' hb]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h3 := hzero _ (hK1 j)
    rw [ev] at h3
    rw [subst_mul hb, h3, zero_mul]
  · have hA : Cen (addOf G.F (pt k (n := 3) d 0) (pt k d 1)) := cen_addAt hF (hp 0) (hp 1)
    rw [hneg (cen2 (hp 0) (hp 2)), hneg (cen2 (hp 1) (hp 2)), hneg (cen2 hA (hp 2)),
      hev K (hp 0) (hp 2), hev K (hp 1) (hp 2), hev K hA (hp 2)]
    have hl0 := cen_mapAt hℓ (hp (n := 3) 0)
    have hl1 := cen_mapAt hℓ (hp (n := 3) 1)
    have hb := hasSubst_elim3 hl0 hl1 (hp 2)
    have h1 := hB hl0 hl1 (hp 2)
    rw [mapAt_mapAt hℓ hel (hp 0), mapAt_mapAt hℓ hel (hp 1), formalSeriesSubstPoints_standard_three, hK, subst_sub hb,
      subst_sub hb, subst_elim2 hb (fun _ => by simp) (cen_X _), subst_elim2 hb (cen_X _) (cen_X _),
      subst_elim2 hb (cen_X _) (cen_X _)] at h1
    simp only [subst_add hb, subst_X hb, elim_inl, elim_inr] at h1
    have h4 : mapAt ℓ (addOf G.F (pt k (n := 3) d 0) (pt k d 1)) =
        fun i => mapAt ℓ (pt k (n := 3) d 0) i + mapAt ℓ (pt k (n := 3) d 1) i :=
      mapAt_addAt hℓ hF hadd (hp 0) (hp 1)
    rw [h4, ← h1]
    ring

end GlobalTheory.FormalCocycle
end
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem canonGauge_of_log : LogSt → CanonGaugeSt := fun hlog =>
  have hcob := FormalCocycle.exists_coboundary_of_symm_cocycle hlog ChartInv.exists_isInvPair
  have huniq := AdditiveSeries.eq_zero_of_additive_of_pderiv
  canonGauge_of_steps exists_formalBiext_map exists_regauge
    (GaugeFirstLaw.exists_gauge_first_law hcob huniq)
    (SecondLawGauge.exists_gauge_second_law hcob huniq)
    (ActionGauge.exists_action_gauge
      (derivation_inner_of_reduced_order SepIdem.exists_separability_element))
    SymGauge.exists_gauge_of_symmetry

end GlobalTheory
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem canonGauge_exists : CanonGaugeSt :=
  canonGauge_of_log FormalLog.logSt_and_logDerivSt.1

end GlobalTheory
