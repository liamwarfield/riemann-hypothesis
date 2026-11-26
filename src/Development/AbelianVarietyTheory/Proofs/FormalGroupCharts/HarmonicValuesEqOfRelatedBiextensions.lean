module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalChartJetRelUnitOneOnAxes
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsBiadditiveSeriesJetEqOfBiadditiveJet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetEqFormalExpIffAndExistsLog
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetEqFormalExpIffAndExistsLog
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jeq_pow_congr {R σ : Type} [CommRing R] {m : ℕ} {a b : MvPowerSeries σ R} (h : JEq m a b) (n : ℕ) :
    JEq m (a ^ n) (b ^ n) := by
  classical
  induction n with
  | zero => intro e _; rw [pow_zero, pow_zero]
  | succ n ih =>
    intro e he
    rw [pow_succ, pow_succ, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hd : p.1.degree + p.2.degree = e.degree := by rw [← map_add (f := _), hp]
    rw [ih p.1 (by omega), h p.2 (by omega)]

theorem jeq_psubst_congr {R σ : Type} [CommRing R] {m : ℕ} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (h : JEq m a b)
    (F : PowerSeries R) : JEq m (PowerSeries.subst a F) (PowerSeries.subst b F) := by
  intro e he
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hb)]
  refine finsum_congr fun n => ?_
  rw [jeq_pow_congr h n e he]

theorem jeq_expS_iff_and_exists_log : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d m : ℕ), (∀ f g : PS k n d, MvPowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff g = 0 → (JEq m f g ↔ JEq m (FB.expS k f) (FB.expS k g))) ∧ ∀ u : PS k n d, MvPowerSeries.constantCoeff u = 1 → ∃ lam : PS k n d, MvPowerSeries.constantCoeff lam = 0 ∧ FB.expS k lam = u := by
  intro k _ _ n d m
  refine ⟨fun f g hf hg => ⟨fun h => jeq_psubst_congr hf hg h _, fun h => ?_⟩, fun u hu => ?_⟩
  · have h1 : JEq m (PowerSeries.subst f (PowerSeries.exp k) - 1) (PowerSeries.subst g (PowerSeries.exp k) - 1) := by
      intro e he
      rw [map_sub, map_sub]
      exact congrArg (· - _) (h e he)
    have h2 := jeq_psubst_congr (by simp [TB.WickVanishing.constantCoeff_exp hf]) (by simp [TB.WickVanishing.constantCoeff_exp hg]) h1
      (PowerSeries.log k)
    rwa [TB.WickVanishing.log_exp hf, TB.WickVanishing.log_exp hg] at h2
  · exact ⟨_, TB.WickVanishing.constantCoeff_logS hu, TB.WickVanishing.exp_log hu⟩

end GlobalTheory.ChartCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetEqFormalExpIffAndExistsLogStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetEq_formalExp_iff_and_exists_log : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d m : ℕ), (∀ f g : PS k n d, MvPowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff g = 0 → (JEq m f g ↔ JEq m (FB.expS k f) (FB.expS k g))) ∧ ∀ u : PS k n d, MvPowerSeries.constantCoeff u = 1 → ∃ lam : PS k n d, MvPowerSeries.constantCoeff lam = 0 ∧ FB.expS k lam = u := by
  first | exact @GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log | exact GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log | (intros; apply GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonicalGaugeDifferenceBiadditiveJet
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonicalGaugeDifferenceBiadditiveJet
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open MvPowerSeries

namespace GlobalTheory.ChartCmp.GaugeDiff

section Map
variable {R k : Type} [CommRing R] [CommRing k] {d : ℕ} (β : R →+* k)

def mapPt {n : ℕ} (a : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map β (a i)

theorem map_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j, GP (a j)) (f : PS R m d) :
    MvPowerSeries.map β (ev a f) = ev (fun j => mapPt β (a j)) (MvPowerSeries.map β f) :=
  MvPowerSeries.map_subst (gt_hasSubst a ha) f

theorem map_ev1 {n : ℕ} (a : Pt R n d) (ha : GP a) (f : PS R 1 d) :
    MvPowerSeries.map β (ev ![a] f) = ev ![mapPt β a] (MvPowerSeries.map β f) := by
  rw [map_ev β _ (single_point_zero_constant ha)]
  congr 1
  funext j; fin_cases j; rfl

theorem map_ev2 {n : ℕ} (a b : Pt R n d) (ha : GP a) (hb : GP b) (f : PS R 2 d) :
    MvPowerSeries.map β (ev ![a, b] f) = ev ![mapPt β a, mapPt β b] (MvPowerSeries.map β f) := by
  rw [map_ev β _ (pair_points_zero_constant ha hb)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem map_ev3 {n : ℕ} (a b c : Pt R n d) (ha : GP a) (hb : GP b) (hc : GP c) (f : PS R 3 d) :
    MvPowerSeries.map β (ev ![a, b, c] f) = ev ![mapPt β a, mapPt β b, mapPt β c] (MvPowerSeries.map β f) := by
  rw [map_ev β _ (triple_points_zero_constant ha hb hc)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem constantCoeff_mapPt_eq_zero {n : ℕ} (a : Pt R n d) (ha : GP a) : GP (mapPt β a) := fun i => by
  simp [mapPt, MvPowerSeries.constantCoeff_map, ha i]

theorem mapPt_pt {n : ℕ} (j : Fin n) : mapPt β (pt R d j) = pt k d j := by
  funext i; simp [mapPt, pt]

theorem mapPt_zero {n : ℕ} : mapPt β (0 : Pt R n d) = 0 := by
  funext i; simp [mapPt]

theorem mapPt_comp1 {n : ℕ} (φ : Pt R 1 d) (a : Pt R n d) (ha : GP a) :
    mapPt β (comp1 φ a) = comp1 (mapPt β φ) (mapPt β a) :=
  funext fun i => map_ev1 β a ha (φ i)

theorem mapPt_addOf {n : ℕ} (F : Fin d → PS R 2 d) (a b : Pt R n d) (ha : GP a) (hb : GP b) :
    mapPt β (addOf F a b) = addOf (mapPt β F) (mapPt β a) (mapPt β b) :=
  funext fun i => map_ev2 β a b ha hb (F i)

theorem jeq_map {σ : Type} {m : ℕ} {f g : MvPowerSeries σ R} (h : JEq m f g) :
    JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g) := fun e he => by
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, h e he]

end Map

section Ring
variable {k : Type} [CommRing k] {d : ℕ}

theorem jeq_of_sub {σ : Type} {m : ℕ} {f g u v : MvPowerSeries σ k} (h : JEq m f g) (e : u - v = f - g) :
    JEq m u v := fun x hx => by
  have := congrArg (MvPowerSeries.coeff x) e
  rw [map_sub, map_sub, h x hx, sub_self] at this
  exact sub_eq_zero.1 this

theorem jeq_of_sub' {σ : Type} {m : ℕ} {f g u v : MvPowerSeries σ k} (h : JEq m f g) (e : u - v = g - f) :
    JEq m u v :=
  jeq_of_sub (f := g) (g := f) (fun x hx => (h x hx).symm) e

theorem coordinateChange_comp1_transported_addOf {n : ℕ} {φ φi : Pt k 1 d} (hinv : IsInvPair φ φi) (F F' : Fin d → PS k 2 d) (hBF : GP F)
    (hF : ∀ i, F' i = transF F φ φi i) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    comp1 φ (addOf F' a b) = addOf F (comp1 φ a) (comp1 φ b) := by
  have hφ : GP φ := hinv.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hcφ : ∀ {n : ℕ} (a : Pt k n d), GP a → GP (comp1 φ a) := fun a ha => gp_comp1 φ a hφ ha
  have hAd : GP (addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) :=
    gp_addOf _ hBF _ _ (hcφ _ (hp 0)) (hcφ _ (hp 1))
  have e : addOf F' a b = comp1 φi (addOf F (comp1 φ a) (comp1 φ b)) := by
    funext i
    change ev ![a, b] (F' i) = ev ![addOf F (comp1 φ a) (comp1 φ b)] (φi i)
    rw [hF i]
    change ev ![a, b] (ev ![addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))]
      (φi i)) = _
    rw [gt_ev_ev' ![a, b] _ (pair_points_zero_constant ha hb) (single_point_zero_constant hAd)]
    congr 1
    funext j
    fin_cases j
    change evP ![a, b] (addOf F (comp1 φ (pt k d 0)) (comp1 φ (pt k d 1))) = _
    rw [evP_addOf _ (pair_points_zero_constant ha hb) _ _ _ (hcφ _ (hp 0)) (hcφ _ (hp 1)),
      evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (hp 0), evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (hp 1),
      evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
    rfl
  rw [e, gt_comp_inv hinv _ (gp_addOf _ hBF _ _ (hcφ _ ha) (hcφ _ hb))]

theorem coordinateChange_comp1_intertwines_action {n : ℕ} {φ φi : Pt k 1 d} (hinv : IsInvPair φ φi) (A A' : Pt k 1 d) (hAa : GP A)
    (hA : A' = comp1 φi (comp1 A φ)) (x : Pt k n d) (hx : GP x) :
    comp1 φ (comp1 A' x) = comp1 A (comp1 φ x) := by
  have hφ : GP φ := hinv.1
  rw [hA, gt_comp1_comp1 φi _ (gp_comp1 _ φ hAa hφ) x hx, gt_comp1_comp1 A φ hφ x hx,
    gt_comp_inv hinv _ (gp_comp1 _ _ hAa (gp_comp1 _ _ hφ hx))]

theorem germEv_germEv_two_points {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a b : Pt k m d) (ha : GP a) (hb : GP b)
    (f : PS k 2 d) : ev V (ev ![a, b] f) = ev ![evP V a, evP V b] f := by
  rw [gt_ev_ev' V _ hV (pair_points_zero_constant ha hb), eval_pair_points]

theorem ev_trans {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (h : PS k 2 d) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    ev ![a, b] (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h) =
      ev ![comp1 φ a, comp1 φ b] h := by
  rw [germEv_germEv_two_points _ (pair_points_zero_constant ha hb) _ _ (gp_comp1 _ _ hφ (gp_pt 0)) (gp_comp1 _ _ hφ (gp_pt 1)),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 0),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 1), evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
  rfl

theorem ev_diff {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (h h' lam : PS k 2 d) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    ev ![a, b] (h' - ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h - lam) =
      ev ![a, b] h' - ev ![comp1 φ a, comp1 φ b] h - ev ![a, b] lam := by
  rw [gt_ev_sub _ (pair_points_zero_constant ha hb), gt_ev_sub _ (pair_points_zero_constant ha hb), ev_trans φ hφ h a b ha hb]

variable [Algebra ℚ k]

theorem expS_zero {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [hn]

theorem jeq_log {n m : ℕ} {A B C D : PS k n d} (hA : constantCoeff A = 0) (hB : constantCoeff B = 0)
    (hC : constantCoeff C = 0) (hD : constantCoeff D = 0)
    (h : JEq m (FB.expS k A * FB.expS k B) (FB.expS k C * FB.expS k D)) : JEq m (A + B) (C + D) := by
  rw [← gt_expS_add _ _ hA hB, ← gt_expS_add _ _ hC hD] at h
  exact ((GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log k n d m).1 _ _ (by simp [hA, hB]) (by simp [hC, hD])).2 h

end Ring

theorem biadd_gauge_diff (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ)
    (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d) (J : JRel m B B' φ φi ε)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h h' lam : PS k 2 d)
    (hh : B.IsCanonGauge k h) (hh' : B'.IsCanonGauge k h') (hlam0 : MvPowerSeries.constantCoeff lam = 0)
    (hε : FB.expS k lam = FB.toK k ε) :
    Biadd m B' k (h' - ev (n := 2) ![comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 0),
      comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 1)] h - lam) := by
  set β := algebraMap R k with hβ
  change Biadd m B' k (h' - ev (n := 2) ![comp1 (mapPt β φ) (pt k (n := 2) d 0),
      comp1 (mapPt β φ) (pt k (n := 2) d 1)] h - lam)
  have hε' : MvPowerSeries.map β ε = FB.expS k lam := hε.symm
  have hφ : GP φ := J.inv.1
  have hψ : GP (mapPt β φ) := constantCoeff_mapPt_eq_zero β φ hφ
  have fk : B.FK k = mapPt β B.G.F := rfl
  have fk' : B'.FK k = mapPt β B'.G.F := rfl
  have ak : ∀ a, B.actK k a = mapPt β (B.A.act a) := fun a => rfl
  have ak' : ∀ a, B'.actK k a = mapPt β (B'.A.act a) := fun a => rfl
  have hF : GP B.G.F := B.G.const
  have hF' : GP B'.G.F := B'.G.const
  have hFk := constantCoeff_mapPt_eq_zero β _ hF
  have hFk' := constantCoeff_mapPt_eq_zero β _ hF'
  have hr : ∀ {n : ℕ} (j : Fin n), GP (pt R (n := n) d j) := fun j => gp_pt j
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hcr : ∀ {n : ℕ} (a : Pt R n d), GP a → GP (comp1 φ a) := fun a ha => gp_comp1 φ a hφ ha
  have hc : ∀ {n : ℕ} (a : Pt k n d), GP a → GP (comp1 (mapPt β φ) a) := fun a ha => gp_comp1 _ a hψ ha
  have hz0 : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz0 (hp 0)), map_zero] at this
  have hh0' : constantCoeff h' = 0 := by
    have := congrArg constantCoeff hh'.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz0 (hp 0)), map_zero] at this
  have cW : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ∀ f : PS k 2 d, constantCoeff f = 0 →
      constantCoeff (ev ![a, b] f) = 0 := fun a b ha hb f hf => gt_const_ev _ (pair_points_zero_constant ha hb) f hf
  have Gl : ∀ i j : Fin 3, comp1 (mapPt β φ) (addOf (mapPt β B'.G.F) (pt k d i) (pt k d j)) =
      addOf (mapPt β B.G.F) (comp1 (mapPt β φ) (pt k d i)) (comp1 (mapPt β φ) (pt k d j)) := by
    intro i j
    have := congrArg (mapPt β) (coordinateChange_comp1_transported_addOf J.inv B.G.F B'.G.F hF J.law (pt R d i) (pt R d j) (hr i) (hr j))
    rwa [mapPt_comp1 β _ _ (gp_addOf _ hF' _ _ (hr i) (hr j)), mapPt_addOf β _ _ _ (hr i) (hr j),
      mapPt_addOf β _ _ _ (hcr _ (hr i)) (hcr _ (hr j)), mapPt_comp1 β _ _ (hr i), mapPt_comp1 β _ _ (hr j),
      mapPt_pt, mapPt_pt] at this
  have Ha : ∀ (a : O) (i : Fin 2), comp1 (mapPt β φ) (comp1 (mapPt β (B'.A.act a)) (pt k d i)) =
      comp1 (mapPt β (B.A.act a)) (comp1 (mapPt β φ) (pt k d i)) := by
    intro a i
    have := congrArg (mapPt β) (coordinateChange_comp1_intertwines_action J.inv (B.A.act a) (B'.A.act a) (B.A.const a) (J.act a) (pt R d i) (hr i))
    rwa [mapPt_comp1 β _ _ (gp_comp1 _ _ (B'.A.const a) (hr i)), mapPt_comp1 β _ _ (hr i),
      mapPt_comp1 β _ _ (hcr _ (hr i)), mapPt_comp1 β _ _ (hr i), mapPt_pt] at this
  obtain ⟨-, hx0, hx1⟩ := GlobalTheory.ChartCmp.jRel_axes R d O m B B' φ φi ε J
  refine ⟨?ax0, ?ax1, ?ph1, ?ph2, ?sy, ?ad⟩
  · have e := jeq_map β hx0
    rw [map_ev2 β _ _ gp_zero₂ (hr 0), mapPt_zero, mapPt_pt, hε', map_one,
      gt_ev_expS _ (pair_points_zero_constant hz0 (hp 0)) _ hlam0, ← expS_zero] at e
    have e' := ((GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log k 1 d m).1 _ _ (cW _ _ hz0 (hp 0) _ hlam0) (map_zero _)).2 e
    have t := congrArg (ev ![mapPt β φ]) hh.ax0
    rw [germEv_germEv_two_points _ (single_point_zero_constant hψ) _ _ hz0 (hp 0), evP_zero _ (single_point_zero_constant hψ),
      evP_pt _ (single_point_zero_constant hψ), gt_ev_zero _ (single_point_zero_constant hψ)] at t
    rw [ev_diff _ hψ _ _ _ _ _ hz0 (hp 0), hh'.ax0, gt_comp1_zero _ hψ, gt_comp1_pt_right]
    refine jeq_of_sub' e' ?_
    erw [t]
    ring
  · have e := jeq_map β hx1
    rw [map_ev2 β _ _ (hr 0) gp_zero₂, mapPt_zero, mapPt_pt, hε', map_one,
      gt_ev_expS _ (pair_points_zero_constant (hp 0) hz0) _ hlam0, ← expS_zero] at e
    have e' := ((GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log k 1 d m).1 _ _ (cW _ _ (hp 0) hz0 _ hlam0) (map_zero _)).2 e
    have t := congrArg (ev ![mapPt β φ]) hh.ax1
    rw [germEv_germEv_two_points _ (single_point_zero_constant hψ) _ _ (hp 0) hz0, evP_zero _ (single_point_zero_constant hψ),
      evP_pt _ (single_point_zero_constant hψ), gt_ev_zero _ (single_point_zero_constant hψ)] at t
    rw [ev_diff _ hψ _ _ _ _ _ (hp 0) hz0, hh'.ax1, gt_comp1_zero _ hψ, gt_comp1_pt_right]
    refine jeq_of_sub' e' ?_
    erw [t]
    ring
  · have hq0 := hp (n := 3) 0
    have hq1 := hp (n := 3) 1
    have hq2 := hp (n := 3) 2
    have hV := triple_points_zero_constant (hc _ hq0) (hc _ hq1) (hc _ hq2)
    have hA := gp_addOf _ hFk _ _ hq0 hq1
    have hA' := gp_addOf _ hFk' _ _ hq0 hq1
    have hA'' := gp_addOf _ hFk _ _ (hc _ hq0) (hc _ hq1)
    have e1 : MvPowerSeries.map β B.ph1 = _ := hh.ph1
    have e2 : MvPowerSeries.map β B'.ph1 = _ := hh'.ph1
    rw [fk] at e1
    rw [fk'] at e2
    have e := jeq_map β J.ph1
    rw [map_mul, map_mul, map_mul, map_ev2 β _ _ (gp_addOf _ hF' _ _ (hr 0) (hr 1)) (hr 2),
      map_ev2 β _ _ (hr 0) (hr 2), map_ev2 β _ _ (hr 1) (hr 2),
      map_ev3 β _ _ _ (hcr _ (hr 0)) (hcr _ (hr 1)) (hcr _ (hr 2)), mapPt_addOf β _ _ _ (hr 0) (hr 1),
      mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1), mapPt_comp1 β _ _ (hr 2), mapPt_pt, mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hA' hq2) _ hlam0, gt_ev_expS _ (pair_points_zero_constant hq0 hq2) _ hlam0,
      gt_ev_expS _ (pair_points_zero_constant hq1 hq2) _ hlam0, ← gt_expS_add _ _ (cW _ _ hq0 hq2 _ hlam0) (cW _ _ hq1 hq2 _ hlam0),
      gt_ev_expS _ hV _ (by simp [cW _ _ hq0 hq2 _ hh0, cW _ _ hq1 hq2 _ hh0, cW _ _ hA hq2 _ hh0]),
      gt_ev_sub _ hV, gt_ev_add _ hV, germEv_germEv_two_points _ hV _ _ hq0 hq2, germEv_germEv_two_points _ hV _ _ hq1 hq2, germEv_germEv_two_points _ hV _ _ hA hq2,
      evP_addOf _ hV _ _ _ hq0 hq1, evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e
    have e' := jeq_log
      (by simp [cW _ _ hq0 hq2 _ hh0', cW _ _ hq1 hq2 _ hh0', cW _ _ hA' hq2 _ hh0'])
      (cW _ _ hA' hq2 _ hlam0)
      (by simp [cW _ _ (hc _ hq0) (hc _ hq2) _ hh0, cW _ _ (hc _ hq1) (hc _ hq2) _ hh0,
        cW _ _ hA'' (hc _ hq2) _ hh0])
      (by simp [cW _ _ hq0 hq2 _ hlam0, cW _ _ hq1 hq2 _ hlam0]) e
    rw [fk', ev_diff _ hψ _ _ _ _ _ hA' hq2, ev_diff _ hψ _ _ _ _ _ hq0 hq2, ev_diff _ hψ _ _ _ _ _ hq1 hq2, Gl]
    refine jeq_of_sub' e' ?_
    ring
  · have hq0 := hp (n := 3) 0
    have hq1 := hp (n := 3) 1
    have hq2 := hp (n := 3) 2
    have hV := triple_points_zero_constant (hc _ hq0) (hc _ hq1) (hc _ hq2)
    have hA := gp_addOf _ hFk _ _ hq1 hq2
    have hA' := gp_addOf _ hFk' _ _ hq1 hq2
    have hA'' := gp_addOf _ hFk _ _ (hc _ hq1) (hc _ hq2)
    have e1 : MvPowerSeries.map β B.ph2 = _ := hh.ph2
    have e2 : MvPowerSeries.map β B'.ph2 = _ := hh'.ph2
    rw [fk] at e1
    rw [fk'] at e2
    have e := jeq_map β J.ph2
    rw [map_mul, map_mul, map_mul, map_ev2 β _ _ (hr 0) (gp_addOf _ hF' _ _ (hr 1) (hr 2)),
      map_ev2 β _ _ (hr 0) (hr 1), map_ev2 β _ _ (hr 0) (hr 2),
      map_ev3 β _ _ _ (hcr _ (hr 0)) (hcr _ (hr 1)) (hcr _ (hr 2)), mapPt_addOf β _ _ _ (hr 1) (hr 2),
      mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1), mapPt_comp1 β _ _ (hr 2), mapPt_pt, mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hq0 hA') _ hlam0, gt_ev_expS _ (pair_points_zero_constant hq0 hq1) _ hlam0,
      gt_ev_expS _ (pair_points_zero_constant hq0 hq2) _ hlam0, ← gt_expS_add _ _ (cW _ _ hq0 hq1 _ hlam0) (cW _ _ hq0 hq2 _ hlam0),
      gt_ev_expS _ hV _ (by simp [cW _ _ hq0 hq1 _ hh0, cW _ _ hq0 hq2 _ hh0, cW _ _ hq0 hA _ hh0]),
      gt_ev_sub _ hV, gt_ev_add _ hV, germEv_germEv_two_points _ hV _ _ hq0 hq1, germEv_germEv_two_points _ hV _ _ hq0 hq2, germEv_germEv_two_points _ hV _ _ hq0 hA,
      evP_addOf _ hV _ _ _ hq1 hq2, evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e
    have e' := jeq_log
      (by simp [cW _ _ hq0 hq1 _ hh0', cW _ _ hq0 hq2 _ hh0', cW _ _ hq0 hA' _ hh0'])
      (cW _ _ hq0 hA' _ hlam0)
      (by simp [cW _ _ (hc _ hq0) (hc _ hq1) _ hh0, cW _ _ (hc _ hq0) (hc _ hq2) _ hh0,
        cW _ _ (hc _ hq0) hA'' _ hh0])
      (by simp [cW _ _ hq0 hq1 _ hlam0, cW _ _ hq0 hq2 _ hlam0]) e
    rw [fk', ev_diff _ hψ _ _ _ _ _ hq0 hA', ev_diff _ hψ _ _ _ _ _ hq0 hq1, ev_diff _ hψ _ _ _ _ _ hq0 hq2, Gl]
    refine jeq_of_sub' e' ?_
    ring
  · have hq0 := hp (n := 2) 0
    have hq1 := hp (n := 2) 1
    have hV := pair_points_zero_constant (hc _ hq0) (hc _ hq1)
    have e1 : MvPowerSeries.map β B.sy = _ := hh.sy
    have e2 : MvPowerSeries.map β B'.sy = _ := hh'.sy
    have e := jeq_map β J.sy
    rw [map_mul, map_mul, map_ev2 β _ _ (hr 1) (hr 0), map_ev2 β _ _ (hcr _ (hr 0)) (hcr _ (hr 1)),
      mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1), mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hq1 hq0) _ hlam0,
      gt_ev_expS _ hV _ (by simp [cW _ _ hq1 hq0 _ hh0, hh0]),
      gt_ev_sub _ hV, germEv_germEv_two_points _ hV _ _ hq1 hq0, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    have e' := jeq_log
      (by simp [cW _ _ hq1 hq0 _ hh0', hh0']) hlam0
      (by simp [cW _ _ (hc _ hq0) (hc _ hq1) _ hh0, cW _ _ (hc _ hq1) (hc _ hq0) _ hh0])
      (cW _ _ hq1 hq0 _ hlam0) e
    rw [ev_diff _ hψ _ _ _ _ _ hq1 hq0]
    refine jeq_of_sub e' ?_
    ring
  · intro a
    have hq0 := hp (n := 2) 0
    have hq1 := hp (n := 2) 1
    have hV := pair_points_zero_constant (hc _ hq0) (hc _ hq1)
    have hB'a : GP (B'.A.act a) := B'.A.const a
    have hB's : GP (B'.A.act (star a)) := B'.A.const (star a)
    have hBa := constantCoeff_mapPt_eq_zero β _ (show GP (B.A.act a) from B.A.const a)
    have hBs := constantCoeff_mapPt_eq_zero β _ (show GP (B.A.act (star a)) from B.A.const (star a))
    have hx0 := gp_comp1 _ _ (constantCoeff_mapPt_eq_zero β _ hB'a) hq0
    have hx1 := gp_comp1 _ _ (constantCoeff_mapPt_eq_zero β _ hB's) hq1
    have hy0 := gp_comp1 _ _ hBa hq0
    have hy1 := gp_comp1 _ _ hBs hq1
    have hw0 := gp_comp1 _ _ hBa (hc _ hq0)
    have hw1 := gp_comp1 _ _ hBs (hc _ hq1)
    have e1 : MvPowerSeries.map β (B.ad a) = _ := hh.ad a
    have e2 : MvPowerSeries.map β (B'.ad a) = _ := hh'.ad a
    rw [ak, ak] at e1
    rw [ak', ak'] at e2
    have e := jeq_map β (J.ad a)
    rw [map_mul, map_mul, map_ev2 β _ _ (hr 0) (gp_comp1 _ _ hB's (hr 1)),
      map_ev2 β _ _ (gp_comp1 _ _ hB'a (hr 0)) (hr 1), map_ev2 β _ _ (hcr _ (hr 0)) (hcr _ (hr 1)),
      mapPt_comp1 β φ _ (hr 0), mapPt_comp1 β φ _ (hr 1), mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1),
      mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hq0 hx1) _ hlam0, gt_ev_expS _ (pair_points_zero_constant hx0 hq1) _ hlam0,
      gt_ev_expS _ hV _ (by simp [cW _ _ hy0 hq1 _ hh0, cW _ _ hq0 hy1 _ hh0]),
      gt_ev_sub _ hV, germEv_germEv_two_points _ hV _ _ hy0 hq1, germEv_germEv_two_points _ hV _ _ hq0 hy1, evP_comp1 _ hV _ _ hq0,
      evP_comp1 _ hV _ _ hq1, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    have e' := jeq_log
      (by simp [cW _ _ hx0 hq1 _ hh0', cW _ _ hq0 hx1 _ hh0']) (cW _ _ hq0 hx1 _ hlam0)
      (by simp [cW _ _ hw0 (hc _ hq1) _ hh0, cW _ _ (hc _ hq0) hw1 _ hh0])
      (cW _ _ hx0 hq1 _ hlam0) e
    rw [ak', ak', ev_diff _ hψ _ _ _ _ _ hx0 hq1, ev_diff _ hψ _ _ _ _ _ hq0 hx1, Ha, Ha]
    refine jeq_of_sub e' ?_
    ring

end GlobalTheory.ChartCmp.GaugeDiff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonicalGaugeDifferenceBiadditiveJetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalGauge_difference_biadditive_jet : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d), JRel m B B' φ φi ε → ∀ (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h h' lam : PS k 2 d), B.IsCanonGauge k h → B'.IsCanonGauge k h' → MvPowerSeries.constantCoeff lam = 0 → FB.expS k lam = FB.toK k ε → Biadd m B' k (h' - ev (n := 2) ![comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 0), comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 1)] h - lam) := by
  first | exact @GlobalTheory.ChartCmp.GaugeDiff.biadd_gauge_diff | exact GlobalTheory.ChartCmp.GaugeDiff.biadd_gauge_diff | (intros; apply GlobalTheory.ChartCmp.GaugeDiff.biadd_gauge_diff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ConstantCoeffInvariantPolyOperatorJetEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ConstantCoeffInvariantPolyOperatorJetEq
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem constantCoeff_DpolyN_jEq : ∀ (k : Type) [CommRing k] (d n : ℕ) (F : Fin d → PS k 2 d) (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (m : ℕ) (f g : PS k n d), P.totalDegree ≤ m → JEq m f g → MvPowerSeries.constantCoeff (DpolyN F cp u P f) = MvPowerSeries.constantCoeff (DpolyN F cp u P g) := by
  intro k _ d n F Ix _ cp u P m f g hP hfg
  classical
  rw [GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq F cp u P f _ subset_rfl,
    GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq F cp u P g _ subset_rfl]
  refine Finset.sum_congr rfl fun e he => ?_
  congr 1
  refine GlobalTheory.PowGerm.NabJet.constantCoeff_DmonN_congr F cp u e f g fun mo hmo => ?_
  refine hfg mo (hmo.trans (le_trans ?_ hP))
  have := MvPolynomial.le_totalDegree he
  rwa [Finsupp.degree_apply]

end GlobalTheory.ChartCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ConstantCoeffInvariantPolyOperatorJetEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_invariantPolyOperator_jetEq : ∀ (k : Type) [CommRing k] (d n : ℕ) (F : Fin d → PS k 2 d) (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (m : ℕ) (f g : PS k n d), P.totalDegree ≤ m → JEq m f g → MvPowerSeries.constantCoeff (DpolyN F cp u P f) = MvPowerSeries.constantCoeff (DpolyN F cp u P g) := by
  first | exact @GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq | exact GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq | (intros; apply GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.InvariantPolyOperatorCopiesTransportedLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.InvariantPolyOperatorCopiesTransportedLaw
set_option autoImplicit false

noncomputable section

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.ChartTrans GlobalTheory.NabCol

namespace GlobalTheory.ChartTransN

variable {k : Type} [CommRing k] {d n : ℕ}

theorem dofN_ev {m : ℕ} (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (V : Fin m → Pt k n d)
    (hV : ∀ j, GP (V j)) (g : PS k m d) :
    DofN F b u (ev V g) = ∑ c : Fin m, ∑ l : Fin d, ev V (pderiv (c, l) g) * DofN F b u (V c l) := by
  unfold DofN
  simp only [pderiv_ev V hV]
  simp only [Finset.mul_sum (s := (Finset.univ : Finset (Fin m))), Finset.mul_sum (f := fun l => ev V _ * _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dofN_inCol_ne (F : Fin d → PS k 2 d) {b c : Fin n} (h : c ≠ b) (u : Fin d → k) (f : PS k 1 d) :
    DofN F b u (inCol c f) = 0 := by
  unfold DofN
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [pderiv_inCol, if_neg h, mul_zero]

theorem dofN_eq_sum (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN F b u g = ∑ l, inCol b (Dof F u (X ((0 : Fin 1), l))) * pderiv (b, l) g := by
  have hX : ∀ l, inCol b (X ((0 : Fin 1), l) : PS k 1 d) = X (b, l) := fun l => gt_ev_X _ (gp b) 0 l
  simp only [← dofN_inCol, hX]
  conv_lhs => unfold DofN
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  unfold DofN
  symm
  rw [Finset.sum_eq_single l]
  · rw [pderiv_X_self, mul_one]
  · intro j _ hj
    rw [pderiv_X_of_ne (fun h => hj (congrArg Prod.snd h).symm), mul_zero]
  · simp

theorem unit_right (G : FGLaw k d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  conv_lhs => rw [← G.comm i]
  rw [gt_ev_ev' _ _ axis_GP (pair_points_zero_constant (gp_pt 1) (gp_pt 0)), eval_pair_points, evP_pt _ axis_GP,
    evP_pt _ axis_GP]
  exact G.unit i

theorem dofN_transF (G : FGLaw k d) (φ φi : Pt k 1 d) (hinv : IsInvPair φ φi) (b : Fin n) (u : Fin d → k)
    (g : PS k n d) :
    DofN (transF G.F φ φi) b u (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
      ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (DofN G.F b ((dLin φ).mulVec u) g) := by
  have hφ : GP φ := hinv.1
  have hΦ : ∀ c : Fin n, GP (comp1 φ (pt k (n := n) d c)) := fun c => gp_comp1 φ _ hφ (gp_pt c)
  have hc : ∀ (c : Fin n) l, comp1 φ (pt k (n := n) d c) l = inCol c (φ l) := fun _ _ => rfl
  have hcol : ∀ f : PS k 1 d, ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (inCol b f) =
      inCol b (ev (n := 1) ![φ] f) := by
    intro f
    unfold inCol
    rw [gt_ev_ev' _ _ hΦ (gp b), gt_ev_ev' _ _ (gp b) (single_point_zero_constant hφ), vec1, vec1, evP_pt _ hΦ]
    rfl
  rw [dofN_ev _ _ _ _ hΦ, dofN_eq_sum G.F, ev_sum _ hΦ, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [gt_ev_mul _ hΦ, hcol, ← dof_transF G.F G.const (unit_right G) φ φi hinv, gt_ev_X _ (single_point_zero_constant hφ), hc,
      dofN_inCol, mul_comm]
    rfl
  · intro c _ hcb
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hc, dofN_inCol_ne _ hcb, mul_zero]
  · simp

theorem dpolyN_transF : ∀ (k : Type) [CommRing k] (d n : ℕ) (G : FGLaw k d) (φ φi : Pt k 1 d), IsInvPair φ φi → ∀ (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (g : PS k n d), DpolyN (transF G.F φ φi) cp u P (ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) g) = ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) (DpolyN G.F cp (fun l => (dLin φ).mulVec (u l)) P g) := by
  intro k _ d n G φ φi hinv Ix _ cp u P g
  have hΦ : ∀ c : Fin n, GP (comp1 φ (pt k (n := n) d c)) := fun c => gp_comp1 φ _ hinv.1 (gp_pt c)
  have hit : ∀ (b : Fin n) (v : Fin d → k) (r : ℕ) (g : PS k n d),
      (DofN (transF G.F φ φi) b v)^[r] (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
        ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) ((DofN G.F b ((dLin φ).mulVec v))^[r] g) := by
    intro b v r
    induction r with
    | zero => intro g; rfl
    | succ r ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dofN_transF G φ φi hinv, ih]
  have hmon : ∀ m : Ix →₀ ℕ,
      DmonN (transF G.F φ φi) cp u m (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
        ev (n := n) (fun c => comp1 φ (pt k (n := n) d c))
          (DmonN G.F cp (fun l => (dLin φ).mulVec (u l)) m g) := by
    intro m
    unfold DmonN
    induction (Finset.univ : Finset Ix).toList with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  unfold DpolyN
  rw [ev_sum _ hΦ]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_C_mul _ hΦ, hmon]

end GlobalTheory.ChartTransN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.InvariantPolyOperatorCopiesTransportedLawStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantPolyOperatorCopies_transportedLaw : ∀ (k : Type) [CommRing k] (d n : ℕ) (G : FGLaw k d) (φ φi : Pt k 1 d), IsInvPair φ φi → ∀ (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (g : PS k n d), DpolyN (transF G.F φ φi) cp u P (ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) g) = ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) (DpolyN G.F cp (fun l => (dLin φ).mulVec (u l)) P g) := by
  first | exact @GlobalTheory.ChartTransN.dpolyN_transF | exact GlobalTheory.ChartTransN.dpolyN_transF | (intros; apply GlobalTheory.ChartTransN.dpolyN_transF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsCanonicalGaugeSubBiadditive
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsCanonicalGaugeSubBiadditive
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.Regauge
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem eq_of_forall_jeq {R σ : Type} [CommRing R] {f g : MvPowerSeries σ R} (h : ∀ m, JEq m f g) : f = g :=
  MvPowerSeries.ext fun e => h e.degree e le_rfl

theorem isCanonGauge_sub : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h g : PS k 2 d), B.IsCanonGauge k h → (∀ m, Biadd m B k g) → B.IsCanonGauge k (h - g) := by
  intro R _ d O _ _ B k _ _ _ h g hc hg
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK k i) = 0 := fun i => by
    simp [FB.FK, FGLaw.mapF, B.G.const]
  have hA : ∀ a, GP (B.actK k a) := fun a i => by simp [FB.actK, B.A.const]
  have gA : ∀ {n : ℕ} (i j : Fin n), GP (addOf (B.FK k) (pt k d i) (pt k d j)) :=
    fun i j => gp_addOf _ hF _ _ (gp_pt i) (gp_pt j)
  have gC : ∀ {n : ℕ} (a : O) (i : Fin n), GP (comp1 (B.actK k a) (pt k d i)) :=
    fun a i => gp_comp1 _ _ (hA a) (gp_pt i)
  have a0 := eq_of_forall_jeq fun m => (hg m).ax0
  have a1 := eq_of_forall_jeq fun m => (hg m).ax1
  have d1 := eq_of_forall_jeq fun m => (hg m).add1
  have d2 := eq_of_forall_jeq fun m => (hg m).add2
  have sy := eq_of_forall_jeq fun m => (hg m).sym
  have bal := fun a => eq_of_forall_jeq fun m => (hg m).bal a
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_sub _ (pair_points_zero_constant gp_zero₂ (gp_pt _)), hc.ax0, a0, sub_zero]
  · rw [gt_ev_sub _ (pair_points_zero_constant (gp_pt _) gp_zero₂), hc.ax1, a1, sub_zero]
  · rw [hc.ph1, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)),
      gt_ev_sub _ (pair_points_zero_constant (gA _ _) (gp_pt _)), d1]
    congr 1; ring
  · rw [hc.ph2, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)),
      gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gA _ _)), d2]
    congr 1; ring
  · rw [hc.sy, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), sy]
    congr 1; ring
  · rw [hc.ad a, gt_ev_sub _ (pair_points_zero_constant (gC _ _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gC _ _)), bal a]
    congr 1; ring

end GlobalTheory.ChartCmp.Regauge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsCanonicalGaugeSubBiadditiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCanonicalGauge_sub_biadditive : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h g : PS k 2 d), B.IsCanonGauge k h → (∀ m, Biadd m B k g) → B.IsCanonGauge k (h - g) := by
  first | exact @GlobalTheory.ChartCmp.Regauge.isCanonGauge_sub | exact GlobalTheory.ChartCmp.Regauge.isCanonGauge_sub | (intros; apply GlobalTheory.ChartCmp.Regauge.isCanonGauge_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValuesEqOfRelatedBiextensions
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartVal

section SlopeTestRemainingChoices
variable {k : Type} [CommRing k] {d : ℕ}

theorem jeq_sum {σ J : Type} {m : ℕ} (s : Finset J) {f g : J → MvPowerSeries σ k} (h : ∀ i, JEq m (f i) (g i)) :
    JEq m (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro e he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => h i e he

theorem jeq_smul {σ : Type} {m : ℕ} (c : k) {f g : MvPowerSeries σ k} (h : JEq m f g) : JEq m (c • f) (c • g) := by
  intro e he
  rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, h e he]

theorem expS_zero [Algebra ℚ k] {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  have hs : PowerSeries.HasSubst (0 : PS k n d) := PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  ext e
  rw [PowerSeries.coeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [hj]

theorem expS_sum [Algebra ℚ k] {n : ℕ} {J : Type} (s : Finset J) (f : J → PS k n d)
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0) : FB.expS k (∑ i ∈ s, f i) = ∏ i ∈ s, FB.expS k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero]
  | insert a s ha ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_insert ha, Finset.prod_insert ha, gt_expS_add _ _ (hf a) (by simp [map_sum, hf]), ih]

theorem expS_natSmul [Algebra ℚ k] {n : ℕ} (q : ℕ) (f : PS k n d)
    (hf : MvPowerSeries.constantCoeff f = 0) : FB.expS k ((q : k) • f) = FB.expS k f ^ q := by
  have h := expS_sum (Finset.range q) (fun _ => f) (fun _ => hf)
  rw [Finset.sum_const, Finset.prod_const, Finset.card_range] at h
  rw [← h, Nat.cast_smul_eq_nsmul]

theorem ev_sum {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) {J : Type} (s : Finset J) (f : J → PS k m d) :
    ev a (∑ i ∈ s, f i) = ∑ i ∈ s, ev a (f i) := by
  unfold ev
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom (gt_hasSubst a ha), map_sum]

theorem ev_smul {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (c : k) (f : PS k m d) :
    ev a (c • f) = c • ev a f := by
  unfold ev
  rw [← MvPowerSeries.coe_substAlgHom (gt_hasSubst a ha), map_smul]

theorem ev_pt_self {n : ℕ} (f : PS k n d) : ev (fun b => pt k (n := n) d b) f = f := by
  change MvPowerSeries.subst (MvPowerSeries.X) f = f
  rw [MvPowerSeries.subst_self]
  rfl

theorem ev_diag {n : ℕ} (a : Pt k 1 d) (x : Pt k n d) (ha : GP a) (hx : GP x) (g : PS k 2 d) :
    ev ![x] (ev (n := 1) ![pt k d 0, comp1 a (pt k d 0)] g) = ev ![x, comp1 a x] g := by
  rw [gt_ev_ev' _ _ (single_point_zero_constant hx) (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ ha (gp_pt 0))), eval_pair_points,
    evP_comp1 _ (single_point_zero_constant hx) _ _ (gp_pt 0), evP_pt _ (single_point_zero_constant hx)]
  rfl

theorem ev_pair {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (a b : Pt k n d) (ha : GP a) (hb : GP b) (h : PS k 2 d) :
    ev ![a, b] (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h) =
      ev ![comp1 φ a, comp1 φ b] h := by
  rw [gt_ev_ev' ![a, b] _ (pair_points_zero_constant ha hb)
      (pair_points_zero_constant (gp_comp1 _ _ hφ (gp_pt 0)) (gp_comp1 _ _ hφ (gp_pt 1))), eval_pair_points,
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 0),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 1), evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
  rfl

theorem jeq_main [Algebra ℚ k] {n : ℕ} (m q : ℕ) (φ φi a : Pt k 1 d) (hinv : IsInvPair φ φi) (ha : GP a)
    (h h' lam : PS k 2 d) (hh : MvPowerSeries.constantCoeff h = 0) (hh' : MvPowerSeries.constantCoeff h' = 0)
    (hl : MvPowerSeries.constantCoeff lam = 0)
    (hj : JEq m h' (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) (f' : PS k n d) :
    JEq m (f' * FB.expS k ((q : k) • ∑ b : Fin n, ev (n := n) ![pt k d b]
        (ev (n := 1) ![pt k d 0, comp1 (comp1 φi (comp1 a φ)) (pt k d 0)] h')))
      (ev (n := n) (fun b => comp1 φ (pt k (n := n) d b))
        (ev (n := n) (fun b => comp1 φi (pt k (n := n) d b))
          (f' * ∏ b : Fin n, (ev ![pt k (n := n) d b, comp1 (comp1 φi (comp1 a φ)) (pt k (n := n) d b)]
            (FB.expS k lam)) ^ q) *
        FB.expS k ((q : k) • ∑ b : Fin n, ev (n := n) ![pt k d b]
          (ev (n := 1) ![pt k d 0, comp1 a (pt k d 0)] h)))) := by
  have hφ : GP φ := hinv.1
  have hφi : GP φi := hinv.2.1
  have ha' : GP (comp1 φi (comp1 a φ)) := gp_comp1 _ _ hφi (gp_comp1 _ _ ha hφ)
  have hp : ∀ b : Fin n, GP (pt k (n := n) d b) := fun b => gp_pt b
  have hΦ : ∀ b : Fin n, GP (comp1 φ (pt k (n := n) d b)) := fun b => gp_comp1 _ _ hφ (hp b)
  have hΦi : ∀ b : Fin n, GP (comp1 φi (pt k (n := n) d b)) := fun b => gp_comp1 _ _ hφi (hp b)
  set a' := comp1 φi (comp1 a φ) with ha'def
  have hL : ∀ b : Fin n, ∀ j, GP (![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] j) :=
    fun b => pair_points_zero_constant (hp b) (gp_comp1 _ _ ha' (hp b))
  have hLa : ∀ b : Fin n, ∀ j, GP (![pt k (n := n) d b, comp1 a (pt k (n := n) d b)] j) :=
    fun b => pair_points_zero_constant (hp b) (gp_comp1 _ _ ha (hp b))
  have hcomp : ∀ g : PS k n d, ev (n := n) (fun b => comp1 φ (pt k (n := n) d b))
      (ev (n := n) (fun b => comp1 φi (pt k (n := n) d b)) g) = g := by
    intro g
    rw [gt_ev_ev' _ _ hΦ hΦi]
    have : (fun j => evP (fun b => comp1 φ (pt k (n := n) d b)) (comp1 φi (pt k (n := n) d j))) =
        fun b => pt k (n := n) d b := by
      funext j
      rw [evP_comp1 _ hΦ _ _ (hp j), evP_pt _ hΦ, gt_comp_inv' hinv _ (hp j)]
    rw [this, ev_pt_self]
  have hφa : ∀ b : Fin n, comp1 φ (comp1 a' (pt k (n := n) d b)) = comp1 a (comp1 φ (pt k (n := n) d b)) := by
    intro b
    rw [ha'def, gt_comp1_comp1 φi _ (gp_comp1 _ φ ha hφ) _ (hp b), gt_comp1_comp1 a φ hφ _ (hp b),
      gt_comp_inv hinv _ (gp_comp1 _ _ ha (hΦ b))]
  have hterm : ∀ b : Fin n, ev (n := n) (fun b => comp1 φ (pt k (n := n) d b))
      (ev ![pt k (n := n) d b, comp1 a (pt k (n := n) d b)] h) =
      ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)]
        (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h) := by
    intro b
    rw [ev_pair φ hφ _ _ (hp b) (gp_comp1 _ _ ha' (hp b)), hφa, gt_ev_ev' _ _ hΦ (hLa b), eval_pair_points,
      evP_comp1 _ hΦ _ _ (hp b), evP_pt _ hΦ]
  set h0 := ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h with h0def
  have hh0 : MvPowerSeries.constantCoeff h0 = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ hφ (gp_pt 0)) (gp_comp1 _ _ hφ (gp_pt 1))) _ hh
  have cS : ∀ (V : Fin n → Fin 2 → Pt k n d), (∀ b j, GP (V b j)) → ∀ g : PS k 2 d,
      MvPowerSeries.constantCoeff g = 0 → MvPowerSeries.constantCoeff (∑ b, ev (V b) g) = 0 := by
    intro V hV g hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => gt_const_ev _ (hV b) _ hg
  have cS' : ∀ (V : Fin n → Fin 2 → Pt k n d), (∀ b j, GP (V b j)) → ∀ g : PS k 2 d,
      MvPowerSeries.constantCoeff g = 0 → MvPowerSeries.constantCoeff ((q : k) • ∑ b, ev (V b) g) = 0 := by
    intro V hV g hg
    rw [MvPowerSeries.constantCoeff_smul, cS V hV g hg, smul_zero]
  simp only [ev_diag _ _ ha' (hp _), ev_diag _ _ ha (hp _)]
  rw [gt_ev_mul _ hΦ, hcomp, gt_ev_expS _ hΦ _ (cS' _ hLa h hh), ev_smul _ hΦ, ev_sum _ hΦ]
  simp only [hterm]
  have hE : ∏ b : Fin n, (ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] (FB.expS k lam)) ^ q =
      FB.expS k ((q : k) • ∑ b : Fin n, ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] lam) := by
    rw [expS_natSmul _ _ (cS _ hL lam hl), expS_sum _ _ (fun b => gt_const_ev _ (hL b) _ hl), Finset.prod_pow]
    congr 1
    exact Finset.prod_congr rfl fun b _ => gt_ev_expS _ (hL b) _ hl
  rw [hE, _root_.mul_assoc, ← gt_expS_add _ _ (cS' _ hL lam hl) (cS' _ hL h0 hh0), ← smul_add, ← Finset.sum_add_distrib]
  refine ((GlobalTheory.T.mvPowerSeriesJetEq_calculus k m).1 _ _ _ _ _ (JEq.refl m f') ?_).2.2
  have hsum : (∑ b : Fin n, (ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] lam +
      ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] h0)) =
      ∑ b : Fin n, ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] (h0 + lam) :=
    Finset.sum_congr rfl fun b _ => by rw [gt_ev_add _ (hL b), add_comm]
  rw [hsum]
  refine ((GlobalTheory.T.jetEq_formalExp_iff_and_exists_log k n d m).1 _ _ (cS' _ hL h' hh') (cS' _ hL _ (by rw [map_add (f := _), hh0, hl, add_zero]))).1 ?_
  exact jeq_smul _ (jeq_sum _ fun b => (GlobalTheory.T.mvPowerSeriesJetEq_calculus k m).2.2.2.1 d 2 n _ _ _ _ (hL b) (hL b)
    (fun _ _ => JEq.refl _ _) hj)

end SlopeTestRemainingChoices


open GlobalTheory.FBMap in
theorem exists_nabValN_eq : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B B' : FB R d O) (φ φi : Pt R 1 d), (∀ m, ∃ ε : PS R 2 d, JRel m B B' φ φi ε) → ∀ h h' : PS k 2 d, B.IsCanonGauge k h → B'.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u u' : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B' a).mulVec (u' l) = σ l.1 a • u' l) → (∀ l, u l = ((dLin φ).map (algebraMap R k)).mulVec (u' l)) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f' : PS R n d), ∃ f : PS R n d, nabValN B k h w0 q (MvPowerSeries.map (algebraMap R k) f) (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B' k h' w0 q (MvPowerSeries.map (algebraMap R k) f') (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u' ⟨ℓ.1, ℓ.2.1⟩) P := by
  intro R _ d O _ _ _ _ _ k _ _ _ B B' φ φi hrel h h' hh hh' T _ r cc isX σ h1 h2 h3 h4 u u' hu' hu n P hP w0 q f'
  open GlobalTheory.FBMap in
    obtain ⟨ε, hε⟩ := hrel (P.totalDegree + 2)
    set m := P.totalDegree + 2 with hm
    have hε1 := (GlobalTheory.T.formalChartJetRel_unit_one_on_axes R d O m B B' φ φi ε hε).1
    obtain ⟨lam, hl0, hle⟩ := (GlobalTheory.T.jetEq_formalExp_iff_and_exists_log k 2 d m).2 (FB.toK k ε) (by simp [FB.toK, hε1])
    have hbi := GlobalTheory.T.canonicalGauge_difference_biadditive_jet R d O m B B' φ φi ε hε k h h' lam hh hh' hl0 hle
    obtain ⟨g', hg', hgg⟩ := GlobalTheory.T.exists_biadditive_series_jetEq_of_biadditiveJet R d O B' k m (by omega) _ hbi
    have hcan := GlobalTheory.T.isCanonicalGauge_sub_biadditive R d O B' k h' g' hh' hg'
    have c0 : ∀ {C : FB R d O} {g : PS k 2 d}, C.IsCanonGauge k g → MvPowerSeries.constantCoeff g = 0 := by
      intro C g hg
      have := congrArg MvPowerSeries.constantCoeff hg.ax0
      rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
    have hφ : NoConst φ := hε.inv.1
    have hφi : NoConst φi := hε.inv.2.1
    have hinv : IsInvPair (mapPt (algebraMap R k) φ) (mapPt (algebraMap R k) φi) := by
      refine ⟨fun i => by simp [mapPt, hφ i], fun i => by simp [mapPt, hφi i], ?_, ?_⟩
      · rw [← mapPt_comp1 _ _ hφi, hε.inv.2.2.1, mapPt_pt]
      · rw [← mapPt_comp1 _ _ hφ, hε.inv.2.2.2, mapPt_pt]
    have hact : B'.actK k w0 = comp1 (mapPt (algebraMap R k) φi) (comp1 (B.actK k w0) (mapPt (algebraMap R k) φ)) := by
      change mapPt (algebraMap R k) (B'.A.act w0) = comp1 _ (comp1 (mapPt (algebraMap R k) (B.A.act w0)) _)
      rw [hε.act w0, mapPt_comp1 _ _ (nc_comp1 (nc_act _ _) hφ), mapPt_comp1 _ _ hφ]
    have hF : B'.FK k = transF (mapLaw (algebraMap R k) B.G).F (mapPt (algebraMap R k) φ) (mapPt (algebraMap R k) φi) := by
      funext i
      change MvPowerSeries.map (algebraMap R k) (B'.G.F i) = _
      rw [hε.law i]
      unfold transF
      rw [map_ev1 _ (nc_addOf (nc_law _) (nc_comp1 hφ (nc_pt _)) (nc_comp1 hφ (nc_pt _))),
        mapPt_addOf _ _ (nc_comp1 hφ (nc_pt _)) (nc_comp1 hφ (nc_pt _)), mapPt_comp1 _ _ (nc_pt _),
        mapPt_comp1 _ _ (nc_pt _), mapPt_pt, mapPt_pt]
      rfl
    have hd : dLin (mapPt (algebraMap R k) φ) = (dLin φ).map (algebraMap R k) := by
      ext i j
      simp [dLin, mapPt]
    have hj : JEq m (h' - g') (ev ![comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 0),
        comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 1)] h + lam) := by
      intro e he
      have := hgg e he
      rw [map_sub, map_sub] at this
      rw [map_sub, map_add (f := _), ← this]
      change _ - (_ - MvPowerSeries.coeff e (ev ![comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 0),
        comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 1)] h) - _) = _
      ring
    have haK : GP (B.actK k w0) := fun i => by simp [FB.actK, B.A.const w0 i]
    have key := jeq_main (n := n) m q _ _ (B.actK k w0) hinv haK h (h' - g') lam (c0 hh) (c0 hcan) hl0 hj
      (MvPowerSeries.map (algebraMap R k) f')
    refine ⟨ev (n := n) (fun b => comp1 φi (pt R (n := n) d b))
      (f' * ∏ b : Fin n, (ev ![pt R (n := n) d b, comp1 (B'.A.act w0) (pt R (n := n) d b)] ε) ^ q), ?_⟩
    rw [GlobalTheory.T.harmonicValueCopies_gauge_independent R d O k B' h' (h' - g') hh' hcan T r cc isX σ h1 h2 h3 h4 u' hu' n P hP w0 q]
    have hmap : MvPowerSeries.map (algebraMap R k) (ev (n := n) (fun b => comp1 φi (pt R (n := n) d b))
        (f' * ∏ b : Fin n, (ev ![pt R (n := n) d b, comp1 (B'.A.act w0) (pt R (n := n) d b)] ε) ^ q)) =
        ev (n := n) (fun b => comp1 (mapPt (algebraMap R k) φi) (pt k (n := n) d b))
          (MvPowerSeries.map (algebraMap R k) f' * ∏ b : Fin n, (ev ![pt k (n := n) d b,
            comp1 (B'.actK k w0) (pt k (n := n) d b)] (FB.expS k lam)) ^ q) := by
      rw [map_ev _ (fun b => nc_comp1 hφi (nc_pt b)), map_mul, map_prod]
      congr 1
      · funext b
        rw [mapPt_comp1 _ _ (nc_pt _), mapPt_pt]
      · congr 1
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [map_pow, map_ev2 _ (nc_pt _) (nc_comp1 (nc_act _ _) (nc_pt _)), mapPt_comp1 _ _ (nc_pt _), mapPt_pt, hle]
        rfl
    unfold nabValN FB.hL
    rw [hmap, hF, hact, GlobalTheory.T.constantCoeff_invariantPolyOperator_jetEq k d n _ _ _ _ P m _ _ (by omega) key,
      GlobalTheory.T.invariantPolyOperatorCopies_transportedLaw k d n (mapLaw (algebraMap R k) B.G) _ _ hinv,
      gt_const_ev_eq _ (fun b => gp_comp1 _ _ hinv.1 (gp_pt b)), hd]
    simp only [hu]
    rfl

end GlobalTheory.ChartVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValuesEqOfRelatedBiextensionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_values_eq_of_related_biextensions : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B B' : FB R d O) (φ φi : Pt R 1 d), (∀ m, ∃ ε : PS R 2 d, JRel m B B' φ φi ε) → ∀ h h' : PS k 2 d, B.IsCanonGauge k h → B'.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u u' : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B' a).mulVec (u' l) = σ l.1 a • u' l) → (∀ l, u l = ((dLin φ).map (algebraMap R k)).mulVec (u' l)) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f' : PS R n d), ∃ f : PS R n d, nabValN B k h w0 q (MvPowerSeries.map (algebraMap R k) f) (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B' k h' w0 q (MvPowerSeries.map (algebraMap R k) f') (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u' ⟨ℓ.1, ℓ.2.1⟩) P := by
  first | exact @GlobalTheory.ChartVal.exists_nabValN_eq | exact GlobalTheory.ChartVal.exists_nabValN_eq | (intros; apply GlobalTheory.ChartVal.exists_nabValN_eq <;> assumption)
end
