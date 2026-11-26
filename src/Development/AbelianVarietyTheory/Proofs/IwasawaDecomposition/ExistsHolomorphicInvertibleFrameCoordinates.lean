module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubset
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Formalism.LocalToGlobal.CarriedPlMap
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AutomorphicArithmetic.CharacterBoxes.ExS
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadFromLocalization
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameSliceComponentUniformisati

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
set_option autoImplicit false

noncomputable section

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam
open GlobalTheory.ArcQ GlobalTheory.FlagBundle Filter Topology

namespace GlobalTheory.FrameLift

open GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {σ : c.F →+* ℂ} {r : ℕ}

theorem nonempty_unfWit {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) : Nonempty (UnfWit U) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hiso, hP⟩ := hU
  choose Pm h1 h2 h3 h4 h5 using hP
  exact ⟨⟨g, e, F, ik, φ, hiso, Pm, h1, h2, fun k x => ⟨h3 k x, h4 k x⟩, h5⟩⟩

theorem exists_transport {p q : CxPts (genStr Z) σ} (h : p = q) (G : EigFrame Z σ (p.1 ≫ genι Z)) :
    ∃ G' : EigFrame Z σ (q.1 ≫ genι Z), (∀ τ i, G'.v τ i = G.v τ i) ∧
      ∀ (M : EigMet Z σ) τ, M.gram q G' τ = M.gram p G τ := by
  subst h
  exact ⟨G, fun _ _ => rfl, fun _ _ => rfl⟩

theorem exists_coords {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) {b₀ : ReciprocityTheory.L2DbarEstimates.V n} (hb₀ : b₀ ∈ B)
    {s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r} (hs : ∀ b ∈ B, s b ∈ (U.X k).dom)
    (hd : DifferentiableOn ℂ s B) (V : (gen Z).affineOpens) {φ : c.F →+* Γ(gen Z, V.1)}
    (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z))
    (hV : ∀ b (hb : b ∈ B), cxPt Z (U.un k ⟨s b, hs b hb⟩) ∈ ptsIn (genStr Z) σ V.1) :
    ∃ N : ReciprocityTheory.L2DbarEstimates.V n → Mat Dw.mult ℂ, (∀ τ a a', DifferentiableOn ℂ (fun b => N b τ a a') B) ∧
      ∀ b (hb : b ∈ B) (y : CxPts (genStr Z) σ), cxPt Z (U.un k ⟨s b, hs b hb⟩) = y →
        ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (G f : EigFrame Z σ (y.1 ≫ genι Z)),
          (∀ τ i, G.v τ i = (cxFrame Z (U.un k ⟨s b, hs b hb⟩)).v τ i) → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v Φ embτ basisIdx) (evHom hy) f →
            ∀ τ, G.co f τ = N b τ := by
  classical
  obtain ⟨W⟩ := nonempty_unfWit hU
  let L := EuclideanSpace.equiv (Fin n) ℂ
  set B₁ : Set (Fin n → ℂ) := L.symm ⁻¹' B with hB₁
  have hB₁o : IsOpen B₁ := hB.preimage L.symm.continuous
  let x : (Fin n → ℂ) → (U.X k).dom := fun v =>
    if h : L.symm v ∈ B then ⟨s (L.symm v), hs _ h⟩ else ⟨s b₀, hs _ hb₀⟩
  have hx : ∀ v ∈ B₁, (x v).1 = s (L.symm v) := fun v hv => by
    simp only [x, dif_pos (show L.symm v ∈ B from hv)]
  have hxL : ∀ b (hb : b ∈ B), x (L b) = ⟨s b, hs b hb⟩ := fun b hb =>
    Subtype.ext ((hx _ (by simpa [hB₁] using hb)).trans (by rw [ContinuousLinearEquiv.symm_apply_apply]))
  have hsd : DifferentiableOn ℂ (fun v => s (L.symm v)) B₁ := hd.comp L.symm.differentiableOn fun v hv => hv
  have hPd : ∀ a, DifferentiableOn ℂ (fun v => W.Pm k (x v) a) B₁ := fun a => differentiableOn_pi.2 fun j =>
    (GlobalTheory.TrueCx.TorHolo.differentiableOn_perFr (U.X k) (x := fun v => s (L.symm v)) (fun v hv => hs _ hv)
      (fun τ a a' => differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hsd τ) a) a') _ _ _).congr
      fun v hv => by rw [W.Pm_eq, hx v hv]
  let p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun v => GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x v))
  have hu : ∀ v, W.F.u (W.ik k) (W.Pm k (x v)) =
      p v ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun v => (W.lie k (x v)).1.symm.trans (ptF_fst (U.un k (x v))).symm
  have hp : ∀ v, p v ≫ pullback.snd _ _ = spMap σ := fun v => ptF_snd (U.un k (x v))
  choose Y hY hYd using fun (a : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) =>
    GlobalTheory.ModelExpCoord.coord_holomorphic _ _ _ _ _ _ _ _ Z σ W.g _ W.F (W.ik k) n B₁ (fun v => W.Pm k (x v)) p hu V
      (Φ.v a.1 a.2) hB₁o (fun v => W.period k (x v)) hPd hp (Φ.tan a.1 a.2)
  refine ⟨fun b τ => of fun a a' => Y ⟨τ, a'⟩ (L b) (W.e.symm ⟨τ, a⟩), fun τ a a' => ?_, fun b hb y hq hy G f hG hf τ => ?_⟩
  · refine differentiableOn_pi.1 ((hY ⟨τ, a'⟩).comp L.differentiableOn fun b hb => ⟨by simpa [hB₁] using hb, ?_⟩) _
    show ⊤ ≤ (cxPt Z (U.un k (x (L b)))).1 ⁻¹ᵁ V.1
    rw [hxL b hb]
    exact hV b hb
  · ext a a'
    obtain ⟨w, hwt, hwm, hwc⟩ := GlobalTheory.HodgeSmooth.exists_lift_comb _ hq G f hG τ a'
    have h1 := hYd ⟨τ, a'⟩ (L b) (by simpa [hB₁] using hb) y hy (by
      show _ = (cxPt Z (U.un k (x (L b)))).1
      rw [hxL b hb, hq])
    have hfv : spMap (dualMap (evHom hy)) ≫ Φ.v τ a' = w ≫ Z.m.φ := by rw [hwm, hf τ a']
    rw [hfv] at h1
    have hbase : w ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p (L b) := by
      show _ = _ ≫ GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x (L b)))
      rw [hxL b hb]
      exact hwt.1
    have h2 := isDerivAt0_ex_of_push Z W.F (p (L b)) (W.ik k) (W.Pm k (x (L b))) (W.period k _) (hu _) hbase h1
    rw [hxL b hb] at h2
    have per := W.period k ⟨s b, hs b hb⟩
    obtain ⟨hPx, hv⟩ := W.lie k ⟨s b, hs b hb⟩
    have h3 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ per _ ((U.un k ⟨s b, hs b hb⟩).u τ) _ (hv τ) _
      _).1 (hPx ▸ hwc)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ per
    have h4 := congrFun ((tn.2.2 _ (tn.1 _ _ h2)).unique h2 h3) (W.e.symm ⟨τ, a⟩)
    have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
    refine Eq.trans ?_ h4.symm
    simp [Finset.sum_apply, Pi.single_apply, hi]

variable {F : Type} [Field F] {X : Var F} {σ' : F →+* ℂ}

theorem eventually_regAt {y : CxPts X.str σ'} {g : X.Fn} (hg : RegAt (under y) g) : ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
  exact regAt_fnOf (mem_ptsIn.1 hz) _ a

theorem eventually_mem {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ'} {A : Mat m X.Fn}
    (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_regAt (mem_O_ratOf.1 ((hP τ).1 i j))).and (eventually_regAt (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem analyticAt_ratVal {d : ℕ} (ch : AlgChart X.str σ' d) {y : CxPts X.str σ'} (hy : y ∈ ch.e.source) {g : X.Fn}
    (hg : RegAt (under y) g) : AnalyticAt ℂ (fun w => ratVal g (ch.e.symm w)) (ch.e y) := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn ((ch.holo W a).congr fun w hw => ratVal_fnOf hw.2 _ a)
    ((GlobalTheory.ChartGlue.isOpen_over ch.e (isOpen_ptsIn W)).mem_nhds ⟨ch.e.map_source hy, ?_⟩)
  show ch.e.symm (ch.e y) ∈ ptsIn X.str σ' W
  rw [ch.e.left_inv hy]
  exact mem_ptsIn.2 hW

end GlobalTheory.FrameLift

end SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

theorem GlobalTheory.FrameLift.exists_holomorphic_frame_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) → (∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w)) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) (c'.e y)) ∧ (∀ τ, IsUnit (K (c'.e y) τ).det) ∧ ∀ᶠ w in 𝓝 (c'.e y), (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm w) g) ∧ ∀ (hs : s w ∈ (U.X k').dom) (g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (c'.e.symm w) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (c'.e.symm w)) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k' ⟨s w, hs⟩)) (cxFrame T.Z (U.un k' ⟨s w, hs⟩)) τ * K w τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ hU X j f₀ Eb A₀ hj hoi hT y _ c' hyc A hA k' s hs hlift
  obtain ⟨V₀, hV₀, φ, Φ, hzV, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β T.Z
    ((cxOf e σ hj y).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen T.Z).affineOpens := ⟨V₀, hV₀⟩
  have hφ' : LogKS.chart V ≫ genStr T.Z = spMap φ := hφ
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr T.Z) σ V.1 := mem_ptsIn.2 hzV
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ' A
  have hpre : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ V.1) ↔ cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 :=
    fun z => mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl)
  have hVn : ∀ᶠ z in 𝓝 y, cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 := by
    filter_upwards [(isOpen_ptsIn _).mem_nhds ((hpre y).2 hyV)] with z hz
    exact (hpre z).1 hz
  have htend : Tendsto c'.e.symm (𝓝 (c'.e y)) (𝓝 y) := c'.e.tendsto_symm hyc
  obtain ⟨B, hBall, hB, hb₀⟩ := eventually_nhds_iff.1 ((hlift.and hs.eventually_analyticAt).and
    (htend.eventually (hVn.and (GlobalTheory.FrameLift.eventually_mem hA))))
  choose hsB hpt using fun b hb => (hBall b hb).1.1
  obtain ⟨N, hN, hNco⟩ := GlobalTheory.FrameLift.exists_coords (Z := T.Z) hU k' hB hb₀ hsB
    (fun b hb => (hBall b hb).1.2.differentiableAt.differentiableWithinAt) V Φ
    (fun b hb => by rw [hpt b hb]; exact (hBall b hb).2.1)
  have key : ∀ b (hb : b ∈ B) (G g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z)),
      (∀ τ i, G.v τ i = (cxFrame T.Z (U.un k' ⟨s b, hsB b hb⟩)).v τ i) → FrameAt e f₀ A₀ A (c'.e.symm b) g →
        ∀ τ, G.co g τ = N b τ * (M τ).map fun r => ratVal r (c'.e.symm b) := by
    intro b hb G g hG hg τ
    obtain ⟨-, hzV, hzS⟩ := hBall b hb
    have hov : σ = (evHom hzV).comp φ := by
      generalize cxOf e σ hj (c'.e.symm b) = z at hzV
      exact GlobalTheory.ShFam.EigLoc.spMap_inj (z.2.symm.trans (by
        rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [← hNco b hb _ (hpt b hb) hzV G f hG hf τ, ← (hM _ hzS hzV).2.2 g hg f hf τ, EigFrame.co_mul]
  have hex : ∀ b ∈ B, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z),
      FrameAt e f₀ A₀ A (c'.e.symm b) g := fun b hb => (hM _ (hBall b hb).2.2 (hBall b hb).2.1).2.1
  refine ⟨fun b τ => N b τ * (M τ).map fun r => ratVal r (c'.e.symm b), fun τ a a' => ?_, fun τ => ?_, ?_⟩
  · simp only [Matrix.mul_apply, Matrix.map_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      (GlobalTheory.SCV.analyticAt_of_differentiableOn (hN τ a i) (hB.mem_nhds hb₀)).mul
        (GlobalTheory.FrameLift.analyticAt_ratVal c' hyc ((hM y hA hyV).1 τ i a'))
  · obtain ⟨g, hg⟩ := hex _ hb₀
    obtain ⟨G, hG, -⟩ := GlobalTheory.FrameLift.exists_transport (hpt _ hb₀) (cxFrame T.Z _)
    show IsUnit (N (c'.e y) τ * (M τ).map fun r => ratVal r (c'.e.symm (c'.e y))).det
    rw [← key _ hb₀ G g hG hg τ]
    exact G.isUnit_det_co g τ
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    refine ⟨hex b hb, fun hsb g hg Me τ => ?_⟩
    obtain ⟨G, hG, hGm⟩ := GlobalTheory.FrameLift.exists_transport (hpt b hb) (cxFrame T.Z _)
    rw [← key b hb G g hG hg τ, ← hGm Me τ]
    exact Me.change _ G g τ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinatesStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_invertible_frame_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) → (∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w)) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) (c'.e y)) ∧ (∀ τ, IsUnit (K (c'.e y) τ).det) ∧ ∀ᶠ w in 𝓝 (c'.e y), (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm w) g) ∧ ∀ (hs : s w ∈ (U.X k').dom) (g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (c'.e.symm w) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (c'.e.symm w)) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k' ⟨s w, hs⟩)) (cxFrame T.Z (U.un k' ⟨s w, hs⟩)) τ * K w τ := by
  first | exact @GlobalTheory.FrameLift.exists_holomorphic_frame_coords | exact GlobalTheory.FrameLift.exists_holomorphic_frame_coords | (intros; apply GlobalTheory.FrameLift.exists_holomorphic_frame_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric

section Subst

variable {n : ℕ}

namespace LinSubst

def rowSel (c : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i => Pi.single (c i) 1

theorem topCoeff_add (P Q : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (P + Q) = topCoeff P + topCoeff Q := by
  simp [topCoeff, MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

theorem topCoeff_C_mul (a : ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) : topCoeff (C a * P) = a * topCoeff P := by
  simp only [topCoeff, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem topCoeff_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, topCoeff (f i) := by
  simp only [topCoeff, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem sum_apply_sum_single {k : ℕ} (f : Fin k → Fin n × Fin n) :
    ∑ x, (∑ i, Finsupp.single (f i) 1 : Fin n × Fin n →₀ ℕ) x = k := by
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply]

theorem prod_X_eq_monomial' {ι : Type} [Fintype ι] (f : ι → Fin n × Fin n) :
    (∏ i, X (f i) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ i, Finsupp.single (f i) 1) 1 := by
  rw [monomial_sum_one]
  rfl

theorem topCoeff_prod_X_of_ne {k : ℕ} (hk : k ≠ n) (f : Fin k → Fin n × Fin n) :
    topCoeff (∏ i, X (f i)) = 0 := by
  rw [topCoeff]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [prod_X_eq_monomial', coeff_monomial, if_neg, mul_zero]
  intro h
  have : ∑ x, (∑ i, Finsupp.single (f i) 1 : Fin n × Fin n →₀ ℕ) x =
      ∑ x, (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x := by rw [h]
  rw [sum_apply_sum_single, sum_apply_sum_single (fun a => (a, w a))] at this
  exact hk this

theorem graph_apply (g : Fin n → Fin n) (x y : Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) (x, y) = if g x = y then 1 else 0 := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

theorem graph_eq_iff (g h : Fin n → Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) = ∑ a, Finsupp.single (a, h a) 1 ↔ g = h := by
  constructor
  · intro e
    funext x
    have := DFunLike.congr_fun e (x, g x)
    rw [graph_apply, graph_apply] at this
    by_contra hne
    rw [if_pos rfl, if_neg (Ne.symm hne)] at this
    exact one_ne_zero this
  · rintro rfl
    rfl

theorem det_rowSel_of_not_injective {c : Fin n → Fin n} (hc : ¬ Function.Injective c) : (rowSel c).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hc
    obtain ⟨i, j, h, h'⟩ := hc
    exact ⟨i, j, h, h'⟩
  exact Matrix.det_zero_of_row_eq hne (by ext k; simp [rowSel, hij])

theorem det_rowSel_perm (σ : Equiv.Perm (Fin n)) : (rowSel σ).det = Equiv.Perm.sign σ := by
  have : rowSel σ = σ.permMatrix ℂ := by
    ext i j
    simp [rowSel, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_permutation]

theorem sum_prod_mul_det_rowSel (U : Matrix (Fin n) (Fin n) ℂ) :
    ∑ c : Fin n → Fin n, (∏ i, U i (c i)) * (rowSel c).det = U.det := by
  have h : (fun i => ∑ a, U i a • (Pi.single a 1 : Fin n → ℂ)) = U := by
    ext i j
    simp [Pi.single_apply]
  conv_rhs => rw [← h]
  change _ = (Matrix.detRowAlternating : AlternatingMap ℂ (Fin n → ℂ) ℂ (Fin n)) _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem topCoeff_prod_X_pair (c d : Fin n → Fin n) :
    topCoeff (∏ i, X (c i, d i)) = (rowSel c).det * (rowSel d).det := by
  rw [topCoeff, prod_X_eq_monomial']
  simp only [coeff_monomial]
  by_cases hc : Function.Injective c
  · have hcb : Function.Bijective c := Finite.injective_iff_bijective.mp hc
    set σ := Equiv.ofBijective c hcb with hσ
    have e : (∑ i, Finsupp.single (c i, d i) 1 : Fin n × Fin n →₀ ℕ) =
        ∑ a, Finsupp.single (a, (d ∘ σ.symm) a) 1 := by
      conv_rhs => rw [← Equiv.sum_comp σ]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [σ]
    simp_rw [e, graph_eq_iff]
    have hcσ : rowSel c = rowSel ⇑σ := rfl
    rw [hcσ, det_rowSel_perm]
    by_cases hd : Function.Injective d
    · set τ := Equiv.ofBijective d (Finite.injective_iff_bijective.mp hd) with hτ
      have hdτ : d ∘ σ.symm = ⇑(σ.symm.trans τ) := by
        ext a
        simp [τ]
      have hdτ' : rowSel d = rowSel ⇑τ := rfl
      rw [hdτ, hdτ', det_rowSel_perm]
      simp only [DFunLike.coe_fn_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp [Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, mul_comm]
    · rw [det_rowSel_of_not_injective hd, mul_zero]
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [if_neg, mul_zero]
      intro h
      apply hd
      have : d = w ∘ σ := by
        rw [← h]
        ext a
        simp
      rw [this]
      exact w.injective.comp σ.injective
  · rw [det_rowSel_of_not_injective hc, zero_mul]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    intro h
    obtain ⟨x, hx⟩ : ∃ x, ∀ i, c i ≠ x := by
      have : ¬ Function.Surjective c := fun hs => hc (Finite.injective_iff_surjective.mpr hs)
      simpa [Function.Surjective] using this
    have h1 := DFunLike.congr_fun h (x, w x)
    rw [graph_apply, if_pos rfl, Finsupp.finsetSum_apply] at h1
    simp [Finsupp.single_apply, hx] at h1

theorem rowSel_mul_apply (c : Fin n → Fin n) (M : Matrix (Fin n) (Fin n) ℂ) (i b : Fin n) :
    (rowSel c * M) i b = M (c i) b := by
  simp [rowSel, Matrix.mul_apply, Pi.single_apply]

theorem exists_prod_X (u : Fin n × Fin n →₀ ℕ) :
    ∃ (k : ℕ) (f : Fin k → Fin n × Fin n), monomial u (1 : ℂ) = ∏ i, X (f i) := by
  induction u using Finsupp.induction with
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | single_add x m u _ _ ih =>
    obtain ⟨k, f, hf⟩ := ih
    refine ⟨m + k, Fin.append (fun _ => x) f, ?_⟩
    rw [Fin.prod_univ_add, monomial_single_add, hf]
    simp [Fin.append_left, Fin.append_right]

theorem topCoeff_subst_prod (J : Matrix (Fin n) (Fin n) ℂ) {k : ℕ} (f : Fin k → Fin n × Fin n) :
    topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
      (∏ i, X (f i) : MvPolynomial (Fin n × Fin n) ℂ)) = J.det * starRingEnd ℂ J.det * topCoeff (∏ i, X (f i)) := by
  rw [map_prod]
  simp only [aeval_X]
  have e : ∀ i, (∑ a, ∑ b, C (J (f i).1 a * starRingEnd ℂ (J (f i).2 b)) * X (a, b) :
      MvPolynomial (Fin n × Fin n) ℂ) =
      ∑ p : Fin n × Fin n, C (J (f i).1 p.1 * starRingEnd ℂ (J (f i).2 p.2)) * X p := fun i =>
    (Fintype.sum_prod_type' (fun a b => C (J (f i).1 a * starRingEnd ℂ (J (f i).2 b)) * X (a, b))).symm
  simp_rw [e]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
  by_cases hk : k = n
  · subst hk
    rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin k) (fun _ => Fin k)).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    simp_rw [topCoeff_prod_X_pair]
    have key : ∀ (c d : Fin k → Fin k),
        (∏ i, J (f i).1 (c i) * starRingEnd ℂ (J (f i).2 (d i))) * ((rowSel c).det * (rowSel d).det) =
        ((∏ i, (rowSel (fun i => (f i).1) * J) i (c i)) * (rowSel c).det) *
        ((∏ i, (rowSel (fun i => (f i).2) * J.map (starRingEnd ℂ)) i (d i)) * (rowSel d).det) := by
      intro c d
      simp only [rowSel_mul_apply, Matrix.map_apply, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => key c d, ← Finset.sum_mul_sum,
      sum_prod_mul_det_rowSel, sum_prod_mul_det_rowSel, Matrix.det_mul, Matrix.det_mul]
    have hc : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := by
      rw [RingHom.map_det]
      rfl
    rw [hc]
    ring
  · simp [topCoeff_prod_X_of_ne hk]

end LinSubst

open LinSubst

theorem topCoeff_subst_conj (J : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) P) =
      J.det * starRingEnd ℂ J.det * topCoeff P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u r =>
    obtain ⟨k, f, hf⟩ := exists_prod_X u
    have e : (monomial u r : MvPolynomial (Fin n × Fin n) ℂ) = C r * ∏ i, X (f i) := by
      rw [← hf, C_mul_monomial, mul_one]
    rw [e, map_mul, aeval_C, algebraMap_eq, topCoeff_C_mul, topCoeff_C_mul, topCoeff_subst_prod]
    ring
  | add p q hp hq =>
    rw [map_add (f := _), topCoeff_add, topCoeff_add, hp, hq, mul_add]

end Subst

end GlobalTheory.GoodMetric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMulStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_linearSubst_eq_absDet_sq_mul : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ), topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) P) = J.det * starRingEnd ℂ J.det * topCoeff P := by
  first | exact @GlobalTheory.GoodMetric.topCoeff_subst_conj | exact GlobalTheory.GoodMetric.topCoeff_subst_conj | (intros; apply GlobalTheory.GoodMetric.topCoeff_subst_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfCellInCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfCellInCone
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.CellFace

theorem exists_face_form : ∀ {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m n : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar ψ γ → IsCell bar ψ γ' → (∀ j, InRCone γ (γ' j)) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (γ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 → InRCone γ' β := by
  intro O _ bar ψ X _ _ _ m n γ γ' hγ hγ' hin
  exact exists_cut_of_cell_le O bar ψ X m n γ γ' hγ hγ' hin

end GlobalTheory.PolFan.CellFace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfCellInConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone : ∀ {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m n : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar ψ γ → IsCell bar ψ γ' → (∀ j, InRCone γ (γ' j)) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (γ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 → InRCone γ' β := by
  first | exact @GlobalTheory.PolFan.CellFace.exists_face_form | exact GlobalTheory.PolFan.CellFace.exists_face_form | (intros; apply GlobalTheory.PolFan.CellFace.exists_face_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreSlotConstructionMonoFewerCoresBothPasses
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.HeightCounting.Up

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

theorem row_mono_id {Bd : GlobalTheory.Fc.BdT} {Q Q₁ : V4.Slot} {Lk Lk₁ : GlobalTheory.Fc.LkT Bd} {H : ∀ 𝒜 : FamClass, GlobalTheory.Fc.RawSel Bd 𝒜 → Prop}
    (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c) (hL : ∀ K β c b, Lk₁ K β c b → Lk K β c b)
    (h : GlobalTheory.Fc.Row Q Lk H) : GlobalTheory.Fc.Row Q₁ Lk₁ H :=
  GlobalTheory.Fc.Row.map (fun _ _ _ b => b) hQ (fun K β c b _ t => hL K β c b t) h

theorem largeBaseProperty_anti {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q₁ R : V4.Slot} (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c)
    (h : GlobalTheory.Fc.LargeBaseCondition KP Q R) : GlobalTheory.Fc.LargeBaseCondition KP Q₁ R :=
  GlobalTheory.Fc.eventuallyAllScaleContexts_mono_of_imp (fun _ H => H.imp fun _ _ _ _ t k C W V S N G c q => t k C W V S N G c (hQ _ _ _ _ _ q)) h

theorem eventually_coreProperty_mono_fewerCores {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q₁ Q' Q'₁ : V4.Slot} {r r₁ : V4.Slot → Prop}
    (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c) (hQ' : ∀ K X f T c, Q'₁ K X f T c → Q' K X f T c)
    (hr : ∀ S S₁ : V4.Slot, (∀ K X f T c, S₁ K X f T c → S K X f T c) → r S → r₁ S₁)
    (h : GlobalTheory.Fc.Lg1 KP Q Q' r) : GlobalTheory.Fc.Lg1 KP Q₁ Q'₁ r₁ := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, largeBaseProperty_anti hQ hR, hr _ _ (fun _ _ _ _ _ t => ⟨hQ' _ _ _ _ _ t.1, t.2⟩) h⟩

end GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

end GlobalTheory.HeightCounting.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperRelAmpleKTrivOfPull
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PolNormal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_generic_pull {S T : Type} [CommRing S] [IsDomain S] [CommRing T] [IsDomain T] (i : S →+* T)
    (hi : Function.Injective i) {t : SAB H (Sp S)} {t' : SAB H (Sp T)} (m : SABMap t' t (spMap i))
    (hg : GlobalTheory.LN.PolAt t (Out.jK S)) : GlobalTheory.LN.PolAt t' (Out.jK T) := by
  let ι : FractionRing S →+* FractionRing T :=
    IsLocalization.map (FractionRing T) i (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i hi)
  refine GlobalTheory.DatUniq.polAt_pull m hg (Out.jK T) (spMap ι) ?_
  simp only [spMap, Out.jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact IsLocalization.map_comp _

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveBalancedFormPrimitiveAmongIntForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveBalancedFormPrimitiveAmongIntForms
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isPrim_eq_one_of_smul_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (β : LinearMap.BilinForm ℤ X) (hβ : β ∈ balForms bar X), IsPrim bar (⟨β, hβ⟩ : balForms bar X) →
  ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  intro O _ bar X _ _ β hβ hp k β' hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exfalso
    have h0 : (⟨β, hβ⟩ : balForms bar X) = 0 := Subtype.ext (by simpa using hk.symm)
    rw [h0] at hp
    exact not_isPrim_zero hp
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hval : ∀ y z, (k : ℤ) * β' y z = β y z := by
    intro y z
    rw [← hk]
    simp
  have hb : β' ∈ balForms bar X := by
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · apply mul_left_cancel₀ hk0
      rw [hval, hval]
      exact hβ.1 y z
    · apply mul_left_cancel₀ hk0
      rw [hval, hval]
      exact hβ.2 a y z
  refine hp k ⟨β', hb⟩ (Subtype.ext ?_)
  simp [← hk]

end GlobalTheory.PolFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveBalancedFormPrimitiveAmongIntFormsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveBalancedForm_primitive_among_intForms : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (β : LinearMap.BilinForm ℤ X) (hβ : β ∈ balForms bar X), IsPrim bar (⟨β, hβ⟩ : balForms bar X) →
  ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  first | exact @GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq | exact GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq | (intros; apply GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntBilinFormDescendAlongSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntBilinFormDescendAlongSurjective
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem exists_bilinForm_descend_of_surjective {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (hf : Function.Surjective f) (β : LinearMap.BilinForm ℤ X)
    (h1 : ∀ x, f x = 0 → ∀ y, β x y = 0) (h2 : ∀ x, f x = 0 → ∀ y, β y x = 0) :
    ∃ ζ : LinearMap.BilinForm ℤ Y, ∀ x y, ζ (f x) (f y) = β x y := by
  classical
  set g := Function.surjInv hf with hgdef
  have hg : ∀ y, f (g y) = y := Function.surjInv_eq hf
  have key1 : ∀ a b, f a = f b → ∀ y, β a y = β b y := by
    intro a b h y
    have hk : f (a - b) = 0 := by rw [map_sub, h, sub_self]
    have := h1 (a - b) hk y
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have key2 : ∀ a b, f a = f b → ∀ y, β y a = β y b := by
    intro a b h y
    have hk : f (a - b) = 0 := by rw [map_sub, h, sub_self]
    have := h2 (a - b) hk y
    rw [map_sub, sub_eq_zero] at this
    exact this
  refine ⟨LinearMap.mk₂ ℤ (fun y y' => β (g y) (g y')) ?_ ?_ ?_ ?_, ?_⟩
  · intro y1 y2 y'
    rw [key1 (g (y1 + y2)) (g y1 + g y2) (by rw [map_add (f := _), hg, hg, hg]), map_add (f := _),
      LinearMap.add_apply]
  · intro c y y'
    rw [key1 (g (c • y)) (c • g y) (by rw [map_zsmul, hg, hg]), map_smul, LinearMap.smul_apply]
  · intro y y1 y2
    rw [key2 (g (y1 + y2)) (g y1 + g y2) (by rw [map_add (f := _), hg, hg, hg]), map_add (f := _)]
  · intro c y y'
    rw [key2 (g (c • y')) (c • g y') (by rw [map_zsmul, hg, hg]), map_smul]
  · intro x y
    rw [LinearMap.mk₂_apply, key1 (g (f x)) x (hg _), key2 (g (f y)) y (hg _)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntBilinFormDescendAlongSurjectiveStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intBilinForm_descend_along_surjective : ∀ {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (f : X →+ Y), Function.Surjective f → ∀ β : LinearMap.BilinForm ℤ X,
  (∀ x, f x = 0 → ∀ y, β x y = 0) → (∀ x, f x = 0 → ∀ y, β y x = 0) →
  ∃ ζ : LinearMap.BilinForm ℤ Y, ∀ x y, ζ (f x) (f y) = β x y := by
  first | exact @GlobalTheory.exists_bilinForm_descend_of_surjective | exact GlobalTheory.exists_bilinForm_descend_of_surjective | (intros; apply GlobalTheory.exists_bilinForm_descend_of_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfLinearPieceThroughCellPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfLinearPieceThroughCellPoint
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

theorem inRCone_of_interior_linearOn {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m k : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X) (hγ : IsCell bar φ γ)
    (hmem : ∀ i, γ' i ∈ balForms bar X) (hpos : ∀ i y, 0 ≤ γ' i y y) (hlin : φ.LinearOn γ')
    (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ i, 0 < b i)
    (e1 : toReal β = ∑ j, a j • toReal (γ j)) (e2 : toReal β = ∑ i, b i • toReal (γ' i)) (i : Fin k) :
    InRCone γ (γ' i) := by
  have hev : ∀ {p : ℕ} (δ : Fin p → LinearMap.BilinForm ℤ X) (c : Fin p → ℝ), (∀ j, 0 ≤ c j) → φ.LinearOn δ →
      toReal β = ∑ j, c j • toReal (δ j) → φ.evalZ β = ∑ j, c j * φ.evalZ (δ j) := by
    intro p δ c hc hl e
    rw [← hl c hc]
    unfold InvFun.evalZ
    congr 1
    funext x y
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ e x y
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have ea := hev γ a ha hγ.linear e1
  have eb := hev γ' b (fun i => (hb i).le) hlin e2
  have la := apply_eq_of_toReal_eq e1 ℓ
  have lb := apply_eq_of_toReal_eq e2 ℓ
  have hsum : ∑ i, b i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← lb, sub_eq_zero, la]
    have e3 : ∑ i, b i * ((N : ℝ) * φ.evalZ (γ' i)) = N * φ.evalZ β := by
      rw [eb, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e3, ea, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [h1 j]; ring
  have hnn : ∀ i, 0 ≤ b i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) := fun i =>
    mul_nonneg (hb i).le (sub_nonneg.2 (h2 _ (hmem i) (hpos i)))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hsum i (Finset.mem_univ _)
  have heq : (N : ℝ) * φ.evalZ (γ' i) = ℓ (γ' i) := by
    have := (mul_eq_zero.1 hz).resolve_left (hb i).ne'
    linarith
  obtain ⟨kk, c, hk, hc⟩ := h3 _ (hmem i) (hpos i) heq
  have hkR : (kk : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun j => (c j : ℝ) / kk, fun j => by positivity, LinearMap.ext₂ fun x y => ?_⟩
  have h4 := LinearMap.congr_fun₂ hc x y
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h4
  have h5 : (kk : ℝ) * (γ' i x y : ℝ) = ∑ j, (c j : ℝ) * (γ j x y : ℝ) := by exact_mod_cast h4
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have h6 : (γ' i x y : ℝ) = (∑ j, (c j : ℝ) * (γ j x y : ℝ)) / kk := by
    rw [eq_div_iff hkR, ← h5]; ring
  rw [h6, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem inRCone_of_interior_linearOn' : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m k : ℕ}
  (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X), IsCell bar φ γ → (∀ i, γ' i ∈ balForms bar X) →
  (∀ i y, 0 ≤ γ' i y y) → φ.LinearOn γ' →
  ∀ (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ), (∀ j, 0 ≤ a j) → (∀ i, 0 < b i) →
    toReal β = ∑ j, a j • toReal (γ j) → toReal β = ∑ i, b i • toReal (γ' i) → ∀ i, InRCone γ (γ' i) := by
  intro O _ bar φ X _ _ _ m k γ γ' hγ hmem hpos hlin β a b ha hb e1 e2 i
  exact inRCone_of_interior_linearOn bar φ γ γ' hγ hmem hpos hlin β a b ha hb e1 e2 i

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfLinearPieceThroughCellPointStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_cell_of_linearPiece_through_cellPoint : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m k : ℕ}
  (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X), IsCell bar φ γ → (∀ i, γ' i ∈ balForms bar X) →
  (∀ i y, 0 ≤ γ' i y y) → φ.LinearOn γ' →
  ∀ (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ), (∀ j, 0 ≤ a j) → (∀ i, 0 < b i) →
    toReal β = ∑ j, a j • toReal (γ j) → toReal β = ∑ i, b i • toReal (γ' i) → ∀ i, InRCone γ (γ' i) := by
  first | exact @GlobalTheory.PolFan.inRCone_of_interior_linearOn' | exact GlobalTheory.PolFan.inRCone_of_interior_linearOn' | (intros; apply GlobalTheory.PolFan.inRCone_of_interior_linearOn' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHoloFrameChart
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.LieBase.HoloFrame

theorem exists_un : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ (y : CxPts (genStr T.Z) σ), ¬ LiesIn y (genBd T.Z) → ∃ (k : U.Comp) (x : (U.X k).dom), cxPt T.Z (U.un k x) = y := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ r U hU y hy
  have hr : Set.range y.1 ⊆ Set.range T.Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    exact not_not.1 hy
  haveI := T.Z.jQ_open
  let xF := IsOpenImmersion.lift T.Z.jQ y.1 hr
  have hxF : xF ≫ T.Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hs : xF ≫ Limits.pullback.snd _ _ = spMap (algebraMap c.F (CAt σ)) := by
    have h2 := y.2
    rw [← hxF, Category.assoc, T.Z.jQ_over] at h2
    exact h2
  have hover : (xF ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs]
    exact GlobalTheory.ShFam.OpenReg.spMap_comp _ _
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨z, hz⟩ : ∃ z : FrPt Xo c (CAt σ), z.x = xF ≫ Limits.pullback.fst _ _ :=
    GlobalTheory.FlagTan.exists_frPt _ hover
  obtain ⟨k, f, t, hb⟩ := hU.2.2.1 z
  refine ⟨k, f, ?_⟩
  rw [cxPt_congr hb.1.symm]
  refine Subtype.ext ?_
  show GlobalTheory.AllWt.ptF (S := CAt σ) z ≫ T.Z.jQ = y.1
  rw [← hxF]
  congr 1
  apply Limits.pullback.hom_ext
  · exact (ptF_fst z).trans hz
  · exact (ptF_snd z).trans hs.symm

theorem exists_holo_frame_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k : U.Comp) (Fr : V X.dim → Frame (U.X k).Ψ (Dw.p + Dw.q)), ∀ᶠ u in 𝓝 (c'.e y), ∃ h : Fr u ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨Fr u, h⟩) = cxOf e σ hj (c'.e.symm u) ∧ ∀ τ' a b, DifferentiableAt ℂ (fun u => mat (Fr u) τ' a b) u := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU X j hjo hj y hy c' hyc
  have hnb : ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
    intro h
    have h1 : IsLocalRing.closedPoint ℂ ∈ y.1 ⁻¹ᵁ openPart j := hy (Set.mem_univ _)
    exact h1 h
  obtain ⟨k, x₀, hx₀⟩ := exists_un E H Dw l Xo c O β Y T σ _ U hU _ hnb
  have hn := GlobalTheory.T.dim_openly_immersed_variety_eq_cmType_card_mul_pq E H Dw l Xo c O β Y T F e σ U hσ hU X j hjo hj ⟨y, hy⟩ k
  obtain ⟨W, a, ψ, hWo, haW, hψd, hψh, hψa, hinj⟩ := GlobalTheory.T.exists_holomorphic_frame_slice_componentUniformisation E H Dw l Xo c σ U hσ hU k x₀ X.dim hn
  obtain ⟨q, hOo, hq, hqd⟩ := GlobalTheory.T.holomorphic_frameFamily_chart_coordinates_holomorphic E H Dw l Xo c O β Y T F e σ U hσ hU X j hjo hj c' k X.dim W ψ hWo hψd hψh
  haveI := T.Z.jQ_open
  have hxeq : ∀ {z z' : FrPt Xo c (CAt σ)}, cxPt T.Z z = cxPt T.Z z' → z.x = z'.x := by
    intro z z' h
    have h1 : GlobalTheory.AllWt.ptF (S := CAt σ) z = GlobalTheory.AllWt.ptF (S := CAt σ) z' :=
      (cancel_mono T.Z.jQ).1 (congrArg Subtype.val h)
    rw [← ptF_fst z, h1, ptF_fst]
  have hcxinj : Function.Injective (cxOf e σ hj) := by
    intro y1 y2 h
    apply Subtype.ext
    exact (cancel_mono j).1 (congrArg Subtype.val h)
  have hya : cxOf e σ hj y = cxPt T.Z (U.un k ⟨ψ a, hψd a haW⟩) := hx₀.symm.trans (cxPt_congr (hψa _).symm)
  have haO : a ∈ {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := ⟨haW, hψd a haW, y, hyc, hya⟩
  have hqa : q a = y := hcxinj ((hq a haW _ ⟨y, hyc, hya⟩).2.trans hya.symm)
  have hinjg : Set.InjOn (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
    rintro w ⟨hw, hwd, hw'⟩ w' ⟨hw2, hwd', hw2'⟩ hg
    have h1 := hq w hw hwd hw'
    have h2 := hq w' hw2 hwd' hw2'
    have hqq : q w = q w' := c'.e.injOn h1.1 h2.1 hg
    refine hinj w hw w' hw2 hwd hwd' (hxeq ?_)
    rw [← h1.2, ← h2.2, hqq]
  obtain ⟨h, hev⟩ := GlobalTheory.T.exists_holomorphic_local_inverse_of_injOn X.dim _ _ a hOo haO hqd hinjg
  refine ⟨k, fun u => ψ (h u), ?_⟩
  rw [show c'.e y = c'.e (q a) by rw [hqa]]
  filter_upwards [hev] with u ⟨⟨huW, hud, hux⟩, hgu, hdu⟩
  refine ⟨hψd _ huW, ?_, fun τ' i i' => ?_⟩
  · have h1 := hq _ huW (hψd _ huW) hux
    rw [← h1.2]
    congr 1
    exact (c'.e.left_inv h1.1).symm.trans (congrArg c'.e.symm hgu)
  · exact ((hψh τ' i i' _ huW).differentiableAt (hWo.mem_nhds huW)).comp u hdu

end GlobalTheory.LieBase.HoloFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersAutCommHostConjugation
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersAutCommHostConjugation
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem ringOfIntegers_equiv_bar_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E), τ (H.bar a) = H.bar (τ a) := by
  intro E _ _ _ H τ a
  have hM : (nonZeroDivisors (𝓞 E)).map (τ : 𝓞 E →* 𝓞 E) = nonZeroDivisors (𝓞 E) := by
    exact MulEquivClass.map_nonZeroDivisors τ
  let τE : E ≃+* E := IsLocalization.ringEquivOfRingEquiv E E τ hM
  have hτE : ∀ x : 𝓞 E, τE (x : E) = ((τ x : 𝓞 E) : E) := by
    intro x
    exact IsLocalization.ringEquivOfRingEquiv_eq hM x
  obtain ⟨ψ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply RingOfIntegers.ext
  rw [← hτE, H.bar_eq, H.bar_eq, ← hτE]
  apply ψ.injective
  have h1 := IsCMField.complexEmbedding_complexConj E (ψ.comp (τE : E →+* E)) (a : E)
  have h2 := IsCMField.complexEmbedding_complexConj E ψ (τE (a : E))
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1
  rw [h1, h2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersAutCommHostConjugationStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOfIntegers_aut_comm_hostConjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E), τ (H.bar a) = H.bar (τ a) := by
  first | exact @GlobalTheory.ringOfIntegers_equiv_bar_comm | exact GlobalTheory.ringOfIntegers_equiv_bar_comm | (intros; apply GlobalTheory.ringOfIntegers_equiv_bar_comm <;> assumption)
end
end
