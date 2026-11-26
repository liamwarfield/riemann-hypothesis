module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntForm
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiesBOfExplicit
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.BasicNotions.TH Formalism.L2.GlobalTheoryTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.PrimIn.AtData


set_option maxHeartbeats 1000000 in
theorem ev_params : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0) →
    ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ SizesAt L ∧ Nonempty (ParameterChoice' X.toD7 L) ∧
      8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  exact ⟨L, e1, M.sizes, ⟨M.params⟩, M.parT.nV_ge⟩

end GlobalTheory.PrimIn.AtData

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2
open Formalism.MainNotions.Inhab Formalism.BasicNotions.TH Formalism.L2.GlobalTheoryTheory IsDedekindDomain NumberField GlobalTheory.EX GlobalTheory.EX.OB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Up.SizePar

end GlobalTheory.HeightCounting.Up.SizePar

namespace GlobalTheory.HeightCounting.Up.SizePar


set_option maxHeartbeats 2000000 in
theorem ev_params_withLoc : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0) →
    (∃ L : SizeData₂ X.toD7, Nonempty (ParameterChoice' X.toD7 L)) ∧
      ∀ Lc : LocAll (lay0 X.toD7), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := GlobalTheory.EX.szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  have hGam : ∀ u, Real.log (D.mem u).A.GamP = K.C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * K.s.L := fun u => by
    have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
    rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl
  refine ⟨?_, fun Lc => ?_⟩
  · obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
      (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta hGam
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
    obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
      ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
    exact ⟨L, ⟨M.params⟩⟩
  · obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s (withLoc Lc) (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx)
      hP.rank hP.val (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta hGam
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
    obtain ⟨⟨M⟩, -, -⟩ := hN (withLoc Lc) L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
      ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
    exact ⟨L, ⟨M.params⟩⟩

end GlobalTheory.HeightCounting.Up.SizePar

namespace GlobalTheory.HeightCounting.Up.SizePar

theorem stepW_start_ev {Q : Ctx → Prop} (h : Ev Q) : StepW Start fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)

theorem aj_zero_at_state : StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P),
    ∀ v, (Dof x).what₂.muAt v = (Dof x).what₂.mu0 → ∀ j, 1 ≤ j → j ≤ (Dof x).R.m → (Dof x).what₂.Aj j v = 0 := by
  refine StepW.of_all fun K B f T w hO hF hS P x v hv j h1 h2 => ?_
  have hex : P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) := by
    have e1 := x.m.W1 (F0K K.s (w.D x.o.Z))
    refine Eq.trans ?_ e1.symm
    refine P.exact.trans ?_
    rw [GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices K B f T w P.Z₀ x.o.Z P.kap (P.q.kap x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G)]
  have H := GlobalTheory.T.indices_pairingLengths_vanish_off_twistedPlaces K B f T w hO hF ⟨hS.1, ⟨P⟩⟩ P x hex
  have key : ∀ v', (w.D x.o.Z).what₂.muAt v' = (w.D x.o.Z).what₂.mu0 → v' ∉ P.Wt := by
    intro v' he hw
    have he' : P.q.W₀.muAt v' = w.C.mu0 := he
    rw [P.q.mu.on v' hw] at he'
    have e2 := P.q.mu.tw v'
    rw [he'] at e2
    exact (TwFin.tw_fin B f T).2.1 v' (e2.symm.trans (show w.I.xi w.C.mu0 = 1 from w.l.xi0))
  change (w.D x.o.Z).what₂.Aj j v = 0
  replace hv : (w.D x.o.Z).what₂.muAt v = (w.D x.o.Z).what₂.mu0 := hv
  have a := H v (key v hv) j h1 h2
  have b := H _ (key _ (((w.D x.o.Z).what₂.muAt_conj v).trans hv)) j h1 h2
  unfold Formalism.BasicNotions.Rows.Data.Aj
  rw [hv, a.1, a.2, b.1]
  rfl

theorem exists_params_allSt : AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧
    ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) :=
  ((stepW_start_ev ev_params_withLoc).and aj_zero_at_state).trans
    (StepW.of_all fun _ _ _ _ w hO _ H P x => H.1 (w.st x.o.Z) hO x.etaF (H.2 P x))

end GlobalTheory.HeightCounting.Up.SizePar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

noncomputable section
namespace GlobalTheory.ChernPull

open ReciprocityTheory.L2DbarEstimates (V)
open ComplexConjugate

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem conn_eq_sum (H : V n → Matrix r r ℂ) (z ζ : V n) :
    conn H z ζ = ∑ c, ζ c • conn H z (coordVec c) := by
  have hζ : ζ = ∑ c, ζ c • coordVec (n := n) c := by
    ext i; simp [coordVec, Pi.single_apply]
  conv_lhs => rw [hζ]
  have hl : ∀ (s : Finset (Fin n)), mdel H z (∑ c ∈ s, ζ c • coordVec c) = ∑ c ∈ s, ζ c • mdel H z (coordVec c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext a b; simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mdel_add_vec, mdel_smul_vec, ih]
  simp only [conn, hl, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_sum, Matrix.mul_smul]

theorem curv_eq_sum (H : V n → Matrix r r ℂ) (z ξ ζ : V n) :
    curv H z ξ ζ = ∑ d, conj (ζ d) • curv H z ξ (coordVec d) := by
  have hζ : ζ = ∑ d, ζ d • coordVec (n := n) d := by
    ext i; simp [coordVec, Pi.single_apply]
  conv_lhs => rw [hζ]
  have hl : ∀ (s : Finset (Fin n)), mdbar (fun x => conn H x ξ) z (∑ d ∈ s, ζ d • coordVec d) =
      ∑ d ∈ s, conj (ζ d) • mdbar (fun x => conn H x ξ) z (coordVec d) := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext a b; simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mdbar_add_vec, mdbar_smul_vec, ih]
  simp only [curv, hl, Finset.sum_neg_distrib, smul_neg]

theorem mContDiffAt_conn {H : V n → Matrix r r ℂ} {y : V n} (h2 : MContDiffAt 2 H y)
    (hu : IsUnit (H y).det) (ξ : V n) : MContDiffAt 1 (fun x => conn H x ξ) y := by
  have h1 : MContDiffAt 1 H y := h2.of_le (by norm_num)
  have hu' : IsUnit ((H y)ᵀ).det := by rwa [Matrix.det_transpose]
  exact (h1.transpose.inv hu').mul ((h2.mdel (j := 1) (by norm_num) ξ).transpose)

theorem conn_comp_eventually {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (ξ : V n) :
    ∀ᶠ w in 𝓝 v, conn (fun x => H (φ x)) w ξ = ∑ c, (fderiv ℂ φ w ξ) c • conn H (φ w) (coordVec c) := by
  have hK : ∀ᶠ w in 𝓝 v, MContDiffAt 2 H (φ w) := hφ.continuousAt.eventually h2.eventually_two
  filter_upwards [hK, hφ.eventually_analyticAt] with w hw ha
  rw [← conn_eq_sum]
  have hm : mdel (fun x => H (φ x)) w ξ = mdel H (φ w) (fderiv ℂ φ w ξ) := by
    ext a b
    exact del_comp_holo (u := fun y => H y a b) ((hw a b).differentiableAt (by norm_num))
      ha.differentiableAt ξ
  simp only [conn, hm]

theorem curv_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (ξ η : V n) :
    curv (fun x => H (φ x)) v ξ η = ∑ c, (fderiv ℂ φ v ξ) c • curv H (φ v) (coordVec c) (fderiv ℂ φ v η) := by
  rw [curv, mdbar_congr (conn_comp_eventually hφ h2 ξ)]
  have hd : DifferentiableAt ℂ φ v := hφ.differentiableAt
  have hf : ∀ c : Fin n, DifferentiableAt ℂ (fun x => (fderiv ℂ φ x ξ) c) v := by
    intro c
    have h1 : DifferentiableAt ℂ (fun x => fderiv ℂ φ x ξ) v :=
      hφ.fderiv.differentiableAt.clm_apply (differentiableAt_const ξ)
    exact (EuclideanSpace.proj (𝕜 := ℂ) c).differentiableAt.comp v h1
  have hc : ∀ (c : Fin n) (i j : r), DifferentiableAt ℝ (fun y => conn H y (coordVec c) i j) (φ v) :=
    fun c i j => (mContDiffAt_conn h2 hu (coordVec c)).diff i j
  ext i j
  simp only [Matrix.neg_apply, mdbar_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_neg_distrib]
  rw [dbar_sum (A := fun c x => (fderiv ℂ φ x ξ) c * conn H (φ x) (coordVec c) i j) (fun c _ => ((hf c).restrictScalars ℝ).mul
    ((hc c i j).comp v (hd.restrictScalars ℝ)))]
  rw [ContinuousLinearMap.sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dbar_mul (a := fun x => (fderiv ℂ φ x ξ) c) (b := fun x => conn H (φ x) (coordVec c) i j) ((hf c).restrictScalars ℝ) ((hc c i j).comp v (hd.restrictScalars ℝ)),
    dbar_eq_zero (hf c), dbar_comp_holo (u := fun y => conn H y (coordVec c) i j) (hc c i j) hd]
  simp [curv]

def substAlg (J : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  aeval fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)

def jac (φ : V n → V n) (v : V n) : Matrix (Fin n) (Fin n) ℂ := fun c a => (fderiv ℂ φ v (coordVec a)) c

theorem curv_comp_coord {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (a b : Fin n) :
    curv (fun x => H (φ x)) v (coordVec a) (coordVec b) =
      ∑ c, ∑ d, (jac φ v c a * conj (jac φ v d b)) • curv H (φ v) (coordVec c) (coordVec d) := by
  rw [curv_comp hφ h2 hu]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [curv_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_smul]; rfl

theorem curvPoly_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) :
    curvPoly (fun x => H (φ x)) v = (curvPoly H (φ v)).map (substAlg (jac φ v)) := by
  refine Matrix.ext fun i j => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [curvPoly, Matrix.of_apply, Matrix.map_apply, curv_comp_coord hφ h2 hu, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, substAlg, aeval_X, aeval_C, algebraMap_eq,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [← Fintype.sum_prod_type']
  let e : Fin n × Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n × Fin n :=
    ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun _ => rfl, fun _ => rfl⟩
  exact Fintype.sum_equiv e _ _ fun x => by simp only [e, Equiv.coe_fn_mk]; ring

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {d : Type} [Fintype d]
    [DecidableEq d] (M : Matrix d d A) :
    (Matrix.charpolyRev M).map f = Matrix.charpolyRev (M.map f) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 1
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem chernPoly_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (k : ℕ) :
    chernPoly (fun x => H (φ x)) v k = substAlg (jac φ v) (chernPoly H (φ v) k) := by
  unfold chernPoly
  rw [curvPoly_comp hφ h2 hu]
  have hm : -(curvPoly H (φ v)).map (substAlg (jac φ v)) = (-curvPoly H (φ v)).map (substAlg (jac φ v)).toRingHom := by
    rw [Matrix.map_neg (f := (substAlg (jac φ v)).toRingHom) (fun a => map_neg _ a)]; rfl
  rw [hm, ← charpolyRev_map, Polynomial.coeff_map]
  rfl

theorem jac_eq_toMatrix (φ : V n → V n) (v : V n) :
    jac φ v = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (fderiv ℂ φ v : V n →ₗ[ℂ] V n) := by
  ext c a
  simp [LinearMap.toMatrix_apply, jac, coordVec]

end GlobalTheory.ChernPull


open ReciprocityTheory.L2DbarEstimates (V) in
theorem GlobalTheory.ChernPull.chernTop_comp : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (K : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n) (v : ReciprocityTheory.L2DbarEstimates.V n), AnalyticAt ℂ φ v → (∀ τ, MContDiffAt 2 (fun u => K u τ) (φ v)) → (∀ τ, IsUnit (K (φ v) τ).det) → chernTop R (fun w => K (φ w)) v = Complex.normSq (LinearMap.det (fderiv ℂ φ v : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n)) * chernTop R K (φ v) := by
  intro n ι m R K φ v hφ h2 hu
  unfold chernTop
  have hc : ∀ x : ι × ℕ, chernPoly (fun u => K (φ u) x.1) v x.2 =
      GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v) (chernPoly (fun u => K u x.1) (φ v) x.2) :=
    fun x => GlobalTheory.ChernPull.chernPoly_comp hφ (h2 x.1) (hu x.1) x.2
  simp only [hc]
  have ha := congrArg (fun F => F R) (MvPolynomial.comp_aeval (R := ℝ)
    (f := fun x : ι × ℕ => chernPoly (fun u => K u x.1) (φ v) x.2)
    ((GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v)).restrictScalars ℝ))
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at ha
  rw [← ha, GlobalTheory.ChernPull.substAlg, GlobalTheory.T.topDegreeFormCoeff_linearSubst_eq_absDet_sq_mul, Complex.mul_conj, GlobalTheory.ChernPull.jac_eq_toMatrix,
    LinearMap.det_toMatrix, Complex.re_ofReal_mul]
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDetStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_comp_holomorphic_normSq_det : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (K : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n) (v : ReciprocityTheory.L2DbarEstimates.V n), AnalyticAt ℂ φ v → (∀ τ, MContDiffAt 2 (fun u => K u τ) (φ v)) → (∀ τ, IsUnit (K (φ v) τ).det) → chernTop R (fun w => K (φ w)) v = Complex.normSq (LinearMap.det (fderiv ℂ φ v : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n)) * chernTop R K (φ v) := by
  first | exact @GlobalTheory.ChernPull.chernTop_comp | exact GlobalTheory.ChernPull.chernTop_comp | (intros; apply GlobalTheory.ChernPull.chernTop_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocSAlt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocS
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLocalRows

open Formalism.IndefR.principalLevelFrame

theorem fixed_fd_of_isotIn {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A)
    (hadm : ∀ N : ℕ, 0 < N →
      FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, NG.Cong D.host.E n N κ → ρ κ x = x}))
    (π : NG.FinTyp D.host.E n) (hne : isotIn (D := D) ρ C π ≠ ⊥) (N : ℕ) (hN : 0 < N) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E n N κ → NG.rt D.host.E n κ f = f}) := by
  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : π.S →ₗ[ℂ] A,
      (IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold isotIn
    exact iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ (GAf D.host.E n → ℂ) := (LinearMap.ker Φ).map π.S.subtype
    have hS'le : S' ≤ π.S := by
      rintro f ⟨k, _, rfl⟩
      exact k.2
    have hS'st : ∀ h, ∀ f ∈ S', NG.rt D.host.E n h f ∈ S' := by
      rintro h f ⟨k, hk, rfl⟩
      refine ⟨⟨NG.rt D.host.E n h k, π.stable h k k.2⟩, ?_, rfl⟩
      show Φ _ = 0
      rw [hΦe h k, LinearMap.mem_ker.1 hk, map_zero]
    rcases π.irr S' hS'le hS'st with h0 | hall
    · rw [eq_bot_iff]
      intro k hk
      have : (k : GAf D.host.E n → ℂ) ∈ S' := ⟨k, hk, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E n → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      rw [show y = k from Subtype.ext hky.symm]
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 hk)
  set F := Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E n N κ → NG.rt D.host.E n κ f = f} with hF
  set T := Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, NG.Cong D.host.E n N κ → ρ κ x = x} with hT
  have := hadm N hN
  have hFS : F ≤ π.S := Submodule.span_le.2 fun f hf => hf.1
  have hFT : ∀ f (hf : f ∈ F), Φ ⟨f, hFS hf⟩ ∈ T := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨hΦC ⟨_, rfl⟩, fun κ hκ => ?_⟩
      rw [← hΦe κ]
      congr 1
      exact Subtype.ext (hx.2 κ hκ)
    | zero =>
      have : (⟨0, hFS F.zero_mem⟩ : π.S) = 0 := rfl
      rw [this, map_zero]
      exact T.zero_mem
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hFS (F.add_mem hx hy)⟩ : π.S) = ⟨x, hFS hx⟩ + ⟨y, hFS hy⟩ := rfl
      rw [this, map_add (f := _)]
      exact T.add_mem ihx ihy
    | smul a x hx ih =>
      have : (⟨a • x, hFS (F.smul_mem a hx)⟩ : π.S) = a • ⟨x, hFS hx⟩ := rfl
      rw [this, map_smul]
      exact T.smul_mem a ih
  let g : F →ₗ[ℂ] T := LinearMap.codRestrict T (Φ ∘ₗ Submodule.inclusion hFS) (fun f => hFT f f.2)
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : Φ (Submodule.inclusion hFS a) = Φ (Submodule.inclusion hFS b) := congrArg Subtype.val hab
    exact Submodule.inclusion_injective hFS (hinj h1)
  exact Module.Finite.of_injective g hg

section Conj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem fixed_fd_of_conjT (π : NG.FinTyp L n) (N : ℕ)
    (h : FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ (FinTyp.conjT π).S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f})) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f}) := by
  set S1 := Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f} with hS1
  set S2 := Submodule.span ℂ {f | f ∈ (FinTyp.conjT π).S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f} with hS2
  have hmap : ∀ f ∈ S1, (fun g => star (f g)) ∈ S2 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨?_, fun κ hκ => ?_⟩
      · rw [conjT_S, mem_conjSub]
        simpa using hx.1
      · rw [← conj_rt, hx.2 κ hκ]
    | zero =>
      have : (fun g => star ((0 : GAf L n → ℂ) g)) = 0 := by
        funext g
        simp
      rw [this]
      exact S2.zero_mem
    | add x y _ _ hx hy =>
      have : (fun g => star ((x + y) g)) = (fun g => star (x g)) + (fun g => star (y g)) := by
        funext g
        simp
      rw [this]
      exact S2.add_mem hx hy
    | smul a x _ hx =>
      have : (fun g => star ((a • x) g)) = star a • (fun g => star (x g)) := by
        funext g
        simp [mul_comm]
      rw [this]
      exact S2.smul_mem _ hx
  let c : S1 →ₗ[ℝ] S2 :=
    { toFun := fun f => ⟨fun g => star ((f : GAf L n → ℂ) g), hmap f f.2⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by simp)
      map_smul' := fun r a => Subtype.ext (funext fun g => by simp) }
  have hc : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    funext g
    have := congrFun (congrArg Subtype.val hab) g
    exact star_injective this
  haveI : FiniteDimensional ℝ S2 := Module.Finite.trans ℂ S2
  haveI : FiniteDimensional ℝ S1 := Module.Finite.of_injective c hc
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ S1

theorem form_of_conjT (π : NG.FinTyp L n) (B' : (FinTyp.conjT π).S → (FinTyp.conjT π).S → ℂ)
    (hlin : ∀ x y z (c : ℂ), B' x (y + c • z) = B' x y + c * B' x z)
    (hherm : ∀ x y, B' x y = starRingEnd ℂ (B' y x))
    (hpos : ∀ x, x ≠ 0 → 0 < (B' x x).re)
    (hinv : ∀ h (x y x' y' : (FinTyp.conjT π).S), (x' : GAf L n → ℂ) = NG.rt L n h x →
      (y' : GAf L n → ℂ) = NG.rt L n h y → B' x' y' = B' x y) :
    ∃ B : π.S → π.S → ℂ, (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) ∧
      (∀ x y, B x y = starRingEnd ℂ (B y x)) ∧ (∀ x, x ≠ 0 → 0 < (B x x).re) ∧
      ∀ h (x y x' y' : π.S), (x' : GAf L n → ℂ) = NG.rt L n h x →
        (y' : GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y := by
  let c : π.S → (FinTyp.conjT π).S := fun f =>
    ⟨fun g => star ((f : GAf L n → ℂ) g), by rw [conjT_S, mem_conjSub]; simpa using f.2⟩
  have hc : ∀ f : π.S, ((c f : (FinTyp.conjT π).S) : GAf L n → ℂ) = fun g => star ((f : GAf L n → ℂ) g) := fun _ => rfl
  refine ⟨fun x y => starRingEnd ℂ (B' (c x) (c y)), ?_, ?_, ?_, ?_⟩
  · intro x y z a
    have e : c (y + a • z) = c y + (starRingEnd ℂ a) • c z := by
      apply Subtype.ext
      funext g
      simp [hc, mul_comm]
    simp only
    rw [e, hlin, map_add (f := _), map_mul, Complex.conj_conj]
  · intro x y
    simp only
    rw [hherm (c x) (c y)]
  · intro x hx
    simp only
    rw [Complex.conj_re]
    apply hpos
    intro h0
    apply hx
    apply Subtype.ext
    funext g
    have := congrFun (congrArg Subtype.val h0) g
    rw [hc] at this
    simpa using this
  · intro h x y x' y' hx hy
    simp only
    congr 1
    apply hinv h
    · rw [hc, hc, hx]
      rfl
    · rw [hc, hc, hy]
      rfl

end Conj

end GlobalTheory.RowLocalRows

namespace GlobalTheory.RowLocalRows

open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult


end GlobalTheory.RowLocalRows

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLocalRows2

open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult


set_option maxHeartbeats 1000000 in
theorem finTyp_rows_exists_isLocS : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → D.host.F = maximalRealSubfield D.host.E → ∀ (σ : D.what₂.FT) (s : SplitPlace D.host.E), ∃ τ, GlobalTheory.HeightCounting.IsLocS (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S s τ := by
  intro hH hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ _ _ σ s
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ
  have hne : isotIn (D := D) (actM Y.PY (R.MY 0)) (Minf R.θ Y.PY (R.MY 0)) (FinTyp.conjT π) ≠ ⊥ := by
    intro h
    apply hb
    unfold isotE isotL
    rw [h, inf_bot_eq]
  have hM := hP.char.base.models
  have hθ : IsInfFam R.θ := hM.inf
  have hSig : (Yc D 0).SigOK := D.sp.Y_sig 0
  have hcc := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  have hfd : ∀ j, j < D.R.m → (R.νY A3.A.μ0 j).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D j)) (R.fdY A3.A.μ0 j) (R.νY A3.A.μ0 j) := by
    intro j hj
    by_cases h : j + 1 < D.R.m
    · have := hM.νY A3.A.μ0 j h
      exact ⟨this.1.1, this.2⟩
    · obtain rfl : j = D.R.m - 1 := by omega
      have := hM.νY' A3.A.μ0
      exact ⟨this.1.1, this.2⟩
  obtain ⟨hHaar, hFD⟩ := hfd 0 Y.hm
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MY 0) (θ := R.θ) (R.νY A3.A.μ0 0)
    (R.fdY A3.A.μ0 0) Y.PY hSA hSig hθ hHaar hFD
  obtain ⟨B', h1, h2, h3, h4⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r _ (actM Y.PY (R.MY 0))
    (Minf R.θ Y.PY (R.MY 0)) (ipM (R.MY 0) (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0)) hlin hherm hpos
    (fun h x hx => GlobalTheory.FinTypesRows.minf_stable Y.PY hcc h hx)
    (fun h x hx y hy => GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Yc D 0) _ R.θ (R.MY 0) D.R.r Y.PY (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0) hSA hSig hθ
      hHaar hFD h x hx y hy) (FinTyp.conjT π) hne
  obtain ⟨B, k1, k2, k3, k4⟩ := GlobalTheory.RowLocalRows.form_of_conjT π B' h1 h2 h3 h4
  have hadm : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ Minf R.θ Y.PY (R.MY 0) ∧
      ∀ κ, NG.Cong D.host.E D.R.r N κ → actM Y.PY (R.MY 0) κ x = x}) := fun N hN =>
    GlobalTheory.FinTypesRows.minf_adm (M := R.MY 0) Y.PY hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open Y.PY Y.stdPsi.1) N hN
  have hfix : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f}) := fun N hN =>
    GlobalTheory.RowLocalRows.fixed_fd_of_conjT π N (GlobalTheory.RowLocalRows.fixed_fd_of_isotIn _ _ hadm _ hne N hN)
  obtain ⟨W, hWS, hW0, hst, hirr⟩ := GlobalTheory.T.exists_irreducible_subspace_trivialOutside_splitPlace D.host.E D.R.r π B k1 k2 k3 k4 hfix s
  exact GlobalTheory.RowLocal.isLocS_of_irr π s W hWS hW0 hst hirr

end GlobalTheory.RowLocalRows2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveIntBilinFormEqOfPositiveRealRay
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveIntBilinFormEqOfPositiveRealRay
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PrimRay

theorem eq_of_toReal_eq_smul : ∀ {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ), 0 < d →
  (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = x → k = 1) → (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = y → k = 1) →
  toReal x = d • toReal y → x = y ∧ d = 1 := by
  intro X _ x y d hd hx hy h
  have hx0 : x ≠ 0 := fun h0 => by
    have := hx 0 0 (by simp [h0])
    simp at this
  have hy0 : y ≠ 0 := fun h0 => by
    have := hy 0 0 (by simp [h0])
    simp at this
  obtain ⟨a, b, ha, hb, hab⟩ := GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm x y d hd hy0 h
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hcop0 := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hg
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right a b
  generalize Nat.gcd a b = g at hg hcop0 ha' hb'
  subst ha' hb'
  have hcop : Nat.Coprime a' b' := by
    have := hcop0
    have e1 : g * a' / g = a' := Nat.mul_div_cancel_left a' hg
    have e2 : g * b' / g = b' := Nat.mul_div_cancel_left b' hg
    rwa [e1, e2] at this
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hgz : ((g : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 : ∀ p q, (a' : ℤ) * x p q = (b' : ℤ) * y p q := fun p q => by
    have := LinearMap.congr_fun₂ hab p q
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    push_cast at this
    apply mul_left_cancel₀ hgz
    linear_combination this
  set z : LinearMap.BilinForm ℤ X := u • y + w • x with hz
  have hxz : ((b' : ℕ) : ℤ) • z = x := by
    ext p q
    simp only [hz, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    linear_combination (-u) * h1 p q + (x p q) * huw
  have hyz : ((a' : ℕ) : ℤ) • z = y := by
    ext p q
    simp only [hz, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    linear_combination w * h1 p q + (y p q) * huw
  have hb1 : b' = 1 := hx b' z hxz
  have ha1 : a' = 1 := hy a' z hyz
  have hxy : x = y := by
    ext p q
    simpa [ha1, hb1] using h1 p q
  refine ⟨hxy, ?_⟩
  subst hxy
  obtain ⟨p, q, hpq⟩ : ∃ p q, x p q ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (LinearMap.ext₂ hc)
  have := LinearMap.congr_fun₂ h p q
  simp only [toReal_apply, LinearMap.smul_apply, smul_eq_mul] at this
  have hne : (x p q : ℝ) ≠ 0 := by exact_mod_cast hpq
  have := mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)
  exact this

end GlobalTheory.PrimRay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveIntBilinFormEqOfPositiveRealRayStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_intBilinForm_eq_of_positive_real_ray : ∀ {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ), 0 < d →
  (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = x → k = 1) → (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = y → k = 1) →
  toReal x = d • toReal y → x = y ∧ d = 1 := by
  first | exact @GlobalTheory.PrimRay.eq_of_toReal_eq_smul | exact GlobalTheory.PrimRay.eq_of_toReal_eq_smul | (intros; apply GlobalTheory.PrimRay.eq_of_toReal_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.KerTwLv

open Formalism.MainNotions.G _root_.Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.CmpJ.AgreeLv _root_.Formalism.L2.Forms Formalism.UG
open scoped TensorProduct

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
  (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

def frOf {N : ℕ} (B : GL (Fin N) D.host.E) (w' : HeightOneSpectrum (𝓞 D.host.F))
    (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal) : GL (Fin N) (w'.adicCompletion D.host.F) :=
  bc (((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom).comp
    (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B

def chartTw (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : T.Ch u μ (i + 1)) (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E)
    (fr_lat : ∀ w' h (x : Fin (D.sp.X (i + 1)).rank → w'.adicCompletion D.host.F),
      (∃ y ∈ Formalism.L2.Herm.locL w' (T.lev u μ (i + 1) (one_le i) hi β).Lb, ∀ a, ((X0.g u w hg).spl w' h (y a)).1 = x a) ↔
        ∀ a, (((frOf X0 u w hg B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) (w'.adicCompletion D.host.F)) :
          Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) (w'.adicCompletion D.host.F)).mulVec x a ∈
            w'.adicCompletionIntegers D.host.F)
    (ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (T.lev u μ (i + 1) (one_le i) hi β).Uloc (D.what₂.places.resChar w) →*
      (D.gat u w hg).Oˣ)
    (fin : Finite (compG D.sp.cm.sig (D.sp.X (i + 1)).gram (T.lev u μ (i + 1) (one_le i) hi β).Uloc (D.what₂.places.resChar w))) :
    ChartG (X0.g u w hg) (D.sp.X (i + 1)).rank where
  J := (D.sp.X (i + 1)).gram
  Lb := (T.lev u μ (i + 1) (one_le i) hi β).Lb
  Uloc := (T.lev u μ (i + 1) (one_le i) hi β).Uloc
  fr := frOf X0 u w hg B
  fr_lat := fr_lat
  ψ := ψ
  eps := 1
  fin := fin

theorem rank_lv (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (i : ℕ) (hi : i < D.R.m) :
    (D.gat u w hg).P.m + (i + 1) * (Fl.t + 1) + 1 = (D.sp.X (i + 1)).rank := by
  have hk := Gt.gat_k u w hg
  rw [← rank_step D i hi, ht]
  omega

instance chFin (i : ℕ) : Finite (T.Ch u μ i) := T.ChFin u μ i

abbrev levelsTwG (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)
    (St : ∀ i (_ : i < D.R.m), T.Ch u μ (i + 1) → ChartG (X0.g u w hg) (D.sp.X (i + 1)).rank) : Levels Fl :=
  levelsG (X0.g u w hg) Fl D.R.m (fun i => (D.sp.X (i + 1)).rank) (rank_lv u w hg Gt Fl ht) (fun i _ => T.Ch u μ (i + 1)) St

structure ChData where
  B : ∀ i (_ : i + 1 ≤ D.R.m), GL (Fin (D.sp.X (i + 1)).rank) D.host.E
  fr_lat : ∀ i (hi : i + 1 ≤ D.R.m) (β : T.Ch u μ (i + 1)) w' h (x : Fin (D.sp.X (i + 1)).rank → w'.adicCompletion D.host.F),
      (∃ y ∈ Formalism.L2.Herm.locL w' (T.lev u μ (i + 1) (one_le i) hi β).Lb, ∀ a, ((X0.g u w hg).spl w' h (y a)).1 = x a) ↔
        ∀ a, (((frOf X0 u w hg (B i hi) w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) (w'.adicCompletion D.host.F)) :
          Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) (w'.adicCompletion D.host.F)).mulVec x a ∈
            w'.adicCompletionIntegers D.host.F
  ψ : ∀ i (hi : i + 1 ≤ D.R.m) (β : T.Ch u μ (i + 1)),
    awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (T.lev u μ (i + 1) (one_le i) hi β).Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ
  fin : ∀ i (hi : i + 1 ≤ D.R.m) (β : T.Ch u μ (i + 1)),
    Finite (compG D.sp.cm.sig (D.sp.X (i + 1)).gram (T.lev u μ (i + 1) (one_le i) hi β).Uloc (D.what₂.places.resChar w))

variable {T X0 u μ w hg}

abbrev ChData.St (Cd : ChData T X0 u μ w hg) (i : ℕ) (hi : i < D.R.m) (β : T.Ch u μ (i + 1)) :
    ChartG (X0.g u w hg) (D.sp.X (i + 1)).rank :=
  chartTw T X0 u μ w hg i hi β (Cd.B i hi) (Cd.fr_lat i hi β) (Cd.ψ i hi β) (Cd.fin i hi β)

abbrev ChData.Lv (Cd : ChData T X0 u μ w hg) (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) : Levels Fl :=
  levelsTwG T X0 u μ w hg Gt Fl ht Cd.St

def ChData.Lc (Cd : ChData T X0 u μ w hg) (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (i : ℕ)
    (hi : i + 1 ≤ D.R.m) : LocIn X0 u w hg (Cd.Lv Gt Fl ht) i (T.Ch u μ (i + 1)) :=
  haveI : ∀ β, Fintype (Cd.St i hi β).comp := fun β => haveI := (Cd.St i hi β).fin; Fintype.ofFinite _
  locInOf (fun β => (Cd.St i hi β).comp) (fun β a => ⟨hi, β, a⟩)
    (levelsG_cover (X0.g u w hg) Fl D.R.m _ (rank_lv u w hg Gt Fl ht) (fun i _ => T.Ch u μ (i + 1)) Cd.St i hi)
    (fun β => (T.lev u μ (i + 1) (one_le i) hi β).Lb) (fun β => (T.lev u μ (i + 1) (one_le i) hi β).Uloc) (Cd.ψ i hi)
    (fun β => levelsG_tie (X0.g u w hg) Fl D.R.m _ (rank_lv u w hg Gt Fl ht) (fun i _ => T.Ch u μ (i + 1)) Cd.St i hi β)
    (Cd.B i hi)

theorem ChData.empty (Cd : ChData T X0 u μ w hg) (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (j : ℕ)
    (hj : D.R.m ≤ j) : IsEmpty ((Cd.Lv Gt Fl ht).compS j) :=
  ⟨fun c => absurd c.1 (by omega)⟩

section Ties
variable {Tw : TwForms D} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} (W : TwFormsTiedS D Tw T J F) (hμ : μ ≠ D.what₂.mu0)
  (Cd : ChData T X0 u μ w hg) (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)
  (dt : ∀ j (hj : j + 1 ≤ D.R.m) β, DetTie (W.ch u μ hμ (j + 1) (one_le j) hj β).lev)

theorem ChData.frRat (j : ℕ) (hj : j + 1 ≤ D.R.m) (β : T.Ch u μ (j + 1)) :
    FrRatJ ((Cd.Lc Gt Fl ht j hj).t β) (Cd.Lc Gt Fl ht j hj).B :=
  fun _ _ => by
    unfold ChData.Lc locInOf levelsG_tie ChData.St chartTw frOf
    rfl


set_option maxHeartbeats 4000000 in
theorem ChData.sameU (j : ℕ) (hj : j + 1 ≤ D.R.m) (β : T.Ch u μ (j + 1)) :
    SameUlocJ hj ((formsInTw W u μ hμ j hj (dt j hj)).K β).lev ((Cd.Lc Gt Fl ht j hj).Uloc β) :=
  (W.car u μ hμ (j + 1) (one_le j) hj β).Uloc_eq


set_option maxHeartbeats 4000000 in
theorem ChData.Lb_eq (j : ℕ) (hj : j + 1 ≤ D.R.m) (β : T.Ch u μ (j + 1)) :
    ((formsInTw W u μ hμ j hj (dt j hj)).K β).lev.Lb = reL (rankN D (j + 1) hj) ((Cd.Lc Gt Fl ht j hj).Lb β) :=
  (W.car u μ hμ (j + 1) (one_le j) hj β).Lb_eq

end Ties

end GlobalTheory.Mem.Top.KerTwLv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVectorConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLevelSplitData

theorem fixed_ne_bot_of_fixed_vector_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), GlobalTheory.HeightCounting.IsLocS π.S s τ → ∀ f ∈ π.S, f ≠ 0 → (∀ κ : Formalism.AUTREP.GAf L n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f) → GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n π s τ h hloc f hf hf0 hfix
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s h
  have hmul : ∀ (a b : Formalism.AUTREP.GAf L n) (g : Formalism.AUTREP.GAf L n → ℂ), NG.rt L n (a * b) g = NG.rt L n a (NG.rt L n b g) := by
    intro a b g
    funext c
    simp [NG.rt, mul_assoc]
  have hone : ∀ g : Formalism.AUTREP.GAf L n → ℂ, NG.rt L n 1 g = g := by
    intro g
    funext c
    simp [NG.rt]
  have hT : ∀ a b : Formalism.AUTREP.GAf L n, TrivOutside {s.v} a → TrivOutside {s.v} b → TrivOutside {s.v} (a * b) :=
    fun a b ha hb v hv => by
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha v hv, hb v hv, mul_one]
  refine GlobalTheory.FixedAtSplit.fixed_ne_bot_of_fixed_vector L n π s τ hloc (NG.rt L n x⁻¹ f) ?_ ?_ ?_
  · exact π.stable _ f hf
  · intro h0
    apply hf0
    rw [← hone f, ← mul_inv_cancel x, hmul, h0, map_zero]
  · intro κ hκ hk
    have h1 := hfix (x * κ * x⁻¹) (hT _ _ (hT _ _ hx hκ) (GlobalTheory.RowLevelSplit.trivOutside_inv hx)) (by
      rw [map_mul, map_mul, map_inv, e, show h⁻¹ * (h * s.loc n κ * h⁻¹) * h = s.loc n κ by group]
      exact hk)
    rw [← hmul, show κ * x⁻¹ = x⁻¹ * (x * κ * x⁻¹) by group, hmul, h1]

end GlobalTheory.RowLevelSplitData

end
end
