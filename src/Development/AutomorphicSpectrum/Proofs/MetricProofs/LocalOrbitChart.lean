module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolution
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCWArith
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorScalar
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralModelFormula
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem exists_injective_linear {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ}
    (h : Module.finrank ℂ W ≤ n) : ∃ j : W →ₗ[ℂ] (Fin n → ℂ), Function.Injective j := by
  let e : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearEquiv.ofFinrankEq _ _ (by simp)
  let s : Fin (Module.finrank ℂ W) → Fin n := Fin.castLE h
  have hs : Function.Injective s := Fin.castLE_injective h
  refine ⟨(Function.ExtendByZero.linearMap ℂ ℂ s).comp e.toLinearMap, fun a b hab => e.injective ?_⟩
  funext i
  have := congrFun hab (s i)
  change Function.extend s (e a) 0 (s i) = Function.extend s (e b) 0 (s i) at this
  rwa [hs.extend_apply, hs.extend_apply] at this

theorem exists_injOn_of_strict {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {Φ : E → F} {L : E →L[ℂ] F} {w : E}
    (hΦ : HasStrictFDerivAt Φ L w) (hL : Function.Injective L) :
    ∃ B : Set E, IsOpen B ∧ w ∈ B ∧ Set.InjOn Φ B := by
  obtain ⟨N, hN, hanti⟩ := (L : E →ₗ[ℂ] F).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hL)
  have hc : (0 : NNReal) < (2 * N)⁻¹ := by positivity
  obtain ⟨s, hs, hap⟩ := hΦ.approximates_deriv_on_nhds (c := (2 * N)⁻¹) (Or.inr hc)
  obtain ⟨B, hBs, hB, hwB⟩ := mem_nhds_iff.1 hs
  refine ⟨B, hB, hwB, fun u hu v hv huv => ?_⟩
  have h1 := hap u (hBs hu) v (hBs hv)
  rw [huv, sub_self, zero_sub, norm_neg] at h1
  have h2 : ‖u - v‖ ≤ N * ‖L (u - v)‖ := by
    have := hanti.le_mul_dist (u - v) 0
    simpa [dist_eq_norm] using this
  by_contra hne
  have hpos : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : ‖u - v‖ ≤ N * (((2 * N)⁻¹ : NNReal) * ‖u - v‖) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 hN'.le)
  have h4 : (N : ℝ) * (((2 * N)⁻¹ : NNReal) * ‖u - v‖) = ‖u - v‖ / 2 := by
    push_cast
    field_simp
  rw [h4] at h3
  linarith

theorem exists_linear_separation {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (n : ℕ)
    (hcard : Fintype.card σ ≤ Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt I w) + n) :
    ∃ (π : (σ → ℂ) →L[ℂ] (Fin n → ℂ)) (B : Set (σ → ℂ)), IsOpen B ∧ w ∈ B ∧
      ∀ u ∈ B, ∀ v ∈ B, (∀ h ∈ I, eval u h = 0) → (∀ h ∈ I, eval v h = 0) → π u = π v → u = v := by
  classical
  set S : Set (σ → ℂ) := (fun h : MvPolynomial σ ℂ => fun j => eval w (pderiv j h)) '' (I : Set _) with hS
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ S
  have hbfin : b.Finite := hli.setFinite
  haveI : Fintype b := hbfin.fintype
  have hex : ∀ t : b, ∃ f ∈ I, (fun j => eval w (pderiv j f)) = (t : σ → ℂ) := fun t => by
    obtain ⟨f, hf, h⟩ := hbS t.2
    exact ⟨f, hf, h⟩
  choose F hFI hFg using hex
  let M : Matrix b σ ℂ := fun t q => (t : σ → ℂ) q
  have hrank : M.rank = Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt I w) := by
    rw [Matrix.rank_eq_finrank_span_row]
    have : Set.range M.row = b := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact t.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [this, hspan]
    rfl
  let W : Submodule ℂ (σ → ℂ) := LinearMap.ker M.mulVecLin
  have hW : Module.finrank ℂ W ≤ n := by
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have h' : Module.finrank ℂ (LinearMap.range M.mulVecLin) = M.rank := rfl
    simp only [Module.finrank_fintype_fun_eq_card] at h
    show Module.finrank ℂ (LinearMap.ker M.mulVecLin) ≤ n
    omega
  obtain ⟨j, hj⟩ := exists_injective_linear hW
  obtain ⟨l, hl⟩ := W.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype W)
  let π : (σ → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap (j.comp l)
  let Φ : (σ → ℂ) → (b → ℂ) × (Fin n → ℂ) := fun x => (fun t => eval x (F t), π x)
  let L0 : (σ → ℂ) →L[ℂ] (b → ℂ) := ContinuousLinearMap.pi fun t => polyDiff (F t) w
  have hd : HasStrictFDerivAt Φ (L0.prod π) w :=
    (hasStrictFDerivAt_pi.2 fun t => hasStrictFDerivAt_eval_poly (F t) w).prodMk π.hasStrictFDerivAt
  have hinj : Function.Injective (L0.prod π) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h1 : L0 v = 0 := congrArg Prod.fst hv
    have h2 : π v = 0 := congrArg Prod.snd hv
    have hvW : v ∈ W := by
      show M.mulVecLin v = 0
      funext t
      have h3 := congrFun h1 t
      have h4 : polyDiff (F t) w v = 0 := h3
      rw [polyDiff_apply] at h4
      have h5 : ∀ q, eval w (pderiv q (F t)) = (t : σ → ℂ) q := fun q => congrFun (hFg t) q
      simp only [h5] at h4
      show ∑ q, (t : σ → ℂ) q * v q = 0
      exact h4
    have h6 : j (l v) = 0 := h2
    have h7 : l v = 0 := hj (by rw [h6, map_zero])
    have h8 : l (W.subtype ⟨v, hvW⟩) = ⟨v, hvW⟩ := LinearMap.congr_fun hl _
    have h9 : (⟨v, hvW⟩ : W) = 0 := by rw [← h8]; exact h7
    exact congrArg Subtype.val h9
  obtain ⟨B, hB, hwB, hBinj⟩ := exists_injOn_of_strict hd hinj
  refine ⟨π, B, hB, hwB, fun u hu v hv hIu hIv huv => hBinj hu hv ?_⟩
  refine Prod.ext (funext fun t => ?_) huv
  show eval u (F t) = eval v (F t)
  rw [hIu _ (hFI t), hIv _ (hFI t)]

theorem localOrbitChart : LocalOrbitChart.Statement := by
  intro K _ ι _ Ω _ inst y n hP hsm z₀ hz₀
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) :=
    isMultiHomogIdeal_pC hP.2.1.2.1
  obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart z₀ hz₀.1
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]
      simp
    have h1 := hz₀.2 _ hX
    rw [map_X, eval_X] at h1
    exact hp k h1
  have hzero : ∀ z ∈ mcPts (mCoordIdeal y), (∀ k, z ⟨k, p k⟩ ≠ 0) →
      ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p,
        eval (ReciprocityTheory.AnForm.R.affCoord p z) h = 0 := fun z hz hzp =>
    (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh p z hzp).1 ((mem_mcPts_iff_conePts_pC _ _).1 hz)
  have hrank := GlobalTheory.CompanionTheory.Ar.PB.SmoothMan.card_le_finrank_jacSpanAt K ι Ω y n hP hsm p hy
    (ReciprocityTheory.AnForm.R.affCoord p z₀) (hzero z₀ hz₀ hp)
  obtain ⟨π, B, hB, hwB, hsep⟩ := exists_linear_separation _ _ n hrank
  let D : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, z ⟨k, p k⟩ ≠ 0}
  have hDopen : IsOpen D := by
    have : D = ⋂ k, {z | z ⟨k, p k⟩ ≠ 0} := by ext z; simp [D]
    rw [this]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have han : ∀ z ∈ D, AnalyticAt ℂ (ReciprocityTheory.AnForm.R.affCoord p) z := by
    intro z hz
    refine analyticAt_pi_iff.2 fun q => ?_
    have hc : ∀ r : Σ k, ι k, AnalyticAt ℂ (fun v : (Σ k, ι k) → ℂ => v r) z := fun r =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) r).analyticAt z
    exact (hc q).div (hc ⟨q.1, p q.1⟩) (hz q.1)
  have hcont : ContinuousOn (ReciprocityTheory.AnForm.R.affCoord p) D := fun z hz =>
    (han z hz).continuousAt.continuousWithinAt
  refine ⟨D ∩ ReciprocityTheory.AnForm.R.affCoord p ⁻¹' B, hcont.isOpen_inter_preimage hDopen hB, ⟨hp, hwB⟩,
    fun z => π (ReciprocityTheory.AnForm.R.affCoord p z), ?_, ?_, ?_⟩
  · intro z hz
    exact (π.analyticAt _).comp (han z hz.1)
  · intro z hz c hc
    have hA : ReciprocityTheory.AnForm.R.affCoord p (torusSmul c z) = ReciprocityTheory.AnForm.R.affCoord p z :=
      ReciprocityTheory.AnForm.R.affCoord_eq_of_sameOrbit p ⟨c, hc, rfl⟩
    refine ⟨⟨fun k => mul_ne_zero (hc k) (hz.1 k), ?_⟩, ?_⟩
    · show ReciprocityTheory.AnForm.R.affCoord p (torusSmul c z) ∈ B
      rw [hA]
      exact hz.2
    · show π _ = π _
      rw [hA]
  · rintro z ⟨hzN, hzX⟩ z' ⟨hzN', hzX'⟩ hκ
    have hA := hsep _ hzN.2 _ hzN'.2 (hzero z hzX hzN.1) (hzero z' hzX' hzN'.1) hκ
    refine ⟨fun k => z' ⟨k, p k⟩ / z ⟨k, p k⟩, fun k => div_ne_zero (hzN'.1 k) (hzN.1 k), ?_⟩
    funext q
    have h1 : z q / z ⟨q.1, p q.1⟩ = z' q / z' ⟨q.1, p q.1⟩ := congrFun hA q
    have h2 := hzN.1 q.1
    have h3 := hzN'.1 q.1
    show z' q = z' ⟨q.1, p q.1⟩ / z ⟨q.1, p q.1⟩ * z q
    rw [div_mul_eq_mul_div, eq_div_iff h2]
    rw [div_eq_div_iff h2 h3] at h1
    linear_combination -h1

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChartStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_orbit_chart_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.LocalOrbitChart.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart | exact GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Slots
variable {X : Type} [TopologicalSpace X] {e : ℕ}

def positionPot (th Pn : LocPot X) (f : X → ℝ) (i : ℕ) : Fin e → LocPot X :=
  fun j => (if (j : ℕ) < i then th else Pn) + LocPot.ofFun (if (j : ℕ) < i then f else fun _ => 0)

end Slots

section Lines
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W}

def muVert (Hd : HodgeData D) (B : ℕ) : HermLine J :=
  hermOfFun J (muTwDeg Hd B) fun z => (muLine Hd).h z * ∏ p ∈ D.SB B, D.vertFactor p z

def limTop (Hd : HodgeData D) (B : ℕ) (Nb : HermLine J) : ℝ :=
  II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) -
    ∑ i ∈ Finset.range (D.n + 1), ptsIntegral (mCoordIdeal D.y)
      (pot fun j : Fin D.n => if (j : ℕ) < i then muVert Hd B else Nb)
      (fun z => Real.log (Nb.h z) - Real.log ((muVert Hd B).h z))

end Lines
end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirst
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlockDiagFrameChange
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlockDiagFrameChange
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem exists_flags_good : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal y) → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z)) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) ∧ ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk z) p.2 ⟨k, m⟩ (h p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F z hz hF hG
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  have hch : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, F.c k⟩ ≠ 0 := fun k h0 => hG.1 k (by
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0])
  obtain ⟨c, hc, hcb, hc1⟩ : ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (∀ k : NonPluckerBlocks M.blk, c k.1 * basePart M.blk z ⟨k, F.c k⟩ = 1) ∧
      ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → c k = 1 := by
    refine ⟨fun k => if hk : ∀ p, M.blk p ≠ some k then (basePart M.blk z ⟨⟨k, hk⟩, F.c ⟨k, hk⟩⟩)⁻¹ else 1,
      fun k => ?_, fun k => ?_, fun p k hp => ?_⟩
    · by_cases hk : ∀ p, M.blk p ≠ some k
      · simp only [dif_pos hk]
        exact inv_ne_zero (hch ⟨k, hk⟩)
      · simp only [dif_neg hk]
        exact one_ne_zero
    · simp only [dif_pos k.2]
      exact inv_mul_cancel₀ (hch k)
    · have hk : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
      simp only [dif_neg hk]
  let z₁ : (Σ k, ι k) → ℂ := fun q => c q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal y) c hc hz
  have hb₁ : basePart M.blk z₁ = fun q => (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk z q := rfl
  have hT := StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x (basePart M.blk z)
    (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc k.1)
  have hI : mCoordIdeal (basePart M.blk z₁) = mCoordIdeal (basePart M.blk z) := by
    rw [hb₁]
    exact hT.1
  have hG₁ : M.GoodAt F (mCoordIdeal (basePart M.blk z₁)) := by rw [hI]; exact hG
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, F.c k⟩ = 1 := hcb
  obtain ⟨h, -, hh, hs⟩ := (h3 F hF z₁ (h1 z₁ hz₁) hG₁ hnorm).1 hz₁
  have hval : ∀ s : M.Ω, valAt M.x s (basePart M.blk z₁) = valAt M.x s (basePart M.blk z) := fun s => by
    rw [hb₁]
    exact (hT.2 (h1 z hz)).2 s
  refine ⟨h, hh, fun p k hp => ?_⟩
  obtain ⟨a, ha, hm⟩ := hs p k hp
  refine ⟨a, ha, fun m => ?_⟩
  have e := hm m
  simp only [hval] at e
  have e' : z₁ ⟨k, m⟩ = z ⟨k, m⟩ := by
    show c k * z ⟨k, m⟩ = z ⟨k, m⟩
    rw [hc1 p k hp, one_mul]
  rw [e'] at e
  exact e

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlockDiagFrameChangeStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_diag_frame_change : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal y) → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z)) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) ∧ ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk z) p.2 ⟨k, m⟩ (h p.1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.exists_flags_good | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.exists_flags_good | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.exists_flags_good <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirst
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem base_orbit {σ : Type} {blk : σ → Option K} {z₁ z : (Σ k, ι k) → ℂ} (h : SameOrbit z₁ z) :
    SameOrbit (basePart blk z₁) (basePart blk z) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem comp_orbit {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) {b₁ b : (Σ k, ι' k) → ℂ} (h : SameOrbit b₁ b) :
    SameOrbit (b₁ ∘ v) (b ∘ v) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext q
  simp only [Function.comp]
  rw [hv.2.2.1 q]

theorem ideal_orbit {b₁ b : (Σ k, ι k) → ℂ} (h : SameOrbit b₁ b) : mCoordIdeal b₁ = mCoordIdeal b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact StepW.TorusAct.mCoordIdeal_torus c hc b

theorem valAt_orbit {x : (Σ k, ι k) → Ω} {b₁ b : (Σ k, ι k) → ℂ} (h : SameOrbit b₁ b)
    (hb : b ∈ mcPts (mCoordIdeal x)) (s : Ω) : valAt x s b₁ = valAt x s b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ((StepW.TorusAct.main K ι Ω x b c hc).2 hb).2 s

end Orbit

theorem img_spec (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j)
    (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F₀' : FrameData ι' Ψ N M'.Ω M'.blk)
    (F₀ : FrameData ι Ψ N M.Ω M.blk) (hz : z ∈ mcPts (mCoordIdeal y')) (hF' : M'.IsFrame F₀') (hF : M.IsFrame F₀)
    (hg' : M'.GoodAt F₀' (mCoordIdeal (basePart M'.blk z)))
    (hg : M.GoodAt F₀ (mCoordIdeal (basePart M'.blk z ∘ Cv.v))) :
    img Cv F₀' F₀ z ∈ mcPts (mCoordIdeal y) ∧ IsImg Cv z (img Cv F₀' F₀ z) := by
  have hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z hz
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨h₀, hh₀, hz₀⟩ := GlobalTheory.T.exists_block_diag_frame_change K' ι' Φ' y' Ψ N j M' F₀' z hz hF' hg'
  have hT₀ := GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F₀' F₀ hb hF' hF hg' hg
  have hH₀ : ∀ τ, IsBlockDiag j (Cv.trans F₀' F₀ (basePart M'.blk z) τ * h₀ τ) ∧
      (Cv.trans F₀' F₀ (basePart M'.blk z) τ * h₀ τ).det ≠ 0 := fun τ =>
    ⟨(hT₀ τ).1.mul (hh₀ τ).1, by rw [det_mul]; exact mul_ne_zero (hT₀ τ).2 (hh₀ τ).2⟩
  have hform := GlobalTheory.T.flag_cover_frames_value_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F₀' F₀ h₀ hb hF' hF hg' hg
    (fun τ => (hh₀ τ).1) hz₀
  have hwb : basePart M.blk (img Cv F₀' F₀ z) = basePart M'.blk z ∘ Cv.v := img_base Cv F₀' F₀ z
  have hw : img Cv F₀' F₀ z ∈ mcPts (mCoordIdeal y) :=
    (GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F₀ (img Cv F₀' F₀ z) _ hF (by rw [hwb]; exact hbv) (by rw [hwb]; exact hg) hH₀
      (by rw [hwb]; exact hform)).1
  refine ⟨hw, ?_⟩
  intro z₁ h1 F' F hF1' hF1 hg1' hg1 h hfl
  have hbo : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z) := base_orbit h1
  have hbov := comp_orbit Cv.block hbo
  rw [ideal_orbit hbo] at hg1'
  rw [ideal_orbit hbov] at hg1
  have htrans : ∀ τ, Cv.trans F' F (basePart M'.blk z₁) τ = Cv.trans F' F (basePart M'.blk z) τ := fun τ => by
    ext a c
    exact valAt_orbit hbo hb _
  obtain ⟨-, hhinv, hflag⟩ := hfl
  have hpl : ∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k',
      plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1) =
        a * plk M' F₀' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h₀ p.1) := fun p k' hp => by
    obtain ⟨a, ha, e⟩ := hflag p k' hp
    obtain ⟨a₀, ha₀, e₀⟩ := hz₀ p k' hp
    obtain ⟨c, hc, rfl⟩ := h1
    refine ⟨a⁻¹ * c k' * a₀, mul_ne_zero (mul_ne_zero (inv_ne_zero ha) (hc k')) ha₀, fun m' => ?_⟩
    have e1 := e m'
    have e2 := e₀ m'
    have e3 : ∑ I, valAt M'.x (F'.u ⟨k', m'⟩ I) (basePart M'.blk fun p => c p.1 * z p) *
        minorIJ (h p.1) I (stepCols N j p.2) = plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1) :=
      Finset.sum_congr rfl fun I _ => by rw [valAt_orbit hbo hb]
    rw [e3] at e1
    simp only at e1
    rw [e2] at e1
    field_simp
    linear_combination -e1
  have hind := GlobalTheory.T.flag_cover_two_frames_comparison K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F₀' F F₀ h h₀ hb hF1' hF' hF1 hF hg1' hg' hg1 hg
    (fun τ => (hhinv τ).1) (fun τ => (hh₀ τ).1) hpl
  have hT := GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hb hF1' hF1 hg1' hg1
  obtain ⟨-, z₀, o1, o2, fl⟩ := GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F (img Cv F₀' F₀ z)
    (fun τ => Cv.trans F' F (basePart M'.blk z) τ * h τ) hF1 (by rw [hwb]; exact hbv) (by rw [hwb]; exact hg1)
    (fun τ => ⟨(hT τ).1.mul (hhinv τ).1, by rw [det_mul]; exact mul_ne_zero (hT τ).2 (hhinv τ).2⟩)
    (fun p k hp => by
      obtain ⟨a₁, ha₁, e₁⟩ := hform p k hp
      obtain ⟨a₂, ha₂, e₂⟩ := hind p k hp
      refine ⟨a₁ * a₂⁻¹, mul_ne_zero ha₁ (inv_ne_zero ha₂), fun m => ?_⟩
      rw [e₁ m, hwb, e₂ m]
      field_simp)
  refine ⟨z₀, o1, Cj.sameOrbit_trans (hwb ▸ o2) (Cj.sameOrbit_symm hbov), ?_⟩
  simp only [htrans]
  exact fl

theorem local_img : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), f z' ∈ mcPts (mCoordIdeal y) ∧ CovMap.IsImg Cv z' (f z') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _ z hz
  have hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z hz
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨F', hF', hg'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 _ hb
  obtain ⟨F, hF, hg⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hbv
  obtain ⟨V, f, hV, hzV, hf, hs⟩ := GlobalTheory.T.flag_cover_frames_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F' F hz hF' hF hg' hg
  refine ⟨V, f, hV, hzV, hf, fun z' hz' => ?_⟩
  obtain ⟨g1, g2, e⟩ := hs z' hz'
  rw [e]
  exact img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z' F' F hz'.2 hF' hF g1 g2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirstStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_arithmetic_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), f z' ∈ mcPts (mCoordIdeal y) ∧ CovMap.IsImg Cv z' (f z') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmetic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmetic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 3) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) (d + 2) ∧ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0) ∧ imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y ∧ ∀ v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀)), (∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩) → (∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) → imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y := by
  first | exact @PositivityTheory.Xgp.t_c_w_arith | exact PositivityTheory.Xgp.t_c_w_arith
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmeticStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 3) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) (d + 2) ∧ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0) ∧ imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y ∧ ∀ v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀)), (∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩) → (∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) → imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic | exact GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystem
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.AigGen
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PositivityTheory.HtPt.Aig

theorem coordFibreDeg : GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.Statement :=
  GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.proof GroundTheory.Heights₂.Heights.Targets.FibreMultiHomog.proof
    (GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof
      GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.proof)
    GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg.proof

theorem genDeg_of_coord (hPF : PFCoordStatement) (hFD : FibreDimStatement) : GenDegStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G J L L' hv hP' hP hJ hL hLL'
  obtain ⟨Ω, _, y, hy, -⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.proof K' ι' P' d hP'
  subst hy
  have : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hz : ((n : ℤ) : Ω) = 0 := by exact_mod_cast hn
    have hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y := by
      simp only [mCoordIdeal, RingHom.mem_ker, mConeMap, eq_intCast]
      rw [map_intCast, ← map_intCast (C : Ω →+* MvPolynomial K' Ω), hz, map_zero]
    have h2 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι') := hmem
    rw [hP'.2.2.1] at h2
    exact_mod_cast (Ideal.mem_bot).1 h2
  have hV : IsProjVarF (fibreIdeal κ G) 0 := hFD K ι K' ι' κ v (mCoordIdeal y) d 0 G hv hP' hP
  choose i hi using hV.1.2.2
  have h0 := hJ.1 (fibreIdeal κ G) Fin.elim0 i hV hi
  rw [hPF I hI K ι K' ι' κ v Ω y d L L' hv hP' hP hL hLL', h0,
    coordFibreDeg K ι K' ι' κ v Ω y d G i hv hP' hP hi, Int.cast_natCast]

theorem genDeg : PFCoordStatement → FibreDimStatement → GenDegStatement :=
  genDeg_of_coord

end PositivityTheory.HtPt.Aig
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfProjectionAndFibreDim
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfProjectionAndFibreDim
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @PositivityTheory.HtPt.Aig.genDeg | exact PositivityTheory.HtPt.Aig.genDeg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfProjectionAndFibreDimStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | exact GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | (intros; apply GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem genDeg_of_system (h : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement) :
    GenDegStatement :=
  GlobalTheory.T.generic_degree_of_projection_and_fibre_dim (GlobalTheory.T.coordinate_projection_of_arith_system h) fibreDim

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothConjInvariantMetric
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothConjInvariantMetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (a : K → ℤ), ∃ A : HermLine J, A.a = a ∧ IsSmoothHerm A ∧ IsConjInvariantH A := by
  intro K _ J _ a
  let S : K → ((k : K) × J k → ℂ) → ℝ := fun k z => ∑ i, ‖z ⟨k, i⟩‖ ^ 2
  have hS0 : ∀ k z, 0 ≤ S k z := fun k z => Finset.sum_nonneg fun i _ => by positivity
  have hSpos : ∀ k (z : (k : K) × J k → ℂ), (∃ i, z ⟨k, i⟩ ≠ 0) → 0 < S k z := by
    rintro k z ⟨i, hi⟩
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))
  have hSmul : ∀ (c : K → ℂ) k (z : (k : K) × J k → ℂ), S k (fun p => c p.1 * z p) = ‖c k‖ ^ 2 * S k z := by
    intro c k z
    simp only [S, norm_mul, mul_pow, Finset.mul_sum]
  refine ⟨⟨a, fun z => ∏ k, S k z ^ ((a k : ℝ) / 2), ?_, ?_⟩, rfl, ?_, ?_⟩
  · intro z hz
    exact Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hSpos k z (hz k)) _
  · intro c z hc
    show ∏ k, S k (fun p => c p.1 * z p) ^ ((a k : ℝ) / 2) = _
    simp only [hSmul]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Real.mul_rpow (by positivity) (hS0 k z)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  · show ContDiffOn ℝ _ (fun z => ∏ k, S k z ^ ((a k : ℝ) / 2)) _
    apply contDiffOn_prod
    intro k _ z hz
    exact ((ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) _)).contDiffAt.rpow_const_of_ne
      (hSpos k z (hz k)).ne').contDiffWithinAt
  · intro z
    simp [S]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothConjInvariantMetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_conj_invariant_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (a : K → ℤ), ∃ A : HermLine J, A.a = a ∧ IsSmoothHerm A ∧ IsConjInvariantH A := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric | exact GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BigLineImpliesHeightPositivity
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BigLineImpliesHeightPositivity
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem selfIntersection_le_volNm_of_moriwakiBig : MoriwakiBigStatement → BirationalPullbackPushforwardFormula := by
  intro h K _ ι _ Ω _ y D A P0 II hD hII hV hB hP hS hF hC
  have hN : NefOnGeneric (mCoordIdeal y) A :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.proof K ι (mCoordIdeal y) P0 A hP hS
  have hb := h K ι Ω y D A P0 II hII hV hB hP hS hC hF hN
  obtain ⟨hfin, C, hC'⟩ := GlobalTheory.T.packing' K ι Ω y D A (chartLatNm y A.a) hV hB hS.1 (fun _ => le_rfl)
  refine hb.trans ?_
  unfold arVolP
  have h0 : ∀ (La : ℕ → AddSubgroup Ω) (τ : ℕ), 0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) La τ := by
    intro La τ
    unfold smallSectionCount
    exact Real.log_natCast_nonneg _
  have hden : ∀ k : ℕ, (0 : ℝ) ≤ ((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := fun k => by positivity
  refine Filter.limsup_le_limsup ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun k => div_le_div_of_nonneg_right
      (GroundTheory.Heights₂.Heights.HilbertSamuel.smallSectionCount_mono_lattice _ _
        (GroundTheory.Heights₂.Heights.HilbertSamuel.chartLat_le_chartLatNm y A.a _) (hfin _)) (hden k)
  · exact Filter.isCoboundedUnder_le_of_le Filter.atTop (fun k => div_nonneg (h0 _ _) (hden k))
  · refine Filter.isBoundedUnder_of_eventually_le (a := max C 0 * 2 ^ (D + 1) * ((D + 1).factorial : ℝ)) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkpos : (0 : ℝ) < ((1 * k : ℕ) : ℝ) := by
      rw [one_mul]
      exact_mod_cast hk
    have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpos : (0 : ℝ) < ((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    have h1 := hC' (1 * k)
    have h2 : ((1 * k : ℕ) : ℝ) + 1 ≤ 2 * ((1 * k : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((1 * k : ℕ) : ℝ) := by
        rw [one_mul]
        exact_mod_cast hk
      linarith
    have h3 : (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) ≤ (2 * ((1 * k : ℕ) : ℝ)) ^ (D + 1) :=
      pow_le_pow_left₀ (by positivity) h2 _
    have h4 : C * (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) ≤ max C 0 * (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hF' := hF.ne'
    calc _ ≤ max C 0 * (2 * ((1 * k : ℕ) : ℝ)) ^ (D + 1) :=
          h1.trans (h4.trans (mul_le_mul_of_nonneg_left h3 (le_max_right _ _)))
      _ = max C 0 * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) *
          (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
        field_simp
        ring

end GlobalTheory.CompanionTheory.Ar.Small
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BigLineImpliesHeightPositivityStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_line_implies_height_positivity : MoriwakiBigStatement → BirationalPullbackPushforwardFormula := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig | exact GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolution
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolution
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isBlockDiag_one_add_single {N j : ℕ} {ca cb : Fin N} (hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s hrs
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
  have h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hrs hs.symm
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem not_sameOrbit_of_ptData : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t → ¬ SameOrbit (fstPt k₀ (RW.lift x x)) (sndPt k₀ (RW.lift x x)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hW x z₀ z₁ F h t hP hOrb
  obtain ⟨hF, hG, h0, h1, hbd, hdet, ht, hE0, hE1⟩ := hP
  obtain ⟨hb0, -, -, -⟩ := GlobalTheory.T.twisted_atlas_compatibility K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW x z₀ z₁ h0 h1
  obtain ⟨c, hc, hcz⟩ : SameOrbit z₁ z₀ := orbit_trans (orbit_trans h1 (orbit_symm hOrb)) (orbit_symm h0)
  have hz : ∀ q, z₁ q = c q.1 * z₀ q := fun q => congrFun hcz q

  have hbase : basePart M.blk z₁ = basePart M.blk z₀ := by
    funext q
    have e₀ : z₀ ⟨q.1.1, F.c q.1⟩ = 1 := (hE0 a).1 q.1
    have e₁ : z₁ ⟨q.1.1, F.c q.1⟩ = 1 := (hE1 a).1 q.1
    have hc1 : c q.1.1 = 1 := by
      have := hz ⟨q.1.1, F.c q.1⟩
      rw [e₀, e₁, mul_one] at this
      exact this.symm
    show z₁ ⟨q.1.1, q.2⟩ = z₀ ⟨q.1.1, q.2⟩
    rw [hz, show c (Sigma.fst (⟨q.1.1, q.2⟩ : Σ k, ι k)) = 1 from hc1, one_mul]
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    have hN := M.j_le
    have ha := a.2
    have hb' := b.2
    unfold lastCol at hca
    split_ifs at hca with hl <;> omega
  have hbd₁ : IsBlockDiag j (h * (1 + Matrix.single cb ca t)) := hbd.mul (isBlockDiag_one_add_single hs t)
  have hplk : ∀ m : ι k₀, plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ (h * (1 + Matrix.single cb ca t)) =
      c k₀ * plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ h := fun m => by
    have e₀ := (hE0 a).2 k₀ hk m
    have e₁ := (hE1 a).2 k₀ hk m
    rw [hbase] at e₁
    have e₂ := hz ⟨k₀, m⟩
    rw [e₁, e₀] at e₂
    exact e₂
  have hmin := Ind.minor_eq_of_plk M hb0 hF hG hk hbd₁ hbd hplk
  have hpl := GlobalTheory.T.elementary_twist_minor_scalar N j a b ca cb M.j_le hb hab hca hcb h 1 0 t (c k₀) hdet isBlockDiag_one
    Matrix.blockTriangular_one (fun I => by
      have e : (1 + Matrix.single cb ca (0 : ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by simp
      rw [e, Matrix.mul_one]
      exact hmin I)
  have h2 := hpl.2
  simp only [mul_zero, Matrix.one_apply_eq, mul_one, Finset.prod_const_one, one_mul] at h2
  exact ht h2.symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t → ¬ SameOrbit (fstPt k₀ (RW.lift x x)) (sndPt k₀ (RW.lift x x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.not_sameOrbit_of_ptData | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.not_sameOrbit_of_ptData | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.not_sameOrbit_of_ptData <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHolds
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree

section Transfer

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem modelChart_injOn (χ φ : OpenPartialHomeomorph X (Fin e → ℂ)) :
    Set.InjOn (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source) := by
  intro u hu u' hu' h
  have h1 : χ.symm u = χ.symm u' := φ.injOn hu.2 hu'.2 h
  have h2 := congrArg χ h1
  rwa [χ.right_inv hu.1, χ.right_inv hu'.1] at h2

theorem modelChart_null (χ φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : AnalyticOnNhd ℂ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source)) (E : Set X)
    (hE : volume (χ.target ∩ χ.symm ⁻¹' E) = 0) :
    volume (φ.target ∩ φ.symm ⁻¹' (E ∩ χ.source)) = 0 := by
  have hd : DifferentiableOn ℝ (φ ∘ χ.symm)
      (χ.target ∩ χ.symm ⁻¹' φ.source ∩ χ.symm ⁻¹' E) :=
    (hσ.differentiableOn.restrictScalars ℝ).mono Set.inter_subset_left
  have h0 : volume (χ.target ∩ χ.symm ⁻¹' φ.source ∩ χ.symm ⁻¹' E) = 0 :=
    measure_mono_null (t := χ.target ∩ χ.symm ⁻¹' E) (fun u hu => ⟨hu.1.1, hu.2⟩) hE
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd h0
  refine measure_mono_null ?_ himg
  rintro y ⟨hy, hyE, hyχ⟩
  refine ⟨χ (φ.symm y), ⟨⟨χ.map_source hyχ, ?_⟩, ?_⟩, ?_⟩
  · show χ.symm (χ (φ.symm y)) ∈ φ.source
    rw [χ.left_inv hyχ]; exact φ.map_target hy
  · show χ.symm (χ (φ.symm y)) ∈ E
    rw [χ.left_inv hyχ]; exact hyE
  · simp [χ.left_inv hyχ, φ.right_inv hy]

theorem modelChart_integrableOn (χ φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : AnalyticOnNhd ℂ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source)) (v : X → ℝ)
    (hv : ∀ Q ⊆ χ.target, IsCompact Q → IntegrableOn (fun y => v (χ.symm y)) Q)
    {Q : Set (Fin e → ℂ)} (hQ : IsCompact Q) (hQs : Q ⊆ φ.target ∩ φ.symm ⁻¹' χ.source) :
    IntegrableOn (fun y => v (φ.symm y)) Q := by
  have hSo : IsOpen (χ.target ∩ χ.symm ⁻¹' φ.source) :=
    χ.isOpen_inter_preimage_symm φ.open_source
  have hρc : ContinuousOn (χ ∘ φ.symm) Q :=
    χ.continuousOn.comp (φ.continuousOn_symm.mono fun y hy => (hQs hy).1) fun y hy => (hQs hy).2
  have hQ' : IsCompact ((χ ∘ φ.symm) '' Q) := hQ.image_of_continuousOn hρc
  have hQS : (χ ∘ φ.symm) '' Q ⊆ χ.target ∩ χ.symm ⁻¹' φ.source := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨χ.map_source (hQs hy).2, ?_⟩
    show χ.symm (χ (φ.symm y)) ∈ φ.source
    rw [χ.left_inv (hQs hy).2]; exact φ.map_target (hQs hy).1
  have himg : (φ ∘ χ.symm) '' ((χ ∘ φ.symm) '' Q) = Q := by
    rw [Set.image_image]
    refine Set.ext fun y => ⟨?_, fun hy => ⟨y, hy, ?_⟩⟩
    · rintro ⟨y', hy', rfl⟩
      simpa [χ.left_inv (hQs hy').2, φ.right_inv (hQs hy').1] using hy'
    · simp [χ.left_inv (hQs hy).2, φ.right_inv (hQs hy).1]
  have hσR : AnalyticOnNhd ℝ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source) :=
    hσ.restrictScalars
  have hder : ∀ u ∈ (χ ∘ φ.symm) '' Q,
      HasFDerivWithinAt (φ ∘ χ.symm) (fderiv ℝ (φ ∘ χ.symm) u) ((χ ∘ φ.symm) '' Q) u :=
    fun u hu => ((hσR u (hQS hu)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hinj : Set.InjOn (φ ∘ χ.symm) ((χ ∘ φ.symm) '' Q) := (modelChart_injOn χ φ).mono hQS
  have hcont : ContinuousOn (fun u => |(fderiv ℝ (φ ∘ χ.symm) u).det|) ((χ ∘ φ.symm) '' Q) := by
    have h1 : ContinuousOn (fderiv ℝ (φ ∘ χ.symm)) (χ.target ∩ χ.symm ⁻¹' φ.source) :=
      (hσR.fderiv).continuousOn
    exact (ContinuousLinearMap.continuous_det.comp_continuousOn (h1.mono hQS)).abs
  have hint := (hv _ (fun u hu => (hQS hu).1) hQ').continuousOn_mul hcont hQ'
  rw [← himg]
  refine (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hQ'.measurableSet hder
    hinj _).2 ?_
  refine hint.congr_fun (fun u hu => ?_) hQ'.measurableSet
  have hu := hQS hu
  simp only [smul_eq_mul, Function.comp_apply, φ.left_inv hu.2]

theorem modelChart_integrableOn_cover {n : ℕ} (χ : Fin n → OpenPartialHomeomorph X (Fin e → ℂ))
    (φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : ∀ k, AnalyticOnNhd ℂ (φ ∘ (χ k).symm) ((χ k).target ∩ (χ k).symm ⁻¹' φ.source))
    (hcov : ∀ x, ∃ k, x ∈ (χ k).source) (v : X → ℝ)
    (hv : ∀ k, ∀ Q ⊆ (χ k).target, IsCompact Q → IntegrableOn (fun y => v ((χ k).symm y)) Q) :
    LocallyIntegrableOn (fun y => v (φ.symm y)) φ.target := by
  intro y hy
  obtain ⟨k, hk⟩ := hcov (φ.symm y)
  have hWo : IsOpen (φ.target ∩ φ.symm ⁻¹' (χ k).source) :=
    φ.isOpen_inter_preimage_symm (χ k).open_source
  obtain ⟨Q, hQn, hQs, hQc⟩ := local_compact_nhds (hWo.mem_nhds ⟨hy, hk⟩)
  exact ⟨Q, mem_nhdsWithin_of_mem_nhds hQn, modelChart_integrableOn (χ k) φ (hσ k) v (hv k) hQc hQs⟩

theorem modelChart_null_cover {n : ℕ} (χ : Fin n → OpenPartialHomeomorph X (Fin e → ℂ))
    (φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : ∀ k, AnalyticOnNhd ℂ (φ ∘ (χ k).symm) ((χ k).target ∩ (χ k).symm ⁻¹' φ.source))
    (hcov : ∀ x, ∃ k, x ∈ (χ k).source) (E : Set X)
    (hE : ∀ k, volume ((χ k).target ∩ (χ k).symm ⁻¹' E) = 0) :
    volume (φ.target ∩ φ.symm ⁻¹' E) = 0 := by
  refine measure_mono_null (t := ⋃ k, φ.target ∩ φ.symm ⁻¹' (E ∩ (χ k).source)) ?_
    (measure_iUnion_null fun k => modelChart_null (χ k) φ (hσ k) E (hE k))
  rintro y ⟨hy, hyE⟩
  obtain ⟨k, hk⟩ := hcov (φ.symm y)
  exact Set.mem_iUnion.2 ⟨k, hy, hyE, hk⟩

end Transfer

theorem modelPtsIntegrable : ModelPtsIntegrable.Statement := by
  intro K _ ι _ P e M n ψ L c N E v g hV hL hN hψ hcov hE hv hg Ψ hΨ
  obtain ⟨Φ₀, hΦ₀, hloc⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K ι P e M L hL
  have hΦ : IsPotential M.atlas (Φ₀.rsmul c) := isPotentialRsmul M.atlas c Φ₀ hΦ₀
  have hli : ∀ j, LocallyIntegrableOn (fun y => v ((M.atlas.chart j).symm y))
      (M.atlas.chart j).target := fun j =>
    modelChart_integrableOn_cover ψ (M.atlas.chart j) (fun k => (hψ k j).2) hcov v hv
  have hint : ∀ j, ∀ Q ⊆ (M.atlas.chart j).target, IsCompact Q →
      IntegrableOn (fun y => v ((M.atlas.chart j).symm y)) Q := fun j Q hQ hQc =>
    (hli j).integrableOn_compact_subset hQ hQc
  have hnull : ∀ j, volume ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' ((Set.univ : Set M.Xc)ᶜ ∪ E)) = 0 := fun j => by
    simpa using modelChart_null_cover ψ (M.atlas.chart j) (fun k => (hψ k j).2) hcov E hE
  have hMI : MIntegrable M.atlas (fun _ : Fin e => Φ₀.rsmul c) v := fun j Q hQ hQc =>
    (hint j Q hQ hQc).mul_continuousOn
      ((locDensCont M.atlas _ (fun _ => hΦ) j).mono hQ) hQc
  refine ((GlobalTheory.T.mixed_integral_model_formula K ι P e M Ψ Set.univ E N (fun _ => c) (fun _ => L)
    (fun _ => Φ₀.rsmul c) g v hV hΨ isOpen_univ hnull hN ?_ ?_ ?_ ?_).2.2 hMI).1
  · exact fun _ x j => (hΦ.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · intro _ x y₀ hy₀
    obtain ⟨U, hUo, hyU, hUs, s, hs, hsh, G, hG, hGe⟩ := hloc x y₀ hy₀
    refine ⟨U, hUo, hyU, hUs, s, hs, hsh, fun z => (c : ℂ) * G z, holoOn_mul M.atlas hG c,
      fun y' hy' => ?_⟩
    have h1 : Φ₀.φ x y' - Real.log (L.h (s y')) = (G y').re := hGe y' hy'
    show c * Φ₀.φ x y' - c * Real.log (L.h (s y')) = ((c : ℂ) * G y').re
    rw [Complex.re_ofReal_mul, ← h1]
    ring
  · exact fun z hz hzN _ hzE => hg z hz hzN hzE
  · exact fun j => (hli j).aestronglyMeasurable

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_points_integrable_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.ModelPtsIntegrable.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.modelPtsIntegrable | exact GlobalTheory.CompanionTheory.Ar.Giv.modelPtsIntegrable | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.modelPtsIntegrable <;> assumption)
end
end
