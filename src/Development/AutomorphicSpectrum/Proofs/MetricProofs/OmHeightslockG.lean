module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSnc
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreMult
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQContinuousAtAndLocalSolution

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

def blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
  (Matrix.fromBlocks (omBlock Γ)ᵀ⁻¹ 0 0 (wBlock Γ)).submatrix (blockEquiv p q).symm (blockEquiv p q).symm

theorem wBlock_blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : wBlock (blockG Γ) = wBlock Γ := by
  ext a b
  simp [wBlock, blockG, ← blockEquiv_inr]

theorem omBlock_blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    omBlock (blockG Γ) = (omBlock Γ)ᵀ⁻¹ := by
  ext a b
  simp [omBlock, blockG, ← blockEquiv_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}


open Classical in
def dualFam (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin D.q → 𝔐.Vgen (.inr τ) :=
  if h : ∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0 then h.choose
  else 0

theorem wFrame_mem (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (a : Fin D.p) : tie.wFrame F τ a ∈ 𝔐.Vgen (.inl τ) := by
  unfold FlagTie.wFrame colFrame
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (tie.eW τ b).2

def gbS (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin (D.p + D.q) → ↥(𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)) := fun i =>
  Sum.elim (fun a => ⟨(dualFam tie F τ a : 𝔐.Li), Submodule.mem_sup_right (dualFam tie F τ a).2⟩)
    (fun a => ⟨tie.wFrame F τ a, Submodule.mem_sup_left (wFrame_mem tie F τ a)⟩) ((blockEquiv D.p D.q).symm i)

def gb (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin (D.p + D.q) → 𝔐.Li := fun i => (gbS tie F τ i : 𝔐.Li)

def baseGram (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) {n : ℕ}
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (x : Rb.X) : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ :=
  HodgeMetric.gramFn 𝔐 (gb tie F τ) (Rb.lift x x)

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositive
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositive
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace PosFs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fsHerm_one_h (y : (Σ k, ι k) → ℂ) :
    (fsHerm ι fun _ => 1).h y = (GroundTheory.Heights₂.Heights.fsMulti ι).h y := by
  rw [fsHerm_h]
  unfold refNorm
  simp only [GroundTheory.Heights₂.Heights.fsMulti, HermLine.ofMetrics, zpow_one]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ‖WithLp.toLp 2 (fun i => y ⟨k, i⟩)‖
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
  norm_num

theorem levi_fs_pos {z w : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    0 < levi (fun y => Real.log ((fsHerm ι fun _ => 1).h y)) z w := by
  have h := GlobalTheory.CompanionTheory.Ar.FS.levi_fsMulti_pos hz hw
  have e : (fun y => Real.log ((fsHerm ι fun _ => 1).h y)) =
      fun y => Real.log ((GroundTheory.Heights₂.Heights.fsMulti ι).h y) := by
    funext y
    rw [fsHerm_one_h]
  rw [e]
  exact h

theorem contDiffAt_log_h {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have hopen : ∀ᶠ y in 𝓝 z, ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    refine Filter.eventually_all.mpr fun k => ?_
    obtain ⟨i, hi⟩ := hz k
    exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
      fun y hy => ⟨i, hy⟩
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h z := hA.contDiffAt hopen
  exact (h1.of_le (by first | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | (rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) by norm_cast]; exact WithTop.coe_le_coe.2 le_top))).log (A.pos z hz).ne'

theorem fderiv_affCoord_torus {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {γ : E → (Σ k, ι k) → ℂ} {y : E} (p : (k : K) → ι k) (hγ : DifferentiableAt ℂ γ y)
    (hp : ∀ k, γ y ⟨k, p k⟩ ≠ 0) {w : E} {c : K → ℂ} (hc : fderiv ℂ γ y w = torusSmul c (γ y)) :
    fderiv ℂ (fun y' => affCoord p (γ y')) y w = 0 := by
  have hd := hγ.hasFDerivAt
  have hq : ∀ q : Σ k, ι k, HasFDerivAt (fun y' => γ y' q)
      ((ContinuousLinearMap.proj q).comp (fderiv ℂ γ y)) y := fun q => hasFDerivAt_pi'.1 hd q
  have hu : ∀ q : Σ k, ι k, HasFDerivAt (fun y' => affCoord p (γ y') q)
      ((γ y q) • ((-((γ y ⟨q.1, p q.1⟩) ^ 2)⁻¹) •
          ((ContinuousLinearMap.proj ⟨q.1, p q.1⟩).comp (fderiv ℂ γ y))) +
        ((γ y ⟨q.1, p q.1⟩)⁻¹) • ((ContinuousLinearMap.proj q).comp (fderiv ℂ γ y))) y := by
    intro q
    have hinv := (hasDerivAt_inv (hp q.1)).comp_hasFDerivAt y (hq ⟨q.1, p q.1⟩)
    have hm := (hq q).mul hinv
    refine hm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y' => ?_)
    simp [affCoord, div_eq_mul_inv]
  have hall : fderiv ℂ (fun y' => affCoord p (γ y')) y = ContinuousLinearMap.pi _ :=
    (hasFDerivAt_pi.2 hu).fderiv
  rw [hall]
  funext q
  have h1 : fderiv ℂ γ y w q = c q.1 * γ y q := congrFun hc q
  have h2 : fderiv ℂ γ y w ⟨q.1, p q.1⟩ = c q.1 * γ y ⟨q.1, p q.1⟩ := congrFun hc _
  have hr := hp q.1
  simp only [ContinuousLinearMap.coe_pi', ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    h1, h2, smul_eq_mul, Pi.zero_apply]
  field_simp
  ring

theorem isPosPot_fs (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D) :
    IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) := by
  classical
  intro x j y hy w hw
  obtain ⟨hyt, hyU⟩ := hy
  have hx₀ : (R.A.chart j).symm y ∈ (R.A.chart j).source := (R.A.chart j).map_target hyt
  have hex₀ : R.A.chart j ((R.A.chart j).symm y) = y := (R.A.chart j).right_inv hyt
  have hxU : (R.A.chart j).symm y ∈ R.U x := hyU
  let γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y')
  have hγ : AnalyticAt ℂ γ y := analyticAt_pi_iff.2 fun q => R.holo x q j y ⟨hyt, hyU⟩
  have hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := (R.mem x _ hxU).1
  have hc2 := contDiffAt_log_h (GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm K ι fun _ => 1) hz
  have heq : levi ((potOf R (fsHerm ι fun _ => 1)).φ x ∘ (R.A.chart j).symm) y w =
      levi (fun z => Real.log ((fsHerm ι fun _ => 1).h z)) (γ y) (fderiv ℂ γ y w) :=
    levi_comp w hγ hc2
  rw [heq]
  refine levi_fs_pos hz fun c hc => hw ?_
  choose p hp using (R.mem _ _ (R.mem_U ((R.A.chart j).symm y))).1
  have hnot : R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y) ∉ mcPts (⊤ : Ideal (MRing ι)) := by
    intro h
    have := h.2 1 trivial
    simp at this
  have himm := R.immersion _ hnot p hp j hx₀
  rw [hex₀] at himm
  have hev : (fun y' => affCoord p (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y'))) =ᶠ[𝓝 y]
      fun y' => affCoord p (γ y') := by
    have hmem : (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U ((R.A.chart j).symm y)) ∈ 𝓝 y :=
      ((R.A.chart j).continuousAt_symm hyt).preimage_mem_nhds
        (((R.isOpen_U x).inter (R.isOpen_U _)).mem_nhds ⟨hxU, R.mem_U _⟩)
    filter_upwards [hmem] with y' hy'
    obtain ⟨c', hc', h⟩ := R.compat _ x _ ⟨hy'.2, hy'.1⟩
    funext q
    simp only [affCoord, γ]
    rw [h]
    exact mul_div_mul_left _ _ (hc' q.1)
  rw [hev.fderiv_eq] at himm
  have hpγ : ∀ k, γ y ⟨k, p k⟩ ≠ 0 := by
    intro k
    obtain ⟨c', hc', h⟩ := R.compat _ x _ ⟨R.mem_U _, hxU⟩
    have := hp k
    rw [h] at this
    exact right_ne_zero_of_mul this
  have hk := fderiv_affCoord_torus p hγ.differentiableAt hpγ hc
  have hmem : w ∈ (fderiv ℂ (fun y' => affCoord p (γ y')) y).ker := hk
  rw [himm] at hmem
  exact (Submodule.mem_bot _).1 hmem

end PosFs

theorem fs_pos_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D), (∀ A : HermLine ι, IsSmoothHerm A → IsPotential R.A (potOf R A)) ∧ IsSmoothHerm (fsHerm ι fun _ => 1) ∧ IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) :=
  fun K _ ι _ P D R => ⟨fun _ hA => isPotential_potOf R hA,
    GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm K ι _, PosFs.isPosPot_fs P D R⟩

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositiveStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_fubini_study_positive : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D), (∀ A : HermLine ι, IsSmoothHerm A → IsPotential R.A (potOf R A)) ∧ IsSmoothHerm (fsHerm ι fun _ => 1) ∧ IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential | exact GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv.ProjF

open GroundTheory.Heights₂.Heights

theorem pfIntZero : Inter.PFIntZero.Statement :=
  Inter.PFIntZero.proof (Inter.pointFormRank_holds.proof Inter.RatioAlgDep.proof)

theorem pfVert : Inter.PFVert.Statement :=
  Inter.PFVert.proof (by intros; exact geoNumStatement _) (by intros; exact Targets.ExistsUnique.full _ _)
    Targets.contractMixedField

theorem contractMixed : ContractMixedStatement :=
  Targets.ContractMixed.of_found imageArith Targets.Contract.pulledBackForms_topDensity_vanish
    (Inter.ProjectivePointVertical.proof (by intros; exact geoNumStatement _) (by intros; exact Targets.ExistsUnique.full _ _)
      (by intros; exact Targets.ProjContract.full _ _ _ _ _))
    pfIntZero pfVert

theorem pfStep : Inter.PFStep.Statement :=
  Inter.PFStep.proof (Inter.PFSecRed.proof (by intros; exact Targets.Multilin.full _ _) GlobalTheory.CompanionTheory.Ar.Giv.fibreDim) pfVert pfIntZero
    Inter.PFHoriz.proof (Inter.PFFibreSum.proof GlobalTheory.CompanionTheory.Ar.Giv.fibreDim Inter.PFFibreBij.proof Inter.PFFibreMult.proof)
    imageArith contractMixed

theorem projFormula : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFStatement := fun h =>
  Inter.PushforwardProjLineFlag.proof (GlobalTheory.T.generic_degree_of_arith_system h) pfStep

end GlobalTheory.CompanionTheory.Ar.Giv.ProjF
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystemStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_formula_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula | exact GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivialization
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivialization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem exists_analytic_param {A B E : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Φ : E → A} {G : A → B} {e₀ : E}
    (hΦ : AnalyticAt ℂ Φ e₀) (hG : AnalyticAt ℂ G (Φ e₀))
    (hinj : ∀ e, fderiv ℂ Φ e₀ e = 0 → e = 0)
    (hker : ∀ w, fderiv ℂ G (Φ e₀) w = 0 → ∃ e, w = fderiv ℂ Φ e₀ e)
    (hzero : ∀ᶠ e in 𝓝 e₀, G (Φ e) = 0) {U : Set E} (hU : U ∈ 𝓝 e₀) :
    ∃ (V : Set A) (S : A → E), IsOpen V ∧ Φ e₀ ∈ V ∧ AnalyticOnNhd ℂ S V ∧ S (Φ e₀) = e₀ ∧
      ∀ z ∈ V, G z = 0 → S z ∈ U ∧ z = Φ (S z) := by
  set L := fderiv ℂ Φ e₀ with hL
  have hLi : LinearMap.ker (L : E →ₗ[ℂ] A) = ⊥ := LinearMap.ker_eq_bot'.mpr hinj
  obtain ⟨p, hp⟩ := (L : E →ₗ[ℂ] A).exists_leftInverse_of_injective hLi
  let π : A →L[ℂ] E := LinearMap.toContinuousLinearMap p
  have hπ : ∀ e, π (L e) = e := fun e => LinearMap.congr_fun hp e

  let h : E → E := fun e => π (Φ e)
  have hh : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) e₀ := by
    have h1 := π.hasStrictFDerivAt.comp e₀ hΦ.hasStrictFDerivAt
    refine h1.congr_fderiv ?_
    ext e
    simp [hπ, ← hL]
  let Φ₁ := hh.toOpenPartialHomeomorph h
  have hΦ₁ : ∀ e, Φ₁ e = π (Φ e) := fun e => rfl
  have hs₁ : e₀ ∈ Φ₁.source := hh.mem_toOpenPartialHomeomorph_source
  have han₁ : AnalyticAt ℂ Φ₁ e₀ := (π.analyticAt _).comp hΦ
  have hsymm : AnalyticAt ℂ Φ₁.symm (Φ₁ e₀) :=
    Φ₁.analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E) hs₁ han₁ hh.hasFDerivAt.fderiv
  have hback : Φ₁.symm (Φ₁ e₀) = e₀ := Φ₁.left_inv hs₁

  let M : A →L[ℂ] B × E := (fderiv ℂ G (Φ e₀)).prod π
  have hMi : LinearMap.ker (M : A →ₗ[ℂ] B × E) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun w hw => ?_
    have h1 : fderiv ℂ G (Φ e₀) w = 0 := congrArg Prod.fst hw
    have h2 : π w = 0 := congrArg Prod.snd hw
    obtain ⟨e, rfl⟩ := hker w h1
    rw [hπ] at h2
    rw [h2, map_zero]
  obtain ⟨q, hq⟩ := (M : A →ₗ[ℂ] B × E).exists_leftInverse_of_injective hMi
  let R : B × E →L[ℂ] A := LinearMap.toContinuousLinearMap q
  have hR : ∀ w, R (M w) = w := fun w => LinearMap.congr_fun hq w
  let Ξ : A → A := fun z => R (G z, π z)
  have hΞ : HasStrictFDerivAt Ξ ((ContinuousLinearEquiv.refl ℂ A : A ≃L[ℂ] A) : A →L[ℂ] A) (Φ e₀) := by
    have h1 := R.hasStrictFDerivAt.comp (Φ e₀) (hG.hasStrictFDerivAt.prodMk π.hasStrictFDerivAt)
    refine h1.congr_fderiv ?_
    ext w
    exact hR w
  let Φ₂ := hΞ.toOpenPartialHomeomorph Ξ
  have hs₂ : Φ e₀ ∈ Φ₂.source := hΞ.mem_toOpenPartialHomeomorph_source

  have hN : ∀ᶠ e in 𝓝 e₀, e ∈ U ∧ G (Φ e) = 0 ∧ Φ e ∈ Φ₂.source :=
    (Filter.eventually_of_mem hU fun _ h => h).and (hzero.and
      (hΦ.continuousAt.eventually_mem (Φ₂.open_source.mem_nhds hs₂)))
  have hc₁ : ContinuousAt Φ₁.symm (Φ₁ e₀) := hsymm.continuousAt
  have hN' : ∀ᶠ x in 𝓝 (Φ₁ e₀), Φ₁.symm x ∈ U ∧ G (Φ (Φ₁.symm x)) = 0 ∧ Φ (Φ₁.symm x) ∈ Φ₂.source := by
    have := hc₁.tendsto.eventually (by rw [hback]; exact hN)
    exact this
  have ht₁ : Φ₁ e₀ ∈ Φ₁.target := Φ₁.map_source hs₁
  have hP : ∀ᶠ x in 𝓝 (Φ₁ e₀), (Φ₁.symm x ∈ U ∧ G (Φ (Φ₁.symm x)) = 0 ∧ Φ (Φ₁.symm x) ∈ Φ₂.source) ∧
      x ∈ Φ₁.target ∧ AnalyticAt ℂ Φ₁.symm x :=
    hN'.and ((Φ₁.open_target.mem_nhds ht₁ |> Filter.eventually_of_mem <| fun _ h => h).and hsymm.eventually_analyticAt)
  have hπc : Tendsto π (𝓝 (Φ e₀)) (𝓝 (Φ₁ e₀)) := π.continuous.tendsto _
  have hQ : ∀ᶠ z in 𝓝 (Φ e₀), ((Φ₁.symm (π z) ∈ U ∧ G (Φ (Φ₁.symm (π z))) = 0 ∧ Φ (Φ₁.symm (π z)) ∈ Φ₂.source) ∧
      π z ∈ Φ₁.target ∧ AnalyticAt ℂ Φ₁.symm (π z)) ∧ z ∈ Φ₂.source :=
    (hπc.eventually hP).and (Φ₂.open_source.mem_nhds hs₂ |> Filter.eventually_of_mem <| fun _ h => h)
  obtain ⟨V, hVs, hVo, hV0⟩ := mem_nhds_iff.mp hQ
  refine ⟨V, fun z => Φ₁.symm (π z), hVo, hV0, ?_, hback, ?_⟩
  · intro z hz
    exact AnalyticAt.comp (f := fun z => π z) (hVs hz).1.2.2 (π.analyticAt z)
  · intro z hz hGz
    obtain ⟨⟨⟨hU', hG', hsrc⟩, htgt, -⟩, hzs⟩ := hVs hz
    refine ⟨hU', ?_⟩
    have h1 : π (Φ (Φ₁.symm (π z))) = π z := Φ₁.right_inv htgt
    refine Φ₂.injOn hzs hsrc ?_
    show R (G z, π z) = R (G _, π _)
    rw [hGz, hG', h1]


open MvPolynomial in
theorem exists_chart_inverse {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}
    (hP : IsMultiHomogIdeal P) {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) {t₀ : Fin n → ℂ}
    (ht₀ : t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1)
    (htan : ∀ v, IsConeTangent (Int.castRingHom ℂ) P (χ.γ t₀) v →
      ∃ (u : Fin n → ℂ) (c : K → ℂ), v = fderiv ℂ χ.γ t₀ u + torusSmul c (χ.γ t₀)) :
    ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin n → ℂ), IsOpen V ∧ χ.γ t₀ ∈ V ∧
      AnalyticOnNhd ℂ T V ∧ T (χ.γ t₀) = t₀ ∧ ∀ z ∈ V ∩ mcPts P, T z ∈ Metric.ball 0 1 ∧
        ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (χ.γ (T z)) := by
  classical
  set z₀ := χ.γ t₀ with hz₀
  let σ : ℤ →+* ℂ := Int.castRingHom ℂ

  let ell : MRing J → Module.Dual ℂ ((Σ k, J k) → ℂ) := fun f =>
    ∑ i, eval z₀ (pderiv i (map σ f)) • LinearMap.proj i
  have hell : ∀ f w, ell f w = ∑ i, eval z₀ (pderiv i (map σ f)) * w i := fun f w => by
    simp [ell, LinearMap.sum_apply]
  obtain ⟨s, hsub, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (ell '' (P : Set (MRing J)))).1
    (IsNoetherian.noetherian (Submodule.span ℂ (ell '' (P : Set (MRing J)))))
  have hch : ∀ l : s, ∃ f ∈ P, ell f = l.1 := fun l => by
    obtain ⟨f, hf, h⟩ := hsub l.2
    exact ⟨f, hf, h⟩
  choose f hfP hfl using hch
  let g : s → MvPolynomial (Σ k, J k) ℂ := fun l => map σ (f l)
  let G : ((Σ k, J k) → ℂ) → s → ℂ := fun z l => eval z (g l)
  let Φ : (K → ℂ) × (Fin n → ℂ) → (Σ k, J k) → ℂ := fun e => torusSmul e.1 (χ.γ e.2)
  let e₀ : (K → ℂ) × (Fin n → ℂ) := (1, t₀)
  have hΦ₀ : Φ e₀ = z₀ := by
    funext p
    simp [Φ, e₀, torusSmul, hz₀]
  have hγ : AnalyticAt ℂ χ.γ t₀ := χ.analytic t₀ ht₀
  have hΦan : AnalyticAt ℂ Φ e₀ := by
    refine AnalyticAt.pi fun p => ?_
    have h1 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 p.1) e₀ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
        (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))).analyticAt e₀
    have h2 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2) e₀ :=
      AnalyticAt.comp (f := fun e : (K → ℂ) × (Fin n → ℂ) => e.2) hγ
        ((ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).analyticAt e₀)
    have h3 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2 p) e₀ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).analyticAt _).comp h2
    exact h1.mul h3
  have hGan : AnalyticAt ℂ G (Φ e₀) := by
    refine AnalyticAt.pi fun l => ?_
    exact AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (g l) _ (Set.mem_univ _)

  have hdΦ : ∀ c u, fderiv ℂ Φ e₀ (c, u) = fderiv ℂ χ.γ t₀ u + torusSmul c z₀ := by
    have hγd := hγ.differentiableAt.hasFDerivAt
    have hD : HasFDerivAt Φ (ContinuousLinearMap.pi fun p : (Σ k, J k) =>
        (1 : ℂ) • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).comp
            ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)))) +
          z₀ p • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ)))) e₀ := by
      refine hasFDerivAt_pi.2 fun p => ?_
      have h1 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 p.1)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))) e₀ :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))).hasFDerivAt
      have h2 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2)
          ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ))) e₀ :=
        HasFDerivAt.comp e₀ (f := fun e : (K → ℂ) × (Fin n → ℂ) => e.2) hγd
          (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).hasFDerivAt
      have h3 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2 p)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).comp
            ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)))) e₀ :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).hasFDerivAt.comp e₀ h2
      refine (h1.mul h3).congr_fderiv ?_
      simp [e₀, hz₀]
    intro c u
    rw [hD.fderiv]
    funext p
    simp [torusSmul, mul_comm]

  have hdG : ∀ w l, fderiv ℂ G (Φ e₀) w l = ell (f l) w := by
    have hD : HasFDerivAt G (ContinuousLinearMap.pi fun l : s =>
        ∑ i, eval (Φ e₀) (pderiv i (g l)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) i)
        (Φ e₀) := hasFDerivAt_pi.2 fun l => hasFDerivAt_eval (g l) (Φ e₀)
    intro w l
    rw [hD.fderiv, hell, hΦ₀]
    simp [g]
  have hinj : ∀ e, fderiv ℂ Φ e₀ e = 0 → e = 0 := by
    rintro ⟨c, u⟩ h
    rw [hdΦ] at h
    have hu : u = 0 := by
      refine χ.immersion t₀ ht₀ u ⟨fun k => - c k, ?_⟩
      funext p
      have := congrFun h p
      simp only [Pi.add_apply, Pi.zero_apply, torusSmul] at this ⊢
      rw [← hz₀]
      linear_combination this
    subst hu
    have hc : c = 0 := by
      funext k
      obtain ⟨i, hi⟩ := (χ.mem t₀ ht₀).1 k
      have := congrFun h ⟨k, i⟩
      simp only [map_zero, Pi.add_apply, Pi.zero_apply, zero_add, torusSmul] at this
      exact (mul_eq_zero.mp this).resolve_right hi
    simp [hc]
  have hker : ∀ w, fderiv ℂ G (Φ e₀) w = 0 → ∃ e, w = fderiv ℂ Φ e₀ e := by
    intro w hw
    have hs0 : ∀ l ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ ((Σ k, J k) → ℂ))), l w = 0 := by
      intro l hl
      induction hl using Submodule.span_induction with
      | mem x hx =>
        have := congrFun hw ⟨x, hx⟩
        rw [hdG, hfl] at this
        exact this
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => simp [hx]
    have htv : IsConeTangent (Int.castRingHom ℂ) P z₀ w := by
      intro q hq
      have : ell q ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ ((Σ k, J k) → ℂ))) := by
        rw [← hspan]
        exact Submodule.subset_span ⟨q, hq, rfl⟩
      have h0 := hs0 _ this
      rw [hell] at h0
      exact h0
    obtain ⟨u, c, hv⟩ := htan w htv
    exact ⟨(c, u), by rw [hdΦ, hv]⟩
  have hopen : ∀ᶠ e : (K → ℂ) × (Fin n → ℂ) in 𝓝 e₀, (∀ k, e.1 k ≠ 0) ∧ e.2 ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    refine Filter.Eventually.and (eventually_all.2 fun k => ?_) ?_
    · have hc : ContinuousAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 k) e₀ := by fun_prop
      exact hc.eventually_ne (by simp [e₀])
    · have hc : ContinuousAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.2) e₀ := by fun_prop
      exact hc.eventually_mem (Metric.isOpen_ball.mem_nhds ht₀)
  have hzero : ∀ᶠ e in 𝓝 e₀, G (Φ e) = 0 := by
    filter_upwards [hopen] with e he
    funext l
    exact (mcPts_smul hP e.1 he.1 (χ.mem e.2 he.2)).2 (f l) (hfP l)
  obtain ⟨V, S, hVo, hV0, hSan, hS0, hS⟩ := exists_analytic_param hΦan hGan hinj hker hzero hopen
  rw [hΦ₀] at hV0 hS0
  refine ⟨V, fun z => (S z).2, hVo, hV0, ?_, by simp [hS0, e₀], ?_⟩
  · intro z hz
    exact ((ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).analyticAt _).comp (hSan z hz)
  · rintro z ⟨hzV, hzP⟩
    have hGz : G z = 0 := by
      funext l
      exact hzP.2 (f l) (hfP l)
    obtain ⟨hU, hz⟩ := hS z hzV hGz
    exact ⟨hU.2, (S z).1, hU.1, hz⟩

theorem chart_torus_open : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts), ∀ t₀ ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), IsOpen V ∧ (D.chart a).γ t₀ ∈ V ∧ AnalyticOnNhd ℂ T V ∧ T ((D.chart a).γ t₀) = t₀ ∧ ∀ z ∈ V ∩ mcPts (mCoordIdeal D.y), T z ∈ Metric.ball 0 1 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((D.chart a).γ (T z)) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D a t₀ ht₀
  exact exists_chart_inverse D.arith.2.1.2.1 (D.chart a) ht₀
    (GlobalTheory.T.cone_tangent_lift_in_chart K J II Ψ Ω W D a t₀ ht₀)

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivializationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_local_analytic_trivialization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts), ∀ t₀ ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), IsOpen V ∧ (D.chart a).γ t₀ ∈ V ∧ AnalyticOnNhd ℂ T V ∧ T ((D.chart a).γ t₀) = t₀ ∧ ∀ z ∈ V ∩ mcPts (mCoordIdeal D.y), T z ∈ Metric.ball 0 1 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((D.chart a).γ (T z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.chart_torus_open | exact GlobalTheory.CompanionTheory.Ar.Cusp.chart_torus_open | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.chart_torus_open <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp


open MuRegSmooth TopNPoly in
theorem muReg_smooth_log : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ), S.IsTied → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg Hd S B t) ∧ (muReg Hd S B t).a = muTwDeg Hd B ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muReg Hd S B t).h z) = Real.log (S.ref.h z) + S.regWeight t (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B hS
  have hP : ProjSmoothAlong.Statement := ProjSmoothAlong.proof HoloInjDerivInj.proof GlobalTheory.T.local_orbit_chart_statement_holds
  have hVS : VertFactorSmooth.Statement := VertFactorSmooth.proof VertFactorPos.proof
  have hSB : ∀ p ∈ D.SB B, p ∈ D.S := fun p hp => (Finset.mem_filter.1 hp).1
  filter_upwards [regWeight_smooth S hS] with t ht
  have hPm : IsMultiHomogIdeal (mCoordIdeal D.y) := D.arith.2.1.2.1
  set F : ((Σ k, J k) → ℂ) → ℝ := fun z =>
    S.ref.h z * Real.exp (S.regWeight t (M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z with hFdef
  have hvpos : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ p ∈ D.SB B, 0 < D.vertFactor p z := fun z hz p hp =>
    VertFactorPos.proof II Ψ K J Ω W D p (hSB p hp) z hz
  have hpos : ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < F z := fun z hz =>
    mul_pos (mul_pos (S.ref.pos z hz.1) (Real.exp_pos _)) (Finset.prod_pos (hvpos z hz))
  have hhom : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ muTwDeg Hd B k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts (mCoordIdeal D.y) := mcPts_smul hPm c hc hz
    have hproj : M.proj (torusSmul c z) = M.proj z := ((M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ Hd.aMu k) * S.ref.h z := by
      rw [show torusSmul c z = fun p => c p.1 * z p from rfl, S.ref.smul c z hc, S.ref_deg]
      rfl
    have hvf : ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
        (∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k) * ∏ p ∈ D.SB B, D.vertFactor p z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p hp => (hVS II Ψ K J Ω W D p (hSB p hp)).1 z hz c hc
    simp only [hFdef]
    rw [href, hproj, hvf, muTwDeg, prod_norm_zpow_add_sum hc]
    ring
  have hsm : SmoothAlong (mcPts (mCoordIdeal D.y)) F :=
    smoothAlong_mul (smoothAlong_mul (smoothAlong_of_contDiffOn S.ref_smooth)
      (smoothAlong_exp (hP II Ψ K J Ω W D M _ ht)))
      (smoothAlong_prod _ fun p hp => (hVS II Ψ K J Ω W D p (hSB p hp)).2)
  obtain ⟨Z, hZa, hZs, hZh⟩ := HermExtend.proof K J (mCoordIdeal D.y) (muTwDeg Hd B) F hPm hpos hhom hsm
  have hagree : ∀ z ∈ mcPts (mCoordIdeal D.y), Z.h z =
      (hermOfFun J (muTwDeg Hd B) fun z => (S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z).h z := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
    have hw0 := orbitRep_blocks hz.1
    have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
      have h := mcPts_smul hPm (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
      convert h using 1
      funext p
      have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
      rw [hp, ← _root_.mul_assoc, inv_mul_cancel₀ (hc _), _root_.one_mul]
    have hG0 : 0 < S.ref.h (orbitRep z) * Real.exp (S.regWeight t (M.proj (orbitRep z))) :=
      mul_pos (S.ref.pos _ hw0) (Real.exp_pos _)
    have hreg : (S.regLine t).h (orbitRep z) =
        S.ref.h (orbitRep z) * Real.exp (S.regWeight t (M.proj (orbitRep z))) :=
      hermOfFun_h_orbitRep hz.1 hG0
    have hFw : (S.regLine t).h (orbitRep z) * ∏ p ∈ D.SB B, D.vertFactor p (orbitRep z) = F (orbitRep z) := by
      rw [hreg]
    rw [hZh z hz, hermOfFun_h_smul hc hzc hz.1 (by rw [hFw]; exact hpos _ hwP), hFw]
    conv_lhs => rw [hzc]
    exact hhom _ hwP c hc
  refine ⟨?_, smoothRep_a _ _, fun z hz => ?_⟩
  · unfold muReg
    exact smoothRep_smooth_of (Z := Z) hZa hZs hagree
  · have hmu : (muReg Hd S B t).h z = F z := by
      unfold muReg
      rw [smoothRep_h _ hz, ← hagree z hz, hZh z hz]
    have h1 : S.ref.h z ≠ 0 := (S.ref.pos z hz.1).ne'
    have h2 : ∏ p ∈ D.SB B, D.vertFactor p z ≠ 0 := (Finset.prod_pos (hvpos z hz)).ne'
    rw [hmu]
    simp only [hFdef]
    rw [Real.log_mul (mul_ne_zero h1 (Real.exp_pos _).ne') h2, Real.log_mul h1 (Real.exp_pos _).ne',
      Real.log_exp, Real.log_prod fun p hp => (hvpos z hz p hp).ne']

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmoothStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_hodge_metric_smooth : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ), S.IsTied → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg Hd S B t) ∧ (muReg Hd S B t).a = muTwDeg Hd B ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muReg Hd S B t).h z) = Real.log (S.ref.h z) + S.regWeight t (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log | exact GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalHodgeMetricLogFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalHodgeMetricLogFormula
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

private theorem zpow_finset_sum_divisor {α : Type*} (s : Finset α) (f : α → ℤ) {x : ℝ} (hx : x ≠ 0) :
    x ^ (∑ p ∈ s, f p) = ∏ p ∈ s, x ^ f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]

theorem log_muVert_h_of_mem : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (B : ℕ), ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muVert Hd B).h z) = Real.log ((muLine Hd).h z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd B z hz
  have hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal D.y) := D.arith.2.1.2.1
  have hpos := GroundTheory.Heights₂.Heights.LowerBoundFree.VertFactorPos.proof
  have hsmooth := GroundTheory.Heights₂.Heights.LowerBoundFree.VertFactorSmooth.proof hpos
  have hSB : ∀ p ∈ D.SB B, p ∈ D.S := fun p hp => (Finset.mem_filter.mp hp).1
  have hnz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz.1
  have hLpos : 0 < (muLine Hd).h z := (muLine Hd).pos z hnz
  have hVpos : ∀ p ∈ D.SB B, 0 < D.vertFactor p z := fun p hp => hpos II Ψ K J Ω W D p (hSB p hp) z hz
  have hPpos : 0 < ∏ p ∈ D.SB B, D.vertFactor p z := Finset.prod_pos hVpos
  have hF : (muVert Hd B).h z = (muLine Hd).h z * ∏ p ∈ D.SB B, D.vertFactor p z := by
    unfold muVert
    refine GroundTheory.Heights₂.Heights.LowerBoundFree.NbarSmooth.hermOfFun_h_of_mem hP ?_ hz (mul_pos hLpos hPpos)
    intro w hw c hc
    have hc' : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have h1 : (muLine Hd).h (torusSmul c w) = (∏ k, ‖c k‖ ^ Hd.aMu k) * (muLine Hd).h w :=
      (muLine Hd).smul c w hc
    have h2 : ∀ p ∈ D.SB B, D.vertFactor p (torusSmul c w) =
        (∏ k, ‖c k‖ ^ D.vdeg p k) * D.vertFactor p w :=
      fun p hp => (hsmooth II Ψ K J Ω W D p (hSB p hp)).1 w hw c hc
    have h3 : ∏ k, ‖c k‖ ^ muTwDeg Hd B k =
        (∏ k, ‖c k‖ ^ Hd.aMu k) * ∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k := by
      rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only [muTwDeg, Pi.add_apply, Finset.sum_apply]
      rw [zpow_add₀ (hc' k), zpow_finset_sum_divisor _ _ (hc' k)]
    rw [h1, Finset.prod_congr rfl h2, Finset.prod_mul_distrib, h3]
    ring
  rw [hF, Real.log_mul hLpos.ne' hPpos.ne', Real.log_prod fun p hp => (hVpos p hp).ne']

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalHodgeMetricLogFormulaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_hodge_metric_log_formula : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (B : ℕ), ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muVert Hd B).h z) = Real.log ((muLine Hd).h z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.log_muVert_h_of_mem | exact GlobalTheory.CompanionTheory.Ar.Cusp.log_muVert_h_of_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.log_muVert_h_of_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSixth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSixth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem continuousWithinAt_valAt {x : (Σ k, ι k) → Ω} {b₀ : (Σ k, ι k) → ℂ} (hb : b₀ ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal b₀) s) : ContinuousWithinAt (valAt x s) (mcPts (mCoordIdeal x)) b₀ := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hx := ValRing.aeval_ne_zero_of_notMem hb hh hn
  have h0 := ValRing.eval_ne_zero_of_notMem hh hn
  have cg : Continuous fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) g) :=
    MvPolynomial.continuous_eval _
  have ch : Continuous fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have hne : ∀ᶠ b in 𝓝 b₀, eval b (map (Int.castRingHom ℂ) h) ≠ 0 := ch.continuousAt.eventually_ne h0
  have key : valAt x s =ᶠ[𝓝[mcPts (mCoordIdeal x)] b₀]
      fun b => eval b (map (Int.castRingHom ℂ) g) / eval b (map (Int.castRingHom ℂ) h) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hne] with b hbm hbn
    exact valAt_eq hbm ⟨d, g, h, hg, hh, hx, heq, hbn, rfl⟩
  have hq : ContinuousWithinAt
      (fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) g) / eval b (map (Int.castRingHom ℂ) h))
      (mcPts (mCoordIdeal x)) b₀ := (cg.continuousAt.div ch.continuousAt h0).continuousWithinAt
  exact hq.congr_of_eventuallyEq key (key.self_of_nhdsWithin hb)

end Values

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem continuousWithinAt_twMinor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {Z : Type}
    [TopologicalSpace Z] {A : Set Z} {z₀ : Z} {bs : Z → (Σ k, baseIdx ι M.blk k) → ℂ} {pt : Z → (Σ k, ι k) → ℂ}
    (hbs : Continuous bs) (hpt : Continuous pt) (hA : Set.MapsTo bs A (mcPts (mCoordIdeal M.x))) (hz₀ : z₀ ∈ A)
    (hG : M.GoodAt F (mCoordIdeal (bs z₀))) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ)
    (J : Finset (Fin N)) : ContinuousWithinAt (fun z => twMinor M F (bs z) i k g (pt z) J) A z₀ := by
  unfold twMinor pluck
  refine tendsto_finsetSum _ fun I _ => Tendsto.const_mul _ (tendsto_finsetSum _ fun m _ => Tendsto.mul ?_ ?_)
  · exact (continuousWithinAt_valAt (hA hz₀) (hG.2.1 _ _).2).comp hbs.continuousWithinAt hA
  · exact ((continuous_apply _).comp hpt).continuousWithinAt

theorem isBlockMap_v₀ (k₀ : K) : IsBlockMap (some : K → Option K) (v₀ (ι := ι) k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, m⟩ ⟨k', m'⟩ e
    simp only [v₀] at e
    obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.1 e
    obtain rfl := Option.some_injective _ e1
    rw [eq_of_heq e2]
  · rintro ⟨_, m⟩ ⟨k, rfl⟩
    exact ⟨⟨k, m⟩, rfl⟩

theorem continuous_fstPt (k₀ : K) : Continuous (fstPt (ι := ι) k₀) :=
  continuous_pi fun p => continuous_apply (v₀ k₀ p)

theorem continuous_sndPt (k₀ : K) : Continuous (sndPt (ι := ι) k₀) :=
  continuous_pi fun p => continuous_apply (v₁ k₀ p)

theorem continuous_baseOf (M : FlagModel y Ψ N j) (k₀ : K) : Continuous (baseOf M k₀) :=
  continuous_pi fun q => continuous_apply (v₀ k₀ ⟨q.1.1, q.2⟩)

theorem fstPt_mem (M : FlagModel y Ψ N j) {d : ℕ} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N}
    (hb : (b : ℕ) = a + 1) (hba : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀)
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hV : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2))
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts (wP M τ a k₀ ca cb)) :
    fstPt k₀ z ∈ mcPts (mCoordIdeal y) := by
  have hI := (GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk hca hcb hV).2.2.2.1
  exact GlobalTheory.CompanionTheory.Ar.Chg.mem_mcPts_restr (isBlockMap_v₀ k₀) hI.ge hz

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∃ O' : Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ), IsOpen O' ∧ wO M Rb τ a k₀ ca cb F kb V r h = O' ∩ mcPts (wP M τ a k₀ ca cb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hc
  obtain ⟨hb, hba, hk₀, hca, hcb, hAV, -, hBC, hr, hrc, -⟩ := hc
  have hmaps : Set.MapsTo (baseOf M k₀) (mcPts (wP M τ a k₀ ca cb)) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    CPts.base_mem M (fstPt_mem M hb hba hk₀ hca hcb hAV hz)
  have key : ∀ z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h,
      wO M Rb τ a k₀ ca cb F kb V r h ∈ 𝓝[mcPts (wP M τ a k₀ ca cb)] z₀ := by
    rintro z₀ ⟨hz₀, hsrc, hV₀, hm₁, hm₂⟩
    have hbm := hmaps hz₀
    have hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z₀)) := by
      obtain ⟨-, -, hgood, horb⟩ := hBC.2.2.2.2 _ hV₀
      rw [(Rb.A.chart kb).left_inv hsrc] at horb
      rwa [CovMap.mCoordIdeal_eq_of_sameOrbit (orbit_trans (orbit_symm (hr _ hbm)) horb)]
    have hrb : ContinuousWithinAt (fun z => r (baseOf M k₀ z)) (mcPts (wP M τ a k₀ ca cb)) z₀ :=
      (hrc _ hbm).comp (continuous_baseOf M k₀).continuousWithinAt hmaps
    have e₁ := hrb.tendsto.eventually_mem ((Rb.A.chart kb).open_source.mem_nhds hsrc)
    have e₂ := (((Rb.A.chart kb).continuousAt hsrc).tendsto.comp hrb.tendsto).eventually_mem (hBC.1.mem_nhds hV₀)
    have tw := fun (pt : _ → (Σ k, ι k) → ℂ) (hpt : Continuous pt) =>
      continuousWithinAt_twMinor M F (continuous_baseOf M k₀) hpt hmaps hz₀ hG
    have e₃ : ∀ᶠ z in 𝓝[mcPts (wP M τ a k₀ ca cb)] z₀, ∀ p k, M.blk p = some k →
        twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0 := by
      refine eventually_all.2 fun p => eventually_all.2 fun k => ?_
      by_cases hp : M.blk p = some k
      · exact ((tw _ (continuous_fstPt k₀) p.2 k (h p.1)⁻¹ (stepCols N j p.2)).tendsto.eventually_ne
          (hm₁ p k hp)).mono fun _ hz _ => hz
      · exact Eventually.of_forall fun _ hp' => absurd hp' hp
    have e₄ := (tw _ (continuous_sndPt k₀) a k₀ (h τ)⁻¹ (stepCols N j a)).tendsto.eventually_ne hm₂
    filter_upwards [self_mem_nhdsWithin, e₁, e₂, e₃, e₄] with z h₀ h₁ h₂ h₃ h₄
    exact ⟨h₀, h₁, h₂, h₃, h₄⟩
  choose! U hU hmem hsub using fun z₀ (hz : z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h) =>
    mem_nhdsWithin.1 (key z₀ hz)
  refine ⟨⋃ z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h, U z₀, isOpen_biUnion hU, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨Set.mem_biUnion hz (hmem z hz), hz.1⟩
  · rintro z ⟨hz, hzA⟩
    obtain ⟨z₀, h₀, hz₀⟩ := Set.mem_iUnion₂.1 hz
    exact hsub z₀ h₀ ⟨hz₀, hzA⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSixthStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_sixth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∃ O' : Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ), IsOpen O' ∧ wO M Rb τ a k₀ ca cb F kb V r h = O' ∩ mcPts (wP M τ a k₀ ca cb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQContinuousAtAndLocalSolutionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartQ_continuousAt_and_local_solution : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) (Pr : Matrix (Fin g) (Fin g) ℝ), IsChart L bas A T0 B c ρ → IsKerProj (∑ j, B j) Pr → ContinuousAt (chartQ Pr A T0) 0 ∧ ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ w ∈ logCover L.a_le, ‖expCover a w‖ < ρ' → ∀ y : Fin g → ℂ, ∃ p : Fin g → ℂ, p - y ∈ Submodule.span ℂ {u | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) ∧ u = L.P w x} ∧ (∀ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) → p ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w x) = 0) ∧ ∀ y' : Fin g → ℂ, y' ⬝ᵥ L.H (expCover a w) *ᵥ star p = y' ⬝ᵥ chartQ Pr A T0 (expCover a w) *ᵥ star y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep <;> assumption)
end
