module

public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationLimit
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationLimit
open Matrix Filter Topology Set MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.BesselCutLim

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem tendsto_cut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure (PI.MtM n)}
    {f : PI.MtM n → E} (hf : Integrable f μ) {ρ : Mat n → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ) :
    Tendsto (fun N : ℕ => ∫ y : PI.MtM n, (ρ (((N : ℝ) + 1)⁻¹ • Matrix.of y) : ℂ) • f y ∂μ) atTop
      (𝓝 ((ρ 0 : ℂ) • ∫ y, f y ∂μ)) := by
  obtain ⟨C, hC⟩ := hρ.bounded_above_of_compact_support hc
  rw [← integral_smul]
  refine tendsto_integral_of_dominated_convergence (fun y => C * ‖f y‖) (fun N => ?_)
    (hf.norm.const_mul C) (fun N => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · have h1 : Continuous fun y : PI.MtM n => (ρ (((N : ℝ) + 1)⁻¹ • Matrix.of y) : ℂ) :=
      Complex.continuous_ofReal.comp (hρ.comp
        ((show Continuous fun y : PI.MtM n => (Matrix.of y : Mat n) from continuous_id).const_smul
          (((N : ℝ) + 1)⁻¹)))
    exact h1.aestronglyMeasurable.smul hf.1
  · rw [norm_smul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · refine Tendsto.smul_const ?_ _
    refine (Complex.continuous_ofReal.comp hρ).continuousAt.tendsto.comp ?_
    have h0 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h0.smul_const (Matrix.of y : Mat n)

theorem integrable_conj_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (Mat n)}
    (hG : IsClosed G) {μ : Measure (PI.MtM n)} (hae : ∀ᵐ y ∂μ, (Matrix.of y : Mat n) ∈ G)
    {c : PI.MtM n → ℂ} (hc : Integrable c μ) {g : Mat n → E} (hg : ContinuousOn g G) {K : ℝ}
    (hK : ∀ x ∈ G, ‖g x‖ ≤ K) : Integrable (fun y => conj (c y) • g (Matrix.of y)) μ := by
  have hms : MeasurableSet {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G} :=
    IsClosed.measurableSet (α := PI.MtM n) hG
  have hg' : ContinuousOn (fun y : PI.MtM n => g (Matrix.of y)) {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G} := hg
  have hm := hg'.aestronglyMeasurable (μ := μ) hms
  rw [Measure.restrict_eq_self_of_ae_mem (s := {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G}) hae] at hm
  refine Integrable.mono' (hc.norm.mul_const K)
    ((Complex.continuous_conj.comp_aestronglyMeasurable hc.1).smul hm) ?_
  filter_upwards [hae] with y hy
  rw [norm_smul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (hK _ hy) (norm_nonneg _)

theorem lieW_of {Hm : Mat n} {W : List (Mat n)} (hW : LieWd Hm W) : LieW (UH Hm) W :=
  fun X hX t => ex_mem_of_lie (hW X hX) t

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Hm : Mat n}
  {σ : Mat n → (H →L[ℂ] H)}

theorem tendsto_dsW (hD : CutDer) (hσ : URep Hm σ) {μ : Measure (PI.MtM n)} (hμ : PI.IsHaarOnM (UH Hm) μ)
    {w : H} (hw : IsSm (UH Hm) σ w)
    (hi : ∀ v, IsSm (UH Hm) σ v → Integrable (fun y : PI.MtM n => ⟪v, σ (Matrix.of y) w⟫_ℂ) μ) {κ : ℂ}
    (hκ : ∀ v, IsSm (UH Hm) σ v →
      ∫ y : PI.MtM n, conj ⟪v, σ (Matrix.of y) w⟫_ℂ • σ (Matrix.of y) w ∂μ = κ • v)
    (W : List (Mat n)) : LieWd Hm W → ∀ ρ : Mat n → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      ∀ v, IsSm (UH Hm) σ v →
      Tendsto (fun N : ℕ => dsW σ W (cutI σ μ w ((N : ℝ) + 1) ρ v)) atTop (𝓝 ((ρ 0 : ℂ) • κ • dsW σ W v)) := by
  induction W using List.reverseRecOn with
  | nil =>
    intro _ ρ hρ hc v hv
    have h1 := integrable_conj_smul hσ.grp.1 hμ.2.2.1 (hi v hv) (g := fun x => σ x w)
      (SmOn.continuousOn hw) (K := ‖w‖) fun x hx => (hσ.iso x hx w).le
    have h2 := tendsto_cut h1 hρ.continuous hc
    rw [hκ v hv] at h2
    simpa only [dsW, List.foldr_nil, cutI, mul_smul] using h2
  | append_singleton W X ih =>
    intro hWX ρ hρ hc v hv
    have hW : LieWd Hm W := fun Y hY => hWX Y (List.mem_append_left _ hY)
    have hX : Lie Hm X := hWX X (by simp)
    have hX' : LieWd Hm [X] := fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
    have hv' : IsSm (UH Hm) σ (ds σ X v) := hv.dsW hσ.rep (lieW_of hX')
    have hρ' := contDiff_Lx X hρ
    have hc' : HasCompactSupport (Lx X ρ) := hasCompactSupport_LW hc [X]
    have e : ∀ u, dsW σ (W ++ [X]) u = dsW σ W (ds σ X u) := fun u => by
      simp only [dsW, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have h1 := (ih hW _ hρ' hc' v hv).add (ih hW ρ hρ hc _ hv')
    have h0 : Lx X ρ 0 = 0 := by simp [Lx]
    rw [h0, Complex.ofReal_zero, zero_smul, zero_add] at h1
    rw [e]
    refine h1.congr fun N => ?_
    have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [e, (hD n Hm H σ hσ μ hμ w hw _ hR ρ hρ hc v hv).2 X hX,
      dsW_add hσ.rep (hD n Hm H σ hσ μ hμ w hw _ hR _ hρ' hc' v hv).1
        (hD n Hm H σ hσ μ hμ w hw _ hR ρ hρ hc _ hv').1 (lieW_of hW)]

theorem dsW_cutI (hσ : URep Hm σ) {μ : Measure (PI.MtM n)} (hμ : PI.IsHaarOnM (UH Hm) μ)
    {w : H} (hw : IsSm (UH Hm) σ w) {R : ℝ} (hR : 0 < R) {ρ : Mat n → ℝ} (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (v : H) {W : List (Mat n)} (hW : LieWd Hm W) :
    Integrable (fun y : PI.MtM n => ((ρ (R⁻¹ • Matrix.of y) : ℂ) * conj ⟪v, σ (Matrix.of y) w⟫_ℂ) •
      dsW σ W (σ (Matrix.of y) w)) μ ∧
    dsW σ W (cutI σ μ w R ρ v) = ∫ y : PI.MtM n, ((ρ (R⁻¹ • Matrix.of y) : ℂ) * conj ⟪v, σ (Matrix.of y) w⟫_ℂ) •
      dsW σ W (σ (Matrix.of y) w) ∂μ := by
  have hG := hσ.grp
  have hι := CompanionTheory.D.Upq.ModEx.MG.measurableEmbedding_toM (hG := hG)
  have hmap := CompanionTheory.D.Upq.Quot.map_comap_toM hG (μ := μ) hμ.2.2.1
  set μ' := μ.comap (CompanionTheory.D.Upq.ModEx.MG.toM (hG := hG)) with hμ'
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun K hK => by
    rw [hμ', hι.comap_apply]
    exact CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact hG hμ
      (hK.image (CompanionTheory.D.Upq.ModEx.MG.continuous_mat (hG := hG)))⟩
  let φ : CompanionTheory.D.Upq.ModEx.MG (UH Hm) hG → ℂ := fun g =>
    (ρ (R⁻¹ • g.mat) : ℂ) * conj ⟪v, σ g.mat w⟫_ℂ
  have ho : Continuous fun g : CompanionTheory.D.Upq.ModEx.MG (UH Hm) hG => σ g.mat w :=
    continuous_orbit hσ.rep hw (W := []) fun _ h => by simp at h
  have hφ : Continuous φ :=
    (Complex.continuous_ofReal.comp (hρ.comp
      (CompanionTheory.D.Upq.ModEx.MG.continuous_mat.const_smul R⁻¹))).mul
      (Complex.continuous_conj.comp (continuous_const.inner ho))
  have hcs : HasCompactSupport fun x : Mat n => (ρ (R⁻¹ • x) : ℂ) :=
    (hc.comp_smul (inv_ne_zero hR.ne')).comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hφc : HasCompactSupport φ :=
    (hcs.comp_isClosedEmbedding CompanionTheory.D.Upq.ModEx.MG.isClosedEmbedding_mat).mul_right
  unfold cutI
  rw [← hmap, hι.integrable_map_iff, hι.integral_map, hι.integral_map]
  exact ⟨integrable_csmul hφ hφc (continuous_orbit hσ.rep hw (lieW_of hW)),
    dsW_integral hσ.rep hw hφ hφc (lieW_of hW)⟩

theorem cutLim_of (hF : Factor) (hD : CutDer) : CutLim := by
  intro n Hm H _ _ _ σ hσ V _ _ _ B hB μ hμ w hw hi κ hκ ⟨K, hK⟩ v hv
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  obtain ⟨M, W, β, hW, hBβ⟩ := hF n Hm H σ hσ V B hB
  obtain ⟨ρ, -, hc, hρ, -, hρ1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (Filter.univ_mem : (univ : Set (Mat n)) ∈ 𝓝 0)
  have hae : ∀ᵐ y ∂μ, (Matrix.of y : Mat n) ∈ UH Hm := hμ.2.2.1
  have h1 : Tendsto (fun N : ℕ => ∑ i, β i (dsW σ (W i) (cutI σ μ w ((N : ℝ) + 1) ρ v))) atTop
      (𝓝 (∑ i, β i ((ρ 0 : ℂ) • κ • dsW σ (W i) v))) :=
    tendsto_finsetSum _ fun i _ => ((β i).continuous.tendsto _).comp
      (tendsto_dsW hD hσ hμ hw hi hκ (W i) (hW i) ρ hρ hc v hv)
  have hBc : ContinuousOn (fun x => B (σ x w)) (UH Hm) :=
    (continuousOn_finsetSum _ fun i _ => (β i).continuous.comp_continuousOn
      (continuousOn_dsW_orbit hσ.rep hw (lieW_of (hW i)))).congr
      fun x hx => hBβ _ (hw.apply hσ.rep hx)
  have h2 := tendsto_cut (integrable_conj_smul hσ.grp.1 hae (hi v hv) hBc hK) hρ.continuous hc
  rw [hρ1, Complex.ofReal_one] at h1 h2
  simp only [one_smul, map_smul] at h1 h2
  rw [← Finset.smul_sum, ← hBβ v hv] at h1
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h3 := fun i => dsW_cutI hσ hμ hw hR hρ.continuous hc v (hW i)
  rw [Finset.sum_congr rfl fun i _ => by rw [(h3 i).2, ← (β i).integral_comp_comm (h3 i).1],
    ← integral_finsetSum _ fun i _ => (β i).integrable_comp (h3 i).1]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hBβ _ (hw.apply hσ.rep hy)]
  simp only [map_smul, mul_smul, Finset.smul_sum]

end GlobalTheory.CompanionTheory.BesselCutLim

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationLimitStatement
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_derivation_limit : Factor → CutDer → CutLim := by
  first | exact @GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of | exact GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of | (intros; apply GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplex
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplex
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckToRaw

variable {k r : ℕ}

theorem dsigW_zero' (R : Rep k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :
    PI.UpqRep.dsigW (k := k) (r := r) R.σ W (0 : R.H) = 0 := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0) = 0
    rw [ih]
    simp [PI.UpqRep.dsig]


open Classical in
def extZ {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub) (y : R.H) : R'.H :=
  if h : y ∈ R.smSub then (f ⟨y, h⟩ : R'.H) else 0

theorem extZ_coe {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub) (y : R.smSub) :
    extZ f (y : R.H) = (f y : R'.H) := by
  simp only [extZ, dite_eq_left y.2]

theorem smMap_extZ {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub)
    (hf : ∀ W, LieWd k r W → ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))), (∀ W' ∈ Ws, LieWd k r W') ∧
      ∀ y : R.smSub, ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (f y : R'.H)‖ ≤
        C * (Ws.map fun W' => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W' (y : R.H)‖).sum) :
    SmMap R R' (extZ f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    have := extZ_coe f ⟨v, hv⟩
    rw [show extZ f v = _ from this]
    exact (f _).2
  · intro v hv w hw
    have h1 := extZ_coe f ⟨v, hv⟩
    have h2 := extZ_coe f ⟨w, hw⟩
    have h3 := extZ_coe f (⟨v, hv⟩ + ⟨w, hw⟩)
    rw [show extZ f v = _ from h1, show extZ f w = _ from h2, show extZ f (v + w) = _ from h3, map_add (f := _)]
    rfl
  · intro a v hv
    have h1 := extZ_coe f ⟨v, hv⟩
    have h3 := extZ_coe f (a • ⟨v, hv⟩)
    rw [show extZ f v = _ from h1, show extZ f (a • v) = _ from h3, map_smul]
    rfl
  · intro W hW
    obtain ⟨C, Ws, h1, h2⟩ := hf W hW
    refine ⟨C, Ws, h1, fun v hv => ?_⟩
    have h3 := extZ_coe f ⟨v, hv⟩
    show ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (extZ f v)‖ ≤ _
    rw [show extZ f v = _ from h3]
    exact h2 ⟨v, hv⟩

theorem sn_single (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (v : X.2.R.smSub) :
    sn X W (Pi.single c v) = ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (v : X.2.R.H)‖ := by
  unfold sn
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, ZeroMemClass.coe_zero, dsigW_zero', norm_zero]
  · simp

theorem le_sn (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (x : M X) :
    ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖ ≤ sn X W x :=
  Finset.single_le_sum (f := fun c => ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ c)

def coord {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (c : X.1.ι) : X.2.R.smSub →ₗ[ℂ] Y.2.R.smSub :=
  LinearMap.proj d ∘ₗ f ∘ₗ LinearMap.single ℂ (fun _ : X.1.ι => X.2.R.smSub) c

theorem coord_apply {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (c : X.1.ι) (v : X.2.R.smSub) :
    coord f d c v = f (Pi.single c v) d := rfl

theorem smMap_coord {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hf : IsHom X Y f) (d : Y.1.ι) (c : X.1.ι) :
    SmMap X.2.R Y.2.R (extZ (coord f d c)) := by
  refine smMap_extZ _ fun W hW => ?_
  obtain ⟨C, Ws, h1, h2⟩ := hf.cont W hW
  refine ⟨C, Ws, h1, fun y => ?_⟩
  have := (le_sn Y W d _).trans (h2 (Pi.single c y))
  simpa only [sn_single, coord_apply] using this

theorem sum_coord {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (x : M X) :
    ∑ c, extZ (coord f d c) (x c : X.2.R.H) = (f x d : Y.2.R.H) := by
  simp only [extZ_coe, coord_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply]
  simp

theorem act_coe (X : Obj k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ GG k r) (x : M X) (c : X.1.ι) :
    (CompanionTheory.Zuck.act X g x c : X.2.R.H) = BranchingSupport.act X.1.ρ X.2.R g (fun d => (x d : X.2.R.H)) c := by
  simp [CompanionTheory.Zuck.act, BranchingSupport.act, mAct, dOp, URep.sig_coe _ hg]

theorem one_coord {U : URep k r} {Y : Obj k r} (f : M (one U) →ₗ[ℂ] M Y) (d : Y.1.ι) (x : M (one U)) :
    extZ (coord f d ()) (x () : U.R.H) = (f x d : Y.2.R.H) := by
  rw [← sum_coord f d x]
  simp

theorem act_one (U : URep k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ GG k r) (x : M (one U)) :
    (CompanionTheory.Zuck.act (one U) g x () : U.R.H) = U.R.σ g (x ()) := by
  rw [act_coe (one U) hg]
  simp [BranchingSupport.act]

theorem toRaw : ToRaw := by
  rintro k r F U κ _ _ T ⟨io, pr, h⟩
  refine ⟨fun a c => extZ (coord (io a) c ()), fun a c => extZ (coord (pr a) () c), ?_⟩
  refine ⟨fun I c => smMap_coord (h.io_hom I) c (), fun I c => smMap_coord (h.pr_hom I) () c,
    fun I g hg y hy => ?_, fun I g hg x hx => ?_, fun x hx c => ?_, fun I y hy => ?_, fun I J hIJ y hy => ?_⟩
  · let y' : M (one (T I)) := fun _ => ⟨y, hy⟩
    funext c
    have e1 : (T I).R.σ g y = (CompanionTheory.Zuck.act (one (T I)) g y' () : (T I).R.H) := (act_one (T I) hg y').symm
    have e2 : ∀ d, extZ (coord (io I) d ()) y = (io I y' d : U.R.H) := fun d => one_coord (io I) d y'
    have e3 := LinearMap.congr_fun ((h.io_hom I).equiv g hg) y'
    simp only [LinearMap.comp_apply] at e3
    simp only [e2]
    rw [e1, one_coord, e3]
    exact act_coe (F, U) hg _ c
  · let x' : M (F, U) := fun c => ⟨x c, hx c⟩
    have e1 : ∀ c, BranchingSupport.act F.ρ U.R g x c = (CompanionTheory.Zuck.act (F, U) g x' c : U.R.H) :=
      fun c => (act_coe (F, U) hg x' c).symm
    have e2 : ∑ c, extZ (coord (pr I) () c) (x c) = (pr I x' () : (T I).R.H) := sum_coord (pr I) () x'
    have e3 := LinearMap.congr_fun ((h.pr_hom I).equiv g hg) x'
    simp only [LinearMap.comp_apply] at e3
    simp only [e1]
    rw [e2, ← act_one (T I) hg, ← e3]
    exact sum_coord (pr I) () _
  · let x' : M (F, U) := fun c => ⟨x c, hx c⟩
    have e2 : ∀ I, ∑ c, extZ (coord (pr I) () c) (x c) = (pr I x' () : (T I).R.H) :=
      fun I => sum_coord (pr I) () x'
    have e4 : ∀ I, extZ (coord (io I) c ()) (pr I x' () : (T I).R.H) = (io I (pr I x') c : U.R.H) :=
      fun I => one_coord (io I) c _
    have e3 := congrFun (LinearMap.congr_fun h.sum x') c
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at e3
    simp only [e2, e4]
    rw [← Submodule.coe_sum, e3]
  · let y' : M (one (T I)) := fun _ => ⟨y, hy⟩
    have e2 : ∀ d, extZ (coord (io I) d ()) y = (io I y' d : U.R.H) := fun d => one_coord (io I) d y'
    have e3 := LinearMap.congr_fun (h.pr_io I) y'
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e3
    simp only [e2]
    refine (sum_coord (pr I) () (io I y')).trans ?_
    rw [e3]
  · let y' : M (one (T J)) := fun _ => ⟨y, hy⟩
    have e2 : ∀ d, extZ (coord (io J) d ()) y = (io J y' d : U.R.H) := fun d => one_coord (io J) d y'
    have e3 := LinearMap.congr_fun (h.pr_io_ne I J hIJ) y'
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at e3
    simp only [e2]
    refine (sum_coord (pr I) () (io J y')).trans ?_
    rw [e3]
    rfl

end GlobalTheory.CompanionTheory.ZuckToRaw

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplexStatement
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ToRawComplex : ToRaw := by
  first | exact @GlobalTheory.CompanionTheory.ZuckToRaw.toRaw | exact GlobalTheory.CompanionTheory.ZuckToRaw.toRaw | (intros; apply GlobalTheory.CompanionTheory.ZuckToRaw.toRaw <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivation
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivation
open Matrix MeasureTheory Filter Topology Set Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.CutDeriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuous_of : Continuous fun y : PI.MtM n => (Matrix.of y : Mat n) := continuous_id

theorem continuous_scale (c : ℝ) : Continuous fun y : PI.MtM n => (c • Matrix.of y : Mat n) :=
  continuous_of.const_smul c

theorem notMem_tsupport {ρ : Mat n → ℝ} {R : ℝ} (hR : 0 < R) (X : Mat n) {T : Set ℝ} {t : ℝ} (ht : t ∈ T)
    {y : PI.MtM n}
    (hy : y ∉ (fun p : ℝ × Mat n => (Matrix.of.symm (R • (ex X p.1 * p.2)) : PI.MtM n)) '' (T ×ˢ tsupport ρ)) :
    ex X (-t) * (R⁻¹ • Matrix.of y) ∉ tsupport ρ := fun hs =>
  hy ⟨(t, ex X (-t) * (R⁻¹ • Matrix.of y)), ⟨ht, hs⟩, by
    simp only
    rw [← Matrix.mul_assoc, ← ex_add, add_neg_cancel, ex_zero, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ hR.ne', one_smul]
    rfl⟩

theorem isCompact_img {ρ : Mat n → ℝ} (hc : HasCompactSupport ρ) (R : ℝ) (X : Mat n) {T : Set ℝ}
    (hT : IsCompact T) : IsCompact
      ((fun p : ℝ × Mat n => (Matrix.of.symm (R • (ex X p.1 * p.2)) : PI.MtM n)) '' (T ×ˢ tsupport ρ)) := by
  have h1 : Continuous fun p : ℝ × Mat n => (R • (ex X p.1 * p.2) : Mat n) :=
    (((continuous_ex X).comp continuous_fst).matrix_mul continuous_snd).const_smul R
  exact (hT.prod hc.isCompact).image h1

theorem hasCompactSupport_coef {ρ : Mat n → ℝ} (hc : HasCompactSupport ρ) {R : ℝ} (hR : 0 < R)
    (φ : PI.MtM n → ℂ) : HasCompactSupport fun y : PI.MtM n => (ρ (R⁻¹ • Matrix.of y) : ℂ) * φ y := by
  refine HasCompactSupport.intro (isCompact_img hc R 0 (isCompact_singleton (x := (0 : ℝ)))) fun y hy => ?_
  have := notMem_tsupport hR 0 (mem_singleton _) hy
  rw [neg_zero, ex_zero, Matrix.one_mul] at this
  rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]

theorem continuous_coef {ρ : Mat n → ℝ} (hρ : Continuous ρ) (R : ℝ) {F : Mat n → H} (hF : Continuous F) (v : H) :
    Continuous fun y : PI.MtM n => (ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ :=
  (Complex.continuous_ofReal.comp (hρ.comp (continuous_scale _))).mul
    ((hF.comp continuous_of).inner continuous_const)

variable {Hm : Mat n} {σ : Mat n → (H →L[ℂ] H)} {μ : Measure (PI.MtM n)} {w : H} {F : Mat n → H}

theorem cutI_eq (hμ : PI.IsHaarOnM (UH Hm) μ) (hFw : ∀ a ∈ UH Hm, F a = σ a w) (R : ℝ) (ρ : Mat n → ℝ) (v : H) :
    cutI σ μ w R ρ v =
      ∫ y : PI.MtM n, ((ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ) • F (Matrix.of y) ∂μ := by
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ UH Hm := hμ.2.2.1
  refine integral_congr_ae ?_
  filter_upwards [hae] with g hg
  rw [hFw _ hg, inner_conj_symm]

theorem inner_iso (h : URep Hm σ) {g : Mat n} (hg : g ∈ UH Hm) (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ g).toLinearMap (h.iso g hg)).inner_map_map x y

variable [CompleteSpace H]

theorem apply_cutI (h : URep Hm σ) (hμ : PI.IsHaarOnM (UH Hm) μ) (hF : Continuous F)
    (hFw : ∀ a ∈ UH Hm, F a = σ a w) {R : ℝ} (hR : 0 < R) {ρ : Mat n → ℝ} (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (v : H) {X : Mat n} (hX : ∀ t, ex X t ∈ UH Hm) (t : ℝ) :
    σ (ex X t) (cutI σ μ w R ρ v) =
      ∫ y : PI.MtM n, ((ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ) •
        F (Matrix.of y) ∂μ := by
  haveI : IsFiniteMeasureOnCompacts μ :=
    ⟨fun _ hK => CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact h.grp hμ hK⟩
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ UH Hm := hμ.2.2.1
  have hi : Integrable (fun y : PI.MtM n =>
      ((ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ) • F (Matrix.of y)) μ :=
    ((continuous_coef hρ R hF v).smul (hF.comp continuous_of)).integrable_of_hasCompactSupport
      (hasCompactSupport_coef hc hR _).smul_right
  have hl : Continuous (PI.lmulQ (ex X t)) := by
    have : Continuous fun y : PI.MtM n => (ex X t * Matrix.of y : Mat n) :=
      continuous_const.matrix_mul continuous_of
    exact this
  have hg : Continuous fun y : PI.MtM n =>
      ((ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ) • F (Matrix.of y) :=
    ((Complex.continuous_ofReal.comp (hρ.comp (continuous_const.matrix_mul (continuous_scale _)))).mul
      ((hF.comp continuous_of).inner continuous_const)).smul (hF.comp continuous_of)
  rw [cutI_eq hμ hFw, ← (σ (ex X t)).integral_comp_comm hi]
  conv_rhs => rw [← hμ.2.2.2 _ (hX t)]
  rw [integral_map hl.measurable.aemeasurable hg.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hae] with g hg
  have e : (Matrix.of (PI.lmulQ (ex X t) g) : Mat n) = ex X t * Matrix.of g := rfl
  rw [e, hFw _ (h.rep.mul_mem _ (hX t) _ hg), h.rep.apply_mul (hX t) hg, inner_iso h (hX t), map_smul,
    hFw _ hg, Matrix.mul_smul, ← Matrix.mul_assoc, ← ex_add, neg_add_cancel, ex_zero, Matrix.one_mul]

theorem cutDer : CutDer := by
  intro n Hm H _ _ _ σ h μ hμ w hw R hR ρ hρ hc v hv
  haveI : IsFiniteMeasureOnCompacts μ :=
    ⟨fun _ hK => CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact h.grp hμ hK⟩
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ UH Hm := hμ.2.2.1
  obtain ⟨F, hF, hFw⟩ := SmOn.exists_contDiff hw h.grp.1
  have hFc : Continuous F := hF.continuous
  have hFo : Continuous fun y : PI.MtM n => F (Matrix.of y) := hFc.comp continuous_of
  refine ⟨?_, fun X hX' => ?_⟩
  · have h1 := isSm_integral h.grp h.rep hw hμ (continuous_coef hρ.continuous R hFc v)
      (hasCompactSupport_coef hc hR _)
    convert h1 using 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with g hg
    rw [hFw _ hg, inner_conj_symm]
  have hX : ∀ t, ex X t ∈ UH Hm := fun t => ex_mem_of_lie hX' t
  have hdv : IsSm (UH Hm) σ (ds σ X v) :=
    hv.dsW h.rep (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
  have hu : Continuous fun t => σ (ex X t) v :=
    continuous_iff_continuousAt.2 fun t => (hv.hasDerivAt h.rep hX t).continuousAt
  have hu' : Continuous fun t => σ (ex X t) (ds σ X v) :=
    continuous_iff_continuousAt.2 fun t => (hdv.hasDerivAt h.rep hX t).continuousAt
  have hγ : Continuous fun p : ℝ × PI.MtM n => ex X (-p.1) * (R⁻¹ • Matrix.of p.2 : Mat n) :=
    ((continuous_ex X).comp continuous_fst.neg).matrix_mul ((continuous_scale _).comp continuous_snd)
  have hρL := (contDiff_Lx X hρ).continuous
  have hcL : HasCompactSupport (Lx X ρ) := hasCompactSupport_LW hc [X]
  have hc1 : ∀ {ψ : Mat n → ℝ} {u : ℝ → H}, Continuous ψ → Continuous u →
      Continuous fun p : ℝ × PI.MtM n =>
        (ψ (ex X (-p.1) * (R⁻¹ • Matrix.of p.2 : Mat n)) : ℂ) * ⟪F (Matrix.of p.2), u p.1⟫_ℂ :=
    fun hψ hu => (Complex.continuous_ofReal.comp (hψ.comp hγ)).mul
      ((hFo.comp continuous_snd).inner (hu.comp continuous_fst))
  have hd := hasDerivAt_integral_cpt (μ := μ)
    (F := fun t y => ((ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ) •
      F (Matrix.of y))
    (F' := fun t y => ((Lx X ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ +
      (ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) (ds σ X v)⟫_ℂ) •
      F (Matrix.of y))
    (fun t => ((hc1 hρ.continuous hu).comp (Continuous.prodMk_right t)).smul hFo)
    (((hc1 hρL hu).add (hc1 hρ.continuous hu')).smul (hFo.comp continuous_snd))
    (fun t a => by
      have d1 := (hasDerivAt_Lx X (R⁻¹ • Matrix.of a) hρ t).ofReal_comp
      have d2 : HasDerivAt (fun s => ⟪F (Matrix.of a), σ (ex X s) v⟫_ℂ)
          ⟪F (Matrix.of a), σ (ex X t) (ds σ X v)⟫_ℂ t :=
        ((innerSL ℂ (F (Matrix.of a))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
          (hv.hasDerivAt h.rep hX t)
      exact (d1.mul d2).smul_const _)
    (isCompact_img hc R X (isCompact_Icc (a := (-1 : ℝ)) (b := 1)))
    (fun a ha => by
      rw [image_eq_zero_of_notMem_tsupport (notMem_tsupport hR X (t := 0) (by norm_num) ha),
        Complex.ofReal_zero, zero_mul, zero_smul])
    (fun t ht a ha => by
      have h0 := notMem_tsupport hR X ht ha
      rw [image_eq_zero_of_notMem_tsupport h0,
        image_eq_zero_of_notMem_tsupport (fun hs => h0 (tsupport_Lx X ρ hs)),
        Complex.ofReal_zero, zero_mul, zero_mul, add_zero, zero_smul])
  have hi : ∀ {ψ : Mat n → ℝ} (u : H), Continuous ψ → HasCompactSupport ψ → Integrable (fun y : PI.MtM n =>
      ((ψ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), u⟫_ℂ) • F (Matrix.of y)) μ := fun u hψ hcψ =>
    ((continuous_coef hψ R hFc u).smul hFo).integrable_of_hasCompactSupport
      (hasCompactSupport_coef hcψ hR _).smul_right
  rw [cutI_eq hμ hFw R (Lx X ρ), cutI_eq hμ hFw R ρ (ds σ X v),
    ← integral_add (hi _ hρL hcL) (hi _ hρ.continuous hc)]
  conv_lhs => unfold ds
  simp_rw [apply_cutI h hμ hFc hFw hR hρ.continuous hc v hX]
  rw [hd.deriv]
  simp only [neg_zero, ex_zero, Matrix.one_mul, h.rep.map_one, ContinuousLinearMap.one_apply, add_smul]

end GlobalTheory.CompanionTheory.CutDeriv

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationStatement
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TruncatedDerivation : CutDer := by
  first | exact @GlobalTheory.CompanionTheory.CutDeriv.cutDer | exact GlobalTheory.CompanionTheory.CutDeriv.cutDer | (intros; apply GlobalTheory.CompanionTheory.CutDeriv.cutDer <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLaws
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLaws
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckDecTens

section Lin

universe u

variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]

theorem dec_comp {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop} (hc : IsLinCat N Hom) {A B P : Type} [Fintype A] [Fintype B]
    [Fintype P] (e : P ≃ A × B) {X : O} {Z : A → O} {S : A → B → O}
    {j : ∀ a, N (Z a) →ₗ[ℂ] N X} {q : ∀ a, N X →ₗ[ℂ] N (Z a)} (h : IsDec Hom X Z j q)
    {io : ∀ a b, N (S a b) →ₗ[ℂ] N (Z a)} {pr : ∀ a b, N (Z a) →ₗ[ℂ] N (S a b)}
    (h2 : ∀ a, IsDec Hom (Z a) (S a) (io a) (pr a)) :
    IsDec Hom X (fun p => S (e p).1 (e p).2) (fun p => j (e p).1 ∘ₗ io (e p).1 (e p).2)
      (fun p => pr (e p).1 (e p).2 ∘ₗ q (e p).1) := by
  exact {
    io_hom p := hc.comp _ _ _ _ _ ((h2 _).io_hom _) (h.io_hom _)
    pr_hom p := hc.comp _ _ _ _ _ (h.pr_hom _) ((h2 _).pr_hom _)
    sum := by
      rw [Equiv.sum_comp e (fun p : A × B => (j p.1 ∘ₗ io p.1 p.2) ∘ₗ (pr p.1 p.2 ∘ₗ q p.1)),
        Fintype.sum_prod_type, ← h.sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ext x
      have := congrArg (fun f => j a (f (q a x))) (h2 a).sum
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum] using this
    pr_io p := by
      ext x
      have h1 := LinearMap.congr_fun (h.pr_io (e p).1) (io (e p).1 (e p).2 x)
      have h3 := LinearMap.congr_fun ((h2 (e p).1).pr_io (e p).2) x
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h3 ⊢
      rw [h1, h3]
    pr_io_ne p p' hne := by
      have hne' : e p ≠ e p' := fun hh => hne (e.injective hh)
      generalize e p = s at hne'
      generalize e p' = s' at hne'
      obtain ⟨a, b⟩ := s
      obtain ⟨a', b'⟩ := s'
      ext x
      by_cases ha : a = a'
      · subst ha
        have hb : b ≠ b' := fun hh => hne' (by rw [hh])
        have h1 := LinearMap.congr_fun (h.pr_io a) (io a b' x)
        have h3 := LinearMap.congr_fun ((h2 a).pr_io_ne b b' hb) x
        simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h3 ⊢
        rw [h1, h3]
      · have h1 := LinearMap.congr_fun (h.pr_io_ne a a' ha) (io a' b' x)
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 ⊢
        rw [h1, map_zero]
  }

end Lin

variable {k r : ℕ}

theorem mAct_reindex {ι ι' V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (e : ι' → ι) :
    (mAct ((1 : Matrix ι ι ℂ).submatrix e id) : (ι → V) →ₗ[ℂ] (ι' → V)) = LinearMap.funLeft ℂ V e := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct, LinearMap.funLeft_apply, Matrix.one_apply]

theorem hom_reindex (hM : MatHom) (F F' : FRep k r) (U : URep k r) (e : F'.ι ≃ F.ι)
    (h : ∀ g, F'.ρ g = (F.ρ g).submatrix e e) :
    IsHom (F, U) (F', U) (LinearMap.funLeft ℂ U.R.smSub e) := by
  have := hM k r F F' U ((1 : Matrix F.ι F.ι ℂ).submatrix e id) (fun g _ => by
    rw [h g, Matrix.submatrix_mul_equiv, Matrix.mul_one]
    have := Matrix.submatrix_mul_equiv (1 : Matrix F.ι F.ι ℂ) (F.ρ g) e (Equiv.refl _) id
    simpa using this)
  rwa [mAct_reindex] at this

theorem hom_cas (hL : HomLie) {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hX : X.1.OK) (hY : Y.1.OK) (hf : IsHom X Y f) :
    cas Y ∘ₗ f = f ∘ₗ cas X := by
  refine LinearMap.ext fun x => ?_
  have h := fun Z y => LinearMap.congr_fun (hL k r X Y f hX hY hf Z) y
  simp only [LinearMap.comp_apply] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cas, LinearMap.comp_apply, LinearMap.sum_apply, map_sum, mul_apply_eq_comp, h]

theorem dec1 (hC : HomCat) (hM : MatHom) (hT : TensHom) (F F' : FRep k r) (U : URep k r) {A : Type} [Fintype A]
    (T : A → URep k r) {io : ∀ a, M (one (T a)) →ₗ[ℂ] M (F, U)} {pr : ∀ a, M (F, U) →ₗ[ℂ] M (one (T a))}
    (h : IsDec (N := M) IsHom (F, U) (fun a => one (T a)) io pr) :
    IsDec (N := M) IsHom (F.tens F', U) (fun a => (F', T a))
      (fun a => on1 (io a) ∘ₗ LinearMap.funLeft ℂ _ (Prod.snd : Unit × F'.ι → F'.ι))
      (fun a => LinearMap.funLeft ℂ _ (fun c : F'.ι => ((), c)) ∘ₗ on1 (pr a)) := by
  exact {
    io_hom a := (hC k r).comp _ ((triv k r).tens F', T a) _ _ _
      (hom_reindex hM F' ((triv k r).tens F') (T a) (Equiv.punitProd _) (fun g => by
        ext c d; simp))
      (hT k r _ _ F' _ _ _ (h.io_hom a)).1
    pr_hom a := (hC k r).comp _ ((triv k r).tens F', T a) _ _ _
      (hT k r _ _ F' _ _ _ (h.pr_hom a)).1
      (hom_reindex hM ((triv k r).tens F') F' (T a) (Equiv.punitProd _).symm (fun g => by
        ext c d; simp))
    sum := by
      refine LinearMap.ext fun x => funext fun p => ?_
      have := congrFun (LinearMap.congr_fun h.sum (fun c => x (c, p.2))) p.1
      rw [LinearMap.sum_apply, Finset.sum_apply] at this ⊢
      exact this
    pr_io a := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io a) (fun _ => x c)) ()
    pr_io_ne a a' hne := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io_ne a a' hne) (fun _ => x c)) ()
  }

theorem dec2 (hC : HomCat) (hM : MatHom) (hT : TensHom) (F F' : FRep k r) (U : URep k r) {A : Type} [Fintype A]
    (T : A → URep k r) {io : ∀ a, M (one (T a)) →ₗ[ℂ] M (F', U)} {pr : ∀ a, M (F', U) →ₗ[ℂ] M (one (T a))}
    (h : IsDec (N := M) IsHom (F', U) (fun a => one (T a)) io pr) :
    IsDec (N := M) IsHom (F.tens F', U) (fun a => (F, T a))
      (fun a => on2 (io a) ∘ₗ LinearMap.funLeft ℂ _ (Prod.fst : F.ι × Unit → F.ι))
      (fun a => LinearMap.funLeft ℂ _ (fun c : F.ι => (c, ())) ∘ₗ on2 (pr a)) := by
  exact {
    io_hom a := (hC k r).comp _ (F.tens (triv k r), T a) _ _ _
      (hom_reindex hM F (F.tens (triv k r)) (T a) (Equiv.prodPUnit _) (fun g => by
        ext c d; simp))
      (hT k r _ _ F _ _ _ (h.io_hom a)).2
    pr_hom a := (hC k r).comp _ (F.tens (triv k r), T a) _ _ _
      (hT k r _ _ F _ _ _ (h.pr_hom a)).2
      (hom_reindex hM (F.tens (triv k r)) F (T a) (Equiv.prodPUnit _).symm (fun g => by
        ext c d; simp))
    sum := by
      refine LinearMap.ext fun x => funext fun p => ?_
      have := congrFun (LinearMap.congr_fun h.sum (fun c => x (p.1, c))) p.2
      rw [LinearMap.sum_apply, Finset.sum_apply] at this ⊢
      exact this
    pr_io a := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io a) (fun _ => x c)) ()
    pr_io_ne a a' hne := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io_ne a a' hne) (fun _ => x c)) ()
  }

theorem decTens : HomCat → MatHom → TensHom → HomLie → OKTriv → DecTens := by
  intro hC hM hT hL hO k r F F' U hF hF'
  refine ⟨fun A B _ _ T S c ⟨io, pr, h⟩ h2 hc => ?_, fun A B _ _ T S c ⟨io, pr, h⟩ h2 hc => ?_⟩
  · choose io2 pr2 h2 using h2
    refine ⟨_, _, dec_comp (hC k r) (Equiv.refl (A × B)) (S := fun a b => one (S (a, b)))
      (dec1 hC hM hT F F' U T h) h2, fun p => ?_⟩
    have h3 := hom_cas hL (X := one (T p.1)) (Y := (F, U)) (hO k r) hF (h.io_hom p.1)
    rw [hc, LinearMap.comp_smul, LinearMap.comp_id] at h3
    refine LinearMap.ext fun x => funext fun s => ?_
    exact congrFun (LinearMap.congr_fun h3 (fun _ => io2 p.1 p.2 x s.2)) s.1
  · choose io2 pr2 h2 using h2
    refine ⟨_, _, dec_comp (hC k r) (Equiv.prodComm A B) (S := fun b a => one (S (a, b)))
      (dec2 hC hM hT F F' U T h) h2, fun p => ?_⟩
    have h3 := hom_cas hL (X := one (T p.2)) (Y := (F', U)) (hO k r) hF' (h.io_hom p.2)
    rw [hc, LinearMap.comp_smul, LinearMap.comp_id] at h3
    refine LinearMap.ext fun x => funext fun s => ?_
    exact congrFun (LinearMap.congr_fun h3 (fun _ => io2 p.2 p.1 x s.1)) s.2

end GlobalTheory.CompanionTheory.ZuckDecTens

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLawsStatement
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_of_tensor_from_hom_laws : HomCat → MatHom → TensHom → HomLie → OKTriv → DecTens := by
  first | exact @GlobalTheory.CompanionTheory.ZuckDecTens.decTens | exact GlobalTheory.CompanionTheory.ZuckDecTens.decTens | (intros; apply GlobalTheory.CompanionTheory.ZuckDecTens.decTens <;> assumption)
end
end
