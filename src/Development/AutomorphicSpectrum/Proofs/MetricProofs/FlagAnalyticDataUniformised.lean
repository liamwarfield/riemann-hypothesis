module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecond
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCUnif
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticAtFlagPt
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsHoloOnOfGerm
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_unif

section Gen

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_inv [CompactSpace Y] [T2Space X] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (π : Y → X)
    (hπ : HoloMap B A π) (hd : IsDegreeOff A B π 1 ∅) (hb : Function.Bijective π) :
    ∃ σ : X → Y, (∀ x, π (σ x) = x) ∧ (∀ y, σ (π y) = y) ∧ HoloMap A B σ ∧
      ∀ x k j, x ∈ (A.chart k).source → σ x ∈ (B.chart j).source →
        Function.Injective (fderiv ℂ (B.chart j ∘ σ ∘ (A.chart k).symm) (A.chart k x)) := by
  obtain ⟨hπc, hπa⟩ := hπ
  obtain ⟨-, -, -, -, -, hdd⟩ := hd
  let Φ : Y ≃ₜ X := (show Continuous (Equiv.ofBijective π hb) from hπc).homeoOfEquivCompactToT2
  let Ψ : Fin A.n → Fin B.n → OpenPartialHomeomorph (Fin e → ℂ) (Fin e → ℂ) :=
    fun i j => (B.chart j).symm.trans (Φ.toOpenPartialHomeomorph.trans (A.chart i))
  have key : ∀ i j z, z ∈ (Ψ i j).target →
      AnalyticAt ℂ (Ψ i j).symm z ∧ Function.Injective (fderiv ℂ (Ψ i j).symm z) := by
    intro i j z hz
    have hw : (Ψ i j).symm z ∈ (Ψ i j).source := (Ψ i j).map_target hz
    have han : AnalyticAt ℂ (Ψ i j) ((Ψ i j).symm z) := hπa j i _ ⟨hw.1, hw.2.2⟩
    have hdet : LinearMap.det (fderiv ℂ (Ψ i j) ((Ψ i j).symm z) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 :=
      hdd j i _ hw.1 (by simp) hw.2.2
    let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) :=
      (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv
    have hL : fderiv ℂ (Ψ i j) ((Ψ i j).symm z) = (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :=
      ContinuousLinearMap.ext fun v => rfl
    have hsymm : AnalyticAt ℂ (Ψ i j).symm z := (Ψ i j).analyticAt_symm hz han hL
    have hder : HasFDerivAt (Ψ i j).symm (L.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) z :=
      (Ψ i j).hasFDerivAt_symm hz (hL ▸ han.differentiableAt.hasFDerivAt)
    refine ⟨hsymm, ?_⟩
    rw [hder.fderiv]
    exact L.symm.injective
  refine ⟨⇑Φ.symm, fun x => Φ.apply_symm_apply x, fun y => Φ.symm_apply_apply y,
    ⟨Φ.symm.continuous, ?_⟩, ?_⟩
  · intro i j z hz
    exact (key i j z ⟨⟨hz.1, Set.mem_univ _⟩, hz.2⟩).1
  · intro x k j hxk hxj
    have hz : A.chart k x ∈ (Ψ k j).target := by
      refine ⟨⟨(A.chart k).map_source hxk, Set.mem_univ _⟩, ?_⟩
      show Φ.symm ((A.chart k).symm (A.chart k x)) ∈ (B.chart j).source
      rw [(A.chart k).left_inv hxk]
      exact hxj
    exact (key k j _ hz).2

theorem holoOn_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h) {W : Set X}
    {f : X → ℂ} (hf : A.HoloOn W f) : B.HoloOn (h ⁻¹' W) (fun y => f (h y)) := by
  intro j z hz
  obtain ⟨hzt, hzW⟩ := hz
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm z))
  obtain ⟨hhc, hha⟩ := hh
  have hin : AnalyticAt ℂ ((A.chart k) ∘ h ∘ (B.chart j).symm) z := hha j k z ⟨hzt, hk⟩
  have hout : AnalyticAt ℂ (f ∘ (A.chart k).symm) (((A.chart k) ∘ h ∘ (B.chart j).symm) z) := by
    apply hf k
    refine ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k (h ((B.chart j).symm z))) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hzW
  have hev : ∀ᶠ w in 𝓝 z, h ((B.chart j).symm w) ∈ (A.chart k).source := by
    have hc : ContinuousAt (h ∘ (B.chart j).symm) z :=
      hhc.continuousAt.comp ((B.chart j).continuousAt_symm hzt)
    exact hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
  refine (hout.comp hin).congr ?_
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply]
  rw [(A.chart k).left_inv hw]

theorem holoOn_mono {A : FinHolAtlas e X} {W W' : Set X} {f : X → ℂ} (h : A.HoloOn W f) (s : W' ⊆ W) :
    A.HoloOn W' f := by
  intro j
  exact (h j).mono (fun z hz => ⟨hz.1, s hz.2⟩)

theorem holoOn_at {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) {x : X} (hx : x ∈ W) {k : Fin A.n}
    (hk : x ∈ (A.chart k).source) : AnalyticAt ℂ (fun w => f ((A.chart k).symm w)) (A.chart k x) := by
  have := h k (A.chart k x) ⟨(A.chart k).map_source hk, by
    show (A.chart k).symm (A.chart k x) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hx⟩
  exact this

theorem exists_holoOn_of_germ (A : FinHolAtlas e X) {x : X} {k : Fin A.n} (hk : x ∈ (A.chart k).source)
    {f : X → ℝ} {H : (Fin e → ℂ) → ℂ} (hH : AnalyticAt ℂ H (A.chart k x))
    (hf : ∀ᶠ w in 𝓝 (A.chart k x), f ((A.chart k).symm w) = (H w).re) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, f y = (G y).re := by
  have hev : ∀ᶠ w in 𝓝 (A.chart k x), AnalyticAt ℂ H w ∧ f ((A.chart k).symm w) = (H w).re :=
    hH.eventually_analyticAt.and hf
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.mp hev
  refine ⟨(A.chart k).source ∩ (A.chart k) ⁻¹' U, (A.chart k).isOpen_inter_preimage hUo, ⟨hk, hxU⟩,
    fun y => H (A.chart k y), ?_, ?_⟩
  · intro j z hz
    obtain ⟨hzt, hzs, hzU⟩ := hz
    have hin : AnalyticAt ℂ ((A.chart k) ∘ (A.chart j).symm) z := A.holo j k z ⟨hzt, hzs⟩
    have hout : AnalyticAt ℂ H (((A.chart k) ∘ (A.chart j).symm) z) := (hU _ hzU).1
    exact hout.comp hin
  · rintro y ⟨hy, hyU⟩
    have := (hU _ hyU).2
    rwa [(A.chart k).left_inv hy] at this

theorem isOpen_ne {A : FinHolAtlas e X} {W : Set X} (hW : IsOpen W) {T : Type} [Finite T] {f : T → X → ℂ}
    (hf : ∀ t, A.HoloOn W (f t)) : IsOpen {y | y ∈ W ∧ ∀ t, f t y ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyW, hy⟩
  obtain ⟨k, hk⟩ := A.cover y
  have hcont : ∀ t, ContinuousAt (f t) y := by
    intro t
    have han : AnalyticAt ℂ (f t ∘ (A.chart k).symm) (A.chart k y) :=
      hf t k (A.chart k y) ⟨(A.chart k).map_source hk, by
        show (A.chart k).symm (A.chart k y) ∈ W
        rw [(A.chart k).left_inv hk]
        exact hyW⟩
    have hc : ContinuousAt ((f t ∘ (A.chart k).symm) ∘ (A.chart k)) y :=
      han.continuousAt.comp ((A.chart k).continuousAt hk)
    refine hc.congr ?_
    filter_upwards [(A.chart k).open_source.mem_nhds hk] with z hz
    simp only [Function.comp_apply, (A.chart k).left_inv hz]
  have hev : ∀ᶠ z in 𝓝 y, ∀ t, f t z ≠ 0 := by
    rw [Filter.eventually_all]
    intro t
    exact (hcont t).eventually_ne (hy t)
  filter_upwards [hW.mem_nhds hyW, hev] with z hz1 hz2
  exact ⟨hz1, hz2⟩

end Gen

section Mat

variable {N j : ℕ}

theorem lower_left_zero {H X D : Matrix (Fin N) (Fin N) ℂ} (hH : IsBlockDiag j H) (hd : H.det ≠ 0)
    (hD : IsBlockDiag j D) (ht : (H⁻¹ * (X * H + D)).BlockTriangular id) (a b : Fin N) (ha : N - j ≤ (a : ℕ))
    (hb : (b : ℕ) < N - j) : X a b = 0 := by
  classical
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hd
  letI : Invertible H := Matrix.invertibleOfIsUnitDet _ hunit
  have h1 : H.BlockTriangular (fun i : Fin N => if (i : ℕ) < N - j then 0 else 1) := by
    intro r s hrs
    apply hH
    by_cases hr : (r : ℕ) < N - j <;> by_cases hs : (s : ℕ) < N - j <;> simp [hr, hs] at hrs ⊢
  have h2 : H.BlockTriangular (fun i : Fin N => if (i : ℕ) < N - j then 1 else 0) := by
    intro r s hrs
    apply hH
    by_cases hr : (r : ℕ) < N - j <;> by_cases hs : (s : ℕ) < N - j <;> simp [hr, hs] at hrs ⊢
  have g1 := Matrix.blockTriangular_inv_of_blockTriangular h1
  have g2 := Matrix.blockTriangular_inv_of_blockTriangular h2
  have hI : ∀ r s : Fin N, ¬((r : ℕ) < N - j ↔ (s : ℕ) < N - j) → H⁻¹ r s = 0 := by
    intro r s hrs
    by_cases hr : (r : ℕ) < N - j <;> by_cases hs : (s : ℕ) < N - j
    · exact absurd (iff_of_true hr hs) hrs
    · exact g2 (by simp [hr, hs])
    · exact g1 (by simp [hr, hs])
    · exact absurd (iff_of_false hr hs) hrs
  have hY : ∀ c d : Fin N, N - j ≤ (c : ℕ) → (d : ℕ) < N - j → (H⁻¹ * X * H) c d = 0 := by
    intro c d hc hdd
    have hT := ht (show d < c from Fin.lt_def.mpr (by omega))
    rw [Matrix.mul_add, Matrix.add_apply, ← Matrix.mul_assoc] at hT
    have hHD : (H⁻¹ * D) c d = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : (m : ℕ) < N - j
      · rw [hI c m (fun hiff => by have := hiff.mpr hm; omega), zero_mul]
      · rw [hD m d (fun hiff => hm (hiff.mpr hdd)), mul_zero]
    rw [hHD, add_zero] at hT
    exact hT
  have hX : X = H * (H⁻¹ * X * H) * H⁻¹ := by
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
  rw [hX, Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  by_cases hm : (m : ℕ) < N - j
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro c _
    by_cases hc : (c : ℕ) < N - j
    · rw [hH a c (fun hiff => by have := hiff.mpr hc; omega), zero_mul]
    · rw [hY c m (by omega) hm, mul_zero]
  · rw [hI m b (fun hiff => hm (hiff.mpr hb)), mul_zero]

theorem eq_zero_of_lower {L D : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) (hD : ∀ a b, a ≤ b → D a b = 0)
    (ht : (L⁻¹ * D).BlockTriangular id) : D = 0 := by
  classical
  obtain ⟨hL1, hL2⟩ := hL
  have hlow : L.BlockTriangular OrderDual.toDual :=
    fun i j hij => hL2 i j (OrderDual.toDual_lt_toDual.mp hij)
  have hunit : IsUnit L.det := by
    rw [Matrix.det_of_isLowerTriangular L hlow]
    simp [hL1]
  letI : Invertible L := Matrix.invertibleOfIsUnitDet _ hunit
  have hlow' : L⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hlow
  have hM : L⁻¹ * D = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    rcases lt_or_ge b a with hba | hab
    · exact ht hba
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun c _ => ?_)
      rcases lt_or_ge a c with hac | hca
      · rw [hlow' (OrderDual.toDual_lt_toDual.mpr hac), zero_mul]
      · rw [hD c b (hca.trans hab), mul_zero]
  have h2 := congrArg (fun M => L * M) hM
  simpa [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit] using h2

theorem fderiv_mul_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {P Q : E → Matrix (Fin N) (Fin N) ℂ}
    {w : E} (hP : ∀ a b, DifferentiableAt ℂ (fun u => P u a b) w) (hQ : ∀ a b, DifferentiableAt ℂ (fun u => Q u a b) w)
    (v : E) : (Matrix.of fun a b => fderiv ℂ (fun u => (P u * Q u) a b) w v) =
      (Matrix.of fun a b => fderiv ℂ (fun u => P u a b) w v) * Q w +
        P w * Matrix.of fun a b => fderiv ℂ (fun u => Q u a b) w v := by
  ext a b
  have h1 : HasFDerivAt (fun u => ∑ c, P u a c * Q u c b)
      (∑ c, (P w a c • fderiv ℂ (fun u => Q u c b) w + Q w c b • fderiv ℂ (fun u => P u a c) w)) w :=
    HasFDerivAt.fun_sum fun c _ => (hP a c).hasFDerivAt.fun_mul (hQ c b).hasFDerivAt
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [h1.fderiv, ← Finset.sum_add_distrib]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

end Mat

end PositivityTheory.Xgp.c_unif
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace PositivityTheory.Xgp.c_unif

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n : ℕ}

theorem analyticAt_flagPt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : FrameData ι Ψ N M.Ω M.blk)
    {b : E → (Σ k, baseIdx ι M.blk k) → ℂ} {h : Ψ → E → Matrix (Fin N) (Fin N) ℂ} {w : E}
    (hb : ∀ q, AnalyticAt ℂ (fun u => b u q) w) (hv : ∀ q I, AnalyticAt ℂ (fun u => valAt M.x (F.u q I) (b u)) w)
    (hh : ∀ τ r s, AnalyticAt ℂ (fun u => h τ u r s) w) (q : Σ k, ι k) :
    AnalyticAt ℂ (fun u => FC.flagPt M F (b u) (fun τ => h τ u) q) w := by
  by_cases hk : ∀ p, M.blk p ≠ some q.1
  · simp only [FC.flagPt, dif_pos hk]
    exact hb _
  · simp only [FC.flagPt, dif_neg hk]
    exact Finset.analyticAt_fun_sum _ fun I _ => (hv q I).mul
      (Fib.analyticAt_minorIJ_of_entries _ w (hh _) _ _)

variable (BM : BaseMetric M n) {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {pr : X → BM.Rb.X}

theorem bvec_holo (hp : HoloMap A BM.Rb.A pr) {W : Set X} (hW : IsOpen W) {l : Fin BM.q}
    (hl : ∀ x ∈ W, pr x ∈ BM.O l) :
    (∀ q, A.HoloOn W fun x => FC.bvec BM l (pr x) q) ∧
      ∀ s : M.Ω, (∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) s) →
        A.HoloOn W fun x => valAt M.x s (FC.bvec BM l (pr x)) := by
  have key := fun k => GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l e ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W)
    (pr ∘ (A.chart k).symm) ((A.chart k).isOpen_inter_preimage_symm hW)
    (hp.1.comp_continuousOn ((A.chart k).continuousOn_symm.mono Set.inter_subset_left))
    (fun m => (hp.2 k m).mono fun t ht => ⟨ht.1.1, ht.2⟩) (fun u hu => hl _ hu.2)
  exact ⟨fun q k => (key k).1 q, fun s hs k => (key k).2 s hs⟩

theorem step_of_orbit {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ} {z : (Σ k, ι k) → ℂ}
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (ho : SameOrbit z (FC.flagPt M F b h)) (p : Ψ × Fin N) (k : K)
    (hk : M.blk p = some k) : ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k,
      z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p.1) I (stepCols N j p.2) := by
  obtain ⟨c, hc, rfl⟩ := ho
  exact ⟨c k, hc k, fun m => by rw [← FC.flagPt_step M F b h hk m]⟩

theorem lowMat_props (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : IsBlockDiag j (lowMat c τ) ∧ IsLowerUni (lowMat c τ) :=
  ⟨fun a b h => (dif_neg fun e => h e.2).trans (if_neg fun e => h (by rw [e])),
    fun _ => (dif_neg fun e => lt_irrefl _ e.1).trans (if_pos rfl),
    fun _ _ h => (dif_neg fun e => lt_asymm h e.1).trans (if_neg h.ne)⟩

theorem lowMat_eq {c : LowIdx Ψ N j → ℂ} {τ : Ψ} {L : Matrix (Fin N) (Fin N) ℂ} (hb : IsBlockDiag j L)
    (hL : IsLowerUni L) (h : ∀ (a b : Fin N) (e : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)), c ⟨(τ, a, b), e⟩ = L a b) :
    lowMat c τ = L := by
  ext a b
  unfold lowMat
  split_ifs with h1 h2
  · exact h a b h1
  · rw [h2, hL.1]
  · rcases lt_or_gt_of_ne h2 with e | e
    · exact (hL.2 a b e).symm
    · exact (hb a b fun e' => h1 ⟨e, e'⟩).symm

theorem exists_holo_flags (hp : HoloMap A BM.Rb.A pr) {W : Set X} (hW : IsOpen W) {z : X → (Σ k, ι k) → ℂ}
    (hz : ∀ q, A.HoloOn W fun x => z x q) (hm : ∀ x ∈ W, z x ∈ mcPts (mCoordIdeal y))
    (hb : ∀ x ∈ W, SameOrbit (basePart M.blk (z x)) (BM.Rb.lift (pr x) (pr x))) {l : Fin BM.q}
    (hl : ∀ x ∈ W, pr x ∈ BM.O l) {x₀ : X} (hx₀ : x₀ ∈ W) :
    ∃ W' : Set X, IsOpen W' ∧ x₀ ∈ W' ∧ W' ⊆ W ∧ ∃ (h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ)
      (L : Ψ → X → Matrix (Fin N) (Fin N) ℂ), (∀ τ, IsBlockDiag j (h₀ τ) ∧ (h₀ τ).det ≠ 0) ∧
      (∀ τ a b, A.HoloOn W' fun x => L τ x a b) ∧ (∀ τ x, IsBlockDiag j (L τ x) ∧ IsLowerUni (L τ x)) ∧
      ∀ x ∈ W', SameOrbit (z x) (FC.flagPt M (BM.F l) (FC.bvec BM l (pr x)) fun τ => h₀ τ * L τ x) := by
  have hj := M.j_le
  have hF := BM.isFrame l
  have hg := GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM l
  have hex := fun x (hx : x ∈ W) => GlobalTheory.T.exists_flag_point_in_orbit K ι Φ y Ψ N j M n BM l (pr x) (hl x hx) (z x) (hm x hx) (hb x hx)
  obtain ⟨h₀, hh₀, ho₀⟩ := hex x₀ hx₀
  let tw : Fin N → K → Ψ → Finset (Fin N) → X → ℂ := fun i k τ J x =>
    twMinor M (BM.F l) (FC.bvec BM l (pr x)) i k (h₀ τ)⁻¹ (z x) J
  have htw : ∀ i k τ J, A.HoloOn W (tw i k τ J) := by
    intro i k τ J m t ht
    have hv := fun I (q : Σ k, ι k) => (bvec_holo BM hp hW hl).2 ((BM.F l).u' I q)
      (fun b hb => ((hg b hb).2.1.2.1 q I).2) m t ht
    show AnalyticAt ℂ (fun w => tw i k τ J ((A.chart m).symm w)) t
    simp only [tw, twMinor, pluck]
    exact Finset.analyticAt_fun_sum _ fun I _ => analyticAt_const.mul
      (Finset.analyticAt_fun_sum _ fun r _ => (hv I ⟨k, r⟩).mul (hz ⟨k, r⟩ m t ht))
  let T := {pk : (Ψ × Fin N) × K // M.blk pk.1 = some pk.2}
  let den : T → X → ℂ := fun t => tw t.1.1.2 t.1.2 t.1.1.1 (stepCols N j t.1.1.2)
  have tweq : ∀ x ∈ W, ∀ h' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (h' τ)) →
      SameOrbit (z x) (FC.flagPt M (BM.F l) (FC.bvec BM l (pr x)) h') → ∀ t : T, ∃ α : ℂ, α ≠ 0 ∧
        den t x = α * minorIJ ((h₀ t.1.1.1)⁻¹ * h' t.1.1.1) (stepCols N j t.1.1.2) (stepCols N j t.1.1.2) := by
    intro x hx h' hb' ho t
    obtain ⟨α, hα, hzk⟩ := step_of_orbit ho t.1.1 t.1.2 t.2
    exact ⟨α, hα, GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M (BM.F l) _ t.1.1 t.1.2 _ _ _ α _ hF (hg _ (hl x hx)).1
      (hg _ (hl x hx)).2.1 t.2 (hb' _) hzk⟩
  refine ⟨{x | x ∈ W ∧ ∀ t, den t x ≠ 0}, isOpen_ne hW fun t => htw _ _ _ _, ⟨hx₀, fun t => ?_⟩, fun x hx => hx.1, h₀,
    fun τ x => lowMat (fun q : LowIdx Ψ N j =>
      lowRead M (BM.F l) (FC.bvec BM l (pr x)) h₀ (z x) q.1.1 q.1.2.1 q.1.2.2) τ, hh₀, fun τ a b => ?_,
    fun τ x => lowMat_props _ _, fun x hx => ?_⟩
  · obtain ⟨α, hα, e⟩ := tweq x₀ hx₀ h₀ (fun τ => (hh₀ τ).1) ho₀ t
    rw [e, Matrix.nonsing_inv_mul _ (hh₀ _).2.isUnit, CPts.minorIJ_one, mul_one]
    exact hα
  · by_cases h1 : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · simp only [lowMat, dif_pos h1, lowRead]
      rcases hk : M.blk (τ, stepOf N j b) with _ | k
      · exact fun _ => analyticOnNhd_const
      · intro m t ht
        exact AnalyticAt.div (htw (stepOf N j b) k τ _ m t ⟨ht.1, ht.2.1⟩) (htw (stepOf N j b) k τ _ m t ⟨ht.1, ht.2.1⟩)
          (ht.2.2 ⟨((τ, stepOf N j b), k), hk⟩)
    · simp only [lowMat, dif_neg h1]
      exact fun _ => analyticOnNhd_const
  · obtain ⟨h', hh', ho⟩ := hex x hx.1
    have hLU : ∀ τ, ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧
        U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ (h₀ τ)⁻¹ * h' τ = L * U := by
      intro τ
      refine GlobalTheory.T.block_LU_factorization N j _ hj (((hh₀ τ).1.inv (hh₀ τ).2.isUnit).mul (hh' τ).1) ?_ fun i hi => ?_
      · rw [Matrix.det_mul]
        exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hh₀ τ).2.isUnit).ne_zero (hh' τ).2
      · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 fun e => (M.blk_none (τ, i)).1 e hi
        obtain ⟨α, -, e⟩ := tweq x hx.1 h' (fun τ => (hh' τ).1) ho ⟨((τ, i), k), hk⟩
        have := hx.2 ⟨((τ, i), k), hk⟩
        rw [e] at this
        exact right_ne_zero_of_mul this
    choose L U hLb hLu hUb hUt hUd hLU using hLU
    have e1 : ∀ τ, lowMat (fun q : LowIdx Ψ N j =>
        lowRead M (BM.F l) (FC.bvec BM l (pr x)) h₀ (z x) q.1.1 q.1.2.1 q.1.2.2) τ = L τ := fun τ =>
      lowMat_eq (hLb τ) (hLu τ) fun a b e => LowRead.main K ι Φ y Ψ N j M (BM.F l) _ h₀ τ a b (z x) (h' τ) (L τ) (U τ)
        hF (hg _ (hl x hx.1)).1 (hg _ (hl x hx.1)).2.1 (hh' τ).1 (hLU τ) (hLb τ) (hLu τ) (hUb τ) (hUt τ)
        (fun c _ => hUd τ c) e.1 e.2 fun k hk => step_of_orbit ho (τ, stepOf N j b) k hk
    simp only [e1]
    have e2 : h' = fun τ => (h₀ τ * L τ) * U τ := funext fun τ => by
      rw [Matrix.mul_assoc, ← hLU, Matrix.mul_nonsing_inv_cancel_left _ _ (hh₀ τ).2.isUnit]
    refine orbit_trans ho ?_
    rw [e2]
    refine GlobalTheory.T.flag_point_triangular_change_orbit K ι Φ y Ψ N j M _ _ (fun τ => h₀ τ * L τ) U fun τ => ⟨hUb τ, hUt τ, ?_⟩
    rw [Matrix.det_of_upperTriangular (hUt τ)]
    exact Finset.prod_ne_zero_iff.2 fun c _ => hUd τ c

end PositivityTheory.Xgp.c_unif
end
end

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticAtDetFac
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace PositivityTheory.Xgp.c_unif

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}

theorem analyticAt_detFac {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin N)
    {H : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : ∀ r s, AnalyticAt ℂ (fun u => H u r s) w) :
    AnalyticAt ℂ (fun u => detFac j i (H u)) w := by
  unfold detFac
  refine AnalyticAt.mul ?_ ?_
  · split_ifs
    · exact Fib.analyticAt_minorIJ_of_entries _ w h _ _
    · exact analyticAt_const
  · split_ifs
    · exact Fib.analyticAt_minorIJ_of_entries _ w h _ _
    · exact analyticAt_const

theorem holoOn_mul {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {W : Set X}
    {P Q : X → Matrix (Fin N) (Fin N) ℂ} (hP : ∀ a b, A.HoloOn W fun x => P x a b)
    (hQ : ∀ a b, A.HoloOn W fun x => Q x a b) (a b : Fin N) : A.HoloOn W fun x => (P x * Q x) a b := by
  intro k t ht
  show AnalyticAt ℂ (fun w => (P ((A.chart k).symm w) * Q ((A.chart k).symm w)) a b) t
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun c _ => (hP a c k t ht).mul (hQ c b k t ht)

theorem period_chart (FA : FlagAn BM d) (hsurj : Function.Surjective FA.Re.π) {l : Fin BM.q} {Vb : Set BM.Rb.X}
    {Pi : Ψ → BM.Rb.X → Matrix (Fin N) (Fin N) ℂ} (hPi : IsPeriodOn BM.Rb.A j Vb Pi (BM.G l)) {W : Set FA.S.X}
    (hW : IsOpen W) {x : FA.S.X} (hx : x ∈ W) (hl : ∀ x' ∈ W, FA.pr x' ∈ BM.O l \ bdry BM.s ∧ FA.pr x' ∈ Vb)
    {H : Ψ → FA.S.X → Matrix (Fin N) (Fin N) ℂ} (hH : ∀ τ a b, FA.S.A.HoloOn W fun x' => H τ x' a b)
    (hHb : ∀ τ, ∀ x' ∈ W, IsBlockDiag j (H τ x') ∧ (H τ x').det ≠ 0)
    (ho : ∀ x' ∈ W, ∀ x₀, FA.Re.π x₀ = x' →
      SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x')) fun τ => H τ x')) :
    ∃ V, IsPeriodChart (FA.S.comap some).A j (FA.S.comap some).potH x V fun τ x' => Pi τ (FA.pr x') * H τ x' := by
  have hj := M.j_le
  have hg := GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM l
  have hl1 : ∀ x' ∈ W, FA.pr x' ∈ BM.O l := fun x' h => (hl x' h).1.1
  have hbv := bvec_holo BM FA.pr_holo hW hl1
  have hst := fun (p : Ψ × Fin N) x' (hx' : x' ∈ W) => GlobalTheory.T.flag_potential_block_decomposition N j p.2 (Pi p.1 (FA.pr x'))
    (BM.G l p.1 (FA.pr x')) (H p.1 x') hj (hPi.2.2 p.1 _ (hl x' hx').2) (BM.G_pos l p.1 _ (hl x' hx').1).1
    (BM.G_pos l p.1 _ (hl x' hx').1).2 (hHb p.1 x' hx').1 (hHb p.1 x' hx').2
  obtain ⟨k, hk⟩ := FA.S.A.cover x
  set c := FA.S.A.chart k with hc
  have hO : IsOpen (c.target ∩ c.symm ⁻¹' W) := c.isOpen_inter_preimage_symm hW
  have hxO : c x ∈ c.target ∩ c.symm ⁻¹' W := ⟨c.map_source hk, by simpa [c.left_inv hk] using hx⟩
  have hsx : c.symm (c x) = x := c.left_inv hk
  have key : ∀ p : Ψ × Fin N, ∃ V : Set FA.S.X, IsOpen V ∧ x ∈ V ∧ ∃ G : FA.S.X → ℂ, FA.S.A.HoloOn V G ∧
      ∀ x' ∈ V, ((FA.S.comap some).potH p).φ x x' - stepPot N j p.2 (Pi p.1 (FA.pr x') * H p.1 x') = (G x').re := by
    intro p
    obtain ⟨H1, hH1, he1⟩ := GlobalTheory.T.local_holomorphic_lift_realisation K ι (d + 1) _ FA.S (mCoordIdeal y) FA.Re (some p) (d + 1)
      (c.target ∩ c.symm ⁻¹' W) c.symm
      (fun u => FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (c.symm u))) fun τ => H τ (c.symm u)) (c x)
      FA.J_top FA.deg_one FA.br_empty hO hxO
      (fun q u hu => analyticAt_flagPt (BM.F l) (fun q => hbv.1 q k u hu)
        (fun q I => hbv.2 _ (fun b hb => ((hg b hb).2.1.2.1 q I).1) k u hu) (fun τ r s => hH τ r s k u hu) q)
      (fun u hu => GlobalTheory.T.flag_point_in_multiprojective_points K ι Φ y Ψ N j M n BM l _ (hl1 _ hu.2) _ fun τ => hHb τ _ hu.2)
      (fun u hu x₀ h => ho _ hu.2 x₀ h)
    obtain ⟨H2, hH2, he2⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) (fun u => detFac j p.2 (H p.1 (c.symm u))) (c x)
      (analyticAt_detFac p.2 fun r s => hH p.1 r s k _ hxO)
      (CPts.detFac_ne_zero hj p.2 (hHb p.1 _ hxO.2).1 (hHb p.1 _ hxO.2).2)
    obtain ⟨H3, hH3, he3⟩ : ∃ H3 : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ H3 (c x) ∧
        ∀ᶠ u in 𝓝 (c x), Fib.upsLogAt BM l p (FA.pr (c.symm u)) = (H3 u).re := by
      by_cases hp : M.blk p = none
      · simp only [Fib.upsLogAt, if_pos hp]
        refine GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) (fun u => Fib.upsVal BM l p (FA.pr (c.symm u))) (c x) ?_
          (GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l p _ (hl1 _ hxO.2) hp)
        exact GlobalTheory.T.regular_function_analytic_on_chart _ _ M.Ω M.x ((BM.F l).υ p) (d + 1) n BM.Rb (c.target ∩ c.symm ⁻¹' W) (FA.pr ∘ c.symm) (c x)
          hO hxO (FA.pr_holo.1.comp_continuousOn (c.continuousOn_symm.mono Set.inter_subset_left))
          (fun m => (FA.pr_holo.2 k m).mono fun t ht => ⟨ht.1.1, ht.2⟩)
          ((BM.good l _ (hl1 _ hxO.2)).2.2 p hp).2.1
      · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun u => by simp [Fib.upsLogAt, hp]⟩
    refine exists_holoOn_of_germ FA.S.A hk (H := fun u => H1 u - H2 u - H3 u) ((hH1.sub hH2).sub hH3) ?_
    filter_upwards [he1, he2, he3, hO.mem_nhds hxO] with u h1 h2 h3 hu
    obtain ⟨x₀, hx₀⟩ := hsurj (c.symm u)
    have hline := GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ _ (FA.pr (c.symm u)) p (H p.1 (c.symm u))
      (hl _ hu.2).1 (ho _ hu.2 x₀ hx₀) (by rw [FC.basePart_flagPt]; exact (hg _ (hl1 _ hu.2)).2.2.2)
      (FC.exactAt_flagPt M (BM.F l) (hg _ (hl1 _ hu.2)).2.2.1 (fun τ => H τ (c.symm u)) p)
      (hHb _ _ hu.2).1 (hHb _ _ hu.2).2
    have hphi : ((FA.S.comap some).potH p).φ x (c.symm u) =
      (FA.S.th (some p)).φ x (c.symm u) + FA.S.ph (some p) (c.symm u) := rfl
    rw [hsx, FA.ref_some] at h1
    rw [hx₀, Fib.potAt] at hline
    rw [hphi, h1, (hst p _ hu.2).2, Complex.sub_re, Complex.sub_re, ← h2, ← h3]
    linarith
  choose V hVo hxV G hG hGe using key
  refine ⟨W ∩ ⋂ p, V p, hW.inter (isOpen_iInter_of_finite hVo), ⟨hx, Set.mem_iInter.2 hxV⟩, fun τ a b => ?_,
    fun τ x' hx' => ?_, fun p => ⟨G p, holoOn_mono (hG p) fun x' hx' => Set.mem_iInter.1 hx'.2 p, fun x' hx' => ?_⟩⟩
  · refine holoOn_mono (holoOn_mul (W := W) (fun a b => ?_) (hH τ) a b) Set.inter_subset_left
    exact holoOn_mono (holoOn_comp FA.pr_holo (hPi.2.1 τ a b)) fun x' hx' => (hl x' hx').2
  · exact StepBlock.inFlagDomain_mul (hPi.2.2 τ _ (hl x' hx'.1).2).1 (hHb τ x' hx'.1).1 (hHb τ x' hx'.1).2
  · have := hGe p x' (Set.mem_iInter.1 hx'.2 p)
    linarith

end PositivityTheory.Xgp.c_unif
end
end

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.NotMemOfEqTop
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace PositivityTheory.Xgp.c_unif

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}

theorem not_mem_of_eq_top {J : Ideal (MRing ι)} (hJ : J = ⊤) (z : (Σ k, ι k) → ℂ) : z ∉ mcPts J := by
  subst hJ
  exact Proj.not_mem_mcPts_top z

private theorem regAt_u_bvec (l : Fin BM.q) (q : (k : K) × ι k) (I : Finset (Fin N)) (b : BM.Rb.X)
    (hb : b ∈ BM.O l) : RegAt M.x (mCoordIdeal (FC.bvec BM l b)) ((BM.F l).u q I) := by
  have hg := BM.good l b hb
  have hne : ∀ k, BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k h =>
    hg.1 k (mem_mCoordIdeal_of_aeval_eq_zero _ (PositivityTheory.Xgp.W.isMultiHomog_X _) (by simpa using h))
  have horb : SameOrbit (FC.bvec BM l b) (BM.Rb.lift b b) :=
    ⟨fun k => (BM.Rb.lift b b ⟨k, (BM.F l).c k⟩)⁻¹, fun k => inv_ne_zero (hne k), by
      funext p; simp [FC.bvec, div_eq_inv_mul]⟩
  rw [GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit horb]
  exact (hg.2.1 q I).1

theorem eq_zero_of_still (FA : FlagAn BM d) {σ : FA.S.X → FA.Re.R.X} (hσ : HoloMap FA.S.A FA.Re.R.A σ)
    (hinj : ∀ x k m, x ∈ (FA.S.A.chart k).source → σ x ∈ (FA.Re.R.A.chart m).source →
      Function.Injective (fderiv ℂ (FA.Re.R.A.chart m ∘ σ ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x)))
    {l : Fin BM.q} {W : Set FA.S.X} (hW : IsOpen W) {x : FA.S.X} (hx : x ∈ W) (hl : FA.pr x ∈ BM.O l)
    {h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ} {L : Ψ → FA.S.X → Matrix (Fin N) (Fin N) ℂ}
    (hL : ∀ τ a b, FA.S.A.HoloOn W fun x' => L τ x' a b)
    (ho : ∀ x' ∈ W, SameOrbit (FA.Re.R.lift (σ x) (σ x'))
      (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x')) fun τ => h₀ τ * L τ x'))
    {k : Fin FA.S.A.n} (hk : x ∈ (FA.S.A.chart k).source) {kb : Fin BM.Rb.A.n}
    (hkb : FA.pr x ∈ (BM.Rb.A.chart kb).source) {v : Fin (d + 1) → ℂ}
    (hβ : fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x) v = 0)
    (hD : ∀ τ a b, fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x) v = 0) : v = 0 := by
  classical
  obtain ⟨m, hm⟩ := FA.Re.R.A.cover (σ x)
  choose p hp using (FA.Re.R.mem (σ x) (σ x) (FA.Re.R.mem_U (σ x))).1
  have hJ : FA.Re.R.lift (σ x) (σ x) ∉ mcPts FA.Re.J := not_mem_of_eq_top FA.J_top _
  have hker := FA.Re.R.immersion (σ x) hJ p hp m hm
  have hu0 : FA.S.A.chart k x ∈ (FA.S.A.chart k).target := (FA.S.A.chart k).map_source hk
  have hcx : (FA.S.A.chart k).symm (FA.S.A.chart k x) = x := (FA.S.A.chart k).left_inv hk
  set φ := (FA.Re.R.A.chart m) ∘ σ ∘ (FA.S.A.chart k).symm with hφ
  have hφd : DifferentiableAt ℂ φ (FA.S.A.chart k x) :=
    (hσ.2 k m (FA.S.A.chart k x) ⟨hu0, by simpa [hcx] using hm⟩).differentiableAt
  have hφu0 : φ (FA.S.A.chart k x) = FA.Re.R.A.chart m (σ x) := by simp [φ, hcx]
  set F : (Fin (d + 1) → ℂ) → ((k : K) × ι k → ℂ) :=
    fun w => affCoord p (FA.Re.R.lift (σ x) ((FA.Re.R.A.chart m).symm w)) with hF
  have hFd : DifferentiableAt ℂ F (φ (FA.S.A.chart k x)) := by
    rw [hφu0, differentiableAt_pi]
    intro q
    have h1 := holoOn_at (FA.Re.R.holo (σ x) q) (FA.Re.R.mem_U (σ x)) hm
    have h2 := holoOn_at (FA.Re.R.holo (σ x) ⟨q.1, p q.1⟩) (FA.Re.R.mem_U (σ x)) hm
    simp only [F, affCoord]
    refine (h1.div h2 ?_).differentiableAt
    simpa [(FA.Re.R.A.chart m).left_inv hm] using hp q.1
  set β := (BM.Rb.A.chart kb) ∘ FA.pr ∘ (FA.S.A.chart k).symm with hβdef
  set Λ : (Fin (d + 1) → ℂ) → (Ψ → Fin N → Fin N → ℂ) :=
    fun u τ a b => L τ ((FA.S.A.chart k).symm u) a b with hΛdef
  set ψ : (Fin (d + 1) → ℂ) → (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) := fun u => (β u, Λ u) with hψdef
  set H : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) → ((k : K) × ι k → ℂ) := fun e =>
    affCoord p (FC.flagPt M (BM.F l) (FC.bvec BM l ((BM.Rb.A.chart kb).symm e.1))
      fun τ => h₀ τ * Matrix.of (e.2 τ)) with hH
  have hcont : ContinuousAt (FA.S.A.chart k).symm (FA.S.A.chart k x) :=
    (FA.S.A.chart k).continuousAt_symm hu0
  have hev : F ∘ φ =ᶠ[𝓝 (FA.S.A.chart k x)] H ∘ ψ := by
    have h1 : (FA.S.A.chart k).symm ⁻¹' W ∈ 𝓝 (FA.S.A.chart k x) :=
      hcont.preimage_mem_nhds (by rw [hcx]; exact hW.mem_nhds hx)
    have h2 : (FA.S.A.chart k).symm ⁻¹' (σ ⁻¹' (FA.Re.R.A.chart m).source) ∈ 𝓝 (FA.S.A.chart k x) :=
      hcont.preimage_mem_nhds (by
        rw [hcx]; exact hσ.1.continuousAt.preimage_mem_nhds ((FA.Re.R.A.chart m).open_source.mem_nhds hm))
    have h3 : (FA.S.A.chart k).symm ⁻¹' (FA.pr ⁻¹' (BM.Rb.A.chart kb).source) ∈ 𝓝 (FA.S.A.chart k x) :=
      hcont.preimage_mem_nhds (by
        rw [hcx]
        exact FA.pr_holo.1.continuousAt.preimage_mem_nhds ((BM.Rb.A.chart kb).open_source.mem_nhds hkb))
    filter_upwards [h1, h2, h3] with u hu1 hu2 hu3
    simp only [Set.mem_preimage] at hu1 hu2 hu3
    simp only [Function.comp, F, H, ψ, β, Λ, φ]
    rw [(FA.Re.R.A.chart m).left_inv hu2, (BM.Rb.A.chart kb).left_inv hu3]
    obtain ⟨cc, hcc, heq⟩ := ho _ hu1
    rw [heq]
    funext q
    simp only [affCoord]
    rw [mul_div_mul_left _ _ (hcc q.1)]
    rfl
  have hβd : DifferentiableAt ℂ β (FA.S.A.chart k x) :=
    (FA.pr_holo.2 k kb (FA.S.A.chart k x) ⟨hu0, by simpa [hcx] using hkb⟩).differentiableAt
  have hLd : ∀ τ a b, DifferentiableAt ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b)
      (FA.S.A.chart k x) := fun τ a b =>
    (holoOn_at (hL τ a b) hx hk).differentiableAt
  have hΛ : HasFDerivAt Λ (ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun a =>
      ContinuousLinearMap.pi fun b => fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b)
        (FA.S.A.chart k x)) (FA.S.A.chart k x) := by
    rw [hasFDerivAt_pi]
    intro τ
    rw [hasFDerivAt_pi]
    intro a
    rw [hasFDerivAt_pi]
    intro b
    simpa using (hLd τ a b).hasFDerivAt
  have hψ := hβd.hasFDerivAt.prodMk hΛ
  have hψv : fderiv ℂ ψ (FA.S.A.chart k x) v = 0 := by
    rw [hψ.fderiv]
    ext <;> simp [β, hβ, hD]
  have hψu0 : ψ (FA.S.A.chart k x) = (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b) := by
    simp [ψ, β, Λ, hcx]
  have hbv := bvec_holo BM (A := BM.Rb.A) (pr := id) ⟨continuous_id, fun j k' => BM.Rb.A.holo j k'⟩
    (BM.O_open l) (fun _ h => h)
  obtain ⟨cc0, hcc0, heq0⟩ := ho x hx
  have hHd : DifferentiableAt ℂ H (ψ (FA.S.A.chart k x)) := by
    rw [hψu0]
    have hb : ∀ q, AnalyticAt ℂ (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) =>
        FC.bvec BM l ((BM.Rb.A.chart kb).symm e.1) q)
        (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b) := fun q => by
      have h := holoOn_at (hbv.1 q) hl hkb
      exact AnalyticAt.comp (f := Prod.fst)
        (g := fun w => FC.bvec BM l ((BM.Rb.A.chart kb).symm w) q) h analyticAt_fst
    have hval : ∀ (q : (k : K) × ι k) (I : Finset (Fin N)), AnalyticAt ℂ
        (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) =>
          valAt M.x ((BM.F l).u q I) (FC.bvec BM l ((BM.Rb.A.chart kb).symm e.1)))
        (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b) := fun q I => by
      have h := holoOn_at (hbv.2 _ (fun b hb => regAt_u_bvec l q I b hb)) hl hkb
      exact AnalyticAt.comp (f := Prod.fst)
        (g := fun w => valAt M.x ((BM.F l).u q I) (FC.bvec BM l ((BM.Rb.A.chart kb).symm w))) h analyticAt_fst
    have hh : ∀ (τ : Ψ) (r s : Fin N), AnalyticAt ℂ
        (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => (h₀ τ * Matrix.of (e.2 τ)) r s)
        (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b) := by
      intro τ r s
      simp only [Matrix.mul_apply, Matrix.of_apply]
      have hp2 : ∀ t : Fin N, AnalyticAt ℂ (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => e.2 τ t s)
          (BM.Rb.A.chart kb (FA.pr x), fun τ a b => L τ x a b) := by
        intro t
        have e : (fun e : (Fin n → ℂ) × (Ψ → Fin N → Fin N → ℂ) => e.2 τ t s) =
            ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) s).comp
              ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) t).comp
                ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Ψ => Fin N → Fin N → ℂ) τ).comp
                  (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Ψ → Fin N → Fin N → ℂ))))) := rfl
        rw [e]
        exact ContinuousLinearMap.analyticAt _ _
      have hs := Finset.analyticAt_sum Finset.univ (fun t _ => (analyticAt_const (v := h₀ τ r t)).mul (hp2 t))
      exact hs.congr (Filter.Eventually.of_forall fun e => by simp)
    have hZ := analyticAt_flagPt (BM.F l) hb hval hh
    rw [differentiableAt_pi]
    intro q
    simp only [H, affCoord]
    refine ((hZ q).div (hZ ⟨q.1, p q.1⟩) ?_).differentiableAt
    have h1 := hp q.1
    rw [heq0] at h1
    have h2 : FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x)) (fun τ => h₀ τ * L τ x) ⟨q.1, p q.1⟩ ≠ 0 :=
      right_ne_zero_of_mul h1
    simp only [(BM.Rb.A.chart kb).left_inv hkb]
    exact h2
  have hψd : DifferentiableAt ℂ ψ (FA.S.A.chart k x) := hψ.differentiableAt
  have key : fderiv ℂ F (φ (FA.S.A.chart k x)) (fderiv ℂ φ (FA.S.A.chart k x) v) = 0 := by
    have e1 := fderiv_comp (FA.S.A.chart k x) hFd hφd
    have e2 := fderiv_comp (FA.S.A.chart k x) hHd hψd
    calc fderiv ℂ F (φ (FA.S.A.chart k x)) (fderiv ℂ φ (FA.S.A.chart k x) v)
        = fderiv ℂ (F ∘ φ) (FA.S.A.chart k x) v := by rw [e1]; rfl
      _ = fderiv ℂ (H ∘ ψ) (FA.S.A.chart k x) v := by rw [hev.fderiv_eq]
      _ = fderiv ℂ H (ψ (FA.S.A.chart k x)) (fderiv ℂ ψ (FA.S.A.chart k x) v) := by rw [e2]; rfl
      _ = 0 := by rw [hψv, map_zero]
  have hz : fderiv ℂ φ (FA.S.A.chart k x) v = 0 := by
    rw [hφu0] at key
    have hinjF := LinearMap.ker_eq_bot.mp hker
    exact hinjF (by rw [map_zero]; exact key)
  exact hinj x k m hk hm (by rw [hz, map_zero])

private theorem isBlockDiag_mul' {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) (hB : IsBlockDiag j B) :
    IsBlockDiag j (A * B) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
  · rw [hB c b (fun h' => hab (h.trans h')), mul_zero]
  · rw [hA a c h, zero_mul]

theorem flag_immersion (FA : FlagAn BM d) {σ : FA.S.X → FA.Re.R.X} (hσ : HoloMap FA.S.A FA.Re.R.A σ)
    (hinj : ∀ x k m, x ∈ (FA.S.A.chart k).source → σ x ∈ (FA.Re.R.A.chart m).source →
      Function.Injective (fderiv ℂ (FA.Re.R.A.chart m ∘ σ ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x)))
    {l : Fin BM.q} {Vb : Set BM.Rb.X} {Pi : Ψ → BM.Rb.X → Matrix (Fin N) (Fin N) ℂ}
    (hPi : IsPeriodOn BM.Rb.A j Vb Pi (BM.G l)) {W : Set FA.S.X} (hW : IsOpen W) {x : FA.S.X} (hx : x ∈ W)
    (hl : FA.pr x ∈ BM.O l) (hVb : FA.pr x ∈ Vb)
    {h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ} {L : Ψ → FA.S.X → Matrix (Fin N) (Fin N) ℂ}
    (hh₀ : ∀ τ, IsBlockDiag j (h₀ τ) ∧ (h₀ τ).det ≠ 0)
    (hL : ∀ τ a b, FA.S.A.HoloOn W fun x' => L τ x' a b) (hLb : ∀ τ x', IsBlockDiag j (L τ x') ∧ IsLowerUni (L τ x'))
    (ho : ∀ x' ∈ W, SameOrbit (FA.Re.R.lift (σ x) (σ x'))
      (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x')) fun τ => h₀ τ * L τ x'))
    (himm : ∀ k, FA.pr x ∈ (BM.Rb.A.chart k).source → ∀ v : Fin n → ℂ,
      (∀ τ (a b : Fin N), N - j ≤ (a : ℕ) → (b : ℕ) < N - j → ((Pi τ (FA.pr x))⁻¹ * Matrix.of fun a b =>
        fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart k).symm w) a b) (BM.Rb.A.chart k (FA.pr x)) v) a b = 0) → v = 0) :
    IsFlagImmersionAt FA.S.A (fun τ x' => Pi τ (FA.pr x') * (h₀ τ * L τ x')) x := by
  intro k hk v hv
  obtain ⟨kb, hkb⟩ := BM.Rb.A.cover (FA.pr x)
  have hφ0 : (FA.S.A.chart k).symm (FA.S.A.chart k x) = x := (FA.S.A.chart k).left_inv hk
  have hu0 : FA.S.A.chart k x ∈ (FA.S.A.chart k).target ∩
      (FA.S.A.chart k).symm ⁻¹' (FA.pr ⁻¹' (BM.Rb.A.chart kb).source) :=
    ⟨(FA.S.A.chart k).map_source hk, by simp only [Set.mem_preimage, hφ0]; exact hkb⟩
  have hβd : DifferentiableAt ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x) :=
    (FA.pr_holo.2 k kb _ hu0).differentiableAt
  have hopen : IsOpen ((FA.S.A.chart k).target ∩
      (FA.S.A.chart k).symm ⁻¹' (FA.pr ⁻¹' (BM.Rb.A.chart kb).source)) :=
    (FA.S.A.chart k).continuousOn_symm.isOpen_inter_preimage (FA.S.A.chart k).open_target
      ((BM.Rb.A.chart kb).open_source.preimage FA.pr_holo.1)
  have hchain : ∀ τ a b, fderiv ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) =
      (fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b) (BM.Rb.A.chart kb (FA.pr x))).comp
        (fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x)) ∧
      DifferentiableAt ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) := by
    intro τ a b
    have hG := (holoOn_at (hPi.2.1 τ a b) hVb hkb).differentiableAt
    have hG' : DifferentiableAt ℂ (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b)
        ((BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x)) := by
      simpa only [Function.comp, hφ0] using hG
    have heq : (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) =ᶠ[𝓝 (FA.S.A.chart k x)]
        (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b) ∘ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) := by
      filter_upwards [hopen.mem_nhds hu0] with u hu
      simp only [Function.comp, (BM.Rb.A.chart kb).left_inv hu.2]
    refine ⟨?_, (hG'.comp _ hβd).congr_of_eventuallyEq heq⟩
    rw [heq.fderiv_eq, fderiv_comp _ hG' hβd]
    simp only [Function.comp, hφ0]
  have hLd : ∀ τ a b, DifferentiableAt ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x) :=
    fun τ a b => (holoOn_at (hL τ a b) hx hk).differentiableAt
  have hLconst : ∀ τ (a b : Fin N), (a ≤ b ∨ ¬((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) →
      fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x) v = 0 := by
    intro τ a b hab
    have : (fun u => L τ ((FA.S.A.chart k).symm u) a b) = fun _ => if a = b then (1 : ℂ) else 0 := by
      funext u
      rcases hab with hab | hab
      · rcases hab.lt_or_eq with h | h
        · rw [(hLb τ _).2.2 a b h, if_neg h.ne]
        · subst h; rw [(hLb τ _).2.1 a, if_pos rfl]
      · have hne : a ≠ b := by rintro rfl; exact hab Iff.rfl
        rw [(hLb τ _).1 a b hab, if_neg hne]
    rw [this]; simp
  have hprod : ∀ τ, (Matrix.of fun a b => fderiv ℂ (fun u => (Pi τ (FA.pr ((FA.S.A.chart k).symm u)) *
      (h₀ τ * L τ ((FA.S.A.chart k).symm u))) a b) (FA.S.A.chart k x) v) =
      (Matrix.of fun a b => fderiv ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) v) *
        (h₀ τ * L τ x) +
      Pi τ (FA.pr x) * (h₀ τ * Matrix.of fun a b => fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b)
        (FA.S.A.chart k x) v) := by
    intro τ
    have hQd : ∀ a b, DifferentiableAt ℂ (fun u => (h₀ τ * L τ ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) := by
      intro a b
      simp only [Matrix.mul_apply]
      exact DifferentiableAt.fun_sum fun c _ => (differentiableAt_const _).mul (hLd τ c b)
    rw [fderiv_mul_of (fun a b => (hchain τ a b).2) hQd v,
      fderiv_mul_of (P := fun _ => h₀ τ) (fun a b => differentiableAt_const _) (hLd τ) v]
    have h0 : (Matrix.of fun a b => fderiv ℂ (fun _ : Fin (d+1) → ℂ => h₀ τ a b) (FA.S.A.chart k x) v) = 0 := by
      ext a b; simp
    rw [h0, Matrix.zero_mul, zero_add, hφ0]
  have hdet : ∀ τ, IsUnit (Pi τ (FA.pr x)).det := fun τ => (hPi.2.2 τ _ hVb).1.1
  have hLdet : ∀ τ (x' : FA.S.X), (L τ x').det = 1 := by
    intro τ x'
    rw [Matrix.det_of_lowerTriangular]
    · simp [(hLb τ x').2.1]
    · intro a b hab; exact (hLb τ x').2.2 a b hab
  have hHdet : ∀ τ, (h₀ τ * L τ x).det ≠ 0 := fun τ => by
    rw [Matrix.det_mul, hLdet, mul_one]; exact (hh₀ τ).2
  set dP : Ψ → Matrix (Fin N) (Fin N) ℂ := fun τ => Matrix.of fun a b =>
    fderiv ℂ (fun u => Pi τ (FA.pr ((FA.S.A.chart k).symm u)) a b) (FA.S.A.chart k x) v with hdP
  set dL : Ψ → Matrix (Fin N) (Fin N) ℂ := fun τ => Matrix.of fun a b =>
    fderiv ℂ (fun u => L τ ((FA.S.A.chart k).symm u) a b) (FA.S.A.chart k x) v with hdL
  have hdLbd : ∀ τ, IsBlockDiag j (dL τ) := fun τ a b hab => hLconst τ a b (Or.inr hab)
  have hkey : ∀ τ, ((h₀ τ * L τ x)⁻¹ * ((Pi τ (FA.pr x))⁻¹ * dP τ * (h₀ τ * L τ x) + h₀ τ * dL τ)).BlockTriangular id := by
    intro τ
    have h1 := hv τ
    have h2 : (Pi τ (FA.pr x) * (h₀ τ * L τ x))⁻¹ * (dP τ * (h₀ τ * L τ x) + Pi τ (FA.pr x) * (h₀ τ * dL τ)) =
        (h₀ τ * L τ x)⁻¹ * ((Pi τ (FA.pr x))⁻¹ * dP τ * (h₀ τ * L τ x) + h₀ τ * dL τ) := by
      rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_add (Pi τ (FA.pr x))⁻¹,
        ← Matrix.mul_assoc (Pi τ (FA.pr x))⁻¹ (Pi τ (FA.pr x)), Matrix.nonsing_inv_mul _ (hdet τ), Matrix.one_mul,
        ← Matrix.mul_assoc (Pi τ (FA.pr x))⁻¹ (dP τ)]
    rw [← h2, ← hprod τ]
    exact h1
  have hll : ∀ τ (a b : Fin N), N - j ≤ (a : ℕ) → (b : ℕ) < N - j → ((Pi τ (FA.pr x))⁻¹ * dP τ) a b = 0 :=
    fun τ => lower_left_zero (isBlockDiag_mul' (hh₀ τ).1 (hLb τ x).1) (hHdet τ) (isBlockDiag_mul' (hh₀ τ).1 (hdLbd τ)) (hkey τ)
  have hdP' : ∀ τ, dP τ = Matrix.of fun a b => fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart kb).symm w) a b)
      (BM.Rb.A.chart kb (FA.pr x)) (fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x) v) := by
    intro τ; ext a b
    simp only [hdP, Matrix.of_apply, (hchain τ a b).1, ContinuousLinearMap.comp_apply]
  have hβ : fderiv ℂ (BM.Rb.A.chart kb ∘ FA.pr ∘ (FA.S.A.chart k).symm) (FA.S.A.chart k x) v = 0 :=
    himm kb hkb _ fun τ a b ha hb => by rw [← hdP' τ]; exact hll τ a b ha hb
  have hdP0 : ∀ τ, dP τ = 0 := by
    intro τ; rw [hdP' τ, hβ]; ext a b; simp
  have hdL0 : ∀ τ, dL τ = 0 := by
    intro τ
    refine eq_zero_of_lower (hLb τ x).2 (fun a b hab => hLconst τ a b (Or.inl hab)) ?_
    have h3 := hkey τ
    rw [hdP0 τ, Matrix.mul_zero, Matrix.zero_mul, zero_add, Matrix.mul_inv_rev, Matrix.mul_assoc,
      ← Matrix.mul_assoc (h₀ τ)⁻¹ (h₀ τ), Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hh₀ τ).2),
      Matrix.one_mul] at h3
    exact h3
  exact eq_zero_of_still FA hσ hinj hW hx hl hL ho hk hkb hβ fun τ a b => by
    have := congrFun (congrFun (hdL0 τ) a) b
    simpa [hdL] using this

end PositivityTheory.Xgp.c_unif
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace PositivityTheory.Xgp.c_unif

open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}

theorem chart_over (FA : FlagAn BM d) (x : FA.S.X) {l : Fin BM.q} (hl : FA.pr x ∈ BM.O l \ bdry BM.s)
    {Vb : Set BM.Rb.X} {Pi : Ψ → BM.Rb.X → Matrix (Fin N) (Fin N) ℂ} (hVb : FA.pr x ∈ Vb)
    (hPi : IsPeriodOn BM.Rb.A j Vb Pi (BM.G l)) :
    ∃ V g, IsPeriodChart (FA.S.comap some).A j (FA.S.comap some).potH x V g ∧
      ((∀ k, FA.pr x ∈ (BM.Rb.A.chart k).source → ∀ v : Fin n → ℂ,
        (∀ τ (a b : Fin N), N - j ≤ (a : ℕ) → (b : ℕ) < N - j → ((Pi τ (FA.pr x))⁻¹ * Matrix.of fun a b =>
          fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart k).symm w) a b) (BM.Rb.A.chart k (FA.pr x)) v) a b = 0) → v = 0) →
        IsFlagImmersionAt (FA.S.comap some).A g x) := by
  have hb := GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA
  have hd := FA.Re.degree
  rw [FA.deg_one, FA.br_empty] at hd
  obtain ⟨σ, h1, h2, hσ, hinj⟩ := exists_inv FA.S.A FA.Re.R.A FA.Re.π FA.Re.holo hd hb
  have hcl : IsClosed (bdry BM.s) := GlobalTheory.T.isClosed_section_boundary n _ BM.Rb.A BM.L BM.s BM.sec
  have hW : IsOpen (σ ⁻¹' FA.Re.R.U (σ x) ∩ FA.pr ⁻¹' ((BM.O l \ bdry BM.s) ∩ Vb)) :=
    ((FA.Re.R.isOpen_U _).preimage hσ.1).inter ((((BM.O_open l).sdiff hcl).inter hPi.1).preimage FA.pr_holo.1)
  have hcomp : ∀ x', σ x' ∈ FA.Re.R.U (σ x) → SameOrbit (FA.Re.R.lift (σ x) (σ x')) (FA.Re.R.lift (σ x') (σ x')) :=
    fun x' h => FA.Re.R.compat _ _ _ ⟨h, FA.Re.R.mem_U _⟩
  obtain ⟨W, hWo, hxW, hsub, h₀, L, hh₀, hL, hLb, ho⟩ := exists_holo_flags BM FA.pr_holo hW
    (z := fun x' => FA.Re.R.lift (σ x) (σ x'))
    (fun q => holoOn_mono (holoOn_comp hσ (FA.Re.R.holo (σ x) q)) Set.inter_subset_left)
    (fun x' h => FA.Re.R.mem _ _ h.1)
    (fun x' h => orbit_trans (Fib.sameOrbit_basePart M.blk (hcomp x' h.1)) (by
      have := FA.pr_eq (σ x')
      rwa [h1] at this))
    (l := l) (fun x' h => h.2.1.1) (x₀ := x) ⟨FA.Re.R.mem_U _, hl, hVb⟩
  obtain ⟨V, hV⟩ := period_chart FA hb.2 hPi hWo hxW (fun x' h => (hsub h).2) (H := fun τ x' => h₀ τ * L τ x')
    (fun τ => holoOn_mul (fun _ _ _ => analyticOnNhd_const) (hL τ))
    (fun τ x' _ => ⟨(hh₀ τ).1.mul (hLb τ x').1, by
      rw [Matrix.det_mul, (hLb τ x').2.det, mul_one]; exact (hh₀ τ).2⟩)
    (fun x' h x₀ e => by
      have e' : x₀ = σ x' := by rw [← e, h2]
      rw [e']
      exact orbit_trans (orbit_symm (hcomp x' (hsub h).1)) (ho x' h))
  exact ⟨V, _, hV, fun himm => flag_immersion FA hσ hinj hPi hWo hxW hl.1 hVb hh₀ hL hLb ho himm⟩

theorem exists_over (FA : FlagAn BM d) {l : Fin BM.q} {b : BM.Rb.X} (hb : b ∈ BM.O l) : ∃ x, FA.pr x = b := by
  obtain ⟨x₀, hx₀⟩ := FA.Re.R.surj _ (GlobalTheory.T.flag_point_in_multiprojective_points K ι Φ y Ψ N j M n BM l b hb (fun _ => 1)
    fun _ => ⟨isBlockDiag_one, by simp⟩) (not_mem_of_eq_top FA.J_top _)
  refine ⟨FA.Re.π x₀, BM.Rb.inj _ _ (not_mem_of_eq_top rfl _) ?_⟩
  have h := Fib.sameOrbit_basePart M.blk hx₀
  rw [FC.basePart_flagPt] at h
  exact orbit_trans (orbit_symm (FA.pr_eq x₀)) (orbit_trans h (GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM l b hb).2.2.2)

theorem mem_open_iff (FA : FlagAn BM d) (x : FA.S.X) : x ∈ (FA.S.comap some).open' ↔ FA.pr x ∉ bdry BM.s := by
  show ¬ FA.S.s x x = 0 ↔ _
  rw [FA.s_eq]
  rfl

end PositivityTheory.Xgp.c_unif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataUniformised
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), n = Fintype.card Ψ * j * (N - j) → d + 1 = antisymDegree Ψ N → IsUniformised (FA.S.comap some).A (FA.S.comap some).open' j (FA.S.comap some).potH := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA _ _
  refine ⟨?_, ?_⟩
  · intro x hx
    have hb := (PositivityTheory.Xgp.c_unif.mem_open_iff FA x).1 hx
    obtain ⟨l, hl⟩ := BM.O_cover (FA.pr x)
    obtain ⟨V, Pi, hxV, hP⟩ := BM.period l (FA.pr x) ⟨hl, hb⟩
    obtain ⟨V', g, hc, -⟩ := PositivityTheory.Xgp.c_unif.chart_over FA x ⟨hl, hb⟩ hxV hP
    exact ⟨V', g, hc⟩
  · obtain ⟨l, b, ⟨hbO, hbs⟩, V, Pi, hbV, hP, himm⟩ := BM.immersion
    obtain ⟨x, rfl⟩ := PositivityTheory.Xgp.c_unif.exists_over FA hbO
    have hx : x ∈ (FA.S.comap some).open' := (PositivityTheory.Xgp.c_unif.mem_open_iff FA x).2 hbs
    obtain ⟨V', g, hc, hi⟩ := PositivityTheory.Xgp.c_unif.chart_over FA x ⟨hbO, hbs⟩ hbV hP
    exact ⟨x, hx, V', g, hc, hi himm⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataUniformisedStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_data_uniformised : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), n = Fintype.card Ψ * j * (N - j) → d + 1 = antisymDegree Ψ N → IsUniformised (FA.S.comap some).A (FA.S.comap some).open' j (FA.S.comap some).potH := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised | exact GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised <;> assumption)
end
