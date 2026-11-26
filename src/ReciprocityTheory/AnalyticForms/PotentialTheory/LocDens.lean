module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HomogeneousLiftHolomorphicOnSnd

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix

noncomputable section

def HessCGermStatement : Prop :=
  ∀ {D : ℕ} (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ), φ =ᶠ[nhds z] ψ → hessC φ z = hessC ψ z

theorem hessCGerm : HessCGermStatement := by
  intro D φ ψ z h
  have hH : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := (h.fderiv (𝕜 := ℝ)).fderiv_eq
  show hessC φ z = hessC ψ z
  unfold hessC
  rw [hH]

theorem maDens_congr_hessC {D : ℕ} (φ ψ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : ∀ k, hessC (φ k) z = hessC (ψ k) z) : maDens φ z = maDens ψ z := by
  simp only [maDens, h]

theorem potSmoothAt {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X)
    (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  exact ((hP.1 x j).contDiffAt (hopen.mem_nhds hy)).of_le (by first | exact ENat.LEInfty.out | simp | norm_num)

theorem potSmoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X)
    (hP : IsPotential A P) (x : X) (j : Fin A.n) :
    ContDiffOn ℝ 2 (P.φ x ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) := by
  exact (hP.1 x j).of_le (by first | exact ENat.LEInfty.out | simp | norm_num)

theorem locDensBase : LocDensBaseStatement := by
  intro e X _ A Φ hΦ j y hy x hx
  unfold locDens
  apply maDens_congr_hessC
  intro i
  obtain ⟨W, hW, hpW, G, hG, hGeq⟩ :=
    (hΦ i).2 ((A.chart j).symm y) (x i) ((A.chart j).symm y) ⟨(Φ i).mem_U _, hx i⟩

  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x i))) :=
    (A.chart j).isOpen_inter_preimage_symm
      ((hW.inter ((Φ i).isOpen_U _)).inter ((Φ i).isOpen_U (x i)))
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x i)) :=
    ⟨hy, ⟨⟨hpW, (Φ i).mem_U _⟩, hx i⟩⟩
  have hev : (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[nhds y]
      (fun y' => (Φ i).φ (x i) ((A.chart j).symm y') + (G ((A.chart j).symm y')).re) := by
    filter_upwards [hopen.mem_nhds hmem] with y' hy'
    rw [← hGeq _ hy'.2]
    ring
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hpW⟩
  have hφs : ContDiffAt ℝ 2 ((Φ i).φ (x i) ∘ (A.chart j).symm) y :=
    potSmoothAt A (Φ i) (hΦ i) (x i) j ⟨hy, hx i⟩
  exact (hessCGerm _ _ y hev).trans (ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ (G ∘ (A.chart j).symm) y hφs hGa)

theorem hessC_continuousOn {D : ℕ} (ψ : (Fin D → ℂ) → ℝ) (V : Set (Fin D → ℂ)) (hV : IsOpen V)
    (hψ : ContDiffOn ℝ 2 ψ V) : ContinuousOn (hessC ψ) V := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ ψ y) V := hψ.fderiv_of_isOpen hV (by norm_num)
  have h2 : ContinuousOn (fun y => fderiv ℝ (fderiv ℝ ψ) y) V :=
    h1.continuousOn_fderiv_of_isOpen hV le_rfl

  have ev : ∀ a b : Fin D → ℂ, ContinuousOn (fun y => fderiv ℝ (fderiv ℝ ψ) y a b) V :=
    fun a b => (h2.clm_apply continuousOn_const).clm_apply continuousOn_const
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  unfold hessC
  dsimp only
  have hre := Complex.continuous_ofReal.comp_continuousOn
    ((ev (Pi.single i 1) (Pi.single j 1)).add
      (ev (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1)))
  have him := Complex.continuous_ofReal.comp_continuousOn
    ((ev (Pi.single i 1) (Complex.I • Pi.single j 1)).sub
      (ev (Complex.I • Pi.single i 1) (Pi.single j 1)))
  exact (hre.add (continuousOn_const.mul him)).div_const 4

theorem maDens_continuousOn {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (V : Set (Fin D → ℂ))
    (hV : IsOpen V) (hφ : ∀ k, ContDiffOn ℝ 2 (φ k) V) : ContinuousOn (maDens φ) V := by
  have hH : ∀ k, ContinuousOn (hessC (φ k)) V := fun k => hessC_continuousOn (φ k) V hV (hφ k)
  unfold maDens mdisc
  refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn ?_)
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun S _ => continuousOn_const.mul ?_)
  exact (continuous_id.matrix_det).comp_continuousOn (continuousOn_finsetSum _ fun k _ => hH k)

theorem locDensCont : LocDensContStatement := by
  intro e X _ A Φ hΦ j y0 hy0

  let x : Fin e → X := fun _ => (A.chart j).symm y0
  let V := (A.chart j).target ∩ (A.chart j).symm ⁻¹' ⋂ i, (Φ i).U (x i)
  have hV : IsOpen V :=
    (A.chart j).isOpen_inter_preimage_symm (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U (x i))
  have hy0V : y0 ∈ V := ⟨hy0, Set.mem_iInter.2 fun i => (Φ i).mem_U _⟩
  have hsm : ∀ i, ContDiffOn ℝ 2 (fun y' => (Φ i).φ (x i) ((A.chart j).symm y')) V := fun i =>
    (potSmoothOn A (Φ i) (hΦ i) (x i) j).mono fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2 i⟩
  have hg := (maDens_continuousOn _ V hV hsm).continuousAt (hV.mem_nhds hy0V)
  have hev : (maDens fun i y' => (Φ i).φ (x i) ((A.chart j).symm y')) =ᶠ[nhds y0]
      locDens A Φ j := by
    filter_upwards [hV.mem_nhds hy0V] with y hy
    exact (locDensBase A Φ hΦ j y hy.1 x fun i => Set.mem_iInter.1 hy.2 i).symm
  exact (hg.congr hev).continuousWithinAt

theorem locDensChart : LocDensChartStatement := by
  intro e X _ A Φ hΦ j k y hy hyk
  have hback : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
    (A.chart k).left_inv hyk
  have hτa : AnalyticAt ℂ (A.chart k ∘ (A.chart j).symm) y := A.holo j k y ⟨hy, hyk⟩
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
  have hsm : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ ((A.chart j).symm y) ∘ (A.chart k).symm)
      ((A.chart k ∘ (A.chart j).symm) y) := fun i =>
    potSmoothAt A (Φ i) (hΦ i) _ k ⟨(A.chart k).map_source hyk, by
      simp only [Set.mem_preimage, Function.comp_apply, hback]; exact (Φ i).mem_U _⟩
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun i => (Φ i).φ ((A.chart j).symm y) ∘ (A.chart k).symm)
    (A.chart k ∘ (A.chart j).symm) y hτa hsm

  have hL : locDens A Φ j y = maDens (fun i => ((Φ i).φ ((A.chart j).symm y) ∘ (A.chart k).symm) ∘
      (A.chart k ∘ (A.chart j).symm)) y := by
    unfold locDens
    apply maDens_congr_hessC
    intro i
    refine hessCGerm _ _ _ ?_
    filter_upwards [hO.mem_nhds ⟨hy, hyk⟩] with y' hy'
    simp only [Function.comp_apply, (A.chart k).left_inv hy'.2]
  rw [hL, hcomp, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq]
  unfold locDens
  simp only [Function.comp_apply, hback]
  rfl

theorem re_star_dot_hessC {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z x : Fin D → ℂ) :
    (star x ⬝ᵥ (hessC φ z *ᵥ x)).re = levi φ z (star x) := by
  classical
  obtain ⟨H, hH⟩ : ∃ H, H = fderiv ℝ (fderiv ℝ φ) z := ⟨_, rfl⟩
  let E : Fin D → Fin D → ℂ := fun i => Pi.single i 1

  have hw : star x = ∑ i, ((x i).re • E i + (-(x i).im) • (Complex.I • E i)) := by
    ext k
    rw [Finset.sum_apply, Finset.sum_eq_single k
      (fun i _ hik => by simp [E, Pi.single_apply, hik.symm]) (by simp)]
    simp [E, Complex.ext_iff]
  have hIw : Complex.I • star x = ∑ i, ((x i).im • E i + (x i).re • (Complex.I • E i)) := by
    ext k
    rw [Finset.sum_apply, Finset.sum_eq_single k
      (fun i _ hik => by simp [E, Pi.single_apply, hik.symm]) (by simp)]
    simp [E, Complex.ext_iff]
  have hL : (star x ⬝ᵥ (hessC φ z *ᵥ x)).re = ∑ i, ∑ j,
      (((x i).re * (x j).re + (x i).im * (x j).im) *
          (H (E i) (E j) + H (Complex.I • E i) (Complex.I • E j)) +
        ((x i).im * (x j).re - (x i).re * (x j).im) *
          (H (E i) (Complex.I • E j) - H (Complex.I • E i) (E j))) / 4 := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ReciprocityTheory.AnForm.A.TraceConjugationCover.hessC_eq_lv, ← hH]
    simp [ReciprocityTheory.AnForm.A.TraceConjugationCover.lv, E, Complex.mul_re, Complex.mul_im]
    ring
  have hR : levi φ z (star x) = ∑ i, ∑ j,
      (((x i).re * (x j).re + (x i).im * (x j).im) *
          (H (E i) (E j) + H (Complex.I • E i) (Complex.I • E j)) +
        ((x i).im * (x j).re - (x i).re * (x j).im) *
          (H (E i) (Complex.I • E j) - H (Complex.I • E i) (E j))) / 4 := by
    unfold levi
    rw [← hH, hIw, hw]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_add (f := _), map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hL, hR]

end

end ReciprocityTheory.AnForm.M
end

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

theorem maDens_congr_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  have hH : ∀ i, hessC (φ i) y = hessC (ψ i) y := by
    intro i
    have h2 : fderiv ℝ (fderiv ℝ (φ i)) y = fderiv ℝ (fderiv ℝ (ψ i)) y := (h i).fderiv.fderiv_eq
    unfold hessC
    simp only [h2]
    rfl
  simp only [maDens, hH]

theorem holoMap_preimage_mem_nhds {e e' : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : h ((B.chart j).symm y) ∈ (A.chart k).source) :
    (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) ∈ 𝓝 y := by
  have hs : IsOpen (h ⁻¹' (A.chart k).source) := (A.chart k).open_source.preimage hh.1
  exact ((B.chart j).isOpen_inter_preimage_symm hs).mem_nhds ⟨hy, hk⟩

theorem potential_contDiffAt_chart {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (k : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart k).target) (hzU : (A.chart k).symm z ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) z := by
  have hS : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x) :=
    (A.chart k).isOpen_inter_preimage_symm (P.isOpen_U x)
  refine ((hP.1 x k).contDiffAt (hS.mem_nhds ⟨hz, hzU⟩)).of_le ?_
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

theorem pullback_local_eq {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h)
    (P : LocPot X) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : h ((B.chart j).symm y) ∈ (A.chart k).source) :
    (fun y' => P.φ (h ((B.chart j).symm y)) (h ((B.chart j).symm y'))) =ᶠ[𝓝 y]
      (P.φ (h ((B.chart j).symm y)) ∘ (A.chart k).symm) ∘
        (A.chart k ∘ h ∘ (B.chart j).symm) := by
  filter_upwards [holoMap_preimage_mem_nhds hh j k hy hk] with y' hy'
  simp only [Function.comp_apply]
  rw [(A.chart k).left_inv hy'.2]

theorem locDensPullback : LocDensPullbackStatement := by
  intro e X Y _ _ A B h hh Φ hΦ j k y hy hk
  set x0 := h ((B.chart j).symm y) with hx0
  set τ := A.chart k ∘ h ∘ (B.chart j).symm with hτ
  have hτa : AnalyticAt ℂ τ y := hh.2 j k y ⟨hy, hk⟩
  have hτy : τ y = A.chart k x0 := rfl
  have hsymm : (A.chart k).symm (A.chart k x0) = x0 := (A.chart k).left_inv hk
  have hφ : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ x0 ∘ (A.chart k).symm) (τ y) := by
    intro i
    rw [hτy]
    exact potential_contDiffAt_chart (hΦ i) x0 k ((A.chart k).map_source hk)
      (by rw [hsymm]; exact (Φ i).mem_U x0)
  unfold locDens
  refine (maDens_congr_eventuallyEq (fun i => pullback_local_eq hh (Φ i) j k hy hk)).trans ?_
  rw [hsymm]
  refine (ReciprocityTheory.AnForm.A.maDens_comp (fun i => (Φ i).φ x0 ∘ (A.chart k).symm) τ y hτa hφ).trans ?_
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hτy]
  rfl

theorem rankDrop : RankDropStatement := by
  intro e e' X Y _ _ A B h hh hrk Φ hΦ g
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_eq_zero fun j _ => ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm y))
    set x0 := h ((B.chart j).symm y) with hx0
    have hsymm : (A.chart k).symm (A.chart k x0) = x0 := (A.chart k).left_inv hk
    have hφ : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ x0 ∘ (A.chart k).symm)
        ((A.chart k ∘ h ∘ (B.chart j).symm) y) := fun i =>
      potential_contDiffAt_chart (hΦ i) x0 k ((A.chart k).map_source hk)
        (by simp only [Function.comp_apply]; rw [hsymm]; exact (Φ i).mem_U x0)
    have h0 : locDens B (fun i => (Φ i).pullback h hh.1) j y = 0 := by
      unfold locDens
      refine (maDens_congr_eventuallyEq (fun i => pullback_local_eq hh (Φ i) j k hy hk)).trans ?_
      exact maDens_comp_eq_zero_of_rank_lt _ _ y (hh.2 j k y ⟨hy, hk⟩) hφ (hrk j k y hy hk)
    rw [h0, mul_zero]
  · rfl

end

end ReciprocityTheory.AnForm.M
end

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureA
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Complex
open scoped ContDiff ComplexOrder Matrix

noncomputable section

theorem leviC_conj_of_symm {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) (a b : Fin e → ℂ) :
    starRingEnd ℂ (leviC H a b) = leviC H b a := by
  simp only [leviC, map_div₀, map_add (f := _), map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [hs b a, hs (I • b) (I • a), hs b (I • a), hs (I • b) a]
  push_cast
  ring

theorem leviC_self_of_symm {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) (a : Fin e → ℂ) :
    leviC H a a = (((H a a + H (I • a) (I • a)) / 4 : ℝ) : ℂ) := by
  simp only [leviC]
  rw [hs a (I • a), sub_self]
  push_cast
  ring

theorem hessC_posSemidef_of_levi {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (hl : ∀ w, 0 ≤ levi f z w) : (hessC f z).PosSemidef := by
  have hH := hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hs : ∀ v w, fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v := fun v w => hH v w
  have hM : ∀ i j, hessC f z i j =
      leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := hessC_eq_leviC f z
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.IsHermitian.ext fun i j => ?_) fun x => ?_
  · rw [hM, hM]
    exact leviC_conj_of_symm _ hs _ _
  · have h1 : ∀ i, ∑ j, hessC f z i j * x j =
        leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (star x) := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← leviC_conj_of_symm _ hs (star x) (Pi.single i 1),
        ← sum_mul_leviC (fderiv ℝ (fderiv ℝ f) z) (star x) (Pi.single i 1), map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM, map_mul, leviC_conj_of_symm _ hs]
      simp [mul_comm]
    have h2 : star x ⬝ᵥ (hessC f z *ᵥ x) =
        leviC (fderiv ℝ (fderiv ℝ f) z) (star x) (star x) := by
      rw [← sum_mul_leviC (fderiv ℝ (fderiv ℝ f) z) (star x) (star x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← h1 i]
      rfl
    rw [h2, leviC_self_of_symm _ hs]
    exact_mod_cast hl (star x)

theorem pot_contDiffAt_two {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (P.isOpen_U x)
  exact ((hP.1 x j).contDiffAt (hopen.mem_nhds ⟨hy, hyU⟩)).of_le (by first | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | norm_num)

theorem hessC_locPot_posSemidef {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (hPsh : IsPsh A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) :
    (hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y).PosSemidef := by
  exact hessC_posSemidef_of_levi _ y (pot_contDiffAt_two hP _ j hy (P.mem_U _))
    (fun w => hPsh _ j y ⟨hy, P.mem_U _⟩ w)

theorem locDens_nonneg_of_psh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i))
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) : 0 ≤ locDens A Φ j y := by
  exact ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y
    (fun i => hessC_locPot_posSemidef (hΦ i) (hPsh i) j hy)

theorem locDens_le_add {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ Θ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hΦp : ∀ i, IsPsh A (Φ i))
    (hΘ : ∀ i, IsPotential A (Θ i)) (hΘp : ∀ i, IsPsh A (Θ i))
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    locDens A Φ j y ≤ locDens A (fun i => Φ i + Θ i) j y := by
  unfold locDens maDens
  refine mul_le_mul_of_nonneg_left (ReciprocityTheory.AnForm.A.mdisc_re_mono _ _
    (fun k => hessC_locPot_posSemidef (hΦ k) (hΦp k) j hy) fun k => ?_) (by positivity)
  show (hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
      (Θ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y -
    hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y).PosSemidef
  rw [ReciprocityTheory.AnForm.A.hessC_add (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
    (fun y' => (Θ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y (pot_contDiffAt_two (hΦ k) _ j hy ((Φ k).mem_U _))
    (pot_contDiffAt_two (hΘ k) _ j hy ((Θ k).mem_U _)), add_sub_cancel_left]
  exact hessC_locPot_posSemidef (hΘ k) (hΘp k) j hy

end

end ReciprocityTheory.AnForm.M
end

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.FubiniStudyPotentialProductIsPotential
namespace ReciprocityTheory.AnForm.M

open MeasureTheory OnePoint CompatibleChartOperations

noncomputable section

section ProdChart

variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n)

end ProdChart

section ProdChart2

variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)

end ProdChart2

section Pull

variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)

end Pull



open scoped Classical in
def diagSec (x y : OnePoint ℂ × OnePoint ℂ) : ℂ := by
  classical
  exact if x.1 = ∞ then
      (if x.2 = ∞ then crd1 y.1 - crd1 y.2 else crd1 y.1 * crd0 y.2 - 1)
    else
      (if x.2 = ∞ then 1 - crd0 y.1 * crd1 y.2 else crd0 y.2 - crd0 y.1)

end

end ReciprocityTheory.AnForm.M
end
