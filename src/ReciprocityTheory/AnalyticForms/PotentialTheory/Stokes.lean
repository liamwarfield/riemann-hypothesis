module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.StokesD
section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.StokesC
section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.StokesB
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem st_trans_smooth (A : FinHolAtlas e X) (j k : Fin A.n) :
    ContDiffOn ℝ ∞ (A.chart k ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) := by
  exact fun y hy => (((A.holo j k y hy).contDiffAt (n := ∞)).restrict_scalars ℝ).contDiffWithinAt

theorem st_exists_good_partition [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) {r : ℕ}
    (Φ : Fin r → LocPot X) :
    ∃ (M : ℕ) (θ : Fin M → X → ℝ) (G : Fin M → Set X) (j : Fin M → Fin A.n)
      (x0 : Fin M → Fin r → X),
      (∀ m, A.Smooth (θ m)) ∧ (∀ m x, 0 ≤ θ m x) ∧ (∀ x, ∑ m, θ m x = 1) ∧
      (∀ m, tsupport (θ m) ⊆ G m) ∧ (∀ m, IsOpen (G m)) ∧
      (∀ m, G m ⊆ (A.chart (j m)).source) ∧ (∀ m i, G m ⊆ (Φ i).U (x0 m i)) := by
  classical
  choose jx hjx using A.cover
  let G : X → Set X := fun x => (A.chart (jx x)).source ∩ ⋂ i, (Φ i).U x
  have hGo : ∀ x, IsOpen (G x) := fun x =>
    (A.chart (jx x)).open_source.inter (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U x)
  have hGx : ∀ x, x ∈ G x := fun x => ⟨hjx x, Set.mem_iInter.mpr fun i => (Φ i).mem_U x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover G hGo
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hGx x⟩)
  let pt : Fin t.card → X := fun m => (t.equivFin.symm m : X)
  let ch : Fin t.card → OpenPartialHomeomorph X (Fin e → ℂ) := fun m =>
    (A.chart (jx (pt m))).restr (G (pt m))
  have hsrc : ∀ m, (ch m).source = G (pt m) := by
    intro m
    simp only [ch, OpenPartialHomeomorph.restr_source, (hGo _).interior_eq]
    exact Set.inter_eq_right.mpr Set.inter_subset_left
  have hcov : ∀ x, ∃ m, x ∈ (ch m).source := by
    intro x
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ G y := by simpa using ht (Set.mem_univ x)
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    rw [hsrc]
    simpa [pt] using hxy
  have htr : ∀ a b, ContDiffOn ℝ ∞ (ch b ∘ (ch a).symm)
      ((ch a).target ∩ (ch a).symm ⁻¹' (ch b).source) := by
    intro a b
    simp only [ch, OpenPartialHomeomorph.restr_apply, OpenPartialHomeomorph.restr_symm_apply,
      OpenPartialHomeomorph.restr_target, OpenPartialHomeomorph.restr_source]
    exact (st_trans_smooth A _ _).mono fun y hy => ⟨hy.1.1, hy.2.1⟩
  obtain ⟨χ, hχ0, hχ1, hχs, hχsm⟩ := exists_chart_partition ch hcov htr
  refine ⟨t.card, χ, fun m => G (pt m), fun m => jx (pt m), fun m _ => pt m, ?_, hχ0, hχ1,
    fun m => (hχs m).trans (hsrc m).subset, fun m => hGo _, fun m => Set.inter_subset_left,
    fun m i x hx => Set.mem_iInter.mp hx.2 i⟩
  intro m k y hy
  obtain ⟨n, hn⟩ := hcov ((A.chart k).symm y)
  have hyk : y ∈ (A.chart k).target := hy.1
  have hxs : (A.chart k).symm y ∈ (A.chart (jx (pt n))).source := by
    have hn' := hn
    rw [hsrc] at hn'
    exact hn'.1
  have hx_in : (A.chart (jx (pt n))) ((A.chart k).symm y) ∈ (ch n).target := (ch n).map_source hn
  have hsm := hχsm m n
  simp only [ch, OpenPartialHomeomorph.restr_symm_apply] at hsm
  have hf := hsm.contDiffAt (((A.chart (jx (pt n))).restr (G (pt n))).open_target.mem_nhds hx_in)
  have hW : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart (jx (pt n))).source) :=
    (A.chart k).isOpen_inter_preimage_symm (A.chart (jx (pt n))).open_source
  have hg := (st_trans_smooth A k (jx (pt n))).contDiffAt (hW.mem_nhds ⟨hyk, hxs⟩)
  have hc := hf.comp y hg
  refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hW.mem_nhds ⟨hyk, hxs⟩] with z hz
  simp only [Function.comp_apply]
  rw [(A.chart (jx (pt n))).left_inv hz.2]

end

end ReciprocityTheory.AnForm.M
end

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem st_hessC_congr {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    hessC f y = hessC g y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y :=
    (h.fderiv (𝕜 := ℝ)).fderiv_eq
  unfold hessC
  rw [h2]

private lemma maDens_congr_of_hessC_eq {D : ℕ} {F F' : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ k, hessC (F k) y = hessC (F' k) y) : maDens F y = maDens F' y := by
  unfold maDens
  simp only [h]

private lemma two_le_infty_withTop : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
    | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
    | exact_mod_cast le_top
    | simp

private lemma three_le_infty_withTop : (3 : WithTop ℕ∞) ≤ ∞ := by
  first
    | exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ ⊤)
    | exact_mod_cast le_top
    | simp

private lemma contDiffAt_two_re_of_analyticAt {D : ℕ} {K : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}
    (hK : AnalyticAt ℂ K z) : ContDiffAt ℝ 2 (fun w => (K w).re) z :=
  Complex.reCLM.contDiff.contDiffAt.comp z (hK.contDiffAt.restrict_scalars ℝ)

private lemma hessC_add_potential {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (hf : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 f z) (hg : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 g z) :
    hessC (fun z => f z + g z) y = hessC f y + hessC g y := by
  have hd : fderiv ℝ (fun z => f z + g z) =ᶠ[𝓝 y] fun z => fderiv ℝ f z + fderiv ℝ g z := by
    filter_upwards [hf, hg] with z h1 h2
    exact fderiv_add (h1.differentiableAt (by first | norm_num | exact one_le_two | simp))
      (h2.differentiableAt (by first | norm_num | exact one_le_two | simp))
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.self_of_nhds.fderiv_right (m := 1)
      (by first | norm_num | exact le_of_eq one_add_one_eq_two | simp)).differentiableAt (by first | exact one_ne_zero | norm_num | simp)
  have hg2 : DifferentiableAt ℝ (fderiv ℝ g) y :=
    (hg.self_of_nhds.fderiv_right (m := 1)
      (by first | norm_num | exact le_of_eq one_add_one_eq_two | simp)).differentiableAt (by first | exact one_ne_zero | norm_num | simp)
  have hH : fderiv ℝ (fderiv ℝ (fun z => f z + g z)) y =
      fderiv ℝ (fderiv ℝ f) y + fderiv ℝ (fderiv ℝ g) y := by
    rw [hd.fderiv_eq]
    exact fderiv_add hf2 hg2
  ext i k
  simp only [hessC, hH, Matrix.add_apply, ContinuousLinearMap.add_apply]
  push_cast
  ring

private lemma hessC_re_of_analyticAt {D : ℕ} {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ}
    (hH : AnalyticAt ℂ H y) : hessC (fun z => (H z).re) y = 0 := by
  have h1 : fderiv ℝ (fun z => (H z).re) =ᶠ[𝓝 y] fun z =>
      (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM)
        ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ) (fderiv ℂ H z)) := by
    filter_upwards [hH.eventually_analyticAt] with z hz
    have hd : HasFDerivAt (fun w => (H w).re)
        (Complex.reCLM.comp ((fderiv ℂ H z).restrictScalars ℝ)) z :=
      Complex.reCLM.hasFDerivAt.comp z (hz.differentiableAt.hasFDerivAt.restrictScalars ℝ)
    rw [hd.fderiv]
    first
      | rfl
      | (ext v; simp)
  have hD : HasFDerivAt (fderiv ℂ H) ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ) y :=
    hH.fderiv.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h2 : HasFDerivAt (fun z => (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM)
        ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ) (fderiv ℂ H z)))
      ((ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).comp
        ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ).comp
          ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ))) y :=
    (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).hasFDerivAt.comp y
    ((ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ).hasFDerivAt.comp y hD)
  have hv : ∀ v w : Fin D → ℂ, fderiv ℝ (fderiv ℝ fun z => (H z).re) y v w =
      (fderiv ℂ (fderiv ℂ H) y v w).re := by
    intro v w
    rw [h1.fderiv_eq, h2.fderiv]
    first
      | rfl
      | simp
  ext i k
  simp only [hessC, hv, Matrix.zero_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp [Complex.mul_re, Complex.mul_im]

theorem st_maDens_cons_congr {n : ℕ} {f g : (Fin (n + 1) → ℂ) → ℝ}
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) {y : Fin (n + 1) → ℂ} (h : f =ᶠ[𝓝 y] g) :
    maDens (Fin.cons f φ) y = maDens (Fin.cons g φ) y := by
  apply maDens_congr_of_hessC_eq
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa only [Fin.cons_zero] using st_hessC_congr h
  · simp only [Fin.cons_succ]

private lemma continuous_of_atlas_smooth' (A : FinHolAtlas e X) {f : X → ℝ} (hf : A.Smooth f) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨k, hk⟩ := A.cover x
  have hs : (A.chart k).target ∩ (A.chart k).symm ⁻¹' univ ∈ 𝓝 ((A.chart k) x) := by
    rw [preimage_univ, inter_univ]
    exact (A.chart k).open_target.mem_nhds ((A.chart k).map_source hk)
  have h1 : ContinuousAt (f ∘ (A.chart k).symm) ((A.chart k) x) :=
    (hf k).continuousOn.continuousAt hs
  have h2 : ContinuousAt ((f ∘ (A.chart k).symm) ∘ (A.chart k)) x :=
    ContinuousAt.comp (f := A.chart k) h1 ((A.chart k).continuousAt hk)
  refine h2.congr ?_
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with z hz
  simp [(A.chart k).left_inv hz]

theorem st_mInt_eq_chart [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (j : Fin A.n) (g : X → ℝ)
    (hg : Continuous g) (hgs : tsupport g ⊆ (A.chart j).source) :
    mInt A Ψ g = ∫ y in (A.chart j).target, g ((A.chart j).symm y) * locDens A Ψ j y := by
  unfold mInt
  rw [dite_eq_left (existsPartition A)]
  exact mIntLocalize A _ Ψ hΨ j g hgs (mIntegrableCont A Ψ hΨ g hg)

theorem st_mInt_eq_piece [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (j : Fin A.n) (G : Set X)
    (hG : G ⊆ (A.chart j).source) (g : X → ℝ) (hg : Continuous g) (hgs : tsupport g ⊆ G) :
    mInt A Ψ g = ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
      g ((A.chart j).symm y) * locDens A Ψ j y := by
  rw [st_mInt_eq_chart A Ψ hΨ j g hg (hgs.trans hG)]
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero (A.chart j).open_target.measurableSet
    inter_subset_left ?_
  intro y hy
  have hyG : (A.chart j).symm y ∉ G := fun h' => hy.2 ⟨hy.1, h'⟩
  have hg0 : g ((A.chart j).symm y) = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hyG (hgs h'))
  rw [hg0, zero_mul]

section Piece

variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))


include hΦ hG hGU in
theorem st_locDens_piece (u : X → ℝ) (hu : A.Smooth u) {y : Fin (e + 1) → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :
    locDens A (Fin.cons (LocPot.ofFun u) Φ) j y =
      maDens (Fin.cons (u ∘ (A.chart j).symm) fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by
  unfold locDens
  apply maDens_congr_of_hessC_eq
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · first
      | rfl
      | (simp only [Fin.cons_zero]; rfl)
      | simp [LocPot.ofFun, Function.comp_def]
  · simp only [Fin.cons_succ]
    have hyG : (A.chart j).symm y ∈ G := hy.2
    obtain ⟨W, hWo, haW, Gh, hGh, hdiff⟩ :=
      (hΦ i).2 ((A.chart j).symm y) (x0 i) ((A.chart j).symm y) ⟨(Φ i).mem_U _, hGU i hyG⟩
    have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x0 i))) :=
      (A.chart j).isOpen_inter_preimage_symm ((hWo.inter ((Φ i).isOpen_U _)).inter ((Φ i).isOpen_U _))
    have hyS : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x0 i)) :=
      ⟨hy.1, ⟨⟨haW, (Φ i).mem_U _⟩, hGU i hyG⟩⟩
    have hSn := hSo.mem_nhds hyS
    have hf2 : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 ((Φ i).φ (x0 i) ∘ (A.chart j).symm) z := by
      filter_upwards [hSn] with z hz
      have hon := (hΦ i).1 (x0 i) j
      exact ((hon.mono (fun w (hw : w ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x0 i))) => ⟨hw.1, hw.2.2⟩)).contDiffAt (hSo.mem_nhds hz)).of_le
        two_le_infty_withTop
    have hK : ∀ z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x0 i)),
        AnalyticAt ℂ (Gh ∘ (A.chart j).symm) z := fun z hz => hGh j z ⟨hz.1, hz.2.1.1⟩
    have hh : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 (fun w => ((Gh ∘ (A.chart j).symm) w).re) z := by
      filter_upwards [hSn] with z hz
      exact contDiffAt_two_re_of_analyticAt (hK z hz)
    have heq : (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
        fun w => ((Φ i).φ (x0 i) ∘ (A.chart j).symm) w + ((Gh ∘ (A.chart j).symm) w).re := by
      filter_upwards [hSn] with z hz
      have hz' := hdiff ((A.chart j).symm z) hz.2
      simp only [Function.comp_apply]
      linarith
    rw [st_hessC_congr heq, hessC_add_potential hf2 hh, hessC_re_of_analyticAt (hK y hyS), add_zero]


include hΦ hGo hG hGU in
theorem st_left_piece (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ) (hψG : tsupport ψ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun w) Φ) ψ =
      ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
        (A.chart j).target.indicator (ψ ∘ (A.chart j).symm) y *
          maDens (Fin.cons (w ∘ (A.chart j).symm)
            fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by
  have hP0 : IsPotential A (LocPot.ofFun w) := by
    unfold IsPotential
    refine ⟨fun _ => hw, fun x x' z _ => ⟨univ, isOpen_univ, mem_univ _, fun _ => 0, ?_, ?_⟩⟩
    · intro k z' _
      exact analyticAt_const
    · intro z' _
      simp [LocPot.ofFun]
  have hΨ : ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun w) Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [Fin.cons_zero] using hP0
    · simpa only [Fin.cons_succ] using hΦ i
  rw [st_mInt_eq_piece A _ hΨ j G hG ψ (continuous_of_atlas_smooth' A hψ) hψG]
  have hSm : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    ((A.chart j).isOpen_inter_preimage_symm hGo).measurableSet
  refine setIntegral_congr_fun hSm ?_
  intro y hy
  have h1 := st_locDens_piece A Φ hΦ j G hG x0 hGU w hw hy
  have h2 : (A.chart j).target.indicator (ψ ∘ (A.chart j).symm) y = ψ ((A.chart j).symm y) :=
    Set.indicator_of_mem hy.1 _
  simp only [h1, h2]


include hΦ hGo hG hGU in
theorem st_right_piece (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ) (hψG : tsupport ψ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun ψ) Φ) w =
      ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
        (w ∘ (A.chart j).symm) y *
          maDens (Fin.cons ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm))
            fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by
  obtain ⟨ρ, hρs, hρ1, -⟩ := exists_tsupport_one_of_isOpen_isClosed hGo
    isClosed_closure.isCompact (isClosed_tsupport ψ) hψG
  have hpot := st_isPotential_cons A hψ hΦ

  have h1 : mInt A (Fin.cons (LocPot.ofFun ψ) Φ) w =
      mInt A (Fin.cons (LocPot.ofFun ψ) Φ) (fun x => ρ x * w x) := by
    unfold mInt
    split_ifs with hP
    · unfold integralWith
      refine Finset.sum_congr rfl fun k _ => ?_
      refine setIntegral_congr_fun (A.chart k).open_target.measurableSet ?_
      intro y hy
      by_cases hs : (A.chart k).symm y ∈ tsupport ψ
      · simp [hρ1 hs]
      · simp [st_locDens_cons_eq_zero A k ψ Φ hy hs]
    · rfl
  rw [h1, st_mInt_eq_piece A _ hpot j G hG (fun x => ρ x * w x) (ρ.continuous.mul (st_smooth_continuous A hw))
    ((tsupport_mul_subset_left).trans hρs)]
  refine setIntegral_congr_fun ((A.chart j).isOpen_inter_preimage_symm hGo).measurableSet ?_
  intro y hy
  have hV : (A.chart j).target ∩ (A.chart j).symm ⁻¹' G ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm hGo).mem_nhds hy
  have hev : ψ ∘ (A.chart j).symm =ᶠ[𝓝 y] (A.chart j).target.indicator (ψ ∘ (A.chart j).symm) := by
    filter_upwards [hV] with z hz
    rw [indicator_of_mem hz.1]
  simp only
  rw [st_locDens_piece A Φ hΦ j G hG x0 hGU ψ hψ hy, ← st_maDens_cons_congr _ hev]
  by_cases hs : (A.chart j).symm y ∈ tsupport ψ
  · simp [hρ1 hs]
  · have h0 := st_locDens_cons_eq_zero A j ψ Φ hy.1 hs
    rw [st_locDens_piece A Φ hΦ j G hG x0 hGU ψ hψ hy] at h0
    simp [h0]


include hΦ hGo hG hGU in
theorem st_symm_piece (hP : ReciprocityTheory.AnForm.A.PartsStatement) (w ψ : X → ℝ) (hw : A.Smooth w)
    (hψ : A.Smooth ψ) (hψG : tsupport ψ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun w) Φ) ψ = mInt A (Fin.cons (LocPot.ofFun ψ) Φ) w := by
  rw [st_left_piece A Φ hΦ j G hGo hG x0 hGU w ψ hw hψ hψG,
    st_right_piece A Φ hΦ j G hGo hG x0 hGU w ψ hw hψ hψG]
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    (A.chart j).isOpen_inter_preimage_symm hGo
  have hsG : tsupport ψ ⊆ (A.chart j).source := hψG.trans hG
  have hKc : IsCompact ((A.chart j) '' tsupport ψ) :=
    (isClosed_tsupport ψ).isCompact.image_of_continuousOn ((A.chart j).continuousOn.mono hsG)
  have hsupp : Function.support ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := by
    intro y hy
    have hy' := Function.mem_support.1 hy
    by_cases hyt : y ∈ (A.chart j).target
    · refine ⟨(A.chart j).symm y, subset_tsupport _ ?_, (A.chart j).right_inv hyt⟩
      rw [Set.indicator_of_mem hyt] at hy'
      exact hy'
    · exact absurd (Set.indicator_of_notMem hyt _) hy'
  have hts : tsupport ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := closure_minimal hsupp hKc.isClosed
  have hKS : (A.chart j) '' tsupport ψ ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(A.chart j).map_source (hsG hx), ?_⟩
    show (A.chart j).symm ((A.chart j) x) ∈ G
    rw [(A.chart j).left_inv (hsG hx)]
    exact hψG hx
  have hH : ReciprocityTheory.AnForm.A.PartsHyp (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
      ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) (w ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := by
    unfold ReciprocityTheory.AnForm.A.PartsHyp
    refine ⟨hSo, ?_, hKc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKS, ?_, ?_⟩
    · exact (((hψ j).mono (fun y (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G) => ⟨hy.1, mem_univ _⟩)).of_le three_le_infty_withTop).congr
        (fun y hy => Set.indicator_of_mem hy.1 _)
    · exact ((hw j).mono (fun y (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G) => ⟨hy.1, mem_univ _⟩)).of_le three_le_infty_withTop
    · intro i
      exact (((hΦ i).1 (x0 i) j).mono (fun y (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G) => ⟨hy.1, hGU i hy.2⟩)).of_le three_le_infty_withTop
  have key := (hP e (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
    ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) (w ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) hH).2.2.2.2
  exact key.symm

end Piece

theorem st_byPartsSymm_of (hP : ReciprocityTheory.AnForm.A.PartsStatement) : ByPartsSymmStatement := by
  intro e X _ _ _ A v w hv hw Φ hΦ
  obtain ⟨M, θ, G, j, x0, hθs, -, hθ1, hθG, hGo, hGs, hGU⟩ := st_exists_good_partition A Φ
  have hsum : (fun x => ∑ m, θ m x * v x) = v := by
    funext x
    rw [← Finset.sum_mul, hθ1, one_mul]
  have hL := st_mInt_finset_sum A _ (st_isPotential_cons A hw hΦ) Finset.univ
    (fun m x => θ m x * v x) (fun m => st_smooth_continuous A (st_smooth_mul A (hθs m) hv))
  have hR := st_mInt_cons_finset_sum A Φ hΦ Finset.univ (fun m x => θ m x * v x)
    (fun m => st_smooth_mul A (hθs m) hv) w (st_smooth_continuous A hw)
  rw [hsum] at hL hR
  rw [hL, hR]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact st_symm_piece A Φ hΦ (j m) (G m) (hGo m) (hGs m) (x0 m) (hGU m) hP w _ hw
    (st_smooth_mul A (hθs m) hv) ((tsupport_mul_subset_left).trans (hθG m))

end

end ReciprocityTheory.AnForm.M
end

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

section Leibniz

variable {D : ℕ}

theorem st_fderiv_cplx {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {L : (Fin D → ℂ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f L y) (d : Fin D → ℂ) :
    fderiv ℝ (cplx f) y d = ((L d : ℝ) : ℂ) := by
  have h : HasFDerivAt (cplx f) (Complex.ofRealCLM.comp L) y := by
    unfold cplx
    exact Complex.ofRealCLM.hasFDerivAt.comp y hf
  rw [h.fderiv]
  simp

theorem st_dz_cplx {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {L : (Fin D → ℂ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f L y) (j : Fin D) :
    dz j (cplx f) y = (((L (Pi.single j 1) : ℝ) : ℂ) -
      Complex.I * ((L (Complex.I • Pi.single j 1) : ℝ) : ℂ)) / 2 := by
  simp only [dz, st_fderiv_cplx hf]

theorem st_dzb_cplx {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {L : (Fin D → ℂ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f L y) (j : Fin D) :
    dzb j (cplx f) y = (((L (Pi.single j 1) : ℝ) : ℂ) +
      Complex.I * ((L (Complex.I • Pi.single j 1) : ℝ) : ℂ)) / 2 := by
  simp only [dzb, st_fderiv_cplx hf]

theorem st_gradDens_leibniz {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (a b c : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (ha : DifferentiableAt ℝ a y)
    (hb : DifferentiableAt ℝ b y) (hc : c =ᶠ[𝓝 y] fun z => a z * b z) :
    gradDens φ c b y = a y * gradDens φ b b y + gradDens φ a (fun z => 1 / 2 * (b z * b z)) y := by
  have hLa := ha.hasFDerivAt
  have hLb := hb.hasFDerivAt
  have hc' : HasFDerivAt c (a y • fderiv ℝ b y + b y • fderiv ℝ a y) y :=
    (hLa.mul hLb).congr_of_eventuallyEq hc
  have hbb : HasFDerivAt (fun z => 1 / 2 * (b z * b z))
      ((1 / 2 : ℝ) • (b y • fderiv ℝ b y + b y • fderiv ℝ b y)) y :=
    (hLb.mul hLb).const_mul (1 / 2)
  have e1 : ∀ j, dz j (cplx c) y = (a y : ℂ) * dz j (cplx b) y + (b y : ℂ) * dz j (cplx a) y := by
    intro j
    rw [st_dz_cplx hc', st_dz_cplx hLb, st_dz_cplx hLa]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_mul]
    ring
  have e2 : ∀ k, dzb k (cplx (fun z => 1 / 2 * (b z * b z))) y = (b y : ℂ) * dzb k (cplx b) y := by
    intro k
    rw [st_dzb_cplx hbb, st_dzb_cplx hLb]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_mul]
    push_cast
    ring
  have hmat : gradMat c b y = (a y : ℂ) • gradMat b b y + gradMat a (fun z => 1 / 2 * (b z * b z)) y := by
    ext j k
    simp only [gradMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e1, e2]
    ring
  simp only [gradDens]
  rw [hmat, mdisc_cons_eq_sum, mdisc_cons_eq_sum, mdisc_cons_eq_sum]
  have hs : ∑ j, ∑ k, ((a y : ℂ) • gradMat b b y + gradMat a (fun z => 1 / 2 * (b z * b z)) y) j k *
        mixedCof (fun i => hessC (φ i) y) j k =
      (a y : ℂ) * ∑ j, ∑ k, gradMat b b y j k * mixedCof (fun i => hessC (φ i) y) j k +
        ∑ j, ∑ k, gradMat a (fun z => 1 / 2 * (b z * b z)) y j k * mixedCof (fun i => hessC (φ i) y) j k := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  rw [hs, Complex.add_re, Complex.re_ofReal_mul]
  ring

end Leibniz

variable {e : ℕ} {X : Type} [TopologicalSpace X]

section Piece

variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))


include hΦ hGo hG hGU in
theorem st_partsHyp_piece (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ)
    (hψG : tsupport ψ ⊆ G) :
    PartsHyp (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
      ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) (w ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := by
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤)
    | exact WithTop.coe_le_coe.mpr le_top
    | norm_num
    | simp
  have hUo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    (A.chart j).isOpen_inter_preimage_symm hGo
  have hKc : IsCompact (tsupport ψ) := (isClosed_tsupport ψ).isCompact
  have hK : IsCompact ((A.chart j) '' tsupport ψ) :=
    hKc.image_of_continuousOn ((A.chart j).continuousOn.mono (hψG.trans hG))
  have hsupp : Function.support ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := by
    intro y hy
    obtain ⟨ht, hs⟩ := Set.indicator_apply_ne_zero.mp hy
    exact ⟨(A.chart j).symm y, subset_tsupport _ hs, (A.chart j).right_inv ht⟩
  have htsK : tsupport ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := closure_minimal hsupp hK.isClosed
  have hKU : (A.chart j) '' tsupport ψ ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G := by
    rintro _ ⟨x, hx, rfl⟩
    have hxs := hG (hψG hx)
    refine ⟨(A.chart j).map_source hxs, ?_⟩
    show (A.chart j).symm (A.chart j x) ∈ G
    rw [(A.chart j).left_inv hxs]
    exact hψG hx
  refine ⟨hUo, ?_, ?_, htsK.trans hKU, ?_, fun i => ?_⟩
  · exact (((hψ j).mono fun y (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G) => ⟨hy.1, Set.mem_univ _⟩).congr
      fun y hy => Set.indicator_of_mem hy.1 _).of_le h3
  · exact hK.of_isClosed_subset (isClosed_tsupport _) htsK
  · exact ((hw j).mono fun y (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G) => ⟨hy.1, Set.mem_univ _⟩).of_le h3
  · exact (((hΦ i).1 (x0 i) j).mono fun y (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G) => ⟨hy.1, hGU i hy.2⟩).of_le h3


include hΦ hGo hG hGU in
theorem st_nonpos_piece (hP : PartsStatement) (v θ : X → ℝ) (hv : A.Smooth v)
    (hθ : A.Smooth θ) (hθG : tsupport θ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => θ x * v x) =
      -(∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
          (A.chart j).target.indicator (θ ∘ (A.chart j).symm) y *
            gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) (v ∘ (A.chart j).symm)
              (v ∘ (A.chart j).symm) y) +
        mInt A (Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ) θ := by
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
    | exact WithTop.coe_le_coe.mpr le_top
    | norm_num
    | simp
  have hUo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    (A.chart j).isOpen_inter_preimage_symm hGo
  have hUm := hUo.measurableSet
  have hθv : A.Smooth (fun x => θ x * v x) := st_smooth_mul A hθ hv
  have hθvG : tsupport (fun x => θ x * v x) ⊆ G := (tsupport_mul_subset_left).trans hθG
  have hvv : A.Smooth (fun x => v x * v x) := st_smooth_mul A hv hv
  have hv2 : A.Smooth (fun x => 1 / 2 * (v x * v x)) :=
    (smoothOnAlg A Set.univ Set.univ _ _ (1 / 2) hvv hvv subset_rfl).2
  have hL := st_left_piece (A := A) (Φ := Φ) (j := j) (G := G) (x0 := x0) (hΦ := hΦ) (hGo := hGo) (hG := hG) (hGU := hGU) v (fun x => θ x * v x) hv hθv hθvG
  have hR := st_left_piece (A := A) (Φ := Φ) (j := j) (G := G) (x0 := x0) (hΦ := hΦ) (hGo := hGo) (hG := hG) (hGU := hGU) (fun x => 1 / 2 * (v x * v x)) θ hv2 hθ hθG
  have P1 := hP e (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
    ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G)
    (st_partsHyp_piece A Φ hΦ j G hGo hG x0 hGU v (fun x => θ x * v x) hv hθv hθvG)
  have P2 := hP e (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
    ((A.chart j).target.indicator (θ ∘ (A.chart j).symm)) ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G)
    (st_partsHyp_piece A Φ hΦ j G hGo hG x0 hGU (fun x => 1 / 2 * (v x * v x)) θ hv2 hθ hθG)
  have e1 : mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => θ x * v x) =
      -gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
        ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := hL.trans P1.2.2.2.1
  have e2 : mInt A (Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ) θ =
      -gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
        ((A.chart j).target.indicator (θ ∘ (A.chart j).symm))
        ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := hR.trans P2.2.2.2.1
  have hdiff : ∀ (f : X → ℝ), A.Smooth f → ∀ y ∈ (A.chart j).target,
      DifferentiableAt ℝ (f ∘ (A.chart j).symm) y := by
    intro f hf y hy
    have hm : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∈ 𝓝 y :=
      Filter.inter_mem ((A.chart j).open_target.mem_nhds hy) (by simp)
    exact ((hf j).contDiffAt hm).differentiableAt (by simp)
  have hlb : ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
      gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
        ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm) y =
      (A.chart j).target.indicator (θ ∘ (A.chart j).symm) y *
          gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) (v ∘ (A.chart j).symm)
            (v ∘ (A.chart j).symm) y +
        gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
          ((A.chart j).target.indicator (θ ∘ (A.chart j).symm))
          ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm) y := by
    intro y hy
    have hnt : (A.chart j).target ∈ 𝓝 y := (A.chart j).open_target.mem_nhds hy.1
    have ha : DifferentiableAt ℝ ((A.chart j).target.indicator (θ ∘ (A.chart j).symm)) y := by
      refine (hdiff θ hθ y hy.1).congr_of_eventuallyEq ?_
      filter_upwards [hnt] with z hz
      exact Set.indicator_of_mem hz _
    have hc : (A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm) =ᶠ[𝓝 y]
        fun z => (A.chart j).target.indicator (θ ∘ (A.chart j).symm) z * (v ∘ (A.chart j).symm) z := by
      filter_upwards [hnt] with z hz
      simp [Set.indicator_of_mem hz]
    exact st_gradDens_leibniz _ _ _ _ y ha (hdiff v hv y hy.1) hc
  have hT1 : ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
        (A.chart j).target.indicator (θ ∘ (A.chart j).symm) y *
          gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) (v ∘ (A.chart j).symm)
            (v ∘ (A.chart j).symm) y =
      gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
          ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) -
        gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
          ((A.chart j).target.indicator (θ ∘ (A.chart j).symm))
          ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := by
    rw [gradInt, gradInt, ← integral_sub P1.2.2.1 P2.2.2.1]
    refine setIntegral_congr_fun hUm fun y hy => ?_
    rw [hlb y hy]
    ring
  rw [e1, e2, hT1]
  ring

end Piece

private theorem mInt_cons_const_eq_zero (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (c : ℝ) (g : X → ℝ) :
    mInt A (Fin.cons (LocPot.ofFun fun _ => c) Φ) g = 0 := by
  have hL : ∀ j y, locDens A (Fin.cons (LocPot.ofFun fun _ => c) Φ) j y =
      locDens A (Fin.cons ((LocPot.ofFun fun _ => c).rsmul 0) Φ) j y := by
    intro j y
    have hf : ∀ c' : ℝ, fderiv ℝ (fderiv ℝ (fun _ : Fin (e + 1) → ℂ => c')) y = 0 := by
      intro c'
      have h0 : fderiv ℝ (fun _ : Fin (e + 1) → ℂ => c') = fun _ => 0 :=
        funext fun x => fderiv_const_apply c'
      rw [h0]
      exact fderiv_const_apply _
    have hz : ∀ c' : ℝ, hessC (fun _ : Fin (e + 1) → ℂ => c') y = 0 := by
      intro c'
      funext a b
      simp only [hessC, hf c']
      simp
    simp only [locDens, maDens]
    congr 3
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero, LocPot.ofFun, LocPot.rsmul, zero_mul]
      rw [hz c, hz 0]
    · simp
  have h := mIntRsmul A 0 (LocPot.ofFun fun _ => c) Φ
    (isPotential_ofFun A _ fun j => contDiffOn_const) hΦ g
  rw [zero_mul] at h
  rw [← h]
  simp only [mInt, integralWith, hL]

theorem st_stokes_of (hP : PartsStatement) : StokesStatement := by
  intro e X _ _ _ A w hw Φ hΦ
  have h1 : A.Smooth (fun _ : X => (1 : ℝ)) := fun j => contDiffOn_const
  rw [st_byPartsSymm_of hP A (fun _ => 1) w h1 hw Φ hΦ]
  exact mInt_cons_const_eq_zero A Φ hΦ 1 w

private theorem mInt_finset_sum [CompactSpace X] [T2Space X] {d : ℕ} (A : FinHolAtlas d X)
    (Ψ : Fin d → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) {M : ℕ} (f : Fin M → X → ℝ)
    (hf : ∀ m, Continuous (f m)) (s : Finset (Fin M)) :
    mInt A Ψ (fun x => ∑ m ∈ s, f m x) = ∑ m ∈ s, mInt A Ψ (f m) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := mIntLinear A Ψ hΨ (-1) (fun _ => 0) (fun _ => 0)
      (mIntegrableCont A Ψ hΨ _ continuous_const) (mIntegrableCont A Ψ hΨ _ continuous_const)
    simp only [mul_zero, add_zero] at h
    simp only [Finset.sum_empty]
    linarith
  | insert a s ha ih =>
    have h := mIntLinear A Ψ hΨ 1 (f a) (fun x => ∑ m ∈ s, f m x)
      (mIntegrableCont A Ψ hΨ _ (hf a))
      (mIntegrableCont A Ψ hΨ _ (continuous_finsetSum _ fun m _ => hf m))
    simp only [one_mul] at h
    simp only [Finset.sum_insert ha]
    rw [h, ih]

theorem st_byPartsNonpos_of (hP : PartsStatement) (hN : GradDensNonnegStatement) :
    ByPartsNonposStatement := by
  intro e X _ _ _ A v hv Φ hΦ hpsh
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    | exact WithTop.coe_le_coe.mpr le_top
    | norm_num
    | simp
  obtain ⟨M, θ, G, j, x0, hθs, hθ0, hθ1, hθG, hGo, hGs, hGU⟩ := st_exists_good_partition A Φ
  have hvc := st_smooth_continuous A hv
  have hvv : A.Smooth (fun x => v x * v x) := st_smooth_mul A hv hv
  have hv2 : A.Smooth (fun x => 1 / 2 * (v x * v x)) :=
    (smoothOnAlg A Set.univ Set.univ _ _ (1 / 2) hvv hvv subset_rfl).2
  have hΦ' : ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun v) Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using isPotential_ofFun A v hv
    · simpa using hΦ k
  have hΦ2 : ∀ i, IsPotential A
      ((Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using isPotential_ofFun A _ hv2
    · simpa using hΦ k
  have hsplit : mInt A (Fin.cons (LocPot.ofFun v) Φ) v =
      ∑ m, mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => θ m x * v x) := by
    have hv' : v = fun x => ∑ m, θ m x * v x := funext fun x => by rw [← Finset.sum_mul, hθ1, one_mul]
    calc mInt A (Fin.cons (LocPot.ofFun v) Φ) v
        = mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => ∑ m, θ m x * v x) := by
          congr 1
      _ = _ := mInt_finset_sum A _ hΦ' (fun m x => θ m x * v x)
          (fun m => (st_smooth_continuous A (hθs m)).mul hvc) Finset.univ
  have hpiece := fun m => st_nonpos_piece A Φ hΦ (j m) (G m) (hGo m) (hGs m) (x0 m) (hGU m) hP v (θ m)
    hv (hθs m) (hθG m)
  have hsum2 : ∑ m, mInt A (Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ) (θ m) = 0 := by
    rw [← mInt_finset_sum A _ hΦ2 θ (fun m => st_smooth_continuous A (hθs m)) Finset.univ]
    have h1 : (fun x => ∑ m, θ m x) = fun _ => 1 := funext hθ1
    rw [h1]
    exact st_stokes_of hP A _ hv2 Φ hΦ
  have hnn : ∀ m, 0 ≤ ∫ y in (A.chart (j m)).target ∩ (A.chart (j m)).symm ⁻¹' G m,
      (A.chart (j m)).target.indicator (θ m ∘ (A.chart (j m)).symm) y *
        gradDens (fun i => (Φ i).φ (x0 m i) ∘ (A.chart (j m)).symm) (v ∘ (A.chart (j m)).symm)
          (v ∘ (A.chart (j m)).symm) y := by
    intro m
    have hUo : IsOpen ((A.chart (j m)).target ∩ (A.chart (j m)).symm ⁻¹' G m) :=
      (A.chart (j m)).isOpen_inter_preimage_symm (hGo m)
    refine setIntegral_nonneg hUo.measurableSet fun y hy => mul_nonneg ?_ ?_
    · exact Set.indicator_nonneg (fun z _ => hθ0 m _) y
    · exact hN e _ _ _ hUo
        (fun i => (((hΦ i).1 (x0 m i) (j m)).mono fun z (hz : z ∈ (A.chart (j m)).target ∩ (A.chart (j m)).symm ⁻¹' G m) => ⟨hz.1, hGU m i hz.2⟩).of_le h2)
        (fun i z hz ξ => hpsh i (x0 m i) (j m) z ⟨hz.1, hGU m i hz.2⟩ ξ) y hy
  rw [hsplit, Finset.sum_congr rfl fun m _ => hpiece m, Finset.sum_add_distrib, hsum2, add_zero,
    Finset.sum_neg_distrib]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun m _ => hnn m)

theorem st_mass_step (hP : PartsStatement) [CompactSpace X] [T2Space X] {n : ℕ}
    (A : FinHolAtlas (n + 1) X) (Ψ : Fin (n + 1) → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i))
    (i0 : Fin (n + 1)) (u : X → ℝ) (hu : A.Smooth u) :
    mInt A (Function.update Ψ i0 (Ψ i0 + LocPot.ofFun u)) (fun _ => 1) =
      mInt A Ψ (fun _ => 1) := by
  classical
  set Ψ' := Function.update Ψ i0 (Ψ i0 + LocPot.ofFun u) with hΨ'
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i0
  have hne : ∀ i : Fin n, σ i.succ ≠ i0 := by
    intro i h
    have h2 := congrArg σ h
    simp only [σ, Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
    exact Fin.succ_ne_zero i h2
  set Φ' : Fin n → LocPot X := fun i => Ψ (σ i.succ) with hΦ'
  have h1 : Ψ' ∘ σ = Fin.cons (Ψ i0 + LocPot.ofFun u) Φ' := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [σ, Ψ']
    · simp only [Function.comp, Fin.cons_succ, Φ', Ψ']
      rw [Function.update_of_ne (hne i)]
  have h2 : Ψ ∘ σ = Fin.cons (Ψ i0) Φ' := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [σ]
    · simp [Φ']
  have hPot' : ∀ i, IsPotential A (Φ' i) := fun i => hΨ _
  have hu' := isPotential_ofFun A u hu
  have hint : ∀ Q : LocPot X, IsPotential A Q → MIntegrable A (Fin.cons Q Φ') (fun _ => 1) := by
    intro Q hQ
    refine mIntegrableCont A _ ?_ _ continuous_const
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hQ
    · simpa using hPot' i
  rw [← mIntSymm A Ψ' σ, h1, mIntAdd A _ _ Φ' (hΨ i0) hu' hPot' _ (hint _ (hΨ i0)) (hint _ hu'),
    st_stokes_of hP A u hu Φ' hPot', add_zero, ← h2, mIntSymm]

theorem st_massIndep_of (hP : PartsStatement) : MassIndepStatement := by
  intro e X _ _ _ A Φ u hΦ hu
  cases e with
  | zero =>
    congr 1
    funext i
    exact i.elim0
  | succ n =>
    classical
    have key : ∀ s : Finset (Fin (n + 1)),
        mInt A (fun i => if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i) (fun _ => 1) =
          mInt A Φ (fun _ => 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have hpot : ∀ i, IsPotential A (if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i) := by
          intro i
          split_ifs
          · exact isPotentialAdd A _ _ (hΦ i) (isPotential_ofFun A _ (hu i))
          · exact hΦ i
        have hupd : (fun i => if i ∈ insert a s then Φ i + LocPot.ofFun (u i) else Φ i) =
            Function.update (fun i => if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i) a
              (Φ a + LocPot.ofFun (u a)) := by
          funext i
          by_cases hi : i = a
          · subst hi
            simp
          · simp [hi, Finset.mem_insert]
        have hstep := st_mass_step hP A (fun i => if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i)
          hpot a (u a) (hu a)
        simp only [ha, if_false] at hstep
        rw [hupd, hstep, ih]
    simpa using key Finset.univ

end

end ReciprocityTheory.AnForm.M
end

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

def LocalSymmStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (j : Fin A.n) (χ w : X → ℝ), A.Smooth χ → A.Smooth w →
    tsupport χ ⊆ (A.chart j).source → ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun w) Φ) χ = mInt A (Fin.cons (LocPot.ofFun χ) Φ) w

theorem localSymm : LocalSymmStatement := by
  intro e X _ _ _ A _ χ w hχ hw _ Φ hΦ
  exact st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm A χ w hχ hw Φ hΦ

theorem stokes : StokesStatement := st_stokes_of ReciprocityTheory.AnForm.A.parts_thm
theorem byPartsSymm : ByPartsSymmStatement := st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm
theorem byPartsNonpos : ByPartsNonposStatement :=
  st_byPartsNonpos_of ReciprocityTheory.AnForm.A.parts_thm ReciprocityTheory.AnForm.A.gradDensNonneg_thm
theorem massIndep : MassIndepStatement := st_massIndep_of ReciprocityTheory.AnForm.A.parts_thm

end

end ReciprocityTheory.AnForm.M
