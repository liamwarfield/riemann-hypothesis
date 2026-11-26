module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHessDeriv
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.CovLog

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace SheetSumMeasurable

variable {n d : ℕ}

theorem measurable_maDens {D : ℕ} (ψ : Fin D → (Fin D → ℂ) → ℝ) :
    Measurable (ReciprocityTheory.AnForm.maDens ψ) := by
  set_option synthInstance.maxHeartbeats 200000 in
  set M : ((Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) → Matrix (Fin D) (Fin D) ℂ := fun H i j =>
    ((H (Pi.single i 1) (Pi.single j 1) +
        H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
      Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1) -
        H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ))) / 4 with hMdef
  have hM : Continuous M := continuous_pi fun i => continuous_pi fun j => by
    simp only [hMdef]
    fun_prop
  have hdisc : Continuous fun B : Fin D → Matrix (Fin D) (Fin D) ℂ =>
      (ReciprocityTheory.AnForm.mdisc B).re := by
    unfold ReciprocityTheory.AnForm.mdisc
    exact Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun S _ =>
      continuous_const.mul (Continuous.matrix_det (continuous_finsetSum _ fun k _ =>
        continuous_apply k))))
  have heq : ReciprocityTheory.AnForm.maDens ψ = fun z => (D.factorial : ℝ) * (2 / Real.pi) ^ D *
      (ReciprocityTheory.AnForm.mdisc fun k => M (fderiv ℝ (fderiv ℝ (ψ k)) z)).re := rfl
  rw [heq]
  exact measurable_const.mul ((hdisc.comp (continuous_pi fun k => hM.comp (continuous_apply k))).measurable.comp
    (Measurable.of_eval fun k => measurable_fderiv ℝ _))

theorem sheet_eventuallyEq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s s' : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    (hs' : IsSheetAt J A x s') : s' =ᶠ[𝓝 (A *ᵥ x)] s := by
  obtain ⟨U, hU, hxU, -, -, -, V, hV, hVs⟩ := hs
  obtain ⟨U', hU', hxU', hsd', hsx', hsec', -⟩ := hs'
  have hcont : ContinuousAt s' (A *ᵥ x) := hsd'.continuousOn.continuousAt (hU'.mem_nhds hxU')
  have h1 : ∀ᶠ w in 𝓝 (A *ᵥ x), s' w ∈ V := hcont.preimage_mem_nhds (by rw [hsx']; exact hV)
  filter_upwards [h1, hU.mem_nhds hxU, hU'.mem_nhds hxU'] with w hwV hwU hwU'
  have h := hVs (s' w) ⟨(hsec' w hwU').2, hwV⟩ (by rw [(hsec' w hwU').1]; exact hwU)
  rw [(hsec' w hwU').1] at h
  exact h

theorem term_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (Φ : ℝ → ℝ → ℝ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) {x : Fin n → ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (h : ∃ s, IsSheetAt J A x s) :
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x)) =
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ x)) := by
  rw [IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k =>
    ((sheet_eventuallyEq hs h.choose_spec).fun_comp (φ k))]

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ ContinuousOn s U ∧ (∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
      (∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ IsSheetAt J A x' s) ∧
      ((∃ s, IsSheetAt J A x s) → x ∈ W) := by
  by_cases hx : ∃ s, IsSheetAt J A x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    refine ⟨s, U, interior V ∩ (fun z => A *ᵥ z) ⁻¹' U, hU,
      isOpen_interior.inter (hU.preimage hAc), hsd.continuousOn, hsec, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'U⟩
    have hx's : s (A *ᵥ x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hAx'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, continuousOn_empty _, by simp,
      by simp, fun h => absurd h hx⟩

theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0} := by
    ext x
    simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const


open Classical in
theorem measurable_sheetSum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) (Φ : ℝ → ℝ → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    {g : (Fin n → ℂ) → ℝ} (hg : Measurable g) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    Measurable fun y => sheetSum J A
      (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y := by
  choose σ U W hU hW hσc hσsec hWsh hxW using
    fun x : Fin n → ℂ => exists_sheet_nhds (J := J) (A := A) x

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ W (e k) := by
    intro x hx
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hx⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact ⟨k, hxi⟩

  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hW (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ zeroSet J ∩ W (e k) := fun k x hx =>
    ⟨hx.1, disjointed_subset (fun k => W (e k)) k hx.2⟩
  have hEdisj : ∀ k k' x, x ∈ E k → x ∈ E k' → k = k' := by
    intro k k' x hk hk'
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_disjointed (fun k => W (e k)) hne) hk.2 hk'.2
  have hEcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ E k := by
    intro x hx
    obtain ⟨m, hm⟩ := hcover x hx
    have hxZ : x ∈ zeroSet J := by
      obtain ⟨s, U₀, -, hxU₀, -, hsx, hsec, -⟩ := hx
      rw [← hsx]
      exact (hsec _ hxU₀).2
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hm⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  set t : (Fin n → ℂ) → ℝ := fun x => if h : ∃ s, IsSheetAt J A x s then
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x)) else 0 with ht
  have htdef : ∀ x, t x = if h : ∃ s, IsSheetAt J A x s then
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x)) else 0 := fun x => rfl
  have htE : ∀ k x, x ∈ E k →
      t x = Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k' => φ k' ∘ σ (e k)) (A *ᵥ x)) := by
    intro k x hx
    have hsh := (hWsh (e k) x (hEW k hx)).2
    rw [htdef, dite_eq_left ⟨_, hsh⟩]
    exact term_eq Φ g φ hsh _
  have htS : ∀ x, t x ≠ 0 → ∃ s, IsSheetAt J A x s := by
    intro x hx
    by_contra h
    exact hx (by rw [htdef, dite_eq_right h])

  set σ' : ℕ → (Fin d → ℂ) → Fin n → ℂ := fun k => (U (e k)).piecewise (σ (e k)) fun _ => 0
    with hσ'
  set f : ℕ → (Fin d → ℂ) → ℝ := fun k => (U (e k) ∩ σ' k ⁻¹' E k).indicator
    (fun y => Φ (g (σ' k y)) (ReciprocityTheory.AnForm.maDens (fun k' => φ k' ∘ σ (e k)) y)) with hf
  have hσ'm : ∀ k, Measurable (σ' k) := fun k =>
    (hσc (e k)).measurable_piecewise continuousOn_const (hU (e k)).measurableSet
  have hfm : ∀ k, Measurable (f k) := fun k =>
    (hΦ.comp ((hg.comp (hσ'm k)).prodMk (measurable_maDens _))).indicator
      ((hU (e k)).measurableSet.inter (hσ'm k (hEm k)))

  have hpiece : ∀ (k : ℕ) (y : Fin d → ℂ) (F : Finset (Fin n → ℂ)),
      (∀ x, x ∈ F ↔ x ∈ ComplexSets.fibre J A y) → ∑ x ∈ F, (E k).indicator t x = f k y := by
    intro k y F hF
    by_cases hy : y ∈ U (e k) ∧ σ (e k) y ∈ E k
    · have hσ'y : σ' k y = σ (e k) y := by simp [hσ', Set.piecewise_eq_of_mem _ _ _ hy.1]
      have hx0 : σ (e k) y ∈ F :=
        (hF _).2 ⟨(hEW k hy.2).1, (hσsec (e k) y hy.1).1⟩
      rw [Finset.sum_eq_single_of_mem _ hx0, Set.indicator_of_mem hy.2, htE k _ hy.2,
        (hσsec (e k) y hy.1).1, hf]
      · simp only
        rw [Set.indicator_of_mem (show y ∈ U (e k) ∩ σ' k ⁻¹' E k from
          ⟨hy.1, by simp only [Set.mem_preimage, hσ'y]; exact hy.2⟩), hσ'y]
      · intro x hxF hne
        refine Set.indicator_of_notMem (fun hxE => hne ?_) _
        obtain ⟨-, hAx⟩ := (hF x).1 hxF
        obtain ⟨-, hsh⟩ := hWsh (e k) x (hEW k hxE)
        obtain ⟨-, -, -, -, hsx, -⟩ := hsh
        rw [← hsx, hAx]
    · have hfy : f k y = 0 := by
        rw [hf]
        refine Set.indicator_of_notMem (fun (hmem : y ∈ U (e k) ∩ σ' k ⁻¹' E k) => hy ⟨hmem.1, ?_⟩) _
        have hσ'y : σ' k y = σ (e k) y := by simp [hσ', Set.piecewise_eq_of_mem _ _ _ hmem.1]
        have := hmem.2
        simp only [Set.mem_preimage, hσ'y] at this
        exact this
      rw [hfy]
      refine Finset.sum_eq_zero fun x hxF => Set.indicator_of_notMem (fun hxE => hy ?_) _
      obtain ⟨-, hAx⟩ := (hF x).1 hxF
      obtain ⟨hAU, hsh⟩ := hWsh (e k) x (hEW k hxE)
      obtain ⟨-, -, -, -, hsx, -⟩ := hsh
      rw [hAx] at hAU hsx
      exact ⟨hAU, hsx ▸ hxE⟩

  refine measurable_of_tendsto_metrizable (f := fun N y => ∑ k ∈ Finset.range N, f k y)
    (fun N => Finset.measurable_sum _ fun k _ => hfm k) (tendsto_pi_nhds.2 fun y => ?_)
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  have hsum : sheetSum J A (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y =
      ∑ x ∈ hfin.toFinset, t x := by
    unfold sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    rw [htdef, hx.2]
  refine tendsto_const_nhds.congr' ?_
  have hev : ∀ x ∈ hfin.toFinset, ∀ᶠ N in atTop,
      t x = ∑ k ∈ Finset.range N, (E k).indicator t x := by
    intro x _
    by_cases hx : ∃ s, IsSheetAt J A x s
    · obtain ⟨k0, hk0⟩ := hEcover x hx
      filter_upwards [eventually_gt_atTop k0] with N hN
      rw [Finset.sum_eq_single_of_mem k0 (Finset.mem_range.2 hN), Set.indicator_of_mem hk0]
      intro k _ hk
      exact Set.indicator_of_notMem (fun hxk => hk (hEdisj k k0 x hxk hk0)) _
    · have htx : t x = 0 := by rw [htdef, dite_eq_right hx]
      refine Eventually.of_forall fun N => ?_
      rw [htx]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      by_cases hxk : x ∈ E k
      · rw [Set.indicator_of_mem hxk]; exact htx
      · exact Set.indicator_of_notMem hxk _
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => hpiece k y _ fun x => Set.Finite.mem_toFinset hfin

end SheetSumMeasurable

theorem SheetSumMeasurable.proof : SheetSumMeasurable.Statement := by
  intro n d J A g φ _ _ hA hg _
  refine ⟨SheetSumMeasurable.measurable_sheetSum hA (fun a b => a * b)
    (continuous_fst.mul continuous_snd).measurable hg φ,
    SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
      (continuous_fst.mul continuous_snd).abs.measurable hg φ⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

variable {n : ℕ}

def branchOrder {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (c : VarBranch I 1 q)
    (f : MvPolynomial (Fin n) ℂ) : ℕ∞ :=
  analyticOrderAt (fun τ : ℂ ↦ eval (c.toFun fun _ ↦ τ) f) 0

theorem branchOrder_eq_of_vanishesToOrder {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (c : VarBranch I 1 q) (f : MvPolynomial (Fin n) ℂ) (k : ℕ)
    (h : VanishesToOrder (fun t ↦ eval (c.toFun t) f) c.radius k) : branchOrder c f = k := by
  obtain ⟨H, hHd, hH0, hF⟩ := h
  let ι : ℂ → (Fin 1 → ℂ) := fun τ _ ↦ τ
  have hιd : Differentiable ℂ ι := differentiable_pi.2 fun _ ↦ differentiable_id
  have hball : ∀ τ ∈ Metric.ball (0 : ℂ) c.radius, ι τ ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
    intro τ hτ
    simpa [ι, Metric.mem_ball, dist_zero_right, pi_norm_const] using hτ
  have hg : AnalyticAt ℂ (H ∘ ι) 0 :=
    (hHd.comp hιd.differentiableOn hball).analyticAt (Metric.ball_mem_nhds 0 c.radius_pos)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), eval (c.toFun (ι τ)) f = (τ - 0) ^ k • (H ∘ ι) τ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) c.radius_pos] with τ hτ
    refine (hF _ (hball τ hτ)).trans ?_
    simp [ι]
  have hF' : AnalyticAt ℂ (fun τ : ℂ ↦ eval (c.toFun (ι τ)) f) 0 :=
    AnalyticAt.congr (((analyticAt_id.sub analyticAt_const).pow k).smul hg) (hev.mono fun τ h ↦ h.symm)
  exact hF'.analyticOrderAt_eq_natCast.2
    ⟨H ∘ ι, hg, hH0 _ (hball 0 (Metric.mem_ball_self c.radius_pos)), hev⟩

def BranchNormalisation.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    IsRadicalAt I q → 0 < m →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ringKrullDim (curveLocalRing I q) = 1 ∧
      (∀ f : MvPolynomial (Fin n) ℂ, (∀ b, branchOrder (c b) f ≠ ⊤) →
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ nonZeroDivisors (curveLocalRing I q)) ∧
      ∃ e : Fin m ≃ MaximalSpectrum (curveNormalisation I q), ∀ b,
        Module.length (curveLocalRing I q) (curveNormalisation I q ⧸ (e b).asIdeal) = 1 ∧
        ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime (e b).asIdeal)
              (algebraMap (curveNormalisation I q) (Localization.AtPrime (e b).asIdeal)
                (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
            branchOrder (c b) f

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

noncomputable section

class IsCohenMacaulayLocalRing (B : Type*) [CommRing B] : Prop extends IsLocalRing B, IsNoetherianRing B where
  exists_isWeaklyRegular : ∃ rs : List B, (∀ r ∈ rs, r ∈ maximalIdeal B) ∧
    RingTheory.Sequence.IsWeaklyRegular B rs ∧ ringKrullDim B = (rs.length : WithBot ℕ∞)

variable {n d : ℕ}

instance isMaximal_ker_eval_point (q : Fin n → ℂ) :
    (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun z => ⟨C z, eval_C z⟩

abbrev localRingAt (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Type :=
  Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))

def IsCohenMacaulayAt (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Prop :=
  IsCohenMacaulayLocalRing (localRingAt I q)

def IsTransverseSliceAt (W : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) :
    Prop :=
  ∀ g : MvPolynomial (Fin n) ℂ, eval q g = 0 → ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧ s * g ∈ sliceIdeal W L q

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem abs_finsum_le_finsum_abs {α : Type*} (f : α → ℝ) : |∑ᶠ i, f i| ≤ ∑ᶠ i, |f i| := by
  by_cases h : (Function.support f).Finite
  · have hs : Function.support (fun i => |f i|) ⊆ ↑h.toFinset := by
      intro i hi
      simpa using hi
    rw [finsum_eq_sum_of_support_subset (s := h.toFinset) f (by rw [Set.Finite.coe_toFinset]),
      finsum_eq_sum_of_support_subset _ hs]
    exact Finset.abs_sum_le_sum_abs _ _
  · rw [finsum_of_infinite_support h, abs_zero]
    exact finsum_nonneg fun i => abs_nonneg _

variable {n d : ℕ}

theorem abs_chartDens_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    |chartDens J A f φ y| ≤ chartAbsDens J A f φ y := by
  classical
  refine (abs_finsum_le_finsum_abs _).trans (le_of_eq (finsum_congr fun x => ?_))
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

theorem chartAbsDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ chartAbsDens J A f φ y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity

theorem CutOff.proof (hS : CutOffShape.Statement) (hT : CutOffTube.Statement)
    (hG : CutOffGradient.Statement) : CutOff.Statement := by
  obtain ⟨K, hK⟩ := hG
  intro n d J A P hJ hdim hA hP
  have hA' : ContDiff ℝ ∞ fun x : Fin n → ℂ => A *ᵥ x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff.restrict_scalars ℝ
  have hc : Continuous fun x : Fin n → ℂ => ‖eval (A *ᵥ x) P‖ ^ 2 :=
    ((MvPolynomial.continuous_eval P).comp hA'.continuous).norm.pow 2
  have key : ∀ T : (Fin (d + 1) → ℂ) → ℝ, Integrable T → ∀ (k : ℕ) (F : (Fin (d + 1) → ℂ) → ℝ),
      (∀ y, ‖F y‖ ≤ K / ((k : ℝ) + 1) * T y) → ‖∫ y, F y‖ ≤ K / ((k : ℝ) + 1) * ∫ y, T y :=
    fun T hTi k F hF => (norm_integral_le_of_norm_le (hTi.const_mul _)
      (Eventually.of_forall hF)).trans_eq (integral_const_mul _ _)
  have lim : ∀ c : ℝ, Tendsto (fun k : ℕ => K / ((k : ℝ) + 1) * c) atTop (𝓝 0) := fun c => by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K).mul_const c
    rw [mul_zero, zero_mul] at h
    exact h.congr fun k => by ring
  refine ⟨logLogCutAlong A P, fun k => ((hS _ P).1 k).1.comp hA', fun k x => ((hS _ P).1 k).2.1 _,
    fun k => ⟨{x | ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k}, isOpen_lt hc continuous_const, fun x hx => ?_,
      fun x hx => ((hS _ P).1 k).2.2 _ hx.1⟩, fun x _ hx => (hS _ P).2 _ hx, fun R => ?_,
    fun R φ hφ => ?_⟩
  · have hx0 : eval (A *ᵥ x) P = 0 := hx
    show ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k
    rw [hx0, norm_zero, zero_pow two_ne_zero]
    exact (cutLevel_mem k).1
  · have hTi := hT n d J A P R (fun _ => euclPot) hJ hdim hA hP
      fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
    have hl := (lim (∫ y, tubeDens J A P R (fun _ => euclPot) y)).const_mul 2
    rw [mul_zero] at hl
    refine squeeze_zero_norm (fun k => ?_) hl
    have h := hK n d J A P R (fun _ => euclPot) k
    refine (norm_sub_le _ _).trans ?_
    rw [two_mul]
    exact add_le_add (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.1)
      (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.2)
  · refine squeeze_zero_norm (fun k => key _ (hT n d J A P R φ hJ hdim hA hP hφ) k _ fun y => ?_)
      (lim _)
    rw [Real.norm_of_nonneg (chartAbsDens_nonneg _ _ _ _ y)]
    exact (hK n d J A P R φ k y hJ hdim hA).1

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def BranchLift.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (M : NormalModel J)
    (γ : GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) →
    ∃ Γ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ,
      DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) ∧
      (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ τ) = γ.toFun τ) ∧
      ∀ V ⊆ Metric.ball 0 γ.radius, IsOpen V →
        ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ Γ '' V = zeroSetIn M.ideal ∩ O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {σ : Type*}

instance isPrime_ker_eval_point (w : σ → ℂ) : (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).IsPrime :=
  RingHom.ker_isPrime _

def pointLocalRing (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : Type _ :=
  Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))

instance (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : CommRing (pointLocalRing I w) :=
  inferInstanceAs (CommRing (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))

instance (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : Algebra (MvPolynomial σ ℂ) (pointLocalRing I w) :=
  inferInstanceAs (Algebra (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))

theorem isUnit_algebraMap_pointLocalRing (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (f : MvPolynomial σ ℂ)
    (hf : eval w f ≠ 0) : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) f) := by
  have hu : IsUnit (algebraMap (MvPolynomial σ ℂ)
      (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) f) :=
    IsLocalization.map_units _
      (⟨f, fun h ↦ hf (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl)
  exact hu.map (Ideal.Quotient.mk _)

def NormalModelPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal → IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q →
      ∃ P : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) =
          Ring.ord (pointLocalRing M.ideal w)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) (rename Sum.inl f))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

variable {n d : ℕ}

theorem logLogCut_mem_Icc {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ) :
    logLogCut Q k y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold logLogCut cutStep
  split_ifs
  · simp
  · simp
  · exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem comp_sheet_eventuallyEq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (g : (Fin d → ℂ) → ℝ) :
    (fun w => g (A *ᵥ s w)) =ᶠ[𝓝 (A *ᵥ x)] g := by
  obtain ⟨U, hU, hxU, -, -, hsec, -⟩ := hs
  filter_upwards [hU.mem_nhds hxU] with w hw
  rw [(hsec w hw).1]

theorem maDens_cons_of_hessC_eq_smul {D : ℕ} (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) (c : ℝ)
    (h : hessC f y = (c : ℂ) • hessC g y) :
    maDens (Fin.cons f ψ) y = c * maDens (Fin.cons g ψ) y := by
  have e : ∀ u : (Fin (D + 1) → ℂ) → ℝ,
      (fun k => hessC ((Fin.cons u ψ : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ) k) y) =
        Fin.cons (hessC u y) (fun k => hessC (ψ k) y) := fun u => by
    funext k; exact Fin.cases rfl (fun i => rfl) k
  have hm := mdisc_update_smul
    (Fin.cons (hessC g y) (fun k => hessC (ψ k) y) : Fin (D + 1) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    0 (c : ℂ) (hessC g y)
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at hm
  unfold maDens
  rw [e, e, h, hm, Complex.re_ofReal_mul]
  ring

theorem vecCons_comp {D : ℕ} (f : (Fin n → ℂ) → ℝ) (φ : Fin D → (Fin n → ℂ) → ℝ)
    (s : (Fin (D + 1) → ℂ) → Fin n → ℂ) :
    (fun k => (vecCons f φ : Fin (D + 1) → (Fin n → ℂ) → ℝ) k ∘ s) = Fin.cons (f ∘ s) (fun k => φ k ∘ s) := by
  funext k; exact Fin.cases rfl (fun i => rfl) k

theorem sheetSum_le_mul {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {y : Fin d → ℂ} (hfin : (ComplexSets.fibre J A y).Finite) (c : ℝ)
    (F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (h : ∀ x ∈ ComplexSets.fibre J A y, ∀ s, IsSheetAt J A x s → F x s ≤ c * G x s) :
    sheetSum J A F y ≤ c * sheetSum J A G y := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · exact h x hx _ hs.choose_spec
  · simp

theorem term_le_of_hessC {D : ℕ} {X : Type*} (B : Set X) (w t : X → ℝ) (x : X)
    (hw : |w x| ≤ 1) (hwB : x ∉ B → w x = 0) (ht : 0 ≤ t x) (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) {c e : ℝ}
    (h : hessC f y = (e : ℂ) • hessC g y) (he : |e| ≤ c * t x) :
    |w x * maDens (Fin.cons f ψ) y| ≤ c * |B.indicator t x * maDens (Fin.cons g ψ) y| := by
  rw [maDens_cons_of_hessC_eq_smul f g ψ y e h]
  by_cases hx : x ∈ B
  · rw [Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_of_nonneg ht]
    have hM := abs_nonneg (maDens (Fin.cons g ψ) y)
    calc |w x| * (|e| * |maDens (Fin.cons g ψ) y|) ≤ 1 * (c * t x * |maDens (Fin.cons g ψ) y|) :=
          mul_le_mul hw (mul_le_mul_of_nonneg_right he hM) (by positivity) zero_le_one
      _ = c * (t x * |maDens (Fin.cons g ψ) y|) := by ring
  · rw [hwB hx, zero_mul, abs_zero, Set.indicator_of_notMem hx, zero_mul, abs_zero, mul_zero]

theorem CutOffGradient.proof (hH : LogLogCutHess.Statement) : CutOffGradient.Statement := by
  obtain ⟨K, hK0, hK⟩ := hH
  refine ⟨K, fun n d J A P R φ k y hJ hdim hA => ?_⟩
  have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
  obtain ⟨a, b, ha, hb, hHa, hHb⟩ := hK (d + 1) P k y
  have hc : 0 ≤ K / ((k : ℝ) + 1) := by positivity
  set B := Metric.closedBall (0 : Fin n → ℂ) R
  have ht : ∀ x, 0 ≤ tubeWeight P (A *ᵥ x) := fun x => by
    unfold tubeWeight; split_ifs <;> positivity

  have key : ∀ (w : (Fin n → ℂ) → ℝ) (g : (Fin (d + 1) → ℂ) → ℝ) (e : ℝ),
      (∀ x, |w x| ≤ 1) → (∀ x, x ∉ B → w x = 0) →
      hessC g y = (e : ℂ) • hessC (fun z => logAbsSq P z ^ 2 / 2) y →
      |e| ≤ K / ((k : ℝ) + 1) * tubeWeight P y →
      chartAbsDens J A w (vecCons (fun x => g (A *ᵥ x)) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y := by
    intro w g e hw hwB hg he
    unfold chartAbsDens tubeDens
    refine sheetSum_le_mul hfin _ _ _ fun x hx s hs => ?_
    have hy : A *ᵥ x = y := hx.2
    rw [vecCons_comp, vecCons_comp]
    refine term_le_of_hessC B w (fun x => tubeWeight P (A *ᵥ x)) x (hw x) (hwB x) (ht x) _ _ _ y ?_
      (by rw [hy]; exact he)
    rw [← hy, Function.comp_def, Function.comp_def, hessC_congr' (comp_sheet_eventuallyEq hs g),
      hessC_congr' (comp_sheet_eventuallyEq hs fun z => logAbsSq P z ^ 2 / 2), hy, hg]
  have h1 : ∀ x, |B.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := fun x => by
    unfold Set.indicator; split_ifs <;> simp
  have h0 : ∀ x, x ∉ B → B.indicator (fun _ => (1 : ℝ)) x = 0 := fun x hx => Set.indicator_of_notMem hx _
  refine ⟨key _ (logLogCut P k) a h1 h0 hHa ha, key _ (fun z => logLogCut P k z ^ 2 / 2) b h1 h0 hHb hb,
    key _ (logLogCut P k) a (fun x => ?_) (fun x hx => Set.indicator_of_notMem hx _) hHa ha⟩
  unfold Set.indicator
  split_ifs
  · have hm := logLogCut_mem_Icc P k (A *ᵥ x)
    show |logLogCut P k (A *ᵥ x)| ≤ 1
    rw [abs_of_nonneg hm.1]; exact hm.2
  · simp

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CurveNormalisationFinite.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), IsRadicalAt I q →
    Module.Finite (curveLocalRing I q) (curveNormalisation I q)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchIntDecompose
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def BranchIntDecompose.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      ∃ N ∈ 𝓝 q, ∀ (f : (Fin n → ℂ) → ℝ) (ψ : Fin (d + 1) → (Fin n → ℂ) → ℝ),
        ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        (∀ i, SmoothNear (zeroSet J) (ψ i)) →
          varInt J (d + 1) f ψ =
            ∑ b, ReciprocityTheory.AnForm.maInt (fun k => ψ k ∘ (γ b).toFun) (f ∘ (γ b).toFun)
              (Metric.ball 0 (γ b).radius)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranchInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceBranchInt.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → q ∈ zeroSet W →
    (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W) →
    (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 q, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      ∃ N ∈ 𝓝 q, ∀ (b : Fin m) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
        ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        (∀ i, SmoothNear (zeroSet J) (φ i)) →
          varInt W d f φ =
            ∫ w in Metric.ball (0 : Fin d → ℂ) (γ b).radius,
              f ((γ b).toFun (ReciprocityTheory.AnForm.A.hypIncl w)) *
                ReciprocityTheory.AnForm.A.densHyp (fun k => φ k ∘ (γ b).toFun) w

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

theorem PosPartSplit.proof : PosPartSplit.Statement := by
  classical
  intro n d J A f φ E y hA hE hcov
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartPosDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]

  set T : ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ := fun g x =>
    if h : ∃ s, IsSheetAt J A x s then
      max (g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y) 0 else 0 with hT
  have hT0 : ∀ g x, 0 ≤ T g x := fun g x => by
    simp only [hT]; split_ifs <;> simp
  have hpt : ∀ x ∈ hfin.toFinset,
      ENNReal.ofReal (T f x) = ∑' k, ENNReal.ofReal (T ((E k).indicator f) x) := by
    intro x hx
    have hx' : x ∈ ComplexSets.fibre J A y := hfin.mem_toFinset.mp hx
    by_cases hs : ∃ s, IsSheetAt J A x s
    · obtain ⟨k₀, hk₀⟩ := hcov x hx' hs
      rw [tsum_eq_single k₀]
      · simp only [hT, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : x ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [hT, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [hT, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 f x), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 _ x)).symm

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveProperClosedFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveProperClosedFinite.Statement : Prop :=
  ∀ (n : ℕ) (W K : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1 → ¬ K ≤ W →
      (zeroSet W ∩ zeroSet K).Finite

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCodimOneCompleteIntersection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCodimOneCompleteIntersection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P Q : Ideal (MvPolynomial σ ℂ)) (e : ℕ), P.IsPrime → Q.IsPrime → P ≤ Q →
    IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ P) = (e + 1 : ℕ) → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (e : ℕ) →
      ∃ (c : ℕ) (f : Fin c → MvPolynomial σ ℂ) (h : MvPolynomial σ ℂ),
        c + (e + 1) = Fintype.card σ ∧ (∀ j, f j ∈ P) ∧ h ∉ Q ∧
          ∀ p ∈ P, ∃ k : ℕ, h ^ k * p ∈ Ideal.span (Set.range f)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceReducedGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
          ∀ L ∈ O, IsRadicalAt (sliceIdeal J L q) q

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeEuclMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

theorem TubeEuclMass.proof (hC : TubeCollarMass.Statement) (hD : TubeDeepMass.Statement) :
    TubeEuclMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  have hS : {y : Fin (d + 1) → ℂ | logAbsSq P y < -Real.exp 1} =
      {y | -Real.exp 1 ≤ logAbsSq P y}ᶜ := by
    ext y
    simp [not_le]
  have h := (hC n d J A P R hJ hdim hA hP).add (hD n d J A P R hJ hdim hA hP)
  rw [hS, Set.indicator_self_add_compl] at h
  exact h

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLelongAnnulus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem ne_of_mem_euclBall_diff {n : ℕ} {x z : Fin n → ℂ} {r s : ℝ} (hr : 0 < r)
    (hz : z ∈ euclBall x s \ euclBall x r) : z ≠ x := by
  rintro rfl
  exact hz.2 (mem_euclBall_self z hr)

def RegLelongAnnulus.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → 0 < r → r ≤ s →
      r ^ (2 * d) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y) -
        s ^ (2 * d) * (∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y) =
      r ^ (2 * d) * s ^ (2 * d) * ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
end
