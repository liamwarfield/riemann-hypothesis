module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.OfListTailLog
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailLogOfMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormHolo

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMonoDens
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

def ListMonoDens.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th : Fin D → LocPot X)
    (Om : LocPot X) (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsPotential A (th i)) →
    IsPotential A Om → (∀ i, A.SmoothOn Yo (u i)) → (∀ i, LeviLe A Set.univ 1 (th i) 1 Om) →
    (∀ i, FormNonneg A Yo (potForm (th i) (u i))) →
    ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo →
      0 ≤ locDens A (fun i => potForm (th i) (u i)) j y ∧
        locDens A (fun i => potForm (th i) (u i)) j y ≤ locDens A (fun i => potForm Om (u i)) j y

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StMIntegrableOfDensLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens MIntegrable)

def MIntegrableOfDensLe.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (V : Set X) (Φ Ψ : Fin D → LocPot X),
    IsOpen V → (∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V)) →
    (∀ j, ContinuousOn (locDens A Ψ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V)) →
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ V →
      0 ≤ locDens A Φ j y ∧ locDens A Φ j y ≤ locDens A Ψ j y) →
    ∀ g : X → ℝ, (∀ x, x ∉ V → g x = 0) → MIntegrable A Ψ g → MIntegrable A Φ g

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic locDensCont locDens_nonneg_of_psh)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLocDensContOnOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

def LocDensContOnOpen.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th : Fin D → LocPot X)
    (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn Yo (u i)) →
    ∀ j, ContinuousOn (locDens A (fun i => potForm (th i) (u i)) j)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMonoRaise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)

def ListMonoRaise.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th Om : LocPot X)
    (u : X → ℝ), IsOpen Yo → IsPotential A th → IsPotential A Om → A.SmoothOn Yo u →
    LeviLe A Set.univ 1 th 1 Om → FormNonneg A Yo (potForm th u) → FormNonneg A Yo (potForm Om u)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdMetric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

noncomputable section

theorem BdMetric.proof (hCC : ChartCont.Statement) (hT : BdTransition.Statement)
    (hC : BdCocycle.Statement) (hL : LogNormHolo.Statement) (hW : BdWeight.Statement) :
    BdMetric.Statement := by
  intro X _ _ _ D A R
  choose g hgH hg using fun j k => hT D A R j k
  have hO : ∀ j k, IsOpen (bdDom R j ∩ bdDom R k) := fun j k =>
    (isOpen_bdDom R j).inter (isOpen_bdDom R k)
  have hgC : ∀ j k, ContinuousOn (g j k) (bdDom R j ∩ bdDom R k) := fun j k =>
    (hCC D A _ (hO j k)).2 _ (hgH j k)
  have hcoc := hC D A R g hgC fun j k y hy => (hg j k y hy).2
  obtain ⟨w, hwS, hwP, hwE⟩ := hW D A R g hgH (fun j k y hy => (hg j k y hy).1) hcoc

  have hd : ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k,
      Real.log (w j y) / 2 = Real.log ‖g j k y‖ + Real.log (w k y) / 2 := by
    intro j k y hy
    have hg0 : ‖g j k y‖ ≠ 0 := norm_ne_zero_iff.mpr (hg j k y hy).1
    rw [hwE j k y hy, Real.log_mul (pow_ne_zero 2 hg0) (hwP k y hy.2).ne', Real.log_pow]
    push_cast
    ring
  refine ⟨fun j y => Real.log (w j y) / 2, fun j i => ?_, fun j k y hy => ?_, fun j k y hy => ?_⟩
  · exact ((hwS j i).log fun z hz => (hwP j _ hz.2).ne').div_const 2
  · obtain ⟨V, hV, hyV, hVW, G, hG, hGe⟩ :=
      hL D A _ (g j k) (hO j k) (hgH j k) (fun z hz => (hg j k z hz).1) y hy
    refine ⟨V, hV, hyV, G, hG, fun z hz => ?_⟩
    show Real.log (w j z) / 2 - Real.log (w k z) / 2 = (G z).re
    rw [hd j k z hz.2, ← hGe z hz.1]
    ring
  · have hgp : 0 < ‖g j k y‖ := norm_pos_iff.mpr (hg j k y hy).1
    simp only
    rw [hd j k y hy, (hg j k y hy).2, norm_mul, neg_add, Real.exp_add, Real.exp_neg (Real.log _),
      Real.exp_log hgp]
    field_simp

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdTransition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdTransition.proof (hDense : RegYoDense.Statement) (hEq : BdEqHolo.Statement)
    (hDiv : BdDivides.Statement) : BdTransition.Statement := by
  intro X _ D A R j k
  obtain ⟨u, hu, huc, hue⟩ := hDiv D A R k j
  obtain ⟨v, -, hvc, hve⟩ := hDiv D A R j k
  have hO : bdDom R k ∩ bdDom R j = bdDom R j ∩ bdDom R k := Set.inter_comm _ _
  rw [hO] at hu huc hue
  set O := bdDom R j ∩ bdDom R k with hOdef
  have hOopen : IsOpen O := (isOpen_bdDom R j).inter (isOpen_bdDom R k)

  have hYo : Set.EqOn (fun y => u y * v y) (fun _ => (1 : ℂ)) (O ∩ R.Yo) := by
    intro y ⟨hyO, hyY⟩
    have hne : bdEq R j y ≠ 0 := fun h0 => ((hEq D A R j).2 y hyO.1).1 h0 hyY
    have h1 : bdEq R j y = (u y * v y) * bdEq R j y := by
      rw [mul_assoc, ← hve y hyO, ← hue y hyO]
    have h2 : (u y * v y) * bdEq R j y = 1 * bdEq R j y := by rw [← h1, one_mul]
    exact mul_right_cancel₀ hne h2

  have hall : Set.EqOn (fun y => u y * v y) (fun _ => (1 : ℂ)) O :=
    hYo.of_subset_closure (huc.mul hvc) continuousOn_const Set.inter_subset_left
      ((hDense D A R).open_subset_closure_inter hOopen)
  refine ⟨u, hu, fun y hy => ⟨fun h0 => ?_, hue y hy⟩⟩
  have := hall hy
  simp only [h0, zero_mul] at this
  exact zero_ne_one this

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdDivides
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

theorem BdDivides.proof (hdiv : CoordDivDivisible.Statement) : BdDivides.Statement := by
  intro X _ D A R j k
  set Ω : Set (Fin D → ℂ) := (R.ψ j).target ∩ (R.ψ j).symm ⁻¹' (bdDom R j ∩ bdDom R k) with hΩdef
  have hΩ : IsOpen Ω :=
    (R.ψ j).isOpen_inter_preimage_symm ((isOpen_bdDom R j).inter (isOpen_bdDom R k))
  set F : (Fin D → ℂ) → ℂ := fun z => ∏ i ∈ R.S k, R.ψ k ((R.ψ j).symm z) i with hFdef
  have hF : AnalyticOnNhd ℂ F Ω := by
    intro z hz
    have ht : AnalyticAt ℂ (R.ψ k ∘ (R.ψ j).symm) z :=
      ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans A (R.compat j) (R.compat k) hz.1 hz.2.2.1
    exact Finset.analyticAt_fun_prod (f := fun i z => R.ψ k ((R.ψ j).symm z) i) _
      fun i _ => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt _ |>.comp ht
  have hvan : ∀ z ∈ Ω, z ∈ coordDiv (R.S j) → F z = 0 := by
    intro z hz hzS
    obtain ⟨hzt, ⟨_, hzW⟩, ⟨hyk, hykW⟩⟩ := hz
    have hjz : R.ψ j ((R.ψ j).symm z) = z := (R.ψ j).right_inv hzt
    rw [Set.mem_preimage, hjz] at hzW
    have hnot : (R.ψ j).symm z ∉ R.Yo := fun h => ((R.mem_Yo_iff j z hzW).1 h) hzS
    have hk : R.ψ k ((R.ψ j).symm z) ∈ coordDiv (R.S k) := by
      by_contra hc
      apply hnot
      have := (R.mem_Yo_iff k _ hykW).2 hc
      rwa [(R.ψ k).left_inv hyk] at this
    obtain ⟨i, hi, h0⟩ := hk
    exact Finset.prod_eq_zero hi h0
  obtain ⟨G, hG, hFG⟩ := hdiv D Ω F (R.S j) hΩ hF hvan
  have hmem : ∀ y ∈ bdDom R j ∩ bdDom R k, R.ψ j y ∈ Ω := fun y hy =>
    ⟨(R.ψ j).map_source hy.1.1, by
      show (R.ψ j).symm (R.ψ j y) ∈ bdDom R j ∩ bdDom R k
      rw [(R.ψ j).left_inv hy.1.1]; exact hy⟩
  refine ⟨fun y => G (R.ψ j y), ?_, ?_, ?_⟩
  · intro m w hw
    have hx : (A.chart m).symm w ∈ bdDom R j ∩ bdDom R k := hw.2
    have hc : AnalyticAt ℂ (R.ψ j ∘ (A.chart m).symm) w := ((R.compat j) m).1 w ⟨hw.1, hx.1.1⟩
    exact (hG _ (hmem _ hx)).comp (f := R.ψ j ∘ (A.chart m).symm) hc
  · exact hG.continuousOn.comp ((R.ψ j).continuousOn.mono fun y hy => hy.1.1) hmem
  · intro y hy
    have h := hFG _ (hmem y hy)
    simp only [hFdef, (R.ψ j).left_inv hy.1.1] at h
    simp only [bdEq]
    rw [h, mul_comm]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegRCont
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open Filter Topology

theorem RegRCont.proof : RegRCont.Statement := by
  intro X _ D A R y hy
  set j := bdIdx R y
  have hyU : y ∈ bdDom R j := mem_bdDom_bdIdx R y
  let g : (Fin D → ℂ) → ℝ := fun z =>
    Real.exp 1 + R.f j z - ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)
  have key : ∀ y' ∈ bdDom R j ∩ R.Yo,
      R.ψ j y' ∉ coordDiv (R.S j) ∧ R.r y' = g (R.ψ j y') := by
    rintro y' ⟨⟨hs, hW⟩, hY⟩
    have hinv : (R.ψ j).symm (R.ψ j y') = y' := (R.ψ j).left_inv hs
    have hnot : R.ψ j y' ∉ coordDiv (R.S j) :=
      (R.mem_Yo_iff j _ hW).1 (by rw [hinv]; exact hY)
    refine ⟨hnot, ?_⟩
    have h := R.r_chart j (R.ψ j y') ⟨hW, hnot⟩
    rw [hinv] at h
    exact h
  have hg : ContinuousAt g (R.ψ j y) := by
    have hW : R.ψ j y ∈ R.W j := hyU.2
    have hnd := (key y ⟨hyU, hy⟩).1
    have hf : ContinuousAt (R.f j) (R.ψ j y) :=
      (R.f_cont j).continuousAt ((R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW)
    refine (continuousAt_const.add hf).sub ?_
    refine tendsto_finsetSum (R.S j) fun i hi => ?_
    have hzi : R.ψ j y i ≠ 0 := fun h0 => hnd ⟨i, hi, h0⟩
    have hc : ContinuousAt (fun z : Fin D → ℂ => ‖z i‖ ^ 2) (R.ψ j y) :=
      ((continuous_apply i).norm.pow 2).continuousAt
    exact hc.log (pow_ne_zero 2 (norm_ne_zero_iff.2 hzi))
  have hO : IsOpen (bdDom R j ∩ R.Yo) := (isOpen_bdDom R j).inter R.isOpen_Yo
  have heq : g ∘ R.ψ j =ᶠ[𝓝 y] R.r :=
    Filter.eventually_of_mem (hO.mem_nhds ⟨hyU, hy⟩) fun y' h => ((key y' h).2).symm
  exact ((hg.comp ((R.ψ j).continuousAt hyU.1)).congr heq).continuousWithinAt

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection logNormSec)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem RegSection.proof (hDense : RegYoDense.Statement) (hRC : RegRCont.Statement)
    (hMet : BdMetric.Statement) (hProps : BdSectionProps.Statement)
    (hNorm : BdNormCont.Statement) (hCmp : BdComparison.Statement) : RegSection.Statement := by
  intro X _ _ _ D A R
  obtain ⟨φ, hφ⟩ := hMet D A R
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y : X,
      ‖bdSec R y y‖ * Real.exp (-(bdPot R φ 0).φ y y) ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_univ.image (hNorm D A R φ hφ 0)).bddAbove
    exact ⟨M, fun y => hM ⟨y, Set.mem_univ _, rfl⟩⟩
  have hM1 : (0 : ℝ) < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set c := Real.log (max M 1) with hc
  have hφc : ∀ y : X, (bdPot R φ c).φ y y = (bdPot R φ 0).φ y y + c := fun y => by
    simp [bdPot]
  obtain ⟨hPot, hSec, hOpen⟩ := hProps D A R φ hφ c
  have hle : ∀ y : X, ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y) ≤ 1 := by
    intro y
    rw [hφc, neg_add, Real.exp_add, ← mul_assoc, Real.exp_neg c, hc, Real.exp_log hM1,
      mul_inv_le_iff₀ hM1, one_mul]
    exact (hM y).trans (le_max_left _ _)
  refine ⟨bdPot R φ c, bdSec R, hPot, hSec, hle, hOpen, hDense D A R, hRC D A R, ?_,
    hCmp D A R φ hφ c⟩
  have hne : ∀ y ∈ R.Yo, ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y) ≠ 0 := by
    intro y hy
    rw [← hOpen] at hy
    exact mul_ne_zero (norm_ne_zero_iff.2 hy) (Real.exp_pos _).ne'
  have hlog : ContinuousOn (fun y => logNormSec (bdPot R φ c) (bdSec R) y) R.Yo :=
    (hNorm D A R φ hφ c).continuousOn.log hne
  exact continuousOn_const.sub (continuousOn_const.mul hlog)

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailShift
section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.IntegrableOnTargetOfMIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot ChartPartition mInt MIntegrable integralWith locDens)

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

theorem chartPartition_le_one {A : FinHolAtlas e X} (P : ChartPartition A) (j : Fin A.n) (x : X) :
    P.χ j x ≤ 1 := by
  rw [← P.sum_eq_one x]
  exact Finset.single_le_sum (fun k _ => P.nonneg k x) (Finset.mem_univ j)

theorem integrableOn_target_of_mIntegrable [CompactSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (P : ChartPartition A) {g : X → ℝ} (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y)
      (A.chart j).target := by
  have hsub := P.tsupport_subset j
  have hKc : IsCompact ((A.chart j) '' tsupport (P.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn ((A.chart j).continuousOn.mono hsub)
  have hKt : (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (hsub hx)
  have hχc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have h := (P.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at h
    exact h
  have hKm : MeasurableSet ((A.chart j) '' tsupport (P.χ j)) := hKc.isClosed.measurableSet
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have h1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) ((A.chart j) '' tsupport (P.χ j)) :=
    Integrable.bdd_mul (c := 1) (hg j _ hKt hKc) ((hχc.mono hKt).aestronglyMeasurable hKm)
      ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun y _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _)]
        exact chartPartition_le_one P j _))
  refine (h1.of_forall_sdiff_eq_zero hT fun y hy => ?_).congr_fun (fun y _ => by ring) hT
  have : (A.chart j).symm y ∉ tsupport (P.χ j) := fun h => hy.2 ⟨_, h, (A.chart j).right_inv hy.1⟩
  rw [image_eq_zero_of_notMem_tsupport this, zero_mul]

theorem mInt_le_mul_of_le [CompactSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (V : Set X)
    {f g : X → ℝ} {c : ℝ} (hg : MIntegrable A Φ g)
    (hdens : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ V → 0 ≤ locDens A Φ j y)
    (hf0 : ∀ x, 0 ≤ f x) (hfV : ∀ x ∉ V, f x = 0) (hgV : ∀ x ∉ V, g x = 0)
    (hfg : ∀ x ∈ V, f x ≤ c * g x) : mInt A Φ f ≤ c * mInt A Φ g := by
  classical
  unfold mInt
  split_ifs with h
  · unfold integralWith
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← integral_const_mul]
    have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
    refine integral_mono_of_nonneg ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall fun y hy => ?_))
      ((integrableOn_target_of_mIntegrable A Φ h.some hg j).const_mul c)
      ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall fun y hy => ?_))
    · by_cases hV : (A.chart j).symm y ∈ V
      · exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hf0 _)) (hdens j y hy hV)
      · simp [hfV _ hV]
    · by_cases hV : (A.chart j).symm y ∈ V
      · calc h.some.χ j ((A.chart j).symm y) * f ((A.chart j).symm y) * locDens A Φ j y
            ≤ h.some.χ j ((A.chart j).symm y) * (c * g ((A.chart j).symm y)) * locDens A Φ j y :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfg _ hV) (h.some.nonneg j _))
                (hdens j y hy hV)
          _ = c * (h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y) := by ring
      · simp [hfV _ hV, hgV _ hV]
  · simp

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

theorem log_le_of_abs_sub_le {B a b : ℝ} (hb : Real.exp 1 ≤ b) (ha : 0 < a) (hab : |a - b| ≤ B) :
    Real.log a ≤ (1 + max B 0) * Real.log b := by
  have hb0 : 0 < b := lt_of_lt_of_le (Real.exp_pos 1) hb
  have hlb : 1 ≤ Real.log b := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hb
  have hB : 0 ≤ max B 0 := le_max_right _ _
  have hb1 : 1 ≤ b := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hb
  have h1 : a ≤ b * (1 + max B 0) := by
    have := (abs_le.1 hab).2
    have := le_max_left B 0
    nlinarith [mul_nonneg (sub_nonneg.2 hb1) hB]
  calc Real.log a ≤ Real.log (b * (1 + max B 0)) := Real.log_le_log ha h1
    _ = Real.log b + Real.log (1 + max B 0) := Real.log_mul hb0.ne' (by positivity)
    _ ≤ Real.log b + max B 0 := by
      linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + max B 0 by positivity)]
    _ ≤ (1 + max B 0) * Real.log b := by nlinarith [mul_nonneg hB (sub_nonneg.2 hlb)]

theorem TailShift.proof : TailShift.Statement := by
  intro D B CE
  set Bp := max B 0 with hBpdef
  set R1 := max (Real.exp 1 + Bp) (2 * Bp)
  refine ⟨2 * (1 + Bp) * max CE 0 * R1, ?_⟩
  intro X _ _ _ A Yo r r' T hYo hr hr' hre hr'e hB hdens hT
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have he := Real.exp_pos 1
  have hBp : 0 ≤ Bp := le_max_right _ _
  have hlog : ∀ x ∈ Yo, Real.log (r x) ≤ (1 + Bp) * Real.log (r' x) := fun x hx =>
    log_le_of_abs_sub_le (hr'e x hx) (lt_of_lt_of_le he (hre x hx)) (hB x hx)
  have hl' : ∀ x ∈ Yo, 1 ≤ Real.log (r' x) := fun x hx => by
    rw [← Real.log_exp 1]; exact Real.log_le_log he (hr'e x hx)
  have hl : ∀ x ∈ Yo, 1 ≤ Real.log (r x) := fun x hx => by
    rw [← Real.log_exp 1]; exact Real.log_le_log he (hre x hx)

  have key : ∀ R₀ R', Real.exp 1 ≤ R' → (∀ x ∈ Yo, R₀ ≤ r x → R' ≤ r' x) →
      mInt A T ((tail Yo r R₀).indicator fun x => Real.log (r x)) ≤
        (1 + Bp) * mInt A T ((tail Yo r' R').indicator fun x => Real.log (r' x)) := by
    intro R₀ R' hR' hsub
    refine mInt_le_mul_of_le A T Yo (hT R' hR').1 hdens (fun x => ?_)
      (fun x hx => Set.indicator_of_notMem (by exact fun h => hx h.1) _)
      (fun x hx => Set.indicator_of_notMem (by exact fun h => hx h.1) _) (fun x hx => ?_)
    · by_cases h : x ∈ tail Yo r R₀
      · rw [Set.indicator_of_mem h]; linarith [hl x h.1]
      · rw [Set.indicator_of_notMem h]
    · by_cases h : R₀ ≤ r x
      · rw [Set.indicator_of_mem (show x ∈ tail Yo r R₀ from ⟨hx, h⟩),
          Set.indicator_of_mem (show x ∈ tail Yo r' R' from ⟨hx, hsub x hx h⟩)]
        exact hlog x hx
      · rw [Set.indicator_of_notMem (show x ∉ tail Yo r R₀ from fun h' => h h'.2)]
        by_cases h' : R' ≤ r' x
        · rw [Set.indicator_of_mem (show x ∈ tail Yo r' R' from ⟨hx, h'⟩)]
          nlinarith [hl' x hx]
        · rw [Set.indicator_of_notMem (show x ∉ tail Yo r' R' from fun h'' => h' h''.2)]; simp

  have hint : ∀ R₀, MIntegrable A T ((tail Yo r R₀).indicator fun x => Real.log (r x)) := by
    intro R₀ j K hK hKc
    have htm : MeasurableSet (tail Yo r R₀) := by
      have : tail Yo r R₀ = Yo \ (Yo ∩ r ⁻¹' Set.Iio R₀) := by
        ext x
        simp only [tail, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_Iio, not_and, not_lt]
        exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
      rw [this]
      exact hYo.measurableSet.diff (hr.isOpen_inter_preimage hYo isOpen_Iio).measurableSet
    have hGc : ContinuousOn (fun x => Real.log (r x) / Real.log (r' x)) (tail Yo r R₀) :=
      ((hr.log fun x hx => (lt_of_lt_of_le he (hre x hx)).ne').div
        (hr'.log fun x hx => (lt_of_lt_of_le he (hr'e x hx)).ne')
        fun x hx => (lt_of_lt_of_le one_pos (hl' x hx)).ne').mono fun x hx => hx.1
    classical
    have hGm : Measurable ((tail Yo r R₀).indicator fun x => Real.log (r x) / Real.log (r' x)) := by
      have := hGc.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) htm
      convert this using 1
      funext x
      simp [Set.indicator, Set.piecewise]
    have hT' : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
    have hsm : AEMeasurable (fun y => (tail Yo r R₀).indicator
        (fun x => Real.log (r x) / Real.log (r' x)) ((A.chart j).symm y)) (volume.restrict K) :=
      (hGm.comp_aemeasurable ((A.chart j).continuousOn_symm.aemeasurable hT')).mono_measure
        (Measure.restrict_mono hK le_rfl)
    have hid : ∀ x, (tail Yo r R₀).indicator (fun x => Real.log (r x)) x =
        (tail Yo r R₀).indicator (fun x => Real.log (r x) / Real.log (r' x)) x *
          (tail Yo r' (Real.exp 1)).indicator (fun x => Real.log (r' x)) x := by
      intro x
      by_cases h : x ∈ tail Yo r R₀
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h,
          Set.indicator_of_mem (show x ∈ tail Yo r' (Real.exp 1) from ⟨h.1, hr'e x h.1⟩),
          div_mul_cancel₀ _ (lt_of_lt_of_le one_pos (hl' x h.1)).ne']
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    have e1 : (fun y => (tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) *
        locDens A T j y) = fun y => (tail Yo r R₀).indicator
          (fun x => Real.log (r x) / Real.log (r' x)) ((A.chart j).symm y) *
          ((tail Yo r' (Real.exp 1)).indicator (fun x => Real.log (r' x)) ((A.chart j).symm y) *
            locDens A T j y) := by
      funext y
      rw [hid, mul_assoc]
    rw [e1]
    refine Integrable.bdd_mul (c := 1 + Bp) ((hT (Real.exp 1) le_rfl).1 j K hK hKc)
      hsm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    by_cases h : (A.chart j).symm y ∈ tail Yo r R₀
    · rw [Set.indicator_of_mem h]
      have h1 := hl' _ h.1
      have h3 := hl _ h.1
      rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith)), div_le_iff₀ (by linarith)]
      exact hlog _ h.1
    · rw [Set.indicator_of_notMem h, abs_zero]
      linarith

  intro R₀ hR₀
  refine ⟨hint R₀, ?_⟩
  have hlR : 1 ≤ Real.log R₀ := by rw [← Real.log_exp 1]; exact Real.log_le_log he hR₀
  have hR0 : 0 < R₀ := lt_of_lt_of_le he hR₀
  have hR1a : Real.exp 1 + Bp ≤ R1 := le_max_left _ _
  have hR1b : 2 * Bp ≤ R1 := le_max_right _ _
  have hCE : CE ≤ max CE 0 := le_max_left _ _
  have hCE0 : 0 ≤ max CE 0 := le_max_right _ _
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL0 : 0 ≤ Real.log R₀ ^ (D + 1) := pow_nonneg (by linarith) _
  have hL1 : 1 ≤ Real.log R₀ ^ (D + 1) := one_le_pow₀ hlR
  have hBp1 : 0 ≤ 1 + Bp := by linarith
  by_cases hbig : R1 ≤ R₀
  · have hR' : Real.exp 1 ≤ R₀ - Bp := by linarith
    have hpos : 0 < R₀ - Bp := by linarith
    refine (key R₀ (R₀ - Bp) hR' fun x hx h => ?_).trans ?_
    · have := (abs_le.1 (hB x hx)).2
      linarith [le_max_left B 0]
    have hb := (hT (R₀ - Bp) hR').2
    have hlog1 : 0 ≤ Real.log (R₀ - Bp) := Real.log_nonneg (by linarith)
    have hpow : Real.log (R₀ - Bp) ^ (D + 1) ≤ Real.log R₀ ^ (D + 1) :=
      pow_le_pow_left₀ hlog1 (Real.log_le_log hpos (by linarith)) _
    have s1 : CE * Real.log (R₀ - Bp) ^ (D + 1) / (R₀ - Bp) ≤
        max CE 0 * Real.log R₀ ^ (D + 1) / (R₀ - Bp) :=
      div_le_div_of_nonneg_right (mul_le_mul hCE hpow (pow_nonneg hlog1 _) hCE0) hpos.le
    have s2 : max CE 0 * Real.log R₀ ^ (D + 1) / (R₀ - Bp) ≤
        max CE 0 * Real.log R₀ ^ (D + 1) * 2 / R₀ := by
      rw [div_le_div_iff₀ hpos hR0]
      nlinarith [mul_nonneg (mul_nonneg hCE0 hL0) (show 0 ≤ 2 * (R₀ - Bp) - R₀ by linarith)]
    have s3 : 2 * (1 + Bp) * max CE 0 * Real.log R₀ ^ (D + 1) ≤
        2 * (1 + Bp) * max CE 0 * R1 * Real.log R₀ ^ (D + 1) := by
      have h0 : 0 ≤ 2 * (1 + Bp) * max CE 0 * Real.log R₀ ^ (D + 1) := by positivity
      nlinarith [mul_nonneg h0 (show 0 ≤ R1 - 1 by linarith)]
    calc (1 + Bp) * mInt A T ((tail Yo r' (R₀ - Bp)).indicator fun x => Real.log (r' x))
        ≤ (1 + Bp) * (max CE 0 * Real.log R₀ ^ (D + 1) * 2 / R₀) :=
          mul_le_mul_of_nonneg_left (hb.trans (s1.trans s2)) hBp1
      _ = 2 * (1 + Bp) * max CE 0 * Real.log R₀ ^ (D + 1) / R₀ := by ring
      _ ≤ 2 * (1 + Bp) * max CE 0 * R1 * Real.log R₀ ^ (D + 1) / R₀ :=
          div_le_div_of_nonneg_right s3 hR0.le
  · replace hbig := not_le.1 hbig
    refine (key R₀ (Real.exp 1) le_rfl fun x hx _ => hr'e x hx).trans ?_
    have hb := (hT (Real.exp 1) le_rfl).2
    rw [Real.log_exp, one_pow, mul_one] at hb
    have s1 : CE / Real.exp 1 ≤ max CE 0 := by
      rw [div_le_iff₀ he]; nlinarith [mul_nonneg hCE0 (show 0 ≤ Real.exp 1 - 1 by linarith)]
    have hZ : 0 ≤ (1 + Bp) * max CE 0 := mul_nonneg hBp1 hCE0
    have s2 : R₀ ≤ 2 * R1 * Real.log R₀ ^ (D + 1) := by nlinarith
    calc (1 + Bp) * mInt A T ((tail Yo r' (Real.exp 1)).indicator fun x => Real.log (r' x))
        ≤ (1 + Bp) * max CE 0 := mul_le_mul_of_nonneg_left (hb.trans s1) hBp1
      _ ≤ 2 * (1 + Bp) * max CE 0 * R1 * Real.log R₀ ^ (D + 1) / R₀ := by
          rw [le_div_iff₀ hR0]
          nlinarith [mul_le_mul_of_nonneg_left s2 hZ]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PMIntMonoOfDensLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens mInt MIntegrable ChartPartition integralWith)

theorem MIntMonoOfDensLe.proof : MIntMonoOfDensLe.Statement := by
  intro D X _ _ A V Φ Ψ hd g hg0 hgV hgi
  unfold mInt
  split_ifs with h
  · unfold integralWith
    refine Finset.sum_le_sum fun j _ => ?_
    have hTm := (A.chart j).open_target.measurableSet
    obtain ⟨hKc, hKs⟩ := ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j)
      (isClosed_tsupport (h.some.χ j)) (h.some.tsupport_subset j)
    have hcc := ReciprocityTheory.AnForm.M.chi_comp_continuousOn h.some j
    have hint : IntegrableOn (fun y => h.some.χ j ((A.chart j).symm y) *
        g ((A.chart j).symm y) * locDens A Ψ j y) (A.chart j).target := by
      refine ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j)
        (Z := tsupport (h.some.χ j)) (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
      have h1 := (hgi j _ hKs hKc).mul_continuousOn (hcc.mono hKs) hKc
      exact h1.congr_fun (fun y _ => by ring) hKc.measurableSet
    refine integral_mono_of_nonneg (ae_restrict_of_forall_mem hTm fun y hy => ?_) hint
      (ae_restrict_of_forall_mem hTm fun y hy => ?_)
    · by_cases hyV : (A.chart j).symm y ∈ V
      · exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hg0 _)) (hd j y hy hyV).1
      · simp [hgV _ hyV]
    · by_cases hyV : (A.chart j).symm y ∈ V
      · exact mul_le_mul_of_nonneg_left (hd j y hy hyV).2 (mul_nonneg (h.some.nonneg j _) (hg0 _))
      · simp [hgV _ hyV]
  · exact le_rfl

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMono
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem ListMono.proof (hRaise : ListMonoRaise.Statement) (hDens : ListMonoDens.Statement)
    (hCont : LocDensContOnOpen.Statement) (hInt : MIntegrableOfDensLe.Statement)
    (hMono : MIntMonoOfDensLe.Statement) : ListMono.Statement := by
  intro X _ _ _ D A Yo r Om C₁ th u hYo hT
  have hdens := hDens A Yo th Om.pot u hYo (fun i => (hT i).th_pot) Om.isPot
    (fun i => (hT i).u_smooth) (fun i => (hT i).th_le) (fun i => (hT i).nonneg)
  refine ⟨fun i => hRaise A Yo (th i) Om.pot (u i) hYo (hT i).th_pot Om.isPot (hT i).u_smooth
    (hT i).th_le (hT i).nonneg, fun j y hy hY => (hdens j y hy hY).1, fun g hg0 hgV hgA => ?_⟩
  have hcT := hCont A Yo th u hYo (fun i => (hT i).th_pot) (fun i => (hT i).u_smooth)
  have hcA := hCont A Yo (fun _ => Om.pot) u hYo (fun _ => Om.isPot) (fun i => (hT i).u_smooth)
  exact ⟨hInt A Yo _ _ hYo hcT hcA hdens g hgV hgA, hMono A Yo _ _ hdens g hg0 hgV hgA⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMonoDens
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Topology
open scoped ComplexOrder Matrix
open ReciprocityTheory.AnForm (levi hessC maDens)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

theorem ListMonoDens.proof : ListMonoDens.Statement := by
  intro D X _ A Yo th Om u hYo hth hOm hu hle hnn j y hy hyY
  set p := (A.chart j).symm y with hp

  set f : Fin D → (Fin D → ℂ) → ℝ := fun i y' => (th i).φ p ((A.chart j).symm y') with hf
  set v : Fin D → (Fin D → ℂ) → ℝ := fun i y' => u i ((A.chart j).symm y') with hv
  set o : (Fin D → ℂ) → ℝ := fun y' => Om.φ p ((A.chart j).symm y') with ho
  have hfC : ∀ i, ContDiffAt ℝ 2 (f i) y := fun i =>
    ReciprocityTheory.AnForm.M.pot_contDiffAt_two (hth i) p j hy ((th i).mem_U p)
  have hoC : ContDiffAt ℝ 2 o y :=
    ReciprocityTheory.AnForm.M.pot_contDiffAt_two hOm p j hy (Om.mem_U p)
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo) :=
    (A.chart j).isOpen_inter_preimage_symm hYo
  have hvC : ∀ i, ContDiffAt ℝ 2 (v i) y := fun i =>
    ((hu i j).contDiffAt (hopen.mem_nhds ⟨hy, hyY⟩)).of_le (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
  have hgC : ∀ i, ContDiffAt ℝ 2 (fun y' => o y' + (-1) * f i y') y := fun i =>
    hoC.add (contDiffAt_const.mul (hfC i))

  have hA : ∀ i, (hessC (fun y' => f i y' + v i y') y).PosSemidef := fun i =>
    ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y ((hfC i).add (hvC i)) fun w =>
      hnn i p j y ⟨hy, hyY, (th i).mem_U p, Set.mem_univ _⟩ w

  have hB : ∀ i, (hessC (fun y' => o y' + (-1) * f i y') y).PosSemidef := fun i => by
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y (hgC i)
      fun w => ?_
    rw [ReciprocityTheory.AnForm.levi_add_smul (-1) hoC (hfC i) w]
    have h := hle i p j y ⟨hy, ⟨⟨Set.mem_univ _, (th i).mem_U p⟩, Om.mem_U p⟩⟩ w
    have h' : 1 * levi (f i) y w ≤ 1 * levi o y w := h
    linarith

  have hsum : ∀ i, hessC (fun y' => o y' + v i y') y =
      hessC (fun y' => f i y' + v i y') y + hessC (fun y' => o y' + (-1) * f i y') y := fun i => by
    rw [← ReciprocityTheory.AnForm.A.hessC_add _ _ y ((hfC i).add (hvC i))
      (hgC i)]
    congr 1
    funext y'
    ring
  have e1 : locDens A (fun i => potForm (th i) (u i)) j y =
      maDens (fun i y' => f i y' + v i y') y := rfl
  have e2 : locDens A (fun i => potForm Om (u i)) j y = maDens (fun i y' => o y' + v i y') y := rfl
  rw [e1, e2]
  refine ⟨ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y hA, ?_⟩
  unfold maDens
  refine mul_le_mul_of_nonneg_left (ReciprocityTheory.AnForm.A.mdisc_re_mono _ _ hA fun i => ?_) (by positivity)
  simpa [hsum i] using hB i

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PMIntegrableOfDensLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens MIntegrable)

theorem MIntegrableOfDensLe.proof : MIntegrableOfDensLe.Statement := by
  intro D X _ A V Φ Ψ hV hΦc hΨc hle g hg hΨ j K hK hKc
  set e := A.chart j
  set dΦ := locDens A Φ j
  set dΨ := locDens A Ψ j
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.isOpen_inter_preimage_symm hV
  set W := (e.target ∩ e.symm ⁻¹' V) ∩ dΨ ⁻¹' Set.Ioi 0 with hWdef
  have hW : IsOpen W := (hΨc j).isOpen_inter_preimage hO isOpen_Ioi
  set q : (Fin D → ℂ) → ℝ := W.indicator (fun y => dΦ y / dΨ y) with hqdef
  have hqc : ContinuousOn (fun y => dΦ y / dΨ y) W :=
    ((hΦc j).mono Set.inter_subset_left).div ((hΨc j).mono Set.inter_subset_left)
      (fun y hy => (ne_of_gt hy.2))
  have hqm : AEStronglyMeasurable q (volume.restrict K) :=
    ((aestronglyMeasurable_indicator_iff hW.measurableSet).2
      (hqc.aestronglyMeasurable hW.measurableSet)).restrict
  have hqb : ∀ y, ‖q y‖ ≤ 1 := by
    intro y
    by_cases hy : y ∈ W
    · have hpos : 0 < dΨ y := hy.2
      obtain ⟨h0, h1⟩ := hle j y hy.1.1 hy.1.2
      rw [hqdef, Set.indicator_of_mem hy, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg h0 hpos.le)]
      exact (div_le_one hpos).2 h1
    · rw [hqdef, Set.indicator_of_notMem hy, norm_zero]
      exact zero_le_one
  have hint : IntegrableOn (fun y => (g (e.symm y) * dΨ y) * q y) K :=
    Integrable.mul_bdd (hΨ j K hK hKc) hqm (Filter.Eventually.of_forall hqb)
  refine hint.congr_fun ?_ hKc.measurableSet
  intro y hy
  have hyt : y ∈ e.target := hK hy
  simp only
  by_cases hyV : e.symm y ∈ V
  · obtain ⟨h0, h1⟩ := hle j y hyt hyV
    by_cases hpos : 0 < dΨ y
    · have hyW : y ∈ W := ⟨⟨hyt, hyV⟩, hpos⟩
      rw [hqdef, Set.indicator_of_mem hyW]
      field_simp
    · have hyW : y ∉ W := fun h => hpos h.2
      have hz : dΦ y = 0 := le_antisymm (h1.trans (not_lt.1 hpos)) h0
      rw [hqdef, Set.indicator_of_notMem hyW, hz]
      ring
  · rw [hg _ hyV]
    ring

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLocDensContOnOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens potSmoothOn hessCGerm maDens_congr_hessC
  maDens_continuousOn)

theorem LocDensContOnOpen.proof : LocDensContOnOpen.Statement := by
  intro D X _ A Yo th u hYo hth hu j y0 hy0
  apply ContinuousAt.continuousWithinAt
  have hu2 : ∀ i, ContDiffOn ℝ 2 (u i ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo) :=
    fun i => (hu i j).of_le (WithTop.coe_le_coe.2 le_top)
  have hNo : IsOpen ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0))) :=
    (A.chart j).isOpen_inter_preimage_symm
      (hYo.inter (isOpen_iInter_of_finite fun i => (th i).isOpen_U _))
  have hy0N : y0 ∈ (A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0)) :=
    ⟨hy0.1, hy0.2, Set.mem_iInter.2 fun i => (th i).mem_U _⟩
  have hsm : ∀ i, ContDiffOn ℝ 2 (fun y' => (th i).φ ((A.chart j).symm y0) ((A.chart j).symm y') +
      u i ((A.chart j).symm y')) ((A.chart j).target ∩
        (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0))) := fun i =>
    ((potSmoothOn A (th i) (hth i) _ j).mono (t := (A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0)))
      fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.2 i⟩).add
      ((hu2 i).mono (t := (A.chart j).target ∩
        (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0)))
        fun y hy => ⟨hy.1, hy.2.1⟩)
  have heq : ReciprocityTheory.AnForm.maDens (fun i y' => (th i).φ ((A.chart j).symm y0) ((A.chart j).symm y') +
      u i ((A.chart j).symm y')) =ᶠ[nhds y0] locDens A (fun i => potForm (th i) (u i)) j := by
    filter_upwards [hNo.mem_nhds hy0N] with y hy
    unfold locDens
    apply maDens_congr_hessC
    intro i
    have hp0 : (A.chart j).symm y ∈ (th i).U ((A.chart j).symm y0) := Set.mem_iInter.1 hy.2.2 i
    obtain ⟨W, hWo, hyW, G, hG, hGeq⟩ :=
      (hth i).2 ((A.chart j).symm y) ((A.chart j).symm y0) ((A.chart j).symm y) ⟨(th i).mem_U _, hp0⟩
    have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U ((A.chart j).symm y0))) :=
      (A.chart j).isOpen_inter_preimage_symm
        ((hWo.inter ((th i).isOpen_U _)).inter ((th i).isOpen_U _))
    have hyV : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U ((A.chart j).symm y0)) :=
      ⟨hy.1, ⟨hyW, (th i).mem_U _⟩, hp0⟩
    have h1 : (fun y' => (potForm (th i) (u i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[nhds y]
        (fun w => ((th i).φ ((A.chart j).symm y0) ((A.chart j).symm w) + u i ((A.chart j).symm w)) +
          ((G ∘ (A.chart j).symm) w).re) := by
      filter_upwards [hVo.mem_nhds hyV] with w hw
      have := hGeq ((A.chart j).symm w) hw.2
      show (th i).φ _ _ + u i _ = _
      simp only [Function.comp_apply]
      linarith
    exact ((hessCGerm _ _ _ h1).trans (ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _
      ((hsm i).contDiffAt (hNo.mem_nhds hy)) (hG j y ⟨hy.1, hyW⟩))).symm
  refine ContinuousAt.congr ?_ heq
  exact (maDens_continuousOn _ _ hNo hsm).continuousAt (hNo.mem_nhds hy0N)

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMonoRaise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_add_smul levi_re_analytic)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential potSmoothAt)

theorem ListMonoRaise.proof : ListMonoRaise.Statement := by
  intro D X _ A Yo th Om u hYo hth hOm hu hle hnn x k y hy w
  set s := (A.chart k).symm with hs
  have hyt : y ∈ (A.chart k).target := hy.1
  have hyYo : s y ∈ Yo := hy.2.1
  have hyOx : s y ∈ Om.U x := hy.2.2.1

  have hadd : ∀ {f g : (Fin D → ℂ) → ℝ}, ContDiffAt ℝ 2 f y → ContDiffAt ℝ 2 g y →
      levi (fun v => f v + g v) y w = levi f y w + levi g y w := by
    intro f g hf hg
    simpa using levi_add_smul 1 hf hg w

  have hus : ContDiffAt ℝ 2 (u ∘ s) y :=
    ((hu k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm hYo).mem_nhds ⟨hyt, hyYo⟩)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hths : ContDiffAt ℝ 2 (th.φ (s y) ∘ s) y := potSmoothAt A th hth (s y) k ⟨hyt, th.mem_U _⟩
  have hOms : ContDiffAt ℝ 2 (Om.φ (s y) ∘ s) y := potSmoothAt A Om hOm (s y) k ⟨hyt, Om.mem_U _⟩

  obtain ⟨W, hWo, hpW, G, hG, hGeq⟩ := hOm.2 (s y) x (s y) ⟨Om.mem_U _, hyOx⟩
  have hGa : AnalyticAt ℂ (G ∘ s) y := hG k y ⟨hyt, hpW⟩
  have hGre : ContDiffAt ℝ 2 (fun v => ((G ∘ s) v).re) y :=
    (Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars.contDiffAt (n := 2)))
  have hVo : IsOpen ((A.chart k).target ∩ s ⁻¹' (W ∩ Om.U (s y) ∩ Om.U x)) :=
    (A.chart k).isOpen_inter_preimage_symm ((hWo.inter (Om.isOpen_U _)).inter (Om.isOpen_U x))
  have hgerm : (potForm Om u).φ x ∘ s =ᶠ[𝓝 y]
      fun v => ((Om.φ (s y) ∘ s) v + (u ∘ s) v) + (-1) * ((G ∘ s) v).re := by
    filter_upwards [hVo.mem_nhds ⟨hyt, ⟨hpW, Om.mem_U _⟩, hyOx⟩] with v hv
    have := hGeq (s v) hv.2
    show Om.φ x (s v) + u (s v) = (Om.φ (s y) (s v) + u (s v)) + (-1) * (G (s v)).re
    linarith
  have hΩ : levi ((potForm Om u).φ x ∘ s) y w = levi (Om.φ (s y) ∘ s) y w + levi (u ∘ s) y w := by
    rw [levi_congr hgerm, levi_add_smul (-1) (hOms.add hus) hGre, levi_re_analytic hGa,
      hadd hOms hus]
    ring

  have h1 := hle (s y) k y ⟨hyt, ⟨trivial, th.mem_U _⟩, Om.mem_U _⟩ w
  have h2 := hnn (s y) k y ⟨hyt, hyYo, th.mem_U _, trivial⟩ w
  have hT : levi ((potForm th u).φ (s y) ∘ s) y w = levi (th.φ (s y) ∘ s) y w + levi (u ∘ s) y w :=
    hadd hths hus
  rw [hT] at h2
  rw [hΩ]
  linarith

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open GroundTheory.Heights₂.Heights.AnalyticLimit

theorem ListMono.full : ListMono.Statement :=
  ListMono.proof ListMonoRaise.proof ListMonoDens.proof LocDensContOnOpen.proof
    MIntegrableOfDensLe.proof MIntMonoOfDensLe.proof

theorem RegSection.full : RegSection.Statement :=
  RegSection.proof RegYoDense.proof RegRCont.proof
    (BdMetric.proof ChartCont.proof
      (BdTransition.proof RegYoDense.proof BdEqHolo.proof
        (BdDivides.proof (CoordDivDivisible.proof HyperplaneDivisible.proof)))
      (BdCocycle.proof RegYoDense.proof BdEqHolo.proof)
      (LogNormHolo.proof ChartCont.proof)
      (BdWeight.proof BdPartition.proof IndicatorSmooth.proof NormSqSmooth.proof))
    (BdSectionProps.proof BdEqHolo.proof)
    (BdNormCont.proof ChartCont.proof BdEqHolo.proof)
    (BdComparison.proof ChartCont.proof BddOnInner.proof)

theorem TailShift.full : TailShift.Statement := TailShift.proof

theorem LemmaETailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : LemmaETailLog.Statement :=
  LemmaETailLog.proof h TailLogOfMass.proof

theorem ListTailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : ListTailLog.Statement :=
  ListTailLog.of_lemmaE (LemmaETailLog.of_lemmaETailMass h) ListMono.full RegSection.full
    TailShift.full

end GroundTheory.Heights₂.Heights.ForSecondHalf
