module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedDegree
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdBasePtFree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLinesProj
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyIntegrableAlt

theorem quad_pos {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (y : Fin e → ℂ) :
    0 < (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re := by
  have hx : (Fin.cons 1 y : Fin (e + 1) → ℂ) ≠ 0 := fun h => by
    have := congr_fun h 0
    simp at this
  exact hM.re_dotProduct_pos hx

theorem measurable_hermChartPot {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    Measurable (hermChartPot M) := by
  have hz : Continuous fun y : Fin e → ℂ => (Fin.cons 1 y : Fin (e + 1) → ℂ) :=
    continuous_const.finCons continuous_id
  have hc : Continuous fun y : Fin e → ℂ =>
      star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) :=
    hz.star.dotProduct (continuous_const.matrix_mulVec hz)
  exact Real.measurable_log.comp (Real.continuous_sqrt.measurable.comp (Complex.measurable_re.comp hc.measurable))

theorem pot_sub_bound (hCmp : HermFormCompare.Statement) {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hM : M.PosDef) (hN : N.PosDef) :
    ∃ K : ℝ, ∀ y : Fin e → ℂ, ‖hermChartPot M y - hermChartPot N y‖ ≤ K := by
  obtain ⟨c, hc, h1⟩ := hCmp _ M N hM hN
  obtain ⟨c', hc', h2⟩ := hCmp _ N M hN hM
  refine ⟨|Real.log c| + |Real.log c'|, fun y => ?_⟩
  have hqM := quad_pos hM y
  have hqN := quad_pos hN y
  have a1 := Real.log_le_log hqM (h1 (Fin.cons 1 y))
  have a2 := Real.log_le_log hqN (h2 (Fin.cons 1 y))
  rw [Real.log_mul hc.ne' hqN.ne'] at a1
  rw [Real.log_mul hc'.ne' hqM.ne'] at a2
  simp only [hermChartPot, Real.log_sqrt hqM.le, Real.log_sqrt hqN.le, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log c), le_abs_self (Real.log c'), abs_nonneg (Real.log c),
    abs_nonneg (Real.log c')]

theorem abs_maDensity_mix_le {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (k : ℕ) (C : ℝ) (y : Fin e → ℂ)
    (hMp : (cxHessian (hermChartPot M) y).PosSemidef) (hNp : (cxHessian (hermChartPot N) y).PosSemidef)
    (hle : ((C : ℂ) • cxHessian (hermChartPot N) y - cxHessian (hermChartPot M) y).PosSemidef) :
    ‖maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y‖ ≤
      max C 1 ^ e * maDensity (fun _ : Fin e => hermChartPot N) y := by
  set HM := cxHessian (hermChartPot M) y
  set HN := cxHessian (hermChartPot N) y
  set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => if (j : ℕ) < k then HM else HN with hAdef
  have hA : (fun j : Fin e => cxHessian (if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) = A := by
    funext j
    simp only [hAdef]
    split_ifs <;> rfl
  set B : Fin e → Matrix (Fin e) (Fin e) ℂ := fun _ => ((max C 1 : ℝ) : ℂ) • HN with hBdef
  have hApsd : ∀ j, (A j).PosSemidef := fun j => by
    simp only [hAdef]
    split_ifs
    · exact hMp
    · exact hNp
  have hsm : ∀ r : ℝ, 0 ≤ r → (((r : ℝ) : ℂ) • HN).PosSemidef := fun r hr =>
    hNp.smul (Complex.zero_le_real.2 hr)
  have hAB : ∀ j, (B j - A j).PosSemidef := fun j => by
    simp only [hBdef, hAdef]
    split_ifs
    · have h : ((max C 1 : ℝ) : ℂ) • HN - HM = ((C : ℂ) • HN - HM) + (((max C 1 - C : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul]
        abel
      rw [h]
      exact hle.add (hsm _ (sub_nonneg.2 (le_max_left C 1)))
    · have h : ((max C 1 : ℝ) : ℂ) • HN - HN = (((max C 1 - 1 : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul, one_smul]
      rw [h]
      exact hsm _ (sub_nonneg.2 (le_max_right C 1))
  have hmono : (mixedDisc A).re ≤ (mixedDisc B).re := ReciprocityTheory.AnForm.A.mdisc_re_mono A B hApsd hAB
  have hnn : 0 ≤ (mixedDisc A).re := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hApsd).2
  have hB : mixedDisc B = ((max C 1 : ℝ) : ℂ) ^ e * HN.det := by
    have h := ReciprocityTheory.AnForm.A.mdisc_const (((max C 1 : ℝ) : ℂ) • HN)
    rw [det_smul, Fintype.card_fin] at h
    exact h
  have hN1 : mixedDisc (fun _ : Fin e => HN) = HN.det := ReciprocityTheory.AnForm.A.mdisc_const HN
  have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDensity
  rw [hA, hN1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_of_nonneg hnn]
  rw [hB, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmono
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (max C 1 ^ e * HN.det.re) :=
        mul_le_mul_of_nonneg_left hmono hc
    _ = _ := by ring

end ChartEnergyIntegrableAlt


open ChartEnergyIntegrableAlt in
theorem ChartEnergyIntegrable.proof (hCmp : HermFormCompare.Statement) (hHess : ChartHessCompare.Statement) :
    ChartEnergyIntegrable.Statement := by
  intro e M N hM hN k
  obtain ⟨C, hC⟩ := hHess e M N hM hN
  obtain ⟨C₀, hC₀⟩ := hHess e N N hN hN
  obtain ⟨K, hK⟩ := pot_sub_bound hCmp hM hN
  have hmix : Integrable (fun y : Fin e → ℂ =>
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) := by
    refine Integrable.mono' ((ChartDensityIntegrable.proof e N hN).const_mul (max C 1 ^ e))
      (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity _).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    exact abs_maDensity_mix_le k C y (hC y).1.posSemidef (hC₀ y).1.posSemidef (hC y).2
  exact hmix.bdd_mul ((measurable_hermChartPot M).sub (measurable_hermChartPot N)).aestronglyMeasurable
    (Eventually.of_forall hK)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace FubiniStudyLeviForm

variable {ι : Type} [Fintype ι]

theorem levi_sum_nonneg {K : Type} {z : ι → ℂ} (f : K → (ι → ℂ) → ℝ)
    (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (hl : ∀ k w, 0 ≤ ReciprocityTheory.AnForm.levi (f k) z w)
    (w : ι → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => ∑ k ∈ s, f k y) z ∧
      0 ≤ ReciprocityTheory.AnForm.levi (fun y => ∑ k ∈ s, f k y) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using contDiffAt_const, by simp [ReciprocityTheory.AnForm.levi]⟩
  | insert a s ha ih =>
    have heq : (fun y => ∑ k ∈ insert a s, f k y) =
        fun y => (fun y' => ∑ k ∈ s, f k y') y + 1 * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq]
    refine ⟨ih.1.add (contDiffAt_const.mul (hf a)), ?_⟩
    rw [ReciprocityTheory.AnForm.levi_add_smul (f := fun y' => ∑ k ∈ s, f k y') (g := f a) 1 ih.1 (hf a) w]
    have h1 := hl a w
    have h2 := ih.2
    linarith

noncomputable def blockProj {K : Type} (ι : K → Type) (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨k, i⟩

end FubiniStudyLeviForm


open FubiniStudyLeviForm in
theorem FsLineLevi.proof : FsLineLevi.Statement := by
  intro K _ ι _ z w hz
  classical
  set F : K → ((Σ k, ι k) → ℂ) → ℝ :=
    fun k y => Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩)) with hF
  have hev : (fun y => Real.log ((fsMulti ι).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, F k y := by
    have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hz k
      exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
        fun y hy => ⟨i, hy⟩
    filter_upwards [Filter.eventually_all.mpr hopen] with y hy
    have hpos : ∀ k, 0 < (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) := fun k => by
      obtain ⟨i, hi⟩ := hy k
      exact (fsMetric (ι := ι k)).pos _ fun h0 => hi (congrFun h0 i)
    simp only [fsMulti, HermLine.ofMetrics, zpow_one, hF]
    exact Real.log_prod fun k _ => (hpos k).ne'
  have hblock : ∀ k, ContDiffAt ℝ 2 (F k) z ∧ ∀ v, 0 ≤ ReciprocityTheory.AnForm.levi (F k) z v := by
    intro k
    have hk0 : (fun i => z ⟨k, i⟩) ≠ 0 := by
      obtain ⟨i, hi⟩ := hz k
      exact fun h0 => hi (congrFun h0 i)
    have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
      (HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) hk0
    have hFk : F k = (fun u => Real.log ((fsMetric (ι := ι k)).ρ u)) ∘ blockProj ι k := rfl
    refine ⟨hFk ▸ hφ.comp z ((blockProj ι k).restrictScalars ℝ).contDiff.contDiffAt, fun v => ?_⟩
    rw [hFk, ReciprocityTheory.AnForm.levi_comp v ((blockProj ι k).analyticAt z) hφ]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hk0 _
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev]
  exact (levi_sum_nonneg F (fun k => (hblock k).1) (fun k => (hblock k).2) w Finset.univ).2

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedBase {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) : Ideal (MRing (stackedBlocks T)) :=
  stackedGraph b' a ⊔ Ideal.span (Set.range fun t => C (a t) * graphFirst t)

def IsStackedExc {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (E : Ideal (MRing (stackedBlocks T))) :
    Prop :=
  E ∈ (stackedBase b' a).minimalPrimes ∧ IsRelevant E

def DualStackedExcCycle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E ∧ ¬ IsHorizontal E ∧
      ∀ t : T,
        ((divCycle (stackedGraph b' a) (C (a t) * graphFirst t) E : ℤ) =
            divCycle (stackedGraph b' a) (graphSecond t) E + 1) ∧
        ∀ W : Ideal (MRing (stackedBlocks T)), ¬ IsHorizontal W → W ≠ E →
          divCycle (stackedGraph b' a) (C (a t) * graphFirst t) W = divCycle (stackedGraph b' a) (graphSecond t) W

def DualStackedExcGeoSecond.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      (geoNum (i - 1) E (fun _ => degSecond) : ℝ) * Real.log (charOf E) =
        Real.log (F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup)

def DualStackedExcGeoFirst.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      ∀ d : Fin (i - 1) → Unit ⊕ Unit → ℤ, (∀ j, d j = degFirst ∨ d j = degSecond) → (∃ j, d j = degFirst) →
        geoNum (i - 1) E d = 0

namespace DualStackedExcExample

open DualTopSimpleSubExample

end DualStackedExcExample

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineSemipositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualLineSemipositiveAlt


open scoped MatrixOrder in
theorem exists_conjTranspose_mul_self {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : ∃ B : Matrix n n ℂ, M = Bᴴ * B := by
  have h0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
  refine ⟨CFC.sqrt M, ?_⟩
  rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self M h0]

theorem re_star_dotProduct_mulVec {n : Type} [Fintype n] (B : Matrix n n ℂ) (w : n → ℂ) :
    (star w ⬝ᵥ ((Bᴴ * B) *ᵥ w)).re = ∑ j, ‖(B *ᵥ w) j‖ ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def factor (F : HermLattice K i) (σ : K →+* ℂ) : Matrix (Fin i) (Fin i) ℂ :=
  Classical.choose (exists_conjTranspose_mul_self (F.posDef σ).posSemidef)

theorem factor_spec (F : HermLattice K i) (σ : K →+* ℂ) :
    F.metric σ = (factor F σ)ᴴ * factor F σ :=
  Classical.choose_spec (exists_conjTranspose_mul_self (F.posDef σ).posSemidef)

def coordMap {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    ((Σ _ : Unit, T) → ℂ) →ₗ[ℂ] ((K →+* ℂ) × Fin i → ℂ) :=
  (LinearMap.pi fun p : (K →+* ℂ) × Fin i => (LinearMap.proj p.2) ∘ₗ (factor F p.1).mulVecLin ∘ₗ
      (LinearMap.pi fun k => LinearMap.proj (p.1, k))) ∘ₗ (dualRecover b hb).toLinearMap ∘ₗ
    (LinearMap.pi fun t => LinearMap.proj (⟨(), t⟩ : Σ _ : Unit, T))


omit [Fintype T] [DecidableEq T] in
theorem dualLine_h_eq {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ) :
    (dualLine F b hb).h z = (fsMetric (ι := (K →+* ℂ) × Fin i)).ρ (coordMap b hb z) := by
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = ‖WithLp.toLp 2 (coordMap b hb z)‖
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [dualNormSq]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [factor_spec F σ, re_star_dotProduct_mulVec]
  rfl

end DualLineSemipositiveAlt


open DualLineSemipositiveAlt in
theorem DualLineSemipositive.proof : DualLineSemipositive.Statement := by
  intro K _ _ i F T _ _ b hb
  set τc : ((Σ _ : Unit, T) → ℂ) →L[ℂ] ((K →+* ℂ) × Fin i → ℂ) :=
    LinearMap.toContinuousLinearMap (coordMap b hb) with hτc
  have hh : ∀ z, (dualLine F b hb).h z = (fsMetric (ι := (K →+* ℂ) × Fin i)).ρ (τc z) :=
    dualLine_h_eq b hb
  have hne : ∀ z : (Σ _ : Unit, T) → ℂ, (∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) → τc z ≠ 0 := by
    intro z hz h0
    have hp := (dualLine F b hb).pos z hz
    rw [hh, h0] at hp
    simp [fsMetric] at hp
  have hfun : (dualLine F b hb).h = (fsMetric (ι := (K →+* ℂ) × Fin i)).ρ ∘ τc := funext hh
  refine ⟨?_, fun z hz w _ => ?_⟩
  · intro z hz
    rw [hfun]
    exact ((HilbertSamuel.ProjLine.isSmoothMetric_fs.contDiffAt (isOpen_ne.mem_nhds (hne z hz))).comp z
      (τc.restrictScalars ℝ).contDiff.contDiffAt).contDiffWithinAt
  · change 0 ≤ ReciprocityTheory.AnForm.levi (fun z => Real.log ((dualLine F b hb).h z)) z w
    have hlog : (fun z => Real.log ((dualLine F b hb).h z)) =
        (fun u => Real.log ((fsMetric (ι := (K →+* ℂ) × Fin i)).ρ u)) ∘ τc := by
      funext y
      simp only [Function.comp_apply, hh]
    have hz0 := hne z hz.1
    have hρ : ContDiffAt ℝ 2 (fsMetric (ι := (K →+* ℂ) × Fin i)).ρ (τc z) :=
      (HilbertSamuel.ProjLine.isSmoothMetric_fs.contDiffAt (isOpen_ne.mem_nhds hz0)).of_le
        (WithTop.coe_le_coe.2 le_top)
    have hlog₀ : ContDiffAt ℝ 2 (fun u => Real.log ((fsMetric (ι := (K →+* ℂ) × Fin i)).ρ u)) (τc z) :=
      hρ.log ((fsMetric (ι := (K →+* ℂ) × Fin i)).pos _ hz0).ne'
    rw [hlog, ReciprocityTheory.AnForm.levi_comp w (τc.analyticAt z) hlog₀]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hz0 _

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionIndexNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace SectionIndexNormAlt

variable {T : Type} {K' : Type} [Field K'] {y : (Σ _ : Unit, T) → K'}

theorem ratio_mem (p : Σ _ : Unit, T) (t : T) :
    y p / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
  Algebra.subset_adjoin ⟨p, rfl⟩

theorem mem_curveRing_iff {b : K'} :
    b ∈ curveRing y ↔ ∀ t : T, y ⟨(), t⟩ ≠ 0 → b ∈ chartRingZ y (fun _ => t) := by
  rw [mem_curveRing]
  refine ⟨fun h t ht => h (fun _ => t) (fun _ => ht), fun h c hc => ?_⟩
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  rw [hc']
  exact h (c ()) (hc ())

theorem mem_chartLat_iff [Fintype T] {z : K'} :
    z ∈ chartLat y (fun _ => 1) 1 ↔ ∀ t : T, y ⟨(), t⟩ ≠ 0 → z / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) := by
  change (∀ c : Unit → T, _ → _) ↔ _
  refine ⟨fun h t ht => ?_, fun h c hc => ?_⟩
  · have := h (fun _ => t) (fun _ => ht)
    simpa [div_eq_mul_inv] using this
  · have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
    rw [hc']
    simpa [div_eq_mul_inv] using h (c ()) (hc ())

theorem aeval_div_mem [Fintype T] {s : MRing (fun _ : Unit => T)} (hs : IsMultiHomog s (fun _ => 1))
    (t : T) : aeval y s / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [s.as_sum, map_sum, Finset.sum_div]
  refine Subalgebra.sum_mem _ fun m hm => ?_
  rw [aeval_monomial, mul_div_assoc]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
  have hsum : ∑ p, m p = 1 := by
    rw [Fintype.sum_sigma, Fintype.sum_unique]
    exact hs m hm ()
  have key : m.prod (fun p e => y p ^ e) / y ⟨(), t⟩ = ∏ p, (y p / y ⟨(), t⟩) ^ m p := by
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp only [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsum, pow_one]
  rw [key]
  exact Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _ (ratio_mem p t) _

theorem exists_mul_mem {m : Ideal (curveRing y)} (hm : m.IsPrime) {t : T}
    (ht : ∀ u, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) {z : K'}
    (hz : z ∈ chartRingZ y (fun _ => t)) : ∃ b : curveRing y, b ∉ m ∧ (b : K') * z ∈ curveRing y := by
  have h1 : (1 : curveRing y) ∉ m := fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := ht u
    exact ⟨b, hb, by convert a.2 using 1⟩
  | algebraMap r =>
    exact ⟨1, h1, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨b1, hb1, h1'⟩ := hx
    obtain ⟨b2, hb2, h2'⟩ := hz
    refine ⟨b1 * b2, fun h => (hm.mem_or_mem h).elim hb1 hb2, ?_⟩
    have e : ((b1 * b2 : curveRing y) : K') * (x + z) = b2 * (b1 * x) + b1 * (b2 * z) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem b2.2 h1') (mul_mem b1.2 h2')
  | mul x z _ _ hx hz =>
    obtain ⟨b1, hb1, h1'⟩ := hx
    obtain ⟨b2, hb2, h2'⟩ := hz
    refine ⟨b1 * b2, fun h => (hm.mem_or_mem h).elim hb1 hb2, ?_⟩
    have e : ((b1 * b2 : curveRing y) : K') * (x * z) = (b1 * x) * (b2 * z) := by
      push_cast; ring
    rw [e]
    exact mul_mem h1' h2'

theorem coe_ne_zero_of_notMem {m : Ideal (curveRing y)} {b : curveRing y} (hb : b ∉ m) : (b : K') ≠ 0 :=
  fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)

theorem genIndex_span_div [NumberField K'] [Fintype T] (hy : y ≠ 0) {x : K'} (hx : x ≠ 0) :
    genIndex (Submodule.span (𝓞 K') (Set.range fun p => y p / x)).toAddSubgroup
        (1 : Submodule (𝓞 K') K').toAddSubgroup =
      genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup *
        |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have hy' : (fun p => y p / x) ≠ 0 := by
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨p, div_ne_zero hp hx⟩
  rw [DualLineIndexAlt.genIndex_span_eq_finprod hy', DualLineIndexAlt.genIndex_span_eq_finprod hy]
  have e : ∀ w : FinitePlace K', ⨆ p, w (y p / x) = (⨆ p, w (y p)) * w x⁻¹ := by
    intro w
    simp only [div_eq_mul_inv, map_mul]
    exact (Real.iSup_mul_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [e]
  rw [finprod_mul_distrib (hasFiniteMulSupport_iSup_place hy)
    (FinitePlace.hasFiniteMulSupport (inv_ne_zero hx)), FinitePlace.prod_eq_inv_abs_norm (inv_ne_zero hx)]
  have hN : Algebra.norm ℚ x⁻¹ = (Algebra.norm ℚ x)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hx, map_one])
  rw [hN]
  push_cast
  rw [abs_inv, inv_inv]

theorem genIndex_span_pos [NumberField K'] [Fintype T] {p0 : Σ _ : Unit, T} (hp0 : y p0 ≠ 0) :
    0 < genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
      (1 : Submodule (𝓞 K') K').toAddSubgroup := by
  have hy : y ≠ 0 := fun h => hp0 (by rw [h, Pi.zero_apply])
  rw [DualLineIndexAlt.genIndex_span_eq_finprod hy,
    finprod_eq_prod _ (hasFiniteMulSupport_iSup_place hy)]
  refine Finset.prod_pos fun w _ => ?_
  exact lt_of_lt_of_le (FinitePlace.pos_iff.mpr hp0) (le_ciSup (f := fun p => w (y p)) (Finite.bddAbove_range _) p0)

end SectionIndexNormAlt


open SectionIndexNormAlt in
theorem SectionIndexNorm.proof (hC : CurveCharts.Statement) (hI : InvertibleIdealIndex.Statement) :
    SectionIndexNorm.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  obtain ⟨hfin, hrank, hloc⟩ := hC T K' y hP
  set x := aeval y s with hxdef
  have hx0 : x ≠ 0 := by
    intro h0
    apply hsP
    change s ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
    rw [← hxdef, h0, map_zero, zero_mul]
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (curveRing y)
  obtain ⟨t1, ht1, hl1⟩ := hloc m0 hm0
  let f : K' →+ K' := AddMonoidHom.mulLeft x⁻¹
  have hf : ∀ z, f z = x⁻¹ * z := fun _ => rfl
  let a : (Σ _ : Unit, T) → K' := fun p => y p / x
  have key := hI K' (curveRing y) ((chartLat y (fun _ => 1) 1).map f) (Σ _ : Unit, T) a hfin ?_ ?_ ?_ ?_
  ·
    have hB : (curveRing y).toAddSubgroup = (curveMul y x).map f := by
      rw [curveMul, AddSubgroup.map_map]
      ext z
      simp [hf, hx0]
    have hinj : Function.Injective f := fun u v h => mul_left_cancel₀ (inv_ne_zero hx0) h
    rw [hB, KLinesLineDegree.genIndex_map_of_injective f hinj, genIndex_span_div ?_ hx0,
      Real.log_mul (genIndex_span_pos (p0 := ⟨(), t1⟩) ht1).ne'
        (abs_pos.mpr (by exact_mod_cast Algebra.norm_ne_zero_iff.mpr hx0)).ne',
      hrank, ← (letI : Module.Free (blockFnField y) K' := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (blockFnField y) K')] at key
    · have hF : (0 : ℝ) < Module.finrank ℚ (blockFnField y) := Nat.cast_pos.mpr Module.finrank_pos
      apply mul_left_cancel₀ hF.ne'
      push_cast at key
      linear_combination key
    · exact fun h => ht1 (by rw [h, Pi.zero_apply])
  ·
    intro b hb z hz
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hz
    refine AddSubgroup.mem_map.mpr ⟨b * w, ?_, by rw [hf, hf]; ring⟩
    rw [mem_chartLat_iff] at hw ⊢
    intro t ht
    rw [mul_div_assoc]
    exact mul_mem (mem_curveRing_iff.mp hb t ht) (hw t ht)
  ·
    intro p
    refine AddSubgroup.mem_map.mpr ⟨y p, ?_, by rw [hf]; simp [a, div_eq_inv_mul]⟩
    exact mem_chartLat_iff.mpr fun t _ => ratio_mem p t
  ·
    rintro ⟨⟨⟩, u⟩
    obtain ⟨β, hβ, hβx⟩ := exists_mul_mem hm0.isPrime hl1 (aeval_div_mem hs t1)
    obtain ⟨c, b, hb, hbc⟩ := hl1 u
    refine ⟨(β : K') * (x / y ⟨(), t1⟩) * b, mul_mem hβx b.2, ?_, ?_⟩
    · exact mul_ne_zero (mul_ne_zero (coe_ne_zero_of_notMem hβ) (div_ne_zero hx0 ht1))
        (coe_ne_zero_of_notMem hb)
    · have e : (β : K') * (x / y ⟨(), t1⟩) * b * a ⟨(), u⟩ = β * c := by
        rw [← hbc]
        simp only [a]
        field_simp
      rw [e]
      exact mul_mem β.2 c.2
  ·
    intro m hm
    obtain ⟨t, ht, hl⟩ := hloc m hm
    refine ⟨⟨(), t⟩, fun z hz => ?_⟩
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hz
    obtain ⟨b, hb, hbw⟩ := exists_mul_mem hm.isPrime hl (mem_chartLat_iff.mp hw t ht)
    refine ⟨b, ⟨_, hbw⟩, hb, ?_⟩
    simp only [hf, a]
    field_simp

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace VerticalPointLength

theorem maximal_and_mult_eq (hCh : VertPointChart.Statement) (hMC : VertPointMultChart.Statement)
    (hSQ : SectionQuotLocal.Statement) {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K']
    {y : (Σ _ : Unit, T) → K'} {s : MRing (fun _ : Unit => T)} (hP : IsArithVar (mCoordIdeal y) 1)
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) {W : Ideal (MRing (fun _ : Unit => T))}
    (hW : W ∈ divSupp (mCoordIdeal y) s) :
    (curvePtIdeal y W).IsMaximal ∧
      multAt (mCoordIdeal y ⊔ Ideal.span {s}) W = locLen (curvePtIdeal y W) (sectionQuot y (aeval y s)) := by
  obtain ⟨t, ht⟩ := hW.2 ()
  obtain ⟨hmax, hrat, hmem⟩ := hCh T K' y s hP hs hsP W hW t ht
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨a, b, -, hb, hab⟩ := (hmem 1 s hs).mp hsW
  rw [pow_one] at hab
  refine ⟨hmax, ?_⟩
  rw [hMC T K' y s hP hs hsP W hW t ht a b hb hab,
    hSQ T K' y s hP hs hsP _ t hmax.isPrime hrat a b hb hab]

end VerticalPointLength

theorem VertPointLength.proof (hCh : VertPointChart.Statement)
    (hInj : VertPointInj.Statement) (hSurj : VertPointSurj.Statement)
    (hMC : VertPointMultChart.Statement) (hSQ : SectionQuotLocal.Statement) :
    VertPointLength.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  refine ⟨⟨fun W hW => ?_, hInj T K' y s hP hs hsP,
      fun m hm => hSurj T K' y s hP hs hsP m hm.1 hm.2⟩,
    fun W hW => (VerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW).2⟩
  obtain ⟨hmax, hmult⟩ := VerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW
  exact ⟨hmax, hmult ▸ (IndefiniteRowSideFullHecke.Inter.multAt_pos_of_mem_divSupp hW).ne'⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassFibreDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial

noncomputable section

namespace GrassmannianFibreDegree

variable (n p : ℕ) [Fact p.Prime]

theorem span_eq_ker :
    (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) =
      RingHom.ker (Bridge.GeoNum.red (ι := plBlocks 1 1 n) p) :=
  (Bridge.GeoNum.ker_red p).symm

theorem isPrime : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).IsPrime := by
  rw [span_eq_ker]
  exact RingHom.ker_isPrime _

theorem isRelevant : IsRelevant (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) := by
  intro k
  refine ⟨plAnchor 1 n, ?_⟩
  rw [span_eq_ker, RingHom.mem_ker, Bridge.GeoNum.red, map_X]
  exact X_ne_zero _

theorem divSupp_eq :
    divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) = {Ideal.span {C (p : ℤ)}} := by
  have := isPrime n p
  ext W
  simp only [divSupp, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, isRelevant n p⟩

theorem ringKrullDim_quot :
    ringKrullDim (MRing (plBlocks 1 1 n) ⧸ (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))) =
      ((n + Fintype.card (Fin 1) : ℕ) : WithBot ℕ∞) := by
  rw [span_eq_ker, ringKrullDim_eq_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective (Bridge.GeoNum.red_surjective p)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  have hc : Nat.card ((_ : Fin 1) × PlIdx 1 n) = n + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
    omega
  rw [ENat.card_eq_coe_natCard, hc, Fintype.card_fin]
  simp

def coordEquiv : (Σ _ : Unit, Fin (n + 1)) ≃ (Σ _ : Fin 1, PlIdx 1 n) :=
  Equiv.ofBijective (GrassmannianLinesProjective.coordMap n)
    ⟨(GrassmannianLinesProjective.isBlockMap n).2.1, GrassmannianLinesProjective.coordMap_surjective n⟩

theorem intNum_bot :
    NumbersDVR.intNum (ZMod p) (⊥ : Ideal (NumbersDVR.MRing (plBlocks 1 1 n) (ZMod p)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have h := FieldNumbers.Relabel.intNum_map_rename (F := ZMod p) (Equiv.ofUnique Unit (Fin 1))
    (coordEquiv n) (fun _ => Subsingleton.elim _ _)
    (⊥ : Ideal (NumbersDVR.MRing (FieldNumbers.ProjIdx n) (ZMod p)))
    (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ))
  rw [Ideal.map_bot] at h
  rw [h]
  exact FieldNumbers.intNum_projectiveSpace (ZMod p) n

theorem geoNum_span :
    geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have := isPrime n p
  have hV : IsMultiProjPrime (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) :=
    ⟨isPrime n p, ⟨{C (p : ℤ)}, fun f hf => ⟨0, by
      rw [Set.mem_singleton_iff.mp hf]
      exact Inter.Conservation.isMultiHomog_C _⟩, rfl⟩, isRelevant n p⟩
  rw [← Bridge.intNum_map_eq_geoNum p n _ hV (Ideal.mem_span_singleton_self _) (ringKrullDim_quot n p)]
  have hb : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).map
      (MvPolynomial.map (Int.castRingHom (ZMod p))) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (span_eq_ker n p).le
  rw [hb]
  exact intNum_bot n p

end GrassmannianFibreDegree


open GrassmannianFibreDegree in
theorem GrassFibreDegree.proof : GrassFibreDegree.Statement := by
  intro n p hp
  have : Fact p.Prime := ⟨hp⟩
  have := isPrime n p
  have hW : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) ∈
      divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) := by
    rw [divSupp_eq]
    rfl
  have hg : geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun j => ((fun _ : Fin n => fsMulti (plBlocks 1 1 n)) j).a) = 1 :=
    geoNum_span n p
  rw [GrassmannianLinesProjective.grassIdeal_eq_bot]
  unfold vertR
  rw [divSupp_eq, finsum_mem_singleton, if_neg (Inter.Conservation.not_horizontal hp hW),
    Inter.Conservation.charOf_eq hp hW, bot_sup_eq, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self, hg]
  simp

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointDegCPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField

noncomputable section

namespace PointDegreeComplexPositive

theorem card_algHom_pos {K' : Type} [Field K'] [NumberField K'] (E : IntermediateField ℚ K') :
    0 < Nat.card (E →ₐ[ℚ] ℂ) := by
  have : FiniteDimensional ℚ E := inferInstance
  have : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  have : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  exact Nat.card_pos

end PointDegreeComplexPositive

theorem PointDegCPos.proof : PointDegCPos.Statement := by
  intro T _ K' _ _ y hP
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP]
  exact PointDegreeComplexPositive.card_algHom_pos _

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointVertR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace PointVertRAux

theorem degC_eq_finrank {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K']
    {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) :
    degC (mCoordIdeal y) = Module.finrank ℚ (blockFnField y) := by
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP, Nat.card_eq_fintype_card,
    AlgHom.card]

end PointVertRAux

theorem PointVertR.proof (hI : VertRIndex.Statement) (hN : SectionIndexNorm.Statement) :
    PointVertR.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  rw [hI T K' y s hP hs hsP, PointVertRAux.degC_eq_finrank hP,
    ← (letI : Module.Free (blockFnField y) K' := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (blockFnField y) K'), Nat.cast_mul, mul_assoc,
    hN T K' y s hP hs hsP]

end

end GroundTheory.Heights₂.Heights
end
