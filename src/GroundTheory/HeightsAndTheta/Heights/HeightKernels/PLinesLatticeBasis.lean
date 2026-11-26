module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShellSum
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsConjInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LinesLatticeBasis.proof (V : Type) [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (ι : Type) [Fintype ι]
    (hcard : Fintype.card ι = Module.finrank ℚ V) (M : Submodule ℤ V)
    (hM : Submodule.IsFullLattice ℚ M) :
    ∃ b : Module.Basis ι ℚ V, M = Submodule.span ℤ (Set.range b) := by
  have : Module.Free ℤ M := Submodule.IsLattice.free ℚ M
  have : Module.Finite ℤ M := Submodule.IsLattice.finite ℚ M
  let b0 := Module.finBasis ℤ M
  let B := b0.extendOfIsFullLattice ℚ
  have hc : Fintype.card (Fin (Module.finrank ℤ M)) = Fintype.card ι := by
    rw [hcard, Module.finrank_eq_card_basis B]
  let e := Fintype.equivOfCardEq hc
  refine ⟨B.reindex e, ?_⟩
  rw [Module.Basis.range_reindex]
  have hB : Set.range B = M.subtype '' Set.range b0 := by
    rw [← Set.range_comp']
    exact congrArg Set.range (funext (b0.extendOfIsFullLattice_apply ℚ))
  rw [hB, ← Submodule.map_span, b0.span_eq, Submodule.map_top, Submodule.range_subtype]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped nonZeroDivisors

noncomputable section

namespace KLinesLineDegree

variable {K : Type} [Field K] {n : ℕ}

theorem genIndex_map_of_injective {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    (hf : Function.Injective f) (A B : AddSubgroup G) :
    genIndex (A.map f) (B.map f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf]

end KLinesLineDegree


end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexTrans

theorem toAddSubgroup_span {V : Type} [AddCommGroup V] (s : Set V) :
    (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s :=
  Submodule.span_int_eq_addSubgroupClosure s

end KLinesGenIndexTrans


open KLinesGenIndexTrans in
theorem LinesGenIndexTrans.proof (h1 : LinesLatticeBasis.Statement)
    (h2 : LinesGenIndexDet.Statement) : LinesGenIndexTrans.Statement := by
  intro V _ _ _ A B C hA hB hC
  classical
  obtain ⟨bA, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) A hA
  obtain ⟨bB, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) B hB
  obtain ⟨bC, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) C hC
  have hAB := h2 V _ bA bB _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  have hBC := h2 V _ bB bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  have hAC := h2 V _ bA bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  refine ⟨?_, ?_⟩
  · rw [hAB]
    have h0 : (bA.det bB : ℚ) ≠ 0 := (bA.isUnit_det bB).ne_zero
    positivity
  · rw [hAB, hBC, hAC, ← abs_mul, ← Rat.cast_mul, Module.Basis.det_mul_det]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexDet

theorem span_basis_isLattice {V : Type} [AddCommGroup V] [Module ℚ V] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ V) : Submodule.IsFullLattice ℚ (Submodule.span ℤ (Set.range b)) := by
  have : Submodule.IsLattice ℚ (Submodule.span ℤ (Set.range b)) :=
    Submodule.IsLattice.of_fg ℚ (Submodule.fg_span (Set.finite_range b))
  refine { span_eq_top := ?_ }
  rw [Submodule.span_span_of_tower ℤ, b.span_eq]

end KLinesGenIndexDet


open KLinesGenIndexDet in
theorem LinesGenIndexDet.proof (h1 : LinesLatticeBasis.Statement) : LinesGenIndexDet.Statement := by
  intro V _ _ _ ι _ _ bA bB A B hA hB
  set MA := Submodule.span ℤ (Set.range bA)
  set MB := Submodule.span ℤ (Set.range bB)
  have : Submodule.IsFullLattice ℚ MA := span_basis_isLattice bA
  have : Submodule.IsFullLattice ℚ MB := span_basis_isLattice bB
  obtain ⟨bE, hE⟩ := h1 V ι (Module.finrank_eq_card_basis bA).symm (MA ⊓ MB)
    (Submodule.IsFullLattice.inf ℚ MA MB)
  have hAB : A ⊓ B = AddSubgroup.closure (Set.range bE) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, ← hE, hA, hB,
      ← Submodule.span_int_eq_addSubgroupClosure, ← Submodule.span_int_eq_addSubgroupClosure]
    rfl
  have hBA : B ⊓ A = AddSubgroup.closure (Set.range bE) := by rw [inf_comm, hAB]
  have e1 : ((B.relIndex A : ℕ) : ℚ) = |bA.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bA hBA hA
  have e2 : ((A.relIndex B : ℕ) : ℚ) = |bB.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bB hAB hB
  have hne : bB.det bE ≠ 0 := (bB.isUnit_det bE).ne_zero
  have key : (B.relIndex A : ℚ) / (A.relIndex B : ℚ) = |bA.det bB| := by
    rw [e1, e2, ← bA.det_mul_det bB bE, abs_mul, mul_div_assoc, div_self (abs_ne_zero.mpr hne),
      mul_one]
  unfold genIndex
  have := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at this
  exact this

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesIsLattice

theorem smul_mem_span_of_mem {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K} (hv : v ∈ M) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  rw [← (integralBasis K).sum_repr t, Finset.sum_smul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_assoc, integralBasis_apply, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (M.smul_mem _ hv))

theorem smul_mem_span {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K}
    (hv : v ∈ Submodule.span ℚ (M : Set (ι → K))) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact smul_mem_span_of_mem M t hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ q hx

def qSpan {K : Type} [Field K] [NumberField K] {ι : Type} (M : Submodule (𝓞 K) (ι → K)) :
    Submodule K (ι → K) where
  carrier := Submodule.span ℚ (M : Set (ι → K))
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  smul_mem' t _ hv := smul_mem_span M t hv

end KLinesIsLattice

theorem LinesIsLattice.proof : LinesIsLattice.Statement := by
  intro K _ _ ι _ M hfg hspan
  letI : Submodule.IsLattice ℚ (M.restrictScalars ℤ) := Submodule.IsLattice.of_fg ℚ hfg
  have htop : Submodule.span ℚ (M : Set (ι → K)) = ⊤ := by
    have hMN : Submodule.span K (M : Set (ι → K)) ≤ KLinesIsLattice.qSpan M :=
      Submodule.span_le.mpr fun v hv => Submodule.subset_span hv
    rw [hspan, top_le_iff] at hMN
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ KLinesIsLattice.qSpan M := hMN ▸ Submodule.mem_top
    exact hv
  letI : Submodule.IsFullLattice ℚ (M.restrictScalars ℤ) := ⟨htop⟩
  exact inferInstance
end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesIdealLatticeFG

theorem idealLattice_eq_iSup (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice a = ⨆ x, Submodule.map (LinearMap.single (𝓞 K) (fun _ : Fin n => K) x)
      (a x : Submodule (𝓞 K) K) :=
  (Submodule.iSup_map_single).symm

theorem fg (K : Type) [Field K] [NumberField K] {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).FG := by
  rw [idealLattice_eq_iSup]
  exact Submodule.fg_iSup _ fun x =>
    ((a x).fg_of_isNoetherianRing le_rfl).map _

theorem single_mem_span (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) (hx : a x ≠ 0) :
    (Pi.single x 1 : Fin n → K) ∈ Submodule.span K (idealLattice a : Set (Fin n → K)) := by
  have hbot : (a x : Submodule (𝓞 K) K) ≠ ⊥ := by
    rwa [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hmem : (Pi.single x y : Fin n → K) ∈ idealLattice a := by
    rw [idealLattice, Submodule.mem_pi]
    intro i _
    by_cases h : i = x
    · subst h; simpa using hy
    · simp [h]
  have heq : (Pi.single x 1 : Fin n → K) = y⁻¹ • (Pi.single x y : Fin n → K) := by
    ext i
    by_cases h : i = x
    · subst h; simp [hy0]
    · simp [h]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end KLinesIdealLatticeFG


open KLinesIdealLatticeFG in
theorem LinesIdealLatticeFG.proof : LinesIdealLatticeFG.Statement := by
  intro K _ _ n a ha
  refine ⟨fg K a, ?_⟩
  refine eq_top_iff.mpr ?_
  rw [← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [Pi.basisFun_apply]
  exact single_mem_span K a x (ha x)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySwap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace ChartEnergySwapHessian

open ChartMongeAmpereAffineInvariance

variable {e : ℕ}

def chartInv (y : Fin (e + 1) → ℂ) : Fin (e + 1) → ℂ := fun j => (y 0)⁻¹ * (if j = 0 then 1 else y j)

theorem chartInv_zero (y : Fin (e + 1) → ℂ) : chartInv y 0 = (y 0)⁻¹ := by
  simp [chartInv]

theorem chartInv_chartInv {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : chartInv (chartInv y) = y := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simp [chartInv]
  · simp only [chartInv, hj, if_false, if_true]
    field_simp

theorem swap_mulVec_cons (y : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) :
    swapFirstTwo e *ᵥ (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ) =
      y 0 • (Fin.cons 1 (chartInv y) : Fin (e + 1 + 1) → ℂ) := by
  funext p
  rw [swapFirstTwo, PEquiv.toMatrix_toPEquiv_mulVec]
  refine Fin.cases ?_ (fun i => ?_) p
  · simp
  · refine Fin.cases ?_ (fun k => ?_) i
    · simp [chartInv, hy]
    · have h0 : (k.succ.succ : Fin (e + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (k.succ.succ : Fin (e + 1 + 1)) ≠ 1 := by
        rw [← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]
        exact Fin.succ_ne_zero _
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.cons_succ, Pi.smul_apply,
        smul_eq_mul, chartInv, Fin.succ_ne_zero, if_false]
      field_simp

theorem hermChartPot_swap (M : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hM : M.PosDef)
    (y : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) :
    hermChartPot ((swapFirstTwo e)ᴴ * M * swapFirstTwo e) y = hermChartPot M (chartInv y) + Real.log ‖y 0‖ := by
  set u : Fin (e + 1 + 1) → ℂ := Fin.cons 1 (chartInv y) with hu
  have hTv := swap_mulVec_cons y hy
  have hq : star (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ) ⬝ᵥ
      (((swapFirstTwo e)ᴴ * M * swapFirstTwo e) *ᵥ (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ)) =
      (Complex.normSq (y 0) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hTv, star_smul, mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply]
    ring
  have hu0 : u ≠ 0 := fun h => by
    have := congrFun h 0
    simp [u] at this
  have hx : 0 < (star u ⬝ᵥ (M *ᵥ u)).re := (Complex.pos_iff.mp (hM.dotProduct_mulVec_pos hu0)).1
  simp only [hermChartPot]
  rw [hq, Complex.re_ofReal_mul, Real.sqrt_mul (Complex.normSq_nonneg (y 0)), ← Complex.norm_def,
    Real.log_mul (norm_ne_zero_iff.mpr hy) (Real.sqrt_pos.mpr hx).ne']
  ring

theorem contDiff_gbPot {D : ℕ} : ContDiff ℝ 2 (gbPot (D := D)) := by
  have hs : ContDiff ℝ 2 fun y : Fin D → ℂ => 1 + ∑ i, ‖y i‖ ^ 2 :=
    contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) i))
  have hpos : ∀ y : Fin D → ℂ, 0 < 1 + ∑ i, ‖y i‖ ^ 2 := fun y => by positivity
  exact (hs.sqrt fun y => (hpos y).ne').log fun y => (Real.sqrt_pos.mpr (hpos y)).ne'

theorem contDiff_hermChartPot (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ContDiff ℝ 2 (hermChartPot M) := by
  obtain ⟨c, P, κ, hP, hEq⟩ := ChartDensityIntegrableAlt.hermChartPot_eq_gbPot_affine M hM
  rw [hEq]
  exact (contDiff_gbPot.comp (contDiff_const.add (realCLE P hP).contDiff)).add contDiff_const

theorem contDiffAt_chartInv {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : ContDiffAt ℂ 2 chartInv y := by
  have h0 : ContDiffAt ℂ 2 (fun y : Fin (e + 1) → ℂ => (y 0)⁻¹) y :=
    (contDiff_apply ℂ (fun _ => ℂ) (0 : Fin (e + 1))).contDiffAt.inv hy
  refine contDiffAt_pi.2 fun j => ?_
  by_cases hj : j = 0
  · subst hj
    simpa [chartInv] using h0
  · simpa [chartInv, hj] using h0.mul (contDiff_apply ℂ (fun _ => ℂ) j).contDiffAt

def logCoord (y : Fin (e + 1) → ℂ) (y' : Fin (e + 1) → ℂ) : ℂ :=
  Complex.log (y' 0 / y 0) + (Real.log ‖y 0‖ : ℂ)

theorem logCoord_re (y y' : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) (hy' : y' 0 ≠ 0) :
    (logCoord y y').re = Real.log ‖y' 0‖ := by
  rw [logCoord, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hy') (norm_ne_zero_iff.mpr hy)]
  ring

theorem contDiffAt_logCoord {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : ContDiffAt ℂ 2 (logCoord y) y := by
  have hmem : y 0 / y 0 ∈ Complex.slitPlane := by
    rw [div_self hy]
    exact Complex.one_mem_slitPlane
  exact ((Complex.contDiffAt_log hmem).comp y
    ((contDiff_apply ℂ (fun _ => ℂ) (0 : Fin (e + 1))).contDiffAt.div_const (y 0))).add contDiffAt_const

end ChartEnergySwapHessian


open ChartEnergySwapHessian ChartMongeAmpereAffineInvariance in
theorem ChartEnergySwapInvariant.proof : ChartEnergySwapInvariant.Statement := by
  intro e M N hM hN k
  set S := swapFirstTwo e with hS
  set U : Set (Fin (e + 1) → ℂ) := {y | y 0 ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun (continuous_apply 0) continuous_const
  have hUm : MeasurableSet U := hUo.measurableSet
  have hae : ∀ᵐ y ∂(volume : Measure (Fin (e + 1) → ℂ)), y ∈ U := by
    set K : Submodule ℝ (Fin (e + 1) → ℂ) :=
      LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (e + 1) => ℂ) 0) with hK
    have hKtop : K ≠ ⊤ := fun h => by
      have hm : (Pi.single 0 1 : Fin (e + 1) → ℂ) ∈ K := h ▸ Submodule.mem_top
      simp [hK] at hm
    have h0 := Measure.addHaar_submodule (volume : Measure (Fin (e + 1) → ℂ)) K hKtop
    rw [ae_iff]
    convert h0 using 2
    ext y
    simp [hK, hU]
  set Φ : Fin (e + 1) → (Fin (e + 1) → ℂ) → ℝ :=
    fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ
  set f : (Fin (e + 1) → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf
  have hpt : ∀ y ∈ U, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
      maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
        else hermChartPot (Sᴴ * N * S)) y = |(fderiv ℝ chartInv y).det| • f (chartInv y) := by
    intro y hy
    have hy : y 0 ≠ 0 := hy
    have hev : ∀ᶠ y' in 𝓝 y, y' 0 ≠ 0 := (continuous_apply 0).continuousAt.eventually_ne hy
    have hΦ' : ∀ j : Fin (e + 1), (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
        else hermChartPot (Sᴴ * N * S)) j =ᶠ[𝓝 y] fun y' => Φ j (chartInv y') + (logCoord y y').re := by
      intro j
      filter_upwards [hev] with y' hy'
      rw [logCoord_re y y' hy hy']
      by_cases hj : (j : ℕ) < k
      · simp only [hΦ, hj, if_true]
        exact hermChartPot_swap M hM y' hy'
      · simp only [hΦ, hj, if_false]
        exact hermChartPot_swap N hN y' hy'
    have hΦs : ∀ j, ContDiffAt ℝ 2 (Φ j) (chartInv y) := fun j => by
      by_cases hj : (j : ℕ) < k
      · simp only [hΦ, hj, if_true]
        exact (contDiff_hermChartPot M hM).contDiffAt
      · simp only [hΦ, hj, if_false]
        exact (contDiff_hermChartPot N hN).contDiffAt
    rw [maDensity_comp_holo _ Φ chartInv (logCoord y) y hΦs (contDiffAt_chartInv hy)
      (contDiffAt_logCoord hy) hΦ', det_fderiv_real ((contDiffAt_chartInv hy).differentiableAt (by norm_num)),
      abs_of_nonneg (Complex.normSq_nonneg _), hermChartPot_swap M hM y hy, hermChartPot_swap N hN y hy, hf,
      smul_eq_mul]
    ring
  have hinj : Set.InjOn chartInv U := fun a ha b hb hab => by
    rw [← chartInv_chartInv (show a 0 ≠ 0 from ha), hab, chartInv_chartInv (show b 0 ≠ 0 from hb)]
  have himage : chartInv '' U = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show chartInv x 0 ≠ 0
      rw [chartInv_zero]
      exact inv_ne_zero hx
    · intro hy
      refine ⟨chartInv y, ?_, chartInv_chartInv hy⟩
      show chartInv y 0 ≠ 0
      rw [chartInv_zero]
      exact inv_ne_zero hy
  have hderiv : ∀ y ∈ U, HasFDerivWithinAt chartInv (fderiv ℝ chartInv y) U y := fun y hy =>
    (((contDiffAt_chartInv (show y 0 ≠ 0 from hy)).restrict_scalars ℝ).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  unfold chartMixedEnergy
  calc ∫ y, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
        maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
          else hermChartPot (Sᴴ * N * S)) y
      = ∫ y in U, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
        maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
          else hermChartPot (Sᴴ * N * S)) y := by
        rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ = ∫ y in U, |(fderiv ℝ chartInv y).det| • f (chartInv y) := setIntegral_congr_fun hUm hpt
    _ = ∫ y in chartInv '' U, f y :=
        (integral_image_eq_integral_abs_det_fderiv_smul volume hUm hderiv hinj f).symm
    _ = ∫ y in U, f y := by rw [himage]
    _ = ∫ y, f y := by rw [Measure.restrict_eq_self_of_ae_mem hae]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassGeomDegChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Matrix

noncomputable section

namespace GrassmannianGeometricDegreeChart

variable {n : ℕ}

def single1 (c : Fin (1 + n)) : PlIdx 1 n := ⟨{c}, Finset.card_singleton c⟩

theorem eq_single1 (I : PlIdx 1 n) : I = single1 (I.1.orderEmbOfFin I.2 0) := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp I.2
  have h2 : ∀ x ∈ I.1, x = c := fun x hx => by rw [hc] at hx; exact Finset.mem_singleton.mp hx
  apply Subtype.ext
  rw [h2 _ (Finset.orderEmbOfFin_mem I.1 I.2 0)]
  exact hc

theorem fin_one_fun_eq_const {α : Type*} (i : Fin 1 → α) : (fun _ => i 0) = i :=
  funext fun k => congrArg i (Subsingleton.elim 0 k)

def a0 : Σ _ : Fin 1, PlIdx 1 n := ⟨0, single1 (Fin.castAdd n 0)⟩

def chartPt (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) : Fin 1 → Matrix (Fin 1) (Fin n) ℂ :=
  fun _ _ b => z ⟨0, single1 (Fin.natAdd 1 b)⟩ / z a0

theorem rootCoord_mul (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (ht : z a0 ≠ 0) :
    (fun p => rootCoord (chartPt z) p * z a0) = z := by
  funext p
  obtain ⟨k, I⟩ := p
  obtain rfl : k = 0 := Subsingleton.elim _ _
  conv_rhs => rw [eq_single1 I]
  simp only [rootCoord, colsOf, onePipe, Matrix.det_unique, Matrix.submatrix_apply, Matrix.of_apply, id]
  generalize I.1.orderEmbOfFin I.2 0 = c
  refine Fin.addCases (fun a => ?_) (fun b => ?_) c
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    simp only [Fin.append_left]
    rw [show (default : Fin 1) = 0 from rfl, Matrix.one_apply_eq, one_mul]
    rfl
  · simp only [Fin.append_right, chartPt]
    exact div_mul_cancel₀ _ ht

theorem eval_eq_zero {g : MRing (plBlocks 1 1 n)} (hg : g ∈ grassIdeal 1 1 n) (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) :
    MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
  have key : ∀ z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ, z a0 ≠ 0 →
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
    intro z hz
    have h0 : mConeMap (rootCoord (chartPt z)) g = 0 := GrassLeRoot.proof 1 1 n _ hg
    have h1 := congrArg ((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ) h0
    rw [map_zero, mConeMap] at h1
    rw [show ((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ)
        ((MvPolynomial.aeval fun p => MvPolynomial.C (rootCoord (chartPt z) p) * MvPolynomial.X p.1) g) =
        (((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ).comp
          (MvPolynomial.aeval fun p => MvPolynomial.C (rootCoord (chartPt z) p) * MvPolynomial.X p.1)) g from rfl,
      MvPolynomial.comp_aeval] at h1
    simp only [AlgHom.restrictScalars_apply, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply] at h1
    rw [rootCoord_mul z hz] at h1
    rw [MvPolynomial.eval_map, ← h1, MvPolynomial.aeval_def]
    rfl
  have hq : MvPolynomial.map (Int.castRingHom ℂ) g * MvPolynomial.X a0 = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_mul, MvPolynomial.eval_X, map_zero]
    by_cases hz : z a0 = 0
    · rw [hz, mul_zero]
    · rw [key z hz, zero_mul]
  rcases mul_eq_zero.mp hq with h | h
  · rw [h, map_zero]
  · exact absurd h (MvPolynomial.X_ne_zero a0)

theorem mem_mcPts (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) :
    z ∈ mcPts (grassIdeal 1 1 n) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ hf => eval_eq_zero hf z⟩⟩

theorem segre_eq (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (i : Fin 1 → PlIdx 1 n) :
    segre (ι := plBlocks 1 1 n) z i = z ⟨0, i 0⟩ := by
  simp [segre]

theorem apply_eq_segre (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (p : Σ _ : Fin 1, PlIdx 1 n) :
    z p = segre (ι := plBlocks 1 1 n) z (fun _ => p.2) := by
  obtain ⟨k, I⟩ := p
  obtain rfl : k = 0 := Subsingleton.elim _ _
  rw [segre_eq]

def blockLift (x : PlIdx 1 n → ℂ) : (Σ _ : Fin 1, PlIdx 1 n) → ℂ := fun p => x p.2

theorem segre_blockLift (x : PlIdx 1 n → ℂ) :
    segre (ι := plBlocks 1 1 n) (blockLift x) = fun i => x (i 0) := by
  funext i
  rw [segre_eq]
  rfl

theorem card_seg : Fintype.card (Fin 1 → PlIdx 1 n) = n + 1 := by
  simp [PlIdx, Fintype.card_subtype, Finset.card_powersetCard, add_comm]

theorem exists_of_ne_zero {w : (Fin 1 → PlIdx 1 n) → ℂ} (hw : w ≠ 0) :
    blockLift (fun I => w fun _ => I) ∈ mcPts (grassIdeal 1 1 n) ∧
      segre (ι := plBlocks 1 1 n) (blockLift fun I => w fun _ => I) = w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine ⟨(mem_mcPts _).2 fun _ => ⟨i 0, ?_⟩, ?_⟩
  · simpa [blockLift, fin_one_fun_eq_const] using hi
  · rw [segre_blockLift]
    funext i'
    simp only [fin_one_fun_eq_const]

theorem injective_of_good {Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hΨ : IsGoodProj (grassIdeal 1 1 n) Ψ) : Function.Injective Ψ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  by_contra hne
  obtain ⟨hm, hs⟩ := exists_of_ne_zero hne
  exact hΨ _ hm (by rw [hs]; exact hw)

theorem exists_good (n : ℕ) :
    ∃ Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj (grassIdeal 1 1 n) Ψ := by
  let Ψ0 := LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq (card_seg (n := n))).symm
  refine ⟨Ψ0.toLinearMap, fun z hz h0 => ?_⟩
  obtain ⟨i, hi⟩ := hz.1 0
  have hs : segre (ι := plBlocks 1 1 n) z = 0 := Ψ0.map_eq_zero_iff.mp h0
  exact hi (by rw [apply_eq_segre z ⟨0, i⟩, hs]; rfl)

theorem ptsIntegralAt_eq {Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hΨ : IsGoodProj (grassIdeal 1 1 n) Ψ) :
    ∃ B : Matrix (PlIdx 1 n) (Fin (n + 1)) ℂ, Function.Bijective B.mulVec ∧
      ptsIntegralAt (grassIdeal 1 1 n) Ψ (fun _ z => Real.log ((fsMulti (plBlocks 1 1 n)).h z)) (fun _ => 1) =
        chartMass (Bᴴ * B) := by
  have hinj := injective_of_good hΨ
  have hrank : Module.finrank ℂ ((Fin 1 → PlIdx 1 n) → ℂ) = Module.finrank ℂ (Fin (n + 1) → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, card_seg, Fintype.card_fin]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  set L := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm with hL
  have hΨL : ∀ v, Ψ (L v) = v := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).apply_symm_apply
  have hLΨ : ∀ w, L (Ψ w) = w := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm_apply_apply
  set M := L.trans (LinearEquiv.funCongrLeft ℂ ℂ (Equiv.funUnique (Fin 1) (PlIdx 1 n))).symm with hM
  set B := LinearMap.toMatrix' M.toLinearMap with hB
  have hmv : ∀ v, B *ᵥ v = M v := fun v => LinearMap.toMatrix'_mulVec _ _
  have hMapp : ∀ v I, M v I = L v fun _ => I := fun v I => rfl
  refine ⟨B, ?_, ?_⟩
  · convert M.bijective using 1
    funext v
    exact hmv v
  have hseg : ∀ v, segre (ι := plBlocks 1 1 n) (blockLift (M v)) = L v := by
    intro v
    rw [segre_blockLift]
    funext i
    rw [hMapp, fin_one_fun_eq_const]
  have hMdiff : Differentiable ℂ fun v => M v := (LinearMap.toContinuousLinearMap M.toLinearMap).differentiable
  have hcons : Differentiable ℂ fun y' : Fin n → ℂ => (Fin.cons 1 y' : Fin (n + 1) → ℂ) := by
    rw [differentiable_pi]
    intro c
    refine Fin.cases ?_ (fun i => ?_) c
    · simp only [Fin.cons_zero]
      exact differentiable_const _
    · simp only [Fin.cons_succ]
      exact differentiable_apply i
  set γ0 : (Fin n → ℂ) → (Σ _ : Fin 1, PlIdx 1 n) → ℂ := fun y' => blockLift (M (Fin.cons 1 y')) with hγ0
  have hγ0d : ∀ y', DifferentiableAt ℂ γ0 y' := by
    intro y'
    rw [differentiableAt_pi]
    intro p
    exact ((differentiable_apply p.2).comp (hMdiff.comp hcons)) y'
  have hγ0mem : ∀ y', γ0 y' ∈ mcPts (grassIdeal 1 1 n) := by
    intro y'
    have hv : (Fin.cons 1 y' : Fin (n + 1) → ℂ) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
    obtain ⟨I, hI⟩ := Function.ne_iff.mp ((M.map_ne_zero_iff).mpr hv)
    exact (mem_mcPts _).2 fun _ => ⟨I, hI⟩
  have hpot : ∀ y', Real.log ((fsMulti (plBlocks 1 1 n)).h (γ0 y')) = hermChartPot (Bᴴ * B) y' := by
    intro y'
    set v : Fin (n + 1) → ℂ := Fin.cons 1 y'
    have h1 : (fsMulti (plBlocks 1 1 n)).h (γ0 y') = ‖WithLp.toLp 2 (B *ᵥ v)‖ := by
      rw [hmv]
      simp [fsMulti, HermLine.ofMetrics, fsMetric, hγ0, blockLift, v]
    have h2 : (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re = ∑ I, ‖(B *ᵥ v) I‖ ^ 2 := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp [dotProduct, Complex.re_sum, Complex.conj_mul']
      norm_cast
    rw [hermChartPot, h1, h2, EuclideanSpace.norm_eq]
  unfold ptsIntegralAt chartMass
  congr 1
  funext y
  have hfib : ReciprocityTheory.ChartRestriction.G.Geo.fibre (grassIdeal 1 1 n) Ψ y = {L (Fin.cons 1 y)} := by
    ext w
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.fibre, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, -, -, hw⟩
      rw [← hw, hLΨ]
    · rintro rfl
      exact ⟨γ0 y, hγ0mem y, hseg _, hΨL _⟩
  have hsheet : IsSheet (grassIdeal 1 1 n) Ψ y (L (Fin.cons 1 y)) γ0 :=
    ⟨hseg _, Eventually.of_forall fun y' => ⟨hγ0d y', hγ0mem y', by rw [hseg, hΨL]⟩⟩
  rw [hfib, finsum_mem_singleton]
  unfold sheetDensity
  split_ifs with hγ
  · have hev : (fun y' => Real.log ((fsMulti (plBlocks 1 1 n)).h (hγ.choose y'))) =ᶠ[𝓝 y]
        hermChartPot (Bᴴ * B) := by
      filter_upwards [hγ.choose_spec.2] with y' hy'
      have hs : segre (ι := plBlocks 1 1 n) (hγ.choose y') = segre (ι := plBlocks 1 1 n) (γ0 y') := by
        rw [hseg, ← hy'.2.2, hLΨ]
      have he : hγ.choose y' = γ0 y' := by
        funext p
        rw [apply_eq_segre (hγ.choose y') p, apply_eq_segre (γ0 y') p, hs]
      rw [he, hpot]
    simp only [one_mul, maDensity, cxHessian_congr hev]
  · exact absurd ⟨γ0, hsheet⟩ hγ

end GrassmannianGeometricDegreeChart


open GrassmannianGeometricDegreeChart in
theorem GrassGeomDegChart.proof : GrassGeomDegChart.Statement := by
  intro n
  have hex := exists_good n
  obtain ⟨B, hB, hval⟩ := ptsIntegralAt_eq hex.choose_spec
  refine ⟨B, hB, ?_⟩
  unfold geomDeg ptsIntegral
  rw [dite_eq_left hex]
  exact hval

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootHeightNE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

theorem anchor_homog (f j m : ℕ) : IsMultiHomog (rootAnchorSection f j m) (fun _ => 1) := by
  classical
  intro μ hμ k
  have hdeg : rootAnchorSection f j m = monomial (∑ τ : Fin f, Finsupp.single (⟨τ, plAnchor j m⟩ : Σ _ : Fin f, PlIdx j m) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]; rfl
  rw [hdeg] at hμ
  have := MvPolynomial.support_monomial_subset hμ
  rw [Finset.mem_singleton] at this
  subst this
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_comm, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single (plAnchor j m)]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  · intro τ _ hτ
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    exact hτ (congrArg Sigma.fst h)
  · simp

theorem RootHeight.proofNE (hA : RootArithVar.Statement) (hD : RootDivSuppEmpty.Statement)
    (hL : RootLogNormBound.Statement) (hF : RootPointsFinite.Statement) (hP : PtsIntegralZeroLowerNE.Statement)
    (hM : MultiHomogMemCoord.Statement) (hS : FsLineSmooth.Statement) : RootHeight.Statement := by
  intro f j m ζ hf hζ II hII
  have : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have hV := hA f j m ζ hf hζ
  have hmem : rootAnchorSection f j m ∉ rootPointIdeal ζ := by
    rw [rootPointIdeal, hM (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) _ _ (anchor_homog f j m)]
    simp [rootAnchorSection, rootCoord, anchor_minor]
  have hsm : IsSmoothHerm (fsMulti (plBlocks f j m)) := hS _ _
  have hR := (hII (Fin f) (plBlocks f j m)).2.2 (rootPointIdeal ζ) 0 Fin.elim0
    (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) (fun _ => 1) hV (fun j => j.elim0) hsm
    (fun _ => by simp [fsMulti, HermLine.ofMetrics]) (anchor_homog f j m) hmem
  have e1 : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) :
      Fin (0 + 1) → HermLine (plBlocks f j m)) = ![fsMulti (plBlocks f j m)] := by
    funext i; fin_cases i; rfl
  rw [e1] at hR
  have hlow := hP (Fin f) (plBlocks f j m) (rootPointIdeal ζ)
    (fun i z => Real.log (((Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) i).h z))
    (logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m)) (-grassConst f j m)
    hV.2.1.2.1 (hF f j m ζ hζ) ?_ (hL f j m ζ hζ)
  · have : recR (II (Fin f) (plBlocks f j m)) (rootPointIdeal ζ)
        (Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) =
        - arInt (rootPointIdeal ζ) (rootAnchorSection f j m) (fsMulti (plBlocks f j m)) Fin.elim0 := by
      simp [recR, hD f j m ζ hζ]
    rw [this] at hR
    show II _ _ _ 1 _ ≤ _
    rw [hR]
    simp only [arInt]
    have := hlow
    nlinarith
  · intro u z hu hz
    have hh := (fsMulti (plBlocks f j m)).smul u z hu
    have hpos := (fsMulti (plBlocks f j m)).pos z hz.1
    have hfa : (fsMulti (plBlocks f j m)).a = fun _ => 1 := rfl
    simp only [logNorm, hh, hfa, zpow_one]
    have hs : eval (fun p : (Σ _ : Fin f, PlIdx j m) => u p.1 * z p) (map (Int.castRingHom ℂ) (rootAnchorSection f j m))
        = (∏ k, u k) * eval z (map (Int.castRingHom ℂ) (rootAnchorSection f j m)) := by
      simp [rootAnchorSection, Finset.prod_mul_distrib]
    have hu0 : (∏ k, ‖u k‖) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (hu k)
    congr 1
    erw [hs]
    rw [norm_mul, norm_prod]
    field_simp

end

end GroundTheory.Heights₂.Heights
end
