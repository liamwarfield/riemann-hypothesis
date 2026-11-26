module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def HermLattice.withStdMetric {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) :
    HermLattice K i where
  lattice := F.lattice
  fg := F.fg
  span_eq := F.span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

def DualTopMetricChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def DualTopLatticeChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice (HermLattice.standard K i)))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) =
      II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine (HermLattice.standard K i) b' hb') -
        F.withStdMetric.degree *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def DualTopStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine (HermLattice.standard K i) b hb) =
      (Module.finrank ℚ K : ℝ) *
        II (Fin 1) (plBlocks 1 1 (i - 1)) (grassIdeal 1 1 (i - 1)) (1 * 1 * (i - 1) + 1)
          (fun _ => fsMulti (plBlocks 1 1 (i - 1)))

def DualGeomDegStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    geomDeg (dualIdeal b) (dualLine F b hb) (i - 1) =
      (Module.finrank ℚ K : ℝ) *
        geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def HermLattice.scaledExample : HermLattice ℚ 1 where
  lattice := (HermLattice.standard ℚ 1).lattice
  fg := (HermLattice.standard ℚ 1).fg
  span_eq := (HermLattice.standard ℚ 1).span_eq
  metric := fun _ => Matrix.diagonal fun _ => (4 : ℂ)
  posDef := fun _ => Matrix.PosDef.diagonal fun _ => by norm_num
  conj := fun _ => by
    ext a c
    by_cases h : a = c <;> simp [h, map_ofNat]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace DualArithmeticVariety

variable {K : Type} [Field K]

def evalForm (m : ℕ) : (Fin m → K) →ₗ[K] ProjField K m :=
  Fintype.linearCombination K fun j => algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j)

theorem algebraicIndependent_gen (m : ℕ) :
    AlgebraicIndependent K fun j : Fin m =>
      algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j) :=
  (MvPolynomial.algebraicIndependent_X (Fin m) K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin m) K) (ProjField K m))
    (IsFractionRing.injective _ _)

theorem evalForm_ne_zero {m : ℕ} {φ : Fin m → K} (hφ : φ ≠ 0) : evalForm m φ ≠ 0 := by
  intro h0
  apply hφ
  apply (algebraicIndependent_gen m).linearIndependent.fintypeLinearCombination_injective
  simpa only [evalForm, map_zero] using h0

theorem mem_of_gen_mem {m : ℕ} (E : IntermediateField K (ProjField K m))
    (h : ∀ j, algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j) ∈ E) (z : ProjField K m) :
    z ∈ E := by
  have hp : ∀ p : MvPolynomial (Fin m) K, algebraMap _ (ProjField K m) p ∈ E := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact E.algebraMap_mem c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp => rw [map_mul]; exact mul_mem hp (h j)
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin m) K) z
  exact div_mem (hp p) (hp q)

theorem isAlgebraic_of_adjoin {m : ℕ} (S : Set (ProjField K m))
    (h : ∀ z, z ∈ IntermediateField.adjoin K S) :
    Algebra.IsAlgebraic (Algebra.adjoin K S) (ProjField K m) := by
  rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
  exact ⟨fun z => isAlgebraic_algebraMap (⟨z, h z⟩ : IntermediateField.adjoin K S)⟩

theorem trdeg_eq (m : ℕ) : Cardinal.mk (Fin m) = Algebra.trdeg K (ProjField K m) :=
  ((algebraicIndependent_gen m).isTranscendenceBasis_iff_isAlgebraic.mpr
    (isAlgebraic_of_adjoin _ (mem_of_gen_mem _ fun j =>
      IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩))).cardinalMk_eq_trdeg

variable [NumberField K] {i : ℕ}

theorem span_dualLattice (F : HermLattice K i) :
    Submodule.span K (dualLattice F : Set (Fin i → K)) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨N, hN, hint⟩ := exists_integral_multiples ℤ ℚ (S.image fun g => v ⬝ᵥ g)
  have hmem : (N : K) • v ∈ dualLattice F := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      have hg' := hint _ (Finset.mem_image_of_mem _ hg)
      rw [smul_dotProduct, Int.cast_smul_eq_zsmul]
      exact RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hg')
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by rw [dotProduct_add, map_add (f := _), ha, hc]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [dotProduct_smul, map_mul, ha]
      rfl
  have hN' : (N : K) ≠ 0 := Int.cast_ne_zero.mpr hN
  have := Submodule.smul_mem (Submodule.span K (dualLattice F : Set (Fin i → K))) (N : K)⁻¹
    (Submodule.subset_span hmem)
  rwa [inv_smul_smul₀ hN'] at this

variable {F : HermLattice K i} {T : Type}

theorem span_basis [Fintype T] (b : Module.Basis T ℤ (dualLattice F)) :
    Submodule.span K (Set.range fun t => (b t : Fin i → K)) = ⊤ := by
  refine eq_top_iff.mpr ((span_dualLattice F).symm.le.trans (Submodule.span_le.mpr fun φ hφ => ?_))
  have h := congrArg Subtype.val (b.sum_repr ⟨φ, hφ⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  rw [← h]
  exact Submodule.sum_mem _ fun t _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self t)) _

theorem dualLatticeCoord_eq (b : Module.Basis T ℤ (dualLattice F)) (t : T) :
    dualLatticeCoord b ⟨(), t⟩ = evalForm i (b t : Fin i → K) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dualLatticeCoord, evalForm, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin i) K),
    MvPolynomial.algebraMap_eq]

end DualArithmeticVariety


open DualArithmeticVariety in
theorem DualArithVar.proof (h : CoordConeArithVar.Statement) : DualArithVar.Statement := by
  intro K _ _ i F T _ _ b hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K fun t => (b t : Fin (n + 1) → K)
  rw [span_basis b] at hsp
  let B : Module.Basis κ K (Fin (n + 1) → K) := Module.Basis.mk hli hsp.ge
  let e : Fin (n + 1) ≃ κ := (B.indexEquiv (Pi.basisFun K (Fin (n + 1)))).symm
  let u : Fin (n + 1) → T := a ∘ e
  let w : Fin (n + 1) → ProjField K (n + 1) := fun l => evalForm (n + 1) (b (u l) : Fin (n + 1) → K)
  let s : Fin n → ProjField K (n + 1) := fun l => w l.succ / w 0
  let v : Fin (n + 1) → ProjField K (n + 1) := Fin.cons (w 0) s
  have hy := dualLatticeCoord_eq b
  have hw0 : w 0 ≠ 0 := evalForm_ne_zero (hli.ne_zero (e 0))
  have hspw : ∀ ψ, evalForm (n + 1) ψ ∈ Submodule.span K (Set.range w) := by
    intro ψ
    have hψ : ψ ∈ Submodule.span K (Set.range (((fun t => (b t : Fin (n + 1) → K)) ∘ a) ∘ e)) := by
      rw [EquivLike.range_comp, hsp]
      exact Submodule.mem_top
    have := Submodule.mem_map_of_mem (f := evalForm (n + 1)) hψ
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  have hwE : ∀ l, w l ∈ IntermediateField.adjoin K (Set.range v) := by
    intro l
    have hv : ∀ l, v l ∈ IntermediateField.adjoin K (Set.range v) :=
      fun l => IntermediateField.subset_adjoin _ _ ⟨l, rfl⟩
    induction l using Fin.cases with
    | zero => exact hv 0
    | succ m =>
      have := mul_mem (hv m.succ) (hv 0)
      simpa [v, s, div_mul_cancel₀ _ hw0] using this
  have hall : ∀ z, z ∈ IntermediateField.adjoin K (Set.range v) := by
    refine mem_of_gen_mem _ fun j => ?_
    have hX : algebraMap (MvPolynomial (Fin (n + 1)) K) (ProjField K (n + 1)) (X j) =
        evalForm (n + 1) (Pi.single j 1) := by
      rw [evalForm, Fintype.linearCombination_apply_single, one_smul]
    rw [hX]
    exact (Submodule.span_le (p := (IntermediateField.adjoin K (Set.range v)).toSubalgebra.toSubmodule)).mpr
      (by rintro _ ⟨l, rfl⟩; exact hwE l) (hspw _)
  have hv : AlgebraicIndependent K v := by
    have := isAlgebraic_of_adjoin _ hall
    exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K v (trdeg_eq (n + 1)).le).1
  have hs : AlgebraicIndependent ℚ s :=
    (hv.comp Fin.succ (Fin.succ_injective _)).restrictScalars (algebraMap ℚ K).injective
  have hint : ∀ z ∈ Submodule.span K (Set.range w),
      IsIntegral (IntermediateField.adjoin ℚ (Set.range s)) (z / w 0) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      induction l using Fin.cases with
      | zero => rw [div_self hw0]; exact isIntegral_one
      | succ m =>
        exact isIntegral_algebraMap (x := (⟨s m, IntermediateField.subset_adjoin _ _ ⟨m, rfl⟩⟩ :
          IntermediateField.adjoin ℚ (Set.range s)))
    | zero => rw [zero_div]; exact isIntegral_zero
    | add x y _ _ hx hy => rw [add_div]; exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, mul_div_assoc]
      set_option synthInstance.maxHeartbeats 200000 in
        exact ((Algebra.IsIntegral.isIntegral (R := ℚ) c).map
          (IsScalarTower.toAlgHom ℚ K (ProjField K (n + 1)))).tower_top.mul hx
  refine h Unit (dualBlocks T) (ProjField K (n + 1)) (dualLatticeCoord b) (fun _ => u 0) n s ⟨()⟩
    (fun _ => by rw [hy]; exact hw0) hs (fun l => IntermediateField.subset_adjoin _ _ ⟨⟨(), u l.succ⟩, ?_⟩) ?_
  · show dualLatticeCoord b ⟨(), u l.succ⟩ / dualLatticeCoord b ⟨(), u 0⟩ = w l.succ / w 0
    rw [hy, hy]
  · rintro r ⟨⟨⟨⟩, t⟩, rfl⟩
    show IsAlgebraic _ (dualLatticeCoord b ⟨(), t⟩ / dualLatticeCoord b ⟨(), u 0⟩)
    rw [hy, hy]
    exact (hint _ (hspw _)).isAlgebraic

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.IsArithVarBotDualBlocksUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField

noncomputable section

def dualPointCoord {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) {K' : Type} [Field K'] [Algebra K K'] (v : Fin i → K') :
    (Σ _ : Unit, T) → K' :=
  fun p => ∑ j, algebraMap K K' ((b p.2 : Fin i → K) j) * v j

def DualCurvePoint.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (W : Ideal (MRing (dualBlocks T))),
    IsArithVar W 1 → dualIdeal b ≤ W →
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (v : Fin i → K'),
        v ≠ 0 ∧ W = mCoordIdeal (dualPointCoord b v)

def PointDegCPos.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 → 0 < degC (mCoordIdeal y)

def PointArInt.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (A : HermLine (fun _ : Unit => T)) (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsSectionOn (mCoordIdeal y) A s →
      (Module.finrank ℚ K' : ℝ) * arInt (mCoordIdeal y) s A (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) =
        (degC (mCoordIdeal y) : ℝ) * ∑ σ : K' →+* ℂ, logNorm A s (fun p => σ (y p))

def PointVertR.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      (Module.finrank ℚ K' : ℝ) * vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) s =
        (degC (mCoordIdeal y) : ℝ) * (Real.log |(Algebra.norm ℚ (aeval y s) : ℝ)| +
          Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
            (1 : Submodule (𝓞 K') K').toAddSubgroup))

def DualLineIndex.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (K' : Type) [Field K'] [NumberField K']
    [Algebra K K'] (v : Fin i → K'), v ≠ 0 →
      genIndex ((Submodule.span (𝓞 K')
          ((fun w : Fin i → K => fun j => algebraMap K K' (w j)) '' F.lattice) ⊓
          (Submodule.span K' (Set.range fun _ : Fin 1 => v)).restrictScalars (𝓞 K')).toAddSubgroup)
        (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 => v)).toAddSubgroup *
      genIndex (Submodule.span (𝓞 K') (Set.range (dualPointCoord b v))).toAddSubgroup
        (1 : Submodule (𝓞 K') K').toAddSubgroup = 1

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualProjApply
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def dualProj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin i → ℂ) :=
  ∑ σ : K →+* ℂ, (LinearMap.pi fun j : Fin i => LinearMap.proj (σ, j)) ∘ₗ
    (dualRecover b hb).toLinearMap ∘ₗ (LinearMap.pi fun t : T => LinearMap.proj fun _ : Unit => t)

omit [Fintype T] [DecidableEq T] in
theorem dualProj_apply (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (s : ((k : Unit) → dualBlocks T k) → ℂ) (j : Fin i) :
    dualProj b hb s j = ∑ σ : K →+* ℂ, dualRecover b hb (fun t => s fun _ => t) (σ, j) := by
  simp [dualProj]
  rfl

def dualPlanePt (b : Module.Basis T ℤ (dualLattice F)) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    (Σ _ : Unit, T) → ℂ :=
  fun p => ∑ j, σ ((b p.2 : Fin i → K) j) * v j

def DualPtsOnPlane.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    ∀ z ∈ mcPts (dualIdeal b), ∃ σ : K →+* ℂ, ∀ τ : K →+* ℂ, τ ≠ σ → ∀ j,
      dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j) = 0

def DualPtsOfPlane.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (_hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ),
    v ≠ 0 → dualPlanePt b σ v ∈ mcPts (dualIdeal b)

def DualStdMassAt.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (F : HermLattice K (D + 1)) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    (∀ σ, F.metric σ = 1) →
    ptsIntegralAt (e := D) (dualIdeal b) (dualProj b hb)
      (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) = Fintype.card (K →+* ℂ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEmbBijective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace DualEmbeddingBijective

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem exists_zsmul_mem_dualLattice (F : HermLattice K i) (y : Fin i → K) :
    ∃ N : ℤ, N ≠ 0 ∧ N • y ∈ dualLattice F := by
  classical
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image y ∪ S.biUnion fun g => Finset.univ.image g)
  have hint : ∀ z : K, IsIntegral ℤ z → z ∈ (algebraMap (𝓞 K) K).range :=
    fun z hz => ⟨⟨z, hz⟩, rfl⟩
  refine ⟨d * d, mul_ne_zero hd0 hd0, ?_⟩
  intro x hx
  rw [← hS] at hx
  refine Submodule.span_induction
    (p := fun x _ => ((d * d) • y) ⬝ᵥ x ∈ (algebraMap (𝓞 K) K).range) ?_ ?_ ?_ ?_ hx
  · intro g hg
    have hsum : ((d * d) • y) ⬝ᵥ g = ∑ j, (d • y j) * (d • g j) := by
      simp only [dotProduct, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum]
    refine sum_mem fun j _ => mul_mem (hint _ (hd _ ?_)) (hint _ (hd _ ?_))
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨g, Finset.mem_coe.mp hg, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
  · rw [dotProduct_zero]
    exact zero_mem _
  · intro x z _ _ hx hz
    rw [dotProduct_add]
    exact add_mem hx hz
  · intro a x _ hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨a * c, by rw [dotProduct_smul, map_mul, hc]; rfl⟩

def pairing (w : (K →+* ℂ) × Fin i → ℂ) : (Fin i → K) →+ ℂ where
  toFun φ := ∑ p, p.1 (φ p.2) * w p
  map_zero' := by simp
  map_add' φ ψ := by simp [add_mul, Finset.sum_add_distrib]

theorem pairing_single (w : (K →+* ℂ) × Fin i → ℂ) (j : Fin i) (x : K) :
    pairing w (Pi.single j x) = ∑ σ : K →+* ℂ, w (σ, j) * σ x := by
  classical
  simp only [pairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro j' _ hj'
    simp [Pi.single_eq_of_ne hj']
  · simp

theorem injective (F : HermLattice K i) {T : Type} [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice F)) :
    Function.Injective (Matrix.mulVecLin (dualEmbMatrix b)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hb : ∀ t, pairing w (b t : Fin i → K) = 0 := fun t => by
    have h := congrFun hw t
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, dualEmbMatrix, pairing] using h
  have hL : ∀ φ : dualLattice F, pairing w φ = 0 := by
    intro φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr φ, Submodule.coe_sum, map_sum]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [Submodule.coe_smul, map_zsmul, hb, smul_zero]
  have hK : ∀ y, pairing w y = 0 := by
    intro y
    obtain ⟨N, hN, hy⟩ := exists_zsmul_mem_dualLattice F y
    have h := hL ⟨_, hy⟩
    rw [Submodule.coe_mk, map_zsmul] at h
    exact (smul_eq_zero.mp h).resolve_left hN
  funext p
  obtain ⟨σ, j⟩ := p
  have hli := (linearIndependent_monoidHom K ℂ).comp (fun σ : K →+* ℂ => σ.toMonoidHom)
    (fun σ τ h => RingHom.ext fun x => DFunLike.congr_fun h x)
  rw [Fintype.linearIndependent_iff] at hli
  refine hli (fun σ => w (σ, j)) ?_ σ
  funext x
  have h := hK (Pi.single j x)
  rw [pairing_single] at h
  simpa [Finset.sum_apply] using h

theorem card_le (F : HermLattice K i) {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) :
    Fintype.card T ≤ Fintype.card ((K →+* ℂ) × Fin i) := by
  have h1 : LinearIndependent ℤ (fun t => (b t : Fin i → K)) :=
    b.linearIndependent.map' (dualLattice F).subtype (Submodule.ker_subtype _)
  have h2 : LinearIndependent ℚ (fun t => (b t : Fin i → K)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have h3 := h2.fintype_card_le_finrank
  rw [Module.finrank_pi_fintype] at h3
  rw [Fintype.card_prod, NumberField.Embeddings.card K ℂ, Fintype.card_fin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
  rw [mul_comm]
  exact h3

end DualEmbeddingBijective

theorem DualEmbBijective.proof : DualEmbBijective.Statement := by
  intro K _ _ i F T _ _ b
  have hinj := DualEmbeddingBijective.injective F b
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hcard := DualEmbeddingBijective.card_le F b
  simp only [Module.finrank_fintype_fun_eq_card] at hle
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  simp only [Module.finrank_fintype_fun_eq_card]
  omega

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeBasisExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix NumberField

noncomputable section

namespace DualLatticeBasisExistsAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem eq_zero_of_dotProduct_gens (F : HermLattice K i) (s : Finset (Fin i → K))
    (hs : Submodule.span (𝓞 K) (s : Set (Fin i → K)) = F.lattice) (φ : Fin i → K)
    (h : ∀ g ∈ s, φ ⬝ᵥ g = 0) : φ = 0 := by
  let L : (Fin i → K) →ₗ[K] K :=
    { toFun := fun x => φ ⬝ᵥ x
      map_add' := dotProduct_add φ
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have h1 : F.lattice ≤ (LinearMap.ker L).restrictScalars (𝓞 K) := by
    rw [← hs, Submodule.span_le]
    intro g hg
    exact h g hg
  have h2 : Submodule.span K (F.lattice : Set (Fin i → K)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    intro x hx
    exact h1 hx
  rw [F.span_eq, top_le_iff] at h2
  funext j
  have hj : Pi.single j (1 : K) ∈ LinearMap.ker L := by rw [h2]; trivial
  have : φ ⬝ᵥ Pi.single j (1 : K) = 0 := hj
  simpa [dotProduct_single] using this

theorem dualLattice_fg (F : HermLattice K i) : (dualLattice F).FG := by
  classical
  obtain ⟨s, hs⟩ := F.fg

  let G : (Fin i → K) →ₗ[ℤ] (s → K) :=
    { toFun := fun φ g => φ ⬝ᵥ (g : Fin i → K)
      map_add' := fun φ ψ => by funext g; simp [add_dotProduct]
      map_smul' := fun c φ => by
        funext g
        show (c • φ) ⬝ᵥ (g : Fin i → K) = c • (φ ⬝ᵥ (g : Fin i → K))
        exact smul_dotProduct c φ _ }
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    refine eq_zero_of_dotProduct_gens F s hs φ (fun g hg => ?_)
    exact congrFun hφ ⟨g, hg⟩

  let ι : (s → 𝓞 K) →ₗ[ℤ] (s → K) :=
    LinearMap.pi (fun g => ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ).comp (LinearMap.proj g))
  have hle : (dualLattice F).map G ≤ LinearMap.range ι := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hv : ∀ g : s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = φ ⬝ᵥ (g : Fin i → K) := fun g =>
      hφ g (hs ▸ Submodule.subset_span g.2)
    choose a ha using hv
    exact ⟨a, funext fun g => ha g⟩
  have hfg : ((dualLattice F).map G).FG := by
    have e : (dualLattice F).map G = (((dualLattice F).map G).comap ι).map ι := by
      rw [Submodule.map_comap_eq, inf_eq_right.mpr hle]
    rw [e]
    exact (IsNoetherian.noetherian _).map ι
  exact Submodule.fg_of_fg_map_injective G hG hfg

end DualLatticeBasisExistsAlt


open DualLatticeBasisExistsAlt in
theorem DualLatticeBasisExists.proof : DualLatticeBasisExists.Statement := by
  intro K _ _ i F
  classical
  have : Module.Finite ℤ (dualLattice F) := Module.Finite.iff_fg.mpr (dualLattice_fg F)
  exact ⟨Module.Free.ChooseBasisIndex ℤ (dualLattice F), inferInstance, inferInstance,
    ⟨Module.Free.chooseBasis ℤ (dualLattice F)⟩⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ReMulOfPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder

noncomputable section

theorem gramAt_single {K : Type*} [Field K] {k : ℕ} (h : Matrix (Fin k) (Fin k) ℂ) (σ : K →+* ℂ) :
    gramAt h σ (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = h := by
  have he : ∀ j : Fin k, embVec σ (Pi.single j 1 : Fin k → K) = Pi.single j 1 := fun j => by
    funext i
    by_cases hij : i = j
    · subst hij; simp [embVec]
    · simp [embVec, hij]
  ext a b
  simp [gramAt, he, mulVec_single, single_dotProduct]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ExistsSmulMemOfSpanEqTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights

noncomputable section

theorem genIndex_eq_div_of_le {M : Type*} [AddCommGroup M] {A B C : AddSubgroup M} (hCA : C ≤ A)
    (hCB : C ≤ B) (hC : C.relIndex B ≠ 0) :
    genIndex A B = (C.relIndex A : ℝ) / (C.relIndex B : ℝ) := by
  have h1 : C.relIndex (A ⊓ B) * B.relIndex A = C.relIndex A := by
    rw [← AddSubgroup.inf_relIndex_left A B]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hCA hCB) inf_le_left
  have h2 : C.relIndex (A ⊓ B) * A.relIndex B = C.relIndex B := by
    rw [← AddSubgroup.inf_relIndex_right A B]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hCA hCB) inf_le_right
  have h3 : (C.relIndex (A ⊓ B) : ℝ) ≠ 0 := by
    intro h
    apply hC
    rw [← h2, Nat.cast_eq_zero.mp h, zero_mul]
  unfold genIndex
  rw [← h1, ← h2]
  push_cast
  rw [mul_div_mul_left _ _ h3]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLineOfLargeDegreeDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem LineOfLargeDegreeFromZ.proofDual (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hArith : DualArithVar.Statement)
    (hSemi : DualLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : DualLineConj.Statement) (hPt : DualPointLineDegree.Statement)
    (hTop : DualTopBound.Statement) (hPos : DualGeomDegPos.Statement) :
    LineOfLargeDegreeFromZ.Statement := by
  intro hZ1 hZ2 hEx K _ _ i hi F ε hε
  obtain ⟨II, hII⟩ := hEx
  obtain ⟨T, _, _, ⟨b⟩⟩ := hBasis K i F
  have hb := hBij K i F T b
  set A := dualLine F b hb with hA
  set e : ℝ := -F.slope + 1 / 2 * Real.log i + ε with he
  by_contra hne
  push Not at hne
  have hW : ∀ W : Ideal (MRing (dualBlocks T)), IsArithVar W 1 → dualIdeal b ≤ W →
      e * degC W ≤ II Unit (dualBlocks T) W 1 ![A] := by
    intro W hW1 hPW
    obtain ⟨hdeg, K', iF, iN, iA, v, hv, hline⟩ := hPt K i F T b hb II hII W hW1 hPW
    have hlt := hne K' iF iN iA v hv
    rw [hline] at hlt
    have hd : (0 : ℝ) < degC W := by exact_mod_cast hdeg
    have h1 : e < II Unit (dualBlocks T) W 1 ![A] / degC W := by
      rw [neg_div] at hlt
      linarith
    exact ((lt_div_iff₀ hd).mp h1).le
  have hV : IsArithVar (dualIdeal b) (i - 1 + 1) := by
    rw [Nat.sub_add_cancel hi]; exact hArith K i F T b hi
  have hZ := hZ1 Unit (dualBlocks T) (dualIdeal b) ⊥ (i - 1) A e II hII hV
    bot_le (hSemi K i F T b hb) (hNef _ _ _ _ fun _ => zero_le_one) (hConj K i F T b hb) hW
  rw [Nat.sub_add_cancel hi] at hZ
  have hT := hTop hZ2 K i F T b hb II hi hII
  have hG := hPos K i F T b hb hi
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have key : (i : ℝ) * e * geomDeg (dualIdeal b) A (i - 1) ≤
      (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * geomDeg (dualIdeal b) A (i - 1) := hZ.trans hT
  have : (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) ≤ 0 := by
    rw [he] at key
    nlinarith
  have : 0 < (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) :=
    mul_pos (mul_pos hi' hε) hG
  linarith

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineConj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField NumberField.ComplexEmbedding

noncomputable section

namespace DualLineConjugation

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def conjPerm (K : Type) [Field K] : Equiv.Perm (K →+* ℂ) :=
  Function.Involutive.toPerm _ (involutive_conjugate K)


omit [Fintype T] [DecidableEq T] in
theorem conj_mulVec (b : Module.Basis T ℤ (dualLattice F)) (w : (K →+* ℂ) × Fin i → ℂ) :
    (fun t => starRingEnd ℂ ((dualEmbMatrix b *ᵥ w) t)) =
      dualEmbMatrix b *ᵥ fun p => starRingEnd ℂ (w (conjugate p.1, p.2)) := by
  funext t
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_sum, map_mul]
  refine Fintype.sum_equiv ((conjPerm K).prodCongr (Equiv.refl _)) _ _ fun p => ?_
  simp [conjPerm, dualEmbMatrix]

theorem recover_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualRecover b hb (fun t => starRingEnd ℂ (z t)) =
      fun p => starRingEnd ℂ (dualRecover b hb z (conjugate p.1, p.2)) := by
  have h1 : ∀ w, (dualRecover b hb).symm w = dualEmbMatrix b *ᵥ w := fun w => by
    simp [dualRecover]
  apply (dualRecover b hb).symm.injective
  rw [LinearEquiv.symm_apply_apply, h1, ← conj_mulVec b (dualRecover b hb z), ← h1,
    LinearEquiv.symm_apply_apply]

theorem re_conj_form {n : Type} [Fintype n] (H : Matrix n n ℂ) (v : n → ℂ) :
    (star (fun j => starRingEnd ℂ (v j)) ⬝ᵥ (H *ᵥ fun j => starRingEnd ℂ (v j))).re =
      (star v ⬝ᵥ (H.map (starRingEnd ℂ) *ᵥ v)).re := by
  rw [← Complex.conj_re (star v ⬝ᵥ _)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, mulVec, map_sum, map_mul]

theorem normSq_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualNormSq b hb (fun t => starRingEnd ℂ (z t)) = dualNormSq b hb z := by
  unfold dualNormSq
  rw [recover_conj]
  refine Fintype.sum_equiv (conjPerm K) _ _ fun σ => ?_
  have hσ : conjPerm K σ = conjugate σ := rfl
  rw [hσ, F.conj σ]
  exact re_conj_form (F.metric σ) fun j => dualRecover b hb z (conjugate σ, j)

end DualLineConjugation

theorem DualLineConj.proof : DualLineConj.Statement := by
  intro K _ _ i F T _ _ b hb z
  show Real.sqrt (dualNormSq b hb fun t => starRingEnd ℂ (z ⟨(), t⟩)) =
    Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  rw [DualLineConjugation.normSq_conj b hb fun t => z ⟨(), t⟩]

end

end GroundTheory.Heights₂.Heights
end
