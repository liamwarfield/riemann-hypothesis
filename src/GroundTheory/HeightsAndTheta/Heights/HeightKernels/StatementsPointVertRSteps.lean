module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsPointVertRSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def curveRing (y : (Σ k, ι k) → Ω) : Subring Ω :=
  ⨅ (c : ∀ k, ι k) (_ : ∀ k, y ⟨k, c k⟩ ≠ 0), (chartRingZ y c).toSubring

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_curveRing {y : (Σ k, ι k) → Ω} {b : Ω} :
    b ∈ curveRing y ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → b ∈ chartRingZ y c := by
  simp [curveRing, Subring.mem_iInf]

def curveMul (y : (Σ k, ι k) → Ω) (x : Ω) : AddSubgroup Ω :=
  (curveRing y).toAddSubgroup.map (AddMonoidHom.mulLeft x)

end Objects

def CurveCharts.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      Module.Finite ℤ (curveRing y) ∧
      Module.finrank ℤ (curveRing y) = Module.finrank ℚ (blockFnField y) ∧
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧
        ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a

def VertRIndex.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) s =
        Real.log (genIndex (chartLat y (fun _ => 1) 1) (curveMul y (aeval y s)))

def SectionIndexNorm.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      (Module.finrank (blockFnField y) K' : ℝ) *
          Real.log (genIndex (chartLat y (fun _ => 1) 1) (curveMul y (aeval y s))) =
        Real.log |(Algebra.norm ℚ (aeval y s) : ℝ)| +
          Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
            (1 : Submodule (𝓞 K') K').toAddSubgroup)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSubLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def DualTopSubLattice.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice ≤ F.lattice →
    II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F'.withStdMetric.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def twoVecExample : Fin 1 → ℚ := fun _ => 2

def HermLattice.twiceStandardExample : HermLattice ℚ 1 where
  lattice := Submodule.span (𝓞 ℚ) {twoVecExample}
  fg := Submodule.fg_span (Set.finite_singleton _)
  span_eq := by
    rw [Submodule.span_span_of_tower]
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x = (x 0 / 2) • twoVecExample := by
      funext j
      fin_cases j
      simp [twoVecExample]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

theorem twiceStandardExample_le :
    HermLattice.twiceStandardExample.lattice ≤ (HermLattice.standard ℚ 1).lattice := by
  show Submodule.span (𝓞 ℚ) {twoVecExample} ≤ _
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have h : twoVecExample = (2 : 𝓞 ℚ) • (Pi.single 0 1 : Fin 1 → ℚ) := by
    funext j
    fin_cases j
    simp [twoVecExample, Algebra.smul_def, map_ofNat]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopBasisChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def DualTopBasisChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T₂ : Type) [Fintype T]
    [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b₂ : Module.Basis T₂ ℤ (dualLattice F))
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T₂) (dualIdeal b₂) i (fun _ => dualLine F b₂ hb₂) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb)

def dualBasisStandardNeg : Module.Basis (Fin 1) ℤ (dualLattice (HermLattice.standard ℚ 1)) :=
  (dualBasisStandard.map (LinearEquiv.neg ℤ)).reindex (Equiv.ofUnique Unit (Fin 1))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOnPlane
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace DualPointsOnPlane

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T]

theorem smul_mem_dualLattice (α : 𝓞 K) {φ : Fin i → K} (hφ : φ ∈ dualLattice F) :
    (α : K) • φ ∈ dualLattice F := by
  intro x hx
  obtain ⟨a, ha⟩ := hφ x hx
  refine ⟨α * a, ?_⟩
  rw [map_mul, ha, smul_dotProduct, smul_eq_mul]

def mulMat (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s t : T) : ℤ :=
  b.repr ⟨(α : K) • (b s : Fin i → K), smul_mem_dualLattice α (b s).2⟩ t

theorem mulMat_sum (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s : T) (j : Fin i) :
    ∑ t, (mulMat b α s t : K) * (b t : Fin i → K) j = (α : K) * (b s : Fin i → K) j := by
  have h := b.sum_repr ⟨(α : K) • (b s : Fin i → K), smul_mem_dualLattice α (b s).2⟩
  have h2 := congrArg (fun v : dualLattice F => (v : Fin i → K) j) h
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
    zsmul_eq_mul, smul_eq_mul] at h2
  exact h2


omit [Fintype T] in
theorem recover_spec (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (Z : T → ℂ) (t : T) :
    Z t = ∑ p : (K →+* ℂ) × Fin i, p.1 ((b t : Fin i → K) p.2) * dualRecover b hb Z p := by
  have h := (LinearEquiv.ofBijective (Matrix.mulVecLin (dualEmbMatrix b)) hb).apply_symm_apply Z
  rw [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply] at h
  conv_lhs => rw [← h]
  rfl

theorem mulMat_recover (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (α : 𝓞 K) (Z : T → ℂ) (s : T) :
    ∑ t, (mulMat b α s t : ℂ) * Z t =
      ∑ p : (K →+* ℂ) × Fin i, p.1 ((b s : Fin i → K) p.2) * (p.1 α * dualRecover b hb Z p) := by
  calc ∑ t, (mulMat b α s t : ℂ) * Z t
      = ∑ t, ∑ p : (K →+* ℂ) × Fin i,
          (mulMat b α s t : ℂ) * (p.1 ((b t : Fin i → K) p.2) * dualRecover b hb Z p) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [recover_spec b hb Z t, Finset.mul_sum]
    _ = ∑ p : (K →+* ℂ) × Fin i,
          (∑ t, (mulMat b α s t : ℂ) * p.1 ((b t : Fin i → K) p.2)) * dualRecover b hb Z p := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have h := congrArg p.1 (mulMat_sum b α s p.2)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, map_intCast] at h
        rw [h]
        ring

def quad (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s r : T) : MRing (dualBlocks T) :=
  X ⟨(), s⟩ * ∑ t, C (mulMat b α r t) * X ⟨(), t⟩ - (∑ t, C (mulMat b α s t) * X ⟨(), t⟩) * X ⟨(), r⟩

theorem quad_mem (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s r : T) :
    quad b α s r ∈ dualIdeal b := by
  have hlin : ∀ u, ∑ t, (mulMat b α u t : MvPolynomial (Fin i) K) *
      ∑ j, C ((b t : Fin i → K) j) * X j = C (α : K) * ∑ j, C ((b u : Fin i → K) j) * X j := by
    intro u
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := congrArg (C : K → MvPolynomial (Fin i) K) (mulMat_sum b α u j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_intCast] at h
    rw [← mul_assoc, ← h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have hS : ∀ u, ∑ t, (mulMat b α u t : ProjField K i) * dualLatticeCoord b ⟨(), t⟩ =
      algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) * dualLatticeCoord b ⟨(), u⟩ := by
    intro u
    have h := congrArg (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) (hlin u)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [dualLatticeCoord, map_sum, map_mul, map_intCast] using h
  have hsum : ∀ u, mConeMap (dualLatticeCoord b) (∑ t, C (mulMat b α u t) * X ⟨(), t⟩) =
      MvPolynomial.C (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) *
        dualLatticeCoord b ⟨(), u⟩) * MvPolynomial.X () := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hS u, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [mConeMap, aeval_X, map_mul, map_intCast, eq_intCast]
    ring
  show quad b α s r ∈ RingHom.ker (mConeMap (dualLatticeCoord b))
  rw [RingHom.mem_ker]
  simp only [quad, map_sub, map_mul, hsum]
  simp only [mConeMap, aeval_X]
  ring

theorem eval_quad (z : (Σ _ : Unit, T) → ℂ) (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K)
    (s r : T) : eval z (map (Int.castRingHom ℂ) (quad b α s r)) =
      z ⟨(), s⟩ * ∑ t, (mulMat b α r t : ℂ) * z ⟨(), t⟩ -
        (∑ t, (mulMat b α s t : ℂ) * z ⟨(), t⟩) * z ⟨(), r⟩ := by
  simp [quad]

theorem agree (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ)
    (hz : z ∈ mcPts (dualIdeal b)) (α : 𝓞 K) (p q : (K →+* ℂ) × Fin i)
    (hp : dualRecover b hb (fun t => z ⟨(), t⟩) p ≠ 0) (hq : dualRecover b hb (fun t => z ⟨(), t⟩) q ≠ 0) :
    p.1 α = q.1 α := by
  obtain ⟨s0, hs0⟩ := hz.1 ()
  obtain ⟨Z, hZ⟩ : ∃ Z : T → ℂ, Z = fun t => z ⟨(), t⟩ := ⟨_, rfl⟩
  have hZt : ∀ t, z ⟨(), t⟩ = Z t := fun t => by rw [hZ]
  rw [← hZ] at hp hq
  rw [hZt] at hs0
  have hrel : ∀ s r, Z s * ∑ t, (mulMat b α r t : ℂ) * Z t =
      (∑ t, (mulMat b α s t : ℂ) * Z t) * Z r := by
    intro s r
    have h := hz.2 _ (quad_mem b α s r)
    rw [eval_quad] at h
    simp only [hZt] at h
    exact sub_eq_zero.mp h
  have hL : ∀ r, ∑ t, (mulMat b α r t : ℂ) * Z t =
      ((∑ t, (mulMat b α s0 t : ℂ) * Z t) / Z s0) * Z r := by
    intro r
    rw [div_mul_eq_mul_div, eq_div_iff hs0]
    linear_combination hrel s0 r
  set lam := (∑ t, (mulMat b α s0 t : ℂ) * Z t) / Z s0
  have hw : (fun p : (K →+* ℂ) × Fin i => p.1 α * dualRecover b hb Z p) = lam • dualRecover b hb Z := by
    apply hb.1
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    funext s
    show ∑ p : (K →+* ℂ) × Fin i, p.1 ((b s : Fin i → K) p.2) * (p.1 α * dualRecover b hb Z p) =
      ∑ p : (K →+* ℂ) × Fin i, p.1 ((b s : Fin i → K) p.2) * (lam * dualRecover b hb Z p)
    rw [← mulMat_recover, hL s, recover_spec b hb Z s, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have hp' := congrFun hw p
  have hq' := congrFun hw q
  simp only [Pi.smul_apply, smul_eq_mul] at hp' hq'
  rw [mul_right_cancel₀ hp hp', mul_right_cancel₀ hq hq']

end DualPointsOnPlane


open DualPointsOnPlane in
theorem DualPtsOnPlane.proof : DualPtsOnPlane.Statement := by
  intro K _ _ i F T _ _ b hb z hz
  obtain ⟨s0, hs0⟩ := hz.1 ()
  obtain ⟨p0, hp0⟩ : ∃ p, dualRecover b hb (fun t => z ⟨(), t⟩) p ≠ 0 := by
    by_contra hne
    simp only [ne_eq, not_exists, not_not] at hne
    exact hs0 ((recover_spec b hb (fun t => z ⟨(), t⟩) s0).trans (by simp [hne]))
  refine ⟨p0.1, fun τ hτ j => ?_⟩
  by_contra hne
  apply hτ
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
  ext α
  exact agree b hb z hz α (τ, j) p0 hne hp0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStdBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualStdBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine (HermLattice.standard K i) b hb) =
      (Module.finrank ℚ K : ℝ) * II Unit (PBlk i) ⊥ i (fun _ => fsMulti (PBlk i))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualGeomDegCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

def DualGeomDegCharts.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∃ A : (K →+* ℂ) → Matrix (Fin i) (Fin (i - 1 + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      geomDeg (dualIdeal b) (dualLine F b hb) (i - 1) =
        ∑ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualMetricEnergy.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∑ k ∈ Finset.range i,
        ptsIntegral (dualIdeal b)
          (pot fun j : Fin (i - 1) =>
            if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
          (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
      1 / 2 * (∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re) *
        geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualEnergyCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

def DualEnergyCharts.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∃ A : (K →+* ℂ) → Matrix (Fin i) (Fin (i - 1 + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      ∀ k : ℕ,
        ptsIntegral (dualIdeal b)
            (pot fun j : Fin (i - 1) =>
              if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
            (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
          ∑ σ : K →+* ℂ, chartMixedEnergy ((A σ)ᴴ * F.metric σ * A σ) ((A σ)ᴴ * A σ) k

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOfPlane
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace DualPointsOfPlane

theorem map_eval₂_int {ι A B : Type*} [CommRing A] [CommRing B] (k : A →+* B) (c : ℤ →+* A) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (eval₂ c g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem map_aeval_int {ι A B : Type*} [CommRing A] {_ : Algebra ℤ A} [CommRing B] (k : A →+* B) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (aeval g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [aeval_def, map_eval₂_int]

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def formPoly (b : Module.Basis T ℤ (dualLattice F)) (p : Σ _ : Unit, T) : MvPolynomial (Fin i) K :=
  ∑ j, C ((b p.2 : Fin i → K) j) * X j


omit [Fintype T] [DecidableEq T] in
theorem dualPlanePt_eq_mulVec [DecidableEq (K →+* ℂ)] (b : Module.Basis T ℤ (dualLattice F))
    (σ : K →+* ℂ) (v : Fin i → ℂ) (t : T) :
    dualPlanePt b σ v ⟨(), t⟩ =
      (dualEmbMatrix b *ᵥ fun p : (K →+* ℂ) × Fin i => if p.1 = σ then v p.2 else 0) t := by
  simp only [dualPlanePt, mulVec, dotProduct, dualEmbMatrix, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single σ]
  · simp
  · intro τ hτ
    simp [hτ]


omit [Fintype T] [DecidableEq T] in
theorem eval₂_formPoly (b : Module.Basis T ℤ (dualLattice F)) (σ : K →+* ℂ) (v : Fin i → ℂ)
    (p : Σ _ : Unit, T) :
    eval₂Hom σ v (formPoly b p) = dualPlanePt b σ v p := by
  simp [formPoly, dualPlanePt]

end DualPointsOfPlane


open DualPointsOfPlane in
theorem DualPtsOfPlane.proof : DualPtsOfPlane.Statement := by
  intro K _ _ i F T _ _ b hb σ v hv
  classical
  refine ⟨fun _ => ?_, fun f hf => ?_⟩
  · have hw : (fun p : (K →+* ℂ) × Fin i => if p.1 = σ then v p.2 else 0) ≠ 0 := by
      intro h0
      apply hv
      funext j
      simpa using congrFun h0 (σ, j)
    have hne : dualEmbMatrix b *ᵥ (fun p : (K →+* ℂ) × Fin i => if p.1 = σ then v p.2 else 0) ≠ 0 := by
      intro h0
      apply hw
      apply hb.1
      rw [map_zero, Matrix.mulVecLin_apply]
      exact h0
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hne
    exact ⟨t, by rw [dualPlanePt_eq_mulVec]; exact ht⟩
  · have h0 : mConeMap (dualLatticeCoord b) f = 0 := hf
    have h1 := congrArg (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) h0
    unfold mConeMap at h1
    rw [map_zero, map_aeval_int] at h1
    have hy : (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) ∘
        (fun p => C (dualLatticeCoord b p) * X p.1) =
        (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) ∘ formPoly b := by
      funext p
      simp [dualLatticeCoord, formPoly]
    rw [hy, ← map_eval₂_int (c := Int.castRingHom _)] at h1
    have h2 : eval₂ (Int.castRingHom _) (formPoly b) f = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h1
    have h3 := congrArg (eval₂Hom σ v) h2
    rw [map_zero, map_eval₂_int] at h3
    have hz : (eval₂Hom σ v) ∘ formPoly b = dualPlanePt b σ v := funext (eval₂_formPoly b σ v)
    rw [hz] at h3
    rw [eval_map]
    exact h3

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdMassAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix

noncomputable section

namespace StandardDualMassAtPoint

variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]

omit [Fintype T] [DecidableEq T] in
theorem segre_const (z : (Σ _ : Unit, T) → ℂ) (t : T) :
    segre (ι := dualBlocks T) z (fun _ => t) = z ⟨(), t⟩ := by
  simp [segre]


open scoped Classical in
omit [Fintype T] [DecidableEq T] in
open Classical in
theorem recover_planePt {i : ℕ} {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    dualRecover b hb (fun t => dualPlanePt b σ v ⟨(), t⟩) =
      fun p => if p.1 = σ then v p.2 else 0 := by
  rw [dualRecover, LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  funext t
  simp [Matrix.mulVec, dotProduct, dualEmbMatrix, dualPlanePt,
    Fintype.sum_prod_type]


omit [Fintype T] [DecidableEq T] in
theorem proj_segre_planePt {i : ℕ} {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    dualProj b hb (segre (dualPlanePt b σ v)) = v := by
  funext j
  simp only [dualProj_apply, segre_const, recover_planePt]
  rw [Finset.sum_eq_single σ (fun τ _ hτ => ite_eq_right hτ) (by simp)]
  exact ite_eq_left rfl

theorem h_eq (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {z : (Σ _ : Unit, T) → ℂ}
    (hz : z ∈ mcPts (dualIdeal b)) :
    (dualLine F b hb).h z = Real.sqrt (∑ j, ‖dualProj b hb (segre z) j‖ ^ 2) := by
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
  have hp : ∀ j, dualProj b hb (segre z) j = dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j) := by
    intro j
    simp only [dualProj_apply, segre_const]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)
  show Real.sqrt (dualNormSq b hb _) = _
  congr 1
  rw [dualNormSq, Finset.sum_eq_single σ]
  · rw [hF, one_mulVec, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, hp]
  · intro τ _ hτ
    have h0 : (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j)) = 0 := funext (hσ τ hτ)
    rw [h0]
    simp
  · simp

theorem sheetDensity_eq (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {y : Fin D → ℂ}
    {w : ((k : Unit) → dualBlocks T k) → ℂ} (h : ∃ γ, IsSheet (dualIdeal b) (dualProj b hb) y w γ) :
    sheetDensity (dualIdeal b) (dualProj b hb) (fun _ z => Real.log ((dualLine F b hb).h z))
      (fun _ => 1) y w = maDensity (fun _ : Fin D => gbPot) y := by
  unfold sheetDensity
  rw [dite_eq_left h, one_mul]
  apply maDensity_congr_of_eventuallyEq
  intro j
  filter_upwards [h.choose_spec.2] with y' hy'
  obtain ⟨-, hmc, hΨ⟩ := hy'
  show Real.log ((dualLine F b hb).h (h.choose y')) = gbPot y'
  rw [h_eq hOn hF b hb hmc, hΨ, gbPot, Fin.sum_univ_succ]
  simp

theorem fibre_eq (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement) {D : ℕ}
    {F : HermLattice K (D + 1)} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (y : Fin D → ℂ) :
    ReciprocityTheory.ChartRestriction.G.Geo.fibre (dualIdeal b) (dualProj b hb) y =
      Set.range fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl, hΨ⟩
    obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
    refine ⟨σ, congrArg segre ?_⟩
    have hW : dualRecover b hb (fun t => z ⟨(), t⟩) =
        dualRecover b hb (fun t => dualPlanePt b σ (Fin.cons 1 y) ⟨(), t⟩) := by
      rw [recover_planePt]
      funext ⟨τ, j⟩
      by_cases hτ : τ = σ
      · subst hτ
        rw [ite_eq_left rfl, ← hΨ]
        simp only [dualProj_apply, segre_const]
        exact (Finset.sum_eq_single τ (fun τ' _ h' => hσ τ' h' j) (by simp)).symm
      · rw [ite_eq_right hτ]
        exact hσ τ hτ j
    have h1 := (dualRecover b hb).injective hW
    funext ⟨u, t⟩
    cases u
    exact (congrFun h1 t).symm
  · rintro ⟨σ, rfl⟩
    have hv : (Fin.cons 1 y : Fin (D + 1) → ℂ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    exact ⟨_, hOf K (D + 1) F T b hb σ _ hv, rfl, proj_segre_planePt b hb σ _⟩


omit [Fintype T] [DecidableEq T] in
theorem planePt_injective {D : ℕ} {F : HermLattice K (D + 1)} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (y : Fin D → ℂ) :
    Function.Injective fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)) := by
  intro σ τ h
  have h1 := congrArg (fun w : ((k : Unit) → dualBlocks T k) → ℂ =>
    dualRecover b hb (fun t => w fun _ => t)) h
  simp only [segre_const, recover_planePt] at h1
  have h2 := congrFun h1 (σ, 0)
  simpa using h2

theorem isSheet_planePt (hOf : DualPtsOfPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (y : Fin D → ℂ) :
    IsSheet (dualIdeal b) (dualProj b hb) y (segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)))
      (fun y' => dualPlanePt b σ (Fin.cons 1 y')) := by
  have hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ)) := by
    rw [differentiable_pi]
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simpa using differentiable_apply (𝕜 := ℂ) k
  refine ⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, ?_, proj_segre_planePt b hb σ _⟩⟩
  · refine (differentiable_pi.mpr fun p => ?_) y'
    simp only [dualPlanePt]
    exact Differentiable.fun_sum fun j _ => (differentiable_pi.mp hc j).const_mul _
  · exact hOf K (D + 1) F T b hb σ _ fun h0 => by simpa using congrFun h0 0

end StandardDualMassAtPoint


open StandardDualMassAtPoint in
theorem DualStdMassAt.proof (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement) :
    DualStdMassAt.Statement := by
  intro K _ _ D F T _ _ b hb hF
  have hint : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (dualIdeal b) (dualProj b hb) y,
      sheetDensity (dualIdeal b) (dualProj b hb) (fun _ z => Real.log ((dualLine F b hb).h z))
        (fun _ => 1) y w = (Fintype.card (K →+* ℂ) : ℝ) * maDensity (fun _ : Fin D => gbPot) y := by
    intro y
    rw [fibre_eq hOn hOf b hb y, finsum_mem_range (planePt_injective b hb y),
      finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl fun σ _ => sheetDensity_eq hOn hF b hb ⟨_, isSheet_planePt hOf b hb σ y⟩,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold ptsIntegralAt
  simp only [hint]
  rw [integral_const_mul, integral_maDensity_gbPot, mul_one]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace TopDualBound

theorem grassConst_lines {i : ℕ} (hi : 1 ≤ i) : grassConst 1 1 (i - 1) = 1 / 2 * Real.log i := by
  have h : (1 : ℝ) + ((i - 1 : ℕ) : ℝ) = i := by
    rw [Nat.cast_sub hi]; push_cast; ring
  simp only [grassConst, h]
  norm_num

theorem dim_lines {i : ℕ} (hi : 1 ≤ i) : ((1 * 1 * (i - 1) + 1 : ℕ) : ℝ) = i := by
  congr 1; omega

end TopDualBound

theorem DualTopBound.proof (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hMetric : DualTopMetricChange.Statement)
    (hLattice : DualTopLatticeChange.Statement) (hStd : DualTopStandard.Statement)
    (hDeg : DualGeomDegStandard.Statement) (hGrass : GrassHeightBound.Statement) :
    DualTopBound.Statement := by
  intro hZ2 K _ _ i F T _ _ b hb II hi hII
  obtain ⟨T', _, _, ⟨b'⟩⟩ := hBasis K i (HermLattice.standard K i)
  have hb' := hBij K i (HermLattice.standard K i) T' b'
  set g := geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd
  have hA := hMetric K i F T b hb II hi hII
  have hB := hLattice K i F T T' b hb b' hb' II hi hII
  have hC := hStd K i T' b' hb' II hi hII
  have hG := hDeg K i F T b hb hi
  have hH := hGrass hZ2 1 1 (i - 1) le_rfl II hII
  rw [TopDualBound.dim_lines hi, TopDualBound.grassConst_lines hi] at hH
  rw [hA, hB, hC, hG]
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hslope : (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * (d * g) =
      -F.degree * g + d * ((i : ℝ) * (1 / 2 * Real.log i) * g) := by
    simp only [HermLattice.slope, normalise]
    rw [← hd]
    field_simp
  rw [hslope]
  have := mul_le_mul_of_nonneg_left hH hd0.le
  linarith

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
open scoped ComplexOrder

noncomputable section

namespace DualGeometricDegreePositive

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def stdLattice (F : HermLattice K i) : HermLattice K i where
  lattice := F.lattice
  fg := F.fg
  span_eq := F.span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

def oneLine : HermLine (dualBlocks T) :=
  HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)

omit [Fintype T] [DecidableEq T] in
theorem logNorm_oneLine : logNorm (oneLine (T := T)) 1 = fun _ => (1 : ℝ) := by
  funext z
  simp [logNorm, oneLine, HermLine.ofWeight]

omit [Fintype T] [DecidableEq T] in
theorem segre_apply (z : (Σ _ : Unit, T) → ℂ) (s : (k : Unit) → dualBlocks T k) :
    segre (ι := dualBlocks T) z s = z ⟨(), s ()⟩ := by
  simp [segre]

theorem isGoodProj (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    IsGoodProj (dualIdeal b) (dualProj b hb) := by
  intro z hz h0
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
  have hne : dualRecover b hb (fun t => z ⟨(), t⟩) ≠ 0 := by
    intro h
    obtain ⟨t, ht⟩ := hz.1 ()
    exact ht (congrFun ((dualRecover b hb).map_eq_zero_iff.mp h) t)
  obtain ⟨⟨τ, j⟩, hτ⟩ := Function.ne_iff.mp hne
  have hτσ : τ = σ := by
    by_contra h
    exact hτ (hσ τ h j)
  subst hτσ
  have h1 := congrFun h0 j
  rw [dualProj_apply] at h1
  simp only [segre_apply] at h1
  rw [Finset.sum_eq_single τ (fun τ' _ h => hσ τ' h j) (fun h => absurd (Finset.mem_univ τ) h)] at h1
  exact hτ h1

end DualGeometricDegreePositive


open DualGeometricDegreePositive in
theorem DualGeomDegPos.proof (hDeg : DegreeStatement) (hInd : PtsIndepStatement)
    (hArith : DualArithVar.Statement) (hSemi : DualLineSemipositive.Statement)
    (hOn : DualPtsOnPlane.Statement) (hMass : DualStdMassAt.Statement) :
    DualGeomDegPos.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨D, rfl⟩ : ∃ D, i = D + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hV : IsArithVar (dualIdeal b) (D + 1) := hArith K (D + 1) F T b hi
  have hS1 : IsSmoothHerm (dualLine (DualGeometricDegreePositive.stdLattice F) b hb) := (hSemi K (D + 1) (DualGeometricDegreePositive.stdLattice F) T b hb).1
  have e0 := hDeg Unit (dualBlocks T) (dualIdeal b) D (fun _ => dualLine F b hb) 2 hV
    (fun _ => (hSemi K (D + 1) F T b hb).1) Nat.prime_two
  have e1 := hDeg Unit (dualBlocks T) (dualIdeal b) D (fun _ => dualLine (DualGeometricDegreePositive.stdLattice F) b hb) 2 hV
    (fun _ => hS1) Nat.prime_two
  have hswap : geomDeg (dualIdeal b) (dualLine F b hb) D =
      geomDeg (dualIdeal b) (dualLine (DualGeometricDegreePositive.stdLattice F) b hb) D := by
    change ptsIntegral (dualIdeal b) (pot fun _ => dualLine F b hb) (fun _ => 1) =
      ptsIntegral (dualIdeal b) (pot fun _ => dualLine (DualGeometricDegreePositive.stdLattice F) b hb) (fun _ => 1)
    rw [e0, e1]
    rfl
  have hgood := isGoodProj hOn b hb
  have hΨ : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (dualIdeal b) Ψ := ⟨_, hgood⟩
  have hsec : IsSectionOn (dualIdeal b) (oneLine (T := T)) 1 := by
    refine ⟨fun _ => 0, fun _ => rfl, ?_, ?_⟩
    · intro d hd k
      rw [support_one] at hd
      simp only [Finset.mem_singleton] at hd
      simp [hd]
    · exact (Ideal.ne_top_iff_one _).1 hV.2.1.1.ne_top
  have h := hInd Unit (dualBlocks T) (dualIdeal b) D hΨ.choose (dualProj b hb)
    (fun _ => dualLine (DualGeometricDegreePositive.stdLattice F) b hb) oneLine 1 hV hΨ.choose_spec hgood (fun _ => hS1)
    contDiffOn_const hsec
  rw [logNorm_oneLine] at h
  have hm := hMass K D (DualGeometricDegreePositive.stdLattice F) T b hb fun _ => rfl
  have hval : geomDeg (dualIdeal b) (dualLine (DualGeometricDegreePositive.stdLattice F) b hb) D = Fintype.card (K →+* ℂ) := by
    unfold geomDeg ptsIntegral
    rw [dite_eq_left hΨ]
    exact h.trans hm
  rw [hswap, hval]
  exact_mod_cast Fintype.card_pos

end

end GroundTheory.Heights₂.Heights
end
