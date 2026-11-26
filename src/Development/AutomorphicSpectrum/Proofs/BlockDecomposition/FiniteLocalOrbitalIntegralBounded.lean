module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumQuadraticCharacterBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvFinSSOneNot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeGaussSumEstimate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMapLaw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndex

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNatMulMem
theorem UpperTheory.Reformulated.B.ExistsNatMulMem.exists_nat_mul_mem :
    ∀ (F : Type) [inst : Field F] [NumberField F] (x : F),
    ∃ (m : ℕ), (0 : ℕ) < m ∧ ∃ (r : NumberField.RingOfIntegers F), (↑r : F) = (↑m : F) * x := by
  intro F _ _ x
  have hx : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, hint⟩ := hx.exists_integral_multiple
  have h2 : IsIntegral ℤ (((y.natAbs : ℕ) : F) * x) := by
    rcases Int.natAbs_eq y with h | h
    · have e : ((y.natAbs : ℕ) : F) * x = y • x := by
        rw [zsmul_eq_mul]
        congr 1
        have := congrArg (Int.cast : ℤ → F) h
        rw [Int.cast_natCast] at this
        exact this.symm
      rw [e]; exact hint
    · have e : ((y.natAbs : ℕ) : F) * x = -(y • x) := by
        rw [zsmul_eq_mul, ← neg_mul]
        congr 1
        have := congrArg (Int.cast : ℤ → F) h
        rw [Int.cast_neg, Int.cast_natCast] at this
        rw [this, neg_neg]
      rw [e]; exact hint.neg
  exact ⟨y.natAbs, Int.natAbs_pos.mpr hy, ⟨_, h2⟩, rfl⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaPosIndex
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaPosIndex
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin

theorem delta_pos_index : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (c : Matrix (Fin n) (Fin n) E),
    delta c ≠ 0 :=
  fun _ _ _ _ c => GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_ne_zero c

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaPosIndexStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_ne_zero' : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (c : Matrix (Fin n) (Fin n) E),
    delta c ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin.delta_pos_index | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin.delta_pos_index | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin.delta_pos_index <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelsNeighbourhoodBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelsNeighbourhoodBasis
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem exists_cube_subset_of_mem_nhds_zero {ι X : Type*} [Finite ι] [TopologicalSpace X] [Zero X]
    {V : Set (ι → X)} (hV : V ∈ nhds (0 : ι → X)) :
    ∃ W ∈ nhds (0 : X), ∀ Y : ι → X, (∀ i, Y i ∈ W) → Y ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  refine ⟨⋂ i, t i, Filter.iInter_mem.mpr (fun i => by simpa using ht i), fun Y hY => hsub ?_⟩
  intro i _
  exact Set.mem_iInter.mp (hY i) i

theorem latN_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ),
    ∀ U ∈ nhds (0 : Fin n → Fin M → Af F ⊗[F] E), ∃ N : ℕ, 0 < N ∧
      (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ⊆ U := by
  intro F E _ _ _ _ _ σ _ d b n M U hU
  let bb := Algebra.TensorProduct.basis (Af F) b
  obtain ⟨W1, hW1, hW1U⟩ := exists_cube_subset_of_mem_nhds_zero hU
  obtain ⟨W, hW, hWW1⟩ := exists_cube_subset_of_mem_nhds_zero hW1
  have hcont : Continuous (fun c : Fin d → Af F => ∑ k, c k • bb k) :=
    continuous_finsetSum _ (fun k _ => (continuous_apply k).smul continuous_const)
  have hV : (fun c : Fin d → Af F => ∑ k, c k • bb k) ⁻¹' W ∈ nhds (0 : Fin d → Af F) := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hW
  obtain ⟨V0, hV0, hV0V⟩ := exists_cube_subset_of_mem_nhds_zero hV
  obtain ⟨-, -, -, -, -, -, -, hN, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨N, hNpos, hNV0⟩ := hN V0 hV0
  refine ⟨N, hNpos, fun X hX => hW1U X fun a => hWW1 (X a) fun i => ?_⟩
  have hXai : InNOh b N (X a i) :=
    (show ∀ (a : Fin n) (i : Fin M), InNOh b N (X a i) from hX) a i
  have hmem : (⇑(bb.repr (X a i))) ∈ (fun c : Fin d → Af F => ∑ k, c k • bb k) ⁻¹' W := by
    apply hV0V
    intro k
    obtain ⟨y, hy, hk⟩ := hXai k
    rw [hk]
    exact hNV0 y hy
  simp only [Set.mem_preimage] at hmem
  rwa [bb.sum_repr] at hmem

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelsNeighbourhoodBasisStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_levels_neighbourhood_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ),
    ∀ U ∈ nhds (0 : Fin n → Fin M → Af F ⊗[F] E), ∃ N : ℕ, 0 < N ∧
      (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_small | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_small | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_small <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelOpenCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelOpenCompact
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem latN_isOpen_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M N : ℕ), 0 < N →
    IsOpen (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ∧
    IsCompact (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ _ d b n M N hN
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  obtain ⟨u, hu⟩ : IsUnit (N : Af F) := by
    have h1 : IsUnit (algebraMap F (Af F) (N : F)) := (IsUnit.mk0 _ hNF).map _
    rwa [map_natCast] at h1
  have hSo : IsOpen {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have hpre : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun y => (↑u⁻¹ : Af F) * y) ⁻¹' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show (↑u⁻¹ : Af F) * ((N : Af F) * z) ∈ Oh F
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
        exact hz
      · intro hy
        exact ⟨(↑u⁻¹ : Af F) * y, hy, by rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [hpre]
    exact (AfTop.isOpen_Oh F).preimage (continuous_const_mul _)
  have hSc : IsCompact {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have himg : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun z => (N : Af F) * z) '' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [himg]
    exact (AfTop.isCompact_Oh F).image (continuous_const_mul _)
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let Bs := Algebra.TensorProduct.basis (Af F) b
  let e : (Af F ⊗[F] E) ≃ₜ (Fin d → Af F) :=
    { Bs.equivFun.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.symm.toLinearMap }
  have hT : {x : Af F ⊗[F] E | InNOh b N x} =
      e ⁻¹' Set.univ.pi (fun _ => {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z}) := by
    ext x
    rw [Set.mem_preimage, Set.mem_univ_pi]
    exact Iff.rfl
  have hlat : (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => {x : Af F ⊗[F] E | InNOh b N x})) := by
    ext X
    simp only [Set.mem_univ_pi]
    exact Iff.rfl
  have hTo : IsOpen {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => hSo).preimage e.continuous
  have hTc : IsCompact {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact e.isCompact_preimage.mpr (isCompact_univ_pi fun _ => hSc)
  rw [hlat]
  exact ⟨isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hTo,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hTc⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelOpenCompactStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_level_open_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M N : ℕ), 0 < N →
    IsOpen (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ∧
    IsCompact (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_isOpen_isCompact | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_isOpen_isCompact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDualDenominatorBoundedStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDualDenominatorBounded
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem traceDual_clear_by_integer : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ f : F,
    (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f := by
  intro F _ _
  obtain ⟨a, ha, hint⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)).isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  refine ⟨Ideal.absNorm (Ideal.span {a}), ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha0
  · intro f hf
    have hmem : f ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (nonZeroDivisors (𝓞 F)) F))]
      intro x hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      obtain ⟨m, hm⟩ := hf r
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, eq_intCast]
      exact hm.symm
    obtain ⟨o, ho⟩ := hint f hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨c * o, ?_⟩
    rw [Algebra.smul_def] at ho
    show algebraMap (𝓞 F) F (c * o) = _
    rw [map_mul, ho, ← mul_assoc, ← map_mul, hc, map_natCast]

end GlobalTheory.CompanionTheory.SiegelND.Integ
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_dual_denominator_bounded : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ f : F,
    (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.traceDual_clear_by_integer | exact GlobalTheory.CompanionTheory.SiegelND.Integ.traceDual_clear_by_integer | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.traceDual_clear_by_integer <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaConjInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaConjInvariant
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap

theorem bijective_algHom (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) : Function.Bijective σ := by
  have hinj : Function.Injective σ := (σ : E →+* E).injective
  refine ⟨hinj, ?_⟩
  let τ : E →ₐ[ℚ] E := (σ : E →+* E).toRatAlgHom
  have h2 : Function.Injective τ.toLinearMap := hinj
  exact LinearMap.injective_iff_surjective.mp h2

theorem delta_map (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (c : Matrix (Fin n) (Fin n) E) : delta (c.map σ) = delta c := by
  classical
  let e : E ≃+* E := (AlgEquiv.ofBijective σ (bijective_algHom F E σ)).toRingEquiv
  let ψ : 𝓞 E ≃+* 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv e
  have hψ : ∀ o : 𝓞 E, algebraMap (𝓞 E) E (ψ o) = σ (algebraMap (𝓞 E) E o) := fun o => rfl
  let φ : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E) :=
    { toFun := fun y i => ψ (y i)
      map_zero' := by
        funext i
        simp
      map_add' := by
        intro y z
        funext i
        simp }
  have hφ : ∀ y j, φ y j = ψ (y j) := fun y j => rfl
  have hvec : ∀ y : Fin n → 𝓞 E, (c.map σ) *ᵥ (fun j => algebraMap (𝓞 E) E (φ y j)) =
      fun i => σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) := by
    intro y
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, hφ, hψ]
  have key : Kc c = (Kc (c.map σ)).comap φ := by
    ext y
    rw [AddSubgroup.mem_comap]
    show (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) ↔
      (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = ((c.map σ) *ᵥ fun j => algebraMap (𝓞 E) E (φ y j)) i)
    rw [hvec]
    refine forall_congr' fun i => ⟨fun h => h.elim fun o ho => ⟨ψ o, by rw [hψ, ho]⟩,
      fun h => h.elim fun o ho => ⟨ψ.symm o, ?_⟩⟩
    apply e.injective
    show σ (algebraMap (𝓞 E) E (ψ.symm o)) = σ _
    rw [← hψ, RingEquiv.apply_symm_apply, ho]
  have hsurj : Function.Surjective φ := fun y =>
    ⟨fun i => ψ.symm (y i), funext fun i => ψ.apply_symm_apply (y i)⟩
  show (Kc (c.map σ)).index = (Kc c).index
  rw [key]
  first
    | exact (AddSubgroup.index_comap_of_surjective hsurj).symm
    | exact (AddSubgroup.index_comap_of_surjective _ hsurj).symm
    | exact (AddSubgroup.index_comap_of_surjective (H := Kc (c.map σ)) hsurj).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaConjInvariantStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_conj_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (c : Matrix (Fin n) (Fin n) E), delta (c.map σ) = delta c := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalTupleInLatticeLevel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalTupleInLatticeLevel
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem

theorem exists_nat_mul_mem (F : Type) [Field F] [NumberField F] (x : F) :
    ∃ m : ℕ, 0 < m ∧ ∃ r : 𝓞 F, (r : F) = (m : F) * x :=
  _root_.UpperTheory.Reformulated.B.ExistsNatMulMem.exists_nat_mul_mem F x

theorem repr_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Af F) b).repr (inclR (Af F) x) k
      = algebraMap F (Af F) (b.repr x k) := by
  have h : inclR (Af F) x = (1 : Af F) ⊗ₜ[F] x := rfl
  rw [h, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem natCast_mul_eq_smul {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℕ) (z : E) :
    (n : E) * z = (n : F) • z := by
  rw [Algebra.smul_def, map_natCast]

theorem intCast_mul_eq_smul {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℤ) (z : E) :
    (n : E) * z = (n : F) • z := by
  rw [Algebra.smul_def, map_intCast]

theorem exists_clear_family {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) {ι : Type} [Fintype ι] (e : ι → E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (t : ι) (o : 𝓞 E) (k : Fin d),
      ∃ r : 𝓞 F, (r : F) = b.repr ((D : E) * (e t * (o : E))) k := by
  classical
  let B := RingOfIntegers.basis E
  choose m hm hr using fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d =>
    exists_nat_mul_mem F (b.repr (e p.1 * (B p.2.1 : E)) p.2.2)
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun t o k => ?_⟩
  set D : ℕ := ∏ p, m p with hDdef
  have hterm : ∀ l, ∃ r : 𝓞 F, (r : F) = b.repr ((D : E) * (e t * (B l : E))) k := by
    intro l
    obtain ⟨c, hc⟩ : m (t, l, k) ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    obtain ⟨r, hr1⟩ := hr (t, l, k)
    refine ⟨(c : 𝓞 F) * r, ?_⟩
    rw [natCast_mul_eq_smul (F := F), map_smul, Finsupp.smul_apply, smul_eq_mul, hc]
    simp only [map_mul, map_natCast, Nat.cast_mul]
    have hr2 : (r : F) = (m (t, l, k) : F) * b.repr (e t * (B l : E)) k := hr1
    change (c : F) * (r : F) = _
    rw [hr2]
    ring
  choose r hr' using hterm
  refine ⟨∑ l, (B.repr o l) • r l, ?_⟩
  have ho : (o : E) = ∑ l, ((B.repr o l : ℤ) : E) * (B l : E) := by
    have h3 := congrArg (algebraMap (𝓞 E) E) (B.sum_repr o)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h3
    rw [show (o : E) = algebraMap (𝓞 E) E o from rfl, ← h3]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
  have hsum : (D : E) * (e t * (o : E))
      = ∑ l, ((B.repr o l : ℤ) : F) • ((D : E) * (e t * (B l : E))) := by
    rw [ho, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← intCast_mul_eq_smul]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum, Finsupp.finsetSum_apply]
  have h4 : ((∑ l, (B.repr o l) • r l : 𝓞 F) : F) = ∑ l, ((B.repr o l : ℤ) : F) * (r l : F) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ l, (B.repr o l) • r l : 𝓞 F) : F)
      = algebraMap (𝓞 F) F (∑ l, (B.repr o l) • r l) from rfl, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
  rw [h4]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hr']

theorem ratTuple_mem_latN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n N : ℕ), 0 < N →
    ∃ s : ℕ, 0 < s ∧ ∀ ρ : Fin M → Fin n → 𝓞 E, ratTuple J s ρ ∈ latN b n M N := by
  intro F E _ _ _ _ _ d b M J n N hN
  obtain ⟨D, hD0, hD⟩ := exists_clear_family b (fun p : Fin M × Fin M => J⁻¹ p.1 p.2)
  refine ⟨N * D, Nat.mul_pos hN hD0, fun ρ => ?_⟩
  show ∀ a i, InNOh b N (ratTuple J (N * D) ρ a i)
  intro a j k
  choose r hr using fun i => hD (j, i) (ρ i a) k
  refine ⟨algebraMap F (Af F) (((∑ i, r i : 𝓞 F)) : F), ?_, ?_⟩
  · exact ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 _).2 ⟨_, rfl⟩
  · show (Algebra.TensorProduct.basis (Af F) b).repr
      (inclR (Af F) (((N * D : ℕ) : E) *
        (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j)) k = _
    rw [repr_inclR]
    have h1 : ((N * D : ℕ) : E) * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j
        = (N : F) • ∑ i, (D : E) * (J⁻¹ j i * (ρ i a : E)) := by
      rw [← natCast_mul_eq_smul, Nat.cast_mul, Matrix.mulVec, dotProduct, ← Finset.mul_sum,
        mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finsupp.finsetSum_apply,
      map_mul, map_natCast]
    congr 2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, r i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∑ i, r i) from rfl, map_sum]
    exact Finset.sum_congr rfl fun i _ => (hr i).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalTupleInLatticeLevelStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_tuple_in_lattice_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n N : ℕ), 0 < N →
    ∃ s : ℕ, 0 < s ∧ ∀ ρ : Fin M → Fin n → 𝓞 E, ratTuple J s ρ ∈ latN b n M N := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem.ratTuple_mem_latN | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem.ratTuple_mem_latN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem.ratTuple_mem_latN <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseCocycleBimultiplicative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseCocycleBimultiplicative
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (z : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ z) = Algebra.trace R (R ⊗[F] E) z := by
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  let e : (R ⊗[F] E) ≃ₐ[R] (R ⊗[F] E) := Algebra.TensorProduct.congr AlgEquiv.refl s
  have h : sigR R σ z = e z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [sigR, e, s]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [h]
  exact Algebra.trace_eq_of_algEquiv e z

theorem hR_add_left (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hR_add_right (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

end Gen

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem trace_gram2_swap (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j) (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J Y X)) =
      Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y)) := by
  rw [← trace_sigR (Af F) σ hσ]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, gram2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  have hb : sigR (Af F) σ ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) c a) = (b : Matrix _ _ _) a c := b.2 a c
  rw [hb, GlobalTheory.CompanionTheory.SiegelND.Coef.sigR_hR (Af F) σ hσ hJ]

theorem gramR_add (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    gramR (Af F) σ J (X + Y) = gramR (Af F) σ J X + gramR (Af F) σ J Y + gram2 σ J X Y + gram2 σ J Y X := by
  funext a c
  simp only [gramR, gram2, Pi.add_apply, Matrix.add_apply, hR_add_left, hR_add_right]
  abel

end Fin

theorem psiFin_add {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (u v : Af F) :
    psiFin F ψ (u + v) = psiFin F ψ u * psiFin F ψ v := by
  have h : pairA F 0 (u + v) = pairA F 0 u + pairA F 0 v := by
    have h0 : (0 : Ainf F) = 0 + 0 := (add_zero 0).symm
    exact congrArg (fun t => pairA F t (u + v)) h0
  simp only [psiFin]
  rw [h, AddChar.map_add_eq_mul]

theorem phaseB_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E),
    phaseB σ J (psiFin F ψ) b (X + Y) =
      phaseB σ J (psiFin F ψ) b X * phaseB σ J (psiFin F ψ) b Y * pairB σ J (psiFin F ψ) b X Y := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ _ b X Y
  have hsw := trace_gram2_swap σ (GlobalTheory.CompanionTheory.SiegelND.Coef.sig_invol hCM) hJ.1 b X Y
  have h2 : algebraMap F (Af F) (1 / 2) + algebraMap F (Af F) (1 / 2) = 1 := by
    rw [← map_add (f := _)]
    norm_num
  simp only [phaseB, pairB]
  rw [← psiFin_add, ← psiFin_add]
  congr 1
  rw [gramR_add, mul_add, mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    map_add, map_add, map_add, hsw]
  linear_combination (Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y))) * h2

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseCocycleBimultiplicativeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phase_cocycle_bimultiplicative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E),
    phaseB σ J (psiFin F ψ) b (X + Y) =
      phaseB σ J (psiFin F ψ) b X * phaseB σ J (psiFin F ψ) b Y * pairB σ J (psiFin F ψ) b X Y := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd.phaseB_add | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd.phaseB_add | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd.phaseB_add <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBiadditive
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBiadditive
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd

theorem psiFin_add' (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (x y : Af F) :
    psiFin F ψ (x + y) = psiFin F ψ x * psiFin F ψ y := by
  have h : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := by
    simp only [pairA]
    exact Prod.ext (add_zero 0).symm rfl
  simp only [psiFin]
  rw [h, AddChar.map_add_eq_mul]

theorem hR_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  simp [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, Finset.sum_add_distrib, add_mul, mul_add]

theorem hR_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' := by
  simp [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, Finset.sum_add_distrib, add_mul, mul_add]

theorem pairB_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
    (b : HermR (Af F) σ n),
    (∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b (X + X') Y =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X' Y) ∧
    (∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b X (Y + Y') =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X Y') := by
  intro F E _ _ _ _ _ σ M J n ψ b
  have hg1 : ∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E,
      gram2 σ J (X + X') Y = gram2 σ J X Y + gram2 σ J X' Y := by
    intro X X' Y
    ext a c
    simp only [gram2, Pi.add_apply, Matrix.add_apply]
    exact hR_add_left _ σ J _ _ _
  have hg2 : ∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E,
      gram2 σ J X (Y + Y') = gram2 σ J X Y + gram2 σ J X Y' := by
    intro X Y Y'
    ext a c
    simp only [gram2, Pi.add_apply, Matrix.add_apply]
    exact hR_add_right _ σ J _ _ _
  refine ⟨fun X X' Y => ?_, fun X Y Y' => ?_⟩
  · simp only [pairB, hg1, Matrix.mul_add, Matrix.trace_add, map_add (f := _), psiFin_add']
  · simp only [pairB, hg2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), psiFin_add']

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBiadditiveStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_biadditive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
    (b : HermR (Af F) σ n),
    (∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b (X + X') Y =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X' Y) ∧
    (∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b X (Y + Y') =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X Y') := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd.pairB_add | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd.pairB_add | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd.pairB_add <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLocalOrbitalIntegralBounded
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec

set_option maxHeartbeats 1000000 in
theorem finite_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
    ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    ∃ (C : ℝ) (t : F), t ≠ 0 ∧ ∀ c : hermE σ n,
      ‖starLoc (Af F) σ J (psiFin F ψ) μ Q (hermIn (Af F) σ n c)‖ ≤
        C * (delta (t • c).1 : ℝ) ^ (-((M : ℝ) / 2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ hψ μ hμ Q hQ
  classical
  obtain ⟨hA1, hA2, hA3, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := hA1
  haveI : SecondCountableTopology (Af F) := hA2
  haveI : T2Space (Af F) := hA3
  obtain ⟨hT1, hT2, hT3, hT4, -, -, -, hT8, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := hT1
  haveI : SecondCountableTopology (Af F ⊗[F] E) := hT3
  haveI : T2Space (Af F ⊗[F] E) := hT4
  haveI : BorelSpace (Fin n → Fin M → Af F ⊗[F] E) := hT8 n M
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (Module.Basis (Fin d) F E) :=
    ⟨_, ⟨Module.finBasis F E⟩⟩
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.T.lattice_levels_neighbourhood_basis F E σ hCM d b n M _ (invariant_mem_nhds hQ.1 hQ.2)
  obtain ⟨hLo, hLc⟩ := GlobalTheory.T.lattice_level_open_compact F E σ hCM d b n M N hN
  set L := latN b n M N with hL
  obtain ⟨s, hs⟩ := eq_sum_cosets hQ.2 L hLo (fun x l hl => hNU hl x)
  obtain ⟨D, hD, hDc⟩ := GlobalTheory.T.trace_dual_denominator_bounded F
  obtain ⟨t₁, ht₁, htest⟩ := GlobalTheory.T.rational_character_kernel_scaling F E σ hCM d b ψ hψ N hN D hD hDc
  obtain ⟨s₂, hs₂, hrat⟩ := GlobalTheory.T.rational_tuple_in_lattice_level F E d b M J n N hN
  have hs₂F : ((s₂ : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hs₂.ne'
  refine ⟨(∑ a ∈ s, ‖Q a‖) * (μ (L : Set _)).toReal, t₁ * (s₂ : F), mul_ne_zero ht₁ hs₂F, fun c => ?_⟩
  set t : F := t₁ * (s₂ : F) with ht
  set bc := hermIn (Af F) σ n c with hbc
  obtain ⟨hp1, hp2, hp3⟩ := GlobalTheory.T.phase_continuous_unitary F E σ hCM M J n ψ hψ bc
  obtain ⟨hq1, hq2⟩ := GlobalTheory.T.pairing_biadditive F E σ M J n ψ bc
  set q := phaseB σ J (psiFin F ψ) bc with hq
  set B := pairB σ J (psiFin F ψ) bc with hB
  set S : Set (Fin n → Fin M → Af F ⊗[F] E) := {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1} with hS
  have hLfin : μ (L : Set _) ≠ ⊤ := hLc.measure_lt_top.ne
  have hSL : S ⊆ L := fun y hy => hy.1
  have hSfin : μ S ≠ ⊤ := ne_top_of_le_ne_top hLfin (measure_mono hSL)

  have hbd : ‖starLoc (Af F) σ J (psiFin F ψ) μ Q bc‖ ≤
      (∑ a ∈ s, ‖Q a‖) * √((μ (L : Set _)).toReal * (μ S).toReal) := by
    have hw := GlobalTheory.T.gauss_sum_quadratic_character_bound _ μ L hLc hLo q B hp1 hp2 (GlobalTheory.T.phase_cocycle_bimultiplicative F E σ hCM M J hJ n ψ hψ bc) hq1 hq2
    exact GlobalTheory.T.gauss_sum_finite_average_bound _ μ L hLc hLo q hp1 hp2 _ hw Q s hs

  have hSm : MeasurableSet S := by
    have e : S = (L : Set _) ∩ ⋂ l ∈ L, (B l) ⁻¹' {1} := by
      ext y
      simp [hS]
    have hcl : IsClosed S := by
      rw [e]
      have hLcl : IsClosed (L : Set (Fin n → Fin M → Af F ⊗[F] E)) := hLc.isClosed
      exact hLcl.inter (isClosed_biInter fun l _ => isClosed_singleton.preimage (hp3 l))
    exact hcl.measurableSet

  have hdiff : ∀ u ∈ S, ∀ v ∈ S, ∀ l ∈ L, B l (v - u) = 1 := by
    intro u hu v hv l hl
    have h := hq2 l u (v - u)
    rw [add_sub_cancel, hv.2 l hl, hu.2 l hl, one_mul] at h
    exact h.symm
  set c' : Matrix (Fin n) (Fin n) E := ((t • c).1).map σ with hc'
  have hδ : delta c' = delta (t • c).1 := GlobalTheory.T.delta_conj_invariant F E σ n _
  have hδ0 : delta c' ≠ 0 := GlobalTheory.T.delta_ne_zero' E n c'
  haveI hfin : Finite ((Fin n → 𝓞 E) ⧸ Kc c') := Nat.finite_of_card_ne_zero hδ0
  haveI := Fintype.ofFinite ((Fin n → 𝓞 E) ⧸ Kc c')

  have hcount : ((delta c' ^ M : ℕ) : ℝ≥0∞) * μ S ≤ μ (L : Set _) := by
    have h := GlobalTheory.T.disjoint_translates_volume_bound _ μ L S hSm hSL (Fin M → (Fin n → 𝓞 E) ⧸ Kc c')
      (fun φ => ratTuple J s₂ fun i => (φ i).out) (fun φ => hrat _) ?_
    · have hc : Fintype.card (Fin M → (Fin n → 𝓞 E) ⧸ Kc c') = delta c' ^ M := by
        rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]
        rfl
      rwa [hc] at h
    · intro φ φ' u v hu hv huv
      funext i₀
      have hρ : ratTuple (F := F) J s₂ (fun i => (φ i).out - (φ' i).out) = ratTuple J s₂ (fun i => (φ i).out) - ratTuple J s₂ (fun i => (φ' i).out) := by
        funext a j
        simp only [ratTuple, Pi.sub_apply, map_sub]
        rw [show (fun i => algebraMap (𝓞 E) E ((φ i).out a) - algebraMap (𝓞 E) E ((φ' i).out a)) =
          (fun i => algebraMap (𝓞 E) E ((φ i).out a)) - (fun i => algebraMap (𝓞 E) E ((φ' i).out a)) from rfl,
          Matrix.mulVec_sub]
        simp [mul_sub]
      have hmem : ∀ l ∈ L, B l (ratTuple J s₂ fun i => (φ i).out - (φ' i).out) = 1 := by
        intro l hl
        have : ratTuple (F := F) J s₂ (fun i => (φ i).out - (φ' i).out) = v - u := by
          rw [hρ, sub_eq_sub_iff_add_eq_add, add_comm v]
          exact huv
        rw [this]
        exact hdiff u hu v hv l hl
      have hK : (φ i₀).out - (φ' i₀).out ∈ Kc c' := by
        intro c₀
        have hx := htest ((s₂ : E) * ∑ a, c.1 a c₀ *
          algebraMap (𝓞 E) E (((φ i₀).out - (φ' i₀).out) a)) (fun x hx => by
            have h1 := hmem (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (by
              intro a i
              by_cases h : a = c₀ ∧ i = i₀
              · simpa [h] using hx
              · simp only [h, if_false]
                exact (latN b n M N).zero_mem a i)
            rw [hB, hbc, GlobalTheory.T.pairing_on_rational_tuple_formula F E σ M J hJ n (psiFin F ψ) c c₀ i₀ x s₂ _] at h1
            exact h1)
        obtain ⟨o, ho⟩ := hx
        refine ⟨o, ?_⟩
        rw [ho]
        simp only [Matrix.mulVec, dotProduct, hc', Matrix.map_apply, Finset.smul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        have h3 : σ (c.1 c₀ a) = c.1 a c₀ := c.2 a c₀
        rw [show σ ((t • c).1 c₀ a) = t • c.1 a c₀ from by
          show σ (t • c.1 c₀ a) = _
          rw [Algebra.smul_def, map_mul, AlgHom.commutes, h3, ← Algebra.smul_def]]
        simp only [ht, Algebra.smul_def, map_mul, map_natCast]
        ring
      have h5 : (QuotientAddGroup.mk (φ' i₀).out : (Fin n → 𝓞 E) ⧸ Kc c') = QuotientAddGroup.mk (φ i₀).out :=
        QuotientAddGroup.eq.2 (by rw [neg_add_eq_sub]; exact hK)
      rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h5
      exact h5.symm

  have hδpos : (0 : ℝ) < (delta c' : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hδ0)
  have hreal : (delta c' : ℝ) ^ M * (μ S).toReal ≤ (μ (L : Set _)).toReal := by
    have h := ENNReal.toReal_mono hLfin hcount
    rw [ENNReal.toReal_mul] at h
    simpa using h
  rw [← hδ]
  set A := (μ (L : Set _)).toReal with hA
  set Sr := (μ S).toReal with hSr
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ Sr := ENNReal.toReal_nonneg
  set w : ℝ := (delta c' : ℝ) ^ (-((M : ℝ) / 2)) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hδpos.le _
  have hw2 : w ^ 2 * (delta c' : ℝ) ^ M = 1 := by
    rw [hw, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hδpos.le, ← Real.rpow_natCast _ M, ← Real.rpow_add hδpos]
    have : -((M : ℝ) / 2) * ((2 : ℕ) : ℝ) + (M : ℝ) = 0 := by push_cast; ring
    rw [this, Real.rpow_zero]
  have hsq : √(A * Sr) ≤ A * w := by
    refine Real.sqrt_le_iff.2 ⟨mul_nonneg hA0 hw0, ?_⟩
    have h1 : Sr = w ^ 2 * ((delta c' : ℝ) ^ M * Sr) := by rw [← mul_assoc, hw2, one_mul]
    have h2 : Sr ≤ w ^ 2 * A := by
      rw [h1]
      exact mul_le_mul_of_nonneg_left hreal (sq_nonneg _)
    calc A * Sr ≤ A * (w ^ 2 * A) := mul_le_mul_of_nonneg_left h2 hA0
      _ = (A * w) ^ 2 := by ring
  calc _ ≤ (∑ a ∈ s, ‖Q a‖) * √(A * Sr) := hbd
    _ ≤ (∑ a ∈ s, ‖Q a‖) * (A * w) :=
        mul_le_mul_of_nonneg_left hsq (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLocalOrbitalIntegralBoundedStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_local_orbital_integral_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
    ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    ∃ (C : ℝ) (t : F), t ≠ 0 ∧ ∀ c : hermE σ n,
      ‖starLoc (Af F) σ J (psiFin F ψ) μ Q (hermIn (Af F) σ n c)‖ ≤
        C * (delta (t • c).1 : ℝ) ^ (-((M : ℝ) / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.finite_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.finite_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.finite_bound <;> assumption)
end
