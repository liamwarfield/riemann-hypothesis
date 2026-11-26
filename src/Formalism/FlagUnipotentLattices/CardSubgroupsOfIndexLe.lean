module

public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SchurAverage
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExponentInequalityNondegenerateMid
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MeasurePreservingPiCompProd
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SumComplexEmbeddingsEqSumInfinitePlace
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ColonCountWeighted
public import Formalism.FlagUnipotentLattices.SignaturePreservingEntryNorms
public import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial

@[expose] public section

section -- merged from Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
namespace Formalism.HermitianLatticeCounting.Final.LatticeSumBounds

theorem absA : Formalism.HermitianLatticeCounting.LatticeSumBounds.AbsA := Formalism.HermitianLatticeCounting.P.absolute_value_bound
theorem wedgeHadamard : Formalism.HermitianLatticeCounting.LatticeSumBounds.WedgeHadamard := Formalism.HermitianLatticeCounting.P.wedge_hadamard_inequality
theorem cramerUpper : Formalism.HermitianLatticeCounting.LatticeSumBounds.CramerUpper := Formalism.HermitianLatticeCounting.P.leadingMinorColumnReplace
theorem gramHadamard : Formalism.HermitianLatticeCounting.LatticeSumBounds.GramHadamard := Formalism.HermitianLatticeCounting.P.gram_hadamard_inequality
theorem lemmaP : Formalism.HermitianLatticeCounting.LatticeSumBounds.LemmaP := Formalism.HermitianLatticeCounting.P.prodMaxInvLeSq
theorem packing : Formalism.HermitianLatticeCounting.LatticeSumBounds.Packing := Formalism.HermitianLatticeCounting.P.packing_bound
theorem traceLower : Formalism.HermitianLatticeCounting.LatticeSumBounds.TraceLower := Formalism.HermitianLatticeCounting.P.traceLowerBound
theorem classNumberBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.ClassNumberBound := Formalism.HermitianLatticeCounting.P.class_number_upper_bound
theorem c2a : Formalism.HermitianLatticeCounting.LatticeSumBounds.CardSubmodulesOfIndexLePow := Formalism.HermitianLatticeCounting.P.ideal_count_statement
theorem c2b : Formalism.HermitianLatticeCounting.LatticeSumBounds.CardSubmodulesAndLinearEquivBounds := Formalism.HermitianLatticeCounting.P.submodule_automorphism_count
theorem unipotentReduce : Formalism.HermitianLatticeCounting.LatticeSumBounds.UnipotentReduce := Formalism.HermitianLatticeCounting.P.unitriangularReduction
theorem leadingMinorInvariant : Formalism.HermitianLatticeCounting.LatticeSumBounds.LeadingMinorInvariant := Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant
theorem minorBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.MinorBound := Formalism.HermitianLatticeCounting.P.normMinorMulLe
theorem monomialMinor : Formalism.HermitianLatticeCounting.LatticeSumBounds.MonomialMinor := Formalism.HermitianLatticeCounting.P.normMinorMonomialLe
theorem omegaNorm : Formalism.HermitianLatticeCounting.LatticeSumBounds.OmegaNorm := Formalism.HermitianLatticeCounting.P.complementNormIdentity
theorem boxCount : Formalism.HermitianLatticeCounting.LatticeSumBounds.BoxCount := Formalism.HermitianLatticeCounting.P.box_count_alt
theorem kernelRowSpace : Formalism.HermitianLatticeCounting.LatticeSumBounds.KernelRowSpace := Formalism.HermitianLatticeCounting.P.cofactorVectorKernel
theorem cofVecAdjugate : Formalism.HermitianLatticeCounting.LatticeSumBounds.CofVecAdjugate := Formalism.HermitianLatticeCounting.P.adjugateLastColumnEqCofactor
theorem projQuotCard : Formalism.HermitianLatticeCounting.LatticeSumBounds.ProjQuotCard := Formalism.HermitianLatticeCounting.P.projective_quotient_card
theorem degFactorBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegFactorBound := Formalism.HermitianLatticeCounting.P.prodHyperbolicRatioSqLe
theorem deNonDegBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DeNonDegBound := Formalism.HermitianLatticeCounting.P.nondegenerateFactorBound
theorem deDegBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DeDegBound := Formalism.HermitianLatticeCounting.P.degenerateFactorBound
theorem nonDegRow : Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegRow := Formalism.HermitianLatticeCounting.P.nondegenerateRowBound
theorem degRow : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegRow := Formalism.HermitianLatticeCounting.P.degenerateRowBound
theorem nonDegSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegSum := Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe
theorem degSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegSum := Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe
theorem smallTerm : Formalism.HermitianLatticeCounting.LatticeSumBounds.SmallTerm := Formalism.HermitianLatticeCounting.P.prodMinLeOfProdRatio
theorem single_row_lattice_sum_bound : Formalism.HermitianLatticeCounting.LatticeSumBounds.SingleRowBound := Formalism.HermitianLatticeCounting.P.singleRowBound
theorem lattice_exp_sum_upper_bound : Formalism.HermitianLatticeCounting.LatticeSumBounds.ExpSumLe' := Formalism.HermitianLatticeCounting.P.expSumLe'
theorem gainSqrt : Formalism.HermitianLatticeCounting.LatticeSumBounds.GainSqrt := Formalism.HermitianLatticeCounting.P.invSqrtPowLeExp
theorem boxCountO : Formalism.HermitianLatticeCounting.LatticeSumBounds.BoxCountO := Formalism.HermitianLatticeCounting.P.box_count_big_O
theorem latticeSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.LatticeSum := Formalism.HermitianLatticeCounting.P.lattice_sum_alt
theorem homRestrictIndex : Formalism.HermitianLatticeCounting.LatticeSumBounds.HomRestrictIndex := Formalism.HermitianLatticeCounting.P.cardCokernelRestriction

theorem coveringO_of_transference (h : Formalism.HermitianLatticeCounting.LatticeSumBounds.Transference) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := Formalism.HermitianLatticeCounting.P.coveringO_of_transference h

end Formalism.HermitianLatticeCounting.Final.LatticeSumBounds
end

section -- merged from Formalism.FlagUnipotentLattices.IdealCountLeWAsm
namespace Formalism.HermitianLatticeCounting.Final.S6

theorem dualIndex : Formalism.HermitianLatticeCounting.S6.DualIndex := Formalism.HermitianLatticeCounting.P.dual_lattice_index

end Formalism.HermitianLatticeCounting.Final.S6
end

section -- merged from Formalism.FlagUnipotentLattices.ArithmeticIdentityEntries
section -- merged from Formalism.FlagUnipotentLattices.LatticeDeterminantIndexSq
open Module NumberField nonZeroDivisors Finset

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

def UnitsSquareIndex : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], (∀ w : InfinitePlace F, w.IsReal) →
    Nat.card ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range) = 2 ^ finrank ℚ F

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
end
end

section -- merged from Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegerGroupLocalParametrization
open Module NumberField nonZeroDivisors Finset

noncomputable section

namespace Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false

set_option backward.isDefEq.respectTransparency false in
open NumberField.Units in
theorem s5a4_torsion_real {F : Type} [Field F] [NumberField F]
    (hr : ∀ w : InfinitePlace F, w.IsReal) (x : (𝓞 F)ˣ) (hx : x ∈ torsion F) :
    x = 1 ∨ x = -1 := by
  by_cases hc : 2 < orderOf x
  · exfalso
    rw [← orderOf_units, ← orderOf_submonoid] at hc
    have h0 := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
      (IsPrimitiveRoot.orderOf ((x : 𝓞 F) : F))
    obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
    haveI : Nonempty {w : InfinitePlace F // w.IsReal} := ⟨⟨w0, hr w0⟩⟩
    rw [InfinitePlace.nrRealPlaces] at h0
    exact ((@Fintype.card_eq_zero_iff _ (_)).1 h0).false ⟨w0, hr w0⟩
  · have hc' : orderOf x ≤ 2 := not_lt.mp hc
    interval_cases hi : orderOf x
    · exact absurd ((CommGroup.mem_torsion x).1 hx) (orderOf_eq_zero_iff.mp hi)
    · exact Or.inl (orderOf_eq_one_iff.1 hi)
    · right
      rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, Units.val_neg, Units.val_one, hi]

open NumberField.Units in
theorem units_square_index : UnitsSquareIndex := by
  intro F _ _ hr
  classical
  set S : Subgroup (𝓞 F)ˣ := (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range with hS
  obtain ⟨θ, hθd⟩ : ∃ θ : (𝓞 F)ˣ →* Multiplicative (Fin (rank F) → ZMod 2), ∀ x, θ x =
      Multiplicative.ofAdd (fun i =>
        (((basisModTorsion F).repr (Additive.ofMul (x : (𝓞 F)ˣ ⧸ torsion F)) i : ℤ) : ZMod 2)) :=
   ⟨{ toFun := fun x => Multiplicative.ofAdd (fun i =>
        (((basisModTorsion F).repr (Additive.ofMul (x : (𝓞 F)ˣ ⧸ torsion F)) i : ℤ) : ZMod 2))
      map_one' := by
        simp only [QuotientGroup.mk_one, ofMul_one, map_zero, Finsupp.coe_zero, Pi.zero_apply,
          Int.cast_zero]; rfl
      map_mul' := by
        intro x y
        simp only [QuotientGroup.mk_mul, ofMul_mul, map_add (f := _), Finsupp.coe_add, Pi.add_apply,
          Int.cast_add]; rfl }, fun _ => rfl⟩
  have hθ : ∀ (x ζ : (𝓞 F)ˣ) (e : Fin (rank F) → ℤ), ζ ∈ torsion F →
      x = ζ * ∏ i, (fundSystem F i) ^ (e i) →
      θ x = Multiplicative.ofAdd (fun i => ((e i : ℤ) : ZMod 2)) := by
    intro x ζ e hζ hx
    have := fun_eq_repr F hζ hx
    rw [hθd, ← this]
  have hsurj : Function.Surjective θ := by
    intro v
    refine ⟨1 * ∏ i, (fundSystem F i) ^ (((Multiplicative.toAdd v i).val : ℕ) : ℤ), ?_⟩
    rw [hθ _ 1 _ (one_mem _) rfl]
    apply Multiplicative.toAdd.injective
    funext i
    simp
  have hsq : ∀ a : Multiplicative (Fin (rank F) → ZMod 2), a ^ 2 = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    funext i
    rw [sq]
    show Multiplicative.toAdd a i + Multiplicative.toAdd a i = 0
    exact CharTwo.add_self_eq_zero _
  have hker : θ.ker = S ⊔ torsion F := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨ζ, e⟩, hxe, _⟩ := exist_unique_eq_mul_prod F x
      simp only at hxe
      rw [MonoidHom.mem_ker, hθ x ζ e ζ.2 hxe] at hx
      have h2 : ∀ i, (2 : ℤ) ∣ e i := by
        intro i
        have := congrFun (congrArg Multiplicative.toAdd hx) i
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (e i) 2).mp this
      choose e' he' using h2
      have : x = (∏ i, (fundSystem F i) ^ (e' i)) ^ 2 * ζ := by
        rw [hxe, mul_comm, ← Finset.prod_pow]
        congr 1
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [he' i, mul_comm, zpow_mul]; rfl
      rw [this]
      exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ζ.2
    · apply sup_le
      · rintro _ ⟨y, rfl⟩
        rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hsq]
      · intro ζ hζ
        rw [MonoidHom.mem_ker, hθ ζ ζ (fun _ => 0) hζ (by simp)]
        simp; rfl
  have hST : S ⊓ torsion F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, hx⟩
    have hx' : y ^ 2 ∈ torsion F := hx
    have hy : y ∈ torsion F := by
      rw [torsion, CommGroup.mem_torsion] at hx' ⊢
      exact hx'.of_pow (by norm_num)
    show y ^ 2 ∈ (⊥ : Subgroup (𝓞 F)ˣ)
    rw [Subgroup.mem_bot]
    rcases s5a4_torsion_real hr y hy with h | h <;> simp [h]
  have hT : Nat.card (torsion F) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨-1, neg_one_mem_torsion⟩, ?_, ?_⟩
    · intro h
      have h1 : (1 : (𝓞 F)ˣ) = -1 := congrArg Subtype.val h
      have h2 : ((1 : 𝓞 F) : F) = -1 := by
        have := congrArg (fun u : (𝓞 F)ˣ => ((u : 𝓞 F) : F)) h1
        simpa using this
      norm_num at h2
    · apply Set.eq_univ_of_forall
      intro x
      rcases s5a4_torsion_real hr x.1 x.2 with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
  have hrank : rank F + 1 = finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 : InfinitePlace.nrComplexPlaces F = 0 := by
      rw [InfinitePlace.nrComplexPlaces, Fintype.card_eq_zero_iff]
      exact ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) (hr w.1)⟩
    have h4 : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    rw [rank]; omega
  show S.index = _
  rw [← Subgroup.relIndex_mul_index (le_sup_left : S ≤ S ⊔ torsion F), Subgroup.relIndex_sup_left,
    ← Subgroup.inf_relIndex_right, hST, Subgroup.relIndex_bot_left, hT, ← hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← hrank, pow_succ,
    mul_comm]



end Formalism.HermitianLatticeCounting.P
end
end

namespace Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure

theorem unitsSquareIndex : Formalism.HermitianLatticeCounting.LocalIntegralStructure.UnitsSquareIndex := Formalism.HermitianLatticeCounting.P.units_square_index

end Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
end

section -- merged from Formalism.FlagUnipotentLattices.StabiliserComplementDecomposition
namespace Formalism.HermitianLatticeCounting.ExpansionTerms

section PartA2
open Finset Real MeasureTheory NumberField

def MomentConstantBound : Prop :=
  ∀ C0 CA C1 : ℝ, 0 ≤ C0 → 0 ≤ CA → 0 ≤ C1 → ∃ C : ℝ,
    ∀ (r n : ℕ) (b bv ka T j q : ℝ), 2 ≤ b → 0 < ka → ka ≤ b ^ C0 → ka⁻¹ ≤ b ^ C0 → 1 ≤ T →
      T ≤ b ^ (C0 * (2 * (r : ℝ) + 2)) → 1 ≤ n → (n : ℝ) ≤ bv → bv ≤ b → 0 ≤ j → 0 ≤ q → j + q ≤ b →
      ((n : ℝ) * √(T * max ka ka⁻¹ ^ (2 * r) * b ^ CA) * (6 * bv) ^ (2 * r + 2)) *
          max 1 (C1 * (n : ℝ) ^ 2 * (b + j + q) / ka) ^ r ≤
        b ^ (C * (2 * (r : ℝ) + 2)) * (1 + 1 / ka) ^ (2 * r + 2)

end PartA2

section PartB2
open Finset Matrix Polynomial
open scoped ComplexConjugate TensorProduct

def LeadingMinorCodingsAgree : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (Z : Matrix (Fin d) (Fin d) R) (l : ℕ) (h : l ≤ d),
    leadingPrincipalMinor Z l = LeadingPrincipalMinor Z l h

def DminBridge : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (l : Fin (r + 2)), Formalism.QuantumDeterminants.Dmin k r z z' g l = leadingPrincipalMinor (Formalism.QuantumDeterminants.Zhat k r z z' g) (l : ℕ)

def GfLeD : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    0 ≤ Formalism.QuantumDeterminants.Tz k r z → 0 ≤ Formalism.QuantumDeterminants.Tz k r z' →
      Formalism.QuantumDeterminants.Gf k r z z' g ≤ ‖Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1))‖ ^ 2

noncomputable def formalDeterminantVector {V : Type*} [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) {r : ℕ}
    (y f' : Fin (r + 1) → V) : V :=
  ∑ a, (Matrix.of fun a b => h (y a) (f' b)).adjugate (Fin.last r) a • y a

def DualVectorOrthogonal : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (r : ℕ) (y f' : Fin (r + 1) → V)
    (b : Fin (r + 1)),
    h (formalDeterminantVector h y f') (f' b) = if b = Fin.last r then (Matrix.of fun a b => h (y a) (f' b)).det else 0

noncomputable def formalDeterminantVectorOnGroup (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Fin (2 * r + k + 1) → ℂ :=
  ∑ a, (Matrix.of fun a b => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a)
    (Formalism.QuantumDeterminants.fvec k r z' b)).adjugate (Fin.last r) a • (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a)

noncomputable def N3om (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if r ≤ i.val ∧ i.val ≤ r + k then
    formalDeterminantVectorOnGroup k r z z' g i +
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (formalDeterminantVectorOnGroup k r z z' g) z' / (Formalism.QuantumDeterminants.Tz k r z' : ℂ) * z' i
  else 0

def OrthogonalComplementDecomposition : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    Formalism.QuantumDeterminants.Tz k r z' ≠ 0 → ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Formalism.QuantumDeterminants.inWb k r (N3om k r z z' g) ∧
      (∀ b, Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (N3om k r z z' g) (Formalism.QuantumDeterminants.fvec k r z' b) = 0) ∧
      ∃ co : Fin (r + 1) → ℂ, formalDeterminantVectorOnGroup k r z z' g = (∑ b, co b • Formalism.QuantumDeterminants.fvec k r z' b) + N3om k r z z' g

def DualVectorUnipotentInvariant : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ n' ∈ Formalism.QuantumDeterminants.Nset k r,
      N3om k r z z' (n * g * n') = N3om k r z z' g

def DualVectorEquivariant : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset k r z',
      N3om k r z z' (h * g * h') = h'⁻¹ *ᵥ N3om k r z z' g

def DualVectorNormOnGroup : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z' → ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (N3om k r z z' g) (N3om k r z z' g) =
        ((Formalism.QuantumDeterminants.Gf k r z z' g / Formalism.QuantumDeterminants.Tz k r z' : ℝ) : ℂ) ∧
      (0 ≤ Formalism.QuantumDeterminants.Tz k r z →
        (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (N3om k r z z' g) (N3om k r z z' g)).re ≤
          ‖Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1))‖ ^ 2 / Formalism.QuantumDeterminants.Tz k r z')

noncomputable def rankTwoSkewOperator {V : Type*} [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (e v x : V) : V :=
  h x v • e - h x e • v

def RankTwoSkewInNilradical : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ x y, h y x = conj (h x y)) →
    ∀ (r : ℕ) (f : Fin (r + 1) → V) (T : ℝ),
      (∀ a b, h (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -(T : ℂ) else 0) →
      ∀ (a : Fin r) (e v : V), e - f a.castSucc ∈ Submodule.span ℂ (f '' {b | b < a.castSucc}) →
        (∀ b, b ≤ a.castSucc → h (f b) v = 0) →
        e ∈ Submodule.span ℂ (f '' {b | b ≤ a.castSucc}) ∧
        (∀ x, (∀ b : Fin r, h x (f b.castSucc) = 0) → rankTwoSkewOperator h e v x = h x v • e) ∧
        (∀ b, rankTwoSkewOperator h e v (f b) = h (f b) v • e) ∧
        (∀ b, b ≤ a.castSucc → rankTwoSkewOperator h e v (f b) = 0) ∧
        rankTwoSkewOperator h e v (f a.succ) - h (f a.succ) v • f a.castSucc ∈ Submodule.span ℂ (f '' {b | b < a.castSucc}) ∧
        rankTwoSkewOperator h e v e = 0 ∧ rankTwoSkewOperator h e v v = h v v • e

noncomputable def rankTwoSkewMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (e v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    Formalism.QuantumDeterminants.herm H (Pi.single j 1) v * e i - Formalism.QuantumDeterminants.herm H (Pi.single j 1) e * v i

def RankTwoSkewMatrixApply : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (e v x : Fin n → ℂ),
    rankTwoSkewMatrix H e v *ᵥ x = Formalism.QuantumDeterminants.herm H x v • e - Formalism.QuantumDeterminants.herm H x e • v

def RankTwoSkewConjugation : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), IsUnit H.det → ∀ g ∈ Formalism.QuantumDeterminants.UH H, ∀ e v : Fin n → ℂ,
    g⁻¹ * rankTwoSkewMatrix H e v * g = rankTwoSkewMatrix H (g⁻¹ *ᵥ e) (g⁻¹ *ᵥ v)

noncomputable def nilpotentExpSquare {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (e v : ι → ℂ) (t : ℝ) :
    Matrix ι ι ℂ :=
  1 + (t : ℂ) • rankTwoSkewMatrix H e v + ((t : ℂ) ^ 2 / 2) • (rankTwoSkewMatrix H e v * rankTwoSkewMatrix H e v)

def RankTwoNilpotentGroup : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    ∀ (a : Fin r) (e v : Fin (2 * r + k + 1) → ℂ),
      e - Formalism.QuantumDeterminants.fvec k r z a.castSucc ∈
        Submodule.span ℂ (Formalism.QuantumDeterminants.fvec k r z '' {b | b < a.castSucc}) →
      (∀ b, b ≤ a.castSucc → Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) v = 0) →
      rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e v * rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e v * rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e v = 0 ∧
      (∀ s t : ℝ, nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v (s + t) =
        nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v s * nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t) ∧
      ∀ t : ℝ, nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t ∈ Formalism.QuantumDeterminants.Nset k r ∧
        Formalism.QuantumDeterminants.ell k r z (nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t) =
          (t : ℂ) * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z a.succ) v

def CharacterDerivativeNorm : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    ∀ (a : Fin r) (e v : Fin (2 * r + k + 1) → ℂ) (ka l : ℝ),
      e - Formalism.QuantumDeterminants.fvec k r z a.castSucc ∈
        Submodule.span ℂ (Formalism.QuantumDeterminants.fvec k r z '' {b | b < a.castSucc}) →
      (∀ b, b ≤ a.castSucc → Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) v = 0) →
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z a.succ) v = -Complex.I * (l : ℂ) →
      ∀ t : ℝ, Formalism.QuantumDeterminants.psi k r z ((ka : ℂ) * Formalism.QuantumDeterminants.cStd) (nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t) =
        Complex.exp (-(2 * (ka : ℂ) * (l : ℂ) * (t : ℂ)) * Complex.I)

def MajorantOrthogonalComponent : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (y : Fin n → V) (a : Fin n),
    ∃ u : V, u - y a ∈ Submodule.span ℂ (y '' {b | b < a}) ∧ (∀ b, b < a → inner ℂ u (y b) = 0) ∧
      ‖u‖ = majorantDistance y a ∧ inner ℂ u (y a) = ((‖u‖ ^ 2 : ℝ) : ℂ)

def SkewVectorChoice : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V), IsSelfAdjointInvolution θ →
    ∀ (r : ℕ) (y : Fin (r + 1) → V) (a : Fin r), majorantDistance y a.succ ≠ 0 →
      ∃ e' v' : V, e' - y a.castSucc ∈ Submodule.span ℂ (y '' {b | b < a.castSucc}) ∧
        ‖e'‖ = majorantDistance y a.castSucc ∧ ‖v'‖ = 1 ∧ (∀ b, b ≤ a.castSucc → majorantHermitianForm θ (y b) v' = 0) ∧
        majorantHermitianForm θ (y a.succ) v' = -Complex.I * (majorantDistance y a.succ : ℂ)

def MomentPointwiseBound : Prop :=
  ∀ (V ι : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (c : ι → ℂ) (x : ι → V) (P : V) (d : ℂ)
    (ka la la1 : ℝ), 0 < la → ‖d‖ = 2 * ka * la1 → d • P = ∑ i, c i • x i → ∑ i, ‖c i‖ ^ 2 ≤ 4 * la ^ 2 →
      (ka * la1 / la) ^ 2 * ‖P‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2

end PartB2

section PartC2
open Finset

end PartC2

section PartD2
open Finset

end PartD2

end Formalism.HermitianLatticeCounting.ExpansionTerms
end

section -- merged from Formalism.FlagUnipotentLattices.AutBoundOfMinkowskiBound
namespace Formalism.HermitianLatticeCounting.Final.S6

theorem nFJZero : Formalism.HermitianLatticeCounting.S6.NFJZero := by
  first
    | exact Formalism.HermitianLatticeCounting.P.normalFormZero
    | exact Formalism.HermitianLatticeCounting.P.S6e.normalFormZero

theorem normalForm : Formalism.HermitianLatticeCounting.S6.NormalForm := by
  first
    | exact Formalism.HermitianLatticeCounting.P.existsNormalForm
    | exact Formalism.HermitianLatticeCounting.P.S6e.existsNormalForm

theorem normSgBound : Formalism.HermitianLatticeCounting.S6.NormSgBound := by
  first
    | exact Formalism.HermitianLatticeCounting.P.norm_singular_value_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.norm_singular_value_bound

theorem finalSum : Formalism.HermitianLatticeCounting.S6.FinalSum := by
  first
    | exact Formalism.HermitianLatticeCounting.P.final_sum_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.final_sum_bound

end Formalism.HermitianLatticeCounting.Final.S6
end
