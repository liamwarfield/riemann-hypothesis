module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUniqueComplexPointLiftClopenCover
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.existsUnique_complexPoint_lift_clopen_cover :
    ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (M : Type) [Fintype M] (W : M → Y.Opens), (∀ i j, i ≠ j → W i ⊓ W j = ⊥) → iSup W = ⊤ → ∀ y : CxPts s' (RingHom.id ℂ), ∃! m : M, ∃! y' : CxPts ((W m).ι ≫ s') (RingHom.id ℂ), y'.1 ≫ (W m).ι = y.1 := by
  intro Y s' M _ W hd hc y
  let x0 : (Sp ℂ : Scheme.{0}) := IsLocalRing.closedPoint ℂ
  have hone : ∀ a : (Sp ℂ : Scheme.{0}), a = x0 := fun a => Subsingleton.elim a x0
  obtain ⟨m, hm⟩ : ∃ m, y.1 x0 ∈ W m := by
    have h : y.1 x0 ∈ iSup W := by
      rw [hc]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h
  have hr : Set.range y.1 ⊆ Set.range (W m).ι := by
    rintro _ ⟨a, rfl⟩
    rw [hone a, Scheme.Opens.range_ι]
    exact hm
  refine ⟨m, ?_, ?_⟩
  · refine ⟨⟨IsOpenImmersion.lift (W m).ι y.1 hr, ?_⟩, ?_, ?_⟩
    · rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact y.2
    · exact IsOpenImmersion.lift_fac _ _ _
    · intro z hz
      apply Subtype.ext
      rw [← cancel_mono (W m).ι, hz]
      exact (IsOpenImmersion.lift_fac _ _ _).symm
  · rintro m' ⟨z, hz, -⟩
    by_contra hne
    have h1 : y.1 x0 ∈ W m' := by
      have hz' : z.1 ≫ (W m').ι = y.1 := hz
      rw [← hz', Scheme.Hom.comp_apply]
      exact (z.1 x0).2
    have h2 : y.1 x0 ∈ W m' ⊓ W m := ⟨h1, hm⟩
    rw [hd m' m hne] at h2
    exact h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CompactSpaceOfProjectiveAndOfFinite
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem UpperTheory.Cb.adjoin_degree_zero_variables_eq_top (N : ℕ) :
    Algebra.adjoin (↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))
      (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0 :=
      MvPolynomial.isHomogeneous_C _ a
    exact Subalgebra.algebraMap_mem _ (⟨_, hC⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p i hp =>
    exact Subalgebra.mul_mem _ (hp trivial) (Algebra.subset_adjoin ⟨i, rfl⟩)

private theorem UpperTheory.Cb.compactSpace_projective_space (N : ℕ) : CompactSpace (PSpace ℂ N) := by
  have hX : ∀ i : Fin (N + 1), (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 1 :=
    fun i => MvPolynomial.isHomogeneous_X ℂ i
  have hcov := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ) (fun i => ⟨1, hX i⟩)
    (UpperTheory.Cb.adjoin_degree_zero_variables_eq_top N)
  refine ⟨?_⟩
  have huniv : (Set.univ : Set (PSpace ℂ N)) =
      ⋃ i, ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
        (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) : (PSpace ℂ N).Opens) : Set (PSpace ℂ N)) := by
    have := congrArg (fun U : (PSpace ℂ N).Opens => (U : Set (PSpace ℂ N))) hcov
    simpa using this.symm
  rw [huniv]
  exact isCompact_iUnion fun i =>
    (Proj.isAffineOpen_basicOpen _ _ (hX i) Nat.one_pos).isCompact

theorem UpperTheory.Cb.compactSpace_of_projective_and_of_finite :
    (∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ), IsProjOver s → CompactSpace Z) ∧ ∀ (Y Z : Scheme.{0}) (c : Y ⟶ Z), IsFinite c → CompactSpace Z → CompactSpace Y := by
  refine ⟨?_, ?_⟩
  · rintro Z s ⟨N, i, hi, -⟩
    haveI := UpperTheory.Cb.compactSpace_projective_space N
    exact QuasiCompact.compactSpace_of_compactSpace i
  · intro Y Z c hc hZ
    exact QuasiCompact.compactSpace_of_compactSpace c
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsIntegralClopenDecompositionOfSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralClopenDecompositionOfSmooth
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmoothComponents

open Topology TopologicalSpace

theorem irreducibleComponent_eq_closure (Z : Scheme.{0})
    (hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) {C : Set Z} (hC : C ∈ irreducibleComponents Z)
    {x : Z} (hx : x ∈ C) :
    haveI := hdom x
    C = closure {Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))} := by
  haveI := hdom x
  set ξ := Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hgen : IsGenericPoint hC.1.genericPoint C := by
    simpa [hCc.closure_eq] using hC.1.isGenericPoint_genericPoint_closure
  have hηx : hC.1.genericPoint ⤳ x := hgen.specializes hx
  have hmem : hC.1.genericPoint ∈ Set.range (Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hηx
  obtain ⟨p, hp⟩ := hmem
  have hξη : ξ ⤳ hC.1.genericPoint := by
    rw [← hp]
    exact ((genericPoint_spec (Spec (Z.presheaf.stalk x))).specializes trivial).map
      (Z.fromSpecStalk x).continuous
  have hsub : C ⊆ closure {ξ} := by
    rw [← hgen.def]
    exact closure_minimal (by simpa using specializes_iff_mem_closure.mp hξη) isClosed_closure
  have hirr : IsIrreducible (closure {ξ}) := isIrreducible_singleton.closure
  exact le_antisymm hsub (hC.2 hirr hsub)

end GlobalTheory.SmoothComponents

namespace GlobalTheory.SmoothComponents

open Topology TopologicalSpace

theorem main : ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]
    [CompactSpace Z], ∃ (J : Type) (_ : Fintype J) (V : J → Z.Opens),
      (∀ i j, i ≠ j → V i ⊓ V j = ⊥) ∧ iSup V = ⊤ ∧ ∀ j, IsIntegral (V j).toScheme := by
  intro Z s d _ _
  have hs : Smooth s := SmoothOfRelativeDimension.smooth d s
  obtain ⟨hred, -, hln⟩ :=
    isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Z s hs
  have hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x ↦
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (isDomain_and_isIntegrallyClosed_stalk_Sp ℂ) x).1
  haveI : IsNoetherian Z := ⟨⟩
  have hfin : (irreducibleComponents Z).Finite := finite_irreducibleComponents_of_isNoetherian
  have disj : ∀ C ∈ irreducibleComponents Z, ∀ D ∈ irreducibleComponents Z, C ≠ D →
      Disjoint C D := by
    intro C hC D hD hne
    rw [Set.disjoint_left]
    intro x hxC hxD
    exact hne ((irreducibleComponent_eq_closure Z hdom hC hxC).trans
      (irreducibleComponent_eq_closure Z hdom hD hxD).symm)
  have cover : ∀ x : Z, ∃ C ∈ irreducibleComponents Z, x ∈ C := fun x ↦
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
      mem_irreducibleComponent⟩
  have hopen : ∀ C ∈ irreducibleComponents Z, IsOpen C := by
    intro C hC
    have hc : Cᶜ = ⋃ D ∈ irreducibleComponents Z \ {C}, D := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff,
        exists_prop]
      constructor
      · intro hx
        obtain ⟨D, hD, hxD⟩ := cover x
        exact ⟨D, ⟨hD, fun h ↦ hx (h ▸ hxD)⟩, hxD⟩
      · rintro ⟨D, ⟨hD, hne⟩, hxD⟩ hxC
        exact Set.disjoint_left.mp (disj D hD C hC hne) hxD hxC
    rw [← isClosed_compl_iff, hc]
    exact (hfin.subset Set.diff_subset).isClosed_biUnion fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1
  letI : Fintype (irreducibleComponents Z) := hfin.fintype
  refine ⟨irreducibleComponents Z, inferInstance, fun C ↦ ⟨C.1, hopen C.1 C.2⟩, ?_, ?_, ?_⟩
  · intro i j hij
    apply Opens.ext
    simp only [Opens.coe_inf, Opens.coe_bot]
    exact Set.disjoint_iff_inter_eq_empty.mp (disj i.1 i.2 j.1 j.2 fun h ↦ hij (Subtype.ext h))
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    rw [Opens.mem_iSup]
    obtain ⟨C, hC, hxC⟩ := cover x
    exact ⟨⟨C, hC⟩, hxC⟩
  · intro C
    have hirr : IsIrreducible C.1 := C.2.1
    haveI : IrreducibleSpace (C.1 : Set Z) := Subtype.irreducibleSpace hirr
    let U : Z.Opens := ⟨C.1, hopen C.1 C.2⟩
    change IsIntegral U.toScheme
    haveI : IrreducibleSpace U.toScheme := this
    exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.SmoothComponents
end
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.exists_integral_clopen_decomposition_of_smooth :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s] [CompactSpace Z], ∃ (J : Type) (_ : Fintype J) (V : J → Z.Opens), (∀ i j, i ≠ j → V i ⊓ V j = ⊥) ∧ iSup V = ⊤ ∧ ∀ j, IsIntegral (V j).toScheme := by
  first | exact @GlobalTheory.SmoothComponents.main | exact GlobalTheory.SmoothComponents.main
end
