module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLocalExtResidueFieldSeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLocalExtResidueFieldSeparable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_etale_of_isSeparable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R],
    AdmBase R (maximalIdeal R) → ∀ (k' : Type) [Field k'] [Algebra (ResidueField R) k']
    [Module.Finite (ResidueField R) k'] [Algebra.IsSeparable (ResidueField R) k'],
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R')
      (σ : k' →+* ResidueField R'), FinExt ρ ∧ ρ.Etale ∧
      σ.comp ((algebraMap (ResidueField R) k').comp (residue R)) = (residue R').comp ρ := by
  intro R _ _ _ hR k' _ _ _ _
  obtain ⟨hN, -, hIC, hC⟩ := hR
  haveI := hN; haveI := hIC; haveI := hC
  obtain ⟨A, _, _, hfin, het, hloc, ⟨ε⟩⟩ := GlobalTheory.exists_etale_lift_of_isSeparable R k'
  haveI : IsLocalHom (algebraMap R A) :=
    ((local_hom_tfae (algebraMap R A)).out 1 5).mpr (comap_eq_maximalIdeal_of_finite _)
  have hm : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨hD, hI⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale R (maximalIdeal A)
    (Localization.AtPrime (maximalIdeal A))
  let e := IsLocalization.atUnits A (maximalIdeal A).primeCompl
    (S := Localization.AtPrime (maximalIdeal A)) (fun y hy => by
      rw [IsUnit.mem_submonoid_iff]
      by_contra h
      exact hy ((IsLocalRing.mem_maximalIdeal y).mpr h))
  haveI : IsDomain A := e.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  haveI : IsNoetherian R A := inferInstance
  haveI : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  let g2 : ResidueField R ⊗[R] A →ₐ[R] ResidueField A :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField A))
      (IsScalarTower.toAlgHom R A (ResidueField A)) (fun _ _ => Commute.all _ _)
  let σ : k' →+* ResidueField A := g2.toRingHom.comp ε.symm.toRingHom
  refine ⟨A, inferInstance, inferInstance, inferInstance, algebraMap R A, σ,
    ⟨⟨inferInstance, inferInstance, inferInstance, ?_⟩, ?_, RingHom.finite_algebraMap.mpr hfin⟩,
    RingHom.etale_algebraMap.mpr het, ?_⟩
  · have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) A
    rwa [hm] at this
  · haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing
    intro x y hxy
    rw [← sub_eq_zero]
    have h0 : (x - y) • (1 : A) = 0 := by
      rw [Algebra.smul_def, _root_.mul_one, map_sub, hxy, sub_self]
    exact (smul_eq_zero.mp h0).resolve_right one_ne_zero
  · ext r
    simp only [RingHom.comp_apply, σ, AlgEquiv.coe_toRingEquiv, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, AlgHom.toRingHom_eq_coe]
    change g2 (algebraMap (ResidueField R) (ResidueField R ⊗[R] A) (residue R r)) = _
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp [g2]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLocalExtResidueFieldSeparableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_local_ext_residueField_separable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (k' : Type) [Field k'] [Algebra (ResidueField R) k'] [Module.Finite (ResidueField R) k'] [Algebra.IsSeparable (ResidueField R) k'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : k' →+* ResidueField R'), FinExt ρ ∧ ρ.Etale ∧ σ.comp ((algebraMap (ResidueField R) k').comp (residue R)) = (residue R').comp ρ := by
  first | exact @GlobalTheory.Mum.exists_finExt_etale_of_isSeparable | exact GlobalTheory.Mum.exists_finExt_etale_of_isSeparable | (intros; apply GlobalTheory.Mum.exists_finExt_etale_of_isSeparable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointSmoothLocalRingOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointSmoothLocalRingOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_separable_point_of_smooth : ∀ (R : Type) [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom →
    ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra (ResidueField R) k') (_ : Module.Finite (ResidueField R) k')
      (_ : Algebra.IsSeparable (ResidueField R) k') (x : Sp k' ⟶ U.left),
      x ≫ U.hom = spMap ((algebraMap (ResidueField R) k').comp (residue R)) ∧ Set.range x ⊆ O := by
  intro R _ _ U hU O hO
  obtain ⟨W, _, _, _, ε, y, hy, hyO⟩ := GlobalTheory.exists_etale_point_of_smooth U.hom R
    (SeparableClosure (ResidueField R)) (𝟙 _) O (by obtain ⟨u, hu, e⟩ := hO; exact ⟨u, hu, e⟩)
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R W).FG)
  let k' : IntermediateField (ResidueField R) (SeparableClosure (ResidueField R)) :=
    IntermediateField.adjoin (ResidueField R) (ε '' (s : Set W))
  have hfin : FiniteDimensional (ResidueField R) k' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hsep : Algebra.IsSeparable (ResidueField R) k' := Algebra.IsSeparable.of_algHom _ _ k'.val
  have hle : Algebra.adjoin R (s : Set W) ≤ (k'.toSubalgebra.restrictScalars R).comap ε :=
    Algebra.adjoin_le fun w hw => IntermediateField.subset_adjoin _ _ ⟨w, hw, rfl⟩
  have hmem : ∀ w, ε w ∈ k' := fun w => hle (hs ▸ Algebra.mem_top)
  let g : W →+* k' := ε.toRingHom.codRestrict k' hmem
  set_option synthInstance.maxHeartbeats 200000 in
    refine ⟨k', inferInstance, inferInstance, hfin, hsep, Spec.map (CommRingCat.ofHom g) ≫ y, ?_, ?_⟩
  · rw [Category.assoc, hy, Category.comp_id, ← Spec.map_comp]
    congr 2
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    congr 1
    change ε (algebraMap R W r) = algebraMap (ResidueField R) _ (residue R r)
    rw [ε.commutes]
    exact IsScalarTower.algebraMap_apply R (ResidueField R) _ r
  · rintro _ ⟨z, rfl⟩
    exact hyO ⟨_, rfl⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointSmoothLocalRingOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separable_point_smooth_localRing_open : ∀ (R : Type) [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) → ∃ (k' : Type) (_ : Field k') (_ : Algebra (ResidueField R) k') (_ : Module.Finite (ResidueField R) k') (_ : Algebra.IsSeparable (ResidueField R) k') (x : Sp k' ⟶ U.left), x ≫ U.hom = spMap ((algebraMap (ResidueField R) k').comp (residue R)) ∧ Set.range x ⊆ O := by
  first | exact @GlobalTheory.Mum.exists_separable_point_of_smooth | exact GlobalTheory.Mum.exists_separable_point_of_smooth | (intros; apply GlobalTheory.Mum.exists_separable_point_of_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finEtale_section_of_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (a : Sp R' ⟶ U.left), FinExt ρ ∧ ρ.Etale ∧ a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  intro R _ _ _ hR U hU O hO
  obtain ⟨k', _, _, _, _, x, hx, hxO⟩ := GlobalTheory.T.exists_separable_point_smooth_localRing_open R U hU O hO
  obtain ⟨R', _, _, _, ρ, σ, hF, hE, hσ⟩ := GlobalTheory.T.exists_finiteEtale_local_ext_residueField_separable R hR k'
  have hN : IsNoetherianRing R' := hF.1.1
  have hc : IsAdicComplete (maximalIdeal R') R' := hF.1.2.2.2
  have hx₀ : (spMap σ ≫ x) ≫ U.hom = spMap ((residue R').comp ρ) := by
    rw [Category.assoc, hx, ← hσ, ← Spec.map_comp]; rfl
  have hr : Set.range (spMap σ ≫ x) ⊆ O := by
    rintro _ ⟨p, rfl⟩; exact hxO ⟨_, rfl⟩
  obtain ⟨a, ha, haO⟩ := GlobalTheory.T.exists_lift_residueFieldPoint_smooth_completeLocal R R' hc ρ U hU (spMap σ ≫ x) hx₀ O hr
  exact ⟨R', _, inferInstance, inferInstance, ρ, a, hF, hE, ha, haO⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (a : Sp R' ⟶ U.left), FinExt ρ ∧ ρ.Etale ∧ a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  first | exact @GlobalTheory.Mum.exists_finEtale_section_of_smooth | exact GlobalTheory.Mum.exists_finEtale_section_of_smooth | (intros; apply GlobalTheory.Mum.exists_finEtale_section_of_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisUniformiserConsResidualLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisUniformiserConsResidualLifts
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

open IsLocalRing Polynomial

theorem eq_zero_of_eval_mem_maximalIdeal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {f : R} (hf0 : f ≠ 0) (hfm : f ∈ maximalIdeal R) (p : R[X])
    (hu : ∀ i, p.coeff i ≠ 0 → IsUnit (p.coeff i)) (he : p.eval f = 0) : p = 0 := by
  suffices h : ∀ d (p : R[X]), p.natDegree = d → (∀ i, p.coeff i ≠ 0 → IsUnit (p.coeff i)) →
      p.eval f = 0 → p = 0 from h _ p rfl hu he
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro p hd hu he
  have hsplit := X_mul_divX_add p
  have h2 : p.eval f = f * (divX p).eval f + p.coeff 0 := by
    have h3 := congrArg (Polynomial.eval f) hsplit
    simp only [eval_add, eval_mul, eval_X, eval_C] at h3
    exact h3.symm
  have he' : f * (divX p).eval f + p.coeff 0 = 0 := by rw [← h2]; exact he
  have hc0 : p.coeff 0 = 0 := by
    by_contra hc
    have hmem : p.coeff 0 ∈ maximalIdeal R := by
      have e : p.coeff 0 = -(f * (divX p).eval f) := by linear_combination he'
      rw [e]
      exact (maximalIdeal R).neg_mem ((maximalIdeal R).mul_mem_right _ hfm)
    exact (mem_maximalIdeal _).1 hmem (hu 0 hc)
  have hdv : (divX p).eval f = 0 := by
    rw [hc0, add_zero] at he'
    exact (mul_eq_zero.1 he').resolve_left hf0
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [eq_C_of_natDegree_eq_zero (hd.trans hd0), hc0, C_0]
  · have h0 : divX p = 0 := ih (d - 1) (by omega) (divX p)
      (by rw [natDegree_divX_eq_natDegree_tsub_one, hd])
      (fun i hi => by rw [coeff_divX] at hi ⊢; exact hu _ hi) hdv
    rw [← hsplit, h0, hc0, mul_zero, C_0, add_zero]

theorem trBasis_uniformiser_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (n : ℕ) (S : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring),
    Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f →
    TrBasis cK (fun i => ψ (w i)) →
    TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) ∧
      (fun ω => @dite ℤ (∃ a, S.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 ∧
      S.ord (f : L) = 1 ∧ ∀ g : S.ring, ψ g ≠ 0 → S.ord (g : L) = 0 := by
  intro L K _ _ cL cK n S ψ f w hψ hc hf hwK
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hunit : ∀ g : S.ring, ψ g ≠ 0 → IsUnit g := by
    intro g hg
    by_contra hu
    exact hg (by rw [← RingHom.mem_ker, hker]; exact hu)
  have hwu : ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) w P) := by
    intro P hP
    apply hunit
    rw [MvPolynomial.hom_eval₂, hcomp]
    intro h0
    have hind : AlgebraicIndependent ℂ (fun i => ψ (w i)) := hwK.1
    exact hP ((algebraicIndependent_iff.1 hind) P h0)

  obtain ⟨m, z, b, -, -⟩ := exists_basis_kaehler_uniformiser ℂ hf
  have hL : Algebra.trdeg ℂ L = (m + 1 : ℕ) := trdeg_eq_of_basis_kaehler ℂ L b
  have hR := trdeg_residueField_of_trdeg ℂ S.ring L hL
  simp only [add_tsub_cancel_right] at hR
  have hK : Algebra.trdeg ℂ K = n := by
    have := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hwK
    rw [Cardinal.mk_fin] at this
    exact this.symm
  have hmn : m ≤ n := by
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℂ (ResidueField S.ring)
    let res := IsLocalRing.residue S.ring
    let lift : s → S.ring := fun i => Function.surjInv IsLocalRing.residue_surjective (i : _)
    have hlift : res ∘ lift = Subtype.val := funext fun i =>
      Function.surjInv_eq IsLocalRing.residue_surjective _
    have hg : AlgebraicIndependent ℂ (fun i => ψ (lift i)) := by
      refine algebraicIndependent_iff.2 fun P hP => ?_
      by_contra hne
      have hu : IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) lift P) := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, MvPolynomial.eval₂_comp_left]
        change MvPolynomial.aeval (res ∘ lift) P ≠ 0
        rw [hlift]
        exact fun h0 => hne (algebraicIndependent_iff.1 hs.1 P h0)
      apply (hu.map ψ).ne_zero
      rw [MvPolynomial.hom_eval₂, hcomp]
      exact hP
    have h1 := hg.cardinalMk_le_trdeg
    rw [hs.cardinalMk_eq_trdeg, hR, hK] at h1
    exact_mod_cast h1

  have hsplit : ∀ P : MvPolynomial (Fin (n + 1)) ℂ,
      MvPolynomial.eval₂ (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) P =
        Polynomial.eval f (Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) w)
          (MvPolynomial.finSuccEquiv ℂ n P)) := by
    intro P
    have hrh : MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) =
        (Polynomial.evalRingHom f).comp
          ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) w)).comp
            (MvPolynomial.finSuccEquiv ℂ n : MvPolynomial (Fin (n + 1)) ℂ →+* _)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [MvPolynomial.finSuccEquiv_apply]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    exact RingHom.congr_fun hrh P
  have hcoe : ∀ P : MvPolynomial (Fin (n + 1)) ℂ,
      MvPolynomial.aeval (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) P =
        ((MvPolynomial.eval₂ (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) P :
          S.ring) : L) := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ S.ring) S.ring.subtype
      (Fin.cons f w : Fin (n + 1) → S.ring)
    rw [ValuationSubring.subtype_apply] at h
    rw [h, MvPolynomial.aeval_def]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hind : AlgebraicIndependent ℂ (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    rw [hcoe, ZeroMemClass.coe_eq_zero, hsplit] at hP
    set Q := MvPolynomial.finSuccEquiv ℂ n P with hQ
    have hq := eq_zero_of_eval_mem_maximalIdeal hf.ne_zero hf.not_isUnit _ (fun i hi => by
      rw [Polynomial.coeff_map] at hi ⊢
      refine hwu _ fun h0 => hi ?_
      rw [h0, map_zero]) hP
    have hQ0 : Q = 0 := by
      apply Polynomial.ext
      intro i
      rw [Polynomial.coeff_zero]
      by_contra h0
      apply (hwu _ h0).ne_zero
      have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hq
      simpa [Polynomial.coeff_map] using this
    exact (MvPolynomial.finSuccEquiv ℂ n).injective (by rw [← hQ, hQ0, map_zero])
  have htr : TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := by
    unfold TrBasis
    refine hind.isTranscendenceBasis_of_trdeg_le_of_finite ?_
    rw [hL, Cardinal.mk_fin]
    exact_mod_cast (by omega : m + 1 ≤ n + 1)
  refine ⟨htr, ?_, S.ord_irreducible hf, fun g hg => S.ord_eq_zero (hunit g hg)⟩
  exact GlobalTheory.formOrd_dForm_uniformiser_cons cL n S f w hf hwu ⟨_, htr⟩

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisUniformiserConsResidualLiftsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transcendenceBasis_uniformiser_cons_residual_lifts : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (S : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) ∧ (fun ω => @dite ℤ (∃ a, S.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 ∧ S.ord (f : L) = 1 ∧ ∀ g : S.ring, ψ g ≠ 0 → S.ord (g : L) = 0 := by
  first | exact @GlobalTheory.FieldPair.trBasis_uniformiser_cons | exact GlobalTheory.FieldPair.trBasis_uniformiser_cons | (intros; apply GlobalTheory.FieldPair.trBasis_uniformiser_cons <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutomorphismActsOnDeeperLevelLabels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutomorphismActsOnDeeperLevelLabels
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalAct


open MonObj in
theorem exists_mulEquiv_points {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {X : Scheme.{0}} (t : X ⟶ S') (g : X ⟶ S)
    (hg : t ≫ f = g) :
    ∃ e : (Over.mk t ⟶ G') ≃* (Over.mk g ⟶ G), ∀ z, (e z).left = z.left ≫ F := by
  subst hg
  let m : (Over.mk t ⟶ G') → (Over.mk (t ≫ f) ⟶ G) := fun z => Over.homMk (z.left ≫ F) (by
    have h : z.left ≫ G'.hom = t := Over.w z
    show (z.left ≫ F) ≫ G.hom = t ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, h])
  have hm : ∀ z, (m z).left = z.left ≫ F := fun _ => rfl
  have hmul : ∀ x y, m (x * y) = m x * m y := fun x y =>
    Over.OverMorphism.ext ((hm _).trans (hF.2 (Over.mk t) x y (m x) (m y) (hm x) (hm y)).symm)
  have hinj : Function.Injective m := fun x y h => by
    refine Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    rw [← hm, ← hm, h]
  have hsurj : Function.Surjective m := fun z =>
    ⟨Over.homMk (hF.1.lift z.left t (Over.w z)) (hF.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hm _).trans (hF.1.lift_fst _ _ _))⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' m hmul) ⟨hinj, hsurj⟩, hm⟩

theorem epi_spMap_of_field {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  have f₁ : Flat (spMap f) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) f
  have f₂ : Surjective (spMap f) := ⟨fun y => ⟨(default : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem eq_id_of_frac {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (h : ∀ x, ∃ a b, x = φ a / φ b)
    (u : Sp K ⟶ Sp K) (hu : u ≫ spMap φ = spMap φ) : u = 𝟙 _ := by
  obtain ⟨j, rfl⟩ := Spec.map_surjective u
  have e : CommRingCat.ofHom φ ≫ j = CommRingCat.ofHom φ := Spec.map_injective ((Spec.map_comp _ _).trans hu)
  have e' : ∀ a, j.hom (φ a) = φ a := fun a => congrArg (fun q => q.hom a) e
  have : j = 𝟙 _ := by
    ext x
    obtain ⟨a, b, rfl⟩ := h x
    exact (map_div₀ j.hom (φ a) (φ b)).trans (by rw [e', e']; rfl)
  rw [this, Spec.map_id]


open MonObj in
theorem exists_generic_labels {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real)
    {G : Over (Sp Ω)} [GrpObj G] {b : G.left ⟶ ρ.P.A.left} (hb : IsGrpPullback G ρ.P.A (spMap S.R.val.toRingHom) b) :
    ∃ w : S.Gam → (Over.mk (𝟙 (Sp Ω)) ⟶ G), (∀ x, (w x).left ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left) ∧
      (∀ x y, w (x + y) = w x * w y) ∧ Function.Injective w ∧ (∀ x, w x ^ (S.r * S.N) = 1) ∧
      ∀ z, z ^ (S.r * S.N) = 1 → ∃ a, w a = z := by
  obtain ⟨e, he⟩ := exists_mulEquiv_points hb (𝟙 _) (spMap S.R.val.toRingHom) (Category.id_comp _)
  let j : Over.mk (spMap S.R.val.toRingHom) ⟶ baseOver (Sp S.R) := Over.homMk (spMap S.R.val.toRingHom) (by simp)
  let k : Sp (AlgebraicClosure Ω) ⟶ Sp Ω := spMap (algebraMap Ω (AlgebraicClosure Ω))
  have : Epi k := epi_spMap_of_field _
  let k' : Over.mk (k ≫ spMap S.R.val.toRingHom) ⟶ Over.mk (spMap S.R.val.toRingHom) := Over.homMk k rfl
  let w : S.Gam → (Over.mk (𝟙 (Sp Ω)) ⟶ G) := fun x => e.symm (j ≫ ρ.pt x)
  have hw : ∀ x, e (w x) = j ≫ ρ.pt x := fun x => e.apply_symm_apply _
  have hadd : ∀ x y, w (x + y) = w x * w y := fun x y => by
    apply e.injective
    rw [map_mul, hw, hw, hw, ρ.pt_add, MonObj.comp_mul]
  let w' : Multiplicative S.Gam →* (Over.mk (𝟙 (Sp Ω)) ⟶ G) := MonoidHom.mk' (fun x => w x.toAdd) fun x y => hadd _ _
  have htor : ∀ x, w x ^ (S.r * S.N) = 1 := fun x => by
    have h0 : (S.r * S.N) • x = 0 := by
      funext i
      simp [nsmul_eq_mul]
    have h1 : (Multiplicative.ofAdd x) ^ (S.r * S.N) = 1 := by rw [← ofAdd_nsmul, h0, ofAdd_zero]
    exact (map_pow w' (Multiplicative.ofAdd x) _).symm.trans (by rw [h1, map_one])
  have key : ∀ z : Over.mk (𝟙 (Sp Ω)) ⟶ G, z ^ (S.r * S.N) = 1 → ∃! a, w a = z := fun z hz => by
    have h := ρ.pt_bij (AlgebraicClosure Ω) (k ≫ spMap S.R.val.toRingHom) (k' ≫ e z)
      ((map_pow (preHom k') (e z) _).symm.trans (by rw [← map_pow, hz, map_one, map_one]))
    refine (existsUnique_congr fun a => ?_).1 h
    constructor
    · intro ha
      apply e.injective
      rw [hw]
      refine Over.OverMorphism.ext ((cancel_epi k).1 ?_)
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left) ha)
    · rintro rfl
      rw [hw]
      exact Over.OverMorphism.ext (Category.assoc _ _ _)
  refine ⟨w, fun x => (he _).symm.trans (congrArg (fun q => q.left) (hw x)), hadd,
    fun x y h => (key _ (htor y)).unique h rfl, htor, fun z hz => (key z hz).exists⟩


open MonObj in
theorem exists_label_action {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real)
    {G : Over (Sp Ω)} [GrpObj G] {b : G.left ⟶ ρ.P.A.left} (hb : IsGrpPullback G ρ.P.A (spMap S.R.val.toRingHom) b)
    (σ : Ω →+* Ω) (hσ : Function.Surjective σ) {t : G.left ⟶ G.left} (ht : IsGrpPullback G G (spMap σ) t) :
    ∃ a : S.Gam ≃+ S.Gam, (∀ x (w w' : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
      w' ≫ t = spMap σ ≫ w → w' ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt (a x)).left) ∧
      ∀ x (w : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left → w ≫ t = spMap σ ≫ w → a x = x := by
  obtain ⟨p, hp, hadd, hinj, htor, hsurj⟩ := exists_generic_labels ρ hb
  obtain ⟨e, he⟩ := exists_mulEquiv_points ht (𝟙 _) (spMap σ) (Category.id_comp _)
  have : Epi (spMap σ) := epi_spMap_of_field _
  let s : Over.mk (spMap σ) ⟶ Over.mk (𝟙 (Sp Ω)) := Over.homMk (spMap σ) (Category.comp_id _)
  let τ : (Over.mk (𝟙 (Sp Ω)) ⟶ G) →* (Over.mk (𝟙 (Sp Ω)) ⟶ G) := e.symm.toMonoidHom.comp (preHom s)
  have hτ : ∀ z, (τ z).left ≫ t = spMap σ ≫ z.left := fun z =>
    (he _).symm.trans (congrArg (fun q => q.left) (e.apply_symm_apply (s ≫ z)))
  have τinj : Function.Injective τ := fun z z' h => by
    refine Over.OverMorphism.ext ((cancel_epi (spMap σ)).1 ?_)
    rw [← hτ, ← hτ, h]
  have hex : ∀ x, ∃ y, p y = τ (p x) := fun x => hsurj _ (by rw [← map_pow, htor, map_one])
  choose a ha using hex
  let a' : S.Gam →+ S.Gam := AddMonoidHom.mk' a fun x y => hinj (by rw [hadd, ha, ha, ha, hadd, map_mul])
  have ainj : Function.Injective a' := fun x y h => hinj (τinj (by
    rw [← ha, ← ha]; exact congrArg p h))
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have abij : Function.Bijective a' := Finite.injective_iff_bijective.1 ainj
  have h₁ : ∀ x (w : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left → w = (p x).left := fun x w h => by
    refine hb.1.hom_ext (h.trans (hp x).symm) (Eq.trans ?_ (Over.w (p x)).symm)
    refine eq_id_of_frac S.R.val.toRingHom (fun y => ?_) _ ?_
    · obtain ⟨c, hc, d, hd, rfl⟩ := S.frac y
      exact ⟨⟨c, hc⟩, ⟨d, hd⟩, rfl⟩
    · rw [Category.assoc, ← hb.1.w, ← Category.assoc, h, Category.assoc]
      exact (congrArg _ (Over.w (ρ.pt x))).trans (Category.comp_id _)
  have h₂ : ∀ x (w' : Sp Ω ⟶ G.left), w' ≫ t = spMap σ ≫ (p x).left → w' = (p (a x)).left := fun x w' h => by
    rw [ha]
    refine ht.1.hom_ext (h.trans (hτ _).symm) (Eq.trans ?_ (Over.w (τ (p x))).symm)
    refine eq_id_of_frac σ (fun y => ?_) _ ?_
    · obtain ⟨c, rfl⟩ := hσ y
      exact ⟨c, 1, by rw [map_one, div_one]⟩
    · rw [Category.assoc, ← ht.1.w, ← Category.assoc, h, Category.assoc]
      exact (congrArg _ (Over.w (p x))).trans (Category.comp_id _)
  refine ⟨AddEquiv.ofBijective a' abij, fun x w w' hw hw' => ?_, fun x w hw hw' => ?_⟩
  · rw [h₁ x w hw] at hw'
    rw [h₂ x w' hw']
    exact hp _
  · have e₁ := h₁ x w hw
    subst e₁
    exact hinj (Over.OverMorphism.ext (h₂ x _ hw').symm)

theorem exists_galLab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ ∀ x, a (D.lab x) = D.lab x := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D σ
  obtain ⟨P₀, a₁, a₂, ε₀, h₁, h₂, l₁, l₂, hε, hpt⟩ := D.same
  have hs : spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun y => σ.commutes _))
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : P₀.A.left ⟶ P₀.A.left, t ≫ a₁ = a₁ ∧
      t ≫ P₀.A.hom = P₀.A.hom ≫ spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) :=
    ⟨h₁.1.lift a₁ (P₀.A.hom ≫ spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) (by rw [Category.assoc, hs, h₁.1.w]),
      h₁.1.lift_fst _ _ _, h₁.1.lift_snd _ _ _⟩
  have ht : IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t := h₁.cancel (h₁.congr hs.symm ht₁.symm) ht₂
  have lt : LBIso (P₀.L.pull t) (X₁.ρ.P.L.pull a₁) :=
    l₁.chartPull (Geo.Tor.chartPullPull P₀.L t t rfl)
      (chartPullSame X₁.ρ.P.L (fun _ => a₁) (fun _ => a₁) _ t fun _ => ht₁.symm)
  obtain ⟨a, ha, ha'⟩ := exists_label_action D.X.ρ h₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) σ.surjective ht
  refine ⟨a, ⟨P₀, a₂, t, ε₀, h₂, ht, l₂,
    LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB _) (pull_isLB P₀.isLB _) l₁ lt.symm, fun E => ⟨(hε E).2, ?_⟩, ha⟩,
    fun x => ?_⟩
  · refine h₁.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ht₁, (hε E).1, ← Category.assoc, ht₁]
    · rw [Category.assoc, Category.assoc, ht₂, Over.w (ε₀ E), ← Category.assoc, Over.w (ε₀ E), ht₂]
  · obtain ⟨w, hw₁, hw₂⟩ := hpt x
    refine ha' _ w hw₂ (h₁.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ht₁, hw₁, ← Category.assoc, hs]
    · have hw : w ≫ P₀.A.hom = 𝟙 _ := by
        refine eq_id_of_frac D.X.S.R.val.toRingHom (fun y => ?_) _ ?_
        · obtain ⟨c, hc, d, hd, rfl⟩ := D.X.S.frac y
          exact ⟨⟨c, hc⟩, ⟨d, hd⟩, rfl⟩
        · rw [Category.assoc, ← h₂.1.w, ← Category.assoc, hw₂, Category.assoc]
          exact (congrArg _ (Over.w (D.X.ρ.pt _))).trans (Category.comp_id _)
      rw [Category.assoc, Category.assoc, ht₂, hw, ← Category.assoc, hw, Category.id_comp, Category.comp_id]

end GlobalTheory.Poinc.GalAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutomorphismActsOnDeeperLevelLabelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_automorphism_acts_on_deeper_level_labels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ ∀ x, a (D.lab x) = D.lab x := by
  first | exact @GlobalTheory.Poinc.GalAct.exists_galLab | exact GlobalTheory.Poinc.GalAct.exists_galLab | (intros; apply GlobalTheory.Poinc.GalAct.exists_galLab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogChernCocycleContractionInvariantFieldTriviali
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogChernCocycleContractionInvariantFieldTriviali
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.PrismDlog

noncomputable def dl {B : Type} [CommRing B] (a : DualNumber B) : B := a.snd * Ring.inverse a.fst

theorem dl_mul {B : Type} [CommRing B] {a b : DualNumber B} (ha : IsUnit a.fst) (hb : IsUnit b.fst) :
    dl (a * b) = dl a + dl b := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  have e : (a * b).fst = ((x * y : Bˣ) : B) := by simp [hx, hy]
  have e2 : (a * b).snd = a.fst * b.snd + a.snd * b.fst := by
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  have h1 : (x : B) * ((x⁻¹ : Bˣ) : B) = 1 := Units.mul_inv x
  have h2 : (y : B) * ((y⁻¹ : Bˣ) : B) = 1 := Units.mul_inv y
  rw [dl, dl, dl, e, e2, Ring.inverse_unit, ← hx, ← hy, Ring.inverse_unit, Ring.inverse_unit, mul_inv_rev,
    Units.val_mul]
  linear_combination (b.snd * ((y⁻¹ : Bˣ) : B)) * h1 + (a.snd * ((x⁻¹ : Bˣ) : B)) * h2

theorem dl_inl {B : Type} [CommRing B] (b : B) : dl (TrivSqZeroExt.inl b : DualNumber B) = 0 := by
  simp [dl]

theorem dl_one_add {B : Type} [CommRing B] {a : DualNumber B} (ha : a.fst = 0) : dl (1 + a) = a.snd := by
  simp [dl, ha]

theorem dl_map {R B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (ρ : B →ₐ[R] B')
    {a : DualNumber B} (ha : IsUnit a.fst) : dl (dualAlg ρ a) = ρ (dl a) := by
  obtain ⟨x, hx⟩ := ha
  have e : (dualAlg ρ a).fst = ((Units.map (ρ : B →* B') x : B'ˣ) : B') := by simp [hx]
  rw [dl, dl, e, ← hx, Ring.inverse_unit, Ring.inverse_unit, snd_dualAlg, map_mul]
  simp

theorem snd_eq_of_mul {B : Type} [CommRing B] {l U X Y : DualNumber B} (hl : l.fst = 0) (hU : IsUnit U.fst)
    (hX : IsUnit X.fst) (hY : IsUnit Y.fst) (h : (1 + l) * U = X * Y) : l.snd = dl X + dl Y - dl U := by
  have h1 : IsUnit (1 + l).fst := by simp [hl]
  have := congrArg dl h
  rw [dl_mul h1 hU, dl_mul hX hY, dl_one_add hl] at this
  rw [← this]; ring

theorem isUnit_fst {B : Type} [CommRing B] {a : DualNumber B} (h : IsUnit a) : IsUnit a.fst :=
  h.map (TrivSqZeroExt.fstHom B B B)

theorem valR_cocycle {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {C : Type} [CommRing C] (w : Sp C ⟶ X)
    (a b k : L.ι) (h : ⊤ ≤ w ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U k)) :
    valR w _ (L.g a b).val * valR w _ (L.g b k).val = valR w _ (L.g a k).val := by
  have := congrArg (fun z ↦ valR w _ (z : Γ(X, L.U a ⊓ L.U b ⊓ L.U k)ˣ).val) (hL.cocycle a b k)
  simp only [Units.val_mul] at this
  rw [GlobalTheory.Points.valR_mul w _ h] at this
  simp only [res, Units.coe_map, MonoidHom.coe_coe] at this
  rwa [GlobalTheory.Points.valR_res w _ h, GlobalTheory.Points.valR_res w _ h, GlobalTheory.Points.valR_res w _ h] at this

theorem isUnit_valR {X : Scheme.{0}} {C : Type} [CommRing C] (w : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : IsUnit (valR w U f.val) := by
  rw [GlobalTheory.Points.valR_eq w U h]; exact f.isUnit.map _

theorem evalAt_eq_valR {X : Scheme.{0}} {C : Type} [CommRing C] (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : evalAt x U h f = valR x U f := by
  rw [valR, dif_pos h]; rfl

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem fst_valR_trx (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) (U : A.left.Opens) (h : P.In U)
    (f : Γ(A.left, U)) : (valR (P.trx v) U f).fst = valR P.x U f := by
  have e := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom P.B P.B P.B).toRingHom (P.trx v) U (h.tr hv) f
  rw [(P.isTransl_trx v).red hv] at e
  rw [e]; rfl

theorem snd_l (L : LB A.left) (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T))
    (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U))
    (hu : ∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T))
      (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val)
    (hl : ∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ)
    (R : GPt A) (hR : ∃ i, R.In (L.U i)) {T T' : Small L.U} (φ : T ⟶ T') (ψ : T' ⟶ ⟨R.ext, hR⟩) :
    TrivSqZeroExt.snd (R := R.B) (l T T' ⟨R.ext, hR⟩ φ ψ : DualNumber R.B) =
      dl (ψ.hom.φ (u T T' φ) : DualNumber R.B) + dl (u T' ⟨R.ext, hR⟩ ψ : DualNumber R.B) -
        dl (u T ⟨R.ext, hR⟩ (φ ≫ ψ) : DualNumber R.B) := by
  have hunit : ∀ (T T' : Small L.U) (φ : T ⟶ T'), IsUnit (T'.obj.π (u T T' φ)) := fun T T' φ ↦ by
    rw [hu]; exact (L.g _ _).isUnit.map _
  obtain ⟨hmem, heq⟩ := hl T T' ⟨R.ext, hR⟩ φ ψ
  rw [dpExp_sqDP _ hmem] at heq
  refine snd_eq_of_mul hmem (hunit T ⟨R.ext, hR⟩ (φ ≫ ψ)) ?_ (hunit T' ⟨R.ext, hR⟩ ψ) heq
  have e := ψ.hom.comm (u T T' φ)
  change _ = TrivSqZeroExt.fst _ at e
  rw [← e]
  exact (hunit T T' φ).map _

theorem snd_l' (L : LB A.left) (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T))
    (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U))
    (hu : ∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T))
      (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val)
    (hl : ∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ)
    (R : GPt A) (hR : ∃ i, R.In (L.U i)) {T T' : Small L.U} (φ : T ⟶ T') (ψ : T' ⟶ ⟨R.ext, hR⟩)
    (χ : T ⟶ ⟨R.ext, hR⟩) (hχ : φ ≫ ψ = χ) :
    TrivSqZeroExt.snd (R := R.B) (l T T' ⟨R.ext, hR⟩ φ ψ : DualNumber R.B) =
      dl (ψ.hom.φ (u T T' φ) : DualNumber R.B) + dl (u T' ⟨R.ext, hR⟩ ψ : DualNumber R.B) -
        dl (u T ⟨R.ext, hR⟩ χ : DualNumber R.B) := by
  subst hχ; exact snd_l L c hc u l hu hl R hR φ ψ


open Classical in
noncomputable def Nf (L : LB A.left) (c : Small L.U → L.ι) (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B)
    {v : epsR K ⟶ A} (hv : IsTangent v) (j : L.ι) : PtFn (A.hom ≫ 𝟙 (Sp K)) := fun P ↦
  if h : P.In (L.U j) then
    dl (u ⟨P.triv, ⟨j, h⟩⟩ ⟨P.ext, ⟨j, h⟩⟩ ⟨P.sec⟩ : DualNumber P.B) -
      dl (u ⟨(P.tr v).triv, ⟨j, h.tr hv⟩⟩ ⟨P.ext, ⟨j, h⟩⟩ ⟨P.tan hv⟩ : DualNumber P.B) -
      dl (valR (P.trx v) _ (L.g (c ⟨(P.tr v).triv, ⟨j, h.tr hv⟩⟩) j).val)
  else 0

end GlobalTheory.CechKS.PrismDlog


open GlobalTheory.CechKS.PrismDlog in
theorem GlobalTheory.CechKS.prism_trivialised : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T)) (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U)), (∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T)) (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val) → (∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧ dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ) → ∀ (v : epsR K ⟶ A) (hv : IsTangent v), ∃ N : L.ι → PtFn (A.hom ≫ 𝟙 (Sp K)), (∀ (j : L.ι) (P Q : GPt A) (φ : P.Hom Q) (hP : P.In (L.U j)), prism l hv φ ⟨j, hP⟩ = N j Q - φ.ρ (N j P)) ∧ ∀ (j j' : L.ι) (P : GPt A), P.In (L.U j) → P.In (L.U j') → N j P - N j' P = dlog L v j j' P := by
  intro K _ A _ L hL c hc u l hu hl v hv
  have hunit : ∀ (T T' : Small L.U) (φ : T ⟶ T'), IsUnit (T'.obj.π (u T T' φ)) := fun T T' φ ↦ by
    rw [hu]; exact (L.g _ _).isUnit.map _
  refine ⟨Nf L c u hv, ?_, ?_⟩
  · intro j P Q φ hP
    have hQ : Q.In (L.U j) := hP.map φ
    have k1 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨P.triv, ⟨j, hP⟩⟩) (T' := ⟨Q.triv, ⟨j, hQ⟩⟩) ⟨φ.triv⟩ ⟨Q.sec⟩
      ⟨P.sec ≫ φ.dual⟩ (by
        ext1
        apply Thick.Hom.ext'
        ext b
        · show (TrivSqZeroExt.inl (φ.ρ b) : DualNumber Q.B).fst = (dualAlg φ.ρ (TrivSqZeroExt.inl b)).fst
          simp
        · show (TrivSqZeroExt.inl (φ.ρ b) : DualNumber Q.B).snd = (dualAlg φ.ρ (TrivSqZeroExt.inl b)).snd
          simp)
    have k2 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨P.triv, ⟨j, hP⟩⟩) (T' := ⟨P.ext, ⟨j, hP⟩⟩) ⟨P.sec⟩ ⟨φ.dual⟩
      ⟨P.sec ≫ φ.dual⟩ rfl
    have k3 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩)
      (T' := ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩) ⟨(φ.tr v).triv⟩ ⟨Q.tan hv⟩ ⟨P.tan hv ≫ φ.dual⟩ (by ext1; apply Thick.Hom.ext'; ext b <;> rfl)
    have k4 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩)
      (T' := ⟨P.ext, ⟨j, hP⟩⟩) ⟨P.tan hv⟩ ⟨φ.dual⟩ ⟨P.tan hv ≫ φ.dual⟩ rfl
    obtain ⟨a, ha⟩ : ∃ a, a = c ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = c ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ := ⟨_, rfl⟩
    have hPa : (P.tr v).In (L.U a) := ha ▸ hc ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩
    have hQb : (Q.tr v).In (L.U b) := hb ▸ hc ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩
    have hQa : (Q.tr v).In (L.U a) := hPa.map (φ.tr v)
    have e1 : (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩ : DualNumber Q.B) =
        valR (Q.trx v) _ (L.g b a).val := by
      subst ha hb
      exact (hu ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩).trans
        (evalAt_eq_valR _ _ _ _)
    have e2 : valR (Q.trx v) _ (L.g a j).val = dualAlg φ.ρ (valR (P.trx v) _ (L.g a j).val) := by
      have e := GlobalTheory.Points.valR_spMap_comp (dualAlg φ.ρ : DualNumber P.B →+* DualNumber Q.B) (P.trx v) _
        (hPa.inf (hP.tr hv)) (L.g a j).val
      have e' : spMap (dualAlg φ.ρ : DualNumber P.B →+* DualNumber Q.B) ≫ P.trx v = Q.trx v := (φ.tr v).pt
      rw [e'] at e
      exact e
    have e3 := valR_cocycle L hL (Q.trx v) b a j ((hQb.inf hQa).inf (hQ.tr hv))
    have e4 : dl (valR (Q.trx v) _ (L.g b j).val) =
        dl (valR (Q.trx v) _ (L.g b a).val) + φ.ρ (dl (valR (P.trx v) _ (L.g a j).val)) := by
      rw [← e3, dl_mul (isUnit_fst (isUnit_valR _ _ (hQb.inf hQa) _))
        (isUnit_fst (isUnit_valR _ _ (hQa.inf (hQ.tr hv)) _)), e2,
        dl_map _ (isUnit_fst (isUnit_valR _ _ (hPa.inf (hP.tr hv)) _))]
    have d1 : dl (Q.sec.φ (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨Q.triv, ⟨j, hQ⟩⟩ ⟨φ.triv⟩) : DualNumber Q.B) = 0 := dl_inl _
    have d2 : dl (φ.dual.φ (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩) : DualNumber Q.B) =
        φ.ρ (dl (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩ : DualNumber P.B)) :=
      dl_map φ.ρ (hunit ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩)
    have d3 : dl ((Q.tan hv).φ (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩
        ⟨(φ.tr v).triv⟩) : DualNumber Q.B) = dl (valR (Q.trx v) _ (L.g b a).val) := congrArg dl e1
    have d4 : dl (φ.dual.φ (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩) : DualNumber Q.B) =
        φ.ρ (dl (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩ : DualNumber P.B)) :=
      dl_map φ.ρ (hunit ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩)
    have k1' := k1.trans (congrArg (fun z ↦ z + _ - _) d1)
    have k2' := k2.trans (congrArg (fun z ↦ z + _ - _) d2)
    have k3' := k3.trans (congrArg (fun z ↦ z + _ - _) d3)
    have k4' := k4.trans (congrArg (fun z ↦ z + _ - _) d4)
    have key : ∀ {x1 x2 x3 x4 : DualNumber Q.B} {y1 y2 y3 y4 : Q.B}, x1.snd = y1 → x2.snd = y2 → x3.snd = y3 →
        x4.snd = y4 → ((x1 - x2) - (x3 - x4)).snd = (y1 - y2) - (y3 - y4) := by
      rintro x1 x2 x3 x4 _ _ _ _ rfl rfl rfl rfl
      simp
    refine (key k1' k2' k3' k4').trans ?_
    simp only [Nf, dif_pos hP, dif_pos hQ, map_sub]
    rw [← ha, ← hb, e4]
    ring
  · intro j j' P hj hj'
    obtain ⟨b, hb⟩ : ∃ b, b = c ⟨(P.tr v).triv, ⟨j, hj.tr hv⟩⟩ := ⟨_, rfl⟩
    have hPb : (P.tr v).In (L.U b) := hb ▸ hc ⟨(P.tr v).triv, ⟨j, hj.tr hv⟩⟩
    simp only [Nf, dif_pos hj, dif_pos hj']
    rw [← hb]
    have e3 := valR_cocycle L hL (P.trx v) b j j' ((hPb.inf (hj.tr hv)).inf (hj'.tr hv))
    have e4 : dl (valR (P.trx v) _ (L.g b j').val) =
        dl (valR (P.trx v) _ (L.g b j).val) + dl (valR (P.trx v) _ (L.g j j').val) := by
      rw [← e3, dl_mul (isUnit_fst (isUnit_valR _ _ (hPb.inf (hj.tr hv)) _))
        (isUnit_fst (isUnit_valR _ _ ((hj.inf hj').tr hv) _))]
    have e5 : dl (valR (P.trx v) _ (L.g j j').val) = dlog L v j j' P := by
      rw [dl, dlog, fst_valR_trx P hv _ (hj.inf hj')]
      have h1 : valR P.x _ (L.g j j').val * valR P.x _ (L.g j j')⁻¹.val = 1 := by
        rw [← GlobalTheory.Points.valR_mul _ _ (hj.inf hj'), Units.mul_inv, GlobalTheory.Points.valR_eq _ _ (hj.inf hj'), map_one]
      have h2 : Ring.inverse (valR P.x _ (L.g j j').val) = valR P.x _ (L.g j j')⁻¹.val :=
        Ring.inverse_unit (Units.mkOfMulEqOne _ _ h1)
      rw [h2]
    rw [← e5, e4]
    ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogChernCocycleContractionInvariantFieldTrivialiStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logChernCocycle_contraction_invariantField_trivialised : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T)) (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U)), (∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T)) (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val) → (∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧ dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ) → ∀ (v : epsR K ⟶ A) (hv : IsTangent v), ∃ N : L.ι → PtFn (A.hom ≫ 𝟙 (Sp K)), (∀ (j : L.ι) (P Q : GPt A) (φ : P.Hom Q) (hP : P.In (L.U j)), prism l hv φ ⟨j, hP⟩ = N j Q - φ.ρ (N j P)) ∧ ∀ (j j' : L.ι) (P : GPt A), P.In (L.U j) → P.In (L.U j') → N j P - N j' P = dlog L v j j' P := by
  first | exact @GlobalTheory.CechKS.prism_trivialised | exact GlobalTheory.CechKS.prism_trivialised | (intros; apply GlobalTheory.CechKS.prism_trivialised <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimAddRank
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem Trait.dim_add_rank : ∀ {g n : ℕ}, 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F),
    T.D.toPre.P.g + Module.finrank ℤ T.D.toPre.X = g := by
  intro g n hn F T
  have hn0 : n ≠ 0 := by omega
  have hζ : IsUnit (zetaAway n) := by rw [← cycBase_ζ hn0]; exact Units.isUnit _
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ hn hζ (isUnit_natCast hn0)
  have hA : SmoothOfRelativeDimension g T.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback T.cart.1 hd
  have e : T.A.g = g :=
    H1.dim_unique _ T.A.smoothDim hA ((η[T.A.A]).left (IsLocalRing.closedPoint _))
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwoPointFunctionMultiplesNaturalCharP
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem chi_natural (p : ℕ) (R : Type) [CommRing R] (hp : (p : R) = 0)
    (A : Over (Sp R)) [GrpObj A] (f : Fn1 A) (g : Fn2 A) (hg : IsAdd f g)
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) :
    chi p g D' (spOver φ ≫ x) - φ (chi p g D x) = f D D' φ (x ^ p) - f D D' φ 1 := by
  have hp' : (p : D') = 0 := by
    rw [← map_natCast (algebraMap R D') p, hp, map_zero]
  unfold chi
  rw [map_sum φ, ← Finset.sum_sub_distrib]
  have h : ∀ i ∈ Finset.range p, g D' ((spOver φ ≫ x) ^ i) (spOver φ ≫ x) - φ (g D (x ^ i) x) =
      (f D D' φ (x ^ (i + 1)) - f D D' φ (x ^ i)) - f D D' φ x := by
    intro i _
    rw [← MonObj.comp_pow, hg D D' φ (x ^ i) x, pow_succ]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ f D D' φ (x ^ i)) p,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, hp', zero_mul, sub_zero, pow_zero]

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFieldExtCancel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFieldExtCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_field_cancel (Ω Ω' : Type) [Field Ω] [Field Ω'] (io : Ω →+* Ω') (X : Scheme.{0}) (a b : Sp Ω ⟶ X)
    (h : spMap io ≫ a = spMap io ≫ b) : a = b := by
  haveI : Epi (spMap io) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (spMap io)).1 h

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFieldExtCancelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spMap_field_ext_cancel : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (io : Ω →+* Ω') (X : Scheme.{0}) (a b : Sp Ω ⟶ X), spMap io ≫ a = spMap io ≫ b → a = b := by
  first | exact @GlobalTheory.Mum.spMap_field_cancel | exact GlobalTheory.Mum.spMap_field_cancel | (intros; apply GlobalTheory.Mum.spMap_field_cancel <;> assumption)
end
end
