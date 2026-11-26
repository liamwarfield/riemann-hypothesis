module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionFieldOfPointCoordsTop
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionFieldOfPointCoordsTop
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.GenTop

theorem appLE_fromSpecResidueField {X : Scheme.{0}} {U : X.Opens} (x : X) (hx : x ∈ U)
    (h : ⊤ ≤ X.fromSpecResidueField x ⁻¹ᵁ U) :
    (X.fromSpecResidueField x).appLE U ⊤ h = X.evaluation U x hx ≫ (Scheme.ΓSpecIso _).inv := by
  have h' : ⊤ ≤ Spec.map (X.residue x) ⁻¹ᵁ (X.fromSpecStalk x ⁻¹ᵁ U) := h
  have e : X.fromSpecResidueField x = Spec.map (X.residue x) ≫ X.fromSpecStalk x := rfl
  have := Scheme.Hom.appLE_comp_appLE (Spec.map (X.residue x)) (X.fromSpecStalk x) U (X.fromSpecStalk x ⁻¹ᵁ U) ⊤ le_rfl h'
  rw [appLE_of_eq e U ⊤ h (h'.trans le_rfl), ← this, ← Scheme.Hom.app_eq_appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, Scheme.Hom.map_appLE]
  rw [← Scheme.germ_residue, Category.assoc, Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem pullRatio_SpecMap_fromSpec {N : ℕ} (i : Fin (N + 1)) {R : CommRingCat.{0}}
    (ψ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ R)
    (h : ⊤ ≤ (Spec.map ψ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ⁻¹ᵁ chart ℤ N i) (j : Fin (N + 1)) :
    pullRatio (Spec.map ψ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ⊤ i h j =
      (Scheme.ΓSpecIso R).inv (ψ (ratio ℤ N i j)) := by
  have h1 : (isAffineOpen_chart ℤ N i).fromSpec.appLE (chart ℤ N i) ⊤
      (isAffineOpen_chart ℤ N i).fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h3 := Scheme.Hom.appLE_comp_appLE (Spec.map ψ) (isAffineOpen_chart ℤ N i).fromSpec
    (chart ℤ N i) ⊤ ⊤ (isAffineOpen_chart ℤ N i).fromSpec_preimage_self.ge le_rfl
  unfold pullRatio
  rw [← h3, h1]
  have := congrArg (fun q => q.hom (ratio ℤ N i j)) (Scheme.ΓSpecIso_inv_naturality ψ)
  exact this.symm

theorem surjective_of_factor {X : Scheme.{0}} (x : X) {F : Type} [Field F]
    (ι : CommRingCat.of F ⟶ X.residueField x) (G : Spec (.of F) ⟶ X)
    (h : Spec.map ι ≫ G = X.fromSpecResidueField x) : Function.Surjective ι.hom := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective G
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h
  have hz : z = x := by
    have e := congrArg (fun f : Spec (X.residueField x) ⟶ X => f default) h
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hz
  rw [← Category.assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (φ ≫ ι) = Spec.map (𝟙 _) := by
    rw [← cancel_mono (X.fromSpecResidueField _), Spec.map_id, Category.id_comp]
    exact h
  have h3 : φ ≫ ι = 𝟙 _ := Spec.map_injective h2
  intro a
  refine ⟨φ.hom a, ?_⟩
  have := congrArg (fun q => q.hom a) h3
  simpa using this

theorem blockFnField_ptCoord_eq_top (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n)
    [CharZero ((MP ℤ m n).residueField x)] : blockFnField (ptCoord x) = ⊤ := by
  have hone : ∀ k, ptCoord x ⟨k, ptChart x k⟩ = 1 := fun k => by
    simp only [ptCoord, pullRatio_self, map_one]
  have hmem : ∀ p, ptCoord x p ∈ blockFnField (ptCoord x) := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, by rw [hone, div_one]⟩
  let F := blockFnField (ptCoord x)
  let r : ∀ k, Fin (n k + 1) → F := fun k j => ⟨ptCoord x ⟨k, j⟩, hmem _⟩
  have hr : ∀ k, r k (ptChart x k) = 1 := fun k => Subtype.ext (hone k)
  let ρ : ∀ k, Γ(PSpace ℤ (n k), chart ℤ (n k) (ptChart x k)) ⟶ CommRingCat.of F := fun k =>
    CommRingCat.ofHom (R := Γ(PSpace ℤ (n k), chart ℤ (n k) (ptChart x k))) (S := F)
      (chartLift (ptChart x k) (Int.castRingHom F) (r k))
  let g : ∀ k, Spec (CommRingCat.of F) ⟶ projectiveSpace ℤ (n k) := fun k =>
    Spec.map (ρ k) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec
  let G : Spec (CommRingCat.of F) ⟶ MP ℤ m n :=
    GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (Spec.map (CommRingCat.ofHom (Int.castRingHom F))) g
      (fun _ => specZIsTerminal.hom_ext _ _)
  let ι : CommRingCat.of F ⟶ (MP ℤ m n).residueField x := CommRingCat.ofHom F.val.toRingHom
  have key : Spec.map ι ≫ G = (MP ℤ m n).fromSpecResidueField x := by
    refine GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_
    rw [Category.assoc, GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr]
    have hx := mem_ptChart x k
    have h₂' : ⊤ ≤ (MP ℤ m n).fromSpecResidueField x ⁻¹ᵁ blockChart n k (ptChart x k) := fun s _ => by
      rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
      exact hx
    have e1 : Spec.map ι ≫ g k = Spec.map (ρ k ≫ ι) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec := by
      rw [Spec.map_comp, Category.assoc]
    have h₁ : ⊤ ≤ (Spec.map (ρ k ≫ ι) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec) ⁻¹ᵁ
        chart ℤ (n k) (ptChart x k) := by
      rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
      exact le_top
    rw [e1]
    refine GlobalTheory.ProjSpace.hom_ext (specZIsTerminal.hom_ext _ _) fun _ =>
      ⟨⊤, trivial, ptChart x k, h₁, by rw [Scheme.Hom.comp_preimage]; exact h₂', fun j => ?_⟩
    rw [pullRatio_SpecMap_fromSpec]
    have e2 := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k) (hi := le_rfl)
      (j := j) ((MP ℤ m n).fromSpecResidueField x) h₂'
    refine Eq.trans ?_ e2
    rw [appLE_fromSpecResidueField x hx]
    show _ = (Scheme.ΓSpecIso _).inv (ptCoord x ⟨k, j⟩)
    congr 1
    show F.val (chartLift (ptChart x k) (Int.castRingHom F) (r k) (ratio ℤ (n k) (ptChart x k) j)) = _
    rw [chartLift_ratio _ _ (hr k)]
    rfl
  have hs := surjective_of_factor x ι G key
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨b, rfl⟩ := hs a
  exact b.2

end GlobalTheory.CompanionTheory.MPDict.GenTop
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionFieldOfPointCoordsTopStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_of_point_coords_top : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) [CharZero ((MP ℤ m n).residueField x)], blockFnField (ptCoord x) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top | exact GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top | (intros; apply GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KrullDimQuotientEqTrdegSucc
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KrullDimQuotientEqTrdegSucc
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.DimChart

theorem isIso_residueFieldMap {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    IsIso (j.residueFieldMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, rfl⟩ := j.stalkMap_surjective x b
  refine ⟨Y.residue _ c, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
  rfl

noncomputable def residueFieldEquiv {Y : Scheme.{0}} {B : Type} [CommRing B] (j : Spec (.of B) ⟶ Y)
    [IsOpenImmersion j] (q : PrimeSpectrum B) :
    Y.residueField (j q) ≃+* q.asIdeal.ResidueField :=
  haveI := isIso_residueFieldMap j q
  (asIso (j.residueFieldMap q) ≪≫ Scheme.Spec.residueFieldIso (.of B) q).commRingCatIsoToRingEquiv

theorem trdeg_int_eq_of_isFractionRing (A : Type) [CommRing A] [IsDomain A] [Algebra ℤ A] (L : Type)
    [Field L] [Algebra ℤ L] [Algebra A L] [IsFractionRing A L]
    (hA : Function.Injective (algebraMap ℤ A)) :
    Algebra.trdeg ℤ A = Algebra.trdeg ℤ L := by
  obtain rfl : ‹Algebra ℤ A› = Ring.toIntAlgebra A := Subsingleton.elim _ _
  obtain rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L := Subsingleton.elim _ _
  have : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A L)
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).2 hA
  have : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  rw [← trdeg_add_eq ℤ A (A := L), trdeg_eq_zero (R := A) (A := L), add_zero]

theorem trdeg_int_eq_of_ringEquiv {L L' : Type} [CommRing L] [CommRing L'] [Algebra ℤ L]
    [Algebra ℤ L'] (e : L ≃+* L') : Algebra.trdeg ℤ L = Algebra.trdeg ℤ L' := by
  obtain rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L := Subsingleton.elim _ _
  obtain rfl : ‹Algebra ℤ L'› = Ring.toIntAlgebra L' := Subsingleton.elim _ _
  exact e.toIntAlgEquiv.trdeg_eq

theorem ringKrullDim_quotient_eq (Y : Scheme.{0}) (B : Type) [CommRing B] [Algebra ℤ B]
    [Algebra.FiniteType ℤ B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B)
    (h0 : CharZero (Y.residueField (j q))) :
    ringKrullDim (B ⧸ q.asIdeal) =
      (((Algebra.trdeg ℤ (Y.residueField (j q))).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  have e := residueFieldEquiv j q
  have : CharZero q.asIdeal.ResidueField := charZero_of_injective_ringHom (f := e.toRingHom) e.injective
  have hinj : Function.Injective (algebraMap ℤ (B ⧸ q.asIdeal)) := by
    have hK : Function.Injective
        ((algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField).comp (algebraMap ℤ (B ⧸ q.asIdeal))) := by
      rw [show (algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField).comp
        (algebraMap ℤ (B ⧸ q.asIdeal)) = Int.castRingHom _ from Subsingleton.elim _ _]
      exact Int.cast_injective
    rw [RingHom.coe_comp] at hK
    exact Function.Injective.of_comp hK
  have : Algebra.FiniteType ℤ (B ⧸ q.asIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q.asIdeal) (Ideal.Quotient.mkₐ_surjective _ _)
  rw [GroundTheory.Heights₂.Heights.IntDomainDim.proof (B ⧸ q.asIdeal) hinj,
    trdeg_int_eq_of_isFractionRing (B ⧸ q.asIdeal) q.asIdeal.ResidueField hinj,
    trdeg_int_eq_of_ringEquiv e.symm]

end GlobalTheory.CompanionTheory.DimChart
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KrullDimQuotientEqTrdegSuccStatement
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ : ∀ (Y : Scheme.{0}) (B : Type) [CommRing B] [Algebra ℤ B] [Algebra.FiniteType ℤ B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B), CharZero (Y.residueField (j q)) → ringKrullDim (B ⧸ q.asIdeal) = (((Algebra.trdeg ℤ (Y.residueField (j q))).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq | exact GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq | (intros; apply GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimension
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimVar

open Topology

theorem finiteType_of_chart {Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] {C : Type} [CommRing C]
    [Algebra ℤ C] (j : Spec (.of C) ⟶ Y) [IsOpenImmersion j] (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℤ C))) :
    Algebra.FiniteType ℤ C :=
  RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap ℤ C))).mp (hj ▸ inferInstance)

theorem topologicalKrullDim_closure_eq (Y : Scheme.{0}) (f : Y ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] (y : Y)
    [CharZero (Y.residueField y)] :
    topologicalKrullDim (closure ({y} : Set Y)) =
      (((Algebra.trdeg ℤ (Y.residueField y)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨B, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f y
  subst hq
  have := finiteType_of_chart f j hj
  rw [← GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y B j q inferInstance, ← topologicalKrullDim_range_inter_closure_eq j q]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun z ↦ ?_)
    (IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  obtain ⟨C, _, _, j', _, y', hy, hj'⟩ := exists_affine_chart_over f z.1
  have := finiteType_of_chart f j' hj'
  obtain ⟨q', hq'⟩ := (specializes_iff_mem_closure.mpr z.2).mem_open
    j'.isOpenEmbedding.isOpen_range ⟨y', hy⟩
  refine ⟨Subtype.val ⁻¹' Set.range j',
    j'.isOpenEmbedding.isOpen_range.preimage continuous_subtype_val, ⟨y', hy⟩, ?_⟩
  rw [← topologicalKrullDim_eq_of_isEmbedding (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    (Z := Set.range j' ∩ closure {j q})
    (by rw [Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe, Set.inter_comm])]
  rw [topologicalKrullDim_range_inter_closure_eq j q, GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y B j q inferInstance]
  conv_lhs => rw [← hq', topologicalKrullDim_range_inter_closure_eq j' q']
  have h0 : CharZero (Y.residueField (j' q')) := hq' ▸ inferInstance
  rw [GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y C j' q' h0, hq']

theorem ptCoord_chart_ne_zero {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) (k : Fin (m + 1)) :
    ptCoord x ⟨k, ptChart x k⟩ ≠ 0 := by
  simp [ptCoord, pullRatio_self]

theorem isArithVar_ptIdeal : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) → Geo.IsArithVar (ptIdeal x) d := by
  intro m n x d hch hd
  have hdim := topologicalKrullDim_closure_eq (MP ℤ m n) (mpStr ℤ m n) x
  rw [hd] at hdim
  have h1 : ((d : ℕ∞)) = (Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat + 1 := WithBot.coe_injective hdim
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat = t := by
    refine ⟨(Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat.toNat, (ENat.natCast_toNat ?_).symm⟩
    intro h
    rw [h] at h1
    simp at h1
  have hdt : d = t + 1 := by
    rw [ht] at h1
    exact_mod_cast h1
  subst hdt
  have htr : Algebra.trdeg ℤ (blockFnField (ptCoord x)) = t := by
    rw [GlobalTheory.T.function_field_of_point_coords_top m n x, GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.trdeg_top]
    exact Cardinal.toENat_eq_natCast.mp ht
  exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_of_trdeg (ptCoord x) (ptChart x) (ptCoord_chart_ne_zero x) t htr

end GlobalTheory.CompanionTheory.MPDict.DimVar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimensionStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_point_dimension : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) → Geo.IsArithVar (ptIdeal x) d := by
  exact @GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal
end
