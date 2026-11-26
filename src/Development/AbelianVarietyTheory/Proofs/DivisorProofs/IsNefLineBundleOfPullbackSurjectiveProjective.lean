module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFiberIsAlgebraicResidueFieldOfLft
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFiberIsAlgebraicResidueFieldOfLft
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

namespace GlobalTheory

theorem isAlgebraic_residueField_transport {X : Scheme.{0}} {w x : X} (h : w = x) {C : CommRingCat.{0}}
    (ψ : X.residueField w ⟶ C) (φ : X.residueField x ⟶ C)
    (e : Spec.map ψ ≫ X.fromSpecResidueField w = Spec.map φ ≫ X.fromSpecResidueField x)
    (hφ : letI := φ.hom.toAlgebra; Algebra.IsAlgebraic (X.residueField x) C) :
    letI := ψ.hom.toAlgebra; Algebra.IsAlgebraic (X.residueField w) C := by
  subst h
  have : ψ = φ := Spec.map_injective ((cancel_mono _).mp e)
  subst this
  exact hφ

theorem exists_mem_fiber_isAlgebraic_residueField :
    ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧
      (letI := (π.residueFieldMap y).hom.toAlgebra;
        Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) := by
  intro Y X π _ y₀
  let x := π y₀
  let s : π.fiber x ⟶ Spec (X.residueField x) := π.fiberToSpecResidueField x
  haveI : LocallyOfFiniteType s := by
    show LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  haveI : JacobsonSpace (π.fiber x) := LocallyOfFiniteType.jacobsonSpace s
  have hx : y₀ ∈ Set.range (π.fiberι x) := by
    rw [π.range_fiberι]; rfl
  obtain ⟨y₀', -⟩ := hx
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set (π.fiber x)))
    ⟨y₀', trivial⟩ isClosed_univ.isLocallyClosed
  have h1 : LocallyOfFiniteType ((π.fiber x).fromSpecResidueField z) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hz
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((π.fiber x).fromSpecResidueField z ≫ s)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  have halg : letI := φ.hom.toAlgebra;
      Algebra.IsAlgebraic (X.residueField x) ((π.fiber x).residueField z) := by
    letI : Algebra (X.residueField x) ((π.fiber x).residueField z) := φ.hom.toAlgebra
    haveI : Algebra.FiniteType (X.residueField x) ((π.fiber x).residueField z) := hft
    haveI : Module.Finite (X.residueField x) ((π.fiber x).residueField z) :=
      finite_of_finite_type_of_isJacobsonRing _ _
    exact Algebra.IsAlgebraic.of_finite _ _
  let y : Y := π.fiberι x z
  have hy : π y = x := by
    have : y ∈ Set.range (π.fiberι x) := ⟨z, rfl⟩
    rw [π.range_fiberι] at this
    exact this
  refine ⟨y, hy, ?_⟩
  let g := (π.fiberι x).residueFieldMap z
  let ψ := π.residueFieldMap y ≫ g
  have e : Spec.map ψ ≫ X.fromSpecResidueField (π y) = Spec.map φ ≫ X.fromSpecResidueField x := by
    have e2 : π.fiberι x ≫ π = s ≫ X.fromSpecResidueField x := pullback.condition
    rw [hφ, Category.assoc, ← e2, Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]
  have hψ := isAlgebraic_residueField_transport hy ψ φ e halg
  letI : Algebra (X.residueField (π y)) (Y.residueField y) := (π.residueFieldMap y).hom.toAlgebra
  letI : Algebra (Y.residueField y) ((π.fiber x).residueField z) := g.hom.toAlgebra
  letI : Algebra (X.residueField (π y)) ((π.fiber x).residueField z) := ψ.hom.toAlgebra
  haveI : IsScalarTower (X.residueField (π y)) (Y.residueField y) ((π.fiber x).residueField z) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.IsAlgebraic.tower_bot_of_injective (R := X.residueField (π y)) (A := (π.fiber x).residueField z) g.hom.injective

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFiberIsAlgebraicResidueFieldOfLftStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_fiber_isAlgebraic_residueField_of_lft : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧ (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) := by
  first | exact @GlobalTheory.exists_mem_fiber_isAlgebraic_residueField | exact GlobalTheory.exists_mem_fiber_isAlgebraic_residueField | (intros; apply GlobalTheory.exists_mem_fiber_isAlgebraic_residueField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureEqOfIsAlgebraicResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureEqOfIsAlgebraicResidue
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ClosureDim

theorem ringKrullDim_quotient_eq_of_trdeg_residueField_eq_zero (F : Type) [Field F]
    {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra.FiniteType F A]
    (φ : A →+* B)
    (hB : @Algebra.FiniteType F B _ _ (φ.comp (algebraMap F A)).toAlgebra)
    (Q : Ideal B) [Q.IsPrime]
    (h : @Algebra.trdeg (Q.comap φ).ResidueField Q.ResidueField _ _
      (Ideal.ResidueField.map (Q.comap φ) Q φ rfl).toAlgebra = 0) :
    ringKrullDim (B ⧸ Q) = ringKrullDim (A ⧸ Q.comap φ) := by
  letI : Algebra F B := (φ.comp (algebraMap F A)).toAlgebra
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  set P := Q.comap φ
  letI : Algebra P.ResidueField Q.ResidueField := (Ideal.ResidueField.map P Q φ rfl).toAlgebra
  haveI : IsScalarTower F P.ResidueField Q.ResidueField := IsScalarTower.of_algebraMap_eq fun f ↦ by
    change algebraMap F Q.ResidueField f = Ideal.ResidueField.map P Q φ rfl (algebraMap F P.ResidueField f)
    rw [IsScalarTower.algebraMap_apply F A P.ResidueField, Ideal.ResidueField.map_algebraMap,
      IsScalarTower.algebraMap_apply F B Q.ResidueField]
    rfl
  haveI : Algebra.FiniteType F (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType F (B ⧸ Q) :=
    haveI := hB; Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F Q) Ideal.Quotient.mk_surjective
  have hfaith (S : Type) [CommRing S] [Nontrivial S] [Algebra F S] : FaithfulSMul F S :=
    (faithfulSMul_iff_algebraMap_injective F S).mpr (algebraMap F S).injective
  haveI := hfaith (A ⧸ P); haveI := hfaith (B ⧸ Q); haveI := hfaith P.ResidueField
  haveI : FaithfulSMul (A ⧸ P) P.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr P.injective_algebraMap_quotient_residueField
  haveI : FaithfulSMul (B ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Q.injective_algebraMap_quotient_residueField
  haveI : FaithfulSMul P.ResidueField Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  haveI : Algebra.IsAlgebraic (A ⧸ P) P.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ P))
  haveI : Algebra.IsAlgebraic (B ⧸ Q) Q.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (B ⧸ Q))
  have h₁ := GlobalTheory.trdeg_eq_of_isAlgebraic_top F (A ⧸ P) P.ResidueField
  have h₂ := GlobalTheory.trdeg_eq_of_isAlgebraic_top F (B ⧸ Q) Q.ResidueField
  have h₃ := trdeg_add_eq F P.ResidueField (A := Q.ResidueField)
  rw [h, add_zero] at h₃
  obtain ⟨d, hd₁, hd₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq F (A ⧸ P)
  rw [hd₁]
  exact GlobalTheory.ringKrullDim_eq_of_trdeg_eq F (B ⧸ Q) (by rw [← h₂, ← h₃, h₁, hd₂])

end GlobalTheory.ClosureDim

namespace GlobalTheory.ClosureDim

theorem dim_closure_eq_of_isAlgebraic : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X)
    (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y),
    (letI := (π.residueFieldMap y).hom.toAlgebra;
      Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) →
    topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) := by
  intro F _ Y X π sX _ _ y halg
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ (π ⁻¹ᵁ U : Set Y) from hxU)
      (π ⁻¹ᵁ U).isOpen
  have hV : IsAffineOpen V := hV
  have e : V ≤ π ⁻¹ᵁ U := hVU
  obtain ⟨p, rfl⟩ : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
  let φ := π.appLE U V e
  have hsq : Spec.map φ ≫ hU.fromSpec = hV.fromSpec ≫ π := IsAffineOpen.SpecMap_appLE_fromSpec π hU hV e
  have hpt : π (hV.fromSpec p) = hU.fromSpec (Spec.map φ p) := by
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have h0 : @Algebra.trdeg (X.residueField (π (hV.fromSpec p))) (Y.residueField (hV.fromSpec p)) _ _
      (π.residueFieldMap (hV.fromSpec p)).hom.toAlgebra = 0 := by
    letI := (π.residueFieldMap (hV.fromSpec p)).hom.toAlgebra
    exact trdeg_eq_zero (R := X.residueField (π (hV.fromSpec p))) (A := Y.residueField (hV.fromSpec p))
  rw [GlobalTheory.RelDimFibCrit.trdeg_affine π U hU V hV e p] at h0
  let ψ := Spec.preimage (hU.fromSpec ≫ sX)
  have hψ : Spec.map ψ = hU.fromSpec ≫ sX := Spec.map_preimage _
  letI : Algebra F Γ(X, U) := ψ.hom.toAlgebra
  have hA : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hB : @Algebra.FiniteType F Γ(Y, V) _ _ (φ.hom.comp (algebraMap F Γ(X, U))).toAlgebra := by
    have h : Spec.map (ψ ≫ φ) = hV.fromSpec ≫ π ≫ sX := by
      rw [Spec.map_comp, hψ, ← Category.assoc, hsq, Category.assoc]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ ≫ φ)).mp (h ▸ inferInstance)
  rw [hpt, GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient (π ≫ sX) hV.fromSpec p,
    GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient sX hU.fromSpec (Spec.map φ p)]
  haveI := p.isPrime
  exact ringKrullDim_quotient_eq_of_trdeg_residueField_eq_zero F φ.hom hB p.asIdeal h0

end GlobalTheory.ClosureDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureEqOfIsAlgebraicResidueStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_closure_eq_of_isAlgebraic_residue : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y), (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) → topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) := by
  first | exact @GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic | exact GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic | (intros; apply GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfPullbackSurjectiveProjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefDescent

theorem exists_algebraic_point : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧ (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) :=
  GlobalTheory.T.exists_mem_fiber_isAlgebraic_residueField_of_lft

theorem dim_closure_eq_of_isAlgebraic : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y), (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) → topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) :=
  GlobalTheory.T.topologicalKrullDim_closure_eq_of_isAlgebraic_residue

theorem exists_curve_over : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F),
    π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    topologicalKrullDim (Z : Set X) = 1 → ∃ C : Closeds Y, IsIrreducible (C : Set Y) ∧
      topologicalKrullDim (C : Set Y) = 1 ∧ π '' (C : Set Y) = (Z : Set X) := by
  intro F _ Y X π sX p hπ hX hY hs Z hZi hZd
  obtain ⟨hPX, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX
  obtain ⟨hPY, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hY
  subst hπ
  have : IsProper π := IsProper.of_comp π sX
  obtain ⟨η, hη⟩ := QuasiSober.sober hZi Z.isClosed
  obtain ⟨y₀, hy₀⟩ := π.surjective η
  obtain ⟨y, hy, halg⟩ := exists_algebraic_point Y X π y₀
  have hd := dim_closure_eq_of_isAlgebraic F Y X π sX y halg
  rw [hy, hy₀, hη.def] at hd
  refine ⟨Closeds.closure {y}, isIrreducible_singleton.closure, ?_, ?_⟩
  · exact hd.trans hZd
  · change π '' closure {y} = Z
    rw [← π.isClosedMap.closure_image_eq_of_continuous π.continuous, Set.image_singleton, hy, hy₀, hη.def]

theorem isNef_of_pull : ∀ (F : Type) [Field F] [NumberField F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F) (L : LB X) (hL : L.IsLB) (L' : LB Y) (hL' : L'.IsLB), π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → CechPic.pull π (cls L hL) = cls L' hL' → (letI := algebraΓOfHom p; IsNef F L') → (letI := algebraΓOfHom sX; IsNef F L) := by
  intro F _ _ Y X π sX p L hL L' hL' hπ hX hY hs hcl hnef
  letI := algebraΓOfHom sX
  letI := algebraΓOfHom p
  have hnef' : IsNef F L' := hnef
  obtain ⟨hPX, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX
  obtain ⟨hPY, A', hA'⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hY
  have : IsProper (strHom F (X := X)) := by rwa [strHom_eq (f := sX) fun _ => rfl]
  have : IsProper (strHom F (X := Y)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  refine ⟨hL, fun Z hZ => ?_⟩
  obtain ⟨C, hCi, hCd, hCZ⟩ := exists_curve_over F Y X π sX p hπ hX hY hs Z hZ.1 hZ.2
  have hC : IsCompleteCurve F C := (isCompleteCurve_iff (f := p) (fun _ => rfl)).2 ⟨hCi, hCd⟩
  by_contra hneg
  push_neg at hneg
  have hM := isLB_dual hL
  have hMpos : 0 < interNumRed F Z ![dual L] := by rw [hZ.interNumRed_dual hA hL]; linarith
  obtain ⟨r, hr, s, hs0⟩ := PosBaseChange.exists_hasNonzeroSec (k := F) hA hM hZ.1 hZ.2.le fun _ => hMpos
  have hr' := isLB_lbPow hM r
  have hZc : Closeds.closure (π '' (C : Set Y)) = Z := by
    ext1
    simp only [Closeds.coe_closure, hCZ, Z.isClosed.closure_eq]
  obtain ⟨φ, hφ⟩ : ∃ φ, φ ≫ redι Z = redι C ≫ π := ⟨IsClosedImmersion.lift (redι Z) (redι C ≫ π) (by
    rw [← hZc, Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_vanishingIdeal]), IsClosedImmersion.lift_fac _ _ _⟩
  have hsφ : Function.Surjective φ := fun z => by
    obtain ⟨y, hy, e⟩ := hCZ.ge ((range_redι Z).le ⟨z, rfl⟩)
    obtain ⟨y, rfl⟩ := (range_redι C).ge hy
    exact ⟨y, (redι Z).isClosedEmbedding.injective ((congrArg (fun q => q y) hφ).trans e)⟩
  have := isIntegral_red hC.1
  have := isIntegral_red hZ.1

  obtain ⟨z, hz⟩ : ∃ z, z ∉ nonzeroLocus s := by
    by_contra! h
    obtain ⟨t, ht⟩ := exists_isGen_of_nonzeroLocus_eq_top s (top_unique fun z _ => h z)
    have e0 := (cls_eq_zero_iff (LB.isLB_pull hr' (redι Z))).2 ⟨t, ht⟩
    have h1 : interNumRed F Z ![lbPow (dual L) r] = 0 := by
      letI := algebraΓAlong F (redι Z)
      rw [interNumRed_one_eq hr']
      exact interNum_eq_zero_of_cls_eq_zero F _ (isLB_vecOne (LB.isLB_pull hr' _)) 0 e0
    rw [hZ.interNumRed_lbPow hA hM] at h1
    have : (0 : ℤ) < r := by exact_mod_cast hr
    nlinarith
  letI := algebraΓAlong F (redι C)
  have := hC.isProper_strHom
  obtain ⟨x, hx⟩ := hsφ (genericPoint _)
  have hx' : x ∈ nonzeroLocus (secPull s φ) := (nonzeroLocus_secPull s φ).ge (by
    change φ x ∈ nonzeroLocus s
    rw [hx]; exact (sec_ne_zero_iff s).1 hs0)
  obtain ⟨c, hc⟩ := hsφ z
  have h0 := (interNum_one_nonneg_of_sec (k := F) (hA'.pull_of_isClosedImmersion (redι C))
      ((topologicalKrullDim_red C).trans hCd) (LB.isLB_pull (LB.isLB_pull hr' _) φ) (secPull s φ)
      ((sec_ne_zero_iff _).1 (sec_ne_zero_of_mem hx'))).2 (fun htop => hz (by
        have := (nonzeroLocus_secPull s φ).le (htop.ge (show c ∈ (⊤ : Opens _) from trivial))
        rw [← hc]; exact this))
  have hD' := isLB_dual hL'
  have hP' := isLB_lbPow hD' r
  have h1 : interNumRed F C ![lbPow (dual L') r] =
      interNum F (structureModule _) ![((lbPow (dual L) r).pull (redι Z)).pull φ] := by
    rw [interNumRed_one_eq hP']
    refine interNum_congr_cls F _ (isLB_vecOne (LB.isLB_pull hP' _))
      (isLB_vecOne (LB.isLB_pull (LB.isLB_pull hr' _) φ)) fun i => ?_
    fin_cases i
    change pull (redι C) (cls _ hP') = pull φ (pull (redι Z) (cls _ hr'))
    rw [← pull_comp, hφ, pull_comp, cls_lbPow hD', cls_lbPow hM, cls_dual hL', cls_dual hL, ← hcl]
    simp only [map_nsmul, map_neg]
  rw [← h1, hC.interNumRed_lbPow hA' hD', hC.interNumRed_dual hA' hL'] at h0
  have h2 := hnef'.2 C hC
  have : (0 : ℤ) ≤ r := by positivity
  nlinarith

end GlobalTheory.NefDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfPullbackSurjectiveProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective : ∀ (F : Type) [Field F] [NumberField F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F) (L : LB X) (hL : L.IsLB) (L' : LB Y) (hL' : L'.IsLB), π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → CechPic.pull π (cls L hL) = cls L' hL' → (letI := algebraΓOfHom p; IsNef F L') → (letI := algebraΓOfHom sX; IsNef F L) := by
  first | exact @GlobalTheory.NefDescent.isNef_of_pull | exact GlobalTheory.NefDescent.isNef_of_pull | (intros; apply GlobalTheory.NefDescent.isNef_of_pull <;> assumption)
end
