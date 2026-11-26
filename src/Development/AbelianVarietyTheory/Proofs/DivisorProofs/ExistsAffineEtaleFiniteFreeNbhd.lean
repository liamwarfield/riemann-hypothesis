module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicAppLE
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.GenDegAlg

theorem isAlgebraic_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (letI := (π.appLE U V h).hom.toAlgebra; Algebra.IsAlgebraic Γ(X, U) Γ(Y, V)) := by
  intro X Y _ _ π hgen hdeg U V hU hV h
  have hη : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hx : π (genericPoint Y) ∈ U := h hη
  letI : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V h).hom.toAlgebra
  letI : Algebra Γ(X, U) (X.residueField (π (genericPoint Y))) :=
    (X.evaluation U _ hx).hom.toAlgebra
  letI : Algebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  letI : Algebra Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation V _ hη).hom.toAlgebra
  letI : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := IsScalarTower.of_algebraMap_eq' rfl
  have hnat : π.appLE U V h ≫ Y.evaluation V _ hη =
      X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y) := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  haveI : IsScalarTower Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(hnat).hom).symm
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation X hU hgen hx
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  haveI : Module.Finite (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)
  haveI : Algebra.IsAlgebraic (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (IsFractionRing.comap_isAlgebraic_iff (K := X.residueField (π (genericPoint Y)))).2 inferInstance
  have hinj : Function.Injective (Y.evaluation V _ hη).hom := by
    have h1 := germ_injective_of_isIntegral Y (genericPoint Y) hη
    have h2 : Function.Injective (Y.residue (genericPoint Y)).hom :=
      RingHom.injective (show Y.functionField →+* Y.residueField (genericPoint Y) from
        (Y.residue (genericPoint Y)).hom)
    exact h2.comp h1
  exact Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom Γ(X, U) Γ(Y, V)
    (Y.residueField (genericPoint Y))) hinj

end GlobalTheory.GenDegAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeAwayMulOfFiniteType
open TensorProduct

namespace GlobalTheory

theorem free_away_mul_of_finiteType : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A] [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Module.Free A' B' := by
  intro A B _ _ _ _ _ _ _
  obtain ⟨a, ha0, hfree⟩ := (generic_freeness A).2.1 B B
  refine ⟨a, ha0, fun c A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  haveI := hA
  have hu : IsUnit (algebraMap A A' a) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := A') (a * c)
    rw [map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  letI : Algebra (Localization.Away a) A' :=
    (IsLocalization.Away.lift a (S := Localization.Away a) hu).toAlgebra
  haveI : IsScalarTower A (Localization.Away a) A' :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (IsLocalization.Away.lift_eq (S := Localization.Away a) a hu x).symm
  haveI : Module.Free (Localization.Away a) ((Localization.Away a) ⊗[A] B) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers a) B)
  haveI : Module.Free A' (A' ⊗[A] B) :=
    Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A
      (Localization.Away a) A' A' B)
  haveI hloc : IsLocalizedModule (Submonoid.powers (a * c))
      (IsScalarTower.toAlgHom A B B').toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hB
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers (a * c)) A'
    (IsScalarTower.toAlgHom A B B').toLinearMap
  exact Module.Free.of_equiv hbc.equiv

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAwayOfIsAlgebraicOfFiniteType
namespace GlobalTheory

theorem finite_away_of_isAlgebraic_of_finiteType : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Module.Finite A' B' := by
  intro A B _ _ _ _ hft halg
  obtain ⟨s, hs⟩ := hft.out
  choose y hy hint using fun b : B =>
    (Algebra.IsAlgebraic.isAlgebraic (R := A) b).exists_integral_multiple
  refine ⟨∏ b ∈ s, y b, Finset.prod_ne_zero_iff.mpr fun b _ => hy b, ?_⟩
  intro c A' B' _ _ _ _ _ _ _ _ hA' hB'
  set a := ∏ b ∈ s, y b with ha
  haveI hBB : Algebra.FiniteType B B' :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (algebraMap A B (a * c))) B'
  haveI : Algebra.FiniteType A B' := Algebra.FiniteType.trans hft hBB
  haveI : Algebra.FiniteType A' B' := .of_restrictScalars_finiteType A A' B'
  have hu : IsUnit (algebraMap A A' (a * c)) := IsLocalization.Away.algebraMap_isUnit (a * c)
  have hunit : ∀ (r : A) (m : ℕ), r ∣ (a * c) ^ m → ∃ r' : A', algebraMap A' B' r' * algebraMap A B' r = 1 := by
    intro r m hr
    obtain ⟨u, hu'⟩ := isUnit_of_dvd_unit (map_dvd (algebraMap A A') hr) (by rw [map_pow]; exact hu.pow m)
    refine ⟨↑u⁻¹, ?_⟩
    rw [IsScalarTower.algebraMap_apply A A' B', ← hu', ← map_mul, Units.inv_mul, map_one]
  haveI : Algebra.IsIntegral A' B' := by
    let S : Subalgebra A B :=
      ((integralClosure A' B').restrictScalars A).comap (IsScalarTower.toAlgHom A B B')
    have hS : Algebra.adjoin A (s : Set B) ≤ S := by
      rw [Algebra.adjoin_le_iff]
      intro b hb
      have h1 : IsIntegral A' (algebraMap B B' (y b • b)) :=
        ((hint b).map (IsScalarTower.toAlgHom A B B')).tower_top
      obtain ⟨r', hr'⟩ := hunit (y b) 1 (by rw [pow_one]; exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hb) c)
      show IsIntegral A' (algebraMap B B' b)
      have : algebraMap B B' b = algebraMap A' B' r' * algebraMap B B' (y b • b) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← mul_assoc, hr', one_mul]
      rw [this]
      exact isIntegral_algebraMap.mul h1
    rw [hs] at hS
    constructor
    intro x
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hx⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap A B (a * c))) x
    have hb : IsIntegral A' (algebraMap B B' b) := hS (Algebra.mem_top (x := b))
    obtain ⟨r', hr'⟩ := hunit ((a * c) ^ n) n dvd_rfl
    refine IsIntegral.of_mul_unit (y := algebraMap B B' (algebraMap A B (a * c) ^ n)) (r := r') ?_ ?_
    · rw [← map_pow, ← IsScalarTower.algebraMap_apply]; exact hr'
    · have hx' : x * algebraMap B B' (algebraMap A B (a * c) ^ n) = algebraMap B B' b := hx
      rw [hx']; exact hb
  exact Algebra.IsIntegral.finite

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfFiniteAppLE
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem preimage_eq_of_finite_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π] {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → IsAffineOpen V → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (π.appLE U V h).hom.Finite → π ⁻¹ᵁ U = V := by
  intro X Y _ π _ U V hU hV hne h hfin
  have : IsAffine U := hU
  have : IsAffine V := hV
  have hf : IsFinite (π.resLE U V h) := by
    have hS : IsFinite (Spec.map (π.resLE U V h).appTop) := (IsFinite.SpecMap_iff _).mpr
      ((RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso π U V h)).mpr hfin)
    rw [Arrow.iso_w' (arrowIsoSpecΓOfIsAffine (π.resLE U V h)).symm]
    infer_instance
  have : UniversallyClosed (Y.homOfLE h ≫ π ∣_ U) := by
    change UniversallyClosed (π.resLE U V h)
    infer_instance
  have : UniversallyClosed (Y.homOfLE h) := .of_comp_of_isSeparated _ (π ∣_ U)
  obtain ⟨y, hy⟩ := hne
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨y, h hy⟩⟩
  have hcl : IsClopen (Set.range (Y.homOfLE h).base) :=
    ⟨(Y.homOfLE h).isClosedMap.isClosed_range,
      (Y.homOfLE h).isOpenEmbedding.isOpenMap.isOpen_range⟩
  have huniv : Set.range (Y.homOfLE h).base = Set.univ :=
    (isClopen_iff.mp hcl).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨_, ⟨⟨y, hy⟩, rfl⟩⟩)
  refine le_antisymm (fun x hx => ?_) h
  obtain ⟨⟨w, hw⟩, hz⟩ : (⟨x, hx⟩ : π ⁻¹ᵁ U) ∈ Set.range (Y.homOfLE h).base := by
    rw [huniv]; trivial
  have hz' : ((Y.homOfLE h) ⟨w, hw⟩).1 = x := congrArg Subtype.val hz
  have hzx : w = x := (Scheme.homOfLE_apply h ⟨w, hw⟩).symm.trans hz'
  exact hzx ▸ hw

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEInjectiveOfGenericPointMap
open CategoryTheory AlgebraicGeometry
namespace GlobalTheory

theorem appLE_injective_of_genericPoint_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (π : Y ⟶ X) (hπ : π (genericPoint Y) = genericPoint X) {U : X.Opens} {V : Y.Opens}
    (hV : (V : Set Y).Nonempty) (h : V ≤ π ⁻¹ᵁ U) :
    Function.Injective (π.appLE U V h).hom := by
  have hy : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hxU : π (genericPoint Y) ∈ U := h hy
  have hF : IsField (X.presheaf.stalk (π (genericPoint Y))) :=
    isField_stalk_of_closure_mem_irreducibleComponents X _
      (by rw [hπ]; simp [irreducibleComponents_eq_singleton])
  letI := hF.toField
  have key : ∀ s, (π.stalkMap (genericPoint Y)).hom (X.presheaf.germ U _ hxU s) =
      Y.presheaf.germ V (genericPoint Y) hy ((π.appLE U V h).hom s) := by
    intro s
    rw [Scheme.Hom.germ_stalkMap_apply]
    simp [Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]
  intro s t hst
  apply germ_injective_of_isIntegral X _ hxU
  apply (π.stalkMap (genericPoint Y)).hom.injective
  rw [key, key, hst]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleAwayOfIsAlgebraic
set_option autoImplicit false

namespace GlobalTheory.GenericEtale

theorem exists_etale_away_of_isAlgebraic : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A] [CharZero A] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Algebra.Etale A' B' := by
  intro A B _ _ _ _ _ _ _ _ _ _
  haveI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  let K := FractionRing A
  let L := FractionRing B
  letI : Algebra K L := FractionRing.liftAlgebra A L
  haveI : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  haveI : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A L := Algebra.IsAlgebraic.trans A B L
  haveI : Algebra.IsAlgebraic K L := (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).1 inferInstance
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  have e1 : Algebra.FormallyEtale A K := .of_isLocalization (nonZeroDivisors A)
  have e2 : Algebra.FormallyEtale K L := .of_isSeparable K L
  have e3 : Algebra.FormallyEtale A L := .comp A K L
  have hl : IsLocalization.AtPrime L (⊥ : Ideal B) := by
    rw [IsLocalization.AtPrime, Ideal.primeCompl_bot]; infer_instance
  have e4 : Algebra.IsEtaleAt A (⊥ : Ideal B) :=
    .of_equiv ((IsLocalization.algEquiv (⊥ : Ideal B).primeCompl L
      (Localization.AtPrime (⊥ : Ideal B))).restrictScalars A)
  obtain ⟨b, hb, hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  obtain ⟨h, hh, hd⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) b).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero (by simpa using hb))
  refine ⟨h, hh, fun c A' B' _ _ _ _ _ _ _ _ hA' hB' => ?_⟩
  have e5 : Algebra.Etale A (Localization.Away (algebraMap A B (h * c))) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale] at hE ⊢
    intro x hx
    refine hE fun hxb => hx ?_
    rw [map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_of_dvd _ hd hxb)
  haveI : Algebra.Etale A B' := .of_equiv ((IsLocalization.algEquiv (.powers (algebraMap A B (h * c)))
    (Localization.Away (algebraMap A B (h * c))) B').restrictScalars A)
  haveI : Algebra.Etale A A' := .of_isLocalizationAway (h * c)
  exact Algebra.Etale.of_restrictScalars A A' B'

end GlobalTheory.GenericEtale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhd
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.GenFinEtField

theorem finrank_app_eq_residueDegree {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (h : f (genericPoint Y) = genericPoint X) {U : X.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen (f ⁻¹ᵁ U)) (hxU₀ : genericPoint X ∈ U) :
    letI := (f.app U).hom.toAlgebra
    Module.finrank Γ(X, U) Γ(Y, f ⁻¹ᵁ U) = f.residueDegree (genericPoint Y) := by
  have hxU : f (genericPoint Y) ∈ U := h ▸ hxU₀
  letI := (f.app U).hom.toAlgebra
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  letI : Algebra Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Y)).hom.toAlgebra
  letI : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (f.app U ≫ Y.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(X, U) (X.residueField (f (genericPoint Y)))
      (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.evaluation_naturality f _ hxU).hom).symm
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation X hU h hxU
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation Y hU' rfl hxU
  exact (IsFractionRing.finrank_eq Γ(X, U) (X.residueField (f (genericPoint Y)))
    Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y))).symm

theorem exists_affine_finite_etale_free : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k], IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧ (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  intro k _ X Y _ _ p q _ hX hY π hπ hg hδ
  have hpP : IsProper p := by
    obtain ⟨N, j, _, hj⟩ := hX
    have := isProper_str k N
    exact hj ▸ inferInstance
  have hqP : IsProper q := by
    obtain ⟨N, j, _, hj⟩ := hY
    have := isProper_str k N
    exact hj ▸ inferInstance
  have : IsSeparated (π ≫ p) := hπ ▸ (inferInstance : IsSeparated q)
  have hsep : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ (inferInstance : LocallyOfFiniteType q)
  have hlft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X))
  have hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀ := by
    show π (genericPoint Y) ∈ U₀
    rw [hg]; exact hxU₀
  obtain ⟨V₀, hV₀, hyV₀, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀
  haveI : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
  haveI : Nonempty V₀ := ⟨⟨_, hyV₀⟩⟩
  letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : CharZero Γ(X, U₀) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U₀ le_top).hom.charZero_iff
      (RingHom.injective (R := k) _)).1 ‹CharZero k›
  haveI : FaithfulSMul Γ(X, U₀) Γ(Y, V₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (GlobalTheory.appLE_injective_of_genericPoint_map π hg ⟨_, hyV₀⟩ hVle)
  haveI : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle
  haveI : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) := GlobalTheory.GenDegAlg.isAlgebraic_appLE π hg hδ hU₀ ⟨_, hyV₀⟩ hVle
  obtain ⟨a₁, ha₁, H₁⟩ := GlobalTheory.finite_away_of_isAlgebraic_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₂, ha₂, H₂⟩ := GlobalTheory.free_away_mul_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₃, ha₃, H₃⟩ := GlobalTheory.GenericEtale.exists_etale_away_of_isAlgebraic (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  have ha : a₁ * a₂ * a₃ ≠ 0 := mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃
  have hUU₀ : X.basicOpen (a₁ * a₂ * a₃) ≤ U₀ := X.basicOpen_le _
  have hUa : IsAffineOpen (X.basicOpen (a₁ * a₂ * a₃)) := hU₀.basicOpen _
  have hxU : genericPoint X ∈ X.basicOpen (a₁ * a₂ * a₃) := by
    have hne : X.basicOpen (a₁ * a₂ * a₃) ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff _).1 h)
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (a₁ * a₂ * a₃)).isOpen).2
      ⟨z, trivial, hz⟩
  set U : X.Opens := X.basicOpen (a₁ * a₂ * a₃) with hU_def
  set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle (a₁ * a₂ * a₃)) with hV_def
  have hVV₀ : V ≤ V₀ := Y.basicOpen_le _
  have hVe : V = V₀ ⊓ π ⁻¹ᵁ U := Scheme.basicOpen_appLE π V₀ U₀ hVle _
  have hVU : V ≤ π ⁻¹ᵁ U := by rw [hVe]; exact inf_le_right
  have hVa : IsAffineOpen V := hV₀.basicOpen _
  have hyV : genericPoint Y ∈ V := by
    rw [hVe]; exact ⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩
  letI iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  letI iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra
  letI iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra
  letI iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)
  haveI : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)
  haveI hlA : IsLocalization.Away (a₁ * a₂ * a₃) Γ(X, U) :=
    hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl
  haveI hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) (a₁ * a₂ * a₃)) Γ(Y, V) :=
    hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl
  have e1 : a₁ * (a₂ * a₃) = a₁ * a₂ * a₃ := (mul_assoc _ _ _).symm
  have e2 : a₂ * (a₁ * a₃) = a₁ * a₂ * a₃ := by ring
  have e3 : a₃ * (a₁ * a₂) = a₁ * a₂ * a₃ := by ring
  have hfin : Module.Finite Γ(X, U) Γ(Y, V) :=
    H₁ (a₂ * a₃) Γ(X, U) Γ(Y, V) (by rw [e1]; exact hlA) (by rw [e1]; exact hlB)
  have hfree : Module.Free Γ(X, U) Γ(Y, V) :=
    H₂ (a₁ * a₃) Γ(X, U) Γ(Y, V) (by rw [e2]; exact hlA) (by rw [e2]; exact hlB)
  have het : Algebra.Etale Γ(X, U) Γ(Y, V) :=
    H₃ (a₁ * a₂) Γ(X, U) Γ(Y, V) (by rw [e3]; exact hlA) (by rw [e3]; exact hlB)
  have hpre : π ⁻¹ᵁ U = V := GlobalTheory.preimage_eq_of_finite_appLE π hUa hVa ⟨_, hyV⟩ hVU hfin
  have key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U → (π.appLE U W hW).hom.Etale →
      (π.appLE U W hW).hom.Finite →
      (letI := (π.appLE U W hW).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, W)) →
      (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    rintro W hW rfl h1 h2 h3
    rw [Scheme.Hom.app_eq_appLE]
    exact ⟨h1, h2, h3⟩
  obtain ⟨h1, h2, h3⟩ := key V hVU hpre.symm het hfin hfree
  exact ⟨U, hUa, hxU, hpre ▸ hVa, h1, h2, h3, finrank_app_eq_residueDegree π hg hUa (hpre ▸ hVa) hxU⟩

end GlobalTheory.GenFinEtField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhdStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_etale_finite_free_nbhd : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k], IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧ (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  first | exact @GlobalTheory.GenFinEtField.exists_affine_finite_etale_free | exact GlobalTheory.GenFinEtField.exists_affine_finite_etale_free | (intros; apply GlobalTheory.GenFinEtField.exists_affine_finite_etale_free <;> assumption)
end
