module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAfterExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicity
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexLinearExtensionCoefficientMap
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondence
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem isReduced_of_pReg_of_factor (p : ℕ) {Y₀ Y : Scheme.{0}} [IsReduced Y₀] (i : Y₀ ⟶ Y) [IsOpenImmersion i]
    (hp : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0)
    (hfac : ∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) :
    IsReduced Y := by

  have haff : ∀ (V : Y.Opens), IsAffineOpen V → ∀ g : Γ(Y, V), IsNilpotent g → g = 0 := by
    intro V hV g hg
    let q : Γ(Y, V) := (p : Γ(Y, V))
    let O := Y.basicOpen q
    let ρ : Γ(Y, V) →+* Γ(Y, O) := (Y.presheaf.map (homOfLE (Y.basicOpen_le q)).op).hom
    letI : Algebra Γ(Y, V) Γ(Y, O) := ρ.toAlgebra
    haveI : IsLocalization.Away q Γ(Y, O) := hV.isLocalization_basicOpen q
    have hu : IsUnit ((p : ℕ) : Γ(O.toScheme, ⊤)) := by
      have h1 : IsUnit (algebraMap Γ(Y, V) Γ(Y, O) q) := IsLocalization.Away.algebraMap_isUnit q
      rw [map_natCast] at h1
      have := h1.map (O.topIso.inv.hom)
      rwa [map_natCast] at this
    obtain ⟨f₀, hf₀⟩ := hfac O.toScheme O.ι hu
    haveI : IsOpenImmersion (f₀ ≫ i) := hf₀ ▸ inferInstance
    haveI : IsOpenImmersion f₀ := IsOpenImmersion.of_comp f₀ i
    haveI : IsReduced O.toScheme := isReduced_of_isOpenImmersion f₀
    haveI : _root_.IsReduced Γ(Y, O) :=
      isReduced_of_injective (O.topIso.inv.hom) (O.topIso.commRingCatIsoToRingEquiv.symm.injective)
    have h0 : algebraMap Γ(Y, V) Γ(Y, O) g = 0 := (hg.map (algebraMap Γ(Y, V) Γ(Y, O))).eq_zero
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers q) _ g).1 h0
    have hk' : q ^ k * g = 0 := hk
    clear hk h0
    induction k with
    | zero => simpa using hk'
    | succ k ih => exact ih (hp V _ (by rw [pow_succ', _root_.mul_assoc] at hk'; exact hk'))
  refine ⟨fun U => ⟨fun f hf => ?_⟩⟩
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · rw [map_zero]
    exact haff V.1.1 V.1.2 _ (hf.map _)

theorem isReduced_normalModel_of_generic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  intro p _ D R _ _ _ _ b N _ M Y₀ s₀ gs hgs _ Y s i _ _ hfl hfac
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsReduced Y₀ := GlobalTheory.isReduced_of_smooth_of_isReduced (gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s)
  have hR : ∀ a : R, (p : R) * a = 0 → a = 0 := fun a ha =>
    (mul_eq_zero.1 ha).resolve_left (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  haveI := hfl
  exact isReduced_of_pReg_of_factor p i (fun U f hf => pReg_of_flat (p := p) (s ≫ M.s) hR U f hf) hfac

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_normalModel_generic_correspondence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  first | (exact @GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic) | (exact GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic) | (intros; apply GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem isInv_constFn (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hv : IsInv G v dd) (O : G.left.Opens) (r : R) :
    dd O (constFn G.hom O r) = 0 := by
  refine TopCat.Presheaf.section_ext G.left.sheaf O _ _ fun y hy => ?_
  let g : Sp (G.left.presheaf.stalk y) ⟶ G.left := G.left.fromSpecStalk y
  let φ : R →+* G.left.presheaf.stalk y := (Spec.preimage (g ≫ G.hom)).hom
  have hφ : g ≫ G.hom = spMap φ := (Spec.map_preimage (g ≫ G.hom)).symm
  have ht : ⊤ ≤ g ⁻¹ᵁ O := by
    intro z _
    have hz : g z ∈ Set.range g := ⟨z, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hz
    exact hz.mem_open O.isOpen hy
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C),
      spMap (f'.comp f) = spMap f' ≫ spMap f := by
    intro A B C _ _ _ f f'
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  let g' : tEpsG (g ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (algebraMap _ (DualNumber (G.left.presheaf.stalk y))) ≫ g) (by simp)
  have hdual : (dualMap φ).comp (algebraMap R (DualNumber R)) =
      (algebraMap _ (DualNumber (G.left.presheaf.stalk y))).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : tEpsG (g ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (dualMap φ) ≫ (tv v).left) (by
      rw [Category.assoc, Over.w (tv v)]
      simp only [Over.mk_hom, Category.comp_id]
      rw [← hcomp, hdual, hcomp, hφ])
  have key := hv.2 _ φ g (g' * v').left O (constFn G.hom O r) hφ ht ⟨g', v', rfl, rfl, rfl⟩
  have h0 : (valR (g' * v').left O (constFn G.hom O r)).snd = 0 := by
    by_cases hw : ⊤ ≤ (g' * v').left ⁻¹ᵁ O
    · rw [GlobalTheory.Points.valR_constFn_of_over G.hom ((algebraMap _ (DualNumber (G.left.presheaf.stalk y))).comp φ)
        _ ?_ O hw r]
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [Over.w (g' * v'), hcomp]
        simp only [Over.mk_hom]
        rw [hφ]
    · simp [valR, dif_neg hw]
  rw [h0] at key
  exact ((GlobalTheory.FormalValue.valR_fromSpecStalk y O hy _).symm.trans key.symm).trans
    (map_zero (G.left.presheaf.germ O y hy).hom).symm

end GlobalTheory.Heat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_apply_constant_eq_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ O r, dd O (constFn G.hom O r) = 0 := by
  first | exact @GlobalTheory.Heat.isInv_constFn | exact GlobalTheory.Heat.isInv_constFn | (intros; apply GlobalTheory.Heat.isInv_constFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalFlatOfSmoothOverRegularLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalFlatOfSmoothOverRegularLocal
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SmoothStalkNormal

theorem flat_fromSpecStalk' (X : Scheme.{0}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

theorem injective_of_flat_of_isDomain {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Nontrivial B] (f : A →+* B) (hf : f.Flat) : Function.Injective f := by
  algebraize [f]
  refine (injective_iff_map_eq_zero f).2 fun r hr => ?_
  by_contra h0
  have hreg : IsSMulRegular B r :=
    Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero h0)
  have h1 : r • (1 : B) = r • (0 : B) := by
    rw [smul_zero, Algebra.smul_def, _root_.mul_one]; exact hr
  exact one_ne_zero (hreg h1)

theorem stalk_of_smooth_over_regular :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (X : Scheme.{0}) (p : X ⟶ Sp R), Smooth p →
      ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧
        IsIntegrallyClosed (X.presheaf.stalk x) ∧
        (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat ∧
        Function.Injective (Spec.preimage (X.fromSpecStalk x ≫ p)).hom := by
  intro R _ _ X p hp x
  haveI : Smooth p := hp
  haveI : IsRegularRing (CommRingCat.of R) := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth p x
  obtain ⟨hdom, hint⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (X.presheaf.stalk x)
  have hRdom : IsDomain R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).1
  have hfl : (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat := by
    haveI := flat_fromSpecStalk' X x
    have h : Flat (Spec.map (Spec.preimage (X.fromSpecStalk x ≫ p))) := by
      rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
  refine ⟨hdom, inferInstance, hint, hfl, ?_⟩
  exact injective_of_flat_of_isDomain (A := R) _ hfl

end GlobalTheory.SmoothStalkNormal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalFlatOfSmoothOverRegularLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_normal_flat_of_smooth_over_regular_local : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (X : Scheme.{0}) (p : X ⟶ Sp R), Smooth p → ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧ (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat ∧ Function.Injective (Spec.preimage (X.fromSpecStalk x ≫ p)).hom := by
  first | exact @GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular | exact GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular | (intros; apply GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaEqOfMkEq
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

def ValAt {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) (p : (torsion G n).left) (c : M) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ Spec ((torsion G n).left.presheaf.stalk p)) (z : Sp Ω ⟶ V),
    y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom = z ≫ ℓ →
      y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion.ι G n).left = z ≫ w c

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem etaSec_w (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) :
    (i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ) ≫ TF.Y.t.G.hom = ℓ ≫ φ ≫ (barComp TF.Y Z).ι := by
  have h1 := TF.Y.m.cart.1.w
  have h2 := Over.w (TF.Y.oF.eta b)
  simp only [Category.assoc] at h1 ⊢
  rw [h1, ← Category.assoc ((TF.Y.oF.eta b).left), h2, reassoc_of% hℓ, j₀_ι]
  exact congrArg (i₀ TF.Y Z ≫ ·) (Category.id_comp _)

def etaSec (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left :=
  pullback.lift _ _ (etaSec_w TF Z φ ℓ hℓ b)

theorem eta_eq_of_mk_eq (TF : TorFlag Xo c) {b b' : Dw.La}
    (h : (Submodule.Quotient.mk b : LevelMod Dw l) = Submodule.Quotient.mk b') :
    TF.Y.oF.eta b = TF.Y.oF.eta b' := by
  rw [Submodule.Quotient.eq] at h
  have := TF.Y.oF.eta_add b' (b - b')
  rwa [add_sub_cancel, TF.Y.oF.eta_ker _ h, mul_one] at this

def etaSecL (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (x : LevelMod Dw l) : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left :=
  Quot.liftOn x (etaSec TF Z φ ℓ hℓ) fun b b' h => by
    have e := eta_eq_of_mk_eq TF (b := b) (b' := b') (Quot.sound h)
    unfold etaSec
    congr 2
    rw [e]

theorem etaSecL_w (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (x : LevelMod Dw l) :
    etaSecL TF Z φ ℓ hℓ x ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = ℓ := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact pullback.lift_snd _ _ _

theorem etaSecL_ψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) :
    etaSecL TF Z φ ℓ hℓ (Submodule.Quotient.mk b) ≫ GlobalTheory.EqvAct.pullψ TF Z φ =
      i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ :=
  pullback.lift_fst _ _ _

end GlobalTheory.TorsSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenFrameChartVectorsCompactFlagSpaceAffi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenFrameChartVectorsCompactFlagSpaceAffi
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

section
open GlobalTheory.FlagMod GlobalTheory.Reg
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompHS.exists_eigFrame_vecAt₀ : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(Y₀ TF.X Z, W)), (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ → ∀ (k : TF.X.F.J) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (x' : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.Y.X) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x'), ∃ fr : GlobalTheory.ShFam.EigFrame TF.Y φ x', ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt k _ hz hx τ j)).left := by
  intro E _ _ _ H Dw l Xo c TF Z W hW φ hφ k hz x' hx
  subst hx
  haveI := TF.X.proper
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim TF.Y.s
  haveI : LocallyOfFiniteType TF.Y.s := inferInstance
  haveI : LocallyOfFiniteType (str₀ TF.X Z) := by unfold str₀ flagStr; infer_instance
  haveI : IsLocallyNoetherian (Y₀ TF.X Z) := LocallyOfFiniteType.isLocallyNoetherian (str₀ TF.X Z)
  obtain ⟨K, _, ρ, hρ, hK⟩ := GlobalTheory.T.affineOpen_ring_injects_to_ring_mapping_to_dense (Y₀ TF.X Z) (U₀ TF.X Z) (dense_U₀ TF.X Z) W hW
  letI : Algebra c.F K := (ρ.comp φ).toAlgebra
  have hz' : ⊤ ≤ (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ⁻¹ᵁ TF.X.F.U k := FlagMod.le_preimage_comp _ hz
  have hr : Set.range ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) ⊆ Set.range TF.Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hK (Set.mem_univ s)
  let yK := IsOpenImmersion.lift TF.Y.j ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) hr
  have hyK : yK ≫ TF.Y.j = (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π := IsOpenImmersion.lift_fac _ _ _
  have hjs : TF.Y.j ≫ TF.Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
      unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over, h1, Category.comp_id]
  have hy : yK ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← hjs, ← Category.assoc, hyK]
    have h2 : spMap ρ ≫ spMap φ = spMap (algebraMap c.F K) := by
      unfold spMap; rw [← Spec.map_comp]; rfl
    rw [← h2, ← hφ]
    simp only [Category.assoc]
  have key : ∀ (x'' : Sp K ⟶ TF.Y.X) (hx : (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π = x''),
      (∀ σ, initSpan K (TF.X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (TF.X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) =
        eigLie c ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) σ := by
    rintro x'' rfl h
    exact h
  exact GlobalTheory.ChartEigFrame.exists_eigFrame_of_top ρ hρ φ rfl (hW.fromSpec ≫ inc₀ TF.X Z) k hz hz'
    (key _ hyK.symm fun σ => TF.X.top K yK hy _ hyK.symm k hz' σ)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenFrameChartVectorsCompactFlagSpaceAffiStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenFrame_chartVectors_compactFlagSpace_affine : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(Y₀ TF.X Z, W)), (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ → ∀ (k : TF.X.F.J) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (x' : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.Y.X) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x'), ∃ fr : GlobalTheory.ShFam.EigFrame TF.Y φ x', ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt k _ hz hx τ j)).left := by
  first | exact @GlobalTheory.CompHS.exists_eigFrame_vecAt₀ | exact GlobalTheory.CompHS.exists_eigFrame_vecAt₀ | (intros; apply GlobalTheory.CompHS.exists_eigFrame_vecAt₀ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasSatakeOfUnrT
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspRep.ParLawsT


open GlobalTheory.CuspRep.ParLaws in
theorem hasSatake_of_repEquiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) k) V} {π' : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv π')
    (hirr : π'.IsIrreducible) {α : Fin n → ℂˣ} (h : HasSatake π α) : HasSatake π' α :=
  ⟨hirr, fixed_ne_bot_of_equiv φ h.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans h.2.2⟩

end GlobalTheory.CuspRep.ParLawsT

namespace GlobalTheory.CuspRep.ParLawsT

open GlobalTheory.CuspRep.ParLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

theorem locParT_eq_locComp [_root_.NumberField.IsTotallyComplex E] (hT : UpperTheory.Zero.LLC.RecTExists) {π : CuspSub E a}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) (h : IsPlaceOver A w) :
    locParT hT (CG.mk π) h = locRecT hT h (cls (toRep σ)) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [locParT, CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

theorem locRecT_sat (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) (σ : IrrRep (GL (Fin a) (w.adicCompletion E)))
    {α : Fin a → ℂˣ} (hα : HasSatake σ.ρ α) : locRecT hT h (cls σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨b, hb, H⟩ := isRecT_locRecT hT h
  exact GlobalTheory.RecT.SphLaw.sat ((GlobalTheory.RecT.lawsT_iff b hb _).2 H) (cls σ) α
    (hasSatake_of_repEquiv (equivRep σ) (IrrRep.irr _) hα)

theorem exists_hasSatake_of_unrT (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w)
    {σ : IrrRep (GL (Fin a) (w.adicCompletion E))} (hu : (locRecT hT h (cls σ)).unr) : ∃ α, HasSatake σ.ρ α := by
  obtain ⟨b, hb, H⟩ := isRecT_locRecT hT h
  have hs := (GlobalTheory.RecT.isSpherical_iff_unr_of_lawsT E Ω A w h b hb _ ((GlobalTheory.RecT.lawsT_iff b hb _).2 H) (cls σ)).2 hu
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) a
    ⟨(cls σ).2.rep.V, (cls σ).2.rep.ρ, (cls σ).2.rep.smooth, (cls σ).2.rep.irr⟩ hs
  exact ⟨α, hasSatake_of_repEquiv (equivRep σ).symm σ.irr hα⟩

end GlobalTheory.CuspRep.ParLawsT

namespace GlobalTheory.CuspRep.ParLawsT

open GlobalTheory.CuspRep.ParLaws

theorem csd_unrT : ∀ (hT : UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (a : ℕ) (π : CG L a), π.IsCsd → ∀ (w w' : HeightOneSpectrum (𝓞 L)), ConjPl (IsCMField.complexConj L).toRingEquiv w w' → ∀ (A A' : ValuationSubring Ω) (h : IsPlaceOver A w) (h' : IsPlaceOver A' w'), (locParT hT π h).unr → (locParT hT π h').unr ∧ (locParT hT π h').frobEig = (locParT hT π h).frobEig.map (·⁻¹) := by
  intro hT hF L Ω _ _ _ _ _ _ a π hπ w w' hc A A' h h' hu
  obtain rfl : w' = conjSrc (IsCMField.complexConj L).toRingEquiv w := eq_conjSrc fun x => by
    simpa using (hc (IsCMField.complexConj L x)).symm
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF L a π w
  have e : locParT hT (Quotient.mk _ π) h = _ := locParT_eq_locComp hT hσ h
  have e' : locParT hT (Quotient.mk _ π) h' = _ := locParT_eq_locComp hT (isLocComp_flip hπ hσ) h'
  rw [e] at hu
  obtain ⟨α, hα⟩ := exists_hasSatake_of_unrT hT h hu
  rw [e, e', locRecT_sat hT h _ hα, locRecT_sat hT h' _ (hasSatake_flip_conjLoc _ w hα),
    WD.frobEig_diag, WD.frobEig_diag, Multiset.map_map]
  refine ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), ?_⟩
  conv_rhs => rw [← Finset.map_univ_equiv Fin.revPerm, Finset.map_val, Multiset.map_map]
  simp

end GlobalTheory.CuspRep.ParLawsT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsPol

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem polOnAb_genPt : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsOpen (abLocus G) →
    genericPoint S ∈ abLocus G → PolOnAb G L.L → PolOnAb (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)).L := by
  intro S _ G _ _ L hO hg hpol V _
  obtain ⟨U, hU, hp, hUs⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⟨abLocus G, hO⟩) (x := genericPoint S) hg
  obtain ⟨ha, hk⟩ := hpol U hUs
  obtain ⟨f, hf⟩ : ∃ f : V.toScheme ⟶ U.toScheme, f ≫ U.ι = V.ι ≫ KeyVals.genPt S :=
    ⟨IsOpenImmersion.lift U.ι (V.ι ≫ KeyVals.genPt S) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact KeyVals.genPt_le U hp (Set.mem_univ (V.ι y))), IsOpenImmersion.lift_fac _ _ _⟩
  have h := isGrpPullback_pullback G (KeyVals.genPt S)
  have h' := isGrpPullback_pullback (KeyVals.bG G (KeyVals.genPt S)) V.ι
  have h₀ := isGrpPullback_pullback G U.ι
  have h₂ := (h'.comp h).congr hf.symm rfl
  let A' := (Over.pullback V.ι).obj (KeyVals.bG G (KeyVals.genPt S))
  let a : (KeyVals.bG G (KeyVals.genPt S)).left ⟶ G.left := pullback.fst G.hom (KeyVals.genPt S)
  let b : A'.left ⟶ (KeyVals.bG G (KeyVals.genPt S)).left := pullback.fst (KeyVals.bG G (KeyVals.genPt S)).hom V.ι
  let ψ : A'.left ⟶ ((Over.pullback U.ι).obj G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst G.hom U.ι = b ≫ a := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback A' ((Over.pullback U.ι).obj G) f ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hL := pull_isLB (pull_isLB L.isLB a) b
  have hL₀ := pull_isLB L.isLB (pullback.fst G.hom U.ι)
  obtain ⟨w, hw⟩ : LBIso ((L.L.pull a).pull b) ((L.L.pull (pullback.fst G.hom U.ι)).pull ψ) :=
    LBIso.chartPull
      (chartPullLinComb L.L a (fun _ : PUnit => b) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
        fun _ => (Category.id_comp _).symm)
      (chartPullLinComb L.L _ (fun _ : PUnit => ψ) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
        fun _ => hψ.trans (Category.id_comp _).symm)
      (lbIso_self (pull_isLB L.isLB (b ≫ a)))
  have : IsAffine U.toScheme := hU
  exact ⟨relAmple_pull h₃.1 hL₀ hL ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) ha,
    kTriv_pull h₃ hL₀ hL ((isGen_iff w).1 hw) hk⟩

end GlobalTheory.KeyValsPol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarisationOnAbLocus_genericFibre : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsOpen (abLocus G) →
    genericPoint S ∈ abLocus G → PolOnAb G L.L → PolOnAb (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)).L := by
  first | exact @GlobalTheory.KeyValsPol.polOnAb_genPt | exact GlobalTheory.KeyValsPol.polOnAb_genPt | (intros; apply GlobalTheory.KeyValsPol.polOnAb_genPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFormOfTensorSectionInChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFormOfTensorSectionInChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsSec

theorem gm_pull_g {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (f : Y ⟶ X') (y : Y) (J J' : PUnit → L.ι)
    (hj : F (f y) ∈ L.U (J PUnit.unit)) (hj' : F (f y) ∈ L.U (J' PUnit.unit)) :
    gm f y ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (f ≫ F) y _ (L.g (J PUnit.unit) (J' PUnit.unit)) := by
  have hp : f y ∈ (L.pull F).U J ⊓ (L.pull F).U J' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U _ ⊓ L.U _) ⟨hj, hj'⟩ _)

theorem exists_sec_of_chart {X X' : Scheme.{0}} (A B : LB X) (hB : B.IsLB) (σ : (CechPic.tens A B).Sec) (b : B.ι)
    (F : X' ⟶ X) (hb : ∀ y : X', F y ∈ B.U b) :
    ∃ t : (A.pull F).Sec, ∀ (j : (A.pull F).ι)
      (h : (A.pull F).U j ≤ F ⁻¹ᵁ (CechPic.tens A B).U (j PUnit.unit, b)),
      t.f j = (F.appLE _ _ h).hom (σ.f (j PUnit.unit, b)) := by
  have hle : ∀ j : (A.pull F).ι, (A.pull F).U j ≤ F ⁻¹ᵁ (CechPic.tens A B).U (j PUnit.unit, b) :=
    fun j y hy => ⟨mem_pull.1 hy, hb y⟩
  refine ⟨⟨fun j => (F.appLE _ _ (hle j)).hom (σ.f (j PUnit.unit, b)), fun j j' => ?_⟩, fun _ _ => rfl⟩
  apply TopCat.Presheaf.section_ext X'.sheaf
  intro y hy
  have hy' : (𝟙 X' : X' ⟶ X') y ∈ (A.pull F).U j ⊓ (A.pull F).U j' := hy
  have hj : F y ∈ A.U (j PUnit.unit) := mem_pull.1 hy.1
  have hj' : F y ∈ A.U (j' PUnit.unit) := mem_pull.1 hy.2
  have hp : (𝟙 X' ≫ F) y ∈ (CechPic.tens A B).U (j PUnit.unit, b) := ⟨hj, hb y⟩
  have hq : (𝟙 X' ≫ F) y ∈ (CechPic.tens A B).U (j' PUnit.unit, b) := ⟨hj', hb y⟩
  have e := gs_compat σ (𝟙 X' ≫ F) y hp hq
  have e₁ := CechPic.gm_tens A B (𝟙 X' ≫ F) y (j PUnit.unit, b) (j' PUnit.unit, b) hp hq
  rw [gm_self hB (𝟙 X' ≫ F) y hp.2, _root_.mul_one] at e₁
  rw [e₁] at e
  refine (gs_eq (𝟙 X') y _ hy' _).symm.trans (Eq.trans ?_ (gs_eq (𝟙 X') y _ hy' _))
  refine (gs_res _ y _ hy' _).trans ((gs_appLE F _ _ _ (𝟙 X') y hy'.1 _).trans (e.trans ?_))
  refine Eq.trans ?_ (gs_mul _ y _ hy' _ _).symm
  refine congrArg₂ (· * ·) ?_ ((gs_res _ y _ hy' _).trans (gs_appLE F _ _ _ (𝟙 X') y hy'.2 _)).symm
  exact ((gs_unit _ y _ hy' _).trans (congrArg Units.val (gm_pull_g A F (𝟙 X') y j j' hj hj'))).symm

theorem exists_locSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    δ.IsLB → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → ∃ t : (KeyVals.bL L ξ).L.Sec, KeyVals.IsLocSec σ i ξ t := by
  intro S G _ _ L δ σ i R _ ξ hδ hξ
  refine exists_sec_of_chart L.L (δ.pull G.hom) (LB.isLB_pull hδ _) σ (fun _ => i) (pullback.fst G.hom ξ) fun y => ?_
  refine mem_pull.2 ?_
  have h : (pullback.fst G.hom ξ ≫ G.hom) y ∈ δ.U i := by
    rw [pullback.condition]
    exact hξ (Set.mem_univ (pullback.snd G.hom ξ y))
  exact h

end GlobalTheory.KeyValsSec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFormOfTensorSectionInChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localFormOfTensorSection_in_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    δ.IsLB → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → ∃ t : (KeyVals.bL L ξ).L.Sec, KeyVals.IsLocSec σ i ξ t := by
  first | exact @GlobalTheory.KeyValsSec.exists_locSec | exact GlobalTheory.KeyValsSec.exists_locSec | (intros; apply GlobalTheory.KeyValsSec.exists_locSec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRules
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRules
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FamCalc

variable {S : Scheme.{0}} {A : Over S}

theorem whisker_eq {Y T : Over S} (y : Y ⟶ T) : A ◁ y = lift (fst A Y) (snd A Y ≫ y) := by
  ext <;> simp

theorem lift_whisker {Y T Z : Over S} (y : Y ⟶ T) (a : Z ⟶ A) (t : Z ⟶ Y) :
    lift a t ≫ A ◁ y = lift a (t ≫ y) := by
  ext <;> simp

theorem pull_whisker_evc {T Y Z : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T) (a : Z ⟶ A)
    (t : Z ⟶ Y) :
    CechPic.pull (lift a t).left (CechPic.pull (A ◁ y).left (cls N hN)) = evc hN a (t ≫ y) := by
  rw [← pull_comp, ← Over.comp_left, lift_whisker, evc]

theorem evc_whisker {T Y : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T) :
    evc hN (fst A Y) (snd A Y ≫ y) = CechPic.pull (A ◁ y).left (cls N hN) := by
  rw [evc, whisker_eq]

theorem evc_ev_whisker {T Y Z : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T)
    (h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB) (a : Z ⟶ A) (t : Z ⟶ Y) :
    evc h a t = evc hN a (t ≫ y) := by
  rw [evc_ev hN, lift_fst, lift_snd_assoc]

theorem famCalc : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], (∀ (T Y : Over S) (N : LB (A ⊗ T).left) (y : Y ⟶ T), Fam A N → Fam A (ev N (fst A Y) (snd A Y ≫ y))) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : Fam A N) (hM : Fam A M) (y : Y ⟶ T) (u : Y ⟶ U) (D : LB (A ⊗ Y).left) (hD : D.IsLB), (cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) + GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB) ∨ cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) - GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB)) → Fam A D) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : N.IsLB) (hM : M.IsLB) (y : Y ⟶ T) (u : Y ⟶ U), Same A N M y u ↔ GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN) = GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) (z : Z ⟶ Y), N.IsLB → M.IsLB → Same A N M y u → Same A N M (z ≫ y) (z ≫ u)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (z : Z ⟶ Y) (u : Z ⟶ U), N.IsLB → M.IsLB → (Same A (ev N (fst A Y) (snd A Y ≫ y)) M z u ↔ Same A N M (z ≫ y) u)) := by
  intro S A _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T Y N y hN
    have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
    refine ⟨h, (isAdditive_iff h).2 fun Z a a' t ↦ ?_⟩
    simp only [evc_ev_whisker hN.isLB y h]
    exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)
  · intro T U Y N M hN hM y u D hD hc
    refine ⟨hD, (isAdditive_iff hD).2 fun Z a a' t ↦ ?_⟩
    have aN := (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)
    have aM := (isAdditive_iff hM.isLB).1 hM.add Z a a' (t ≫ u)
    rcases hc with hc | hc
    · have e : ∀ b : Z ⟶ A, evc hD b t = evc hN.isLB b (t ≫ y) + evc hM.isLB b (t ≫ u) := fun b ↦ by
        rw [evc, hc, map_add (f := _), pull_whisker_evc, pull_whisker_evc]
      rw [e, e, e, aN, aM]
      abel
    · have e : ∀ b : Z ⟶ A, evc hD b t = evc hN.isLB b (t ≫ y) - evc hM.isLB b (t ≫ u) := fun b ↦ by
        rw [evc, hc, map_sub, pull_whisker_evc, pull_whisker_evc]
      rw [e, e, e, aN, aM]
      abel
  · intro T U Y N M hN hM y u
    rw [same_iff hN hM, evc_whisker, evc_whisker]
  · intro T U Y Z N M y u z hN hM h
    rw [same_iff hN hM] at h ⊢
    have e := congrArg (CechPic.pull (A ◁ z).left) h
    rwa [pull_evc, pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd_assoc] at e
  · intro T U Y Z N M y z u hN hM
    have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN _
    rw [same_iff h hM, same_iff hN hM, evc_ev_whisker hN y h, Category.assoc]

end GlobalTheory.FamCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRulesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveLineBundleFamily_calculus_rules : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], (∀ (T Y : Over S) (N : LB (A ⊗ T).left) (y : Y ⟶ T), Fam A N → Fam A (ev N (fst A Y) (snd A Y ≫ y))) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : Fam A N) (hM : Fam A M) (y : Y ⟶ T) (u : Y ⟶ U) (D : LB (A ⊗ Y).left) (hD : D.IsLB), (cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) + GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB) ∨ cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) - GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB)) → Fam A D) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : N.IsLB) (hM : M.IsLB) (y : Y ⟶ T) (u : Y ⟶ U), Same A N M y u ↔ GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN) = GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) (z : Z ⟶ Y), N.IsLB → M.IsLB → Same A N M y u → Same A N M (z ≫ y) (z ≫ u)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (z : Z ⟶ Y) (u : Z ⟶ U), N.IsLB → M.IsLB → (Same A (ev N (fst A Y) (snd A Y ≫ y)) M z u ↔ Same A N M (z ≫ y) u)) := by
  first | exact @GlobalTheory.FamCalc.famCalc | exact GlobalTheory.FamCalc.famCalc | (intros; apply GlobalTheory.FamCalc.famCalc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjCoefAt
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem scale_pow_eq_of_isScale {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := _root_.GlobalTheory.BigOn.Exp.isScale_pow_eq (D := D) (Γ := Γ) (Pl0 := Pl0) (I0 := I0) (T := T) (A3 := A3) (Ks := Ks) (j := j) (c := c) (c' := c') Rl v₀ B h h'

theorem coefFn_map_eq {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n)
    (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) : coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  simp only [coefFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, RingHom.id_comp]

theorem exists_fixed_of_mem_span {D : D7} (j : Fin D.R.m) {W M : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
    (Φ : W →ₗ[ℂ] M) (c : VsV D j ℂ →ₗ[ℂ] W) (a₀ : ℂ) (S : Set (VV (↥D.LL0) (lamV D j))) {P : M}
    (hP : P ∈ Submodule.span (smallInt D)
      {P | ∃ Fv ∈ S, P = Φ (c (a₀ • GlobalTheory.CoefModel.mapVV (Formalism.L2.Host.embLL0 D) (lamV D j) Fv))}) :
    ∃ y : VsV D j ℂ, P = a₀ • Φ (c y) ∧
      ∀ τ : ℂ ≃+* ℂ, (∀ z, τ (Formalism.L2.Host.embLL0 D z) = Formalism.L2.Host.embLL0 D z) → ConjVec j τ y y := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨Fv, -, rfl⟩ := hP
    refine ⟨GlobalTheory.CoefModel.mapVV (Formalism.L2.Host.embLL0 D) (lamV D j) Fv, by rw [c.map_smul, Φ.map_smul], fun τ hτ => ?_⟩
    change MvPolynomial.map _ _ = MvPolynomial.map _ (MvPolynomial.map _ _)
    rw [MvPolynomial.map_map, show (τ : ℂ →+* ℂ).comp (Formalism.L2.Host.embLL0 D) = Formalism.L2.Host.embLL0 D from RingHom.ext hτ]
  | zero => exact ⟨0, by rw [c.map_zero, Φ.map_zero, smul_zero], fun τ _ => (map_zero _).symm⟩
  | add P₁ P₂ _ _ h1 h2 =>
    obtain ⟨y1, rfl, c1⟩ := h1
    obtain ⟨y2, rfl, c2⟩ := h2
    refine ⟨y1 + y2, by rw [map_add c, map_add Φ, smul_add], fun τ hτ => ?_⟩
    have e1 := c1 τ hτ
    have e2 := c2 τ hτ
    unfold ConjVec at e1 e2 ⊢
    rw [Submodule.coe_add, map_add (f := _), ← e1, ← e2]
  | smul a P₁ _ h1 =>
    obtain ⟨y1, rfl, c1⟩ := h1
    refine ⟨(a : ℂ) • y1, ?_, fun τ hτ => ?_⟩
    · rw [c.map_smul, Φ.map_smul, smul_comm a₀]
      rfl
    · have e1 := c1 τ hτ
      unfold ConjVec at e1 ⊢
      obtain ⟨o, ho⟩ := a.2
      have ha : (τ : ℂ →+* ℂ) (a : ℂ) = a := by rw [← ho]; exact hτ _
      rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← e1, ha]


end GlobalTheory.BigOn.Exp.TwConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushSecOfLeft
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelPull

theorem push_sec_of_left {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hpb : IsGrpPullback A' A f φ) {x : 𝟙_ (Over S) ⟶ A} {x' : 𝟙_ (Over S') ⟶ A'}
    (hx : x'.left ≫ φ = f ≫ x.left) (T : Over S') :
    pushHom hpb T (toUnit T ≫ x') = toUnit (Over.mk (T.hom ≫ f)) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ x'.left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ x.left
  rw [Category.assoc, hx, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem isSympLev_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left}
    (hpb : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (G2 A).left} {P' : LB (G2 A').left}
    (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) {h M : ℕ} {B : Type} [CommRing B] {ζ : B}
    {s : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)}
    {lev' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A')} (hl : ∀ a, (lev' a).left ≫ φ = f ≫ (lev a).left)
    (hS : IsSympLev P h M ζ s lev) : IsSympLev P' h M ζ (f ≫ s) lev' := by
  have hp' : ∀ a, pushHom hpb _ (lev' a) = toUnit _ ≫ lev a := fun a => by
    have e := push_sec_of_left hpb (hl a) (𝟙_ (Over S'))
    rwa [toUnit_unit, Category.id_comp] at e
  refine ⟨fun a b => push_injective hpb _ ?_, fun a => push_injective hpb _ ?_, ?_⟩
  · rw [map_mul, hp', hp', hp', hS.1, MonObj.comp_mul]
  · rw [map_pow, map_one, hp', ← MonObj.comp_pow, hS.2.1, MonObj.comp_one]
  intro k _ _ x β z hx hz
  obtain ⟨g₁, g₂, g₃⟩ := hS.2.2 k (x ≫ f) β z (by rw [Category.assoc, hx]) hz
  refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
  · rw [← (push_injective hpb (Over.mk x)).eq_iff, push_sec_of_left hpb (hl a), map_one]
    rfl
  · obtain ⟨a, ha⟩ := g₂ (pushHom hpb (Over.mk x) g) (by
      have := congrArg (pushHom hpb (Over.mk x)) hg
      rw [map_pow, map_one] at this
      exact this)
    exact ⟨a, push_injective hpb _ ((push_sec_of_left hpb (hl a) _).trans ha)⟩
  · exact (weilIs_grpPullback_of_comm S S' A A' f φ _ _ (pull_isLB hP _) (pull_isLB hP' _) hpb
      (diag_iso sq H) (Over.mk x) M _ _ _ _ _
      (congrArg (fun q => q.left) (push_sec_of_left hpb (hl a) (Over.mk x)).symm)
      (congrArg (fun q => q.left) (push_sec_of_left hpb (hl b) (Over.mk x)).symm)).2 (g₃ a b)

theorem kerBy_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂)
    {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) (d : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ d = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x ^ d = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine push_injective h T ?_
  rw [map_pow, map_one]
  refine hn _ (pushHom h T x) ?_
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

theorem siegKerBy_pull {S S' : Scheme.{0}} {h M : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c : SiegPre h M ζ s} {c' : SiegPre h M ζ' s'} {f : S' ⟶ S}
    (m : SiegPB c' c f) {d : ℕ} (hc : SiegKerBy c d) : SiegKerBy c' d := by
  obtain ⟨φ, φ₂, pb, sq, iso, -⟩ := m
  exact ⟨(GlobalTheory.pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
    (diag_iso sq iso)).2.1 hc.1, kerBy_pull pb sq c.isLB c'.isLB iso d hc.2⟩

end GlobalTheory.UPel.HT
end
end
