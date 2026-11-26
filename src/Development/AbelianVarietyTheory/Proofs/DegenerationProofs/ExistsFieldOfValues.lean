module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem residue_embedding_unique {X : Scheme.{0}} {Ω : CommRingCat.{0}} [Nonempty (Spec Ω)]
    {p q : X} (φ : X.residueField p ⟶ Ω) (ψ : X.residueField q ⟶ Ω)
    (h : Spec.map φ ≫ X.fromSpecResidueField p = Spec.map ψ ≫ X.fromSpecResidueField q) :
    ∃ e : p = q, φ = (X.residueFieldCongr e).hom ≫ ψ := by
  obtain ⟨t⟩ := ‹Nonempty (Spec Ω)›
  have e : p = q := by
    have := congrArg (fun f => f t) h
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using this
  subst e
  refine ⟨rfl, ?_⟩
  rw [cancel_mono, Spec.map_inj] at h
  simpa using h

theorem essFiniteType_residueField_of_locallyOfFiniteType {X : Scheme.{0}} {R : CommRingCat.{0}}
    (s : X ⟶ Spec R) [LocallyOfFiniteType s] (p : X) (ψ : R ⟶ X.residueField p)
    (h : Spec.map ψ = X.fromSpecResidueField p ≫ s) : ψ.hom.EssFiniteType := by
  haveI : (s p).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have e : ψ = CommRingCat.ofHom (algebraMap R (s p).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R (s p)).inv ≫ s.residueFieldMap p := by
    rw [← Spec.map_inj, h, Spec.map_comp, Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [e]
  refine .comp (RingHom.essFiniteType_algebraMap.mpr inferInstance) (.comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.Spec.residueFieldIso R (s p)).inv).2).essFiniteType
    (RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap s p)))

theorem exists_fieldOfValues : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X), ∃ E : Subfield Ω, (∀ τ τ' : Ω →+* Ω, spMap τ ≫ x = spMap τ' ≫ x ↔ ∀ c ∈ E, τ c = τ' c) ∧ (∀ (K' : Type) [Field K'] (j : K' →+* Ω), E ≤ j.fieldRange ↔ ∃ y : Sp K' ⟶ X, spMap j ≫ y = x) ∧ ∀ (K : Type) [Field K] [Algebra K Ω] (s : X ⟶ Sp K), LocallyOfFiniteType s → x ≫ s = spMap (algebraMap K Ω) → Algebra.IsAlgebraic K Ω → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ L.toSubfield = E := by
  intro X Ω _ x
  obtain ⟨⟨p, φ⟩, hx⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  subst hx
  let f : X.residueField p →+* Ω := φ.hom
  refine ⟨f.fieldRange, fun τ τ' => ?_, fun K' _ j => ⟨fun h => ?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp,
      Spec.map_inj]
    constructor
    · rintro h _ ⟨c, rfl⟩
      exact congrArg (fun g => g.hom c) h
    · intro h
      ext c
      exact h _ ⟨c, rfl⟩
  · let e : K' ≃+* j.fieldRange := j.rangeRestrictFieldEquiv
    let g : X.residueField p →+* K' :=
      e.symm.toRingHom.comp (f.codRestrict j.fieldRange fun c => h ⟨c, rfl⟩)
    refine ⟨Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecResidueField p, ?_⟩
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f c, h ⟨c, rfl⟩⟩)
  · rintro ⟨y, hy⟩
    obtain ⟨⟨q, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K' X).symm.surjective y
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hy
    rw [← Category.assoc, ← Spec.map_comp] at hy
    obtain ⟨e, he⟩ := residue_embedding_unique _ _ hy.symm
    rintro _ ⟨c, rfl⟩
    exact ⟨ψ.hom ((X.residueFieldCongr e).hom.hom c), (congrArg (fun g => g.hom c) he).symm⟩
  · intro K _ _ s hs hxs halg
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.fromSpecResidueField p ≫ s)
    have hess := essFiniteType_residueField_of_locallyOfFiniteType s p ψ hψ
    rw [Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj] at hxs
    letI : Algebra K (X.residueField p) := ψ.hom.toAlgebra
    let fa : X.residueField p →ₐ[K] Ω :=
      { f with commutes' := fun c => congrArg (fun g => g.hom c) hxs }
    haveI : Algebra.EssFiniteType K (X.residueField p) := hess
    haveI : Algebra.IsAlgebraic K (X.residueField p) :=
      Algebra.IsAlgebraic.of_injective fa f.injective
    haveI : Module.Finite K (X.residueField p) := Algebra.finite_of_essFiniteType_of_isAlgebraic
    refine ⟨fa.fieldRange, ?_, rfl⟩
    exact Module.Finite.equiv (AlgEquiv.ofInjectiveField fa).toLinearEquiv

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValuesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_of_definition_of_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X), ∃ E : Subfield Ω, (∀ τ τ' : Ω →+* Ω, spMap τ ≫ x = spMap τ' ≫ x ↔ ∀ c ∈ E, τ c = τ' c) ∧ (∀ (K' : Type) [Field K'] (j : K' →+* Ω), E ≤ j.fieldRange ↔ ∃ y : Sp K' ⟶ X, spMap j ≫ y = x) ∧ ∀ (K : Type) [Field K] [Algebra K Ω] (s : X ⟶ Sp K), LocallyOfFiniteType s → x ≫ s = spMap (algebraMap K Ω) → Algebra.IsAlgebraic K Ω → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ L.toSubfield = E := by
  first | exact @GlobalTheory.SS.exists_fieldOfValues | exact GlobalTheory.SS.exists_fieldOfValues | (intros; apply GlobalTheory.SS.exists_fieldOfValues <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.ArcInf

section General
variable {k : Type} [CommRing k] {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]

theorem algOverHom_left (ψ : A →ₐ[k] B) : (algOverHom ψ).left = spMap (ψ : A →+* B) := rfl

theorem algOverHom_comp (ψ : A →ₐ[k] B) (χ : B →ₐ[k] C) :
    algOverHom (χ.comp ψ) = algOverHom χ ≫ algOverHom ψ := by
  ext1
  rw [Over.comp_left, algOverHom_left, algOverHom_left, algOverHom_left]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem algOverHom_id : algOverHom (AlgHom.id k A) = 𝟙 _ := by
  ext1
  rw [algOverHom_left]
  exact Spec.map_id _

theorem algOverHom_injective : Function.Injective (algOverHom : (A →ₐ[k] B) → _) := by
  intro a b h
  have h1 : spMap (a : A →+* B) = spMap (b : A →+* B) := congrArg (fun x => x.left) h
  have h2 := Spec.map_injective h1
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h2)

theorem algOverHom_surjective : Function.Surjective (algOverHom : (A →ₐ[k] B) → _) := by
  intro φ
  obtain ⟨g, hg⟩ := Spec.map_surjective φ.left
  have hw : φ.left ≫ spMap (algebraMap k A) = spMap (algebraMap k B) := Over.w φ
  rw [← hg, ← Spec.map_comp] at hw
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective hw)
  refine ⟨⟨g.hom, fun c => congrArg (fun f : k →+* B => f c) h2⟩, ?_⟩
  ext1
  exact hg

theorem eq_of_comp_eq {G : Over (Sp k)} {j : algOver k A ⟶ G} (hj : IsOpenImmersion j.left) {a b : A →ₐ[k] B}
    (h : algOverHom a ≫ j = algOverHom b ≫ j) : a = b := by
  apply algOverHom_injective
  ext1
  have := congrArg (fun x => x.left) h
  simp only [Over.comp_left] at this
  exact (cancel_mono j.left).1 this

end General

variable {k : Type} [Field k]

theorem exists_lift {F : Type} [CommRing F] [Algebra k F] (ρ : PowerSeries k →ₐ[k] F)
    (h : IsUnit (ρ PowerSeries.X)) :
    ∃ σ : FractionRing (PowerSeries k) →ₐ[k] F, ∀ x, σ (algebraMap (PowerSeries k) _ x) = ρ x := by
  have hu : ∀ y : nonZeroDivisors (PowerSeries k), IsUnit (ρ y) := by
    rintro ⟨y, hy⟩
    have h0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))
    obtain ⟨u, hu⟩ := hn.symm
    show IsUnit (ρ y)
    rw [← hu, map_mul, map_pow]
    exact (h.pow n).mul (u.isUnit.map ρ)
  exact ⟨IsLocalization.liftAlgHom (S := FractionRing (PowerSeries k)) hu, fun x => by simp⟩

def IsChart (G : Over (Sp k)) [GrpObj G] {A : Type} [CommRing A] [Algebra k A] (j : algOver k A ⟶ G)
    (ε : A →ₐ[k] k) {r : ℕ} (f : Fin r → A) : Prop :=
  IsOpenImmersion j.left ∧ algOverHom ε ≫ j = 1 ∧ Algebra.adjoin k (Set.range f) = ⊤ ∧ ∀ i, ε (f i) = 0

def TwoVar {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] (j : algOver k A ⟶ G)
    {r : ℕ} (f : Fin r → A) (a : algOver k (FractionRing (PowerSeries k)) ⟶ G)
    (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ (F : Type) [Field F] [Algebra k F] (τ : MvPowerSeries (Fin 2) k →ₐ[k] F)
    (σ₀ σ₁ : FractionRing (PowerSeries k) →ₐ[k] F), τ d ≠ 0 →
    (∀ x : PowerSeries k, σ₀ (algebraMap _ _ x) = τ (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k))) →
    (∀ x : PowerSeries k, σ₁ (algebraMap _ _ x) = τ (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))) →
    ∃ χ : A →ₐ[k] F, (∀ i, χ (f i) * τ d = τ (h i)) ∧
      algOverHom σ₁ ≫ a = (algOverHom χ ≫ j) * (algOverHom σ₀ ≫ a)

theorem IsChart.hom_ext {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G}
    {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A} (hc : IsChart G j ε f) {B : Type} [CommRing B] [Algebra k B]
    {a b : A →ₐ[k] B} (h : ∀ i, a (f i) = b (f i)) : a = b :=
  AlgHom.ext_of_adjoin_eq_top hc.2.2.1 (by rintro _ ⟨i, rfl⟩; exact h i)

end GlobalTheory.SS.ArcInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValHomEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ImmSep
open GlobalTheory.ZH.CrdCalc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem eq_of_valHom_eq (x x' : Sp R ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : valHom x U h = valHom x' U h') : x = x' := by
  have e₁ : x.appLE U ⊤ h = x'.appLE U ⊤ h' := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of R)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Sp R)) h
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec x' hU (isAffineOpen_top (Sp R)) h'
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem valHom_constFn {k : Type} [CommRing k] (p : X ⟶ Sp k) (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : k) :
    valHom x U h (constFn p U a) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (((x ≫ p).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) := by
  rw [← Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ le_top h]
  rfl

theorem eq_of_crd_eq : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x x' : Sp R ⟶ X) (v : J → R), x ≫ p = x' ≫ p → Crd H s x v → Crd H s x' v → x = x') := by
  intro k _ X p H J s J₀ _ hI R _ _ x x' v hp hx hx'
  have hm : x (IsLocalRing.closedPoint R) ∈ ⨆ i ∈ J₀, Out.nonzeroLocus (s i) := by
    rw [hI.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  obtain ⟨hi₀, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have h := (top_le_iff x _).2 hi
  have hu : IsUnit (v i) := (crd_isUnit_iff i hx).2 h
  have h' := (crd_isUnit_iff i hx').1 hu
  obtain ⟨hA, r, hr, hc⟩ := hI.2 i hi₀
  refine eq_of_valHom_eq x x' _ hA h h' (RingHom.eq_of_eqOn_set_dense hc ?_)
  rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
  · rw [valHom_constFn, valHom_constFn]
    simp only [hp]
  · have e := (crd_ratio hx (hr j) h).symm.trans (crd_ratio hx' (hr j) h')
    rw [valR_eq x _ h, valR_eq x' _ h'] at e
    exact hu.mul_right_cancel e

end GlobalTheory.ZH.ImmSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOneOfPowOfClosedPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.RedPts

variable {S : Scheme.{0}}

def precomp (G : Over S) [GrpObj G] {T T' : Over S} (u : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) where
  toFun x := u ≫ x
  map_one' := MonObj.comp_one u
  map_mul' x y := MonObj.comp_mul u x y

def diagSec {T : Scheme.{0}} (p : T ⟶ S) : 𝟙_ (Over T) ⟶ (Over.pullback p).obj (Over.mk p) :=
  Over.homMk (pullback.lift (𝟙 T) (𝟙 T) rfl) (pullback.lift_snd _ _ _)

def toSec (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) :
    (Over.mk p ⟶ G) →* (𝟙_ (Over T) ⟶ (Over.pullback p).obj G) :=
  (precomp _ (diagSec p)).comp (Over.pullback p).homMonoidHom

theorem toSec_left_fst (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) (x : Over.mk p ⟶ G) :
    (toSec G p x).left ≫ pullback.fst G.hom p = x.left := by
  have h₁ : ((Over.pullback p).map x).left ≫ pullback.fst G.hom p = pullback.fst p p ≫ x.left :=
    pullback.lift_fst _ _ _
  have h₂ : (diagSec p).left ≫ pullback.fst p p = 𝟙 T := pullback.lift_fst _ _ _
  change ((diagSec p).left ≫ ((Over.pullback p).map x).left) ≫ _ = _
  rw [Category.assoc, h₁]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) h₂)).trans (Category.id_comp _)

theorem toSec_injective (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) :
    Function.Injective (toSec G p) := fun x y h =>
  Over.OverMorphism.ext (by rw [← toSec_left_fst, h, toSec_left_fst])

theorem eq_one_of_pow_of_closedPoint (G : Over S) [GrpObj G] [IsCommMonObj G]
    [LocallyOfFiniteType G.hom] {R : Type} [CommRing R] [IsLocalRing R] (p : Sp R ⟶ S) {n : ℕ}
    (hn : IsUnit (n : R)) (x : Over.mk p ⟶ G) (hx : x ^ n = 1) {Z : Over S} (j : Z ⟶ Over.mk p)
    (hj : IsLocalRing.closedPoint R ∈ Set.range (show Z.left ⟶ Sp R from j.left)) (h : j ≫ x = 1) :
    x = 1 := by
  apply toSec_injective G p
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by simpa using hn.map (Scheme.ΓSpecIso (.of R)).inv.hom
  let G' := (Over.pullback p).obj G
  have : LocallyOfFiniteType G'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom p))
  have := GlobalTheory.GrpTangent.formallyUnramified_mulN G' hn'
  have : LocallyOfFiniteType ((mulN G' n).left ≫ G'.hom) := by rw [Over.w]; infer_instance
  have := locallyOfFiniteType_of_comp (mulN G' n).left G'.hom
  refine Over.OverMorphism.ext (GlobalTheory.eq_of_isLocalRing_of_unramified (R := .of R) (mulN G' n).left
    (a := (toSec G p x).left) (b := (toSec G p 1).left) ?_ (show Z.left ⟶ Sp R from j.left) hj ?_)
  · have e : toSec G p x ≫ mulN G' n = toSec G p 1 ≫ mulN G' n := by
      rw [GlobalTheory.GrpTangent.comp_mulN, GlobalTheory.GrpTangent.comp_mulN, ← map_pow, ← map_pow, hx, one_pow]
    exact congrArg Over.Hom.left e
  · refine pullback.hom_ext ?_ ?_
    · have e : j ≫ x = j ≫ 1 := by rw [h, MonObj.comp_one]
      exact ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·) (toSec_left_fst G p x))).trans
        ((congrArg Over.Hom.left e).trans
          ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·) (toSec_left_fst G p 1))).symm)
    · exact ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·)
        ((Over.w (toSec G p x)).trans (Over.w (toSec G p 1)).symm))).trans (Category.assoc _ _ _).symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_reduction : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∃ (H : Subgroup (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (r : H →* (𝟙_ (Over (Sp (IsLocalRing.ResidueField R))) ⟶ (Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G)), (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = x.left) ∧ (∀ (x : H) (s : Sp R ⟶ G.left), s ≫ G.hom = spMap (algebraMap W R) → spMap (algebraMap R Ω) ≫ s = x.1.left → (r x).left ≫ pullback.fst G.hom _ = spMap (IsLocalRing.residue R) ≫ s) ∧ ∀ (n : ℕ) (x : H), IsUnit (n : R) → x ^ n = 1 → r x = 1 → x = 1 := by
  intro W R Ω _ _ _ _ _ _ _ _ _ hj G _ hG
  obtain ⟨hc, hsm, hsep, -, -⟩ := hG
  let u : Over.mk (spMap (algebraMap W Ω)) ⟶ Over.mk (spMap (algebraMap W R)) :=
    Over.homMk (spMap (algebraMap R Ω))
      ((spMap_comp _ _).trans (congrArg spMap (IsScalarTower.algebraMap_eq W R Ω).symm))
  let v : Over.mk (spMap ((IsLocalRing.residue R).comp (algebraMap W R))) ⟶
      Over.mk (spMap (algebraMap W R)) :=
    Over.homMk (spMap (IsLocalRing.residue R)) (spMap_comp _ _)
  have hdom : IsDominant (spMap (algebraMap R Ω)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap R Ω) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hj]; exact bot_le)⟩
  have hu : Function.Injective (precomp G u) := fun a b h => Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp R) G.hom ((Over.w a).trans (Over.w b).symm)
      (spMap (algebraMap R Ω)) (congrArg Over.Hom.left h))
  let e := MonoidHom.ofInjective hu
  refine ⟨(precomp G u).range, ((toSec G _).comp (precomp G v)).comp e.symm.toMonoidHom,
    fun x => ⟨?_, ?_⟩, fun x s hs hx => ?_, fun n x hn hx hr => ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.left, Over.w s, rfl⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨Over.homMk s hs, Over.OverMorphism.ext hx⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    obtain rfl : y = Over.homMk s hs := hu (Over.OverMorphism.ext hx.symm)
    change (toSec G _ (precomp G v (e.symm (e _)))).left ≫ _ = _
    rw [e.symm_apply_apply, toSec_left_fst]
    rfl
  · obtain ⟨y, rfl⟩ := e.surjective x
    change toSec G _ (precomp G v (e.symm (e _))) = _ at hr
    rw [e.symm_apply_apply, map_eq_one_iff _ (toSec_injective G _)] at hr
    rw [← map_pow, map_eq_one_iff _ e.injective] at hx
    rw [eq_one_of_pow_of_closedPoint G _ hn y hx v
      ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩ hr, map_one]

end GlobalTheory.RedPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfRatPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.RatPointConn

universe u

theorem fibre_subsingleton {k K : Type u} [Field k] [Field K] {X Z : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {y : Spec (.of K) ⟶ Spec (.of k)} {p : Z ⟶ X} {q : Z ⟶ Spec (.of K)}
    (h : IsPullback p q f y) (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) (a b : Z)
    (ha : p a = s (IsLocalRing.closedPoint k)) (hb : p b = s (IsLocalRing.closedPoint k)) :
    a = b := by
  let t : Spec (.of K) ⟶ Z := h.lift (y ≫ s) (𝟙 _) (by simp [hs])
  have ht : IsPullback t y p s := by
    refine IsPullback.of_right (h₁₂ := q) (v₁₃ := y) (h₂₂ := f) ?_ (by simp [t]) h.flip
    rw [hs, show t ≫ q = 𝟙 _ by simp [t]]
    exact IsPullback.of_id_fst
  obtain ⟨a', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht a (IsLocalRing.closedPoint k) ha
  obtain ⟨b', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht b (IsLocalRing.closedPoint k) hb
  rw [Subsingleton.elim a' b']

theorem of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [ConnectedSpace X] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z p q h => ?_⟩
  have := LocallyOfFiniteType.jacobsonSpace f
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hs : Surjective p := MorphismProperty.of_isPullback h.flip hy
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)
  have fib : ∀ x : X, IsClosed {x} → ∀ a b : Z, p a = x → p b = x → a = b := by
    intro x hx a b ha hb
    exact fibre_subsingleton h (pointOfClosedPoint f x hx) (pointOfClosedPoint_comp f x hx) a b
      (ha.trans (pointOfClosedPoint_apply f x hx _).symm)
      (hb.trans (pointOfClosedPoint_apply f x hx _).symm)
  have hne : Nonempty Z := (p.surjective (Classical.arbitrary X)).nonempty
  have : PreconnectedSpace Z := ⟨fun U V hU hV hUV hU' hV' => by
    rw [Set.univ_inter] at hU' hV' ⊢
    have o₁ : IsOpen (p '' U) := p.isOpenMap _ hU
    have o₂ : IsOpen (p '' V) := p.isOpenMap _ hV
    have hc : Set.univ ⊆ p '' U ∪ p '' V := by
      intro x _
      obtain ⟨z, rfl⟩ := p.surjective x
      exact (hUV (Set.mem_univ z)).imp (fun hz => ⟨z, hz, rfl⟩) (fun hz => ⟨z, hz, rfl⟩)
    have hi := isPreconnected_univ _ _ o₁ o₂ hc (by simpa using hU') (by simpa using hV')
    rw [Set.univ_inter] at hi
    obtain ⟨x, ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, hxc⟩ := nonempty_inter_closedPoints hi
      (o₁.inter o₂).isLocallyClosed
    exact ⟨a, ha, fib x hxc a b hax hbx ▸ hb⟩⟩
  exact ⟨hne⟩

theorem preconnectedSpace_of_fibre {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X]
    [PreconnectedSpace X] {p : Z → X} (ho : IsOpenMap p) (hc : IsClosedMap p) (x : X)
    (hx : ∀ a b, p a = x → p b = x → a = b) : PreconnectedSpace Z := by
  have key : ∀ U : Set Z, IsClopen U → U.Nonempty → ∃ a ∈ U, p a = x := by
    intro U hU hne
    have h1 : IsClopen (p '' U) := ⟨hc _ hU.1, ho _ hU.2⟩
    have h2 := h1.eq_univ (hne.image _)
    exact h2.ge (Set.mem_univ x)
  refine ⟨(isPreconnected_iff_subset_of_disjoint).2 fun U V hU hV hUV hd => ?_⟩
  rw [Set.univ_inter] at hd
  have hdis : Disjoint U V := Set.disjoint_iff_inter_eq_empty.2 hd
  have hcompl : IsCompl U V := ⟨hdis, codisjoint_iff.2 (Set.univ_subset_iff.1 hUV)⟩
  have cU : IsClopen U := ⟨⟨by rw [hcompl.compl_eq]; exact hV⟩, hU⟩
  have cV : IsClopen V := ⟨⟨by rw [hcompl.symm.compl_eq]; exact hU⟩, hV⟩
  rcases U.eq_empty_or_nonempty with rfl | nU
  · right; simpa using hUV
  rcases V.eq_empty_or_nonempty with rfl | nV
  · left; simpa using hUV
  obtain ⟨a, ha, hax⟩ := key U cU nU
  obtain ⟨b, hb, hbx⟩ := key V cV nV
  obtain rfl := hx a b hax hbx
  exact absurd hb (Set.disjoint_left.1 hdis ha)

theorem of_isPullback {A G U Z : Scheme.{u}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Surjective j] (h : IsPullback φ f g j) [GeometricallyConnected f] :
    GeometricallyConnected g := by
  refine ⟨fun K _ y W p q hW => ?_⟩
  obtain ⟨w⟩ : Nonempty ↥(pullback j y) :=
    ((pullback.snd j y).surjective (Classical.arbitrary _)).nonempty
  let r := (pullback j y).fromSpecResidueField w
  let a := r ≫ pullback.fst j y
  let b := r ≫ pullback.snd j y
  have hab : a ≫ j = b ≫ y := by simp [a, b, pullback.condition]
  have H : IsPullback (pullback.fst q b ≫ p) (pullback.snd q b) g (b ≫ y) :=
    (IsPullback.of_hasPullback q b).paste_horiz hW
  rw [← hab] at H
  have H' := IsPullback.of_right' H h
  have : ConnectedSpace ↥(pullback q b) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) a _ _ H'
  have hb : Surjective b := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  exact (pullback.fst q b).surjective.connectedSpace (pullback.fst q b).continuous

theorem of_section {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [ConnectedSpace X] (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f := by
  let y : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hi : IsIntegralHom y := by
    rw [IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.2 inferInstance
  have h := IsPullback.of_hasPullback f y
  have ho : UniversallyOpen (pullback.fst f y) := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)
  have : PreconnectedSpace ↥(pullback f y) :=
    preconnectedSpace_of_fibre (pullback.fst f y).isOpenMap (pullback.fst f y).isClosedMap _
      (fibre_subsingleton h s hs)
  have : ConnectedSpace ↥(pullback f y) :=
    ⟨((pullback.fst f y).surjective (Classical.arbitrary X)).nonempty⟩
  have := of_isAlgClosed (pullback.snd f y)
  exact of_isPullback h

theorem geometricallyConnected_of_ratPoint :
    ∀ (k : Type) [Field k] (X : Over (Sp k)), LocallyOfFiniteType X.hom → QuasiCompact X.hom → ConnectedSpace X.left → Nonempty (𝟙_ (Over (Sp k)) ⟶ X) → GeometricallyConnected X.hom := by
  rintro k _ X _ - _ ⟨s⟩
  exact of_section (k := k) X.hom s.left (Over.w s)

end GlobalTheory.RatPointConn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelExtensionOfDefinedAtPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelExtensionOfDefinedAtPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

section
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem Model.isPullback_j (M : Model R A) :
    IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  refine IsPullback.of_iso (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
    ((Over.forget _).mapIso M.e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · have : M.e.hom.left ≫ M.e.inv.left = 𝟙 _ := by rw [← Over.comp_left, M.e.hom_inv_id]; rfl
    simp [Model.j, reassoc_of% this]
  · have := Over.w M.e.hom
    simpa using this.symm

theorem Model.quasiCompact_j (M : Model R A) : QuasiCompact M.j :=
  MorphismProperty.of_isPullback M.isPullback_j.flip inferInstance

variable [IsDomain R] [IsFractionRing R K]

theorem Model.dominant_j (M : Model R A) : IsSchemeTheoreticallyDominant M.j := by
  have := schemeTheoreticallyDominant_fractionField R K
  have := M.smooth
  exact IsSchemeTheoreticallyDominant.of_isPullback M.isPullback_j.flip

theorem Model.hom_ext_of_flat (M : Model R A) {P X : Scheme.{0}} (p : P ⟶ M.Y.left) [Flat p]
    (s : X ⟶ Sp R) [IsSeparated s] {a b : P ⟶ X} (hab : a ≫ s = b ≫ s)
    (h : pullback.fst p M.j ≫ a = pullback.fst p M.j ≫ b) : a = b := by
  have := M.dominant_j
  have := M.quasiCompact_j
  have : IsSchemeTheoreticallyDominant (pullback.fst p M.j) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback p M.j).flip
  have : IsSeparated (Over.mk s).hom := ‹_›
  have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk (a ≫ s)) (X := Over.mk s)
    (pullback.fst p M.j) (a := Over.homMk a rfl) (b := Over.homMk b hab.symm) h
  exact congr(($this).left)

omit [IsDomain R] [IsFractionRing R K] in
theorem Extends.comp_eq {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) {W : Scheme.{0}} (u : W ⟶ U.toScheme)
    (v : W ⟶ A.left) (e : u ≫ U.ι = v ≫ M.j) : u ≫ g = v ≫ f.left ≫ N.j := by
  have P := isPullback_morphismRestrict M.j U
  rw [← P.lift_fst u v e, Category.assoc, h.2, P.lift_snd_assoc]

theorem exists_glue (M : Model R A) (N : Model R A') (f : A ⟶ A') (U : M.Y.left → M.Y.left.Opens)
    (g : ∀ y, (U y).toScheme ⟶ N.Y.left) (hU : ∀ y, y ∈ U y) (hg : ∀ y, Extends M N f (U y) (g y)) :
    ∃ G : M.Y ⟶ N.Y, M.j ≫ G.left = f.left ≫ N.j ∧ ∀ y, (U y).ι ≫ G.left = g y := by
  have := N.sep
  have hc : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hU y⟩
  let 𝒰 := M.Y.left.openCoverOfIsOpenCover U hc
  have hgl : ∀ x y, pullback.fst (U x).ι (U y).ι ≫ g x = pullback.snd (U x).ι (U y).ι ≫ g y := by
    intro x y
    refine M.hom_ext_of_flat (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) N.Y.hom ?_ ?_
    · rw [Category.assoc, Category.assoc, (hg x).1, (hg y).1, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc,
        (hg x).comp_eq _ (pullback.snd _ M.j) (by rw [Category.assoc]; exact pullback.condition),
        (hg y).comp_eq _ (pullback.snd _ M.j)
          (by rw [Category.assoc, ← pullback.condition (f := (U x).ι)]; exact pullback.condition)]
  obtain ⟨G, hG⟩ : ∃ G : M.Y.left ⟶ N.Y.left, ∀ y, (U y).ι ≫ G = g y :=
    ⟨𝒰.glueMorphisms g hgl, fun y => 𝒰.ι_glueMorphisms g hgl y⟩
  refine ⟨Over.homMk G (𝒰.hom_ext _ _ fun y : M.Y.left => ?_), ?_, hG⟩
  · change (U y).ι ≫ G ≫ N.Y.hom = (U y).ι ≫ M.Y.hom
    rw [← Category.assoc, hG, (hg y).1]
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ M.j) _ _ fun y : M.Y.left => ?_
    change pullback.fst M.j (U y).ι ≫ M.j ≫ G = pullback.fst M.j (U y).ι ≫ f.left ≫ N.j
    rw [pullback.condition_assoc, hG]
    exact (hg y).comp_eq _ _ pullback.condition.symm

theorem ext_unique (M : Model R A) (N : Model R A') {a b : M.Y ⟶ N.Y}
    (h : M.j ≫ a.left = M.j ≫ b.left) : a = b := by
  have := M.dominant_j
  have := N.sep
  exact over_ext_of_schemeTheoreticallyDominant M.j h

end

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma isPullback_model_j_spMap_algebraMap (M : _root_.GlobalTheory.SS.Model R A) :
    IsPullback M.j A.hom M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  have h := IsPullback.of_hasPullback M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K))
  refine IsPullback.of_iso h ((Over.forget _).mapIso M.e) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [_root_.GlobalTheory.SS.Model.j, ← Over.comp_left_assoc]
  · have := Over.w M.e.hom
    simpa using this.symm

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma eq_of_openImmersion_of_eq_on_genericFibre [IsDomain R] [IsFractionRing R K]
    (M : _root_.GlobalTheory.SS.Model R A)
    (N : _root_.GlobalTheory.SS.Model R A') {W : Scheme} (i : W ⟶ M.Y.left)
    [IsOpenImmersion i] (a b : W ⟶ N.Y.left)
    (ha : a ≫ N.Y.hom = i ≫ M.Y.hom)
    (hb : b ≫ N.Y.hom = i ≫ M.Y.hom)
    (h : pullback.snd M.j i ≫ a = pullback.snd M.j i ≫ b) :
    a = b := by
  haveI := M.smooth
  haveI := N.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  have hP := ((IsPullback.of_hasPullback M.j i).flip.paste_vert
    (isPullback_model_j_spMap_algebraMap M)).flip
  haveI := IsSchemeTheoreticallyDominant.of_isPullback hP
  have := _root_.GlobalTheory.over_ext_of_schemeTheoreticallyDominant (Y := Over.mk (i ≫ M.Y.hom))
    (X := N.Y) (pullback.snd M.j i)
    (a := Over.homMk a ha) (b := Over.homMk b hb) h
  exact congrArg (fun c => c.left) this

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma comp_eq_of_extends_of_genericFibre_comm {M : _root_.GlobalTheory.SS.Model R A}
    {N : _root_.GlobalTheory.SS.Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : (U : Scheme) ⟶ N.Y.left} (hg : _root_.GlobalTheory.SS.Extends M N f U g)
    {T : Scheme} (t : T ⟶ U) (s : T ⟶ A.left) (hts : s ≫ M.j = t ≫ U.ι) :
    t ≫ g = s ≫ f.left ≫ N.j := by
  have hP := isPullback_morphismRestrict M.j U
  have h2 := hg.2
  rw [← hP.lift_fst t s hts.symm, Category.assoc, h2, ← Category.assoc, hP.lift_snd]

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
theorem _root_.GlobalTheory.SS.existsUnique_extension_of_forall_defAt :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (M : _root_.GlobalTheory.SS.Model R A)
      (N : _root_.GlobalTheory.SS.Model R A') (f : A ⟶ A'),
      (∀ y, _root_.GlobalTheory.SS.DefAt M N f y) →
        ∃! g : M.Y ⟶ N.Y,
          M.j ≫ g.left = f.left ≫ N.j := by
  intro R K _ _ _ _ _ _ A A' M N f hdef
  choose U g hyU hg using hdef
  have hcov : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
  have key : ∀ x y, pullback.fst (U x).ι (U y).ι ≫ g x = pullback.snd (U x).ι (U y).ι ≫ g y := by
    intro x y
    refine eq_of_openImmersion_of_eq_on_genericFibre M N (pullback.fst (U x).ι (U y).ι ≫ (U x).ι)
      _ _ ?_ ?_ ?_
    · simp only [Category.assoc, (hg x).1]
    · simp only [Category.assoc, (hg y).1]
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    · have e1 := comp_eq_of_extends_of_genericFibre_comm (hg x)
        (pullback.snd M.j (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ≫
          pullback.fst _ _)
        (pullback.fst _ _) (by rw [Category.assoc]; exact pullback.condition)
      have e2 := comp_eq_of_extends_of_genericFibre_comm (hg y)
        (pullback.snd M.j (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ≫
          pullback.snd _ _)
        (pullback.fst _ _) (by rw [Category.assoc, ← pullback.condition]; exact pullback.condition)
      simp only [Category.assoc] at e1 e2
      rw [e1, e2]
  let 𝒰 := M.Y.left.openCoverOfIsOpenCover U hcov
  have hcompat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ g x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ g y :=
    fun x y => key x y
  let G := 𝒰.glueMorphisms g hcompat
  have hG : ∀ y, (U y).ι ≫ G = g y := fun y => 𝒰.ι_glueMorphisms g hcompat y
  have hw : G ≫ N.Y.hom = M.Y.hom := by
    refine 𝒰.hom_ext _ _ fun y => ?_
    change (U y).ι ≫ G ≫ N.Y.hom = (U y).ι ≫ M.Y.hom
    exact (Category.assoc _ _ _).symm.trans ((hG y =≫ _).trans (hg y).1)
  haveI := M.smooth
  haveI := N.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  haveI := IsSchemeTheoreticallyDominant.of_isPullback (isPullback_model_j_spMap_algebraMap M).flip
  have hex : M.j ≫ G = f.left ≫ N.j := by
    have hcovA : TopologicalSpace.IsOpenCover (fun y => M.j ⁻¹ᵁ U y) := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      intro a _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨M.j a, hyU _⟩
    refine (A.left.openCoverOfIsOpenCover _ hcovA).hom_ext _ _ fun y => ?_
    change (M.j ⁻¹ᵁ U y).ι ≫ M.j ≫ G =
      (M.j ⁻¹ᵁ U y).ι ≫ f.left ≫ N.j
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    exact (M.j ∣_ U y ≫= hG y).trans (hg y).2
  exact ⟨Over.homMk G hw, hex, fun g' hg' =>
    _root_.GlobalTheory.over_ext_of_schemeTheoreticallyDominant M.j (hg'.trans hex.symm)⟩

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelExtensionOfDefinedAtPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_model_extension_of_definedAtPoints : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A A' : Over (Sp K)) (M : Model R A) (N : Model R A') (f : A ⟶ A'), (∀ y, DefAt M N f y) → ∃! g : M.Y ⟶ N.Y, M.j ≫ g.left = f.left ≫ N.j := by
  first | exact @GlobalTheory.SS.existsUnique_extension_of_forall_defAt | exact GlobalTheory.SS.existsUnique_extension_of_forall_defAt | (intros; apply GlobalTheory.SS.existsUnique_extension_of_forall_defAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothFreeAway
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem free_localizedModule_mul {C : Type} [CommRing C] (M : Type) [AddCommGroup M] [Module C M]
    (r g : C) (h : Module.Free (Localization.Away r) (LocalizedModule (Submonoid.powers r) M)) :
    Module.Free (Localization.Away (r * g)) (LocalizedModule (Submonoid.powers (r * g)) M) := by
  let _ : Algebra (Localization.Away r) (Localization.Away (r * g)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away r) r g).toAlgebra
  have _ : IsScalarTower C (Localization.Away r) (Localization.Away (r * g)) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away r) r g c).symm
  let _ : Module (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M) :=
    Module.compHom _ (algebraMap (Localization.Away r) (Localization.Away (r * g)))
  have _ : IsScalarTower (Localization.Away r) (Localization.Away (r * g))
      (LocalizedModule (Submonoid.powers (r * g)) M) :=
    ⟨fun a b x => by
      show (a • b) • x = algebraMap _ (Localization.Away (r * g)) a • b • x
      rw [Algebra.smul_def, mul_smul]⟩
  have _ : IsScalarTower C (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M) :=
    ⟨fun c a x => by
      show algebraMap _ (Localization.Away (r * g)) (c • a) • x =
        c • algebraMap _ (Localization.Away (r * g)) a • x
      rw [Algebra.smul_def, map_mul, mul_smul,
        ← IsScalarTower.algebraMap_apply C (Localization.Away r) (Localization.Away (r * g)),
        algebraMap_smul]⟩
  have hr := LocalizedModule.isBaseChange (Submonoid.powers r) M
  have hrg := LocalizedModule.isBaseChange (Submonoid.powers (r * g)) M
  rw [← hr.lift_comp (LocalizedModule.mkLinearMap (Submonoid.powers (r * g)) M)] at hrg
  exact Module.Free.of_equiv (hr.of_comp hrg).equiv

theorem exists_smooth_free_away : ∀ (k C : Type) [Field k] [PerfectField k] [CommRing C] [Nontrivial C] [IsReduced C] [Algebra k C] [Algebra.FiniteType k C] (M : Type) [AddCommGroup M] [Module C M] [Module.Finite C M], ∃ f : C, f ≠ 0 ∧ Algebra.Smooth k (Localization.Away f) ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  intro k C _ _ _ _ _ _ _ M _ _ _
  have _ : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have _ : Algebra.FinitePresentation k C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have _ : Module.FinitePresentation C M := Module.finitePresentation_of_finite C M
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  have := hm.isPrime
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal C)) (J := m) bot_le
  have _ : p.IsPrime := hp.1.1
  have _ : Ring.KrullDimLE 0 (Localization.AtPrime p) := Ring.KrullDimLE.of_isLocalization p hp _
  let _ : Field (Localization.AtPrime p) := (Ring.KrullDimLE.isField_of_isReduced).toField
  have _ : Algebra.IsSmoothAt k p := Algebra.FormallySmooth.of_perfectField
  have _ : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.Free.of_divisionRing _ _
  obtain ⟨f₁, hf₁p, hf₁⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k p
  obtain ⟨r, hrp, hr, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  refine ⟨r * f₁, ?_, ?_, free_localizedModule_mul M r f₁ hr⟩
  · intro h0
    have : r * f₁ ∈ p := by rw [h0]; exact p.zero_mem
    exact (Ideal.IsPrime.mem_or_mem ‹_› this).elim hrp hf₁p
  · rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth] at hf₁ ⊢
    exact fun x hx => hf₁ (PrimeSpectrum.basicOpen_mul_le_right r f₁ hx)

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.StalkGlue

theorem sec_ext {X : Scheme.{0}} (U : X.Opens) (s t : Γ(X, U))
    (h : ∀ (x : X) (hx : x ∈ U), (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom t) :
    s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t h

theorem germ_map {X : Scheme.{0}} {U V : X.Opens} (i : V ⟶ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom ((X.presheaf.map i.op).hom s) =
      (X.presheaf.germ U x (i.le hx)).hom s :=
  TopCat.Presheaf.germ_res_apply X.presheaf i x hx s

theorem exists_section {X : Scheme.{0}} (U : X.Opens) (g : ∀ (x : X), x ∈ U → X.presheaf.stalk x)
    (H : ∀ x : X, x ∈ U → ∃ (W : X.Opens) (h : W ≤ U) (t : Γ(X, W)), x ∈ W ∧
      ∀ (y : X) (hy : y ∈ W), g y (h hy) = (X.presheaf.germ W y hy).hom t) :
    ∃ s : Γ(X, U), ∀ (x : X) (hx : x ∈ U), (X.presheaf.germ U x hx).hom s = g x hx := by
  choose W hW t hx ht using H
  have hcov : U ≤ iSup (fun p : U => W p.1 p.2) := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun p : U => W p.1 p.2) U
    (fun p => homOfLE (hW p.1 p.2)) hcov (fun p => t p.1 p.2) (by
      intro p q
      apply sec_ext (W p.1 p.2 ⊓ W q.1 q.2)
      intro y hy
      exact (germ_map (TopologicalSpace.Opens.infLELeft _ _) y hy _).trans
        (((ht p.1 p.2 y hy.1).symm.trans (ht q.1 q.2 y hy.2)).trans
          (germ_map (TopologicalSpace.Opens.infLERight _ _) y hy _).symm))
  refine ⟨s, fun x hxU => ?_⟩
  have h1 : (X.presheaf.map (homOfLE (hW x hxU)).op).hom s = t x hxU := hs ⟨x, hxU⟩
  rw [ht x hxU x (hx x hxU), ← h1]
  exact (germ_map (homOfLE (hW x hxU)) x (hx x hxU) s).symm

theorem exists_vf : ∀ (K : Type) [Field K] (X : Over (Sp K)) (δ : ∀ x : X.left, X.left.presheaf.stalk x →+ X.left.presheaf.stalk x), (∀ x a b, δ x (a * b) = a * δ x b + b * δ x a) → (∀ (U : X.left.Opens) (x : X.left) (hx : x ∈ U) (c : K), δ x ((X.left.presheaf.germ U x hx).hom (cstK X U c)) = 0) → (∀ (U : X.left.Opens) (s : Γ(X.left, U)) (x : X.left), x ∈ U → ∃ (W : X.left.Opens) (h : W ≤ U) (t : Γ(X.left, W)), x ∈ W ∧ ∀ (y : X.left) (hy : y ∈ W), δ y ((X.left.presheaf.germ U y (h hy)).hom s) = (X.left.presheaf.germ W y hy).hom t) → ∃ D : VF X, ∀ (U : X.left.Opens) (s : Γ(X.left, U)) (x : X.left) (hx : x ∈ U), (X.left.presheaf.germ U x hx).hom (D.D U s) = δ x ((X.left.presheaf.germ U x hx).hom s) := by
  intro K _ X δ hL hc hloc
  choose D hD using fun (U : X.left.Opens) (s : Γ(X.left, U)) =>
    exists_section U (fun x hx => δ x ((X.left.presheaf.germ U x hx).hom s)) (hloc U s)
  refine ⟨⟨fun U => AddMonoidHom.mk' (D U) (fun a b => ?_), fun U a b => ?_, fun U c => ?_,
    fun U V h a => ?_⟩, fun U s x hx => hD U s x hx⟩
  · apply sec_ext
    intro x hx
    simp only [map_add (f := _), hD]
  · apply sec_ext
    intro x hx
    simp only [AddMonoidHom.mk'_apply, map_add (f := _), map_mul, hD, hL]
  · apply sec_ext
    intro x hx
    simp only [AddMonoidHom.mk'_apply, map_zero, hD, hc]
  · apply sec_ext
    intro x hx
    simp only [AddMonoidHom.mk'_apply]
    rw [hD, germ_map, germ_map, hD]

end GlobalTheory.SS.StalkGlue
end
end
