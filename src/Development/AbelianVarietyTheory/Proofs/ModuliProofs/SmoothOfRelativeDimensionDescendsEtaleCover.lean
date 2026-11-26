module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
namespace GlobalTheory.SmoothDescent

section Rings

open TensorProduct KaehlerDifferential

theorem flat_of_formallySmooth_of_essFiniteType (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Algebra.EssFiniteType R B] [Algebra.FormallySmooth R B] :
    Module.Flat R B := by
  let P := Algebra.EssFiniteType.subalgebra R B
  let M : Submonoid P := Algebra.EssFiniteType.submonoid R B
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R P)
  let M' := M.comap f₀
  let P' := Localization M'
  let fP : P' →ₐ[R] B := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R P B).comp f₀) fun x ↦
    IsLocalization.map_units (M := M) B ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    exact (IsLocalization.lift_mk'_spec (M := M') (S := P')
      (g := ((IsScalarTower.toAlgHom R P B).comp f₀).toRingHom)
      (fun x ↦ IsLocalization.map_units (M := M) B ⟨f₀ x.1, x.2⟩) x _ ⟨s, hs⟩).mpr
      (IsLocalization.mk'_spec' B (f₀ x) (⟨f₀ s, hs⟩ : M)).symm
  have : Module.Flat R P' := .trans R (MvPolynomial (Fin n) R) P'
  exact Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing fP hf₁

theorem formallySmooth_of_flat_of_formallyUnramified (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
    [Algebra.EssFiniteType R A] [Module.Flat R A] [Algebra.FormallyUnramified R A] :
    Algebra.FormallySmooth R A := by
  have : Algebra.FormallyEtale (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] A) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Algebra.FinitePresentation R (Algebra.EssFiniteType.subalgebra R A) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (Algebra.EssFiniteType.submonoid R A)

theorem formallyEtale_of_bijective_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P] [CommRing B]
    [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Algebra.FormallySmooth R B]
    (h : Function.Bijective (mapBaseChange R P B)) : Algebra.FormallyEtale P B := by
  have h1 : Subsingleton Ω[B⁄P] := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := map_surjective R P B x
    exact (exact_mapBaseChange_map R P B y).mpr (h.2 y)
  have h2 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have h3 : Algebra.H1Cotangent.δ R P B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B x).mp h3
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨h1, h2⟩

theorem formallySmooth_of_faithfullyFlat (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsNoetherianRing R] [IsLocalRing A]
    [Algebra.EssFiniteType R A] [Algebra.EssFiniteType A B] [Module.FaithfullyFlat A B]
    [Algebra.FormallyEtale A B] [Algebra.FormallySmooth R B] : Algebra.FormallySmooth R A := by
  classical
  have : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing R A
  have : Algebra.EssFiniteType R B := .comp R A B
  have : Module.FinitePresentation A Ω[A⁄R] := Module.finitePresentation_of_finite _ _
  have : Module.Flat B (B ⊗[A] Ω[A⁄R]) := .of_linearEquiv (tensorKaehlerEquivOfFormallyEtale R A B)
  have : Module.Flat A Ω[A⁄R] := Module.Flat.of_flat_tensorProduct _ _ B
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _ (span_range_derivation R A)
  have : Finite κ := Module.Finite.finite_basis b
  let P := MvPolynomial κ R
  let φ : P →ₐ[R] A := MvPolynomial.aeval a
  algebraize [φ.toRingHom, (algebraMap A B).comp φ.toRingHom]
  have : IsScalarTower R P B := .to₁₂₄ R P A B
  have hX (i : κ) : algebraMap P A (MvPolynomial.X i) = a i := MvPolynomial.aeval_X _ _
  let bB : Module.Basis κ B Ω[B⁄R] := (b.baseChange B).map (tensorKaehlerEquivOfFormallyEtale R A B)
  let bP : Module.Basis κ B (B ⊗[P] Ω[P⁄R]) := (mvPolynomialBasis R κ).baseChange B
  have hbij : Function.Bijective (mapBaseChange R P B) := by
    have : mapBaseChange R P B = (bP.equiv bB (Equiv.refl κ)).toLinearMap := by
      refine bP.ext fun i => ?_
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      simp [bP, bB, hb, ← hX, ← IsScalarTower.algebraMap_apply, P]
    rw [this]
    exact (bP.equiv bB (Equiv.refl κ)).bijective
  have : Algebra.FormallyEtale P B := formallyEtale_of_bijective_mapBaseChange R P B hbij
  let p : Ideal P := (IsLocalRing.maximalIdeal A).comap (algebraMap P A)
  let Q := Localization.AtPrime p
  let ψ : Q →ₐ[P] A := IsLocalization.liftAlgHom (M := p.primeCompl) (f := Algebra.ofId P A) fun x => by
    by_contra h
    exact x.2 h
  algebraize [ψ.toRingHom, (algebraMap A B).comp ψ.toRingHom]
  have : IsScalarTower P Q B := .to₁₂₄ P Q A B
  have : IsScalarTower R Q A := .to₁₃₄ R P Q A
  have : IsScalarTower R Q B := .to₁₂₄ R Q A B
  have : IsLocalHom (algebraMap Q A) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff Q p]
    intro hxp
    have e : algebraMap P A x = algebraMap P A s * algebraMap Q A (IsLocalization.mk' Q x s) := by
      rw [IsScalarTower.algebraMap_apply P Q A s, ← map_mul, IsLocalization.mk'_spec',
        ← IsScalarTower.algebraMap_apply]
    have hs : IsUnit (algebraMap P A s) := by
      by_contra h
      exact s.2 h
    exact hxp (e ▸ hs.mul hx)
  have : Algebra.FormallyEtale Q B := Algebra.FormallyEtale.localization_base p.primeCompl
  have : Algebra.EssFiniteType Q A := .of_comp R Q A
  have : Algebra.EssFiniteType Q B := .of_comp R Q B
  have : Module.Flat Q B := flat_of_formallySmooth_of_essFiniteType Q B
  have : Module.Flat Q A := by
    rw [← RingHom.flat_algebraMap_iff]
    refine ringHom_flat_of_comp_faithfullyFlat (β := algebraMap A B)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) ?_
    rw [← IsScalarTower.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have : Algebra.FormallyUnramified Q A := by
    have h1 : Subsingleton (B ⊗[A] Ω[A⁄Q]) := (tensorKaehlerEquivOfFormallyEtale Q A B).subsingleton
    exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B).mp h1⟩
  have : Algebra.FormallySmooth Q A := formallySmooth_of_flat_of_formallyUnramified Q A
  have : Algebra.FormallySmooth P A := .comp P Q A
  exact .comp R P A

end Rings

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem smooth_of_comp_of_etale_of_surjective {X Y S : Scheme.{0}} (π : X ⟶ Y) (s : Y ⟶ S)
    [IsLocallyNoetherian S] [Etale π] [Surjective π] [LocallyOfFiniteType s] [Smooth (π ≫ s)] :
    Smooth s := by
  have : LocallyOfFinitePresentation s := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  have : Flat π := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale π›).1
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := π.surjective y
  rw [Scheme.Hom.mem_smoothLocus]
  have h : ((π ≫ s).stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp ((π ≫ s).smoothLocus_eq_top.ge (Set.mem_univ x))
  rw [Scheme.Hom.stalkMap_comp] at h
  replace h : ((π.stalkMap x).hom.comp (s.stalkMap (π x)).hom).FormallySmooth := h
  have hs : (π.stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (π.smoothLocus_eq_top.ge (Set.mem_univ x))
  have hu := FormallyUnramified.stalkMap π x
  have hf := faithfullyFlat_stalkMap_of_flat π x
  have e₁ := LocallyOfFiniteType.stalkMap π x
  have e₂ := LocallyOfFiniteType.stalkMap s (π x)
  algebraize [(π.stalkMap x).hom, (s.stalkMap (π x)).hom, (π.stalkMap x).hom.comp (s.stalkMap (π x)).hom]
  have : Algebra.FormallyEtale (Y.presheaf.stalk (π x)) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  exact formallySmooth_of_faithfullyFlat (S.presheaf.stalk (s (π x))) (Y.presheaf.stalk (π x))
    (X.presheaf.stalk x)

theorem smoothOfRelativeDimension_of_etale_cover :
    ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  intro K _ X Y π s d _ _ _ hd
  have : Smooth (π ≫ s) := SmoothOfRelativeDimension.smooth d _
  have : Smooth s := smooth_of_comp_of_etale_of_surjective π s
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose n W hW hn using H1.exists_dim s
  have key (y : Y) : n y = d := by
    obtain ⟨x, rfl⟩ := π.surjective y
    have := hn (π x)
    have h₁ : SmoothOfRelativeDimension (0 + n (π x)) ((π ∣_ W (π x)) ≫ (W (π x)).ι ≫ s) := inferInstance
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
    have h₂ : SmoothOfRelativeDimension (0 + d) ((π ⁻¹ᵁ W (π x)).ι ≫ π ≫ s) := inferInstance
    simpa using H1.dim_unique _ h₁ h₂ ⟨x, hW (π x)⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W ?_ fun y => key y ▸ hn y
  rw [← top_le_iff]
  rintro y -
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩

end GlobalTheory.SmoothDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_descends_etale_cover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  first | exact @GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover | exact GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover | (intros; apply GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.NearBuild

variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {R R' : Type} [CommRing R] [CommRing R']

abbrev loc (f : R) : R →+* Localization.Away f := algebraMap R (Localization.Away f)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (x : B →+* C) (y : A →+* B) :
    spMap (x.comp y) = spMap x ≫ spMap y := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)

def Good {K : Type} [Field K] (x : R →+* K) {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) : Prop :=
  s = spMap x ≫ spMap β ∧ t.Shape Mat κ ∧ t.HasTh (𝟙 _) (fun a => x (v a))

def Den (q₀ : Ideal R) : Prop := DenseP (objPrimes b Mat κ β v) ∧ q₀ ∈ objPrimes b Mat κ β v

def Concl : Prop :=
  ∃ t : TObj g (N' ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t' → TMap t' t (spMap x)

def NearC (q₀ : Ideal R) : Prop :=
  ∃ f : R, f ∉ q₀ ∧ Concl b Mat κ ((loc f).comp β) (fun a => loc f (v a))

def FibData (m : ℕ) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R) {Hh : Type} (hh : Hh → Ix g (N' ^ 2)) (Q : Polynomial ℚ)
    (d : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
    Good b Mat κ β v x t →
    ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _))))
      (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) K)), t.Emb m (Over.mk (𝟙 _)) σ ∧
      ProjRep I (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ ∧ (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧
      CutBy I Q d (fun h a => x (p (hh h) a)) ∧
      ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N')).left (fun a => x (p h a))
end

def Fib {b : TBase o (N' ^ 2)} (m : ℕ) {Z : Over (Sp R)} (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec)
    (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) {K : Type} [Field K] (x : R →+* K) {s : Sp K ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ Z.left) : Prop :=
  IsPullback φ t.A.hom Z.hom (spMap x) ∧
    (∃ σ, t.Emb m (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t.A).left)
      (w : Ix g (N' ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ) w) ∧
    LBIso (lbPow t.L (m ^ 2)) (M.pull φ) ∧ ∀ h, (t.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left

section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) {Z : Over (Sp R)} (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec)
  (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z))

def Fam : Prop :=
  (∃ (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) R)) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R),
    ProjRep I Z.hom M th ∧ ∀ h, SecCoord M th (sc h).left (p h)) ∧ Flat Z.hom ∧
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
    Good b Mat κ β v x t → ∃ φ, Fib m M th sc x t φ

def AddOk (ρ : R →+* R') {Z' : Over (Sp R')} (π : Z'.left ⟶ Z.left) (mu : Z' ⊗ Z' ⟶ Z') : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z'.left), Good b Mat κ β v (x.comp ρ) t → Fib m M th sc (x.comp ρ) t (φ ≫ π) →
    φ ≫ Z'.hom = t.A.hom ≫ spMap x →
    ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z' ⊗ Z').left, IsSquare φ φ₂ → φ₂ ≫ mu.left = (μ[t.A]).left ≫ φ

def EndOk (ρ : R →+* R') {Z' : Over (Sp R')} (π : Z'.left ⟶ Z.left) (i : Option J) (F : Z' ⟶ Z') : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z'.left), Good b Mat κ β v (x.comp ρ) t → Fib m M th sc (x.comp ρ) t (φ ≫ π) →
    φ ≫ Z'.hom = t.A.hom ≫ spMap x →
    φ ≫ F.left = (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ

def AddAt (mu : Z ⊗ Z ⟶ Z) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z.left), Good b Mat κ β v x t → Fib m M th sc x t φ →
    ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ mu.left = (μ[t.A]).left ≫ φ

def EndAt (i : Option J) (F : Z ⟶ Z) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z.left), Good b Mat κ β v x t → Fib m M th sc x t φ →
    φ ≫ F.left = (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ
end

def Lab (k : ℕ) {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) : Prop :=
  (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ k = 1) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 →
      ∃! c : Ix g k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ Q i)
        (fun i => (c i).val) = y

def GLies {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (y : S' ⟶ S) {s : S' ⟶ Sp o} (t : TObj g (N' ^ 2) J b s)
    (ψ : t.A.left ⟶ A.left) : Prop :=
  IsGrpPullback t.A A y ψ ∧ (∀ i, (t.act i).left ≫ ψ = ψ ≫ (act i).left) ∧
    ∀ i, (t.pt i ^ N').left ≫ ψ = y ≫ (Q i).left

section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)

def GrpFam (m : ℕ) (A : Over (Sp R)) [GrpObj A] (M : LB A.left) (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ M.IsLB ∧ Out.RelAmple A M ∧ Lab N' A act Q ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t → ∃ ψ, GLies A act Q (spMap x) t ψ ∧ LBIso (lbPow t.L (m ^ 2)) (M.pull ψ)

def PolFam (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧
    Out.RelAmple A L ∧ Lab N' A act Q ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t → ∃ ψ, GLies A act Q (spMap x) t ψ ∧ LBIso t.L (L.pull ψ)

variable {b Mat κ β v}

theorem good_comp (ρ : R →+* R') {K : Type} [Field K] (x : R' →+* K) {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) :
    Good b Mat κ (ρ.comp β) (fun a => ρ (v a)) x t ↔ Good b Mat κ β v (x.comp ρ) t := by
  simp only [Good, spMap_comp, Category.assoc, RingHom.comp_apply]

theorem mem_objPrimes {q : Ideal R} : q ∈ objPrimes b Mat κ β v ↔
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      RingHom.ker x = q ∧ Good b Mat κ β v x t := by
  constructor
  · rintro ⟨K, hF, hA, x, t, hk, hs, hth⟩
    exact ⟨K, hF, hA, x, _, t, hk, rfl, hs, hth⟩
  · rintro ⟨K, hF, hA, x, s, t, hk, ⟨rfl, hs, hth⟩⟩
    exact ⟨K, hF, hA, x, t, hk, hs, hth⟩

theorem isPrime_of_mem {q : Ideal R} (h : q ∈ objPrimes b Mat κ β v) : q.IsPrime := by
  obtain ⟨K, hF, -, x, -, rfl, -⟩ := h
  exact RingHom.ker_isPrime x

theorem exists_mem_loc {q : Ideal R} (h : q ∈ objPrimes b Mat κ β v) {f : R} (hf : f ∉ q) :
    ∃ q₁ ∈ objPrimes b Mat κ ((loc f).comp β) (fun a => loc f (v a)), q₁.comap (loc f) = q := by
  obtain ⟨K, hF, hA, x, s, t, hk, hg⟩ := mem_objPrimes.1 h
  have hu : IsUnit (x f) := by
    refine isUnit_iff_ne_zero.2 fun h0 => hf ?_
    rw [← hk]
    exact h0
  let y : Localization.Away f →+* K := IsLocalization.Away.lift f hu
  have hy : y.comp (loc f) = x := IsLocalization.Away.lift_comp f hu
  refine ⟨RingHom.ker y, mem_objPrimes.2 ⟨K, hF, hA, y, s, t, rfl, ?_⟩, ?_⟩
  · rw [good_comp, hy]
    exact hg
  · rw [RingHom.comap_ker, hy, hk]

theorem densePrimes_localization (h : DenseP (objPrimes b Mat κ β v)) (f : R) :
    DenseP (objPrimes b Mat κ ((loc f).comp β) (fun a => loc f (v a))) := by
  intro g hg
  obtain ⟨⟨a, c⟩, hc⟩ := IsLocalization.surj (Submonoid.powers f) g
  have hfa : f * a = 0 := by
    apply h
    intro p hp _
    by_cases hfp : f ∈ p
    · exact p.mul_mem_right a hfp
    · obtain ⟨q₁, hq₁, hcomap⟩ := exists_mem_loc hp hfp
      have hgq : g ∈ q₁ := hg q₁ hq₁ (isPrime_of_mem hq₁)
      have haq : algebraMap R (Localization.Away f) a ∈ q₁ := by
        rw [← hc]
        exact q₁.mul_mem_right _ hgq
      have : a ∈ p := by
        rw [← hcomap]
        exact haq
      exact p.mul_mem_left f this
  have hloc : algebraMap R (Localization.Away f) a = 0 := by
    have h1 := congrArg (algebraMap R (Localization.Away f)) hfa
    rw [map_mul, map_zero] at h1
    exact (IsLocalization.Away.algebraMap_isUnit f).mul_right_eq_zero.1 h1
  have hcu : IsUnit (algebraMap R (Localization.Away f) (c : R)) :=
    IsLocalization.map_units (Localization.Away f) c
  simp only at hc
  rw [hloc] at hc
  exact hcu.mul_left_eq_zero.1 hc

theorem Den.loc {q₀ : Ideal R} (h : Den b Mat κ β v q₀) {f : R} (hf : f ∉ q₀) :
    ∃ q₁, Den b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ ∧ q₁.comap (loc f) = q₀ := by
  obtain ⟨q₁, hq₁, hcomap⟩ := exists_mem_loc h.2 hf
  exact ⟨q₁, ⟨densePrimes_localization h.1 f, hq₁⟩, hcomap⟩

theorem FibData.comp {m : ℕ} {p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R} {Hh : Type} {hh : Hh → Ix g (N' ^ 2)}
    {Q : Polynomial ℚ} {d : ℕ} (h : FibData b Mat κ β v m p hh Q d) (ρ : R →+* R') :
    FibData b Mat κ (ρ.comp β) (fun a => ρ (v a)) m (fun c a => ρ (p c a)) hh Q d := by
  intro K _ _ x s t hg
  exact h K (x.comp ρ) s t ((good_comp ρ x t).1 hg)

theorem dense_of_denseP {P : Set (Ideal R)} (h : DenseP P) : Dense {p : Sp R | p.asIdeal ∈ P} := by
  have hv : PrimeSpectrum.vanishingIdeal {p : PrimeSpectrum R | p.asIdeal ∈ P} = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_bot]
    refine h a fun p hp hpr => ?_
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 ha ⟨p, hpr⟩ hp
  have hc : closure {p : PrimeSpectrum R | p.asIdeal ∈ P} = Set.univ := by
    rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hv]
    simp
  exact dense_iff_closure_eq.2 hc
end

end GlobalTheory.ZM.NearBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LinDescent

private lemma isOpenImmersion_of_section_of_etale' {X Y : Scheme.{0}} (s : Y ⟶ X) (g : X ⟶ Y)
    [Etale g] (h : s ≫ g = 𝟙 Y) : IsOpenImmersion s := by
  have hP : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr fun _ _ f hf => by
      have : Etale f := hf
      exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))
  refine MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @Etale) s g inferInstance ?_
  rw [h]
  infer_instance

private lemma exists_mem_range_lift_of_isGaloisCover {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga]
    {ρ : Ga → (X ⟶ X)} (h : IsGaloisCover Ga ρ π) (p : ↥(pullback π π)) :
    ∃ a, p ∈ Set.range ⇑(pullback.lift (ρ a) (𝟙 X) (by rw [h.inv a, Category.id_comp]) :
      X ⟶ pullback π π) := by
  let K := AlgebraicClosure ((pullback π π).residueField p)
  let q : Spec (CommRingCat.of K) ⟶ pullback π π :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑((pullback π π).residueField p) K)) ≫ (pullback π π).fromSpecResidueField p
  obtain ⟨a, ha, -⟩ := h.fibre K (q ≫ pullback.snd π π) (q ≫ pullback.fst π π)
    (by simp only [Category.assoc, pullback.condition])
  let x : ↥(Spec (CommRingCat.of K)) := show PrimeSpectrum K from IsLocalRing.closedPoint K
  refine ⟨a, (q ≫ pullback.snd π π) x, ?_⟩
  have e : (q ≫ pullback.snd π π) ≫ pullback.lift (ρ a) (𝟙 X) (by rw [h.inv a, Category.id_comp]) = q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact ha
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  have hq : q x = p := by
    have hx : q x ∈ Set.range ((pullback π π).fromSpecResidueField p) :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rw [Scheme.range_fromSpecResidueField] at hx
    exact Set.mem_singleton_iff.mp hx
  calc _ = ((q ≫ pullback.snd π π) ≫ pullback.lift (ρ a) (𝟙 X)
        (by rw [h.inv a, Category.id_comp])) x := (Scheme.Hom.comp_apply _ _ _).symm
    _ = q x := by rw [e]
    _ = p := hq

theorem locTransitive_of_isGaloisCover {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga]
    {ρ : Ga → (X ⟶ X)} (h : IsGaloisCover Ga ρ π) : LocTransitive ρ π := by
  intro Z g₁ g₂ hg z
  let φ : Z ⟶ pullback π π := pullback.lift g₁ g₂ hg
  obtain ⟨c, hc⟩ := exists_mem_range_lift_of_isGaloisCover h (φ z)
  let gr : X ⟶ pullback π π := pullback.lift (ρ c) (𝟙 X) (by rw [h.inv c, Category.id_comp])
  have : Etale π := h.etale
  have : IsOpenImmersion gr :=
    isOpenImmersion_of_section_of_etale' gr (pullback.snd π π) (pullback.lift_snd _ _ _)
  let U : Z.Opens := φ ⁻¹ᵁ gr.opensRange
  have hr : Set.range (U.ι ≫ φ) ⊆ Set.range gr := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact v.2
  let lw := IsOpenImmersion.lift gr (U.ι ≫ φ) hr
  have hw : lw ≫ gr = U.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨c, U.toScheme, U.ι, inferInstance, ⟨z, hc⟩, rfl, ?_⟩
  have h1 : U.ι ≫ g₁ = lw ≫ ρ c := by
    have e := congrArg (· ≫ pullback.fst π π) hw
    simp only [Category.assoc, gr, φ, pullback.lift_fst] at e
    exact e.symm
  have h2 : U.ι ≫ g₂ = lw := by
    have e := congrArg (· ≫ pullback.snd π π) hw
    simp only [Category.assoc, gr, φ, pullback.lift_snd, Category.comp_id] at e
    exact e.symm
  rw [h1, h2]

theorem exists_descent_of_isGaloisCover :
    ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (L : LB X), IsGaloisCover Ga ρ π → L.IsLB → ∀ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a)))) → ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  intro X Y π Ga _ ρ L hG hL u hu hc
  have : Finite Ga := hG.finite
  have : IsFinite π := hG.fin
  have : Etale π := hG.etale
  have : Surjective π := hG.onto
  have hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      Function.Injective fun c => r ≫ ρ c := by
    intro k _ _ r a b hab
    obtain ⟨d, -, hd⟩ := hG.fibre k r (r ≫ ρ a) (by rw [Category.assoc, hG.inv])
    exact (hd a rfl).trans (hd b hab.symm).symm
  exact exists_descent_of_galois hL hG.one (fun a c => (hG.mul a c).symm) hG.inv
    (locTransitive_of_isGaloisCover hG) hfree hu hc

end GlobalTheory.LinDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_linearised_lineBundle_galoisCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (L : LB X), IsGaloisCover Ga ρ π → L.IsLB → ∀ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a)))) → ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  first | exact @GlobalTheory.LinDescent.exists_descent_of_isGaloisCover | exact GlobalTheory.LinDescent.exists_descent_of_isGaloisCover | (intros; apply GlobalTheory.LinDescent.exists_descent_of_isGaloisCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.ZM.CycBase

abbrev CF (k : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zeta k}

def zF (k : ℕ) : CF k := ⟨zeta k, IntermediateField.subset_adjoin _ _ rfl⟩

private lemma zeta_isPrimitiveRoot' {k : ℕ} (hk : k ≠ 0) : IsPrimitiveRoot (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta k) k := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta; exact Complex.isPrimitiveRoot_exp k hk

lemma _root_.GlobalTheory.ZM.CycBase.zF_prim {k : ℕ} (hk : k ≠ 0) :
    IsPrimitiveRoot (_root_.GlobalTheory.ZM.CycBase.zF k) k :=
  IsPrimitiveRoot.of_map_of_injective (f := (_root_.GlobalTheory.ZM.CycBase.CF k).val)
    (zeta_isPrimitiveRoot' hk) (_root_.GlobalTheory.ZM.CycBase.CF k).val.injective

lemma _root_.GlobalTheory.ZM.CycBase.cyc {k : ℕ} [NeZero k] :
    IsCyclotomicExtension {k} ℚ (_root_.GlobalTheory.ZM.CycBase.CF k) := by
  have hζ := zeta_isPrimitiveRoot' (NeZero.ne k)
  haveI := hζ.adjoin_isCyclotomicExtension ℚ
  have h2 : (_root_.GlobalTheory.ZM.CycBase.CF k).toSubalgebra = Algebra.adjoin ℚ {_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta k} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral (NeZero.pos k)).tower_top.isAlgebraic)
  exact IsCyclotomicExtension.equiv _ _ _ (Subalgebra.equivOfEq _ _ h2).symm

lemma _root_.GlobalTheory.ZM.CycBase.mem_ZP (p n e : ℕ) (hn : n.Prime) (a : 𝓞 (_root_.GlobalTheory.ZM.CycBase.CF (n ^ e))) :
    ((a : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) : ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) := by
  haveI : Fact n.Prime := ⟨hn⟩
  haveI : NeZero (n ^ e) := ⟨pow_ne_zero _ hn.ne_zero⟩
  haveI := _root_.GlobalTheory.ZM.CycBase.cyc (k := n ^ e)
  have hζ := _root_.GlobalTheory.ZM.CycBase.zF_prim (NeZero.ne (n ^ e))
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  obtain ⟨x, hx⟩ := hcl.isIntegral_iff.mp (RingOfIntegers.isIntegral_coe a)
  have hax : (a : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) = x := hx.symm
  rw [hax]
  obtain ⟨y, hmem⟩ := x
  change ((y : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) : ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)
  clear hx hax
  induction hmem using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
    exact Subring.subset_closure (Or.inl rfl)
  | algebraMap r =>
    simpa using intCast_mem (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) r
  | add y z _ _ hy hz => simpa using add_mem hy hz
  | mul y z _ _ hy hz => simpa using mul_mem hy hz

private lemma inv_natCast_mem_ZP_of_coprime {p M m : ℕ} (hm : m.Coprime p) :
    ((m : ℂ)⁻¹) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
  exact Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)

private lemma snd_eq_zero_of_natCast_mul_eq_one {K : Type} [Field K] {m : ℕ} {v : DualNumber K}
    (h : (m : DualNumber K) * v = 1) : v.snd = 0 ∧ (m : K) ≠ 0 := by
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp at h1 h2
  have hm : (m : K) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨by simpa [hm] using h2, hm⟩

private lemma zeta_mem_ZP (p M : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta M ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
  exact Subring.subset_closure (Or.inl rfl)

private lemma ringHom_ZP_pow_dualNumber_snd_eq_zero {K : Type} [Field K] {p n e : ℕ}
    (hn : n.Coprime p) (hn0 : n ≠ 0) (f : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) →+* DualNumber K)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) : (f x).snd = 0 := by
  have hnK : (n : K) ≠ 0 := by
    have hmul : ((n : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) * ⟨(n : ℂ)⁻¹, inv_natCast_mem_ZP_of_coprime hn⟩ = 1 := by
      apply Subtype.ext; simp [hn0]
    have := congrArg f hmul
    rw [map_mul, map_natCast, map_one] at this
    exact (snd_eq_zero_of_natCast_mul_eq_one this).2
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with hy | ⟨m, hm, rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      set z := f ⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e), zeta_mem_ZP p _⟩ with hz
      have hN : n ^ e ≠ 0 := pow_ne_zero _ hn0
      have hpow : z ^ (n ^ e) = 1 := by
        rw [hz, ← map_pow]
        have : (⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e), zeta_mem_ZP p _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) ^ (n ^ e) = 1 :=
          Subtype.ext (by simpa using (zeta_isPrimitiveRoot' hN).pow_eq_one)
        rw [this, map_one]
      have h1 := congrArg TrivSqZeroExt.fst hpow
      have h2 := congrArg TrivSqZeroExt.snd hpow
      simp only [TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_one] at h1
      rw [TrivSqZeroExt.snd_pow, TrivSqZeroExt.snd_one] at h2
      have hz0 : z.fst ≠ 0 := by
        intro h0; rw [h0, zero_pow hN] at h1; exact zero_ne_one h1
      simp only [nsmul_eq_mul, smul_eq_mul] at h2
      have hNK : ((n ^ e : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hnK
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hNK
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd (pow_eq_zero_iff'.mp h).1 hz0
        · exact h
    · by_cases hm0 : m = 0
      · subst hm0
        have : (⟨((0 : ℕ) : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨0, hm, rfl⟩)⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 0 :=
          Subtype.ext (by simp)
        rw [this, map_zero]; rfl
      · have hmul : ((m : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) *
            ⟨(m : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)⟩ = 1 := by
          apply Subtype.ext; simp [hm0]
        have := congrArg f hmul
        rw [map_mul, map_natCast, map_one] at this
        exact (snd_eq_zero_of_natCast_mul_eq_one this).1
  | zero => rw [show (⟨0, _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 0 from rfl, map_zero]; rfl
  | one => rw [show (⟨1, _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 1 from rfl, map_one]; rfl
  | add y z hy hz ihy ihz =>
    rw [show (⟨y + z, add_mem hy hz⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = ⟨y, hy⟩ + ⟨z, hz⟩ from rfl, map_add (f := _),
      TrivSqZeroExt.snd_add, ihy, ihz, add_zero]
  | neg y hy ihy =>
    rw [show (⟨-y, neg_mem hy⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = -⟨y, hy⟩ from rfl, map_neg,
      TrivSqZeroExt.snd_neg, ihy, neg_zero]
  | mul y z hy hz ihy ihz =>
    rw [show (⟨y * z, mul_mem hy hz⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl, map_mul,
      TrivSqZeroExt.snd_mul, ihy, ihz, smul_zero, smul_zero, add_zero]

private lemma spec_dualNumber_hom_ZP_eq_constPt {K : Type} [Field K] {p n e : ℕ}
    (hn : n.Coprime p) (hn0 : n ≠ 0)
    (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e))) : y = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
  conv_lhs => rw [← Spec.map_preimage y]
  conv_rhs => rw [← Spec.map_preimage y]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, ringHom_ZP_pow_dualNumber_snd_eq_zero hn hn0]

theorem _root_.GlobalTheory.ZM.CycBase.exists_base : ∀ (n e p k : ℕ), n.Prime → p.Prime → n ≠ p → 1 ≤ e →
    k = n ^ e → ∃ (o : Type) (_ : CommRing o) (b : _root_.GlobalTheory.ZM.TBase o k) (em : o →+* ℂ)
      (j : o →+* _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k), _root_.GlobalTheory.ZM.ArBase em ∧ j (b.ζ : o) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zetaZP p k ∧
      (∀ x, ((j x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k) : ℂ) = em x) ∧
      ∀ (K : Type) [Field K] (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k)), y = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt y := by
  intro n e p k hn hp hnp _ hk
  subst hk
  have hN : n ^ e ≠ 0 := pow_ne_zero _ hn.ne_zero
  haveI : NeZero (n ^ e) := ⟨hN⟩
  haveI := _root_.GlobalTheory.ZM.CycBase.cyc (k := n ^ e)
  haveI : NumberField (_root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) :=
    IsCyclotomicExtension.numberField {n ^ e} ℚ _
  have hcop : n.Coprime p := (Nat.coprime_primes hn hp).mpr hnp
  set F := _root_.GlobalTheory.ZM.CycBase.CF (n ^ e) with hF
  obtain ⟨em, har, hcomp⟩ :=
    _root_.GlobalTheory.ZM.exists_arBase_away (F := F) F.val.toRingHom hn.ne_zero
  have hζ := _root_.GlobalTheory.ZM.CycBase.zF_prim hN
  have hζi := hζ.toInteger_isPrimitiveRoot
  have hpos : 0 < n ^ e := Nat.pos_of_ne_zero hN
  let u : (𝓞 F)ˣ := (hζi.isUnit hN).unit
  let ζo : (Localization.Away (n : 𝓞 F))ˣ := Units.map (algebraMap (𝓞 F) _).toMonoidHom u
  have hkunit : IsUnit ((n ^ e : ℕ) : Localization.Away (n : 𝓞 F)) := by
    have := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (n : 𝓞 F))
      (n : 𝓞 F)).pow e
    simpa using this
  have hprim : ∀ (K : Type) [Field K] (β : Localization.Away (n : 𝓞 F) →+* K),
      IsPrimitiveRoot (β ζo) (n ^ e) := by
    intro K _ β
    have hroot := (hζi.isRoot_cyclotomic hpos).map (f := β.comp (algebraMap (𝓞 F) _))
    rw [Polynomial.map_cyclotomic] at hroot
    haveI : NeZero ((n ^ e : ℕ) : K) := ⟨by simpa using (hkunit.map β).ne_zero⟩
    exact Polynomial.isRoot_cyclotomic_iff.mp hroot
  let b : _root_.GlobalTheory.ZM.TBase (Localization.Away (n : 𝓞 F)) (n ^ e) := ⟨ζo, hkunit, hprim⟩
  have hcompx : ∀ a : 𝓞 F, em (algebraMap _ _ a) = ((a : F) : ℂ) := fun a =>
    RingHom.congr_fun hcomp a
  have hmemZ : ∀ x, em x ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (n : 𝓞 F)) x
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hspec := congrArg em (IsLocalization.mk'_spec (Localization.Away (n : 𝓞 F)) a s)
    rw [map_mul, hcompx, hcompx, ← hm] at hspec
    have hnm : (((((n : 𝓞 F) ^ m : 𝓞 F)) : F) : ℂ) = (n : ℂ) ^ m := by simp
    rw [hnm] at hspec
    have hn0 : (n : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne_zero)
    rw [eq_div_of_mul_eq hn0 hspec, div_eq_mul_inv, ← inv_pow]
    exact mul_mem (_root_.GlobalTheory.ZM.CycBase.mem_ZP p n e hn a)
      (pow_mem (inv_natCast_mem_ZP_of_coprime hcop) m)
  refine ⟨Localization.Away (n : 𝓞 F), inferInstance, b, em, em.codRestrict _ hmemZ, har, ?_,
    fun x => rfl, ?_⟩
  · apply Subtype.ext
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zetaZP
    change em (algebraMap (𝓞 F) _ hζ.toInteger) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e)
    rw [hcompx]
    exact congrArg Subtype.val hζ.coe_toInteger
  · intro K _ y
    exact spec_dualNumber_hom_ZP_eq_constPt hcop hn.ne_zero y

end GlobalTheory.ZM.CycBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomic_base_ring_inverting_prime : ∀ (n e p k : ℕ), n.Prime → p.Prime → n ≠ p → 1 ≤ e → k = n ^ e → ∃ (o : Type) (_ : CommRing o) (b : TBase o k) (em : o →+* ℂ) (j : o →+* ZP p k), ArBase em ∧ j (b.ζ : o) = zetaZP p k ∧ (∀ x, ((j x : ZP p k) : ℂ) = em x) ∧ ∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y := by
  first | exact @GlobalTheory.ZM.CycBase.exists_base | exact GlobalTheory.ZM.CycBase.exists_base | (intros; apply GlobalTheory.ZM.CycBase.exists_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsDescendToLargeSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsDescendToLargeSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem morphisms_descend_to_large_subfield :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀ := by
  intro K _ K₀ X₀ X p₀ p φ Z q _ _ _ I _ f hX hf
  have hX' : IsPullback φ p p₀ (spMap (algebraMap K₀ K)) := hX
  obtain ⟨R, g, ⟨s, rfl⟩, -, hg⟩ := Spread.exists_fg_forall_comp_eq (A := K) p₀ q
    (fun j ↦ hX'.isoPullback.inv ≫ f j)
    (fun j ↦ by rw [Category.assoc, hf, IsPullback.isoPullback_inv_fst_assoc]) ⊥ Subalgebra.fg_bot
  refine ⟨s, fun K₁ h hs X₁ p₁ φ₁ ψ h₁ hψ₁ hψ₂ ↦ ?_⟩
  have hle : ∀ x ∈ Algebra.adjoin K₀ (s : Set K), x ∈ K₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  let e : Algebra.adjoin K₀ (s : Set K) →+* K₁ :=
    (Algebra.adjoin K₀ (s : Set K)).val.toRingHom.codRestrict K₁ fun x ↦ hle x x.2
  have he₁ : spMap e ≫ spMap (algebraMap K₀ (Algebra.adjoin K₀ (s : Set K))) =
      spMap (Subfield.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have he₂ : spMap K₁.subtype ≫ spMap e =
      spMap (Algebra.adjoin K₀ (s : Set K)).val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let u : X₁ ⟶ pullback p₀ (spMap (algebraMap K₀ (Algebra.adjoin K₀ (s : Set K)))) :=
    pullback.lift φ₁ (p₁ ≫ spMap e) (by rw [Category.assoc, he₁, h₁.w])
  have hu : ψ ≫ u = hX'.isoPullback.hom ≫ Spread.bcMap p₀ (Algebra.adjoin K₀ (s : Set K)).val := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst,
        pullback.lift_fst, hψ₁]
    · rw [Category.assoc, Category.assoc, Spread.bcMap_snd, IsPullback.isoPullback_hom_snd_assoc,
        pullback.lift_snd, ← Category.assoc, hψ₂, Category.assoc, he₂]
  refine ⟨fun j ↦ u ≫ g j, fun j ↦ ⟨?_, ?_⟩⟩
  · rw [← Category.assoc, hu, Category.assoc, (hg j).2, Iso.hom_inv_id_assoc]
  · rw [Category.assoc, (hg j).1, pullback.lift_fst_assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsDescendToLargeSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_descent_of_morphisms_to_subfield : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀ := by
  first | exact @GlobalTheory.morphisms_descend_to_large_subfield | exact GlobalTheory.morphisms_descend_to_large_subfield | (intros; apply GlobalTheory.morphisms_descend_to_large_subfield <;> assumption)
end
end
