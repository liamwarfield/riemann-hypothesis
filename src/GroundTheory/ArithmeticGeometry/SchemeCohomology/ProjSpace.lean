module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistAway
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable (A : Type u) [CommRing A] (n : ℕ)

abbrev grading : ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A) :=
  homogeneousSubmodule (Fin (n + 1)) A

end ProjSpace

open ProjSpace

abbrev projectiveSpace (A : Type u) [CommRing A] (n : ℕ) : Scheme.{u} := Proj (grading A n)

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

def stdOpen (A : Type u) [CommRing A] (n : ℕ) (j : Fin (n + 1)) : (projectiveSpace A n).Opens :=
  Proj.basicOpen (grading A n) (X j)

def xprod {p : ℕ} (i : Fin p → Fin (n + 1)) : MvPolynomial (Fin (n + 1)) A := ∏ a, X (i a)

lemma xprod_mem {p : ℕ} (i : Fin p → Fin (n + 1)) : xprod (A := A) i ∈ grading A n p := by
  have := IsHomogeneous.prod (Finset.univ : Finset (Fin p)) (fun a => (X (i a) : MvPolynomial _ A))
    (fun _ => 1) (fun a _ => isHomogeneous_X A (i a))
  simpa [xprod] using this

lemma X_mem (j : Fin (n + 1)) : (X j : MvPolynomial (Fin (n + 1)) A) ∈ grading A n 1 :=
  isHomogeneous_X A j

lemma xprod_succ {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    xprod (A := A) i = X (i 0) * xprod (A := A) (i ∘ Fin.succ) := by
  simp [xprod, Fin.prod_univ_succ]

lemma inter_stdOpen {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i =
      Proj.basicOpen (grading A n) (xprod i) := by
  ext x
  change x ∈ inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i ↔ _
  rw [mem_inter_iff]
  change (∀ a, x ∈ stdOpen A n (i a)) ↔ x ∈ Proj.basicOpen (grading A n) (xprod i)
  change (∀ a, X (i a) ∉ x.asHomogeneousIdeal.toIdeal) ↔
    (∏ a, X (i a)) ∉ x.asHomogeneousIdeal.toIdeal
  have := x.isPrime
  rw [Ideal.IsPrime.prod_mem_iff]
  simp

lemma isAffineOpen_inter {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    IsAffineOpen (inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i) := by
  rw [inter_stdOpen]
  exact Proj.isAffineOpen_basicOpen (grading A n) (xprod i) (xprod_mem i) (Nat.succ_pos p)

lemma isAffineOpen_stdOpen (j : Fin (n + 1)) : IsAffineOpen (stdOpen A n j) :=
  Proj.isAffineOpen_basicOpen (grading A n) (X j) (X_mem j) Nat.one_pos

lemma iSup_stdOpen : ⨆ j, stdOpen A n j = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  intro p hp
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  subst hm0
  have h0 : GradedRing.proj (grading A n) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' p 0 : homogeneousSubmodule (Fin (n + 1)) A 0) :
    MvPolynomial (Fin (n + 1)) A) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at h0
  exact (MvPolynomial.mem_support_iff.mp hm) h0

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing

universe u

theorem IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsPrincipalIdealRing R := by
  have : IsDomain R := IsRegularLocalRing.isDomain
  have hreg := (isRegularLocalRing_iff R).mp inferInstance
  have hle : (maximalIdeal R).spanFinrank ≤ 1 := by
    rw [← hreg] at h; exact_mod_cast h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · have hbot : maximalIdeal R = ⊥ := (Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal R).fg_of_isNoetherianRing).mp h0
    let := ((isField_iff_maximalIdeal_eq).mpr hbot).toField
    infer_instance
  · have : IsDiscreteValuationRing R := IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp (by
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]; exact h1)
    infer_instance

theorem IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_one {R : Type*}
    [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : UniqueFactorizationMonoid R :=
  have : IsDomain R := IsRegularLocalRing.isDomain
  have := IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one h
  inferInstance

theorem IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one {R : Type*}
    [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsIntegrallyClosed R :=
  have : IsDomain R := IsRegularLocalRing.isDomain
  have := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_one h
  inferInstance

theorem ringKrullDim_localization_le_of_etale {P B : Type*} [CommRing P] [CommRing B]
    [Algebra P B] [Algebra.Etale P B] [IsRegularRing P] (Q : Ideal B) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (Localization.AtPrime (Q.under P)) := by
  let p := Q.under P
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have hun : Algebra.IsUnramifiedAt P Q := inferInstance
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq P p Q).mp hun).2
  have h : (maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) =
      maximalIdeal (Localization.AtPrime Q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact hmap
  calc ringKrullDim (Localization.AtPrime Q)
      ≤ (maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
        ringKrullDim_le_spanFinrank_maximalIdeal _
    _ ≤ (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
        rw [← h]
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg _
          (maximalIdeal (Localization.AtPrime p)).fg_of_isNoetherianRing
    _ = ringKrullDim (Localization.AtPrime p) :=
        (isRegularLocalRing_iff (Localization.AtPrime p)).mp inferInstance

open AlgebraicGeometry CategoryTheory

theorem ringKrullDim_stalk_le_of_smoothOfRelativeDimension {X : Scheme.{u}} {k : Type u} [Field k]
    (n : ℕ) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ n := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hUtop : U = ⊤ := eq_top_iff.mpr fun y _ ↦ Subsingleton.elim (f.base x) y ▸ e hx
  subst hUtop
  let eΓ := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  have : IsRegularRing Γ(Spec (.of k), ⊤) := IsRegularRing.of_ringEquiv eΓ.symm
  have : IsNoetherianRing Γ(Spec (.of k), ⊤) := isNoetherianRing_of_ringEquiv k eΓ.symm
  have hdim0 : ringKrullDim Γ(Spec (.of k), ⊤) = 0 := by
    rw [ringKrullDim_eq_of_ringEquiv eΓ, ringKrullDim_eq_zero_of_field]
  algebraize [(f.appLE ⊤ V e).hom]
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n
    Γ(Spec (.of k), ⊤) Γ(X, V)
  algebraize [g.toRingHom]
  set P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P := hV.isLocalization_stalk ⟨x, hx⟩
  rw [← ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv (R := Γ(X, V)) P.primeCompl
    (Localization.AtPrime P) (X.presheaf.stalk x)).toRingEquiv]
  refine (ringKrullDim_localization_le_of_etale (P := MvPolynomial (Fin n) Γ(Spec (.of k), ⊤))
    P).trans ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (P.under (MvPolynomial (Fin n) Γ(Spec (.of k), ⊤))) (Localization.AtPrime _)]
  refine (Ideal.height_le_ringKrullDim_of_isPrime).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hdim0]
  simp

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.CechToDerived
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace Limits Abelian

universe w' u

variable {X : TopCat.{u}} {B : Opens X → Prop}

noncomputable def injectiveSequence (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

lemma injectiveSequence_shortExact (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (injectiveSequence F).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι F)))
    (inferInstanceAs (Mono (Injective.ι F))) coequalizer.π_epi

instance (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Injective (injectiveSequence F).X₂ :=
  inferInstanceAs (Injective (Injective.under F))

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorSheaf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}}

noncomputable def sectionValue [IsIntegral X] (V : X.Opens) (y : V) :
    Γ(X, V) →+* X.functionField :=
  (algebraMap (X.presheaf.stalk y) X.functionField).comp (X.presheaf.germ V y y.2).hom

lemma sectionValue_eq [IsIntegral X] (V : X.Opens) (y : V) (r : Γ(X, V)) :
    sectionValue V y r = (haveI : Nonempty V := ⟨y⟩; X.germToFunctionField V r) := by
  have : Nonempty V := ⟨y⟩
  exact Scheme.algebraMap_germ_eq_germToFunctionField X y.2 r

lemma sectionValue_res [IsIntegral X] {V W : X.Opens} (h : W ≤ V) (y : W) (r : Γ(X, V)) :
    sectionValue W y (X.presheaf.map (homOfLE h).op r) = sectionValue V ⟨y.1, h y.2⟩ r := by
  simp only [sectionValue, RingHom.comp_apply]
  congr 1
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

lemma sectionValue_const [IsIntegral X] (V : X.Opens) (y z : V) (r : Γ(X, V)) :
    sectionValue V y r = sectionValue V z r := by
  rw [sectionValue_eq, sectionValue_eq]

def PrimeDivisor.ofPoint (y : X) (hy : ringKrullDim (X.presheaf.stalk y) = 1) : PrimeDivisor X :=
  ⟨y, hy⟩

section

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

def divisorPredicate (D : WeilDivisor X) :
    TopCat.LocalPredicate (X := X.carrier) (fun _ => X.functionField) where
  pred {V} f := (∀ y : V, ∃ W : X.Opens, y.1 ∈ W ∧ ∀ z : V, z.1 ∈ W → f z = f y) ∧
    ∀ (y : V) (hy : ringKrullDim (X.presheaf.stalk y.1) = 1),
      (PrimeDivisor.ofPoint y.1 hy).valuation (f y) ≤ WithZero.exp (D (PrimeDivisor.ofPoint y.1 hy))
  res {V W} i f h := by
    refine ⟨fun y => ?_, fun y hy => h.2 (i y) hy⟩
    obtain ⟨W', hyW', hW'⟩ := h.1 (i y)
    exact ⟨W', hyW', fun z hz => hW' (i z) hz⟩
  locality {V} f w := by
    refine ⟨fun y => ?_, fun y hy => ?_⟩
    · obtain ⟨W, hyW, i, hW⟩ := w y
      obtain ⟨W', hyW', hW'⟩ := hW.1 ⟨y.1, hyW⟩
      refine ⟨W ⊓ W', ⟨hyW, hyW'⟩, fun z hz => ?_⟩
      exact hW' ⟨z.1, hz.1⟩ hz.2
    · obtain ⟨W, hyW, i, hW⟩ := w y
      exact hW.2 ⟨y.1, hyW⟩ hy

lemma PrimeDivisor.valuation_algebraMap_le_one (Z : PrimeDivisor X)
    (a : X.presheaf.stalk Z.point) : Z.valuation (algebraMap _ X.functionField a) ≤ 1 := by
  have := Z.isDedekindDomain_stalk
  simp only [PrimeDivisor.valuation]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _

def divisorSections (D : WeilDivisor X) (V : X.Opens) : AddSubgroup (V → X.functionField) where
  carrier := {f | (divisorPredicate D).pred f}
  zero_mem' := ⟨fun _ => ⟨⊤, trivial, fun _ _ => rfl⟩, fun y hy => by simp⟩
  add_mem' {f g} hf hg := by
    refine ⟨fun y => ?_, fun y hy => ?_⟩
    · obtain ⟨W₁, hy₁, h₁⟩ := hf.1 y
      obtain ⟨W₂, hy₂, h₂⟩ := hg.1 y
      exact ⟨W₁ ⊓ W₂, ⟨hy₁, hy₂⟩, fun z hz => by
        simp only [Pi.add_apply, h₁ z hz.1, h₂ z hz.2]⟩
    · exact (Valuation.map_add _ _ _).trans (max_le (hf.2 y hy) (hg.2 y hy))
  neg_mem' {f} hf := by
    refine ⟨fun y => ?_, fun y hy => ?_⟩
    · obtain ⟨W, hyW, h⟩ := hf.1 y
      exact ⟨W, hyW, fun z hz => by simp only [Pi.neg_apply, h z hz]⟩
    · simp only [Pi.neg_apply, Valuation.map_neg]
      exact hf.2 y hy

lemma smul_mem_divisorSections (D : WeilDivisor X) (V : X.Opens) (r : Γ(X, V))
    {f : V → X.functionField} (hf : f ∈ divisorSections D V) :
    (fun y => sectionValue V y r * f y) ∈ divisorSections D V := by
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨W, hyW, h⟩ := hf.1 y
    exact ⟨W, hyW, fun z hz => by simp only [h z hz, sectionValue_const V z y r]⟩
  · simp only [map_mul]
    calc _ ≤ 1 * WithZero.exp (D (PrimeDivisor.ofPoint y.1 hy)) :=
          mul_le_mul' ((PrimeDivisor.ofPoint y.1 hy).valuation_algebraMap_le_one
            (X.presheaf.germ V y.1 y.2 r)) (hf.2 y hy)
      _ = _ := one_mul _

noncomputable instance (D : WeilDivisor X) (V : X.Opens) :
    Module Γ(X, V) (divisorSections D V) where
  smul r f := ⟨fun y => sectionValue V y r * f.1 y, smul_mem_divisorSections D V r f.2⟩
  one_smul f := Subtype.ext (funext fun y => by
    change sectionValue V y 1 * f.1 y = f.1 y
    rw [map_one, one_mul])
  mul_smul r s f := Subtype.ext (funext fun y => by
    change sectionValue V y (r * s) * f.1 y = sectionValue V y r * (sectionValue V y s * f.1 y)
    rw [map_mul, mul_assoc])
  smul_zero r := Subtype.ext (funext fun y => by
    change sectionValue V y r * 0 = 0
    rw [mul_zero])
  smul_add r f g := Subtype.ext (funext fun y => by
    change sectionValue V y r * (f.1 y + g.1 y) = sectionValue V y r * f.1 y +
      sectionValue V y r * g.1 y
    rw [mul_add])
  add_smul r s f := Subtype.ext (funext fun y => by
    change sectionValue V y (r + s) * f.1 y = sectionValue V y r * f.1 y +
      sectionValue V y s * f.1 y
    rw [map_add (f := _), add_mul])
  zero_smul f := Subtype.ext (funext fun y => by
    change sectionValue V y 0 * f.1 y = 0
    rw [map_zero, zero_mul])

def divisorSectionsRes (D : WeilDivisor X) {V W : X.Opens} (h : W ≤ V) :
    divisorSections D V →+ divisorSections D W where
  toFun f := ⟨fun y => f.1 ⟨y.1, h y.2⟩, (divisorPredicate D).res (homOfLE h) f.1 f.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def divisorPresheaf (D : WeilDivisor X) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (divisorSections D V.unop)
  map i := AddCommGrpCat.ofHom (divisorSectionsRes D i.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable instance (D : WeilDivisor X) (V : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj V) ((divisorPresheaf D).obj V) :=
  inferInstanceAs (Module Γ(X, V.unop) (divisorSections D V.unop))

noncomputable def divisorPresheafOfModules (D : WeilDivisor X) :
    PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (divisorPresheaf D) (fun {V W} i r f => by
    apply Subtype.ext
    funext y
    exact congrArg (· * f.1 ⟨y.1, i.unop.le y.2⟩)
      (sectionValue_res i.unop.le y (show Γ(X, V.unop) from r)).symm)

theorem divisorPresheaf_isSheaf (D : WeilDivisor X) :
    TopCat.Presheaf.IsSheaf (X := X.carrier) (divisorPresheaf D) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]
  refine TopCat.Presheaf.isSheaf_of_iso ?_
    (TopCat.subpresheafToTypes.isSheaf (divisorPredicate D))
  refine NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) ?_
  intro V W i
  rfl

noncomputable def divisorSheaf (D : WeilDivisor X) : X.Modules :=
  SheafOfModules.mk (divisorPresheafOfModules D) (divisorPresheaf_isSheaf D)

lemma PrimeDivisor.valuation_le_exp_iff (Z : PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0)
    (n : ℤ) : Z.valuation f ≤ WithZero.exp n ↔ -n ≤ Z.ord f := by
  have hv0 : Z.valuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  rw [← WithZero.log_le_iff_le_exp hv0, PrimeDivisor.ord]
  omega

end

section Basis

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

end Basis

end GroundTheory.Arith.SchemeCoh
end
