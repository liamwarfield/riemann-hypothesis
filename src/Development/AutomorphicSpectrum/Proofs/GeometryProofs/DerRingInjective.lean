module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.Tan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R)

def augPart (f : B) : RingHom.ker ε :=
  ⟨f - algebraMap R B (ε f), by simp [RingHom.mem_ker]⟩

theorem augPart_coe (f : B) : ((augPart ε f : RingHom.ker ε) : B) = f - algebraMap R B (ε f) := rfl

theorem augPart_of_mem (f : RingHom.ker ε) : augPart ε f.1 = f := by
  apply Subtype.ext
  rw [augPart_coe, RingHom.mem_ker.mp f.2, map_zero, sub_zero]

theorem augPart_add (f g : B) : augPart ε (f + g) = augPart ε f + augPart ε g := by
  apply Subtype.ext
  simp only [Submodule.coe_add, augPart_coe, map_add (f := _)]
  abel

theorem augPart_smul (r : R) (f : B) : (RingHom.ker ε).toCotangent (augPart ε (r • f)) =
    r • (RingHom.ker ε).toCotangent (augPart ε f) := by
  have h : augPart ε (r • f) = algebraMap R B r • augPart ε f := by
    apply Subtype.ext
    have hr : algebraMap R R r = r := rfl
    simp only [Submodule.coe_smul, augPart_coe, smul_eq_mul, Algebra.smul_def, map_mul,
      AlgHom.commutes, hr]
    ring
  rw [h, map_smul, algebraMap_smul]

theorem augPart_mul (f g : B) : (RingHom.ker ε).toCotangent (augPart ε (f * g)) =
    (ε f) • (RingHom.ker ε).toCotangent (augPart ε g) + (ε g) • (RingHom.ker ε).toCotangent (augPart ε f) := by
  have hab : ((augPart ε f : B) * (augPart ε g : B)) ∈ RingHom.ker ε :=
    Ideal.mul_mem_left _ _ (augPart ε g).2
  have hdec : augPart ε (f * g) =
      ⟨(augPart ε f : B) * (augPart ε g : B), hab⟩ + algebraMap R B (ε f) • augPart ε g +
        algebraMap R B (ε g) • augPart ε f := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, augPart_coe, smul_eq_mul, map_mul]
    ring
  have h0 : (RingHom.ker ε).toCotangent ⟨(augPart ε f : B) * (augPart ε g : B), hab⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul (augPart ε f).2 (augPart ε g).2
  rw [hdec, map_add (f := _), map_add (f := _), h0, zero_add, map_smul, map_smul, algebraMap_smul, algebraMap_smul]

variable {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

def derRing (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) : B →ₐ[R] TrivSqZeroExt R V :=
  AlgHom.ofLinearMap
    { toFun := fun f => TrivSqZeroExt.inl (ε f) + TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent (augPart ε f)))
      map_add' := fun f g => by
        rw [augPart_add, map_add (f := _), map_add (f := _), map_add (f := _)]
        ext <;> simp <;> abel
      map_smul' := fun r f => by
        rw [augPart_smul, map_smul]
        ext <;> simp }
    (by
      have : augPart ε (1 : B) = 0 := by
        apply Subtype.ext
        simp [augPart_coe]
      simp [this])
    (fun f g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [augPart_mul, map_add (f := _), map_smul, map_smul]
      ext <;> simp [add_comm])

theorem derRing_apply (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (f : B) : derRing ε ψ f =
    TrivSqZeroExt.inl (ε f) + TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent (augPart ε f))) := rfl

theorem derRing_of_mem (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (f : RingHom.ker ε) :
    derRing ε ψ f.1 = TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent f)) := by
  rw [derRing_apply, augPart_of_mem, RingHom.mem_ker.mp f.2]
  simp

theorem derRing_injective {ψ ψ' : (RingHom.ker ε).Cotangent →ₗ[R] V} (h : derRing ε ψ = derRing ε ψ') : ψ = ψ' := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker ε) x
  have hy := congrArg TrivSqZeroExt.snd (DFunLike.congr_fun h y.1)
  simpa [derRing_of_mem] using hy

end Alg

section Op
variable (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]

abbrev opMod : Module Rᵐᵒᵖ V := Module.compHom V ((RingHom.id R).fromOpposite fun _ _ => mul_comm _ _)

theorem opCentral : @IsCentralScalar R V _ (opMod R V).toSMul := by
  exact @IsCentralScalar.mk R V _ (opMod R V).toSMul (fun _ _ => rfl)
end Op

section Red
variable {R : Type} [CommRing R] (I : Ideal R)

def kap : TrivSqZeroExt R (R ⧸ I) →ₐ[R] DualNumber (R ⧸ I) where
  toFun a := TrivSqZeroExt.inl (Ideal.Quotient.mk I a.fst) + TrivSqZeroExt.inr a.snd
  map_one' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' a b := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [TrivSqZeroExt.snd_mul, Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  commutes' r := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem kap_inr (q : R ⧸ I) : kap I (TrivSqZeroExt.inr q) = TrivSqZeroExt.inr q := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap]

theorem kap_algebraMap (r : R) : kap I (algebraMap R _ r) = algebraMap (R ⧸ I) (DualNumber (R ⧸ I)) (Ideal.Quotient.mk I r) := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap, TrivSqZeroExt.algebraMap_eq_inl']

theorem kap_map (a : DualNumber R) : kap I (TrivSqZeroExt.map (Ideal.Quotient.mkₐ R I).toLinearMap a) =
    dualMap (Ideal.Quotient.mk I) a := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap, dualMap]
end Red

section Rel

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]
  {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

abbrev ev1 (Γ : QFGroup R T) : Γ.btOrder ⊤ →ₐ[R] R := evalAt (Γ.btOrder ⊤) 1

def TanRel (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} {x : Spec (CommRingCat.of R) ⟶ S} (i : Γ.G.left ⟶ G.left)
    (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))) (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) (v : ob x V ⟶ G) : Prop :=
  ∃ y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left,
    y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) ∧
    y ≫ j = Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) ∧
    y ≫ i = v.left

end Rel

end GlobalTheory.CompanionTheory.Ar.BT.Tan
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZarhinBundleKernelFirstCoordEquations
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar

namespace ProjCoord

section OpenImm

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]

def push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) : Cpt (η ≫ f) :=
  ⟨f p.1, p.2.map f.continuous⟩

theorem genMap_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) :
    genMap (η ≫ f) (push η f p) = (genMap η p).comp (f.stalkMap p.1).hom := by
  have h1 := Scheme.stalkClosedPointTo_comp η f
  have h2 := Scheme.Hom.stalkSpecializes_stalkMap f _ _ p.2
  have h3 : X.presheaf.stalkSpecializes (push η f p).2 ≫ Scheme.stalkClosedPointTo (η ≫ f) =
      f.stalkMap p.1 ≫ (Y.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo η) :=
    (congrArg (X.presheaf.stalkSpecializes (push η f p).2 ≫ ·) h1).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Scheme.stalkClosedPointTo η) h2).trans
        (Category.assoc _ _ _)))
  exact congrArg (fun g => g.hom) h3

theorem regAt_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f] (p : Cpt η) :
    regAt (η ≫ f) (push η f p) = regAt η p := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  unfold regAt
  rw [genMap_push]
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := hb.2 s
    exact ⟨t, rfl⟩

theorem genMap_push_injective (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]
    (p : Cpt η) (h : Function.Injective (genMap η p)) :
    Function.Injective (genMap (η ≫ f) (push η f p)) := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  rw [genMap_push]
  exact h.comp hb.1

end OpenImm

section Chart

variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]

end Chart

section Away

open HomogeneousLocalization

variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]

end Away

section Poly

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem aeval_mul_of_isHomogeneous {B : Type} [CommRing B] [Algebra o B] (x : κ → B) (t : B)
    {g : MvPolynomial κ o} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun j => t * x j) g = t ^ n * aeval x g := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h : ∑ i ∈ d.support, d i = n := by
    have := hg (mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

end Poly

end ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtCompLocalHom
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtCompLocalHom
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeRing

variable {X : Scheme.{0}} {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']

theorem centre_specializes (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) ⤳ centre z := by
  have h := (IsLocalRing.specializes_closedPoint
    (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint R'))).map z.continuous
  exact h


set_option backward.isDefEq.respectTransparency false in
theorem stalkSpecializes_stalkClosedPointTo (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalkSpecializes (centre_specializes ψ z) ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ) ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (Spec.map (CommRingCat.ofHom ψ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

theorem valAt_change : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (R R' : Type)
    [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ψ : R →+* R')
    (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R), ValAt ξ z a r →
    genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) →
    ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  intro X Ω _ ξ R R' _ _ _ _ ψ z a r h h'
  obtain ⟨h1, s, rfl, rfl⟩ := h
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalkSpecializes_stalkClosedPointTo ψ z)

end GlobalTheory.CompanionTheory.Ar.ChangeRing
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtCompLocalHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valAt_comp_local_hom : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R), ValAt ξ z a r → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) → ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change | exact GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change | (intros; apply GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHom
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHom
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.Funct

theorem valAt_pullback {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (a : X ⟶ Y)
    (y : Spec (CommRingCat.of B) ⟶ Y) (hy : x ≫ a = y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (h' : ⊤ ≤ x ⁻¹ᵁ (a ⁻¹ᵁ U)) (s : Γ(Y, U)) :
    valAt x (a ⁻¹ᵁ U) h' ((a.app U).hom s) = valAt y U h s := by
  subst hy
  simp only [valAt]
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem regularAt_pullback {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ₁ : QFGroup R T)
    {T' : Type} [CommGroup T'] (Γ₂ : QFGroup R T') (a : Γ₁.G ⟶ Γ₂.G) (α : T →* T')
    (ha : ∀ t, Γ₁.pt t ≫ a = Γ₂.pt (α t)) (φ : T' → FractionRing R) (g : Γ₁.G.left)
    (hg : Γ₂.RegularAt φ (a.left g)) : Γ₁.RegularAt (fun t => φ (α t)) g := by
  obtain ⟨U, hU, s, hs⟩ := hg
  refine ⟨a.left ⁻¹ᵁ U, hU, (a.left.app U).hom s, fun t h => ?_⟩
  have hy : (Γ₁.pt t).left ≫ a.left = (Γ₂.pt (α t)).left := by
    rw [← ha t, Over.comp_left]
  have h₂ : ⊤ ≤ (Γ₂.pt (α t)).left ⁻¹ᵁ U := by
    rw [← hy]
    exact h
  rw [valAt_pullback _ _ _ hy U h₂ h s]
  exact hs (α t) h₂

theorem comp_mem_btOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (T' : Type) [CommGroup T'] [Finite T'] (Γ' : QFGroup R T') (a : Γ.G ⟶ Γ'.G) (α : T →* T'), (∀ t, Γ.pt t ≫ a = Γ'.pt (α t)) → ∀ f ∈ Γ'.btOrder ⊤, (fun t => f (α t)) ∈ Γ.btOrder ⊤ := by
  intro R _ _ T _ _ Γ T' _ _ Γ' a α ha f hf
  let Φ : (T' → R) →ₐ[R] (T → R) :=
    { toFun := fun f t => f (α t)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hle : Γ'.btOrder ⊤ ≤ (Γ.btOrder ⊤).comap Φ := by
    refine Algebra.adjoin_le fun f hf => ?_
    refine Algebra.subset_adjoin fun t g _ => ?_
    have h := regularAt_pullback Γ Γ' a α ha _ g (hf (α t) (a.left g) trivial)
    change Γ.RegularAt (fun x => algebraMap R (FractionRing R) (f (α (t * x)))) g
    simpa only [map_mul] using h
  exact hle hf

end GlobalTheory.CompanionTheory.Ar.BT.Funct
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHomStatement
alias GlobalTheory.T.btOrder_comap_hom := GlobalTheory.CompanionTheory.Ar.BT.Funct.comp_mem_btOrder
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHom
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem comp_hom_apply_pointOfLocal {a b c d : CommRingCat.{0}} (A : a ⟶ b) (B : b ⟶ c) (D : a ⟶ c) (T : c ⟶ d)
    (e : A ≫ B = D) (s : a) : (B ≫ T).hom (A.hom s) = (D ≫ T).hom s := by
  subst e
  simp

theorem genMap_apply_of_specializes_pointOfLocal {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p q : Cpt ξ) (h : p.1 ⤳ q.1) (s : X.presheaf.stalk q.1) :
    genMap ξ p ((X.presheaf.stalkSpecializes h).hom s) = genMap ξ q s := by
  have e : X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes p.2 =
      X.presheaf.stalkSpecializes q.2 := TopCat.Presheaf.stalkSpecializes_comp _ _ _
  unfold genMap
  exact comp_hom_apply_pointOfLocal _ _ _ _ e s

theorem exists_unique_point_of_local (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (R : Type) [CommRing R] [IsLocalRing R] (φ : regAt ξ p →+* R)
    (hφ : IsLocalHom φ) :
    ∃! z : Spec (CommRingCat.of R) ⟶ X, centre z = p.1 ∧ ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a) := by
  let e : X.presheaf.stalk p.1 →+* regAt ξ p := (genMap ξ p).rangeRestrict
  have he : ∀ s, ((e s : regAt ξ p) : Ω) = genMap ξ p s := fun s => rfl
  have einj : Function.Injective e := fun s t h => hξ.inj p (by rw [← he, ← he, h])
  have esurj : Function.Surjective e := (genMap ξ p).rangeRestrict_surjective
  let ψ : X.presheaf.stalk p.1 ⟶ CommRingCat.of R := CommRingCat.ofHom (φ.comp e)
  have hψ : ∀ s, ψ.hom s = φ (e s) := fun s => rfl
  have hloc : IsLocalHom ψ.hom := by
    refine ⟨fun s hs => ?_⟩
    have h1 : IsUnit (e s) := hφ.map_nonunit _ (by rwa [hψ] at hs)
    obtain ⟨b, hb⟩ := h1.exists_right_inv
    obtain ⟨t, rfl⟩ := esurj b
    have : s * t = 1 := einj (by rw [map_mul, hb, map_one])
    exact IsUnit.of_mul_eq_one t this
  let w : Σ x, { f : X.presheaf.stalk x ⟶ CommRingCat.of R // IsLocalHom f.hom } := ⟨p.1, ψ, hloc⟩
  let E := SpecToEquivOfLocalRing X (CommRingCat.of R)
  have key : ∀ y : Spec (CommRingCat.of R) ⟶ X, ∀ hc : centre y = p.1,
      (∀ s : X.presheaf.stalk (centre y),
        (Scheme.stalkClosedPointTo y).hom s =
          ψ.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom s)) → y = E.symm w := by
    intro y hc h
    rw [Equiv.eq_symm_apply]
    refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨hc, ?_⟩
    ext s
    exact h s
  refine ⟨E.symm w, ?_, ?_⟩
  · have hs := E.apply_symm_apply w
    obtain ⟨hc, hT⟩ := SpecToEquivOfLocalRing_eq_iff.mp hs
    have hc' : centre (E.symm w) = p.1 := hc
    refine ⟨hc', fun a => ?_⟩
    obtain ⟨s, hsa⟩ := a.2
    have hsa' : e s = a := Subtype.ext hsa
    have hg : genPt ξ ⤳ centre (E.symm w) := hc'.symm ▸ p.2
    refine ⟨hg, (X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s, ?_, ?_⟩
    · exact (genMap_apply_of_specializes_pointOfLocal ξ ⟨_, hg⟩ p (specializes_of_eq hc') s).trans hsa
    · have h1 := congrArg (fun f => f.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s)) hT
      have h1' : (Scheme.stalkClosedPointTo (E.symm w)).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s) =
          ψ.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom
            ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s)) := h1
      have h2 : (X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s) = s := by
        have h3 : X.presheaf.stalkSpecializes (specializes_of_eq hc') ≫
            X.presheaf.stalkSpecializes (specializes_of_eq hc.symm) = 𝟙 _ := by
          rw [TopCat.Presheaf.stalkSpecializes_comp]
          exact TopCat.Presheaf.stalkSpecializes_refl _ _
        have h4 := congrArg (fun f => f.hom s) h3
        exact h4
      rw [h2, hψ, hsa'] at h1'
      exact h1'
  · rintro y ⟨hc, hv⟩
    refine key y hc fun s => ?_
    obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom s := ⟨_, rfl⟩
    obtain ⟨hg, s1, hs1, hr⟩ := hv (e s0)
    have h1 : s1 = s := by
      apply hξ.inj ⟨_, hg⟩
      rw [hs1, he, hs0]
      exact genMap_apply_of_specializes_pointOfLocal ξ p ⟨_, hg⟩ (specializes_of_eq hc.symm) s
    rw [← hs0, hψ, ← hr, h1]

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_centre_local_hom : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (R : Type) [CommRing R] [IsLocalRing R] (φ : regAt ξ p →+* R), IsLocalHom φ → ∃! z : Spec (CommRingCat.of R) ⟶ X, centre z = p.1 ∧ ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local | exact GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitNatCastStalk
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem isUnit_natCast_stalk (X : Scheme.{0}) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ X) (n : ℕ) (hn : n ≠ 0) :
    IsUnit ((n : X.presheaf.stalk (centre z))) := by
  set x := IsLocalRing.closedPoint L
  have hL : IsUnit (n : L) := (Nat.cast_ne_zero.mpr hn).isUnit
  let φ : L →+* (Sp L).presheaf.stalk x :=
    ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (Sp L).presheaf.germ ⊤ x trivial).hom
  have h2 : IsUnit (n : (Sp L).presheaf.stalk x) := by
    simpa using hL.map φ
  have h3 : IsUnit ((z.stalkMap x).hom (n : X.presheaf.stalk (z x))) := by
    simpa using h2
  haveI : IsLocalHom (z.stalkMap x).hom := z.prop x
  exact (isUnit_map_iff (z.stalkMap x).hom _).mp h3

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToToStalk
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory CptModel

namespace CoordInhab

variable {o K : Type} [CommRing o] [Field K] [Algebra o K]

theorem inv_mem_of_span_eq_top {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (S : Subring K) (h1 : ∀ a : o, algebraMap o K a ∈ S)
    (h2 : ∀ j, algebraMap o K (x j) / algebraMap o K (x c) ∈ S) : (algebraMap o K (x c))⁻¹ ∈ S := by
  have h1mem : (1 : o) ∈ Submodule.span o (Set.range x) := by
    have h : (1 : o) ∈ Ideal.span (Set.range x) := by
      rw [hx]
      exact Submodule.mem_top
    exact h
  have key : ∀ y ∈ Submodule.span o (Set.range x),
      algebraMap o K y / algebraMap o K (x c) ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact h2 j
    | zero =>
      rw [map_zero, zero_div]
      exact S.zero_mem
    | add y z _ _ hy hz =>
      rw [map_add (f := _), add_div]
      exact S.add_mem hy hz
    | smul r y _ hy =>
      rw [smul_eq_mul, map_mul, mul_div_assoc]
      exact S.mul_mem (h1 r) hy
  have h := key 1 h1mem
  rwa [map_one, one_div] at h

theorem algebraMap_mem_regAt (p : Cpt (pt (algebraMap o K))) (a : o) :
    algebraMap o K a ∈ regAt (pt (algebraMap o K)) p :=
  RingHom.mem_range.2 ⟨tS p.1 a, genMap_toStalk _ p a⟩

variable [IsFractionRing o K]

theorem inChart_iff {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (p : Cpt (pt (algebraMap o K))) :
    InChart (pt (algebraMap o K)) (fun j => algebraMap o K (x j)) c p ↔ x c ∉ p.1.asIdeal := by
  have hinj := IsFractionRing.injective o K
  constructor
  · rintro ⟨hne, hrat⟩ hmem
    have hne' : algebraMap o K (x c) ≠ 0 := hne
    have hinv : (algebraMap o K (x c))⁻¹ ∈ regAt (pt (algebraMap o K)) p :=
      inv_mem_of_span_eq_top x hx c _ (algebraMap_mem_regAt p) hrat
    obtain ⟨b, s, hs, -, hbs⟩ := (mem_regAt_iff _ p _).1 hinv
    apply hs
    have hsb : algebraMap o K s = algebraMap o K (b * x c) := by
      rw [map_mul, ← hbs, mul_comm ((algebraMap o K (x c))⁻¹) (algebraMap o K s), mul_assoc,
        inv_mul_cancel₀ hne', mul_one]
    rw [hinj hsb]
    exact p.1.asIdeal.mul_mem_left b hmem
  · intro hnot
    have hne : algebraMap o K (x c) ≠ 0 := by
      intro h0
      apply hnot
      rw [(map_eq_zero_iff _ hinj).1 h0]
      exact p.1.asIdeal.zero_mem
    exact ⟨hne, fun c' => (mem_regAt_iff _ p _).2 ⟨x c', x c, hnot, hne, div_mul_cancel₀ _ hne⟩⟩

variable {R : Type} [CommRing R] [IsLocalRing R]

end CoordInhab

open CoordInhab

theorem ValAt.unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (hξ : IsCptGen ξ) (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hs, s, hsa, rfl⟩ := h
  obtain ⟨hs', s', hsa', rfl⟩ := h'
  exact congrArg (Scheme.stalkClosedPointTo z).hom (hξ.inj ⟨centre z, hs⟩ (hsa.trans hsa'.symm))

namespace CoordInhab

end CoordInhab

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinitePointExtendsSection
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem spec_gamma_isoSpec_inv (S : CommRingCat.{0}) :
    Spec.map (Scheme.ΓSpecIso S).hom ≫ (Spec S).isoSpec.inv = 𝟙 _ := by
  simp [Scheme.isoSpec_Spec_inv, ← Spec.map_comp]

theorem exists_section_of_isFinite (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsFinite f]
    (p : Spec (CommRingCat.of (FractionRing R)) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ s = p := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of R ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop
  let φ : Γ(X, ⊤) ⟶ CommRingCat.of (FractionRing R) :=
    p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom
  have hφψ : ψ ≫ φ = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    have h1 : f.appTop ≫ p.appTop = (p ≫ f).appTop := by simp
    simp only [ψ, φ, Category.assoc]
    rw [reassoc_of% h1, hp, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  have hfin : ψ.hom.Finite := by
    have h2 : f.appTop.hom.Finite := IsFinite.finite_app f ⊤ (isAffineOpen_top _)
    have h3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
    simpa [ψ] using RingHom.Finite.comp h2 h3
  have hint : ∀ a : Γ(X, ⊤), ∃ y : R, algebraMap R (FractionRing R) y = φ.hom a := by
    intro a
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    obtain ⟨P, hm, hP⟩ := hfin.to_isIntegral a
    refine ⟨P, hm, ?_⟩
    have h4 : φ.hom.comp ψ.hom = algebraMap R (FractionRing R) := by
      rw [← CommRingCat.hom_comp, hφψ]; rfl
    have := Polynomial.hom_eval₂ P ψ.hom φ.hom a
    rw [hP, map_zero, h4] at this
    exact this.symm
  have hinj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  let e : R ≃+* (algebraMap R (FractionRing R)).range :=
    RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let θ₀ : Γ(X, ⊤) →+* R :=
    e.symm.toRingHom.comp (φ.hom.codRestrict (algebraMap R (FractionRing R)).range (fun a => hint a))
  have hθ₀ : ∀ a, algebraMap R (FractionRing R) (θ₀ a) = φ.hom a := by
    intro a
    have h5 : e (θ₀ a) = φ.hom.codRestrict (algebraMap R (FractionRing R)).range (fun a => hint a) a := by
      simp [θ₀]
    exact congrArg Subtype.val h5
  let θ : Γ(X, ⊤) ⟶ CommRingCat.of R := CommRingCat.ofHom θ₀
  have hθφ : θ ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = φ := by
    ext a; exact hθ₀ a
  have hψθ : ψ ≫ θ = 𝟙 _ := by
    ext r
    apply hinj
    have h6 := congrArg (fun g => g.hom r) hφψ
    have h7 := hθ₀ (ψ.hom r)
    exact h7.trans h6
  have hfθ : f.appTop ≫ θ = (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.inv_hom_id, ← hψθ]
    simp [ψ]
  refine ⟨Spec.map θ ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc, hfθ]
    exact spec_gamma_isoSpec_inv _
  · rw [← Spec.map_comp_assoc, hθφ]
    simp only [φ, Spec.map_comp, Category.assoc]
    rw [Scheme.isoSpec_inv_naturality, reassoc_of% spec_gamma_isoSpec_inv]

theorem exists_section_of_generic_point (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens)
    (hU : IsFinite (U.ι ≫ Γ.G.hom)) (t : T) (ht : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) :
    ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, (∀ z, σ.left z ∈ U) ∧
      toUnit (genPt R) ≫ σ = Γ.pt t := by
  have hr : Set.range (Γ.pt t).left ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ht (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  let p := IsOpenImmersion.lift U.ι (Γ.pt t).left hr
  have hpι : p ≫ U.ι = (Γ.pt t).left := IsOpenImmersion.lift_fac _ _ _
  have hp : p ≫ U.ι ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [reassoc_of% hpι]; exact Over.w (Γ.pt t)
  obtain ⟨s, hs, hsp⟩ := exists_section_of_isFinite R (U.ι ≫ Γ.G.hom) p hp
  refine ⟨Over.homMk (s ≫ U.ι) (by simpa using hs), ?_, ?_⟩
  · intro z
    have h8 : U.ι (s z) ∈ Set.range U.ι := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at h8
    simpa using h8
  · apply Over.OverMorphism.ext
    change (genPt R).hom ≫ s ≫ U.ι = (Γ.pt t).left
    rw [← hpι, ← hsp]
    simp

end GlobalTheory.CompanionTheory.Ar.BT
end
