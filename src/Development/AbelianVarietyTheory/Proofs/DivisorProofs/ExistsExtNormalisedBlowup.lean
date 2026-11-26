module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqSpanMonomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalCompactificationExtensionOfCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtOfMinAt5
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalNormalDomainFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalNormalDomainFiniteExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open scoped Pointwise

namespace GlobalTheory.LocalNormalExt

theorem exists_eq_of_mul_mem_integralClosure
    (R K K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra R K'] [IsScalarTower R K K']
    (P : Ideal (integralClosure R K')) [P.IsMaximal]
    (x : K) (s : integralClosure R K') (hs : s ∉ P)
    (hx : algebraMap K K' x * (s : K') ∈ integralClosure R K') :
    ∃ r : R, algebraMap R K r = x := by
  classical
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R K' L := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R K K', ← IsScalarTower.algebraMap_apply K K' L]; rfl)
  haveI : FiniteDimensional K L := inferInstance
  haveI : IsGalois K L := inferInstance
  haveI : IsScalarTower R R L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure R L
  let C := integralClosure R K'
  haveI : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  let f : C →ₐ[R] S := ((IsScalarTower.toAlgHom R K' L).comp C.val).codRestrict S
    (fun c => (c.2 : IsIntegral R (c : K')).map (IsScalarTower.toAlgHom R K' L))
  have hfv : ∀ c : C, ((f c : S) : L) = algebraMap K' L (c : K') := fun _ => rfl
  have hfinj : Function.Injective f := by
    intro c d h
    have := congrArg (fun u : S => (u : L)) h
    simp only [hfv] at this
    exact Subtype.ext ((algebraMap K' L).injective this)
  letI : Algebra C S := f.toRingHom.toAlgebra
  haveI : IsScalarTower R C S := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.IsIntegral C S := ⟨fun u => (Algebra.IsIntegral.isIntegral (R := R) u).tower_top⟩
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) P
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap C S)).mp hfinj]; exact bot_le)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  let J : Ideal S :=
    { carrier := {u | ∃ v : S, u * algebraMap R S a = algebraMap R S b * v}
      add_mem' := by
        rintro u₁ u₂ ⟨v₁, h₁⟩ ⟨v₂, h₂⟩
        exact ⟨v₁ + v₂, by rw [add_mul, h₁, h₂, mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c u ⟨v, h⟩
        exact ⟨c * v, by rw [smul_eq_mul, _root_.mul_assoc, h, mul_left_comm]⟩ }
  have hJg : ∀ (g : S ≃ₐ[R] S) (u : S), u ∈ J → g u ∈ J := by
    rintro g u ⟨v, h⟩
    exact ⟨g v, by rw [← g.commutes a, ← g.commutes b, ← map_mul, h, map_mul]⟩

  have e1 : ∀ r : R, ((algebraMap R S r : S) : L) = algebraMap K L (algebraMap R K r) :=
    fun _ => rfl
  have hbL : algebraMap K L (algebraMap R K b) ≠ 0 := (map_ne_zero _).mpr hb0
  have htJ : f s ∈ J := by
    refine ⟨f ⟨_, hx⟩, ?_⟩
    apply Subtype.ext
    show (f s : L) * ((algebraMap R S a : S) : L) = ((algebraMap R S b : S) : L) * (f ⟨_, hx⟩ : L)
    rw [hfv, hfv, e1, e1]
    simp only [map_mul]
    rw [← IsScalarTower.algebraMap_apply K K' L, ← hab, map_div₀]
    field_simp
  have hmax : ∀ (I : Ideal S) [I.IsMaximal], I.under R = IsLocalRing.maximalIdeal R :=
    fun I _ => IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) I)
  have hJtop : J = ⊤ := by
    by_contra hne
    obtain ⟨N, hNmax, hJN⟩ := Ideal.exists_le_maximal J hne
    haveI : Finite (S ≃ₐ[R] S) := Finite.of_equiv _ (galRestrict R K L S).toEquiv
    haveI : Algebra.IsInvariant R S (S ≃ₐ[R] S) := Algebra.isInvariant_of_isGalois' R K L S
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := R) (B := S) (G := S ≃ₐ[R] S) Q N
      ((hmax Q).trans (hmax N).symm)
    set_option synthInstance.maxHeartbeats 200000 in
    have h1 : g • f s ∈ g • Q := by
      rw [← hg]; exact hJN (hJg g _ htJ)
    have h2 : f s ∈ Q := (Ideal.smul_mem_pointwise_smul_iff).mp h1
    exact hs (by rw [← hQ]; exact h2)
  obtain ⟨v, hv⟩ : (1 : S) ∈ J := hJtop ▸ Submodule.mem_top
  have hvL : (v : L) = algebraMap K L x := by
    have := congrArg (fun u : S => (u : L)) hv
    simp only [_root_.one_mul, Subalgebra.coe_mul, e1] at this
    rw [← hab, map_div₀, this]
    field_simp
  have hint : IsIntegral R (algebraMap K L x) := hvL ▸ v.2
  have hxint : IsIntegral R x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).mp hint
  exact IsIntegrallyClosed.isIntegral_iff.mp hxint

theorem exists_local_normal_domain_of_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (ρ : R →+* R') (e : FractionRing R' ≃+* K'), IsLocalHom ρ ∧ Function.Injective ρ ∧ (∀ r, e (algebraMap R' _ (ρ r)) = algebraMap (FractionRing R) K' (algebraMap R _ r)) ∧ ∀ (x : FractionRing R) (w : R'), e (algebraMap R' _ w) = algebraMap (FractionRing R) K' x → ∃ r : R, algebraMap R _ r = x := by
  intro R _ _ _ _ _ _ K' _ _ _
  classical
  let K := FractionRing R
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let C := integralClosure R K'
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension K K'
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : IsNoetherianRing C := IsIntegralClosure.isNoetherianRing R K K' C
  haveI : IsDomain C := inferInstance
  obtain ⟨m', hm'⟩ := Ideal.exists_maximal C
  obtain ⟨R', _, _, _⟩ : ∃ (R' : Type) (_ : CommRing R') (_ : Algebra C R'),
      IsLocalization.AtPrime R' m' :=
    ⟨Localization.AtPrime m', inferInstance, inferInstance, inferInstance⟩
  haveI : IsLocalRing R' := IsLocalization.AtPrime.isLocalRing R' m'
  haveI : IsDomain R' :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := m'.primeCompl) (S := R') m'.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing m'.primeCompl R' inferInstance
  haveI : IsIntegrallyClosed R' :=
    isIntegrallyClosed_of_isLocalization R' m'.primeCompl m'.primeCompl_le_nonZeroDivisors
  letI : Algebra R' K' := (IsLocalization.lift (M := m'.primeCompl) (S := R') (g := algebraMap C K')
    (fun y => IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C K')).mpr
      (fun h => y.2 (h ▸ m'.zero_mem))))).toAlgebra
  haveI : IsScalarTower C R' K' :=
    IsScalarTower.of_algebraMap_eq (fun c => (IsLocalization.lift_eq _ c).symm)
  haveI : IsFractionRing R' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m'.primeCompl R' K'
  let e : FractionRing R' ≃+* K' :=
    (FractionRing.algEquiv R' K').toRingEquiv
  have he : ∀ w : R', e (algebraMap R' _ w) = algebraMap R' K' w := fun w =>
    (FractionRing.algEquiv R' K').commutes w
  have hRC : ∀ r : R, algebraMap C K' (algebraMap R C r) = algebraMap K K' (algebraMap R K r) :=
    fun _ => rfl
  have hinjRC : Function.Injective (algebraMap R C) := by
    intro a b h
    have := congrArg (algebraMap C K') h
    rw [hRC, hRC] at this
    exact IsFractionRing.injective R K ((algebraMap K K').injective this)
  have hinjCR' : Function.Injective (algebraMap C R') :=
    IsLocalization.injective R' m'.primeCompl_le_nonZeroDivisors
  have hcomap : m'.comap (algebraMap R C) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) m')
  refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap C R').comp (algebraMap R C), e, ?_, hinjCR'.comp hinjRC, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    by_contra hnu
    have h1 : algebraMap R C r ∈ m' := by
      rw [← Ideal.mem_comap, hcomap]; exact hnu
    have h2 : algebraMap C R' (algebraMap R C r) ∈ IsLocalRing.maximalIdeal R' := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff R' m']; exact h1
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hr
  · intro r
    rw [he]
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply C R' K', hRC]
  · intro x w hw
    rw [he] at hw
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective m'.primeCompl w
    have hmul : algebraMap K K' x * (s : C) = (c : K') := by
      rw [← hw]
      have := congrArg (algebraMap R' K') (IsLocalization.mk'_spec R' c s)
      rw [map_mul, ← IsScalarTower.algebraMap_apply C R' K', ← IsScalarTower.algebraMap_apply C R' K'] at this
      exact this
    exact exists_eq_of_mul_mem_integralClosure R K K' m' x (s : C) s.2 (hmul ▸ c.2)

end GlobalTheory.LocalNormalExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalNormalDomainFiniteExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_normal_domain_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (ρ : R →+* R') (e : FractionRing R' ≃+* K'), IsLocalHom ρ ∧ Function.Injective ρ ∧ (∀ r, e (algebraMap R' _ (ρ r)) = algebraMap (FractionRing R) K' (algebraMap R _ r)) ∧ ∀ (x : FractionRing R) (w : R'), e (algebraMap R' _ w) = algebraMap (FractionRing R) K' x → ∃ r : R, algebraMap R _ r = x := by
  first | exact @GlobalTheory.LocalNormalExt.exists_local_normal_domain_of_finite_extension | exact GlobalTheory.LocalNormalExt.exists_local_normal_domain_of_finite_extension | (intros; apply GlobalTheory.LocalNormalExt.exists_local_normal_domain_of_finite_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionGenericPointFractionMeet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionGenericPointFractionMeet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorDown

theorem ext_of_fraction_meet : ∀ (Z : Scheme.{0}) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (gam : FractionRing R →+* FractionRing R'), (∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x) → ∀ (x : Sp (FractionRing R) ⟶ Z) (a' : Sp R' ⟶ Z), jK R' ≫ a' = spMap gam ≫ x → ∃ a : Sp R ⟶ Z, jK R ≫ a = x := by
  intro Z R R' _ _ _ _ _ gam hgam x a' hx
  obtain ⟨U, hU, hz, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens)
    (show a' (IsLocalRing.closedPoint R') ∈ (⊤ : Z.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hra : Set.range a' ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map a'.continuous).mem_open U.isOpen hz
  have hrx : Set.range x ⊆ Set.range hU'.fromSpec := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t'⟩ : Nonempty (Sp (FractionRing R')) := inferInstance
    have e1 : (spMap gam) t' = t := Subsingleton.elim _ _
    have e2 := congrArg (fun h : Sp (FractionRing R') ⟶ Z => h t') hx
    simp only [Scheme.Hom.comp_apply] at e2
    rw [← e1, ← e2]
    exact hra ⟨_, rfl⟩
  have ha₁ := IsOpenImmersion.lift_fac hU'.fromSpec a' hra
  have hx₁ := IsOpenImmersion.lift_fac hU'.fromSpec x hrx
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec a' hra)] at ha₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)] at hx₁
  set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec a' hra) with hψ
  set χ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hχ
  have key : ψ ≫ CommRingCat.ofHom (algebraMap R' (FractionRing R')) = χ ≫ CommRingCat.ofHom gam := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ha₁, hx₁]
    exact hx
  have hmem : ∀ b : Γ(Z, U), χ.hom b ∈ (algebraMap R (FractionRing R)).range := by
    intro b
    have e := congrArg (fun h => h.hom b) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    obtain ⟨r, hr⟩ := hgam (χ.hom b) (ψ.hom b) e
    exact ⟨r, hr⟩
  have hinj : Function.Injective (algebraMap R (FractionRing R)).rangeRestrict := fun a b h =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)
  let eR := RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
    ⟨hinj, RingHom.rangeRestrict_surjective _⟩
  let θ : Γ(Z, U) →+* R := eR.symm.toRingHom.comp (χ.hom.codRestrict _ hmem)
  have hθ : ∀ b, algebraMap R (FractionRing R) (θ b) = χ.hom b := by
    intro b
    have := eR.apply_symm_apply (χ.hom.codRestrict _ hmem b)
    exact congrArg Subtype.val this
  refine ⟨Spec.map (CommRingCat.ofHom θ : Γ(Z, U) ⟶ CommRingCat.of R) ≫ hU'.fromSpec, ?_⟩
  rw [← hx₁, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext b
  exact hθ b

end GlobalTheory.TorDown
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionGenericPointFractionMeetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_generic_point_fraction_meet : ∀ (Z : Scheme.{0}) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (gam : FractionRing R →+* FractionRing R'), (∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x) → ∀ (x : Sp (FractionRing R) ⟶ Z) (a' : Sp R' ⟶ Z), jK R' ≫ a' = spMap gam ≫ x → ∃ a : Sp R ⟶ Z, jK R ≫ a = x := by
  first | exact @GlobalTheory.TorDown.ext_of_fraction_meet | exact GlobalTheory.TorDown.ext_of_fraction_meet | (intros; apply GlobalTheory.TorDown.ext_of_fraction_meet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointLiftFiniteSurjectiveMorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointLiftFiniteSurjectiveMorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinLift

theorem lift_fieldPoint : ∀ (U X : Scheme.{0}) (c : U ⟶ X) [IsFinite c] [Surjective c] (K : Type) [Field K] (y : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (y' : Sp K' ⟶ U), y' ≫ c = spMap (algebraMap K K') ≫ y := by
  intro U X c _ _ K _ y
  set P := pullback y c
  haveI : IsAffine P := inferInstance
  let f : P ⟶ Sp K := pullback.fst y c
  let A : CommRingCat := Γ(P, ⊤)
  let φ : CommRingCat.of K ⟶ A := Spec.preimage (P.isoSpec.inv ≫ f)
  have hφ : Spec.map φ = P.isoSpec.inv ≫ f := Spec.map_preimage _
  haveI : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hfin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance

  obtain ⟨p, -⟩ := (pullback.fst y c).surjective (IsLocalRing.closedPoint K)
  haveI : Nontrivial A := by
    have q : PrimeSpectrum A := P.isoSpec.hom.base p
    exact q.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A : Type)
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI : Algebra K A := φ.hom.toAlgebra
  haveI : Module.Finite K A := hfin
  haveI : Module.Finite K (A ⧸ m) := Module.Finite.trans A (A ⧸ m)
  refine ⟨A ⧸ m, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ P.isoSpec.inv ≫ pullback.snd y c, ?_⟩
  simp only [Category.assoc]
  rw [← pullback.condition, ← Category.assoc P.isoSpec.inv, ← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.FinLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointLiftFiniteSurjectiveMorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fieldPoint_lift_finite_surjective_morphism : ∀ (U X : Scheme.{0}) (c : U ⟶ X) [IsFinite c] [Surjective c] (K : Type) [Field K] (y : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (y' : Sp K' ⟶ U), y' ≫ c = spMap (algebraMap K K') ≫ y := by
  first | exact @GlobalTheory.FinLift.lift_fieldPoint | exact GlobalTheory.FinLift.lift_fieldPoint | (intros; apply GlobalTheory.FinLift.lift_fieldPoint <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MinExt

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem exists_factor {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : G''.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (n : IsGrpPullback G'' G k ψ) (e : g ≫ f = k) :
    ∃ φ', IsGrpPullback G'' G' g φ' := by
  subst e
  have w : ψ ≫ G.hom = (G''.hom ≫ g) ≫ f := by rw [n.1.w, Category.assoc]
  exact ⟨h.1.lift ψ (G''.hom ≫ g) w, h.cancel (n.congr rfl (h.1.lift_fst _ _ w).symm) (h.1.lift_snd _ _ w)⟩

theorem exists_ext_of_minAt5 : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z), MinAt5 F z i OZ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ F.X) (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left), IsGenFibre F y α₁ → ∀ b : cycAway n →+* R, y ≫ F.s = jK R ≫ spMap b → ∃ a : Sp R ⟶ Z, jK R ≫ a = y ≫ i := by
  intro g n F Z z i OZ h R _ _ _ _ _ _ G₁ _ _ hG₁ y α₁ hα₁ b hyb
  obtain ⟨o', _, β, S', s', U, c, π, G, _, e, _, N, ⟨-, hz, -, hiz, -, hOZ, hamp⟩,
    ⟨-, -, -, -, -, hcfin, hcsurj, hUπ, -, -, hπp, -⟩, ⟨hGsa, hGsm, he⟩, ⟨-, hL⟩⟩ := h
  haveI := hcfin
  haveI := hcsurj
  haveI := hπp
  haveI : IsProper z := by
    obtain ⟨m, j, hj, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  obtain ⟨K', _, _, _, y', hy'⟩ := GlobalTheory.T.exists_fieldPoint_lift_finite_surjective_morphism U.toScheme F.X c (FractionRing R) y
  obtain ⟨R', _, _, _, _, _, ρ, eR, -, hinj, hcomp, hmeet⟩ := GlobalTheory.T.exists_local_normal_domain_finite_extension R K'
  haveI : CharZero R' := charZero_of_injective_ringHom hinj
  let gam : FractionRing R →+* FractionRing R' := (eR.symm : K' →+* FractionRing R').comp (algebraMap (FractionRing R) K')
  have E1 : spMap gam = spMap (eR.symm : K' →+* FractionRing R') ≫ spMap (algebraMap (FractionRing R) K') :=
    spMap_comp_eq _ _
  have E2 : spMap gam ≫ jK R = jK R' ≫ spMap ρ := by
    change spMap gam ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ
    rw [← spMap_comp_eq, ← spMap_comp_eq]
    congr 1
    ext r
    simp only [RingHom.comp_apply, gam]
    rw [← hcomp r]
    simp
  let yy : Sp (FractionRing R') ⟶ S' := spMap (eR.symm : K' →+* FractionRing R') ≫ y' ≫ U.ι
  have E4 : spMap gam ≫ y = (spMap (eR.symm : K' →+* FractionRing R') ≫ y') ≫ c := by
    rw [Category.assoc, hy', E1, Category.assoc]
  have E3 : yy ≫ π = spMap gam ≫ y ≫ i := by
    simp only [yy, Category.assoc]
    rw [hUπ, ← Category.assoc y' c i, hy', E1]
    simp only [Category.assoc]
  let G₁' := (Over.pullback (spMap ρ)).obj G₁
  have hG₁' : IsSemiAbelian G₁' := IsSemiAbelian.pullback (spMap ρ) G₁ hG₁
  haveI : IsCommMonObj G₁' := hG₁'.comm
  have h1 := ((isGrpPullback_pullback G₁' (jK R')).comp (isGrpPullback_pullback G₁ (spMap ρ))).congr E2.symm rfl
  obtain ⟨φ1, hφ1⟩ := exists_factor (isGrpPullback_pullback G₁ (jK R)) h1 rfl
  have h2 := (hφ1.comp hα₁).congr E4 rfl
  obtain ⟨φ2, hφ2⟩ := exists_factor (isGrpPullback_pullback F.univ.A c) h2 rfl
  have h3 := (hφ2.comp he).congr (Category.assoc _ _ _) rfl
  have hyz : yy ≫ π ≫ z = jK R' ≫ spMap (ρ.comp b) := by
    rw [← Category.assoc, E3, Category.assoc, Category.assoc, hiz, hyb, ← Category.assoc, E2, spMap_comp_eq,
      Category.assoc]
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_minimalCompactification_extension_of_cover (cycAway n) g Z S' z π OZ hOZ hamp G N hGsa hGsm hL R' (ρ.comp b) G₁' hG₁' yy _ h3 hyz
  have hmeet' : ∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x :=
    fun x w hw => hmeet x w (by rw [hw]; simp [gam])
  exact GlobalTheory.T.exists_extension_generic_point_fraction_meet Z R R' gam hmeet' (y ≫ i) a' (ha'.trans E3)

end GlobalTheory.MinExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtNormalisedBlowup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem Taut.exists_ext_normBl : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∃ ξ : Sp C.R ⟶ S, y ≫ j = jK C.R ≫ ξ := by
  intro g _ φ hφ _ n hn _ F Z z i OZ d S π j _ BD hM hB C G₁ _ y α₁ hC
  obtain ⟨hsa, hab, hgen, hmum, hy⟩ := hC
  obtain ⟨J, -, -, hval, hbl, -, -, hji, hpre, -, -⟩ := hB
  obtain ⟨hreg, hchar, -, -, hpar, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, hrk, hcone, hdef, ht⟩ := Taut.monomial_chart g n φ (by omega) C
  haveI : IsOpenImmersion i := hM.isThetaCompact.1.2.2.1
  haveI : IsCommMonObj G₁ := hsa.comm
  haveI : IsNoetherianRing C.R := C.compl.1
  haveI : IsIntegrallyClosed C.R := hmum.1.2.1
  obtain ⟨a, ha⟩ := GlobalTheory.MinExt.exists_ext_of_minAt5 g n F Z z i OZ hM C.R G₁ hsa y α₁ hgen C.b hy
  have hon : IsPolFanOn id φ C.Q.X := hφ C.Q.X hrk
  have he : ∀ k, ∃ e : ℕ, (e : ℝ) = d * φ.evalZ ((n : ℤ) • C.δ k) := by
    intro k
    have hmem : (n : ℤ) • C.δ k ∈ balForms (id : ℤ → ℤ) C.Q.X := Submodule.smul_mem _ _ (hcone.mem k)
    have hnn : ∀ w, 0 ≤ ((n : ℤ) • C.δ k) w w := fun w => by
      simpa using mul_nonneg (Int.natCast_nonneg n) (hcone.nonneg k w)
    obtain ⟨c, hc⟩ := hon.integral _ hmem hnn
    have hc0 : 0 ≤ c := by
      have hne : (n : ℤ) • C.δ k ≠ 0 := by
        refine fun h => hcone.basis.linearIndependent.ne_zero k (Subtype.ext ?_)
        exact (smul_eq_zero.1 h).resolve_left (by omega)
      have := hon.pos _ hmem hnn hne
      rw [hc] at this
      exact_mod_cast this.le
    lift c to ℕ using hc0
    exact ⟨d * c, by rw [hc]; push_cast; rfl⟩
  choose e he using he
  have hJ := GlobalTheory.ChartIdeal.idlAlong_eq_span_monomial g n F Z i φ hφ d J hval C.R C.compl.2.1 C.b a C.Q G₁ y α₁ hsa hgen ha
    hmum C.m C.t C.δ e hpar hab hcone hdef hmono he
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.NormBlLift.lift_normBl g n F Z S i π j J hbl hji hpre C.R a y ha _
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)) hJ
  refine ⟨ξ, ?_⟩
  have hπ : (jK C.R ≫ ξ) ≫ π = y ≫ i := by rw [Category.assoc, hξ, ha]
  have hr : Set.range (jK C.R ≫ ξ) ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    rw [← hpre]
    exact ⟨y p, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hπ]⟩
  have hl := IsOpenImmersion.lift_fac j (jK C.R ≫ ξ) hr
  have : IsOpenImmersion.lift j (jK C.R ≫ ξ) hr = y := by
    rw [← cancel_mono i, ← hπ, ← hji, ← Category.assoc, hl]
  rw [← this, hl]

end GlobalTheory.TChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtNormalisedBlowupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ext_normalised_blowup : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∃ ξ : Sp C.R ⟶ S, y ≫ j = jK C.R ≫ ξ := by
  first | exact @GlobalTheory.TChart.Taut.exists_ext_normBl | exact GlobalTheory.TChart.Taut.exists_ext_normBl | (intros; apply GlobalTheory.TChart.Taut.exists_ext_normBl <;> assumption)
end
