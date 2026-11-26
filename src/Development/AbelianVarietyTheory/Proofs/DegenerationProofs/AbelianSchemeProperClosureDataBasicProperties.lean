module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureWeightSectionToTwistedPolarisationPower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem spMap_factor_jK {V Ω : Type} [CommRing V] [IsDomain V] [Field Ω] (φ : V →+* Ω)
    (hi : Function.Injective φ) : ∃ r, spMap φ = r ≫ Out.jK V := by
  refine ⟨spMap (IsFractionRing.lift (K := FractionRing V) hi), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (IsFractionRing.lift_algebraMap hi x).symm

theorem range_comp_ι_subset {X Y : Scheme.{0}} (U : Y.Opens) (f : X ⟶ U.toScheme) :
    Set.range (f ≫ U.ι) ⊆ U := by
  rintro _ ⟨x, rfl⟩
  exact (f x).2

theorem field_point_factor_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (Ω : Type) [Field Ω] (q : Sp Ω ⟶ Sp V) :
    (∃ r, q = r ≫ spMap (IsLocalRing.residue V)) ∨ ∃ r, q = r ≫ Out.jK V := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  by_cases h : RingHom.ker φ.hom = ⊥
  · exact Or.inr (spMap_factor_jK φ.hom ((RingHom.injective_iff_ker_eq_bot _).2 h))
  · have hp : (RingHom.ker φ.hom).IsPrime := RingHom.ker_isPrime _
    have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal V :=
      IsLocalRing.eq_maximalIdeal (hp.isMaximal h)
    refine Or.inl ⟨spMap (Ideal.Quotient.lift (IsLocalRing.maximalIdeal V) φ.hom
      fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)), ?_⟩
    rw [← Spec.map_comp]
    congr 1

theorem isSemiAbelian_of_fibres_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (H : Over (Sp V)) [GrpObj H] [hc : IsCommMonObj H] (hs : Smooth H.hom) (hsep : IsSeparated H.hom)
    (hq : QuasiCompact H.hom)
    (h₁ : IsSemiAbelian ((Over.pullback (spMap (IsLocalRing.residue V))).obj H))
    (h₂ : IsSemiAbelian ((Over.pullback (Out.jK V)).obj H)) : IsSemiAbelian H := by
  have key : ∀ (Ω : Type) [Field Ω] (q : Sp Ω ⟶ Sp V), ∃ (T : Scheme.{0}) (r : Sp Ω ⟶ T) (f : T ⟶ Sp V),
      q = r ≫ f ∧ IsSemiAbelian ((Over.pullback f).obj H) := by
    intro Ω _ q
    rcases field_point_factor_dvr V Ω q with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨_, r, _, hr, h₁⟩
    · exact ⟨_, r, _, hr, h₂⟩
  refine ⟨hc, hs, hsep, hq, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩,
    fun Ω _ _ q => ?_⟩
  · obtain ⟨T, r, f, rfl, h⟩ := key K q
    have hg : GeometricallyConnected (pullback.snd H.hom f) := h.geomConnected
    rw [← (pullbackLeftPullbackSndIso H.hom f r).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hg.1 K r
  · obtain ⟨T, r, f, rfl, h⟩ := key Ω q
    obtain ⟨E⟩ := h.fibres Ω r
    have : IsMonHom (pullCompIso r f H).symm.hom := inferInstanceAs (IsMonHom (pullCompIso r f H).inv)
    exact ⟨torusExtOfIso (pullCompIso r f H).symm E⟩

namespace Core

variable (C : Core)

theorem isPullback_a : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
  have h : IsPullback C.a (𝟙 _) C.G.ι (C.a ≫ C.G.ι) := IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa using h.paste_vert C.cart

theorem isOpenImmersion_a : IsOpenImmersion C.a :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) C.isPullback_a.flip inferInstance

theorem range_a : Set.range C.a = C.GG.hom ⁻¹' C.U := by
  have h := C.isPullback_a
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    h.isoPullback.hom.surjective.range_comp, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

theorem isNoetherian_Z : IsNoetherian C.Z := by
  have := C.lft
  have := C.qc
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.π
  have : CompactSpace C.Z := QuasiCompact.compactSpace_of_compactSpace C.π
  exact {}

theorem isNoetherian_P : IsNoetherian C.P.left := by
  have := C.isNoetherian_Z
  have := C.proper
  have : IsLocallyNoetherian C.P.left := LocallyOfFiniteType.isLocallyNoetherian C.P.hom
  have : CompactSpace C.P.left := QuasiCompact.compactSpace_of_compactSpace C.P.hom
  exact {}

theorem surjective_GG : Surjective C.GG.hom :=
  ⟨fun z => ⟨C.e z, by
    change (C.e ≫ C.G.ι ≫ C.P.hom) z = z
    rw [C.e_sec]; rfl⟩⟩

theorem nonempty_A : Nonempty C.A.left := by
  obtain ⟨z, hz⟩ := C.ne
  have := C.ab.geomConnected
  exact ⟨(C.A.hom.surjective ⟨z, hz⟩).choose⟩

theorem isIntegral_G : IsIntegral C.G.toScheme := by
  have : Nonempty C.G.toScheme := C.nonempty_A.map C.a
  exact isIntegral_of_isOpenImmersion C.G.ι

theorem flat_P : Flat (C.P.hom ≫ C.π) := by
  have := C.isNoetherian_P
  have := C.isOpenImmersion_a
  have := C.nonempty_A
  have := C.flat
  have := C.ab.smooth
  have : TopologicalSpace.NoetherianSpace C.A.left :=
    (C.a ≫ C.G.ι).isOpenEmbedding.isInducing.noetherianSpace
  have : IsDominant (C.a ≫ C.G.ι) :=
    ⟨(C.a ≫ C.G.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have : IsSchemeTheoreticallyDominant (C.a ≫ C.G.ι) := .of_isDominant _
  have : Flat ((C.a ≫ C.G.ι) ≫ C.P.hom ≫ C.π) := by
    rw [← Category.assoc, C.cart.w]
    infer_instance
  exact flat_of_isSchemeTheoreticallyDominant
    (fun _ _ inst h => (@Module.Flat.flat_iff_torsion_eq_bot_of_isBezout ℤ _ _ _ inst.toModule _ _).mpr h)
    (C.a ≫ C.G.ι) _

variable {C} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)


include τ in
theorem Test.cl : C.Cl y := by
  have hi : Function.Injective ((OO p).subtype.comp τ.j) := (OO p).subtype_injective.comp τ.j_inj
  obtain ⟨r, hr⟩ := spMap_factor_jK _ hi
  have e : gPt p ≫ spMap τ.j = r ≫ Out.jK τ.V := (Spec.map_comp _ _).symm.trans hr
  have e' : gPt p ≫ y = (r ≫ τ.yK) ≫ C.U.ι := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← e, Category.assoc, τ.fac]
  unfold Cl
  rw [e']
  exact range_comp_ι_subset _ _

theorem Test.charZero : CharZero τ.V :=
  RingHom.charZero ((OO p).subtype.comp τ.j)

theorem Test.isSemiAbelian : IsSemiAbelian τ.H := by
  obtain ⟨S, hS⟩ := τ.split
  have := τ.smooth
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue τ.V))).obj τ.H) := Functor.isCommMonObj_obj
  exact isSemiAbelian_of_fibres_dvr τ.V τ.H (SmoothOfRelativeDimension.smooth C.g _) τ.sep τ.qc
    (isSemiAbelian_of_isGt _ S _ hS)
    (isSemiAbelian_of_isAbelianScheme _ (PolPull.isAbelianScheme_of_isGrpPullback C.ab τ.φ_cart))

end Core

theorem core_basic : ∀ C : Core, IsSeparated C.GG.hom ∧ LocallyOfFiniteType C.GG.hom ∧ QuasiCompact C.GG.hom ∧ IsIntegral C.G.toScheme ∧ Flat (C.GG.hom ≫ C.π) ∧ Flat (C.P.hom ≫ C.π) ∧ IsOpenImmersion C.a ∧ IsPullback C.a C.A.hom C.GG.hom C.U.ι ∧ Set.range C.a = C.GG.hom ⁻¹' C.U ∧ IsNoetherian C.Z ∧ IsNoetherian C.P.left ∧ IsDominant C.GG.hom ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.Cl y ∧ CharZero τ.V ∧ IsSemiAbelian τ.H := by
  intro C
  have := C.proper
  have := C.isNoetherian_P
  have := C.flat_P
  have := C.surjective_GG
  have : TopologicalSpace.NoetherianSpace C.G.toScheme := C.G.ι.isOpenEmbedding.isInducing.noetherianSpace
  refine ⟨inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom)),
    inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom)),
    inferInstanceAs (QuasiCompact (C.G.ι ≫ C.P.hom)), C.isIntegral_G, ?_, C.flat_P, C.isOpenImmersion_a,
    C.isPullback_a, C.range_a, C.isNoetherian_Z, C.isNoetherian_P, inferInstance,
    fun p _ y τ => ⟨τ.cl, τ.charZero, τ.isSemiAbelian⟩⟩
  change Flat ((C.G.ι ≫ C.P.hom) ≫ C.π)
  rw [Category.assoc]
  infer_instance

end GlobalTheory.ZJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicPropertiesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.abelianSchemeProperClosureData_basic_properties : ∀ C : Core, IsSeparated C.GG.hom ∧ LocallyOfFiniteType C.GG.hom ∧ QuasiCompact C.GG.hom ∧ IsIntegral C.G.toScheme ∧ Flat (C.GG.hom ≫ C.π) ∧ Flat (C.P.hom ≫ C.π) ∧ IsOpenImmersion C.a ∧ IsPullback C.a C.A.hom C.GG.hom C.U.ι ∧ Set.range C.a = C.GG.hom ⁻¹' C.U ∧ IsNoetherian C.Z ∧ IsNoetherian C.P.left ∧ IsDominant C.GG.hom ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.Cl y ∧ CharZero τ.V ∧ IsSemiAbelian τ.H := by
  first | exact @GlobalTheory.ZJ.core_basic | exact GlobalTheory.ZJ.core_basic | (intros; apply GlobalTheory.ZJ.core_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpan
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SpanImm

theorem closure_eq_top_iff {A B J : Type} [CommRing A] [CommRing B] (c : A →+* B) (r : J → B) :
    Subring.closure (Set.range c ∪ Set.range r) = ⊤ ↔
      Function.Surjective (MvPolynomial.eval₂Hom c r) := by
  rw [← RingHom.range_eq_top]
  suffices h : Subring.closure (Set.range c ∪ Set.range r) = (MvPolynomial.eval₂Hom c r).range by
    rw [h]
  refine le_antisymm (Subring.closure_le.2 ?_) ?_
  · rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  · rintro _ ⟨q, rfl⟩
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (Subring.subset_closure (Or.inr ⟨j, rfl⟩))

theorem range_constFn {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) :
    Set.range (constFn p U) = Set.range (p.appLE ⊤ U le_top).hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
  exact hs.range_comp (p.appLE ⊤ U le_top).hom

theorem immBy_iff {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type}
    (s : J → H.Sec) : ImmBy p H s Set.univ ↔ AmpleSpan.EmbedsBy p s := by
  unfold ImmBy AmpleSpan.EmbedsBy
  simp only [Set.mem_univ, iSup_pos, forall_true_left, range_constFn, closure_eq_top_iff]
  rfl

theorem immBy_of_span : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsProper p] (H : LB X), H.IsLB → ∀ (I J : Type) [Fintype I] [Fintype J] (t : I → H.Sec) (s : J → H.Sec), ImmBy p H t Set.univ → (∀ i, ∃ a : J → k, IsLin p s a (t i)) → ImmBy p H s Set.univ) := by
  intro k _ X p _ H _ I J _ _ t s ht hs
  refine (immBy_iff p H s).2 (((immBy_iff p H t).1 ht).of_inSpan fun i => ?_)
  obtain ⟨a, ha⟩ := hs i
  exact ⟨fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (a j), ha⟩

end GlobalTheory.ZH.SpanImm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpanStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersionBySections_of_span : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsProper p] (H : LB X), H.IsLB → ∀ (I J : Type) [Fintype I] [Fintype J] (t : I → H.Sec) (s : J → H.Sec), ImmBy p H t Set.univ → (∀ i, ∃ a : J → k, IsLin p s a (t i)) → ImmBy p H s Set.univ) := by
  first | exact @GlobalTheory.ZH.SpanImm.immBy_of_span | exact GlobalTheory.ZH.SpanImm.immBy_of_span | (intros; apply GlobalTheory.ZH.SpanImm.immBy_of_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateOfSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateOfSection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnitTheta

theorem exists_pull_one {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (θ : LB.Sec L) :
    ∃ th : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval th ρ z J = gs (ρ ≫ f) z _ (θ.f (J (ρ ≫ f))) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => f) j ≤ f ⁻¹ᵁ L.U (j 0) :=
    fun j y hy => Set.mem_iInter.1 hy 0
  let u : ∀ j : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) := fun j =>
    (Y.presheaf.map (homOfLE (le j)).op).hom ((f.app _).hom (θ.f (j 0)))
  have hu : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) j, ρ z ∈ LB.wchart L (fun _ : Fin 1 => f) j →
      gs ρ z _ (u j) = gs (ρ ≫ f) z _ (θ.f (j 0)) := fun Z ρ z j h =>
    (gs_res ρ z _ h _).trans (gs_pull ρ f z _ (le j h) _)
  refine ⟨⟨u, fun j j' => fn_ext fun y hy => ?_⟩, fun Z ρ z J hJ => hu Z ρ z _ (hJ.mem (fun _ : Fin 1 => f) ρ)⟩
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val
      (gm_linComb L (fun _ : Fin 1 => f) (fun _ => 1) (𝟙 Y) y j j' hy.1 hy.2))) (gs_res (𝟙 Y) y _ hy _))).symm)
  rw [Fin.prod_univ_one, zpow_one]
  exact (hu _ (𝟙 Y) y j hy.1).trans ((gs_compat θ (𝟙 Y ≫ f) y (le j hy.1) (le j' hy.2)).trans
    (congrArg (_ * ·) (hu _ (𝟙 Y) y j' hy.2).symm))

theorem exists_good_point_of_sec : PolBaseChangeSt → GoodPtSt → ∀ (S : Scheme.{0}) (P : PolAV S) (θ : LB.Sec P.L) (κ : Type) [Field κ] [IsAlgClosed κ] (r : Sp κ ⟶ S) (n : ℕ), 2 ≤ n → (n : κ) ≠ 0 → (∃ z ∈ nonzeroLocus θ, P.A.hom z ∈ Set.range r) → ∀ b : Over.mk r ⟶ P.A, ∃ x : Over.mk r ⟶ P.A, x ^ n = 1 ∧ ⊤ ≤ (b * x).left ⁻¹ᵁ nonzeroLocus θ := by
  intro hB hG S P θ κ _ _ r n hn hκ ⟨z, hz, p, hp⟩ b
  obtain ⟨th, hth⟩ := exists_pull_one P.L (snd (Over.mk r) P.A).left θ
  have hne : SecM.ofSec P.A (a := 1) (T := Over.mk r) th ≠ 0 := fun e => by
    obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback r P.A.hom) p z hp
    let y' : (Over.mk r ⊗ P.A).left := y
    obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB y' (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
    have h₁ : (𝟙 _ ≫ (snd (Over.mk r) P.A).left) y' ∈ nonzeroLocus θ := by
      rw [Category.id_comp]; exact hy ▸ hz
    have h₂ := (AmpleSpan.mem_nonzeroLocus_iff_gs θ _ y' (hJ _)).1 h₁
    rw [← hth _ _ y' J hJ] at h₂
    have h₃ : th.f (fun _ => J (𝟙 _ ≫ (snd (Over.mk r) P.A).left)) = 0 :=
      congrArg (fun s : SecM P.A P.L 1 (Over.mk r) => s.1 _) e
    rw [sval, h₃] at h₂
    exact not_isUnit_zero ((congrArg IsUnit (GlobalTheory.UT.ExactTerm.gs_zero' _ _ _ (hJ.mem (fun _ : Fin 1 => (snd (Over.mk r) P.A).left) (𝟙 _)))).mp h₂)
  obtain ⟨x, hx, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hG hB P r hn hκ th hne b
  refine ⟨x, hx, fun q _ => ?_⟩
  obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
  have h₁ : IsUnit (sval th (ptSecT P.A (b * x)).left q J) := hu q J hJ
  have e : (ptSecT P.A (b * x)).left ≫ (snd (Over.mk r) P.A).left = (b * x).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  rw [hth _ _ q J hJ, e] at h₁
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs θ _ q (hJ _)).2 h₁

end GlobalTheory.UnitTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateOfSectionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_torsion_translate_of_section : PolBaseChangeSt → GoodPtSt → ∀ (S : Scheme.{0}) (P : PolAV S) (θ : LB.Sec P.L) (κ : Type) [Field κ] [IsAlgClosed κ] (r : Sp κ ⟶ S) (n : ℕ), 2 ≤ n → (n : κ) ≠ 0 → (∃ z ∈ nonzeroLocus θ, P.A.hom z ∈ Set.range r) → ∀ b : Over.mk r ⟶ P.A, ∃ x : Over.mk r ⟶ P.A, x ^ n = 1 ∧ ⊤ ≤ (b * x).left ⁻¹ᵁ nonzeroLocus θ := by
  first | exact @GlobalTheory.UnitTheta.exists_good_point_of_sec | exact GlobalTheory.UnitTheta.exists_good_point_of_sec | (intros; apply GlobalTheory.UnitTheta.exists_good_point_of_sec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionOfBaseProductSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionOfBaseProductSection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem le_preimage_wchart_of_section {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (k : L.ι) : L.U k ≤ σ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => k) := by
  intro x hx
  refine Set.mem_iInter.2 fun _ => ?_
  change (σ ≫ π) x ∈ L.U k
  rw [h]
  exact hx

noncomputable def secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) : LB.Sec L where
  f k := (X.presheaf.map (homOfLE (le_preimage_wchart_of_section L π σ h k)).op).hom
    ((σ.app _).hom (s.f (fun _ => k)))
  compat i j := fn_ext fun x hx => by
    have li := le_preimage_wchart_of_section L π σ h i hx.1
    have lj := le_preimage_wchart_of_section L π σ h j hx.2
    rw [gs_res _ x inf_le_left hx, gs_mul _ x _ hx, gs_res _ x inf_le_right hx, gs_res _ x _ hx.1, gs_res _ x _ hx.2,
      gs_unit _ x _ hx]
    refine (gs_pull (𝟙 X) σ x _ li _).trans ((sec_trans s (𝟙 X ≫ σ) x li lj).trans
      (congrArg₂ (· * ·) ?_ (gs_pull (𝟙 X) σ x _ lj _).symm))
    simp only [trF, Fin.prod_univ_one, zpow_one, Category.assoc, h, Category.comp_id]

theorem gs_secOfSection {X Y Z : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) (r : Z ⟶ X) (z : Z) (k : L.ι)
    (hz : r z ∈ L.U k) : gs r z _ ((secOfSection L π σ h s).f k) =
      gs (r ≫ σ) z (LB.wchart L (fun _ : Fin 1 => π) (fun _ => k)) (s.f (fun _ => k)) :=
  (gs_res r z _ hz _).trans (gs_pull r σ z _ (le_preimage_wchart_of_section L π σ h k hz) _)

theorem valR_secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) {F : Type} [CommRing F] (r : Sp F ⟶ X)
    (k : L.ι) (hr : ⊤ ≤ r ⁻¹ᵁ L.U k) : valR r _ ((secOfSection L π σ h s).f k) =
      valR (r ≫ σ) (LB.wchart L (fun _ : Fin 1 => π) (fun _ => k)) (s.f (fun _ => k)) :=
  (HolHom.valR_res r _ _ hr).trans (HolHom.valR_comp r σ _ _).symm

theorem mem_nonzeroLocus_secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (h' : π ≫ σ = 𝟙 Y) (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) (y : Y)
    (hy : y ∈ nonzeroLocus s) : π y ∈ nonzeroLocus (secOfSection L π σ h s) := by
  obtain ⟨j, hj⟩ := AmpleSpan.exists_chart_of_mem s hy
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j (0 : Fin 1), funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hk : π y ∈ L.U k := Set.mem_iInter.1 hj 0
  rw [AmpleSpan.mem_nonzeroLocus_iff_gs _ π y hk, gs_secOfSection L π σ h s π y k hk, h']
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs s (𝟙 Y) y hj).1 hy

theorem exists_sec_of_baseOver : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), ∃ θ : LB.Sec P.L, (∀ y ∈ nonzeroLocus th, (snd (baseOver (Sp R)) P.A).left y ∈ nonzeroLocus θ) ∧ ∀ (z : baseOver (Sp R) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp R)).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (a : R), IsValueAt P.A P.L 1 th z τ (fn a) → ∀ (F : Type) [CommRing F] (f : R →+* F) (k : P.L.ι), ⊤ ≤ (spMap f ≫ z.left) ⁻¹ᵁ P.L.U k → valR (spMap f ≫ z.left) _ (θ.f k) = f a * valR (X := (baseOver (Sp R)).left) (spMap f) _ (τ.s (fun _ => k)).val := by
  intro R _ P th
  let σ : P.A ⟶ baseOver (Sp R) ⊗ P.A := lift (toUnit P.A) (𝟙 P.A)
  have h : σ ≫ snd _ _ = 𝟙 _ := lift_snd _ _
  have h' : snd _ _ ≫ σ = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, h, Category.comp_id, Category.id_comp]
  have hl : σ.left ≫ (snd (baseOver (Sp R)) P.A).left = 𝟙 _ := by rw [← Over.comp_left, h, Over.id_left]
  have hl' : (snd (baseOver (Sp R)) P.A).left ≫ σ.left = 𝟙 _ := by rw [← Over.comp_left, h', Over.id_left]
  refine ⟨secOfSection P.L _ σ.left hl th, mem_nonzeroLocus_secOfSection P.L _ σ.left hl hl' th, ?_⟩
  intro z τ a hv F _ f k hk
  have e : z ≫ σ = ptSecT P.A z := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, h, Category.comp_id, ptSecT, lift_snd]
  have e' : z.left ≫ σ.left = (ptSecT P.A z).left := by rw [← Over.comp_left, e]
  let x : Sp F ⟶ (baseOver (Sp R)).left := spMap f
  have hw : ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => z.left) (fun _ => k) :=
    fun p hp => Set.mem_iInter.2 fun _ => hk hp
  have H := congrArg (valR x _) (hv (fun _ => k))
  have H₁ := (HolHom.valR_comp x (ptSecT P.A z).left _ _).trans ((HolHom.valR_res x _ _ hw).symm.trans H)
  have H₂ := H₁.trans (((HolHom.valR_eq x _ hw _).trans (map_mul _ _ _)).trans (congrArg₂ (· * ·)
    ((HolHom.valR_eq x _ hw _).symm.trans ((HolHom.valR_res x _ _ hw).trans (Conv.valR_spMap_top f a)))
    (HolHom.valR_eq x _ hw _).symm))
  refine (valR_secOfSection P.L _ σ.left hl th (x ≫ z.left) k hk).trans ?_
  rw [Category.assoc, e']
  exact H₂

end GlobalTheory.UnitTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionOfBaseProductSectionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_section_of_baseProduct_section : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), ∃ θ : LB.Sec P.L, (∀ y ∈ nonzeroLocus th, (snd (baseOver (Sp R)) P.A).left y ∈ nonzeroLocus θ) ∧ ∀ (z : baseOver (Sp R) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp R)).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (a : R), IsValueAt P.A P.L 1 th z τ (fn a) → ∀ (F : Type) [CommRing F] (f : R →+* F) (k : P.L.ι), ⊤ ≤ (spMap f ≫ z.left) ⁻¹ᵁ P.L.U k → valR (spMap f ≫ z.left) _ (θ.f k) = f a * valR (X := (baseOver (Sp R)).left) (spMap f) _ (τ.s (fun _ => k)).val := by
  first | exact @GlobalTheory.UnitTheta.exists_sec_of_baseOver | exact GlobalTheory.UnitTheta.exists_sec_of_baseOver | (intros; apply GlobalTheory.UnitTheta.exists_sec_of_baseOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionAbelianPartBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionAbelianPartBundle
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.VeryAmpleMove

variable {k : Type} [CommRing k] {X Y : Scheme.{0}}

theorem immBy_pull {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (ψ : Y ⟶ X) [IsIso ψ] (hq : ψ ≫ p = q) {L : LB X} {M : LB Y}
    (hL : L.IsLB) (hM : M.IsLB) (H : LBIso M (L.pull ψ)) {J : Type} (s : J → L.Sec) (J₀ : Set J)
    (hs : ImmBy p L s J₀) : ∃ t : J → M.Sec, ImmBy q M t J₀ := by
  obtain ⟨W, hW⟩ := H
  obtain ⟨hcov, hs⟩ := hs
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hL hM (s i)
  have loc : ∀ i, Out.nonzeroLocus (s' i) = ψ ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hL (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hM y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨s', ?_, fun i hi => ?_⟩
  · simp only [loc]
    rw [← Scheme.Hom.preimage_top ψ, ← hcov]
    simp only [Scheme.Hom.preimage_iSup]
  obtain ⟨haff, r, hr, hsurj⟩ := hs i hi
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hL (ψ y)
    have hm : ψ y ∈ Out.nonzeroLocus (s i) ⊓ L.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · have hsur := VeryAmpleCharts.appLE_surjective (ψ := ψ) _ _ (loc i)
    have hc : ∀ a, (ψ.appLE _ _ (loc i).le).hom (constFn p (Out.nonzeroLocus (s i)) a) =
        constFn q (Out.nonzeroLocus (s' i)) a := fun a => by
      subst hq
      unfold constFn
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
      erw [Scheme.Hom.appLE_comp_appLE]
    have e := congrArg (Subring.map (ψ.appLE _ _ (loc i).le).hom) hsurj
    rw [RingHom.map_closure, ← RingHom.range_eq_map, RingHom.range_eq_top.2 hsur, Set.image_union,
      ← Set.range_comp, ← Set.range_comp] at e
    rw [← e]
    congr 2
    exact congrArg Set.range (funext fun a => (hc a).symm)

theorem immBy_lbPow (hA : Out.AmpleSt) (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ)
    (hN : 4 ≤ N) : ∃ (m : ℕ) (s : Fin m → (lbPow P.L N).Sec), ImmBy P.A.hom (lbPow P.L N) s Set.univ := by
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow hA K P N hN
  refine ⟨m + 1, s, by simpa using hcov, fun i _ => ?_⟩
  obtain ⟨haff, r, hr, hf⟩ := hs i
  refine ⟨haff, r, hr, top_le_iff.1 fun f _ => ?_⟩
  obtain ⟨F, rfl⟩ := hf f
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C]
    exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  | add F G hF hG =>
    rw [MvPolynomial.eval₂_add]
    exact add_mem (hF trivial) (hG trivial)
  | mul_X F j hF =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact mul_mem (hF trivial) (Subring.subset_closure (Or.inr ⟨j, rfl⟩))

theorem exists_immBy_abelianPart : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∃ (m : ℕ) (t : Fin m → Φ.N₀.Sec), ImmBy Φ.E.B.hom Φ.N₀ t Set.univ) := by
  intro hL _ k _ _ Φ N hN P
  obtain ⟨m, s, hs⟩ := immBy_lbPow hL.ample k P.PB N hN
  have : IsIso P.β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map P.β.hom))
  obtain ⟨t, ht⟩ := immBy_pull P.β.hom.left (Over.w P.β.hom) (DVR.linComb_isLB _ P.PB.isLB _ _) Φ.isLB P.w₀ s _ hs
  exact ⟨m, t, ht⟩

end GlobalTheory.VeryAmpleMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionAbelianPartBundleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedImmersion_abelianPart_bundle : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∃ (m : ℕ) (t : Fin m → Φ.N₀.Sec), ImmBy Φ.E.B.hom Φ.N₀ t Set.univ) := by
  first | exact @GlobalTheory.VeryAmpleMove.exists_immBy_abelianPart | exact GlobalTheory.VeryAmpleMove.exists_immBy_abelianPart | (intros; apply GlobalTheory.VeryAmpleMove.exists_immBy_abelianPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMemNonzeroLocusFibreOfSecBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMemNonzeroLocusFibreOfSecBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFibre

open TwistLoc VVRank

theorem exists_clear_sval {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (M : Submonoid R)
    [IsLocalization M Rm] {X Y Y' : Scheme.{0}} {π : Y ⟶ Spec (CommRingCat.of R)}
    {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
    [CompactSpace Y] [QuasiSeparatedSpace Y] {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) (ε : K → ℤ)
    (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ t ∈ M, ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s (r ≫ h) z J = gc (r ≫ h ≫ π) z t * sval s' r z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  obtain ⟨t, ht, s, hs⟩ := exists_clear_denominator M H hL φ ε s'
  refine ⟨t, ht, s, fun Z r z J hJ => ?_⟩
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact hs Z r z _ (hJ.mem (fun k => h ≫ φ k) r)

theorem exists_mem_nonzeroLocus_fibre : SecBaseChangeAnySt → ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsSecBasis _ (fun _ : Fin 1 => th) → ∀ s : Sp R, ∃ y ∈ nonzeroLocus th, P.A.hom ((snd (baseOver (Sp R)) P.A).left y) = s := by
  intro hS R _ P th hth s
  obtain ⟨V, hV, b, hb⟩ := ThetaReal.exists_univBasis hS P 1 le_rfl s
  have hp : s.asIdeal.IsPrime := s.isPrime
  let Rp := Localization.AtPrime s.asIdeal
  let k := IsLocalRing.ResidueField Rp
  let Tp : Over (Sp R) := Over.mk (spMap (algebraMap R Rp))
  let Tk : Over (Sp R) := Over.mk (spMap (IsLocalRing.residue Rp) ≫ spMap (algebraMap R Rp))
  let hk : Tk ⟶ Tp := Over.homMk (spMap (IsLocalRing.residue Rp)) rfl
  let u : Tp ⟶ baseOver (Sp R) := Over.homMk Tp.hom (Category.comp_id _)
  have hr : Set.range (spMap (algebraMap R Rp)) ⊆ Set.range V.ι := by
    rintro _ ⟨q, rfl⟩
    refine (Scheme.Opens.range_ι V).ge ?_
    refine Specializes.mem_open ?_ V.isOpen hV
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun x hx => ?_
    by_contra hx'
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
      (IsLocalization.map_units Rp (⟨x, hx'⟩ : s.asIdeal.primeCompl)))
  let v : Tp ⟶ overRes (T := baseOver (Sp R)) V := Over.homMk (IsOpenImmersion.lift V.ι _ hr) (by
    show IsOpenImmersion.lift V.ι _ hr ≫ V.ι ≫ 𝟙 _ = spMap (algebraMap R Rp)
    rw [Category.comp_id, IsOpenImmersion.lift_fac])
  let i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  let bp : LB.Sec (LPow P.A P.L 1 Tp) := pullS P.A _ v (SecM.toSec P.A (b i₀))
  have haff : IsAffine Tk.left := inferInstanceAs (IsAffine (Spec _))
  have hnt : Nontrivial Γ(Tk.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.domain_nontrivial
  obtain ⟨c, hc⟩ := hb Tk (hk ≫ v)
  have hne : (SecM.ofSec P.A (pullS P.A 1 hk bp) : SecM P.A P.L 1 Tk) ≠ 0 := fun h0 =>
    c.ne_zero i₀ ((hc i₀).trans ((pullM_comp P.A P.isLB _ hk v _).symm.trans h0))
  have hsm := P.isAb.smooth
  have hpr := P.isAb.proper
  have hred : IsReduced (Tk ⊗ P.A).left :=
    have : IsReduced Tk.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
    have : Smooth (fst Tk P.A).left := inferInstanceAs (Smooth (pullback.fst Tk.hom P.A.hom))
    GlobalTheory.isReduced_of_smooth_of_isReduced (fst Tk P.A).left
  obtain ⟨z, hz⟩ : ∃ z, z ∈ nonzeroLocus (pullS P.A 1 hk bp) := by
    by_contra hn
    exact hne (Subtype.ext (funext fun j => eq_zero_of_basicOpen_eq_bot ((pullS P.A 1 hk bp).f j)
      (eq_bot_iff.2 fun y hy => (hn ⟨y, TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩⟩).elim)))
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : QuasiSeparatedSpace P.A.left := (quasiSeparated_iff_quasiSeparatedSpace P.A.hom).mp inferInstance
  have H : IsPullback (snd Tp P.A).left (fst Tp P.A).left P.A.hom (spMap (algebraMap R Rp)) :=
    (IsPullback.of_hasPullback Tp.hom P.A.hom).flip
  obtain ⟨t, ht, σ, hσ⟩ := exists_clear_sval s.asIdeal.primeCompl H P.isLB (fun _ : Fin 1 => 𝟙 P.A.left)
    (fun _ => (snd Tp P.A).left) (fun _ => Category.comp_id _) (fun _ => 1) bp
  obtain ⟨a, ha, -⟩ := hth (pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) σ
    (snd (baseOver (Sp R)) P.A).left (fun _ => Category.comp_id _))
  choose J hJ using fun χ : (Tk ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ z)
  have hJ' : Good P.L z J := hJ
  let r : (Tk ⊗ P.A).left ⟶ (Tp ⊗ P.A).left := 𝟙 _ ≫ (hk ▷ P.A).left
  let ρ : (Tk ⊗ P.A).left ⟶ (baseOver (Sp R) ⊗ P.A).left := r ≫ (u ▷ P.A).left
  have e₁ : ρ ≫ (snd (baseOver (Sp R)) P.A).left = r ≫ (snd Tp P.A).left := by
    rw [Category.assoc, whisker_snd_left]
  have e₂ : r ≫ (snd Tp P.A).left ≫ P.A.hom = (fst Tk P.A).left ≫ Tk.hom := by
    rw [Category.assoc, Category.id_comp, ← Category.assoc, whisker_snd_left, Over.w, Over.w]
  have hs : ((fst Tk P.A).left ≫ Tk.hom) z = s := by
    show spMap (algebraMap R Rp) (spMap (IsLocalRing.residue Rp) ((fst Tk P.A).left z)) = s
    generalize (fst Tk P.A).left z = w
    obtain rfl : w = (IsLocalRing.closedPoint k : PrimeSpectrum k) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    have : spMap (IsLocalRing.residue Rp) (IsLocalRing.closedPoint k : PrimeSpectrum k) =
        (IsLocalRing.closedPoint Rp : PrimeSpectrum Rp) := IsLocalRing.comap_closedPoint (IsLocalRing.residue Rp)
    rw [this]
    exact PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := s.asIdeal))
  have u₁ : IsUnit (sv P.A bp r z J) := by
    rw [← sv_pullS P.A 1 hk bp (𝟙 _) z hJ']
    exact (AmpleSpan.mem_nonzeroLocus_iff_gs _ (𝟙 _) z (hJ'.mem (fun _ : Fin 1 => (snd Tk P.A).left) _)).1 hz
  have u₂ : IsUnit (gc (r ≫ (snd Tp P.A).left ≫ P.A.hom) z t) := by
    rw [gc, AmpleSpan.isUnit_gs_iff _ z ⊤ trivial, e₂, hs]
    exact (basicOpen_eq_of_affine (R := CommRingCat.of R) t).ge ht
  have u₃ := u₂.mul u₁
  have hm := hJ'.mem (fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) ρ
  have e₃ := IsComb.gs (π := (fst (baseOver (Sp R)) P.A).left) ha ρ z _ hm
  rw [Fin.sum_univ_one] at e₃
  have e₄ := sval_pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) σ
    (snd (baseOver (Sp R)) P.A).left (fun _ => Category.comp_id _) ρ z hJ'
  rw [e₁, hσ _ r z J hJ'] at e₄
  refine ⟨ρ z, (AmpleSpan.mem_nonzeroLocus_iff_gs th ρ z hm).2
    (isUnit_of_mul_isUnit_right ((congrArg IsUnit (e₃.symm.trans e₄)).mpr u₃)), ?_⟩
  show ((ρ ≫ (snd (baseOver (Sp R)) P.A).left) ≫ P.A.hom) z = s
  rw [e₁, Category.assoc, e₂, hs]

end GlobalTheory.ThetaFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMemNonzeroLocusFibreOfSecBasisStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_nonzeroLocus_fibre_of_secBasis : SecBaseChangeAnySt → ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsSecBasis _ (fun _ : Fin 1 => th) → ∀ s : Sp R, ∃ y ∈ nonzeroLocus th, P.A.hom ((snd (baseOver (Sp R)) P.A).left y) = s := by
  first | exact @GlobalTheory.ThetaFibre.exists_mem_nonzeroLocus_fibre | exact GlobalTheory.ThetaFibre.exists_mem_nonzeroLocus_fibre | (intros; apply GlobalTheory.ThetaFibre.exists_mem_nonzeroLocus_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionNeZeroAt
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOfUnitAt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.TwistNoBasePoint

section
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.NoBasePoint

theorem exists_sec_of_unitAt {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {ε : I → ℤ} {y : Y} (h : UnitAt L φ ε y) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), y ∈ nonzeroLocus s := by
  obtain ⟨s, hs⟩ := h
  choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
  exact ⟨s, (mem_nonzeroLocus s y).2 ⟨fun i => J (𝟙 _ ≫ φ i), Good.mem hJ φ (𝟙 _), hs J hJ⟩⟩

theorem unitAt_twist (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K))
    (x : baseOver (Sp K) ⟶ P.A) (p : (baseOver (Sp K)).left) (m : ℕ) (b : baseOver (Sp K) ⟶ P.A) :
    UnitAt P.L ![(translPt P.A b).left, (snd (baseOver (Sp K)) P.A).left] ![1, (m : ℤ) + 1]
      ((ptSecT P.A x).left p) := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := geometricallyIntegral_of_smooth _
  let t : Spec (CommRingCat.of K) ⟶ Sp K := 𝟙 _
  have : IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 : Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L (1 : ℕ) (Over.mk t)) = 1 ^ P.g :=
    hL.globalSectionsRank K P 1 le_rfl
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let y : (Over.mk t ⊗ P.A).left := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    unitAt_transl P.isLB θ k a y (by
      rw [← ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hL.square _ P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  exact main m b

end

theorem exists_sec_twist :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ), 4 ≤ n → ∀ c x : Out.baseOver (Sp k) ⟶ P.A, ∃ s : LB.Sec (Out.twistLB P.A P.L n c), ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s) := by
  intro hL _ k _ _ P n hn c x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let p : (Out.baseOver (Sp k)).left := IsLocalRing.closedPoint k
  have h : H1.SquareUnits.UnitAt P.L (K := Fin 2)
      ![(snd (Out.baseOver (Sp k)) P.A).left, (Out.translPt P.A c).left] ![((m + 2 : ℕ) : ℤ) - 1, 1]
      ((Out.ptSecT P.A x).left p) := by
    refine H1.SquareUnits.UnitAt.congr P.isLB (H1.SquareUnits.formEq_of_add fun U _ hh => ?_) (unitAt_twist hL k P x p m c)
    simp [Fin.sum_univ_succ]
    module
  obtain ⟨s, hs⟩ := exists_sec_of_unitAt P.isLB h
  refine ⟨s, fun q _ => ?_⟩
  obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum k) _ _
  exact hs

end GlobalTheory.TwistNoBasePoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionNeZeroAt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem FibPre.exists_pure_ne_zero_at :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∀ (α : Φ.E.X) (x : Φ.Pt), ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) := by
  intro hL hL2 k _ _ Φ N hN π α x
  obtain ⟨s, hs⟩ := GlobalTheory.TwistNoBasePoint.exists_sec_twist hL hL2 k π.PB (N * 1) (by omega) _
    (x ≫ Φ.D.q ≫ π.β.hom)
  obtain ⟨φ, hφ, h⟩ := (GlobalTheory.T.pureWeightSection_to_twistedPolarisationPower k Φ N 1 π α (by omega) le_rfl).2 s
  exact ⟨φ, hφ, (h x).2 hs⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionNeZeroAtStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pureWeight_section_ne_zero_at : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∀ (α : Φ.E.X) (x : Φ.Pt), ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) := by
  first | exact @GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at | exact GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at | (intros; apply GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at <;> assumption)
end
end
