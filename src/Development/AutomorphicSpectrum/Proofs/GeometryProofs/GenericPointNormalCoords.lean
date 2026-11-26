module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsInGenericFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeModelBaseChangeSubalgebra
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPf

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsInGenericFibreStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj
namespace GenericFibreProof

theorem spMap_field_pt {R K : Type} [CommRing R] [Field K] (δ : R →+* K) (z : Sp K) :
    (spMap δ z).asIdeal = RingHom.ker δ := by
  have hz : z.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := z.2)
  show Ideal.comap δ z.asIdeal = _
  rw [hz]; rfl

theorem preimm_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) : IsPreimmersion (spMap β) := by
  letI := β.toAlgebra
  haveI := h
  exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)

theorem generic_max {X : Type} [TopologicalSpace X] [T0Space X] {v v' : X} (h : v ∈ genericPoints X)
    (hs : v' ⤳ v) : v' = v := by
  have h1 : closure {v} ⊆ closure {v'} := specializes_iff_closure_subset.1 hs
  have h2 : closure {v'} ⊆ closure {v} := h.2 isIrreducible_singleton.closure h1
  exact (hs.antisymm (specializes_iff_closure_subset.2 h2)).eq

theorem mem_of_dense_of_max {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (ho : IsOpen U) (hd : Dense U) {z : X} (hz : ∀ z', z' ⤳ z → z' = z) : z ∈ U := by
  have hC := irreducibleComponent_mem_irreducibleComponents z
  obtain ⟨o, hoo, ⟨u, hu⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨w, hwo, hwU⟩ := hd.inter_open_nonempty o hoo ⟨u, hu⟩
  have hg := hC.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents _ hC).closure_eq] at hg
  have hgz : hC.1.genericPoint = z := hz _ (hg.specializes mem_irreducibleComponent)
  have hzw : z ⤳ w := hgz ▸ hg.specializes (hoC hwo)
  exact hzw.mem_open ho hwU

private theorem isLocallyNoetherian_of_closedImmersion_pSpace (O F : Type) [CommRing O] [Field F] (β : O →+* F) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (hp : IsProjOver s) : TopologicalSpace.NoetherianSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) := by
  obtain ⟨N, i, hi, hs⟩ := hp
  haveI := hi
  haveI : Algebra.FiniteType ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)
      (MvPolynomial (Fin (N + 1)) O) :=
    haveI : IsScalarTower O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)
        (MvPolynomial (Fin (N + 1)) O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  have hsurj : Function.Surjective
      (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)) := by
    rintro ⟨p, hp⟩
    have h0 : p.totalDegree = 0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := p)).mpr
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0).symm
  haveI : LocallyOfFiniteType (spMap (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0))) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ hsurj
  haveI : LocallyOfFiniteType (PSpace.str O N) := by
    unfold PSpace.str
    infer_instance
  haveI : QuasiCompact (PSpace.str O N) := by
    unfold PSpace.str
    infer_instance
  haveI : LocallyOfFiniteType s := by
    rw [← hs]
    infer_instance
  haveI : QuasiCompact s := by
    rw [← hs]
    infer_instance
  haveI : IsLocallyNoetherian (pullback s (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β))
  haveI : CompactSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (spMap β))
  haveI : IsNoetherian (pullback s (spMap β)) := {}
  infer_instance

theorem generic_points_range_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y hO h v hv
  haveI : IsPreimmersion (spMap β) := preimm_frac β h
  haveI := Y.flat
  haveI := Y.jQ_open
  haveI := isLocallyNoetherian_of_closedImmersion_pSpace O c.F β Y.X Y.s Y.proj
  have hβ : Function.Injective β := by
    letI := β.toAlgebra
    exact IsFractionRing.injective O c.F
  let z0 : Sp c.F := IsLocalRing.closedPoint c.F
  have hgen : (spMap β z0).asIdeal = ⊥ := by
    rw [spMap_field_pt]
    exact (RingHom.injective_iff_ker_eq_bot β).mp hβ
  have hle : (spMap β z0).asIdeal ≤ (Y.s v).asIdeal := by
    rw [hgen]
    exact bot_le
  have hspec : spMap β z0 ⤳ Y.s v := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨v', hv'v, hv'⟩ := Flat.generalizingMap Y.s hspec
  rw [generic_max hv hv'v] at hv'
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback v z0 hv'
  have hqmax : ∀ q', q' ⤳ q → q' = q := by
    intro q' hq'
    apply (pullback.fst Y.s (spMap β)).isEmbedding.injective
    rw [hq]
    exact generic_max hv (hq ▸ hq'.map (pullback.fst Y.s (spMap β)).continuous)
  obtain ⟨w, hw⟩ := mem_of_dense_of_max Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hqmax
  refine ⟨w, ?_⟩
  rw [← hq, ← hw]
  simp [Model.j]

end GenericFibreProof

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_in_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  exact @GenericFibreProof.generic_points_range_local
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FieldPointLiftsGenericFibreStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_point_lifts_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x := by
  exact @PositivityTheory.HtPt.Ml.lift_generic_point
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem genMap_germ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ)
    {U : X.Opens} (hpU : p.1 ∈ U) (heU : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ p ((X.presheaf.germ U p.1 hpU).hom s) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) heU).hom s) := by
  have e : (X.presheaf.stalkSpecializes p.2).hom ((X.presheaf.germ U p.1 hpU).hom s) =
      (X.presheaf.germ U (genPt ξ) heU).hom s :=
    ConcreteCategory.congr_hom (X.presheaf.germ_stalkSpecializes hpU p.2) s
  exact congrArg (fun t : X.presheaf.stalk (genPt ξ) => (Scheme.stalkClosedPointTo ξ).hom t) e

theorem exists_eq_div_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    ∃ u v : X.presheaf.stalk p.1, genMap ξ p v ≠ 0 ∧ a = genMap ξ p u / genMap ξ p v := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have heU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  obtain ⟨g, hg⟩ : ∃ g : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom g = a := hξ.bij.2 a
  letI alg : Algebra Γ(X, U) (X.presheaf.stalk (genPt ξ)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, heU⟩ : U)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk (genPt ξ)) (hU.primeIdealOf ⟨genPt ξ, heU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨genPt ξ, heU⟩
  obtain ⟨⟨f, h⟩, hfh⟩ := IsLocalization.surj (hU.primeIdealOf ⟨genPt ξ, heU⟩).asIdeal.primeCompl g
  have hunit := IsLocalization.map_units (X.presheaf.stalk (genPt ξ)) h
  let ψ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
  have germ_val : ∀ s : Γ(X, U), genMap ξ p ((X.presheaf.germ U p.1 hpU).hom s) =
      (Scheme.stalkClosedPointTo ξ).hom (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) s) :=
    fun s => genMap_germ p hpU heU s
  have hv : (Scheme.stalkClosedPointTo ξ).hom
      (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) (h : Γ(X, U))) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨(X.presheaf.germ U p.1 hpU).hom f, (X.presheaf.germ U p.1 hpU).hom h, ?_, ?_⟩
  · rw [germ_val]
    exact hv
  · rw [germ_val, germ_val, eq_div_iff hv, ← hg]
    exact (map_mul ψ _ _).symm.trans (congrArg ψ hfh)

theorem normalCpt_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : Flat.NormalCpt ξ := by
  intro p a ha
  obtain ⟨hd, hc⟩ := hX p.1
  letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk p.1) Ω) := hξ.inj p
  haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨u, v, -, e⟩ := exists_eq_div_genMap hξ p z
    exact ⟨u, v, e⟩
  letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
    Algebra.IsIntegral.of_surjective (R := X.presheaf.stalk p.1) (A := X.presheaf.stalk p.1)
      (Algebra.ofId _ _) (genMap ξ p).rangeRestrict_surjective
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk p.1) (K := Ω)).1
    (isIntegral_trans (R := X.presheaf.stalk p.1) (A := regAt ξ p) a ha)
  exact ⟨b, hb⟩

theorem exists_cpt_of_genericPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), ∀ e ∈ genericPoints Y.X, ∃ (K : Type) (_ : Field K) (_ : CharZero K) (n : ℕ) (x : Fin n → K) (y : Sp K ⟶ Xo.XF c), CoordTie ℤ (y ≫ Y.j) x ∧ Flat.NormalCpt (y ≫ Y.j) ∧ GlobalTheory.CompanionTheory.Ar.genPt (y ≫ Y.j) = e := by
  intro E _ _ _ H D l Xo c Y e he
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hfrac : (letI := (algebraMap (𝓞 c.F) c.F).toAlgebra; IsFractionRing (𝓞 c.F) c.F) := by
    have : (algebraMap (𝓞 c.F) c.F).toAlgebra = (inferInstance : Algebra (𝓞 c.F) c.F) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [this]
    infer_instance
  have hmax : ∀ y : Y.X, y ⤳ e → y = e := by
    intro y hy
    have h1 : closure {e} = closure {y} :=
      (show Maximal IsIrreducible (closure {e}) from he).eq_of_le isIrreducible_singleton.closure
        (specializes_iff_closure_subset.1 hy)
    exact (inseparable_iff_closure_eq.2 h1.symm).eq
  have hgen : IsCptGen (Ω := Y.X.residueField e) (Y.X.fromSpecResidueField e) :=
    isCptGen_of_maximal Y.X (fun x => (Y.normal x).1) e hmax
  have hj : e ∈ Set.range Y.j :=
    GlobalTheory.T.generic_points_in_generic_fibre E H D l Xo c (𝓞 c.F) _ Y inferInstance hfrac he
  have hr : Set.range (Y.X.fromSpecResidueField e) ⊆ Set.range Y.j := by
    rw [Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.2 hj
  obtain ⟨y, hy⟩ := GlobalTheory.T.field_point_lifts_generic_fibre E H D l Xo c (𝓞 c.F) _ Y hfrac (Y.X.residueField e)
    (Y.X.fromSpecResidueField e) hr
  have hch : CharZero (Y.X.residueField e) := by
    let φ : c.F →+* Y.X.residueField e :=
      (Spec.preimage (y ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))).hom
    exact charZero_of_injective_ringHom φ.injective
  have hover : Y.X.fromSpecResidueField e ≫ Y.s ≫ spMap (Int.castRingHom (𝓞 c.F)) =
      spMap (algebraMap ℤ (Y.X.residueField e)) := by
    rw [← Spec.map_preimage (Y.X.fromSpecResidueField e ≫ Y.s ≫ spMap (Int.castRingHom (𝓞 c.F)))]
    congr 1
    ext1
    exact Subsingleton.elim (α := ℤ →+* Y.X.residueField e) _ _
  obtain ⟨n, x, hx⟩ := GlobalTheory.T.projective_over_coords_exist ℤ Y.X (Y.s ≫ spMap (Int.castRingHom (𝓞 c.F)))
    (GlobalTheory.T.projective_over_restrict_int (𝓞 c.F) Y.X Y.s Y.proj) (Y.X.residueField e) (Y.X.fromSpecResidueField e) hgen hover
  refine ⟨Y.X.residueField e, inferInstance, hch, n, x, y, ?_, ?_, ?_⟩
  · rw [hy]; exact hx
  · rw [hy]; exact normalCpt_of_isCptGen hgen Y.normal
  · rw [hy]; exact Y.X.fromSpecResidueField_apply e _

end GlobalTheory.CompanionTheory.Ar.XR
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoordsStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_normal_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), ∀ e ∈ genericPoints Y.X, ∃ (K : Type) (_ : Field K) (_ : CharZero K) (n : ℕ) (x : Fin n → K) (y : Sp K ⟶ Xo.XF c), CoordTie ℤ (y ≫ Y.j) x ∧ Flat.NormalCpt (y ≫ Y.j) ∧ GlobalTheory.CompanionTheory.Ar.genPt (y ≫ Y.j) = e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.exists_cpt_of_genericPoint | exact GlobalTheory.CompanionTheory.Ar.XR.exists_cpt_of_genericPoint | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.exists_cpt_of_genericPoint <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartOfBasis
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Conj.GermInh
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem chart_of_basis (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {n : ℕ}
    (tg : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (h : GlobalTheory.ChartCompare.IsTanBasisG t x0 tg) :
    ∃ (G : Germ.FGLaw S (Fintype.card (Fin n))) (A : Germ.OAct (𝓞 E) G)
      (tg' : Fin (Fintype.card (Fin n)) → (Sp (DualNumber S) ⟶ t.G.left)) (x : ∀ m, jOG x0 _ m 1 ⟶ t.G),
      IsChartG t x0 _ G.F A.act tg' (fun l j => if l = j then 1 else 0) x ∧ (∀ l, IsTanAtG t x0 (tg' l)) ∧
      ∀ w, IsTanAtG t x0 w → ∃! a : Fin (Fintype.card (Fin n)) → S, IsCombAtG t x0 tg' a w := by
  obtain ⟨d, G, A, uvec, x, rfl, hu, hc⟩ := GlobalTheory.ChartData.exists_isChartG_of_basis E H X0 t S x0 _ tg h.1 h.2
  let e := Fintype.equivFin (Fin n)
  refine ⟨G, A, fun i => tg (e.symm i), x, ⟨hc.zero, hc.trunc, hc.law, hc.act, fun l => ?_, fun v => ?_⟩,
    fun l => h.1 _, fun w hw => ?_⟩
  · have := hc.tan (e.symm l)
    convert this using 2 with j
    rw [hu]; simp [e, Fin.ext_iff, eq_comm]
  · refine ⟨v, fun j => by simp, fun a ha => funext fun j => by simpa using ha j⟩
  · obtain ⟨a, ha, hu⟩ := h.2 w hw
    refine ⟨fun i => a (e.symm i), ha, fun b hb => ?_⟩
    have := hu (fun l => b (e l)) (by simpa only [e, Equiv.apply_symm_apply] using hb)
    funext i; rw [← this]; simp

theorem germ_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0), ∃ d, Nonempty (GermAt t x d) := by
  intro E _ _ _ H _ hs X0 t hp S _ _ x0
  obtain ⟨n, tg, h⟩ := GlobalTheory.ChartDataChecks.premises_met t x0
  obtain ⟨G, A, tg', x, hc, ht, hb⟩ := chart_of_basis t x0 tg h
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, -, htr, hfa, had, -⟩ := GermB.frameSt_holds E H X0 t S x0 _ G A _ tg' _ x hc
  obtain ⟨hax, hr⟩ := FBIdAd.fbId E H X0 t hp hs S x0 _ G A _ tg' _ x e ph1 ph2 sy ad hc hfr hfa had
  exact ⟨_, ⟨⟨mkFB G A ph1 ph2 sy ad hax hr, x, e, tg', hc, ht, hb, hfr, htr, hfa⟩⟩⟩

section One
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

end One

end GlobalTheory.CompanionTheory.Ar.Conj.GermInh
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueLineBundleSection
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueLineBundleSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl.TorsChart

theorem alg {R : Type*} [CommRing R] (t s : R) (g g' a r v : Rˣ) (N n : ℕ)
    (h : t * ((g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a).val * (g * r).val ^ (N ^ 2)) ^ n =
      ((g' ^ (n : ℤ)).val * s) ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n) :
    t * (a.val * r.val ^ (N ^ 2)) ^ n = s ^ (N ^ 2) * v.val ^ n := by
  have hz : ∀ u : Rˣ, u ^ (-((N : ℤ) ^ 2)) = (u ^ (N ^ 2))⁻¹ := fun u => by
    rw [zpow_neg, ← zpow_natCast]; push_cast; rfl
  have e₁ : g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a * (g * r) ^ (N ^ 2) = g * (a * r ^ (N ^ 2)) := by
    rw [hz, zpow_one, mul_pow]
    calc g * (g ^ (N ^ 2))⁻¹ * a * (g ^ (N ^ 2) * r ^ (N ^ 2))
        = g * (a * r ^ (N ^ 2)) * ((g ^ (N ^ 2))⁻¹ * g ^ (N ^ 2)) := by ac_rfl
      _ = _ := by rw [inv_mul_cancel, _root_.mul_one]
  have e₂ : ((g' ^ (n : ℤ)) ^ (N ^ 2)) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v) ^ n = g ^ n * v ^ n := by
    rw [hz, zpow_one, zpow_natCast, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm n]
    calc g' ^ (N ^ 2 * n) * (g ^ n * (g' ^ (N ^ 2 * n))⁻¹ * v ^ n)
        = g ^ n * v ^ n * (g' ^ (N ^ 2 * n) * (g' ^ (N ^ 2 * n))⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel, _root_.mul_one]
  have l : (g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a).val * (g * r).val ^ (N ^ 2) = g.val * (a.val * r.val ^ (N ^ 2)) := by
    have := congrArg Units.val e₁
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have m : (g' ^ (n : ℤ)).val ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n = g.val ^ n * v.val ^ n := by
    have := congrArg Units.val e₂
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  rw [l] at h
  apply (g ^ n).isUnit.mul_right_inj.1
  simp only [Units.val_pow_eq_pow_val]
  calc g.val ^ n * (t * (a.val * r.val ^ (N ^ 2)) ^ n)
      = t * (g.val * (a.val * r.val ^ (N ^ 2))) ^ n := by rw [mul_pow g.val]; ring
    _ = _ := h
    _ = ((g' ^ (n : ℤ)).val ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n) * s ^ (N ^ 2) := by
        rw [mul_pow (g' ^ (n : ℤ)).val]; ring
    _ = g.val ^ n * v.val ^ n * s ^ (N ^ 2) := by rw [m]
    _ = _ := by ring

variable {F : Type} [Field F] {X S : Scheme.{0}}

theorem charts {L : LB X} {q : X ⟶ X} {e : S ⟶ X} {b : Sp F ⟶ S} {o y : Sp F ⟶ X}
    (hbe : b ≫ e = o) (hoq : o ≫ q = o) (hyq : y ≫ q = o) {n N : ℕ}
    (w : LB.Gen (LB.LinComb L (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)])) (hw : w.IsGen)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => e) (fun _ => 1))) (hr : rig.IsGen)
    (s : Out.H0 L n) (T : F) (i₀ i : L.ι) (h₀ : ⊤ ≤ o ⁻¹ᵁ L.U i₀) (hi : ⊤ ≤ y ⁻¹ᵁ L.U i)
    (hE : T * (valF o _ (w.s ![i₀, i₀]).val * valF b _ (rig.s fun _ => i₀).val ^ (N ^ 2)) ^ n =
      valF y _ (s.f fun _ => i) ^ (N ^ 2) * valF y _ (w.s ![i₀, i]).val ^ n)
    (z : Sp F) (J : (Sp F ⟶ X) → L.ι) (hJ : Good L z J) :
    toStk z T * ((val w o z J).val * (val rig b z J).val ^ (N ^ 2)) ^ n =
      sval s y z J ^ (N ^ 2) * (val w y z J).val ^ n := by
  have m₀ : o z ∈ L.U i₀ := (top_le_iff_mem _ _ z).1 h₀
  have mi : y z ∈ L.U i := (top_le_iff_mem _ _ z).1 hi
  have mo : o z ∈ L.U (J o) := hJ o
  have my : y z ∈ L.U (J y) := hJ y
  have wm : ∀ (r : Sp F ⟶ X), r ≫ q = o → ∀ a c : L.ι, o z ∈ L.U a → r z ∈ L.U c →
      r z ∈ LB.wchart L (K := Fin 2) ![q, 𝟙 X] ![a, c] := by
    intro r hr' a c ha hc
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show q (r z) ∈ L.U a
      have : q (r z) = o z := by rw [← hr']; rfl
      rw [this]; exact ha
    · exact hc
  have rm : ∀ a : L.ι, o z ∈ L.U a → b z ∈ LB.wchart L (K := PUnit) (fun _ => e) (fun _ => a) := by
    intro a ha
    refine Set.mem_iInter.2 fun _ => ?_
    show e (b z) ∈ L.U a
    have : e (b z) = o z := by rw [← hbe]; rfl
    rw [this]; exact ha
  have sm : ∀ a : L.ι, y z ∈ L.U a → y z ∈ LB.wchart L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a) :=
    fun a ha => Set.mem_iInter.2 fun _ => ha
  have a₁ : toStk z (valF o _ (w.s ![i₀, i₀]).val) =
      (trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] o z ![i₀, i₀] ![J o, J o] *
        gm o z (LB.wchart L ![q, 𝟙 X] ![J o, J o]) (w.s ![J o, J o])).val :=
    (toStk_valF o _ z (wm o hoq _ _ m₀ m₀) _).trans
      (congrArg Units.val (gen_trans hw o z (wm o hoq _ _ m₀ m₀) (wm o hoq (J o) (J o) mo mo)))
  have a₂ : toStk z (valF b _ (rig.s fun _ => i₀).val) =
      (trF (L := L) (K := PUnit) (fun _ => e) (fun _ => 1) b z (fun _ => i₀) (fun _ => J o) *
        gm b z (LB.wchart L (fun _ => e) (fun _ => J o)) (rig.s fun _ => J o)).val :=
    (toStk_valF b _ z (rm _ m₀) _).trans (congrArg Units.val (gen_trans hr b z (rm _ m₀) (rm (J o) mo)))
  have a₃ : toStk z (valF y _ (s.f fun _ => i)) =
      (trF (L := L) (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) y z (fun _ => i) (fun _ => J y)).val *
        gs y z (LB.wchart L (fun _ => 𝟙 X) (fun _ => J y)) (s.f fun _ => J y) :=
    (GlobalTheory.ThetaInValues.toStk_valF' y _ z (sm _ mi) _).trans (sec_trans s y z (sm _ mi) (sm (J y) my))
  have a₄ : toStk z (valF y _ (w.s ![i₀, i]).val) =
      (trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] y z ![i₀, i] ![J o, J y] *
        gm y z (LB.wchart L ![q, 𝟙 X] ![J o, J y]) (w.s ![J o, J y])).val :=
    (toStk_valF y _ z (wm y hyq _ _ m₀ mi) _).trans
      (congrArg Units.val (gen_trans hw y z (wm y hyq _ _ m₀ mi) (wm y hyq (J o) (J y) mo my)))
  have hE' := congrArg (toStk z) hE
  simp only [map_mul, map_pow] at hE'
  rw [a₁, a₂, a₃, a₄] at hE'
  have f₁ : trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] o z ![i₀, i₀] ![J o, J o] =
      gm o z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm o z _ (L.g i₀ (J o)) ^ (-((N : ℤ) ^ 2)) := by
    rw [trF, Fin.prod_univ_two]
    show gm (o ≫ q) z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm (o ≫ 𝟙 X) z _ (L.g i₀ (J o)) ^ (-((N : ℤ) ^ 2)) = _
    rw [hoq, Category.comp_id]
  have f₂ : trF (L := L) (K := PUnit) (fun _ => e) (fun _ => 1) b z (fun _ => i₀) (fun _ => J o) =
      gm o z _ (L.g i₀ (J o)) := by
    rw [trF, Fintype.prod_unique]
    show gm (b ≫ e) z _ (L.g i₀ (J o)) ^ (1 : ℤ) = _
    rw [hbe, zpow_one]
  have f₃ : trF (L := L) (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) y z (fun _ => i) (fun _ => J y) =
      gm y z _ (L.g i (J y)) ^ (n : ℤ) := by
    rw [trF, Fintype.prod_unique]
    show gm (y ≫ 𝟙 X) z _ (L.g i (J y)) ^ (n : ℤ) = _
    rw [Category.comp_id]
  have f₄ : trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] y z ![i₀, i] ![J o, J y] =
      gm o z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm y z _ (L.g i (J y)) ^ (-((N : ℤ) ^ 2)) := by
    rw [trF, Fin.prod_univ_two]
    show gm (y ≫ q) z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm (y ≫ 𝟙 X) z _ (L.g i (J y)) ^ (-((N : ℤ) ^ 2)) = _
    rw [hyq, Category.comp_id]
  rw [f₁, f₂, f₃, f₄] at hE'
  rw [val_of w o z J ![J o, J o] (Fin.forall_fin_two.2 ⟨congrArg J hoq, congrArg J (Category.comp_id _)⟩),
    val_of rig b z J (fun _ => J o) (fun _ => congrArg J hbe),
    sval_of s y z J (fun _ => J y) (fun _ => congrArg J (Category.comp_id _)),
    val_of w y z J ![J o, J y] (Fin.forall_fin_two.2 ⟨congrArg J hyq, congrArg J (Category.comp_id _)⟩)]
  exact alg _ _ _ _ _ _ _ N n hE'

end GlobalTheory.CompanionTheory.Ar.Sl.Transl.TorsChart

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem torsVal_charts : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) (N : ℕ) (T : F), TorsVal P s y N T → ∀ (z : Sp F) (J : (Sp F ⟶ G.left) → P.L.ι), Good P.L z J → ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), w.IsGen ∧ toStk z T * ((val (Z := Sp F) w (1 : Over.mk b ⟶ G).left z J).val * (val (Z := Sp F) P.rig b z J).val ^ (N ^ 2)) ^ n = sval (Z := Sp F) s y.left z J ^ (N ^ 2) * (val (Z := Sp F) w y.left z J).val ^ n := by
  intro S G _ _ P n s F _ b y N T hT z J hJ
  obtain ⟨-, hy, w, i₀, i, hw, h₀, hi, hE⟩ := hT
  have key : ∀ t : Over.mk b ⟶ G, t ^ N = 1 →
      t.left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (1 : Over.mk b ⟶ G).left := by
    intro t ht
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ht]
  have hbe : b ≫ eSec G = (1 : Over.mk b ⟶ G).left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl
  refine ⟨w, hw, TorsChart.charts (e := eSec G) hbe (key 1 (one_pow N)) (key y hy) w hw P.rig P.rigGen
    s T i₀ i h₀ hi hE z J hJ⟩

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueLineBundleSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_value_line_bundle_section : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) (N : ℕ) (T : F), TorsVal P s y N T → ∀ (z : Sp F) (J : (Sp F ⟶ G.left) → P.L.ι), Good P.L z J → ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), w.IsGen ∧ toStk z T * ((val (Z := Sp F) w (1 : Over.mk b ⟶ G).left z J).val * (val (Z := Sp F) P.rig b z J).val ^ (N ^ 2)) ^ n = sval (Z := Sp F) s y.left z J ^ (N ^ 2) * (val (Z := Sp F) w y.left z J).val ^ n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.torsVal_charts | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.torsVal_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.torsVal_charts <;> assumption)
end
end
