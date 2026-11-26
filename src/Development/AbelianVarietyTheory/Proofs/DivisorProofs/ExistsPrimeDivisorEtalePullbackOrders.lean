module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfImHermFormIntegralRealBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleDiv

open IsLocalRing

theorem formallyEtale_of_bijective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) : f.FormallyEtale := by
  algebraize [f]
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

theorem formallyEtale_of_comp_bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hg : Function.Bijective g) (h : (g.comp f).FormallyEtale) :
    f.FormallyEtale := by
  let e := RingEquiv.ofBijective g hg
  have : f = (e.symm : T →+* S).comp (g.comp f) := by
    ext x
    exact (e.symm_apply_apply (f x)).symm
  rw [this]
  exact h.comp (formallyEtale_of_bijective _ e.symm.bijective)

theorem formallyEtale_stalkMap {M W : Scheme.{0}} (f : M ⟶ W) (U : M.Opens)
    [Etale (U.ι ≫ f)] (w : U.toScheme) : (f.stalkMap (U.ι w)).hom.FormallyEtale := by
  have hu := FormallyUnramified.stalkMap (U.ι ≫ f) w
  have hs : ((U.ι ≫ f).stalkMap w).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ w))
  have h : ((U.ι ≫ f).stalkMap w).hom.FormallyEtale := by
    algebraize [((U.ι ≫ f).stalkMap w).hom]
    exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have : IsIso (U.ι.stalkMap w) := inferInstance
  rw [Scheme.Hom.stalkMap_comp] at h
  exact formallyEtale_of_comp_bijective (f.stalkMap (U.ι w)).hom (U.ι.stalkMap w).hom
    (ConcreteCategory.bijective_of_isIso _) h

theorem strictMono_ι {M : Scheme.{0}} (U : M.Opens) : StrictMono U.ι := by
  have hi := U.ι.isOpenEmbedding.isInducing
  intro a b h
  refine lt_of_le_not_ge ?_ ?_
  · exact hi.specializes_iff.2 h.le
  · exact fun h' => h.not_ge (hi.specializes_iff.1 h')

theorem map_maximalIdeal_stalk {M W : Scheme.{0}} (f : M ⟶ W) [LocallyOfFiniteType f] (z : M)
    (h : (f.stalkMap z).hom.FormallyEtale) :
    (maximalIdeal (W.presheaf.stalk (f z))).map (f.stalkMap z).hom =
      maximalIdeal (M.presheaf.stalk z) := by
  have hft := LocallyOfFiniteType.stalkMap f z
  algebraize [(f.stalkMap z).hom]
  have : IsLocalHom (algebraMap (W.presheaf.stalk (f z)) (M.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
  exact Algebra.FormallyUnramified.map_maximalIdeal

theorem log_ordFrac_map {K L : Type} [Field K] [Field L] (V : ValuationSubring K)
    (V' : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing V']
    (ρ : K →+* L) (ψ : V →+* V') (hψ : ∀ a, (ψ a : L) = ρ a) {t : V} (ht : Irreducible t)
    (ht' : Irreducible (ψ t)) {g : K} (hg : g ≠ 0) :
    WithZero.log (Ring.ordFrac V' (ρ g)) = WithZero.log (Ring.ordFrac V g) := by
  obtain ⟨m, u, rfl⟩ := exists_eq_unit_mul_zpow (F := K) ht hg
  have h1 := ordTop_vw_unit_mul_zpow (F := K) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := L) ht' (Units.map ψ.toMonoidHom u) m
  have e : ρ (algebraMap V K u * algebraMap V K t ^ m) =
      algebraMap V' L (Units.map ψ.toMonoidHom u) * algebraMap V' L (ψ t) ^ m := by
    rw [map_mul, map_zpow₀]
    simp [hψ]
  rw [← e] at h2
  rw [ordTop_vw_of_ne_zero _ hg, WithTop.coe_inj] at h1
  rw [ordTop_vw_of_ne_zero _ ((map_ne_zero ρ).2 hg), WithTop.coe_inj] at h2
  rw [h1, h2]

theorem isFreeGen_formMap {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] {α : k →+* A}
    {β : k →+* B} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β) {D : ℕ}
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem maximalIdeal_eq_bot {X : Scheme.{0}} [IsIntegral X] {x : X} (h : Order.coheight x = 0) :
    maximalIdeal (X.presheaf.stalk x) = ⊥ := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h.le
  exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime ⊥).symm

theorem coheight_apply_eq_one {M W : Scheme.{0}} [IsIntegral W] (f : M ⟶ W) [LocallyOfFiniteType f]
    (U : M.Opens) [Etale (U.ι ≫ f)] (w : U.toScheme) (h1 : Order.coheight (U.ι w) = 1)
    (hB : maximalIdeal (M.presheaf.stalk (U.ι w)) ≠ ⊥) : Order.coheight (f (U.ι w)) = 1 := by
  have hle : Order.coheight w ≤ 1 :=
    h1 ▸ Order.coheight_le_coheight_apply_of_strictMono _ (strictMono_ι U) w
  have hle' := GlobalTheory.GenExtendNormal.coheight_apply_le_one (U.ι ≫ f) (Flat.generalizingMap _) w hle
  refine le_antisymm hle' ?_
  rw [Order.one_le_iff_ne_zero]
  intro h0
  apply hB
  rw [← map_maximalIdeal_stalk f _ (formallyEtale_stalkMap f U w), maximalIdeal_eq_bot h0,
    Ideal.map_bot]

theorem exists_isAt_ord_formOrd : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f]
    (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens),
    Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ E' : DivOver (f ≫ p), E'.IsAt z →
    ∃ E : DivOver p, E.IsAt (f z) ∧
      (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧
      ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro M W _ _ _ _ p f _ n _ _ U hU z hz E' hE'
  haveI := hU
  obtain ⟨w, rfl⟩ : ∃ w : U.toScheme, U.ι w = z := ⟨⟨z, hz⟩, rfl⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme W := GlobalTheory.ModifSections.isNormalScheme_of_smooth p
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f p
  haveI hB : IsDiscreteValuationRing (M.presheaf.stalk (U.ι w)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing hE'.equiv.symm
  have hφ := formallyEtale_stalkMap f U w
  have hmax := map_maximalIdeal_stalk f (U.ι w) hφ
  have hc := coheight_apply_eq_one f U w hE'.coheight_eq_one
    (IsDiscreteValuationRing.not_a_field _)
  obtain ⟨E, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hc
  haveI hA : IsDiscreteValuationRing (W.presheaf.stalk (f (U.ι w))) :=
    GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hc
  let ψ : E.ring →+* E'.ring :=
    hE'.equiv.toRingHom.comp ((f.stalkMap (U.ι w)).hom.comp hE.equiv.symm.toRingHom)
  have hψ : ∀ a, (ψ a : M.functionField) = functionFieldMap f a := by
    intro a
    obtain ⟨b, rfl⟩ := hE.equiv.surjective a
    have e : ψ (hE.equiv b) = hE'.equiv (f.stalkMap (U.ι w) b) := by
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    rw [e]
    exact (functionFieldMap_algebraMap f (U.ι w) b).symm
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (W.presheaf.stalk (f (U.ι w)))
  have ht' : Irreducible (f.stalkMap (U.ι w) t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at ht ⊢
    rw [← hmax, ht, Ideal.map_span, Set.image_singleton]
  have htE : Irreducible (hE.equiv t) := ht.map hE.equiv
  have htE' : Irreducible (ψ (hE.equiv t)) := by
    have e : ψ (hE.equiv t) = hE'.equiv (f.stalkMap (U.ι w) t) := by
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    rw [e]
    exact ht'.map hE'.equiv
  have hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := fun g =>
    log_ordFrac_map E.ring E'.ring (functionFieldMap f) ψ hψ htE htE' g.ne_zero
  refine ⟨E, hE, hord, fun η hη => ?_⟩
  have hn : topologicalKrullDim W = n := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hn
  obtain ⟨c, rfl⟩ := (E.isFreeGen_toRat hω).2 η
  have hc0 : c ≠ 0 := fun h => hη (by rw [h]; exact zero_smul _ _)
  have hconst : ψ.comp E.const = E'.const := RingHom.ext fun a => Subtype.ext
    ((hψ _).trans (RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) a))
  have hψFE : ψ.FormallyEtale :=
    RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp
      (formallyEtale_of_bijective _ hE.equiv.symm.bijective) hφ)
      (formallyEtale_of_bijective _ hE'.equiv.bijective)
  have h3 : ((functionFieldMap f).comp E.ring.subtype).comp E.const = Cartier.constFn (f ≫ p) := by
    ext a
    exact RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) a
  have e1 : GlobalTheory.EtaleKlt.ratPull p f n (E.toRat n ω) =
      E'.toRat n (TopForm.formMap n ψ hconst ω) := by
    change TopForm.formMap n (functionFieldMap f) _ (TopForm.formMap n E.ring.subtype rfl ω) =
      TopForm.formMap n E'.ring.subtype rfl (TopForm.formMap n ψ hconst ω)
    exact (formMap_formMap E.ring.subtype (functionFieldMap f)
      ((functionFieldMap f).comp E.ring.subtype) rfl _ _ h3 ω).trans
      (formMap_formMap ψ E'.ring.subtype ((functionFieldMap f).comp E.ring.subtype)
        (RingHom.ext hψ) _ _ h3 ω).symm
  have h1 : E.formOrd (c • E.toRat n ω) = E.ord (Units.mk0 c hc0) :=
    DivOver.IsFormOrd.formOrd_eq hη ⟨ω, hω, Units.mk0 c hc0, rfl, rfl⟩
  have hη' : GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω) ≠ 0 := by
    have hfree := E'.isFreeGen_toRat (isFreeGen_formMap hψFE hconst hω)
    rw [map_smulₛₗ, e1]
    intro h0
    have := hfree.1 (a₁ := functionFieldMap f c) (a₂ := 0) (by simp only [h0, zero_smul])
    exact hc0 ((map_eq_zero _).1 this)
  have h2 : E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω)) =
      E'.ord (Units.map (functionFieldMap f).toMonoidHom (Units.mk0 c hc0)) :=
    DivOver.IsFormOrd.formOrd_eq hη' ⟨_, isFreeGen_formMap hψFE hconst hω, _,
      by rw [map_smulₛₗ, e1]; rfl, rfl⟩
  change E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω)) =
    E.formOrd (c • E.toRat n ω)
  rw [h1, h2, hord]

end GlobalTheory.EtaleDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrdersStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeDivisor_etalePullback_orders : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ E' : DivOver (f ≫ p), E'.IsAt z → ∃ E : DivOver p, E.IsAt (f z) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd | exact GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd | (intros; apply GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDualDetLieEqNegFlatSectionDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatSectionValueEqMulDetInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatSectionValueEqMulDetInv
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.FlatValue

theorem exists_reduced_frameRing (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) :
    ∃ (A : TRing K) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), (∀ τ, IsUnit (X τ).det) ∧
      ∀ (T : Type) [CommRing T] [Algebra K T] (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T) (a : Tˣ),
        (∀ τ, IsUnit (g τ).det) → ∃ k : A.R →ₐ[K] T, (∀ τ, (X τ).map k = g τ) ∧ k (s : A.R) = (a : T) := by
  let p : TRing K := ⟨0, ⊥, Ideal.isRadical_bot⟩
  obtain ⟨A, π, X, s, hA⟩ := GlobalTheory.T.exists_frameRing_over_testRing K J m p
  refine ⟨A, X, s, hA.1, fun T _ _ g a hg => ?_⟩
  let ψ : p.R →ₐ[K] T := Ideal.Quotient.liftₐ ⊥ (MvPolynomial.aeval Fin.elim0) (fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero])
  obtain ⟨k, ⟨-, h1, h2⟩, -⟩ := hA.2 T ψ g a hg
  exact ⟨k, h1, h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exOf_flatWt (hq : Dw.q = 0) (τ : Psi H) (b : E →+* ℂ) (i : Fin (Dw.mult b)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨b, i⟩) = if b = τ.1 then -1 else 0 := by
  have hi := i.2
  by_cases h : b (H.rt : E) = H.rt0
  · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
    refine (wtOf_big _ 0 ⟨b, h⟩ i hp).trans ?_
    simp [flatWt, parWt, Subtype.ext_iff]
  · have hq' : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
    omega

theorem evR_mul_det_field (hq : Dw.q = 0) (τ : Psi H) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (K : Type) [Field K] [Algebra c.F K] (z y : FrPt Xo c K) (Y : Mats Dw K) (u : Kˣ) (hY : ∀ b, (Y b).det ≠ 0)
    (h : FrChg (fun b => (Y b)ᵀ) (u : K) z y) : evR Xo c f y * (Y τ.1).det = evR Xo c f z := by
  obtain ⟨G, hG, hev⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ E H Dw l Xo c K z _
    (fun b => if b = τ.1 then 1 else 0) (fun _ _ => 0) rfl
    (fun b i => by rw [exOf_flatWt hq]; split_ifs <;> simp) f hf
  simp only [Finset.sum_const_zero] at hG
  have hC : G = MvPolynomial.C (G.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hG.totalDegree_le)
  have h1 := hev y Y u hY h
  have h2 := hev z (fun _ => 1) 1 (fun _ => by simp) (by
    simpa using (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K z z z).1)
  rw [hC] at h1 h2
  simp only [Formalism.L2.LamCM.evalFr, MvPolynomial.eval_C, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq',
    Finset.mem_univ, if_true, Matrix.det_one, ite_self, Finset.prod_const_one, one_mul] at h1 h2
  rw [mul_comm, h1, h2]

theorem exists_evR_mul_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ), ∃ b : c.F, b ≠ 0 ∧ (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s
  refine ⟨evR Xo c s.sig P.y₀,
    left_ne_zero_of_mul_eq_one (s.evR_mul_inv P.on (GlobalTheory.FlagTan.fromTest_of_isLocalRing _)), ?_⟩
  obtain ⟨A, X, t, hX, hA⟩ := exists_reduced_frameRing c.F (E →+* ℂ) Dw.mult
  haveI : _root_.IsReduced A.R := (Ideal.isRadical_iff_quotient_reduced _).1 A.rad
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.FlagTan.exists_frMap (Algebra.ofId c.F A.R) P.y₀
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A.R w₀ (fun b => (X b)ᵀ) t
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  have step : ∀ (S : Type) [CommRing S] [Algebra c.F S] (k : A.R →ₐ[c.F] S) (z y : FrPt Xo c S),
      FrMap (Algebra.ofId c.F S) P.y₀ z → (FrMap k w y ↔ FrChg (fun b => ((X b).map k)ᵀ) (k t) z y) := by
    intro S _ _ k z y hz
    have h0 : FrMap k w₀ z := GlobalTheory.FlagTan.frMap_of_comp hw₀ hz fun a => k.commutes a
    exact GlobalTheory.FlagTan.frMap_iff_frChg hw h0
  have nat : ∀ (S : Type) [CommRing S] [Algebra c.F S] (k : A.R →ₐ[c.F] S) (y : FrPt Xo c S), FrMap k w y →
      evR Xo c s.sig y = k (evR Xo c s.sig w) := fun S _ _ k y h =>
    GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c s.sig s.sig_mem.1 k w y h
  have univ : evR Xo c s.sig w * (X τ.1).det = algebraMap c.F A.R (evR Xo c s.sig P.y₀) := by
    rw [← sub_eq_zero]
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun q hq => ?_)
    let K : Type := q.ResidueField
    let k : A.R →ₐ[c.F] K := IsScalarTower.toAlgHom c.F A.R K
    obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap (Algebra.ofId c.F K) P.y₀
    obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frMap k w
    have hd : ∀ b, ((X b).map k).det = k (X b).det := fun b => (AlgHom.map_det k (X b)).symm
    have h1 := evR_mul_det_field hD.q τ s.sig_mem K z y (fun b => (X b).map k)
      (Units.map (k : A.R →* K) t) (fun b => by rw [hd]; exact ((hX b).map k).ne_zero) ((step K k z y hz).1 hy)
    rw [nat K k y hy, GlobalTheory.FlagTan.evR_frMap s.sig_mem.1 hz, hd] at h1
    rw [← Ideal.algebraMap_residueField_eq_zero]
    show k _ = 0
    rw [map_sub, map_mul, h1, k.commutes]
    exact sub_self _
  intro S _ _ z y Y u hY hu hz h
  obtain ⟨k, hk, hkt⟩ := hA S Y hu.unit hY
  have hy : FrMap k w y := (step S k z y hz).2 (by
    rw [hkt, IsUnit.unit_spec]
    simpa only [hk] using h)
  rw [nat S k y hy, ← hk τ.1, ← k.commutes, ← univ, map_mul]
  exact congrArg _ (AlgHom.map_det k (X τ.1)).symm

end GlobalTheory.FlatValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatSectionValueEqMulDetInvStatement
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flatSectionValue_eq_mul_det_inv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ), ∃ b : c.F, b ≠ 0 ∧ (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) := by
  first | exact @GlobalTheory.FlatValue.exists_evR_mul_det | exact GlobalTheory.FlatValue.exists_evR_mul_det | (intros; apply GlobalTheory.FlatValue.exists_evR_mul_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionValuationAtFinitePlaceEqSubDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionValuationAtFinitePlaceEqSubDet
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

theorem vV_algebraMap_of_isUnit (T : CDVR) {u : T.V} (hu : IsUnit u) : vV T.V (algebraMap T.V T.Fr u) = 0 := by
  have : valV T.V (algebraMap T.V T.Fr u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal u).1 h hu
  simp [vV, this]

theorem rho_vw_eq_vAdd_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ w, s.rho_vw w = (vAdd w b : ℝ) - (vAdd w (P.B w τ.1).det : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s b hb hev w
  obtain ⟨v, hv⟩ := s.hasPts.2 w
  have hval := s.val_eq hv
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  have hval' : nval T.V e (evR Xo c s.sig y.1) = ((flDefect_vw Dw c τ w + s.rho_vw w : ℝ) : EReal) := hval
  have hδ : flDefect_vw Dw c τ w = 0 := by simp [flDefect_vw, hD.q]
  rw [hδ, zero_add] at hval'
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F T.Fr
    (Algebra.ofId c.F T.Fr) P.y₀
  obtain ⟨ha, hB, hloc⟩ := P.loc w
  have hx : y.1.x = z.x := (P.only T.Fr y.1 hy.2).trans hz.1.symm
  obtain ⟨Y, u, hY, hch⟩ := hloc T io e ho y.1 z y.2.2 hz hx
  have hdet : ∀ τ', ((P.B w τ').map io * (Y τ').map (algebraMap T.V T.Fr)).det =
      io (P.B w τ').det * algebraMap T.V T.Fr (Y τ').det := fun τ' => by
    rw [Matrix.det_mul, RingHom.map_det, RingHom.map_det]; rfl
  have hYne : ∀ τ', algebraMap T.V T.Fr (Y τ').det ≠ 0 := fun τ' => ((hY τ').map _).ne_zero
  have hBne : ∀ τ', io (P.B w τ').det ≠ 0 := fun τ' => (map_ne_zero io).2 (hB τ')
  have key := hev T.Fr z y.1 (fun τ' => (P.B w τ').map io * (Y τ').map (algebraMap T.V T.Fr)) _
    (fun τ' => by rw [hdet]; exact (mul_ne_zero (hBne τ') (hYne τ')).isUnit)
    (mul_ne_zero ((map_ne_zero io).2 ha) (u.isUnit.map _).ne_zero).isUnit hz hch
  rw [hdet] at key
  have key' : evR Xo c s.sig y.1 * (io (P.B w τ.1).det * algebraMap T.V T.Fr (Y τ.1).det) = io b := key
  have hbne : io b ≠ 0 := (map_ne_zero io).2 hb
  have h0 : evR Xo c s.sig y.1 ≠ 0 := left_ne_zero_of_mul (key' ▸ hbne)
  have h1 := congrArg (vV T.V) key'
  rw [vV_mul h0 (mul_ne_zero (hBne _) (hYne _)), vV_mul (hBne _) (hYne _), vV_algebraMap_of_isUnit T (hY _),
    ho.2, ho.2] at h1
  rw [nval_of_ne h0, EReal.coe_eq_coe_iff] at hval'
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  rw [← hval', div_eq_iff he]
  show _ = ((vLa w b : ℝ) - (vLa w (P.B w τ.1).det : ℝ)) * e
  linarith

end GlobalTheory.DefPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionValuationAtFinitePlaceEqSubDetStatement
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatSection_valuation_at_finitePlace_eq_sub_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ w, s.rho_vw w = (vAdd w b : ℝ) - (vAdd w (P.B w τ.1).det : ℝ) := by
  first | exact @GlobalTheory.DefPt.rho_vw_eq_vAdd_sub | exact GlobalTheory.DefPt.rho_vw_eq_vAdd_sub | (intros; apply GlobalTheory.DefPt.rho_vw_eq_vAdd_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDualDetLieEqNegFlatSectionDegree
noncomputable section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

theorem degLie_eq_neg_deg_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ (τ : Psi H) (s : FlatSec U ξ Z τ), P.degLie τ.1 = -s.deg) ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 → Dw.mult τ = 0 := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P
  refine ⟨fun τ s => ?_, fun τ h => ?_⟩
  · obtain ⟨b, hb0, hb⟩ := GlobalTheory.T.exists_flatSectionValue_eq_mul_det_inv E H Dw l Xo c r U ξ hD Z P τ s
    have h2 := GlobalTheory.T.flatSection_valuation_at_finitePlace_eq_sub_det E H Dw l Xo c r U ξ hD Z P τ s b hb0 hb
    have h3 := GlobalTheory.T.constantNorm_flatSection_eq_norm_div_norm_det E H Dw l Xo c r U ξ hD Z P τ s b hb0 hb
    have hX : ∀ σ, 0 < ‖(P.X σ τ.1).det‖ := fun σ => norm_pos_iff.2 ((P.arch σ).2.1 τ.1)
    have hfB : (Function.support fun w => (vAdd w (P.B w τ.1).det : ℝ)).Finite := by
      have e : (fun w => (vAdd w (P.B w τ.1).det : ℝ)) = (fun w => (vAdd w b : ℝ)) - s.rho_vw := by
        funext w; rw [Pi.sub_apply, h2 w]; ring
      rw [e]
      exact ((finite_vAdd hb0).union s.finite_rho).subset (Function.support_sub _ _)
    have hm := lineDeg_mul (r := fun σ => ‖(P.X σ τ.1).det‖) (r' := s.cInf) hX s.cInf_pos hfB s.finite_rho
    have e1 : ((fun σ => ‖(P.X σ τ.1).det‖) * s.cInf) = fun σ : c.F →+* ℂ => ‖σ b‖ := by
      funext σ; rw [Pi.mul_apply, h3 σ]; field_simp [(hX σ).ne']
    have e2 : ((fun w => (vAdd w (P.B w τ.1).det : ℝ)) + s.rho_vw) = fun w => (vAdd w b : ℝ) := by
      funext w; rw [Pi.add_apply, h2 w]; ring
    rw [e1, e2, lineDeg_num hb0] at hm
    have : P.degLie τ.1 + s.deg = 0 := by
      rw [hm]; rfl
    linarith
  · have hq : Dw.q = 0 := hD.q
    simp only [Datum.mult, if_neg h, hq]

end GlobalTheory.DefPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDualDetLieEqNegFlatSectionDegreeStatement
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ (τ : Psi H) (s : FlatSec U ξ Z τ), P.degLie τ.1 = -s.deg) ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 → Dw.mult τ = 0 := by
  first | exact @GlobalTheory.DefPt.degLie_eq_neg_deg_flat | exact GlobalTheory.DefPt.degLie_eq_neg_deg_flat | (intros; apply GlobalTheory.DefPt.degLie_eq_neg_deg_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.JetUniq

open GlobalTheory.MBLow.ScaleJet

theorem tr_unique {S : Scheme.{0}} (P : PolAV S) (ρ : LB.Gen (P.L.pull (eSec P.A))) {m : ℕ} (hm : Odd m) {T : Over S}
    {th th' : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)} (hth : ∀ j, th.f j = th'.f j) {x : T ⟶ P.A} {U U' t t'}
    (hU : SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U) (hU' : SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U')
    (H : Tr P ρ m th U t) (H' : Tr P ρ m th' U' t') (j) : t.f j = t'.f j := by
  have hL := P.isLB
  obtain ⟨α, s, hα, hn, h₁, h₂⟩ := H
  obtain ⟨α', s', hα', hn', h₁', h₂'⟩ := H'
  have hc := SymLiftOdd.symLift_unique globalFns_holds P.isAb hL hm.pow _ _ hU hU'
  have ha := gen_unique' hL (fun _ _ _ => rfl) (fst T P.A).left (ptSecT P.A (1 : T ⟶ P.A)).left
    (congrArg (fun q => q.left) (lift_fst _ _ : lift (𝟙 T) (1 : T ⟶ P.A) ≫ _ = _))
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_fst globalFns_holds P.isAb T) hα hα' (fun w I hI => by
      have q := val_corr hI hn (𝟙 _)
      have q' := val_corr hI hn' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at q q'
      exact q.trans q'.symm)
  obtain ⟨p, φ, hφ⟩ := U
  obtain ⟨p', φ', hφ'⟩ := U'
  obtain rfl : p = x := hU.pt_eq
  obtain rfl : p' = p := hU'.pt_eq
  refine sec_ext_val (φ := fun _ : Fin 1 => (snd T P.A).left) hL (fun y J hJ => ?_) j
  refine (twist_val h₂ _ y hJ).trans (Eq.trans ?_ (twist_val h₂' _ y hJ).symm)
  refine congrArg₂ (· * ·) (congrArg Units.val (val_corr hJ hc _)) ?_
  refine (twist_val h₁ _ y hJ).trans (Eq.trans ?_ (twist_val h₁' _ y hJ).symm)
  exact congrArg₂ (· * ·) (congrArg Units.val (ha _ _ y J hJ)) (congrArg (gs _ y _) (hth _))

section Germ

variable {B : Type} [CommRing B] {X : Scheme.{0}}

def germAt (z : Sp B) : B →+* (Sp B).presheaf.stalk z :=
  ((Sp B).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

theorem germAt_valR (x : Sp B ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (z : Sp B) :
    germAt z (valR x U f) = gs x z U f := by
  rw [valR, dite_eq_left h, gs_eq x z U (h trivial), germAt, RingHom.comp_apply, Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp B).presheaf (homOfLE h) z trivial _

theorem germAt_ext {a b : B} (h : ∀ z : Sp B, germAt z a = germAt z b) : a = b := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a = (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b :=
    TopCat.Presheaf.section_ext (Sp B).sheaf ⊤ _ _ fun z _ => h z
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1 e

theorem isUnit_valR (x : Sp B ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) : IsUnit (valR x U u.val) := by
  rw [valR, dite_eq_left h]
  exact (u.isUnit.map _).map _

theorem valR_sec_chart {Y : Scheme.{0}} {L : LB X} (φ : Y ⟶ X) (n : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (n : ℤ)))) (y : Sp B ⟶ Y) {i i' : L.ι}
    (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i') :
    valR y (LB.wchart L (fun _ : Fin 1 => φ) fun _ => i') (s.f fun _ => i') =
      valR (y ≫ φ) (L.U i' ⊓ L.U i) (L.g i' i).val ^ n * valR y (LB.wchart L (fun _ : Fin 1 => φ) fun _ => i) (s.f fun _ => i) := by
  have a : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) fun _ => i := fun z hz => Set.mem_iInter.2 fun _ => h hz
  have a' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) fun _ => i' := fun z hz => Set.mem_iInter.2 fun _ => h' hz
  have b : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ (L.U i' ⊓ L.U i) := fun z hz => ⟨h' hz, h hz⟩
  refine germAt_ext fun z => ?_
  have q := sec_trans s y z (a' trivial) (a trivial)
  rw [trF, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val] at q
  rw [map_mul, map_pow, germAt_valR _ _ b, gs_unit (y ≫ φ) z (L.U i' ⊓ L.U i) (b trivial)]
  exact (germAt_valR _ _ a' _ z).trans (q.trans (congrArg _ (germAt_valR _ _ a _ z).symm))

theorem valR_gen_chart {Y : Scheme.{0}} {L : LB X} (φ : Y ⟶ X) {ρ : LB.Gen (L.pull φ)} (hρ : ρ.IsGen) (y : Sp B ⟶ Y)
    {i i' : L.ι} (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i') :
    valR y ((L.pull φ).U fun _ => i') (ρ.s fun _ => i').val =
      valR (y ≫ φ) (L.U i' ⊓ L.U i) (L.g i' i).val * valR y ((L.pull φ).U fun _ => i) (ρ.s fun _ => i).val := by
  have a : ⊤ ≤ y ⁻¹ᵁ (L.pull φ).U fun _ => i := fun z hz => Set.mem_iInter.2 fun _ => h hz
  have a' : ⊤ ≤ y ⁻¹ᵁ (L.pull φ).U fun _ => i' := fun z hz => Set.mem_iInter.2 fun _ => h' hz
  have b : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ (L.U i' ⊓ L.U i) := fun z hz => ⟨h' hz, h hz⟩
  refine germAt_ext fun z => ?_
  have q := congrArg Units.val (gen_trans (φ := fun _ : PUnit => φ) (ε := fun _ => 1) hρ y z (a' trivial) (a trivial))
  rw [trF, Fintype.prod_unique, zpow_one, Units.val_mul] at q
  rw [map_mul, germAt_valR _ _ b, gs_unit (y ≫ φ) z (L.U i' ⊓ L.U i) (b trivial)]
  exact ((germAt_valR _ _ a' _ z).trans (gs_unit y z _ (a' trivial) _)).trans
    (q.trans (congrArg _ ((germAt_valR _ _ a _ z).trans (gs_unit y z _ (a trivial) _)).symm))

end Germ

section Tangent

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

def toProd (A : Over (Sp R)) : A.left ⟶ (baseOver (Sp R) ⊗ A).left :=
  (lift (Over.homMk A.hom (by simp) : A ⟶ baseOver (Sp R)) (𝟙 A)).left

omit [GrpObj A] in
theorem epsLift_eq (v : epsR R ⟶ A) : epsLift v = v.left ≫ toProd A := by
  rw [epsLift, toProd, ← Over.comp_left, comp_lift, Category.comp_id]
  congr 2
  exact Over.OverMorphism.ext (Over.w v).symm

omit [GrpObj A] in
theorem epsLift_snd (v : epsR R ⟶ A) : epsLift v ≫ (snd (baseOver (Sp R)) A).left = v.left := by
  rw [epsLift, ← Over.comp_left, lift_snd]

theorem grpPullback_id : IsGrpPullback A A (𝟙 (Sp R)) (𝟙 A.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 (Sp R)) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul]
  simp [j]

theorem tan_le {v : epsR R ⟶ A} (hv : IsTangent v) {V : A.left.Opens} (hV : ⊤ ≤ eSec A ⁻¹ᵁ V) : ⊤ ≤ v.left ⁻¹ᵁ V := by
  rw [GlobalTheory.ArcLie.le_iff_fst, hv]
  exact hV

theorem fst_valR {v : epsR R ⟶ A} (hv : IsTangent v) {V : A.left.Opens} (hV : ⊤ ≤ eSec A ⁻¹ᵁ V) (f : Γ(A.left, V)) :
    (valR (A := DualNumber R) v.left V f).fst = valR (A := R) (eSec A) V f := by
  have e := GlobalTheory.HolHom.valR_spMap (TrivSqZeroExt.fstHom R R R).toRingHom v.left V (tan_le hv hV) f
  rw [hv] at e
  exact e.symm

theorem snd_valR [IsCommMonObj A] {n : ℕ} {v : Fin n → (epsR R ⟶ A)} (hv : ∀ k, IsTangent (v k)) {c : Fin n → R}
    {w : epsR R ⟶ A} (hc : IsLieComb c v w) {V : A.left.Opens} (hV : ⊤ ≤ eSec A ⁻¹ᵁ V) (f : Γ(A.left, V)) :
    (valR (A := DualNumber R) w.left V f).snd = ∑ k, c k * (valR (A := DualNumber R) (v k).left V f).snd := by
  have e := GlobalTheory.ArcLieCoord.comb_snd grpPullback_id v hv c w hc V (by rw [Category.comp_id]; exact hV) f
  simpa only [Category.comp_id] using e

omit [GrpObj A] in
theorem toProd_snd : toProd A ≫ (snd (baseOver (Sp R)) A).left = 𝟙 A.left := by
  rw [toProd, ← Over.comp_left, lift_snd]; rfl

theorem le_toProd {L : LB A.left} {i : L.ι} (h : ⊤ ≤ eSec A ⁻¹ᵁ L.U i) :
    ⊤ ≤ eSec A ⁻¹ᵁ toProd A ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd (baseOver (Sp R)) A).left) fun _ => i := by
  intro z hz
  refine Set.mem_iInter.2 fun _ => ?_
  have e : (toProd A ≫ (snd (baseOver (Sp R)) A).left) (eSec A z) ∈ L.U i := by
    rw [toProd_snd]; exact h hz
  exact e

end Tangent

theorem thJet_change : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (hp rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → ∀ (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ P.A)) (ϑ ϑ' : I → K) (J J' : I → Fin P.g → K), ThJet ⟨P, hp, rig, hr, th, hth, v, hv⟩ rfl m pt ϑ J → ThJet ⟨P, hp, rig, hr, th', hth', v', hv'⟩ rfl m pt ϑ' J' → (∀ i, ϑ' i = a * ϑ i) ∧ ∃ c : Fin P.g → K, ∀ i j, J' i j = a * ∑ l, M j l * J i l + c j * ϑ i := by
  intro K _ P hp rig hr th hth v hv th' hth' v' hv' a M hs hM m hm _ I pt ϑ ϑ' J J'
  rintro ⟨θ, hθ, U, t, i₀, c, hU, hi, H⟩ ⟨θ', hθ', U', t', i₁, c', hU', hi', H'⟩
  have := P.isAb.comm
  dsimp only at hθ hθ' hU hU' hi hi' H H'
  have k₀ : ⊤ ≤ eSec P.A ⁻¹ᵁ P.L.U i₀ := fun z hz => hi hz
  have k₁ : ⊤ ≤ eSec P.A ⁻¹ᵁ P.L.U i₁ := fun z hz => hi' hz
  have hθ₁ : ∀ j, θ'.f j = (cMul (baseOver (Sp K) ⊗ P.A).hom a θ).f j := fun j => by
    obtain ⟨i, rfl⟩ : ∃ i : P.L.ι, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    have h := LB.wchart_le P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) P.A).left) (fun _ => i) 0
    exact (hθ' i h).trans ((congrArg _ (hs i)).trans (polAVSectionInverseImage_mulConstant P _ th θ a hθ i h).symm)
  have ht : ∀ i j, (t' i).f j = constFn (baseOver (Sp K) ⊗ P.A).hom _ a * (t i).f j := fun i j => by
    obtain ⟨α, s₁, h1, h2, h3, h4⟩ := (hU i).2
    exact tr_unique P rig hm hθ₁ (hU' i).1 (hU i).1 (hU' i).2 (t' := cMul _ a (t i))
      ⟨α, cMul _ a s₁, h1, h2, twist_cMul _ _ _ _ _ _ _ _ _ _ h3, twist_cMul _ _ _ _ _ _ _ _ _ _ h4⟩ j

  let V := LB.wchart P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) P.A).left) fun _ => i₀
  let D : I → (epsR K ⟶ P.A) → DualNumber K := fun i w => valR (epsLift w) V ((t i).f fun _ => i₀)
  let r : K := valR (𝟙 (Sp K)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (rig.s fun _ => i₀).val
  let G : K := valR (A := K) (eSec P.A) (P.L.U i₁ ⊓ P.L.U i₀) (P.L.g i₁ i₀).val
  let u : Fin P.g → DualNumber K := fun j =>
    valR (A := DualNumber K) (v' j).left (P.L.U i₁ ⊓ P.L.U i₀) (P.L.g i₁ i₀).val ^ (m ^ 2)
  have k₂ : ⊤ ≤ eSec P.A ⁻¹ᵁ (P.L.U i₁ ⊓ P.L.U i₀) := fun z hz => ⟨k₁ hz, k₀ hz⟩
  have hr₀ : r ≠ 0 := (isUnit_valR (𝟙 (Sp K)) ((P.L.pull (eSec P.A)).U fun _ => i₀)
    (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  have hG₀ : G ≠ 0 := (isUnit_valR (B := K) _ _ k₂ _).ne_zero
  have hu : ∀ j, (u j).fst = G ^ (m ^ 2) := fun j => by
    rw [TrivSqZeroExt.fst_pow, fst_valR (hv'.1 j) k₂]
  have hD : ∀ i l, D i (v l) = TrivSqZeroExt.inl (r ^ (m ^ 2)) *
      (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i l + c l * ϑ i)) := H
  have hD' : ∀ i w, D i w = valR (A := DualNumber K) w.left (toProd P.A ⁻¹ᵁ V)
      (((toProd P.A).app V).hom ((t i).f fun _ => i₀)) := fun i w => by
    simp only [D]
    rw [epsLift_eq]
    exact GlobalTheory.HolHom.valR_comp _ _ _ _
  have f₁ : ∀ i j, (D i (v' j)).fst = r ^ (m ^ 2) * ϑ i := fun i j => by
    have e := congrArg TrivSqZeroExt.fst (hD i j)
    rw [hD', fst_valR (hv.1 j) (le_toProd k₀)] at e
    rw [hD', fst_valR (hv'.1 j) (le_toProd k₀), e]
    simp
  have f₂ : ∀ i j, (D i (v' j)).snd = r ^ (m ^ 2) * (∑ l, M j l * J i l + (∑ l, M j l * c l) * ϑ i) := fun i j => by
    rw [hD', snd_valR hv.1 (hM j) (le_toProd k₀), Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hD', hD]
    simp
    ring
  have main : ∀ i j, algebraMap K (DualNumber K) a * (u j * D i (v' j)) = TrivSqZeroExt.inl ((G * r) ^ (m ^ 2)) *
      (TrivSqZeroExt.inl (ϑ' i) + TrivSqZeroExt.inr (J' i j + c' j * ϑ' i)) := fun i j => by
    have e₁ := valR_gen_chart (eSec P.A) hr (𝟙 (Sp K)) hi hi'
    have e₂ := valR_sec_chart (snd (baseOver (Sp K)) P.A).left (m ^ 2) (t i) (epsLift (v' j)) (i := i₀) (i' := i₁)
      (by rw [epsLift_snd]; exact tan_le (hv'.1 j) k₀) (by rw [epsLift_snd]; exact tan_le (hv'.1 j) k₁)
    rw [epsLift_snd] at e₂
    have hx : epsLift (v' j) ≫ (baseOver (Sp K) ⊗ P.A).hom = spMap (algebraMap K (DualNumber K)) := Over.w _
    have e₃ := valR_cMul _ _ _ hx _ a ((t i).f fun _ => i₁)
    have e₄ := H' i j
    rw [e₁] at e₄
    exact (congrArg _ e₂).symm.trans (e₃.symm.trans ((congrArg (valR _ _) (ht i _)).symm.trans e₄))
  have hϑ : ∀ i, ϑ' i = a * ϑ i := fun i => by
    have e := congrArg TrivSqZeroExt.fst (main i ⟨0, hp⟩)
    simp only [TrivSqZeroExt.fst_mul, hu, f₁, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero, mul_pow] at e
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero (m ^ 2) hG₀) (pow_ne_zero (m ^ 2) hr₀)) ?_
    linear_combination -e
  refine ⟨hϑ, fun j => a * (∑ l, M j l * c l + (u j).snd / G ^ (m ^ 2) - c' j), fun i j => ?_⟩
  have e := congrArg TrivSqZeroExt.snd (main i j)
  simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mul, hu, f₁, f₂, hϑ, TrivSqZeroExt.algebraMap_eq_inl,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inr, zero_add, zero_mul,
    add_zero, mul_pow] at e
  have hG₁ := pow_ne_zero (m ^ 2) hG₀
  refine mul_left_cancel₀ (mul_ne_zero hG₁ (pow_ne_zero (m ^ 2) hr₀)) ?_
  linear_combination -e - r ^ (m ^ 2) * a * ϑ i * div_mul_cancel₀ (u j).snd hG₁

end GlobalTheory.MBLow.JetUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_jets_change_section_basis : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (hp rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → ∀ (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ P.A)) (ϑ ϑ' : I → K) (J J' : I → Fin P.g → K), ThJet ⟨P, hp, rig, hr, th, hth, v, hv⟩ rfl m pt ϑ J → ThJet ⟨P, hp, rig, hr, th', hth', v', hv'⟩ rfl m pt ϑ' J' → (∀ i, ϑ' i = a * ϑ i) ∧ ∃ c : Fin P.g → K, ∀ i j, J' i j = a * ∑ l, M j l * J i l + c j * ϑ i := by
  first | exact @GlobalTheory.MBLow.JetUniq.thJet_change | exact GlobalTheory.MBLow.JetUniq.thJet_change | (intros; apply GlobalTheory.MBLow.JetUniq.thJet_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTuple
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceFlatLevel

open GlobalTheory.TraceLevelPf

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem traceLevel_flat (R : RealDat D A Ks) (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)) (hB : B.Good) (hBo : BaseOf R i B)
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c))
    (hU : ∀ g, e g ∈ B.G.P.H ↔ g ∈ U)
    (hchi : ∀ (u : U) (hu : e u ∈ B.G.P.H), ((B.G.P.chi ⟨e u, hu⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ u : D.what₂.LLˣ) : D.what₂.LL))
    (τ : Twist D Circle) (hτ : τ.Good) (hQ : B.admitted τ.Q) (ω : PairRep (Vc D i) (Wc D i)) (hω : B.IsWeil τ.chi ω)
    (hh : GA D (Vc D i)) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    levelTrace R i U ψ (series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P) = series B.F ω (B.vecFlat τ) hh P := by
  classical
  have hW : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) _ _ ω := hω
  have hlift := fun g => exists_lift_datWp hB hBo e hent g
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  have hQ' : (GlobalTheory.FlatVecSum.princ B).admitted τ.Q := hQ
  have hfθ : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
      (Base.isThetaAt_vecAt (GlobalTheory.FlatVecSum.princ_good hB) hQ' _) hB.frame.vac.2.theta
  have hsum : B.vecFlat τ = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) •
      ω (1, (hlift (e.symm p)).choose) ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) :=
    GlobalTheory.FlatVecSum.vecFlat_eq_sum_princ hB (D.sp.V_sig _) hτ hQ hω (fun p => (hlift (e.symm p)).choose) (fun p => by
      have := lifts_of_datWp hBo e hent (hlift (e.symm p)).choose_spec
      rwa [MulEquiv.apply_symm_apply] at this)
  funext x
  have hL : levelTrace R i U ψ (series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P) x =
      ∑ g, (if hg : g ∈ U then D.what₂.embLL (((ψ ⟨g, hg⟩)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0) *
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P (x * (hlift g).choose) := by
    unfold levelTrace gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    show Lev.actG0 _ _ _ _ _ x = _
    rw [Lev.actG0]
    split_ifs with hk
    · rw [GlobalTheory.CuspMult.EqCut.levChi_flag rfl rfl, inv_one]
      exact one_mul _
    · exact absurd (hlift g) hk
  have hR : series B.F ω (B.vecFlat τ) hh P x = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) *
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P (x * (hlift (e.symm p)).choose) := by
    rw [hsum, GlobalTheory.SpecFac.series_sum hB ω _ _ _ (fun p _ => hW.om_pres _ _ hfθ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [series_om_fin hB hW hfθ hh P x (hlift (e.symm p)).choose_spec.1]
  rw [hL, hR]
  symm
  refine Fintype.sum_of_injective (fun p : B.G.P.H => e.symm p) (fun p q hpq => Subtype.ext (e.symm.injective hpq)) _ _
    (fun g hg => ?_) (fun p => ?_)
  · rw [dite_eq_right, zero_mul]
    intro hgU
    exact hg ⟨⟨e g, (hU g).2 hgU⟩, e.symm_apply_apply g⟩
  · have hp : e.symm p ∈ U := (hU _).1 (by rw [MulEquiv.apply_symm_apply]; exact p.2)
    have key : ((B.G.P.chi p : ℂˣ) : ℂ) = D.what₂.embLL ((ψ ⟨e.symm p, hp⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have hp' : e (e.symm p) ∈ B.G.P.H := by rw [MulEquiv.apply_symm_apply]; exact p.2
      have := hchi ⟨e.symm p, hp⟩ hp'
      have hpe : (⟨e (e.symm p), hp'⟩ : B.G.P.H) = p := Subtype.ext (e.apply_symm_apply p)
      rw [hpe] at this
      exact this
    rw [dite_eq_left hp, Units.val_inv_eq_inv_val, key, Units.val_inv_eq_inv_val, map_inv₀]

end GlobalTheory.TraceFlatLevel

namespace GlobalTheory.BigOn.Exp.TupLe

end GlobalTheory.BigOn.Exp.TupLe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoeffInfinitePlacesWeightRep
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAutRepOfVecFun
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AutRec

theorem continuous_coord_emb {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    Continuous (coord (E := E) τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

theorem continuous_cEmb_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) :
    Continuous (cEmb (E := E) (n := n) τ) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_coord_emb τ))).comp GlobalTheory.DefU.continuous_cInf

end GlobalTheory.AutRec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoeffInfinitePlacesWeightRep
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem continuous_coef_piTensorMap {X ι : Type} [TopologicalSpace X] [Fintype ι] {M : ι → Type}
    [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)] [∀ c, Module.Finite ℂ (M c)]
    (f : X → ∀ c, M c →ₗ[ℂ] M c)
    (hf : ∀ c (x : M c) (ℓ : Module.Dual ℂ (M c)), Continuous fun g => ℓ (f g c x))
    (u : PiTensorProduct ℂ M) (ℓ : Module.Dual ℂ (PiTensorProduct ℂ M)) :
    Continuous fun g => ℓ (PiTensorProduct.map (f g) u) := by
  classical
  let bc := fun c => Module.Free.chooseBasis ℂ (M c)
  let B := Basis.piTensorProduct bc
  have key : ∀ k k', Continuous fun g => B.repr (PiTensorProduct.map (f g) (B k)) k' := by
    intro k k'
    simp only [B, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
    exact continuous_finsetProd _ fun c _ => by
      simpa [Module.Basis.coord_apply] using hf c (bc c (k c)) ((bc c).coord (k' c))
  have h : ∀ g, ℓ (PiTensorProduct.map (f g) u) =
      ∑ k, ∑ k', B.repr u k * (B.repr (PiTensorProduct.map (f g) (B k)) k' * ℓ (B k')) := by
    intro g
    conv_lhs => rw [← B.sum_repr u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [← B.sum_repr (PiTensorProduct.map (f g) (B k))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  simp_rw [h]
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun k' _ =>
    continuous_const.mul ((key k k').mul continuous_const)

theorem continuous_coef_sqRep (n : ℕ) (mu : DomWeight n) (x : nablaSq ℂ n mu) (ℓ : Module.Dual ℂ (nablaSq ℂ n mu)) :
    Continuous fun a : GL (Fin n) ℂ => ℓ (GlobalTheory.Branching.sqRep ℂ n mu a x) := by
  obtain ⟨P, hP⟩ := GlobalTheory.Branching.exists_coef_sqRep n mu x ℓ
  simp only [hP]
  exact (Units.continuous_val.matrix_det.zpow₀ _
      fun a : GL (Fin n) ℂ => Or.inl (Matrix.GeneralLinearGroup.det a).ne_zero).mul
    ((MvPolynomial.continuous_eval P).comp (continuous_pi fun i => Units.continuous_val.matrix_elem i.1 i.2))

theorem continuous_coef_wInf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n) (u : Wsp lam) (ℓ : Module.Dual ℂ (Wsp lam)),
    Continuous fun g : UA E n => ℓ (wInf lam g u) := by
  intro E _ _ _ n lam u ℓ
  exact continuous_coef_piTensorMap
    (fun g v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding g))
    (fun v x ℓ' => (continuous_coef_sqRep n (lam v) x ℓ').comp (GlobalTheory.AutRec.continuous_cEmb_emb _)) u ℓ

end GlobalTheory.BCT.TrKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoeffInfinitePlacesWeightRepStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_matrixCoeff_infinitePlacesWeightRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (u : Wsp lam) (ℓ : Module.Dual ℂ (Wsp lam)), Continuous fun g : UA E n => ℓ (wInf lam g u) := by
  first | exact @GlobalTheory.BCT.TrKer.continuous_coef_wInf | exact GlobalTheory.BCT.TrKer.continuous_coef_wInf | (intros; apply GlobalTheory.BCT.TrKer.continuous_coef_wInf <;> assumption)
end
end
