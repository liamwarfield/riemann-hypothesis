module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEight
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode
open AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory Limits IsLocalRing

namespace GlobalTheory.ThetaNormal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Models
open scoped CategoryTheory.Obj

theorem exists_theta_of_flat {X : Scheme.{0}} {G : Over X} [GrpObj G] (hG : IsSemiAbelian G) {L : LB G.left}
    (hL : L.IsLB) (x : X) {R : Type} [CommRing R] [IsLocalRing R] (ψ : X.presheaf.stalk x →+* R) (hψ : ψ.Flat)
    [IsLocalHom ψ] {G' : Over (Sp R)} {φ : G'.left ⟶ G.left}
    (hφ : IsPullback φ G'.hom G.hom (spMap ψ ≫ X.fromSpecStalk x)) {L' : LB G'.left} (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull φ)) (hθ : LN.ThetaNZ G' L') :
    ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V),
      ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i) := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  let ι := pullback.fst G.hom hU.fromSpec
  let f := pullback.snd G.hom hU.fromSpec
  let gm : Γ(X, U) →+* R := ψ.comp (X.presheaf.germ U x hx).hom
  have hξ : spMap gm ≫ hU.fromSpec = spMap ψ ≫ X.fromSpecStalk x := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
    show Spec.map (CommRingCat.ofHom (X.presheaf.germ U x hx).hom ≫ CommRingCat.ofHom ψ) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    rfl
  let π : G'.left ⟶ pullback G.hom hU.fromSpec := pullback.lift φ (G'.hom ≫ spMap gm)
    (by rw [Category.assoc, hξ, hφ.w])
  have hπ : π ≫ ι = φ := pullback.lift_fst _ _ _
  have hP : IsPullback π G'.hom f (spMap gm) :=
    IsPullback.of_right (by rw [hπ, hξ]; exact hφ) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have : CompactSpace (pullback G.hom hU.fromSpec : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace (pullback G.hom hU.fromSpec : Scheme.{0}) := quasiSeparatedSpace_of_quasiSeparated f
  have hflat : gm.Flat := by
    have h₀ : (X.presheaf.germ U x hx).hom.Flat := by
      letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
      have := hU.isLocalization_stalk ⟨x, hx⟩
      exact RingHom.flat_algebraMap_iff.2
        (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    exact RingHom.Flat.comp h₀ hψ
  have hM := pull_isLB hL ι
  obtain ⟨w, hw'⟩ : LBIso ((L.pull ι).pull π) (L'.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullLinComb L ι (fun _ : PUnit => π) (fun _ => φ) (fun _ => 1) (𝟙 _)
      fun _ => hπ.trans (Category.id_comp _).symm) (Geo.Tor.chartPullPull L' _ _ rfl) hw.symm
  obtain ⟨θ', hθ'⟩ := hθ
  obtain ⟨σ, hσ⟩ := ThetaLocal.exists_sec_pull hL' (pull_isLB hM π) (𝟙 _) w hw' (O := ⊤) le_top _
    (SecSpread.res_mem_secOn θ' ⊤)
  obtain ⟨z, i, hz, hi⟩ := hθ' (IsLocalRing.closedPoint _)
  obtain ⟨k, hk⟩ := hσ z i ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, G'.left.basicOpen_le _ hi⟩, hi⟩)
  obtain ⟨k, rfl⟩ : ∃ j, k = fun _ => j := ⟨k PUnit.unit, rfl⟩
  have hk₁ := G'.left.basicOpen_le _ hk
  have hk₂ : π z ∈ (L.pull ι).U k := mem_pull.1 hk₁
  obtain ⟨n, a, u, hu⟩ := FlatSec.exists_comb_of_flat _ _ gm hflat _ f _ π G'.hom hP _ hM σ
  obtain ⟨j, hj⟩ : ∃ j, π z ∈ Scheme.basicOpen _ ((u j).f k) := by
    by_contra hn
    have h₁ := (AbLocusPull.isUnit_gs_iff (𝟙 _) z _ hk₁ _).2 hk
    rw [hu z k hk₂] at h₁
    refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_) h₁
    exact fun h₂ => hn ⟨j, (AbLocusPull.isUnit_gs_iff π z _ hk₂ _).1 h₂⟩
  let V : X.Opens := ⟨(ι ≫ G.hom) '' Scheme.basicOpen _ ((u j).f k),
    (ι ≫ G.hom).isOpenMap _ (Scheme.basicOpen _ ((u j).f k)).isOpen⟩
  have hr : G.hom ⁻¹ᵁ V ≤ ι.opensRange := by
    rintro g ⟨y, -, e⟩
    obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback G.hom hU.fromSpec) g (f y)
      (e.symm.trans (congrArg (fun r : pullback G.hom hU.fromSpec ⟶ X => r y) pullback.condition))
    exact ⟨q, hq⟩
  obtain ⟨θ, hθ, hb⟩ := ThetaLocal.exists_secOn_push hL hM (lbIso_refl hM) hr le_top
    (SecSpread.res_mem_secOn (u j) ⊤)
  refine ⟨V, ⟨π z, hj, ?_⟩, θ, hθ, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Category.assoc, hπ, hφ.w, Scheme.Hom.comp_apply, hz]
    show X.fromSpecStalk x (spMap ψ (IsLocalRing.closedPoint R)) = x
    have hc : spMap ψ (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint _ := IsLocalRing.comap_closedPoint ψ
    rw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨i', hi'⟩ := exists_chart hL (ι y)
    exact ⟨ι y, i', rfl, hb y ⟨y, hy, rfl⟩ i' k hi'
      ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, Scheme.basicOpen_le _ _ hy⟩, hy⟩)⟩

theorem hasTheta_of_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L := by
  intro E _ _ _ H Dw _ l Xo c Y hsm x
  have : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  haveI hAr : IsRegularRing (Y.X.presheaf.stalk x) :=
    ExtendRig.isRegularRing_stalk isRegularRing_of_smooth c.F Y.s x
  haveI : IsRegularLocalRing (Y.X.presheaf.stalk x) :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) :=
    RegularCompletion.isRegularLocalRing_adicCompletion _
  obtain ⟨hdC, hnC⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))

  haveI hκ : CharZero (Y.X.residueField x) := by
    let φ : c.F →+* Y.X.residueField x := (Y.X.evaluation ⊤ x trivial).hom.comp (GlobalTheory.QCoh.structureRingHom Y.s)
    exact charZero_of_injective_ringHom φ.injective
  obtain ⟨k, _, _, hk, S', hS'⟩ := CoveringCompare.exists_finite_splitOver Y.t.G Y.t.semi x

  haveI : Algebra.IsSeparable (Y.X.residueField x) k := inferInstance
  obtain ⟨R, _, _, _, _, j, _, _, hj⟩ := LocM.Bdy.exists_etale_local
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (Y.X.residueField x) k
    (ResidueField.map (algebraMap (Y.X.presheaf.stalk x)
      (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))))
  have : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalization.self fun a ha => by_contra fun h => ha h
  obtain ⟨hd, hn⟩ := isDomain_and_isIntegrallyClosed_atPrime_of_etale
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (maximalIdeal R) R
  have hNR : IsNoetherianRing R :=
    IsNoetherianRing.of_finite (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R
  have f₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.X.presheaf.stalk x)
    (B := AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))
  have f₂ := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (B := R)
  let ψ : Y.X.presheaf.stalk x →+* R := (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x))
    (Y.X.presheaf.stalk x)) R).comp (algebraMap (Y.X.presheaf.stalk x) (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)))
  have hinj : Function.Injective ψ :=
    (FaithfulSMul.algebraMap_injective _ _).comp (FaithfulSMul.algebraMap_injective _ _)
  haveI : CharZero (ResidueField (Y.X.presheaf.stalk x)) := hκ
  haveI : CharZero (Y.X.presheaf.stalk x) := RingHom.charZero (residue (Y.X.presheaf.stalk x))
  haveI : CharZero R := charZero_of_injective_ringHom hinj
  have hadm := isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hNR hn hc
  have hψf : ψ.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance)
    (RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : IsLocalHom ψ := inferInstance

  obtain ⟨t, ⟨m⟩⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sab (spMap ψ ≫ Y.X.fromSpecStalk x) Y.t
  haveI : IsProper Y.s := ProperFamily.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  haveI : IsNoetherian Y.X := {}
  have hjo := GenFan.Tri.isOpenImmersion_j_id Y
  have hopen : IsOpen (Set.range Y.j) := Y.j.isOpenEmbedding.isOpen_range
  have hdense : Dense (Set.range Y.j) := by
    have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
      have : IsIso (spMap (RingHom.id c.F)) := by
        show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
        rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
        infer_instance
      infer_instance
    have e : Set.range Y.j = (pullback.fst Y.s (spMap (RingHom.id c.F))) '' Set.range Y.jQ := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨Y.jQ w, ⟨w, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
      · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
        exact ⟨w, Scheme.Hom.comp_apply _ _ _⟩
    rw [e]
    exact ((pullback.fst Y.s (spMap (RingHom.id c.F))).surjective.denseRange).dense_image
      (pullback.fst Y.s (spMap (RingHom.id c.F))).continuous Y.jQ_dense
  let ξ : Sp R := (⊥ : PrimeSpectrum R)
  have hgen : (spMap ψ ≫ Y.X.fromSpecStalk x) ξ ∈ Set.range Y.j :=
    LocM.SharedLaws.mem_of_maximal (fun y hy => LocM.Bdy.generic_image x ψ hinj ξ rfl y hy) hopen hdense
  have hr : Set.range (jK R ≫ spMap ψ ≫ Y.X.fromSpecStalk x) ⊆ Set.range Y.j := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact LN.GenericPoint.jK_mem (U := (spMap ψ ≫ Y.X.fromSpecStalk x) ⁻¹' Set.range Y.j)
      (hopen.preimage (Scheme.Hom.continuous _)) ⟨ξ, hgen⟩ q
  have hpol : LN.PolAt t (jK R) :=
    GoodTrait.polAt_of_point Y m (jK R) (IsOpenImmersion.lift Y.j _ hr) (IsOpenImmersion.lift_fac _ _ _)
  have h₁ := LocM.Bdy.residue_comp (R := R) x
  have e : spMap (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R) ≫
      fromSpecCompletedStalk Y.X x = spMap ψ ≫ Y.X.fromSpecStalk x := by
    rw [spMap_comp, Category.assoc]; rfl
  have h₂ : spMap j ≫ spMap (algebraMap (Y.X.residueField x) k) =
      spMap ((ResidueField.map (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x))
        (Y.X.presheaf.stalk x)) R)).comp (ResidueField.map (algebraMap (Y.X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))))) :=
    (spMap_comp _ _).symm.trans (congrArg spMap hj)
  obtain ⟨S₁, hS₁⟩ := LocM.Bdy.split_pull _ hS' j (ι := spMap ψ ≫ Y.X.fromSpecStalk x) (by
    rw [← Category.assoc]
    refine (congrArg (· ≫ Y.X.fromSpecResidueField x) h₂).trans ?_
    exact h₁.trans (congrArg (spMap (residue R) ≫ ·) e)) m
  have hsplit : LN.SplitOver t.G (maximalIdeal R) := ⟨S₁, hS₁⟩
  have hθ := thetaNZ_of_polAt E H R hadm t hpol hsplit
  exact exists_theta_of_flat Y.t.semi Y.t.PP.isLB x ψ hψf m.cart.1 t.PP.isLB (m.lin.imp fun _ h => h.1) hθ

end GlobalTheory.ThetaNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothModeStatement
open AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFibrewiseNonvanishingThetaSection_of_smooth_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L := by
  first | exact @GlobalTheory.ThetaNormal.hasTheta_of_smooth | exact GlobalTheory.ThetaNormal.hasTheta_of_smooth | (intros; apply GlobalTheory.ThetaNormal.hasTheta_of_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain
open NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links (PolF labLL)
open Formalism.L2.Host (embLL0)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallSpan

variable {D : D7} {m n : ℕ}


open GlobalTheory.ExportSeries.Onto in
theorem exists_harm (w : GlobalTheory.ExportSeries.Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) (F : VV ℂ w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n) := by
  obtain ⟨s, hs⟩ := GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  have hle : (VV ℂ w.lam).map (coefLin w.lam) ≤ (harm m w B).map (harmFn m w B) := by
    rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle (Submodule.mem_map_of_mem F.2)


open GlobalTheory.ExportSeries.HarmLattice in
theorem harmLat_le_span {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] (f : K₀ →+* K) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K₀)) (O O' : Subring ℂ) (hO' : ∀ a : 𝓞 K, σ a ∈ O') (w : GlobalTheory.ExportSeries.Weight D n) (B : GLR D n)
    (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hM : Submodule.IsFullLattice D.host.E M) {P : PolF D m n} (hP : P ∈ harmLat σ (fun τ => f.comp (emb τ)) O' m w B M) :
    P ∈ Submodule.span O' (harmLat (σ.comp f) emb O m w B M : Set (PolF D m n)) := by
  set N := Submodule.span O' (harmLat (σ.comp f) emb O m w B M : Set (PolF D m n))
  have hN : N ≤ (harm m w B).restrictScalars O' := Submodule.span_le.2 fun Q hQ => hQ.1
  have hle : coefLatFn σ (fun τ => f.comp (emb τ)) O' w.lam M ≤ N.map ((harmFn m w B).restrictScalars O') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    have hF' := GlobalTheory.NabBC.nabBaseChange _ _ _ _ n f emb w.lam M hM hF
    rw [coefFn_eq, SetLike.mem_coe]
    clear hF
    induction hF' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, e⟩ := hy
      obtain ⟨Q, hQ, eQ⟩ := exists_harm w B hw hm (GlobalTheory.CoefModel.mapVV (σ.comp f) w.lam x)
      have e1 : harmFn m w B Q = coefFn (σ.comp f) w.lam (x : Pol K₀ D.what₂.Tau n) := eQ.trans (coefFn_eq _ _ x).symm
      refine ⟨Q, Submodule.subset_span ⟨hQ, ?_⟩, ?_⟩
      · exact Submodule.subset_span ⟨x, hx, e1⟩
      · refine eQ.trans (congrArg (cf w.lam) (Subtype.ext ?_))
        change MvPolynomial.map (σ.comp f) x.1 = MvPolynomial.map σ y.1
        rw [e, MvPolynomial.map_map]
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
    | smul a F _ h1 =>
      rw [← algebraMap_smul K a F, LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hO' a⟩ : O') h1
  obtain ⟨Q, hQ, e⟩ := hle hP.2
  have h0 : P - Q = 0 := GlobalTheory.ExportSeries.HarmInj.harm_inj D m n w B hw hm _ (sub_mem hP.1 (hN hQ)) (by
    rw [map_sub, sub_eq_zero]
    exact e.symm)
  rw [sub_eq_zero.1 h0]
  exact hQ

theorem isLattice_latAt {S T : HSp D} {B : Base S T} (hF : B.F.Good) (h : Bridge.Gf S) :
    Submodule.IsFullLattice D.host.E (B.latAt h) :=
  by
  classical
  have hspan : Submodule.span D.host.E (B.F.ΛS : Set (Fin S.rank → D.host.E)) = ⊤ := by
    let W := Submodule.span D.host.E (B.F.ΛS : Set (Fin S.rank → D.host.E))
    change W = ⊤
    by_contra hW
    let g : (Fin S.rank → D.host.E) →ₗ[D.host.E] Module.Dual D.host.E W :=
      { toFun := fun x => { toFun := fun y => ∑ i, ∑ j, x i * S.gram i j * y.1 j
                            map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
                            map_smul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
        map_add' := by intros; ext y; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := by intros; ext y; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E (Fin S.rank → D.host.E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let v : Fin S.rank → D.host.E := fun i => star (x i)
    have hv0 : v ≠ 0 := by
      intro hv
      apply hx0
      funext i
      have hi := congrFun hv i
      simpa [v] using congrArg star hi
    have hline (r : D.host.E) : r • v ∈ B.F.ΛS := by
      apply (hF.sdS.2 _).2
      intro y hy
      have hz : (∑ i, ∑ j, x i * S.gram i j * y j) = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      have hzy : (∑ i, ∑ j, star (y i) * S.gram i j * v j) = 0 := by
        have hg (i j : Fin S.rank) : star (S.gram i j) = S.gram j i := by
          exact S.herm.eq _ _
        have hs : (starRingEnd D.host.E) (∑ i, ∑ j, x i * S.gram i j * y j) = 0 := by rw [hz, map_zero]
        simp only [map_sum, map_mul] at hs
        change (∑ i, ∑ j, star (x i) * star (S.gram i j) * star (y j)) = 0 at hs
        simp only [hg] at hs
        rw [Finset.sum_comm] at hs
        simpa [mul_comm, mul_left_comm, mul_assoc] using hs
      refine ⟨0, ?_⟩
      simp only [map_zero, Pi.smul_apply, smul_eq_mul]
      calc
        0 = r * (∑ i, ∑ j, star (y i) * S.gram i j * v j) := by rw [hzy, mul_zero]
        _ = ∑ i, ∑ j, star (y i) * S.gram i j * (r * v j) := by simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hn
      apply hv0
      funext i
      simpa using not_exists.mp hn i
    let coord := (LinearMap.proj i : (Fin S.rank → D.host.E) →ₗ[D.host.E] D.host.E).restrictScalars (𝓞 D.host.E)
    have htop : B.F.ΛS.map coord = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact ⟨(a / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
    have : Module.Finite (𝓞 D.host.E) D.host.E := Module.finite_def.mpr (htop ▸ hF.sdS.1.fg.map coord)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  exact Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hF.sdS.1.fg) hspan _

end GlobalTheory.SmallSpan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem spMap_comp' {A B K : Type} [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) :
    spMap (h.comp f) = spMap h ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eSec_hom' {S : Scheme.{0}} (G : Over S) [GrpObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  simpa [eSec] using Over.w η[G]

theorem gs_appLE' {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (r : Z ⟶ Y) (p : Z) (U : X.Opens) (V : Y.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (hp : r p ∈ V) (a : Γ(X, U)) : gs r p V ((φ.appLE U V e).hom a) = gs (r ≫ φ) p U a := by
  rw [← gs_pull r φ p U (e hp) a, ← gs_res r p e hp]
  rfl

theorem dualMap_alg {B K : Type} [CommRing B] [CommRing K] (h : B →+* K) (a : B) :
    GlobalTheory.MBLow.dualMap h (algebraMap B _ a) = algebraMap K _ (h a) := by
  ext <;> simp [GlobalTheory.MBLow.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_eps {B K : Type} [CommRing B] [CommRing K] (h : B →+* K) :
    GlobalTheory.MBLow.dualMap h DualNumber.eps = DualNumber.eps := by
  ext <;> simp [GlobalTheory.MBLow.dualMap]

theorem dual_decomp {A : Type} [CommRing A] (z : DualNumber A) :
    z = algebraMap A _ z.fst + algebraMap A _ z.snd * DualNumber.eps := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem ringHom_dual_ext {A K : Type} [CommRing A] [CommRing K] (F G : DualNumber A →+* K)
    (h1 : ∀ a, F (algebraMap A _ a) = G (algebraMap A _ a)) (h2 : F DualNumber.eps = G DualNumber.eps) : F = G := by
  refine DFunLike.ext _ _ fun z => ?_
  rw [dual_decomp z, map_add (f := _), map_add (f := _), map_mul, map_mul, h1, h1, h2]

end GlobalTheory.KeyEven

namespace GlobalTheory.KeyEven

theorem keyPB_of_keyOn_comp : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K)
    (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G))
    (x : KeyIn B) (x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g),
    KeyOn f x G L σ (fun i => y (i.cast hg)) → KeyOn (h.comp f) x' G L σ (fun i => y (i.cast hg')) → KeyPB x' x h := by
  intro A B K _ _ _ f h G _ _ L σ g y x x' hg hg' H H'
  obtain ⟨φ, he, ψ, F, hpb, hψ, hrig, hsec, hF1, hF2, hv⟩ := H
  obtain ⟨φ', he', ψ', F', hpb', hψ', hrig', hsec', hF1', hF2', hv'⟩ := H'
  have hc : spMap (h.comp f) = spMap h ≫ spMap f := spMap_comp' f h
  obtain ⟨φ₁, h1, h2⟩ : ∃ φ₁ : x'.P.A.left ⟶ x.P.A.left, φ₁ ≫ φ = φ' ∧ φ₁ ≫ x.P.A.hom = x'.P.A.hom ≫ spMap h :=
    ⟨hpb.1.lift φ' (x'.P.A.hom ≫ spMap h) (by rw [hpb'.1.w, hc, Category.assoc]), hpb.1.lift_fst _ _ _,
      hpb.1.lift_snd _ _ _⟩
  subst h1
  have gp : IsGrpPullback x'.P.A x.P.A (spMap h) φ₁ := IsGrpPullback.cancel hpb (hpb'.congr hc rfl) h2
  have he₁ : eSec x'.P.A ≫ φ₁ = spMap h ≫ eSec x.P.A := by
    apply hpb.1.hom_ext
    · rw [Category.assoc, he', Category.assoc, he, hc, Category.assoc]
    · rw [Category.assoc, h2, ← Category.assoc, eSec_hom', Category.assoc, eSec_hom']
      rfl
  have hL := L.isLB
  have hx := x.P.isLB
  have hx' := x'.P.isLB
  have pψ := (isGen_iff ψ).1 hψ
  have pψ' := (isGen_iff ψ').1 hψ'
  obtain ⟨w, T⟩ := exists_cancel hL ψ ψ' pψ pψ' hx hx'
  have hg₁ : x'.P.g = x.P.g := hg'.trans hg.symm
  refine ⟨φ₁, he₁, w, hg₁, GlobalTheory.MBLow.dualMap h, gp, (isGen_iff w).2 (T.pgen_cancel hL pψ pψ'), ?_, ?_,
    dualMap_alg h, dualMap_eps h, ?_⟩
  ·
    have H := (maps_iff ψ _ (fun _ => eSec G) _ x.rig L.rig (spMap f) _ (rigPull_le φ (spMap f) he L.L)
      (fun _ => rfl)).1 hrig
    have H'' := (maps_iff ψ' _ (fun _ => eSec G) _ x'.rig L.rig (spMap (h.comp f)) _
      (rigPull_le (φ₁ ≫ φ) (spMap (h.comp f)) he' L.L) (fun _ => rfl)).1 hrig'
    rw [hc] at H''
    exact (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap h) _ (rigPull_le φ₁ (spMap h) he₁ x.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel hL (fun _ => he₁) H H'')
  ·
    intro j i hle
    apply fn_ext
    intro p hp
    obtain ⟨c, hcp⟩ := exists_chart hL (φ (φ₁ p))
    have hk : φ₁ p ∈ x.P.L.U (j PUnit.unit) := hle hp
    have le₀ : (L.L.pull φ).U (fun _ => c) ⊓ x.P.L.U (j PUnit.unit) ≤ φ ⁻¹ᵁ L.L.U c := fun q hq => mem_pull.1 hq.1
    have m₀ : φ₁ p ∈ (L.L.pull φ).U (fun _ => c) ⊓ x.P.L.U (j PUnit.unit) := ⟨mem_pull.2 hcp, hk⟩
    have e₀ := congrArg (gs φ₁ p _) (hsec (fun _ => c) (j PUnit.unit) le₀)
    dsimp only at e₀
    rw [gs_appLE' φ φ₁ p _ _ le₀ m₀] at e₀
    erw [gs_mul φ₁ p _ m₀] at e₀
    erw [gs_unit φ₁ p _ m₀, gs_res φ₁ p _ m₀] at e₀
    have le₁ : ((L.L.pull (φ₁ ≫ φ)).U (fun _ => c)) ⊓ x'.P.L.U i ≤ (φ₁ ≫ φ) ⁻¹ᵁ L.L.U c :=
      fun q hq => mem_pull.1 hq.1
    have m₁ : (𝟙 x'.P.A.left) p ∈ (L.L.pull (φ₁ ≫ φ)).U (fun _ => c) ⊓ x'.P.L.U i := ⟨mem_pull.2 hcp, hp.2⟩
    have e₁ := congrArg (gs (𝟙 _) p _) (hsec' (fun _ => c) i le₁)
    dsimp only at e₁
    rw [gs_appLE' (φ₁ ≫ φ) (𝟙 _) p _ _ le₁ m₁] at e₁
    erw [gs_mul (𝟙 _) p _ m₁] at e₁
    erw [gs_unit (𝟙 _) p _ m₁, gs_res (𝟙 _) p _ m₁] at e₁
    rw [Category.id_comp] at e₁
    have tri := T (x'.P.A.left) (𝟙 _) p c (j PUnit.unit) i hcp hk hp.2
    rw [gs_appLE' φ₁ (𝟙 _) p _ _ hle hp, Category.id_comp]
    erw [gs_mul (𝟙 _) p _ hp]
    erw [gs_unit (𝟙 _) p _ hp, gs_res (𝟙 _) p _ hp]
    change gs φ₁ p _ _ = (gw w (𝟙 _) p (j PUnit.unit) i).val * _
    have e₂ : (gw ψ' (𝟙 _) p c i).val * gs (𝟙 _) p (x'.P.L.U i) (x'.th.f i) =
        (gw ψ φ₁ p c (j PUnit.unit)).val * gs φ₁ p (x.P.L.U (j PUnit.unit)) (x.th.f (j PUnit.unit)) :=
      e₁.symm.trans e₀
    rw [tri, Category.id_comp, Units.val_mul, _root_.mul_assoc] at e₂
    exact ((Units.mul_right_inj _).1 e₂).symm
  ·
    intro i
    apply hpb.1.hom_ext
    · have a1 := hv (i.cast hg₁)
      have a2 := hv' i
      simp only at a1 a2
      rw [Category.assoc, a2, Category.assoc, a1, Fin.cast_cast, ← Category.assoc, ← spMap_comp']
      congr 2
      refine ringHom_dual_ext _ _ (fun a => ?_) ?_
      · simp only [RingHom.comp_apply, hF1, hF1', dualMap_alg]
      · simp only [RingHom.comp_apply, hF2, hF2', dualMap_eps]
    · rw [Category.assoc, h2, ← Category.assoc, Over.w (x'.v i), Category.assoc, Over.w (x.v _)]
      show spMap (algebraMap K (DualNumber K)) ≫ spMap h = spMap (GlobalTheory.MBLow.dualMap h) ≫ spMap (algebraMap B (DualNumber B))
      rw [← spMap_comp', ← spMap_comp']
      congr 1
      exact RingHom.ext fun a => (dualMap_alg h a).symm

end GlobalTheory.KeyEven
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyDatum_fibre_of_composable_baseChange : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G)) (x : KeyIn B) (x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g), KeyOn f x G L σ (fun i => y (i.cast hg)) → KeyOn (h.comp f) x' G L σ (fun i => y (i.cast hg')) → KeyPB x' x h := by
  first | exact @GlobalTheory.KeyEven.keyPB_of_keyOn_comp | exact GlobalTheory.KeyEven.keyPB_of_keyOn_comp | (intros; apply GlobalTheory.KeyEven.keyPB_of_keyOn_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSecOfMemCuspWWtZ
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackMemCuspFormSupLatticeIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackMemCuspFormSupLatticeIff
noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CovTop.PullLat

variable {D : D7}

theorem levPull_of_pull {T : Core D} {j : ℕ} (Y : Deep T j) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : T.R j}
    (hf : f ∈ sec (T.Q.Xo j) T.Q.c a n) {g : Rul Y.d.Xo₂ Y.d.c₂} (hp : Y.Pull f g) :
    GlobalTheory.LevPull.Pull Y.d (GlobalTheory.FieldBC.rulBC Y.hle f) g := by
  intro k _ _ _ _ hk y₂ y hov
  letI : Algebra T.Q.c.F k := GlobalTheory.FieldBC.resAlg Y.hle k
  have ho : AlgOver T.Q.c Y.c' Y.hle k := fun _ => rfl
  rw [((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ _ _ _ Y.hle).1 a n f hf).2 k ho y]
  exact hp k ho hk y₂ y (y.res Y.hle ho) hov rfl rfl HEq.rfl

theorem pull_mem_latW : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j →
    Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))
      (g : Y.V (wtZ a n)), Y.Pull f g → (g ∈ latW Y.U (wtZ a n) ↔ f ∈ latW (T.U j) (wtZ a n)) := by
  intro D T j Y e o hT hj hY a n f g hp
  have hpos := GlobalTheory.CovTop.Inhab.rank_pos T.toCore hT.pins j hj
  have hfs : (f : T.R j) ∈ sec (T.Q.Xo j) T.Q.c a n := by
    have h : (f : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) a n := by rw [← cuspW_wtZ]; exact f.2
    exact cusp_le_sec _ _ _ _ _ h
  have hgs : (g : Rul Y.d.Xo₂ Y.d.c₂) ∈ sec Y.d.Xo₂ Y.d.c₂ a n := by
    have h : (g : Rul Y.d.Xo₂ Y.d.c₂) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by rw [← cuspW_wtZ]; exact g.2
    exact cusp_le_sec _ _ _ _ _ h
  have hfs' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (T.Q.Xo j) _ _ Y.hle).1 a n _ hfs).1
  have hL := GlobalTheory.LevGeo.laws_core D T j hT hj
  have hne : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  have h1 := GlobalTheory.CoverInt.pull_intAt_iff _ _ _ _ _ _ Y.d hpos hY.lev.1 (Or.inl ⟨hne, hL.levA⟩) a n _ hfs' _ hgs (levPull_of_pull Y hfs hp)
  have h2 := GlobalTheory.T.isIntegralRule_ruleBaseChangeCoeffField_iff _ _ _ _ _ _ _ Y.hle a n _ hfs
  exact h1.trans h2

end GlobalTheory.CovTop.PullLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackMemCuspFormSupLatticeIffStatement
open NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_mem_cuspFormSupLattice_iff : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)) (g : Y.V (wtZ a n)), Y.Pull f g → (g ∈ latW Y.U (wtZ a n) ↔ f ∈ latW (T.U j) (wtZ a n)) := by
  first | exact @GlobalTheory.CovTop.PullLat.pull_mem_latW | exact GlobalTheory.CovTop.PullLat.pull_mem_latW | (intros; apply GlobalTheory.CovTop.PullLat.pull_mem_latW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramedPointRestrictCoefficientField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramedPointRestrictCoefficientField
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.RefSum

open AlgebraicGeometry CategoryTheory

theorem intFr_res_down : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (c' : Coeff l) (hle : c.F ≤ c'.F) (T : CDVR) (io' : c'.F →+* T.Fr) (y' : IntFr Xo c' T io'), y'.IsAlg → ∃ y : IntFr Xo c T (io'.comp (IntermediateField.inclusion hle).toRingHom), y.IsAlg ∧ (∀ φ : ℝ, HasPhi y' φ → HasPhi y φ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evI y' (GlobalTheory.FieldBC.rulBC hle f) = evI y f := by
  intro E _ _ _ H Dw l Xo c c' hle T io' y' hy
  obtain ⟨pt, rest⟩ := y'
  letI : Algebra c'.F T.Fr := io'.toAlgebra
  letI : Algebra c.F T.Fr := (io'.comp (IntermediateField.inclusion hle).toRingHom).toAlgebra
  have hover : AlgOver c c' hle T.Fr := fun _ => rfl
  refine ⟨⟨pt.res hle hover, GlobalTheory.FlagTan.fromTest_of_isLocalRing _, rest.2⟩, hy, fun φ hφ => hφ, ?_⟩
  intro a n f hf
  exact ((GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2 T.Fr hover pt

end GlobalTheory.RefSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramedPointRestrictCoefficientFieldStatement
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFramedPoint_restrict_coefficient_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (c' : Coeff l) (hle : c.F ≤ c'.F) (T : CDVR) (io' : c'.F →+* T.Fr) (y' : IntFr Xo c' T io'), y'.IsAlg → ∃ y : IntFr Xo c T (io'.comp (IntermediateField.inclusion hle).toRingHom), y.IsAlg ∧ (∀ φ : ℝ, HasPhi y' φ → HasPhi y φ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evI y' (GlobalTheory.FieldBC.rulBC hle f) = evI y f := by
  first | exact @GlobalTheory.RefSum.intFr_res_down | exact GlobalTheory.RefSum.intFr_res_down | (intros; apply GlobalTheory.RefSum.intFr_res_down <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverLaUnder
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.PlaceBelow

theorem exists_overLa_under : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (i : K →+* K') (q : ℕ) (la' : HeightOneSpectrum (𝓞 K')), q.Prime → ((q : ℕ) : 𝓞 K') ∈ la'.asIdeal → ∀ (T : CDVR) (io' : K' →+* T.Fr) (e' : ℕ), OverLa la' T.V io' e' → ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), ((q : ℕ) : 𝓞 K) ∈ la.asIdeal ∧ OverLa la T.V (io'.comp i) e := by
  intro K K' _ _ _ _ i q la' hq hmem T io' e' h
  letI : Algebra K K' := i.toAlgebra

  set la : HeightOneSpectrum (𝓞 K) := la'.under (𝓞 K) with hla
  set r : ℕ := la.asIdeal.ramificationIdx' la'.asIdeal with hr
  have hr0 : r ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la'.asIdeal la.ne_bot
  refine ⟨la, e' * r, ?_, ?_⟩
  ·
    show ((q : ℕ) : 𝓞 K) ∈ la'.asIdeal.under (𝓞 K)
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  · unfold OverLa vLa at h ⊢
    obtain ⟨he', hv⟩ := h
    refine ⟨Nat.mul_pos he' (Nat.pos_of_ne_zero hr0), fun a => ?_⟩

    have key : la.valuation K a ^ r = la'.valuation K' (algebraMap K K' a) :=
      by
        rw [hr, Ideal.ramificationIdx'_eq_ramificationIdx _ _ la.ne_bot]
        exact HeightOneSpectrum.valuation_liesOver K' la la' a
    rw [RingHom.comp_apply, hv, show i a = algebraMap K K' a from rfl, ← key, WithZero.log_pow]
    push_cast
    ring

end GlobalTheory.PlaceBelow
end

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum

theorem mem_sec_of_mem_cuspW_wtZ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ cuspW Xo c U (wtZ a n)) : f ∈ sec Xo c a n := by
  rw [cuspW_wtZ] at hf
  exact cusp_le_sec Xo c U a n hf

theorem refExp_vp_cover_le : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (cst : ℝ) (q : ℕ), q.Prime → refExp_vp Y.U cst (wtZ a n) q ≤ refExp_vp (T.U j) cst (wtZ a n) q := by
  intro D T j Y e o hJ hj hG a n hD cst q hq
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq', -⟩ := hJ.pins.2.2.2 j hj
    obtain ⟨h1, h2⟩ := hj
    have h3 := D.R.m_add_three_le_k
    rw [hp, hq']
    simp only [Ranks.sigW]
    omega
  have hne : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    obtain ⟨hp, hq', -⟩ := hJ.pins.2.2.2 j hj
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq']
    simp only [Ranks.sigW]
    omega
  rw [refExp_vp_le_iff]
  intro la₂ S io₂ e₂ ho₂ y₂ ha₂ φ hφ
  obtain ⟨y', ha', hφ', hv'⟩ := GlobalTheory.CoverDown.exists_intFr_below _ _ _ _ (T.Q.Xo j) Y.c' Y.d hpq hG.lev.1
    (Or.inl ⟨hne, hJ.pins.2.1.2⟩) S io₂ y₂ ha₂
  obtain ⟨y, ha, hφy, hv⟩ := GlobalTheory.T.integralFramedPoint_restrict_coefficient_field _ _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle S _ y' ha'
  obtain ⟨la', e', hq', ho'⟩ := GlobalTheory.PlaceBelow.exists_overLa_under Y.c'.F Y.d.c₂.F (Y.d.eF : Y.c'.F →+* Y.d.c₂.F) q la₂.1 hq la₂.2 S io₂ e₂ ho₂
  obtain ⟨la, e₀, hq₀, ho⟩ := GlobalTheory.PlaceBelow.exists_overLa_under T.Q.c.F Y.c'.F (IntermediateField.inclusion Y.hle).toRingHom q la' hq hq' S _ e' ho'
  refine le_trans ?_ (refExp_vp_le_iff (T.U j) |>.1 le_rfl ⟨la, hq₀⟩ S _ e₀ ho y ha φ (hφy φ (hφ' φ hφ)))
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨g, ⟨hg, hP⟩, -⟩ := GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover D T j Y e o hJ hj hG hG.unit hG.modelW a n hD f.1 f.2
  have hgl := (GlobalTheory.T.pullback_mem_cuspFormSupLattice_iff D T j Y e o hJ hj hG a n f ⟨g, hg⟩ hP).2 hf
  have hfs : f.1 ∈ sec (T.Q.Xo j) T.Q.c a n := mem_sec_of_mem_cuspW_wtZ f.2
  have hP' := ((GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hJ hj hG hG.unit hG.modelW).2.2 a n f.1 hfs g).1 hP
  have hbc := ((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle).1 a n f.1 hfs).1
  have hval : evI y₂ g = evI y f.1 :=
    (hv' a n _ hbc g (mem_sec_of_mem_cuspW_wtZ hg) hP').trans (hv a n f.1 hfs)
  refine (iInf₂_le (⟨g, hg⟩ : Y.V (wtZ a n)) hgl).trans (le_of_eq ?_)
  exact congrArg _ hval

end GlobalTheory.RefSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleEqZeroOfComp
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

namespace GlobalTheory.SWOpFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adele_eq_zero_of_comp {c : AF F} (hf : ∀ v, evFin F v c = 0) (hi : ∀ w, evInf F w c = 0) : c = 0 := by
  refine Prod.ext (funext fun w => hi w) ?_
  exact Subtype.ext (funext fun v => hf v)

theorem tens_eq_zero_of_comp {z : AF F ⊗[F] E} (hf : ∀ v, compFin F E v z = 0) (hi : ∀ w, compInf F E w z = 0) :
    z = 0 := by
  let b := Module.Free.chooseBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have key : ∀ {A : Type} [CommRing A] [Algebra F A] (f : AF F →ₐ[F] A),
      (Algebra.TensorProduct.map f (AlgHom.id F E)) z = 0 → ∀ i, f (B.repr z i) = 0 := by
    intro A _ _ f hz i
    have hs : z = ∑ j, B.repr z j • B j := (B.sum_repr z).symm
    have hz' : ∑ j, f (B.repr z j) • (Algebra.TensorProduct.basis A b) j = 0 := by
      rw [hs] at hz
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [B, Algebra.TensorProduct.basis_apply, Finset.sum_apply, map_sum, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        Algebra.TensorProduct.map_tmul] using hz
    exact Fintype.linearIndependent_iff.1 (Algebra.TensorProduct.basis A b).linearIndependent _ hz' i
  have hc : ∀ i, B.repr z i = 0 := fun i =>
    adele_eq_zero_of_comp (fun v => key (evFin F v) (hf v) i) (fun w => key (evInf F w) (hi w) i)
  rw [← B.sum_repr z]
  simp [hc]

variable {σ : E →ₐ[F] E} {n : ℕ} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

end GlobalTheory.SWOpFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O.CompModel

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

theorem stalkPt_genStr (C : FlagCpt Z e) (z : C.Y.X) (φ : c.F →+* C.Y.X.presheaf.stalk z)
    (hφ : constF e C.Y = (algebraMap (C.Y.X.presheaf.stalk z) C.Y.X.functionField).comp φ) :
    stalkPt C.Y z ≫ C.π ≫ genStr Z = spMap φ := by
  let ρ : c.F →+* C.Y.X.presheaf.stalk z := (Spec.preimage (stalkPt C.Y z ≫ C.π ≫ genStr Z)).hom
  have h0 : spMap ρ = stalkPt C.Y z ≫ C.π ≫ genStr Z := Spec.map_preimage _
  let j := algebraMap (C.Y.X.presheaf.stalk z) C.Y.X.functionField
  letI := (constF e C.Y).toAlgebra
  have hgen : spMap j ≫ stalkPt C.Y z = genericPt C.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C.Y.X).specializes trivial)
  have h1 : spMap (j.comp ρ) = spMap (constF e C.Y) := by
    rw [← sp_comp, h0, ← Category.assoc, ← Category.assoc, hgen]
    exact (congrArg (· ≫ genStr Z) C.y0_x.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) Z.jQ_over).trans (pullback.lift_snd _ _ _)))
  have h2 : j.comp ρ = constF e C.Y := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have h3 : ρ = φ := RingHom.ext fun r => IsFractionRing.injective (C.Y.X.presheaf.stalk z) C.Y.X.functionField
      ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hφ r))
  rw [← h0, h3]

theorem exists_flagPt (C : FlagCpt Z e) {K : Type} [Field K] (p : Sp K ⟶ C.Y.X) :
    ∃ y : FlagPt Z K, p ≫ C.π = y.y ∧ C.Carries p y.frame := by
  obtain ⟨φ, f, t, hT, -⟩ := C.gr_spec (below p)
  let ψ : C.Y.X.presheaf.stalk (below p) →+* K := (Scheme.stalkClosedPointTo p).hom
  have hp : p = spMap ψ ≫ stalkPt C.Y (below p) := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm
  have hx : spMap ψ ≫ stalkPt C.Y (below p) ≫ C.π ≫ genι Z = (p ≫ C.π) ≫ genι Z := by
    rw [← Category.assoc, ← hp, Category.assoc]
  obtain ⟨g, hg⟩ : ∃ g : EigFrame Z (ψ.comp φ) ((p ≫ C.π) ≫ genι Z), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i := by
    rw [← hx]
    exact EigFrame.exists_baseChange E H Dw l Xo c O β Z _ _ φ _ f ψ
  have ho : (p ≫ C.π) ≫ genStr Z = spMap (ψ.comp φ) := by
    rw [← sp_comp, ← stalkPt_genStr C _ φ hT.2.1, ← Category.assoc (spMap ψ), ← hp, Category.assoc]
  refine ⟨⟨ψ.comp φ, p ≫ C.π, ho, g.v, g.tan, g.eig, g.basis⟩, rfl, below p, ψ, φ, f, t, 1, hp, hT, hx.symm, rfl,
    fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
  change IsCombAtG Z.t ((p ≫ C.π) ≫ genι Z)
    (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) (Pi.single i 1) (g.v τ i)
  rw [show (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) = g.v τ from funext fun k => (hg τ k).symm]
  exact isCombAtG_single Z.t _ (g.tan τ) i

end Free

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : TrueGeo.Model Y)

end Model

end GlobalTheory.Mean4O.CompModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingPullbackPowerMapLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingPullbackPowerMapLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HeckePullLevel

open GlobalTheory.CechPic

theorem isMonHom_id_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom ((𝟙 G) ^ n : G ⟶ G) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih => rw [pow_succ, Hom.mul_def]; infer_instance

theorem weilIs_powPull : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left) (P : LB (G2 A).left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m a b : ℕ) (n : ℤ) (T : Over S) (x₁ x₂ y₁ y₂ : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) n (lift (x₁ ^ a) (x₂ ^ b)) (lift (y₁ ^ a) (y₂ ^ b)) c → Out.WeilIs (G2 A) P (n * ((m * a * b : ℕ) : ℤ)) (lift x₁ x₂) (lift y₁ y₂) c := by
  intro S A _ _ H₀ P hA hH hamp hP h₁ h₂ m a b n T x₁ x₂ y₁ y₂ c h
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A),
      DiagPairing.pc hP (x * x') y = DiagPairing.pc hP x y + DiagPairing.pc hP x' y := fun T x x' y => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A H₀ hA hH hamp P hP h₁ h₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A),
      DiagPairing.pc hP x (y * y') = DiagPairing.pc hP x y + DiagPairing.pc hP x y' := fun T x y y' => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A H₀ hA hH hamp P hP h₁ h₂ T y y' x).2
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  haveI := isMonHom_id_pow A a
  haveI := isMonHom_id_pow A b
  let ψ : G2 A ⟶ G2 A := lift (fst A A ≫ (𝟙 A) ^ a) (snd A A ≫ (𝟙 A) ^ b)
  have e : ∀ {T : Over S} (u v : T ⟶ A), lift u v ≫ ψ = lift (u ^ a) (v ^ b) := fun u v => by
    simp only [ψ, comp_lift, ← Category.assoc, MonObj.comp_pow, Category.comp_id, lift_fst, lift_snd]
  have hM : (GlobalTheory.UPel.HT.Hecke.lbPow P m).IsLB := LB.isLB_linComb hP _ _
  have hψ : pull ψ.left (cls P hP) = (a * b) • cls P hP := by
    have e₀ : ψ = lift (fst A A ^ a) (snd A A ^ b) := by
      rw [← e (fst A A) (snd A A), lift_fst_snd, Category.id_comp]
    rw [e₀]
    change DiagPairing.pc hP (fst A A ^ a) (snd A A ^ b) = _
    rw [DiagPairing.pc_pow_left hP hB, DiagPairing.pc_pow_right hP hB', DiagPairing.pc, lift_fst_snd,
      Over.id_left, pull_id, smul_smul, mul_comm]
  have hw : LBIso (lbPow P (m * a * b)) ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull ψ.left) := by
    refine (cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hM _)).1 ?_
    have hc : cls _ hM = m • cls P hP := by
      refine (cls_linComb hP (K := Fin m) (fun _ => 𝟙 (G2 A).left) (fun _ => 1) hM).trans ?_
      simp only [pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [cls_lbPow hP, cls_pull hM, hc, map_nsmul, hψ, smul_smul]
    congr 1
    ring
  have h' : Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) n (lift x₁ x₂ ≫ ψ) (lift y₁ y₂ ≫ ψ) c := by
    rw [e, e]; exact h
  exact WeilIsogeny.weilIs_pull_hom hG hAA hP hM ψ hw h'

end GlobalTheory.HeckePullLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingPullbackPowerMapLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_pullback_powerMap_level : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left) (P : LB (G2 A).left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m a b : ℕ) (n : ℤ) (T : Over S) (x₁ x₂ y₁ y₂ : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) n (lift (x₁ ^ a) (x₂ ^ b)) (lift (y₁ ^ a) (y₂ ^ b)) c → Out.WeilIs (G2 A) P (n * ((m * a * b : ℕ) : ℤ)) (lift x₁ x₂) (lift y₁ y₂) c := by
  first | (exact @GlobalTheory.HeckePullLevel.weilIs_powPull) | (exact GlobalTheory.HeckePullLevel.weilIs_powPull) | (intros; apply GlobalTheory.HeckePullLevel.weilIs_powPull <;> assumption)
end
end
