module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleComplexExistenceJetsKeyValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedLieBasisTorusExtensionModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateTermsJetsBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorSectionValueEqExpansionSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleConstantAlongDeformationOfClauses

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalOfLocalUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValuesDetOmegaDeltaLocalUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedAlongAllTraitsRestrictAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedAlongAllTraitsRestrictAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals


open GlobalTheory.TorsionFormCompare GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum in
theorem hasUnif_of_iso {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (hV : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (G G₀ : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀]
    [IsCommMonObj G₀] (ε : G ≅ G₀) (hε : IsMonHom ε.hom) (hsa : IsSemiAbelian G₀) (L₀ : LB G₀.left)
    (h : HasUnif G₀ L₀) : HasUnif G (L₀.pull ε.hom.left) := by
  obtain ⟨D, A₀, U₀, hL⟩ := h
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have he : eSec G ≫ ε.hom.left = 𝟙 _ ≫ eSec G₀ := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε.hom)
  let L' : RigLB G := ⟨U₀.LG.L.pull ε.hom.left, rigPullOf ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig,
    LB.isLB_pull U₀.LG.isLB _,
    GlobalTheory.CubePullLawChecks.rigPullIsGen ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig U₀.LG.isLB U₀.LG.rigGen⟩
  let w : LB.Iso L'.L (U₀.LG.L.pull ε.hom.left) := idIso L'.L
  have hw : RigAlong ε.hom U₀.LG L' w :=
    ⟨idIso_isGen L'.isLB, (maps_iff w _ (fun _ => eSec G₀) _ L'.rig U₀.LG.rig (𝟙 _) _
      (rigPull_le _ _ he U₀.LG.L) (fun _ => rfl)).1 (idIso_maps L')⟩
  obtain ⟨W, hW, hψ⟩ := psiOnExists V (IsLocalRing.maximalIdeal V) hR D
  obtain ⟨hD, -⟩ := exists_isIdPull V D.toPre W hW hψ
  obtain ⟨bc, U, -, -, hLG, -, -⟩ :=
    exists_unif_move V (IsLocalRing.maximalIdeal V) D A₀ G₀ G ε hR hsa hε U₀ L' w hw hD
  refine ⟨D, A₀, U, ?_⟩
  rw [hLG]
  exact LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hL

theorem unifAlong_bG {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) {R : Type} [CommRing R]
    (f : Sp R ⟶ S) (hG : IsSemiAbelian G) (h : UnifAlong G L.L) : UnifAlong (bG G f) (bL L f).L := by
  intro V _ _ _ _ hV hf ξ hξ _
  have hξ' : ((ξ ≫ f) ⁻¹' abLocus G).Nonempty := by
    obtain ⟨p, hp⟩ := hξ
    refine ⟨p, ?_⟩
    have := (abLocus_pullback (G' := bG G f) abLocusOne hG (isGrpPullback_pullback G f).1 (ξ p)).2 hp
    simpa using this
  obtain ⟨ε, hε, hφ⟩ := grpPullback_iso ((isGrpPullback_pullback (bG G f) ξ).comp (isGrpPullback_pullback G f))
    (isGrpPullback_pullback G (ξ ≫ f))
  obtain ⟨D, A, U, hU⟩ := hasUnif_of_iso hV _ _ ε hε (IsSemiAbelian.pullback (ξ ≫ f) G hG) _ (h V hV hf (ξ ≫ f) hξ')
  refine ⟨D, A, U, LBIso.trans U.LG.isLB (LB.isLB_pull (LB.isLB_pull L.isLB _) _)
    (LB.isLB_pull (bL L f).isLB _) hU ?_⟩
  exact LBIso.chartPull (h := ε.hom.left)
    (chartPullLinComb L.L _ (fun _ : PUnit => ε.hom.left) (fun _ => pullback.fst G.hom (ξ ≫ f)) (fun _ => 1) _ fun _ => rfl)
    (chartPullLinComb L.L _ (fun _ : PUnit => pullback.fst (bG G f).hom ξ) (fun _ => pullback.fst G.hom (ξ ≫ f))
      (fun _ => 1) _ fun _ => hφ.symm)
    (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _))

theorem unifAlong_affineOpen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsSemiAbelian G → UnifAlong G L.L → UnifAlong (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L :=
  fun _ G _ _ L _ hW hG h => unifAlong_bG G L hW.fromSpec hG h

end GlobalTheory.KeyVals

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedAlongAllTraitsRestrictAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedAlongAllTraits_restrict_affineOpen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsSemiAbelian G → UnifAlong G L.L → UnifAlong (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L := by
  first | exact @GlobalTheory.KeyVals.unifAlong_affineOpen | exact GlobalTheory.KeyVals.unifAlong_affineOpen | (intros; apply GlobalTheory.KeyVals.unifAlong_affineOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingNormalCharZeroFiniteTypeOverInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingNormalCharZeroFiniteTypeOverInt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyVals

theorem ring_of_isAffineOpen : ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (W : S.Opens), IsAffineOpen W → (W : Set S).Nonempty →
    Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s → CharZero Γ(S, ⊤) →
    IsIntegrallyClosed Γ(S, W) ∧ CharZero Γ(S, W) ∧ Algebra.FiniteType ℤ Γ(S, W) := by
  intro S _ s W hW hne hN hs hc
  haveI : Nonempty W := hne.to_subtype
  haveI : GlobalTheory.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).2 hN
  refine ⟨GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW, ?_, ?_⟩
  · exact charZero_of_injective_ringHom (map_injective_of_isIntegral S (homOfLE (le_top : W ≤ ⊤)))
  · have h₁ : (s.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s hs ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
    have h₂ : ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType :=
      RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv.surjective
    have h₃ := h₁.comp h₂
    rw [← RingHom.finiteType_algebraMap, RingHom.ext_int (algebraMap ℤ Γ(S, W))
      ((s.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom)]
    exact h₃

end GlobalTheory.KeyVals
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingNormalCharZeroFiniteTypeOverIntStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineOpen_ring_normal_charZero_finiteType_over_int : ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (W : S.Opens), IsAffineOpen W → (W : Set S).Nonempty →
    Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s → CharZero Γ(S, ⊤) →
    IsIntegrallyClosed Γ(S, W) ∧ CharZero Γ(S, W) ∧ Algebra.FiniteType ℤ Γ(S, W) := by
  first | exact @GlobalTheory.KeyVals.ring_of_isAffineOpen | exact GlobalTheory.KeyVals.ring_of_isAffineOpen | (intros; apply GlobalTheory.KeyVals.ring_of_isAffineOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValuesDetOmegaDeltaLocalUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open Classical

namespace GlobalTheory.KeyValsPf

theorem smooth_bG : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g (KeyVals.bG G ξ).hom := by
  intro S G _ g R _ ξ h
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) (isGrpPullback_pullback G ξ).1 h

theorem semi_bG : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    IsSemiAbelian G → IsSemiAbelian (KeyVals.bG G ξ) := by
  intro S G _ R _ ξ h
  exact IsSemiAbelian.pullback ξ G h

theorem mem_abLocus_bG {S : Scheme.{0}} (G : Over S) {R : Type} [CommRing R] (ξ : Sp R ⟶ S) (q : Sp R)
    (h : ξ q ∈ abLocus G) : q ∈ abLocus (KeyVals.bG G ξ) := by
  intro K _ _ t ⟨z, hz⟩
  have := h K (t ≫ ξ) ⟨z, by rw [← hz]; rfl⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom ξ) t).paste_horiz (IsPullback.of_hasPullback G.hom ξ)
  have e := P.isoPullback_hom_snd
  show IsProper (pullback.snd (pullback.snd G.hom ξ) t)
  rw [← e]
  infer_instance

theorem mem_abLocus_of_bG {S : Scheme.{0}} (G : Over S) {R : Type} [CommRing R] (ξ : Sp R ⟶ S) [IsOpenImmersion ξ] (q : Sp R)
    (h : q ∈ abLocus (KeyVals.bG G ξ)) : ξ q ∈ abLocus G := by
  intro K _ _ t ⟨z, hz⟩
  have hr : Set.range t ⊆ Set.range ξ := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w z]
    exact ⟨q, hz.symm⟩
  obtain ⟨u, rfl⟩ : ∃ u : Sp K ⟶ Sp R, u ≫ ξ = t := ⟨IsOpenImmersion.lift ξ t hr, IsOpenImmersion.lift_fac _ _ _⟩
  have : IsProper (pullback.snd (pullback.snd G.hom ξ) u) := h K u ⟨z, ξ.isOpenEmbedding.injective hz⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom ξ) u).paste_horiz (IsPullback.of_hasPullback G.hom ξ)
  rw [← P.isoPullback_inv_snd]
  infer_instance

theorem abLocus_generic : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G], genericPoint S ∈ abLocus G →
    abLocus (KeyVals.bG G (KeyVals.genPt S)) = Set.univ := by
  intro S _ G _ h
  refine Set.eq_univ_of_forall fun q => mem_abLocus_bG G _ q ?_
  have hp : KeyVals.genPt S q ∈ Set.range (S.fromSpecStalk (genericPoint S)) := ⟨q, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  rwa [(hp.antisymm (genericPoint_specializes _)).eq]

theorem abLocus_affine : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] (W : S.Opens) (hW : IsAffineOpen W), (W : Set S).Nonempty →
    IsOpen (abLocus G) → genericPoint S ∈ abLocus G → IsOpen (abLocus (KeyVals.bG G hW.fromSpec)) ∧
      Set.range (spMap (algebraMap Γ(S, W) (FractionRing Γ(S, W)))).base ⊆ abLocus (KeyVals.bG G hW.fromSpec) := by
  intro S _ G _ W hW hne hop h
  haveI : Nonempty W := ⟨⟨hne.some, hne.some_mem⟩⟩
  have e : abLocus (KeyVals.bG G hW.fromSpec) = hW.fromSpec ⁻¹' abLocus G :=
    Set.ext fun q => ⟨mem_abLocus_of_bG (R := Γ(S, W)) G hW.fromSpec q, mem_abLocus_bG (R := Γ(S, W)) G hW.fromSpec q⟩
  have ho : IsOpen (hW.fromSpec ⁻¹' abLocus G) := hop.preimage hW.fromSpec.continuous
  rw [e]
  refine ⟨ho, ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨q, hq⟩ : genericPoint S ∈ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    exact ((genericPoint_spec S).mem_open_set_iff W.isOpen).2 ⟨hne.some, trivial, hne.some_mem⟩
  refine Specializes.mem_open (y := q) ?_ ho (show hW.fromSpec q ∈ abLocus G from hq ▸ h)
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  intro a ha
  have ha' : algebraMap Γ(S, W) (FractionRing Γ(S, W)) a ∈ (show PrimeSpectrum (FractionRing Γ(S, W)) from z).asIdeal := ha
  have hz : (show PrimeSpectrum (FractionRing Γ(S, W)) from z).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [hz, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at ha'
  exact ha' ▸ Ideal.zero_mem _

theorem exists_keyVal : ∀ κ : Rule, ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∀ (c : VB.Chart (LieVB.omega G) g) (i : δ.ι), genericPoint S ∈ c.U ⊓ δ.U i → ∃ v, KeyVals.IsKeyVal κ g L σ c i v := by
  intro κ S _ _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i hgen
  have hgab : genericPoint S ∈ abLocus G := by
    obtain ⟨p, hp⟩ := hne
    exact ((genericPoint_spec S).mem_open_set_iff hop).2 ⟨p, trivial, hp⟩
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_localFormOfTensorSection_in_chart S G L δ σ i _ (KeyVals.genPt S) hδ (KeyVals.genPt_le _ hgen.2)
  obtain ⟨y, hy, hyb⟩ := GlobalTheory.T.exists_dualTangentBasis_pulledCotangentChartFrame S G g c _ (KeyVals.genPt S) hsa hsm (KeyVals.genPt_le _ hgen.1)
  have hab := abLocus_generic S G hgab
  obtain ⟨x, hxg, hx⟩ := GlobalTheory.KeyDatumAb.exists_keyOn (KeyVals.FF S) (KeyVals.FF S) (RingHom.id _)
    (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)) t g y hg (semi_bG S G _ _ hsa)
    (smooth_bG S G g _ _ hsm) (by rw [hab]; exact isOpen_univ) (GlobalTheory.T.isSymmetric_rigidifiedBundleBaseChange S G L _ _ hsym) (GlobalTheory.T.principalPolarisationOnAbLocus_genericFibre S G L hop hgab hpol) hyb
    (GlobalTheory.T.sectionNonzeroOnEveryFibre_localFormBaseChange S G L δ σ i _ _ t (KeyVals.genPt_le _ hgen.2) ht hnz) (by rw [hab]; exact Set.subset_univ _)
  exact ⟨_, t, y, x, hxg, ht, hy, hx, rfl⟩

theorem keyVal_unit : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∀ (c : VB.Chart (LieVB.omega G) g) (i : δ.ι) (v : KeyVals.FF S), KeyVals.IsKeyVal κ g L σ c i v → ∀ p ∈ c.U ⊓ δ.U i,
      ∃ (V : S.Opens) (_ : V ≤ c.U ⊓ δ.U i) (_ : p ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V,
        S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = v := by
  intro κ hH hF hL S _ _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i v hv p hp
  obtain ⟨t', y', x, hxg, ht', hy', hx, rfl⟩ := hv
  have hgab : genericPoint S ∈ abLocus G := by
    obtain ⟨p, hp⟩ := hne
    exact ((genericPoint_spec S).mem_open_set_iff hop).2 ⟨p, trivial, hp⟩
  obtain ⟨W, hW, hpW, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hp
  have hW : IsAffineOpen W := hW
  haveI : Nonempty W := ⟨⟨p, hpW⟩⟩
  obtain ⟨hic, hcz, hft⟩ := GlobalTheory.T.affineOpen_ring_normal_charZero_finiteType_over_int S s W hW ⟨p, hpW⟩ hN hs h0
  haveI : IsNoetherianRing Γ(S, W) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hr : ∀ U : S.Opens, W ≤ U → ⊤ ≤ hW.fromSpec ⁻¹ᵁ U := fun U h q _ =>
    h (show hW.fromSpec q ∈ (W : Set S) from hW.range_fromSpec ▸ ⟨q, rfl⟩)
  have hri := hr _ (hle.trans inf_le_right)
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_localFormOfTensorSection_in_chart S G L δ σ i Γ(S, W) hW.fromSpec hδ hri
  obtain ⟨y, hy, hyb⟩ := GlobalTheory.T.exists_dualTangentBasis_pulledCotangentChartFrame S G g c Γ(S, W) hW.fromSpec hsa hsm (hr _ (hle.trans inf_le_left))
  obtain ⟨hopW, habW⟩ := abLocus_affine S G W hW ⟨p, hpW⟩ hop hgab
  have hsaW := semi_bG S G Γ(S, W) hW.fromSpec hsa
  have hsmW := smooth_bG S G g Γ(S, W) hW.fromSpec hsm
  have hsyW := GlobalTheory.T.isSymmetric_rigidifiedBundleBaseChange S G L Γ(S, W) hW.fromSpec hsym
  have hpoW := GlobalTheory.T.principalPolarisationOnAbLocus_restrict_affineOpen S G L W hW hop hpol
  have hnzW := GlobalTheory.T.sectionNonzeroOnEveryFibre_localFormBaseChange S G L δ σ i Γ(S, W) hW.fromSpec t hri ht hnz
  obtain ⟨z, hzg, hz⟩ := GlobalTheory.KeyDatumAb.exists_keyOn Γ(S, W) (FractionRing Γ(S, W)) (algebraMap _ _)
    (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t g y hg hsaW hsmW hopW hsyW hpoW hyb hnzW habW
  subst hzg
  obtain ⟨u, hu⟩ := hL Γ(S, W) (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t z y hsaW hsmW hopW hsyW hpoW
    (GlobalTheory.T.uniformisedAlongAllTraits_restrict_affineOpen S G L W hW hsa hunif) hyb hnzW hz
  refine ⟨W, hle, hpW, u, fun h => ?_⟩
  let r : Γ(S, W) →+* KeyVals.FF S := (S.presheaf.germ W (genericPoint S) h).hom
  have hinj : Function.Injective r := germ_injective_of_isIntegral S (genericPoint S) h
  let e : FractionRing Γ(S, W) →+* KeyVals.FF S := IsFractionRing.lift hinj
  have he : (RingHom.id _).comp r = e.comp (algebraMap _ _) := RingHom.ext fun a => (IsFractionRing.lift_algebraMap hinj a).symm
  have hξ := KeyVals.spMap_germ_fromSpec W hW h
  have hx' := GlobalTheory.T.fibreDatum_baseChange_to_coarserPoint S G _ L δ σ i Γ(S, W) (KeyVals.FF S) (KeyVals.FF S) hW.fromSpec r (KeyVals.genPt S) (RingHom.id _)
    t y t' y' x hxg hξ hri ht ht' (GlobalTheory.T.dualTangentBasis_pulledFrame_compatible_pointChange S G _ c Γ(S, W) (KeyVals.FF S) hW.fromSpec r (KeyVals.genPt S) y y' hξ hsa hsm hy hy') hx
  rw [he] at hx'
  have hpb := GlobalTheory.KeyEven.keyPB_of_keyOn_comp Γ(S, W) (FractionRing Γ(S, W)) (KeyVals.FF S) (algebraMap _ _) e
    (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t _ y z x rfl hxg hz hx'
  rw [hF _ _ e z x hpb, hu]
  exact (IsFractionRing.lift_algebraMap hinj _).symm

theorem keyVal_compat : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)]
    (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S) (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec),
    IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → δ.IsLB →
    ∀ (c c' : VB.Chart (LieVB.omega G) g) (i i' : δ.ι) (v v' : KeyVals.FF S)
      (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
      (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
      KeyVals.IsKeyVal κ g L σ c i v → KeyVals.IsKeyVal κ g L σ c' i' v' →
      v * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
        S.presheaf.germ _ (genericPoint S) h1
          ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * v' := by
  intro κ hH hF S _ _ G _ _ g L δ σ hsa hsm hδ c c' i i' v v' h1 h2 hv hv'
  obtain ⟨t, y, x, hg, ht, hy, hk, rfl⟩ := hv
  obtain ⟨t', y', x', hg', ht', hy', hk', rfl⟩ := hv'
  obtain ⟨M, hM, hdet⟩ := GlobalTheory.T.dualTangentVectors_genericFibre_det_eq_detOmegaTrans S G g hsa hsm c c' h1 y y' hy hy'
  have hs := GlobalTheory.T.localFormsTensorSection_genericFibre_transitionGerm S G L δ σ hδ i i' h2 t t' ht ht'
  have := GlobalTheory.KeyEven.keyValue_homog_of_fibres κ hH hF (KeyVals.FF S) (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)) t' t g y' y
    x' x hg' hg _ M hk' hk hs hM
  rw [← hdet, mul_comm]
  exact this

theorem keyVals : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  intro κ hH hF hL S _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  haveI : CharZero (KeyVals.FF S) :=
    charZero_of_injective_ringHom (f := (S.presheaf.germ ⊤ (genericPoint S) trivial).hom)
      (germ_injective_of_isIntegral S (U := ⊤) (genericPoint S) trivial)
  let f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S) := fun c i =>
    if h : ∃ v, KeyVals.IsKeyVal κ g L σ c i v then h.choose else 1
  have hf : ∀ c i, genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i → KeyVals.IsKeyVal κ g L σ c i (f c i) := by
    intro c i h
    have ex := exists_keyVal κ S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i h
    simp only [f, dif_pos ex]
    exact ex.choose_spec
  have hgen : ∀ U : S.Opens, (U : Set S).Nonempty → genericPoint S ∈ U := fun U ⟨p, hp⟩ =>
    ((genericPoint_spec S).mem_open_set_iff U.isOpen).2 ⟨p, trivial, hp⟩
  refine ⟨f, fun c i p hp => ?_, fun c c' i i' h1 h2 => ?_⟩
  · exact keyVal_unit κ hH hF hL S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i (f c i)
      (hf c i (hgen _ ⟨p, hp⟩)) p hp
  · exact keyVal_compat κ hH hF S G g L δ σ hsa hsm hδ c c' i i' (f c i) (f c' i') h1 h2
      (hf c i ⟨h1.1, h2.1⟩) (hf c' i' ⟨h1.2, h2.2⟩)

end GlobalTheory.KeyValsPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValuesDetOmegaDeltaLocalUnitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyValues_detOmega_delta_local_units : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  first | exact @GlobalTheory.KeyValsPf.keyVals | exact GlobalTheory.KeyValsPf.keyVals | (intros; apply GlobalTheory.KeyValsPf.keyVals <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalOfLocalUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEvenGlue

theorem lbPow_U' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j : (lbPow M n).ι) : (lbPow M n).U j = M.U (j PUnit.unit) := by
  ext x
  simp only [lbPow, LB.LinComb, LB.wchart]
  simp
  exact ⟨fun h => h _, fun h i => h⟩

theorem germ_lbPow_g' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j j' : (lbPow M n).ι) (x : S)
    (h : x ∈ (lbPow M n).U j ⊓ (lbPow M n).U j') (h' : x ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :
    S.presheaf.germ _ x h ((lbPow M n).g j j' : Γ(S, (lbPow M n).U j ⊓ (lbPow M n).U j')) =
      S.presheaf.germ _ x h' (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(S, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) ^ n := by
  simp only [lbPow, LB.LinComb, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  congr 1
  simp [res, pullU]
  erw [map_pow]
  congr 1
  erw [Units.coe_map, Units.coe_map]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem keyGlob_of_keyLoc : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → KeyGlob := by
  intro κ hH hF hL S s G _ _ g L δ σ hg hS hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  haveI := hS
  obtain ⟨f, hloc, hcomp⟩ := GlobalTheory.T.thetaKeyValues_detOmega_delta_local_units κ hH hF hL S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  refine GlobalTheory.T.lineBundleIso_of_compatible_rational_local_units S (lbPow δ 8) (lbPow (SiegelTor.hodge G g) 4) (fun p => f (p.1 PUnit.unit) (p.2 PUnit.unit)) ?_ ?_
  · rintro ⟨c, i⟩ x hx
    rw [lbPow_U', lbPow_U'] at hx
    obtain ⟨V, hV, hxV, u, hu⟩ := hloc _ _ x hx
    exact ⟨V, by rw [lbPow_U', lbPow_U']; exact hV, hxV, u, hu⟩
  · rintro ⟨c, i⟩ ⟨c', i'⟩ h1 h2
    have h1' : genericPoint S ∈ (VB.det (LieVB.omega G) g).U (c PUnit.unit) ⊓ (VB.det (LieVB.omega G) g).U (c' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h1; exact h1
    have h2' : genericPoint S ∈ δ.U (i PUnit.unit) ⊓ δ.U (i' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h2; exact h2
    dsimp only
    rw [germ_lbPow_g' δ 8 i i' _ h2 h2', germ_lbPow_g' _ 4 c c' _ h1 h1']
    exact hcomp _ _ _ _ h1' h2'

end GlobalTheory.KeyEvenGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalOfLocalUnitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.key_formula_even_degeneration_global_of_local_units : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → KeyGlob := by
  first | exact @GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc | exact GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc | (intros; apply GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUniformisedFourierFrameAbsOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUniformisedFourierFrameAbsOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.KapFPf

theorem norm_toF_unit {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {C : Type} [NormedField C]
    [Algebra (FractionRing V) C] (hC : CExt V I C) (u : Vˣ) : ‖toF V C u‖ = 1 := by
  have h1 : ‖toF V C u‖ ≤ 1 := hC.1 u
  have h2 : ‖toF V C ↑u⁻¹‖ ≤ 1 := hC.1 ↑u⁻¹
  have h3 : toF V C u * toF V C ↑u⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have h4 : ‖toF V C u‖ * ‖toF V C ↑u⁻¹‖ = 1 := by rw [← norm_mul, h3, norm_one]
  nlinarith [norm_nonneg (toF V C u), norm_nonneg (toF V C ↑u⁻¹)]

theorem c_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre), GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N) (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → c ≠ 0 := GlobalTheory.T.genericThetaExpansion_scalar_ne_zero

theorem level_labels : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := GlobalTheory.T.levelStructure_baseChange_labels_torsion

theorem jc_smul : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (a : F) (gm : GtPt D (TE R F)) (α : N.X),
    jc ν (a • s) gm α = TrivSqZeroExt.inl a * jc ν s gm α := GlobalTheory.T.torusExtDualNumberTermValue_smul

theorem fst_indep : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := GlobalTheory.T.section_value_eq_at_first_order_of_tangents

theorem deform_of_series : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := GlobalTheory.T.powerSeriesDeformation_of_boundedLatticeSeries

end GlobalTheory.MBLow.KapFPf

namespace GlobalTheory.MBLow.KapFPf


set_option maxHeartbeats 4000000 in
theorem kapF_of_rule4 : ∀ κ : Rule, Rule4 κ → KapF κ := by
  intro κ hR4
  obtain ⟨hHom, hFun, hTh1, hFamU⟩ := id hR4
  intro V _ _ _ _ hcomp hfin D x G _ _ hSA U w₀ hNW y hy hyv C _ _ _ _ _ _ hCE hiso N ν hInt th ϑ c hOn hExp hFV
  obtain ⟨e⟩ := hiso

  set K := FractionRing V

  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.transfer_of_rule4' κ hR4 x.P.g 3 Nat.prime_three ⟨1, rfl⟩
  set j := max j₀ 1 with hj
  set m := 3 ^ j with hm
  have hmOdd : Odd m := Odd.pow ⟨1, rfl⟩
  have hm1 : 1 ≤ m := Nat.one_le_pow _ _ (by norm_num)
  have hm2 : 2 ≤ m ^ 2 := by
    have : 3 ≤ m := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    nlinarith

  have hAdapt : ∃ (vB : Fin D.toPre.P.g → (epsR V ⟶ D.toPre.P.A))
      (r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X)
      (σ : Fin x.P.g ≃ Fin D.toPre.P.g ⊕ Fin r)
      (y' : Fin x.P.g → (epsR V ⟶ G)) (gm₀ : Fin x.P.g → GtPt D.toPre (epsR V))
      (gm : Fin x.P.g → GtPt D.toPre (TE V C)),
      IsLieBasis y' ∧ Adapted ν vB bX σ gm ∧ ∀ j,
        TanRel U.toUnifPre (y' j) (gm₀ j) ∧ GtTan (gm₀ j) ∧
          GtPt.IsPull (spMap (dualMap (toF V C))) (gm₀ j) (gm j) :=
    GlobalTheory.T.exists_adaptedLieBasis_torusExtensionModel V hcomp D x.P G hSA U C hCE N ν hInt
  obtain ⟨vB, r, bX, σ, y', gm₀, gm, hy', hAd, hT⟩ := hAdapt
  have hvec := fun j => GlobalTheory.T.existsUnique_genericFibreDualNumberPoint_of_model V hcomp D x.P G hSA U C (y' j)
  choose yA hyA _ using fun j => (hvec j).1
  choose v' hv'o _ using fun j => (hvec j).2.1
  have hyAs : ∀ j, yA j ≫ (snd (TFK (R := V) C) x.P.A).left =
      spMap (dualMap (algebraMap (FractionRing V) C)) ≫ (v' j).left := fun j => (hvec j).2.2 (v' j) (yA j) (hv'o j) (hyA j)
  obtain ⟨-, -, -, hgp, -⟩ := GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso V _ D x.P G U.toUnifPre
  obtain ⟨hv', u, hu⟩ := GlobalTheory.T.thetaKeyRule_lieBasisChange_unit_factor κ hHom V (FractionRing V) (algebraMap V (FractionRing V)) x G _ hgp y y' v' hy hy' hyv hv'o
  set x' : KeyIn (FractionRing V) := ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv'⟩ with hx'

  obtain ⟨xC, hgC, io, hPB, hW, hJ⟩ := GlobalTheory.T.exists_keyDatumBaseChange_thetaJets (FractionRing V) C (algebraMap (FractionRing V) C) x'
  have hκC : (κ C xC : C) = algebraMap (FractionRing V) C (κ (FractionRing V) x') := hFun _ _ _ x' xC hPB
  obtain ⟨ζ, ⟨lev⟩⟩ := GlobalTheory.T.exists_symplecticLevel_algClosed_charZero C xC.P (m ^ 2) (by omega)
  obtain ⟨hprim, hadd, hinj, hsurj, hweil⟩ :=
    level_labels (FractionRing V) C (algebraMap (FractionRing V) C) x'.P xC.P io hW x.P.g (m ^ 2) hgC ζ lev hm2
  set pt : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → (TFK (R := V) C ⟶ x.P.A) := fun a => io.symm (levelPoint lev hgC a) with hpt
  obtain ⟨p, Q, hQL, hpq⟩ := GlobalTheory.T.torsionSymplecticLabels_of_levelStructure V hcomp D x.P G hSA U C hCE N ν hInt x.P.g (m ^ 2) (by omega) ζ pt hprim
    hadd hinj hsurj hweil

  choose Θ tt ss ff hfam using fun a => GlobalTheory.T.symmetricThetaTranslates_expand_seriesFamilies V hcomp D x.P G hSA U C hCE N ν hInt w₀ x.rig hNW th ϑ c hExp hFV
    m hmOdd (p a) (Q a) (pt a) (hpq a).1 (hpq a).2
  have hc : c ≠ 0 := c_ne_zero V hcomp D x G hSA U w₀ hNW C hCE N ν th ϑ c hOn hExp hFV
  set s' : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fam D.toPre C (m ^ 2) := fun a => c⁻¹ • ss a with hs'
  have hs'V : ∀ a, ν.FamV (s' a) (ff a) := fun a => by
    have := GlobalTheory.WeilValues.famV_smul ν (hfam a).2.2.2.2 c⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

  have hch : ∃ i₀, ⊤ ≤ (jFK (R := V) C ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U i₀ := by
    have h : (jFK (R := V) C ≫ eSec x.P.A) (default : PrimeSpectrum C) ∈ (⨆ i, x.P.L.U i) := by
      rw [x.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    refine ⟨i, fun z _ => ?_⟩
    obtain rfl : z = (default : PrimeSpectrum C) := Subsingleton.elim _ _
    exact hi
  obtain ⟨i₀, hi₀⟩ := hch
  choose cj hcj using fun j => GlobalTheory.T.tangentVector_section_value_eq_expansion_sum V hcomp D x.P G hSA U C hCE N ν hInt w₀ x.rig hNW (y' j) (gm₀ j) (gm j)
    (yA j) (hy'.1 j) (hT j).1 (hT j).2.2 (hyA j) (m ^ 2) i₀ hi₀
  set j₁ : Fin x.P.g := ⟨0, x.g_pos⟩
  set Sf : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fin x.P.g → C :=
    fun a j => ∑' α, (jc ν (ss a) (gm j) α).fst / ν.rg ^ (m ^ 2) with hSf
  set Ss : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fin x.P.g → C :=
    fun a j => ∑' α, (jc ν (ss a) (gm j) α).snd / ν.rg ^ (m ^ 2) with hSs
  have hind : ∀ a j, Sf a j = Sf a j₁ := fun a j =>
    fst_indep (FractionRing V) C x.P x.rig (m ^ 2) (tt a) i₀ hi₀ (v' j) (v' j₁) (hv'.1 j) (hv'.1 j₁) (yA j) (yA j₁)
      (hyA j).1 (hyAs j) (hyA j₁).1 (hyAs j₁) _ _ _ _ (hcj j (tt a) (ss a) (hfam a).2.2.1).2.2
      (hcj j₁ (tt a) (ss a) (hfam a).2.2.1).2.2
  have hTJ : ThJetT x'.P x'.rig m (spMap (algebraMap (FractionRing V) C)) th pt yA (fun a => Sf a j₁) Ss := by
    refine ⟨Θ, tt, i₀, cj, fun a => ⟨(hfam a).1, (hfam a).2.1⟩, hi₀, fun a j => ?_⟩
    have h := (hcj j (tt a) (ss a) (hfam a).2.2.1).2.2
    have e := hind a j
    simp only [hSf] at e
    rw [e] at h
    exact h
  have hJC := hJ m th _ pt yA (fun a => Sf a j₁) Ss hOn (fun j => ⟨(hyA j).1, hyAs j⟩) hTJ
  have hio : (fun a => io (pt a)) = levelPoint lev hgC := funext fun a => io.apply_symm_apply _
  rw [hio] at hJC
  obtain ⟨th'', hth'', hsc, hJsc⟩ := GlobalTheory.T.thetaKeyRule_scale_section_pow_eight κ hHom C xC c⁻¹ (inv_ne_zero hc)
  have hJ'' := hJsc x.P.g hgC m _ (levelPoint lev hgC) _ _ hJC
  set x'' : KeyIn C := ⟨xC.P, xC.g_pos, xC.rig, xC.rig_gen, th'', hth'', xC.v, xC.basis⟩ with hx''

  have hadm : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  obtain ⟨q, hq⟩ := GlobalTheory.T.degenerationValues_int_of_admissibleBase V _ hadm D C hCE N ν hInt
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨hrg, hdisc⟩ := GlobalTheory.T.degenerationValues_norms_eq_uniformizer_zpow V ϖ hϖ D C hCE N ν hInt
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have ht1 : ‖toF V C ϖ‖ < 1 := hCE.2 ϖ hϖm
  have ht0 : toF V C ϖ ≠ 0 := by
    intro h
    have hinj : Function.Injective (toF V C) :=
      (algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))
    exact hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨β, π, hπ0, hπ1, hfinβ, hexp⟩ := GlobalTheory.T.exists_integralForm_parameter_of_discreteNorms C N q (toF V C ϖ) hq ht0 ht1 hdisc m hm1
  choose bd hbd using fun a j => GlobalTheory.T.thetaTranslateTerms_jets_bounded V D C hCE N ν hInt q hq m hmOdd (Q a) (s' a) (ff a) (hs'V a)
    (hfam a).2.2.2.1 (gm₀ j) (gm j) (hT j).2.1 (hT j).2.2
  haveI : NeZero (m ^ 2) := ⟨by omega⟩
  set B : ℝ := ∑ a, ∑ j, |bd a j| with hB
  have hbB : ∀ a j, bd a j ≤ B := fun a j =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun j => |bd a j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun a => ∑ j, |bd a j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)))
  obtain ⟨k₀, hBK, hk₀⟩ := GlobalTheory.T.exists_abelianKeyValue_norm_one κ hR4 V D.toPre C hCE N ν hInt vB hAd.1
  have hAF := GlobalTheory.T.archimedeanExistence_of_complex_isomorphic_field κ hFun (GlobalTheory.T.keyRule_complex_existence_jets_key_value κ hR4)
  obtain ⟨ε, hε, hAε⟩ := hAF V D.toPre D.psi_even D.tau_bimult C e N ν x.P.g r m (m ^ 2) x.g_pos hmOdd dvd_rfl β ζ Q hQL
    s' (fun a => ⟨ff a, hs'V a, (hfam a).2.2.2.1⟩) vB bX σ gm hAd k₀ hBK
  set nn : N.X → ℕ := fun α => (β.be α α / (2 * m ^ 2)).toNat with hnn
  set aa : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → N.X → C :=
    fun a α => (jc ν (s' a) (gm j₁) α).fst / ν.rg ^ (m ^ 2) with haa
  set bb : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fin x.P.g → N.X → C :=
    fun a j α => (jc ν (s' a) (gm j) α).snd / ν.rg ^ (m ^ 2) with hbb
  have hSa : ∀ a, c⁻¹ * Sf a j₁ = ∑' α, aa a α := fun a => by
    rw [hSf, ← tsum_mul_left]
    apply tsum_congr
    intro α
    simp [haa, hs', jc_smul, TrivSqZeroExt.fst_mul, mul_div_assoc]
  have hSb : ∀ a j, c⁻¹ * Ss a j = ∑' α, bb a j α := fun a j => by
    rw [hSs, ← tsum_mul_left]
    apply tsum_congr
    intro α
    simp [hbb, hs', jc_smul, TrivSqZeroExt.snd_mul, mul_div_assoc]
  have hJ3 : ThJet x'' hgC m (levelPoint lev hgC) (fun i => ∑' α, aa i α) (fun i j => ∑' α, bb i j α) := by
    have e1 : (fun i => ∑' α, aa i α) = fun i => c⁻¹ * Sf i j₁ := funext fun i => (hSa i).symm
    have e2 : (fun i j => ∑' α, bb i j α) = fun i j => c⁻¹ * Ss i j := funext fun i => funext fun j => (hSb i j).symm
    rw [e1, e2]
    exact hJ''
  have hba : ∀ i α, ‖aa i α‖ ≤ B * ‖π‖ ^ nn α := fun i α => by
    have h := ((hbd i j₁) α).1
    rw [hexp α] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hbB i j₁) (pow_nonneg (norm_nonneg _) _))
  have hbb' : ∀ i j α, ‖bb i j α‖ ≤ B * ‖π‖ ^ nn α := fun i j α => by
    have h := ((hbd i j) α).2
    rw [hexp α] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hbB i j) (pow_nonneg (norm_nonneg _) _))
  have hDef : Deform κ (e : C →+* ℂ) x'' hgC m ζ lev k₀ := by
    refine deform_of_series κ C (e : C →+* ℂ) x'' x.P.g hgC m ζ lev k₀ N.X nn π B aa bb hπ0 hπ1 hfinβ hba hbb' hJ3
      ⟨ε, hε, fun u hu hu' => ?_⟩
    obtain ⟨hsm, x₀, hg₀, lev₀, ϑ₀, hϑ₀, hJ₀, hk⟩ := hAε u hu hu'
    refine ⟨⟨fun i => (hsm i j₁).1, fun i j => (hsm i j).2⟩, x₀, hg₀, lev₀, ?_, hk⟩
    have e3 : ϑ₀ = fun i => ∑' α, (e : C →+* ℂ) (aa i α) * u ^ nn α := funext fun i => hϑ₀ i j₁
    rw [e3] at hJ₀
    exact hJ₀
  have hk := hj₀ j (le_max_left _ _) C (e : C →+* ℂ) x'' hgC ζ lev k₀ hDef
  have h1 : (κ C xC : C) = toF V C u * algebraMap (FractionRing V) C (κ (FractionRing V) x) := by
    rw [hκC, hu, map_mul]
    rfl
  have h2 : c⁻¹ ^ 8 * k₀ = toF V C u * algebraMap (FractionRing V) C (κ (FractionRing V) x) := by
    rw [← hk]
    exact hsc.trans h1
  have h3 := congrArg norm h2
  rw [norm_mul, norm_mul, norm_pow, norm_inv, hk₀, norm_toF_unit hCE u, _root_.mul_one, _root_.one_mul] at h3
  rw [← h3, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 hc))]

end GlobalTheory.MBLow.KapFPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUniformisedFourierFrameAbsOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.key_value_uniformised_fourier_frame_abs_one : ∀ κ : Rule, Rule4 κ → KapF κ := by
  first | exact @GlobalTheory.MBLow.KapFPf.kapF_of_rule4 | exact GlobalTheory.MBLow.KapFPf.kapF_of_rule4 | (intros; apply GlobalTheory.MBLow.KapFPf.kapF_of_rule4 <;> assumption) | exact @GlobalTheory.MBLow.KapFPf.deform_of_series | exact GlobalTheory.MBLow.KapFPf.deform_of_series | (intros; apply GlobalTheory.MBLow.KapFPf.deform_of_series <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitUniformisedOfAbsValueOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteAlgClosedFieldDvrEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteAlgClosedFieldDvrEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.CompleteDvrToComplex

theorem norm_lt_one_of_mem_maximalIdeal {W C : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [NormedField C] (g : W →+* C) (hg : ∀ a, ‖g a‖ ≤ 1) {b : W}
    (hb0 : b ≠ 0) (hb : ‖g b‖ < 1) {a : W} (ha : a ∈ IsLocalRing.maximalIdeal W) : ‖g a‖ < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n := Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)
  have h : ‖g a‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, hc, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)
  exact lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)

theorem norm_le_one_padicComplexInt (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  have hv : ((Valued.v (x : ℂ_[p]) : NNReal) : ℝ) = ‖(x : ℂ_[p])‖ := by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, (show Valuation.RankLeOne.hom' Valued.v = MonoidWithZeroHom.ValueGroup₀.embedding from rfl),
      Valuation.embedding_restrict]
  rw [← hv]
  have : Valued.v (x : ℂ_[p]) ≤ 1 := x.2
  exact_mod_cast this

theorem norm_natCast_prime_lt_one (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have hc : ((p : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by push_cast; rfl
  rw [hc] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem exists_complete_closed_field :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : Algebra (FractionRing V) C), CExt V (IsLocalRing.maximalIdeal V) C ∧ Nonempty (C ≃+* ℂ) := by
  intro V _ _ _ _ hc hf
  let T : Formalism.L2.Pj.CDVR := { V := V }
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hf
  letI : Algebra (FractionRing V) ℂ_[p] := k.toAlgebra
  obtain ⟨eC⟩ := GlobalTheory.MomOne.Inh.nonempty_iso p
  refine ⟨ℂ_[p], inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, this, ⟨?_, ?_⟩, ⟨eC.symm⟩⟩
  · have hle : ∀ r : V, ‖k (algebraMap V (FractionRing V) r)‖ ≤ 1 := fun r => by
      rw [← hk r]
      exact norm_le_one_padicComplexInt p (kO r)
    exact hle
  · have hle : ∀ r : V, ‖(k.comp (algebraMap V (FractionRing V))) r‖ ≤ 1 := fun r => by
      rw [RingHom.comp_apply, ← hk r]
      exact norm_le_one_padicComplexInt p (kO r)
    have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    have hpl : ‖(k.comp (algebraMap V (FractionRing V))) (p : V)‖ < 1 := by
      rw [map_natCast]; exact norm_natCast_prime_lt_one p
    intro r hr
    exact norm_lt_one_of_mem_maximalIdeal _ hle hp0 hpl hr

end GlobalTheory.CompleteDvrToComplex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteAlgClosedFieldDvrEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_algClosed_field_dvr_embedding : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : Algebra (FractionRing V) C), CExt V (IsLocalRing.maximalIdeal V) C ∧ Nonempty (C ≃+* ℂ) := by
  first | exact @GlobalTheory.CompleteDvrToComplex.exists_complete_closed_field | exact GlobalTheory.CompleteDvrToComplex.exists_complete_closed_field | (intros; apply GlobalTheory.CompleteDvrToComplex.exists_complete_closed_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitUniformisedOfAbsValueOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem keyTraitU_of_kapF : ∀ κ : Rule, MBLow.KapF κ → KeyTraitU κ := by
  intro κ hK V _ _ _ _ hcpl hfin D x G _ _ hG U w₀ hN y hy hvec σ hNz hMaps
  obtain ⟨C, i1, i2, i3, i4, i5, i6, hC, hCC⟩ := GlobalTheory.T.exists_complete_algClosed_field_dvr_embedding V hcpl hfin
  obtain ⟨N, ν, hInt⟩ := GlobalTheory.T.exists_degenerationData_values_ultrametric V hcpl D C hC
  obtain ⟨σ₁, f, th, ϑ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.integralSection_expands_integrally_genericFibre V hcpl D x.P G hG U w₀ hN.1 x.th σ hMaps C
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  obtain ⟨hv₁, -, -, -, hv₅, -⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨f', hf', -⟩ := hv₁ ϑ
  obtain ⟨c, rfl⟩ := hv₅ ϑ f' hf'
  have hc : ‖c‖ = 1 := GlobalTheory.T.section_nonzero_fibres_unit_multiple_thetaSeries V hcpl D x.P G hG U σ σ₁ f hNz h1 h2 C hC N ν hInt ϑ c h5 hf'
  have e := hK V hcpl hfin D x G hG U w₀ hN y hy hvec C hC hCC N ν hInt th ϑ c h3 h4 hf'
  rw [hc, one_pow, _root_.one_mul] at e
  exact GlobalTheory.T.exists_unit_of_norm_one_fractionRing_dvr V C hC _ e

end GlobalTheory.KeyEven
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitUniformisedOfAbsValueOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyValue_unit_uniformised_of_absValueOne : ∀ κ : Rule, MBLow.KapF κ → KeyTraitU κ := by
  first | exact @GlobalTheory.KeyEven.keyTraitU_of_kapF | exact GlobalTheory.KeyEven.keyTraitU_of_kapF | (intros; apply GlobalTheory.KeyEven.keyTraitU_of_kapF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitTraitsOfUniformisedTraits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitTraitsOfUniformisedTraits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven

theorem dualMapR_eq_of_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (F : DualNumber R →+* DualNumber R')
    (h1 : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h2 : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun a => ?_
  have hx : ∀ (S : Type) [CommRing S] (b : DualNumber S),
      b = algebraMap S (DualNumber S) (TrivSqZeroExt.fst b) + algebraMap S (DualNumber S) (TrivSqZeroExt.snd b) * DualNumber.eps := by
    intro S _ b
    rw [← Algebra.smul_def, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.algebraMap_eq_inl,
      TrivSqZeroExt.inl_fst_add_inr_snd_eq]
  have hF : F a = algebraMap R' (DualNumber R') (f (TrivSqZeroExt.fst a)) +
      algebraMap R' (DualNumber R') (f (TrivSqZeroExt.snd a)) * DualNumber.eps := by
    conv_lhs => rw [hx R a]
    rw [map_add (f := _), map_mul, h1, h1, h2]
  rw [hF, ← Algebra.smul_def, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

theorem keyTrait_of_keyTraitU : ∀ κ : Rule, KeyTraitU κ → KeyTrait κ := by
  intro κ hU V _ _ _ _ hA hF G _ _ L σ x y hSA hUn hLie hNz hKey
  obtain ⟨D, A, U, e, he⟩ := hUn
  obtain ⟨φ, hφe, ψ, F, hPB, hψ, hRig, hTh, hF1, hF2, hv⟩ := hKey
  obtain ⟨θ, hθm, hθφ⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hPB

  obtain ⟨e', he', heR⟩ := GlobalTheory.T.exists_rescaled_iso_preserving_rigidification G U.LG L e he
  obtain ⟨σ', hσ', hnz⟩ := GlobalTheory.T.exists_section_transport_along_generating_iso e' he' U.LG.isLB L.isLB σ
  obtain ⟨w₀, hw₀, hPW⟩ := GlobalTheory.T.exists_iso_cancel_pulled_bundles_germs θ.hom.left φ (pullback.fst G.hom (jK V)) hθφ x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB ψ e' hψ he'
  let U' : Unif (IsLocalRing.maximalIdeal V) D x.P G :=
    { toUnifPre := { U.toUnifPre with gen := θ, gen_hom := hθm, ext := ⟨w₀, hw₀⟩ }, expand := U.expand }
  have hinv : U'.gen.inv.left ≫ pullback.fst G.hom (jK V) = φ := by
    show θ.inv.left ≫ pullback.fst G.hom (jK V) = φ
    rw [← hθφ, ← Category.assoc, ← Over.comp_left, θ.inv_hom_id, Over.id_left, Category.id_comp]
  have hFd := dualMapR_eq_of_map _ F hF1 hF2
  haveI : IsMonHom θ.hom := hθm
  refine hU V hA hF D x G hSA U' w₀ ⟨hw₀, x.rig_gen, ?_⟩ y hLie (fun i => ?_) σ' ?_ ?_
  · exact GlobalTheory.T.iso_preserves_rigidification_at_origin V G x.P.A θ.hom φ hθφ hφe x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB x.rig L.rig U.LG.rig ψ e' w₀ hPW hRig heR
  · show (x.v i).left ≫ (U'.gen.inv.left ≫ pullback.fst G.hom (jK V)) = _
    rw [hinv, hv i, hFd]
  · intro s
    obtain ⟨z, hz, hz'⟩ := hNz s
    exact ⟨z, hz, hnz hz'⟩
  · exact GlobalTheory.T.secMaps_secPull_of_pointwise_germs θ.hom.left φ _ hθφ x.P.L L.L U.LG.L L.isLB ψ e' w₀ hPW x.th σ σ' hTh hσ'

end GlobalTheory.KeyEven

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitTraitsOfUniformisedTraitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyValue_unit_traits_of_uniformised_traits : ∀ κ : Rule, KeyTraitU κ → KeyTrait κ := by
  first | exact @GlobalTheory.KeyEven.keyTrait_of_keyTraitU | exact GlobalTheory.KeyEven.keyTrait_of_keyTraitU | (intros; apply GlobalTheory.KeyEven.keyTrait_of_keyTraitU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEvenClosing

theorem keyGlob : KeyGlob := by
  obtain ⟨κ, hH, hF, -, hT, -, hU, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  have h4 : MBLow.Rule4 κ := ⟨hH, hF, hT, hU⟩
  exact GlobalTheory.T.key_formula_even_degeneration_global_of_local_units κ hH hF (GlobalTheory.T.keyFormulaUnitOverNormalBase_of_familyUnit_of_traits κ hU (GlobalTheory.T.keyValue_unit_traits_of_uniformised_traits κ (GlobalTheory.T.keyValue_unit_uniformised_of_absValueOne κ (GlobalTheory.T.key_value_uniformised_fourier_frame_abs_one κ h4))))

end GlobalTheory.KeyEvenClosing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyFormula_evenDegeneration_global : KeyGlob := by
  first | exact @GlobalTheory.KeyEvenClosing.keyGlob | exact GlobalTheory.KeyEvenClosing.keyGlob | (intros; apply GlobalTheory.KeyEvenClosing.keyGlob <;> assumption)
end
