module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasicHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CorrUniqHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLocTower
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JBridgeInt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.CechHEquivCohOnCechCubeMapOver
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.ClosedHT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NiceBc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpsExHolds
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CoverOfPf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.HOpCover
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.OccMoveHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JTrBc
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jTrBc :
    BcSplits → TrBc.{u} := by
  intro hbc B B' R _ T g Z Y p q s _ _ hs tr htr W r c hc J _ σ hσ hspl x
  have key := (hbc g p q r s hs c hc J σ hσ).2.2 hspl
  exact htr (pullback r g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) J
    (fun j => bcMap g (σ j) (hσ j)) (fun j => bcMap_snd g (σ j) (hσ j)) key x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowCov
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open NumberField IsDedekindDomain UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
universe u v

private theorem ext2 {X B k K T : Scheme.{0}} {p : X ⟶ B} {g₁ : k ⟶ B} {g₂ : K ⟶ k}
    (a b : T ⟶ pullback (pullback.snd p g₁) g₂)
    (h1 : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _)
    (h2 : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ ≫ pullback.fst _ _) : a = b := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h2
    · simp only [Category.assoc, pullback.condition]
      rw [reassoc_of% h1]
  · exact h1

private theorem bcComp {B B' X Y Z : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : Z ⟶ B'}
    (f₁ : Z ⟶ Y) (f₂ : Y ⟶ X) (h₁ : f₁ ≫ q = r) (h₂ : f₂ ≫ p = q) (h : (f₁ ≫ f₂) ≫ p = r) :
    bcMap g (f₁ ≫ f₂) h = bcMap g f₁ h₁ ≫ bcMap g f₂ h₂ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcMap_fst]
    rw [← Category.assoc (bcMap g f₁ h₁), bcMap_fst, Category.assoc]
  · simp only [Category.assoc, bcMap_snd]

private theorem bcCongr {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {f f' : Y ⟶ X}
    (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) : bcMap g f h = bcMap g f' h' := by
  subst e; rfl

private theorem square {B B' k K X Y : Scheme.{0}} (gφ : B' ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k) (gO : K ⟶ B')
    {p : X ⟶ B} {q : Y ⟶ B} (u : Y ⟶ X) (h : u ≫ p = q)
    (eX : pullback (pullback.snd p gφ) gO ⟶ pullback (pullback.snd p g₁) g₂)
    (eY : pullback (pullback.snd q gφ) gO ⟶ pullback (pullback.snd q g₁) g₂)
    (hX1 : eX ≫ pullback.snd _ _ = pullback.snd _ _)
    (hX2 : eX ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _)
    (hY1 : eY ≫ pullback.snd _ _ = pullback.snd _ _)
    (hY2 : eY ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _) :
    bcMap gO (bcMap gφ u h) (bcMap_snd _ _ _) ≫ eX = eY ≫ bcMap g₂ (bcMap g₁ u h) (bcMap_snd _ _ _) := by
  apply ext2
  · simp only [Category.assoc, hX1, hY1, bcMap_snd]
  · simp only [Category.assoc, hX2, reassoc_of% hY2, bcMap_fst, reassoc_of% bcMap_fst]

private theorem modP (hM : ModBc) (l : ℕ) [Fact l.Prime] (K : FinExt l) {O : Type} [CommRing O] [IsNoetherianRing O]
    (φ : O →+* ↥(CrystallineSemistableComparison.OK l K.1)) {Y : Scheme.{0}} (p : Y ⟶ sp O) (d : ℕ)
    (hs : SmoothOfRelativeDimension d p) (hp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p) :
    (⟨_, pullback.snd p (Spec.map (CommRingCat.ofHom φ))⟩ : CrystallineSemistableComparison.Model l K.1).Sm ∧
      SmoothOfRelativeDimension d (pullback.snd p (Spec.map (CommRingCat.ofHom φ))) := by
  have h : (⟨_, pullback.snd (𝟙 Y ≫ p) (Spec.map (CommRingCat.ofHom φ))⟩ : CrystallineSemistableComparison.Model l K.1).Sm ∧
      SmoothOfRelativeDimension d (pullback.snd (𝟙 Y ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    hM l K φ p d hs hp (𝟙 Y)
  rw [Category.id_comp] at h
  exact h

private theorem galPart (hSp : BcSplits) (hGal : BcGal) {B k K Y T W₀ : Scheme.{0}} (p : Y ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k)
    (s : T ⟶ Y) [IsFinite s] [Etale s] (c₀ : W₀ ⟶ Y) (G : Type) [Group G] [Finite G] (a₀ : G → (W₀ ⟶ W₀)) (n : ℕ)
    (σ₀ : Fin n → (W₀ ⟶ T)) (hG : IsGalois c₀ G a₀) (hS : Splits s c₀ σ₀) :
    ∃ (ha : ∀ x, a₀ x ≫ c₀ ≫ p = c₀ ≫ p) (hσ : ∀ j, σ₀ j ≫ s ≫ p = c₀ ≫ p)
      (hσ₁ : ∀ j, bcMap g₁ (σ₀ j) (hσ j) ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁),
      IsGalois (bcMap g₂ (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _)) G
        (fun x => bcMap g₂ (bcMap g₁ (a₀ x) (ha x)) (bcMap_snd _ _ _)) ∧
      Splits (bcMap g₂ (bcMap g₁ s rfl) rfl) (bcMap g₂ (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _))
        (fun j => bcMap g₂ (bcMap g₁ (σ₀ j) (hσ j)) (hσ₁ j)) := by
  have hac := hG.2.2.2.2.2.1
  have hsc := hS.1
  have ha : ∀ x, a₀ x ≫ c₀ ≫ p = c₀ ≫ p := fun x => by rw [← Category.assoc, hac x]
  have hσ : ∀ j, σ₀ j ≫ s ≫ p = c₀ ≫ p := fun j => by rw [← Category.assoc, hsc j]
  have hσ₁ : ∀ j, bcMap g₁ (σ₀ j) (hσ j) ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ =
      pullback.snd (c₀ ≫ p) g₁ := fun j => by simp only [bcMap_snd]
  refine ⟨ha, hσ, hσ₁, ?_, ?_⟩
  · have hG1 := hGal g₁ p (c₀ ≫ p) c₀ rfl G a₀ ha hG
    exact hGal g₂ (pullback.snd p g₁) (pullback.snd (c₀ ≫ p) g₁) (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _) G _
      (fun x => bcMap_snd _ _ _) hG1
  · obtain ⟨hF, hE, hsp⟩ := hSp g₁ p (s ≫ p) (c₀ ≫ p) s rfl c₀ rfl (Fin n) σ₀ hσ
    haveI := hF
    haveI := hE
    exact (hSp g₂ (pullback.snd p g₁) _ (pullback.snd (c₀ ≫ p) g₁) (bcMap g₁ s rfl) rfl (bcMap g₁ c₀ rfl)
      (bcMap_snd _ _ _) (Fin n) _ hσ₁).2.2 (hsp hS)

private theorem compPart {B k K Y T W₀ : Scheme.{0}} (p : Y ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k) (s t : T ⟶ Y)
    (ht : t ≫ p = s ≫ p) (c₀ : W₀ ⟶ Y) (σ : W₀ ⟶ T) (hσ : σ ≫ s ≫ p = c₀ ≫ p) (hu : (σ ≫ t) ≫ p = c₀ ≫ p)
    (hσ₁ : bcMap g₁ σ hσ ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁)
    (ht' : bcMap g₁ t ht ≫ pullback.snd p g₁ = bcMap g₁ s rfl ≫ pullback.snd p g₁) :
    bcMap g₂ (bcMap g₁ (σ ≫ t) hu) (bcMap_snd _ _ _) = bcMap g₂ (bcMap g₁ σ hσ) hσ₁ ≫ bcMap g₂ (bcMap g₁ t ht) ht' := by
  have h' : (bcMap g₁ σ hσ ≫ bcMap g₁ t ht) ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁ := by
    simp only [Category.assoc, ht', hσ₁]
  exact (bcCongr g₂ (bcComp g₁ σ t hσ ht hu) _ h').trans (bcComp g₂ _ _ hσ₁ ht' h')

set_option maxHeartbeats 4000000 in
theorem UpperTheory.Gal.G3.jLowCov :
    GalClosD → BcSplits → BcGal → GenIso → ModBc → LowCov := by
  intro hGC hSp hGal hGI hM E _ _ l _ H θ w C D K τK hτ
  let φ : Ow w →+* CrystallineSemistableComparison.OK l K.1 :=
    RingHom.codRestrict (τK.comp (HeightOneSpectrum.valuation E w).valuationSubring.subtype) _
      (fun x => GroundTheory.PAdicHodge.mem_normInteger.mpr (hτ x))
  have hφ : ∀ x : Ow w, algebraMap (CrystallineSemistableComparison.OK l K.1) K.1 (φ x) = τK (algebraMap (Ow w) E x) := fun x => rfl
  obtain ⟨d₀, hd₀⟩ := C.dim
  obtain ⟨eZ, hZ1, hZ2⟩ := hGI φ τK hφ C.p
  have hMZ := modP hM l K φ C.p d₀ hd₀ C.proj
  refine ⟨⟨_, pullback.snd C.p (Spec.map (CommRingCat.ofHom φ))⟩, eZ,
    ⟨hMZ.1, ⟨d₀, hMZ.2⟩, eZ, hZ1⟩, hZ1, fun g => ?_⟩
  have hfet := D.fet g
  haveI := hfet.1
  haveI := hfet.2.1
  obtain ⟨W₀, c₀, G, _, _, a₀, σ₀, hG, hS⟩ := hGC (D.s g) (D.d g) (D.fet g)
  obtain ⟨ha, hσ, hσ₁, hGal', hSpl⟩ := galPart hSp hGal C.p (gen (Ow w) E)
    (Spec.map (CommRingCat.ofHom τK)) (D.s g) c₀ G a₀ (D.d g) σ₀ hG hS
  haveI := hG.1
  haveI := hG.2.1
  have hMW := hM l K φ C.p d₀ hd₀ C.proj c₀
  obtain ⟨eW, hW1, hW2⟩ := hGI φ τK hφ (c₀ ≫ C.p)
  have hu : ∀ i, (σ₀ i ≫ D.t g) ≫ C.p = c₀ ≫ C.p := fun i => by
    rw [Category.assoc, D.comm g, ← Category.assoc, hS.1 i]
  have ht' : bcMap (gen (Ow w) E) (D.t g) (D.comm g) ≫ pullback.snd C.p (gen (Ow w) E) =
      bcMap (gen (Ow w) E) (D.s g) rfl ≫ pullback.snd C.p (gen (Ow w) E) := by
    simp only [bcMap_snd]
  refine ⟨_, bcMap (Spec.map (CommRingCat.ofHom τK)) (bcMap (gen (Ow w) E) c₀ rfl) (bcMap_snd _ _ _),
    G, inferInstance, inferInstance, _, Fin (D.d g), inferInstance,
    fun i => bcMap (Spec.map (CommRingCat.ofHom τK)) (bcMap (gen (Ow w) E) (σ₀ i) (hσ i)) (hσ₁ i), hGal', ?_,
    ⟨_, pullback.snd (c₀ ≫ C.p) (Spec.map (CommRingCat.ofHom φ))⟩, eW,
    ⟨hMW.1, ⟨d₀, hMW.2⟩, eW, ?_⟩,
    ⟨bcMap (Spec.map (CommRingCat.ofHom φ)) c₀ rfl, bcMap_snd _ _ _, ?_⟩,
    fun i => ⟨bcMap (Spec.map (CommRingCat.ofHom φ)) (σ₀ i ≫ D.t g) (hu i), bcMap_snd _ _ _, ?_⟩⟩
  · exact hSpl
  · exact (congrArg (eW.hom ≫ ·) (bcMap_snd _ _ _)).trans hW1
  · exact square (Spec.map (CommRingCat.ofHom φ)) (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK))
      (gen (CrystallineSemistableComparison.OK l K.1) K.1) c₀ rfl eZ.hom eW.hom hZ1 hZ2 hW1 hW2
  · have hcp := compPart C.p (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK)) (D.s g) (D.t g) (D.comm g)
      c₀ (σ₀ i) (hσ i) (hu i) (hσ₁ i) ht'
    have hsq := square (Spec.map (CommRingCat.ofHom φ)) (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK))
      (gen (CrystallineSemistableComparison.OK l K.1) K.1) (σ₀ i ≫ D.t g) (hu i) eZ.hom eW.hom hZ1 hZ2 hW1 hW2
    exact hsq.trans (congrArg (eW.hom ≫ ·) hcp)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHOmega
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHOmega :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_forms → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_sections → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_omega := by
  intro hE hF hS hA k k' _ _ _ J e X X' s s' g h a V hV
  letI := algΓ s
  letI := algΓ s'
  haveI : IsAffineHom g := hA k k' (algebraMap k k') X X' s s' g h
  have hV' : IsAffineOpen (g ⁻¹ᵁ V) := hV.preimage g
  have hForms : IsBC e (formPullS h.w V a) :=
    hF k k' J e _ _ _ (semiHom_appSecS h.w V) (hS k k' J e X X' s s' g h V hV) a
  refine hE k k' J e _ _ _ _ (formPullS h.w V a) (omSecEquiv s a ⟨V, hV⟩).symm
    (omSecEquiv s' a ⟨g ⁻¹ᵁ V, hV'⟩) _ (fun x ↦ ?_) hForms
  obtain ⟨y, rfl⟩ := (omSecEquiv s a ⟨V, hV⟩).surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact omegaPullS_toOmega h.w a V y
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIsBC
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

private theorem iInf_pre {X X' : Scheme.{0}} (g : X' ⟶ X) {n : ℕ} (U : Fin n → X.Opens)
    (S : Finset (Fin n)) : (⨅ i ∈ S, g ⁻¹ᵁ U i) = g ⁻¹ᵁ (⨅ i ∈ S, U i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S _ ih
    rw [Finset.iInf_insert, Finset.iInf_insert, Scheme.Hom.preimage_inf, ih]

private theorem pull_isBC (pE : P_equiv) (pC : P_cube) (pA : P_affine) (pV : P_cover)
    (pO : P_omega) (pH : P_cech) {k k' : Type} [Field k] [Field k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X)
    (h : IsPullback g s' s (spMap (algebraMap k k'))) [IsProper s] (a b : ℕ) :
    IsBC e (hodgePullS h.w a b) := by
  letI := algΓ s
  letI := algΓ s'
  obtain ⟨n, U, hc, hU⟩ := pV k X s
  haveI : IsAffineHom g := pA k k' (algebraMap k k') X X' s s' g h
  have hc' : ⨆ i, g ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  have hU' : ∀ S : Finset (Fin n), S.Nonempty → IsAffineOpen (⨅ i ∈ S, g ⁻¹ᵁ U i) := by
    intro S hS
    rw [iInf_pre]
    exact IsAffineHom.isAffine_preimage _ (hU S hS)
  have hcube : IsBC e
      ((cechCubeMapOver ⊤ U (appTop_algebraMapS h.w) (omegaPullS h.w a)).homology b) := by
    apply pC k k' J e (Fin n)
    intro S hS
    have hA : IsAffineOpen (cechOpen ⊤ U S) := by
      rw [cechOpen, top_inf_eq]
      exact hU S hS
    refine pE k k' J e _ _ _ _
      (sectionsOn.mapOver (appTop_algebraMapS h.w) (omegaPullS h.w a) (cechOpen ⊤ U S))
      (LinearEquiv.refl k _) (sectionsOn.congrOpens k' _ (preimage_cechOpen g ⊤ U S)) _ ?_
      (pO k k' J e X X' s s' g h a _ hA)
    intro x
    exact (sectionsOn.congrOpens_apply k' (Omega s' a) (preimage_cechOpen g ⊤ U S) _).symm
  refine pE k k' J e _ _ _ _ _ (cechHEquivCoh k hc hU (Omega s a) b).symm
    (cechHEquivCoh k' hc' hU' (Omega s' a) b) (hodgePullS h.w a b) ?_ hcube
  intro x
  obtain ⟨y, rfl⟩ := (cechHEquivCoh k hc hU (Omega s a) b).surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact pH k k' X X' s s' g h.w a b n U hc hU hc' hU' y

theorem UpperTheory.Gal.G3.jHBC :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_basis → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cube → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cover → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_omega → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cech → (∀ (k k' : Type) [Field k] [Field k'] (φ : k →+* k') {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (h : IsPullback g s' s (spMap φ)) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (he : IsPullback e r' r (spMap φ)) (f : Y ⟶ X) (hf : f ≫ s = r) (f' : Y' ⟶ X') (hf' : f' ≫ s' = r'), e ≫ f = f' ≫ g → ∀ (a b : ℕ) [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] (y : hodgeH r a b), hodgePullS h.w a b (hodgeTrace hf a b y) = hodgeTrace hf' a b (hodgePullS he.w a b y)) → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HodgeBC := by
  intro pB pE pC pA pV pO pH pT k k' _ _ φ
  refine ⟨fun s s' g h a b ↦ hodgePullS h.w a b, ?_, ?_⟩
  · intro X X' s s' g h _ a b I c
    letI : Algebra k k' := φ.toAlgebra
    have h₀ : IsPullback g s' s (spMap (algebraMap k k')) := h
    exact pB k k' _ (Module.Basis.ofVectorSpace k k') _ _ (hodgePullS h₀.w a b)
      (pull_isBC pE pC pA pV pO pH _ s s' g h₀ a b) I c
  · intro X X' Y Y' s s' g h r r' e he f hf f' hf' w a b
    exact ⟨fun x ↦ hodgePullS_nat_pull h.w he.w hf hf' w a b x,
      fun y ↦ pT k k' φ s s' g h r r' e he f hf f' hf' w a b y⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHFun
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHFun :
    ∀ (k k' : Type) [Field k] [Field k'] {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (f : Y ⟶ X) (f' : Y' ⟶ X') [IsFinite f] [Etale f] [IsFinite f'] [Etale f'], IsPullback e f' f g → ∀ (U : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen (g ⁻¹ᵁ U)) (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b : Sec r (f ⁻¹ᵁ U)), appSecS s s' g U (secTrace s r hU b) = secTrace s' r' hU' (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b)) := by
  intro k k' _ _ X X' Y Y' s s' g r r' e f f' _ _ _ _ H U hU hU' hle b
  have hfU : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hUY : f' ⁻¹ᵁ (g ⁻¹ᵁ U) = e ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ f' ⁻¹ᵁ (g ⁻¹ᵁ U) := (inf_eq_right.mpr hle).symm
  have hP := (isIso_pushoutSection_iff H (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    le_rfl le_rfl hUY).mp (isIso_pushoutSection_of_isAffineOpen H le_rfl le_rfl hUY hU hU' hfU)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at hP
  letI iBC : Algebra (Sec s U) (Sec s' (g ⁻¹ᵁ U)) := (appSecS s s' g U).toAlgebra
  letI iBB : Algebra (Sec s U) (Sec r (f ⁻¹ᵁ U)) := secAlg s r f U
  letI iCC : Algebra (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) := secAlg s' r' f' (g ⁻¹ᵁ U)
  letI iBC' : Algebra (Sec r (f ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    ((Sec.res r' hle).toRingHom.comp (appSecS r r' e (f ⁻¹ᵁ U))).toAlgebra
  letI iBX : Algebra (Sec s U) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    ((algebraMap (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U)))).comp
      (algebraMap (Sec s U) (Sec s' (g ⁻¹ᵁ U)))).toAlgebra
  haveI t1 : IsScalarTower (Sec s U) (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI t2 : IsScalarTower (Sec s U) (Sec r (f ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    IsScalarTower.of_algebraMap_eq (fun x => (congrArg (fun φ => CommRingCat.Hom.hom φ x) hP.w).symm)
  haveI := sec_finite (s := s) (s' := r) (f := f) hU
  haveI := sec_etale (s := s) (s' := r) (f := f) hU
  haveI := projective_of_etale (Sec s U) (Sec r (f ⁻¹ᵁ U))
  haveI := sec_finite (s := s') (s' := r') (f := f') hU'
  haveI := sec_etale (s := s') (s' := r') (f := f') hU'
  haveI := projective_of_etale (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U)))
  haveI hPo : Algebra.IsPushout (Sec s U) (Sec s' (g ⁻¹ᵁ U)) (Sec r (f ⁻¹ᵁ U))
      (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    CommRingCat.isPushout_iff_isPushout.mp hP.flip
  exact (algTrace_of_isPushout (B := Sec s U) (B' := Sec r (f ⁻¹ᵁ U)) (C := Sec s' (g ⁻¹ᵁ U))
    (C' := Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) b).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHForms
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN
open KaehlerDifferential
open scoped TensorProduct

namespace UpperTheory.Gal.G3

private theorem isBC_iff {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k' N] [Module k N] [IsScalarTower k k' N] (ψ : M →ₛₗ[algebraMap k k'] N)
    (f : M →ₗ[k] N) (hf : ∀ m, f m = ψ m) : IsBC e ψ ↔ IsBaseChange k' f := by
  classical
  let L : k' ⊗[k] M →ₗ[k] N := TensorProduct.lift
    (((Algebra.linearMap k' (Module.End k' (M →ₗ[k] N))).flip f).restrictScalars k)
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := M) e
  have hL : bcSum e ψ = L.toAddMonoidHom.comp E.symm.toLinearMap.toAddMonoidHom :=
    Finsupp.addHom_ext fun j m ↦ by
      rw [bcSum_single]
      simp [L, E, hf]
  change Function.Bijective (bcSum e ψ) ↔ Function.Bijective L
  rw [hL]
  exact Function.Bijective.of_comp_iff L E.symm.bijective

private theorem isBaseChange_bottom {k k' B B' : Type} [CommRing k] [CommRing k'] [CommRing B]
    [CommRing B'] [Algebra k k'] [Algebra k B] [Algebra k B'] [Algebra B B'] [Algebra k' B']
    [IsScalarTower k B B'] [IsScalarTower k k' B'] [Algebra.IsPushout k k' B B'] {P Q : Type*}
    [AddCommGroup P] [Module B P] [Module k P] [IsScalarTower k B P] [AddCommGroup Q] [Module B' Q]
    [Module B Q] [Module k' Q] [Module k Q] [IsScalarTower B B' Q] [IsScalarTower k' B' Q]
    [IsScalarTower k k' Q] [IsScalarTower k B Q] {u : P →ₗ[B] Q} (hu : IsBaseChange B' u) :
    IsBaseChange k' (u.restrictScalars k) :=
  IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange k k' B B' P).symm ≪≫ₗ hu.equiv.restrictScalars k')
    fun p ↦ by simp

private theorem isBaseChange_map (k k' B B' : Type) [CommRing k] [CommRing k'] [CommRing B]
    [CommRing B'] [Algebra k k'] [Algebra k B] [Algebra k B'] [Algebra B B'] [Algebra k' B']
    [IsScalarTower k B B'] [IsScalarTower k k' B'] [Algebra.IsPushout k k' B B'] :
    IsBaseChange B' (KaehlerDifferential.map k k' B B') := by
  refine IsBaseChange.of_equiv (tensorKaehlerEquiv k k' B B') fun ω ↦ ?_
  have h : ((tensorKaehlerEquiv k k' B B').toLinearMap.restrictScalars B) ∘ₗ
      (TensorProduct.mk B B' Ω[B⁄k] 1) = KaehlerDifferential.map k k' B B' := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    simp [tensorKaehlerEquiv_tmul_D]
  exact LinearMap.congr_fun h ω

theorem jHForms : P_forms := by
  intro k k' _ _ _ J e B B' _ _ _ _ α hα hB j
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra k B' := ((algebraMap k' B').comp (algebraMap k k')).toAlgebra
  haveI : IsScalarTower k k' B' := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower k B B' := .of_algebraMap_eq fun r ↦ (hα.map_algebraMap r).symm
  haveI : Algebra.IsPushout k k' B B' := ⟨(isBC_iff e (semiSl hα) _ fun _ ↦ rfl).1 hB⟩
  have hone (ω : Ω[B⁄k]) : hα.m1 ω = KaehlerDifferential.map k k' B B' ω := by
    induction ω using ind1 with
    | h b c => rw [hα.oneFormMap_smul_semilinear, hα.m1_D, map_smul, map_D]; rfl
    | h0 => simp
    | ha x y hx hy => simp only [map_add (f := _), hx, hy]
  let pull : Om k B j →ₗ[B] Om k' B' j :=
    { toFun := hα.mOm j
      map_add' := map_add _
      map_smul' := fun b x ↦ hα.mOm_smul b x }
  have hpull : exteriorPowerMapOver B' j (KaehlerDifferential.map k k' B B') = pull := by
    apply exteriorPower.linearMap_ext
    ext1 v
    simp only [LinearMap.compAlternatingMap_apply, exteriorPowerMapOver_ιMulti]
    refine Subtype.ext ?_
    change _ = hα.mDR (exteriorPower.ιMulti B j v : DR k B)
    rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
      ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    exact ((hα.mDR_ι (v i)).trans (congrArg ι1 (hone (v i)))).symm
  exact (isBC_iff e (hα.mOm j) _ fun x ↦ LinearMap.congr_fun hpull x).2
    (isBaseChange_bottom (k := k) (k' := k') (B := B) (B' := B')
      (TopForm.isBaseChange_exteriorPower (isBaseChange_map k k' B B') j))

end UpperTheory.Gal.G3

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHEquiv
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHEquiv :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv := by
  intro k k' _ _ _ J e M N M₀ N₀ _ _ _ _ _ _ _ _ ψ E E' ψ₀ h hψ
  let R : (J →₀ M₀) ≃+ (J →₀ M) := Finsupp.mapRange.addEquiv E.toAddEquiv
  have key : ∀ f : J →₀ M₀, bcSum e ψ₀ f = E' (bcSum e ψ (R f)) := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hf, hg]
    | single j m =>
      simp only [R, Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_single]
      rw [bcSum_single, bcSum_single, h, map_smul]
      rfl
  have hfun : ⇑(bcSum e ψ₀) = ⇑E' ∘ ⇑(bcSum e ψ) ∘ ⇑R := funext key
  show Function.Bijective ⇑(bcSum e ψ₀)
  rw [hfun]
  exact E'.bijective.comp (hψ.comp R.bijective)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHTrace
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.G3.HeckeTraceSheaves

section Two
variable {k k' : Type} [CommRing k] [CommRing k'] {φ : k →+* k'}

private theorem omegaPullS_app_toOm {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}
    (hg : g ≫ s = s' ≫ spMap φ) (j : ℕ) (U : X.Opens) (x : OmU s U j) :
    (omegaPullS hg j).app U (toOm s j U x) = toOm s' j (g ⁻¹ᵁ U) (formPullS hg U j x) :=
  omegaPullS_toOmega hg j U x

private theorem formRes_formPullS_eq {X Y' : Scheme.{0}} {s : X ⟶ Sp k} {r' : Y' ⟶ Sp k'} {u v : Y' ⟶ X}
    (w : u = v) (hu : u ≫ s = r' ≫ spMap φ) (hv : v ≫ s = r' ≫ spMap φ) (U : X.Opens)
    (hle : v ⁻¹ᵁ U ≤ u ⁻¹ᵁ U) (j : ℕ) (x : OmU s U j) :
    formRes r' hle j (formPullS hu U j x) = formPullS hv U j x := by
  subst w
  have h := formRes_refl r' (u ⁻¹ᵁ U) (formPullS hu U j x)
  rw [h]

end Two

section Sheaf

variable {k k' : Type} [CommRing k] [CommRing k'] {φ : k →+* k'}
  {X X' Y Y' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}
  {r : Y ⟶ Sp k} {r' : Y' ⟶ Sp k'} {e : Y' ⟶ Y} {f : Y ⟶ X} {f' : Y' ⟶ X'}

private def mid (he : e ≫ r = r' ≫ spMap φ) (w : e ≫ f = f' ≫ g) (a : ℕ) :
    (Scheme.Modules.pushforward f).obj (Omega r a) ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f').obj (Omega r' a)) :=
  (Scheme.Modules.pushforward f).map (omegaPullS he a) ≫
    (Scheme.Modules.pushforwardComp e f).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr w).hom.app _ ≫
        (Scheme.Modules.pushforwardComp f' g).inv.app _

private theorem mid_app (he : e ≫ r = r' ≫ spMap φ) (w : e ≫ f = f' ≫ g) (a : ℕ) (U : X.Opens)
    (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U))
    (y : Γ((Scheme.Modules.pushforward f).obj (Omega r a), U)) :
    (mid he w a).app U y = (Omega r' a).presheaf.map (homOfLE hle).op
      ((omegaPullS he a).app (f ⁻¹ᵁ U) y) := by
  simp [mid]
  rfl

private theorem mid_form (hg : g ≫ s = s' ≫ spMap φ) (he : e ≫ r = r' ≫ spMap φ)
    (hf : f ≫ s = r) (hf' : f' ≫ s' = r') (w : e ≫ f = f' ≫ g) (a : ℕ) (U : X.Opens)
    (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b' : Sec r (f ⁻¹ᵁ U)) (x : OmU s U a) :
    (mid he w a).app U (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x)) =
      toOm r' a (f' ⁻¹ᵁ (g ⁻¹ᵁ U)) (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b') •
        formPull hf' (g ⁻¹ᵁ U) a (formPullS hg U a x)) := by
  have hu : (e ≫ f) ≫ s = r' ≫ spMap φ := by rw [Category.assoc, hf, he]
  have hu' : (f' ≫ g) ≫ s = r' ≫ spMap φ := by
    rw [Category.assoc, hg, ← Category.assoc, hf']
  have key : formRes r' hle a (formPullS he (f ⁻¹ᵁ U) a (formPull hf U a x)) =
      formPull hf' (g ⁻¹ᵁ U) a (formPullS hg U a x) :=
    ((congrArg (formRes r' hle a) (formPullS_formPull hf he hu U a x)).trans
      (formRes_formPullS_eq w hu hu' U hle a x)).trans (formPull_formPullS hg hf' hu' U a x).symm
  refine (mid_app he w a U hle _).trans ?_
  rw [omegaPullS_app_toOm, res_toOm, formPullS_smul, formRes_smul, key]

private theorem sheaf_lhs [IsFinite f] [Etale f] (hg : g ≫ s = s' ≫ spMap φ) (hf : f ≫ s = r)
    (a : ℕ) {U : X.Opens} (hU : IsAffineOpen U) (b' : Sec r (f ⁻¹ᵁ U)) (x : OmU s U a) :
    (omegaTrace hf a ≫ omegaPullS hg a).app U (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x)) =
      toOm s' a (g ⁻¹ᵁ U) (appSecS s s' g U (secTrace s r hU b') • formPullS hg U a x) := by
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaPullS hg a).app U
    ((omegaTrace hf a).app U (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x))) = _
  rw [omegaTrace_toOm_smul_formPull hf a hU, omegaPullS_app_toOm, formPullS_smul]

private theorem sheaf_rhs [IsFinite f'] [Etale f'] (hg : g ≫ s = s' ≫ spMap φ)
    (he : e ≫ r = r' ≫ spMap φ) (hf : f ≫ s = r) (hf' : f' ≫ s' = r') (w : e ≫ f = f' ≫ g)
    (a : ℕ) {U : X.Opens} (hV : IsAffineOpen (g ⁻¹ᵁ U))
    (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b' : Sec r (f ⁻¹ᵁ U)) (x : OmU s U a) :
    (mid he w a ≫ (Scheme.Modules.pushforward g).map (omegaTrace hf' a)).app U
        (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x)) =
      toOm s' a (g ⁻¹ᵁ U) (secTrace s' r' hV (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b')) •
        formPullS hg U a x) := by
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaTrace hf' a).app (g ⁻¹ᵁ U) ((mid he w a).app U
    (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x))) = _
  rw [mid_form hg he hf hf' w a U hle, omegaTrace_toOm_smul_formPull hf' a hV]

private theorem sheaf_id [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] [IsAffineHom g]
    (hg : g ≫ s = s' ≫ spMap φ) (he : e ≫ r = r' ≫ spMap φ) (hf : f ≫ s = r) (hf' : f' ≫ s' = r')
    (w : e ≫ f = f' ≫ g)
    (hT : ∀ (U : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen (g ⁻¹ᵁ U))
      (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b : Sec r (f ⁻¹ᵁ U)),
      appSecS s s' g U (secTrace s r hU b) =
        secTrace s' r' hV (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b))) (a : ℕ) :
    omegaTrace hf a ≫ omegaPullS hg a =
      mid he w a ≫ (Scheme.Modules.pushforward g).map (omegaTrace hf' a) := by
  refine hom_ext_affine fun U hU y ↦ ?_
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  have hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  obtain ⟨z, rfl⟩ := toOm_surjective (s := r) (j := a) (hU.preimage f) y
  refine formOm_induction (P := fun z ↦ (omegaTrace hf a ≫ omegaPullS hg a).app U
      (toOm r a (f ⁻¹ᵁ U) z) =
    (mid he w a ≫ (Scheme.Modules.pushforward g).map (omegaTrace hf' a)).app U
      (toOm r a (f ⁻¹ᵁ U) z)) hf hU ?_ (fun y z hy hz ↦ ?_) (fun b' x ↦ ?_) z
  · erw [map_zero, map_zero, map_zero]
  · erw [map_add, map_add, map_add]; exact congrArg₂ (· + ·) hy hz
  · rw [sheaf_lhs hg hf a hU, sheaf_rhs hg he hf hf' w a hV hle, hT U hU hV hle b']

end Sheaf

section Coh

private theorem pull_pull {X Y Z : Scheme.{0}} {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R Γ(X, ⊤)] [Algebra S Γ(Y, ⊤)] [Algebra T Γ(Z, ⊤)] {σ : R →+* S} {τ : S →+* T}
    {ρ : R →+* T} {u : Y ⟶ X} {v : Z ⟶ Y} {F : X.Modules} {G : Y.Modules} {L : Z.Modules}
    (hσ : ∀ r, u.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (hτ : ∀ r, v.appTop (algebraMap S Γ(Y, ⊤) r) = algebraMap T Γ(Z, ⊤) (τ r))
    (hρ : ∀ r, (v ≫ u).appTop (algebraMap R Γ(X, ⊤) r) = algebraMap T Γ(Z, ⊤) (ρ r))
    (Φ : F ⟶ (Scheme.Modules.pushforward u).obj G) (Ψ : G ⟶ (Scheme.Modules.pushforward v).obj L)
    (n : ℕ) (x : cohOn F ⊤ n) :
    cohOn.pull hτ Ψ (le_refl (v ⁻¹ᵁ ⊤)) n (cohOn.pull hσ Φ (le_refl (u ⁻¹ᵁ ⊤)) n x) =
      cohOn.pull hρ (Φ ≫ (Scheme.Modules.pushforward u).map Ψ ≫
        (Scheme.Modules.pushforwardComp v u).hom.app L) (le_refl ((v ≫ u) ⁻¹ᵁ ⊤)) n x := by
  apply (cohOn.toH' L _ n).injective
  refine (cohOn.toH'_pull hτ Ψ _ _).trans ?_
  refine Eq.trans ?_ (cohOn.toH'_pull hρ _ _ x).symm
  erw [cohOn.toH'_pull hσ Φ, SheafPull.pull_pull]
  rfl

private theorem comp_pushforwardCongr_rfl_hom_app {X Y : Scheme.{0}} {F : X.Modules} {G : Y.Modules}
    (u : Y ⟶ X) (Φ : F ⟶ (Scheme.Modules.pushforward u).obj G) :
    Φ ≫ (Scheme.Modules.pushforwardCongr (rfl : u = u)).hom.app G = Φ := by
  ext U x
  simp
  rfl

private theorem pull_congr {X Y : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]
    [Algebra R Γ(X, ⊤)] [Algebra S Γ(Y, ⊤)] {σ : R →+* S} {F : X.Modules} {G : Y.Modules}
    {u v : Y ⟶ X} (w : u = v)
    (hu : ∀ r, u.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (hv : ∀ r, v.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (Φ : F ⟶ (Scheme.Modules.pushforward u).obj G) (n : ℕ) (x : cohOn F ⊤ n) :
    cohOn.pull hv (Φ ≫ (Scheme.Modules.pushforwardCongr w).hom.app G)
        (le_refl (v ⁻¹ᵁ ⊤)) n x = cohOn.pull hu Φ (le_refl (u ⁻¹ᵁ ⊤)) n x := by
  subst w
  rw [comp_pushforwardCongr_rfl_hom_app]

end Coh

end UpperTheory.Gal.G3.HeckeTraceSheaves

open UpperTheory.Gal.G3.HeckeTraceSheaves in
theorem UpperTheory.Gal.G3.jHTrace :
    (∀ (k k' : Type) [Field k] [Field k'] {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (f : Y ⟶ X) (f' : Y' ⟶ X') [IsFinite f] [Etale f] [IsFinite f'] [Etale f'], IsPullback e f' f g → ∀ (U : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen (g ⁻¹ᵁ U)) (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b : Sec r (f ⁻¹ᵁ U)), appSecS s s' g U (secTrace s r hU b) = secTrace s' r' hU' (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b))) → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → ∀ (k k' : Type) [Field k] [Field k'] (φ : k →+* k') {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (h : IsPullback g s' s (spMap φ)) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (he : IsPullback e r' r (spMap φ)) (f : Y ⟶ X) (hf : f ≫ s = r) (f' : Y' ⟶ X') (hf' : f' ≫ s' = r'), e ≫ f = f' ≫ g → ∀ (a b : ℕ) [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] (y : hodgeH r a b), hodgePullS h.w a b (hodgeTrace hf a b y) = hodgeTrace hf' a b (hodgePullS he.w a b y) := by
  intro hT hP k k' _ _ φ X X' Y Y' s s' g h r r' e he f hf f' hf' w a b _ _ _ _ y
  haveI : IsAffineHom g := hP k k' φ X X' s s' g h
  have hpb : IsPullback e f' f g := by
    subst hf hf'
    exact IsPullback.of_bot he w h
  have hid := sheaf_id h.w he.w hf hf' w
    (fun U hU hV hle b => hT k k' s s' g r r' e f f' hpb U hU hV hle b) a
  letI := algΓ s
  letI := algΓ s'
  letI := algΓ r
  letI := algΓ r'
  obtain ⟨z, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b).surjective y
  change cohOn.pull (appTop_algebraMapS h.w) (omegaPullS h.w a) _ b
      (cohOn.map k (omegaTrace hf a) ⊤ b
        ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b).symm
          ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b) z))) =
    cohOn.map k' (omegaTrace hf' a) ⊤ b
      ((coh.pushforwardEquiv k' (appTop_algebraMap hf') (Omega r' a) b).symm
        (cohOn.pull (appTop_algebraMapS he.w) (omegaPullS he.w a) _ b
          ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b) z)))
  rw [LinearEquiv.symm_apply_apply]
  refine (cohOn.pull_map (appTop_algebraMapS h.w) (omegaPullS h.w a) (omegaTrace hf a) _ z).trans ?_
  rw [hid]
  refine (cohOn.map_pull (appTop_algebraMapS h.w) (mid he.w w a) (omegaTrace hf' a) _ z).symm.trans ?_
  congr 1
  rw [LinearEquiv.eq_symm_apply]
  have hu : (e ≫ f) ≫ s = r' ≫ spMap φ := by rw [Category.assoc, hf, he.w]
  have hu' : (f' ≫ g) ≫ s = r' ≫ spMap φ := by
    rw [Category.assoc, h.w, ← Category.assoc, hf']
  refine (pull_pull (appTop_algebraMapS h.w) (appTop_algebraMap hf') (appTop_algebraMapS hu')
    (mid he.w w a) (𝟙 _) b z).trans ?_
  refine Eq.trans ?_ (pull_pull (appTop_algebraMap hf) (appTop_algebraMapS he.w)
    (appTop_algebraMapS hu) (𝟙 _) (omegaPullS he.w a) b z).symm
  refine Eq.trans ?_ (pull_congr w (appTop_algebraMapS hu) (appTop_algebraMapS hu') _ b z)
  congr 1

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHBasis
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHBasis :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_basis := by
  classical
  intro k k' _ _ _ J e M N _ _ _ _ ψ hψ I c
  let T : (I →₀ k') ≃+ (J →₀ M) :=
    (Finsupp.mapRange.addEquiv e.repr.toAddEquiv).trans ((Finsupp.curryAddEquiv).symm.trans
      ((Finsupp.domCongr (Equiv.prodComm I J)).trans
        (Finsupp.curryAddEquiv.trans (Finsupp.mapRange.addEquiv c.repr.symm.toAddEquiv))))
  have hTs : ∀ (i : I) (a : k'),
      T (Finsupp.single i a) = Finsupp.mapRange (fun b : k => b • c i) (zero_smul k _) (e.repr a) := by
    intro i a
    ext j
    simp only [Finsupp.mapRange_apply]
    simp [T, Finsupp.curryAddEquiv]
    have h : ((Finsupp.equivMapDomain (Equiv.prodComm I J) (Finsupp.single i (e.repr a)).uncurry).curry j)
        = Finsupp.single i (e.repr a j) := by
      ext i'
      simp only [Finsupp.curry_apply, Finsupp.equivMapDomain_apply, Finsupp.uncurry_apply]
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp_all
    rw [h, Finsupp.linearCombination_single]
  have hbc : ∀ f : J →₀ M, bcSum e ψ f = f.sum (fun j m => e j • ψ m) := by
    intro f
    simp [bcSum]; rfl
  let Φ : (I →₀ k') →ₗ[k'] N := Finsupp.linearCombination k' (fun i => ψ (c i))
  have key : ∀ g, Φ g = bcSum e ψ (T g) := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add (f := _), map_add (f := _), map_add (f := _), hf, hg]
    | single i a =>
      rw [hTs, hbc, Finsupp.sum_mapRange_index (by intro j; simp)]
      simp only [Φ, Finsupp.linearCombination_single]
      conv_lhs => rw [← e.linearCombination_repr a, Finsupp.linearCombination_apply]
      rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smulₛₗ, Algebra.smul_def, mul_comm, mul_smul]
  have hΦ : Function.Bijective Φ := by
    have h : (Φ : (I →₀ k') → N) = bcSum e ψ ∘ T := funext key
    rw [h]
    exact hψ.comp T.bijective
  let E := LinearEquiv.ofBijective Φ hΦ
  refine ⟨Module.Basis.ofRepr E.symm, fun i => ?_⟩
  rw [Module.Basis.coe_ofRepr]
  simp [E, Φ]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHCube
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

section
variable {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k'] {J : Type}
  (e : Module.Basis J k k')

private theorem bcSum_mapRange {M N M' N' : Type} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k' N] [AddCommGroup M'] [Module k M'] [AddCommGroup N'] [Module k' N']
    (ψ : M →ₛₗ[algebraMap k k'] N) (ψ' : M' →ₛₗ[algebraMap k k'] N') (f : M → M') (hf : f 0 = 0)
    (hfa : ∀ a b, f (a + b) = f a + f b) (g : N →ₗ[k'] N') (h : ∀ m, ψ' (f m) = g (ψ m))
    (x : J →₀ M) : bcSum e ψ' (x.mapRange f hf) = g (bcSum e ψ x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapRange_add hfa, map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | single j m => rw [Finsupp.mapRange_single, bcSum_single, bcSum_single, map_smul, h]

private theorem isBC_pi {T : Type} [Finite T] {M N : T → Type} [∀ t, AddCommGroup (M t)]
    [∀ t, Module k (M t)] [∀ t, AddCommGroup (N t)] [∀ t, Module k' (N t)]
    (ψ : ∀ t, M t →ₛₗ[algebraMap k k'] N t)
    (Ψ : (∀ t, M t) →ₛₗ[algebraMap k k'] (∀ t, N t)) (hΨ : ∀ x t, Ψ x t = ψ t (x t))
    (h : ∀ t, IsBC e (ψ t)) : IsBC e Ψ := by
  classical
  have := Fintype.ofFinite T
  have key : ∀ (x : J →₀ ∀ t, M t) t,
      bcSum e Ψ x t = bcSum e (ψ t) (x.mapRange (fun m => m t) rfl) := by
    intro x t
    have := bcSum_mapRange e Ψ (ψ t) (fun m => m t) rfl (fun a b => rfl) (LinearMap.proj t)
      (fun m => (hΨ m t).symm) x
    simpa using this.symm
  constructor
  · intro x y hxy
    ext j t
    have h1 : x.mapRange (fun m => m t) rfl = y.mapRange (fun m => m t) rfl := by
      apply (h t).1
      rw [← key, ← key, hxy]
    have := congrArg (fun z => z j) h1
    simpa using this
  · intro y
    choose x hx using fun t => (h t).2 (y t)
    refine ⟨∑ t, (x t).mapRange (Pi.single t) (Pi.single_zero t), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have hs : ∀ t, bcSum e Ψ ((x t).mapRange (Pi.single t) (Pi.single_zero t)) = Pi.single t (y t) := by
      intro t
      rw [bcSum_mapRange e (ψ t) Ψ (Pi.single t) (Pi.single_zero t)
        (fun a b => Pi.single_add t a b) (LinearMap.single k' N t) ?_ (x t)]
      · simp [hx]
      · intro m
        funext s
        rw [hΨ]
        by_cases hst : s = t
        · subst hst
          simp
        · simp [Pi.single_eq_of_ne hst]
    simp only [hs]
    exact Finset.univ_sum_single y

end

theorem UpperTheory.Gal.G3.jHCube :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cube := by
  unfold P_cube
  intro k k' _ _ _ J e ι _ _ A B ψ hψ
  classical
  have := Fintype.ofFinite ι
  have hT : ∀ q, IsBC e (ψ.term (q + 1)) := by
    intro q
    exact isBC_pi e (fun s : {s : Finset ι // s.card = q + 1} => ψ.app s.1) (ψ.term (q + 1))
      (fun x s => rfl) (fun s => hψ s.1 (Finset.card_pos.1 (by rw [s.2]; omega)))
  have hd : ∀ q (w : J →₀ A.Term q), bcSum e (ψ.term (q + 1)) (w.mapRange (A.d q) (map_zero _))
      = B.d q (bcSum e (ψ.term q) w) := fun q w =>
    bcSum_mapRange e (ψ.term q) (ψ.term (q + 1)) (A.d q) (map_zero _) (fun a b => map_add _ a b)
      (B.d q) (fun m => ψ.term_d q m) w
  have hz : ∀ q (x : J →₀ (A.d q).ker), ((bcSum e (ψ.cocycle q) x : (B.d q).ker) : B.Term q)
      = bcSum e (ψ.term q) (x.mapRange Subtype.val rfl) := fun q x =>
    (bcSum_mapRange e (ψ.cocycle q) (ψ.term q) Subtype.val rfl (fun a b => rfl)
      (B.d q).ker.subtype (fun m => rfl) x).symm
  have hZ : ∀ q, IsBC e (ψ.cocycle (q + 1)) := by
    intro q
    constructor
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      rw [hz, hz] at h1
      have h2 := (hT q).1 h1
      refine Finsupp.ext fun j => Subtype.ext ?_
      simpa using congrArg (fun w => w j) h2
    · intro z
      obtain ⟨w, hw⟩ := (hT q).2 (z : B.Term (q + 1))
      have h0 : w.mapRange (A.d (q + 1)) (map_zero _) = 0 := by
        apply (hT (q + 1)).1
        rw [hd, hw, map_zero]
        exact (LinearMap.mem_ker).1 z.2
      have hw0 : ∀ j, A.d (q + 1) (w j) = 0 := fun j => by
        simpa using congrArg (fun v => v j) h0
      let x : J →₀ (A.d (q + 1)).ker :=
        w.mapRange (fun v => if hv : A.d (q + 1) v = 0 then (⟨v, hv⟩ : (A.d (q + 1)).ker) else 0)
          (by simp; rfl)
      have hxw : x.mapRange Subtype.val rfl = w := by
        ext j
        simp [x, hw0 j]
      refine ⟨x, Subtype.ext ?_⟩
      rw [hz, hxw, hw]
  intro p
  have hH : ∀ x : J →₀ (A.d (p + 1)).ker,
      bcSum e (ψ.homology p) (x.mapRange (cechClass A p) (map_zero _))
        = cechClass B p (bcSum e (ψ.cocycle (p + 1)) x) := fun x =>
    bcSum_mapRange e (ψ.cocycle (p + 1)) (ψ.homology p) (cechClass A p) (map_zero _)
      (fun a b => map_add _ a b) (cechClass B p) (fun m => ψ.homology_cechClass p m) x
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x, rfl⟩ := Finsupp.mapRange_surjective _ (map_zero (cechClass A p))
      (cechClass_surjective A p) c
    rw [hH] at hc
    cases p with
    | zero =>
      rw [cechClass_zero_eq_zero_iff] at hc
      have hx : x = 0 := (hZ 0).1 (by rw [hc, map_zero])
      simp [hx]
    | succ q =>
      rw [cechClass_succ_eq_zero_iff] at hc
      obtain ⟨y, hy⟩ := hc
      obtain ⟨w, rfl⟩ := (hT q).2 y
      rw [← hd, hz] at hy
      have h2 := (hT (q + 1)).1 hy
      ext j
      have hj := congrArg (fun v => v j) h2
      simp only [Finsupp.mapRange_apply] at hj
      simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply]
      rw [cechClass_succ_eq_zero_iff]
      exact ⟨w j, hj⟩
  · intro h
    obtain ⟨z, rfl⟩ := cechClass_surjective B p h
    obtain ⟨x, rfl⟩ := (hZ p).2 z
    exact ⟨_, hH x⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHSections
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR
open PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

namespace UpperTheory.Gal.G3

private theorem secMap_eq_appLE {k : Type} [CommRing k] {X : Scheme.{0}} (s : X ⟶ Sp k) (U : X.Opens) :
    secMap s U = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ U le_top := rfl

private theorem pushout_secMap {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k']
    {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}
    (h : IsPullback g s' s (spMap (algebraMap k k'))) {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout (secMap s V) (CommRingCat.ofHom (algebraMap k k')) (g.app V)
      (secMap s' (g ⁻¹ᵁ V)) := by
  have po := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  refine po.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Scheme.ΓSpecIso (.of k')) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp [secMap_eq_appLE, Scheme.Hom.appLE]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp [secMap_eq_appLE, Scheme.Hom.appLE]

private theorem isBC_semiSl_of_pushout {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {B B' : Type} [CommRing B] [CommRing B'] [Algebra k B] [Algebra k' B']
    {α : B →+* B'} (hα : SemiHom (algebraMap k k') α)
    (H : IsPushout (CommRingCat.ofHom (algebraMap k B)) (CommRingCat.ofHom (algebraMap k k'))
      (CommRingCat.ofHom α) (CommRingCat.ofHom (algebraMap k' B'))) : IsBC e (semiSl hα) := by
  classical
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra k B' := ((algebraMap k' B').comp (algebraMap k k')).toAlgebra
  haveI : IsScalarTower k k' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun r ↦
    (congrArg (fun q ↦ q.hom r) H.w).symm
  have P : Algebra.IsPushout k k' B B' := CommRingCat.isPushout_iff_isPushout.1 H.flip
  have key : (bcSum e (semiSl hα) : (J →₀ B) → B') =
      P.out.equiv ∘ (TensorProduct.equivFinsuppOfBasisLeft e).symm := by
    funext x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), Function.comp_apply, hx, hy] at *
    | single j b =>
      rw [bcSum_single, Function.comp_apply, TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
        Finsupp.sum_single_index (by simp), IsBaseChange.equiv_tmul]
      rfl
  unfold IsBC
  rw [key]
  exact P.out.equiv.bijective.comp (TensorProduct.equivFinsuppOfBasisLeft e).symm.bijective

theorem jHSections : P_sections := by
  intro k k' _ _ _ J e X X' s s' g h V hV
  exact isBC_semiSl_of_pushout e (semiHom_appSecS h.w V) (pushout_secMap h hV)

end UpperTheory.Gal.G3

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHAffine
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

theorem UpperTheory.Gal.G3.jHAffine :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine := by
  intro k k' _ _ φ X X' s s' g h
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHCover
open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.G3

theorem jHCover : PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cover := by
  intro k _ X s _
  haveI : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from s]; infer_instance⟩
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  let C := X.affineCover.finiteSubcover
  let e := Fintype.equivFin C.I₀
  refine ⟨Fintype.card C.I₀, fun i => (C.f (e.symm i)).opensRange, ?_, ?_⟩
  · rw [e.symm.surjective.iSup_comp (fun j => (C.f j).opensRange)]
    exact C.iSup_opensRange
  · intro S hS
    have h := IsAffineOpen.biInf (X := X) (S : Set (Fin (Fintype.card C.I₀))) S.finite_toSet
      (Finset.coe_nonempty.mpr hS) (U := fun i => (C.f (e.symm i)).opensRange)
      (fun i _ => isAffineOpen_opensRange _)
    simpa only [Finset.mem_coe] using h

end UpperTheory.Gal.G3
end

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G3

theorem seamHopEx_holds : UpperTheory.Gal.Seam.HopEx := by
  intro l _ k Ω _ _ _ _ _ H hN g
  obtain ⟨d, hd⟩ := hN.2.2 g
  have hl : (l : k) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap k Ω) h
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  exact (hopSpec_holds l hl H Ω g d hd).1

theorem locTower_holds : UpperTheory.Gal.Seam.LocTower := locTower_of vBcS_holds seamHopEx_holds UpperTheory.Gal.Seam.niceBc

theorem traceSplit_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.TraceSplit := by
  intro k _ Z Y W q s _ _ c _ _ I _ σ hσ hS a b y
  exact hodgeTr_holds k a b q (s ≫ q) s rfl W (c ≫ q) c rfl I σ hσ hS y

theorem hodgeBC_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.HodgeBC :=
  jHBC jHBasis jHEquiv jHCube jHAffine jHCover (jHOmega jHEquiv jHForms jHSections jHAffine) PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.cech_holds
    (jHTrace jHFun jHAffine)

theorem coverOp_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.CoverOp := jCoverOp etnGood_holds @bcSplits_holds @bcGal_holds corrUniq_holds

theorem lowHodge_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowHodge :=
  jLowHodge hodgeGood_holds @bcGood_holds.{0} fEtBasic_holds
    (jHodgeOpBc @bcSplits_holds hodgeTr_holds (jTrBc.{0} @bcSplits_holds)) @coverInv_holds.{0} @liesOp_holds.{0}

theorem hopLies_holds : HopLies := jHopLies etGood_holds @bcGood_holds.{1} fEtBasic_holds hopSpec_holds @liesOp_holds.{1}

theorem lowPiece_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowPiece := jLowPiece hopLies_holds pieceLe_holds

private theorem jGenIso : GenIso := by
  intro O O' k K _ _ _ _ _ _ φ τ h X p
  have hg : gen O' K ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom τ) ≫ gen O k := by
    simp only [gen, ← Spec.map_comp]
    congr 1
    ext x
    simpa using h x
  refine ⟨pullbackLeftPullbackSndIso p (Spec.map (CommRingCat.ofHom φ)) (gen O' K) ≪≫
    pullback.congrHom rfl hg ≪≫
    (pullbackLeftPullbackSndIso p (gen O k) (Spec.map (CommRingCat.ofHom τ))).symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd]
    rw [pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  · simp only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_fst]
    rw [pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

theorem lowCov_holds : LowCov :=
  jLowCov @galClosD_holds @bcSplits_holds @bcGal_holds @jGenIso (jModBc UpperTheory.Gal.Seam.goodOf)

theorem jumpStep_of (hS : CrystallineSemistableComparison.HTSpecB.HTSpecGood) (hC : CrysStep) (hR : RepEx) : JumpStep :=
  PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpStep_of
    (PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpCore_of hS (jLowNice fEtBasic_holds) lowHodge_holds lowPiece_holds (matEx_of hR)
      (jLocalMat UpperTheory.Gal.Seam.niceBc seamHopEx_holds locTower_holds) (coverLow_of_cov PositivityTheory.AutomorphicGaloisHodgeTate.G8.coverOf lowCov_holds)
      (jBridgeInt UpperTheory.Gal.Seam.intMap) (jBCTower UpperTheory.Gal.Seam.niceBc)
      (PositivityTheory.AutomorphicGaloisHodgeTate.G8.locE_of hodgeBC_holds traceSplit_holds coverOp_holds) PositivityTheory.AutomorphicGaloisHodgeTate.G8.OccMove_holds
      PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpsEx_holds jConjBridge jJumpOfHT2) hC

end UpperTheory.Gal.G3
