module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndGeometricallyConnectedOfIsNilpotent
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilProper

theorem isSeparated_of_comp_surjective {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  let m := pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp)
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have hcomm : pullback.diagonal (j ≫ f) ≫ m = j ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.diagonal_fst_assoc]
      simp
    · rw [Category.assoc, pullback.lift_snd, pullback.diagonal_snd_assoc]
      simp
  have key : m '' Set.range (pullback.diagonal (j ≫ f)) = Set.range (pullback.diagonal f) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨j x, by rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := j.surjective y
      exact ⟨_, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]⟩
  refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rw [← key]
  exact m.isClosedMap _ (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range

theorem surjective_specMap_mk (A : Type) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) :
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  obtain ⟨n, hn⟩ := hJ
  have hle : J ≤ nilradical A := fun x hx ↦ by
    rw [mem_nilradical]
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hle).2⟩

theorem isProper_and_geometricallyConnected_of_isNilpotent :
    ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (Y : Over (Spec (CommRingCat.of A))) [LocallyOfFiniteType Y.hom], (IsProper (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → IsProper Y.hom) ∧ (GeometricallyConnected (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → GeometricallyConnected Y.hom) := by
  intro A _ J hJ Y _
  have hsq : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap_mk A J hJ
  have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨fun hP ↦ ?_, fun hG ↦ ?_⟩
  · have hcomp : IsProper (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
        ≫ Y.hom) := by
      rw [pullback.condition]
      infer_instance
    have : IsSeparated Y.hom :=
      isSeparated_of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom
    have : UniversallyClosed Y.hom :=
      UniversallyClosed.of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom
    exact { toIsSeparated := ‹_›, toUniversallyClosed := ‹_›, toLocallyOfFiniteType := ‹_› }
  · rw [geometricallyConnected_iff] at hG ⊢
    intro K _ y Z fst snd h
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    have hker : ∀ x ∈ J, φ.hom x = 0 := by
      obtain ⟨n, hn⟩ := hJ
      intro x hx
      have hx' : x ^ n = 0 := by
        have := Ideal.pow_mem_pow hx n
        rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      exact (IsNilpotent.map ⟨n, hx'⟩ φ.hom).eq_zero
    let ψ := Ideal.Quotient.lift J φ.hom hker
    have hφ : φ = CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom ψ := by
      ext x
      simp [ψ]
    rw [hφ, Spec.map_comp] at h
    let p : Z ⟶ pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
      pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [h.w, Category.assoc])
    apply hG (Spec.map (CommRingCat.ofHom ψ)) p snd
    have e : p ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = fst :=
      pullback.lift_fst _ _ _
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [e]
    exact h

end GlobalTheory.NilProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackPullbackMap
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusExtBaseChange

theorem isPullback_pullback_map {S S' : Scheme.{0}} (f : S' ⟶ S) {G B : Over S} (q : G ⟶ B) :
    IsPullback (pullback.fst G.hom f) ((Over.pullback f).map q).left q.left (pullback.fst B.hom f) := by
  have h1 : ((Over.pullback f).map q).left ≫ pullback.fst B.hom f = pullback.fst G.hom f ≫ q.left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback f).map q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_bot ?_ h1.symm (IsPullback.of_hasPullback B.hom f)
  rw [h2, Over.w q]
  exact IsPullback.of_hasPullback _ _

theorem exists_extension {S S' : Scheme.{0}} (f : S' ⟶ S) {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    {T' G' B' : Over S'} [GrpObj T'] [GrpObj G'] [GrpObj B']
    (eT : T' ≅ (Over.pullback f).obj T) (eG : G' ≅ (Over.pullback f).obj G)
    (eB : B' ≅ (Over.pullback f).obj B) [IsMonHom eT.hom] [IsMonHom eG.hom] [IsMonHom eB.hom]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] (hf : Flat q.left) (hs : Surjective q.left)
    (ha : IsAffineHom q.left) (hk : IsPullback i (toUnit _) q η[B]) :
    ∃ (q' : G' ⟶ B') (i' : T' ⟶ G'), IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧
      IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' η[B'] ∧
      q'.left ≫ eB.hom.left ≫ pullback.fst B.hom f = (eG.hom.left ≫ pullback.fst G.hom f) ≫ q.left ∧
      i'.left ≫ eG.hom.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst T.hom f) ≫ i.left := by
  have pq := isPullback_pullback_map f q
  have pi := isPullback_pullback_map f i
  have iG : IsIso eG.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eG.hom))
  have iB : IsIso eB.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eB.inv))
  have hf' : Flat ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq hf
  have hs' : Surjective ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq hs
  have ha' : IsAffineHom ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq ha
  refine ⟨eG.hom ≫ (Over.pullback f).map q ≫ eB.inv, eT.hom ≫ (Over.pullback f).map i ≫ eG.inv,
    inferInstance, ?_, ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · refine (hk.map (Over.pullback f)).of_iso eT.symm eG.symm
      (Functor.Monoidal.εIso (Over.pullback f)).symm eB.symm ?_ (toUnit_unique _ _) ?_ ?_
    · simp
    · simp
    · have : η[(Over.pullback f).obj B] ≫ eB.inv = η[B'] := IsMonHom.one_hom _
      rw [← this, Functor.obj.η_def]
      simp
  · rw [← Over.comp_left_assoc, Category.assoc, Category.assoc, eB.inv_hom_id, Category.comp_id,
      Over.comp_left, Category.assoc, Category.assoc, pq.w]
  · rw [← Over.comp_left_assoc, Category.assoc, Category.assoc, eG.inv_hom_id, Category.comp_id,
      Over.comp_left, Category.assoc, Category.assoc, pi.w]

theorem exists_iso_of_square {S S' S₀ S₀' : Scheme.{0}} (f : S' ⟶ S) (f₀ : S₀' ⟶ S₀) (j : S₀ ⟶ S)
    (j' : S₀' ⟶ S') (w : j' ≫ f = f₀ ≫ j) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
    (bc : G' ≅ (Over.pullback f).obj G) [IsMonHom bc.hom] :
    ∃ e : (Over.pullback j').obj G' ≅ (Over.pullback f₀).obj ((Over.pullback j).obj G), IsMonHom e.hom ∧
      e.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom f₀ ≫ pullback.fst G.hom j =
        pullback.fst G'.hom j' ≫ bc.hom.left ≫ pullback.fst G.hom f :=
  Geo.Tor.grpPullback_iso
    (((Geo.Tor.isGrpPullback_pullback G' j').comp
      (((Geo.Tor.isGrpPullback_of_iso bc).comp (Geo.Tor.isGrpPullback_pullback G f)).congr
        (Category.id_comp _) rfl)).congr w rfl)
    ((Geo.Tor.isGrpPullback_pullback _ f₀).comp (Geo.Tor.isGrpPullback_pullback G j))

theorem exists_splitTorus_iso {S S' : Scheme.{0}} (f : S' ⟶ S) {X X' : Type} [AddCommGroup X]
    [AddCommGroup X'] (xe : X' ≃+ X) :
    ∃ e : splitTorus S' X' ≅ (Over.pullback f).obj (splitTorus S X), IsMonHom e.hom ∧
      ∀ x : X', (e.hom.left ≫ pullback.fst (splitTorus S X).hom f).appTop.hom (charUnit S X (xe x)).val =
        (charUnit S' X' x).val := by
  obtain ⟨e, he, hc⟩ := splitTorus_baseChange S S' f X
  let e₀ : splitTorus S' X' ≅ splitTorus S' X :=
    { hom := SplitTorus.torusMap S' xe.symm.toAddMonoidHom
      inv := SplitTorus.torusMap S' xe.toAddMonoidHom
      hom_inv_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]; congr 1; ext; simp
      inv_hom_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]; congr 1; ext; simp }
  have : IsMonHom e₀.hom := SplitTorus.isMonHom_torusMap _
  refine ⟨e₀ ≪≫ e, inferInstanceAs (IsMonHom (e₀.hom ≫ e.hom)), fun x => ?_⟩
  rw [Iso.trans_hom, Over.comp_left, Category.assoc, Rosenlicht.appTop_comp_apply, hc,
    SplitTorus.charUnit_val, SplitTorus.charUnit_val]
  refine (SplitTorus.torusMap_appTop_chi xe.symm.toAddMonoidHom (xe x)).trans ?_
  simp

end TorusExtBaseChange

open TorusExtBaseChange in
theorem gtCoord_baseChange_maps : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (I : Ideal R) (I' : Ideal R'), I.map φ ≤ I' → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (e : ℕ) (g : GtCoord I D e G), ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) (q' : thickObj R' I' e G' ⟶ thickObj R' I' e D'.P.A) (i' : splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X ⟶ thickObj R' I' e G'), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧ IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' (η[thickObj R' I' e D'.P.A]) ∧ ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ g.pG.left ∧ ∃ hT : (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, i'.left ≫ h = hT ≫ g.i.left ∧ ∀ x : D'.X, hT.appTop.hom (charUnit _ D.X (hD.xe x)).val = (charUnit _ D'.X x).val := by
  intro R R' _ _ _ _ φ D D' hD I I' hI G _ _ G' _ _ bc hbc e g
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hI _
  let f₀ : Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ hle))
  have w : thick R' I' e ≫ specOf φ = f₀ ≫ thick R I e := by
    simp only [f₀, thick, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
  have := hD.e_hom
  have := g.q_hom
  have := g.i_hom
  obtain ⟨eG, mG, hG⟩ := exists_iso_of_square _ f₀ _ _ w G G' bc
  obtain ⟨eB, mB, hB⟩ := exists_iso_of_square _ f₀ _ _ w D.P.A D'.P.A hD.e
  obtain ⟨eT, mT, hT⟩ := exists_splitTorus_iso f₀ hD.xe
  obtain ⟨q', i', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_extension f₀ eT eG eB g.i g.q g.q_flat g.q_surj g.q_affine g.isKernel
  refine ⟨eG.hom.left ≫ pullback.fst _ f₀, q', i', ?_, h1, h2, h3, h4, h5, h6, ?_, _, h8, hT⟩
  · exact (Category.assoc _ _ _).trans hG
  · change (q'.left ≫ pullback.fst D'.P.A.hom (thick R' I' e)) ≫ _ =
      _ ≫ g.q.left ≫ pullback.fst D.P.A.hom (thick R I e)
    rw [Category.assoc, ← hB, ← Category.assoc _ g.q.left, ← h7]
    simp only [Category.assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPushoutQuotientMap
namespace GlobalTheory.NilpotentLift

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.GlobalTheory.NilpotentLift.isPushout_quotient_map {A : Type} [CommRing A] (J : Ideal A) {B : CommRingCat.{0}}
    (σ : CommRingCat.of A ⟶ B) :
    IsPushout σ (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap (J.map σ.hom) σ.hom Ideal.le_comap_map)) := by
  refine IsPushout.of_isColimit' (CommSq.mk ?_) ?_
  · ext a
    simp [Ideal.quotientMap_mk]
  · have key : ∀ s : PushoutCocone σ (CommRingCat.ofHom (Ideal.Quotient.mk J)),
        J.map σ.hom ≤ RingHom.ker s.inl.hom := by
      intro s
      rw [Ideal.map_le_iff_le_comap]
      intro j hj
      have h := congrArg (fun φ => φ.hom j) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      simp [RingHom.mem_ker, h, Ideal.Quotient.eq_zero_iff_mem.mpr hj]
    refine PushoutCocone.IsColimit.mk _
      (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (fun a ha => key s ha)))
      (fun s => ?_) (fun s => ?_) (fun s m h₁ _ => ?_)
    · ext b
      exact Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)
    · ext a
      have h := congrArg (fun φ => φ.hom a) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact (Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)).trans h
    · ext b
      have h := congrArg (fun φ => φ.hom b) h₁
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact h.trans (Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)).symm

theorem _root_.GlobalTheory.NilpotentLift.main : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J →
    ∀ (G Y : Over (Spec (CommRingCat.of A))) [Smooth G.hom] [IsAffine Y.left]
      (f₀ : pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⟶ G.left),
      f₀ ≫ G.hom = pullback.fst _ _ ≫ Y.hom →
      (∃ W : G.left.Opens, IsAffineOpen W ∧ f₀ ⁻¹ᵁ W = ⊤) →
      ∃ f : Y ⟶ G, pullback.fst _ _ ≫ f.left = f₀ := by
  intro A _ J hJ G Y _ _ f₀ hf₀ hW
  obtain ⟨W, hWaff, hWtop⟩ := hW
  set e := Y.left.isoSpec with he
  obtain ⟨σ, hσdef⟩ : ∃ σ : CommRingCat.of A ⟶ Γ(Y.left, ⊤),
      σ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Y.hom.appTop := ⟨_, rfl⟩
  have hσ : e.hom ≫ Spec.map σ = Y.hom := by
    have h1 := Scheme.isoSpec_hom_naturality Y.hom
    rw [Scheme.isoSpec_Spec_hom] at h1
    rw [hσdef, Spec.map_comp, ← Category.assoc, he, h1, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have hσ' : e.inv ≫ Y.hom = Spec.map σ := by
    rw [← hσ, Iso.inv_hom_id_assoc]
  have hPB := isPullback_SpecMap_of_isPushout _ _ _ _ (_root_.GlobalTheory.NilpotentLift.isPushout_quotient_map J σ)
  have hPB' : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) ≫ e.inv)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map σ.hom) σ.hom Ideal.le_comap_map)))
      Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsPullback.of_iso hPB (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, hσ'])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
  have hx₀ : (hPB'.isoPullback.hom ≫ f₀) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) ≫ Spec.map σ := by
    rw [Category.assoc, hf₀, IsPullback.isoPullback_hom_fst_assoc, Category.assoc, hσ']
  obtain ⟨x, hx, hxs⟩ := _root_.GlobalTheory.exists_lift_of_smooth_of_isAffineOpen G.hom
    (isAffineOpen_top (Spec (CommRingCat.of A))) hWaff le_top
    (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) (Spec.map σ) (hPB'.isoPullback.hom ≫ f₀) hx₀
    (by simp)
    (by
      rintro _ ⟨y, rfl⟩
      have : hPB'.isoPullback.hom y ∈ f₀ ⁻¹ᵁ W := by rw [hWtop]; trivial
      simpa using this)
    (by
      intro R' A' _ _ _ _ _ _ π' hπ' φ
      have hsurj : Function.Surjective π' := by
        intro c
        obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective c
        exact ⟨b, (hπ' b).trans hb⟩
      have hnil : IsNilpotent (RingHom.ker π'.toRingHom) := by
        obtain ⟨n, hn⟩ := hJ
        refine ⟨n, eq_bot_iff.mpr ?_⟩
        have hle : RingHom.ker π'.toRingHom ≤ J.map σ.hom := fun b hb =>
          Ideal.Quotient.eq_zero_iff_mem.mp ((hπ' b).symm.trans hb)
        calc _ ≤ (J.map σ.hom) ^ n := Ideal.pow_right_mono hle n
          _ = ⊥ := by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
      exact ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective φ π' hsurj hnil⟩)
  refine ⟨Over.homMk (e.hom ≫ x) (by rw [Category.assoc, hxs, hσ]), ?_⟩
  rw [← cancel_epi hPB'.isoPullback.hom]
  show hPB'.isoPullback.hom ≫ pullback.fst _ _ ≫ e.hom ≫ x = hPB'.isoPullback.hom ≫ f₀
  rw [IsPullback.isoPullback_hom_fst_assoc, Category.assoc, Iso.inv_hom_id_assoc, hx]

end GlobalTheory.NilpotentLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfStalks
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootUnit

open TopologicalSpace

theorem gs_id {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (h : y ∈ U) (a : Γ(Y, U)) :
    gs (𝟙 Y) y U a = (Y.presheaf.germ U y h).hom a := gs_eq (𝟙 Y) y U h a

theorem gs_ne_zero {Y : Scheme.{0}} [IsIntegral Y] (y : Y) (U : Y.Opens) (h : y ∈ U) {a : Γ(Y, U)} (ha : a ≠ 0) :
    gs (𝟙 Y) y U a ≠ 0 := by
  rw [gs_id y U h]
  intro e
  exact ha (germ_injective_of_isIntegral Y y h (e.trans (map_zero _).symm))

theorem exists_unit_of_stalks {Y : Scheme.{0}} [IsIntegral Y] (W : Y.Opens) (a b : Γ(Y, W))
    (hb : ∀ y ∈ W, gs (𝟙 Y) y W b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y W a = v.val * gs (𝟙 Y) y W b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y W a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y W b := by
  have loc : ∀ y : W, ∃ (V : Y.Opens) (_ : y.1 ∈ V) (_ : V ≤ W) (c : Γ(Y, V)),
      ∀ z ∈ V, gs (𝟙 Y) z W a = gs (𝟙 Y) z V c * gs (𝟙 Y) z W b := by
    rintro ⟨y, hy⟩
    obtain ⟨v, hv⟩ := h y hy
    obtain ⟨U, hU, c, hc⟩ := Y.presheaf.germ_exist v.val
    have hm : y ∈ U ⊓ W := ⟨hU, hy⟩
    have e : gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_right).op).hom a) =
        gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_left).op).hom c *
          (Y.presheaf.map (homOfLE inf_le_right).op).hom b) := by
      rw [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, hv, gs_id y U hU]
      exact congrArg (· * _) hc.symm
    rw [gs_id y _ hm, gs_id y _ hm] at e
    have e' := germ_injective_of_isIntegral Y y hm e
    refine ⟨U ⊓ W, hm, inf_le_right, (Y.presheaf.map (homOfLE inf_le_left).op).hom c, fun z hz => ?_⟩
    have := congrArg (gs (𝟙 Y) z (U ⊓ W)) e'
    rwa [gs_mul _ z _ hz, gs_res _ z inf_le_right hz, gs_res _ z inf_le_right hz] at this
  choose V hV hle c hc using loc
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hle i))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV _⟩) c
    (fun i j => fn_ext (V := V i ⊓ V j) fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      exact mul_right_cancel₀ (hb y (hle i hy.1)) ((hc i y hy.1).symm.trans (hc j y hy.2)))
  have key : ∀ y ∈ W, gs (𝟙 Y) y W a = gs (𝟙 Y) y W s * gs (𝟙 Y) y W b := fun y hy => by
    rw [hc ⟨y, hy⟩ y (hV _), ← hs ⟨y, hy⟩]
    exact congrArg (· * _) (gs_res (𝟙 Y) y (hle ⟨y, hy⟩) (hV ⟨y, hy⟩) s)
  have hu : IsUnit (show Γ(Y, W) from s) := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨v, hv⟩ := h y hy
    have := mul_right_cancel₀ (hb y hy) ((key y hy).symm.trans hv)
    exact (congrArg IsUnit ((gs_id y W hy _).symm.trans this)).mpr v.isUnit
  refine ⟨hu.unit, fun y hy => ?_⟩
  rw [← gs_unit _ y W hy]
  exact key y hy

theorem exists_unit_of_stalks' {Y : Scheme.{0}} [IsIntegral Y] (W U V : Y.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (a : Γ(Y, U)) (b : Γ(Y, V)) (hb : ∀ y ∈ W, gs (𝟙 Y) y V b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y U a = v.val * gs (𝟙 Y) y V b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y U a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y V b := by
  obtain ⟨r, hr⟩ := exists_unit_of_stalks W ((Y.presheaf.map (homOfLE hU).op).hom a)
    ((Y.presheaf.map (homOfLE hV).op).hom b)
    (fun y hy => by rw [gs_res (𝟙 Y) y hV hy]; exact hb y hy)
    (fun y hy => by rw [gs_res (𝟙 Y) y hU hy, gs_res (𝟙 Y) y hV hy]; exact h y hy)
  refine ⟨r, fun y hy => ?_⟩
  have := hr y hy
  rwa [gs_res (𝟙 Y) y hU hy, gs_res (𝟙 Y) y hV hy] at this

theorem sec_gs_ne_zero {X Y : Scheme.{0}} [IsIntegral Y] {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∃ j, s.f j ≠ 0) (y : Y) (i : K → L.ι)
    (hy : y ∈ LB.wchart L φ i) : gs (𝟙 Y) y (LB.wchart L φ i) (s.f i) ≠ 0 := by
  obtain ⟨j, hj⟩ := hs
  have hne : (LB.wchart L φ j : Set Y).Nonempty := by
    by_contra hn
    exact hj (fn_ext (V := LB.wchart L φ j) fun x hx => absurd ⟨x, hx⟩ hn)
  obtain ⟨z, hz, hz'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen (LB.wchart L φ i).isOpen hne ⟨y, hy⟩
  refine gs_ne_zero y _ hy fun e => gs_ne_zero z _ hz hj ?_
  rw [sec_trans s (𝟙 Y) z hz hz', e, gs_id z _ hz', map_zero, mul_zero]

theorem trF_pull {X Y : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (y : Y) (i j : PUnit → L.ι) :
    trF (L := L) (K := PUnit) (fun _ => f) (fun _ => 1) (𝟙 Y) y i j =
      gm (𝟙 Y ≫ f) y (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) (L.g _ _) := by
  rw [trF, Fintype.prod_unique, zpow_one]

theorem exists_gen_of_pow : ∀ (X Y : Scheme.{0}) [IsIntegral Y], (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → ∀ (L : LB X), L.IsLB → ∀ (f₁ f₂ : Y ⟶ X) (l : ℕ), 1 ≤ l → ∀ (s₁ : LB.Sec (L.pull f₁)) (s₂ : LB.Sec (L.pull f₂)) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![f₁, f₂] ![(l : ℤ), -(l : ℤ)])), u.IsGen → (∃ j, s₂.f j ≠ 0) → (∀ (y : Y) (J), Good L y J → sval s₁ (𝟙 Y) y J ^ l = (val u (𝟙 Y) y J).val * sval s₂ (𝟙 Y) y J ^ l) → ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![f₁, f₂] ![1, -1]), r.IsGen ∧ ∀ (y : Y) (J), Good L y J → sval s₁ (𝟙 Y) y J = (val r (𝟙 Y) y J).val * sval s₂ (𝟙 Y) y J := by
  intro X Y _ hN L hL f₁ f₂ l hl s₁ s₂ u _ hs H
  have l₁ : ∀ j : Fin 2 → L.ι, LB.wchart L ![f₁, f₂] j ≤ LB.wchart L (K := PUnit) (fun _ => f₁) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  have l₂ : ∀ j : Fin 2 → L.ι, LB.wchart L ![f₁, f₂] j ≤ LB.wchart L (K := PUnit) (fun _ => f₂) (fun _ => j 1) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1
  have main : ∀ j : Fin 2 → L.ι, ∃ r : Γ(Y, LB.wchart L ![f₁, f₂] j)ˣ, ∀ y ∈ LB.wchart L ![f₁, f₂] j,
      gs (𝟙 Y) y (LB.wchart L (K := PUnit) (fun _ => f₁) (fun _ => j 0)) (s₁.f fun _ => j 0) =
        (gm (𝟙 Y) y _ r).val *
          gs (𝟙 Y) y (LB.wchart L (K := PUnit) (fun _ => f₂) (fun _ => j 1)) (s₂.f fun _ => j 1) := by
    intro j
    exact exists_unit_of_stalks' (LB.wchart L ![f₁, f₂] j) _ _ (l₁ j) (l₂ j) _ _
      (fun y hy => sec_gs_ne_zero s₂ hs y _ (l₂ j hy))
      (fun y hy => by
        choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
        have hJ' : Good L y J := hJ
        haveI := hN y
        have as : Associated (sval s₂ (𝟙 Y) y J) (sval s₁ (𝟙 Y) y J) :=
          (Associated.pow_iff (by omega : l ≠ 0)).1 ⟨val u (𝟙 Y) y J, (_root_.mul_comm _ _).trans (H y J hJ').symm⟩
        obtain ⟨v, hv⟩ := as
        have e₁ := sec_trans s₁ (𝟙 Y) y (l₁ j hy) (hJ'.mem (K := PUnit) (fun _ => f₁) (𝟙 Y))
        have e₂ := sec_trans s₂ (𝟙 Y) y (l₂ j hy) (hJ'.mem (K := PUnit) (fun _ => f₂) (𝟙 Y))
        change _ = _ * sval s₁ (𝟙 Y) y J at e₁
        change _ = _ * sval s₂ (𝟙 Y) y J at e₂
        rw [e₁, e₂, ← hv]
        generalize trF (L := L) (K := PUnit) (fun _ => f₁) (fun _ => 1) (𝟙 Y) y _ _ = t₁
        generalize trF (L := L) (K := PUnit) (fun _ => f₂) (fun _ => 1) (𝟙 Y) y _ _ = t₂
        refine ⟨t₁ * v * t₂⁻¹, ?_⟩
        rw [Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, Units.val_mul]
        ring)
  choose r hr using main
  refine ⟨⟨r⟩, fun i j => unit_ext fun y hy => ?_, fun y J hJ => hr _ y (hJ.mem ![f₁, f₂] (𝟙 Y))⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y i j hy.1 hy.2) (gm_res _ y _ hy _))).symm)
  have e₁ := sec_trans s₁ (𝟙 Y) y (l₁ i hy.1) (l₁ j hy.2)
  have e₂ := sec_trans s₂ (𝟙 Y) y (l₂ i hy.1) (l₂ j hy.2)
  have hb := sec_gs_ne_zero s₂ hs y _ (l₂ j hy.2)
  rw [hr i y hy.1, hr j y hy.2, e₂, trF_pull, trF_pull, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
    ← Units.val_mul] at e₁
  have e := Units.ext (mul_right_cancel₀ hb e₁)
  rw [Fin.prod_univ_two]
  change gm (𝟙 Y) y _ (r i) = gm (𝟙 Y ≫ f₁) y _ (L.g (i 0) (j 0)) ^ (1 : ℤ) *
    gm (𝟙 Y ≫ f₂) y _ (L.g (i 1) (j 1)) ^ (-1 : ℤ) * gm (𝟙 Y) y _ (r j)
  rw [zpow_one, zpow_neg_one, mul_right_comm, ← e, mul_inv_cancel_right]

end GlobalTheory.RootUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElement
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionKernel

theorem mem_map_of_flat {R B : Type} [CommRing R] [CommRing B] (c : R →+* B) (hf : c.Flat)
    {I : Ideal R} {ε : R} (h : ∀ x, ε * x = 0 → x ∈ I) (b : B) (hb : c ε * b = 0) :
    b ∈ I.map c := by
  letI := c.toAlgebra
  haveI : Module.Flat R B := hf
  obtain ⟨l, d, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := B)
    (f := fun _ : Unit => ε) (x := fun _ => b)
    (by rw [Fintype.sum_unique, Algebra.smul_def]; exact hb)
  have : b = ∑ j, d () j • y j := hy ()
  rw [this]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem c (h _ ?_))
  have h := hc j
  rwa [Fintype.sum_unique] at h

variable {X Y : Scheme.{0}}

theorem app_rs (i : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (i.app V).hom (rs X h a) = rs Y (i.preimage_mono h) ((i.app U).hom a) := by
  have := congr(($(i.naturality (homOfLE h).op)).hom a)
  exact this

theorem gs_sub (r : Y ⟶ X) (z : Y) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq r z U h, map_sub]

theorem gs_of_app_eq_zero (r : Y ⟶ X) (z : Y) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U))
    (ha : (r.app U).hom a = 0) : gs r z U a = 0 := by rw [gs_eq r z U h, ha, map_zero]

theorem exists_rs_eq_zero {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U))
    (h : (X.presheaf.germ U x hx).hom a = 0) :
    ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ rs X hV a = 0 := by
  obtain ⟨V, hxV, i, i', e⟩ := X.presheaf.germ_eq x hx hx a 0 (h.trans (map_zero _).symm)
  exact ⟨V, i.le, hxV, e.trans (map_zero _)⟩

variable {A A₀ : Type} [CommRing A] [CommRing A₀] {g₀ : A →+* A₀} {a : A}
  {f : X ⟶ Spec (CommRingCat.of A)} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} {j : Y ⟶ X}

theorem cst_eq (f : X ⟶ Spec (CommRingCat.of A)) (W : X.Opens) :
    SmallExtLift.cst f W = cst f W := rfl

theorem mul_eq_zero_iff_app (hg : Function.Surjective g₀)
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) [Flat f]
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) {V : X.Opens} (hV : IsAffineOpen V)
    (u : Γ(X, V)) : cst f V a * u = 0 ↔ (j.app V).hom u = 0 := by
  rw [← cst_eq]
  constructor
  · intro h
    have h := mem_map_of_flat _ (SmallExtLift.cst_flat f hV) (fun x hx => (ha x).1 hx) u h
    refine (show _ ≤ RingHom.ker (j.app V).hom from Ideal.map_le_iff_le_comap.2 fun r hr => ?_) h
    rw [Ideal.mem_comap, RingHom.mem_ker, SmallExtLift.app_cst P.w, RingHom.mem_ker.1 hr, map_zero]
  · intro h
    exact SmallExtLift.mul_eq_zero_of_mem _ (fun x hx => (mul_comm _ _).trans ((ha x).2 hx))
      (SmallExtLift.mem_of_app_eq_zero hg P hV u h)

theorem gs_mul_eq_zero_iff (hg : Function.Surjective g₀)
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) [Flat f]
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) {W : X.Opens} (z : Y) (hz : j z ∈ W)
    (u : Γ(X, W)) : gs (𝟙 X) (j z) W (cst f W a * u) = 0 ↔ gs j z W u = 0 := by
  constructor
  · intro h
    rw [gs_eq (𝟙 X) (j z) W hz] at h
    obtain ⟨V, hV, hx, e⟩ := exists_rs_eq_zero hz (cst f W a * u) h
    obtain ⟨V', hA, hx', hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    have e' := congrArg (rs X hle) e
    rw [rs_rs, map_mul, rs_cst, map_zero] at e'
    rw [← gs_res j z (hle.trans hV) hx']
    exact gs_of_app_eq_zero j z V' hx' _ ((mul_eq_zero_iff_app hg ha P hA _).1 e')
  · intro h
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g₀)) :=
      IsClosedImmersion.spec_of_surjective _ hg
    have : IsClosedImmersion j := MorphismProperty.of_isPullback P.flip this
    rw [gs_eq _ _ W hz] at h
    obtain ⟨O, hO, hx, e⟩ := exists_rs_eq_zero (U := j ⁻¹ᵁ W) hz _ h
    obtain ⟨D, hD, hD'⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp O.isOpen
    have hx₁ : j z ∈ W ⊓ ⟨D, hD⟩ := ⟨hz, show z ∈ j ⁻¹' D from hD' ▸ hx⟩
    obtain ⟨V', hA, hx', hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx₁
    have l : j ⁻¹ᵁ V' ≤ O := fun y hy => by
      have : y ∈ j ⁻¹' D := (hle hy).2
      rwa [hD'] at this
    have e' := congrArg (rs Y l) e
    rw [rs_rs, map_zero] at e'
    have h₂ := (mul_eq_zero_iff_app hg ha P hA (rs X (hle.trans inf_le_left) u)).2
      ((app_rs j _ u).trans e')
    rw [← gs_res (𝟙 X) (j z) (hle.trans inf_le_left) hx']
    refine gs_of_app_eq_zero (𝟙 X) (j z) V' hx' _ ?_
    change rs X _ _ = 0
    rw [map_mul, rs_cst, h₂]

theorem surjective_of_isNilpotent (hg : Function.Surjective g₀)
    (hn : IsNilpotent (RingHom.ker g₀))
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) : Function.Surjective j := by
  have h2 : Surjective (Spec.map (CommRingCat.ofHom g₀)) := ⟨fun x => by
    obtain ⟨n, hn⟩ := hn
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g₀ : Set A) := fun a ha =>
      x.isPrime.mem_of_pow_mem n (by
        have := Ideal.pow_mem_pow ha n
        rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
        rw [this]
        exact zero_mem _)
    rw [← range_comap_of_surjective _ g₀ hg] at hx
    exact hx⟩
  have : Surjective j := MorphismProperty.of_isPullback P.flip h2
  exact j.surjective

theorem exists_sec_of_local {N : LB X} {N₀ : LB Y} (w : LB.Iso N₀ (N.pull j)) (hN₀ : N₀.IsLB)
    (hw : w.IsGen) {I : Type} (V : I → X.Opens) (c : I → N.ι) (hc : ∀ q, V q ≤ N.U (c q))
    (cov : ∀ z : Y, ∃ q, j z ∈ V q) (u : ∀ q, Γ(X, V q))
    (hu : ∀ q q' z, j z ∈ V q → j z ∈ V q' →
      gs j z _ (u q) = (gm j z _ (N.g (c q) (c q'))).val * gs j z _ (u q')) :
    ∃ τ₀ : LB.Sec N₀, ∀ q k' z, j z ∈ V q → z ∈ N₀.U k' →
      (gw w (𝟙 _) z (c q) k').val * gs (𝟙 _) z _ (τ₀.f k') = gs j z _ (u q) := by
  have tr : ∀ q q' k' l' z, j z ∈ V q → j z ∈ V q' → z ∈ N₀.U k' → z ∈ N₀.U l' →
      (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) =
        (gm (𝟙 _) z _ (N₀.g k' l')).val * ((gw w (𝟙 _) z (c q') l')⁻¹.val * gs j z _ (u q')) := by
    intro q q' k' l' z h h' hk hl
    have e := (isGen_iff w).1 hw _ (𝟙 Y) z (c q) (c q') k' l' (hc q h) (hc q' h') hk hl
    rw [Category.id_comp] at e
    rw [hu q q' z h h', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    congr 2
    generalize gm j z _ (N.g (c q) (c q')) = B
    generalize gm (𝟙 Y) z _ (N₀.g k' l') = C
    generalize gw w (𝟙 Y) z (c q') l' = D
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ k' : N₀.ι, ∃ s : Γ(Y, N₀.U k'), ∀ q z, j z ∈ V q → z ∈ N₀.U k' →
      gs (𝟙 _) z _ s = (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) := by
    intro k'
    let O : I → Y.Opens := fun q => j ⁻¹ᵁ V q ⊓ N₀.U k'
    have l₁ : ∀ q, O q ≤ (N.pull j).U (fun _ => c q) ⊓ N₀.U k' := fun q x hx =>
      ⟨mem_pull.2 (hc q hx.1), hx.2⟩
    obtain ⟨b, hb⟩ : ∃ b : ∀ q, Γ(Y, O q), ∀ q z, z ∈ O q →
        gs (𝟙 _) z (O q) (b q) = (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) :=
      ⟨fun q => rs Y (l₁ q) (w.s (fun _ => c q, k'))⁻¹.val *
          rs Y (inf_le_left : O q ≤ j ⁻¹ᵁ V q) ((j.app (V q)).hom (u q)), fun q z hz =>
        (gs_mul (𝟙 Y) z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_res (𝟙 Y) z _ hz _).trans ((gs_unit (𝟙 Y) z _ (l₁ q hz) _).trans
            (congrArg Units.val (map_inv _ _))))
          ((gs_res (𝟙 Y) z _ hz _).trans ((gs_pull (𝟙 Y) j z _ hz.1 _).trans
            (by rw [Category.id_comp]))))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' O (N₀.U k')
      (fun q => homOfLE inf_le_right) (fun z hz => by
        obtain ⟨q, hq⟩ := cov z
        exact Opens.mem_iSup.2 ⟨q, hq, hz⟩) b
      (fun q q' => fn_ext (V := O q ⊓ O q') fun z hz => by
        refine (gs_res (𝟙 Y) z inf_le_left hz _).trans
          (Eq.trans ?_ (gs_res (𝟙 Y) z inf_le_right hz _).symm)
        rw [hb q z hz.1, hb q' z hz.2, tr q q' k' k' z hz.1.1 hz.2.1 hz.1.2 hz.1.2,
          gm_self hN₀ (𝟙 Y) z hz.1.2, Units.val_one, _root_.one_mul])
    refine ⟨s, fun q z h₁ h₂ => ?_⟩
    have hz : z ∈ O q := ⟨h₁, h₂⟩
    exact (gs_res (𝟙 Y) z inf_le_right hz s).symm.trans
      ((congrArg (gs (𝟙 Y) z (O q)) (hs q)).trans (hb q z hz))
  choose s hs using glue
  refine ⟨⟨s, fun k' l' => fn_ext fun z hz => ?_⟩, fun q k' z h₁ h₂ => ?_⟩
  · obtain ⟨q, hq⟩ := cov z
    refine (gs_res (𝟙 Y) z _ hz _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 Y) z _ hz _) (gs_res (𝟙 Y) z _ hz _))).symm)
    rw [hs k' q z hq hz.1, hs l' q z hq hz.2]
    exact tr q q k' l' z hq hq hz.1 hz.2
  · change _ * gs (𝟙 Y) z _ (s k') = _
    rw [hs k' q z h₁ h₂, Units.mul_inv_cancel_left]

theorem exists_sec_of_vanishing : ∀ (A A₀ A' : Type) [CommRing A] [CommRing A₀] [CommRing A'] (g₀ : A →+* A₀) (g' : A →+* A') (a : A), Function.Surjective g₀ → Function.Surjective g' → IsNilpotent (RingHom.ker g₀) → RingHom.ker g' = Ideal.span {a} → a ∈ RingHom.ker g₀ → (∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) → ∀ (X X₀ X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f' : X' ⟶ Spec (CommRingCat.of A')) (j₀ : X₀ ⟶ X) (β : X' ⟶ X), Flat f → IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → ∀ (N : LB X) (N₀ : LB X₀) (w₀ : LB.Iso N₀ (N.pull j₀)), N.IsLB → N₀.IsLB → w₀.IsGen → ∀ σ : LB.Sec N, (∀ k, (β.app (N.U k)).hom (σ.f k) = 0) → ∃ τ₀ : LB.Sec N₀, ∀ τ : LB.Sec N, (∀ z (k : (N).ι) (k' : (N₀).ι), (j₀) z ∈ (N).U k → z ∈ (N₀).U k' → gs (j₀) z _ ((τ).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ₀).f k')) → ∀ k, σ.f k = cst f (N.U k) a * τ.f k := by
  intro A A₀ A' _ _ _ g₀ g' a hg hg' hn hk _ ha X Y X' f f₀ f' j β _ P P' N N₀ w hN hN₀ hw σ hσ
  let I := {q : Σ (_ : N.ι) (W : X.Opens), Γ(X, W) //
    ∃ h : q.2.1 ≤ N.U q.1, rs X h (σ.f q.1) = cst f q.2.1 a * q.2.2}
  let V : I → X.Opens := fun q => q.1.2.1
  let c : I → N.ι := fun q => q.1.1
  let u : ∀ q, Γ(X, V q) := fun q => q.1.2.2
  have hc : ∀ q, V q ≤ N.U (c q) := fun q => q.2.1
  have hu : ∀ q, rs X (hc q) (σ.f (c q)) = cst f (V q) a * u q := fun q => q.2.2
  have loc : ∀ k x, x ∈ N.U k → ∃ q, c q = k ∧ x ∈ V q := by
    intro k x hx
    obtain ⟨W, hW, hxW, hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    have h := SmallExtLift.mem_of_app_eq_zero hg' P' hW (rs X hle (σ.f k))
      (by rw [app_rs, hσ, map_zero])
    rw [hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨⟨⟨k, W, b⟩, hle, hb⟩, rfl, hxW⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_sec_of_local w hN₀ hw V c hc (fun z => by
      obtain ⟨k, hk⟩ := exists_chart hN (j z)
      obtain ⟨q, -, hq⟩ := loc k _ hk
      exact ⟨q, hq⟩) u (fun q q' z h h' => by
      have hm : j z ∈ V q ⊓ V q' := ⟨h, h'⟩
      have e := (gs_mul_eq_zero_iff hg ha P z hm (rs X inf_le_left (u q) -
        rs X (inf_le_inf (hc q) (hc q')) (N.g (c q) (c q')).val * rs X inf_le_right (u q'))).1 (by
          refine gs_of_app_eq_zero (𝟙 X) (j z) _ hm _ ?_
          change (_ : Γ(X, V q ⊓ V q')) = 0
          have e₁ := congrArg (rs X (inf_le_left : V q ⊓ V q' ≤ _)) (hu q)
          have e₂ := congrArg (rs X (inf_le_right : V q ⊓ V q' ≤ _)) (hu q')
          have e₃ := congrArg (rs X (inf_le_inf (hc q) (hc q'))) (σ.compat (c q) (c q'))
          simp only [map_mul, rs_rs, rs_cst] at e₁ e₂ e₃
          change cst f (V q ⊓ V q') a * (_ - _ * _) = 0
          linear_combination e₃ - e₁ + rs X (inf_le_inf (hc q) (hc q')) (N.g (c q) (c q')).val * e₂)
      rw [gs_sub _ _ _ hm, gs_mul _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm,
        gs_unit j z (N.U (c q) ⊓ N.U (c q')) ⟨hc q h, hc q' h'⟩, sub_eq_zero] at e
      exact e)
  refine ⟨τ₀, fun τ hτ k => fn_ext fun x hx => ?_⟩
  obtain ⟨z, rfl⟩ := surjective_of_isNilpotent hg hn P x
  obtain ⟨q, rfl, hq⟩ := loc k _ hx
  obtain ⟨k', hk'⟩ := exists_chart hN₀ z
  have e := (gs_mul_eq_zero_iff hg ha P z hq (u q - rs X (hc q) (τ.f (c q)))).2 (by
    rw [gs_sub _ _ _ hq, gs_res _ _ _ hq, hτ z (c q) k' hx hk', hτ₀ q k' z hq hk', sub_self])
  rw [mul_sub, ← hu, ← rs_cst f (hc q), ← map_mul, gs_sub (𝟙 X) (j z) _ hq, gs_res (𝟙 X) (j z) _ hq,
    gs_res (𝟙 X) (j z) _ hq, sub_eq_zero] at e
  exact e

end GlobalTheory.SectionKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElementStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_section_eq_mul_of_vanishing_mod_element : ∀ (A A₀ A' : Type) [CommRing A] [CommRing A₀] [CommRing A'] (g₀ : A →+* A₀) (g' : A →+* A') (a : A), Function.Surjective g₀ → Function.Surjective g' → IsNilpotent (RingHom.ker g₀) → RingHom.ker g' = Ideal.span {a} → a ∈ RingHom.ker g₀ → (∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) → ∀ (X X₀ X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f' : X' ⟶ Spec (CommRingCat.of A')) (j₀ : X₀ ⟶ X) (β : X' ⟶ X), Flat f → IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → ∀ (N : LB X) (N₀ : LB X₀) (w₀ : LB.Iso N₀ (N.pull j₀)), N.IsLB → N₀.IsLB → w₀.IsGen → ∀ σ : LB.Sec N, (∀ k, (β.app (N.U k)).hom (σ.f k) = 0) → ∃ τ₀ : LB.Sec N₀, ∀ τ : LB.Sec N, (∀ z (k : (N).ι) (k' : (N₀).ι), (j₀) z ∈ (N).U k → z ∈ (N₀).U k' → gs (j₀) z _ ((τ).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ₀).f k')) → ∀ k, σ.f k = cst f (N.U k) a * τ.f k := by
  first | exact @GlobalTheory.SectionKernel.exists_sec_of_vanishing | exact GlobalTheory.SectionKernel.exists_sec_of_vanishing | (intros; apply GlobalTheory.SectionKernel.exists_sec_of_vanishing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OpenEqTopOfContainsSpecialPartUniversallyClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OpenEqTopOfContainsSpecialPartUniversallyClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem eq_top_of_special_part : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y : Over (Spec (CommRingCat.of R))) [UniversallyClosed Y.hom] (U : Y.left.Opens), (∀ z : (thickObj R I 0 Y).left, pullback.fst Y.hom (thick R I 0) z ∈ U) → U = ⊤ := by
  intro R _ I hI Y _ U hU
  by_contra hne
  have hcl : IsClosed (Y.hom '' ((U : Set Y.left)ᶜ)) :=
    Y.hom.isClosedMap _ U.isOpen.isClosed_compl
  have hne' : ((U : Set Y.left)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    exact hne (TopologicalSpace.Opens.ext h)
  obtain ⟨y, hy⟩ := hne'
  let p : PrimeSpectrum R := Y.hom y
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have hspec : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 hpm
  have hq : q ∈ Y.hom '' ((U : Set Y.left)ᶜ) :=
    hspec.mem_closed hcl ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hyq⟩ := hq
  have hr : q ∈ Set.range (thick R I 0) := by
    have h1 : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        PrimeSpectrum.mem_zeroLocus]
      intro x hx
      have hx' : x ∈ I := by simpa using hx
      exact (Ideal.mem_sInf.1 (hI hx')) ⟨bot_le, hm⟩
    exact h1
  have h2 : y' ∈ Set.range (pullback.fst Y.hom (thick R I 0)) := by
    rw [Scheme.Pullback.range_fst]
    show Y.hom y' ∈ Set.range (thick R I 0)
    rw [hyq]; exact hr
  obtain ⟨z, rfl⟩ := h2
  exact hy' (hU z)

end GlobalTheory.Unif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OpenEqTopOfContainsSpecialPartUniversallyClosedStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_eq_top_of_contains_special_part_universallyClosed : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y : Over (Spec (CommRingCat.of R))) [UniversallyClosed Y.hom] (U : Y.left.Opens), (∀ z : (thickObj R I 0 Y).left, pullback.fst Y.hom (thick R I 0) z ∈ U) → U = ⊤ := by
  first | exact @GlobalTheory.Unif.eq_top_of_special_part | exact GlobalTheory.Unif.eq_top_of_special_part | (intros; apply GlobalTheory.Unif.eq_top_of_special_part <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenLiftOfIsNilpotent
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenLift

open GlobalTheory.LB

variable {X Y : Scheme.{0}}

theorem pullSec_surjective_of_le (f : Y ⟶ X) [IsClosedImmersion f] {L : LB X} (hL : L.IsLB)
    {V : X.Opens} (hV : IsAffineOpen V) (i : L.ι) (h : V ≤ L.U i) :
    Function.Surjective (pullSec L f V) := by
  intro s
  have h' : f ⁻¹ᵁ V ≤ (L.pull f).U (fun _ => i) :=
    (f.preimage_mono h).trans (pull_U f (fun _ => i)).ge
  obtain ⟨a, ha⟩ := f.app_surjective V hV (chartEquiv (Semi.LB.isLB_pull hL f) (fun _ => i) h' s)
  refine ⟨(chartEquiv hL i h).symm a, ?_⟩
  apply (chartEquiv (Semi.LB.isLB_pull hL f) (fun _ => i) h').injective
  rw [chartEquiv_pullSec f hL (fun _ => i) h h', LinearEquiv.apply_symm_apply]
  exact ha

theorem pullSec_surjective (f : Y ⟶ X) [IsClosedImmersion f] [IsAffine X] {L : LB X}
    (hL : L.IsLB) : Function.Surjective (pullSec L f ⊤) := by
  intro s
  haveI := isQuasicoherent_toMod hL
  haveI := isQuasicoherent_toMod (Semi.LB.isLB_pull hL f)
  let I : Ideal Γ(X, ⊤) :=
    { carrier := {c | ∃ σ, pullSec L f ⊤ σ = (f.app ⊤).hom c • s}
      add_mem' := by
        rintro a b ⟨σ, hσ⟩ ⟨τ, hτ⟩
        exact ⟨σ + τ, by rw [map_add (f := _), hσ, hτ, map_add (f := _), add_smul]⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro a b ⟨σ, hσ⟩
        exact ⟨a • σ, by rw [LinearMap.map_smulₛₗ, hσ, smul_eq_mul, map_mul, mul_smul]⟩ }
  have key : ∀ x : X, ∃ c ∈ I, x ∈ X.basicOpen c := by
    intro x
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨a, ha, hx⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hi⟩ (Opens.mem_top x)
    obtain ⟨u, hu⟩ := pullSec_surjective_of_le f hL ((isAffineOpen_top X).basicOpen a) i ha
      ((toMod (L.pull f)).presheaf.map (homOfLE (f.preimage_mono (X.basicOpen_le a))).op s)
    obtain ⟨n, σ, hσ⟩ := QCoh.exists_pow_smul_eq_res (toMod L) (isAffineOpen_top X) a
      (X.basicOpen_le a) rfl u
    obtain ⟨m, hm⟩ := QCoh.exists_pow_smul_eq_zero (toMod (L.pull f))
      ((isAffineOpen_top X).preimage f) ((f.app ⊤).hom a) (f.preimage_mono (X.basicOpen_le a))
      (f.preimage_basicOpen a) (pullSec L f ⊤ σ - (f.app ⊤).hom a ^ n • s) (by
        rw [map_sub, ← pullSec_map f (X.basicOpen_le a), ← hσ, LinearMap.map_smulₛₗ, hu, Scheme.Modules.map_smul,
          map_pow, map_pow, sub_eq_zero]
        congr 2
        exact congrArg (fun q => q.hom a) (f.naturality (homOfLE (X.basicOpen_le a)).op))
    refine ⟨a ^ (m + n + 1), ?_, by rwa [X.basicOpen_pow a (Nat.succ_pos _)]⟩
    rw [pow_succ']
    refine I.mul_mem_left a ⟨a ^ m • σ, ?_⟩
    rw [smul_sub, sub_eq_zero] at hm
    rw [LinearMap.map_smulₛₗ, map_pow, hm, map_pow, pow_add, mul_smul]
  have hI : I = ⊤ := by
    rw [← Ideal.span_eq I, ← (isAffineOpen_top X).iSup_basicOpen_eq_self_iff]
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨c, hc, hx⟩ := key x
    exact Opens.mem_iSup.2 ⟨⟨c, hc⟩, hx⟩
  obtain ⟨σ, hσ⟩ : (1 : Γ(X, ⊤)) ∈ I := hI ▸ Submodule.mem_top
  exact ⟨σ, by rw [hσ, map_one, one_smul]⟩

theorem isUnit_of_isUnit_app (f : Y ⟶ X) [Surjective f] {U : X.Opens} (a : Γ(X, U))
    (ha : IsUnit ((f.app U).hom a)) : IsUnit a := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ U a fun x hx => ?_
  obtain ⟨y, rfl⟩ := f.surjective x
  have h₁ : y ∈ Y.basicOpen ((f.app U).hom a) := by
    rw [Y.basicOpen_of_isUnit ha]; exact hx
  have h₂ : y ∈ f ⁻¹ᵁ X.basicOpen a := by rw [f.preimage_basicOpen]; exact h₁
  exact (X.mem_basicOpen a (f y) hx).1 h₂

theorem exists_genPull_eq (f : Y ⟶ X) [IsClosedImmersion f] [Surjective f] [IsAffine X]
    {L : LB X} (hL : L.IsLB) (t₀ : LB.Gen (L.pull f)) (ht₀ : t₀.IsGen) :
    ∃ t : LB.Gen L, t.IsGen ∧ LB.genPull L t f = t₀ := by
  obtain ⟨σ, hσ⟩ := pullSec_surjective f hL (ofSec (genSec t₀ ht₀) _)
  obtain ⟨s, rfl⟩ := (globalEquiv L).symm.surjective σ
  have e : ∀ j : (L.pull f).ι,
      (f.appLE _ _ (pull_U_le f j)).hom (s.f (j PUnit.unit)) = (t₀.s j).val := fun j => by
    rw [← globalEquiv_pullSec_f f s j]
    exact congrArg (fun z : LB.Sec (L.pull f) => z.f j)
      ((congrArg (globalEquiv (L.pull f)) hσ).trans
        ((globalEquiv (L.pull f)).apply_symm_apply (genSec t₀ ht₀)))
  have hu : ∀ i, IsUnit (s.f i) := fun i => by
    refine isUnit_of_isUnit_app f _ ?_
    have h := ((e fun _ => i).symm ▸ (t₀.s fun _ => i).isUnit :
      IsUnit ((f.appLE _ _ (pull_U_le f fun _ => i)).hom (s.f i))).map
      (resG Y (pull_U f fun _ => i).ge)
    rwa [resG_appLE, Scheme.Hom.appLE_eq_app] at h
  refine ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j), ?_⟩
  cases t₀ with | mk t₀ => ?_
  exact congrArg LB.Gen.mk (funext fun j => Units.ext (e j))

end GlobalTheory.GenLift
end
end
