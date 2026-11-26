module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverEmbeddingClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothModelNearClosedFibreEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulDescendsNearClosedFibreOfEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorDescendedBundleNearClosedPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisationOfTraitUnif

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfClosedFibreEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalBundleModificationDescendsToGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalBundleModificationDescendsToGroup
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeDesc

theorem app_bijective (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : AdmBase R (maximalIdeal R))
    (M : Modif R) (G' : Over M.S) (G : Over (Sp R)) (β : G'.left ⟶ G.left) (hf : Flat G.hom)
    (hp : IsPullback β G'.hom G.hom M.π) : ∀ V : G.left.Opens, Function.Bijective (β.app V).hom := by
  obtain ⟨hN, -, hI, -⟩ := hR
  haveI := M.proper
  exact GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R M.S G.left G'.left M.π G.hom β G'.hom inferInstance inferInstance
    (GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M).1 hf hp

theorem exists_closed_spec (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) (hG : QuasiCompact G.hom)
    (y : G.left) (hy : G.hom y = closedPoint R) :
    ∃ z : G.left, IsClosed ({z} : Set G.left) ∧ y ⤳ z ∧ G.hom z = closedPoint R := by
  haveI : CompactSpace G.left := by
    haveI := hG
    exact QuasiCompact.compactSpace_of_compactSpace G.hom
  obtain ⟨z, hz, hzc⟩ := (isClosed_closure (s := ({y} : Set G.left))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  have hyz : y ⤳ z := specializes_iff_mem_closure.2 hz
  refine ⟨z, hzc, hyz, ?_⟩
  have h := hyz.map G.hom.base.hom.continuous
  rw [hy] at h
  have hc : IsClosed ({closedPoint R} : Set (PrimeSpectrum R)) := isClosed_singleton_closedPoint R
  have h' := specializes_iff_mem_closure.1 h
  exact hc.closure_subset h'

theorem cubicalBundle_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∃ L : LB G.left, L.IsLB ∧ LBIso P'.L.L (L.pull β) := by
  intro R _ _ _ hR M G' _ _ hG' P' G _ _ β hG hpb θ O hO hθ
  have hflat : Flat G.hom := by haveI := hG.smooth; infer_instance
  have hbij := app_bijective R hR M G' G β hflat hpb.1
  have hloc : ∀ y : G.left, ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
    intro y
    by_cases hy : G.hom y = closedPoint R
    · obtain ⟨z, hzc, hyz, hz⟩ := exists_closed_spec R G hG.quasiCompact y hy
      obtain ⟨V, hzV, t⟩ := GlobalTheory.T.exists_generator_descendedBundle_near_closedPoint R hR M G' hG' P' G β hG hpb θ O hO hθ z hzc hz
      exact ⟨V, hyz.mem_open V.isOpen hzV, t⟩
    · exact GlobalTheory.T.exists_generator_off_closedFibre_descended R hR M G' hG' P' G β hG hpb θ O hO hθ y hy
  exact GlobalTheory.T.exists_lineBundle_descent_bijective_app _ _ β hbij P'.L.L P'.L.isLB hloc

end GlobalTheory.Mum.CubeDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalBundleModificationDescendsToGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalBundle_modification_descends_to_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∃ L : LB G.left, L.IsLB ∧ LBIso P'.L.L (L.pull β) := by
  first | exact @GlobalTheory.Mum.CubeDesc.cubicalBundle_descends | exact GlobalTheory.Mum.CubeDesc.cubicalBundle_descends | (intros; apply GlobalTheory.Mum.CubeDesc.cubicalBundle_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenThetaNonvanishingDescendedGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenThetaNonvanishingDescendedGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_open_theta_descent : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (E : Emb π G') (N : Near π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (L : LB G'.left), E.Theta L → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), β ≫ G.hom = G'.hom ≫ π → IsOpenImmersion i.left → N.u ≫ β = pullback.fst _ _ ≫ i.left → ∃ (θ : L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ k, g ∈ G'.left.basicOpen (θ.f k) := by
  intro R _ _ S π hπ G' _ E N fU l hl hlf L hT G β i hβ hi hu
  obtain ⟨θ, OY, ⟨y₀, hy₀⟩, hθ⟩ := hT
  haveI := E.imm
  obtain ⟨W, hW, hWY⟩ := (E.j.isEmbedding.isInducing.isOpen_iff).1 OY.isOpen
  have hrng := GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R S π G' E
  have e1 : ∀ z, E.H.ι (l z) = N.u z := fun z => by rw [← Scheme.Hom.comp_apply, hl]
  have e2 : ∀ z, E.f (l z) = fU (pullback.fst N.U.hom π z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hlf, Scheme.Hom.comp_apply]
  have e3 : ∀ z, β (N.u z) = i.left (pullback.fst N.U.hom π z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hu, Scheme.Hom.comp_apply]
  have e4 : ∀ x, G.hom (β x) = π (G'.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply]
  have hWj : ∀ y, y ∈ OY ↔ E.j y ∈ W := fun y => by
    show y ∈ (OY : Set E.Y.left) ↔ _
    rw [← hWY]; rfl
  refine ⟨θ, ⟨i.left '' (fU ⁻¹' W), i.left.isOpenEmbedding.isOpenMap _ (hW.preimage fU.continuous)⟩, ?_, ?_⟩
  · obtain ⟨g₀, hg₀c, hg₀f⟩ := hrng.2 hπ y₀
    obtain ⟨z, hz⟩ := N.all (E.H.ι g₀) hg₀c
    have hlz : l z = g₀ := E.H.ι.isOpenEmbedding.injective (by rw [e1, hz])
    refine ⟨i.left (pullback.fst N.U.hom π z), ⟨pullback.fst N.U.hom π z, ?_, rfl⟩, ?_⟩
    · show fU (pullback.fst N.U.hom π z) ∈ W
      rw [← e2 z, hlz, hg₀f]
      exact (hWj y₀).1 hy₀
    · rw [← e3, e4, hz]
      exact hg₀c
  · rintro g ⟨w, hw, hwg⟩ hc
    have hc' : π (G'.hom g) = closedPoint R := by rw [← e4]; exact hc
    obtain ⟨z, rfl⟩ := N.all g hc'
    have hzw : pullback.fst N.U.hom π z = w := i.left.isOpenEmbedding.injective (by rw [hwg, ← e3])
    have hc'' : π (G'.hom (E.H.ι (l z))) = closedPoint R := by rw [e1]; exact hc'
    obtain ⟨y, hy⟩ := hrng.1 (l z) hc''
    have hyO : y ∈ OY := (hWj y).2 (by rw [← hy, e2, hzw]; exact hw)
    obtain ⟨k, hk⟩ := hθ (l z) y hyO hc'' hy
    exact ⟨k, by rwa [e1] at hk⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenThetaNonvanishingDescendedGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_thetaNonvanishing_descendedGroup : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (E : Emb π G') (N : Near π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (L : LB G'.left), E.Theta L → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), β ≫ G.hom = G'.hom ≫ π → IsOpenImmersion i.left → N.u ≫ β = pullback.fst _ _ ≫ i.left → ∃ (θ : L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ k, g ∈ G'.left.basicOpen (θ.f k) := by
  first | exact @GlobalTheory.Mum.exists_open_theta_descent | exact GlobalTheory.Mum.exists_open_theta_descent | (intros; apply GlobalTheory.Mum.exists_open_theta_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureOfPushedPointValuesCubeFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureOfPushedPointValuesCubeFunction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
namespace PushCub
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β)

theorem push_one {T : Over S'} : pushHom h T 1 = toUnit _ ≫ η[G] := by
  rw [map_one, Hom.one_def]

theorem face0 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 0 =
    lift (pushHom h (G2 G') 1) (lift (pushHom h (G2 G') (fst G' G')) (pushHom h (G2 G') (snd G' G'))) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem face1 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 1 =
    lift (pushHom h (G2 G') (fst G' G')) (lift (pushHom h (G2 G') 1) (pushHom h (G2 G') (snd G' G'))) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem face2 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 2 =
    lift (pushHom h (G2 G') (fst G' G')) (lift (pushHom h (G2 G') (snd G' G')) (pushHom h (G2 G') 1)) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem pushPt_lift_cubeTriplePoint_of_isGrpPullback (i : Fin 3) : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫ x3 G i =
    pushHom h (G3 G') (x3 G' i) := by
  fin_cases i <;> simp [x3] <;> rfl

theorem pushPt_lift_cubeQuadruplePoint_of_isGrpPullback (i : Fin 4) : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
    (pushPt h.1.w (x4 G' 3)))) ≫ x4 G i = pushHom h (G4 G') (x4 G' i) := by
  fin_cases i <;> simp [x4] <;> rfl

theorem padd_push (i j : Fin 4) : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
    (pushPt h.1.w (x4 G' 3)))) ≫ padd G (x4 G i) (x4 G j) = pushHom h (G4 G') (x4 G' i * x4 G' j) := by
  rw [map_mul, ← pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h i, ← pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h j]
  exact MonObj.comp_mul _ _ _

theorem cubeMapOf_thirdFace_eq_pushPt_lift : (cubeMapOf h).F3 =
    (lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))).left := rfl

theorem sw01 : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫
    lift (x3 G 1) (lift (x3 G 0) (x3 G 2)) =
    lift (pushHom h (G3 G') (x3 G' 1)) (lift (pushHom h (G3 G') (x3 G' 0)) (pushHom h (G3 G') (x3 G' 2))) := by
  simp only [comp_lift, pushPt_lift_cubeTriplePoint_of_isGrpPullback h]

theorem sw12 : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫
    lift (x3 G 0) (lift (x3 G 2) (x3 G 1)) =
    lift (pushHom h (G3 G') (x3 G' 0)) (lift (pushHom h (G3 G') (x3 G' 2)) (pushHom h (G3 G') (x3 G' 1))) := by
  simp only [comp_lift, pushPt_lift_cubeTriplePoint_of_isGrpPullback h]

theorem coc1 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (padd G (x4 G 0) (x4 G 1)) (lift (x4 G 2) (x4 G 3)) =
    lift (pushHom h (G4 G') (x4 G' 0 * x4 G' 1)) (lift (pushHom h (G4 G') (x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h, padd_push h]

theorem coc2 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 0) (lift (x4 G 1) (x4 G 3)) = lift (pushHom h (G4 G') (x4 G' 0)) (lift (pushHom h (G4 G') (x4 G' 1)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h]

theorem coc3 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 0) (lift (padd G (x4 G 1) (x4 G 2)) (x4 G 3)) =
    lift (pushHom h (G4 G') (x4 G' 0)) (lift (pushHom h (G4 G') (x4 G' 1 * x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h, padd_push h]

theorem coc4 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 1) (lift (x4 G 2) (x4 G 3)) = lift (pushHom h (G4 G') (x4 G' 1)) (lift (pushHom h (G4 G') (x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h]

end PushCub
end GlobalTheory.Mum

namespace GlobalTheory.Mum

open PushCub in
theorem cubicalStr_of_push_val : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (t : LB.Gen (Theta G L.L)), t.IsGen → (∀ U, Function.Injective ((lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G2 G).left ⟶ X), (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ a = (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ b → a = b) → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ U, Function.Injective ((lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G4 G).left ⟶ X), (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ a = (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → IsCub (fun a b d : T ⟶ G' => GlobalTheory.CubTransport.thV t z I (pushHom h T a) (pushHom h T b) (pushHom h T d))) → ∃ c : CubicalStr G L, c.t = t := by
  intro S S' G G' _ _ _ _ f β h L t ht i2 c2 i3 c3 i4 c4 hup
  have hv : ∀ {T : Over S'} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι} (V : Over.mk (T.hom ≫ f) ⟶ G3 G)
      (a b d : T ⟶ G'), V = lift (pushHom h T a) (lift (pushHom h T b) (pushHom h T d)) →
      val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t V.left z J =
        GlobalTheory.CubTransport.thV t z J (pushHom h T a) (pushHom h T b) (pushHom h T d) := by
    rintro T z J V a b d rfl; rfl
  refine ⟨{ t := t, isGen := ht, face := fun i => ?_, cubeSymmetric_swap_first := ?_, cubeSymmetric_swap_last := ?_, cocycle := ?_ }, rfl⟩
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i2 c2 fun z J hJ => ?_
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [← Over.comp_left]
    have C := hup (G2 G') z J hJ
    fin_cases i
    · exact (hv _ 1 (fst G' G') (snd G' G') (face0 h)).trans (C.face _ _)
    · exact (hv _ (fst G' G') 1 (snd G' G') (face1 h)).trans (C.face₂ _ _)
    · exact (hv _ (fst G' G') (snd G' G') 1 (face2 h)).trans (C.face₃ _ _)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i3 c3 fun z J hJ => ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [cubeMapOf_thirdFace_eq_pushPt_lift h, ← Over.comp_left]
    have C := hup (G3 G') z J hJ
    exact (hv (T := G3 G') _ (x3 G' 0) (x3 G' 1) (x3 G' 2) rfl).trans ((C.s01 _ _ _).trans
      (hv (T := G3 G') _ (x3 G' 1) (x3 G' 0) (x3 G' 2) (sw01 h)).symm)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i3 c3 fun z J hJ => ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [cubeMapOf_thirdFace_eq_pushPt_lift h, ← Over.comp_left]
    have C := hup (G3 G') z J hJ
    exact (hv (T := G3 G') _ (x3 G' 0) (x3 G' 1) (x3 G' 2) rfl).trans ((C.s12 _ _ _).trans
      (hv (T := G3 G') _ (x3 G' 0) (x3 G' 2) (x3 G' 1) (sw12 h)).symm)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i4 c4 fun z J hJ => ?_
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    refine (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)).symm)
    simp only [← Over.comp_left]
    have C := hup (G4 G') z J hJ
    exact (congrArg₂ (· * ·) (hv _ _ _ _ (coc1 h)) (hv _ _ _ _ (coc2 h))).trans ((C.coc _ _ _ _).trans
      (congrArg₂ (· * ·) (hv _ _ _ _ (coc3 h)) (hv _ _ _ _ (coc4 h))).symm)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureOfPushedPointValuesCubeFunctionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalStructure_of_pushed_point_values_cube_function : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (t : LB.Gen (Theta G L.L)), t.IsGen → (∀ U, Function.Injective ((lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G2 G).left ⟶ X), (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ a = (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ b → a = b) → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ U, Function.Injective ((lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G4 G).left ⟶ X), (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ a = (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → IsCub (fun a b d : T ⟶ G' => GlobalTheory.CubTransport.thV t z I (pushHom h T a) (pushHom h T b) (pushHom h T d))) → ∃ c : CubicalStr G L, c.t = t := by
  first | exact @GlobalTheory.Mum.cubicalStr_of_push_val | exact GlobalTheory.Mum.cubicalStr_of_push_val | (intros; apply GlobalTheory.Mum.cubicalStr_of_push_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportedGeneratorDescendBijectiveApp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportedGeneratorDescendBijectiveApp
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU GlobalTheory.UU.PackageDescent

noncomputable section
namespace GlobalTheory.Mum.BijDescent

variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_gen_descend_val_bij {L : LB X} (π : Y' ⟶ Y)
    (hπ : ∀ V : Y.Opens, Function.Bijective (π.app V).hom) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → val t (r ≫ π) z J = val u r z J := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j),
      (π.app _).hom a = (res (le j) (u.s j)).val := fun j => (hπ _).2 _
  choose a ha using desc
  have hun : ∀ j, IsUnit (a j) := by
    intro j
    obtain ⟨b, hb⟩ := (hπ (LB.wchart L φ j)).2 ((res (le j) (u.s j))⁻¹).val
    refine IsUnit.of_mul_eq_one b ((hπ _).1 ?_)
    rw [map_mul, map_one, ha j, hb]
    exact Units.mul_inv _
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z), π (r y) ∈ LB.wchart L φ j →
      gm (r ≫ π) y (LB.wchart L φ j) (hun j).unit =
      gm r y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j Z r y hy
    have e : pullU π _ (hun j).unit = res (le j) (u.s j) := Units.ext (ha j)
    exact (gm_pull r π y _ hy _).symm.trans ((congrArg (gm r y _) e).trans (gm_res r y (le j) hy _))
  refine ⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext
    ((hπ (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 ?_), fun Z r z J hJ => ?_⟩
  · refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
    have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
    refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
    refine ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε (𝟙 Y' ≫ π) y j j' hy'.1 hy'.2).trans ?_)
      ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans (hv j' _ _ y hy'.2)))
    simp only [trF, Category.id_comp]
  · rw [val_of _ (r ≫ π) z J (fun k => J (r ≫ π ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun k => hJ (r ≫ π ≫ φ k))

theorem exists_descend_bij {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)} (hw : PGen w)
    (hM : M.IsLB) (hL : L.IsLB) (π : Y' ⟶ Y) (hπ : ∀ V : Y.Opens, Function.Bijective (π.app V).hom)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} (hc : ∀ k, φ' k ≫ F = π ≫ φ k) {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I : (Z ⟶ X) → M.ι) (J : (Z ⟶ X') → L.ι), Good M z I → Good L z J →
        val t (r ≫ π) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up hw hM hL a ha
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := fun k => π ≫ φ k) (ε' := ε)
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (hc k)) t₁ ht₁
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I J), Good M z I → Good L z J → val u r z I =
      (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
    intro Z r z I J hI hJ
    rw [vu Z r z I hI, val_of t₁ r z I (fun k => I ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc])]
    exact v₁ Z r z _ _ (Set.mem_iInter.2 fun k => hI ((r ≫ φ' k) ≫ F)) (hJ.mem φ' r)
  obtain ⟨t, ht, vt⟩ := exists_gen_descend_val_bij π hπ φ ε u hu
  exact ⟨t, ht, fun Z r z I J hI hJ => (vt Z r z I hI).trans (key Z r z I J hI hJ)⟩

end GlobalTheory.Mum.BijDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportedGeneratorDescendBijectiveAppStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transported_generator_descend_bijective_app : ∀ {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K] {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)}, PGen w → M.IsLB → L.IsLB → ∀ (π : Y' ⟶ Y), (∀ V : Y.Opens, Function.Bijective (π.app V).hom) → ∀ {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}, (∀ k, φ' k ≫ F = π ≫ φ k) → ∀ {ε : K → ℤ} (a : LB.Gen (LB.LinComb L φ' ε)), a.IsGen → ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I : (Z ⟶ X) → M.ι) (J : (Z ⟶ X') → L.ι), Good M z I → Good L z J → val t (r ≫ π) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  first | exact @GlobalTheory.Mum.BijDescent.exists_descend_bij | exact GlobalTheory.Mum.BijDescent.exists_descend_bij | (intros; apply GlobalTheory.Mum.BijDescent.exists_descend_bij <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeSymmCompatDescendsFromPushedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeSymmCompatDescendsFromPushedPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CubeSymDescent

theorem of_push : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → ∀ x y u : T ⟶ G', cubV c z I (pushHom h T x⁻¹) (pushHom h T y⁻¹) (pushHom h T u⁻¹) * val s (pushHom h T (x * y)).left z I * val s (pushHom h T (x * u)).left z I * val s (pushHom h T (y * u)).left z I = cubV c z I (pushHom h T x) (pushHom h T y) (pushHom h T u) * val s (pushHom h T (x * y * u)).left z I * val s (pushHom h T x).left z I * val s (pushHom h T y).left z I * val s (pushHom h T u).left z I) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J = cubV c z J x y u * val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J := by
  intro S S' G G' _ _ _ _ f β h L c s hs i₃ c₃ hup T x y u z J hJ
  let φs : Fin 2 → (G.left ⟶ G.left) := ![(ι[G]).left, 𝟙 G.left]
  let εs : Fin 2 → ℤ := ![1, -1]
  let a := x3 G 0
  let b := x3 G 1
  let d := x3 G 2
  let A := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
    (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left))
    (LB.pullGen L.L φs εs s (b * d).left)
  have vA : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      val A V.left z J = cubV c z J (V ≫ a)⁻¹ (V ≫ b)⁻¹ (V ≫ d)⁻¹ * val s ((V ≫ a) * (V ≫ b)).left z J *
        val s ((V ≫ a) * (V ≫ d)).left z J * val s ((V ≫ b) * (V ≫ d)).left z J := by
    intro T V z J hJ
    have m1 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left))
      (LB.pullGen L.L φs εs s (b * d).left) V.left
    have m2 := val_mul hJ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left) V.left
    have m3 := val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left) V.left
    refine m1.trans ?_
    rw [m2, m3, val_pull hJ, val_pull hJ, val_pull hJ, val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]
    simp only [← Over.comp_left, comp_lift, GrpObj.comp_inv, MonObj.comp_mul]
    rfl
  let B := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
    (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
    (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d.left)
  have vB : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      val B V.left z J = cubV c z J (V ≫ a) (V ≫ b) (V ≫ d) * val s ((V ≫ a) * (V ≫ b) * (V ≫ d)).left z J *
        val s (V ≫ a).left z J * val s (V ≫ b).left z J * val s (V ≫ d).left z J := by
    intro T V z J hJ
    have m1 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
      (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d.left) V.left
    have m2 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
      (LB.pullGen L.L φs εs s b.left) V.left
    have m3 := val_mul hJ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left) V.left
    have m4 := val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left) V.left
    refine m1.trans ?_
    rw [m2, m3, m4, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ,
      val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]
    simp only [← Over.comp_left, comp_lift, MonObj.comp_mul]
    rfl
  have hcorr : LB.Gen.Corr L.L _ _ _ _ A B := by
    refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB (cubeMapOf h).F3 i₃ (fun a b e => c₃ a b e) fun z J hJ => ?_
    let P : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G :=
      lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))
    have hP : (cubeMapOf h).F3 = P.left := rfl
    have ha : P ≫ a = pushHom h (G3 G') (x3 G' 0) := by simp [P, a, x3]; rfl
    have hb : P ≫ b = pushHom h (G3 G') (x3 G' 1) := by simp [P, b, x3]; rfl
    have hd : P ≫ d = pushHom h (G3 G') (x3 G' 2) := by simp [P, d, x3]; rfl
    rw [hP, vA _ P z J hJ, vB _ P z J hJ, ha, hb, hd]
    have e := hup (G3 G') z J hJ (x3 G' 0) (x3 G' 1) (x3 G' 2)
    simp only [map_inv, map_mul] at e ⊢
    exact e
  have e := val_corr hJ hcorr (lift x (lift y u)).left
  have ha : lift x (lift y u) ≫ a = x := by simp [a, x3]
  have hb : lift x (lift y u) ≫ b = y := by simp [b, x3]
  have hd : lift x (lift y u) ≫ d = u := by simp [d, x3]
  rw [vA _ _ z J hJ, vB _ _ z J hJ, ha, hb, hd] at e
  exact e

end GlobalTheory.CubeSymDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeSymmCompatDescendsFromPushedPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeSymm_compat_descends_from_pushed_points : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → ∀ x y u : T ⟶ G', cubV c z I (pushHom h T x⁻¹) (pushHom h T y⁻¹) (pushHom h T u⁻¹) * val s (pushHom h T (x * y)).left z I * val s (pushHom h T (x * u)).left z I * val s (pushHom h T (y * u)).left z I = cubV c z I (pushHom h T x) (pushHom h T y) (pushHom h T u) * val s (pushHom h T (x * y * u)).left z I * val s (pushHom h T x).left z I * val s (pushHom h T y).left z I * val s (pushHom h T u).left z I) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J = cubV c z J x y u * val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J := by
  first | exact @GlobalTheory.CubeSymDescent.of_push | exact GlobalTheory.CubeSymDescent.of_push | (intros; apply GlobalTheory.CubeSymDescent.of_push <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpDescent
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CPDesc

theorem cancel_of_surjective {X Y : Scheme.{0}} (π : X ⟶ Y) [Surjective π]
    (h : ∀ W, Function.Injective (π.app W)) {Z : Scheme.{0}} (a b : Y ⟶ Z) (hab : π ≫ a = π ≫ b) : a = b := by
  have hb : a.base = b.base := by
    ext y
    obtain ⟨x, rfl⟩ := π.surjective y
    exact congr($hab x)
  refine Scheme.Hom.ext hb fun U ↦ ?_
  have : Mono (π.app (b ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (h _)
  rw [← cancel_mono (π.app _)]
  simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, hab]

end GlobalTheory.Mum.CPDesc

namespace GlobalTheory.Mum
open CPDesc

theorem flat_tensor {S : Scheme.{0}} (G H : Over S) [Flat G.hom] [Flat H.hom] : Flat (G ⊗ H).hom := by
  show Flat (pullback.fst G.hom H.hom ≫ G.hom); infer_instance

theorem exists_cp_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G')
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G →
    IsGrpPullback G' G M.π β → ∀ L : LB G.left, L.IsLB → LBIso P'.L.L (L.pull β) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  intro R _ _ _ hR M G' _ _ _ P' G _ _ β hG h L hL hLw
  obtain ⟨w, hw⟩ := hLw
  obtain ⟨_, -, _, -⟩ := hR
  have hp := (isGen_iff w).1 hw
  obtain ⟨hbijπ, hsurjπ⟩ := GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M
  have := M.proper
  have hf1 : Flat G.hom := by have := hG.smooth; infer_instance
  have hf2 : Flat (G2 G).hom := flat_tensor _ _
  have hf3 : Flat (G3 G).hom := by have := hf2; exact flat_tensor _ _
  have hf4 : Flat (G4 G).hom := by have := hf3; exact flat_tensor _ _
  have key : ∀ {Y Z : Scheme.{0}} (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ M.S), Flat y → IsPullback p q y M.π →
      (∀ V, Function.Bijective (p.app V).hom) ∧ (∀ {X : Scheme.{0}} (a b : Y ⟶ X), p ≫ a = p ≫ b → a = b) := by
    intro Y Z y p q hy hpb
    have hb := GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R M.S Y Z M.π y p q inferInstance inferInstance hbijπ hy hpb
    have : Surjective p := MorphismProperty.of_isPullback hpb.flip hsurjπ
    exact ⟨hb, fun a b e => cancel_of_surjective p (fun V => (hb V).1) a b e⟩
  obtain ⟨A2, A3, A4⟩ := GlobalTheory.T.isPullback_powers_cartesian_group_square h
  have k0 := key (𝟙 (Sp R)) M.π (𝟙 M.S) inferInstance (IsPullback.id_vert M.π)
  have k1 := key G.hom β G'.hom hf1 h.1
  have k2 := key _ _ _ hf2 A2
  have k3 := key _ _ _ hf3 A3
  have k4 := key _ _ _ hf4 A4

  obtain ⟨rig, hr, -⟩ := GlobalTheory.T.exists_transported_generator_descend_bijective_app hp hL P'.L.isLB M.π k0.1 (K := PUnit) (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (fun _ => (cubeMapOf h).e_comm) P'.L.rig P'.L.rigGen

  have hι : (ι[G']).left ≫ β = β ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ β) ≫ _ = _
    rw [Category.id_comp]
  have hc₂ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ β = β ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s, hs, vs⟩ := GlobalTheory.T.exists_transported_generator_descend_bijective_app hp hL P'.L.isLB β k1.1 hc₂ P'.sym P'.sym_gen

  have hc : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ β = (cubeMapOf h).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf h).psum_comm I.down
  obtain ⟨t, ht, vt⟩ := GlobalTheory.T.exists_transported_generator_descend_bijective_app hp hL P'.L.isLB (cubeMapOf h).F3 k3.1 hc P'.c.t P'.c.isGen
  let L₁ : RigLB G := ⟨L, rig, hL, hr⟩
  let Wf : ∀ {T : Over M.S} (z : T.left), ((T.left ⟶ G.left) → L.ι) → ((T.left ⟶ G'.left) → P'.L.L.ι) →
      (T ⟶ G') → (T.left.presheaf.stalk z)ˣ := fun z I J x => gw w x.left z (I (x.left ≫ β)) (J x.left)
  have vcub : ∀ (T : Over M.S) (z : T.left) (I J), Good L z I → Good P'.L.L z J → ∀ a b d : T ⟶ G',
      GlobalTheory.CubTransport.thV (L := L₁) t z I (pushHom h T a) (pushHom h T b) (pushHom h T d) =
        Wf z I J (a * b * d) * (Wf z I J (a * b))⁻¹ * (Wf z I J (a * d))⁻¹ * (Wf z I J (b * d))⁻¹ * Wf z I J a *
          Wf z I J b * Wf z I J d * (Wf z I J 1)⁻¹ * cubV P'.c z J a b d := by
    intro T z I J hI hJ a b d
    have q : (lift a (lift b d)).left ≫ (cubeMapOf h).F3 =
        (lift (pushHom h T a) (lift (pushHom h T b) (pushHom h T d))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    have e := vt _ (lift a (lift b d)).left z I J hI hJ
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b d (fun q => gw w q z (I (q ≫ β)) (J q))) rfl)
  have vsym : ∀ (T : Over M.S) (z : T.left) (I J), Good L z I → Good P'.L.L z J → ∀ a : T ⟶ G',
      val s (pushHom h T a).left z I = Wf z I J a⁻¹ * (Wf z I J a)⁻¹ * val P'.sym a.left z J := by
    intro T z I J hI hJ a
    exact (vs _ a.left z I J hI hJ).trans
      (congrArg₂ (· * ·) (GlobalTheory.UU.prod_sym a (fun q => gw w q z (I (q ≫ β)) (J q))) rfl)
  obtain ⟨c, hct⟩ := GlobalTheory.T.cubicalStructure_of_pushed_point_values_cube_function h L₁ t ht (fun U => (k2.1 U).1) k2.2 (fun U => (k3.1 U).1) k3.2
    (fun U => (k4.1 U).1) k4.2 fun T z I hI => by
      obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt P'.L.isLB z
      refine GlobalTheory.CubTransport.isCub_of_twist (isCub_cubV P'.c hJ) (MonoidHom.id _) (fun a => (Wf z I J a)⁻¹)
        fun a b d => ?_
      rw [MonoidHom.id_apply, MonoidHom.id_apply, MonoidHom.id_apply, vcub T z I J hI hJ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, inv_inv]
      abel
  subst hct
  have symCub := GlobalTheory.T.cubeSymm_compat_descends_from_pushed_points h L₁ c s hs (fun U => (k3.1 U).1) k3.2 fun T z I hI x y u => by
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt P'.L.isLB z
    refine GlobalTheory.UU.sym_cub_alg (MonoidHom.id _) (fun a => (Wf z I J a)⁻¹) (θ := cubV P'.c z J)
      (θ' := fun a b d => cubV c z I (pushHom h T a) (pushHom h T b) (pushHom h T d))
      (σ := fun a => val P'.sym a.left z J) (σ' := fun a => val s (pushHom h T a).left z I) (fun a b d => ?_)
      (fun a => ?_) (P'.sym_cub T x y u z J hJ)
    · have := vcub T z I J hI hJ a b d
      show cubV P'.c z J a b d = _
      rw [show cubV c z I (pushHom h T a) (pushHom h T b) (pushHom h T d) =
        GlobalTheory.CubTransport.thV (L := L₁) c.t z I (pushHom h T a) (pushHom h T b) (pushHom h T d) from rfl, this]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, inv_inv]
      abel
    · show val P'.sym a.left z J = _
      rw [vsym T z I J hI hJ a]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, inv_inv]
      abel
  have symRig : LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s (eSec G)) (LB.oneGen L₁.L) := by
    refine GlobalTheory.GtTorsionPoints.corr_of_val_pull hL M.π (fun U => (k0.1 U).1) (fun a b e => k0.2 a b e)
      fun z I hI => ?_
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt P'.L.isLB z
    have e₁ : M.π ≫ eSec G = eSec G' ≫ β := (cubeMapOf h).e_comm.symm
    have e₂ : eSec G' ≫ (ι[G']).left = eSec G' := by
      rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    have e₃ := vs _ (eSec G') z I J hI hJ
    have e₄ : val P'.sym (eSec G') z J = 1 := by
      have := (val_pull hJ P'.sym (eSec G') (𝟙 _)).symm.trans ((val_corr hJ P'.sym_rig (𝟙 _)).trans (val_one _))
      rwa [Category.id_comp] at this
    rw [val_pull hI, e₁, e₃, e₄, Fin.prod_univ_two, val_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₂, Category.comp_id, zpow_one, zpow_neg,
      mul_inv_cancel, _root_.one_mul]
  exact ⟨⟨L₁, c, s, hs, symRig, fun T x y u z J hJ => symCub T x y u z J hJ⟩, rfl⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cp_descent' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ L : LB G.left, L.IsLB → LBIso P'.L.L (L.pull β) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  first | exact @GlobalTheory.Mum.exists_cp_descent | exact GlobalTheory.Mum.exists_cp_descent | (intros; apply GlobalTheory.Mum.exists_cp_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfClosedFibreEmbedding
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem descend_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (E : Emb M.π G'), E.Theta P'.L.L → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : GlobalTheory.UU.CP G) (β : G'.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G' G M.π β ∧ LBIso P'.L.L (P.L.L.pull β) := by
  intro R _ _ _ hR M G' _ _ hG' P' E hθ
  have : IsNoetherianRing R := hR.1
  have : IsIntegrallyClosed R := hR.2.2.1
  have hs : Surjective M.π := (Modif.appTop_bijective_surjective R M).2
  obtain ⟨N, fU, l, hl, hf⟩ := GlobalTheory.T.exists_smooth_model_near_closedFibre_embedding R hR M G' hG' E
  have hN : N.Law := GlobalTheory.T.mul_descends_near_closed_fibre_of_embedding R hR M G' hG' E N fU l hl hf
  obtain ⟨G, i1, i2, β, i, hG, hβ, hi, hu⟩ := GlobalTheory.T.semiAbelian_descends_of_descends_near_closedFibre R hR M.S M.π M.proper hs M.integral G' hG' N hN
  obtain ⟨θ, O, hO, hθO⟩ := GlobalTheory.T.exists_open_thetaNonvanishing_descendedGroup R M.S M.π hs G' E N fU l hl hf P'.L.L hθ G β i hβ.1.w hi hu
  obtain ⟨L, hL, hLi⟩ := GlobalTheory.T.cubicalBundle_modification_descends_to_group R hR M G' hG' P' G β hG hβ θ O hO hθO
  obtain ⟨P, rfl⟩ := GlobalTheory.T.exists_cp_descent' R hR M G' hG' P' G β hG hβ L hL hLi
  exact ⟨G, i1, i2, P, β, hG, hβ, hLi⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfClosedFibreEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_descends_of_closedFibre_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (E : Emb M.π G'), E.Theta P'.L.L → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : GlobalTheory.UU.CP G) (β : G'.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G' G M.π β ∧ LBIso P'.L.L (P.L.L.pull β) := by
  first | exact @GlobalTheory.Mum.descend_of_emb | exact GlobalTheory.Mum.descend_of_emb | (intros; apply GlobalTheory.Mum.descend_of_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfLabelledCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CoverFin

theorem semiAbelian_of_pull {S T : Scheme.{0}} {G : Over S} [GrpObj G] {f : T ⟶ S} {G' : Over T} [GrpObj G']
    [IsCommMonObj G'] {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, hbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  haveI := hbc
  exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

theorem isLocalHom_of_comap {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (φ : A →+* B)
    (h : (maximalIdeal B).comap φ = maximalIdeal A) : IsLocalHom φ := by
  refine ⟨fun a ha => ?_⟩
  by_contra hn
  have : a ∈ (maximalIdeal B).comap φ := by rw [h]; exact (mem_maximalIdeal a).2 hn
  exact (mem_maximalIdeal _).1 this ha

end GlobalTheory.Mum.CoverFin

open GlobalTheory.Mum.CoverFin

theorem GlobalTheory.Mum.hasFin_of_labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), Nonempty (LabCover D) → HasFin D := by
  intro R _ _ _ hB D ⟨C⟩
  obtain ⟨R', _, _, _, ρ, D', C', E, hρ, hD', hθ⟩ := GlobalTheory.T.exists_labelledCover_embedding_closedFibre R hB D C
  obtain ⟨G, _, _, P, β, hG, hβ, hL⟩ := GlobalTheory.T.semiAbelian_descends_of_closedFibre_embedding R' hρ.1 C'.toModif C'.G C'.semi C'.P E hθ
  haveI : IsNoetherianRing R' := hρ.1.1
  haveI : CharZero R := hB.2
  haveI : CharZero R' := charZero_of_injective_ringHom hρ.2.1
  obtain ⟨V, _, _, _, φ, hV, hφ, hm⟩ := GlobalTheory.PrimeUnif.exists_cdvr R' (maximalIdeal R')
  have hloc : IsLocalHom φ := isLocalHom_of_comap φ hm
  haveI : IsDiscreteValuationRing V := hV.1
  let fφ : FractionRing R' →+* FractionRing V :=
    IsLocalization.map (FractionRing V) φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ)
  have hfφ : ∀ r, fφ (algebraMap R' _ r) = algebraMap V _ (φ r) := fun r => IsLocalization.map_eq _ _
  haveI : IsProper C'.π := C'.proper
  obtain ⟨ξ, -, hξ⟩ := val_exists C'.π (spMap fφ ≫ C'.gp) (spMap φ) (by
    rw [Category.assoc, C'.gp_π]
    show spMap fφ ≫ spMap (algebraMap R' (FractionRing R')) = spMap (algebraMap V (FractionRing V)) ≫ spMap φ
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    exact RingHom.ext fun r => hfφ r)
  obtain ⟨W', _, _, _, io, G'', _, _, β', D'', A'', U'', hD'', hW', hio, hfin, hβ', hL', -⟩ :=
    C'.trait V hV φ ξ hφ hloc hξ
  haveI : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  have hcomp : IsGrpPullback G'' G (spMap (io.comp φ)) (β' ≫ β) :=
    (hβ'.comp hβ).congr (by rw [Category.assoc, hξ, spMap_comp]) rfl
  have h₂ : LBIso (C'.P.L.L.pull β') (P.L.L.pull (β' ≫ β)) :=
    LBIso.chartPull (chartPullPull C'.P.L.L β') (chartPullSame P.L.L _ _ _ β' fun _ => rfl) hL
  have hLc : LBIso U''.LG.L (P.L.L.pull (β' ≫ β)) :=
    LBIso.trans U''.LG.isLB (pull_isLB C'.P.L.isLB β') (pull_isLB P.L.isLB _) hL' h₂
  obtain ⟨R₁, _, _, _, ρ₁, D₁, G₁, _, _, β₁, A₁, U₁, hρ₁, hD₁, hβ₁, -⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisation_of_trait_unif R' ⟨hρ.1, inferInstance⟩ D' G P hG W' hW' (io.comp φ) (hio.comp hφ) inferInstance G'' (β' ≫ β) D'' A'' U''
      hcomp hLc ⟨hD''⟩
  exact GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt_trans R R' ρ hρ D D' hD'
    ⟨R₁, _, _, _, ρ₁, D₁, hρ₁, hD₁, G₁, _, _, A₁, semiAbelian_of_pull hβ₁ hG, ⟨U₁⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfLabelledCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_of_labelledCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), Nonempty (LabCover D) → HasFin D := by
  first | exact @GlobalTheory.Mum.hasFin_of_labCover | exact GlobalTheory.Mum.hasFin_of_labCover | (intros; apply GlobalTheory.Mum.hasFin_of_labCover <;> assumption)
end
