module

public import Development.EtaleCohomology.EtaleSheaves.LeafMapFPPf
public import Development.EtaleCohomology.EtaleSheaves.LeafDescendMapPf
public import Development.EtaleCohomology.EtaleSheaves.LeafTw0GenFreeOf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafLimFPPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf LateralTheory.E.LeafMapFPPf

namespace LateralTheory.E.LeafLimFPPf

theorem isLimit_pullback_finitelyGenerated : LeafLimFP := by
  intro k _ Ω _ _ R hR C1 D1 c1 q1 v1 hs _
  refine ⟨IsLimit.ofExistsUnique fun s => ?_⟩
  let o : GlobalTheory.FGAbove R := ⟨R, hR, le_rfl⟩
  let a : ∀ S : GlobalTheory.FGAbove R, s.pt ⟶ pullback q1 (incl S.2.2) := fun S => s.π.app (op S)
  have ha : ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1), a T ≫ dgMap q1 S.2.2 T.2.2 h = a S :=
    fun S T h => s.w (homOfLE (show S ≤ T from h)).op
  have hsnd : ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1),
      (a T ≫ pullback.snd _ _) ≫ incl h = a S ≫ pullback.snd _ _ := fun S T h => by
    rw [← ha S T h, Category.assoc, Category.assoc, dgMap_snd]
  obtain ⟨ψ, hψ⟩ := GlobalTheory.FGAbove.exists_ringHom hR
    (fun S => ((Scheme.ΓSpecIso (.of S.1)).inv ≫ (a S ≫ pullback.snd _ _).appTop).hom) (by
      intro S T h x
      rw [← hsnd S T h]
      exact (GlobalTheory.appTop_comp_spMap (Subalgebra.inclusion h).toRingHom _ x).symm)
  obtain ⟨b, hb⟩ : ∃ b : s.pt ⟶ Sp Ω, (Scheme.ΓSpecIso (.of Ω)).inv ≫ b.appTop = CommRingCat.ofHom ψ := by
    refine ⟨s.pt.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop]
    simp
  have hb' : ∀ S : GlobalTheory.FGAbove R, b ≫ toR S.1 = a S ≫ pullback.snd _ _ := fun S =>
    GlobalTheory.hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => by
      refine (GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) b x).trans ?_
      rw [hb]
      exact hψ S x))
  have hf : ∀ S : GlobalTheory.FGAbove R, a S ≫ pullback.fst _ _ = a o ≫ pullback.fst _ _ := fun S => by
    rw [← ha o S S.2.2, Category.assoc, dgMap_fst]
  have hw : (a o ≫ pullback.fst _ _) ≫ q1 = b ≫ toR R := by
    conv_rhs => rw [← toR_incl o.2.2]
    rw [← Category.assoc, hb' o, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨hs.lift (a o ≫ pullback.fst _ _) b hw, fun S => ?_, fun m hm => ?_⟩
  · show _ ≫ pullback.lift v1 (c1 ≫ toR S.unop.1) _ = a S.unop
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hs.lift_fst, hf S.unop]
    · rw [Category.assoc, pullback.lift_snd, hs.lift_snd_assoc, hb']
  · change s.pt ⟶ C1 at m
    have hm' : ∀ S : GlobalTheory.FGAbove R, m ≫ pullback.lift v1 (c1 ≫ toR S.1)
        (by rw [Category.assoc, toR_incl, hs.w]) = a S := fun S => hm (op S)
    apply hs.hom_ext
    · rw [hs.lift_fst, ← hm' o, Category.assoc, pullback.lift_fst]
    · rw [hs.lift_snd]
      refine GlobalTheory.hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
      obtain ⟨S, hx⟩ := GlobalTheory.FGAbove.exists_mem hR x
      have e : (m ≫ c1) ≫ toR S.1 = b ≫ toR S.1 := by
        rw [hb', ← hm' S, Category.assoc, Category.assoc, pullback.lift_snd]
      exact (GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) _ ⟨x, hx⟩).symm.trans
        (e ▸ GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) b ⟨x, hx⟩)

end LateralTheory.E.LeafLimFPPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DiagramDescent
section -- merged from Development.EtaleCohomology.EtaleSheaves.DgMapIsPullback
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf LateralTheory.E.LeafMapFPPf

namespace LateralTheory.E.LeafMapFPPf2

theorem dgMap_isPullback {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R : Subalgebra k Ω} {D1 : Scheme.{0}}
    (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S) (hT : R ≤ T) (h : S ≤ T) :
    IsPullback (dgMap q1 hS hT h) (pullback.snd q1 (incl hT)) (pullback.snd q1 (incl hS)) (incl h) := by
  have t : IsPullback (dgMap q1 hS hT h ≫ pullback.fst _ _) (pullback.snd q1 (incl hT)) q1 (incl h ≫ incl hS) := by
    rw [dgMap_fst, incl_comp]; exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right t (dgMap_snd q1 hS hT h) (IsPullback.of_hasPullback _ _)

theorem stages : LeafStagesFP := by
  intro k _ Ω _ _ R D1 q1 hq1
  obtain ⟨_, h2, h3⟩ := hq1
  refine ⟨fun S => ⟨?_, ?_⟩, fun S T h => ?_⟩
  · have : QuasiCompact (pullback.snd q1 (incl S.unop.2.2)) :=
      by
      first
        | exact MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback q1 (incl S.unop.2.2)) h2
    exact @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.snd q1 (incl S.unop.2.2)) this _
  · have : QuasiSeparated (pullback.snd q1 (incl S.unop.2.2)) :=
      by
      first
        | exact MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback q1 (incl S.unop.2.2)) h3
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd q1 (incl S.unop.2.2)) _ this
  · first
      | exact MorphismProperty.of_isPullback (P := @IsAffineHom) (dgMap_isPullback q1 S.2.2 T.2.2 h) inferInstance
      | exact MorphismProperty.of_isPullback (P := @IsAffineHom) (dgMap_isPullback q1 S.2.2 T.2.2 h).flip inferInstance

theorem morphismDescent_of_isLimit (hL : LeafLimFP) : LeafMapFP := LateralTheory.E.LeafMapFPPf.morphismDescent_of_isLimit hL stages

end LateralTheory.E.LeafMapFPPf2

end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.DiagramDescent

theorem descendFP_of (hA : LateralTheory.E.LeafObjFPPf.LeafObjAff) (hG : LateralTheory.E.LeafObjGluePf.LeafGlueTwo)
    (hQ : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct) (hI : LateralTheory.E.LeafInclDescendPf.LeafInclPiece)
    (hL : LateralTheory.E.LeafMapFPPf.LeafLimFP) (hF : LateralTheory.E.LeafPairRelPf.LeafFactorStage) : LeafDescendFP := by
  have hO : LeafObjFP := LateralTheory.E.LeafObjFPPf.objectDescent_of_affineDescent hA
    (LateralTheory.E.LeafObjGluePf.LeafObjGlue_of (LateralTheory.E.LeafInclDescendPf.LeafInclDescend_of hI) hG) hQ
  exact diagramDescent_of_objects_pairs_triples hO (LateralTheory.E.LeafPairFPPf.pairDescent_of_objects_morphisms hO (LateralTheory.E.LeafMapFPPf2.morphismDescent_of_isLimit hL))
    (LateralTheory.E.LeafTripleFPPf.tripleDescent_of_pairRelation (LateralTheory.E.LeafPairRelPf.LeafPairRel_of hO hF))

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem cond {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D} {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    v ≫ g = (c ≫ toR R') ≫ incl hR := by
  rw [Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_incl]; exact h.w

theorem sq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D} {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (cond hR h)) c (pullback.snd g (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g (incl hR))
  rw [pullback.lift_fst, LateralTheory.E.LeafDescendMapPf.toR_incl]; exact h

theorem LeafDescendPreMap_of (hA : LateralTheory.E.LeafObjFPPf.LeafObjAff) (hG : LateralTheory.E.LeafObjGluePf.LeafGlueTwo)
    (hQ : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct) (hI : LateralTheory.E.LeafInclDescendPf.LeafInclPiece)
    (hL : LateralTheory.E.LeafMapFPPf.LeafLimFP) (hF : LateralTheory.E.LeafPairRelPf.LeafFactorStage) :
    LateralTheory.E.QuasiFiniteDescent.LeafDescendPreMap := by
  intro k _ X p _ Ω _ _ C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hRfg, D0, D1, D2, q, d1, d2, v0, v1, v2, hpre⟩ :=
    descendFP_of hA hG hQ hI hL hF k Ω c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨hq0, hq1, hq2, p0, p1, p2, m1, m2⟩ := hpre
  have : LocallyOfFinitePresentation p := LateralTheory.E.LeafDescendMapPf.lfp p
  let bk := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hlfp : LocallyOfFinitePresentation (pullback.snd p bk) := inferInstance
  have ha : e ≫ p = (c0 ≫ toR R) ≫ bk := by
    rw [he, Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_base]
  obtain ⟨R', h, hR'fg, g, hg1, hg2⟩ := hF k Ω R hRfg c0 q v0 hq0 p0 (pullback.snd p bk) hlfp
    (pullback.lift e (c0 ≫ toR R) ha) (pullback.lift_snd _ _ _)
  let e1 : pullback (d1 ≫ q) (incl h) ⟶ pullback q (incl h) :=
    pullback.map _ _ _ _ d1 (𝟙 _) (𝟙 _) (by simp) (by simp)
  let e2 : pullback (d2 ≫ d1 ≫ q) (incl h) ⟶ pullback (d1 ≫ q) (incl h) :=
    pullback.map _ _ _ _ d2 (𝟙 _) (𝟙 _) (by simp) (by simp)
  have E1 : e1 ≫ pullback.snd q (incl h) = pullback.snd (d1 ≫ q) (incl h) := by
    simp only [e1, pullback.map, pullback.lift_snd, Category.comp_id]
  have E2 : e2 ≫ e1 ≫ pullback.snd q (incl h) = pullback.snd (d2 ≫ d1 ≫ q) (incl h) := by
    rw [E1]; simp only [e2, pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨R', hR'fg, _, _, _, pullback.snd q (incl h), e1, e2, g ≫ pullback.fst p bk,
    pullback.lift v0 (c0 ≫ toR R') (cond h p0), pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (cond h p1),
    pullback.lift v2 ((γ2 ≫ γ1 ≫ c0) ≫ toR R') (cond h p2), ?_, ⟨fp_snd _ _ hq0, ?_, ?_, sq h p0, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg1, Category.assoc,
      LateralTheory.E.LeafDescendMapPf.incl_base]
  · rw [E1]; exact fp_snd _ _ hq1
  · rw [E2]; exact fp_snd _ _ hq2
  · rw [E1]; exact sq h p1
  · rw [E2]; exact sq h p2
  · apply pullback.hom_ext
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact m1
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · apply pullback.hom_ext
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact m2
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · rw [← Category.assoc, hg2, pullback.lift_fst]

end LateralTheory.E.DiagramDescent

end
end
