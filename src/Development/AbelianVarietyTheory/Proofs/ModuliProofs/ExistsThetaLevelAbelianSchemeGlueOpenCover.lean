module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLocalOnBaseCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLocalOnBaseCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem sym_inv_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  have e₁ : (𝟙 G' : G' ⟶ G')⁻¹ = GrpObj.inv := by rw [Hom.inv_def, Category.id_comp]
  rw [e₁, Hom.inv_def] at e
  refine e.trans ?_
  show ((𝟙 G' : G' ⟶ G').left ≫ φ) ≫ _ = _
  rw [Over.id_left, Category.id_comp]

theorem sym_of_cover (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A]
    (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (hU : iSup U = ⊤)
    (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (L : LB A.left) (M : ∀ i, LB (G i).left) (hL : L.IsLB)
    (hM : ∀ i, (M i).IsLB) (hw : ∀ i, LBIso (M i) (L.pull (ψ i))) (hs : ∀ i, Out.Sym (G i) (M i)) :
    Out.Sym A L := by
  intro s
  obtain ⟨i, hi⟩ : ∃ i, s ∈ U i := TopologicalSpace.Opens.mem_iSup.1 (by rw [hU]; trivial)
  obtain ⟨V, hV, c, hc⟩ := hs i ⟨s, hi⟩
  obtain ⟨w, hw⟩ := hw i
  refine ⟨(U i).ι ''ᵁ V, ⟨⟨s, hi⟩, hV, rfl⟩, ?_⟩
  have hp := (hψ i).1

  obtain ⟨b, hb⟩ : ∃ b : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).toScheme ⟶ V.toScheme,
      b ≫ V.ι ≫ (U i).ι = (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι ≫ A.hom :=
    ⟨IsOpenImmersion.lift (V.ι ≫ (U i).ι) _ (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, hz, e⟩ := y.2
      exact ⟨⟨z, hz⟩, e⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have sq : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι ≫ A.hom = (b ≫ V.ι) ≫ (U i).ι := by rw [Category.assoc, hb]
  let m := hp.lift _ _ sq
  have m₁ : m ≫ ψ i = (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι := hp.lift_fst _ _ _
  have m₂ : m ≫ (G i).hom = b ≫ V.ι := hp.lift_snd _ _ _
  obtain ⟨n, hn⟩ : ∃ n : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).toScheme ⟶ ((G i).hom ⁻¹ᵁ V).toScheme,
      n ≫ ((G i).hom ⁻¹ᵁ V).ι = m :=
    ⟨IsOpenImmersion.lift _ m (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y ∈ V) m₂).mpr (b y).2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL (hM i) c hc
  refine gen_chartPull (chartPullSame L _ _ _ n fun k => ?_) c₂ h₂
  fin_cases k
  · show _ ≫ _ = n ≫ (_ ≫ _) ≫ ψ i
    rw [Category.assoc, sym_inv_comm (hψ i), ← Category.assoc n, hn, ← Category.assoc m, m₁]
  · show (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι = n ≫ ((G i).hom ⁻¹ᵁ V).ι ≫ ψ i
    rw [← Category.assoc n, hn, m₁]

end GlobalTheory.CoverGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLocalOnBaseCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_local_on_base_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → (∀ i, Out.Sym (G i) (M i)) → Out.Sym A L := by
  first | exact @GlobalTheory.CoverGlue.sym_of_cover | exact GlobalTheory.CoverGlue.sym_of_cover | (intros; apply GlobalTheory.CoverGlue.sym_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsLocalOnBaseOfOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsLocalOnBaseOfOpenCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.WeilLocal

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

private theorem gm_comp_global_eq_gm_units_map {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (c : Γ(X, ⊤)ˣ) :
    gm (f ≫ g) z ⊤ c = gm f z ⊤ (Units.map g.appTop.hom.toMonoidHom c) := by
  unfold gm pullU
  rw [dite_eq_left (show (f ≫ g) z ∈ (⊤ : X.Opens) from trivial), dite_eq_left (show f z ∈ (⊤ : Y.Opens) from trivial)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
  rfl

theorem commIsOf_of_retract (hL : L.IsLB) {T T' : Over S} (g : T' ⟶ T) (h : T ⟶ T') (w : g ≫ h = 𝟙 T')
    {c : Γ(T.left, ⊤)ˣ} (θx' θy' : ThetaGrp A L k T')
    (H : ∀ θx θy : ThetaGrp A L k T, θx.pt = h ≫ θx'.pt → θy.pt = h ≫ θy'.pt → CommIsOf A L k θx θy c) :
    CommIsOf A L k θx' θy' (Units.map g.left.appTop.hom.toMonoidHom c) := by
  obtain ⟨θx, hx, hxv⟩ := exists_pull hL h θx'
  obtain ⟨θy, hy, hyv⟩ := exists_pull hL h θy'
  have Hc := (commIsOf_iff hL θx θy c).1 (H θx θy hx hy)
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  have e := Hc Z (r ≫ (g ▷ A).left) z J hJ
  have e1 : r ≫ (g ▷ A).left ≫ (h ▷ A).left = r := by
    rw [← Over.comp_left, ← comp_whiskerRight, w, id_whiskerRight, Over.id_left, Category.comp_id]
  have e2 : ∀ x : T' ⟶ A, r ≫ (g ▷ A).left ≫ (translT A (h ≫ x)).left ≫ (h ▷ A).left = r ≫ (translT A x).left := by
    intro x
    rw [← Over.comp_left _ _ _ (translT A (h ≫ x)), whisker_translT, Over.comp_left, ← Category.assoc (g ▷ A).left,
      ← Over.comp_left _ _ _ (g ▷ A), ← comp_whiskerRight, w, id_whiskerRight, Over.id_left, Category.id_comp]
  have e3 : r ≫ (g ▷ A).left ≫ (fst T A).left = (r ≫ (fst T' A).left) ≫ g.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left, Category.assoc]
  rw [hxv _ _ _ _ hJ, hxv _ _ _ _ hJ, hyv _ _ _ _ hJ, hyv _ _ _ _ hJ, hx, hy] at e
  simp only [Category.assoc] at e
  rw [e1, e2, e2, e3, gm_comp_global_eq_gm_units_map] at e
  exact e

private theorem exists_overRes_section_image_openImmersion {T T' : Over S} (j : T' ⟶ T) [IsOpenImmersion j.left]
    (V' : T'.left.Opens) :
    ∃ (a : overRes V' ⟶ overRes (j.left ''ᵁ V')) (b : overRes (j.left ''ᵁ V') ⟶ overRes V'),
      b ≫ a = 𝟙 _ ∧ a ≫ overResι (j.left ''ᵁ V') = overResι V' ≫ j := by
  have he : (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι = V'.ι ≫ j.left := Scheme.Hom.isoImage_hom_ι _ _
  refine ⟨Over.homMk (j.left.isoImage V').hom ?_, Over.homMk (j.left.isoImage V').inv ?_, ?_, ?_⟩
  · show (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι ≫ T.hom = V'.ι ≫ T'.hom
    rw [← Category.assoc, he, Category.assoc, Over.w j]
  · show (j.left.isoImage V').inv ≫ V'.ι ≫ T'.hom = (j.left ''ᵁ V').ι ≫ T.hom
    rw [← Over.w j, ← Category.assoc V'.ι, ← he, Category.assoc, Iso.inv_hom_id_assoc]
  · apply Over.OverMorphism.ext
    show (j.left.isoImage V').inv ≫ (j.left.isoImage V').hom = 𝟙 _
    exact Iso.inv_hom_id _
  · apply Over.OverMorphism.ext
    show (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι = V'.ι ≫ j.left
    exact he

theorem local_of_openImmersion (hL : L.IsLB) {T T' : Over S} (j : T' ⟶ T) [IsOpenImmersion j.left]
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (H : WeilIs A L k (j ≫ x) (j ≫ y) (Units.map j.left.appTop.hom.toMonoidHom c)) (p : T'.left) :
    ∃ V : T.left.Opens, j.left p ∈ V ∧
      (∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y) ∧
      ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
        CommIsOf A L k θx θy (unitRes V c) := by
  obtain ⟨V', hpV', ⟨θx₀, θy₀, hx₀, hy₀⟩, HV'⟩ := H p
  obtain ⟨a, b, hba, ha⟩ := exists_overRes_section_image_openImmersion j V'
  have hb : b ≫ overResι V' ≫ j = overResι (j.left ''ᵁ V') := by
    rw [← ha, ← Category.assoc, hba, Category.id_comp]
  refine ⟨j.left ''ᵁ V', ⟨p, hpV', rfl⟩, ?_, ?_⟩
  · obtain ⟨θx, hx, -⟩ := exists_pull hL b θx₀
    obtain ⟨θy, hy, -⟩ := exists_pull hL b θy₀
    refine ⟨θx, θy, ?_, ?_⟩
    · rw [hx, hx₀, ← hb]
      simp only [Category.assoc]
    · rw [hy, hy₀, ← hb]
      simp only [Category.assoc]
  · intro θx θy hx hy
    have key := commIsOf_of_retract hL b a hba θx θy
      (c := unitRes V' (Units.map j.left.appTop.hom.toMonoidHom c))
      (fun θ₁ θ₂ h₁ h₂ => HV' θ₁ θ₂ (by rw [h₁, hx, ← Category.assoc, ha, Category.assoc])
        (by rw [h₂, hy, ← Category.assoc, ha, Category.assoc]))
    have hbl : b.left ≫ V'.ι ≫ j.left = (j.left ''ᵁ V').ι := congrArg Over.Hom.left hb
    have hu : Units.map b.left.appTop.hom.toMonoidHom (unitRes V' (Units.map j.left.appTop.hom.toMonoidHom c)) =
        unitRes (j.left ''ᵁ V') c := by
      unfold unitRes
      rw [← hbl]
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_app,
        CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
      rfl
    rw [hu] at key
    exact key

end GlobalTheory.WeilLocal

theorem GlobalTheory.weilIs_of_openCover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (k : ℤ) (x y : Out.baseOver S ⟶ A) (x' y' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i) (c : Γ(S, ⊤)ˣ), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, (y' i).left ≫ ψ i = (U i).ι ≫ y.left) → (∀ i, Out.WeilIs (G i) (M i) k (x' i) (y' i) (Units.map (U i).ι.appTop.hom.toMonoidHom c)) → Out.WeilIs A L k x y c := by
  intro S I U A _ G _ ψ hU hψ L M hL hM hML hA hG k x y x' y' c hx hy hW
  haveI : IsCommMonObj A := hA.comm
  unfold Out.WeilIs
  intro p
  obtain ⟨i, hi⟩ := GlobalTheory.CoverGlue.exists_mem hU p
  obtain ⟨j, hj⟩ : ∃ j : Over.mk ((Out.baseOver (U i).toScheme).hom ≫ (U i).ι) ⟶ Out.baseOver S,
      j.left = (U i).ι := ⟨Over.homMk (U i).ι (by simp [Out.baseOver]), rfl⟩
  haveI : IsOpenImmersion j.left := by
    rw [hj]
    infer_instance
  have hx₀ : (j ≫ x).left = (x' i).left ≫ ψ i := by rw [Over.comp_left, hj, hx i]
  have hy₀ : (j ≫ y).left = (y' i).left ≫ ψ i := by rw [Over.comp_left, hj, hy i]
  have H₀ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm S (U i).toScheme A (G i) (U i).ι (ψ i) L (M i) hL (hM i)
    (hψ i) (hML i) (Out.baseOver (U i).toScheme) k (x' i) (y' i) (j ≫ x) (j ≫ y)
    (Units.map (U i).ι.appTop.hom.toMonoidHom c) hx₀ hy₀).1 (hW i)
  have H₁ : Out.WeilIs A L k (j ≫ x) (j ≫ y) (Units.map j.left.appTop.hom.toMonoidHom c) := by
    rw [hj]
    exact H₀
  obtain ⟨V, hV, hl, hc⟩ := GlobalTheory.WeilLocal.local_of_openImmersion hL j H₁ ⟨p, hi⟩
  refine ⟨V, ?_, hl, hc⟩
  rw [hj] at hV
  exact hV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsLocalOnBaseOfOpenCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilIs_local_on_base_of_openCover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (k : ℤ) (x y : Out.baseOver S ⟶ A) (x' y' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i) (c : Γ(S, ⊤)ˣ), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, (y' i).left ≫ ψ i = (U i).ι ≫ y.left) → (∀ i, Out.WeilIs (G i) (M i) k (x' i) (y' i) (Units.map (U i).ι.appTop.hom.toMonoidHom c)) → Out.WeilIs A L k x y c := by
  first | exact @GlobalTheory.weilIs_of_openCover | exact GlobalTheory.weilIs_of_openCover | (intros; apply GlobalTheory.weilIs_of_openCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGrpObjOfLocalGroupLawsOnCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGrpObjOfLocalGroupLawsOnCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem exists_grpObj_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (m n : A ⊗ A ⟶ A) (e : Out.baseOver S ⟶ A), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ ψ i ∧ (lift x₀ y₀ ≫ n).left = (x⁻¹).left ≫ ψ i) → (∀ i, (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = (U i).ι ≫ e.left) → ∃ _ : GrpObj A, ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i) := by
  intro S I U A G _ ψ m n e hU hpb hgrp hone

  have hl : ∀ i (T' : Over (U i).toScheme) (a : Over.mk (T'.hom ≫ (U i).ι) ⟶ A),
      ∃ x : T' ⟶ G i, a.left = x.left ≫ ψ i :=
    fun i _ a => GlobalTheory.CoverGlue.exists_lift (hpb i) a
  have hm : ∀ i (T' : Over (U i).toScheme) (a b : Over.mk (T'.hom ≫ (U i).ι) ⟶ A) (x y : T' ⟶ G i),
      a.left = x.left ≫ ψ i → b.left = y.left ≫ ψ i → (lift a b ≫ m).left = (x * y).left ≫ ψ i :=
    fun i T' a b x y ha hb => (hgrp i T' x y a b ha hb).1
  have hn : ∀ i (T' : Over (U i).toScheme) (a b : Over.mk (T'.hom ≫ (U i).ι) ⟶ A) (x y : T' ⟶ G i),
      a.left = x.left ≫ ψ i → b.left = y.left ≫ ψ i → (lift a b ≫ n).left = (x⁻¹).left ≫ ψ i :=
    fun i T' a b x y ha hb => (hgrp i T' x y a b ha hb).2
  obtain ⟨e', he'⟩ : ∃ e' : 𝟙_ (Over S) ⟶ A, e' = e := ⟨e, rfl⟩
  subst he'

  have h1 : ∀ i (T' : Over (U i).toScheme) (p : Over.mk (T'.hom ≫ (U i).ι) ⟶ 𝟙_ (Over S)),
      (p ≫ e').left = (1 : T' ⟶ G i).left ≫ ψ i := by
    intro i T' p
    have hp : p.left = T'.hom ≫ (U i).ι := by
      have h := Over.w p
      first | simpa using h | simpa [Over.tensorUnit_hom] using h | exact (Category.comp_id _).symm.trans h
    have hT : (toUnit T').left = T'.hom := by
      have h := Over.w (toUnit T')
      first | simpa using h | simpa [Over.tensorUnit_hom] using h | exact (Category.comp_id _).symm.trans h
    have h1' : (1 : T' ⟶ G i) = toUnit T' ≫ (1 : Out.baseOver (U i).toScheme ⟶ G i) := by
      rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, ← Category.assoc]
      first | exact congrArg (· ≫ _) (toUnit_unique _ _) | (congr 1; exact toUnit_unique _ _)
    rw [h1']
    first
      | (rw [Over.comp_left, Over.comp_left, Category.assoc, hone i, hp, hT, Category.assoc])
      | (simp only [Over.comp_left, Category.assoc, hone i, hp, hT])
  have ax1 : e' ▷ A ≫ m = (λ_ A).hom := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨p, c, rfl⟩ : ∃ p c, r = lift p c := ⟨_, _, (lift_comp_fst_snd r).symm⟩
    obtain ⟨z, hz⟩ := hl i T' c
    simp only [lift_whiskerRight_assoc, leftUnitor_hom, lift_snd]
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ 1 z (h1 i T' p) hz, _root_.one_mul, hz]
  have ax2 : A ◁ e' ≫ m = (ρ_ A).hom := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨c, p, rfl⟩ : ∃ c p, r = lift c p := ⟨_, _, (lift_comp_fst_snd r).symm⟩
    obtain ⟨z, hz⟩ := hl i T' c
    simp only [lift_whiskerLeft_assoc, rightUnitor_hom, lift_fst]
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ z 1 hz (h1 i T' p), _root_.mul_one, hz]
  have ax3 : m ▷ A ≫ m = (α_ A A A).hom ≫ A ◁ m ≫ m := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨q, c, rfl⟩ : ∃ q c, r = lift q c := ⟨_, _, (lift_comp_fst_snd r).symm⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b, q = lift a b := ⟨_, _, (lift_comp_fst_snd q).symm⟩
    obtain ⟨x, hx⟩ := hl i T' a
    obtain ⟨y, hy⟩ := hl i T' b
    obtain ⟨z, hz⟩ := hl i T' c
    simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ (x * y) z (hm i T' a b x y hx hy) hz,
      hm i T' _ _ x (y * z) hx (hm i T' b c y z hy hz), _root_.mul_assoc]
  have ax4 : lift (lift (𝟙 A) (𝟙 A) ≫ n) (𝟙 A) ≫ m = toUnit A ≫ e' := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨z, hz⟩ := hl i T' r
    simp only [comp_lift_assoc, Category.comp_id]
    rw [← Category.assoc r (toUnit A) e']
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ z⁻¹ z (hn i T' r r z z hz hz) hz, _root_.inv_mul_cancel, h1 i T' (r ≫ toUnit A)]
  have ax5 : lift (𝟙 A) (lift (𝟙 A) (𝟙 A) ≫ n) ≫ m = toUnit A ≫ e' := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨z, hz⟩ := hl i T' r
    simp only [comp_lift_assoc, comp_lift, Category.comp_id]
    rw [← Category.assoc r (toUnit A) e']
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ z z⁻¹ hz (hn i T' r r z z hz hz), _root_.mul_inv_cancel, h1 i T' (r ≫ toUnit A)]
  let inst : GrpObj A :=
    { one := e', mul := m, inv := lift (𝟙 A) (𝟙 A) ≫ n,
      one_mul := ax1, mul_one := ax2, mul_assoc := ax3, left_inv := ax4, right_inv := ax5 }
  refine ⟨inst, fun i => ⟨hpb i, fun T x y x₀ y₀ hx hy => ?_⟩⟩
  rw [CategoryTheory.Hom.mul_def]
  exact hm i T x₀ y₀ x y hx hy

end GlobalTheory.CoverGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGrpObjOfLocalGroupLawsOnCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpObj_of_local_group_laws_on_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (m n : A ⊗ A ⟶ A) (e : Out.baseOver S ⟶ A), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ ψ i ∧ (lift x₀ y₀ ≫ n).left = (x⁻¹).left ≫ ψ i) → (∀ i, (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = (U i).ι ≫ e.left) → ∃ _ : GrpObj A, ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i) := by
  first | exact @GlobalTheory.CoverGlue.exists_grpObj_of_cover | exact GlobalTheory.CoverGlue.exists_grpObj_of_cover | (intros; apply GlobalTheory.CoverGlue.exists_grpObj_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectComparisonMapsCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectComparisonMapsCocycle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaCocycle

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {β : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

def PullsBack (t' : TObj g k J β s') (t : TObj g k J β s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧ ∀ l, (t'.pt l).left ≫ φ = f ≫ (t.pt l).left

private theorem lbIso_pull_comp_of_lbIso_pull {X Y Z : Scheme.{0}} {L : LB X} {L' : LB Y} {f : Y ⟶ X}
    (H : LBIso L' (L.pull f)) (c : Z ⟶ Y) : LBIso (L'.pull c) (L.pull (c ≫ f)) := by
  have a : ChartPull (L'.pull c) L' c :=
    ⟨fun J => J PUnit.unit, fun J y hy => Set.mem_iInter.1 hy PUnit.unit, fun y J J' hJ hJ' => by
      refine (gm_linComb L' (fun _ => c) (fun _ => 1) (𝟙 _) y J J' hJ hJ').trans ?_
      simp⟩
  exact LBIso.chartPull a (chartPullSame L (fun _ => c ≫ f) (fun _ => f) (fun _ => 1) c (fun _ => rfl)) H

theorem PullsBack.comp {t'' : TObj g k J β s''} {t' : TObj g k J β s'} {t : TObj g k J β s} {f' : S'' ⟶ S'} {f : S' ⟶ S}
    {h : S'' ⟶ S} {φ' : t''.A.left ⟶ t'.A.left} {φ : t'.A.left ⟶ t.A.left} (H' : PullsBack t'' t' f' φ')
    (H : PullsBack t' t f φ) (e : f' ≫ f = h) : PullsBack t'' t h (φ' ≫ φ) := by
  obtain ⟨g', l', p'⟩ := H'
  obtain ⟨g₀, l₀, p₀⟩ := H
  subst e
  refine ⟨g'.comp g₀, ?_, fun i => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t'.isLB φ') (pull_isLB t.isLB (φ' ≫ φ)) l'
      (lbIso_pull_comp_of_lbIso_pull l₀ φ')
  · rw [reassoc_of% (p' i), p₀ i, Category.assoc]

theorem PullsBack.cancel {t'' : TObj g k J β s''} {t' : TObj g k J β s'} {t : TObj g k J β s} (f' : S'' ⟶ S') {f : S' ⟶ S}
    {h : S'' ⟶ S} {ψ : t''.A.left ⟶ t.A.left} {φ : t'.A.left ⟶ t.A.left} (H'' : PullsBack t'' t h ψ)
    (H : PullsBack t' t f φ) (e : f' ≫ f = h) : ∃ c, PullsBack t'' t' f' c ∧ c ≫ φ = ψ := by
  obtain ⟨g'', l'', p''⟩ := H''
  obtain ⟨g₀, l₀, p₀⟩ := H
  subst e
  have sq : ψ ≫ t.A.hom = (t''.A.hom ≫ f') ≫ f := by rw [g''.1.w, Category.assoc]
  set c := g₀.1.lift ψ (t''.A.hom ≫ f') sq with hcdef
  have hc₁ : c ≫ φ = ψ := g₀.1.lift_fst _ _ _
  have hc₂ : c ≫ t'.A.hom = t''.A.hom ≫ f' := g₀.1.lift_snd _ _ _
  refine ⟨c, ⟨g₀.cancel (by rw [hc₁]; exact g'') hc₂, ?_, fun i => ?_⟩, hc₁⟩
  · have l₁ := lbIso_pull_comp_of_lbIso_pull l₀ c
    rw [hc₁] at l₁
    exact LBIso.trans t''.isLB (pull_isLB t.isLB ψ) (pull_isLB t'.isLB c) l'' (LBIso.symm l₁)
  · apply g₀.1.hom_ext
    · rw [Category.assoc, hc₁, p'' i, Category.assoc, Category.assoc, p₀ i]
    · rw [Category.assoc, hc₂, ← Category.assoc, Over.w (t''.pt i), Category.assoc, Over.w (t'.pt i)]
      simp [Out.baseOver]

theorem cocycle : (∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' → ∃ t' : TObj g k J b s', TMap t' t f) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (β : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J β ((U i).ι ≫ s)) (u : ∀ i j, TObj g k J β ((U i ⊓ U j).ι ≫ s)) (a : ∀ i j, (u i j).A.left ⟶ (t i).A.left) (b : ∀ i j, (u i j).A.left ⟶ (t j).A.left), (∀ i j, IsGrpPullback (u i j).A (t i).A (S.homOfLE inf_le_left) (a i j) ∧ LBIso (u i j).L ((t i).L.pull (a i j)) ∧ ∀ l, ((u i j).pt l).left ≫ a i j = S.homOfLE inf_le_left ≫ ((t i).pt l).left) → (∀ i j, IsGrpPullback (u i j).A (t j).A (S.homOfLE inf_le_right) (b i j) ∧ LBIso (u i j).L ((t j).L.pull (b i j)) ∧ ∀ l, ((u i j).pt l).left ≫ b i j = S.homOfLE inf_le_right ≫ ((t j).pt l).left) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J β (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∀ i j k (T : Scheme.{0}) (x : T ⟶ (u i j).A.left) (y : T ⟶ (u j k).A.left) (z : T ⟶ (u i k).A.left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k := by
  intro hex o _ g n J β S s I U t u a b ha hb hrig i j m T x y z hxy hxz
  have HA : ∀ i j, PullsBack (u i j) (t i) (S.homOfLE inf_le_left) (a i j) := ha
  have HB : ∀ i j, PullsBack (u i j) (t j) (S.homOfLE inf_le_right) (b i j) := hb
  let V : S.Opens := (U i ⊓ U j) ⊓ (U j ⊓ U m)
  have hVm : V ≤ U m := inf_le_right.trans inf_le_right
  have hVim : V ≤ U i ⊓ U m := le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
  obtain ⟨t', φk, gk, lk, pk, -⟩ := hex o g n J β (U m).toScheme V.toScheme ((U m).ι ≫ s)
    (S.homOfLE hVm ≫ (U m).ι ≫ s) (S.homOfLE hVm) (t m) rfl
  have hk : PullsBack t' (t m) (S.homOfLE hVm) φk := ⟨gk, lk, pk⟩
  obtain ⟨c₁, h₁, e₁⟩ := PullsBack.cancel (S.homOfLE (inf_le_right : V ≤ U j ⊓ U m)) hk (HB j m) (by simp)
  have h₁' : PullsBack t' (t j) (S.homOfLE (inf_le_right.trans inf_le_left : V ≤ U j)) (c₁ ≫ a j m) :=
    h₁.comp (HA j m) (by simp)
  obtain ⟨c₂, h₂, e₂⟩ := PullsBack.cancel (S.homOfLE (inf_le_left : V ≤ U i ⊓ U j)) h₁' (HB i j) (by simp)
  have h₂' : PullsBack t' (t i) (S.homOfLE (inf_le_left.trans inf_le_left : V ≤ U i)) (c₂ ≫ a i j) :=
    h₂.comp (HA i j) (by simp)
  obtain ⟨c₃, h₃, e₃⟩ := PullsBack.cancel (S.homOfLE hVim) h₂' (HA i m) (by simp)
  have h₃' : PullsBack t' (t m) (S.homOfLE hVm) (c₃ ≫ b i m) := h₃.comp (HB i m) (by simp)
  have hφ : φk = c₃ ≫ b i m := hrig V.toScheme m (S.homOfLE hVm) t' φk (c₃ ≫ b i m) inferInstance hk.1 h₃'.1
    hk.2.1 h₃'.2.1 (fun l => by rw [hk.2.2 l, h₃'.2.2 l])
  have hq : (x ≫ (u i j).A.hom) ≫ S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) =
      (y ≫ (u j m).A.hom) ≫ S.homOfLE (inf_le_left : U j ⊓ U m ≤ U j) := by
    rw [Category.assoc, Category.assoc, ← (HB i j).1.1.w, ← (HA j m).1.1.w, ← Category.assoc, hxy, Category.assoc]
  have sq := isPullback_opens_inf_le (X := S) (inf_le_right : U i ⊓ U j ≤ U j) (inf_le_left : U j ⊓ U m ≤ U j)
  obtain ⟨q, hq₁, hq₂⟩ : ∃ q : T ⟶ V.toScheme, q ≫ S.homOfLE (inf_le_left : V ≤ U i ⊓ U j) = x ≫ (u i j).A.hom ∧
      q ≫ S.homOfLE (inf_le_right : V ≤ U j ⊓ U m) = y ≫ (u j m).A.hom :=
    ⟨sq.lift _ _ hq, sq.lift_fst _ _ _, sq.lift_snd _ _ _⟩
  obtain ⟨w, hw₁, hw₂⟩ : ∃ w : T ⟶ t'.A.left, w ≫ c₁ = y ∧ w ≫ t'.A.hom = q :=
    ⟨h₁.1.1.lift y q hq₂.symm, h₁.1.1.lift_fst _ _ _, h₁.1.1.lift_snd _ _ _⟩
  have hwx : w ≫ c₂ = x := by
    apply (HB i j).1.1.hom_ext
    · rw [Category.assoc, e₂, ← Category.assoc, hw₁, hxy]
    · rw [Category.assoc, h₂.1.1.w, ← Category.assoc, hw₂, hq₁]
  have hbase : q ≫ S.homOfLE hVim = z ≫ (u i m).A.hom := by
    have e₅ : ∀ {W : Scheme.{0}} (h : W ⟶ (U i ⊓ U m).toScheme),
        h ≫ (U i ⊓ U m).ι = (h ≫ S.homOfLE (inf_le_left : U i ⊓ U m ≤ U i)) ≫ (U i).ι := fun h => by simp
    rw [← cancel_mono (U i ⊓ U m).ι, Category.assoc, Scheme.homOfLE_ι, e₅ (z ≫ (u i m).A.hom)]
    simp only [Category.assoc]
    rw [← reassoc_of% (HA i m).1.1.w, ← reassoc_of% hxz, reassoc_of% (HA i j).1.1.w, ← reassoc_of% hq₁]
    simp
  have hwz : w ≫ c₃ = z := by
    apply (HA i m).1.1.hom_ext
    · rw [Category.assoc, e₃, ← Category.assoc, hwx, hxz]
    · rw [Category.assoc, h₃.1.1.w, ← Category.assoc, hw₂, hbase]
  calc y ≫ b j m = w ≫ c₁ ≫ b j m := by rw [← Category.assoc, hw₁]
    _ = w ≫ c₃ ≫ b i m := by rw [e₁, hφ]
    _ = z ≫ b i m := by rw [← Category.assoc, hwz]

end GlobalTheory.ThetaCocycle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectComparisonMapsCocycleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaObject_comparison_maps_cocycle : (∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' → ∃ t' : TObj g k J b s', TMap t' t f) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (β : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J β ((U i).ι ≫ s)) (u : ∀ i j, TObj g k J β ((U i ⊓ U j).ι ≫ s)) (a : ∀ i j, (u i j).A.left ⟶ (t i).A.left) (b : ∀ i j, (u i j).A.left ⟶ (t j).A.left), (∀ i j, IsGrpPullback (u i j).A (t i).A (S.homOfLE inf_le_left) (a i j) ∧ LBIso (u i j).L ((t i).L.pull (a i j)) ∧ ∀ l, ((u i j).pt l).left ≫ a i j = S.homOfLE inf_le_left ≫ ((t i).pt l).left) → (∀ i j, IsGrpPullback (u i j).A (t j).A (S.homOfLE inf_le_right) (b i j) ∧ LBIso (u i j).L ((t j).L.pull (b i j)) ∧ ∀ l, ((u i j).pt l).left ≫ b i j = S.homOfLE inf_le_right ≫ ((t j).pt l).left) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J β (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∀ i j k (T : Scheme.{0}) (x : T ⟶ (u i j).A.left) (y : T ⟶ (u j k).A.left) (z : T ⟶ (u i k).A.left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k := by
  first | exact @GlobalTheory.ThetaCocycle.cocycle | exact GlobalTheory.ThetaCocycle.cocycle | (intros; apply GlobalTheory.ThetaCocycle.cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionBasisGeometricFibresOfOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionBasisGeometricFibresOfOpenCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem exists_fac_field {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) (K : Type) [Field K]
    (x : Sp K ⟶ S) : ∃ (i : I) (x' : Sp K ⟶ (U i).toScheme), x' ≫ (U i).ι = x := by
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  obtain ⟨i, hi⟩ := exists_mem hU (x p)
  have hr : Set.range x.base ⊆ Set.range (U i).ι.base := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hq : q = p := Subsingleton.elim (α := PrimeSpectrum K) q p
    subst hq
    exact hi
  exact ⟨i, IsOpenImmersion.lift (U i).ι x hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem map_linComb {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S} {T' : Over S'}
    (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G')) (c : Fin n → ℕ) :
    ρ (Out.linComb x c) = Out.linComb (fun l => ρ (x l)) c := by
  unfold Out.linComb
  rw [map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, map_pow]

private theorem exists_bijective_monoidHom_points_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {ψ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f ψ) (T : Over S') :
    ∃ ρ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G),
      (∀ z, (ρ z).left = z.left ≫ ψ) ∧ Function.Injective ρ ∧ Function.Surjective ρ := by
  have hw : ∀ z : T ⟶ G', (z.left ≫ ψ) ≫ G.hom = T.hom ≫ f := fun z => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w z]
  refine ⟨MonoidHom.mk' (fun z => Over.homMk (z.left ≫ ψ) (hw z)) (fun a b => ?_), fun _ => rfl, ?_, ?_⟩
  · exact Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm
  · intro a b hab
    exact lift_ext h.1 (congrArg CommaMorphism.left hab)
  · intro y
    obtain ⟨z, hz⟩ := exists_lift h.1 y
    exact ⟨z, Over.OverMorphism.ext hz.symm⟩

theorem torsionBasis_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (g k : ℕ) (P : Fin (2 * g) → (Out.baseOver S ⟶ A)) (Q : ∀ i, Fin (2 * g) → (Out.baseOver (U i).toScheme ⟶ G i)), (∀ i l, (Q i l).left ≫ ψ i = (U i).ι ≫ (P l).left) → (∀ i (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ (U i).toScheme) (y : Over.mk x ⟶ G i), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) (fun l => (c l).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ P l) (fun l => (c l).val) = y := by
  intro S I U A _ G _ ψ hU hψ _ _ g k P Q hPQ hQ K _ _ x y hy
  obtain ⟨i, x', rfl⟩ := exists_fac_field hU K x
  obtain ⟨ρ, hρ, hinj, hsurj⟩ := exists_bijective_monoidHom_points_of_isGrpPullback (hψ i) (Over.mk x')
  obtain ⟨y', rfl⟩ := hsurj y
  have hpt : ∀ l, ρ ((Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) =
      (Over.homMk (x' ≫ (U i).ι) (by simp) : Over.mk (x' ≫ (U i).ι) ⟶ Out.baseOver S) ≫ P l := by
    intro l
    apply Over.OverMorphism.ext
    rw [hρ]
    simp [hPQ]
  have hy' : y' ^ k = 1 := hinj (by rw [map_pow, map_one]; exact hy)
  obtain ⟨c, hc, huniq⟩ := hQ i K x' y' hy'
  refine ⟨c, ?_, fun c' hc' => huniq c' (hinj ?_)⟩
  · rw [← hc, map_linComb]
    simp only [hpt]
  · rw [map_linComb]
    simp only [hpt]
    exact hc'

end GlobalTheory.CoverGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionBasisGeometricFibresOfOpenCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionBasis_geometric_fibres_of_open_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (g k : ℕ) (P : Fin (2 * g) → (Out.baseOver S ⟶ A)) (Q : ∀ i, Fin (2 * g) → (Out.baseOver (U i).toScheme ⟶ G i)), (∀ i l, (Q i l).left ≫ ψ i = (U i).ι ≫ (P l).left) → (∀ i (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ (U i).toScheme) (y : Over.mk x ⟶ G i), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) (fun l => (c l).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ P l) (fun l => (c l).val) = y := by
  first | exact @GlobalTheory.CoverGlue.torsionBasis_of_cover | exact GlobalTheory.CoverGlue.torsionBasis_of_cover | (intros; apply GlobalTheory.CoverGlue.torsionBasis_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBinaryOpGluedAlongCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBinaryOpGluedAlongCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem exists_binary_op : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) (ψ : ∀ i, (G i).left ⟶ A.left) (o : ∀ i, G i ⊗ G i ⟶ G i), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (lift x y ≫ o i).left ≫ ψ i = (lift x' y' ≫ o j).left ≫ ψ j) → ∃ m : A ⊗ A ⟶ A, ∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (lift x y ≫ o i).left ≫ ψ i := by
  intro S I U A G ψ o hU hpb hcomp

  let p : (A ⊗ A).left ⟶ S := (A ⊗ A).hom
  let V : I → (A ⊗ A).left.Opens := fun i => p ⁻¹ᵁ U i
  let q : ∀ i, (V i).toScheme ⟶ (U i).toScheme := fun i => p ∣_ U i
  have hP : ∀ i, IsPullback (V i).ι (q i) p (U i).ι := fun i => (isPullback_morphismRestrict p (U i)).flip

  let T₀ : ∀ i, Over (U i).toScheme := fun i => Over.mk (q i)
  let r : ∀ i, Over.mk ((T₀ i).hom ≫ (U i).ι) ⟶ A ⊗ A := fun i =>
    Over.homMk (V i).ι (hP i).w

  have hx : ∀ i, ∃ x : T₀ i ⟶ G i, (r i ≫ fst A A).left = x.left ≫ ψ i := fun i =>
    exists_lift (hpb i) _
  have hy : ∀ i, ∃ y : T₀ i ⟶ G i, (r i ≫ snd A A).left = y.left ≫ ψ i := fun i =>
    exists_lift (hpb i) _
  choose x hx using hx
  choose y hy using hy

  let f : ∀ i, (V i).toScheme ⟶ A.left := fun i => (lift (x i) (y i) ≫ o i).left ≫ ψ i
  have hf : ∀ i j (T : Scheme.{0}) (a : T ⟶ (V i).toScheme) (b : T ⟶ (V j).toScheme),
      a ≫ (V i).ι = b ≫ (V j).ι → a ≫ f i = b ≫ f j := by
    intro i j T a b hab
    let ea : Over.mk (a ≫ q i) ⟶ T₀ i := Over.homMk a rfl
    let eb : Over.mk (b ≫ q j) ⟶ T₀ j := Over.homMk b rfl
    have key := hcomp i j T (a ≫ q i) (b ≫ q j) (ea ≫ x i) (ea ≫ y i) (eb ≫ x j) (eb ≫ y j)
      (by
        simp only [Over.comp_left, Category.assoc, ← hx, ea, eb, Over.homMk_left, r]
        rw [← Category.assoc, hab, Category.assoc])
      (by
        simp only [Over.comp_left, Category.assoc, ← hy, ea, eb, Over.homMk_left, r]
        rw [← Category.assoc, hab, Category.assoc])
    rw [← comp_lift, ← comp_lift] at key
    simpa only [f, ea, eb, Over.homMk_left, Over.comp_left, Category.assoc] using key
  obtain ⟨F, hF, -⟩ := existsUnique_hom (fun i => (V i).ι) (fun i => inferInstance)
    (covers hU hP) f hf

  have hFw : F ≫ A.hom = (A ⊗ A).hom := by
    refine hom_ext (fun i => (V i).ι) (fun i => inferInstance) (covers hU hP) (fun i => ?_)
    rw [reassoc_of% (hF i)]
    simp only [f, Category.assoc, (hpb i).w]
    rw [← Category.assoc (lift (x i) (y i) ≫ o i).left, Over.w]
    exact (hP i).w.symm
  refine ⟨Over.homMk F hFw, ?_⟩
  intro i T x' y' x₀ y₀ hx₀ hy₀
  have hg : (lift x₀ y₀).left ≫ p = T.hom ≫ (U i).ι := Over.w (lift x₀ y₀)
  let k : T.left ⟶ (V i).toScheme := (hP i).lift (lift x₀ y₀).left T.hom hg
  have hk₁ : k ≫ (V i).ι = (lift x₀ y₀).left := (hP i).lift_fst _ _ _
  have hk₂ : k ≫ q i = T.hom := (hP i).lift_snd _ _ _
  let e : T ⟶ T₀ i := Over.homMk k hk₂
  have ex : e ≫ x i = x' := by
    apply lift_ext (hpb i)
    rw [Over.comp_left, Category.assoc, ← hx i, ← hx₀, Over.comp_left]
    change k ≫ (V i).ι ≫ (fst A A).left = _
    rw [reassoc_of% hk₁, ← Over.comp_left, lift_fst]
  have ey : e ≫ y i = y' := by
    apply lift_ext (hpb i)
    rw [Over.comp_left, Category.assoc, ← hy i, ← hy₀, Over.comp_left]
    change k ≫ (V i).ι ≫ (snd A A).left = _
    rw [reassoc_of% hk₁, ← Over.comp_left, lift_snd]
  rw [← ex, ← ey, ← comp_lift, Category.assoc]
  change (lift x₀ y₀).left ≫ F = (k ≫ (lift (x i) (y i) ≫ o i).left) ≫ ψ i
  rw [← hk₁, Category.assoc, hF i, Category.assoc]

end GlobalTheory.CoverGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBinaryOpGluedAlongCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_binary_op_glued_along_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) (ψ : ∀ i, (G i).left ⟶ A.left) (o : ∀ i, G i ⊗ G i ⟶ G i), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (lift x y ≫ o i).left ≫ ψ i = (lift x' y' ≫ o j).left ≫ ψ j) → ∃ m : A ⊗ A ⟶ A, ∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (lift x y ≫ o i).left ≫ ψ i := by
  first | exact @GlobalTheory.CoverGlue.exists_binary_op | exact GlobalTheory.CoverGlue.exists_binary_op | (intros; apply GlobalTheory.CoverGlue.exists_binary_op <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionAndIsMonHomOfOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionAndIsMonHomOfOpenCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens} {A : Over S} [GrpObj A] {G : ∀ i, Over (U i).toScheme}
  [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}

private theorem isGrpPullback_one_left {X' X : Scheme.{0}} {H' : Over X'} [GrpObj H'] {H : Over X} [GrpObj H]
    {g : X' ⟶ X} {φ : H'.left ⟶ H.left} (h : IsGrpPullback H' H g φ) (T : Over X') :
    (1 : Over.mk (T.hom ≫ g) ⟶ H).left = (1 : T ⟶ H').left ≫ φ := by
  have hw : ((1 : T ⟶ H').left ≫ φ) ≫ H.hom = (Over.mk (T.hom ≫ g)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let z : Over.mk (T.hom ≫ g) ⟶ H := Over.homMk ((1 : T ⟶ H').left ≫ φ) hw
  have hz : z * z = z := by
    apply Over.OverMorphism.ext
    rw [h.2 T 1 1 z z rfl rfl, _root_.mul_one]
    rfl
  have hz1 : z = 1 := _root_.mul_eq_left.mp hz
  rw [← hz1]
  rfl

private theorem pow_left_eq_pow_left_comp_of_isGrpPullback {X' X : Scheme.{0}} {H' : Over X'} [GrpObj H'] {H : Over X} [GrpObj H]
    {g : X' ⟶ X} {φ : H'.left ⟶ H.left} (h : IsGrpPullback H' H g φ) {T : Over X'} (y : T ⟶ H')
    (z : Over.mk (T.hom ≫ g) ⟶ H) (hz : z.left = y.left ≫ φ) (n : ℕ) :
    (z ^ n).left = (y ^ n).left ≫ φ := by
  induction n with
  | zero => simpa only [_root_.pow_zero] using isGrpPullback_one_left h T
  | succ n ih =>
    rw [_root_.pow_succ, _root_.pow_succ]
    exact h.2 T _ _ _ _ ih hz

theorem pow_eq_one_of_cover (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (k : ℕ)
    (x : Out.baseOver S ⟶ A) (x' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i)
    (hx : ∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) (hk : ∀ i, x' i ^ k = 1) : x ^ k = 1 := by
  refine over_ext hU fun i T' r => ?_
  rw [MonObj.comp_pow, MonObj.comp_one]
  have hr : r.left = T'.hom ≫ (U i).ι := by simpa using Over.w r
  let t : T' ⟶ Out.baseOver (U i).toScheme := Over.homMk T'.hom (by simp)
  have hy : (t ≫ x' i) ^ k = 1 := by rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  have key := pow_left_eq_pow_left_comp_of_isGrpPullback (hψ i) (t ≫ x' i) (r ≫ x) (by simp [t, hr, hx]) k
  rw [hy, ← isGrpPullback_one_left (hψ i) T'] at key
  exact Over.OverMorphism.ext key

private theorem mul_comp_of_cover_isGrpPullback_isMonHom (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (f : A ⟶ A)
    (f' : ∀ i, G i ⟶ G i) (hf : ∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) (hm : ∀ i, IsMonHom (f' i))
    {T : Over S} (a b : T ⟶ A) : (a * b) ≫ f = (a ≫ f) * (b ≫ f) := by
  refine over_ext hU fun i T' r => ?_
  haveI := hm i
  obtain ⟨a', ha⟩ := exists_lift (hψ i).1 (r ≫ a)
  obtain ⟨b', hb⟩ := exists_lift (hψ i).1 (r ≫ b)
  have e1 := (hψ i).2 T' a' b' (r ≫ a) (r ≫ b) ha hb
  have ha' : (r ≫ a ≫ f).left = (a' ≫ f' i).left ≫ ψ i := by
    have := congrArg (· ≫ f.left) ha
    simp only [Over.comp_left, Category.assoc] at this ⊢
    rw [this, hf]
  have hb' : (r ≫ b ≫ f).left = (b' ≫ f' i).left ≫ ψ i := by
    have := congrArg (· ≫ f.left) hb
    simp only [Over.comp_left, Category.assoc] at this ⊢
    rw [this, hf]
  have e2 := (hψ i).2 T' (a' ≫ f' i) (b' ≫ f' i) (r ≫ a ≫ f) (r ≫ b ≫ f) ha' hb'
  have e3 : (a' * b') ≫ f' i = (a' ≫ f' i) * (b' ≫ f' i) := MonObj.mul_comp _ _ _
  apply Over.OverMorphism.ext
  rw [← Category.assoc, MonObj.comp_mul, MonObj.comp_mul, Over.comp_left, e1, e2, ← e3, Over.comp_left]
  simp only [Category.assoc, hf]

theorem isMonHom_of_cover (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (f : A ⟶ A)
    (f' : ∀ i, G i ⟶ G i) (hf : ∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) (hm : ∀ i, IsMonHom (f' i)) :
    IsMonHom f := by
  have hmul : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) :=
    fun a b => mul_comp_of_cover_isGrpPullback_isMonHom hU hψ f f' hf hm a b
  have hone : ∀ {T : Over S}, (1 : T ⟶ A) ≫ f = 1 := by
    intro T
    have h1 := hmul (1 : T ⟶ A) 1
    rw [_root_.mul_one] at h1
    exact _root_.mul_eq_left.mp h1.symm
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one]
    exact hone
  · rw [MonObj.mul_eq_mul, hmul, MonObj.comp_mul]
    simp

theorem tors_and_isMonHom_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ (k : ℕ) (x : Out.baseOver S ⟶ A) (x' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, x' i ^ k = 1) → x ^ k = 1) ∧ ∀ (f : A ⟶ A) (f' : ∀ i, G i ⟶ G i), (∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) → (∀ i, IsMonHom (f' i)) → IsMonHom f := by
  intro S I U A _ G _ ψ hU hψ _ _
  exact ⟨fun k x x' hx hk => pow_eq_one_of_cover hU hψ k x x' hx hk,
    fun f f' hf hm => isMonHom_of_cover hU hψ f f' hf hm⟩

end GlobalTheory.CoverGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionAndIsMonHomOfOpenCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_and_isMonHom_of_open_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ (k : ℕ) (x : Out.baseOver S ⟶ A) (x' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, x' i ^ k = 1) → x ^ k = 1) ∧ ∀ (f : A ⟶ A) (f' : ∀ i, G i ⟶ G i), (∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) → (∀ i, IsMonHom (f' i)) → IsMonHom f := by
  first | exact @GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover | exact GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover | (intros; apply GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueOpenCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

open CoverGlue

private theorem exists_section_of_compatible_local_sections {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    {G : ∀ i, Over (U i).toScheme} {ψ : ∀ i, (G i).left ⟶ A.left}
    (hp : ∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι)
    (σ : ∀ i, Out.baseOver (U i).toScheme ⟶ G i)
    (hσ : ∀ i j, S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (σ i).left ≫ ψ i =
      S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (σ j).left ≫ ψ j) :
    ∃ x : Out.baseOver S ⟶ A, ∀ i, (σ i).left ≫ ψ i = (U i).ι ≫ x.left := by
  have hc : ∀ p : S, ∃ i, p ∈ Set.range (U i).ι := fun p => by
    obtain ⟨i, hi⟩ := exists_mem hU p
    exact ⟨i, by simpa using hi⟩
  obtain ⟨F, hF⟩ := exists_hom (fun i => (U i).ι) (fun i => inferInstance) hc
    (fun i => (σ i).left ≫ ψ i) (fun i j => isPullback_opens_inf (U i) (U j)) hσ
  have hw : F ≫ A.hom = 𝟙 S := by
    refine hom_ext (fun i => (U i).ι) (fun i => inferInstance) hc (fun i => ?_)
    have h1 := Over.w (σ i)
    rw [reassoc_of% (hF i), (hp i).w, reassoc_of% h1]
    simp
  refine ⟨Over.homMk F (by simpa using hw), fun i => ?_⟩
  simpa using (hF i).symm

private theorem exists_endo_of_compatible_local_endos {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    {G : ∀ i, Over (U i).toScheme} {ψ : ∀ i, (G i).left ⟶ A.left}
    (hp : ∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι)
    {B : I → I → Scheme.{0}} {a : ∀ i j, B i j ⟶ (G i).left} {a' : ∀ i j, B i j ⟶ (G j).left}
    (hB : ∀ i j, IsPullback (a i j) (a' i j) (ψ i) (ψ j)) (e : ∀ i, G i ⟶ G i)
    (he : ∀ i j, a i j ≫ (e i).left ≫ ψ i = a' i j ≫ (e j).left ≫ ψ j) :
    ∃ f : A ⟶ A, ∀ i, (e i).left ≫ ψ i = ψ i ≫ f.left := by
  have hψ : ∀ i, IsOpenImmersion (ψ i) := fun i => isOpenImmersion (hp i)
  have hc := covers hU hp
  obtain ⟨F, hF⟩ := exists_hom ψ hψ hc (fun i => (e i).left ≫ ψ i) hB he
  have hw : F ≫ A.hom = A.hom := by
    refine hom_ext ψ hψ hc (fun i => ?_)
    rw [reassoc_of% (hF i), (hp i).w, reassoc_of% (Over.w (e i))]
  exact ⟨Over.homMk F hw, fun i => (hF i).symm⟩

private theorem hcompl_unit_property_of_isPrime {o : Type} [CommRing o] {S S' : Scheme.{0}} (f : S' ⟶ S) (s : S ⟶ Sp o) (u : oˣ) :
    Units.map f.appTop.hom.toMonoidHom (unitS s u) = unitS (f ≫ s) u := by
  ext
  simp [unitS]
  rfl

theorem exists_tobj_of_cover : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J b ((U i).ι ≫ s)), iSup U = ⊤ → (∀ i j, ∃ u : TObj g k J b ((U i ⊓ U j).ι ≫ s), TMap u (t i) (S.homOfLE inf_le_left) ∧ TMap u (t j) (S.homOfLE inf_le_right)) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J b (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∃ t₀ : TObj g k J b s, ∀ i, TMap (t i) t₀ (U i).ι := by
  intro o _ g k J b S s I U t hU hov hrig
  choose u hl hr using hov
  simp only [TMap] at hl hr
  choose a ha using hl
  choose a' ha' using hr
  have hcoc := GlobalTheory.T.thetaObject_comparison_maps_cocycle tObj_pull o g k J b S s I U t u a a'
    (fun i j => ⟨(ha i j).1, (ha i j).2.1, (ha i j).2.2.1⟩)
    (fun i j => ⟨(ha' i j).1, (ha' i j).2.1, (ha' i j).2.2.1⟩) hrig
  obtain ⟨A, ψ, hp, hB⟩ := GlobalTheory.T.glue_schemes_over_opens_along_cocycle S I U (fun i => (t i).A) (fun i j => (u i j).A) a a'
    (fun i j => (ha i j).1.1) (fun i j => (ha' i j).1.1) hcoc
  have hgl := GlobalTheory.T.group_laws_on_cover_agree_on_common_points S I U A (fun i => (t i).A) ψ (fun i j => (u i j).A) a a' hp
    (fun i j => (ha i j).1) (fun i j => (ha' i j).1) hB
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_binary_op_glued_along_cover S I U A (fun i => (t i).A) ψ (fun i => μ) hU hp
    (fun i j T r r' x y x' y' hx hy => by
      simpa only [Hom.mul_def] using (hgl.1 i j T r r' x y x' y' hx hy).1)
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_binary_op_glued_along_cover S I U A (fun i => (t i).A) ψ (fun i => fst _ _ ≫ ι) hU hp
    (fun i j T r r' x y x' y' hx hy => by
      simpa only [lift_fst_assoc, Hom.inv_def] using (hgl.1 i j T r r' x y x' y' hx hy).2)
  obtain ⟨e, he⟩ := exists_section_of_compatible_local_sections hU hp (fun i => (1 : Out.baseOver (U i).toScheme ⟶ (t i).A)) hgl.2
  obtain ⟨inst, hgp⟩ := GlobalTheory.T.exists_grpObj_of_local_group_laws_on_cover S I U A (fun i => (t i).A) ψ m n e hU hp
    (fun i T x y x₀ y₀ hx hy => ⟨by simpa only [Hom.mul_def] using hm i T x y x₀ y₀ hx hy,
      by simpa only [lift_fst_assoc, Hom.inv_def] using hn i T x y x₀ y₀ hx hy⟩) he
  have hab := GlobalTheory.T.isAbelianScheme_and_relDim_of_open_cover S I U A (fun i => (t i).A) ψ hU hgp
  have hA : IsAbelianScheme A := hab.1 (fun i => (t i).ab)
  obtain ⟨L, hL, hrigL, hLi⟩ := GlobalTheory.T.exists_glue_rigidified_lineBundles_cover S I U A (fun i => (t i).A) ψ hU hgp hA (fun i => (t i).ab)
    (fun i => (t i).L) (fun i j => (u i j).A.left) a a' hB (fun i => (t i).isLB) (fun i => (t i).rigid)
    (fun i j => LBIso.trans (pull_isLB (t i).isLB _) (u i j).isLB (pull_isLB (t j).isLB _)
      (ha i j).2.1.symm (ha' i j).2.1)
  choose P hP using fun l => exists_section_of_compatible_local_sections hU hp (fun i => (t i).pt l) (fun i j => by
    rw [← Category.assoc, ← (ha i j).2.2.1 l, Category.assoc, (hB i j).w, ← Category.assoc,
      (ha' i j).2.2.1 l, Category.assoc])
  choose F hF using fun w => exists_endo_of_compatible_local_endos hU hp hB (fun i => (t i).act w) (fun i j => by
    rw [← Category.assoc, ← (ha i j).2.2.2 w, Category.assoc, (hB i j).w, ← Category.assoc,
      (ha' i j).2.2.2 w, Category.assoc])
  have h82 := GlobalTheory.T.torsion_and_isMonHom_of_open_cover S I U A (fun i => (t i).A) ψ hU hgp hA (fun i => (t i).ab)
  have hsym := GlobalTheory.T.symmetric_local_on_base_cover S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
    (fun i => (t i).isLB) hLi (fun i => (t i).sym)
  have hamp := GlobalTheory.T.relAmple_of_open_cover_grpPullback_relAmple S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
    (fun i => (t i).isLB) hLi hA (fun i => (t i).ab) (fun i => (t i).ample)
  have hkt := GlobalTheory.T.thetaGroupKernel_trivial_of_open_cover S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
    (fun i => (t i).isLB) hLi hA (fun i => (t i).ab) (fun i => (t i).ktriv)
  have htor : ∀ l, P l ^ k = 1 := fun l =>
    h82.1 k (P l) (fun i => (t i).pt l) (fun i => hP l i) (fun i => (t i).torsion l)
  have hbij := GlobalTheory.T.torsionBasis_geometric_fibres_of_open_cover S I U A (fun i => (t i).A) ψ hU hgp hA (fun i => (t i).ab) g k P
    (fun i => (t i).pt) (fun i l => hP l i) (fun i => (t i).bij)
  have hunit : ∀ i, Units.map (U i).ι.appTop.hom.toMonoidHom (unitS s b.ζ) = unitS ((U i).ι ≫ s) b.ζ :=
    fun i => hcompl_unit_property_of_isPrime (U i).ι s b.ζ
  have hpair : ∀ l l', Out.WeilIs A L k (P l) (P l') (unitS s b.ζ ^ Out.stdSymp g l l') := fun l l' =>
    GlobalTheory.T.weilIs_local_on_base_of_openCover S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
      (fun i => (t i).isLB) hLi hA (fun i => (t i).ab) k (P l) (P l') (fun i => (t i).pt l)
      (fun i => (t i).pt l') _ (fun i => hP l i) (fun i => hP l' i) (fun i => by
        rw [map_zpow, hunit i]
        exact (t i).pairing l l')
  have hhom : ∀ w, IsMonHom (F w) := fun w =>
    h82.2 (F w) (fun i => (t i).act w) (fun i => hF w i) (fun i => (t i).hom w)
  let t₀ : TObj g k J b s :=
    { A := A
      grp := inst
      ab := hA
      dim := hab.2 g (fun i => (t i).dim)
      L := L
      isLB := hL
      rigid := hrigL
      sym := hsym
      ample := hamp
      ktriv := hkt
      pt := P
      torsion := htor
      bij := hbij
      pairing := hpair
      act := F
      hom := hhom }
  exact ⟨t₀, fun i => ⟨ψ i, hgp i, hLi i, fun l => hP l i, fun w => hF w i⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueOpenCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLevelAbelianScheme_glue_openCover : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J b ((U i).ι ≫ s)), iSup U = ⊤ → (∀ i j, ∃ u : TObj g k J b ((U i ⊓ U j).ι ≫ s), TMap u (t i) (S.homOfLE inf_le_left) ∧ TMap u (t j) (S.homOfLE inf_le_right)) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J b (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∃ t₀ : TObj g k J b s, ∀ i, TMap (t i) t₀ (U i).ι := by
  first | exact @GlobalTheory.exists_tobj_of_cover | exact GlobalTheory.exists_tobj_of_cover | (intros; apply GlobalTheory.exists_tobj_of_cover <;> assumption)
end
