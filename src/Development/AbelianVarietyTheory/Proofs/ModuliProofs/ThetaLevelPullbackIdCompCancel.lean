module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

theorem lbIso_pull_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X}
    (H : LBIso L' (L.pull φ)) (φ' : X'' ⟶ X') : LBIso (L'.pull φ') (L.pull (φ' ≫ φ)) :=
  LBIso.chartPull (chartPullPull L' φ' φ' rfl) (chartPullSame L _ _ _ φ' fun _ => rfl) H

theorem TMap.refl (t : TObj g k J b s) : TMap t t (𝟙 S) := by
  refine ⟨𝟙 _, ?_, ?_, fun i => by simp, fun j => by simp⟩
  · have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
    exact isGrpPullback_of_iso (Iso.refl t.A)
  · exact LBIso.chartPull (chartPullId t.L) (chartPullPull t.L _ _ rfl) (GlobalTheory.PolBaseChange.lbIso_refl t.isLB)

theorem TMap.comp {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h' : TMap t'' t' f') (h : TMap t' t f) : TMap t'' t (f' ≫ f) := by
  obtain ⟨φ, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨φ', k₁, k₂, k₃, k₄⟩ := h'
  refine ⟨φ' ≫ φ, k₁.comp h₁, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) k₂ (lbIso_pull_comp h₂ φ')
  · rw [← Category.assoc, k₃, Category.assoc, h₃, Category.assoc]
  · rw [← Category.assoc, k₄, Category.assoc, h₄, Category.assoc]

theorem TMap.cancel {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h : TMap t' t f) (n : TMap t'' t (f' ≫ f)) : TMap t'' t' f' := by
  obtain ⟨φ, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨ψ, k₁, k₂, k₃, k₄⟩ := n
  have hp := h₁.1
  obtain ⟨F, hF, hw⟩ : ∃ F : t''.A.left ⟶ t'.A.left, F ≫ φ = ψ ∧ F ≫ t'.A.hom = t''.A.hom ≫ f' :=
    ⟨hp.lift ψ (t''.A.hom ≫ f') (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  subst hF
  refine ⟨F, h₁.cancel k₁ hw, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) k₂ (lbIso_pull_comp h₂ F).symm
  · apply hp.hom_ext
    · rw [Category.assoc, k₃, Category.assoc, Category.assoc, h₃]
    · have a₁ : (t''.pt i).left ≫ t''.A.hom = 𝟙 S'' := Over.w (t''.pt i)
      have a₂ : (t'.pt i).left ≫ t'.A.hom = 𝟙 S' := Over.w (t'.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

theorem tmap_id_comp_cancel : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (s'' : S'' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (t'' : TObj g k J b s''), TMap t t (𝟙 S) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S'), TMap t' t f → (TMap t'' t' f' ↔ TMap t'' t (f' ≫ f)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ t _ _ => ⟨TMap.refl t, fun _ _ h => ⟨fun h' => h'.comp h, fun n => h.cancel n⟩⟩

end GlobalTheory.ZM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevelPullback_id_comp_cancel : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (s'' : S'' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (t'' : TObj g k J b s''), TMap t t (𝟙 S) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S'), TMap t' t f → (TMap t'' t' f' ↔ TMap t'' t (f' ≫ f)) := by
  first | exact @GlobalTheory.ZM.tmap_id_comp_cancel | exact GlobalTheory.ZM.tmap_id_comp_cancel | (intros; apply GlobalTheory.ZM.tmap_id_comp_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamRep

theorem hom_ext_loc {X Y : Scheme.{0}} {f g : X ⟶ Y}
    (h : ∀ p : X, ∃ (W : Scheme.{0}) (a : W ⟶ X), IsOpenImmersion a ∧ p ∈ Set.range a ∧ a ≫ f = a ≫ g) : f = g := by
  choose W a ha hp e using h
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X W a
    (fun p => by obtain ⟨y, hy⟩ := hp p; exact ⟨p, y, hy⟩) ha
  exact 𝒰.hom_ext _ _ e

theorem exists_glue {X Y : Scheme.{0}} {I : Type} (U : I → Scheme.{0}) (j : ∀ i, U i ⟶ X) (g : ∀ i, U i ⟶ Y)
    (hj : ∀ i, IsOpenImmersion (j i)) (hc : ∀ p : X, ∃ i, p ∈ Set.range (j i))
    (h : ∀ i i' (y : U i), j i y ∈ Set.range (j i') → ∃ (W : Scheme.{0}) (a : W ⟶ U i) (a' : W ⟶ U i'),
      IsOpenImmersion a ∧ y ∈ Set.range a ∧ a ≫ j i = a' ≫ j i' ∧ a ≫ g i = a' ≫ g i') :
    ∃ G : X ⟶ Y, ∀ i, j i ≫ G = g i := by
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers I U j
    (fun p => by obtain ⟨i, y, hy⟩ := hc p; exact ⟨i, y, hy⟩) hj
  have hg : ∀ i i', pullback.fst (j i) (j i') ≫ g i = pullback.snd (j i) (j i') ≫ g i' := by
    intro i i'
    refine hom_ext_loc fun p => ?_
    obtain ⟨W, a, a', ha, ⟨w, hw⟩, e, e'⟩ := h i i' (pullback.fst (j i) (j i') p)
      ⟨pullback.snd (j i) (j i') p, by rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
    have := hj i'
    have h1 : pullback.lift a a' e ≫ pullback.fst (j i) (j i') = a := pullback.lift_fst _ _ _
    have : IsOpenImmersion (pullback.lift a a' e ≫ pullback.fst (j i) (j i')) := by rw [h1]; exact ha
    refine ⟨W, pullback.lift a a' e, IsOpenImmersion.of_comp _ (pullback.fst (j i) (j i')), ⟨w, ?_⟩, ?_⟩
    · apply (pullback.fst (j i) (j i')).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, h1, hw]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, e']
  exact ⟨𝒰.glueMorphisms g hg, fun i => 𝒰.ι_glueMorphisms g hg i⟩

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (x : X) : x ∈ Set.range a ↔ f x ∈ Set.range g := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨b p, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback h x y hy.symm
    exact ⟨p, hp⟩

theorem mul_left_pre {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (k : T'.left ⟶ T.left)
    (hk : k ≫ T.hom = T'.hom) (x y : T ⟶ G) (x' y' : T' ⟶ G) (hx : x'.left = k ≫ x.left)
    (hy : y'.left = k ≫ y.left) : (x' * y').left = k ≫ (x * y).left := by
  have e1 : x' = (Over.homMk k hk : T' ⟶ T) ≫ x := Over.OverMorphism.ext hx
  have e2 : y' = (Over.homMk k hk : T' ⟶ T) ≫ y := Over.OverMorphism.ext hy
  rw [e1, e2, ← MonObj.comp_mul]
  rfl

theorem isGrpPullback_of_loc {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left) [IsIso φ]
    (w : φ ≫ A'.hom = A.hom)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (B : Over W) (_ : GrpObj B) (a : B.left ⟶ A.left),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) :
    IsGrpPullback A A' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by rw [w, Category.comp_id]⟩, fun T y z y₀ z₀ hy hz => ?_⟩
  refine hom_ext_loc fun q => ?_
  obtain ⟨W, x, B, _, a, hx, hp, ha, hb⟩ := h (T.hom q)
  let k := pullback.fst T.hom x
  let T' : Over W := Over.mk (pullback.snd T.hom x)
  have hk : k ≫ T.hom = T'.hom ≫ x := pullback.condition
  let y' : T' ⟶ B := Over.homMk (ha.1.lift (k ≫ y.left) T'.hom (by rw [Category.assoc, Over.w y, hk]))
    (ha.1.lift_snd _ _ _)
  let z' : T' ⟶ B := Over.homMk (ha.1.lift (k ≫ z.left) T'.hom (by rw [Category.assoc, Over.w z, hk]))
    (ha.1.lift_snd _ _ _)
  have ey : y'.left ≫ a = k ≫ y.left := ha.1.lift_fst _ _ _
  have ez : z'.left ≫ a = k ≫ z.left := ha.1.lift_fst _ _ _
  have e1 := ha.2 T' y' z' (pushPt ha.1.w y') (pushPt ha.1.w z') rfl rfl
  have e2 := hb.2 T' y' z' (pushPt hb.1.w y') (pushPt hb.1.w z') rfl rfl
  have e3 := mul_left_pre (T' := Over.mk (T'.hom ≫ x)) k hk y z (pushPt ha.1.w y') (pushPt ha.1.w z') ey ez
  have e4 := mul_left_pre (T := Over.mk (T.hom ≫ 𝟙 S)) (T' := Over.mk (T'.hom ≫ x)) k
    (by show k ≫ T.hom ≫ 𝟙 S = T'.hom ≫ x; rw [Category.comp_id, hk]) y₀ z₀ (pushPt hb.1.w y') (pushPt hb.1.w z')
    (by show y'.left ≫ a ≫ φ = _; rw [← Category.assoc, ey, hy, Category.assoc])
    (by show z'.left ≫ a ≫ φ = _; rw [← Category.assoc, ez, hz, Category.assoc])
  refine ⟨_, k, inferInstance, (range_of_isPullback (IsPullback.of_hasPullback T.hom x) q).2 hp, ?_⟩
  refine e4.symm.trans (e2.trans ?_)
  rw [← Category.assoc, ← e1, e3, Category.assoc]

theorem lbIso_of_loc (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (rL : Out.Rigidified A L) (rM : Out.Rigidified A M)
    (h : ∀ p : S, ∃ (W B : Scheme.{0}) (x : W ⟶ S) (a : B ⟶ A.left) (c : B ⟶ W),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsPullback a c A.hom x ∧ LBIso (L.pull a) (M.pull a)) : LBIso L M := by
  refine exists_gen_of_local_of_section A.left S A.hom (eSec A) (LB.div M L) (LB.isLB_div hM hL) (Over.w η[A])
    (BaseChangeFns.app_surjective hG S A hA S A.left (𝟙 _) (𝟙 _) A.hom (IsPullback.of_horiz_isIso ⟨by simp⟩))
    (fun p => ?_) ?_
  · obtain ⟨W, B, x, a, c, hx, hp, ha, H⟩ := h p
    have : IsOpenImmersion a := MorphismProperty.of_isPullback ha.flip hx
    refine ⟨x.opensRange, hp, ?_⟩
    have hr : Set.range (A.hom ⁻¹ᵁ x.opensRange).ι ⊆ Set.range a := by
      rintro _ ⟨y, rfl⟩
      exact (range_of_isPullback ha _).2 y.2
    have e := IsOpenImmersion.lift_fac a _ hr
    obtain ⟨w, hw⟩ := H.chartPull (chartPullSame L (fun _ : PUnit => (A.hom ⁻¹ᵁ x.opensRange).ι) _ _ _ fun _ => e.symm)
      (chartPullSame M (fun _ : PUnit => (A.hom ⁻¹ᵁ x.opensRange).ι) _ _ _ fun _ => e.symm)
    exact gen_chartPull (IsoDescent.chartPullDiv M L _) w hw
  · obtain ⟨u, hu⟩ := rL
    obtain ⟨u', hu'⟩ := rM
    obtain ⟨w, hw⟩ := IsoDescent.lbIso_of_gens hL hM _ _ _ _ u hu u' hu'
    exact gen_chartPull (IsoDescent.chartPullDiv M L _) w hw

variable {o : Type} [CommRing o] {S S' S'' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

def IsTM (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left

theorem tMap_iff {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} : TMap t' t f ↔ ∃ φ, IsTM t' t f φ := Iff.rfl

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (h : Z ⟶ Y) :
    LBIso ((L.pull f).pull h) (L.pull (h ≫ f)) :=
  (PolBaseChange.lbIso_refl (LB.isLB_pull hL (h ≫ f))).chartPull
    (chartPullOut L (fun _ : PUnit => f) (fun _ => 1) h _ fun _ => rfl) (chartPullId _)

theorem lbIso_pull {Y Z : Scheme.{0}} {L M : LB Y} (H : LBIso L M) (h : Z ⟶ Y) : LBIso (L.pull h) (M.pull h) :=
  H.chartPull (chartPullPull L h h rfl) (chartPullPull M h h rfl)

theorem IsTM.congr {t' : TObj g k J b s'} {t : TObj g k J b s} {f f' : S' ⟶ S} {φ φ' : t'.A.left ⟶ t.A.left}
    (h : IsTM t' t f φ) (e : f = f') (e' : φ = φ') : IsTM t' t f' φ' := e ▸ e' ▸ h

theorem IsTM.comp {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    {φ : t'.A.left ⟶ t.A.left} {φ' : t''.A.left ⟶ t'.A.left} (h' : IsTM t'' t' f' φ') (h : IsTM t' t f φ) :
    IsTM t'' t (f' ≫ f) (φ' ≫ φ) := by
  refine ⟨h'.1.comp h.1, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (LB.isLB_pull t'.isLB _) (LB.isLB_pull t.isLB _) h'.2.1
      (LBIso.trans (LB.isLB_pull t'.isLB _) (LB.isLB_pull (LB.isLB_pull t.isLB _) _) (LB.isLB_pull t.isLB _)
        (lbIso_pull h.2.1 φ') (lbIso_pull_pull t.isLB φ φ'))
  · rw [← Category.assoc, h'.2.2.1, Category.assoc, h.2.2.1, Category.assoc]
  · rw [← Category.assoc, h'.2.2.2, Category.assoc, h.2.2.2, Category.assoc]

theorem IsTM.cancel {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    {φ : t'.A.left ⟶ t.A.left} {ψ : t''.A.left ⟶ t.A.left} (h : IsTM t' t f φ) (n : IsTM t'' t (f' ≫ f) ψ) :
    ∃ φ', φ' ≫ φ = ψ ∧ IsTM t'' t' f' φ' := by
  have hp := h.1.1
  let F : t''.A.left ⟶ t'.A.left := hp.lift ψ (t''.A.hom ≫ f') (by rw [n.1.1.w, Category.assoc])
  have hF : F ≫ φ = ψ := hp.lift_fst _ _ _
  have hw : F ≫ t'.A.hom = t''.A.hom ≫ f' := hp.lift_snd _ _ _
  refine ⟨F, hF, h.1.cancel (by rw [hF]; exact n.1) hw, ?_, fun i => ?_, fun j => ?_⟩
  · have H := n.2.1
    rw [← hF] at H
    exact LBIso.trans t''.isLB (LB.isLB_pull t.isLB _) (LB.isLB_pull t'.isLB _) H
      (LBIso.trans (LB.isLB_pull t'.isLB _) (LB.isLB_pull (LB.isLB_pull t.isLB _) _) (LB.isLB_pull t.isLB _)
        (lbIso_pull h.2.1 F) (lbIso_pull_pull t.isLB φ F)).symm
  · apply hp.hom_ext
    · rw [Category.assoc, hF, n.2.2.1, Category.assoc, Category.assoc, h.2.2.1]
    · have a1 : (t''.pt i).left ≫ t''.A.hom = 𝟙 _ := Over.w _
      have a2 : (t'.pt i).left ≫ t'.A.hom = 𝟙 _ := Over.w _
      rw [Category.assoc, hw, ← Category.assoc, a1, Category.assoc, a2]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, hF, n.2.2.2, Category.assoc, h.2.2.2, ← Category.assoc, hF]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

theorem tMap_comp {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h' : TMap t'' t' f') (h : TMap t' t f) : TMap t'' t (f' ≫ f) := by
  obtain ⟨φ', h'⟩ := tMap_iff.1 h'
  obtain ⟨φ, h⟩ := tMap_iff.1 h
  exact tMap_iff.2 ⟨_, h'.comp h⟩

theorem tMap_cancel {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h : TMap t' t f) (n : TMap t'' t (f' ≫ f)) : TMap t'' t' f' := by
  obtain ⟨φ, h⟩ := tMap_iff.1 h
  obtain ⟨ψ, n⟩ := tMap_iff.1 n
  obtain ⟨φ', -, H⟩ := h.cancel n
  exact tMap_iff.2 ⟨_, H⟩

theorem exists_glue_tm (t t' : TObj g k J b s) {I : Type} (W : I → Scheme.{0}) (x : ∀ i, W i ⟶ S)
    (u : ∀ i, TObj g k J b (x i ≫ s)) (a : ∀ i, (u i).A.left ⟶ t.A.left) (a' : ∀ i, (u i).A.left ⟶ t'.A.left)
    (hx : ∀ i, IsOpenImmersion (x i)) (hc : ∀ p : S, ∃ i, p ∈ Set.range (x i))
    (ha : ∀ i, IsTM (u i) t (x i) (a i)) (ha' : ∀ i, IsTM (u i) t' (x i) (a' i))
    (hp : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ S), ∃ w : TObj g k J b (z ≫ s), TMap w t z)
    (hu : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ S) (w : TObj g k J b (z ≫ s)) φ φ', IsOpenImmersion z →
      IsTM w t' z φ → IsTM w t' z φ' → φ = φ') :
    ∃ φ : t.A.left ⟶ t'.A.left, ∀ i, a i ≫ φ = a' i := by
  have hao : ∀ i, IsOpenImmersion (a i) := fun i => MorphismProperty.of_isPullback (ha i).1.1.flip (hx i)
  refine exists_glue _ a a' hao (fun q => ?_) fun i i' y hy => ?_
  · obtain ⟨i, hi⟩ := hc (t.A.hom q)
    exact ⟨i, (range_of_isPullback (ha i).1.1 q).2 hi⟩
  · have := hx i
    have := hx i'
    have := hao i
    have h1 := (range_of_isPullback (ha i).1.1 (a i y)).1 ⟨y, rfl⟩
    have h2 := (range_of_isPullback (ha i').1.1 (a i y)).1 hy
    obtain ⟨R, z, hz, hq, hr⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (U := (x i).opensRange ⊓ (x i').opensRange) (x := t.A.hom (a i y)) ⟨h1, h2⟩
    have e1 := IsOpenImmersion.lift_fac (x i) z (fun p hp => (hr hp).1)
    have e2 := IsOpenImmersion.lift_fac (x i') z (fun p hp => (hr hp).2)
    obtain ⟨w, hw⟩ := hp R z
    obtain ⟨c, hw⟩ := tMap_iff.1 hw
    obtain ⟨d, hd, Hd⟩ := (ha i).cancel (hw.congr e1.symm rfl)
    obtain ⟨d', hd', Hd'⟩ := (ha i').cancel (hw.congr e2.symm rfl)
    have hco : IsOpenImmersion c := MorphismProperty.of_isPullback hw.1.1.flip hz
    have : IsOpenImmersion (d ≫ a i) := by rw [hd]; exact hco
    refine ⟨_, d, d', IsOpenImmersion.of_comp d (a i), ?_, hd.trans hd'.symm,
      hu R z w _ _ hz ((Hd.comp (ha' i)).congr e1 rfl) ((Hd'.comp (ha' i')).congr e2 rfl)⟩
    obtain ⟨q, hq⟩ := (range_of_isPullback hw.1.1 (a i y)).2 hq
    refine ⟨q, (a i).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hd, hq]

theorem tMap_of_loc (hG : Out.GlobalFnsSt) (t t' : TObj g k J b s)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (u : TObj g k J b (x ≫ s)),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ TMap u t x ∧ TMap u t' x)
    (hp : ∀ (t : TObj g k J b s) (R : Type) [CommRing R] (z : Sp R ⟶ S), ∃ w : TObj g k J b (z ≫ s), TMap w t z)
    (hu : ∀ (t : TObj g k J b s) (R : Type) [CommRing R] (z : Sp R ⟶ S) (w : TObj g k J b (z ≫ s)) φ φ',
      IsOpenImmersion z → IsTM w t z φ → IsTM w t z φ' → φ = φ') : TMap t t' (𝟙 S) := by
  choose W x u hx hc ha ha' using h
  choose a ha using fun p => tMap_iff.1 (ha p)
  choose a' ha' using fun p => tMap_iff.1 (ha' p)
  obtain ⟨φ, hφ⟩ := exists_glue_tm t t' W x u a a' hx (fun p => ⟨p, hc p⟩) ha ha' (hp t) (hu t')
  obtain ⟨φ', hφ'⟩ := exists_glue_tm t' t W x u a' a hx (fun p => ⟨p, hc p⟩) ha' ha (hp t') (hu t)
  have ext : ∀ {Y : Scheme.{0}} {f f' : t.A.left ⟶ Y}, (∀ p, a p ≫ f = a p ≫ f') → f = f' := fun H =>
    hom_ext_loc fun q => ⟨_, a (t.A.hom q), MorphismProperty.of_isPullback (ha _).1.1.flip (hx _),
      (range_of_isPullback (ha _).1.1 q).2 (hc _), H _⟩
  have ext' : ∀ {Y : Scheme.{0}} {f f' : t'.A.left ⟶ Y}, (∀ p, a' p ≫ f = a' p ≫ f') → f = f' := fun H =>
    hom_ext_loc fun q => ⟨_, a' (t'.A.hom q), MorphismProperty.of_isPullback (ha' _).1.1.flip (hx _),
      (range_of_isPullback (ha' _).1.1 q).2 (hc _), H _⟩
  have : IsIso φ := ⟨φ', ext fun p => by rw [← Category.assoc, hφ, hφ', Category.comp_id],
    ext' fun p => by rw [← Category.assoc, hφ', hφ, Category.comp_id]⟩
  have gp : IsGrpPullback t.A t'.A (𝟙 S) φ :=
    isGrpPullback_of_loc φ (ext fun p => by rw [← Category.assoc, hφ, (ha p).1.1.w, (ha' p).1.1.w])
      fun p => ⟨W p, x p, (u p).A, inferInstance, a p, hx p, hc p, (ha p).1, by rw [hφ]; exact (ha' p).1⟩
  refine ⟨φ, gp, ?_, fun i => hom_ext_loc fun p => ⟨W p, x p, hx p, hc p, ?_⟩, fun j => ext fun p => ?_⟩
  · refine lbIso_of_loc hG t.ab t.isLB (LB.isLB_pull t'.isLB _) t.rigid (PolBaseChange.rigidified_pull gp t'.rigid)
      fun p => ⟨W p, _, x p, a p, _, hx p, hc p, (ha p).1.1, ?_⟩
    have H := (ha' p).2.1
    rw [← hφ] at H
    exact LBIso.trans (LB.isLB_pull t.isLB _) (u p).isLB (LB.isLB_pull (LB.isLB_pull t'.isLB _) _) (ha p).2.1.symm
      (LBIso.trans (u p).isLB (LB.isLB_pull t'.isLB _) (LB.isLB_pull (LB.isLB_pull t'.isLB _) _) H
        (lbIso_pull_pull t'.isLB φ (a p)).symm)
  · rw [← Category.assoc, ← (ha p).2.2.1, Category.assoc, hφ, (ha' p).2.2.1, Category.id_comp]
  · rw [← Category.assoc, ← (ha p).2.2.2, Category.assoc, hφ, (ha' p).2.2.2, ← Category.assoc, hφ]

end GlobalTheory.FamRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TateIsoFieldExt

theorem exists_unit_of_pow_eq_one {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] [CharZero K]
    (i : K →+* Ω) (n : ℕ) (hn : 0 < n) (z : Ωˣ) (hz : z ^ n = 1) :
    ∃ u : Kˣ, Units.map i.toMonoidHom u = z := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have h2 : IsPrimitiveRoot (i ξ) n := hξ.map_of_injective i.injective
  have hz' : (z : Ω) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  obtain ⟨j, -, hj⟩ := h2.eq_pow_of_pow_eq_one hz'
  refine ⟨(hξ.isUnit hn.ne').unit ^ j, Units.ext ?_⟩
  simpa using hj

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
  {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) {Q Q' : Type} [Group Q] [Group Q'] (f : Q →* Q')
  {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
  {e : ℕ → Q → Q → Kˣ → Prop} {e' : ℕ → Q' → Q' → Ωˣ → Prop}

theorem units_map_injective : Function.Injective (Units.map i.toMonoidHom) :=
  Units.map_injective i.injective

theorem up (hinj : Function.Injective f)
    (honto : ∀ n, 0 < n → ∀ z : Q', z ^ n = 1 → ∃ y : Q, y ^ n = 1 ∧ f y = z)
    (hact : ∀ c y, f (act c y) = act' c (f y))
    (he : ∀ n y y' c, e' n (f y) (f y') (Units.map i.toMonoidHom c) ↔ e n y y' c)
    (I : TateIso D K Q act e) :
    ∃ I' : TateIso D Ω Q' act' e', ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = f (I.ev n v) := by
  refine ⟨{ ζ := fun n => Units.map i.toMonoidHom (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (units_map_injective i)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n v => f (I.ev n v)
            add := fun n a b => by rw [I.add, map_mul]
            lin := fun n c a => by rw [I.lin, hact]
            ker := fun n hn a => by rw [← I.ker n hn a, map_eq_one_iff f hinj]
            onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
            tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm]
            isom := fun n hn a b => by rw [← map_zpow, he]; exact I.isom n hn a b },
    fun n _ => ⟨rfl, fun _ => rfl⟩⟩
  · obtain ⟨y, hy, rfl⟩ := honto n hn z hz
    obtain ⟨a, rfl⟩ := (I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]

theorem down [IsAlgClosed K] [CharZero K] (hinj : Function.Injective f)
    (honto : ∀ n, 0 < n → ∀ z : Q', z ^ n = 1 → ∃ y : Q, y ^ n = 1 ∧ f y = z)
    (hact : ∀ c y, f (act c y) = act' c (f y)) (hone : ∀ c, act c 1 = 1)
    (he : ∀ n y y' c, e' n (f y) (f y') (Units.map i.toMonoidHom c) ↔ e n y y' c)
    (I' : TateIso D Ω Q' act' e') :
    ∃ I : TateIso D K Q act e, ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = f (I.ev n v) := by
  have h1 : ∀ n, ∃ u : Kˣ, 0 < n → Units.map i.toMonoidHom u = I'.ζ n := fun n => by
    by_cases hn : 0 < n
    · obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one i n hn _ (I'.ζ_prim n hn).pow_eq_one
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hn⟩
  have h2 : ∀ n v, ∃ y : Q, (0 < n → f y = I'.ev n v) ∧ (¬ 0 < n → y = 1) := fun n v => by
    by_cases hn : 0 < n
    · obtain ⟨y, -, hy⟩ := honto n hn _ ((I'.onto n hn _).2 ⟨v, rfl⟩)
      exact ⟨y, fun _ => hy, fun h => absurd hn h⟩
    · exact ⟨1, fun h => absurd h hn, fun _ => rfl⟩
  choose ζ hζ using h1
  choose ev hev hev0 using h2
  refine ⟨{ ζ := ζ
            ζ_prim := fun n hn => ?_
            ζ_pow := fun n m hn hm => units_map_injective i ?_
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => by rw [← I'.ker n hn a, ← hev n a hn, map_eq_one_iff f hinj]
            onto := fun n hn z => ?_
            tower := fun n m hn hm a => hinj ?_
            isom := fun n hn a b => ?_ },
    fun n hn => ⟨by rw [← hζ n hn]; rfl, fun v => (hev n v hn).symm⟩⟩
  · refine IsPrimitiveRoot.of_map_of_injective ?_ (units_map_injective i)
    rw [hζ n hn]; exact I'.ζ_prim n hn
  · rw [map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, I'.ζ_pow n m hn hm]
  · by_cases hn : 0 < n
    · apply hinj
      rw [map_mul, hev _ _ hn, hev _ _ hn, hev _ _ hn, I'.add]
    · rw [hev0 _ _ hn, hev0 _ _ hn, hev0 _ _ hn, _root_.mul_one]
  · by_cases hn : 0 < n
    · apply hinj
      rw [hact, hev _ _ hn, hev _ _ hn, I'.lin]
    · rw [hev0 _ _ hn, hev0 _ _ hn, hone]
  · rw [← map_eq_one_iff f hinj, map_pow, I'.onto n hn]
    refine exists_congr fun a => ?_
    rw [← hev n a hn, hinj.eq_iff]
  · rw [map_pow, hev _ _ (Nat.mul_pos hn hm), hev _ _ hn, I'.tower n m hn hm]
  · rw [← he, map_zpow, hζ n hn, hev _ _ hn, hev _ _ hn]
    exact I'.isom n hn a b

end Abstract

noncomputable def precomp {S : Scheme.{0}} {T T' : Over S} (g : T' ⟶ T) (A : Over S) [GrpObj A] :
    (T ⟶ A) →* (T' ⟶ A) where
  toFun y := g ≫ y
  map_one' := MonObj.comp_one g
  map_mul' a b := MonObj.comp_mul g a b

theorem tateIso_fieldExt : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S), (∀ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ I' : TateIso D Ω (Over.mk (spMap i ≫ x) ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ I.ev n v) ∧ ∀ I' : TateIso D Ω (Over.mk (spMap i ≫ x) ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), (∀ c, IsMonHom (act c)) → ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ I.ev n v := by
  intro hL E _ _ _ H D S P act K Ω _ _ _ _ _ i x
  obtain ⟨hinj, honto⟩ := GlobalTheory.T.torsion_points_descend_field_extension hL S P K Ω i x
  let g : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have honto' : ∀ n, 0 < n → ∀ z : Over.mk (spMap i ≫ x) ⟶ P.A, z ^ n = 1 →
      ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ precomp g P.A y = z :=
    fun n hn z hz => honto n z (Nat.cast_ne_zero.mpr hn.ne') hz
  refine ⟨fun I => up D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm)
      (fun n y y' c => GlobalTheory.T.weilPairing_fieldExtension_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I,
    fun I' hm => down D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm)
      (fun c => ?_) (fun n y y' c => GlobalTheory.T.weilPairing_fieldExtension_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I'⟩
  haveI := hm c
  exact MonObj.one_comp (act c)

end GlobalTheory.TateIsoFieldExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixTorsionOfForallGeometric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem eq_id_of_forall_geometric_fibre (hG : Out.GlobalFnsSt) {S : Scheme.{0}} (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (σ : A ⟶ A) (h0 : η[A] ≫ σ = η[A])
    (hσ : ∀ t : S, ∃ (S' X : Scheme.{0}) (f : S' ⟶ S) (g : X ⟶ A.left) (q : X ⟶ S') (y : S'),
      f y = t ∧ IsPullback g q A.hom f ∧ g ≫ σ.left = g) : σ = 𝟙 A := by
  have := hA.proper
  let u : A ⟶ A := σ * (𝟙 A)⁻¹
  have hu : ∀ {T : Over S} (x : T ⟶ A), x ≫ σ = x → x ≫ u = 1 := fun x hx => by
    simp only [u, MonObj.comp_mul, GrpObj.comp_inv, hx, Category.comp_id, mul_inv_cancel]
  have hη : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  have hfib : ∀ (t : S) (x : A.left), A.hom x = t →
      u.left x = (η[A] : 𝟙_ (Over S) ⟶ A).left t := by
    intro t x hx
    obtain ⟨S', X, f, g, q, y, hy, hg, e⟩ := hσ t
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hg x y (hx.trans hy.symm)
    let x₀ : Over.mk (g ≫ A.hom) ⟶ A := Over.homMk g rfl
    have h₀ : g ≫ u.left = (g ≫ A.hom) ≫ (η[A] : 𝟙_ (Over S) ⟶ A).left :=
      congrArg (fun q => q.left) (hu x₀ (Over.OverMorphism.ext e))
    rw [← Scheme.Hom.comp_apply, h₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
  have key : u.left = A.hom ≫ (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ u.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    obtain ⟨V, hV, e⟩ := local_rigidity _ _ _ A.hom _ u.left hη inferInstance
      (surjective_app_of_isAbelianScheme hG A hA) (A.hom x) _ (hfib _)
    exact ⟨A.hom ⁻¹ᵁ V, hV, e⟩
  have h₁ : u = toUnit A ≫ η[A] ≫ u := Over.OverMorphism.ext key
  rw [hu η[A] h0, MonObj.comp_one] at h₁
  exact mul_inv_eq_one.1 h₁

theorem serre_any_base (hL : Out.Laws) {S : Scheme.{0}} (P : Out.PolAV S) (M : ℕ) (hM : 3 ≤ M)
    (σ : P.A ≅ P.A) (hσ : IsMonHom σ.hom)
    (hloc : ∀ p : S, ∃ V : S.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]).pull
        (P.A.hom ⁻¹ᵁ V).ι), c.IsGen)
    (hfix : ∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) : σ.hom = 𝟙 P.A := by
  refine eq_id_of_forall_geometric_fibre hL.globalFns P.A P.isAb σ.hom (IsMonHom.one_hom σ.hom)
    fun t => ?_
  obtain ⟨V, hV, c, hc⟩ := hloc t
  have hf : ∀ y, S.fromSpecResidueField t y = t := Scheme.fromSpecResidueField_apply t
  obtain ⟨X, g, q, hg, e⟩ := comp_aut_eq_of_serre_baseChange hL.polBaseChange
    (S.fromSpecResidueField t) P M
    (fun P' σ' h' ⟨c', hc'⟩ hx => hL.serre _ P' M hM σ' h' (fun _ => ⟨⊤, trivial,
      gen_chartPull (chartPullPull _ _ _ rfl) c' hc'⟩) hx)
    σ hσ V (fun y => by rw [hf]; exact hV) c hc hfix
  exact ⟨_, X, _, g, q, (default : PrimeSpectrum (S.residueField t)), hf _, hg, e⟩

theorem fix_torsion_of_forall_geometric {S : Scheme.{0}} (A : Over S) [GrpObj A] (n : ℕ)
    [Etale (Out.mulA A n).left] (σ : A ⟶ A) [IsMonHom σ]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A),
      x ^ n = 1 → x ≫ σ = x) (T : Over S) (x : T ⟶ A) (hx : x ^ n = 1) : x ≫ σ = x := by
  have e : ∀ y : T ⟶ A, y ≫ Out.mulA A n = y ^ n := fun y => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  have hx' : (x ≫ σ) ^ n = 1 := by
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  apply Over.OverMorphism.ext
  refine eq_of_range_equalizer_ι_eq_univ (Out.mulA A n).left
    (by rw [← Over.comp_left, ← Over.comp_left, e, e, hx, hx']) (Set.eq_univ_of_forall fun z => ?_)
  let K : Type := AlgebraicClosure (T.left.residueField z)
  let j : Sp K ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField z) K)) ≫
      T.left.fromSpecResidueField z
  have hj : ∀ p, j p = z := fun p =>
    (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply z _)
  let j' : Over.mk (j ≫ T.hom) ⟶ T := Over.homMk j rfl
  have h₁ := h K (j ≫ T.hom) (j' ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  replace h₁ := (Category.assoc _ _ _).symm.trans h₁
  exact range_subset_range_equalizer_ι j (congrArg (fun q => q.left) h₁)
    ⟨(default : PrimeSpectrum K), hj _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem obj_aut_fix_geometric_torsion {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o : Obj D l b s) (θ : o.t.G ≅ o.t.G) [IsMonHom θ.hom]
    (hact : ∀ a, o.t.act.act a ≫ θ.hom = θ.hom ≫ o.t.act.act a)
    (hL : LBIso o.t.PP.L (o.t.PP.L.pull θ.hom.left)) (heta : ∀ a, o.eta a ≫ θ.hom = o.eta a)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ o.t.G)
    (hy : y ^ l.M = 1) : y ≫ θ.hom = y := by
  obtain ⟨w, hw⟩ := hL
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage _).symm
  refine ObjRigid.fix_torsion l I (IsMonHom.monoidHom θ.hom (Over.mk x)) (fun a z => ?_)
    (fun z z' c c' h h' => ?_) (fun a ha => ?_) y hy
  · show (z ≫ _) ≫ θ.hom = (z ≫ θ.hom) ≫ _
    rw [Category.assoc, hact, Category.assoc]
  · have : Subsingleton (Over.mk x).left := inferInstanceAs (Subsingleton (Sp k))
    exact H1.unitOn_injective
      (ObjRigid.weil_eq_of_iso (T := Over.mk x) o.t.PP.isLB θ w hw _ z z' _ _ h h')
  · show _ ≫ θ.hom = _
    rw [← hI a ha, Category.assoc, heta]

theorem obj_rigid_of_pol : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ := by
  intro hL hpol E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f m m' heta
  obtain ⟨hA, hd, hr, hs⟩ := hpol E H D l B' b' S' s' o'
  obtain ⟨θ, hθ, hφ, hact, -, w, hw, -⟩ := sabMap_iso m m' rfl rfl
  have hη : ∀ a, o'.eta a ≫ θ.hom = o'.eta a := fun a => by
    obtain ⟨σ, h₁, h₂⟩ := heta a
    apply Over.OverMorphism.ext
    apply m'.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc]
      exact (congrArg _ hφ).trans (h₁.trans h₂.symm)
    · rw [Over.w, Over.w]
  let P : Out.PolAV S' :=
    { A := o'.t.G, g := _, smoothDim := hd, L := o'.t.PP.L, isLB := o'.t.PP.isLB,
      ample := o'.ample, ktriv := o'.ktriv, isAb := hA, rigid := hr, sym := hs }
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hMu : IsUnit (l.M : Γ(S', ⊤)) := by
    simpa using (b'.unit _ hM).map ((Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ s'.appTop).hom
  have := hA.smooth
  have : Etale (Out.mulA o'.t.G l.M).left := GrpTangent.etale_id_pow o'.t.G hMu
  have h : θ.hom = 𝟙 _ := by
    refine serre_any_base hL P l.M l.three_le θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric o'.t.G l.M θ.hom
        (obj_aut_fix_geometric_torsion o' θ hact ⟨w, hw⟩ hη))
    obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (o'.t.G.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut o'.t.PP.L _ _ _ _ fun n => ?_) t ht
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  rw [← hφ, h, Over.id_left, Category.id_comp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.CubeGen

open GlobalTheory.AbLaw.Cube

theorem surjective_appTop {X : Scheme.{0}} (P : Over X) (e : 𝟙_ (Over X) ⟶ P) (hs : Smooth P.hom)
    (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P) :
    Function.Surjective P.hom.appTop.hom := by
  change ∀ u : Γ(P.left, P.hom ⁻¹ᵁ ⊤), ∃ a, (P.hom.app ⊤).hom a = u
  intro u
  have he : e.left ≫ P.hom = 𝟙 X := Over.w e
  have hle : (⊤ : X.Opens) ≤ e.left ⁻¹ᵁ (P.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial
  have key : ∀ (g : X ⟶ X) (hg : g = 𝟙 X) (h' : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)),
      (g.appLE ⊤ ⊤ h').hom c = c := by
    rintro g rfl h' c
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    change (X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens)))).hom c = c
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hφψ : ∀ c : Γ(X, ⊤), (e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom ((P.hom.app ⊤).hom c) = c := fun c =>
    (congrArg (fun φ => CommRingCat.Hom.hom φ c) (Scheme.Hom.comp_appLE e.left P.hom ⊤ ⊤ hle)).symm.trans
      (key _ he hle c)
  refine ⟨(e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom u, ?_⟩
  have h1 := GlobalTheory.eq_one_of_appLE_section_eq_one X P e.left he hs hg ⟨hr, hab⟩ ⊤
    (1 + u - (P.hom.app ⊤).hom ((e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom u)) hle
    (by rw [map_sub, map_add (f := _), map_one, hφψ]; ring)
  linear_combination -h1

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def cubicalOfNormalised (s₂ : Function.Surjective (A ⊗ A).hom.appTop.hom)
    (s₃ : Function.Surjective (A ⊗ A ⊗ A).hom.appTop.hom) (s₄ : Function.Surjective (A ⊗ A ⊗ A ⊗ A).hom.appTop.hom)
    (M : RigLB A) (t : LB.Gen (Theta A M.L)) (ht : t.IsGen) (hn : IsNormalised t) : CubicalStr A M :=
  { t := t
    isGen := ht
    face := fun i => by
      have key : ∀ a b c : G2 A ⟶ A, lift 1 1 ≫ a = (1 : 𝟙_ (Over S) ⟶ A) → lift 1 1 ≫ b = (1 : 𝟙_ (Over S) ⟶ A) →
          lift 1 1 ≫ c = (1 : 𝟙_ (Over S) ⟶ A) → a = 1 ∨ b = 1 ∨ c = 1 →
          LB.Gen.Corr M.L _ _ (Y := (G2 A).left) _ _
            (LB.pullGen M.L (thφ A (x3 A)) thε t (lift a (lift b c)).left) (LB.oneGen M.L) := by
        intro a b c ha hb hc h
        refine corr_of_val_section M.isLB s₂ (lift 1 1) (fun V _ k => ?_) (DVR.pullGen_isGen _ _ _ _ ht _) oneGen_isGen
          (fun y J hJ => (hn.pull _ ha hb hc hJ).trans (val_one _).symm)
        refine (Fintype.prod_empty _).trans (Eq.trans ?_ (prod_cub a b c k).symm)
        apply Additive.ofMul.injective
        rcases h with rfl | rfl | rfl <;> simp only [_root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;> abel
      fin_cases i
      · exact key 1 (x2 A 0) (x2 A 1) (MonObj.comp_one _) (by simp [x2]) (by simp [x2]) (.inl rfl)
      · exact key (x2 A 0) 1 (x2 A 1) (by simp [x2]) (MonObj.comp_one _) (by simp [x2]) (.inr (.inl rfl))
      · exact key (x2 A 0) (x2 A 1) 1 (by simp [x2]) (by simp [x2]) (MonObj.comp_one _) (.inr (.inr rfl))
    cubeSymmetric_swap_first := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 1) (x3 A 0)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cubeSymmetric_swap_last := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 2) (x3 A 1), mul_right_comm (x3 A 0) (x3 A 2)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cocycle := by
      let e : 𝟙_ (Over S) ⟶ G4 A := lift 1 (lift 1 (lift 1 1))
      have e₀ : e ≫ x4 A 0 = 1 := by simp [e, x4]
      have e₁ : e ≫ x4 A 1 = 1 := by simp [e, x4]
      have e₂ : e ≫ x4 A 2 = 1 := by simp [e, x4]
      have e₃ : e ≫ x4 A 3 = 1 := by simp [e, x4]
      have f₀ : e ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
      have f₁ : e ≫ padd A (x4 A 1) (x4 A 2) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])
      refine corr_of_val_section M.isLB s₄ e (fun V _ k => ?_)
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (fun y J hJ => ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e f₀ e₂ e₃ hJ) (hn.pull e e₀ e₁ e₃ hJ))).trans ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e e₀ f₁ e₃ hJ) (hn.pull e e₁ e₂ e₃ hJ))).symm)
      refine (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0) (x4 A 1 * x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 1) (x4 A 2) (x4 A 3) k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0 * x4 A 1) (x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 0) (x4 A 1) (x4 A 3) k)).symm)
      apply Additive.ofMul.injective
      simp only [_root_.mul_assoc (x4 A 0), ofMul_mul, ofMul_inv]
      abel }

theorem exists_gen_of_lbIso {Z : Scheme.{0}} (L : LB Z) (f : Z ⟶ Z) (h : LBIso L (L.pull f)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![f, 𝟙 Z] ![1, -1]), s.IsGen := by
  obtain ⟨w, hw⟩ := h
  refine gen_chartPull (A := (L.pull f).div L) (h := 𝟙 Z)
    { idx := fun j => (fun _ => j 0, j 1)
      le := fun j y hy => ?_
      g := fun y j j' hj hj' => ?_ } w hw
  · have h0 : f y ∈ L.U (j 0) := Set.mem_iInter.1 hy 0
    have h1 : y ∈ L.U (j 1) := Set.mem_iInter.1 hy 1
    exact ⟨mem_pull.2 h0, h1⟩
  · have a0 : f y ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    have a1 : y ∈ L.U (j 1) := Set.mem_iInter.1 hj 1
    have b0 : f y ∈ L.U (j' 0) := Set.mem_iInter.1 hj' 0
    have b1 : y ∈ L.U (j' 1) := Set.mem_iInter.1 hj' 1
    refine (gm_linComb L _ _ (𝟙 Z) y j j' hj hj').trans ?_
    refine Eq.trans ?_ (gm_div L (L.pull f) (𝟙 Z) y _ _ ⟨⟨mem_pull.2 a0, a1⟩, mem_pull.2 b0, b1⟩).symm
    rw [gm_pull_g L f (𝟙 Z) y _ _ (mem_pull.2 a0) (mem_pull.2 b0)]
    simp [Fin.prod_univ_two]

theorem cubical_and_symmetric : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsSemiAbelian G → (IsReduced X ∧ genericPoints X ⊆ abLocus G) → ((∃ t : (Theta G L.L).Gen, t.IsGen) → Nonempty (CubicalStr G L)) ∧ (LBIso L.L (L.L.pull (GrpObj.inv (X := G)).left) → L.IsSymmetric) := by
  intro X G _ _ L hsa hrg
  obtain ⟨hr, hab⟩ := hrg
  have hsm : Smooth G.hom := hsa.smooth
  have hgc : GeometricallyConnected G.hom := hsa.geomConnected
  have hgi : GeometricallyIntegral G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth X G
  refine ⟨fun ⟨t, ht⟩ => ?_, fun hiso => ?_⟩
  · obtain ⟨t', ht', hn⟩ := exists_normalised L.isLB t ht
    obtain ⟨sm2, gi2, ab2⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G G hsm hsm hgi hgi
    obtain ⟨sm3, gi3, ab3⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G (G ⊗ G) hsm sm2 hgi gi2
    obtain ⟨sm4, gi4, ab4⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G (G ⊗ G ⊗ G) hsm sm3 hgi gi3
    have g2 : genericPoints X ⊆ abLocus (G ⊗ G) := fun x hx => ab2 ⟨hab hx, hab hx⟩
    have g3 : genericPoints X ⊆ abLocus (G ⊗ G ⊗ G) := fun x hx => ab3 ⟨hab hx, g2 hx⟩
    have g4 : genericPoints X ⊆ abLocus (G ⊗ G ⊗ G ⊗ G) := fun x hx => ab4 ⟨hab hx, g3 hx⟩
    exact ⟨cubicalOfNormalised (surjective_appTop (G ⊗ G) (lift 1 1) sm2 gi2 hr g2)
      (surjective_appTop (G ⊗ G ⊗ G) (lift 1 (lift 1 1)) sm3 gi3 hr g3)
      (surjective_appTop (G ⊗ G ⊗ G ⊗ G) (lift 1 (lift 1 (lift 1 1))) sm4 gi4 hr g4) L t' ht' hn⟩
  · exact GlobalTheory.PrimNorm.isSymmetric_of_hasGen L (exists_gen_of_lbIso L.L _ hiso)

end GlobalTheory.CubeGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.cubicalStructure_and_symmetric_of_cube_gen : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsSemiAbelian G → (IsReduced X ∧ genericPoints X ⊆ abLocus G) → ((∃ t : (Theta G L.L).Gen, t.IsGen) → Nonempty (CubicalStr G L)) ∧ (LBIso L.L (L.L.pull (GrpObj.inv (X := G)).left) → L.IsSymmetric) := by
  first | exact @GlobalTheory.CubeGen.cubical_and_symmetric | exact GlobalTheory.CubeGen.cubical_and_symmetric | (intros; apply GlobalTheory.CubeGen.cubical_and_symmetric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfComplementary
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem exists_chart_lbPow (u : HolUnif A L g) (hL : L.IsLB) (n : ℕ) (z : Fin g → ℂ) :
    ∃ k : (lbPow L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k := by
  obtain ⟨i, hi⟩ := SymmetricSemicharacter.exists_chart u SymmetricSemicharacter.valueRules hL z
  refine ⟨fun _ => i, ?_⟩
  rwa [Cartier.lbPow_U]

theorem fr_pow_ne_zero (u : HolUnif A L g) (n : ℕ) {z : Fin g → ℂ} {k : (lbPow L n).ι}
    (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k) : u.fr (k PUnit.unit) z ^ n ≠ 0 :=
  pow_ne_zero n (u.fr_ne _ z (Cartier.lbPow_U L n k ▸ hk))

theorem le_preimage_nonzeroLocus_iff (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {s : (lbPow L n).Sec}
    {θ : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow n s θ) (z : Fin g → ℂ) :
    ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus s ↔ θ z ≠ 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_preimage_iff_mem _ _).1 h)
    have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 ((top_le_preimage_iff_mem _ _).2 hk)
    rw [hs k z (top_le_preimage_of_valAt'_ne_zero _ h1)] at h1
    exact left_ne_zero_of_mul h1
  · intro h
    obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z
    refine top_le_preimage_mono _ (le_iSup (fun k => A.left.basicOpen (s.f k)) k) ?_
    rw [top_le_preimage_basicOpen_iff, hs k z hk]
    exact mul_ne_zero h (fr_pow_ne_zero u n hk)

theorem valAt'_eq_div_of_mul (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {s s' : (lbPow L n).Sec}
    {θ θ' : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow n s θ) (hs' : u.IsFnPow n s' θ') (r : Γ(A.left, Out.nonzeroLocus s))
    (hr : ∀ k, resG _ (inf_le_right : Out.nonzeroLocus s ⊓ (lbPow L n).U k ≤ _) (s'.f k) =
      resG _ inf_le_left r * resG _ inf_le_right (s.f k)) {z : Fin g → ℂ} (hz : θ z ≠ 0) :
    valAt' (u.ex z).left _ r = θ' z / θ z := by
  obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z
  have hW := (top_le_preimage_inf _ _ _).2 ⟨(le_preimage_nonzeroLocus_iff u hL hs z).2 hz, hk⟩
  have h := congrArg (valAt' (u.ex z).left _) (hr k)
  rw [valAt'_mul, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, hs k z hk, hs' k z hk,
    ← _root_.mul_assoc] at h
  rw [mul_right_cancel₀ (fr_pow_ne_zero u n hk) h, mul_div_cancel_right₀ _ hz]

theorem exists_regular_quotients (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {κ : Type*} {s : κ → (lbPow L n).Sec}
    {θ : κ → (Fin g → ℂ) → ℂ} (hs : ∀ j, u.IsFnPow n (s j) (θ j)) (i : κ) {z₀ : Fin g → ℂ} (h0 : θ i z₀ ≠ 0) :
    ∃ (U : A.left.Opens) (ρ : κ → Γ(A.left, U)), ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → θ i z ≠ 0 ∧ ∀ j, valAt' (u.ex z).left U (ρ j) = θ j z / θ i z := by
  obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z₀
  have hle := A.left.basicOpen_le ((s i).f k)
  obtain ⟨v, hv⟩ : IsUnit (resG A.left hle ((s i).f k)) := RingedSpace.isUnit_res_basicOpen _ _
  refine ⟨A.left.basicOpen ((s i).f k), fun j => resG A.left hle ((s j).f k) * (v⁻¹).val, ?_, fun z hz => ?_⟩
  · rw [top_le_preimage_basicOpen_iff, hs i k z₀ hk]
    exact mul_ne_zero h0 (fr_pow_ne_zero u n hk)
  · have hk' := top_le_preimage_mono _ hle hz
    have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 hz
    rw [hs i k z hk'] at h1
    refine ⟨left_ne_zero_of_mul h1, fun j => ?_⟩
    rw [valAt'_mul, valAt'_units_inv _ hz, hv, valAt'_res _ _ _ hz, valAt'_res _ _ _ hz, hs i k z hk', hs j k z hk',
      ← div_eq_mul_inv, mul_div_mul_right _ _ (right_ne_zero_of_mul h1)]

theorem isMonHom_of_lift {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} {g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A' L' g') [Smooth A.hom] (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (f : A ⟶ A')
    (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f) : IsMonHom f := by
  have hr : IsReduced A.left := isReduced_of_smooth_complex _ A.hom inferInstance
  have h0 : u.ex 0 = η[A] := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  have h0' : u'.ex 0 = η[A'] := by
    rw [(u'.ker 0).2 u'.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  refine ⟨?_, ?_⟩
  · rw [← h0, ← hf, map_zero, h0']
  · have hft : LocallyOfFiniteType (A ⊗ A).hom := by
      change LocallyOfFiniteType (pullback.fst A.hom A.hom ≫ A.hom)
      infer_instance
    refine TorusEnd.hom_ext_of_points (existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) A' (A ⊗ A)
      (isReduced_tensorObj_complex A A hr hr inferInstance inferInstance) hft) fun y => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (y ≫ fst A A)
    obtain ⟨w, hw⟩ := u.ex_onto (y ≫ snd A A)
    have hy : y = lift (u.ex z) (u.ex w) := by
      ext1 <;> simp [hz, hw]
    rw [hy, ← Category.assoc, ← Hom.mul_def, ← u.ex_add, ← hf, map_add (f := _), u'.ex_add, Hom.mul_def, ← Category.assoc,
      lift_map, ← hf, ← hf]

theorem exists_isMonHom_of_complementary (hamp : Out.AmpleSt) (P P' : Out.PolAV (Sp ℂ)) {g g' : ℕ}
    (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g') {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ}
    (hsec : ∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ)
    (hfn : ∀ (k : ℕ) s, ∃ θ, u'.IsThetaFn Hm' χ' k θ ∧ u'.IsFnPow k s θ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (d : ℕ)
    (hd : ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧
      ∀ θ, u'.IsThetaFn Hm' χ' 4 θ → u.IsThetaFn Hm χ d (fun z => θ (F z) * G z)) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  have hsm := P.isAb.smooth
  have hr : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom hsm
  let Φ : (𝟙_ (Over (Sp ℂ)) ⟶ P.A) → (𝟙_ (Over (Sp ℂ)) ⟶ P'.A) := fun y => u'.ex (F (Function.surjInv u.ex_onto y))
  have hΦ : ∀ z, Φ (u.ex z) = u'.ex (F z) := fun z => by
    have h1 : Function.surjInv u.ex_onto (u.ex z) - z ∈ u.Λ := by
      rw [← u.ker]
      have := u.ex_add (Function.surjInv u.ex_onto (u.ex z) - z) z
      rw [sub_add_cancel, Function.surjInv_eq u.ex_onto] at this
      exact mul_eq_right.1 this.symm
    have := SectionTheta.ex_add_lattice u' (F z) ⟨_, hF _ h1⟩
    rwa [← map_add, add_sub_cancel] at this
  obtain ⟨m, s, hcov, hD⟩ := veryAmple_lbPow hamp ℂ P' 4 le_rfl
  choose θ hθ hθs using fun j => hfn 4 (s j)
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) P'.A P.A hr inferInstance Φ fun y => by
    obtain ⟨z₀, rfl⟩ := u.ex_onto y
    obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u'.ex (F z₀)).left _ hcov
    obtain ⟨haff, r, hr, hgen⟩ := hD i
    have hmem := le_preimage_nonzeroLocus_iff u' P'.isLB (hθs i)
    obtain ⟨G, hG0, hG⟩ := hd z₀
    choose t ht using fun j => hsec d _ (hG _ (hθ j))
    obtain ⟨U, ρ, hU0, hU⟩ := exists_regular_quotients u P.isLB ht i (mul_ne_zero ((hmem _).1 hi) hG0)
    refine ⟨U, _, hU0, haff, fun y' hy' => ?_, fun ψ => ?_⟩
    · obtain ⟨z, rfl⟩ := u.ex_onto y'
      rw [hΦ]
      exact (hmem _).2 (left_ne_zero_of_mul (hU z hy').1)
    · obtain ⟨Q, rfl⟩ := hgen ψ
      refine ⟨MvPolynomial.eval₂ (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ Q, fun y' hy' => ?_⟩
      obtain ⟨z, rfl⟩ := u.ex_onto y'
      have h1 := left_ne_zero_of_mul (hU z hy').1
      have h2 := right_ne_zero_of_mul (hU z hy').1
      rw [hΦ, TorusEnd.valAt'_eval₂ _ _ hy', TorusEnd.valAt'_eval₂ _ _ ((hmem _).2 h1)]
      congr 2
      funext j
      rw [(hU z hy').2 j, valAt'_eq_div_of_mul u' P'.isLB (hθs i) (hθs j) (r j) (hr j) h1, mul_div_mul_right _ _ h2]
  have hfe : ∀ z, u'.ex (F z) = u.ex z ≫ f := fun z => by rw [hf, hΦ]
  exact ⟨f, isMonHom_of_lift u u' F f hfe, hfe⟩

end GlobalTheory.LatticeHom
end
end
