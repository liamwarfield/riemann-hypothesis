module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionsOrderFiniteUnramifiedScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelDescendsFiniteTypeSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesNoetherianLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelClassifiedAtPrimeSpreadsBasicOpen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem comp_eq_of_pair : ∀ (h n : ℕ) (B B' B₁ B₂ : Type) [CommRing B] [CommRing B'] [CommRing B₁] [CommRing B₂] (b : TBase B n) (ζ' : B') (ζ₁ : B₁) (ζ₂ : B₂) (T T₁ T₂ : Scheme.{0}) (sc : T ⟶ Sp B') (su : T ⟶ Sp B) (s₁ : T₁ ⟶ Sp B₁) (s₂ : T₂ ⟶ Sp B₂) (c : SiegPre h n ζ' sc) (u : SiegPre h n (b.ζ : B) su) (c₁ : SiegPre h n ζ₁ s₁) (c₂ : SiegPre h n ζ₂ s₂) (p₁ : T₁ ⟶ T) (p₂ : T₂ ⟶ T) (φ₁ : c₁.A.left ⟶ c.A.left) (ψ₁ : c₁.A.left ⟶ u.A.left) (φ₂ : c₂.A.left ⟶ c.A.left) (ψ₂ : c₂.A.left ⟶ u.A.left), 3 ≤ n → Odd n → u.Principal → SRelBy c₁ c 1 1 p₁ φ₁ → SRelBy c₁ u 1 1 p₁ ψ₁ → SRelBy c₂ c 1 1 p₂ φ₂ → SRelBy c₂ u 1 1 p₂ ψ₂ → ∀ (Z : Scheme.{0}) (g₁ : Z ⟶ c₁.A.left) (g₂ : Z ⟶ c₂.A.left), g₁ ≫ φ₁ = g₂ ≫ φ₂ → g₁ ≫ ψ₁ = g₂ ≫ ψ₂ := by
  intro h n B B' B₁ B₂ _ _ _ _ b ζ' ζ₁ ζ₂ T T₁ T₂ sc su s₁ s₂ c u c₁ c₂ p₁ p₂ φ₁ ψ₁ φ₂ ψ₂ hn ho hu m₁ k₁ m₂ k₂ Z g₁ g₂ e
  obtain ⟨-, hφ₁, -⟩ := (sRelBy_one_iff _ _ _ _).1 m₁
  obtain ⟨-, hφ₂, -⟩ := (sRelBy_one_iff _ _ _ _).1 m₂
  have hz : (g₁ ≫ c₁.A.hom) ≫ p₁ = (g₂ ≫ c₂.A.hom) ≫ p₂ := by
    rw [Category.assoc, Category.assoc, ← hφ₁.1.w, ← hφ₂.1.w, reassoc_of% e]
  obtain ⟨⟨o, ho'⟩, -⟩ := GlobalTheory.siegPre_pullback h n B₁ ζ₁ T₁ Z s₁ ((g₁ ≫ c₁.A.hom) ≫ s₁) (g₁ ≫ c₁.A.hom) c₁ rfl
  obtain ⟨κ, hκ⟩ := exists_of_siegPB ho'
  have a₁ := comp_by m₁ hκ
  rw [hz] at a₁
  obtain ⟨κ', hκ', hκ'b⟩ := cancel_by m₂ a₁
  have n₁ := comp_by k₁ hκ
  have n₂ := comp_by k₂ hκ'b
  rw [← hz] at n₂
  have r := GlobalTheory.SiegRigid.eq_of_sRelBy h n n 1 B B₁ b ζ₁ T Z su _ u o _ _ _ hn ho hu n₁ n₂
  obtain ⟨-, hκg, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ
  obtain ⟨-, hκ'g, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ'b
  have hl : g₁ ≫ c₁.A.hom = 𝟙 Z ≫ g₁ ≫ c₁.A.hom := (Category.id_comp _).symm
  have h₁ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ = g₁ := hκg.1.lift_fst _ _ _
  have h₀ : hκg.1.lift g₁ (𝟙 Z) hl ≫ o.A.hom = 𝟙 Z := hκg.1.lift_snd _ _ _
  have h₂ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' = g₂ := by
    apply hφ₂.1.hom_ext
    · rw [Category.assoc, hκ', ← Category.assoc, h₁, e]
    · rw [Category.assoc, hκ'g.1.w, ← Category.assoc, h₀, Category.id_comp]
  calc g₁ ≫ ψ₁ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ ≫ ψ₁ := by rw [← Category.assoc, h₁]
    _ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' ≫ ψ₂ := by rw [r]
    _ = g₂ ≫ ψ₂ := by rw [← Category.assoc, h₂]

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem isPullback_of_sRelBy {h n : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c' : SiegPre h n ζ' s'} {c : SiegPre h n ζ s} {f : S' ⟶ S}
    {φ : c'.A.left ⟶ c.A.left} (m : SRelBy c' c 1 1 f φ) : IsPullback φ c'.A.hom c.A.hom f :=
  ((sRelBy_one_iff _ _ _ _).1 m).choose_spec.1.1

theorem iso_of_local : ∀ (g n : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S : Scheme.{0}) (sc : S ⟶ Sp B') (su : S ⟶ Sp B) (c : SiegPre g n ζ' sc) (u : SiegPre g n (b.ζ : B) su), 3 ≤ n → Odd n → u.Principal → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ SiegPB cV u j) → ∃ φ : c.A.left ⟶ u.A.left, IsIso φ ∧ φ ≫ u.A.hom = c.A.hom ∧ ∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)) (φV : cV.A.left ⟶ c.A.left), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SRelBy cV c 1 1 j φV ∧ SRelBy cV u 1 1 j (φV ≫ φ) := by
  intro g n B B' _ _ b ζ' S sc su c u hn ho hu hloc
  choose V j cV hj hx m k using hloc
  choose φV hm using fun x => exists_of_siegPB (m x)
  choose ψV hk using fun x => exists_of_siegPB (k x)
  have pφ : ∀ x, IsPullback (φV x) (cV x).A.hom c.A.hom (j x) := fun x => isPullback_of_sRelBy (hm x)
  have pψ : ∀ x, IsPullback (ψV x) (cV x).A.hom u.A.hom (j x) := fun x => isPullback_of_sRelBy (hk x)
  have oφ : ∀ x, IsOpenImmersion (φV x) := fun x => MorphismProperty.of_isPullback (pφ x).flip (hj x)
  have oψ : ∀ x, IsOpenImmersion (ψV x) := fun x => MorphismProperty.of_isPullback (pψ x).flip (hj x)
  let 𝒰 : c.A.left.OpenCover := Scheme.Cover.mkOfCovers S (fun x => (cV x).A.left) φV
    (fun a => ⟨c.A.hom a, (GlobalTheory.GrpLoc.range_of_isPullback (pφ (c.A.hom a)) a).2 (hx _)⟩) oφ
  let 𝒰' : u.A.left.OpenCover := Scheme.Cover.mkOfCovers S (fun x => (cV x).A.left) ψV
    (fun a => ⟨u.A.hom a, (GlobalTheory.GrpLoc.range_of_isPullback (pψ (u.A.hom a)) a).2 (hx _)⟩) oψ
  have pair := fun x y => comp_eq_of_pair g n B B' B' B' b ζ' ζ' ζ' S (V x) (V y) sc su (j x ≫ sc) (j y ≫ sc) c u
    (cV x) (cV y) (j x) (j y) (φV x) (ψV x) (φV y) (ψV y) hn ho hu (hm x) (hk x) (hm y) (hk y)
  have compat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ ψV x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ ψV y :=
    fun x y => pair x y _ _ _ pullback.condition
  let φ := 𝒰.glueMorphisms ψV compat
  have hφ : ∀ x, φV x ≫ φ = ψV x := fun x => 𝒰.ι_glueMorphisms ψV compat x
  have hw : φ ≫ u.A.hom = c.A.hom := by
    refine 𝒰.hom_ext _ _ fun x => ?_
    show φV x ≫ φ ≫ u.A.hom = φV x ≫ c.A.hom
    rw [reassoc_of% (hφ x), (pψ x).w, (pφ x).w]
  have key : ∀ x y (Z : Scheme.{0}) (g₁ : Z ⟶ (cV x).A.left) (g₂ : Z ⟶ (cV y).A.left),
      g₁ ≫ ψV x = g₂ ≫ ψV y → g₁ ≫ φV x = g₂ ≫ φV y := by
    intro x y Z g₁ g₂ e
    have e₁ : (g₁ ≫ φV x) ≫ c.A.hom = (g₂ ≫ (cV y).A.hom) ≫ j y := by
      calc (g₁ ≫ φV x) ≫ c.A.hom = g₁ ≫ φV x ≫ φ ≫ u.A.hom := by rw [hw, Category.assoc]
        _ = g₁ ≫ ψV x ≫ u.A.hom := by rw [reassoc_of% (hφ x)]
        _ = g₂ ≫ ψV y ≫ u.A.hom := by rw [reassoc_of% e]
        _ = _ := by rw [(pψ y).w, Category.assoc]
    let t := (pφ y).lift (g₁ ≫ φV x) (g₂ ≫ (cV y).A.hom) e₁
    have t₁ : t ≫ φV y = g₁ ≫ φV x := (pφ y).lift_fst _ _ _
    have t₂ : t ≫ (cV y).A.hom = g₂ ≫ (cV y).A.hom := (pφ y).lift_snd _ _ _
    have t₃ : t ≫ ψV y = g₁ ≫ ψV x := pair y x _ t g₁ t₁
    have tg : t = g₂ := (pψ y).hom_ext (t₃.trans e) t₂
    rw [← t₁, tg]
  have compat' : ∀ x y, pullback.fst (𝒰'.f x) (𝒰'.f y) ≫ φV x = pullback.snd (𝒰'.f x) (𝒰'.f y) ≫ φV y :=
    fun x y => key x y _ _ _ pullback.condition
  let ψ := 𝒰'.glueMorphisms φV compat'
  have hψ : ∀ x, ψV x ≫ ψ = φV x := fun x => 𝒰'.ι_glueMorphisms φV compat' x
  have i₁ : φ ≫ ψ = 𝟙 _ := 𝒰.hom_ext _ _ fun x => by
    show φV x ≫ φ ≫ ψ = φV x ≫ 𝟙 _
    rw [reassoc_of% (hφ x), hψ x, Category.comp_id]
  have i₂ : ψ ≫ φ = 𝟙 _ := 𝒰'.hom_ext _ _ fun x => by
    show ψV x ≫ ψ ≫ φ = ψV x ≫ 𝟙 _
    rw [reassoc_of% (hψ x), hφ x, Category.comp_id]
  exact ⟨φ, ⟨ψ, i₁, i₂⟩, hw, fun x => ⟨V x, j x, cV x, φV x, hj x, hx x, hm x, by rw [hφ x]; exact hk x⟩⟩

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem siegPB_id_of_local : ∀ (g n : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S : Scheme.{0}) (sc : S ⟶ Sp B') (su : S ⟶ Sp B) (c : SiegPre g n ζ' sc) (u : SiegPre g n ζ su) (φ : c.A.left ⟶ u.A.left), IsIso φ → φ ≫ u.A.hom = c.A.hom → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)) (φV : cV.A.left ⟶ c.A.left), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SRelBy cV c 1 1 j φV ∧ SRelBy cV u 1 1 j (φV ≫ φ)) → SiegPB c u (𝟙 S) := by
  intro g n B B' _ _ ζ ζ' S sc su c u φ hi hw hloc
  have gp : IsGrpPullback c.A u.A (𝟙 S) φ := GlobalTheory.GrpLoc.isGrpPullback_local_on_base S c.A u.A φ hi hw fun p => by
    obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
    exact ⟨V, j, cV.A, inferInstance, φV, hj, hx, ((sRelBy_one_iff _ _ _ _).1 m).choose_spec.1,
      ((sRelBy_one_iff _ _ _ _).1 k).choose_spec.1⟩
  obtain ⟨φ₂, sq⟩ := GlobalTheory.SiegDesc.exists_isSquare gp.1.w
  have lev : ∀ a, (c.lev a).left ≫ φ = 𝟙 S ≫ (u.lev a).left := fun a => by
    refine GlobalTheory.GrpLoc.hom_ext_loc fun p => ?_
    obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
    obtain ⟨-, -, -, -, lm⟩ := (sRelBy_one_iff _ _ _ _).1 m
    obtain ⟨-, -, -, -, lk⟩ := (sRelBy_one_iff _ _ _ _).1 k
    refine ⟨V, j, hj, hx, ?_⟩
    rw [Category.id_comp, ← reassoc_of% (lm a), ← lk a]
  have gp₂ : IsGrpPullback (G2 c.A) (G2 u.A) (𝟙 S) φ₂ := GlobalTheory.ShearLift.isGrpPullback_tensor gp gp sq.1 sq.2
  have rig (d : SiegPre g n ζ' sc) : Out.Rigidified (G2 d.A) d.P := by
    have he : eSec d.A ≫ (lift (1 : d.A ⟶ d.A) (𝟙 d.A)).left = eSec (G2 d.A) := by
      unfold eSec
      rw [← Over.comp_left]
      congr 1
      ext <;> simp [Hom.one_def]
    have z := (CechPic.cls_eq_zero_iff (pull_isLB d.isLB _)).2 d.rig₁
    rw [CechPic.cls_pull d.isLB] at z
    apply (CechPic.cls_eq_zero_iff (pull_isLB d.isLB _)).1
    rw [CechPic.cls_pull d.isLB, ← he, CechPic.pull_comp, z, map_zero]
  have rL : Out.Rigidified (G2 c.A) c.P := rig c
  have rL' : Out.Rigidified (G2 u.A) u.P := by
    have he : eSec u.A ≫ (lift (1 : u.A ⟶ u.A) (𝟙 u.A)).left = eSec (G2 u.A) := by
      unfold eSec
      rw [← Over.comp_left]
      congr 1
      ext <;> simp [Hom.one_def]
    have z := (CechPic.cls_eq_zero_iff (pull_isLB u.isLB _)).2 u.rig₁
    rw [CechPic.cls_pull u.isLB] at z
    apply (CechPic.cls_eq_zero_iff (pull_isLB u.isLB _)).1
    rw [CechPic.cls_pull u.isLB, ← he, CechPic.pull_comp, z, map_zero]
  have hiso : LBIso c.P (u.P.pull φ₂) :=
    GlobalTheory.RigidLocal.lbIso_of_local GlobalTheory.abelianSchemeLaws_all.1.globalFns S (G2 c.A) (G2 u.A) c.P u.P φ₂
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ c.ab c.ab) c.isLB u.isLB rL rL' gp₂ fun p => by
        obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
        obtain ⟨φV₂, gm, sm, im, -⟩ := (sRelBy_one_iff _ _ _ _).1 m
        obtain ⟨ψV₂, -, sk, ik, -⟩ := (sRelBy_one_iff _ _ _ _).1 k
        have e₂ : φV₂ ≫ φ₂ = ψV₂ := GlobalTheory.SiegDesc.isSquare_comp rfl sm sq sk
        refine ⟨V, (G2 cV.A).left, j, (G2 cV.A).hom, φV₂, hj, hx, GlobalTheory.SiegDesc.isPullback_of_isSquare gm.1 sm, ?_⟩
        rw [e₂]
        exact im.symm.trans (pull_isLB c.isLB _) cV.isLB (pull_isLB u.isLB _) ik
  exact ⟨φ, φ₂, gp, sq, hiso, lev⟩

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegelPullComp

theorem glue_classifying : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ ∃ f : V ⟶ F.X, f ≫ F.s = j ≫ s' ∧ SiegPB cV F.univ f) → ∃ f : S ⟶ F.X, f ≫ F.s = s' ∧ ∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ SiegPB cV F.univ (j ≫ f) := by
  intro g n hg hn ho F S s' c hloc
  choose V j cV hj hx m f hfs hpb using hloc
  let 𝒰 : S.OpenCover := Scheme.Cover.mkOfCovers S V j (fun x => ⟨x, hx x⟩) hj
  have key : ∀ x y, pullback.fst (j x) (j y) ≫ f x = pullback.snd (j x) (j y) ≫ f y := by
    intro x y
    obtain ⟨⟨cP, hcP⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) S (pullback (j x) (j y)) s'
      (pullback.fst (j x) (j y) ≫ j x ≫ s') (pullback.fst (j x) (j y) ≫ j x) c (Category.assoc _ _ _)
    have hcP' : SiegPB cP c (pullback.snd (j x) (j y) ≫ j y) := by rw [← pullback.condition]; exact hcP
    have h₁ := pb_comp (hpb x) (pb_cancel (m x) hcP)
    have h₂ := pb_comp (hpb y) (pb_cancel (m y) hcP')
    refine GlobalTheory.SiegUniq.eq_of_siegPB g n hg hn ho F _ _ cP _ _ ?_ ?_ h₁ h₂
    · rw [Category.assoc, hfs x]
    · rw [Category.assoc, hfs y, pullback.condition_assoc]
  let φ := 𝒰.glueMorphisms f key
  have hφ : ∀ x, j x ≫ φ = f x := fun x => 𝒰.ι_glueMorphisms f key x
  refine ⟨φ, 𝒰.hom_ext _ _ fun x => ?_, fun x => ⟨V x, j x, cV x, hj x, hx x, m x, by rw [hφ x]; exact hpb x⟩⟩
  show j x ≫ φ ≫ F.s = j x ≫ s'
  rw [reassoc_of% (hφ x), hfs x]

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegelPullComp

theorem classified_of_local : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ ∃ f : V ⟶ F.X, f ≫ F.s = j ≫ s' ∧ SiegPB cV F.univ f) → ∃ f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  intro g n hg hn ho F S s' c _ hloc
  obtain ⟨f, hf, hl⟩ := glue_classifying g n hg hn ho F S s' c hloc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨⟨u, hu⟩, hpr⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X S F.s (f ≫ F.s) f F.univ rfl
  have hup : u.Principal := hpr u hu F.princ
  obtain ⟨φ, hi, hw, hφ⟩ := iso_of_local g n (cycAway n) (cycAway n) (cycBase hn0) (zetaAway n) S s' (f ≫ F.s) c u
    hn ho hup fun x => by
      obtain ⟨V, j, cV, hj, hx, h₁, h₂⟩ := hl x
      exact ⟨V, j, cV, hj, hx, h₁, pb_cancel hu h₂⟩
  have e := pb_comp hu (siegPB_id_of_local g n (cycAway n) (cycAway n) _ (zetaAway n) S s' (f ≫ F.s) c u φ hi hw hφ)
  rw [Category.id_comp] at e
  exact ⟨f, hf, e⟩

end GlobalTheory.SiegZar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_classified_of_local : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ ∃ f : V ⟶ F.X, f ≫ F.s = j ≫ s' ∧ SiegPB cV F.univ f) → ∃ f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegZar.classified_of_local | exact GlobalTheory.SiegZar.classified_of_local | (intros; apply GlobalTheory.SiegZar.classified_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyExistsUniqueClassifyScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesNoetherian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelNoeth

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id_eq (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap]
  exact Spec.map_id _

theorem classify_noetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ β c hc
  refine GlobalTheory.T.siegelFamily_classified_of_local g n hg hn hodd F (Sp R) (spMap β) c hc ?_
  intro x
  let 𝔭 : Ideal R := x.asIdeal
  haveI : 𝔭.IsPrime := x.isPrime
  have loc : ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)),
      SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) →
      ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧
        SiegPB c' F.univ f := by
    intro c' hc'
    have hP := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) (Sp R) (Sp (Localization.AtPrime 𝔭)) (spMap β)
      (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)) (spMap (algebraMap R (Localization.AtPrime 𝔭))) rfl
      (by rw [spMap_id_eq, Category.comp_id]; exact (spMap_comp_eq _ _).symm)).2.1 c c' hc' hc
    exact GlobalTheory.T.siegelFamily_classifies_noetherian_local g n hg hn hodd F (Localization.AtPrime 𝔭) ((algebraMap R (Localization.AtPrime 𝔭)).comp β) c' hP
  obtain ⟨r, hr, H⟩ := GlobalTheory.T.siegelClassified_at_prime_spreads_basicOpen g n hg hn hodd F R β c 𝔭 hc loc
  let j : Sp (Localization.Away r) ⟶ Sp R := spMap (algebraMap R (Localization.Away r))
  have e : spMap ((algebraMap R (Localization.Away r)).comp β) = j ≫ spMap β := spMap_comp_eq _ _
  rw [e] at H
  obtain ⟨cV, hcV⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) (Sp R) (Sp (Localization.Away r)) (spMap β) (j ≫ spMap β) j rfl
      (by rw [spMap_id_eq, Category.comp_id])).1 c
  obtain ⟨f, hf, hfu⟩ := H cV hcV
  refine ⟨Sp (Localization.Away r), j, cV, IsOpenImmersion.of_isLocalization r, ?_, hcV, f, hf, hfu⟩
  have hu : Set.range j = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
  rw [hu]
  exact hr

end GlobalTheory.SiegelNoeth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_classifies_noetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegelNoeth.classify_noetherian | exact GlobalTheory.SiegelNoeth.classify_noetherian | (intros; apply GlobalTheory.SiegelNoeth.classify_noetherian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyExistsUniqueClassifyScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFamAll

theorem exists_classify_affine {g n : ℕ} (hg : 1 ≤ g) (hn : 3 ≤ n) (hodd : Odd n) (F : SFam g n (zetaAway n))
    (R : Type) [CommRing R] (t : Sp R ⟶ Sp (cycAway n)) (d : SiegPre g n (zetaAway n) t) (hd : d.Principal) :
    ∃ f : Sp R ⟶ F.X, f ≫ F.s = t ∧ SiegPB d F.univ f := by
  obtain ⟨β, rfl⟩ := GlobalTheory.SiegelRingChange.exists_spMap t
  obtain ⟨R₀, β₀, c₀, hft, hβ, hp₀, hpb⟩ := GlobalTheory.T.principalSiegel_descends_finiteType_subring g n hn hodd R β d hd
  haveI : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  obtain ⟨f₀, hf₀, hpb₀⟩ := GlobalTheory.T.siegelFamily_classifies_noetherian g n hg hn hodd F R₀ β₀ c₀ hp₀
  refine ⟨spMap R₀.subtype ≫ f₀, ?_, GlobalTheory.TChart.AbLevel.siegPB_trans hpb hpb₀⟩
  rw [Category.assoc, hf₀, ← GlobalTheory.SiegelRingChange.spMap_comp', hβ]

theorem existsUnique_classify : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal →
      ∃! f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F S s' c hc
  obtain ⟨f, hf, hpf⟩ := GlobalTheory.T.siegelFamily_classified_of_local g n hg hn hodd F S s' c hc (fun x => by
    let 𝒰 := S.affineOpenCover
    let j : Sp (𝒰.X (𝒰.idx x)) ⟶ S := 𝒰.f (𝒰.idx x)
    have hid : j ≫ s' = (j ≫ s') ≫ spMap (RingHom.id (cycAway n)) := by simp [spMap]
    have key := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) S (Sp (𝒰.X (𝒰.idx x))) s' (j ≫ s') j rfl hid
    obtain ⟨cV, hcV⟩ := key.1 c
    have hpV : cV.Principal := key.2.1 c cV hcV hc
    obtain ⟨fV, hfV, hpbV⟩ := exists_classify_affine hg hn hodd F (𝒰.X (𝒰.idx x)) (j ≫ s') cV hpV
    exact ⟨Sp (𝒰.X (𝒰.idx x)), j, cV, inferInstance, 𝒰.covers x, hcV, fV, hfV, hpbV⟩)
  exact ⟨f, ⟨hf, hpf⟩, fun f' hf' => GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn hodd F S s' c f' f hf'.1 hf hf'.2 hpf⟩

end GlobalTheory.SiegFamAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyExistsUniqueClassifySchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_existsUnique_classify_scheme : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal → ∃! f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegFamAll.existsUnique_classify | exact GlobalTheory.SiegFamAll.existsUnique_classify | (intros; apply GlobalTheory.SiegFamAll.existsUnique_classify <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepPrincipalSiegelAdjointOrderAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActSieg

section Pull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
  {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem one_left (h : IsGrpPullback A' A f φ) : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e : (1 : A' ⟶ A').left ≫ φ = (1 : Over.mk (A'.hom ≫ f) ⟶ A).left :=
    congrArg (fun q => q.left) (map_one (pushHom h A'))
  rw [e, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ← Category.assoc, h.1.w]
  rfl

theorem lift_one_id (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (1 : A' ⟶ A') (𝟙 A')
    (Z := A) φ (1 : A ⟶ A) (𝟙 A) (by exact (Category.id_comp _).trans (one_left h)) (by simp)
  exact (Category.id_comp _).symm.trans this

theorem lift_id_one (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (1 : A' ⟶ A')
    (Z := A) φ (𝟙 A) (1 : A ⟶ A) (by simp) (by exact (Category.id_comp _).trans (one_left h))
  exact (Category.id_comp _).symm.trans this

theorem lift_swap (sq : IsSquare φ φ₂) :
    (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    (Z := A ⊗ A) φ₂ (snd A A) (fst A A) (by exact (Category.id_comp _).trans sq.2.symm)
    (by exact (Category.id_comp _).trans sq.1.symm)
  exact (Category.id_comp _).symm.trans this

end Pull

section Obj

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}

def onPull (c : SiegPre h M ζ s) (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ c.A.left)
    (φ₂ : (A' ⊗ A').left ⟶ (c.A ⊗ c.A).left) (pb : IsGrpPullback A' c.A f φ) (sq : IsSquare φ φ₂) :
    SiegPre h M ζ (f ≫ s) :=
  haveI : IsCommMonObj A' := (GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab pb).comm
  { A := A'
    ab := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab pb
    P := c.P.pull φ₂
    isLB := pull_isLB c.isLB φ₂
    rig₁ := by
      obtain ⟨t, ht⟩ := c.rig₁
      exact gen_chartPull (chartPullLinComb c.P φ₂ _ _ _ φ fun _ => lift_one_id pb sq) t ht
    rig₂ := by
      obtain ⟨t, ht⟩ := c.rig₂
      exact gen_chartPull (chartPullLinComb c.P φ₂ _ _ _ φ fun _ => lift_id_one pb sq) t ht
    symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl) (chartPullLinComb c.P _ _ _ _ φ₂ fun _ => lift_swap sq) c.symm
    lev := fun a => GlobalTheory.SiegelPull.secPull pb (c.lev a)
    lev_add := fun a b => GlobalTheory.SiegelPull.push_injective pb _ (by
      rw [map_mul, GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', c.lev_add, MonObj.comp_mul])
    lev_tors := fun a => GlobalTheory.SiegelPull.push_injective pb _ (by
      rw [map_pow, map_one, GlobalTheory.SiegelPull.push_secPull', ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one])
    geom := fun k _ _ x β z hx hz => by
      obtain ⟨g₁, g₂, g₃⟩ := c.geom k (x ≫ f) β z (by rw [Category.assoc]; exact hx) hz
      refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
      · rw [← (GlobalTheory.SiegelPull.push_injective pb (Over.mk x)).eq_iff, GlobalTheory.SiegelPull.push_secPull, map_one]
        rfl
      · obtain ⟨a, ha⟩ := g₂ (pushHom pb (Over.mk x) g) (by
          have := congrArg (pushHom pb (Over.mk x)) hg
          rw [map_pow, map_one] at this
          exact this)
        exact ⟨a, GlobalTheory.SiegelPull.push_injective pb _ ((GlobalTheory.SiegelPull.push_secPull pb _ _).trans ha)⟩
      · exact (weilIs_grpPullback_of_comm S S' c.A A' f φ _ _ (pull_isLB c.isLB _)
          (pull_isLB (pull_isLB c.isLB φ₂) _) pb
          (GlobalTheory.SiegelPull.diag_iso sq (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ (pull_isLB c.isLB φ₂))) (Over.mk x) M _ _ _ _ _
          (congrArg (fun q => q.left) (GlobalTheory.SiegelPull.push_secPull pb (c.lev a) (Over.mk x)).symm)
          (congrArg (fun q => q.left) (GlobalTheory.SiegelPull.push_secPull pb (c.lev b) (Over.mk x)).symm)).2 (g₃ a b) }

theorem onPull_lev (c : SiegPre h M ζ s) (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ c.A.left)
    (φ₂ : (A' ⊗ A').left ⟶ (c.A ⊗ c.A).left) (pb : IsGrpPullback A' c.A f φ) (sq : IsSquare φ φ₂)
    (a : Fin h ⊕ Fin h → ℤ) : ((onPull c A' φ φ₂ pb sq).lev a).left ≫ φ = f ≫ (c.lev a).left :=
  GlobalTheory.SiegelPull.secPull_left pb _

theorem onPull_siegPB (c : SiegPre h M ζ s) (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ c.A.left)
    (φ₂ : (A' ⊗ A').left ⟶ (c.A ⊗ c.A).left) (pb : IsGrpPullback A' c.A f φ) (sq : IsSquare φ φ₂) :
    SiegPB (onPull c A' φ φ₂ pb sq) c f :=
  ⟨φ, φ₂, pb, sq, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ (pull_isLB c.isLB φ₂), onPull_lev c A' φ φ₂ pb sq⟩

end Obj

theorem adj_of_lbIso {S : Scheme.{0}} {A : Over S} [GrpObj A] {O : Type} [Ring O] {P Q : LB (A ⊗ A).left}
    (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) {bar : O → O} {act : O → (A ⟶ A)} (h : Adj A P bar act) :
    Adj A Q bar act := by
  intro a
  have ha := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 (h a)
  have he := (GlobalTheory.CechPic.cls_eq_iff hP hQ).2 e
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hQ _) (pull_isLB hQ _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hQ, ← he]
  exact ha

theorem exists_rep : ∀ (h' M : ℕ), 1 ≤ h' → 3 ≤ M → Odd M → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range eO) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d₀ → ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) → ∃ (H : Scheme.{0}) (sH : H ⟶ Sp (cycAway M)) (zH : SiegPre h' M (zetaAway M) sH) (actH : O → (zH.A ⟶ zH.A)), zH.Principal ∧ IsRAct zH.A actH ∧ Adj zH.A zH.P bar actH ∧ IsQProjOver sH ∧ IsLocallyNoetherian H ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃! g : S ⟶ H, g ≫ sH = t ∧ ActPB z act zH actH g := by
  intro h' M hh hM hodd O _ bar r eO W d₀ hbar hspan hW hd hsum
  have hM0 : M ≠ 0 := by omega
  obtain ⟨F⟩ := exists_sFam_cycAway h' M hh hM hodd
  haveI : IsDedekindDomain (cycAway M) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway M
  haveI : IsLocallyNoetherian F.X := GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth (cycAway M) F.X F.s F.qproj
  obtain ⟨R, hRf, -⟩ := GlobalTheory.T.adjointActions_order_finite_unramified_scheme F.X F.univ.A F.univ.P F.univ.ab F.univ.isLB F.univ.rig₁ F.univ.rig₂
    F.univ.symm F.princ.1 O bar r eO W d₀ hbar hspan hW hd hsum
  have hq : IsQProjOver (R.π ≫ F.s) :=
    GlobalTheory.isQProjOver_comp_of_isFinite_noetherian (cycAway M) R.H F.X R.π F.s hRf F.qproj
  have hzH : SiegPB (onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq) F.univ R.π := onPull_siegPB F.univ R.AH R.φ R.φ₂ R.pb R.sq
  refine ⟨R.H, R.π ≫ F.s, onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq, R.act,
    (GlobalTheory.siegPre_pullback h' M (cycAway M) (zetaAway M) F.X R.H F.s (R.π ≫ F.s) R.π F.univ rfl).2 _ hzH F.princ,
    R.isAct, R.adj, hq, GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth (cycAway M) R.H _ hq, ?_⟩
  intro S t z act hz hact hadj
  obtain ⟨f, ⟨hfs, ⟨φz, φ₂z, pbz, sqz, isoz, levz⟩⟩, hfu⟩ := GlobalTheory.T.siegelFamily_existsUnique_classify_scheme h' M hh hM hodd F S t z hz
  have hadj' : Adj z.A (F.univ.P.pull φ₂z) bar act := adj_of_lbIso z.isLB (pull_isLB F.univ.isLB _) isoz hadj
  obtain ⟨g, ⟨hgπ, ψ, hψ, hψφ, hψa⟩, hgu⟩ := R.rep S f z.A φz φ₂z act pbz sqz hact hadj'
  have sqψ := GlobalTheory.LamPull.exists_isSquare hψ.1.w
  have e₂ := GlobalTheory.LamPull.isSquare_unique (GlobalTheory.TChart.AbPol.isSquare_comp sqψ R.sq) (by rw [hψφ]; exact sqz)
  have iso : LBIso z.P ((F.univ.P.pull R.φ₂).pull
      (lift (pushPt hψ.1.w (fst z.A z.A)) (pushPt hψ.1.w (snd z.A z.A))).left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff z.isLB (pull_isLB (pull_isLB F.univ.isLB _) _)).1 ?_
    rw [(GlobalTheory.CechPic.cls_eq_iff z.isLB (pull_isLB F.univ.isLB _)).2 isoz, ← e₂, GlobalTheory.CechPic.cls_pull F.univ.isLB,
      GlobalTheory.CechPic.cls_pull (pull_isLB F.univ.isLB _), GlobalTheory.CechPic.cls_pull F.univ.isLB, GlobalTheory.CechPic.pull_comp]
  have hlev : ∀ a, (z.lev a).left ≫ ψ = g ≫ ((onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq).lev a).left := fun a => by
    apply R.pb.1.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg ((z.lev a).left ≫ ·) hψφ).trans ((levz a).trans
        ((congrArg (· ≫ (F.univ.lev a).left) hgπ.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (g ≫ ·) (onPull_lev F.univ R.AH R.φ R.φ₂ R.pb R.sq a).symm).trans (Category.assoc _ _ _).symm)))))
    · exact ((Category.assoc _ _ _).trans ((congrArg _ hψ.1.w).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g) (Over.w (z.lev a)))))).trans ((Category.id_comp g).trans ((Category.comp_id g).symm.trans
        ((congrArg (g ≫ ·) (Over.w ((onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq).lev a)).symm).trans
        (Category.assoc _ _ _).symm)))
  refine ⟨g, ⟨by rw [← Category.assoc, hgπ, hfs], ψ, _, hψ, sqψ, iso, hlev, hψa⟩, ?_⟩
  rintro g' ⟨hg's, ψ', ψ₂', hψ', sqψ', iso', hlev', hact'⟩
  have hlev'' : ∀ a, (z.lev a).left ≫ ψ' ≫ R.φ = (g' ≫ R.π) ≫ (F.univ.lev a).left := fun a => by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ R.φ) (hlev' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (g' ≫ ·) (onPull_lev F.univ R.AH R.φ R.φ₂ R.pb R.sq a)).trans (Category.assoc _ _ _).symm)))
  have iso'' : LBIso z.P (F.univ.P.pull (ψ₂' ≫ R.φ₂)) :=
    GlobalTheory.TChart.AbLevel.lbIso_comp F.univ.isLB (pull_isLB F.univ.isLB _) z.isLB
      (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ (pull_isLB F.univ.isLB R.φ₂)) iso'
  have hf' : g' ≫ R.π = f := hfu _ ⟨by rw [Category.assoc]; exact hg's,
    ψ' ≫ R.φ, ψ₂' ≫ R.φ₂, hψ'.comp R.pb, GlobalTheory.TChart.AbPol.isSquare_comp sqψ' R.sq, iso'', hlev''⟩
  have s' : GlobalTheory.SiegLev.SRelBy z F.univ 1 1 f (ψ' ≫ R.φ) :=
    ⟨(hψ'.comp R.pb).congr hf' rfl, ⟨ψ₂' ≫ R.φ₂, GlobalTheory.TChart.AbPol.isSquare_comp sqψ' R.sq, iso''⟩,
      fun a => by simpa only [pow_one, hf'] using hlev'' a⟩
  have s : GlobalTheory.SiegLev.SRelBy z F.univ 1 1 f φz :=
    ⟨pbz, ⟨φ₂z, sqz, isoz⟩, fun a => by simpa only [pow_one] using levz a⟩
  have hφeq : ψ' ≫ R.φ = φz := GlobalTheory.SiegRigid.eq_of_sRelBy h' M M 1 (cycAway M) (cycAway M) (cycBase hM0)
    (zetaAway M) F.X S F.s t F.univ z f _ _ hM hodd F.princ s' s
  exact hgu g' ⟨hf', ψ', hψ', hφeq, hact'⟩

end GlobalTheory.ActSieg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepPrincipalSiegelAdjointOrderActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_principalSiegel_adjoint_orderAction : ∀ (h' M : ℕ), 1 ≤ h' → 3 ≤ M → Odd M → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range eO) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d₀ → ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) → ∃ (H : Scheme.{0}) (sH : H ⟶ Sp (cycAway M)) (zH : SiegPre h' M (zetaAway M) sH) (actH : O → (zH.A ⟶ zH.A)), zH.Principal ∧ IsRAct zH.A actH ∧ Adj zH.A zH.P bar actH ∧ IsQProjOver sH ∧ IsLocallyNoetherian H ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃! g : S ⟶ H, g ≫ sH = t ∧ ActPB z act zH actH g := by
  first | (exact @GlobalTheory.ActSieg.exists_rep) | (exact GlobalTheory.ActSieg.exists_rep) | (intros; apply GlobalTheory.ActSieg.exists_rep  <;> assumption)
end
