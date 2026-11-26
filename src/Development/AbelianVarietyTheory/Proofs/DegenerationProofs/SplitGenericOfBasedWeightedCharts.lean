module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusKernelGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusStableWeightsGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomGenericFibreKernelTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomGenericFibreKernelTorus
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.KerSubgroup
open SplitPull

theorem exists_agree_locus (X : Scheme.{0}) (N : Type) (v w : N → Γ(X, ⊤)) :
    ∃ (Z : Scheme.{0}) (m : Z ⟶ X), IsClosedImmersion m ∧ (∀ n, m.appTop.hom (v n) = m.appTop.hom (w n)) ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X), (∀ n, f.appTop.hom (v n) = f.appTop.hom (w n)) → ∃ z, z ≫ m = f := by
  let A : Over X := Over.mk (𝔸(N; X) ↘ X)
  have : IsSeparated A.hom := inferInstanceAs (IsSeparated (𝔸(N; X) ↘ X))
  let hv : Over.mk (𝟙 X) ⟶ A := Over.homMk (AffineSpace.homOfVector (𝟙 X) v) (AffineSpace.homOfVector_over _ _)
  let hw : Over.mk (𝟙 X) ⟶ A := Over.homMk (AffineSpace.homOfVector (𝟙 X) w) (AffineSpace.homOfVector_over _ _)
  have key : ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (u : N → Γ(X, ⊤)) (n : N),
      (f ≫ AffineSpace.homOfVector (𝟙 X) u).appTop (AffineSpace.coord X n) = f.appTop.hom (u n) := by
    intro Y f u n
    rw [AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord]
    rfl
  refine ⟨(equalizer hv hw).left, (equalizer.ι hv hw).left, inferInstance, fun n => ?_, fun Y f hf => ?_⟩
  · have e : (equalizer.ι hv hw).left ≫ AffineSpace.homOfVector (𝟙 X) v =
        (equalizer.ι hv hw).left ≫ AffineSpace.homOfVector (𝟙 X) w :=
      congrArg CommaMorphism.left (equalizer.condition hv hw)
    rw [← key, ← key, e]
  · let f' : Over.mk f ⟶ Over.mk (𝟙 X) := Over.homMk f (Category.comp_id _)
    have e : f' ≫ hv = f' ≫ hw := by
      ext1
      change f ≫ AffineSpace.homOfVector (𝟙 X) v = f ≫ AffineSpace.homOfVector (𝟙 X) w
      refine AffineSpace.hom_ext (by simp) fun n => ?_
      rw [key, key, hf]
    exact ⟨(equalizer.lift f' e).left, congrArg CommaMorphism.left (equalizer.lift_ι f' e)⟩

def Rel {X Y : Scheme.{0}} (C : Charts X) (a : {i // C.wt i = C.c₀}) {d : ℕ} (j : Fin d → C.I)
    (k₁ k₂ k₃ e : Y ⟶ X) : Prop :=
  ∃ (h₁ : ⊤ ≤ k₁ ⁻¹ᵁ C.W a) (h₂ : ⊤ ≤ k₂ ⁻¹ᵁ C.W a) (h₃ : ⊤ ≤ k₃ ⁻¹ᵁ C.W a) (h : ⊤ ≤ e ⁻¹ᵁ C.W a),
    (∀ l, C.wt l = C.c₀ → (k₁.appLE _ ⊤ h₁).hom (C.r a l) = (e.appLE _ ⊤ h).hom (C.r a l) ∧
      (k₂.appLE _ ⊤ h₂).hom (C.r a l) = (e.appLE _ ⊤ h).hom (C.r a l) ∧
      (k₃.appLE _ ⊤ h₃).hom (C.r a l) = (e.appLE _ ⊤ h).hom (C.r a l)) ∧
    ∀ n, (k₁.appLE _ ⊤ h₁).hom (C.r a (j n)) * (k₂.appLE _ ⊤ h₂).hom (C.r a (j n)) =
      (k₃.appLE _ ⊤ h₃).hom (C.r a (j n)) * (e.appLE _ ⊤ h).hom (C.r a (j n))

theorem Rel.comp {X Y Y' : Scheme.{0}} {C : Charts X} {a : {i // C.wt i = C.c₀}} {d : ℕ} {j : Fin d → C.I}
    {k₁ k₂ k₃ e : Y ⟶ X} (H : Rel C a j k₁ k₂ k₃ e) (p : Y' ⟶ Y) :
    Rel C a j (p ≫ k₁) (p ≫ k₂) (p ≫ k₃) (p ≫ e) := by
  obtain ⟨h₁, h₂, h₃, h, H₁, H₂⟩ := H
  have g : ∀ k : Y ⟶ X, ⊤ ≤ k ⁻¹ᵁ C.W a → ⊤ ≤ (p ≫ k) ⁻¹ᵁ C.W a := fun k h => p.preimage_mono h
  have key : ∀ (k : Y ⟶ X) (h : ⊤ ≤ k ⁻¹ᵁ C.W a) (l : C.I),
      ((p ≫ k).appLE _ ⊤ (g k h)).hom (C.r a l) = p.appTop.hom ((k.appLE _ ⊤ h).hom (C.r a l)) :=
    fun k h l => (appTop_appLE p k _ rfl _ h _ _).symm
  refine ⟨g _ h₁, g _ h₂, g _ h₃, g _ h, fun l hl => ?_, fun n => ?_⟩
  · rw [key _ h₁, key _ h₂, key _ h₃, key _ h, (H₁ l hl).1, (H₁ l hl).2.1, (H₁ l hl).2.2]
    exact ⟨rfl, rfl, rfl⟩
  · rw [key _ h₁, key _ h₂, key _ h₃, key _ h, ← map_mul, ← map_mul, H₂]

theorem rel_pull {X X' Y : Scheme.{0}} (C : Charts X) (φ : X' ⟶ X) [IsAffineHom φ] (a : {i // C.wt i = C.c₀})
    {d : ℕ} (j : Fin d → C.I) (k₁ k₂ k₃ e : Y ⟶ X') :
    Rel (C.pull φ) a j k₁ k₂ k₃ e ↔ Rel C a j (k₁ ≫ φ) (k₂ ≫ φ) (k₃ ≫ φ) (e ≫ φ) := by
  have key : ∀ (k : Y ⟶ X') (h : ⊤ ≤ k ⁻¹ᵁ (C.pull φ).W a) (l : C.I),
      (k.appLE _ ⊤ h).hom ((C.pull φ).r a l) = ((k ≫ φ).appLE (C.W a) ⊤ h).hom (C.r a l) :=
    fun k h l => appLE_app k φ _ rfl _ h h _
  refine exists_congr fun h₁ => exists_congr fun h₂ => exists_congr fun h₃ => exists_congr fun h => ?_
  simp only [key]
  rfl

variable {S : Scheme.{0}} {H : Over S} [GrpObj H]

theorem exists_rep [IsAffine S] [LocallyOfFiniteType H.hom] (C : Charts H.left) (a : {i // C.wt i = C.c₀})
    {d : ℕ} (j : Fin d → C.I) (he : ⊤ ≤ eSec H ⁻¹ᵁ C.W a) :
    ∃ (Z : Over S) (k₁ k₂ k₃ : Z ⟶ H), LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧
      Rel C a j k₁.left k₂.left k₃.left (1 : Z ⟶ H).left ∧
      ∀ (Y : Over S) (l₁ l₂ l₃ : Y ⟶ H), Rel C a j l₁.left l₂.left l₃.left (1 : Y ⟶ H).left →
        ∃ z : Y ⟶ Z, z ≫ k₁ = l₁ ∧ z ≫ k₂ = l₂ ∧ z ≫ k₃ = l₃ := by
  let W : Over S := Over.mk ((C.W a).ι ≫ H.hom)
  let inc : W ⟶ H := Over.homMk (C.W a).ι rfl
  have : IsAffine W.left := C.aff a
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType ((C.W a).ι ≫ H.hom))
  have : QuasiCompact W.hom := inferInstance
  let X : Over S := W ⊗ W ⊗ W
  have hX₁ : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType (pullback.fst W.hom (pullback.fst W.hom W.hom ≫ W.hom) ≫ W.hom)
    infer_instance
  have hX₂ : QuasiCompact X.hom := by
    change QuasiCompact (pullback.fst W.hom (pullback.fst W.hom W.hom ≫ W.hom) ≫ W.hom)
    infer_instance
  have hinc : ∀ p : X ⟶ W, ⊤ ≤ (p ≫ inc).left ⁻¹ᵁ C.W a := fun p x _ => (p.left x).2
  have h1 : ⊤ ≤ (1 : X ⟶ H).left ⁻¹ᵁ C.W a := (toUnit X).left.preimage_mono he
  let p₁ : X ⟶ W := fst _ _
  let p₂ : X ⟶ W := snd _ _ ≫ fst _ _
  let p₃ : X ⟶ W := snd _ _ ≫ snd _ _
  let E (p : X ⟶ W) (l : C.I) := ((p ≫ inc).left.appLE _ ⊤ (hinc p)).hom (C.r a l)
  let E₀ (l : C.I) := ((1 : X ⟶ H).left.appLE _ ⊤ h1).hom (C.r a l)
  let J := {l // C.wt l = C.c₀}
  obtain ⟨Z, m, hm, hZ, hu⟩ := exists_agree_locus X.left (J ⊕ J ⊕ J ⊕ Fin d)
    (Sum.elim (fun l => E p₁ l.1) (Sum.elim (fun l => E p₂ l.1) (Sum.elim (fun l => E p₃ l.1)
      fun n => E p₁ (j n) * E p₂ (j n))))
    (Sum.elim (fun l => E₀ l.1) (Sum.elim (fun l => E₀ l.1) (Sum.elim (fun l => E₀ l.1)
      fun n => E p₃ (j n) * E₀ (j n))))
  have key : ∀ (Y : Over S) (f : Y ⟶ X),
      Rel C a j (f ≫ p₁ ≫ inc).left (f ≫ p₂ ≫ inc).left (f ≫ p₃ ≫ inc).left (1 : Y ⟶ H).left ↔
      ((∀ l : J, f.left.appTop.hom (E p₁ l.1) = f.left.appTop.hom (E₀ l.1)) ∧
      (∀ l : J, f.left.appTop.hom (E p₂ l.1) = f.left.appTop.hom (E₀ l.1)) ∧
      (∀ l : J, f.left.appTop.hom (E p₃ l.1) = f.left.appTop.hom (E₀ l.1)) ∧
      ∀ n, f.left.appTop.hom (E p₁ (j n) * E p₂ (j n)) = f.left.appTop.hom (E p₃ (j n) * E₀ (j n))) := by
    intro Y f
    have g : ∀ p : X ⟶ W, ⊤ ≤ (f ≫ p ≫ inc).left ⁻¹ᵁ C.W a := fun p => f.left.preimage_mono (hinc p)
    have g1 : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a := (toUnit Y).left.preimage_mono he
    have e : ∀ p l, f.left.appTop.hom (E p l) = ((f ≫ p ≫ inc).left.appLE _ ⊤ (g p)).hom (C.r a l) :=
      fun p l => appTop_appLE _ _ _ rfl _ _ _ _
    have e₀ : ∀ l, f.left.appTop.hom (E₀ l) = ((1 : Y ⟶ H).left.appLE _ ⊤ g1).hom (C.r a l) :=
      fun l => appTop_appLE _ _ _ (by rw [← Over.comp_left, MonObj.comp_one]) _ _ _ _
    simp only [map_mul, e, e₀]
    constructor
    · rintro ⟨_, _, _, _, H₁, H₂⟩
      exact ⟨fun l => (H₁ l.1 l.2).1, fun l => (H₁ l.1 l.2).2.1, fun l => (H₁ l.1 l.2).2.2, H₂⟩
    · rintro ⟨H₁, H₂, H₃, H₄⟩
      exact ⟨g _, g _, g _, g1, fun l hl => ⟨H₁ ⟨l, hl⟩, H₂ ⟨l, hl⟩, H₃ ⟨l, hl⟩⟩, H₄⟩
  let m' : Over.mk (m ≫ X.hom) ⟶ X := Over.homMk m rfl
  refine ⟨Over.mk (m ≫ X.hom), m' ≫ p₁ ≫ inc, m' ≫ p₂ ≫ inc, m' ≫ p₃ ≫ inc,
    inferInstanceAs (LocallyOfFiniteType (m ≫ X.hom)), inferInstanceAs (QuasiCompact (m ≫ X.hom)),
    (key _ m').2 ⟨fun l => hZ (.inl l), fun l => hZ (.inr (.inl l)), fun l => hZ (.inr (.inr (.inl l))),
      fun l => hZ (.inr (.inr (.inr l)))⟩, fun Y l₁ l₂ l₃ hl => ?_⟩
  have lf : ∀ l : Y ⟶ H, ⊤ ≤ l.left ⁻¹ᵁ C.W a → ∃ q : Y ⟶ W, q ≫ inc = l := by
    intro l h
    have hr : Set.range l.left ⊆ Set.range (C.W a).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact h trivial
    refine ⟨Over.homMk (IsOpenImmersion.lift (C.W a).ι l.left hr) ?_, ?_⟩
    · change _ ≫ (C.W a).ι ≫ H.hom = _
      rw [IsOpenImmersion.lift_fac_assoc, Over.w]
    · ext1
      exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨q₁, rfl⟩ := lf l₁ hl.1
  obtain ⟨q₂, rfl⟩ := lf l₂ hl.2.1
  obtain ⟨q₃, rfl⟩ := lf l₃ hl.2.2.1
  let f : Y ⟶ X := lift q₁ (lift q₂ q₃)
  have f₁ : f ≫ p₁ ≫ inc = q₁ ≫ inc := by simp [f, p₁]
  have f₂ : f ≫ p₂ ≫ inc = q₂ ≫ inc := by simp [f, p₂]
  have f₃ : f ≫ p₃ ≫ inc = q₃ ≫ inc := by simp [f, p₃]
  rw [← f₁, ← f₂, ← f₃] at hl ⊢
  obtain ⟨H₁, H₂, H₃, H₄⟩ := (key Y f).1 hl
  obtain ⟨z, hz⟩ := hu Y.left f.left (by
    rintro (l | l | l | l)
    exacts [H₁ l, H₂ l, H₃ l, H₄ l])
  let z' : Y ⟶ Over.mk (m ≫ X.hom) := Over.homMk z (by
    change z ≫ m ≫ X.hom = _
    rw [← Category.assoc, hz, Over.w])
  have hz' : z' ≫ m' = f := Over.OverMorphism.ext hz
  exact ⟨z', by rw [← Category.assoc z', hz'], by rw [← Category.assoc z', hz'], by rw [← Category.assoc z', hz']⟩

theorem appTop_charUnit_mul {X : Type} [AddCommGroup X] {Y : Over S} (t₁ t₂ : Y ⟶ splitTorus S X) (χ : X) :
    (t₁ * t₂).left.appTop.hom (charUnit S X χ).val =
      t₁.left.appTop.hom (charUnit S X χ).val * t₂.left.appTop.hom (charUnit S X χ).val := by
  rw [← splitTorusPointsEquiv_val, ← splitTorusPointsEquiv_val,
    ← splitTorusPointsEquiv_val, map_mul, MonoidHom.mul_apply, Units.val_mul]

theorem torus_ext {d : ℕ} {Y : Over S} (t₁ t₂ : Y ⟶ splitTorus S (Fin d → ℤ))
    (h : ∀ n, t₁.left.appTop.hom (charUnit S _ (Pi.single n 1)).val =
      t₂.left.appTop.hom (charUnit S _ (Pi.single n 1)).val) : t₁ = t₂ := by
  apply (splitTorusPointsEquiv S _ Y).injective
  apply MonoidHom.toAdditiveRight.injective
  refine AddMonoidHom.toIntLinearMap_injective ((Pi.basisFun ℤ (Fin d)).ext fun n => ?_)
  rw [Pi.basisFun_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  exact (splitTorusPointsEquiv_val S _ Y t₁ _).trans ((h n).trans (splitTorusPointsEquiv_val S _ Y t₂ _).symm)

theorem rel_of_kerIs {C : Charts H.left} {a : {i // C.wt i = C.c₀}} {d : ℕ} {j : Fin d → C.I}
    {i : splitTorus S (Fin d → ℤ) ⟶ H} (hi : C.KerIs a j i) {Y : Over S} (t₁ t₂ : Y ⟶ splitTorus S (Fin d → ℤ)) :
    Rel C a j (t₁ ≫ i).left (t₂ ≫ i).left ((t₁ * t₂) ≫ i).left (1 : Y ⟶ H).left := by
  obtain ⟨h₁, h, H₁⟩ := (hi.2.1 Y _).2 ⟨t₁, rfl⟩
  obtain ⟨h₂, _, H₂⟩ := (hi.2.1 Y _).2 ⟨t₂, rfl⟩
  obtain ⟨h₃, _, H₃⟩ := (hi.2.1 Y _).2 ⟨t₁ * t₂, rfl⟩
  refine ⟨h₁, h₂, h₃, h, fun l hl => ⟨H₁ l hl, H₂ l hl, H₃ l hl⟩, fun n => ?_⟩
  rw [hi.2.2 Y t₁ n h₁ h, hi.2.2 Y t₂ n h₂ h, hi.2.2 Y _ n h₃ h, appTop_charUnit_mul]
  ring

theorem mul_eq_of_rel {C : Charts H.left} {a : {i // C.wt i = C.c₀}} {d : ℕ} {c : Fin d → C.Cl} {j : Fin d → C.I}
    {i : splitTorus S (Fin d → ℤ) ⟶ H} [IsMonHom i] (hi : C.KerIs a j i) (hb : C.Based c a j) {Y : Over S}
    {k₁ k₂ k₃ : Y ⟶ H} (hk : Rel C a j k₁.left k₂.left k₃.left (1 : Y ⟶ H).left) : k₁ * k₂ = k₃ := by
  obtain ⟨h₁, h₂, h₃, h, H₁, H₂⟩ := hk
  obtain ⟨t₁, rfl⟩ := (hi.2.1 Y k₁).1 ⟨h₁, h, fun l hl => (H₁ l hl).1⟩
  obtain ⟨t₂, rfl⟩ := (hi.2.1 Y k₂).1 ⟨h₂, h, fun l hl => (H₁ l hl).2.1⟩
  obtain ⟨t₃, rfl⟩ := (hi.2.1 Y k₃).1 ⟨h₃, h, fun l hl => (H₁ l hl).2.2⟩
  rw [← MonObj.mul_comp]
  congr 1
  refine torus_ext _ _ fun n => ?_
  have e := H₂ n
  rw [hi.2.2 Y t₁ n h₁ h, hi.2.2 Y t₂ n h₂ h, hi.2.2 Y _ n h₃ h] at e
  have hu : IsUnit (((1 : Y ⟶ H).left.appLE _ ⊤ h).hom (C.r a (j n))) := by
    refine RingedSpace.isUnit_of_isUnit_germ (X := Y.left.toRingedSpace) ⊤ _ fun x hx => ?_
    refine (Scheme.mem_basicOpen Y.left _ x hx).1 ?_
    erw [Scheme.basicOpen_appLE]
    exact ⟨trivial, (toUnit Y).left.preimage_mono (hb.2 n).2 trivial⟩
  rw [appTop_charUnit_mul]
  refine (hu.mul hu).mul_right_cancel ?_
  linear_combination e

theorem eSec_pull {S' : Scheme.{0}} (t : S' ⟶ S) :
    ∃ q, eSec ((Over.pullback t).obj H) ≫ pullback.fst H.hom t = q ≫ eSec H := by
  refine ⟨(Functor.LaxMonoidal.ε (Over.pullback t)).left ≫ pullback.fst _ t, ?_⟩
  rw [Category.assoc]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (SplitTorusPoints.map_left_fst t η[H]))

theorem based_pull {S' : Scheme.{0}} (t : S' ⟶ S) [IsAffineHom (pullback.fst H.hom t)]
    {C : Charts H.left} {a : {i // C.wt i = C.c₀}} {d : ℕ} {c : Fin d → C.Cl} {j : Fin d → C.I}
    (hb : C.Based c a j) :
    Charts.Based (H := (Over.pullback t).obj H) (C.pull (pullback.fst H.hom t)) c a j := by
  obtain ⟨q, hq⟩ := eSec_pull (H := H) t
  refine ⟨?_, fun n => ⟨(hb.2 n).1, ?_⟩⟩
  · change ⊤ ≤ (eSec ((Over.pullback t).obj H) ≫ pullback.fst H.hom t) ⁻¹ᵁ C.W a
    rw [hq]
    exact q.preimage_mono hb.1
  · have e := Scheme.preimage_basicOpen (pullback.fst H.hom t) (C.r a (j n))
    have : ⊤ ≤ (eSec ((Over.pullback t).obj H) ≫ pullback.fst H.hom t) ⁻¹ᵁ H.left.basicOpen (C.r a (j n)) := by
      rw [hq]
      exact q.preimage_mono (hb.2 n).2
    rw [Scheme.Hom.comp_preimage, e] at this
    exact this

theorem one_left_fst {S' : Scheme.{0}} (t : S' ⟶ S) (Y' : Over S') (Y : Over S) (p : Y'.left ⟶ Y.left)
    (hp : p ≫ Y.hom = Y'.hom ≫ t) :
    (1 : Y' ⟶ (Over.pullback t).obj H).left ≫ pullback.fst H.hom t = p ≫ (1 : Y ⟶ H).left := by
  let z : Y' ⟶ (Over.pullback t).obj Y := Over.homMk (pullback.lift p Y'.hom hp) (pullback.lift_snd _ _ _)
  rw [← MonObj.comp_one z, ← Functor.map_one, Over.comp_left, Category.assoc, SplitTorusPoints.map_left_fst,
    ← Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

theorem rel_map {S' : Scheme.{0}} (t : S' ⟶ S) [IsAffineHom (pullback.fst H.hom t)]
    {C : Charts H.left} {a : {i // C.wt i = C.c₀}} {d : ℕ} {j : Fin d → C.I} {Z : Over S} {k₁ k₂ k₃ : Z ⟶ H}
    (hk : Rel C a j k₁.left k₂.left k₃.left (1 : Z ⟶ H).left) :
    Rel (C.pull (pullback.fst H.hom t)) a j ((Over.pullback t).map k₁).left ((Over.pullback t).map k₂).left
      ((Over.pullback t).map k₃).left (1 : (Over.pullback t).obj Z ⟶ (Over.pullback t).obj H).left := by
  refine (rel_pull C _ a j _ _ _ _).2 ?_
  have e := one_left_fst (H := H) t ((Over.pullback t).obj Z) Z (pullback.fst _ _) pullback.condition
  have h := hk.comp (pullback.fst Z.hom t)
  rw [← SplitTorusPoints.map_left_fst, ← SplitTorusPoints.map_left_fst, ← SplitTorusPoints.map_left_fst] at h
  exact e ▸ h

theorem mul_eq_of_univ {S' : Scheme.{0}} (t : S' ⟶ S) [IsAffineHom (pullback.fst H.hom t)]
    {C : Charts H.left} {a : {i // C.wt i = C.c₀}} {d : ℕ} {j : Fin d → C.I} {Z : Over S} {k₁ k₂ k₃ : Z ⟶ H}
    (hu : ∀ (Y : Over S) (l₁ l₂ l₃ : Y ⟶ H), Rel C a j l₁.left l₂.left l₃.left (1 : Y ⟶ H).left →
        ∃ z : Y ⟶ Z, z ≫ k₁ = l₁ ∧ z ≫ k₂ = l₂ ∧ z ≫ k₃ = l₃)
    (hgen : (Over.pullback t).map (k₁ * k₂) = (Over.pullback t).map k₃) {Y : Over S'}
    {l₁ l₂ l₃ : Y ⟶ (Over.pullback t).obj H}
    (hl : Rel (C.pull (pullback.fst H.hom t)) a j l₁.left l₂.left l₃.left
      (1 : Y ⟶ (Over.pullback t).obj H).left) : l₁ * l₂ = l₃ := by
  have h := (rel_pull C _ a j _ _ _ _).1 hl
  let Y₀ : Over S := Over.mk (Y.hom ≫ t)
  let P (k : Y ⟶ (Over.pullback t).obj H) : Y₀ ⟶ H :=
    Over.homMk (k.left ≫ pullback.fst H.hom t) (by
      change _ = Y.hom ≫ t
      rw [← Over.w k]
      exact (Category.assoc _ _ _).trans ((congrArg (k.left ≫ ·) pullback.condition).trans
        (Category.assoc _ _ _).symm))
  have e := (one_left_fst (H := H) t Y Y₀ (𝟙 _) (Category.id_comp _)).trans (Category.id_comp _)
  obtain ⟨z, h₁, h₂, h₃⟩ := hu Y₀ (P l₁) (P l₂) (P l₃) (e ▸ h)
  let z' : Y ⟶ (Over.pullback t).obj Z :=
    Over.homMk (pullback.lift z.left Y.hom (Over.w z)) (pullback.lift_snd _ _ _)
  have key : ∀ (k : Z ⟶ H) (l : Y ⟶ (Over.pullback t).obj H), z ≫ k = P l →
      z' ≫ (Over.pullback t).map k = l := by
    intro k l hl
    ext1
    refine pullback.hom_ext ?_ ((Over.w _).trans (Over.w l).symm)
    refine (Category.assoc _ _ _).trans ((congrArg (z'.left ≫ ·) (SplitTorusPoints.map_left_fst t k)).trans
      ((Category.assoc _ _ _).symm.trans ?_))
    exact (congrArg (· ≫ k.left) (pullback.lift_fst _ _ _)).trans (congrArg CommaMorphism.left hl)
  rw [← key _ _ h₃, ← hgen, Functor.map_mul, MonObj.comp_mul, key _ _ h₁, key _ _ h₂]

theorem isMonHom_of_mul {T : Over S} [GrpObj T] (i : T ⟶ H)
    (hmul : ∀ (Y : Over S) (t₁ t₂ : Y ⟶ T), (t₁ ≫ i) * (t₂ ≫ i) = (t₁ * t₂) ≫ i) : IsMonHom i := by
  constructor
  · have h := hmul (𝟙_ _) 1 1
    rw [_root_.mul_one, mul_eq_left, Hom.one_def, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _)] at h
    simpa using h
  · have h := hmul _ (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [← h]
    congr 1

theorem isMonHom_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → IsMonHom i := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS a j hb i hi
  obtain ⟨Z, k₁, k₂, k₃, _, _, hk, hu⟩ := exists_rep C a j hb.1
  have hgen := GenericEq.map_eq_generic R Z Sg hD G (k₁ * k₂) k₃ fun x hx => by
    obtain ⟨K, _, t, _, ht, hc, i', hT⟩ := hS x hx
    refine ⟨K, inferInstance, t, ht, ?_⟩
    have := hT.hom
    have : Smooth ((Over.pullback t).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom t))
    have : IsSeparated ((Over.pullback t).obj G).hom := inferInstanceAs (IsSeparated (pullback.snd G.hom t))
    have : QuasiCompact ((Over.pullback t).obj G).hom := inferInstanceAs (QuasiCompact (pullback.snd G.hom t))
    have hb' := based_pull t hb
    rw [Functor.map_mul]
    exact mul_eq_of_rel (GlobalTheory.T.torus_cut_by_invariantRatios_field K ((Over.pullback t).obj G) _ d c i' a j hc hT hb') hb' (rel_map t hk)
  exact isMonHom_of_mul i fun Y t₁ t₂ => mul_eq_of_univ (Out.jK R) hu hgen (rel_of_kerIs hi t₁ t₂)

end GlobalTheory.ZJ.KerSubgroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomGenericFibreKernelTorusStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_generic_fibre_kernel_torus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → IsMonHom i := by
  first | exact @GlobalTheory.ZJ.KerSubgroup.isMonHom_generic | exact GlobalTheory.ZJ.KerSubgroup.isMonHom_generic | (intros; apply GlobalTheory.ZJ.KerSubgroup.isMonHom_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericInvariantsGeneratedByRatios
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearMapEqZeroOfOneTmulMemRange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open TensorProduct in
theorem _root_.GlobalTheory.exists_smul_mem_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : Type) [CommRing A]
      [Algebra R A] [Algebra.FiniteType R A] (A₀ : Subalgebra R A) (x : A)
      (Sg : Set (PrimeSpectrum R)), A₀.FG → Dense Sg →
      (∀ P ∈ Sg, ∃ (K : Type) (_ : Field K) (_ : Algebra R K),
        RingHom.ker (algebraMap R K) = P.asIdeal ∧
        (1 ⊗ₜ[R] x : TensorProduct R K A) ∈
          (Algebra.TensorProduct.map (AlgHom.id R K) A₀.val).range) →
      ∃ a : R, a ≠ 0 ∧ a • x ∈ A₀ := by
  intro R _ _ _ A _ _ _ A₀ x Sg hfg hdense hfib
  classical
  haveI : Algebra.FiniteType R A₀ := (Subalgebra.fg_iff_finiteType A₀).1 hfg
  haveI : Algebra.FiniteType A₀ A := Algebra.FiniteType.of_restrictScalars_finiteType R A₀ A
  obtain ⟨a, ha0, s, -, hli, hspan⟩ := _root_.GlobalTheory.GenericFreeness.exists_hasBasisAway_quotient R A₀ A (M := A) (Submodule.span A₀ ({1} : Set A)) (Submodule.fg_span_singleton 1)
  set P := (Submodule.span A₀ ({1} : Set A)).restrictScalars R with hPdef
  have hP : ∀ y, y ∈ P ↔ y ∈ A₀ := by
    intro y
    rw [hPdef, Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      rw [Algebra.smul_def, _root_.mul_one]
      exact c.2
    · intro hy
      exact ⟨⟨y, hy⟩, by rw [Algebra.smul_def, _root_.mul_one]; rfl⟩
  obtain ⟨N, hN⟩ := hspan x Submodule.mem_top
  obtain ⟨p, hp, v, hv, hpv⟩ := Submodule.mem_sup.1 hN
  obtain ⟨c, hcs, hcv⟩ := Submodule.mem_span_set.1 hv
  have hcoord : ∀ (K : Type) [Field K] [Algebra R K], algebraMap R K a ≠ 0 → ∀ j ∈ s,
      ∃ θ : A →ₗ[R] K, (∀ y ∈ P, θ y = 0) ∧ ∀ m ∈ s, θ m = if m = j then 1 else 0 := by
    intro K _ _ haK j hj
    let S := Submonoid.powers a
    let f := LocalizedModule.mkLinearMap S (A ⧸ P)
    have hli' : LinearIndependent R (fun i : s => P.mkQ (i : A)) := hli
    have hliₐ := hli'.of_isLocalizedModule (Localization S) S f
    have hsp : ⊤ ≤ Submodule.span (Localization S) (Set.range (⇑f ∘ fun i : s => P.mkQ (i : A))) := by
      intro z _
      obtain ⟨⟨q, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f z
      obtain ⟨y, rfl⟩ := P.mkQ_surjective q
      obtain ⟨n, hn⟩ := hspan y Submodule.mem_top
      obtain ⟨p', hp', w, hw, hpw⟩ := Submodule.mem_sup.1 hn
      have h1 : P.mkQ (a ^ n • y) ∈ Submodule.span R (Set.range fun i : s => P.mkQ (i : A)) := by
        have hp0 : P.mkQ p' = 0 := (Submodule.Quotient.mk_eq_zero P).2 hp'
        rw [← hpw, map_add (f := _), hp0, zero_add]
        have := Submodule.mem_map_of_mem (f := P.mkQ) hw
        rwa [Submodule.map_span, Set.image_eq_range] at this
      have h2 : f (P.mkQ (a ^ n • y)) ∈ Submodule.span (Localization S) (Set.range (⇑f ∘ fun i : s => P.mkQ (i : A))) := by
        have := Submodule.mem_map_of_mem (f := f) h1
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact Submodule.span_le_restrictScalars R (Localization S) _ this
      have hmemS : a ^ n * (t : R) ∈ S := S.mul_mem (Submonoid.pow_mem _ (Submonoid.mem_powers a) n) t.2
      have hu : IsUnit (algebraMap R (Localization S) (a ^ n * t)) := IsLocalization.map_units _ ⟨_, hmemS⟩
      have heq : (algebraMap R (Localization S) (a ^ n * t)) • IsLocalizedModule.mk' f (P.mkQ y) t = f (P.mkQ (a ^ n • y)) := by
        rw [algebraMap_smul, mul_smul, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel', map_smul, map_smul]
      show IsLocalizedModule.mk' f (P.mkQ y) t ∈ _
      rw [← inv_smul_smul hu.unit (IsLocalizedModule.mk' f (P.mkQ y) t)]
      exact Submodule.smul_of_tower_mem _ _ (by rw [Units.smul_def, IsUnit.unit_spec, heq]; exact h2)
    let b := Module.Basis.mk hliₐ hsp
    have hunit : ∀ y : S, IsUnit ((Algebra.ofId R K) y) := by
      rintro ⟨y, k, rfl⟩
      exact IsUnit.mk0 _ (by rw [map_pow]; exact pow_ne_zero _ haK)
    let ψ : Localization S →ₐ[R] K := IsLocalization.liftAlgHom hunit
    refine ⟨ψ.toLinearMap ∘ₗ ((b.coord ⟨j, hj⟩).restrictScalars R) ∘ₗ f ∘ₗ P.mkQ, ?_, ?_⟩
    · intro y hy
      simp [(Submodule.Quotient.mk_eq_zero P).2 hy]
    · intro m hm
      have hb : f (P.mkQ m) = b ⟨m, hm⟩ := by simp [b]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, hb, Module.Basis.coord_apply, Module.Basis.repr_self]
      by_cases hmj : m = j
      · subst hmj; simp
      · simp [Finsupp.single_apply, hmj, Ne.symm hmj]
  have hfibre : ∀ P' ∈ Sg, a ∉ P'.asIdeal → ∀ j ∈ s, c j ∈ P'.asIdeal := by
    intro P' hP' haP j hj
    obtain ⟨K, hK, hKa, hker, hmem⟩ := hfib P' hP'
    obtain ⟨z, hz⟩ := (AlgHom.mem_range _).1 hmem
    have haK : algebraMap R K a ≠ 0 := fun h => haP (hker ▸ RingHom.mem_ker.2 h)
    obtain ⟨θ, hθP, hθs⟩ := hcoord K haK j hj
    let Θ : K ⊗[R] A →ₗ[R] K := TensorProduct.lift ((LinearMap.mul R K).compl₂ θ)
    have hΘ : ∀ k y, Θ (k ⊗ₜ y) = k * θ y := fun k y => rfl
    have hΘ0' : ∀ w, Θ (Algebra.TensorProduct.map (AlgHom.id R K) A₀.val w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul k y =>
        rw [Algebra.TensorProduct.map_tmul, hΘ, hθP (A₀.val y) ((hP _).2 y.2), mul_zero]
      | add z₁ z₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂, add_zero]
    have hx : θ x = 0 := by
      have hΘ0 := hΘ0' z
      rw [hz, hΘ, _root_.one_mul] at hΘ0
      exact hΘ0
    by_cases hjs : j ∈ c.support
    · have hθv : θ v = c j • (1 : K) := by
        rw [← hcv, map_finsuppSum, Finsupp.sum, Finset.sum_eq_single j]
        · rw [map_smul, hθs j hj, if_pos rfl]
        · intro m hm hmj
          rw [map_smul, hθs m (hcs hm), if_neg hmj, smul_zero]
        · intro h; exact absurd hjs h
      have h0 : θ (a ^ N • x) = 0 := by rw [map_smul, hx, smul_zero]
      rw [← hpv, map_add (f := _), hθP p hp, zero_add, hθv, Algebra.smul_def, _root_.mul_one] at h0
      rw [← hker]
      exact RingHom.mem_ker.2 h0
    · rw [Finsupp.notMem_support_iff.1 hjs]
      exact P'.asIdeal.zero_mem
  have hc0 : c = 0 := by
    ext j
    by_contra hne
    have hj : j ∈ s := hcs (Finsupp.mem_support_iff.2 hne)
    have hsub : Sg ⊆ PrimeSpectrum.zeroLocus {c j * a} := by
      intro P' hP'
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      by_cases haP : a ∈ P'.asIdeal
      · exact P'.asIdeal.mul_mem_left _ haP
      · exact P'.asIdeal.mul_mem_right _ (hfibre P' hP' haP j hj)
    have huniv : PrimeSpectrum.zeroLocus {c j * a} = Set.univ :=
      Set.eq_univ_of_univ_subset (hdense.closure_eq ▸ closure_minimal hsub (PrimeSpectrum.isClosed_zeroLocus _))
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff, Set.singleton_subset_iff] at huniv
    have hz : c j * a = 0 := (mem_nilradical.1 huniv).eq_zero
    exact hne ((mul_eq_zero.1 hz).resolve_right ha0)
  refine ⟨a ^ N, pow_ne_zero _ ha0, (hP _).1 ?_⟩
  have hv0 : v = 0 := by rw [← hcv, hc0, Finsupp.sum_zero_index]
  rw [← hpv, hv0, add_zero]
  exact hp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericInvariantsGeneratedByRatios
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.GenericInv
open SplitPull
open scoped TensorProduct

theorem exists_locus {S : Scheme.{0}} (X : Over S) {n : Type} (v w : n → Γ(X.left, ⊤)) :
    ∃ (E : Over S) (e : E ⟶ X), IsClosedImmersion e.left ∧
      (∀ l, e.left.appTop.hom (v l) = e.left.appTop.hom (w l)) ∧
      ∀ (Y : Over S) (m : Y ⟶ X), (∀ l, m.left.appTop.hom (v l) = m.left.appTop.hom (w l)) →
        ∃ q : Y ⟶ E, q ≫ e = m := by
  let A : Over S := Over.mk (𝔸(n; S) ↘ S)
  have : IsSeparated A.hom := inferInstanceAs (IsSeparated (𝔸(n; S) ↘ S))
  let f : X ⟶ A := Over.homMk (AffineSpace.homOfVector X.hom v) (AffineSpace.homOfVector_over _ _)
  let g : X ⟶ A := Over.homMk (AffineSpace.homOfVector X.hom w) (AffineSpace.homOfVector_over _ _)
  have key : ∀ (Y : Over S) (m : Y ⟶ X) (u : n → Γ(X.left, ⊤)) l,
      (m.left ≫ AffineSpace.homOfVector X.hom u).appTop.hom (AffineSpace.coord S l) =
        m.left.appTop.hom (u l) := by
    intro Y m u l
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact congrArg _ (AffineSpace.homOfVector_appTop_coord _ _ l)
  refine ⟨equalizer f g, equalizer.ι f g, inferInstance, fun l => ?_, fun Y m hm => ?_⟩
  · have h : (equalizer.ι f g).left ≫ AffineSpace.homOfVector X.hom v =
        (equalizer.ι f g).left ≫ AffineSpace.homOfVector X.hom w :=
      congrArg (fun k => k.left) (equalizer.condition f g)
    rw [← key, ← key, h]
  · refine ⟨equalizer.lift m ?_, equalizer.lift_ι _ _⟩
    refine Over.OverMorphism.ext (AffineSpace.hom_ext ((Over.w _).trans (Over.w _).symm) fun l => ?_)
    exact (key Y m v l).trans ((hm l).trans (key Y m w l).symm)

theorem exists_clear {R : Type} [CommRing R] [IsDomain R] {A A' : CommRingCat.{0}}
    {a : CommRingCat.of R ⟶ A} {p : A ⟶ A'} {q : CommRingCat.of (FractionRing R) ⟶ A'}
    (h : IsPushout a (CommRingCat.ofHom (algebraMap R (FractionRing R))) p q) (u : A') :
    ∃ (s : R) (x : A), s ≠ 0 ∧ p.hom (a.hom s) * u = p.hom x := by
  have hw : ∀ s, p.hom (a.hom s) = q.hom (algebraMap R (FractionRing R) s) :=
    fun s => congrArg (fun k => k.hom s) h.w
  have hu := (CommRingCat.closure_range_union_range_eq_top_of_isPushout h).ge (Subring.mem_top u)
  induction hu using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨x, rfl⟩ | ⟨z, rfl⟩
    · exact ⟨1, x, one_ne_zero, by simp⟩
    · obtain ⟨⟨r, s⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors R) (S := FractionRing R) z
      refine ⟨s, a.hom r, nonZeroDivisors.ne_zero s.2, ?_⟩
      rw [hw, hw, ← map_mul, _root_.mul_comm, hz]
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | one => exact ⟨1, 1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, x, hs, e⟩ := hy
    obtain ⟨s', x', hs', e'⟩ := hz
    refine ⟨s * s', a.hom s' * x + a.hom s * x', mul_ne_zero hs hs', ?_⟩
    simp only [map_mul, map_add (f := _), ← e, ← e']
    ring
  | neg y _ hy =>
    obtain ⟨s, x, hs, e⟩ := hy
    exact ⟨s, -x, hs, by rw [map_neg, ← e, mul_neg]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨s, x, hs, e⟩ := hy
    obtain ⟨s', x', hs', e'⟩ := hz
    refine ⟨s * s', x * x', mul_ne_zero hs hs', ?_⟩
    simp only [map_mul, ← e, ← e']
    ring

theorem one_tmul_mem_range {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {A A' : CommRingCat.{0}}
    [Algebra R A] {p : A ⟶ A'} {q : CommRingCat.of K ⟶ A'}
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R K)) p q)
    (T : Set A) (x : A) (hx : p.hom x ∈ Subring.closure (Set.range q.hom ∪ p.hom '' T)) :
    (1 ⊗ₜ[R] x : K ⊗[R] A) ∈
      (Algebra.TensorProduct.map (AlgHom.id R K) (Algebra.adjoin R T).val).range := by
  let θ : A' ⟶ CommRingCat.of (K ⊗[R] A) := h.desc
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := A)).toRingHom)
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := K) (B := A)).toRingHom) (by
      ext r
      exact ((Algebra.TensorProduct.includeRight (R := R) (A := K) (B := A)).commutes r).trans
        ((Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := K) (B := A)).commutes r).symm)
  have hp : ∀ y, θ.hom (p.hom y) = (1 ⊗ₜ[R] y : K ⊗[R] A) := fun y =>
    congrArg (fun k : A ⟶ CommRingCat.of (K ⊗[R] A) => k.hom y) (h.inl_desc _ _ _ : p ≫ θ = _)
  have hq : ∀ y, θ.hom (q.hom y) = (y ⊗ₜ[R] 1 : K ⊗[R] A) := fun y =>
    congrArg (fun k : CommRingCat.of K ⟶ CommRingCat.of (K ⊗[R] A) => k.hom y) (h.inr_desc _ _ _ : q ≫ θ = _)
  rw [← hp]
  refine (Subring.closure_le (t := (Algebra.TensorProduct.map (AlgHom.id R K)
    (Algebra.adjoin R T).val).range.toSubring.comap θ.hom)).2 ?_ hx
  rintro _ (⟨y, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact ⟨y ⊗ₜ 1, (hq y).symm⟩
  · exact ⟨1 ⊗ₜ ⟨y, Algebra.subset_adjoin hy⟩, (hp y).symm⟩

theorem isPushout_sections {R K : CommRingCat.{0}} (ψ : R ⟶ K) {X : Scheme.{0}} (π : X ⟶ Spec R)
    {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout ((Scheme.ΓSpecIso R).inv ≫ π.appLE ⊤ V le_top) ψ ((pullback.fst π (Spec.map ψ)).app V)
      ((Scheme.ΓSpecIso K).inv ≫ (pullback.snd π (Spec.map ψ)).appLE ⊤
        (pullback.fst π (Spec.map ψ) ⁻¹ᵁ V) le_top) := by
  have h := IsPullback.of_hasPullback π (Spec.map ψ)
  have po := ((isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V)
    (UY := pullback.fst π (Spec.map ψ) ⁻¹ᵁ V) le_top
      le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
        (isAffineOpen_top _) hV))
  rw [Scheme.Hom.appLE_eq_app] at po
  refine po.of_iso (Scheme.ΓSpecIso R) (Iso.refl _) (Scheme.ΓSpecIso K) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · erw [Scheme.Hom.appLE_eq_app]
    exact Scheme.ΓSpecIso_naturality ψ
  · simp
  · simp

theorem appLE_congr {A B : Scheme.{0}} {r s : A ⟶ B} (e : r = s) (V : B.Opens) (k : ⊤ ≤ r ⁻¹ᵁ V)
    (k' : ⊤ ≤ s ⁻¹ᵁ V) (u : Γ(B, V)) : (r.appLE V ⊤ k).hom u = (s.appLE V ⊤ k').hom u := by
  subst e
  rfl

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

omit [GrpObj G] in
theorem le_comp {Y Y' : Over S} (m : Y' ⟶ Y) {k : Y ⟶ G} {V : G.left.Opens} (h : ⊤ ≤ k.left ⁻¹ᵁ V) :
    ⊤ ≤ (m ≫ k).left ⁻¹ᵁ V := m.left.preimage_mono h

theorem one_mem {V : G.left.Opens} (h : ⊤ ≤ eSec G ⁻¹ᵁ V) (Y : Over S) : ⊤ ≤ (1 : Y ⟶ G).left ⁻¹ᵁ V :=
  le_comp (toUnit Y) (k := η[G]) h

theorem inK_comp {C : Charts G.left} {a} {Y Y' : Over S} (m : Y' ⟶ Y) {k : Y ⟶ G} (h : C.InK a k) :
    C.InK a (m ≫ k) := by
  obtain ⟨h, h₁, e⟩ := h
  have e₁ : (1 : Y' ⟶ G).left = m.left ≫ (1 : Y ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  refine ⟨le_comp m h, e₁ ▸ m.left.preimage_mono h₁, fun j hj => ?_⟩
  rw [← appTop_appLE m.left k.left (m ≫ k).left rfl _ h, ← appTop_appLE m.left _ _ e₁ _ h₁, e j hj]

theorem inK_push {S' : Scheme.{0}} {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {F : G'.left ⟶ G.left} [IsAffineHom F]
    (hF : IsGrpPullback G' G f F) (C : Charts G.left) (a) {Y : Over S'} (k : Y ⟶ G') :
    (C.pull F).InK a k ↔ C.InK a (pushPt hF.1.w k) := by
  have e₁ : (1 : Over.mk (Y.hom ≫ f) ⟶ G).left = (1 : Y ⟶ G').left ≫ F :=
    (congrArg (fun z => z.left) (map_one (pushHom hF Y))).symm
  constructor
  · rintro ⟨h, h₁, e⟩
    have h₂ : ⊤ ≤ (1 : Over.mk (Y.hom ≫ f) ⟶ G).left ⁻¹ᵁ C.W a := by rw [e₁]; exact h₁
    refine ⟨h, h₂, fun j hj => ?_⟩
    exact (appLE_app k.left F _ rfl _ h h _).symm.trans ((e j hj).trans (appLE_app _ F _ e₁ _ h₁ h₂ _))
  · rintro ⟨h, h₂, e⟩
    have h₁ : ⊤ ≤ ((1 : Y ⟶ G').left ≫ F) ⁻¹ᵁ C.W a := by rw [← e₁]; exact h₂
    refine ⟨h, h₁, fun j hj => ?_⟩
    exact (appLE_app k.left F _ rfl _ h h _).trans ((e j hj).trans (appLE_app _ F _ e₁ _ h₁ h₂ _).symm)

theorem inK_torus {C : Charts G.left} {d : ℕ} {c : Fin d → C.Cl} {i : splitTorus S (Fin d → ℤ) ⟶ G}
    (hT : C.Torus c i) {a} {Y : Over S} (h₁ : ⊤ ≤ (1 : Y ⟶ G).left ⁻¹ᵁ C.W a)
    (t : Y ⟶ splitTorus S (Fin d → ℤ)) : C.InK a (t ≫ i) := by
  have h := hT.stable a Y t 1 h₁
  have e : ((t ≫ i) * 1).left = (t ≫ i).left := by rw [_root_.mul_one]
  refine ⟨e ▸ h, h₁, fun j hj => ?_⟩
  have h0 := hT.inv a j hj Y t 1 h₁ h
  rw [charUnit_zero_val, map_one, _root_.one_mul] at h0
  exact (appLE_congr e.symm _ _ _ _).trans h0

theorem exists_universal (C : Charts G.left) {a} (h₁ : ⊤ ≤ eSec G ⁻¹ᵁ C.W a) (V : G.left.Opens) :
    ∃ (E : Over S) (k₀ g₀ : E ⟶ G), IsImmersion (lift k₀ g₀).left ∧ C.InK a k₀ ∧ ⊤ ≤ g₀.left ⁻¹ᵁ V ∧
      ⊤ ≤ (k₀ * g₀).left ⁻¹ᵁ V ∧ ∀ (Y : Over S) (k g : Y ⟶ G), C.InK a k → ⊤ ≤ g.left ⁻¹ᵁ V →
        ⊤ ≤ (k * g).left ⁻¹ᵁ V → ∃ q : Y ⟶ E, q ≫ k₀ = k ∧ q ≫ g₀ = g := by
  let U : (G ⊗ G).left.Opens := (fst G G).left ⁻¹ᵁ C.W a ⊓ ((snd G G).left ⁻¹ᵁ V ⊓ (fst G G * snd G G).left ⁻¹ᵁ V)
  let X : Over S := Over.mk (U.ι ≫ (G ⊗ G).hom)
  let u : X ⟶ G ⊗ G := Over.homMk U.ι rfl
  have hu : ⊤ ≤ U.ι ⁻¹ᵁ U := U.ι_preimage_self.ge
  have k₁ : ⊤ ≤ (u ≫ fst G G).left ⁻¹ᵁ C.W a := hu.trans (U.ι.preimage_mono inf_le_left)
  have k₂ : ⊤ ≤ (u ≫ snd G G).left ⁻¹ᵁ V := hu.trans (U.ι.preimage_mono (inf_le_right.trans inf_le_left))
  have k₃ : ⊤ ≤ (u ≫ (fst G G * snd G G)).left ⁻¹ᵁ V :=
    hu.trans (U.ι.preimage_mono (inf_le_right.trans inf_le_right))
  obtain ⟨E, e, he, h, hE⟩ := exists_locus X (n := {l // C.wt l = C.c₀})
    (fun l => ((u ≫ fst G G).left.appLE _ ⊤ k₁).hom (C.r a l.1))
    (fun l => ((1 : X ⟶ G).left.appLE _ ⊤ (one_mem h₁ X)).hom (C.r a l.1))
  have one : ∀ {Y : Over S} (m : Y ⟶ X), (1 : Y ⟶ G).left = m.left ≫ (1 : X ⟶ G).left := fun m => by
    rw [← Over.comp_left, MonObj.comp_one]
  refine ⟨E, e ≫ u ≫ fst G G, e ≫ u ≫ snd G G, ?_, ⟨le_comp e k₁, one_mem h₁ E, fun j hj => ?_⟩,
    le_comp e k₂, ?_, fun Y k g hk hg hkg => ?_⟩
  · have : lift (e ≫ u ≫ fst G G) (e ≫ u ≫ snd G G) = e ≫ u := by ext1 <;> simp
    rw [this]
    exact inferInstanceAs (IsImmersion (e.left ≫ U.ι))
  · rw [← appTop_appLE e.left _ (e ≫ u ≫ fst G G).left rfl _ k₁, ← appTop_appLE e.left _ _ (one e) _ (one_mem h₁ X)]
    exact h ⟨j, hj⟩
  · rw [← MonObj.comp_mul, ← MonObj.comp_mul]
    exact le_comp e k₃
  · obtain ⟨hk, hk₁, hr⟩ := hk
    have hm : ⊤ ≤ (lift k g).left ⁻¹ᵁ U := by
      change ⊤ ≤ (lift k g ≫ fst G G).left ⁻¹ᵁ C.W a ⊓ ((lift k g ≫ snd G G).left ⁻¹ᵁ V ⊓
        (lift k g ≫ (fst G G * snd G G)).left ⁻¹ᵁ V)
      refine le_inf ?_ (le_inf ?_ ?_)
      · rwa [lift_fst]
      · rwa [lift_snd]
      · rwa [MonObj.comp_mul, lift_fst, lift_snd]
    have hr' : Set.range (lift k g).left ⊆ Set.range U.ι := by
      rintro _ ⟨y, rfl⟩
      rw [U.range_ι]
      exact hm (Set.mem_univ y)
    let m : Y ⟶ X := Over.homMk (IsOpenImmersion.lift U.ι (lift k g).left hr') (by
      change _ ≫ U.ι ≫ _ = _
      rw [IsOpenImmersion.lift_fac_assoc, Over.w])
    have hmu : m ≫ u = lift k g := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    have hmk : k.left = m.left ≫ (u ≫ fst G G).left := by
      rw [← Over.comp_left, ← Category.assoc, hmu, lift_fst]
    obtain ⟨q, hq⟩ := hE Y m fun l => by
      rw [appTop_appLE m.left _ _ hmk _ k₁ hk, appTop_appLE m.left _ _ (one m) _ (one_mem h₁ X) hk₁]
      exact hr l.1 l.2
    exact ⟨q, by rw [← Category.assoc, hq, ← Category.assoc, hmu, lift_fst],
      by rw [← Category.assoc, hq, ← Category.assoc, hmu, lift_snd]⟩

end

theorem range_jK (R : Type) [CommRing R] [IsDomain R] :
    Set.range (Out.jK R) = {(⊥ : PrimeSpectrum R)} := by
  have key : ∀ y, Out.jK R y = (⊥ : PrimeSpectrum R) := fun y => by
    apply PrimeSpectrum.ext
    obtain rfl : y = (⊥ : PrimeSpectrum (FractionRing R)) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact key y
  · rintro rfl
    exact ⟨(⊥ : PrimeSpectrum (FractionRing R)), key _⟩

theorem pull_eq {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {F : G'.left ⟶ G.left} [IsAffineHom F] (hF : IsGrpPullback G' G f F) (C : Charts G.left) {a}
    (V : G.left.Opens) (x : Γ(G.left, V))
    (H : ∀ (Y : Over S') (k g : Y ⟶ G'), (C.pull F).InK a k → ∀ h h',
      ((k * g).left.appLE (F ⁻¹ᵁ V) ⊤ h').hom ((F.app V).hom x) =
        (g.left.appLE (F ⁻¹ᵁ V) ⊤ h).hom ((F.app V).hom x))
    {E : Over S} {k₀ g₀ : E ⟶ G} (hk₀ : C.InK a k₀) (hg₀ : ⊤ ≤ g₀.left ⁻¹ᵁ V) (hm₀ : ⊤ ≤ (k₀ * g₀).left ⁻¹ᵁ V) :
    (pullback.fst E.hom f).appTop.hom (((k₀ * g₀).left.appLE V ⊤ hm₀).hom x) =
      (pullback.fst E.hom f).appTop.hom ((g₀.left.appLE V ⊤ hg₀).hom x) := by
  let Y : Over S' := Over.mk (pullback.snd E.hom f)
  let p : Over.mk (Y.hom ≫ f) ⟶ E := Over.homMk (pullback.fst E.hom f) pullback.condition
  have A : ∀ z : E ⟶ G, ∃ z' : Y ⟶ G', (p ≫ z).left = z'.left ≫ F := fun z =>
    ⟨Over.homMk (hF.1.lift _ _ (Over.w (p ≫ z))) (hF.1.lift_snd _ _ _), (hF.1.lift_fst _ _ _).symm⟩
  obtain ⟨k, Ak⟩ := A k₀
  obtain ⟨g, Ag⟩ := A g₀
  have hk : pushPt hF.1.w k = p ≫ k₀ := Over.OverMorphism.ext Ak.symm
  have hm := hF.2 Y _ _ _ _ Ak Ag
  rw [← MonObj.comp_mul] at hm
  have l₁ := le_comp p hg₀
  have l₂ := le_comp p hm₀
  have l₁' := l₁
  have l₂' := l₂
  rw [Ag] at l₁'
  rw [hm] at l₂'
  have h0 := H Y k g ((inK_push hF C a _).2 (hk ▸ inK_comp p hk₀)) l₁' l₂'
  exact (appTop_appLE p.left _ _ rfl V hm₀ l₂ x).trans <| (appLE_app _ _ _ hm V l₂' l₂ x).symm.trans <|
    h0.trans <| (appLE_app _ _ _ Ag V l₁' l₁ x).trans (appTop_appLE p.left _ _ rfl V hg₀ l₁ x).symm

theorem exists_scal_mul_inv {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {G : Over (Sp R)} [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (C : Charts G.left)
    [IsAffineHom (pullback.fst G.hom (Out.jK R))] {a} (h₁ : ⊤ ≤ eSec G ⁻¹ᵁ C.W a) (V : G.left.Opens)
    (x : Γ(G.left, V))
    (H : ∀ (Y : Over (Sp (FractionRing R))) (k g : Y ⟶ (Over.pullback (Out.jK R)).obj G),
      Charts.InK (H := (Over.pullback (Out.jK R)).obj G) (C.pull (pullback.fst G.hom (Out.jK R))) a k →
      ∀ h h', ((k * g).left.appLE (pullback.fst G.hom (Out.jK R) ⁻¹ᵁ V) ⊤ h').hom
          (((pullback.fst G.hom (Out.jK R)).app V).hom x) =
        (g.left.appLE (pullback.fst G.hom (Out.jK R) ⁻¹ᵁ V) ⊤ h).hom
          (((pullback.fst G.hom (Out.jK R)).app V).hom x)) :
    ∃ b : R, b ≠ 0 ∧ ∀ (Y : Over (Sp R)) (k g : Y ⟶ G), C.InK a k → ∀ h h',
      Out.scal Y.hom b * (((k * g).left.appLE V ⊤ h').hom x - (g.left.appLE V ⊤ h).hom x) = 0 := by
  obtain ⟨E, k₀, g₀, him, hk₀, hg₀, hm₀, hE⟩ := exists_universal C h₁ V
  have i₁ : LocallyOfFiniteType (G ⊗ G).hom := inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G.hom ≫ G.hom))
  have i₂ : QuasiCompact (G ⊗ G).hom := inferInstanceAs (QuasiCompact (pullback.fst G.hom G.hom ≫ G.hom))
  have : IsLocallyNoetherian (G ⊗ G).left := LocallyOfFiniteType.isLocallyNoetherian (G ⊗ G).hom
  have : CompactSpace (G ⊗ G).left := QuasiCompact.compactSpace_of_compactSpace (G ⊗ G).hom
  have : IsNoetherian (G ⊗ G).left := {}
  have : TopologicalSpace.NoetherianSpace E.left := (lift k₀ g₀).left.isEmbedding.isInducing.noetherianSpace
  have : LocallyOfFiniteType E.hom := by rw [← Over.w (lift k₀ g₀)]; infer_instance
  have : QuasiCompact E.hom := ⟨fun U _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hD : Dense ({(⊥ : PrimeSpectrum R)} : Set (Sp R)) := by
    change Dense ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R))
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  obtain ⟨b, hb0, hb⟩ := GenericEq.exists_scal_mul_eq_zero R E _ hD
    (((k₀ * g₀).left.appLE V ⊤ hm₀).hom x - (g₀.left.appLE V ⊤ hg₀).hom x) (by
    rintro _ rfl
    refine ⟨FractionRing R, inferInstance, Out.jK R, range_jK R, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact pull_eq (isGrpPullback_pullback G (Out.jK R)) C V x H hk₀ hg₀ hm₀)
  refine ⟨b, hb0, fun Y k g hk h h' => ?_⟩
  obtain ⟨q, rfl, rfl⟩ := hE Y k g hk h h'
  have h0 := congrArg q.left.appTop.hom hb
  rw [map_mul, map_zero, map_sub, GenericEq.appTop_scal, Over.w,
    appTop_appLE q.left _ (q ≫ g₀).left rfl V hg₀ h,
    appTop_appLE q.left _ ((q ≫ k₀) * (q ≫ g₀)).left (by rw [← MonObj.comp_mul]; rfl) V hm₀ h'] at h0
  exact h0

theorem hasWt_fibre {R K : Type} [CommRing R] [Field K] {G : Over (Sp R)} [GrpObj G] (C : Charts G.left)
    (ψ : CommRingCat.of R ⟶ CommRingCat.of K) [IsAffineHom (pullback.fst G.hom (Spec.map ψ))]
    {a} (h₁ : ⊤ ≤ eSec G ⁻¹ᵁ C.W a) {V : G.left.Opens} {x : Γ(G.left, V)} {b : R} (hb : ψ.hom b ≠ 0)
    (H : ∀ (Y : Over (Sp R)) (k g : Y ⟶ G), C.InK a k → ∀ h h',
      Out.scal Y.hom b * (((k * g).left.appLE V ⊤ h').hom x - (g.left.appLE V ⊤ h).hom x) = 0)
    {d : ℕ} {c : Fin d → C.Cl} {i : splitTorus (Sp K) (Fin d → ℤ) ⟶ (Over.pullback (Spec.map ψ)).obj G}
    (hT : Charts.Torus (H := (Over.pullback (Spec.map ψ)).obj G) (C.pull (pullback.fst G.hom (Spec.map ψ))) c i) :
    HasWt i (pullback.fst G.hom (Spec.map ψ) ⁻¹ᵁ V) (((pullback.fst G.hom (Spec.map ψ)).app V).hom x) 0 := by
  intro Y t g h h'
  have hF := isGrpPullback_pullback G (Spec.map ψ)
  have e₁ : (1 : Over.mk (Y.hom ≫ Spec.map ψ) ⟶ G).left =
      (1 : Y ⟶ (Over.pullback (Spec.map ψ)).obj G).left ≫ pullback.fst G.hom (Spec.map ψ) :=
    (congrArg (fun z => z.left) (map_one (pushHom hF Y))).symm
  have o := one_mem h₁ (Over.mk (Y.hom ≫ Spec.map ψ))
  rw [e₁] at o
  have hk := (inK_push hF C a _).1 (inK_torus hT (a := a) o t)
  have hm := hF.2 Y (t ≫ i) g (pushPt hF.1.w (t ≫ i)) (pushPt hF.1.w g) rfl rfl
  have l : ⊤ ≤ (pushPt hF.1.w (t ≫ i) * pushPt hF.1.w g).left ⁻¹ᵁ V := by rw [hm]; exact h'
  have h0 := H _ _ (pushPt hF.1.w g) hk h l
  have hu : IsUnit (Out.scal (Y.hom ≫ Spec.map ψ) b) := by
    rw [← GenericEq.appTop_scal]
    refine IsUnit.map _ ?_
    have n := congrArg (fun k => k.hom b) (Scheme.ΓSpecIso_inv_naturality ψ)
    exact (show Out.scal (Spec.map ψ) b = _ from n.symm) ▸ hb.isUnit.map (Scheme.ΓSpecIso (.of K)).inv.hom
  rw [charUnit_zero_val, map_one, _root_.one_mul]
  exact (appLE_app _ _ _ hm V h' l x).trans <| (sub_eq_zero.1 (hu.mul_right_eq_zero.1 h0)).trans
    (appLE_app g.left _ (pushPt hF.1.w g).left rfl V h h x).symm

theorem generic_invariants : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → (∀ a', Stable i ((C.pull (pullback.fst G.hom (Out.jK R))).W a')) → ∀ a' (u : Γ(((Over.pullback (Out.jK R)).obj G).left, (C.pull (pullback.fst G.hom (Out.jK R))).W a')), HasWt i _ u 0 → u ∈ Subring.closure (Set.range (((Over.pullback (Out.jK R)).obj G).hom.appLE ⊤ ((C.pull (pullback.fst G.hom (Out.jK R))).W a') le_top).hom ∪ {v | ∃ j', C.wt j' = C.c₀ ∧ v = (C.pull (pullback.fst G.hom (Out.jK R))).r a' j'}) := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS a j hB i hi _ a' u hu
  change Γ(pullback G.hom (Out.jK R), pullback.fst G.hom (Out.jK R) ⁻¹ᵁ C.W a') at u
  let φ : CommRingCat.of R ⟶ Γ(G.left, C.W a') := (Scheme.ΓSpecIso (.of R)).inv ≫ G.hom.appLE ⊤ (C.W a') le_top
  letI : Algebra R Γ(G.left, C.W a') := φ.hom.toAlgebra
  have : Algebra.FiniteType R Γ(G.left, C.W a') :=
    (G.hom.finiteType_appLE (isAffineOpen_top _) (C.aff a') le_top).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2)
  have po := isPushout_sections (CommRingCat.ofHom (algebraMap R (FractionRing R))) G.hom (C.aff a')
  obtain ⟨s, x, hs, hx⟩ := exists_clear po u
  set p := (pullback.fst G.hom (Out.jK R)).app (C.W a') with hp
  set q := (pullback.snd G.hom (Out.jK R)).appLE ⊤ (pullback.fst G.hom (Out.jK R) ⁻¹ᵁ C.W a') le_top with hq
  have hw : ∀ r : R, p.hom (φ.hom r) =
      q.hom ((Scheme.ΓSpecIso (.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r)) :=
    fun r => congrArg (fun k => k.hom r) po.w
  change p.hom (φ.hom s) * u = p.hom x at hx
  obtain ⟨b, hb0, hb⟩ := exists_scal_mul_inv C hB.1 (C.W a') x (by
    intro Y k g hk h h'
    obtain ⟨t, rfl⟩ := (hi.2.1 Y k).1 hk
    have h0 := hu Y t g h h'
    rw [charUnit_zero_val, map_one, _root_.one_mul] at h0
    have e : ∀ (z : Y ⟶ (Over.pullback (Out.jK R)).obj G) hz v,
        (z.left.appLE (pullback.fst G.hom (Out.jK R) ⁻¹ᵁ C.W a') ⊤ hz).hom (q.hom v) = Y.hom.appTop.hom v :=
      fun z hz v => appLE_appLE_top _ _ _ (Over.w z) _ _ _
    rw [← hp, ← hx, hw, map_mul, map_mul]
    exact congrArg₂ (· * ·) ((e _ _ _).trans (e _ _ _).symm) h0)
  let T : Set Γ(G.left, C.W a') := Set.range fun l : {l // C.wt l = C.c₀} => C.r a' l.1
  obtain ⟨r, hr0, hr⟩ := exists_smul_mem_of_dense_fibres R Γ(G.left, C.W a') (Algebra.adjoin R T) x
    (Sg ∩ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum R)))
    (Subalgebra.fg_def.2 ⟨T, Set.finite_range _, rfl⟩)
    (Dense.inter_of_isOpen_right (X := PrimeSpectrum R) hD
      ((PrimeSpectrum.basicOpen b).isOpen.dense ⟨⊥, hb0⟩) (PrimeSpectrum.basicOpen b).isOpen) (by
    rintro P ⟨hP, hPb⟩
    obtain ⟨K, _, t, _, ht, -, i', hT⟩ := hS P hP
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
    letI : Algebra R K := ψ.hom.toAlgebra
    have hker : RingHom.ker (algebraMap R K) = P.asIdeal := by
      have : Spec.map ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = P := ht.le (Set.mem_range_self _)
      rw [← this]
      rfl
    refine ⟨K, inferInstance, inferInstance, hker, ?_⟩
    have hg := hT.gen a' _ (hasWt_fibre C ψ hB.1 (fun e => hPb (hker.le e)) hb hT)
    refine one_tmul_mem_range (isPushout_sections ψ G.hom (C.aff a')) T x (Subring.closure_mono ?_ hg)
    rintro _ (⟨w, rfl⟩ | ⟨l, hl, rfl⟩)
    · refine Or.inl ⟨(Scheme.ΓSpecIso (.of K)).hom.hom w, ?_⟩
      rw [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply]
      rfl
    · exact Or.inr ⟨_, ⟨⟨l, hl⟩, rfl⟩, rfl⟩)
  set B := Subring.closure (Set.range q.hom ∪ {v | ∃ j', C.wt j' = C.c₀ ∧ v = p.hom (C.r a' j')}) with hBdef
  change u ∈ B
  have h1 : ∀ y ∈ Algebra.adjoin R T, p.hom y ∈ B := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      exact Subring.subset_closure (Or.inr ⟨l.1, l.2, rfl⟩)
    | algebraMap r => exact Subring.subset_closure (Or.inl ⟨_, (hw r).symm⟩)
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact B.add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact B.mul_mem hy hz
  have h2 := h1 _ hr
  have hne : algebraMap R (FractionRing R) (r * s) ≠ 0 := fun e =>
    mul_ne_zero hr0 hs ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective R (FractionRing R)) _ e)
  have h3 : u = q.hom ((Scheme.ΓSpecIso (.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) (r * s))⁻¹) *
      p.hom (r • x) := by
    rw [Algebra.smul_def, map_mul p.hom, ← hx, ← _root_.mul_assoc, ← _root_.mul_assoc]
    change u = _ * p.hom (φ.hom r) * _ * _
    rw [hw, hw, ← map_mul q.hom, ← map_mul q.hom, ← map_mul, ← map_mul, _root_.mul_assoc _⁻¹, ← map_mul, inv_mul_cancel₀ hne,
      map_one, map_one, _root_.one_mul]
  rw [h3]
  exact B.mul_mem (Subring.subset_closure (Or.inl ⟨_, rfl⟩)) h2

end GlobalTheory.ZJ.GenericInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericInvariantsGeneratedByRatiosStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_invariants_generated_by_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → (∀ a', Stable i ((C.pull (pullback.fst G.hom (Out.jK R))).W a')) → ∀ a' (u : Γ(((Over.pullback (Out.jK R)).obj G).left, (C.pull (pullback.fst G.hom (Out.jK R))).W a')), HasWt i _ u 0 → u ∈ Subring.closure (Set.range (((Over.pullback (Out.jK R)).obj G).hom.appLE ⊤ ((C.pull (pullback.fst G.hom (Out.jK R))).W a') le_top).hom ∪ {v | ∃ j', C.wt j' = C.c₀ ∧ v = (C.pull (pullback.fst G.hom (Out.jK R))).r a' j'}) := by
  first | exact @GlobalTheory.ZJ.GenericInv.generic_invariants | exact GlobalTheory.ZJ.GenericInv.generic_invariants | (intros; apply GlobalTheory.ZJ.GenericInv.generic_invariants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitGenericOfBasedWeightedCharts
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Charts.split_generic_of_based : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → Charts.Split (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) c := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS a j hB
  obtain ⟨i, hi⟩ := GlobalTheory.T.exists_splitTorus_kernel_genericFibre R G C d c Sg hD hS a j hB
  obtain ⟨hst, hinv, hwt⟩ := GlobalTheory.T.torusStable_weights_genericFibre R G C d c Sg hD hS a j hB i hi
  obtain ⟨hc, hb⟩ := GlobalTheory.T.geometricallyConnected_basePointFree_generic_fibre R G C d c Sg hD hS
  exact ⟨hc, i, GlobalTheory.T.isMonHom_generic_fibre_kernel_torus R G C d c Sg hD hS a j hB i hi, hst, hinv, hwt, hb,
    GlobalTheory.T.generic_invariants_generated_by_ratios R G C d c Sg hD hS a j hB i hi hst⟩
end GlobalTheory.ZJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitGenericOfBasedWeightedChartsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_generic_of_based_weightedCharts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → Charts.Split (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) c := by
  first | exact @GlobalTheory.ZJ.Charts.split_generic_of_based | exact GlobalTheory.ZJ.Charts.split_generic_of_based | (intros; apply GlobalTheory.ZJ.Charts.split_generic_of_based <;> assumption)
end
