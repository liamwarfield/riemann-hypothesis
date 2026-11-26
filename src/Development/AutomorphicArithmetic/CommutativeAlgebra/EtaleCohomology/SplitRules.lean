module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitRules
noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

def SplitOn {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) {m : ℕ} (z : Fin m → (X ⟶ Z)) : Prop :=
  ∃ h : ∀ i, z i ≫ p = x, IsIso (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [h i, Category.id_comp])) :
    ∐ (fun _ : Fin m => X) ⟶ pullback p x)

abbrev awayPt (l : ℕ) (U : Type) [CommRing U] : Spec (CommRingCat.of (Localization.Away (l : U))) ⟶ Spec (CommRingCat.of U) :=
  Spec.map (CommRingCat.ofHom (algebraMap U (Localization.Away (l : U))))

structure WDat (l : ℕ) {Y : Scheme.{0}} {J : Type} (T : J → Corr l Y) : Type 1 where
  W : Scheme.{0}
  π : W ⟶ Y
  s : ∀ j, Fin (T j).d → (W ⟶ (T j).Z)
  hs : ∀ j i, s j i ≫ (T j).p = π
  gen : ∀ (X : Scheme.{0}) (w : X ⟶ W), IsUnit (l : Γ(X, ⊤)) → ∀ j, SplitOn (T j).p (w ≫ π) fun i => w ≫ s j i
  univ : ∀ (U : Type) [CommRing U], (l : U) ∈ nonZeroDivisors U → ∀ (y : Spec (CommRingCat.of U) ⟶ Y)
    (z : ∀ j, Fin (T j).d → (Spec (CommRingCat.of U) ⟶ (T j).Z)), (∀ j i, z j i ≫ (T j).p = y) →
    (∀ j, SplitOn (T j).p (awayPt l U ≫ y) fun i => awayPt l U ≫ z j i) →
    ∃! w : Spec (CommRingCat.of U) ⟶ W, w ≫ π = y ∧ ∀ j i, w ≫ s j i = z j i

def WEx : Prop := ∀ (l : ℕ) (Y : Scheme.{0}) (J : Type) [Fintype J] (T : J → Corr l Y), Nonempty (WDat l T)

def SplitEx : Prop := ∀ (l : ℕ), l.Prime → ∀ (Y : Scheme.{0}) (T : Corr l Y) (U : Type) [CommRing U], (l : U) ∈ nonZeroDivisors U →
  (∀ x : Localization.Away (l : U), IsIntegral U x → ∃ u : U, algebraMap U _ u = x) →
  (∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of (Localization.Away (l : U)))), Etale f → Surjective f → ∃ s, s ≫ f = 𝟙 _) →
  ∀ y : Spec (CommRingCat.of U) ⟶ Y, ∃ z : Fin T.d → (Spec (CommRingCat.of U) ⟶ T.Z), (∀ i, z i ≫ T.p = y) ∧
    SplitOn T.p (awayPt l U ≫ y) fun i => awayPt l U ≫ z i

def SplitPerm : Prop := ∀ (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (U : Type) [CommRing U], (l : U) ∈ nonZeroDivisors U →
  (∀ x : Localization.Away (l : U), IsIntegral U x → ∃ u : U, algebraMap U _ u = x) →
  ∀ (y : Spec (CommRingCat.of U) ⟶ Y) (z z' : Fin T.d → (Spec (CommRingCat.of U) ⟶ T.Z)), (∀ i, z i ≫ T.p = y) → (∀ i, z' i ≫ T.p = y) →
  (SplitOn T.p (awayPt l U ≫ y) fun i => awayPt l U ≫ z i) → (SplitOn T.p (awayPt l U ≫ y) fun i => awayPt l U ≫ z' i) →
  ∃ e : Equiv.Perm (Fin T.d) → U, CompleteOrthogonalIdempotents e ∧ ∀ (σ : Equiv.Perm (Fin T.d)) (V : Type) [CommRing V] (ρ : U →+* V),
    ρ (e σ) = 1 → ∀ i, Spec.map (CommRingCat.ofHom ρ) ≫ z' i = Spec.map (CommRingCat.ofHom ρ) ≫ z (σ i)

def SplitRules : Prop :=
  (∀ {X' X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) (g : X' ⟶ X) {m : ℕ} (z : Fin m → (X ⟶ Z)), SplitOn p x z →
    (SplitOn p (g ≫ x) fun i => g ≫ z i) ∧ ∀ σ : Equiv.Perm (Fin m), SplitOn p x fun i => z (σ i)) ∧
  ∀ (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (U : Y.Opens), IsAffineOpen U → ∀ (B : Type) [CommRing B]
    (y : Spec (CommRingCat.of B) ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U) (z : Fin T.d → (Spec (CommRingCat.of B) ⟶ T.Z))
    (hz : ∀ i, ⊤ ≤ z i ⁻¹ᵁ (T.p ⁻¹ᵁ U)), (∀ i, z i ≫ T.p = y) → (SplitOn T.p (awayPt l B ≫ y) fun i => awayPt l B ≫ z i) →
    letI := T.alg U
    letI : Algebra Γ(Y, U) B := ((y.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom).toAlgebra
    ∃ ζ : Fin T.d → (Γ(T.Z, T.p ⁻¹ᵁ U) →ₐ[Γ(Y, U)] B), SplitsAway l ζ ∧
      ∀ i a, ζ i a = ((z i).appLE (T.p ⁻¹ᵁ U) ⊤ (hz i) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom a

end UpperTheory.Ru.crystallineComparison
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EvalExact
open CategoryTheory

namespace UpperTheory.Ru.crystallineComparison

private lemma evalExact {C : Type 1} [Category.{0} C] (S : ShortComplex (Coef C))
    (h : S.ShortExact) (B : C) :
    Function.Exact (S.f.app B).hom (S.g.app B).hom ∧
      Function.Injective (S.f.app B).hom ∧ Function.Surjective (S.g.app B).hom := by
  have hB := h.map_of_exact ((evaluation C AddCommGrpCat.{1}).obj B)
  have hm := hB.mono_f
  have he := hB.epi_g
  exact ⟨(ShortComplex.ab_exact_iff_function_exact _).1 hB.exact,
    (AddCommGrpCat.mono_iff_injective _).1 hm, (AddCommGrpCat.epi_iff_surjective _).1 he⟩

end UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.quotAdd :
    UpperTheory.Ru.crystallineComparison.QuotAdd := by
  intro C _ Pa S hS h1 h2 A T hT
  have ex := fun B => UpperTheory.Ru.crystallineComparison.evalExact S hS B
  have natf : ∀ (i : T.ι) (z : S.X₁.obj A),
      (S.f.app (T.B i)).hom ((S.X₁.map (T.f i)).hom z) =
        (S.X₂.map (T.f i)).hom ((S.f.app A).hom z) := by
    intro i z
    have := congrArg (fun φ => φ.hom z) (S.f.naturality (T.f i))
    simpa using this
  have natg : ∀ (i : T.ι) (y : S.X₂.obj A),
      (S.g.app (T.B i)).hom ((S.X₂.map (T.f i)).hom y) =
        (S.X₃.map (T.f i)).hom ((S.g.app A).hom y) := by
    intro i y
    have := congrArg (fun φ => φ.hom y) (S.g.naturality (T.f i))
    simpa using this
  have inj0 : ∀ x : S.X₃.obj A, (∀ i, (S.X₃.map (T.f i)).hom x = 0) → x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := (ex A).2.2 x
    have hz : ∀ i, ∃ z : S.X₁.obj (T.B i),
        (S.f.app (T.B i)).hom z = (S.X₂.map (T.f i)).hom y := by
      intro i
      have : (S.g.app (T.B i)).hom ((S.X₂.map (T.f i)).hom y) = 0 := by
        rw [natg]; exact hx i
      exact ((ex (T.B i)).1 _).1 this
    choose z hz using hz
    obtain ⟨w, hw⟩ := (h1 A T hT).2 z
    have hy : y = (S.f.app A).hom w := by
      apply (h2 A T hT).1
      funext i
      show (S.X₂.map (T.f i)).hom y = (S.X₂.map (T.f i)).hom ((S.f.app A).hom w)
      rw [← natf, ← hz i]
      exact congrArg _ (congrFun hw i).symm
    rw [hy]
    exact ((ex A).1 _).2 ⟨w, rfl⟩
  constructor
  · intro x x' e
    rw [← sub_eq_zero]
    apply inj0
    intro i
    have := congrFun e i
    simp only at this
    rw [map_sub, this, sub_self]
  · intro v
    have hy : ∀ i, ∃ y : S.X₂.obj (T.B i), (S.g.app (T.B i)).hom y = v i :=
      fun i => (ex (T.B i)).2.2 (v i)
    choose y hy using hy
    obtain ⟨w, hw⟩ := (h2 A T hT).2 y
    refine ⟨(S.g.app A).hom w, ?_⟩
    funext i
    show (S.X₃.map (T.f i)).hom ((S.g.app A).hom w) = v i
    rw [← natg, ← hy i]
    exact congrArg _ (congrFun hw i)
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AddIff
noncomputable section

open CategoryTheory Opposite

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

private def pre {A : C} (S : Fam A) : Presieve (op A : Cᵒᵖ) :=
  Presieve.ofArrows (fun i => op (S.B i)) (fun i => (S.f i).op)

private def cov (Pa : Parts C) : Coverage Cᵒᵖ where
  coverings X := {R | ∃ S : Fam X.unop, Pa.Cov S ∧ R = pre S}
  pullback := by
    rintro X Y f R ⟨S, hS, rfl⟩
    obtain ⟨B', f', ψ, hc, hcomm⟩ := Pa.pull f.unop S hS
    refine ⟨_, ⟨⟨S.ι, B', f'⟩, hc, rfl⟩, ?_⟩
    rintro Z g ⟨i⟩
    refine ⟨op (S.B i), (ψ i).op, (S.f i).op, Presieve.ofArrows.mk i, ?_⟩
    apply Quiver.Hom.unop_inj
    simpa using hcomm i

private abbrev Jt (Pa : Parts C) : GrothendieckTopology Cᵒᵖ := (cov Pa).toGrothendieck

private theorem add_iff (Pa : Parts C) (F : Coef C) :
    Pa.Add F ↔ Presheaf.IsSheaf (Jt Pa) (unopUnop C ⋙ F) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat.{1}),
    isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
  constructor
  · rintro h X R ⟨S, hS, rfl⟩
    refine (Presieve.isSheafFor_arrows_iff _ _).2 fun x _ => ?_
    obtain ⟨t, ht⟩ := (h _ S hS).2 x
    exact ⟨t, fun i => congrFun ht i,
      fun t' ht' => (h _ S hS).1 (funext fun i => (ht' i).trans (congrFun ht i).symm)⟩
  · intro h A S hS
    have arrows : ∀ {X : C} (S : Fam X), Pa.Cov S → ∀ x : ∀ i, F.obj (S.B i),
        Presieve.Arrows.Compatible ((unopUnop C ⋙ F) ⋙ forget AddCommGrpCat.{1})
          (fun i => (S.f i).op) x → ∃! t, ∀ i, (F.map (S.f i)).hom t = x i :=
      fun {X} S hS x hx =>
        (Presieve.isSheafFor_arrows_iff _ _).1 (h (X := op X) (pre S) ⟨S, hS, rfl⟩) x hx
    have sub : ∀ X : C, Pa.Cov (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam X) →
        Subsingleton (F.obj X) := fun X hX => ⟨fun a b =>
      (arrows _ hX (fun e => e.elim) (fun e => e.elim)).unique (fun e => e.elim) (fun e => e.elim)⟩
    have compat : ∀ x : ∀ i, F.obj (S.B i),
        Presieve.Arrows.Compatible ((unopUnop C ⋙ F) ⋙ forget AddCommGrpCat.{1})
          (fun i => (S.f i).op) x := by
      intro x i j Z gi gj e
      have e' : S.f i ≫ gi.unop = S.f j ≫ gj.unop := congrArg Quiver.Hom.unop e
      by_cases hij : i = j
      · subst hij
        have : gi.unop = gj.unop := (Pa.epi S hS i).left_cancellation _ _ e'
        rw [Quiver.Hom.unop_inj this]
      · have := sub _ (Pa.disj S hS hij gi.unop gj.unop e')
        exact Subsingleton.elim (α := F.obj Z.unop) _ _
    constructor
    · intro a b hab
      exact (arrows S hS _ (compat fun i => (F.map (S.f i)).hom a)).unique (fun i => rfl)
        (fun i => (congrFun hab i).symm)
    · intro x
      obtain ⟨t, ht, -⟩ := arrows S hS x (compat x)
      exact ⟨t, funext ht⟩

private theorem enough (Pa : Parts C) : EnoughInjectives (Sheaf (Jt Pa) AddCommGrpCat.{1}) :=
  haveI : EssentiallySmall.{1} Cᵒᵖ := essentiallySmall_of_small_of_locallySmall _
  haveI : IsGrothendieckAbelian.{1} (Sheaf (Jt Pa) AddCommGrpCat.{1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  inferInstance

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.emb :
    UpperTheory.Ru.crystallineComparison.Emb := by
  intro C _ Pa F hF
  haveI := enough Pa
  let Fs : Sheaf (Jt Pa) AddCommGrpCat.{1} := ⟨unopUnop C ⋙ F, (add_iff Pa F).1 hF⟩
  let I := Injective.under Fs
  let G := (sheafToPresheaf (Jt Pa) AddCommGrpCat.{1}).obj I
  have hG : Presheaf.IsSheaf (Jt Pa) G := I.property
  haveI inj : Injective G :=
    Injective.injective_of_adjoint (sheafificationAdjunction (Jt Pa) AddCommGrpCat.{1}) I
  let m := (sheafToPresheaf (Jt Pa) AddCommGrpCat.{1}).map (Injective.ι Fs)
  have hm : Mono m := inferInstance
  refine ⟨opOp C ⋙ G, { app := fun X => m.app (op (op X)), naturality := fun X Y f => m.naturality f.op.op }, ?_, ?_, ?_⟩
  · rw [NatTrans.mono_iff_mono_app]
    intro X
    exact (NatTrans.mono_iff_mono_app m).1 hm _
  · exact Injective.injective_of_adjoint
      ((opOpEquivalence C).congrLeft (E := AddCommGrpCat.{1})).symm.toAdjunction G
  · exact (add_iff Pa _).2 hG
end
end
