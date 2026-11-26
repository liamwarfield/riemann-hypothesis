module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicOfSectionsOfVeryAmple
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G G' T T' : Over S} [GrpObj G] [GrpObj G']

def lam (c : Pic G.left) (x y : T ⟶ G) : Pic T.left :=
  pull (x * y).left c - pull x.left c - pull y.left c + pull (1 : T ⟶ G).left c

theorem cls_cube_two {L : LB G.left} (hL : L.IsLB) (x y : T ⟶ G) (h : (cubeLB G ![x, y] L).IsLB) :
    cls _ h = lam (cls L hL) x y := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.sum_comp Equiv.ulift.symm,
    show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e : ((-1 : ℤ) ^ 2) • pull (1 : T ⟶ G).left (cls L hL) + (((-1 : ℤ) ^ 1) • pull (x * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (y * 1).left (cls L hL) + ((-1 : ℤ) ^ 0) • pull (x * (y * 1)).left (cls L hL))) =
      lam (cls L hL) x y := by
    simp only [_root_.mul_one, lam]
    norm_num
    abel
  exact e

theorem cls_cube_three [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (x y z : T ⟶ G)
    (h : (cubeLB G ![x, y, z] L).IsLB) :
    cls _ h = lam (cls L hL) (x * y) z - lam (cls L hL) x z - lam (cls L hL) y z := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.sum_comp Equiv.ulift.symm,
    show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have e : ((-1 : ℤ) ^ 3) • pull (1 : T ⟶ G).left (cls L hL) + (((-1 : ℤ) ^ 2) • pull (x * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 2) • pull (y * 1).left (cls L hL) + (((-1 : ℤ) ^ 2) • pull (z * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (x * (y * 1)).left (cls L hL) + (((-1 : ℤ) ^ 1) • pull (x * (z * 1)).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (y * (z * 1)).left (cls L hL) +
        ((-1 : ℤ) ^ 0) • pull (x * (y * (z * 1))).left (cls L hL))))))) =
      lam (cls L hL) (x * y) z - lam (cls L hL) x z - lam (cls L hL) y z := by
    simp only [_root_.mul_one, lam, _root_.mul_assoc]
    norm_num
    abel
  exact e

theorem pull_lam (h : T' ⟶ T) (c : Pic G.left) (x y : T ⟶ G) :
    pull h.left (lam c x y) = lam c (h ≫ x) (h ≫ y) := by
  simp only [lam, map_add (f := _), map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul, MonObj.comp_one]

theorem lam_pull (ψ : G ⟶ G') [IsMonHom ψ] (c : Pic G'.left) (x y : T ⟶ G) :
    lam (pull ψ.left c) x y = lam c (x ≫ ψ) (y ≫ ψ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, MonObj.mul_comp, MonObj.one_comp]

theorem lam_nsmul (n : ℕ) (c : Pic G.left) (x y : T ⟶ G) : lam (n • c) x y = n • lam c x y := by
  simp only [lam, map_nsmul, nsmul_add, nsmul_sub]

theorem lam_one_left (c : Pic G.left) (y : T ⟶ G) : lam c 1 y = 0 := by
  simp only [lam, _root_.one_mul]; abel

theorem lam_one_right (c : Pic G.left) (x : T ⟶ G) : lam c x 1 = 0 := by
  simp only [lam, _root_.mul_one]; abel

variable [IsCommMonObj G]

theorem lam_comm (c : Pic G.left) (x y : T ⟶ G) : lam c x y = lam c y x := by
  simp only [lam, _root_.mul_comm x y]; abel

theorem lam_mul_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y z : T ⟶ G) :
    lam (cls L hL) (x * y) z = lam (cls L hL) x z + lam (cls L hL) y z := by
  have h₀ := (cls_eq_zero_iff (N := Theta G L) (LB.isLB_linComb hL _ _)).2 hΘ
  have h₁ := (cls_cube_three hL (fst _ _) (snd _ _ ≫ fst _ _) (snd G (G ⊗ G) ≫ snd _ _)
    (LB.isLB_linComb hL _ _)).symm.trans h₀
  have h₂ := congrArg (pull (lift x (lift y z)).left) h₁
  simp only [map_sub, map_zero, pull_lam, MonObj.comp_mul, lift_fst, lift_snd_assoc, lift_snd] at h₂
  rw [sub_sub, sub_eq_zero] at h₂
  exact h₂

theorem lam_pow_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℕ) :
    lam (cls L hL) (x ^ n) z = n • lam (cls L hL) x z := by
  induction n with
  | zero => rw [pow_zero, lam_one_left, zero_nsmul]
  | succ n ih => rw [pow_succ, lam_mul_left hL hΘ, ih, succ_nsmul]

theorem lam_pow_right {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℕ) :
    lam (cls L hL) x (z ^ n) = n • lam (cls L hL) x z := by
  rw [lam_comm, lam_pow_left hL hΘ, lam_comm]

theorem sym_of_isSymmetric (L : RigLB G) (h : L.IsSymmetric) : Out.Sym G L.L := by
  obtain ⟨_, w, hw, -⟩ := h
  have e := (cls_eq_iff L.isLB (pull_isLB L.isLB _)).2 ⟨w, hw⟩
  rw [cls_pull L.isLB] at e
  refine fun s => ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb L.isLB _ _)).1 ?_⟩
  rw [cls_linComb L.isLB, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, ← e, one_smul, neg_smul, add_neg_cancel]

end Pairing

theorem dense_image_points {k : Type} [Field k] [IsAlgClosed k] {A B : Over (Sp k)} [LocallyOfFiniteType A.hom]
    (f : A ⟶ B) [Surjective f.left] (P : Set (𝟙_ (Over (Sp k)) ⟶ B)) (hP : ∀ u : 𝟙_ (Over (Sp k)) ⟶ A, u ≫ f ∈ P) :
    Dense (⋃ x ∈ P, Set.range x.left) := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hd : Dense (closedPoints A.left) := dense_iff_closure_eq.2 closure_closedPoints
  refine (f.left.surjective.denseRange.dense_image f.left.continuous hd).mono ?_
  rintro _ ⟨a, ha, rfl⟩
  let u : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk (pointOfClosedPoint A.hom a ha) (pointOfClosedPoint_comp A.hom a ha)
  refine Set.mem_iUnion₂.2 ⟨u ≫ f, hP u, ⟨(default : PrimeSpectrum k), ?_⟩⟩
  exact congrArg f.left (pointOfClosedPoint_apply A.hom a ha _)

end GlobalTheory.CechPic

namespace GlobalTheory

open CechPic

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

namespace GlobalTheory.AmpleBaseChange

theorem relAmple_of_isPullback {S S' : Scheme.{0}} {B : Over S} [IsProper B.hom] {M : LB B.left}
    (hM : M.IsLB) (hA : Out.RelAmple B M) {t : S' ⟶ S} {X : Scheme.{0}} {π : X ⟶ B.left}
    {f : X ⟶ S'} (h : IsPullback π f B.hom t) : Out.RelAmple (Over.mk f) (M.pull π) := by
  have hp : IsProper (Over.mk f).hom := MorphismProperty.of_isPullback (P := @IsProper) h ‹_›
  refine AmpleLocal.relAmple_of_locally S' (Over.mk f) (M.pull π) (pull_isLB hM π)
    inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := t s) trivial
  exact ⟨t ⁻¹ᵁ V, hs, PolBaseChange.relAmple_restrict (A' := Over.mk f) h hM hA V hV⟩

theorem isProjBy_smooth_isProper_geometricallyIntegral :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom t → IsProjBy f ∧ Smooth f ∧ IsProper f ∧ GeometricallyIntegral f := by
  intro S B _ M hB hM hA R _ t X π f h
  have := hB.proper
  have hs : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) h hB.smooth
  refine ⟨?_, hs, MorphismProperty.of_isPullback (P := @IsProper) h hB.proper,
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ f hs
      (MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hB.geomConnected)⟩
  obtain ⟨N, -, m, s, hN, hv⟩ := veryAmpleBy_of_relAmple (A := Over.mk f) (pull_isLB hM π)
    (relAmple_of_isPullback hM hA h) (𝟙 X) (Category.id_comp f) (pull_isLB hM π)
    (LBIso.chartPull (chartPullId _) (chartPullPull (M.pull π) (𝟙 X) (𝟙 X) rfl)
      (PolBaseChange.lbIso_refl (pull_isLB hM π)))
  exact ⟨_, hN, m, s, hv⟩

end GlobalTheory.AmpleBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem pol_pull :
    ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L') :=
  PolPull.pol_pull_of_relAmple_local GlobalTheory.T.relAmple_of_locally_on_base

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_rigid_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ :=
  fun hL E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f _ =>
    obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym E H D l B B' b b' S S' s s' o o' f

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelDescent

section Points

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem isPullback_square (hA : IsPullback φ G'.hom G.hom f) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left)
    (h : IsSquare φ φ₂) : IsPullback φ₂ (G' ⊗ G').hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst G' G').left ≫ G'.hom = (G' ⊗ G').hom := Over.w _
  have v₂ : (snd G' G').left ≫ G'.hom = (G' ⊗ G').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ G'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst G' G').left = _
      refine hA.hom_ext ?_ ?_
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd G' G').left = _
      refine hA.hom_ext ?_ ?_
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem lift_square {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) {T : Over S'} {T₀ : Over S}
    {τ : T.left ⟶ T₀.left} {a b : T ⟶ G'} {a₀ b₀ : T₀ ⟶ G} (ha : a.left ≫ φ = τ ≫ a₀.left)
    (hb : b.left ≫ φ = τ ≫ b₀.left) : (lift a b).left ≫ φ₂ = τ ≫ (lift a₀ b₀).left := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ (fst G G).left = (_ ≫ _) ≫ (fst G G).left
    rw [Category.assoc, h.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
      lift_fst, ha]
  · change (_ ≫ _) ≫ (snd G G).left = (_ ≫ _) ≫ (snd G G).left
    rw [Category.assoc, h.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
      lift_snd, hb]

variable [GrpObj G] [GrpObj G']

theorem exists_liftHom (h : IsGrpPullback G' G f φ) (T : Over S') (T₀ : Over S) (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) :
    ∃ ρ : (T₀ ⟶ G) →* (T ⟶ G'), ∀ x₀ x, ρ x₀ = x ↔ x.left ≫ φ = τ ≫ x₀.left := by
  let r : (T₀ ⟶ G) → (T ⟶ G') := fun x₀ => Over.homMk
    (h.1.lift (τ ≫ x₀.left) T.hom (by rw [Category.assoc, Over.w, hτ])) (h.1.lift_snd _ _ _)
  have hr : ∀ x₀, (r x₀).left ≫ φ = τ ≫ x₀.left := fun x₀ => h.1.lift_fst _ _ _
  have key : ∀ x₀ x, r x₀ = x ↔ x.left ≫ φ = τ ≫ x₀.left := fun x₀ x =>
    ⟨fun e => e ▸ hr x₀, fun e => Over.OverMorphism.ext
      (h.1.hom_ext ((hr x₀).trans e.symm) (by rw [Over.w, Over.w]))⟩
  let U : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk τ hτ
  refine ⟨MonoidHom.mk' r fun a b => (key _ _).2 ?_, key⟩
  rw [← h.2 T (r a) (r b) (U ≫ a) (U ≫ b) (hr a).symm (hr b).symm, ← MonObj.comp_mul]
  rfl

theorem one_comp (h : IsGrpPullback G' G f φ) (T : Over S') (T₀ : Over S) (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) : (1 : T ⟶ G').left ≫ φ = τ ≫ (1 : T₀ ⟶ G).left := by
  obtain ⟨ρ, hρ⟩ := exists_liftHom h T T₀ τ hτ
  exact (hρ _ _).1 (map_one ρ)


omit [GrpObj G'] in
theorem weilIs_congr {X : Scheme.{0}} {a b : X ⟶ S} (e : a = b) (L : LB G.left) (k : ℤ)
    (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(X, ⊤)ˣ) (H : Out.WeilIs G L k x y c) : Out.WeilIs G L k x' y' c := by
  subst e
  rw [← Over.OverMorphism.ext hx, ← Over.OverMorphism.ext hy]
  exact H

end Points

section Bundles

variable {X X₀ Y Y₀ : Scheme.{0}}

theorem lbIso_square {P : LB X} {P₀ : LB X₀} (hP : P.IsLB) (hP₀ : P₀.IsLB) {F : X ⟶ X₀} (hw : LBIso P (P₀.pull F))
    {a : Y ⟶ X} {a₀ : Y₀ ⟶ X₀} {ψ : Y ⟶ Y₀} (e : a ≫ F = ψ ≫ a₀) : LBIso (P.pull a) ((P₀.pull a₀).pull ψ) :=
  LBIso.trans (pull_isLB hP _) (pull_isLB hP₀ (ψ ≫ a₀)) (pull_isLB (pull_isLB hP₀ _) _)
    (LBIso.chartPull (chartPullPull P a a rfl) (chartPullSame P₀ _ _ _ a fun _ => e.symm) hw)
    (LBIso.chartPull (chartPullSame P₀ _ _ _ ψ fun _ => rfl) (chartPullPull _ ψ ψ rfl)
      (PolBaseChange.lbIso_refl (pull_isLB hP₀ a₀)))

theorem exists_gen_of_lbIso {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) (H : LBIso L N)
    (h : ∃ t : L.Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen :=
  (CechPic.iso_triv_iff N).1 (LBIso.trans (LB.isLB_triv X) hL hN ((CechPic.iso_triv_iff L).2 h) H)

end Bundles

theorem prod_zpow_single {I H : Type} [Fintype I] [DecidableEq I] [CommGroup H] (l : (I → ℤ) → H)
    (hl : ∀ a b, l (a + b) = l a * l b) (a : I → ℤ) : ∏ u, l (Pi.single u 1) ^ a u = l a := by
  let F : (I → ℤ) →+ Additive H := AddMonoidHom.mk' (fun a => Additive.ofMul (l a)) fun a b => by
    rw [hl, ofMul_mul]
  have e : a = ∑ u, a u • (Pi.single u 1 : I → ℤ) := by
    ext v
    simp [Finset.sum_apply, Pi.single_apply]
  have : F a = ∑ u, a u • F (Pi.single u 1) := by
    conv_lhs => rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
  apply Additive.ofMul.injective
  rw [ofMul_prod]
  simp only [ofMul_zpow]
  exact this.symm

end GlobalTheory.SiegelDescent

namespace GlobalTheory

open SiegelDescent

theorem exists_siegPre_of_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₀)) ⟶ A₀)), s = spMap i ≫ s₀ → IsGrpPullback c.A A₀ (spMap i) φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∀ u, (c.lev (Pi.single u 1)).left ≫ φ = spMap i ≫ (lev₀ u).left) → ∃ c₀ : SiegPre h M ζ s₀, SiegPB c c₀ (spMap i) := by
  intro h M o _ ζ K₀ K _ _ i s₀ s c A₀ _ φ φ₂ P₀ lev₀ hs hp sq hP₀ hw hlev
  have ab : IsAbelianScheme A₀ := (T.abelian_scheme_descent_smooth_dimension K₀ K i A₀ c.A φ hp c.ab).1
  haveI := ab.comm
  haveI := ab.smooth
  haveI := ab.proper
  haveI := ab.geomConnected
  have epi : ∀ (F F' : Type) [Field F] [Field F'] (j : F →+* F'), Epi (spMap j) := fun F F' _ _ j =>
    ((_root_.GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff F F' j).1 _ _ (𝟙 _) (𝟙 _) (spMap j) (IsPullback.of_vert_isIso ⟨by simp⟩)).1
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ spMap i := hp.1.w
  have one := one_comp hp c.A A₀ φ hφ
  have idφ : (𝟙 c.A : c.A ⟶ c.A).left ≫ φ = φ ≫ (𝟙 A₀ : A₀ ⟶ A₀).left := by simp
  have gen := (T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom c.A.hom φ inferInstance inferInstance inferInstance hp.1).1
  have rig : ∀ (a : c.A ⟶ c.A ⊗ c.A) (a₀ : A₀ ⟶ A₀ ⊗ A₀), a.left ≫ φ₂ = φ ≫ a₀.left →
      (∃ t : (c.P.pull a.left).Gen, t.IsGen) → ∃ t : (P₀.pull a₀.left).Gen, t.IsGen := fun a a₀ e ht =>
    gen _ (pull_isLB hP₀ _) (exists_gen_of_lbIso (pull_isLB c.isLB _) (pull_isLB (pull_isLB hP₀ _) _)
      (lbIso_square c.isLB hP₀ hw e) ht)
  have symm : LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
    have h₁ : Smooth (A₀ ⊗ A₀).hom := by rw [Over.tensorObj_hom]; infer_instance
    have h₂ : IsProper (A₀ ⊗ A₀).hom := by rw [Over.tensorObj_hom]; infer_instance
    have h₃ : GeometricallyConnected (A₀ ⊗ A₀).hom := by
      rw [Over.tensorObj_hom]; exact GeometricallyConnected.comp _ _
    refine (T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom (c.A ⊗ c.A).hom φ₂ h₁ h₂ h₃ (isPullback_square hp.1 φ₂ sq)).2 _ _ hP₀
      (pull_isLB hP₀ _) ?_
    exact LBIso.trans (pull_isLB hP₀ _) c.isLB (pull_isLB (pull_isLB hP₀ _) _) hw.symm
      (LBIso.trans c.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB hP₀ _) _) c.symm
        (lbIso_square c.isLB hP₀ hw (lift_square sq sq.2.symm sq.1.symm)))
  have diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    lbIso_square c.isLB hP₀ hw (lift_square sq idφ idφ)

  obtain ⟨ρ, hρ⟩ := exists_liftHom hp (𝟙_ _) (𝟙_ _) (spMap i)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp K₀)) ⟶ A₀) := fun a => ∏ u, lev₀ u ^ a u
  have ρlev : ∀ a, ρ (lev a) = c.lev a := fun a => by
    rw [← prod_zpow_single c.lev c.lev_add a]
    refine (map_prod ρ _ _).trans (Finset.prod_congr rfl fun u _ => ?_)
    rw [map_zpow, (hρ _ _).2 (hlev u)]
  have hlev' : ∀ a, (c.lev a).left ≫ φ = spMap i ≫ (lev a).left := fun a => (hρ _ _).1 (ρlev a)
  have ρinj : Function.Injective ρ := fun x y e => by
    haveI := epi _ _ i
    exact Over.OverMorphism.ext ((cancel_epi (spMap i)).1
      (((hρ x _).1 rfl).symm.trans ((hρ y _).1 e.symm)))
  refine ⟨{ A := A₀, ab := ab, P := P₀, isLB := hP₀
            rig₁ := rig _ _ (lift_square sq one idφ) c.rig₁
            rig₂ := rig _ _ (lift_square sq idφ one) c.rig₂
            symm := symm, lev := lev
            lev_add := fun a b => ρinj (by rw [map_mul, ρlev, ρlev, ρlev, c.lev_add])
            lev_tors := fun a => ρinj (by rw [map_pow, ρlev, c.lev_tors, map_one])
            geom := ?_ }, φ, φ₂, hp, sq, hw, hlev'⟩
  intro k _ _ x β z hx hz
  obtain ⟨i', rfl⟩ : ∃ i' : K₀ →+* k, x = spMap i' := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  obtain ⟨Ω, _, _, j, j', hj⟩ := exists_algClosed_join_of_two_field_extensions K₀ K k i i'
  have e : spMap j' ≫ spMap i' = spMap j ≫ spMap i := by rw [← spMap_comp, ← spMap_comp, hj]
  obtain ⟨g₁, g₂, g₃⟩ := c.geom Ω (spMap j) (j'.comp β) (Units.map j'.toMonoidHom z)
    (by rw [hs, ← Category.assoc, ← e, Category.assoc, hx, spMap_comp]) (congrArg j' hz)
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk (spMap j)) (Over.mk (spMap i')) (spMap j') e
  have σinj : Function.Injective σ := fun x y e => by
    haveI := epi _ _ j'
    exact Over.OverMorphism.ext ((cancel_epi (spMap j')).1
      (((hσ x _).1 rfl).symm.trans ((hσ y _).1 e.symm)))
  have pt : ∀ a, (toUnit (Over.mk (spMap j)) ≫ c.lev a).left ≫ φ =
      spMap j' ≫ (toUnit (Over.mk (spMap i')) ≫ lev a).left := fun a => by
    change (spMap j ≫ (c.lev a).left) ≫ φ = spMap j' ≫ spMap i' ≫ (lev a).left
    rw [Category.assoc, hlev', reassoc_of% e]
  have σlev : ∀ a, σ (toUnit _ ≫ lev a) = toUnit _ ≫ c.lev a := fun a => (hσ _ _).2 (pt a)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    refine (T.weilPairing_fieldExtension_iff _ A₀ k Ω j' (spMap i') _ _ _ _ _ ab hD).1 ?_
    have H := (weilIs_grpPullback_of_comm _ _ A₀ c.A (spMap i) φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    rw [map_zpow]
    exact weilIs_congr e.symm _ _ _ _ _ _ (pt a) (pt b) _ H

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_of_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₀)) ⟶ A₀)), s = spMap i ≫ s₀ → IsGrpPullback c.A A₀ (spMap i) φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∀ u, (c.lev (Pi.single u 1)).left ≫ φ = spMap i ≫ (lev₀ u).left) → ∃ c₀ : SiegPre h M ζ s₀, SiegPB c c₀ (spMap i) := by
  first | exact @GlobalTheory.exists_siegPre_of_descended_data | exact GlobalTheory.exists_siegPre_of_descended_data | (intros; apply GlobalTheory.exists_siegPre_of_descended_data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem principalTorus_algebraic :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (χ : u.Λ → ℂ), P.g = g ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) :=
  TorusTransfer.torus_algebraic_of_siegel polarisedTorus_algebraic

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.BilinCalc

theorem sum_antisymm {M : Type*} [AddCommGroup M] {n : ℕ} (b : Fin n → Fin n → M) (hb : ∀ i j, b i j = b j i)
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : ∀ i j, D i j + D j i = 0) :
    ∑ uv : Fin n × Fin n, D uv.1 uv.2 • b uv.1 uv.2 = 0 := by
  classical

  let E : Fin n → Fin n → ℤ := fun i j => if i < j then D i j else 0
  have hDE : ∀ i j, D i j = E i j - E j i := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [E, hij, not_lt.mpr hij.le]
    · have := hD i i
      simp [E]
      omega
    · have := hD i j
      simp [E, hij, not_lt.mpr hij.le]
      omega
  have hswap : ∑ uv : Fin n × Fin n, E uv.2 uv.1 • b uv.1 uv.2 =
      ∑ uv : Fin n × Fin n, E uv.1 uv.2 • b uv.1 uv.2 := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun uv => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [hb]
  simp only [hDE, sub_smul, Finset.sum_sub_distrib, hswap, sub_self]

theorem map_prod_zpow {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    {n : ℕ} (x : Fin n → G) (c : Fin n → ℤ) : f (∏ i, x i ^ c i) = ∑ i, c i • f (x i) := by
  let φ : Additive G →+ M := AddMonoidHom.mk' (fun a => f a.toMul) fun a a' => hf _ _
  have hφ : ∀ g : G, f g = φ (Additive.ofMul g) := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hφ, ofMul_prod, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofMul_zpow, map_zsmul, ← hφ]

theorem sum_subst {G M : Type*} [CommGroup G] [AddCommGroup M] (B : G → G → M)
    (hB : ∀ x x' y, B (x * x') y = B x y + B x' y) (hs : ∀ x y, B x y = B y x) {n m : ℕ} (x : Fin n → G)
    (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ)
    (h : W' + W'.transpose = c.transpose * (W + W.transpose) * c) :
    ∑ uv : Fin n × Fin n, W' uv.1 uv.2 • B (x uv.1) (x uv.2) =
      ∑ uv : Fin m × Fin m, W uv.1 uv.2 • B (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i) := by
  classical
  have hL : ∀ (y : G) (k : Fin n → ℤ), B (∏ i, x i ^ k i) y = ∑ i, k i • B (x i) y :=
    fun y k => map_prod_zpow (fun g => B g y) (fun g g' => hB g g' y) x k
  have hR : ∀ (z : G) (k : Fin n → ℤ), B z (∏ i, x i ^ k i) = ∑ i, k i • B z (x i) :=
    fun z k => map_prod_zpow (fun g => B z g) (fun g g' => by rw [hs z, hB, hs g, hs g']) x k

  have hV : ∀ i j, ∑ a : Fin m, ∑ a' : Fin m, W a a' * (c a i * c a' j) = (c.transpose * W * c) i j := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hrhs : ∑ uv : Fin m × Fin m, W uv.1 uv.2 • B (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i) =
      ∑ ij : Fin n × Fin n, (c.transpose * W * c) ij.1 ij.2 • B (x ij.1) (x ij.2) := by
    simp only [hL, hR, Finset.smul_sum, smul_smul, Fintype.sum_prod_type, ← hV, Finset.sum_smul]
    calc _ = ∑ a : Fin m, ∑ i : Fin n, ∑ j : Fin n, ∑ a' : Fin m,
          (W a a' * (c a i * c a' j)) • B (x i) (x j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hrhs, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  refine sum_antisymm (fun i j => B (x i) (x j)) (fun i j => hs _ _) (W' - c.transpose * W * c) fun i j => ?_
  have hij := congrFun (congrFun h i) j
  have ht : (c.transpose * W * c).transpose = c.transpose * W.transpose * c := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hji := congrFun (congrFun ht i) j
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_add, Matrix.add_mul] at hij hji
  simp only [Matrix.sub_apply]
  linarith


open GlobalTheory.CechPic in
theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Pb : LB (G2 A).left), Pb.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso Pb (Pb.pull (lift (snd A A) (fst A A)).left) → ∀ (T : Over S) (n m : ℕ) (x : Fin n → (T ⟶ A)) (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ), W' + W'.transpose = c.transpose * (W + W.transpose) * c → LBIso (LB.LinComb Pb (K := Fin n × Fin n) (fun uv => (lift (x uv.1) (x uv.2)).left) (fun uv => W' uv.1 uv.2)) (LB.LinComb Pb (K := Fin m × Fin m) (fun uv => (lift (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i)).left) (fun uv => W uv.1 uv.2)) := by
  intro S A _ _ Pb hPb hbi hsym T n m x W W' c h
  classical

  let β : (T ⟶ A) → (T ⟶ A) → Pic T.left := fun u v => pull (lift u v).left (cls Pb hPb)
  have hadd : ∀ u u' v : T ⟶ A, β (u * u') v = β u v + β u' v := by
    intro u u' v
    obtain ⟨t, ht⟩ := (hbi T u u' v).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hPb _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hPb] at e
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_smul, neg_smul] at e
    simp only [β]
    rw [← sub_eq_zero, ← e]
    abel
  have hsw : ∀ u v : T ⟶ A, β u v = β v u := by
    intro u v
    have e : cls Pb hPb = cls _ (pull_isLB hPb _) := (cls_eq_iff hPb (pull_isLB hPb _)).2 hsym
    rw [cls_pull hPb] at e
    simp only [β]
    conv_lhs => rw [e, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  refine (cls_eq_iff (LB.isLB_linComb hPb _ _) (LB.isLB_linComb hPb _ _)).1 ?_
  rw [cls_linComb hPb, cls_linComb hPb]
  exact sum_subst β hadd hsw x W W' c h

end GlobalTheory.BilinCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitutionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.lineBundleIso_linComb_symm_biadditive_substitution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Pb : LB (G2 A).left), Pb.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso Pb (Pb.pull (lift (snd A A) (fst A A)).left) → ∀ (T : Over S) (n m : ℕ) (x : Fin n → (T ⟶ A)) (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ), W' + W'.transpose = c.transpose * (W + W.transpose) * c → LBIso (LB.LinComb Pb (K := Fin n × Fin n) (fun uv => (lift (x uv.1) (x uv.2)).left) (fun uv => W' uv.1 uv.2)) (LB.LinComb Pb (K := Fin m × Fin m) (fun uv => (lift (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.BilinCalc.main | exact GlobalTheory.BilinCalc.main | (intros; apply GlobalTheory.BilinCalc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open LatticeHom in
theorem exists_isMonHom_of_map_lattice :
    ThetaUnifAV → Out.Laws → ∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro hT hL P P' g u u' F hg hg' hF
  have key : ∀ (Q : Out.PolAV (Sp ℂ)) (w : HolUnif Q.A Q.L g), Q.g = g →
      ∃ (v : HolUnif Q.A Q.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : v.Λ → ℂ) (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        v.IsAH Hm χ ∧ (∀ (k : ℕ) θ, v.IsThetaFn Hm χ k θ → ∃ s, v.IsFnPow k s θ) ∧
        (∀ (k : ℕ) s, ∃ θ, v.IsThetaFn Hm χ k θ ∧ v.IsFnPow k s θ) ∧ ∀ z, v.ex (T z) = w.ex z := by
    rintro Q w rfl
    obtain ⟨rig, hrig⟩ := Q.rigid
    obtain ⟨v, Hm, χ, -, hAH, -, -, -, -, hsec, -⟩ := hT Q rig hrig
    obtain ⟨T, hTv⟩ := exists_linearEquiv_of_holUnif hL.mulN Q w v
    exact ⟨v, Hm, χ, T, hAH, fun k θ h => ((hsec k).2 θ h).exists, fun k s => ((hsec k).1 s).exists, hTv⟩
  obtain ⟨v, Hm, χ, T, hAH, hsec, -, hv⟩ := key P u hg
  obtain ⟨v', Hm', χ', T', hAH', -, hfn, hv'⟩ := key P' u' hg'
  let F₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap
  have hF₀ : ∀ z, F₀ (T z) = T' (F z) := fun z => by simp [F₀]
  have hΛ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ := fun l hl => by
    obtain ⟨z, rfl⟩ := T.surjective l
    rw [hF₀, ← v'.ker, hv', u'.ker]
    refine hF z ?_
    rwa [← u.ker, ← hv, v.ker]
  obtain ⟨d, hd⟩ := exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.isLB P'.isLB hAH hAH'
    F₀ hΛ 4
  obtain ⟨f, hf, hfe⟩ := exists_isMonHom_of_complementary hL.ample P P' v v' hsec hfn F₀ hΛ d hd
  exact ⟨f, hf, fun z => by rw [← hv', ← hF₀, hfe, hv]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasisOnAny
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.PushInv

open LBGerm

theorem exists_basisOn_any {S : Scheme.{0}} (hS : SecBaseChangeAnySt) (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∃ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ V), IsBasisOn P.A P.L V θ := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl x
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let T : Over S := overRes (T := baseOver S) V
  have hT : T.hom = V.ι := Category.comp_id _
  haveI : IsOpenImmersion T.hom := by rw [hT]; exact inferInstanceAs (IsOpenImmersion V.ι)
  haveI : IsOpenImmersion (snd T P.A).left := inferInstanceAs (IsOpenImmersion (pullback.snd T.hom P.A.hom))
  have hr : ∀ g : P.A.left, P.A.hom g ∈ V → g ∈ Set.range (snd T P.A).left := fun g hg => by
    rw [range_snd, hT]
    exact ⟨⟨_, hg⟩, rfl⟩
  choose θ hθ using fun i => exists_lift (snd T P.A).left (P.A.hom ⁻¹ᵁ V ⊓ P.L.U i) (fun g hg => hr g hg.1)
    ((LPow P.A P.L (1 : ℕ) T).U (fun _ => i)) (fun z hz => (mem_chart _ _ _ _ _ _).2 hz.2)
    ((b hq.default).f (fun _ => i))
  refine ⟨V, hV, θ, mem_secOn_of_germ θ fun g i j hg hi hj => ?_, fun R _ q hqV => ?_⟩
  · obtain ⟨z, rfl⟩ := hr g hg
    apply stalk_inj (snd T P.A).left z
    have hi' := (mem_chart P.A P.L T (1 : ℕ) z (fun _ => i)).2 hi
    have hj' := (mem_chart P.A P.L T (1 : ℕ) z (fun _ => j)).2 hj
    rw [map_mul, ← gs_stalkMap _ z (P.A.hom ⁻¹ᵁ V ⊓ P.L.U i) ⟨hg, hi⟩, ← gs_stalkMap _ z (P.A.hom ⁻¹ᵁ V ⊓ P.L.U j) ⟨hg, hj⟩,
      ← gm_comp _ (𝟙 _) z (P.L.U i ⊓ P.L.U j) ⟨hi, hj⟩, Category.comp_id]
    have e₁ := hθ i _ (𝟙 _) z ⟨hg, hi⟩
    have e₂ := hθ j _ (𝟙 _) z ⟨hg, hj⟩
    have e₃ := gm_lpow P.A P.L T (𝟙 _) z _ _ hi' hj'
    rw [Category.id_comp] at e₁ e₂ e₃
    rw [e₁, e₂, gs_compat (b hq.default) (𝟙 _) z hi' hj', e₃]
  · obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of R) ⟶ T.left, t ≫ T.hom = q :=
      ⟨IsOpenImmersion.lift T.hom q (by rw [hT]; exact hqV.trans (Scheme.Opens.range_ι V).ge), IsOpenImmersion.lift_fac _ _ _⟩
    choose b' hb' using fun i => exists_pull P.A P.L (1 : ℕ) (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i)
    obtain ⟨hli, hsp⟩ := hb R t b' hb'
    have e : (homAt t ▷ P.A).left ≫ (snd T P.A).left = (snd (baseAt t) P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)
    have val : ∀ (z : (baseAt t ⊗ P.A).left) i, (snd (baseAt t) P.A).left z ∈ P.L.U i →
        gs (𝟙 _) z _ ((b' hq.default).f (fun _ => i)) = gs (snd (baseAt t) P.A).left z _ (θ i) := fun z i hi => by
      have hi' := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).2 hi
      have hV' : P.A.hom ((snd (baseAt t) P.A).left z) ∈ V := by
        rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]
        exact hqV ⟨_, rfl⟩
      have hm : (snd T P.A).left ((homAt t ▷ P.A).left z) ∈ P.A.hom ⁻¹ᵁ V ⊓ P.L.U i := by
        rw [← Scheme.Hom.comp_apply, e]; exact ⟨hV', hi⟩
      have e₁ := hθ i _ (homAt t ▷ P.A).left z hm
      rw [e] at e₁
      rw [e₁, hb' hq.default (fun _ => i)]
      exact (gs_appLE (homAt t ▷ P.A).left _ _ _ (𝟙 _) z hi' _).trans (by rw [Category.id_comp])
    refine ⟨fun s => ?_, fun r h0 => ?_⟩
    · rw [Set.range_unique] at hsp
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
      refine ⟨r, fun z i hi => ?_⟩
      have hi' := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).2 hi
      have := gs_smul P.A P.L (baseAt t) _ r (SecM.ofSec P.A (b' hq.default)) (fun _ => i) z hi'
      rw [hr] at this
      exact this.trans (congrArg _ (val z i hi))
    · refine Fintype.linearIndependent_iff.1 hli (fun _ => r) ?_ hq.default
      rw [Fintype.sum_unique]
      refine Subtype.ext (funext fun j => fn_ext fun z hz => ?_)
      obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
      have hi := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).1 hz
      refine (gs_smul P.A P.L (baseAt t) _ r (SecM.ofSec P.A (b' hq.default)) (fun _ => i) z hz).trans ?_
      exact ((congrArg _ (val z i hi)).trans (h0 z i hi)).trans (gs_zero _ z _ hz).symm

theorem pushInvertible_any : Out.SecBaseChangeAnySt → Out.GlobalSectionsRankAlgClosed →
    ∀ (S : Scheme.{0}) (Q : Out.PolAV S), PushInvertible Q.A Q.L := by
  intro hS _ S P x
  obtain ⟨V, hV, θ, hθ, H⟩ := exists_basisOn_any hS P x
  haveI := P.smoothDim
  haveI : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  refine ⟨V, hV, θ, hθ, fun W hW s hs => ?_, exists_nonvanishing H⟩
  have e : ∀ (a : Γ(S, W)) (g : P.A.left) i, P.A.hom g ∈ W → g ∈ P.L.U i →
      gs (𝟙 _) g _ ((P.A.hom.appLE W (P.A.hom ⁻¹ᵁ W ⊓ P.L.U i) inf_le_left).hom a *
        resG P.A.left (inf_le_inf_right _ (P.A.hom.preimage_mono hW)) (θ i)) =
      gs P.A.hom g W a * gs (𝟙 _) g _ (θ i) := fun a g i hg hi => by
    have hm : g ∈ P.A.hom ⁻¹ᵁ W ⊓ P.L.U i := ⟨hg, hi⟩
    rw [gs_mul (𝟙 _) g _ hm, gs_res (𝟙 _) g _ hm, gs_appLE _ _ _ _ (𝟙 _) g hm, Category.id_comp]
  obtain ⟨a, ha⟩ := exists_coeff H hW hs
  refine ⟨a, fun i => fn_ext fun g hg => (ha g i hg.1 hg.2).trans (e a g i hg.1 hg.2).symm, fun a' ha' => ?_⟩
  exact eq_of_mul H hW _ _ fun g i hg hi =>
    ((e a' g i hg hi).symm.trans (congrArg _ (ha' i).symm)).trans (ha g i hg hi)

end GlobalTheory.PushInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDim
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDim
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open LatticeHom in
theorem existsUnique_isMonHom_of_map_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃! f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro hlaws _ _ hT P P' L L' u u' F hF
  obtain ⟨rig, hrig⟩ := P.8
  obtain ⟨rig', hrig'⟩ := P'.8
  obtain ⟨v, Hm, χ, Ef, hAH, -, -, -, -, hth, -⟩ := hT P rig hrig
  obtain ⟨v', Hm', χ', Ef', hAH', -, -, -, -, hth', -⟩ := hT P' rig' hrig'
  obtain ⟨T, hTu⟩ := exists_linearEquiv_of_holUnif hlaws.6 P u v
  obtain ⟨T', hTu'⟩ := exists_linearEquiv_of_holUnif hlaws.6 P' u' v'
  set F₀ : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ) :=
    T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap
  have hF₀T : ∀ z, F₀ (T z) = T' (F z) := fun z => by simp [F₀]
  have hF₀ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ := by
    intro l hl
    have h1 : u.ex (T.symm l) = 1 := by
      rw [← hTu, T.apply_symm_apply]
      exact (v.5 l).2 hl
    have h2 : u'.ex (F (T.symm l)) = 1 := (u'.5 _).2 (hF _ ((u.5 _).1 h1))
    refine (v'.5 _).1 ?_
    have h3 : F₀ l = T' (F (T.symm l)) := by simp [F₀]
    rw [h3, hTu']
    exact h2
  obtain ⟨d, hd⟩ := exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.7 P'.7
    hAH hAH' F₀ hF₀ 4
  obtain ⟨f, hf, hfF⟩ := exists_isMonHom_of_complementary hlaws.3 P P' v v'
    (fun k θ hθ => ((hth k).2 θ hθ).exists) (fun k s => ((hth' k).1 s).exists) F₀ hF₀ d hd
  have hfu : ∀ z, u'.ex (F z) = u.ex z ≫ f := by
    intro z
    rw [← hTu' (F z), ← hTu z, ← hfF, hF₀T]
  refine ⟨f, ⟨hf, hfu⟩, ?_⟩
  rintro f' ⟨-, hf'⟩
  have := P.5
  have : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g P.A.hom
  have : IsReduced P.A.left := isReduced_of_smooth_complex P.A.left P.A.hom inferInstance
  have := P'.3
  have : IsSeparated P'.A.hom := inferInstance
  apply ComplexPoints.over_hom_ext_of_complexPoints
  intro x
  obtain ⟨z, rfl⟩ := u.3 x
  rw [← hf' z, hfu z]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDimStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃! f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  first | exact @GlobalTheory.existsUnique_isMonHom_of_map_lattice | exact GlobalTheory.existsUnique_isMonHom_of_map_lattice | (intros; apply GlobalTheory.existsUnique_isMonHom_of_map_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem kTriv_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.KTriv (G i) (M i)) → Out.KTriv A L := by
  intro S I U A _ G _ ψ hU hG L M hL hM hLM hA hGA hK
  rw [GlobalTheory.UU.kTriv_iff_forall]
  intro T x hx
  apply over_ext hU
  intro i T' r
  obtain ⟨y, hy⟩ := exists_lift (hG i).1 (r ≫ x)
  have hpush : pushPt (hG i).1.w y = r ≫ x := by
    ext1
    exact hy.symm
  have hyK : GlobalTheory.UU.InK (G i) (M i) y :=
    GlobalTheory.UU.inK_of_push (hG i) hL (hM i) (hLM i) y (hpush ▸ hx.comp r)
  have hy1 : y = 1 := (GlobalTheory.UU.kTriv_iff_forall.1 (hK i)) T' y hyK
  have hsq : (r ≫ x) * (r ≫ x) = r ≫ x := by
    ext1
    rw [((hG i).2 T' y y (r ≫ x) (r ≫ x) hy hy), hy, hy1, _root_.mul_one]
  have h1 : r ≫ x = 1 := by simpa using hsq
  rw [h1]
  simp

end GlobalTheory.CoverGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupKernel_trivial_of_open_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.KTriv (G i) (M i)) → Out.KTriv A L := by
  first | exact @GlobalTheory.CoverGlue.kTriv_of_cover | exact GlobalTheory.CoverGlue.kTriv_of_cover | (intros; apply GlobalTheory.CoverGlue.kTriv_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecOnNonvanishing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SecFamily

theorem pushInvertible_of_laws (h : Out.Laws) (X : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) :
    PushInvertible P.A P.L :=
  GlobalTheory.PushInv.pushInvertible h.secBaseChange X P

theorem exists_secOn_nonvanishing : Out.Laws → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (x : X), ∃ (V : X.Opens) (θ : ∀ i, Γ(P.A.left, P.A.hom ⁻¹ᵁ V ⊓ P.L.U i)), x ∈ V ∧ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ V) ∧ (∀ y ∈ V, ∃ (a : P.A.left) (i : P.L.ι), P.A.hom a = y ∧ a ∈ P.A.left.basicOpen (θ i)) := by
  intro h X _ P x
  obtain ⟨V, hV, θ, hθ, -, H⟩ := pushInvertible_of_laws h X P x
  exact ⟨V, θ, hV, hθ, H⟩

end GlobalTheory.SecFamily
end
