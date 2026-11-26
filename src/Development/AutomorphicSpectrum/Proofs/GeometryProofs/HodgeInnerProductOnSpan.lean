module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUnique

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeExt

open GlobalTheory.TangentOrigin

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem isTangent_one' : IsTangent (1 : epsR ℂ ⟶ A) := by
  unfold IsTangent
  have e : (1 : epsR ℂ ⟶ A).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ η[A].left := by
    rw [Hom.one_def, Over.comp_left]
    congr 1
  rw [e, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
    ext x
    simp
  rw [this]
  simp

theorem isDiff_one_of_fderiv (u : HolUnif A L g) {U : A.left.Opens} (hU : IsAffineOpen U)
    (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) {w : Fin g → ℂ}
    (hw : ∀ s : Γ(A.left, U), fderiv ℂ (fun z => valAt' (u.ex z).left U s) 0 w = 0) :
    u.IsDiff w (1 : epsR ℂ ⟶ A) := by
  have hv : IsTangent (1 : epsR ℂ ⟶ A) := isTangent_one'
  have hvU := (tangent_mem_iff (u := u) hv U).2 h0
  refine (isDiff_iff hv hU hvU h0 w).2 ?_
  rw [(isDiff_iff hv hU hvU h0 0).1 (GlobalTheory.UnifDifferential.isDiff_one u)]
  refine RingHom.ext fun s => TrivSqZeroExt.ext rfl ?_
  rw [jet_snd, jet_snd, map_zero]
  exact (hw s).symm

def transl (u : HolUnif A L g) (z : Fin g → ℂ) : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A

theorem ex_comp_transl (u : HolUnif A L g) (z y : Fin g → ℂ) : u.ex y ≫ transl u z = u.ex (z + y) := by
  rw [transl, MonObj.comp_mul, u.ex_add, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex y ≫ toUnit A) (𝟙 _),
    Category.id_comp]

theorem fderiv_eq_zero_of_isDiff_one (u : HolUnif A L g) {w : Fin g → ℂ} (h : u.IsDiff w (1 : epsR ℂ ⟶ A))
    (z : Fin g → ℂ) {W : A.left.Opens} (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W) (s : Γ(A.left, W)) :
    fderiv ℂ (fun y => valAt' (u.ex y).left W s) z w = 0 := _root_.GlobalTheory.CompanionTheory.Ar.HodgeUnique.fderiv_eq_zero_of_isDiff_one (w := w) (W := W) u h z hz s

theorem eq_zero_of_isDiff_one (u : HolUnif A L g) {w : Fin g → ℂ} (h : u.IsDiff w (1 : epsR ℂ ⟶ A)) : w = 0 := _root_.GlobalTheory.CompanionTheory.Ar.HodgeUnique.eq_zero_of_isDiff_one (w := w) u h

theorem exists_affine (u : HolUnif A L g) : ∃ U : A.left.Opens, IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  refine ⟨U, hU, ?_⟩
  intro q _
  rw [hsub q]
  exact hpU

theorem eq_of_isDiff (u : HolUnif A L g) {v : epsR ℂ ⟶ A} (hv : IsTangent v) {d d' : Fin g → ℂ}
    (h : u.IsDiff d v) (h' : u.IsDiff d' v) : d = d' := by
  obtain ⟨U, hU, h0⟩ := exists_affine u
  have hvU := (tangent_mem_iff (u := u) hv U).2 h0
  exact sub_eq_zero.1 (eq_zero_of_isDiff_one u (isDiff_one_of_fderiv u hU h0 fun s => by
    rw [map_sub, ← h U hvU s, ← h' U hvU s, sub_self]))

theorem exists_linear_compare {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} {g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A' L' g') (f : A' ⟶ A) [IsMonHom f] :
    ∃ F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u'.ex z ≫ f := _root_.GlobalTheory.CompanionTheory.Ar.HodgeUnique.exists_linear_compare (A' := A') (L' := L') (g' := g') u u' f

end Unif

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X}
  {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

def push (h : IsGrpPullback A G z φ) {T : Over (Sp ℂ)} (x : T ⟶ A) : Over.mk (T.hom ≫ z) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]
    rfl)

theorem one_left_comp (h : IsGrpPullback A G z φ) (T : Over (Sp ℂ)) :
    (1 : T ⟶ A).left ≫ φ = (1 : Over.mk (T.hom ≫ z) ⟶ G).left := by
  have e := h.2 T 1 1 (push h 1) (push h 1) rfl rfl
  rw [_root_.mul_one] at e
  have e' : push h 1 * push h 1 = push h (1 : T ⟶ A) := Over.OverMorphism.ext e
  exact congrArg (·.left) (mul_eq_left.1 e')

theorem one_left {Y : Scheme.{0}} (y : Y ⟶ X) : (1 : Over.mk y ⟶ G).left = y ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

def lft (h : IsGrpPullback A G z φ) (v : epsAt z ⟶ G) : epsR ℂ ⟶ A :=
  Over.homMk (h.1.lift v.left (spMap (algebraMap ℂ (DualNumber ℂ))) (Over.w v)) (h.1.lift_snd _ _ _)

theorem lft_left (h : IsGrpPullback A G z φ) (v : epsAt z ⟶ G) : (lft h v).left ≫ φ = v.left :=
  h.1.lift_fst _ _ _

theorem lft_unique (h : IsGrpPullback A G z φ) {v : epsAt z ⟶ G} {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) :
    v' = lft h v :=
  Over.OverMorphism.ext (h.1.hom_ext (e.trans (lft_left h v).symm) (by rw [Over.w, Over.w]))

theorem lft_mul (h : IsGrpPullback A G z φ) (v w : epsAt z ⟶ G) : lft h (v * w) = lft h v * lft h w :=
  (lft_unique h (h.2 (epsR ℂ) (lft h v) (lft h w) v w (lft_left h v).symm (lft_left h w).symm).symm).symm

theorem isTangent_lft (h : IsGrpPullback A G z φ) {v : epsAt z ⟶ G} (hv : IsTanAt G z v) : IsTangent (lft h v) := by
  unfold IsTangent
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, lft_left]
    refine Eq.trans hv ?_
    have e := one_left_comp h (𝟙_ (Over (Sp ℂ)))
    rw [Hom.one_def, toUnit_unit, Category.id_comp] at e
    rw [e, one_left, one_left]
    simp
  · rw [Category.assoc]
    have e1 : (lft h v).left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w _
    have e2 : η[A].left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
    rw [e1, e2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext x
      simp
    rw [this]
    simp

theorem exists_map (h : IsGrpPullback A G z φ) {A' : Over (Sp ℂ)} [GrpObj A'] {φ' : A'.left ⟶ G.left}
    (h' : IsGrpPullback A' G z φ') : ∃ f : A' ⟶ A, IsMonHom f ∧ f.left ≫ φ = φ' := by
  let f : A' ⟶ A := Over.homMk (h.1.lift φ' A'.hom h'.1.w) (h.1.lift_snd _ _ _)
  have hf : f.left ≫ φ = φ' := h.1.lift_fst _ _ _
  refine ⟨f, isMonHom_of_mul _ fun T x y => ?_, hf⟩
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))
  have e1 := h'.2 T x y (push h' x) (push h' y) rfl rfl
  have e2 := h.2 T (x ≫ f) (y ≫ f) (push h' x) (push h' y)
    (by simp [push, hf]) (by simp [push, hf])
  rw [Over.comp_left, Category.assoc, hf, ← e1, e2]

variable {L₀ : LB A.left} {g : ℕ}

theorem exists_coords (h : IsGrpPullback A G z φ) (u₀ : HolUnif A L₀ g) {v : epsAt z ⟶ G} (hv : IsTanAt G z v)
    {A' : Over (Sp ℂ)} [GrpObj A'] {φ' : A'.left ⟶ G.left} (h' : IsGrpPullback A' G z φ') {L' : LB A'.left}
    {g' : ℕ} (u : HolUnif A' L' g') {v' : epsR ℂ ⟶ A'} (e : v'.left ≫ φ' = v.left) {α : Fin g' → ℂ}
    (d : u.IsDiff α v') : ∃ a, u₀.IsDiff a (lft h v) := by
  obtain ⟨f, _, hf⟩ := exists_map h h'
  obtain ⟨F, hF⟩ := exists_linear_compare u₀ u f
  have ht : IsTangent v' := by
    rw [lft_unique h' e]
    exact isTangent_lft h' hv
  have e' : v' ≫ f = lft h v := lft_unique h (by rw [Over.comp_left, Category.assoc, hf, e])
  exact ⟨F α, e' ▸ GlobalTheory.HomLinear.isDiff_comp u u₀ f F hF ht d⟩

theorem forall_of_span {V : Type} [AddCommGroup V] [Module ℂ V] {W : Set V} (hspan : Submodule.span ℂ W = ⊤)
    {p : V → Prop} (h0 : p 0) (hm : ∀ a ∈ W, p a) (hadd : ∀ a b, p a → p b → p (a + b))
    (hsm : ∀ (c : ℂ) a, p a → p (c • a)) (a : V) : p a :=
  Submodule.span_induction (p := fun x _ => p x) hm h0 (fun x y _ _ => hadd x y) (fun c x _ => hsm c x)
    (hspan ▸ Submodule.mem_top)

theorem exists_linear_coords {V : Type} [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V)
    (h : IsGrpPullback A G z φ) (u₀ : HolUnif A L₀ g) {W : Set V} (h0 : (0 : V) ∈ W)
    (hspan : Submodule.span ℂ W = ⊤) (hW : ∀ a ∈ W, ∃ d, u₀.IsDiff d (lft h (Mz.pt a))) :
    ∃ D : V →ₗ[ℂ] (Fin g → ℂ), ∀ a, u₀.IsDiff (D a) (lft h (Mz.pt a)) := by
  have ht : ∀ a, IsTangent (lft h (Mz.pt a)) := fun a => isTangent_lft h (Mz.tan a)
  have hadd : ∀ a b, lft h (Mz.pt (a + b)) = lft h (Mz.pt a) * lft h (Mz.pt b) := fun a b => by
    rw [Mz.add, lft_mul]
  have hmul : ∀ {a b d d'}, u₀.IsDiff d (lft h (Mz.pt a)) → u₀.IsDiff d' (lft h (Mz.pt b)) →
      u₀.IsDiff (d + d') (lft h (Mz.pt (a + b))) := fun {a b d d'} e e' => by
    rw [hadd]
    exact GlobalTheory.UnifDifferential.isDiff_mul u₀ ((Chart.isTan_iff _).2 (ht a)) ((Chart.isTan_iff _).2 (ht b)) e e'
  have hsm : ∀ (c : ℂ) {a d}, u₀.IsDiff d (lft h (Mz.pt a)) → u₀.IsDiff (c • d) (lft h (Mz.pt (c • a))) :=
    fun c {a d} e => by
      refine GlobalTheory.CMNormIdentity.isDiff_of_isLieComb u₀ e c ⟨![lft h (Mz.pt (c • a))], fun i => ?_, by simp⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      change (lft h (Mz.pt (c • a))).left = spMap (epsScaleR c) ≫ (lft h (Mz.pt a)).left
      refine h.1.hom_ext ?_ ?_
      · rw [lft_left, Category.assoc, lft_left]
        exact Mz.smul c a
      · have e1 : (lft h (Mz.pt (c • a))).left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w _
        have e2 : (lft h (Mz.pt a)).left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w _
        rw [e1, Category.assoc, e2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have : (epsScaleR c).comp (algebraMap ℂ (DualNumber ℂ)) = algebraMap ℂ (DualNumber ℂ) := by
          ext x <;> simp [epsScaleR]
        rw [this]
  have hall : ∀ a, ∃ d, u₀.IsDiff d (lft h (Mz.pt a)) := forall_of_span hspan (hW 0 h0) hW
    (fun a b ⟨d, e⟩ ⟨d', e'⟩ => ⟨_, hmul e e'⟩) (fun c a ⟨d, e⟩ => ⟨_, hsm c e⟩)
  choose D hD using hall
  exact ⟨{ toFun := D
           map_add' := fun a b => eq_of_isDiff u₀ (ht _) (hD _) (hmul (hD a) (hD b))
           map_smul' := fun c a => eq_of_isDiff u₀ (ht _) (hD _) (hsm c (hD a)) }, hD⟩

end Pull

theorem hodgeInnerProduct_of_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S' S : Scheme.{0}) (t₀ : SAB H S') (t : SAB H S) (f : S' ⟶ S) (_ : SABMap t₀ t f) (z₀ : Sp ℂ ⟶ S') (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (z₀ ≫ f) V) (core : InnerProductSpace.Core ℂ V) (W : Set V), (0 : V) ∈ W → Submodule.span ℂ W = ⊤ → (∀ a ∈ W, ∀ b ∈ W, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (core.inner a b)) → ∀ a b : V, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (core.inner a b) := by
  intro E _ _ _ H S' S t₀ t f m z₀ V _ _ Mz core W h0 hspan hW
  obtain ⟨hLB, -, -, A₀, _, φ₀, g, u₀, Hm₀, χ₀, -, -, -, -, hpb, hAH, -, -, -, -, -⟩ := hW 0 h0 0 h0
  obtain ⟨D, hD⟩ := exists_linear_coords Mz hpb u₀ h0 hspan fun a ha => by
    obtain ⟨-, -, -, A, _, φ, g', u, Hm, χ, v', -, α, -, hpb', -, e1, -, d1, -, -⟩ := hW a ha a ha
    exact exists_coords hpb u₀ (Mz.tan a) hpb' u e1 d1
  let T : V → V → ℂ := fun a b => Real.pi * (D b ⬝ᵥ Hm₀.mulVec (star (D a)))
  have hT : ∀ a b, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (T a b) := fun a b =>
    ⟨hLB, Mz.tan a, Mz.tan b, A₀, _, φ₀, g, u₀, Hm₀, χ₀, lft hpb _, lft hpb _, D a, D b, hpb, hAH, lft_left hpb _, lft_left hpb _, hD a, hD b,
      rfl⟩
  have hlift : ∀ v : epsAt (z₀ ≫ f) ⟶ t.G, ∃ v' : epsAt z₀ ⟶ t₀.G, v'.left ≫ m.φ = v.left := fun v =>
    ⟨Over.homMk (m.cart.1.lift v.left (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ z₀)
      (by simpa using Over.w v)) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩
  have hWW : ∀ a ∈ W, ∀ b ∈ W, T a b = core.inner a b := fun a ha b hb => by
    obtain ⟨a', ea⟩ := hlift (Mz.pt a)
    obtain ⟨b', eb⟩ := hlift (Mz.pt b)
    exact (GlobalTheory.T.hodge_inner_product_pullback_unique E H S' S t₀ t f m z₀ a' b' _ _ ea eb).2 _ _ (hT a b) (hW a ha b hb)
  have hr : ∀ x y y', core.inner x (y + y') = core.inner x y + core.inner x y' := fun x y y' => by
    rw [← core.conj_inner_symm, core.add_left, map_add (f := _), core.conj_inner_symm, core.conj_inner_symm]
  have hs : ∀ (c : ℂ) x y, core.inner x (c • y) = c * core.inner x y := fun c x y => by
    rw [← core.conj_inner_symm, core.smul_left, map_mul, core.conj_inner_symm, Complex.conj_conj]
  have h1 : ∀ a ∈ W, ∀ b, T a b = core.inner a b := fun a ha =>
    forall_of_span hspan (hWW a ha 0 h0) (hWW a ha)
      (fun b b' e e' => by
        rw [hr, ← e, ← e']
        simp only [T, map_add (f := _), add_dotProduct, mul_add])
      (fun c b e => by
        rw [hs, ← e]
        simp only [T, map_smul, smul_dotProduct, smul_eq_mul]
        ring)
  have h2 : ∀ a b, T a b = core.inner a b := fun a b =>
    forall_of_span hspan (p := fun a => T a b = core.inner a b) (h1 0 h0 b) (fun a ha => h1 a ha b)
      (fun a a' e e' => by
        change _ = core.inner (a + a') b
        rw [core.add_left]
        rw [← e, ← e']
        simp only [T, map_add (f := _), star_add, mulVec_add, dotProduct_add, mul_add])
      (fun c a e => by
        change _ = core.inner (c • a) b
        rw [core.smul_left]
        rw [← e]
        simp only [T, map_smul, star_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]
        simp
        ring) a
  intro a b
  rw [← h2]
  exact hT a b

end GlobalTheory.CompanionTheory.Ar.HodgeExt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpanStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inner_product_on_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S' S : Scheme.{0}) (t₀ : SAB H S') (t : SAB H S) (f : S' ⟶ S) (_ : SABMap t₀ t f) (z₀ : Sp ℂ ⟶ S') (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (z₀ ≫ f) V) (core : InnerProductSpace.Core ℂ V) (W : Set V), (0 : V) ∈ W → Submodule.span ℂ W = ⊤ → (∀ a ∈ W, ∀ b ∈ W, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (core.inner a b)) → ∀ a b : V, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (core.inner a b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span | exact GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span <;> assumption)
end
