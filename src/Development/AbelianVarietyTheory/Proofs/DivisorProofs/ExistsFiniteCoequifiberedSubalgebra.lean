module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace GlobalTheory.QcSub

variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)

def gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) : Subring (F.obj (op W)) :=
  Subring.closure (Set.range (α.app (op W)).hom ∪ (F.map (homOfLE h).op).hom '' T)

lemma algebraMap_mem_gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) (r : Γ(X, W)) :
    (α.app (op W)).hom r ∈ gen F α h T :=
  Subring.subset_closure (Or.inl ⟨r, rfl⟩)

lemma res_mem_gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) {t : F.obj (op V)}
    (ht : t ∈ T) : (F.map (homOfLE h).op).hom t ∈ gen F α h T :=
  Subring.subset_closure (Or.inr ⟨t, ht, rfl⟩)

lemma map_gen_le {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V))) :
    (gen F α h T).map (F.map (homOfLE h').op).hom ≤ gen F α (h'.trans h) T := by
  rw [gen, RingHom.map_closure, Subring.closure_le]
  rintro _ ⟨y, (⟨r, rfl⟩ | ⟨t, ht, rfl⟩), rfl⟩
  · have := congr($(α.naturality (homOfLE h').op).hom r)
    simp only [CommRingCat.comp_apply] at this
    rw [← this]
    exact algebraMap_mem_gen F α _ T _
  · rw [← CommRingCat.comp_apply, ← F.map_comp]
    exact res_mem_gen F α _ T ht

lemma res_mem_gen_of_mem {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V)))
    {b : F.obj (op W)} (hb : b ∈ gen F α h T) :
    (F.map (homOfLE h').op).hom b ∈ gen F α (h'.trans h) T :=
  map_gen_le F α h h' T ⟨b, hb, rfl⟩

lemma gen_eq_adjoin {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) :
    (letI := (α.app (op W)).hom.toAlgebra
     gen F α h T = (Algebra.adjoin Γ(X, W) ((F.map (homOfLE h).op).hom '' T)).toSubring) := by
  let := (α.app (op W)).hom.toAlgebra
  rw [Algebra.adjoin_eq_ring_closure]
  rfl

variable {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))

def sub (W : X.Opens) : Subring (F.obj (op W)) :=
  ⨅ (j : ι) (W' : X.Opens) (_ : IsAffineOpen W') (hW : W' ≤ W) (hV : W' ≤ V j),
    (gen F α hV (T j)).comap (F.map (homOfLE hW).op).hom

lemma mem_sub {W : X.Opens} {b : F.obj (op W)} :
    b ∈ sub F α V T W ↔ ∀ (j : ι) (W' : X.Opens), IsAffineOpen W' → ∀ (hW : W' ≤ W)
      (hV : W' ≤ V j), (F.map (homOfLE hW).op).hom b ∈ gen F α hV (T j) := by
  simp only [sub, Subring.mem_iInf, Subring.mem_comap]

lemma algebraMap_mem_sub (W : X.Opens) (r : Γ(X, W)) : (α.app (op W)).hom r ∈ sub F α V T W := by
  rw [mem_sub]
  intro j W' _ hW hV
  have := congr($(α.naturality (homOfLE hW).op).hom r)
  simp only [CommRingCat.comp_apply] at this
  rw [← this]
  exact algebraMap_mem_gen F α _ _ _

lemma res_mem_sub {W W₁ : X.Opens} (h : W₁ ≤ W) {b : F.obj (op W)} (hb : b ∈ sub F α V T W) :
    (F.map (homOfLE h).op).hom b ∈ sub F α V T W₁ := by
  rw [mem_sub] at hb ⊢
  intro j W' hW' hW hV
  rw [← CommRingCat.comp_apply, ← F.map_comp]
  exact hb j W' hW' (hW.trans h) hV

def subMap (W : X.Opens) : Γ(X, W) →+* sub F α V T W :=
  (α.app (op W)).hom.codRestrict _ (algebraMap_mem_sub F α V T W)

def subFunctor : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj W := CommRingCat.of (sub F α V T W.unop.1)
  map {W W₁} f := CommRingCat.ofHom
    ((F.map ((Scheme.AffineZariskiSite.toOpensFunctor X).map f.unop).op).hom.restrict _ _
      (fun _ hb ↦ res_mem_sub F α V T _ hb))
  map_id W := by
    ext b
    change (F.map _).hom b.1 = b.1
    rw [Subsingleton.elim ((Scheme.AffineZariskiSite.toOpensFunctor X).map (𝟙 W).unop).op (𝟙 _)]
    erw [F.map_id]
    rfl
  map_comp {W₁ W₂ W₃} f g := by
    ext b
    change (F.map _).hom b.1 = (F.map _).hom ((F.map _).hom b.1)
    rw [← CommRingCat.comp_apply]
    erw [← F.map_comp]
    rfl

def subNat : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ subFunctor F α V T where
  app W := CommRingCat.ofHom (subMap F α V T W.unop.1)
  naturality {W W₁} f := by
    ext r
    exact Subtype.ext congr($(α.naturality ((Scheme.AffineZariskiSite.toOpensFunctor X).map f.unop).op).hom r)

def subIncl : subFunctor F α V T ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F where
  app W := CommRingCat.ofHom (sub F α V T W.unop.1).subtype
  naturality _ _ _ := rfl

lemma subNat_comp_subIncl :
    subNat F α V T ≫ subIncl F α V T = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α :=
  rfl

lemma subIncl_injective (W : X.AffineZariskiSiteᵒᵖ) : Function.Injective ((subIncl F α V T).app W).hom :=
  Subtype.val_injective

lemma isLocalizationAway
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W)) :
    (letI := (F.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
     IsLocalization.Away ((α.app (op W)).hom f) (F.obj (op (X.basicOpen f)))) :=
  Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp hα ⟨W, hW⟩ f

end GlobalTheory.QcSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdjoinRestrictedSectionsOfLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdjoinRestrictedSectionsOfLocal
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub.Local

theorem adjoin_mem_of_away {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R']
    [IsLocalization.Away (algebraMap R A g) A'] (T : Set A) (b : A)
    (hb : algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T)) :
    ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  classical
  have hgen : ∀ k : ℕ, algebraMap R A g ^ k ∈ Algebra.adjoin R T := fun k =>
    pow_mem (Subalgebra.algebraMap_mem _ g) k
  have hgA : algebraMap A A' (algebraMap R A g) = algebraMap R' A' (algebraMap R R' g) := by
    rw [← IsScalarTower.algebraMap_apply R A A', ← IsScalarTower.algebraMap_apply R R' A']
  have key : ∀ x ∈ Algebra.adjoin R' (algebraMap A A' '' T), ∃ m : ℕ, ∃ s ∈ Algebra.adjoin R T,
      algebraMap A A' (algebraMap R A g) ^ m * x = algebraMap A A' s := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨0, t, Algebra.subset_adjoin ht, by simp⟩
    | algebraMap r =>
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) r
      refine ⟨n, algebraMap R A a, Subalgebra.algebraMap_mem _ a, ?_⟩
      have h2 := congrArg (algebraMap R' A') hr
      simp only [map_mul, map_pow] at h2
      rw [mul_comm, hgA, h2, ← IsScalarTower.algebraMap_apply R R' A',
        ← IsScalarTower.algebraMap_apply R A A']
    | add x y _ _ hx hy =>
      obtain ⟨m1, s1, hs1, e1⟩ := hx
      obtain ⟨m2, s2, hs2, e2⟩ := hy
      refine ⟨m1 + m2, algebraMap R A g ^ m2 * s1 + algebraMap R A g ^ m1 * s2,
        add_mem (mul_mem (hgen _) hs1) (mul_mem (hgen _) hs2), ?_⟩
      rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← e1, ← e2]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨m1, s1, hs1, e1⟩ := hx
      obtain ⟨m2, s2, hs2, e2⟩ := hy
      refine ⟨m1 + m2, s1 * s2, mul_mem hs1 hs2, ?_⟩
      rw [map_mul, ← e1, ← e2]
      ring
  obtain ⟨m, s, hs, hms⟩ := key _ hb
  rw [← map_pow, ← map_mul] at hms
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R A g)) A').mp hms
  refine ⟨k + m, ?_⟩
  have h3 : algebraMap R A g ^ (k + m) * b = algebraMap R A g ^ k * s := by
    rw [pow_add, mul_assoc]
    exact hk
  rw [h3]
  exact mul_mem (hgen k) hs

theorem mem_gen_of_local (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    (V W : X.Opens) (T : Set (F.obj (op V))) (b : F.obj (op W))
    (H : ∀ x ∈ W ⊓ V, ∃ D : X.Opens, IsAffineOpen D ∧ x ∈ D ∧ ∃ (hW : D ≤ W) (hV : D ≤ V),
      (F.map (homOfLE hW).op).hom b ∈ gen F α hV T)
    (W' : X.Opens) (hW' : IsAffineOpen W') (hW : W' ≤ W) (hV : W' ≤ V) :
    (F.map (homOfLE hW).op).hom b ∈ gen F α hV T := by
  classical
  let _ : Algebra Γ(X, W') (F.obj (op W')) := (α.app (op W')).hom.toAlgebra
  have comp : ∀ {U₁ U₂ U₃ : X.Opens} (h₁₂ : U₂ ≤ U₁) (h₂₃ : U₃ ≤ U₂) (y : F.obj (op U₁)),
      (F.map (homOfLE h₂₃).op).hom ((F.map (homOfLE h₁₂).op).hom y) =
        (F.map (homOfLE (h₂₃.trans h₁₂)).op).hom y := by
    intro U₁ U₂ U₃ h₁₂ h₂₃ y
    show (F.map (homOfLE h₁₂).op ≫ F.map (homOfLE h₂₃).op).hom y = _
    rw [← F.map_comp]
    rfl
  let b' := (F.map (homOfLE hW).op).hom b
  let T' : Set (F.obj (op W')) := (F.map (homOfLE hV).op).hom '' T
  let S := Algebra.adjoin Γ(X, W') T'
  let I : Ideal Γ(X, W') :=
    (Subalgebra.toSubmodule S).comap (LinearMap.toSpanSingleton Γ(X, W') (F.obj (op W')) b')
  have hI : ∀ r, r ∈ I ↔ (α.app (op W')).hom r * b' ∈ S := fun r => by
    simp only [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Subalgebra.mem_toSubmodule,
      Algebra.smul_def]
    rfl
  have key : ∀ (D : X.Opens) (f : Γ(X, W')) (hfD : X.basicOpen f ≤ D) (hDW : D ≤ W) (hDV : D ≤ V),
      (F.map (homOfLE hDW).op).hom b ∈ gen F α hDV T → f ∈ I.radical := by
    intro D f hfD hDW hDV hbD
    let _ : Algebra Γ(X, X.basicOpen f) (F.obj (op (X.basicOpen f))) :=
      (α.app (op (X.basicOpen f))).hom.toAlgebra
    let _ : Algebra (F.obj (op W')) (F.obj (op (X.basicOpen f))) :=
      (F.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    let _ : Algebra Γ(X, W') (F.obj (op (X.basicOpen f))) :=
      ((F.map (homOfLE (X.basicOpen_le f)).op).hom.comp (α.app (op W')).hom).toAlgebra
    have : IsScalarTower Γ(X, W') (F.obj (op W')) (F.obj (op (X.basicOpen f))) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : IsScalarTower Γ(X, W') Γ(X, X.basicOpen f) (F.obj (op (X.basicOpen f))) :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        have h := congrArg (fun φ => φ.hom x) (α.naturality (homOfLE (X.basicOpen_le f)).op)
        exact h.symm)
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := hW'.isLocalization_basicOpen f
    have : IsLocalization.Away (algebraMap Γ(X, W') (F.obj (op W')) f)
        (F.obj (op (X.basicOpen f))) := isLocalizationAway F α hα hW' f
    have hres := res_mem_gen_of_mem F α hDV hfD T hbD
    rw [gen_eq_adjoin] at hres
    have hb'' : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) b' ∈
        Algebra.adjoin Γ(X, X.basicOpen f)
          (algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) '' T') := by
      have e1 : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) b' =
          (F.map (homOfLE hfD).op).hom ((F.map (homOfLE hDW).op).hom b) :=
        (comp hW (X.basicOpen_le f) b).trans (comp hDW hfD b).symm
      have e2 : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) '' T' =
          (F.map (homOfLE (hfD.trans hDV)).op).hom '' T := by
        simp only [T', Set.image_image]
        exact Set.image_congr (fun y _ => comp hV (X.basicOpen_le f) y)
      rw [e1, e2]
      exact hres
    obtain ⟨m, hm⟩ := adjoin_mem_of_away f T' b' hb''
    exact ⟨m, (hI _).mpr (by rw [map_pow]; exact hm)⟩
  have cover : W' ≤ ⨆ f : (I.radical : Set Γ(X, W')), X.basicOpen f.1 := by
    intro x hx
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨D, hD, hxD, hDW, hDV, hbD⟩ := H x (by exact ⟨hW hx, hV hx⟩)
    obtain ⟨f, hfD, hxf⟩ := hW'.exists_basicOpen_le (V := D) ⟨x, hxD⟩ hx
    exact ⟨⟨f, key D f hfD hDW hDV hbD⟩, hxf⟩
  have htop : I = ⊤ := by
    rw [← Ideal.radical_eq_top, ← Ideal.span_eq I.radical]
    exact (hW'.self_le_iSup_basicOpen_iff).mp cover
  have h1 : (1 : Γ(X, W')) ∈ I := htop ▸ Submodule.mem_top
  rw [hI, map_one, one_mul] at h1
  rw [gen_eq_adjoin]
  exact h1

end GlobalTheory.QcSub.Local
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdjoinRestrictedSectionsOfLocalStatement
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adjoin_restricted_sections_of_local : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ (V W : X.Opens) (T : Set (F.obj (op V))) (b : F.obj (op W)), (∀ x ∈ W ⊓ V, ∃ D : X.Opens, IsAffineOpen D ∧ x ∈ D ∧ ∃ (hW : D ≤ W) (hV : D ≤ V), (F.map (homOfLE hW).op).hom b ∈ gen F α hV T) → ∀ W' : X.Opens, IsAffineOpen W' → ∀ (hW : W' ≤ W) (hV : W' ≤ V), (F.map (homOfLE hW).op).hom b ∈ gen F α hV T := by
  first | exact @GlobalTheory.QcSub.Local.mem_gen_of_local | exact GlobalTheory.QcSub.Local.mem_gen_of_local | (intros; apply GlobalTheory.QcSub.Local.mem_gen_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineInterFiniteBasicOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineInterFiniteBasicOpenCover
open AlgebraicGeometry TopologicalSpace

namespace GlobalTheory

theorem affine_inter_finite_basicOpen_cover :
    ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (W V : X.Opens), IsAffineOpen W → IsAffineOpen V →
      ∃ s : Finset Γ(X, W), (∀ h ∈ s, ∃ r : Γ(X, V), X.basicOpen h = X.basicOpen r) ∧
        ((W ⊓ V : X.Opens) : Set X) ⊆ ⋃ h ∈ s, (X.basicOpen h : Set X) := by
  intro X hX W V hW hV
  classical
  have key : ∀ x : ((W ⊓ V : X.Opens) : Set X), ∃ (f : Γ(X, W)) (g : Γ(X, V)),
      X.basicOpen f = X.basicOpen g ∧ (x : X) ∈ X.basicOpen f :=
    fun x => exists_basicOpen_le_affine_inter hW hV x.1 x.2
  choose f g hfg hx using key
  have hc : IsCompact ((W ⊓ V : X.Opens) : Set X) := NoetherianSpace.isCompact _
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hx _⟩)
  refine ⟨t.image f, ?_, ?_⟩
  · intro h hh
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hh
    exact ⟨g x, hfg x⟩
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    exact Set.mem_iUnion₂.2 ⟨f x, Finset.mem_image_of_mem f hxt, hyx⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineInterFiniteBasicOpenCoverStatement
open AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (W V : X.Opens), IsAffineOpen W → IsAffineOpen V → ∃ s : Finset Γ(X, W), (∀ h ∈ s, ∃ r : Γ(X, V), X.basicOpen h = X.basicOpen r) ∧ ((W ⊓ V : X.Opens) : Set X) ⊆ ⋃ h ∈ s, (X.basicOpen h : Set X) := by
  first | exact @GlobalTheory.affine_inter_finite_basicOpen_cover | exact GlobalTheory.affine_inter_finite_basicOpen_cover | (intros; apply GlobalTheory.affine_inter_finite_basicOpen_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulMemSubalgebraOfResBasicOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemAdjoinOfLocalizationAway
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemAdjoinOfLocalizationAway
open Algebra

theorem GlobalTheory.adjoin_mem_of_away_localization {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'] (T : Set A) (b : A)
    (hb : algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T)) :
    ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  have hg : algebraMap A A' (algebraMap R A g) = algebraMap R A' g :=
    (IsScalarTower.algebraMap_apply R A A' g).symm
  have key : ∀ y ∈ Algebra.adjoin R' (algebraMap A A' '' T), ∃ k : ℕ, ∃ z ∈ Algebra.adjoin R T,
      algebraMap A A' z = algebraMap R A' g ^ k * y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨0, a, Algebra.subset_adjoin ha, by simp⟩
    | algebraMap r =>
      obtain ⟨⟨r0, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) r
      refine ⟨n, algebraMap R A r0, Subalgebra.algebraMap_mem _ r0, ?_⟩
      simp only at hr
      rw [← IsScalarTower.algebraMap_apply R A A', IsScalarTower.algebraMap_apply R R' A', ← hr,
        map_mul, ← IsScalarTower.algebraMap_apply R R' A', map_pow, mul_comm]
    | add x y _ _ hx hy =>
      obtain ⟨k1, z1, hz1, e1⟩ := hx
      obtain ⟨k2, z2, hz2, e2⟩ := hy
      refine ⟨k1 + k2, algebraMap R A g ^ k2 * z1 + algebraMap R A g ^ k1 * z2, ?_, ?_⟩
      · refine add_mem (mul_mem ?_ hz1) (mul_mem ?_ hz2) <;>
          (rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _)
      · rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, hg, e1, e2]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨k1, z1, hz1, e1⟩ := hx
      obtain ⟨k2, z2, hz2, e2⟩ := hy
      refine ⟨k1 + k2, z1 * z2, mul_mem hz1 hz2, ?_⟩
      rw [map_mul, e1, e2]; ring
  obtain ⟨k, z, hz, e⟩ := key _ hb
  have h0 : algebraMap A A' (z - algebraMap R A g ^ k * b) = 0 := by
    rw [map_sub, map_mul, map_pow, hg, e, sub_self]
  obtain ⟨⟨_, c, rfl⟩, hc⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A g)) A' _).1 h0
  refine ⟨c + k, ?_⟩
  have : algebraMap R A g ^ (c + k) * b = algebraMap R A g ^ c * z := by
    simp only at hc
    rw [mul_sub, sub_eq_zero] at hc
    rw [hc, pow_add]; ring
  rw [this]
  refine mul_mem ?_ hz
  rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _

theorem GlobalTheory.adjoin_mem_of_away_localization' : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (T : Set A) (b : A), algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T) → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  intros R A R' A' _ _ _ _ _ _ _ _ _ _ _ g _ _ T b h
  exact GlobalTheory.adjoin_mem_of_away_localization g T b h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemAdjoinOfLocalizationAwayStatement
open Algebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_mem_adjoin_of_localizationAway : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (T : Set A) (b : A), algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T) → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  first | exact @GlobalTheory.adjoin_mem_of_away_localization' | exact GlobalTheory.adjoin_mem_of_away_localization' | (intros; apply GlobalTheory.adjoin_mem_of_away_localization' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulMemSubalgebraOfResBasicOpen
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub.PowerMultiple

variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)

theorem res_pow_mul_mem_gen
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {D W V : X.Opens} (hD : IsAffineOpen D) (hDW : D ≤ W) (hDV : D ≤ V)
    (T : Set (F.obj (op V))) (f : Γ(X, W)) (a : F.obj (op W))
    (ha : ∀ (W' : X.Opens), IsAffineOpen W' → ∀ (h1 : W' ≤ X.basicOpen f) (h2 : W' ≤ V),
      (F.map (homOfLE h1).op).hom ((F.map (homOfLE (X.basicOpen_le f)).op).hom a) ∈
        gen F α h2 T) :
    ∃ m : ℕ, (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f ^ m * a) ∈ gen F α hDV T := by
  set fD : Γ(X, D) := (X.presheaf.map (homOfLE hDW).op).hom f with hfD
  have hbo : X.basicOpen fD = D ⊓ X.basicOpen f := Scheme.basicOpen_res X f (homOfLE hDW).op
  have hD'D : X.basicOpen fD ≤ D := X.basicOpen_le fD
  have hD'f : X.basicOpen fD ≤ X.basicOpen f := hbo.le.trans inf_le_right
  have hD'V : X.basicOpen fD ≤ V := hD'D.trans hDV
  have hD' : IsAffineOpen (X.basicOpen fD) := hD.basicOpen fD
  letI iRA : Algebra Γ(X, D) (F.obj (op D)) := (α.app (op D)).hom.toAlgebra
  letI iRR' : Algebra Γ(X, D) Γ(X, X.basicOpen fD) :=
    (X.presheaf.map (homOfLE hD'D).op).hom.toAlgebra
  letI iR'A' : Algebra Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) :=
    (α.app (op (X.basicOpen fD))).hom.toAlgebra
  letI iAA' : Algebra (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    (F.map (homOfLE hD'D).op).hom.toAlgebra
  letI iRA' : Algebra Γ(X, D) (F.obj (op (X.basicOpen fD))) :=
    ((F.map (homOfLE hD'D).op).hom.comp (α.app (op D)).hom).toAlgebra
  haveI : IsScalarTower Γ(X, D) (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(X, D) Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have := congr($(α.naturality (homOfLE hD'D).op).hom r)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  haveI : IsLocalization.Away fD Γ(X, X.basicOpen fD) := hD.isLocalization_basicOpen fD
  haveI : IsLocalization.Away (algebraMap Γ(X, D) (F.obj (op D)) fD)
      (F.obj (op (X.basicOpen fD))) := isLocalizationAway F α hα hD fD
  have hres : ∀ {U₁ U₂ U₃ : X.Opens} (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂) (y : F.obj (op U₁)),
      (F.map (homOfLE h₂).op).hom ((F.map (homOfLE h₁).op).hom y) =
        (F.map (homOfLE (h₂.trans h₁)).op).hom y := by
    intro U₁ U₂ U₃ h₁ h₂ y
    rw [← CommRingCat.comp_apply, ← F.map_comp]
    rfl
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_pow_mul_mem_adjoin_of_localizationAway (R := Γ(X, D)) (A := F.obj (op D))
    (R' := Γ(X, X.basicOpen fD)) (A' := F.obj (op (X.basicOpen fD))) fD
    ((F.map (homOfLE hDV).op).hom '' T) ((F.map (homOfLE hDW).op).hom a) (by
      have h0 := ha _ hD' hD'f hD'V
      rw [hres, gen_eq_adjoin] at h0
      change (F.map (homOfLE hD'D).op).hom ((F.map (homOfLE hDW).op).hom a) ∈ _
      rw [hres, Set.image_image]
      have hfun : (fun x => (algebraMap (F.obj (op D)) (F.obj (op (X.basicOpen fD))))
          ((F.map (homOfLE hDV).op).hom x)) = ⇑(F.map (homOfLE hD'V).op).hom :=
        funext fun x => hres _ _ x
      rw [hfun]
      exact h0)
  refine ⟨m, ?_⟩
  have hnat : (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f) = (α.app (op D)).hom fD := by
    have := congr($(α.naturality (homOfLE hDW).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  rw [map_mul, map_pow, hnat, gen_eq_adjoin]
  exact hm

end GlobalTheory.QcSub.PowerMultiple

theorem GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by
  intro X hX F α hα ι _ V hV T W hW f a ha
  classical
  haveI := Fintype.ofFinite ι
  rw [mem_sub] at ha
  choose s hs1 hs2 using fun j => GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen X hX W (V j) hW (hV j)
  have hle : ∀ j, ∀ h ∈ s j, X.basicOpen h ≤ V j := by
    intro j h hh
    obtain ⟨r, hr⟩ := hs1 j h hh
    rw [hr]
    exact X.basicOpen_le r
  choose m hm using fun j (h : s j) =>
    GlobalTheory.QcSub.PowerMultiple.res_pow_mul_mem_gen F α hα (hW.basicOpen h.1) (X.basicOpen_le h.1)
      (hle j h.1 h.2) (T j) f a (fun W' hW' h1 h2 => ha j W' hW' h1 h2)
  refine ⟨∑ j, ∑ h : s j, m j h, ?_⟩
  rw [mem_sub]
  intro j W' hW' hWW' hWV
  refine GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) W (T j) _ ?_ W' hW' hWW' hWV
  intro x hx
  have hx' := hs2 j hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx'
  obtain ⟨h, hh, hxh⟩ := hx'
  refine ⟨X.basicOpen h, hW.basicOpen h, hxh, X.basicOpen_le h, hle j h hh, ?_⟩
  have hmle : m j ⟨h, hh⟩ ≤ ∑ j, ∑ h : s j, m j h :=
    le_trans (Finset.single_le_sum (f := fun h' => m j h') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨h, hh⟩ : s j)))
      (Finset.single_le_sum (f := fun j' => ∑ h' : s j', m j' h') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j))
  rw [show ∑ j, ∑ h : s j, m j h = (∑ j, ∑ h : s j, m j h - m j ⟨h, hh⟩) + m j ⟨h, hh⟩ by omega,
    pow_add, mul_assoc, map_mul]
  refine mul_mem ?_ (hm j ⟨h, hh⟩)
  rw [map_pow]
  refine pow_mem ?_ _
  have := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom f)
  simp only [CommRingCat.comp_apply] at this
  rw [← this]
  exact algebraMap_mem_gen F α _ _ _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulMemSubalgebraOfResBasicOpenStatement
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_mem_subalgebra_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by
  first | exact @GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen | exact GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen | (intros; apply GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetsSubalgebraFiniteAffineCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetsSubalgebraFiniteAffineCover
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.SubChoose

theorem exists_num {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {U : X.Opens} (hU : IsAffineOpen U) (h : Γ(X, U)) (z : F.obj (op (X.basicOpen h))) :
    ∃ (a : F.obj (op U)) (n : ℕ), z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a := by
  letI := (F.map (homOfLE (X.basicOpen_le h)).op).hom.toAlgebra
  haveI := isLocalizationAway F α hα hU h
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj ((α.app (op U)).hom h) z
  refine ⟨a, n, ?_⟩
  have nat := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom h)
  simp only [CommRingCat.comp_apply] at nat
  rw [nat]
  exact e

theorem mem_gen_of_eq {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    {U : X.Opens} (h : Γ(X, U)) (T : Set (F.obj (op U))) {a : F.obj (op U)} (ha : a ∈ T)
    (z : F.obj (op (X.basicOpen h))) (n : ℕ)
    (e : z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a) :
    z ∈ gen F α (X.basicOpen_le h) T := by
  have hu0 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) :=
    X.toRingedSpace.isUnit_res_basicOpen h
  obtain ⟨u, hu⟩ := hu0
  have key : (α.app (op (X.basicOpen h))).hom (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) *
      (α.app (op (X.basicOpen h))).hom ↑u⁻¹ = 1 := by
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  have hz : z = (F.map (homOfLE (X.basicOpen_le h)).op).hom a *
      ((α.app (op (X.basicOpen h))).hom ↑u⁻¹) ^ n := by
    rw [← e, mul_assoc, ← mul_pow, key, one_pow, mul_one]
  rw [hz]
  exact mul_mem (res_mem_gen F α _ T ha) (pow_mem (algebraMap_mem_gen F α _ T _) n)

end GlobalTheory.SubChoose

theorem GlobalTheory.sub_choose_finite : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  intro X hX F α hα ι _ V hV S hS
  choose s hs1 hs2 using fun i j => GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen X hX (V j) (V i) (hV j) (hV i)
  have hDi : ∀ i j, ∀ h ∈ s i j, X.basicOpen h ≤ V i := by
    intro i j h hh
    obtain ⟨r, hr⟩ := hs1 i j h hh
    rw [hr]
    exact X.basicOpen_le r
  haveI : ∀ i, Finite (S i) := fun i => (hS i).to_subtype
  choose a n ha using fun (j : ι) (p : Σ i, (S i) × (s i j)) =>
    GlobalTheory.SubChoose.exists_num F α hα (hV j) p.2.2.1
      ((F.map (homOfLE (hDi p.1 j p.2.2.1 p.2.2.2)).op).hom p.2.1.1)
  refine ⟨fun j => Set.range (a j), fun j => Set.finite_range _, ?_⟩
  intro i x hx
  rw [SetLike.mem_coe, mem_sub]
  intro j W' hW' hWi hWj
  apply GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) (V i) (Set.range (a j)) x _ W' hW' hWi hWj
  intro y hy
  have hy' : y ∈ ((V j ⊓ V i : X.Opens) : Set X) := ⟨hy.2, hy.1⟩
  have := hs2 i j hy'
  simp only [Set.mem_iUnion] at this
  obtain ⟨h, hh, hyh⟩ := this
  refine ⟨X.basicOpen h, (hV j).basicOpen h, hyh, hDi i j h hh, X.basicOpen_le h, ?_⟩
  exact GlobalTheory.SubChoose.mem_gen_of_eq F α h _ (Set.mem_range_self (⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩ : Σ i, (S i) × (s i j))) _ _
    (ha j ⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetsSubalgebraFiniteAffineCoverStatement
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_sets_subalgebra_finite_affine_cover : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  first | exact @GlobalTheory.sub_choose_finite | exact GlobalTheory.sub_choose_finite | (intros; apply GlobalTheory.sub_choose_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCutOutSubalgebraQuasiCoherent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLocalizationAwaySpanFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLocalizationAwaySpanFinset
namespace GlobalTheory

open Submodule

theorem fg_localizationAway_span_finset
    {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R)
    [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A']
    (N : Submodule R' A') (hN : N.FG) :
    ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N →
      ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  classical
  obtain ⟨S, rfl⟩ := hN
  have hA : ∀ (c : R) (z : A),
      algebraMap A A' (c • z) = algebraMap R A' c * algebraMap A A' z := by
    intro c z
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  have hsurj : ∀ n : A', ∃ e : A, ∃ k : ℕ,
      n * algebraMap R A' g ^ k = algebraMap A A' e := by
    intro n
    obtain ⟨k, e, h⟩ := IsLocalization.Away.surj (algebraMap R A g) n
    exact ⟨e, k, by rw [IsScalarTower.algebraMap_apply R A A']; exact h⟩
  choose e k he using hsurj
  refine ⟨S.image e, ?_⟩
  have key : ∀ y ∈ Submodule.span R' (S : Set A'), ∃ m : ℕ,
      ∃ z ∈ Submodule.span R ((S.image e : Finset A) : Set A),
        algebraMap A A' z = algebraMap R A' g ^ m * y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      refine ⟨k x, e x, Submodule.subset_span ?_, ?_⟩
      · simp only [Finset.coe_image]
        exact Set.mem_image_of_mem e hx
      · rw [← he, mul_comm]
    | zero => exact ⟨0, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m1, z1, hz1, h1⟩ := hx
      obtain ⟨m2, z2, hz2, h2⟩ := hy
      refine ⟨m1 + m2, g ^ m2 • z1 + g ^ m1 • z2,
        add_mem (smul_mem _ _ hz1) (smul_mem _ _ hz2), ?_⟩
      rw [map_add (f := _), hA, hA, h1, h2, map_pow, map_pow]
      ring
    | smul r' x _ hx =>
      obtain ⟨m, z, hz, h⟩ := hx
      obtain ⟨l, r, hr⟩ := IsLocalization.Away.surj g r'
      refine ⟨m + l, r • z, smul_mem _ _ hz, ?_⟩
      have hr' : algebraMap R A' r = algebraMap R' A' r' * algebraMap R A' g ^ l := by
        rw [IsScalarTower.algebraMap_apply R R' A', ← hr, map_mul, map_pow,
          ← IsScalarTower.algebraMap_apply]
      rw [hA, h, Algebra.smul_def, hr']
      ring
  intro b hb
  obtain ⟨m, z, hz, h⟩ := key _ hb
  have h0 : algebraMap A A' (z - algebraMap R A g ^ m * b) = 0 := by
    rw [map_sub, h, map_mul, map_pow, ← IsScalarTower.algebraMap_apply, sub_self]
  obtain ⟨⟨x, hx⟩, hc⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A g)) A' _).1 h0
  obtain ⟨c, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hx
  refine ⟨c + m, ?_⟩
  have hc' : algebraMap R A g ^ c * (z - algebraMap R A g ^ m * b) = 0 := hc
  have : algebraMap R A g ^ (c + m) * b = g ^ c • z := by
    rw [Algebra.smul_def, map_pow]
    linear_combination -hc'
  rw [this]
  exact smul_mem _ _ hz

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLocalizationAwaySpanFinsetStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (N : Submodule R' A'), N.FG → ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  first | exact @GlobalTheory.fg_localizationAway_span_finset | exact GlobalTheory.fg_localizationAway_span_finset | (intros; apply GlobalTheory.fg_localizationAway_span_finset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleFgOfLocallyLeFg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleFgOfLocallyLeFg
namespace GlobalTheory

theorem submodule_fg_of_locally_le_fg {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] (M : Submodule R A) (s : Set R) (hs : Ideal.span s = ⊤)
    (hE : ∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ,
      algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) : M.FG := by
  classical
  obtain ⟨s0, hs0s, hs0⟩ := (Ideal.span_eq_top_iff_finite s).1 hs
  choose! E hEm using hE
  let T : Set A := ⋃ g ∈ (s0 : Set R), (E g : Set A)
  have hT : T.Finite := Set.Finite.biUnion s0.finite_toSet fun g _ => (E g).finite_toSet
  refine Submodule.FG.of_le (Submodule.fg_span hT) ?_
  intro b hb
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s0 : Set R) hs0 b ?_
  intro g
  obtain ⟨m, hm⟩ := hEm g.1 (hs0s g.2) b hb
  refine ⟨m, ?_⟩
  have hle : Submodule.span R (E g.1 : Set A) ≤ Submodule.span R T :=
    Submodule.span_mono (Set.subset_biUnion_of_mem (u := fun g => (E g : Set A)) g.2)
  have : (g.1 ^ m) • b = algebraMap R A g.1 ^ m * b := by
    rw [Algebra.smul_def, map_pow]
  rw [this]
  exact hle hm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleFgOfLocallyLeFgStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem : ∀ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing R] (M : Submodule R A) (s : Set R), Ideal.span s = ⊤ → (∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) → M.FG := by
  first | exact @GlobalTheory.submodule_fg_of_locally_le_fg | exact GlobalTheory.submodule_fg_of_locally_le_fg | (intros; apply GlobalTheory.submodule_fg_of_locally_le_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCutOutSubalgebraQuasiCoherent
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem subMap_finite (X : Scheme.{0}) (_hX : IsNoetherian X) (F : X.Opensᵒᵖ ⥤ CommRingCat)
    (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    (hint : ∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral)
    {ι : Type} (V : ι → X.Opens) (_hV : ∀ j, IsAffineOpen (V j)) (hcov : ∀ x : X, ∃ j, x ∈ V j)
    (T : ∀ j, Set (F.obj (op (V j)))) (hT : ∀ j, (T j).Finite) (W : X.Opens)
    (hW : IsAffineOpen W) : (subMap F α V T W).Finite := by
  haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI alg : Algebra Γ(X, W) (F.obj (op W)) := (α.app (op W)).hom.toAlgebra
  let S : Subalgebra Γ(X, W) (F.obj (op W)) :=
    { sub F α V T W with algebraMap_mem' := algebraMap_mem_sub F α V T W }
  let s : Set Γ(X, W) := {g | ∃ j, X.basicOpen g ≤ V j}
  have hs : Ideal.span s = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨g, hg, hxg⟩ := hW.exists_basicOpen_le (V := V j) ⟨x, hj⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, j, hg⟩, hxg⟩
  have hloc : ∀ g ∈ s, ∃ E : Finset (F.obj (op W)), ∀ b ∈ S.toSubmodule, ∃ m : ℕ,
      algebraMap Γ(X, W) (F.obj (op W)) g ^ m * b ∈ Submodule.span Γ(X, W) (E : Set _) := by
    rintro g ⟨j, hj⟩
    have hD : IsAffineOpen (X.basicOpen g) := hW.basicOpen g
    letI a1 : Algebra Γ(X, W) Γ(X, X.basicOpen g) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    letI a2 : Algebra Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      (α.app (op (X.basicOpen g))).hom.toAlgebra
    letI a3 : Algebra (F.obj (op W)) (F.obj (op (X.basicOpen g))) :=
      (F.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    letI a4 : Algebra Γ(X, W) (F.obj (op (X.basicOpen g))) :=
      ((α.app (op (X.basicOpen g))).hom.comp
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).toAlgebra
    haveI : IsScalarTower Γ(X, W) (F.obj (op W)) (F.obj (op (X.basicOpen g))) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ by
        have := congr($(α.naturality (homOfLE (X.basicOpen_le g)).op).hom r)
        simp only [CommRingCat.comp_apply] at this
        exact this
    haveI : IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ rfl
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) := hW.isLocalization_basicOpen g
    haveI : IsLocalization.Away (algebraMap Γ(X, W) (F.obj (op W)) g)
        (F.obj (op (X.basicOpen g))) := isLocalizationAway F α hα hW g
    let N : Submodule Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      (Algebra.adjoin Γ(X, X.basicOpen g) ((F.map (homOfLE hj).op).hom '' T j)).toSubmodule
    have hN : N.FG := fg_adjoin_of_finite ((hT j).image _) (fun x _ ↦ hint _ hD x)
    obtain ⟨E, hE⟩ := GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway (R := Γ(X, W)) (A := F.obj (op W)) (R' := Γ(X, X.basicOpen g))
      (A' := F.obj (op (X.basicOpen g))) g N hN
    refine ⟨E, fun b hb ↦ hE b ?_⟩
    have := (mem_sub F α V T).mp hb j (X.basicOpen g) hD (X.basicOpen_le g) hj
    rw [gen_eq_adjoin] at this
    exact this
  have hfg : S.toSubmodule.FG := GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem S.toSubmodule s hs hloc
  letI := (subMap F α V T W).toAlgebra
  have hfin : Module.Finite Γ(X, W) S.toSubmodule := Module.Finite.iff_fg.mpr hfg
  let e : S.toSubmodule ≃ₗ[Γ(X, W)] sub F α V T W :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact Module.Finite.equiv e

end GlobalTheory.QcSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCutOutSubalgebraQuasiCoherentStatement
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral) → ∀ {ι : Type} (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → (∀ x : X, ∃ j, x ∈ V j) → ∀ (T : ∀ j, Set (F.obj (op (V j)))), (∀ j, (T j).Finite) → ∀ W : X.Opens, IsAffineOpen W → (subMap F α V T W).Finite := by
  first | exact @GlobalTheory.QcSub.subMap_finite | exact GlobalTheory.QcSub.subMap_finite | (intros; apply GlobalTheory.QcSub.subMap_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoequifiberedGeneratedSubalgebraQuasiCoherent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoequifiberedGeneratedSubalgebraQuasiCoherent
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem isLocalizationAway_subring {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A')
    (S : Subring A) (S' : Subring A') (hρ : ∀ a ∈ S, ρ a ∈ S') (s : A) (hs : s ∈ S)
    (hloc : letI := ρ.toAlgebra; IsLocalization.Away s A')
    (hu : ∃ v ∈ S', ρ s * v = 1) (hd : ∀ a : A, ρ a ∈ S' → ∃ m : ℕ, s ^ m * a ∈ S) :
    (letI := (ρ.restrict S S' hρ).toAlgebra
     IsLocalization.Away (⟨s, hs⟩ : S) S') := by
  let := ρ.toAlgebra
  let := (ρ.restrict S S' hρ).toAlgebra
  refine .mk _ ?_ (fun z ↦ ?_) fun a b hab ↦ ?_
  · obtain ⟨v, hv, hsv⟩ := hu
    exact .of_mul_eq_one (⟨v, hv⟩ : S') (Subtype.ext hsv)
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := A') s (z : A')
    have ha' : ρ a = (z : A') * ρ s ^ n := ha.symm
    have hmem : ρ a ∈ S' := ha' ▸ S'.mul_mem z.2 (S'.pow_mem (hρ s hs) n)
    obtain ⟨m, hm⟩ := hd a hmem
    refine ⟨n + m, ⟨s ^ m * a, hm⟩, Subtype.ext ?_⟩
    change (z : A') * ρ s ^ (n + m) = ρ (s ^ m * a)
    rw [map_mul, map_pow, ha', pow_add]
    ring
  · have h : ρ a = ρ b := congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') s (a := (a : A)) (b := (b : A)) h
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

end GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem coequifibered_subNat (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))
    (hd : ∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) →
      ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) :
    (subNat F α V T).Coequifibered := by
  rw [Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  have hloc := Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp hα U f
  have hnat : (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) =
      (α.app (op (X.basicOpen f))).hom ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) := by
    have := congr($(α.naturality (homOfLE (X.basicOpen_le f)).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  have hu : ∃ v ∈ sub F α V T (X.basicOpen f),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) * v = 1 := by
    obtain ⟨w, hw⟩ : ∃ w : Γ(X, X.basicOpen f),
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f * w = 1 :=
      (X.toRingedSpace.isUnit_res_basicOpen f).exists_right_inv
    refine ⟨(α.app (op (X.basicOpen f))).hom w, algebraMap_mem_sub F α V T _ w, ?_⟩
    rw [hnat, ← map_mul, hw, map_one]
  exact isLocalizationAway_subring (F.map (homOfLE (X.basicOpen_le f)).op).hom
    (sub F α V T U.1) (sub F α V T (X.basicOpen f)) (fun a ha ↦ res_mem_sub F α V T _ ha)
    _ (algebraMap_mem_sub F α V T U.1 f) hloc hu (hd U.1 U.2 f)

end GlobalTheory.QcSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoequifiberedGeneratedSubalgebraQuasiCoherentStatement
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j)))), (∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) → (subNat F α V T).Coequifibered := by
  first | exact @GlobalTheory.QcSub.coequifibered_subNat | exact GlobalTheory.QcSub.coequifibered_subNat | (intros; apply GlobalTheory.QcSub.coequifibered_subNat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoequifiberedSubalgebra
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem exists_finite_coequifibered_subalgebra : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (Opposite.op U)).hom.IsIntegral) → ∀ (n : ℕ) (U : Fin n → X.AffineZariskiSite) (S : ∀ k, Finset (F.obj (Opposite.op (U k).1))), ∃ (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α' : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (ι : F' ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F), α'.Coequifibered ∧ α' ≫ ι = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α ∧ (∀ V, Function.Injective (ι.app V).hom) ∧ (∀ V, (α'.app V).hom.Finite) ∧ ∀ k, ∀ x ∈ S k, ∃ y, (ι.app (Opposite.op (U k))).hom y = x := by
  intro X hX F α hα hint n U S
  obtain ⟨t, ht⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun A : X.AffineZariskiSite => (A.1 : Set X)) (fun A => A.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  let V : Fin n ⊕ t → X.Opens := Sum.elim (fun k => (U k).1) (fun A => A.1.1)
  have hV : ∀ j, IsAffineOpen (V j) := by
    rintro (k | A)
    exacts [(U k).2, A.1.2]
  have hcov : ∀ x : X, ∃ j, x ∈ V j := by
    intro x
    obtain ⟨A, hA, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨.inr ⟨A, hA⟩, hx⟩
  let S' : ∀ j, Set (F.obj (op (V j))) := fun j =>
    Sum.rec (motive := fun j => Set (F.obj (op (V j)))) (fun k => ((S k : Set (F.obj (op (U k).1))))) (fun _ => ∅) j
  have hS' : ∀ j, (S' j).Finite := by
    rintro (k | A)
    exacts [(S k).finite_toSet, Set.finite_empty]
  obtain ⟨T, hTfin, hST⟩ := GlobalTheory.T.exists_finite_sets_subalgebra_finite_affine_cover X hX F α hα V hV S' hS'
  refine ⟨subFunctor F α V T, subNat F α V T, subIncl F α V T,
    GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent X F α hα V T (GlobalTheory.T.pow_mul_mem_subalgebra_of_res_basicOpen X hX F α hα V hV T), subNat_comp_subIncl F α V T,
    subIncl_injective F α V T,
    fun W => GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent X hX F α hα hint V hV hcov T hTfin W.unop.1 W.unop.2,
    fun k x hx => ⟨⟨x, hST (.inl k) (Finset.mem_coe.mpr hx)⟩, rfl⟩⟩

end GlobalTheory.QcSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoequifiberedSubalgebraStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_coequifibered_subalgebra_alt : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (Opposite.op U)).hom.IsIntegral) → ∀ (n : ℕ) (U : Fin n → X.AffineZariskiSite) (S : ∀ k, Finset (F.obj (Opposite.op (U k).1))), ∃ (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α' : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (ι : F' ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F), α'.Coequifibered ∧ α' ≫ ι = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α ∧ (∀ V, Function.Injective (ι.app V).hom) ∧ (∀ V, (α'.app V).hom.Finite) ∧ ∀ k, ∀ x ∈ S k, ∃ y, (ι.app (Opposite.op (U k))).hom y = x := by
  first | exact @GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra | exact GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra | (intros; apply GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra <;> assumption)
end
