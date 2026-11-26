module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjOfDescendedData
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaDescent

theorem map_prod_pow {M N : Type*} [Monoid M] [Monoid N] (P : M →* N) {n : ℕ} (p : Fin n → M) (a : Fin n → ℕ) :
    P (List.ofFn fun i => p i ^ a i).prod = (List.ofFn fun i => P (p i) ^ a i).prod := by
  simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_pow]

theorem existsUnique_transfer {M M₀ N C : Type*} [Monoid M] [Monoid M₀] [Monoid N] (P : M →* N) (R : M₀ →* N)
    (hP : Function.Bijective P) (hR : Function.Injective R) {n : ℕ} (p : Fin n → M) (p₀ : Fin n → M₀)
    (h : ∀ i, P (p i) = R (p₀ i)) (k : ℕ) (e : C → Fin n → ℕ)
    (H : ∀ y : M, y ^ k = 1 → ∃! c : C, (List.ofFn fun i => p i ^ e c i).prod = y)
    (y₀ : M₀) (hy : y₀ ^ k = 1) : ∃! c : C, (List.ofFn fun i => p₀ i ^ e c i).prod = y₀ := by
  obtain ⟨y, hyR⟩ := hP.2 (R y₀)
  have hyk : y ^ k = 1 := hP.1 (by rw [map_pow, hyR, ← map_pow, hy, map_one, map_one])
  have key : ∀ c : C, (List.ofFn fun i => p₀ i ^ e c i).prod = y₀ ↔ (List.ofFn fun i => p i ^ e c i).prod = y := by
    intro c
    rw [← hR.eq_iff, ← hP.1.eq_iff, hyR, map_prod_pow, map_prod_pow]
    simp only [h]
  simpa only [key] using H y hyk

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pushHom_left (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') :
    (pushHom h T x).left = x.left ≫ φ := rfl

theorem pushHom_bijective (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have e := congrArg (fun u => u.left) hxy
    simp only [pushHom_left] at e
    exact Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w x, Over.w y]))
  · refine ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), ?_⟩
    ext1
    rw [pushHom_left]
    exact h.1.lift_fst _ _ _

theorem preHom_injective {T T' : Over S} (U : T' ⟶ T) [Epi U.left] :
    Function.Injective (preHom (G := G) U) := by
  intro x y hxy
  ext1
  rw [← cancel_epi U.left, ← Over.comp_left, ← Over.comp_left]
  exact congrArg (fun u => u.left) hxy

theorem weilIs_congr {Z : Scheme.{0}} {s s' : Z ⟶ S} (e : s = s') (L : LB G.left) (k : ℤ)
    (x y : Over.mk s ⟶ G) (x' y' : Over.mk s' ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(Z, ⊤)ˣ) : Out.WeilIs G L k x y c ↔ Out.WeilIs G L k x' y' c := by
  subst e
  obtain rfl : x = x' := Over.OverMorphism.ext hx
  obtain rfl : y = y' := Over.OverMorphism.ext hy
  exact Iff.rfl

theorem unitS_spMap {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) (n : ℤ) :
    unitS (spMap β) u ^ n = unitOn (Units.map β.toMonoidHom u ^ n) := by
  unfold unitS unitOn
  simp only [← map_zpow]
  ext1
  simp only [Units.coe_map]
  exact (congrArg (fun g => CommRingCat.Hom.hom g ((u ^ n : oˣ) : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem epi_spMap {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) : Epi (spMap j) := by
  have := (GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K Ω j).1 (Sp K) (Sp Ω) (𝟙 _) (𝟙 _) (spMap j)
    (IsPullback.of_vert_isIso ⟨by simp⟩)
  exact this.1

end GlobalTheory.ThetaDescent

namespace GlobalTheory

open ThetaDescent

theorem exists_thetaObj_of_descended_data : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (β : o →+* K) (t : TObj g k J b (spMap β)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : t.A.left ⟶ A₀.left) (L₀ : LB A₀.left) (pt₀ : Fin (2 * g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (act₀ : J → (A₀ ⟶ A₀)), i.comp β₀ = β → IsGrpPullback t.A A₀ (spMap i) φ → L₀.IsLB → LBIso t.L (L₀.pull φ) → (∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) → (∀ j, (t.act j).left ≫ φ = φ ≫ (act₀ j).left) → ∃ t₀ : TObj g k J b (spMap β₀), TMap t t₀ (spMap i) := by
  intro o _ g k J b K₀ K _ _ i β₀ β t A₀ _ φ L₀ pt₀ act₀ hβ hpb hL₀ hLiso hpt hact
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_scheme_descent_smooth_dimension K₀ K i A₀ t.A φ hpb t.ab
  obtain ⟨hrig, hsym, hkt⟩ := GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt K₀ K i A₀ t.A φ L₀ t.L hab hpb hL₀ t.isLB hLiso
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₀ K i A₀ t.A φ L₀ t.L hab hpb hL₀ t.isLB hLiso t.ample
  have hmon := (GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i).2
  refine ⟨{ A := A₀, ab := hab, dim := hdim g t.dim, L := L₀, isLB := hL₀
            rigid := hrig t.rigid, sym := hsym (TObj.sym t), ample := hamp, ktriv := hkt t.ktriv
            pt := pt₀, torsion := ?_, bij := ?_, pairing := ?_, act := act₀
            hom := fun j => (hmon A₀ A₀ t.A t.A φ φ (act₀ j) (t.act j) hpb hpb (hact j).symm).1 (t.hom j) },
    φ, hpb, hLiso, hpt, hact⟩
  ·
    intro a
    obtain ⟨U0, hU0⟩ : ∃ U0 : Over.mk ((Out.baseOver (Sp K)).hom ≫ spMap i) ⟶ Out.baseOver (Sp K₀),
        U0.left = spMap i := ⟨Over.homMk (spMap i) (by simp), rfl⟩
    have hE : Epi U0.left := by rw [hU0]; exact epi_spMap i
    apply preHom_injective U0
    have e1 : preHom U0 (pt₀ a) = pushHom hpb _ (t.pt a) := by
      ext1
      show (U0 ≫ pt₀ a).left = _
      rw [Over.comp_left, hU0, pushHom_left, hpt a]
    rw [map_pow, map_one, e1, ← map_pow, t.torsion a, map_one]
  ·
    intro K' _ _ x y hy
    obtain ⟨χ, rfl⟩ : ∃ χ : K₀ →+* K', spMap χ = x := ⟨(Spec.preimage x).hom, by
      show Spec.map (CommRingCat.ofHom _) = x
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    obtain ⟨Ω, _, _, jK, jL, hcomm⟩ : ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (jK : K →+* Ω) (jL : K' →+* Ω),
        jK.comp i = jL.comp χ := by
      let _ : Algebra K₀ K := i.toAlgebra
      let _ : Algebra K₀ K' := χ.toAlgebra
      have : Nontrivial (K ⊗[K₀] K') :=
        Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K K' i.injective χ.injective
      obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
      let _ := Ideal.Quotient.field m
      refine ⟨AlgebraicClosure (K ⊗[K₀] K' ⧸ m), inferInstance, inferInstance,
        ((algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)).comp
          (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').toRingHom,
        ((algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)).comp
          (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').toRingHom, ?_⟩
      ext r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      have h1 := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').commutes r
      have h2 := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').commutes r
      exact congrArg (fun z => algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))
        (Ideal.Quotient.mk m z)) (h1.trans h2.symm)
    have hw : spMap jL ≫ spMap χ = spMap jK ≫ spMap i := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
    have hE : Epi (Over.Hom.left (Over.homMk (spMap jL) hw :
        Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ))) := epi_spMap jL
    refine existsUnique_transfer (pushHom hpb (Over.mk (spMap jK)))
      (preHom (G := A₀) (Over.homMk (spMap jL) hw : Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ)))
      (pushHom_bijective hpb _) (preHom_injective _)
      (fun a => (Over.homMk (spMap jK) (by simp) : Over.mk (spMap jK) ⟶ Out.baseOver (Sp K)) ≫ t.pt a)
      (fun a => (Over.homMk (spMap χ) (by simp) : Over.mk (spMap χ) ⟶ Out.baseOver (Sp K₀)) ≫ pt₀ a)
      ?_ k (fun (c : Ix g k) a => (c a).val) (fun z hz => t.bij Ω (spMap jK) z hz) y hy
    intro a
    ext1
    rw [pushHom_left]
    show ((Over.homMk (spMap jK) (by simp) : Over.mk (spMap jK) ⟶ Out.baseOver (Sp K)) ≫ t.pt a).left ≫ φ = ((Over.homMk (spMap jL) hw : Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ)) ≫
      (Over.homMk (spMap χ) (by simp) : Over.mk (spMap χ) ⟶ Out.baseOver (Sp K₀)) ≫ pt₀ a).left
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]
    rw [hpt a, ← Category.assoc, ← Category.assoc, hw]
  ·
    intro a a'
    subst hβ
    have := t.ab.comm
    have h1 := (GlobalTheory.weilIs_grpPullback_of_comm' (Sp K₀) (Sp K) A₀ t.A (spMap i) φ L₀ t.L hL₀ t.isLB hpb hLiso
      (Out.baseOver (Sp K)) (k : ℤ) (t.pt a) (t.pt a') (pushHom hpb _ (t.pt a)) (pushHom hpb _ (t.pt a')) _
      (pushHom_left hpb _ _) (pushHom_left hpb _ _)).1 (t.pairing a a')
    have e1 : unitS (spMap (i.comp β₀)) b.ζ ^ (Out.stdSymp g a a') =
        unitOn (Units.map i.toMonoidHom (Units.map β₀.toMonoidHom b.ζ ^ (Out.stdSymp g a a'))) := by
      rw [unitS_spMap, map_zpow]
      rfl
    rw [e1] at h1
    have hxa : ∀ c, (pushHom hpb (Out.baseOver (Sp K)) (t.pt c)).left =
        ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K₀)) ⟶ Over.mk (𝟙 (Sp K₀))) ≫ pt₀ c).left := by
      intro c
      rw [pushHom_left, hpt c]
      rfl
    have h2 := (weilIs_congr (s' := spMap i ≫ 𝟙 (Sp K₀)) (by simp) L₀ (k : ℤ) _ _ _ _ (hxa a) (hxa a') _).1 h1
    have h3 := (GlobalTheory.T.weilPairing_fieldExtension_iff (Sp K₀) A₀ K₀ K i (𝟙 _) L₀ k (pt₀ a) (pt₀ a')
      (Units.map β₀.toMonoidHom b.ζ ^ Out.stdSymp g a a') hab hL₀).1 h2
    rw [unitS_spMap]
    exact h3

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ThetaDescent

def gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) : Subfield K :=
  Subfield.closure (Set.range β ∪ s)

theorem gen_mono {o K : Type} [CommRing o] [Field K] (β : o →+* K) {s s' : Finset K} (h : s ⊆ s') :
    gen β s ≤ gen β s' :=
  Subfield.closure_mono (Set.union_subset_union_right _ (Finset.coe_subset.2 h))

theorem subset_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) {s s' : Finset K} (h : s ⊆ s') :
    (s : Set K) ⊆ gen β s' :=
  fun _ hx => Subfield.subset_closure (Or.inr (h hx))

theorem mem_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) (a : o) : β a ∈ gen β s :=
  Subfield.subset_closure (Or.inl ⟨a, rfl⟩)

theorem countable_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) [Countable o] :
    Countable (gen β s) := by
  have hc : (Set.range β ∪ (s : Set K)).Countable := (Set.countable_range β).union s.countable_toSet
  rw [← Cardinal.mk_le_aleph0_iff]
  refine (Subfield.cardinalMk_closure_le_max _).trans ?_
  exact max_le (Cardinal.mk_le_aleph0_iff.2 hc.to_subtype) le_rfl

theorem spMap_subtype {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

theorem isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem descends_of
    (hproj : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype))
    (hmor : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀)
    (hgrp : ∀ (K : Type) [Field K] (K₀ : Subfield K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ A₀.left) [QuasiCompact A₀.hom] [QuasiSeparated A₀.hom] [LocallyOfFinitePresentation A₀.hom], IsPullback φ A.hom A₀.hom (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (A₁ : Over (Sp K₁)) (φ₁ : A₁.left ⟶ A₀.left) (ψ : A.left ⟶ A₁.left), IsPullback φ₁ A₁.hom A₀.hom (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype → ∃ _ : GrpObj A₁, IsGrpPullback A A₁ (spMap K₁.subtype) ψ)
    (hlb : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) [QuasiCompact p₀] [QuasiSeparated p₀] (L : LB X), L.IsLB → IsPullback φ p p₀ (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ L₁ : LB X₁, L₁.IsLB ∧ LBIso L (L₁.pull ψ))
    (hobj : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (β : o →+* K) (t : TObj g k J b (spMap β)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : t.A.left ⟶ A₀.left) (L₀ : LB A₀.left) (pt₀ : Fin (2 * g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (act₀ : J → (A₀ ⟶ A₀)), i.comp β₀ = β → IsGrpPullback t.A A₀ (spMap i) φ → L₀.IsLB → LBIso t.L (L₀.pull φ) → (∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) → (∀ j, (t.act j).left ≫ φ = φ ≫ (act₀ j).left) → ∃ t₀ : TObj g k J b (spMap β₀), TMap t t₀ (spMap i)) :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) := by
  intro o _ g k J b _ K _ β t
  classical
  obtain ⟨s₀, H₀⟩ := hproj K (gen β ∅) t.A.left t.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple t.ample)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ (gen β s₀) (gen_mono β (Finset.empty_subset _)) (subset_gen β le_rfl)
  have : IsProper p₀ := isProper_of_isProjOver hp₀
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := hgrp K (gen β s₀) (Over.mk p₀) t.A φ sq
  obtain ⟨s₂, H₂⟩ := hlb K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ t.L t.isLB sq
  obtain ⟨s₃, H₃⟩ := hmor K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ X₀ p₀ J (fun j => (t.act j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := hmor K (gen β s₀) (Sp (gen β s₀)) (Sp K) (𝟙 _) (𝟙 _) (spMap (gen β s₀).subtype) X₀ p₀
    (Fin (2 * g)) (fun a => (t.pt a).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun a => by
      have e : (t.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt a)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  have h : gen β s₀ ≤ gen β s := gen_mono β (fun x hx => by simp [s, hx])
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp (gen β s)) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : t.A.left ⟶ A₁.left := sq₁.lift φ (t.A.hom ≫ spMap (gen β s).subtype)
    (by rw [Category.assoc, spMap_subtype h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = t.A.hom ≫ spMap (gen β s).subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) (Sp (gen β s)) (𝟙 _) inc
    (spMap (gen β s).subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype h) (by simp)
  let act₁ : J → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : Fin (2 * g) → (Out.baseOver (Sp (gen β s)) ⟶ A₁) := fun a =>
    Over.homMk (sq₁.lift (x₁ a) (𝟙 _) (by rw [(hx₁ a).2]; simp)) (sq₁.lift_snd _ _ _)
  let β₁ : o →+* gen β s := β.codRestrict _ (mem_gen β s)
  have hβ : (gen β s).subtype.comp β₁ = β := rfl
  obtain ⟨t₀, ht₀⟩ := hobj o g k J b (gen β s) K (gen β s).subtype β₁ β t A₁ ψ L₁ pt₁ act₁ hβ hG hL₁ hL
    (fun a => by
      have e : (t.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt a)
      have e₁ : (pt₁ a).left ≫ φ₁ = x₁ a := sq₁.lift_fst _ _ _
      have e₂ : (pt₁ a).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
      apply sq₁.hom_ext
      · rw [Category.assoc, hψ₁]
        exact ((hx₁ a).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
      · rw [Category.assoc, hψ₂, ← Category.assoc, e]
        refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        exact ((congrArg _ e₂).trans (Category.comp_id _)).symm)
    (fun j => by
      have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
      apply sq₁.hom_ext
      · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
      · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂])
  exact ⟨gen β s, β₁, t₀, hβ, fun _ => countable_gen β s, ⟨s, rfl⟩, ht₀⟩

theorem descends_to_fg_subfield :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) :=
  descends_of (@GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield) (@GlobalTheory.T.exists_descent_of_morphisms_to_subfield) (@GlobalTheory.grpObj_descends_to_large_subfield) (@GlobalTheory.T.exists_lineBundle_descent_to_subfield) (@GlobalTheory.exists_thetaObj_of_descended_data)

end GlobalTheory.ThetaDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_object_descends_fg_subfield : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) := by
  first | exact @GlobalTheory.ThetaDescent.descends_to_fg_subfield | exact GlobalTheory.ThetaDescent.descends_to_fg_subfield | (intros; apply GlobalTheory.ThetaDescent.descends_to_fg_subfield <;> assumption)
end
