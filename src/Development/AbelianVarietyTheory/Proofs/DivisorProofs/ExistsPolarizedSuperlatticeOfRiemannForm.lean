module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSuperlatticeOfRiemannForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSuperlatticeOfRiemannForm
set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnimodOver

open Module

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_basis (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℝ V), Submodule.span ℤ (Set.range b) = Λ := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  let b := (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivFin _)
  exact ⟨_, b.ofZLatticeBasis ℝ Λ, b.ofZLatticeBasis_span ℝ Λ⟩

theorem discrete_dual (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    DiscreteTopology (B.dualSubmodule Λ) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis Λ hs
  rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b]
  infer_instance

theorem discrete_of_le {L M : Submodule ℤ V} [DiscreteTopology M] (h : L ≤ M) :
    DiscreteTopology L :=
  DiscreteTopology.of_continuous_injective (continuous_inclusion h) (Set.inclusion_injective h)

theorem span_of_le {L M : Submodule ℤ V} (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    Submodule.span ℝ (M : Set V) = ⊤ := by
  rw [eq_top_iff, ← hs]
  exact Submodule.span_mono h

theorem exists_nsmul_mem {L M : Submodule ℤ V} [DiscreteTopology M]
    (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ M, N • x ∈ L := by
  haveI := discrete_of_le h
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : IsZLattice ℝ M := ⟨span_of_le hs h⟩
  have hr : finrank ℤ (L.comap M.subtype) = finrank ℤ M := by
    rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq, ZLattice.rank ℝ L, ZLattice.rank ℝ M]
  haveI hfin : Finite (M ⧸ L.comap M.subtype) := Submodule.finiteQuotientOfFreeOfRankEq _ hr
  refine ⟨Nat.card (M ⧸ L.comap M.subtype), Nat.card_pos, fun x hx => ?_⟩
  have h1 := (L.comap M.subtype).toAddSubgroup.nsmul_index_mem ⟨x, hx⟩
  exact h1

theorem exists_selfDual (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ M : Submodule ℤ V, Λ ≤ M ∧ M ≤ B.dualSubmodule Λ ∧ B.dualSubmodule M = M := by
  haveI := discrete_dual B hB Λ hs
  set D := B.dualSubmodule Λ with hD
  haveI : IsZLattice ℝ D := ⟨span_of_le hs hint⟩
  haveI : IsNoetherian ℤ D := inferInstance
  have anti : ∀ {L M : Submodule ℤ V}, L ≤ M → B.dualSubmodule M ≤ B.dualSubmodule L :=
    fun h _ hy x hx => hy x (h hx)
  obtain ⟨M, ⟨h1, h2⟩, hmax⟩ := (set_has_maximal_iff_noetherian.2 this)
    {M : Submodule ℤ D | Λ ≤ M.map D.subtype ∧
      M.map D.subtype ≤ B.dualSubmodule (M.map D.subtype)}
    ⟨Λ.comap D.subtype, by
      simp only [Set.mem_setOf_eq, Submodule.map_comap_subtype, inf_eq_right.2 hint]
      exact ⟨le_rfl, hint⟩⟩
  refine ⟨M.map D.subtype, h1, Submodule.map_subtype_le _ _, le_antisymm ?_ h2⟩
  intro w hw
  have hwD : w ∈ D := anti h1 hw
  have hle : M ≤ M ⊔ Submodule.span ℤ {⟨w, hwD⟩} := le_sup_left
  have heq : M = M ⊔ Submodule.span ℤ {⟨w, hwD⟩} := by
    by_contra hne
    refine hmax _ ⟨h1.trans (Submodule.map_mono hle), ?_⟩ (lt_of_le_of_ne hle hne)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx₂
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy₂
    have e1 := h2 ⟨x₁, hx₁, rfl⟩ _ ⟨y₁, hy₁, rfl⟩
    have e2 := hw _ ⟨y₁, hy₁, rfl⟩
    have e3 := hw _ ⟨x₁, hx₁, rfl⟩
    have e4 : B (x₁ : V) w = - B w (x₁ : V) := (hA.neg_eq _ _).symm
    have e5 : B w w = 0 := hA w
    have e6 : B (D.subtype (x₁ + a • ⟨w, hwD⟩)) (D.subtype (y₁ + c • ⟨w, hwD⟩)) =
        B (D.subtype x₁) (D.subtype y₁) + a • B w (D.subtype y₁) - c • B w (D.subtype x₁) := by
      simp only [Submodule.subtype_apply, Submodule.coe_add, Submodule.coe_smul, map_add (f := _), map_zsmul,
        LinearMap.add_apply, LinearMap.smul_apply, e4, e5, smul_zero, smul_neg, add_zero]
      ring
    rw [e6]
    exact sub_mem (add_mem e1 (Submodule.smul_mem _ _ e2)) (Submodule.smul_mem _ _ e3)
  have : (⟨w, hwD⟩ : D) ∈ M := by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  exact ⟨_, this, rfl⟩

theorem dualSubmoduleToDual_surjective (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    Function.Surjective (B.dualSubmoduleToDual Λ) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis Λ hs
  have hbmem : ∀ i, b i ∈ Λ := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  intro φ
  set y : V := ∑ i, (φ ⟨b i, hbmem i⟩ : ℤ) • B.dualBasis hB b i with hy
  have hymem : y ∈ B.dualSubmodule Λ := by
    rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hLI : LinearIndependent ℤ b := b.linearIndependent.restrict_scalars' ℤ
  let bΛ : Module.Basis (Fin n) ℤ Λ := (Module.Basis.span hLI).map (LinearEquiv.ofEq _ _ hb)
  have hbΛ : ∀ i, (bΛ i : V) = b i := fun i => by simp [bΛ, Module.Basis.span_apply]
  refine ⟨⟨y, hymem⟩, bΛ.ext fun j => ?_⟩
  apply Int.cast_injective (α := ℝ)
  have hspec := LinearMap.BilinForm.dualSubmoduleParing_spec B ⟨y, hymem⟩ (bΛ j)
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at hspec
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply, hspec]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hbΛ, hy, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
    LinearMap.BilinForm.apply_dualBasis_left, smul_ite, smul_zero, zsmul_eq_mul, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 2
  exact Subtype.ext (hbΛ j).symm

theorem exists_unimodular (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ (M : Submodule ℤ V) (N : ℕ) (Ef : LinearMap.BilinForm ℤ M),
      Λ ≤ M ∧ 0 < N ∧ (∀ x ∈ M, N • x ∈ Λ) ∧ DiscreteTopology M ∧
      Submodule.span ℝ (M : Set V) = ⊤ ∧ (∀ a b : M, (Ef a b : ℝ) = B a b) ∧
      Function.Bijective Ef := by
  obtain ⟨M, h1, h2, h3⟩ := exists_selfDual B hB hA Λ hs hint
  haveI := discrete_dual B hB Λ hs
  haveI : DiscreteTopology M := discrete_of_le h2
  have hsM := span_of_le hs h1
  obtain ⟨N, hN, hNM⟩ := exists_nsmul_mem hs h1
  let e := LinearEquiv.ofEq _ _ h3.symm
  refine ⟨M, N, (B.dualSubmoduleToDual M).comp e.toLinearMap, h1, hN, hNM, this, hsM, ?_, ?_⟩
  · intro a b
    exact B.dualSubmoduleParing_spec (e a) b
  · exact Function.Bijective.comp (g := B.dualSubmoduleToDual M) (f := e)
      ⟨B.dualSubmoduleToDual_injective hB M hsM, dualSubmoduleToDual_surjective B hB M hsM⟩
      e.bijective

end General

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ Hm.mulVec (star w)).im)
    (fun a b w => by simp [add_dotProduct])
    (fun r a w => by simp [smul_dotProduct])
    (fun a b w => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun r a w => by simp [Matrix.mulVec_smul, dotProduct_smul])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (z ⬝ᵥ Hm.mulVec (star w)).im := rfl

theorem imForm_isAlt {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) :
    (imForm Hm).IsAlt := by
  have key : ∀ u : Fin g → ℂ, star (star u ⬝ᵥ Hm.mulVec u) = star u ⬝ᵥ Hm.mulVec u := by
    intro u
    rw [← Matrix.star_dotProduct (Hm.mulVec u) u, Matrix.star_mulVec, h.eq, ← Matrix.dotProduct_mulVec]
  intro z
  rw [imForm_apply]
  have hq := key (star z)
  rw [star_star] at hq
  exact Complex.conj_eq_iff_im.mp hq

theorem imForm_nondegenerate {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) :
    (imForm Hm).Nondegenerate := by
  have hL : ∀ z : Fin g → ℂ, (∀ w, imForm Hm z w = 0) → z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hz (Complex.I • z)
    rw [imForm_apply, star_smul, Complex.star_def, Complex.conj_I, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul] at h1
    have h2 := hp z hne
    simp [Complex.mul_im] at h1
    linarith
  have hR : ∀ w : Fin g → ℂ, (∀ z, imForm Hm z w = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := hw (Complex.I • w)
    rw [imForm_apply, smul_dotProduct, smul_eq_mul] at h1
    have h2 := hp w hne
    simp [Complex.mul_im] at h1
    linarith
  first
    | exact ⟨hL, hR⟩
    | exact hL

theorem exists_unimodular_overlattice :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (N : ℕ) (Ef : LinearMap.BilinForm ℤ Λ₁),
      Λ ≤ Λ₁ ∧ 0 < N ∧ (∀ x ∈ Λ₁, (N : ℂ) • x ∈ Λ) ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧
      (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  intro g Λ Hm hd hs hH hp hint
  obtain ⟨M, N, Ef, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_unimodular (imForm Hm) (imForm_nondegenerate hH hp) (imForm_isAlt hH) Λ hs
      (fun x hx y hy => by
        obtain ⟨n, hn⟩ := hint x hx y hy
        exact Submodule.mem_one.2 ⟨n, by rw [imForm_apply, hn]; simp⟩)
  refine ⟨M, N, Ef, h1, h2, fun x hx => ?_, h4, h5, h6, h7⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact h3 x hx

end GlobalTheory.UnimodOver
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSuperlatticeOfRiemannFormStatement
set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarized_superlattice_of_riemann_form : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (N : ℕ) (Ef : LinearMap.BilinForm ℤ Λ₁),
      Λ ≤ Λ₁ ∧ 0 < N ∧ (∀ x ∈ Λ₁, (N : ℂ) • x ∈ Λ) ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧
      (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  first | exact @GlobalTheory.UnimodOver.exists_unimodular_overlattice | exact GlobalTheory.UnimodOver.exists_unimodular_overlattice | (intros; apply GlobalTheory.UnimodOver.exists_unimodular_overlattice <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFiltered
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFiltered
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem exists_common_under {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    (k : K) (l : I → K) (f : ∀ i, k ⟶ l i) :
    ∃ (m : K) (p : k ⟶ m) (r : ∀ i, l i ⟶ m), ∀ i, f i ≫ r i = p := by
  classical
  letI := Fintype.ofFinite I
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan k l f)
  exact ⟨c'.pt, c'.ι.app none, fun i => c'.ι.app (some i), fun i => c'.w (.init i)⟩

theorem exists_stage_eq {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    {R S : CommRingCat.{0}} (E : K ⥤ CommRingCat.{0}) (α : (Functor.const _).obj R ⟶ E)
    (φ : R ⟶ S) (c : Cocone E) (hc : IsColimit c) (hφ : φ.hom.EssFiniteType) {k : K}
    (a b : I → (S ⟶ E.obj k)) (ha : ∀ i, φ ≫ a i = α.app k) (hb : ∀ i, φ ≫ b i = α.app k)
    (hab : ∀ i, a i ≫ c.ι.app k = b i ≫ c.ι.app k) :
    ∃ (m : K) (p : k ⟶ m), ∀ i, a i ≫ E.map p = b i ≫ E.map p := by
  choose l f₁ f₂ h using fun i => RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit R E α φ c hc
    hφ (a i) (ha i) (b i) (hb i) (hab i)
  obtain ⟨m, p, r, hr⟩ := exists_common_under k (fun i => IsFiltered.coeq (f₁ i) (f₂ i))
    (fun i => f₁ i ≫ IsFiltered.coeqHom (f₁ i) (f₂ i))
  refine ⟨m, p, fun i => ?_⟩
  have h2 : (f₂ i ≫ IsFiltered.coeqHom (f₁ i) (f₂ i)) ≫ r i = p := by
    rw [← IsFiltered.coeq_condition]; exact hr i
  conv_lhs => rw [← hr i]
  conv_rhs => rw [← h2]
  simp only [E.map_comp, Category.assoc]
  rw [reassoc_of% (h i)]

theorem exists_stage_factor {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    {R S : CommRingCat.{0}} (E : K ⥤ CommRingCat.{0}) (α : (Functor.const _).obj R ⟶ E)
    (φ : R ⟶ S) (c : Cocone E) (hc : IsColimit c) (hφ : φ.hom.FinitePresentation)
    (a : I → (S ⟶ c.pt)) (ha : ∀ i k, φ ≫ a i = α.app k ≫ c.ι.app k) :
    ∃ (m : K) (s : I → (S ⟶ E.obj m)), ∀ i, φ ≫ s i = α.app m ∧ s i ≫ c.ι.app m = a i := by
  classical
  choose l s h₁ h₂ using fun i => RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R E α φ c
    hc hφ (a i) (ha i)
  letI := Fintype.ofFinite I
  obtain ⟨m, hm⟩ := IsFiltered.sup_objs_exists (Finset.univ.image l)
  have r : ∀ i, l i ⟶ m := fun i => (hm (Finset.mem_image_of_mem l (Finset.mem_univ i))).some
  refine ⟨m, fun i => s i ≫ E.map (r i), fun i => ⟨?_, ?_⟩⟩
  · rw [reassoc_of% (h₁ i), ← α.naturality]
    exact Category.id_comp _
  · rw [Category.assoc, c.w, ← h₂]

theorem exists_stage_action {K : Type} [SmallCategory K] [IsFiltered K] {G : Type} [Monoid G]
    [Finite G] {R S : CommRingCat.{0}} (P E : K ⥤ CommRingCat.{0})
    (β : ∀ k, R ⟶ P.obj k) (φ : R ⟶ S) (hφ : φ.hom.FinitePresentation)
    (u : P ⟶ E) (v : (Functor.const _).obj S ⟶ E)
    (hpo : ∀ k, IsPushout φ (β k) (v.app k) (u.app k))
    (c : Cocone E) (hc : IsColimit c) (τ : G → (c.pt ⟶ c.pt)) (τ1 : τ 1 = 𝟙 _)
    (τm : ∀ g h, τ (g * h) = τ h ≫ τ g)
    (τu : ∀ g k, u.app k ≫ c.ι.app k ≫ τ g = u.app k ≫ c.ι.app k) :
    ∃ (m : K) (σ : G → (E.obj m ⟶ E.obj m)), σ 1 = 𝟙 _ ∧ (∀ g h, σ (g * h) = σ h ≫ σ g) ∧
      (∀ g, u.app m ≫ σ g = u.app m) ∧ ∀ g, σ g ≫ c.ι.app m = c.ι.app m ≫ τ g := by
  let α : (Functor.const K).obj R ⟶ E := (Functor.const K).map φ ≫ v
  let w : ∀ k, S ⟶ E.obj k := fun k => v.app k
  let ι : ∀ k, E.obj k ⟶ c.pt := fun k => c.ι.app k
  have hα : ∀ k, α.app k = φ ≫ w k := fun k => rfl
  have hι : ∀ {k l} (f : k ⟶ l), E.map f ≫ ι l = ι k := fun f => c.w f
  have hw : ∀ {k l} (f : k ⟶ l), w k ≫ E.map f = w l := fun f =>
    (v.naturality f).symm.trans (Category.id_comp _)
  have hpo' : ∀ k, IsPushout φ (β k) (w k) (u.app k) := hpo
  have τu' : ∀ g k, u.app k ≫ ι k ≫ τ g = u.app k ≫ ι k := τu
  have k₀ : K := IsFiltered.nonempty.some
  have hwι : ∀ k, w k ≫ ι k = w k₀ ≫ ι k₀ := fun k => by
    rw [← hι (IsFiltered.leftToMax k k₀), ← hι (IsFiltered.rightToMax k k₀), reassoc_of% hw,
      reassoc_of% hw]
  obtain ⟨k, s, hs⟩ := exists_stage_factor E α φ c hc hφ (fun g : G => w k₀ ≫ ι k₀ ≫ τ g)
    (fun g k => by
      change φ ≫ w k₀ ≫ ι k₀ ≫ τ g = (φ ≫ w k) ≫ ι k
      rw [← reassoc_of% (hwι k), (hpo' k).w, reassoc_of% (hpo' k).w, τu', Category.assoc])
  have hs1 : ∀ g, φ ≫ s g = φ ≫ w k := fun g => (hs g).1
  have hs2 : ∀ g, s g ≫ ι k = w k₀ ≫ ι k₀ ≫ τ g := fun g => (hs g).2
  let σ : ∀ {l} (_ : k ⟶ l), G → (E.obj l ⟶ E.obj l) := fun {l} f g =>
    (hpo' l).desc (s g ≫ E.map f) (u.app l) (by
      rw [reassoc_of% hs1, hw, (hpo' l).w])
  have σw : ∀ {l} (f : k ⟶ l) g, w l ≫ σ f g = s g ≫ E.map f := fun f g => (hpo' _).inl_desc _ _ _
  have σu : ∀ {l} (f : k ⟶ l) g, u.app l ≫ σ f g = u.app l := fun f g => (hpo' _).inr_desc _ _ _
  have σι : ∀ {l} (f : k ⟶ l) g, σ f g ≫ ι l = ι l ≫ τ g := fun {l} f g => by
    apply (hpo' l).hom_ext
    · rw [reassoc_of% σw, hι, hs2, reassoc_of% (hwι l)]
    · rw [reassoc_of% σu, τu']
  have σmap : ∀ {l} (f : k ⟶ l) g, σ (𝟙 k) g ≫ E.map f = E.map f ≫ σ f g := fun {l} f g => by
    apply (hpo' k).hom_ext
    · rw [reassoc_of% σw, reassoc_of% hw, σw, E.map_id, Category.id_comp]
    · rw [reassoc_of% σu, ← u.naturality_assoc, σu, u.naturality]
  obtain ⟨m, p, hp⟩ := exists_stage_eq (I := Option (G × G)) E α φ c hc
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hφ)) (k := k)
    (fun i => i.elim (s 1) (fun x => s (x.1 * x.2)))
    (fun i => i.elim (w k) (fun x => s x.2 ≫ σ (𝟙 k) x.1))
    (by
      rintro (_ | x)
      · exact hs1 _
      · exact hs1 _)
    (by
      rintro (_ | x)
      · rfl
      · change φ ≫ s x.2 ≫ σ (𝟙 k) x.1 = φ ≫ w k
        rw [reassoc_of% hs1, σw, E.map_id, Category.comp_id, hs1])
    (by
      rintro (_ | x)
      · change s 1 ≫ ι k = w k ≫ ι k
        rw [hs2, τ1, Category.comp_id, hwι k]
      · change s (x.1 * x.2) ≫ ι k = (s x.2 ≫ σ (𝟙 k) x.1) ≫ ι k
        rw [Category.assoc, σι, reassoc_of% hs2, hs2, τm])
  refine ⟨m, σ p, ?_, fun g h => ?_, σu p, σι p⟩
  · apply (hpo' m).hom_ext
    · rw [σw, Category.comp_id, ← hw p]
      exact hp none
    · rw [σu, Category.comp_id]
  · apply (hpo' m).hom_ext
    · rw [σw, reassoc_of% σw, ← σmap, ← Category.assoc]
      exact hp (some (g, h))
    · rw [σu, reassoc_of% σu, σu]

theorem finitePresentation_of_isPushout {R S R' S' : CommRingCat.{0}} {φ : R ⟶ S} {β : R ⟶ R'}
    {v : S ⟶ S'} {u : R' ⟶ S'} (h : IsPushout φ β v u) (hφ : φ.hom.FinitePresentation) :
    u.hom.FinitePresentation := by
  algebraize [φ.hom, β.hom, v.hom, u.hom, v.hom.comp φ.hom]
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have : Algebra.IsPushout R S R' S' := CommRingCat.isPushout_iff_isPushout.1 h
  exact RingHom.finitePresentation_isStableUnderBaseChange R S R' S' hφ

theorem exists_algEquiv_of_isPushout {R C B D : Type} [CommRing R] [CommRing C] [CommRing B]
    [CommRing D] [Algebra R C] [Algebra R B] [Algebra C D] (ι : B →+* D)
    (h : IsPushout (CommRingCat.ofHom (algebraMap R C)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap C D)) (CommRingCat.ofHom ι)) :
    ∃ e : C ⊗[R] B ≃ₐ[C] D, ∀ x y, e (x ⊗ₜ y) = algebraMap C D x * ι y := by
  algebraize [ι, (algebraMap C D).comp (algebraMap R C)]
  have : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have : Algebra.IsPushout R C B D := CommRingCat.isPushout_iff_isPushout.1 h
  exact ⟨Algebra.IsPushout.equiv R C B D, fun x y => Algebra.IsPushout.equiv_tmul R C B D x y⟩

theorem exists_action_model_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  intro J _ _ F c hc q hq j A _ _ _ D _ _ act
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  rintro ⟨e₀⟩
  haveI : NeZero q := ⟨hq.ne'⟩
  let φ : F.obj j ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap (F.obj j) A)
  have hφ : φ.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  let g₀ : c.pt ⟶ CommRingCat.of D := CommRingCat.ofHom (algebraMap c.pt D)
  let h₀ : CommRingCat.of A ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (e₀.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := A)).toRingHom)
  let ιc : ∀ k, F.obj k ⟶ c.pt := fun k => c.ι.app k
  have hsq : IsPushout φ (ιc j) h₀ g₀ := by
    refine (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt A).flip.of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) e₀.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · ext x
      exact e₀.commutes x
  obtain ⟨E, ι, u, v, ⟨hE⟩, hk⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ φ h₀ g₀ hsq
  let τ : Multiplicative (ZMod q) → (CommRingCat.of D ⟶ CommRingCat.of D) := fun g =>
    CommRingCat.ofHom (act g).toRingEquiv.toRingHom
  have hτ : ∀ g, g₀ ≫ τ g = g₀ := fun g => by
    ext x
    exact (act g).commutes x
  let ι' : ∀ k, E.obj k ⟶ CommRingCat.of D := fun k => ι.app k
  let u' : ∀ k : Under j, F.obj k.right ⟶ E.obj k := fun k => u.app k
  let v' : ∀ k : Under j, CommRingCat.of A ⟶ E.obj k := fun k => v.app k
  have hu : ∀ k, u' k ≫ ι' k = ιc k.right ≫ g₀ := fun k => (hk k).2.2
  have hv : ∀ k, v' k ≫ ι' k = h₀ := fun k => (hk k).2.1
  have hpo : ∀ k : Under j, IsPushout φ (F.map k.hom) (v' k) (u' k) := fun k => (hk k).1
  obtain ⟨m, σ, σ1, σm, σu, σι⟩ := exists_stage_action (Under.forget j ⋙ F) E
    (fun k => F.map k.hom) φ hφ u v hpo (Cocone.mk _ ι) hE τ
    (by
      ext x
      change act 1 x = x
      simp)
    (fun g h => by
      ext x
      change act (g * h) x = act g (act h x)
      simp)
    (fun g k => by
      change u' k ≫ ι' k ≫ τ g = u' k ≫ ι' k
      rw [reassoc_of% hu, hτ, hu])
  letI : Algebra (F.obj m.right) (E.obj m) := (u' m).hom.toAlgebra
  letI : Algebra (F.obj m.right) c.pt := (c.ι.app m.right).hom.toAlgebra
  let σ' : Multiplicative (ZMod q) →* (E.obj m →ₐ[F.obj m.right] E.obj m) :=
    { toFun := fun g => ⟨(σ g).hom, fun x => congr(($(σu g)).hom x)⟩
      map_one' := AlgHom.ext fun x => congr(($σ1).hom x)
      map_mul' := fun g h => AlgHom.ext fun x => congr(($(σm g h)).hom x) }
  have hsq' : IsPushout (u' m) (ιc m.right) (ι' m) g₀ := by
    have hcw : F.map m.hom ≫ ιc m.right = ιc j := c.w m.hom
    refine IsPushout.of_top ?_ (hu m) (hpo m)
    rw [hv]
    exact hcw ▸ hsq
  obtain ⟨e, he⟩ := exists_algEquiv_of_isPushout (R := F.obj m.right) (C := c.pt) (B := E.obj m)
    (D := D) (ι' m).hom hsq'.flip
  refine ⟨m.right, E.obj m, inferInstance, inferInstance,
    finitePresentation_of_isPushout (hpo m) hφ,
    (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp σ'.toHomUnits, e, fun g x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s b =>
    rw [bcAct_tmul, he, he, map_mul, AlgEquiv.commutes]
    congr 1
    exact congr(($(σι g)).hom b)

end GlobalTheory.TorsorColim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFilteredStatement
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra;
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  first | (exact @GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_action_model_of_isColimit  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeSheafHomValueAtCechNerveSimplexBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeSheafHomValueAtCechNerveSimplexBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.CechPts

variable {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {Z : Scheme.{0}} (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y))
  (h : ∀ i, y i ≫ f = x)

def cmp : yoneda.obj Z ⟶ widePullback (yoneda.obj X) (fun _ : Fin (k + 1) => yoneda.obj Y) (fun _ => yoneda.map f) :=
  WidePullback.lift (yoneda.map x) (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i])

theorem cechPt_eq : cechPt f k x y h = (cmp f k x y h).app (op Z) (𝟙 Z) := rfl

theorem map_cechPt {U : Scheme.{0}} (g : U ⟶ Z) :
    ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h) = (cmp f k x y h).app (op U) g := by
  rw [cechPt_eq]
  have hn := (congrArg (fun t => t (𝟙 Z)) ((cmp f k x y h).naturality g.op)).symm
  change _ = (cmp f k x y h).app (op U) (g ≫ 𝟙 Z)
  change ((cech f).obj (op ⦋k⦌)).map g.op ((cmp f k x y h).app (op Z) (𝟙 Z)) =
    (cmp f k x y h).app (op U) (g ≫ 𝟙 Z) at hn
  exact hn

theorem app_eq {U : Scheme.{0}} (g : U ⟶ Z) :
    (cmp f k x y h).app (op U) g = yonedaEquiv (yoneda.map g ≫ cmp f k x y h) := by
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

theorem bij (hc : IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h)) (U : Scheme.{0}) :
    Function.Bijective ((cmp f k x y h).app (op U)) := by
  constructor
  · intro g g' hg
    rw [app_eq, app_eq] at hg
    have hm := yonedaEquiv.injective hg
    apply WidePullbackCone.IsLimit.hom_ext hc
    · apply yoneda.map_injective
      have := hm =≫ WidePullback.base _
      simp only [cmp, Category.assoc, WidePullback.lift_base] at this
      exact (yoneda.map_comp _ _).trans (this.trans (yoneda.map_comp _ _).symm)
    · intro i
      apply yoneda.map_injective
      have := hm =≫ WidePullback.π _ i
      simp only [cmp, Category.assoc, WidePullback.lift_π] at this
      exact (yoneda.map_comp _ _).trans (this.trans (yoneda.map_comp _ _).symm)
  · intro v
    obtain ⟨m, rfl⟩ := yonedaEquiv.surjective v
    have w : ∀ i, yonedaEquiv (m ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) ≫ f =
        yonedaEquiv (m ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) := by
      intro i
      rw [← WidePullback.π_arrow (fun _ : Fin (k + 1) => yoneda.map f) i, ← Category.assoc, yonedaEquiv_comp]
      rfl
    refine ⟨WidePullbackCone.IsLimit.lift hc _ _ w, (app_eq f k x y h _).trans ?_⟩
    congr 1
    apply WidePullback.hom_ext
    · intro i
      apply yonedaEquiv.injective
      have := WidePullbackCone.IsLimit.lift_π hc _ _ w i
      simp only [WidePullbackCone.mk_π] at this
      rw [Category.assoc]
      simp only [cmp, WidePullback.lift_π]
      exact (congrArg yonedaEquiv (yoneda.map_comp _ _).symm).trans ((yonedaEquiv_yoneda_map _).trans this)
    · apply yonedaEquiv.injective
      have := WidePullbackCone.IsLimit.lift_base hc _ _ w
      simp only [WidePullbackCone.mk_base] at this
      rw [Category.assoc]
      simp only [cmp, WidePullback.lift_base]
      exact (congrArg yonedaEquiv (yoneda.map_comp _ _).symm).trans ((yonedaEquiv_yoneda_map _).trans this)

end GlobalTheory.EtC.CechPts


open GlobalTheory.EtC.CechPts in
theorem GlobalTheory.EtC.CechPts.main : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (k : ℕ) (Z : Scheme.{0}) (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x), IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h) → Function.Bijective (fun s : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F => val s Z (cechPt f k x y h)) := by
  intro R _ F Y X f k Z x y h hc
  have e : ∀ U : Scheme.{0}, Function.Bijective
      (fun g : U ⟶ Z => ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h)) := by
    intro U
    have hb := bij f k x y h hc U
    refine ⟨fun g g' hg => hb.1 ((map_cechPt f k x y h g).symm.trans (hg.trans (map_cechPt f k x y h g'))), fun v => ?_⟩
    obtain ⟨g, hg⟩ := hb.2 v
    exact ⟨g, (map_cechPt f k x y h g).trans hg⟩
  have hext : ∀ s s' : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F,
      (∀ U v, val s U v = val s' U v) → s = s' := by
    intro s s' hs
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ F.property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨v⟩
    exact hs U.unop v
  have hnat : ∀ (s : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)),
      val s V (((cech f).obj (op ⦋k⦌)).map g.op v) = Sec.res g (val s U v) := by
    intro s V U g v
    let η := toSheafify Scheme.etaleTopology ((freeP R).obj ((cech f).obj (op ⦋k⦌))) ≫ s.hom
    change (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (((cech f).obj (op ⦋k⦌)).map g.op v))) =
      (F.obj.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up v)))
    rw [← GlobalTheory.EtC.FreeHom.freePresheaf_map_freeMk _ g.op v]
    exact congrArg (fun t => t.hom (ModuleCat.freeMk (ULift.up v))) (η.naturality g.op)
  have hex : ∀ φ : ∀ U : Scheme.{0}, ((cech f).obj (op ⦋k⦌)).obj (op U) → Sec F U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) v, φ V (((cech f).obj (op ⦋k⦌)).map g.op v) = Sec.res g (φ U v)) →
      ∃ s : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F, ∀ U v, val s U v = φ U v := by
    intro φ hφ
    refine ⟨GlobalTheory.EtC.FreeHom.desc _ F φ hφ, ?_⟩
    intro U v
    change ((toSheafify Scheme.etaleTopology ((freeP R).obj _) ≫ (GlobalTheory.EtC.FreeHom.desc _ F φ hφ).hom).app (op U)).hom (ModuleCat.freeMk (ULift.up v)) = _
    have hd : toSheafify Scheme.etaleTopology ((freeP R).obj ((cech f).obj (op ⦋k⦌))) ≫ (GlobalTheory.EtC.FreeHom.desc _ F φ hφ).hom = GlobalTheory.EtC.FreeHom.descP _ F φ hφ := by
      have ht := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply (GlobalTheory.EtC.FreeHom.descP _ F φ hφ)
      rw [Adjunction.homEquiv_unit] at ht
      exact ht
    rw [hd]
    change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up v)) = _
    erw [ModuleCat.freeDesc_apply]
    rfl
  constructor
  · intro s s' hs
    change val s Z (cechPt f k x y h) = val s' Z (cechPt f k x y h) at hs
    apply hext
    intro U v
    obtain ⟨g, rfl⟩ := (e U).2 v
    dsimp only
    rw [hnat s U Z g, hnat s' U Z g, hs]
  · intro a
    choose c hc0 using fun (U : Scheme.{0}) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)) => (e U).2 v
    have hc' : ∀ (U : Scheme.{0}) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)),
        ((cech f).obj (op ⦋k⦌)).map (c U v).op (cechPt f k x y h) = v := hc0
    obtain ⟨s, hs⟩ := hex (fun U v => Sec.res (c U v) a) (by
      intro V U g v
      have h1 : c V (((cech f).obj (op ⦋k⦌)).map g.op v) = g ≫ c U v := by
        apply (e V).1
        change ((cech f).obj (op ⦋k⦌)).map (c V _).op (cechPt f k x y h) =
          ((cech f).obj (op ⦋k⦌)).map (g ≫ c U v).op (cechPt f k x y h)
        rw [hc' V, op_comp, Functor.map_comp_apply, hc' U v]
      dsimp only
      rw [h1]
      simp [Sec.res])
    refine ⟨s, ?_⟩
    change val s Z (cechPt f k x y h) = a
    rw [hs]
    have h2 : c Z (cechPt f k x y h) = 𝟙 Z := by
      apply (e Z).1
      change ((cech f).obj (op ⦋k⦌)).map (c Z _).op (cechPt f k x y h) =
        ((cech f).obj (op ⦋k⦌)).map (𝟙 Z).op (cechPt f k x y h)
      rw [hc' Z, op_id]
      change _ = ((cech f).obj (op ⦋k⦌)).map (𝟙 (op Z)) _
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [h2]
    simp [Sec.res]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeSheafHomValueAtCechNerveSimplexBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (k : ℕ) (Z : Scheme.{0}) (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x), IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h) → Function.Bijective (fun s : (free R).obj ((cech f).obj (op (SimplexCategory.mk k))) ⟶ F => GlobalTheory.EtC.val s Z (cechPt f k x y h)) := by
  intro R _ F Y X f k Z x y h hc
  have e : ∀ U : Scheme.{0}, Function.Bijective
      (fun g : U ⟶ Z => ((cech f).obj (op (SimplexCategory.mk k))).map g.op (cechPt f k x y h)) := by
    intro U
    have hb := CechPts.bij f k x y h hc U
    refine ⟨fun g g' hg => hb.1 ((CechPts.map_cechPt f k x y h g).symm.trans (hg.trans (CechPts.map_cechPt f k x y h g'))), fun v => ?_⟩
    obtain ⟨g, hg⟩ := hb.2 v
    exact ⟨g, (CechPts.map_cechPt f k x y h g).trans hg⟩
  let P := (cech f).obj (op (SimplexCategory.mk k))
  have evaluate (s : (free R).obj P ⟶ F) (U : Scheme.{0}) (v : P.obj (op U)) :
      val s U v =
        ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom).app (op U)).hom
          (ModuleCat.freeMk (ULift.up v)) := rfl
  have hext (s s' : (free R).obj P ⟶ F) (hs : ∀ U v, val s U v = val s' U v) : s = s' := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ F.property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨v⟩
    have hv := hs U.unop v
    rw [evaluate, evaluate] at hv
    exact hv
  have hex (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
      (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : P.obj (op U)),
        φ V (P.map g.op v) = Sec.res g (φ U v)) :
      ∃ s : (free R).obj P ⟶ F, ∀ U v, val s U v = φ U v := by
    let s := GlobalTheory.EtC.FreeHom.desc P F φ hφ
    refine ⟨s, ?_⟩
    intro U v
    rw [evaluate]
    have hdesc : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom =
        GlobalTheory.EtC.FreeHom.descP P F φ hφ := by
      have h := ((sheafificationAdjunction Scheme.etaleTopology.{0}
        (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply
          (GlobalTheory.EtC.FreeHom.descP P F φ hφ)
      rw [Adjunction.homEquiv_unit] at h
      exact h
    rw [hdesc]
    change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up v)) = _
    erw [ModuleCat.freeDesc_apply]
    rfl
  have hnat (s : (free R).obj P ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U) (v : P.obj (op U)) :
      val s V (P.map g.op v) = Sec.res g (val s U v) := by
    rw [evaluate, evaluate]
    let η := toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom
    change (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op v))) =
      (F.obj.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up v)))
    rw [← GlobalTheory.EtC.FreeHom.freePresheaf_map_freeMk P g.op v]
    exact congrArg (fun m => m.hom (ModuleCat.freeMk (ULift.up v))) (η.naturality g.op)
  constructor
  · intro s s' hs
    change val s Z (cechPt f k x y h) = val s' Z (cechPt f k x y h) at hs
    apply hext
    intro U v
    obtain ⟨g, rfl⟩ := (e U).2 v
    dsimp only
    rw [hnat s U Z g, hnat s' U Z g, hs]
  · intro a
    choose c hc0 using fun (U : Scheme.{0}) (v : ((cech f).obj (op (SimplexCategory.mk k))).obj (op U)) => (e U).2 v
    have hc' : ∀ (U : Scheme.{0}) (v : ((cech f).obj (op (SimplexCategory.mk k))).obj (op U)),
        ((cech f).obj (op (SimplexCategory.mk k))).map (c U v).op (cechPt f k x y h) = v := hc0
    obtain ⟨s, hs⟩ := hex (fun U v => Sec.res (c U v) a) (by
      intro V U g v
      have h1 : c V (((cech f).obj (op (SimplexCategory.mk k))).map g.op v) = g ≫ c U v := by
        apply (e V).1
        change ((cech f).obj (op (SimplexCategory.mk k))).map (c V _).op (cechPt f k x y h) =
          ((cech f).obj (op (SimplexCategory.mk k))).map (g ≫ c U v).op (cechPt f k x y h)
        rw [hc' V, op_comp, Functor.map_comp_apply, hc' U v]
      dsimp only
      rw [h1]
      simp [Sec.res])
    refine ⟨s, ?_⟩
    change val s Z (cechPt f k x y h) = a
    rw [hs]
    have h2 : c Z (cechPt f k x y h) = 𝟙 Z := by
      apply (e Z).1
      change ((cech f).obj (op (SimplexCategory.mk k))).map (c Z _).op (cechPt f k x y h) =
        ((cech f).obj (op (SimplexCategory.mk k))).map (𝟙 Z).op (cechPt f k x y h)
      rw [hc' Z, op_id, P.map_id]
      exact (types_id_apply (P.obj (op Z)) (cechPt f k x y h)).symm
    rw [h2]
    simp [Sec.res]
end
end
