module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory

open scoped Pointwise

theorem lintegral_fundamentalDomain_le_of_meets_orbits
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 ν) (_hS : MeasurableSet S)
    (hmeet : ∀ g, ∃ γ ∈ Γ, γ * g ∈ S) {f : G → ℝ≥0∞} (_hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • S ∩ 𝓕 := by
    intro g hg
    obtain ⟨γ, hγ, hγS⟩ := hmeet g
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩
    refine Set.mem_smul_set.2 ⟨γ * g, hγS, ?_⟩
    show (γ⁻¹ : G) * (γ * g) = g
    group
  calc ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in ⋃ γ : Γ, γ • S ∩ 𝓕, f g ∂ν := lintegral_mono_set hsub
    _ ≤ ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f g ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f (γ⁻¹ • g) ∂ν := by
        refine tsum_congr fun γ => ?_
        congr 1
        funext g
        show f g = f ((γ⁻¹ : Γ) * g)
        exact (hinv _ (γ⁻¹ : Γ).2 g).symm
    _ = ∫⁻ g in S, f g ∂ν := (h𝓕.setLIntegral_eq_tsum' f S).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbitsStatement
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ] (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}, IsFundamentalDomain Γ 𝓕 ν → MeasurableSet S → (∀ g, ∃ γ ∈ Γ, γ * g ∈ S) → ∀ {f : G → ℝ≥0∞}, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by
  first | exact @GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits | exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits | (intros; apply GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdUpdateRegroup
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdUpdateRegroup
open Finset

namespace GlobalTheory

theorem sum_update_fiber_count {ι : Type} [Fintype ι] [DecidableEq ι] {m : ι → ℕ} (i₀ : ι)
    (G : (∀ i, Fin (m i)) → ℂ) :
    ∑ J : (∀ i, Fin (m i)), ∑ j : Fin (m i₀), G (Function.update J i₀ j) = (m i₀ : ℂ) * ∑ J, G J := by
  let e : (∀ i, Fin (m i)) × Fin (m i₀) ≃ (∀ i, Fin (m i)) × Fin (m i₀) :=
    { toFun := fun p => (Function.update p.1 i₀ p.2, p.1 i₀)
      invFun := fun p => (Function.update p.1 i₀ p.2, p.1 i₀)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  rw [← Fintype.sum_prod_type' (fun J j => G (Function.update J i₀ j))]
  rw [Fintype.sum_equiv e (fun p => G (Function.update p.1 i₀ p.2)) (fun p => G p.1) (fun p => rfl)]
  rw [Fintype.sum_prod_type' (fun J (_ : Fin (m i₀)) => G J)]
  simp [Finset.mul_sum]

theorem sum_prod_update_regroup : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by
  intro ι _ _ X W _ _ m k ℓ i₀ F F' w w' hone v
  have key : ∀ (u : W i₀) (H : (∀ i, X i) → ℂ) (J : ∀ i, Fin (m i)),
      ∑ j, (∏ i, ℓ i (Function.update J i₀ j i) (Function.update v i₀ u i)) *
          H (fun i => k i (Function.update J i₀ j i))
        = (∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (J i) (v i)) *
          ∑ j, ℓ i₀ j u * H (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) := by
    intro u H J
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.prod_eq_mul_prod_compl i₀]
    have hrest : ∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (Function.update J i₀ j i) (Function.update v i₀ u i)
        = ∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (J i) (v i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ i₀ := by simpa using hi
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    have hk : (fun i => k i (Function.update J i₀ j i)) = Function.update (fun i => k i (J i)) i₀ (k i₀ j) := by
      funext i
      exact Function.apply_update k J i₀ j i
    rw [hrest, hk, Function.update_self, Function.update_self]
    ring
  by_cases hm : m i₀ = 0
  · haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by
      have h := J i₀
      rw [hm] at h
      exact h.elim0⟩
    simp
  · have hm' : (m i₀ : ℂ) ≠ 0 := by exact_mod_cast hm
    apply mul_left_cancel₀ hm'
    rw [← sum_update_fiber_count, ← sum_update_fiber_count]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [key w' F J, key w F' J, hone J]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdUpdateRegroupStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prod_update_regroup_of_update_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by
  first | exact @GlobalTheory.sum_prod_update_regroup | exact GlobalTheory.sum_prod_update_regroup | (intros; apply GlobalTheory.sum_prod_update_regroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpandPiOfExpandEach
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpandPiOfExpandEach
namespace GlobalTheory

theorem expand_pi_of_expand_each {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i) :
    f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  classical
  by_cases hm : ∃ i, m i = 0
  · obtain ⟨i0, hi0⟩ := hm
    have h1 : f g = 0 := by
      rw [hf i0 g hg]
      apply Finset.sum_eq_zero
      intro j _
      exact absurd j.2 (by omega)
    haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by have := (J i0).2; omega⟩
    rw [h1, Finset.univ_eq_empty, Finset.sum_empty]
  push_neg at hm
  let j0 : ∀ i, Fin (m i) := fun i => ⟨0, Nat.pos_of_ne_zero (hm i)⟩
  let T : Finset ι → ∀ i, Finset (Fin (m i)) := fun s i => if i ∈ s then Finset.univ else {j0 i}
  let H : Finset ι → (∀ i, Fin (m i)) → (∀ i, X i) → (∀ i, X i) :=
    fun s J g i => if i ∈ s then k i (J i) else g i
  have hmem : ∀ s (J : ∀ i, Fin (m i)), J ∈ Fintype.piFinset (T s) ↔ ∀ i, i ∉ s → J i = j0 i := by
    intro s J
    rw [Fintype.mem_piFinset]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;> simp [T, hi]
  have key : ∀ s : Finset ι, ∀ g : ∀ i, X i, (∀ i, g i ∈ K i) →
      f g = ∑ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have hT : T ∅ = fun i => {j0 i} := by funext i; simp [T]
      rw [hT, Fintype.piFinset_singleton, Finset.sum_singleton, Finset.prod_empty, mul_one]
      congr 1
    | insert a s ha ih =>
      intro g hg
      have hHK : ∀ J, ∀ i, H s J g i ∈ K i := by
        intro J i
        simp only [H]
        split_ifs
        exacts [hk _ _, hg i]
      rw [ih g hg]
      have step : ∀ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i)
          = ∑ j, f (H (insert a s) (Function.update J a j) g)
              * ∏ i ∈ insert a s, c i (Function.update J a j i) (g i) := by
        intro J _
        rw [hf a _ (hHK J), Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        have e1 : Function.update (H s J g) a (k a j) = H (insert a s) (Function.update J a j) g := by
          funext i
          by_cases hia : i = a
          · subst hia
            simp [H]
          · simp [H, Function.update_of_ne hia, Finset.mem_insert, hia]
        have e2 : H s J g a = g a := by simp [H, ha]
        rw [e1, e2, Finset.prod_insert ha, Function.update_self]
        have e3 : ∏ i ∈ s, c i (Function.update J a j i) (g i) = ∏ i ∈ s, c i (J i) (g i) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have : i ≠ a := fun h => ha (h ▸ hi)
          rw [Function.update_of_ne this]
        rw [e3]
        ring
      rw [Finset.sum_congr rfl step, ← Finset.sum_product']
      refine Finset.sum_nbij' (fun p => Function.update p.1 a p.2)
        (fun J' => (Function.update J' a (j0 a), J' a)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Finset.mem_coe, hmem]
        intro i hi
        rw [Finset.mem_insert, not_or] at hi
        rw [Function.update_of_ne hi.1]
        exact hp.1 i hi.2
      · intro J' hJ'
        simp only [Finset.mem_coe, hmem] at hJ'
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product,
          Finset.mem_univ, and_true, hmem]
        intro i hi
        by_cases hia : i = a
        · subst hia
          simp
        · rw [Function.update_of_ne hia]
          exact hJ' i (by simp [hia, hi])
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
        funext i
        by_cases hia : i = a
        · subst hia
          rw [Function.update_self]
          exact (hp.1 _ ha).symm
        · rw [Function.update_of_ne hia]
      · intro J' _
        simp only [Function.update_idem, Function.update_eq_self]
      · rintro ⟨J, j⟩ _
        rfl
  rw [key Finset.univ g hg]
  have hTu : T Finset.univ = fun _ => Finset.univ := by funext i; simp [T]
  rw [hTu, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun J _ => ?_
  congr 2
  funext i
  simp [H]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpandPiOfExpandEachStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i), f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  first | exact @GlobalTheory.expand_pi_of_expand_each | exact GlobalTheory.expand_pi_of_expand_each | (intros; apply GlobalTheory.expand_pi_of_expand_each <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualFrameSpanUnitaryRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualFrameSpanUnitaryRepresentation
open Module

namespace GlobalTheory.DualFrameSpan

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

lemma sum_comp' {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  ext x; simp [LinearMap.sum_apply]

lemma comp_sum' {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  ext x; simp [LinearMap.sum_apply]

lemma eq_zero_of_trace_adjoint_comp_self (B : H →ₗ[ℂ] H)
    (h : LinearMap.trace ℂ H (LinearMap.adjoint B ∘ₗ B) = 0) : B = 0 := by
  set b := stdOrthonormalBasis ℂ H
  rw [LinearMap.trace_eq_sum_inner _ b] at h
  have h' : ∀ i, (inner ℂ (b i) ((LinearMap.adjoint B ∘ₗ B) (b i)) : ℂ)
      = ((‖B (b i)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast; first | rfl | simp | norm_cast
  simp_rw [h'] at h
  have h2 : (∑ i, ‖B (b i)‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h2
  apply b.toBasis.ext
  intro i
  have := h3 i (Finset.mem_univ _)
  simpa using this

noncomputable def pairing (W : Submodule ℂ (H →ₗ[ℂ] H)) : LinearMap.BilinForm ℂ W :=
  LinearMap.mk₂ ℂ (fun X Y : W => LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)))
    (fun x y z => by simp [LinearMap.add_comp]) (fun c x y => by simp [LinearMap.smul_comp])
    (fun x y z => by simp [LinearMap.comp_add]) (fun c x y => by simp [LinearMap.comp_smul])

lemma pairing_apply (W : Submodule ℂ (H →ₗ[ℂ] H)) (X Y : W) :
    pairing W X Y = LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)) := rfl

lemma pairing_nondegenerate (W : Submodule ℂ (H →ₗ[ℂ] H))
    (hW : ∀ X ∈ W, LinearMap.adjoint X ∈ W) : (pairing W).Nondegenerate := by
  have key : ∀ y : W, (∀ x : W, pairing W x y = 0) → y = 0 := by
    intro y hy
    have := hy ⟨LinearMap.adjoint (y : H →ₗ[ℂ] H), hW _ y.2⟩
    rw [pairing_apply] at this
    exact Subtype.ext (eq_zero_of_trace_adjoint_comp_self _ this)
  refine ⟨fun x hx => key x (fun y => ?_), fun y hy => key y hy⟩
  rw [pairing_apply, LinearMap.trace_comp_comm']
  exact hx y

section span

variable {G : Type} [Mul G] (K : Set G) (ρ : G → (H →ₗ[ℂ] H))

lemma adjoint_mem_span (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g')
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    LinearMap.adjoint X ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', he⟩ := hadj g hg
    rw [he]; exact Submodule.subset_span ⟨g', hg', rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

lemma comp_mem_span (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h) {h : G} (hh : h ∈ K)
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    X ∘ₗ ρ h ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← hρ g hg h hh]; exact Submodule.subset_span ⟨_, hmul g hg h hh, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [LinearMap.add_comp]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.smul_comp]; exact Submodule.smul_mem _ _ hx

end span

theorem dual_frame : ∀ {G H : Type} [Mul G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g'), ∃ (m : ℕ) (k : Fin m → G) (B : Fin m → (H →ₗ[ℂ] H)), (∀ j, k j ∈ K) ∧
      (∀ A : H →ₗ[ℂ] H, ∀ g ∈ K, LinearMap.trace ℂ H (ρ g ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) * LinearMap.trace ℂ H (ρ g ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j) := by
  intro G H _ _ _ _ K ρ hmul hρ hadj
  classical
  obtain ⟨t, hts, hsp, hli⟩ := exists_linearIndependent ℂ (ρ '' K)
  set W := Submodule.span ℂ (ρ '' K) with hWdef
  have hWt : Submodule.span ℂ (Set.range ((↑) : t → (H →ₗ[ℂ] H))) = W := by
    rw [Subtype.range_coe]; exact hsp
  haveI : Finite t := hli.finite
  letI : Fintype t := Fintype.ofFinite t
  let b0 : Basis t ℂ W := (Basis.span hli).map (LinearEquiv.ofEq _ _ hWt)
  let e := Fintype.equivFin t
  let b : Basis (Fin (Fintype.card t)) ℂ W := b0.reindex e
  have hb : ∀ j, ((b j : W) : H →ₗ[ℂ] H) = ((e.symm j : t) : H →ₗ[ℂ] H) := by
    intro j; simp [b, b0, Basis.span_apply]
  have hbK : ∀ j, ∃ g ∈ K, ρ g = (b j : H →ₗ[ℂ] H) := fun j => by
    rw [hb]; exact hts (e.symm j).2
  choose k hkK hk using hbK
  have hnd := pairing_nondegenerate W (fun X hX => adjoint_mem_span K ρ hadj hX)
  let D := (pairing W).dualBasis hnd b
  have expand : ∀ X ∈ W, X = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ X) • (D j : H →ₗ[ℂ] H) := by
    intro X hX
    have h1 := congrArg Subtype.val (D.sum_repr ⟨X, hX⟩)
    rw [Submodule.coe_sum] at h1
    change _ = X at h1
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, LinearMap.BilinForm.dualBasis_repr_apply, pairing_apply, hk,
      LinearMap.trace_comp_comm' (b j : H →ₗ[ℂ] H) X]
  have hdual : ∀ i j, LinearMap.trace ℂ H (ρ (k i) ∘ₗ (D j : H →ₗ[ℂ] H)) = if i = j then 1 else 0 := by
    intro i j
    rw [hk, LinearMap.trace_comp_comm']
    exact LinearMap.BilinForm.apply_dualBasis_left hnd b j i
  refine ⟨Fintype.card t, k, fun j => (D j : H →ₗ[ℂ] H), hkK, ?_, ?_⟩
  · intro A g hg
    set A' := ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) • (D j : H →ₗ[ℂ] H) with hA'
    have hbi : ∀ i, LinearMap.trace ℂ H (ρ (k i) ∘ₗ A') = LinearMap.trace ℂ H (ρ (k i) ∘ₗ A) := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, hdual, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hvan : ∀ C ∈ W, LinearMap.trace ℂ H (C ∘ₗ A') = LinearMap.trace ℂ H (C ∘ₗ A) := by
      intro C hC
      have h1 := congrArg Subtype.val (b.sum_repr ⟨C, hC⟩)
      rw [Submodule.coe_sum] at h1
      change _ = C at h1
      rw [← h1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Submodule.coe_smul, sum_comp', LinearMap.smul_comp, map_sum, map_smul, ← hk, hbi]
    rw [← hvan (ρ g) (Submodule.subset_span ⟨g, hg, rfl⟩)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul]
  · intro i h hh
    exact expand _ (comp_mem_span K ρ hmul hρ hh (D i).2)

end GlobalTheory.DualFrameSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualFrameSpanUnitaryRepresentationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_frame_span_unitary_representation : ∀ {G H : Type} [Mul G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g'), ∃ (m : ℕ) (k : Fin m → G) (B : Fin m → (H →ₗ[ℂ] H)), (∀ j, k j ∈ K) ∧
      (∀ A : H →ₗ[ℂ] H, ∀ g ∈ K, LinearMap.trace ℂ H (ρ g ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) * LinearMap.trace ℂ H (ρ g ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j) := by
  first | exact @GlobalTheory.DualFrameSpan.dual_frame | exact GlobalTheory.DualFrameSpan.dual_frame | (intros; apply GlobalTheory.DualFrameSpan.dual_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightOfMemCompactSubgroup
open MeasureTheory
open scoped Pointwise NNReal ENNReal

namespace GlobalTheory

theorem haar_map_mul_right_of_mem_compact_subgroup {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hK : IsCompact (K : Set G))
    (k : G) (hk : k ∈ K) : Measure.map (fun g => g * k) μ = μ := by
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g => g * k) μ) μ
  set c := Measure.haarScalarFactor (Measure.map (fun g => g * k) μ) μ with hc
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have hS : IsCompact (C * (K : Set G)) := hC.mul hK
  have hsub : C ⊆ C * (K : Set G) := fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩
  have hpos : 0 < μ (C * (K : Set G)) :=
    Measure.measure_pos_of_mem_nhds μ (Filter.mem_of_superset hC1 hsub)
  have hfin : μ (C * (K : Set G)) < ⊤ := hS.measure_lt_top
  have hpre : (fun g => g * k) ⁻¹' (C * (K : Set G)) = C * (K : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      refine ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩
      simp only at hab ⊢
      rw [← mul_assoc, hab, mul_inv_cancel_right]
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, K.mul_mem hb hk, (mul_assoc _ _ _).symm⟩
  have h1 : Measure.map (fun g => g * k) μ (C * (K : Set G)) = μ (C * (K : Set G)) := by
    have := (MeasurableEquiv.mulRight k).map_apply (μ := μ) (C * (K : Set G))
    rw [MeasurableEquiv.coe_mulRight, hpre] at this
    exact this
  have h2 : (c : ℝ≥0∞) * μ (C * (K : Set G)) = 1 * μ (C * (K : Set G)) := by
    rw [one_mul]
    conv_rhs => rw [← h1, h]
    simp
  have h3 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h2
  have h4 : c = 1 := by exact_mod_cast h3
  rw [h, h4, one_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransport
namespace GlobalTheory

theorem hasSum_quotient_transport :
    ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H),
      (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ,
      HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by
  intro G H _ _ e K K' hK f hf s hs
  have hrel : ∀ a b : G, (QuotientGroup.leftRel K) a b ↔ (QuotientGroup.leftRel K') (e a) (e b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK, map_mul, map_inv]

  let ψ : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv hrel
  have hψ : ∀ q : G ⧸ K, f (e.symm (ψ q).out) = f q.out := by
    intro q
    have h2 : ψ q = QuotientGroup.mk (e q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have h3 : (e q.out)⁻¹ * (ψ q).out ∈ K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', h2]
    have h4 : e.symm (ψ q).out = q.out * e.symm ((e q.out)⁻¹ * (ψ q).out) := by
      rw [map_mul, map_inv, MulEquiv.symm_apply_apply, mul_inv_cancel_left]
    rw [h4, hf _ _ ((hK _).2 (by simpa using h3))]
  have hcomp : (fun a : G ⧸ K => f a.out) = (fun b : H ⧸ K' => f (e.symm b.out)) ∘ ψ := by
    funext q
    exact (hψ q).symm
  rw [hcomp]
  exact (Equiv.hasSum_iff ψ).2 hs

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransportStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient : ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H), (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ, HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by
  first | exact @GlobalTheory.hasSum_quotient_transport | exact GlobalTheory.hasSum_quotient_transport | (intros; apply GlobalTheory.hasSum_quotient_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteReproducingOfSubmodule
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInterpolation
namespace GlobalTheory.LagrangeInterpolationExistence

theorem exists_sum_add {X M : Type} [AddCommGroup M] [Module ℂ M] (S : Finset X) (a : X → M)
    (y : X) (b : M) :
    ∃ (T : Finset X) (u : X → M), ∀ c : X → ℂ,
      ∑ x ∈ T, c x • u x = ∑ x ∈ S, c x • a x + c y • b := by
  classical
  refine ⟨insert y S, fun x => if x = y then (if y ∈ S then a y + b else b) else a x, fun c => ?_⟩
  by_cases hy : y ∈ S
  · rw [Finset.insert_eq_of_mem hy, ← Finset.add_sum_erase S _ hy, ← Finset.add_sum_erase S _ hy]
    simp only [if_pos rfl, hy, if_true, ite_true, smul_add]
    rw [Finset.sum_congr rfl (fun x hx => by rw [if_neg (Finset.ne_of_mem_erase hx)])]
    abel
  · rw [Finset.sum_insert hy]
    simp only [if_neg hy, eq_self_iff_true, if_true, ite_true]
    rw [Finset.sum_congr rfl (fun x hx => by rw [if_neg (fun (h : x = y) => hy (h ▸ hx))]), add_comm]

theorem exists_interpolation {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset V) :
    ∃ (S : Finset X) (u : X → V), ∀ f ∈ F, f = ∑ x ∈ S, (f : X → ℂ) x • u x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, 0, by simp⟩
  | insert g F _ ih =>
    obtain ⟨S, u, hu⟩ := ih
    set h : V := g - ∑ x ∈ S, (g : X → ℂ) x • u x with hh
    by_cases h0 : h = 0
    · refine ⟨S, u, fun f hf => ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact sub_eq_zero.mp h0
      · exact hu f hf
    · obtain ⟨y, hy⟩ : ∃ y, (h : X → ℂ) y ≠ 0 := by
        by_contra hc
        apply h0
        ext y
        by_contra hy
        exact hc ⟨y, by simpa using hy⟩
      obtain ⟨T, w, hw⟩ := exists_sum_add S
        (fun x => u x - ((u x : X → ℂ) y / (h : X → ℂ) y) • h) y (((h : X → ℂ) y)⁻¹ • h)
      have key : ∀ f : V, ∑ x ∈ T, (f : X → ℂ) x • w x =
          ∑ x ∈ S, (f : X → ℂ) x • u x +
            (((f - ∑ x ∈ S, (f : X → ℂ) x • u x : V) : X → ℂ) y / (h : X → ℂ) y) • h := by
        intro f
        rw [hw]
        simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul,
          Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_div, sub_smul, Finset.sum_div,
          mul_div_assoc, div_eq_mul_inv, Finset.sum_mul, mul_assoc, sub_mul]
        abel
      refine ⟨T, w, fun f hf => ?_⟩
      rw [key]
      rcases Finset.mem_insert.mp hf with rfl | hf
      · rw [← hh, div_self hy, one_smul, hh]; abel
      · rw [← hu f hf]; simp

end GlobalTheory.LagrangeInterpolationExistence
end

namespace GlobalTheory

open Finset

theorem exists_finite_reproducing_of_submodule {X : Type} (V : Submodule ℂ (X → ℂ))
    (F : Finset ↥V) :
    ∃ (S : Finset X) (u : X → ↥V), ∀ f ∈ F, f = ∑ x ∈ S, (f : X → ℂ) x • u x := by
  apply _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> assumption

theorem finsupp_sum_multilinear_eq_of_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : ι → Type} (V : ∀ k, Submodule ℂ (X k → ℂ)) {R : Type} [AddCommGroup R] [Module ℂ R]
    (M : (∀ k, ↥(V k)) →ₘₗ[ℂ] R) {A : Type} (τ τ' : A →₀ ℂ)
    (φ φ' : A → ∀ k, ↥(V k))
    (h : ∀ z : ∀ k, X k, (τ.sum fun a c => c * ∏ k, (φ a k : X k → ℂ) (z k)) =
      τ'.sum fun a c => c * ∏ k, (φ' a k : X k → ℂ) (z k)) :
    (τ.sum fun a c => c • M (φ a)) = τ'.sum fun a c => c • M (φ' a) := by
  classical
  let T : Finset A := τ.support ∪ τ'.support
  let F : ∀ k, Finset ↥(V k) := fun k => T.image (fun a => φ a k) ∪ T.image (fun a => φ' a k)
  choose S u hSu using fun k => exists_finite_reproducing_of_submodule (V k) (F k)
  have key : ∀ w : ∀ k, ↥(V k), (∀ k, w k ∈ F k) →
      M w = ∑ z ∈ Fintype.piFinset S, (∏ k, (w k : X k → ℂ) (z k)) • M (fun k => u k (z k)) := by
    intro w hw
    have hw' : w = fun k => ∑ x ∈ S k, (w k : X k → ℂ) x • u k x :=
      funext fun k => hSu k (w k) (hw k)
    conv_lhs => rw [hw']
    rw [MultilinearMap.map_sum_finset]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply]
  have expand : ∀ (σ : A →₀ ℂ) (ψ : A → ∀ k, ↥(V k)), σ.support ⊆ T →
      (∀ a ∈ T, ∀ k, ψ a k ∈ F k) →
      (σ.sum fun a c => c • M (ψ a)) = ∑ z ∈ Fintype.piFinset S,
        (σ.sum fun a c => c * ∏ k, (ψ a k : X k → ℂ) (z k)) • M (fun k => u k (z k)) := by
    intro σ ψ hσ hψ
    unfold Finsupp.sum
    rw [Finset.sum_congr rfl fun a ha => congrArg (σ a • ·) (key (ψ a) (hψ a (hσ ha)))]
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [expand τ φ Finset.subset_union_left
      (fun a ha k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)),
    expand τ' φ' Finset.subset_union_right
      (fun a ha k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))]
  exact Finset.sum_congr rfl fun z _ => by rw [h z]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
open scoped TensorProduct

namespace GlobalTheory.TensHead

def Stab {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (N : Submodule ℂ V) : Prop :=
  ∀ g ∈ G, ∀ x ∈ N, g x ∈ N

def SimpleOver {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) : Prop :=
  ∀ N : Submodule ℂ V, Stab G N → K ≤ N → N = K ∨ N = ⊤

def piOp {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i)) : Module.End ℂ (⨂[ℂ] j, M j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)

def piOps {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) :
    Set (Module.End ℂ (⨂[ℂ] j, M j)) :=
  {f | ∃ i, ∃ g ∈ Op i, f = piOp i g}

def tensOps {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) : Set (Module.End ℂ (V₀ ⊗[ℂ] V₁)) :=
  {f | ∃ g ∈ A, f = TensorProduct.map g LinearMap.id} ∪
    {f | ∃ h ∈ B, f = TensorProduct.map LinearMap.id h}

def piKer {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (K : ∀ i, Submodule ℂ (M i)) : Submodule ℂ (⨂[ℂ] j, M j) :=
  Submodule.span ℂ {t | ∃ y : ∀ i, M i, (∃ i, y i ∈ K i) ∧ t = PiTensorProduct.tprod ℂ y}

def tensKer {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁) : Submodule ℂ (V₀ ⊗[ℂ] V₁) :=
  Submodule.span ℂ {t | ∃ (x : V₀) (y : V₁), (x ∈ K₀ ∨ y ∈ K₁) ∧ t = x ⊗ₜ[ℂ] y}

end GlobalTheory.TensHead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalOrbitOfBoundedRankGenerat
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalOrbitOfBoundedRankGenerat
namespace GlobalTheory

open Submodule

theorem exists_finiteDimensional_orbit_of_generated :
    ∀ (V ι K : Type) [AddCommGroup V] [Module ℂ V] (U : Set ι) (G : Set V) (P : Submodule ℂ V) (D : ι → V →ₗ[ℂ] V)
    (m : ℕ) (L : Fin m → V →ₗ[ℂ] V) (T : K → V →ₗ[ℂ] V) (a : K → ι → ι),
    FiniteDimensional ℂ (Submodule.span ℂ G) →
    (∀ u ∈ U, ∀ f, D u f ∈ Submodule.span ℂ (Set.range fun i => L i f)) →
    G ⊆ P → (∀ u ∈ U, ∀ f ∈ P, D u f ∈ P) →
    (∀ N : Submodule ℂ V, G ⊆ N → (∀ u ∈ U, ∀ f ∈ N, D u f ∈ N) → P ≤ N) →
    (∀ k, ∀ g ∈ G, T k g ∈ Submodule.span ℂ G) → (∀ k, ∀ u ∈ U, a k u ∈ U) →
    (∀ k, ∀ u ∈ U, ∀ f ∈ P, T k (D u f) = D (a k u) (T k f)) →
    ∀ f ∈ P, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ k, T k f ∈ S := by
  intro V ι K _ _ U G P D m L T a hG hDL hGP hDP hmin hTG ha hTD f hf
  obtain ⟨Q, hQ0, hQs⟩ : ∃ Q : ℕ → Submodule ℂ V, Q 0 = span ℂ G ∧
      ∀ n, Q (n + 1) = Q n ⊔ span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V)) :=
    ⟨fun n => Nat.rec (span ℂ G) (fun _ R => R ⊔ span ℂ (⋃ u ∈ U, (D u) '' (R : Set V))) n,
      rfl, fun _ => rfl⟩
  have hmono : Monotone Q := monotone_nat_of_le_succ fun n => by
    rw [hQs]; exact le_sup_left
  have hDQ : ∀ n, ∀ u ∈ U, ∀ x ∈ Q n, D u x ∈ Q (n + 1) := by
    intro n u hu x hx
    rw [hQs]
    exact mem_sup_right (subset_span (Set.mem_iUnion₂.2 ⟨u, hu, x, hx, rfl⟩))
  have hfin : ∀ n : ℕ, FiniteDimensional ℂ (Q n) := by
    intro n
    induction n with
    | zero => rw [hQ0]; exact hG
    | succ n ih =>
      rw [hQs]
      have hle : span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V)) ≤ ⨆ i, (Q n).map (L i) := by
        refine span_le.2 (Set.iUnion₂_subset fun u hu => ?_)
        rintro _ ⟨x, hx, rfl⟩
        refine (span_le.2 ?_) (hDL u hu x)
        rintro _ ⟨i, rfl⟩
        exact mem_iSup_of_mem i (mem_map_of_mem hx)
      haveI : FiniteDimensional ℂ (span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V))) :=
        Submodule.finiteDimensional_of_le hle
      exact Submodule.finiteDimensional_sup _ _
  have hQP : ∀ n, Q n ≤ P := by
    intro n
    induction n with
    | zero => rw [hQ0]; exact span_le.2 hGP
    | succ n ih =>
      rw [hQs]
      refine sup_le ih (span_le.2 (Set.iUnion₂_subset fun u hu => ?_))
      rintro _ ⟨y, hy, rfl⟩
      exact hDP u hu y (ih hy)
  have hT : ∀ n k, Q n ≤ (Q n).comap (T k) := by
    intro n k
    induction n with
    | zero => rw [hQ0]; exact span_le.2 fun g hg => hTG k g hg
    | succ n ih =>
      rw [hQs]
      refine sup_le (ih.trans (comap_mono le_sup_left)) ?_
      refine span_le.2 (Set.iUnion₂_subset fun u hu => ?_)
      rintro _ ⟨x, hx, rfl⟩
      have hxP : x ∈ P := hQP n hx
      rw [SetLike.mem_coe, mem_comap, ← hQs, hTD k u hu x hxP]
      exact hDQ n (a k u) (ha k u hu) (T k x) (ih hx)
  have hGN : G ⊆ (⨆ n, Q n : Submodule ℂ V) := fun g hg =>
    mem_iSup_of_mem 0 (hQ0 ▸ subset_span hg)
  have hDN : ∀ u ∈ U, ∀ x ∈ (⨆ n, Q n : Submodule ℂ V), D u x ∈ (⨆ n, Q n : Submodule ℂ V) := by
    intro u hu x hx
    obtain ⟨n, hn⟩ := (mem_iSup_of_directed Q hmono.directed_le).1 hx
    exact mem_iSup_of_mem (n + 1) (hDQ n u hu x hn)
  obtain ⟨n, hn⟩ := (mem_iSup_of_directed Q hmono.directed_le).1 (hmin _ hGN hDN hf)
  exact ⟨Q n, hfin n, fun k => hT n k hn⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalOrbitOfBoundedRankGeneratStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_orbit_of_boundedRank_generated : ∀ (V ι K : Type) [AddCommGroup V] [Module ℂ V] (U : Set ι) (G : Set V) (P : Submodule ℂ V) (D : ι → V →ₗ[ℂ] V)
    (m : ℕ) (L : Fin m → V →ₗ[ℂ] V) (T : K → V →ₗ[ℂ] V) (a : K → ι → ι),
    FiniteDimensional ℂ (Submodule.span ℂ G) →
    (∀ u ∈ U, ∀ f, D u f ∈ Submodule.span ℂ (Set.range fun i => L i f)) →
    G ⊆ P → (∀ u ∈ U, ∀ f ∈ P, D u f ∈ P) →
    (∀ N : Submodule ℂ V, G ⊆ N → (∀ u ∈ U, ∀ f ∈ N, D u f ∈ N) → P ≤ N) →
    (∀ k, ∀ g ∈ G, T k g ∈ Submodule.span ℂ G) → (∀ k, ∀ u ∈ U, a k u ∈ U) →
    (∀ k, ∀ u ∈ U, ∀ f ∈ P, T k (D u f) = D (a k u) (T k f)) →
    ∀ f ∈ P, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ k, T k f ∈ S := by
  first | exact @GlobalTheory.exists_finiteDimensional_orbit_of_generated | exact GlobalTheory.exists_finiteDimensional_orbit_of_generated | (intros; apply GlobalTheory.exists_finiteDimensional_orbit_of_generated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfAeFundamentalDomainOfLeftInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfAeFundamentalDomainOfLeftInvariant
open MeasureTheory Pointwise

namespace GlobalTheory

theorem eq_zero_of_ae_fundamentalDomain_of_leftInvariant
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsHaarMeasure] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ)
    (hF : Continuous F) (hinv : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x)
    (hae : ∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) : ∀ x, F x = 0 := by
  set U : Set G := {x | F x ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hF continuous_const
  have hUinv : ∀ g : Γ, g • U = U := by
    intro g
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, hUdef, Set.mem_setOf_eq, Subgroup.smul_def,
      smul_eq_mul]
    rw [hinv _ (Γ.inv_mem g.2)]
  have hU𝓕 : μ (U ∩ 𝓕) = 0 := by
    rw [ae_iff, Measure.restrict_apply hUo.measurableSet] at hae
    simpa [hUdef] using hae
  have hU0 : μ U = 0 := h𝓕.measure_zero_of_invariant U hUinv hU𝓕
  have hUe : U = ∅ := by
    by_contra hne
    exact (hUo.measure_pos μ (Set.nonempty_iff_ne_empty.mpr hne)).ne' hU0
  intro x
  by_contra hx
  have : x ∈ U := hx
  rw [hUe] at this
  exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfAeFundamentalDomainOfLeftInvariantStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_ae_zero_on_fundamentalDomain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ F : G → ℂ, Continuous F → (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → (∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) → ∀ x, F x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant | exact GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant | (intros; apply GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefConjTransposeMulSelfEqExpPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefConjTransposeMulSelfEqExpPolynomial
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace GlobalTheory

theorem posDef_conjTranspose_mul_self_eq_exp_polynomial :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g →
      ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
        Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧ L = Polynomial.aeval (gᴴ * g) p := by
  intro n g hg
  set h : Matrix (Fin n) (Fin n) ℂ := gᴴ * g with hh
  have hpd : h.PosDef :=
    Matrix.PosDef.conjTranspose_mul_self g (Matrix.mulVec_injective_iff_isUnit.mpr hg)
  have hsp : IsStrictlyPositive h := hpd.isStrictlyPositive
  have hsa : IsSelfAdjoint h := hpd.isHermitian
  have hfin : (spectrum ℝ h).Finite := Matrix.finite_real_spectrum
  classical
  let s : Finset ℝ := hfin.toFinset
  let q : Polynomial ℝ := Lagrange.interpolate s id Real.log
  have hq : ∀ x ∈ spectrum ℝ h, q.eval x = Real.log x := by
    intro x hx
    have hxs : x ∈ s := hfin.mem_toFinset.mpr hx
    exact Lagrange.eval_interpolate_at_node (r := Real.log) (Set.injOn_id _) hxs
  refine ⟨CFC.log h, q.map (algebraMap ℝ ℂ), ?_, CFC.exp_log h hsp, ?_⟩
  · have : IsSelfAdjoint (CFC.log h) := by
      unfold CFC.log; exact cfc_predicate _ _
    exact this
  · rw [Polynomial.aeval_map_algebraMap, ← cfc_polynomial q h]
    unfold CFC.log
    exact cfc_congr (fun x hx => (hq x hx).symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefConjTransposeMulSelfEqExpPolynomialStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_exp_eq_conjTranspose_mul_poly : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g → ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧ L = Polynomial.aeval (gᴴ * g) p := by
  first | exact @GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial | exact GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial | (intros; apply GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsBis
namespace GlobalTheory.OneAddPowBoundTwistedOperators

theorem one_add_pow_le : ∀ {L : ℝ}, (0 : ℝ) ≤ L → ∀ (N : ℕ), ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N * ((1 : ℝ) + L ^ N) := by
  intro L hL N
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
  have hLN : (0 : ℝ) ≤ L ^ N := pow_nonneg hL N
  rcases le_total L 1 with h | h
  · have h1 : ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    nlinarith
  · have h1 : ((1 : ℝ) + L) ^ N ≤ (2 * L) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at h1
    nlinarith

end GlobalTheory.OneAddPowBoundTwistedOperators
end
