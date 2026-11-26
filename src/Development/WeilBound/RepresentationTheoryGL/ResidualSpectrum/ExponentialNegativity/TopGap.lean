module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.LatticeReduction.RedApplyCongr

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumHyperplanesComplementFlags
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardAffineHyperplane
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardAffineHyperplane
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

theorem card_dotProduct_eq_one :
    ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a : Fin (n + 1) → k), a ≠ 0 →
  Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  intro k _ _ n a ha
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  have hax₀ : a ⬝ᵥ Pi.single i (a i)⁻¹ = 1 := by
    rw [dotProduct_single, mul_inv_cancel₀ hi]
  have hfib : ∀ c : k, (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = c)).card =
      (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card := by
    intro c
    apply Finset.card_bij' (fun x _ => x + (1 - c) • Pi.single i (a i)⁻¹)
      (fun x _ => x - (1 - c) • Pi.single i (a i)⁻¹)
    case hi =>
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [dotProduct_add, dotProduct_smul, hax₀, hx, smul_eq_mul, mul_one]
      ring
    case hj =>
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [dotProduct_sub, dotProduct_smul, hax₀, hx, smul_eq_mul, mul_one]
      ring
    case left_inv =>
      intro x _
      simp
    case right_inv =>
      intro x _
      simp
  have htot : (Finset.univ : Finset (Fin (n + 1) → k)).card =
      ∑ c : k, (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (a ⬝ᵥ x))
  have hcard : (Finset.univ : Finset (Fin (n + 1) → k)).card = Fintype.card k ^ (n + 1) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [← hcard, htot, Finset.sum_congr rfl (fun c _ => hfib c), Finset.sum_const,
    Finset.card_univ, smul_eq_mul]

end GlobalTheory.CompanionTheory.GapOpCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardAffineHyperplaneStatement
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_affine_hyperplane : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a : Fin (n + 1) → k), a ≠ 0 →
  Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one | exact GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one | (intros; apply GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFunctionalsVanishingSubspace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFunctionalsVanishingSubspace
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

theorem card_forms_vanishing_missing_line : ∀ (k : Type) [Field k] [Fintype k] (n j : ℕ) (M : Submodule k (Fin (n + 1) → k)), e0 k n ∉ M →
    Module.finrank k M + (j + 1) = n + 1 →
    (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = Fintype.card k ^ j := by
  intro k _ _ n j M hM hdim
  let E := dotProductEquiv k (Fin (n + 1))
  have hE : ∀ a x : Fin (n + 1) → k, E a x = a ⬝ᵥ x := fun a x => by
    simp [E, dotProductEquiv]
  let W : Submodule k (Fin (n + 1) → k) := M ⊔ Submodule.span k {e0 k n}
  let T : Submodule k (Fin (n + 1) → k) := W.dualAnnihilator.comap E.toLinearMap
  have hT : ∀ a, a ∈ T ↔ a ⬝ᵥ e0 k n = 0 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0 := by
    intro a
    simp only [T, W, Submodule.mem_comap, Submodule.mem_dualAnnihilator, LinearEquiv.coe_coe, hE]
    constructor
    · intro h
      exact ⟨h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)),
        fun x hx => h x (Submodule.mem_sup_left hx)⟩
    · rintro ⟨h0, h1⟩ w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [dotProduct_add, dotProduct_smul, h0, h1 x hx, smul_zero, add_zero]
  have hfr : Module.finrank k T = j := by
    have hmap : T.map E.toLinearMap = W.dualAnnihilator :=
      Submodule.map_comap_eq_of_surjective E.surjective _
    have h1 : Module.finrank k T = Module.finrank k W.dualAnnihilator := by
      rw [← hmap]
      exact (LinearEquiv.finrank_map_eq E T).symm
    have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    have h3 : Module.finrank k W = Module.finrank k M + 1 := Submodule.finrank_sup_span_singleton hM
    have h4 : Module.finrank k (Fin (n + 1) → k) = n + 1 := by simp
    omega
  obtain ⟨f, hf0, hfM⟩ := Submodule.exists_le_ker_of_notMem hM
  obtain ⟨b, rfl⟩ := E.surjective f
  have hb0 : b ⬝ᵥ e0 k n ≠ 0 := by rwa [← hE]
  have hbM : ∀ x ∈ M, b ⬝ᵥ x = 0 := fun x hx => by
    rw [← hE]
    exact hfM hx
  let a0 : Fin (n + 1) → k := (b ⬝ᵥ e0 k n)⁻¹ • b
  have ha0 : a0 ⬝ᵥ e0 k n = 1 := by
    simp only [a0, smul_dotProduct, smul_eq_mul]
    exact inv_mul_cancel₀ hb0
  have ha0M : ∀ x ∈ M, a0 ⬝ᵥ x = 0 := fun x hx => by
    simp only [a0, smul_dotProduct, hbM x hx, smul_zero]
  have hcard : (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card
      = (Finset.univ : Finset T).card := by
    refine Finset.card_bij' (fun a ha => ⟨a - a0, ?_⟩) (fun t _ => t.1 + a0) ?_ ?_ ?_ ?_
    · obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 ha
      refine (hT _).2 ⟨?_, fun x hx => ?_⟩
      · rw [sub_dotProduct, h1, ha0, sub_self]
      · rw [sub_dotProduct, h2 x hx, ha0M x hx, sub_self]
    · intro a ha
      exact Finset.mem_univ _
    · intro t _
      obtain ⟨h1, h2⟩ := (hT t.1).1 t.2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, fun x hx => ?_⟩
      · rw [add_dotProduct, h1, ha0, zero_add]
      · rw [add_dotProduct, h2 x hx, ha0M x hx, add_zero]
    · intro a ha
      simp
    · intro t _
      ext1
      simp
  rw [hcard, Finset.card_univ, Module.card_eq_pow_finrank (K := k) (V := T), hfr]

end GlobalTheory.CompanionTheory.GapOpCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFunctionalsVanishingSubspaceStatement
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_functionals_vanishing_subspace : ∀ (k : Type) [Field k] [Fintype k] (n j : ℕ) (M : Submodule k (Fin (n + 1) → k)), e0 k n ∉ M →
  Module.finrank k M + (j + 1) = n + 1 →
  (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = Fintype.card k ^ j := by
  first | exact @GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line | exact GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line | (intros; apply GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCountFromHyperplanes
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCountFromHyperplanes
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpLower

open Finset

theorem re_sesq_sum {V ι : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (s t : Finset ι) (f : ι → V) :
    (B (∑ a ∈ s, f a) (∑ b ∈ t, f b)).re = ∑ a ∈ s, ∑ b ∈ t, (B (f a) (f b)).re := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, Complex.re_sum]
  rw [Finset.sum_comm]

theorem card_filter_ne_zero {α : Type} [Fintype α] [Zero α] :
    (((univ : Finset α).filter (fun a => a ≠ 0)).card : ℝ) = (Fintype.card α : ℝ) - 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) (fun a => a ≠ 0)
  have h0 : ((univ : Finset α).filter (fun a => ¬ a ≠ 0)).card = 1 := by
    have : (univ : Finset α).filter (fun a => ¬ a ≠ 0) = {0} := by
      ext a; simp
    rw [this, card_singleton]
  rw [h0, card_univ] at h
  rw [← h]; push_cast; ring

theorem sum_line {k : Type} [Field k] [Fintype k] {n : ℕ} (a : Fin (n + 1) → k) (ha : a ≠ 0)
    (D : (Fin (n + 1) → k) → ℝ) (hD : ∀ b, (∀ s : k, b ≠ s • a) → D b = 0) :
    ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), D b
      = ∑ s ∈ (univ : Finset k).filter (fun s => s ≠ 0), D (s • a) := by
  have hinj : Function.Injective (fun s : k => s • a) := smul_left_injective k ha
  rw [← Finset.sum_image (f := D) (g := fun s : k => s • a) hinj.injOn]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro b hb
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hb
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    exact smul_ne_zero hs ha
  · intro b hb hb'
    refine hD b ?_
    intro s hs
    apply hb'
    refine Finset.mem_image.mpr ⟨s, ?_, hs.symm⟩
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rintro rfl
    exact hb (by simpa using hs)

theorem row_identity {k : Type} [Field k] [Fintype k] {n : ℕ} (a : Fin (n + 1) → k) (ha : a ≠ 0)
    (N R : (Fin (n + 1) → k) → ℝ) (c : ℝ)
    (hN0 : N 0 = 0)
    (hNa : (Fintype.card k : ℝ) * N a = (Fintype.card k : ℝ) ^ (n + 1))
    (hNs : ∀ s : k, s ≠ 1 → N (s • a) = 0)
    (hNo : ∀ b, (∀ s : k, b ≠ s • a) → (Fintype.card k : ℝ) * N b = (Fintype.card k : ℝ) ^ n)
    (hR : ∀ s : k, s ≠ 0 → R (s • a) = c) :
    (Fintype.card k : ℝ) * ∑ b, N b * R b
      = (Fintype.card k : ℝ) ^ n *
          ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), R b
        + (Fintype.card k : ℝ) ^ n * c := by
  set q : ℝ := (Fintype.card k : ℝ) with hq
  have hZ : ∑ b, N b * R b
      = ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), N b * R b := by
    symm
    refine Finset.sum_subset (filter_subset _ _) ?_
    intro b _ hb
    have : b = 0 := by simpa using hb
    simp [this, hN0]
  have hD := sum_line a ha (fun b => (q * N b - q ^ n) * R b)
    (fun b hb => by show (q * N b - q ^ n) * R b = 0; rw [hNo b hb]; ring)
  have hterm : ∀ s ∈ (univ : Finset k).filter (fun s => s ≠ 0),
      (q * N (s • a) - q ^ n) * R (s • a) = (if s = 1 then q ^ (n + 1) * c else 0) - q ^ n * c := by
    intro s hs
    have s0 : s ≠ 0 := by simpa using hs
    rw [hR s s0]
    by_cases h : s = 1
    · subst h
      rw [one_smul, hNa]; simp; ring
    · rw [hNs s h]; simp [h]
  have h1mem : (1 : k) ∈ (univ : Finset k).filter (fun s => s ≠ 0) := by simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos h1mem,
    Finset.sum_const, nsmul_eq_mul, card_filter_ne_zero] at hD
  have hsplit : q * ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), N b * R b
      = q ^ n * ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), R b
        + ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0),
            (q * N b - q ^ n) * R b := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hZ, hsplit, hD]
  ring

theorem sum_expand {k : Type} [Field k] [Fintype k] {n : ℕ}
    (R : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ) :
    ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = ∑ a, ∑ b, ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card : ℝ)
          * R a b := by
  calc ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = ∑ x : Fin (n + 1) → k, ∑ a, ∑ b, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : a ⬝ᵥ x = 1
        · simp [ha, Finset.sum_filter]
        · simp [ha]
    _ = ∑ a, ∑ x : Fin (n + 1) → k, ∑ b, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 :=
        Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x : Fin (n + 1) → k, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem lower_from_counts : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  (w : (Fin (n + 1) → k) → V) (c A : ℝ),
  (∀ x, 0 ≤ (B x x).re) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 →
    Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a b : Fin (n + 1) → k, a ≠ 0 → (∀ s : k, b ≠ s • a) →
    Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → ∀ s : k, s ≠ 0 → w (s • a) = w a) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → (B (w a) (w a)).re = c) →
  (∀ x : Fin (n + 1) → k, x ≠ 0 →
    (B (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)
       (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)).re = A) →
  (Fintype.card k : ℝ) ^ n * c ≤ (Fintype.card k : ℝ) * A := by
  intro k _ _ n V _ _ B w c A hpos h1 h2 hw hc hA
  have hq1 : (1 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.one_lt_card
  set q : ℝ := (Fintype.card k : ℝ) with hq
  have hq0 : q ≠ 0 := by linarith
  let N : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ := fun a b =>
    ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card : ℝ)
  let R : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ := fun a b => (B (w a) (w b)).re
  let Z : Finset (Fin (n + 1) → k) := univ.filter (fun b => b ≠ 0)
  have hZc : (Z.card : ℝ) = q ^ (n + 1) - 1 := by
    have h := card_filter_ne_zero (α := Fin (n + 1) → k)
    have hc' : (Fintype.card (Fin (n + 1) → k) : ℝ) = q ^ (n + 1) := by simp [hq]
    rw [hc'] at h
    rw [← h]
    simp only [Z]
    congr!
  have hrow : ∀ a, a ≠ 0 → q * ∑ b, N a b * R a b
      = q ^ n * ∑ b ∈ Z, R a b + q ^ n * c := by
    intro a ha
    refine row_identity a ha (N a) (R a) c ?_ ?_ ?_ ?_ ?_
    · simp [N]
    · have h := h1 a ha
      have : N a a = ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card : ℝ) := by
        simp only [N, and_self]
      rw [this]
      exact_mod_cast h
    · intro s hs
      have : univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ (s • a) ⬝ᵥ x = 1) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr ?_
        rintro x - ⟨hx, hx'⟩
        rw [smul_dotProduct, hx] at hx'
        exact hs (by simpa using hx')
      simp only [N, this, card_empty, Nat.cast_zero]
    · intro b hb
      have h := h2 a b ha hb
      have h' : q ^ 2 * N a b = q ^ (n + 1) := by
        simp only [N]; rw [hq]; exact_mod_cast h
      apply mul_left_cancel₀ hq0
      rw [← mul_assoc, ← pow_two, h', pow_succ]; ring
    · intro s hs
      simp only [R, hw a ha s hs, hc a ha]

  have hleft : ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = (q ^ (n + 1) - 1) * A := by
    have hZ : ∑ x ∈ Z, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
        = ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b := by
      refine Finset.sum_subset (filter_subset _ _) ?_
      intro x _ hx
      have hx0 : x = 0 := by simpa [Z] using hx
      subst hx0
      simp
    rw [← hZ]
    have hconst : ∀ x ∈ Z, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b = A := by
      intro x hx
      have hx0 : x ≠ 0 := by simpa [Z] using hx
      rw [← hA x hx0, re_sesq_sum]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hZc]

  have hright : q * ∑ a, ∑ b, N a b * R a b
      = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b + (q ^ (n + 1) - 1) * (q ^ n * c) := by
    have hZ : ∑ a ∈ Z, ∑ b, N a b * R a b = ∑ a, ∑ b, N a b * R a b := by
      refine Finset.sum_subset (filter_subset _ _) ?_
      intro a _ ha
      have ha0 : a = 0 := by simpa [Z] using ha
      subst ha0
      simp [N]
    rw [← hZ, Finset.mul_sum, Finset.sum_congr rfl (fun a ha => hrow a (by simpa [Z] using ha)),
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hZc]
  have hP : 0 ≤ ∑ a ∈ Z, ∑ b ∈ Z, R a b := by
    have := hpos (∑ a ∈ Z, w a)
    rwa [re_sesq_sum] at this
  have hmain : q * ((q ^ (n + 1) - 1) * A)
      = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b + (q ^ (n + 1) - 1) * (q ^ n * c) := by
    rw [← hleft, sum_expand R]
    exact hright
  have hQ : 0 < q ^ (n + 1) - 1 := by
    have : 1 < q ^ (n + 1) := one_lt_pow₀ hq1 (Nat.succ_ne_zero n)
    linarith
  have hqn : 0 ≤ q ^ n := by positivity
  have hfin : 0 ≤ (q ^ (n + 1) - 1) * (q * A - q ^ n * c) := by
    have : (q ^ (n + 1) - 1) * (q * A - q ^ n * c) = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b := by
      linear_combination hmain
    rw [this]
    exact mul_nonneg hqn hP
  have := nonneg_of_mul_nonneg_right hfin hQ
  linarith

end GlobalTheory.CompanionTheory.GapOpLower
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCountFromHyperplanesStatement
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_count_from_hyperplanes : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  (w : (Fin (n + 1) → k) → V) (c A : ℝ),
  (∀ x, 0 ≤ (B x x).re) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 →
    Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a b : Fin (n + 1) → k, a ≠ 0 → (∀ s : k, b ≠ s • a) →
    Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → ∀ s : k, s ≠ 0 → w (s • a) = w a) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → (B (w a) (w a)).re = c) →
  (∀ x : Fin (n + 1) → k, x ≠ 0 →
    (B (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)
       (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)).re = A) →
  (Fintype.card k : ℝ) ^ n * c ≤ (Fintype.card k : ℝ) * A := by
  first | exact @GlobalTheory.CompanionTheory.GapOpLower.lower_from_counts | exact GlobalTheory.CompanionTheory.GapOpLower.lower_from_counts | (intros; apply GlobalTheory.CompanionTheory.GapOpLower.lower_from_counts <;> assumption)
end
end

noncomputable section

open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpMain

variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}

theorem zx_map (hD : LatData k n B red ρ t v) (γ : Γ) (x : Fin (n + 1) → k) (j : ℕ) :
    ρ γ (zx v x j) = zx v ((red γ).val *ᵥ x) j := by
  unfold zx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [hD.equiv]
  refine Finset.sum_equiv (gmapEquiv (red γ)) ?_ (fun _ _ => rfl)
  intro M
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show _ ↔ (red γ).val *ᵥ x ∈ gmap (red γ) M ∧ Module.finrank k ↥(gmap (red γ) M) + j = n + 1
  rw [smul_mem_gmap, finrank_gmap]

theorem zx_smul (v : Submodule k (Fin (n + 1) → k) → V) (x : Fin (n + 1) → k) (j : ℕ) {s : k} (hs : s ≠ 0) :
    zx v (s • x) j = zx v x j := by
  unfold zx
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext M
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 := M.smul_mem s⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at h3
  · rintro ⟨h1, h2⟩
    exact ⟨M.smul_mem s h1, h2⟩

theorem zx_mem (hD : LatData k n B red ρ t v) (j : ℕ) : zx v (e0 k n) j ∈ stabV red ρ := by
  rw [mem_stabV]
  intro γ h
  obtain ⟨s, hs, hse⟩ := exists_scalar_stabilizer_line (red γ) h
  rw [zx_map hD, hse, zx_smul v _ _ hs]

private theorem monoidHom_mul_apply_eq_apply_apply (ρ : Γ →* Module.End ℂ V) (a b : Γ) (x : V) : ρ (a * b) x = ρ a (ρ b x) :=
  congrArg (fun f : Module.End ℂ V => f x) (map_mul ρ a b)

theorem fix_of_gmap (hD : LatData k n B red ρ t v) {y : V} (hy : y ∈ stabV red ρ) {γ₁ γ₂ : Γ}
    (h : gmap (red γ₁) (H0 k n) = gmap (red γ₂) (H0 k n)) : ρ γ₁ (t y) = ρ γ₂ (t y) := by
  have hfix := (mem_stabV red ρ y).mp hy
  have hδ : gmap (red (γ₂⁻¹ * γ₁)) (H0 k n) = H0 k n := by
    rw [map_mul, gmap_mul, h, ← gmap_mul, ← map_mul, inv_mul_cancel, map_one, gmap_one]
  have key := hD.fix y hfix (γ₂⁻¹ * γ₁) hδ
  calc ρ γ₁ (t y) = ρ (γ₂ * (γ₂⁻¹ * γ₁)) (t y) := by rw [mul_inv_cancel_left]
    _ = ρ γ₂ (ρ (γ₂⁻¹ * γ₁) (t y)) := monoidHom_mul_apply_eq_apply_apply ρ _ _ _
    _ = ρ γ₂ (t y) := by rw [key]

theorem w_scale (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {y : V} (hy : y ∈ stabV red ρ) {a : Fin (n + 1) → k} (ha : a ≠ 0) {s : k} (hs : s ≠ 0) :
    ρ (gam (s • a)) (t y) = ρ (gam a) (t y) := by
  have hsa : s • a ≠ 0 := smul_ne_zero hs ha
  apply fix_of_gmap hD hy
  ext z
  rw [mem_GL_image_hyperplane_iff _ _ (hc (s • a) hsa) z, mem_GL_image_hyperplane_iff _ _ (hc a ha) z, smul_dotProduct, smul_eq_mul,
    mul_eq_zero, or_iff_right hs]

def dualEquiv (g : GL (Fin (n + 1)) k) : (Fin (n + 1) → k) ≃ (Fin (n + 1) → k) where
  toFun a := a ᵥ* (g⁻¹).val
  invFun b := b ᵥ* g.val
  left_inv a := by
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  right_inv a := by
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem dualEquiv_dot (g : GL (Fin (n + 1)) k) (a x : Fin (n + 1) → k) :
    dualEquiv g a ⬝ᵥ (g.val *ᵥ x) = a ⬝ᵥ x := by
  show (a ᵥ* (g⁻¹).val) ⬝ᵥ (g.val *ᵥ x) = a ⬝ᵥ x
  rw [← dotProduct_mulVec, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem dualEquiv_ne (g : GL (Fin (n + 1)) k) {a : Fin (n + 1) → k} (ha : a ≠ 0) : dualEquiv g a ≠ 0 := by
  intro h
  apply ha
  apply (dualEquiv g).injective
  rw [h]
  show (0 : Fin (n + 1) → k) = 0 ᵥ* (g⁻¹).val
  rw [zero_vecMul]

theorem w_map (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {y : V} (hy : y ∈ stabV red ρ) (γ : Γ) {a : Fin (n + 1) → k} (ha : a ≠ 0) :
    ρ γ (ρ (gam a) (t y)) = ρ (gam (dualEquiv (red γ) a)) (t y) := by
  have ha' : dualEquiv (red γ) a ≠ 0 := dualEquiv_ne _ ha
  rw [← monoidHom_mul_apply_eq_apply_apply]
  apply fix_of_gmap hD hy
  ext z
  rw [mem_GL_image_hyperplane_iff (red (gam (dualEquiv (red γ) a))) _ (hc _ ha') z]
  rw [map_mul, gmap_mul, mem_gmap (red γ), mem_GL_image_hyperplane_iff _ _ (hc a ha)]
  have key : dualEquiv (red γ) a ⬝ᵥ z = a ⬝ᵥ (((red γ)⁻¹).val *ᵥ z) := by
    have h2 := dualEquiv_dot (red γ) a (((red γ)⁻¹).val *ᵥ z)
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h2
  rw [key]

def ux (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V) (gam : (Fin (n + 1) → k) → Γ) (y : V)
    (x : Fin (n + 1) → k) : V :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), ρ (gam a) (t y)

theorem ux_map (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {y : V} (hy : y ∈ stabV red ρ) (γ : Γ) (x : Fin (n + 1) → k) :
    ρ γ (ux ρ t gam y x) = ux ρ t gam y ((red γ).val *ᵥ x) := by
  unfold ux
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_equiv (dualEquiv (red γ)) ?_ ?_
  · intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, dualEquiv_dot]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    exact w_map hD hc hy γ ha0

theorem ux_smul (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {y : V} (hy : y ∈ stabV red ρ) (x : Fin (n + 1) → k) {s : k} (hs : s ≠ 0) :
    ux ρ t gam y (s • x) = ux ρ t gam y x := by
  let e : (Fin (n + 1) → k) ≃ (Fin (n + 1) → k) :=
    { toFun := fun a => s • a
      invFun := fun b => s⁻¹ • b
      left_inv := fun a => by simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]
      right_inv := fun b => by simp only [smul_smul, mul_inv_cancel₀ hs, one_smul] }
  unfold ux
  refine Finset.sum_equiv e ?_ ?_
  · intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show a ⬝ᵥ (s • x) = 1 ↔ (s • a) ⬝ᵥ x = 1
    rw [dotProduct_smul, smul_dotProduct]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    exact (w_scale hD hc hy ha0 hs).symm

theorem uop_apply (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V) (gam : (Fin (n + 1) → k) → Γ) (y : V) :
    uop ρ t gam y = ux ρ t gam y (e0 k n) := by
  unfold uop
  exact LinearMap.sum_apply _ _ _

theorem uop_mem (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {y : V} (hy : y ∈ stabV red ρ) : uop ρ t gam y ∈ stabV red ρ := by
  rw [mem_stabV]
  intro γ h
  obtain ⟨s, hs, hse⟩ := exists_scalar_stabilizer_line (red γ) h
  rw [uop_apply, ux_map hD hc hy, hse, ux_smul hD hc hy _ hs]

theorem uop_bound (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {y : V} (hy : y ∈ stabV red ρ) :
    (Fintype.card k : ℝ) ^ ((n : ℝ) - 1) * (B y y).re ≤ (B (uop ρ t gam y) (uop ρ t gam y)).re := by
  have hq : (0 : ℝ) < Fintype.card k := by exact_mod_cast Fintype.card_pos
  have hpos : ∀ x : V, 0 ≤ (B x x).re := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hD.pos x hx).le
  have hw : ∀ a : Fin (n + 1) → k, a ≠ 0 → ∀ s : k, s ≠ 0 → ρ (gam (s • a)) (t y) = ρ (gam a) (t y) :=
    fun a ha s hs => w_scale hD hc hy ha hs
  have hc' : ∀ a : Fin (n + 1) → k, a ≠ 0 → (B (ρ (gam a) (t y)) (ρ (gam a) (t y))).re = (B y y).re := by
    intro a _
    rw [hD.unit, hD.isom]
  have hA : ∀ x : Fin (n + 1) → k, x ≠ 0 →
      (B (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), ρ (gam a) (t y))
        (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), ρ (gam a) (t y))).re =
      (B (uop ρ t gam y) (uop ρ t gam y)).re := by
    intro x hx
    obtain ⟨g, hg⟩ := exists_GL_first_basis_eq x hx
    obtain ⟨γ, rfl⟩ := hD.surj g
    have h1 : ux ρ t gam y x = ρ γ (uop ρ t gam y) := by
      rw [uop_apply, ux_map hD hc hy, hg]
    show (B (ux ρ t gam y x) (ux ρ t gam y x)).re = _
    rw [h1, hD.unit]
  have key := GlobalTheory.T.hermitian_count_from_hyperplanes k n V B (fun a => ρ (gam a) (t y)) (B y y).re (B (uop ρ t gam y) (uop ρ t gam y)).re
    hpos (GlobalTheory.T.card_affine_hyperplane k n) (GlobalTheory.T.card_two_affine_hyperplanes k n) hw hc' hA
  have hrpow : (Fintype.card k : ℝ) ^ ((n : ℝ) - 1) = (Fintype.card k : ℝ) ^ n / Fintype.card k := by
    rw [Real.rpow_sub hq, Real.rpow_one, Real.rpow_natCast]
  rw [hrpow, div_mul_eq_mul_div, div_le_iff₀ hq]
  linarith [key]

theorem finsum_conv (P : Submodule k (Fin (n + 1) → k) → Prop) [DecidablePred P] (f : Submodule k (Fin (n + 1) → k) → V) :
    ∑ᶠ (M : Submodule k (Fin (n + 1) → k)) (_ : P M), f M = ∑ M ∈ Finset.univ.filter P, f M := by
  apply finsum_cond_eq_sum_of_cond_iff
  intro x _
  simp

private theorem sup_H0_eq_top_of_e0_mem {K : Type} [Field K] {m : ℕ} (M : Submodule K (Fin (m + 1) → K)) (h : e0 K m ∈ M) :
    M ⊔ H0 K m = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x 0 • e0 K m + (x - x 0 • e0 K m) := (add_sub_cancel _ _).symm
  rw [hx]
  refine Submodule.add_mem_sup (M.smul_mem _ h) ?_
  rw [mem_riemannRochSpace_iff_regularAt_everywhere]
  simp [e0]

private theorem span_e0_inf_H0_eq_bot {K : Type} [Field K] {m : ℕ} : Submodule.span K {e0 K m} ⊓ H0 K m = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf, Submodule.mem_span_singleton, mem_riemannRochSpace_iff_regularAt_everywhere] at hx
  obtain ⟨⟨c, rfl⟩, h0⟩ := hx
  have hc : c = 0 := by simpa [e0] using h0
  rw [hc, zero_smul]
  exact Submodule.zero_mem _

private theorem finrank_H0 {K : Type} [Field K] {m : ℕ} : Module.finrank K ↥(H0 K m) = m := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {e0 K m}) (H0 K m)
  rw [sup_H0_eq_top_of_e0_mem _ (Submodule.mem_span_singleton_self _), span_e0_inf_H0_eq_bot,
    finrank_span_singleton first_basis_ne_zero] at h1
  simp at h1
  omega

private theorem finrank_inf_H0_add_one_of_e0_mem {K : Type} [Field K] {m : ℕ} (M : Submodule K (Fin (m + 1) → K)) (h : e0 K m ∈ M) :
    Module.finrank K ↥(M ⊓ H0 K m) + 1 = Module.finrank K M := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq M (H0 K m)
  rw [sup_H0_eq_top_of_e0_mem M h, finrank_H0] at h1
  simp at h1
  omega

private theorem finrank_sup_span_e0_of_le_H0 {K : Type} [Field K] {m : ℕ} (N : Submodule K (Fin (m + 1) → K)) (hN : N ≤ H0 K m) :
    Module.finrank K ↥(N ⊔ Submodule.span K {e0 K m}) = Module.finrank K N + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq N (Submodule.span K {e0 K m})
  have h2 : N ⊓ Submodule.span K {e0 K m} = ⊥ := by
    refine eq_bot_iff.mpr (le_trans ?_ (span_e0_inf_H0_eq_bot (K := K) (m := m)).le)
    rw [inf_comm]
    exact inf_le_inf_left _ hN
  rw [h2, finrank_span_singleton first_basis_ne_zero] at h1
  simp at h1
  omega

theorem t_zx (hD : LatData k n B red ρ t v) (j : ℕ) :
    t (zx v (e0 k n) j) = ∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => M ≤ H0 k n ∧ Module.finrank k M + (j + 1) = n + 1), v M := by
  unfold zx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_nbij' (fun M => M ⊓ H0 k n) (fun N => N ⊔ Submodule.span k {e0 k n}) ?_ ?_ ?_ ?_ ?_
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
    refine ⟨inf_le_right, ?_⟩
    have h3 := finrank_inf_H0_add_one_of_e0_mem M hM.1
    omega
  · intro N hN
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hN ⊢
    refine ⟨Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), ?_⟩
    have h3 := finrank_sup_span_e0_of_le_H0 N hN.1
    omega
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    apply le_antisymm
    · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hM.1)
    · intro x hx
      have hx' : x = (x - x 0 • e0 k n) + x 0 • e0 k n := (sub_add_cancel _ _).symm
      rw [hx']
      refine Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨M.sub_mem hx (M.smul_mem _ hM.1), ?_⟩)
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      rw [mem_riemannRochSpace_iff_regularAt_everywhere]
      simp [e0]
  · intro N hN
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hN
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx1
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hy0 : y 0 = 0 := (mem_riemannRochSpace_iff_regularAt_everywhere y).mp (hN.1 hy)
      rw [mem_riemannRochSpace_iff_regularAt_everywhere] at hx2
      have hc : c = 0 := by simpa [e0, hy0] using hx2
      rw [hc, zero_smul, add_zero]
      exact hy
    · exact le_inf le_sup_left hN.1
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    exact hD.step M hM.1

theorem sum_hyperplanes_complement_flags (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {a : Fin (n + 1) → k} (ha : a ≠ 0) (j : ℕ) :
    ρ (gam a) (∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => M ≤ H0 k n ∧ Module.finrank k M + (j + 1) = n + 1), v M) =
    ∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => (∀ x ∈ M, a ⬝ᵥ x = 0) ∧ Module.finrank k M + (j + 1) = n + 1), v M := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [hD.equiv]
  refine Finset.sum_equiv (gmapEquiv (red (gam a))) ?_ (fun _ _ => rfl)
  intro M
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show _ ↔ (∀ x ∈ gmap (red (gam a)) M, a ⬝ᵥ x = 0) ∧
    Module.finrank k ↥(gmap (red (gam a)) M) + (j + 1) = n + 1
  rw [finrank_gmap]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro hM x hx
    rw [mem_gmap] at hx
    have h2 := hc a ha (((red (gam a))⁻¹).val *ᵥ x)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h2
    rw [h2]
    exact (mem_riemannRochSpace_iff_regularAt_everywhere _).mp (hM hx)
  · intro h z hz
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, ← hc a ha z]
    exact h _ ((smul_mem_gmap _ _ _).mpr hz)

theorem uop_zx (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    (lam : ℕ → ℂ)
    (hl : ∀ j ≤ n + 1, ∑ᶠ (M : Submodule k (Fin (n + 1) → k)) (_ : Module.finrank k M + j = n + 1), v M = lam j • v ⊤)
    {j : ℕ} (hj : j ≤ n) :
    uop ρ t gam (zx v (e0 k n) j) = (Fintype.card k : ℂ) ^ j • (lam (j + 1) • v ⊤ - zx v (e0 k n) (j + 1)) := by
  have hXne : ∀ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1), a ≠ 0 := by
    intro a ha h0
    rw [h0] at ha
    simp at ha
  have hfs : ∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => Module.finrank k M + (j + 1) = n + 1), v M = lam (j + 1) • v ⊤ := by
    rw [← hl (j + 1) (by omega), finsum_conv]
  have hswap : ∀ (a : Fin (n + 1) → k) (M : Submodule k (Fin (n + 1) → k)),
      a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1) ∧
        M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) =>
          (∀ x ∈ M, a ⬝ᵥ x = 0) ∧ Module.finrank k M + (j + 1) = n + 1) ↔
      a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0) ∧
        M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) => Module.finrank k M + (j + 1) = n + 1) := by
    intro a M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hterm : ∀ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => Module.finrank k M + (j + 1) = n + 1),
      (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card • v M =
      (if e0 k n ∈ M then (0 : ℂ) else (Fintype.card k : ℂ) ^ j) • v M := by
    intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    by_cases he : e0 k n ∈ M
    · have h0 : (Finset.univ.filter
          (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro a _ ha
        have h3 := ha.2 _ he
        rw [ha.1] at h3
        exact one_ne_zero h3
      rw [h0, if_pos he, zero_smul, zero_smul]
    · rw [if_neg he, ← Nat.cast_smul_eq_nsmul ℂ, GlobalTheory.T.card_functionals_vanishing_subspace k n j M he hM, Nat.cast_pow]
  rw [uop_apply]
  unfold ux
  rw [t_zx hD j]
  refine (Finset.sum_congr rfl (fun a ha => sum_hyperplanes_complement_flags hD hc (hXne a ha) j)).trans ?_
  rw [Finset.sum_comm' hswap]
  simp only [Finset.sum_const]
  refine (Finset.sum_congr rfl hterm).trans ?_
  rw [← hfs]
  unfold zx
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, smul_sub, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h1 : Module.finrank k M + (j + 1) = n + 1 <;> by_cases h2 : e0 k n ∈ M <;> simp [h1, h2]

theorem card_ne_zero_mem (M : Submodule k (Fin (n + 1) → k)) :
    (((Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ M)).card : ℕ) : ℂ) =
      (Fintype.card k : ℂ) ^ Module.finrank k M - 1 := by
  have h1 : Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ M) =
      (Finset.univ.filter (fun x : Fin (n + 1) → k => x ∈ M)).erase 0 := by
    ext x
    simp
  have h2 : (Finset.univ.filter (fun x : Fin (n + 1) → k => x ∈ M)).card =
      Fintype.card k ^ Module.finrank k M := by
    rw [← Fintype.card_subtype, ← Module.card_eq_pow_finrank]
  rw [h1, Finset.card_erase_of_mem (by simp), h2, Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos),
    Nat.cast_pow, Nat.cast_one]

theorem pairing (hD : LatData k n B red ρ t v) (lam : ℕ → ℂ)
    (hl : ∀ j ≤ n + 1, ∑ᶠ (M : Submodule k (Fin (n + 1) → k)) (_ : Module.finrank k M + j = n + 1), v M = lam j • v ⊤)
    {j : ℕ} (hj : j ≤ n + 1) :
    ((Fintype.card k : ℂ) ^ (n + 1) - 1) * B (zx v (e0 k n) j) (v ⊤) =
      ((Fintype.card k : ℂ) ^ (n + 1 - j) - 1) * lam j * B (v ⊤) (v ⊤) := by
  have hconst : ∀ x : Fin (n + 1) → k, x ≠ 0 → B (zx v x j) (v ⊤) = B (zx v (e0 k n) j) (v ⊤) := by
    intro x hx
    obtain ⟨g, hg⟩ := exists_GL_first_basis_eq x hx
    obtain ⟨γ, rfl⟩ := hD.surj g
    have htop : ρ γ (v ⊤) = v ⊤ := by rw [hD.equiv, gmap_top]
    calc B (zx v x j) (v ⊤) = B (ρ γ (zx v (e0 k n) j)) (ρ γ (v ⊤)) := by rw [htop, zx_map hD, hg]
      _ = B (zx v (e0 k n) j) (v ⊤) := hD.unit γ _ _
  have hfs : ∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => Module.finrank k M + j = n + 1), v M = lam j • v ⊤ := by
    rw [← hl j hj, finsum_conv]
  have hswap : ∀ (x : Fin (n + 1) → k) (M : Submodule k (Fin (n + 1) → k)),
      x ∈ Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ (⊤ : Submodule k (Fin (n + 1) → k))) ∧
        M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) => x ∈ M ∧ Module.finrank k M + j = n + 1) ↔
      x ∈ Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ M) ∧
        M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) => Module.finrank k M + j = n + 1) := by
    intro x M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Submodule.mem_top, and_true]
    tauto
  have hsum : ∑ x ∈ Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ (⊤ : Submodule k (Fin (n + 1) → k))),
      zx v x j = (((Fintype.card k : ℂ) ^ (n + 1 - j) - 1) * lam j) • v ⊤ := by
    unfold zx
    rw [Finset.sum_comm' hswap]
    simp_rw [Finset.sum_const]
    rw [Finset.sum_congr rfl (g := fun M => ((Fintype.card k : ℂ) ^ (n + 1 - j) - 1) • v M)]
    · rw [← Finset.smul_sum, hfs, smul_smul]
    · intro M hM
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
      rw [← Nat.cast_smul_eq_nsmul ℂ, card_ne_zero_mem M, show Module.finrank k M = n + 1 - j by omega]
  have hcard := card_ne_zero_mem (k := k) (n := n) ⊤
  rw [finrank_top, Module.finrank_fin_fun] at hcard
  have e1 : ∑ x ∈ Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ (⊤ : Submodule k (Fin (n + 1) → k))),
      B (zx v x j) (v ⊤) = ((Fintype.card k : ℂ) ^ (n + 1) - 1) * B (zx v (e0 k n) j) (v ⊤) := by
    rw [Finset.sum_congr rfl (fun x hx => hconst x (Finset.mem_filter.mp hx).2.1), Finset.sum_const,
      nsmul_eq_mul, hcard]
  have e2 : ∑ x ∈ Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ (⊤ : Submodule k (Fin (n + 1) → k))),
      B (zx v x j) (v ⊤) = ((Fintype.card k : ℂ) ^ (n + 1 - j) - 1) * lam j * B (v ⊤) (v ⊤) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← LinearMap.sum_apply, ← map_sum, hsum, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← e1, e2]

theorem zx_zero (hD : LatData k n B red ρ t v) : zx v (e0 k n) 0 = v ⊤ := by
  unfold zx
  rw [Finset.sum_eq_single ⊤]
  · intro M hM hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    exfalso
    apply hne
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    omega
  · intro h
    exfalso
    apply h
    simp

theorem zx_last (v : Submodule k (Fin (n + 1) → k) → V) : zx v (e0 k n) (n + 1) = 0 := by
  unfold zx
  apply Finset.sum_eq_zero
  intro M hM
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
  exfalso
  have h0 : Module.finrank k M = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h0
  have h1 := hM.1
  rw [h0, Submodule.mem_bot] at h1
  exact first_basis_ne_zero h1

theorem gapOp : PositivityTheory.Rg.Rs.GapOp := by
  unfold GapOp
  intro k _ _ n V Γ _ _ _ B red ρ t v lam hD hl
  have hgam : ∀ a : Fin (n + 1) → k, a ≠ 0 → ∃ γ : Γ, ∀ x, a ⬝ᵥ ((red γ).val *ᵥ x) = x 0 := by
    intro a ha
    obtain ⟨g, hg⟩ := exists_gl_cov a ha
    obtain ⟨γ, rfl⟩ := hD.surj g
    exact ⟨γ, hg⟩
  let gam : (Fin (n + 1) → k) → Γ := fun a => if ha : a = 0 then 1 else Classical.choose (hgam a ha)
  have hc : IsCov red gam := by
    intro a ha x
    have h1 : gam a = Classical.choose (hgam a ha) := dif_neg ha
    rw [h1]
    exact Classical.choose_spec (hgam a ha) x
  exact ⟨stabV red ρ, uop ρ t gam, zx v (e0 k n), fun y hy => uop_mem hD hc hy, fun j => zx_mem hD j,
    fun y hy => uop_bound hD hc hy, zx_zero hD, zx_last v, fun j hj => uop_zx hD hc lam hl hj,
    fun j hj => pairing hD lam hl hj⟩

end GlobalTheory.CompanionTheory.GapOpMain
end
end

namespace PositivityTheory.Rg.Rs

theorem gap_holds : Gap := gap_of latOf_holds GlobalTheory.CompanionTheory.GapOpMain.gapOp

end PositivityTheory.Rg.Rs
