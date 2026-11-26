module

public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper

@[expose] public section

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.ProdPowFactorizationLe
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

private theorem sum_le_prod_of_two_le (s : Finset ℕ) (f : ℕ → ℕ) (h : ∀ l ∈ s, 2 ≤ f l) :
    ∑ l ∈ s, f l ≤ ∏ l ∈ s, f l ∧ (s = ∅ ∨ 2 ≤ ∏ l ∈ s, f l) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h' : ∀ l ∈ s, 2 ≤ f l := fun l hl => h l (Finset.mem_insert_of_mem hl)
    obtain ⟨ih1, ih2⟩ := ih h'
    have hfa := h a (Finset.mem_insert_self a s)
    have hpos : 0 < ∏ l ∈ s, f l := Finset.prod_pos (fun l hl => by have := h' l hl; omega)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, Or.inr (by nlinarith)⟩
    rcases ih2 with rfl | h2
    · simp
    · nlinarith

private theorem prod_pow_factorization_le (s : Finset ℕ) (n : ℕ) (hn : n ≠ 0) (hs : ∀ l ∈ s, l.Prime) :
    ∏ l ∈ s, l ^ n.factorization l ≤ n := by
  classical
  calc ∏ l ∈ s, l ^ n.factorization l ≤ ∏ l ∈ s ∪ n.primeFactors, l ^ n.factorization l := by
        apply Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left
        intro l hl _
        rcases Finset.mem_union.1 hl with h | h
        · exact Nat.one_le_pow _ _ (hs l h).pos
        · exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors h).pos
    _ = ∏ l ∈ n.primeFactors, l ^ n.factorization l := by
        symm
        apply Finset.prod_subset Finset.subset_union_right
        intro l _ hl
        have : n.factorization l = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hl
        rw [this, pow_zero]
    _ = n := by
        conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
        rfl

private theorem lte_val (g δ l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hδ : 1 ≤ δ) (hl : l.Prime)
    (hd : l ∣ g - 1) : padicValNat l (g ^ δ - 1) = padicValNat l (g - 1) + padicValNat l δ := by
  have : Fact l.Prime := ⟨hl⟩
  have hlg : ¬ l ∣ g := by
    intro h
    have : l ∣ 1 := by
      have h2 : l ∣ g - (g - 1) := Nat.dvd_sub h hd
      have : g - (g - 1) = 1 := by omega
      rwa [this] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hl.eq_two_or_odd' with rfl | hodd
  · have hgz : (4 : ℤ) ∣ (g : ℤ) - 1 := by
      have : ((g - 1 : ℕ) : ℤ) = (g : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring
      rw [← this]; exact_mod_cast h4
    have hg2 : ¬ (2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast hlg
    have key := Int.two_pow_sub_pow' (x := (g : ℤ)) (y := 1) δ hgz hg2
    have hpos : 1 ≤ g ^ δ := Nat.one_le_pow _ _ (by omega)
    have e1 : ((g : ℤ) ^ δ - 1 ^ δ) = ((g ^ δ - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hpos]; ring
    have e2 : ((g : ℤ) - 1) = ((g - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring
    rw [e1, e2] at key
    have c2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [c2, Int.natCast_emultiplicity, Int.natCast_emultiplicity, Int.natCast_emultiplicity] at key
    have n1 : g ^ δ - 1 ≠ 0 := by
      have : g ^ 1 ≤ g ^ δ := Nat.pow_le_pow_right (by omega) hδ
      simp at this; omega
    rw [← padicValNat_eq_emultiplicity n1, ← padicValNat_eq_emultiplicity (by omega : g - 1 ≠ 0),
      ← padicValNat_eq_emultiplicity (by omega : δ ≠ 0)] at key
    simp only [Nat.padicValNat_def]
    exact_mod_cast key
  · have := padicValNat.pow_sub_pow (p := l) hodd (x := g) (y := 1) (by omega) hd hlg (n := δ) (by omega)
    simpa [Nat.padicValNat_def] using this

theorem prime_power_order_count : PrimePowerOrderCount := by
  classical
  intro g δ hg h4 hδ
  set A := g - 1 with hA
  have hA0 : A ≠ 0 := by omega
  obtain ⟨B, hB⟩ : A ∣ g ^ δ - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 δ
  have n1 : g ^ δ - 1 ≠ 0 := by
    have : g ^ 1 ≤ g ^ δ := Nat.pow_le_pow_right (by omega) hδ
    simp at this; omega
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB; exact n1 hB
  have hdiv : (g ^ δ - 1) / A = B := by rw [hB]; exact Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv, ← Finset.sum_filter_add_sum_filter_not _ (fun l => l ∣ A)]
  apply add_le_add
  · have e : ∀ l ∈ (g ^ δ - 1).primeFactors.filter (fun l => l ∣ A),
        l ^ padicValNat l (g ^ δ - 1) = l ^ (δ * A).factorization l := by
      intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      rw [lte_val g δ l hg h4 hδ hp hl.2, Nat.padicValNat_def, Nat.padicValNat_def, Nat.factorization_mul (by omega) hA0,
        Finsupp.add_apply, Nat.factorization_def _ hp, Nat.factorization_def _ hp, add_comm]
    rw [Finset.sum_congr rfl e]
    refine le_trans (sum_le_prod_of_two_le _ _ ?_).1 (prod_pow_factorization_le _ _
      (Nat.mul_ne_zero (by omega) hA0) ?_)
    · intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      have : 1 ≤ (δ * A).factorization l :=
        (hp.dvd_iff_one_le_factorization (Nat.mul_ne_zero (by omega) hA0)).1 (Dvd.dvd.mul_left hl.2 _)
      calc 2 ≤ l := hp.two_le
        _ = l ^ 1 := (pow_one l).symm
        _ ≤ _ := Nat.pow_le_pow_right hp.pos this
    · intro l hl
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hl).1
  · have e : ∀ l ∈ (g ^ δ - 1).primeFactors.filter (fun l => ¬ l ∣ A),
        l ^ padicValNat l (g ^ δ - 1) = l ^ B.factorization l := by
      intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      rw [Nat.padicValNat_def, ← Nat.factorization_def _ hp, hB, Nat.factorization_mul hA0 hB0]
      have : A.factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hl.2
      simp [this]
    rw [Finset.sum_congr rfl e]
    refine le_trans (sum_le_prod_of_two_le _ _ ?_).1 (prod_pow_factorization_le _ _ hB0 ?_)
    · intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      have hd : l ∣ B := by
        have := Nat.dvd_of_mem_primeFactors hl.1
        rw [hB] at this
        exact (hp.dvd_mul.1 this).resolve_left hl.2
      have : 1 ≤ B.factorization l := (hp.dvd_iff_one_le_factorization hB0).1 hd
      calc 2 ≤ l := hp.two_le
        _ = l ^ 1 := (pow_one l).symm
        _ ≤ _ := Nat.pow_le_pow_right hp.pos this
    · intro l hl
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hl).1

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.CentralIdempotentsSumOne
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

namespace CISum

open Classical in
theorem centralIdem_act {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hρ : IsIrr ρ) (hσ : IsIrr σ) :
    σ.asAlgebraHom (centralIdem ρ) = if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by
  have := hρ.1
  have := hσ.1
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ.2
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ.2
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  set c : ℂ := (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) with hc
  have e : σ.asAlgebraHom (centralIdem ρ) = ∑ g, (c * ρ.character g⁻¹) • σ g := by
    unfold centralIdem
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
    rfl
  obtain ⟨μ, hμ⟩ := schur_scalar σ hσ.2 (fun g => c * ρ.character g⁻¹) (by
    intro g k
    have : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
    simp only [this, Representation.char_conj])
  have htr : μ * (Module.finrank ℂ W : ℂ) = c * ∑ g, σ.character g * ρ.character g⁻¹ := by
    have h1 := congrArg (LinearMap.trace ℂ W) hμ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1
    rw [← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by simp only [Representation.character]; ring
  have horth := Representation.char_orthonormal σ ρ
  rw [Nat.card_eq_fintype_card] at horth
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  rw [e, hμ]
  split_ifs with hiso
  · rw [if_pos hiso] at horth
    obtain ⟨φ⟩ := hiso
    have hdim : Module.finrank ℂ V = Module.finrank ℂ W := φ.toLinearEquiv.finrank_eq
    have hsum : ∑ g, σ.character g * ρ.character g⁻¹ = (Fintype.card G : ℂ) := by
      field_simp at horth
      simpa using horth
    rw [hsum, hc, hdim, div_mul_cancel₀ _ hc0] at htr
    have : μ = 1 := by
      have := mul_right_cancel₀ hd (htr.trans (one_mul _).symm)
      exact this
    rw [this, one_smul]
  · rw [if_neg hiso] at horth
    have hsum : ∑ g, σ.character g * ρ.character g⁻¹ = 0 := by
      simpa [hc0] using horth
    rw [hsum, mul_zero] at htr
    rw [(mul_eq_zero.mp htr).resolve_right hd, zero_smul]

theorem isIrr_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrr ρ := by
  unfold Representation.IsIrreducible at h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))
  · rcases h.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h1 | h1
    · left
      exact congrArg Subrepresentation.toSubmodule h1
    · right
      exact congrArg Subrepresentation.toSubmodule h1

end CISum

open CISum in
set_option backward.isDefEq.respectTransparency false in
theorem central_idempotents_sum_one : CentralIdemSumOne := by
  intro G I _ _ _ V _ _ _ ρ hirr hne hfull
  classical
  set z : MonoidAlgebra ℂ G := ∑ i, centralIdem (ρ i) with hz
  have hcentral : ∀ x : MonoidAlgebra ℂ G, z * x = x * z := by
    intro x
    rw [hz, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hirr i).1
    exact (central_idempotent_holds G (V i) (ρ i) (hirr i).2).2 x

  have hact : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (σ : Representation ℂ G W), IsIrr σ → σ.asAlgebraHom z = 1 := by
    intro W _ _ _ σ hσ
    obtain ⟨i₀, φ, hφ⟩ := hfull W σ hσ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sum, Finset.sum_eq_single i₀]
    · rw [centralIdem_act (ρ i₀) σ (hirr i₀) hσ, if_pos]
      exact ⟨(Representation.Equiv.mk φ (fun g => LinearMap.ext fun x => hφ g x)).symm⟩
    · intro i _ hi
      rw [centralIdem_act (ρ i) σ (hirr i) hσ, if_neg]
      rintro ⟨ψ⟩
      apply hi
      apply hne
      refine ⟨ψ.toLinearEquiv.trans φ, fun g x => ?_⟩
      have h1 : ψ (ρ i g x) = σ g (ψ x) := LinearMap.congr_fun (ψ.isIntertwining' g) x
      simp only [LinearEquiv.trans_apply]
      erw [h1]
      exact hφ g _
    · intro h; exact absurd (Finset.mem_univ _) h
  have : NeZero (Nat.card G : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero⟩
  let N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
    { carrier := {x | z * x = x}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [mul_add, hx, hy]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at hx ⊢
        rw [← mul_assoc, hcentral a, mul_assoc, hx] }
  have hN : N = ⊤ := by
    rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G)]
    apply sSup_le
    intro S hS x hx
    have hS' : IsSimpleModule (MonoidAlgebra ℂ G) S := hS
    have hirrS := (Representation.isSimpleModule_iff_irreducible_ofModule (k := ℂ) (G := G) S).mp hS'
    have hfd : FiniteDimensional ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) S) := by
      let ι : RestrictScalars ℂ (MonoidAlgebra ℂ G) S →ₗ[ℂ] MonoidAlgebra ℂ G :=
        { toFun := fun y => ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S y : S) :
            MonoidAlgebra ℂ G)
          map_add' := by intro a b; simp
          map_smul' := by
            intro c y
            simp [RestrictScalars.addEquiv_map_smul, Algebra.smul_def] }
      refine Module.Finite.of_injective ι ?_
      intro a b hab
      exact (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).injective (Subtype.ext hab)
    have h1 := hact _ (Representation.ofModule S) (isIrr_of_isIrreducible _ hirrS)
    have h2 := LinearMap.congr_fun h1 ((RestrictScalars.addEquiv _ _ _).symm ⟨x, hx⟩)
    rw [Representation.ofModule_asAlgebraHom_apply_apply] at h2
    have h3 := (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm.injective h2
    have h4 : z * x = x := by simpa using congrArg Subtype.val h3
    exact h4
  have h1 : (1 : MonoidAlgebra ℂ G) ∈ N := hN ▸ Submodule.mem_top
  have h2 : z * 1 = 1 := h1
  rwa [mul_one] at h2

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
