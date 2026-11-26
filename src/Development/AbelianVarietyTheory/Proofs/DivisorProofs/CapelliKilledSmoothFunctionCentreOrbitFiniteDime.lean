module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZalgEqAdjoinFiniteCapelli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZalgEqAdjoinFiniteCapelli
open NumberField GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.CuspRep


open Finset in
theorem zalg_eq_adjoin_finite_caps : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ),
    ∃ T : Finset (Module.End ℂ (Sm E b)), (∀ t ∈ T, ∃ (τ : E →+* ℂ) (u : ℂ), t = cap τ u) ∧
      Zalg E b = Algebra.adjoin ℂ (T : Set (Module.End ℂ (Sm E b))) := by
  intro E _ _ _ b
  classical
  refine ⟨univ.image (fun p : (E →+* ℂ) × Fin (b + 1) => cap (a := b) p.1 ((p.2 : ℕ) : ℂ)), ?_, ?_⟩
  · intro t ht
    obtain ⟨p, -, rfl⟩ := mem_image.1 ht
    exact ⟨p.1, _, rfl⟩
  · apply le_antisymm
    · unfold Zalg
      rw [Algebra.adjoin_le_iff]
      rintro z ⟨τ, u, rfl⟩
      obtain ⟨w, hw⟩ := cap_eq_sum_nodes E b τ u
      rw [hw]
      refine Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨(τ, j), rfl⟩
    · unfold Zalg
      apply Algebra.adjoin_mono
      intro t ht
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at ht
      obtain ⟨p, rfl⟩ := ht
      exact ⟨p.1, _, rfl⟩

end GlobalTheory.CuspRep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZalgEqAdjoinFiniteCapelliStatement
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zalg_eq_adjoin_finite_capelli : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ), ∃ T : Finset (Module.End ℂ (Sm E b)), (∀ t ∈ T, ∃ (τ : E →+* ℂ) (u : ℂ), t = cap τ u) ∧ Zalg E b = Algebra.adjoin ℂ (T : Set (Module.End ℂ (Sm E b))) := by
  first | exact @GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps | exact GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps | (intros; apply GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigencharactersFiniteOfCommutingAnnihilated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigencharactersFiniteOfCommutingAnnihilated
namespace GlobalTheory

open Polynomial

theorem eigencharacters_finite_of_commuting_annihilated :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V))
      (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) →
      (∀ t ∈ T, p t ≠ 0) → ∃ X' : Set (Module.End ℂ V → ℂ), X'.Finite ∧ ∀ ψ : V,
        (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → ∀ (χ' : Module.End ℂ V → ℂ) (u : V),
        u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
          (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) → u ≠ 0 →
        (∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), z u = χ' z • u) →
        ∃ χ ∈ X', ∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), χ' z = χ z := by
  intro V _ _ T p hcomm hp
  classical
  set A := Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) with hA
  let X' : Set (Module.End ℂ V → ℂ) :=
    {χ | (∀ z, z ∉ A → χ z = 0) ∧ (∃ u : V, u ≠ 0 ∧ ∀ z ∈ A, z u = χ z • u) ∧
      ∀ t ∈ T, (p t).eval (χ t) = 0}

  have hdet : ∀ χ₁ ∈ X', ∀ χ₂ ∈ X', (∀ t ∈ T, χ₁ t = χ₂ t) → χ₁ = χ₂ := by
    rintro χ₁ ⟨h₁0, ⟨u₁, hu₁, he₁⟩, -⟩ χ₂ ⟨h₂0, ⟨u₂, hu₂, he₂⟩, -⟩ hT

    have key : ∀ (χ : Module.End ℂ V → ℂ) (u : V), u ≠ 0 → (∀ z ∈ A, z u = χ z • u) →
        (∀ r : ℂ, χ (algebraMap ℂ _ r) = r) ∧
        (∀ x ∈ A, ∀ y ∈ A, χ (x + y) = χ x + χ y) ∧
        (∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) := by
      intro χ u hu he
      have inj := smul_left_injective ℂ hu
      refine ⟨fun r => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_⟩
      · apply inj
        simp only
        rw [← he _ (Subalgebra.algebraMap_mem A r)]
        simp [Module.algebraMap_end_apply]
      · apply inj
        simp only
        rw [← he _ (add_mem hx hy), LinearMap.add_apply, he x hx, he y hy, add_smul]
      · apply inj
        simp only
        rw [← he _ (mul_mem hx hy), Module.End.mul_apply, he y hy, map_smul, he x hx,
          smul_smul, mul_comm]
    obtain ⟨m₁, a₁, p₁⟩ := key χ₁ u₁ hu₁ he₁
    obtain ⟨m₂, a₂, p₂⟩ := key χ₂ u₂ hu₂ he₂
    funext z
    by_cases hz : z ∈ A
    · induction hz using Algebra.adjoin_induction with
      | mem x hx => exact hT x hx
      | algebraMap r => rw [m₁, m₂]
      | add x y hx hy ihx ihy => rw [a₁ x hx y hy, a₂ x hx y hy, ihx, ihy]
      | mul x y hx hy ihx ihy => rw [p₁ x hx y hy, p₂ x hx y hy, ihx, ihy]
    · rw [h₁0 z hz, h₂0 z hz]
  refine ⟨X', ?_, ?_⟩
  ·
    let f : (Module.End ℂ V → ℂ) → (T → ℂ) := fun χ t => χ t
    apply Set.Finite.of_finite_image (f := f)
    · apply (Set.Finite.pi (t := fun t : T => ((p t).roots.toFinset : Set ℂ))
        (fun t => Finset.finite_toSet _)).subset
      rintro _ ⟨χ, ⟨-, -, hroot⟩, rfl⟩
      simp only [Set.mem_pi, Set.mem_univ, Finset.mem_coe, Multiset.mem_toFinset, true_implies]
      intro t
      rw [Polynomial.mem_roots (hp t t.2)]
      exact hroot t t.2
    · intro χ₁ h₁ χ₂ h₂ hf
      exact hdet χ₁ h₁ χ₂ h₂ fun t ht => congrFun hf ⟨t, ht⟩
  · intro ψ hψ χ' u hu hu0 he
    refine ⟨fun z => if z ∈ A then χ' z else 0, ⟨fun z hz => if_neg hz,
      ⟨u, hu0, fun z hz => by simp only [if_pos hz]; exact he z hz⟩, fun t ht => ?_⟩,
      fun z hz => (if_pos hz).symm⟩
    have htA : t ∈ A := Algebra.subset_adjoin ht
    simp only [if_pos htA]

    have hker : u ∈ LinearMap.ker (Polynomial.aeval t (p t)) := by
      refine (Submodule.span_le.mpr ?_) hu
      rintro _ ⟨z, hz, rfl⟩
      have hzt : Commute t z :=
        Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz (fun s hs => hcomm t ht s hs)
      have hc : Commute z (Polynomial.aeval t (p t)) :=
        Algebra.commute_of_mem_adjoin_singleton_of_commute
          (Polynomial.aeval_mem_adjoin_singleton ℂ t) hzt.symm
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hψ t ht, map_zero]
    have hev : t.HasEigenvector (χ' t) u :=
      Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (he t htA), hu0⟩
    have := Module.End.aeval_apply_of_hasEigenvector (p := p t) hev
    rw [LinearMap.mem_ker.mp hker] at this
    exact smul_left_injective ℂ hu0 (by simpa using this.symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigencharactersFiniteOfCommutingAnnihilatedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_eigencharacters_of_eigenvector : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V)) (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) → (∀ t ∈ T, p t ≠ 0) → ∃ X' : Set (Module.End ℂ V → ℂ), X'.Finite ∧ ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → ∀ (χ' : Module.End ℂ V → ℂ) (u : V), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) → u ≠ 0 → (∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), χ' z = χ z := by
  first | exact @GlobalTheory.eigencharacters_finite_of_commuting_annihilated | exact GlobalTheory.eigencharacters_finite_of_commuting_annihilated | (intros; apply GlobalTheory.eigencharacters_finite_of_commuting_annihilated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
namespace GlobalTheory.KilledFin

open Polynomial

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem span_adjoin_apply_le (s : Set (Module.End ℂ V)) (K : Submodule ℂ V)
    (hs : ∀ u ∈ s, ∀ v ∈ K, u v ∈ K) (ψ : V) (hψ : ψ ∈ K) :
    Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ s : Set (Module.End ℂ V)))
      ≤ K := by
  have key : ∀ z ∈ Algebra.adjoin ℂ s, ∀ v ∈ K, z v ∈ K := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap r =>
      intro v hv
      rw [Module.algebraMap_end_apply]
      exact K.smul_mem r hv
    | add x y _ _ hx hy =>
      intro v hv
      rw [LinearMap.add_apply]
      exact K.add_mem (hx v hv) (hy v hv)
    | mul x y _ _ hx hy =>
      intro v hv
      rw [Module.End.mul_apply]
      exact hx _ (hy v hv)
  rw [Submodule.span_le]
  rintro _ ⟨z, hz, rfl⟩
  exact key z hz ψ hψ

theorem span_adjoin_apply_stable (s : Set (Module.End ℂ V)) (ψ : V) (u : Module.End ℂ V)
    (hu : u ∈ Algebra.adjoin ℂ s) (v : V)
    (hv : v ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
      (Algebra.adjoin ℂ s : Set (Module.End ℂ V)))) :
    u v ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
      (Algebra.adjoin ℂ s : Set (Module.End ℂ V))) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨u * z, Subalgebra.mul_mem _ hu hz, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem commute_of_mem_adjoin (s : Set (Module.End ℂ V)) (t : Module.End ℂ V)
    (ht : ∀ u ∈ s, Commute u t) (z : Module.End ℂ V) (hz : z ∈ Algebra.adjoin ℂ s) (q : ℂ[X]) :
    Commute z (aeval t q) := by
  have h1 : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {t} := by
    rw [Algebra.adjoin_le_iff]
    intro u hu
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ((ht u hu).eq).symm
  have h2 : z ∈ Subalgebra.centralizer ℂ {t} := h1 hz
  have h3 : Algebra.adjoin ℂ {t} ≤ Subalgebra.centralizer ℂ {z} := by
    rw [Algebra.adjoin_le_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [Subalgebra.mem_centralizer_iff] at h2
    exact (h2 g rfl).symm
  have h4 := h3 (Polynomial.aeval_mem_adjoin_singleton ℂ (x := t) (p := q))
  rw [Subalgebra.mem_centralizer_iff] at h4
  exact h4 z rfl

def powSpan (t : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ i < d, ∃ n ∈ N, v = (t ^ i) n}

theorem pow_mem_powSpan (t : Module.End ℂ V) (q : ℂ[X]) (hq : q ≠ 0) (N : Submodule ℂ V)
    (hkill : ∀ n ∈ N, aeval t q n = 0) (n : V) (hn : n ∈ N) :
    (t ^ q.natDegree) n ∈ powSpan t q.natDegree N := by
  set d := q.natDegree with hd
  have hlc : q.coeff d ≠ 0 := by
    rw [hd, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hq
  have h0 := hkill n hn
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, LinearMap.add_apply,
    LinearMap.sum_apply] at h0
  have h1 := eq_neg_of_add_eq_zero_right h0
  have h2 : q.coeff d • (t ^ d) n ∈ powSpan t d N := by
    rw [← LinearMap.smul_apply, h1]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
    rw [LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨j, Finset.mem_range.mp hj, n, hn, rfl⟩
  exact (Submodule.smul_mem_iff _ hlc).mp h2

theorem powSpan_stable_self (t : Module.End ℂ V) (q : ℂ[X]) (hq : q ≠ 0) (N : Submodule ℂ V)
    (hkill : ∀ n ∈ N, aeval t q n = 0) (v : V) (hv : v ∈ powSpan t q.natDegree N) :
    t v ∈ powSpan t q.natDegree N := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, n, hn, rfl⟩ := hx
    have e : t ((t ^ i) n) = (t ^ (i + 1)) n := by rw [pow_succ', Module.End.mul_apply]
    rw [e]
    rcases Nat.lt_or_ge (i + 1) q.natDegree with h | h
    · exact Submodule.subset_span ⟨i + 1, h, n, hn, rfl⟩
    · have : i + 1 = q.natDegree := by omega
      rw [this]
      exact pow_mem_powSpan t q hq N hkill n hn
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem powSpan_stable (t u : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V)
    (hu : ∀ n ∈ N, u n ∈ N) (hc : Commute u t) (v : V) (hv : v ∈ powSpan t d N) :
    u v ∈ powSpan t d N := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, n, hn, rfl⟩ := hx
    have e : u ((t ^ i) n) = (t ^ i) (u n) := by
      rw [← Module.End.mul_apply, (hc.pow_right i).eq, Module.End.mul_apply]
    rw [e]
    exact Submodule.subset_span ⟨i, hi, u n, hu n hn, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem le_powSpan (t : Module.End ℂ V) (q : ℂ[X]) (hq : q ≠ 0) (N : Submodule ℂ V)
    (hkill : ∀ n ∈ N, aeval t q n = 0) : N ≤ powSpan t q.natDegree N := by
  intro n hn
  rcases Nat.eq_zero_or_pos q.natDegree with h | h
  · have hC := Polynomial.eq_C_of_natDegree_eq_zero h
    have h0 := hkill n hn
    rw [hC, Polynomial.aeval_C, Module.algebraMap_end_apply] at h0
    have hc0 : q.coeff 0 ≠ 0 := by
      intro hc; apply hq; rw [hC, hc, map_zero]
    rw [(smul_eq_zero.mp h0).resolve_left hc0]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨0, h, n, hn, by simp⟩

theorem powSpan_finite (t : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) [FiniteDimensional ℂ N] :
    FiniteDimensional ℂ (powSpan t d N) ∧
      Module.finrank ℂ (powSpan t d N) ≤ d * Module.finrank ℂ N := by
  let Φ : (Fin d → N) →ₗ[ℂ] V :=
    ∑ i : Fin d, (t ^ (i : ℕ)) ∘ₗ N.subtype ∘ₗ LinearMap.proj i
  have hle : powSpan t d N ≤ LinearMap.range Φ := by
    rw [powSpan, Submodule.span_le]
    rintro _ ⟨i, hi, n, hn, rfl⟩
    refine ⟨Pi.single ⟨i, hi⟩ ⟨n, hn⟩, ?_⟩
    simp [Φ, LinearMap.sum_apply, Pi.single_apply]
    rw [Finset.sum_eq_single ⟨i, hi⟩ (fun b _ hb => by simp [hb]) (by simp)]
    simp
  haveI : FiniteDimensional ℂ (LinearMap.range Φ) := inferInstance
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  calc Module.finrank ℂ (powSpan t d N) ≤ Module.finrank ℂ (LinearMap.range Φ) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ (Fin d → N) := LinearMap.finrank_range_le Φ
    _ = d * Module.finrank ℂ N := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]

end GlobalTheory.KilledFin


open Polynomial in
theorem GlobalTheory.killed_span_adjoin_finrank_le :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V))
      (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) →
      (∀ t ∈ T, p t ≠ 0) → ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) →
      FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ∧
      Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ≤
        ∏ t ∈ T, (p t).natDegree := by
  intro V _ _ T p
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _ _ ψ _
    have hle := GlobalTheory.KilledFin.span_adjoin_apply_le (V := V) ((∅ : Finset (Module.End ℂ V)) : Set _)
      (Submodule.span ℂ {ψ}) (by intro u hu; simp at hu) ψ (Submodule.mem_span_singleton_self ψ)
    refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
    rw [Finset.prod_empty]
    refine (Submodule.finrank_mono hle).trans ?_
    exact (finrank_span_le_card ({ψ} : Set V)).trans (by simp)
  | insert t T htT ih =>
    intro hcomm hne ψ hkillψ
    have hcommT : ∀ s ∈ T, ∀ u ∈ T, Commute s u := fun s hs u hu =>
      hcomm s (Finset.mem_insert_of_mem hs) u (Finset.mem_insert_of_mem hu)
    obtain ⟨hfd, hrk⟩ := ih hcommT (fun u hu => hne u (Finset.mem_insert_of_mem hu)) ψ
      (fun u hu => hkillψ u (Finset.mem_insert_of_mem hu))
    set N := Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) with hN
    have htcomm : ∀ u ∈ (T : Set (Module.End ℂ V)), Commute u t := fun u hu =>
      hcomm u (Finset.mem_insert_of_mem hu) t (Finset.mem_insert_self t T)
    have hkill : ∀ n ∈ N, aeval t (p t) n = 0 := by
      intro n hn
      induction hn using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        have hc := GlobalTheory.KilledFin.commute_of_mem_adjoin _ t htcomm z hz (p t)
        show aeval t (p t) (z ψ) = 0
        rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply,
          hkillψ t (Finset.mem_insert_self t T), map_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
    have hq := hne t (Finset.mem_insert_self t T)
    have hK := GlobalTheory.KilledFin.powSpan_finite t (p t).natDegree N
    have hψK : ψ ∈ GlobalTheory.KilledFin.powSpan t (p t).natDegree N :=
      GlobalTheory.KilledFin.le_powSpan t (p t) hq N hkill
        (Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩)
    have hle := GlobalTheory.KilledFin.span_adjoin_apply_le
      ((insert t T : Finset (Module.End ℂ V)) : Set (Module.End ℂ V))
      (GlobalTheory.KilledFin.powSpan t (p t).natDegree N) (by
        intro u hu v hv
        rw [Finset.coe_insert, Set.mem_insert_iff] at hu
        rcases hu with hut | hu
        · subst hut
          exact GlobalTheory.KilledFin.powSpan_stable_self u (p u) hq N hkill v hv
        · exact GlobalTheory.KilledFin.powSpan_stable t u _ N
            (fun n hn => GlobalTheory.KilledFin.span_adjoin_apply_stable _ ψ u
              (Algebra.subset_adjoin hu) n hn) (htcomm u hu) v hv) ψ hψK
    haveI := hK.1
    refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
    rw [Finset.prod_insert htT]
    calc _ ≤ Module.finrank ℂ (GlobalTheory.KilledFin.powSpan t (p t).natDegree N) :=
          Submodule.finrank_mono hle
      _ ≤ (p t).natDegree * Module.finrank ℂ N := hK.2
      _ ≤ _ := Nat.mul_le_mul_left _ hrk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAlgebraOrbitOfAnnihilatedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_algebra_orbit_of_annihilated : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V)) (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) → (∀ t ∈ T, p t ≠ 0) → ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ≤ ∏ t ∈ T, (p t).natDegree := by
  first | exact @GlobalTheory.killed_span_adjoin_finrank_le | exact GlobalTheory.killed_span_adjoin_finrank_le | (intros; apply GlobalTheory.killed_span_adjoin_finrank_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSmoothFunctionCentreOrbitFiniteDime
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.KilledFinCentre

theorem centre_orbit_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (q : (E →+* ℂ) → ℂ → Polynomial ℂ), (∀ τ u, q τ u ≠ 0) → ∃ (X' : Set (Module.End ℂ (Sm E b) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E b) → ℂ) (u : Sm E b), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b) → u ≠ 0 → (∀ z ∈ Zalg E b, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E b, χ' z = χ z := by
  intro E _ _ _ b q hq
  classical
  obtain ⟨T, hT, hZ⟩ := GlobalTheory.T.zalg_eq_adjoin_finite_capelli E b
  let p : Module.End ℂ (Sm E b) → Polynomial ℂ := fun t =>
    if h : ∃ τ u, t = cap τ u then q h.choose h.choose_spec.choose else 1
  have hp : ∀ t ∈ T, p t ≠ 0 := by
    intro t ht
    simp only [p]
    split_ifs with h
    · exact hq _ _
    · exact one_ne_zero
  have hkill : ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) →
      ∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0 := by
    intro ψ hψ t ht
    have h : ∃ τ u, t = cap τ u := hT t ht
    have key : ∀ τ u, t = cap τ u → Polynomial.aeval t (q τ u) ψ = 0 := by
      rintro τ u rfl; exact hψ τ u
    simp only [p, dif_pos h]
    exact key _ _ h.choose_spec.choose_spec
  have hc : ∀ s ∈ T, ∀ t ∈ T, Commute s t := fun s hs t ht =>
    GlobalTheory.AutGrowth.KilledFin.Zalg_commute (hZ ▸ Algebra.subset_adjoin hs) (hZ ▸ Algebra.subset_adjoin ht)
  obtain ⟨X', hX', hX'e⟩ := GlobalTheory.T.exists_mem_eigencharacters_of_eigenvector _ T p hc hp
  refine ⟨X', ∏ t ∈ T, (p t).natDegree, hX', fun ψ hψ => ?_⟩
  rw [hZ]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finiteDimensional_span_algebra_orbit_of_annihilated _ T p hc hp ψ (hkill ψ hψ)
  exact ⟨h1, h2, hX'e ψ (hkill ψ hψ)⟩

end GlobalTheory.KilledFinCentre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSmoothFunctionCentreOrbitFiniteDimeStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliKilled_smoothFunction_centreOrbit_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (q : (E →+* ℂ) → ℂ → Polynomial ℂ), (∀ τ u, q τ u ≠ 0) → ∃ (X' : Set (Module.End ℂ (Sm E b) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E b) → ℂ) (u : Sm E b), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b) → u ≠ 0 → (∀ z ∈ Zalg E b, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E b, χ' z = χ z := by
  first | exact @GlobalTheory.KilledFinCentre.centre_orbit_finite | exact GlobalTheory.KilledFinCentre.centre_orbit_finite | (intros; apply GlobalTheory.KilledFinCentre.centre_orbit_finite <;> assumption)
end
