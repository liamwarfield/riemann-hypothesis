module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvalues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjacentSelfDualLatticesIndexSimple
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjacentSelfDualLatticesIndexSimple
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

private lemma existsUnique_quotient_sub_smul_mem {R X : Type} [CommRing R] [AddCommGroup X]
    [Module R X] (A B : Submodule R X) (x : X) (P : Ideal R)
    (hxP : ∀ r : R, r • x ∈ A ↔ r ∈ P) (hBle : B ≤ (A ⊓ B) ⊔ Submodule.span R {x}) :
    ∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A := by
  intro b hb
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle hb)
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨Ideal.Quotient.mk P r, ?_, ?_⟩
  · have h1 : (r - Quotient.out (Ideal.Quotient.mk P r)) • x ∈ A := by
      rw [hxP, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
    have h2 : c + r • x - Quotient.out (Ideal.Quotient.mk P r) • x =
        c + (r - Quotient.out (Ideal.Quotient.mk P r)) • x := by
      rw [sub_smul]; abel
    show c + r • x - Quotient.out (Ideal.Quotient.mk P r) • x ∈ A
    rw [h2]
    exact A.add_mem (Submodule.mem_inf.1 hc).1 h1
  · intro q hq
    have h2 : (r - Quotient.out q) • x ∈ A := by
      have h3 : (r - Quotient.out q) • x = (c + r • x - Quotient.out q • x) - c := by
        rw [sub_smul]; abel
      rw [h3]
      exact A.sub_mem hq (Submodule.mem_inf.1 hc).1
    rw [hxP, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out] at h2
    exact h2.symm

private lemma le_or_eq_of_inf_le_of_le_of_isMaximal {R X : Type} [CommRing R] [AddCommGroup X]
    [Module R X] (A B : Submodule R X) (x : X) (hx : x ∈ B) (P : Ideal R) (hP : P.IsMaximal)
    (hxP : ∀ r : R, r • x ∈ A ↔ r ∈ P) (hBle : B ≤ (A ⊓ B) ⊔ Submodule.span R {x})
    (T : Submodule R X) (h1 : A ⊓ B ≤ T) (h2 : T ≤ B) : T ≤ A ∨ T = B := by
  by_cases hTA : T ≤ A
  · exact Or.inl hTA
  right
  obtain ⟨t, htT, htA⟩ := Set.not_subset.1 hTA
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle (h2 htT))
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hr : r ∉ P := fun hr => htA (A.add_mem (Submodule.mem_inf.1 hc).1 ((hxP r).2 hr))
  obtain ⟨s, i, hi, hsi⟩ := hP.exists_inv hr
  have hrx : r • x ∈ T := by
    have h3 := T.sub_mem htT (h1 hc)
    rwa [add_sub_cancel_left] at h3
  have hix : i • x ∈ T := h1 (Submodule.mem_inf.2 ⟨(hxP i).2 hi, B.smul_mem i hx⟩)
  have hxT : x ∈ T := by
    have h4 : x = s • r • x + i • x := by rw [smul_smul, ← add_smul, hsi, one_smul]
    rw [h4]
    exact T.add_mem (T.smul_mem s hrx) hix
  refine le_antisymm h2 (hBle.trans (sup_le h1 ?_))
  rw [Submodule.span_singleton_le_iff_mem]
  exact hxT

private lemma toAddSubgroup_inf {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) : (A ⊓ B).toAddSubgroup = A.toAddSubgroup ⊓ B.toAddSubgroup := by
  ext; simp

theorem _root_.GlobalTheory.FinWeil.adjacent_selfDual_simple : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ (A B : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B → ∀ x ∈ B, ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r : R, r • x ∈ A ↔ r ∈ P) → B ≤ (A ⊓ B) ⊔ Submodule.span R {x} → _root_.GlobalTheory.FinWeil.idx A B = Nat.card (R ⧸ P) ∧ _root_.GlobalTheory.FinWeil.idx B A = Nat.card (R ⧸ P) ∧ (∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ B → T ≤ A ∨ T = B) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ A → T ≤ B ∨ T = A) := by
  intro R X M _ _ _ _ _ σ w γ W hW A B hA hB x hx P hP hfin hxP hBle
  have hA' : ∀ y, y ∈ A ↔ ∀ a ∈ A, γ y a = 1 := hA
  have hB' : ∀ y, y ∈ B ↔ ∀ b ∈ B, γ y b = 1 := hB
  have hrep := existsUnique_quotient_sub_smul_mem A B x P hxP hBle
  have hN : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB : _root_.GlobalTheory.FinWeil.idx A B = Nat.card (R ⧸ P) := by
    haveI := Fintype.ofFinite (R ⧸ P)
    rw [Nat.card_eq_fintype_card]
    exact (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A B hB (0 : M) (fun a _ => map_zero (W a)) (R ⧸ P)
      (fun q => Quotient.out q • x) (fun q => B.smul_mem _ hx) hrep).2
  have hAB' : A.toAddSubgroup.relIndex B.toAddSubgroup = Nat.card (R ⧸ P) := hAB
  have hBA : B.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ P) := by
    have key := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup A.toAddSubgroup
      B.toAddSubgroup (fun a _ => by simpa only [Submodule.mem_toAddSubgroup] using hB' a)
      (fun t ht => by
        simp only [Submodule.mem_toAddSubgroup] at ht ⊢
        rw [hA' t]
        exact ⟨fun h a ha => hW.swap_eq_one (h a ha),
          fun h a ha => hW.swap_eq_one (h a ha)⟩)
      (by rw [hAB']; exact hN)).1
    rw [key, hAB']
  have hdich := le_or_eq_of_inf_le_of_le_of_isMaximal A B x hx P hP hxP hBle
  refine ⟨hAB, hBA, hrep, hdich, ?_⟩
  intro T h1 h2
  by_cases hTB : T ≤ B
  · exact Or.inl hTB
  right
  let T' : Submodule R X :=
    { carrier := {b | b ∈ B ∧ ∀ t ∈ T, γ t b = 1}
      add_mem' := fun {b b'} hb hb' => ⟨B.add_mem hb.1 hb'.1, fun t ht => by
        rw [hW.add_right, hb.2 t ht, hb'.2 t ht, one_mul]⟩
      zero_mem' := ⟨B.zero_mem, fun t _ => hW.zero_right t⟩
      smul_mem' := fun r b hb => ⟨B.smul_mem r hb.1, fun t ht => by
        have h3 := hW.adj (σ r) t b
        rw [hW.sg_sg] at h3
        rw [← h3]
        exact hb.2 _ (T.smul_mem _ ht)⟩ }
  have hmemT' : ∀ b, b ∈ T' ↔ b ∈ B ∧ ∀ t ∈ T, γ t b = 1 := fun b => Iff.rfl
  have hT'1 : A ⊓ B ≤ T' := fun c hc => (hmemT' c).2
    ⟨(Submodule.mem_inf.1 hc).2, fun t ht =>
      hW.iso hA (h2 ht) (Submodule.mem_inf.1 hc).1⟩
  have hT'2 : T' ≤ B := fun b hb => ((hmemT' b).1 hb).1
  rcases hdich T' hT'1 hT'2 with hle | heq
  · have hT'eq : T' = A ⊓ B := le_antisymm (le_inf hle hT'2) hT'1
    have hprod : (A ⊓ B).toAddSubgroup.relIndex T.toAddSubgroup *
        T.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ P) := by
      rw [AddSubgroup.relIndex_mul_relIndex (A ⊓ B).toAddSubgroup T.toAddSubgroup
        A.toAddSubgroup (fun y hy => h1 hy) (fun y hy => h2 hy),
        toAddSubgroup_inf, AddSubgroup.inf_relIndex_left, hBA]
    have hne : (A ⊓ B).toAddSubgroup.relIndex T.toAddSubgroup ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hprod; exact hN hprod.symm
    have key := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW T'.toAddSubgroup B.toAddSubgroup
      (A ⊓ B).toAddSubgroup T.toAddSubgroup
      (fun b hb => by
        simp only [Submodule.mem_toAddSubgroup] at hb ⊢
        rw [hmemT']
        exact ⟨fun h t ht => hW.swap_eq_one (h.2 t ht),
          fun h => ⟨hb, fun t ht => hW.swap_eq_one (h t ht)⟩⟩)
      (fun t ht => by
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf] at ht ⊢
        rw [hB' t]
        exact ⟨fun h b hb => hW.swap_eq_one (h.2 b hb),
          fun h => ⟨h2 ht, fun b hb => hW.swap_eq_one (h b hb)⟩⟩)
      hne).1
    rw [hT'eq, toAddSubgroup_inf, AddSubgroup.inf_relIndex_right, hAB',
      ← toAddSubgroup_inf] at key
    rw [← key] at hprod
    have hone : T.toAddSubgroup.relIndex A.toAddSubgroup = 1 := by
      have h5 : Nat.card (R ⧸ P) * T.toAddSubgroup.relIndex A.toAddSubgroup =
          Nat.card (R ⧸ P) * 1 := by rw [hprod, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h5
    have hAT := AddSubgroup.relIndex_eq_one.1 hone
    exact le_antisymm h2 (fun a ha => hAT ha)
  · exfalso
    apply hTB
    intro t ht
    rw [hB' t]
    intro b hb
    rw [← heq] at hb
    exact ((hmemT' b).1 hb).2 t ht

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjacentSelfDualLatticesIndexSimpleStatement
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjacent_selfDual_lattices_index_simple : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → ∀ x ∈ B, ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r : R, r • x ∈ A ↔ r ∈ P) → B ≤ (A ⊓ B) ⊔ Submodule.span R {x} → idx A B = Nat.card (R ⧸ P) ∧ idx B A = Nat.card (R ⧸ P) ∧ (∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ B → T ≤ A ∨ T = B) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ A → T ≤ B ∨ T = A) := by
  first | exact @GlobalTheory.FinWeil.adjacent_selfDual_simple | exact GlobalTheory.FinWeil.adjacent_selfDual_simple | (intros; apply GlobalTheory.FinWeil.adjacent_selfDual_simple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumCompOfIntermediateLatti
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumCompOfIntermediateLatti
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem sumOp_comp_of_between : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx B C ≠ 0 → B ≤ (B ⊓ A) ⊔ (B ⊓ C) → idx A C = idx A B * idx B C ∧ ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = sumOp W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h A B C hA hB hC hAB hBC hle
  have hdec : ∀ b ∈ B, ∃ c, c ∈ B ∧ c ∈ C ∧ b - c ∈ A := by
    intro b hb
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 (hle hb)
    exact ⟨c, hc.1, hc.2, by simpa using ha.2⟩
  have hAC : ∀ x, x ∈ A → x ∈ C → x ∈ B := by
    intro x hxA hxC
    refine (hB x).2 fun b hb => ?_
    obtain ⟨c, -, hcC, hcA⟩ := hdec b hb
    have e : b = (b - c) + c := by abel
    rw [e, h.add_right, h.iso hA hxA hcA, h.iso hC hxC hcC, one_mul]
  obtain ⟨tAB, tAB2, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h A B hB
  obtain ⟨tBC, tBC2, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h B C hC
  obtain ⟨tAC, -, -⟩ := GlobalTheory.FinWeil.sumOp_transversal h A C hC
  obtain ⟨⟨n, f0, hf0B, hf0⟩, hfix, -⟩ := tAB2 hAB
  obtain ⟨⟨m, g, hgC, hg⟩, -, -⟩ := tBC2 hBC
  choose f hfB hfC hfA using fun i => hdec (f0 i) (hf0B i)
  have hf : ∀ b ∈ B, ∃! i, b - f i ∈ A := by
    intro b hb
    have key : ∀ i, b - f i ∈ A ↔ b - f0 i ∈ A := by
      intro i
      have e : b - f i = (b - f0 i) + (f0 i - f i) := by abel
      rw [e]
      exact A.add_mem_iff_left (hfA i)
    simp only [key]
    exact hf0 b hb
  have hkC : ∀ p : Fin m × Fin n, g p.1 + f p.2 ∈ C := fun p => C.add_mem (hgC _) (hfC _)
  have hk : ∀ x ∈ C, ∃! p : Fin m × Fin n, x - (g p.1 + f p.2) ∈ A := by
    intro x hx
    obtain ⟨j, hj, hju⟩ := hg x hx
    obtain ⟨i, hi, hiu⟩ := hf _ hj
    refine ⟨(j, i), by simpa [sub_add_eq_sub_sub] using hi, ?_⟩
    rintro ⟨j', i'⟩ hp
    have hp' : x - (g j' + f i') ∈ A := hp
    have h1 : x - (g j' + f i') ∈ B := hAC _ hp' (C.sub_mem hx (hkC (j', i')))
    have h2 : x - g j' ∈ B := by
      have e : x - g j' = (x - (g j' + f i')) + f i' := by abel
      rw [e]
      exact B.add_mem h1 (hfB i')
    obtain rfl : j' = j := hju j' h2
    obtain rfl : i' = i := hiu i' (by simpa [sub_add_eq_sub_sub] using hp')
    rfl
  have z : ∀ D : Submodule R X, Fixes W D 0 := fun D a _ => map_zero _
  refine ⟨?_, fun v hv => ?_⟩
  · rw [(tAC 0 (z A) _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).2, (tAB 0 (z A) _ f hfB hf).2,
      (tBC 0 (z B) _ g hgC hg).2, Fintype.card_prod, mul_comm]
  · rw [(tBC _ (hfix v hv) _ g hgC hg).1, (tAB v hv _ f hfB hf).1,
      (tAC v hv _ (fun p : Fin m × Fin n => g p.1 + f p.2) hkC hk).1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => h.comp_of_mem hC (hgC j) (hfC i) v

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumCompOfIntermediateLattiStatement
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx B C ≠ 0 → B ≤ (B ⊓ A) ⊔ (B ⊓ C) → idx A C = idx A B * idx B C ∧ ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = sumOp W A C v := by
  first | exact @GlobalTheory.FinWeil.sumOp_comp_of_between | exact GlobalTheory.FinWeil.sumOp_comp_of_between | (intros; apply GlobalTheory.FinWeil.sumOp_comp_of_between <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedIntertwinerCompOfAdjacentLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergSumCompOfAdjacentOfInfEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergSumCompOfAdjacentOfInfEq
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

private lemma submodule_toAddSubgroup_inf {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) : (A ⊓ B).toAddSubgroup = A.toAddSubgroup ⊓ B.toAddSubgroup := by
  ext; simp

theorem _root_.GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam → ∀ (A B C : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B → _root_.GlobalTheory.FinWeil.SelfDual γ C → _root_.GlobalTheory.FinWeil.Adj A B → _root_.GlobalTheory.FinWeil.idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → _root_.GlobalTheory.FinWeil.sumOp W B C (_root_.GlobalTheory.FinWeil.sumOp W A B v) = lam (_root_.GlobalTheory.FinWeil.idx A B) • _root_.GlobalTheory.FinWeil.sumOp W A C v := by
  intro R X M _ _ _ _ _ σ w γ W hW lam hlam A B C hA hB hC hAdj hAC hinf v hv
  have hA' : ∀ y, y ∈ A ↔ ∀ a ∈ A, γ y a = 1 := hA
  have hB' : ∀ y, y ∈ B ↔ ∀ b ∈ B, γ y b = 1 := hB
  have hC' : ∀ y, y ∈ C ↔ ∀ c ∈ C, γ y c = 1 := hC
  have hv' : ∀ a ∈ A, W a v = v := hv
  have hlam' : (∀ n : ℕ, n ≠ 0 → lam n ≠ 0) ∧ ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) →
      lam (Nat.card (R ⧸ P)) ^ 2 = (Nat.card (R ⧸ P) : ℂ) ∧ ((∀ r ∈ P, σ r ∈ P) →
        lam (Nat.card (R ⧸ P)) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) ∧ ∃ r, σ r - r ∉ P) := hlam
  obtain ⟨x, hx, P, hP, hfin, hxP, hBle⟩ : ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧
      (∀ r : R, r • x ∈ A ↔ r ∈ P) ∧ B ≤ (A ⊓ B) ⊔ Submodule.span R {x} := hAdj
  obtain ⟨hAB, -, hrep, -, -⟩ :=
    _root_.GlobalTheory.FinWeil.adjacent_selfDual_simple hW A B hA hB x hx P hP hfin hxP hBle
  haveI := Fintype.ofFinite (R ⧸ P)
  have hN : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hu : _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ q : R ⧸ P, W (Quotient.out q • x) v :=
    (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A B hB v hv (R ⧸ P) (fun q => Quotient.out q • x)
      (fun q => B.smul_mem _ hx) hrep).1
  have huB : _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v) :=
    ((_root_.GlobalTheory.FinWeil.sumOp_transversal hW A B hB).2.1 (hAB ▸ hN)).2.1 v hv
  obtain ⟨n, f, hfC, hfrep⟩ := _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A C hAC
  have hfrepB : ∀ c ∈ C, ∃! i, c - f i ∈ B := by
    intro c hc
    have key : ∀ i, c - f i ∈ A ↔ c - f i ∈ B := fun i => by
      have hm : c - f i ∈ C := C.sub_mem hc (hfC i)
      constructor
      · intro h
        have h' : c - f i ∈ A ⊓ C := Submodule.mem_inf.2 ⟨h, hm⟩
        rw [hinf] at h'
        exact (Submodule.mem_inf.1 h').1
      · intro h
        have h' : c - f i ∈ B ⊓ C := Submodule.mem_inf.2 ⟨h, hm⟩
        rw [← hinf] at h'
        exact (Submodule.mem_inf.1 h').1
    simpa only [key] using hfrep c hc
  have hBC := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW B C hC _ huB (Fin n) f hfC hfrepB).1
  have hACsum := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A C hC v hv (Fin n) f hfC hfrep).1
  have hSfix : ∀ c ∈ C, W c (_root_.GlobalTheory.FinWeil.sumOp W A C v) = _root_.GlobalTheory.FinWeil.sumOp W A C v :=
    ((_root_.GlobalTheory.FinWeil.sumOp_transversal hW A C hC).2.1 hAC).2.1 v hv

  have hmemE : ∀ y, y ∈ (A ⊓ C).toAddSubgroup ↔ y ∈ A ∧ y ∈ C := fun y => by
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf]
  have hEC : (A ⊓ C).toAddSubgroup.relIndex C.toAddSubgroup ≠ 0 := by
    rw [submodule_toAddSubgroup_inf, AddSubgroup.inf_relIndex_right]
    exact hAC
  have hEA := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW (A ⊓ C).toAddSubgroup A.toAddSubgroup
    (A ⊓ C).toAddSubgroup C.toAddSubgroup
    (fun a ha => by
      simp only [Submodule.mem_toAddSubgroup] at ha
      rw [hmemE, hC' a]
      exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩)
    (fun t ht => by
      simp only [Submodule.mem_toAddSubgroup] at ht
      rw [hmemE, hA' t]
      exact ⟨fun h a ha => hW.swap_eq_one (h.1 a ha),
        fun h => ⟨fun a ha => hW.swap_eq_one (h a ha), ht⟩⟩)
    hEC).1
  have hdual := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW (A ⊓ C).toAddSubgroup C.toAddSubgroup
    (A ⊓ C).toAddSubgroup A.toAddSubgroup
    (fun c hc => by
      simp only [Submodule.mem_toAddSubgroup] at hc
      rw [hmemE, hA' c]
      exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩)
    (fun t ht => by
      simp only [Submodule.mem_toAddSubgroup] at ht
      rw [hmemE, hC' t]
      exact ⟨fun h c hc => hW.swap_eq_one (h.2 c hc),
        fun h => ⟨ht, fun c hc => hW.swap_eq_one (h c hc)⟩⟩)
    (hEA ▸ hEC)).2.1

  obtain ⟨a, ha, hxa⟩ := hdual x (fun c _ hcE => by
    have hcBC : c ∈ B ⊓ C := by
      rw [← hinf]
      exact Submodule.mem_inf.2 ((hmemE c).1 hcE)
    exact hW.iso hB (Submodule.mem_inf.1 hcBC).1 hx)
  simp only [Submodule.mem_toAddSubgroup] at ha
  have hc₀ : x - a ∈ C := by
    rw [hC']
    intro c hc
    apply hW.swap_eq_one
    rw [sub_eq_add_neg, hW.add_right, hW.neg_right, hxa c hc,
      mul_inv_cancel₀ (hW.ne_zero c a)]
  obtain ⟨c₀, hc₀C, hxac⟩ : ∃ c₀ ∈ C, x = a + c₀ := ⟨x - a, hc₀, by abel⟩

  obtain ⟨χ, hχ⟩ : ∃ χ : R → ℂ, ∀ t, χ t = γ a (t • c₀) := ⟨fun t => γ a (t • c₀), fun _ => rfl⟩
  have hχne : ∀ t, χ t ≠ 0 := fun t => by rw [hχ]; exact hW.ne_zero _ _
  have hχadd : ∀ s t, χ (s + t) = χ s * χ t := fun s t => by
    rw [hχ, hχ, hχ, add_smul, hW.add_right]
  have hχ0 : χ 0 = 1 := by rw [hχ, zero_smul]; exact hW.zero_right a
  have hχx : ∀ t, χ t = γ a (t • x) := fun t => by
    rw [hχ, hxac, smul_add, hW.add_right,
      hW.iso hA ha (A.smul_mem t ha), one_mul]
  have hχP : ∀ r ∈ P, χ r = 1 := fun r hr => by
    rw [hχx]
    exact hW.iso hA ha ((hxP r).2 hr)
  have hχσ : ∀ t, χ (σ t) = χ t := fun t => by
    have h1 : γ (t • a) c₀ * γ (t • c₀) a = 1 := by
      have h0 := hW.iso hB (B.smul_mem t hx) hx
      rw [hxac, smul_add, hW.add_left, hW.add_right,
        hW.add_right,
        hW.iso hA (A.smul_mem t ha) ha,
        hW.iso hC (C.smul_mem t hc₀C) hc₀C] at h0
      simpa only [one_mul, mul_one] using h0
    rw [hW.swap a (t • c₀), ← hχ] at h1
    rw [hχ, ← hW.adj t a c₀]
    exact (mul_inv_eq_one₀ (hχne t)).1 h1
  have hχnt : ∃ t, χ t ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have haB : a ∈ B := by
      rw [hB']
      intro b hb
      obtain ⟨d, hd, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle hb)
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [hW.add_right,
        hW.iso hA ha (Submodule.mem_inf.1 hd).1, ← hχx,
        hcon, one_mul]
    have hc₀A : c₀ ∈ A := by
      have h1 : c₀ ∈ B ⊓ C := by
        refine Submodule.mem_inf.2 ⟨?_, hc₀C⟩
        have h2 := B.sub_mem hx haB
        rwa [hxac, add_sub_cancel_left] at h2
      rw [← hinf] at h1
      exact (Submodule.mem_inf.1 h1).1
    have h3 : (1 : R) • x ∈ A := by
      rw [one_smul, hxac]
      exact A.add_mem ha hc₀A
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 ((hxP 1).1 h3))
  have hσP : ∀ r ∈ P, σ r ∈ P := by
    intro r hr
    by_contra hσr
    obtain ⟨s, i, hi, hsi⟩ := hP.exists_inv hσr
    obtain ⟨t, ht⟩ := hχnt
    apply ht
    have h1 : t = t * i + σ (r * σ (t * s)) := by
      rw [map_mul, hW.sg_sg]
      linear_combination (-t) * hsi
    rw [h1, hχadd, hχP _ (P.mul_mem_left t hi), hχσ, hχP _ (P.mul_mem_right _ hr), one_mul]

  have hterm : ∀ s : R, W (s • x) v = χ (w * s * σ s) • W (s • c₀) v := fun s => by
    have hcomp := hW.comp (s • c₀) (s • a) v
    rw [hv' _ (A.smul_mem s ha), ← smul_add, add_comm c₀ a, ← hxac] at hcomp
    have e : γ (w • s • c₀) (s • a) = (χ (w * s * σ s))⁻¹ := by
      rw [hW.swap (s • a) (w • s • c₀), hW.adj s a,
        smul_smul, smul_smul, hχ, show σ s * w * s = w * s * σ s by ring]
    rw [hcomp, e, smul_smul, mul_inv_cancel₀ (hχne _), one_smul]

  have hshift : ∀ c ∈ C, ∑ i, W (f i) (W c v) = _root_.GlobalTheory.FinWeil.sumOp W A C v := by
    intro c hc
    have h1 : ∀ i, W (f i) (W c v) = W c (W (f i) v) := fun i => by
      rw [hW.comm,
        hW.iso hC (hfC i) hc, one_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun i _ => h1 i), ← map_sum, ← hACsum]
    exact hSfix c hc
  have hstep : ∀ i, W (f i) (∑ q : R ⧸ P, W (Quotient.out q • x) v) =
      ∑ q : R ⧸ P, χ (w * Quotient.out q * σ (Quotient.out q)) •
        W (f i) (W (Quotient.out q • c₀) v) := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hterm, map_smul]
  have hstep' : ∀ q : R ⧸ P, ∑ i, χ (w * Quotient.out q * σ (Quotient.out q)) •
      W (f i) (W (Quotient.out q • c₀) v) =
        χ (w * Quotient.out q * σ (Quotient.out q)) • _root_.GlobalTheory.FinWeil.sumOp W A C v :=
    fun q => by rw [← Finset.smul_sum, hshift _ (C.smul_mem _ hc₀C)]
  rw [hBC, hu, Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_comm,
    Finset.sum_congr rfl (fun q _ => hstep' q), ← Finset.sum_smul]
  congr 1
  rw [← finsum_eq_sum_of_fintype,
    _root_.GlobalTheory.NormFormGauss.gauss_quotient σ w hW.sg_sg hW.w_add P hP hfin hσP
      ((hlam'.2 P hP hfin).2 hσP).2 χ hχadd hχ0 hχP hχσ hχnt,
    hAB, ((hlam'.2 P hP hfin).2 hσP).1]

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergSumCompOfAdjacentOfInfEqStatement
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = lam (idx A B) • sumOp W A C v := by
  first | exact @GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq | exact GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq | (intros; apply GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedIntertwinerCompOfAdjacentLattices
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem idx_congr_of_inf_eq {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    {A B C : Submodule R X} (h : A ⊓ C = B ⊓ C) : idx A C = idx B C := by
  unfold idx
  rw [← AddSubgroup.inf_relIndex_right A.toAddSubgroup, ← AddSubgroup.inf_relIndex_right B.toAddSubgroup]
  have : A.toAddSubgroup ⊓ C.toAddSubgroup = B.toAddSubgroup ⊓ C.toAddSubgroup := by
    ext x
    have := SetLike.ext_iff.1 h x
    simpa using this
  rw [this]

theorem normOp_comp_of_adj : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hl A B C hA hB hC hadj hAC v hv
  obtain ⟨x, hx, P, hP, hfin, hann, hle⟩ := id hadj
  obtain ⟨hAB, hBA, -, hsB, hsA⟩ := GlobalTheory.T.adjacent_selfDual_lattices_index_simple h A B hA hB x hx P hP hfin hann hle
  have hn : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB0 : idx A B ≠ 0 := hAB ▸ hn
  have hBA0 : idx B A ≠ 0 := hBA ▸ hn
  have hBC0 : idx B C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hBA0 hAC
  have hsq : lam (idx A B) ^ 2 = (idx A B : ℂ) := by
    rw [hAB]; exact (hl.2 P hP hfin).1
  have lAB := hl.1 _ hAB0
  have lBC := hl.1 _ hBC0
  have lAC := hl.1 _ hAC
  have homBC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h B C hC).2.1 hBC0).2.2
  have homAC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A C hC).2.1 hAC).2.2
  have fixB := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A B hB).2.1 hAB0).2.1 v hv
  unfold normOp
  rw [homBC, smul_smul]
  by_cases h1 : B ⊓ C ≤ A
  · by_cases h2 : A ⊓ C ≤ B
    · have he : A ⊓ C = B ⊓ C :=
        le_antisymm (le_inf h2 inf_le_right) (le_inf h1 inf_le_right)
      rw [GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq h lam hl A B C hA hB hC hadj hAC he v hv, smul_smul, ← idx_congr_of_inf_eq he]
      congr 1
      field_simp
    · have hT : A ⊓ B ⊔ A ⊓ C = A := by
        rcases hsA (A ⊓ B ⊔ A ⊓ C) le_sup_left (sup_le inf_le_left inf_le_left) with h3 | h3
        · exact absurd (le_sup_right.trans h3) h2
        · exact h3
      obtain ⟨hi, hs⟩ := GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h B A C hB hA hC hBA0 hAC hT.ge
      rw [← hs _ fixB, (GlobalTheory.T.heisenberg_intertwining_sums_comp_eq_index h A B hA hB hAB0).2 v hv, homAC, smul_smul, hi,
        hBA.trans hAB.symm, map_mul, ← hsq]
      congr 1
      field_simp
  · have hT : A ⊓ B ⊔ B ⊓ C = B := by
      rcases hsB (A ⊓ B ⊔ B ⊓ C) le_sup_left (sup_le inf_le_right inf_le_left) with h3 | h3
      · exact absurd (le_sup_right.trans h3) h1
      · exact h3
    obtain ⟨hi, hs⟩ := GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h A B C hA hB hC hAB0 hBC0 (by rw [inf_comm B A]; exact hT.ge)
    rw [hs v hv, hi, map_mul]
    congr 1
    field_simp

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedIntertwinerCompOfAdjacentLatticesStatement
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  first | exact @GlobalTheory.FinWeil.normOp_comp_of_adj | exact GlobalTheory.FinWeil.normOp_comp_of_adj | (intros; apply GlobalTheory.FinWeil.normOp_comp_of_adj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdjacentSelfDualLatticeToward
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdjacentSelfDualLatticeToward
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem index_comap_toSpanSingleton_ne_zero {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) {y : X} (hy : y ∈ B) :
    (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index ≠ 0 := by
  have h1 : (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup =
      A.toAddSubgroup.comap (LinearMap.toSpanSingleton R X y).toAddMonoidHom := rfl
  rw [h1, AddSubgroup.index_comap]
  intro h0
  refine hAB (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
  rintro _ ⟨r, rfl⟩
  exact B.smul_mem r hy

theorem exists_mem_maximal_annihilator {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) (hBA : ¬ B ≤ A) :
    ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ ∀ r : R, r • x ∈ A ↔ r ∈ P := by
  have hex : ∃ n, ∃ y ∈ B, y ∉ A ∧
      (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index = n := by
    obtain ⟨y, hyB, hyA⟩ := SetLike.not_le_iff_exists.1 hBA
    exact ⟨_, y, hyB, hyA, rfl⟩
  obtain ⟨x, hxB, hxA, hx⟩ := Nat.find_spec hex
  have hne := index_comap_toSpanSingleton_ne_zero A B hAB hxB
  let P : Ideal R := A.comap (LinearMap.toSpanSingleton R X x)
  have hP : ∀ r : R, r • x ∈ A ↔ r ∈ P := fun r => Iff.rfl
  have hfin : Finite (R ⧸ P) := Nat.finite_of_card_ne_zero hne
  have hprime : P.IsPrime := by
    refine ⟨fun htop => hxA ?_, fun {r s} hrs => ?_⟩
    · have : (1 : R) ∈ P := htop ▸ Submodule.mem_top
      simpa using (hP 1).2 this
    · by_contra hcon
      rw [not_or] at hcon
      have hs : s • x ∉ A := fun h => hcon.2 ((hP s).1 h)
      have hmin := Nat.find_min' hex ⟨s • x, B.smul_mem s hxB, hs, rfl⟩
      have hne' := index_comap_toSpanSingleton_ne_zero A B hAB (B.smul_mem s hxB)
      have hle : (A.comap (LinearMap.toSpanSingleton R X x)).toAddSubgroup ≤
          (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup := by
        intro a ha
        have ha' : a • x ∈ A := ha
        show a • s • x ∈ A
        rw [smul_comm]
        exact A.smul_mem s ha'
      have hmul := AddSubgroup.relIndex_mul_index hle
      rw [← hx, ← hmul] at hmin
      have h1 : (A.comap (LinearMap.toSpanSingleton R X x)).toAddSubgroup.relIndex
          (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup = 1 := by
        rw [← hmul] at hne
        have h2 := Nat.pos_of_ne_zero (left_ne_zero_of_mul hne)
        have h3 := Nat.pos_of_ne_zero hne'
        nlinarith
      rw [AddSubgroup.relIndex_eq_one] at h1
      have hr : r ∈ (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup := by
        show r • s • x ∈ A
        rw [smul_smul]
        exact (hP _).2 hrs
      exact hcon.1 (h1 hr)
  haveI := hprime
  exact ⟨x, hxB, P, Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain _), hfin, hP⟩

theorem exists_adj_selfDual_step : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → ¬ B ≤ A → ∃ A' : Submodule R X, SelfDual γ A' ∧ Adj A A' ∧ A' ≤ (A' ⊓ A) ⊔ (A' ⊓ B) := by
  intro R X M _ _ _ _ _ σ w γ W h A B hA hB hAB hBA
  obtain ⟨x, hxB, P, hPm, hPf, hP⟩ := exists_mem_maximal_annihilator A B hAB hBA
  let T : Submodule R X := Submodule.span R {x}
  have hTB : T ≤ B := (Submodule.span_singleton_le_iff_mem x B).2 hxB
  have hxT : x ∈ T := Submodule.mem_span_singleton_self x
  let S : Submodule R X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [h.add_left, ha.2 t ht, hb.2 t ht, one_mul]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => h.zero_left t⟩
      smul_mem' := fun r a ha => ⟨A.smul_mem r ha.1, fun t ht => by
        rw [h.adj]
        exact ha.2 _ (T.smul_mem _ ht)⟩ }
  have hS : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  have hSA : S ≤ A := fun a ha => ha.1
  have hidx : A.toAddSubgroup.relIndex T.toAddSubgroup ≠ 0 := fun h0 =>
    hAB (AddSubgroup.relIndex_eq_zero_of_le_right (fun t ht => hTB ht) h0)
  obtain ⟨-, hdual, -⟩ := perfect_pairing_quotients h S.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup T.toAddSubgroup (fun a ha => ⟨fun h1 => h1.2, fun h1 => ⟨ha, h1⟩⟩)
    (fun t _ => ⟨fun h1 a ha => h.iso hA ha h1,
      fun h1 => (hA t).2 fun a ha => h.swap_eq_one (h1 a ha)⟩) hidx
  refine ⟨S ⊔ T, fun y => ⟨fun hy z hz => ?_, fun hy => ?_⟩,
    ⟨x, Submodule.mem_sup_right hxT, P, hPm, hPf, hP, ?_⟩, ?_⟩
  · obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨b, hb, u, hu, rfl⟩ := Submodule.mem_sup.1 hz
    rw [h.add_left, h.add_right, h.add_right, h.iso hA ha.1 hb.1, ha.2 u hu,
      h.swap_eq_one (hb.2 t ht), h.iso hB (hTB ht) (hTB hu)]
    simp
  · obtain ⟨t, ht, hyt⟩ := hdual y fun a _ ha =>
      h.swap_eq_one (hy a (Submodule.mem_sup_left ha))
    have ht' : t ∈ T := ht
    have h1 : y + -t ∈ S := by
      refine ⟨(hA _).2 fun a ha => h.swap_eq_one ?_, fun u hu => ?_⟩
      · rw [h.add_right, h.neg_right, hyt a ha, mul_inv_cancel₀ (h.ne_zero _ _)]
      · rw [h.add_left, hy u (Submodule.mem_sup_right hu),
          h.iso hB (B.neg_mem (hTB ht')) (hTB hu), one_mul]
    exact Submodule.mem_sup.2 ⟨_, h1, t, ht', by abel⟩
  · exact sup_le_sup_right (le_inf hSA le_sup_left) _
  · exact sup_le_sup (le_inf le_sup_left hSA) (le_inf le_sup_right hTB)

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdjacentSelfDualLatticeTowardStatement
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjacent_selfDual_lattice_toward : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → ¬ B ≤ A → ∃ A' : Submodule R X, SelfDual γ A' ∧ Adj A A' ∧ A' ≤ (A' ⊓ A) ⊔ (A' ⊓ B) := by
  first | exact @GlobalTheory.FinWeil.exists_adj_selfDual_step | exact GlobalTheory.FinWeil.exists_adj_selfDual_step | (intros; apply GlobalTheory.FinWeil.exists_adj_selfDual_step <;> assumption)
end
end

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem normOp_comp : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hlam A B C hA hB hC hAB hAC v hv
  induction hn : idx A B using Nat.strong_induction_on generalizing A v with
  | _ n ih =>
  by_cases hle : B ≤ A
  · have hAB' : A = B := by
      refine le_antisymm (fun x hx => (hB x).2 fun b hb => h.iso hA hx (hle hb)) hle
    subst hAB'
    obtain ⟨h1, h2⟩ := (GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A A hA).2.2 le_rfl
    have : normOp lam W A A v = v := by
      rw [normOp, h1, map_one, inv_one, one_smul, h2 v hv]
    rw [this]
  · obtain ⟨A', hA', hadj, hbet⟩ := GlobalTheory.T.exists_adjacent_selfDual_lattice_toward h A B hA hB hAB hle
    obtain ⟨x, hx, P, hP, hfin, hann, hgen⟩ := id hadj
    obtain ⟨e1, e2, -⟩ := GlobalTheory.T.adjacent_selfDual_lattices_index_simple h A A' hA hA' x hx P hP hfin hann hgen
    have hcard : 1 < Nat.card (R ⧸ P) := by
      haveI : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
      exact Finite.one_lt_card
    have hAA' : idx A A' ≠ 0 := by omega
    have hA'A : idx A' A ≠ 0 := by omega
    have hA'B : idx A' B ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hA'A hAB
    have hA'C : idx A' C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hA'A hAC
    have hmul := (GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h A A' B hA hA' hB hAA' hA'B hbet).1
    have hlt : idx A' B < n := by
      rw [← hn, hmul, e1]
      exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hA'B) hcard
    have hfix : Fixes W A' (normOp lam W A A' v) := by
      intro a ha
      rw [normOp, map_smul, ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A A' hA').2.1 hAA').2.1 v hv a ha]
    rw [← GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices h lam hlam A A' B hA hA' hB hadj hAB v hv,
      ih _ hlt A' hA' hA'B hA'C _ hfix rfl,
      GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices h lam hlam A A' C hA hA' hC hadj hAC v hv]

end GlobalTheory.FinWeil
