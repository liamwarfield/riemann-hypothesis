module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues
public import Formalism.UnipotentAdelicQuotients.EllRegCheck

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesOfLatticeVacuaEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesOfLatticeVacuaEqTop
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

open Classical in
open scoped BigOperators in
private theorem sum_over_quotient_fixed_of_fixed {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (S : AddSubgroup X)
    [Fintype (↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup)]
    (hSA : ∀ s ∈ S, s ∈ A) (y : M) (hy : ∀ s ∈ S, W s y = y) :
    ∀ b ∈ A, W b (∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
      W ((Quotient.out q : ↥A.toAddSubgroup) : X) y) =
      ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
        W ((Quotient.out q : ↥A.toAddSubgroup) : X) y := by
  intro b hb
  have hstep : ∀ x s : X, x ∈ A → s ∈ S → W (x + s) y = W x y := fun x s hx hs => by
    rw [← hW.comp_of_mem hA hx (hSA s hs), hy s hs]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  let b' : ↥A.toAddSubgroup := ⟨b, hb⟩
  refine Fintype.sum_equiv
    (Equiv.addLeft (QuotientAddGroup.mk b' : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup))
    _ _ (fun q => ?_)
  rw [hW.comp_of_mem hA hb (Quotient.out q).2 y]
  have hmem : -(b' + Quotient.out q) + Quotient.out ((QuotientAddGroup.mk b' :
      ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) + q) ∈ S.addSubgroupOf A.toAddSubgroup := by
    rw [← QuotientAddGroup.eq]
    simp [QuotientAddGroup.out_eq']
  simp only [Equiv.coe_addLeft]
  have hdec : ((Quotient.out ((QuotientAddGroup.mk b' :
      ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) + q) : ↥A.toAddSubgroup) : X) =
      (b + ((Quotient.out q : ↥A.toAddSubgroup) : X)) +
        ((-(b' + Quotient.out q) + Quotient.out ((QuotientAddGroup.mk b' :
          ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) + q) : ↥A.toAddSubgroup) : X) := by
    push_cast
    abel
  rw [hdec, hstep _ _ (A.add_mem hb (Quotient.out q).2) (AddSubgroup.mem_addSubgroupOf.mp hmem)]


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.span_translates_vacua : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ A : Submodule R X, _root_.GlobalTheory.FinWeil.SelfDual γ A → (∀ v : M, ∃ T : Submodule R X, _root_.GlobalTheory.FinWeil.idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ := by
  intro R X M _ _ _ _ _ σ w γ W hW A hA hloc
  rw [eq_top_iff]
  rintro v -
  obtain ⟨T, hT, hfix⟩ := hloc v
  have hAdual : ∀ x, x ∈ A ↔ ∀ a ∈ A, γ x a = 1 := by
    unfold _root_.GlobalTheory.FinWeil.SelfDual at hA
    exact hA
  unfold _root_.GlobalTheory.FinWeil.idx at hT
  let S : AddSubgroup X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [hW.add_left, ha.2 t ht, hb.2 t ht, one_mul]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => hW.zero_left t⟩
      neg_mem' := fun {a} ha => ⟨A.neg_mem ha.1, fun t ht => by
        rw [hW.neg_left, ha.2 t ht, inv_one]⟩ }
  have hSmem : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  let T₀ : AddSubgroup X := A.toAddSubgroup ⊓ T.toAddSubgroup
  have hS : ∀ a ∈ A.toAddSubgroup, a ∈ S ↔ ∀ t ∈ T.toAddSubgroup, γ a t = 1 :=
    fun a ha => ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have hT₀ : ∀ t ∈ T.toAddSubgroup, t ∈ T₀ ↔ ∀ a ∈ A.toAddSubgroup, γ a t = 1 := by
    intro t ht
    constructor
    · rintro ⟨htA, -⟩ a ha
      exact hW.iso hA ha htA
    · intro h
      exact ⟨(hAdual t).2 fun a ha => hW.swap_eq_one (h a ha), ht⟩
  have hidx : T₀.relIndex T.toAddSubgroup ≠ 0 := by
    rwa [AddSubgroup.inf_relIndex_right]
  obtain ⟨hKN, -, -⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW S A.toAddSubgroup T₀ T.toAddSubgroup hS hT₀ hidx
  have hK : S.relIndex A.toAddSubgroup ≠ 0 := hKN ▸ hidx
  obtain ⟨-, -, horth⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW T₀ T.toAddSubgroup S A.toAddSubgroup
    (fun t ht => by
      rw [hT₀ t ht]
      exact ⟨fun h a ha => hW.swap_eq_one (h a ha),
        fun h a ha => hW.swap_eq_one (h a ha)⟩)
    (fun a ha => by
      rw [hS a ha]
      exact ⟨fun h t ht => hW.swap_eq_one (h t ht),
        fun h t ht => hW.swap_eq_one (h t ht)⟩) hK
  haveI : (S.addSubgroupOf A.toAddSubgroup).FiniteIndex := ⟨hK⟩
  haveI : (T₀.addSubgroupOf T.toAddSubgroup).FiniteIndex := ⟨hidx⟩
  letI := Fintype.ofFinite (↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup)
  letI := Fintype.ofFinite (↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup)
  have hz : ∀ t ∈ T, (∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
      γ ((Quotient.out q : ↥A.toAddSubgroup) : X) t • W ((Quotient.out q : ↥A.toAddSubgroup) : X) v)
      ∈ Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} := by
    intro t ht
    have hy : ∀ s ∈ S, W s (W t v) = W t v := by
      intro s hs
      rw [hW.comm, hs.2 t ht, one_smul, hfix s hs.1 hs.2]
    have hu := sum_over_quotient_fixed_of_fixed hW hA S (fun s hs => hs.1) (W t v) hy
    set c := γ (w • -t) t with hc_def
    have hc : c ≠ 0 := hW.ne_zero _ _
    have key : (∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
        γ ((Quotient.out q : ↥A.toAddSubgroup) : X) t •
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) v) =
        W (-t) (c⁻¹ • ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) (W t v)) := by
      symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hW.comm _ t v, map_smul, hW.neg_comp,
        ← hc_def, smul_smul, smul_smul, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [key]
    refine Submodule.subset_span ⟨-t, c⁻¹ • ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) (W t v), ?_, rfl⟩
    unfold _root_.GlobalTheory.FinWeil.Fixes
    intro a ha
    rw [map_smul, hu a ha]
  have horth' : ∀ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
      ∑ p : ↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup,
        γ ((Quotient.out p : ↥T.toAddSubgroup) : X) ((Quotient.out q : ↥A.toAddSubgroup) : X) =
      if ((Quotient.out q : ↥A.toAddSubgroup) : X) ∈ S then
        ((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ) else 0 := fun q => by
    rw [← finsum_eq_sum_of_fintype]
    exact horth _ (Quotient.out q).2
  have hsum : (∑ p : ↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup,
      ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
        γ ((Quotient.out q : ↥A.toAddSubgroup) : X) (-((Quotient.out p : ↥T.toAddSubgroup) : X)) •
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) v) =
      ((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ) • v := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hW.neg_right, ← hW.swap, horth']
    rw [Finset.sum_eq_single 0]
    · have h0 : ((Quotient.out (0 : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) :
          ↥A.toAddSubgroup) : X) ∈ S :=
        AddSubgroup.mem_addSubgroupOf.mp
          ((QuotientAddGroup.eq_zero_iff _).mp (QuotientAddGroup.out_eq' 0))
      rw [if_pos h0, hfix _ h0.1 h0.2]
    · intro q _ hq
      have hqS : ¬ (((Quotient.out q : ↥A.toAddSubgroup) : X) ∈ S) := fun h => hq (by
        rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
        exact AddSubgroup.mem_addSubgroupOf.mpr h)
      rw [if_neg hqS, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hNne : ((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hidx
  have hv : v = (((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ))⁻¹ •
      ∑ p : ↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup,
        ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
          γ ((Quotient.out q : ↥A.toAddSubgroup) : X) (-((Quotient.out p : ↥T.toAddSubgroup) : X)) •
            W ((Quotient.out q : ↥A.toAddSubgroup) : X) v := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hNne, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun p _ =>
    hz _ (T.neg_mem (Quotient.out p).2))

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesOfLatticeVacuaEqTopStatement
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ := by
  first | exact @GlobalTheory.FinWeil.span_translates_vacua | exact GlobalTheory.FinWeil.span_translates_vacua | (intros; apply GlobalTheory.FinWeil.span_translates_vacua <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwiner
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwiner
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

end

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma lam_idx_sq_eq_idx_of_fixed_ne_zero (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (lam : ℕ →* ℂ) (hlam : _root_.GlobalTheory.FinWeil.GoodNorm σ lam) {A A' : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (hA' : _root_.GlobalTheory.FinWeil.SelfDual γ A')
    (hidx : _root_.GlobalTheory.FinWeil.idx A A' ≠ 0) {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (he0 : e ≠ 0) :
    lam (_root_.GlobalTheory.FinWeil.idx A A') ^ 2 = _root_.GlobalTheory.FinWeil.idx A A' := by
  have hAA := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A A hA e he Unit (fun _ => 0) (fun _ => zero_mem A)
    (fun b hb => ⟨(), by simpa using hb, fun _ _ => rfl⟩)
  have hcomp := _root_.GlobalTheory.FinWeil.normOp_comp hW lam hlam A A' A hA hA' hA hidx
    (by rw [hAA.2]; simp) e he
  obtain ⟨hsym, hback⟩ := _root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul hW A A' hA hA' hidx
  have hlin : ∀ (c : ℂ) (v : M),
      _root_.GlobalTheory.FinWeil.sumOp W A' A (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A' A v := by
    intro c v
    unfold _root_.GlobalTheory.FinWeil.sumOp
    simp only [map_smul]
    rw [smul_finsum]
  unfold _root_.GlobalTheory.FinWeil.normOp at hcomp
  rw [hAA.1, hAA.2, hsym, hlin, hback e he] at hcomp
  simp only [Fintype.card_unit, map_one, inv_one, one_smul, Finset.univ_unique,
    Finset.sum_singleton, hW.zero, smul_smul] at hcomp
  have hc0 : lam (_root_.GlobalTheory.FinWeil.idx A A') ≠ 0 := hlam.1 _ hidx
  have hz : ((lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ * (lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ *
      (_root_.GlobalTheory.FinWeil.idx A A' : ℂ) - 1) • e = 0 := by
    rw [sub_smul, one_smul, mul_assoc, hcomp, sub_self]
  have h1 := (smul_eq_zero.1 hz).resolve_right he0
  field_simp at h1
  linear_combination -h1

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma mul_conj_eq_natCast_of_sq_eq (c : ℂ) (n : ℕ) (h : c ^ 2 = n) :
    c * starRingEnd ℂ c = n := by
  have hn : ‖c‖ ^ 2 = n := by rw [← norm_pow, h, Complex.norm_natCast]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  push_cast
  rfl

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForm_translate_vacuum_eq_zero
    (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x u v, B (W x u) (W x v) = B u v) {e e' : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (he' : _root_.GlobalTheory.FinWeil.Fixes W A e') {z : X} (hz : z ∉ A) : B (W z e) e' = 0 := by
  obtain ⟨a, ha, hza⟩ : ∃ a ∈ A, γ z a ≠ 1 := by
    by_contra h
    push_neg at h
    exact hz ((hA z).2 h)
  have haz : γ a z ≠ 1 := fun h => hza (hW.swap_eq_one h)
  have key := hB a (W z e) e'
  rw [hW.comm, he a ha, he' a ha, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at key
  have : (γ a z - 1) * B (W z e) e' = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 haz)

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForm_translate_pair_eq (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (hB : ∀ x u v, B (W x u) (W x v) = B u v) (x y : X) (e e' : M) :
    B (W x e) (W y e') = γ (w • -y) x * (starRingEnd ℂ) (γ (w • -y) y) * B (W (-y + x) e) e' := by
  rw [← hB (-y) (W x e) (W y e'), hW.comp, hW.neg_comp]
  simp
  ring

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForms_eq_of_eq_on_vacua (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤)
    (B₁ B₂ : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (h₁ : ∀ x u v, B₁ (W x u) (W x v) = B₁ u v)
    (h₂ : ∀ x u v, B₂ (W x u) (W x v) = B₂ u v)
    (hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B₁ e e' = B₂ e e')
    (u v : M) : B₁ u v = B₂ u v := by
  have htr : ∀ z e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B₁ (W z e) e' = B₂ (W z e) e' := by
    intro z e e' he he'
    by_cases hz : z ∈ A
    · rw [he z hz]
      exact hvac e e' he he'
    · rw [invariantForm_translate_vacuum_eq_zero hW hA B₁ h₁ he he' hz,
        invariantForm_translate_vacuum_eq_zero hW hA B₂ h₂ he he' hz]
  have hS : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e},
      ∀ t ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s t = B₂ s t := by
    rintro s ⟨x, e, he, rfl⟩ t ⟨y, e', he', rfl⟩
    rw [invariantForm_translate_pair_eq hW B₁ h₁, invariantForm_translate_pair_eq hW B₂ h₂,
      htr _ e e' he he']
  have hleft : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s = B₂ s :=
    fun s hs => LinearMap.ext_on hspan (fun t ht => hS s hs t ht)
  have hflip : B₁.flip v = B₂.flip v :=
    LinearMap.ext_on hspan (fun s hs => by simp [hleft s hs])
  simpa using LinearMap.congr_fun hflip u


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.invForm_intertwiner : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam →
    ∀ A : Submodule R X, _root_.GlobalTheory.FinWeil.SelfDual γ A →
    Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ →
    ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → _root_.GlobalTheory.FinWeil.SelfDual γ (A.map φ) →
    _root_.GlobalTheory.FinWeil.idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) →
    (∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map φ) e) →
    ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) →
    ∀ u v, B (T u) (T v) = B u v := by
  intro R X M _ _ _ _ _ σ w γ W hW _ lam hlam A hA hspan φ _ hA' hidx T hT hTe B hB u v
  obtain ⟨n, f, hfB, hfu⟩ := _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A (A.map φ) hidx
  have hsum := fun e (he : _root_.GlobalTheory.FinWeil.Fixes W A e) =>
    _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A (A.map φ) hA' e he (Fin n) f hfB hfu
  have hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B (T e) (T e') = B e e' := by
    intro e e' he he'
    by_cases he0 : e = 0
    · subst he0
      simp
    have hn : _root_.GlobalTheory.FinWeil.idx A (A.map φ) = n := by simpa using (hsum e he).2
    have hc2 := lam_idx_sq_eq_idx_of_fixed_ne_zero hW lam hlam hA hA' hidx he he0
    rw [hn] at hc2
    have hcn := mul_conj_eq_natCast_of_sq_eq _ _ hc2
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hn ▸ hidx)
    have hT' : ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = (lam n)⁻¹ • ∑ i, W (f i) e := by
      intro e he
      rw [hTe e he]
      unfold _root_.GlobalTheory.FinWeil.normOp
      rw [hn, (hsum e he).1]
    have hterm : ∀ i j, B (W (f i) e) (W (f j) e') = if i = j then B e e' else 0 := by
      intro i j
      rw [← hB (-f j), hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB i),
        hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB j), neg_add_cancel,
        hW.zero]
      split_ifs with hij
      · subst hij
        rw [neg_add_cancel, hW.zero]
      · apply invariantForm_translate_vacuum_eq_zero hW hA B hB he he'
        intro hmem
        apply hij
        obtain ⟨k, -, hk⟩ := hfu (f i) (hfB i)
        rw [hk i (by simp), hk j (by show f i - f j ∈ A; rwa [sub_eq_neg_add])]
    rw [hT' e he, hT' e' he']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_sum, LinearMap.sum_apply,
      smul_eq_mul, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_inv₀]
    have hinv : (lam n)⁻¹ * (starRingEnd ℂ (lam n))⁻¹ * n = 1 := by
      rw [← mul_inv, hcn, inv_mul_cancel₀ hn0]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    linear_combination B e e' * hinv
  have key := invariantForms_eq_of_eq_on_vacua hW hA hspan ((B.comp T).compl₂ T) B
    (fun x u v => by simp [hT, hB]) hB (fun e e' he he' => by simpa using hvac e e' he he') u v
  simpa using key

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwinerStatement
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) → ∀ u v, B (T u) (T v) = B u v := by
  first | exact @GlobalTheory.FinWeil.invForm_intertwiner | exact GlobalTheory.FinWeil.invForm_intertwiner | (intros; apply GlobalTheory.FinWeil.invForm_intertwiner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationIndependentOfChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationIndependentOfChart
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

open GlobalTheory.SecGlue

namespace GlobalTheory.SecGlue.ChartIndep

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {f g : Sp S ⟶ Y}
    (e : f = g) (hf : f ⁻¹ᵁ V = ⊤) (hg : g ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hf x = chartHom V g hg x := by
  subst e; rfl

theorem chartHom_comp {Y : Scheme.{0}} (V : Y.Opens) {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') (f : Sp S ⟶ Y) (hf : f ⁻¹ᵁ V = ⊤) (hgf : (spMap g ≫ f) ⁻¹ᵁ V = ⊤)
    (x : Γ(Y, V)) : chartHom V (spMap g ≫ f) hgf x = g (chartHom V f hf x) := by
  unfold chartHom
  rw [← Scheme.Hom.appLE_comp_appLE (spMap g) f V ⊤ ⊤ hf.ge le_top]
  have h1 : Scheme.Hom.appLE (spMap g) ⊤ ⊤ le_top = (spMap g).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)
  rw [h1]
  change ((Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom.comp
    ((Spec.map (CommRingCat.ofHom g)).appTop.hom.comp (f.appLE V ⊤ hf.ge).hom)) x = _
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, h2]
  rfl

theorem chartHom_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) (hV : f ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hV x = chartHom W f hW (Y.presheaf.map (homOfLE hWV).op x) := by
  unfold chartHom
  rw [← Scheme.Hom.map_appLE f hW.ge (homOfLE hWV).op]
  rfl

theorem lands_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) : f ⁻¹ᵁ V = ⊤ :=
  top_le_iff.mp (hW.ge.trans (Scheme.Hom.preimage_mono f hWV))

theorem comb_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    {ι : Type} [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S)
    (h : IsCombIn W u c w a) : IsCombIn V u c w a := by
  obtain ⟨hu, hc, hw, hx⟩ := h
  refine ⟨lands_mono hWV u hu, lands_mono hWV c hc, fun i => lands_mono hWV (w i) (hw i), fun x => ?_⟩
  rw [chartHom_mono hWV c hc, chartHom_mono hWV u hu, hx]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartHom_mono hWV (w i) (hw i)]

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue.ChartIndep

variable {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (s : S)

noncomputable def locMap : Localization.Away s →+* Localization ((Submonoid.powers s).map q) :=
  IsLocalization.map (M := Submonoid.powers s) (S := Localization.Away s)
    (T := (Submonoid.powers s).map q) _ q (Submonoid.le_comap_map _)

theorem locMap_alg (x : S) :
    locMap q s (algebraMap S (Localization.Away s) x) =
      algebraMap T (Localization ((Submonoid.powers s).map q)) (q x) :=
  IsLocalization.map_eq (M := Submonoid.powers s) (S := Localization.Away s)
    (T := (Submonoid.powers s).map q) _ x

theorem locMap_surj (hq : Function.Surjective q) : Function.Surjective (locMap q s) :=
  IsLocalization.map_surjective_of_surjective (Submonoid.powers s) (Localization.Away s)
    (Localization ((Submonoid.powers s).map q)) hq

theorem locMap_ker (hk : RingHom.ker q ^ 2 = ⊥) : RingHom.ker (locMap q s) ^ 2 = ⊥ := by
  have hprod : ∀ a b : S, a ∈ RingHom.ker q → b ∈ RingHom.ker q → a * b = 0 := by
    intro a b ha hb
    have : a * b ∈ RingHom.ker q ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hk] at this
    exact (Submodule.mem_bot S).mp this

  have hform : ∀ x ∈ RingHom.ker (locMap q s), ∃ (k : S) (m : Submonoid.powers s),
      k ∈ RingHom.ker q ∧ x = IsLocalization.mk' (Localization.Away s) k m := by
    intro x hx
    obtain ⟨⟨k, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) x
    rw [RingHom.mem_ker] at hx
    simp only [locMap] at hx
    rw [IsLocalization.map_mk' (M := Submonoid.powers s) (S := Localization.Away s)
      (T := (Submonoid.powers s).map q), IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨m', hm'⟩, hm'k⟩ := hx
    obtain ⟨m'', hm'', rfl⟩ := Submonoid.mem_map.mp hm'
    refine ⟨m'' * k, ⟨m'', hm''⟩ * m, ?_, ?_⟩
    · rw [RingHom.mem_ker, map_mul]; exact hm'k
    · simp only
      rw [IsLocalization.mk'_eq_iff_eq]
      simp only [Submonoid.coe_mul]
      ring_nf
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨k, m, hk1, rfl⟩ := hform x hx
  obtain ⟨k', m', hk2, rfl⟩ := hform y hy
  rw [← IsLocalization.mk'_mul, hprod k k' hk1 hk2, IsLocalization.mk'_zero]
  exact Submodule.zero_mem _

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue.ChartIndep

theorem lands_loc {Y : Scheme.{0}} (W : Y.Opens) {S : Type} [CommRing S] (s : S) (f : Sp S ⟶ Y)
    (hs : ∀ p : Sp S, s ∉ p.asIdeal → p ∈ f ⁻¹ᵁ W) :
    (spMap (algebraMap S (Localization.Away s)) ≫ f) ⁻¹ᵁ W = ⊤ := by
  rw [Scheme.Hom.comp_preimage]
  refine top_le_iff.mp fun x _ => ?_
  rw [Scheme.Hom.mem_preimage]
  apply hs
  intro hx
  change s ∈ Ideal.comap (algebraMap S (Localization.Away s)) x.asIdeal at hx
  rw [Ideal.mem_comap] at hx
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.Away.algebraMap_isUnit s))

theorem eq_zero_of_loc {S : Type} [CommRing S] (D : S)
    (h : ∀ p : Ideal S, p.IsMaximal → ∃ s ∉ p, algebraMap S (Localization.Away s) D = 0) : D = 0 := by
  by_contra hD
  let I : Ideal S := LinearMap.ker (LinearMap.toSpanSingleton S S D)
  have hI : I ≠ ⊤ := by
    intro hI
    have : (1 : S) ∈ I := hI ▸ Submodule.mem_top
    simp [I] at this
    exact hD this
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsD⟩ := h p hp
  obtain ⟨⟨m, hm⟩, hmD⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ D).mp hsD
  obtain ⟨n, rfl⟩ := hm
  have : s ^ n ∈ I := by simp [I]; exact hmD
  exact hs (hp.isPrime.mem_of_pow_mem n (hIp this))

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue

open ChartIndep

theorem isCombIn_of_chart : ∀ (Y : Scheme.{0}) (V V' : Y.Opens), IsAffineOpen V → IsAffineOpen V' →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    (∀ i, spMap q ≫ w i = spMap q ≫ u) → GlobalTheory.SecGlue.IsCombIn V u c w a → u ⁻¹ᵁ V' = ⊤ →
    GlobalTheory.SecGlue.IsCombIn V' u c w a := by
  intro Y V V' hV _hV' S T _ _ q hq hk ι _ u c w a hw hcomb hu'

  have hqc : spMap q ≫ c = spMap q ≫ u := by
    have h1 := GlobalTheory.T.isAffineCombinationInChart_specMap_comp Y V S T q ι u c w a hcomb
    refine GlobalTheory.T.isAffineCombinationInChart_unique Y V hV T ι (spMap q ≫ u) _ _ (fun i => spMap q ≫ w i) (fun i => q (a i)) h1 ?_
    obtain ⟨hu1, _, hw1, _⟩ := h1
    refine ⟨hu1, hu1, hw1, fun x => ?_⟩
    have h0 : ∀ i, chartHom V (spMap q ≫ w i) (hw1 i) x - chartHom V (spMap q ≫ u) hu1 x = 0 :=
      fun i => by rw [chartHom_congr V (hw i) (hw1 i) hu1 x, sub_self]
    simp [h0]

  have hc' : c ⁻¹ᵁ V' = ⊤ := by rw [← GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u c hqc.symm V']; exact hu'
  have hw' : ∀ i, w i ⁻¹ᵁ V' = ⊤ := fun i => by
    rw [← GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u (w i) (hw i).symm V']; exact hu'
  have hWsame : ∀ W : Y.Opens, c ⁻¹ᵁ W = u ⁻¹ᵁ W ∧ ∀ i, w i ⁻¹ᵁ W = u ⁻¹ᵁ W := fun W =>
    ⟨(GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u c hqc.symm W).symm,
      fun i => (GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u (w i) (hw i).symm W).symm⟩
  obtain ⟨hu, _, _, _⟩ := hcomb
  refine ⟨hu', hc', hw', fun x => ?_⟩
  rw [← sub_eq_zero]
  apply eq_zero_of_loc
  intro p hp
  let P : Sp S := ⟨p, hp.isPrime⟩
  have hPV : u P ∈ V ⊓ V' := by
    refine ⟨(Scheme.Hom.mem_preimage u).mp ?_, (Scheme.Hom.mem_preimage u).mp ?_⟩
    · rw [hu]; trivial
    · rw [hu']; trivial
  obtain ⟨W, hWaff, hPW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)) hPV
  obtain ⟨_, ⟨s, rfl⟩, hPs, hsW⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := S)).exists_subset_of_mem_open
    (a := P) (u := ((u ⁻¹ᵁ W : (Sp S).Opens) : Set (Sp S)))
    ((Scheme.Hom.mem_preimage u).mpr hPW) (u ⁻¹ᵁ W).isOpen
  refine ⟨s, hPs, ?_⟩
  set g := algebraMap S (Localization.Away s) with hg
  have landW : ∀ f : Sp S ⟶ Y, f ⁻¹ᵁ W = u ⁻¹ᵁ W → (spMap g ≫ f) ⁻¹ᵁ W = ⊤ := by
    intro f hf
    refine lands_loc W s f fun p hp' => ?_
    rw [hf]
    exact hsW hp'
  set qs := locMap q s
  have hsq : spMap qs ≫ spMap g =
      spMap (algebraMap T (Localization ((Submonoid.powers s).map q))) ≫ spMap q := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext y
    exact locMap_alg q s y
  have hws : ∀ i, spMap qs ≫ (spMap g ≫ w i) = spMap qs ≫ (spMap g ≫ u) := fun i => by
    rw [← Category.assoc, hsq, Category.assoc, hw i, ← Category.assoc, ← hsq, Category.assoc]
  obtain ⟨d, hd, -, -⟩ := GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart Y W hWaff (Localization.Away s) _ qs (locMap_surj q s hq)
    (locMap_ker q s hk) ι (spMap g ≫ u) (fun i => spMap g ≫ w i) (fun i => g (a i)) (landW u rfl) hws
  have hcs := GlobalTheory.T.isAffineCombinationInChart_specMap_comp Y V S (Localization.Away s) g ι u c w a ⟨hu, by assumption, by assumption, by assumption⟩
  have hdc : d = spMap g ≫ c :=
    GlobalTheory.T.isAffineCombinationInChart_unique Y V hV _ ι _ _ _ _ _ (comb_mono (hWle.trans inf_le_left) _ _ _ _ hd) hcs
  have hV'd := comb_mono (hWle.trans inf_le_right) _ _ _ _ hd
  rw [hdc] at hV'd
  obtain ⟨h1, h2, h3, hx⟩ := hV'd
  have hxx := hx x
  have hsum : ∑ i, g (a i) * (chartHom V' (spMap g ≫ w i) (h3 i) x - chartHom V' (spMap g ≫ u) h1 x) =
      g (∑ i, a i * (chartHom V' (w i) (hw' i) x - chartHom V' u hu' x)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [chartHom_comp V' g (w i) (hw' i) (h3 i), chartHom_comp V' g u hu' h1, map_mul, map_sub]
  rw [hsum, chartHom_comp V' g c hc' h2, chartHom_comp V' g u hu' h1] at hxx
  rw [map_sub, map_add (f := _), hxx, sub_self]

end GlobalTheory.SecGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationIndependentOfChartStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineCombination_independent_of_chart : ∀ (Y : Scheme.{0}) (V V' : Y.Opens), IsAffineOpen V → IsAffineOpen V' →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    (∀ i, spMap q ≫ w i = spMap q ≫ u) → GlobalTheory.SecGlue.IsCombIn V u c w a → u ⁻¹ᵁ V' = ⊤ →
    GlobalTheory.SecGlue.IsCombIn V' u c w a := by
  first | exact @GlobalTheory.SecGlue.isCombIn_of_chart | exact GlobalTheory.SecGlue.isCombIn_of_chart | (intros; apply GlobalTheory.SecGlue.isCombIn_of_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableExtendByZeroOffSubset
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.HCA.SolSub

variable {d : ℕ}

theorem contDiff_dw {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) :
    ∀ w : List (Fin d), ContDiff ℝ ∞ (dw w f) := by
  intro w
  induction w with
  | nil => exact hf
  | cons j w ih =>
    show ContDiff ℝ ∞ (fun x => fderiv ℝ (dw w f) x (ev j))
    exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_dw {f : E d → ℂ} (hf : HasCompactSupport f) :
    ∀ w : List (Fin d), HasCompactSupport (dw w f) := by
  intro w
  induction w with
  | nil => exact hf
  | cons j w ih =>
    show HasCompactSupport (fun x => fderiv ℝ (dw w f) x (ev j))
    exact ih.fderiv_apply (𝕜 := ℝ) (ev j)

theorem contDiff_mul_of_on {U : Set (E d)} (hU : IsOpen U) {b φ : E d → ℂ}
    (hb : ContDiffOn ℝ ∞ b U) (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => b y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hb.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have hx' : x ∉ tsupport φ := fun h => hx (hs h)
    have h0 : φ =ᶠ[nhds x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    have : (fun y => b y * φ y) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem integrable_tr {ι : Type} (P : Sys d ι) {U : Set (E d)} (hU : IsOpen U)
    (ha : ∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) (i : ι) {φ : E d → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (P.tr i φ) := by
  unfold Sys.tr trOp
  refine MeasureTheory.integrable_finsetSum _ (fun n _ => MeasureTheory.integrable_finsetSum _ (fun w _ => ?_))
  refine Integrable.const_mul ?_ _
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (contDiff_dw (contDiff_mul_of_on hU (ha i n w) hφ hs) _).continuous
  · refine hasCompactSupport_dw ?_ _
    exact hc.mul_left

theorem norm_extendByZeroOffSubset_le {U : Set (E d)} (u : U →ᵇ ℂ) (x : E d) : ‖ext0 U u x‖ ≤ ‖u‖ := by
  by_cases hx : x ∈ U
  · simp only [ext0, hx, dif_pos]; exact u.norm_coe_le_norm _
  · simp [ext0, hx]

theorem aestronglyMeasurable_extendByZeroOffSubset {U : Set (E d)} (hU : IsOpen U) (u : U →ᵇ ℂ) :
    AEStronglyMeasurable (ext0 U u) volume := by
  have heq : U.indicator (ext0 U u) = ext0 U u := by
    funext x; by_cases hx : x ∈ U <;> simp [ext0, hx]
  have hc : ContinuousOn (ext0 U u) U := by
    rw [continuousOn_iff_continuous_restrict]
    have : U.domRestrict (ext0 U u) = u := by funext x; exact dif_pos x.2
    rw [this]; exact u.continuous
  have : AEStronglyMeasurable (U.indicator (ext0 U u)) volume :=
    (aestronglyMeasurable_indicator_iff hU.measurableSet).mpr (hc.aestronglyMeasurable hU.measurableSet)
  rwa [heq] at this

theorem integrable_extendByZeroOffSubset_mul {U : Set (E d)} (hU : IsOpen U) (u : U →ᵇ ℂ) {ψ : E d → ℂ}
    (hψ : Integrable ψ) : Integrable (fun x => ext0 U u x * ψ x) :=
  hψ.bdd_mul (aestronglyMeasurable_extendByZeroOffSubset hU u) (Filter.Eventually.of_forall fun x => norm_extendByZeroOffSubset_le u x)

theorem matrixExtendByZero_add {U : Set (E d)} (u v : U →ᵇ ℂ) (x : E d) :
    ext0 U (⇑(u + v)) x = ext0 U u x + ext0 U v x := by
  by_cases hx : x ∈ U <;> simp [ext0, hx]

theorem extendByZeroOffSubset_smul_apply {U : Set (E d)} (c : ℂ) (u : U →ᵇ ℂ) (x : E d) :
    ext0 U (⇑(c • u)) x = c * ext0 U u x := by
  by_cases hx : x ∈ U <;> simp [ext0, hx]

def pair {U : Set (E d)} (hU : IsOpen U) (ψ : E d → ℂ) (hψ : Integrable ψ) : (U →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x, ext0 U u x * ψ x
      map_add' := fun u v => by
        simp only [matrixExtendByZero_add, add_mul]
        exact integral_add (integrable_extendByZeroOffSubset_mul hU u hψ) (integrable_extendByZeroOffSubset_mul hU v hψ)
      map_smul' := fun c u => by
        simp only [extendByZeroOffSubset_smul_apply, mul_assoc, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul c _ }
    (∫ x, ‖ψ x‖) (fun u => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ x, ext0 U u x * ψ x‖ ≤ ∫ x, ‖u‖ * ‖ψ x‖ := by
            refine norm_integral_le_of_norm_le (hψ.norm.const_mul _) (Filter.Eventually.of_forall ?_)
            intro x
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (norm_extendByZeroOffSubset_le u x) (norm_nonneg _)
        _ = (∫ x, ‖ψ x‖) * ‖u‖ := by rw [integral_const_mul, mul_comm])

end GlobalTheory.HCA.SolSub


open GlobalTheory.HCA.SolSub in
theorem GlobalTheory.HCA.solSet_closed_submodule :
    ∀ (d : ℕ) (ι : Type) (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) →
      IsClosed (solSet P U) ∧ ∃ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U := by
  intro d ι P U hU ha
  have hint : ∀ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
      Integrable (P.tr i φ) := fun i φ h => SolSub.integrable_tr P hU ha i h.1 h.2.1 h.2.2
  have key : ∀ u : U →ᵇ ℂ, u ∈ solSet P U ↔
      ∀ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
        SolSub.pair hU (P.tr i φ) (hint i φ h) u = 0 := by
    intro u
    constructor
    · intro hu i φ h
      exact hu i φ h.1 h.2.1 h.2.2
    · intro hu i φ h1 h2 h3
      exact hu i φ ⟨h1, h2, h3⟩
  refine ⟨?_, ?_⟩
  · have : solSet P U = ⋂ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
        {u | SolSub.pair hU (P.tr i φ) (hint i φ h) u = 0} := by
      ext u; simp only [Set.mem_iInter, Set.mem_setOf_eq]; exact key u
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun φ => isClosed_iInter fun h =>
      isClosed_eq (SolSub.pair hU (P.tr i φ) (hint i φ h)).continuous continuous_const
  · refine ⟨{ carrier := solSet P U, add_mem' := ?_, zero_mem' := zero_mem_solSet P U, smul_mem' := ?_ }, rfl⟩
    · intro u v hu hv
      rw [key] at hu hv ⊢
      intro i φ h
      rw [map_add (f := _), hu i φ h, hv i φ h, add_zero]
    · intro c u hu
      rw [key] at hu ⊢
      intro i φ h
      rw [map_smul, hu i φ h, smul_zero]
end
end
