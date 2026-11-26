module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegSumLogDerivNonneg
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.TwoRealCharacters

theorem hasSum_re_neg_logDeriv (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (χ n).re * (vonMangoldt n / (n : ℝ) ^ σ))
      (-(deriv (LFunction χ) σ / LFunction χ σ).re) := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have h := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs] at h
  have h' := Complex.hasSum_re h
  convert (preTransparency := .reducible) h' using 1
  · funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast n,
        ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp [Pi.mul_apply, Complex.div_ofReal_re, mul_div_assoc]
  · rw [neg_div, Complex.neg_re]

theorem re_sum_nonneg (q : ℕ) (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (a : ZMod q) :
    0 ≤ ((1 : DirichletCharacter ℂ q) a).re + (χ a).re + (ψ a).re + ((χ * ψ) a).re := by
  by_cases ha : IsUnit a
  · have hsq : ∀ φ : DirichletCharacter ℂ q, φ ^ 2 = 1 → φ a = 1 ∨ φ a = -1 := by
      intro φ hφ
      apply mul_self_eq_one_iff.mp
      have hval := congrArg (fun ξ : DirichletCharacter ℂ q => ξ a) hφ
      simp only [MulChar.pow_apply' φ two_ne_zero, MulChar.one_apply ha] at hval
      rw [← pow_two]
      exact hval
    rw [MulChar.one_apply ha, MulChar.coeToFun_mul, Pi.mul_apply]
    rcases hsq χ hχ with h1 | h1 <;> rcases hsq ψ hψ with h2 | h2 <;> norm_num [h1, h2]
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha,
      MulChar.map_nonunit _ ha]
    simp

theorem neg_sum_logDeriv_nonneg : ∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q) (σ : ℝ), χ ^ 2 = 1 → ψ ^ 2 = 1 → 1 < σ → 0 ≤ -((deriv (LFunction (1 : DirichletCharacter ℂ q)) σ / LFunction (1 : DirichletCharacter ℂ q) σ).re + (deriv (LFunction χ) σ / LFunction χ σ).re + (deriv (LFunction ψ) σ / LFunction ψ σ).re + (deriv (LFunction (χ * ψ)) σ / LFunction (χ * ψ) σ).re) := by
  intro q _ χ ψ σ hχ hψ hσ
  have h := (((hasSum_re_neg_logDeriv q 1 σ hσ).add (hasSum_re_neg_logDeriv q χ σ hσ)).add
    (hasSum_re_neg_logDeriv q ψ σ hσ)).add (hasSum_re_neg_logDeriv q (χ * ψ) σ hσ)
  have hnn := h.nonneg fun n => by
    have h1 := re_sum_nonneg q χ ψ hχ hψ (n : ZMod q)
    have h2 : 0 ≤ vonMangoldt n / (n : ℝ) ^ σ :=
      div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
    have h3 := mul_nonneg h1 h2
    linarith
  linarith

end GlobalTheory.TwoRealCharacters
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitsAlgebraMap
namespace GlobalTheory.SplittingAdditive

open BigOperators

def Splits {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) (p : G → ℂ) : Prop :=
  ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
    (∀ i : Fin m, a i ∈ A ∧ b i ∈ A) ∧ ∀ x k : G, p (x * k) = ∑ i : Fin m, a i x * b i k

theorem splits_add {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) {p q : G → ℂ}
    (hp : Splits A p) (hq : Splits A q) : Splits A (p + q) := by
  obtain ⟨m, a, b, hab, h⟩ := hp
  obtain ⟨n, c, d, hcd, h'⟩ := hq
  refine ⟨m + n, Fin.append a c, Fin.append b d, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hab j
    · simpa using hcd j
  · intro x k
    rw [Fin.sum_univ_add]
    simp [h, h']

theorem splits_mul {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) {p q : G → ℂ}
    (hp : Splits A p) (hq : Splits A q) : Splits A (p * q) := by
  obtain ⟨m, a, b, hab, h⟩ := hp
  obtain ⟨n, c, d, hcd, h'⟩ := hq
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  refine ⟨m * n, fun j => a (e.symm j).1 * c (e.symm j).2,
    fun j => b (e.symm j).1 * d (e.symm j).2, ?_, ?_⟩
  · intro j
    exact ⟨A.mul_mem (hab _).1 (hcd _).1, A.mul_mem (hab _).2 (hcd _).2⟩
  · intro x k
    have key : ∀ f : Fin m × Fin n → ℂ, ∑ j : Fin (m * n), f (e.symm j) = ∑ q, f q :=
      fun f => Equiv.sum_comp e.symm f
    simp only [Pi.mul_apply]
    rw [key (fun q => a q.1 x * c q.2 x * (b q.1 k * d q.2 k)), h, h', Finset.sum_mul_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring

theorem splits_algebraMap {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) (r : ℂ) :
    Splits A (algebraMap ℂ (G → ℂ) r) := by
  refine ⟨1, fun _ => algebraMap ℂ (G → ℂ) r, fun _ => 1, ?_, ?_⟩
  · intro _
    exact ⟨A.algebraMap_mem r, A.one_mem⟩
  · intro x k
    simp

theorem main :
    ∀ {G : Type} [inst : Mul G] (S : Set (G → ℂ)),
      (∀ p ∈ S, ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
        (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
          ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k) →
      ∀ p ∈ Algebra.adjoin ℂ S, ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
        (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
          ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k := by
  intro G _ S hS p hp
  change Splits (Algebra.adjoin ℂ S) p
  induction hp using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap r => exact splits_algebraMap _ r
  | add x y _ _ hx hy => exact splits_add _ hx hy
  | mul x y _ _ hx hy => exact splits_mul _ hx hy

end GlobalTheory.SplittingAdditive
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumCosetRepsNeZeroIffCommensurable
namespace GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable

theorem finsum_quot_eq {V K : Type} [AddCommGroup V] [Field K] (f : V → K) (M N : AddSubgroup V)
    (S : Finset V) (hMN : M ≤ N) (hidx : M.relIndex N ≠ 0)
    (hf : ∀ v, ∀ u ∈ N, f (v + u) = f v)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) :
    ∑ᶠ c : V ⧸ M, f c.out = (M.relIndex N : K) * ∑ s ∈ S, f s := by
  classical
  haveI : Finite (N ⧸ M.addSubgroupOf N) := Nat.finite_of_card_ne_zero hidx
  letI : Fintype (N ⧸ M.addSubgroupOf N) := Fintype.ofFinite _
  let φ : V × (N ⧸ M.addSubgroupOf N) → V ⧸ M :=
    fun p => QuotientAddGroup.mk (p.1 + ((p.2.out : N) : V))
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := by
    intro v
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    have := hf v _ (hMN h)
    simpa using this
  rw [finsum_eq_sum_of_support_subset (s := (S ×ˢ Finset.univ).image φ)]
  · rw [Finset.sum_image]
    · rw [Finset.sum_product]
      have : ∀ s ∈ S, ∑ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = (M.relIndex N : K) * f s := by
        intro s _
        have : ∀ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = f s := by
          intro q
          simp only [φ]
          rw [hout, hf _ _ (q.out).2]
        simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card]
        rfl
      rw [Finset.sum_congr rfl this, Finset.mul_sum]
    · rintro ⟨s, q⟩ hp ⟨s', q'⟩ hp' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
      simp only [φ, QuotientAddGroup.eq] at h
      have hs : s = s' := by
        apply hinj s hp.1 s' hp'.1
        have h1 := N.add_mem (N.sub_mem (q'.out).2 (q.out).2) (N.neg_mem (hMN h))
        convert h1 using 1
        abel
      subst hs
      have hq : q = q' := by
        rw [← Quotient.out_eq q, ← Quotient.out_eq q']
        apply QuotientAddGroup.eq.2
        rw [AddSubgroup.mem_addSubgroupOf]
        convert h using 1
        push_cast
        abel
      rw [hq]
  · intro c hc
    obtain ⟨s, hs, hn⟩ := hcov c.out hc
    simp only [Finset.coe_image, Set.mem_image]
    refine ⟨(s, QuotientAddGroup.mk ⟨c.out - s, hn⟩), by simp [hs], ?_⟩
    have h : -(QuotientAddGroup.mk (⟨c.out - s, hn⟩ : N) : N ⧸ M.addSubgroupOf N).out
        + (⟨c.out - s, hn⟩ : N) ∈ M.addSubgroupOf N := by
      rw [← QuotientAddGroup.eq]; simp
    rw [AddSubgroup.mem_addSubgroupOf] at h
    conv_rhs => rw [← Quotient.out_eq c]
    apply QuotientAddGroup.eq.2
    convert h using 1
    push_cast
    abel

theorem sum_reps_ne_zero_iff : ∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0) := by
  intro V K _ _ _ f N N' S S' h1 h2 hf hf' hi hc hi' hc'
  have e1 : (N ⊓ N').relIndex N ≠ 0 := by rwa [AddSubgroup.inf_relIndex_left]
  have e2 : (N ⊓ N').relIndex N' ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have a := finsum_quot_eq f (N ⊓ N') N S inf_le_left e1 hf hi hc
  have b := finsum_quot_eq f (N ⊓ N') N' S' inf_le_right e2 hf' hi' hc'
  have c1 : (((N ⊓ N').relIndex N : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 e1
  have c2 : (((N ⊓ N').relIndex N' : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 e2
  rw [← mul_ne_zero_iff_left c1, ← a, b, mul_ne_zero_iff_left c2]

end GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumPiFinsetFinSuccCons
namespace GlobalTheory

open Finset

theorem sum_piFinset_fin_succ_cons {α K : Type} [AddCommMonoid K] (n : ℕ) (S : Finset α)
    (F : (Fin (n + 1) → α) → K) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S), F t =
      ∑ a ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) := by
  rw [← Finset.sum_product' S (Fintype.piFinset (fun _ : Fin n => S))
    (fun a t => F (Fin.cons a t))]
  symm
  refine Finset.sum_equiv (Fin.consEquiv (fun _ => α)) ?_ ?_
  · rintro ⟨a, t⟩
    simp [Fin.forall_fin_succ, Fin.consEquiv]
  · rintro ⟨a, t⟩ _
    rfl

theorem weighted_sum_piFinset_fin {α K : Type} [CommRing K] (G : (α → K) → Prop)
    (S S' : Finset α) (w w' : K)
    (h : ∀ f, G f → w * ∑ a ∈ S, f a = w' * ∑ a ∈ S', f a) (n : ℕ) :
    ∀ F : (Fin n → α) → K, (∀ (t : Fin n → α) (i : Fin n), G (fun a => F (Function.update t i a))) →
      w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F t =
        w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F t := by
  induction n with
  | zero => intro F _; simp
  | succ n ih =>
    intro F hF
    have h1 : ∀ a : α, w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) =
        w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F (Fin.cons a t) := by
      intro a
      refine ih (fun t => F (Fin.cons a t)) ?_
      intro t i
      have := hF (Fin.cons a t) i.succ
      simpa only [← Fin.cons_update] using this
    have h2 : ∀ t : Fin n → α, w * ∑ a ∈ S, F (Fin.cons a t) =
        w' * ∑ a ∈ S', F (Fin.cons a t) := by
      intro t
      rcases isEmpty_or_nonempty α with hα | ⟨⟨a0⟩⟩
      · simp [Finset.eq_empty_of_isEmpty S, Finset.eq_empty_of_isEmpty S']
      · refine h _ ?_
        have := hF (Fin.cons a0 t) 0
        simpa only [Fin.update_cons_zero] using this
    rw [sum_piFinset_fin_succ_cons, sum_piFinset_fin_succ_cons]
    calc w ^ (n + 1) * ∑ a ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t)
        = w * ∑ a ∈ S, w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) := by
          rw [← Finset.mul_sum]; ring
      _ = w * ∑ a ∈ S, w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F (Fin.cons a t) := by
          simp only [h1]
      _ = w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), w * ∑ a ∈ S, F (Fin.cons a t) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]; ring
      _ = w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), w' * ∑ a ∈ S', F (Fin.cons a t) := by
          simp only [h2]
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_comm]; ring

theorem weighted_sum_piFinset : ∀ (ι α K : Type) [Fintype ι] [DecidableEq ι] [CommRing K] (G : (α → K) → Prop) (S S' : Finset α) (w w' : K), (∀ f, G f → w * ∑ a ∈ S, f a = w' * ∑ a ∈ S', f a) → ∀ F : (ι → α) → K, (∀ (t : ι → α) (i : ι), G (fun a => F (Function.update t i a))) → w ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S), F t = w' ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S'), F t := by
  intro ι α K _ _ _ G S S' w w' h F hF
  let e := Fintype.equivFin ι
  have key : ∀ T : Finset α, ∑ t ∈ Fintype.piFinset (fun _ : ι => T), F t =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin (Fintype.card ι) => T), F (t ∘ e) := by
    intro T
    symm
    refine Finset.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl α)) ?_ ?_
    · intro t
      simp only [Fintype.mem_piFinset, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl,
        Function.comp, id]
      exact ⟨fun H i => H _, fun H i => by simpa using H (e.symm i)⟩
    · intro t _
      rfl
  rw [key, key]
  refine weighted_sum_piFinset_fin G S S' w w' h _ (fun t => F (t ∘ e)) ?_
  intro t i
  simp only [Function.update_comp_equiv]
  exact hF _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivativeBound
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.logDerivativeThreeFourOne

lemma comb_nonneg {z : ℂ} (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have h : z.re ^ 2 + z.im ^ 2 = 1 := by
    have e := Complex.normSq_eq_norm_sq z
    rw [hz, Complex.normSq_apply] at e
    nlinarith
  have e2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by simp [sq]
  rw [e2]
  nlinarith [sq_nonneg (z.re + 1)]

lemma neg_logDeriv_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (LSeries.term ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ))) s n).re)
      (-(deriv (LFunction χ) s / LFunction χ s).re) := by
  have h := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs] at h
  have h' := Complex.hasSum_re h
  simpa [neg_div] using h'

lemma term_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term ((fun n : ℕ => (1 : DirichletCharacter ℂ q) n) *
          (fun n : ℕ => (vonMangoldt n : ℂ))) σ n).re
      + 4 * (LSeries.term ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
          (σ + t * I) n).re
      + (LSeries.term ((fun n : ℕ => (χ ^ 2) n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
          (σ + 2 * t * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hA : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) σ
  set A : ℝ := (n : ℝ) ^ σ with hAdef
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  set b : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hbdef
  have ha : (n : ℂ) ^ (σ : ℂ) = (A : ℂ) := by
    rw [hAdef, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_cast
  have hb : ‖b‖ = 1 := by
    rw [hbdef, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hb0 : b ≠ 0 := by
    rintro h
    simp [h] at hb
  have e1 : (n : ℂ) ^ ((σ : ℂ) + t * I) = A * b := by
    rw [cpow_add _ _ hn', ha]
  have e2 : (n : ℂ) ^ ((σ : ℂ) + 2 * t * I) = A * b ^ 2 := by
    rw [cpow_add _ _ hn', ha, hbdef, ← cpow_nat_mul]
    push_cast
    ring_nf
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  simp only [Pi.mul_apply]
  rw [e1, e2, ha]
  set c : ℝ := vonMangoldt n / A with hcdef
  have hc : 0 ≤ c := div_nonneg vonMangoldt_nonneg hA.le
  by_cases hu : IsUnit (n : ZMod q)
  · have hz : ‖χ n / b‖ = 1 := by
      rw [norm_div, hb, div_one]
      simpa using χ.unit_norm_eq_one hu.unit
    have k1 : (1 : DirichletCharacter ℂ q) n * (vonMangoldt n : ℂ) / (A : ℂ) = (c : ℂ) := by
      rw [MulChar.one_apply hu, one_mul, hcdef, Complex.ofReal_div]
    have k2 : χ n * (vonMangoldt n : ℂ) / ((A : ℂ) * b) = (c : ℂ) * (χ n / b) := by
      rw [hcdef, Complex.ofReal_div]
      field_simp
    have k3 : (χ ^ 2) n * (vonMangoldt n : ℂ) / ((A : ℂ) * b ^ 2) = (c : ℂ) * (χ n / b) ^ 2 := by
      rw [MulChar.pow_apply' χ two_ne_zero, hcdef, Complex.ofReal_div]
      field_simp
    rw [k1, k2, k3, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have hcomb := comb_nonneg hz
    nlinarith [mul_nonneg hc hcomb]
  · simp [MulChar.map_nonunit _ hu]

theorem three_four_one : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ), 1 < σ → 0 ≤ -(3 * (deriv (LFunction (1 : DirichletCharacter ℂ q)) σ / LFunction (1 : DirichletCharacter ℂ q) σ).re + 4 * (deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)).re + (deriv (LFunction (χ ^ 2)) (σ + 2 * t * I) / LFunction (χ ^ 2) (σ + 2 * t * I)).re) := by
  intro q _ χ σ t hσ
  have h1 := neg_logDeriv_eq (1 : DirichletCharacter ℂ q) (s := (σ : ℂ)) (by simpa using hσ)
  have h2 := neg_logDeriv_eq χ (s := (σ : ℂ) + t * I) (by simpa using hσ)
  have h3 := neg_logDeriv_eq (χ ^ 2) (s := (σ : ℂ) + 2 * t * I) (by simpa using hσ)
  have h := ((h1.mul_left 3).add (h2.mul_left 4)).add h3
  have hnn := h.nonneg (fun n => term_nonneg χ σ t n)
  linarith

end GlobalTheory.logDerivativeThreeFourOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralComplexEqLintegralSqrtMulExp
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImageSqIoi
namespace GlobalTheory.SquareImageInterval

open MeasureTheory

theorem image_sq_Ioi : (fun r : ℝ => r ^ 2) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact pow_pos (Set.mem_Ioi.1 hr) 2
  · intro hy
    exact ⟨√y, Real.sqrt_pos.2 hy, Real.sq_sqrt (le_of_lt hy)⟩

theorem main : ∀ (G : ℝ → ENNReal), ∫⁻ (r : ℝ) in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r
    = ∫⁻ (u : ℝ) in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G √u := by
  intro G
  have hinj : Set.InjOn (fun r : ℝ => r ^ 2) (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    have h2 : a ^ 2 = b ^ 2 := hab
    nlinarith [h2]
  have hder : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * x) (Set.Ioi 0) x := by
    intro x _
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj
    (fun u => (2 : ENNReal)⁻¹ * G √u)
  rw [image_sq_Ioi] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  have hx' : 0 < x := hx
  simp only
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * x), Real.sqrt_sq (le_of_lt hx'),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  calc ENNReal.ofReal x * G x = (2 * 2⁻¹) * (ENNReal.ofReal x * G x) := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ = 2 * ENNReal.ofReal x * (2⁻¹ * G x) := by ring

end GlobalTheory.SquareImageInterval
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralComplexEqLintegralSqrtMulExp
open MeasureTheory

namespace GlobalTheory

theorem lintegral_Ioi_mul_eq_lintegral_Ioi_sqrt (G : ℝ → ENNReal) :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r
      = ∫⁻ u in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G (Real.sqrt u) := by
  apply _root_.GlobalTheory.SquareImageInterval.main <;> assumption

theorem lintegral_complex_eq_lintegral_sqrt_mul_exp (ε c : ℝ) (hε : ε = 1 ∨ ε = -1)
    (g : ℂ → ENNReal) (hg : Measurable g) (h0 : g 0 = 0) :
    ∫⁻ z, g z = ∫⁻ t : ℝ, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
      (2 : ENNReal)⁻¹ *
        g ((Real.sqrt (ε * (t - c)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  set G : ℝ → ENNReal := fun r => ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
    g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) with hG
  have h1 : ∫⁻ z, g z = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r := by
    rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod]
    have hm : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal p.1 * g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by
      refine (ENNReal.measurable_ofReal.comp measurable_fst).mul (hg.comp ?_)
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)).measurable
    have he : (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • g (Complex.polarCoord.symm p))
        = fun p : ℝ × ℝ =>
          ENNReal.ofReal p.1 * g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by
      funext p
      simp [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
    rw [he, setLIntegral_prod _ hm.aemeasurable]
    refine lintegral_congr fun r => ?_
    simp only [hG]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h2 : ∫⁻ u in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G (Real.sqrt u)
      = ∫⁻ u, (2 : ENNReal)⁻¹ * G (Real.sqrt u) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, Real.sqrt_eq_zero_of_nonpos (not_lt.1 hu)]
      simp [hG, h0]
  have h3 : ∀ F : ℝ → ENNReal, ∫⁻ u, F u = ∫⁻ t, F (ε * (t - c)) := by
    intro F
    rw [lintegral_sub_right_eq_self (fun u => F (ε * u)) c]
    rcases hε with rfl | rfl
    · simp
    · simp only [neg_mul, one_mul]
      exact (lintegral_neg_eq_self F).symm
  rw [h1, lintegral_Ioi_mul_eq_lintegral_Ioi_sqrt, h2, h3]
  refine lintegral_congr fun t => ?_
  simp only [hG]
  rw [lintegral_const_mul' _ _ (by norm_num)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralComplexEqLintegralSqrtMulExpStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_eq_polar_sqrt : ∀ (ε c : ℝ), (ε = 1 ∨ ε = -1) → ∀ g : ℂ → ENNReal, Measurable g → g 0 = 0 → ∫⁻ z, g z = ∫⁻ t : ℝ, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, (2 : ENNReal)⁻¹ * g ((Real.sqrt (ε * (t - c)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  first | exact @GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp | exact GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp | (intros; apply GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableAtFractInt
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZetaEqSubIntegralFract
namespace GlobalTheory.ZetaFractionalIntegral

open MeasureTheory Set Filter Asymptotics

lemma zeta_eq_mul_integral_floor {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (fun _ : ℕ ↦ (1 : ℝ)) k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.isBigO_of_le _ fun n ↦ ?_
    simp
  have key := LSeries_eq_mul_integral_of_nonneg (fun _ ↦ (1 : ℝ)) zero_le_one hs hO (fun _ ↦ zero_le_one)
  have e1 : LSeries (fun n : ℕ ↦ (((fun _ : ℕ ↦ (1 : ℝ)) n : ℝ) : ℂ)) s = riemannZeta s := by
    rw [← LSeries_one_eq_riemannZeta hs]
    congr 1
  rw [← e1, key]
  congr 2
  funext t
  simp

lemma integrableOn_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi 1) := integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos

lemma integrableOn_fract_mul {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hg : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re, Complex.add_re, Complex.one_re]; linarith) one_pos
  refine MeasureTheory.Integrable.mono hg (((Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable).mul
    hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1.le
  calc ‖((Int.fract t : ℝ) : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖ ≤ 1 * ‖(t : ℂ) ^ (-(s + 1))‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = ‖(t : ℂ) ^ (-(s + 1))‖ := one_mul _

theorem zeta_eq_sub_integral_fract :
    (let d1 : ℂ → ℂ := @(fun (s : ℂ) ↦ ∫ (t : ℝ) in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (↑t : ℂ) ^ (-(s + (1 : ℂ)))); ∀ {s : ℂ}, (1 : ℝ) < Complex.re s → riemannZeta s = s / (s - (1 : ℂ)) - s * d1 s) := by
  intro d1 s hs
  simp only [d1]
  have hA := integrableOn_cpow_neg hs
  have hB := integrableOn_fract_mul hs
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s)) -
        ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← integral_sub hA hB]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      rw [Int.self_sub_fract, natCast_floor_eq_intCast_floor ht0.le]
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = -(s + 1) + 1 by ring, Complex.cpow_add _ _ (by exact_mod_cast ht0.ne'), Complex.cpow_one,
        mul_comm]
    have hfl' : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, hfl, Complex.ofReal_sub]
    rw [hpow, hfl']
    ring
  have hI : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos, Complex.ofReal_one,
      Complex.one_cpow, show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
  rw [zeta_eq_mul_integral_floor hs, hsplit, hI]
  ring

end GlobalTheory.ZetaFractionalIntegral
end

open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology

namespace GlobalTheory.ZetaHalfPlane

noncomputable def fractInt (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

noncomputable def cutFract : ℝ → ℂ := (Ioi (1 : ℝ)).indicator fun t => ((Int.fract t : ℝ) : ℂ)

lemma norm_fract_le (t : ℝ) : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
  exact (Int.fract_lt_one t).le

lemma norm_cutFract_le (t : ℝ) : ‖cutFract t‖ ≤ 1 :=
  (norm_indicator_le_norm_self _ _).trans (norm_fract_le t)

lemma measurable_fract_ofReal : Measurable fun t : ℝ => ((Int.fract t : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp measurable_fract

lemma measurable_cutFract : Measurable cutFract :=
  measurable_fract_ofReal.indicator measurableSet_Ioi

lemma fractInt_eq_mellin (s : ℂ) : fractInt s = mellin cutFract (-s) := by
  unfold fractInt mellin cutFract
  have h : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • (Ioi (1 : ℝ)).indicator
      (fun t => ((Int.fract t : ℝ) : ℂ)) t = (Ioi (1 : ℝ)).indicator
      (fun t => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul, mul_comm,
        show -s - 1 = -(s + 1) by ring]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

lemma differentiableAt_fractInt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ fractInt s := by
  have h1 : DifferentiableAt ℂ (mellin cutFract) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const (1 : ℝ)).mono measurable_cutFract.aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => by simpa using norm_cutFract_le t
    · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
      simpa using norm_cutFract_le t
    · simpa using hs
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      have : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
      filter_upwards [this] with t ht
      have ht' : t ∉ Ioi (1 : ℝ) := fun h => lt_asymm (mem_Iio.1 ht) (mem_Ioi.1 h)
      rw [cutFract, indicator_of_notMem ht', norm_zero]
      positivity
    · simp
  have h2 : fractInt = fun s => mellin cutFract (-s) := funext fractInt_eq_mellin
  rw [h2]
  exact h1.comp s differentiableAt_id.neg

lemma norm_integrand_le (s : ℂ) {t : ℝ} (ht : t ∈ Ioi (1 : ℝ)) :
    ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-(s.re + 1)) := by
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  simp only [neg_re, add_re, one_re]
  exact mul_le_of_le_one_left (by positivity) (norm_fract_le t)

lemma norm_fractInt_le {s : ℂ} (hs : 0 < s.re) : ‖fractInt s‖ ≤ 1 / s.re := by
  have h : -(s.re + 1) < -1 := by linarith
  calc ‖fractInt s‖ ≤ ∫ t in Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt h one_pos) ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun t ht => norm_integrand_le s ht
    _ = 1 / s.re := by
        rw [integral_Ioi_rpow_of_lt h one_pos, Real.one_rpow,
          show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]

lemma integrableOn_integrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have h : (-(s + 1)).re < -1 := by simp; linarith
  exact (integrableOn_Ioi_cpow_of_lt h one_pos).bdd_mul (c := 1)
    measurable_fract_ofReal.aestronglyMeasurable (Eventually.of_forall norm_fract_le)

lemma zeta_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * fractInt s := by
  apply _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract <;> assumption

theorem zeta_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * fractInt s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hf : AnalyticOnNhd ℂ riemannZeta₀ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₀.differentiableOn.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun z => 1 - z * fractInt z) {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      ((differentiableAt_const _).sub
        (differentiableAt_id.mul (differentiableAt_fractInt hz))).differentiableWithinAt) hU
  have key : ∀ z : ℂ, z ≠ 1 → z / (z - 1) = (z - 1)⁻¹ + 1 := by
    intro z hz
    have := sub_ne_zero.2 hz
    field_simp
    ring
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp) (by
      have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
      filter_upwards [this] with z hz
      have hz1 : z ≠ 1 := by
        rintro rfl
        simp at hz
      have h1 := zeta_eq_of_one_lt hz
      rw [riemannZeta_eq_inv_sub_add hz1, key z hz1] at h1
      linear_combination h1)
  have h2 : riemannZeta₀ s = 1 - s * fractInt s := heq hs
  rw [riemannZeta_eq_inv_sub_add hs1, key s hs1, h2]
  ring

theorem norm_zeta_sub_le :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → ‖riemannZeta s - s / (s - 1)‖ ≤ ‖s‖ / s.re := by
  intro s hs hs1
  rw [zeta_eq hs hs1, sub_sub_cancel_left, norm_neg, norm_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (norm_fractInt_le hs) (norm_nonneg s)

end GlobalTheory.ZetaHalfPlane
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteOfFiniteQuotMapOfIsPrecomplete
open IsLocalRing

namespace GlobalTheory

theorem nak_mem_smul_top_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Ideal R) (x : ι → R) :
    x ∈ J • (⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun x => ∀ i, x i ∈ J) hx ?_ ?_
    · intro a ha m _ i; exact J.mul_mem_right _ ha
    · intro a b ha hb i; exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [show x = ∑ i, x i • Pi.single i (1 : R) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

theorem nak_isPrecomplete_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I (ι → R) := by
  have key : ∀ k (x : ι → R), x ∈ I ^ k • (⊤ : Submodule R (ι → R)) ↔
      ∀ i, x i ∈ I ^ k • (⊤ : Submodule R R) := by
    intro k x
    rw [nak_mem_smul_top_pi]
    simp only [smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ l : R, ∀ n, f n i ≡ l [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (fun n => f n i) fun {m n} hmn => ?_
    have := (hf hmn)
    rw [SModEq.sub_mem] at this ⊢
    exact (key m _).1 this i
  choose l hl using hc
  refine ⟨l, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  exact SModEq.sub_mem.1 (hl i n)

theorem finite_of_finite_quot_map_of_isPrecomplete :
    ∀ (O A : Type) [CommRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A]
      (J : Ideal O) [IsPrecomplete J O], J.map (algebraMap O A) ≠ ⊤ →
      Module.Finite O (A ⧸ J.map (algebraMap O A)) → Module.Finite O A := by
  intro O A _ _ _ _ _ J _ hJ hfin
  have hsm : ∀ n : ℕ, (J ^ n • (⊤ : Submodule O A)) =
      Submodule.restrictScalars O ((J.map (algebraMap O A)) ^ n) := by
    intro n
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
  have hH : IsHausdorff J A := by
    refine ⟨fun x hx => ?_⟩
    have : x ∈ ⨅ n : ℕ, (J.map (algebraMap O A)) ^ n := by
      rw [Submodule.mem_iInf]
      intro n
      have h1 := SModEq.sub_mem.1 (hx n)
      rw [sub_zero, hsm n] at h1
      exact h1
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ] at this
    exact this
  set I := J.map (algebraMap O A) with hI
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := A ⧸ I)
  choose s' hs' using fun i => Ideal.Quotient.mk_surjective (s i)
  have : IsPrecomplete J (Fin r → O) := nak_isPrecomplete_pi _
  have hsurj : Function.Surjective ((J • (⊤ : Submodule O A)).mkQ ∘ₗ
      Fintype.linearCombination O s') := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx : (Ideal.Quotient.mk I x) ∈ Submodule.span O (Set.range s) := by
      rw [hs]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    refine ⟨c, ?_⟩
    have hq : Ideal.Quotient.mk I (Fintype.linearCombination O s' c) = Ideal.Quotient.mk I x := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Fintype.linearCombination_apply, map_sum, ← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, ← hs' i, Algebra.smul_def]
      rfl
    have hmem : Fintype.linearCombination O s' c - x ∈ I := by
      rw [← Ideal.Quotient.eq]; exact hq
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have h1 := hsm 1
    simp only [pow_one] at h1
    rw [h1]
    exact hmem
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end GlobalTheory
end
