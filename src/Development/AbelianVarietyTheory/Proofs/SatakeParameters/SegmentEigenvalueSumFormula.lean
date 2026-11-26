module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentEigenvalueSumFormula
namespace GlobalTheory

theorem multiset_mem_list_sum' {α : Type*} (l : List (Multiset α)) (x : α) :
    x ∈ l.sum ↔ ∃ m ∈ l, x ∈ m := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.sum_cons, Multiset.mem_add, ih]

theorem multiset_le_list_sum' {α : Type*} (l : List (Multiset α)) (m : Multiset α) (h : m ∈ l) :
    m ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Multiset.le_add_right _ _
    · exact (ih h).trans (Multiset.le_add_left _ _)

theorem norm_natCast_cpow_ofReal {q : ℕ} (hq : 0 < q) (s : ℝ) :
    ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s := by
  rw [Complex.norm_natCast_cpow_of_pos hq]
  simp

theorem rpow_exponent_inj_of_one_lt {b : ℝ} (hb : 1 < b) {x y : ℝ} (h : b ^ x = b ^ y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))
  · exact hxy
  · exact absurd h (ne_of_gt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSumLt
namespace GlobalTheory.NormSumLt

universe u_1

theorem norm_sum_lt {K : Type u_1} [NormedField K] [IsUltrametricDist K] (s : Finset ℕ) (f : ℕ → K)
    {r : ℝ} (hr : (0 : ℝ) < r) (h : ∀ i ∈ s, ‖f i‖ < r) : ‖∑ i ∈ s, f i‖ < r := by
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖f a‖ < r := h a (Finset.mem_insert_self a s)
    have h2 : ‖∑ i ∈ s, f i‖ < r := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)

theorem main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] (s : Finset ℕ) (f : ℕ → K) {r : ℝ}, (0 : ℝ) < r → (∀ i ∈ s, ‖f i‖ < r) → ‖∑ i ∈ s, f i‖ < r :=
  by
  intro K _ _ s f r hr h
  exact norm_sum_lt s f hr h

end GlobalTheory.NormSumLt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlace
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_finset_sum_lt_of_forall_lt {K : Type*} [NormedField K] [IsUltrametricDist K]
    (s : Finset ℕ) (f : ℕ → K) {r : ℝ} (hr : 0 < r) (h : ∀ i ∈ s, ‖f i‖ < r) :
    ‖∑ i ∈ s, f i‖ < r := by
  apply _root_.GlobalTheory.NormSumLt.main <;> assumption

theorem norm_le_one_of_isIntegral_int {K : Type*} [NormedField K] [IsUltrametricDist K]
    {z : K} (hz : IsIntegral ℤ z) : ‖z‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hz
  by_contra hlt
  push_neg at hlt
  set n := p.natDegree
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree,
    hm.leadingCoeff, map_one, one_mul] at hp
  set S := ∑ i ∈ Finset.range n, (algebraMap ℤ K) (p.coeff i) * z ^ i
  have hS : ‖S‖ < ‖z‖ ^ n := by
    refine norm_finset_sum_lt_of_forall_lt _ _ (pow_pos (by linarith) n) ?_
    intro i hi
    rw [norm_mul, norm_pow]
    have h1 : ‖(algebraMap ℤ K) (p.coeff i)‖ ≤ 1 := by
      rw [eq_intCast]; exact IsUltrametricDist.norm_intCast_le_one K _
    calc ‖(algebraMap ℤ K) (p.coeff i)‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ i :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg _) _)
      _ = ‖z‖ ^ i := one_mul _
      _ < ‖z‖ ^ n := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  have h2 : z ^ n = -S := by linear_combination hp
  have h3 : ‖z‖ ^ n = ‖S‖ := by rw [← norm_pow, h2, norm_neg]
  linarith

theorem exists_embedding_padicAlgCl_place (E : Type) [Field E] [NumberField E] (l : ℕ)
    [Fact l.Prime] : ∃ (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E)),
      ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal := by
  let τ : E →+* PadicAlgCl l := (IsAlgClosed.lift : E →ₐ[ℚ] PadicAlgCl l).toRingHom
  have hle : ∀ x : 𝓞 E, ‖τ (x : E)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral_int ((x.isIntegral_coe).map τ.toIntAlgHom)
  let I : Ideal (𝓞 E) :=
    { carrier := {x | ‖τ (x : E)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        push_cast
        rw [map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        push_cast
        rw [map_mul, norm_mul]
        calc ‖τ (c : E)‖ * ‖τ (x : E)‖ ≤ 1 * ‖τ (x : E)‖ :=
              mul_le_mul_of_nonneg_right (hle c) (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hx }
  have hmem : ∀ x : 𝓞 E, x ∈ I ↔ ‖τ (x : E)‖ < 1 := fun x => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmem]
      simp
    · intro x y hxy
      rw [hmem] at hxy
      rw [hmem, hmem]
      by_contra h
      push_neg at h
      have : 1 ≤ ‖τ ((x * y : 𝓞 E) : E)‖ := by
        push_cast
        rw [map_mul, norm_mul]
        exact one_le_mul_of_one_le_of_one_le h.1 h.2
      linarith
  have hne : I ≠ ⊥ := by
    intro hbot
    have hl : ((l : 𝓞 E)) ∈ I := by
      rw [hmem]
      have h1 : ((l : 𝓞 E) : E) = (l : E) := by push_cast; rfl
      rw [h1, map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l,
        PadicAlgCl.norm_extends]
      exact Padic.norm_p_lt_one
    rw [hbot, Ideal.mem_bot] at hl
    have h2 : ((l : 𝓞 E) : E) = 0 := by rw [hl]; rfl
    have h3 : ((l : 𝓞 E) : E) = (l : E) := by push_cast; rfl
    rw [h3] at h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  exact ⟨τ, ⟨I, hprime, hne⟩, fun x => (hmem x).symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlaceStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicAlgCl_embedding_and_place_norm_lt_one : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], ∃ (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E)), ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal := by
  first | exact @GlobalTheory.exists_embedding_padicAlgCl_place | exact GlobalTheory.exists_embedding_padicAlgCl_place | (intros; apply GlobalTheory.exists_embedding_padicAlgCl_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemOfMemHeckeLevel
namespace GlobalTheory.HeckeCorr

variable {Gf : Type*} [Group Gf]

def heckeLevel (U : Subgroup Gf) (g : Gf) : Subgroup Gf := U ⊓ U.map (MulAut.conj g).toMonoidHom

theorem heckeLevel_le (U : Subgroup Gf) (g : Gf) : heckeLevel U g ≤ U := inf_le_left

theorem conj_mem_of_mem_heckeLevel {U : Subgroup Gf} {g u : Gf} (hu : u ∈ heckeLevel U g) : g⁻¹ * u * g ∈ U := by
  obtain ⟨-, v, hv, rfl⟩ := hu
  simpa [MulAut.conj_apply, mul_assoc] using hv

end GlobalTheory.HeckeCorr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueDegreeOneOfLinearMem
namespace GlobalTheory

theorem residue_degree_one_of_linear_mem : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime] (θ : B) (D a b : A), (P.comap (algebraMap A B)).IsMaximal → (∀ y : B, ∃ u v : A, algebraMap A B D * y = algebraMap A B u + algebraMap A B v * θ) → algebraMap A B D ∉ P → algebraMap A B b ∉ P → algebraMap A B a + algebraMap A B b * θ ∈ P → ∀ y : B, ∃ u : A, y - algebraMap A B u ∈ P := by
  intro A B _ _ _ P _ θ D a b hmax hgen hD hb hab y
  obtain ⟨b', i, hi, hbi⟩ := hmax.exists_inv (x := b) (by rwa [Ideal.mem_comap])
  obtain ⟨D', j, hj, hDj⟩ := hmax.exists_inv (x := D) (by rwa [Ideal.mem_comap])
  rw [Ideal.mem_comap] at hi hj
  obtain ⟨u, v, hy⟩ := hgen y
  have hbi' := congrArg (algebraMap A B) hbi
  have hDj' := congrArg (algebraMap A B) hDj
  simp only [map_add (f := _), map_mul, map_one] at hbi' hDj'
  refine ⟨D' * (u - v * a * b'), ?_⟩
  have key : y - algebraMap A B (D' * (u - v * a * b')) =
      algebraMap A B D' * algebraMap A B v * algebraMap A B b' * (algebraMap A B a + algebraMap A B b * θ)
      + (algebraMap A B D' * algebraMap A B v * θ) * algebraMap A B i + y * algebraMap A B j := by
    simp only [map_sub, map_mul]
    linear_combination algebraMap A B D' * hy - y * hDj' - algebraMap A B D' * algebraMap A B v * θ * hbi'
  rw [key]
  exact P.add_mem (P.add_mem (P.mul_mem_left _ hab) (P.mul_mem_left _ hi)) (P.mul_mem_left _ hj)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointEigenDecomposition
open Polynomial

namespace GlobalTheory.CommSemisimpleChars

open Classical in
theorem card_eq_of_sum_eq {H ι κ : Type} [Monoid H] [Fintype ι] [Fintype κ]
    (a : ι → (H →* ℂ)) (c : κ → (H →* ℂ)) (h : ∀ g, ∑ j, a j g = ∑ i, c i g) (ψ : H →* ℂ) :
    (Finset.univ.filter fun j => a j = ψ).card = (Finset.univ.filter fun i => c i = ψ).card := by
  classical
  let F : Finset (H →* ℂ) := insert ψ (Finset.univ.image a ∪ Finset.univ.image c)
  have li := linearIndependent_iff'.1 (linearIndependent_monoidHom H ℂ) F
    (fun φ => ((Finset.univ.filter fun j => a j = φ).card : ℂ) - (Finset.univ.filter fun i => c i = φ).card)
  have key : ∀ {τ : Type} [Fintype τ] (e : τ → (H →* ℂ)), (∀ t, e t ∈ F) →
      ∑ φ ∈ F, ((Finset.univ.filter fun t => e t = φ).card : ℂ) • (φ : H → ℂ) = ∑ t, (e t : H → ℂ) := by
    intro τ _ e he
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := F) (g := e) (fun t _ => he t)]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
  have hz : ∑ φ ∈ F, (((Finset.univ.filter fun j => a j = φ).card : ℂ) -
      (Finset.univ.filter fun i => c i = φ).card) • (φ : H → ℂ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [key a (fun j => by simp [F]), key c (fun i => by simp [F]), sub_eq_zero]
    funext g
    simp only [Finset.sum_apply]
    exact h g
  have := li hz ψ (Finset.mem_insert_self _ _)
  exact_mod_cast sub_eq_zero.1 this

end GlobalTheory.CommSemisimpleChars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldProdEmbeddingsRegroupMaximalReal
open NumberField

namespace GlobalTheory

theorem cm_eq_or_conj_of_comp_eq (E : Type) [Field E] [NumberField E] [IsCMField E]
    (τ τ' : E →+* ℂ)
    (h : τ'.comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E)) :
    τ' = τ ∨ τ' = ComplexEmbedding.conjugate τ := by
  have h1 : InfinitePlace.mk τ = InfinitePlace.mk τ' := by
    apply (IsCMField.equivInfinitePlace E).injective
    rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply,
      InfinitePlace.comap_mk, InfinitePlace.comap_mk, h]
  rcases InfinitePlace.mk_eq_iff.1 h1 with h2 | h2
  · exact Or.inl h2.symm
  · exact Or.inr h2.symm

theorem cm_conj_comp_eq (E : Type) [Field E] [NumberField E] (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ).comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E) := by
  have h := IsTotallyReal.complexEmbedding_isReal (τ.comp (algebraMap (maximalRealSubfield E) E))
  rw [ComplexEmbedding.isReal_iff] at h
  exact h

theorem cm_prod_regroup_maximalReal (E : Type) [Field E] [NumberField E] [IsCMField E]
    (k : (E →+* ℂ) → ℤ) (hk : ∀ τ, k (ComplexEmbedding.conjugate τ) = k τ) :
    ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, ∀ g : (maximalRealSubfield E →+* ℂ) → ℂ,
      ∏ τ : E →+* ℂ, g (τ.comp (algebraMap (maximalRealSubfield E) E)) ^ k τ =
        ∏ φ, g φ ^ (2 * n φ) := by
  classical
  refine ⟨fun φ => k (ComplexEmbedding.lift E φ), fun g => ?_⟩
  rw [← Finset.prod_fiberwise Finset.univ
    (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E))]
  refine Finset.prod_congr rfl fun φ _ => ?_
  set τ₀ := ComplexEmbedding.lift E φ with hτ₀
  have h0 : τ₀.comp (algebraMap (maximalRealSubfield E) E) = φ :=
    ComplexEmbedding.lift_comp_algebraMap E φ
  have h1 : (ComplexEmbedding.conjugate τ₀).comp (algebraMap (maximalRealSubfield E) E) = φ := by
    rw [cm_conj_comp_eq, h0]
  have hne : τ₀ ≠ ComplexEmbedding.conjugate τ₀ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ₀ (ComplexEmbedding.isReal_iff.2 h.symm)
  have hfib : Finset.univ.filter
      (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E) = φ) =
      {τ₀, ComplexEmbedding.conjugate τ₀} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      exact cm_eq_or_conj_of_comp_eq E τ₀ τ (h.trans h0.symm)
    · rintro (rfl | rfl)
      · exact h0
      · exact h1
  rw [hfib, Finset.prod_pair hne, h0, h1, hk, mul_comm (2 : ℤ), zpow_mul, zpow_two]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticRingOfIntegersMulMemSpanOneGen
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticRingOfIntegersMulMemSpanOneGen
open NumberField IsDedekindDomain

namespace GlobalTheory

private theorem exists_integral_generator_common_denom_of_finrank_two
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
    by_contra! hx
    have htop : (⊤ : IntermediateField F E) = ⊥ := by
      ext x
      simp only [IntermediateField.mem_top, true_iff]
      exact IntermediateField.mem_bot.mpr (hx x)
    have h1 := IntermediateField.finrank_eq_one_iff.mpr htop
    rw [IntermediateField.finrank_top'] at h1
    omega
  obtain ⟨n, hn, hnx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have hint : IsIntegral ℤ (n • x) := hnx x (Finset.mem_singleton_self x)
  obtain ⟨θ, hθx⟩ : ∃ θ : 𝓞 E, (θ : E) = (n : E) * x :=
    ⟨⟨n • x, hint⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hθ : (θ : E) ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    apply hx
    refine ⟨a / n, ?_⟩
    have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
    rw [map_div₀, map_intCast, ha, hθx]
    field_simp
  have hli : LinearIndependent F ![(1 : E), (θ : E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-s / t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).mpr ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hst
  obtain ⟨b, hb1⟩ : ∃ b : Module.Basis (Fin 2) F E, ⇑b = ![(1 : E), (θ : E)] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h, Fintype.card_fin]),
      coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
  have hb : ∀ z : E, z = algebraMap F E (b.repr z 0) + algebraMap F E (b.repr z 1) * θ := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    rw [Fin.sum_univ_two, hb1]
    simp [Algebra.smul_def]
  set B := RingOfIntegers.basis E
  obtain ⟨d, hd, hdint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin 2 =>
      b.repr (B p.1 : E) p.2)
  have hmem : ∀ i k, IsIntegral ℤ (d • b.repr (B i : E) k) := fun i k =>
    hdint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  refine ⟨θ, hθ, (d : 𝓞 F), by exact_mod_cast hd, ?_⟩
  let M : Submodule ℤ (𝓞 E) :=
    { carrier := {z | ∃ u v : 𝓞 F, z = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ}
      add_mem' := by
        rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
        exact ⟨u + u', v + v', by simp only [map_add (f := _)]; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro c _ ⟨u, v, rfl⟩
        exact ⟨c • u, c • v, by simp only [zsmul_eq_mul, map_mul, map_intCast]; ring⟩ }
  have hall : ∀ y : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) (d : 𝓞 F) * y ∈ M := by
    intro y
    have hspan : y ∈ Submodule.span ℤ (Set.range B) := by rw [B.span_eq]; trivial
    induction hspan using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine ⟨⟨_, hmem i 0⟩, ⟨_, hmem i 1⟩, ?_⟩
      rw [RingOfIntegers.ext_iff]
      have e := hb (B i : E)
      have key : algebraMap F E (d : F) * (B i : E) =
          algebraMap F E (d • b.repr (B i : E) 0) +
            algebraMap F E (d • b.repr (B i : E) 1) * θ := by
        simp only [zsmul_eq_mul, map_mul, map_intCast]
        linear_combination (d : E) * e
      exact key
    | zero => simpa using M.zero_mem
    | add z w _ _ hz hw => rw [mul_add]; exact M.add_mem hz hw
    | smul c z _ hz => rw [mul_smul_comm]; exact M.smul_mem c hz
  intro y
  obtain ⟨u, v, huv⟩ := hall y
  exact ⟨u, v, huv⟩

theorem _root_.GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∃ (θ : 𝓞 E) (D : 𝓞 F), D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  intro F E _ _ _ _ _ h
  obtain ⟨θ, -, D, hD, hy⟩ := exists_integral_generator_common_denom_of_finrank_two F E h
  exact ⟨θ, D, hD, hy⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticRingOfIntegersMulMemSpanOneGenStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denom_mul_mem_span_one_gen_of_finrank_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∃ (θ : 𝓞 E) (D : 𝓞 F), D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  first | exact @GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen | exact GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen | (intros; apply GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteInvolutionFixedUnitEqMulConj
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteInvolutionFixedUnitEqMulConj
namespace GlobalTheory

private lemma exists_pos_pow_mul_pow_eq_pow_of_finite {S : Type} [Monoid S] [Finite S] (a : S) :
    ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M := by
  have key : ∀ i j : ℕ, i < j → a ^ i = a ^ j → ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M := by
    intro i j hij h
    obtain ⟨p, rfl⟩ : ∃ p, j = i + (p + 1) := ⟨j - i - 1, by omega⟩
    have step : ∀ n, a ^ (i + n + (p + 1)) = a ^ (i + n) := by
      intro n
      rw [show i + n + (p + 1) = n + (i + (p + 1)) by ring, pow_add, ← h, ← pow_add,
        show n + i = i + n by ring]
    have rep : ∀ k n, a ^ (i + n + k * (p + 1)) = a ^ (i + n) := by
      intro k
      induction k with
      | zero => intro n; simp
      | succ k ih =>
        intro n
        rw [show i + n + (k + 1) * (p + 1) = i + (n + k * (p + 1)) + (p + 1) by ring, step,
          ← add_assoc, ih]
    refine ⟨(i + 1) * (p + 1), by positivity, ?_⟩
    rw [← pow_add]
    have hr := rep (i + 1) (i * p + p + 1)
    rwa [show i + (i * p + p + 1) + (i + 1) * (p + 1) = (i + 1) * (p + 1) + (i + 1) * (p + 1) by ring,
      show i + (i * p + p + 1) = (i + 1) * (p + 1) by ring] at hr
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt h
  · exact key j i hlt h.symm

theorem finite_involution_hilbert90 {S : Type} [CommRing S] [Finite S] (c : S →+* S)
    (hc : ∀ x, c (c x) = x) (ω : S) (hω : IsUnit (ω - c ω)) (y : S) (hy : y * c y = 1) :
    ∃ x : S, IsUnit x ∧ x = y * c x := by
  have hyu : IsUnit y := ⟨⟨y, c y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  obtain ⟨M, hM0, hM⟩ := exists_pos_pow_mul_pow_eq_pow_of_finite ((1 + y) * c (1 + y))
  obtain ⟨e, he⟩ : ∃ e, e = ((1 + y) * c (1 + y)) ^ M := ⟨_, rfl⟩
  rw [← he] at hM
  have hce : c e = e := by
    rw [he, map_pow, map_mul, hc, mul_comm]
  have h1 : y * c (1 + y) = 1 + y := by
    rw [map_add (f := _), map_one]; linear_combination hy
  refine ⟨e * (1 + y) + (1 - e) * (ω + y * c ω), ?_, ?_⟩
  · by_contra hx
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
    have hp := hm.isPrime
    have hnot : y * (ω - c ω) ∉ m := fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem m h (hyu.mul hω))
    have hid : ω * (1 + y) - (ω + y * c ω) = y * (ω - c ω) := by ring
    have hex : e ∈ m → 1 + y ∈ m := by
      intro h
      rw [he] at h
      rcases hp.mem_or_mem (hp.mem_of_pow_mem M h) with h' | h'
      · exact h'
      · rw [← h1]; exact m.mul_mem_left y h'
    by_cases hem : e ∈ m
    · have hx1 : 1 + y ∈ m := hex hem
      have h2 : (1 - e) * (ω + y * c ω) ∈ m := by
        have hr : (1 - e) * (ω + y * c ω)
            = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - e * (1 + y) := by ring
        rw [hr]; exact m.sub_mem hxm (m.mul_mem_right _ hem)
      have h1e : 1 - e ∉ m := by
        intro h
        apply hm.ne_top
        rw [Ideal.eq_top_iff_one]
        have hs := m.add_mem hem h
        rwa [add_sub_cancel] at hs
      have hxω : ω + y * c ω ∈ m := (hp.mem_or_mem h2).resolve_left h1e
      apply hnot
      rw [← hid]
      exact m.sub_mem (m.mul_mem_left ω hx1) hxω
    · have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hM, sub_self]
      have h1e : 1 - e ∈ m := by
        refine (hp.mem_or_mem ?_).resolve_left hem
        rw [hee]; exact m.zero_mem
      have h2 : e * (1 + y) ∈ m := by
        have hr : e * (1 + y)
            = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - (1 - e) * (ω + y * c ω) := by ring
        rw [hr]; exact m.sub_mem hxm (m.mul_mem_right _ h1e)
      have hx1 : 1 + y ∈ m := (hp.mem_or_mem h2).resolve_left hem
      apply hem
      rw [he]
      exact Ideal.pow_mem_of_mem m (m.mul_mem_right _ hx1) M hM0
  · simp only [map_add (f := _), map_mul, map_sub, map_one, hc, hce]
    linear_combination (-(e + (1 - e) * ω)) * hy

theorem finite_involution_fixed_unit_isNorm :
    ∀ (S : Type) [CommRing S] [Finite S] (c : S →+* S), (∀ x, c (c x) = x) →
      (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  intro S _ _ c hc hω u hcu hu
  obtain ⟨ω, hω⟩ := hω
  let cu : Sˣ →* Sˣ := Units.map (c : S →* S)
  have hcuv : ∀ x : Sˣ, ((cu x : Sˣ) : S) = c x := fun x => rfl
  have hcc : ∀ x : Sˣ, cu (cu x) = x := fun x => Units.ext (by rw [hcuv, hcuv, hc])
  let N : Sˣ →* Sˣ := MonoidHom.id Sˣ * cu
  let ψ : Sˣ →* Sˣ := MonoidHom.id Sˣ / cu
  have hN : ∀ x, N x = x * cu x := fun x => rfl
  have hψ : ∀ x, ψ x = x / cu x := fun x => MonoidHom.div_apply _ _ x
  have hker : N.ker ≤ ψ.range := by
    intro y hy
    rw [MonoidHom.mem_ker, hN] at hy
    have hy' : (y : S) * c y = 1 := by
      have := congrArg Units.val hy
      rwa [Units.val_mul, hcuv, Units.val_one] at this
    obtain ⟨x, hxu, hx⟩ := finite_involution_hilbert90 c hc ω hω y hy'
    refine ⟨hxu.unit, ?_⟩
    rw [hψ, div_eq_iff_eq_mul]
    exact Units.ext (by rw [Units.val_mul, hcuv, IsUnit.unit_spec]; exact hx)
  have hrange : N.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, hψ, div_eq_one, hN, map_mul, hcc, mul_comm]
  have hcard : Nat.card ψ.ker ≤ Nat.card N.range := by
    have e1 := N.ker.card_mul_index
    have e2 := ψ.ker.card_mul_index
    rw [Subgroup.index_ker] at e1 e2
    have hle : Nat.card N.ker ≤ Nat.card ψ.range := Subgroup.card_le_of_le hker
    have hpos : 0 < Nat.card ψ.range := Nat.card_pos
    have h3 : Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card N.range * Nat.card ψ.range := by
      rw [e2, ← e1, mul_comm (Nat.card N.range)]
      exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have heq : N.range = ψ.ker := Subgroup.eq_of_le_of_card_ge hrange hcard
  have hmem : hu.unit ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hψ, div_eq_one]
    exact Units.ext (by rw [hcuv, IsUnit.unit_spec, hcu])
  rw [← heq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  have := congrArg Units.val hx
  rwa [hN, Units.val_mul, hcuv, IsUnit.unit_spec] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteInvolutionFixedUnitEqMulConjStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_involution_fixed_unit_eq_mul_conj : ∀ (S : Type) [CommRing S] [Finite S] (c : S →+* S), (∀ x, c (c x) = x) → (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  first | exact @GlobalTheory.finite_involution_fixed_unit_isNorm | exact GlobalTheory.finite_involution_fixed_unit_isNorm | (intros; apply GlobalTheory.finite_involution_fixed_unit_isNorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ProdFinEqProdCastLE
namespace GlobalTheory.ProdFinCastLE

theorem prod_fin_eq_prod_castLE {a b : ℕ} {M : Type} [CommMonoid M] (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ r : Fin b, a ≤ (r : ℕ) → f r = 1) :
    ∏ r : Fin b, f r = ∏ r : Fin a, f (Fin.castLE h r) := by
  symm
  rw [show (∏ r : Fin a, f (Fin.castLE h r)) =
      ∏ x ∈ Finset.univ.map ⟨Fin.castLE h, Fin.castLE_injective h⟩, f x by
    rw [Finset.prod_map]
    rfl]
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => hf x ?_
  by_contra hlt
  push Not at hlt
  exact hx (Finset.mem_map.2 ⟨⟨x, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

end GlobalTheory.ProdFinCastLE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgClosedResidueField
open Polynomial

namespace GlobalTheory.AlgClosedResidueField

theorem isAlgClosed_residueField {K : Type} [Field K] (O : ValuationSubring K) [IsAlgClosed K] :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue O) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue O) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨q, hqp, hdeg, hq⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hd : (q.map (algebraMap O K)).degree ≠ 0 := by
    rw [hq.degree_map, hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hx' : q.eval₂ (algebraMap O K) x = 0 := by
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hx
  have hint : IsIntegral O x := ⟨q, hq, hx'⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hy : q.eval y = 0 := by
    rw [Polynomial.eval₂_at_apply] at hx'
    exact (IsFractionRing.injective O K) (by rw [hx', map_zero])
  refine ⟨IsLocalRing.residue O y, ?_⟩
  rw [← hqp, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

end GlobalTheory.AlgClosedResidueField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsFurther
namespace GlobalTheory.NatMulIsIntegralSatakeParameters

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * a) := by
  obtain ⟨y, hy0, hy'⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have hy := hy' a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  rw [zsmul_eq_mul] at hy
  rcases Int.natAbs_eq y with h | h
  · rw [h] at hy
    simpa using hy
  · rw [h] at hy
    simpa using hy.neg

theorem exists_nsmul_mem {E : Type} [Field E] [NumberField E] {N : ℕ}
    (Lb : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) {v : Fin N → E}
    (hv : v ∈ Submodule.span E (↑Lb : Set (Fin N → E))) :
    ∃ n : ℕ, 0 < n ∧ n • v ∈ Lb := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, h₁⟩ := hx
    obtain ⟨n₂, hn₂, h₂⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, ?_⟩
    have e : (n₁ * n₂) • (x + y) = n₂ • (n₁ • x) + n₁ • (n₂ • y) := by
      ext i
      show (n₁ * n₂) • (x i + y i) = n₂ • (n₁ • x i) + n₁ • (n₂ • y i)
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [e]
    exact Lb.add_mem (nsmul_mem h₁ n₂) (nsmul_mem h₂ n₁)
  | smul c x _ hx =>
    obtain ⟨n, hn, h⟩ := hx
    obtain ⟨m, hm, hc⟩ := exists_nat_mul_isIntegral c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have e : (m * n) • (c • x) =
        (⟨(m : E) * c, (mem_integralClosure_iff ℤ E).mpr hc⟩ : NumberField.RingOfIntegers E) • (n • x) := by
      ext i
      show (m * n) • (c * x i) = ((m : E) * c) * (n • x i)
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [e]
    exact Lb.smul_mem _ h

end GlobalTheory.NatMulIsIntegralSatakeParameters
end
