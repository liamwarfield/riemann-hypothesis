module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefficientCongruenceOfTwistedValues
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesEqZeroOfValsTendstoZero
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

namespace GlobalTheory

theorem KZ.norm_prime_lt_one_qbar (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem KZ.eq_zero_of_cg_all (l : ℕ) [Fact l.Prime] (x : Qbar l) (h : ∀ k : ℕ, Cg k x 0) :
    x = 0 := by
  have hlt := KZ.norm_prime_lt_one_qbar l
  have hn : 0 ≤ ‖((l : ℕ) : Qbar l)‖ := norm_nonneg _
  have ht : Filter.Tendsto (fun k : ℕ => ‖((l : ℕ) : Qbar l)‖ ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hn hlt
  have hle : ∀ k : ℕ, ‖x‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ k := by
    intro k
    have := h k
    unfold Cg at this
    simpa [norm_pow] using this
  have h0 : ‖x‖ ≤ 0 := ge_of_tendsto' ht hle
  exact norm_le_zero_iff.mp h0

theorem KZ.series_eq_zero_of_vals_tendsto_zero : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)), (∀ n, F.coeff n ∈ c.O) → (∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) → F = 0 := by
  intro l _ c F hO hv
  ext n
  rw [map_zero]
  apply KZ.eq_zero_of_cg_all l
  intro k
  obtain ⟨m₁, hm⟩ := hv k
  exact GlobalTheory.T.coefficient_congruence_of_twisted_values l c F k m₁ hO hm n

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HtPresNu7MonoLoss
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ

theorem htPresNu7_mono_loss : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
  (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₂ c' : ℕ) (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l),
  HTPresNuOfPolys A c m c₂ Z ζ P o → c₂ ≤ c' → HTPresNuOfPolys A c m c' Z ζ P o := by
  intro l _ Ω _ _ _ A c Z m c₂ c' ζ ι _ P o h hc
  obtain ⟨hζ, hco, hoO, hne, hK⟩ := h
  obtain ⟨hζ₂, -, hu, ho, hs⟩ := hK
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    have : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hl.pos i).ne'⟩
    infer_instance
  set n' := m - c' with hn'
  set d := (m - c₂) - n' with hd
  have hdn : d + n' = m - c₂ := by omega
  have hpow : (ζ ^ l ^ c₂) ^ l ^ d = ζ ^ l ^ c' := by
    rw [← pow_mul, ← pow_add]
    rcases Nat.lt_or_ge m c' with h | h
    swap
    · congr 2; omega
    · have e1 : m ≤ c₂ + d := by omega
      rw [(hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l e1), (hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l h.le)]
  have hζ' : IsPrimitiveRoot (ζ ^ l ^ c') (l ^ n') := by
    rw [← hpow]
    exact hζ₂.pow (pow_pos hl.pos _) (by rw [← pow_add, hdn])
  refine ⟨hζ, hco, hoO, hne, hζ', by omega, hu, ho, ?_⟩
  intro s hsI hcyc _
  have hfix : s (ζ ^ l ^ c₂) = ζ ^ l ^ c₂ := by
    refine GlobalTheory.Col.fix_of_cycMod (le_refl m) hcyc ?_
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨k, hkv, hcg⟩ := hs s hsI hcyc hfix
  refine ⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩
  · obtain ⟨v, hv, hsv⟩ := hkv i
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, hdn, hv], ?_⟩
    rw [ZMod.val_natCast, map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, hpow,
      ← pow_eq_pow_mod _ hζ'.pow_eq_one]
  · have hN : ∀ a : ℕ, ‖(a : Qbar l)‖ ≤ 1 := fun a => IsUltrametricDist.norm_natCast_le_one _ a
    have key : ∀ i, ‖o i * ((k i).val : Qbar l) -
        o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      intro i
      have e : (((k i).val : ℕ) : Qbar l) =
          ((l : ℕ) : Qbar l) ^ n' * (((k i).val / l ^ n' : ℕ) : Qbar l) + (((k i).val % l ^ n' : ℕ) : Qbar l) := by
        exact_mod_cast (Nat.div_add_mod (k i).val (l ^ n')).symm
      have e2 : o i * ((k i).val : Qbar l) - o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l) =
          ((l : ℕ) : Qbar l) ^ n' * (o i * (((k i).val / l ^ n' : ℕ) : Qbar l)) := by
        rw [ZMod.val_natCast]
        linear_combination (o i) * e
      rw [e2, norm_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (ho i) (norm_nonneg _) (hN _))
    have h1 : ‖Z m s 1 - ∑ i, o i * ((k i).val : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      refine le_trans hcg ?_
      rw [norm_pow, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (hN l) (by omega)
    have h2 : ‖∑ i, (o i * ((k i).val : Qbar l) -
        o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => key i)
    have h3 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
    rw [Finset.sum_sub_distrib, sub_add_sub_cancel] at h3
    exact h3

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInPrimitiveRootOfInertiaFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInertiaFixedEvalEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInertiaFixedEvalEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory

theorem exists_polynomial_closedSubgroup_fixed_eval_eq {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] [IsGalois F Ω] (H : ClosedSubgroup (Ω ≃ₐ[F] Ω)) (ζ u : Ω)
    (h : ∀ s ∈ H.toSubgroup, s ζ = ζ → s u = u) :
    ∃ P : Polynomial Ω, (∀ s ∈ H.toSubgroup, ∀ d, s (P.coeff d) = P.coeff d) ∧
      P.eval ζ = u := by
  classical
  let T : IntermediateField F Ω := IntermediateField.fixedField H.toSubgroup
  have hT : T.fixingSubgroup = H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
  let E : IntermediateField F Ω :=
    (IntermediateField.adjoin T ({ζ} : Set Ω)).restrictScalars F
  have hu : u ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro s hs
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs
    refine h s ?_ (hs ζ (IntermediateField.mem_adjoin_simple_self T ζ))
    have : s ∈ T.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hs x ((IntermediateField.adjoin T ({ζ} : Set Ω)).algebraMap_mem ⟨x, hx⟩)
    rw [hT] at this
    exact this
  have hint : IsIntegral T ζ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := F) ζ).isIntegral.tower_top
  have hu' : u ∈ (IntermediateField.adjoin T ({ζ} : Set Ω)).toSubalgebra := hu
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hu'
  obtain ⟨Q, hQ⟩ := hu'
  refine ⟨Q.map (algebraMap T Ω), ?_, ?_⟩
  · intro s hs d
    rw [Polynomial.coeff_map]
    exact (IntermediateField.mem_fixedField_iff H.toSubgroup _).1 (Q.coeff d).2 s hs
  · rw [Polynomial.eval_map_algebraMap]
    exact hQ

theorem exists_polynomial_inertia_fixed_eval_eq (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (ζ u : Ω)
    (h : ∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) :
    ∃ P : Polynomial Ω, (∀ s ∈ Ine (F := ℚ) A, ∀ d, s (P.coeff d) = P.coeff d) ∧
      P.eval ζ = u :=
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  exists_polynomial_closedSubgroup_fixed_eval_eq
    ⟨Ine (F := ℚ) A, isClosed_Ine (F := ℚ) A⟩ ζ u h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInertiaFixedEvalEqStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_eval_eq_of_inertia_fixed : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (ζ u : Ω), (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ P : Polynomial Ω, (∀ s ∈ Ine (F := ℚ) A, ∀ d, s (P.coeff d) = P.coeff d) ∧ P.eval ζ = u := by
  first | exact @GlobalTheory.exists_polynomial_inertia_fixed_eval_eq | exact GlobalTheory.exists_polynomial_inertia_fixed_eval_eq | (intros; apply GlobalTheory.exists_polynomial_inertia_fixed_eval_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfSumMulPowMemOfValuationZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfSumMulPowMemOfValuationZpow
namespace GlobalTheory

theorem mem_of_sum_mul_pow_mem_of_valuation_zpow (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    (N : ℕ) (π ℓ : Ω) (c : ℕ → Ω) (hN : 0 < N) (hℓ : ℓ ≠ 0)
    (hℓ1 : A.valuation ℓ < 1) (hπ : A.valuation π ^ N = A.valuation ℓ)
    (hc : ∀ i < N, c i ≠ 0 → ∃ k : ℤ, A.valuation (c i) = A.valuation ℓ ^ k)
    (hsum : (∑ i ∈ Finset.range N, c i * π ^ i) ∈ A) : ∀ i < N, c i ∈ A := by
  classical
  set v := A.valuation with hv
  set b := v ℓ with hb
  have hb0 : 0 < b := lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff v).2 hℓ))
  set t : ℕ → A.ValueGroup := fun i => v (c i * π ^ i) with ht

  have hpow : ∀ i (k : ℤ), v (c i) = b ^ k → t i ^ N = b ^ ((N : ℤ) * k + i) := by
    intro i k hk
    simp only [ht, map_mul, map_pow, hk]
    rw [mul_pow, ← pow_mul, mul_comm i N, pow_mul, hπ, zpow_add₀ hb0.ne', mul_comm (N : ℤ) k,
      zpow_mul, zpow_natCast, zpow_natCast]

  have hdist : ∀ i < N, ∀ j < N, c i ≠ 0 → c j ≠ 0 → t i = t j → i = j := by
    intro i hi j hj hci hcj hij
    obtain ⟨k, hk⟩ := hc i hi hci
    obtain ⟨l, hl⟩ := hc j hj hcj
    have e : b ^ ((N : ℤ) * k + i) = b ^ ((N : ℤ) * l + j) := by
      rw [← hpow i k hk, ← hpow j l hl, hij]
    have e2 := (zpow_right_strictAnti₀ hb0 hℓ1).injective e
    have h1 : ((N : ℤ) * k + i) % N = (i : ℤ) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have h2 : ((N : ℤ) * l + j) % N = (j : ℤ) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have : (i : ℤ) = j := by rw [← h1, ← h2, e2]
    exact_mod_cast this

  have hle : ∀ i ∈ Finset.range N, t i ≤ 1 := by
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range N) t ⟨0, Finset.mem_range.2 hN⟩
    suffices t j ≤ 1 from fun i hi => (hmax i hi).trans this
    by_cases htj : t j = 0
    · rw [htj]; exact zero_le'
    have hcj : c j ≠ 0 := by
      intro h; apply htj; simp [ht, h]
    have hlt : ∀ i ∈ Finset.range N \ {j}, v (c i * π ^ i) < v (c j * π ^ j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      refine lt_of_le_of_ne (hmax i hi.1) ?_
      intro heq
      by_cases hci : c i = 0
      · apply htj; show v (c j * π ^ j) = 0; rw [← heq]; simp [hci]
      · exact hi.2 (hdist i (Finset.mem_range.1 hi.1) j (Finset.mem_range.1 hj) hci hcj heq)
    have := Valuation.map_sum_eq_of_lt v hj hlt
    rw [← (A.valuation_le_one_iff _)] at hsum
    show v (c j * π ^ j) ≤ 1
    rw [← this]; exact hsum
  intro i hi
  by_cases hci : c i = 0
  · rw [hci]; exact A.zero_mem
  obtain ⟨k, hk⟩ := hc i hi hci
  have h1 : t i ^ N ≤ 1 := pow_le_one₀ zero_le' (hle i (Finset.mem_range.2 hi))
  rw [hpow i k hk, zpow_le_one_iff_right_of_lt_one₀ hb0 hℓ1] at h1
  have hk0 : 0 ≤ k := by
    by_contra hneg
    push_neg at hneg
    have : (N : ℤ) * k ≤ -(N : ℤ) := by nlinarith
    omega
  rw [← A.valuation_le_one_iff, hk]
  exact zpow_le_one₀ hb0 hℓ1.le hk0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfSumMulPowMemOfValuationZpowStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_of_sum_mul_pow_mem_of_valuation_zpow : ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (N : ℕ) (π ℓ : Ω) (c : ℕ → Ω), 0 < N → ℓ ≠ 0 → A.valuation ℓ < 1 → A.valuation π ^ N = A.valuation ℓ → (∀ i < N, c i ≠ 0 → ∃ k : ℤ, A.valuation (c i) = A.valuation ℓ ^ k) → (∑ i ∈ Finset.range N, c i * π ^ i) ∈ A → ∀ i < N, c i ∈ A := by
  first | exact @GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow | exact GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow | (intros; apply GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInPrimitiveRootOfInertiaFixed
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

theorem GlobalTheory.ZetaPoly.exists_poly : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ n) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ Q : Polynomial Ω, (∀ d, Q.coeff d ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s (Q.coeff d) = Q.coeff d) ∧ Q.eval ζ = u := by
  intro l _ Ω _ _ _ A hA n ζ hζ u hu hfix
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hζ1 : ζ = 1 := by simpa using hζ
    subst hζ1
    refine ⟨Polynomial.C u, fun d => ?_, by simp⟩
    rw [Polynomial.coeff_C]
    split_ifs
    · exact ⟨hu, fun s hs => hfix s hs (map_one s)⟩
    · exact ⟨A.zero_mem, fun s _ => map_zero s⟩
  obtain ⟨P, hPfix, hPev⟩ := GlobalTheory.T.exists_polynomial_eval_eq_of_inertia_fixed Ω A ζ u hfix
  set N := (l ^ n).totient with hN
  have hlpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hNpos : 0 < N := Nat.totient_pos.2 hlpos
  set Φ := Polynomial.cyclotomic (l ^ n) Ω with hΦ
  have hΦm : Φ.Monic := Polynomial.cyclotomic.monic _ _
  have hΦdeg : Φ.natDegree = N := Polynomial.natDegree_cyclotomic _ _
  have hΦ1 : Φ ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hΦdeg; omega
  set P' := P %ₘ Φ with hP'
  have hroot : Φ.eval ζ = 0 := (hζ.isRoot_cyclotomic hlpos)
  have hev : P'.eval ζ = u := by
    rw [← hPev]
    show (P %ₘ Φ).eval ζ = P.eval ζ
    conv_rhs => rw [← Polynomial.modByMonic_add_div P Φ]
    rw [Polynomial.eval_add, Polynomial.eval_mul, hroot, zero_mul, add_zero]
  have hdeg : P'.natDegree < N := hΦdeg ▸ Polynomial.natDegree_modByMonic_lt P hΦm hΦ1
  have hPmap : ∀ s ∈ Ine (F := ℚ) A, P.map (s : Ω →+* Ω) = P := fun s hs =>
    Polynomial.ext fun d => by rw [Polynomial.coeff_map]; exact hPfix s hs d
  have hP'map : ∀ s ∈ Ine (F := ℚ) A, P'.map (s : Ω →+* Ω) = P' := fun s hs => by
    rw [hP', Polynomial.map_modByMonic _ hΦm, hPmap s hs, hΦ, Polynomial.map_cyclotomic]
  set T := Polynomial.taylor (1 : Ω) P' with hT
  have hTmap : ∀ s ∈ Ine (F := ℚ) A, T.map (s : Ω →+* Ω) = T := fun s hs => by
    rw [hT, Polynomial.map_taylor, hP'map s hs, map_one]
  have hTdeg : T.natDegree < N := by rw [hT, Polynomial.natDegree_taylor]; exact hdeg
  have hsum : (∑ i ∈ Finset.range N, T.coeff i * (ζ - 1) ^ i) = u := by
    rw [← Polynomial.eval_eq_sum_range' hTdeg, hT, Polynomial.taylor_eval, sub_add_cancel, hev]
  obtain ⟨v, hv, hlv⟩ := hA
  have hl1 : A.valuation (l : Ω) < 1 := by
    have := (hv ((l : ℕ) : 𝓞 ℚ)).2 hlv
    simpa using this
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hcA : ∀ i < N, T.coeff i ∈ A := by
    refine GlobalTheory.T.coeff_mem_of_sum_mul_pow_mem_of_valuation_zpow Ω A N (ζ - 1) (l : Ω) (fun i => T.coeff i) hNpos hl0 hl1
      (GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_ratAlg l Ω A n ζ hn hζ) (fun i _ hc => ?_) (hsum ▸ hu)
    refine GlobalTheory.T.inertiaFixed_valuation_eq_zpow_prime_ratAlgClosure l Ω A ⟨v, hv, hlv⟩ _ hc (fun s hs => ?_)
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) (hTmap s hs)
    simpa [Polynomial.coeff_map] using this
  have hcA' : ∀ i, T.coeff i ∈ A := fun i => by
    rcases lt_or_ge i N with h | h
    · exact hcA i h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact A.zero_mem
  have hlift : T ∈ Polynomial.lifts (A.subtype) :=
    (Polynomial.lifts_iff_coeff_lifts T).2 fun i => ⟨⟨_, hcA' i⟩, rfl⟩
  obtain ⟨T₀, hT₀⟩ := Polynomial.mem_lifts T |>.1 hlift
  have hback : Polynomial.taylor (-1 : Ω) T = P' := by
    rw [hT, Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
  refine ⟨P', fun d => ⟨?_, fun s hs => ?_⟩, hev⟩
  · rw [← hback, ← hT₀]
    have : ((-1 : A) : Ω) = -1 := by simp
    rw [← this, show ((-1 : A) : Ω) = A.subtype (-1) from rfl, ← Polynomial.map_taylor, Polynomial.coeff_map]
    exact (Polynomial.taylor (-1 : A) T₀).coeff d |>.2
  · have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p d) (hP'map s hs)
    simpa [Polynomial.coeff_map] using this

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInPrimitiveRootOfInertiaFixedStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ n) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ Q : Polynomial Ω, (∀ d, Q.coeff d ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s (Q.coeff d) = Q.coeff d) ∧ Q.eval ζ = u := by
  first | exact @GlobalTheory.ZetaPoly.exists_poly | exact GlobalTheory.ZetaPoly.exists_poly | (intros; apply GlobalTheory.ZetaPoly.exists_poly; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormGaussSumModPrimePowerLeHalfPower
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormGaussSumModPrimePowerLeHalfPower
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

theorem norm_gSum_le : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)),
    z ^ (l ^ m) = 1 → ‖gSum m z ψ‖ ≤ ‖(l : Qbar l) ^ (m / 2)‖ := by
  intro l _ m z ψ hz
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨k, hk⟩ : ∃ k, k = m / 2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = m - k := ⟨_, rfl⟩
  rw [← hk]
  have hsm : s ≤ m := by omega
  have hmss : m ≤ s + s := by omega
  have hmsk : m = s + k := by omega
  haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let π : ZMod (l ^ m) →+* ZMod (l ^ s) := ZMod.castHom (pow_dvd_pow l hsm) (ZMod (l ^ s))
  have hsurj : Function.Surjective π := ZMod.castHom_surjective (pow_dvd_pow l hsm)
  let q : ZMod (l ^ m) := ((l ^ s : ℕ) : ZMod (l ^ m))
  have hqq : q * q = 0 := by
    simp only [q, ← Nat.cast_mul, ← pow_add, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow l hmss
  have hπq : π q = 0 := by
    simp only [q]
    rw [map_natCast, ZMod.natCast_self]
  have hfib : ∀ x x0 : ZMod (l ^ m), π x = π x0 → ∃ y, x = x0 + q * y := by
    intro x x0 h
    have h0 : π (x - x0) = 0 := by rw [map_sub, h, sub_self]
    have hd : ((x - x0).val : ZMod (l ^ m)) = x - x0 := ZMod.natCast_zmod_val _
    rw [← hd, map_natCast, ZMod.natCast_eq_zero_iff] at h0
    obtain ⟨j, hj⟩ := h0
    refine ⟨(j : ZMod (l ^ m)), ?_⟩
    rw [← sub_eq_iff_eq_add', ← hd, hj, Nat.cast_mul]
  let e : ZMod (l ^ m) → Qbar l := fun x => z ^ x.val
  have he : ∀ a b, e (a + b) = e a * e b := by
    intro a b
    simp only [e, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hz).symm
  let g : ZMod (l ^ m) → Qbar l := fun x => ψ x * e x
  have hzn : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).1 h1
  have hg1 : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    simp only [g, e, norm_mul, norm_pow, hzn, one_pow, mul_one]
    exact DirichletCharacter.norm_le_one ψ x
  have hsum : gSum m z ψ = ∑ x, g x := by
    unfold gSum
    symm
    rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun x _ hx => by
      by_contra h; exact hx (by simp [g, MulChar.map_nonunit ψ h]))]
    refine Finset.sum_bij' (fun x hx => (Finset.mem_filter.1 hx).2.unit) (fun b _ => (b : ZMod (l ^ m)))
      ?_ ?_ ?_ ?_ ?_ <;> simp [g, e]
  have hmove : ∀ x x0 y : ZMod (l ^ m), π x = π x0 → x * q * y = x0 * q * y := by
    intro x x0 y h
    obtain ⟨y', rfl⟩ := hfib x x0 h
    linear_combination (y' * y) * hqq
  have h1 : ∀ y : ZMod (l ^ m), (1 - q * y) * (1 + q * y) = 1 := fun y => by
    linear_combination (-(y * y)) * hqq
  have hinv : ∀ x0 y : ZMod (l ^ m), ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x =
      ψ (1 + q * y) * e (x0 * q * y) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x := by
    intro x0 y
    rw [Finset.mul_sum]
    calc ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x
        = ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g (x * (1 + q * y)) := by
          refine Finset.sum_nbij' (fun x => x * (1 - q * y)) (fun x => x * (1 + q * y)) ?_ ?_ ?_ ?_ ?_
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_sub, map_one, hπq,
              zero_mul, sub_zero, mul_one] at ha ⊢
            exact ha
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_add (f := _), map_one, hπq,
              zero_mul, add_zero, mul_one] at ha ⊢
            exact ha
          · intro a _
            simp only [mul_assoc, h1, mul_one]
          · intro a _
            simp only [mul_assoc, mul_comm (1 + q * y), h1, mul_one]
          · intro a _
            simp only [mul_assoc, h1, mul_one]
      _ = _ := Finset.sum_congr rfl fun x hx => by
          have hx' : π x = π x0 := (Finset.mem_filter.1 hx).2
          show ψ (x * (1 + q * y)) * e (x * (1 + q * y)) = ψ (1 + q * y) * e (x0 * q * y) * (ψ x * e x)
          rw [map_mul, show x * (1 + q * y) = x + x * q * y by ring, he, hmove x x0 y hx']
          ring
  have H : ∀ u w y' : ZMod (l ^ m), IsUnit u → w = u + q * y' →
      (∀ y, ψ (1 + q * y) * e (u * q * y) = 1) → g w = g u := by
    intro u w y' hu hw hχu
    obtain ⟨U, rfl⟩ := hu
    have hUU : (U : ZMod (l ^ m)) * ((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = 1 := Units.mul_inv U
    have hw' : w = (U : ZMod (l ^ m)) + U * q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y') := by
      rw [hw]; linear_combination (-(q * y')) * hUU
    have hw'' : w = (U : ZMod (l ^ m)) * (1 + q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')) := by
      rw [hw']; ring
    have := hχu (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')
    show ψ w * e w = ψ U * e U
    rw [hw'', map_mul, ← hw'', hw', he]
    linear_combination (ψ U * e U) * this
  have hcard0 : ∀ x0, (Finset.univ.filter (fun x => π x = π x0)).card =
      (Finset.univ.filter (fun x => π x = 0)).card := by
    intro x0
    refine Finset.card_nbij' (fun x => x - x0) (fun x => x + x0) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      rw [map_sub, ha, sub_self]
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      rw [map_add (f := _), ha, zero_add]
    · intro a _; simp
    · intro a _; simp
  have htot : l ^ m = l ^ s * (Finset.univ.filter (fun x => π x = 0)).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := π)
      (fun x _ => Finset.mem_univ _)
    rw [Finset.card_univ, ZMod.card] at this
    refine this.trans ?_
    rw [Finset.sum_congr rfl (g := fun _ => (Finset.univ.filter (fun x => π x = 0)).card) (fun c _ => by
      obtain ⟨x0, rfl⟩ := hsurj c
      exact hcard0 x0), Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  have hcardk : (Finset.univ.filter (fun x => π x = 0)).card = l ^ k := by
    have h2 : l ^ s * (Finset.univ.filter (fun x => π x = 0)).card = l ^ s * l ^ k := by
      rw [← htot, ← pow_add, ← hmsk]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos s) h2
  rw [hsum, ← Finset.sum_fiberwise Finset.univ π g]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun c _ => ?_
  obtain ⟨x0, rfl⟩ := hsurj c
  by_cases hχ : ∀ y, ψ (1 + q * y) * e (x0 * q * y) = 1
  · have hall : ∀ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = g x0 := by
      intro x hx
      have hx' : π x = π x0 := (Finset.mem_filter.1 hx).2
      obtain ⟨y', hy'⟩ := hfib x x0 hx'
      by_cases hu0 : IsUnit x0
      · exact H x0 x y' hu0 hy' hχ
      by_cases hu : IsUnit x
      · refine (H x x0 (-y') hu (by rw [hy']; ring) fun y => ?_).symm
        rw [hmove x x0 y hx']
        exact hχ y
      · show ψ x * e x = ψ x0 * e x0
        rw [MulChar.map_nonunit ψ hu, MulChar.map_nonunit ψ hu0, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, norm_mul, hcard0, hcardk]
    push_cast
    calc ‖(l : Qbar l) ^ k‖ * ‖g x0‖ ≤ ‖(l : Qbar l) ^ k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hg1 x0) (norm_nonneg _)
      _ = _ := mul_one _
  · push_neg at hχ
    obtain ⟨y, hy⟩ := hχ
    have hI := hinv x0 y
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0 := by
      have hm : (1 - ψ (1 + q * y) * e (x0 * q * y)) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0 := by
        rw [sub_mul, one_mul, ← hI, sub_self]
      exact (mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 (Ne.symm hy))
    rw [h0, norm_zero]
    positivity

end GlobalTheory.KZ.Cmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormGaussSumModPrimePowerLeHalfPowerStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_gaussSumModPrimePower_le_half_power : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), z ^ (l ^ m) = 1 → ‖gSum m z ψ‖ ≤ ‖(l : Qbar l) ^ (m / 2)‖ := by
  first | (exact @GlobalTheory.KZ.Cmp.norm_gSum_le) | (exact GlobalTheory.KZ.Cmp.norm_gSum_le) | (intros; apply GlobalTheory.KZ.Cmp.norm_gSum_le  <;> assumption)
end
end
