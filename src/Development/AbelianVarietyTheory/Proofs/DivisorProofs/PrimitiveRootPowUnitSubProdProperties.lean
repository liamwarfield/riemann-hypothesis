module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

def μc (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

lemma μc_prim (q : ℕ) [NeZero q] : IsPrimitiveRoot (μc q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

lemma aeval_cyc {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    aeval x (cyclotomic n ℤ) = eval x (cyclotomic n R) := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]

lemma transfer {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (P : ℤ[X])
    (hP : aeval (μc q) P = 0) : aeval ζ.1 P = 0 := by
  have hμ := μc_prim q
  have h1 : cyclotomic q ℤ = minpoly ℤ (μc q) := cyclotomic_eq_minpoly hμ (NeZero.pos q)
  have hd : cyclotomic q ℤ ∣ P := h1 ▸ minpoly.isIntegrallyClosed_dvd (hμ.isIntegral (NeZero.pos q)) hP
  obtain ⟨Q, rfl⟩ := hd
  rw [map_mul, ζ.2.2, zero_mul]

lemma transfer2 {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (F : (ℤ[X])[X])
    (hF : F.map (aeval (μc q)).toRingHom = 0) : F.map (aeval ζ.1).toRingHom = 0 := by
  ext k
  rw [coeff_map, coeff_zero]
  apply transfer ζ
  have := congrArg (fun G : ℂ[X] => G.coeff k) hF
  simpa [coeff_map] using this

lemma nthRoots_eq (q : ℕ) [NeZero q] :
    nthRootsFinset q (1 : ℂ) = (Finset.range q).image (fun a => μc q ^ a) := by
  have hμ := μc_prim q
  ext z
  rw [mem_nthRootsFinset (NeZero.pos q), Finset.mem_image]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := hμ.eq_pow_of_pow_eq_one hz
    exact ⟨i, Finset.mem_range.2 hi, rfl⟩
  · rintro ⟨a, -, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]

lemma primRoots_eq (q : ℕ) [NeZero q] :
    primitiveRoots q ℂ = ((Finset.range q).filter (fun a => Nat.Coprime a q)).image (fun a => μc q ^ a) := by
  have hμ := μc_prim q
  ext z
  rw [mem_primitiveRoots (NeZero.pos q), Finset.mem_image]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := hμ.eq_pow_of_pow_eq_one hz.pow_eq_one
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, (hμ.pow_iff_coprime (NeZero.pos q) i).1 hz⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact hμ.pow_of_coprime a (Finset.mem_filter.1 ha).2

lemma injOn (q : ℕ) [NeZero q] (s : Finset ℕ) (hs : s ⊆ Finset.range q) :
    Set.InjOn (fun a => μc q ^ a) s := by
  intro i hi j hj h
  exact (μc_prim q).pow_inj (Finset.mem_range.1 (hs hi)) (Finset.mem_range.1 (hs hj)) h

lemma C_prod_range (q : ℕ) [NeZero q] :
    ∏ a ∈ Finset.range q, (X - C (μc q ^ a)) = (X ^ q - 1 : ℂ[X]) := by
  rw [X_pow_sub_one_eq_prod (NeZero.pos q) (μc_prim q), nthRoots_eq,
    Finset.prod_image (injOn q _ (subset_refl _))]

lemma C_prod_coprime (q : ℕ) [NeZero q] :
    ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C (μc q ^ a)) = cyclotomic q ℂ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (μc_prim q), primRoots_eq,
    Finset.prod_image (injOn q _ (Finset.filter_subset _ _))]

lemma C_prod_erase (q : ℕ) [NeZero q] :
    ∏ a ∈ (Finset.range q).erase 0, (X - C (μc q ^ a)) = ∑ i ∈ Finset.range q, (X ^ i : ℂ[X]) := by
  have h0 : 0 ∈ Finset.range q := Finset.mem_range.2 (NeZero.pos q)
  have h := Finset.mul_prod_erase (Finset.range q) (fun a => (X - C (μc q ^ a) : ℂ[X])) h0
  have hne : (X - C (1 : ℂ) : ℂ[X]) ≠ 0 := X_sub_C_ne_zero 1
  apply mul_left_cancel₀ hne
  calc (X - C (1 : ℂ)) * ∏ a ∈ (Finset.range q).erase 0, (X - C (μc q ^ a))
      = ∏ a ∈ Finset.range q, (X - C (μc q ^ a)) := by simpa only [pow_zero] using h
    _ = X ^ q - 1 := C_prod_range q
    _ = (X - C (1 : ℂ)) * ∑ i ∈ Finset.range q, (X ^ i : ℂ[X]) := by
        rw [map_one, mul_comm, geom_sum_mul]

end GlobalTheory.EtC.PrimBasic

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

lemma prim_pow_q {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := transfer ζ (X ^ q - 1) (by simp [(μc_prim q).pow_eq_one])
  simpa [sub_eq_zero] using h

lemma prod_range {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ Finset.range q, (X - C (ζ.1 ^ a)) = (X ^ q - 1 : A[X]) := by
  have h := transfer2 ζ (∏ a ∈ Finset.range q, (X - C X ^ a) - (X ^ q - 1 : (ℤ[X])[X])) (by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_range, sub_self])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  simpa only [← C_pow, sub_eq_zero] using h

lemma prod_coprime {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C (ζ.1 ^ a)) = cyclotomic q A := by
  have h := transfer2 ζ (∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C X ^ a)
      - cyclotomic q (ℤ[X])) (by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_coprime, sub_self])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  simpa only [← C_pow, sub_eq_zero] using h

lemma prod_erase {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ (Finset.range q).erase 0, (1 - ζ.1 ^ a) = (q : A) := by
  have h := transfer2 ζ (∏ a ∈ (Finset.range q).erase 0, (X - C X ^ a) - ∑ i ∈ Finset.range q, (X ^ i : (ℤ[X])[X])) (by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_erase, sub_self])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  have h2 := congrArg (eval (1 : A)) h
  simp only [eval_sub, eval_prod, eval_finsetSum, eval_X, eval_C, eval_pow, one_pow, eval_zero,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, sub_eq_zero] at h2
  simpa [← C_pow] using h2

end GlobalTheory.EtC.PrimBasic

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

lemma isUnit_one_sub {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (c : ℕ)
    (hc : c % q ≠ 0) : IsUnit (1 - ζ.1 ^ c) := by
  have hmem : c % q ∈ (Finset.range q).erase 0 :=
    Finset.mem_erase.2 ⟨hc, Finset.mem_range.2 (Nat.mod_lt _ (NeZero.pos q))⟩
  have hd : (1 - ζ.1 ^ (c % q)) ∣ (q : A) :=
    (Finset.dvd_prod_of_mem (fun a => 1 - ζ.1 ^ a) hmem).trans (dvd_of_eq (prod_erase ζ))
  rw [pow_eq_pow_mod c (prim_pow_q ζ)]
  exact isUnit_of_dvd_unit hd ζ.2.1

lemma isUnit_val {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : IsUnit ζ.1 := by
  refine isUnit_iff_exists_inv.2 ⟨ζ.1 ^ (q - 1), ?_⟩
  rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q), prim_pow_q ζ]

lemma isUnit_pow_sub_pow_of_le {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (a b : ℕ)
    (hab : ¬ a ≡ b [MOD q]) (hle : b ≤ a) : IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hd : d % q ≠ 0 := by
    intro h0
    apply hab
    exact (Nat.modEq_iff_dvd' hle).2 (by simpa using Nat.dvd_of_mod_eq_zero h0) |>.symm
  have e : ζ.1 ^ (b + d) - ζ.1 ^ b = -(ζ.1 ^ b * (1 - ζ.1 ^ d)) := by ring
  rw [e]
  exact (((isUnit_val ζ).pow b).mul (isUnit_one_sub ζ d hd)).neg

theorem prim_basic : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], (∀ ζ : Prim q A, ζ.1 ^ q = 1) ∧ (∀ (ζ : Prim q A) (a : ℕ), Nat.Coprime a q → ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ a) ∧ (∀ (ζ : Prim q A) (a b : ℕ), ¬ a ≡ b [MOD q] → IsUnit (ζ.1 ^ a - ζ.1 ^ b)) ∧ (∀ (ζ : Prim q A) (x : A), x ^ q = 1 → ∏ a ∈ Finset.range q, (x - ζ.1 ^ a) = 0) ∧ (∀ (ζ ξ : Prim q A), ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (ξ.1 - ζ.1 ^ a) = 0) ∧ ∀ (r : ℕ), r ∣ q → ∀ ζ : Prim q A, ∃ ξ : Prim r A, ξ.1 = ζ.1 ^ (q / r) := by
  intro q _ A _
  refine ⟨fun ζ => prim_pow_q ζ, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ a ha
    have h : aeval (ζ.1 ^ a) (cyclotomic q ℤ) = 0 := by
      rw [← aeval_X_pow (R := ℤ), ← aeval_comp]
      apply transfer ζ
      rw [aeval_comp, aeval_X_pow, aeval_cyc]
      exact ((μc_prim q).pow_of_coprime a ha).isRoot_cyclotomic (NeZero.pos q)
    exact ⟨(⟨ζ.1 ^ a, ζ.2.1, h⟩ : {z : A // IsUnit (q : A) ∧ aeval z (cyclotomic q ℤ) = 0}), rfl⟩
  · intro ζ a b hab
    rcases le_total b a with hle | hle
    · exact isUnit_pow_sub_pow_of_le ζ a b hab hle
    · have := isUnit_pow_sub_pow_of_le ζ b a (fun h => hab h.symm) hle
      have e : ζ.1 ^ a - ζ.1 ^ b = -(ζ.1 ^ b - ζ.1 ^ a) := by ring
      rw [e]; exact this.neg
  · intro ζ x hx
    have h := congrArg (eval x) (prod_range ζ)
    simpa [eval_prod, hx] using h
  · intro ζ ξ
    have h := congrArg (eval ξ.1) (prod_coprime ζ)
    rw [← aeval_cyc, ξ.2.2] at h
    simpa [eval_prod] using h
  · intro r hr ζ
    have hq0 : q ≠ 0 := NeZero.ne q
    have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (Nat.eq_zero_of_zero_dvd hr)
    have hk0 : q / r ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hr) (Nat.pos_of_ne_zero hr0)).ne'
    have hunit : IsUnit (r : A) := by
      obtain ⟨k, hk⟩ := hr
      have : IsUnit ((r : A) * k) := by rw [← Nat.cast_mul, ← hk]; exact ζ.2.1
      exact isUnit_of_mul_isUnit_left this
    have h : aeval (ζ.1 ^ (q / r)) (cyclotomic r ℤ) = 0 := by
      rw [← aeval_X_pow (R := ℤ), ← aeval_comp]
      apply transfer ζ
      rw [aeval_comp, aeval_X_pow, aeval_cyc]
      have hp := (μc_prim q).pow_of_dvd hk0 (Nat.div_dvd_of_dvd hr)
      rw [Nat.div_div_self hr hq0] at hp
      exact hp.isRoot_cyclotomic (Nat.pos_of_ne_zero hr0)
    exact ⟨(⟨ζ.1 ^ (q / r), hunit, h⟩ : {z : A // IsUnit (r : A) ∧ aeval z (cyclotomic r ℤ) = 0}), rfl⟩

end GlobalTheory.EtC.PrimBasic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], (∀ ζ : Prim q A, ζ.1 ^ q = 1) ∧ (∀ (ζ : Prim q A) (a : ℕ), Nat.Coprime a q → ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ a) ∧ (∀ (ζ : Prim q A) (a b : ℕ), ¬ a ≡ b [MOD q] → IsUnit (ζ.1 ^ a - ζ.1 ^ b)) ∧ (∀ (ζ : Prim q A) (x : A), x ^ q = 1 → ∏ a ∈ Finset.range q, (x - ζ.1 ^ a) = 0) ∧ (∀ (ζ ξ : Prim q A), ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (ξ.1 - ζ.1 ^ a) = 0) ∧ ∀ (r : ℕ), r ∣ q → ∀ ζ : Prim q A, ∃ ξ : Prim r A, ξ.1 = ζ.1 ^ (q / r) := by
  first | (exact @GlobalTheory.EtC.PrimBasic.prim_basic) | (exact GlobalTheory.EtC.PrimBasic.prim_basic) | (intros; apply GlobalTheory.EtC.PrimBasic.prim_basic  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValues
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem ev_delta_values : ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
    (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
    (∀ (x : Sx E 0 U), EtC.ev (δ n m α) 0 m (by simp) U x =
      Sec.map (I.d n m) (EtC.ev α 0 n (by simp) U x)) ∧
    ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
      EtC.ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (EtC.ev α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • EtC.ev α p t (by omega) U (x.face i) := by
  intro R _ E I n m hm α U
  exact ⟨fun x => CupSpec.ev_δ_zero hm α U n m (by simp) (by simp) x,
    fun p s t hs ht x => CupSpec.ev_δ_succ hm α U p s t hs ht x⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
      (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
      (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x =
        Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧
      ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
        (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
        ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
          m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  intro R _ E I n m hm α U
  have ev_def {k : ℤ} (β : Cochain ((chains R).obj E) I k) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + k = s) (x : Sx E p U) :
      ev β p s h U x = Sec.map ((chainsXIso R E p).inv ≫ β.v _ _ h) (freeGen R _ U x) := rfl
  have hzero (x : Sx E 0 U) :
      ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x) := by
    rw [ev_def, δ_v n m hm α _ m (by simp) n 1 (by omega) (by simp),
      (CupSpec.isZero_chains (R := R) E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0,
      zero_comp, smul_zero, add_zero]
    rfl
  have hsucc (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
      (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
      ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
    rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add,
      Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _),
      CupSpec.chains_d, Category.assoc, Preadditive.sum_comp]
    refine (map_add (CupSpec.mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zsmul, map_sum, Units.smul_def]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    rfl
  exact ⟨hzero, hsucc⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicProperti
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicProperti
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ResBasic

variable {C : Type*} [Category C] [Abelian C] {X : C} (I : InjectiveResolution X)

end GlobalTheory.EtC.ResBasic

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private theorem injectiveResolution_cochainComplex_exact_and_exactAt {C : Type*} [Category C] [Abelian C]
    {X : C} (I : InjectiveResolution X) :
    (∀ n : ℤ, Injective (I.cochainComplex.X n)) ∧
    (∀ n : ℤ, n < 0 → IsZero (I.cochainComplex.X n)) ∧
    Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ∧
    (∃ w : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
        I.cochainComplex.d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧
    (∀ n : ℤ, n ≠ 0 → I.cochainComplex.ExactAt n) := by
  refine ⟨fun n => inferInstance, fun n hn => ?_, ?_, ?_, fun n hn => ?_⟩
  · exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
      have h : (ComplexShape.embeddingUpNat.f i : ℤ) = i := rfl
      omega)
  · rw [I.ι'_f_zero]
    erw [Iso.inv_hom_id_assoc]
    exact mono_comp (I.ι.f 0) _
  · have hw : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
        I.cochainComplex.d 0 1 = 0 := by
      rw [I.ι'_f_zero, I.cochainComplex_d 0 1 0 1 rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      erw [Category.assoc, Iso.inv_hom_id_assoc, I.ι_f_zero_comp_complex_d_assoc, zero_comp]
      rfl
    refine ⟨hw, ?_⟩
    refine (ShortComplex.exact_iff_of_iso ?_).mpr I.exact₀
    refine ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl)
      (I.cochainComplexXIso 1 1 rfl) ?_ ?_
    · dsimp only
      rw [I.ι'_f_zero]
      erw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, Iso.inv_hom_id_assoc]
    · dsimp only
      rw [I.cochainComplex_d 0 1 0 1 rfl rfl]
      simp
  · exact (quasiIsoAt_iff_exactAt I.ι' n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn)).mp
      inferInstance


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.res_basic : ∀ (R : Type) [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R), (∀ n : ℤ, Injective ((_root_.GlobalTheory.EtC.res R F).X n)) ∧
    (∀ n : ℤ, n < 0 → IsZero ((_root_.GlobalTheory.EtC.res R F).X n)) ∧ Mono (_root_.GlobalTheory.EtC.resι R F) ∧
    (∃ w : _root_.GlobalTheory.EtC.resι R F ≫ (_root_.GlobalTheory.EtC.res R F).d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧
    (∀ n : ℤ, n ≠ 0 → (_root_.GlobalTheory.EtC.res R F).ExactAt n) ∧
    ∀ (E : _root_.GlobalTheory.EtC.Spc) (n : ℤ), 0 < n → IsZero (((_root_.GlobalTheory.EtC.chains R).obj E).X n) := by
  intro R _ F
  unfold _root_.GlobalTheory.EtC.res _root_.GlobalTheory.EtC.resι _root_.GlobalTheory.EtC.chains
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := injectiveResolution_cochainComplex_exact_and_exactAt (injectiveResolution F)
  refine ⟨h₁, h₂, h₃, h₄, h₅, fun E n hn => ?_⟩
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
    have h : (ComplexShape.embeddingDownNat.f i : ℤ) = -i := rfl
    omega)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ n : ℤ, Injective ((res R F).X n)) ∧ (∀ n : ℤ, n < 0 → IsZero ((res R F).X n)) ∧ Mono (resι R F) ∧ (∃ w : resι R F ≫ (res R F).d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧ (∀ n : ℤ, n ≠ 0 → (res R F).ExactAt n) ∧ ∀ (E : Spc) (n : ℤ), 0 < n → IsZero (((chains R).obj E).X n) := by
  first | exact @GlobalTheory.EtC.res_basic | exact GlobalTheory.EtC.res_basic | (intros; apply GlobalTheory.EtC.res_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSections
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.MonoEpi

instance wEqLBMonoEpi (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable {R : Type} [CommRing R]

theorem sec_ext {F G : Shv R} (φ ψ : F ⟶ G) (h : ∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) : φ = ψ := by
  apply Sheaf.hom_ext
  ext U a
  exact h (unop U) a

theorem mono_iff_inj {F G : Shv R} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U)) := by
  constructor
  · intro h U
    have : Mono φ.hom := inferInstanceAs (Mono ((sheafToPresheaf _ _).map φ))
    have : Mono (φ.hom.app (op U)) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 this
  · intro h
    have : Mono φ.hom := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      exact (ModuleCat.mono_iff_injective _).2 (h (unop U))
    exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem inj_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    (∀ U, Function.Injective (Sec.map φ (U := U))) ↔
      ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  constructor
  · intro h U a ha
    have : a = 0 := h U (by rw [ha]; exact (map_zero _).symm)
    subst this
    exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => map_zero _⟩
  · intro h U
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨S, hS, hP⟩ := h U a ha
    have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
      (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
    refine (hF S hS).isSeparatedFor.ext fun V g hg => ?_
    change Sec.res g a = Sec.res g (0 : Sec F U)
    rw [hP V g hg]
    exact (map_zero _).symm

theorem epi_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b := by
  rw [← Sheaf.isLocallySurjective_iff_epi']
  constructor
  · intro h U b
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology φ.hom b, fun V g hg => hg⟩
  · intro h
    constructor
    intro U b
    obtain ⟨S, hS, hP⟩ := h U b
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    exact hP V g hg

end GlobalTheory.EtC.MonoEpi

open GlobalTheory.EtC.MonoEpi in
theorem GlobalTheory.EtC.mono_epi_sections : ∀ (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G), (Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U))) ∧ (Mono φ ↔ ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0) ∧ (Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) ∧ (∀ ψ : F ⟶ G, (∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) → φ = ψ) := by
  intro R _ F G φ
  exact ⟨mono_iff_inj φ, (mono_iff_inj φ).trans (inj_iff_loc φ), epi_iff_loc φ, fun ψ h => sec_ext φ ψ h⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections : ∀ (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G), (Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U))) ∧ (Mono φ ↔ ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0) ∧ (Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) ∧ (∀ ψ : F ⟶ G, (∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) → φ = ψ) := by
  first | (exact @GlobalTheory.EtC.mono_epi_sections) | (exact GlobalTheory.EtC.mono_epi_sections) | (intros; apply GlobalTheory.EtC.mono_epi_sections  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculus
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.OrdCalc

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem vne (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≠ 0 := (map_ne_zero v.1).2 hx

theorem ord_mul (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul (vne v hx) (vne v hy)]; ring

theorem ord_zpow (v : Place k F) (x : F) (m : ℤ) : ord v (x ^ m) = m * ord v x := by
  unfold ord
  rw [map_zpow₀, WithZero.log_zpow]; simp [smul_eq_mul]

theorem le_one_iff (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x ≤ 1 ↔ 0 ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) one_ne_zero, WithZero.log_one, neg_nonneg]

theorem le_iff (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) (vne v hy), neg_le_neg_iff]

theorem eq_one_iff (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x = 1 ↔ ord v x = 0 := by
  have h1 := WithZero.log_le_log (vne v hx) (one_ne_zero (α := WithZero (Multiplicative ℤ)))
  have h2 := WithZero.log_le_log (one_ne_zero (α := WithZero (Multiplicative ℤ))) (vne v hx)
  rw [WithZero.log_one] at h1 h2
  unfold ord
  constructor
  · intro h; rw [h, WithZero.log_one]; simp
  · intro h
    exact le_antisymm (h1.1 (by omega)) (h2.1 (by omega))

theorem exists_unif (v : Place k F) : ∃ π : F, π ≠ 0 ∧ ord v π = 1 := by
  obtain ⟨π, hπ⟩ := v.2.1 (WithZero.exp (-1 : ℤ))
  refine ⟨π, ?_, ?_⟩
  · rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  · unfold ord; rw [hπ, WithZero.log_exp]; simp

theorem nrm_max (v : Place k F) (n : ℕ) (x : Fin n → F) (hx : x ≠ 0) :
    ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hx
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i0, Finset.mem_univ _⟩ (fun i => v.1 (x i))
  have hle : ∀ j, v.1 (x j) ≤ v.1 (x i) := fun j => by
    rw [← hi]; exact Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j)
  refine ⟨i, ?_, hi, ?_, hle⟩
  · intro h0
    have := hle i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  · unfold ordVec ord nrm; rw [hi]

theorem nrm_smul (v : Place k F) (n : ℕ) (x : Fin n → F) (c : F) :
    nrm v (c • x) = v.1 c * nrm v x := by
  unfold nrm
  apply le_antisymm
  · apply Finset.sup_le; intro i _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_mul' le_rfl (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ i))
  · rcases isEmpty_or_nonempty (Fin n) with h | h
    · simp [Finset.univ_eq_empty]
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => v.1 (x i))
      rw [hi]
      calc v.1 c * v.1 (x i) = v.1 ((c • x) i) := by simp
      _ ≤ _ := Finset.le_sup (f := fun i => v.1 ((c • x) i)) (Finset.mem_univ i)

theorem nrm_mulVec_le (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : nrm v (u.mulVec x) ≤ nrm v x := by
  unfold nrm
  apply Finset.sup_le; intro i _
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (u i j) * v.1 (x j) ≤ 1 * Finset.univ.sup (fun i => v.1 (x i)) :=
        mul_le_mul' (hu i j) (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j))
  _ = _ := one_mul _

theorem mul_int (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) (hu' : ∀ i j, v.1 (u' i j) ≤ 1) : ∀ i j, v.1 ((u * u') i j) ≤ 1 := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro l _
  rw [map_mul]
  calc v.1 (u i l) * v.1 (u' l j) ≤ 1 * 1 := mul_le_mul' (hu i l) (hu' l j)
  _ = 1 := one_mul _

theorem det_adj_int (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : v.1 u.det ≤ 1 ∧ ∀ i j, v.1 (u.adjugate i j) ≤ 1 := by
  let M : Matrix (Fin n) (Fin n) v.O := fun i j => ⟨u i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu i j)⟩
  have hM : M.map v.O.subtype = u := by ext i j; rfl
  constructor
  · have e : u.det = ((M.det : v.O) : F) := by
      rw [← hM]; exact (RingHom.map_det v.O.subtype M).symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.det).2
  · intro i j
    have e : u.adjugate i j = ((M.adjugate i j : v.O) : F) := by
      rw [← hM]
      have := congrFun (congrFun (RingHom.map_adjugate v.O.subtype M) i) j
      exact this.symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.adjugate i j).2

theorem unimod_mul_inv (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : Unimod v u) (hu' : Unimod v u') : Unimod v (u * u') ∧ Unimod v u⁻¹ := by
  refine ⟨⟨mul_int v n u u' hu.1 hu'.1, by rw [Matrix.det_mul, map_mul, hu.2, hu'.2, one_mul]⟩, ?_⟩
  have hd : u.det ≠ 0 := fun h => by have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hu.2, inv_one, one_mul]
    exact (det_adj_int v n u hu.1).2 i j
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hu.2, inv_one]

theorem nrm_unimod (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : Unimod v u) : nrm v (u.mulVec x) = nrm v x := by
  have hd : IsUnit u.det := isUnit_iff_ne_zero.2 (fun h => by
    have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this)
  apply le_antisymm (nrm_mulVec_le v n u x hu.1)
  have h := nrm_mulVec_le v n u⁻¹ (u.mulVec x) (unimod_mul_inv v n u u hu hu).2.1
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul u hd, Matrix.one_mulVec] at h

end GlobalTheory.Nef.OrdCalc

open GlobalTheory.Nef.OrdCalc in
theorem GlobalTheory.Nef.ord_calculus : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ v : Place k F, (∀ x y : F, x ≠ 0 → y ≠ 0 → ord v (x * y) = ord v x + ord v y) ∧ (∀ x : F, x ≠ 0 → ∀ m : ℤ, ord v (x ^ m) = m * ord v x) ∧ (∀ x : F, x ≠ 0 → (v.1 x ≤ 1 ↔ 0 ≤ ord v x)) ∧ (∀ x : F, x ≠ 0 → (v.1 x = 1 ↔ ord v x = 0)) ∧ (∀ x y : F, x ≠ 0 → y ≠ 0 → (v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x)) ∧ (∃ π : F, π ≠ 0 ∧ ord v π = 1) ∧ (∀ (n : ℕ) (x : Fin n → F), x ≠ 0 → ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i)) ∧ (∀ (n : ℕ) (x : Fin n → F) (c : F), nrm v (c • x) = v.1 c * nrm v x) ∧ (∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F), Unimod v u → nrm v (u.mulVec x) = nrm v x) ∧ (∀ (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F), Unimod v u → Unimod v u' → Unimod v (u * u') ∧ Unimod v u⁻¹) := by
  intro k F _ _ _ v
  exact ⟨fun x y hx hy => ord_mul v x y hx hy, fun x _ m => ord_zpow v x m,
    fun x hx => le_one_iff v x hx, fun x hx => eq_one_iff v x hx, fun x y hx hy => le_iff v x y hx hy,
    exists_unif v, fun n x hx => nrm_max v n x hx, fun n x c => nrm_smul v n x c,
    fun n u x hu => nrm_unimod v n u x hu, fun n u u' hu hu' => unimod_mul_inv v n u u' hu hu'⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldPlaceOrder_calculus : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ v : Place k F, (∀ x y : F, x ≠ 0 → y ≠ 0 → ord v (x * y) = ord v x + ord v y) ∧ (∀ x : F, x ≠ 0 → ∀ m : ℤ, ord v (x ^ m) = m * ord v x) ∧ (∀ x : F, x ≠ 0 → (v.1 x ≤ 1 ↔ 0 ≤ ord v x)) ∧ (∀ x : F, x ≠ 0 → (v.1 x = 1 ↔ ord v x = 0)) ∧ (∀ x y : F, x ≠ 0 → y ≠ 0 → (v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x)) ∧ (∃ π : F, π ≠ 0 ∧ ord v π = 1) ∧ (∀ (n : ℕ) (x : Fin n → F), x ≠ 0 → ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i)) ∧ (∀ (n : ℕ) (x : Fin n → F) (c : F), nrm v (c • x) = v.1 c * nrm v x) ∧ (∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F), Unimod v u → nrm v (u.mulVec x) = nrm v x) ∧ (∀ (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F), Unimod v u → Unimod v u' → Unimod v (u * u') ∧ Unimod v u⁻¹) := by
  first | exact @GlobalTheory.Nef.ord_calculus | exact GlobalTheory.Nef.ord_calculus | (intros; apply GlobalTheory.Nef.ord_calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasic
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_basic : ∀ (R : Type) [CommRing R] , (∀ E : Spc, ((chains R).obj E).IsStrictlyLE 0) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (p : ℕ), ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom = (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p)))) ∧ ∀ (E : Spc) (p : ℕ), (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) := by
  intro R _
  refine ⟨fun E => (CochainComplex.isStrictlyLE_iff _ 0).2 (fun i hi => CupSpec.isZero_chains E i hi), fun {E E'} f p => ?_, fun E p => ?_⟩
  · rw [← cancel_epi (chainsXIso R E p).inv, ← Category.assoc, CupSpec.chains_map, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  · rw [← Category.assoc, CupSpec.chains_d, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasicStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta : ∀ (R : Type) [CommRing R] , (∀ E : Spc, ((chains R).obj E).IsStrictlyLE 0) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (p : ℕ), ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom = (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p)))) ∧ ∀ (E : Spc) (p : ℕ), (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) := by
  first | (exact @GlobalTheory.EtC.chains_basic) | (exact GlobalTheory.EtC.chains_basic) | (intros; apply GlobalTheory.EtC.chains_basic  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopology
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopology
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem quadExt_topology : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ), FiniteDimensional F E ∧ IsTopologicalRing E ∧ ContinuousInv₀ E ∧ T2Space E ∧ Continuous c ∧ Continuous (Algebra.norm F : E → F) ∧ Continuous (Algebra.trace F E) ∧ ∀ (α ν : Type) [Fintype α] [Fintype ν], IsModuleTopology F (Matrix α ν E) ∧ Good (Matrix α ν E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE
  obtain ⟨b, -, -⟩ := hE.basis
  haveI hfd : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing F E
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have htr : Continuous (Algebra.trace F E) := IsModuleTopology.continuous_of_linearMap (Algebra.trace F E)
  have hN : ∀ z : E, Algebra.norm F z = (2 : F)⁻¹ * Algebra.trace F E (z * c z) := by
    intro z
    rw [← hE.algebraMap_norm z, Algebra.trace_algebraMap, Module.finrank_eq_card_basis b, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hNc : Continuous (Algebra.norm F : E → F) := by
    have : (Algebra.norm F : E → F) = fun z => (2 : F)⁻¹ * Algebra.trace F E (z * c z) := funext hN
    rw [this]
    exact continuous_const.mul (htr.comp (continuous_id.mul hc))
  have hT2 : T2Space E := (GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F E).t2
  have hinv : ∀ z : E, z⁻¹ = (Algebra.norm F z)⁻¹ • c z := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hn : Algebra.norm F z ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hz
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [Algebra.smul_def, mul_assoc, mul_comm (c z) z, ← hE.algebraMap_norm z, ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hI : ContinuousInv₀ E := by
    refine ⟨fun z hz => ?_⟩
    have : (Inv.inv : E → E) = fun z => (Algebra.norm F z)⁻¹ • c z := funext hinv
    rw [this]
    have hn : Algebra.norm F z ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hz
    exact ((continuousAt_inv₀ hn).comp hNc.continuousAt).smul hc.continuousAt
  refine ⟨hfd, inferInstance, hI, hT2, hc, hNc, htr, fun α ν _ _ => ?_⟩
  haveI hM : IsModuleTopology F (Matrix α ν E) := inferInstanceAs (IsModuleTopology F (α → ν → E))
  exact ⟨hM, GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F (Matrix α ν E)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadExt_topological_properties : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ), FiniteDimensional F E ∧ IsTopologicalRing E ∧ ContinuousInv₀ E ∧ T2Space E ∧ Continuous c ∧ Continuous (Algebra.norm F : E → F) ∧ Continuous (Algebra.trace F E) ∧ ∀ (α ν : Type) [Fintype α] [Fintype ν], IsModuleTopology F (Matrix α ν E) ∧ Good (Matrix α ν E) := by
  first | exact @GlobalTheory.quadExt_topology | exact GlobalTheory.quadExt_topology | (intros; apply GlobalTheory.quadExt_topology <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndE
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndE
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open IntermediateField

theorem finiteDimensional_adjoin_of_trdeg_le_one {k F : Type} [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F] (htr : Algebra.trdeg k F ≤ 1) (x : F) (hx : Transcendental k x) :
    FiniteDimensional k⟮x⟯ F := by
  have hind : AlgebraicIndependent k (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hb : IsTranscendenceBasis k (fun _ : Unit => x) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have halg : Algebra.IsAlgebraic k⟮x⟯ F := by
    have := hb.isAlgebraic_field
    rwa [Set.range_const] at this
  have : Algebra.EssFiniteType k⟮x⟯ F := Algebra.EssFiniteType.of_comp k k⟮x⟯ F
  obtain ⟨S, hS⟩ := IntermediateField.fg_top_iff.mpr this
  have hfin : FiniteDimensional k⟮x⟯ (adjoin k⟮x⟯ (S : Set F)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [hS] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := k⟮x⟯) (E := F)).toLinearEquiv

theorem essFiniteType_trdeg_of_isFF {k F : Type} [Field k] [Field F] [Algebra k F] (h : IsFF k F) :
    Algebra.EssFiniteType k F ∧ Algebra.trdeg k F ≤ 1 := by
  obtain ⟨t, ht, hfin⟩ := h
  have h1 : Algebra.EssFiniteType k k⟮t⟯ :=
    IntermediateField.essFiniteType_iff.mpr ⟨{t}, by simp⟩
  refine ⟨Algebra.EssFiniteType.comp k k⟮t⟯ F, ?_⟩
  open IntermediateField.algebraAdjoinAdjoin in
  have : Algebra.IsAlgebraic (Algebra.adjoin k {t}) F := Algebra.IsAlgebraic.trans _ k⟮t⟯ _
  have hind : AlgebraicIndependent k (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hb : IsTranscendenceBasis k (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_iff_isAlgebraic.mpr (by rwa [Set.range_const])
  rw [← hb.cardinalMk_eq_trdeg]
  simp

theorem isFF_main : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], IsFF k F →
    (∀ x : F, Transcendental k x → FiniteDimensional k⟮x⟯ F) ∧
    ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k E := by
  intro k F _ _ _ h
  obtain ⟨hfg, htr⟩ := essFiniteType_trdeg_of_isFF h
  refine ⟨fun x hx => finiteDimensional_adjoin_of_trdeg_le_one htr x hx, ?_⟩
  intro E _ _ _ _ _
  have hfgE : Algebra.EssFiniteType k E := Algebra.EssFiniteType.comp k F E
  have h0 : Algebra.trdeg F E = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have htrE : Algebra.trdeg k E ≤ 1 := by
    rw [← trdeg_add_eq k F, h0, add_zero]; exact htr
  obtain ⟨t, ht, _⟩ := h
  have ht' : Transcendental k (algebraMap F E t) :=
    (transcendental_algebraMap_iff (algebraMap F E).injective).mpr ht
  exact ⟨algebraMap F E t, ht', finiteDimensional_adjoin_of_trdeg_le_one htrE _ ht'⟩

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndEStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], IsFF k F → (∀ x : F, Transcendental k x → FiniteDimensional k⟮x⟯ F) ∧ ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k E := by
  first | exact @GlobalTheory.Nef.isFF_main | exact GlobalTheory.Nef.isFF_main | (intros; apply GlobalTheory.Nef.isFF_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

private theorem eis_spread (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ) (a : ℕ → ℂ) (h : HasQ 1 f a) :
    HasQ N f (spread N a) := by
  unfold HasQ at h ⊢
  intro τ
  have hg : Function.Injective (fun n : ℕ => N * n) := fun x y hxy => Nat.eq_of_mul_eq_mul_left hN hxy
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← hg.hasSum_iff]
  · convert h τ using 1
    funext n
    simp only [Function.comp_apply, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hN]
    congr 2
    push_cast
    field_simp
  · intro m hm
    simp only [spread]
    rw [if_neg, zero_mul]
    rintro ⟨k, rfl⟩
    exact hm ⟨k, rfl⟩

private theorem eis_one {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (p : PowerSeries ℤ)
    (hp : p.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 f) :
    HasQ 1 f fun n => ((PowerSeries.coeff n p : ℤ) : ℂ) := by
  unfold HasQ
  intro τ
  have hs := hf.hasSum τ
  rw [← hp] at hs
  convert hs using 1
  funext n
  rw [PowerSeries.coeff_map, eq_intCast, ReciprocityTheory.ChartRestriction.L1.qm, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem eis_hasQ_int (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) :
    ∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ) := by
  obtain ⟨k, hk, p, hp⟩ : ∃ k : ℤ, IsMF k F ∧ ∃ p : PowerSeries ℤ,
      p.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 F := by
    rcases hF with rfl | rfl | rfl
    · exact ⟨4, ⟨E₄, fun _ => rfl⟩, _, ReciprocityTheory.ChartRestriction.L1.map_eisensteinFourInt⟩
    · exact ⟨6, ⟨E₆, fun _ => rfl⟩, _, ReciprocityTheory.ChartRestriction.L1.map_eisensteinSixInt⟩
    · exact ⟨12, ReciprocityTheory.ChartRestriction.L1.isMF_DD, _, ReciprocityTheory.ChartRestriction.L1.dC_eq⟩
  refine ⟨fun n => if N ∣ n then PowerSeries.coeff (n / N) p else 0, ?_⟩
  convert eis_spread N hN F _ (eis_one hk p hp) using 1
  funext n
  simp only [spread]
  split_ifs <;> simp

theorem eis_qAll (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD)
    (R : Subring ℂ) : QAll (· ∈ R) N F := by
  obtain ⟨a, ha⟩ := eis_hasQ_int N hN F hF
  exact ⟨_, ha, fun n => intCast_mem R (a n)⟩

theorem eis_qConj (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD)
    (g : ℂ ≃+* ℂ) : QConj g N F F := by
  obtain ⟨a, ha⟩ := eis_hasQ_int N hN F hF
  refine ⟨_, ha, ?_⟩
  simpa only [map_intCast] using ha

theorem eis_q : ∀ (N : ℕ), 0 < N → ∀ F : ℍ → ℂ, (F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) →
    (∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ)) ∧ (∀ R : Subring ℂ, QAll (· ∈ R) N F) ∧
      ∀ g : ℂ ≃+* ℂ, QConj g N F F := by
  intro N hN F hF
  exact ⟨eis_hasQ_int N hN F hF, fun R => eis_qAll N hN F hF R, fun g => eis_qConj N hN F hF g⟩

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegralityStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_delta_qExpansion_integrality : ∀ (N : ℕ), 0 < N → ∀ F : ℍ → ℂ, (F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) → (∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ)) ∧ (∀ R : Subring ℂ, QAll (· ∈ R) N F) ∧ ∀ g : ℂ ≃+* ℂ, QConj g N F F := by
  first | exact @GlobalTheory.QFam.eis_q | exact GlobalTheory.QFam.eis_q | (intros; apply GlobalTheory.QFam.eis_q <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def liftHom {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) : ULift.{1} R →+* ULift.{1} S :=
  (ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)

instance {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) :
    (ModuleCat.coextendScalars.{1, 1, 1} (liftHom φ)).IsRightAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (liftHom φ)).isRightAdjoint

def coind {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) : Shv R ⥤ Shv S :=
  sheafCompose _ (ModuleCat.coextendScalars.{1, 1, 1} (liftHom φ))

end GlobalTheory.EtC

end
end
