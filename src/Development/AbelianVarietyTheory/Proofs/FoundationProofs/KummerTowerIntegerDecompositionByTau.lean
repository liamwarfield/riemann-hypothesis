module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterPowersOrthogonalGeometricInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralCoeffsOfGeometricFixedQExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralCoeffsOfGeometricFixedQExpansion
open GlobalTheory.K5

namespace GlobalTheory.K5.OrthDecomp

theorem orth : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) →
      IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) →
        ∀ j < p ^ N, IsInt (p := p) (c j) :=
  GlobalTheory.K5.Orth.orth

end GlobalTheory.K5.OrthDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralCoeffsOfGeometricFixedQExpansionStatement
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_coeffs_of_geometric_fixed_qExpansion : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) →
    IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) →
      ∀ j < p ^ N, IsInt (p := p) (c j) := by
  first | exact @GlobalTheory.K5.OrthDecomp.orth | exact GlobalTheory.K5.OrthDecomp.orth | (intros; apply GlobalTheory.K5.OrthDecomp.orth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizer
open Polynomial IntermediateField

namespace GlobalTheory.K5.Span

variable (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]

def baseField : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x})

variable {p Ω}

theorem algebraMap_mem_baseField (a : O0 p) : algebraMap (O0 p) Ω a ∈ baseField p Ω :=
  Subfield.subset_closure (Or.inl ⟨a, rfl⟩)

theorem ggeo_fix_baseField {g : Gal p Ω} (hg : g ∈ Ggeo (p := p) Ω) {x : Ω}
    (hx : x ∈ baseField p Ω) :
    g x = x := by
  have hle : baseField p Ω ≤ RingHom.eqLocusField (g : Ω →+* Ω) (RingHom.id Ω) := by
    refine Subfield.closure_le.2 ?_
    rintro z (⟨a, rfl⟩ | hz)
    · show g (algebraMap (O0 p) Ω a) = algebraMap (O0 p) Ω a
      exact g.commutes a
    · show g z = z
      exact hg z hz
  exact hle hx

noncomputable def toGal (σ : Ω ≃ₐ[baseField p Ω] Ω) : Gal p Ω :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun a =>
    σ.commutes (⟨algebraMap (O0 p) Ω a, algebraMap_mem_baseField a⟩ : baseField p Ω)

theorem toGal_apply (σ : Ω ≃ₐ[baseField p Ω] Ω) (x : Ω) : toGal σ x = σ x := rfl

theorem isAlgebraic_baseField (h : IsClo p Ω) : Algebra.IsAlgebraic (baseField p Ω) Ω := by
  haveI := h.alg
  refine ⟨fun x => ?_⟩
  obtain ⟨P, hP0, hPx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := O0 p) x
  let φ : O0 p →+* baseField p Ω :=
    (algebraMap (O0 p) Ω).codRestrict (baseField p Ω) algebraMap_mem_baseField
  have hφ : Function.Injective φ := fun a b hab => h.inj (congrArg Subtype.val hab)
  refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφ).2 hP0, ?_⟩
  rw [aeval_def, eval₂_map]
  have : (algebraMap (baseField p Ω) Ω).comp φ = algebraMap (O0 p) Ω := by
    ext a; rfl
  rw [this, ← aeval_def, hPx]

end GlobalTheory.K5.Span

open GlobalTheory.K5.Span in
open GlobalTheory.K5 GlobalTheory.K5.Span in
theorem GlobalTheory.K5.span_fixed_ggeo_stab : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (y : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧
    y = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  intro p _ Ω _ _ h T N y hy
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  haveI := h.clo
  set L := baseField p Ω
  haveI : CharZero L := inferInstance
  haveI : Algebra.IsAlgebraic L Ω := isAlgebraic_baseField h
  haveI : IsAlgClosure L Ω := ⟨h.clo, inferInstance⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  set M : IntermediateField L Ω := IntermediateField.adjoin L {T.qq N}
  have hyM : y ∈ M := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, mem_fixedField_iff]
    intro σ hσ
    have hq : σ (T.qq N) = T.qq N :=
      (mem_fixingSubgroup_iff M σ).1 hσ _ (mem_adjoin_simple_self L _)
    refine hy (toGal σ) (Subgroup.mem_inf.2 ⟨fun x hx => ?_, ?_⟩)
    · exact σ.commutes (⟨x, Subfield.subset_closure (Or.inr hx)⟩ : L)
    · rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, toGal_apply, hq]
  have hyA : y ∈ (aeval (T.qq N) : L[X] →ₐ[L] Ω).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval,
      ← adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _)]
    exact hyM
  obtain ⟨P, hP⟩ := hyA
  set q0 : L := ⟨algebraMap (O0 p) Ω (qO p), algebraMap_mem_baseField _⟩
  set Q : L[X] := X ^ (p ^ N) - C q0
  have hpN : p ^ N ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hQm : Q.Monic := monic_X_pow_sub_C _ hpN
  have hQd : Q.natDegree = p ^ N := natDegree_X_pow_sub_C _
  have hQ1 : Q ≠ 1 := by
    intro e; rw [e, natDegree_one] at hQd; exact hpN hQd.symm
  have hQq : aeval (T.qq N) Q = 0 := by
    simp only [Q, map_sub, map_pow, aeval_X, aeval_C, Basic.qq_pow]
    exact sub_self _
  set R := P %ₘ Q
  have hRd : R.natDegree < p ^ N := hQd ▸ natDegree_modByMonic_lt P hQm hQ1
  have hR : aeval (T.qq N) R = y := by
    have e := congrArg (aeval (T.qq N)) (modByMonic_add_div P Q)
    rw [map_add (f := _), map_mul, hQq, zero_mul, add_zero] at e
    rw [e]; exact hP
  refine ⟨fun j => ((R.coeff j : L) : Ω), fun j g hg => ggeo_fix_baseField hg (R.coeff j).2, ?_⟩
  rw [← hR, aeval_eq_sum_range' hRd]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizerStatement
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (y : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧
    y = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  first | exact @GlobalTheory.K5.span_fixed_ggeo_stab | exact GlobalTheory.K5.span_fixed_ggeo_stab | (intros; apply GlobalTheory.K5.span_fixed_ggeo_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerIntegerDecompositionByTau
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.Decomp

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_pow_eq_one' (T : Tower p Ω) (m : ℕ) : T.ζ (m + 1) ^ p ^ m = T.ζ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, T.ζpow, ih]

theorem exists_pow_eq_zeta_one (T : Tower p Ω) (N j : ℕ) (hj0 : 0 < j) (hjN : j < p ^ N) :
    ∃ e : ℕ, (T.ζ N ^ j) ^ e = T.ζ 1 := by
  have hN : N ≠ 0 := by rintro rfl; simp at hjN; omega
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hglt : Nat.gcd j (p ^ (M + 1)) < p ^ (M + 1) :=
    lt_of_le_of_lt (Nat.le_of_dvd hj0 (Nat.gcd_dvd_left _ _)) hjN
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hglt
  obtain ⟨a, ha, hga⟩ := (Nat.dvd_prime_pow hp.out).1 (Nat.gcd_dvd_right j (p ^ (M + 1)))
  have haM : a ≤ M := by
    by_contra h
    have : a = M + 1 := by omega
    subst this
    have h2 : p ^ (M + 1) ∣ j := hga ▸ Nat.gcd_dvd_left _ _
    exact absurd (Nat.le_of_dvd hj0 h2) (by omega)
  obtain ⟨t, ht⟩ : Nat.gcd j (p ^ (M + 1)) ∣ p ^ M := hga ▸ pow_dvd_pow p haM
  refine ⟨m * t, ?_⟩
  rw [← pow_mul, ← zeta_pow_eq_one' T M, Basic.zeta_pow_eq_iff]
  have h1 : j * m ≡ Nat.gcd j (p ^ (M + 1)) [MOD p ^ (M + 1)] := by
    unfold Nat.ModEq; rw [hm, Nat.mod_eq_of_lt hglt]
  have h2 := h1.mul_right t
  rw [← ht] at h2
  rw [← mul_assoc]; exact h2

theorem isInt_zeta (T : Tower p Ω) (N : ℕ) : IsInt (p := p) (T.ζ N) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos N) ?_
  rw [(T.prim N).pow_eq_one]; exact isIntegral_one

theorem ggeo_zeta (T : Tower p Ω) (N : ℕ) {g : Gal p Ω} (hg : g ∈ Ggeo p Ω) : g (T.ζ N) = T.ζ N := by
  apply hg
  refine ⟨Polynomial.X ^ (p ^ N) - 1, Polynomial.X_pow_sub_C_ne_zero (pow_pos hp.out.pos N) 1, ?_⟩
  simp [(T.prim N).pow_eq_one]

end GlobalTheory.K5.Decomp

namespace GlobalTheory.K5.Decomp

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isInt_qq (T : Tower p Ω) (N : ℕ) : IsInt (p := p) (T.qq N) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos N) ?_
  rw [Basic.qq_pow]; exact isIntegral_algebraMap

theorem exists_mult (T : Tower p Ω) (N j : ℕ) (hj0 : 0 < j) (hjN : j < p ^ N) :
    ∃ s : Ω, IsInt (p := p) s ∧ (∀ g ∈ Ggeo p Ω, g s = s) ∧ s * (T.ζ N ^ j - 1) = T.ζ 1 - 1 := by
  obtain ⟨e, he⟩ := exists_pow_eq_zeta_one T N j hj0 hjN
  refine ⟨∑ i ∈ Finset.range e, (T.ζ N ^ j) ^ i, ?_, ?_, ?_⟩
  · exact IsIntegral.sum _ fun i _ => ((isInt_zeta T N).pow j).pow i
  · intro g hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_pow, ggeo_zeta T N hg]
  · rw [geom_sum_mul, he]

end GlobalTheory.K5.Decomp


open GlobalTheory.K5.Decomp in
theorem GlobalTheory.K5.Decomp.decomp : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (y : Ω), IsInt (p := p) y → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ o w : Ω, IsInt (p := p) o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧ IsInt (p := p) w ∧
    (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) ∧
    (T.ζ 1 - 1) * y = (T.ζ 1 - 1) * o + (τ w - w) := by
  intro p _ _ Ω _ _ hΩ T τ hτ hτq N y hy hfix
  obtain ⟨c, hc, rfl⟩ := GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer p Ω hΩ T N y hfix
  have hci := GlobalTheory.T.isIntegral_coeffs_of_geometric_fixed_qExpansion p Ω hΩ T N c hc hy
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hs : ∀ j, ∃ s : Ω, IsInt (p := p) s ∧ (∀ g ∈ Ggeo p Ω, g s = s) ∧
      (0 < j → j < p ^ N → s * (T.ζ N ^ j - 1) = T.ζ 1 - 1) := by
    intro j
    by_cases h : 0 < j ∧ j < p ^ N
    · obtain ⟨s, h1, h2, h3⟩ := exists_mult T N j h.1 h.2
      exact ⟨s, h1, h2, fun _ _ => h3⟩
    · exact ⟨0, isIntegral_zero, fun g _ => map_zero g, fun a b => absurd ⟨a, b⟩ h⟩
  choose s hsi hsg hse using hs
  refine ⟨c 0, ∑ j ∈ Finset.range (p ^ N), s j * c j * T.qq N ^ j, hci 0 hpos, hc 0, ?_, ?_, ?_⟩
  · refine IsIntegral.sum _ fun j hj => ?_
    exact ((hsi j).mul (hci j (Finset.mem_range.1 hj))).mul ((isInt_qq T N).pow j)
  · intro g hg
    have hg1 := (Subgroup.mem_inf.1 hg).1
    have hg2 : g (T.qq N) = T.qq N := (Subgroup.mem_inf.1 hg).2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, hsg _ g hg1, hc _ g hg1, hg2]
  · obtain ⟨M, hM⟩ : ∃ M, p ^ N = M + 1 := ⟨p ^ N - 1, by omega⟩
    have key : ∀ i < M, s (i + 1) * (T.ζ N ^ (i + 1) - 1) = T.ζ 1 - 1 := fun i hi =>
      hse (i + 1) (Nat.succ_pos i) (by omega)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, hsg _ τ hτ, hc _ τ hτ, hτq N]
    rw [hM, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range M, s (i + 1) * c (i + 1) * (T.ζ N * T.qq N) ^ (i + 1) =
        s (i + 1) * c (i + 1) * T.qq N ^ (i + 1) + (T.ζ 1 - 1) * (c (i + 1) * T.qq N ^ (i + 1)) := by
      intro i hi
      rw [← key i (Finset.mem_range.1 hi)]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerIntegerDecompositionByTauStatement
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerTower_integer_decomposition_by_tau : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (y : Ω), IsInt (p := p) y →
    (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ o w : Ω, IsInt (p := p) o ∧ (∀ g ∈ Ggeo (p := p) Ω, g o = o) ∧ IsInt (p := p) w ∧
    (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) ∧
    (T.ζ 1 - 1) * y = (T.ζ 1 - 1) * o + (τ w - w) := by
  first | exact @GlobalTheory.K5.Decomp.decomp | exact GlobalTheory.K5.Decomp.decomp | (intros; apply GlobalTheory.K5.Decomp.decomp <;> assumption)
end
