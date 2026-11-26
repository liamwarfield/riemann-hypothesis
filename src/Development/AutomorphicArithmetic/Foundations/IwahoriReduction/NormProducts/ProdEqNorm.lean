module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmodule
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLevStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.ExistsOfFixed
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem exists_of_fixed {E : Type} [Field E] (G : Type) [Group G] [Finite G] [MulSemiringAction G E] (σ : E ≃+* E)
    (h : ∀ x ∈ FixedPoints.subfield G E, σ x = x) : ∃ g : G, ∀ x : E, g • x = σ x := by
  let σ' : E ≃ₐ[FixedPoints.subfield G E] E := AlgEquiv.ofRingEquiv (f := σ) fun x => h x x.2
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective G E σ'
  refine ⟨g, fun x => ?_⟩
  exact DFunLike.congr_fun hg x

theorem UpperTheory.Kd.K4.faith :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (H' : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M → CongruenceSubgroup.Gamma M ≤ H' → ∀ γ : SL(2, ℤ), (∀ f ∈ lev X H', X.sl (ofSL γ) f = f) → γ ∈ H' ∨ -γ ∈ H' := by
  intro Ω _ _ _ ε X H' M hM hle γ hγ
  have hfin : Finite (H'.map (GlobalTheory.KZ.FracGen.rhoF X M)) := by
    haveI := GlobalTheory.KZ.FracGen.finite_range X M hM
    have hr : H'.map (GlobalTheory.KZ.FracGen.rhoF X M) ≤ (GlobalTheory.KZ.FracGen.rhoF X M).range := by
      rintro _ ⟨δ, -, rfl⟩
      exact ⟨δ, rfl⟩
    exact Finite.of_injective _ (Subgroup.inclusion_injective hr)
  obtain ⟨s, hs⟩ := exists_of_fixed (H'.map (GlobalTheory.KZ.FracGen.rhoF X M))
    (GlobalTheory.KZ.FracGen.rhoF X M γ⁻¹).toRingEquiv (by
      intro x hx
      apply Subtype.ext
      show X.sl (ofSL γ⁻¹⁻¹) x = x
      rw [inv_inv]
      refine hγ _ ((mem_lev_iff X H' _).2 fun δ hδ => ?_)
      have h1 := hx ⟨GlobalTheory.KZ.FracGen.rhoF X M δ⁻¹, ⟨δ⁻¹, inv_mem hδ, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      have h3 : ((GlobalTheory.KZ.FracGen.rhoF X M δ⁻¹ x : GlobalTheory.KZ.FracGen.FM X M) : X.K) = X.sl (ofSL δ⁻¹⁻¹) x :=
        GlobalTheory.KZ.FracGen.rhoF_apply X M δ⁻¹ x
      rw [inv_inv] at h3
      rw [← h3]
      exact h2)
  obtain ⟨_, ⟨δ, hδ, rfl⟩⟩ := s

  have hact : ∀ x : GlobalTheory.KZ.FracGen.FM X M, X.sl (ofSL δ⁻¹) x = X.sl (ofSL γ) x := by
    intro x
    have h1 := congrArg Subtype.val (hs x)
    have h2 := GlobalTheory.KZ.FracGen.rhoF_apply X M δ x
    have h3 := GlobalTheory.KZ.FracGen.rhoF_apply X M γ⁻¹ x
    rw [inv_inv] at h3
    rw [← h2, ← h3]
    exact h1
  have hc1 : 1 < 6 * M + 1 := by omega
  have hc6 : Nat.Coprime (6 * M + 1) 6 := by simp
  have hcM : 6 * M + 1 ≡ 1 [MOD M] := by
    simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod_left]
  have hfix : ∀ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) →
      X.sl (ofSL (δ⁻¹ * γ⁻¹)) (siegel X (6 * M + 1) ![(a : ℚ) / M, (b : ℚ) / M]) =
        siegel X (6 * M + 1) ![(a : ℚ) / M, (b : ℚ) / M] := by
    intro a b hab
    have hmem := (GlobalTheory.KZ.FracGen.mem_FM X M _).2 (GlobalTheory.KZ.FracGen.siegel_inv X M _ hM hc1 hc6 hcM a b hab)
    have h1 := hact ⟨_, hmem⟩
    rw [map_mul, X.sl_mul]
    refine (congrArg (X.sl (ofSL γ⁻¹)) h1).trans ?_
    rw [← X.sl_mul, ← map_mul, mul_inv_cancel, map_one]
    exact X.sl_one _
  rcases GlobalTheory.T.siegel_invariance_implies_congruence ε X M (6 * M + 1) (δ⁻¹ * γ⁻¹) hM hc1 hc6 hcM hfix with h | h
  · left
    have e : γ = (δ * (δ⁻¹ * γ⁻¹))⁻¹ := by group
    rw [e]
    exact inv_mem (mul_mem hδ (hle h))
  · right
    have e : -γ = (δ * -(δ⁻¹ * γ⁻¹))⁻¹ := by
      rw [mul_neg, inv_neg]
      congr 1
      group
    rw [e]
    exact inv_mem (mul_mem hδ (hle h))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.RelOfComap
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial UniqueFactorizationMonoid
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4.Ns

section core

variable {A B : Type*} (K L : Type*) [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Field K] [Field L] [Algebra A B] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L]

private def Rel (m : ℕ) (I J : Ideal B) : Prop :=
  ∃ (x y : B) (E F : Ideal B), x ≠ 0 ∧ y ≠ 0 ∧ E ≠ 0 ∧ F ≠ 0 ∧
    Algebra.norm K (algebraMap B L x) = Algebra.norm K (algebraMap B L y) ∧
    Ideal.span {x} * I * E ^ m = Ideal.span {y} * J * F ^ m

private theorem rel_mul {m : ℕ} {I J I' J' : Ideal B} (h : Rel K L m I J) (h' : Rel K L m I' J') :
    Rel K L m (I * I') (J * J') := by
  obtain ⟨x, y, E, F, hx, hy, hE, hF, hn, he⟩ := h
  obtain ⟨x', y', E', F', hx', hy', hE', hF', hn', he'⟩ := h'
  refine ⟨x * x', y * y', E * E', F * F', mul_ne_zero hx hx', mul_ne_zero hy hy',
    mul_ne_zero hE hE', mul_ne_zero hF hF', by simp only [map_mul, hn, hn'], ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
  calc _ = (Ideal.span {x} * I * E ^ m) * (Ideal.span {x'} * I' * E' ^ m) := by ring
    _ = _ := by rw [he, he']; ring

private theorem rel_prod {m : ℕ} (φ : Ideal B → Ideal B) (s : Multiset (Ideal B))
    (h : ∀ P ∈ s, Rel K L m P (φ P)) : Rel K L m s.prod (s.map φ).prod := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, 1, 1, 1, one_ne_zero, one_ne_zero, one_ne_zero, one_ne_zero, rfl, rfl⟩
  | cons a s ih =>
    simp only [Multiset.prod_cons, Multiset.map_cons]
    exact rel_mul K L (h a (Multiset.mem_cons_self a s))
      (ih fun P hP => h P (Multiset.mem_cons_of_mem hP))

private theorem rel_of_comap {m : ℕ} (hC : ∀ c : ClassGroup B, ∃ d, c = d ^ m) {P Q : Ideal B}
    (hP : P ≠ 0) (σ : Gal(L/K)) (h : Ideal.comap (galRestrict A K L B σ) P = Q) :
    Rel K L m P Q := by
  classical
  set τ := galRestrict A K L B σ with hτ
  let e : B ≃+* B := τ.symm.toRingEquiv
  have hτe : ∀ x, τ (e x) = x := fun x => τ.apply_symm_apply x
  have hnm : ∀ x, Algebra.norm K (algebraMap B L (e x)) = Algebra.norm K (algebraMap B L x) := by
    intro x
    conv_rhs => rw [← hτe x]
    rw [hτ, algebraMap_galRestrict_apply]
    exact (Algebra.norm_eq_of_algEquiv σ _).symm
  have hQ : Q = P.map e := by
    rw [← h]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_map_of_equiv]
    constructor
    · intro hx
      exact ⟨τ x, hx, τ.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hτe]
      exact hy
  have hP' : P ∈ nonZeroDivisors (Ideal B) := mem_nonZeroDivisors_of_ne_zero hP
  obtain ⟨d, hd⟩ := hC (ClassGroup.mk0 ⟨P, hP'⟩)
  obtain ⟨E0, rfl⟩ := ClassGroup.mk0_surjective d
  rw [← map_pow, ClassGroup.mk0_eq_mk0_iff] at hd
  obtain ⟨x, y, hx, hy, hxy⟩ := hd
  have hE : (E0 : Ideal B) ≠ 0 := nonZeroDivisors.coe_ne_zero E0
  simp only [SubmonoidClass.coe_pow] at hxy
  have h2 := congrArg (Ideal.map e) hxy
  simp only [Ideal.map_mul, Ideal.map_pow, Ideal.map_span, Set.image_singleton, ← hQ] at h2
  have hne : ∀ z : B, z ≠ 0 → e z ≠ 0 := fun z hz => (map_ne_zero_iff e e.injective).2 hz
  have heE : (E0 : Ideal B).map e ≠ 0 := by
    intro h0
    apply hE
    exact (Ideal.map_eq_bot_iff_of_injective e.injective).1 h0
  refine ⟨x * e y, y * e x, (E0 : Ideal B).map e, E0, mul_ne_zero hx (hne y hy),
    mul_ne_zero hy (hne x hx), heE, hE, by simp only [map_mul, hnm, mul_comm], ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
  calc _ = Ideal.span {e y} * (Ideal.span {x} * P) * ((E0 : Ideal B).map e) ^ m := by ring
    _ = Ideal.span {y} * (Ideal.span {e y} * ((E0 : Ideal B).map e) ^ m) * (E0 : Ideal B) ^ m := by
        rw [hxy]; ring
    _ = _ := by rw [← h2]; ring

end core

section core2

variable {A B : Type*} (K L : Type*) [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Field K] [Field L] [Algebra A B] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L] [Module.Finite A B] [Module.IsTorsionFree A B]
  [PerfectField (FractionRing A)]

private theorem inertia_one (hres : ∀ P : Ideal B, P.IsMaximal → ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ P)
    (P : Ideal B) [hP : P.IsMaximal] [(P.under A).IsMaximal] : P.inertiaDeg A = 1 := by
  letI : Field (A ⧸ P.under A) := Ideal.Quotient.field _
  have h1 : Module.finrank (A ⧸ P.under A) (B ⧸ P) = 1 := by
    refine (finrank_eq_one_iff_of_nonzero' (1 : B ⧸ P) one_ne_zero).2 fun w => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨a, ha⟩ := hres P hP b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Algebra.smul_def, mul_one]
    exact (Ideal.Quotient.eq.2 ha).symm
  rw [← h1]
  have hl : P.LiesOver (P.under A) := ⟨rfl⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal (P.under A) P]

open Classical in
private theorem core {m : ℕ} (hC : ∀ c : ClassGroup B, ∃ d, c = d ^ m)
    (hres : ∀ P : Ideal B, P.IsMaximal → ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ P)
    (g : B) (hg : g ≠ 0)
    (hdiv : ∀ p : Ideal A, m ∣ Multiset.count p (normalizedFactors (Ideal.span {Algebra.intNorm A B g}))) :
    ∃ D : Ideal B, Rel K L m (Ideal.span {g}) (D ^ m) := by
  have hI : Ideal.span {g} ≠ ⊥ := by simpa using hg
  set s := normalizedFactors (Ideal.span {g}) with hs
  have hsP : ∀ P ∈ s, P.IsPrime ∧ P ≠ 0 := fun P hP =>
    ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor P hP),
      (prime_of_normalized_factor P hP).ne_zero⟩
  have hsM : ∀ P ∈ s, P.IsMaximal := fun P hP =>
    (hsP P hP).1.isMaximal (hsP P hP).2
  let un : Ideal B → Ideal A := fun P => P.under A
  let S : Set (Ideal B) := {P | P.IsPrime ∧ P ≠ 0}
  let ch : Ideal A → Ideal B := Function.invFunOn un S
  have hunM : ∀ P ∈ s, (un P).IsMaximal ∧ un P ≠ 0 := fun P hP => by
    have := hsM P hP
    refine ⟨Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) P, fun h0 => (hsP P hP).2 ?_⟩
    exact Ideal.eq_bot_of_comap_eq_bot h0
  have hch : ∀ P ∈ s, ch (un P) ∈ S ∧ un (ch (un P)) = un P := fun P hP =>
    Function.invFunOn_pos ⟨P, hsP P hP, rfl⟩
  have hrel : ∀ P ∈ s, Rel K L m P (ch (un P)) := by
    intro P hP
    obtain ⟨⟨hQp, hQ0⟩, hQu⟩ := hch P hP
    have := (hsP P hP).1
    have h1 : P ∈ (un P).primesOver B := ⟨(hsP P hP).1, ⟨rfl⟩⟩
    have h2 : ch (un P) ∈ (un P).primesOver B := ⟨hQp, ⟨hQu.symm⟩⟩
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq A K L B h1 h2
    exact rel_of_comap K L hC (hsP P hP).2 σ hσ
  have hR := rel_prod K L (fun P => ch (un P)) s hrel
  rw [hs, Ideal.prod_normalizedFactors_eq_self hI, ← hs] at hR
  set t := s.map un with ht
  have hnorm : Ideal.span {Algebra.intNorm A B g} = t.prod := by
    rw [← Ideal.relNorm_singleton, ← Ideal.prod_normalizedFactors_eq_self hI, ← hs,
      map_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun P hP => ?_
    have := hsM P hP
    have := (hunM P hP).1
    have hl : P.LiesOver (P.under A) := ⟨rfl⟩
    rw [Ideal.relNorm_eq_pow_of_isMaximal P (P.under A), inertia_one hres P, pow_one]
  have hfac : normalizedFactors t.prod = t := by
    refine normalizedFactors_prod_of_prime fun p hp => ?_
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hp
    exact Ideal.prime_of_isPrime (hunM P hP).2 (hunM P hP).1.isPrime
  obtain ⟨T, hT⟩ := Multiset.exists_smul_of_dvd_count t (k := m) fun p _ => by
    have := hdiv p
    rwa [hnorm, hfac] at this
  refine ⟨(T.map ch).prod, ?_⟩
  have hm : s.map (fun P => ch (un P)) = m • T.map ch := by
    rw [← Multiset.map_nsmul, ← hT, ht, Multiset.map_map]
    rfl
  rwa [hm, Multiset.prod_nsmul] at hR

end core2

section fin

variable {B L : Type*} [CommRing B] [IsDedekindDomain B] [Field L] [Algebra B L]

private theorem principal_in (W : ValuationSubring L) (φ : B →+* W) (hφ : Function.Injective φ)
    (E : Ideal B) (hE : E ≠ 0) : ∃ w : W, w ≠ 0 ∧ E.map φ = Ideal.span {w} := by
  have hfg : (E.map φ).FG := Ideal.FG.map (IsNoetherian.noetherian E) φ
  obtain ⟨w, hw⟩ := (IsBezout.isPrincipal_of_FG _ hfg).principal
  refine ⟨w, ?_, by simpa using hw⟩
  rintro rfl
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE
  have h1 : φ b ∈ E.map φ := Ideal.mem_map_of_mem φ hb
  rw [hw] at h1
  simp only [Submodule.span_zero_singleton, Submodule.mem_bot] at h1
  exact hb0 (hφ (h1.trans (map_zero φ).symm))

private theorem val_of {m : ℕ} (hm : 0 < m) (hinj : Function.Injective (algebraMap B L))
    (W : ValuationSubring L) (hW : ∀ b : B, algebraMap B L b ∈ W) {a y : B} {D E F : Ideal B}
    (ha : a ≠ 0) (hy : y ≠ 0) (hE : E ≠ 0) (hF : F ≠ 0)
    (h : Ideal.span {a} * E ^ m = Ideal.span {y} * D ^ m * F ^ m) :
    ∃ c : L, c ≠ 0 ∧ W.valuation (algebraMap B L a / algebraMap B L y / c ^ m) = 1 := by
  let φ : B →+* W := (algebraMap B L).codRestrict W.toSubring hW
  have hcoe : ∀ b, ((φ b : W) : L) = algebraMap B L b := fun _ => rfl
  have hφ : Function.Injective φ := fun x y hxy => hinj (by rw [← hcoe, ← hcoe, hxy])
  have hD : D ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', mul_zero, zero_mul] at h
    exact mul_ne_zero (by simpa using ha) (pow_ne_zero m hE) h
  obtain ⟨e, he0, he⟩ := principal_in W φ hφ E hE
  obtain ⟨d, hd0, hd⟩ := principal_in W φ hφ D hD
  obtain ⟨f, hf0, hf⟩ := principal_in W φ hφ F hF
  have h2 := congrArg (Ideal.map φ) h
  simp only [Ideal.map_mul, Ideal.map_pow, Ideal.map_span, Set.image_singleton, he, hd, hf,
    Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton] at h2
  rw [Ideal.span_singleton_eq_span_singleton] at h2
  obtain ⟨u, hu⟩ := h2
  have hL := congrArg (fun w : W => (w : L)) hu
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, hcoe] at hL
  have he' : (e : L) ≠ 0 := by simpa using he0
  have hd' : (d : L) ≠ 0 := by simpa using hd0
  have hf' : (f : L) ≠ 0 := by simpa using hf0
  have hy' : algebraMap B L y ≠ 0 := fun h0 => hy (hinj (h0.trans (map_zero _).symm))
  refine ⟨d * f / e, div_ne_zero (mul_ne_zero hd' hf') he', ?_⟩
  have hz : algebraMap B L a / algebraMap B L y / ((d : L) * f / e) ^ m * ((u : W) : L) = 1 := by
    rw [div_pow, mul_pow]
    field_simp
    rw [hL]
  have h3 := congrArg W.valuation hz
  rw [map_mul, W.valuation_unit u, mul_one, map_one] at h3
  exact h3

end fin

section abs

open IsDedekindDomain

variable {A B : Type*} (K L : Type*) [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Field K] [Field L] [Algebra A B] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L] [Module.Finite A B] [Module.IsTorsionFree A B]
  [PerfectField (FractionRing A)] [IsFractionRing B L]

open Classical in
private theorem dvd_count {m : ℕ} (n : A) (hn : n ≠ 0) (h : ∀ v : HeightOneSpectrum A, ∃ z : K, z ≠ 0 ∧
      v.valuation K (algebraMap A K n) = (v.valuation K z) ^ m) (p : Ideal A) :
    m ∣ Multiset.count p (normalizedFactors (Ideal.span {n})) := by
  by_cases hp : p ∈ normalizedFactors (Ideal.span {n})
  · have hpr := prime_of_normalized_factor p hp
    let v : HeightOneSpectrum A := ⟨p, Ideal.isPrime_of_prime hpr, hpr.ne_zero⟩
    obtain ⟨z, hz0, hz⟩ := h v
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hn,
      Ideal.count_associates_factors_eq (by simpa using hn) v.isPrime v.ne_bot] at hz
    have h2 := congrArg WithZero.log hz
    rw [WithZero.log_exp, WithZero.log_pow] at h2
    have h3 : (m : ℤ) ∣ (Multiset.count p (normalizedFactors (Ideal.span {n})) : ℤ) :=
      ⟨-(v.valuation K z).log, by
        have : -(Multiset.count p (normalizedFactors (Ideal.span {n})) : ℤ) = m * (v.valuation K z).log := by
          simpa using h2
        linarith⟩
    exact Int.natCast_dvd_natCast.1 h3
  · rw [Multiset.count_eq_zero_of_notMem hp]
    exact dvd_zero m

private theorem abs_fin {m : ℕ} (hm : 0 < m) (hC : ∀ c : ClassGroup B, ∃ d, c = d ^ m)
    (hres : ∀ P : Ideal B, P.IsMaximal → ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ P)
    (f : K) (hf0 : f ≠ 0) (g0 : L) (hg0 : Algebra.norm K g0 = f)
    (hf : ∀ v : HeightOneSpectrum A, ∃ c : K, c ≠ 0 ∧ v.valuation K (f / c ^ m) = 1) :
    ∃ f' : L, f' ≠ 0 ∧ Algebra.norm K f' = f ∧ ∀ W : ValuationSubring L,
      (∀ b : B, algebraMap B L b ∈ W) → ∃ c : L, c ≠ 0 ∧ W.valuation (f' / c ^ m) = 1 := by
  classical
  have hinj : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hg00 : g0 ≠ 0 := Algebra.norm_ne_zero_iff.1 (hg0 ▸ hf0)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) g0
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : algebraMap B L b ≠ 0 := fun h0 => hb0 (hinj (h0.trans (map_zero _).symm))
  have haL : algebraMap B L a ≠ 0 := fun h0 => hg00 (by rw [h0, zero_div])
  have ha0 : a ≠ 0 := fun h0 => haL (by rw [h0, map_zero])
  set g0 := algebraMap B L a / algebraMap B L b with hg0d
  set g := a * b ^ (m - 1) with hg
  have hg_ne : g ≠ 0 := mul_ne_zero ha0 (pow_ne_zero _ hb0)
  have hgL : algebraMap B L g = g0 * algebraMap B L b ^ m := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hg, hg0d, map_mul, map_pow, Nat.add_sub_cancel]
    field_simp
    ring
  set n := Algebra.intNorm A B g with hn
  have hnK : algebraMap A K n = f * Algebra.norm K (algebraMap B L b) ^ m := by
    rw [hn, Algebra.algebraMap_intNorm (L := L), hgL, map_mul, map_pow, hg0]
  have hNb : Algebra.norm K (algebraMap B L b) ≠ 0 := Algebra.norm_ne_zero_iff.2 hbL
  have hn0 : n ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hnK
    exact mul_ne_zero hf0 (pow_ne_zero m hNb) hnK.symm
  have hdiv := dvd_count K (m := m) n hn0 (fun v => by
    obtain ⟨c, hc0, hc⟩ := hf v
    refine ⟨c * Algebra.norm K (algebraMap B L b), mul_ne_zero hc0 hNb, ?_⟩
    have hc' : v.valuation K f = v.valuation K c ^ m := by
      rw [map_div₀, map_pow] at hc
      exact (div_eq_one_iff_eq (pow_ne_zero m ((Valuation.ne_zero_iff _).2 hc0))).1 hc
    rw [hnK, map_mul, map_mul, map_pow, hc', mul_pow])
  obtain ⟨D, x, y, E, F, hx, hy, hE, hF, hxy, hR⟩ := core K L hC hres g hg_ne hdiv
  have hxL : algebraMap B L x ≠ 0 := fun h0 => hx (hinj (h0.trans (map_zero _).symm))
  have hyL : algebraMap B L y ≠ 0 := fun h0 => hy (hinj (h0.trans (map_zero _).symm))
  refine ⟨g0 * algebraMap B L x / algebraMap B L y, div_ne_zero (mul_ne_zero hg00 hxL) hyL, ?_, ?_⟩
  · have hNy : Algebra.norm K (algebraMap B L y) ≠ 0 := Algebra.norm_ne_zero_iff.2 hyL
    apply mul_right_cancel₀ hNy
    rw [← map_mul, div_mul_cancel₀ _ hyL, map_mul, hg0, hxy]
  · intro W hW
    rw [Ideal.span_singleton_mul_span_singleton] at hR
    obtain ⟨c, hc0, hc⟩ := val_of hm hinj W hW (mul_ne_zero hx hg_ne) hy hE hF hR
    refine ⟨c / algebraMap B L b, div_ne_zero hc0 hbL, ?_⟩
    rw [← hc, map_mul, hgL, div_pow]
    congr 1
    field_simp

end abs

private theorem mem_of_int {R L : Type*} [CommRing R] [Field L] [Algebra R L] (W : ValuationSubring L)
    (hW : ∀ p : R, algebraMap R L p ∈ W) {x : L} (hx : IsIntegral R x) : x ∈ W := by
  let ψ : R →+* W := (algebraMap R L).codRestrict W.toSubring hW
  obtain ⟨P, hP, h0⟩ := hx
  have h1 : IsIntegral W x := ⟨P.map ψ, hP.map ψ, by rw [eval₂_map]; exact h0⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  exact y.2

private theorem res_of (k B : Type*) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (P : Ideal B) (hP : P.IsMaximal) (b : B) :
    ∃ c : k, b - algebraMap k B c ∈ P := by
  letI := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := B ⧸ P)).2
    (Ideal.Quotient.mk P b)
  exact ⟨c, Ideal.Quotient.eq.1 hc.symm⟩

end UpperTheory.Kd.K4.Ns

open UpperTheory.Kd.K4.Ns in
theorem UpperTheory.Kd.K4.nsAbs :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (K' : Type) [Field K'] [Algebra K K'] [Algebra k[X] K'] [IsScalarTower k[X] K K'] [FiniteDimensional K K'] [IsGalois K K'] (m : ℕ) (f : K), 0 < m → f ≠ 0 →
      (∀ B : ValuationSubring K, (∀ p : k[X], algebraMap k[X] K p ∈ B) → ∃ c : K, c ≠ 0 ∧ B.valuation (f / c ^ m) = 1) →
      ∃ f' : K', f' ≠ 0 ∧ Algebra.norm K f' = f ∧
        ∀ B : ValuationSubring K', (∀ p : k[X], algebraMap k[X] K' p ∈ B) → ∃ c : K', c ≠ 0 ∧ B.valuation (f' / c ^ m) = 1 := by
  intro k K _ _ _ _ _ _ _ _ K' _ _ _ _ _ _ m f hm hf0 hf
  letI : Algebra (RatFunc k) K' := ((algebraMap K K').comp (algebraMap (RatFunc k) K)).toAlgebra
  haveI : IsScalarTower (RatFunc k) K K' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k[X] (RatFunc k) K' := .of_algebraMap_eq fun p => by
    rw [IsScalarTower.algebraMap_apply k[X] K K', IsScalarTower.algebraMap_apply k[X] (RatFunc k) K]
    rfl
  haveI : FiniteDimensional (RatFunc k) K' := .trans (RatFunc k) K K'
  haveI : Algebra.IsSeparable (RatFunc k) K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable (RatFunc k) K' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  haveI : Module.IsTorsionFree k[X] K' := .trans_faithfulSMul k[X] (RatFunc k) K'
  let A := FunctionField.ringOfIntegers k K
  let B := FunctionField.ringOfIntegers k K'
  haveI : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) K _
  haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) K' _
  haveI : IsFractionRing A K := IsIntegralClosure.isFractionRing_of_finite_extension k[X] (RatFunc k) K _
  haveI : IsFractionRing B K' := IsIntegralClosure.isFractionRing_of_finite_extension k[X] (RatFunc k) K' _
  have hAB : ∀ a : A, algebraMap K K' (algebraMap A K a) ∈ B := fun a =>
    IsIntegral.algebraMap (R := k[X]) (A := K) (B := K') a.2
  letI : Algebra A B := (((algebraMap K K').comp (algebraMap A K)).codRestrict B hAB).toAlgebra
  haveI : IsScalarTower A K K' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A B K' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k[X] A K' := .of_algebraMap_eq fun p =>
    IsScalarTower.algebraMap_apply k[X] K K' p
  haveI : Algebra.IsIntegral k[X] A := inferInstanceAs (Algebra.IsIntegral k[X] (integralClosure k[X] K))
  have hinjB : Function.Injective (algebraMap B K') := IsFractionRing.injective B K'
  haveI : IsIntegralClosure B A K' := ⟨hinjB, fun {x} =>
    ⟨fun hx => ⟨⟨x, isIntegral_trans (R := k[X]) (A := A) x hx⟩, rfl⟩, by
      rintro ⟨b, rfl⟩
      exact IsIntegral.tower_top (R := k[X]) (A := A) b.2⟩⟩
  haveI : Module.Finite A B := IsIntegralClosure.finite A K K' B
  have hinjAB : Function.Injective (algebraMap A B) := fun x y hxy => by
    apply IsFractionRing.injective A K
    apply (algebraMap K K').injective
    exact congrArg (fun b : B => (b : K')) hxy
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinjAB
  haveI : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.2 hinjAB
  haveI : CharZero (FractionRing A) :=
    charZero_of_injective_ringHom (f := ((algebraMap A (FractionRing A)).comp (algebraMap k[X] A)).comp
      (algebraMap k k[X])) (RingHom.injective _)
  letI : Algebra k B := ((algebraMap k[X] B).comp (algebraMap k k[X])).toAlgebra
  haveI : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite k[X] B := IsIntegralClosure.finite k[X] (RatFunc k) K' _
  haveI : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  have hres : ∀ P : Ideal B, P.IsMaximal → ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ P := by
    intro P hP b
    obtain ⟨c, hc⟩ := res_of k B P hP b
    refine ⟨algebraMap k[X] A (algebraMap k k[X] c), ?_⟩
    convert hc using 2
    exact Subtype.ext (IsScalarTower.algebraMap_apply k[X] K K' _).symm
  have hfv : ∀ v : IsDedekindDomain.HeightOneSpectrum A, ∃ c : K, c ≠ 0 ∧ v.valuation K (f / c ^ m) = 1 := by
    intro v
    obtain ⟨c, hc0, hc⟩ := hf (v.valuation K).valuationSubring fun p =>
      (Valuation.mem_valuationSubring_iff _ _).2 (v.valuation_le_one (algebraMap k[X] A p))
    exact ⟨c, hc0, ((v.valuation K).isEquiv_valuation_valuationSubring.eq_one_iff_eq_one).2 hc⟩
  obtain ⟨g0, hg0⟩ := GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass K K' (GlobalTheory.T.tsen_theorem k K) f hf0
  obtain ⟨f', h0, h1, h2⟩ := abs_fin (A := A) (B := B) K K' hm (fun c => GlobalTheory.T.classGroup_affineCurve_divisible_charZero k K' m hm c)
    hres f hf0 g0 hg0 hfv
  exact ⟨f', h0, h1, fun W hW => h2 W fun b => mem_of_int W hW b.2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.CountSpanEqZero
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem valuation_eq_exp_neg_count_spanSingleton {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (v : IsDedekindDomain.HeightOneSpectrum R) {x : L}
    (hx : x ≠ 0) :
    v.valuation L x = WithZero.exp
      (-FractionalIdeal.count L v (FractionalIdeal.spanSingleton (nonZeroDivisors R) x)) := by
  classical
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hs : (s : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors R) (IsLocalization.mk' L a s) =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) ((algebraMap R L) (s : R))⁻¹ *
        ↑(Ideal.span {a}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined L v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    hspan, IsDedekindDomain.HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg ha,
    v.intValuation_if_neg hs, ← WithZero.exp_sub]
  congr 1
  ring

private theorem valuation_eq_one_of_valuationSubring_eq_one {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (v : IsDedekindDomain.HeightOneSpectrum R) {y : L}
    (hy : ((v.valuation L).valuationSubring).valuation y = 1) : v.valuation L y = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have h1 : y ∈ (v.valuation L).valuationSubring :=
    (ValuationSubring.valuation_le_one_iff _ y).mp hy.le
  have h2 : y⁻¹ ∈ (v.valuation L).valuationSubring :=
    (ValuationSubring.valuation_le_one_iff _ _).mp (by rw [map_inv₀, hy, inv_one])
  rw [Valuation.mem_valuationSubring_iff] at h1 h2
  rw [map_inv₀] at h2
  have hv0 : v.valuation L y ≠ 0 := by simpa using hy0
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr hv0)).mp h2)

private theorem ringOfIntegers_mem_of_polynomial_mem (k K : Type) [Field k] [Field K] [Algebra k[X] K]
    [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K] (B : ValuationSubring K)
    (hB : ∀ p : k[X], algebraMap k[X] K p ∈ B) (x : FunctionField.ringOfIntegers k K) :
    (x : K) ∈ B := by
  obtain ⟨p, hpm, hp⟩ := x.2
  let φ : k[X] →+* B := (algebraMap k[X] K).codRestrict B hB
  have hc : (algebraMap B K).comp φ = algebraMap k[X] K := RingHom.ext fun _ => rfl
  have hint : IsIntegral B (x : K) := by
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hc]
    exact hp
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

private theorem exists_mul_spanSingleton_eq_of_classGroup_mk_eq {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (I J : (FractionalIdeal (nonZeroDivisors R) L)ˣ)
    (h : ClassGroup.mk L I = ClassGroup.mk L J) :
    ∃ x : L, x ≠ 0 ∧
      (I : FractionalIdeal (nonZeroDivisors R) L) * FractionalIdeal.spanSingleton (nonZeroDivisors R) x = J := by
  have h2 := congrArg (ClassGroup.equiv L) h
  rw [ClassGroup.equiv_mk, ClassGroup.equiv_mk, QuotientGroup.mk'_eq_mk'] at h2
  obtain ⟨z, ⟨x, rfl⟩, hz⟩ := h2
  refine ⟨x, x.ne_zero, ?_⟩
  have h3 := congrArg Units.val hz
  simpa [FractionalIdeal.canonicalEquiv_self] using h3

theorem UpperTheory.Kd.K4.cdAbs :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (m m' : ℕ) (f : K), 0 < m → 0 < m' → f ≠ 0 →
      (∀ B : ValuationSubring K, (∀ p : k[X], algebraMap k[X] K p ∈ B) → ∃ c : K, c ≠ 0 ∧ B.valuation (f / c ^ m) = 1) →
      ∃ h : K, h ≠ 0 ∧ ∀ B : ValuationSubring K, (∀ p : k[X], algebraMap k[X] K p ∈ B) → ∃ c : K, c ≠ 0 ∧ B.valuation (f / h ^ m / c ^ (m * m')) = 1 := by
  intro k K _ _ _ _ _ _ _ _ m m' f hm hm' hf hloc
  classical
  have hF : FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf
  have hdiv : ∀ v : IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k K),
      (m : ℤ) ∣ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f) := by
    intro v
    obtain ⟨c, hc, hcv⟩ := hloc ((v.valuation K).valuationSubring) (fun p => by
      rw [Valuation.mem_valuationSubring_iff,
        IsScalarTower.algebraMap_apply k[X] (FunctionField.ringOfIntegers k K) K]
      exact v.valuation_le_one _)
    have h1 := valuation_eq_one_of_valuationSubring_eq_one v hcv
    have hc0 : v.valuation K c ^ m ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hc)
    rw [map_div₀, map_pow, div_eq_one_iff_eq hc0, valuation_eq_exp_neg_count_spanSingleton v hf, valuation_eq_exp_neg_count_spanSingleton v hc,
      ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h1
    exact ⟨FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ c), by linarith⟩
  obtain ⟨I, hIdef⟩ : ∃ I : FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K,
      I = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k K),
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K) ^
          (FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f) / m) :=
    ⟨_, rfl⟩
  have he : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k K) in
      Filter.cofinite, FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f) / m = 0 :=
    (FractionalIdeal.finite_factors _).mono fun v hv => by rw [hv, Int.zero_ediv]
  have hI0 : I ≠ 0 := by
    rw [hIdef]
    refine finprod_induction (fun J => J ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) ?_
    intro v
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have hIm : I ^ m = FractionalIdeal.spanSingleton _ f := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (pow_ne_zero m hI0)]
    conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hF]
    refine finprod_congr fun v => ?_
    rw [FractionalIdeal.count_pow, hIdef, FractionalIdeal.count_finprod K v _ he,
      Int.mul_ediv_cancel' (hdiv v)]
  obtain ⟨d, hd⟩ := GlobalTheory.T.classGroup_affineCurve_divisible_charZero k K m' hm' (ClassGroup.mk K (Units.mk0 I hI0))
  obtain ⟨Ju, rfl⟩ : ∃ Ju : (FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K)ˣ,
      ClassGroup.mk K Ju = d :=
    ClassGroup.induction K (P := fun d => ∃ Ju, ClassGroup.mk K Ju = d) (fun J => ⟨J, rfl⟩) d
  rw [← map_pow] at hd
  obtain ⟨x, hx, hxJ⟩ := exists_mul_spanSingleton_eq_of_classGroup_mk_eq _ _ hd
  rw [Units.val_mk0, Units.val_pow_eq_pow_val] at hxJ
  refine ⟨x⁻¹, inv_ne_zero hx, fun B hB => ?_⟩
  have hJ : ((Ju : FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K) :
      Submodule (FunctionField.ringOfIntegers k K) K) ^ (m * m') =
        (FunctionField.ringOfIntegers k K) ∙ (f / x⁻¹ ^ m) := by
    rw [← FractionalIdeal.coe_pow, ← FractionalIdeal.coe_spanSingleton (nonZeroDivisors _), pow_mul',
      ← hxJ, mul_pow, hIm, FractionalIdeal.spanSingleton_pow,
      FractionalIdeal.spanSingleton_mul_spanSingleton, inv_pow, div_inv_eq_mul]
  have hw : f / x⁻¹ ^ m ≠ 0 := div_ne_zero hf (pow_ne_zero _ (inv_ne_zero hx))
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span K K (FunctionField.ringOfIntegers k K) B _ (m * m')
    (Nat.mul_pos hm hm') (fun r => ringOfIntegers_mem_of_polynomial_mem k K B hB r) (f / x⁻¹ ^ m) hw hJ
  exact ⟨c, hc, by simpa using hcv⟩
end

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 40000

private theorem val_one_iff {K : Type} [Field K] (A : ValuationSubring K) (x : K) :
    A.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ A ∧ x⁻¹ ∈ A := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl
      simp at h
    · rw [← A.valuation_le_one_iff, h]
    · rw [← A.valuation_le_one_iff, map_inv₀, h, inv_one]
  · rintro ⟨h0, h1, h2⟩
    rw [← A.valuation_le_one_iff] at h1 h2
    rw [map_inv₀] at h2
    have h3 : A.valuation x ≠ 0 := by simpa using h0
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h3)).1 h2)

private theorem val_comap {K : Type} [Field K] (F : Subfield K) (W : ValuationSubring K) (x : F) :
    (W.comap F.subtype).valuation x = 1 ↔ W.valuation (x : K) = 1 := by
  rw [val_one_iff, val_one_iff]
  simp [ValuationSubring.mem_comap]

private theorem exists_ext {K : Type} [Field K] (F : Subfield K) (B : ValuationSubring F) :
    ∃ W : ValuationSubring K, W.comap F.subtype = B := by
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (F.subtype.comp B.subtype)
  refine ⟨W, ?_⟩
  ext x
  rw [ValuationSubring.mem_comap]
  refine ⟨fun hx => ?_, fun hx => hW ⟨x, hx⟩⟩
  by_contra hn
  have hi : x⁻¹ ∈ B := (B.mem_or_inv_mem x).resolve_left hn
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hn B.zero_mem
  have hu : IsUnit ((F.subtype.comp B.subtype).codRestrict W.toSubring hW ⟨x⁻¹, hi⟩) := by
    refine IsUnit.of_mul_eq_one ⟨F.subtype x, hx⟩ (Subtype.ext ?_)
    show F.subtype x⁻¹ * F.subtype x = 1
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  obtain ⟨y, hy⟩ := (hloc.map_nonunit _ hu).exists_right_inv
  have hy' : x⁻¹ * (y : F) = 1 := congrArg Subtype.val hy
  have : (y : F) = x := by
    field_simp at hy'
    exact hy'
  exact hn (this ▸ y.2)

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem over_iff (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (W : ValuationSubring X.K) :
    X.OverY W ↔ ∀ p : Polynomial Ω, jPoly X H p ∈ W.comap (lev X H).subtype := by
  constructor
  · rintro ⟨h1, h2⟩ p
    rw [ValuationSubring.mem_comap]
    show ((jPoly X H p : lev X H) : X.K) ∈ W
    rw [coe_jPoly]
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add (f := _)]; exact W.add_mem _ _ hp hq
    | monomial n c =>
      rw [Polynomial.aeval_monomial]
      exact W.mul_mem _ _ (h1 c) (pow_mem h2 n)
  · intro h
    have h' : ∀ p : Polynomial Ω, Polynomial.aeval X.jK p ∈ W := fun p => by
      rw [← coe_jPoly X H]
      exact h p
    exact ⟨fun c => by simpa using h' (C c), by simpa using h' Polynomial.X⟩

private theorem lun_iff (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (m : ℕ) (f : lev X H) :
    (∀ W : ValuationSubring X.K, X.OverY W → ∃ c ∈ lev X H, c ≠ 0 ∧ W.valuation ((f : X.K) / c ^ m) = 1) ↔
      ∀ B : ValuationSubring (lev X H), (∀ p : Polynomial Ω, jPoly X H p ∈ B) → ∃ c : lev X H, c ≠ 0 ∧ B.valuation (f / c ^ m) = 1 := by
  constructor
  · intro h B hB
    obtain ⟨W, rfl⟩ := exists_ext (lev X H) B
    obtain ⟨c, hc, hc0, hv⟩ := h W ((over_iff X H W).2 hB)
    refine ⟨⟨c, hc⟩, fun e => hc0 (congrArg Subtype.val e), ?_⟩
    rw [val_comap]
    simpa using hv
  · intro h W hW
    obtain ⟨c, hc0, hv⟩ := h _ ((over_iff X H W).1 hW)
    rw [val_comap] at hv
    exact ⟨c, c.2, fun e => hc0 (Subtype.ext e), by simpa using hv⟩

private theorem lev_anti (X : Tower Ω ε) {H H' : Subgroup SL(2, ℤ)} (h : H' ≤ H) : lev X H ≤ lev X H' := fun f hf =>
  (mem_lev_iff X H' f).2 fun γ hγ => (mem_lev_iff X H f).1 hf γ (h hγ)

end

private theorem fd_tower (k K K' : Type) [Field k] [Field K] [Field K'] [Algebra (Polynomial k) K] [Algebra (RatFunc k) K]
    [IsScalarTower (Polynomial k) (RatFunc k) K] [Algebra (Polynomial k) K'] [Algebra (RatFunc k) K']
    [IsScalarTower (Polynomial k) (RatFunc k) K'] [Algebra K K'] [IsScalarTower (Polynomial k) K K']
    [FiniteDimensional (RatFunc k) K'] : FiniteDimensional K K' := by
  have e : algebraMap (RatFunc k) K' = (algebraMap K K').comp (algebraMap (RatFunc k) K) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial k)) (RingHom.ext fun p => ?_)
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) K', ← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) K,
      ← IsScalarTower.algebraMap_apply (Polynomial k) K K']
  haveI : IsScalarTower (RatFunc k) K K' := IsScalarTower.of_algebraMap_eq' e
  exact Module.Finite.of_restrictScalars_finite (RatFunc k) _ _

section
variable {L Γ : Type} [Field L] [Group Γ] (a : Γ → L ≃+* L) (a1 : ∀ f, a 1 f = f)
  (am : ∀ x y f, a (x * y) f = a y (a x f)) {H H' : Subgroup Γ}
  (hn : ∀ γ ∈ H, ∀ δ ∈ H', γ * δ * γ⁻¹ ∈ H') {F F' : Subfield L}
  (hF : ∀ f, f ∈ F ↔ ∀ γ ∈ H, a γ f = f) (hF' : ∀ f, f ∈ F' ↔ ∀ γ ∈ H', a γ f = f)

include a1 am hn hF hF' in
private theorem a_mem {γ : Γ} (hγ : γ ∈ H) {f : L} (hf : f ∈ F') : a γ f ∈ F' := by
  rw [hF'] at hf ⊢
  intro δ hδ
  have e : γ * δ = (γ * δ * γ⁻¹) * γ := by group
  rw [← am, e, am, hf _ (hn γ hγ δ hδ)]

include a1 am hn hF hF' in
private theorem exists_aut' [Algebra F F'] (ha : ∀ x : F, ((algebraMap F F' x : F') : L) = x) {γ : Γ} (hγ : γ ∈ H) :
    ∃ τ : F' ≃ₐ[F] F', ∀ x : F', ((τ x : F') : L) = a γ x := by
  refine ⟨{ toFun := fun x => ⟨a γ x, a_mem a a1 am hn hF hF' hγ x.2⟩
            invFun := fun x => ⟨a γ⁻¹ x, a_mem a a1 am hn hF hF' (H.inv_mem hγ) x.2⟩
            left_inv := fun x => Subtype.ext ?_
            right_inv := fun x => Subtype.ext ?_
            map_mul' := fun x y => Subtype.ext ?_
            map_add' := fun x y => Subtype.ext ?_
            commutes' := fun x => Subtype.ext ?_ }, fun x => rfl⟩
  · show a γ⁻¹ (a γ x) = x
    rw [← am, mul_inv_cancel, a1]
  · show a γ (a γ⁻¹ x) = x
    rw [← am, inv_mul_cancel, a1]
  · exact map_mul (a γ) (x : L) y
  · exact map_add (a γ) (x : L) y
  · show a γ _ = _
    rw [ha]
    exact (hF _).1 x.2 γ hγ

include a1 am hn hF hF' in
private theorem gal_surj' [Algebra F F'] (ha : ∀ x : F, ((algebraMap F F' x : F') : L) = x) [FiniteDimensional F F'] :
    IsGalois F F' ∧ ∀ τ : F' ≃ₐ[F] F', ∃ γ ∈ H, ∀ x : F', ((τ x : F') : L) = a γ x := by
  let S : Subgroup (F' ≃ₐ[F] F') :=
    { carrier := {τ | ∃ γ ∈ H, ∀ x : F', ((τ x : F') : L) = a γ x}
      one_mem' := ⟨1, H.one_mem, fun x => (a1 _).symm⟩
      mul_mem' := by
        rintro σ τ ⟨p, hpH, hσ⟩ ⟨q, hqH, hτ⟩
        refine ⟨q * p, H.mul_mem hqH hpH, fun x => ?_⟩
        rw [am, ← hτ, ← hσ]
        rfl
      inv_mem' := by
        rintro σ ⟨p, hpH, hσ⟩
        refine ⟨p⁻¹, H.inv_mem hpH, fun x => ?_⟩
        have e : (x : L) = a p (σ⁻¹ x : F') := by
          rw [← hσ]
          exact congrArg Subtype.val (σ.apply_symm_apply x).symm
        rw [e, ← am, mul_inv_cancel, a1] }
  have hS : IntermediateField.fixedField S = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxH : (x : L) ∈ F := (hF _).2 fun γ hγ => by
      obtain ⟨τ, hτ⟩ := exists_aut' a a1 am hn hF hF' ha hγ
      rw [← hτ, hx τ ⟨γ, hγ, hτ⟩]
    exact IntermediateField.mem_bot.2 ⟨⟨x, hxH⟩, Subtype.ext (ha _)⟩
  have hT : S = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField S, hS, IntermediateField.fixingSubgroup_bot]
  refine ⟨IsGalois.of_fixedField_eq_bot _ _ (hT ▸ hS), fun τ => ?_⟩
  have : τ ∈ S := hT ▸ Subgroup.mem_top τ
  exact this

include a1 am hn hF hF' in
private theorem prod_eq_norm [Algebra F F'] (ha : ∀ x : F, ((algebraMap F F' x : F') : L) = x) [FiniteDimensional F F']
    [IsGalois F F'] (faith : ∀ γ ∈ H, (∀ f ∈ F', a γ f = f) → γ ∈ H') {ι : Type} [Fintype ι] (δ : ι → Γ)
    (hδ1 : ∀ i, δ i ∈ H) (hδ2 : ∀ x ∈ H, ∃! i, x * (δ i)⁻¹ ∈ H') (f' : F') :
    ∏ i, a (δ i) (f' : L) = ((Algebra.norm F f' : F) : L) := by
  classical
  obtain ⟨-, hsurj⟩ := gal_surj' a a1 am hn hF hF' ha
  choose σ hσ using fun i => exists_aut' a a1 am hn hF hF' ha (hδ1 i)
  have hbij : Function.Bijective σ := by
    constructor
    · intro i j hij
      have hfix : ∀ x ∈ F', a (δ i * (δ j)⁻¹) x = x := fun x hx => by
        rw [am, ← hσ i ⟨x, hx⟩, hij, hσ j ⟨x, hx⟩, ← am, mul_inv_cancel, a1]
      have hmem : δ i * (δ j)⁻¹ ∈ H' := faith _ (H.mul_mem (hδ1 i) (H.inv_mem (hδ1 j))) hfix
      exact (hδ2 (δ i) (hδ1 i)).unique (by rw [mul_inv_cancel]; exact H'.one_mem) hmem
    · intro τ
      obtain ⟨γ, hγ, hτ⟩ := hsurj τ
      obtain ⟨i, hi, -⟩ := hδ2 γ hγ
      refine ⟨i, AlgEquiv.ext fun x => Subtype.ext ?_⟩
      have e : γ = γ * (δ i)⁻¹ * δ i := by group
      rw [hσ, hτ, e, am, (hF' _).1 x.2 _ hi]
  have h1 := Algebra.norm_eq_prod_automorphisms F f'
  rw [← hbij.prod_comp (fun τ => τ f')] at h1
  have h2 := congrArg (fun y : F' => (y : L)) h1
  change F'.subtype (algebraMap F F' (Algebra.norm F f')) =
    F'.subtype (∏ i, σ i f') at h2
  rw [map_prod] at h2
  change ((algebraMap F F' (Algebra.norm F f') : F') : L) =
    ∏ i, ((σ i f' : F') : L) at h2
  simpa only [ha, hσ] using h2.symm
end

private theorem abs_step {k L Γ : Type} [Field k] [IsAlgClosed k] [CharZero k] [Field L] [Group Γ] (a : Γ → L ≃+* L)
    (a1 : ∀ f, a 1 f = f) (am : ∀ x y f, a (x * y) f = a y (a x f)) {H H' : Subgroup Γ}
    (hn : ∀ γ ∈ H, ∀ δ ∈ H', γ * δ * γ⁻¹ ∈ H') {F F' : Subfield L} (hle : F ≤ F')
    (hF : ∀ f, f ∈ F ↔ ∀ γ ∈ H, a γ f = f) (hF' : ∀ f, f ∈ F' ↔ ∀ γ ∈ H', a γ f = f)
    [Algebra (Polynomial k) F] [Algebra (RatFunc k) F] [IsScalarTower (Polynomial k) (RatFunc k) F]
    [FiniteDimensional (RatFunc k) F] [Algebra (Polynomial k) F'] [Algebra (RatFunc k) F']
    [IsScalarTower (Polynomial k) (RatFunc k) F'] [FiniteDimensional (RatFunc k) F']
    (hc : ∀ p : Polynomial k, ((algebraMap (Polynomial k) F p : F) : L) = (algebraMap (Polynomial k) F' p : F'))
    (faith : ∀ γ ∈ H, (∀ f ∈ F', a γ f = f) → γ ∈ H') {ι : Type} [Fintype ι] (δ : ι → Γ)
    (hδ1 : ∀ i, δ i ∈ H) (hδ2 : ∀ x ∈ H, ∃! i, x * (δ i)⁻¹ ∈ H') (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (f : F)
    (hf0 : f ≠ 0)
    (hf : ∀ B : ValuationSubring F, (∀ p : Polynomial k, algebraMap (Polynomial k) F p ∈ B) →
      ∃ c : F, c ≠ 0 ∧ B.valuation (f / c ^ m) = 1) :
    ∃ f' : F', f' ≠ 0 ∧ (∀ B : ValuationSubring F', (∀ p : Polynomial k, algebraMap (Polynomial k) F' p ∈ B) →
      ∃ c : F', c ≠ 0 ∧ B.valuation (f' / c ^ (m * m')) = 1) ∧
      ∃ h : L, h ≠ 0 ∧ ∏ i, a (δ i) (f' : L) = (f : L) * h ^ m := by
  letI : Algebra F F' := (Subfield.inclusion hle).toAlgebra
  have ha : ∀ x : F, ((algebraMap F F' x : F') : L) = x := fun _ => rfl
  haveI : IsScalarTower (Polynomial k) F F' := IsScalarTower.of_algebraMap_eq fun p => Subtype.ext <| by
    rw [ha]
    exact (hc p).symm
  haveI : FiniteDimensional F F' := fd_tower k F F'
  haveI := (gal_surj' a a1 am hn hF hF' ha).1
  obtain ⟨h, hh0, hh⟩ := UpperTheory.Kd.K4.cdAbs k F m m' f hm hm' hf0 hf
  obtain ⟨f', hf'0, hN, hf'⟩ := UpperTheory.Kd.K4.nsAbs k F F' (m * m') (f / h ^ m) (Nat.mul_pos hm hm')
    (div_ne_zero hf0 (pow_ne_zero _ hh0)) hh
  refine ⟨f', hf'0, hf', (h : L)⁻¹, inv_ne_zero fun e => hh0 (Subtype.ext e), ?_⟩
  rw [prod_eq_norm a a1 am hn hF hF' ha faith δ hδ1 hδ2 f', hN, inv_pow, ← div_eq_mul_inv]
  simp

theorem UpperTheory.Kd.K4.step :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (H H' : Subgroup SL(2, ℤ)) (M m m' : ℕ), 0 < M → 0 < m → 0 < m' → CongruenceSubgroup.Gamma M ≤ H' → H' ≤ H → -1 ∉ H →
      (∀ γ ∈ H, ∀ δ ∈ H', γ * δ * γ⁻¹ ∈ H') → ∀ (ι : Type) [Fintype ι] (δ : ι → SL(2, ℤ)), IsTr H' H δ → ∀ f : X.K, LUnH X H m f →
      ∃ f' : X.K, LUnH X H' (m * m') f' ∧ ∃ h : X.K, h ≠ 0 ∧ ∏ i, X.sl (ofSL (δ i)) f' = f * h ^ m := by
  intro Ω _ _ _ ε X H H' M m m' hM hm hm' hΓ hle hneg hn ι _ δ hδ f hf
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨hf0, hfH, hfW⟩ := hf
  have hF0 : (⟨f, hfH⟩ : lev X H) ≠ 0 := fun e => hf0 (congrArg Subtype.val e)
  have hfaith : ∀ γ ∈ H, (∀ g ∈ lev X H', X.sl (ofSL γ) g = g) → γ ∈ H' := fun γ hγ hfix =>
    (UpperTheory.Kd.K4.faith ε X H' M hM hΓ γ hfix).resolve_right fun h1 => hneg <| by
      have h2 := H.mul_mem (hle h1) (H.inv_mem hγ)
      rwa [neg_mul, mul_inv_cancel] at h2
  obtain ⟨f', hf'0, hf', h, hh0, hprod⟩ :=
    @abs_step Ω X.K SL(2, ℤ) _ _ _ _ _ (fun γ => (X.sl (ofSL γ)).toRingEquiv)
      (fun g => by simp [X.sl_one]) (fun x y g => by simp [X.sl_mul]) H H' hn (lev X H) (lev X H') (lev_anti X hle)
      (mem_lev_iff X H) (mem_lev_iff X H') (algPoly X H) (algRat X H) (isScalarTower_poly_rat X H)
      (GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X H M hM (hΓ.trans hle)) (algPoly X H') (algRat X H') (isScalarTower_poly_rat X H')
      (GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X H' M hM hΓ) (fun p => (coe_jPoly X H p).trans (coe_jPoly X H' p).symm) hfaith ι _ δ hδ.1 hδ.2
      m m' hm hm' ⟨f, hfH⟩ hF0 ((lun_iff X H m ⟨f, hfH⟩).1 hfW)
  exact ⟨f', ⟨fun e => hf'0 (Subtype.ext e), f'.2, (lun_iff X H' (m * m') f').2 hf'⟩, h, hh0, hprod⟩
