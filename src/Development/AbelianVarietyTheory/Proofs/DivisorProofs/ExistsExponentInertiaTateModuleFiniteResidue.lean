module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaPowFixesOfCommutative
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemPowSucc
namespace GlobalTheory.AlgEquivTrivialPowerCongruence

theorem sub_mem_pow_succ {B : Type} [CommRing B] (Q : Ideal B) (ρ : B →+* B)
    (h0 : ∀ x, ρ x - x ∈ Q) (h1 : ∀ x ∈ Q, ρ x - x ∈ Q ^ 2) :
    ∀ (k : ℕ), ∀ x ∈ Q ^ k, ρ x - x ∈ Q ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro x _; simpa using h0 x
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha q hq
      have hd := ih a ha
      have hρa : ρ a ∈ Q ^ k := by
        have h2 : ρ a - a ∈ Q ^ k := Ideal.pow_le_pow_right (Nat.le_succ k) hd
        have h3 := Ideal.add_mem _ h2 ha
        simpa using h3
      have e : ρ (a * q) - a * q = ρ a * (ρ q - q) + (ρ a - a) * q := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have h4 := Ideal.mul_mem_mul hρa (h1 q hq)
        rw [← pow_add] at h4
        exact h4
      · have h4 := Ideal.mul_mem_mul hd hq
        rw [← pow_succ] at h4
        exact h4
    · intro a b ha hb
      have e : ρ (a + b) - (a + b) = (ρ a - a) + (ρ b - b) := by
        rw [map_add (f := _)]; ring
      rw [e]
      exact Ideal.add_mem _ ha hb

theorem algEquiv_eq_one (A B : Type) [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Algebra A B] (Q : Ideal B) (ρ : B ≃ₐ[A] B) (m : ℕ) (hQ : Q ≠ ⊤) (hm : IsUnit (m : B))
    (hρ : ρ ^ m = 1) (h0 : ∀ x : B, ρ x - x ∈ Q) (h1 : ∀ x ∈ Q, ρ x - x ∈ Q ^ 2) :
    ρ = 1 := by
  have step : ∀ (k : ℕ), ∀ x ∈ Q ^ k, ρ x - x ∈ Q ^ (k + 1) :=
    sub_mem_pow_succ Q (ρ : B →+* B) h0 h1
  have key : ∀ (k : ℕ) (x : B), ρ x - x ∈ Q ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have hy := ih x
      have hj : ∀ j : ℕ, (ρ ^ j) x - x - (j : B) * (ρ x - x) ∈ Q ^ (k + 1) := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          have hz := step (k + 1) _ ihj
          have hz' := Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)) hz) ihj
          rw [sub_add_cancel] at hz'
          have hw := Ideal.mul_mem_left _ (j : B) (step k _ hy)
          have h5 := Ideal.add_mem _ hz' hw
          convert h5 using 1
          rw [pow_succ', AlgEquiv.mul_apply]
          simp only [map_sub, map_mul, map_natCast]
          push_cast
          ring
      have hmm := hj m
      rw [hρ] at hmm
      simp only [AlgEquiv.one_apply, sub_self, zero_sub, neg_mem_iff] at hmm
      exact (Ideal.unit_mul_mem_iff_mem _ hm).1 hmm
  have hbot : ⨅ k : ℕ, Q ^ k = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain Q hQ
  ext x
  have hx : ρ x - x ∈ ⨅ k : ℕ, Q ^ k := Ideal.mem_iInf.2 fun k => key k x
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at hx
  simpa using hx

end GlobalTheory.AlgEquivTrivialPowerCongruence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaPowFixesOfCommutative
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TameInertia

theorem eq_one_of_pow_eq_one_of_sub_mem_sq : ∀ (A B : Type) [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra A B] (Q : Ideal B) (ρ : B ≃ₐ[A] B) (m : ℕ), Q ≠ ⊤ → IsUnit (m : B) → ρ ^ m = 1 → (∀ x, ρ x - x ∈ Q) → (∀ x ∈ Q, ρ x - x ∈ Q ^ 2) → ρ = 1 := by
  first
  | exact @_root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one
  | exact _root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one
  | (apply _root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one ..)

theorem exists_generator_mod_sq : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (Q : Ideal B) [Q.IsPrime], Q ≠ ⊥ → (∃ π ∈ Q, π ∉ Q ^ 2 ∧ ∀ x ∈ Q, ∃ c, x - c * π ∈ Q ^ 2) ∧ ∀ a b : B, a * b ∈ Q ^ 2 → a ∉ Q → b ∈ Q ^ 2 := by
  intro B _ _ Q hQ hQ0
  have hQt : Q ≠ ⊤ := Ideal.IsPrime.ne_top hQ
  have hmax : Q.IsMaximal := Ideal.IsPrime.isMaximal hQ hQ0
  refine ⟨?_, fun a b hab ha => ?_⟩
  · obtain ⟨π, hπ, hπ2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self Q hQ0 hQt 2 le_rfl)
    refine ⟨π, hπ, hπ2, fun x hx => ?_⟩
    have hlt : Q ^ (1 + 1) < Ideal.span {π} ⊔ Q ^ 2 := by
      refine lt_of_le_of_ne le_sup_right fun h => hπ2 ?_
      rw [h]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)
    have hle : Ideal.span {π} ⊔ Q ^ 2 ≤ Q ^ 1 := by
      rw [pow_one]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hπ) (Ideal.pow_le_self two_ne_zero)
    have heq := Ideal.eq_prime_pow_of_succ_lt_of_le hQ0 hlt hle
    rw [pow_one] at heq
    rw [← heq] at hx
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    exact ⟨c, by simpa using hw⟩
  · have hrad : (Q ^ 2).radical = Q := by
      rw [Ideal.radical_pow Q two_ne_zero, hQ.radical]
    have hprim : (Q ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hmax)
    rcases (Ideal.isPrimary_iff.1 hprim).2 (by rw [mul_comm]; exact hab) with h | h
    · exact h
    · rw [hrad] at h
      exact absurd h ha

theorem exists_tame_scalar : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (Q : Ideal B) (π : B), π ∈ Q → (∀ x ∈ Q, ∃ c, x - c * π ∈ Q ^ 2) → ∀ ρ : B ≃ₐ[A] B, (∀ x, ρ x - x ∈ Q) → ∃ c : B, ∀ k : ℕ, ∀ x ∈ Q, (ρ ^ k) x - c ^ k * x ∈ Q ^ 2 := by
  intro A B _ _ _ Q π hπ hgen ρ hI
  have hmul : ∀ a b : B, a ∈ Q → b ∈ Q → a * b ∈ Q ^ 2 := fun a b ha hb => by
    rw [pow_two]; exact Ideal.mul_mem_mul ha hb
  have hρQ : ∀ x ∈ Q, ρ x ∈ Q := fun x hx => by
    have := Q.add_mem (hI x) hx
    rwa [sub_add_cancel] at this
  have hρQ2 : ∀ y ∈ Q ^ 2, ρ y ∈ Q ^ 2 := fun y hy => by
    have h1 : Q.map (ρ : B →+* B) ≤ Q := Ideal.map_le_iff_le_comap.2 fun x hx => hρQ x hx
    have h2' : (Q ^ 2).map (ρ : B →+* B) ≤ Q ^ 2 := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono h1 2
    exact h2' (Ideal.mem_map_of_mem _ hy)
  obtain ⟨c, hc⟩ := hgen (ρ π) (hρQ π hπ)
  have h1 : ∀ x ∈ Q, ρ x - c * x ∈ Q ^ 2 := fun x hx => by
    obtain ⟨d, hd⟩ := hgen x hx
    set w := x - d * π with hw
    have hx' : x = d * π + w := by rw [hw]; ring
    have e : ρ x - c * x = (ρ d - d) * ρ π + d * (ρ π - c * π) + (ρ w - c * w) := by
      rw [hx', map_add (f := _), map_mul]; ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.add_mem _ (hmul _ _ (hI d) (hρQ π hπ)) (Ideal.mul_mem_left _ _ hc)) ?_
    exact Ideal.sub_mem _ (hρQ2 w hd) (Ideal.mul_mem_left _ _ hd)
  refine ⟨c, fun k => ?_⟩
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    have e : (ρ ^ (k + 1)) x - c ^ (k + 1) * x =
        ρ ((ρ ^ k) x - c ^ k * x) + (ρ (c ^ k) - c ^ k) * ρ x + c ^ k * (ρ x - c * x) := by
      rw [pow_succ', AlgEquiv.mul_apply, map_sub, map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hρQ2 _ (ih x hx)) (hmul _ _ (hI _) (hρQ x hx)))
      (Ideal.mul_mem_left _ _ (h1 x hx))

theorem pow_card_sub_one_sub_mem_sq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (Q : Ideal B) [Q.IsPrime] (π : B), π ∈ Q → π ∉ Q ^ 2 → (∀ x ∈ Q, ∃ c, x - c * π ∈ Q ^ 2) → (∀ a b : B, a * b ∈ Q ^ 2 → a ∉ Q → b ∈ Q ^ 2) → ∀ (ρ φ : B ≃ₐ[A] B) (q : ℕ) (c : B), IsOfFinOrder ρ → IsOfFinOrder φ → ρ * φ = φ * ρ → (∀ x, φ x - x ^ q ∈ Q) → (∀ k : ℕ, ∀ x ∈ Q, (ρ ^ k) x - c ^ k * x ∈ Q ^ 2) → ∀ x ∈ Q, (ρ ^ (q - 1)) x - x ∈ Q ^ 2 := by
  intro A B _ _ _ Q hQ π hπ hπ2 hgen hprim ρ φ q c hρf hφf hcomm hφ hc
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · intro x _; simp
  have hmul : ∀ a b : B, a ∈ Q → b ∈ Q → a * b ∈ Q ^ 2 := fun a b ha hb => by
    rw [pow_two]; exact Ideal.mul_mem_mul ha hb
  have hQ2Q : Q ^ 2 ≤ Q := Ideal.pow_le_self two_ne_zero
  have pres : ∀ α : B ≃ₐ[A] B, (∀ x ∈ Q, α x ∈ Q) → ∀ y ∈ Q ^ 2, α y ∈ Q ^ 2 := fun α hα y hy => by
    have h1 : Q.map (α : B →+* B) ≤ Q := Ideal.map_le_iff_le_comap.2 fun x hx => hα x hx
    have h2' : (Q ^ 2).map (α : B →+* B) ≤ Q ^ 2 := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono h1 2
    exact h2' (Ideal.mem_map_of_mem _ hy)
  have hfin : ∀ α : B ≃ₐ[A] B, IsOfFinOrder α → (∀ x ∈ Q, α x ∈ Q) → α π ∈ Q ^ 2 → False := by
    intro α hαf hα hαπ
    obtain ⟨n, hn, hαn⟩ := hαf.exists_pow_eq_one
    have hk : ∀ k : ℕ, ∀ y ∈ Q ^ 2, (α ^ k) y ∈ Q ^ 2 := fun k => by
      induction k with
      | zero => intro y hy; simpa using hy
      | succ k ih => intro y hy; rw [pow_succ' α k, AlgEquiv.mul_apply]; exact pres α hα _ (ih y hy)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    apply hπ2
    have := hk n' _ hαπ
    rwa [← AlgEquiv.mul_apply, ← pow_succ, hαn, AlgEquiv.one_apply] at this
  have hc1 : ∀ x ∈ Q, ρ x - c * x ∈ Q ^ 2 := fun x hx => by simpa using hc 1 x hx
  have hρQ : ∀ x ∈ Q, ρ x ∈ Q := fun x hx => by
    have := Q.add_mem (hQ2Q (hc1 x hx)) (Q.mul_mem_left c hx)
    rwa [sub_add_cancel] at this
  have hφQ : ∀ x ∈ Q, φ x ∈ Q := fun x hx => by
    have := Q.add_mem (hφ x) (Q.pow_mem_of_mem hx q hq)
    rwa [sub_add_cancel] at this
  have hcQ : c ∉ Q := fun hcQ => hfin ρ hρf hρQ (by
    have := Ideal.add_mem _ (hc1 π hπ) (hmul c π hcQ hπ)
    rwa [sub_add_cancel] at this)
  have hφπ : φ π ∉ Q ^ 2 := fun h => hfin φ hφf hφQ h
  have hd : (φ c - c) * φ π ∈ Q ^ 2 := by
    have h1 := hc1 (φ π) (hφQ π hπ)
    have h2 := pres φ hφQ _ (hc1 π hπ)
    have hcm : φ (ρ π) = ρ (φ π) := by rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, hcomm]
    have e : (φ c - c) * φ π = (ρ (φ π) - c * φ π) - (φ (ρ π - c * π)) := by
      rw [map_sub, map_mul, hcm]; ring
    rw [e]
    exact Ideal.sub_mem _ h1 h2
  have hφc : φ c - c ∈ Q := by
    by_contra h
    exact hφπ (hprim _ _ hd h)
  have hcq : c * (c ^ (q - 1) - 1) ∈ Q := by
    have e : c * (c ^ (q - 1) - 1) = (φ c - c) - (φ c - c ^ q) := by
      rw [mul_sub, _root_.mul_one, ← pow_succ', Nat.sub_add_cancel hq]; ring
    rw [e]
    exact Ideal.sub_mem _ hφc (hφ c)
  have hcq' : c ^ (q - 1) - 1 ∈ Q := (hQ.mem_or_mem hcq).resolve_left hcQ
  intro x hx
  have e : (ρ ^ (q - 1)) x - x = ((ρ ^ (q - 1)) x - c ^ (q - 1) * x) + (c ^ (q - 1) - 1) * x := by ring
  rw [e]
  exact Ideal.add_mem _ (hc (q - 1) x hx) (hmul _ _ hcq' hx)

theorem integral_mem_and_valuation_lt_one : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → (∀ x : Ω, IsIntegral R x → x ∈ V) ∧ ∀ r : R, (V.valuation (algebraMap R Ω r) < 1 ↔ r ∈ maximalIdeal R) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  have memV : ∀ a : K, algebraMap K Ω a ∈ V ↔ a ∈ (algebraMap R K).range := fun a => by
    rw [← hV]; rfl
  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := fun r => by
    rw [IsScalarTower.algebraMap_apply R K Ω]
    exact (memV _).2 ⟨r, rfl⟩
  refine ⟨fun x hx => ?_, fun r => ?_⟩
  · letI : Algebra R V := ((algebraMap R Ω).codRestrict V hRV).toAlgebra
    haveI : IsScalarTower R V Ω := .of_algebraMap_eq fun _ => rfl
    have hxV : IsIntegral V x := hx.tower_top
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hxV
    exact y.2
  · constructor
    · intro h
      by_contra hr
      have hu : IsUnit r := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hr
      obtain ⟨u, rfl⟩ := hu
      have h1 : V.valuation (algebraMap R Ω (u : R)) * V.valuation (algebraMap R Ω ((u⁻¹ : Rˣ) : R)) = 1 := by
        rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
      have h2 : V.valuation (algebraMap R Ω ((u⁻¹ : Rˣ) : R)) ≤ 1 := (V.valuation_le_one_iff _).2 (hRV _)
      have h3 : V.valuation (algebraMap R Ω (u : R)) * V.valuation (algebraMap R Ω ((u⁻¹ : Rˣ) : R)) < 1 :=
        mul_lt_one_of_lt_of_le h h2
      rw [h1] at h3
      exact lt_irrefl _ h3
    · intro hr
      by_contra h
      have hle : V.valuation (algebraMap R Ω r) = 1 :=
        le_antisymm ((V.valuation_le_one_iff _).2 (hRV r)) (not_lt.1 h)
      have hne : algebraMap R Ω r ≠ 0 := fun e => by rw [e, map_zero] at hle; exact zero_ne_one hle
      have hinv : (algebraMap R Ω r)⁻¹ ∈ V := by
        rw [← V.valuation_le_one_iff, map_inv₀, hle, inv_one]
      rw [IsScalarTower.algebraMap_apply R K Ω, ← map_inv₀] at hinv
      obtain ⟨s, hs⟩ := (memV _).1 hinv
      have hrK : algebraMap R K r ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply R K Ω] at hne
        exact fun e => hne (by rw [e, map_zero])
      have hrs : algebraMap R K (r * s) = algebraMap R K 1 := by
        rw [map_mul, hs, mul_inv_cancel₀ hrK, map_one]
      have := IsFractionRing.injective R K hrs
      exact (mem_maximalIdeal _ |>.1 hr) ⟨⟨r, s, this, by rw [mul_comm]; exact this⟩, rfl⟩

theorem exists_frobenius : ∀ (R B G : Type) [CommRing R] [IsLocalRing R] [Finite (ResidueField R)] [CommRing B] [Algebra R B] [Module.Finite R B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B] [Algebra.IsInvariant R B G] (Q : Ideal B) [Q.IsPrime], Q.under R = maximalIdeal R → ∃ σ : G, ∀ x : B, σ • x - x ^ Nat.card (ResidueField R) ∈ Q := by
  intro R B G _ _ _ _ _ _ _ _ _ _ _ Q _ hQ
  haveI : Q.LiesOver (maximalIdeal R) := ⟨hQ.symm⟩
  haveI : Finite (R ⧸ maximalIdeal R) := inferInstanceAs (Finite (ResidueField R))
  haveI : Module.Finite (R ⧸ maximalIdeal R) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ maximalIdeal R) (B ⧸ Q)
  haveI : Finite (B ⧸ Q) := Module.finite_of_finite (R ⧸ maximalIdeal R)
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant R G Q
  refine ⟨σ, fun x => ?_⟩
  have := hσ x
  rw [hQ] at this
  exact this

theorem inertia_pow_fixes_of_commutative : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω), FiniteDimensional K L → IsGalois K L → (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) → ∀ σ ∈ inertia K V, ∃ a : ℕ, ∀ x ∈ L, (σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a)) x = x := by
  intro R K Ω _ _ _ _ _ _ _ _ _ V hV L hfin hgal hab σ hσ
  haveI := hfin
  haveI := hgal

  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R K L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R L Ω := .of_algebraMap_eq fun _ => rfl
  let B := integralClosure R L
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension R K L B
  haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain R K L B
  haveI : Module.Finite R B := IsIntegralClosure.finite R K L B
  haveI : Algebra.IsInvariant R B (B ≃ₐ[R] B) := Algebra.isInvariant_of_isGalois' R K L B
  haveI : Finite (B ≃ₐ[R] B) := Finite.of_equiv _ (galRestrict R K L B).toEquiv

  obtain ⟨hint, hres⟩ := integral_mem_and_valuation_lt_one R K Ω V hV
  have hBV : ∀ b : B, algebraMap L Ω (algebraMap B L b) ∈ V := fun b =>
    hint _ ((b.2).map (IsScalarTower.toAlgHom R L Ω))
  let f : B →+* V := ((algebraMap L Ω).comp (algebraMap B L)).codRestrict V hBV
  let Q : Ideal B := (maximalIdeal V).comap f
  have hQmem : ∀ b : B, b ∈ Q ↔ V.valuation (algebraMap L Ω (algebraMap B L b)) < 1 := fun b =>
    ValuationSubring.valuation_lt_one_iff V (f b)
  haveI : Q.IsPrime := Ideal.comap_isPrime f _
  have hunder : Q.under R = maximalIdeal R := by
    ext r
    rw [Ideal.under, Ideal.mem_comap, hQmem, ← hres r, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hQ0 : Q ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    intro h
    have h1 : algebraMap R B ϖ ∈ Q := by
      change ϖ ∈ Q.under R
      rw [hunder]
      exact hϖ.not_isUnit
    rw [h, Ideal.mem_bot] at h1
    have h2 : algebraMap R L ϖ = 0 := by
      rw [IsScalarTower.algebraMap_apply R B L, h1, map_zero]
    rw [IsScalarTower.algebraMap_apply R K L, map_eq_zero] at h2
    exact hϖ.ne_zero (IsFractionRing.injective R K (h2.trans (map_zero _).symm))
  obtain ⟨φ, hφ⟩ := exists_frobenius R B (B ≃ₐ[R] B) Q hunder
  set q := Nat.card (ResidueField R) with hq
  set τ := AlgEquiv.restrictNormal σ L with hτdef
  set ρ := galRestrict R K L B τ with hρdef
  have hσ' := (mem_inertia_iff V σ).1 hσ
  have hρ : ρ ∈ Q.inertia (B ≃ₐ[R] B) := fun b => by
    show ρ • b - b ∈ Q
    rw [hQmem]
    have e : algebraMap L Ω (algebraMap B L (ρ • b - b)) =
        σ (algebraMap L Ω (algebraMap B L b)) - algebraMap L Ω (algebraMap B L b) := by
      rw [AlgEquiv.smul_def, (algebraMap B L).map_sub, (algebraMap L Ω).map_sub,
        algebraMap_galRestrict_apply, AlgEquiv.restrictNormal_commutes]
    rw [e]
    exact hσ'.2 _ (hBV b)
  have hcomm : ∀ α β : B ≃ₐ[R] B, α * β = β * α := fun α β => by
    obtain ⟨α', rfl⟩ := (galRestrict R K L B).surjective α
    obtain ⟨β', rfl⟩ := (galRestrict R K L B).surjective β
    rw [← map_mul, ← map_mul, hab]
  set N := orderOf ρ with hNdef
  have hN : 0 < N := orderOf_pos ρ
  set p := ringChar (ResidueField R) with hpdef
  haveI := Fintype.ofFinite (ResidueField R)
  have hp : p.Prime := CharP.char_is_prime (ResidueField R) p
  set a := N.factorization p with hadef
  set m := N / p ^ a with hmdef
  have hNm : p ^ a * m = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp hN.ne'
  have hmk : (m : ResidueField R) ≠ 0 := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop ((CharP.cast_eq_zero_iff (ResidueField R) p m).1 h))
  have hmR : IsUnit (m : R) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    exact hmk
  have hmB : IsUnit (m : B) := by simpa using hmR.map (algebraMap R B)
  set ρ1 := ρ ^ (p ^ a) with hρ1
  have hρ1I : ρ1 ∈ Q.inertia (B ≃ₐ[R] B) := Subgroup.pow_mem _ hρ _
  obtain ⟨⟨π, hπQ, hπ2, hπgen⟩, hprim⟩ := exists_generator_mod_sq B Q hQ0
  obtain ⟨c, hc⟩ := exists_tame_scalar R B Q π hπQ hπgen ρ1 hρ1I
  have h2 := pow_card_sub_one_sub_mem_sq R B Q π hπQ hπ2 hπgen hprim ρ1 φ q c (isOfFinOrder_of_finite _) (isOfFinOrder_of_finite _)
    (hcomm _ _) (fun x => hφ x) hc
  have hρ2 : ρ1 ^ (q - 1) = 1 := by
    refine eq_one_of_pow_eq_one_of_sub_mem_sq R B Q (ρ1 ^ (q - 1)) m (Ideal.IsPrime.ne_top inferInstance) hmB ?_
      (Subgroup.pow_mem _ hρ1I _) h2
    rw [hρ1, ← pow_mul, ← pow_mul, show p ^ a * ((q - 1) * m) = N * (q - 1) by rw [← hNm]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  have hτn : τ ^ ((q - 1) * p ^ a) = 1 := by
    apply (galRestrict R K L B).injective
    rw [map_pow, map_one, ← hρdef, mul_comm, pow_mul]
    exact hρ2
  refine ⟨a, fun x hx => ?_⟩
  have e1 : AlgEquiv.restrictNormal (σ ^ ((q - 1) * p ^ a)) L = τ ^ ((q - 1) * p ^ a) :=
    map_pow (AlgEquiv.restrictNormalHom L) σ _
  have := AlgEquiv.restrictNormal_commutes (σ ^ ((q - 1) * p ^ a)) L ⟨x, hx⟩
  rw [e1, hτn] at this
  simpa using this.symm

end GlobalTheory.TameInertia
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaPowFixesOfCommutativeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_pow_fixes_of_commutative_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω), FiniteDimensional K L → IsGalois K L → (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) → ∀ σ ∈ inertia K V, ∃ a : ℕ, ∀ x ∈ L, (σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a)) x = x := by
  first | exact @GlobalTheory.TameInertia.inertia_pow_fixes_of_commutative | exact GlobalTheory.TameInertia.inertia_pow_fixes_of_commutative | (intros; apply GlobalTheory.TameInertia.inertia_pow_fixes_of_commutative <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentInertiaTateModuleFiniteResidue
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InertiaTate

theorem iterate_map_mul' {M : Type} [CommGroup M] (φ : M →* M) (j : ℕ) (a b : M) :
    (⇑φ)^[j] (a * b) = (⇑φ)^[j] a * (⇑φ)^[j] b := by
  induction j generalizing a b with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_mul, ih]

theorem pow_fix_of_fix {M : Type} [CommGroup M] (φ : M →* M) (l : ℕ)
    (h : ∀ x : M, x ^ l = 1 → φ x = x) :
    ∀ (k : ℕ) (x : M), x ^ l ^ (k + 1) = 1 → (⇑φ)^[l ^ k] x = x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [pow_zero, Function.iterate_one]
    exact h x (by simpa using hx)
  | succ k ih =>
    intro x hx
    let ψ : M →* M := MonoidHom.mk' ((⇑φ)^[l ^ k]) (iterate_map_mul' φ _)
    have hψ : ∀ y, ψ y = (⇑φ)^[l ^ k] y := fun _ => rfl
    have ih' : ∀ y : M, y ^ l ^ (k + 1) = 1 → ψ y = y := fun y hy => by rw [hψ]; exact ih y hy
    have hxl : ψ (x ^ l) = x ^ l := ih' _ (by rw [← pow_mul, ← pow_succ', hx])
    obtain ⟨d, hd⟩ : ∃ d : M, d = ψ x * x⁻¹ := ⟨_, rfl⟩
    have hψx : ψ x = x * d := by rw [hd, mul_comm (ψ x), mul_inv_cancel_left]
    have hdl : d ^ l = 1 := by
      rw [hd, mul_pow, inv_pow, ← map_pow, hxl, mul_inv_cancel]
    have hdψ : ψ d = d := ih' d (by rw [pow_succ', pow_mul, hdl, one_pow])
    have hit : ∀ j : ℕ, (⇑ψ)^[j] x = x * d ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        rw [Function.iterate_succ_apply', ihj, map_mul, map_pow, hdψ, hψx, _root_.mul_assoc, ← pow_succ']
    have e : (⇑φ)^[l ^ (k + 1)] x = (⇑ψ)^[l] x := by
      rw [pow_succ, Function.iterate_mul]
      rfl
    rw [e, hit, hdl, _root_.mul_one]

theorem mem_of_pow_mem_of_coprime {G : Type} [Group G] (H : Subgroup G) (g : G) {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : g ^ m ∈ H) (hn : g ^ n ∈ H) : g ∈ H := by
  have e : ((Nat.gcd m n : ℕ) : ℤ) = m * Nat.gcdA m n + n * Nat.gcdB m n := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one, Nat.cast_one] at e
  have : g = (g ^ m) ^ Nat.gcdA m n * (g ^ n) ^ Nat.gcdB m n := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← e, zpow_one]
  rw [this]
  exact H.mul_mem (H.zpow_mem hm _) (H.zpow_mem hn _)

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

def stab (x : ptOver K Ω ⟶ A) : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | specAut σ ≫ x = x}
  one_mem' := by
    change specAut 1 ≫ x = x
    rw [specAut_one, Category.id_comp]
  mul_mem' := by
    intro a b ha hb
    change specAut (a * b) ≫ x = x
    change specAut a ≫ x = x at ha
    change specAut b ≫ x = x at hb
    rw [specAut_mul, Category.assoc, hb, ha]
  inv_mem' := by
    intro a ha
    change specAut a ≫ x = x at ha
    change specAut a⁻¹ ≫ x = x
    conv_lhs => rw [← ha]
    rw [← Category.assoc, ← specAut_mul, inv_mul_cancel, specAut_one, Category.id_comp]

theorem mem_stab_iff (x : ptOver K Ω ⟶ A) (σ : Ω ≃ₐ[K] Ω) : σ ∈ stab A x ↔ galPts A σ x = x := Iff.rfl

theorem galPts_pow (σ : Ω ≃ₐ[K] Ω) (j : ℕ) (x : ptOver K Ω ⟶ A) :
    galPts A (σ ^ j) x = (⇑(galPts A σ))^[j] x := by
  induction j generalizing x with
  | zero =>
    change specAut (σ ^ 0) ≫ x = x
    rw [pow_zero, specAut_one, Category.id_comp]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← ih]
    change specAut (σ ^ (j + 1)) ≫ x = specAut σ ≫ (specAut (σ ^ j) ≫ x)
    rw [pow_succ', specAut_mul, Category.assoc]

theorem exists_field_of_point [Algebra.IsAlgebraic K Ω] [LocallyOfFiniteType A.hom] (x : ptOver K Ω ⟶ A) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ stab A x ↔ σ ∈ E.fixingSubgroup := by
  obtain ⟨E, hE1, -, hE3⟩ := GlobalTheory.SS.exists_fieldOfValues A.left Ω x.left
  obtain ⟨L, hL, hLE⟩ := hE3 K A.hom inferInstance (Over.w x) inferInstance
  refine ⟨L, hL, fun σ => ?_⟩
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [← Spec.map_id]
    congr 1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have h1 : σ ∈ stab A x ↔ spMap (σ : Ω →+* Ω) ≫ x.left = spMap (RingHom.id Ω) ≫ x.left := by
    rw [hid, Category.id_comp]
    constructor
    · intro h
      exact congrArg CommaMorphism.left h
    · intro h
      exact Over.OverMorphism.ext h
  rw [h1, hE1]
  constructor
  · intro h c hc
    exact h c (by rw [← hLE]; exact hc)
  · intro h c hc
    exact h c (by rw [← hLE] at hc; exact hc)

end GlobalTheory.InertiaTate

namespace GlobalTheory.InertiaTate

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

theorem exists_galois_field_of_finite [IsGalois K Ω] [LocallyOfFiniteType A.hom] (S : Set (ptOver K Ω ⟶ A))
    (hS : S.Finite) (hst : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ S, galPts A σ x ∈ S) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ L.fixingSubgroup ↔ ∀ x ∈ S, σ ∈ stab A x := by
  choose E hE hEs using fun x : S => exists_field_of_point A x.1
  haveI : Finite S := hS.to_subtype
  haveI := hE
  have key : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ (⨆ x : S, E x).fixingSubgroup ↔ ∀ x ∈ S, σ ∈ stab A x := by
    intro σ
    rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, iSup_le_iff]
    constructor
    · intro h x hx
      exact (hEs ⟨x, hx⟩ σ).2 (Subgroup.zpowers_le.1 ((IntermediateField.le_iff_le _ _).1 (h ⟨x, hx⟩)))
    · intro h x
      exact (IntermediateField.le_iff_le _ _).2 (Subgroup.zpowers_le.2 ((hEs x σ).1 (h x.1 x.2)))
  refine ⟨⨆ x : S, E x, inferInstance, ?_, key⟩
  refine (InfiniteGalois.normal_iff_isGalois _).1 ⟨fun n hn g => ?_⟩
  rw [key] at hn ⊢
  intro x hx
  have h1 := hn _ (hst g⁻¹ x hx)
  change specAut n ≫ (specAut g⁻¹ ≫ x) = specAut g⁻¹ ≫ x at h1
  change specAut (g * n * g⁻¹) ≫ x = x
  rw [specAut_mul, specAut_mul, Category.assoc, Category.assoc, h1, ← Category.assoc, ← specAut_mul,
    mul_inv_cancel, specAut_one, Category.id_comp]

theorem aut_comm_of_galTate_comm (l : ℕ) [Fact l.Prime]
    (hc : ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ)
    (L : IntermediateField K Ω) [Normal K L] [Normal K Ω] (n : ℕ)
    (hL : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ L.fixingSubgroup ↔
      ∀ x ∈ Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n), σ ∈ stab A x) :
    ∀ α β : L ≃ₐ[K] L, α * β = β * α := by
  intro α β
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω α
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω β
  rw [← map_mul, ← map_mul, MonoidHom.eq_iff, IntermediateField.restrictNormalHom_ker, hL]
  rintro _ ⟨t, rfl⟩
  have h1 : galTate A l ((τ * σ)⁻¹ * (σ * τ)) = 1 := by
    rw [map_mul, map_mul (galTate A l) σ τ, hc σ τ, ← map_mul (galTate A l) τ σ, ← map_mul, inv_mul_cancel,
      map_one]
  exact (congrArg (fun f => Tate.lev (f t) n) h1 :)

end GlobalTheory.InertiaTate


open GlobalTheory.InertiaTate in
theorem GlobalTheory.InertiaTate.exists_exponent_inertia_galTate : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) → ∃ E : ℕ, 0 < E ∧ ∀ σ ∈ inertia K V, galTate A l σ ^ E = 1 := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA l _ hl hc
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : LocallyOfFiniteType A.hom := by
    haveI := hA.smooth
    infer_instance
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K A hA
  have hlK : (l : K) ≠ 0 := by
    intro h0
    apply hl
    have : (l : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, h0, map_zero])
    rw [← map_natCast (residue R), this, map_zero]
  have hfin : ∀ n : ℕ, {x : ptOver K Ω ⟶ A | x ^ (l ^ n) = 1}.Finite := by
    intro n
    have h := GlobalTheory.T.card_abelianVariety_torsion_sepClosed K Ω A hA g hg (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)
    have : Finite {x : ptOver K Ω ⟶ A // x ^ (l ^ n) = 1} :=
      Nat.finite_of_card_ne_zero (by
        rw [h]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
    exact Set.finite_coe_iff.mp this
  have hSfin : ∀ n, (Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n)).Finite := fun n =>
    (hfin n).subset (by rintro _ ⟨t, rfl⟩; exact t.lev_pow n)
  have hSst : ∀ n, ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n),
      galPts A σ x ∈ Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n) := by
    rintro n σ _ ⟨t, rfl⟩
    exact ⟨galTate A l σ t, rfl⟩
  have h1st : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ {x : ptOver K Ω ⟶ A | x ^ l = 1},
      galPts A σ x ∈ {x : ptOver K Ω ⟶ A | x ^ l = 1} := by
    intro σ x hx
    change galPts A σ x ^ l = 1
    rw [← map_pow, show x ^ l = 1 from hx, map_one]
  obtain ⟨L₁, hL₁f, hL₁g, hL₁⟩ := exists_galois_field_of_finite A {x : ptOver K Ω ⟶ A | x ^ l = 1}
    (by simpa using hfin 1) h1st
  have hq : 1 < Nat.card (ResidueField R) := Finite.one_lt_card
  have hN : 0 < Nat.card (L₁ ≃ₐ[K] L₁) := Nat.card_pos
  refine ⟨(Nat.card (ResidueField R) - 1) * Nat.card (L₁ ≃ₐ[K] L₁), Nat.mul_pos (by omega) hN, ?_⟩
  intro σ hσ
  obtain ⟨g0, hg0⟩ : ∃ g0, g0 = (σ ^ (Nat.card (ResidueField R) - 1)) ^ Nat.card (L₁ ≃ₐ[K] L₁) := ⟨_, rfl⟩
  rw [← map_pow, pow_mul, ← hg0]
  refine LinearMap.ext fun t => Tate.ext fun n => ?_
  change galPts A g0 (t.lev n) = t.lev n
  rw [← mem_stab_iff]
  have hp : (ringChar (ResidueField R)).Prime := CharP.char_is_prime (ResidueField R) _
  have hpl : ringChar (ResidueField R) ≠ l := by
    intro h
    apply hl
    rw [← h, ringChar.Nat.cast_ringChar]
  have hA1 : ∀ y : ptOver K Ω ⟶ A, y ^ l = 1 → galPts A g0 y = y := by
    intro y hy
    have : g0 ∈ L₁.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, hg0, map_pow, pow_card_eq_one']
    exact (hL₁ g0).1 this y hy
  have hlp : g0 ^ (l ^ n) ∈ stab A (t.lev n) := by
    rw [mem_stab_iff, galPts_pow]
    exact pow_fix_of_fix (galPts A g0) l hA1 n _ (by rw [pow_succ, pow_mul, t.lev_pow, one_pow])
  obtain ⟨Ln, hLnf, hLng, hLn⟩ := exists_galois_field_of_finite A _ (hSfin n) (hSst n)
  have hcomm := aut_comm_of_galTate_comm A l hc Ln n hLn
  obtain ⟨a, ha⟩ := GlobalTheory.T.inertia_pow_fixes_of_commutative_alt R K Ω V hV Ln hLnf hLng hcomm σ hσ
  have hpp : g0 ^ (ringChar (ResidueField R) ^ a) ∈ stab A (t.lev n) := by
    have h2 : σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a) ∈ Ln.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 ha
    have h3 := (hLn _).1 h2 _ ⟨t, rfl⟩
    have e : g0 ^ (ringChar (ResidueField R) ^ a) =
        (σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a)) ^ Nat.card (L₁ ≃ₐ[K] L₁) := by
      rw [hg0, ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [e]
    exact Subgroup.pow_mem _ h3 _
  exact mem_of_pow_mem_of_coprime _ g0 (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Fact.out).2 hpl)) hpp hlp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentInertiaTateModuleFiniteResidueStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponent_inertia_tateModule_finite_residue : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) → ∃ E : ℕ, 0 < E ∧ ∀ σ ∈ inertia K V, galTate A l σ ^ E = 1 := by
  first | exact @GlobalTheory.InertiaTate.exists_exponent_inertia_galTate | exact GlobalTheory.InertiaTate.exists_exponent_inertia_galTate | (intros; apply GlobalTheory.InertiaTate.exists_exponent_inertia_galTate <;> assumption)
end
