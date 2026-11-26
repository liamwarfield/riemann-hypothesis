module

public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.UnitLemmaCaseALevelZero
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.ResidueQuotientHolds

@[expose] public section

section -- merged from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.TotallyRealRoots
section -- merged from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SecondDescentFreePartHolds
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial

theorem val_zero_of_not_dvd {ℓ : ℕ} [Fact ℓ.Prime] {x : ℤ_[ℓ]} (h : ¬ (ℓ : ℤ_[ℓ]) ∣ x) :
    x ≠ 0 ∧ x.valuation = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact h (dvd_zero _)
  refine ⟨hx0, ?_⟩
  by_contra hv
  obtain ⟨w, hw⟩ := Nat.exists_eq_succ_of_ne_zero hv
  apply h
  rw [PadicInt.unitCoeff_spec hx0, hw, pow_succ]
  exact Dvd.intro_left ((PadicInt.unitCoeff hx0 : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ w) (by ring)

private theorem w3_lemma {ℓ : ℕ} [Fact ℓ.Prime] {z : ℤ_[ℓ]} (hz : z ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) z = (z.valuation : ℕ∞) := by
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, z = (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ z.valuation :=
    ⟨_, PadicInt.unitCoeff_spec hz⟩
  generalize z.valuation = v at hu ⊢
  rw [emultiplicity_eq_coe]
  constructor
  · rw [hu]
    exact dvd_mul_left _ _
  · rintro ⟨c, hc⟩
    have hne : (ℓ : ℤ_[ℓ]) ^ v ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
    have hcu : (u : ℤ_[ℓ]) = ℓ * c := by
      have h' : (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ v = ((ℓ : ℤ_[ℓ]) * c) * (ℓ : ℤ_[ℓ]) ^ v := by
        rw [← hu, hc]
        ring
      exact mul_right_cancel₀ hne h'
    have hU := u.isUnit
    rw [hcu] at hU
    have h1 := PadicInt.isUnit_iff.mp (isUnit_of_mul_isUnit_left hU)
    rw [PadicInt.norm_p] at h1
    have h2 : (ℓ : ℝ) = 1 := inv_eq_one.mp h1
    exact (Fact.out : ℓ.Prime).one_lt.ne' (by exact_mod_cast h2)

theorem character_value_formula_holds : StatChiVal := by
  intro ℓ _ hℓ χ hχ k hk
  by_cases hdk : (ℓ - 1) ∣ k
  · rw [if_pos hdk]
    obtain ⟨t, rfl⟩ := hdk
    have ht : t ≠ 0 := by
      rintro rfl
      simp at hk
    obtain ⟨a, t', ht', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht ℓ (Fact.out : ℓ.Prime).one_lt.ne'
    have hpr : Prime (ℓ : ℤ_[ℓ]) := PadicInt.prime_p
    have hodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ
    have hv1 := hχ.2
    have hw0 : (χ : ℤ_[ℓ]) ^ (ℓ - 1) - 1 ≠ 0 := by
      intro h0
      rw [h0, PadicInt.valuation_zero] at hv1
      exact zero_ne_one hv1
    have hem1 : emultiplicity (ℓ : ℤ_[ℓ]) ((χ : ℤ_[ℓ]) ^ (ℓ - 1) - 1) = 1 := by
      rw [w3_lemma hw0, hv1]
      rfl
    have hdiv : (ℓ : ℤ_[ℓ]) ∣ (χ : ℤ_[ℓ]) ^ (ℓ - 1) - 1 := by
      have := (emultiplicity_eq_coe.mp (by rw [hem1]; rfl : emultiplicity (ℓ : ℤ_[ℓ]) ((χ : ℤ_[ℓ]) ^ (ℓ - 1) - 1) = ((1 : ℕ) : ℕ∞))).1
      simpa using this
    have hwu : ¬ (ℓ : ℤ_[ℓ]) ∣ (χ : ℤ_[ℓ]) ^ (ℓ - 1) := fun h =>
      hpr.not_isUnit (isUnit_of_dvd_unit h ((Units.isUnit χ).pow (ℓ - 1)))
    have hxy : (ℓ : ℤ_[ℓ]) ∣ ((χ : ℤ_[ℓ]) ^ (ℓ - 1)) ^ ℓ ^ a - 1 := by
      refine hdiv.trans ?_
      simpa using sub_dvd_pow_sub_pow ((χ : ℤ_[ℓ]) ^ (ℓ - 1)) 1 (ℓ ^ a)
    have hx : ¬ (ℓ : ℤ_[ℓ]) ∣ ((χ : ℤ_[ℓ]) ^ (ℓ - 1)) ^ ℓ ^ a := fun h => hwu (hpr.dvd_of_dvd_pow h)
    have hn : ¬ (ℓ : ℤ_[ℓ]) ∣ ((t' : ℕ) : ℤ_[ℓ]) := by
      rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff]
      exact ht'
    have e1 := emultiplicity_pow_sub_pow_of_prime hpr hxy hx hn
    have e2 := emultiplicity_pow_prime_pow_sub_pow_prime_pow hpr hodd (y := 1) (by simpa using hdiv)
      (by simpa using hwu) a
    rw [one_pow] at e1 e2
    have key : emultiplicity (ℓ : ℤ_[ℓ]) ((χ : ℤ_[ℓ]) ^ ((ℓ - 1) * (ℓ ^ a * t')) - 1) = ((1 + a : ℕ) : ℕ∞) := by
      rw [pow_mul, pow_mul, e1, e2, hem1]
      push_cast
      ring
    have hne : (χ : ℤ_[ℓ]) ^ ((ℓ - 1) * (ℓ ^ a * t')) - 1 ≠ 0 := by
      intro h0
      rw [h0, emultiplicity_zero] at key
      exact ENat.top_ne_natCast _ key
    refine ⟨hne, ?_⟩
    have hv := w3_lemma hne
    rw [key] at hv
    have hv' : PadicInt.valuation ((χ : ℤ_[ℓ]) ^ ((ℓ - 1) * (ℓ ^ a * t')) - 1) = 1 + a := by
      exact_mod_cast hv.symm
    rw [hv']
    have hl1 : ℓ - 1 ≠ 0 := by have := (Fact.out : ℓ.Prime).two_le; omega
    have ht0 : t' ≠ 0 := by
      rintro rfl
      exact ht' (dvd_zero _)
    have hpow : ℓ ^ a ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
    have hnd : ¬ ℓ ∣ ℓ - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [Nat.padicValNat_def, Nat.multiplicity_mul hl1 (mul_ne_zero hpow ht0),
      Nat.multiplicity_mul hpow ht0, Nat.multiplicity_prime_pow,
      multiplicity_eq_zero_of_not_dvd ht', multiplicity_eq_zero_of_not_dvd hnd,
      Nat.add_zero, Nat.zero_add]
  · rw [if_neg hdk]
    exact val_zero_of_not_dvd (fun h => hdk (hχ.1 k h))

private theorem w3_lemma_2 {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {G : GBase ℓ A}
    {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) {a : A} (b : A) (h : P.Kills a) : P.Kills (b * a) := by
  intro n hn
  rw [mul_smul]
  exact P.N'.smul_mem b (h n hn)

private theorem w3_lemma_3 {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (c : ℤ_[ℓ]) (j : ℕ) (h : P.Kills (algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1))) :
    P.Kills (algebraMap ℤ_[ℓ] A (c * ((G.u : ℤ_[ℓ]) ^ (j + 1) - 1)) * G.X ^ j) := by
  intro n hn
  rw [map_mul, map_sub, map_pow, map_one]
  obtain ⟨t, ht⟩ := G.γX
  have hA : (algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1)) • n ∈ P.N' := h n hn
  have hXy : G.X • ((algebraMap ℤ_[ℓ] A c * G.X ^ j) • n) ∈ P.N' := by
    rw [smul_smul]
    have := h n hn
    rwa [show algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1) = G.X * (algebraMap ℤ_[ℓ] A c * G.X ^ j) by ring] at this
  obtain ⟨z, hz, hzeq⟩ := P.γ_N' _ hXy
  obtain ⟨n', hn', hn'eq⟩ := P.γ_N n hn
  have hγn : P.γ n = n + G.X • n' := by
    rw [← hn'eq]
    abel
  have hγy : P.γ ((algebraMap ℤ_[ℓ] A c * G.X ^ j) • n) =
      (algebraMap ℤ_[ℓ] A c * (G.X * (algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ]) + G.X * t)) ^ j) • (n + G.X • n') := by
    rw [P.γ_smul, map_mul, map_pow, ht, hγn, AlgHom.commutes]
  have h1 : G.X • ((algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ]) + G.X * t) • P.γ ((algebraMap ℤ_[ℓ] A c * G.X ^ j) • n) -
      (algebraMap ℤ_[ℓ] A c * G.X ^ j) • n - z) = 0 := by
    rw [smul_sub, smul_sub, smul_smul, ← ht, ← P.γ_smul, ← hzeq]
    abel
  have h2 : (algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ]) + G.X * t) • P.γ ((algebraMap ℤ_[ℓ] A c * G.X ^ j) • n) -
      (algebraMap ℤ_[ℓ] A c * G.X ^ j) • n = z := by
    have := P.X_inj _ h1
    rwa [sub_eq_zero] at this
  obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow (algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ]) + G.X * t)
    (algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ])) (j + 1)
  have hB : (algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1)) • n' ∈ P.N' := h n' hn'
  rw [hγy] at h2
  generalize algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ]) = u' at h2 hr ⊢
  generalize algebraMap ℤ_[ℓ] A c = c' at h2 hA hB ⊢
  have hr' : (u' + G.X * t) ^ (j + 1) = u' ^ (j + 1) + G.X * (t * r) := by
    rw [sub_eq_iff_eq_add] at hr
    rw [hr]
    ring
  generalize u' + G.X * t = q at h2 hr'
  have key : (c' * (u' ^ (j + 1) - 1) * G.X ^ j) • n =
      z - (t * r) • ((c' * G.X ^ (j + 1)) • n) - q ^ (j + 1) • ((c' * G.X ^ (j + 1)) • n') := by
    rw [← h2]
    linear_combination (norm := module) (-(c' * G.X ^ j) * hr') • n
  rw [key]
  exact P.N'.sub_mem (P.N'.sub_mem hz (P.N'.smul_mem _ hA)) (P.N'.smul_mem _ hB)

private theorem w3_lemma_4 {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {G : GBase ℓ A}
    {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (s j : ℕ) (hjs : j ≤ s) (h : P.Kills (G.X ^ s)) :
    P.Kills (algebraMap ℤ_[ℓ] A (∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1)) * G.X ^ j) := by
  have main : ∀ d, d ≤ s - j → P.Kills (algebraMap ℤ_[ℓ] A
      (∏ k ∈ Finset.Ioc (s - d) s, ((G.u : ℤ_[ℓ]) ^ k - 1)) * G.X ^ (s - d)) := by
    intro d
    induction d with
    | zero =>
      intro _
      simpa using h
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have hsd : s - d = (s - (d + 1)) + 1 := by omega
      rw [hsd] at h1
      have h2 := w3_lemma_3 G P _ (s - (d + 1)) h1
      have hmem : s - (d + 1) + 1 ∈ Finset.Ioc (s - (d + 1)) s := by
        simp only [Finset.mem_Ioc]
        omega
      have hprod : ∏ k ∈ Finset.Ioc (s - (d + 1)) s, ((G.u : ℤ_[ℓ]) ^ k - 1) =
          (∏ k ∈ Finset.Ioc (s - (d + 1) + 1) s, ((G.u : ℤ_[ℓ]) ^ k - 1)) *
            ((G.u : ℤ_[ℓ]) ^ (s - (d + 1) + 1) - 1) := by
        rw [← Finset.mul_prod_erase _ _ hmem, mul_comm]
        congr 1
        apply Finset.prod_congr _ (fun _ _ => rfl)
        ext x
        simp only [Finset.mem_erase, Finset.mem_Ioc]
        omega
      rw [hprod]
      exact h2
  have := main (s - j) le_rfl
  rwa [show s - (s - j) = j by omega] at this

theorem cost_bound_kills_obstruction : StatCostKills := by
  intro ℓ _ hℓ A _ _ G D _ _ _ _ P s j hgen hjs h
  have hd := w3_lemma_4 P s j hjs h
  have hfac : ∀ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1) ≠ 0 ∧
      PadicInt.valuation ((G.u : ℤ_[ℓ]) ^ k - 1) = if (ℓ - 1) ∣ k then 1 + padicValNat ℓ k else 0 := by
    intro k hk
    simp only [Finset.mem_Ioc] at hk
    exact character_value_formula_holds ℓ hℓ G.u hgen k (by omega)
  have hPr0 : ∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k hk => (hfac k hk).1)
  have hval : (∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1)).valuation = cost ℓ j s := by
    have e := Finset.emultiplicity_prod PadicInt.prime_p (Finset.Ioc j s) (fun k => (G.u : ℤ_[ℓ]) ^ k - 1)
    rw [w3_lemma hPr0, Finset.sum_congr rfl (fun k hk => by rw [w3_lemma (hfac k hk).1, (hfac k hk).2])] at e
    unfold cost
    exact_mod_cast e
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, ∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1) =
      (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ cost ℓ j s :=
    ⟨PadicInt.unitCoeff hPr0, by rw [← hval]; exact PadicInt.unitCoeff_spec hPr0⟩
  have heq : (ℓ : A) ^ cost ℓ j s * G.X ^ j = algebraMap ℤ_[ℓ] A ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) *
      (algebraMap ℤ_[ℓ] A (∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1)) * G.X ^ j) := by
    rw [hu, ← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow, map_natCast]
  rw [heq]
  exact w3_lemma_2 P _ hd

theorem first_descent_of_cost_bound (hB : StatCostBound) : Stat1 := by
  intro ℓ _ hℓ A _ _ G D _ _ _ _ P s H a j hgen hsH hk ha
  by_cases hjs : j ≤ s
  · have hc := cost_bound_kills_obstruction ℓ hℓ A G D P s j hgen hjs hk
    have hb := hB ℓ hℓ j s H hjs hsH
    have hcw : 1 + Real.logb ℓ ((H : ℝ) + 1) ≤ (cW ℓ H : ℝ) := by
      unfold cW
      exact Nat.le_ceil _
    have hlt : (cost ℓ j s : ℝ) < a := by linarith
    have hle : cost ℓ j s ≤ a := by exact_mod_cast hlt.le
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [show (ℓ : A) ^ (cost ℓ j s + e) * G.X ^ j = (ℓ : A) ^ e * ((ℓ : A) ^ cost ℓ j s * G.X ^ j) by ring]
    exact w3_lemma_2 P _ hc
  · push Not at hjs
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hjs
    rw [show (ℓ : A) ^ a * G.X ^ (s + e + 1) = ((ℓ : A) ^ a * G.X ^ (e + 1)) * G.X ^ s by ring]
    exact w3_lemma_2 P _ hk

theorem wA_of (h1 : Stat1) : StatWA := by
  intro ℓ _ hℓ A _ _ G D _ _ _ _ P H hgen hk
  suffices hnum : ((H : ℝ) - ((0 : ℕ) : ℝ)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H ≤ (eWA ℓ H : ℝ) by
    simpa using h1 ℓ hℓ A G D P H H (eWA ℓ H) 0 hgen le_rfl hk hnum
  have hl : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hlog : 0 ≤ Real.logb ℓ ((H : ℝ) + 1) := Real.logb_nonneg hl (by linarith)
  have hc : (cW ℓ H : ℝ) < 1 + Real.logb ℓ ((H : ℝ) + 1) + 1 := by
    unfold cW
    exact Nat.ceil_lt_add_one (by linarith)
  have hq : 0 ≤ (H : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 := div_nonneg (mul_nonneg hH (by linarith)) (sq_nonneg _)
  have hf : (H : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 3 + Real.logb ℓ ((H : ℝ) + 1) < (eWA ℓ H : ℝ) + 1 := by
    unfold eWA
    exact Nat.lt_floor_add_one _
  simp only [Nat.cast_zero, sub_zero]
  linarith

theorem second_descent_free_part_holds : Stat2Free := by
  intro ℓ A _ D D' _ _ _ _ S hPP hgen hl hind x hx hφx
  let T : Set D' := {w | ∃ y : Fin ℓ → D, (∀ k, y k ∈ S.P') ∧ w = ∑ k : Fin ℓ, S.π ^ (k : ℕ) • S.φ (y k)}
  have hT0 : (0 : D') ∈ T := ⟨0, fun _ => S.P'.zero_mem, by simp⟩
  have hTadd : ∀ w₁ ∈ T, ∀ w₂ ∈ T, w₁ + w₂ ∈ T := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    exact ⟨y₁ + y₂, fun k => S.P'.add_mem (hy₁ k) (hy₂ k), by
      simp [map_add (f := _), smul_add, Finset.sum_add_distrib]⟩
  have hTsum : ∀ (s : Finset (Fin ℓ)) (f : Fin ℓ → D'), (∀ k ∈ s, f k ∈ T) → ∑ k ∈ s, f k ∈ T := by
    intro s f
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using hT0
    | insert a s ha ih =>
      intro hf
      rw [Finset.sum_insert ha]
      exact hTadd _ (hf a (Finset.mem_insert_self a s)) _
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
  have hL : ∀ (g : A) (y : D), y ∈ S.P' → g • S.φ y ∈ T := by
    intro g y hy
    obtain ⟨e, he⟩ := hgen g
    refine ⟨fun k => e k • y, fun k => S.P'.smul_mem _ hy, ?_⟩
    rw [he, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [S.φ_smul, mul_smul]
  have hall : ∀ w ∈ Submodule.span A (S.φ '' (S.P' : Set D)), w ∈ T := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      simpa using hL 1 y hy
    | zero => exact hT0
    | add w₁ w₂ _ _ h₁ h₂ => exact hTadd _ h₁ _ h₂
    | smul g w _ hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [Finset.smul_sum]
      refine hTsum _ _ (fun k _ => ?_)
      rw [smul_smul]
      exact hL _ _ (hy k)
  obtain ⟨y, hy, hxy⟩ := hall _ hφx
  let k0 : Fin ℓ := ⟨0, hl⟩
  have hx' : ∀ k, (if k = k0 then x else 0) - y k ∈ S.P := by
    intro k
    refine S.P.sub_mem ?_ (hPP (hy k))
    split_ifs
    · exact hx
    · exact S.P.zero_mem
  have hterm : ∀ k : Fin ℓ, S.π ^ (k : ℕ) • S.φ (if k = k0 then x else 0) = if k = k0 then S.φ x else 0 := by
    intro k
    split_ifs with hk
    · subst hk
      simp [k0]
    · simp
  have hsum : ∑ k : Fin ℓ, S.π ^ (k : ℕ) • S.φ ((fun k => (if k = k0 then x else 0) - y k) k) = 0 := by
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib]
    rw [← hxy, Finset.sum_congr rfl (fun k _ => hterm k)]
    simp
  have h0 := hind (fun k => (if k = k0 then x else 0) - y k) hx' hsum k0
  have hx0 : x = y k0 := by simpa [sub_eq_zero] using h0
  rw [hx0]
  exact hy k0

end Formalism.RepresentationBoundsCohomology.N2
end
end

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem cost_formula_holds : StatCostFormula := by
  intro ℓ _ hℓ2 j s hjs
  have hℓ : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hd : 0 < ℓ - 1 := by omega
  induction s, hjs using Nat.le_induction with
  | base => simp [cost]
  | succ s hjs ih =>
    have hI : Finset.Ioc j (s + 1) = insert (s + 1) (Finset.Ioc j s) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hnot : s + 1 ∉ Finset.Ioc j s := by simp
    have hc : cost ℓ j (s + 1) =
        cost ℓ j s + (if (ℓ - 1) ∣ (s + 1) then 1 + padicValNat ℓ (s + 1) else 0) := by
      unfold cost
      rw [hI, Finset.sum_insert hnot, add_comm]
    rw [hc]
    by_cases hdv : (ℓ - 1) ∣ (s + 1)
    · rw [if_pos hdv]
      have hq : (s + 1) / (ℓ - 1) = s / (ℓ - 1) + 1 := Nat.succ_div_of_dvd hdv
      have hjq : j / (ℓ - 1) ≤ s / (ℓ - 1) := Nat.div_le_div_right hjs
      have hmul : s + 1 = (ℓ - 1) * (s / (ℓ - 1) + 1) := by
        rw [← hq]
        exact (Nat.mul_div_cancel' hdv).symm
      have hv0 : padicValNat ℓ (ℓ - 1) = 0 := by
        rw [Nat.padicValNat_def]
        exact padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd hd h; omega)
      have hv : padicValNat ℓ (s + 1) = padicValNat ℓ (s / (ℓ - 1) + 1) := by
        rw [hmul, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.pos_iff_ne_zero.1 hd) (Nat.succ_ne_zero _), hv0, zero_add]
      have hf : padicValNat ℓ (s / (ℓ - 1) + 1).factorial =
          padicValNat ℓ (s / (ℓ - 1) + 1) + padicValNat ℓ (s / (ℓ - 1)).factorial := by
        rw [Nat.factorial_succ, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
      rw [hq, hv, hf]
      omega
    · rw [if_neg hdv, add_zero, Nat.succ_div_of_not_dvd hdv]
      exact ih

theorem cost_bound : StatCostBound := by
  intro ℓ _ hℓ j s H hjs hsH
  have hprime : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by have := hprime.two_le; omega
  have hform := cost_formula_holds ℓ hℓ j s hjs
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hform
  have hL2 : 2 ≤ L := by omega
  set k0 := j / L with hk0
  set k1 := s / L with hk1
  have hk01 : k0 ≤ k1 := Nat.div_le_div_right hjs
  obtain ⟨n', hn'⟩ : ∃ n', k1 = k0 + n' := ⟨k1 - k0, by omega⟩
  have hch := Nat.choose_mul_factorial_mul_factorial hk01
  have hvch : padicValNat (L + 1) k1.factorial = padicValNat (L + 1) (k1.choose k0) +
      padicValNat (L + 1) k0.factorial + padicValNat (L + 1) n'.factorial := by
    rw [← hch, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.mul_ne_zero (Nat.choose_pos hk01).ne' (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _), (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.choose_pos hk01).ne' (Nat.factorial_ne_zero _),
      show k1 - k0 = n' by omega]
  have hcost : cost (L + 1) j s = n' + padicValNat (L + 1) n'.factorial +
      padicValNat (L + 1) (k1.choose k0) := by omega
  have hLr : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
  have hsub : (((L + 1 : ℕ) : ℝ) - 1) = L := by push_cast; ring
  have hb1 : (1 : ℝ) < ((L + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hHr : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) := Real.logb_nonneg hb1 (by linarith)
  have hjsr : (j : ℝ) ≤ s := by exact_mod_cast hjs
  rw [hsub]
  have hpos : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos n' with h0 | hpos'
  · have : cost (L + 1) j s = 0 := by
      rw [hcost, h0, hn', h0]; simp [Nat.padicValNat_def]
    rw [this]
    have : 0 ≤ ((s : ℝ) - j) * ((L + 1 : ℕ) : ℝ) / (L : ℝ) ^ 2 := by
      apply div_nonneg _ hpos.le
      apply mul_nonneg (by linarith) (by linarith)
    push_cast at this hlog0 ⊢
    linarith
  ·
    have hw : L * padicValNat (L + 1) n'.factorial < n' := by
      have := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := L + 1) (n := n') hpos'.ne'
      simpa [Nat.padicValNat_def] using this
    have hc : padicValNat (L + 1) (k1.choose k0) ≤ Nat.log (L + 1) k1 := by
      rw [Nat.padicValNat_def, ← Nat.factorization_def _ hprime]
      exact Nat.factorization_choose_le_log
    have hk1pos : 1 ≤ k1 := by
      rw [hn']; exact le_trans hpos' (Nat.le_add_left _ _)
    have hk1H : k1 ≤ H := le_trans (Nat.div_le_self _ _) hsH
    have hlog : (Nat.log (L + 1) k1 : ℝ) ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) := by
      refine le_trans (Real.natLog_le_logb _ _) ?_
      apply Real.logb_le_logb_of_le hb1
      · exact_mod_cast hk1pos
      · have : (k1 : ℝ) ≤ H := by exact_mod_cast hk1H
        linarith
    have h1 : L * k1 ≤ s := Nat.mul_div_le s L
    have h2 : j < L * k0 + L := by
      have := Nat.lt_mul_div_succ j (show 0 < L by omega)
      rw [← hk0] at this
      nlinarith
    have hA : L * n' + j + 1 ≤ s + L := by
      have : L * k1 = L * k0 + L * n' := by rw [hn']; ring
      omega
    set w := padicValNat (L + 1) n'.factorial with hwdef
    set c := padicValNat (L + 1) (k1.choose k0) with hcdef
    have rA : (L : ℝ) * n' + j + 1 ≤ s + L := by exact_mod_cast hA
    have rB : (L : ℝ) * w + 1 ≤ n' := by exact_mod_cast hw
    have rC : (c : ℝ) ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) :=
      le_trans (by exact_mod_cast hc) hlog
    have key : ((n' : ℝ) + w) < ((s : ℝ) - j) * ((L + 1 : ℕ) : ℝ) / (L : ℝ) ^ 2 + 1 := by
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ hpos]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left rA (by linarith : (0 : ℝ) ≤ L),
        mul_le_mul_of_nonneg_left rB (by linarith : (0 : ℝ) ≤ L)]
    rw [hcost]
    push_cast at key rC ⊢
    linarith

theorem unconditional_first_statement : Stat1 := first_descent_of_cost_bound cost_bound

theorem unit_lemma_case_a_unconditional : StatWA := wA_of unconditional_first_statement

end Formalism.RepresentationBoundsCohomology.N2
end
end

section -- merged from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SecondDescentStatementHolds
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem second_descent_statement_holds : Stat2 := by
  intro ℓ _ hℓ2 A _ D D' _ _ _ _ S Mi hi s H h1 h2 h3 h4 h5 n hn
  set t := (s + (ℓ - 2)) / (ℓ - 1) with ht
  set c := cW ℓ H with hc
  have hℓ3 : 3 ≤ ℓ := by
    have := (Fact.out : ℓ.Prime).two_le
    omega
  have hts : s ≤ (ℓ - 1) * t := by
    have e1 := Nat.div_add_mod (s + (ℓ - 2)) (ℓ - 1)
    have e2 := Nat.mod_lt (s + (ℓ - 2)) (show 0 < ℓ - 1 by omega)
    rw [← ht] at e1
    generalize (ℓ - 1) * t = X at *
    omega
  have hℓR : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ3
  have hℓ1 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have htsR : (s : ℝ) ≤ ((ℓ : ℝ) - 1) * t := by
    have := (Nat.cast_le (α := ℝ)).2 hts
    push_cast [hℓ1] at this
    rw [← hℓ1]
    exact_mod_cast hts
  have hkey : ∀ r ∈ S.R, (S.π ^ t * S.q ^ (c + 2 + t)) • r ∈ S.R' := by
    intro r hr
    rw [S.hq, add_pow, Finset.mul_sum, Finset.sum_smul]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    obtain ⟨U, hU⟩ : ∃ U, c + 2 + t - i = U := ⟨_, rfl⟩
    have hU' : c + 2 + t = i + U := by omega
    rw [hU]
    have e : S.π ^ t * (((ℓ : A) * S.w) ^ i * (S.π ^ (ℓ - 1)) ^ U * ((c + 2 + t).choose i : A)) =
        (S.w ^ i * ((c + 2 + t).choose i : A)) * ((ℓ : A) ^ i * S.π ^ ((ℓ - 1) * U + t)) := by
      rw [← pow_mul, pow_add, mul_pow]
      ring
    rw [e, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hj : s ≤ (ℓ - 1) * U + t
    · rw [← Nat.sub_add_cancel hj, pow_add, ← mul_assoc, mul_smul]
      exact Submodule.smul_mem _ _ (h4 r hr)
    · refine h5 i ((ℓ - 1) * U + t) ?_ r hr
      have hU0 : (0 : ℝ) ≤ U := by positivity
      have ht0 : (0 : ℝ) ≤ t := by positivity
      have hiR : (i : ℝ) = c + 2 + t - U := by
        have := congrArg (Nat.cast : ℕ → ℝ) hU'
        push_cast at this
        linarith
      have hpos : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
      have hsl : (s : ℝ) * ℓ ≤ ((ℓ : ℝ) - 1) * t * ℓ := mul_le_mul_of_nonneg_right htsR (by linarith)
      have hcU : (0 : ℝ) ≤ U * ((ℓ : ℝ) - 1) := mul_nonneg hU0 (by linarith)
      have hj' : (((ℓ - 1) * U + t : ℕ) : ℝ) = ((ℓ : ℝ) - 1) * U + t := by
        push_cast [hℓ1]
        ring
      rw [hj', hiR]
      have hdiv : ((s : ℝ) - (((ℓ : ℝ) - 1) * U + t)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤ 2 + t - U := by
        rw [div_le_iff₀ hpos]
        nlinarith
      linarith
  have hR1 := hkey _ (h1 n hn)
  have hR2 : (S.π ^ (Mi + hi + c + 2) * (S.π ^ t * S.q ^ (c + 2 + t))) • (S.q ^ Mi • S.φ n) ∈ S.R' := by
    rw [mul_smul]
    exact Submodule.smul_mem _ _ hR1
  have hsp := h2 _ hR2
  have hφ : S.φ (S.π ^ (Mi + hi + c + 2 + t) • n) = S.q ^ hi •
      ((S.π ^ (Mi + hi + c + 2) * (S.π ^ t * S.q ^ (c + 2 + t))) • (S.q ^ Mi • S.φ n)) := by
    rw [S.φ_smul, map_pow, S.φπ, smul_smul, smul_smul]
    congr 1
    ring
  apply h3 _ (Submodule.smul_mem _ _ hn)
  rw [hφ]
  exact hsp

end Formalism.RepresentationBoundsCohomology.N2
end
end

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem unit_lemma_prime_case_holds : StatWPrime := by
  intro ℓ _ hℓ A _ _ G n _ D _ _ _ _ Λ Mi hi s H hgen hM hh hgen2 hind hKH hs
  have hsH : ∀ i, s i ≤ H := fun i => (hs i).2 H (hKH i)
  have hℓ3 : 3 ≤ ℓ := by
    have h2 := (Fact.out : ℓ.Prime).two_le
    omega
  have part1 : ∀ i, s (i - 1) ≤ Mi i + hi i + cW ℓ H + 2 + (s i + (ℓ - 2)) / (ℓ - 1) := by
    intro i
    let S : PhiStep ℓ A D D :=
      { φA := Λ.φA, π := G.X, q := Λ.q, w := Λ.w, φπ := Λ.φπ, hq := Λ.hq, φ := Λ.φ i,
        φ_smul := Λ.φ_smul i, P := (Λ.pair (i - 1)).N, P' := (Λ.pair (i - 1)).N',
        R := (Λ.pair i).N, R' := (Λ.pair i).N' }
    have hc := second_descent_free_part_holds ℓ A D D S (Λ.pair (i - 1)).le hgen2 (by omega) (hind i)
    have he : ∀ a j : ℕ, ((s i : ℝ) - j) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H ≤ a →
        ∀ r ∈ S.R, ((ℓ : A) ^ a * S.π ^ j) • r ∈ S.R' := fun a j ha =>
      unconditional_first_statement ℓ hℓ A G D (Λ.pair i) (s i) H a j hgen (hsH i) (hs i).1 ha
    have key := second_descent_statement_holds ℓ hℓ A D D S (Mi i) (hi i) (s i) H (hM i) (hh i) hc (hs i).1 he
    exact (hs (i - 1)).2 (Mi i + hi i + cW ℓ H + 2 + (s i + (ℓ - 2)) / (ℓ - 1)) key
  have part2 : ∀ (i : ZMod n) (m : ℕ), (s i : ℝ) ≤
      (∑ a ∈ Finset.range m, (((Mi (i + ((a + 1 : ℕ) : ZMod n)) + hi (i + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)
        + cW ℓ H + 3) / ((ℓ : ℝ) - 1) ^ a) + (s (i + (m : ZMod n)) : ℝ) / ((ℓ : ℝ) - 1) ^ m := by
    intro i m
    have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
    refine residue_finite_holds n (ℓ : ℝ) (cW ℓ H : ℝ) (fun k => (s k : ℝ))
      (fun k => ((Mi k + hi k : ℕ) : ℝ)) hℓR ?_ i m
    intro k
    have h1 := part1 k
    have hℓ1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
    have hdiv : (((s k + (ℓ - 2)) / (ℓ - 1) : ℕ) : ℝ) ≤ (s k : ℝ) / ((ℓ : ℝ) - 1) + 1 := by
      calc (((s k + (ℓ - 2)) / (ℓ - 1) : ℕ) : ℝ)
          ≤ ((s k + (ℓ - 2) : ℕ) : ℝ) / ((ℓ - 1 : ℕ) : ℝ) := Nat.cast_div_le
        _ = ((s k : ℝ) + ((ℓ : ℝ) - 2)) / ((ℓ : ℝ) - 1) := by
          push_cast [Nat.cast_sub (show 2 ≤ ℓ by omega), Nat.cast_sub (show 1 ≤ ℓ by omega)]
          try ring
        _ ≤ (s k : ℝ) / ((ℓ : ℝ) - 1) + 1 := by
          rw [add_div]
          have : ((ℓ : ℝ) - 2) / ((ℓ : ℝ) - 1) ≤ 1 := by rw [div_le_one hℓ1]; linarith
          linarith
    have h1R : (s (k - 1) : ℝ) ≤
        ((Mi k + hi k + cW ℓ H + 2 + (s k + (ℓ - 2)) / (ℓ - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_add] at h1R
    show (s (k - 1) : ℝ) ≤ ((Mi k + hi k : ℕ) : ℝ) + (cW ℓ H : ℝ) + 3 + (s k : ℝ) / ((ℓ : ℝ) - 1)
    rw [Nat.cast_add]
    norm_num at h1R ⊢
    linarith
  have part3 : ∀ i, (Λ.pair i).Kills ((ℓ : A) ^ cost ℓ 0 (s i)) ∧
      (cost ℓ 0 (s i) : ℝ) < (s i : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H := by
    intro i
    refine ⟨?_, ?_⟩
    · have h := cost_bound_kills_obstruction ℓ hℓ A G D (Λ.pair i) (s i) 0 hgen (Nat.zero_le _) (hs i).1
      simpa using h
    · have h := cost_bound ℓ hℓ 0 (s i) H (Nat.zero_le _) (hsH i)
      have hc : 1 + Real.logb ℓ ((H : ℝ) + 1) ≤ (cW ℓ H : ℝ) := Nat.le_ceil _
      simp only [Nat.cast_zero, sub_zero] at h
      linarith
  have part4 : ∀ (i : ZMod n) (j : ℕ) (Gw : ℝ), 0 ≤ Gw →
      (∀ k : ℕ, 1 ≤ k → k ≤ j → ((Mi (i + (k : ZMod n)) + hi (i + (k : ZMod n)) : ℕ) : ℝ) ≤ 2 * Gw) →
      (s i : ℝ) ≤ (2 * Gw + cW ℓ H + 3) * ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) +
        (H : ℝ) / ((ℓ : ℝ) - 1) ^ j := by
    intro i j Gw hGw hb
    have h2 := part2 i j
    have hℓ3R : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ3
    have hL : (1 : ℝ) < (ℓ : ℝ) - 1 := by linarith
    have hLpos : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
    have hK0 : (0 : ℝ) ≤ 2 * Gw + cW ℓ H + 3 := by positivity
    set K : ℝ := 2 * Gw + cW ℓ H + 3 with hK
    have hsum : (∑ a ∈ Finset.range j, (((Mi (i + ((a + 1 : ℕ) : ZMod n)) +
        hi (i + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) + cW ℓ H + 3) / ((ℓ : ℝ) - 1) ^ a) ≤
        ∑ a ∈ Finset.range j, K / ((ℓ : ℝ) - 1) ^ a := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : a < j := Finset.mem_range.mp ha
      have hak := hb (a + 1) (by omega) (by omega)
      apply div_le_div_of_nonneg_right _ (pow_pos hLpos a).le
      rw [hK]
      linarith
    have hgeom := geom_id K ((ℓ : ℝ) - 1) hL j
    have htail : 0 ≤ K * ((ℓ : ℝ) - 1) / (((ℓ : ℝ) - 1 - 1) * ((ℓ : ℝ) - 1) ^ j) := by
      apply div_nonneg (mul_nonneg hK0 hLpos.le)
      exact mul_nonneg (by linarith) (pow_pos hLpos j).le
    have hsH' : (s (i + (j : ZMod n)) : ℝ) / ((ℓ : ℝ) - 1) ^ j ≤ (H : ℝ) / ((ℓ : ℝ) - 1) ^ j :=
      div_le_div_of_nonneg_right (by exact_mod_cast hsH _) (pow_pos hLpos j).le
    have heq : K * ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1 - 1) = K * ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) := by
      rw [show (ℓ : ℝ) - 1 - 1 = (ℓ : ℝ) - 2 by ring]
    linarith
  exact ⟨part1, part2, part3, part4⟩

end Formalism.RepresentationBoundsCohomology.N2
