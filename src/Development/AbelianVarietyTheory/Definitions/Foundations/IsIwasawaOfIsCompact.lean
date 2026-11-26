module

public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.CobOn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
noncomputable section

namespace GlobalTheory.Doubling

open scoped NNReal
open MeasureTheory

section Iwasawa

variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)

theorem hom_pos {H : Type} [Group H] (δ : H →* ℝ≥0) (p : H) : 0 < δ p :=
  pos_iff_ne_zero.2 ((Group.isUnit p).map δ).ne_zero

def IsIwasawa : Prop := (∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) ∧ ∀ p : P, (p : G) ∈ K → δ p = 1


open Classical in
def iwAbs (g : G) : ℝ≥0 := by
  classical
  exact if h : ∃ p : P, ∃ k ∈ K, g = p * k then δ h.choose else 1

theorem iwAbs_pos (g : G) : 0 < iwAbs (δ := δ) (K := K) g := by
  unfold iwAbs; split_ifs
  · exact hom_pos δ _
  · exact one_pos

variable {δ K}

theorem iwAbs_mul_of_triv (h : ∀ p : P, (p : G) ∈ K → δ p = 1) (p : P) {k : G} (hk : k ∈ K) :
    iwAbs (δ := δ) (K := K) (p * k) = δ p := by
  have e : ∃ p' : P, ∃ k' ∈ K, (p : G) * k = p' * k' := ⟨p, k, hk, rfl⟩
  rw [iwAbs, dite_eq_left e]
  obtain ⟨k', hk', e'⟩ := e.choose_spec
  have h1 := h (p⁻¹ * e.choose) (by
    have : ((p⁻¹ * e.choose : P) : G) = k * k'⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq, mul_assoc, ← e', inv_mul_cancel_left]
    rw [this]; exact mul_mem hk (inv_mem hk'))
  rw [← mul_inv_cancel_left p e.choose, map_mul, h1, mul_one]

namespace IsIwasawa

variable (h : IsIwasawa δ K)
include h

theorem iwAbs_mul (p : P) {k : G} (hk : k ∈ K) : iwAbs (δ := δ) (K := K) (p * k) = δ p := iwAbs_mul_of_triv h.2 p hk

theorem iwAbs_coe (p : P) : iwAbs (δ := δ) (K := K) p = δ p := by simpa using h.iwAbs_mul p (one_mem K)

theorem iwAbs_of_mem {k : G} (hk : k ∈ K) : iwAbs (δ := δ) (K := K) k = 1 := by simpa using h.iwAbs_mul 1 hk

theorem iwAbs_left (p : P) (g : G) : iwAbs (δ := δ) (K := K) (p * g) = δ p * iwAbs (δ := δ) (K := K) g := by
  obtain ⟨p', k, hk, rfl⟩ := h.1 g
  rw [← mul_assoc, ← Subgroup.coe_mul, h.iwAbs_mul _ hk, h.iwAbs_mul _ hk, map_mul]

theorem iwAbs_right (g : G) {k : G} (hk : k ∈ K) : iwAbs (δ := δ) (K := K) (g * k) = iwAbs (δ := δ) (K := K) g := by
  obtain ⟨p', k', hk', rfl⟩ := h.1 g
  rw [mul_assoc, h.iwAbs_mul _ (mul_mem hk' hk), h.iwAbs_mul _ hk']

end IsIwasawa

variable [TopologicalSpace G] [IsTopologicalGroup G]


omit [IsTopologicalGroup G] in
theorem triv_of_isCompact (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) (p : P)
    (hp : (p : G) ∈ K) : δ p = 1 := by
  obtain ⟨C, hC⟩ := ((hP.isClosedEmbedding_subtypeVal.isCompact_preimage hK).image hδ).bddAbove
  have key : ∀ q : P, (q : G) ∈ K → δ q ≤ 1 := fun q hq => by
    by_contra hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hc)
    exact absurd (hC ⟨q ^ n, pow_mem hq n, map_pow δ q n⟩) (not_le.2 hn)
  refine le_antisymm (key p hp) ?_
  have := key p⁻¹ (inv_mem hp)
  rwa [map_inv, inv_le_one₀ (hom_pos δ p)] at this

omit [IsTopologicalGroup G] in
theorem isIwasawa_of_isCompact (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) : IsIwasawa δ K := ⟨h, triv_of_isCompact hP hδ hK⟩

theorem continuous_of_prod (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) {X : Type} [TopologicalSpace X] {f : G → X}
    (hf : Continuous fun x : P × K => f (x.1 * x.2)) : Continuous f := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e : G × K ≃ₜ G × K :=
    { toFun := fun x => (x.1 * x.2, x.2), invFun := fun x => (x.1 * (x.2 : G)⁻¹, x.2)
      left_inv := fun x => by simp, right_inv := fun x => by simp
      continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }
  have hc : IsClosedMap fun x : P × K => (x.1 : G) * x.2 :=
    (isClosedMap_fst_of_compactSpace.comp e.isClosedMap).comp
      (hP.isClosedEmbedding_subtypeVal.prodMap (Topology.IsClosedEmbedding.id (X := K))).isClosedMap
  exact (hc.isQuotientMap (by fun_prop) fun g => by
    obtain ⟨p, k, hk, rfl⟩ := h g; exact ⟨(p, ⟨k, hk⟩), rfl⟩).continuous_iff.2 hf

theorem IsIwasawa.continuous_iwAbs (h : IsIwasawa δ K) (hP : IsClosed (P : Set G)) (hδ : Continuous δ)
    (hK : IsCompact (K : Set G)) : Continuous (iwAbs (δ := δ) (K := K)) :=
  continuous_of_prod hP hK h.1 ((hδ.comp continuous_fst).congr fun x => (h.iwAbs_mul x.1 x.2.2).symm)

end Iwasawa

def npow (r : ℝ≥0) (t : ℂ) : ℂ := ((r : ℝ) : ℂ) ^ t

theorem npow_mul (r r' : ℝ≥0) (t : ℂ) : npow (r * r') t = npow r t * npow r' t := by
  rw [npow, NNReal.coe_mul, Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg r.2 r'.2 t

theorem npow_add {r : ℝ≥0} (hr : 0 < r) (t t' : ℂ) : npow r (t + t') = npow r t * npow r t' :=
  Complex.cpow_add _ _ (by exact_mod_cast hr.ne')

@[simp] theorem npow_zero (r : ℝ≥0) : npow r 0 = 1 := Complex.cpow_zero _
@[simp] theorem one_npow (t : ℂ) : npow 1 t = 1 := by simp [npow]

theorem norm_npow {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : ‖npow r t‖ = (r : ℝ) ^ t.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hr t

theorem npow_ne_zero {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_npow hr]; exact (Real.rpow_pos_of_pos hr _).ne'

theorem npow_eq_exp {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r t = Complex.exp (Real.log r * t) := by
  rw [npow, Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log r.coe_nonneg]

theorem continuous_npow {X : Type} [TopologicalSpace X] {f : X → ℝ≥0} (hf : Continuous f) (h : ∀ x, 0 < f x) (t : ℂ) :
    Continuous fun x => npow (f x) t := by
  simp only [npow_eq_exp (h _)]
  exact ((Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp hf).log fun x => (NNReal.coe_pos.2 (h x)).ne')).mul continuous_const).cexp

section Induced

variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)

def IndLaw (Φ : G → ℂ) : Prop := ∀ (p : P) (g : G), Φ (p * g) = χ p * npow (δ p) t * Φ g

def kSpan (Φ : G → ℂ) : Submodule ℂ (G → ℂ) := Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = fun g => Φ (g * k)}

def IsKFinite (Φ : G → ℂ) : Prop := FiniteDimensional ℂ (kSpan K Φ)

variable {K}

theorem isKFinite_iff {Φ : G → ℂ} : IsKFinite K Φ ↔
    ∃ W : Submodule ℂ (G → ℂ), FiniteDimensional ℂ W ∧ ∀ k ∈ K, (fun g => Φ (g * k)) ∈ W :=
  ⟨fun h => ⟨_, h, fun k hk => Submodule.subset_span ⟨k, hk, rfl⟩⟩, fun ⟨_, _, h⟩ =>
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact h k hk))⟩

theorem IsKFinite.of_invariant {Φ : G → ℂ} (h : ∀ g, ∀ k ∈ K, Φ (g * k) = Φ g) : IsKFinite K Φ :=
  isKFinite_iff.2 ⟨ℂ ∙ Φ, inferInstance, fun k hk => by
    rw [show (fun g => Φ (g * k)) = Φ from funext fun g => h g k hk]; exact Submodule.mem_span_singleton_self _⟩

theorem IsKFinite.add {Φ Ψ : G → ℂ} (h : IsKFinite K Φ) (h' : IsKFinite K Ψ) : IsKFinite K (Φ + Ψ) := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  obtain ⟨W', _, hW'⟩ := isKFinite_iff.1 h'
  exact isKFinite_iff.2 ⟨W ⊔ W', inferInstance, fun k hk => Submodule.add_mem_sup (hW k hk) (hW' k hk)⟩

theorem IsKFinite.mul_invariant {Φ f : G → ℂ} (h : IsKFinite K Φ) (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    IsKFinite K fun g => Φ g * f g := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  refine isKFinite_iff.2 ⟨W.map (LinearMap.mulRight ℂ f), inferInstance, fun k hk => ⟨_, hW k hk, funext fun g => ?_⟩⟩
  simp [hf g k hk]

theorem IsKFinite.translate {Φ : G → ℂ} (h : IsKFinite K Φ) {k : G} (hk : k ∈ K) : IsKFinite K fun g => Φ (g * k) := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  exact isKFinite_iff.2 ⟨W, inferInstance, fun k' hk' => by simpa only [mul_assoc] using hW _ (mul_mem hk' hk)⟩

variable (K)

def indSpace [TopologicalSpace G] : Submodule ℂ (G → ℂ) where
  carrier := {Φ | IndLaw δ χ t Φ ∧ Continuous Φ ∧ IsKFinite K Φ}
  zero_mem' := ⟨fun _ _ => by simp, continuous_zero, .of_invariant fun _ _ _ => rfl⟩
  add_mem' := fun h h' => ⟨fun p g => by simp only [Pi.add_apply, h.1 p g, h'.1 p g, mul_add],
    h.2.1.add h'.2.1, h.2.2.add h'.2.2⟩
  smul_mem' := fun c Φ h => ⟨fun p g => by simp only [Pi.smul_apply, h.1 p g, smul_eq_mul]; ring,
    h.2.1.const_smul c, by
      have := h.2.2.mul_invariant (f := fun _ => c) fun _ _ _ => rfl
      simp only [mul_comm _ c] at this
      exact this⟩

def flatSec (Φ : G → ℂ) (s₀ s : ℂ) : G → ℂ := fun g => Φ g * npow (iwAbs (δ := δ) (K := K) g) (s - s₀)

variable {δ K χ t}

@[simp] theorem flatSec_self (Φ : G → ℂ) (s₀ : ℂ) : flatSec (δ := δ) (K := K) Φ s₀ s₀ = Φ := funext fun g => by simp [flatSec]

namespace IsIwasawa

variable (h : IsIwasawa δ K)
include h

theorem indLaw_flatSec {Φ : G → ℂ} {ρ s₀ : ℂ} (hΦ : IndLaw δ χ (s₀ + ρ) Φ) (s : ℂ) :
    IndLaw δ χ (s + ρ) (flatSec (δ := δ) (K := K) Φ s₀ s) := fun p g => by
  rw [flatSec, flatSec, hΦ, h.iwAbs_left, npow_mul, show s + ρ = (s₀ + ρ) + (s - s₀) by ring,
    npow_add (hom_pos δ p) _ (s - s₀)]
  ring

theorem norm_le {Φ : G → ℂ} (hΦ : IndLaw δ χ t Φ) {C : ℝ} (hC : ∀ k ∈ K, ‖Φ k‖ ≤ C) (g : G) :
    ‖Φ g‖ ≤ C * (iwAbs (δ := δ) (K := K) g : ℝ) ^ t.re := by
  obtain ⟨p, k, hk, rfl⟩ := h.1 g
  rw [hΦ, h.iwAbs_mul _ hk, norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_npow (hom_pos δ p), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC k hk) (by positivity)

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem flatSec_mem (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) {Φ : G → ℂ}
    {ρ s₀ : ℂ} (hΦ : Φ ∈ indSpace δ K χ (s₀ + ρ)) (s : ℂ) : flatSec (δ := δ) (K := K) Φ s₀ s ∈ indSpace δ K χ (s + ρ) :=
  ⟨h.indLaw_flatSec hΦ.1 s, hΦ.2.1.mul (continuous_npow (h.continuous_iwAbs hP hδ hK) (iwAbs_pos (δ := δ) (K := K)) _),
    hΦ.2.2.mul_invariant (f := fun g => npow (iwAbs (δ := δ) (K := K) g) (s - s₀)) fun g k hk => by rw [h.iwAbs_right g hk]⟩

theorem npow_iwAbs_mem (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) (t : ℂ) :
    (fun g => npow (iwAbs δ K g) t) ∈ indSpace δ K 1 t :=
  ⟨fun p g => by simp [h.iwAbs_left, npow_mul], continuous_npow (h.continuous_iwAbs hP hδ hK) (iwAbs_pos (δ := δ) (K := K)) _,
    .of_invariant fun g k hk => by rw [h.iwAbs_right g hk]⟩

end IsIwasawa

end Induced

section ZetaNonvanishing₂

variable {H : Type} {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def coef (π : H → X → X) (x y : X) : H → ℂ := fun g => inner ℂ y (π g x)

variable [MeasurableSpace H] (m : Measure H)

def pairInt (f c : H → ℂ) : ℂ := ∫ g, f g * starRingEnd ℂ (c g) ∂m

def PairConv (f c : H → ℂ) : Prop := Integrable (fun g => f g * starRingEnd ℂ (c g)) m

end ZetaNonvanishing₂

end GlobalTheory.Doubling

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
noncomputable section

open scoped UpperHalfPlane

namespace GlobalTheory.Sieg.Model

theorem exponent_exact {c : ℕ} (h : Nat.Coprime c 6) :
    12 * ((c ^ 2 - 1) / 12) + 1 = c ^ 2 ∧ 2 * (((c : ℤ) - (c : ℤ) ^ 2) / 2) = (c : ℤ) - (c : ℤ) ^ 2 := by
  constructor
  · have h2 : ¬ 2 ∣ c := fun hh => by
      have := Nat.dvd_gcd hh (show 2 ∣ 6 by norm_num); rw [h] at this; omega
    have h3 : ¬ 3 ∣ c := fun hh => by
      have := Nat.dvd_gcd hh (show 3 ∣ 6 by norm_num); rw [h] at this; omega
    have h12 : c ^ 2 % 12 = 1 := by
      rw [Nat.pow_mod]
      have : c % 12 = 1 ∨ c % 12 = 5 ∨ c % 12 = 7 ∨ c % 12 = 11 := by omega
      rcases this with h | h | h | h <;> rw [h]
    omega
  · apply Int.mul_ediv_cancel'
    have : (c : ℤ) - (c : ℤ) ^ 2 = -((c : ℤ) * (c - 1)) := by ring
    rw [this]
    exact (dvd_neg).2 (Int.even_mul_pred_self (c : ℤ)).two_dvd

theorem ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

theorem ee_add (z w : ℂ) : ee (z + w) = ee z * ee w := by
  simp only [ee, mul_add, Complex.exp_add]

theorem ee_nat_mul (n : ℕ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  simp only [ee, ← Complex.exp_nat_mul]; congr 1; ring

theorem ee_neg (z : ℂ) : ee (-z) = (ee z)⁻¹ := by
  simp only [ee, ← Complex.exp_neg]; congr 1; ring

theorem norm_ee (z : ℂ) : ‖ee z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  simp [ee, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem norm_ee_lt_one (τ : ℍ) : ‖ee τ‖ < 1 := by
  rw [norm_ee, Real.exp_lt_one_iff]
  have := τ.im_pos
  have h : 0 < 2 * Real.pi * (τ : ℂ).im := by
    have := Real.pi_pos
    simp only [UpperHalfPlane.coe_im]; positivity
  linarith

theorem ee_eq_one {a b : ℚ} (τ : ℍ) (h : ee ((a : ℂ) * τ + b) = 1) : a = 0 ∧ ∃ n : ℤ, (n : ℚ) = b := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h1 : (a : ℂ) * τ + b = n := by
    apply mul_left_cancel₀ hp; rw [hn]; ring
  have him := congrArg Complex.im h1
  simp at him
  have ha : a = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h τ.im_pos.ne'
  refine ⟨ha, n, ?_⟩
  subst ha
  simp at h1
  exact_mod_cast h1.symm

theorem ne_one_of_not_int {y : Fin 2 → ℚ}
    (hy : ¬ (y 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ y 1 ∈ Set.range ((↑) : ℤ → ℚ))) (τ : ℍ) (m : ℕ) :
    1 - ee τ ^ m * ee (pt y τ) ≠ 0 ∧ 1 - ee τ ^ m * (ee (pt y τ))⁻¹ ≠ 0 := by
  constructor
  · intro h
    have h' : ee ((((m : ℚ) + y 0 : ℚ) : ℂ) * τ + (y 1 : ℚ)) = 1 := by
      rw [sub_eq_zero, ← ee_nat_mul, ← ee_add] at h
      rw [h]; congr 1; simp [pt]; ring
    obtain ⟨h0, n, hn⟩ := ee_eq_one τ h'
    exact hy ⟨⟨-m, by push_cast; linarith⟩, ⟨n, hn⟩⟩
  · intro h
    have h' : ee ((((m : ℚ) - y 0 : ℚ) : ℂ) * τ + (-y 1 : ℚ)) = 1 := by
      rw [sub_eq_zero, ← ee_nat_mul, ← ee_neg, ← ee_add] at h
      rw [h]; congr 1; simp [pt]; ring
    obtain ⟨h0, n, hn⟩ := ee_eq_one τ h'
    exact hy ⟨⟨m, by push_cast; linarith⟩, ⟨-n, by push_cast; linarith⟩⟩

theorem hasProd_geom {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) (h : ∀ m : ℕ, 1 - q ^ (m + 1) * a ≠ 0) :
    ∃ P : ℂ, P ≠ 0 ∧ HasProd (fun m : ℕ => 1 - q ^ (m + 1) * a) P := by
  have hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * a)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_succ]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _).mul_right _
  refine ⟨∏' m : ℕ, (1 + -(q ^ (m + 1) * a)), ?_, ?_⟩
  · exact tprod_one_add_ne_zero_of_summable (fun m => by simpa [sub_eq_add_neg] using h m) hs
  · simpa [sub_eq_add_neg] using (multipliable_one_add_of_summable hs).hasProd

theorem hasProd_inv {f : ℕ → ℂ} {P : ℂ} (h : HasProd f P) (hP : P ≠ 0) : HasProd (fun m => (f m)⁻¹) P⁻¹ := by
  have := Filter.Tendsto.inv₀ h hP
  simpa [HasProd, Finset.prod_inv_distrib] using this

theorem hasProd_pow {f : ℕ → ℂ} {P : ℂ} (h : HasProd f P) (k : ℕ) : HasProd (fun m => (f m) ^ k) (P ^ k) := by
  have := Filter.Tendsto.pow h k
  simpa [HasProd, Finset.prod_pow] using this

theorem ee_pt_pow (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ee (pt x τ) ^ c = ee (pt (c • x) τ) := by
  rw [← ee_nat_mul]; congr 1; simp [pt]; ring

theorem multipliable_and_sg_ne_zero {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    Multipliable (fun m : ℕ => cthFac c (ee τ) (ee (pt x τ)) (m + 1)) ∧ 1 - ee (pt x τ) ^ c ≠ 0 ∧ sg c x τ ≠ 0 := by
  have hc : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa using h.2.2
  have hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact h.2.2 ⟨⟨c * a, by rw [← ha]; push_cast; ring⟩, ⟨c * b, by rw [← hb]; push_cast; ring⟩⟩
  have hq := norm_ee_lt_one τ
  obtain ⟨A, hA, pA⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hx τ (m + 1)).1
  obtain ⟨B, hB, pB⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hx τ (m + 1)).2
  obtain ⟨C, hC, pC⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hc τ (m + 1)).1
  obtain ⟨D, hD, pD⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hc τ (m + 1)).2
  have hP : HasProd (fun m : ℕ => cthFac c (ee τ) (ee (pt x τ)) (m + 1)) (A ^ (c ^ 2) * B ^ (c ^ 2) * (C * D)⁻¹) := by
    have := ((hasProd_pow pA (c ^ 2)).mul (hasProd_pow pB (c ^ 2))).mul (hasProd_inv (pC.mul pD) (mul_ne_zero hC hD))
    simpa only [cthFac, ee_pt_pow, div_eq_mul_inv] using this
  have h1 : 1 - ee (pt x τ) ^ c ≠ 0 := by
    have := (ne_one_of_not_int hc τ 0).1
    rwa [pow_zero, one_mul, ← ee_pt_pow] at this
  have h2 : 1 - ee (pt x τ) ≠ 0 := by
    have := (ne_one_of_not_int hx τ 0).1
    rwa [pow_zero, one_mul] at this
  refine ⟨hP.multipliable, h1, ?_⟩
  unfold sg cth
  rw [hP.tprod_eq]
  have e1 := ee_ne_zero (τ : ℂ)
  have e2 : -ee (pt x τ) ≠ 0 := neg_ne_zero.2 (ee_ne_zero _)
  refine mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ e1) (zpow_ne_zero _ e2)) (pow_ne_zero _ h2)) h1) ?_
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB)) (inv_ne_zero (mul_ne_zero hC hD))

theorem summable_exp_abs {a : ℝ} (ha : 0 < a) : Summable fun n : ℤ => Real.exp (-(a * |(n : ℝ)|)) := by
  have hs : Summable fun n : ℕ => Real.exp (-(a * n)) := by
    have := summable_geometric_of_lt_one (Real.exp_pos (-a)).le (Real.exp_lt_one_iff.2 (by linarith))
    refine this.congr fun n => ?_
    rw [← Real.exp_nat_mul]; congr 1; ring
  apply Summable.of_nat_of_neg <;> simpa using hs

theorem summable_pow_exp_abs {a : ℝ} (ha : 0 < a) (k : ℕ) (s : ℝ) :
    Summable fun n : ℤ => |s + n| ^ k * Real.exp (-(2 * a * |s + n|)) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((summable_exp_abs ha).mul_left ((k.factorial : ℝ) / a ^ k * Real.exp (a * |s|)))
  have h1 := Real.pow_div_factorial_le_exp (a * |s + n|) (by positivity) k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h2 : |s + n| ^ k ≤ (k.factorial : ℝ) / a ^ k * Real.exp (a * |s + n|) := by
    rw [div_le_iff₀ hk, mul_pow] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have h3 : |(n : ℝ)| ≤ |s + n| + |s| := by
    have := abs_sub (s + n) s
    simpa using this
  calc |s + n| ^ k * Real.exp (-(2 * a * |s + n|))
      ≤ ((k.factorial : ℝ) / a ^ k * Real.exp (a * |s + n|)) * Real.exp (-(2 * a * |s + n|)) := by gcongr
    _ = (k.factorial : ℝ) / a ^ k * Real.exp (-(a * |s + n|)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ (k.factorial : ℝ) / a ^ k * Real.exp (a * |s| + -(a * |(n : ℝ)|)) := by
        gcongr; nlinarith
    _ = _ := by rw [Real.exp_add, mul_assoc]

theorem summable_fTerm (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : Summable (fTerm j x τ) := by
  have hy : 0 < τ.im := τ.im_pos
  have hπ := Real.pi_pos
  have hN : (0 : ℝ) < (x 0).den := by exact_mod_cast (x 0).den_pos
  have s1 := summable_pow_exp_abs (a := Real.pi * τ.im / 2) (by positivity) (j - 1) (x 0 : ℝ)
  have s2 := summable_exp_abs (a := Real.pi * τ.im / (x 0).den) (by positivity)
  refine Summable.of_norm_bounded (s1.mul_of_nonneg s2 (fun _ => by positivity) (fun _ => by positivity)) ?_
  rintro ⟨n, d⟩
  unfold fTerm
  split_ifs with h
  · have hν : x 0 + n ≠ 0 := fun h0 => by simp [h0] at h
    have hd : d ≠ 0 := fun h0 => by simp [h0] at h
    have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast Int.one_le_abs hd
    have hint : ((x 0).den : ℚ) * (x 0 + n) = (((x 0).num + (x 0).den * n : ℤ) : ℚ) := by
      push_cast; rw [mul_add, Rat.den_mul_eq_num]
    have hk0 : ((x 0).num + (x 0).den * n : ℤ) ≠ 0 := fun h0 => by
      rw [h0] at hint
      exact hν (by simpa using hint)
    have hν1 : (1 : ℝ) ≤ (x 0).den * |(x 0 : ℝ) + n| := by
      have h1 : (1 : ℝ) ≤ |((((x 0).num + (x 0).den * n : ℤ) : ℚ) : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
      rw [← hint] at h1
      push_cast at h1
      rwa [abs_mul, abs_of_pos hN] at h1
    have hpos : (0 : ℝ) < ((x 0 : ℝ) + n) * d := by exact_mod_cast h
    have habs : ((x 0 : ℝ) + n) * d = |(x 0 : ℝ) + n| * |(d : ℝ)| := by rw [← abs_mul, abs_of_pos hpos]
    have hs : ‖(Int.sign d : ℂ)‖ = 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast Int.abs_sign_of_ne_zero hd
    have hn : ‖((x 0 + n : ℚ) : ℂ)‖ = |(x 0 : ℝ) + n| := by
      rw [Complex.norm_ratCast]; push_cast; rfl
    simp only [norm_mul, norm_pow, hs, hn, norm_ee, one_mul]
    have i1 : (((x 0 + n : ℚ) : ℂ) * d * (τ : ℂ)).im = ((x 0 : ℝ) + n) * d * τ.im := by
      simp [Complex.mul_im]
    have i2 : ((x 1 : ℂ) * d).im = 0 := by simp [Complex.mul_im]
    rw [i1, i2, habs, mul_zero, neg_zero, Real.exp_zero, mul_one,
      mul_assoc (|(x 0 : ℝ) + n| ^ (j - 1)), ← Real.exp_add]
    gcongr
    set u := |(x 0 : ℝ) + n|
    set v := |(d : ℝ)|
    have hu : 0 ≤ u := abs_nonneg _
    have a1 : u ≤ u * v := by nlinarith
    have a2 : v / (x 0).den ≤ u * v := by
      rw [div_le_iff₀ hN]; nlinarith
    have hp : 0 < Real.pi * τ.im := by positivity
    have e : Real.pi * τ.im / (x 0).den * v = Real.pi * τ.im * (v / (x 0).den) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left a1 hp.le, mul_le_mul_of_nonneg_left a2 hp.le]
  · simp only [norm_zero]; positivity

end GlobalTheory.Sieg.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.DiagUnitsEqLocalIdele
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.Mem.Chr
namespace GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) v = x
  exact Pi.mulSingle_eq_same _ _

theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) w = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) w = x
  exact Pi.mulSingle_eq_same _ _

theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) u = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem finSingle_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (finSingle L v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 L))) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal {v}ᶜ) :=
    fun x => ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.mulSingle_eq_of_ne (Set.mem_compl_singleton_iff.mp hw)]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_mulSingle v)
  have hfg : (finSingle L v : v.adicCompletion L → FiniteAdeleRing (𝓞 L) L) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    funext x
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

theorem localIdele_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  exact Continuous.units_map _ (continuous_const.prodMk (finSingle_continuous L v))

end GlobalTheory.Mem.Chr.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.EtaSixProductDifferentiable
noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace GlobalTheory.HeckeFamilyMatrices

def ev (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) : SL(2, ℤ) → ℂ := fun x => (F ∣[k] x) τ

section EtaSix

open Complex Function ModularForm
open scoped Manifold Real

def eta6 (z : ℍ) : ℂ := ModularForm.eta z ^ 6

lemma eta_six_ne_zero (z : ℍ) : eta6 z ≠ 0 := pow_ne_zero _ (eta_ne_zero z.2)

lemma eta_six_product_formula (z : ℍ) : eta6 z = Periodic.qParam 4 z * (∏' n, (1 - eta_q n z)) ^ 6 := by
  simp only [eta6, ModularForm.eta, mul_pow]
  congr
  simp [Periodic.qParam, ← Complex.exp_nsmul, nsmul_eq_mul]
  congr 1
  ring

lemma eta6_slash_three_T_eq_I_smul : eta6 ∣[(3 : ℤ)] ModularGroup.T = (Complex.I : ℂ) • eta6 := by
  ext z
  rw [SL_slash_apply, ModularGroup.denom_apply, modular_T_smul]
  have h1 : ∀ n, eta_q n (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = eta_q n z := by
    intro n
    simp only [eta_q, Periodic.qParam, coe_vadd]
    rw [← exp_periodic (2 * π * Complex.I * z / ((1:ℝ):ℂ))]
    congr 2
    push_cast; ring
  have h2 : Periodic.qParam 4 (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = Complex.I * Periodic.qParam 4 z := by
    simp only [Periodic.qParam, coe_vadd]
    rw [← exp_pi_div_two_mul_I, ← Complex.exp_add, exp_pi_div_two_mul_I]
    congr 1
    push_cast; ring
  simp only [eta_six_product_formula, h1, h2, Pi.smul_apply, smul_eq_mul]
  simp [ModularGroup.T, mul_assoc]

lemma sqrt_pow_six (z : ℂ) : Complex.sqrt z ^ 6 = z ^ 3 := by
  have : Complex.sqrt z ^ 2 = z := by
    simp [Complex.sqrt]
  rw [show 6 = 2 * 3 by rfl, pow_mul, this]

lemma eta_six_slash_S : eta6 ∣[(3 : ℤ)] ModularGroup.S = (Complex.I : ℂ) • eta6 := by
  ext z
  rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]
  have he : η (-(↑z)⁻¹) = (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt z * η z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.2
  have hz := z.ne_zero
  simp only [eta6, inv_neg, he, mul_pow, inv_pow, sqrt_pow_six, Pi.smul_apply, smul_eq_mul]
  have : (Complex.I : ℂ) ^ 3 = -Complex.I := by rw [pow_succ, I_sq]; ring
  rw [this, zpow_neg, inv_neg, inv_I]
  field_simp

lemma eta_six_slash_root_of_unity (γ : SL(2, ℤ)) : ∃ c : ℂ, c ^ 4 = 1 ∧ eta6 ∣[(3 : ℤ)] γ = c • eta6 := by
  have hγ : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨Complex.I, I_pow_four, eta_six_slash_S⟩
    · exact ⟨Complex.I, I_pow_four, eta6_slash_three_T_eq_I_smul⟩
  | one => exact ⟨1, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, by rw [mul_pow, ha, hb, one_mul], ?_⟩
    rw [SlashAction.slash_mul, hx, SL_smul_slash, hy, smul_smul]
  | inv x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    refine ⟨a⁻¹, by rw [inv_pow, ha, inv_one], ?_⟩
    have : eta6 = a • eta6 ∣[(3 : ℤ)] x⁻¹ := by
      rw [← SL_smul_slash, ← hx, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    conv_rhs => rw [this]
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]

def eta6MultiplierFunction (γ : SL(2, ℤ)) : ℂ := (eta6 ∣[(3 : ℤ)] γ) UpperHalfPlane.I / eta6 UpperHalfPlane.I

lemma eta6Mult0_eq {γ : SL(2, ℤ)} {c : ℂ} (h : eta6 ∣[(3 : ℤ)] γ = c • eta6) : eta6MultiplierFunction γ = c := by
  simp [eta6MultiplierFunction, h, eta_six_ne_zero]

lemma eta_six_slash_multiplier (γ : SL(2, ℤ)) : eta6 ∣[(3 : ℤ)] γ = eta6MultiplierFunction γ • eta6 := by
  obtain ⟨c, -, h⟩ := eta_six_slash_root_of_unity γ
  rw [eta6Mult0_eq h, h]

def eta6Mult : SL(2, ℤ) →* ℂ where
  toFun := eta6MultiplierFunction
  map_one' := eta6Mult0_eq (by simp)
  map_mul' x y := eta6Mult0_eq (by
    rw [SlashAction.slash_mul, eta_six_slash_multiplier, SL_smul_slash, eta_six_slash_multiplier, smul_smul])

lemma eta6Mult_T_eq_I : eta6Mult ModularGroup.T = Complex.I := eta6Mult0_eq eta6_slash_three_T_eq_I_smul

lemma eta6Mult_S : eta6Mult ModularGroup.S = Complex.I := eta6Mult0_eq eta_six_slash_S

lemma eta6Mult_neg_one : eta6Mult (-1) = -1 := by
  have : (-1 : SL(2, ℤ)) = ModularGroup.S * ModularGroup.S := by decide
  rw [this, map_mul, eta6Mult_S, I_mul_I]

def eta6Group : Subgroup SL(2, ℤ) := eta6Mult.toHomUnits.ker

lemma mem_eta6Group (γ : SL(2, ℤ)) : γ ∈ eta6Group ↔ eta6Mult γ = 1 := by
  simp [eta6Group, MonoidHom.mem_ker, Units.ext_iff]

lemma neg_one_not_mem_eta6Group : (-1 : SL(2, ℤ)) ∉ eta6Group := by
  rw [mem_eta6Group, eta6Mult_neg_one]; norm_num

end EtaSix

end GlobalTheory.HeckeFamilyMatrices
end
end
