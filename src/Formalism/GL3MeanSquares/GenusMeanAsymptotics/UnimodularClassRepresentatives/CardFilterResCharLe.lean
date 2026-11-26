module

public import Mathlib

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFilterResCharLe
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities

variable {K : Type} [Field K] [NumberField K]

def resChar (P : Ideal (𝓞 K)) : ℕ := Ideal.absNorm (P.under ℤ)

theorem span_resChar (P : Ideal (𝓞 K)) : Ideal.span {(resChar P : ℤ)} = P.under ℤ := Int.ideal_span_absNorm_eq_self _

theorem under_ne_bot {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : P.under ℤ ≠ ⊥ := by
  intro h
  have hPb : P = ⊥ := Ideal.eq_bot_of_comap_eq_bot h
  exact Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField K) hPb

theorem under_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (P.under ℤ).IsMaximal := by
  haveI := hP
  exact Ideal.IsMaximal.under ℤ P

theorem resChar_prime {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (resChar P).Prime := by

  have h1 := span_resChar P
  have hmax := under_isMaximal hP
  rw [← h1] at hmax
  have hne : ((resChar P : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply under_ne_bot hP
    rw [← h1, h0]
    simp
  have hpr := (Ideal.span_singleton_prime hne).mp hmax.isPrime
  exact Nat.prime_iff_prime_int.mpr hpr

theorem exists_absNorm_eq_pow {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm P = resChar P ^ k := by

  have hp := resChar_prime hP
  haveI : P.LiesOver (Ideal.span {((resChar P : ℕ) : ℤ)}) := ⟨span_resChar P⟩
  have h1 := Ideal.absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)
  rw [show (((resChar P : ℕ) : ℤ)).natAbs = resChar P by simp] at h1
  refine ⟨_, ?_, h1⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at h1
  exact hP.ne_top h1

theorem resChar_le_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    resChar P ≤ Ideal.absNorm P := by

  obtain ⟨k, hk, hk2⟩ := exists_absNorm_eq_pow hP
  rw [hk2]
  exact Nat.le_self_pow (by omega) _

theorem resChar_le_of_sq {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {q : ℕ}
    (hq : Ideal.absNorm P = q ^ 2) : resChar P ≤ q := by

  obtain ⟨k, hk, hk2⟩ := exists_absNorm_eq_pow hP
  have hp := resChar_prime hP
  have hdvd : resChar P ∣ q ^ 2 := by
    rw [← hq, hk2]
    exact dvd_pow_self _ (by omega)
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h0 : resChar P ^ k = 0 := by rw [← hk2, hq]; simp
    exact hp.ne_zero (pow_eq_zero_iff (by omega) |>.mp h0)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (hp.dvd_of_dvd_pow hdvd)

set_option linter.deprecated false in
theorem card_filter_resChar_le (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) (n : ℕ) :
    (s.filter (fun P => resChar P.1 = n)).card ≤ finrank ℚ K := by

  classical
  by_cases hn : ∃ P ∈ s, resChar P.1 = n
  · obtain ⟨P0, -, hP0⟩ := hn
    have hJ : Ideal.span {((n : ℕ) : ℤ)} = P0.1.under ℤ := by
      rw [← hP0]
      exact span_resChar P0.1
    haveI : (Ideal.span {((n : ℕ) : ℤ)}).IsMaximal := by
      rw [hJ]
      exact under_isMaximal P0.2
    have hJne : Ideal.span {((n : ℕ) : ℤ)} ≠ ⊥ := by
      rw [hJ]
      exact under_ne_bot P0.2
    calc (s.filter (fun P => resChar P.1 = n)).card
        ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((n : ℕ) : ℤ)}) (𝓞 K)).card := by
          refine Finset.card_le_card_of_injOn (fun P => P.1) (by
            intro P hP
            rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hJne]
            obtain ⟨-, hPn⟩ := Finset.mem_filter.mp hP
            refine ⟨P.2.isPrime, ⟨?_⟩⟩
            rw [← hPn]
            exact span_resChar P.1) (fun a _ b _ h => Subtype.ext h)
      _ ≤ finrank ℚ K := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hJne
  · push_neg at hn
    rw [Finset.filter_false_of_mem (fun P hP => hn P hP)]
    simp

theorem summable_resChar_sq :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => ((resChar P.1 : ℝ) ^ 2)⁻¹) := by

  classical
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  refine summable_of_sum_le (c := (finrank ℚ K : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) (fun P => by positivity)
    (fun u => ?_)
  calc ∑ P ∈ u, ((resChar P.1 : ℝ) ^ 2)⁻¹
      = ∑ n ∈ u.image (fun P => resChar P.1),
          ∑ P ∈ u.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ n ∈ u.image (fun P => resChar P.1),
          ((u.filter (fun P => resChar P.1 = n)).card : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ n ∈ u.image (fun P => resChar P.1), (finrank ℚ K : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_filter_resChar_le u n
    _ = (finrank ℚ K : ℝ) * ∑ n ∈ u.image (fun P => resChar P.1), ((n : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (finrank ℚ K : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hs.sum_le_tsum _ (fun n _ => by positivity)

end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNormOneOfPair
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K : Type*} [Field K] [StarRing K]

def IsUnitIn (S : Subring K) (a : K) : Prop := a ≠ 0 ∧ a ∈ S ∧ a⁻¹ ∈ S

structure IsHermSemilocal (S : Subring K) : Prop where
  star_mem : ∀ a ∈ S, star a ∈ S
  frac : ∀ a : K, ∃ t ∈ S, t ≠ 0 ∧ t * a ∈ S
  unram : ∃ θ ∈ S, IsUnitIn S (θ - star θ)
  principal : ∀ A : AddSubgroup K, (∀ s ∈ S, ∀ a ∈ A, s * a ∈ A) → (∃ a ∈ A, a ≠ 0) →
    (∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S) → ∃ α ∈ A, α ≠ 0 ∧ ∀ a ∈ A, a * α⁻¹ ∈ S
  unit_or : ∀ a ∈ S, ∀ κ ∈ S, ∀ μ : K, a⁻¹ ∉ S → IsUnitIn S μ →
    IsUnitIn S (1 - κ * a) ∨ IsUnitIn S (1 - (κ + μ) * a)

variable {S : Subring K}

theorem exists_trace_eq (hS : IsHermSemilocal S) {s : K} (hs : s ∈ S) (hss : star s = s) :
    ∃ c ∈ S, c + star c = s := by
  obtain ⟨θ, hθ, hu0, -, hui⟩ := hS.unram
  refine ⟨s * θ * (θ - star θ)⁻¹, S.mul_mem (S.mul_mem hs hθ) hui, ?_⟩
  have hst : star (θ - star θ) = -(θ - star θ) := by
    rw [star_sub, star_star]
    ring
  have hn : -(θ - star θ) ≠ 0 := neg_ne_zero.mpr hu0
  rw [star_mul, star_mul, star_inv₀, hst, hss]
  field_simp
  try ring

theorem exists_norm_one_mul_mem (hS : IsHermSemilocal S) {a : K} (ha : star a * a ∈ S) :
    ∃ b : K, star b * b = 1 ∧ a * b ∈ S := by
  let A : AddSubgroup K :=
    { carrier := {w | ∃ x ∈ S, ∃ y ∈ S, w = x + y * a}
      add_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        exact ⟨x + x', S.add_mem hx hx', y + y', S.add_mem hy hy', by ring⟩
      zero_mem' := ⟨0, S.zero_mem, 0, S.zero_mem, by ring⟩
      neg_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact ⟨-x, S.neg_mem hx, -y, S.neg_mem hy, by ring⟩ }
  have hmem : ∀ w, w ∈ A ↔ ∃ x ∈ S, ∃ y ∈ S, w = x + y * a := fun w => Iff.rfl
  have h1 : ∀ s ∈ S, ∀ w ∈ A, s * w ∈ A := by
    intro s hs w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := (hmem w).1 hw
    exact (hmem _).2 ⟨s * x, S.mul_mem hs hx, s * y, S.mul_mem hs hy, by ring⟩
  have h2 : ∃ w ∈ A, w ≠ 0 := ⟨1, (hmem 1).2 ⟨1, S.one_mem, 0, S.zero_mem, by ring⟩, one_ne_zero⟩
  obtain ⟨t, ht, ht0, hta⟩ := hS.frac a
  have h3 : ∃ t : K, t ≠ 0 ∧ ∀ w ∈ A, t * w ∈ S := by
    refine ⟨t, ht0, fun w hw => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (hmem w).1 hw
    have e : t * (x + y * a) = t * x + y * (t * a) := by ring
    rw [e]
    exact S.add_mem (S.mul_mem ht hx) (S.mul_mem hy hta)
  obtain ⟨α, hαA, hα0, hαdiv⟩ := hS.principal A h1 h2 h3
  have h1inv : 1 * α⁻¹ ∈ S := hαdiv 1 ((hmem 1).2 ⟨1, S.one_mem, 0, S.zero_mem, by ring⟩)
  have haα : a * α⁻¹ ∈ S := hαdiv a ((hmem a).2 ⟨0, S.zero_mem, 1, S.one_mem, by ring⟩)
  obtain ⟨x, hx, y, hy, hαxy⟩ := (hmem α).1 hαA
  have hsα0 : star α ≠ 0 := star_ne_zero.mpr hα0
  have hsα : star α = star x + star a * star y := by
    rw [hαxy, star_add, star_mul]
  refine ⟨star α / α, ?_, ?_⟩
  · rw [star_div₀, star_star, div_mul_div_comm, mul_comm α (star α), div_self (mul_ne_zero hsα0 hα0)]
  · have e : a * (star α / α) = star x * (a * α⁻¹) + star y * (star a * a) * (1 * α⁻¹) := by
      rw [hsα]
      field_simp
      try ring
    rw [e]
    exact S.add_mem (S.mul_mem (hS.star_mem x hx) haα)
      (S.mul_mem (S.mul_mem (hS.star_mem y hy) ha) h1inv)

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_norm_one_of_pair (hS : IsHermSemilocal S) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {y w : V} {a : K} (ha : a ∈ S) (ha0 : a ≠ 0) (hy : h y y = star a * a) (hyw : h y w = 1)
    (hw : h w w ∈ S) :
    ∃ c ∈ S, ∃ d ∈ S, h (c • w + d • y) (c • w + d • y) = 1 := by
  have hwy : h w y = 1 := by
    have := hs.eq y w
    rw [hyw, map_one] at this
    exact this.symm
  have hH : star (h w w) = h w w := hs.eq w w
  have key : ∀ c d : K, h (c • w + d • y) (c • w + d • y) =
      star c * c * h w w + star c * d + star d * c + star d * d * (star a * a) := by
    intro c d
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hy, hyw, hwy, starRingEnd_apply, RingHom.id_apply]
    ring
  by_cases hu : a⁻¹ ∈ S
  · refine ⟨0, S.zero_mem, a⁻¹, hu, ?_⟩
    have hsa : star a ≠ 0 := star_ne_zero.mpr ha0
    rw [key, star_inv₀]
    field_simp
    simp
  · obtain ⟨θ, hθ, hμ⟩ := hS.unram
    have h1a : 1 + a ∈ S := S.add_mem S.one_mem ha
    obtain ⟨κ, hκ, hκt⟩ : ∃ κ ∈ S, κ + star κ = star (1 + a) * (1 + a) * h w w - 1 := by
      apply exists_trace_eq hS
      · exact S.sub_mem (S.mul_mem (S.mul_mem (hS.star_mem _ h1a) h1a) hw) S.one_mem
      · simp only [star_sub, star_mul', star_star, hH, star_one]
        ring
    have fin : ∀ κ' ∈ S, κ' + star κ' = star (1 + a) * (1 + a) * h w w - 1 →
        IsUnitIn S (1 - κ' * a) →
        ∃ c ∈ S, ∃ d ∈ S, h (c • w + d • y) (c • w + d • y) = 1 := by
      rintro κ' hκ' ht ⟨h0, -, h2⟩
      refine ⟨star (1 + a) * (1 - κ' * a)⁻¹, S.mul_mem (hS.star_mem _ h1a) h2,
        -κ' * (1 - κ' * a)⁻¹, S.mul_mem (S.neg_mem hκ') h2, ?_⟩
      have h0' : star (1 - κ' * a) ≠ 0 := star_ne_zero.mpr h0
      have hb : star (1 + a) * (1 + a) * h w w = κ' + star κ' + 1 := by rw [ht]; ring
      rw [key]
      have e : star (star (1 + a) * (1 - κ' * a)⁻¹) * (star (1 + a) * (1 - κ' * a)⁻¹) * h w w +
          star (star (1 + a) * (1 - κ' * a)⁻¹) * (-κ' * (1 - κ' * a)⁻¹) +
          star (-κ' * (1 - κ' * a)⁻¹) * (star (1 + a) * (1 - κ' * a)⁻¹) +
          star (-κ' * (1 - κ' * a)⁻¹) * (-κ' * (1 - κ' * a)⁻¹) * (star a * a) =
          (star (1 - κ' * a))⁻¹ * (1 - κ' * a)⁻¹ * (star (1 + a) * (1 + a) * h w w
            - (1 + a) * κ' - star κ' * star (1 + a) + star κ' * κ' * (star a * a)) := by
        simp only [star_mul', star_inv₀, star_star, star_neg]
        ring
      rw [e, hb]
      have e2 : κ' + star κ' + 1 - (1 + a) * κ' - star κ' * star (1 + a) +
          star κ' * κ' * (star a * a) = star (1 - κ' * a) * (1 - κ' * a) := by
        simp only [star_sub, star_add, star_mul', star_one]
        ring
      rw [e2]
      field_simp
    rcases hS.unit_or a ha κ hκ (θ - star θ) hu hμ with h1 | h1
    · exact fin κ hκ hκt h1
    · refine fin (κ + (θ - star θ)) (S.add_mem hκ hμ.2.1) ?_ h1
      rw [← hκt]
      simp only [star_add, star_sub, star_star]
      ring

end Formalism.HermitianLattices.Ext.L3.WA
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLocUnif
open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K]

structure IsLocUnif (S : Subring K) (ϖ : K) : Prop where
  star_mem : ∀ a ∈ S, star a ∈ S
  mem : ϖ ∈ S
  fix : star ϖ = ϖ
  ne : ϖ ≠ 0
  tr : ∃ τ ∈ S, τ + star τ = 1
  skew : ∃ θ ∈ S, star θ = -θ ∧ θ ≠ 0
  dv : ∀ f ∈ S, star f = f → f⁻¹ ∈ S ∨ f * ϖ⁻¹ ∈ S
  rad : ∀ s ∈ S, 1 + ϖ * s ≠ 0 ∧ (1 + ϖ * s)⁻¹ ∈ S
  arch : ∀ a : K, ∃ l : ℕ, ϖ ^ l * a ∈ S

def Ent (S : Subring K) {m n : Type*} (M : Matrix m n K) : Prop := ∀ i j, M i j ∈ S

variable {S : Subring K} {m n o : Type*}

theorem Ent.add {M N : Matrix m n K} (hM : Ent S M) (hN : Ent S N) : Ent S (M + N) := by
  exact fun i j => S.add_mem (hM i j) (hN i j)

theorem Ent.sub {M N : Matrix m n K} (hM : Ent S M) (hN : Ent S N) : Ent S (M - N) := by
  exact fun i j => S.sub_mem (hM i j) (hN i j)

theorem Ent.neg {M : Matrix m n K} (hM : Ent S M) : Ent S (-M) := by
  exact fun i j => S.neg_mem (hM i j)

theorem Ent.zero : Ent S (0 : Matrix m n K) := by
  exact fun _ _ => S.zero_mem

theorem Ent.smul {a : K} (ha : a ∈ S) {M : Matrix m n K} (hM : Ent S M) : Ent S (a • M) := by
  exact fun i j => S.mul_mem ha (hM i j)

theorem Ent.mul [Fintype n] {M : Matrix m n K} {N : Matrix n o K} (hM : Ent S M) (hN : Ent S N) :
    Ent S (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => S.mul_mem (hM i k) (hN k j)

theorem Ent.one [DecidableEq n] : Ent S (1 : Matrix n n K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem Ent.conjTranspose (hS : ∀ a ∈ S, star a ∈ S) {M : Matrix m n K} (hM : Ent S M) : Ent S Mᴴ := by
  exact fun i j => hS _ (hM j i)

theorem Ent.exists_map {M : Matrix m n K} (hM : Ent S M) :
    ∃ M₀ : Matrix m n S, M₀.map S.subtype = M := by
  refine ⟨fun i j => ⟨M i j, hM i j⟩, ?_⟩
  ext i j
  rfl

theorem Ent.det [Fintype n] [DecidableEq n] {M : Matrix n n K} (hM : Ent S M) : M.det ∈ S := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  have h := RingHom.map_det S.subtype M₀
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact (M₀.det).2

theorem Ent.adjugate [Fintype n] [DecidableEq n] {M : Matrix n n K} (hM : Ent S M) :
    Ent S M.adjugate := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  have h := RingHom.map_adjugate S.subtype M₀
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [← h]
  intro i j
  exact (M₀.adjugate i j).2

theorem pow_mem {ϖ : K} (hS : IsLocUnif S ϖ) (k : ℕ) : ϖ ^ k ∈ S := by
  exact S.pow_mem hS.mem k

end Formalism.HermitianLattices.Ext.L3.HU
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SummableSqGeom
open Filter Topology Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {ι : Type*}

def ebox (s : Finset ι) (J : ι → ℕ) : Finset (ι →₀ ℕ) := s.finsupp fun i => range (J i + 1)

theorem mem_ebox {s : Finset ι} {J : ι → ℕ} {v : ι →₀ ℕ} :
    v ∈ ebox s J ↔ v.support ⊆ s ∧ ∀ i ∈ s, v i ≤ J i := by
  classical
  simp [ebox, Finset.mem_finsupp_iff, Nat.lt_succ_iff]

theorem sum_ebox (f : ι → ℕ → ℝ) (hf : ∀ i, f i 0 = 1) (s : Finset ι) (J : ι → ℕ) :
    ∑ v ∈ ebox s J, v.prod f = ∏ i ∈ s, ∑ j ∈ range (J i + 1), f i j := by
  classical
  rw [Finset.prod_sum, ebox, Finset.finsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Finsupp.prod_of_support_subset _ (Finsupp.support_indicator_subset s g) _ (fun i _ => hf i),
    ← Finset.prod_attach s]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.indicator_apply, dite_eq_left i.2]

theorem mem_ebox_support {v w : ι →₀ ℕ} : v ∈ ebox w.support w ↔ v ≤ w := by
  rw [mem_ebox, Finsupp.le_def]
  constructor
  · rintro ⟨hs, hle⟩ i
    by_cases hi : i ∈ w.support
    · exact hle i hi
    · have h0 : v i = 0 := by
        by_contra h
        exact hi (hs (Finsupp.mem_support_iff.mpr h))
      rw [h0]
      exact Nat.zero_le _
  · intro h
    refine ⟨fun i hi => ?_, fun i _ => h i⟩
    rw [Finsupp.mem_support_iff] at hi ⊢
    have := h i
    omega

def dif (R : ι → ℕ → ℝ) (i : ι) : ℕ → ℝ
  | 0 => 1
  | j + 1 => R i (j + 1) - R i j

theorem sum_dif (R : ι → ℕ → ℝ) (hR : ∀ i, R i 0 = 1) (i : ι) (J : ℕ) :
    ∑ j ∈ range (J + 1), dif R i j = R i J := by
  induction J with
  | zero => simp [dif, hR]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    simp [dif]

theorem prod_eq_sum_dif (R : ι → ℕ → ℝ) (hR : ∀ i, R i 0 = 1) (w : ι →₀ ℕ) :
    w.prod R = ∑ v ∈ ebox w.support w, v.prod (dif R) := by
  rw [sum_ebox (dif R) (fun i => rfl) w.support w, Finsupp.prod]
  exact Finset.prod_congr rfl fun i _ => (sum_dif R hR i (w i)).symm

theorem summable_prod {u : ι → ℕ → ℝ} (hu0 : ∀ i, u i 0 = 1) (hu : ∀ i j, 0 ≤ u i j) {t : ι → ℝ}
    (ht : Summable t) (hut : ∀ i J, ∑ j ∈ range (J + 1), u i j ≤ 1 + t i) :
    Summable fun v : ι →₀ ℕ => v.prod u := by
  classical
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i
    have h := hut i 0
    simp [hu0] at h
    linarith
  apply summable_of_sum_le (c := Real.exp (∑' i, t i)) (fun v => by unfold Finsupp.prod; exact Finset.prod_nonneg fun i _ => hu i _)
  intro F
  have hsub : F ⊆ ebox (F.biUnion fun v => v.support) (fun i => F.sup fun v => v i) := by
    intro v hv
    rw [mem_ebox]
    exact ⟨fun i hi => Finset.mem_biUnion.mpr ⟨v, hv, hi⟩,
      fun i _ => Finset.le_sup (f := fun v : ι →₀ ℕ => v i) hv⟩
  calc ∑ v ∈ F, v.prod u
      ≤ ∑ v ∈ ebox (F.biUnion fun v => v.support) (fun i => F.sup fun v => v i), v.prod u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun v _ _ => by unfold Finsupp.prod; exact Finset.prod_nonneg fun i _ => hu i _)
    _ = ∏ i ∈ F.biUnion (fun v => v.support), ∑ j ∈ range ((F.sup fun v => v i) + 1), u i j :=
        sum_ebox u hu0 _ _
    _ ≤ ∏ i ∈ F.biUnion (fun v => v.support), Real.exp (t i) := by
        apply Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => hu i j)
        intro i _
        calc _ ≤ 1 + t i := hut i _
          _ ≤ Real.exp (t i) := by linarith [Real.add_one_le_exp (t i)]
    _ = Real.exp (∑ i ∈ F.biUnion (fun v => v.support), t i) := (Real.exp_sum _ t).symm
    _ ≤ Real.exp (∑' i, t i) := Real.exp_le_exp.mpr (ht.sum_le_tsum _ (fun i _ => ht0 i))

theorem summable_sq_geom : Summable fun j : ℕ => 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j := by
  have h0 := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  refine (((h2.add (h1.mul_left 4)).add (h0.mul_left 4)).mul_left 8).congr fun j => ?_
  ring

def cGeom : ℝ := ∑' j : ℕ, 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j

variable {q : ι → ℝ}

def nrm (q : ι → ℝ) (v : ι →₀ ℕ) : ℝ := v.prod fun i e => q i ^ e

theorem nrm_pos (hq : ∀ i, 2 ≤ q i) (v : ι →₀ ℕ) : 0 < nrm q v := by
  unfold nrm Finsupp.prod
  exact Finset.prod_pos fun i _ => pow_pos (by linarith [hq i]) _

theorem abs_div_nrm (f : ι → ℕ → ℝ) (v : ι →₀ ℕ) :
    |v.prod f| / nrm q v = v.prod fun i e => |f i e| / q i ^ e := by
  unfold nrm Finsupp.prod
  rw [Finset.abs_prod, ← Finset.prod_div_distrib]

theorem sum_dif_le (hq : ∀ i, 2 ≤ q i) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) (i : ι) (J : ℕ) :
    ∑ j ∈ range (J + 1), |dif R i j| / q i ^ j ≤ 1 + cGeom * (q i ^ 2)⁻¹ := by
  have hq0 : 0 < q i := by linarith [hq i]
  rw [Finset.sum_range_succ']
  simp only [dif, pow_zero, div_one, abs_one]
  rw [add_comm]
  refine add_le_add le_rfl ?_
  have hterm : ∀ j ∈ range J, |R i (j + 1) - R i j| / q i ^ (j + 1) ≤
      (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) := by
    intro j _
    have hqj : 0 < q i ^ (j + 1) := pow_pos hq0 _
    have hqne : q i ≠ 0 := hq0.ne'
    rw [div_le_iff₀ hqj]
    have hx : 1 ≤ (q i / 2) ^ j := one_le_pow₀ (by linarith [hq i])
    have hc : 0 ≤ 8 * ((j : ℝ) + 2) ^ 2 := by positivity
    have e : (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) * q i ^ (j + 1) =
        8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by
      have h2 : (q i ^ 2)⁻¹ * q i ^ (j + 1) = q i ^ j / q i := by
        rw [pow_succ (q i) j, sq]
        field_simp
      calc (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) * q i ^ (j + 1)
          = 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j * ((q i ^ 2)⁻¹ * q i ^ (j + 1)) := by ring
        _ = 8 * ((j : ℝ) + 2) ^ 2 * ((1 / 2 : ℝ) ^ j * q i ^ j) / q i := by rw [h2]; ring
        _ = 8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by rw [← mul_pow]; ring_nf
    rw [e]
    calc |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i := hRb i j
      _ ≤ 8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by
        exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hc hx) hq0.le
  calc ∑ j ∈ range J, |R i (j + 1) - R i j| / q i ^ (j + 1)
      ≤ ∑ j ∈ range J, (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) :=
        Finset.sum_le_sum hterm
    _ = (q i ^ 2)⁻¹ * ∑ j ∈ range J, 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ (q i ^ 2)⁻¹ * cGeom := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact summable_sq_geom.sum_le_tsum _ (fun j _ => by positivity)
    _ = cGeom * (q i ^ 2)⁻¹ := mul_comm _ _

theorem summable_dif (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) :
    Summable fun v : ι →₀ ℕ => |v.prod (dif R)| / nrm q v := by
  have h := summable_prod (u := fun i e => |dif R i e| / q i ^ e) (fun i => by simp [dif])
    (fun i j => div_nonneg (abs_nonneg _) (pow_nonneg (by linarith [hq i]) _))
    (hsum.mul_left cGeom) (fun i J => sum_dif_le hq hRb i J)
  exact h.congr fun v => (abs_div_nrm (dif R) v).symm

end Formalism.HermitianLattices.Ext.L3.A5
end
end
