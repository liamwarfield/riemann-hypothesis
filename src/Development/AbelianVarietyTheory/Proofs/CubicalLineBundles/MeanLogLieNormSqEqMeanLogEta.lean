module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyComplex
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogCovolumeEqMeanClassGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumLogNormEmbeddingEqFinrankMulLogAbsNorm
open NumberField

namespace GlobalTheory

theorem exists_span_singleton_eq_map_of_integral (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∃ β₀ : 𝓞 M, (β₀ : M) = β ∧ Ideal.span {β₀} = 𝔟.map (algebraMap (𝓞 K) (𝓞 M)) := by
  have hint : IsIntegral ℤ β := by
    have := h₁ 1 (fun b _ => by simpa using RingOfIntegers.isIntegral_coe b)
    simpa using this
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : 𝓞 M, (β₀ : M) = β := ⟨⟨β, hint⟩, rfl⟩
  refine ⟨β₀, hβ₀, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have hone : (1 : K) ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹) := by
      rw [FractionalIdeal.coe_ideal_mul_inv 𝔟 h𝔟]
      exact FractionalIdeal.one_mem_one _
    have key : ∀ r ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹),
        ∃ z ∈ 𝔟.map (algebraMap (𝓞 K) (𝓞 M)), (z : M) = β * algebraMap K M r := by
      intro r hr
      refine FractionalIdeal.mul_induction_on
        (C := fun r => ∃ z ∈ 𝔟.map (algebraMap (𝓞 K) (𝓞 M)), (z : M) = β * algebraMap K M r)
        hr ?_ ?_
      · intro i hi j hj
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have h0 : (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
          FractionalIdeal.coeIdeal_ne_zero.2 h𝔟
        have hj' := (FractionalIdeal.mem_inv_iff h0).1 hj
        have hI : IsIntegral ℤ (β * algebraMap K M j) := by
          refine h₁ j fun c hc => ?_
          obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
            (hj' _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨c, hc, rfl⟩))
          have : j * (c : K) = (w : K) := hw.symm
          rw [this]
          exact RingOfIntegers.isIntegral_coe w
        refine ⟨algebraMap (𝓞 K) (𝓞 M) b * ⟨_, hI⟩,
          Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb), ?_⟩
        change algebraMap K M (b : K) * (β * algebraMap K M j) =
          β * algebraMap K M ((b : K) * j)
        rw [map_mul]; ring
      · rintro x y ⟨z, hz, hx⟩ ⟨w, hw, hy⟩
        refine ⟨z + w, Ideal.add_mem _ hz hw, ?_⟩
        change (z : M) + (w : M) = _
        rw [hx, hy, map_add (f := _)]; ring
    obtain ⟨z, hz, hz'⟩ := key 1 hone
    have : β₀ = z := by
      apply RingOfIntegers.ext
      rw [hz', hβ₀]; simp
    rw [this]; exact hz
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨⟨_, h₂ y hy⟩, ?_⟩
    apply RingOfIntegers.ext
    change β⁻¹ * algebraMap K M (y : K) * (β₀ : M) = algebraMap K M (y : K)
    rw [hβ₀]
    field_simp

theorem abs_norm_eq_absNorm_pow_of_integral (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    |Algebra.norm ℚ β| = (Ideal.absNorm 𝔟 : ℚ) ^ Module.finrank K M := by
  obtain ⟨β₀, rfl, hspan⟩ := exists_span_singleton_eq_map_of_integral K M 𝔟 β h𝔟 hβ h₁ h₂
  have h := congrArg Ideal.absNorm hspan
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_algebraMap,
    ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 M) M] at h
  rw [← Algebra.coe_norm_int, ← Nat.cast_pow, ← h, Nat.cast_natAbs, Int.cast_abs]

theorem sum_log_norm_embedding_eq_finrank_mul_log_absNorm (K M : Type) [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∑ σ : M →+* ℂ, Real.log ‖σ β‖ =
      (Module.finrank K M : ℝ) * Real.log (Ideal.absNorm 𝔟 : ℝ) := by
  have h := abs_norm_eq_absNorm_pow_of_integral K M 𝔟 β h𝔟 hβ h₁ h₂
  have hp : ∏ σ : M →+* ℂ, ‖σ β‖ = ((|Algebra.norm ℚ β| : ℚ) : ℝ) := by
    have h3 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ β)
    rw [norm_prod] at h3
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom M ℂ) (fun σ : M →+* ℂ => ‖σ β‖)
      (fun σ : M →ₐ[ℚ] ℂ => ‖σ β‖) (fun _ => rfl), ← h3]
    simp
  rw [← Real.log_prod (fun σ _ => by simpa using hβ), hp, h]
  push_cast
  rw [Real.log_pow]

end GlobalTheory
end

open Complex NumberField
open scoped nonZeroDivisors Real UpperHalfPlane

noncomputable section

namespace GlobalTheory

def latticeNormDisc (L : PeriodPair) : ℝ := latticeArea L ^ 6 * ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖

theorem latticeArea_eq_abs_im_mul_conj (L : PeriodPair) :
    latticeArea L = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  rw [latticeArea_eq, ← abs_neg]
  congr 1
  simp
  ring

theorem latticeNormDisc_eq (L : PeriodPair) :
    latticeNormDisc L = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ^ 6 * ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ := by
  rw [latticeNormDisc, latticeArea_eq_abs_im_mul_conj]

theorem latticeNormDisc_pos (L : PeriodPair) : 0 < latticeNormDisc L :=
  mul_pos (pow_pos (latticeArea_pos L) _) (norm_pos_iff.2 (g₂_cube_sub_g₃_sq_ne_zero L))

theorem IsHomothetic.latticeNormDisc_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    latticeNormDisc L' = latticeNormDisc L := by
  have hc : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 h.ne_zero
  have e : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [h.g₂_eq, h.g₃_eq]
    ring
  rw [latticeNormDisc, latticeNormDisc, h.latticeArea_eq, e, norm_mul, norm_inv, norm_pow]
  field_simp

def conjPeriods (L : PeriodPair) : PeriodPair where
  ω₁ := starRingEnd ℂ L.ω₁
  ω₂ := starRingEnd ℂ L.ω₂
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    refine LinearIndependent.pair_iff.1 L.indep s t ?_
    have := congrArg (starRingEnd ℂ) h
    simpa using this

theorem mem_conjPeriods_lattice (L : PeriodPair) (z : ℂ) :
    z ∈ (conjPeriods L).lattice ↔ starRingEnd ℂ z ∈ L.lattice := by
  simp only [PeriodPair.mem_lattice, conjPeriods]
  refine exists₂_congr fun m n => ⟨fun h => ?_, fun h => ?_⟩
  · simpa using congrArg (starRingEnd ℂ) h
  · simpa using congrArg (starRingEnd ℂ) h

theorem G_conjPeriods (L : PeriodPair) (n : ℕ) :
    (conjPeriods L).G n = starRingEnd ℂ (L.G n) := by
  let e : L.lattice ≃ (conjPeriods L).lattice :=
    { toFun := fun x => ⟨starRingEnd ℂ x, (mem_conjPeriods_lattice L _).2 (by simp)⟩
      invFun := fun y => ⟨starRingEnd ℂ y, (mem_conjPeriods_lattice L _).1 y.2⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  simp only [PeriodPair.G]
  rw [← e.tsum_eq, Complex.conj_tsum]
  simp [e]

theorem latticeNormDisc_conjPeriods (L : PeriodPair) :
    latticeNormDisc (conjPeriods L) = latticeNormDisc L := by
  have e : (conjPeriods L).g₂ ^ 3 - 27 * (conjPeriods L).g₃ ^ 2 =
      starRingEnd ℂ (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    simp only [PeriodPair.g₂, PeriodPair.g₃, G_conjPeriods, map_sub, map_mul, map_pow, map_ofNat]
  have a : latticeArea (conjPeriods L) = latticeArea L := by
    rw [latticeArea_eq, latticeArea_eq_abs_im_mul_conj]
    simp [conjPeriods]
  rw [latticeNormDisc, latticeNormDisc, e, a, Complex.norm_conj]

theorem latticeNormDisc_eq_eta {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    latticeNormDisc L = (4 * π ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4) ^ 6 := by
  have hp : ((periodsOfUpperHalfPlane τ).ω₁ = 1 ∧ (periodsOfUpperHalfPlane τ).ω₂ = τ) ∨
      ((periodsOfUpperHalfPlane τ).ω₁ = τ ∧ (periodsOfUpperHalfPlane τ).ω₂ = 1) := by
    simp [periodsOfUpperHalfPlane]
  have H : IsHomothetic a (periodsOfUpperHalfPlane τ) L := by
    intro x
    rw [h, mem_lattice_iff_of_periods_eq hp]
    simp [ha]
  rw [H.latticeNormDisc_eq, latticeNormDisc, latticeArea_periodsOfUpperHalfPlane,
    (invariants_of_periods_eq hp).2.1]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_ofNat]
  ring

theorem log_pi_sub_log_latticeNormDisc {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    Real.log π - Real.log (|(L.ω₁ * starRingEnd ℂ L.ω₂).im| ^ 6 *
        ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖) / 6 =
      -Real.log (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) := by
  have hpos := latticeNormDisc_pos L
  rw [← latticeNormDisc_eq]
  rw [latticeNormDisc_eq_eta ha h] at hpos ⊢
  have hne : 4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4 ≠ 0 := by
    intro h0
    rw [show 4 * π ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4 =
      π * (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) by ring, h0] at hpos
    simp at hpos
  rw [Real.log_pow, show 4 * π ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4 =
      π * (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) by ring, Real.log_mul Real.pi_ne_zero hne]
  push_cast
  ring

section CM

variable {K : Type} [Field K] [NumberField K]

theorem embedding_eq_or_eq_conjugate (hK : Module.finrank ℚ K = 2) {σ₀ : K →+* ℂ}
    (h₀ : ¬ ComplexEmbedding.IsReal σ₀) (σ : K →+* ℂ) :
    σ = σ₀ ∨ σ = ComplexEmbedding.conjugate σ₀ := by
  classical
  have hne : σ₀ ≠ ComplexEmbedding.conjugate σ₀ := fun h =>
    h₀ (ComplexEmbedding.isReal_iff.2 h.symm)
  have : ({σ₀, ComplexEmbedding.conjugate σ₀} : Finset (K →+* ℂ)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, Embeddings.card, hK]
  have hm := this ▸ Finset.mem_univ σ
  simpa using hm

theorem exists_mul_mem_iff_of_mk0_eq (𝔞 𝔟 𝔡 : (Ideal (𝓞 K))⁰)
    (h : ClassGroup.mk0 𝔡 * ClassGroup.mk0 𝔟 = ClassGroup.mk0 𝔞) :
    ∃ u : K, u ≠ 0 ∧ ∀ t : K, (∀ b ∈ (𝔟 : Ideal (𝓞 K)), ∃ a ∈ (𝔞 : Ideal (𝓞 K)),
      u * t * (b : K) = a) ↔ ∃ d ∈ (𝔡 : Ideal (𝓞 K)), t = d := by
  rw [← map_mul, ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, e⟩ := h
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : K) ≠ 0 := by exact_mod_cast hy
  have hB : ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (nonZeroDivisors.coe_ne_zero 𝔟)
  have e' := congrArg (fun I : Ideal (𝓞 K) => (I : FractionalIdeal (𝓞 K)⁰ K)) e
  simp only [Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_span_singleton] at e'
  have hY : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K y) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hy'
  have key : ((𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) / (𝔟 : Ideal (𝓞 K)) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : K) / (y : K)) * (𝔡 : Ideal (𝓞 K)) := by
    rw [div_eq_iff hB]
    apply mul_left_cancel₀ hY
    rw [← e', ← mul_assoc, ← mul_assoc, ← mul_assoc,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 3
    change (x : K) = (y : K) * _
    field_simp
  refine ⟨x / y, div_ne_zero hx' hy', fun t => ?_⟩
  have h1 : (∀ b ∈ (𝔟 : Ideal (𝓞 K)), ∃ a ∈ (𝔞 : Ideal (𝓞 K)), (x : K) / y * t * (b : K) = a) ↔
      (x : K) / y * t ∈ ((𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) / (𝔟 : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.mem_div_iff_of_ne_zero hB]
    constructor
    · intro h b hb
      obtain ⟨b, hb', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
      obtain ⟨a, ha, e⟩ := h b hb'
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, e.symm⟩
    · intro h b hb
      obtain ⟨a, ha, e⟩ := (FractionalIdeal.mem_coeIdeal _).1
        (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hb))
      exact ⟨a, ha, e.symm⟩
  rw [h1, key, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨d, hd, e⟩
    obtain ⟨d, hd', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hd
    exact ⟨d, hd', mul_left_cancel₀ (div_ne_zero hx' hy') e⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨_, FractionalIdeal.mem_coeIdeal_of_mem _ hd, rfl⟩

theorem exists_isHomothetic_of_mk0_eq (σ : K →+* ℂ) (𝔞 𝔟 𝔡 : (Ideal (𝓞 K))⁰)
    (h : ClassGroup.mk0 𝔡 * ClassGroup.mk0 𝔟 = ClassGroup.mk0 𝔞) {L L' P : PeriodPair}
    {c β : ℂ} (hc : c ≠ 0) (hβ : β ≠ 0)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ a ∈ (𝔞 : Ideal (𝓞 K)), z = c * σ (a : K))
    (hL' : ∀ z, z ∈ L'.lattice ↔ ∀ y ∈ (𝔟 : Ideal (𝓞 K)), β⁻¹ * σ (y : K) * z ∈ L.lattice)
    (hP : ∀ z, z ∈ P.lattice ↔ ∃ d ∈ (𝔡 : Ideal (𝓞 K)), z = σ (d : K)) :
    ∃ κ : ℂ, IsHomothetic κ P L' := by
  obtain ⟨u, hu, H⟩ := exists_mul_mem_iff_of_mk0_eq 𝔞 𝔟 𝔡 h
  have hu' : σ u ≠ 0 := (map_ne_zero σ).2 hu
  refine ⟨β * c * σ u, fun z => ?_⟩
  have e : ∀ (y : 𝓞 K) (t : K), β⁻¹ * σ (y : K) * (β * c * σ u * σ t) = c * σ (u * t * y) := by
    intro y t
    rw [map_mul, map_mul]
    field_simp
  rw [hL', hP]
  constructor
  · intro hz
    obtain ⟨t, rfl⟩ : ∃ t : K, z = σ t := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (nonZeroDivisors.coe_ne_zero 𝔟)
      obtain ⟨a, -, ha⟩ := (hL _).1 (hz y hy)
      have hy1 : σ (y : K) ≠ 0 := by
        rw [map_ne_zero]; exact_mod_cast hy0
      refine ⟨a / (u * y), ?_⟩
      rw [map_div₀, map_mul]
      field_simp
      field_simp at ha
      linear_combination ha
    obtain ⟨d, hd, rfl⟩ := (H t).1 fun b hb => by
      obtain ⟨a, ha, e'⟩ := (hL _).1 (hz b hb)
      rw [e] at e'
      exact ⟨a, ha, σ.injective (mul_left_cancel₀ hc e')⟩
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩ y hy
    obtain ⟨a, ha, e'⟩ := (H d).2 ⟨d, hd, rfl⟩ y hy
    rw [e, e']
    exact (hL _).2 ⟨a, ha, rfl⟩

end CM

theorem mean_log_covolume_eq_mean_classGroup :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M], Module.finrank ℚ K = 2 →
  ∀ (σ₀ : K →+* ℂ), ¬ NumberField.ComplexEmbedding.IsReal σ₀ →
  ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))) (Lc : ClassGroup (𝓞 K) → PeriodPair), (∀ C, ClassGroup.mk0 (𝔟 C) = C) →
  (∀ C z, z ∈ (Lc C).lattice ↔ ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = σ₀ (a : K)) →
  ∀ (L₀ : (M →+* ℂ) → PeriodPair) (L : ClassGroup (𝓞 K) → (M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ) (β : ClassGroup (𝓞 K) → M),
  (∀ s (a : 𝓞 K), ∀ z ∈ (L₀ s).lattice, s (algebraMap K M a) * z ∈ (L₀ s).lattice) →
  (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s ((δ C : 𝓞 M) : M)) → (∀ C, β C ≠ 0) →
  (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β C * algebraMap K M x) ∧
    ∀ s, ∀ z ∈ (L₀ s).lattice, s (β C * algebraMap K M x) * z ∈ (L C s).lattice) →
  (∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ ((β C)⁻¹ * algebraMap K M (y : K)) ∧
    ∀ s, ∀ z ∈ (L C s).lattice, s ((β C)⁻¹ * algebraMap K M (y : K)) * z ∈ (L₀ s).lattice) →
  (∑ s : M →+* ℂ, Real.log |((L₀ s).ω₁ * starRingEnd ℂ (L₀ s).ω₂).im|) / Module.finrank ℚ M =
    (∑ C, Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 * ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖)) / (6 * Fintype.card (ClassGroup (𝓞 K))) := by
  intro K M _ _ _ _ _ hK σ₀ h₀ 𝔟 Lc h𝔟 hLc L₀ L δ β hst hδ hβ h1 h2
  simp only [← latticeNormDisc_eq]
  simp only [← latticeArea_eq_abs_im_mul_conj]
  have hb0 : ∀ C, (𝔟 C : Ideal (𝓞 K)) ≠ ⊥ := fun C => nonZeroDivisors.coe_ne_zero _
  have hnr : ∀ s : M →+* ℂ, ¬ ComplexEmbedding.IsReal (s.comp (algebraMap K M)) := by
    intro s
    rcases embedding_eq_or_eq_conjugate hK h₀ (s.comp (algebraMap K M)) with h | h <;> rw [h]
    · exact h₀
    · rwa [ComplexEmbedding.isReal_conjugate_iff]
  have hlat := fun C s => lattice_cm_eq_ideal_and_covolume K hK (s.comp (algebraMap K M)) (hnr s)
    (L₀ s) (L C s) (hst s)
  have hsβ : ∀ C (s : M →+* ℂ), s (β C) ≠ 0 := fun C s => (map_ne_zero s).2 (hβ C)
  have hdiv := fun C s => (hlat C s).2 (𝔟 C) (s (β C)) (hb0 C) (hsβ C s)
    (fun x hx z hz => by simpa using (h1 C x hx).2 s z hz)
    (fun y hy z hz => by simpa using (h2 C y hy).2 s z hz)

  have hA : ∀ C, ∑ s, Real.log (latticeNormDisc (L C s)) =
      6 * ∑ s, Real.log (latticeArea (L₀ s)) := by
    intro C
    have hN : (Ideal.absNorm (𝔟 C : Ideal (𝓞 K)) : ℝ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 (hb0 C)
    have hδ0 : ((δ C : 𝓞 M) : M) ≠ 0 := by exact_mod_cast (δ C).ne_zero
    have e1 : ∑ s : M →+* ℂ, Real.log ‖s ((δ C : 𝓞 M) : M)‖ = 0 := by
      have := sum_log_norm_embedding_eq_finrank_mul_log_absNorm M M ⊤ ((δ C : 𝓞 M) : M)
        top_ne_bot hδ0
        (fun x hx => (RingOfIntegers.isIntegral_coe _).mul (by simpa using hx 1 trivial))
        (fun y _ => by
          have : (((δ C : 𝓞 M) : M))⁻¹ = (((δ C)⁻¹ : (𝓞 M)ˣ) : 𝓞 M) := by
            apply inv_eq_of_mul_eq_one_right
            rw [← map_mul]; simp
          rw [this]
          exact (RingOfIntegers.isIntegral_coe _).mul (RingOfIntegers.isIntegral_coe _))
      simpa using this
    have e2 := sum_log_norm_embedding_eq_finrank_mul_log_absNorm K M (𝔟 C) (β C) (hb0 C) (hβ C)
      (fun x hx => (h1 C x hx).1) (fun y hy => (h2 C y hy).1)
    have e3 : ∀ s : M →+* ℂ, Real.log (latticeNormDisc (L C s)) =
        6 * (2 * Real.log ‖s (β C)‖ + Real.log (latticeArea (L₀ s)) -
          Real.log (Ideal.absNorm (𝔟 C : Ideal (𝓞 K)) : ℝ)) +
          Real.log ‖s ((δ C : 𝓞 M) : M)‖ := by
      intro s
      have h := congrArg Real.log (hdiv C s).2
      rw [← latticeArea_eq_abs_im_mul_conj, ← latticeArea_eq_abs_im_mul_conj,
        Real.log_mul (latticeArea_pos _).ne' hN,
        Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hsβ C s))) (latticeArea_pos _).ne',
        Real.log_pow] at h
      rw [latticeNormDisc, Real.log_mul (pow_pos (latticeArea_pos _) _).ne'
        (norm_ne_zero_iff.2 (g₂_cube_sub_g₃_sq_ne_zero _)), Real.log_pow, hδ]
      push_cast at h ⊢
      linarith
    have e4 : (Fintype.card (M →+* ℂ) : ℝ) = 2 * Module.finrank K M := by
      rw [Embeddings.card, ← Module.finrank_mul_finrank ℚ K M, hK]
      push_cast; ring
    simp only [e3, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, e4]
    ring

  have hB : ∀ s, ∑ C, Real.log (latticeNormDisc (L C s)) =
      ∑ C, Real.log (latticeNormDisc (Lc C)) := by
    intro s
    obtain ⟨𝔞, c, h𝔞, hc, hL⟩ := (hlat 1 s).1
    let 𝔞' : (Ideal (𝓞 K))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
    refine Fintype.sum_equiv (Equiv.divLeft (ClassGroup.mk0 𝔞')) _ _ fun C => ?_
    congr 1
    have hcl : ClassGroup.mk0 (𝔟 (ClassGroup.mk0 𝔞' / C)) * ClassGroup.mk0 (𝔟 C) =
        ClassGroup.mk0 𝔞' := by
      rw [h𝔟, h𝔟, div_mul_cancel]
    change _ = latticeNormDisc (Lc (ClassGroup.mk0 𝔞' / C))
    rcases embedding_eq_or_eq_conjugate hK h₀ (s.comp (algebraMap K M)) with h | h
    · obtain ⟨κ, H⟩ := exists_isHomothetic_of_mk0_eq (s.comp (algebraMap K M)) 𝔞' _ _ hcl hc
        (hsβ C s) hL (hdiv C s).1 (P := Lc (ClassGroup.mk0 𝔞' / C)) (by rw [h]; exact hLc _)
      exact H.latticeNormDisc_eq
    · obtain ⟨κ, H⟩ := exists_isHomothetic_of_mk0_eq (s.comp (algebraMap K M)) 𝔞' _ _ hcl hc
        (hsβ C s) hL (hdiv C s).1 (P := conjPeriods (Lc (ClassGroup.mk0 𝔞' / C))) (by
          intro z
          rw [h, mem_conjPeriods_lattice, hLc]
          refine exists_congr fun a => and_congr_right fun _ => ?_
          rw [ComplexEmbedding.conjugate_coe_eq]
          constructor
          · intro e; rw [← e]; simp
          · intro e; rw [e]; simp)
      rw [H.latticeNormDisc_eq, latticeNormDisc_conjPeriods]
  have hS := Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun C s => Real.log (latticeNormDisc (L C s)))
  simp only [hA, hB, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Embeddings.card] at hS
  have hm : (Module.finrank ℚ M : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hh : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  linear_combination hS

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralDerivativeCurveHomGoodReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralDerivativeCurveHomGoodReduction
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace HomIntegral

theorem isLieComb_single_iff {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (c : R) (v w : epsR R ⟶ G) :
    IsLieComb ![c] ![v] w ↔ w.left = spMap (epsScaleR c) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    exact ⟨fun _ => w, fun i => by fin_cases i; exact h, by simp⟩

theorem isLieComb_fibre {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} {G H : Over (Sp R)} [GrpObj H]
    {G' H' : Over (Sp R')} [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hψ : IsPullback ψ H'.hom H.hom (spMap g)) {F : G ⟶ H} {f : G' ⟶ H'} (hf : f.left ≫ ψ = φ ≫ F.left)
    {v : epsR R ⟶ G} {t : epsR R ⟶ H} {v' : epsR R' ⟶ G'} {t' : epsR R' ⟶ H'} (hv : IsVecOver g φ v v')
    (ht : IsVecOver g ψ t t') {b : R} (h : IsLieComb ![b] ![t] (v ≫ F)) : IsLieComb ![g b] ![t'] (v' ≫ f) := by
  rw [isLieComb_single_iff] at h ⊢
  unfold IsVecOver at hv ht
  refine hψ.hom_ext ?_ ?_
  · rw [Over.comp_left] at h
    rw [Over.comp_left, Category.assoc, hf, ← Category.assoc, hv, Category.assoc, h, Category.assoc, ht,
      ← Category.assoc, ← Category.assoc]
    congr 1
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
    congr 1
    ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [Over.w, Category.assoc, Over.w t']
    refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
    change spMap _ = spMap _
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_extension {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] [GrpObj H]
    (h : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f →
      ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback j).map F = f)
    {G' H' : Over S'} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback H' H j ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃ F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hψ (isGrpPullback_pullback H j)
  obtain ⟨F, ⟨hF, e⟩, -⟩ := h (a.inv ≫ f ≫ b.hom) inferInstance
  refine ⟨F, hF, ?_⟩
  have e₁ : ((Over.pullback j).map F).left ≫ pullback.fst H.hom j = pullback.fst G.hom j ≫ F.left :=
    pullback.lift_fst _ _ _
  have e₂ : f ≫ b.hom = a.hom ≫ (Over.pullback j).map F := by rw [e, Iso.hom_inv_id_assoc]
  rw [← ha', ← hb', ← Category.assoc, ← Over.comp_left, e₂, Over.comp_left, Category.assoc, Category.assoc]
  exact congrArg (a.hom.left ≫ ·) e₁

end HomIntegral


open HomIntegral in
theorem isIntegral_of_hom_derivative : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.PolBaseChangeSt → ∀ (M : Type) [Field M] [NumberField M] (P Q : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (t : epsR (𝓞 M) ⟶ Q.A) (a : M), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) Q Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) → IsIntegral ℤ a := by
  intro hext hB M _ _ P Q v t a hv ht hf
  have key : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 M),
      a ∈ Localization.subalgebra.ofField M _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors := by
    intro 𝔭
    set T := Localization.subalgebra.ofField M _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors with hT
    have : IsDiscreteValuationRing T :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 M) 𝔭.ne_bot T
    have : IsFractionRing T M := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.asIdeal.primeCompl T M
    have e : (algebraMap T M).comp (algebraMap (𝓞 M) T) = algebraMap (𝓞 M) M :=
      (IsScalarTower.algebraMap_eq _ _ _).symm
    obtain ⟨P₀, φ₀, hP₀⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) T) P
    obtain ⟨Q₀, ψ₀, hQ₀⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) T) Q
    obtain ⟨P₁, φ₁, hP₁⟩ := exists_isPolFibre hB (algebraMap T M) P₀
    obtain ⟨Q₁, ψ₁, hQ₁⟩ := exists_isPolFibre hB (algebraMap T M) Q₀
    obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hP₀.2.1.1 v
    obtain ⟨t₀, ht₀, -⟩ := existsUnique_isVecOver hQ₀.2.1.1 t
    obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver hP₁.2.1.1 v₀
    obtain ⟨t₁, ht₁, -⟩ := existsUnique_isVecOver hQ₁.2.1.1 t₀
    have hP := e ▸ PolFibre.comp hP₀ hP₁
    have hQ := e ▸ PolFibre.comp hQ₀ hQ₁
    have hv' := e ▸ (PolFibre.vec_iff hP₀.2.1.1 hP₁.2.1.1.w hv₀).1 hv₁
    have ht' := e ▸ (PolFibre.vec_iff hQ₀.2.1.1 hQ₁.2.1.1.w ht₀).1 ht₁
    obtain ⟨f, hfm, hfa⟩ := hf P₁ Q₁ _ _ v₁ t₁ hP hQ hv' ht'
    obtain ⟨F, hF, hFf⟩ := exists_extension (hext T M P₀.A Q₀.A (isSemiAbelian_of_isAbelianScheme _ P₀.isAb)
      (isSemiAbelian_of_isAbelianScheme _ Q₀.isAb)) hP₁.2.1 hQ₁.2.1 f
    have tv₀ := hv₀.isTangent hP₀.2.1 hv
    obtain ⟨c, hc, -⟩ := (ht T _ Q₀ ψ₀ t₀ hQ₀ ht₀).2 _ (isTangent_comp_of_isMonHom F v₀ tv₀)
    have ec : c = ![c 0] := by funext i; fin_cases i; rfl
    rw [ec] at hc
    have h₁ := isLieComb_fibre hQ₁.2.1.1 hFf hv₁ ht₁ hc
    have u := ((ht M _ Q₁ _ t₁ hQ ht').2 _
      (isTangent_comp_of_isMonHom f v₁ (hv₁.isTangent hP₁.2.1 tv₀))).unique hfa h₁
    have ea : a = algebraMap T M (c 0) := congrFun u 0
    rw [ea]
    exact (c 0).2
  have h := Algebra.mem_iInf.2 key
  rw [IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot, Algebra.mem_bot] at h
  obtain ⟨x, rfl⟩ := h
  exact x.isIntegral_coe

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralDerivativeCurveHomGoodReductionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.isIntegral_derivative_curve_hom_good_reduction : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.PolBaseChangeSt → ∀ (M : Type) [Field M] [NumberField M] (P Q : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (t : epsR (𝓞 M) ⟶ Q.A) (a : M), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) Q Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) → IsIntegral ℤ a := by
  first | exact @GlobalTheory.isIntegral_of_hom_derivative | exact GlobalTheory.isIntegral_of_hom_derivative | (intros; apply GlobalTheory.isIntegral_of_hom_derivative <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LogPiSubMeanLogLatticeNormDisc
open NumberField
open scoped nonZeroDivisors UpperHalfPlane

namespace GlobalTheory

theorem IsIdealClassPoint.exists_lattice_eq {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {𝔟 : (Ideal (𝓞 K))⁰} {τ : ℍ} (hτ : IsIdealClassPoint σ (ClassGroup.mk0 𝔟) τ)
    {P : PeriodPair} (hP : ∀ z, z ∈ P.lattice ↔ ∃ a ∈ (𝔟 : Ideal (𝓞 K)), z = σ (a : K)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ x, x ∈ P.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := by
  classical
  obtain ⟨𝔞, ω, h𝔞, hω⟩ := hτ
  set J := FractionalIdeal.mk0 K 𝔟 with hJ
  have hcl : ClassGroup.mk K (𝔞⁻¹ * J) = 1 := by
    rw [map_mul, map_inv, h𝔞, hJ, ClassGroup.mk_mk0, inv_mul_cancel]
  obtain ⟨x₀, hx₀⟩ := (ClassGroup.mk_eq_one_iff.1 hcl).principal

  have hJx : ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
    have h1 : ((𝔞⁻¹ * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ := by
      apply FractionalIdeal.coeToSubmodule_injective
      dsimp only
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx₀
    have h2 : J = 𝔞 * (𝔞⁻¹ * J) := (mul_inv_cancel_left 𝔞 J).symm
    conv_lhs => rw [h2]
    rw [Units.val_mul, h1, mul_comm]
  have hmemJ : ∀ y : K, (∃ b ∈ (𝔟 : Ideal (𝓞 K)), (b : K) = y) ↔
      ∃ y' ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), y = x₀ * y' := by
    intro y
    rw [← FractionalIdeal.mem_singleton_mul, ← hJx, hJ, FractionalIdeal.coe_mk0,
      FractionalIdeal.mem_coeIdeal]
  have hmem : ∀ z, z ∈ P.lattice ↔ ∃ m n : ℤ, σ x₀ * ω * (m * (τ : ℂ) + n) = z := by
    intro z
    rw [hP]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨y', hy', hby⟩ := (hmemJ _).1 ⟨b, hb, rfl⟩
      obtain ⟨m, n, hmn⟩ := (hω (σ y')).1 ⟨y', hy', rfl⟩
      exact ⟨m, n, by rw [hby, map_mul, ← hmn]; ring⟩
    · rintro ⟨m, n, rfl⟩
      obtain ⟨y', hy', hy'eq⟩ := (hω (ω * (m * (τ : ℂ) + n))).2 ⟨m, n, rfl⟩
      obtain ⟨b, hb, hbeq⟩ := (hmemJ (x₀ * y')).2 ⟨y', hy', rfl⟩
      exact ⟨b, hb, by rw [hbeq, map_mul, hy'eq]; ring⟩
  refine ⟨σ x₀ * ω, ?_, hmem⟩
  intro ha
  obtain ⟨m, n, hmn⟩ := (hmem P.ω₁).1 P.ω₁_mem_lattice
  rw [ha, zero_mul] at hmn
  exact P.indep.ne_zero 0 (by simpa using hmn.symm)

theorem log_pi_sub_mean_log_latticeNormDisc :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), ∀ (Lc : ClassGroup (𝓞 K) → PeriodPair), (∀ C, ClassGroup.mk0 (𝔟 C) = C) → (∀ C z, z ∈ (Lc C).lattice ↔ ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = σ₀ (a : K)) → ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) → Real.log Real.pi - (∑ C, Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 * ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖)) / (6 * Fintype.card (ClassGroup (𝓞 K))) = (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
  intro K _ _ hK σ₀ h₀ 𝔟 Lc h𝔟 hL σ τ hτ
  classical

  have key : ∀ C, Real.log Real.pi - Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 *
      ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖) / 6 =
      -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4) := by
    intro C
    have hτC : IsIdealClassPoint σ (ClassGroup.mk0 (𝔟 C)) (τ C) := by
      rw [h𝔟 C]
      exact hτ C
    rcases embedding_eq_or_eq_conjugate hK h₀ σ with rfl | rfl
    · obtain ⟨a, ha, h⟩ := hτC.exists_lattice_eq (hL C)
      exact log_pi_sub_log_latticeNormDisc ha h
    · have hP : ∀ z, z ∈ (conjPeriods (Lc C)).lattice ↔
          ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = ComplexEmbedding.conjugate σ₀ (a : K) := by
        intro z
        rw [mem_conjPeriods_lattice, hL]
        refine exists_congr fun a => and_congr_right fun _ => ?_
        rw [ComplexEmbedding.conjugate_coe_eq]
        constructor
        · intro h
          rw [← h, Complex.conj_conj]
        · intro h
          rw [h, Complex.conj_conj]
      obtain ⟨a, ha, h⟩ := hτC.exists_lattice_eq hP
      have e := log_pi_sub_log_latticeNormDisc ha h
      rw [← latticeNormDisc_eq, latticeNormDisc_conjPeriods, latticeNormDisc_eq] at e
      exact e
  have hh : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp_rw [← key]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div]
  simp only [NumberField.classNumber]
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogLieNormSqEqMeanLogEta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem exists_periodPair_image_ideal {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {σ : K →+* ℂ} (hσ : ¬ ComplexEmbedding.IsReal σ) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ a ∈ I, z = σ (a : K) := by
  have hr : Module.finrank ℤ I = 2 :=
    (Ideal.finrank_eq_finrank (RingOfIntegers.basis K) I hI).trans ((RingOfIntegers.rank K).trans hK)
  let b : Module.Basis (Fin 2) ℤ I := Module.finBasisOfFinrankEq ℤ _ hr
  have hs : ∀ x : I, σ ((x : 𝓞 K) : K) =
      b.repr x 0 * σ ((b 0 : 𝓞 K) : K) + b.repr x 1 * σ ((b 1 : 𝓞 K) : K) := by
    intro x
    have := congrArg (fun x : I => σ ((x : 𝓞 K) : K)) (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  obtain ⟨a, ha⟩ := CMLattice.exists_im_ne_zero σ hσ
  have hb0 : σ ((b 0 : 𝓞 K) : K) ≠ 0 := by
    rw [map_ne_zero]
    have : (b 0 : 𝓞 K) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
    exact_mod_cast this
  have h0 : (σ ((b 1 : 𝓞 K) : K) * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im ≠ 0 := by
    intro h0
    have e := hs ⟨a * b 0, I.mul_mem_left a (b 0).2⟩
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at e' h0 ha hb0
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨σ ((b 0 : 𝓞 K) : K), σ ((b 1 : 𝓞 K) : K), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 1 : 𝓞 K) : K)).im * e1 - (σ ((b 1 : 𝓞 K) : K)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 0 : 𝓞 K) : K)).re * e2 - (σ ((b 0 : 𝓞 K) : K)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, _, (hs ⟨x, hx⟩).symm⟩

theorem mean_log_lieNormSq_eq_mean_log_eta :
    ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), (∀ C, ClassGroup.mk0 (𝔟 C) = C) → ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀ s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) → (∃ β : ClassGroup (𝓞 K) → M, (∀ C, β C ≠ 0) ∧ (∀ a : 𝓞 K, (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![κ (a : K)] ![t₁] (v₁ ≫ f₁))) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ (Q C).A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) (Q C) Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ (t C) t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![β C * κ x] ![t₁] (v₁ ≫ f₁))) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ (Q C).A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) (Q C) P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ (t C) v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![(β C)⁻¹ * κ (y : K)] ![t₁] (v₁ ≫ f₁))) → ∀ n : (M →+* ℂ) → ℝ, (∀ s, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) (n s)) → ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) → (∑ s, Real.log (n s)) / Module.finrank ℚ M = (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
  intro hU hB hN K _ _ hK σ₀ h₀ 𝔟 h𝔟 M _ κ P v L₀ Q t L δ ⟨_, ⟨hPg, hv, hvb, hPL⟩, hQ, hδ, _⟩
    ⟨β, hβ, hEnd, h1, h2⟩ n hn σ τ hτ
  let _ : Algebra K M := κ.toAlgebra
  have hvt : IsTangent v := hv.1 0
  have htt : ∀ C, IsTangent (t C) := fun C => (hQ C).2.1.1 0
  obtain ⟨P₀, φ, hφ⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) M) P
  obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
  choose Q₀ ψ hψ using fun C => exists_isPolFibre hB (algebraMap (𝓞 M) M) (Q C)
  choose t₀ ht₀ using fun C => (existsUnique_isVecOver (hψ C).2.1.1 (t C)).exists
  choose Lc hLc using fun C => exists_periodPair_image_ideal hK h₀ (nonZeroDivisors.coe_ne_zero (𝔟 C))
  have key := mean_log_covolume_eq_mean_classGroup K M hK σ₀ h₀ 𝔟 Lc h𝔟 hLc
    (fun s => L₀ (s.comp (algebraMap (𝓞 M) M))) (fun C s => L C (s.comp (algebraMap (𝓞 M) M))) δ β
    (fun s a => by
      obtain ⟨f, hf, hc⟩ := hEnd a P₀ P₀ φ φ v₀ v₀ hφ hφ hv₀ hv₀
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ P P v v _ _ _ _ hPg hPg hvt hvt (hPL _) (hPL _)).2
        (hom_deriv_baseChange _ P P v v _ _ P₀ P₀ φ φ v₀ v₀ f _ hφ hφ hv₀ hv₀ hf hc ℂ s))
    (fun C s => hδ C _) hβ
    (fun C x hx => ⟨T.isIntegral_derivative_curve_hom_good_reduction hN hB M P (Q C) v (t C) _ hvt (hQ C).2.2.1 (h1 C x hx), fun s => by
      obtain ⟨f, hf, hc⟩ := h1 C x hx P₀ (Q₀ C) φ (ψ C) v₀ (t₀ C) hφ (hψ C) hv₀ (ht₀ C)
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ P (Q C) v (t C) _ _ _ _ hPg (hQ C).1 hvt (htt C) (hPL _) ((hQ C).2.2.2 _)).2
        (hom_deriv_baseChange _ P (Q C) v (t C) _ _ _ _ _ _ _ _ f _ hφ (hψ C) hv₀ (ht₀ C) hf hc ℂ s)⟩)
    (fun C y hy => ⟨T.isIntegral_derivative_curve_hom_good_reduction hN hB M (Q C) P (t C) v _ (htt C) hvb (h2 C y hy), fun s => by
      obtain ⟨f, hf, hc⟩ := h2 C y hy (Q₀ C) P₀ (ψ C) φ (t₀ C) v₀ (hψ C) hφ (ht₀ C) hv₀
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ (Q C) P (t C) v _ _ _ _ (hQ C).1 hPg (htt C) hvt ((hQ C).2.2.2 _) (hPL _)).2
        (hom_deriv_baseChange _ (Q C) P (t C) v _ _ _ _ _ _ _ _ f _ (hψ C) hφ (ht₀ C) hv₀ hf hc ℂ s)⟩)
  rw [← log_pi_sub_mean_log_latticeNormDisc K hK σ₀ h₀ 𝔟 Lc h𝔟 hLc σ τ hτ, ← key]
  have hlog : ∀ s : M →+* ℂ, Real.log (n s) = Real.log Real.pi -
      Real.log |((L₀ (s.comp (algebraMap (𝓞 M) M))).ω₁ *
        starRingEnd ℂ (L₀ (s.comp (algebraMap (𝓞 M) M))).ω₂).im| := by
    intro s
    obtain ⟨hp, hr⟩ := isLieNormSq_iff_eq_pi_div_covolume hU hB _ P v _ _ hPg hvt (hPL (s.comp (algebraMap (𝓞 M) M)))
    rw [(hr _).1 (hn s), Real.log_div Real.pi_ne_zero]
    intro h
    rw [h, div_zero] at hp
    exact lt_irrefl _ hp
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  simp only [hlog, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogLieNormSqEqMeanLogEtaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_log_lieNormSq_eq_mean_log_eta_alt : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), (∀ C, ClassGroup.mk0 (𝔟 C) = C) → ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀ s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) → (∃ β : ClassGroup (𝓞 K) → M, (∀ C, β C ≠ 0) ∧ (∀ a : 𝓞 K, (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![κ (a : K)] ![t₁] (v₁ ≫ f₁))) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ (Q C).A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) (Q C) Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ (t C) t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![β C * κ x] ![t₁] (v₁ ≫ f₁))) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ (Q C).A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) (Q C) P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ (t C) v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![(β C)⁻¹ * κ (y : K)] ![t₁] (v₁ ≫ f₁))) → ∀ n : (M →+* ℂ) → ℝ, (∀ s, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) (n s)) → ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) → (∑ s, Real.log (n s)) / Module.finrank ℚ M = (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
  first | exact @GlobalTheory.mean_log_lieNormSq_eq_mean_log_eta | exact GlobalTheory.mean_log_lieNormSq_eq_mean_log_eta | (intros; apply GlobalTheory.mean_log_lieNormSq_eq_mean_log_eta <;> assumption)
end
