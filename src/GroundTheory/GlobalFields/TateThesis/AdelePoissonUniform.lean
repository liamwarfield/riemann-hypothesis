module

public import GroundTheory.GlobalFields.TateThesis.AdelePoisson
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaInfinite
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite

@[expose] public section

section -- merged from GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem exists_mul_mem_integralFiniteAdeles_of_isCompact {S : Set 𝔸ᶠ[K]} (hS : IsCompact S) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ s ∈ S,
      algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d) * s ∈ integralFiniteAdeles (𝓞 K) K := by
  have hint : ∀ r : 𝓞 K,
      algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K r) ∈ integralFiniteAdeles (𝓞 K) K :=
    fun r v ↦ coe_algebraMap_mem_adicCompletionIntegers v r
  let U : {d : 𝓞 K // d ≠ 0} → Set 𝔸ᶠ[K] := fun d ↦
    {s | algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d.1) * s ∈ integralFiniteAdeles (𝓞 K) K}
  have hUo : ∀ d, IsOpen (U d) := fun d ↦
    isOpen_integralFiniteAdeles.preimage (continuous_const_mul _)
  have hsU : S ⊆ ⋃ d, U d := by
    intro s _
    obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) s
    obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hmK : algebraMap (𝓞 K) K m ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hm0
    refine Set.mem_iUnion.mpr ⟨⟨m, hm0⟩, ?_⟩
    have h : algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * s =
        algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K n) + algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) *
          (s - algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K m)) := by
      rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hmK]
      ring
    show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * s ∈ integralFiniteAdeles (𝓞 K) K
    rw [h]
    exact add_mem (hint n) (mul_mem (hint m) hk)
  have hdU : Directed (· ⊆ ·) U := by
    intro d e
    refine ⟨⟨d.1 * e.1, mul_ne_zero d.2 e.2⟩, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
    · have := mul_mem (hint e.1) hs
      show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K (d.1 * e.1)) * s ∈ integralFiniteAdeles (𝓞 K) K
      rwa [map_mul, map_mul, mul_comm (algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d.1)), mul_assoc]
    · have := mul_mem (hint d.1) hs
      show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K (d.1 * e.1)) * s ∈ integralFiniteAdeles (𝓞 K) K
      rwa [map_mul, map_mul, mul_assoc]
  have : Nonempty {d : 𝓞 K // d ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  obtain ⟨d, hd⟩ := hS.elim_directed_cover U hUo hsU hdU
  exact ⟨d.1, d.2, fun s hs ↦ hd hs⟩

theorem summable_ite_mem_of_summable_idealLattice (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {h : mixedSpace K → ℝ} (hh : Summable fun α : idealLattice K J ↦ h α) :
    Summable fun ξ : K ↦
      if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then h (mixedEmbedding K ξ) else 0 := by
  set e := idealLatticeEquiv J
  let g : idealLattice K J → K := fun α ↦ ((e.symm α : _) : K)
  have hinj : Function.Injective g := fun α β hαβ ↦ e.symm.injective (Subtype.ext hαβ)
  have hsupp : ∀ ξ ∉ Set.range g,
      (if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then h (mixedEmbedding K ξ) else 0) = 0 := by
    intro ξ hξ
    rw [if_neg]
    intro hm
    exact hξ ⟨e ⟨ξ, hm⟩, by simp [g]⟩
  rw [← hinj.summable_iff hsupp]
  convert hh using 1
  funext α
  change (if ((e.symm α : _) : K) ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then
    h (mixedEmbedding K ((e.symm α : _) : K)) else 0) = h α
  rw [if_pos (show ((e.symm α : _) : K) ∈ (J : FractionalIdeal (𝓞 K)⁰ K) from (e.symm α).2)]
  have he := coe_idealLatticeEquiv J (e.symm α)
  rw [Equiv.apply_symm_apply] at he
  rw [he]

theorem summable_inv_one_add_norm_pow_idealLattice (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Summable fun α : idealLattice K J ↦
      ((1 + ‖(α : mixedSpace K)‖) ^ (Module.finrank ℤ (idealLattice K J) + 1))⁻¹ := by
  have hs := ZLattice.summable_norm_pow_inv (L := idealLattice K J)
    (Module.finrank ℤ (idealLattice K J) + 1) (by omega)
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [(Set.finite_singleton (0 : idealLattice K J)).compl_mem_cofinite] with ℓ hℓ
  have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
  rw [Real.norm_of_nonneg (by positivity), inv_pow]
  gcongr
  change ‖ℓ‖ ≤ 1 + ‖ℓ‖
  linarith

theorem exists_summable_bound_tensor_cosetIndicator (φ : 𝓢(mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]) {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ ξ : K,
      ‖schwartzBruhatTensor φ (cosetIndicator I b) (a • algebraMap K 𝔸[K] ξ)‖ ≤ u ξ := by

  set S : Set 𝔸ᶠ[K] := (fun p : IdeleGroup K × 𝔸ᶠ[K] ↦
      ((IdeleGroup.toFinite K p.1⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * p.2) ''
    (C ×ˢ (b +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])))
  have hS : IsCompact S := (hC.prod ((isCompact_idealFiniteAdeles I).vadd b)).image
    ((Units.continuous_val.comp ((IdeleGroup.continuous_toFinite (K := K)).comp
      (continuous_inv.comp continuous_fst))).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK))
  have hJ : ∀ a ∈ C, ∀ ξ : K,
      ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ - b ∈
        idealFiniteAdeles I → ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a ha ξ hξ
    have hmem : algebraMap K 𝔸ᶠ[K] ξ ∈ S := by
      refine ⟨(a, ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ),
        ⟨ha, mem_vadd_idealFiniteAdeles.mpr hξ⟩, ?_⟩
      simp only [map_inv, Units.inv_mul_cancel_left]
    have h1 := hd _ hmem
    rw [← map_mul] at h1
    have h2 : dK * ξ ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
      exact h1
    rw [Units.val_one] at h2
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
    refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
    rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

  set k := Module.finrank ℤ (idealLattice K J) + 1
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ k
  have hcont : Continuous fun a : IdeleGroup K ↦ ‖homeomorphMixedSpace K
      ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ :=
    continuous_norm.comp ((homeomorphMixedSpace K).continuous.comp (Units.continuous_val.comp
      ((IdeleGroup.continuous_toInfinite (K := K)).comp continuous_inv)))
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  refine ⟨fun ξ ↦ if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then
      A * B' ^ k * ((1 + ‖mixedEmbedding K ξ‖) ^ k)⁻¹ else 0, ?_, ?_⟩
  · exact summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ A * B' ^ k * ((1 + ‖x‖) ^ k)⁻¹)
      ((summable_inv_one_add_norm_pow_idealLattice J).mul_left (A * B' ^ k))
  intro a ha ξ
  set c := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  set c' := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  have hcc : c' * c = 1 := by
    rw [← homeomorphMixedSpace_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, homeomorphMixedSpace_apply, map_one]
  have hval : schwartzBruhatTensor φ (cosetIndicator I b) (a • algebraMap K 𝔸[K] ξ) =
      φ (c * mixedEmbedding K ξ) * cosetIndicator I b
        (((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ) := by
    have h1 : (a • algebraMap K 𝔸[K] ξ).1 = ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K) * algebraMap K (InfiniteAdeleRing K) ξ := rfl
    have h2 : (a • algebraMap K 𝔸[K] ξ).2 =
        ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ := rfl
    simp only [schwartzBruhatTensor]
    rw [h1, h2, homeomorphMixedSpace_mul, homeomorphMixedSpace_algebraMap]
  rw [hval, cosetIndicator_apply]
  beta_reduce
  split_ifs with hm hJm hJm
  · rw [mul_one]
    set x := mixedEmbedding K ξ
    have hx : ‖x‖ ≤ B' * ‖c * x‖ := by
      calc ‖x‖ = ‖c' * (c * x)‖ := by rw [← mul_assoc, hcc, one_mul]
        _ ≤ ‖c'‖ * ‖c * x‖ := norm_mul_le _ _
        _ ≤ B' * ‖c * x‖ := by
          gcongr
          exact ((norm_norm _).symm.trans_le (hB a ha)).trans (le_max_left _ _)
    have key : 1 + ‖x‖ ≤ B' * (1 + ‖c * x‖) := by nlinarith [norm_nonneg (c * x)]
    calc ‖φ (c * x)‖ ≤ A * ((1 + ‖c * x‖) ^ k)⁻¹ := hφ _
      _ = A * (B' ^ k * ((B' * (1 + ‖c * x‖)) ^ k)⁻¹) := by
          rw [mul_pow, mul_inv, ← mul_assoc (B' ^ k), mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ A * (B' ^ k * ((1 + ‖x‖) ^ k)⁻¹) := by gcongr
      _ = A * B' ^ k * ((1 + ‖x‖) ^ k)⁻¹ := by ring
  · exact absurd (hJ a ha ξ hm) hJm
  · rw [mul_zero, norm_zero]
    positivity
  · rw [mul_zero, norm_zero]

theorem exists_summable_bound_smul_algebraMap {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ ξ : K, ‖F (a • algebraMap K 𝔸[K] ξ)‖ ≤ u ξ := by
  have hF' := schwartzBruhat_le_span_cosetIndicator hF
  clear hF
  induction hF' using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_summable_bound_tensor_cosetIndicator φ I b hC
  | zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨w, hw, hHw⟩ := hH
    exact ⟨u + w, hu.add hw, fun a ha ξ ↦ (norm_add_le _ _).trans (add_le_add (hGu a ha ξ) (hHw a ha ξ))⟩
  | smul r G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖r‖ * u ξ, hu.mul_left _, fun a ha ξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGu a ha ξ) (norm_nonneg r)

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.TateThesis.GlobalZeta
open NumberField IsDedekindDomain Topology Filter MeasureTheory NumberField.mixedEmbedding Metric
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap nonZeroDivisors Classical

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem continuous_of_mem_schwartzBruhat {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    Continuous F := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    exact (φ.continuous.comp ((homeomorphMixedSpace K).continuous.comp continuous_fst)).mul
      (hg.1.continuous.comp continuous_snd)
  | zero => exact continuous_const
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.const_smul c

theorem continuous_ideleModule_val : Continuous fun x : IdeleGroup K ↦ (ideleModule K x : ℝ) :=
  continuous_subtype_val.comp continuous_ideleModule

theorem infiniteZetaBound_nonneg (σ : ℝ) (k : ℕ) (a : (InfiniteAdeleRing K)ˣ) :
    0 ≤ infiniteZetaBound σ k a :=
  Finset.prod_nonneg fun w _ ↦ by positivity

theorem ideleModule_rpow_eq (x : IdeleGroup K) (σ : ℝ) :
    (ideleModule K x : ℝ) ^ σ = (∏ w, ‖((toInfinite K x : (InfiniteAdeleRing K)ˣ) :
      InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)) * finiteModule (ofFinite (toFinite K x)) ^ σ := by
  rw [ideleModule_apply, Real.mul_rpow (infiniteModule_pos x).le (finiteModule_pos x).le,
    infiniteModule, ← Real.finsetProd_rpow _ _ (fun w _ ↦ by positivity)]
  congr 1
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  rfl

theorem exists_bound_schwartzBruhatTensor (φ : 𝓢(mixedSpace K, ℂ))
    {g : FiniteAdeleRing (𝓞 K) K → ℂ} (hg : g ∈ finiteSchwartzBruhat K) (σ : ℝ) :
    ∃ C : ℝ, ∃ k : ℕ, ∃ L : (FractionalIdeal (𝓞 K)⁰ K)ˣ, 0 ≤ C ∧ 2 * σ + 2 < k ∧
      ∀ x : IdeleGroup K, ‖schwartzBruhatTensor φ g (x : 𝔸[K])‖ * (ideleModule K x : ℝ) ^ σ ≤
        C * (infiniteZetaBound σ k (toInfinite K x) * finiteZetaBound L σ (toFinite K x)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * σ + 2 < k := exists_nat_gt _
  obtain ⟨C₁, hC₁, hφ⟩ := exists_norm_schwartz_le_prod φ k
  obtain ⟨M, hM⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles hg.2
  refine ⟨C₁ * max M 0, k, L, by positivity, hk, fun x ↦ ?_⟩
  set a := toInfinite K x
  set b := toFinite K x
  have hinf : ‖φ (homeomorphMixedSpace K (x : 𝔸[K]).1)‖ *
      ∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ) ≤ C₁ * infiniteZetaBound σ k a := by
    calc ‖φ (homeomorphMixedSpace K (x : 𝔸[K]).1)‖ *
          ∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)
        ≤ (C₁ * ∏ w, ((1 + ‖(a : InfiniteAdeleRing K) w‖) ^ k)⁻¹) *
            ∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ) :=
          mul_le_mul_of_nonneg_right (hφ _) (Finset.prod_nonneg fun w _ ↦ by positivity)
      _ = C₁ * infiniteZetaBound σ k a := by
          rw [mul_assoc, ← Finset.prod_mul_distrib, infiniteZetaBound]
          congr 1
          refine Finset.prod_congr rfl fun w _ ↦ ?_
          rw [div_eq_mul_inv, mul_comm]
  have hI := infiniteZetaBound_nonneg σ k a
  unfold schwartzBruhatTensor
  by_cases hb : (b : FiniteAdeleRing (𝓞 K) K) ∈ idealFiniteAdeles L
  · have hfz : finiteZetaBound L σ b = finiteModule (ofFinite b) ^ σ := by
      rw [finiteZetaBound, if_pos hb]
    rw [hfz, ideleModule_rpow_eq, norm_mul]
    have hgM : ‖g (x : 𝔸[K]).2‖ ≤ max M 0 := (hM _).trans (le_max_left _ _)
    have hfm : 0 ≤ finiteModule (ofFinite b) ^ σ := by
      have := finiteModule_pos (ofFinite b)
      positivity
    calc ‖φ (homeomorphMixedSpace K (x : 𝔸[K]).1)‖ * ‖g (x : 𝔸[K]).2‖ *
          ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)) *
            finiteModule (ofFinite b) ^ σ)
        = (‖φ (homeomorphMixedSpace K (x : 𝔸[K]).1)‖ *
            ∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)) * ‖g (x : 𝔸[K]).2‖ *
              finiteModule (ofFinite b) ^ σ := by ring
      _ ≤ (C₁ * infiniteZetaBound σ k a) * max M 0 * finiteModule (ofFinite b) ^ σ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hinf hgM (norm_nonneg _) (mul_nonneg hC₁ hI)) hfm
      _ = C₁ * max M 0 * (infiniteZetaBound σ k a * finiteModule (ofFinite b) ^ σ) := by ring
  · have hg0 : g (x : 𝔸[K]).2 = 0 := by
      by_contra h
      exact hb (hL (subset_tsupport g h))
    rw [hg0, mul_zero, norm_zero, zero_mul]
    exact mul_nonneg (by positivity) (mul_nonneg hI (finiteZetaBound_nonneg _ _ _))

theorem integrable_zetaBound {σ : ℝ} (hσ : 1 < σ) {k : ℕ} (hk : 2 * σ + 2 < k)
    (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Integrable (fun x : IdeleGroup K ↦
      infiniteZetaBound σ k (toInfinite K x) * finiteZetaBound L σ (toFinite K x))
      (ideleMeasure K) := by
  have h := (integrable_infiniteZetaBound (K := K) hσ.le hk).mul_prod
    (integrable_finiteZetaBound L hσ)
  exact ((measurePreserving_prodEquiv K).integrable_comp_emb
    (prodEquiv K).toHomeomorph.measurableEmbedding).2 h

theorem continuous_norm_mul_rpow {F : 𝔸[K] → ℂ} (hF : Continuous F) {σ : ℝ} (hσ : 0 ≤ σ) :
    Continuous fun x : IdeleGroup K ↦ ‖F x‖ * (ideleModule K x : ℝ) ^ σ :=
  (hF.comp Units.continuous_val).norm.mul
    (continuous_ideleModule_val.rpow_const fun _ ↦ Or.inr hσ)

theorem integrable_norm_mul_rpow {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) {σ : ℝ}
    (hσ : 1 < σ) :
    Integrable (fun x : IdeleGroup K ↦ ‖F x‖ * (ideleModule K x : ℝ) ^ σ) (ideleMeasure K) := by
  have hcont : ∀ {G : 𝔸[K] → ℂ}, G ∈ schwartzBruhat K →
      AEStronglyMeasurable (fun x : IdeleGroup K ↦ ‖G x‖ * (ideleModule K x : ℝ) ^ σ)
        (ideleMeasure K) := fun hG ↦
    (continuous_norm_mul_rpow (continuous_of_mem_schwartzBruhat hG) (by linarith)).aestronglyMeasurable
  have hpow : ∀ x : IdeleGroup K, 0 ≤ (ideleModule K x : ℝ) ^ σ := fun x ↦
    Real.rpow_nonneg (ideleModule K x).2.le σ
  have hmem := hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨C, k, L, hC, hk, hb⟩ := exists_bound_schwartzBruhatTensor φ hg σ
    refine Integrable.mono' ((integrable_zetaBound hσ hk L).const_mul C) (hcont hmem)
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hpow x))]
    exact hb x
  | zero =>
    simp only [Pi.zero_apply, norm_zero, zero_mul]
    exact integrable_zero _ _ _
  | add G H hGm hHm hG hH =>
    refine Integrable.mono' ((hG hGm).add (hH hHm)) (hcont hmem) (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hpow x))]
    show ‖G x + H x‖ * _ ≤ ‖G x‖ * _ + ‖H x‖ * _
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (hpow x)
  | smul c G hGm hG =>
    convert (hG hGm).const_mul ‖c‖ using 1
    funext x
    simp [mul_assoc]

def globalZeta (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  ∫ x, f x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s ∂ideleMeasure K

theorem continuous_zetaIntegrand {F : 𝔸[K] → ℂ} (hF : Continuous F) (χ : HeckeCharacter K)
    (s : ℂ) :
    Continuous fun x : IdeleGroup K ↦ F x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s :=
  ((hF.comp Units.continuous_val).mul (continuous_subtype_val.comp χ.continuous_toIdele)).mul
    ((Complex.continuous_ofReal.comp continuous_ideleModule_val).cpow continuous_const
      fun x ↦ Complex.ofReal_mem_slitPlane.2 (ideleModule K x).2)

theorem norm_zetaIntegrand (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (s : ℂ) (x : IdeleGroup K) :
    ‖F x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s‖ =
      ‖F x‖ * (ideleModule K x : ℝ) ^ s.re := by
  rw [norm_mul, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule K x).2]

theorem integrable_globalZetaIntegrand {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun x : IdeleGroup K ↦ F x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s)
      (ideleMeasure K) := by
  refine (integrable_norm_mul_rpow hF hs).mono'
    (continuous_zetaIntegrand (continuous_of_mem_schwartzBruhat hF) χ s).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  rw [norm_zetaIntegrand]

theorem rpow_mul_abs_log_le {t σ₀ δ σ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hσ : |σ - σ₀| < δ) :
    t ^ σ * |Real.log t| ≤ (t ^ (σ₀ - 2 * δ) + t ^ (σ₀ + 2 * δ)) / δ := by
  have hσ' := abs_lt.1 hσ
  rcases le_or_gt 1 t with h1 | h1
  · have hlog : |Real.log t| ≤ t ^ δ / δ := by
      rw [abs_of_nonneg (Real.log_nonneg h1)]
      exact Real.log_le_rpow_div ht.le hδ
    have hpow : t ^ σ ≤ t ^ (σ₀ + δ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    calc t ^ σ * |Real.log t| ≤ t ^ (σ₀ + δ) * (t ^ δ / δ) :=
          mul_le_mul hpow hlog (abs_nonneg _) (by positivity)
      _ = t ^ (σ₀ + 2 * δ) / δ := by
          rw [mul_div_assoc', ← Real.rpow_add ht]
          congr 2
          ring
      _ ≤ (t ^ (σ₀ - 2 * δ) + t ^ (σ₀ + 2 * δ)) / δ :=
          div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hδ.le
  · have hlog : |Real.log t| ≤ t ^ (-δ) / δ := by
      rw [abs_of_nonpos (Real.log_nonpos ht.le h1.le)]
      have := Real.log_le_rpow_div (inv_nonneg.2 ht.le) hδ
      rwa [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this
    have hpow : t ^ σ ≤ t ^ (σ₀ - δ) :=
      Real.rpow_le_rpow_of_exponent_ge ht h1.le (by linarith)
    calc t ^ σ * |Real.log t| ≤ t ^ (σ₀ - δ) * (t ^ (-δ) / δ) :=
          mul_le_mul hpow hlog (abs_nonneg _) (by positivity)
      _ = t ^ (σ₀ - 2 * δ) / δ := by
          rw [mul_div_assoc', ← Real.rpow_add ht]
          congr 2
          ring
      _ ≤ (t ^ (σ₀ - 2 * δ) + t ^ (σ₀ + 2 * δ)) / δ :=
          div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hδ.le

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.TateThesis.EulerFactorsInverse
open NumberField InfinitePlace InfinitePlace.Completion _root_.Complex
open scoped Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem eq_of_forall_exp_mul_I {a b : ℝ}
    (h : ∀ t : ℝ, Complex.exp (a * t * I) = Complex.exp (b * t * I)) : a = b := by
  by_contra hab
  have hne : a - b ≠ 0 := sub_ne_zero.2 hab
  set t : ℝ := π / (a - b)
  have ht : (a - b) * t = π := by simp only [t]; field_simp
  have h1 : Complex.exp ((((a - b) * t : ℝ) : ℂ) * I) = 1 := by
    have e : ((((a - b) * t : ℝ) : ℂ) * I) = (a : ℂ) * t * I - (b : ℂ) * t * I := by
      push_cast; ring
    rw [e, Complex.exp_sub, h t, div_self (Complex.exp_ne_zero _)]
  rw [ht, Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have h2 : (π : ℂ) = ((n * (2 * π) : ℝ) : ℂ) := by
    refine mul_right_cancel₀ I_ne_zero (hn.trans ?_)
    push_cast; ring
  have h3 : π = n * (2 * π) := by exact_mod_cast h2
  have h4 : (1 : ℝ) = 2 * n := by
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp at h3
    linarith
  have h5 : (1 : ℤ) = 2 * n := by exact_mod_cast h4
  omega


omit [NumberField K] in
theorem exists_extensionEmbedding_eq_ofReal (w : InfinitePlace K) (r : ℝ) :
    ∃ a : w.Completion, extensionEmbedding w a = r := by
  by_cases hw : w.IsReal
  · obtain ⟨a, ha⟩ := surjective_extensionEmbeddingOfIsReal hw r
    exact ⟨a, by rw [← extensionEmbeddingOfIsReal_apply hw, ha]⟩
  · exact surjective_extensionEmbedding_of_isComplex (not_isReal_iff_isComplex.1 hw) (r : ℂ)

omit [NumberField K] in
theorem norm_extensionEmbedding' (w : InfinitePlace K) (a : w.Completion) :
    ‖extensionEmbedding w a‖ = ‖a‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a

theorem ofReal_exp_cpow (t : ℝ) (c : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ c = Complex.exp (t * c) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← ofReal_log
    (Real.exp_pos t).le, Real.log_exp]

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem infiniteParams_unique (w : InfinitePlace K) {p : ℤ × ℝ}
    (hp1 : w.IsReal → 0 ≤ p.1 ∧ p.1 < 2)
    (hp2 : ∀ a : (w.Completion)ˣ, (χ.infiniteComponent w a : ℂ) =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((p.2 : ℂ) * I)) :
    p = χ.infiniteParams w := by
  set q := χ.infiniteParams w
  have hq1 : w.IsReal → 0 ≤ q.1 ∧ q.1 < 2 := (χ.exists_infiniteParams w).choose_spec.1
  have hq2 := (χ.exists_infiniteParams w).choose_spec.2
  have heq : ∀ a : (w.Completion)ˣ,
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ q.1 *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((q.2 : ℂ) * I) :=
    fun a ↦ (hp2 a).symm.trans (hq2 a)
  have hM : (1 : ℝ) ≤ w.mult := by exact_mod_cast InfinitePlace.one_le_mult

  have hτ : p.2 = q.2 := by
    have key : ∀ t : ℝ, Complex.exp ((w.mult * p.2 : ℝ) * t * I) =
        Complex.exp ((w.mult * q.2 : ℝ) * t * I) := by
      intro t
      obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal w (Real.exp t)
      have ha0 : a ≠ 0 := fun h0 ↦ by
        rw [h0, map_zero] at ha
        exact (Real.exp_pos t).ne' (by exact_mod_cast ha.symm)
      have hn : ‖a‖ = Real.exp t := by
        rw [← norm_extensionEmbedding', ha, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos t)]
      have h := heq (Units.mk0 a ha0)
      simp only [Units.val_mk0, ha, hn, div_self (by exact_mod_cast (Real.exp_pos t).ne' :
        ((Real.exp t : ℝ) : ℂ) ≠ 0), one_zpow, one_mul, ← Real.exp_nat_mul,
        ofReal_exp_cpow] at h
      convert h using 2 <;> push_cast <;> ring
    have := eq_of_forall_exp_mul_I key
    have hM0 : (w.mult : ℝ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hM0 this

  have hm : ∀ a : (w.Completion)ˣ,
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ q.1 := by
    intro a
    have h := heq a
    rw [hτ] at h
    have hpos : (0 : ℝ) < ‖(a : w.Completion)‖ ^ w.mult := pow_pos (norm_pos_iff.2 a.ne_zero) _
    have hne : ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((q.2 : ℂ) * I) ≠ 0 := by
      rw [cpow_def_of_ne_zero (by exact_mod_cast hpos.ne')]
      exact Complex.exp_ne_zero _
    exact mul_right_cancel₀ hne h
  refine Prod.ext ?_ hτ
  by_cases hw : w.IsReal
  · obtain ⟨hp0, hp2'⟩ := hp1 hw
    obtain ⟨hq0, hq2'⟩ := hq1 hw
    obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal w (-1)
    have ha0 : a ≠ 0 := fun h0 ↦ by rw [h0, map_zero] at ha; norm_num at ha
    have hn : ‖a‖ = 1 := by rw [← norm_extensionEmbedding', ha]; simp
    have h := hm (Units.mk0 a ha0)
    simp only [Units.val_mk0, ha, hn, ofReal_one, div_one, ofReal_neg] at h
    rcases (show p.1 = 0 ∨ p.1 = 1 by omega) with h1 | h1 <;>
      rcases (show q.1 = 0 ∨ q.1 = 1 by omega) with h2 | h2 <;> rw [h1, h2] at h ⊢ <;>
      norm_num at h
  · have hc := not_isReal_iff_isComplex.1 hw
    have key : ∀ θ : ℝ, Complex.exp ((p.1 : ℝ) * θ * I) = Complex.exp ((q.1 : ℝ) * θ * I) := by
      intro θ
      obtain ⟨a, ha⟩ := surjective_extensionEmbedding_of_isComplex hc (Complex.exp (θ * I))
      have ha0 : a ≠ 0 := fun h0 ↦ by
        rw [h0, map_zero] at ha
        exact Complex.exp_ne_zero _ ha.symm
      have hn : ‖a‖ = 1 := by
        rw [← norm_extensionEmbedding', ha, Complex.norm_exp_ofReal_mul_I]
      have h := hm (Units.mk0 a ha0)
      simp only [Units.val_mk0, ha, hn, ofReal_one, div_one, ← Complex.exp_int_mul] at h
      convert h using 2 <;> push_cast <;> ring
    exact_mod_cast eq_of_forall_exp_mul_I key

theorem inv_toIdele (x : IdeleGroup K) : (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ := rfl

theorem localComponent_inv (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : (χ⁻¹).localComponent v a = (χ.localComponent v a)⁻¹ := rfl

theorem infiniteComponent_inv (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    (χ⁻¹).infiniteComponent w a = (χ.infiniteComponent w a)⁻¹ := rfl

theorem conductor_inv : χ⁻¹.conductor = χ.conductor := by
  have hker : (χ⁻¹).toIdele.ker = χ.toIdele.ker := by
    ext x
    simp only [MonoidHom.mem_ker, inv_toIdele, inv_eq_one]
  have h1 : χ⁻¹.conductor ∣ χ.conductor := by
    rw [← (χ⁻¹).map_idealLevel_le_ker_iff χ.conductor_ne_bot, hker]
    exact χ.map_idealLevel_conductor_le_ker
  have h2 : χ.conductor ∣ χ⁻¹.conductor := by
    rw [← χ.map_idealLevel_le_ker_iff (χ⁻¹).conductor_ne_bot, ← hker]
    exact (χ⁻¹).map_idealLevel_conductor_le_ker
  exact le_antisymm (Ideal.le_of_dvd h2) (Ideal.le_of_dvd h1)


open Classical in
theorem infiniteParams_inv (w : InfinitePlace K) :
    (χ⁻¹).infiniteParams w =
      (if w.IsReal then χ.infiniteWeight w else -χ.infiniteWeight w, -χ.infiniteTau w) := by
  symm
  refine (χ⁻¹).infiniteParams_unique w ?_ fun a ↦ ?_
  · intro hw
    rw [if_pos hw]
    exact χ.infiniteWeight_of_isReal hw
  · rw [infiniteComponent_inv, Circle.coe_inv, χ.infiniteComponent_eq]
    simp only
    rw [mul_inv, ofReal_neg, neg_mul, cpow_neg]
    congr 1
    split_ifs with hw
    ·
      have hι : extensionEmbedding w (a : w.Completion) =
          ((extensionEmbeddingOfIsReal hw (a : w.Completion) : ℝ) : ℂ) :=
        (extensionEmbeddingOfIsReal_apply hw _).symm
      have hn : ‖(a : w.Completion)‖ = |extensionEmbeddingOfIsReal hw (a : w.Completion)| := by
        rw [← Real.norm_eq_abs]
        exact ((isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm
      have hx0 : extensionEmbeddingOfIsReal hw (a : w.Completion) ≠ 0 :=
        (map_ne_zero_iff _ (extensionEmbeddingOfIsReal hw).injective).2 a.ne_zero
      rw [hι, hn, ofReal_div_abs_eq_sign hx0, ← zpow_neg, ← inv_zpow']
      congr 1
      rcases lt_or_gt_of_ne hx0 with h | h
      · rw [Real.sign_of_neg h]; push_cast; norm_num
      · rw [Real.sign_of_pos h]; push_cast; norm_num
    · rw [zpow_neg]

theorem infiniteWeight_inv_of_isReal {w : InfinitePlace K} (hw : w.IsReal) :
    (χ⁻¹).infiniteWeight w = χ.infiniteWeight w := by
  rw [infiniteWeight, infiniteParams_inv, if_pos hw]

theorem infiniteWeight_inv_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) :
    (χ⁻¹).infiniteWeight w = -χ.infiniteWeight w := by
  rw [infiniteWeight, infiniteParams_inv, if_neg (not_isReal_iff_isComplex.2 hw)]

end HeckeCharacter

end

end GroundTheory.Global
end
