module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVB
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVM
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex Module

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem emb_indep (g : (E →+* ℂ) → ℂ) (h : ∀ β : 𝓞 E, ∑ σ, σ (β : E) * g σ = 0) : g = 0 := by
  have hb : ∀ i, ∑ σ : E →+* ℂ, σ (integralBasis E i) * g σ = 0 := fun i => by
    rw [integralBasis_apply]
    exact h _
  have hE : ∀ x : E, ∑ σ : E →+* ℂ, σ x * g σ = 0 := by
    intro x
    rw [← (integralBasis E).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have e : ∀ σ : E →+* ℂ, σ ((integralBasis E).repr x i • integralBasis E i) * g σ =
        ((integralBasis E).repr x i : ℂ) * (σ (integralBasis E i) * g σ) := fun σ => by
      rw [map_rat_smul, Rat.smul_def, mul_assoc]
    rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, hb i, mul_zero]
  have hli : LinearIndependent ℂ (fun σ : E →+* ℂ => ((σ : E →* ℂ) : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun σ : E →+* ℂ => (σ : E →* ℂ))
      (fun a b hab => RingHom.ext fun x => DFunLike.congr_fun hab x)
  rw [Fintype.linearIndependent_iff] at hli
  funext σ
  refine hli g ?_ σ
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← hE x]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [mul_comm]

def ConjSymm (t : (E →+* ℂ) → ℂ) : Prop :=
  ∀ σ, t (ComplexEmbedding.conjugate σ) = (starRingEnd ℂ) (t σ)

theorem conjSymm_canonical (x : E) : ConjSymm (canonicalEmbedding E x) := fun σ => by
  simp only [canonicalEmbedding.apply_at, ComplexEmbedding.conjugate_coe_eq]

theorem conjSymm_sum {ι : Type} (s : Finset ι) (c : ι → ℝ) (v : ι → (E →+* ℂ) → ℂ)
    (hv : ∀ i, ConjSymm (v i)) : ConjSymm (∑ i ∈ s, c i • v i) := fun σ => by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, hv i σ, Complex.real_smul, Complex.real_smul, map_mul,
    Complex.conj_ofReal]

theorem eq_of_commMap (t t' : (E →+* ℂ) → ℂ) (ht : ConjSymm t) (ht' : ConjSymm t')
    (h : mixedEmbedding.commMap E t = mixedEmbedding.commMap E t') : t = t' := by
  funext σ
  obtain ⟨w, hwdef⟩ : ∃ w, w = InfinitePlace.mk σ := ⟨_, rfl⟩
  have hcases := InfinitePlace.embedding_mk_eq σ
  rw [← hwdef] at hcases
  have key : t w.embedding = t' w.embedding := by
    by_cases hw : w.IsReal
    · have h1 := congrArg (fun m => m.1 ⟨w, hw⟩) h
      simp only [mixedEmbedding.commMap_apply_of_isReal] at h1
      have hr : ComplexEmbedding.conjugate w.embedding = w.embedding :=
        ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
      have a1 : starRingEnd ℂ (t w.embedding) = t w.embedding := by rw [← ht, hr]
      have a2 : starRingEnd ℂ (t' w.embedding) = t' w.embedding := by rw [← ht', hr]
      apply Complex.ext h1
      rw [Complex.conj_eq_iff_im.mp a1, Complex.conj_eq_iff_im.mp a2]
    · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have h1 := congrArg (fun m => m.2 ⟨w, hw'⟩) h
      simpa only [mixedEmbedding.commMap_apply_of_isComplex] using h1
  rcases hcases with he | he
  · rw [he] at key
    exact key
  · rw [he, ht, ht'] at key
    simpa using congrArg (starRingEnd ℂ) key

theorem real_span (t : (E →+* ℂ) → ℂ) (ht : ConjSymm t) :
    ∃ c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ,
      t = ∑ k, c k • canonicalEmbedding E (integralBasis E k) := by
  refine ⟨fun k => (mixedEmbedding.latticeBasis E).repr (mixedEmbedding.commMap E t) k, ?_⟩
  apply eq_of_commMap t _ ht (conjSymm_sum Finset.univ
    (fun k => (mixedEmbedding.latticeBasis E).repr (mixedEmbedding.commMap E t) k)
    (fun k => canonicalEmbedding E (integralBasis E k)) fun k => conjSymm_canonical _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul]
  conv_lhs => rw [← (mixedEmbedding.latticeBasis E).sum_repr (mixedEmbedding.commMap E t)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mixedEmbedding.latticeBasis_apply, mixedEmbedding.commMap_canonical_eq_mixed]

theorem conjugate_ne [_root_.NumberField.IsTotallyComplex E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hr : ComplexEmbedding.IsReal σ := ComplexEmbedding.isReal_iff.mpr h
  exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk σ))
    ⟨σ, hr, rfl⟩

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVA
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Module
open scoped nonZeroDivisors

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem exists_dual (φ : 𝓞 E →+ ℤ) :
    ∃ y : E, ∀ β : 𝓞 E, Algebra.trace ℚ E ((β : E) * y) = φ β := by
  classical
  let bZ := NumberField.RingOfIntegers.basis E
  let bQ := NumberField.integralBasis E
  have hnd : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  let dB := (Algebra.traceForm ℚ E).dualBasis hnd bQ
  refine ⟨∑ i, (φ (bZ i) : ℚ) • dB i, fun β => ?_⟩
  let f₁ : 𝓞 E →ₗ[ℤ] ℚ :=
    ((Algebra.trace ℚ E).restrictScalars ℤ).comp
      ((LinearMap.mulRight ℚ (∑ i, (φ (bZ i) : ℚ) • dB i)).restrictScalars ℤ ∘ₗ
        (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)
  let f₂ : 𝓞 E →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap ∘ₗ φ.toIntLinearMap
  have hf : f₁ = f₂ := by
    refine bZ.ext fun j => ?_
    simp only [f₁, f₂, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.mulRight_apply, Algebra.linearMap_apply, AddMonoidHom.coe_toIntLinearMap,
      Int.coe_castAddHom]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    have hb : (algebraMap (𝓞 E) E) (bZ j) = bQ j := (NumberField.integralBasis_apply E j).symm
    rw [hb]
    simp_rw [mul_smul_comm, map_smul]
    have h : ∀ i, Algebra.trace ℚ E (bQ j * dB i) = if j = i then 1 else 0 := fun i => by
      rw [mul_comm, ← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left hnd bQ i j
    simp [h]
  have := congrArg (fun g => g β) hf
  simpa [f₁, f₂] using this

abbrev Dual1 (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)

theorem mem_dual_of (y : E) (hy : ∀ β : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E ((β : E) * y) = k) :
    y ∈ Dual1 E := by
  rw [FractionalIdeal.mem_dual (I := (1 : FractionalIdeal (𝓞 E)⁰ E)) one_ne_zero]
  intro a ha
  obtain ⟨β, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
  obtain ⟨k, hk⟩ := hy β
  refine ⟨k, ?_⟩
  rw [Algebra.traceForm_apply, mul_comm, hk]
  simp

theorem one_le_norm_mul (l : E) (hl : l ≠ 0) (hmem : l ∈ Dual1 E * Dual1 E) :
    (1 : ℚ) ≤ |Algebra.norm ℚ l| * ((NumberField.discr E).natAbs : ℚ) ^ 2 := by
  classical
  have hD0 : Dual1 E ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  set dI : FractionalIdeal (𝓞 E)⁰ E :=
    ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) with hdI
  have hdD : dI * Dual1 E = 1 := by
    rw [hdI, coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]
    exact inv_mul_cancel₀ hD0
  have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ l ≤ Dual1 E * Dual1 E :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
  have hJ : dI * dI * FractionalIdeal.spanSingleton (𝓞 E)⁰ l ≤ 1 := by
    calc _ ≤ dI * dI * (Dual1 E * Dual1 E) := by first | exact mul_le_mul' le_rfl hle | gcongr
      _ = (dI * Dual1 E) * (dI * Dual1 E) := by ring
      _ = 1 := by rw [hdD, one_mul]
  obtain ⟨J, hJe⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hn := congrArg FractionalIdeal.absNorm hJe
  rw [map_mul, map_mul, FractionalIdeal.absNorm_span_singleton, hdI, FractionalIdeal.coeIdeal_absNorm (K := E),
    FractionalIdeal.coeIdeal_absNorm (K := E), NumberField.absNorm_differentIdeal (K := E) (𝒪 := 𝓞 E)] at hn
  have hN0 : Algebra.norm ℚ l ≠ 0 := Algebra.norm_ne_zero_iff.mpr hl
  have hd0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have hpos : ((NumberField.discr E).natAbs : ℚ) * (NumberField.discr E).natAbs
      * |Algebra.norm ℚ l| ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hd0) (by exact_mod_cast hd0)) (abs_ne_zero.mpr hN0)
  have hJ1 : 1 ≤ Ideal.absNorm J := by
    rcases Nat.eq_zero_or_pos (Ideal.absNorm J) with h0 | h0
    · exfalso; rw [h0, Nat.cast_zero] at hn; exact hpos hn.symm
    · exact h0
  have h1 : (1 : ℚ) ≤ Ideal.absNorm J := by exact_mod_cast hJ1
  rw [hn] at h1
  calc (1 : ℚ) ≤ _ := h1
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex Module

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section Emb

theorem trace_sum_emb (z : E) : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ z := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := z)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

theorem norm_prod_emb (z : E) : ((Algebra.norm ℚ z : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ z := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ z
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

end Emb

section Coord
variable {dim : (E →+* ℂ) → ℕ}

def pN (ξ : Vsp dim) (σ : E →+* ℂ) : ℝ := ∑ a : Fin (dim σ), ‖ξ ⟨σ, a⟩‖ ^ 2

def nS (ξ : Vsp dim) (σ : E →+* ℂ) : ℝ := pN ξ σ + pN ξ (ComplexEmbedding.conjugate σ)

theorem pN_nonneg (ξ : Vsp dim) (σ : E →+* ℂ) : 0 ≤ pN ξ σ :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem nS_conj (ξ : Vsp dim) (σ : E →+* ℂ) : nS ξ (ComplexEmbedding.conjugate σ) = nS ξ σ := by
  rw [nS, nS, ComplexEmbedding.involutive_conjugate (K := E) σ, add_comm]

theorem norm_sq_sum_pN (ξ : Vsp dim) : ‖ξ‖ ^ 2 = ∑ σ, pN ξ σ := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  rfl

theorem nS_le [_root_.NumberField.IsTotallyComplex E] (ξ : Vsp dim) (σ : E →+* ℂ) : nS ξ σ ≤ ‖ξ‖ ^ 2 := by
  classical
  rw [norm_sq_sum_pN, nS]
  have hne : ComplexEmbedding.conjugate σ ≠ σ := conjugate_ne σ
  rw [← Finset.sum_pair hne.symm]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun τ _ _ => pN_nonneg ξ τ)

def hA (x ξ : Vsp dim) (σ : E →+* ℂ) : ℂ := ∑ a : Fin (dim σ), x ⟨σ, a⟩ * (starRingEnd ℂ) (ξ ⟨σ, a⟩)

theorem im_Hf_act (x ξ : Vsp dim) (β : 𝓞 E) :
    ((Hf x (act β ξ)).im : ℂ) =
      ∑ σ, σ (β : E) * ((hA x ξ (ComplexEmbedding.conjugate σ) - (starRingEnd ℂ) (hA x ξ σ)) / (2 * I)) := by
  have hZ : Hf x (act β ξ) = ∑ σ, (starRingEnd ℂ) (σ (β : E)) * hA x ξ σ := by
    simp only [Hf, act, hA, Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [PiLp.toLp_apply, map_mul]
    ring
  have hre : ∑ σ, σ (β : E) * hA x ξ (ComplexEmbedding.conjugate σ) =
      ∑ σ, (starRingEnd ℂ) (σ (β : E)) * hA x ξ σ := by
    refine Fintype.sum_equiv (ComplexEmbedding.involutive_conjugate (K := E)).toPerm _ _ (fun σ => ?_)
    simp only [Function.Involutive.coe_toPerm, ComplexEmbedding.involutive_conjugate (K := E) σ,
      ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hZ, Complex.im_eq_sub_conj, map_sum]
  simp only [map_mul, Complex.conj_conj, mul_sub, mul_div_assoc', Finset.sum_div, Finset.sum_sub_distrib]
  rw [← hre]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_div]

theorem emb_dual (x ξ : Vsp dim) (y : E)
    (hy : ∀ β : 𝓞 E, ((Algebra.trace ℚ E ((β : E) * y) : ℚ) : ℝ) = (Hf x (act β ξ)).im) (σ : E →+* ℂ) :
    σ y = (hA x ξ (ComplexEmbedding.conjugate σ) - (starRingEnd ℂ) (hA x ξ σ)) / (2 * I) := by
  have h := emb_indep (fun σ => σ y -
      (hA x ξ (ComplexEmbedding.conjugate σ) - (starRingEnd ℂ) (hA x ξ σ)) / (2 * I)) (fun β => by
    have h1 := congrArg (fun r : ℝ => (r : ℂ)) (hy β)
    simp only [Complex.ofReal_ratCast] at h1
    rw [trace_sum_emb, im_Hf_act] at h1
    simp only [map_mul] at h1
    simp only [mul_sub, Finset.sum_sub_distrib, h1, sub_self])
  have := congrFun h σ
  simpa [sub_eq_zero] using this

theorem emb_dual_zero (x ξ : Vsp dim) (y : E)
    (hy : ∀ β : 𝓞 E, ((Algebra.trace ℚ E ((β : E) * y) : ℚ) : ℝ) = (Hf x (act β ξ)).im) (σ : E →+* ℂ)
    (hn : nS ξ σ = 0) : σ y = 0 := by
  have h1 : pN ξ σ = 0 := by
    have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); rw [nS] at hn; linarith
  have h2 : pN ξ (ComplexEmbedding.conjugate σ) = 0 := by
    have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); rw [nS] at hn; linarith
  have hz : ∀ τ, pN ξ τ = 0 → hA x ξ τ = 0 := by
    intro τ hτ
    have : ∀ a, ξ ⟨τ, a⟩ = 0 := by
      intro a
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 hτ a (Finset.mem_univ a)
      simpa using h
    simp [hA, this]
  rw [emb_dual x ξ y hy σ, hz _ h2, hz _ h1]
  simp

def actT (t : (E →+* ℂ) → ℂ) (v : Vsp dim) : Vsp dim := WithLp.toLp 2 fun i => t i.1 * v i

theorem act_eq_actT (β : 𝓞 E) (v : Vsp dim) : act β v = actT (canonicalEmbedding E (β : E)) v := rfl

theorem actT_sum {ι : Type} (s : Finset ι) (c : ι → ℝ) (t : ι → (E →+* ℂ) → ℂ) (v : Vsp dim) :
    actT (∑ k ∈ s, c k • t k) v = ∑ k ∈ s, c k • actT (t k) v := by
  ext i
  simp [actT, Finset.sum_mul, Complex.real_smul, mul_assoc]

theorem norm_actT_sq (t : (E →+* ℂ) → ℂ) (v : Vsp dim) :
    ‖actT t v‖ ^ 2 = ∑ σ, ‖t σ‖ ^ 2 * pN v σ := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [pN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [actT, norm_mul, mul_pow]

end Coord

section CS
variable {dim : (E →+* ℂ) → ℕ}

theorem cs_bound [IsCMField E] (I : Submodule ℤ (Vsp dim))
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) {ξ : Vsp dim} (hξ : ξ ∈ I) (x u : Vsp dim)
    (hu : IsU I x u) (y : E)
    (hy : ∀ β : 𝓞 E, ((Algebra.trace ℚ E ((β : E) * y) : ℚ) : ℝ) = (Hf x (act β ξ)).im) :
    2 * ∑ σ : E →+* ℂ, ‖σ y‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖u‖ ^ 2 := by
  classical
  set t : (E →+* ℂ) → ℂ := fun σ =>
    if nS ξ σ = 0 then 0 else (starRingEnd ℂ) (σ y) / (nS ξ σ : ℂ) with htdef
  have ht : ConjSymm t := by
    intro σ
    simp only [htdef, nS_conj, ComplexEmbedding.conjugate_coe_eq]
    split_ifs
    · simp
    · rw [map_div₀, Complex.conj_ofReal]
  obtain ⟨c, hc⟩ := real_span t ht
  set β : Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E := fun k => RingOfIntegers.basis E k
  have hβ : ∀ k, canonicalEmbedding E (integralBasis E k) = canonicalEmbedding E ((β k : 𝓞 E) : E) :=
    fun k => by rw [integralBasis_apply]
  set b := actT t ξ with hbdef
  have hb : b = ∑ k, c k • act (β k) ξ := by
    rw [hbdef, hc, actT_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hβ, ← act_eq_actT]
  have hactI : ∀ k, act (β k) ξ ∈ IR I := fun k => Submodule.subset_span (hst _ _ hξ)
  set S : ℝ := ∑ σ, if nS ξ σ = 0 then 0 else ‖σ y‖ ^ 2 / nS ξ σ with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun σ _ => by
    split_ifs with h
    · exact le_refl _
    · exact div_nonneg (by positivity) (by
        have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); rw [nS]; linarith)
  have hub : inner ℝ u b = S := by
    have e1 : inner ℝ u b = ∑ k, c k * ((Algebra.trace ℚ E ((β k : E) * y) : ℚ) : ℝ) := by
      rw [hb, inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_right, hu.2 _ (hactI k), hy]
    rw [e1]
    apply Complex.ofReal_injective
    push_cast
    simp only [trace_sum_emb, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm, hSdef]
    push_cast
    refine Finset.sum_congr rfl fun σ _ => ?_
    have htσ : t σ = ∑ k, (c k : ℂ) * σ ((β k : 𝓞 E) : E) := by
      have := congrFun hc σ
      rw [Finset.sum_apply] at this
      rw [this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, hβ, canonicalEmbedding.apply_at, Complex.real_smul]
    have e2 : ∑ k, (c k : ℂ) * (σ ((β k : 𝓞 E) : E) * σ y) = t σ * σ y := by
      rw [htσ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e2, htdef]
    simp only
    split_ifs with h
    · simp
    · rw [div_mul_eq_mul_div, Complex.conj_mul', Complex.ofReal_div]
      push_cast
      ring
  have hbb : ‖b‖ ^ 2 = S / 2 := by
    rw [hbdef, norm_actT_sq]
    have hF : ∀ σ, ‖t σ‖ ^ 2 = if nS ξ σ = 0 then 0 else ‖σ y‖ ^ 2 / nS ξ σ ^ 2 := by
      intro σ
      simp only [htdef]
      split_ifs with h
      · simp
      · rw [norm_div, Complex.norm_conj, div_pow]
        congr 1
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hsym : ∑ σ, ‖t σ‖ ^ 2 * pN ξ σ = ∑ σ, ‖t σ‖ ^ 2 * pN ξ (ComplexEmbedding.conjugate σ) := by
      refine Fintype.sum_equiv (ComplexEmbedding.involutive_conjugate (K := E)).toPerm _ _ (fun σ => ?_)
      simp only [Function.Involutive.coe_toPerm, ComplexEmbedding.involutive_conjugate (K := E) σ]
      rw [hF, hF, nS_conj, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
    have h2 : 2 * ∑ σ, ‖t σ‖ ^ 2 * pN ξ σ = S := by
      rw [two_mul]
      nth_rewrite 2 [hsym]
      rw [← Finset.sum_add_distrib, hSdef]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [← mul_add, hF]
      split_ifs with h
      · simp
      · rw [show pN ξ σ + pN ξ (ComplexEmbedding.conjugate σ) = nS ξ σ from rfl]
        field_simp
    linarith
  have hS2 : 2 * S ≤ ‖u‖ ^ 2 := by
    have hcs : S ≤ ‖u‖ * ‖b‖ := hub ▸ real_inner_le_norm u b
    rcases hS0.lt_or_eq with hpos | hzero
    · have h3 : S ^ 2 ≤ ‖u‖ ^ 2 * ‖b‖ ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hS0 hcs 2
      rw [hbb] at h3
      nlinarith
    · rw [← hzero]
      have := sq_nonneg ‖u‖
      linarith
  by_cases hξ0 : ‖ξ‖ = 0
  · have hz : ∀ σ : E →+* ℂ, σ y = 0 := by
      intro σ
      apply emb_dual_zero x ξ y hy σ
      have h1 := nS_le ξ σ
      rw [hξ0] at h1
      have h2 : 0 ≤ nS ξ σ := by
        have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); unfold nS; linarith
      have h3 : nS ξ σ ≤ 0 := by simpa using h1
      exact le_antisymm h3 h2
    simp [hz]
    positivity
  · have hpos : 0 < ‖ξ‖ ^ 2 := by positivity
    have hlow : ∑ σ : E →+* ℂ, ‖σ y‖ ^ 2 / ‖ξ‖ ^ 2 ≤ S := by
      rw [hSdef]
      refine Finset.sum_le_sum fun σ _ => ?_
      split_ifs with h
      · rw [emb_dual_zero x ξ y hy σ h]
        simp
      · have hn : 0 < nS ξ σ := lt_of_le_of_ne (by
          have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); rw [nS]; linarith)
          (Ne.symm h)
        exact div_le_div_of_nonneg_left (by positivity) hn (nS_le ξ σ)
    rw [← Finset.sum_div] at hlow
    have := (div_le_iff₀ hpos).1 hlow
    nlinarith

end CS

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVC
namespace ReciprocityTheory.ChartRestriction.G.I2

theorem amgm_sum_ge {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ℝ) (hP : 0 ≤ P) (hprod : P ≤ ∏ i, a i) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) * P ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, a i := by
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) a (fun _ _ => zero_le_one)
    (by simpa using hn') (fun i _ => ha i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [le_div_iff₀ hn'] at h
  have h2 : P ^ ((Fintype.card ι : ℝ)⁻¹) ≤ (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
    Real.rpow_le_rpow hP hprod (by positivity)
  calc (Fintype.card ι : ℝ) * P ^ ((Fintype.card ι : ℝ)⁻¹)
      ≤ (Fintype.card ι : ℝ) * (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left h2 hn'.le
    _ = (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) * Fintype.card ι := mul_comm _ _
    _ ≤ ∑ i, a i := h

theorem inv_sq_rpow_inv (D : ℝ) (hD : 0 < D) (n : ℝ) :
    ((D ^ 2)⁻¹) ^ n⁻¹ = ((D ^ n⁻¹) ^ 2)⁻¹ := by
  rw [Real.inv_rpow (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (D ^ n⁻¹), ← Real.rpow_mul hD.le,
    ← Real.rpow_mul hD.le, mul_comm]

theorem sum_ge_of_prod_ge {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (D : ℝ) (hD : 0 < D) (hprod : (D ^ 2)⁻¹ ≤ ∏ i, a i) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) / (D ^ ((Fintype.card ι : ℝ)⁻¹)) ^ 2 ≤ ∑ i, a i := by
  have h := amgm_sum_ge a ha _ (by positivity) hprod hn
  rwa [inv_sq_rpow_inv D hD, ← div_eq_mul_inv] at h

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section SlopeTestRemainingChoices
variable {dim : (E →+* ℂ) → ℕ}

theorem smul_add_scalar (β β' : 𝓞 E) (v : Vsp dim) : act (β + β') v = act β v + act β' v := by
  ext i
  simp [act, add_mul]

theorem Hf_add_rightSquareIntegrability (x w w' : Vsp dim) : Hf x (w + w') = Hf x w + Hf x w' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left_conj [IsCMField E] (α : 𝓞 E) (v w : Vsp dim) :
    Hf (act α v) w = Hf v (act (IsCMField.ringOfIntegersComplexConj E α) w) := by
  simp only [Hf, act, PiLp.toLp_apply, IsCMField.coe_ringOfIntegersComplexConj,
    IsCMField.complexEmbedding_complexConj, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring

end SlopeTestRemainingChoices

theorem sum_sq_norm_ge_of_span [IsCMField E] (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) {ξ : Vsp X.dim} (hξ : ξ ∈ I) (hξ0 : ξ ≠ 0)
    (k : ℕ) (x u : Fin k → Vsp X.dim) (hxu : ∀ j, x j ∈ X.L ∧ IsU I (x j) (u j))
    (hspan : Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (x j)) w} = IR I) :
    2 * PT.f E / (PT.rd E ^ 2 * ‖ξ‖ ^ 2) ≤ ∑ j, ‖u j‖ ^ 2 / 2 := by
  classical

  have hint : ∀ j (β : 𝓞 E), ∃ n : ℤ, (Hf (x j) (act β ξ)).im = n := fun j β =>
    X.integral _ _ (hxu j).1 (hle (hst β ξ hξ))
  let φ : Fin k → 𝓞 E →+ ℤ := fun j => AddMonoidHom.mk' (fun β => (hint j β).choose) (by
    intro β β'
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← (hint j (β + β')).choose_spec, ← (hint j β).choose_spec, ← (hint j β').choose_spec,
      smul_add_scalar, Hf_add_rightSquareIntegrability, Complex.add_im])
  have hφ : ∀ j β, ((φ j β : ℤ) : ℝ) = (Hf (x j) (act β ξ)).im := fun j β =>
    ((hint j β).choose_spec).symm

  choose y hy using fun j => exists_dual (φ j)
  have hyR : ∀ j (β : 𝓞 E), ((Algebra.trace ℚ E ((β : E) * y j) : ℚ) : ℝ) = (Hf (x j) (act β ξ)).im := by
    intro j β
    rw [hy j β, ← hφ j β]
    push_cast
    rfl
  have hcs : ∀ j, 2 * ∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖u j‖ ^ 2 := fun j =>
    cs_bound I hst hξ (x j) (u j) (hxu j).2 (y j) (hyR j)

  set l : E := ∑ j, y j * IsCMField.complexConj E (y j) with hldef
  set a : (E →+* ℂ) → ℝ := fun σ => ∑ j, ‖σ (y j)‖ ^ 2 with hadef
  have ha0 : ∀ σ, 0 ≤ a σ := fun σ => Finset.sum_nonneg fun _ _ => by positivity
  have hσl : ∀ σ : E →+* ℂ, σ l = (a σ : ℂ) := by
    intro σ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hldef, hadef, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_conj']

  have hl : l ≠ 0 := by
    intro hl0
    obtain ⟨σ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : a σ₀ = 0 := by
      have := hσl σ₀
      rw [hl0, map_zero] at this
      exact_mod_cast this.symm
    have hy0 : ∀ j, y j = 0 := by
      intro j
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 j
        (Finset.mem_univ j)
      have h3 : σ₀ (y j) = 0 := by simpa using h2
      exact (map_eq_zero_iff σ₀ σ₀.injective).1 h3
    have horth : ∀ w ∈ IR I, inner ℝ w ξ = 0 := by
      intro w hw
      rw [← hspan] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨j, α, hU⟩ := hw
        rw [hU.2 ξ (Submodule.subset_span hξ), herm_smul_left_conj, ← hyR, hy0 j, mul_zero, map_zero]
        simp
      | zero => simp
      | add w w' _ _ h h' => rw [inner_add_left, h, h', add_zero]
      | smul r w _ h => rw [real_inner_smul_left, h, mul_zero]
    have h4 := horth ξ (Submodule.subset_span hξ)
    rw [real_inner_self_eq_norm_sq] at h4
    have h5 : ‖ξ‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 h4
    exact hξ0 (norm_eq_zero.1 h5)

  have hmemD : ∀ j, y j ∈ Dual1 E := fun j => mem_dual_of (y j) fun β => ⟨φ j β, hy j β⟩
  have htr : ∀ z : E, Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  have hmemD' : ∀ j, IsCMField.complexConj E (y j) ∈ Dual1 E := fun j =>
    mem_dual_of _ fun β => by
      refine ⟨φ j (IsCMField.ringOfIntegersComplexConj E β), ?_⟩
      rw [← hy j, IsCMField.coe_ringOfIntegersComplexConj, ← htr, map_mul,
        IsCMField.complexConj_apply_apply]
  have hmem : l ∈ Dual1 E * Dual1 E := by
    rw [hldef, ← FractionalIdeal.mem_coe]
    exact Submodule.sum_mem _ fun j _ =>
      (FractionalIdeal.mem_coe).2 (FractionalIdeal.mul_mem_mul (hmemD j) (hmemD' j))
  have hnorm := one_le_norm_mul l hl hmem

  have hprodC : ((Algebra.norm ℚ l : ℚ) : ℂ) = ((∏ σ, a σ : ℝ) : ℂ) := by
    rw [norm_prod_emb]
    push_cast
    exact Finset.prod_congr rfl fun σ _ => hσl σ
  have hprodR : ((Algebra.norm ℚ l : ℚ) : ℝ) = ∏ σ, a σ := by exact_mod_cast hprodC
  have hP0 : 0 ≤ ∏ σ, a σ := Finset.prod_nonneg fun σ _ => ha0 σ
  set D : ℝ := ((NumberField.discr E).natAbs : ℝ) with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    exact_mod_cast Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  have hprod : (D ^ 2)⁻¹ ≤ ∏ σ, a σ := by
    have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ l : ℚ) : ℝ)| * D ^ 2 := by
      have h1' := (Rat.cast_le (K := ℝ)).2 hnorm
      push_cast at h1'
      rw [hDdef]
      exact h1'
    rw [hprodR, abs_of_nonneg hP0] at h1
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    linarith
  have hcard : Fintype.card (E →+* ℂ) = 2 * PT.f E := by
    rw [NumberField.Embeddings.card, PT.f, IsTotallyComplex.finrank]
    omega
  have hcpos : 0 < Fintype.card (E →+* ℂ) := Fintype.card_pos
  have hsum := sum_ge_of_prod_ge a ha0 D hD hprod hcpos
  have hrd : D ^ ((Fintype.card (E →+* ℂ) : ℝ)⁻¹) = PT.rd E := by
    rw [PT.rd, NumberField.Embeddings.card, one_div, hDdef]
    congr 1
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hrd, hcard] at hsum
  push_cast at hsum

  have hξpos : 0 < ‖ξ‖ ^ 2 := by
    have := norm_pos_iff.2 hξ0
    positivity
  have hj : ∀ j, (∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2) / ‖ξ‖ ^ 2 ≤ ‖u j‖ ^ 2 / 2 := by
    intro j
    rw [div_le_iff₀ hξpos]
    linarith [hcs j]
  have hsw : ∑ σ, a σ = ∑ j, ∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2 := by
    rw [hadef]
    exact Finset.sum_comm
  calc 2 * PT.f E / (PT.rd E ^ 2 * ‖ξ‖ ^ 2) = (2 * PT.f E / PT.rd E ^ 2) / ‖ξ‖ ^ 2 := by
        rw [div_div]
    _ ≤ (∑ σ, a σ) / ‖ξ‖ ^ 2 := by
        apply div_le_div_of_nonneg_right hsum hξpos.le
    _ = ∑ j, (∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2) / ‖ξ‖ ^ 2 := by
        rw [hsw, Finset.sum_div]
    _ ≤ ∑ j, ‖u j‖ ^ 2 / 2 := Finset.sum_le_sum fun j _ => hj j

end

end ReciprocityTheory.ChartRestriction.G.I2
