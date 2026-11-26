module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hadamard
namespace ReciprocityTheory.ChartRestriction.G.T0

open scoped BigOperators ComplexOrder
open Finset Matrix

theorem psd_det_re_le_one_of_diag (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosSemidef)
    (hd : ∀ c, H c c = 1) : H.det.re ≤ 1 := by
  have hHerm := hH.isHermitian
  have htr : ∑ i, hHerm.eigenvalues i = N := by
    have h := hHerm.trace_eq_sum_eigenvalues
    have h2 : H.trace = N := by simp [Matrix.trace, hd]
    rw [h2] at h
    have h4 := congrArg (RCLike.re : ℂ → ℝ) h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, RCLike.ofReal_re, RCLike.natCast_re] at h4
    linarith
  have hre : H.det.re = ∏ i, hHerm.eigenvalues i := by
    rw [hHerm.det_eq_prod_eigenvalues]
    norm_cast
  rw [hre]
  calc ∏ i, hHerm.eigenvalues i ≤ ∏ i, Real.exp (hHerm.eigenvalues i - 1) :=
        Finset.prod_le_prod₀ (fun i _ => hH.eigenvalues_nonneg i)
          (fun i _ => by linarith [Real.add_one_le_exp (hHerm.eigenvalues i - 1)])
    _ = Real.exp (∑ i, (hHerm.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
    _ = 1 := by simp [Finset.sum_sub_distrib, htr]

theorem psd_det_re_le_prod_diag (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosSemidef) :
    G.det.re ≤ ∏ c, (G c c).re := by
  classical
  have hdiag : ∀ c, G c c = ((G c c).re : ℂ) := fun c =>
    (Complex.conj_eq_iff_re.mp (by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hG.1 c) c)).symm
  have hnn : ∀ c, 0 ≤ (G c c).re := fun c => (Complex.nonneg_iff.mp (hG.diag_nonneg (i := c))).1
  by_cases hz : ∃ c, (G c c).re = 0
  · obtain ⟨c, hc⟩ := hz
    have hcol : G *ᵥ Pi.single c 1 = 0 := by
      rw [← hG.dotProduct_mulVec_zero_iff]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hdiag c, hc]
      simp
    have hdet : G.det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero c
      intro i
      have h := congrFun hcol i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
    rw [hdet, Complex.zero_re]
    exact Finset.prod_nonneg fun c _ => hnn c
  · push_neg at hz
    have hpos : ∀ c, 0 < (G c c).re := fun c => lt_of_le_of_ne (hnn c) (Ne.symm (hz c))
    set d : Fin N → ℝ := fun c => (Real.sqrt (G c c).re)⁻¹ with hd_def
    have hdr : ∀ c, d c * (G c c).re * d c = 1 := fun c => by
      have hs := Real.mul_self_sqrt (hnn c)
      have hsq : Real.sqrt (G c c).re ≠ 0 := (Real.sqrt_pos.mpr (hpos c)).ne'
      simp only [hd_def]
      field_simp
      nlinarith [hs]
    set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal fun c => (d c : ℂ) with hD_def
    have hD : Dᴴ = D := by simp [hD_def, Matrix.diagonal_conjTranspose]
    have hH : (D * G * D).PosSemidef := by
      have h := hG.conjTranspose_mul_mul_same D
      rwa [hD] at h
    have hHd : ∀ c, (D * G * D) c c = 1 := by
      intro c
      simp only [hD_def, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [hdiag c]
      exact_mod_cast hdr c
    have h1 := psd_det_re_le_one_of_diag N _ hH hHd
    have hdet : (D * G * D).det = (((∏ c, d c) ^ 2 : ℝ) : ℂ) * G.det := by
      simp only [hD_def, Matrix.det_mul, Matrix.det_diagonal]
      push_cast
      ring
    rw [hdet, Complex.re_ofReal_mul] at h1
    have hprod : (∏ c, d c) ^ 2 * ∏ c, (G c c).re = 1 := by
      rw [show (∏ c, d c) ^ 2 * ∏ c, (G c c).re = ∏ c, (d c * (G c c).re * d c) by
        rw [sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun c _ => by ring]
      exact Finset.prod_eq_one fun c _ => hdr c
    have hp : 0 < (∏ c, d c) ^ 2 :=
      pow_pos (Finset.prod_pos fun c _ => inv_pos.mpr (Real.sqrt_pos.mpr (hpos c))) 2
    by_contra hlt
    push_neg at hlt
    have := mul_lt_mul_of_pos_left hlt hp
    linarith

theorem hadamard_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  have hdet : (A * Aᴴ).det.re = ‖A.det‖ ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    rw [show star A.det = (starRingEnd ℂ) A.det from rfl, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hdiag : ∀ i, ((A * Aᴴ) i i).re = ∑ j, ‖A i j‖ ^ 2 := fun i => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show star (A i j) = (starRingEnd ℂ) (A i j) from rfl, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have key := psd_det_re_le_prod_diag n (A * Aᴴ) (Matrix.posSemidef_self_mul_conjTranspose A)
  rw [hdet] at key
  simp only [hdiag] at key
  have hs : ∀ i, 0 ≤ ∑ j, ‖A i j‖ ^ 2 := fun i => Finset.sum_nonneg fun j _ => by positivity
  calc ‖A.det‖ = Real.sqrt (‖A.det‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [← Finset.prod_pow]
        have h : ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) ^ 2 = ∏ i, ∑ j, ‖A i j‖ ^ 2 :=
          Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hs i)
        rw [h]
        exact key
    _ = ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) :=
        Real.sqrt_sq (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FlatLength
namespace ReciprocityTheory.ChartRestriction.G.T0

open scoped TensorProduct

private theorem length_baseChange_of_isSimpleModule {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (X : Type*) [AddCommGroup X] [Module R X] [hX : IsSimpleModule R X] :
    Module.length S (S ⊗[R] X) = Module.length R X := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hX
  have hIm : I.map (algebraMap R S) = IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.eq_maximalIdeal hI, hm]
  have e2 : (S ⊗[R] X) ≃ₗ[S] (S ⧸ IsLocalRing.maximalIdeal S) :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) e).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.trans
        (Submodule.quotEquivOfEq _ _ hIm))
  have : IsSimpleModule S (S ⧸ IsLocalRing.maximalIdeal S) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal S))
  have : IsSimpleModule S (S ⊗[R] X) := IsSimpleModule.congr e2
  rw [Module.length_eq_one, Module.length_eq_one]

private theorem length_baseChange_of_submodule_simple_quotient {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M) [IsSimpleModule R (M ⧸ N)]
    (ih : Module.length S (S ⊗[R] N) = Module.length R N) :
    Module.length S (S ⊗[R] M) = Module.length R M := by
  have hinj : Function.Injective (N.subtype.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype
  have hsurj : Function.Surjective (N.mkQ.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective S N.mkQ_surjective
  have hex : Function.Exact (N.subtype.baseChange S) (N.mkQ.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact S (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective
  rw [Module.length_eq_add_of_exact _ _ hinj hsurj hex,
    Module.length_eq_add_of_exact _ _ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N),
    ih, length_baseChange_of_isSimpleModule hm (M ⧸ N)]

private theorem length_baseChange_of_isFiniteLength {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    {M : Type*} [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    Module.length S (S ⊗[R] M) = Module.length R M := by
  induction h with
  | @of_subsingleton M' _ _ _ =>
    have : Subsingleton (S ⊗[R] M') := by
      have h0 : ∀ z : S ⊗[R] M', z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul s m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [hx, hy, add_zero]
      exact ⟨fun a b => by rw [h0 a, h0 b]⟩
    rw [Module.length_eq_zero, Module.length_eq_zero]
  | of_simple_quotient _ ih =>
    exact length_baseChange_of_submodule_simple_quotient hm _ ih

private theorem length_le_length_baseChange_of_faithfullyFlat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Module.length R Q ≤ Module.length S (S ⊗[R] Q) := by
  have hmono : ∀ N N' : Submodule R Q, N ≤ N' →
      LinearMap.range (N.subtype.baseChange S) ≤ LinearMap.range (N'.subtype.baseChange S) := by
    intro N N' h x hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    refine LinearMap.mem_range.mpr ⟨(Submodule.inclusion h).baseChange S z, ?_⟩
    rw [← Submodule.subtype_comp_inclusion _ _ h, LinearMap.baseChange_comp, LinearMap.comp_apply]
  have hrefl : ∀ N N' : Submodule R Q,
      LinearMap.range (N'.subtype.baseChange S) ≤ LinearMap.range (N.subtype.baseChange S) →
        N' ≤ N := by
    intro N N' h
    have hz : ∀ w : S ⊗[R] N, (N.mkQ.baseChange S) ((N.subtype.baseChange S) w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul s n =>
        have hn : N.mkQ (N.subtype n) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr n.2
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hn, TensorProduct.tmul_zero]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
    have h0 : (N.mkQ ∘ₗ N'.subtype).lTensor S = 0 := by
      refine LinearMap.ext fun z => ?_
      obtain ⟨w, hw⟩ :=
        LinearMap.mem_range.mp (h (LinearMap.mem_range_self (N'.subtype.baseChange S) z))
      have hb : ((N.mkQ ∘ₗ N'.subtype).baseChange S) z = 0 := by
        rw [LinearMap.baseChange_comp, LinearMap.comp_apply, ← hw, hz]
      rw [LinearMap.zero_apply]
      rwa [LinearMap.baseChange_eq_ltensor] at hb
    have hf : N.mkQ ∘ₗ N'.subtype = 0 :=
      (Module.FaithfullyFlat.zero_iff_lTensor_zero R S _).mpr h0
    intro x hx
    have hx0 := LinearMap.congr_fun hf ⟨x, hx⟩
    simpa using hx0
  have hsm : StrictMono (fun N : Submodule R Q => LinearMap.range (N.subtype.baseChange S)) :=
    fun N N' hlt => lt_of_le_of_ne (hmono N N' hlt.le)
      (fun heq => hlt.ne (le_antisymm hlt.le (hrefl N N' heq.ge)))
  have h1 : (Module.length R Q : WithBot ℕ∞) ≤ (Module.length S (S ⊗[R] Q) : WithBot ℕ∞) := by
    rw [Module.coe_length, Module.coe_length]
    exact Order.krullDim_le_of_strictMono _ hsm
  exact WithBot.coe_le_coe.mp h1

theorem length_baseChange_eq {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [Module.Flat R S] [IsLocalHom (algebraMap R S)]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Module.length S (S ⊗[R] Q) = Module.length R Q := by
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hge := length_le_length_baseChange_of_faithfullyFlat (R := R) (S := S) Q
  by_cases hQ : Module.length R Q = ⊤
  · rw [hQ] at hge ⊢
    exact top_le_iff.mp hge
  · exact length_baseChange_of_isFiniteLength hm (Module.length_ne_top_iff.mp hQ)

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TransferenceA
namespace ReciprocityTheory.ChartRestriction.G.T0

open MeasureTheory Module Submodule

theorem gtA_countable {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) :
    Countable (span ℤ (Set.range B)).toAddSubgroup := by
  have e : ((span ℤ (Set.range B) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)) =
      Set.range (fun c : Fin n → ℤ => ∑ i, c i • B i) := by
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun, Set.mem_range]
  have hc : ((span ℤ (Set.range B) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)).Countable := by
    rw [e]
    exact Set.countable_range _
  exact hc.to_subtype

theorem gtA_mink_pi_lt {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (h : |(Matrix.of B).det| < t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ < t := by
  haveI := gtA_countable B
  have fund := ZSpan.isAddFundamentalDomain B volume
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (span ℤ (Set.range B)).toAddSubgroup) fund (s := Metric.ball (0 : Fin n → ℝ) t) (fun y hy => by simpa using hy)
    (convex_ball (0 : Fin n → ℝ) t) (by
      have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [ZSpan.volume_fundamentalDomain B, Real.volume_pi_ball 0 ht, Module.finrank_fin_fun,
        Fintype.card_fin, h2, ← ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_lt_ofReal_iff (by positivity), mul_pow, mul_comm ((2 : ℝ) ^ n)]
      exact mul_lt_mul_of_pos_right h (by positivity))
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hxs

theorem gtA_mink_pi_le {n : ℕ} (hn : 0 < n) (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ}
    (ht : 0 < t) (h : |(Matrix.of B).det| ≤ t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ ≤ t := by
  haveI := gtA_countable B
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have fund := ZSpan.isAddFundamentalDomain B volume
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := (span ℤ (Set.range B)).toAddSubgroup) fund (s := Metric.closedBall (0 : Fin n → ℝ) t) (fun y hy => by simpa using hy)
    (convex_closedBall (0 : Fin n → ℝ) t) (isCompact_closedBall (0 : Fin n → ℝ) t) (by
      have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [ZSpan.volume_fundamentalDomain B, Real.volume_pi_closedBall 0 ht.le, Module.finrank_fin_fun,
        Fintype.card_fin, h2, ← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_pow, mul_comm ((2 : ℝ) ^ n)]
      exact mul_le_mul_of_nonneg_right h (by positivity))
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hxs

theorem gtA_norm_le_sqrt_mul (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by
  rw [EuclideanSpace.norm_eq]
  have hM : ∀ i, ‖x i‖ ≤ ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := fun i =>
    norm_le_pi_norm (EuclideanSpace.equiv (Fin n) ℝ x) i
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin n, ‖EuclideanSpace.equiv (Fin n) ℝ x‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => by gcongr; exact hM i
    _ = Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem gtB_inner_eq (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ k, EuclideanSpace.equiv (Fin n) ℝ x k * EuclideanSpace.equiv (Fin n) ℝ y k := by
  simp [PiLp.inner_apply, mul_comm]

theorem gtB_nondeg (n : ℕ) : (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate := by
  show _ ∧ _
  constructor
  · intro x hx
    simpa using hx x
  · intro y hy
    simpa using hy y

theorem gtB_dual_short {n : ℕ} (hn : 0 < n) (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ (∀ j, ∃ m : ℤ, inner ℝ y (b j) = m) ∧
      ‖y‖ ≤ n / lam := by
  set e := EuclideanSpace.equiv (Fin n) ℝ with he
  set B := b.map e.toLinearEquiv with hBdef
  have hB : ∀ j, B j = e (b j) := fun j => by simp [B]
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hdet : (lam / Real.sqrt n) ^ n ≤ |(Matrix.of B).det| := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hxs, hx0, hxn⟩ := gtA_mink_pi_lt B (by positivity) hlt
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxs
    have hex : e (∑ i, c i • b i) = ∑ i, c i • B i := by simp [hB, map_sum, map_zsmul]
    have hx'0 : (∑ i, c i • b i) ≠ 0 := by intro h; apply hx0; rw [← hex, h, map_zero]
    have h1 := hmin _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hx'0
    have h2 := gtA_norm_le_sqrt_mul n (∑ i, c i • b i)
    rw [hex] at h2
    have : Real.sqrt n * ‖∑ i, c i • B i‖ < lam := by
      calc _ < Real.sqrt n * (lam / Real.sqrt n) := mul_lt_mul_of_pos_left hxn hsq
        _ = lam := by field_simp
    linarith
  set c := LinearMap.BilinForm.dualBasis (innerₗ (EuclideanSpace ℝ (Fin n))) (gtB_nondeg n) b with hcdef
  have hc : ∀ i j, inner ℝ (c i) (b j) = if j = i then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left (gtB_nondeg n) b i j
    simpa using this
  set C := c.map e.toLinearEquiv with hCdef
  have hC : ∀ j, C j = e (c j) := fun j => by simp [C]
  have hCB : Matrix.of C * (Matrix.of B).transpose = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, hB, hC]
    rw [← gtB_inner_eq, hc]
    simp [eq_comm]
  have hdetCB : (Matrix.of C).det * (Matrix.of B).det = 1 := by
    rw [← Matrix.det_transpose (Matrix.of B), ← Matrix.det_mul, hCB, Matrix.det_one]
  have hdetC : |(Matrix.of C).det| ≤ (Real.sqrt n / lam) ^ n := by
    have hpos : 0 < (lam / Real.sqrt n) ^ n := by positivity
    have h1 : |(Matrix.of C).det| * |(Matrix.of B).det| = 1 := by rw [← abs_mul, hdetCB, abs_one]
    have h2 : |(Matrix.of C).det| = |(Matrix.of B).det|⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, show (Real.sqrt n / lam) ^ n = ((lam / Real.sqrt n) ^ n)⁻¹ by
      rw [← inv_pow, inv_div]]
    exact inv_anti₀ hpos hdet
  obtain ⟨x, hxs, hx0, hxn⟩ := gtA_mink_pi_le hn C (by positivity) hdetC
  obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxs
  have hex : e (∑ i, k i • c i) = ∑ i, k i • C i := by simp [hC, map_sum, map_zsmul]
  refine ⟨∑ i, k i • c i, ?_, ?_, ?_⟩
  · intro h; apply hx0; rw [← hex, h, map_zero]
  · intro j
    refine ⟨k j, ?_⟩
    rw [sum_inner]
    simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hc]
    simp
  · have h2 := gtA_norm_le_sqrt_mul n (∑ i, k i • c i)
    rw [hex] at h2
    calc _ ≤ _ := h2
      _ ≤ Real.sqrt n * (Real.sqrt n / lam) := mul_le_mul_of_nonneg_left hxn hsq.le
      _ = n / lam := by
        rw [← mul_div_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BasisExtend
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LinearIndependentC
namespace ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

lemma coeff_smul_C (q : MvPolynomial σ L) (e : E) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (q • C e : MvPolynomial σ E) m = algebraMap L E (AddMonoidAlgebra.coeff q m) * e := by
  rw [Algebra.smul_def, algebraMap_def, mul_comm, coeff_C_mul, coeff_map, mul_comm]

variable {n : Type} [Fintype n] (b : Module.Basis n L E)

noncomputable def crd (p : MvPolynomial σ E) (i : n) : MvPolynomial σ L :=
  ∑ m ∈ p.support, monomial m (b.repr (AddMonoidAlgebra.coeff p m) i)

lemma coeff_crd (p : MvPolynomial σ E) (i : n) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (crd b p i) m = b.repr (AddMonoidAlgebra.coeff p m) i := by
  classical
  rw [crd, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero, Finsupp.zero_apply]

lemma eq_sum_crd (p : MvPolynomial σ E) : p = ∑ i, crd b p i • (C (b i) : MvPolynomial σ E) := by
  ext m
  rw [coeff_sum]
  simp only [coeff_smul_C, coeff_crd, ← Algebra.smul_def]
  exact (b.sum_repr (AddMonoidAlgebra.coeff p m)).symm

lemma linearIndependent_C : LinearIndependent (MvPolynomial σ L) (fun i => (C (b i) : MvPolynomial σ E)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  apply MvPolynomial.ext
  intro m
  have h : ∑ j, AddMonoidAlgebra.coeff (g j) m • b j = 0 := by
    simpa only [coeff_sum, coeff_smul_C, ← Algebra.smul_def,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      congrArg (AddMonoidAlgebra.coeff · m) hg
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  exact (Fintype.linearIndependent_iff.1 b.linearIndependent) (fun j => AddMonoidAlgebra.coeff (g j) m) h i

end ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis
end

namespace ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension

variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

noncomputable def liftY : FractionRing (MvPolynomial σ L) →+* FractionRing (MvPolynomial σ E) :=
  IsFractionRing.lift (A := MvPolynomial σ L)
    (g := (algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))).comp
      (MvPolynomial.map (algebraMap L E)))
    ((IsFractionRing.injective (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))).comp
      (MvPolynomial.map_injective _ (algebraMap L E).injective))

theorem basis_extend [FiniteDimensional L E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n L E) :
    letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
      (liftY (L := L) (E := E) (σ := σ)).toAlgebra;
    ∃ b' : Module.Basis n (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)),
      (∀ i, b' i = algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.C (b i))) ∧
      ∀ e : E, Algebra.leftMulMatrix b' (algebraMap (MvPolynomial σ E)
          (FractionRing (MvPolynomial σ E)) (MvPolynomial.C e)) =
        (Algebra.leftMulMatrix b e).map (algebraMap L (FractionRing (MvPolynomial σ L))) := by

  try intro _
  letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) := (liftY (L := L) (E := E) (σ := σ)).toAlgebra
  letI : Algebra (MvPolynomial σ L) (MvPolynomial σ E) := MvPolynomial.algebraMvPolynomial
  classical
  have hlift : ∀ q : MvPolynomial σ L, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) =
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.map (algebraMap L E) q) := by
    intro q
    show liftY (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) = _
    simp only [liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  have hsmul : ∀ (q : MvPolynomial σ L) (P : MvPolynomial σ E),
      q • P = MvPolynomial.map (algebraMap L E) q * P := fun q P => by
    rw [Algebra.smul_def]; rfl
  have himg : ∀ (q : MvPolynomial σ L) (P : MvPolynomial σ E),
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (q • P) = algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) P := by
    intro q P; rw [hsmul, map_mul, hlift]
  have hmem : ∀ P : MvPolynomial σ E, algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) P ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro P
    set_option synthInstance.maxHeartbeats 100000 in
      rw [PolynomialCoordinateBasis.eq_sum_crd b P, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [himg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (FractionRing (MvPolynomial σ L)) (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (MvPolynomial σ L))
      Finset.univ g
    have hd' : ∀ j, ∃ a : MvPolynomial σ L, algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) a = (d : MvPolynomial σ L) • g j :=
      fun j => hd j (Finset.mem_univ j)
    choose a ha using hd'
    have h0 : algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (∑ j, a j • (MvPolynomial.C (b j) : MvPolynomial σ E)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [himg, ha]
      have e1 : ∑ j, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) ((d : MvPolynomial σ L) • g j) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) =
          algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) d) * ∑ j, g j • algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
      rw [e1]
      beta_reduce at hg
      rw [hg, mul_zero]
    have h1 : ∑ j, a j • (MvPolynomial.C (b j) : MvPolynomial σ E) = 0 :=
      IsFractionRing.injective _ (FractionRing (MvPolynomial σ E)) (by rw [h0, map_zero])
    have h2 := (Fintype.linearIndependent_iff.mp (PolynomialCoordinateBasis.linearIndependent_C (σ := σ) b)) a h1 i
    have h3 : (d : MvPolynomial σ L) • g i = 0 := by rw [← ha i, h2, map_zero]
    rw [Algebra.smul_def] at h3
    exact (mul_eq_zero.mp h3).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)
  have hmul : ∀ x ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))), ∀ y ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))), x * y ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro x hx y hy
    have hxy := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at hxy
    refine (Submodule.span_le.mpr ?_) hxy
    rintro _ ⟨_, ⟨k, rfl⟩, _, ⟨l, rfl⟩, rfl⟩
    show algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b k)) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b l)) ∈ _
    rw [← map_mul]; exact hmem _
  have hone : (1 : FractionRing (MvPolynomial σ E)) ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by simpa using hmem 1
  have hfg : (Subalgebra.toSubmodule ((Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))))).toSubalgebra hone (fun x y hx hy => hmul x hx y hy))).FG := by
    rw [Submodule.toSubalgebra_toSubmodule]
    exact Submodule.fg_span (Set.finite_range _)
  have htop : ⊤ ≤ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro x _
    obtain ⟨a, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial σ E) x
    have hint := IsIntegral.of_mem_of_fg _ hfg (algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) q) (hmem q)
    have hinv := Subalgebra.inv_mem_of_algebraic ((Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))))).toSubalgebra hone (fun x y hx hy => hmul x hx y hy))
      (x := ⟨algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) q, hmem q⟩) hint.isAlgebraic
    rw [div_eq_mul_inv]
    exact hmul _ (hmem a) _ hinv
  refine ⟨Module.Basis.mk hli htop, fun i => Module.Basis.mk_apply _ _ _, fun e => ?_⟩
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.mk_apply]
  have hx : algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C e) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) =
      ∑ k, algebraMap L (FractionRing (MvPolynomial σ L)) (b.repr (e * b j) k) • (Module.Basis.mk hli htop) k := by
    rw [← map_mul, ← MvPolynomial.C_mul]
    conv_lhs => rw [← b.sum_repr (e * b j)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Module.Basis.mk_apply, Algebra.smul_def (algebraMap L (FractionRing (MvPolynomial σ L)) _),
      IsScalarTower.algebraMap_apply L (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)), MvPolynomial.algebraMap_eq,
      ← himg, hsmul, MvPolynomial.map_C, ← MvPolynomial.C_mul, Algebra.smul_def]
  beta_reduce
  rw [hx, Module.Basis.repr_sum_self]

end ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PrimeAvoidanceFibre
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SpanTopOfComplete
namespace ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete

theorem span_eq_top_of_complete {O N : Type*} [CommRing O] [AddCommGroup N] [Module O N] (ϖ : O)
    [IsPrecomplete (Ideal.span {ϖ}) O]
    (hsep : ∀ x : N, (∀ k : ℕ, ∃ y : N, x = ϖ ^ k • y) → x = 0) {n : ℕ} (S : Fin n → N)
    (hS : ∀ x : N, ∃ c : Fin n → O, ∃ y : N, x = ∑ i, c i • S i + ϖ • y) :
    Submodule.span O (Set.range S) = ⊤ := by
  classical
  choose c y hcy using hS
  rw [eq_top_iff]
  intro x _
  let xs : ℕ → N := fun k => Nat.rec x (fun _ z => y z) k
  have hxs : ∀ k, xs (k + 1) = y (xs k) := fun k => rfl
  let a : ℕ → Fin n → O := fun k i => ∑ j ∈ Finset.range k, ϖ ^ j * c (xs j) i
  have hxa : ∀ k, x = ∑ i, a k i • S i + ϖ ^ k • xs k := by
    intro k
    induction k with
    | zero => simp [a, xs]
    | succ k ih =>
      have hk := hcy (xs k)
      calc x = ∑ i, a k i • S i + ϖ ^ k • xs k := ih
        _ = ∑ i, a k i • S i + ϖ ^ k • (∑ i, c (xs k) i • S i + ϖ • y (xs k)) := by rw [← hk]
        _ = ∑ i, a (k + 1) i • S i + ϖ ^ (k + 1) • xs (k + 1) := by
          rw [hxs]
          simp only [a, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum,
            smul_smul, pow_succ]
          abel

  have hmem : ∀ m k, m ≤ k → ∀ i, a k i - a m i ∈ Ideal.span {ϖ ^ m} := by
    intro m k hmk i
    have : a k i - a m i = ∑ j ∈ Finset.Ico m k, ϖ ^ j * c (xs j) i := by
      simp only [a]
      rw [← Finset.sum_range_add_sum_Ico _ hmk]
      ring
    rw [this]
    refine Ideal.sum_mem _ fun j hj => ?_
    rw [Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (pow_dvd_pow ϖ (Finset.mem_Ico.1 hj).1) _
  have hpow : ∀ m : ℕ, (Ideal.span {ϖ} ^ m • ⊤ : Submodule O O) = Ideal.span {ϖ ^ m} := by
    intro m
    rw [Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top]
  have hlim : ∀ i, ∃ L : O, ∀ k, a k i - L ∈ Ideal.span {ϖ ^ k} := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (fun k => a k i) (fun {m k} hmk => by
      rw [SModEq.sub_mem, hpow]
      have := hmem m k hmk i
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 this)
    exact ⟨L, fun k => by have := hL k; rwa [SModEq.sub_mem, hpow] at this⟩
  choose L hL using hlim
  have hx : x = ∑ i, L i • S i := by
    rw [← sub_eq_zero]
    refine hsep _ fun k => ?_
    have ht : ∀ i, ∃ t : O, a k i - L i = ϖ ^ k * t := fun i => Ideal.mem_span_singleton'.1 (hL i k) |>.imp
      fun t ht => by rw [← ht, mul_comm]
    choose t ht using ht
    refine ⟨∑ i, t i • S i + xs k, ?_⟩
    conv_lhs => rw [hxa k]
    have e : ∀ i, a k i • S i = L i • S i + ϖ ^ k • t i • S i := by
      intro i
      rw [smul_smul, ← ht i, sub_smul]
      abel
    simp only [e, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
    abel
  rw [hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete
end

namespace ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre

open IsLocalRing

theorem avoid {B : Type*} [CommRing B] [IsNoetherianRing B] (M q : Ideal B) [hM : M.IsMaximal] (w : B)
    (hchain : ∀ P : Ideal B, P.IsPrime → q ≤ P → P ≤ M → w ∈ P → P = M) :
    ∃ s ∉ M, ∀ P : Ideal B, P.IsPrime → q ≤ P → w ∈ P → s ∉ P → P = M := by
  classical
  haveI := hM.isPrime
  set I : Ideal B := q ⊔ Ideal.span {w} with hI
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
  have hprop : ∀ p ∈ I.minimalPrimes, p.IsPrime ∧ I ≤ p := fun p hp => hp.1
  have hnot : ∀ p ∈ I.minimalPrimes, p ≠ M → ¬ p ≤ M := by
    intro p hp hne hle
    obtain ⟨hpp, hIp⟩ := hprop p hp
    exact hne (hchain p hpp (le_trans le_sup_left hIp) hle
      (hIp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))
  have hex : ∀ p ∈ I.minimalPrimes, p ≠ M → ∃ x ∈ p, x ∉ M :=
    fun p hp hne => SetLike.not_le_iff_exists.mp (hnot p hp hne)
  let f : Ideal B → B := fun p =>
    if h : p ∈ I.minimalPrimes ∧ p ≠ M then (hex p h.1 h.2).choose else 1
  let T := hfin.toFinset.filter (· ≠ M)
  refine ⟨∏ p ∈ T, f p, ?_, ?_⟩
  · intro hmem
    obtain ⟨p, hpT, hpM⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset] at hpT
    have h1 := (hex p hpT.1 hpT.2).choose_spec.2
    simp only [f, dif_pos hpT] at hpM
    exact h1 hpM
  · intro P hP hqP hwP hsP
    have hIP : I ≤ P := sup_le hqP ((Ideal.span_singleton_le_iff_mem P).mpr hwP)
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le hIP
    by_cases hpM : p = M
    · rw [hpM] at hpP
      exact (hM.eq_of_le hP.ne_top hpP).symm
    · exfalso
      apply hsP
      apply Ideal.IsPrime.prod_mem_iff.mpr
      refine ⟨p, ?_, ?_⟩
      · simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨hp, hpM⟩
      · simp only [f, dif_pos (And.intro hp hpM)]
        exact hpP (hex p hp hpM).choose_spec.1

theorem finite_of_fibre {O T : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing T] [IsDomain T] [IsNoetherianRing T] [Algebra O T]
    [Algebra.FiniteType O T] (ϖ : O) (hϖ : Irreducible ϖ)
    (hex : ∃ P : Ideal T, P.IsPrime ∧ algebraMap O T ϖ ∈ P)
    (huniq : ∀ P P' : Ideal T, P.IsPrime → P'.IsPrime → algebraMap O T ϖ ∈ P → algebraMap O T ϖ ∈ P' →
      P = P') : Module.Finite O T := by
  classical
  set w := algebraMap O T ϖ with hw
  set J : Ideal T := Ideal.span {w} with hJ
  obtain ⟨P0, hP0, hwP0⟩ := hex
  have hJtop : J ≠ ⊤ := fun h => hP0.ne_top (eq_top_iff.2 (h ▸ (Ideal.span_singleton_le_iff_mem P0).2 hwP0))

  have hdim : Ring.KrullDimLE 0 (T ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    obtain ⟨N, hN, hIN⟩ := Ideal.exists_le_maximal I hI.ne_top
    have hwI : w ∈ Ideal.comap (Ideal.Quotient.mk J) I := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self w)]
      exact I.zero_mem
    have hwN : w ∈ Ideal.comap (Ideal.Quotient.mk J) N := Ideal.comap_mono hIN hwI
    have e := huniq _ _ (Ideal.comap_isPrime _ I) (Ideal.comap_isPrime _ N) hwI hwN
    have : I = N := by
      have h1 := congrArg (Ideal.map (Ideal.Quotient.mk J)) e
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    rw [this]; exact hN
  have hart : IsArtinianRing (T ⧸ J) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

  have hmJ : maximalIdeal O ≤ Ideal.comap (algebraMap O T) J := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_span_singleton_self w
  let _ : Algebra (O ⧸ maximalIdeal O) (T ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hmJ
  have hmk : ∀ c : O, algebraMap (O ⧸ maximalIdeal O) (T ⧸ J) (Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk J (algebraMap O T c) := fun c => rfl
  have : IsScalarTower O (O ⧸ maximalIdeal O) (T ⧸ J) := IsScalarTower.of_algebraMap_eq fun c => (hmk c).symm
  have : Algebra.FiniteType O (T ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O J) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType (O ⧸ maximalIdeal O) (T ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  have : IsJacobsonRing (O ⧸ maximalIdeal O) := by
    let _ := Ideal.Quotient.field (maximalIdeal O); infer_instance
  have : Module.Finite (O ⧸ maximalIdeal O) (T ⧸ J) := Module.finite_of_isArtinianRing _ _
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := O ⧸ maximalIdeal O) (M := T ⧸ J)
  choose S hS using fun i => Ideal.Quotient.mk_surjective (g i)
  have hgen : ∀ x : T, ∃ c : Fin n → O, ∃ y : T, x = ∑ i, c i • S i + ϖ • y := by
    intro x
    have hx : Ideal.Quotient.mk J x ∈ Submodule.span (O ⧸ maximalIdeal O) (Set.range g) := by
      rw [hg]; trivial
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    choose c hc using fun i => Ideal.Quotient.mk_surjective (cb i)
    have hmem : x - ∑ i, c i • S i ∈ J := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, ← hcb, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc i, ← hS i, Algebra.smul_def, Algebra.smul_def, map_mul, hmk]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨c, y, ?_⟩
    rw [Algebra.smul_def, ← hw, mul_comm, hy]
    abel
  have hsep : ∀ x : T, (∀ k : ℕ, ∃ y : T, x = ϖ ^ k • y) → x = 0 := by
    intro x hx
    have h0 := Ideal.iInf_pow_eq_bot_of_isDomain J hJtop
    have : x ∈ ⨅ k : ℕ, J ^ k := by
      rw [Ideal.mem_iInf]
      intro k
      obtain ⟨y, rfl⟩ := hx k
      rw [hJ, Ideal.span_singleton_pow, Algebra.smul_def, map_pow, ← hw]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [h0] at this
    exact (Submodule.mem_bot T).1 this
  have : IsAdicComplete (Ideal.span {ϖ}) O := hϖ.maximalIdeal_eq ▸ inferInstance
  have htop := SpanTopOfComplete.span_eq_top_of_complete ϖ hsep S hgen
  exact ⟨Submodule.fg_def.2 ⟨Set.range S, Set.finite_range S, htop⟩⟩

end ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre
end
