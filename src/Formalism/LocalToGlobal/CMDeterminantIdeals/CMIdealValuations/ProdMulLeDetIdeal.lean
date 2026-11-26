module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

namespace A2

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_pos' {I : FractionalIdeal (𝓞 K)⁰ K} (h : I ≠ 0) : 0 < FractionalIdeal.absNorm I :=
  lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I) (fun e => h (FractionalIdeal.absNorm_eq_zero_iff.1 e.symm))

theorem absNorm_anti' {I J : FractionalIdeal (𝓞 K)⁰ K} (hIJ : I ≤ J) (hI : I ≠ 0) :
    FractionalIdeal.absNorm J ≤ FractionalIdeal.absNorm I := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact hI (FractionalIdeal.le_zero_iff.1 hIJ)
  have hX : I * J⁻¹ ≤ 1 := by
    calc I * J⁻¹ ≤ J * J⁻¹ := mul_le_mul' hIJ le_rfl
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨X, hX'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX
  have hdec : I = J * (I * J⁻¹) := by
    rw [mul_comm I, ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]
  have hIJ0 : I * J⁻¹ ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
  have hX0 : X ≠ ⊥ := by
    rintro rfl
    apply hIJ0
    rw [← hX']
    exact FractionalIdeal.coeIdeal_bot
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm (I * J⁻¹) := by
    rw [← hX', FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm X ≠ 0 := fun e => hX0 (Ideal.absNorm_eq_zero_iff.1 e)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  calc FractionalIdeal.absNorm J = FractionalIdeal.absNorm J * 1 := (mul_one _).symm
    _ ≤ FractionalIdeal.absNorm J * FractionalIdeal.absNorm (I * J⁻¹) :=
        mul_le_mul_of_nonneg_left hN (FractionalIdeal.absNorm_nonneg _)
    _ = FractionalIdeal.absNorm I := by rw [← map_mul, ← hdec]

theorem abs_norm_eq_prod (x : K) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  have h2 := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h2
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖) (fun _ => rfl), ← h2]
  simp

theorem absNorm_span_real (x : K) :
    ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  rw [FractionalIdeal.absNorm_span_singleton (𝓞 K), abs_norm_eq_prod]

theorem det_re_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : A.PosDef) : 0 < A.det.re := by
  simpa using (Complex.lt_def.1 h.det_pos).1

theorem exists_den {m : ℕ} (M : Submodule (𝓞 K) (Fin m → K)) (hM : M.FG) :
    ∃ a ∈ (𝓞 K)⁰, ∀ x ∈ M, ∀ i, IsLocalization.IsInteger (𝓞 K) (a • x i) := by
  have hc : ∀ i : Fin m, ∃ a ∈ (𝓞 K)⁰, ∀ b ∈ M.map (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K),
      IsLocalization.IsInteger (𝓞 K) (a • b) :=
    fun i => FractionalIdeal.isFractional_of_fg (hM.map _)
  choose a ha hb using hc
  refine ⟨∏ i, a i, prod_mem fun i _ => ha i, fun x hx i => ?_⟩
  have hxi := hb i (x i) (Submodule.mem_map_of_mem (f := (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K)) hx)
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
  exact IsLocalization.isInteger_smul hxi

theorem isInteger_det {m : ℕ} (x : Fin m → Fin m → K) (hx : ∀ i j, IsLocalization.IsInteger (𝓞 K) (x i j)) :
    IsLocalization.IsInteger (𝓞 K) (Matrix.of x).det := by
  have hx' : ∀ i j, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x i j := fun i j => hx i j
  choose y hy using hx'
  refine ⟨(Matrix.of y).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [hy]

theorem detSub_isFractional {m : ℕ} (L : MLat K m) (hM : L.M.FG) : IsFractional (𝓞 K)⁰ L.detSub := by
  obtain ⟨a, ha, hint⟩ := exists_den L.M hM
  refine ⟨a ^ m, pow_mem ha m, fun b hb => ?_⟩
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    have : (a ^ m) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det := by
      rw [show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 K) K a) • Matrix.of x by
        ext i j; simp [Algebra.smul_def]]
      rw [Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
    rw [this]
    exact isInteger_det _ fun i j => hint _ (hx i) j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [smul_add]; exact IsLocalization.isInteger_add hx hy
  | smul r x _ hx => rw [smul_comm]; exact IsLocalization.isInteger_smul hx

theorem detIdeal_coe {m : ℕ} (L : MLat K m) (h : IsFractional (𝓞 K)⁰ L.detSub) :
    (L.detIdeal : Submodule (𝓞 K) K) = L.detSub := by
  have e : L.detIdeal = ⟨L.detSub, h⟩ := dif_pos h
  rw [e]
  rfl

theorem det_mem {m : ℕ} (L : MLat K m) (x : Fin m → Fin m → K) (hx : ∀ i, x i ∈ L.M) :
    (Matrix.of x).det ∈ L.detSub :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem exists_det_ne {m : ℕ} (M : Submodule (𝓞 K) (Fin m → K))
    (hM : Submodule.span K (M : Set (Fin m → K)) = ⊤) :
    ∃ x : Fin m → Fin m → K, (∀ i, x i ∈ M) ∧ (Matrix.of x).det ≠ 0 := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (M : Set (Fin m → K))
  let B := Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hspan, hM]))
  let e := B.indexEquiv (Pi.basisFun K (Fin m))
  refine ⟨fun i => (e.symm i : Fin m → K), fun i => hs (e.symm i).2, ?_⟩
  have hli' : LinearIndependent K (fun i => (e.symm i : Fin m → K)) := hli.comp _ e.symm.injective
  have : IsUnit (Matrix.of fun i => (e.symm i : Fin m → K)) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

end A2


namespace A2
variable {K : Type} [Field K] [NumberField K]

end A2


namespace A2
variable {K : Type} [Field K] [NumberField K]

theorem detSub_free {m : ℕ} (L : MLat K m) (b : Fin m → Fin m → K)
    (hb : L.M = Submodule.span (𝓞 K) (Set.range b)) :
    L.detSub = Submodule.span (𝓞 K) {(Matrix.of b).det} := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro d ⟨x, hx, rfl⟩
    have : ∀ i, ∃ c : Fin m → 𝓞 K, ∑ j, c j • b j = x i := fun i => by
      have := hx i
      rw [hb] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using this
    have hx' : Matrix.of x = (Matrix.of c).map (algebraMap (𝓞 K) K) * Matrix.of b := by
      ext i j
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
      rw [← hc i]
      simp [Finset.sum_apply, Algebra.smul_def]
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨(Matrix.of c).det, ?_⟩
    rw [Algebra.smul_def, RingHom.map_det, hx', Matrix.det_mul]
    rfl
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.subset_span ⟨b, fun i => ?_, rfl⟩
    rw [hb]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem gramC_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC H σ b = ((Matrix.of b).map σ).transpose.conjTranspose * H * ((Matrix.of b).map σ).transpose := by
  ext i j
  simp only [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, Matrix.of_apply, Matrix.mul_apply, dotProduct,
    Matrix.mulVec, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem gramC_det {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    (ReciprocityTheory.MultiplicativeHeights.gramC H σ b).det = (Complex.normSq (σ (Matrix.of b).det) : ℂ) * H.det := by
  rw [gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose,
    RingHom.map_det σ (Matrix.of b), Complex.normSq_eq_conj_mul_self]
  simp only [RingHom.mapMatrix_apply, Complex.star_def]
  ring

end A2


theorem hadamardInequality : HadamardPD := by
  intro m A hA
  have hdpos : ∀ i, 0 < (A i i).re := fun i => by
    simpa using (Complex.lt_def.1 (hA.diag_pos (i := i))).1
  have hdiag : ∀ i, A i i = ((A i i).re : ℂ) := fun i => (hA.isHermitian.coe_re_apply_self i).symm
  set s : Fin m → ℝ := fun i => (Real.sqrt (A i i).re)⁻¹ with hs
  have hspos : ∀ i, 0 < s i := fun i => inv_pos.2 (Real.sqrt_pos.2 (hdpos i))
  have hs2 : ∀ i, s i ^ 2 * (A i i).re = 1 := fun i => by
    rw [hs]; simp only
    rw [inv_pow, Real.sq_sqrt (hdpos i).le, inv_mul_cancel₀ (hdpos i).ne']
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i => (s i : ℂ) with hD
  have hDh : D.conjTranspose = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp
  have hDdet : D.det = ∏ i, (s i : ℂ) := by rw [hD, Matrix.det_diagonal]
  have hDu : IsUnit D := by
    rw [Matrix.isUnit_iff_isUnit_det, hDdet]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (hspos i).ne')
  have hC : (D.conjTranspose * A * D).PosDef := hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 hDu)
  set C := D.conjTranspose * A * D with hCdef
  have hCii : ∀ i, C i i = 1 := fun i => by
    rw [hCdef, hDh, hD]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hdiag i]
    rw [show (s i : ℂ) * ((A i i).re : ℂ) * (s i : ℂ) = ((s i ^ 2 * (A i i).re : ℝ) : ℂ) by push_cast; ring, hs2 i]
    simp
  have hCdet : C.det = A.det * ∏ i, ((s i ^ 2 : ℝ) : ℂ) := by
    rw [hCdef, Matrix.det_mul, Matrix.det_mul, hDh, hDdet]
    push_cast
    rw [Finset.prod_pow]
    ring
  have hev := hC.isHermitian.det_eq_prod_eigenvalues
  have htr := hC.isHermitian.trace_eq_sum_eigenvalues
  set ev := hC.isHermitian.eigenvalues with hev_def
  have hevpos : ∀ i, 0 < ev i := hC.eigenvalues_pos
  have hsum : ∑ i, ev i = m := by
    have : C.trace = (m : ℂ) := by
      simp [Matrix.trace, hCii]
    rw [this] at htr
    apply Complex.ofReal_injective
    push_cast
    exact htr.symm
  have hprod : ∏ i, ev i ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have amgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) ev
      (fun _ _ => zero_le_one) (by simp [hmR]) (fun i _ => (hevpos i).le)
    simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, hsum, div_self hmR.ne'] at amgm
    by_contra hlt
    push Not at hlt
    have := Real.one_lt_rpow hlt (inv_pos.2 hmR)
    linarith
  have hA' : A.det = (∏ i, ev i : ℝ) * ∏ i, (((A i i).re : ℝ) : ℂ) := by
    have h1 : C.det = ((∏ i, ev i : ℝ) : ℂ) := by rw [hev]; push_cast; rfl
    have h2 : (∏ i, ((s i ^ 2 : ℝ) : ℂ)) * ∏ i, (((A i i).re : ℝ) : ℂ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro i _
      rw [← Complex.ofReal_mul, hs2 i, Complex.ofReal_one]
    calc A.det = A.det * ((∏ i, ((s i ^ 2 : ℝ) : ℂ)) * ∏ i, (((A i i).re : ℝ) : ℂ)) := by rw [h2, mul_one]
      _ = C.det * ∏ i, (((A i i).re : ℝ) : ℂ) := by rw [hCdet]; ring
      _ = _ := by rw [h1]
  rw [hA', ← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re]
  calc (∏ i, ev i) * ∏ i, (A i i).re ≤ 1 * ∏ i, (A i i).re :=
        mul_le_mul_of_nonneg_right hprod (Finset.prod_nonneg fun i _ => (hdpos i).le)
    _ = _ := one_mul _

namespace A2
variable {K : Type} [Field K] [NumberField K]
open scoped Pointwise

end A2


end Formalism.L2.LamCM
end
end

section -- merged from Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

section general

variable {K : Type} [Field K] [NumberField K]

lemma absNorm_pos' {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (0 : ℝ) < ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  have h1 := FractionalIdeal.absNorm_nonneg I
  have h2 : (FractionalIdeal.absNorm I : ℚ) ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)

lemma log_absNorm_mul {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Real.log ((FractionalIdeal.absNorm (I * J) : ℚ) : ℝ) =
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) + Real.log ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
  rw [map_mul, Rat.cast_mul, Real.log_mul (absNorm_pos' hI).ne' (absNorm_pos' hJ).ne']

lemma mul_le_mul_r {A B : FractionalIdeal (𝓞 K)⁰ K} (h : A ≤ B) (C : FractionalIdeal (𝓞 K)⁰ K) :
    A * C ≤ B * C :=
  mul_le_mul' h le_rfl

lemma spanSingleton_ne_zero' {x : K} (hx : x ≠ 0) : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by
  rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]

lemma le_one_mul {A B : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≤ 1) (hB : B ≤ 1) : A * B ≤ 1 := by
  obtain ⟨A0, rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hA
  obtain ⟨B0, rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hB
  rw [← FractionalIdeal.coeIdeal_mul]
  exact FractionalIdeal.coeIdeal_le_one

lemma valuation_algebraMap_eq (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    v.valuation K (algebraMap (𝓞 K) K r) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r))) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg hr,
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v (by simpa using hr)]

lemma valuation_eq_exp_count (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (𝓞 K)⁰ x
  simp only at hrs
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hs : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hr : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hrs
    exact mul_ne_zero hx hs0 hrs
  have hv : v.valuation K x * v.valuation K (algebraMap (𝓞 K) K s) = v.valuation K (algebraMap (𝓞 K) K r) := by
    rw [← map_mul, hrs]
  have hc : FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) +
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K s)) =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r)) := by
    rw [← FractionalIdeal.count_mul K v (spanSingleton_ne_zero' hx) (spanSingleton_ne_zero' hs0),
      FractionalIdeal.spanSingleton_mul_spanSingleton, hrs]
  rw [valuation_algebraMap_eq v hs, valuation_algebraMap_eq v hr, ← hc, neg_add, WithZero.exp_add] at hv
  exact mul_right_cancel₀ WithZero.exp_ne_zero hv

lemma le_one_of_count_nonneg {J : FractionalIdeal (𝓞 K)⁰ K} (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K v J) : J ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  refine finprod_induction (· ≤ 1) le_rfl (fun a b ha hb => le_one_mul ha hb) (fun v => ?_)
  show (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v J ≤ 1
  rw [← Int.toNat_of_nonneg (h v), zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

end general

theorem degree_algebraic : DegAlg := by
  intro K _ _ L M hL hM
  obtain ⟨hLI, hLn⟩ := hL
  obtain ⟨hMI, hMn⟩ := hM
  refine ⟨⟨mul_ne_zero hLI hMI, fun σ => mul_pos (hLn σ) (hMn σ)⟩, ?_,
    ⟨inv_ne_zero hLI, fun σ => inv_pos.mpr (hLn σ)⟩, ?_,
    fun k => ⟨⟨pow_ne_zero _ hLI, fun σ => pow_pos (hLn σ) k⟩, ?_⟩⟩
  · simp only [MLine.deg, MLine.tensor]
    rw [log_absNorm_mul hLI hMI,
      Finset.sum_congr rfl (fun σ _ => Real.log_mul (hLn σ).ne' (hMn σ).ne'), Finset.sum_add_distrib]
    ring
  · simp only [MLine.deg, MLine.dual]
    rw [map_inv₀, Rat.cast_inv, Real.log_inv,
      Finset.sum_congr rfl (fun σ _ => Real.log_inv (L.n σ)), Finset.sum_neg_distrib]
    ring
  · simp only [MLine.deg, MLine.pow]
    rw [map_pow, Rat.cast_pow, Real.log_pow,
      Finset.sum_congr rfl (fun σ _ => Real.log_pow (L.n σ) k), ← Finset.mul_sum]
    ring

theorem mem_of_loc' : MemOfLoc := by
  intro K _ _ I x hI hloc
  by_cases hx : x = 0
  · rw [hx]; exact FractionalIdeal.zero_mem I
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hge : ∀ p : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K p I ≤ FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
    intro p
    obtain ⟨c, ⟨hc0, hcount⟩, hle⟩ := hloc p
    rw [valuation_eq_exp_count p hx, valuation_eq_exp_count p hc0, WithZero.exp_le_exp, hcount] at hle
    linarith
  set J := FractionalIdeal.spanSingleton (𝓞 K)⁰ x * I⁻¹ with hJdef
  have hJ0 : J ≠ 0 := mul_ne_zero hs (inv_ne_zero hI)
  have hJ : J ≤ 1 := by
    refine le_one_of_count_nonneg hJ0 fun p => ?_
    rw [hJdef, FractionalIdeal.count_mul K p hs (inv_ne_zero hI), FractionalIdeal.count_inv]
    linarith [hge p]
  have hJI : J * I = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
    rw [hJdef, mul_assoc, inv_mul_cancel₀ hI, mul_one]
  rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← hJI]
  calc J * I ≤ 1 * I := mul_le_mul_r hJ I
    _ = I := one_mul I

end Formalism.L2.LamCM
end
end

section -- merged from Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsMonicIrreducibleCardGt
noncomputable section

namespace Formalism.L2.LamCM

open Polynomial IsLocalRing

theorem exists_monic_irreducible_card_gt (k : Type) [Field k] [Finite k] (N : ℕ) :
    ∃ f : k[X], f.Monic ∧ Irreducible f ∧ N < Nat.card (AdjoinRoot f) := by
  classical

  have hcard : ∀ f : k[X], f.Monic → Nat.card (AdjoinRoot f) = Nat.card k ^ f.natDegree := by
    intro f hf
    rw [Nat.card_congr (AdjoinRoot.powerBasis hf.ne_zero).basis.equivFun.toEquiv, Nat.card_fun]
    simp [AdjoinRoot.powerBasis_dim]
  by_contra hcon
  push_neg at hcon
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card

  have hdeg : ∀ α : AlgebraicClosure k, (minpoly k α).natDegree ≤ N := by
    intro α
    have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
    have h1 := hcon _ (minpoly.monic hint) (minpoly.irreducible hint)
    rw [hcard _ (minpoly.monic hint)] at h1
    have h2 : (minpoly k α).natDegree < 2 ^ (minpoly k α).natDegree := Nat.lt_two_pow_self
    have h3 : 2 ^ (minpoly k α).natDegree ≤ Nat.card k ^ (minpoly k α).natDegree := Nat.pow_le_pow_left hq _
    omega
  have hsub : (Set.univ : Set (AlgebraicClosure k)) ⊆ ⋃ c : Fin (N + 1) → k,
      (∑ i : Fin (N + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).rootSet (AlgebraicClosure k) := by
    intro α _
    have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
    refine Set.mem_iUnion.2 ⟨fun i => (minpoly k α).coeff i, ?_⟩
    have hp : (∑ i : Fin (N + 1), Polynomial.C ((minpoly k α).coeff i) * Polynomial.X ^ (i : ℕ)) = minpoly k α := by
      rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C ((minpoly k α).coeff i) * Polynomial.X ^ i)]
      conv_rhs => rw [Polynomial.as_sum_range' (minpoly k α) (N + 1) (by have := hdeg α; omega)]
      simp only [Polynomial.C_mul_X_pow_eq_monomial]
    rw [hp, Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval k α⟩
  have hfin : (Set.univ : Set (AlgebraicClosure k)).Finite :=
    Set.Finite.subset (Set.finite_iUnion fun c => Polynomial.rootSet_finite _ _) hsub
  have : Finite (AlgebraicClosure k) := Set.finite_univ_iff.1 hfin
  exact not_finite (AlgebraicClosure k)

theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ J • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on (p := fun x => b.repr x i ∈ J) hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · simp only [map_add (f := _), Finsupp.add_apply]
      exact J.add_mem hx hy
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem mem_smul_top_self_iff {R : Type} [CommRing R] (J : Ideal R) (y : R) :
    y ∈ J • (⊤ : Submodule R R) ↔ y ∈ J := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

theorem isAdicComplete_of_basis {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (I : Ideal R) (b : Module.Basis ι R M) (h : IsAdicComplete I R) : IsAdicComplete I M := by

  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    simp only [map_sub, Finsupp.sub_apply, SModEq.sub_mem, mem_smul_top_self_iff]
  haveI := h
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    have h0 : ∀ i, b.repr x i = 0 := fun i =>
      IsHausdorff.haus' (I := I) (b.repr x i) fun n => by simpa using (key n x 0).1 (hx n) i
    exact b.repr.injective (Finsupp.ext fun i => by simpa using h0 i)
  have hP : IsPrecomplete I M := by
    refine ⟨fun f hf => ?_⟩
    have hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
      IsPrecomplete.prec' (I := I) (fun n => b.repr (f n) i) fun hmn => (key _ _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    have hr : b.repr (b.equivFun.symm L) i = L i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hr]
    exact hL i n
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

def quotResidueEquiv {V : Type} [CommRing V] [IsLocalRing V] (g : V[X]) :
    AdjoinRoot g ⧸ Ideal.map (algebraMap V (AdjoinRoot g)) (maximalIdeal V) ≃+*
      AdjoinRoot (g.map (residue V)) :=
  AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal V) g

theorem largeResidueExtension : BigResExt := by
  intro V _ _ _ hV _ N
  obtain ⟨gb, hgbm, hgbi, hN⟩ := exists_monic_irreducible_card_gt (ResidueField V) N
  obtain ⟨g, hgmap, hgdeg, hg⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts _).2 (map_surjective (residue V) residue_surjective gb)) hgbm
  subst hgmap
  set W := AdjoinRoot g
  have hirr : Irreducible g := Monic.irreducible_of_irreducible_map (residue V) g hg hgbi
  have hdom : IsDomain W := AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.1 hirr)
  let pb := AdjoinRoot.powerBasis' hg
  have : Module.Finite V W := pb.finite
  have : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have : IsNoetherianRing W := IsNoetherianRing.of_finite V W
  set M0 : Ideal W := Ideal.map (algebraMap V W) (maximalIdeal V) with hM0def
  have : Fact (Irreducible (g.map (residue V))) := ⟨hgbi⟩
  have hM0 : M0.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).2
    (MulEquiv.isField (Field.toIsField (AdjoinRoot (g.map (residue V)))) (quotResidueEquiv g).toMulEquiv)
  have hloc : IsLocalRing W := IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM => by
    letI := hM
    have hc : (M.comap (algebraMap V W)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap V W)
        (fun x => Algebra.IsIntegral.isIntegral x) M
    have h1 := eq_maximalIdeal hc
    have hle : M0 ≤ M := by
      rw [hM0def, ← h1]
      exact Ideal.map_comap_le
    exact (hM0.eq_of_le hM.ne_top hle).symm⟩
  have hmax : maximalIdeal W = M0 := (eq_maximalIdeal hM0).symm
  have hdeg : g.degree ≠ 0 := by
    intro h
    have h0 : g.natDegree = 0 := by rw [natDegree_eq_zero_iff_degree_le_zero, h]
    have := hgbi.natDegree_pos
    omega
  have hinj : Function.Injective (algebraMap V W) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg
  obtain ⟨⟨ϖ, hϖ⟩⟩ := IsPrincipalIdealRing.principal (maximalIdeal V)
  have hprin : (maximalIdeal W).IsPrincipal := by
    refine ⟨⟨algebraMap V W ϖ, ?_⟩⟩
    rw [hmax, hM0def, hϖ, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField W := by
    intro hf
    have h1 : maximalIdeal W = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).1 hf
    rw [hmax, hM0def, Ideal.map_eq_bot_iff_of_injective hinj] at h1
    exact IsDiscreteValuationRing.not_a_field V h1
  have hdvr : IsDiscreteValuationRing W := ((IsDiscreteValuationRing.TFAE W hnf).out 1 5).2 hprin
  have ecard : Nat.card (ResidueField W) = Nat.card (AdjoinRoot (g.map (residue V))) :=
    Nat.card_congr ((Ideal.quotEquivOfEq hmax).trans (quotResidueEquiv g)).toEquiv
  refine ⟨W, inferInstance, hdom, hdvr, inferInstance, ?_, ?_, ?_, hinj, ?_⟩
  · rw [hmax, hM0def, IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_basis _ pb.basis hV
  · exact Nat.finite_of_card_ne_zero (by omega)
  · omega
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : a ∈ maximalIdeal V := (mem_maximalIdeal a).2 hna
    have h2 : algebraMap V W a ∈ maximalIdeal W := by
      rw [hmax]; exact Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).1 h2 ha

end Formalism.L2.LamCM
end
end

section -- merged from Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
noncomputable section

namespace Formalism.L2.LamCM

open MvPolynomial IsLocalRing

section SlopeTestRemainingChoices

theorem exists_eval_ne_zero_of_totalDegree_lt {k σ : Type} [Field k] [Finite σ] (p : MvPolynomial σ k) (hp : p ≠ 0)
    (S : Finset k) (hS : p.totalDegree < S.card) : ∃ x : σ → k, eval x p ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hp (eq_zero_of_eval_zero_at_prod_finset p (fun _ => S)
    (fun i => lt_of_le_of_lt (degreeOf_le_totalDegree p i) hS) (fun x _ => h x))

theorem exists_finset_card_gt {k : Type} (D : ℕ) (h : Infinite k ∨ D < Nat.card k) : ∃ S : Finset k, D < S.card := by
  rcases h with h | h
  · obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq k (D + 1)
    exact ⟨S, by omega⟩
  · have : Finite k := Nat.finite_of_card_ne_zero (by omega)
    have := Fintype.ofFinite k
    refine ⟨Finset.univ, ?_⟩
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]

theorem totalDegree_det_X_le {k σ : Type} [Field k] (n : ℕ) (f : Fin n → Fin n → σ) :
    (Matrix.of fun i j => (X (f i j) : MvPolynomial σ k)).det.totalDegree ≤ n := by
  rw [Matrix.det_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s _ => ?_)
  rw [Units.smul_def]
  refine (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, ((Matrix.of fun i j => (X (f i j) : MvPolynomial σ k)) (s i) i).totalDegree
      ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => by simp [totalDegree_X]
    _ = n := by simp

end SlopeTestRemainingChoices

section Subst

theorem coeff_aeval_scale {K σ : Type} [Field K] [Fintype σ] (c : σ → K) (F : MvPolynomial σ K) (μ : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun w => C (c w) * X w) F) μ = AddMonoidAlgebra.coeff F μ * ∏ w, c w ^ μ w := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial s a =>
    have hs : (s.prod fun i k => (C (c i) * X i) ^ k : MvPolynomial σ K) = C (∏ w, c w ^ s w) * monomial s 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), map_prod,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [mul_pow, map_pow]
    rw [aeval_monomial, hs, algebraMap_eq, ← mul_assoc, ← C_mul, coeff_C_mul,
      coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add p q hp hq => simp only [map_add (f := _), AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_mul]

theorem substGauss : SubstGauss := by
  intro R K _ _ _ B _ m P U c hP hcU μ
  classical
  obtain ⟨P0, hP0⟩ : P ∈ Set.range (map (algebraMap R K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨ν, -, rfl⟩ := mem_coeffs_iff.mp ha
    exact hP ν
  let g0 : FrVar m → MvPolynomial (FrVar m) R := fun v =>
    ∑ j, C (hcU v.1 j v.2.2).choose * X (⟨v.1, (v.2.1, j)⟩ : FrVar m)
  have key : aeval (fun w : FrVar m => C (c w.1 w.2.2) * X w) (substFr U P) = map (algebraMap R K) (bind₁ g0 P0) := by
    rw [map_bind₁, hP0, substFr, aeval_bind₁]
    change bind₁ _ P = bind₁ _ P
    refine congrArg (fun g => bind₁ g P) (funext fun v => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [g0, map_sum, map_mul, aeval_C, aeval_X, map_C, map_X, algebraMap_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hcU v.1 j v.2.2).choose_spec, C_mul]
    ring
  have h := coeff_aeval_scale (fun w : FrVar m => c w.1 w.2.2) (substFr U P) μ
  rw [key, coeff_map] at h
  exact ⟨_, h⟩

end Subst

section Core

theorem coeffIntegralOfUnitEval : LemmaGCore := by
  intro R K _ _ _ _ _ _ B _ m P hcard hval μ0
  classical
  by_contra hμ0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) P.support (fun μ => AddMonoidAlgebra.coeff P μ)
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨n, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hex : ∃ e : ℕ, ∀ μ, algebraMap R K (ϖ ^ e) * AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap R K) := by
    refine ⟨n, fun μ => ?_⟩
    by_cases hμ : μ ∈ P.support
    · obtain ⟨r, hr⟩ := hb μ hμ
      refine ⟨(↑u⁻¹ : R) * r, ?_⟩
      rw [map_mul, hr, Algebra.smul_def, hbu, map_mul, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
        one_mul]
    · rw [notMem_support_iff.mp hμ, mul_zero]
      exact ⟨0, map_zero _⟩
  set e := Nat.find hex with he_def
  have he : ∀ μ, algebraMap R K (ϖ ^ e) * AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap R K) := Nat.find_spec hex
  have he0 : e ≠ 0 := by
    intro h0
    apply hμ0
    simpa [h0] using he μ0
  have hmin : ¬ ∀ μ, algebraMap R K (ϖ ^ (e - 1)) * AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap R K) :=
    Nat.find_min hex (by omega)
  push Not at hmin
  obtain ⟨μ1, hμ1⟩ := hmin

  obtain ⟨Q, hQ⟩ : C (algebraMap R K (ϖ ^ e)) * P ∈ Set.range (map (algebraMap R K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨ν, -, rfl⟩ := mem_coeffs_iff.mp ha
    rw [coeff_C_mul]
    exact he ν
  have hQc : ∀ μ, algebraMap R K (AddMonoidAlgebra.coeff Q μ) = algebraMap R K (ϖ ^ e) * AddMonoidAlgebra.coeff P μ := by
    intro μ
    rw [← coeff_map, hQ, coeff_C_mul]
  have hu1 : IsUnit (AddMonoidAlgebra.coeff Q μ1) := by
    by_contra hnu
    have hmem : AddMonoidAlgebra.coeff Q μ1 ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
    obtain ⟨t, ht⟩ := hmem
    apply hμ1
    refine ⟨t, ?_⟩
    have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ0
    apply mul_left_cancel₀ hϖK
    rw [← map_mul, mul_comm, ht, hQc, ← mul_assoc, ← map_mul, ← pow_succ', Nat.sub_add_cancel (by omega)]

  set Qb : MvPolynomial (FrVar m) (ResidueField R) := map (residue R) Q with hQb
  let Dt : MvPolynomial (FrVar m) (ResidueField R) :=
    ∏ b, (Matrix.of fun (k i : Fin (m b)) => (X (⟨b, (i, k)⟩ : FrVar m) : MvPolynomial (FrVar m) (ResidueField R))).det
  have hDt : ∀ x : FrVar m → ResidueField R,
      eval x Dt = ∏ b, (Matrix.of fun (k i : Fin (m b)) => x ⟨b, (i, k)⟩).det := by
    intro x
    simp only [Dt, map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext k i
    simp [RingHom.mapMatrix_apply]
  have hQb0 : Qb ≠ 0 := by
    intro h0
    have := congrArg (AddMonoidAlgebra.coeff · μ1) h0
    simp only [hQb, coeff_map, AddMonoidAlgebra.coeff_zero] at this
    exact (residue_ne_zero_iff_isUnit _).mpr hu1 this
  have hDt0 : Dt ≠ 0 := by
    intro h0
    have := hDt (fun v => if v.2.1 = v.2.2 then 1 else 0)
    rw [h0, map_zero] at this
    have h1 : ∀ b, (Matrix.of fun (k i : Fin (m b)) =>
        (fun v : FrVar m => if v.2.1 = v.2.2 then (1 : ResidueField R) else 0) ⟨b, (i, k)⟩) = 1 := by
      intro b
      ext k i
      simp [Matrix.one_apply, eq_comm]
    simp only [h1, Matrix.det_one, Finset.prod_const_one] at this
    exact zero_ne_one this
  have hdeg : (Qb * Dt).totalDegree ≤ P.totalDegree + ∑ b, m b := by
    refine (totalDegree_mul _ _).trans (add_le_add ?_ ?_)
    · have hsub : Qb.support ⊆ P.support := by
        intro μ hμ
        rw [mem_support_iff] at hμ ⊢
        intro hP0
        apply hμ
        rw [hQb, coeff_map]
        have : AddMonoidAlgebra.coeff Q μ = 0 := hinj (by rw [hQc, hP0, mul_zero, map_zero])
        rw [this, map_zero]
      unfold totalDegree
      exact Finset.sup_mono hsub
    · refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      exact totalDegree_det_X_le (m b) _
  obtain ⟨S, hS⟩ := exists_finset_card_gt (k := ResidueField R) _ hcard
  obtain ⟨x, hx⟩ := exists_eval_ne_zero_of_totalDegree_lt (Qb * Dt) (mul_ne_zero hQb0 hDt0) S (by omega)
  rw [map_mul, hDt, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hx
  obtain ⟨hxQ, hxD⟩ := hx

  choose y hy using fun v => residue_surjective (R := R) (x v)
  let Xf : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R := fun b => Matrix.of fun k i => y ⟨b, (i, k)⟩
  have hdet : ∀ b, IsUnit (Xf b).det := by
    intro b
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det]
    convert hxD b (Finset.mem_univ _) using 2
    ext k i
    simp [Xf, RingHom.mapMatrix_apply, hy]
  have hyx : (residue R) ∘ y = x := funext hy
  have hQy : IsUnit (eval y Q) := by
    rw [← residue_ne_zero_iff_isUnit, map_eval, hyx]
    exact hxQ
  obtain ⟨r, hr⟩ := hval Xf hdet
  have hev : evalFr P (fun b => (Xf b).map (algebraMap R K)) = eval (algebraMap R K ∘ y) P := rfl
  have hyQ : eval y Q = ϖ ^ e * r := by
    apply hinj
    rw [map_eval, hQ, map_mul, eval_C, map_mul, hr, hev]
  rw [hyQ] at hQy
  exact hϖ.not_isUnit ((isUnit_pow_iff he0).mp (isUnit_of_mul_isUnit_left hQy))

end Core

section Descent

theorem LemmaG_of : BigResExt → LemmaG := by
  intro hB V K _ _ _ _ _ _ B _ m P hc hfin hW μ
  classical
  obtain ⟨W, _, _, _, _, hcW, hfinW, hN, hinj, hloc⟩ := hB V hc hfin (P.totalDegree + ∑ b, m b)
  have hg : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W (FractionRing W)).comp hinj
  let f : K →+* FractionRing W := IsFractionRing.lift hg
  have hf : ∀ a : V, f (algebraMap V K a) = algebraMap W (FractionRing W) (algebraMap V W a) :=
    fun a => IsFractionRing.lift_algebraMap hg a
  have hdeg : (map f P).totalDegree ≤ P.totalDegree := by
    unfold totalDegree
    exact Finset.sup_mono (support_map_subset f P)
  have hcoef := coeffIntegralOfUnitEval W (FractionRing W) B m (map f P) (Or.inr (by omega))
    (hW W (FractionRing W) f hcW hfinW hloc hf) μ
  rw [coeff_map] at hcoef
  obtain ⟨w, hw⟩ := hcoef
  set x := AddMonoidAlgebra.coeff P μ
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [hx0, map_zero]⟩
  rcases ValuationRing.isInteger_or_isInteger V x with ⟨r, hr⟩ | ⟨y, hy⟩
  · exact ⟨r, hr⟩
  · by_cases hyu : IsUnit y
    · refine ⟨↑hyu.unit⁻¹, ?_⟩
      have h1 : algebraMap V K y * algebraMap V K ↑hyu.unit⁻¹ = 1 := by
        rw [← map_mul, ← map_one (algebraMap V K)]
        congr 1
        exact hyu.mul_val_inv
      rw [hy] at h1
      rw [← inv_inv x]
      exact (eq_inv_of_mul_eq_one_right h1)
    · exfalso
      apply hyu
      apply isUnit_of_map_unit (algebraMap V W) y
      have h1 : algebraMap W (FractionRing W) (w * algebraMap V W y) = algebraMap W (FractionRing W) 1 := by
        rw [map_mul, hw, ← hf, hy, ← map_mul, mul_inv_cancel₀ hx0, map_one, map_one]
      have h2 := IsFractionRing.injective W (FractionRing W) h1
      exact ⟨⟨algebraMap V W y, w, by rw [mul_comm]; exact h2, h2⟩, rfl⟩

end Descent

end Formalism.L2.LamCM
end
end
