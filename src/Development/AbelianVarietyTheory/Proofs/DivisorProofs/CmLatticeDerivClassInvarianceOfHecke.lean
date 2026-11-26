module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePrincMulUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndLatticeTraceIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnWirtWordMulExpCompStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.CMTypeRealEmb

theorem comp_isReal {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
  rw [ComplexEmbedding.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply]
  rw [← IsCMField.complexEmbedding_complexConj]
  congr 1
  exact IsCMField.complexConj_apply_eq_self E a

theorem exists_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E),
      φ i (a : E) = ((e i a : ℝ) : ℂ) := by
  set F := maximalRealSubfield E
  let ψ : I → F →+* ℂ := fun i => (φ i).comp (algebraMap F E)
  have hre : ∀ i, ComplexEmbedding.IsReal (ψ i) := fun i => comp_isReal (φ i)
  let e : I → Emb F := fun i => (hre i).embedding
  have he : ∀ i a, ((e i a : ℝ) : ℂ) = φ i (a : E) := fun i a =>
    (hre i).coe_embedding_apply a
  have hplace : ∀ i, (InfinitePlace.mk (φ i)).comap (algebraMap F E) = InfinitePlace.mk (ψ i) :=
    fun i => InfinitePlace.comap_mk _ _
  refine ⟨Equiv.ofBijective e ⟨?_, ?_⟩, fun i a => (he i a).symm⟩
  · intro i j hij
    have hψ : ψ i = ψ j := by
      ext a
      show φ i (a : E) = φ j (a : E)
      rw [← he, ← he, hij]
    have h1 : InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j) := by
      apply (IsCMField.equivInfinitePlace E).injective
      simp only [IsCMField.equivInfinitePlace_apply]
      rw [hplace, hplace, hψ]
    rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
    · obtain ⟨k, _, hk⟩ := hφ (φ j)
      exact (hk i (Or.inl h.symm)).trans (hk j (Or.inl rfl)).symm
    · obtain ⟨k, _, hk⟩ := hφ (φ j)
      exact (hk i (Or.inr h.symm)).trans (hk j (Or.inl rfl)).symm
  · intro f
    let fc : F →+* ℂ := Complex.ofRealHom.comp f
    have hfc : ComplexEmbedding.IsReal fc := by
      rw [ComplexEmbedding.isReal_iff]
      ext a
      simp [fc]
    let w : InfinitePlace E := (IsCMField.equivInfinitePlace E).symm (InfinitePlace.mk fc)
    obtain ⟨i, hi, _⟩ := hφ w.embedding
    have hmk : InfinitePlace.mk (φ i) = w := by
      rcases hi with h | h
      · rw [← h, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
    have h2 : InfinitePlace.mk (ψ i) = InfinitePlace.mk fc := by
      rw [← hplace, hmk]
      have := (IsCMField.equivInfinitePlace E).apply_symm_apply (InfinitePlace.mk fc)
      rw [IsCMField.equivInfinitePlace_apply] at this
      exact this
    have h3 : ψ i = fc := by
      rcases InfinitePlace.mk_eq_iff.mp h2 with h | h
      · exact h
      · rw [← h]; exact ((ComplexEmbedding.isReal_iff).mp (hre i)).symm
    refine ⟨i, ?_⟩
    ext a
    apply Complex.ofReal_injective
    rw [he]
    show ψ i a = fc a
    rw [h3]

end GlobalTheory.CMTypeRealEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddingsMaxRealSubfieldStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_cmType_realEmbeddings_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CMTypeRealEmb.exists_equiv | exact GlobalTheory.CMTypeRealEmb.exists_equiv | (intros; apply GlobalTheory.CMTypeRealEmb.exists_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTwoDerivativeEisensteinTermUniformBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTwoDerivativeEisensteinTermUniformBound
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoSum.Bound

theorem eTerm_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (m : I → ℕ) (σ : ℂ) (r : ℝ), 0 ≤ σ.re → r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) →
      ∀ x : E, x ≠ 0 → ‖eTerm φ m σ z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) := by
  intro E _ _ _ I _ φ hφ m σ r hσ hr
  have hr' : 0 < 1 - r := by linarith
  refine ⟨∏ i, (‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * ((1 - r)⁻¹) ^ (2 + m i) *
    (1 - r) ^ (-2 * σ.re)), fun z hz x hx => ?_⟩
  have hN : |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) = ∏ i, (‖φ i x‖ ^ 2) ^ (-(1 + σ.re)) := by
    rw [← TermUnit.prod_norm_sq hφ x, Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  rw [hN, ← Finset.prod_mul_distrib, eTerm, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  have hp : 0 < ‖φ i x‖ := norm_pos_iff.2 ((map_ne_zero (φ i)).2 hx)
  have hl := GlobalTheory.DeformedSum.Bound.defCoord_lower φ z x i (hz i)
  have hd : 0 < ‖defCoord φ z x i‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos hd]
  set a := ‖φ i x‖ with ha
  set d := ‖defCoord φ z x i‖ with hdd
  have h1 : a ^ m i * d⁻¹ ^ (2 + m i) ≤ (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 := by
    have hinv : d⁻¹ ≤ (1 - r)⁻¹ * a⁻¹ := by
      rw [← mul_inv]; exact inv_anti₀ (mul_pos hr' hp) hl
    calc a ^ m i * d⁻¹ ^ (2 + m i) ≤ a ^ m i * ((1 - r)⁻¹ * a⁻¹) ^ (2 + m i) := by gcongr
      _ = (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 * (a ^ m i * a⁻¹ ^ m i) := by rw [mul_pow, pow_add a⁻¹]; ring
      _ = (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 := by rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow, mul_one]
  have h2 : d ^ ((-2 * σ).re) ≤ (1 - r) ^ (-2 * σ.re) * a ^ (-2 * σ.re) := by
    rw [show (-2 * σ).re = -2 * σ.re by simp, ← Real.mul_rpow hr'.le hp.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hr' hp) hl (by linarith)
  have h3 : (a ^ 2) ^ (-(1 + σ.re)) = a⁻¹ ^ 2 * a ^ (-2 * σ.re) := by
    calc (a ^ 2) ^ (-(1 + σ.re)) = a ^ ((2 : ℝ) * (-(1 + σ.re))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num
      _ = a ^ (-(2 : ℝ)) * a ^ (-2 * σ.re) := by rw [← Real.rpow_add hp]; ring_nf
      _ = a⁻¹ ^ 2 * a ^ (-2 * σ.re) := by rw [Real.rpow_neg hp.le, inv_pow]; norm_num
  rw [h3]
  calc ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * a ^ m i * d⁻¹ ^ (2 + m i) * d ^ ((-2 * σ).re)
      = ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * (a ^ m i * d⁻¹ ^ (2 + m i)) * d ^ ((-2 * σ).re) := by
        ring
    _ ≤ ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * ((1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2) *
        ((1 - r) ^ (-2 * σ.re) * a ^ (-2 * σ.re)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (by positivity) (by positivity)
    _ = _ := by ring

end GlobalTheory.WeightTwoSum.Bound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTwoDerivativeEisensteinTermUniformBoundStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightTwoDerivativeEisensteinTerm_uniform_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (m : I → ℕ) (σ : ℂ) (r : ℝ), 0 ≤ σ.re → r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 → ‖eTerm φ m σ z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) := by
  first | exact @GlobalTheory.WeightTwoSum.Bound.eTerm_bound | exact GlobalTheory.WeightTwoSum.Bound.eTerm_bound | (intros; apply GlobalTheory.WeightTwoSum.Bound.eTerm_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesDifferentiable
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DeformedSum.Series

theorem series_differentiable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ), IsCMType φ → ∀ s : ℕ, 2 ≤ s → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → Summable (fun q : modUnits (lattice c y) => dTerm φ (2 * s) m z q.1.out) ∧ DifferentiableAt ℂ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out) z ∧ ∀ i : I, HasLineDerivAt ℂ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out) (∑' q : modUnits (lattice c y), dTerm φ (2 * s) (m + Pi.single i 1) z q.1.out) z (Pi.single i 1) := by
  intro E _ _ _ I _ _ φ hφ s hs c y hc m z hz

  have hz1 : ‖z‖ < 1 := by
    rcases isEmpty_or_nonempty I with hI | hI
    · simp [Subsingleton.elim z 0]
    · exact (pi_norm_lt_iff one_pos).2 hz
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  set U : Set (I → ℂ) := Metric.ball 0 r with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUc : IsPreconnected U := (convex_ball (0 : I → ℂ) r).isPreconnected
  have hzU : z ∈ U := by simpa [hU] using hzr
  have hUle : ∀ w ∈ U, ∀ i, ‖w i‖ ≤ r := fun w hw i =>
    (norm_le_pi_norm w i).trans (show ‖w‖ < r by simpa [hU] using hw).le
  have hUpd : ∀ w ∈ U, w ∈ polydisc I := fun w hw i => lt_of_le_of_lt (hUle w hw i) hr1

  set N : modUnits (lattice c y) → ℝ := fun q => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-(s : ℝ)) with hN
  have hNs : Summable N := GlobalTheory.CMVal.Conv.summable_norm_rpow E c y (s : ℝ) hc (by exact_mod_cast (by omega : 1 < s))
  have hne : ∀ q : modUnits (lattice c y), q.1.out ≠ 0 := fun q => (out_mem_lattice q).2
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform E I φ hφ s m r hr1
  have hsum : ∀ w ∈ U, Summable (fun q : modUnits (lattice c y) => dTerm φ (2 * s) m w q.1.out) := fun w hw =>
    Summable.of_norm_bounded (hNs.mul_left C0) fun q => hC0 w (hUle w hw) _ (hne q)
  choose C hC using fun j : I => GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform E I φ hφ s (m + Pi.single j 1) r hr1
  set f' : modUnits (lattice c y) → (I → ℂ) → ((I → ℂ) →L[ℂ] ℂ) := fun q w =>
    ∑ j, dTerm φ (2 * s) (m + Pi.single j 1) w q.1.out • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j) with hf'
  set u : modUnits (lattice c y) → ℝ := fun q => ∑ j, C j * N q * ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j‖ with hu
  have hus : Summable u := summable_sum fun j _ => ((hNs.mul_left (C j)).mul_right _)
  have hder : ∀ q w, w ∈ U → HasFDerivAt (fun w : I → ℂ => dTerm φ (2 * s) m w q.1.out) (f' q w) w :=
    fun q w hw => GlobalTheory.T.hasFDerivAt_deformedProductDerivativeTerm E I φ (2 * s) m q.1.out (hne q) w (hUpd w hw)
  have hbd : ∀ q w, w ∈ U → ‖f' q w‖ ≤ u q := by
    intro q w hw
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC j w (hUle w hw) _ (hne q)) (norm_nonneg _)
  have hF : HasFDerivAt (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out)
      (∑' q, f' q z) z :=
    hasFDerivAt_tsum_of_isPreconnected hus hUo hUc hder hbd hzU (hsum z hzU) hzU
  refine ⟨hsum z hzU, hF.differentiableAt, fun i => ?_⟩
  have hL := hF.hasLineDerivAt (Pi.single i 1)
  have hcs : Summable (fun q => f' q z) := Summable.of_norm_bounded hus fun q => hbd q z hzU
  have hev : (∑' q, f' q z) (Pi.single i 1) = ∑' q : modUnits (lattice c y), dTerm φ (2 * s) (m + Pi.single i 1) z q.1.out := by
    have hm := (ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ) : I → ℂ)).map_tsum hcs
    simp only [ContinuousLinearMap.apply_apply] at hm
    rw [hm]
    refine tsum_congr fun q => ?_
    simp [hf', ContinuousLinearMap.sum_apply, Pi.single_apply]
  rwa [hev] at hL

end GlobalTheory.DeformedSum.Series
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFormExistsUnique
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

noncomputable section

namespace GlobalTheory.DualFormExists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def riemannBil (ξ : E) : LinearMap.BilinForm ℚ E :=
  LinearMap.mk₂ ℚ (riemann ξ)
    (fun x x' y => by simp [riemann, mul_add, add_mul, map_add (f := _)])
    (fun q x y => by
      simp only [riemann, smul_eq_mul]
      rw [show ξ * (q • x) * IsCMField.complexConj E y = q • (ξ * x * IsCMField.complexConj E y) by
        rw [mul_smul_comm, smul_mul_assoc], map_smul, smul_eq_mul])
    (fun x y y' => by simp [riemann, mul_add, map_add (f := _)])
    (fun q x y => by
      have h : IsCMField.complexConj E (q • y) = q • IsCMField.complexConj E y := map_rat_smul _ q y
      simp only [riemann, smul_eq_mul, h]
      rw [mul_smul_comm, map_smul, smul_eq_mul])

theorem riemannBil_apply (ξ x y : E) : riemannBil ξ x y = riemann ξ x y := rfl

theorem riemann_left_nondeg (ξ : E) (hξ : ξ ≠ 0) (x : E) (hx : ∀ y, riemann ξ x y = 0) : x = 0 := by
  by_contra h0
  have h1 := hx (IsCMField.complexConj E (ξ * x)⁻¹)
  rw [riemann, IsCMField.complexConj_apply_apply,
    mul_inv_cancel₀ (mul_ne_zero hξ h0)] at h1
  rw [show (1 : E) = algebraMap ℚ E 1 by simp, Algebra.trace_algebraMap] at h1
  have := Module.finrank_pos (R := ℚ) (M := E)
  simp at h1
  omega

def riemannClL (ξ : E) : E →ₗ[ℚ] Coh E where
  toFun := riemannCl ξ
  map_add' x x' := by
    ext y; simp [riemannCl, riemann, mul_add, add_mul, map_add (f := _)]
  map_smul' q x := by
    ext y
    show ((riemann ξ (q • x) y : ℚ) : ℂ) = q • ((riemann ξ x y : ℚ) : ℂ)
    rw [← riemannBil_apply, LinearMap.map_smul₂, riemannBil_apply, smul_eq_mul, Rat.cast_mul, Rat.smul_def]

theorem riemannClL_apply (ξ x : E) : riemannClL ξ x = riemannCl ξ x := rfl

theorem riemannCl_apply (ξ x y : E) : riemannCl ξ x y = (riemann ξ x y : ℂ) := rfl

def gram (ξ : E) : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℚ :=
  LinearMap.toMatrix₂ (Module.finBasis ℚ E) (Module.finBasis ℚ E) (riemannBil ξ)

theorem gram_apply (ξ : E) (i j) : gram ξ i j = riemann ξ (Module.finBasis ℚ E i) (Module.finBasis ℚ E j) := by
  simp [gram, LinearMap.toMatrix₂_apply, riemannBil_apply]

theorem gram_det_ne_zero (ξ : E) (hξ : ξ ≠ 0) : (gram ξ).det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  apply hv
  set b := Module.finBasis ℚ E
  have hx : (∑ i, v i • b i) = 0 := by
    apply riemann_left_nondeg ξ hξ
    intro y
    rw [← riemannBil_apply, ← b.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j _
    have := congrFun hv0 j
    simp only [Matrix.vecMul, dotProduct, gram_apply, Pi.zero_apply] at this
    exact mul_eq_zero_of_right _ this
  have := b.linearIndependent
  exact Fintype.linearIndependent_iff.mp this v hx |> funext

end GlobalTheory.DualFormExists

namespace GlobalTheory.DualFormExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_coh : Module.finrank ℂ (Coh E) = Module.finrank ℚ E := by
  rw [← ((Module.finBasis ℚ E).constr ℂ).finrank_eq, Module.finrank_fin_fun]

theorem riemannCl_linInd (ξ : E) (hξ : ξ ≠ 0) :
    LinearIndependent ℂ (fun i => riemannCl ξ (Module.finBasis ℚ E i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set Gc := (gram ξ).map (Rat.castHom ℂ)
  have hdet : Gc.det ≠ 0 := by
    rw [show Gc = (Rat.castHom ℂ).mapMatrix (gram ξ) from rfl, ← RingHom.map_det]
    simpa using gram_det_ne_zero ξ hξ
  have hv : Matrix.vecMul c Gc = 0 := by
    funext j
    have := LinearMap.congr_fun hc (Module.finBasis ℚ E j)
    simpa [Matrix.vecMul, dotProduct, Gc, gram_apply, riemannCl_apply] using this
  by_contra h
  push_neg at h
  obtain ⟨i, hi⟩ := h
  exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, fun h0 => hi (by simp [h0]), hv⟩)

def clBasis (ξ : E) (hξ : ξ ≠ 0) : Module.Basis (Fin (Module.finrank ℚ E)) ℂ (Coh E) :=
  haveI : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  basisOfLinearIndependentOfCardEqFinrank (riemannCl_linInd ξ hξ) (by simp [finrank_coh])

theorem clBasis_apply (ξ : E) (hξ : ξ ≠ 0) (i) : clBasis ξ hξ i = riemannCl ξ (Module.finBasis ℚ E i) := by
  simp [clBasis]

theorem clBasis_repr (ξ : E) (hξ : ξ ≠ 0) (x : E) (i) :
    (clBasis ξ hξ).repr (riemannCl ξ x) i = (((Module.finBasis ℚ E).repr x i : ℚ) : ℂ) := by
  have h : riemannCl ξ x = (clBasis ξ hξ).equivFun.symm (fun i => (((Module.finBasis ℚ E).repr x i : ℚ) : ℂ)) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← riemannClL_apply, ← (Module.finBasis ℚ E).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, clBasis_apply, riemannClL_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext y
    simp [Rat.smul_def]
  rw [h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.DualFormExists

namespace GlobalTheory.DualFormExists

theorem dualForm_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ : E), ξ ≠ 0 →
    ∃! B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B := by
  intro E _ _ _ ξ hξ
  set b := Module.finBasis ℚ E
  set cb := clBasis ξ hξ
  set Gc : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℂ := fun i j => ((gram ξ i j : ℚ) : ℂ)
  refine ⟨Matrix.toLinearMap₂ cb cb Gc, ?_, ?_⟩
  · intro x y
    rw [Matrix.toLinearMap₂_apply]
    simp only [cb, clBasis_repr]
    rw [← riemannBil_apply, ← Matrix.toLinearMap₂_toMatrix₂ b b (riemannBil ξ), Matrix.toLinearMap₂_apply]
    push_cast
    simp [Gc, gram, b]
  · intro B' hB'
    apply LinearMap.ext_basis cb cb
    intro i j
    rw [Matrix.toLinearMap₂_apply_basis, clBasis_apply, clBasis_apply, hB']
    simp [Gc, gram_apply, b]

end GlobalTheory.DualFormExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannClEqSum
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualFormValues

variable {E : Type} [Field E] [NumberField E]

theorem trace_eq_sum (x : E) : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ : E →+* ℂ => σ x) _ (fun σ => rfl)).symm

theorem coeff_eq_zero (c : (E →+* ℂ) → (E →+* ℂ) → ℂ)
    (h : ∀ x y : E, ∑ τ₁, ∑ τ₂, c τ₁ τ₂ * (τ₁ x * τ₂ y) = 0) (τ₁ τ₂ : E →+* ℂ) : c τ₁ τ₂ = 0 := by
  have hli : LinearIndependent ℂ (fun (τ : E →+* ℂ) => (fun x => τ x : E → ℂ)) := by
    have h0 := linearIndependent_monoidHom E ℂ
    have hinj : Function.Injective (fun τ : E →+* ℂ => (τ : E →* ℂ)) := by
      intro a b hab
      ext x
      exact DFunLike.congr_fun hab x
    exact h0.comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have h1 : ∀ y : E, ∀ a : E →+* ℂ, ∑ b, c a b * b y = 0 := by
    intro y
    refine hli (fun a => ∑ b, c a b * b y) ?_
    funext x
    have := h x y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.sum_mul]
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  exact hli (c τ₁) (by
    funext y
    simpa [mul_comm] using h1 y τ₁) τ₂

variable [IsCMField E]

theorem riemannCl_eq_sum (ξ x : E) :
    riemannCl ξ x = ∑ σ : E →+* ℂ, σ (ξ * x) • (ComplexEmbedding.conjugate σ).toRatAlgHom.toLinearMap := by
  ext y
  simp only [riemannCl, riemann, LinearMap.coe_mk, AddHom.coe_mk, trace_eq_sum, LinearMap.sum_apply,
    LinearMap.smul_apply, map_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]

theorem dualForm_values (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ : E) (hξ : ξ ≠ 0)
    (_hc : IsCMField.complexConj E ξ = -ξ) (B : LinearMap.BilinForm ℂ (Coh E)) (hB : IsDualForm ξ B)
    (ρ ρ' : E →+* ℂ) :
    (ρ' = ComplexEmbedding.conjugate ρ →
      B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = (ρ ξ)⁻¹) ∧
    (ρ' ≠ ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = 0) := by
  classical
  let b : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun a a' => B a.toRatAlgHom.toLinearMap a'.toRatAlgHom.toLinearMap
  let c : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun τ₁ τ₂ =>
    τ₁ ξ * τ₂ ξ * b (ComplexEmbedding.conjugate τ₁) (ComplexEmbedding.conjugate τ₂) -
      if τ₂ = ComplexEmbedding.conjugate τ₁ then τ₁ ξ else 0
  have hz : ∀ τ : E →+* ℂ, τ ξ ≠ 0 := fun τ => by simpa using hξ
  have hsum : ∀ x y : E, ∑ τ₁, ∑ τ₂, c τ₁ τ₂ * (τ₁ x * τ₂ y) = 0 := by
    intro x y
    have h1 := hB x y
    rw [riemannCl_eq_sum, riemannCl_eq_sum] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : ((riemann ξ x y : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ ξ * σ x * ComplexEmbedding.conjugate σ y := by
      simp only [riemann, trace_eq_sum, map_mul]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    rw [h2] at h1
    simp only [c, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [sub_eq_zero]
    have h3 : ∑ τ₁, ∑ τ₂, τ₁ ξ * τ₂ ξ * b (ComplexEmbedding.conjugate τ₁) (ComplexEmbedding.conjugate τ₂) *
        (τ₁ x * τ₂ y) = ∑ σ : E →+* ℂ, σ ξ * σ x * ComplexEmbedding.conjugate σ y := by
      rw [← h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ₁ _ => ?_
      simp only [b, map_mul]
      ring
    rw [h3]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
    intro τ
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hc := coeff_eq_zero c hsum (ComplexEmbedding.conjugate ρ) (ComplexEmbedding.conjugate ρ')
  simp only [c, b, hcc] at hc
  constructor
  · rintro rfl
    rw [hcc, if_pos rfl] at hc
    have h0 := hz (ComplexEmbedding.conjugate ρ)
    have h4 : ComplexEmbedding.conjugate ρ ξ *
        (ρ ξ * B ρ.toRatAlgHom.toLinearMap (ComplexEmbedding.conjugate ρ).toRatAlgHom.toLinearMap - 1) = 0 := by
      linear_combination hc
    have h5 := (mul_eq_zero.1 h4).resolve_left h0
    exact eq_inv_of_mul_eq_one_right (sub_eq_zero.1 h5)
  · intro hne
    have hne' : ComplexEmbedding.conjugate ρ' ≠ ρ := fun h => hne (by rw [← h, hcc])
    rw [if_neg hne', sub_zero] at hc
    exact (mul_eq_zero.1 hc).resolve_left (mul_ne_zero (hz _) (hz _))

end GlobalTheory.DualFormValues
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivFormulaOfSeries
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DerivAtOrigin

theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  have : polydisc I = ⋂ i : I, {z : I → ℂ | ‖z i‖ < 1} := by
    ext z; simp [polydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

theorem zero_mem_polydisc (I : Type) : (0 : I → ℂ) ∈ polydisc I := by
  intro i; simp

theorem count_cons_eq {I : Type} [DecidableEq I] (i : I) (l : List I) :
    (fun j => (i :: l).count j) = (fun j => l.count j) + Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [List.count_cons]
  · simp [List.count_cons, Pi.single_apply, h, Ne.symm h]

theorem risingFactor_ne_zero {I : Type} [Fintype I] (k : ℕ) (hk : 1 ≤ k) (κ : I → ℕ) :
    risingFactor k κ ≠ 0 := by
  unfold risingFactor
  rw [Finset.prod_ne_zero_iff]
  intro i _
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro j _
  have : ((k : ℂ) + j) = ((k + j : ℕ) : ℂ) := by push_cast; ring
  rw [this]
  exact_mod_cast (by omega : k + j ≠ 0)

theorem term_origin {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (x : E) :
    term φ k κ 0 x = ∏ i, ((φ i x)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i x)) ^ κ i) := by
  unfold term
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

theorem derivFormula_of_series : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (L : Set E), 4 ≤ k → (∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → Summable (fun q : modUnits L => dTerm φ k m z q.1.out) ∧ DifferentiableAt ℂ (fun w : I → ℂ => ∑' q : modUnits L, dTerm φ k m w q.1.out) z ∧ ∀ i : I, HasLineDerivAt ℂ (fun w : I → ℂ => ∑' q : modUnits L, dTerm φ k m w q.1.out) (∑' q : modUnits L, dTerm φ k (m + Pi.single i 1) z q.1.out) z (Pi.single i 1)) → DerivFormula φ k L := by
  intro E _ _ I _ _ φ k L hk H
  set T : (I → ℕ) → (I → ℂ) → ℂ := fun m w => ∑' q : modUnits L, dTerm φ k m w q.1.out with hT
  have hT0 : ∀ z ∈ polydisc I, HasSum (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) (T 0 z) := by
    intro z hz
    have e : (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) = fun q : modUnits L => dTerm φ k 0 z q.1.out :=
      funext fun q => (dTerm_zero φ k z q.1.out).symm
    rw [e]
    exact (H 0 z hz).1.hasSum

  have hagree : ∀ g, IsDefSum φ k L g → ∀ z ∈ polydisc I, g z = (cWt E k : ℂ) * T 0 z := by
    intro g hg z hz
    obtain ⟨G, hG, hgz⟩ := hg z hz
    rw [hgz, (hG.1 (by omega)).unique (hT0 z hz)]

  have hiter : ∀ g, IsDefSum φ k L g → ∀ l : List I, ∀ z ∈ polydisc I,
      iterD l g z = (cWt E k : ℂ) * T (fun j => l.count j) z := by
    intro g hg l
    induction l with
    | nil =>
      intro z hz
      have : (fun j : I => ([] : List I).count j) = 0 := by funext j; simp
      rw [this]
      exact hagree g hg z hz
    | cons i l ih =>
      intro z hz
      have hev : iterD l g =ᶠ[nhds z] fun w => (cWt E k : ℂ) * T (fun j => l.count j) w := by
        filter_upwards [(isOpen_polydisc I).mem_nhds hz] with w hw using ih w hw
      have hd : HasLineDerivAt ℂ (fun w => (cWt E k : ℂ) * T (fun j => l.count j) w)
          ((cWt E k : ℂ) * T ((fun j => l.count j) + Pi.single i 1) z) z (Pi.single i 1) := by
        have h1 := (H (fun j => l.count j) z hz).2.2 i
        unfold HasLineDerivAt at h1 ⊢
        exact h1.const_mul _
      have h2 : iterD (i :: l) g z = lineDeriv ℂ (iterD l g) z (Pi.single i 1) := rfl
      rw [h2, hev.lineDeriv_eq, hd.lineDeriv, count_cons_eq]
  refine ⟨⟨fun z => (cWt E k : ℂ) * T 0 z, fun z hz => ⟨T 0 z, ⟨fun _ => hT0 z hz, fun h => by omega⟩, rfl⟩⟩, ?_⟩
  intro g hg
  refine ⟨?_, ?_⟩
  · intro z hz
    have hev : g =ᶠ[nhds z] fun w => (cWt E k : ℂ) * T 0 w := by
      filter_upwards [(isOpen_polydisc I).mem_nhds hz] with w hw using hagree g hg w hw
    have hda : DifferentiableAt ℂ (fun w => (cWt E k : ℂ) * T 0 w) z :=
      ((H 0 z hz).2.1).const_mul _
    exact (hda.congr_of_eventuallyEq hev).differentiableWithinAt
  · intro κ l hl
    have hκ : (fun j => l.count j) = κ := funext hl
    have h0 : iterD l g 0 = (cWt E k : ℂ) * T κ 0 := by
      rw [hiter g hg l 0 (zero_mem_polydisc I), hκ]
    have hTκ : T κ 0 = risingFactor k κ *
        ∑' q : modUnits L, ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i) := by
      simp only [hT, dTerm_origin]
      exact tsum_mul_left
    refine ⟨?_, ?_⟩
    · intro S hS
      have hS0 := hS.2 0 (by
        have : (4 : ℝ) ≤ k := by exact_mod_cast hk
        simp; linarith)
      simp only [term_origin] at hS0
      rw [h0, hTκ, hS0.tsum_eq]; ring
    · intro _
      have hsum : Summable (fun q : modUnits L =>
          ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i)) := by
        have h := (H κ 0 (zero_mem_polydisc I)).1
        simp only [dTerm_origin] at h
        exact (summable_mul_left_iff (risingFactor_ne_zero k (by omega) κ)).1 h
      refine ⟨_, hsum.hasSum, ?_⟩
      rw [h0, hTκ]; ring

end GlobalTheory.DerivAtOrigin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFormValueOfValues
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualFormOrtho

theorem bilin_eq_zero_of_span {V : Type} [AddCommGroup V] [Module ℂ V] (B : LinearMap.BilinForm ℂ V) {s t : Set V}
    (h : ∀ u ∈ s, ∀ v ∈ t, B u v = 0) {a b : V} (ha : a ∈ Submodule.span ℂ s) (hb : b ∈ Submodule.span ℂ t) : B a b = 0 := by
  induction ha using Submodule.span_induction with
  | mem u hu =>
    induction hb using Submodule.span_induction with
    | mem v hv => exact h u hu v hv
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem dualFormValue_of_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → (∀ ξ : E, ξ ≠ 0 → ∃! B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B) →
    (∀ ξ : E, ξ ≠ 0 → IsCMField.complexConj E ξ = -ξ → ∀ B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B →
      ∀ ρ ρ' : E →+* ℂ, (ρ' = ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = (ρ ξ)⁻¹) ∧
        (ρ' ≠ ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = 0)) →
    DualFormValue φ := by
  intro E _ _ _ I _ _ φ hφ hex hval ξ hξ hc
  refine ⟨hex ξ hξ, fun B hB ε => ?_⟩
  have hv := hval ξ hξ hc B hB
  have key : ∀ i j, i ≠ j → ∀ σ : E →+* ℂ, (σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)) →
      (σ = φ j ∨ σ = ComplexEmbedding.conjugate (φ j)) → False :=
    fun i j hij σ h1 h2 => hij ((hφ σ).unique h1 h2)
  have gen : ∀ i j, i ≠ j → ∀ u ∈ ({eCl φ i, fCl φ i} : Set (Coh E)), ∀ v ∈ ({eCl φ j, fCl φ j} : Set (Coh E)), B u v = 0 := by
    rintro i j hij u (rfl | rfl) v (rfl | rfl)
    · exact (hv (φ i) (φ j)).2 fun h => key i j hij (φ j) (Or.inr h) (Or.inl rfl)
    · exact (hv (φ i) (ComplexEmbedding.conjugate (φ j))).2 fun h =>
        key i j hij (ComplexEmbedding.conjugate (φ j)) (Or.inr h) (Or.inr rfl)
    · refine (hv (ComplexEmbedding.conjugate (φ i)) (φ j)).2 fun h => ?_
      rw [ComplexEmbedding.involutive_conjugate E (φ i)] at h
      exact key i j hij (φ j) (Or.inl h) (Or.inl rfl)
    · refine (hv (ComplexEmbedding.conjugate (φ i)) (ComplexEmbedding.conjugate (φ j))).2 fun h => ?_
      rw [ComplexEmbedding.involutive_conjugate E (φ i)] at h
      exact key i j hij (ComplexEmbedding.conjugate (φ j)) (Or.inl h) (Or.inr rfl)
  refine ⟨fun i j hij a ha b hb => ?_, fun i => ?_⟩
  · have h0 : B a b = 0 := bilin_eq_zero_of_span B (gen i j hij) ha hb
    rw [pairing, h0, mul_zero]
  · have h1 : B (eCl φ i) (fCl φ i) = (φ i ξ)⁻¹ := (hv (φ i) (ComplexEmbedding.conjugate (φ i))).1 rfl
    rw [pairing, h1, div_eq_mul_inv]
    ring

end GlobalTheory.DualFormOrtho
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFormBaseOfValue
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualBase

theorem dualFormBase_of_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → DualFormValue φ → DualFormBase φ := by
  intro E _ _ _ I _ _ φ hcm hval d δ hd hδ hφ η
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have : (d : E) = 0 := by simpa using hδ.symm
    have : d = 0 := by exact_mod_cast this
    omega
  obtain ⟨i0, -⟩ := hcm (Classical.choice (inferInstance : Nonempty (E →+* ℂ)))
  have hconj : IsCMField.complexConj E δ = -δ := by
    apply (φ i0).injective
    rw [IsCMField.complexEmbedding_complexConj, hφ, map_neg, hφ]
    simp [Complex.conj_ofReal]
  have hξ0 : ((η : ℤ) : E) * δ⁻¹ ≠ 0 := mul_ne_zero (by simp) (inv_ne_zero hδ0)
  have hξc : IsCMField.complexConj E (((η : ℤ) : E) * δ⁻¹) = -(((η : ℤ) : E) * δ⁻¹) := by
    rw [map_mul, map_inv₀, hconj, map_intCast, inv_neg, mul_neg]
  obtain ⟨h1, h2⟩ := hval _ hξ0 hξc
  refine ⟨h1, fun B hB ε => ?_⟩
  obtain ⟨h3, h4⟩ := h2 B hB ε
  refine ⟨h3, fun i => ?_⟩
  rw [h4 i, map_mul, map_inv₀, map_intCast, hφ]
  have hs : (Real.sqrt d : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rcases Int.units_eq_one_or η with rfl | rfl <;> rcases Int.units_eq_one_or ε with rfl | rfl <;>
    · push_cast
      field_simp

end GlobalTheory.DualBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHecke
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum GlobalTheory.DeformedSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.DerivAtOrigin

theorem series_weightTwo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (σ : ℂ), 0 < σ.re → ∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → DifferentiableAt ℝ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), eTerm φ m σ w q.1.out) z ∧ ∀ i : I, wirt i false (fun w : I → ℂ => ∑' q : modUnits (lattice c y), eTerm φ m σ w q.1.out) z = ∑' q : modUnits (lattice c y), eTerm φ (m + Pi.single i 1) σ z q.1.out := by
  intro E _ _ _ I _ _ φ hφ c y hc σ hσ m z hz
  have hz1 : ‖z‖ < 1 := (pi_norm_lt_iff one_pos).2 hz
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  set U : Set (I → ℂ) := Metric.ball 0 r with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUc : IsPreconnected U := (convex_ball (0 : I → ℂ) r).isPreconnected
  have hzU : z ∈ U := by simpa [hU] using hzr
  have hUle : ∀ w ∈ U, ∀ i, ‖w i‖ ≤ r := fun w hw i =>
    (norm_le_pi_norm w i).trans (show ‖w‖ < r by simpa [hU] using hw).le
  have hUpd : ∀ w ∈ U, w ∈ polydisc I := fun w hw i => lt_of_le_of_lt (hUle w hw i) hr1
  set N : modUnits (lattice c y) → ℝ := fun q => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-(1 + σ.re)) with hN
  have hNs : Summable N := GlobalTheory.CMVal.Conv.summable_norm_rpow E c y (1 + σ.re) hc (by linarith)
  have hne : ∀ q : modUnits (lattice c y), q.1.out ≠ 0 := fun q => (out_mem_lattice q).2
  choose C hC using fun m : I → ℕ => GlobalTheory.T.weightTwoDerivativeEisensteinTerm_uniform_bound E I φ hφ m σ r hσ.le hr1
  have hsum : ∀ m, ∀ w ∈ U, Summable (fun q : modUnits (lattice c y) => eTerm φ m σ w q.1.out) := fun m w hw =>
    Summable.of_norm_bounded (hNs.mul_left (C m)) fun q => hC m w (hUle w hw) _ (hne q)
  set f' : modUnits (lattice c y) → (I → ℂ) → ((I → ℂ) →L[ℝ] ℂ) := fun q w =>
    ∑ j, (eTerm φ (m + Pi.single j 1) σ w q.1.out • dz j +
      (eTerm φ m σ w q.1.out * (-σ * φ j q.1.out / starRingEnd ℂ (defCoord φ w q.1.out j))) • dzbar j) with hf'
  set u : modUnits (lattice c y) → ℝ := fun q => ∑ j : I, (C (m + Pi.single j 1) * N q * ‖(dz j : (I → ℂ) →L[ℝ] ℂ)‖ +
    C m * N q * (‖σ‖ / (1 - r)) * ‖(dzbar j : (I → ℂ) →L[ℝ] ℂ)‖) with hu
  have hus : Summable u := summable_sum fun j _ =>
    ((hNs.mul_left _).mul_right _).add (((hNs.mul_left _).mul_right _).mul_right _)
  have hder : ∀ q w, w ∈ U → HasFDerivAt (fun w : I → ℂ => eTerm φ m σ w q.1.out) (f' q w) w :=
    fun q w hw => GlobalTheory.T.hasFDerivAt_weightTwoDerivativeEisensteinTerm E I φ m σ q.1.out (hne q) w (hUpd w hw)
  have hrat : ∀ (q : modUnits (lattice c y)) w, w ∈ U → ∀ j,
      ‖-σ * φ j q.1.out / starRingEnd ℂ (defCoord φ w q.1.out j)‖ ≤ ‖σ‖ / (1 - r) := by
    intro q w hw j
    have hl := GlobalTheory.DeformedSum.Bound.defCoord_lower φ w q.1.out j (hUle w hw j)
    have hp : 0 < ‖φ j q.1.out‖ := by simpa using hne q
    have hr' : 0 < 1 - r := by linarith
    have hd : 0 < ‖defCoord φ w q.1.out j‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
    rw [norm_div, norm_mul, norm_neg, Complex.norm_conj, div_le_div_iff₀ hd hr']
    nlinarith [norm_nonneg σ]
  have hbd : ∀ q w, w ∈ U → ‖f' q w‖ ≤ u q := by
    intro q w hw
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_add_le _ _).trans (add_le_add ?_ ?_))
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC _ w (hUle w hw) _ (hne q)) (norm_nonneg _)
    · rw [norm_smul, norm_mul]
      have h1 := hC m w (hUle w hw) _ (hne q)
      exact mul_le_mul_of_nonneg_right (mul_le_mul h1 (hrat q w hw j) (norm_nonneg _) ((norm_nonneg _).trans h1))
        (norm_nonneg _)
  have hF : HasFDerivAt (fun w : I → ℂ => ∑' q : modUnits (lattice c y), eTerm φ m σ w q.1.out)
      (∑' q, f' q z) z :=
    hasFDerivAt_tsum_of_isPreconnected hus hUo hUc hder hbd hzU (hsum m z hzU) hzU
  refine ⟨hF.differentiableAt, fun i => ?_⟩
  have hcs : Summable (fun q => f' q z) := Summable.of_norm_bounded hus fun q => hbd q z hzU
  have hap : ∀ v : I → ℂ, HasSum (fun q => f' q z v) ((∑' q, f' q z) v) := fun v =>
    (ContinuousLinearMap.apply ℝ ℂ v).hasSum hcs.hasSum
  unfold wirt
  rw [hF.fderiv]
  refine (HasSum.tsum_eq ?_).symm
  refine (((hap _).add ((hap _).mul_left _)).div_const 2).congr_fun ?_
  intro q
  simp only [hf', ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dz_apply,
    dzbar_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
    Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp only [Pi.single_eq_same, map_one, Complex.conj_I, Bool.false_eq_true, if_false]
  linear_combination (eTerm φ (m + Pi.single i 1) σ z q.1.out / 2 -
    eTerm φ m σ z q.1.out * (-σ * φ i q.1.out / starRingEnd ℂ (defCoord φ z q.1.out i)) / 2) * Complex.I_mul_I

theorem wirtWord_congr {I : Type} [Fintype I] {U : Set (I → ℂ)} (hU : IsOpen U) {f g : (I → ℂ) → ℂ}
    (h : ∀ z ∈ U, f z = g z) (w : List (I × Bool)) : ∀ z ∈ U, wirtWord w f z = wirtWord w g z := by
  induction w with
  | nil => exact h
  | cons a w ih =>
    intro z hz
    have hev : wirtWord w f =ᶠ[nhds z] wirtWord w g := by
      filter_upwards [hU.mem_nhds hz] with u hu using ih u hu
    simp only [wirtWord_cons, wirt, hev.fderiv_eq]

theorem wirt_const_mul {I : Type} [Fintype I] (i : I) (bar : Bool) (a : ℂ) {f : (I → ℂ) → ℂ} {z : I → ℂ}
    (hf : DifferentiableAt ℝ f z) : wirt i bar (fun w => a * f w) z = a * wirt i bar f z := by
  simp only [wirt, fderiv_const_mul hf, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem eq_at_zero {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f halfPlane) (hg : DifferentiableOn ℂ g halfPlane)
    (h : ∀ σ : ℂ, 0 < σ.re → f σ = g σ) : f 0 = g 0 := by
  have ho : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
  have hc : IsPreconnected halfPlane := (convex_halfSpace_re_gt _).isPreconnected
  have h1 : (1 : ℂ) ∈ halfPlane := by simp [halfPlane]; norm_num
  have h0 : (0 : ℂ) ∈ halfPlane := by simp [halfPlane]; norm_num
  have ho' : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (hf.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd ho) hc h1 ?_ h0
  filter_upwards [ho'.mem_nhds (show (1 : ℂ) ∈ {s : ℂ | 0 < s.re} by simp)] with s hs using h s hs

theorem isOpen_upperHalf (F : Type) [Field F] [NumberField F] : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, {z : Emb F → ℂ | 0 < (z τ).im} := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply i))

theorem derivFormula_two (hH : HeckeWeightTwo) (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    [DecidableEq I] (φ : I → E →+* ℂ) (hF : 2 ≤ Module.finrank ℚ (maximalRealSubfield E)) (hφ : IsCMType φ)
    (c : Ideal (OF E)) (y : (Af E)ˣ) (hc : c ≠ ⊥) : DerivFormula φ 2 (lattice c y) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_cmType_realEmbeddings_maxRealSubfield E I φ hφ
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_element_pos_im_under_cmType E I φ hφ
  have hne : Nonempty I := by
    obtain ⟨i, -⟩ := hφ (Classical.arbitrary (E →+* ℂ))
    exact ⟨i⟩
  have hnot : ∀ θ : E, (∀ i, 0 < (φ i θ).im) → θ ∉ maximalRealSubfield E := fun θ h hθ => by
    obtain ⟨i⟩ := hne
    have h1 := h i
    rw [show θ = ((⟨θ, hθ⟩ : maximalRealSubfield E) : E) from rfl, he] at h1
    simp at h1
  obtain ⟨𝔞, 𝔟, a₀, hL⟩ := GlobalTheory.T.orderLattice_eq_steinitzForm_cm E c y hc θ₀ (hnot θ₀ hθ₀)
  set θ : E := θ₀ + a₀ with hθdef
  have hθ : ∀ i, 0 < (φ i θ).im := fun i => by
    rw [hθdef, map_add (f := _), he]; simpa using hθ₀ i
  obtain ⟨G, ⟨hG1, hG2, hG3⟩, hG0, -⟩ := hH (maximalRealSubfield E) hF 𝔞 𝔟
  have hP := GlobalTheory.WeightTwoSum.isOpen_polydisc I
  have hmaps : Set.MapsTo (modPt φ e θ) (polydisc I) (upperHalf _) := fun z hz τ => modPt_im_pos φ e θ hθ hz τ
  set cw : ℂ := (cWt E 2 : ℂ) with hcw
  set b : (I → ℂ) → ℂ := fun z => (homFac z)⁻¹ ^ 2 with hb
  have hbC : ContDiffOn ℂ ∞ b (polydisc I) :=
    (contDiff_homFac.contDiffOn.inv fun z hz => homFac_ne_zero hz).pow 2
  set K : ℂ → (I → ℂ) → ℂ := fun σ z => b z * Complex.exp (-σ * logFac z) * G σ (modPt φ e θ z) with hK
  have hchain : ∀ (a : ℂ) (w : List (I × Bool)), ∀ z ∈ polydisc I,
      DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => a * K σ z') z) halfPlane := fun a w z hz => by
    have h := GlobalTheory.T.differentiableOn_wirtWord_mul_exp_comp' _ I (polydisc I) (upperHalf _) halfPlane G (modPt φ e θ) (fun z => a * b z) logFac hP
      (isOpen_upperHalf _) hmaps ((contDiffOn_modPt φ e θ).restrict_scalars ℝ)
      ((contDiffOn_const.mul hbC).restrict_scalars ℝ) contDiffOn_logFac hG2 hG3 w z hz
    simpa only [hK, mul_assoc] using h
  have hKd : ∀ z ∈ polydisc I, DifferentiableOn ℂ (fun σ => K σ z) halfPlane := fun z hz => by
    simpa [wirtWord_nil] using hchain 1 [] z hz
  have hKs : ∀ z ∈ polydisc I, ∀ σ : ℂ, 0 < σ.re →
      HasSum (fun q : modUnits (lattice c y) => defTerm φ 2 z σ q.1.out) (K σ z) := fun z hz σ hσ => by
    obtain ⟨h1, h2⟩ := hG1 σ hσ _ (hmaps hz)
    refine GlobalTheory.T.hasSum_deformedLatticeEisensteinSummand_weight_two E I φ e he 𝔞 𝔟 θ _ (hnot θ hθ) hL z hz σ _ ?_
    rw [h2]
    exact h1.hasSum
  have hagree : ∀ g, IsDefSum φ 2 (lattice c y) g → ∀ z ∈ polydisc I, g z = cw * K 0 z := by
    intro g hg z hz
    obtain ⟨G', hG', hgz⟩ := hg z hz
    obtain ⟨H, hH1, hH2, rfl⟩ := hG'.2 rfl
    rw [hgz, eq_at_zero hH1 (hKd z hz) fun σ hσ => (hH2 σ hσ).unique (hKs z hz σ hσ)]
  have hK0 : DifferentiableOn ℂ (fun z => cw * K 0 z) (polydisc I) := by
    simp only [hK, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    refine (((hbC.differentiableOn (by simp)).mul (hG0.comp ((contDiffOn_modPt φ e θ).differentiableOn (by simp)) hmaps))).const_mul _
  refine ⟨⟨fun z => cw * K 0 z, fun z hz => ⟨K 0 z, ⟨fun h => absurd rfl h,
    fun _ => ⟨fun σ => K σ z, hKd z hz, hKs z hz, rfl⟩⟩, rfl⟩⟩, fun g hg => ?_⟩
  have hgd : DifferentiableOn ℂ g (polydisc I) := hK0.congr (hagree g hg)
  refine ⟨hgd, fun κ l hl => ⟨fun S hS => ?_, fun h => absurd h (by norm_num)⟩⟩
  have h0 : (0 : I → ℂ) ∈ polydisc I := GlobalTheory.DerivAtOrigin.zero_mem_polydisc I
  have hκ : (fun j => l.count j) = κ := funext hl

  have hser : ∀ σ : ℂ, 0 < σ.re → ∀ l : List I, ∀ z ∈ polydisc I,
      wirtWord (l.map fun i => (i, false)) (fun z' => cw * K σ z') z =
        cw * ∑' q : modUnits (lattice c y), eTerm φ (fun j => l.count j) σ z q.1.out := by
    intro σ hσ l
    induction l with
    | nil =>
      intro z hz
      have : (fun j : I => ([] : List I).count j) = 0 := by funext j; simp
      rw [this]
      simp only [List.map_nil, wirtWord_nil, eTerm_zero]
      rw [(hKs z hz σ hσ).tsum_eq]
    | cons i l ih =>
      intro z hz
      obtain ⟨h1, h2⟩ := series_weightTwo E I φ hφ c y hc σ hσ (fun j => l.count j) z hz
      have h3 := wirtWord_congr hP ih [(i, false)] z hz
      rw [List.map_cons, wirtWord_cons, count_cons_eq, ← h2 i, ← wirt_const_mul i false cw h1]
      exact h3
  rw [GlobalTheory.T.iteratedComplexPartialDerivative_eq_wirtingerWord I _ g hP hgd l 0 h0, wirtWord_congr hP (hagree g hg) _ 0 h0, ← risingS_zero]
  refine eq_at_zero (f := fun σ => wirtWord (l.map fun i => (i, false)) (fun z' => cw * K σ z') 0)
    (g := fun σ => cw * risingS σ κ * S σ) (hchain cw _ 0 h0)
    ((((differentiable_risingS κ).const_mul cw).mul hS.1).differentiableOn) fun σ hσ => ?_
  have h4 := hS.2 σ (by push_cast; linarith)
  simp only [hser σ hσ l 0 h0, hκ, eTerm_origin]
  rw [tsum_mul_left, h4.tsum_eq, mul_assoc]

theorem statement (hH : HeckeWeightTwo) : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement := by
  intro E _ _ _ I _ _ φ hF hφ
  have hV := GlobalTheory.DualFormOrtho.dualFormValue_of_values E I φ hφ (GlobalTheory.DualFormExists.dualForm_existsUnique E)
    (GlobalTheory.DualFormValues.dualForm_values E)
  refine ⟨fun s hs => ⟨fun c y hc => ⟨?_, GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _⟩,
    GlobalTheory.ClassInv.classInvariance E I φ hφ (GlobalTheory.HomothetyLatSum.homothety E I φ hφ) s⟩, hV,
    GlobalTheory.DualBase.dualFormBase_of_value E I φ hφ hV⟩
  rcases Nat.lt_or_ge s 2 with h | h
  · obtain rfl : s = 1 := by omega
    exact derivFormula_two hH E I φ hF hφ c y hc
  · exact derivFormula_of_series E I φ (2 * s) _ (by omega)
      (fun m z hz => GlobalTheory.DeformedSum.Series.series_differentiable E I φ hφ s h c y hc m z hz)

end GlobalTheory.DerivAtOrigin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHeckeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement := by
  first | exact @GlobalTheory.DerivAtOrigin.statement | exact GlobalTheory.DerivAtOrigin.statement | (intros; apply GlobalTheory.DerivAtOrigin.statement <;> assumption)
end
