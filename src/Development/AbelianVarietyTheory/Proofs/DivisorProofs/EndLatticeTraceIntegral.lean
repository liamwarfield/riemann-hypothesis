module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHilbertLatticeTwistIffLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndLatticeTraceIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndLatticeTraceIntegral
noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix Polynomial GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

theorem isIntegral_trace_of_isIntegral_matrix {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := _root_.Formalism.IrreducibleCountingLemmas.TW.isIntegral_trace_of_isIntegral (K := K) (n := n) M hM

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem isIntegral_of_mapsTo_lattice (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (Y : Matrix (Fin r) (Fin r) E)
    (hY : ∀ x ∈ Λ, Y *ᵥ x ∈ Λ) : IsIntegral (𝓞 E) Y := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  let f : Module.End (𝓞 E) Λ :=
    { toFun := fun x => ⟨Y *ᵥ (x : Fin r → E), hY _ x.2⟩
      map_add' := fun x y => by ext1; simp [mulVec_add]
      map_smul' := fun c x => by ext1; simp [mulVec_smul] }
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero (𝓞 E) f
  have key : ∀ q : (𝓞 E)[X], ∀ x (hx : x ∈ Λ), aeval Y q *ᵥ x = ((aeval f q ⟨x, hx⟩ : Λ) : Fin r → E) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x hx
      simp only [aeval_C]
      rw [show (algebraMap (𝓞 E) (Matrix (Fin r) (Fin r) E)) a = Matrix.diagonal (fun _ => (a : E)) from rfl]
      ext i
      rw [mulVec_diagonal, Module.algebraMap_end_apply]
      rfl
    | add p q hp hq =>
      intro x hx
      rw [map_add (f := _), add_mulVec, hp x hx, hq x hx, map_add (f := _)]
      rfl
    | monomial n a ih =>
      intro x hx
      have e1 : aeval Y (C a * X ^ (n + 1)) = aeval Y (C a * X ^ n) * Y := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      have e2 : aeval f (C a * X ^ (n + 1)) = aeval f (C a * X ^ n) * f := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      rw [e1, e2, ← mulVec_mulVec, ih _ (hY x hx)]
      rfl
  have hker : ∀ v, aeval Y p *ᵥ v = 0 := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => rw [key p x hx, hp0]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy, add_zero]
    | smul c x _ hx => rw [mulVec_smul, hx, smul_zero]
  have hA : aeval Y p = 0 := by
    apply Matrix.toLin'.injective
    ext v i
    simp [Matrix.toLin'_apply, hker]
  exact ⟨p, hp, by rw [← aeval_def]; exact hA⟩

theorem isIntegral_trace_of_mem_endLat [IsCMField E] (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E) (hS : SelfDualLat G Λ)
    (hY : Y ∈ endLat Λ) : IsIntegral ℤ Y.trace :=
  isIntegral_trace_of_isIntegral_matrix Y
    (@isIntegral_trans ℤ (𝓞 E) _ _ _ _ _ _ _ AddCommGroup.intIsScalarTower _ Y
      (isIntegral_of_mapsTo_lattice Λ hS.2.2.1 hS.2.2.2.1 Y (mem_endLat.mp hY)))

theorem trace_integral_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E),
    SelfDualLat G Λ → Y ∈ endLat Λ → IsIntegral ℤ Y.trace :=
  fun _ _ _ _ _ G Λ Y hS hY => isIntegral_trace_of_mem_endLat G Λ Y hS hY

end GlobalTheory.LieDisc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndLatticeTraceIntegralStatement
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.end_lattice_trace_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → IsIntegral ℤ Y.trace := by
  first | exact @GlobalTheory.LieDisc.trace_integral_main | exact GlobalTheory.LieDisc.trace_integral_main | (intros; apply GlobalTheory.LieDisc.trace_integral_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFDerivAtWeightTwoDerivativeEisensteinTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFDerivAtWeightTwoDerivativeEisensteinTerm
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoSum

theorem norm_cpow_eq_mul_conj_cpow (u s : ℂ) :
    ((‖u‖ : ℝ) : ℂ) ^ (-2 * s) = (u * starRingEnd ℂ u) ^ (-s) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [sq, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  rw [show -2 * s = ((2:ℕ):ℂ) * (-s) by push_cast; ring, Complex.cpow_nat_mul, sq]

theorem hasFDerivAt_factor_norm_cpow {I : Type} [Fintype I] (j : I) (a c K σ : ℂ) (n : ℕ) (z : I → ℂ)
    (hu : a + z j * c ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => K * (a + w j * c)⁻¹ ^ n * ((‖a + w j * c‖ : ℝ) : ℂ) ^ (-2 * σ))
      ((K * (a + z j * c)⁻¹ ^ n * ((‖a + z j * c‖ : ℝ) : ℂ) ^ (-2 * σ) * (-((n : ℂ) + σ) * c / (a + z j * c))) • dz j +
       (K * (a + z j * c)⁻¹ ^ n * ((‖a + z j * c‖ : ℝ) : ℂ) ^ (-2 * σ) *
         (-σ * starRingEnd ℂ c / starRingEnd ℂ (a + z j * c))) • dzbar j) z := by
  simp_rw [norm_cpow_eq_mul_conj_cpow]
  set u := a + z j * c with hu_def
  have hU : HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => a + w j * c) (c • dz j) z :=
    ((dz j).hasFDerivAt.mul_const c).const_add a
  have hC : HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => starRingEnd ℂ (a + w j * c))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (c • dz j)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hU
  have hP := hU.mul hC
  have hcu : starRingEnd ℂ u ≠ 0 := (map_ne_zero _).2 hu
  have hne : u * starRingEnd ℂ u ≠ 0 := mul_ne_zero hu hcu
  have hslit : u * starRingEnd ℂ u ∈ Complex.slitPlane := by
    rw [Complex.mul_conj]
    exact Complex.ofReal_mem_slitPlane.2 (Complex.normSq_pos.2 hu)
  have hpow := ((hasDerivAt_id (u * starRingEnd ℂ u)).cpow_const (c := -σ) hslit).comp_hasFDerivAt z hP
  have hinv := (((hasDerivAt_id u).inv hu).pow n).comp_hasFDerivAt z hU
  have h := (hinv.const_mul K).mul hpow
  refine h.congr_fderiv ?_
  ext v
  clear h hinv hpow hP hC hU hslit
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    dz_apply, dzbar_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    Function.comp_apply, id, Pi.inv_apply, Pi.pow_apply, Pi.mul_apply, ← hu_def]
  rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
  rcases n with _ | n
  · simp
    field_simp
    ring
  · simp only [Nat.add_sub_cancel, inv_pow]
    field_simp
    push_cast
    ring

theorem hasFDerivAt_eTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I,
    HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => eTerm φ m σ w x)
      (∑ j, (eTerm φ (m + Pi.single j 1) σ z x • dz j +
        (eTerm φ m σ z x * (-σ * φ j x / starRingEnd ℂ (defCoord φ z x j))) • dzbar j)) z := by
  intro E _ _ I _ _ φ m σ x hx z hz
  let C : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * ∏ j ∈ Finset.range n, (2 + σ + j)
  let c : I → ℂ := fun i => starRingEnd ℂ (φ i x)
  let F : I → (I → ℂ) → ℂ := fun i w => C (m i) * c i ^ m i * (φ i x + w i * c i)⁻¹ ^ (2 + m i) *
    ((‖φ i x + w i * c i‖ : ℝ) : ℂ) ^ (-2 * σ)
  let α : I → ℂ := fun i => -(((2 + m i : ℕ) : ℂ) + σ) * c i / (φ i x + z i * c i)
  let β : I → ℂ := fun i => -σ * starRingEnd ℂ (c i) / starRingEnd ℂ (φ i x + z i * c i)
  have hF : ∀ i, HasFDerivAt (𝕜 := ℝ) (F i) ((F i z * α i) • dz i + (F i z * β i) • dzbar i) z := fun i =>
    hasFDerivAt_factor_norm_cpow i (φ i x) (c i) (C (m i) * c i ^ m i) σ (2 + m i) z
      (GlobalTheory.DeformedSum.defCoord_ne_zero φ z hz x hx i)
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ) (g := F) (x := z) (fun i _ => hF i)
  have hfun : (fun w : I → ℂ => eTerm φ m σ w x) = fun w => ∏ i ∈ Finset.univ, F i w := rfl
  have hval : eTerm φ m σ z x = ∏ i ∈ Finset.univ, F i z := rfl
  rw [hfun]
  refine hprod.congr_fderiv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have key : ∀ (f g : I → ℂ), (∀ i, i ≠ j → g i = f i) →
      ∏ i, g i = (∏ i ∈ Finset.univ.erase j, f i) * g j := by
    intro f g h
    rw [← Finset.prod_erase_mul Finset.univ g (Finset.mem_univ j)]
    congr 1
    exact Finset.prod_congr rfl fun i hi => h i (Finset.ne_of_mem_erase hi)
  rw [smul_add, smul_smul, smul_smul]
  congr 1
  · congr 1
    unfold eTerm
    rw [key (fun i => F i z) _ ?_]
    · congr 1
      simp only [Pi.add_apply, Pi.single_eq_same, F, α, C, c, defCoord, Finset.prod_range_succ, pow_succ]
      push_cast
      ring
    · intro i hij
      simp only [Pi.add_apply, Pi.single_eq_of_ne hij, add_zero]
      rfl
  · congr 1
    rw [hval, ← Finset.prod_erase_mul Finset.univ (fun i => F i z) (Finset.mem_univ j)]
    simp only [β, c, defCoord, Complex.conj_conj]
    ring

end GlobalTheory.WeightTwoSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFDerivAtWeightTwoDerivativeEisensteinTermStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_weightTwoDerivativeEisensteinTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => eTerm φ m σ w x) (∑ j, (eTerm φ (m + Pi.single j 1) σ z x • dz j + (eTerm φ m σ z x * (-σ * φ j x / starRingEnd ℂ (defCoord φ z x j))) • dzbar j)) z := by
  first | exact @GlobalTheory.WeightTwoSum.hasFDerivAt_eTerm | exact GlobalTheory.WeightTwoSum.hasFDerivAt_eTerm | (intros; apply GlobalTheory.WeightTwoSum.hasFDerivAt_eTerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDeformedLatticeEisensteinSummandWeightTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDeformedLatticeEisensteinSummandWeightTwo
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem prodCpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w = (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j)]

theorem norm_cpow_eq_exp {h : ℂ} (hh : h ≠ 0) (σ : ℂ) :
    ((‖h‖ : ℝ) : ℂ) ^ (-2 * σ) = Complex.exp (-σ * ((Real.log (Complex.normSq h) : ℝ) : ℂ)) := by
  have hn : ((‖h‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hh
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (norm_nonneg _), Complex.normSq_eq_norm_sq,
    Real.log_pow]
  congr 1
  push_cast
  ring

variable [IsCMField E]

theorem defCoord_eq (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E))
    (he : ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) (θ : E) {z : I → ℂ}
    (hz : z ∈ polydisc I) (a b : maximalRealSubfield E) (i : I) :
    defCoord φ z ((a : E) + (b : E) * θ) i =
      (1 + z i) / (2 * (Real.pi : ℂ) * Complex.I) * latPt (modPt φ e θ z) (a, b) (e i) := by
  have h1 := one_add_ne_zero hz i
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  simp only [defCoord, latPt, modPt, Equiv.symm_apply_apply, map_add (f := _), map_mul, he, Complex.conj_ofReal]
  field_simp
  ring

theorem defTerm_eq (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E))
    (he : ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) (θ : E) {z : I → ℂ}
    (hz : z ∈ polydisc I) (σ : ℂ) (a b : maximalRealSubfield E) :
    defTerm φ 2 z σ ((a : E) + (b : E) * θ) =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisTerm 2 σ (modPt φ e θ z) (a, b) := by
  set w := latPt (modPt φ e θ z) (a, b)
  set c : I → ℂ := fun i => (1 + z i) / (2 * (Real.pi : ℂ) * Complex.I)
  have hc : homFac z = ∏ i, c i := rfl
  have hw : ∏ τ, w τ = ∏ i, w (e i) := (Equiv.prod_comp e w).symm
  unfold defTerm eisTerm logFac
  simp only [defCoord_eq φ e he θ hz a b]
  rw [Finset.prod_mul_distrib]
  have h1 : ∏ i, (c i * w (e i))⁻¹ ^ 2 = (homFac z)⁻¹ ^ 2 * (∏ τ, w τ)⁻¹ ^ 2 := by
    rw [hc, hw, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_inv, mul_pow]
  have h2 : ∏ i, ((‖c i * w (e i)‖ : ℝ) : ℂ) ^ (-2 * σ) =
      ((‖homFac z‖ : ℝ) : ℂ) ^ (-2 * σ) * ((‖∏ τ, w τ‖ : ℝ) : ℂ) ^ (-2 * σ) := by
    rw [prodCpow _ _ (fun i => norm_nonneg _), hc, hw, norm_prod, norm_prod,
      ← Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)
        (Finset.prod_nonneg fun i _ => norm_nonneg _), ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
    simp only [norm_mul]
  rw [h1, h2, norm_cpow_eq_exp (homFac_ne_zero hz)]
  ring

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_of_add_mul {θ : E} (hθ : θ ∉ maximalRealSubfield E) {a b a' b' : maximalRealSubfield E}
    (h : (a : E) + (b : E) * θ = (a' : E) + (b' : E) * θ) : a = a' ∧ b = b' := by
  by_cases hb : b = b'
  · subst hb
    refine ⟨Subtype.ext ?_, rfl⟩
    simpa using h
  · exfalso
    apply hθ
    have hb' : ((b : E) - (b' : E)) ≠ 0 := by
      intro h0; apply hb; exact Subtype.ext (sub_eq_zero.1 h0)
    have : θ = ((a' : E) - (a : E)) / ((b : E) - (b' : E)) := by
      field_simp
      linear_combination h
    rw [this]
    exact div_mem (sub_mem a'.2 a.2) (sub_mem b.2 b'.2)

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem algebraMap_unit (u : (OF E)ˣ) :
    algebraMap (OF E) E (u : OF E) = (((u : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E) : E) := rfl

noncomputable def classMap (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ)
    (c : Quotient (latRel 𝔞 𝔟)) : modUnits L :=
  ⟨Quotient.mk _ ((c.out.1.1 : E) + (c.out.1.2 : E) * θ),
    (c.out.1.1 : E) + (c.out.1.2 : E) * θ, (hL _).2 ⟨_, c.out.2.1, _, c.out.2.2.1, rfl⟩, fun h0 => c.out.2.2.2 (by
      have h := eq_of_add_mul hθ (a := c.out.1.1) (b := c.out.1.2) (a' := 0) (b' := 0) (by simpa using h0)
      exact Prod.ext h.1 h.2), rfl⟩

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem classMap_bijective (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) :
    Function.Bijective (classMap 𝔞 𝔟 θ L hθ hL) := by
  constructor
  · intro c c' h
    have h1 := Quotient.exact (congrArg Subtype.val h)
    obtain ⟨u, hu⟩ := h1
    rw [algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul] at hu
    obtain ⟨ha, hb⟩ := eq_of_add_mul hθ hu
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨u, ha, hb⟩
  · rintro ⟨q, x, hxL, hx0, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (hL x).1 hxL
    have hp : ((a, b) : maximalRealSubfield E × maximalRealSubfield E) ≠ 0 := by
      intro h0
      apply hx0
      have h1 : a = 0 := congrArg Prod.fst h0
      have h2 : b = 0 := congrArg Prod.snd h0
      simp [h1, h2]
    let p : LatPair 𝔞 𝔟 := ⟨(a, b), ha, hb, hp⟩
    refine ⟨Quotient.mk _ p, Subtype.ext ?_⟩
    obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r (Quotient.mk (latRel 𝔞 𝔟) p).out p := Quotient.exact (Quotient.out_eq _)
    show Quotient.mk _ _ = Quotient.mk _ _
    refine Quotient.sound ⟨ε, ?_⟩
    rw [algebraMap_unit]
    have e1 : a = p.1.1 := rfl
    have e2 : b = p.1.2 := rfl
    rw [e1, e2, h1, h2, Subfield.coe_mul, Subfield.coe_mul]
    ring

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

theorem hasSum_defTerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (e : I ≃ Emb (maximalRealSubfield E)), (∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) →
    ∀ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E), θ ∉ maximalRealSubfield E →
    (∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) →
    ∀ z ∈ polydisc I, ∀ (σ S : ℂ), HasSum (eisClass 𝔞 𝔟 2 σ (modPt φ e θ z)) S →
      HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ((homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * S) := by
  intro E _ _ _ I _ φ e he 𝔞 𝔟 θ L hθ hL z hz σ S hS
  let g := Equiv.ofBijective _ (classMap_bijective 𝔞 𝔟 θ L hθ hL)
  rw [← g.hasSum_iff]
  have key1 : ∀ c, defTerm φ 2 z σ (g c).1.out =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    intro c
    set x : E := (c.out.1.1 : E) + (c.out.1.2 : E) * θ with hx
    have hg : (g c).1 = Quotient.mk _ x := rfl
    obtain ⟨u, hu⟩ : unitRel.r x (g c).1.out := Quotient.exact (by rw [hg, Quotient.out_eq])
    rw [hu, hx, algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul,
      defTerm_eq φ e he θ hz, eisTerm_unit (by decide)]
    rfl
  have key : (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ∘ g =
      fun c => (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    funext c
    simp only [Function.comp_apply]
    exact key1 c
  rw [key]
  exact hS.mul_left _

end GlobalTheory.WeightTwoCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDeformedLatticeEisensteinSummandWeightTwoStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_deformedLatticeEisensteinSummand_weight_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E)), (∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) → ∀ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E), θ ∉ maximalRealSubfield E → (∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)), x = (a : E) + (b : E) * θ) → ∀ z ∈ polydisc I, ∀ (σ S : ℂ), HasSum (eisClass 𝔞 𝔟 2 σ (modPt φ e θ z)) S → HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ((homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * S) := by
  first | exact @GlobalTheory.WeightTwoCompare.hasSum_defTerm | exact GlobalTheory.WeightTwoCompare.hasSum_defTerm | (intros; apply GlobalTheory.WeightTwoCompare.hasSum_defTerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnWirtWordMulExpComp
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

noncomputable section

namespace GlobalTheory.WirtChain

open Complex

variable {Φ I : Type} [Fintype Φ] [Fintype I]

theorem contDiffOn_wirt' {V : Set (Φ → ℂ)} (hV : IsOpen V) {g : (Φ → ℂ) → ℂ} (hg : ContDiffOn ℝ ∞ g V)
    (τ : Φ) (bar : Bool) : ContDiffOn ℝ ∞ (wirt τ bar g) V := by
  have hd := ((contDiffOn_infty_iff_fderiv_of_isOpen hV).1 hg).2
  unfold wirt
  exact ((hd.clm_apply contDiffOn_const).add (contDiffOn_const.mul (hd.clm_apply contDiffOn_const))).div_const 2

theorem contDiffOn_wirtWord' {V : Set (Φ → ℂ)} (hV : IsOpen V) {g : (Φ → ℂ) → ℂ} (hg : ContDiffOn ℝ ∞ g V)
    (w : List (Φ × Bool)) : ContDiffOn ℝ ∞ (wirtWord w g) V := by
  induction w with
  | nil => simpa [wirtWord_nil] using hg
  | cons a w ih => rw [wirtWord_cons]; exact contDiffOn_wirt' hV ih _ _

open Classical in
theorem fderiv_eq_sum_wirt' (h : (Φ → ℂ) → ℂ) (y u : Φ → ℂ) :
    fderiv ℝ h y u = ∑ τ, (u τ * wirt τ false h y + (starRingEnd ℂ) (u τ) * wirt τ true h y) := by
  have hu : u = ∑ τ, ((u τ).re • (Pi.single τ (1:ℂ) : Φ → ℂ) + (u τ).im • (Pi.single τ I : Φ → ℂ)) := by
    ext τ'
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp [Complex.re_add_im]
  conv_lhs => rw [hu]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_add (f := _), map_smul, map_smul]
  simp only [wirt, Bool.false_eq_true, if_false, if_true, real_smul]
  set A := fderiv ℝ h y (Pi.single τ 1)
  set B := fderiv ℝ h y (Pi.single τ I)
  have hc : (starRingEnd ℂ) (u τ) = (u τ).re - (u τ).im * I := by
    apply Complex.ext <;> simp
  have hu' : u τ = (u τ).re + (u τ).im * I := (Complex.re_add_im _).symm
  have key : ∀ (a c : ℝ) (A B : ℂ), (a:ℂ) * A + (c:ℂ) * B =
      ((a:ℂ) + (c:ℂ) * I) * ((A + -I * B) / 2) + ((a:ℂ) - (c:ℂ) * I) * ((A + I * B) / 2) := by
    intro a c A B
    ring_nf
    rw [I_sq]
    ring
  have := key (u τ).re (u τ).im A B
  rw [← hu', ← hc] at this
  linear_combination this

section Rep

variable (U : Set (I → ℂ)) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (l : (I → ℂ) → ℂ)

inductive ExpSum : (ℂ → (I → ℂ) → ℂ) → Prop
  | zero : ExpSum fun _ _ => 0
  | term (n : ℕ) (β : (I → ℂ) → ℂ) (w : List (Φ × Bool)) : ContDiffOn ℝ ∞ β U →
      ExpSum fun σ z => σ ^ n * β z * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z)
  | add {F₁ F₂ : ℂ → (I → ℂ) → ℂ} : ExpSum F₁ → ExpSum F₂ → ExpSum fun σ z => F₁ σ z + F₂ σ z

variable {U G t l}

theorem ExpSum.const_mul {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) (c : ℂ) :
    ExpSum U G t l fun σ z => c * F σ z := by
  induction hF with
  | zero => simpa using ExpSum.zero (U := U) (G := G) (t := t) (l := l)
  | term n β w hβ =>
    have h := ExpSum.term (U := U) (G := G) (t := t) (l := l) n (fun z => c * β z) w (contDiffOn_const.mul hβ)
    convert h using 2
    ring_nf
  | add _ _ h₁ h₂ =>
    have h := ExpSum.add h₁ h₂
    convert h using 2
    ring_nf

theorem ExpSum.sum {α : Type} (s : Finset α) (F : α → ℂ → (I → ℂ) → ℂ) (hF : ∀ a ∈ s, ExpSum U G t l (F a)) :
    ExpSum U G t l fun σ z => ∑ a ∈ s, F a σ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ExpSum.zero (U := U) (G := G) (t := t) (l := l)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ExpSum.add (hF a (Finset.mem_insert_self a s)) (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

theorem ExpSum.holo {D : Set ℂ} {V : Set (Φ → ℂ)} (hmaps : Set.MapsTo t U V)
    (hGh : ∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) {z : I → ℂ} (hz : z ∈ U) :
    DifferentiableOn ℂ (fun σ => F σ z) D := by
  induction hF with
  | zero => exact differentiableOn_const _
  | term n β w hβ =>
    exact (((differentiableOn_id.pow n).mul (differentiableOn_const _)).mul
      ((differentiableOn_id.neg.mul_const (l z)).cexp)).mul (hGh w (t z) (hmaps hz))
  | add _ _ h₁ h₂ => exact h₁.add h₂

theorem ExpSum.smooth {D : Set ℂ} {V : Set (Φ → ℂ)} (hV : IsOpen V) (hmaps : Set.MapsTo t U V)
    (ht : ContDiffOn ℝ ∞ t U) (hl : ContDiffOn ℝ ∞ l U)
    (hGs : ∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) {σ : ℂ} (hσ : σ ∈ D) :
    ContDiffOn ℝ ∞ (F σ) U := by
  induction hF with
  | zero => exact contDiffOn_const
  | term n β w hβ =>
    exact ((contDiffOn_const.mul hβ).mul (contDiffOn_const.mul hl).cexp).mul
      ((contDiffOn_wirtWord' hV (hGs σ hσ) w).comp ht hmaps)
  | add _ _ h₁ h₂ => exact h₁.add h₂

end Rep

section Deriv

variable {U : Set (I → ℂ)} {G : ℂ → (Φ → ℂ) → ℂ} {t : (I → ℂ) → Φ → ℂ} {l : (I → ℂ) → ℂ}

theorem ExpSum.deriv {D : Set ℂ} {V : Set (Φ → ℂ)} (hU : IsOpen U) (hV : IsOpen V) (hmaps : Set.MapsTo t U V)
    (ht : ContDiffOn ℝ ∞ t U) (hl : ContDiffOn ℝ ∞ l U)
    (hGs : ∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) (v : I → ℂ) :
    ∃ F', ExpSum U G t l F' ∧ ∀ σ ∈ D, ∀ z ∈ U, fderiv ℝ (F σ) z v = F' σ z := by
  have hdt := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 ht).2
  have hdl := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hl).2
  have hdtv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ t z v) U := hdt.clm_apply contDiffOn_const
  have hdlv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ l z v) U := hdl.clm_apply contDiffOn_const
  induction hF with
  | zero => exact ⟨fun _ _ => 0, ExpSum.zero, fun σ _ z _ => by simp⟩
  | @add F₁ F₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨F₁', h₁', e₁⟩ := ih₁
    obtain ⟨F₂', h₂', e₂⟩ := ih₂
    refine ⟨fun σ z => F₁' σ z + F₂' σ z, ExpSum.add h₁' h₂', fun σ hσ z hz => ?_⟩
    have d₁ := ((h₁.smooth hV hmaps ht hl hGs hσ).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    have d₂ := ((h₂.smooth hV hmaps ht hl hGs hσ).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    show fderiv ℝ (fun y => F₁ σ y + F₂ σ y) z v = F₁' σ z + F₂' σ z
    have hsum : HasFDerivAt (fun y => F₁ σ y + F₂ σ y) _ z := d₁.hasFDerivAt.add d₂.hasFDerivAt
    rw [hsum.fderiv, ContinuousLinearMap.add_apply, e₁ σ hσ z hz, e₂ σ hσ z hz]
  | term n β w hβ =>
    have hdb := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hβ).2
    have hdbv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ β z v) U := hdb.clm_apply contDiffOn_const
    refine ⟨fun σ z => (σ ^ n * fderiv ℝ β z v * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z) +
        σ ^ (n + 1) * (-(β z * fderiv ℝ l z v)) * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z)) +
        ∑ τ : Φ, (σ ^ n * (β z * fderiv ℝ t z v τ) * Complex.exp (-σ * l z) * wirtWord ((τ, false) :: w) (G σ) (t z) +
          σ ^ n * (β z * (starRingEnd ℂ) (fderiv ℝ t z v τ)) * Complex.exp (-σ * l z) *
            wirtWord ((τ, true) :: w) (G σ) (t z)), ?_, ?_⟩
    · refine ExpSum.add (ExpSum.add (ExpSum.term n _ w hdbv) (ExpSum.term (n + 1) _ w (hβ.mul hdlv).neg))
        (ExpSum.sum Finset.univ _ fun τ _ => ExpSum.add (ExpSum.term n _ _ (hβ.mul (contDiffOn_pi.1 hdtv τ)))
          (ExpSum.term n _ _ (hβ.mul ?_)))
      have := Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.1 hdtv τ)
      simpa [Function.comp_def] using this
    · intro σ hσ z hz
      have hzn := hU.mem_nhds hz
      set W := wirtWord w (G σ) with hWdef
      have hWs : ContDiffOn ℝ ∞ W V := contDiffOn_wirtWord' hV (hGs σ hσ) w
      have hb' : HasFDerivAt β (fderiv ℝ β z) z :=
        ((hβ.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have hl' : HasFDerivAt l (fderiv ℝ l z) z :=
        ((hl.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have ht' : HasFDerivAt t (fderiv ℝ t z) z :=
        ((ht.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have hW' : HasFDerivAt W (fderiv ℝ W (t z)) (t z) :=
        ((hWs.differentiableOn (by simp)).differentiableAt (hV.mem_nhds (hmaps hz))).hasFDerivAt
      have hE := (hl'.const_mul (-σ)).cexp
      have hWt := hW'.comp z ht'
      have hall := ((hb'.const_mul (σ ^ n)).mul hE).mul hWt
      have hall' : HasFDerivAt (fun y => σ ^ n * β y * Complex.exp (-σ * l y) * W (t y)) _ z := hall
      rw [hall'.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.comp_apply, Function.comp_apply, Pi.mul_apply]
      rw [fderiv_eq_sum_wirt' W (t z) (fderiv ℝ t z v)]
      simp only [wirtWord_cons]
      rw [← hWdef]
      have hs : ∀ τ : Φ, σ ^ n * β z * Complex.exp (-σ * l z) * (fderiv ℝ t z v τ * wirt τ false W (t z) +
          (starRingEnd ℂ) (fderiv ℝ t z v τ) * wirt τ true W (t z)) =
          σ ^ n * (β z * fderiv ℝ t z v τ) * Complex.exp (-σ * l z) * wirt τ false W (t z) +
          σ ^ n * (β z * (starRingEnd ℂ) (fderiv ℝ t z v τ)) * Complex.exp (-σ * l z) * wirt τ true W (t z) :=
        fun τ => by ring
      rw [Finset.mul_sum]
      simp only [hs]
      ring

end Deriv


open Classical in
theorem differentiableOn_wirtWord_mul_exp_comp : ∀ (Φ I : Type) [Fintype Φ] [Fintype I] (U : Set (I → ℂ)) (V : Set (Φ → ℂ)) (D : Set ℂ) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (b l : (I → ℂ) → ℂ), IsOpen U → IsOpen V → Set.MapsTo t U V → ContDiffOn ℝ ∞ t U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ l U → (∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V) → (∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D) → ∀ w : List (I × Bool), ∀ z ∈ U, DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) z) D := by
  intro Φ I _ _ U V D G t b l hU hV hmaps ht hb hl hGs hGh w z hz
  have key : ∀ w : List (I × Bool), ∃ F, ExpSum U G t l F ∧ ∀ σ ∈ D,
      Set.EqOn (wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z'))) (F σ) U := by
    intro w
    induction w with
    | nil =>
      refine ⟨_, ExpSum.term 0 b [] hb, fun σ _ z _ => ?_⟩
      simp [wirtWord_nil]
    | cons a w ih =>
      obtain ⟨F, hF, hEq⟩ := ih
      obtain ⟨F₁, hF₁, hd₁⟩ := hF.deriv hU hV hmaps ht hl hGs (Pi.single a.1 1)
      obtain ⟨F₂, hF₂, hd₂⟩ := hF.deriv hU hV hmaps ht hl hGs (Pi.single a.1 Complex.I)
      refine ⟨fun σ z => (1 / 2 : ℂ) * (F₁ σ z + (if a.2 then Complex.I else -Complex.I) * F₂ σ z),
        (ExpSum.add hF₁ (hF₂.const_mul _)).const_mul _, fun σ hσ z hz => ?_⟩
      have hev : wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) =ᶠ[nhds z] F σ :=
        Filter.eventually_of_mem (hU.mem_nhds hz) fun y hy => hEq σ hσ hy
      rw [wirtWord_cons]
      simp only [wirt]
      rw [hev.fderiv_eq, hd₁ σ hσ z hz, hd₂ σ hσ z hz]
      ring
  obtain ⟨F, hF, hEq⟩ := key w
  exact (hF.holo hmaps hGh hz).congr fun σ hσ => hEq σ hσ hz

end GlobalTheory.WirtChain
end
end
