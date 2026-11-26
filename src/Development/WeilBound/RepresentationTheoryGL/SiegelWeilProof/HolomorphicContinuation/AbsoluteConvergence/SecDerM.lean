module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMSt
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ}

def mulR (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ := fun a j => ∑ i, y a i * A i j

def aE (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp ((σ : ℂ) • H)

def DMp (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  eulH H R - MvPolynomial.C (2 * (c : ℂ)) *
    (∑ i, ∑ j, MvPolynomial.C (H i j) * (Qb ε true j i + Qb ε false j i)) * R

def CellM : Prop := ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.IsHermitian → ∀ f : ℝ → GR n,
  (∀ σ : ℝ, mR (f σ) = fromBlocks (NormedSpace.exp ((σ : ℂ) • H)) 0 0 (NormedSpace.exp (-((σ : ℂ) • H)))) →
  ∀ g : GR n, (mR g).toBlocks₂₁.det ≠ 0 → ∃ (y₁ : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧
    ∀ (p q : ℕ) (e : ℤ) (σ : ℝ), ∃ (mA w : GR n), IsUp mA ∧
      F0 p q e mA = Complex.exp (-((σ : ℂ) * ((p + q : ℕ) : ℂ) * H.trace)) ∧
      mR w = JJ n * nU (aE H (-σ) * b * aE H (-σ)) ∧ (aE H (-σ) * b * aE H (-σ)).IsHermitian ∧
      g * f σ = y₁ * mA * w

def CoV : Prop := ∀ (m n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.det ≠ 0 → ∀ F : (Fin m → Fin n → ℂ) → ℂ,
  ∫ x, F x = ((Complex.normSq A.det ^ m : ℝ) : ℂ) * ∫ y, F (mulR A y)

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMD
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMC
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMB
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem coV : CoV := by
  intro m n A hA F
  let Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' Aᵀ).restrictScalars ℝ
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a => Li.comp (LinearMap.proj a)
  have hL : ∀ y, L y = mulR A y := by
    intro y; funext a j
    simp [L, Li, mulR, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hdetLi : LinearMap.det Li = Complex.normSq A.det := by
    simp only [Li]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Matrix.det_transpose]
  have hdet : LinearMap.det L = Complex.normSq A.det ^ m := by
    simp only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hD : 0 < Complex.normSq A.det ^ m := pow_pos (Complex.normSq_pos.2 hA) _
  have hne : LinearMap.det L ≠ 0 := by rw [hdet]; exact hD.ne'
  let Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.equivOfDetNeZero L hne
  have hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = mulR A y := fun y => hL y
  have hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume := by
    have : (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L := by funext y; rfl
    rw [this]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne
  have h1 : ∫ y, F (mulR A y) = ((Complex.normSq A.det ^ m)⁻¹ : ℝ) * ∫ x, F x := by
    have := integral_map_equiv e F (μ := volume)
    simp only [he] at this
    rw [← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.2 hD)]
    simp [Complex.real_smul]
  rw [h1, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem aE_eq (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H σ = NormedSpace.exp (σ • H) := by
  unfold aE; rw [Complex.coe_smul]

theorem hasDerivAt_aE_entry (H : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun σ : ℝ => aE H σ i j) ((aE H s * H) i j) s := by
  simp only [aE_eq]
  open scoped Matrix.Norms.Operator in
  exact ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt s
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) H s)

theorem mulR_mul (A B : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    mulR B (mulR A y) = mulR (A * B) y := by
  funext a j
  simp only [mulR, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem mulR_one (y : Fin m → Fin n → ℂ) : mulR (1 : Matrix (Fin n) (Fin n) ℂ) y = y := by
  funext a j
  simp [mulR, Matrix.one_apply]

theorem hasDerivAt_mulR (H : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) (s : ℝ) (a : Fin m) (j : Fin n) :
    HasDerivAt (fun σ : ℝ => mulR (aE H σ) y a j) (mulR H (mulR (aE H s) y) a j) s := by
  have h : HasDerivAt (fun σ : ℝ => ∑ i, y a i * aE H σ i j) (∑ i, y a i * (aE H s * H) i j) s :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_aE_entry H s i j).const_mul (y a i)
  have e : ∑ i, y a i * (aE H s * H) i j = mulR H (mulR (aE H s) y) a j := by
    rw [mulR_mul]; rfl
  exact e ▸ h

theorem hasDerivAt_ept (H : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) (s : ℝ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun σ : ℝ => ept (mulR (aE H σ) y) k) (ept (mulR H (mulR (aE H s) y)) k) s := by
  rcases k with ⟨a, j, b⟩
  cases b
  · exact hasDerivAt_mulR H y s a j
  · exact (hasDerivAt_mulR H y s a j).star

theorem evX_eulH (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (z : Fin m → Fin n → ℂ) :
    evX (eulH H R) z = ∑ k, MvPolynomial.eval (ept z) (pderiv k R) * ept (mulR H z) k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [eulH, evX_eq, map_sum, map_add (f := _), map_mul, eval_X, eval_C]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [ept, mulR, if_true, Bool.false_eq_true, if_false, star_sum, star_mul']
  ring_nf

def trHQ (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n :=
  ∑ i, ∑ j, MvPolynomial.C (H i j) * (Qb ε true j i + Qb ε false j i)

theorem evX_Qb_add (ε : Fin m → Bool) (z : Fin m → Fin n → ℂ) (i j : Fin n) :
    evX (Qb ε true i j + Qb ε false i j) z = ∑ a, star (z a i) * z a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Qb, evX_eq, map_add (f := _), map_sum, map_mul, eval_X, ept, if_true, Bool.false_eq_true, if_false]
  convert Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => ε x = true) (fun x => star (z x i) * z x j) using 3
  ext x; simp

theorem evX_trHQ (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (z : Fin m → Fin n → ℂ) :
    evX (trHQ ε H) z = ∑ a, ∑ j, star (z a j) * mulR H z a j := by
  have e : evX (trHQ ε H) z = ∑ i, ∑ j, H i j * evX (Qb ε true j i + Qb ε false j i) z := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [trHQ, evX_eq, map_sum, map_mul, eval_C]
  rw [e]
  simp only [evX_Qb_add, mulR, Finset.mul_sum]
  calc ∑ i, ∑ j, ∑ a, H i j * (star (z a j) * z a i) = ∑ j, ∑ i, ∑ a, H i j * (star (z a j) * z a i) :=
        Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ i, H i j * (star (z a j) * z a i) := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, H i j * (star (z a j) * z a i) := Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, star (z a j) * (z a i * H i j) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem trHQ_real (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (z : Fin m → Fin n → ℂ) :
    (evX (trHQ ε H) z).im = 0 := by
  have hij : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this
  have hconj : star (evX (trHQ ε H) z) = evX (trHQ ε H) z := by
    rw [evX_trHQ]
    simp only [mulR, star_sum, star_mul', star_star, Finset.mul_sum, hij]
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ j, ∑ i, z a j * (star (z a i) * H j i) = ∑ i, ∑ j, z a j * (star (z a i) * H j i) := Finset.sum_comm
      _ = ∑ i, ∑ j, star (z a i) * (z a j * H j i) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have := congrArg Complex.im hconj
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem hasDerivAt_normSq (w : ℝ → ℂ) (w' : ℂ) (s : ℝ) (hw : HasDerivAt w w' s) :
    HasDerivAt (fun σ => ‖w σ‖ ^ 2) (2 * (star (w s) * w').re) s := by
  have hre : HasDerivAt (fun σ => (w σ).re) w'.re s := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hw
  have him : HasDerivAt (fun σ => (w σ).im) w'.im s := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hw
  have h := (hre.pow 2).add (him.pow 2)
  have e : ∀ σ, (w σ).re ^ 2 + (w σ).im ^ 2 = ‖w σ‖ ^ 2 := fun σ => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun σ => (e σ).symm)).congr_deriv ?_
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem hasDerivAt_gsE (c : ℝ) (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (y : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun σ => gs c (mulR (aE H σ) y))
      (gs c (mulR (aE H s) y) * (-(2 * (c : ℂ)) * evX (trHQ ε H) (mulR (aE H s) y))) s := by
  have hS : HasDerivAt (fun σ => ∑ a, ∑ j, ‖mulR (aE H σ) y a j‖ ^ 2)
      (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) s :=
    HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun j _ => hasDerivAt_normSq _ _ s (hasDerivAt_mulR H y s a j)
  have hg := (((hS.const_mul c).ofReal_comp).neg).cexp
  set T := evX (trHQ ε H) (mulR (aE H s) y) with hTdef
  have h0 : T.im = 0 := trHQ_real ε hH _
  have hsum : (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) = 2 * T.re := by
    rw [hTdef, evX_trHQ]
    simp only [Complex.re_sum, Finset.mul_sum]
  have hT' : ((T.re : ℝ) : ℂ) = T := Complex.ext (by simp) (by simp [h0])
  unfold gs
  refine hg.congr_deriv ?_
  simp only [Pi.neg_apply]
  rw [hsum]
  push_cast
  rw [hT']
  ring

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMA
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem aE_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H (-σ) = NormedSpace.exp (-((σ : ℂ) • H)) := by
  simp [aE, neg_smul]

theorem aE_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H (-σ) * aE H σ = 1 := by
  rw [aE_neg, aE, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem aE_mul_neg' (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H σ * aE H (-σ) = 1 := by
  rw [aE_neg, aE, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem aE_herm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : (aE H σ)ᴴ = aE H σ := by
  rw [aE, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq]
  congr 1
  simp

theorem det_aE (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : (aE H σ).det = Complex.exp ((σ : ℂ) * H.trace) := by
  rw [aE, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, smul_eq_mul]

private theorem JJ_mul_self_eq_neg_one (n : ℕ) : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp
private theorem mul_JJ_mul_conjTranspose_eq_JJ_of_inG {n : ℕ} (G Gi : M2 n) (hGi : G * Gi = 1) (hG : InG G) :
    G * JJ n * Gᴴ = JJ n := by
  have hJ := JJ_mul_self_eq_neg_one n
  have h1 : Gᴴ * JJ n = JJ n * Gi := by
    calc Gᴴ * JJ n = Gᴴ * JJ n * (G * Gi) := by rw [hGi, Matrix.mul_one]
      _ = (Gᴴ * JJ n * G) * Gi := by simp only [Matrix.mul_assoc]
      _ = JJ n * Gi := by rw [hG]
  calc G * JJ n * Gᴴ = G * JJ n * Gᴴ * (JJ n * (-JJ n)) := by
        rw [Matrix.mul_neg, hJ, neg_neg, Matrix.mul_one]
    _ = G * (JJ n * (Gᴴ * JJ n)) * (-JJ n) := by simp only [Matrix.mul_assoc]
    _ = G * ((JJ n * JJ n) * Gi) * (-JJ n) := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = JJ n := by
        rw [hJ]
        simp [hGi]
private theorem exists_GR_mR_eq_of_inG_of_inverse {n : ℕ} (M Mi : M2 n) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hM : InG M) : ∃ x : GR n, mR x = M ∧ mR x⁻¹ = Mi :=
  ⟨⟨⟨M, Mi, h1, h2⟩, hM⟩, rfl, rfl⟩
private theorem inG_JJ_mul_nU_of_isHermitian {n : ℕ} (c : Matrix (Fin n) (Fin n) ℂ) (hc : c.IsHermitian) :
    InG (JJ n * nU c) := by
  unfold InG JJ nU
  rw [fromBlocks_multiply, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hc.eq]
private theorem inG_fromBlocks_diag_of_hermitian_inverse {n : ℕ} (a a' : Matrix (Fin n) (Fin n) ℂ) (ha : a.IsHermitian)
    (ha' : a'.IsHermitian) (h : a * a' = 1) (h' : a' * a = 1) :
    InG (fromBlocks a' 0 0 a) := by
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ha.eq, ha'.eq]
  simp [h, h']

theorem cellM : CellM := by
  intro n H hH f hf g hC
  have hG : mR g = fromBlocks (toBlocks₁₁ (mR g)) (toBlocks₁₂ (mR g)) (toBlocks₂₁ (mR g))
      (toBlocks₂₂ (mR g)) := (fromBlocks_toBlocks _).symm
  set A := toBlocks₁₁ (mR g)
  set B := toBlocks₁₂ (mR g)
  set C := toBlocks₂₁ (mR g)
  set D := toBlocks₂₂ (mR g)
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  have hgi : mR g * mR g⁻¹ = 1 := congrArg mR (mul_inv_cancel g)
  have hgJ : mR g * JJ n * (mR g)ᴴ = JJ n := mul_JJ_mul_conjTranspose_eq_JJ_of_inG (mR g) (mR g⁻¹) hgi g.2
  have hCD : C * Dᴴ = D * Cᴴ := by
    have h22 := congrArg toBlocks₂₂ hgJ
    rw [hG, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h22
    simp at h22
    exact ((neg_add_eq_zero).mp h22).symm
  have hCHu : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hCu.star
  have hbH : (C⁻¹ * D).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * (Cᴴ)⁻¹ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hCu, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hCD]
      _ = C⁻¹ * D := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one]
  have hnU : ∀ c : Matrix (Fin n) (Fin n) ℂ, nU c * nU (-c) = 1 ∧ nU (-c) * nU c = 1 := by
    intro c
    constructor <;> rw [nU, nU, fromBlocks_multiply, ← fromBlocks_one] <;> simp
  have hJ := JJ_mul_self_eq_neg_one n
  have hWinv : ∀ c : Matrix (Fin n) (Fin n) ℂ,
      JJ n * nU c * (nU (-c) * -JJ n) = 1 ∧ nU (-c) * -JJ n * (JJ n * nU c) = 1 := by
    intro c
    constructor
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (nU c), (hnU c).1, Matrix.one_mul, Matrix.mul_neg, hJ,
        neg_neg]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (-JJ n), Matrix.neg_mul, hJ, neg_neg, Matrix.one_mul,
        (hnU c).2]
  obtain ⟨w₀, hw₀, hw₀i⟩ := exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (C⁻¹ * D)).1 (hWinv (C⁻¹ * D)).2
    (inG_JJ_mul_nU_of_isHermitian _ hbH)
  refine ⟨g * w₀⁻¹, C⁻¹ * D, ?_, hbH, ?_⟩
  · show toBlocks₂₁ (mR g * mR w₀⁻¹) = 0
    rw [hw₀i, hG, nU, JJ, fromBlocks_neg, fromBlocks_multiply, fromBlocks_multiply]
    simp [← Matrix.mul_assoc, mul_nonsing_inv _ hCu]
  intro p q e σ
  have h1 : aE H σ * aE H (-σ) = 1 := aE_mul_neg' H σ
  have h2 : aE H (-σ) * aE H σ = 1 := aE_mul_neg H σ
  have ha : (aE H σ).IsHermitian := aE_herm hH σ
  have ha' : (aE H (-σ)).IsHermitian := aE_herm hH (-σ)
  have hc : (aE H (-σ) * (C⁻¹ * D) * aE H (-σ)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, ha'.eq, hbH.eq, ← Matrix.mul_assoc]
  obtain ⟨mA, hmA, -⟩ := exists_GR_mR_eq_of_inG_of_inverse (fromBlocks (aE H (-σ)) 0 0 (aE H σ))
    (fromBlocks (aE H σ) 0 0 (aE H (-σ)))
    (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2])
    (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2])
    (inG_fromBlocks_diag_of_hermitian_inverse _ _ ha ha' h1 h2)
  obtain ⟨w, hw, -⟩ := exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (aE H (-σ) * (C⁻¹ * D) * aE H (-σ))).1
    (hWinv _).2 (inG_JJ_mul_nU_of_isHermitian _ hc)
  refine ⟨mA, w, ?_, ?_, hw, hc, ?_⟩
  · show toBlocks₂₁ (mR mA) = 0
    rw [hmA]
    simp
  · unfold F0 f0 u1 u2
    rw [hmA]
    simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero, zero_add, neg_zero,
      det_fromBlocks_zero₂₁]
    rw [← det_mul, h2, det_one, _root_.one_zpow, one_mul, det_aE, ← Complex.exp_int_mul,
      ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · apply Subtype.ext
    apply Units.ext
    show mR g * mR (f σ) = mR g * mR w₀⁻¹ * mR mA * mR w
    rw [hf σ, hw₀i, hmA, hw, Matrix.mul_assoc (mR g), Matrix.mul_assoc (mR g)]
    congr 1
    change fromBlocks (aE H σ) 0 0 (NormedSpace.exp (-((σ : ℂ) • H))) = _
    rw [← aE_neg, nU, nU, JJ, fromBlocks_neg]
    simp [fromBlocks_multiply, ← Matrix.mul_assoc, h1]

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem hasDerivAt_phiE (c : ℝ) (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (R : PX m n)
    (y : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun σ => evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y))
      (evX (DMp ε c H R) (mulR (aE H s) y) * gs c (mulR (aE H s) y)) s := by
  have hR : HasDerivAt (fun σ => evX R (mulR (aE H σ) y)) (evX (eulH H R) (mulR (aE H s) y)) s := by
    rw [evX_eulH]
    exact hasDerivAt_eval_curve R (fun σ => ept (mulR (aE H σ) y)) _ s
      (fun k => hasDerivAt_ept H y s k)
  refine (hR.mul (hasDerivAt_gsE c ε hH y s)).congr_deriv ?_
  simp only [DMp, trHQ, evX_eq, map_sub, map_mul, MvPolynomial.eval_C]
  ring

theorem norm_mulR_le (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    ‖mulR A y‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  calc ‖mulR A y a j‖ = ‖∑ i, y a i * A i j‖ := rfl
    _ ≤ ∑ i, ‖y a i * A i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖y‖ * ‖A i j‖ := by
        gcongr with i
        rw [norm_mul]
        gcongr
        exact (norm_le_pi_norm (y a) i).trans (norm_le_pi_norm y a)
    _ = ‖y‖ * ∑ i, ‖A i j‖ := by rw [Finset.mul_sum]
    _ ≤ ‖y‖ * ∑ i, ∑ j, ‖A i j‖ := by
        gcongr with i
        exact Finset.single_le_sum (f := fun j => ‖A i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ = _ := mul_comm _ _

theorem continuous_aE_entry (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : Continuous fun σ : ℝ => aE H σ i j :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_aE_entry H s i j).continuousAt

theorem dom_boundE (c : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℂ) (P : PX m n) (s : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, |σ - s| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  have hr0 : 0 ≤ r := by positivity
  obtain ⟨Cp, k, hCp, hP⟩ := PositivityTheory.Rg.Sw.AbsSt.DF.poly_bound P
  obtain ⟨Cd, hCd, hdec⟩ := PositivityTheory.Rg.Sw.AbsSt.DF.decay k c hc r
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := s - 1) (b := s + 1)).exists_bound_of_continuousOn
    (f := fun σ : ℝ => ∑ i, ∑ j, ‖aE H (-σ) i j‖)
    (Continuous.continuousOn (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((continuous_aE_entry H i j).comp continuous_neg).norm))
  set L' := max L 1 with hL'
  have hL'1 : 1 ≤ L' := le_max_right _ _
  have hL'0 : 0 ≤ L' := by linarith
  refine ⟨Cp * Cd * L' ^ r, mul_nonneg (mul_nonneg hCp hCd) (Real.rpow_nonneg hL'0 r),
    fun σ hσ y => ?_⟩
  set z := mulR (aE H σ) y with hz
  have hσI : σ ∈ Icc (s - 1) (s + 1) := by
    rw [abs_lt] at hσ
    constructor <;> linarith [hσ.1, hσ.2]
  have hsum : ∑ i, ∑ j, ‖aE H (-σ) i j‖ ≤ L' := by
    have := hL σ hσI
    rw [Real.norm_of_nonneg (by positivity)] at this
    exact this.trans (le_max_left _ _)
  have hy : ‖y‖ ≤ L' * ‖z‖ := by
    have hyz : y = mulR (aE H (-σ)) z := by rw [hz, mulR_mul, aE_mul_neg', mulR_one]
    calc ‖y‖ = ‖mulR (aE H (-σ)) z‖ := by rw [← hyz]
      _ ≤ (∑ i, ∑ j, ‖aE H (-σ) i j‖) * ‖z‖ := norm_mulR_le _ _
      _ ≤ L' * ‖z‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have hg : ‖gs c z‖ ≤ Real.exp (-(c * ‖z‖ ^ 2)) := by
    rw [gs, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (PositivityTheory.Rg.Sw.AbsSt.DF.sq_norm_le_sum z) hc.le))
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hmain : ‖evX P z * gs c z‖ ≤ Cp * Cd * (1 + ‖z‖) ^ (-r) := by
    rw [norm_mul]
    calc ‖evX P z‖ * ‖gs c z‖ ≤ (Cp * (1 + ‖z‖) ^ k) * Real.exp (-(c * ‖z‖ ^ 2)) :=
          mul_le_mul (hP z) hg (norm_nonneg _) (by positivity)
      _ = Cp * ((1 + ‖z‖) ^ k * Real.exp (-(c * ‖z‖ ^ 2))) := by ring
      _ ≤ Cp * (Cd * (1 + ‖z‖) ^ (-r)) := mul_le_mul_of_nonneg_left (hdec _ hz0) hCp
      _ = _ := by ring
  have hcmp : (1 + ‖z‖) ^ (-r) ≤ L' ^ r * (1 + ‖y‖) ^ (-r) := by
    have h1 : 1 + ‖y‖ ≤ L' * (1 + ‖z‖) := by nlinarith
    have h2 : (L' * (1 + ‖z‖)) ^ (-r) ≤ (1 + ‖y‖) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    rw [Real.mul_rpow hL'0 (by positivity)] at h2
    calc (1 + ‖z‖) ^ (-r) = L' ^ r * (L' ^ (-r) * (1 + ‖z‖) ^ (-r)) := by
          rw [← mul_assoc, ← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ L' ^ r * (1 + ‖y‖) ^ (-r) := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hL'0 r)
  calc ‖evX P z * gs c z‖ ≤ Cp * Cd * (1 + ‖z‖) ^ (-r) := hmain
    _ ≤ Cp * Cd * (L' ^ r * (1 + ‖y‖) ^ (-r)) :=
        mul_le_mul_of_nonneg_left hcmp (mul_nonneg hCp hCd)
    _ = _ := by ring

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem gram_eq (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) :
    gramX ε x = (Matrix.of x)ᴴ * diagonal (sgn ε) * Matrix.of x := by
  ext i j
  rw [gramX_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem gramX_mulR (ε : Fin m → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    gramX ε (mulR A y) = Aᴴ * gramX ε y * A := by
  have e : Matrix.of (mulR A y) = Matrix.of y * A := by
    ext a j; simp [mulR, Matrix.mul_apply]
  rw [gram_eq, gram_eq, e, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem trace_herm_re {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : ((H.trace.re : ℝ) : ℂ) = H.trace := by
  have him : H.trace.im = 0 := by
    simp only [Matrix.trace, Matrix.diag, Complex.im_sum]
    exact Finset.sum_eq_zero fun i _ => Complex.conj_eq_iff_im.mp (hH.apply i i)
  exact Complex.ext (by simp) (by simp [him])

def Psi (ε : Fin m → Bool) (c t : ℝ) (H b : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (σ : ℝ) : ℂ :=
  ∫ y, evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) * Complex.exp (Complex.I * t * (b * gramX ε y).trace)

theorem secN_aE (ε : Fin m → Bool) (c t : ℝ) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (b : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (σ : ℝ) :
    secN ε c t R (aE H (-σ) * b * aE H (-σ)) =
      Complex.exp (((2 * m * σ * H.trace.re : ℝ) : ℂ)) * Psi ε c t H b R σ := by
  have hdet : (aE H σ).det ≠ 0 := by
    rw [det_aE]
    exact Complex.exp_ne_zero _
  have hr : Complex.normSq (aE H σ).det ^ m = Real.exp (2 * m * σ * H.trace.re) := by
    rw [det_aE, Complex.normSq_eq_norm_sq, Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    simp only [Complex.re_ofReal_mul]
    push_cast
    ring
  unfold secN Psi
  rw [coV m n (aE H σ) hdet, hr, Complex.ofReal_exp]
  congr 1
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [gramX_mulR, aE_herm hH]
  have e1 : aE H (-σ) * b * aE H (-σ) * (aE H σ * gramX ε y * aE H σ) =
      aE H (-σ) * (b * gramX ε y * aE H σ) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (aE H (-σ)) (aE H σ), aE_mul_neg, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, Matrix.mul_assoc, aE_mul_neg', Matrix.mul_one]

private theorem continuous_evX_gs_exp_trace_mulR_aE (ε : Fin m → Bool) (c t : ℝ) (H b : Matrix (Fin n) (Fin n) ℂ)
    (P : PX m n) (σ : ℝ) :
    Continuous fun y : Fin m → Fin n → ℂ => evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
  have hm : Continuous fun y : Fin m → Fin n → ℂ => mulR (aE H σ) y := by
    unfold mulR
    refine continuous_pi fun a => continuous_pi fun j => ?_
    exact continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp (continuous_apply a) :
        Continuous fun y : Fin m → Fin n → ℂ => y a i)).mul continuous_const
  refine (((continuous_evX P).comp hm).mul ((continuous_gs c).comp hm)).mul ?_
  exact Complex.continuous_exp.comp
    (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace))

private theorem exists_norm_evX_gs_exp_le_polynomial_decay (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (P : PX m n)
    (s : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, |σ - s| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
          Complex.exp (Complex.I * t * (b * gramX ε y).trace)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  obtain ⟨K, hK0, hK⟩ := dom_boundE c hc H P s
  refine ⟨K, hK0, fun σ hσ y => ?_⟩
  have hE : ‖Complex.exp (Complex.I * t * (b * gramX ε y).trace)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, trace_im ε y hb]
  rw [norm_mul, hE, mul_one]
  exact hK σ hσ y

theorem hasDerivAt_Psi (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (R : PX m n) (s : ℝ) :
    HasDerivAt (Psi ε c t H b R) (Psi ε c t H b (DMp ε c H R) s) s ∧
      ∀ P : PX m n, Integrable fun y => evX P (mulR (aE H s) y) * gs c (mulR (aE H s) y) *
        Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have hd : ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℕ) : ℝ) <
      (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 := by linarith
  have hint : ∀ P : PX m n, Integrable fun y => evX P (mulR (aE H s) y) * gs c (mulR (aE H s) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
    intro P
    obtain ⟨K, hK0, hK⟩ := exists_norm_evX_gs_exp_le_polynomial_decay ε hc t H hb P s
    exact ((integrable_one_add_norm hd).const_mul K).mono'
      (continuous_evX_gs_exp_trace_mulR_aE ε c t H b P s).aestronglyMeasurable
      (ae_of_all _ fun y => hK s (by simp) y)
  refine ⟨?_, hint⟩
  obtain ⟨K, hK0, hK⟩ := exists_norm_evX_gs_exp_le_polynomial_decay ε hc t H hb (DMp ε c H R) s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun σ y => evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace))
    (F' := fun σ y => evX (DMp ε c H R) (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace))
    (bound := fun y => K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)))
    (x₀ := s) (s := Metric.ball s 1) (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun σ => (continuous_evX_gs_exp_trace_mulR_aE ε c t H b R σ).aestronglyMeasurable)
    (hint R) (continuous_evX_gs_exp_trace_mulR_aE ε c t H b (DMp ε c H R) s).aestronglyMeasurable
    (ae_of_all _ fun y σ hσ => hK σ (by rwa [Metric.mem_ball, Real.dist_eq] at hσ) y)
    ((integrable_one_add_norm hd).const_mul K)
    (ae_of_all _ fun y σ _ => (hasDerivAt_phiE c ε hH R y σ).mul_const _)
  exact key.2

theorem evX_DM (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (z : Fin m → Fin n → ℂ) :
    evX (DM ε c H R) z = ((m : ℂ) * H.trace) * evX R z + evX (DMp ε c H R) z := by
  have h : DM ε c H R = C ((m : ℂ) * H.trace) * R + DMp ε c H R := by
    simp only [DM, DMp]
    ring
  rw [h, evX_eq, evX_eq, evX_eq, map_add (f := _), map_mul, eval_C]

end PositivityTheory.Rg.Sw.AbsSt.SDM

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SDM

theorem mDer : MDer := by
  intro m n ε c t p q e sL ρ hL R H hH f hf g hg s
  obtain ⟨C0, -, hcell⟩ := hL.cell
  obtain ⟨y₁, b, hy₁, hb, hdec⟩ := cellM n H hH f hf g hg
  have hpq : (p : ℂ) + q = m := by
    rcases hL.sign with ⟨_, hp, hq⟩ | ⟨_, hp, hq⟩
    · rw [hp, hq]
      exact_mod_cast DF.cnt_add ε
    · rw [hp, hq, add_comm]
      exact_mod_cast DF.cnt_add ε
  have hrep : ∀ (P : PX m n) (σ : ℝ), sL P (g * f σ) =
      F0 p q e y₁ * C0 * (Complex.exp (↑σ * (↑m * H.trace)) * Psi ε c t H b P σ) := by
    intro P σ
    obtain ⟨mA, w, hmA, hF0, hw, hb', heq⟩ := hdec p q e σ
    have hex : Complex.exp (-(↑σ * ↑(p + q) * H.trace)) *
        Complex.exp (((2 * m * σ * H.trace.re : ℝ) : ℂ)) = Complex.exp (↑σ * (↑m * H.trace)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      rw [trace_herm_re hH]
      linear_combination (-(σ : ℂ) * H.trace) * hpq
    rw [heq, mul_assoc y₁ mA w, hL.law P y₁ _ hy₁, hL.law P mA w hmA, hcell P w _ hb' hw,
      secN_aE ε c t hH b P σ, hF0, ← hex]
    ring
  have hΨ := hasDerivAt_Psi ε hL.cpos t hH hb R s
  have hE : HasDerivAt (fun σ : ℝ => Complex.exp (↑σ * (↑m * H.trace)))
      (Complex.exp (↑s * (↑m * H.trace)) * (↑m * H.trace)) s := by
    have h1 := ((hasDerivAt_id s).ofReal_comp.mul_const ((m : ℂ) * H.trace)).cexp
    simpa using h1
  have hfun : (fun σ : ℝ => sL R (g * f σ)) = fun σ =>
      F0 p q e y₁ * C0 * (Complex.exp (↑σ * (↑m * H.trace)) * Psi ε c t H b R σ) := funext (hrep R)
  have hlin : Psi ε c t H b (DM ε c H R) s =
      (↑m * H.trace) * Psi ε c t H b R s + Psi ε c t H b (DMp ε c H R) s := by
    unfold Psi
    rw [← integral_const_mul, ← integral_add ((hΨ.2 R).const_mul _) (hΨ.2 _)]
    congr 1
    funext y
    rw [evX_DM]
    ring
  rw [hfun, hrep (DM ε c H R) s, hlin]
  exact ((hE.mul hΨ.1).const_mul (F0 p q e y₁ * C0)).congr_deriv (by ring)

end PositivityTheory.Rg.Sw.AbsSt
