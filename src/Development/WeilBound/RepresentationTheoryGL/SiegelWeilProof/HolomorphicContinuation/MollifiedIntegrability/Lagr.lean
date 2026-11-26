module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Lagr
noncomputable section

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

def Twist : Prop :=
  ∀ (n : ℕ) (H : E n → ℂ), ContDiff ℝ (⊤ : ℕ∞) H → ∀ N : ℕ, ∃ G : ℕ → E n → ℂ,
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ ∀ (z : ℂ) (y : E n),
      (Delta^[N] (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * H y)) y =
        ((dP y : ℝ) : ℂ) ^ (-z) * ∑ j ∈ Finset.range (n * N + 1), z ^ j * G j y

def Lagr : Prop :=
  ∀ D : ℕ, ∃ C : ℝ, ∀ (c : ℕ → ℂ) (B : ℝ), (∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * c j‖ ≤ B) →
    ∀ j ≤ D, ‖c j‖ ≤ C * B

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.HermTranspose
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBaseB
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBaseA
noncomputable section

open MeasureTheory Complex

namespace PositivityTheory.Rg.Sw.WR.G.GB

theorem gauss_one (w : ℂ) (hw : 0 < w.re) :
    ∫ z : ℂ, cexp (-(w * ((‖z‖ ^ 2 : ℝ) : ℂ))) = (Real.pi : ℂ) / w := by
  have h := Complex.volume_preserving_equiv_real_prod.symm
  rw [← h.integral_comp' (g := fun z : ℂ => cexp (-(w * ((‖z‖ ^ 2 : ℝ) : ℂ))))]
  have e : ∀ p : ℝ × ℝ, cexp (-(w * ((‖measurableEquivRealProd.symm p‖ ^ 2 : ℝ) : ℂ))) =
      cexp (-w * (p.1 : ℂ) ^ 2) * cexp (-w * (p.2 : ℂ) ^ 2) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    rw [measurableEquivRealProd_symm_apply, Complex.sq_norm, Complex.normSq_apply]
    push_cast
    ring
  simp_rw [e]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    integral_prod_mul (fun x : ℝ => cexp (-w * (x : ℂ) ^ 2)) (fun x : ℝ => cexp (-w * (x : ℂ) ^ 2)),
    integral_gaussian_complex hw]
  have hne : (Real.pi : ℂ) / w ≠ 0 := by
    have : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) this
  rw [← Complex.cpow_add _ _ hne]
  norm_num

theorem gauss_diag {n : ℕ} (d : Fin n → ℂ) (hd : ∀ k, 0 < (d k).re) :
    ∫ r : Fin n → ℂ, cexp (-∑ k, d k * ((‖r k‖ ^ 2 : ℝ) : ℂ)) = ∏ k, (Real.pi : ℂ) / d k := by
  have e : ∀ r : Fin n → ℂ, cexp (-∑ k, d k * ((‖r k‖ ^ 2 : ℝ) : ℂ)) =
      ∏ k, cexp (-(d k * ((‖r k‖ ^ 2 : ℝ) : ℂ))) := by
    intro r
    rw [← Complex.exp_sum, Finset.sum_neg_distrib]
  simp_rw [e]
  rw [integral_fintype_prod_volume_eq_prod (fun k (z : ℂ) => cexp (-(d k * ((‖z‖ ^ 2 : ℝ) : ℂ))))]
  exact Finset.prod_congr rfl fun k _ => gauss_one (d k) (hd k)

end PositivityTheory.Rg.Sw.WR.G.GB
end
end

noncomputable section

open MeasureTheory Complex Matrix

namespace PositivityTheory.Rg.Sw.WR.G.GB

variable {n : ℕ}

theorem normSq_det_unitary (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Complex.normSq U.det = 1 := by
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.mp hU)
  rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at h
  have h2 : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  exact_mod_cast h2

theorem integral_unitary (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℂ) : ∫ r, g (U *ᵥ r) = ∫ r, g r := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  let eC : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
    LinearEquiv.ofLinear (Matrix.toLin' U) (Matrix.toLin' (star U))
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  let eR : (Fin n → ℂ) ≃ₗ[ℝ] (Fin n → ℂ) := eC.restrictScalars ℝ
  let e : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) := eR.toContinuousLinearEquiv
  let me : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) := e.toHomeomorph.toMeasurableEquiv
  have hcoe : ∀ r, me r = U *ᵥ r := fun r => by
    simp [me, e, eR, eC, Matrix.toLin'_apply]
  have hdet : LinearMap.det ((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars]
    have : (eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = Matrix.toLin' U := rfl
    rw [this, LinearMap.det_toLin', Algebra.norm_complex_apply, normSq_det_unitary U hU]
  have hmap : Measure.map (((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ)) volume =
      (volume : Measure (Fin n → ℂ)) := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  have hpres : MeasurePreserving me volume volume := by
    refine ⟨me.measurable, ?_⟩
    have : (me : (Fin n → ℂ) → (Fin n → ℂ)) =
        (((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) : (Fin n → ℂ) → (Fin n → ℂ)) := by
      funext r; rw [hcoe r]; simp [eC, Matrix.toLin'_apply]
    rw [this, hmap]
  have := hpres.integral_comp' g
  simpa [hcoe] using this

theorem gauss_row (c τ : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ∫ r : Fin n → ℂ, cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * τ * ∑ i, ∑ j, star (r i) * H i j * r j) =
      (Real.pi : ℂ) ^ n / ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H).det := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ := (hH.eigenvectorUnitary).2
  set lam : Fin n → ℂ := RCLike.ofReal ∘ hH.eigenvalues with hlam
  have hspec : H = U * Matrix.diagonal lam * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hV : star U ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact h2)

  set G : (Fin n → ℂ) → ℂ := fun r' => cexp (-∑ k, ((c : ℂ) - Complex.I * τ * lam k) * ((‖r' k‖ ^ 2 : ℝ) : ℂ))
    with hG
  have hpt : ∀ r : Fin n → ℂ, cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
      Complex.I * τ * ∑ i, ∑ j, star (r i) * H i j * r j) = G (star U *ᵥ r) := by
    intro r
    simp only [hG]
    congr 1
    have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]; rfl
    have e1 : ∑ i, ∑ j, star (r i) * H i j * r j = star r ⬝ᵥ (H *ᵥ r) := by
      simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
    have e2 : star r ⬝ᵥ (H *ᵥ r) = star (star U *ᵥ r) ⬝ᵥ (Matrix.diagonal lam *ᵥ (star U *ᵥ r)) := by
      rw [hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
      congr 1
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    have e3 : star r ⬝ᵥ r = star (star U *ᵥ r) ⬝ᵥ (star U *ᵥ r) := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mulVec]
    have hn' : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = star z * z := fun z => by rw [← hn z]; push_cast; ring
    have e4 : (((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) = (c : ℂ) * (star r ⬝ᵥ r) := by
      push_cast
      simp only [dotProduct, Pi.star_apply, hn']
    rw [e4, e1, e2, e3]
    simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal, hn, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_unitary (star U) hV G]
  simp only [hG]
  rw [gauss_diag (fun k => (c : ℂ) - Complex.I * τ * lam k) (fun k => by simp [hlam, hc])]
  have hdet : ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H).det =
      ∏ k, ((c : ℂ) - Complex.I * τ * lam k) := by
    have : (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H =
        U * Matrix.diagonal (fun k => (c : ℂ) - Complex.I * τ * lam k) * star U := by
      rw [hspec]
      have hd : Matrix.diagonal (fun k => (c : ℂ) - Complex.I * τ * lam k) =
          (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • Matrix.diagonal lam := by
        ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
      rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h1,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hdu : U.det * (star U).det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
    calc (U.det * ∏ k, ((c : ℂ) - Complex.I * τ * lam k)) * (star U).det
        = (U.det * (star U).det) * ∏ k, ((c : ℂ) - Complex.I * τ * lam k) := by ring
      _ = _ := by rw [hdu, one_mul]
  rw [hdet, Finset.prod_div_distrib]
  simp

end PositivityTheory.Rg.Sw.WR.G.GB
end
end

noncomputable section

open MeasureTheory Complex Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

namespace GB

def sgnR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sgnR ε a : ℝ) : ℂ) := by
  unfold sgn sgnR; split_ifs <;> simp

theorem evX_Qb (ε : Fin m → Bool) (bb : Bool) (i j : Fin n) (x : Fin m → Fin n → ℂ) :
    evX (Qb ε bb i j) x = ∑ a ∈ Finset.univ.filter (fun a => ε a = bb), star (x a i) * x a j := by
  simp [evX, Qb]

theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, ((sgnR ε a : ℝ) : ℂ) * (star (x a i) * x a j) := by
  unfold gramX
  rw [Qp, evX, map_sub, ← evX, ← evX, evX_Qb, evX_Qb, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sgnR
  cases h : ε a <;> simp

theorem trace_gram (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, ((sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j := by
  have L : (b * gramX ε x).trace =
      ∑ a, ∑ i, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_apply, Finset.mul_sum]
    calc (∑ i, ∑ j, ∑ a, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)))
        = ∑ i, ∑ a, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [L]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.transpose_apply]
  ring

theorem herm_transpose (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : bᵀ.IsHermitian := by
  ext i j
  have := congrFun (congrFun hb j) i
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at this ⊢
  rw [← this]

end GB

open GB in
theorem base : Base := by
  intro m n ε c t hc b hb
  unfold secN
  have hpt : ∀ x : Fin m → Fin n → ℂ, evX 1 x * gs c x * cexp (Complex.I * t * (b * gramX ε x).trace) =
      ∏ a, cexp (-(((c * ∑ k, ‖x a k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j) := by
    intro x
    have h1 : evX (1 : PX m n) x = 1 := by simp [evX]
    rw [h1, one_mul, gs, ← Complex.exp_add, ← Complex.exp_sum, trace_gram]
    congr 1
    rw [Finset.sum_add_distrib]
    congr 1
    · push_cast
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast
      ring
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun a (r : Fin n → ℂ) => cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (r i) * bᵀ i j * r j))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [GB.gauss_row c (t * sgnR ε a) hc bᵀ (herm_transpose b hb)]
  have e : Complex.I * ((t * sgnR ε a : ℝ) : ℂ) = Complex.I * t * sgn ε a := by
    rw [sgn_eq]; push_cast; ring
  rw [e]
  rfl

end PositivityTheory.Rg.Sw.WR.G
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousEvXI
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisMore
theorem UpperTheory.Reformulated.B.DYka1.main :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by positivity
  have hle : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    calc ‖x a i‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun j : Fin n => ‖x a j‖ ^ (2 : ℕ))
            (fun j _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ b : Fin m, ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun b : Fin m => ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ))
            (fun b _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ a)
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by
        gcongr
    _ = ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := Real.sq_sqrt hS
end

noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem norm_coord_le (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) : ‖x a i‖ ≤ ‖x‖ :=
  (norm_le_pi_norm (x a) i).trans (norm_le_pi_norm x a)

theorem continuous_evXI (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  unfold evX
  have hg : Continuous fun x : Fin m → Fin n → ℂ =>
      (fun k : Fin m × Fin n × Bool => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1) := by
    refine continuous_pi fun k => ?_
    by_cases h : k.2.2
    · simp only [h, if_true]
      exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
    · simp only [h, if_false, Bool.false_eq_true]
      exact (continuous_apply _).comp (continuous_apply _)
  exact (MvPolynomial.continuous_eval P).comp hg

theorem continuous_gs (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  unfold gs
  fun_prop

theorem evX_bound (P : PX m n) : ∃ (C : ℝ) (d : ℕ), ∀ x : Fin m → Fin n → ℂ, ‖evX P x‖ ≤ C * (1 + ‖x‖) ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, fun x => by simp [evX]⟩
  | add p q hp hq =>
    obtain ⟨C1, d1, h1⟩ := hp
    obtain ⟨C2, d2, h2⟩ := hq
    refine ⟨|C1| + |C2|, d1 + d2, fun x => ?_⟩
    have h0 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have e1 : (1 + ‖x‖) ^ d1 ≤ (1 + ‖x‖) ^ (d1 + d2) := pow_le_pow_right₀ h0 (by omega)
    have e2 : (1 + ‖x‖) ^ d2 ≤ (1 + ‖x‖) ^ (d1 + d2) := pow_le_pow_right₀ h0 (by omega)
    have f1 : C1 * (1 + ‖x‖) ^ d1 ≤ |C1| * (1 + ‖x‖) ^ (d1 + d2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity)).trans
        (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
    have f2 : C2 * (1 + ‖x‖) ^ d2 ≤ |C2| * (1 + ‖x‖) ^ (d1 + d2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)).trans
        (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
    calc ‖evX (p + q) x‖ ≤ ‖evX p x‖ + ‖evX q x‖ := by
          simp only [evX, map_add (f := _)]; exact norm_add_le _ _
      _ ≤ C1 * (1 + ‖x‖) ^ d1 + C2 * (1 + ‖x‖) ^ d2 := add_le_add (h1 x) (h2 x)
      _ ≤ |C1| * (1 + ‖x‖) ^ (d1 + d2) + |C2| * (1 + ‖x‖) ^ (d1 + d2) := add_le_add f1 f2
      _ = (|C1| + |C2|) * (1 + ‖x‖) ^ (d1 + d2) := by ring
  | mul_X p v hp =>
    obtain ⟨C, d, h⟩ := hp
    refine ⟨|C|, d + 1, fun x => ?_⟩
    have hv : ‖(if v.2.2 then star (x v.1 v.2.1) else x v.1 v.2.1)‖ ≤ 1 + ‖x‖ := by
      have := norm_coord_le x v.1 v.2.1
      by_cases hb : v.2.2 <;> simp [hb] <;> linarith
    have hC : ‖evX p x‖ ≤ |C| * (1 + ‖x‖) ^ d :=
      (h x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    calc ‖evX (p * MvPolynomial.X v) x‖
        = ‖evX p x‖ * ‖(if v.2.2 then star (x v.1 v.2.1) else x v.1 v.2.1)‖ := by
          by_cases hb : v.2.2 <;> simp [evX, hb]
      _ ≤ (|C| * (1 + ‖x‖) ^ d) * (1 + ‖x‖) := mul_le_mul hC hv (norm_nonneg _) (by positivity)
      _ = |C| * (1 + ‖x‖) ^ (d + 1) := by ring

theorem sq_norm_le_sum (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.DYka1.main x

theorem norm_gs_le (c : ℝ) (hc : 0 < c) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
  unfold gs
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  exact Real.exp_le_exp.2 (by nlinarith [sq_norm_le_sum x])

theorem decay (c : ℝ) (hc : 0 < c) (k : ℕ) : ∃ K : ℝ, ∀ s : ℝ, 0 ≤ s → (1 + s) ^ (2 * k) * Real.exp (-(c * s ^ 2)) ≤ K := by
  refine ⟨4 ^ k * (1 + (k.factorial : ℝ) / c ^ k), fun s hs => ?_⟩
  have hpow : (1 + s) ^ (2 * k) ≤ 4 ^ k * (1 + s ^ (2 * k)) := by
    rcases le_total s 1 with h | h
    · calc (1 + s) ^ (2 * k) ≤ 2 ^ (2 * k) := pow_le_pow_left₀ (by linarith) (by linarith) _
        _ = 4 ^ k := by rw [pow_mul]; norm_num
        _ ≤ 4 ^ k * (1 + s ^ (2 * k)) := by
          have : 0 ≤ s ^ (2 * k) := by positivity
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) k]
    · calc (1 + s) ^ (2 * k) ≤ (2 * s) ^ (2 * k) := pow_le_pow_left₀ (by linarith) (by linarith) _
        _ = 4 ^ k * s ^ (2 * k) := by rw [mul_pow, pow_mul]; norm_num
        _ ≤ 4 ^ k * (1 + s ^ (2 * k)) := by
          have : 0 ≤ (4:ℝ) ^ k := by positivity
          nlinarith
  have hexp : s ^ (2 * k) ≤ (k.factorial : ℝ) / c ^ k * Real.exp (c * s ^ 2) := by
    have h1 := Real.pow_div_factorial_le_exp (c * s ^ 2) (by positivity) k
    have hck : 0 < c ^ k := pow_pos hc k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ hf] at h1
    rw [pow_mul, div_mul_eq_mul_div, le_div_iff₀ hck]
    calc (s ^ 2) ^ k * c ^ k = (c * s ^ 2) ^ k := by ring
      _ ≤ Real.exp (c * s ^ 2) * k.factorial := h1
      _ = k.factorial * Real.exp (c * s ^ 2) := by ring
  have he : 0 < Real.exp (-(c * s ^ 2)) := Real.exp_pos _
  have hee : Real.exp (c * s ^ 2) * Real.exp (-(c * s ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h1le : 1 ≤ Real.exp (c * s ^ 2) := Real.one_le_exp (by positivity)
  calc (1 + s) ^ (2 * k) * Real.exp (-(c * s ^ 2))
      ≤ 4 ^ k * (1 + s ^ (2 * k)) * Real.exp (-(c * s ^ 2)) := mul_le_mul_of_nonneg_right hpow he.le
    _ ≤ 4 ^ k * (Real.exp (c * s ^ 2) + (k.factorial : ℝ) / c ^ k * Real.exp (c * s ^ 2)) *
          Real.exp (-(c * s ^ 2)) := by gcongr
    _ = 4 ^ k * (1 + (k.factorial : ℝ) / c ^ k) * (Real.exp (c * s ^ 2) * Real.exp (-(c * s ^ 2))) := by ring
    _ = 4 ^ k * (1 + (k.factorial : ℝ) / c ^ k) := by rw [hee, mul_one]

instance haarNested (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := by
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  have : SigmaFinite (volume : Measure (Fin n → ℂ)) := inferInstance
  exact Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite

theorem intG : IntG := by
  intro m n c hc P
  obtain ⟨C, d, hP⟩ := evX_bound P
  set r : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hr
  obtain ⟨K, hK⟩ := decay c hc (d + r)
  have hint : Integrable (fun x : Fin m → Fin n → ℂ => (1 + ‖x‖) ^ (-(r : ℝ))) :=
    integrable_one_add_norm (by rw [hr]; push_cast; linarith)
  refine (hint.const_mul (|C| * K)).mono' ((continuous_evXI P).mul (continuous_gs c)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hpos : 0 < 1 + ‖x‖ := by linarith
  have hK' : (1 + ‖x‖) ^ (d + r) * Real.exp (-(c * ‖x‖ ^ 2)) ≤ K :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (by omega)) (Real.exp_pos _).le).trans
      (hK ‖x‖ (norm_nonneg x))
  have hrp : (1 + ‖x‖) ^ (-(r : ℝ)) = ((1 + ‖x‖) ^ r)⁻¹ := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
  have hPx : ‖evX P x‖ ≤ |C| * (1 + ‖x‖) ^ d :=
    (hP x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hr0 : 0 < (1 + ‖x‖) ^ r := pow_pos hpos r
  rw [norm_mul, hrp]
  calc ‖evX P x‖ * ‖gs c x‖ ≤ (|C| * (1 + ‖x‖) ^ d) * Real.exp (-(c * ‖x‖ ^ 2)) :=
        mul_le_mul hPx (norm_gs_le c hc x) (norm_nonneg _) (by positivity)
    _ = |C| * ((1 + ‖x‖) ^ (d + r) * Real.exp (-(c * ‖x‖ ^ 2))) * ((1 + ‖x‖) ^ r)⁻¹ := by
        rw [pow_add]; field_simp
    _ ≤ |C| * K * ((1 + ‖x‖) ^ r)⁻¹ := by
        gcongr

end PositivityTheory.Rg.Sw.WR.D
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousGramX
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.NormMono
noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G.GI

open PositivityTheory.Rg.Sw

lemma abs_pow_exp (b : ℝ) (hb : 0 < b) (k : ℕ) :
    Integrable fun x : ℝ => |x| ^ k * Real.exp (-b * x ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ))
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  simp_rw [Real.rpow_natCast] at h
  refine h.norm.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) : (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ k ≤ (2 * b) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * b ^ k := mul_pow 2 b k
      _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
          have := pow_nonneg ha k
          gcongr; linarith
  · calc (a + b) ^ k ≤ (2 * a) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * a ^ k := mul_pow 2 a k
      _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
          have := pow_nonneg hb k
          gcongr; linarith

lemma cplx (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Integrable fun z : ℂ => ‖z‖ ^ k * Real.exp (-c * ‖z‖ ^ 2) := by
  have hP : Integrable (fun p : ℝ × ℝ => (2 : ℝ) ^ k * ((|p.1| ^ k * Real.exp (-c * p.1 ^ 2)) *
      Real.exp (-c * p.2 ^ 2) + Real.exp (-c * p.1 ^ 2) * (|p.2| ^ k * Real.exp (-c * p.2 ^ 2)))) := by
    refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · exact (abs_pow_exp c hc k).mul_prod (integrable_exp_neg_mul_sq hc)
    · exact (integrable_exp_neg_mul_sq hc).mul_prod (abs_pow_exp c hc k)
  have hC : Integrable (fun z : ℂ => (2 : ℝ) ^ k * ((|z.re| ^ k * Real.exp (-c * z.re ^ 2)) *
      Real.exp (-c * z.im ^ 2) + Real.exp (-c * z.re ^ 2) * (|z.im| ^ k * Real.exp (-c * z.im ^ 2)))) := by
    have := (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hP
    simpa [Function.comp_def, Complex.measurableEquivRealProd] using this
  refine hC.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have he : Real.exp (-c * ‖z‖ ^ 2) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2) := by
    rw [hz, ← Real.exp_add]; ring_nf
  have h1 : ‖z‖ ^ k ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k) :=
    (pow_le_pow_left₀ (norm_nonneg z) (Complex.norm_le_abs_re_add_abs_im z) k).trans
      (add_pow_le _ _ (abs_nonneg _) (abs_nonneg _) k)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), he]
  have e1 := Real.exp_pos (-c * z.re ^ 2)
  have e2 := Real.exp_pos (-c * z.im ^ 2)
  calc ‖z‖ ^ k * (Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2))
      ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k) * (Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)) := by
        gcongr
    _ = _ := by ring

lemma prodG (m n : ℕ) (c : ℝ) (hc : 0 < c) (D : Fin m → Fin n → ℕ) :
    Integrable fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, (‖x a i‖ ^ D a i * Real.exp (-c * ‖x a i‖ ^ 2)) := by
  refine Integrable.fintype_prod (f := fun a (r : Fin n → ℂ) => ∏ i, (‖r i‖ ^ D a i * Real.exp (-c * ‖r i‖ ^ 2)))
    (μ := fun _ => volume) (fun a => ?_)
  exact Integrable.fintype_prod (f := fun i (z : ℂ) => ‖z‖ ^ D a i * Real.exp (-c * ‖z‖ ^ 2))
    (μ := fun _ => volume) (fun i => cplx c hc _)

abbrev fx {m n : ℕ} (x : Fin m → Fin n → ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

lemma continuous_evX {m n : ℕ} (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  have : Continuous fun x : Fin m → Fin n → ℂ => fx x := by
    refine continuous_pi fun k => ?_
    by_cases h : k.2.2
    · simp only [fx, h, if_true]; fun_prop
    · simp only [fx, h, if_false, Bool.false_eq_true]; fun_prop
  exact (MvPolynomial.continuous_eval P).comp this

lemma continuous_gs {m n : ℕ} (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  unfold gs; fun_prop

lemma norm_gs {m n : ℕ} (c : ℝ) (x : Fin m → Fin n → ℂ) :
    ‖gs c x‖ = ∏ a, ∏ i, Real.exp (-c * ‖x a i‖ ^ 2) := by
  unfold gs
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  have : -(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) = ∑ a, ∑ i, (-c * ‖x a i‖ ^ 2) := by
    simp [Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
  rw [this, Real.exp_sum]
  exact Finset.prod_congr rfl fun a _ => Real.exp_sum _ _

lemma norm_mono {m n : ℕ} (d : (Fin m × Fin n × Bool) →₀ ℕ) (x : Fin m → Fin n → ℂ) :
    ‖evX (monomial d 1) x‖ = ∏ a, ∏ i, ‖x a i‖ ^ (d (a, i, false) + d (a, i, true)) := by
  unfold evX
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, norm_prod]
  simp_rw [norm_pow]
  rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
    simp [Finsupp.notMem_support_iff.mp hk])]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool]
  simp [pow_add, mul_comm]

theorem integP : IntegP := by
  intro m n c hc P
  have key : ∀ d : (Fin m × Fin n × Bool) →₀ ℕ,
      Integrable fun x : Fin m → Fin n → ℂ => evX (monomial d 1) x * gs c x := by
    intro d
    refine (prodG m n c hc (fun a i => d (a, i, false) + d (a, i, true))).mono'
      ((continuous_evX _).mul (continuous_gs c)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    rw [norm_mul, norm_mono, norm_gs, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_mul_distrib]
  have hP : (fun x => evX P x * gs c x) =
      fun x => ∑ d ∈ P.support, AddMonoidAlgebra.coeff P d * (evX (monomial d 1) x * gs c x) := by
    funext x
    simp only [evX]
    rw [MvPolynomial.eval_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, mul_assoc]
  rw [hP]
  exact integrable_finsetSum _ fun d _ => (key d).const_mul _

end PositivityTheory.Rg.Sw.WR.G.GI
end
end

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

theorem integP : IntegP := GI.integP

lemma map_smul_volume {m n : ℕ} (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    Measure.map (fun x : Fin m → Fin n → ℂ => ζ • x) volume = volume := by
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) :=
    ((ζ • LinearMap.id : (Fin m → Fin n → ℂ) →ₗ[ℂ] (Fin m → Fin n → ℂ))).restrictScalars ℝ
  have hdet : LinearMap.det L = 1 := by
    simp only [L]
    rw [LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Algebra.norm_complex_apply, map_pow, Complex.normSq_eq_norm_sq, hζ]
    simp
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → Fin n → ℂ)))
    (f := L) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at this
  calc Measure.map (fun x : Fin m → Fin n → ℂ => ζ • x) volume = Measure.map (⇑L) volume := rfl
    _ = volume := by rw [this]; simp

lemma evX_smul_mono {m n : ℕ} (ζ : ℂ) (d : (Fin m × Fin n × Bool) →₀ ℕ) (hd : ∀ k, k.2.2 = true → d k = 0)
    (x : Fin m → Fin n → ℂ) :
    evX (monomial d 1) (ζ • x) = ζ ^ (d.sum fun _ e => e) * evX (monomial d 1) x := by
  unfold evX
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, one_mul, one_mul, Finsupp.prod, Finsupp.prod,
    Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk2 : k.2.2 = false := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hk) (hd k (by simpa using h))
  simp [hk2, mul_pow]

lemma gs_smul {m n : ℕ} (c : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) : gs c (ζ • x) = gs c x := by
  unfold gs
  simp [hζ]

lemma gramX_smul {m n : ℕ} (ε : Fin m → Bool) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) :
    gramX ε (ζ • x) = gramX ε x := by
  have h1 : (starRingEnd ℂ) ζ * ζ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ]; simp
  have key : ∀ u v : ℂ, (starRingEnd ℂ) (ζ * u) * (ζ * v) = (starRingEnd ℂ) u * v := by
    intro u v
    rw [map_mul]
    linear_combination ((starRingEnd ℂ) u * v) * h1
  ext _i _j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, evX, Qp, Qb, map_sub, map_sum, map_mul, MvPolynomial.eval_X]
  congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_ <;>
    simp only [Pi.smul_apply, smul_eq_mul, Bool.false_eq_true, if_true, if_false] <;>
    exact key _ _

lemma continuous_gramX {m n : ℕ} (ε : Fin m → Bool) : Continuous fun x : Fin m → Fin n → ℂ => gramX ε x :=
  continuous_pi fun i => continuous_pi fun j => GI.continuous_evX _

theorem rot : Rot := by
  intro m n ε c t hc b hb d hd hd0
  set N := d.sum fun _ e => e with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply hd0
    ext k
    have := (Finset.sum_eq_zero_iff.mp h) k
    by_cases hk : k ∈ d.support
    · simpa using this hk
    · simpa using hk
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  set ζ : ℂ := Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I) with hζdef
  have hζ : ‖ζ‖ = 1 := by rw [hζdef, Complex.norm_exp_ofReal_mul_I]
  have hζN : ζ ^ N = -1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    have : (N : ℂ) * (((Real.pi / N : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  let F : (Fin m → Fin n → ℂ) → ℂ := fun x =>
    evX (monomial d 1) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
  have hcont : Continuous F :=
    ((GI.continuous_evX _).mul (GI.continuous_gs c)).mul (Complex.continuous_exp.comp
      (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace)))
  have hcomp : (fun x => F (ζ • x)) = fun x => ζ ^ N * F x := by
    funext x
    simp only [F, evX_smul_mono ζ d hd, gs_smul c ζ hζ, gramX_smul ε ζ hζ]
    ring
  have hint : ∫ x, F (ζ • x) = ∫ x, F x := by
    rw [← integral_map (μ := volume) (φ := fun x : Fin m → Fin n → ℂ => ζ • x)
      (continuous_const_smul ζ).measurable.aemeasurable
      (by rw [map_smul_volume ζ hζ]; exact hcont.aestronglyMeasurable), map_smul_volume ζ hζ]
  have h2 : ∫ x, F x = -∫ x, F x := by
    conv_lhs => rw [← hint, hcomp, integral_const_mul, hζN, neg_one_mul]
  show ∫ x, F x = 0
  linear_combination (1 / 2 : ℂ) * h2

end PositivityTheory.Rg.Sw.WR.G
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousEvX
noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gramX_star (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    star (gramX ε x i j) = gramX ε x j i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, ↓reduceIte,
    Bool.false_eq_true, star_sub, star_sum, star_mul, star_star]

theorem herm_hinv (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, star (T i j) = T j i) : herm (hinv T) = T := by
  ext i j
  have h1 : (T j i).re = (T i j).re := by rw [← hT i j]; simp
  have h2 : (T j i).im = -(T i j).im := by rw [← hT i j]; simp
  apply Complex.ext
  · simp [herm, hinv, h1, h2]
    try ring
  · simp [herm, hinv, h1, h2]
    try ring

theorem hinv_herm' (y : E n) : hinv (herm y) = y := by
  funext i j
  simp [hinv, herm]
  ring

theorem herm_mul_apply (y y' : E n) (i j : Fin n) :
    herm y i j * herm y' j i =
      (((y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) + Complex.I * (((y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [herm] <;> ring

theorem trace_herm_mul (y y' : E n) : (herm y * herm y').trace = ((ip y y' : ℝ) : ℂ) := by
  have h1 : ∑ i, ∑ j, (y i j * y' j i - y j i * y' i j) / 2 = 0 := by
    simp only [sub_div, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => y j i * y' i j / 2)]
    exact sub_self _
  have h2 : ∑ i, ∑ j, (y i j * y' i j + y j i * y' j i) / 2 = ip y y' := by
    simp only [add_div, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => y j i * y' j i / 2)]
    simp only [ip, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  calc (herm y * herm y').trace = ∑ i, ∑ j, herm y i j * herm y' j i := by
        simp [Matrix.trace, Matrix.mul_apply]
    _ = ((∑ i, ∑ j, (y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) +
          Complex.I * ((∑ i, ∑ j, (y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by
        simp only [herm_mul_apply, Finset.sum_add_distrib, Complex.ofReal_sum, Finset.mul_sum]
    _ = ((ip y y' : ℝ) : ℂ) := by rw [h1, h2]; simp

theorem evX_detQ (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : evX (detQ ε) x = (gramX ε x).det := by
  rw [evX, detQ, RingHom.map_det]
  rfl

theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  split_ifs
  · exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
  · exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_qX (ε : Fin m → Bool) : Continuous (qX (n := n) ε) := by
  unfold qX hinv gramX
  exact continuous_pi fun i => continuous_pi fun j =>
    (Complex.continuous_re.comp (continuous_evX _)).add (Complex.continuous_im.comp (continuous_evX _))

theorem algA : AlgA := by
  intro m n ε
  refine ⟨fun y x => ?_, fun x => herm_hinv _ (gramX_star ε x), hinv_herm', evX_detQ ε, continuous_qX ε⟩
  have h := trace_herm_mul y (qX ε x)
  rwa [show herm (qX ε x) = gramX ε x from herm_hinv _ (gramX_star ε x)] at h

end PositivityTheory.Rg.Sw.WR.D
end
end
