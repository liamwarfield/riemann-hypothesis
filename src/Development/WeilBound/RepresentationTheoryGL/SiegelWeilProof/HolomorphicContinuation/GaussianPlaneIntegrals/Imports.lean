module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.IntegralMonSelf
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.ContinuousPhi
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.IntegralHkDiag
noncomputable section

open MeasureTheory Complex Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

def e1 (z : ℂ) : ℂ := Complex.exp (((-(‖z‖ ^ 2)) : ℝ) : ℂ)

def hk (k l : ℕ) (z : ℂ) : ℂ := z ^ k * star z ^ l * e1 z

theorem continuous_hk (k l : ℕ) : Continuous (hk k l) := by
  unfold hk e1
  fun_prop

theorem norm_hk (k l : ℕ) (z : ℂ) : ‖hk k l z‖ = ‖z‖ ^ (k + l) * Real.exp (-(‖z‖ ^ 2)) := by
  simp only [hk, e1, norm_mul, norm_pow, norm_star, Complex.norm_exp_ofReal, pow_add]

theorem pow_exp_le (n : ℕ) : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    t ^ n * Real.exp (-(t ^ 2)) ≤ C * (1 + t) ^ (-(3 : ℝ)) := by
  refine ⟨((n + 3).factorial : ℝ) * Real.exp 2, fun t ht => ?_⟩
  have h1 : 0 < 1 + t := by linarith
  have hr : (1 + t) ^ (-(3 : ℝ)) = ((1 + t) ^ 3)⁻¹ := by
    rw [Real.rpow_neg h1.le]
    norm_cast
  rw [hr, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hA : t ^ n ≤ (1 + t) ^ n := pow_le_pow_left₀ ht (by linarith) n
  have hB : (1 + t) ^ (n + 3) ≤ ((n + 3).factorial : ℝ) * Real.exp (1 + t) := by
    have h := Real.pow_div_factorial_le_exp (1 + t) h1.le (n + 3)
    rwa [div_le_iff₀ (by positivity), mul_comm] at h
  have hC : Real.exp (1 + t) * Real.exp (-(t ^ 2)) ≤ Real.exp 2 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (t - 1 / 2)])
  calc t ^ n * Real.exp (-(t ^ 2)) * (1 + t) ^ 3
      ≤ (1 + t) ^ n * Real.exp (-(t ^ 2)) * (1 + t) ^ 3 := by gcongr
    _ = (1 + t) ^ (n + 3) * Real.exp (-(t ^ 2)) := by ring
    _ ≤ ((n + 3).factorial : ℝ) * Real.exp (1 + t) * Real.exp (-(t ^ 2)) := by gcongr
    _ ≤ ((n + 3).factorial : ℝ) * Real.exp 2 := by
      rw [mul_assoc]
      gcongr

theorem integrable_hk (k l : ℕ) : Integrable (hk k l) := by
  obtain ⟨C, hC⟩ := pow_exp_le (k + l)
  have hi : Integrable (fun z : ℂ => (1 + ‖z‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by norm_num [finrank_real_complex])
  refine (hi.const_mul C).mono' (continuous_hk k l).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [norm_hk]
  exact hC _ (norm_nonneg _)

theorem integral_hk_ne (k l : ℕ) (h : k ≠ l) : ∫ z, hk k l z = 0 := by
  have hkl : ((k : ℂ) - l) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
  set θ : ℝ := Real.pi / ((k : ℝ) - l) with hθ
  have hfac : Complex.exp (θ * I) ^ k * star (Complex.exp (θ * I)) ^ l = -1 := by
    have hs : star (Complex.exp (θ * I)) = Complex.exp (-(θ * I)) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      simp
    rw [hs, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have h2 : (θ : ℂ) * ((k : ℂ) - l) = Real.pi := by
      rw [hθ]
      push_cast
      field_simp
    have h3 : (k : ℂ) * (θ * I) + l * (-(θ * I)) = Real.pi * I := by
      linear_combination I * h2
    rw [h3, Complex.exp_pi_mul_I]
  have hrot : ∀ z : ℂ, hk k l (Complex.exp (θ * I) * z) = -hk k l z := by
    intro z
    have he : e1 (Complex.exp (θ * I) * z) = e1 z := by
      simp only [e1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    simp only [hk]
    rw [he, star_mul', mul_pow, mul_pow]
    calc Complex.exp (θ * I) ^ k * z ^ k * (star (Complex.exp (θ * I)) ^ l * star z ^ l) * e1 z
        = (Complex.exp (θ * I) ^ k * star (Complex.exp (θ * I)) ^ l) * (z ^ k * star z ^ l * e1 z) := by ring
      _ = -(z ^ k * star z ^ l * e1 z) := by rw [hfac]; ring
  have key := (rotation (Circle.exp θ)).measurePreserving.integral_comp
    (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding (hk k l)
  simp only [LinearIsometryEquiv.coe_toHomeomorph, rotation_apply, Circle.coe_exp, hrot, integral_neg] at key
  linear_combination (-1 / 2 : ℂ) * key

def jr (k : ℕ) : ℝ := ∫ z : ℂ, (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2))

theorem hk_diag (k : ℕ) (z : ℂ) : hk k k z = (((‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) : ℝ) : ℂ) := by
  simp only [hk, e1]
  rw [← mul_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem integral_hk_diag (k : ℕ) : ∫ z, hk k k z = (jr k : ℂ) := by
  simp_rw [hk_diag]
  exact integral_ofReal

theorem jr_pos (k : ℕ) : 0 < jr k := by
  have hint : Integrable (fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2))) := by
    refine (integrable_hk k k).norm.congr (ae_of_all _ fun z => ?_)
    simp only [norm_hk]
    ring
  have hnn : 0 ≤ fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) := fun z => by positivity
  unfold jr
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hc : Continuous fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) := by fun_prop
  exact hc.isOpen_support.measure_pos volume ⟨1, by simp⟩

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
end
end

noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

abbrev Sg (ι A B : Type) := (ι × A) ⊕ (ι × B)

def Phi (g : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : Sg ι A B → ℂ :=
  Sum.elim (fun x => z (Sum.inl x)) (fun y => ∑ j, g y.1 j * z (Sum.inr (j, y.2)))

theorem eval_sub (g : Matrix ι ι ℂ) (f : PV ι A B) (z : Sg ι A B → ℂ) :
    eval z (sub 1 g f) = eval (Phi g z) f := by
  have h : (eval z).comp (sub (A := A) (B := B) 1 g).toRingHom = eval (Phi g z) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [sub]
    · intro s
      rcases s with ⟨i, a⟩ | ⟨i, b⟩
      · simp [sub, Phi, Matrix.one_apply]
      · simp [sub, Phi]
  exact RingHom.congr_fun h f

theorem Phi_mul (g h : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : Phi (g * h) z = Phi g (Phi h z) := by
  funext s
  rcases s with x | ⟨i, b⟩
  · rfl
  · simp only [Phi, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

theorem Phi_one (z : Sg ι A B → ℂ) : Phi 1 z = z := by
  funext s
  rcases s with x | ⟨i, b⟩
  · rfl
  · simp [Phi, Matrix.one_apply]

theorem unitary_norm (U : Matrix ι ι ℂ) (hU : star U * U = 1) (v : ι → ℂ) :
    ∑ i, ‖∑ j, U i j * v j‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  have key : star (U.mulVec v) ⬝ᵥ U.mulVec v = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU,
      Matrix.one_mulVec]
  have e1' : ∀ w : ι → ℂ, star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [← e1', ← e1', ← key]
  rfl

theorem norm_Phi (U : Matrix ι ι ℂ) (hU : star U * U = 1) (z : Sg ι A B → ℂ) :
    ∑ s, ‖Phi U z s‖ ^ 2 = ∑ s, ‖z s‖ ^ 2 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact unitary_norm U hU fun j => z (Sum.inr (j, b))

def PhiL (g : Matrix ι ι ℂ) : (Sg ι A B → ℂ) →ₗ[ℝ] (Sg ι A B → ℂ) where
  toFun := Phi g
  map_add' z w := by
    funext s
    rcases s with x | y
    · rfl
    · simp [Phi, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext s
    rcases s with x | y
    · rfl
    · simp only [Phi, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.real_smul, Complex.real_smul]
      ring

theorem PhiL_apply (g : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : PhiL g z = Phi g z := rfl

theorem map_PhiL (U : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) :
    Measure.map (PhiL (A := A) (B := B) U) volume = volume := by
  set L := PhiL (A := A) (B := B) U
  set S : Set (Sg ι A B → ℂ) := {z | ∑ s, ‖z s‖ ^ 2 ≤ 1}
  have hU3 : star (star U) * star U = 1 := by rw [star_star]; exact hU2
  have himg : L '' S = S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [S, Set.mem_setOf_eq, L, PhiL_apply, norm_Phi U hU1] at hw ⊢
      exact hw
    · intro hz
      refine ⟨Phi (star U) z, ?_, ?_⟩
      · simp only [S, Set.mem_setOf_eq, norm_Phi (star U) hU3]
        exact hz
      · simp only [L, PhiL_apply, ← Phi_mul, hU2, Phi_one]
  have hpos : 0 < volume S := by
    have hopen : IsOpen {z : Sg ι A B → ℂ | ∑ s, ‖z s‖ ^ 2 < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    refine lt_of_lt_of_le (hopen.measure_pos volume ⟨0, by simp⟩) (measure_mono fun z hz => show ∑ s, ‖z s‖ ^ 2 ≤ 1 from le_of_lt hz)
  have hfin : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : Sg ι A B → ℂ)) (r := 1)).ne
      (measure_mono fun z hz => ?_)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro s
    have h1 : ‖z s‖ ^ 2 ≤ 1 := le_trans (Finset.single_le_sum (f := fun s => ‖z s‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ s)) hz
    nlinarith [norm_nonneg (z s)]
  have hdet : |LinearMap.det L| = 1 := by
    have h := Measure.addHaar_image_linearMap (volume : Measure (Sg ι A B → ℂ)) L S
    rw [himg] at h
    have h' : ENNReal.ofReal |LinearMap.det L| * volume S = 1 * volume S := by rw [← h, one_mul]
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h'
    exact (ENNReal.ofReal_eq_one).1 this
  have hne : LinearMap.det L ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hdet
    exact zero_ne_one hdet
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, abs_inv, hdet, inv_one, ENNReal.ofReal_one, one_smul]

theorem integral_Phi (U : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (H : (Sg ι A B → ℂ) → ℂ) (hH : Continuous H) :
    ∫ z, H z = ∫ z, H (Phi U z) := by
  have hL : Continuous (PhiL (A := A) (B := B) U) := LinearMap.continuous_of_finiteDimensional _
  conv_lhs => rw [← map_PhiL (A := A) (B := B) U hU1 hU2]
  rw [integral_map hL.measurable.aemeasurable hH.aestronglyMeasurable]
  rfl

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
end
end

noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

theorem gw_prod (z : Sg ι A B → ℂ) : Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, e1 (z s) := by
  simp only [e1]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp [Finset.sum_neg_distrib]

def mon (m : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) : ℂ := ∏ s, z s ^ m s

theorem mon_prod (m m' : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) :
    mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, hk (m s) (m' s) (z s) := by
  rw [gw_prod]
  simp only [mon, hk, Complex.star_def, map_prod, map_pow, Finset.prod_mul_distrib]

theorem integrable_mon (m m' : Sg ι A B →₀ ℕ) :
    Integrable (fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
  simp_rw [mon_prod]
  have := Integrable.fintype_prod (f := fun s => hk (m s) (m' s)) (μ := fun _ => (volume : Measure ℂ))
    (fun s => integrable_hk _ _)
  rwa [← volume_pi] at this

theorem integral_mon (m m' : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ∏ s, ∫ w, hk (m s) (m' s) w := by
  simp_rw [mon_prod]
  exact integral_fintype_prod_volume_eq_prod (fun s w => hk (m s) (m' s) w)

theorem integral_mon_ne (m m' : Sg ι A B →₀ ℕ) (h : m ≠ m') :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = 0 := by
  rw [integral_mon]
  obtain ⟨s, hs⟩ : ∃ s, m s ≠ m' s := by
    by_contra hc
    push Not at hc
    exact h (Finsupp.ext hc)
  exact Finset.prod_eq_zero (Finset.mem_univ s) (integral_hk_ne _ _ hs)

theorem integral_mon_self (m : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ((∏ s, jr (m s) : ℝ) : ℂ) := by
  rw [integral_mon]
  push_cast
  exact Finset.prod_congr rfl fun s _ => integral_hk_diag _

def kap (d : ι → ℝ) : Sg ι A B → ℝ := Sum.elim (fun _ => 1) (fun y => d y.1)

def lam (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) : ℝ := ∏ s, kap d s ^ m s

theorem Phi_diag (d : ι → ℝ) (z : Sg ι A B → ℂ) :
    Phi (Matrix.diagonal fun i => (d i : ℂ)) z = fun s => (kap d s : ℂ) * z s := by
  funext s
  rcases s with x | ⟨i, b⟩
  · simp [Phi, kap]
  · simp [Phi, kap, Matrix.diagonal_apply]

theorem gip_diag (d : ι → ℝ) (g : PV ι A B) :
    gip (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) g =
      ((∑ m ∈ g.support, Complex.normSq (g.coeff m) * lam d m * ∏ s, jr (m s) : ℝ) : ℂ) := by
  unfold gip
  have hpt : ∀ z : Sg ι A B → ℂ,
      eval z (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
        ∑ m ∈ g.support, ∑ m' ∈ g.support, (g.coeff m * (lam d m : ℂ) * star (g.coeff m')) *
          (mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
    intro z
    rw [eval_sub, Phi_diag, MvPolynomial.eval_eq', MvPolynomial.eval_eq']
    have hl : ∀ m : Sg ι A B →₀ ℕ, ∏ s, ((kap d s : ℂ) * z s) ^ m s = (lam d m : ℂ) * mon m z := by
      intro m
      simp only [mul_pow, Finset.prod_mul_distrib, lam, mon]
      push_cast
      rfl
    simp_rw [hl]
    rw [star_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m' _ => ?_
    have hmon : (∏ i, z i ^ m' i) = mon m' z := rfl
    try simp only [star_mul']
    try rw [hmon]
    ring
  simp_rw [hpt]
  have hint : ∀ m m' : Sg ι A B →₀ ℕ, Integrable fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) :=
    integrable_mon
  rw [MeasureTheory.integral_finsetSum _ fun m _ => MeasureTheory.integrable_finsetSum _ fun m' _ => (hint m m').const_mul _]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MeasureTheory.integral_finsetSum _ fun m' _ => (hint m m').const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single_of_mem m hm fun m' _ hne => by rw [integral_mon_ne m m' hne.symm, mul_zero]]
  rw [integral_mon_self]
  have hc : ((Complex.normSq (g.coeff m) : ℝ) : ℂ) = g.coeff m * star (g.coeff m) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, hc]
  ring

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
end
end

noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps

open PosProof

private theorem gip_monomial_self_eq_prod_jr {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (m : Sg ι A B →₀ ℕ) :
    gip (monomial m (1 : ℂ)) (monomial m (1 : ℂ)) = ((∏ s : Sg ι A B, jr (m s) : ℝ) : ℂ) := by
  rw [← integral_mon_self m]
  unfold gip
  congr 1
  funext z
  rw [mon_prod]
  have h1 : (eval z) (monomial m (1 : ℂ)) = ∏ s : Sg ι A B, z s ^ m s := by
    rw [eval_monomial, one_mul, Finsupp.prod_fintype]
    intro i
    simp
  rw [h1, star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_sum, ← Finset.sum_neg_distrib,
    Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hk_diag, star_pow, ← mul_pow]
  have h2 : z s * star (z s) = ((‖z s‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h2]
  push_cast
  ring_nf

private theorem pos_lemma {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) :
    sub 1 (Matrix.diagonal fun i => (d i : ℂ)) (monomial m (1 : ℂ)) =
      C ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * monomial m (1 : ℂ) := by
  apply MvPolynomial.funext
  intro z
  rw [PosProof.eval_sub, Phi_diag, eval_mul, eval_C, eval_monomial, eval_monomial, one_mul, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  push_cast
  simp only [mul_pow, Finset.prod_mul_distrib]

private theorem lam_eq_prod_kap_pow {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) :
    lam d m = ∏ s : Sg ι A B, kap d s ^ m s := by
  classical
  have hP : (0 : ℝ) < ∏ s : Sg ι A B, jr (m s) := Finset.prod_pos fun s _ => jr_pos _
  have h := gip_diag (A := A) (B := B) d (monomial m (1 : ℂ))
  rw [pos_lemma, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl,
    Complex.normSq_one, one_mul] at h
  have h3 : gip (C ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * monomial m (1 : ℂ)) (monomial m (1 : ℂ)) =
      ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * ((∏ s : Sg ι A B, jr (m s) : ℝ) : ℂ) := by
    rw [← gip_monomial_self_eq_prod_jr]
    unfold gip
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [eval_mul, eval_C]
    ring
  rw [h3] at h
  have h4 : (∏ s : Sg ι A B, kap d s ^ m s) * (∏ s : Sg ι A B, jr (m s)) =
      lam d m * ∏ s : Sg ι A B, jr (m s) := by
    exact_mod_cast h
  exact (mul_right_cancel₀ hP.ne' h4).symm

private theorem gip_sub_eq_of_unitary_conj_diag {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (M U D : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) (hMU : M * U = U * D)
    (f : PV ι A B) :
    gip (sub 1 M f) f = gip (sub 1 D (sub 1 U f)) (sub 1 U f) := by
  have hcont : Continuous fun z : Sg ι A B → ℂ =>
      (eval z) (sub 1 M f) * star ((eval z) f) * Complex.exp (-↑(∑ s : Sg ι A B, ‖z s‖ ^ 2)) :=
    ((continuous_eval _).mul (continuous_star.comp (continuous_eval _))).mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_finsetSum _ fun s _ => (continuous_norm.comp (continuous_apply s)).pow 2)).neg)
  unfold gip
  rw [integral_Phi U hU1 hU2 _ hcont]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [PosProof.eval_sub]
  rw [← Phi_mul, ← Phi_mul, hMU, norm_Phi U hU1]

theorem pos : Pos := by
  intro ι A B _ _ _ _ M hM f
  have hH := hM.isHermitian
  have hMe : M = (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hU1 : star (hH.eigenvectorUnitary : Matrix ι ι ℂ) * (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hU2 : (hH.eigenvectorUnitary : Matrix ι ι ℂ) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    simpa [Unitary.coe_star] using Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hMU : M * (hH.eigenvectorUnitary : Matrix ι ι ℂ) =
      (hH.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    have h := congrArg (· * (hH.eigenvectorUnitary : Matrix ι ι ℂ)) hMe
    rw [h, Matrix.mul_assoc (_ * _), hU1, Matrix.mul_one]
  have hkap : ∀ s : Sg ι A B, 0 ≤ kap hH.eigenvalues s := by
    intro s
    rcases s with s | s
    · simp [kap]
    · simp only [kap, Sum.elim_inr]
      exact hM.eigenvalues_nonneg _
  rw [gip_sub_eq_of_unitary_conj_diag M _ _ hU1 hU2 hMU f, gip_diag]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, trivial, ?_⟩
  · refine Finset.sum_nonneg fun m _ => mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) ?_)
      (Finset.prod_nonneg fun s _ => (jr_pos _).le)
    rw [lam_eq_prod_kap_pow]
    exact Finset.prod_nonneg fun s _ => pow_nonneg (hkap s) _
  · intro hPD hf
    have hkap' : ∀ s : Sg ι A B, 0 < kap hH.eigenvalues s := by
      intro s
      rcases s with s | s
      · simp [kap]
      · simp only [kap, Sum.elim_inr]
        exact hPD.eigenvalues_pos _
    have hinv : sub 1 (star (hH.eigenvectorUnitary : Matrix ι ι ℂ))
        (sub 1 (hH.eigenvectorUnitary : Matrix ι ι ℂ) f) = f := by
      apply MvPolynomial.funext
      intro z
      rw [PosProof.eval_sub, PosProof.eval_sub, ← Phi_mul, hU2, Phi_one]
    have hg : sub 1 (hH.eigenvectorUnitary : Matrix ι ι ℂ) f ≠ 0 := by
      intro hg
      apply hf
      rw [← hinv, hg, map_zero]
    refine Finset.sum_pos (fun m hm => mul_pos (mul_pos (Complex.normSq_pos.2 (mem_support_iff.1 hm)) ?_)
      (Finset.prod_pos fun s _ => jr_pos _)) ?_
    · rw [lam_eq_prod_kap_pow]
      exact Finset.prod_pos fun s _ => pow_pos (hkap' s) _
    · exact Finset.nonempty_iff_ne_empty.2 (by rwa [Ne, MvPolynomial.support_eq_empty])

end PositivityTheory.Rg.Sw.FFTSteps
