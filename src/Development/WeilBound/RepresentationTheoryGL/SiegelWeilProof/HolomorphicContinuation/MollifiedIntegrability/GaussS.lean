module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS
noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def Amat (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * t * sgn ε a) • bᵀ

def IntegP : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, Integrable fun x : Fin m → Fin n → ℂ => evX P x * gs c x

def Wick : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∀ (M : PX m n) (a : Fin m) (i : Fin n),
      secN ε c t (X (a, i, true) * M) b = ∑ j, (Amat ε c t b a)⁻¹ j i * secN ε c t (pderiv (a, j, false) M) b

def Rot : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∀ d : (Fin m × Fin n × Bool) →₀ ℕ, (∀ k, k.2.2 = true → d k = 0) → d ≠ 0 →
      secN ε c t (monomial d 1) b = 0

def Base : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    secN ε c t 1 b = ∏ a, ((Real.pi : ℂ) ^ n / (Amat ε c t b a).det)

end PositivityTheory.Rg.Sw.WR.G
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DensDefs
noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def hinv (T : Matrix (Fin n) (Fin n) ℂ) : E n := fun i j => (T i j).re + (T i j).im

def ip (y y' : E n) : ℝ := ∑ a, ∑ b, y a b * y' a b

def qX (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : E n := hinv (gramX ε x)

def detQ (ε : Fin m → Bool) : PX m n := (Matrix.of fun i j => Qp ε i j).det

def FP (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (y : E n) : ℂ :=
  ∫ x, evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x))

def AlgA : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool), (∀ (y : E n) (x : Fin m → Fin n → ℂ),
      (herm y * gramX ε x).trace = (ip y (qX ε x) : ℂ)) ∧
    (∀ x : Fin m → Fin n → ℂ, herm (qX ε x) = gramX ε x) ∧ (∀ y : E n, hinv (herm y) = y) ∧
    (∀ x : Fin m → Fin n → ℂ, evX (detQ ε) x = (gramX ε x).det) ∧ Continuous (qX (n := n) ε)

def IntG : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, Integrable (fun x => evX P x * gs c x)

def DerivF : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (P : PX m n) (N : ℕ),
    Continuous (FP ε c t P) ∧
    Delta^[N] (FP ε c t P) = FP ε c t ((MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε) ^ N * P)

def MollId : Prop :=
  ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure X) [SFinite μ] (Ψ : X → ℂ) (qq : X → E n), Integrable Ψ μ →
    Measurable qq → ∀ t : ℝ, t ≠ 0 →
    Integrable (fun y : E n => ∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) →
    ∀ ψ : E n → ℂ, Continuous ψ → HasCompactSupport ψ →
      ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ β, ψ β * (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * Complex.exp (-(Complex.I * t * ip β y)))

end PositivityTheory.Rg.Sw.WR.D
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Integr
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.WR.I

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm, star_add, star_div₀, star_mul', Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem normSq_herm (y : E n) (i j : Fin n) :
    Complex.normSq (herm y i j) = (y i j ^ 2 + y j i ^ 2) / 2 := by
  simp only [herm, Complex.normSq_apply]
  simp
  ring

theorem sum_normSq_herm (y : E n) :
    ∑ i, ∑ j, Complex.normSq (herm y i j) = ∑ a, ∑ b, y a b ^ 2 := by
  simp_rw [normSq_herm, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => y j i ^ 2)]
  ring

theorem one_add_sum_le_prod (s : Finset (Fin n)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have h0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
    nlinarith [ha j]

theorem dP_eq_prod (y : E n) :
    dP y = ∏ i, (1 + (herm_isHermitian y).eigenvalues i ^ 2) ∧
      ∑ a, ∑ b, y a b ^ 2 = ∑ i, (herm_isHermitian y).eigenvalues i ^ 2 := by
  set hA := herm_isHermitian y
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hUs : star U * U = 1 := Unitary.coe_star_mul_self _
  have hsU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : herm y = U * D * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hsq : 1 + herm y * herm y = U * (1 + D * D) * star U := by
    rw [hspec]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    rw [hsU]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]
  have hDD : 1 + D * D = diagonal fun i => ((1 + hA.eigenvalues i ^ 2 : ℝ) : ℂ) := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one, diagonal_add]
    congr 1
    funext i
    simp [pow_two]
  have hdetU : U.det * (star U).det = 1 := by rw [← det_mul, hsU, det_one]
  constructor
  · unfold dP
    rw [hsq, det_mul, det_mul, hDD, det_diagonal]
    rw [mul_comm U.det, mul_assoc, hdetU, mul_one, ← Complex.ofReal_prod, Complex.ofReal_re]
  · have hsq2 : herm y * herm y = U * (D * D) * star U := by
      rw [hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]
    have htr : (herm y * herm y).trace = ∑ i, ((hA.eigenvalues i ^ 2 : ℝ) : ℂ) := by
      rw [hsq2, trace_mul_comm, ← Matrix.mul_assoc, hUs, Matrix.one_mul, hD, diagonal_mul_diagonal, trace_diagonal]
      simp [pow_two]
    have hre : (herm y * herm y).trace.re = ∑ i, ∑ j, Complex.normSq (herm y i j) := by
      rw [trace]
      simp only [diag_apply, Matrix.mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hji : herm y j i = star (herm y i j) := by
        have := congrFun (congrFun hA.eq j) i
        rw [conjTranspose_apply] at this
        exact this.symm
      rw [hji, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    rw [← sum_normSq_herm, ← hre, htr, Complex.re_sum]
    simp only [Complex.ofReal_re]

theorem dP_ge (y : E n) : 1 + ∑ a, ∑ b, y a b ^ 2 ≤ dP y := by
  obtain ⟨h1, h2⟩ := dP_eq_prod y
  rw [h1, h2]
  exact one_add_sum_le_prod _ _ fun i => sq_nonneg _

theorem dP_pos (y : E n) : 0 < dP y := by
  have h0 : 0 ≤ ∑ a, ∑ b, y a b ^ 2 := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  linarith [dP_ge y]

theorem continuous_herm : Continuous (herm : E n → Matrix (Fin n) (Fin n) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold herm
  fun_prop

theorem continuous_dP : Continuous (dP : E n → ℝ) := by
  unfold dP
  have : Continuous fun y : E n => 1 + herm y * herm y := continuous_const.add (continuous_herm.matrix_mul continuous_herm)
  exact Complex.continuous_re.comp this.matrix_det

theorem norm_sq_le_sum (y : E n) : ‖y‖ ^ 2 ≤ ∑ a, ∑ b, y a b ^ 2 := by
  have h0 : 0 ≤ ∑ a, ∑ b, y a b ^ 2 := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hle : ‖y‖ ≤ Real.sqrt (∑ a, ∑ b, y a b ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    calc y a b ^ 2 ≤ ∑ b', y a b' ^ 2 := Finset.single_le_sum (fun b' _ => sq_nonneg (y a b')) (Finset.mem_univ b)
      _ ≤ ∑ a', ∑ b', y a' b' ^ 2 :=
        Finset.single_le_sum (f := fun a' => ∑ b', y a' b' ^ 2) (fun a' _ => Finset.sum_nonneg fun b' _ => sq_nonneg _)
          (Finset.mem_univ a)
  calc ‖y‖ ^ 2 ≤ Real.sqrt (∑ a, ∑ b, y a b ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = _ := Real.sq_sqrt h0

theorem integr : Integr := by
  intro n
  refine ⟨⟨1, one_pos, fun y => by simpa using dP_ge y⟩, fun σ hσ => ?_⟩
  have hfin : (Module.finrank ℝ (E n) : ℝ) = (n : ℝ) ^ 2 := by
    have h : Module.finrank ℝ (Fin n → Fin n → ℝ) = n * n := by
      rw [Module.finrank_pi_fintype]
      simp
    change ((Module.finrank ℝ (Fin n → Fin n → ℝ) : ℕ) : ℝ) = (n : ℝ) ^ 2
    rw [h]
    push_cast
    ring
  have hr : (Module.finrank ℝ (E n) : ℝ) < 2 * σ := by rw [hfin]; linarith
  have hint := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (E n))) hr
  have hσ0 : 0 ≤ σ := by nlinarith [sq_nonneg (n : ℝ)]
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (continuous_dP.rpow_const fun y => Or.inl (dP_pos y).ne').aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dP_pos y).le _)]
    have h1 : 1 + ‖y‖ ^ 2 ≤ dP y := by linarith [norm_sq_le_sum y, dP_ge y]
    have h2 : 0 < 1 + ‖y‖ ^ 2 := by positivity
    rw [show -(2 * σ) / 2 = -σ by ring]
    exact Real.rpow_le_rpow_of_nonpos h2 h1 (by linarith)

end PositivityTheory.Rg.Sw.WR.I
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainBSt
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Mc (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def cpart (i j : Fin n) (F : Mc n → ℂ) : Mc n → ℂ := fun b => fderiv ℂ F b (Matrix.single i j 1)

def word (L : List (Fin n × Fin n)) (F : Mc n → ℂ) : Mc n → ℂ := L.foldr (fun ij g => cpart ij.1 ij.2 g) F

def DeltaC (F : Mc n → ℂ) : Mc n → ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => cpart (σ k) k g) F

def Fr (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (b : Mc n) : ℂ :=
  (1 - (Complex.I * s) • b)⁻¹.det ^ p * (1 + (Complex.I * s) • b)⁻¹.det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • b)⁻¹ k.2.1 k.2.2 else (1 - (Complex.I * s) • b)⁻¹ k.2.1 k.2.2) R

def Ugood (s : ℂ) : Set (Mc n) := {b | IsUnit (1 - (Complex.I * s) • b).det ∧ IsUnit (1 + (Complex.I * s) • b).det}

def pdisc (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ) : Set (Mc n) := {b | ∀ i j, ‖b i j - b₀ i j‖ ≤ ρ i j}

def CauchyW : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ), (∀ i j, 0 < ρ i j) → pdisc b₀ ρ ⊆ U →
    ∀ M : ℝ, (∀ b ∈ pdisc b₀ ρ, ‖F b‖ ≤ M) → ∀ L : List (Fin n × Fin n),
      ‖word L F b₀‖ ≤ (L.map fun ij => (L.length : ℝ) / ρ ij.1 ij.2).prod * M

def Invar : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ N : ℕ, ∀ b, k * b * kᴴ ∈ U →
      (DeltaC^[N] (fun c => F (k * c * kᴴ))) b = (DeltaC^[N] F) (k * b * kᴴ)

def PBound : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    IsOpen (Ugood (n := n) s) ∧ ContDiffOn ℂ (⊤ : ℕ∞) (Fr s p q R) (Ugood s) ∧
    ∃ (c₀ C : ℝ), 0 < c₀ ∧ ∀ (k : Mc n), k ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ (lam : Fin n → ℝ),
      ∀ b ∈ pdisc (Matrix.diagonal fun i => (lam i : ℂ)) (fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|))),
        k * b * kᴴ ∈ Ugood s ∧ ‖Fr s p q R (k * b * kᴴ)‖ ≤ C * (∏ i, (1 + |lam i|)) ^ (-((p + q : ℕ) : ℝ))

def Link : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U → (∀ y, herm y ∈ U) →
    (∀ N y, (Delta^[N] (fun y => F (herm y))) y = (DeltaC^[N] F) (herm y)) ∧
    ∀ N : ℕ, ∀ b ∈ U, (DeltaC^[N] F) b = ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F b

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainSt
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

abbrev MC (n : ℕ) := Fin n → Fin n → ℂ

def eU (a b : Fin n) : MC n := fun i j => if i = a ∧ j = b then 1 else 0

def cay (F : MC n → ℂ) (B : MC n) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n F B (fun k => eU (σ k) k)

def OmS (s : ℂ) : Set (MC n) :=
  {B | (1 - (Complex.I * s) • Matrix.of B).det ≠ 0 ∧ (1 + (Complex.I * s) • Matrix.of B).det ≠ 0 ∧
    (1 + Matrix.of B * Matrix.of B).det ∈ Complex.slitPlane}

def clsC (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B : MC n) : ℂ :=
  Complex.exp (-z * Complex.log (1 + Matrix.of B * Matrix.of B).det) *
    ((1 - (Complex.I * s) • Matrix.of B)⁻¹).det ^ p * ((1 + (Complex.I * s) • Matrix.of B)⁻¹).det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
      else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) R

def Ext : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → IsOpen (OmS (n := n) s) ∧ (∀ y : E n, (herm y : MC n) ∈ OmS s) ∧
    ∀ (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
      AnalyticOnNhd ℂ (clsC s z p q R) (OmS s) ∧ ∀ y, clsC s z p q R (herm y) = cls s z p q R y

def Chain : Prop :=
  ∀ (n : ℕ) (U : Set (MC n)) (F : MC n → ℂ), IsOpen U → (∀ y : E n, (herm y : MC n) ∈ U) → AnalyticOnNhd ℂ F U →
    ∀ N y, (Delta^[N] (fun y : E n => F (herm y))) y = (cay^[N] F) (herm y)

end PositivityTheory.Rg.Sw.WR.Z
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.IntegrableOfBound
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.WR.Ib

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {n : ℕ}

def lf (t : ℝ) (β : E n) : E n →L[ℝ] ℂ :=
  ∑ a, ∑ b, (-(Complex.I * t * β a b)) • (Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj b : (Fin n → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj a : E n →L[ℝ] (Fin n → ℝ))))

theorem lf_apply (t : ℝ) (β w : E n) :
    lf t β w = -(Complex.I * t * ∑ a, ∑ b, (β a b : ℂ) * (w a b : ℂ)) := by
  simp only [lf, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem chr_eq (t : ℝ) (β y : E n) : chr t β y = Complex.exp (lf t β y) := by
  rw [lf_apply, chr]
  push_cast
  rfl

theorem hasFDerivAt_chr (t : ℝ) (β y : E n) : HasFDerivAt (chr t β) (chr t β y • lf t β) y := by
  have e : chr t β = fun y => Complex.exp (lf t β y) := funext (chr_eq t β)
  rw [e]
  exact (lf t β).hasFDerivAt.cexp

theorem fderiv_chr (t : ℝ) (β y w : E n) : fderiv ℝ (chr t β) y w = chr t β y * lf t β w := by
  rw [(hasFDerivAt_chr t β y).fderiv]
  simp [smul_eq_mul]

theorem differentiable_chr (t : ℝ) (β : E n) : Differentiable ℝ (chr t β) :=
  fun y => (hasFDerivAt_chr t β y).differentiableAt

theorem continuous_chr (t : ℝ) (β : E n) : Continuous (chr t β) := (differentiable_chr t β).continuous

theorem norm_chr (t : ℝ) (β y : E n) : ‖chr t β y‖ = 1 := by
  rw [chr_eq, Complex.norm_exp, lf_apply]
  have h : (∑ a, ∑ b, (β a b : ℂ) * (y a b : ℂ)) = ((∑ a, ∑ b, β a b * y a b : ℝ) : ℂ) := by push_cast; rfl
  rw [h]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im]

theorem lf_re_im (t : ℝ) (β : E n) (w : Fin n → Fin n → ℂ) :
    lf t β (fun a b => (w a b).re) + Complex.I * lf t β (fun a b => (w a b).im) =
      -(Complex.I * t * ∑ a, ∑ b, (β a b : ℂ) * w a b) := by
  rw [lf_apply, lf_apply]
  have h : ∀ a b, (β a b : ℂ) * w a b =
      (β a b : ℂ) * ((w a b).re : ℂ) + Complex.I * ((β a b : ℂ) * ((w a b).im : ℂ)) := by
    intro a b
    conv_lhs => rw [← Complex.re_add_im (w a b)]
    ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem herm_apply' (x : E n) (i j : Fin n) :
    herm x i j = ((x i j + x j i : ℝ) : ℂ) / 2 + Complex.I * ((x i j - x j i : ℝ) : ℂ) / 2 := rfl

theorem sum_single (β : E n) (c : ℂ) (k l : Fin n) :
    ∑ a, ∑ b, (β a b : ℂ) * (if a = k ∧ b = l then c else 0) = β k l * c := by
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [ha]
  · simp

theorem sum_vkl (β : E n) (k l : Fin n) : ∑ a, ∑ b, (β a b : ℂ) * vkl k l a b = herm β k l := by
  simp only [vkl, mul_add, Finset.sum_add_distrib, sum_single]
  rw [herm_apply']
  push_cast
  ring

theorem conj_half_add : starRingEnd ℂ ((1 + Complex.I) / 2) = (1 - Complex.I) / 2 := by
  rw [map_div₀, map_add (f := _), map_one, Complex.conj_I, map_ofNat]; ring

theorem conj_half_sub : starRingEnd ℂ ((1 - Complex.I) / 2) = (1 + Complex.I) / 2 := by
  rw [map_div₀, map_sub, map_one, Complex.conj_I, map_ofNat]; ring

theorem vkl_swap (k l a b : Fin n) : vkl l k a b = starRingEnd ℂ (vkl k l a b) := by
  simp only [vkl, map_add (f := _), apply_ite (starRingEnd ℂ), map_zero, conj_half_add, conj_half_sub]
  rw [add_comm]

theorem dkl_swap (g : E n → ℂ) (k l : Fin n) (y : E n) :
    Dkl l k g y = fderiv ℝ g y (fun a b => (vkl k l a b).re) -
      Complex.I * fderiv ℝ g y (fun a b => (vkl k l a b).im) := by
  have e1 : (fun a b => (vkl l k a b).re) = fun a b => (vkl k l a b).re := by
    funext a b; rw [vkl_swap]; simp
  have e2 : (fun a b => (vkl l k a b).im) = -(fun a b => (vkl k l a b).im) := by
    funext a b; rw [vkl_swap]; simp
  simp only [Dkl, dirC]
  rw [e1, e2, map_neg]
  ring

theorem contDiff_dkl {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l g) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := (contDiff_infty_iff_fderiv.mp hg).2
  simp only [Dkl, dirC]
  exact (hd.clm_apply contDiff_const).add (contDiff_const.mul (hd.clm_apply contDiff_const))

theorem integrable_of_bound {g : E n → ℂ} (hg : Continuous g) {h : E n → ℝ} (hh : Integrable h)
    (hb : ∀ y, ‖g y‖ ≤ h y) : Integrable g :=
  hh.mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem integrable_mul_chr {g : E n → ℂ} (hg : Integrable g) (hc : Continuous g) (t : ℝ) (β : E n) :
    Integrable fun y => g y * chr t β y :=
  hg.norm.mono' (hc.mul (continuous_chr t β)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by rw [norm_mul, norm_chr, mul_one])

theorem ibp_dir {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgi : Integrable g) (w : E n)
    (hgw : Integrable fun y => fderiv ℝ g y w) (t : ℝ) (β : E n) :
    ∫ y, fderiv ℝ g y w * chr t β y = -(lf t β w) * ∫ y, g y * chr t β y := by
  have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hcont : Continuous g := hg.continuous
  have hcw : Continuous fun y => fderiv ℝ g y w :=
    ((contDiff_infty_iff_fderiv.mp hg).2.continuous).clm_apply continuous_const
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := g) (g := chr t β) (v := w)
    (integrable_mul_chr hgw hcw t β)
    (by
      have : (fun y => g y * fderiv ℝ (chr t β) y w) = fun y => (g y * chr t β y) * lf t β w := by
        funext y; rw [fderiv_chr]; ring
      rw [this]
      exact (integrable_mul_chr hgi hcont t β).mul_const _)
    (integrable_mul_chr hgi hcont t β)
    (fun x _ => hdiff x) (fun x _ => differentiable_chr t β x)
  have : (fun y => g y * fderiv ℝ (chr t β) y w) = fun y => (g y * chr t β y) * lf t β w := by
    funext y; rw [fderiv_chr]; ring
  rw [this, integral_mul_const] at H
  linear_combination H

theorem ibp_dkl {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgi : Integrable g) (k l : Fin n)
    (h1 : Integrable (Dkl k l g)) (h2 : Integrable (Dkl l k g)) (t : ℝ) (β : E n) :
    ∫ y, Dkl k l g y * chr t β y = -((-(Complex.I * t)) * herm β k l) * ∫ y, g y * chr t β y := by
  set u : E n := fun a b => (vkl k l a b).re
  set w : E n := fun a b => (vkl k l a b).im
  have hre : (fun y => fderiv ℝ g y u) = fun y => (Dkl k l g y + Dkl l k g y) / 2 := by
    funext y; rw [dkl_swap g k l y]; simp only [Dkl, dirC, u, w]; ring
  have him : (fun y => fderiv ℝ g y w) = fun y => (Dkl k l g y - Dkl l k g y) / (2 * Complex.I) := by
    funext y; rw [dkl_swap g k l y]; simp only [Dkl, dirC, u, w]; field_simp; ring
  have iu : Integrable fun y => fderiv ℝ g y u := by rw [hre]; exact (h1.add h2).div_const _
  have iw : Integrable fun y => fderiv ℝ g y w := by rw [him]; exact (h1.sub h2).div_const _
  have hcont := hg.continuous
  have hcu : Continuous fun y => fderiv ℝ g y u :=
    ((contDiff_infty_iff_fderiv.mp hg).2.continuous).clm_apply continuous_const
  have hcw : Continuous fun y => fderiv ℝ g y w :=
    ((contDiff_infty_iff_fderiv.mp hg).2.continuous).clm_apply continuous_const
  have eD : (fun y => Dkl k l g y * chr t β y) =
      fun y => fderiv ℝ g y u * chr t β y + Complex.I * (fderiv ℝ g y w * chr t β y) := by
    funext y; simp only [Dkl, dirC, u, w]; ring
  rw [eD, integral_add (integrable_mul_chr iu hcu t β) ((integrable_mul_chr iw hcw t β).const_mul _),
    integral_const_mul, ibp_dir hg hgi u iu t β, ibp_dir hg hgi w iw t β]
  have h := lf_re_im t β (vkl k l)
  rw [sum_vkl] at h
  linear_combination (-(∫ y, g y * chr t β y)) * h

theorem contDiff_foldr {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List (Fin n × Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (L.foldr (fun kl g => Dkl kl.1 kl.2 g) f) := by
  induction L with
  | nil => simpa using hf
  | cons kl L ih => simpa using contDiff_dkl ih kl.1 kl.2

theorem ibp_list {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (β : E n)
    (hb : ∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧
      ∀ y, ‖L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y‖ ≤ h y) (L : List (Fin n × Fin n)) :
    ∫ y, L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y * chr t β y =
      (L.map fun kl => Complex.I * t * herm β kl.1 kl.2).prod * ∫ y, f y * chr t β y := by
  have hI : ∀ L : List (Fin n × Fin n), Integrable (L.foldr (fun kl g => Dkl kl.1 kl.2 g) f) := by
    intro L
    obtain ⟨h, hh, hbd⟩ := hb L
    exact integrable_of_bound (contDiff_foldr hf L).continuous hh hbd
  induction L with
  | nil => simp
  | cons kl L ih =>
    have h1 := hI (kl :: L)
    have h2 := hI ((kl.2, kl.1) :: L)
    simp only [List.foldr_cons] at h1 h2 ⊢
    rw [ibp_dkl (contDiff_foldr hf L) (hI L) kl.1 kl.2 h1 h2 t β, ih, List.map_cons, List.prod_cons]
    ring

theorem ibp : IBP := by
  intro n f t β hf ht hdet hb
  have hI : ∀ L : List (Fin n × Fin n), Integrable (L.foldr (fun kl g => Dkl kl.1 kl.2 g) f) := by
    intro L
    obtain ⟨h, hh, hbd⟩ := hb L
    exact integrable_of_bound (contDiff_foldr hf L).continuous hh hbd
  have hfold : ∀ σ : Equiv.Perm (Fin n), (List.finRange n).foldr (fun k g => Dkl k (σ k) g) f =
      ((List.finRange n).map fun k => (k, σ k)).foldr (fun kl g => Dkl kl.1 kl.2 g) f := by
    intro σ; rw [List.foldr_map]
  have hΔ : ∫ y, Delta f y * chr t β y = (Complex.I * t) ^ n * (herm β).det * ∫ y, f y * chr t β y := by
    have e : (fun y => Delta f y * chr t β y) = fun y => ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * (((List.finRange n).map fun k => (k, σ k)).foldr
          (fun kl g => Dkl kl.1 kl.2 g) f y * chr t β y) := by
      funext y
      simp only [Delta, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, hfold]
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [e, MeasureTheory.integral_finsetSum]
    swap
    · intro σ _
      exact (integrable_mul_chr (hI _) (contDiff_foldr hf _).continuous t β).const_mul _
    simp_rw [integral_const_mul, ibp_list hf t β hb, List.map_map]
    have hdet' : (herm β).det = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, herm β k (σ k) := by
      rw [← Matrix.det_transpose, Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      rfl
    rw [hdet', Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hp : (((List.finRange n).map ((fun kl : Fin n × Fin n => Complex.I * t * herm β kl.1 kl.2) ∘
        fun k => (k, σ k))).prod) = (Complex.I * t) ^ n * ∏ k, herm β k (σ k) := by
      rw [← Fin.prod_univ_def]
      simp only [Function.comp_apply]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hp]
    ring
  have hc : (Complex.I * t) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ht))
  rw [hΔ]
  have e2 : (-(Complex.I * t)) ^ n = (-1) ^ n * (Complex.I * t) ^ n := by rw [neg_eq_neg_one_mul, mul_pow]
  rw [e2]
  have h1 : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by rw [← mul_pow]; norm_num
  field_simp

end PositivityTheory.Rg.Sw.WR.Ib

namespace PositivityTheory.Rg.Sw.WR

theorem ibp : IBP := Ib.ibp

end PositivityTheory.Rg.Sw.WR
end
end
