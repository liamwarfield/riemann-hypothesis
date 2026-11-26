module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.DetSplit
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.TorusEigenvalueFormula
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.LowerInv
noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

def lowerInv_e (r : ℝ) : ℂ := Complex.exp ((r : ℂ) * Complex.I)

lemma lowerInv_e_mul_pow (r s : ℝ) (m : ℕ) :
    lowerInv_e r * lowerInv_e s ^ m = lowerInv_e (r + m * s) := by
  unfold lowerInv_e
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma lowerInv_conj_e (r : ℝ) : (starRingEnd ℂ) (lowerInv_e r) = lowerInv_e (-r) := by
  unfold lowerInv_e
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

lemma lowerInv_evM_affine {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ)
    (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ p : Polynomial ℂ, ∀ c : ℂ, evM (A + c • B) Q = p.eval c := by
  induction Q using MvPolynomial.induction_on with
  | C r => exact ⟨Polynomial.C r, fun c => by simp [evM]⟩
  | add p q hp hq =>
    obtain ⟨p1, h1⟩ := hp
    obtain ⟨q1, h2⟩ := hq
    refine ⟨p1 + q1, fun c => ?_⟩
    have e : evM (A + c • B) (p + q) = evM (A + c • B) p + evM (A + c • B) q := by
      simp [evM]
    rw [e, h1, h2, Polynomial.eval_add]
  | mul_X p i hp =>
    obtain ⟨p1, h1⟩ := hp
    refine ⟨p1 * (Polynomial.C (A i.1 i.2) + Polynomial.C (B i.1 i.2) * Polynomial.X), fun c => ?_⟩
    have e : evM (A + c • B) (p * X i) = evM (A + c • B) p * (A i.1 i.2 + c * B i.1 i.2) := by
      simp [evM]
    rw [e, h1, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, Polynomial.eval_X]
    ring

lemma lowerInv_torus_mem {N : ℕ} (θ : Fin N → ℝ) : torus θ ∈ Kset (allPos N) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, torus, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    simp
  · simp [Jm, allPos]

lemma lowerInv_torus_mul {N : ℕ} (θ φ : Fin N → ℝ) : torus θ * torus φ = torus (θ + φ) := by
  unfold torus
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.exp_add]
  congr 1
  push_cast [Pi.add_apply]
  ring

lemma lowerInv_torus_zero {N : ℕ} : torus (0 : Fin N → ℝ) = 1 := by
  unfold torus
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  simp

lemma lowerInv_det_ne {N : ℕ} (θ : Fin N → ℝ) : (torus θ).det ≠ 0 := by
  unfold torus
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Complex.exp_ne_zero _

lemma lowerInv_comm {N : ℕ} {a b : Fin N} (hab : a < b) (θ : Fin N → ℝ) (c : ℂ) :
    (1 + Matrix.single b a c) * torus θ =
      torus θ * (1 + Matrix.single b a (c * lowerInv_e (θ a - θ b))) := by
  have key : Complex.exp ((θ b : ℂ) * Complex.I) * lowerInv_e (θ a - θ b) =
      Complex.exp ((θ a : ℂ) * Complex.I) := by
    unfold lowerInv_e
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  ext i j
  simp only [torus, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, if_true]
    rw [Matrix.one_apply_ne (ne_of_gt hab), ← key]; ring
  · simp only [if_neg h, add_zero]
    by_cases hij : i = j
    · subst hij; ring
    · rw [Matrix.one_apply_ne hij]; ring

section
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)}

lemma lowerInv_inner_pres (hU : IsURepOn (Kset (allPos N)) σ) {g : Matrix (Fin N) (Fin N) ℂ}
    (hg : g ∈ Kset (allPos N)) (u w : H) : ⟪σ g u, σ g w⟫_ℂ = ⟪u, w⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g).toLinearMap, norm_map' := fun v => hU.2.1 g hg v }
  exact L.inner_map_map u w

lemma lowerInv_adj (hU : IsURepOn (Kset (allPos N)) σ) (θ : Fin N → ℝ) (y w : H) :
    ⟪y, σ (torus θ) w⟫_ℂ = ⟪σ (torus (-θ)) y, w⟫_ℂ := by
  have h1 : σ (torus θ) (σ (torus (-θ)) y) = y := by
    have h := hU.1.2 (torus θ) (lowerInv_torus_mem θ) (torus (-θ)) (lowerInv_torus_mem (-θ))
    rw [lowerInv_torus_mul, add_neg_cancel, lowerInv_torus_zero, hU.1.1] at h
    have h' := congrArg (fun f : H →L[ℂ] H => f y) h
    simpa using h'.symm
  rw [← lowerInv_inner_pres hU (lowerInv_torus_mem θ) (σ (torus (-θ)) y) w, h1]

end

lemma lowerInv_not_cdom {N : ℕ} {Λ : Fin N → ℝ} {a b : Fin N} (hab : a < b) {m : ℕ} (hm : 1 ≤ m) :
    ¬ CDom (allPos N) (Λ + (m : ℝ) • root a b) Λ := by
  rintro ⟨cc, hcc, heq⟩
  let L : (Fin N → ℝ) →ₗ[ℝ] ℝ := ∑ x : Fin N, ((x : ℕ) : ℝ) • LinearMap.proj x
  have hL : ∀ v, L v = ∑ x : Fin N, ((x : ℕ) : ℝ) * v x := by
    intro v; simp [L, LinearMap.sum_apply]
  have hroot : ∀ x y : Fin N, L (root x y) = ((x : ℕ) : ℝ) - ((y : ℕ) : ℝ) := by
    intro x y
    rw [hL]
    simp [root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
  have h1 := congrArg L heq
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hroot] at h1
  have lhs : L (Λ - (Λ + (m : ℝ) • root a b)) = (m : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [sub_add_cancel_left, map_neg, map_smul, hroot, smul_eq_mul]; ring
  rw [lhs] at h1
  have hle : ∑ x, ∑ y, (cc x y : ℝ) • (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => by
      by_cases h : cc x y = 0
      · simp [h]
      · have hxy : (x : ℕ) < y := (hcc x y h).1
        rw [smul_eq_mul]
        apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
        rw [sub_nonpos]; exact_mod_cast hxy.le
  have hpos : 0 < (m : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    apply mul_pos (by exact_mod_cast hm)
    rw [sub_pos]; exact_mod_cast hab
  linarith

lemma lowerInv_coeff_scale (p q : Polynomial ℂ) (D u : ℂ) (h : ∀ c, q.eval c = D * p.eval (c * u))
    (m : ℕ) : q.coeff m = D * u ^ m * p.coeff m := by
  have hq : q = Polynomial.C D * p.comp (Polynomial.C u * Polynomial.X) := by
    apply Polynomial.funext
    intro c
    rw [h, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, mul_comm u c]
  rw [hq, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff]
  ring

theorem lower_triangular_invariance : LowerInv := by
  intro N Λ H _ _ σ S K P hU hKT hP hPσ v0 hv0 a b hab c x
  have : FiniteDimensional ℂ S := hKT.1
  have hex : ∀ y : S, ∃ p : Polynomial ℂ, ∀ c : ℂ,
      p.eval c = ⟪v0, P (1 + Matrix.single b a c) y⟫_ℂ := by
    intro y
    obtain ⟨Q, hQ⟩ := hP.poly y v0
    obtain ⟨p, hp⟩ := lowerInv_evM_affine 1 (Matrix.single b a 1) Q
    refine ⟨p, fun c => ?_⟩
    rw [← hp c, hQ, Matrix.smul_single, smul_eq_mul, mul_one]
  choose pp hpp using hex
  have hadd : ∀ y z : S, pp (y + z) = pp y + pp z := fun y z => Polynomial.funext fun c => by
    rw [Polynomial.eval_add, hpp, hpp, hpp, map_add (f := _), inner_add_right]
  have hsmul : ∀ (r : ℂ) (y : S), pp (r • y) = Polynomial.C r * pp y := fun r y =>
    Polynomial.funext fun c => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, hpp, hpp, map_smul, inner_smul_right]
  let ψ : ℕ → S →ₗ[ℂ] ℂ := fun m =>
    { toFun := fun y => (pp y).coeff m
      map_add' := fun y z => by simp only [hadd, Polynomial.coeff_add]
      map_smul' := fun r y => by
        simp only [hsmul, Polynomial.coeff_C_mul, smul_eq_mul, RingHom.id_apply] }
  have hψ_apply : ∀ m (y : S), ψ m y = (pp y).coeff m := fun _ _ => rfl
  have hstab : ∀ θ (y : S), σ (torus θ) (y : H) ∈ S := fun θ y =>
    hKT.2.1 _ (lowerInv_torus_mem θ) _ y.2

  have hv0eig : ∀ (θ : Fin N → ℝ) (w : H),
      ⟪(v0 : H), σ (torus θ) w⟫_ℂ = lowerInv_e (∑ i, Λ i * θ i) * ⟪(v0 : H), w⟫_ℂ := by
    intro θ w
    have hw : σ (torus (-θ)) (v0 : H) =
        Complex.exp (((∑ i, Λ i * (-θ) i : ℝ) : ℂ) * Complex.I) • (v0 : H) :=
      hv0 (-θ) (lowerInv_torus_mem (-θ))
    rw [lowerInv_adj hU θ, hw, inner_smul_left]
    have := lowerInv_conj_e (∑ i, Λ i * (-θ) i)
    unfold lowerInv_e at this ⊢
    rw [this]
    congr 3
    simp [Finset.sum_neg_distrib]
  have hv0P : ∀ θ (y : S), ⟪v0, P (torus θ) y⟫_ℂ =
      (torus θ).det ^ K * lowerInv_e (∑ i, Λ i * θ i) * ⟪v0, y⟫_ℂ := by
    intro θ y
    rw [Submodule.coe_inner, hPσ _ (lowerInv_torus_mem θ), inner_smul_right, hv0eig,
      Submodule.coe_inner, mul_assoc]
  have hrel : ∀ θ (y : S) (c : ℂ), (pp (P (torus θ) y)).eval c =
      ((torus θ).det ^ K * lowerInv_e (∑ i, Λ i * θ i)) *
        (pp y).eval (c * lowerInv_e (θ a - θ b)) := by
    intro θ y c
    rw [hpp, hpp, ← LinearMap.comp_apply, ← hP.mul, lowerInv_comm hab, hP.mul, LinearMap.comp_apply,
      hv0P]
  have hψ : ∀ m, 1 ≤ m → ψ m = 0 := by
    intro m hm
    let y : S := (InnerProductSpace.toDual ℂ S).symm (LinearMap.toContinuousLinearMap (ψ m))
    have hyx : ∀ z : S, ⟪y, z⟫_ℂ = ψ m z := fun z => by
      rw [InnerProductSpace.toDual_symm_apply]; rfl
    have hsc : ∀ θ (z : S), ψ m (P (torus θ) z) =
        (torus θ).det ^ K * lowerInv_e (∑ i, Λ i * θ i) * lowerInv_e (θ a - θ b) ^ m * ψ m z :=
      fun θ z => by
        rw [hψ_apply, hψ_apply, lowerInv_coeff_scale _ _ _ _ (hrel θ z) m]
    have hwt : IsWtOn (Kset (allPos N)) σ (Λ + (m : ℝ) • root a b) (y : H) := by
      intro θ _
      show σ (torus θ) (y : H) = _
      have key : ∀ z : S, ⟪σ (torus θ) (y : H), (z : H)⟫_ℂ =
          lowerInv_e (∑ i, Λ i * (-θ) i) * lowerInv_e ((-θ) a - (-θ) b) ^ m * ⟪(y : H), (z : H)⟫_ℂ := by
        intro z
        have h1 := hsc (-θ) z
        rw [← hyx, ← hyx, Submodule.coe_inner, Submodule.coe_inner, hPσ _ (lowerInv_torus_mem _),
          inner_smul_right, lowerInv_adj hU, neg_neg, mul_assoc ((torus (-θ)).det ^ K),
          mul_assoc ((torus (-θ)).det ^ K)] at h1
        exact mul_left_cancel₀ (pow_ne_zero _ (lowerInv_det_ne (-θ))) h1
      have hE : lowerInv_e (∑ i, Λ i * (-θ) i) * lowerInv_e ((-θ) a - (-θ) b) ^ m =
          (starRingEnd ℂ) (Complex.exp (((∑ i, (Λ + (m : ℝ) • root a b) i * θ i : ℝ) : ℂ) *
            Complex.I)) := by
        rw [lowerInv_e_mul_pow]
        have := lowerInv_conj_e (∑ i, (Λ + (m : ℝ) • root a b) i * θ i)
        unfold lowerInv_e at this ⊢
        rw [this]
        congr 3
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, root, Pi.sub_apply,
          add_mul, Finset.sum_add_distrib, mul_sub, sub_mul, Finset.sum_sub_distrib, Pi.single_apply,
          mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true, mul_neg, Finset.sum_neg_distrib]
        ring
      set ev := Complex.exp (((∑ i, (Λ + (m : ℝ) • root a b) i * θ i : ℝ) : ℂ) * Complex.I)
      let w : S := ⟨σ (torus θ) (y : H), hstab θ y⟩ - ev • y
      have hw0 : ∀ z : S, ⟪w, z⟫_ℂ = 0 := by
        intro z
        rw [inner_sub_left, inner_smul_left, Submodule.coe_inner, Submodule.coe_inner]
        show ⟪σ (torus θ) (y : H), (z : H)⟫_ℂ - _ = 0
        rw [key, hE, sub_self]
      have hw : w = 0 := inner_self_eq_zero.mp (hw0 w)
      have := congrArg (fun u : S => (u : H)) hw
      simp only [w, Submodule.coe_sub, Submodule.coe_smul, ZeroMemClass.coe_zero] at this
      exact sub_eq_zero.mp this
    by_contra hne
    have hy0 : (y : H) ≠ 0 := by
      intro h0
      apply hne
      ext z
      rw [← hyx, Submodule.coe_inner, h0, inner_zero_left]
      rfl
    exact lowerInv_not_cdom hab hm (hKT.2.2.2.2 _ (y : H) y.2 hy0 hwt)
  have hconst : pp x = Polynomial.C ((pp x).coeff 0) := by
    ext m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Polynomial.coeff_C, if_neg (by omega)]
      have := LinearMap.congr_fun (hψ m hm) x
      rw [hψ_apply] at this
      simpa using this
  have h0 := hpp x 0
  rw [Matrix.single_zero, add_zero, hP.one, LinearMap.id_apply] at h0
  rw [← hpp, hconst, Polynomial.eval_C]
  rw [hconst, Polynomial.eval_C] at h0
  exact h0

end PI.WMI
end
end

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem lambda_integrality : LamInt := by
  intro N Λ H _ _ σ v hU hv hw a
  have hfun : (fun b => Complex.exp ((((Pi.single a (2 * Real.pi) : Fin N → ℝ) b : ℝ) : ℂ) * Complex.I))
      = fun _ => (1 : ℂ) := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Pi.single_eq_same]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [hb]
  have hmem := lowerInv_torus_mem (N := N) (Pi.single a (2 * Real.pi))
  have h := hw (Pi.single a (2 * Real.pi)) hmem
  rw [hfun, Matrix.diagonal_one, hU.1.1] at h
  have hsum : (∑ b, Λ b * (Pi.single a (2 * Real.pi) : Fin N → ℝ) b) = Λ a * (2 * Real.pi) := by
    simp [Pi.single_apply]
  rw [hsum] at h
  have he : Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    by_contra hne
    apply hv
    have h2 : (1 - Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) • v = 0 := by
      rw [sub_smul, one_smul, ← h]
      simp
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨n, ?_⟩
  have hpi : (2 * (Real.pi : ℂ)) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (Λ a : ℂ) = (n : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  exact_mod_cast this

theorem torus_eigenvalue_formula : TorusEig := by
  intro N Λ H _ _ σ S K P hU hstab hPσ v0 hw θ x
  have hwt : σ (torus (-θ)) (v0 : H) =
      Complex.exp (((∑ a, Λ a * (-θ) a : ℝ) : ℂ) * Complex.I) • (v0 : H) :=
    hw (-θ) (lowerInv_torus_mem (-θ))
  have hdet : (torus θ).det = Complex.exp (((∑ a, θ a : ℝ) : ℂ) * Complex.I) := by
    rw [torus, Matrix.det_diagonal]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  rw [Submodule.coe_inner, hPσ (torus θ) (lowerInv_torus_mem θ) x, inner_smul_right,
    lowerInv_adj hU θ, hwt, inner_smul_left, ← Submodule.coe_inner, hdet, ← Complex.exp_nat_mul,
    ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  simp only [Pi.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  ring_nf
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

end PI.WMI
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.ModelMap
noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

namespace MMap

lemma eval_aeval_eq {σ τ : Type*} (y : τ → ℂ) (g : σ → MvPolynomial τ ℂ) (f : MvPolynomial σ ℂ) :
    eval y (aeval g f) = eval (fun i => eval y (g i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

lemma poly_ext {N : ℕ} {p q : MvPolynomial (Fin N × Fin N) ℂ}
    (h : ∀ A : Matrix (Fin N) (Fin N) ℂ, evM A p = evM A q) : p = q := by
  apply MvPolynomial.funext
  intro x
  have := h (Matrix.of fun i j => x (i, j))
  simpa [evM] using this

lemma evM_add {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (p + q) = evM A p + evM A q := by simp [evM]

lemma evM_smul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (c • p) = c * evM A p := by
  rw [evM, evM, smul_eq_C_mul, eval_mul, eval_C]

lemma evM_C_mul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (C c * p) = c * evM A p := by
  rw [evM, evM, eval_mul, eval_C]

lemma evM_rename_swap {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (q : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (rename Prod.swap q) = evM Aᵀ q := by
  simp only [evM, eval_rename]
  rfl

lemma evM_rowAct {N : ℕ} (g A : Matrix (Fin N) (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (rowAct ℂ (n := N) g f) = evM (g * A) f := by
  unfold rowAct evM
  rw [eval_aeval_eq]
  refine congrArg (fun y => eval y f) (funext fun v => ?_)
  simp [Matrix.mul_apply]

lemma evM_colAdd {N : ℕ} (l j : Fin N) (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (colAdd ℂ (r := N) l j c f) = evM (A * (1 + Matrix.single l j c)) f := by
  unfold colAdd evM
  rw [eval_aeval_eq]
  refine congrArg (fun y => eval y f) (funext fun v => ?_)
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  split_ifs with h
  · simp [Matrix.mul_apply, Matrix.single_apply, h, mul_comm]
  · have h' : j ≠ v.2 := fun e => h e.symm
    simp [Matrix.mul_apply, Matrix.single_apply, h']

lemma evM_scale {N : ℕ} (t : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (aeval (fun v : Fin N × Fin N => C (t v.2) * X v) f) = evM (A * Matrix.diagonal t) f := by
  unfold evM
  rw [eval_aeval_eq]
  refine congrArg (fun y => eval y f) (funext fun v => ?_)
  simp [Matrix.mul_diagonal, mul_comm]

lemma aeval_scale_monomial {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℂ) (u : σ →₀ ℕ) (c : ℂ) :
    aeval (fun v : σ => C (w v) * X v) (monomial u c) = monomial u (c * ∏ v, w v ^ u v) := by
  rw [aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (w v) : MvPolynomial σ ℂ) ^ e) = C (u.prod fun v e => w v ^ e) := by
    rw [map_finsuppProd]; simp only [map_pow]
  rw [hC, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), monomial_eq, C_mul, algebraMap_eq]
  ring

lemma coeff_scale {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℂ) (f : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun v : σ => C (w v) * X v) f) m = AddMonoidAlgebra.coeff f m * ∏ v, w v ^ m v := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, add_mul]

lemma prod_exp {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (θ : Fin N → ℝ) :
    ∏ v : Fin N × Fin N, Complex.exp ((θ v.2 : ℂ) * Complex.I) ^ m v =
      Complex.exp (((∑ v : Fin N × Fin N, (m v : ℝ) * θ v.2 : ℝ) : ℂ) * Complex.I) := by
  simp_rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => by ring

lemma real_eq_of_exp {d c : ℝ}
    (h : ∀ τ : ℝ, Complex.exp (((τ * d : ℝ) : ℂ) * Complex.I) = Complex.exp (((τ * c : ℝ) : ℂ) * Complex.I)) :
    d = c := by
  by_contra hne
  have hk : d - c ≠ 0 := sub_ne_zero.mpr hne
  have h1 := h (Real.pi / (d - c))
  have h2 : Complex.exp (((Real.pi / (d - c) * d : ℝ) : ℂ) * Complex.I -
      ((Real.pi / (d - c) * c : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 : ((Real.pi / (d - c) * d : ℝ) : ℂ) * Complex.I - ((Real.pi / (d - c) * c : ℝ) : ℂ) * Complex.I =
      (Real.pi : ℂ) * Complex.I := by
    rw [← sub_mul]
    congr 1
    rw [← Complex.ofReal_sub]
    congr 1
    field_simp
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

lemma weight_colW {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (s : Fin N) :
    Finsupp.weight (colW N N) m s = ∑ v : Fin N × Fin N, if v.2 = s then m v else 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : v.2 = s
  · subst h; simp [colW]
  · simp [colW, h, Ne.symm h]

section

variable {N : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {P : Matrix (Fin N) (Fin N) ℂ → (V →ₗ[ℂ] V)} (hP : IsPolyMon P) (v0 : V)

def Fq (x : V) : MvPolynomial (Fin N × Fin N) ℂ :=
  rename Prod.swap (Classical.choose (hP.poly x v0))

lemma evM_Fq (x : V) (A : Matrix (Fin N) (Fin N) ℂ) : evM A (Fq hP v0 x) = ⟪v0, P Aᵀ x⟫_ℂ := by
  unfold Fq
  rw [evM_rename_swap]
  exact Classical.choose_spec (hP.poly x v0) Aᵀ

def Fl : V →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ where
  toFun := Fq hP v0
  map_add' x y := poly_ext fun A => by
    rw [evM_add, evM_Fq, evM_Fq, evM_Fq, map_add (f := _), inner_add_right]
  map_smul' c x := poly_ext fun A => by
    rw [RingHom.id_apply, evM_smul, evM_Fq, evM_Fq, map_smul, inner_smul_right]

lemma Fl_apply (x : V) : Fl hP v0 x = Fq hP v0 x := rfl

lemma Fq_intertwine (g : Matrix (Fin N) (Fin N) ℂ) (x : V) :
    Fq hP v0 (P g x) = rowAct ℂ (n := N) gᵀ (Fq hP v0 x) := poly_ext fun A => by
  rw [evM_rowAct, evM_Fq, evM_Fq, Matrix.transpose_mul, Matrix.transpose_transpose, hP.mul,
    LinearMap.comp_apply]

lemma Fq_colAdd
    (hlow : ∀ a b : Fin N, a < b → ∀ (c : ℂ) (x : V), ⟪v0, P (1 + Matrix.single b a c) x⟫_ℂ = ⟪v0, x⟫_ℂ)
    (l j : Fin N) (hlj : l < j) (c : ℂ) (x : V) :
    colAdd ℂ (r := N) l j c (Fq hP v0 x) = Fq hP v0 x := poly_ext fun A => by
  rw [evM_colAdd, evM_Fq, evM_Fq, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, hP.mul, LinearMap.comp_apply, hlow l j hlj]

lemma Fq_scale (μ : Fin N → ℤ) (K : ℕ)
    (htor : ∀ (θ : Fin N → ℝ) (x : V), ⟪v0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪v0, x⟫_ℂ)
    (θ : Fin N → ℝ) (x : V) :
    aeval (fun v : Fin N × Fin N => C (Complex.exp ((θ v.2 : ℂ) * Complex.I)) * X v) (Fq hP v0 x) =
      C (Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I)) * Fq hP v0 x :=
  poly_ext fun A => by
    rw [evM_scale (fun s => Complex.exp ((θ s : ℂ) * Complex.I)), evM_C_mul, evM_Fq, evM_Fq, Matrix.transpose_mul, Matrix.diagonal_transpose, ← htor θ,
      hP.mul, LinearMap.comp_apply]
    rfl

lemma Fq_deg (μ : Fin N → ℤ) (K : ℕ)
    (htor : ∀ (θ : Fin N → ℝ) (x : V), ⟪v0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪v0, x⟫_ℂ)
    (x : V) (m : Fin N × Fin N →₀ ℕ) (hm : AddMonoidAlgebra.coeff (Fq hP v0 x) m ≠ 0) (s : Fin N) :
    (((∑ v : Fin N × Fin N, if v.2 = s then m v else 0 : ℕ)) : ℤ) = μ s + K := by
  have key : ((∑ v : Fin N × Fin N, if v.2 = s then m v else 0 : ℕ) : ℝ) = (μ s : ℝ) + K := by
    apply real_eq_of_exp
    intro τ
    have h1 := congrArg (AddMonoidAlgebra.coeff · m) (Fq_scale hP v0 μ K htor (fun s' => if s' = s then τ else 0) x)
    rw [coeff_scale, coeff_C_mul, mul_comm (Complex.exp _), prod_exp m (fun s' => if s' = s then τ else 0)] at h1
    have h2 := mul_left_cancel₀ hm h1
    have e1 : (∑ v : Fin N × Fin N, (m v : ℝ) * (if v.2 = s then τ else 0)) =
        τ * ((∑ v : Fin N × Fin N, if v.2 = s then m v else 0 : ℕ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> ring
    have e2 : (∑ a : Fin N, ((μ a : ℝ) + K) * (if a = s then τ else 0)) = τ * ((μ s : ℝ) + K) := by
      simp [mul_ite, Finset.sum_ite_eq']
      ring
    rw [e1, e2] at h2
    exact h2
  exact_mod_cast key

end

end MMap

open MMap in
theorem model_map_equivariance : ModelMap := by
  intro N V _ _ _ P v0 μ K hP hv0 htor hlow
  have hF0 : Fq hP v0 v0 ≠ 0 := by
    intro h
    have h1 := evM_Fq hP v0 v0 1
    rw [h, Matrix.transpose_one, hP.one, LinearMap.id_apply] at h1
    have h2 : evM (1 : Matrix (Fin N) (Fin N) ℂ) (0 : MvPolynomial (Fin N × Fin N) ℂ) = 0 := by simp [evM]
    rw [h2] at h1
    exact hv0 (inner_self_eq_zero.mp h1.symm)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hF0
  have hnn : ∀ s, 0 ≤ μ s + K := fun s => by
    rw [← Fq_deg hP v0 μ K htor v0 m0 hm0 s]
    positivity
  refine ⟨fun s => (μ s + K).toNat, Fl hP v0, fun s => Int.toNat_of_nonneg (hnn s), ?_, hF0, ?_⟩
  · intro x
    rw [Fl_apply, dualWeylPoint ℂ N N _ _]
    refine ⟨?_, fun l j hlj c => Fq_colAdd hP v0 hlow l j hlj c x⟩
    intro m hm
    funext s
    rw [weight_colW]
    have h1 := Fq_deg hP v0 μ K htor x m hm s
    have h2 := Int.toNat_of_nonneg (hnn s)
    omega
  · intro g x
    rw [Fl_apply, Fl_apply]
    exact Fq_intertwine hP v0 g x

end PI.WMI
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.PolyExt
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.PolyExtLem
noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

lemma pe_evM_detPoly {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) : evM g (detPoly N) = g.det := by
  unfold evM detPoly
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

lemma pe_one_mem (N : ℕ) : (1 : Matrix (Fin N) (Fin N) ℂ) ∈ Kset (allPos N) := by
  refine ⟨one_mem _, by simp⟩

lemma pe_mul_mem {N : ℕ} {g h : Matrix (Fin N) (Fin N) ℂ} (hg : g ∈ Kset (allPos N)) (hh : h ∈ Kset (allPos N)) :
    g * h ∈ Kset (allPos N) := by
  refine ⟨mul_mem hg.1 hh.1, ?_⟩
  rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

lemma pe_unitary_mem {N : ℕ} (u : Matrix (Fin N) (Fin N) ℂ) (hu : uᴴ * u = 1) : u ∈ Kset (allPos N) := by
  have hJ : Jm (allPos N) = 1 := by
    unfold Jm allPos
    simp
  refine ⟨?_, by rw [hJ]; simp⟩
  rw [Matrix.mem_unitaryGroup_iff']
  exact hu

lemma pe_right {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ Q' : MvPolynomial (Fin N × Fin N) ℂ, ∀ g, evM g Q' = evM (g * h) Q := by
  refine ⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, X (pq.1, r) * C (h r pq.2)) Q, fun g => ?_⟩
  induction Q using MvPolynomial.induction_on with
  | C a => simp [evM]
  | add p q hp hq => simp only [map_add (f := _), evM] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, evM, bind₁_X_right] at *
    rw [hp]
    simp [Matrix.mul_apply]

lemma pe_left {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ Q' : MvPolynomial (Fin N × Fin N) ℂ, ∀ h, evM h Q' = evM (g * h) Q := by
  refine ⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, C (g pq.1 r) * X (r, pq.2)) Q, fun h => ?_⟩
  induction Q using MvPolynomial.induction_on with
  | C a => simp [evM]
  | add p q hp hq => simp only [map_add (f := _), evM] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, evM, bind₁_X_right] at *
    rw [hp]
    simp [Matrix.mul_apply]

end PI.WMI
end
end

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem polyExt_of (hp : PI.PolyCoef) (hu : PI.UnitaryDense) : PolyExt := by
  intro N H _ _ σ S hσ hfin hS
  classical
  let d := Module.finrank ℂ S
  let b : OrthonormalBasis (Fin d) ℂ S := stdOrthonormalBasis ℂ S
  have hc : ∀ i j : Fin d, ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ), ∀ g ∈ Kset (allPos N),
      inner ℂ ((b i : S) : H) (σ g ((b j : S) : H)) * g.det ^ k =
        MvPolynomial.eval (fun ij => g ij.1 ij.2) P :=
    fun i j => hp N H σ S hσ hfin hS ((b j : S) : H) (b j).2 ((b i : S) : H)
  choose k P hkP using hc
  let K : ℕ := ∑ p : Fin d × Fin d, k p.1 p.2
  have hk : ∀ i j, k i j ≤ K := fun i j =>
    Finset.single_le_sum (f := fun p : Fin d × Fin d => k p.1 p.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (i, j))
  let Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) ℂ := fun i j => P i j * detPoly N ^ (K - k i j)
  have hQ : ∀ g ∈ Kset (allPos N), ∀ i j,
      evM g (Q i j) = g.det ^ K * ⟪((b i : S) : H), σ g ((b j : S) : H)⟫_ℂ := by
    intro g hg i j
    have e1 : evM g (Q i j) = evM g (P i j) * g.det ^ (K - k i j) := by
      rw [← pe_evM_detPoly g]
      simp only [Q, evM, map_mul, map_pow]
    rw [e1, show evM g (P i j) = _ from (hkP i j g hg).symm, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (hk i j), mul_comm]
  let Pm : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin d) (Fin d) ℂ := fun g => Matrix.of fun i j => evM g (Q i j)
  let Pl : Matrix (Fin N) (Fin N) ℂ → (S →ₗ[ℂ] S) := fun g => Matrix.toLin b.toBasis b.toBasis (Pm g)
  have hA : ∀ g ∈ Kset (allPos N), ∀ x : S, ((Pl g x : S) : H) = g.det ^ K • σ g (x : H) := by
    intro g hg x
    have key : S.subtype ∘ₗ Pl g = g.det ^ K • ((σ g : H →ₗ[ℂ] H) ∘ₗ S.subtype) := by
      refine b.toBasis.ext fun j => ?_
      have hmem : σ g ((b j : S) : H) ∈ S := hS g hg _ (b j).2
      have hsum := b.sum_repr' (⟨σ g ((b j : S) : H), hmem⟩ : S)
      have hsumH := congrArg (fun y : S => (y : H)) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hsumH
      show ((Matrix.toLin b.toBasis b.toBasis (Pm g) (b.toBasis j) : S) : H) =
        g.det ^ K • σ g ((b.toBasis j : S) : H)
      rw [Matrix.toLin_self]
      simp only [OrthonormalBasis.coe_toBasis, Submodule.coe_sum, Submodule.coe_smul, Pm, Matrix.of_apply]
      conv_rhs => rw [← hsumH]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hQ g hg i j, smul_smul]
    exact congrArg (fun f : S →ₗ[ℂ] H => f x) key
  have hPlmul : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pl (g * h) = Pl g ∘ₗ Pl h := by
    intro g hg h hh
    ext x
    rw [LinearMap.comp_apply, hA _ (pe_mul_mem hg hh), hA g hg, hA h hh, hσ.1.2 g hg h hh,
      ContinuousLinearMap.comp_apply, map_smul, smul_smul, Matrix.det_mul, mul_pow]
  have hB : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pm (g * h) = Pm g * Pm h := by
    intro g hg h hh
    apply (Matrix.toLin b.toBasis b.toBasis).injective
    rw [Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]
    exact hPlmul g hg h hh
  have hC1 : ∀ h ∈ Kset (allPos N), ∀ g, Pm (g * h) = Pm g * Pm h := by
    intro h hh g
    ext i j
    obtain ⟨Q', hQ'⟩ := pe_right h (Q i j)
    let D := Q' - ∑ r, Q i r * C (Pm h r j)
    have hD : ∀ g', evM g' D = (Pm (g' * h) - Pm g' * Pm h) i j := by
      intro g'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢
      rw [hQ']
      simp [Pm, evM, Matrix.mul_apply]
    have hD0 : D = 0 := hu N D fun u hu' => by
      rw [← evM, hD u, hB u (pe_unitary_mem u hu') h hh, sub_self, Matrix.zero_apply]
    have := hD g
    rw [hD0] at this
    simp only [evM, map_zero, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this.symm
  have hC2 : ∀ g h, Pm (g * h) = Pm g * Pm h := by
    intro g h
    ext i j
    obtain ⟨Q', hQ'⟩ := pe_left g (Q i j)
    let D := Q' - ∑ r, C (Pm g i r) * Q r j
    have hD : ∀ h', evM h' D = (Pm (g * h') - Pm g * Pm h') i j := by
      intro h'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢
      rw [hQ']
      simp [Pm, evM, Matrix.mul_apply]
    have hD0 : D = 0 := hu N D fun u hu' => by
      rw [← evM, hD u, hC1 u (pe_unitary_mem u hu') g, sub_self, Matrix.zero_apply]
    have := hD h
    rw [hD0] at this
    simp only [evM, map_zero, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this.symm
  refine ⟨K, Pl, ⟨?_, ?_, ?_⟩, hA⟩
  · intro g h
    show Matrix.toLin b.toBasis b.toBasis (Pm (g * h)) = _
    rw [hC2, Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]
  · ext x
    rw [hA 1 (pe_one_mem N), hσ.1.1]
    simp
  · intro x y
    let fL : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ :=
      (innerₛₗ ℂ y).comp ((LinearMap.applyₗ x).comp (Matrix.toLin b.toBasis b.toBasis).toLinearMap)
    refine ⟨∑ i, ∑ j, Q i j * C (fL (Matrix.single i j 1)), fun g => ?_⟩
    have hf : ⟪y, Pl g x⟫_ℂ = fL (Pm g) := rfl
    rw [hf, Matrix.matrix_eq_sum_single (Pm g)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, evM, map_mul, eval_C]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (Pm g i j) = Pm g i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    rfl

end PI.WMI
end
end

theorem modelIso_of : PI.PolyCoef → PI.UnitaryDense → PI.HwIrred → PI.ModelIso :=
  fun hp hu hh => PI.WMI.modelIso_of_steps (PI.WMI.polyExt_of hp hu) PI.WMI.lambda_integrality
    PI.WMI.torus_eigenvalue_formula PI.WMI.lower_triangular_invariance PI.WMI.model_map_equivariance PI.WMI.determinant_splitting_formula hh
