module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFact

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacB
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacA
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

def ptX {m : ℕ} (u : Matrix (Fin m) (Fin n) ℂ) : Fin m × Fin n × Bool → ℂ := fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1

theorem evX_eq_eval {m : ℕ} (Q : PX m n) (u : Matrix (Fin m) (Fin n) ℂ) : evX Q u = eval (ptX u) Q := rfl

theorem ptX_add_smul {m : ℕ} (u w : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    ptX (u + (t : ℂ) • w) = ptX u + (t : ℂ) • ptX w := by
  funext k
  simp only [ptX, Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [Complex.conj_ofReal]

theorem gAway_add_dirAt (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (X : Matrix (Fin V.rank) (Fin n) ℂ) (t : ℝ) :
    gAway V l s τ (z + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X) = gAway V l s τ z := by
  have hz : ∀ τ', τ' ≠ τ → (z + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X) τ' = z τ' := by
    intro τ' h
    rw [Pi.add_apply, Pi.smul_apply, dirAt_ne h, smul_zero, add_zero]
  delta gAway
  beta_reduce
  congr 2
  refine Finset.sum_congr rfl fun τ' hτ' => ?_
  rw [hz τ' (by simpa using hτ')]

theorem gaussian_vacuum_add_line {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) (x : Mx D V.rank n)
    (X : Matrix (Fin V.rank) (Fin n) ℂ) (t : ℝ) :
    psi0 θ V n l s τ (x + lineAt θ τ X t) = psi0 θ V n l s τ x := by
  obtain ⟨-, hfinL, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ X
  have h1 : (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) =
      (fun τ' => compAt θ τ' x) + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X := by
    funext τ'
    have hadd : compAt θ τ' (x + lineAt θ τ X t) = compAt θ τ' x + compAt θ τ' (lineAt θ τ X t) := by
      ext i j
      show (θ τ') (infPart D ((x + lineAt θ τ X t) i j)) =
        (θ τ') (infPart D (x i j)) + (θ τ') (infPart D (lineAt θ τ X t i j))
      rw [show (x + lineAt θ τ X t) i j = x i j + lineAt θ τ X t i j from rfl, map_add (f := _), map_add (f := _)]
    rw [hadd, hcomp t τ', Pi.add_apply, Pi.smul_apply]
    by_cases h : τ' = τ
    · rw [if_pos h, h, dirAt_self]
    · rw [if_neg h, dirAt_ne h, smul_zero]
  have h2 : (fun i j => finPart D ((x + lineAt θ τ X t) i j)) = (fun i j => finPart D (x i j)) := by
    funext i j
    have h0 : finPart D (lineAt θ τ X t i j) = 0 := congrFun (congrFun (hfinL t) i) j
    rw [show (x + lineAt θ τ X t) i j = x i j + lineAt θ τ X t i j from rfl, map_add (f := _), h0, add_zero]
  show gAway V l s τ (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) *
      g0 D V.rank n (fun i j => finPart D ((x + lineAt θ τ X t) i j)) =
    gAway V l s τ (fun τ' => compAt θ τ' x) * g0 D V.rank n (fun i j => finPart D (x i j))
  rw [h1, h2, gAway_add_dirAt]

private theorem hasDerivAt_mvPolynomial_eval_line_zero {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℂ) (a v : σ → ℂ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (a + (t : ℂ) • v) p)
      (∑ k, v k * MvPolynomial.eval a (MvPolynomial.pderiv k p)) 0 := by
  induction p using MvPolynomial.induction_on
  next r =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  next p q hp hq =>
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  next p i hp =>
    have hX : HasDerivAt (fun t : ℝ => (a + (t : ℂ) • v) i) (v i) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
      have h2 := (h1.mul_const (v i)).const_add (a i)
      simpa using h2
    have h := hp.mul hX
    simp only [map_mul, MvPolynomial.eval_X]
    refine h.congr_deriv ?_
    have hk : ∀ k, MvPolynomial.eval a (MvPolynomial.pderiv k (p * MvPolynomial.X i)) =
        MvPolynomial.eval a (MvPolynomial.pderiv k p) * a i +
          (if i = k then MvPolynomial.eval a p else 0) := by
      intro k
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul,
        MvPolynomial.eval_X, Pi.single_apply]
      split_ifs with h
      · simp only [map_one, mul_one]
        ring
      · simp only [map_zero, mul_zero, zero_add, add_zero]
        ring
    have hs1 : ∑ k, v k * (MvPolynomial.eval a (MvPolynomial.pderiv k p) * a i) =
        (∑ k, v k * MvPolynomial.eval a (MvPolynomial.pderiv k p)) * a i := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hs2 : ∑ k, v k * (if i = k then MvPolynomial.eval a p else 0) = MvPolynomial.eval a p * v i := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
        ring
      · intro b _ hb
        rw [if_neg (Ne.symm hb), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    simp only [hk, mul_add, Finset.sum_add_distrib, hs1, hs2, Complex.ofReal_zero, zero_smul, add_zero]

private theorem hasDerivAt_norm_sq_add_smul_zero (u w : ℂ) :
    HasDerivAt (fun t : ℝ => ‖u + (t : ℂ) * w‖ ^ 2) (2 * (star u * w).re) 0 := by
  have h : (fun t : ℝ => ‖u + (t : ℂ) * w‖ ^ 2) =
      fun t : ℝ => (u.re + t * w.re) * (u.re + t * w.re) + (u.im + t * w.im) * (u.im + t * w.im) := by
    funext t
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  rw [h]
  have h1 : HasDerivAt (fun t : ℝ => u.re + t * w.re) w.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.re).const_add u.re
  have h2 : HasDerivAt (fun t : ℝ => u.im + t * w.im) w.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.im).const_add u.im
  refine ((h1.mul h1).add (h2.mul h2)).congr_deriv ?_
  show _ = 2 * ((starRingEnd ℂ) u * w).re
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem hasDerivAt_gs_line_zero {m : ℕ} (c : ℝ) (U W : Matrix (Fin m) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => gs c (U + (t : ℂ) • W))
      (gs c U * (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ))) 0 := by
  have hr : HasDerivAt (fun t : ℝ => c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2)
      (c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re) 0 := by
    refine HasDerivAt.const_mul c ?_
    first
      | exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun i _ => hasDerivAt_norm_sq_add_smul_zero (U a i) (W a i)
      | exact HasDerivAt.sum fun a _ => HasDerivAt.sum fun i _ => hasDerivAt_norm_sq_add_smul_zero (U a i) (W a i)
  have hn : HasDerivAt (fun t : ℝ => -((c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2 : ℝ) : ℂ))
      (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ)) 0 := hr.ofReal_comp.neg
  have hc := hn.cexp
  have e0 : (fun t : ℝ => gs c (U + (t : ℂ) • W)) =
      fun t : ℝ => Complex.exp (-((c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2 : ℝ) : ℂ)) := by
    funext t
    rfl
  rw [e0]
  refine hc.congr_deriv ?_
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  rfl

theorem annS_tens {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (X : Matrix (Fin V.rank) (Fin n) ℂ) (x : Mx D V.rank n) :
    annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) x =
      (∑ k, ptX (fr⁻¹ * X) k * eval (ptX (fr⁻¹ * compAt θ τ x)) (pderiv k Q)) *
        gs (cLoc l τ) (fr⁻¹ * compAt θ τ x) * psi0 θ V n l s τ x := by
  obtain ⟨-, -, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ X
  set c := cLoc l τ with hc
  set z := compAt θ τ x with hz
  set U : Matrix (Fin V.rank) (Fin n) ℂ := fr⁻¹ * z with hU
  set W : Matrix (Fin V.rank) (Fin n) ℂ := fr⁻¹ * X with hW
  set Ψx := psi0 θ V n l s τ x with hΨ
  have hadd : ∀ y : Mx D V.rank n, compAt θ τ (x + y) = z + compAt θ τ y := by
    intro y
    ext i j
    show (θ τ) (infPart D ((x + y) i j)) = (θ τ) (infPart D (x i j)) + (θ τ) (infPart D (y i j))
    rw [show (x + y) i j = x i j + y i j from rfl, map_add (f := _), map_add (f := _)]
  have hcz : ∀ t : ℝ, compAt θ τ (x + lineAt θ τ X t) = z + (t : ℂ) • X := by
    intro t
    rw [hadd, hcomp t τ, if_pos rfl]
  have hφ : ∀ t : ℝ, tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t) =
      eval (ptX U + (t : ℂ) • ptX W) Q * gs c (U + (t : ℂ) • W) * Ψx := by
    intro t
    have e1 : fr⁻¹ * compAt θ τ (x + lineAt θ τ X t) = U + (t : ℂ) • W := by
      rw [hcz t, Matrix.mul_add, Matrix.mul_smul]
    show fP c Q (fr⁻¹ * compAt θ τ (x + lineAt θ τ X t)) * psi0 θ V n l s τ (x + lineAt θ τ X t) = _
    rw [e1, gaussian_vacuum_add_line hθ V l s τ x X t]
    show evX Q (U + (t : ℂ) • W) * gs c (U + (t : ℂ) • W) * Ψx = _
    rw [evX_eq_eval, ptX_add_smul]
  have hderiv : HasDerivAt (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t))
      ((∑ k, ptX W k * eval (ptX U) (pderiv k Q)) * gs c U * Ψx +
        eval (ptX U) Q * (gs c U * (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ))) * Ψx) 0 := by
    have hP := hasDerivAt_mvPolynomial_eval_line_zero Q (ptX U) (ptX W)
    have hG := hasDerivAt_gs_line_zero c U W
    rw [show (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t)) =
        fun t : ℝ => eval (ptX U + (t : ℂ) • ptX W) Q * gs c (U + (t : ℂ) • W) * Ψx from funext hφ]
    refine ((hP.mul hG).mul_const Ψx).congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_smul, add_zero]
    ring
  have hφx : tens θ τ fr (fP c Q) (psi0 θ V n l s τ) x = eval (ptX U) Q * gs c U * Ψx := by
    have h0 := hφ 0
    simp only [map_zero, add_zero, Complex.ofReal_zero, zero_smul] at h0
    exact h0
  have hdet : IsUnit fr.det := hfr.1
  have hdetH : IsUnit frᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star
  have hGs : gramAt D V τ * s τ = (fr⁻¹)ᴴ * fr⁻¹ := by
    have h := hfr.2.2
    calc gramAt D V τ * s τ = (frᴴ)⁻¹ * (frᴴ * (gramAt D V τ * s τ) * fr) * fr⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
            ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul]
      _ = (fr⁻¹)ᴴ * fr⁻¹ := by
          rw [h, Matrix.mul_one, Matrix.conjTranspose_nonsing_inv]
  have e1' : ∑ a, ∑ i, 2 * (star (U a i) * W a i).re = 2 * (Uᴴ * W).trace.re := by
    show _ = 2 * (∑ i, (Uᴴ * W) i i).re
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_comm
  have e2' : Uᴴ * W = zᴴ * (gramAt D V τ * s τ) * X := by
    rw [hGs]
    simp only [hU, hW, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e3' : (zᴴ * (gramAt D V τ * s τ) * X).trace.re = (Xᴴ * (gramAt D V τ * s τ) * z).trace.re := by
    have h : Xᴴ * (gramAt D V τ * s τ) * z = (zᴴ * (gramAt D V τ * s τ) * X)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        (hM τ).eq, Matrix.mul_assoc]
    rw [h, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
  have hc' : c = 2 * Real.pi * |l τ| := rfl
  have hlin : GlobalTheory.StdUnn.linF V l s τ X z = ((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ) := by
    show ((4 * Real.pi * |l τ| * (Xᴴ * (gramAt D V τ * s τ) * z).trace.re : ℝ) : ℂ) = _
    congr 1
    rw [e1', e2', e3', hc']
    ring
  show deriv (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t)) 0 +
      GlobalTheory.StdUnn.linF V l s τ X z * tens θ τ fr (fP c Q) (psi0 θ V n l s τ) x = _
  rw [hderiv.deriv, hφx, hlin]
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem const_of_annS {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (h : ∀ X, annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) = 0) :
    Q = C (evX Q 0) := by
  have hk : ∀ u W : Matrix (Fin V.rank) (Fin n) ℂ, ∑ k, ptX W k * eval (ptX u) (pderiv k Q) = 0 := by
    intro u W
    have e := congrFun (h (fr * W)) (xL θ τ (fr * u))
    rw [annS_tens hθ hfr hM l] at e
    have hinv : ∀ v : Matrix (Fin V.rank) (Fin n) ℂ, fr⁻¹ * (fr * v) = v := fun v => by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
    have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
      have := congrFun (compAt_xL hθ τ (fr * u)) τ
      simpa [dirAt_self] using this
    have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
      unfold psi0
      rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
      simp only [one_mul]
      exact gaussian_at_zero_eq_one D V.rank n
    rw [hc, hinv, hinv, hp, mul_one] at e
    exact (mul_eq_zero.1 e).resolve_right (gs_ne_zero _ _)
  have hconst : ∀ u : Matrix (Fin V.rank) (Fin n) ℂ, evX Q u = evX Q 0 := by
    intro u
    let F : ℝ → ℂ := fun t => eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u) Q
    have hF : ∀ t, HasDerivAt F 0 t := by
      intro t
      have hd := GlobalTheory.FockAnnKill.hasDerivAt_eval_line Q (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ)) (ptX u) t
      refine hd.congr_deriv ?_
      have e2 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u = ptX ((0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • u) :=
        (ptX_add_smul _ _ t).symm
      rw [e2]
      exact hk _ u
    have hdiff : Differentiable ℝ F := fun t => (hF t).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff (fun t => (hF t).deriv) 1 0
    have e1 : F 1 = evX Q u := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((1 : ℝ) : ℂ) • ptX u) Q = eval (ptX u) Q
      rw [Complex.ofReal_one, one_smul]
      have e3 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ptX u = ptX u := by
        funext k
        obtain ⟨a, i, b⟩ := k
        cases b <;> simp [ptX]
      rw [e3]
    have e0 : F 0 = evX Q 0 := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((0 : ℝ) : ℂ) • ptX u) Q = eval (ptX 0) Q
      rw [Complex.ofReal_zero, zero_smul, add_zero]
    rw [← e1, ← e0, hc]
  apply sub_eq_zero.1
  apply evX_eq_zero
  intro u
  show eval _ (Q - C (evX Q 0)) = 0
  rw [map_sub, eval_C]
  exact sub_eq_zero.2 (hconst u)

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacC
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.RhoH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

theorem annS_stable : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ (τ : D.what₂.Tau) (Φ : schwartzA θ V.rank n), (∀ X, annS V l s θ τ X Φ.1 = 0) →
    ∀ k ∈ K D n, ∀ X, annS V l s θ τ X (ω k Φ).1 = 0 := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs τ Φ hann k hk X
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨hschS, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ

  have hkill1 : ∀ Z : Matrix (Fin V.rank) (Fin A.rank) ℂ,
      annih (heisO ψ₀ (dblSp A) V) θ τ (cplxO (s' τ) (s τ)) (Z * (dblDec A).qX.map (tauE D τ)) f = 0 := by
    intro Z
    apply GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero D ψ₀ hstd A V μ 𝓕 hμ _ (GlobalTheory.StdUnn.isThetaFunO_annih_of_std (A := A) (B := V) (ν := μ) (𝓨 := 𝓕) hstd hθ hμ τ _ _ hf)
    rw [GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf τ Z, hfΦ]
    exact hann Z
  have hkill : ∀ Y : Matrix (Fin V.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ₀ (dblSp A) V) θ τ (cplxO (s' τ) (s τ)) Y f = 0 := by
    intro Y
    obtain ⟨Z, Z', c, hdec⟩ := GlobalTheory.T.annihilationOperator_doubledHermitianSpace_decomp D ψ₀ hstd θ hθ A V μ' hsk s' s hstd' hs τ Y
    rw [hdec f hf, hkill1, hkill1, smul_zero, add_zero]

  have hkk : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hS : ∀ τ', s' τ' * compAt θ τ' (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) =
      compAt θ τ' (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) * s' τ' := fun τ' => (hcomm (κ.symm k) hkk τ').symm
  have hm1 : ∀ τ', compAt θ τ' (Formalism.L2.Theta.mt V 1) = 1 := by
    intro τ'
    simp [Formalism.L2.Theta.mt, compAt, Matrix.map_one]
  have hT : ∀ τ', s τ' * compAt θ τ' (Formalism.L2.Theta.mt V 1) = compAt θ τ' (Formalism.L2.Theta.mt V 1) * s τ' := by
    intro τ'
    rw [hm1, Matrix.mul_one, Matrix.one_mul]
  let X' : Matrix (Fin V.rank) (Fin A.rank) ℂ := X
  set Y0 : Matrix (Fin V.rank) (Fin (dblSp A).rank) ℂ :=
    (X' * (dblDec A).qX.map (tauE D τ)) * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) with hY0
  have hmove := (GlobalTheory.FockMove.om_foldr hdat hθ (κ.symm k) 1 hS hT hf [(τ, Y0)]).2
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil] at hmove
  rw [hkill Y0, map_zero, hm1, Matrix.one_mul, hY0, Matrix.mul_assoc,
    GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.mul_one] at hmove

  have htk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htk
  have hth' : IsThetaFunO ψ₀ (dblSp A) V (omh (κ.symm k, 1) f) := hdat.om_pres _ f hf
  have e := GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hth' τ X'
  rw [← hmove] at e
  have hs0 : sch ψ₀ A V μ 𝓕 (0 : WO (dblSp A) V → ℂ) = 0 := by
    have := (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ f f hf hf 0).2.2.2
    rw [zero_smul, zero_smul] at this
    exact this
  rw [hs0] at e
  show annS V l s θ τ X ((ω k) Φ).1 = 0
  rw [show ((ω k) Φ).1 = sch ψ₀ A V μ 𝓕 (omh (κ.symm k, 1) f) from htk]
  exact e.symm

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 8000000

open RhoH in
theorem lIkvac : LIkvac := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL e hvac k hk
  classical
  obtain ⟨𝓕, hμ⟩ := hC.hμ
  have hΨ0m : psi0 θ V n l s τ ∈ awayA θ V n l s τ := unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V l s τ
  have hl0 : ∀ τ, l τ ≠ 0 := l_ne_zero D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl
  have hmem : ∀ P : PX V.rank n, tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ fockA θ V n l s :=
    fun P => hT D n V θ l s τ ε fr hC.hθ hl0 hC.hs hC.hfr _ hΨ0m P
  have hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian := fun τ => (hC.hs τ).2.2.1

  have hann1 : ∀ X, annS V l s θ τ X (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 1).1 = 0 := by
    intro X
    rw [phiS_val (hmem 1).1]
    funext x
    rw [annS_tens hC.hθ hC.hfr hM l]
    simp
  have hann2 := annS_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs τ _ hann1 (ι k)
    (iota_mem_K hC.hθ hC.hι k hk)
  rw [hL k _ hΨ0m 1] at hann2

  have hΦ : (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 1).1 ∈ fockA θ V n l s := by
    rw [phiS_val (hmem 1).1]
    exact (hmem 1).2
  have hst := fock_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs _ hΦ (ι k)
    (iota_mem_K hC.hθ hC.hι k hk)
  rw [hL k _ hΨ0m 1] at hst
  obtain ⟨Q, hQ⟩ := tens_slice hC.hθ hC.hfr l _ hst
  rw [hQ] at hann2
  have hQc := const_of_annS hC.hθ hC.hfr hM l Q hann2
  set a := evX Q 0 with ha
  have hL1 : L k (fP (cLoc l τ) 1) = a • fP (cLoc l τ) 1 := by
    rw [hQ, hQc]
    funext u
    simp [fP, evX]

  have hv := hvac k
  unfold sLd at hv
  rw [hL1] at hv
  have hg0 : gs (cLoc l τ) (0 : Fin V.rank → Fin n → ℂ) = 1 := by
    simp [gs]
  have hf0 : fP (cLoc l τ) (1 : PX V.rank n) 0 = 1 := by
    simp [fP, evX, hg0]
  simp only [Pi.smul_apply, smul_eq_mul, hf0, mul_one] at hv
  rw [hL1, hv]

end PositivityTheory.Rg.Sw.Glob
