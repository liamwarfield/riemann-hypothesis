module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventually

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZero
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.DilFam

variable {m n : ℕ}

def pt (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1) * Complex.exp (z * X k.2.1)

def Fam (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (P : PositivityTheory.Rg.Sw.PX m n) (z : ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * MvPolynomial.eval (pt X v z) P *
    Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))

theorem hasDerivAt_pt (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun w => pt X v w k) ((X k.2.1 : ℂ) * pt X v z k) z := by
  have h : HasDerivAt (fun w : ℂ => w * (X k.2.1 : ℂ)) (X k.2.1 : ℂ) z := by
    simpa using (hasDerivAt_id z).mul_const (X k.2.1 : ℂ)
  refine ((h.cexp).const_mul (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1)).congr_deriv ?_
  rw [show GlobalTheory.CompanionTheory.DilFam.pt X v z k =
      (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1) * Complex.exp (z * X k.2.1) from rfl]
  ring

theorem hasDerivAt_eval {σ : Type*} [Fintype σ] (x : ℂ → σ → ℂ) (x' : σ → ℂ) (z : ℂ)
    (hx : ∀ k, HasDerivAt (fun w => x w k) (x' k) z) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun w => MvPolynomial.eval (x w) P)
      (∑ k, x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k P)) z := by
  classical
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const z a
  next p q hp hq =>
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  next p i hp =>
    have hX : ∀ k, MvPolynomial.eval (x z) (MvPolynomial.pderiv k (MvPolynomial.X i : MvPolynomial σ ℂ)) =
        if k = i then 1 else 0 := by
      intro k
      by_cases h : k = i
      · subst h
        simp [MvPolynomial.pderiv_X_self]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h), map_zero, if_neg h]
    have hf : (fun w => MvPolynomial.eval (x w) (p * MvPolynomial.X i)) =
        fun w => MvPolynomial.eval (x w) p * x w i := by
      funext w
      simp only [map_mul, MvPolynomial.eval_X]
    rw [hf]
    refine (hp.mul (hx i)).congr_deriv ?_
    symm
    have hs : ∀ k, x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k (p * MvPolynomial.X i)) =
        x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k p) * x z i +
          (if k = i then x' k else 0) * MvPolynomial.eval (x z) p := by
      intro k
      rw [MvPolynomial.pderiv_mul, map_add (f := _), map_mul, map_mul, MvPolynomial.eval_X, hX k]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun k _ => hs k), Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

theorem pt_mul (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (a : Fin m) (j : Fin n) :
    pt X v z (a, j, false) * pt X v z (a, j, true) =
      Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ) := by
  show v a j * Complex.exp (z * ((X j : ℝ) : ℂ)) * (star (v a j) * Complex.exp (z * ((X j : ℝ) : ℂ))) = _
  rw [show (2 * z * ((X j : ℝ) : ℂ)) = z * X j + z * X j by ring, Complex.exp_add]
  rw [show ((‖v a j‖ ^ 2 : ℝ) : ℂ) = v a j * star (v a j) by
    rw [Complex.star_def, Complex.mul_conj']; norm_cast]
  ring

theorem sum_pt (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (f : Fin m × Fin n × Bool → ℂ) :
    ∑ k, (X k.2.1 : ℂ) * pt X v z k * f k =
      ∑ j, (X j : ℂ) * ∑ a, (pt X v z (a, j, false) * f (a, j, false) +
        pt X v z (a, j, true) * f (a, j, true)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem eval_dil (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (P : PositivityTheory.Rg.Sw.PX m n) :
    MvPolynomial.eval (pt X v z) (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) =
      (m : ℂ) * (∑ j, (X j : ℂ)) * MvPolynomial.eval (pt X v z) P +
      (∑ k, (X k.2.1 : ℂ) * pt X v z k * MvPolynomial.eval (pt X v z) (MvPolynomial.pderiv k P)) +
      (-(4 * Real.pi : ℂ)) * (∑ a, ∑ j, (X j : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))) *
        MvPolynomial.eval (pt X v z) P := by
  have hA : MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) =
      ∑ j, (X j : ℂ) * ((m : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P +
        ∑ a, (GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, false) *
            MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv (a, j, false) P) +
          GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, true) *
            MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv (a, j, true) P) -
          2 * ((2 * Real.pi : ℝ) : ℂ) * (GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, false) *
            GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, true) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [PositivityTheory.Rg.Sw.dil, Finset.sum_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, LinearMap.id_apply, Derivation.coeFn_coe, map_sum, map_add, map_sub,
      MvPolynomial.smul_eval, map_mul, MvPolynomial.eval_X]
  rw [hA, GlobalTheory.CompanionTheory.DilFam.sum_pt X v z
    (fun k => MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv k P))]
  simp only [GlobalTheory.CompanionTheory.DilFam.pt_mul]
  have h1 : (m : ℂ) * (∑ j, (X j : ℂ)) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P =
      ∑ j, (X j : ℂ) * ((m : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : (-(4 * Real.pi : ℂ)) * (∑ a, ∑ j, (X j : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))) *
        MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P =
      ∑ j, (X j : ℂ) * -(∑ a, 2 * ((2 * Real.pi : ℝ) : ℂ) *
        (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P)) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    push_cast
    ring
  rw [h1, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_sub_distrib]
  ring

theorem hasDerivAt_gauss (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * w * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))
      (Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) *
        ((-(4 * Real.pi : ℂ)) * ∑ a, ∑ j, (X j : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) z := by
  have hin : HasDerivAt
      (fun w : ℂ => -(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * w * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))
      (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * (2 * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) z := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.mul_const
    have h : HasDerivAt (fun w : ℂ => 2 * w * (X j : ℂ)) (2 * X j) z := by
      simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).mul_const (X j : ℂ)
    exact h.cexp
  convert hin.cexp using 1
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hasDerivAt_Fam (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (P : PositivityTheory.Rg.Sw.PX m n) (z : ℂ) :
    HasDerivAt (Fam X v P) (Fam X v (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) z) z := by
  have he : HasDerivAt (fun w : ℂ => Complex.exp ((m : ℂ) * w * ∑ j, (X j : ℂ)))
      (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * ((m : ℂ) * ∑ j, (X j : ℂ))) z := by
    have h : HasDerivAt (fun w : ℂ => (m : ℂ) * w * ∑ j, (X j : ℂ)) ((m : ℂ) * ∑ j, (X j : ℂ)) z := by
      simpa using ((hasDerivAt_id z).const_mul (m : ℂ)).mul_const (∑ j, (X j : ℂ))
    exact h.cexp
  have hp := GlobalTheory.CompanionTheory.DilFam.hasDerivAt_eval (GlobalTheory.CompanionTheory.DilFam.pt X v)
    (fun k => (X k.2.1 : ℂ) * GlobalTheory.CompanionTheory.DilFam.pt X v z k) z (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_pt X v z) P
  have hg := GlobalTheory.CompanionTheory.DilFam.hasDerivAt_gauss X v z
  have h := (he.mul hp).mul hg
  refine h.congr_deriv ?_
  rw [show GlobalTheory.CompanionTheory.DilFam.Fam X v (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) z =
      Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
        MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) *
        Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) from rfl,
    GlobalTheory.CompanionTheory.DilFam.eval_dil]
  simp only [Pi.mul_apply]
  ring

theorem Fam_one (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) :
    Fam X v 1 = fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
      Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))) := by
  funext z
  simp only [GlobalTheory.CompanionTheory.DilFam.Fam, map_one, mul_one]

theorem Fam_zero (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (P : PositivityTheory.Rg.Sw.PX m n) :
    Fam X v P 0 = PositivityTheory.Rg.Sw.evX P v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  have hD : GlobalTheory.CompanionTheory.DilFam.pt X v 0 = fun k => if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1 := by
    funext k
    simp only [GlobalTheory.CompanionTheory.DilFam.pt, zero_mul, Complex.exp_zero, mul_one]
  simp only [GlobalTheory.CompanionTheory.DilFam.Fam, PositivityTheory.Rg.Sw.evX, PositivityTheory.Rg.Sw.gs, hD, mul_zero,
    zero_mul, Complex.exp_zero, one_mul]
  congr 1
  congr 1
  push_cast
  ring

theorem iteratedDeriv_Fam (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (r : ℕ) (P : PositivityTheory.Rg.Sw.PX m n) :
    iteratedDeriv r (Fam X v P) = Fam X v ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) P) := by
  induction r generalizing P with
  | zero => rw [iteratedDeriv_zero, pow_zero, Module.End.one_apply]
  | succ r ih =>
    have hd : deriv (GlobalTheory.CompanionTheory.DilFam.Fam X v P) =
        GlobalTheory.CompanionTheory.DilFam.Fam X v (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) := by
      funext z
      exact (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_Fam X v P z).deriv
    rw [iteratedDeriv_succ', hd, ih, pow_succ, Module.End.mul_apply]

theorem main : ∀ (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ), Differentiable ℂ (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = PositivityTheory.Rg.Sw.evX ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) 1) v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  intro m n X v
  rw [← GlobalTheory.CompanionTheory.DilFam.Fam_one X v]
  refine ⟨fun z => (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_Fam X v 1 z).differentiableAt, fun r => ?_⟩
  rw [GlobalTheory.CompanionTheory.DilFam.iteratedDeriv_Fam, GlobalTheory.CompanionTheory.DilFam.Fam_zero]

end GlobalTheory.CompanionTheory.DilFam
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_gaussian_exponential_at_zero : ∀ (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ), Differentiable ℂ (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = PositivityTheory.Rg.Sw.evX ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) 1) v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  first | exact @GlobalTheory.CompanionTheory.DilFam.main | exact GlobalTheory.CompanionTheory.DilFam.main | (intros; apply GlobalTheory.CompanionTheory.DilFam.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleConsecutiveVeryAmple
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleConsecutiveVeryAmple
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre GlobalTheory.ProjSpace

namespace GlobalTheory.CompanionTheory.ConsecAmple

variable {R : Type} [CommRing R] {X Y Z P : Scheme.{0}}

theorem veryAmpleBy_box {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Spec (CommRingCat.of R)}
    {g : Y ⟶ Spec (CommRingCat.of R)} (sq : IsPullback p q f g) {H : LB X} {K : LB Y} {m n : ℕ}
    {s : Fin (m + 1) → LB.Sec H} {t : Fin (n + 1) → LB.Sec K} (hf : VeryAmpleBy f H s) (hg : VeryAmpleBy g K t)
    (e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1)) :
    VeryAmpleBy (p ≫ f) (box p q H K) fun a => boxSec p q (s (e a).1) (t (e a).2) := by
  obtain ⟨hs, hs'⟩ := hf
  obtain ⟨ht, ht'⟩ := hg
  refine ⟨?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show q y ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (i, j), ?_⟩
    rw [nonzeroLocus_boxSec, e.apply_symm_apply]
    exact ⟨hi, hj⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' (e a).1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := ht' (e a).2
  have loc := nonzeroLocus_boxSec p q (s (e a).1) (t (e a).2)
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  have o₁ : r₁ (e a).1 = 1 := ratio_self _ _ (hr₁ _)
  have o₂ : r₂ (e a).2 = 1 := ratio_self _ _ (hr₂ _)
  refine ⟨?_, fun b => ap p l₁ (r₁ (e b).1) * ap q l₂ (r₂ (e b).2), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg₂ (· * ·) (ap_ratio p (hr₁ (e b).1 k.1) _ _) (ap_ratio q (hr₂ (e b).2 k.2) _ _)).trans
      (mul_mul_mul_comm _ _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm (i, (e a).2)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₂, map_one, _root_.mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      change ap q l₂ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e a).1, i)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₁, map_one, _root_.one_mul]

theorem veryAmpleBy_secPull {f : Y ⟶ Spec (CommRingCat.of R)} {L : LB Y} {M : ℕ} {s : Fin (M + 1) → LB.Sec L}
    (h : VeryAmpleBy f L s) (j : Z ⟶ Y) [IsClosedImmersion j] :
    VeryAmpleBy (j ≫ f) (L.pull j) fun i => GlobalTheory.Cartier.secPull (s i) j := by
  obtain ⟨hs, hc⟩ := (veryAmpleBy_iff f s).1 h
  refine (veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_secPull hs j, ?_⟩
  rw [toProj_secPull hs j]
  infer_instance

theorem gm_ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (r : Z ⟶ P) (z : Z) (hz : r z ∈ W)
    (u : Γ(X, U)ˣ) : gm r z W (Units.map (ap p h).toMonoidHom u) = gm (r ≫ p) z U u := by
  have e : Units.map (ap p h).toMonoidHom u = res h (pullU p U u) := Units.ext rfl
  rw [e]
  exact (gm_res r z h hz _).trans (gm_pull r p z U (h hz) u)

theorem gm_box (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (K : LB Y) (r : Z ⟶ P) (z : Z) (a b : H.ι × K.ι)
    (h : r z ∈ (box p q H K).U a ⊓ (box p q H K).U b) :
    gm r z ((box p q H K).U a ⊓ (box p q H K).U b) ((box p q H K).g a b) =
      gm (r ≫ p) z (H.U a.1 ⊓ H.U b.1) (H.g a.1 b.1) * gm (r ≫ q) z (K.U a.2 ⊓ K.U b.2) (K.g a.2 b.2) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_ap p _ r z h _) (gm_ap q _ r z h _))

theorem mem_box_of_graph (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (B : LB Y) (ψ : X ⟶ Y) (j : X ⟶ P) (hp : j ≫ p = 𝟙 X)
    (hq : j ≫ q = ψ) (c : (B.pull ψ).ι × H.ι) (y : X) (hy : y ∈ (tw (B.pull ψ) H 1).U c) :
    j y ∈ (box p q H B).U (c.2, c.1 PUnit.unit) := by
  have h₁ : p (j y) = y := by rw [← Scheme.Hom.comp_apply, hp]; rfl
  have h₂ : q (j y) = ψ y := by rw [← Scheme.Hom.comp_apply, hq]
  have h₃ : ψ y ∈ B.U (c.1 PUnit.unit) := mem_pull.1 hy.1
  have h₄ : y ∈ H.U c.2 := hy.2
  exact ⟨show p (j y) ∈ H.U c.2 by rw [h₁]; exact h₄, show q (j y) ∈ _ by rw [h₂]; exact h₃⟩

def chartPullBox (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (B : LB Y) (ψ : X ⟶ Y) (j : X ⟶ P) (hp : j ≫ p = 𝟙 X)
    (hq : j ≫ q = ψ) : ChartPull (tw (B.pull ψ) H 1) (box p q H B) j where
  idx c := (c.2, c.1 PUnit.unit)
  le c y hy := mem_box_of_graph p q H B ψ j hp hq c y hy
  g y c c' hc hc' := by
    refine (GlobalTheory.LBAlg.gm_tw (B.pull ψ) H 1 (𝟙 X) y c c' ⟨hc, hc'⟩).trans (Eq.trans ?_
      (gm_box p q H B j y _ _ ⟨mem_box_of_graph p q H B ψ j hp hq c y hc,
        mem_box_of_graph p q H B ψ j hp hq c' y hc'⟩).symm)
    rw [gm_pull_g B ψ (𝟙 X) y c.1 c'.1 hc.1 hc'.1, hp, hq, Category.id_comp, zpow_one, mul_comm]

theorem exists_veryAmpleBy_tw {f : X ⟶ Spec (CommRingCat.of R)} {K M : LB X} (hK : K.IsLB) (hM : M.IsLB) {m n : ℕ}
    {a : Fin (m + 1) → LB.Sec K} (ha : VeryAmpleBy f K a) {c : Fin (n + 1) → LB.Sec M}
    (hc : ⨆ i, nonzeroLocus (c i) = ⊤) :
    ∃ (m' : ℕ) (s : Fin (m' + 1) → LB.Sec (tw M K 1)), VeryAmpleBy f (tw M K 1) s := by
  have hψ : toProj f c hc ≫ PSpace.str R n = f := toProj_str f c hc
  have sq := IsPullback.of_hasPullback f (PSpace.str R n)
  let j : X ⟶ pullback f (PSpace.str R n) := pullback.lift (𝟙 X) (toProj f c hc) (by rw [hψ, Category.id_comp])
  have hp : j ≫ pullback.fst f (PSpace.str R n) = 𝟙 X := pullback.lift_fst _ _ _
  have hq : j ≫ pullback.snd f (PSpace.str R n) = toProj f c hc := pullback.lift_snd _ _ _
  have := isProper_str R n
  have : IsSeparated (pullback.fst f (PSpace.str R n)) := inferInstance
  have : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ pullback.fst f (PSpace.str R n)) := by rw [hp]; infer_instance
    exact IsClosedImmersion.of_comp j (pullback.fst f (PSpace.str R n))
  have hcoord : VeryAmpleBy (PSpace.str R n) (O1 R n) (coord R n) :=
    (veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_coord R n, by rw [toProj_coord]; infer_instance⟩
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) := (finCongr (by ring)).trans finProdFinEquiv.symm
  have h₁ := veryAmpleBy_secPull (veryAmpleBy_box sq ha hcoord e) j
  have e₁ : j ≫ pullback.fst f (PSpace.str R n) ≫ f = f := by rw [← Category.assoc, hp, Category.id_comp]
  rw [e₁] at h₁
  have hB := isLB_box (pullback.fst f (PSpace.str R n)) (pullback.snd f (PSpace.str R n)) hK (O1_isLB R n)
  have hO := LB.isLB_pull (O1_isLB R n) (toProj f c hc)
  have i₁ : LBIso ((box (pullback.fst f (PSpace.str R n)) (pullback.snd f (PSpace.str R n)) K (O1 R n)).pull j)
      (tw ((O1 R n).pull (toProj f c hc)) K 1) :=
    LBIso.chartPull (chartPullPull _ j) (chartPullBox _ _ K (O1 R n) _ j hp hq) (GlobalTheory.LBAlg.lbIso_self hB)
  have i₂ := GlobalTheory.LBAlg.lbIso_tw_congr (t := 1) hK (lbIso_pullback_O1_toProj f c hc)
  obtain ⟨t, ht⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (LB.isLB_pull hB j) (isLB_tw hM hK 1)
    (LBIso.trans (LB.isLB_pull hB j) (isLB_tw hO hK 1) (isLB_tw hM hK 1) i₁ i₂) h₁
  exact ⟨_, t, ht⟩

theorem gm_pw (H : LB X) (n : ℤ) (r : Z ⟶ X) (z : Z) (i j : H.ι) :
    gm r z ((pw H n).U i ⊓ (pw H n).U j) ((pw H n).g i j) = gm r z (H.U i ⊓ H.U j) (H.g i j) ^ n :=
  map_zpow _ _ _

theorem pw_pw (L : LB X) (a b : ℤ) : pw (pw L a) b = pw L (a * b) := by
  change (⟨L.ι, L.U, fun i j => (L.g i j ^ a) ^ b⟩ : LB X) = ⟨L.ι, L.U, fun i j => L.g i j ^ (a * b)⟩
  simp only [zpow_mul]

theorem lbIso_tw_tw_pw {L : LB X} (hL : L.IsLB) (N t : ℤ) :
    LBIso (tw (tw L (pw L N) t) (pw (pw L N) t) 1) (pw L (1 + 2 * N * t)) := by
  have l₁ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1.1 :=
    fun p x hx => ⟨hx.1, hx.2.1.1⟩
  have l₂ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1.2 :=
    fun p x hx => ⟨hx.1, hx.2.1.2⟩
  have l₃ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.2 :=
    fun p x hx => ⟨hx.1, hx.2.2⟩
  have v : ∀ (x : X) (p : L.ι × ((L.ι × L.ι) × L.ι)), x ∈ L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) →
      gm (𝟙 X) x _ (res (l₁ p) (L.g p.1 p.2.1.1) * res (l₂ p) (L.g p.1 p.2.1.2) ^ (N * t) *
          res (l₃ p) (L.g p.1 p.2.2) ^ (N * t)) =
        gm (𝟙 X) x _ (L.g p.1 p.2.1.1) * gm (𝟙 X) x _ (L.g p.1 p.2.1.2) ^ (N * t) *
          gm (𝟙 X) x _ (L.g p.1 p.2.2) ^ (N * t) :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res _ x _ hx _) ((map_zpow _ _ _).trans (congrArg (· ^ (N * t)) (gm_res _ x _ hx _)))))
      ((map_zpow _ _ _).trans (congrArg (· ^ (N * t)) (gm_res _ x _ hx _))))
  have key : ∀ (x : X) {a b i j : L.ι}, x ∈ L.U a → x ∈ L.U b → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (L.g a i) = gm (𝟙 X) x _ (L.g a b) * gm (𝟙 X) x _ (L.g b j) * (gm (𝟙 X) x _ (L.g i j))⁻¹ := by
    intro x a b i j ha hb hi hj
    rw [gm_cocycle hL (𝟙 X) x ha hb hj, ← gm_cocycle hL (𝟙 X) x ha hi hj, mul_inv_cancel_right]
  refine GlobalTheory.LBAlg.lbIso_of_germs (fun p => res (l₁ p) (L.g p.1 p.2.1.1) * res (l₂ p) (L.g p.1 p.2.1.2) ^ (N * t) *
    res (l₃ p) (L.g p.1 p.2.2) ^ (N * t)) fun x p q h₁ h₂ h₃ h₄ => ?_
  have eA : gm (𝟙 X) x _ ((tw (tw L (pw L N) t) (pw (pw L N) t) 1).g p.2 q.2) =
      gm (𝟙 X) x (L.U p.2.1.1 ⊓ L.U q.2.1.1) (L.g p.2.1.1 q.2.1.1) *
        gm (𝟙 X) x (L.U p.2.1.2 ⊓ L.U q.2.1.2) (L.g p.2.1.2 q.2.1.2) ^ (N * t) *
        gm (𝟙 X) x (L.U p.2.2 ⊓ L.U q.2.2) (L.g p.2.2 q.2.2) ^ (N * t) := by
    refine (GlobalTheory.LBAlg.gm_tw (tw L (pw L N) t) (pw (pw L N) t) 1 (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩).trans ?_
    rw [GlobalTheory.LBAlg.gm_tw L (pw L N) t (𝟙 X) x p.2.1 q.2.1 ⟨h₂.1, h₄.1⟩]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl ?_) ?_
    · exact (congrArg (· ^ t) (gm_pw L N (𝟙 X) x p.2.1.2 q.2.1.2)).trans (zpow_mul _ _ _).symm
    · exact ((zpow_one _).trans (gm_pw (pw L N) t (𝟙 X) x p.2.2 q.2.2)).trans
        ((congrArg (· ^ t) (gm_pw L N (𝟙 X) x p.2.2 q.2.2)).trans (zpow_mul _ _ _).symm)
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pw L _ (𝟙 X) x p.1 q.1).symm
    (congrArg (·⁻¹) eA.symm)) (v x q ⟨h₃, h₄⟩).symm))
  have k₁ := key x (a := p.1) (b := q.1) (i := p.2.1.1) (j := q.2.1.1) h₁ h₃ h₂.1.1 h₄.1.1
  have k₂ := key x (a := p.1) (b := q.1) (i := p.2.1.2) (j := q.2.1.2) h₁ h₃ h₂.1.2 h₄.1.2
  have k₃ := key x (a := p.1) (b := q.1) (i := p.2.2) (j := q.2.2) h₁ h₃ h₂.2 h₄.2
  rw [k₁, k₂, k₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem exists_consecutive_veryAmple : ∀ (A : Type) [CommRing A] [IsNoetherianRing A]
    (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∃ (m : ℕ)
    (s : Fin (m + 1) → LB.Sec (pw L (d : ℤ))) (m' : ℕ) (s' : Fin (m' + 1) → LB.Sec (pw L ((d + 1 : ℕ) : ℤ))),
    VeryAmpleBy X.hom (pw L (d : ℤ)) s ∧ VeryAmpleBy X.hom (pw L ((d + 1 : ℕ) : ℤ)) s' := by
  intro A _ _ X L hL hA
  obtain ⟨N, hN, m, s, hH, hs⟩ := veryAmpleBy_of_relAmple hL hA (𝟙 X.left) (Category.id_comp _) hL
    (LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _)) (GlobalTheory.LBAlg.lbIso_self hL))
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.TwistGen.twist_generated A X.left X.hom (pw L N) m s hH hs L hL
  obtain ⟨T, hT, hTt⟩ : ∃ T : ℕ, 1 ≤ T ∧ t₀ ≤ (T : ℤ) := ⟨(max t₀ 1).toNat, by omega, by omega⟩
  obtain ⟨n', u, hu⟩ := ht₀ T hTt
  obtain ⟨k, a, ha⟩ := veryAmpleBy_pw A X.left X.hom (pw L N) m s hH hs T hT
  have hK := isLB_pw hH T
  have hM := isLB_tw hL hH T
  obtain ⟨m', s', hs'⟩ := exists_veryAmpleBy_tw hK hM ha hu
  obtain ⟨t', ht'⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (isLB_tw hM hK 1) (isLB_pw hL _)
    (lbIso_tw_tw_pw hL N T) hs'
  have A₁ : ∃ (k : ℕ) (a : Fin (k + 1) → LB.Sec (pw L ((2 * N * T : ℕ) : ℤ))),
      VeryAmpleBy X.hom (pw L ((2 * N * T : ℕ) : ℤ)) a := by
    have e₁ : pw L ((2 * N * T : ℕ) : ℤ) = pw (pw L N) ((2 * T : ℕ) : ℤ) := by
      rw [pw_pw]
      congr 1
      push_cast
      ring
    rw [e₁]
    exact veryAmpleBy_pw A X.left X.hom (pw L N) m s hH hs (2 * T) (by omega)
  have A₂ : ∃ (k : ℕ) (a : Fin (k + 1) → LB.Sec (pw L ((2 * N * T + 1 : ℕ) : ℤ))),
      VeryAmpleBy X.hom (pw L ((2 * N * T + 1 : ℕ) : ℤ)) a := by
    have e₂ : ((2 * N * T + 1 : ℕ) : ℤ) = 1 + 2 * (N : ℤ) * (T : ℤ) := by
      push_cast
      ring
    rw [e₂]
    exact ⟨m', t', ht'⟩
  obtain ⟨k₁, a₁, h₁⟩ := A₁
  obtain ⟨k₂, a₂, h₂⟩ := A₂
  exact ⟨2 * N * T, Nat.mul_pos (Nat.mul_pos two_pos hN) hT, k₁, a₁, k₂, a₂, h₁, h₂⟩

end GlobalTheory.CompanionTheory.ConsecAmple
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleConsecutiveVeryAmpleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatively_ample_consecutive_very_ample : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw L (d : ℤ))) (m' : ℕ) (s' : Fin (m' + 1) → LB.Sec (pw L ((d + 1 : ℕ) : ℤ))), VeryAmpleBy X.hom (pw L (d : ℤ)) s ∧ VeryAmpleBy X.hom (pw L ((d + 1 : ℕ) : ℤ)) s' := by
  first | exact @GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple | exact GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple | (intros; apply GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformGenerationOfVanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedVanishingSectionsSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedVanishingSectionsSpan
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE

theorem span_range_twist_eq_top : ∀ {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X), L.IsLB →
    ∀ {k : ℕ} {P : Fin k → X.Modules} {Q K : X.Modules} (f : ∀ i, P i ⟶ Q) (ι : K ⟶ ⨁ P)
      (w : ι ≫ biproduct.desc f = 0), (ShortComplex.mk ι (biproduct.desc f) w).ShortExact →
      Subsingleton (GlobalTheory.coh (GlobalTheory.twist K L) 1) →
      Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map L (f i)).app ⊤)) = ⊤ := by
  intro X L hL k P Q K f ι w hS hK
  have hsurj := GlobalTheory.cohOn.app_surjective (GlobalTheory.Twist.shortExact_map hL hS) ⊤ hK
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  have hg : (ShortComplex.map (ShortComplex.mk ι (biproduct.desc f) w) (GlobalTheory.twistFunctor L)).g =
      ∑ i, GlobalTheory.Twist.map L (biproduct.π P i) ≫ GlobalTheory.Twist.map L (f i) := by
    show (GlobalTheory.twistFunctor L).map (biproduct.desc f) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [biproduct.desc_eq, Functor.map_sum]
    rfl
  let e : (GlobalTheory.twist (⨁ P) L ⟶ GlobalTheory.twist Q L) →+ Γ(GlobalTheory.twist Q L, ⊤) :=
    { toFun := fun φ => (φ.app ⊤) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have key : ((ShortComplex.map (ShortComplex.mk ι (biproduct.desc f) w) (GlobalTheory.twistFunctor L)).g.app ⊤) x =
      ∑ i, ((GlobalTheory.Twist.map L (f i)).app ⊤) (((GlobalTheory.Twist.map L (biproduct.π P i)).app ⊤) x) := by
    rw [hg]
    exact map_sum e _ _
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span (Set.mem_iUnion.2 ⟨i, ?_⟩)
  exact ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.GE
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedVanishingSectionsSpanStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_vanishing_sections_span : ∀ {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X), L.IsLB → ∀ {k : ℕ} {P : Fin k → X.Modules} {Q K : X.Modules} (f : ∀ i, P i ⟶ Q) (ι : K ⟶ ⨁ P) (w : ι ≫ biproduct.desc f = 0), (ShortComplex.mk ι (biproduct.desc f) w).ShortExact → Subsingleton (GlobalTheory.coh (GlobalTheory.twist K L) 1) → Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map L (f i)).app ⊤)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top | exact GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top | (intros; apply GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpi
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpi
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.KerSeq

theorem epi_sumMap_of_opSeq {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (e : ℕ) :
    Epi (KerSeq.sumMap T d e) := by
  haveI : ∀ n, (M n).IsQuasicoherent := fun n => (h.coherent n).1
  haveI : (KerSeq.sumN M k d e).IsQuasicoherent := by
    unfold KerSeq.sumN
    exact GlobalTheory.QCoh.isQuasicoherent_biproduct _
  rw [GlobalTheory.QCoh.epi_iff_forall_affine]
  intro U hU
  have hg := h.gen (d + e) (Nat.le_add_right d e) ⟨U, hU⟩
  have hr : (GlobalTheory.QCoh.appLinear (KerSeq.sumMap T d e) U).range = ⊤ := by
    rw [eq_top_iff, ← hg, Submodule.span_le]
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨i, x, rfl⟩ := hy
    refine ⟨(biproduct.ι (fun _ : Fin k => M (d + e)) i).app U x, ?_⟩
    rw [GlobalTheory.QCoh.appLinear_apply, GlobalTheory.QCoh.app_app]
    simp [KerSeq.sumMap]
  rw [← GlobalTheory.QCoh.coe_appLinear]
  exact LinearMap.range_eq_top.1 hr

end GlobalTheory.CompanionTheory.GE.KerSeq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpiStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operator_sequence_sum_epi : ∀ {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}, OpSeq k M T d → ∀ e, Epi (KerSeq.sumMap T d e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq | exact GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq | (intros; apply GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSequenceCoherent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSequenceCoherent
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

theorem isCoherent_biproduct {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → X.Modules) (hF : ∀ i, IsCoherent (F i)) : IsCoherent (⨁ F) := by
  haveI : ∀ i, SheafOfModules.IsQuasicoherent (F i) := fun i => (hF i).1
  refine ⟨isQuasicoherent_biproduct F, fun U hU => ?_⟩
  haveI : ∀ i, Module.Finite Γ(X, U) ((F i).presheaf.obj (Opposite.op U)) := fun i => (hF i).2 U hU
  let L : ∀ j, (F j).presheaf.obj (Opposite.op U) →ₗ[Γ(X, U)] (⨁ F).presheaf.obj (Opposite.op U) :=
    fun j =>
    { toFun := fun x => ConcreteCategory.hom (Scheme.Modules.Hom.app (biproduct.ι F j) U) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        exact Scheme.Modules.Hom.app_smul _ r x }
  let f : (∀ j, (F j).presheaf.obj (Opposite.op U)) →ₗ[Γ(X, U)] (⨁ F).presheaf.obj (Opposite.op U) :=
    ∑ j, (L j).comp (LinearMap.proj j)
  refine Module.Finite.of_surjective f ?_
  intro m
  refine ⟨fun j => ConcreteCategory.hom (Scheme.Modules.Hom.app (biproduct.π F j) U) m, ?_⟩
  rw [LinearMap.sum_apply]
  exact (biproduct_app_eq_sum F U m).symm

theorem isCoherent_kerSeq : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}, OpSeq k M T d →
    ∀ e, IsCoherent (KerSeq.kerSeq T d e) := by
  intro X _ k M T d h e
  haveI : SheafOfModules.IsQuasicoherent (M (d + e + 1)) := (h.coherent _).1
  exact isCoherent_kernel (KerSeq.sumMap T d e) (isCoherent_biproduct _ fun _ => h.coherent _)

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSequenceCoherentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_sequence_coherent : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}, OpSeq k M T d → ∀ e, IsCoherent (KerSeq.kerSeq T d e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.isCoherent_kerSeq | exact GlobalTheory.CompanionTheory.GE.isCoherent_kerSeq | (intros; apply GlobalTheory.CompanionTheory.GE.isCoherent_kerSeq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformSpanEventually
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformSpanEventually
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Uniform

theorem span_range_eq_top_iff_surjective {X : Scheme.{0}} {k : ℕ} {A B : X.Modules}
    (T : Fin k → (A ⟶ B)) (U : X.Opens) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U)) = ⊤ ↔
      Function.Surjective ((biproduct.desc T).app U) := by
  have hι : ∀ i (z : Γ(A, U)),
      (biproduct.desc T).app U ((biproduct.ι (fun _ : Fin k => A) i).app U z) = (T i).app U z := by
    intro i z
    rw [← GlobalTheory.QCoh.appLinear_apply, ← GlobalTheory.QCoh.appLinear_apply, ← LinearMap.comp_apply,
      ← GlobalTheory.QCoh.appLinear_comp, biproduct.ι_desc, GlobalTheory.QCoh.appLinear_apply]
  constructor
  · intro h y
    have hy : y ∈ Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U)) := h ▸ Submodule.mem_top
    have hle : Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U)) ≤
        LinearMap.range (GlobalTheory.QCoh.appLinear (biproduct.desc T) U) := by
      rw [Submodule.span_le]
      intro w hw
      obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.1 hw
      exact ⟨(biproduct.ι (fun _ : Fin k => A) i).app U z, by rw [GlobalTheory.QCoh.appLinear_apply, hι]⟩
    obtain ⟨x, hx⟩ := hle hy
    exact ⟨x, hx⟩
  · intro h
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := h y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [biproduct_app_eq_sum (fun _ : Fin k => A) U x, ← GlobalTheory.QCoh.appLinear_apply, map_sum]
    refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
      (Set.mem_iUnion.2 ⟨i, (biproduct.π (fun _ : Fin k => A) i).app U x, ?_⟩)
    rw [GlobalTheory.QCoh.appLinear_apply, hι]

theorem span_range_eq_top_uniform : ∀ {X : Scheme.{0}} [CompactSpace X] {k : ℕ}
    {K : ℕ → X.Modules} (T : Fin k → ∀ e, K e ⟶ K (e + 1)), (∀ e, (K e).IsQuasicoherent) →
    (∀ U : X.affineOpens, ∃ dU : ℕ, ∀ e, dU ≤ e →
      Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤) →
    ∃ d' : ℕ, ∀ e, d' ≤ e → ∀ U : X.affineOpens,
      Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤ := by
  intro X _ k K T hq hgen
  obtain ⟨ι, _, 𝒰, haff, hcov⟩ := GlobalTheory.QCoh.exists_finite_affine_cover_of_isCompact (X := X)
    (W := ⊤) (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  choose dU hdU using fun i => hgen ⟨𝒰 i, haff i⟩
  refine ⟨Finset.univ.sup dU, fun e he U => ?_⟩
  haveI := hq e
  haveI := hq (e + 1)
  have hepi : Epi (biproduct.desc fun i => T i e) := by
    rw [GlobalTheory.QCoh.epi_iff_affineCover 𝒰 hcov.symm haff]
    intro i
    exact (span_range_eq_top_iff_surjective (fun j => T j e) (𝒰 i)).1
      (hdU i e ((Finset.le_sup (f := dU) (Finset.mem_univ i)).trans he))
  exact (span_range_eq_top_iff_surjective (fun j => T j e) U).2
    (GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen _ U.2)

end GlobalTheory.CompanionTheory.GE.Uniform
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformSpanEventuallyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_span_eventually : ∀ {X : Scheme.{0}} [CompactSpace X] {k : ℕ} {K : ℕ → X.Modules} (T : Fin k → ∀ e, K e ⟶ K (e + 1)), (∀ e, (K e).IsQuasicoherent) → (∀ U : X.affineOpens, ∃ dU : ℕ, ∀ e, dU ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤) → ∃ d' : ℕ, ∀ e, d' ≤ e → ∀ U : X.affineOpens, Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform | exact GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform | (intros; apply GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformGenerationOfVanishing
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem uniformGen_of_gradedNoeth : GradedNoeth → UniformVanishing → UniformGen := by
  intro hN hV A _ _ X _ _ H hH k M T d hM
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := hH.compactSpace
  have hcoh := GlobalTheory.T.kernel_sequence_coherent hM
  obtain ⟨d', hd'⟩ := GlobalTheory.T.uniform_span_eventually (KerSeq.kerOp T hM.comm d) (fun e => (hcoh e).1)
    (GlobalTheory.T.kernel_operators_span_eventually hN hM)
  have hK : OpSeq k (KerSeq.kerSeq T d) (KerSeq.kerOp T hM.comm d) d' :=
    ⟨hcoh, KerSeq.kerOp_comm T hM.comm d, hd'⟩
  obtain ⟨n₀, hn₀⟩ := hV (A := A) H hH k _ _ d' hK
  refine ⟨n₀, fun n hn e he => ?_⟩
  obtain ⟨e₀, rfl⟩ := Nat.exists_eq_add_of_le he
  haveI := GlobalTheory.T.operator_sequence_sum_epi hM e₀
  exact GlobalTheory.T.twisted_vanishing_sections_span (GlobalTheory.lbZPow H n) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n) (fun i => T i (d + e₀))
    (kernel.ι _) (kernel.condition _) (KerSeq.kerSC_shortExact T d e₀) (hn₀ n hn e₀ 1 one_pos)

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformGenerationOfVanishingStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_generation_of_vanishing : GradedNoeth → UniformVanishing → UniformGen := by
  first | exact @GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth | exact GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth | (intros; apply GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth <;> assumption)
end
end
