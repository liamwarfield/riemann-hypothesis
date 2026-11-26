module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def genSet (D : D7) (n : ℕ) : Set (G D n) :=
  {g | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1)}

def blkDm {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

def eI {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if i ∈ I then 1 else 0

def wIm {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 (1 - eI I) (eI I) (-eI I) (1 - eI I)

def J2 (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R := blk4 0 1 (-1) 0

def UnitD : Prop :=
  ∀ (D : D7) (n : ℕ) (g : G D n), IsUnit (blkDm (mat g)).det → g ∈ Subgroup.closure (genSet D n)

def PIn : Prop := ∀ (D : D7) (n : ℕ), ∀ p ∈ P D n, p ∈ Subgroup.closure (genSet D n)

def LocRedField : Prop :=
  ∀ (k : Type) [Field k] (σ : k →+* k), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (g : GL (Fin (n + n)) k),
    g ∈ Formalism.UG.UJ σ (J2 k n) → ∃ I : Finset (Fin n), IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * wIm I)).det

def LocRedSplit : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (g : GL (Fin (n + n)) k), ∃ (a d : GL (Fin n) k) (I : Finset (Fin n)),
    IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * blk4 a.1 0 0 d.1 * wIm I)).det

def KInInf : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (mat k).map (finPart D) = 1 → k ∈ Subgroup.closure (genSet D n)

def KInFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (∀ τ, (mat k).map (Formalism.IndefR.Eqv.psiT D τ) = 1) → k ∈ Subgroup.closure (genSet D n)

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GIautoOf
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem gIauto_of (hT : PositivityTheory.PfSWUS.ThetaAuto) (hM : TensMem) : GIauto := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC Ψ hΨ
  have hm := hM D n V θ l s τ ε fr hC.hθ (lNZ D ψ θ l hC.hψ hC.hθ hC.hl) hC.hs hC.hfr Ψ hΨ 1
  have hphi : (phiS θ τ fr (cLoc l τ) Ψ 1).1 = tens θ τ fr (fP (cLoc l τ) 1) Ψ := by
    unfold phiS
    rw [dite_eq_left hm.1]
  have hStd : PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ 1) :=
    ⟨hC.hψ, hC.hχ, hC.hη, hC.hθ, hC.hμ, hC.hω, hC.hH, hC.hl, hC.hs, hC.hν, by rw [hphi]; exact hm.2⟩
  obtain ⟨h1, h2⟩ := hT D n V ψ χ θ μ ω H l s ν _ hStd hC.hr
  exact ⟨h1, fun γ hγ g => h2 γ hγ g⟩

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ThetaIntSmul
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ZReAddZImStar
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

def xyC (Z : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (Z a c) * MvPolynomial.X (c, i, b)

def vfC (c : ℝ) (Zh Za : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyC Zh a i false * pderiv (a, i, false) P + xyC Za a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyC Zh a i false * MvPolynomial.X (a, i, true) + xyC Za a i true * MvPolynomial.X (a, i, false)) * P)

theorem vfX_eq (c : ℝ) (Z : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : vfX c Z P = vfC c Z (Z.map star) P := by
  have h1 : ∀ a (i : Fin n), xyP Z a i false = xyC Z a i false := fun a i => by simp [xyP, xyC]
  have h2 : ∀ a (i : Fin n), xyP Z a i true = xyC (Z.map star) a i true := fun a i => by simp [xyP, xyC, Matrix.map_apply]
  simp only [vfX, vfC, h1, h2]

theorem xyC_add_smul (Z Z' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    xyC (Z + r • Z') a i b = xyC Z a i b + C r * xyC Z' a i b := by
  simp only [xyC, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem vfC_lin (c : ℝ) (Zh Za Zh' Za' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (P : PX m n) :
    vfC c Zh Za P + r • vfC c Zh' Za' P = vfC c (Zh + r • Zh') (Za + r • Za') P := by
  simp only [vfC, xyC_add_smul, smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem xyC_single (a b a' : Fin m) (r : ℂ) (i : Fin n) (β : Bool) :
    xyC (r • Matrix.single a b (1 : ℂ)) a' i β = if a' = a then C r * MvPolynomial.X (b, i, β) else 0 := by
  by_cases h : a' = a
  · subst h
    simp only [xyC, Matrix.smul_apply, Matrix.single_apply, true_and, smul_eq_mul, mul_ite, mul_one,
      mul_zero, if_true]
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  · simp [xyC, Matrix.single_apply, h, Ne.symm h]

theorem sgn_star (ε : Fin m → Bool) (a : Fin m) : star (sgn ε a) = sgn ε a := by
  unfold sgn; split_ifs <;> simp

theorem zRe_add_zIm (ε : Fin m → Bool) (a b : Fin m) :
    zRe ε a b + Complex.I • zIm ε a b = (1 : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem zRe_add_zIm_star (ε : Fin m → Bool) (a b : Fin m) :
    (zRe ε a b).map star + Complex.I • (zIm ε a b).map star = (-(sgn ε a * sgn ε b)) • Matrix.single b a (1 : ℂ) := by
  have hs : (starRingEnd ℂ) (sgn ε a) = sgn ε a := sgn_star ε a
  have ht : (starRingEnd ℂ) (sgn ε b) = sgn ε b := sgn_star ε b
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply,
    smul_eq_mul, Matrix.neg_apply, Matrix.single_apply, Complex.star_def]
  split_ifs <;> simp [map_add (f := _), map_mul, map_neg, map_sub, hs, ht, h2, Complex.conj_I] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem hOp_eq (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (P : PX m n) :
    hOp ε c a b P = vfX c (zRe ε a b) P + Complex.I • vfX c (zIm ε a b) P := by
  rw [vfX_eq, vfX_eq, vfC_lin, zRe_add_zIm, zRe_add_zIm_star]
  unfold vfC hOp
  simp only [xyC_single]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, add_mul, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [map_neg, map_one, map_mul, map_sub]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

theorem isUe_zRe (ε : Fin m → Bool) (a b : Fin m) : IsUe ε (zRe ε a b) := by
  have e1 : star ((1 : ℂ) / 2) = 1 / 2 := by simp
  ext i j
  simp only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, zRe, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_sub, e1]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
    simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>
    (try subst_vars) <;> unfold sgn <;> split_ifs <;>
    first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | norm_num | (simp only [star_one, star_zero]; norm_num)

theorem isUe_zIm (ε : Fin m → Bool) (a b : Fin m) : IsUe ε (zIm ε a b) := by
  have e2 : star (-(Complex.I / 2)) = Complex.I / 2 := by
    apply Complex.ext <;> simp <;> norm_num
  ext i j
  simp only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, zIm, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_add, e2]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
    simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>
    (try subst_vars) <;> unfold sgn <;> split_ifs <;>
    first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | ring | (simp only [star_one, star_zero]; norm_num)

theorem thetaInt_at {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank n) (g : G D n) : thetaInt ω ν Φ g = thetaInt ω ν (ω g Φ) 1 := by
  have h : theta ω Φ g = theta ω (ω g Φ) 1 := by
    funext h
    simp only [theta, map_one, Module.End.one_apply]
  simp only [thetaInt, h]

theorem thetaInt_smul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (r : ℂ) (Φ : schwartzA θ V.rank n) (g : G D n) : thetaInt ω ν (r • Φ) g = r * thetaInt ω ν Φ g := by
  have h : theta ω (r • Φ) g = fun h => r * theta ω Φ g h := by
    funext h
    simp only [theta, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact tsum_mul_left
  simp only [thetaInt, h, GlobalTheory.AutomorphicL2Unitary.descend, MeasureTheory.average_eq, integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

theorem phiS_of_mem {θ : InfFam D} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (P : PX m n) (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : phiS θ τ fr c Ψ P = ⟨_, h⟩ := by
  unfold phiS; rw [dite_eq_left h]

theorem tens_add_smul {θ : InfFam D} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (A B : PX m n) (r : ℂ) :
    tens θ τ fr (fP c (A + r • B)) Ψ = tens θ τ fr (fP c A) Ψ + r • tens θ τ fr (fP c B) Ψ := by
  funext x
  simp only [tens, fP, evX, map_add (f := _), MvPolynomial.smul_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH

namespace PositivityTheory.Rg.Sw.Glob

open IInvH in
theorem gIinv_of (hT : TensMem) (hL : ThLin) (hC : LieComm) (hO : DerivOne) : GIinv := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ g a b P
  have hmem := fun Q => hT D n V θ l s τ ε fr hx.hθ (lNZ D ψ θ l hx.hψ hx.hθ hx.hl) hx.hs hx.hfr Ψ hΨ Q
  have hstd : ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ :=
    fun Φ hΦ => ⟨hx.hψ, hx.hχ, hx.hη, hx.hθ, hx.hμ, hx.hω, hx.hH, hx.hl, hx.hs, hx.hν, hΦ⟩

  have h0 : ∀ X, IsUe ε X → ∀ Q, thF ω ν τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q) g = 0 := by
    intro X hX Q
    unfold thF
    rw [thetaInt_at]
    exact hO D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX (ω g (phiS θ τ fr (cLoc l τ) Ψ Q))
      (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q))) (fun x => hC D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ X hX Q g x)
  rw [hOp_eq]
  set A := vfX (cLoc l τ) (zRe ε a b) P
  set B := vfX (cLoc l τ) (zIm ε a b) P
  have hA := phiS_of_mem τ fr (cLoc l τ) Ψ A (hmem A).1
  have hB := phiS_of_mem τ fr (cLoc l τ) Ψ B (hmem B).1
  have hAB := phiS_of_mem τ fr (cLoc l τ) Ψ (A + Complex.I • B) (hmem (A + Complex.I • B)).1
  have hsum : phiS θ τ fr (cLoc l τ) Ψ (A + Complex.I • B) =
      phiS θ τ fr (cLoc l τ) Ψ A + Complex.I • phiS θ τ fr (cLoc l τ) Ψ B := by
    rw [hA, hB, hAB]
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    exact tens_add_smul τ fr (cLoc l τ) Ψ A B Complex.I
  have hfA : (phiS θ τ fr (cLoc l τ) Ψ A).1 ∈ fockA θ V n l s := by rw [hA]; exact (hmem A).2
  have hfB : (Complex.I • phiS θ τ fr (cLoc l τ) Ψ B).1 ∈ fockA θ V n l s := by
    rw [hB, Submodule.coe_smul]; exact (fockA θ V n l s).smul_mem _ (hmem B).2
  unfold thF
  rw [hsum, hL D n V ψ χ θ μ ω H l s ν _ _ (hstd _ hfA) (hstd _ hfB) hx.hr g, thetaInt_smul]
  have e1 := h0 _ (isUe_zRe ε a b) P
  have e2 := h0 _ (isUe_zIm ε a b) P
  unfold thF at e1 e2
  rw [e1, e2]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end
