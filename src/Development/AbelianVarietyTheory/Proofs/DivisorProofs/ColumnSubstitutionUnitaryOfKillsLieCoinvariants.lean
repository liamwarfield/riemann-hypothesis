module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [DecidableEq ι]

def colDer {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (Pol ι d a) :=
  ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a,
    S k j • (LinearMap.mulLeft ℂ (X (τ, i, k) : Pol ι d a) ∘ₗ (pderiv (τ, i, j)).toLinearMap)

def atPl {a : ℕ} (τ : ι) (g : Matrix (Fin a) (Fin a) ℂ) : ι → Matrix (Fin a) (Fin a) ℂ :=
  Function.update 1 τ g

theorem colDer_apply {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colDer τ S P = ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a, S k j • (X (τ, i, k) * pderiv (τ, i, j) P) := by
  simp [colDer, LinearMap.sum_apply]

theorem colDer_X {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (v : Var ι d a) :
    colDer (d := d) τ S (X v) = if v.1 = τ then ∑ k, S k v.2.2 • (X (τ, v.2.1, k) : Pol ι d a) else 0 := by
  obtain ⟨σ, i₀, j₀⟩ := v
  rw [colDer_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.ext_iff]
  by_cases h : σ = τ
  · subst h
    simp only [if_true]
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  · simp [h, Ne.symm h]

end GlobalTheory.ColLie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedOppositeSigns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedOppositeSigns
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockOpp

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem raiO_mul_lowO_apply {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (h : ∀ i j, ε' i ≠ ε j) (i : Fin b) (j k : Fin a) (P : PolF D b a) :
    (raiO τ ε ε' i j * lowO τ ε ε' i k) P =
      -(X (τ, i, k) * pderiv (τ, i, j) P) - (if j = k then P else 0) := by
  classical
  have hs : sgn (ε j) * sgn (ε k) = 1 := by
    have h1 := h i j
    have h2 := h i k
    unfold sgn
    cases hi : ε' i <;> cases hj : ε j <;> cases hk : ε k <;> simp_all
  unfold raiO lowO
  rw [if_neg (h i j), if_neg (h i k), smul_mul_smul_comm, hs, one_smul]
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    Derivation.leibniz, smul_eq_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq, true_and]
  by_cases hjk : j = k
  · subst hjk
    simp only [if_true, mul_one]
    ring
  · simp [hjk, Ne.symm hjk]

theorem fockS_of_opposite {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (Y : Matrix (Fin a) (Fin a) ℂ) (h : ∀ i j, ε' i ≠ ε j) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y =
      -(GlobalTheory.ColLie.colDer τ Y.transpose : Module.End ℂ (PolF D b a)) - (((b : ℂ) / 2) * Y.trace) • 1 := by
  classical
  refine LinearMap.ext fun P => ?_
  have key : ∀ (i : Fin b) (j k : Fin a),
      (raiO τ ε ε' i j * lowO τ ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0 : Module.End ℂ (PolF D b a)) P =
        -(X (τ, i, k) * pderiv (τ, i, j) P) - (if j = k then (1 / 2 : ℂ) else 0) • P := by
    intro i j k
    rw [LinearMap.add_apply, raiO_mul_lowO_apply τ ε ε' h]
    by_cases hjk : j = k
    · simp only [hjk, if_true, LinearMap.smul_apply, Module.End.one_apply]
      module
    · simp [hjk]
  have htr : ∑ j, ∑ k, Y j k • ∑ _i : Fin b, (if j = k then (1 / 2 : ℂ) else 0) • P =
      (((b : ℂ) / 2) * Y.trace) • P := by
    simp only [← Finset.sum_smul, smul_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcol : (GlobalTheory.ColLie.colDer τ Y.transpose : Module.End ℂ (PolF D b a)) P =
      ∑ j, ∑ k, Y j k • ∑ i : Fin b, (X (τ, i, k) * pderiv (τ, i, j) P : PolF D b a) := by
    rw [GlobalTheory.ColLie.colDer_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    rfl
  rw [LinearMap.sub_apply, LinearMap.neg_apply, hcol, LinearMap.smul_apply, Module.End.one_apply, ← htr]
  unfold fockS
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    smul_sub, smul_neg]

end GlobalTheory.FockOpp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedOppositeSignsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSourceGlActionSymmetrised_opposite_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i ≠ ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = -(GlobalTheory.ColLie.colDer τ Y.transpose : Module.End ℂ (PolF D b a)) - (((b : ℂ) / 2) * Y.trace) • 1 := by
  first | exact @GlobalTheory.FockOpp.fockS_of_opposite | exact GlobalTheory.FockOpp.fockS_of_opposite | (intros; apply GlobalTheory.FockOpp.fockS_of_opposite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedSameSigns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedSameSigns
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColLie

theorem fockS_eq_colDer_of_same_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i = ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = (GlobalTheory.ColLie.colDer τ Y : Module.End ℂ (PolF D b a)) + (((b : ℂ) / 2) * Y.trace) • 1 := by
  intro D a b τ ε ε' Y h
  have hs : ∀ (i : Fin b) (j k : Fin a), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ ε ε' i j * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ ε ε' i k =
      (LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j) : PolF D b a) ∘ₗ
        (MvPolynomial.pderiv (τ, i, k)).toLinearMap : Module.End ℂ (PolF D b a)) := by
    intro i j k
    have hjk : ε j = ε k := (h i j).symm.trans (h i k)
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε j) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε k) = 1 := by
      rw [hjk]; unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn; split_ifs <;> simp
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO
    rw [if_pos (h i j), if_pos (h i k), smul_mul_smul_comm, h1, one_smul]
    rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS GlobalTheory.ColLie.colDer
  simp only [hs, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  congr 1
  · rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin b)))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
  · simp only [smul_ite, smul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory.ColLie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedSameSignsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSourceGlActionSymmetrised_same_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i = ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = (GlobalTheory.ColLie.colDer τ Y : Module.End ℂ (PolF D b a)) + (((b : ℂ) / 2) * Y.trace) • 1 := by
  first | exact @GlobalTheory.ColLie.fockS_eq_colDer_of_same_signs | exact GlobalTheory.ColLie.fockS_eq_colDer_of_same_signs | (intros; apply GlobalTheory.ColLie.fockS_eq_colDer_of_same_signs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockColumnSubstitutionExpOfColumnDerivation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockColumnSubstitutionExpOfColumnDerivation
noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem totalDegree_colSub_le {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    (colSub g P).totalDegree ≤ P.totalDegree := by
  have hX : ∀ y : Var ι d a, (colSub g (X y : Pol ι d a)).totalDegree ≤ 1 := by
    intro y
    rw [colSub, aeval_X]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  conv_lhs => rw [as_sum P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine le_trans ?_ (le_totalDegree hm)
  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [map_pow]
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (m y) (hX y)

theorem hasDerivAt_dual_of_coeff {σ : Type} [Finite σ] (l : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (N : ℕ)
    (u : ℝ → MvPolynomial σ ℂ) (u' : MvPolynomial σ ℂ) (t : ℝ) (hu : ∀ s, (u s).totalDegree ≤ N)
    (hd : ∀ m, HasDerivAt (fun s => AddMonoidAlgebra.coeff (u s) m) (AddMonoidAlgebra.coeff u' m) t) : HasDerivAt (fun s => l (u s)) (l u') t := by
  classical
  let A : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset ∪ u'.support
  have key : ∀ P : MvPolynomial σ ℂ, P.support ⊆ A → l P = ∑ m ∈ A, AddMonoidAlgebra.coeff P m * l (monomial m 1) := by
    intro P hP
    conv_lhs => rw [as_sum P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_subset_zero_on_sdiff hP (fun m hm => ?_) (fun m _ => ?_)
    · rw [notMem_support_iff.1 (Finset.mem_sdiff.1 hm).2, zero_mul]
    · rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  have h1 : ∀ s, (u s).support ⊆ A := by
    intro s m hm
    refine Finset.mem_union_left _ ?_
    rw [Set.Finite.mem_toFinset]
    exact (le_totalDegree hm).trans (hu s)
  rw [key u' Finset.subset_union_right, funext fun s => key (u s) (h1 s)]
  exact HasDerivAt.fun_sum fun m _ => (hd m).mul_const _

omit [Fintype ι] in
theorem atPl_mul {a : ℕ} (τ : ι) (A B : Matrix (Fin a) (Fin a) ℂ) :
    atPl τ (A * B) = fun σ => atPl τ A σ * atPl τ B σ := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp [atPl]
  · simp [atPl, h]

theorem colSub_atPl_one {d a : ℕ} (τ : ι) (P : Pol ι d a) : colSub (atPl τ 1) P = P := by
  have : (colSub (atPl τ 1) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
    refine algHom_ext fun v => ?_
    have h1 : atPl τ (1 : Matrix (Fin a) (Fin a) ℂ) v.1 = 1 := by
      by_cases h : v.1 = τ
      · rw [h]; simp [atPl]
      · simp [atPl, h]
    rw [colSub, aeval_X, h1, Finset.sum_eq_single v.2.2]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply_ne hb]
      simp
    · simp
  rw [this, AlgHom.id_apply]

theorem colSub_exp_of_colDer : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (c : ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Q),
    (∀ (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a) (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
      HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R) m)
        (AddMonoidAlgebra.coeff (GlobalTheory.ColLie.colDer τ S R) m) 0) →
    (∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P, q (GlobalTheory.ColLie.colDer τ S P) = ((c : ℂ) * S.trace) • q P) →
    ∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P,
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp S)) P) = ((NormedSpace.exp S).det ^ c) • q P := by
  intro ι _ _ d a τ c Q _ _ q hco hq S hS P
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul]
  set k : ℂ := (c : ℂ) * S.trace with hk
  let R : ℝ → Pol ι d a := fun t => colSub (atPl τ (NormedSpace.exp ((t : ℂ) • S))) P
  let f : ℝ → ℂ := fun t => l (q (R t))
  have hadd : ∀ s t : ℝ, colSub (atPl τ (NormedSpace.exp ((s : ℂ) • S))) (R t) = R (s + t) := by
    intro s t
    simp only [R]
    rw [← colSub_mul, ← atPl_mul, Complex.ofReal_add, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl S).smul_left _).smul_right _)]
  have hd : ∀ t, HasDerivAt f (f t * k) t := by
    intro t
    have h0 := hasDerivAt_dual_of_coeff (l ∘ₗ q) (R t).totalDegree
      (fun h : ℝ => colSub (atPl τ (NormedSpace.exp ((h : ℂ) • S))) (R t)) (colDer τ S (R t)) 0
      (fun s => totalDegree_colSub_le _ _) (hco S (R t))
    simp only [hadd, LinearMap.comp_apply, hq S hS, map_smul, smul_eq_mul] at h0
    rw [← sub_self t] at h0
    have h1 := h0.comp_sub_const t t
    simp only [sub_add_cancel] at h1
    rw [mul_comm]
    exact h1
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * k))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * k)) (-k) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const k).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [f, R, Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, NormedSpace.exp_zero, colSub_atPl_one,
    one_mul, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [← hc, GlobalTheory.SUVol.det_exp, ← Complex.exp_nat_mul, ← hk, mul_comm, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

end GlobalTheory.ColLie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockColumnSubstitutionExpOfColumnDerivationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockColumnSubstitution_exp_of_columnDerivation : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (c : ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Q),
    (∀ (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a) (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
      HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R) m)
        (AddMonoidAlgebra.coeff (GlobalTheory.ColLie.colDer τ S R) m) 0) →
    (∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P, q (GlobalTheory.ColLie.colDer τ S P) = ((c : ℂ) * S.trace) • q P) →
    ∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P,
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp S)) P) = ((NormedSpace.exp S).det ^ c) • q P := by
  first | exact @GlobalTheory.ColLie.colSub_exp_of_colDer | exact GlobalTheory.ColLie.colSub_exp_of_colDer | (intros; apply GlobalTheory.ColLie.colSub_exp_of_colDer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtCoeffFockColumnSubstitutionExp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtCoeffFockColumnSubstitutionExp
noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [DecidableEq ι]

theorem hasDerivAt_exp_ofReal_smul_entry {a : ℕ} (S : Matrix (Fin a) (Fin a) ℂ) (i j : Fin a) :
    HasDerivAt (fun h : ℝ => NormedSpace.exp ((h : ℂ) • S) i j) (S i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) S 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  simp only [Complex.coe_smul]
  exact h2

theorem colDer_mul_X {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (v : Var ι d a) :
    colDer τ S (R * X v) = colDer τ S R * X v + R * colDer τ S (X v) := by
  simp only [colDer_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_mul]
  simp only [smul_eq_C_mul]
  ring

theorem hasDerivAt_coeff_mul_X {σ : Type} {A : ℝ → MvPolynomial σ ℂ} {B : MvPolynomial σ ℂ}
    (hA : ∀ m, HasDerivAt (fun h => AddMonoidAlgebra.coeff (A h) m) (AddMonoidAlgebra.coeff B m) 0) (w : σ) (m : σ →₀ ℕ) :
    HasDerivAt (fun h => AddMonoidAlgebra.coeff (A h * X w) m) (AddMonoidAlgebra.coeff (B * X w) m) 0 := by
  classical
  simp only [coeff_mul_X']
  split_ifs
  · exact hA _
  · exact hasDerivAt_const _ _

theorem hasDerivAt_coeff_colSub_of_curve [Fintype ι] {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ)
    (g : ℝ → ι → Matrix (Fin a) (Fin a) ℂ) (h0 : g 0 = 1)
    (hg : ∀ σ i j, HasDerivAt (fun h => g h σ i j) (if σ = τ then S i j else 0) 0)
    (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (colSub (g h) R) m) (AddMonoidAlgebra.coeff (colDer τ S R) m) 0 := by
  have hone : ∀ P : Pol ι d a, colSub (g 0) P = P := by
    have : (colSub (g 0) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro y
      rw [h0]
      simp only [colSub, aeval_X, Pi.one_apply, AlgHom.id_apply]
      rw [Finset.sum_eq_single y.2.2]
      · simp
      · intro j _ hj
        simp [Matrix.one_apply_ne hj]
      · simp
    intro P
    rw [this, AlgHom.id_apply]
  induction R using MvPolynomial.induction_on generalizing m with
  | C c =>
    have h1 : colDer τ S (C c : Pol ι d a) = 0 := by simp [colDer_apply]
    simp only [h1, algHom_C, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact hasDerivAt_const _ _
  | add P Q hP hQ =>
    simp only [map_add (f := _), AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (hP m).add (hQ m)
  | mul_X P v hP =>
    have e1 : ∀ h, AddMonoidAlgebra.coeff (colSub (g h) (P * X v)) m =
        ∑ k, g h v.1 k v.2.2 * AddMonoidAlgebra.coeff (colSub (g h) P * X (v.1, v.2.1, k)) m := by
      intro h
      rw [map_mul]
      conv_lhs => rw [show colSub (g h) (X v : Pol ι d a) = ∑ k, C (g h v.1 k v.2.2) * X (v.1, v.2.1, k) by
        simp [colSub]]
      rw [Finset.mul_sum, coeff_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_left_comm, coeff_C_mul]
    simp only [e1]
    have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hg v.1 k v.2.2).fun_mul (hasDerivAt_coeff_mul_X hP (v.1, v.2.1, k) m)
    refine hd.congr_deriv ?_
    rw [colDer_mul_X, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finset.sum_add_distrib, add_comm]
    congr 1
    · rw [h0, Finset.sum_eq_single v.2.2]
      · simp
      · intro j _ hj
        simp [Matrix.one_apply_ne hj]
      · simp
    · rw [colDer_X, hone]
      by_cases hv : v.1 = τ
      · subst hv
        simp only [if_true, Finset.mul_sum, coeff_sum, mul_smul_comm, coeff_smul, smul_eq_mul]
      · simp [hv]

theorem hasDerivAt_coeff_colSub_exp {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι)
    (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (colSub (atPl τ (NormedSpace.exp ((h : ℂ) • S))) R) m)
      (AddMonoidAlgebra.coeff (colDer τ S R) m) 0 := by
  refine hasDerivAt_coeff_colSub_of_curve τ S (fun h => atPl τ (NormedSpace.exp ((h : ℂ) • S))) ?_ ?_ R m
  · simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, atPl]
    exact Function.update_eq_self τ 1
  · intro σ i j
    by_cases h : σ = τ
    · subst h
      simp only [atPl, Function.update_self, if_true]
      exact hasDerivAt_exp_ofReal_smul_entry S i j
    · simp only [atPl, Function.update_of_ne h, if_neg h]
      exact hasDerivAt_const _ _

end GlobalTheory.ColLie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtCoeffFockColumnSubstitutionExpStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a)
    (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
    HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R) m)
      (AddMonoidAlgebra.coeff (GlobalTheory.ColLie.colDer τ S R) m) 0 := by
  first | exact @GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp | exact GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp | (intros; apply GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnSubstitutionUnitaryOfKillsLieCoinvariants
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.LieInt

theorem exists_exp_unitary {a : ℕ} (u : Matrix.unitaryGroup (Fin a) ℂ) :
    ∃ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S ∧ NormedSpace.exp S = u := by
  have hJ : ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin a => true) = 1 := by
    simp [ReciprocityTheory.ChartRestriction.DS.Jm]
  obtain ⟨Z, ⟨hG, -⟩, hZ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_exp_eq_of_mem_Kset (ε := fun _ : Fin a => true)
    (k := (u : Matrix (Fin a) (Fin a) ℂ)) ⟨u.2, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
  refine ⟨Z, ?_, hZ⟩
  unfold ReciprocityTheory.ChartRestriction.DS.inG at hG
  rw [hJ, Matrix.mul_one, Matrix.one_mul] at hG
  exact eq_neg_of_add_eq_zero_left hG

theorem colDer_neg {ι : Type} [DecidableEq ι] {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) :
    (GlobalTheory.ColLie.colDer (d := d) τ (-S)) = -GlobalTheory.ColLie.colDer τ S := by
  simp [GlobalTheory.ColLie.colDer, Finset.sum_neg_distrib, neg_smul]

theorem trace_map_conj {a : ℕ} (S : Matrix (Fin a) (Fin a) ℂ) (hS : S.conjTranspose = -S) :
    (S.map (starRingEnd ℂ)).trace = -S.trace := by
  have h : (S.map (starRingEnd ℂ)).trace = S.conjTranspose.trace := by
    simp [Matrix.trace, Matrix.diag, Matrix.conjTranspose_apply]
  rw [h, hS, Matrix.trace_neg]

theorem act_eq (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X)
    (eT : D.what₂.Tau → ℚ) (n₀ : D.what₂.Tau → ℕ) (hA : ∀ τ j, A.ε τ j = true) (hB : ∀ τ i, B.ε τ i = true)
    (hn : ∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) (τ : D.what₂.Tau)
    (S : Matrix (Fin M.rank) (Fin M.rank) ℂ) (hS : S.conjTranspose = -S) :
    ∃ Z ∈ lieAt M τ, GlobalTheory.RealQuot.actS ε A B eT τ Z =
      GlobalTheory.ColLie.colDer τ S - (((n₀ τ : ℕ) : ℂ) * S.trace) • (1 : Module.End ℂ (PolF D X.rank M.rank)) := by
  classical
  set F := A.fr τ with hF
  have hFu : IsUnit F := A.fr_unit τ
  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hFu
  have hFFi : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hFd
  have hFiF : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul F hFd
  have hJ : Formalism.REAL.Jm (A.ε τ) = 1 := by
    ext i j
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, hA τ]
  have hG : gramAt D M τ = F.conjTranspose * F := by
    rw [← A.fr_gram τ, hJ, Matrix.mul_one]
  set Zf : Matrix (Fin M.rank) (Fin M.rank) ℂ := if ε then S else S.map (starRingEnd ℂ) with hZf
  have hZfs : Zf.conjTranspose = -Zf := by
    rcases ε with _ | _
    · simp only [hZf, if_false, Bool.false_eq_true]
      ext i j
      have := congrFun (congrFun hS j) i
      simp [Matrix.conjTranspose_apply] at this ⊢
      rw [this, neg_neg]
    · simpa [hZf] using hS
  refine ⟨F⁻¹ * Zf * F, ?_, ?_⟩
  · show (F⁻¹ * Zf * F).conjTranspose * gramAt D M τ + gramAt D M τ * (F⁻¹ * Zf * F) = 0
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hZfs]
    have h1 : (F⁻¹).conjTranspose * F.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hFFi, Matrix.conjTranspose_one]
    calc _ = F.conjTranspose * -Zf * ((F⁻¹).conjTranspose * F.conjTranspose) * F +
          F.conjTranspose * (F * F⁻¹) * Zf * F := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1, hFFi]; simp [Matrix.mul_neg, Matrix.neg_mul]
  · have hconj : F * (F⁻¹ * Zf * F) * F⁻¹ = Zf := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFFi, Matrix.one_mul, Matrix.mul_assoc, hFFi, Matrix.mul_one]
    have htr : (F⁻¹ * Zf * F).trace = Zf.trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hFFi, Matrix.one_mul]
    have hsg : (GlobalTheory.SquareComm.frSgn ε A).ε τ = fun _ => !ε := by
      funext j
      simp [GlobalTheory.SquareComm.frSgn, hA τ j]
    have hn' : ((n₀ τ : ℕ) : ℂ) = (((if ε then eT τ else -eT τ) : ℚ) : ℂ) - (X.rank : ℂ) / 2 := by
      have := congrArg (fun x : ℚ => (x : ℂ)) (hn τ)
      push_cast at this ⊢
      exact this
    unfold GlobalTheory.RealQuot.actS
    rw [hsg, hconj, htr]
    rcases ε with _ | _
    · have h2 := GlobalTheory.T.fockSourceGlActionSymmetrised_same_signs (D := D) τ (fun _ : Fin M.rank => !false) (B.ε τ) (Zf.map (starRingEnd ℂ))
        (fun i j => by simp [hB τ i])
      rw [h2]
      have hY : Zf.map (starRingEnd ℂ) = S := by
        ext i j
        simp [hZf]
      have hZt : Zf.trace = -S.trace := by
        simp only [hZf, Bool.false_eq_true, if_false]
        exact trace_map_conj S hS
      rw [hY, hZt, hn']
      simp only [Bool.false_eq_true, if_false]
      push_cast
      module
    · have h1 := GlobalTheory.T.fockSourceGlActionSymmetrised_opposite_signs (D := D) τ (fun _ : Fin M.rank => !true) (B.ε τ) (Zf.map (starRingEnd ℂ))
        (fun i j => by simp [hB τ i])
      rw [h1]
      have hY : (Zf.map (starRingEnd ℂ)).transpose = -S := by
        rw [← hS]
        ext i j
        simp [hZf, Matrix.conjTranspose_apply]
      have hYt : (Zf.map (starRingEnd ℂ)).trace = -S.trace := by
        simp only [hZf, if_true]
        exact trace_map_conj S hS
      have hZt : Zf.trace = S.trace := by simp [hZf]
      rw [hY, hYt, hZt, hn', colDer_neg]
      simp only [if_true]
      push_cast
      module

theorem colSub_unitary_of_coinv : ∀ (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (eT : D.what₂.Tau → ℚ)
    (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q] (q : PolF D X.rank M.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) →
    GlobalTheory.RealQuot.coinv ε A B eT ≤ LinearMap.ker q →
    ∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) • q P := by
  intro D ε M X A B eT n₀ Q _ _ q hA hB hn hker
  have hS : ∀ τ (S : Matrix (Fin M.rank) (Fin M.rank) ℂ), S.conjTranspose = -S → ∀ P : PolF D X.rank M.rank,
      q (GlobalTheory.ColLie.colDer τ S P) = (((n₀ τ : ℕ) : ℂ) * S.trace) • q P := by
    intro τ S hS P
    obtain ⟨Z, hZ, he⟩ := act_eq D ε M X A B eT n₀ hA hB hn τ S hS
    have hmem : GlobalTheory.RealQuot.actS ε A B eT τ Z P ∈ GlobalTheory.RealQuot.coinv ε A B eT :=
      Submodule.subset_span ⟨τ, Z, hZ, P, rfl⟩
    have h0 := hker hmem
    rw [LinearMap.mem_ker, he, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul,
      sub_eq_zero] at h0
    exact h0
  have h1 : ∀ τ (u : Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (u : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        ((u : Matrix (Fin M.rank) (Fin M.rank) ℂ).det ^ n₀ τ) • q P := by
    intro τ u P
    obtain ⟨S, hS', he⟩ := exists_exp_unitary u
    rw [← he]
    exact GlobalTheory.T.fockColumnSubstitution_exp_of_columnDerivation _ _ τ (n₀ τ) Q q (GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp _ _ τ) (hS τ) S hS' P
  intro g P
  have key : ∀ s : Finset D.what₂.Tau, ∀ P : PolF D X.rank M.rank,
      q (GlobalTheory.MinorFrame.colSub (fun τ => if τ ∈ s then (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) P) =
        (∏ τ ∈ s, (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ).det ^ n₀ τ) • q P := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro P
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, one_smul]
      rw [GlobalTheory.MinorFrame.colSub_one, AlgHom.id_apply]
    | insert τ s hτ ih =>
      intro P
      have hsplit : (fun σ => if σ ∈ insert τ s then (g σ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) =
          fun σ => GlobalTheory.ColLie.atPl τ (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ) σ *
            (if σ ∈ s then (g σ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) := by
        funext σ
        by_cases h : σ = τ
        · subst h
          simp [GlobalTheory.ColLie.atPl, hτ]
        · simp [GlobalTheory.ColLie.atPl, h, Function.update_of_ne h]
      rw [hsplit, GlobalTheory.MinorFrame.colSub_mul, h1, ih, smul_smul, Finset.prod_insert hτ]
  have := key Finset.univ P
  simp only [Finset.mem_univ, if_true] at this
  rw [this]
  rfl

end GlobalTheory.LieInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnSubstitutionUnitaryOfKillsLieCoinvariantsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnSubstitution_unitary_of_kills_lieCoinvariants : ∀ (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (eT : D.what₂.Tau → ℚ)
    (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q] (q : PolF D X.rank M.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) →
    GlobalTheory.RealQuot.coinv ε A B eT ≤ LinearMap.ker q →
    ∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) • q P := by
  first | exact @GlobalTheory.LieInt.colSub_unitary_of_coinv | exact GlobalTheory.LieInt.colSub_unitary_of_coinv | (intros; apply GlobalTheory.LieInt.colSub_unitary_of_coinv <;> assumption)
end
