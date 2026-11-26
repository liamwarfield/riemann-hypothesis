module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.RowActDiagMonomial
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FockFEqSumOfSubsetB
noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

private theorem fockF_eq_sum_lemma {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

theorem fockF_smul_left_B {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) g = c * Formalism.REAL.fockF f g := by
  rw [fockF_eq_sum_lemma (c • f) g f.support MvPolynomial.support_smul]
  unfold Formalism.REAL.fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fockF_smul_right_B {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (c • g) = star c * Formalism.REAL.fockF f g := by
  unfold Formalism.REAL.fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fockF_add_left_B {σ : Type} [DecidableEq σ] (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  rw [fockF_eq_sum_lemma (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fockF_eq_sum_lemma f g (f.support ∪ f'.support) Finset.subset_union_left,
    fockF_eq_sum_lemma f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fockF_self_re_nonneg_B {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ (Formalism.REAL.fockF f f).re := by
  unfold Formalism.REAL.fockF
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun m _ => ?_
  rw [show star (f.coeff m) = (starRingEnd ℂ) (f.coeff m) from rfl, Complex.mul_conj,
    Complex.re_ofReal_mul, Complex.natCast_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

def coreB {N : ℕ} (lam : DomWeight N) : InnerProductSpace.Core ℂ (nablaSq ℂ N lam) where
  inner x y := Formalism.REAL.fockF (y : MvPolynomial (Fin N × Fin N) ℂ) x
  conj_inner_symm x y := by
    show starRingEnd ℂ (Formalism.REAL.fockF (x : MvPolynomial (Fin N × Fin N) ℂ) y) =
      Formalism.REAL.fockF (y : MvPolynomial (Fin N × Fin N) ℂ) x
    rw [starRingEnd_apply, ← Formalism.GradedWeylDivisibility.fockHerm]
  re_inner_nonneg x := fockF_self_re_nonneg_B (x : MvPolynomial (Fin N × Fin N) ℂ)
  add_left x y z := by
    show Formalism.REAL.fockF (z : MvPolynomial (Fin N × Fin N) ℂ)
      ((x + y : nablaSq ℂ N lam) : MvPolynomial (Fin N × Fin N) ℂ) = _
    rw [Submodule.coe_add, Formalism.GradedWeylDivisibility.fockHerm, fockF_add_left_B, star_add, ← Formalism.GradedWeylDivisibility.fockHerm,
      ← Formalism.GradedWeylDivisibility.fockHerm]
  smul_left x y r := by
    show Formalism.REAL.fockF (y : MvPolynomial (Fin N × Fin N) ℂ)
      ((r • x : nablaSq ℂ N lam) : MvPolynomial (Fin N × Fin N) ℂ) = _
    rw [Submodule.coe_smul, fockF_smul_right_B, starRingEnd_apply]
  definite x hx := by
    apply Subtype.ext
    by_contra hne
    have := (Formalism.GradedWeylDivisibility.fockPos _ (x : MvPolynomial (Fin N × Fin N) ℂ) hne).1
    have hx' : Formalism.REAL.fockF (x : MvPolynomial (Fin N × Fin N) ℂ) x = 0 := hx
    rw [hx'] at this; simp at this

theorem dualWeyl_le_homog_B (r n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl ℂ r n ν ≤ homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s) := by
  intro f hf
  have hw := (Submodule.mem_inf.mp hf).1
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hw
  rw [MvPolynomial.mem_homogeneousSubmodule]
  intro d hd
  have h1 := hw hd
  rw [← h1]
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  simp

theorem fd_B (N : ℕ) (lam : DomWeight N) : FiniteDimensional ℂ (nablaSq ℂ N lam) := by
  have hle := dualWeyl_le_homog_B N N lam.natW
  have hfin : {d : (Fin N × Fin N) →₀ ℕ | d.degree = ∑ s, lam.natW s}.Finite := by
    refine (Finset.finsuppAntidiag Finset.univ (∑ s, lam.natW s)).finite_toSet.subset fun d hd => ?_
    rw [Finset.mem_coe, Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    rw [← hd, Finsupp.degree_eq_sum]
  have hsub : homogeneousSubmodule (Fin N × Fin N) ℂ (∑ s, lam.natW s) ≤
      Submodule.span ℂ ((fun d => (MvPolynomial.monomial d (1 : ℂ))) ''
        {d : (Fin N × Fin N) →₀ ℕ | d.degree = ∑ s, lam.natW s}) := by
    intro f hf
    rw [MvPolynomial.mem_homogeneousSubmodule] at hf
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hdeg : d.degree = ∑ s, lam.natW s := by
      have h2 := hf (MvPolynomial.mem_support_iff.mp hd)
      rw [Finsupp.degree_eq_weight_one]
      exact h2
    rw [show MvPolynomial.monomial d (f.coeff d) = f.coeff d • MvPolynomial.monomial d (1 : ℂ) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hdeg, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ ((fun d => (MvPolynomial.monomial d (1 : ℂ))) ''
      {d : (Fin N × Fin N) →₀ ℕ | d.degree = ∑ s, lam.natW s})) :=
    FiniteDimensional.span_of_finite ℂ (hfin.image _)
  exact Submodule.finiteDimensional_of_le (hle.trans hsub)

def gStarB {N : ℕ} (g : GL (Fin N) ℂ) : GL (Fin N) ℂ where
  val := Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ)
  inv := Matrix.conjTranspose ((g⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  val_inv := by rw [← Matrix.conjTranspose_mul]; simp
  inv_val := by rw [← Matrix.conjTranspose_mul]; simp

theorem gStarB_val {N : ℕ} (g : GL (Fin N) ℂ) :
    ((gStarB g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ) := rfl

theorem embGL_gStarB {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    embGL ℂ n N h (gStarB g) = gStarB (embGL ℂ n N h g) := by
  apply Units.ext
  simp only [embGL, Units.coe_map, gStarB_val, MonoidHom.comp_apply]
  simp [blkHom, Matrix.fromBlocks_conjTranspose]

theorem detPow_gStarB {N : ℕ} (g : GL (Fin N) ℂ) (k : ℤ) :
    detPow ℂ N (gStarB g) k = star (detPow ℂ N g k) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, gStarB_val, Matrix.det_conjTranspose, star_zpow₀]

theorem sqAct_mem_B {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ nablaSq ℂ N lam) : sqAct ℂ N lam g f ∈ nablaSq ℂ N lam := by
  unfold sqAct
  exact (nablaSq ℂ N lam).smul_mem _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)

theorem fock_sqAct_adj_B {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.REAL.fockF (sqAct ℂ N lam g x) y = Formalism.REAL.fockF x (sqAct ℂ N lam (gStarB g) y) := by
  unfold sqAct
  rw [fockF_smul_left_B, fockF_smul_right_B, detPow_gStarB, star_star, Formalism.GradedWeylDivisibility.fockRowAdj]
  congr 2

theorem stableCompl_B : StableCompl := by
  intro n N h lam W hW hstab
  classical
  let W' : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
    { carrier := {f | f ∈ nablaSq ℂ N lam ∧ ∀ w ∈ W, Formalism.REAL.fockF f w = 0}
      add_mem' := fun {a b} ha hb => ⟨(nablaSq ℂ N lam).add_mem ha.1 hb.1, fun w hw => by
        rw [fockF_add_left_B, ha.2 w hw, hb.2 w hw, add_zero]⟩
      zero_mem' := ⟨(nablaSq ℂ N lam).zero_mem, fun w _ => by simp [Formalism.REAL.fockF]⟩
      smul_mem' := fun c a ha => ⟨(nablaSq ℂ N lam).smul_mem c ha.1, fun w hw => by
        rw [fockF_smul_left_B, ha.2 w hw, mul_zero]⟩ }
  have hW'V : W' ≤ nablaSq ℂ N lam := fun f hf => hf.1
  refine ⟨W', hW'V, ?_, ?_, ?_⟩
  · intro g f hf
    refine ⟨sqAct_mem_B lam _ f hf.1, fun w hw => ?_⟩
    rw [fock_sqAct_adj_B, ← embGL_gStarB]
    exact hf.2 _ (hstab (gStarB g) w hw)
  · apply le_antisymm (sup_le hW hW'V)
    intro f hf
    letI := coreB lam
    letI : NormedAddCommGroup (nablaSq ℂ N lam) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    letI : InnerProductSpace ℂ (nablaSq ℂ N lam) := InnerProductSpace.ofCore (coreB lam).toCore
    haveI : FiniteDimensional ℂ (nablaSq ℂ N lam) := fd_B N lam
    let K : Submodule ℂ (nablaSq ℂ N lam) := W.comap (nablaSq ℂ N lam).subtype
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K K.orthogonal
    rw [Submodule.inf_orthogonal_eq_bot, finrank_bot, add_zero, Submodule.finrank_add_finrank_orthogonal] at h1
    have hs : K ⊔ K.orthogonal = ⊤ := Submodule.eq_top_of_finrank_eq h1
    have hmem : (⟨f, hf⟩ : nablaSq ℂ N lam) ∈ K ⊔ K.orthogonal := by
      rw [hs]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    rw [Submodule.mem_sup]
    refine ⟨(a : MvPolynomial (Fin N × Fin N) ℂ), ha, (b : MvPolynomial (Fin N × Fin N) ℂ),
      ⟨b.2, fun w hw => ?_⟩, ?_⟩
    · exact (Submodule.mem_orthogonal K b).mp hb ⟨w, hW hw⟩ hw
    · have hv := congrArg Subtype.val hab
      simpa using hv
  · rw [eq_bot_iff]
    intro f hf
    obtain ⟨hfW, hfW'⟩ := Submodule.mem_inf.mp hf
    have h0 : Formalism.REAL.fockF f f = 0 := hfW'.2 f hfW
    rw [Submodule.mem_bot]
    by_contra hne
    have hpos := (Formalism.GradedWeylDivisibility.fockPos _ f hne).1
    rw [h0] at hpos
    simp at hpos

end PI.WGB
end
end

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

def wnB (n N : ℕ) : Fin N × Fin N → (Fin n → ℕ) :=
  fun v => if hv : v.1.1 < n then Pi.single (⟨v.1.1, hv⟩ : Fin n) 1 else 0

def prowB (n N : ℕ) (a : Fin N) : ℕ := if a.1 < n then n - a.1 else 0

def psiB (n N : ℕ) : Fin N × Fin N → ℕ := fun v => prowB n N v.1

def PsiB (n : ℕ) : (Fin n → ℕ) →+ ℕ where
  toFun m := ∑ j, (n - j.1) * m j
  map_zero' := by simp
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]

theorem PsiB_apply (n : ℕ) (m : Fin n → ℕ) : PsiB n m = ∑ j, (n - j.1) * m j := rfl

theorem PsiB_wnB (n N : ℕ) (v : Fin N × Fin N) : PsiB n (wnB n N v) = psiB n N v := by
  unfold wnB psiB prowB
  split_ifs with hv
  · rw [PsiB_apply]
    simp [Pi.single_apply]
  · simp

theorem weight_psiB (n N : ℕ) (e : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (psiB n N) e = PsiB n (Finsupp.weight (wnB n N) e) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_nsmul, PsiB_wnB]

def chiB {n : ℕ} (t : Fin n → ℂ) (m : Fin n → ℕ) : ℂ := ∏ j, t j ^ m j

theorem chiB_add {n : ℕ} (t : Fin n → ℂ) (a b : Fin n → ℕ) : chiB t (a + b) = chiB t a * chiB t b := by
  simp [chiB, pow_add, Finset.prod_mul_distrib]

theorem chiB_smul {n : ℕ} (t : Fin n → ℂ) (k : ℕ) (a : Fin n → ℕ) : chiB t (k • a) = chiB t a ^ k := by
  simp only [chiB, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm]

theorem chiB_zero {n : ℕ} (t : Fin n → ℂ) : chiB t 0 = 1 := by simp [chiB]

theorem chiB_weight {n : ℕ} {σ : Type*} (t : Fin n → ℂ) (w : σ → (Fin n → ℕ)) (e : σ →₀ ℕ) :
    chiB t (Finsupp.weight w e) = ∏ v ∈ e.support, chiB t (w v) ^ e v := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  induction e.support using Finset.cons_induction with
  | empty => simp [chiB_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, chiB_add, chiB_smul, ih]

def dB (n N : ℕ) (t : Fin n → ℂ) : Fin N → ℂ := fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1

theorem chiB_wnB {n N : ℕ} (t : Fin n → ℂ) (v : Fin N × Fin N) : chiB t (wnB n N v) = dB n N t v.1 := by
  unfold wnB dB
  split_ifs with hv
  · unfold chiB
    rw [Finset.prod_eq_single (⟨v.1.1, hv⟩ : Fin n)]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  · simp [chiB]

theorem rowAct_diag_X {N : ℕ} (d : Fin N → ℂ) (v : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal d) (X v) = C (d v.1) * X v := by
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem rowAct_diag_monomial {n N : ℕ} (t : Fin n → ℂ) (e : Fin N × Fin N →₀ ℕ) (c : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) (monomial e c) =
      chiB t (Finsupp.weight (wnB n N) e) • monomial e c := by
  have hC : Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) (C c) = C c := by
    simp [Formalism.GradedWeylDivisibility.rowAct]
  rw [chiB_weight, monomial_eq, map_mul, hC, Finsupp.prod, map_prod]
  simp only [map_pow, rowAct_diag_X, mul_pow, Finset.prod_mul_distrib, chiB_wnB]
  rw [smul_eq_C_mul, map_prod]
  simp only [C_pow]
  ring

theorem rowAct_diag_homog {n N : ℕ} (t : Fin n → ℂ) (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ)
    (hg : IsWeightedHomogeneous (wnB n N) g m) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) g = chiB t m • g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [rowAct_diag_monomial, hg (mem_support_iff.mp he)]

theorem comp_sum_B {σ M : Type*} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (f : MvPolynomial σ ℂ)
    (F : Finset M) (hF : ∀ e ∈ f.support, Finsupp.weight w e ∈ F) :
    ∑ m ∈ F, weightedHomogeneousComponent w m f = f := by
  ext e
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hF e (mem_support_iff.mpr (Ne.symm hne)))

theorem comp_zero_B {σ M : Type*} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (f : MvPolynomial σ ℂ) (m : M)
    (hm : ∀ e ∈ f.support, Finsupp.weight w e ≠ m) : weightedHomogeneousComponent w m f = 0 := by
  ext e
  rw [coeff_weightedHomogeneousComponent]
  change (if Finsupp.weight w e = m then f.coeff e else 0) = 0
  split_ifs with h
  · by_contra hne
    exact hm e (mem_support_iff.mpr hne) h
  · rfl

theorem sep_mem_B {ι T V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (C : T → Module.End ℂ V) (p : ι → T → ℂ) (P : Submodule ℂ V) (hP : ∀ t, ∀ x ∈ P, C t x ∈ P)
    (hsep : ∀ i j, i ≠ j → ∃ t, p i t ≠ p j t) :
    ∀ (F : Finset ι) (y : ι → V), (∀ i ∈ F, ∀ t, C t (y i) = p i t • y i) → ∑ i ∈ F, y i ∈ P →
      ∀ i ∈ F, y i ∈ P := by
  intro F
  induction F using Finset.strongInduction with
  | H F ih =>
    intro y hy hs i0 hi0
    by_cases hall : ∀ i ∈ F, i = i0
    · have hF : F = {i0} := by
        ext i
        simp only [Finset.mem_singleton]
        exact ⟨hall i, fun e => e ▸ hi0⟩
      rw [hF, Finset.sum_singleton] at hs
      exact hs
    push_neg at hall
    obtain ⟨i1, hi1, hne⟩ := hall
    obtain ⟨t, ht⟩ := hsep i1 i0 hne
    let y' : ι → V := fun i => (p i t - p i1 t) • y i
    have hy'1 : y' i1 = 0 := by simp [y']
    have hsum : ∑ i ∈ F.erase i1, y' i = C t (∑ i ∈ F, y i) - p i1 t • ∑ i ∈ F, y i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_erase _ hy'1, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [y']
      rw [hy i hi t, sub_smul]
    have hmem : ∑ i ∈ F.erase i1, y' i ∈ P := by
      rw [hsum]
      exact P.sub_mem (hP t _ hs) (P.smul_mem _ hs)
    have key := ih (F.erase i1) (Finset.erase_ssubset hi1) y'
      (fun i hi u => by
        simp only [y']
        rw [map_smul, hy i (Finset.mem_of_mem_erase hi) u, smul_comm]) hmem
      i0 (Finset.mem_erase.mpr ⟨fun e => hne e.symm, hi0⟩)
    have hd : p i0 t - p i1 t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    have e0 : y i0 = (p i0 t - p i1 t)⁻¹ • y' i0 := by
      simp only [y']
      rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [e0]
    exact P.smul_mem _ key

theorem embGL_apply_B {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) (a b : Fin N) :
    ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) a b =
      if ha : a.1 < n then (if hb : b.1 < n then (g : Matrix (Fin n) (Fin n) ℂ) ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0)
      else (if b.1 < n then 0 else 1) := by
  subst h
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

theorem embGL_diag_B {n N : ℕ} (h : n + 1 = N) (t : Fin n → ℂˣ) :
    ((embGL ℂ n N h (diagGL ℂ n t) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal (dB n N (fun j => (t j : ℂ))) := by
  ext a b
  have ha2 := a.2
  have hb2 := b.2
  rw [embGL_apply_B, Matrix.diagonal_apply]
  by_cases ha : a.1 < n <;> by_cases hb : b.1 < n
  · rw [dite_eq_left ha, dite_eq_left hb]
    show (Matrix.diagonal fun a => (t a : ℂ)) ⟨a.1, ha⟩ ⟨b.1, hb⟩ = _
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp [dB, ha]
    · have hne : (⟨a.1, ha⟩ : Fin n) ≠ ⟨b.1, hb⟩ := fun e => hab (Fin.ext (Fin.mk.inj_iff.mp e))
      simp [hab, hne]
  · have hab : a ≠ b := fun e => hb (e ▸ ha)
    rw [dite_eq_left ha, dite_eq_right hb, if_neg hab]
  · have hab : a ≠ b := fun e => ha (e ▸ hb)
    rw [dite_eq_right ha, if_pos hb, if_neg hab]
  · have hab : a = b := Fin.ext (by omega)
    subst hab
    rw [dite_eq_right ha, if_neg hb, if_pos rfl]
    simp [dB, ha]

theorem torus_mem_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (t : Fin n → ℂˣ) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ W) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N fun j => (t j : ℂ))) f ∈ W := by
  have h1 := hW (diagGL ℂ n t) f hf
  unfold sqAct at h1
  rw [embGL_diag_B, Matrix.diagonal_transpose] at h1
  have hu : detPow ℂ N (embGL ℂ n N h (diagGL ℂ n t)) lam.detShift ≠ 0 := Units.ne_zero _
  have := W.smul_mem (detPow ℂ N (embGL ℂ n N h (diagGL ℂ n t)) lam.detShift)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at this

theorem graded_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ W) (m : Fin n → ℕ) :
    weightedHomogeneousComponent (wnB n N) m f ∈ W := by
  classical
  let F := f.support.image (Finsupp.weight (wnB n N))
  by_cases hm : m ∈ F
  · refine sep_mem_B (T := Fin n → ℂˣ)
      (fun t => (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N fun j => (t j : ℂ)))).toLinearMap)
      (fun m t => chiB (fun j => (t j : ℂ)) m) W (fun t x hx => torus_mem_B h lam W hW t x hx) ?_ F
      (fun m => weightedHomogeneousComponent (wnB n N) m f) ?_ ?_ m hm
    · intro i j hij
      obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := Function.ne_iff.mp hij
      let τ : Fin n → ℂˣ := fun l => if l = k then Units.mk0 (2 : ℂ) two_ne_zero else 1
      have key : ∀ a : Fin n → ℕ, chiB (fun l => ((τ l : ℂˣ) : ℂ)) a = (2 : ℂ) ^ a k := by
        intro a
        unfold chiB
        rw [Finset.prod_eq_single k]
        · simp [τ]
        · intro l _ hl
          simp [τ, hl]
        · simp
      refine ⟨τ, ?_⟩
      show chiB (fun l => ((τ l : ℂˣ) : ℂ)) i ≠ chiB (fun l => ((τ l : ℂˣ) : ℂ)) j
      rw [key, key]
      intro he
      apply hk
      have h2 : ((2 ^ i k : ℕ) : ℂ) = ((2 ^ j k : ℕ) : ℂ) := by push_cast; exact he
      exact Nat.pow_right_injective le_rfl (Nat.cast_injective h2)
    · intro i _ t
      exact rowAct_diag_homog _ _ _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · rw [comp_sum_B]
      · exact hf
      · intro e he
        exact Finset.mem_image_of_mem _ he
  · rw [comp_zero_B]
    · exact W.zero_mem
    · intro e he hw
      exact hm (hw ▸ Finset.mem_image_of_mem _ he)

end PI.WGB
end
end

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

def FiltB {σ : Type*} (ψ : σ → ℕ) (d : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) where
  carrier := {g | ∀ e ∈ g.support, d ≤ Finsupp.weight ψ e}
  add_mem' := by
    intro a b ha hb e he
    classical
    rcases Finset.mem_union.mp (support_add he) with h1 | h1
    exacts [ha e h1, hb e h1]
  zero_mem' := by
    intro e he
    simp at he
  smul_mem' := by
    intro c a ha e he
    exact ha e (support_smul he)

theorem FiltB_mono {σ : Type*} (ψ : σ → ℕ) {d d' : ℕ} (h : d' ≤ d) : FiltB ψ d ≤ FiltB ψ d' :=
  fun _ hp e he => le_trans h (hp e he)

theorem FiltB_mul {σ : Type*} (ψ : σ → ℕ) {d d' : ℕ} {p q : MvPolynomial σ ℂ} (hp : p ∈ FiltB ψ d)
    (hq : q ∈ FiltB ψ d') : p * q ∈ FiltB ψ (d + d') := by
  classical
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul p q he)
  rw [map_add (f := _)]
  exact Nat.add_le_add (hp a ha) (hq b hb)

theorem X_mem_FiltB {σ : Type*} (ψ : σ → ℕ) (v : σ) : (X v : MvPolynomial σ ℂ) ∈ FiltB ψ (ψ v) := by
  intro e he
  rw [support_X, Finset.mem_singleton] at he
  subst he
  rw [Finsupp.weight_single, one_smul]

def GoodB {σ : Type*} (R : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (ψ : σ → ℕ) (p : MvPolynomial σ ℂ) (d : ℕ) :
    Prop :=
  p ∈ FiltB ψ d ∧ R p - p ∈ FiltB ψ (d + 1)

section Good

variable {σ : Type*} (R : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (ψ : σ → ℕ)

theorem GoodB_mul {p q : MvPolynomial σ ℂ} {d d' : ℕ} (hp : GoodB R ψ p d) (hq : GoodB R ψ q d') :
    GoodB R ψ (p * q) (d + d') := by
  refine ⟨FiltB_mul ψ hp.1 hq.1, ?_⟩
  have hRq : R q ∈ FiltB ψ d' := by
    have e : R q = (R q - q) + q := by ring
    rw [e]
    exact Submodule.add_mem _ (FiltB_mono ψ (Nat.le_succ d') hq.2) hq.1
  have e : R (p * q) - p * q = (R p - p) * R q + p * (R q - q) := by
    rw [map_mul]; ring
  rw [e]
  refine Submodule.add_mem _ ?_ ?_
  · have := FiltB_mul ψ hp.2 hRq
    rwa [show d + 1 + d' = d + d' + 1 by ring] at this
  · have := FiltB_mul ψ hp.1 hq.2
    rwa [show d + (d' + 1) = d + d' + 1 by ring] at this

theorem GoodB_one : GoodB R ψ 1 0 :=
  ⟨fun _ _ => Nat.zero_le _, by rw [map_one, sub_self]; exact Submodule.zero_mem _⟩

theorem GoodB_pow {p : MvPolynomial σ ℂ} {d : ℕ} (hp : GoodB R ψ p d) : ∀ k : ℕ, GoodB R ψ (p ^ k) (k * d)
  | 0 => by simpa using GoodB_one R ψ
  | k + 1 => by
    rw [pow_succ, Nat.succ_mul]
    exact GoodB_mul R ψ (GoodB_pow hp k) hp

theorem GoodB_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ) (d : ι → ℕ)
    (h : ∀ i ∈ s, GoodB R ψ (f i) (d i)) : GoodB R ψ (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GoodB_one R ψ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GoodB_mul R ψ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem GoodB_smul (c : ℂ) {p : MvPolynomial σ ℂ} {d : ℕ} (hp : GoodB R ψ p d) : GoodB R ψ (c • p) d := by
  refine ⟨Submodule.smul_mem _ c hp.1, ?_⟩
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_mem _ c hp.2

theorem GoodB_monomial (hX : ∀ v, GoodB R ψ (X v) (ψ v)) (e : σ →₀ ℕ) (c : ℂ) :
    GoodB R ψ (monomial e c) (Finsupp.weight ψ e) := by
  have he : Finsupp.weight ψ e = ∑ v ∈ e.support, e v * ψ v := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    simp [smul_eq_mul]
  rw [monomial_eq, ← smul_eq_C_mul, Finsupp.prod, he]
  exact GoodB_smul R ψ c (GoodB_prod R ψ _ _ _ fun v _ => GoodB_pow R ψ (hX v) (e v))

theorem GoodB_homog (hX : ∀ v, GoodB R ψ (X v) (ψ v)) (g : MvPolynomial σ ℂ) (d : ℕ)
    (hg : IsWeightedHomogeneous ψ g d) : R g - g ∈ FiltB ψ (d + 1) := by
  have e0 : R g - g = ∑ e ∈ g.support, (R (monomial e (AddMonoidAlgebra.coeff g e)) - monomial e (AddMonoidAlgebra.coeff g e)) := by
    conv_lhs => rw [g.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_sub_distrib]
  rw [e0]
  refine Submodule.sum_mem _ fun e he => ?_
  have := (GoodB_monomial R ψ hX e (AddMonoidAlgebra.coeff g e)).2
  rwa [hg (mem_support_iff.mp he)] at this

end Good

theorem rowAct_X_B {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) M (X v) = ∑ b, C (M v.1 b) * X (b, v.2) := by
  simp [Formalism.GradedWeylDivisibility.rowAct]

theorem GoodB_X_tri {n N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hd : ∀ a, M a a = 1)
    (ho : ∀ a b, a ≠ b → M a b ≠ 0 → prowB n N a < prowB n N b) (v : Fin N × Fin N) :
    GoodB (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) M) (psiB n N) (X v) (psiB n N v) := by
  refine ⟨X_mem_FiltB _ v, ?_⟩
  rw [rowAct_X_B, ← Finset.add_sum_erase _ _ (Finset.mem_univ v.1), hd, map_one, one_mul, Prod.mk.eta,
    add_sub_cancel_left]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hb' : b ≠ v.1 := Finset.ne_of_mem_erase hb
  by_cases h0 : M v.1 b = 0
  · rw [h0, map_zero, zero_mul]
    exact Submodule.zero_mem _
  · rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ _ (FiltB_mono _ ?_ (X_mem_FiltB _ (b, v.2)))
    exact ho v.1 b (Ne.symm hb') h0

theorem homog_psi_B {n N : ℕ} (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ)
    (hg : IsWeightedHomogeneous (wnB n N) g m) : IsWeightedHomogeneous (psiB n N) g (PsiB n m) := by
  intro e he
  rw [weight_psiB, hg he]

theorem high_zero_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (k : ℕ)
    (hmax : ∀ g ∈ W, g ≠ 0 → ∀ m, IsWeightedHomogeneous (wnB n N) g m → PsiB n m ≤ k)
    (x : MvPolynomial (Fin N × Fin N) ℂ) (hxW : x ∈ W) (hxF : x ∈ FiltB (psiB n N) (k + 1)) : x = 0 := by
  classical
  rw [← comp_sum_B (wnB n N) x (x.support.image (Finsupp.weight (wnB n N)))
    (fun e he => Finset.mem_image_of_mem _ he)]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_contra hne
  have hle := hmax _ (graded_B h lam W hW x hxW m) hne m (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨e, hc⟩ := MvPolynomial.ne_zero_iff.mp hne
  rw [coeff_weightedHomogeneousComponent] at hc
  split_ifs at hc with hw
  · have h1 := hxF e (mem_support_iff.mpr hc)
    rw [weight_psiB, hw] at h1
    omega
  · exact hc rfl

theorem psi_le_B {n N : ℕ} (e : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (psiB n N) e ≤ n * Finsupp.weight (1 : Fin N × Fin N → ℕ) e := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  simp only [smul_eq_mul, Pi.one_apply, mul_one]
  have : psiB n N v ≤ n := by
    unfold psiB prowB
    split_ifs <;> omega
  calc e v * psiB n N v ≤ e v * n := Nat.mul_le_mul_left _ this
    _ = n * e v := mul_comm _ _

theorem bound_B {n N : ℕ} (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ) (hg : g ∈ nablaSq ℂ N lam)
    (hg0 : g ≠ 0) (m : Fin n → ℕ) (hm : IsWeightedHomogeneous (wnB n N) g m) :
    PsiB n m ≤ n * ∑ s, lam.natW s := by
  obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.mp hg0
  have hhom := dualWeyl_le_homog_B N N lam.natW hg
  rw [mem_homogeneousSubmodule] at hhom
  have h1 : Finsupp.weight (1 : Fin N × Fin N → ℕ) e = ∑ s, lam.natW s := hhom he
  rw [← hm he, ← weight_psiB, ← h1]
  exact psi_le_B e

theorem embGL_unitri_B {n N : ℕ} (h : n + 1 = N) (u : GL (Fin n) ℂ) (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) :
    (∀ a, ((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) a a = 1) ∧
    (∀ a b, a ≠ b → ((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) b a ≠ 0 →
      prowB n N a < prowB n N b) ∧
    (∀ a b, a < b → ((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) b a = 0) := by
  refine ⟨fun a => ?_, fun a b hab hne => ?_, fun a b hab => ?_⟩
  · rw [embGL_apply_B]
    by_cases ha : a.1 < n
    · rw [dite_eq_left ha, dite_eq_left ha]; exact hd _
    · rw [dite_eq_right ha, if_neg ha]
  · have ha2 := a.2
    have hb2 := b.2
    rw [embGL_apply_B] at hne
    by_cases hb : b.1 < n <;> by_cases ha : a.1 < n
    · rw [dite_eq_left hb, dite_eq_left ha] at hne
      have hba : ¬ (a.1 < b.1) := fun hlt => hne (hl _ _ (Fin.mk_lt_mk.mpr hlt))
      have hne' : a.1 ≠ b.1 := fun e => hab (Fin.ext e)
      unfold prowB
      rw [if_pos ha, if_pos hb]
      omega
    · rw [dite_eq_left hb, dite_eq_right ha] at hne; exact absurd rfl hne
    · rw [dite_eq_right hb, if_pos ha] at hne; exact absurd rfl hne
    · exact absurd (Fin.ext (by omega)) hab
  · have ha2 := a.2
    have hb2 := b.2
    rw [embGL_apply_B]
    by_cases hb : b.1 < n <;> by_cases ha : a.1 < n
    · rw [dite_eq_left hb, dite_eq_left ha]
      exact hl _ _ (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hab))
    · exact absurd (lt_trans (Fin.lt_def.mp hab) hb) ha
    · rw [dite_eq_right hb, if_pos ha]
    · have := Fin.lt_def.mp hab
      omega

theorem detPow_unitri_B {n N : ℕ} (h : n + 1 = N) (u : GL (Fin n) ℂ) (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) (c : ℤ) : detPow ℂ N (embGL ℂ n N h u) c = 1 := by
  obtain ⟨h1, _, h3⟩ := embGL_unitri_B h u hl hd
  have hdet : (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => h3 j i hij)]
    simp [h1]
  have hu : Matrix.GeneralLinearGroup.det (embGL ℂ n N h u) = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdet]
    rfl
  unfold detPow
  rw [hu, one_zpow, Units.val_one]

end PI.WGB
