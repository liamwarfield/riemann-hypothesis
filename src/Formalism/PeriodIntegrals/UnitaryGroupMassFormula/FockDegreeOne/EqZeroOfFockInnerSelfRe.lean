module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.RaisingLoweringSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OneDegOfHalves
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.BlockDiagonalPreservesDegree

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.EqZeroOfFockInnerSelfRe
noncomputable section

open MvPolynomial FockH1Action FockRaiseLowInner

namespace PI.FockOneDegW.Inner

export FockRaiseLowInner (fockInner_X_mul fockInner_mul_X fockInner_sum_left fockInner_sum_right
  fockInner_swap fockInner_zero_left fockInner_zero_right fockInner_add_left fockInner_add_right
  fockInner_smul_left fockInner_smul_right fockInner_neg_left fockInner_neg_right fockInner_sub_right
  fockInner_eq_support wt)

section Pos

variable {σ : Type*}

def wtN (α : σ →₀ ℕ) : ℕ := α.prod (fun _ k => k.factorial)

theorem wtN_pos (α : σ →₀ ℕ) : 0 < wtN α := by
  unfold wtN Finsupp.prod
  exact Finset.prod_pos fun i _ ↦ Nat.factorial_pos _

theorem wt_eq_wtN (α : σ →₀ ℕ) : wt α = (wtN α : ℂ) := by
  simp only [wt, wtN, Finsupp.prod, Nat.cast_prod]

theorem fockInner_self_eq (F : MvPolynomial σ ℂ) :
    fockInner F F = ((∑ α ∈ F.support, Complex.normSq (AddMonoidAlgebra.coeff F α) * (wtN α : ℝ) : ℝ) : ℂ) := by
  rw [fockInner_eq_support, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.ofReal_natCast, wt_eq_wtN]

theorem fockInner_self_re_nonneg (F : MvPolynomial σ ℂ) : 0 ≤ (fockInner F F).re := by
  rw [fockInner_self_eq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun α _ ↦ mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fockInner_self_im (F : MvPolynomial σ ℂ) : (fockInner F F).im = 0 := by
  rw [fockInner_self_eq, Complex.ofReal_im]

theorem eq_zero_of_fockInner_self_re (F : MvPolynomial σ ℂ) (h : (fockInner F F).re = 0) :
    F = 0 := by
  rw [fockInner_self_eq, Complex.ofReal_re] at h
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun α _ ↦ mul_nonneg (Complex.normSq_nonneg (AddMonoidAlgebra.coeff F α)) (Nat.cast_nonneg (wtN α)))).1 h
  by_contra hF
  obtain ⟨α, hα⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.1 hF)
  have hc : AddMonoidAlgebra.coeff F α ≠ 0 := MvPolynomial.mem_support_iff.1 hα
  have hne : Complex.normSq (AddMonoidAlgebra.coeff F α) * (wtN α : ℝ) ≠ 0 :=
    mul_ne_zero (Complex.normSq_pos.2 hc).ne' (by exact_mod_cast (wtN_pos α).ne')
  exact hne (hall α hα)

end Pos

end PI.FockOneDegW.Inner

namespace PI.FockOneDegW

open PI.FockOneDegW.Inner in
theorem fock_inner_facts : InnerFacts := by
  intro σ P Q Q' c
  refine ⟨fockInner_add_right _ _ _, fockInner_smul_right _ _ _, fockInner_swap _ _,
    ⟨fockInner_self_im _, fockInner_self_re_nonneg _⟩, fun h ↦ ?_, fun l ↦ fockInner_X_mul l P Q⟩
  exact eq_zero_of_fockInner_self_re P (by rw [h]; simp)

end PI.FockOneDegW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.FockOperatorsKernel
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW

section Ops

theorem omE_same {p q r s : ℕ} (a b : Ix p q) (c : Ix r s) (hab : sameBlock a b)
    (P : Pol p q r s) :
    omE ((a, c) : Ln p q r s) (b, c) P =
      ((if linePos ((a, c) : Ln p q r s) = true then
          X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P else 0)
        - (if linePos ((b, c) : Ln p q r s) = true then 0 else
          X ((b, c) : Ln p q r s) * pderiv ((a, c) : Ln p q r s) P))
      + (if a = b then
          (if linePos ((a, c) : Ln p q r s) = true then (1 / 2 : ℂ) else -(1 / 2)) • P else 0) := by
  classical

  have hl : linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s) := by
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [sameBlock, linePos]
  have hab' : (((a, c) : Ln p q r s) = (b, c)) ↔ a = b := by simp
  rw [FockRL.omE_apply]
  unfold raiB lowB
  rw [hl]
  cases h : linePos ((a, c) : Ln p q r s)
  · by_cases hab2 : a = b
    · subst hab2
      simp [Derivation.leibniz, pderiv_X]
      module
    · have hne : ((a, c) : Ln p q r s) ≠ (b, c) := fun h' => hab2 (hab'.1 h')
      simp [hab2, hne, Derivation.leibniz, pderiv_X, Pi.single_apply, Ne.symm hne]
  · simp [hab']

theorem fockAct1_Eab_apply {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    fockAct1 p q r s (Eab a b) P = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (b, c) P := by
  classical
  rw [FockRL.fockAct1_eq, FockRL.omAct_eq_sum]
  simp [Eab, Matrix.single_apply, Matrix.one_apply, ite_and, Fintype.sum_prod_type,
    LinearMap.sum_apply]

theorem posOp_apply {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    posOp a b P = ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then
      X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P else 0) := by
  unfold posOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem negOp_apply {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    negOp a b P = ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then 0 else
      X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P) := by
  unfold negOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem sum_half {p q r s : ℕ} (a : Ix p q) :
    ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then (1 / 2 : ℂ) else -(1 / 2)) =
      (((kShift r s a : ℚ)) : ℂ) := by
  rcases a with a | a <;> simp [kShift, cPair, linePos, Fintype.sum_sum_type] <;> push_cast <;> ring

theorem fock_operators_kernel : OpsK := by
  intro p q r s a b hab
  apply LinearMap.ext
  intro P
  rw [fockAct1_Eab_apply]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, posOp_apply, negOp_apply]
  rw [Finset.sum_congr rfl fun c _ => omE_same a b c hab P, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  congr 1
  split_ifs with h
  · subst h
    simp only [↓reduceIte, LinearMap.smul_apply, Module.End.one_apply]
    rw [← Finset.sum_smul, sum_half]
  · simp

end Ops

section Harm

theorem minus2_eq {p q r s : ℕ} (Z : Mat r s) (hZ : IsPC Z) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s Z) P = -∑ c : Ix r s, ∑ d : Ix r s, Z c d • lowOp (p := p) (q := q) c d P := by
  classical

  have hside : ∀ (a : Ix p q) (c d : Ix r s), ¬ sameBlock c d →
      linePos ((a, d) : Ln p q r s) = true → linePos ((a, c) : Ln p q r s) = false := by
    intro a c d hcd hd
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      simp_all [sameBlock, linePos]
  have hOpp : FockRL.OppSign (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : Mat p q) Z) := by
    rintro ⟨a, c⟩ ⟨b, d⟩ hne
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at hne
    split_ifs at hne with hab
    · subst hab
      have hcd : ¬ sameBlock c d := fun h => hne (by rw [hZ c d h, mul_zero])
      intro hEq
      rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
        simp_all [sameBlock, linePos]
    · simp at hne
  rw [FockRL.fockAct2_eq, FockRL.omAct_eq_Rop_add_Lop _ hOpp,
    (FockRaiseLowGrade.raisingLoweringSplit _ _ _ (fun d P hP => FockRL.Rop_raise _ d P hP)
      (fun e P => FockRL.Lop_shift _ e P) P).2, FockRL.Lop_apply]

  have hL : ∀ (a : Ix p q) (c : Ix r s),
      (∑ l' : Ln p q r s, if linePos ((a, c) : Ln p q r s) = false ∧ linePos l' = true then
        Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : Mat p q) Z (a, c) l' •
          (-(pderiv ((a, c) : Ln p q r s) (pderiv l' P))) else 0) =
      ∑ d : Ix r s, if linePos ((a, d) : Ln p q r s) = true then
        Z c d • (-(pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P))) else 0 := by
    intro a c
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun d _ => ?_
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
      by_cases hZcd : Z c d = 0
      · simp [hZcd]
      · have hcd : ¬ sameBlock c d := fun h => hZcd (hZ c d h)
        by_cases hd : linePos ((a, d) : Ln p q r s) = true
        · simp [hd, hside a c d hcd hd]
        · simp [hd]
    · intro b _ hba
      refine Finset.sum_eq_zero fun d _ => ?_
      simp [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hba)]
    · simp
  have hR : -∑ c : Ix r s, ∑ d : Ix r s, Z c d • lowOp (p := p) (q := q) c d P =
      ∑ c : Ix r s, ∑ a : Ix p q, ∑ d : Ix r s, if linePos ((a, d) : Ln p q r s) = true then
        Z c d • (-(pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P))) else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [lowOp, LinearMap.sum_apply, Finset.smul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [Fintype.sum_prod_type]
  simp only [hL]
  rw [Finset.sum_comm, hR]

theorem harmIff : HarmIff := by
  intro p q r s P
  unfold Harm2
  constructor
  · intro h c d hcd
    have hZ : IsPC (Matrix.single c d (1 : ℂ) : Mat r s) := by
      intro a b hab
      rw [Matrix.single_apply]
      split_ifs with h'
      · obtain ⟨rfl, rfl⟩ := h'
        exact absurd hab hcd
      · rfl
    have h1 := h _ hZ
    rw [minus2_eq _ hZ] at h1
    simpa [Matrix.single_apply, ite_and] using h1
  · intro h Z hZ
    rw [minus2_eq _ hZ, neg_eq_zero]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    by_cases hcd : sameBlock c d
    · rw [hZ c d hcd, zero_smul]
    · rw [h c d hcd, smul_zero]

end Harm

end PI.FockOneDegW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KroneckerOneRightSwap
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.Swap

open PI.FockOneDegW PI.FockOneDegW.Diag

section Transport

variable {m n : ℕ} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_hwSub_iff (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (ν : Ix m n → ℚ) (w : V) :
    w ∈ hwSub act ν ↔ (∀ a, act (Eab a a) w = ((ν a : ℚ) : ℂ) • w) ∧
      ∀ a b, posC a b → act (Eab a b) w = 0 := by
  unfold hwSub wtSub
  simp [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem isHW_map (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (act' : Mat m n →ₗ[ℂ] Module.End ℂ V')
    (e : V →ₗ[ℂ] V') (he : Function.Injective e) (hint : ∀ X w, act' X (e w) = e (act X w))
    (ν : Ix m n → ℚ) (w : V) (h : IsHW act ν w) : IsHW act' ν (e w) := by
  obtain ⟨h0, hmem⟩ := h
  refine ⟨fun h' => h0 (he (by rw [h', map_zero])), ?_⟩
  rw [mem_hwSub_iff] at hmem ⊢
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [hint, hmem.1 a, map_smul]
  · rw [hint, hmem.2 a b hab, map_zero]

theorem isHW_of_map (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (act' : Mat m n →ₗ[ℂ] Module.End ℂ V')
    (e : V →ₗ[ℂ] V') (he : Function.Injective e) (hint : ∀ X w, act' X (e w) = e (act X w))
    (ν : Ix m n → ℚ) (w : V) (h : IsHW act' ν (e w)) : IsHW act ν w := by
  obtain ⟨h0, hmem⟩ := h
  refine ⟨fun h' => h0 (by rw [h', map_zero]), ?_⟩
  rw [mem_hwSub_iff] at hmem ⊢
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · apply he
    rw [← hint, hmem.1 a, map_smul]
  · apply he
    rw [← hint, hmem.2 a b hab, map_zero]

theorem ofType_map (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (act' : Mat m n →ₗ[ℂ] Module.End ℂ V')
    (e : V →ₗ[ℂ] V') (he : Function.Injective e) (hint : ∀ X w, act' X (e w) = e (act X w))
    (μ : Ix m n → ℚ) (v : V) (h : OfType act μ v) : OfType act' μ (e v) := by
  obtain ⟨W, hW, hv, hK, hty⟩ := h
  refine ⟨W.map e, ?_, Submodule.mem_map_of_mem hv, ?_, ?_⟩
  · exact Module.Finite.map W e
  · intro X hX w' hw'
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hw'
    rw [hint]
    exact Submodule.mem_map_of_mem (hK X hX w hw)
  · intro ν w' hw' hhw
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hw'
    exact hty ν w hw (isHW_of_map act act' e he hint ν w hhw)

end Transport

section Rename

variable {σ τ : Type*} (f : σ ≃ τ)

theorem hc_rename (φ : MvPolynomial σ ℂ) (k : ℕ) :
    homogeneousComponent k (rename f φ) = rename f (homogeneousComponent k φ) := by
  conv_lhs => rw [← sum_homogeneousComponent φ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  have h : ∀ i, homogeneousComponent k (rename f (homogeneousComponent i φ)) =
      if k = i then rename f (homogeneousComponent i φ) else 0 := fun i =>
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
      ((homogeneousComponent_isHomogeneous i φ).rename_isHomogeneous))
  simp_rw [h]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simp only [Finset.mem_range] at hk; omega), map_zero]

theorem minusPart_rename (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (hAB : ∀ Q, B (rename f Q) = rename f (A Q))
    (P : MvPolynomial σ ℂ) : rename f (minusPart A P) = minusPart B (rename f P) := by
  unfold minusPart
  have hfin : Function.HasFiniteSupport
      (fun d : ℕ => homogeneousComponent d (A (homogeneousComponent (d + 2) P))) := by
    refine (Set.finite_Iio P.totalDegree).subset ?_
    intro d hd
    by_contra h
    apply hd
    simp only [Set.mem_Iio, not_lt] at h
    simp only [homogeneousComponent_eq_zero (d + 2) P (by omega), map_zero]
  rw [map_finsum (rename f) hfin]
  refine finsum_congr fun d => ?_
  rw [← hc_rename, ← hAB, ← hc_rename]

end Rename

variable {p q r s : ℕ}

abbrev sw (p q r s : ℕ) : Ln p q r s ≃ Ln r s p q := Equiv.prodComm _ _

theorem linePos_sw (l : Ln p q r s) : linePos (sw p q r s l) = linePos l := by
  rcases l with ⟨a | a, b | b⟩ <;> rfl

theorem rename_X_mul (l : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (X l * P) = X (sw p q r s l) * rename (sw p q r s) P := by
  rw [map_mul, rename_X]

theorem rename_pderiv (l : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (pderiv l P) = pderiv (sw p q r s l) (rename (sw p q r s) P) := (pderiv_rename (sw p q r s).injective l P).symm

theorem rename_lowB (l : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (lowB l P) = lowB (sw p q r s l) (rename (sw p q r s) P) := by
  unfold lowB
  rw [linePos_sw]
  split_ifs
  · exact rename_pderiv l P
  · exact rename_X_mul l P

theorem rename_raiB (l : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (raiB l P) = raiB (sw p q r s l) (rename (sw p q r s) P) := by
  unfold raiB
  rw [linePos_sw]
  split_ifs
  · exact rename_X_mul l P
  · show rename _ (-(pderiv l P)) = -(pderiv (sw p q r s l) (rename _ P))
    rw [map_neg, rename_pderiv]

theorem rename_omE (l l' : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (omE l l' P) =
      omE (sw p q r s l) (sw p q r s l') (rename (sw p q r s) P) := by
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add (f := _), rename_raiB, rename_lowB]
  congr 1
  by_cases h : l = l'
  · subst h
    simp
  · have h' : sw p q r s l ≠ sw p q r s l' := fun e => h ((sw p q r s).injective e)
    simp [h, h']

theorem rename_omAct (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    rename (sw p q r s) (omAct p q r s M P) =
      omAct r s p q (M.submatrix (sw p q r s).symm (sw p q r s).symm) (rename (sw p q r s) P) := by
  simp only [omAct, LinearMap.sum_apply, LinearMap.smulRight_apply,
    Matrix.entryLinearMap_apply, LinearMap.smul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, rename_omE]
  refine Fintype.sum_equiv (sw p q r s) _ _ (fun l => ?_)
  refine Fintype.sum_equiv (sw p q r s) _ _ (fun l' => ?_)
  simp [Matrix.submatrix_apply]

theorem kronecker_one_left_swap (X : Mat p q) :
    ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s) X).submatrix
        (sw p q r s).symm (sw p q r s).symm =
      (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat r s) X := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, mul_comm]

theorem kronecker_one_right_swap (Y : Mat r s) :
    ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat p q) Y).submatrix
        (sw p q r s).symm (sw p q r s).symm =
      (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat p q) Y := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, mul_comm]

theorem rename_fockAct1 (X : Mat p q) (P : Pol p q r s) :
    rename (sw p q r s) (fockAct1 p q r s X P) = fockAct2 r s p q X (rename (sw p q r s) P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct, kronecker_one_left_swap]

theorem rename_fockAct2 (Y : Mat r s) (P : Pol p q r s) :
    rename (sw p q r s) (fockAct2 p q r s Y P) = fockAct1 r s p q Y (rename (sw p q r s) P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct, kronecker_one_right_swap]

theorem rename_sw_injective (p q r s : ℕ) :
    Function.Injective (rename (R := ℂ) (sw p q r s)) := rename_injective _ (sw p q r s).injective

def swL (p q r s : ℕ) : Pol p q r s →ₗ[ℂ] Pol r s p q := (rename (sw p q r s)).toLinearMap

theorem fock_swap_groups : Swap := by
  intro h1 p q r s μ P hP hOT hh
  have hint : ∀ (X : Mat r s) (w : Pol p q r s),
      fockAct1 r s p q X (swL p q r s w) = swL p q r s (fockAct2 p q r s X w) :=
    fun X w => (rename_fockAct2 X w).symm
  have hOT' := ofType_map (fockAct2 p q r s) (fockAct1 r s p q) (swL p q r s)
    (rename_sw_injective p q r s) hint μ P hOT
  have hP' : rename (sw p q r s) P ≠ 0 := fun h =>
    hP (rename_sw_injective p q r s (by rw [h, map_zero]))
  have hh' : ∀ Z : Mat p q, IsPC Z → minusPart (fockAct2 r s p q Z) (rename (sw p q r s) P) = 0 := by
    intro Z hZ
    rw [← minusPart_rename (sw p q r s) (fockAct1 p q r s Z) (fockAct2 r s p q Z)
      (fun Q => (rename_fockAct1 Z Q).symm) P, hh Z hZ, map_zero]
  obtain ⟨d, hd, hmem⟩ := h1 r s p q μ (rename (sw p q r s) P) hP' hOT' hh'
  refine ⟨d, hd, ?_⟩
  have hback : rename (sw p q r s).symm (rename (sw p q r s) P) = P := by
    rw [rename_rename]
    simp
  rw [← hback]
  exact (mem_homogeneousSubmodule _ _).2
    (((mem_homogeneousSubmodule _ _).1 hmem).rename_isHomogeneous)

theorem hwHarmDeg2 (hT : HwHarmDeg) (p q r s : ℕ) (μ : Ix r s → ℚ) (e : ℕ) (v : Pol p q r s)
    (hv : v ∈ homog (Ix p q × Ix r s) e) (hw : IsHW (fockAct2 p q r s) μ v)
    (hh : ∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) v = 0) :
    (e : ℚ) = degW (cPair p q) μ := by
  have hint : ∀ (X : Mat r s) (w : Pol p q r s),
      fockAct1 r s p q X (swL p q r s w) = swL p q r s (fockAct2 p q r s X w) :=
    fun X w => (rename_fockAct2 X w).symm
  have hw' := isHW_map (fockAct2 p q r s) (fockAct1 r s p q) (swL p q r s)
    (rename_sw_injective p q r s) hint μ v hw
  have hv' : rename (sw p q r s) v ∈ homog (Ix r s × Ix p q) e :=
    (mem_homogeneousSubmodule _ _).2 (((mem_homogeneousSubmodule _ _).1 hv).rename_isHomogeneous)
  have hh' : Harm2 (rename (sw p q r s) v) := by
    intro Z hZ
    rw [← minusPart_rename (sw p q r s) (fockAct1 p q r s Z) (fockAct2 r s p q Z)
      (fun Q => (rename_fockAct1 Z Q).symm) v, hh Z hZ, map_zero]
  exact hT r s p q μ e (rename (sw p q r s) v) hv' hw' hh'

end PI.FockOneDegW.Swap
end
end
