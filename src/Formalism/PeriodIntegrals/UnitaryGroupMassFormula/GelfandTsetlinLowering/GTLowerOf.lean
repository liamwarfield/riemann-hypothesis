module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.NumMore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Capelli2_2
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionLift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionAdj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionBrInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.IoXiHw

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionIo
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem ioExists_of (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) : IoExists :=
  ioExists_of' h3 h4 hx

end PI.WGL
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionXi
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.EvalInitMinorNormLe
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.RowsZStrictMono
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.MultisetProdNormLeOne
noncomputable section

namespace PI.WGL.XiU

open Matrix

theorem normSq_sum_eq {N : ℕ} (u : Fin N → ℂ) :
    star u ⬝ᵥ u = ((∑ a, Complex.normSq (u a) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]

theorem normSq_sum_mulVec {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (w : Fin N → ℂ) : ∑ a, Complex.normSq ((x *ᵥ w) a) = ∑ b, Complex.normSq (w b) := by
  apply Complex.ofReal_injective
  rw [← normSq_sum_eq, ← normSq_sum_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hx,
    Matrix.one_mulVec]

theorem sum_comp_le {N s : ℕ} (I : Fin s → Fin N) (hI : Function.Injective I) (f : Fin N → ℝ)
    (hf : ∀ a, 0 ≤ f a) : ∑ p, f (I p) ≤ ∑ a, f a := by
  rw [← Finset.sum_image (fun p _ q _ h => hI h)]
  exact Finset.sum_le_univ_sum_of_nonneg hf

theorem sum_comp_eq {N s : ℕ} {M : Type*} [AddCommMonoid M] (I : Fin s → Fin N) (hI : Function.Injective I)
    (f : Fin N → M) (hf : ∀ b, b ∉ Set.range I → f b = 0) : ∑ b, f b = ∑ p, f (I p) := by
  rw [← Finset.sum_image (fun p _ q _ h => hI h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  apply hf
  rintro ⟨p, rfl⟩
  exact hb (Finset.mem_image_of_mem _ (Finset.mem_univ p))

theorem sub_contract {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I J : Fin s → Fin N) (hI : Function.Injective I) (hJ : Function.Injective J) (v : Fin s → ℂ) :
    ∑ p, Complex.normSq (((Matrix.of fun p q => x (I p) (J q)) *ᵥ v) p) ≤ ∑ q, Complex.normSq (v q) := by
  set w : Fin N → ℂ := Function.extend J v 0 with hw
  have hwJ : ∀ q, w (J q) = v q := fun q => hJ.extend_apply v 0 q
  have hw0 : ∀ b, b ∉ Set.range J → w b = 0 := by
    intro b hb
    rw [hw, Function.extend_apply' _ _ _ hb]
    rfl
  have hmv : ∀ p, ((Matrix.of fun p q => x (I p) (J q)) *ᵥ v) p = (x *ᵥ w) (I p) := by
    intro p
    have hs := sum_comp_eq J hJ (fun b => x (I p) b * w b) (fun b hb => by simp [hw0 b hb])
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [hs]
    simp only [hwJ]
  have hnorm : ∑ b, Complex.normSq (w b) = ∑ q, Complex.normSq (v q) := by
    have hs := sum_comp_eq J hJ (fun b => Complex.normSq (w b)) (fun b hb => by simp [hw0 b hb])
    rw [hs]
    simp only [hwJ]
  calc ∑ p, Complex.normSq (((Matrix.of fun p q => x (I p) (J q)) *ᵥ v) p)
      = ∑ p, Complex.normSq ((x *ᵥ w) (I p)) := by simp only [hmv]
    _ ≤ ∑ a, Complex.normSq ((x *ᵥ w) a) :=
        sum_comp_le I hI _ (fun a => Complex.normSq_nonneg _)
    _ = ∑ b, Complex.normSq (w b) := normSq_sum_mulVec x hx w
    _ = ∑ q, Complex.normSq (v q) := hnorm

theorem multiset_prod_norm_le_one (m : Multiset ℂ) (h : ∀ μ ∈ m, ‖μ‖ ≤ 1) : ‖m.prod‖ ≤ 1 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have ha := h a (by simp)
    have hs := ih (fun μ hμ => h μ (by simp [hμ]))
    exact mul_le_one₀ ha (norm_nonneg _) hs

theorem det_sub_norm_le_one {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I J : Fin s → Fin N) (hI : Function.Injective I) (hJ : Function.Injective J) :
    ‖(Matrix.of fun p q => x (I p) (J q)).det‖ ≤ 1 := by
  set A := Matrix.of fun p q => x (I p) (J q) with hA
  rw [Matrix.det_eq_prod_roots_charpoly]
  apply multiset_prod_norm_le_one
  intro μ hμ
  have hroot : A.charpoly.IsRoot μ := (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).1 hμ
  have hspec : μ ∈ spectrum ℂ A := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hspec
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hspec
  have hAv : A *ᵥ v = μ • v := by
    first
    | rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at hv
    | rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
        Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv.symm
  have hc := sub_contract x hx I J hI hJ v
  rw [← hA, hAv] at hc
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, ← Finset.mul_sum] at hc
  have hpos : 0 < ∑ q, Complex.normSq (v q) := by
    obtain ⟨q, hq⟩ := Function.ne_iff.1 hv0
    exact lt_of_lt_of_le (Complex.normSq_pos.2 hq)
      (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (v i)) (Finset.mem_univ q))
  have h1 : Complex.normSq μ ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have h2 := Complex.normSq_eq_norm_sq μ
  nlinarith [norm_nonneg μ]

end PI.WGL.XiU
end
end

noncomputable section

namespace PI.WGL.XiA

open Formalism.BasicNotions MvPolynomial

theorem embGL_apply {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) (a b : Fin N) :
    ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) a b =
      if ha : a.1 < n then (if hb : b.1 < n then (g : Matrix (Fin n) (Fin n) ℂ) ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0)
      else (if b.1 < n then 0 else 1) := by
  unfold embGL blkHom
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hl : ∀ (x : Fin N) (hx : x.1 < n),
      finSumFinEquiv.symm (Fin.cast h.symm x) = (Sum.inl ⟨x.1, hx⟩ : Fin n ⊕ Fin 1) := by
    intro x hx
    have hc : Fin.cast h.symm x = Fin.castAdd 1 ⟨x.1, hx⟩ := Fin.ext rfl
    rw [hc, finSumFinEquiv_symm_apply_castAdd]
  have hr : ∀ (x : Fin N), ¬ x.1 < n →
      finSumFinEquiv.symm (Fin.cast h.symm x) = (Sum.inr 0 : Fin n ⊕ Fin 1) := by
    intro x hx
    have hxN := x.isLt
    have hc : Fin.cast h.symm x = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp; omega)
    rw [hc, finSumFinEquiv_symm_apply_natAdd]
  by_cases ha : a.1 < n <;> by_cases hb : b.1 < n
  · rw [hl a ha, hl b hb]
    simp [ha, hb]
  · rw [hl a ha, hr b hb]
    simp [ha, hb]
  · rw [hr a ha, hl b hb]
    simp [ha, hb]
  · rw [hr a ha, hr b hb]
    simp [ha, hb]

theorem rowAct_initMinor {N s : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (I : Fin s → Fin N) (hI : StrictMono I)
    (hs : s ≤ N) (hG : ∀ a b : Fin N, a < b → G b a = 0)
    (hcl : ∀ p b, G b (I p) ≠ 0 → b ∈ Set.range I) :
    Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs) =
      C (∏ p, G (I p) (I p)) * Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs := by
  classical
  set B : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun p p' => G (I p') (I p) with hB
  have hmat : ((Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) G.transpose : MvPolynomial (Fin N × Fin N) ℂ →+* MvPolynomial (Fin N × Fin N) ℂ)).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) =
      (C : ℂ →+* MvPolynomial (Fin N × Fin N) ℂ).mapMatrix B *
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, hB,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.transpose_apply]
    rw [XiU.sum_comp_eq I hI.injective]
    intro b hb
    have : G b (I p) = 0 := by
      by_contra hne
      exact hb (hcl p b hne)
    simp [this]
  have hBdet : B.det = ∏ p, G (I p) (I p) := by
    rw [Matrix.det_of_isLowerTriangular B]
    · rfl
    · intro p p' hpp'
      exact hG _ _ (hI (by simpa using hpp'))
  have hdet := RingHom.map_det ((Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) G.transpose :
      MvPolynomial (Fin N × Fin N) ℂ →+* MvPolynomial (Fin N × Fin N) ℂ))
    (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ))
  rw [RingHom.coe_coe] at hdet
  show Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)).det =
    C (∏ p, G (I p) (I p)) * (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)).det
  rw [hdet, hmat, Matrix.det_mul, ← RingHom.map_det, hBdet]

theorem lpMinor_eq {N : ℕ} (s : ℕ) (hr : s ≤ N) (hn : s ≤ N) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) s hr hn = Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (Fin.castLE hr) hn := rfl

theorem rowsZ_strictMono {n N : ℕ} (h : n + 1 = N) (i : Fin n) : StrictMono (rowsZ h i) := by
  unfold rowsZ
  intro p q hpq
  have hpq' := Fin.lt_def.mp hpq
  have hq := q.isLt
  have hi := i.isLt
  simp only
  split_ifs with h1 h2 h2 <;> simp only [Fin.lt_def] <;> omega

def GoodG (n : ℕ) {N : ℕ} (h : n + 1 = N) (G : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (∀ a b : Fin N, a < b → G b a = 0) ∧ (∀ b : Fin N, b.1 ≠ n → G b ⟨n, by omega⟩ = 0)

def xiScal {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (G : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∏ i : Fin n, (∏ p : Fin (i.1 + 1), G (Fin.castLE (by omega) p) (Fin.castLE (by omega) p)) ^ (aa h lam sg i).toNat *
    (∏ p : Fin (i.1 + 1), G (rowsZ h i p) (rowsZ h i p)) ^ (bb h lam sg i).toNat

theorem rowAct_xi {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (G : Matrix (Fin N) (Fin N) ℂ) (hG : GoodG n h G) :
    Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (xi ℂ h lam sg) = C (xiScal h lam sg G) * xi ℂ h lam sg := by
  have hlp : ∀ i : Fin n, Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose
      (Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) (i.1 + 1) (by omega) (by omega)) =
      C (∏ p : Fin (i.1 + 1), G (Fin.castLE (by omega) p) (Fin.castLE (by omega) p)) *
        Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) (i.1 + 1) (by omega) (by omega) := by
    intro i
    rw [lpMinor_eq]
    apply rowAct_initMinor G _ (Fin.strictMono_castLE _) _ hG.1
    intro p b hb
    have hle : b ≤ Fin.castLE (by omega) p := by
      by_contra hlt
      push Not at hlt
      exact hb (hG.1 _ _ hlt)
    refine ⟨⟨b.1, ?_⟩, Fin.ext rfl⟩
    have := p.2
    simp only [Fin.le_def, Fin.coe_castLE] at hle
    omega
  have hrz : ∀ i : Fin n, Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (rowsZ h i) (by omega)) =
      C (∏ p : Fin (i.1 + 1), G (rowsZ h i p) (rowsZ h i p)) *
        Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (rowsZ h i) (by omega) := by
    intro i
    apply rowAct_initMinor G _ (rowsZ_strictMono h i) _ hG.1
    intro p b hb
    by_cases hp : p.1 = i.1
    · have e : rowsZ h i p = ⟨n, by omega⟩ := by
        simp only [rowsZ, hp, if_true]; ext; simp; omega
      rw [e] at hb
      have hbn : b.1 = n := by
        by_contra hne
        exact hb (hG.2 b hne)
      refine ⟨⟨i.1, by omega⟩, ?_⟩
      simp only [rowsZ, if_true]
      ext; simp; omega
    · have e : rowsZ h i p = ⟨p.1, by omega⟩ := by
        simp only [rowsZ, hp, if_false]
      rw [e] at hb
      have hle : b.1 ≤ p.1 := by
        by_contra hlt
        push Not at hlt
        exact hb (hG.1 _ _ (by simpa [Fin.lt_def] using hlt))
      have hpi : p.1 < i.1 := by have := p.2; omega
      refine ⟨⟨b.1, by omega⟩, ?_⟩
      have : b.1 ≠ i.1 := by omega
      simp only [rowsZ, this, if_false]
  unfold xi xiScal
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, map_pow, hlp i, hrz i, mul_pow, mul_pow, map_mul, map_pow, map_pow]
  ring

theorem initMinor_mem {N s : ℕ} (I : Fin s → Fin N) (hs : s ≤ N) :
    Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (fun t : Fin N => if t.1 < s then 1 else 0) := by
  have hm := Formalism.GradedWeylDivisibility.bidetMem ℂ N N 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : Formalism.GradedWeylDivisibility.bideterminant ℂ (r := N) (n := N) (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) =
      Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs := by
    simp [Formalism.GradedWeylDivisibility.bideterminant]
  have e2 : Formalism.GradedWeylDivisibility.shapeDeg (n := N) (fun _ : Fin 1 => s) = fun t : Fin N => if t.1 < s then 1 else 0 := by
    funext t
    by_cases ht : t.1 < s <;> simp [Formalism.GradedWeylDivisibility.shapeDeg, ht]
  rwa [e1, e2] at hm

private theorem mul_mem_dualWeyl_complex {N : ℕ} (ν μ : Fin N → ℕ) (f g : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) (hg : g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N μ) :
    f * g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν + μ) := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf hg ⊢
  rw [Submodule.mem_inf] at hf hg ⊢
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hf1 hg1 ⊢
    exact hf1.mul hg1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at hf2 hg2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, hf2 l j hlj, hg2 l j hlj]

private theorem one_mem_dualWeyl_complex {N : ℕ} :
    (1 : MvPolynomial (Fin N × Fin N) ℂ) ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N 0 := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact MvPolynomial.isWeightedHomogeneous_one _ _
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero]
    intro l j hlj
    rw [map_one, map_one]

theorem pow_mem {N : ℕ} (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) (k : ℕ) : f ^ k ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (k • ν) := by
  induction k with
  | zero => simpa using one_mem_dualWeyl_complex (N := N)
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_dualWeyl_complex _ _ _ _ ih hf

theorem prod_mem {N : ℕ} {ι : Type*} (s : Finset ι) (ν : ι → Fin N → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) ℂ)
    (hf : ∀ i ∈ s, f i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν i)) :
    ∏ i ∈ s, f i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_dualWeyl_complex (N := N)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_complex _ _ _ _ (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem tele_sum (ℓ : ℕ → ℤ) (n t : ℕ) (ht : t ≤ n) :
    ∑ i ∈ Finset.range n, (if t ≤ i then ℓ i - ℓ (i + 1) else 0) = ℓ t - ℓ n := by
  induction n with
  | zero =>
    have ht0 : t = 0 := by omega
    subst ht0
    simp
  | succ n ih =>
    rcases Nat.lt_or_ge n t with h | h
    · have htn : t = n + 1 := by omega
      subst htn
      rw [Finset.sum_eq_zero]
      · ring
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [if_neg (by omega)]
    · rw [Finset.sum_range_succ, ih h, if_pos h]
      ring

end PI.WGL.XiA
end
end

noncomputable section

namespace PI.WGL.XiB

open Formalism.BasicNotions MvPolynomial

theorem teleA {G : Type*} [AddCommGroup G] (n : ℕ) (P : ℕ → G) (hP0 : P 0 = 0) (w : G) (ℓ σ : ℕ → ℤ) :
    ℓ n • (P n + w) + ∑ i ∈ Finset.range n, ((σ i - ℓ (i + 1)) • P (i + 1) + (ℓ i - σ i) • (P i + w)) =
    (∑ j ∈ Finset.range n, σ j • (P (j + 1) - P j)) +
      ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) • w := by
  induction n with
  | zero => simp [hP0]
  | succ n ih =>
    rw [Finset.sum_range_succ, eq_sub_of_add_eq' ih]
    simp only [Finset.sum_range_succ]
    simp only [smul_add, smul_sub, add_smul, sub_smul]
    abel

theorem teleM {G : Type*} [CommGroup G] (n : ℕ) (P : ℕ → G) (hP0 : P 0 = 1) (w : G) (ℓ σ : ℕ → ℤ) :
    (P n * w) ^ ℓ n * ∏ i ∈ Finset.range n, (P (i + 1) ^ (σ i - ℓ (i + 1)) * (P i * w) ^ (ℓ i - σ i)) =
    (∏ j ∈ Finset.range n, (P (j + 1) / P j) ^ σ j) *
      w ^ ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) := by
  have h := teleA (G := Additive G) n (fun i => Additive.ofMul (P i)) (by simp [hP0])
    (Additive.ofMul w) ℓ σ
  have h2 := congrArg Additive.toMul h
  simpa [toMul_sum, toMul_zsmul, toMul_sub, toMul_add, mul_zpow] using h2

theorem diag_scalar {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (s : Fin N → ℂˣ) :
    detPow ℂ N (diagGL ℂ N s) lam.detShift * XiA.xiScal h lam sg (Matrix.diagonal fun a => (s a : ℂ)) =
      (((∏ j : Fin n, s ⟨j.1, by omega⟩ ^ sg.w j) * s ⟨n, by omega⟩ ^ degZ lam sg : ℂˣ) : ℂ) := by
  subst h
  set v : ℕ → ℂˣ := fun p => if hp : p < n + 1 then s ⟨p, hp⟩ else 1 with hv
  set P : ℕ → ℂˣ := fun k => ∏ p ∈ Finset.range k, v p with hP
  set ℓ : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0 with hℓ
  set σ : ℕ → ℤ := fun k => if hk : k < n then sg.w ⟨k, hk⟩ else 0 with hσ
  set w : ℂˣ := s ⟨n, by omega⟩ with hw
  have hPa : ∀ k (hk : k ≤ n + 1), ∏ p : Fin k, s (Fin.castLE hk p) = P k := by
    intro k hk
    show ∏ p : Fin k, s (Fin.castLE hk p) = ∏ p ∈ Finset.range k, v p
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    have : p.1 < n + 1 := by omega
    simp only [hv, dif_pos this]
    rfl
  have hPs : ∀ k, P (k + 1) = P k * v k := fun k => by simp only [hP, Finset.prod_range_succ]
  have hdet : Matrix.GeneralLinearGroup.det (diagGL ℂ (n + 1) s) = P n * w := by
    ext
    have e := hPa (n + 1) le_rfl
    simp only [Fin.castLE_rfl, id] at e
    rw [hPs, show v n = w by simp [hv, hw]] at e
    rw [← e]
    simp [diagGL, Matrix.det_diagonal]
  have hshift : lam.detShift = ℓ n := by
    simp [DomWeight.detShift, hℓ]
  have hx : XiA.xiScal rfl lam sg (Matrix.diagonal fun a => (s a : ℂ)) =
      ((∏ i ∈ Finset.range n, (P (i + 1) ^ (σ i - ℓ (i + 1)) * (P i * w) ^ (ℓ i - σ i)) : ℂˣ) : ℂ) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => P (i + 1) ^ (σ i - ℓ (i + 1)) * (P i * w) ^ (ℓ i - σ i)) n]
    unfold XiA.xiScal
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hi := i.2
    have hA : 0 ≤ aa rfl lam sg i := by have := (hI i).2; unfold aa; omega
    have hB : 0 ≤ bb rfl lam sg i := by have := (hI i).1; unfold bb; omega
    have e1 : ∏ p : Fin (i.1 + 1), (Matrix.diagonal fun a => (s a : ℂ)) (Fin.castLE (by omega) p)
        (Fin.castLE (by omega) p) = ((P (i.1 + 1) : ℂˣ) : ℂ) := by
      rw [← hPa (i.1 + 1) (by omega), Units.coe_prod]
      simp [Matrix.diagonal_apply_eq]
    have e2 : ∏ p : Fin (i.1 + 1), (Matrix.diagonal fun a => (s a : ℂ)) (rowsZ rfl i p) (rowsZ rfl i p) =
        ((P i.1 * w : ℂˣ) : ℂ) := by
      simp only [Matrix.diagonal_apply_eq]
      rw [Fin.prod_univ_castSucc, ← hPa i.1 (by omega), Units.val_mul, Units.coe_prod]
      congr 1
      · refine Finset.prod_congr rfl (fun p _ => ?_)
        have : (Fin.castSucc p).1 ≠ i.1 := by simp; omega
        simp only [rowsZ, this, if_false]
        rfl
      · simp only [rowsZ, Fin.val_last, if_true, hw]
        congr 2
    rw [e1, e2, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB]
    congr 2
    · simp [aa, hσ, hℓ, hi]
    · simp [bb, hσ, hℓ, hi]
  have htarget : ((∏ j : Fin n, s ⟨j.1, by omega⟩ ^ sg.w j) * s ⟨n, by omega⟩ ^ degZ lam sg : ℂˣ) =
      (∏ j ∈ Finset.range n, (P (j + 1) / P j) ^ σ j) *
        w ^ ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) := by
    congr 1
    · rw [← Fin.prod_univ_eq_prod_range (fun j => (P (j + 1) / P j) ^ σ j) n]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      have hj := j.2
      rw [hPs, mul_div_cancel_left]
      simp [hv, hσ, hj, show j.1 < n + 1 by omega]
    · congr 1
      unfold degZ wsum
      rw [← Fin.sum_univ_eq_sum_range ℓ (n + 1), ← Fin.sum_univ_eq_sum_range σ n]
      congr 1
      · refine Finset.sum_congr rfl (fun p _ => ?_)
        simp only [hℓ]; rw [dif_pos p.2]
      · refine Finset.sum_congr rfl (fun p _ => ?_)
        simp only [hσ]; rw [dif_pos p.2]
  unfold detPow
  rw [hx, hdet, hshift, htarget, ← Units.val_mul, teleM n P (by simp [hP]) w ℓ σ]

theorem sqAct_diag_xi {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (s : Fin N → ℂˣ) :
    sqAct ℂ N lam (diagGL ℂ N s) (xi ℂ h lam sg) =
      (((∏ j : Fin n, s ⟨j.1, by omega⟩ ^ sg.w j) * s ⟨n, by omega⟩ ^ degZ lam sg : ℂˣ) : ℂ) • xi ℂ h lam sg := by
  have hG : XiA.GoodG n h (Matrix.diagonal fun a => (s a : ℂ)) := by
    unfold XiA.GoodG
    refine ⟨fun a b hab => ?_, fun b hb => ?_⟩
    · exact Matrix.diagonal_apply_ne _ (ne_of_lt hab).symm
    · apply Matrix.diagonal_apply_ne
      intro e
      apply hb
      rw [e]
  have hcoe : ((diagGL ℂ N s : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal fun a => (s a : ℂ) := by
    ext i j
    unfold diagGL
    simp [Matrix.diagonal_apply]
  unfold sqAct
  rw [hcoe, XiA.rowAct_xi h lam sg _ hG, MvPolynomial.C_mul', smul_smul, diag_scalar h lam sg hI s]

theorem embGL_diag {n N : ℕ} (h : n + 1 = N) (t : Fin n → ℂˣ) :
    embGL ℂ n N h (diagGL ℂ n t) = diagGL ℂ N (fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1) := by
  apply Units.ext
  ext a b
  rw [XiA.embGL_apply]
  unfold diagGL
  simp only [Matrix.diagonal_apply]
  by_cases ha : a.1 < n
  · by_cases hb : b.1 < n
    · simp only [ha, hb, dite_true]
      by_cases hab : a = b
      · subst hab
        simp
      · have hab' : (⟨a.1, ha⟩ : Fin n) ≠ ⟨b.1, hb⟩ := fun e => hab (Fin.ext (Fin.mk.inj_iff.mp e))
        simp [hab, hab']
    · have hab : a ≠ b := fun e => hb (e ▸ ha)
      simp [ha, hb, hab]
  · by_cases hb : b.1 < n
    · have hab : a ≠ b := fun e => ha (e ▸ hb)
      simp [ha, hb, hab]
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      simp [ha]

theorem xi_torus {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : Fin n → ℂˣ) :
    sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) (xi ℂ h lam sg) =
      ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) • xi ℂ h lam sg := by
  rw [embGL_diag, sqAct_diag_xi h lam sg hI]
  simp

theorem xi_last {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (a : ℂˣ) :
    sqAct ℂ N lam (lastGL ℂ N a) (xi ℂ h lam sg) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • xi ℂ h lam sg := by
  have hL : lastGL ℂ N a = diagGL ℂ N (fun b => if b.1 < n then 1 else a) := by
    apply Units.ext
    ext i j
    unfold lastGL diagGL
    simp [Matrix.diagonal_apply]
    split_ifs <;> simp_all <;> omega
  rw [hL, sqAct_diag_xi h lam sg hI]
  simp

theorem xi_unitri {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (g : GL (Fin n) ℂ) (hlow : ∀ i j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0)
    (hdiag : ∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) :
    sqAct ℂ N lam (embGL ℂ n N h g) (xi ℂ h lam sg) = xi ℂ h lam sg := by
  set G := ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hGdef
  have hlowG : ∀ a b : Fin N, a < b → G b a = 0 := by
    intro a b hab
    have hab' := Fin.lt_def.mp hab
    rw [hGdef, XiA.embGL_apply]
    by_cases hb : b.1 < n
    · have ha : a.1 < n := by omega
      rw [dif_pos hb, dif_pos ha]
      exact hlow _ _ (Fin.mk_lt_mk.mpr hab')
    · have hbN := b.isLt
      rw [dite_eq_right hb, if_pos (by omega)]
  have hcol : ∀ b : Fin N, b.1 ≠ n → G b ⟨n, by omega⟩ = 0 := by
    intro b hb
    have hbN := b.isLt
    have hb' : b.1 < n := by omega
    rw [hGdef, XiA.embGL_apply, dif_pos hb', dite_eq_right (lt_irrefl n)]
  have hdg : ∀ a : Fin N, G a a = 1 := by
    intro a
    rw [hGdef, XiA.embGL_apply]
    by_cases ha : a.1 < n
    · rw [dif_pos ha, dif_pos ha]
      exact hdiag ⟨a.1, ha⟩
    · rw [dite_eq_right ha, if_neg ha]
  have hgood : XiA.GoodG n h G := by
    unfold XiA.GoodG
    exact ⟨hlowG, hcol⟩
  have hdet : G.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hlowG j i hij)]
    simp [hdg]
  have hxs : XiA.xiScal h lam sg G = 1 := by
    unfold XiA.xiScal
    simp [hdg]
  unfold sqAct
  rw [XiA.rowAct_xi h lam sg G hgood, hxs, MvPolynomial.C_1, one_mul]
  have hdu : Matrix.GeneralLinearGroup.det (embGL ℂ n N h g) = 1 := by
    apply Units.ext
    rw [Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, ← hGdef, hdet]
  unfold detPow
  rw [hdu]
  simp

private theorem mul_mem_dualWeyl_complex_add {N : ℕ} (ν μ : Fin N → ℕ) (f g : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) (hg : g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N μ) :
    f * g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν + μ) := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf hg ⊢
  rw [Submodule.mem_inf] at hf hg ⊢
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hf1 hg1 ⊢
    exact hf1.mul hg1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at hf2 hg2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, hf2 l j hlj, hg2 l j hlj]

theorem nu_eq {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : Fin N) :
    (∑ i : Fin n, ((aa h lam sg i).toNat * (if t.1 < i.1 + 1 then 1 else 0) +
      (bb h lam sg i).toNat * (if t.1 < i.1 + 1 then 1 else 0)) : ℕ) = lam.natW t := by
  subst h
  set ℓ : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0 with hℓ
  apply Nat.cast_injective (R := ℤ)
  have hnat : ((lam.natW t : ℕ) : ℤ) = lam.w t - lam.w ⟨n, by omega⟩ := by
    have hle : t ≤ ⟨n, by omega⟩ := by rw [Fin.le_def]; have := t.2; simp; omega
    have := lam.anti hle
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos (show 0 < n + 1 by omega)]
    rw [Int.toNat_of_nonneg (by simp; omega)]
    simp
  rw [hnat]
  push_cast
  rw [Finset.sum_congr rfl (g := fun i : Fin n => (fun k : ℕ => if t.1 ≤ k then ℓ k - ℓ (k + 1) else 0) i.1)]
  · rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if t.1 ≤ k then ℓ k - ℓ (k + 1) else 0) n,
      XiA.tele_sum ℓ n t.1 (by have := t.2; omega)]
    simp only [hℓ, dif_pos t.2, dif_pos (show n < n + 1 by omega)]
  · intro i _
    have hi := i.2
    have hA : 0 ≤ aa rfl lam sg i := by have := (hI i).2; unfold aa; omega
    have hB : 0 ≤ bb rfl lam sg i := by have := (hI i).1; unfold bb; omega
    rw [Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB]
    simp only [hℓ, dif_pos (show i.1 < n + 1 by omega), dif_pos (show i.1 + 1 < n + 1 by omega)]
    by_cases hti : t.1 ≤ i.1
    · rw [if_pos (by omega), if_pos hti]
      unfold aa bb
      ring
    · rw [if_neg (by omega), if_neg hti]
      ring

theorem xi_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg) :
    xi ℂ h lam sg ∈ nablaSq ℂ N lam := by
  unfold nablaSq
  have key : lam.natW = ∑ i : Fin n, ((aa h lam sg i).toNat • (fun t : Fin N => if t.1 < i.1 + 1 then 1 else 0) +
      (bb h lam sg i).toNat • (fun t : Fin N => if t.1 < i.1 + 1 then 1 else 0)) := by
    funext t
    rw [← nu_eq h lam sg hI t]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  unfold xi
  rw [key]
  refine XiA.prod_mem Finset.univ _ _ (fun i _ => ?_)
  apply mul_mem_dualWeyl_complex_add
  · apply XiA.pow_mem
    rw [XiA.lpMinor_eq]
    exact XiA.initMinor_mem _ _
  · apply XiA.pow_mem
    exact XiA.initMinor_mem _ _

theorem initMinor_ne {N s : ℕ} (I : Fin s → Fin N) (hI : Function.Injective I) (hs : s ≤ N) :
    Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs ≠ 0 := by
  classical
  intro h0
  let v : Fin N × Fin N → ℂ := fun w => if ∃ p : Fin s, I p = w.1 ∧ Fin.castLE hs p = w.2 then 1 else 0
  have h1 := congrArg (MvPolynomial.eval v) h0
  rw [map_zero] at h1
  unfold Formalism.GradedWeylDivisibility.initMinor at h1
  rw [RingHom.map_det] at h1
  have hM : (MvPolynomial.eval v).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.one_apply, v]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos ⟨p, rfl, rfl⟩, if_pos rfl]
    · rw [if_neg hpq, if_neg]
      rintro ⟨p', h2, h3⟩
      have h4 : p' = p := hI h2
      subst h4
      apply hpq
      have h5 := congrArg Fin.val h3
      simp only [Fin.coe_castLE] at h5
      exact Fin.ext h5
  rw [hM, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem xi_ne {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : xi ℂ h lam sg ≠ 0 := by
  unfold xi
  rw [Finset.prod_ne_zero_iff]
  intro i _
  apply mul_ne_zero
  · apply pow_ne_zero
    rw [XiA.lpMinor_eq]
    exact initMinor_ne _ (Fin.castLE_injective _) _
  · apply pow_ne_zero
    exact initMinor_ne _ (XiA.rowsZ_strictMono h i).injective _

theorem eval_initMinor_norm_le {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I : Fin s → Fin N) (hI : Function.Injective I) (hs : s ≤ N) :
    ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs)‖ ≤ 1 := by
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det]
  have : (MvPolynomial.eval fun v : Fin N × Fin N => x v.1 v.2).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) =
      Matrix.of fun p q => x (I p) (Fin.castLE hs q) := by
    ext p q; simp
  rw [this]
  exact XiU.det_sub_norm_le_one x hx I (Fin.castLE hs) hI (Fin.castLE_injective hs)

theorem xi_unitary {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) (xi ℂ h lam sg)‖ ≤ 1 := by
  unfold xi
  rw [map_prod, norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
  intro i _
  rw [map_mul, map_pow, map_pow, norm_mul, norm_pow, norm_pow]
  apply mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ?_) (pow_nonneg (norm_nonneg _) _)
    (pow_le_one₀ (norm_nonneg _) ?_)
  · rw [XiA.lpMinor_eq]
    exact eval_initMinor_norm_le x hx _ (Fin.castLE_injective _) _
  · exact eval_initMinor_norm_le x hx _ (XiA.rowsZ_strictMono h i).injective _

end PI.WGL.XiB
end
end

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem xi_coefficient_facts : XiFacts := by
  intro n N h lam sg hI
  refine ⟨XiB.xi_ne h lam sg, XiB.xi_mem h lam sg hI, ?_, ?_, ?_, ?_⟩
  · intro g hlow hdiag
    exact XiB.xi_unitri h lam sg g hlow hdiag
  · intro t
    exact XiB.xi_torus h lam sg hI t
  · intro a
    exact XiB.xi_last h lam sg hI a
  · intro x hx
    exact XiB.xi_unitary h lam sg x hx

end PI.WGL
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionNum
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem numbers_dominant_large : Numbers := by
  intro n N h lam sg hI
  exact ⟨PI.GTNum.cBr_ne_zero h lam sg hI, PI.GTNum.abs_cBr_le_cBd h lam sg hI,
    PI.GTNum.degZ_eq h lam sg⟩

theorem scalar_vanishing_criterion : ZScalarVanish := by
  intro n N h lam sg mu hsg hmu hne hw
  have hsum : (∑ i : Fin n, mu.w i) = ∑ i : Fin n, sg.w i := by
    unfold wsum at hw
    exact hw
  have hD : D0 h lam mu = D0 h lam sg := by
    unfold D0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ sg.w i := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  have hmem : mu.w i ∈ Rset h lam sg i := by
    have hm := PI.GTNum.sg_mem_R h lam mu hmu i
    unfold Rset at hm ⊢
    rw [hD] at hm
    exact hm
  unfold zScalar
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, hmem⟩)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  ring

end PI.WGL
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Assembly
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem ioIntegral_of (hZ : CapelliZ) (hL : LiftMod) (hV : ZScalarVanish) : IoIntegral := by
  intro n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨Z, hZi, hZa⟩ := hZ n N h lam sg hI
  obtain ⟨m, hm, hd⟩ := hL n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨f', hf', hZf⟩ := hZi m hm
  refine ⟨f', hf', ?_⟩
  have hsC : MvPolynomial.map (Int.castRingHom ℂ) s ∈ nablaSq ℂ n sg :=
    Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW s hs
  have hO : OtherPart h lam sg ≤ LinearMap.ker Z := by
    unfold OtherPart
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun hne => iSup_le fun hw =>
      iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [LinearMap.mem_ker, hZa mu hmu φ hφ t ht, hV n N h lam sg mu hI hmu hne hw, Int.cast_zero, zero_smul]
  have h0 := hO hd
  rw [LinearMap.mem_ker, map_sub, hZf, hZa sg hI io0 hE _ hsC] at h0
  have hz : zScalar h lam sg sg = cBr h lam sg := rfl
  rw [hz] at h0
  rw [map_smul]
  exact (sub_eq_zero.mp h0).symm

theorem sqAct_smul {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) (c : ℂ)
    (x : MvPolynomial (Fin k × Fin k) ℂ) : sqAct ℂ k mu g (c • x) = c • sqAct ℂ k mu g x := by
  rw [sqAct, sqAct, map_smul, smul_comm]

theorem gTLower_of_steps (hN : Numbers) (hX : XiFacts) (hE : IoExists) (hP4 : IoIntegral)
    (hA : AdjointBr) (hB : BrIntegral) : PI.GTLower := by
  intro n N h lam sg hI
  obtain ⟨hc0, hcB, hdeg⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, -⟩ := hX n N h lam sg hI
  obtain ⟨io0, ⟨hE1, hE2⟩, hx, hW⟩ := hE n N h lam sg hI
  let c : ℂ := ((cBr h lam sg : ℤ) : ℂ)
  let io := c • io0
  have hio : ∀ x, io x = c • io0 x := fun x => rfl
  have I2 : ∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam := fun s hs =>
    Submodule.smul_mem _ _ (hE1 s hs)
  have I3 : ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
      io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s) := by
    intro g s hs
    rw [hio, hio, hE2 g s hs, sqAct_smul]
  have I4 : io (extremal ℂ n sg) = c • xi ℂ h lam sg := by rw [hio, hx]
  have I5 : LastWeight lam sg io := by
    intro a s hs
    rw [hio, sqAct_smul, hW a s hs, smul_comm]
  have I1 : ∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
      io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f := by
    intro s hs
    obtain ⟨f, hf, hf'⟩ := hP4 n N h lam sg hI io0 ⟨hE1, hE2⟩ hx hW s hs
    exact ⟨f, hf, by rw [hio, ← map_smul]; exact hf'⟩
  obtain ⟨I6, br, hrest, hT⟩ := hA n N h lam sg hI io ⟨I2, I3⟩ I4 I5
  have B1 := hB n N h lam sg hI io br I1 I2 hrest.1 hT
  exact ⟨hc0, hcB, hxi0, hdeg, io, br, ⟨I1, I2, I3, I4, I5, I6⟩, ⟨B1, hrest⟩, hT⟩

end PI.WGL
end
end

noncomputable section

namespace PI.WGL

theorem gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) (h3 : PI.HwIrred) (h4 : PI.GTBranch)
    (h5 : PI.SchurFock) : PI.GTLower := by
  have hN : Numbers := numbers_dominant_large
  have hX : XiFacts := xi_coefficient_facts
  have hZ : CapelliZ := capelli_scalar_identity
  have hV : ZScalarVanish := scalar_vanishing_criterion
  exact gTLower_of_steps hN hX (ioExists_of h3 h4 hX)
    (ioIntegral_of hZ (liftMod_of h3 h4 hZ hV hN hX) hV)
    (adjointBr_of h3 h5 hN hX) (brIntegral_of h2 h3)

end PI.WGL
