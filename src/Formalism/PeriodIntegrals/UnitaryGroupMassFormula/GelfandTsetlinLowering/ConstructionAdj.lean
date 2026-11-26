module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitPowerNormScale.NormUnitsZpowSq

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.AdjBase
noncomputable section

namespace PI.WGL.Adj

open Formalism.BasicNotions MvPolynomial

theorem fockF_eq_sum_of_subset {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS ?_
  intro m _ hm
  simp only [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fockF_add_left {σ : Type} [DecidableEq σ] (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  rw [fockF_eq_sum_of_subset (f + f') g _ MvPolynomial.support_add,
    fockF_eq_sum_of_subset f g _ Finset.subset_union_left,
    fockF_eq_sum_of_subset f' g _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem fockF_add_right {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (g + g') = Formalism.REAL.fockF f g + Formalism.REAL.fockF f g' := by
  unfold Formalism.REAL.fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]; ring

theorem den_pos {N : ℕ} (lam : DomWeight N) :
    0 < (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re ∧
      (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).im = 0 :=
  Formalism.GradedWeylDivisibility.fockPos _ _ (Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW)

theorem den_eq {N : ℕ} (lam : DomWeight N) :
    Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam) =
      (((Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [(den_pos lam).2])

theorem nf_eq {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f g = Formalism.REAL.fockF f g /
      (((Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re : ℝ) : ℂ) := by
  unfold normFock; rw [← den_eq]

theorem nf_herm {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam g f = star (normFock lam f g) := by
  rw [nf_eq, nf_eq, Formalism.GradedWeylDivisibility.fockHerm, star_div₀, Complex.star_def, Complex.conj_ofReal]

theorem nf_add_left {N : ℕ} (lam : DomWeight N) (f f' g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (f + f') g = normFock lam f g + normFock lam f' g := by
  unfold normFock; rw [fockF_add_left, add_div]

theorem nf_add_right {N : ℕ} (lam : DomWeight N) (f g g' : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (g + g') = normFock lam f g + normFock lam f g' := by
  unfold normFock; rw [fockF_add_right, add_div]

theorem nf_smul_left {N : ℕ} (lam : DomWeight N) (c : ℂ) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (c • f) g = c * normFock lam f g := by
  unfold normFock; rw [PI.WHw.bC_smul_left, mul_div_assoc]

theorem nf_smul_right {N : ℕ} (lam : DomWeight N) (c : ℂ) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (c • g) = star c * normFock lam f g := by
  unfold normFock; rw [PI.WHw.bC_smul_right, mul_div_assoc]

def nfL {N : ℕ} (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun f := normFock lam f g
  map_add' f f' := nf_add_left lam f f' g
  map_smul' c f := by simp [nf_smul_left]

theorem nfL_apply {N : ℕ} (lam : DomWeight N) (g f : MvPolynomial (Fin N × Fin N) ℂ) :
    nfL lam g f = normFock lam f g := rfl

theorem nf_sum_smul_left {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (∑ k ∈ S, a k • v k) g = ∑ k ∈ S, a k * normFock lam (v k) g := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← nfL_apply, map_sum]
  simp [nfL_apply]

theorem nf_sum_smul_right {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (∑ k ∈ S, a k • v k) = ∑ k ∈ S, star (a k) * normFock lam f (v k) := by
  rw [nf_herm, nf_sum_smul_left, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', ← nf_herm]

theorem nf_sub_right {N : ℕ} (lam : DomWeight N) (f g g' : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (g - g') = normFock lam f g - normFock lam f g' := by
  rw [nf_herm, ← nfL_apply, map_sub, star_sub, nfL_apply, nfL_apply, ← nf_herm, ← nf_herm]

theorem nf_zero_right {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f 0 = 0 := by
  have := nf_smul_right lam 0 f 0
  simpa using this

theorem nf_self_im {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    (normFock lam f f).im = 0 := by
  rw [nf_eq, Complex.div_ofReal_im]
  by_cases hf : f = 0
  · subst hf; simp [Formalism.REAL.fockF]
  · rw [(Formalism.GradedWeylDivisibility.fockPos _ f hf).2, zero_div]

theorem nf_self_re_pos {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ≠ 0) :
    0 < (normFock lam f f).re := by
  rw [nf_eq, Complex.div_ofReal_re]
  exact div_pos (Formalism.GradedWeylDivisibility.fockPos _ f hf).1 (den_pos lam).1

theorem nf_self_re_nonneg {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    0 ≤ (normFock lam f f).re := by
  by_cases hf : f = 0
  · subst hf; rw [nf_zero_right]; simp
  · exact (nf_self_re_pos lam f hf).le

theorem nf_self_eq_zero {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (h : normFock lam f f = 0) : f = 0 := by
  by_contra hf
  have := nf_self_re_pos lam f hf
  rw [h] at this; simp at this

theorem nf_self_eq_re {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f f = (((normFock lam f f).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [nf_self_im])

theorem nf_extremal {N : ℕ} (lam : DomWeight N) :
    normFock lam (extremal ℂ N lam) (extremal ℂ N lam) = 1 := by
  unfold normFock
  refine div_self ?_
  intro h0
  have := (den_pos lam).1
  rw [h0] at this; simp at this

def nfCore {N : ℕ} (lam : DomWeight N) : InnerProductSpace.Core ℂ (MvPolynomial (Fin N × Fin N) ℂ) where
  inner x y := normFock lam y x
  conj_inner_symm x y := by
    show starRingEnd ℂ (normFock lam x y) = normFock lam y x
    rw [starRingEnd_apply, ← nf_herm]
  re_inner_nonneg x := nf_self_re_nonneg lam x
  add_left x y z := nf_add_right lam z x y
  smul_left x y r := by
    show normFock lam y (r • x) = starRingEnd ℂ r * normFock lam y x
    rw [nf_smul_right, starRingEnd_apply]
  definite x hx := nf_self_eq_zero lam x hx

theorem nf_cauchy_schwarz {N : ℕ} (lam : DomWeight N) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    ‖normFock lam y x‖ * ‖normFock lam x y‖ ≤ (normFock lam x x).re * (normFock lam y y).re := by
  letI : PreInnerProductSpace.Core ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nfCore lam).toCore
  exact InnerProductSpace.Core.inner_mul_inner_self_le x y

def frameCore (n : ℕ) (sg : DomWeight n) : InnerProductSpace.Core ℂ (nablaSq ℂ n sg) where
  inner x y := normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) x
  conj_inner_symm x y := by
    show starRingEnd ℂ (normFock sg (x : MvPolynomial (Fin n × Fin n) ℂ) y) = normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) x
    rw [starRingEnd_apply, ← nf_herm]
  re_inner_nonneg x := nf_self_re_nonneg sg x
  add_left x y z := by
    show normFock sg (z : MvPolynomial (Fin n × Fin n) ℂ) ((x + y : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ) = _
    rw [Submodule.coe_add, nf_add_right]
  smul_left x y r := by
    show normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) ((r • x : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ) = _
    rw [Submodule.coe_smul, nf_smul_right, starRingEnd_apply]
  definite x hx := by
    have := nf_self_eq_zero sg (x : MvPolynomial (Fin n × Fin n) ℂ) hx
    exact Subtype.ext this

theorem exists_frame (n : ℕ) (sg : DomWeight n) :
    ∃ (d : ℕ) (b : Fin d → MvPolynomial (Fin n × Fin n) ℂ), (∀ k, b k ∈ nablaSq ℂ n sg) ∧
      ∀ s ∈ nablaSq ℂ n sg, s = ∑ k, normFock sg s (b k) • b k := by
  letI : NormedAddCommGroup (nablaSq ℂ n sg) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (frameCore n sg)
  letI : InnerProductSpace ℂ (nablaSq ℂ n sg) := InnerProductSpace.ofCore (frameCore n sg).toCore
  haveI : FiniteDimensional ℂ (nablaSq ℂ n sg) := PI.WHw.bC_fd n n sg.natW
  let b := stdOrthonormalBasis ℂ (nablaSq ℂ n sg)
  refine ⟨Module.finrank ℂ (nablaSq ℂ n sg), fun k => (b k : MvPolynomial (Fin n × Fin n) ℂ),
    fun k => (b k).2, fun s hs => ?_⟩
  have h1 := congrArg Subtype.val (b.sum_repr' ⟨s, hs⟩)
  rw [Submodule.coe_sum] at h1
  exact h1.symm

end PI.WGL.Adj
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.SqActMemNabla
noncomputable section

namespace PI.WGL.Adj

open Formalism.BasicNotions MvPolynomial

def gStar {N : ℕ} (g : GL (Fin N) ℂ) : GL (Fin N) ℂ where
  val := Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ)
  inv := Matrix.conjTranspose ((g⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  val_inv := by rw [← Matrix.conjTranspose_mul]; simp
  inv_val := by rw [← Matrix.conjTranspose_mul]; simp

theorem gStar_val {N : ℕ} (g : GL (Fin N) ℂ) :
    ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ) := rfl

theorem gStar_gStar {N : ℕ} (g : GL (Fin N) ℂ) : gStar (gStar g) = g := by
  ext i j; simp [gStar_val]

def cU (a : ℂˣ) : ℂˣ := Units.map (starRingEnd ℂ : ℂ →* ℂ) a

theorem cU_zpow_val (a : ℂˣ) (e : ℤ) : ((cU a ^ e : ℂˣ) : ℂ) = star ((a ^ e : ℂˣ) : ℂ) := by
  unfold cU
  rw [← map_zpow, Units.coe_map]
  rfl

theorem embGL_gStar {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    embGL ℂ n N h (gStar g) = gStar (embGL ℂ n N h g) := by
  have key : ∀ p q : Fin n ⊕ Fin 1,
      Matrix.fromBlocks (Matrix.conjTranspose (g : Matrix (Fin n) (Fin n) ℂ)) 0 0 1 p q =
        (starRingEnd ℂ) (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 1 q p) := by
    rintro (p | p) (q | q)
    · simp [Matrix.conjTranspose_apply]
    · simp
    · simp
    · have hp : p = q := Subsingleton.elim _ _
      subst hp; simp
  ext i j
  simp only [embGL, blkHom, gStar_val, Matrix.conjTranspose_apply]
  simp
  exact key _ _

theorem lastGL_cU (N : ℕ) (a : ℂˣ) : lastGL ℂ N (cU a) = gStar (lastGL ℂ N a) := by
  ext i j
  simp only [lastGL, diagGL, gStar_val, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; split_ifs <;> simp [cU]
  · have hji : j ≠ i := fun e => hij e.symm
    simp [hij, hji]

theorem detPow_gStar {N : ℕ} (g : GL (Fin N) ℂ) (k : ℤ) :
    detPow ℂ N (gStar g) k = star (detPow ℂ N g k) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, star_zpow₀]
  congr 1
  simp [gStar_val, Matrix.det_conjTranspose]

theorem sqAct_mem_nabla {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ nablaSq ℂ N lam) : sqAct ℂ N lam g f ∈ nablaSq ℂ N lam := by
  unfold sqAct
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)

theorem sqAct_smul {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (c : ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g (c • f) = c • sqAct ℂ N lam g f := by
  unfold sqAct
  rw [map_smul, smul_comm]

theorem nf_sqAct_adj {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (sqAct ℂ N lam g x) y = normFock lam x (sqAct ℂ N lam (gStar g) y) := by
  have hm : Matrix.conjTranspose (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) =
      Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j; simp [gStar_val, Matrix.conjTranspose_apply]
  have hf : Formalism.REAL.fockF (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) x) y =
      Formalism.REAL.fockF x (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) y) := by
    rw [Formalism.GradedWeylDivisibility.fockRowAdj, hm]
  unfold sqAct
  rw [nf_smul_left, nf_smul_right, detPow_gStar, star_star]
  unfold normFock
  rw [hf]

theorem nf_sqAct_adj' {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam x (sqAct ℂ N lam g y) = normFock lam (sqAct ℂ N lam (gStar g) x) y := by
  rw [nf_sqAct_adj, gStar_gStar]

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by have := lam.anti hij; linarith)

theorem extremal_mem {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ∈ nablaSq ℂ N lam :=
  Formalism.GradedWeylDivisibility.hwMem ℂ N N le_rfl lam.natW (natW_anti lam)

theorem extremal_ne {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW

end PI.WGL.Adj
end
end

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial PI.WGL.Adj

theorem adjointBr_of (h3 : PI.HwIrred) (h5 : PI.SchurFock) (hN : Numbers) (hX : XiFacts) :
    AdjointBr := by
  intro n N h lam sg hI io hio hext hlast
  obtain ⟨hioV, hioEq⟩ := hio
  obtain ⟨hc0, hcB, -⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, hxiV, -, -, -, hxiU⟩ := hX n N h lam sg hI
  obtain ⟨d, b, hbV, hexp⟩ := exists_frame n sg
  have hdel_sg : delSq ℂ n sg = nablaSq ℂ n sg := ((h3 n sg).1).symm
  have hdel_lam : delSq ℂ N lam = nablaSq ℂ N lam := ((h3 N lam).1).symm

  let br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    ∑ k, (nfL lam (io (b k))).smulRight (b k)
  have hbr : ∀ f, br f = ∑ k, normFock lam f (io (b k)) • b k := by
    intro f
    simp [br, LinearMap.sum_apply, LinearMap.smulRight_apply, nfL_apply]
  have hbrV : ∀ f, br f ∈ nablaSq ℂ n sg := by
    intro f
    rw [hbr]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hbV k)
  have hT : ∀ s ∈ nablaSq ℂ n sg, ∀ f, normFock lam (io s) f = normFock sg s (br f) := by
    intro s hs f
    have e := hexp s hs
    calc normFock lam (io s) f = normFock lam (io (∑ k, normFock sg s (b k) • b k)) f := by rw [← e]
      _ = ∑ k, normFock sg s (b k) * normFock lam (io (b k)) f := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          simp only [map_smul]
          rw [nf_sum_smul_left]
      _ = normFock sg s (br f) := by
          rw [hbr, nf_sum_smul_right]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← nf_herm, mul_comm]
  have hsep : ∀ x y, x ∈ nablaSq ℂ n sg → y ∈ nablaSq ℂ n sg →
      (∀ s ∈ nablaSq ℂ n sg, normFock sg s x = normFock sg s y) → x = y := by
    intro x y hx hy hxy
    have hd : x - y ∈ nablaSq ℂ n sg := Submodule.sub_mem _ hx hy
    have h0 : normFock sg (x - y) (x - y) = 0 := by rw [nf_sub_right, hxy _ hd, sub_self]
    exact sub_eq_zero.mp (nf_self_eq_zero sg _ h0)

  have hB4 : ∀ (g : GL (Fin n) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ),
      br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f) := by
    intro g f
    refine hsep _ _ (hbrV _) (sqAct_mem_nabla sg g _ (hbrV f)) fun s hs => ?_
    have hs' : sqAct ℂ n sg (gStar g) s ∈ nablaSq ℂ n sg := sqAct_mem_nabla sg _ s hs
    rw [← hT s hs, nf_sqAct_adj' lam (embGL ℂ n N h g) (io s) f, ← embGL_gStar, ← hioEq _ s hs,
      hT _ hs', nf_sqAct_adj' sg g s (br f)]
  have hB5 : ∀ (a : ℂˣ) (f : MvPolynomial (Fin N × Fin N) ℂ),
      br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f := by
    intro a f
    refine hsep _ _ (hbrV _) (Submodule.smul_mem _ _ (hbrV f)) fun s hs => ?_
    rw [← hT s hs, nf_sqAct_adj' lam (lastGL ℂ N a) (io s) f, ← lastGL_cU, hlast _ s hs, nf_smul_left,
      nf_smul_right, hT s hs, cU_zpow_val]

  have hextV : extremal ℂ n sg ∈ nablaSq ℂ n sg := extremal_mem sg
  have hext0 : extremal ℂ n sg ≠ 0 := extremal_ne sg
  let Tm : Module.End ℂ (nablaSq ℂ n sg) :=
    LinearMap.codRestrict (nablaSq ℂ n sg) ((br ∘ₗ io) ∘ₗ (nablaSq ℂ n sg).subtype) (fun x => hbrV _)
  haveI : FiniteDimensional ℂ (nablaSq ℂ n sg) := PI.WHw.bC_fd n n sg.natW
  haveI : Nontrivial (nablaSq ℂ n sg) :=
    ⟨⟨⟨_, hextV⟩, 0, fun h0 => hext0 (congrArg Subtype.val h0)⟩⟩
  obtain ⟨κ, hκ⟩ := Module.End.exists_eigenvalue Tm
  obtain ⟨v, hv⟩ := hκ.exists_hasEigenvector
  have hv1 : br (io (v : MvPolynomial (Fin n × Fin n) ℂ)) = κ • (v : MvPolynomial (Fin n × Fin n) ℂ) := by
    have := Module.End.HasEigenvector.apply_eq_smul hv
    exact congrArg Subtype.val this
  have hv0 : (v : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0 := fun h0 => hv.2 (Subtype.ext h0)
  let U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    nablaSq ℂ n sg ⊓ LinearMap.ker (br ∘ₗ io - κ • LinearMap.id)
  have hmemU : ∀ x, x ∈ U ↔ x ∈ nablaSq ℂ n sg ∧ br (io x) = κ • x := by
    intro x
    simp only [U, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hUst : ∀ (g : GL (Fin n) ℂ), ∀ x ∈ U, sqAct ℂ n sg g x ∈ U := by
    intro g x hx
    rw [hmemU] at hx ⊢
    refine ⟨sqAct_mem_nabla sg g x hx.1, ?_⟩
    rw [hioEq g x hx.1, hB4, hx.2, sqAct_smul]
  have hall : ∀ s ∈ nablaSq ℂ n sg, br (io s) = κ • s := by
    rcases (h3 n sg).2.1 U inf_le_left hUst with hU | hU
    · exfalso
      have hvU : (v : MvPolynomial (Fin n × Fin n) ℂ) ∈ U := (hmemU _).2 ⟨v.2, hv1⟩
      rw [hU, Submodule.mem_bot] at hvU
      exact hv0 hvU
    · intro s hs
      rw [← hU] at hs
      exact ((hmemU s).1 hs).2

  set K := normFock lam (io (extremal ℂ n sg)) (io (extremal ℂ n sg)) with hKdef
  have hnorm : ∀ s ∈ nablaSq ℂ n sg, normFock lam (io s) (io s) = K * normFock sg s s := by
    have hK : star κ = K := by
      have := hT _ hextV (io (extremal ℂ n sg))
      rw [hall _ hextV, nf_smul_right, nf_extremal, mul_one] at this
      exact this.symm
    intro s hs
    rw [hT s hs, hall s hs, nf_smul_right, hK]
  have hKre : K.re = ‖((cBr h lam sg : ℤ) : ℂ)‖ ^ 2 * (normFock lam (xi ℂ h lam sg) (xi ℂ h lam sg)).re := by
    rw [hKdef, hext, PI.GTS.re_normFock_smul]
  have hKreal : K = ((K.re : ℝ) : ℂ) := by rw [hKdef]; exact nf_self_eq_re lam _
  have hcpos : 0 < ‖((cBr h lam sg : ℤ) : ℂ)‖ := by
    rw [norm_pos_iff]; exact_mod_cast hc0
  have hKpos : 0 < K.re := by
    rw [hKre]; exact mul_pos (pow_pos hcpos 2) (nf_self_re_pos lam _ hxi0)
  have hKle : K.re ≤ brBd h lam sg ^ 2 := by
    have hc2 : ‖((cBr h lam sg : ℤ) : ℂ)‖ ^ 2 ≤ cBd h lam sg ^ 2 := by
      have hcn : ‖((cBr h lam sg : ℤ) : ℂ)‖ = |((cBr h lam sg : ℤ) : ℝ)| := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      rw [hcn]
      exact pow_le_pow_left₀ (abs_nonneg _) hcB 2
    have hSF := h5 N lam (xi ℂ h lam sg) hxiV hxiU
    have hbb : brBd h lam sg ^ 2 = cBd h lam sg ^ 2 * (Module.finrank ℂ (delSq ℂ N lam) : ℝ) := by
      unfold brBd; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hKre, hbb]
    exact mul_le_mul hc2 hSF (nf_self_re_nonneg lam _) (sq_nonneg _)
  refine ⟨?_, br, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro s hs
    rw [hnorm s hs, hKreal, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_right hKle (nf_self_re_nonneg sg s)
  ·
    intro f _
    rw [hdel_sg]; exact hbrV f
  ·
    refine ⟨io (extremal ℂ n sg), ?_, ?_⟩
    · rw [hdel_lam]; exact hioV _ hextV
    · intro h0
      have := hT _ hextV (io (extremal ℂ n sg))
      rw [h0, nf_zero_right] at this
      rw [← hKdef] at this
      rw [this] at hKpos
      simp at hKpos
  ·
    intro g f _
    exact hB4 g f
  ·
    intro a f _
    exact hB5 a f
  ·
    intro f _
    set u := br f with hu
    have huV : u ∈ nablaSq ℂ n sg := hbrV f
    have hTu : normFock lam (io u) f = normFock sg u u := hT u huV f
    have hCS := nf_cauchy_schwarz lam (io u) f
    have hnA : ‖normFock sg u u‖ = (normFock sg u u).re := by
      conv_lhs => rw [nf_self_eq_re sg u]
      exact Complex.norm_of_nonneg (nf_self_re_nonneg sg u)
    rw [nf_herm lam (io u) f, hTu, norm_star, hnA, hnorm u huV, hKreal, Complex.re_ofReal_mul] at hCS
    have hA := nf_self_re_nonneg sg u
    have hF := nf_self_re_nonneg lam f
    have hAle : (normFock sg u u).re ≤ K.re * (normFock lam f f).re := by
      rcases hA.lt_or_eq with hApos | hA0
      · refine le_of_mul_le_mul_left ?_ hApos
        nlinarith
      · rw [← hA0]; exact mul_nonneg hKpos.le hF
    calc (normFock sg u u).re ≤ K.re * (normFock lam f f).re := hAle
      _ ≤ brBd h lam sg ^ 2 * (normFock lam f f).re := mul_le_mul_of_nonneg_right hKle hF
  ·
    intro s hs f _
    exact hT s hs f

end PI.WGL
