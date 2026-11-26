module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IteratedDerivativeColumnCaseInt
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivFsum
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivDeterminantPowerColumnSum
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDeterminantPowerZeroInt
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivDeterminantPowerCornerInt
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetColumnPerturbation
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetDFin
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem isymm (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin n → F) (π : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℂ n G x (u ∘ π) = iteratedFDeriv ℂ n G x u :=
  hG.contDiffAt.iteratedFDeriv_comp_perm u π

theorem ipeel0 (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u 0)) x (fun k => u k.succ) := by
  have hfd : ContDiffAt ℂ n (fderiv ℂ G) x := (hG.contDiffAt (n := ω)).fderiv_right le_top
  have happ := (ContinuousLinearMap.apply ℂ ℂ (u 0)).iteratedFDeriv_comp_left hfd (i := n) le_rfl
  have hfun : (fun y => fderiv ℂ G y (u 0)) = (ContinuousLinearMap.apply ℂ ℂ (u 0)) ∘ fderiv ℂ G := rfl
  rw [← isymm G x hG (n + 1) u (finRotate (n + 1)), iteratedFDeriv_succ_apply_right, hfun, happ]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply, finRotate_last]
  congr 2
  funext k
  simp [Fin.init, finRotate_apply, Fin.coeSucc_eq_succ]

theorem ipeel (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) (i0 : Fin (n + 1)) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u i0)) x (fun k => u (i0.succAbove k)) := by
  rw [← isymm G x hG (n + 1) u i0.cycleRange.symm, ipeel0 G x hG n]
  simp [Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ]

theorem detD_fin (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ → ℂ) (hG : AnalyticAt ℂ G 0) :
    detD G = ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by
  have hgen : ∀ (m : ℕ) (h : m = N) (e : Fin m ≃ Fin N) (σ : Equiv.Perm (Fin N)),
      iteratedFDeriv ℂ m G 0 (fun i => Matrix.single (e i) (σ (e i)) (1 : ℂ)) =
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by
    intro m h e σ
    subst h
    exact isymm G 0 hG m (fun k => Matrix.single k (σ k) 1) e
  unfold detD
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hgen _ (Fintype.card_fin N) _ σ]

end PositivityTheory.Rg.Sw.LVs.CK
end
end

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

def phiF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Fin.cons 0 X

def piF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ := fun k l => X k l.succ

def colQ (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (c : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun k l => if l = c then X k 0 else 0

@[simp] theorem phiF_zero_row (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (j : Fin (N + 1)) : phiF X 0 j = 0 := rfl

@[simp] theorem phiF_succ_row (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (k : Fin N) (j : Fin (N + 1)) :
    phiF X k.succ j = X k j := rfl

def phiL (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℂ →L[ℂ] Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := phiF
      map_add' := fun X Y => by
        ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> simp
      map_smul' := fun a X => by
        ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> simp }

def piL (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℂ →L[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := piF
      map_add' := fun X Y => by ext k l; simp [piF]
      map_smul' := fun a X => by ext k l; simp [piF] }

@[simp] theorem piL_apply (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : piL N X = piF X := rfl

theorem phiF_single (k : Fin N) (j : Fin (N + 1)) :
    phiF (Matrix.single k j (1 : ℂ)) = Matrix.single k.succ j 1 := by
  ext i l
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [Matrix.single_apply, (Fin.succ_ne_zero k).symm]
  · simp [Matrix.single_apply, Fin.succ_inj]

theorem piF_single_succ (k : Fin N) (j : Fin N) :
    piF (Matrix.single k j.succ (1 : ℂ)) = Matrix.single k j 1 := by
  ext a b; simp [piF, Matrix.single_apply, Fin.succ_inj]

theorem piF_single_zero (k : Fin N) : piF (Matrix.single k (0 : Fin (N + 1)) (1 : ℂ)) = 0 := by
  ext a b; simp only [piF, Matrix.single_apply, Matrix.zero_apply]
  rw [if_neg]; rintro ⟨_, h⟩; exact Fin.succ_ne_zero b h.symm

theorem det_first_row_expansion (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (a : ℂ) (h : ∀ j, A 0 j = if j = 0 then a else 0) :
    A.det = a * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · simp [h]
  · intro j _ hj; simp [h, hj]
  · simp

theorem det_corner_perturbation (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    (1 + phiF X + s • Matrix.single 0 0 1).det = (1 + s) * (1 + piF X).det := by
  have hsub : (1 + phiF X + s • Matrix.single 0 0 1).submatrix Fin.succ Fin.succ = 1 + piF X := by
    ext k l
    simp [piF, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj, Fin.succ_ne_zero]
    intro h; exact absurd h.symm (Fin.succ_ne_zero k)
  rw [det_first_row_expansion _ (1 + s), hsub]
  intro j
  refine Fin.cases ?_ (fun m => ?_) j
  · simp [Matrix.one_apply, Matrix.single_apply]
  · simp [Matrix.one_apply, Matrix.single_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero m).symm]

theorem det_column_perturbation (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) (c : Fin N) :
    (1 + phiF X + s • Matrix.single 0 c.succ 1).det = (1 + piF X - s • colQ X c).det := by
  set A := 1 + phiF X + s • Matrix.single 0 c.succ (1 : ℂ) with hA
  have hne : c.succ ≠ (0 : Fin (N + 1)) := Fin.succ_ne_zero c
  have hz : ∀ k : Fin N, ((0 : Fin (N + 1)) = k.succ) ↔ False :=
    fun k => ⟨fun h => Fin.succ_ne_zero k h.symm, False.elim⟩
  rw [← Matrix.det_updateCol_add_smul_self A hne (-s)]
  rw [det_first_row_expansion _ 1]
  · rw [one_mul]
    congr 1
    ext k l
    by_cases hl : l = c
    · subst hl
      simp [A, Matrix.updateCol_apply, piF, colQ, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj,
        Fin.succ_ne_zero, hz]
      ring
    · have hl' : l.succ ≠ c.succ := fun h => hl (Fin.succ_inj.mp h)
      simp [A, Matrix.updateCol_apply, piF, colQ, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj,
        hl, hl', Fin.succ_ne_zero, hz]
  · intro j
    by_cases hj : j = c.succ
    · subst hj
      simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, Fin.succ_ne_zero, hz]
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨m, rfl⟩
      · simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, hne.symm, hz]
      · have hm : m ≠ c := fun h => hj (by rw [h])
        simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, hm, Fin.succ_ne_zero, hz,
          Fin.succ_inj, Ne.symm hm]

end PositivityTheory.Rg.Sw.LVs.CK
end
end

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

theorem fderiv_line {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (G : F → ℂ) (y v : F)
    (hG : DifferentiableAt ℂ G y) : HasDerivAt (fun s : ℂ => G (y + s • v)) (fderiv ℂ G y v) 0 := by
  have h1 : HasDerivAt (fun s : ℂ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).smul_const v).const_add y
  have h2 : HasFDerivAt G (fderiv ℂ G y) ((fun s : ℂ => y + s • v) 0) := by
    simpa using hG.hasFDerivAt
  exact h2.comp_hasDerivAt (0:ℂ) h1

theorem det_phiF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : (1 + phiF X).det = (1 + piF X).det := by
  have h0 : ∀ j : Fin (N+1), (1 + phiF X) 0 j = if j = 0 then 1 else 0 := by
    intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp [phiF_zero_row]
    · simp [phiF_zero_row, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero j).symm]
  rw [det_first_row_expansion _ 1 h0, one_mul]
  congr 1
  ext k l
  simp [Matrix.one_apply, phiF_succ_row, piF]

theorem fderiv_determinant_power_corner_int (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 0 1) = (t : ℂ) * H N t (piF X) := by
  set d := (1 + piF X).det with hd
  have hdiff : DifferentiableAt ℂ (H (N + 1) t) (phiF X) :=
    (analyticAt_H (N + 1) t (phiF X) (by rw [det_phiF]; exact hX)).differentiableAt
  have hl := fderiv_line (H (N + 1) t) (phiF X) (Matrix.single 0 0 1) hdiff
  have heq : (fun s : ℂ => H (N + 1) t (phiF X + s • Matrix.single 0 0 1)) =
      fun s => ((1 + s) * d) ^ t := by
    funext s
    simp only [H]
    congr 1
    have h0 : ∀ j : Fin (N + 1),
        ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) + (phiF X + s •
          (Matrix.single 0 0 1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))) 0 j =
        if j = 0 then 1 + s else 0 := by
      intro j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simp [phiF_zero_row]
      · simp [phiF_zero_row, Matrix.one_apply, (Fin.succ_ne_zero j).symm, Matrix.single_apply]
    rw [det_first_row_expansion _ (1 + s) h0]
    congr 2
    ext k l
    simp [Matrix.one_apply, phiF_succ_row, piF, Matrix.single_apply, (Fin.succ_ne_zero k).symm]
  rw [heq] at hl
  have hf : HasDerivAt (fun s : ℂ => (1 + s) * d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).const_add 1).mul_const d
  have hz := (hasDerivAt_zpow t ((1 + 0) * d) (Or.inl (by simpa using hX))).comp (0:ℂ) hf
  refine (hl.unique hz).trans ?_
  simp only [H, ← hd, add_zero, one_mul]
  rw [zpow_sub_one₀ hX]
  field_simp

theorem fderiv_determinant_power_column_int (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) (c : Fin N) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = -fderiv ℂ (H N t) (piF X) (colQ X c) := by
  have hdiff : DifferentiableAt ℂ (H (N + 1) t) (phiF X) :=
    (analyticAt_H (N + 1) t (phiF X) (by rw [det_phiF]; exact hX)).differentiableAt
  have hl := fderiv_line (H (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) hdiff
  have hl' := fderiv_line (H N t) (piF X) (-colQ X c)
    (analyticAt_H N t (piF X) hX).differentiableAt
  have heq : (fun s : ℂ => H (N + 1) t (phiF X + s • Matrix.single 0 c.succ 1)) =
      fun s => H N t (piF X + s • -colQ X c) := by
    funext s
    simp only [H]
    congr 1
    set A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
      1 + (phiF X + s • (Matrix.single 0 c.succ 1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) with hA
    rw [← Matrix.det_updateCol_add_smul_self A (i := c.succ) (j := 0) (Fin.succ_ne_zero c) (-s)]
    have h0 : ∀ j : Fin (N + 1),
        (A.updateCol c.succ (fun k => A k c.succ + (-s) • A k 0)) 0 j = if j = 0 then 1 else 0 := by
      intro j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simp [hA, Matrix.updateCol_apply, phiF_zero_row, Matrix.single_apply,
          (Fin.succ_ne_zero c).symm]
      · by_cases hj : j = c
        · subst hj
          simp [hA, Matrix.updateCol_apply, phiF_zero_row, Matrix.single_apply, Matrix.one_apply,
            (Fin.succ_ne_zero j).symm]
        · simp [hA, Matrix.updateCol_apply, phiF_zero_row, Matrix.single_apply, Matrix.one_apply,
            (Fin.succ_ne_zero j).symm, hj, Ne.symm hj, Fin.succ_inj]
    rw [det_first_row_expansion _ 1 h0, one_mul]
    congr 1
    ext k l
    by_cases hlc : l = c
    · subst hlc
      simp [hA, Matrix.updateCol_apply, phiF_succ_row, piF, colQ, Matrix.single_apply,
        Matrix.one_apply, (Fin.succ_ne_zero k).symm, sub_eq_add_neg]
      ring
    · simp [hA, Matrix.updateCol_apply, phiF_succ_row, piF, colQ, Matrix.single_apply,
        Matrix.one_apply, (Fin.succ_ne_zero k).symm, hlc, Fin.succ_inj]
  rw [heq] at hl
  refine (hl.unique hl').trans ?_
  simp <;> rfl

end PositivityTheory.Rg.Sw.LVs.CK
end
end

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

theorem analyticAt_determinant_power_zero_int (N : ℕ) (t : ℤ) : AnalyticAt ℂ (H N t) 0 := analyticAt_H N t 0 (by simp)

theorem analyticAt_fderiv_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (G : F → ℂ) (x v : F) (hG : AnalyticAt ℂ G x) : AnalyticAt ℂ (fun y => fderiv ℂ G y v) x := by
  have h2 : AnalyticAt ℂ (fun L : F →L[ℂ] ℂ => L v) (fderiv ℂ G x) :=
    (ContinuousLinearMap.apply ℂ ℂ v).analyticAt _
  exact h2.comp hG.fderiv

theorem ev_piF (N : ℕ) : ∀ᶠ X in 𝓝 (0 : Matrix (Fin N) (Fin (N + 1)) ℂ), (1 + piF X).det ≠ 0 := by
  have hc : Continuous fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => (1 + piF X).det := by
    unfold piF
    fun_prop
  have hz : piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ) = 0 := by
    ext k l
    simp [piF]
  have h0 : (1 + piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)).det ≠ 0 := by
    simp [hz]
  exact hc.continuousAt.eventually_ne h0

theorem iconst_mul {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (G : F → ℂ) (x : F) (a : ℂ)
    (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin n → F) :
    iteratedFDeriv ℂ n (fun y => a * G y) x u = a * iteratedFDeriv ℂ n G x u := by
  have h := iteratedFDeriv_const_smul_apply' (a := a) (i := n) (hG.contDiffAt (n := n))
  simp only [smul_eq_mul] at h
  rw [h, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

theorem icompL {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (G : F → ℂ) (φ : E → F) (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hsmul : ∀ (c : ℂ) a, φ (c • a) = c • φ a)
    (x : E) (y : F) (hxy : φ x = y) (hG : AnalyticAt ℂ G y) (n : ℕ) (u : Fin n → E)
    (v : Fin n → F) (huv : ∀ i, φ (u i) = v i) :
    iteratedFDeriv ℂ n (G ∘ φ) x u = iteratedFDeriv ℂ n G y v := by
  let Lℓ : E →ₗ[ℂ] F := { toFun := φ, map_add' := hadd, map_smul' := hsmul }
  let L : E →L[ℂ] F := LinearMap.toContinuousLinearMap Lℓ
  have hL : ∀ z, L z = φ z := fun z => rfl
  obtain ⟨U, hUP, hUo, hyU⟩ := eventually_nhds_iff.1 hG.eventually_analyticAt
  have hU : ContDiffOn ℂ n G U := fun z hz => (hUP z hz).contDiffAt.contDiffWithinAt
  have hxU : L x ∈ U := by rw [hL, hxy]; exact hyU
  have hpre : IsOpen (L ⁻¹' U) := hUo.preimage L.continuous
  have key := L.iteratedFDerivWithin_comp_right hU hUo.uniqueDiffOn hpre.uniqueDiffOn hxU
    (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpre (show x ∈ L ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hUo hxU] at key
  have hcomp : G ∘ φ = G ∘ L := rfl
  rw [hcomp, key, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  show iteratedFDeriv ℂ n G (φ x) (fun i => φ (u i)) = _
  rw [hxy]
  congr 1
  funext i
  exact huv i

theorem phiF_add (a b : Matrix (Fin N) (Fin (N + 1)) ℂ) : phiF (a + b) = phiF a + phiF b := by
  ext i j
  cases i using Fin.cases <;> simp [phiF_zero_row, phiF_succ_row]

theorem phiF_smul (c : ℂ) (a : Matrix (Fin N) (Fin (N + 1)) ℂ) : phiF (c • a) = c • phiF a := by
  ext i j
  cases i using Fin.cases <;> simp [phiF_zero_row, phiF_succ_row]

theorem piF_add (a b : Matrix (Fin N) (Fin (N + 1)) ℂ) : piF (a + b) = piF a + piF b := by
  ext i j; rfl

theorem piF_smul (c : ℂ) (a : Matrix (Fin N) (Fin (N + 1)) ℂ) : piF (c • a) = c • piF a := by
  ext i j; rfl

theorem phiF_zero : phiF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ) = 0 := by
  ext i j
  cases i using Fin.cases <;> simp [phiF_zero_row, phiF_succ_row]

theorem piF_zero : piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ) = 0 := by
  ext i j; rfl

theorem iterated_derivative_corner_case_int (t : ℤ) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) 0
        (fun k => Matrix.single k.succ (e k).succ 1) =
      (t : ℂ) * iteratedFDeriv ℂ N (H N t) 0 (fun k => Matrix.single k (e k) 1) := by
  have hA : AnalyticAt ℂ (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int (N + 1) t)
  have h1 := icompL (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) phiF phiF_add
    phiF_smul 0 0 phiF_zero hA N (fun k => Matrix.single k (e k).succ 1)
    (fun k => Matrix.single k.succ (e k).succ 1) (fun k => phiF_single k (e k).succ)
  rw [← h1]
  have hpi : piF = ⇑(piL N) := funext fun X => (piL_apply X).symm
  have hB : AnalyticAt ℂ (H N t ∘ piF) 0 := by
    rw [hpi]
    refine (analyticAt_H N t (piL N 0) ?_).comp ((piL N).analyticAt 0)
    rw [piL_apply, piF_zero, add_zero, det_one]
    exact one_ne_zero
  have hev : (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) ∘ phiF =ᶠ[𝓝 0]
      fun X => (t : ℂ) * (H N t ∘ piF) X := by
    filter_upwards [ev_piF N] with X hX
    exact fderiv_determinant_power_corner_int t X hX
  rw [(Filter.EventuallyEq.iteratedFDeriv ℂ hev N).eq_of_nhds, iconst_mul _ 0 _ hB]
  congr 1
  exact icompL (H N t) piF piF_add piF_smul 0 0 piF_zero (analyticAt_determinant_power_zero_int N t) N _ _
    (fun k => piF_single_succ k (e k))

end PositivityTheory.Rg.Sw.LVs.CK
end
end

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

def fsum (t : ℤ) (c : Fin N) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : ℂ :=
  -∑ k, X k 0 * fderiv ℂ (H N t) (piF X) (Matrix.single k c 1)

theorem colQ_expand (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (c : Fin N) :
    colQ X c = ∑ k, X k 0 • Matrix.single k c (1 : ℂ) := by
  ext k l
  simp only [colQ, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h
    simp
  · simp [Ne.symm h]

theorem fderiv_determinant_power_column_sum (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) (c : Fin N) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = fsum t c X := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fderiv_determinant_power_column_int t X hX c, colQ_expand, map_sum, fsum]
  simp only [map_smul, smul_eq_mul]

theorem analyticAt_entry (k : Fin N) (j : Fin (N + 1)) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) :
    AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => X k j) X0 := by
  have := (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℂ ℂ k j : Matrix (Fin N) (Fin (N + 1)) ℂ →ₗ[ℂ] ℂ)).analyticAt X0
  exact this

theorem analyticAt_piF (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) :
    AnalyticAt ℂ (piF : Matrix (Fin N) (Fin (N + 1)) ℂ → Matrix (Fin N) (Fin N) ℂ) X0 :=
  (piL N).analyticAt X0

theorem analyticAt_fsum (t : ℤ) (c : Fin N) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) (h : (1 + piF X0).det ≠ 0) :
    AnalyticAt ℂ (fsum t c) X0 := by
  have hE : ∀ k : Fin N, AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ =>
      X k 0 * fderiv ℂ (H N t) (piF X) (Matrix.single k c 1)) X0 := by
    intro k
    refine (analyticAt_entry k 0 X0).mul ?_
    exact (analyticAt_fderiv_apply (H N t) (piF X0) (Matrix.single k c 1)
      (analyticAt_H N t _ h)).comp (analyticAt_piF X0)
  have hs := (Finset.analyticAt_sum Finset.univ (fun k _ => hE k)).neg
  convert hs using 1
  funext X
  simp [fsum, Finset.sum_apply]

end PositivityTheory.Rg.Sw.LVs.CK
end
end

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

theorem fsum_line (t : ℤ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    fsum t c (y + s • Matrix.single k0 0 1) =
      fsum t c y - s * fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) := by
  have hp : piF (y + s • Matrix.single k0 0 1) = piF y := by
    ext k l
    simp [piF, Matrix.single_apply, Fin.succ_ne_zero]
    intro _ h
    exact absurd h.symm (Fin.succ_ne_zero l)
  simp only [fsum, hp]
  (simp [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']) <;> ring

theorem fderiv_fsum (t : ℤ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (hy : (1 + piF y).det ≠ 0) :
    fderiv ℂ (fsum t c) y (Matrix.single k0 0 1) = -fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) := by
  have hd : DifferentiableAt ℂ (fsum t c) y := (analyticAt_fsum t c y hy).differentiableAt
  have hl : HasDerivAt (fun s : ℂ => y + s • Matrix.single k0 0 (1 : ℂ)) (Matrix.single k0 0 1) 0 := by
    have h0 := ((hasDerivAt_id (0 : ℂ)).smul_const (Matrix.single k0 0 (1 : ℂ))).const_add y
    simp only [id_eq, one_smul] at h0
    exact h0
  have h1 : HasDerivAt (fun s : ℂ => fsum t c (y + s • Matrix.single k0 0 1))
      (fderiv ℂ (fsum t c) y (Matrix.single k0 0 1)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hd.hasFDerivAt hl (by simp)
  have h2 : HasDerivAt (fun s : ℂ => fsum t c (y + s • Matrix.single k0 0 1))
      (-fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1)) 0 := by
    have he : (fun s : ℂ => fsum t c (y + s • Matrix.single k0 0 1)) =
        fun s => fsum t c y - s * fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) :=
      funext fun s => fsum_line t c k0 y s
    rw [he]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const
      (fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1))).const_sub (fsum t c y)
  exact h1.unique h2

end PositivityTheory.Rg.Sw.LVs.CK
end
end

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem iterated_derivative_column_case_int (t : ℤ) (M : ℕ) (e : Equiv.Perm (Fin (M + 1))) (c : Fin (M + 1)) :
    iteratedFDeriv ℂ (M + 1) (fun y => fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1) =
      -iteratedFDeriv ℂ (M + 1) (H (M + 1) t) 0 (fun k => Matrix.single k (e k) 1) := by
  have hσ : ∀ k : Fin (M + 1), Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ =
      Equiv.swap 0 c.succ (e k).succ :=
    fun k => Equiv.Perm.decomposeFin_symm_apply_succ e c.succ k
  have hG : AnalyticAt ℂ (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int _ t)
  have e1 := icompL (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) phiF phiF_add phiF_smul 0 0
    phiF_zero hG (M + 1)
    (fun k => Matrix.single k (Equiv.swap 0 c.succ (e k).succ) 1)
    (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1)
    (fun i => by rw [phiF_single, hσ])
  rw [← e1]
  have hev : (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) ∘ phiF =ᶠ[𝓝 0] fsum t c := by
    filter_upwards [ev_piF (M + 1)] with X hX
    exact fderiv_determinant_power_column_sum t X hX c
  rw [(hev.iteratedFDeriv ℂ (M + 1)).eq_of_nhds]
  have h0 : (1 + piF (0 : Matrix (Fin (M + 1)) (Fin (M + 1 + 1)) ℂ)).det ≠ 0 := by
    simp [piF_zero]
  rw [ipeel (fsum t c) 0 (analyticAt_fsum t c 0 h0) M _ (e.symm c)]
  beta_reduce
  have hu0 : Equiv.swap 0 c.succ (e (e.symm c)).succ = 0 := by simp
  rw [hu0]
  have hev2 : (fun y => fderiv ℂ (fsum t c) y (Matrix.single (e.symm c) 0 1)) =ᶠ[𝓝 0]
      (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
        (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) ∘ piF := by
    filter_upwards [ev_piF (M + 1)] with y hy
    simp [fderiv_fsum t c (e.symm c) y hy]
  erw [(hev2.iteratedFDeriv ℂ M).eq_of_nhds]
  have hK : AnalyticAt ℂ (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int _ t)
  have hK' : AnalyticAt ℂ (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) 0 :=
    analyticAt_const.mul hK
  have hne : ∀ k : Fin M, Equiv.swap 0 c.succ (e ((e.symm c).succAbove k)).succ =
      (e ((e.symm c).succAbove k)).succ := by
    intro k
    have h1 : e ((e.symm c).succAbove k) ≠ c := by
      intro h
      have h2 := congrArg e.symm h
      rw [Equiv.symm_apply_apply] at h2
      exact Fin.succAbove_ne _ _ h2
    exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => h1 (Fin.succ_injective _ h))
  erw [icompL (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1))
    piF piF_add piF_smul 0 0 piF_zero hK' M
    (fun k => Matrix.single ((e.symm c).succAbove k)
      (Equiv.swap 0 c.succ (e ((e.symm c).succAbove k)).succ) 1)
    (fun k => Matrix.single ((e.symm c).succAbove k) (e ((e.symm c).succAbove k)) 1)
    (fun k => by rw [hne, piF_single_succ])]
  rw [iconst_mul _ 0 (-1) hK]
  rw [ipeel (H (M + 1) t) 0 (analyticAt_determinant_power_zero_int _ t) M (fun k => Matrix.single k (e k) 1) (e.symm c)]
  clear e1 hev hev2 hK' hne hσ hG h0 hu0 hK
  simp
  rfl

end PositivityTheory.Rg.Sw.LVs.CK
end
end

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem term_p (t : ℤ) (N : ℕ) (p : Fin (N + 1)) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ (N + 1) (H (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (p, e) k) 1) =
      iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 p 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (p, e) k.succ) 1) := by
  rw [ipeel0 (H (N + 1) t) 0 (analyticAt_determinant_power_zero_int (N + 1) t) N]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero]
  rfl

theorem rec_step (t : ℤ) (N : ℕ) : detD (H (N + 1) t) = ((t : ℂ) + N) * detD (H N t) := by
  rw [detD_fin _ _ (analyticAt_determinant_power_zero_int _ _), detD_fin _ _ (analyticAt_determinant_power_zero_int _ _),
    Finset.univ_perm_fin_succ, ← Finset.univ_product_univ, Finset.sum_map, Finset.sum_product,
    Fin.sum_univ_succ]
  simp only [Equiv.toEmbedding_apply, term_p, Equiv.Perm.decomposeFin.symm_sign, if_pos rfl]
  have h0 : ∀ e : Equiv.Perm (Fin N),
      (iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 (0 : Fin (N + 1)) 1)) 0)
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm ((0 : Fin (N + 1)), e) k.succ) 1) =
      t * iteratedFDeriv ℂ N (H N t) 0 (fun k => Matrix.single k (e k) 1) := by
    intro e
    simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    exact iterated_derivative_corner_case_int t e
  simp only [h0, if_true, one_mul, Fin.succ_ne_zero, if_false]
  cases N with
  | zero => simp
  | succ M =>
    simp only [iterated_derivative_column_case_int, Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg,
      Int.cast_one, neg_one_mul, neg_mul_neg]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, add_mul, Finset.mul_sum, Finset.mul_sum,
      nsmul_eq_mul, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;> push_cast <;> ring

theorem capelli_determinant_integer_rising (t : ℤ) : ∀ N : ℕ, detD (H N t) = ∏ i ∈ Finset.range N, ((t : ℂ) + i)
  | 0 => by
    rw [detD_fin 0 _ (analyticAt_determinant_power_zero_int 0 t)]
    simp [H, iteratedFDeriv_zero_apply]
  | N + 1 => by
    rw [rec_step, capelli_determinant_integer_rising t N, Finset.prod_range_succ]
    ring

end PositivityTheory.Rg.Sw.LVs.CK

namespace PositivityTheory.Rg.Sw.LVs

theorem kappaFin : KappaFin := fun N t => CK.capelli_determinant_integer_rising t N

end PositivityTheory.Rg.Sw.LVs
