module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExp

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarPolB
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarPolA
noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.HPol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Log

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_strict :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
  first
  | exact hasStrictFDerivAt_exp_zero
  | exact hasStrictFDerivAt_exp_zero.congr_fderiv (by ext; simp)


variable (n) in
def logM : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
  (exp_strict (n := n)).localInverse _ _ _

theorem logM_exp : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), logM n (NormedSpace.exp X) = X := by
  exact (exp_strict (n := n)).eventually_left_inverse

theorem exp_logM : ∀ᶠ h in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (logM n h) = h := by
  have h := (exp_strict (n := n)).eventually_right_inverse
  rw [NormedSpace.exp_zero] at h
  exact h

theorem logM_one : logM n 1 = 0 := by
  have h := (exp_strict (n := n)).localInverse_apply_image
  rw [NormedSpace.exp_zero] at h
  exact h

theorem logM_strict : HasStrictFDerivAt (logM n) (ContinuousLinearMap.id ℝ _) 1 := by
  have h := (exp_strict (n := n)).to_localInverse
  rw [NormedSpace.exp_zero] at h
  exact h

end Log

private theorem Jm_mul_self_eq_one' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem Jm_inv (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε := by
  exact Matrix.inv_eq_left_inv (Jm_mul_self_eq_one' ε)

theorem Jm_isUnit (ε : Fin n → Bool) : IsUnit (Jm ε) := by
  exact ⟨⟨Jm ε, Jm ε, Jm_mul_self_eq_one' ε, Jm_mul_self_eq_one' ε⟩, rfl⟩

theorem conjT_of_inG {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    Yᴴ = Jm ε * (-Y) * (Jm ε)⁻¹ := by
  have hJ := Jm_mul_self_eq_one' ε
  have h' : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left h'
  rw [Jm_inv]
  calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε * (-Y) * Jm ε := by rw [h1, Matrix.mul_neg]

theorem exp_inUJ {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  have hJ := Jm_mul_self_eq_one' ε
  show (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε
  rw [← Matrix.exp_conjTranspose, conjT_of_inG h, Matrix.exp_conj _ _ (Jm_isUnit ε), Jm_inv,
    Matrix.mul_assoc (Jm ε * NormedSpace.exp (-Y)) (Jm ε) (Jm ε), hJ, Matrix.mul_one, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

theorem inG_of_exp {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (hU : inUJ ε (NormedSpace.exp Y)) (h1 : ℓ (NormedSpace.exp Y) = Y)
    (h2 : ℓ (NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε)) = Jm ε * (-Yᴴ) * Jm ε) : inG ε Y := by
  have hJ := Jm_mul_self_eq_one' ε
  have hU' : (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε := hU
  have hEE : NormedSpace.exp Y * NormedSpace.exp (-Y) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl Y)), add_neg_cancel,
      NormedSpace.exp_zero]
  have key : NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε) = NormedSpace.exp Y := by
    have e1 : Jm ε * (-Yᴴ) * Jm ε = Jm ε * (-Y)ᴴ * (Jm ε)⁻¹ := by
      rw [Jm_inv, Matrix.conjTranspose_neg]
    rw [e1, Matrix.exp_conj _ _ (Jm_isUnit ε), Jm_inv, Matrix.exp_conjTranspose]
    calc Jm ε * (NormedSpace.exp (-Y))ᴴ * Jm ε
        = Jm ε * (NormedSpace.exp (-Y))ᴴ * ((NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y) := by
          rw [hU']
      _ = Jm ε * (NormedSpace.exp Y * NormedSpace.exp (-Y))ᴴ * Jm ε * NormedSpace.exp Y := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = NormedSpace.exp Y := by
          rw [hEE, Matrix.conjTranspose_one, Matrix.mul_one, hJ, Matrix.one_mul]
  have hY : Y = Jm ε * (-Yᴴ) * Jm ε := by rw [← h2, key, h1]
  have h3 : Jm ε * Y = -(Yᴴ * Jm ε) := by
    calc Jm ε * Y = Jm ε * (Jm ε * (-Yᴴ) * Jm ε) := congrArg (Jm ε * ·) hY
      _ = -(Yᴴ * Jm ε) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.neg_mul]
  show Yᴴ * Jm ε + Jm ε * Y = 0
  rw [h3, add_neg_cancel]

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem entry_of_inG {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (i j : Fin n) :
    star (Y j i) * sg ε j + sg ε i * Y i j = 0 := by
  have h' := congrFun (congrFun (show Yᴴ * Jm ε + Jm ε * Y = 0 from h) i) j
  simpa [Jm, sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h'

theorem inG_of_entry' {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, star (Y j i) * sg ε j + sg ε i * Y i j = 0) : inG ε Y := by
  show Yᴴ * Jm ε + Jm ε * Y = 0
  ext i j
  simpa [Jm, sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h i j

def cLin (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] GCo ε where
  toFun Y := ((fun a => (Y a a).im, fun ab => Y ab.1.1 ab.1.2), fun ab => Y ab.1.1 ab.1.2)
  map_add' _ _ := by
    ext <;> simp
  map_smul' _ _ := by
    ext <;> simp

theorem cLin_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cLin ε Y = ((fun a => (Y a a).im, fun ab => Y ab.1.1 ab.1.2), fun ab => Y ab.1.1 ab.1.2) := rfl

theorem cLin_gMat {ε : Fin n → Bool} (s : GCo ε) : cLin ε (gMat s) = s := by
  obtain ⟨⟨d, k⟩, p⟩ := s
  rw [cLin_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [gMat, kMat, pmat]
  · funext ab
    obtain ⟨⟨a, b⟩, hab⟩ := ab
    have h1 : a ≠ b := ne_of_gt hab.1
    have h2 : ¬ a < b := not_lt_of_gt hab.1
    simp [gMat, kMat, pmat, h1, h2, hab.1, hab.2]
  · funext ab
    obtain ⟨⟨a, b⟩, hab⟩ := ab
    have h1 : a ≠ b := ne_of_gt hab.1
    have h2 : ¬ a < b := not_lt_of_gt hab.1
    simp [gMat, kMat, pmat, h1, h2, hab.1, hab.2]

theorem gMat_cLin {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    gMat (cLin ε Y) = Y := by
  ext a b
  have hE := entry_of_inG h a b
  rw [cLin_apply]
  simp only [gMat, kMat, pmat, Matrix.add_apply]
  rcases lt_trichotomy a b with hab | rfl | hab
  · have h1 : a ≠ b := ne_of_lt hab
    have h2 : ¬ b < a := not_lt_of_gt hab
    cases ha : ε a <;> cases hb : ε b <;>
      simp only [sg, ha, hb, ↓reduceIte, Bool.false_eq_true] at hE <;>
      simp [ha, hb, h1, h2, hab] <;>
      (try simp only [Complex.star_def] at hE) <;>
      first | linear_combination hE | linear_combination -hE
  · have h0 : star (Y a a) + Y a a = 0 := by
      cases ha : ε a <;> simp only [sg, ha, ↓reduceIte, Bool.false_eq_true] at hE <;>
        first | linear_combination hE | linear_combination -hE
    have hre : (Y a a).re = 0 := by
      have h4 := congrArg Complex.re h0
      simp at h4
      linarith
    apply Complex.ext <;> simp [hre]
  · have h1 : a ≠ b := ne_of_gt hab
    have h2 : ¬ a < b := not_lt_of_gt hab
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, h1, h2, hab]

theorem sg_eq {ε : Fin n → Bool} {i j : Fin n} (h : ε i = ε j) : sg ε i = sg ε j := by
  simp [sg, h]

theorem sg_ne {ε : Fin n → Bool} {i j : Fin n} (h : ¬ ε i = ε j) : sg ε i = -sg ε j := by
  unfold sg
  cases hi : ε i <;> cases hj : ε j <;> simp_all

theorem inG_gMat {ε : Fin n → Bool} (s : GCo ε) : inG ε (gMat s) := by
  apply inG_of_entry'
  intro i j
  obtain ⟨⟨d, k⟩, p⟩ := s
  simp only [gMat, kMat, pmat, Matrix.add_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have h1 : i ≠ j := ne_of_lt hij
    have h2 : ¬ j < i := not_lt_of_gt hij
    by_cases hε : ε i = ε j
    · simp [hε, h1, h1.symm, h2, hij, sg_eq hε]
      ring
    · simp [hε, Ne.symm hε, h1, h1.symm, h2, hij, sg_ne hε]
      ring
  · simp <;> ring
  · have h1 : i ≠ j := ne_of_gt hij
    have h2 : ¬ i < j := not_lt_of_gt hij
    by_cases hε : ε i = ε j
    · simp [hε, h1, h1.symm, h2, hij, sg_eq hε]
      ring
    · simp [hε, Ne.symm hε, h1, h1.symm, h2, hij, sg_ne hε]
      ring

end ReciprocityTheory.ChartRestriction.DS.HPol
end
end

noncomputable section

open Matrix Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.HPol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pmat_zero' (ε : Fin n → Bool) : pmat (0 : PCoord ε → ℂ) = 0 := by
  ext a b; simp [pmat]

theorem kMat_zero' (ε : Fin n → Bool) : kMat (0 : KCo ε) = 0 := by
  ext a b; simp [kMat]

theorem gMat_fst {ε : Fin n → Bool} (w : KCo ε) : gMat ((w, 0) : GCo ε) = kMat w := by
  simp [gMat, pmat_zero']

theorem gMat_snd {ε : Fin n → Bool} (z : PCoord ε → ℂ) : gMat ((0, z) : GCo ε) = pmat z := by
  simp [gMat, kMat_zero']

def gLin (ε : Fin n → Bool) : GCo ε →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := gMat
  map_add' s t := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp <;> ring
  map_smul' c s := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul] <;> ring

theorem inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

theorem inUJ_pol {ε : Fin n → Bool} (s : GCo ε) :
    inUJ ε (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)) := by
  rw [← gMat_fst, ← gMat_snd]
  exact inUJ_mul (exp_inUJ (inG_gMat _)) (exp_inUJ (inG_gMat _))

def Lm {ε : Fin n → Bool} (s : GCo ε) : GCo ε :=
  cLin ε (logM n (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)))

section An

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_comp_strict {ε : Fin n → Bool} (A : GCo ε →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    HasStrictFDerivAt (fun s => NormedSpace.exp (A s)) A 0 := by
  have h1 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (ContinuousLinearMap.id ℝ _) (A 0) := by
    rw [map_zero]; exact exp_strict
  exact h1.comp (0 : GCo ε) A.hasStrictFDerivAt

theorem prod_strict (ε : Fin n → Bool) :
    HasStrictFDerivAt (fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2))
      (LinearMap.toContinuousLinearMap (gLin ε)) 0 := by
  let kL : GCo ε →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap ((gLin ε).comp ((LinearMap.inl ℝ _ _).comp (LinearMap.fst ℝ _ _)))
  let pL : GCo ε →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap ((gLin ε).comp ((LinearMap.inr ℝ _ _).comp (LinearMap.snd ℝ _ _)))
  have ek : ∀ s : GCo ε, kL s = kMat s.1 := fun s => gMat_fst s.1
  have ep : ∀ s : GCo ε, pL s = pmat s.2 := fun s => gMat_snd s.2
  have h := (exp_comp_strict kL).mul' (exp_comp_strict pL)
  have hf : ((fun s : GCo ε => NormedSpace.exp (kL s)) * fun s => NormedSpace.exp (pL s)) =
      fun s => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2) := by
    funext s; rw [Pi.mul_apply, ek, ep]
  rw [hf] at h
  refine h.congr_fderiv (ContinuousLinearMap.ext fun s => ?_)
  have e0 : kMat (0 : GCo ε).1 = 0 := kMat_zero' ε
  have e1 : pmat (0 : GCo ε).2 = 0 := pmat_zero' ε
  change NormedSpace.exp (kL 0) * pL s + kL s * NormedSpace.exp (pL 0) = gMat s
  rw [ek, ep, ek, ep, e0, e1, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one, add_comm]
  rfl

theorem Lm_strict (ε : Fin n → Bool) :
    HasStrictFDerivAt (Lm (ε := ε)) (ContinuousLinearMap.id ℝ (GCo ε)) 0 := by
  have h0 : (fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)) 0 = 1 := by
    simp [kMat_zero', pmat_zero']
  have hl : HasStrictFDerivAt (logM n) (ContinuousLinearMap.id ℝ _)
      ((fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)) 0) := by
    have h := (exp_strict (n := n)).to_localInverse
    rw [NormedSpace.exp_zero] at h
    rw [h0]
    exact h
  have h := (LinearMap.toContinuousLinearMap (cLin ε)).hasStrictFDerivAt.comp (0 : GCo ε)
    (hl.comp (0 : GCo ε) (prod_strict ε))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun s => ?_)
  simp only [ContinuousLinearMap.id_apply]
  exact cLin_gMat s

end An

section An

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem Lm_exp (ε : Fin n → Bool) : ∀ᶠ s in 𝓝 (0 : GCo ε),
    NormedSpace.exp (gMat (Lm s)) = NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2) := by
  have hP0 : NormedSpace.exp (kMat (0 : GCo ε).1) * NormedSpace.exp (pmat (0 : GCo ε).2) = 1 := by
    simp [kMat_zero', pmat_zero']
  have hP : Tendsto (fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2))
      (𝓝 0) (𝓝 1) := by
    have := (prod_strict ε).continuousAt.tendsto
    rwa [hP0] at this
  have hlog := exp_strict (n := n)
  have hl : Tendsto (logM n) (𝓝 1) (𝓝 0) := by
    have h := hlog.to_localInverse.continuousAt.tendsto
    rw [hlog.localInverse_apply_image, NormedSpace.exp_zero] at h
    exact h
  have hΦ := hl.comp hP
  have hc : Continuous fun Y : Matrix (Fin n) (Fin n) ℂ => Jm ε * (-Yᴴ) * Jm ε :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose.neg).matrix_mul continuous_const
  have hJ : Tendsto (fun s : GCo ε =>
      Jm ε * (-(logM n (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)))ᴴ) * Jm ε)
      (𝓝 0) (𝓝 0) := by
    have := (hc.tendsto 0).comp hΦ
    simp only [Matrix.conjTranspose_zero, neg_zero, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this
  have hleft : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), logM n (NormedSpace.exp X) = X :=
    hlog.eventually_left_inverse
  have hright : ∀ᶠ Y in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (logM n Y) = Y := by
    have h := hlog.eventually_right_inverse
    rw [NormedSpace.exp_zero] at h
    exact h
  filter_upwards [hP.eventually hright, hΦ.eventually hleft, hJ.eventually hleft]
    with s h1 h2 h3
  have hU : inUJ ε (NormedSpace.exp (logM n (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)))) := by
    rw [h1]; exact inUJ_pol s
  have hG := inG_of_exp (logM n) hU h2 h3
  show NormedSpace.exp (gMat (cLin ε _)) = _
  rw [gMat_cLin hG, h1]

end An

theorem polSet_eq_expSet (ε : Fin n → Bool) : ∃ δ > 0, ∀ S : Set (GCo ε), (∀ s ∈ S, ‖s‖ < δ) →
    polSet S = expSet (Lm '' S) := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp (Lm_exp ε)
  refine ⟨δ, hδ, fun S hS => ?_⟩
  ext g
  constructor
  · rintro ⟨s, hs, hg⟩
    refine ⟨Lm s, ⟨s, hs, rfl⟩, ?_⟩
    rw [hg, h s (by simpa using hS s hs)]
  · rintro ⟨t, ⟨s, hs, rfl⟩, hg⟩
    refine ⟨s, hs, ?_⟩
    rw [hg, h s (by simpa using hS s hs)]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem Lm_zero (ε : Fin n → Bool) : Lm (0 : GCo ε) = 0 := by
  have h := (exp_strict (n := n)).localInverse_apply_image
  rw [NormedSpace.exp_zero] at h
  have hzero : logM n 1 = 0 := h
  simp [Lm, kMat_zero', pmat_zero', hzero]

instance borel_gco (ε : Fin n → Bool) : BorelSpace (GCo ε) := Prod.borelSpace

theorem volume_gco_isAddHaar (ε : Fin n → Bool) : (volume : Measure (GCo ε)).IsAddHaarMeasure := by
  have : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

theorem image_est (ε : Fin n → Bool) {η : ℝ} (hη : 0 < η) : ∃ δ > 0, ∀ S : Set (GCo ε),
    MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      MeasurableSet (Lm '' S) ∧ (∀ s ∈ S, ‖Lm s‖ ≤ 2 * ‖s‖) ∧
      volume (Lm '' S) ≤ ENNReal.ofReal (1 + η) * volume S ∧
      ENNReal.ofReal (1 - η) * volume S ≤ volume (Lm '' S) := by
  have := volume_gco_isAddHaar ε
  set A := ContinuousLinearMap.id ℝ (GCo ε)
  have hdet : A.det = 1 := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
  have hm1 : ENNReal.ofReal |A.det| < ((Real.toNNReal (1 + η) : ℝ≥0) : ℝ≥0∞) := by
    rw [hdet, abs_one, ENNReal.ofReal_one]
    have : (1 : ℝ≥0) < Real.toNNReal (1 + η) := by
      rw [← Real.toNNReal_one]; exact (Real.toNNReal_lt_toNNReal_iff (by linarith)).2 (by linarith)
    exact_mod_cast this
  have hm2 : ((Real.toNNReal (1 - η) : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal |A.det| := by
    rw [hdet, abs_one, ENNReal.ofReal_one]
    have : Real.toNNReal (1 - η) < 1 := by
      rw [Real.toNNReal_lt_one]; linarith
    exact_mod_cast this
  have h1 := addHaar_image_le_mul_of_det_lt (volume : Measure (GCo ε)) A hm1
  have h2 := mul_le_addHaar_image_of_lt_det (volume : Measure (GCo ε)) A hm2
  have h3 : ∀ᶠ c in 𝓝[>] (0 : ℝ≥0), c < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one)
  have h4 : ∀ᶠ c in 𝓝[>] (0 : ℝ≥0), 0 < c := self_mem_nhdsWithin
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := (h1.and (h2.and (h3.and h4))).exists
  obtain ⟨U, hU, hA⟩ := (Lm_strict ε).approximates_deriv_on_nhds (c := c) (Or.inr hc4)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hB := hA.mono_set hball
  refine ⟨δ, hδ, fun S hS hSδ => ?_⟩
  have hSb : S ⊆ ball 0 δ := fun s hs => mem_ball_zero_iff.mpr (hSδ s hs)
  have hAS := hB.mono_set hSb
  have hc1' : (c : ℝ) < 1 := by exact_mod_cast hc3
  have hinj : Set.InjOn Lm S := by
    intro x hx y hy hxy
    have h := hAS x hx y hy
    simp only [ContinuousLinearMap.id_apply, hxy, sub_self, zero_sub, norm_neg] at h
    have h0 : ‖x - y‖ = 0 := by
      have := norm_nonneg (x - y)
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have : PolishSpace (KPair ε → ℂ) := inferInstance
  have : PolishSpace (PCoord ε → ℂ) := inferInstance
  have : PolishSpace (KCo ε) := inferInstance
  have : PolishSpace (GCo ε) := inferInstance
  refine ⟨hS.image_of_continuousOn_injOn hAS.continuousOn hinj, fun s hs => ?_, hc1 S Lm hAS,
    hc2 S Lm hAS⟩
  have h := hB s (hSb hs) 0 (mem_ball_self hδ)
  simp only [ContinuousLinearMap.id_apply, Lm_zero, sub_zero] at h
  have := norm_sub_norm_le (Lm s) s
  have := norm_nonneg s
  nlinarith

end ReciprocityTheory.ChartRestriction.DS.HPol
end
end

noncomputable section

open Finset Matrix MeasureTheory Metric

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HPol

variable {n : ℕ}

theorem haar_pol_density {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (d : ℝ)
    (h : DensOn (fun S => μ (expSet S)) d) : DensOn (fun S => μ (polSet S)) d := by
  intro η hη
  set η' : ℝ := min (η / 3) (1 / 2) with hη'def
  have hη'0 : 0 < η' := lt_min (by positivity) (by norm_num)
  have hη'1 : η' ≤ 1 / 2 := min_le_right _ _
  have hη'3 : η' ≤ η / 3 := min_le_left _ _
  obtain ⟨δ1, hδ1, hE⟩ := h η' hη'0
  obtain ⟨δ4, hδ4, hE2⟩ := h 2 (by norm_num)
  obtain ⟨δ2, hδ2, hI⟩ := HPol.image_est ε hη'0
  obtain ⟨δ3, hδ3, hP⟩ := HPol.polSet_eq_expSet ε
  refine ⟨min (min δ2 δ3) (min (δ1 / 2) (δ4 / 2)),
    lt_min (lt_min hδ2 hδ3) (lt_min (by positivity) (by positivity)), fun S hS hsmall => ?_⟩
  have hs2 : ∀ s ∈ S, ‖s‖ < δ2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_left _ _))
  have hs3 : ∀ s ∈ S, ‖s‖ < δ3 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_right _ _))
  have hs1 : ∀ s ∈ S, ‖s‖ < δ1 / 2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : ∀ s ∈ S, ‖s‖ < δ4 / 2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hmeas, hnorm, hup, hlo⟩ := hI S hS hs2
  have hsm1 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ1 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hs1 s hs
    linarith [hnorm s hs]
  have hsm4 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ4 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hs4 s hs
    linarith [hnorm s hs]
  obtain ⟨hEu, hEl⟩ := hE _ hmeas hsm1
  beta_reduce at hEu hEl ⊢
  rw [hP S hs3]
  have hsq1 : (1 + η') * (1 + η') ≤ 1 + η := by nlinarith
  have hsq2 : 1 - η ≤ (1 - η') * (1 - η') := by nlinarith
  constructor
  · calc μ (expSet (HPol.Lm '' S)) ≤ ENNReal.ofReal ((1 + η') * d) * volume (HPol.Lm '' S) := hEu
      _ ≤ ENNReal.ofReal ((1 + η') * d) * (ENNReal.ofReal (1 + η') * volume S) := by gcongr
      _ = (ENNReal.ofReal ((1 + η') * d) * ENNReal.ofReal (1 + η')) * volume S := by
        rw [mul_assoc]
      _ ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by
        gcongr
        rcases le_or_gt 0 d with hd | hd
        · rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          calc (1 + η') * d * (1 + η') = ((1 + η') * (1 + η')) * d := by ring
            _ ≤ (1 + η) * d := mul_le_mul_of_nonneg_right hsq1 hd
        · rw [ENNReal.ofReal_of_nonpos (by nlinarith), zero_mul]
          exact zero_le
  · rcases le_or_gt 0 d with hd | hd
    · calc ENNReal.ofReal ((1 - η) * d) * volume S
          ≤ (ENNReal.ofReal ((1 - η') * d) * ENNReal.ofReal (1 - η')) * volume S := by
            gcongr
            rw [← ENNReal.ofReal_mul (mul_nonneg (by linarith) hd)]
            apply ENNReal.ofReal_le_ofReal
            calc (1 - η) * d ≤ ((1 - η') * (1 - η')) * d := mul_le_mul_of_nonneg_right hsq2 hd
              _ = (1 - η') * d * (1 - η') := by ring
        _ = ENNReal.ofReal ((1 - η') * d) * (ENNReal.ofReal (1 - η') * volume S) := by
            rw [mul_assoc]
        _ ≤ ENNReal.ofReal ((1 - η') * d) * volume (HPol.Lm '' S) := by gcongr
        _ ≤ μ (expSet (HPol.Lm '' S)) := hEl
    ·
      obtain ⟨hE2u, hE2l⟩ := hE2 _ hmeas hsm4
      beta_reduce at hE2u hE2l
      have h3 : ENNReal.ofReal ((1 + 2) * d) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
      rw [h3, zero_mul] at hE2u
      have h0 : ENNReal.ofReal ((1 - 2) * d) * volume (HPol.Lm '' S) = 0 :=
        le_antisymm (hE2l.trans hE2u) (zero_le)
      have hpos : ENNReal.ofReal ((1 - 2) * d) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hvL : volume (HPol.Lm '' S) = 0 := (mul_eq_zero.mp h0).resolve_left hpos
      rw [hvL] at hlo
      have hpos' : ENNReal.ofReal (1 - η') ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hvS : volume S = 0 :=
        (mul_eq_zero.mp (le_antisymm hlo (zero_le))).resolve_left hpos'
      rw [hvS, mul_zero]
      exact zero_le

end ReciprocityTheory.ChartRestriction.DS
