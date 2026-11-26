module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfC
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma gram_eq_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma gram_mul_lemma_2 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem dom_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul x b ∈ X.dom := by
  rw [X.mem_dom_iff] at hx ⊢
  intro τ
  have hN := FrameDegreeData.upper_of_bor (X := X) hb τ
  have hbd := (hb τ).1
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 hbd
  · have hd := (hx τ).2 i
    have hdiag : ∀ j, mat b τ j j ≠ 0 := by
      intro j
      rw [Matrix.det_of_upperTriangular hN] at hbd
      exact Finset.prod_ne_zero_iff.1 hbd j (Finset.mem_univ j)
    have hP0 : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => hdiag _
    have heq : dmin X.Gm (rmul x b) τ i = dmin X.Gm x τ i *
        (Complex.normSq (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
          (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) : ℂ) := by
      show lminor (gram τ.1 X.Gm (mat x τ * mat b τ)) i = _
      rw [gram_mul_lemma_2, FrameDegreeData.lminor_conj hN,
        show ∀ z w : ℂ, z * w * conj z = w * (z * conj z) from fun z w => by ring, Complex.mul_conj]
      rfl
    rw [heq, Complex.re_mul_ofReal, ← mul_assoc]
    exact mul_pos hd (Complex.normSq_pos.2 hP0)

theorem stab_mat {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
  have hst := (X.Γ_stab γ hγ).1
  ext i j
  have h := hst (Pi.single i 1) (Pi.single j 1)
  have hR : herm X.Gm (Pi.single i (1 : E)) (Pi.single j 1) = X.Gm i j := by
    simp [herm, Pi.single_apply, cc, apply_ite]
  have hL : herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single i 1)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single j 1) =
      ((γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc) i j := by
    simp only [herm, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [← hL, h, hR]

theorem gram_gam {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1) = X.Gm.map τ.1 := by
  have h := stab_mat X hγ
  rw [gram_eq_lemma]
  conv_rhs => rw [← h]
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, emb_cc]

theorem gram_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
  show gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) = _
  rw [gram_mul_lemma_2, gram_gam X hγ τ, gram_eq_lemma]

theorem dom_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  rw [X.mem_dom_iff] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
    rw [Matrix.det_mul]
    refine mul_ne_zero ?_ (hx τ).1
    have h1 : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det := by
      rw [RingHom.map_det]
      rfl
    rw [h1]
    exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units γ).ne_zero
  · have := (hx τ).2 i
    simpa only [dmin, gram_lact X hγ x τ] using this

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure LUData (X : Data E r) (x0 : Frame X.Ψ r) where
  Δ : Frame X.Ψ r → ℂ
  zOf : Frame X.Ψ r → V (nd X)
  bOf : Frame X.Ψ r → Frame X.Ψ r
  hΔ : Differentiable ℂ Δ
  dense : ∀ x ∈ X.dom, ∀ ε > 0, ∃ y ∈ Metric.ball x ε, Δ y ≠ 0
  hz : DifferentiableOn ℂ zOf {x | x ∈ X.dom ∧ Δ x ≠ 0}
  hb : DifferentiableOn ℂ bOf {x | x ∈ X.dom ∧ Δ x ≠ 0}
  split : ∀ x ∈ X.dom, Δ x ≠ 0 → zOf x ∈ OmF X x0 ∧ bOf x ∈ Bor X.Ψ r ∧
    x = rmul (cpt X x0 (zOf x)) (bOf x)
  uniq : ∀ z ∈ OmF X x0, ∀ b ∈ Bor X.Ψ r, Δ (rmul (cpt X x0 z) b) ≠ 0 ∧
    zOf (rmul (cpt X x0 z) b) = z ∧ bOf (rmul (cpt X x0 z) b) = b

theorem luData_of (hLU : LUStatement (E := E)) (X : Data E r) (x0 : Frame X.Ψ r) (hx0 : IsOrth X x0) :
    Nonempty (LUData X x0) := by
  obtain ⟨Δ, zOf, bOf, h1, h2, h3, h4, h5, h6⟩ := hLU r X x0 hx0
  exact ⟨⟨Δ, zOf, bOf, h1, h2, h3, h4, h5, h6⟩⟩

variable (X : Data E r)

def oneF : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

private lemma mem_bor_iff' {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} :
    b ∈ Bor Ψ r ↔ ∀ τ : Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 :=
  Iff.rfl

private lemma mat_rmul' {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) :
    mat (rmul x b) τ = mat x τ * mat b τ :=
  rfl

theorem oneF_mem : oneF X ∈ Bor X.Ψ r := by
  rw [mem_bor_iff']
  intro τ
  refine ⟨?_, fun a c h => ?_⟩
  · show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne (ne_of_gt h)

theorem rmul_oneF (x : Frame X.Ψ r) : rmul x (oneF X) = x := by
  funext τ
  show mat x τ * (1 : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Matrix.mul_one]
  rfl

theorem rmul_assoc (x b b' : Frame X.Ψ r) : rmul (rmul x b) b' = rmul x (rmul b b') := by
  funext τ
  show mat x τ * mat b τ * mat b' τ = mat x τ * (mat b τ * mat b' τ)
  exact Matrix.mul_assoc _ _ _

theorem upper_iff (b : Frame X.Ψ r) (τ : X.Ψ) :
    (∀ a c : Fin r, c < a → b τ a c = 0) ↔ (mat b τ).BlockTriangular id := by
  exact ⟨fun h a c hca => h a c hca, fun h a c hca => h hca⟩

theorem mul_mem {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    rmul b b' ∈ Bor X.Ψ r := by
  rw [mem_bor_iff']
  intro τ
  refine ⟨?_, ?_⟩
  · rw [mat_rmul', Matrix.det_mul]
    exact mul_ne_zero (mem_bor_iff'.1 hb τ).1 (mem_bor_iff'.1 hb' τ).1
  · refine (upper_iff X _ τ).2 ?_
    rw [mat_rmul']
    exact ((upper_iff X b τ).1 (mem_bor_iff'.1 hb τ).2).mul ((upper_iff X b' τ).1 (mem_bor_iff'.1 hb' τ).2)

def invF (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem invF_mem {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : invF X b ∈ Bor X.Ψ r := by
  rw [mem_bor_iff']
  intro τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (mem_bor_iff'.1 hb τ).1
  have e : mat (invF X b) τ = (mat b τ)⁻¹ := rfl
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
  · refine (upper_iff X _ τ).2 ?_
    rw [e]
    haveI := Matrix.invertibleOfIsUnitDet _ hu
    exact Matrix.blockTriangular_inv_of_blockTriangular ((upper_iff X b τ).1 (mem_bor_iff'.1 hb τ).2)

theorem rmul_invF {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : rmul b (invF X b) = oneF X := by
  funext τ
  show mat b τ * (mat b τ)⁻¹ = (1 : Matrix (Fin r) (Fin r) ℂ)
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (mem_bor_iff'.1 hb τ).1)

theorem diag_mul {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    rmul b b' τ i i = b τ i i * b' τ i i := by
  show (mat b τ * mat b' τ) i i = b τ i i * b' τ i i
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rfl
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [show mat b τ i k = 0 from (mem_bor_iff'.1 hb τ).2 i k h, zero_mul]
    · rw [show mat b' τ k i = 0 from (mem_bor_iff'.1 hb' τ).2 k i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem bchar_mul (la : Wt X.Ψ r) {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    bchar la (rmul b b') = bchar la b * bchar la b' := by
  unfold bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [diag_mul X hb hb' τ i, mul_zpow]

theorem bchar_oneF (la : Wt X.Ψ r) : bchar la (oneF X) = 1 := by
  simp [bchar, oneF]

variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0)

def cell : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ D.Δ x ≠ 0}

theorem cell_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hΔ : D.Δ x ≠ 0) (hb : b ∈ Bor X.Ψ r) :
    D.Δ (rmul x b) ≠ 0 ∧ D.zOf (rmul x b) = D.zOf x ∧ D.bOf (rmul x b) = rmul (D.bOf x) b := by
  obtain ⟨hz, hbx, hxe⟩ := D.split x hx hΔ
  have e : rmul x b = rmul (cpt X x0 (D.zOf x)) (rmul (D.bOf x) b) := by
    rw [← rmul_assoc X, ← hxe]
  obtain ⟨h1, h2, h3⟩ := D.uniq (D.zOf x) hz (rmul (D.bOf x) b) (mul_mem X hbx hb)
  rw [e]
  exact ⟨h1, h2, h3⟩

theorem cell_of_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (hΔ : D.Δ (rmul x b) ≠ 0) : D.Δ x ≠ 0 := by
  have hxb : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom (X := X) hx hb
  have h := (cell_rmul D hxb hΔ (invF_mem X hb)).1
  rwa [rmul_assoc X, rmul_invF X hb, rmul_oneF X] at h

theorem cpt_cell {z : V (nd X)} (hz : z ∈ OmF X x0) :
    D.Δ (cpt X x0 z) ≠ 0 ∧ D.zOf (cpt X x0 z) = z ∧ D.bOf (cpt X x0 z) = oneF X := by
  have h := D.uniq z hz (oneF X) (oneF_mem X)
  rwa [rmul_oneF X] at h


open Classical in
def P0 (la : Wt X.Ψ r) (F : V (nd X) → ℂ) (x : Frame X.Ψ r) : ℂ :=
  if x ∈ X.dom ∧ D.Δ x ≠ 0 then bchar la (D.bOf x) * F (D.zOf x) else 0

theorem poincareLift_on_chart (la : Wt X.Ψ r) (F : V (nd X) → ℂ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    P0 D la F (cpt X x0 z) = F z := by
  obtain ⟨h1, h2, h3⟩ := cpt_cell D hz
  have hd : cpt X x0 z ∈ X.dom := hz
  unfold P0
  rw [if_pos ⟨hd, h1⟩, h2, h3, bchar_oneF X, one_mul]

theorem poincareLift_borel_equivariant (la : Wt X.Ψ r) (F : V (nd X) → ℂ) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) : P0 D la F (rmul x b) = bchar la b * P0 D la F x := by
  have hxb : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom (X := X) hx hb
  unfold P0
  by_cases hΔ : D.Δ x = 0
  · have hΔ' : D.Δ (rmul x b) = 0 := by
      by_contra h
      exact cell_of_rmul D hx hb h hΔ
    rw [if_neg (fun h => h.2 hΔ'), if_neg (fun h => h.2 hΔ), mul_zero]
  · obtain ⟨h1, h2, h3⟩ := cell_rmul D hx hΔ hb
    obtain ⟨-, hbx, -⟩ := D.split x hx hΔ
    rw [if_pos ⟨hxb, h1⟩, if_pos ⟨hx, hΔ⟩, h2, h3, bchar_mul X la hbx hb]
    ring

private lemma continuous_dmin' {Ψ : Finset (E →+* ℂ)} (G : Matrix (Fin r) (Fin r) E) (τ : Ψ) (i : Fin (r + 1)) :
    Continuous (fun x : Frame Ψ r => dmin G x τ i) := by
  unfold dmin lminor
  apply Continuous.matrix_det
  apply Continuous.matrix_submatrix
  refine continuous_pi (fun a => continuous_pi (fun c => ?_))
  simp only [gram, Matrix.of_apply, hermC, col, mat]
  fun_prop

private lemma isOpen_dom_upper_bounds : IsOpen X.dom := by
  show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite (fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite (fun i => ?_)))
  · exact isOpen_ne_fun (by unfold mat; fun_prop) continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (continuous_dmin' X.Gm τ i)))

theorem isOpen_cell : IsOpen (cell D) := by
  show IsOpen (X.dom ∩ {x | D.Δ x ≠ 0})
  exact (isOpen_dom_upper_bounds (X := X)).inter (isOpen_ne_fun D.hΔ.continuous continuous_const)

theorem diffOn_prod {ι : Type*} (u : Finset ι) {g : ι → Frame X.Ψ r → ℂ} {s : Set (Frame X.Ψ r)}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (g i) s) : DifferentiableOn ℂ (fun x => ∏ i ∈ u, g i x) s := by
  classical
  revert h
  refine Finset.induction_on u (fun _ => ?_) (fun a u ha ih h => ?_)
  · simp only [Finset.prod_empty]
    exact differentiableOn_const 1
  · simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).mul (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem poincareLift_differentiableOn (la : Wt X.Ψ r) (F : V (nd X) → ℂ) (hF : DifferentiableOn ℂ F (OmF X x0)) :
    DifferentiableOn ℂ (P0 D la F) (cell D) := by
  have hsub : ∀ x ∈ cell D, D.zOf x ∈ OmF X x0 ∧ D.bOf x ∈ Bor X.Ψ r := by
    intro x hx
    have hx' : x ∈ X.dom ∧ D.Δ x ≠ 0 := hx
    have h := D.split x hx'.1 hx'.2
    exact ⟨h.1, h.2.1⟩
  have hbc : DifferentiableOn ℂ (fun x => bchar la (D.bOf x)) (cell D) := by
    unfold bchar
    refine diffOn_prod (g := fun τ x => ∏ i, D.bOf x τ i i ^ la τ i) Finset.univ (fun τ _ => ?_)
    refine diffOn_prod (g := fun i x => D.bOf x τ i i ^ la τ i) Finset.univ (fun i _ => ?_)
    refine DifferentiableOn.zpow ?_ (Or.inl (fun x hx => FrameDegreeData.bdiag_ne (X := X) (hsub x hx).2 τ i))
    have h1 := (differentiableOn_pi.1 D.hb) τ
    have h2 := (differentiableOn_pi.1 h1) i
    exact (differentiableOn_pi.1 h2) i
  have hFz : DifferentiableOn ℂ (fun x => F (D.zOf x)) (cell D) :=
    hF.comp D.hz (fun x hx => (hsub x hx).1)
  refine (hbc.mul hFz).congr (fun x hx => ?_)
  have hx' : x ∈ X.dom ∧ D.Δ x ≠ 0 := hx
  unfold P0
  rw [if_pos hx']
  rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfD
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfC
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

variable {f p q N' : ℕ}

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
  | exact WithTop.coe_le_coe.mpr le_top
  | simp

theorem sqNorm_nonneg' {m : ℕ} (g : Fin m → ℂ) : 0 ≤ sqNorm g :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhF

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

variable {f p q N' : ℕ}

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhF
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cd_nM (τ : X.Ψ) (a b : Fin r) : ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ a b := by
  show ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ a b
  unfold nmat
  by_cases h : b < a
  · simp only [dif_pos h]
    first
      | exact (EuclideanSpace.proj (𝕜 := ℂ) _).contDiff
      | fun_prop
      | exact ((EuclideanSpace.proj (𝕜 := ℂ) _).contDiff).congr fun z => rfl
  · simp only [dif_neg h]
    exact contDiff_const

theorem unipotentFrame_inv_eq_adjugate (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ)⁻¹ = (n1 X z τ).adjugate := by
  have hdet : (n1 X z τ).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [n1, nM_diag]
    · intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      exact nM_upper X z τ (show Fin.castLE X.p0_le i < Fin.castLE X.p0_le j from hij')
  rw [Matrix.inv_def, hdet]
  simp

private lemma cd_det_lemma {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ} {M : F → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun z => M z i j) : ContDiff 𝕜 ∞ fun z => (M z).det := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

private lemma cd_adj_lemma_2 {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ} {M : F → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun z => M z i j) (i j : Fin k) :
    ContDiff 𝕜 ∞ fun z => (M z).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine cd_det_lemma fun a b => ?_
  by_cases hab : a = j
  · simp only [Matrix.updateRow_apply, hab, if_true]
    exact contDiff_const
  · simp only [Matrix.updateRow_apply, hab, if_false]
    exact h a b

theorem cd_Zt (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    ContDiff ℂ ∞ fun z : V (nd X) => Zt X z τ a m := by
  have hfun : (fun z : V (nd X) => Zt X z τ a m) =
      fun z => ∑ k, Wm X z τ m k * (n1 X z τ).adjugate k a := by
    funext z
    simp only [Zt, Matrix.transpose_apply, Matrix.mul_apply, unipotentFrame_inv_eq_adjugate]
  rw [hfun]
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ ?_
  · show ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ (qI X m) (Fin.castLE X.p0_le k)
    exact cd_nM X τ _ _
  · refine cd_adj_lemma_2 (M := fun z : V (nd X) => n1 X z τ) (fun i j => ?_) k a
    show ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j)
    exact cd_nM X τ _ _

theorem cd_Am_entry (τ : X.Ψ) (a c : Fin X.p0) :
    ContDiff ℝ ∞ fun z : V (nd X) => Am X z τ a c := by
  have hZ : ∀ a m, ContDiff ℝ ∞ fun z : V (nd X) => Zt X z τ a m :=
    fun a m => (cd_Zt X τ a m).restrict_scalars ℝ
  have hfun : (fun z : V (nd X) => Am X z τ a c) = fun z =>
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a c - ∑ m, Zt X z τ a m * star (Zt X z τ c m) := by
    funext z
    simp only [Am, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hfun]
  refine contDiff_const.sub (ContDiff.sum fun m _ => (hZ a m).mul ?_)
  first
    | exact (hZ c m).star
    | exact Complex.conjCLE.contDiff.comp (hZ c m)

theorem cd_detAm (τ : X.Ψ) : ContDiff ℝ ∞ fun z : V (nd X) => (Am X z τ).det := by
  exact cd_det_lemma (M := fun z : V (nd X) => Am X z τ) fun a c => cd_Am_entry X τ a c

theorem rhF_contDiffAt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (rhF X x0) z := by
  have hfun : rhF X x0 = fun w => -∑ τ, Real.log ‖(Am X w τ).det‖ := funext (rhF_eq_sum X x0 ho)
  have hpd := (mem_OmF_iff X x0 ho z).1 hz
  rw [hfun]
  refine (ContDiffAt.sum fun τ _ => ?_).neg
  have hne : (Am X z τ).det ≠ 0 := (hpd τ).det_pos.ne'
  have h1 : ContDiffAt ℝ ∞ (fun w : V (nd X) => (Am X w τ).det) z := (cd_detAm X τ).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun w : V (nd X) => ‖(Am X w τ).det‖) z :=
    (contDiffAt_norm ℂ hne).comp z h1
  exact h2.log (norm_ne_zero_iff.2 hne)

theorem T_cd {n : ℕ} : ContDiff ℝ ∞ fun z : V n => Real.log (1 + ‖z‖ ^ 2) := by
  exact (contDiff_const.add (contDiff_norm_sq ℂ)).log fun z => by positivity

theorem eF_contDiffAt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (eF X x0) z := by
  exact (rhF_contDiffAt X x0 ho hz).add (T_cd (n := nd X)).contDiffAt

theorem isOpen_OmF (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  have hc : Continuous fun z : V (nd X) => cpt X x0 z := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    have hfun : (fun z : V (nd X) => cpt X x0 z τ a b) = fun z => ∑ k, x0 τ a k * nM X z τ k b := by
      funext z
      have h := congrFun (congrFun (mat_cpt X x0 z τ) a) b
      simpa [mat, Matrix.mul_apply] using h
    rw [hfun]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (cd_nM X τ k b).continuous
  have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
    continuous_pi fun a => continuous_pi fun b =>
      (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
    fun τ => (hmat τ).matrix_det
  have hdmin : ∀ τ i, Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    refine Continuous.matrix_det ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.submatrix_apply, FD.gram, Matrix.of_apply, FD.hermC, FD.col, mat]
    fun_prop
  have hset : OmF X x0 = ⋂ τ : X.Ψ, ({z | (mat (cpt X x0 z) τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {z | 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re}) := by
    ext z
    simp only [OmF, Set.mem_setOf_eq, X.mem_dom_iff, Set.mem_iInter, Set.mem_inter_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun ((hdet τ).comp hc) continuous_const
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp ((hdmin τ i).comp hc)))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
end
