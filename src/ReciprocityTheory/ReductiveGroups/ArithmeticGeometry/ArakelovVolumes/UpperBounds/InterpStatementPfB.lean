module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStartPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def KronHolStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ j, ∃ (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ)
      (P : Frame X.Ψ r → ℂ) (γ0 : GL (Fin r) E),
      IsOrth X x0 ∧ IsMetricW X Xa.Fp W ∧ WLower X Xa.Fp W ∧ 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X Xa.Fp P ∧
      (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ γ0 ∈ X.Γ ∧ P (lact γ0 (Fl.xs j)) ≠ 0 ∧
      ∀ γ ∈ X.Γ, ∀ j', (γ ≠ γ0 ∨ j' ≠ j) → P (lact γ (Fl.xs j')) = 0

theorem chi_ne_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have h1 := h γ hγ
  rw [h0, zero_pow hn.ne'] at h1
  exact zero_ne_one h1

theorem poin_single {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    {γ0 : GL (Fin r) E} (h0 : γ0 ∈ X.Γ) (hz : ∀ γ ∈ X.Γ, γ ≠ γ0 → P (lact γ x) = 0) :
    poin X la P x = (X.χ la γ0)⁻¹ * P (lact γ0 x) := by
  unfold poin
  rw [tsum_eq_single ⟨γ0, h0⟩ fun γ hγ => by
    rw [hz γ.1 γ.2 fun h => hγ (Subtype.ext h), mul_zero]]

theorem poin_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (hz : ∀ γ ∈ X.Γ, P (lact γ x) = 0) : poin X la P x = 0 := by
  unfold poin
  exact (tsum_congr fun γ => by rw [hz γ.1 γ.2, mul_zero]).trans tsum_zero

theorem leviO_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (fun _ => (0 : ℝ)) z ξ = 0 := by
  have h0 : ∀ k, wdb (nd X) k (fun _ : V (nd X) => (0 : ℂ)) = fun _ => 0 := fun k => by
    funext y
    simp [wdb]
  simp [leviO, leviM, leviV, wd, h0]

theorem kronHol_of_psi (hK : KronHolPsiStatement (E := E)) : KronHolStatement (E := E) := by
  intro r X Xa Fl hPD hm hL j
  obtain ⟨bb, m, hb1, hb2, hb3⟩ := hm

  obtain ⟨η, hη, hpos⟩ := Xa.posF
  have hmarg : ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 (fun _ => (0 : ℝ)) z ξ :=
    ⟨bb, m, hb1, hb2, fun x0 hx z hz ξ => by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.leviO_zero, add_zero]
      exact hb3 x0 hx z hz ξ⟩
  have heta : ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 (fun _ => (0 : ℝ)) z ξ :=
    ⟨η, hη, fun x0 hx z hz ξ => by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.leviO_zero, add_zero]
      have h1 := hpos 0 le_rfl (by rw [zero_mul]; positivity) x0
        (ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X x0 hx) z hz ξ
      rw [zero_mul, zero_mul, sub_zero, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.leviM_comb X x0 hx hz] at h1
      exact h1⟩
  obtain ⟨x0, W, bb', F, P, γ0, h1, h2, h3, -, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    hK r X Xa Fl hPD (fun _ => 0) (fun _ _ _ _ _ _ => rfl) (fun _ _ => contDiffOn_const)
      ⟨0, fun _ _ => le_rfl⟩ hmarg heta hL j
  exact ⟨x0, W, bb', F, P, γ0, h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem interp_of (hP : PoinStatement (E := E)) (hK' : KronHolPsiStatement (E := E)) :
    InterpStatement (E := E) := by
  intro r X Xa Fl hPD hm hL hSS
  have hK := ReciprocityTheory.ChartRestriction.G.AR.Up.kronHol_of_psi hK'
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.interp_of_kron X Xa.Fp Fl.xs fun j => ?_
  obtain ⟨x0, W, bb, F, P, γ0, hO, hW, hWL, hbb, hF, hIn, hBE, hPF, hγ0, hne, hzero⟩ :=
    hK r X Xa Fl hPD hm hL j

  have hIn' : InAt X x0 W bb (fun z => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z) := by
    unfold InAt at hIn ⊢
    have h1 : ∀ z, ENNReal.ofReal (‖X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z‖ ^ 2 / kaF X x0 bb z) *
        W (cpt X x0 z) = ENNReal.ofReal (‖X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j))‖ ^ 2) *
          (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := fun z => by
      rw [norm_mul, mul_pow, mul_div_assoc, ENNReal.ofReal_mul (by positivity), mul_assoc]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIn
  have hBE' : IsBEq X Xa.Fp (fun x => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * P x) :=
    ⟨(differentiableOn_const _).mul hBE.1, fun x hx b hb => by dsimp only; rw [hBE.2 x hx b hb]; ring⟩
  obtain ⟨-, hbdd, -⟩ := hP r X x0 hO hPD Xa.Fp W bb hW hWL hbb
    (fun z => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z)
    (fun x => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * P x)
    ((differentiableOn_const _).mul hF) hIn' hBE' fun z hz => by simp only [hPF z hz]
  refine ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ss_sub_ssgt0 X Xa.Fp (hSS _ hbdd), fun j' => ?_⟩
  split_ifs with hj
  · subst hj
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.poin_single X Xa.Fp _ (Fl.xs j') hγ0 fun γ hγ hγ' => by
      simp only [hzero γ hγ j' (Or.inl hγ'), mul_zero]]
    rw [div_mul_cancel₀ _ hne, inv_mul_cancel₀ (ReciprocityTheory.ChartRestriction.G.AR.Up.chi_ne_zero X Xa.Fp hγ0)]
  · exact ReciprocityTheory.ChartRestriction.G.AR.Up.poin_zero X Xa.Fp _ (Fl.xs j') fun γ hγ => by
      simp only [hzero γ hγ j' (Or.inr hj), mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfL
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Wpsi {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x : Frame X.Ψ r) : ℝ≥0∞ := by
  classical
  exact if x ∈ X.dom then ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))) else 0

theorem metricW_of (hR : NfacRmulStatement (E := E)) (hLa : NfacLactStatement (E := E))
    (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E)) {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (ψ : Frame X.Ψ r → ℝ) (hψ : IsInvFn X ψ)
    (hψs : ∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0))
    (hψb : ∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) :
    IsMetricW X la (Wpsi X la ψ) ∧ WLower X la (Wpsi X la ψ) := by
  classical

  have hlact1 : ∀ y : Frame X.Ψ r, lact (1 : GL (Fin r) E) y = y := by
    intro y; funext τ a c
    simp [lact, mat]
  have hψr : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    have h := hψ 1 X.Γ.one_mem x hx b hb
    rwa [hlact1] at h
  have hψl : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ψ (lact γ x) = ψ x := by
    intro γ hγ x hx
    have h := hψ γ hγ x hx (ExtFPf.oneF X) (ExtFPf.oneF_mem (X := X))
    rwa [ExtFPf.rmul_oneF] at h

  have hnpos : ∀ x ∈ X.dom, 0 < X.nfac la x := by
    intro x hx
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.mpr (div_ne_zero (ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.dmin_ne (X := X) hx τ _)
      (ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.dmin_ne (X := X) hx τ _))
  have hopen : IsOpen X.dom := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom (X := X)

  have hphr : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      0 < ‖bchar la b‖ ∧ phla X la (rmul x b) = phla X la x + 2 * Real.log ‖bchar la b‖ := by
    intro x hx b hb
    have hn := hnpos x hx
    have h1 := hnpos (rmul x b) (OntoS.dom_rmul (X := X) hx hb)
    rw [hR r X la x hx b hb] at h1
    have hinv : 0 < ‖bchar la b‖⁻¹ := by
      by_contra hc
      push_neg at hc
      nlinarith
    refine ⟨inv_pos.mp hinv, ?_⟩
    unfold phla
    rw [hR r X la x hx b hb, Real.log_mul hinv.ne' hn.ne', Real.log_inv]
    ring
  have hphl : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, phla X la (lact γ x) = phla X la x := by
    intro γ hγ x hx
    unfold phla
    rw [hLa r X la γ hγ x hx]

  have hψc : ContinuousOn ψ X.dom := by
    intro x hx
    obtain ⟨x1, ho, b, hb, hxe⟩ := hO r X x hx
    obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hdec, hcomp⟩ := hLU r X x1 ho
    have hn0 : nmat X (0 : V (nd X)) = ExtFPf.oneF X := by
      funext τ a c
      simp only [nmat, ExtFPf.oneF, Matrix.one_apply]
      split_ifs <;> first | rfl | (exfalso; subst_vars; exact lt_irrefl _ ‹_ < _›) | simp_all
    have hc0 : cpt X x1 0 = x1 := by
      unfold cpt
      rw [hn0, ExtFPf.rmul_oneF]
    have hΔx : Δ x ≠ 0 := by
      have h := (hcomp 0 (zero_mem_OmF (X := X) x1 ho) b hb).1
      rwa [hc0, ← hxe] at h
    have hUo : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
      hopen.inter (isOpen_ne_fun hΔ.continuous continuous_const)
    have hmap : Set.MapsTo zOf {y | y ∈ X.dom ∧ Δ y ≠ 0} (OmF X x1) :=
      fun y hy => (hdec y hy.1 hy.2).1
    have hcomp' : ContinuousOn ((fun z => ψ (cpt X x1 z)) ∘ zOf) {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
      (hψs x1 ho).continuousOn.comp hz.continuousOn hmap
    have heq : Set.EqOn ψ ((fun z => ψ (cpt X x1 z)) ∘ zOf) {y | y ∈ X.dom ∧ Δ y ≠ 0} := by
      intro y hy
      obtain ⟨hzy, hby, hye⟩ := hdec y hy.1 hy.2
      have hmem : cpt X x1 (zOf y) ∈ X.dom := hzy
      show ψ y = ψ (cpt X x1 (zOf y))
      exact (congrArg ψ hye).trans (hψr _ hmem _ hby)
    exact ((hcomp'.congr heq).continuousAt (hUo.mem_nhds ⟨hx, hΔx⟩)).continuousWithinAt
  have hphc : ContinuousOn (phla X la) X.dom := by
    show ContinuousOn (fun x => -2 * Real.log (X.nfac la x)) X.dom
    exact continuousOn_const.mul
      ((ExtFPf.nfac_contOn (X := X) la).log fun x hx => (hnpos x hx).ne')
  have hcont : ContinuousOn (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) X.dom :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (hphc.add hψc).neg)
  have hW : ∀ x ∈ X.dom, Wpsi X la ψ x = ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))) := by
    intro x hx
    simp [Wpsi, hx]
  have hWeq : Wpsi X la ψ = X.dom.piecewise
      (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ X.dom <;> simp [Wpsi, Set.piecewise, hx]
  unfold IsMetricW WLower
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hWeq]
    exact ContinuousOn.measurable_piecewise hcont continuousOn_const hopen.measurableSet
  · intro x hx b hb
    obtain ⟨hB, hph⟩ := hphr x hx b hb
    rw [hW _ (OntoS.dom_rmul (X := X) hx hb), hW x hx, hph, hψr x hx b hb,
      ← ENNReal.ofReal_div_of_pos (pow_pos hB 2)]
    congr 1
    rw [show -(phla X la x + 2 * Real.log ‖bchar la b‖ + ψ x)
        = -(phla X la x + ψ x) - Real.log (‖bchar la b‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_sub, Real.exp_log (pow_pos hB 2)]
  · intro γ hγ x hx
    rw [hW _ (OntoS.dom_lact (X := X) hγ hx), hW x hx, hphl γ hγ x hx, hψl γ hγ x hx]
  · obtain ⟨C, hC⟩ := hψb
    refine ⟨Real.exp (-C), Real.exp_pos _, fun x hx => ?_⟩
    rw [hW x hx, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hC x hx]))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FSM

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private theorem rmul_rmul' {Ψ : Finset (E →+* ℂ)} (x a b : Frame Ψ r) :
    rmul (rmul x a) b = rmul x (rmul a b) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat a τ) (mat b τ)

private theorem rmul_mem_bor_upper_bounds {Ψ : Finset (E →+* ℂ)} {a b : Frame Ψ r} (ha : a ∈ Bor Ψ r)
    (hb : b ∈ Bor Ψ r) : rmul a b ∈ Bor Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at ha hb ⊢
  intro τ
  obtain ⟨ha1, ha2⟩ := ha τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hA : Matrix.BlockTriangular (mat a τ) id := by
    intro i j h
    exact ha2 i j h
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  refine ⟨?_, fun i j h => hA.mul hB h⟩
  show (mat a τ * mat b τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero ha1 hb1

private theorem mem_bor_of_mat_eq_inv {Ψ : Finset (E →+* ℂ)} {b c : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (hc : ∀ τ, mat c τ = (mat b τ)⁻¹) : c ∈ Bor Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at hb ⊢
  intro τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hb1)
  have hI : Matrix.BlockTriangular (mat b τ)⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨?_, fun i j h => ?_⟩
  · rw [hc τ]
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hb1)).ne_zero
  · have h2 := hI h
    rw [← hc τ] at h2
    exact h2

private theorem rmul_rmul_of_mat_eq_inv {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) {b c : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (hc : ∀ τ, mat c τ = (mat b τ)⁻¹) : rmul (rmul x b) c = x := by
  simp only [Bor, Set.mem_setOf_eq] at hb
  funext τ
  have h := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat x τ * mat b τ * mat c τ = x τ
  rw [hc τ, Matrix.mul_nonsing_inv_cancel_right _ _ h]
  rfl

private theorem lact_rmul_upper_bounds {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

private theorem lact_lact' {Ψ : Finset (E →+* ℂ)} (γ δ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

private theorem lact_inv_lact_upper_bounds {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ⁻¹ (lact γ x) = x := by
  rw [lact_lact', inv_mul_cancel]
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]
  try rfl

theorem atMostOnce (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : IsFundSet X x0 FF) (y : Frame X.Ψ r) :
    ∑' γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 y) ≤ 1 := by
  unfold IsFundSet at hFF
  obtain ⟨_, hFO, hFinj, _⟩ := hFF
  have hS : ∀ w, w ∈ KU.Sset X x0 FF → ∃ z ∈ FF, ∃ b ∈ Bor X.Ψ r, w = rmul (cpt X x0 z) b := by
    intro w hw
    simp only [KU.Sset] at hw
    obtain ⟨⟨z, b⟩, ⟨hz, hb⟩, he⟩ := hw
    exact ⟨z, hz, b, hb, he.symm⟩
  have huniq : ∀ γ γ0 : X.Γ, lact γ.1 y ∈ KU.Sset X x0 FF → lact γ0.1 y ∈ KU.Sset X x0 FF →
      γ = γ0 := by
    intro γ γ0 h1 h2
    obtain ⟨z, hz, b, hb, hzb⟩ := hS _ h1
    obtain ⟨z0, hz0, b0, hb0, hzb0⟩ := hS _ h2
    have hg : γ.1 * γ0.1⁻¹ ∈ X.Γ := X.Γ.mul_mem γ.2 (X.Γ.inv_mem γ0.2)
    have hy : y = lact γ0.1⁻¹ (rmul (cpt X x0 z0) b0) := by
      rw [← hzb0, lact_inv_lact_upper_bounds]
    have hst : rmul (lact (γ.1 * γ0.1⁻¹) (cpt X x0 z0)) b0 = rmul (cpt X x0 z) b := by
      rw [← lact_rmul_upper_bounds, ← lact_lact', ← hy, hzb]
    obtain ⟨bi, hbi⟩ : ∃ c : Frame X.Ψ r, ∀ τ, mat c τ = (mat b τ)⁻¹ :=
      ⟨(fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)), fun τ => rfl⟩
    obtain ⟨bi0, hbi0⟩ : ∃ c : Frame X.Ψ r, ∀ τ, mat c τ = (mat b0 τ)⁻¹ :=
      ⟨(fun τ => ((mat b0 τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)), fun τ => rfl⟩
    have hw : cpt X x0 z = lact (γ.1 * γ0.1⁻¹) (rmul (cpt X x0 z0) (rmul b0 bi)) := by
      rw [lact_rmul_upper_bounds, ← rmul_rmul', hst, rmul_rmul_of_mat_eq_inv _ hb hbi]
    have hzz : z0 = z := hFinj z0 hz0 z hz _ hg _ (rmul_mem_bor_upper_bounds hb0 (mem_bor_of_mat_eq_inv hb hbi)) hw
    subst hzz
    have hw0 : cpt X x0 z0 ∈ X.dom := hFO hz0
    have hfix : lact (γ.1 * γ0.1⁻¹) (cpt X x0 z0) = rmul (cpt X x0 z0) (rmul b bi0) := by
      rw [← rmul_rmul', ← hst, rmul_rmul_of_mat_eq_inv _ hb0 hbi0]
    have hg1 : γ.1 * γ0.1⁻¹ = 1 := X.Γ_free _ hg _ hw0 _ (rmul_mem_bor_upper_bounds hb (mem_bor_of_mat_eq_inv hb0 hbi0)) hfix
    exact Subtype.ext (mul_inv_eq_one.mp hg1)
  by_cases hex : ∃ γ0 : X.Γ, lact γ0.1 y ∈ KU.Sset X x0 FF
  · obtain ⟨γ0, hγ0⟩ := hex
    rw [tsum_eq_single γ0]
    · rw [Set.indicator_of_mem hγ0]
      simp
    · intro γ hne
      exact Set.indicator_apply_eq_zero.mpr fun hm => absurd (huniq γ γ0 hm hγ0) hne
  · push_neg at hex
    have h0 : ∀ γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 y) = 0 :=
      fun γ => Set.indicator_apply_eq_zero.mpr fun hm => absurd hm (hex γ)
    rw [tsum_congr h0, tsum_zero]
    exact zero_le_one

end

theorem fundSetMeasStatement_of_isCMField {E : Type} [Field E] [NumberField E] [IsCMField E] :
    FundSetMeasStatement (E := E) := by
  intro r X x0 FF ho hFF ⟨x1, ho1, CechHodgeFiltration, hFF1, hfin⟩
  classical
  have := KU.countable_Γ X
  have hM := measInv_holds (E := E)
  have hS : MeasurableSet (KU.Sset X x0 FF) := KU.meas_S X ho hFF.1
  have hS1 : MeasurableSet (KU.Sset X x1 CechHodgeFiltration) := KU.meas_S X ho1 hFF1.1
  have hcpt0 := (KU.cont_cpt X x0).measurable
  have hcpt1 := (KU.cont_cpt X x1).measurable

  set Bad : Set (Frame X.Ψ r) := ⋂ γ : X.Γ, (lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration)ᶜ with hBaddef
  have hBad : MeasurableSet Bad :=
    MeasurableSet.iInter fun γ => ((KU.cont_lact X γ.1⁻¹).measurable hS1).compl
  have hBadB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul x b) = Bad.indicator 1 x := by
    intro x _ b hb
    have e : rmul x b ∈ Bad ↔ x ∈ Bad := by
      simp only [hBaddef, Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage, KU.lact_rmul',
        KU.rmul_mem_S X hb]
    by_cases h : x ∈ Bad
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (e.mpr h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (e.mp h'))]
  have h1 : ∫⁻ z, Bad.indicator 1 (cpt X x1 z) ∂muF X x1 = 0 := by
    have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x1 z) :=
      (measurable_one.indicator hBad).comp hcpt1
    rw [lintegral_eq_zero_iff hm]
    filter_upwards [KU.cover X hFF1] with z ⟨γ, hγ, hSz⟩
    have : cpt X x1 z ∉ Bad := fun h => (Set.mem_iInter.mp h ⟨γ, hγ⟩) hSz
    simp [Set.indicator_of_notMem this]
  have h0 : ∫⁻ z, Bad.indicator 1 (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [hM r X x0 x1 ho ho1 _ (measurable_one.indicator hBad) hBadB]; exact h1
  have hcov : ∀ᵐ z ∂muF X x0, cpt X x0 z ∉ Bad := by
    have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) :=
      (measurable_one.indicator hBad).comp hcpt0
    have := (lintegral_eq_zero_iff hm).mp h0
    filter_upwards [this] with z hz hb
    simp [Set.indicator_of_mem hb] at hz

  let H : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ y =>
    (KU.Sset X x0 FF).indicator 1 y * (lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration).indicator 1 y
  have hHm : ∀ γ, Measurable (H γ) := fun γ =>
    (measurable_one.indicator hS).mul (measurable_one.indicator ((KU.cont_lact X γ.1⁻¹).measurable hS1))
  have hHB : ∀ γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, H γ (rmul x b) = H γ x := by
    intro γ x _ b hb
    have e1 : rmul x b ∈ KU.Sset X x0 FF ↔ x ∈ KU.Sset X x0 FF := KU.rmul_mem_S X hb
    have e2 : rmul x b ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration ↔ x ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration := by
      simp only [Set.mem_preimage, KU.lact_rmul', KU.rmul_mem_S X hb]
    simp only [H, Set.indicator_apply, e1, e2, Pi.one_apply]
  have step1 : muF X x0 FF = ∫⁻ z, (KU.Sset X x0 FF).indicator 1 (cpt X x0 z) ∂muF X x0 := by
    rw [← lintegral_indicator_one hFF.1]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ FF
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((KU.cpt_mem_S X ho z).mpr hz)]; rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((KU.cpt_mem_S X ho z).mp h))]
  have step2 : ∫⁻ z, (KU.Sset X x0 FF).indicator 1 (cpt X x0 z) ∂muF X x0 ≤
      ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 := by
    refine lintegral_mono_ae (hcov.mono fun z hz => ?_)
    by_cases hS0 : cpt X x0 z ∈ KU.Sset X x0 FF
    · have : ∃ γ : X.Γ, cpt X x0 z ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration := by
        by_contra hn
        push_neg at hn
        exact hz (Set.mem_iInter.mpr fun γ => hn γ)
      obtain ⟨γ, hγ⟩ := this
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum γ)
      simp only [H, Set.indicator_of_mem hS0, Set.indicator_of_mem hγ, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hS0]; exact bot_le
  have step3 : ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 = ∑' γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 :=
    lintegral_tsum fun γ => ((hHm γ).comp hcpt0).aemeasurable
  have hae1 : ∀ᵐ z ∂muF X x1, z ∈ OmF X x1 := ExtFPf.ae_OmF (X := X) (x0 := x1)
  have step4 : ∀ γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, CechHodgeFiltration.indicator (fun z => (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
        (lact γ.1 (cpt X x1 z))) z ∂muF X x1 := by
    intro γ
    rw [hM r X x0 (lact γ.1 x1) ho (KU.isOrth_lact X γ.2 ho1) (H γ) (hHm γ) (hHB γ), KU.muF_lact X γ.2]
    refine lintegral_congr fun z => ?_
    rw [KU.cpt_lact]
    simp only [H]
    have e : lact γ.1 (cpt X x1 z) ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration ↔ z ∈ CechHodgeFiltration := by
      rw [Set.mem_preimage, KU.lact_lact, inv_mul_cancel, KU.lact_one, KU.cpt_mem_S X ho1]
    by_cases hz : z ∈ CechHodgeFiltration
    · rw [Set.indicator_of_mem (e.mpr hz), Set.indicator_of_mem hz, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (fun h => hz (e.mp h)), Set.indicator_of_notMem hz, mul_zero]
  have hI : ∀ γ : X.Γ, Measurable fun z => CechHodgeFiltration.indicator (fun z => (KU.Sset X x0 FF).indicator
      (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 (cpt X x1 z))) z := fun γ =>
    ((measurable_one.indicator hS).comp ((KU.cont_lact X γ.1).comp (KU.cont_cpt X x1)).measurable).indicator hFF1.1
  have step5 : ∑' γ : X.Γ, ∫⁻ z, CechHodgeFiltration.indicator (fun z => (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
      (lact γ.1 (cpt X x1 z))) z ∂muF X x1 ≤ muF X x1 CechHodgeFiltration := by
    rw [← lintegral_tsum fun γ => (hI γ).aemeasurable, ← lintegral_indicator_one hFF1.1]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ CechHodgeFiltration
    · simp only [Set.indicator_of_mem hz, Pi.one_apply]
      exact FSM.atMostOnce X ho hFF _
    · simp [Set.indicator_of_notMem hz]
  calc muF X x0 FF = _ := step1
    _ ≤ _ := step2
    _ = _ := step3
    _ = _ := tsum_congr step4
    _ ≤ muF X x1 CechHodgeFiltration := step5
    _ < ⊤ := hfin

end ReciprocityTheory.ChartRestriction.G.AR.Up.FSM

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem FundSetMeasStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    FundSetMeasStatement (E := E) := FSM.fundSetMeasStatement_of_isCMField

theorem DivStartStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    DivStartStatement (E := E) := DivSt.divStart_of FundSetMeasStatement_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

section V

variable {n : ℕ} {U : Set (V n)}

def twoLog {N M : ℕ} (a c : ℝ) (w : Fin N → V n → ℂ) (s : Fin M → V n → ℂ) (y : V n) : ℝ :=
  a * Real.log (∑ k, Complex.normSq (w k y)) + c * Real.log (∑ k, Complex.normSq (s k y))

theorem sumSq_cdAt {N : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} (hw : ∀ k, DifferentiableOn ℂ (w k) U)
    {y : V n} (hy : y ∈ U) : ContDiffAt ℝ ∞ (fun v => ∑ k, Complex.normSq (w k v)) y :=
  ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (HE.contDiffAt_of_punct hU (hw k) hy)

theorem twoLog_cdAt {N M : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} {s : Fin M → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hs : ∀ k, DifferentiableOn ℂ (s k) U) (a c : ℝ)
    {y : V n} (hy : y ∈ U) (hwp : 0 < ∑ k, Complex.normSq (w k y)) (hsp : 0 < ∑ k, Complex.normSq (s k y)) :
    ContDiffAt ℝ ∞ (twoLog a c w s) y := by
  unfold twoLog
  exact (contDiffAt_const.mul ((sumSq_cdAt hU hw hy).log hwp.ne')).add
    (contDiffAt_const.mul ((sumSq_cdAt hU hs hy).log hsp.ne'))

theorem logSum_levi_nonneg {N : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hwp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (w k y))
    {y : V n} (hy : y ∈ U) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun v => ((Real.log (∑ k, Complex.normSq (w k v)) : ℝ) : ℂ)) y ξ).re :=
  lseV n N U (fun k v => Complex.normSq (w k v)) hU
    (fun k => Or.inr ⟨w k, ((contDiffOn_of_differentiableOn n (w k) U hU (hw k)).of_le HE.two_le_inf),
      fun _ _ => rfl⟩) hwp y hy ξ

theorem twoLog_levi_nonneg {N M : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} {s : Fin M → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hwp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (w k y)) (hsp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (s k y))
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {y : V n} (hy : y ∈ U) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun v => ((twoLog a c w s v : ℝ) : ℂ)) y ξ).re := by
  have h1 : ContDiffAt ℝ 2 (fun v => Real.log (∑ k, Complex.normSq (w k v))) y :=
    ((sumSq_cdAt hU hw hy).log (hwp y hy).ne').of_le HE.two_le_inf
  have h2 : ContDiffAt ℝ 2 (fun v => Real.log (∑ k, Complex.normSq (s k v))) y :=
    ((sumSq_cdAt hU hs hy).log (hsp y hy).ne').of_le HE.two_le_inf
  have e : (fun v => ((twoLog a c w s v : ℝ) : ℂ)) = fun v =>
      ((a * Real.log (∑ k, Complex.normSq (w k v)) + c * Real.log (∑ k, Complex.normSq (s k v)) : ℝ) : ℂ) := rfl
  rw [e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h1) (contDiffAt_const.mul h2),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h1, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have := logSum_levi_nonneg hU hw hwp hy ξ
  have := logSum_levi_nonneg hU hs hsp hy ξ
  positivity

end V

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem pnorm_eq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl

theorem exp_neg_phla (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
  have hn : 0 < X.nfac la x := by
    unfold Data.nfac
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.mpr (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))
  unfold phla
  rw [neg_mul, neg_neg, show 2 * Real.log (X.nfac la x) = Real.log (X.nfac la x ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

theorem pnorm_sq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P x ^ 2 = Complex.normSq (P x) * Real.exp (-phla X la x) := by
  rw [pnorm_eq, mul_pow, exp_neg_phla X la hx, Complex.normSq_eq_norm_sq]

theorem sum_pnorm_sq {N : ℕ} (la : Wt X.Ψ r) (P : Fin N → Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∑ k, X.pnorm la (P k) x ^ 2 = (∑ k, Complex.normSq (P k x)) * Real.exp (-phla X la x) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => pnorm_sq X la (P k) hx)

theorem phla_add_nsmul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la1 la2 : Wt X.Ψ r) (k : ℕ) :
    phla X (la1 + k • la2) x = phla X la1 x + k * phla X la2 x := by
  rw [IW.phla_eq X hx, IW.phla_eq X hx, IW.phla_eq X hx, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  ring

variable {X}

def PsK (Xa : ArchInM X) (Fl : FlatM X Xa) (x : Frame X.Ψ r) : ℝ :=
  phla X (Xa.Fp + Xa.T • Xa.L) x + (Xa.T : ℝ) * Real.log (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) +
    ((Xa.T : ℝ) - 1 / 2) * Real.log ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2)

theorem sumw_pos (Xa : ArchInM X) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, Complex.normSq (Xa.w k x) := by
  obtain ⟨k, hk⟩ := Xa.w_nz x hx
  exact lt_of_lt_of_le (Complex.normSq_pos.2 hk)
    (Finset.single_le_sum (f := fun k => Complex.normSq (Xa.w k x)) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ k))

theorem sums_pos {Xa : ArchInM X} (Fl : FlatM X Xa) {x : Frame X.Ψ r} {k0 : Fin (nd X)}
    (h : Fl.s k0 x ≠ 0) : 0 < ∑ k, Complex.normSq (Fl.s k x) :=
  lt_of_lt_of_le (Complex.normSq_pos.mpr h)
    (Finset.single_le_sum (f := fun k => Complex.normSq (Fl.s k x)) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ k0))

theorem PsK_eq (Xa : ArchInM X) (Fl : FlatM X Xa) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    PsK Xa Fl x = phla X Xa.Fp x + ((1 / 2 : ℝ) * Real.log (∑ k, Complex.normSq (Xa.w k x)) +
      ((Xa.T : ℝ) - 1 / 2) * Real.log (∑ k, Complex.normSq (Fl.s k x))) := by
  have hw := sumw_pos Xa hx
  have he : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  unfold PsK
  rw [sum_pnorm_sq X _ _ hx, sum_pnorm_sq X _ _ hx, phla_add_nsmul X hx, mul_div_mul_right _ _ he.ne',
    Real.log_mul hw.ne' he.ne', Real.log_exp, Real.log_div hs.ne' hw.ne']
  ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem WSk_eq_exp (Xa : ArchInM X) (Fl : FlatM X Xa) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    WSk X Xa Fl x = ENNReal.ofReal (Real.exp (-PsK Xa Fl x)) := by
  have hw := sumw_pos Xa hx
  have he : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  have hA : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]; positivity
  have hS : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]; positivity
  have hR : 0 < (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := div_pos hS hA
  unfold WSk
  rw [if_pos hx, ENNReal.ofReal_rpow_of_pos hA, ENNReal.ofReal_rpow_of_pos hR,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hR, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold PsK
  ring

def Uk {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) : Set (V (nd X)) :=
  {z | z ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 z) ≠ 0}

theorem s_diffOn {Xa : ArchInM X} (Fl : FlatM X Xa) (k : Fin (nd X)) : DifferentiableOn ℂ (Fl.s k) X.dom :=
  (Fl.s_van k).1.1.1.1

theorem w_diffOn (Xa : ArchInM X) (k : Fin Xa.N) : DifferentiableOn ℂ (Xa.w k) X.dom :=
  (Xa.w_van k).1.1.1.1

theorem isOpen_Uk {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) :
    IsOpen (Uk Fl x0 k0) :=
  HE.isOpen_punct (ExF.isOpen_OmF X x0) (IW.comp_cpt_diffOn X (s_diffOn Fl k0) x0)

theorem PsK_cpt_eventually {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) :
    (fun v => PsK Xa Fl (cpt X x0 v)) =ᶠ[𝓝 z] fun v => phla X Xa.Fp (cpt X x0 v) +
      twoLog (1 / 2) ((Xa.T : ℝ) - 1 / 2) (fun k v => Xa.w k (cpt X x0 v)) (fun k v => Fl.s k (cpt X x0 v)) v := by
  filter_upwards [(isOpen_Uk Fl x0 k0).mem_nhds hz] with v hv
  rw [PsK_eq Xa Fl hv.1 (sums_pos Fl hv.2)]
  rfl

theorem twoLog_cpt_cdAt {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) (a c : ℝ) :
    ContDiffAt ℝ ∞ (twoLog a c (fun k v => Xa.w k (cpt X x0 v)) (fun k v => Fl.s k (cpt X x0 v))) z :=
  twoLog_cdAt (ExF.isOpen_OmF X x0) (fun k => IW.comp_cpt_diffOn X (w_diffOn Xa k) x0)
    (fun k => IW.comp_cpt_diffOn X (s_diffOn Fl k) x0) a c hz.1 (sumw_pos Xa hz.1) (sums_pos Fl hz.2)

theorem PsK_cpt_cdAt {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) : ContDiffAt ℝ ∞ (fun v => PsK Xa Fl (cpt X x0 v)) z :=
  ((IW.phla_cpt_cdAt X x0 hz.1 Xa.Fp).add (twoLog_cpt_cdAt Fl x0 k0 hz _ _)).congr_of_eventuallyEq
    (PsK_cpt_eventually Fl x0 k0 hz)

theorem PsK_levi {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) (m : ℝ)
    (hm : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ)
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) (ξ : Fin (nd X) → ℂ) :
    m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
      (leviV (nd X) (fun w => ((PsK Xa Fl (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re := by
  have hT : (0 : ℝ) ≤ (Xa.T : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ Xa.T := by
      have h1 := Xa.T_ge
      have h2 := Xa.n_ge
      have : 1 ≤ Xa.T := by nlinarith
      exact_mod_cast this
    linarith
  set tl := twoLog (1 / 2) ((Xa.T : ℝ) - 1 / 2) (fun k v => Xa.w k (cpt X x0 v))
    (fun k v => Fl.s k (cpt X x0 v)) with htl
  have hev : (fun w => ((PsK Xa Fl (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => (((phla X Xa.Fp (cpt X x0 w) + (-1) * Real.log (densF X x0 w)) + tl w : ℝ) : ℂ) := by
    filter_upwards [PsK_cpt_eventually Fl x0 k0 hz] with w hw
    rw [hw]
    push_cast
    ring
  have h1 := (IW.phla_cpt_cdAt X x0 hz.1 Xa.Fp).of_le HE.two_le_inf
  have h2 := (IW.logDens_cdAt X x0 hz.1).of_le HE.two_le_inf
  have h3 := (twoLog_cpt_cdAt Fl x0 k0 hz (1 / 2) ((Xa.T : ℝ) - 1 / 2)).of_le HE.two_le_inf
  have hU := isOpen_Uk Fl x0 k0
  have hpos : 0 ≤ (leviV (nd X) (fun v => ((tl v : ℝ) : ℂ)) z ξ).re :=
    twoLog_levi_nonneg hU (fun k => (IW.comp_cpt_diffOn X (w_diffOn Xa k) x0).mono fun v hv => hv.1)
      (fun k => (IW.comp_cpt_diffOn X (s_diffOn Fl k) x0).mono fun v hv => hv.1)
      (fun v hv => sumw_pos Xa hv.1) (fun v hv => sums_pos Fl hv.2) (by norm_num) hT hz ξ
  have hmz := hm z hz.1 ξ
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (h1.add (contDiffAt_const.mul h2)) h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h2), Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  unfold leviRh leviO leviM leviDens at hmz
  linarith

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace BigC

variable {r : ℕ}

private theorem norm_dmin_succ_div_castSucc_pos (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin r) :
    0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
  have h := (hx τ).2
  have h1 := h i.succ
  have h2 := h i.castSucc
  refine norm_pos_iff.mpr (div_ne_zero ?_ ?_)
  · intro h0
    rw [h0] at h1
    simp at h1
  · intro h0
    rw [h0] at h2
    simp at h2

private theorem nfac_pos_of_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    0 < X.nfac la x := by
  unfold Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos X hx τ i) _

private theorem phla_eq_sum_log_norm_dmin_ratio (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    phla X la x = ∑ τ, ∑ i : Fin r,
      (la τ i : ℝ) * Real.log ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ := by
  unfold phla Data.nfac
  rw [Real.log_prod (fun τ _ =>
    (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos X hx τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos X hx τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_rpow (norm_dmin_succ_div_castSucc_pos X hx τ i)]
  ring

theorem phla_sub (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) :
    phla X (la - la') x = phla X la x - phla X la' x := by
  rw [phla_eq_sum_log_norm_dmin_ratio X hx, phla_eq_sum_log_norm_dmin_ratio X hx, phla_eq_sum_log_norm_dmin_ratio X hx, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Int.cast_sub]
  ring

theorem phla_nsmul (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (k : ℕ) (la : Wt X.Ψ r) :
    phla X (k • la) x = k * phla X la x := by
  rw [phla_eq_sum_log_norm_dmin_ratio X hx, phla_eq_sum_log_norm_dmin_ratio X hx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul]
  push_cast
  ring

theorem log_pnorm_sq (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hP : P x ≠ 0) :
    Real.log (X.pnorm la P x ^ 2) = Real.log (Complex.normSq (P x)) - phla X la x := by
  have hN := nfac_pos_of_mem_dom X hx la
  have hp : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  have hn2 : Complex.normSq (P x) = ‖P x‖ ^ 2 := by
    first
      | exact Complex.normSq_eq_norm_sq _
      | exact (Complex.sq_norm _).symm
      | simp [Complex.normSq_eq_abs]
  rw [hp, mul_pow, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hP)) (pow_ne_zero _ hN.ne'), hn2,
    Real.log_pow, Real.log_pow, phla]
  ring

end BigC

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
