module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeviFormWeightMetricOrthonormalDiagonal
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLtTopOfCutoff
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.CurvatureFamilyNorm
namespace GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def de2 (X : Data E r) : Wt X.Ψ r := fun _ i => if (i : ℕ) < X.p0 then -1 else 1

def frameWt (X : Data E r) (a : Wt X.Ψ r) (h : ℤ) : Wt X.Ψ r := a + h • de2 X

def IsGap (X : Data E r) (i j : Fin r) : Prop := (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ X.p0

def rd (X : Data E r) : ℝ := |(discr E : ℝ)| ^ (1 / (2 * (X.Ψ.card : ℝ)))

def RR (X : Data E r) : ℝ := rd X ^ 7

def dp (X : Data E r) : ℝ := 2 * (X.Ψ.card : ℝ) * X.p0

def g0half (r : ℕ) : ℕ := 5 ^ 4 * r

def g0 (r : ℕ) : ℕ := 2 * g0half r

def a1 (X : Data E r) : ℝ := (X.Ψ.card : ℝ) / (5 ^ 4 * rd X ^ 2)

def bb (X : Data E r) : ℝ := 5 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2

def Crh (X : Data E r) : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ)

structure Shape (X : Data E r) : Prop where
  p0_pos : 0 < X.p0
  witt : 2 * X.p0 ≤ r
  r_ge : 8 ≤ r
  D_ge : 2 ≤ nd X

structure Weights (X : Data E r) where
  shape : Shape X
  T : ℕ
  i : ℕ
  c : ℝ
  hW : ℕ
  hF : ℕ
  aK : Wt X.Ψ r
  aW : Wt X.Ψ r
  i_pos : 0 < i
  c_pos : 0 < c
  T_cols : (nd X + 2) * (2 * hW) + 2 * r ≤ T
  T_forty : 40 * (nd X + 2) ≤ T
  T_sq : 11 * nd X ^ 2 ≤ T
  cols_lo : 8 * X.Ψ.card * r + 4 ≤ 2 * hF
  cols_hi : 2 * hF ≤ 2 * hW
  Tcg : (T : ℝ) * c * g0 r ≤ 1
  cRR : (g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X ^ 2 * c ≤ 1
  b_cut : bb X < 3.8 * T - 2 * T
  b_onto : bb X ^ 2 * Crh X + bb X < 1.9 * ((nd X : ℝ) + 2) * T
  gap_big : ∀ τ a b, IsGap X a b →
    ((T : ℤ) + nd X + 2) * ((T : ℤ) + nd X + 2 + 2 * r) ≤ aK τ a - aK τ b + 2
  plus_big : ∀ τ (a : Fin r), (a : ℕ) + 1 = r → 2 * (T : ℤ) ^ 2 ≤ aK τ a
  minus_big : ∀ τ (a : Fin r), (a : ℕ) = 0 → 2 * (T : ℤ) ^ 2 ≤ -aK τ a
  gap_div : ∀ τ a b, IsGap X a b →
    aK τ a - aK τ b + 2 - ((T : ℤ) + nd X + 2) * (aW τ a - aW τ b) ∈ Set.Ico (0 : ℤ) (T + nd X + 2)
  plus_div : ∀ τ (a : Fin r), (a : ℕ) + 1 = r →
    aK τ a - ((T : ℤ) + nd X + 2) * aW τ a - ((nd X : ℤ) + 2) * (2 * hW) - 2 * r ∈
      Set.Ico (0 : ℤ) (T + nd X + 2)
  minus_div : ∀ τ (a : Fin r), (a : ℕ) = 0 →
    -aK τ a - ((T : ℤ) + nd X + 2) * (-aW τ a) ∈ Set.Ico (0 : ℤ) (T + nd X + 2)

namespace Weights

variable {X : Data E r} (w : Weights X)

def L : Wt X.Ψ r := frameWt X w.aW w.hW

def Fp : Wt X.Ψ r := frameWt X (w.aK - (w.T : ℤ) • w.aW) w.hF

def twoG₁ : Wt X.Ψ r := (2 : ℤ) • w.L - de2 X

def G₂ : Wt X.Ψ r := ((nd X : ℤ) + 4) • w.L - w.Fp

def wEt : Wt X.Ψ r := frameWt X 0 (w.i * g0half r : ℕ)

def rem : Wt X.Ψ r := w.Fp - ((nd X : ℤ) + 2) • w.L - kapW X

def c1 : ℝ := RR X * w.T * w.c * dp X ^ 2 * X.p0 / 2

def t : ℝ := 1 + w.c1 / a1 X

end Weights

def lev (X : Data E r) (x0 : Frame X.Ψ r) (u : Frame X.Ψ r → ℝ) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((u (cpt X x0 y) : ℝ) : ℂ)) z ξ).re

def curv (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  lev X x0 (phla X la) z ξ

def curvDe (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  curv X x0 (de2 X) z ξ / 2

def omRh (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z ξ).re

def IsInv (X : Data E r) (u : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (rmul x b) = u x) ∧ ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, u (lact γ x) = u x

def famNorm (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm la (w j) x ^ 2)

structure ThetaInputs (X : Data E r) extends Weights X where

  N : ℕ
  w : Fin N → Frame X.Ψ r → ℂ
  et : Frame X.Ψ r → ℂ
  th₁ : Frame X.Ψ r → ℂ
  th₂ : Frame X.Ψ r → ℂ
  thp : Frame X.Ψ r → ℂ
  phi : Frame X.Ψ r → ℝ
  mu : ℝ
  ps0 : Frame X.Ψ r → ℝ
  w_cusp : ∀ j, w j ∈ X.SS toWeights.L
  et_bdd : X.IsBddSec toWeights.wEt et
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  th₁_cusp : th₁ ∈ X.SS toWeights.twoG₁
  th₁_ne : ∃ x ∈ X.dom, th₁ x ≠ 0
  th₂_cusp : th₂ ∈ X.SS toWeights.G₂
  th₂_ne : ∃ x ∈ X.dom, th₂ x ≠ 0
  thp_cusp : thp ∈ X.SS toWeights.Fp
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0
  phi_inv : IsInv X phi
  phi_nonneg : ∀ x ∈ X.dom, 0 ≤ phi x
  phi_lower : ∀ x ∈ X.dom, X.la1 x < Real.sqrt X.Ψ.card * Real.exp (-mu) →
    1 ≤ 4 * RR X * dp X ^ 2 * X.la1 x ^ 2 * phi x
  phi_upper : ∀ x ∈ X.dom, 2 * X.la1 x ^ 2 * phi x ≤ X.p0 * dp X ^ 2
  w_lower : ∃ C : ℝ, ∀ x ∈ X.dom, Real.exp (-(C + c * phi x)) ≤ famNorm X toWeights.L w x
  et_upper : ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm toWeights.wEt et x ≤ Real.exp (-(i * (phi x - C)))
  potential_smooth : ContDiffOn ℝ ∞ ps0 X.dom
  potential_invariant : IsInv X ps0
  potential_bounded : ∃ C : ℝ, ∀ x ∈ X.dom, ps0 x ≤ C
  curvature_lower_bound : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, -(r * curvDe X x0 z ξ) ≤ lev X x0 ps0 z ξ
  potential_decay : ∃ A : ℝ, ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ, X.IsIso ξ →
    (∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
    ps0 x ≤ C + A * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a1 X * ⨅ τ, X.tt ξ x τ
  curv_L : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, ξ ≠ 0 → 0 < curv X x0 toWeights.L z ξ
  curv_G₁ : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, ξ ≠ 0 →
    curvDe X x0 z ξ < curv X x0 toWeights.L z ξ
  margin_cut : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    curv X x0 toWeights.L z ξ + 3.8 * T * omRh X x0 z ξ ≤
      curv X x0 ((2 : ℤ) • toWeights.L + toWeights.rem) z ξ
  margin_twist : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    curv X x0 toWeights.L z ξ + (3.8 * T - 2 * T) * omRh X x0 z ξ ≤
      curv X x0 ((2 : ℤ) • toWeights.L + toWeights.rem) z ξ - toWeights.t * r * curvDe X x0 z ξ
  margin_onto : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    1.9 * ((nd X : ℝ) + 2) * T * omRh X x0 z ξ ≤ curv X x0 (toWeights.Fp - kapW X) z ξ

end

end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm

namespace GlobalTheory.FrameThetaCompare

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cpt_contDiff (X : Data E r) (x0 : Frame X.Ψ r) : ContDiff ℂ ∞ (cpt X x0) :=
  contDiff_pi.2 fun τ => contDiff_pi.2 fun a => contDiff_pi.2 fun c => IW.cpt_entry_cd X x0 τ a c

theorem chart_smooth (X : Data E r) {u : Frame X.Ψ r → ℝ} (hu : ContDiffOn ℝ ∞ u X.dom)
    (x0 : Frame X.Ψ r) : ContDiffOn ℝ ∞ (fun z => u (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom} :=
  hu.comp ((cpt_contDiff X x0).restrict_scalars ℝ).contDiffOn fun _ hz => hz

theorem contDiffOn_frame {Ψ : Finset (E →+* ℂ)} {g : Frame Ψ r → ℂ} {U : Set (Frame Ψ r)}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) : ContDiffOn ℂ ∞ g U := by
  let n := Module.finrank ℂ (Frame Ψ r)
  let e : Frame Ψ r ≃L[ℂ] V n := ContinuousLinearEquiv.ofFinrankEq (by simp [n, V])
  have h := contDiffOn_of_differentiableOn n (g ∘ e.symm) (e.symm ⁻¹' U)
    (hU.preimage e.symm.continuous) (hg.comp e.symm.differentiableOn fun _ h => h)
  refine (h.comp e.contDiff.contDiffOn fun x hx => by simpa using hx).congr fun x _ => by simp

theorem smooth_of_chart (X : Data E r) {u : Frame X.Ψ r → ℝ}
    (hinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (rmul x b) = u x)
    (hu : ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => u (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}) :
    ContDiffOn ℝ ∞ u X.dom := by
  intro x hx
  obtain ⟨x1, ho, b, hb, hxb⟩ := ortho_holds r X _ hx
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, -, hsplit, hin⟩ := lu_holds r X x1 ho
  have h0 := hin 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero, ← hxb] at h0
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hz : ContDiffOn ℂ ∞ zOf {x | x ∈ X.dom ∧ Δ x ≠ 0} := by
    rw [contDiffOn_piLp]
    intro i
    exact contDiffOn_frame hU ((differentiableOn_piLp 2).1 hzd i)
  have h1 : ContDiffOn ℝ ∞ u {x | x ∈ X.dom ∧ Δ x ≠ 0} := by
    refine ((hu x1 (IW.orth_mem_dom X x1 ho)).comp (hz.restrict_scalars ℝ)
      fun y hy => (hsplit y hy.1 hy.2).1).congr fun y hy => ?_
    obtain ⟨k1, k2, k3⟩ := hsplit y hy.1 hy.2
    show u y = u (cpt X x1 (zOf y))
    rw [← hinv _ k1 _ k2, ← k3]
  exact (h1.contDiffAt (hU.mem_nhds ⟨hx, h0.1⟩)).contDiffWithinAt

theorem levi_transfer (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom) :
    ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧
      Function.Injective D ∧ ∀ (la : Wt X.Ψ r) (u : Frame X.Ψ r → ℝ),
        (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
          u (rmul x b) = u x + Real.log (Complex.normSq (bchar la b))) →
        ContDiffAt ℝ 2 (fun w => u (cpt X x1 w)) 0 →
        ∀ ξ, lev X x0 u z ξ = lev X x1 u 0 (D ξ) := by
  obtain ⟨x1, ho, b, hb, hxb⟩ := ortho_holds r X _ hz
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero, ← hxb] at h0
  have hcd : Differentiable ℂ (cpt X x0) := (cpt_contDiff X x0).differentiable (by simp)
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter
      (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hdet := GlobalTheory.FrameMeasureClosed.kapGG_holds r X x0 x1 1 U Φ bf hU hΦ (fun w hw =>
    ⟨hw.1, (hsplit _ hw.1 hw.2).2.1, by
      rw [LeviTransfer.left_act_one]; exact (hsplit _ hw.1 hw.2).2.2⟩) z hzU
  have hdet' : (fderiv ℂ Φ z).det ≠ 0 := by
    rw [hdet]; exact LeviTransfer.borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hinj : Function.Injective (fderiv ℂ Φ z) := by
    have hu : IsUnit ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet')
    exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hu)
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  refine ⟨x1, (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).toLinearMap ∘ₗ
    ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.toLinearMap, ho, ?_, ?_⟩
  · exact (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).injective.comp
      (hinj.comp (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.injective)
  intro la u hu hg0 ξ
  have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
    classical
    intro w hw
    unfold bchar
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
      fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
      fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
    have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
      differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
    have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
      differentiableAt_zpow.2 (Or.inl (LeviTransfer.borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
    exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
  have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
    (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
  have hne : bchar la (bf z) ≠ 0 := LeviTransfer.borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hev : (fun w => ((u (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((u (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
    rw [← hu _ h1 _ h2, ← h3]
  have hg : ContDiffAt ℝ 2 (fun w => u (cpt X x1 w)) (Φ z) := by rwa [hΦz]
  have h1 : ContDiffAt ℝ 2 (fun w => u (cpt X x1 (Φ w))) z :=
    hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
    (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
  have hgC : ContDiffAt ℝ 2 (fun w => ((u (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
  have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
  rw [hΦz] at hc
  unfold lev
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
    HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
  exact congrArg Complex.re hc

def diagForm (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ) : ℝ :=
  ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 *
    ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2

theorem transfer (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom) :
    ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧
      Function.Injective D ∧
      (∀ la ξ, curv X x0 la z ξ = curv X x1 la 0 (D ξ)) ∧
      (∀ la ξ, curv X x0 la z ξ = diagForm X la (D ξ)) ∧
      ∀ u : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (rmul x b) = u x) →
        ContDiffOn ℝ ∞ u X.dom → ∀ ξ, lev X x0 u z ξ = lev X x1 u 0 (D ξ) := by
  obtain ⟨x1, D, ho, hD, h⟩ := levi_transfer X x0 z hz
  have h0 := IW.zero_mem_OmF X x1 ho
  have h1 : ∀ la ξ, curv X x0 la z ξ = curv X x1 la 0 (D ξ) := fun la =>
    h la _ (fun x hx b hb => LeviTransfer.metric_rmul GlobalTheory.NormFactor.nfac_transform.1 X la hx hb)
      ((IW.phla_cpt_cdAt X x1 h0 la).of_le HE.two_le_inf)
  refine ⟨x1, D, ho, hD, h1, fun la ξ => (h1 la ξ).trans
    (GlobalTheory.LeviZero.levi_phla_zero r X la x1 ho _), fun u hu hs => h 0 u
      (fun x hx b hb => by simp [hu x hx b hb, bchar]) ?_⟩
  exact ((chart_smooth X hs x1).contDiffAt ((ExF.isOpen_OmF X x1).mem_nhds h0)).of_le HE.two_le_inf

theorem diagForm_lin (X : Data E r) (a b : ℤ) (la la' : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ) :
    diagForm X (a • la + b • la') ξ = a * diagForm X la ξ + b * diagForm X la' ξ := by
  simp only [diagForm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem curv_lin (X : Data E r) {x0 : Frame X.Ψ r} {z : V (nd X)} (hz : cpt X x0 z ∈ X.dom)
    (a b : ℤ) (la la' : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ) :
    curv X x0 (a • la + b • la') z ξ = a * curv X x0 la z ξ + b * curv X x0 la' z ξ := by
  obtain ⟨x1, D, -, -, -, h, -⟩ := transfer X x0 z hz
  rw [h, h, h, diagForm_lin]

theorem curvDe_eq_omRh (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) : curvDe X x0 z ξ = omRh X x0 z ξ := by
  obtain ⟨x1, D, -, -, -, h, -⟩ := transfer X x0 z hz
  have e : omRh X x0 z ξ = curv X x0 (CurvMargin.blockWt X) z ξ := CurvMargin.leviRh_eq X x0 ho hz ξ
  rw [e, curvDe, h, h, diagForm, diagForm, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [de2, CurvMargin.blockWt]
  split_ifs <;> push_cast <;> ring

theorem margin_of_gaps (X : Data E r) (hp : 0 < X.p0) (la : Wt X.Ψ r) (m : ℝ)
    (hgap : ∀ τ a b, IsGap X a b → la τ b ≤ la τ a)
    (hpair : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) + 1 = r → m ≤ (la τ b : ℝ) - la τ a)
    {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (ξ : Fin (nd X) → ℂ) : m * omRh X x0 z ξ ≤ curv X x0 la z ξ := by
  have mono : ∀ τ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k → ((j : ℕ) < X.p0 ∨ X.p0 ≤ (i : ℕ)) →
      la τ j ≤ la τ i := by
    intro τ k
    induction k with
    | zero => intro i j h _; rw [show j = i from Fin.ext h]
    | succ k ih =>
      intro i j h h'
      have hl : (i : ℕ) + k < r := by have := j.isLt; omega
      exact (hgap τ ⟨i + k, hl⟩ j ⟨h, by omega⟩).trans (ih i ⟨i + k, hl⟩ rfl (by simp only; omega))
  refine (CurvMargin.curv_and_margin GlobalTheory.LeviZero.levi_phla_zero
    (LeviTransfer.levi_transfer GlobalTheory.FrameMeasureClosed.kapGG_holds
      GlobalTheory.NormFactor.nfac_transform)).2 r X la m
    (fun τ i j hij hj => mono τ (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega) (Or.inl hj))
    (fun τ i j hi hij => mono τ (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega) (Or.inr hi))
    (fun τ i j hi hj => ?_) x0 ho z hz ξ
  have hr : 0 < r := i.pos
  have h1 := mono τ i ⟨0, hr⟩ i (by simp) (Or.inl hi)
  have h2 := mono τ (r - 1 - j) j ⟨r - 1, by omega⟩ (by have := j.isLt; simp only; omega) (Or.inr hj)
  have h3 := hpair τ ⟨0, hr⟩ ⟨r - 1, by omega⟩ rfl (by simp only; omega)
  have h1' : (la τ i : ℝ) ≤ la τ ⟨0, hr⟩ := by exact_mod_cast h1
  have h2' : (la τ ⟨r - 1, by omega⟩ : ℝ) ≤ la τ j := by exact_mod_cast h2
  linarith

theorem curvDe_nonneg (X : Data E r) {x0 : Frame X.Ψ r} {z : V (nd X)} (hz : cpt X x0 z ∈ X.dom)
    (ξ : Fin (nd X) → ℂ) : 0 ≤ curvDe X x0 z ξ := by
  obtain ⟨x1, D, -, -, -, h, -⟩ := transfer X x0 z hz
  rw [curvDe, h, diagForm]
  refine div_nonneg (Finset.sum_nonneg fun e _ => mul_nonneg ?_ (by positivity)) two_pos.le
  have : (e.2.1.2 : ℕ) < e.2.1.1 := e.2.2
  simp only [de2, sgn]
  split_ifs <;> first | omega | norm_num

section Weights

variable {X : Data E r} (w : Weights X)

end Weights

theorem isInv_iff (X : Data E r) (u : Frame X.Ψ r → ℝ) : IsInv X u ↔ IsInvFn X u := by
  constructor
  · rintro ⟨h1, h2⟩ γ hγ x hx b hb
    rw [h2 γ hγ _ (OrthogonalFrameDomain.rmul_mem_dom X hx hb), h1 x hx b hb]
  · intro h
    refine ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
    · simpa only [LeviTransfer.left_act_one] using h 1 X.Γ.one_mem x hx b hb
    · simpa only [ExtFPf.rmul_oneF] using h γ hγ x hx _ (ExtFPf.oneF_mem X)

theorem mem_SS_iff (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) :
    P ∈ X.SS la ↔ P ∈ X.SSgt la 0 := ⟨ss_sub_ssgt0 X la, fun h => h.1⟩

theorem pnorm_nonneg (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    0 ≤ X.pnorm la P x := by
  unfold Data.pnorm
  positivity

theorem lower_iff (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) (c : ℝ)
    (ph : Frame X.Ψ r → ℝ) :
    (∃ C : ℝ, ∀ x ∈ X.dom, Real.exp (-(C + c * ph x)) ≤ famNorm X la w x) ↔
      ∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * ph x)) ≤ K * ∑ k, X.pnorm la (w k) x ^ 2 := by
  have hs : ∀ x, 0 ≤ ∑ k, X.pnorm la (w k) x ^ 2 := fun x => by positivity
  have he : ∀ C x, Real.exp (-(2 * c * ph x)) = Real.exp (2 * C) * Real.exp (-(C + c * ph x)) ^ 2 :=
    fun C x => by rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  constructor
  · rintro ⟨C, h⟩
    refine ⟨Real.exp (2 * C), fun x hx => ?_⟩
    rw [he C]
    exact mul_le_mul_of_nonneg_left ((Real.le_sqrt (Real.exp_pos _).le (hs x)).1 (h x hx))
      (Real.exp_pos _).le
  · rintro ⟨K, h⟩
    refine ⟨K / 2, fun x hx => (Real.le_sqrt (Real.exp_pos _).le (hs x)).2 ?_⟩
    have h1 := h x hx
    rw [he (K / 2)] at h1
    have h2 : K ≤ Real.exp (2 * (K / 2)) := by have := Real.add_one_le_exp (2 * (K / 2)); linarith
    exact le_of_mul_le_mul_left (h1.trans (mul_le_mul_of_nonneg_right h2 (hs x))) (Real.exp_pos _)

theorem upper_iff (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {i : ℕ} (hi : 0 < i)
    (ph : Frame X.Ψ r → ℝ) :
    (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ Real.exp (-(i * (ph x - C)))) ↔
      ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ K * Real.exp (-(2 * i * ph x)) := by
  have he : ∀ C x, Real.exp (-(i * (ph x - C))) ^ 2 =
      Real.exp (2 * i * C) * Real.exp (-(2 * i * ph x)) :=
    fun C x => by rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  constructor
  · rintro ⟨C, h⟩
    refine ⟨Real.exp (2 * i * C), fun x hx => ?_⟩
    rw [← he C]
    exact pow_le_pow_left₀ (pnorm_nonneg X la P x) (h x hx) 2
  · rintro ⟨K, h⟩
    refine ⟨K / (2 * i), fun x hx => ?_⟩
    refine (pow_le_pow_iff_left₀ (pnorm_nonneg X la P x) (Real.exp_pos _).le two_ne_zero).1 ?_
    rw [he, mul_div_cancel₀ _ (by positivity)]
    have h2 : K ≤ Real.exp K := by have := Real.add_one_le_exp K; linarith
    exact (h x hx).trans (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)

theorem bdd_of_upper (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (i : ℕ)
    {ph : Frame X.Ψ r → ℝ} (h0 : ∀ x ∈ X.dom, 0 ≤ ph x)
    (h : ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ Real.exp (-(i * (ph x - C)))) :
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C := by
  obtain ⟨C, h⟩ := h
  refine ⟨Real.exp (i * C), fun x hx => (h x hx).trans (Real.exp_le_exp.2 ?_)⟩
  have : 0 ≤ (i : ℝ) * ph x := mul_nonneg (Nat.cast_nonneg _) (h0 x hx)
  linarith

theorem card_pos {X : Data E r} (h : 2 ≤ nd X) : 0 < X.Ψ.card := by
  have : 0 < nd X := by omega
  obtain ⟨e⟩ := Fintype.card_pos_iff.1 this
  exact Finset.card_pos.2 ⟨e.1.1, e.1.2⟩

section Clauses

variable {X : Data E r} (I : ThetaInputs X)

end Clauses

end

end GlobalTheory.FrameThetaCompare
