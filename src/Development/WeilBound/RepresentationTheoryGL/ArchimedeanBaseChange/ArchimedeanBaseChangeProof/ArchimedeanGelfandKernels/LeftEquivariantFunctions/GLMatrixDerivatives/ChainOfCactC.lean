module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCactB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdcB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KchainSt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCactC
noncomputable section

open MeasureTheory Matrix Finset Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.LengthGL (isOpen_GLs mem_GLs_val isCompact_G contDiffOn_lg)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fderiv_eq_zero_of_lg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Mat n → V} {R : ℝ}
    (hg : ∀ y ∈ GLs n, R < lg y → g y = 0) {y : Mat n} (hy : y ∈ GLs n) (hR : R < lg y) : fderiv ℝ g y = 0 := by
  have hN : IsOpen (GLs n ∩ lg ⁻¹' Ioi R) := contDiffOn_lg.continuousOn.isOpen_inter_preimage isOpen_GLs isOpen_Ioi
  have h0 : g =ᶠ[𝓝 y] fun _ => (0 : V) :=
    eventually_of_mem (hN.mem_nhds ⟨hy, hR⟩) fun w hw => hg w hw.1 hw.2
  rw [h0.fderiv_eq]
  exact fderiv_const_apply 0

theorem continuousOn_Rd {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : Mat n → V}
    (hg : ContDiffOn ℝ ∞ g (GLs n)) (X : Mat n) : ContinuousOn (Rd X g) (GLs n) := by
  have h1 : ContinuousOn (fderiv ℝ g) (GLs n) := hg.continuousOn_fderiv_of_isOpen isOpen_GLs (by simp)
  have h2 : ContinuousOn (fun y : Mat n => y * X) (GLs n) := (cdo_mul contDiffOn_id contDiffOn_const).continuousOn
  exact h1.clm_apply h2

theorem ibpAct : IBPAct := by
  intro _hU hRc n _ _ μ _ E k f hk hkc hf X x hx
  have hmap : MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n) := fun y hy => mul_mem hx hy
  have hxy : ContDiffOn ℝ ∞ (fun y : Mat n => x * y) (GLs n) := cdo_mul contDiffOn_const contDiffOn_id
  have hkr : ContDiffOn ℝ ∞ (fun y => (k y).restrictScalars ℝ) (GLs n) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).contDiff.comp_contDiffOn hk
  have hF : ContDiffOn ℝ ∞ (fun y : Mat n => k y (f (x * y))) (GLs n) := hkr.clm_apply (hf.comp hxy hmap)
  obtain ⟨R, hR⟩ := hkc
  have hFc : Cpt (fun y : Mat n => k y (f (x * y))) := ⟨R, fun y hy h => by simp [hR y hy h]⟩
  have h0 := (hRc n).2.2 μ E.V (fun y : Mat n => k y (f (x * y))) hF hFc X
  have hdF : ∀ y ∈ GLs n, Rd X (fun y : Mat n => k y (f (x * y))) y =
      Rd X k y (f (x * y)) + k y (Rd X f (x * y)) := by
    intro y hy
    have hk' : HasFDerivAt k (fderiv ℝ k y) y :=
      ((hk.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hy)).hasFDerivAt
    have hk2 : HasFDerivAt (fun y => (k y).restrictScalars ℝ)
        ((ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).comp (fderiv ℝ k y)) y :=
      (ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).hasFDerivAt.comp y hk'
    have hf' : HasFDerivAt f (fderiv ℝ f (x * y)) (x * y) :=
      ((hf.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds (hmap hy))).hasFDerivAt
    have hg : HasFDerivAt (fun y : Mat n => f (x * y)) ((fderiv ℝ f (x * y)).comp (mulL x)) y :=
      hf'.comp y (mulL x).hasFDerivAt
    have hFD := hk2.clm_apply hg
    have e1 : Rd X (fun y : Mat n => k y (f (x * y))) y =
        k y (fderiv ℝ f (x * y) (x * (y * X))) + (fderiv ℝ k y (y * X)) (f (x * y)) := by
      exact (congrArg (fun L => L (y * X)) hFD.fderiv).trans rfl
    rw [e1, ← Matrix.mul_assoc]
    show _ = fderiv ℝ k y (y * X) (f (x * y)) + k y (fderiv ℝ f (x * y) (x * y * X))
    exact add_comm _ _
  have hK := isCompact_G (n := n) R
  have hA : Integrable (fun y : G n => Rd X k y.val (f (x * y.val))) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK fun y hy => ?_)
    · have hc : ContinuousOn (fun y : Mat n => Rd X k y (f (x * y))) (GLs n) :=
        (continuousOn_Rd hk X).clm_apply (hf.continuousOn.comp hxy.continuousOn hmap)
      exact hc.comp_continuous Units.continuous_val mem_GLs_val
    · have : fderiv ℝ k y.val = 0 := fderiv_eq_zero_of_lg hR (mem_GLs_val y) (lt_of_not_ge hy)
      simp [Rd, this]
  have hB : Integrable (fun y : G n => k y.val (Rd X f (x * y.val))) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK fun y hy => ?_)
    · have hc : ContinuousOn (fun y : Mat n => k y (Rd X f (x * y))) (GLs n) :=
        hk.continuousOn.clm_apply ((continuousOn_Rd hf X).comp hxy.continuousOn hmap)
      exact hc.comp_continuous Units.continuous_val mem_GLs_val
    · simp [hR y.val (mem_GLs_val y) (lt_of_not_ge hy)]
  have hsum : ∫ y : G n, Rd X (fun y : Mat n => k y (f (x * y))) y.val ∂μ =
      ∫ y : G n, Rd X k y.val (f (x * y.val)) ∂μ + ∫ y : G n, k y.val (Rd X f (x * y.val)) ∂μ := by
    rw [← integral_add hA hB]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hdF y.val (mem_GLs_val y))
  rw [hsum] at h0
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h0

end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdcC
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulLL (a : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)

theorem hb_conj_back' (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) :
    (k.1)ᴴ * (k.1 * X * (k.1)ᴴ) * k.1 = X := by
  rw [show (k.1)ᴴ * (k.1 * X * (k.1)ᴴ) * k.1 = (k.1)ᴴ * (((k.1 * X * (k.1)ᴴ)) * k.1) by simp only [Matrix.mul_assoc],
    hb_conj_back]

theorem kapEquiv : KapEquiv := by
  intro n lam E Fr ε ι S Γ T h k hk hkK
  have hopen := isOpen_GLs (n := n)
  have hkd : ∀ y ∈ GLs n, DifferentiableAt ℝ k y := fun y hy =>
    (hk.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hy)
  have hcont := hk.continuousOn_fderiv_of_isOpen hopen (by simp)
  refine ⟨?_, ?_, ?_⟩
  · unfold kapL
    apply continuousOn_finsetSum
    intro p _
    apply continuousOn_const.mul
    apply ContinuousOn.add
    · unfold Ld
      exact (hcont.clm_apply (mulLL (hb p)).continuous.continuousOn).neg
    · exact continuousOn_const.mul hk.continuousOn
  · unfold kapR
    apply continuousOn_finsetSum
    intro p _
    apply ContinuousOn.add
    · unfold Rd
      exact (hcont.clm_apply (mulRL (hb p)).continuous.continuousOn).neg.mul continuousOn_const
    · exact (hk.continuousOn.mul continuousOn_const).mul continuousOn_const
  · intro y hy k₂
    set Φ : (E.V →L[ℂ] E.V) →L[ℝ] (E.V →L[ℂ] E.V) :=
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂)).restrictScalars ℝ with hΦ
    have hyk : y * k₂.1 ∈ GLs n := mem_GLs_mul hy (unit_mem k₂)
    have hEq : (fun z => k (z * k₂.1)) =ᶠ[nhds y] fun z => Φ (k z) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      rw [hkK z hz k₂]
      rfl
    have hD : ∀ Z, fderiv ℝ k (y * k₂.1) (Z * k₂.1) = fderiv ℝ k y Z * E.ρ k₂ := fun Z =>
      fderiv_right k k₂.1 y Φ (hkd _ hyk) (hkd y hy) hEq Z
    constructor
    · have hLd : ∀ X, Ld X k (y * k₂.1) = Ld X k y * E.ρ k₂ := by
        intro X
        unfold Ld
        rw [show X * (y * k₂.1) = (X * y) * k₂.1 by rw [Matrix.mul_assoc], hD, neg_mul]
      unfold kapL
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hLd, hkK y hy k₂]
      simp only [mul_assoc, add_mul]
    · set Y : Fin n × Fin n → Mat n := fun p => k₂.1 * hb p * (k₂.1)ᴴ with hYdef
      have hRd : ∀ p, Rd (hb p) k (y * k₂.1) = Rd (Y p) k y * E.ρ k₂ := by
        intro p
        unfold Rd
        rw [show y * k₂.1 * hb p = (y * Y p) * k₂.1 by
          simp only [hYdef, Matrix.mul_assoc, unit_star_mul, Matrix.mul_one], hD]
      have hε : ∀ p, E.ρ k₂ * ε (hb p) = ε (Y p) * E.ρ k₂ := by
        intro p
        rw [eps_rho h k₂ (Y p) (conj_herm _ _ (hb_herm p)), hYdef]
        dsimp only
        rw [hb_conj_back']
      have hF : ∀ p, E.ρ k₂ * fderiv ℝ Fr 1 (hb p) = fderiv ℝ Fr 1 (Y p) * E.ρ k₂ := by
        intro p
        have := dFr_conj h k₂ (Y p)
        rw [hYdef, hb_conj_back] at this
        rw [this, ← mul_assoc, ← mul_assoc, rho_mul_inv, one_mul]
      let B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V) := LinearMap.mk₂ ℝ
        (fun H H' => -(fderiv ℝ k y (y * H')) * ε H + k y * ε H * fderiv ℝ Fr 1 H')
        (fun H₁ H₂ H' => by simp only [map_add (f := _), mul_add, add_mul]; abel)
        (fun c H H' => by simp only [map_smul, mul_smul_comm, smul_mul_assoc, smul_add])
        (fun H H₁ H₂ => by simp only [Matrix.mul_add, map_add (f := _), neg_add, add_mul, mul_add]; abel)
        (fun c H H' => by
          simp only [Matrix.mul_smul, map_smul, neg_smul, smul_mul_assoc, mul_smul_comm, smul_add, ← smul_neg])
      have hkapR : kapR ε Fr k y = ∑ p, B (hb p) (hb p) := rfl
      have hterm : ∀ p, -(Rd (hb p) k (y * k₂.1)) * ε (hb p) + k (y * k₂.1) * ε (hb p) * fderiv ℝ Fr 1 (hb p) =
          B (Y p) (Y p) * E.ρ k₂ := by
        intro p
        rw [hRd, hkK y hy k₂]
        show -(Rd (Y p) k y * E.ρ k₂) * ε (hb p) + k y * E.ρ k₂ * ε (hb p) * fderiv ℝ Fr 1 (hb p) =
          (-(fderiv ℝ k y (y * Y p)) * ε (Y p) + k y * ε (Y p) * fderiv ℝ Fr 1 (Y p)) * E.ρ k₂
        rw [neg_mul, mul_assoc (Rd (Y p) k y), hε, mul_assoc (k y), hε, mul_assoc (k y), mul_assoc (ε (Y p)), hF]
        simp only [Rd, add_mul, neg_mul, mul_assoc]
      unfold kapR
      rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.sum_mul]
      congr 1
      rw [basis_inv B k₂]
      rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HasDerivAtFderivLine
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KbCurve
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KbBase
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbBase

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def entL (a b : Fin n) : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)

theorem contDiff_entry (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) := (entL a b).contDiff

theorem contDiffAt_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → Mat n} {x : E}
    (h : ∀ a b, ContDiffAt ℝ ∞ (fun z => F z a b) x) : ContDiffAt ℝ ∞ F x :=
  contDiffAt_pi' fun a => contDiffAt_pi' fun b => h a b

theorem contDiff_det_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → Mat n)
    (h : ∀ a b, ContDiff ℝ ∞ (fun z => F z a b)) : ContDiff ℝ ∞ (fun z => (F z).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_det : ContDiff ℝ ∞ (fun y : Mat n => y.det) := contDiff_det_of id fun a b => contDiff_entry a b

theorem contDiffAt_inv {x : Mat n} (hx : x.det ≠ 0) : ContDiffAt ℝ ∞ (fun y : Mat n => y⁻¹) x := by
  refine contDiffAt_of_entries fun a b => ?_
  have e : (fun y : Mat n => y⁻¹ a b) = fun y => (y.det)⁻¹ * (y.updateRow b (Pi.single a 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  rw [e]
  refine (contDiff_det.contDiffAt.inv hx).mul (contDiff_det_of _ fun i j => ?_).contDiffAt
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry _ _

end PositivityTheory.RgBcC.LfSt.Kchain.KbBase
end
end

noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbCurve

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain.KbBase
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hasDerivAt_entry {A : ℝ → Mat n} {A' : Mat n} {t : ℝ} (h : HasDerivAt A A' t) (a b : Fin n) :
    HasDerivAt (fun s => A s a b) (A' a b) t :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 h a) b

theorem hasDerivAt_of_entry {A : ℝ → Mat n} {A' : Mat n} {t : ℝ} (h : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t) :
    HasDerivAt A A' t :=
  hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => h a b

theorem hasDerivAt_matmul {A B : ℝ → Mat n} {A' B' : Mat n} {t : ℝ} (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  apply hasDerivAt_of_entry
  intro a b
  have hsum : HasDerivAt (fun s => ∑ k, A s a k * B s k b)
      (∑ k, (A' a k * B t k b + A t a k * B' k b)) t :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_entry hA a k).mul (hasDerivAt_entry hB k b)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using hsum

theorem hasDerivAt_line (X : Mat n) : HasDerivAt (fun t : ℝ => 1 + t • X) X 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
  simp only [id, one_smul] at h
  exact h

theorem det_line_ne (X : Mat n) : ∀ᶠ t : ℝ in 𝓝 0, (1 + t • X).det ≠ 0 := by
  have hc : Continuous fun t : ℝ => (1 + t • X).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have h0 : (1 + (0:ℝ) • X).det ≠ 0 := by simp
  exact hc.continuousAt.eventually_ne h0

theorem hasDerivAt_lineInv (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (-X) 0 := by
  set B : ℝ → Mat n := fun t => (1 + t • X)⁻¹ with hB
  have hB0 : B 0 = 1 := by simp [hB]
  have hcont : ContinuousAt B 0 := by
    have hline : Continuous fun t : ℝ => (1 : Mat n) + t • X :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hdet : ContinuousAt Ring.inverse ((1 : Mat n) + (0:ℝ) • X).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (by simp)
    have h2 : ContinuousAt (fun t : ℝ => (1 : Mat n) + t • X) 0 := hline.continuousAt
    exact ContinuousAt.comp (g := Inv.inv) (f := fun t : ℝ => (1 : Mat n) + t • X)
      (continuousAt_matrix_inv _ hdet) h2
  have hlim : Tendsto (fun t => -(B t * X)) (𝓝[≠] (0:ℝ)) (𝓝 (-X)) := by
    have h1 : Tendsto (fun t => -(B t * X)) (𝓝 (0:ℝ)) (𝓝 (-(B 0 * X))) :=
      ((hcont.mul continuousAt_const).neg)
    rw [hB0, one_mul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  refine hasDerivAt_iff_tendsto_slope.mpr (hlim.congr' ?_)
  have hne : ∀ᶠ t in 𝓝[≠] (0:ℝ), (1 + t • X).det ≠ 0 :=
    (det_line_ne X).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne, self_mem_nhdsWithin] with t ht ht0
  have hinv : B t * (1 + t • X) = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)
  rw [mul_add, mul_one, Matrix.mul_smul] at hinv
  have ht0' : t ≠ 0 := ht0
  rw [slope_def_module, hB0, sub_zero, ← hinv, sub_add_cancel_left, smul_neg, smul_smul,
    inv_mul_cancel₀ ht0', one_smul]

theorem hasDerivAt_detLine (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X).det) X.trace 0 := by
  set p : Polynomial ℂ := (1 + (Polynomial.X : Polynomial ℂ) • X.map Polynomial.C).det with hp
  have hev : ∀ t : ℝ, (1 + t • X).det = p.eval (t : ℂ) := by
    intro t
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, Complex.real_smul] <;> ring
  have hd : HasDerivAt (fun y : ℝ => p.eval (y : ℂ)) (p.derivative.eval ((0:ℝ) : ℂ)) 0 :=
    (p.hasDerivAt ((0:ℝ) : ℂ)).comp_ofReal
  rw [Complex.ofReal_zero, hp, Matrix.derivative_det_one_add_X_smul] at hd
  rw [show (fun t : ℝ => (1 + t • X).det) = fun y : ℝ => p.eval (y : ℂ) from funext hev]
  exact hd

end PositivityTheory.RgBcC.LfSt.Kchain.KbCurve
end
end

noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbFr

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain PositivityTheory.RgBcC.LfSt.Kchain.KbBase
  PositivityTheory.RgBcC.LfSt.Kchain.KbCurve
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs' : IsOpen (GLs n) :=
  isOpen_compl_singleton.preimage (contDiff_det (n := n)).continuous

theorem line_mem (X : Mat n) : ∀ᶠ t : ℝ in 𝓝 0, 1 + t • X ∈ GLs n := det_line_ne X

theorem hasDerivAt_fderiv_line {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : Mat n → Z} {x : Mat n}
    (hF : DifferentiableAt ℝ F x) (v : Mat n) : HasDerivAt (fun t : ℝ => F (x + t • v)) (fderiv ℝ F x v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    simp only [id, one_smul] at h
    exact h
  exact hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

theorem diffAt_of {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : Mat n → Z} (hF : ContDiffOn ℝ ∞ F (GLs n))
    {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ F x :=
  ((hF.contDiffAt (isOpen_GLs'.mem_nhds hx)).differentiableAt (by simp))

theorem one_mem : (1 : Mat n) ∈ GLs n := by simp [GLs]

section

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem hasDerivAt_Fr_line (h : CxData lam E Fr ε ι S Γ T) (Y : Mat n) :
    HasDerivAt (fun t : ℝ => Fr (1 + t • Y)) (fderiv ℝ Fr 1 Y) 0 :=
  hasDerivAt_fderiv_line (diffAt_of h.smooth one_mem) Y

theorem conjT_line {X : Mat n} (hX : X.IsHermitian) (t : ℝ) : (1 + t • X)ᴴ = 1 + t • X := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hX.eq]
  simp

theorem frComm_at (h : CxData lam E Fr ε ι S Γ T) {X H : Mat n} (hX : X.IsHermitian) (hH : H.IsHermitian) :
    fderiv ℝ Fr 1 X * ε H = ε H * fderiv ℝ Fr 1 X - ε (X * H + H * X) ∧ Γ * fderiv ℝ Fr 1 X = fderiv ℝ Fr 1 X * Γ := by
  have hF := hasDerivAt_Fr_line h X
  constructor
  · set εc : Mat n →L[ℝ] (E.V →L[ℂ] E.V) := LinearMap.toContinuousLinearMap ε
    have hM : HasDerivAt (fun t : ℝ => (1 + t • X) * H * (1 + t • X)) (X * H + H * X) 0 := by
      have := hasDerivAt_matmul (hasDerivAt_matmul (hasDerivAt_line X) (hasDerivAt_const (0 : ℝ) H)) (hasDerivAt_line X)
      refine this.congr_deriv ?_
      simp
    have hE : HasDerivAt (fun t : ℝ => ε ((1 + t • X) * H * (1 + t • X))) (ε (X * H + H * X)) 0 :=
      εc.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hM
    have hR := hF.mul hE
    have hL := hF.const_mul (ε H)
    have e : ∀ᶠ t : ℝ in 𝓝 0, ε H * Fr (1 + t • X) = Fr (1 + t • X) * ε ((1 + t • X) * H * (1 + t • X)) := by
      filter_upwards [line_mem X] with t ht
      have := h.frε _ ht H hH
      rwa [conjT_line hX] at this
    have hL' := hL.congr_of_eventuallyEq (e.mono fun t ht => ht.symm)
    have u := hL'.unique hR
    simp only [zero_smul, add_zero, h.one, one_mul, Matrix.mul_one] at u
    rw [u]; abel
  · have hL := hF.const_mul Γ
    have hR := hF.mul_const Γ
    have e : ∀ᶠ t : ℝ in 𝓝 0, Γ * Fr (1 + t • X) = Fr (1 + t • X) * Γ := by
      filter_upwards [line_mem X] with t ht
      exact h.ΓFr _ ht
    exact (hL.congr_of_eventuallyEq (e.mono fun t ht => ht.symm)).unique hR

end

theorem frComm : FrComm := fun _ _ _ _ _ _ _ _ _ h _X _H hX hH => frComm_at h hX hH

end PositivityTheory.RgBcC.LfSt.Kchain.KbFr
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HalfOne
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.Kchain

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def HalfOne : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (σ : (Fin n × Fin n → ℝ) → Mat n), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    ∀ (d : Mat n), d ∈ GLs n → ∀ c : ℝ, ∀ v ∈ cone n, ∀ w ∈ cone n,
      ∑ i, ε (hb i) * fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (Pi.single i 1, 0) =
        ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • (Fr (σ v) * ((1 / 2 : ℂ) • ∑ p, ε (hb p) *
          (fderiv ℝ Fr 1 (hb p) * k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) + Ld (hb p) k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹))) * Γ * T * Fr (σ w)⁻¹)

def HalfTwo : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (σ : (Fin n × Fin n → ℝ) → Mat n), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    ∀ (d : Mat n), d ∈ GLs n → ∀ c : ℝ, ∀ v ∈ cone n, ∀ w ∈ cone n,
      ∑ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) * ε (hb i) =
        ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • (Fr (σ v) * ((1 / 2 : ℂ) • ∑ p,
          (Rd (hb p) k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) -
            k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) * fderiv ℝ Fr 1 (hb p))) * Γ * T * Fr (σ w)⁻¹)

end PositivityTheory.RgBcC.LfSt.Kchain
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KcDual
noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcDual

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem trace_hOf_mul (hH : HbFacts) (u u' : Fin n × Fin n → ℝ) :
    (hOf u * hOf u').trace = ∑ p, ((u p * u' p : ℝ) : ℂ) := by
  obtain ⟨-, horth, -⟩ := hH n
  simp only [hOf, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, horth, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  push_cast
  ring

theorem map_hOf {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (α : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (u : Fin n × Fin n → ℝ) : α (hOf u) = ∑ p, ((u p : ℝ) : ℂ) • α (hb p) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hOf, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e : ((u p : ℝ) : ℂ) • (hb p : Mat n) = (u p) • hb p := by
    ext a b
    simp [Complex.real_smul]
  rw [e, map_smul]
  ext v
  simp [Complex.coe_smul]

theorem dualSum (hH : HbFacts) : DualSum := by
  intro n V _ _ α β A A' hA hA' htr
  obtain ⟨-, -, hcoord, -, -, -, -, -⟩ := hH n
  set a : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun i p => coords (A i) p with ha
  set a' : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun i p => coords (A' i) p with ha'
  have eA : ∀ i, A i = hOf (a i) := fun i => (hcoord _ (hA i)).symm
  have eA' : ∀ i, A' i = hOf (a' i) := fun i => (hcoord _ (hA' i)).symm
  have h1 : a * a'ᵀ = 1 := by
    ext i j
    have := htr i j
    rw [eA i, eA' j, trace_hOf_mul hH] at this
    have hre := congrArg Complex.re this
    simp only [Complex.re_sum, Complex.ofReal_re] at hre
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    rw [hre]
    split_ifs <;> simp
  have h2 : a'ᵀ * a = 1 := mul_eq_one_comm.mp h1
  calc ∑ i, α (A i) * β (A' i)
      = ∑ i, ∑ p, ∑ q, ((a i p * a' i q : ℝ) : ℂ) • (α (hb p) * β (hb q)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eA i, eA' i, map_hOf α, map_hOf β, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [smul_mul_smul_comm]
        push_cast
        rfl
    _ = ∑ p, ∑ q, ((a'ᵀ * a) q p : ℂ) • (α (hb p) * β (hb q)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ p, α (hb p) * β (hb p) := by
        rw [h2]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [Matrix.one_apply]

end PositivityTheory.RgBcC.LfSt.Kchain.KcDual
end
end
