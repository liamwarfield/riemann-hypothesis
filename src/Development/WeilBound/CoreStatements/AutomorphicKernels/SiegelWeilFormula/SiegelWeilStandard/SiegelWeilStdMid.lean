module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.GoodSigPq
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.PolyKFinOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.GIdilFull
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.BorelTup
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CrLem
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTau
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarId
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SmoothTop

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolLeadB
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AsmH
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AsmCore
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IteratedDerivEqOfEventuallyEq
noncomputable section

open Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

theorem iteratedDeriv_eq_of_eventuallyEq {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[𝓝 s] g) (k : ℕ) :
    iteratedDeriv k f s = iteratedDeriv k g s := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ]
  exact Filter.EventuallyEq.iteratedDerivWithin_eq (by simpa using h) h.eq_of_nhds

theorem leib {U : Set ℂ} (hU : IsOpen U) : ∀ (j : ℕ) (h₁ h₂ : ℂ → ℂ), DifferentiableOn ℂ h₁ U → DifferentiableOn ℂ h₂ U →
    ∀ s ∈ U, iteratedDeriv j (fun z => h₁ z * h₂ z) s =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i h₁ s * iteratedDeriv (j - i) h₂ s := by
  intro j
  induction j with
  | zero => intro h₁ h₂ _ _ s _; simp
  | succ j ih =>
    intro h₁ h₂ hd₁ hd₂ s hs
    have hd₁' : DifferentiableOn ℂ (deriv h₁) U := hd₁.deriv hU
    have hd₂' : DifferentiableOn ℂ (deriv h₂) U := hd₂.deriv hU
    have hev : deriv (fun z => h₁ z * h₂ z) =ᶠ[𝓝 s] fun z => deriv h₁ z * h₂ z + h₁ z * deriv h₂ z := by
      filter_upwards [hU.mem_nhds hs] with z hz
      exact deriv_mul ((hd₁.differentiableAt (hU.mem_nhds hz))) ((hd₂.differentiableAt (hU.mem_nhds hz)))
    rw [iteratedDeriv_succ', iteratedDeriv_eq_of_eventuallyEq hev]
    have hc₁ : ContDiffAt ℂ j (fun z => deriv h₁ z * h₂ z) s :=
      ((hd₁'.mul hd₂).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top
    have hc₂ : ContDiffAt ℂ j (fun z => h₁ z * deriv h₂ z) s :=
      ((hd₁.mul hd₂').contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top
    have hsplit : (fun z => deriv h₁ z * h₂ z + h₁ z * deriv h₂ z) =
        (fun z => deriv h₁ z * h₂ z) + (fun z => h₁ z * deriv h₂ z) := rfl
    rw [hsplit, iteratedDeriv_add hc₁ hc₂, ih _ _ hd₁' hd₂ s hs, ih _ _ hd₁ hd₂' s hs]
    have key := Finset.sum_choose_succ_mul (R := ℂ) (fun a b => iteratedDeriv a h₁ s * iteratedDeriv b h₂ s) j
    simp only [mul_assoc] at key ⊢
    rw [key, add_comm]
    congr 1
    all_goals
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      (try rw [← iteratedDeriv_succ']); (try rw [show j + 1 - i = j - i + 1 by omega])

end PositivityTheory.Rg.Sw.HSt
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ExpLie : Prop := ∀ (n : ℕ) (x Z : M2 n) (t : ℝ), InG x →
  InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) ∧
  InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))

theorem lift_mR' (φ : GR n → ℂ) (y : GR n) : lift φ (mR y) = φ y := by
  have h : IsUnit (mR y) ∧ InG (mR y) := ⟨y.1.isUnit, y.2⟩
  unfold lift
  rw [dite_eq_left h]
  congr 1
  ext : 2
  rfl

theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x :=
  (Matrix.isUnit_iff_isUnit_det x).2 (PositivityTheory.Rg.Sw.Glob.DenseP.isUnit_det_of_inG hx)

def toGR (x : M2 n) (hx : InG x) : GR n := ⟨(isUnit_of_inG hx).unit, hx⟩

theorem mR_toGR (x : M2 n) (hx : InG x) : mR (toGR x hx) = x := rfl

theorem rC_const_mul (Z : M2 n) (a : ℂ) (F : M2 n → ℂ) (x : M2 n) :
    rC Z (fun x => a * F x) x = a * rC Z F x := by
  unfold rC
  rw [deriv_const_mul_field', deriv_const_mul_field']
  ring

theorem rC_zero (Z : M2 n) (x : M2 n) : rC Z (fun _ => (0 : ℂ)) x = 0 := by
  unfold rC
  simp

def Van (j : ℕ) (h : ℂ → ℂ) (s : ℂ) : Prop := ∀ k ≤ j, iteratedDeriv k h s = 0

theorem van_mul {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {q h : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hh : DifferentiableOn ℂ h U) {j : ℕ} (hv : Van j h s) : Van j (fun z => q z * h z) s := by
  intro k hk
  rw [leib hU k q h hq hh s hs]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hv (k - i) (by omega)]
  simp

theorem van_sum {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {ι : Type} (S : Finset ι) (h : ι → ℂ → ℂ)
    (hd : ∀ l, DifferentiableOn ℂ (h l) U) {j : ℕ} (hv : ∀ l, Van j (h l) s) : Van j (fun z => ∑ l ∈ S, h l z) s := by
  classical
  induction S using Finset.induction_on with
  | empty => intro k _; simp
  | insert a S ha ih =>
    intro k hk
    have e : (fun z => ∑ l ∈ insert a S, h l z) = (fun z => h a z) + (fun z => ∑ l ∈ S, h l z) := by
      funext z; simp [Finset.sum_insert ha]
    have hds : DifferentiableOn ℂ (fun z => ∑ l ∈ S, h l z) U := by
      exact DifferentiableOn.fun_sum (fun l _ => hd l)
    rw [e, iteratedDeriv_add (((hd a).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top)
      ((hds.contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top), hv a k hk, ih k hk, add_zero]

theorem iter_mul_low {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {q h : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hh : DifferentiableOn ℂ h U) {j : ℕ} (hv : ∀ i < j, iteratedDeriv i h s = 0) :
    iteratedDeriv j (fun z => q z * h z) s = q s * iteratedDeriv j h s ∧
      ∀ i < j, iteratedDeriv i (fun z => q z * h z) s = 0 := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [leib hU j q h hq hh s hs, Finset.sum_eq_single 0]
    · simp
    · intro b hbm hb
      have := Finset.mem_range.1 hbm
      rw [hv (j - b) (by omega)]
      simp
    · intro h0; exact absurd (Finset.mem_range.2 (Nat.succ_pos j)) h0
  · rw [leib hU i q h hq hh s hs]
    refine Finset.sum_eq_zero fun b hb => ?_
    have : b < i + 1 := Finset.mem_range.1 hb
    rw [hv (i - b) (by omega)]
    simp

theorem asmH_of (hF : FarId) (hS : SmoothX) (hT : TopHol) (hR : RcCongr) (hE : ExpLie) : AsmH := by
  intro hLT hSec hCR
  intro m n e hm hmn G _ _ _ _ _ _ Pp Γ ι s₀ Ht f hι hsplit U d Ê t hU hRU hs0 hhol hcont hfar j hlow hsing g
  have hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t := ⟨hι, hsplit, hU, hRU, hs0, hhol, hcont, hfar⟩
  haveI : CompactSpace (KR n) := kRCpt n
  letI : MeasurableSpace (KR n) := borel _
  haveI : BorelSpace (KR n) := ⟨rfl⟩
  let μ : Measure (KR n) := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  haveI : IsProbabilityMeasure μ := ⟨by simpa [μ] using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (KR n)))⟩

  obtain ⟨Φs, Ω, c, hΩo, hΩG, hcd, hc0, hΦG, -, hΦj, hΦd, hΦrC⟩ := hS m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD g
  set φ : GR n → ℂ := fun y => iteratedDeriv j (Ê · (g * ι y)) s₀ with hφ
  set Ψ : ℕ → M2 n → ℂ := fun r x => iteratedDeriv r (Φs · x) s₀ with hΨ

  have hΨG : ∀ (y : GR n), Ψ j (mR y) = c s₀ * φ y ∧ ∀ i < j, Ψ i (mR y) = 0 := by
    intro y
    have hev : (Φs · (mR y)) =ᶠ[𝓝 s₀] fun z => c z * Ê z (g * ι y) := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hΦG z hz y
    have hlow' : ∀ i < j, iteratedDeriv i (Ê · (g * ι y)) s₀ = 0 := fun i hi => hlow i hi (g * ι y)
    obtain ⟨h1, h2⟩ := iter_mul_low hU hs0 hcd (hhol (g * ι y)) hlow'
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [hΨ]
      rw [iteratedDeriv_eq_of_eventuallyEq hev j, h1]
    · simp only [hΨ]
      rw [iteratedDeriv_eq_of_eventuallyEq hev i, h2 i hi]
  have hΨ0 : ∀ i < j, ∀ x', InG x' → Ψ i x' = 0 := by
    intro i hi x' hx'
    have := (hΨG (toGR x' hx')).2 i hi
    rwa [mR_toGR] at this

  have hιKc : Continuous (ιK n) := by
    unfold ιK
    exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hιKiff : ∀ x, InK x ↔ ∃ k, ιK n k = x := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨toGR x hx.1, hx⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2

  obtain ⟨N₀, ρ₀, ψ₀, a₀, b₀, D₀, M₀, hρ₀, hψ₀, hab₀, hDd₀, -, hMd₀, hid₀⟩ := hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff 0
  obtain ⟨-, hK⟩ := hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ 0 N₀ ρ₀ ψ₀ a₀ b₀ D₀ M₀ hρ₀ hψ₀ hab₀ hDd₀ hMd₀ hid₀
  refine hCR n m e φ (fun x => (c s₀)⁻¹ * Ψ j x) Ω hΩo hΩG (contDiffOn_const.mul (hΦj j)) ?_ ?_ ?_
  · intro y
    simp only [(hΨG y).1]
    field_simp
  · intro y k hk
    have hev : (Ê · (g * ι (y * k))) =ᶠ[𝓝 s₀] fun z => Ê z (g * ι y) * F0 m 0 e k := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hK z hz g y k hk
    simp only [hφ]
    rw [iteratedDeriv_eq_of_eventuallyEq hev j, iteratedDeriv_mul_const_field]
  · intro y Q
    rw [rC_const_mul]
    suffices h : rC (lowQ Q) (Ψ j) (mR y) = 0 by rw [h, mul_zero]
    obtain ⟨N, ρ, ψ, a, b, D, M, hρ, hψ, hab, hDd, hD0, hMd, hid⟩ := hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff Q
    obtain ⟨⟨t', hfarId⟩, -⟩ := hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ Q N ρ ψ a b D M hρ hψ hab hDd hMd hid
    set L : ℂ → ℂ := fun z => rC (lowQ Q) (Φs z) (mR y) with hL
    set T : Fin N → ℂ → ℂ := fun l z => tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (Ê z) g) (mR y) with hTdef
    set R : ℂ → ℂ := fun z => c z * ∑ l, M l (z - s₀) * T l z with hRdef
    have hTH : ∀ l, DifferentiableOn ℂ (T l) U ∧ ∀ r : ℕ, iteratedDeriv r (T l) s₀ =
        tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (fun x => iteratedDeriv r (Ê · x) s₀) g) (mR y) := fun l =>
      hT m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD μ (ρ l) (ψ l) (a l) (b l) (hρ l) (hψ l).1 (hψ l).2.1 (hab l).1 (hab l).2 g y
    have hDs : Differentiable ℂ fun z => D (z - s₀) := hDd.comp (differentiable_id.sub_const s₀)
    have hMs : ∀ l, Differentiable ℂ fun z => M l (z - s₀) := fun l => (hMd l).comp (differentiable_id.sub_const s₀)
    have hLd : DifferentiableOn ℂ L U := (hΦrC Q y).1
    have hsumd : DifferentiableOn ℂ (fun z => ∑ l, M l (z - s₀) * T l z) U :=
      DifferentiableOn.fun_sum fun l _ => (hMs l).differentiableOn.mul (hTH l).1
    have hRd : DifferentiableOn ℂ R U := hcd.mul hsumd

    have hEq : EqOn (fun z => D (z - s₀) * L z) R U := by
      obtain ⟨σ, hσ⟩ := hRU.1
      set z₁ : ℂ := ((max t' σ + 1 : ℝ) : ℂ) with hz₁
      have hz₁U : z₁ ∈ U := hσ (GlobalTheory.Cont.mem_rightOf.2 (by rw [hz₁, Complex.ofReal_re]; linarith [le_max_right t' σ]))
      refine (hDs.differentiableOn.mul hLd).analyticOnNhd hU |>.eqOn_of_preconnected_of_eventuallyEq
        (hRd.analyticOnNhd hU) (rightConn U hU hRU) hz₁U ?_
      have hopen : IsOpen {z : ℂ | max t' σ < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (show max t' σ < z₁.re by rw [hz₁, Complex.ofReal_re]; linarith)] with z hz
      have hzt : t' < z.re := lt_of_le_of_lt (le_max_left _ _) hz
      have hzU : z ∈ U := hσ (GlobalTheory.Cont.mem_rightOf.2 (lt_of_le_of_lt (le_max_right _ _) hz))
      have hcong : L z = rC (lowQ Q) (fun x => c z * resG ι (Ê z) g x) (mR y) := by
        refine hR n (Φs z) _ (lowQ Q) (mR y) y.2 (fun x' hx' => ?_) (fun s => (hE n (mR y) (lowQ Q) s y.2).1)
          (fun s => (hE n (mR y) (lowQ Q) s y.2).2)
        have e1 := hΦG z hzU (toGR x' hx')
        rw [mR_toGR] at e1
        have e2 := lift_mR' (fun y => Ê z (g * ι y)) (toGR x' hx')
        rw [mR_toGR] at e2
        simp only [resG]
        rw [e1, e2]
      show D (z - s₀) * L z = c z * ∑ l, M l (z - s₀) * T l z
      rw [hcong, rC_const_mul, mul_left_comm, hfarId z hzt g y]
    have hev : (fun z => D (z - s₀) * L z) =ᶠ[𝓝 s₀] R := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hEq hz
    have hLlow : ∀ i < j, iteratedDeriv i L s₀ = 0 := by
      intro i hi
      rw [(hΦrC Q y).2 i, hR n _ (fun _ => 0) (lowQ Q) (mR y) y.2 (fun x' hx' => hΨ0 i hi x' hx')
        (fun s => (hE n (mR y) (lowQ Q) s y.2).1) (fun s => (hE n (mR y) (lowQ Q) s y.2).2), rC_zero]
    obtain ⟨hL1, -⟩ := iter_mul_low hU hs0 hDs.differentiableOn hLd hLlow
    have hnb : ∀ t, InG (nU (herm t) : M2 n) := fun t => PositivityTheory.Rg.Sw.LVs.HolB.inG_upper (PositivityTheory.Rg.Sw.AbsSt.LocOpA.herm_isHermitian t).eq
    have hRv : Van j R s₀ := by
      apply van_mul hU hs0 hcd hsumd
      apply van_sum hU hs0 Finset.univ (fun l z => M l (z - s₀) * T l z)
        (fun l => (hMs l).differentiableOn.mul (hTH l).1)
      intro l
      apply van_mul hU hs0 (hMs l).differentiableOn (hTH l).1
      intro k hk
      rw [(hTH l).2 k]
      rcases lt_or_eq_of_le hk with hk' | hkj
      · have hz0 : resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g = fun _ => 0 := by
          funext x
          unfold resG lift
          split_ifs <;> simp [hlow k hk']
        rw [hz0]
        simp [tOp]
      · subst hkj
        have hin : ∀ k' : KR n, (∫ t : Fin n → Fin n → ℝ, resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g
            (mR y * ιK n k' * a l * nU (herm t) * b l) * ψ l t) = 0 := by
          intro k'
          let nb : (Fin n → Fin n → ℝ) → GR n := fun t => toGR (nU (herm t)) (hnb t)
          have key := hsing (ψ l) (hψ l) nb (fun t => rfl) g (y * (k' : GR n) * toGR (a l) (hab l).1)
            (toGR (b l) (hab l).2)
          refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans key
          show resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g
              (mR (y * (k' : GR n) * toGR (a l) (hab l).1 * nb t * toGR (b l) (hab l).2)) * ψ l t = _
          simp only [resG]
          rw [lift_mR']
        unfold tOp
        simp_rw [hin, mul_zero, integral_zero]
    have hRj := hRv j le_rfl
    have h0 : D 0 * iteratedDeriv j L s₀ = 0 := by
      have h1 := iteratedDeriv_eq_of_eventuallyEq hev j
      rw [hL1, hRj, sub_self] at h1
      exact h1
    have hLj : iteratedDeriv j L s₀ = 0 := (mul_eq_zero.1 h0).resolve_left hD0
    rw [(hΦrC Q y).2 j] at hLj
    exact hLj

end PositivityTheory.Rg.Sw.HSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TopHolPf
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lift_mR (φ : GR n → ℂ) (w : GR n) : lift φ (mR w) = φ w := by
  have h : IsUnit (mR w) ∧ InG (mR w) := ⟨⟨w.1, rfl⟩, w.2⟩
  unfold lift
  rw [dite_eq_left h]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp [mR]

theorem ιK_apply (k : KR n) : ιK n k = mR (k : GR n) := rfl

theorem mR_mul' (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem tOp_resG {G : Type} [Group G] (ι : GR n →* G) [MeasurableSpace (KR n)] (μ : Measure (KR n)) (ρ : KR n → ℂ)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b : M2 n} (ha : InG a) (hb : InG b) (F : G → ℂ) (g : G) (y : GR n) :
    tOp μ (ιK n) ρ ψ a b (resG ι F g) (mR y) =
      ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, F ((g * ι y) * ι ((k : GR n) * LocOpA.mkG a ha * LocOpA.nbEl t *
        LocOpA.mkG b hb)) * ψ t) ∂μ := by
  unfold tOp resG
  congr 1
  funext k
  congr 1
  congr 1
  funext t
  congr 1
  have e1 : mR y * ιK n k * a * nU (herm t) * b =
      mR (y * ((k : GR n) * LocOpA.mkG a ha * LocOpA.nbEl t * LocOpA.mkG b hb)) := by
    simp only [mR_mul', ιK_apply, LocOpA.mR_mkG, LocOpA.nbEl, Matrix.mul_assoc]
  rw [e1, lift_mR, map_mul]
  simp only [mul_assoc]

theorem hol_int {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ι : GR n →* G} (hιc : Continuous ι)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n)) [IsFiniteMeasure μ]
    {a b : GR n} {ρ : KR n → ℂ} (hρ : Continuous ρ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) {U : Set ℂ} (hU : IsOpen U) (E : ℂ → G → ℂ)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ)) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (g : G) :
    DifferentiableOn ℂ (fun z => ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ,
      E z (g * ι ((k : GR n) * a * LocOpA.nbEl t * b)) * ψ t) ∂μ) U ∧
    ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ,
      E z (g * ι ((k : GR n) * a * LocOpA.nbEl t * b)) * ψ t) ∂μ) z =
      ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, iteratedDeriv r (fun w => E w (g * ι ((k : GR n) * a * LocOpA.nbEl t * b))) z *
        ψ t) ∂μ := by
  set C := tsupport ψ
  have hC : IsCompact C := hψs
  haveI : IsFiniteMeasure (volume.restrict C) := ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hCc : (volume.restrict C) Cᶜ = 0 := by
    rw [Measure.restrict_apply (isClosed_tsupport ψ).isOpen_compl.measurableSet, Set.compl_inter_self, measure_empty]
  have hnb := LocOpA.continuous_nbEl (n := n)
  have hj : ContinuousOn (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ =>
      E y.2 (g * ι ((y.1.1 : GR n) * a * LocOpA.nbEl y.1.2 * b)) * ψ y.1.2) (univ ×ˢ U) := by
    refine ContinuousOn.mul ?_ (hψc.comp (continuous_snd.comp continuous_fst)).continuousOn
    refine hEc.comp (Continuous.continuousOn (continuous_snd.prodMk ((Vac.continuous_arg hιc hnb g).comp continuous_fst))) ?_
    intro y hy
    exact ⟨hy.2, trivial⟩
  have e1 : ∀ (k : KR n) (h : ℂ → G → ℂ) (z : ℂ), (∫ x in C, h z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) =
      ∫ x, h z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x := fun k h z =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hinner : ∀ k : KR n, ContinuousOn (fun y : (Fin n → Fin n → ℝ) × ℂ =>
      E y.2 (g * ι ((k : GR n) * a * LocOpA.nbEl y.1 * b)) * ψ y.1) (C ×ˢ U) := by
    intro k
    refine hj.comp (Continuous.continuousOn ((Continuous.prodMk_right k).prodMap continuous_id)) ?_
    intro y hy; exact ⟨trivial, hy.2⟩
  have hind : ∀ k : KR n, ∀ x ∈ C, DifferentiableOn ℂ (fun z => E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) U :=
    fun k x _ => (hEh _).mul_const _
  have hin : ∀ k : KR n, DifferentiableOn ℂ (fun z => ∫ x in C, E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) U :=
    fun k => (holParam (Fin n → Fin n → ℝ) (volume.restrict C) C hC hCc U _ hU (hinner k) (hind k)).1
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hcont : Continuous (fun y : KR n × U => ∫ x in C, E (y.2 : ℂ) (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) := by
    refine continuous_parametric_integral_of_continuous
      (f := fun (y : KR n × U) x => E (y.2 : ℂ) (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) ?_ hC
    have : Continuous (fun w : (KR n × U) × (Fin n → Fin n → ℝ) =>
        (((w.1.1, w.2), (w.1.2 : ℂ)) : (KR n × (Fin n → Fin n → ℝ)) × ℂ)) :=
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    exact hj.comp_continuous this fun w => ⟨trivial, w.1.2.2⟩
  have hcon : ContinuousOn (fun y : KR n × ℂ => ρ y.1 *
      ∫ x in C, E y.2 (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) (univ ×ˢ U) := by
    refine (hρ.comp continuous_fst).continuousOn.mul ?_
    rw [continuousOn_iff_continuous_domRestrict]
    have : (univ ×ˢ U).domRestrict (fun y : KR n × ℂ => ∫ x in C, E y.2 (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) =
        (fun y : KR n × U => ∫ x in C, E (y.2 : ℂ) (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) ∘
          (fun w : (univ ×ˢ U : Set (KR n × ℂ)) => ((w.1.1, ⟨w.1.2, w.2.2⟩) : KR n × U)) := by
      funext w; rfl
    rw [this]
    exact hcont.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  have hP := holParam (KR n) μ univ isCompact_univ (by simp) U
    (fun k z => ρ k * ∫ x in C, E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) hU hcon
    (fun k _ => (hin k).const_mul _)
  have e2 : (fun z => ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, E z (g * ι ((k : GR n) * a * LocOpA.nbEl t * b)) * ψ t) ∂μ) =
      fun z => ∫ k, ρ k * (∫ x in C, E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) ∂μ := by
    funext z
    congr 1
    funext k
    rw [e1 k E z]
  rw [e2]
  refine ⟨hP.1, fun z hz r => ?_⟩
  rw [hP.2 z hz r]
  congr 1
  funext k
  rw [iteratedDeriv_const_mul_field]
  congr 1
  rw [(holParam (Fin n → Fin n → ℝ) (volume.restrict C) C hC hCc U _ hU (hinner k) (hind k)).2 z hz r]
  simp_rw [iteratedDeriv_mul_const_field]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem topHol : TopHol := by
  intro m n e _ _ G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD _ _ μ _ _ ρ ψ a b hρ hψc hψs ha hb g y
  haveI : CompactSpace (KR n) := kRCpt n
  have hfun : ∀ F : ℂ → G → ℂ, (fun z => tOp μ (ιK n) ρ ψ a b (resG ι (F z) g) (mR y)) = fun z =>
      ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, F z ((g * ι y) * ι ((k : GR n) * LocOpA.mkG a ha * LocOpA.nbEl t *
        LocOpA.mkG b hb)) * ψ t) ∂μ := fun F => funext fun z => tOp_resG ι μ ρ ψ ha hb (F z) g y
  have H := hol_int hD.ιc μ (a := LocOpA.mkG a ha) (b := LocOpA.mkG b hb) hρ hψc hψs hD.hU Ê hD.cont hD.hol (g * ι y)
  refine ⟨?_, fun r => ?_⟩
  · rw [hfun Ê]
    exact H.1
  · rw [hfun Ê, H.2 s₀ hD.hs r, tOp_resG ι μ ρ ψ ha hb _ g y]

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  unfold JJ
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, zero_add, add_zero, Matrix.mul_neg, Matrix.mul_one]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem JJ_inv : (JJ n)⁻¹ = -JJ n := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_neg, JJ_mul_self, neg_neg]

theorem JJ_conjTranspose : (JJ n)ᴴ = -JJ n := by
  unfold JJ
  rw [fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
  simp

theorem sig_eq (X : M2 n) : sig X = JJ n * Xᴴ * JJ n := by
  unfold sig
  rw [JJ_inv]
  simp [Matrix.neg_mul]

theorem sig_conjTranspose (X : M2 n) : (sig X)ᴴ = JJ n * X * JJ n := by
  rw [sig_eq]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, JJ_conjTranspose, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

theorem lie_half1 (Z : M2 n) (t : ℝ) :
    ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))ᴴ * JJ n + JJ n * ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))) = 0 := by
  have h := JJ_mul_self (n := n)
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, sig_conjTranspose, Complex.star_def,
    Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  rw [sig_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h]
  rw [← Matrix.mul_assoc (JJ n) (JJ n), h]
  simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
  module

theorem lie_half2 (Z : M2 n) (t : ℝ) :
    ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z)))ᴴ * JJ n +
      JJ n * ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))) = 0 := by
  have h := JJ_mul_self (n := n)
  have hI : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I]
    simp [Complex.conj_ofNat]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, sig_conjTranspose, hI, Complex.star_def,
    Complex.conj_ofReal]
  rw [sig_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h]
  rw [← Matrix.mul_assoc (JJ n) (JJ n), h]
  simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
  module

theorem inG_exp_of_lie {X : M2 n} (hX : Xᴴ * JJ n + JJ n * X = 0) : InG (NormedSpace.exp X) := by
  unfold InG
  have hJu : IsUnit (JJ n) := by
    refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
    have := congrArg Matrix.det (JJ_mul_self (n := n))
    rw [Matrix.det_mul, Matrix.det_neg] at this
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at this
    simp at this
  have hXh : Xᴴ = JJ n * (-X) * (JJ n)⁻¹ := by
    have h1 : Xᴴ * JJ n = -(JJ n * X) := eq_neg_of_add_eq_zero_left hX
    calc Xᴴ = Xᴴ * JJ n * (JJ n)⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hJu), Matrix.mul_one]
      _ = JJ n * (-X) * (JJ n)⁻¹ := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  rw [← Matrix.exp_conjTranspose, hXh, Matrix.exp_conj _ _ hJu, Matrix.exp_neg]
  have hE : IsUnit (NormedSpace.exp X) := Matrix.isUnit_exp X
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (JJ n)⁻¹ (JJ n),
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hJu), Matrix.one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hE), Matrix.mul_one]

theorem expLie (x Z : M2 n) (t : ℝ) (hx : InG x) :
    InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) ∧
      InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z)))) := by
  have hmul : ∀ {a b : M2 n}, InG a → InG b → InG (a * b) := fun {a b} ha hb => by
    unfold InG at *
    calc (a * b)ᴴ * JJ n * (a * b) = bᴴ * (aᴴ * JJ n * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [ha, hb]
  exact ⟨hmul hx (inG_exp_of_lie (lie_half1 Z t)), hmul hx (inG_exp_of_lie (lie_half2 Z t))⟩

theorem rcCongr : RcCongr := by
  intro n F F' Z x _ h h1 h2
  unfold rC
  have e1 : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))))) =
      fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) := funext fun t => h _ (h1 t)
  have e2 : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))) =
      fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z)))) := funext fun t => h _ (h2 t)
  rw [e1, e2]

end PositivityTheory.Rg.Sw.HSt
end
end

namespace PositivityTheory.Rg.Sw.HSt

theorem asmH : AsmH :=
  asmH_of farId Conv.smoothX topHol rcCongr (fun _ x Z t hx => expLie x Z t hx)

end PositivityTheory.Rg.Sw.HSt
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SphericalSectionConjugationSwap
noncomputable section

open MeasureTheory Matrix Set
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def epsM (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

theorem epsM_mul_self : epsM n * epsM n = 1 := by
  simp [epsM, fromBlocks_multiply, ← fromBlocks_one]

def epsU (n : ℕ) : GL (Fin n ⊕ Fin n) ℂ := ⟨epsM n, epsM n, epsM_mul_self, epsM_mul_self⟩

theorem eps_conj_blocks (M : M2 n) :
    epsM n * M * epsM n = fromBlocks M.toBlocks₁₁ (-M.toBlocks₁₂) (-M.toBlocks₂₁) M.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [epsM, fromBlocks_multiply]

theorem epsM_conjTranspose : (epsM n)ᴴ = epsM n := by
  simp [epsM, fromBlocks_conjTranspose]

theorem eps_JJ : epsM n * JJ n * epsM n = -JJ n := by
  simp [epsM, JJ, fromBlocks_multiply, fromBlocks_neg]

theorem inG_eps_conj {M : M2 n} (h : InG M) : InG (epsM n * M * epsM n) := by
  unfold InG at h ⊢
  have e4 : ∀ X : M2 n, epsM n * (JJ n * (epsM n * X)) = -(JJ n * X) := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, eps_JJ, Matrix.neg_mul]
  have h' : ∀ X : M2 n, Mᴴ * (JJ n * (M * X)) = JJ n * X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h]
  simp only [conjTranspose_mul, epsM_conjTranspose, Matrix.mul_assoc]
  rw [e4, Matrix.mul_neg, Matrix.mul_neg, h', ← Matrix.mul_assoc, eps_JJ, neg_neg]

def cHom (n : ℕ) : GR n →* GR n where
  toFun y := ⟨epsU n * y.1 * epsU n, by
    show InG ((epsU n * y.1 * epsU n : GL (Fin n ⊕ Fin n) ℂ) : M2 n)
    simpa [epsU] using inG_eps_conj (n := n) y.2⟩
  map_one' := by
    ext : 2
    simp [epsU, epsM_mul_self]
  map_mul' x y := by
    ext : 2
    simp only [Subgroup.coe_mul, Units.val_mul]
    have h := epsM_mul_self (n := n)
    simp only [epsU, Units.val_mk]
    calc epsM n * (x.1.1 * y.1.1) * epsM n = epsM n * x.1.1 * (epsM n * epsM n) * y.1.1 * epsM n := by
          rw [h]; simp [Matrix.mul_assoc]
      _ = epsM n * x.1.1 * epsM n * (epsM n * y.1.1 * epsM n) := by simp [Matrix.mul_assoc]

theorem mR_c (y : GR n) : mR (cHom n y) = epsM n * mR y * epsM n := rfl

theorem cHom_cHom (y : GR n) : cHom n (cHom n y) = y := by
  apply Subtype.ext
  apply Units.ext
  show mR (cHom n (cHom n y)) = mR y
  rw [mR_c, mR_c]
  have h := epsM_mul_self (n := n)
  calc epsM n * (epsM n * mR y * epsM n) * epsM n = (epsM n * epsM n) * mR y * (epsM n * epsM n) := by
        simp only [Matrix.mul_assoc]
    _ = mR y := by rw [h, Matrix.one_mul, Matrix.mul_one]

theorem cHom_cont : Continuous (cHom n) := by
  show Continuous fun y : GR n => (⟨epsU n * y.1 * epsU n, _⟩ : GR n)
  exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

theorem first_cayley_block_of_conjugation (y : GR n) : u1 (mR (cHom n y)) = u2 (mR y) := by
  rw [mR_c, u1, u2, eps_conj_blocks]
  simp

theorem second_cayley_block_of_conjugation (y : GR n) : u2 (mR (cHom n y)) = u1 (mR y) := by
  rw [mR_c, eps_conj_blocks]
  simp [u1, u2]

theorem det_c (y : GR n) : (mR (cHom n y)).det = (mR y).det := by
  have h := congrArg Matrix.det (epsM_mul_self (n := n))
  rw [det_mul, det_one] at h
  rw [mR_c, det_mul, det_mul]
  calc (epsM n).det * (mR y).det * (epsM n).det = (mR y).det * ((epsM n).det * (epsM n).det) := by ring
    _ = (mR y).det := by rw [h, mul_one]

theorem spherical_section_conjugation_swap (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e (cHom n y) = F0 q p e y := by
  simp only [F0, f0, det_c, first_cayley_block_of_conjugation, second_cayley_block_of_conjugation]
  ring

theorem norm_sq_det_cayley_blocks_eq (M : M2 n) (h : InG M) : ‖(u1 M).det‖ ^ 2 = ‖(u2 M).det‖ ^ 2 := by
  have hJ2 : JJ n * JJ n = -1 := by
    simp only [JJ, fromBlocks_multiply]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  unfold InG at h
  have hL : (-(JJ n * Mᴴ * JJ n)) * M = 1 := by
    calc -(JJ n * Mᴴ * JJ n) * M = -(JJ n * (Mᴴ * JJ n * M)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h, hJ2, neg_neg]
  have hR : M * (-(JJ n * Mᴴ * JJ n)) = 1 := mul_eq_one_comm.1 hL
  have hMJ : M * JJ n * Mᴴ = JJ n := by
    calc M * JJ n * Mᴴ = M * (-(JJ n * Mᴴ * JJ n)) * JJ n := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ2, Matrix.mul_one, neg_neg]
      _ = JJ n := by rw [hR, Matrix.one_mul]
  have hM : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
    (fromBlocks_toBlocks M).symm
  rw [hM] at hMJ
  have hb := congrArg toBlocks₂₂ hMJ
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at hb
  have key : M.toBlocks₂₁ * (M.toBlocks₂₂)ᴴ = M.toBlocks₂₂ * (M.toBlocks₂₁)ᴴ := by
    rw [← sub_eq_zero, ← hb]
    abel
  have e1 : u1 M * (u1 M)ᴴ = u2 M * (u2 M)ᴴ := by
    simp [u1, u2, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, key]
    abel
  have hn : ∀ u : Matrix (Fin n) (Fin n) ℂ, ((‖u.det‖ ^ 2 : ℝ) : ℂ) = (u * uᴴ).det := by
    intro u
    simp [det_mul, det_conjTranspose, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  rw [hn, hn, e1]

theorem hLoc_c (y : GR n) : hLoc (cHom n y) = hLoc y := by
  simp only [hLoc, first_cayley_block_of_conjugation]
  rw [norm_sq_det_cayley_blocks_eq (mR y) y.2]

theorem zkey (a b c d : Matrix (Fin n) (Fin n) ℂ) (E1 : aᴴ * c - cᴴ * a = 0) (E2 : aᴴ * d - cᴴ * b = 1)
    (E3 : bᴴ * d - dᴴ * b = 0) :
    (Complex.I • c + d)ᴴ * (Complex.I • a - b) = -((Complex.I • a + b)ᴴ * (-(Complex.I • c) + d)) := by
  rw [eq_neg_iff_add_eq_zero]
  have E2' : dᴴ * a - bᴴ * c = 1 := by
    have := congrArg conjTranspose E2
    simpa [conjTranspose_sub, conjTranspose_mul] using this
  have h1 : aᴴ * c = cᴴ * a := sub_eq_zero.1 E1
  have h3 : bᴴ * d = dᴴ * b := sub_eq_zero.1 E3
  have h2 : aᴴ * d = 1 + cᴴ * b := by
    rw [← E2]
    abel
  have h4 : dᴴ * a = 1 + bᴴ * c := by
    rw [← E2']
    abel
  simp [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rw [h1, h3, h2, h4]
  simp only [smul_add]
  abel

private theorem eq_zero_of_star_dotProduct_self_eq_zero (v : Fin n → ℂ) (h : star v ⬝ᵥ v = 0) : v = 0 := by
  have e : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simp [dotProduct, Complex.conj_mul']
  rw [e] at h
  have h' : ∑ i, ‖v i‖ ^ 2 = 0 := by exact_mod_cast h
  have h'' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).1 h'
  funext i
  simpa using h'' i (Finset.mem_univ i)

private theorem card_fromBlocks_cayley_eq_mul (M : M2 n) (h : InG M) :
    -((M.toBlocks₂₁)ᴴ * M.toBlocks₁₁) + (M.toBlocks₁₁)ᴴ * M.toBlocks₂₁ = 0 ∧
    -((M.toBlocks₂₁)ᴴ * M.toBlocks₁₂) + (M.toBlocks₁₁)ᴴ * M.toBlocks₂₂ = 1 ∧
    -((M.toBlocks₂₂)ᴴ * M.toBlocks₁₂) + (M.toBlocks₁₂)ᴴ * M.toBlocks₂₂ = 0 := by
  have hM := (fromBlocks_toBlocks M).symm
  unfold InG at h
  rw [hM] at h
  have h11 := congrArg toBlocks₁₁ h
  have h12 := congrArg toBlocks₁₂ h
  have h22 := congrArg toBlocks₂₂ h
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at h11 h12 h22
  exact ⟨h11, h12, h22⟩

private theorem conjTranspose_I_smul_add_sub_eq_two_I (a b c d : Matrix (Fin n) (Fin n) ℂ) (E1 : -(cᴴ * a) + aᴴ * c = 0)
    (E2 : -(cᴴ * b) + aᴴ * d = 1) (E3 : -(dᴴ * b) + bᴴ * d = 0) :
    (Complex.I • c + d)ᴴ * (Complex.I • a + b) - (Complex.I • a + b)ᴴ * (Complex.I • c + d) =
      (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have E2' : dᴴ * a - bᴴ * c = 1 := by
    have := congrArg conjTranspose E2
    simp [conjTranspose_add, conjTranspose_neg, conjTranspose_mul] at this
    rw [sub_eq_neg_add]
    exact this
  have h1 : aᴴ * c = cᴴ * a := by
    rw [← sub_eq_zero, sub_eq_neg_add]
    exact E1
  have h3 : bᴴ * d = dᴴ * b := by
    rw [← sub_eq_zero, sub_eq_neg_add]
    exact E3
  have h2 : aᴴ * d = 1 + cᴴ * b := by
    rw [← E2]
    abel
  have h4 : dᴴ * a = 1 + bᴴ * c := by
    rw [← E2']
    abel
  simp [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h1, h3, h2, h4]
  simp only [smul_add]
  module

private theorem det_u1_ne_zero_of_inG (M : M2 n) (h : InG M) : (u1 M).det ≠ 0 := by
  obtain ⟨h11, h12, h22⟩ := card_fromBlocks_cayley_eq_mul M h
  intro hdet
  obtain ⟨v, hv, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have W := conjTranspose_I_smul_add_sub_eq_two_I _ _ _ _ h11 h12 h22
  have hu' : (Complex.I • M.toBlocks₂₁ + M.toBlocks₂₂) *ᵥ v = 0 := hu
  have hz : star v ⬝ᵥ (((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) = 0 := by
    rw [← W, Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu',
      Matrix.mulVec_zero, dotProduct_zero, sub_zero, dotProduct_mulVec, ← star_mulVec, hu', star_zero,
      zero_dotProduct]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at hz
  rcases hz with h0 | h0
  · simp [Complex.I_ne_zero] at h0
  · exact hv (eq_zero_of_star_dotProduct_self_eq_zero v h0)

private theorem det_u2_ne_zero_of_inG (M : M2 n) (h : InG M) : (u2 M).det ≠ 0 := by
  have e : u2 M = u1 (epsM n * M * epsM n) := by
    rw [u1, u2, eps_conj_blocks]
    simp
  rw [e]
  exact det_u1_ne_zero_of_inG _ (inG_eps_conj h)

theorem zOf_c (y : GR n) : zOf (cHom n y) = -(zOf y)ᴴ := by
  have hy : InG (mR y) := y.2
  obtain ⟨h11, h12, h22⟩ := card_fromBlocks_cayley_eq_mul (mR y) hy
  have hU1 := det_u1_ne_zero_of_inG (mR y) hy
  have hU2 := det_u2_ne_zero_of_inG (mR y) hy
  have zk := zkey (mR y).toBlocks₁₁ (mR y).toBlocks₁₂ (mR y).toBlocks₂₁ (mR y).toBlocks₂₂
    (by rw [sub_eq_neg_add]; exact h11) (by rw [sub_eq_neg_add]; exact h12)
    (by rw [sub_eq_neg_add]; exact h22)
  simp only [zOf, first_cayley_block_of_conjugation]
  rw [mR_c, eps_conj_blocks]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂]
  rw [conjTranspose_mul, conjTranspose_nonsing_inv]
  have hU1h : IsUnit ((u1 (mR y))ᴴ).det := by
    rw [det_conjTranspose]
    exact (isUnit_iff_ne_zero.2 hU1).star
  have hU2' : IsUnit (u2 (mR y)).det := isUnit_iff_ne_zero.2 hU2
  have zk' : (u1 (mR y))ᴴ * (Complex.I • (mR y).toBlocks₁₁ + -(mR y).toBlocks₁₂) =
      -((Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂)ᴴ * u2 (mR y)) := by
    rw [← sub_eq_add_neg]
    exact zk
  calc (Complex.I • (mR y).toBlocks₁₁ + -(mR y).toBlocks₁₂) * (u2 (mR y))⁻¹
      = ((u1 (mR y))ᴴ)⁻¹ * ((u1 (mR y))ᴴ * (Complex.I • (mR y).toBlocks₁₁ + -(mR y).toBlocks₁₂)) *
          (u2 (mR y))⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU1h, Matrix.one_mul]
    _ = ((u1 (mR y))ᴴ)⁻¹ * (-((Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂)ᴴ * u2 (mR y))) *
          (u2 (mR y))⁻¹ := by rw [zk']
    _ = -(((u1 (mR y))ᴴ)⁻¹ * (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂)ᴴ) := by
        rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ hU2', Matrix.mul_one]

theorem herm_neg (x : Fin n → Fin n → ℝ) : herm (-x) = -herm x := by
  ext i j
  simp [herm]
  ring

theorem eps_nU (B : Matrix (Fin n) (Fin n) ℂ) : epsM n * nU B * epsM n = nU (-B) := by
  rw [eps_conj_blocks]
  simp [nU]

theorem singTest_neg {ψ : (Fin n → Fin n → ℝ) → ℂ} (h : IsSingTest ψ) : IsSingTest (fun x => ψ (-x)) := by
  refine ⟨h.1.comp continuous_neg, h.2.1.comp_homeomorph (Homeomorph.neg _), fun β hβ hdet => ?_⟩
  have e : ∀ x, eTr β x = eTr (-β) (-x) := by
    intro x
    simp [eTr, herm_neg]
  simp_rw [e]
  rw [integral_neg_eq_self (fun x => ψ x * eTr (-β) x) volume]
  exact h.2.2 (-β) hβ.neg (by rw [det_neg, hdet, mul_zero])

theorem conj : Conj := by
  intro hh m n p q e hm hmn hpq G _ _ _ _ _ _ Pp Γ ι s₀ Ht f hι hf U d Ê t hU hR hs hD hC hE j hj hsing g
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq] at hf
    rw [hp, hq]
    exact hh m n e hm hmn G Pp Γ ι s₀ Ht f hι hf U d Ê t hU hR hs hD hC hE j hj hsing g
  · rw [hp, hq] at hf
    rw [hp, hq]
    have hm0 : m ≠ 0 := by omega
    have hf' : ∀ g' : G, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g' = x * (ι.comp (cHom n)) y ∧
        ∀ y' : GR n, ((Ht (x * (ι.comp (cHom n)) y') : ℝ) = r * hLoc y' ∧
          f (x * (ι.comp (cHom n)) y') = S * F0 m 0 e y') := by
      intro g'
      obtain ⟨x, y, S, r, hr, hg, hy⟩ := hf g'
      refine ⟨x, cHom n y, S, r, hr, ?_, fun y' => ?_⟩
      · simp [hg, cHom_cHom]
      · obtain ⟨h1, h2⟩ := hy (cHom n y')
        refine ⟨?_, ?_⟩
        · simpa [hLoc_c] using h1
        · simpa [spherical_section_conjugation_swap] using h2
    have hs' : ∀ ψ : (Fin n → Fin n → ℝ) → ℂ, IsSingTest ψ → ∀ nb : (Fin n → Fin n → ℝ) → GR n,
        (∀ x, mR (nb x) = nU (herm x)) → ∀ (g' : G) (a b : GR n),
          ∫ x, iteratedDeriv j (fun s => Ê s (g' * (ι.comp (cHom n)) (a * nb x * b))) s₀ * ψ x = 0 := by
      intro ψ hψ nb hnb g' a b
      have hnb' : ∀ x, mR (cHom n (nb (-x))) = nU (herm x) := by
        intro x
        rw [mR_c, hnb, herm_neg, eps_nU, neg_neg]
      have h0 := hsing (fun x => ψ (-x)) (singTest_neg hψ) (fun x => cHom n (nb (-x))) hnb' g'
        (cHom n a) (cHom n b)
      rw [← integral_neg_eq_self]
      simpa [map_mul] using h0
    obtain ⟨H, hH, hrep⟩ := hh m n e hm hmn G Pp Γ (ι.comp (cHom n)) s₀ Ht f (hι.comp cHom_cont) hf' U d Ê t
      hU hR hs hD hC hE j hj hs' g
    refine ⟨H, hH, fun y => ?_⟩
    have h1 := hrep (cHom n y)
    simp only [MonoidHom.comp_apply, cHom_cHom, spherical_section_conjugation_swap, zOf_c] at h1
    show iteratedDeriv j (fun x => Ê x (g * ι y)) s₀ = _
    rw [h1]
    simp [hm0]

end PositivityTheory.Rg.Sw.HSt
end
end

namespace PositivityTheory.Rg.Sw.HSt

theorem holLeadB : PositivityTheory.SiegelWeilFormula.HolLead := conj (asmH locTau secFz crLem)

end PositivityTheory.Rg.Sw.HSt
end

noncomputable section

open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Fin

theorem locInst_of (hT : TAll) : LocInst := KLI.locInst_of hT kfour.auxEx KFock.fockMem (KFock.liftEx hT.1)

theorem siegelWeilStd_mid (hW : TWeyl) (hKP : KFinPoly) (hLD : LDEx) (hCT : CTSplit) : SiegelWeilStd :=
  have hT := tAll_of hW
  siegelWeilStd_of hT (locInst_of hT)
    (Kdil.gIdil_full hT kfour.auxEx (locOpEx_of_tAll hT) (KAway.awayAct_of_tAll hT) (locInst_of hT)) hKP
    (KK.polyKFin_of hT KFock.fockMem) hLD hCT HSt.holLeadB

end PositivityTheory.SiegelWeilFormula.Fin

end
