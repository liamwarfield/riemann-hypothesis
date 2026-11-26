module

public import Formalism.LocalToGlobal.InertKernelTheory.KerTransAll
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.KappaSelfDualFourthPowerLattice
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
public import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
public import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
public import Formalism.LocalToGlobal.GlobalTheory.GL3.ProvisionExtensionLink
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.KerTh
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.CurveIdealPrimeReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseThetaTensorPowerTranslatesIntegral

@[expose] public section

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ReBase
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4 stdChar)
open Formalism.L2.Th1.Top (IsLTNorm)

namespace ReBase

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} (hcc : TaylorLogMetric.IsCurveIdeal D cc) : Odd (Ideal.absNorm cc) := by
  have hc2 : Nat.Coprime (Ideal.absNorm cc) 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 _) hcc.2
  rcases Nat.even_or_odd (Ideal.absNorm cc) with he | ho
  · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 he) hc2) (by decide)
  · exact ho

theorem cm_change_of_base : CmReBase := by
  intro D cc δ B hcc hδ
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, -, hlat⟩ := curve_lattice_compatible D cc δ hcc.1 (odd_norm hcc) hδ
  have hlat' : (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := hlat.symm
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat', KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat', ?_⟩
  have e : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
    rw [KS.theta_val']; ring
  have h := KS.half_period_unique_CM a₀ b₀ c₀ D.host.d ha hd _ hl hcm (B.ω₀ / 2)
    ((KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat' _).1 B.t0.1)
    (by rw [← KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat', KS.theta_val']; exact B.t0.2.1)
    (by rw [← KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat', ← e]; exact B.t0.2.2)
  rw [KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat',
    show (B.ω₀ - (g : ℂ) * δ * a₀) / 2 = B.ω₀ / 2 - (g : ℂ) * δ * a₀ / 2 by ring]
  exact h

theorem isThMM_eq {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B B' : Base D cc δ) (hγ : B'.gC = B.gC)
    (hκ : B'.kappa = B.kappa) (hω : (B.ω₀ - B'.ω₀) / 2 ∈ B'.L.lattice) : B'.IsThMM = B.IsThMM := by
  have h := KS.lattice_eq B B'
  have e : IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa = IsThM B'.L B'.ω₀ B.cq B.lamM B.gC B.kappa := by
    funext θ
    unfold IsThM kernel4 Formalism.L2.Th1.H.F0 Formalism.L2.Th1.H.stdLat
    rw [KS.hOne_congr h, KS.stdH_congr h, KS.thetaNull_congr_lattice h hω (Base.half_not_mem B'), h]
  show IsThM B'.L B'.ω₀ B.cq B.lamM B'.gC B'.kappa = IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa
  rw [hγ, hκ, e]

theorem theta_change_of_base : ThMMReBase := by
  intro D cc δ B hcc
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat, ht, hω⟩ := cm_change_of_base D cc δ B hcc (delta_ne_of_base B)
  have hω' : (B.ω₀ - (g : ℂ) * δ * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice :=
    (KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat _).1 hω
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat, hcm, hN,
    KS.cmBase_isCm B a₀ b₀ c₀ ha hd _ hl hcm hlat, KS.lattice_eq _ B, rfl, rfl, rfl,
    (KS.lattice_eq B (KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat)) ▸ hω',
    isThMM_eq B _ rfl rfl hω', (KS.thMM_reBase B _ hlat _ (KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat) hω').symm⟩

theorem stdLat_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : Type) : stdLat L n = stdLat L' n := by
  unfold Formalism.L2.Th1.H.stdLat; rw [h]

theorem isLTNorm_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 s2 ε : MaximalUnramifiedExtension l) : IsLTNorm l L ι g2 g3 s2 ε ↔ IsLTNorm l L' ι g2 g3 s2 ε := by
  obtain ⟨-, -, -, -, hs, -, -, h2, h3⟩ := Formalism.L2.Th1.F.latticeOnly L L' h
  unfold IsLTNorm
  rw [h2, h3, hs]

theorem th0Char_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    {x : ℂ} (hx : x ∈ L'.lattice) : Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ x = Formalism.L2.Th1.F.thetaZeroCharacter L' ω₀' x := _root_.GlobalTheory.CmThetaMoment.th0Char_congr (L := L) (L' := L') (ω₀ := ω₀) (ω₀' := ω₀') (x := x) h hω hx

theorem stdData_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    (hn : ω₀ / 2 ∉ L.lattice) {n : Type} [Fintype n] [DecidableEq n] {hh : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)}
    {α : (n → ℂ) → ℂ} {β : (Fin 4 × n → ℂ) → ℂ} {g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)}
    (S : StdData L' ω₀' hh Λ α β g) : StdData L ω₀ hh Λ α β g := _root_.GlobalTheory.CmThetaMoment.stdData_congr (L := L) (L' := L') (ω₀ := ω₀) (ω₀' := ω₀') (n := n) (hh := hh) (Λ := Λ) (α := α) (β := β) (g := g) h hω hn S

end ReBase

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.TestVectorMemSchwartzBruhat
noncomputable section

namespace Formalism.L2.KerInert

namespace JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Good

variable {p : ℕ} [Fact p.Prime] {σ ι : Type*}

variable (δ : ι → MvPowerSeries σ ℂ_[p] →+ MvPowerSeries σ ℂ_[p])

def Wd (l : List ι) (G : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  l.foldr (fun j H => δ j H) G

def Good (G : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ l : List ι, IsIntP (MvPowerSeries.constantCoeff (Wd δ l G))

variable {δ}

end Good

section Ring

variable {p : ℕ} [Fact p.Prime]

end Ring

section Deriv

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

end Deriv

section Chain

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Chain

section Lin

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem test_vector_mem_schwartz_bruhat (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map D.host.φ₀.toRatAlgHom

theorem isPadicIntegral_lamC_K (c : 𝓞 D.host.K) : IsIntP (lamC lam (D.host.φ₀ ((c : D.host.K) : D.host.E))) := by
  have hI : IsIntegral ℤ ((c : D.host.K) : D.host.E) :=
    map_isIntegral_int (algebraMap D.host.K D.host.E) (NumberField.RingOfIntegers.isIntegral_coe c)
  unfold lamC
  rw [dite_eq_left (test_vector_mem_schwartz_bruhat _)]
  exact RestC.norm_le_one_of_int (map_isIntegral_int (lam.comp (D.host.φ₀.codRestrict Qbar test_vector_mem_schwartz_bruhat)) hI)

variable (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Lin

section Core

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end Core

section Log

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {p : ℕ} [Fact p.Prime]

end Log

end JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepScal
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.IteratedFDerivConstSmul
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

theorem iteratedFDeriv_const_smul' {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (c : ℂ) (hc : c ≠ 0) (f : E → F) (n : ℕ) :
    iteratedFDeriv ℂ n (fun y => c • f y) = c • iteratedFDeriv ℂ n f := by
  let _ : Invertible c := invertibleOfNonzero hc
  induction n with
  | zero =>
    ext x m
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    simp only [Function.comp_apply]
    rw [fderiv_const_smul_of_invertible c, map_smul]
    rfl

theorem taylor_const_mul (D : D7) {N N' : ℕ} (s : ℂ) (hs : s ≠ 0) (G : TaylorLogMetric.VC D N N' → ℂ) (α : TaylorLogMetric.Mono D N N') :
    TaylorLogMetric.taylor D (fun z => s * G z) α = s * TaylorLogMetric.taylor D G α := by
  unfold TaylorLogMetric.taylor
  have h := iteratedFDeriv_const_smul' s hs G (Multiset.card α.toMultiset)
  simp only [smul_eq_mul] at h
  rw [h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

theorem lamC_mul {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (hs0 : s ≠ 0) (t : ℂ) :
    TaylorLogMetric.lamC lam (s * t) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam t := by
  unfold TaylorLogMetric.lamC
  by_cases ht : t ∈ TaylorLogMetric.Qbar
  · have hst : s * t ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem hs ht
    rw [dite_eq_left hst, dite_eq_left hs, dite_eq_left ht, ← map_mul]
    rfl
  · have hst : s * t ∉ TaylorLogMetric.Qbar := by
      intro h
      apply ht
      have : s⁻¹ * (s * t) ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.inv_mem hs) h
      rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at this
    rw [dite_eq_right hst, dite_eq_right ht, mul_zero]

theorem pSer_const_mul (D : D7) {N N' p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar)
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pSer D lam (fun z => s * G z) = MvPowerSeries.C (TaylorLogMetric.lamC lam s) * TaylorLogMetric.pSer D lam G := by
  by_cases hs0 : s = 0
  · subst hs0
    ext α
    rw [MvPowerSeries.coeff_C_mul]
    have h0 : TaylorLogMetric.lamC lam 0 = 0 := by
      unfold TaylorLogMetric.lamC
      rw [dite_eq_left (TaylorLogMetric.Qbar.zero_mem)]
      exact map_zero lam
    show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => 0 * G z) α) = _
    simp only [zero_mul]
    rw [h0, zero_mul]
    have : TaylorLogMetric.taylor D (fun _ : TaylorLogMetric.VC D N N' => (0 : ℂ)) α = 0 := by
      unfold TaylorLogMetric.taylor
      simp
    rw [this, h0]
  · ext α
    rw [MvPowerSeries.coeff_C_mul]
    show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * G z) α) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D G α)
    rw [taylor_const_mul D s hs0 G α, lamC_mul lam hs hs0]

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

noncomputable section

namespace Formalism.L2.KerInert.Rep

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.MainNotions.FormalGroupSystem (Sys)

theorem isComb_smul (D : D7) (T : Tor D) (e : FamE D) {N N' p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]} (h : IsComb D T e lam L L' F) {c : ℂ_[p]}
    (hc : ‖c‖ ≤ 1) : IsComb D T e lam L L' (c • F) := by
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hL, rfl⟩ := h
  refine ⟨m, fun k => c * r k, t, L₁, L₁', fun k => ?_, ht, hL, ?_⟩
  · have := hr k
    simp only [IsIntP] at this ⊢
    rw [norm_mul]
    exact mul_le_one₀ hc (norm_nonneg _) this
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, mul_assoc]

theorem isComb_scalar (D : D7) (T : Tor D) (e : FamE D) {N N' p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (G : VC D N N' → ℂ) (h : IsComb D T e lam L L' (pSer D lam G)) {s : ℂ} (hs : s ∈ Qbar) (k : ℤ)
    (hk : ‖(p : ℂ_[p]) ^ k * lamC lam s‖ ≤ 1) :
    IsComb D T e lam L L' (((p : ℂ_[p]) ^ k) • pSer D lam (fun z => s * G z)) := by
  have e1 : ((p : ℂ_[p]) ^ k) • pSer D lam (fun z => s * G z) = ((p : ℂ_[p]) ^ k * lamC lam s) • pSer D lam G := by
    rw [Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.pSer_const_mul D lam hs, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
    rfl
  rw [e1]
  exact isComb_smul D T e lam h hk

end Formalism.L2.KerInert.Rep
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneDatumExistence
noncomputable section

namespace Formalism.L2.KerInert.GenusOneDatumExistence

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend PowerSeries

section Gen

variable {p : ℕ} [Fact p.Prime]

theorem mem_Wp_of_kur {x : ℂ_[p]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h1 : ‖x‖ ≤ 1) : x ∈ Wp p := by
  have hp : p.Prime := Fact.out
  have hB := ((Formalism.L2.Th1.D.kurIntegers p).1 x).2 ⟨hx, h1⟩
  have hS : Formalism.L2.Th1.D.muPrime p = {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} := by
    ext ζ
    simp only [Formalism.L2.Th1.D.muPrime, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn), h⟩
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hn), h⟩
  unfold Formalism.L2.Th1.D.ringB Formalism.L2.Th1.D.ringA at hB
  rw [hS] at hB
  exact hB

theorem logF_eq : logF p = Formalism.L2.Th1.CM.ltLog ℂ_[p] p := _root_.GlobalTheory.InertGenusOne.logF_eq

theorem isWq_wU (W : WeierstrassCurve ℂ_[p]) : Formalism.MainNotions.TaylorLogMetric.IsWq W (Formalism.L2.Th1.A.wU W) := by
  have hF := (Formalism.L2.Th1.A.CurveSer.wSer_fixed W).2
  rw [Formalism.L2.Th1.A.CurveSer.wSer_eq] at hF
  unfold Formalism.MainNotions.TaylorLogMetric.IsWq
  simp only [PowerSeries.algebraMap_eq]
  apply mul_left_cancel₀ (pow_ne_zero 3 (X_ne_zero (R := ℂ_[p])))
  linear_combination hF

theorem norm_four (h5 : 5 ≤ p) : ‖(4 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have h := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) (m := 4) hp
    (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p) (by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega)
  exact_mod_cast h

theorem datum_of_short (h5 : 5 ≤ p) (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (g2 g3 : ℂ_[p])
    (hW : C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ = Formalism.L2.Th1.A.shortW g2 g3)
    (k2 : g2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (k3 : g3 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (n2 : ‖g2‖ ≤ 1) (n3 : ‖g3‖ ≤ 1)
    (nd : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (ε : ℂ_[p]) (hε1 : ‖ε‖ = 1)
    (hint : ∀ n : ℕ,
      PowerSeries.coeff n ((Formalism.L2.Th1.CM.uSer g2 g3).subst (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p)) ∈
          Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧
        ‖PowerSeries.coeff n ((Formalism.L2.Th1.CM.uSer g2 g3).subst
          (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p))‖ ≤ 1) :
    ∃ g : G1 p, g.lam = lam ∧ g.abelian₂ = Λ ∧ g.C = C ∧ g.Ok ∧ ModelOverW g.lam g.abelian₂ g.C ∧ LTIso g := _root_.GlobalTheory.InertGenusOne.datum_of_short h5 lam Λ C g2 g3 hW k2 k3 n2 n3 nd ε hε1 hint

end Gen

open NumberField Formalism.BasicNotions


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem genus_one_datum_exists (hInv : Formalism.L2.KerInert.Sigma.InvAlg) : Formalism.L2.KerInert.GenusOneModelExists := by
  intro D cc δ hcurve hδ12 p _ hcop h5 hIn lam
  have hp : p.Prime := Fact.out
  have hcc : cc ≠ ⊥ := hcurve.1

  have hδ : δ ≠ 0 := by
    intro h0
    obtain ⟨⟨L1, hL1⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc 1 hcc one_ne_zero
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L1 (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL1)
    have hd := Formalism.L2.Th1.F.discNeZero L1
    apply hd
    have h12 := hδ12
    unfold Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice Formalism.MainNotions.TaylorLogMetric.discr at h12
    rw [h0, e2, e3] at h12
    rw [← h12]; norm_num

  obtain ⟨⟨L, hL⟩, hCM⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcurve hδ12 L hL
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL)
  set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3
  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p lam

  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod p) := ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn
  have hsq' : ¬ ∃ a : ZMod p, a ^ 2 = -(D.host.d : ZMod p) := by
    rintro ⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩
  have hpd : ¬ p ∣ D.host.d := by
    intro h; apply hsq'; refine ⟨0, ?_⟩
    rw [(ZMod.natCast_eq_zero_iff _ _).2 h]; ring
  have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
    intro ω hω
    have h1 := hCM ω (by rw [← hL]; exact hω)
    rw [← hL] at h1
    have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
      unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
    rw [e]; exact h1

  obtain ⟨g2', g3', hGood⟩ := Formalism.L2.Th1.CM.cm2 D.host.d L hdp.squarefree hd4 hcmby p h5 hpd ι
  obtain ⟨ε, -, hε1, hεint⟩ :=
    Formalism.L2.Th1.CM.cm3 D.host.d L hdp.squarefree hd4 hcmby p h5 hpd hsq' ι g2' g3' hGood
  obtain ⟨k2, k3, n2, n3, nd, μ, hμ, hg2', hg3'⟩ := hGood

  let C : WeierstrassCurve.VariableChange ℂ_[p] := ⟨(Units.mk0 μ hμ)⁻¹, 0, 0, 0⟩
  have ea4 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4) = -(ι L.g₂) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g2 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4 = ((-a2 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by
      rw [e2]; push_cast; rfl
    rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat, ← hι a2]
  have ea6 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4) = -(ι L.g₃) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g3 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4 = ((-a3 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by
      rw [e3]; push_cast; rfl
    rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat, ← hι a3]
  have hW : C • Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.A.shortW g2' g3' := by
    have hw : Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = ⟨0, 0, 0, -(ι L.g₂) / 4, -(ι L.g₃) / 4⟩ := by
      simp only [Formalism.MainNotions.TaylorLogMetric.wModel, ea4, ea6]
    rw [hw]
    ext <;> simp [C, Formalism.L2.Th1.A.shortW, hg2', hg3', WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆] <;> ring
  obtain ⟨g, hgl, hgL, -, hOk, hM, hLT⟩ :=
    datum_of_short h5 lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) C g2' g3' hW k2 k3 n2 n3 nd ε hε1 hεint
  exact ⟨g, hgl, ⟨hcurve, hcop, hδ12, hgL, hOk⟩, hM, hLT⟩


end Formalism.L2.KerInert.GenusOneDatumExistence
end
end
