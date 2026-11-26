module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HalfTorsionNotMemCmLattice
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetSplitPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaTranslatesPrimeToQIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaBaseVectorTranslatesIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStandardIsometryFourthPowerSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStandardIsometryFourthPowerSplitPrime
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN Formalism.L2.KerInert
open Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
open Formalism.L2.Th1.F (cmTheta)

namespace GlobalTheory.CmThetaMoment

theorem cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

theorem stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

theorem odd_of_cmOK {a : ℕ} {b c : ℤ} {d : ℕ} (h : CmOK a b c d) : Odd b := by
  by_contra hb
  obtain ⟨k, rfl⟩ := Int.not_odd_iff_even.1 hb
  have h1 := h.1
  have h8 := h.2.2.1
  have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
    have : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [this] at h1
    linarith
  generalize (a : ℤ) * c - k * k = t at h2
  omega

theorem hermitianSelfDual_of_fourfoldBlock {n : Type} [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH (blk4 h)) (pow4 Λ)) : IsSelfDual (matH h) Λ := by
  have key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ), altE (matH (blk4 h)) (CmData.embA 0 x) y = altE (matH h) x (slice 0 y) := by
    intro x y
    simp only [altE, matrixForm_fourfoldBlock, CmData.slice_embA]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  ext x
  constructor
  · intro hx
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (slice 0 y) (hy 0)
      exact ⟨m, by rw [key, hm]⟩
    rw [hsd] at h1
    have h2 := h1 0
    rwa [CmData.slice_embA, if_pos rfl] at h2
  · intro hx y hy
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      rw [hsd]
      exact CmData.embA_mem Λ 0 hx
    obtain ⟨m, hm⟩ := h1 _ (CmData.embA_mem Λ 0 hy)
    refine ⟨m, ?_⟩
    rw [key, CmData.slice_embA, if_pos rfl] at hm
    exact hm

section Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem selfDual_fourfold_curveIdeal_lattice (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (blk4 (hOne B.L D.what₂.Tau))) (pow4 B.lamM) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h
  rw [SO.reix_pow] at h2
  exact h2

theorem selfDual_lamM (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L D.what₂.Tau)) B.lamM :=
  hermitianSelfDual_of_fourfoldBlock _ _ (selfDual_fourfold_curveIdeal_lattice B hcc hδ)

theorem stable_lamM (b : ℤ) (hb : Odd b) : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
  refine stable_of_one _ _ (fun x hx => ?_) b hb
  have := SO.lamMM_smul (AR.om D) hx
  rw [← SO.theta_eq] at this
  exact this

end Base

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} (hcc : TaylorLogMetric.IsCurveIdeal D cc) : Odd (Ideal.absNorm cc) := by
  have hc2 : Nat.Coprime (Ideal.absNorm cc) 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 _) hcc.2
  rcases Nat.even_or_odd (Ideal.absNorm cc) with he | ho
  · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 he) hc2) (by decide)
  · exact ho

theorem cmReBase' : CmReBase := by
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

theorem thMMReBase' : ThMMReBase := by
  intro D cc δ B hcc
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat, ht, hω⟩ := cmReBase' D cc δ B hcc (delta_ne_of_base B)
  have hω' : (B.ω₀ - (g : ℂ) * δ * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice :=
    (KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat _).1 hω
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat, hcm, hN,
    KS.cmBase_isCm B a₀ b₀ c₀ ha hd _ hl hcm hlat, KS.lattice_eq _ B, rfl, rfl, rfl,
    (KS.lattice_eq B (KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat)) ▸ hω',
    isThMM_eq B _ rfl rfl hω', (KS.thMM_reBase B _ hlat _ (KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat) hω').symm⟩

theorem stdLat_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : Type) : stdLat L n = stdLat L' n := by
  unfold Formalism.L2.Th1.H.stdLat; rw [h]

theorem th0Char_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    {x : ℂ} (hx : x ∈ L'.lattice) : Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ x = Formalism.L2.Th1.F.thetaZeroCharacter L' ω₀' x := by
  obtain ⟨-, -, -, hA, -, -, -, -, -⟩ := Formalism.L2.Th1.F.latticeOnly L L' h
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L' x ((ω₀ - ω₀') / 2) hx hω
  have e0 : x * (starRingEnd ℂ) ω₀ / (Formalism.L2.Th1.F.area L' : ℂ) = x * (starRingEnd ℂ) ω₀' / (Formalism.L2.Th1.F.area L' : ℂ) +
      2 * (x * (starRingEnd ℂ) ((ω₀ - ω₀') / 2) / (Formalism.L2.Th1.F.area L' : ℂ)) := by
    simp only [map_div₀, map_sub, map_ofNat]; ring
  have e1 : Formalism.L2.Th1.F.altE L x ω₀ = Formalism.L2.Th1.F.altE L' x ω₀' + 2 * Formalism.L2.Th1.F.altE L' x ((ω₀ - ω₀') / 2) := by
    simp only [Formalism.L2.Th1.F.altE, Formalism.L2.Th1.F.herm, hA]
    rw [e0]
    simp [Complex.add_im, Complex.mul_im]
  unfold Formalism.L2.Th1.F.thetaZeroCharacter Formalism.L2.Th1.F.semiChar
  rw [h, e1, hk]
  congr 1
  rw [show ((Formalism.L2.Th1.F.altE L' x ω₀' + 2 * (k : ℝ) : ℝ) : ℂ) = (Formalism.L2.Th1.F.altE L' x ω₀' : ℂ) + (k : ℂ) * 2 by
    push_cast; ring]
  rw [mul_add, Complex.exp_add, show (Real.pi : ℂ) * Complex.I * ((k : ℂ) * 2) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem stdData_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    (hn : ω₀ / 2 ∉ L.lattice) {n : Type} [Fintype n] [DecidableEq n] {hh : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)}
    {α : (n → ℂ) → ℂ} {β : (Fin 4 × n → ℂ) → ℂ} {g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)}
    (S : StdData L' ω₀' hh Λ α β g) : StdData L ω₀ hh Λ α β g := by
  have hS := KS.stdH_congr h (Fin 4 × n)
  have hL := stdLat_congr h (Fin 4 × n)
  refine ⟨?_, hn, ?_, S.alpha0, ?_, ?_, S.betaAlpha, ?_, ?_, ?_⟩
  · rw [h, show ω₀ = ω₀' + ((ω₀ - ω₀') / 2 + (ω₀ - ω₀') / 2) by ring]
    exact add_mem S.per (add_mem hω hω)
  · rw [hS]; exact S.isom
  · intro x hx
    have hx' : x ∈ stdLat L' (Fin 4 × n) := hL ▸ hx
    rw [S.betaStd x hx']
    unfold Formalism.L2.Th1.H.stdChar
    exact (Finset.prod_congr rfl fun i _ => th0Char_congr h hω (hx' i (Set.mem_univ i))).symm
  · rw [hS]; exact S.betaSemi
  · rw [hS]; exact S.selfDual
  · rw [hL]; exact S.idx₁
  · rw [hL]; exact S.idx₂

theorem kernel4_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ}
    (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice) (hn : ω₀' / 2 ∉ L'.lattice) {n : Type} [Fintype n] [DecidableEq n]
    (Λ : AddSubgroup (n → ℂ)) (cq : ℝ) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    kernel4 L ω₀ Λ (alphaQ cq (stdH L (Fin 4 × n))) g = kernel4 L' ω₀' Λ (alphaQ cq (stdH L' (Fin 4 × n))) g := by
  unfold kernel4 F0 stdLat
  rw [KS.stdH_congr h, KS.thetaNull_congr_lattice h hω hn, h]

theorem isomStdCm (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ D.host.d) (hB : B.IsCm a₀ b₀ ha hd lam hlam) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (hj : jacobiSym (-(D.host.d : ℤ)) q = 1) (hco : Nat.Coprime (Ideal.absNorm cc) q) (ι : ℂ ≃+* ℂ_[q]) :
    ∃ (g : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ),
      StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
        (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g ∧
      ¬ q ∣ relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
        (imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ∧
      ‖ι e‖ = 1 ∧
      tens4 B.thMM = e • kernel4 B.L B.ω₀ B.lamM (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g := by
  have hK := GlobalTheory.T.norm_kappa_sq_mul_det_splitPrime D cc δ B hcc hδ q hq2 hj hco ι
  obtain ⟨hL, hω⟩ := hB
  have hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
    (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := B.stdOK hcc hδ
  have hsd := selfDual_lamM B hcc hδ
  have hst := stable_lamM B b₀ (odd_of_cmOK hcm)
  have hspec := B.thMM_spec (B.stdOK hcc hδ)
  have h2 : tens4 B.thMM = B.kappa • kernel4 B.L B.ω₀ B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := hspec.2
  have iso := hS.isom
  have i1 := hS.idx₁
  have i2 := hS.idx₂
  rw [hω] at h2 ⊢
  rw [hL] at h2 hK iso i1 i2 hsd ⊢
  have hsda := CmData.selfDual_img _ _ B.gC iso _ (CmData.isSelfDual_matH_blk4_pow4 _ B.lamM hsd)
  have hsta : ∀ x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM),
      cmTheta b₀ D.host.d • x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) := by
    rintro x ⟨x', hx', rfl⟩
    refine ⟨cmTheta b₀ D.host.d • x', fun a' => hst _ (hx' a'), ?_⟩
    simp
  obtain ⟨u, huiso, hufix, j1, jl, j2⟩ := localStandard a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (Fin 4 × D.what₂.Tau) _
    hsda hsta i1 i2 q Fact.out
  have hκu := hK u huiso j1 jl j2
  rw [← KR.imgLat_trans] at j1 jl j2
  have hg₁ : IsIsom (matH (blk4 (hOne (cmL a₀ b₀ D.host.d ha hd lam hlam) D.what₂.Tau)))
      (stdH (cmL a₀ b₀ D.host.d ha hd lam hlam) (Fin 4 × D.what₂.Tau))
      ((B.gC.trans u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) :
        (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
    intro x y
    have h1 := huiso (B.gC x) (B.gC y)
    have h0 := iso x y
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply] at h0 h1 ⊢
    rw [h1, h0]
  have D0 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM B.gC iso hsd hst i1 i2
  have D1 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM (B.gC.trans u) hg₁
    hsd hst j1 j2
  have hcomp : B.gC.symm.trans (B.gC.trans u) = u := by
    ext x
    simp
  have hfix : ∀ x, (B.gC.trans u) x = B.gC x → x = 0 := by
    intro x hx
    have h1 : B.gC x = 0 := hufix _ hx
    simpa using congrArg B.gC.symm h1
  rw [← hcomp] at hκu
  obtain ⟨c, hc8, hc⟩ := kernelRatio _ _ D.what₂.Tau _ B.lamM _ _ B.gC (B.gC.trans u) D0 D1 hfix
  exact ⟨B.gC.trans u, B.kappa * c, D1, jl, KR.norm_mul_eq_one ι B.kappa c _ hc8 hκu,
    by rw [h2, hc, smul_smul]; rfl⟩

theorem isomStd : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∃ (g : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ), Formalism.L2.Th1.H.StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))) (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))) g ∧ ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) ∧ ‖ι e‖ = 1 ∧ Formalism.L2.Th1.H.tens4 B.thMM = e • Formalism.L2.Th1.H.kernel4 B.L B.ω₀ B.lamM (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))) g := by
  intro D cc δ B hcc hδ q _ hq2 hj hco ι
  obtain ⟨a₀, gg, b₀, c₀, ha, hd, hl, B', hcm, -, hIs, hlat, -, -, -, hω, -, hth⟩ := thMMReBase' D cc δ B hcc
  have h : B.L.lattice = B'.L.lattice := hlat.symm
  obtain ⟨G, e, hS, hidx, he, hten⟩ := isomStdCm D cc δ B' hcc hδ a₀ b₀ c₀ ha hd _ hl hcm hIs q hq2 hj hco ι
  have hωB' : (B.ω₀ - B'.ω₀) / 2 ∈ B'.L.lattice := h ▸ hω
  have hω' : (B'.ω₀ - B.ω₀) / 2 ∈ B.L.lattice := by
    have := neg_mem hω
    rwa [show -((B.ω₀ - B'.ω₀) / 2) = (B'.ω₀ - B.ω₀) / 2 by ring] at this
  have hk : kernel4 B'.L B'.ω₀ B'.lamM (alphaQ B'.cq (stdH B'.L (Fin 4 × D.what₂.Tau))) G
      = kernel4 B.L B.ω₀ B.lamM (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) G :=
    kernel4_congr hlat hω' (Base.half_not_mem B) B.lamM B.cq G
  refine ⟨G, e, ?_, ?_, he, ?_⟩
  · have hS' := hS
    rw [← KS.hOne_congr h, ← KS.stdH_congr h] at hS'
    exact stdData_congr h hωB' (Base.half_not_mem B) hS'
  · rw [stdLat_congr h]; exact hidx
  · rw [← hth, hten, hk]

end GlobalTheory.CmThetaMoment
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStandardIsometryFourthPowerSplitPrimeStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_isometry_fourthPower_split_prime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∃ (g : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ), Formalism.L2.Th1.H.StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))) (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))) g ∧ ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) ∧ ‖ι e‖ = 1 ∧ Formalism.L2.Th1.H.tens4 B.thMM = e • Formalism.L2.Th1.H.kernel4 B.L B.ω₀ B.lamM (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))) g := by
  first | exact @GlobalTheory.CmThetaMoment.isomStd | exact GlobalTheory.CmThetaMoment.isomStd | (intros; apply GlobalTheory.CmThetaMoment.isomStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfTensorFourthPower
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulOfDisjointSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulOfDisjointSupport
open GlobalTheory.MomN

namespace GlobalTheory

theorem mahler_mul_of_disjoint_support :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι']
      (u : ι' → V) (F H : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ H → ∀ (S T : Finset ι'), Disjoint S T →
      (∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u F k = 0) →
      (∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u H k = 0) →
      (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = 0) ∧
      (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) →
        GlobalTheory.MomN.mahler u (fun z => F z * H z) N =
          GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) *
            GlobalTheory.MomN.mahler u H (fun p => if p ∈ T then N p else 0)) := by
  intro V _ _ ι' _ _ u F H hF hH S T hST hFS hHT
  constructor
  · intro N ⟨p, hp, hNp⟩
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V ι' u F H hF hH N]
    apply Finset.sum_eq_zero
    intro k _
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ h)
    have hpT : p ∉ T := fun h => hp (Finset.mem_union_right _ h)
    by_cases hk : k p = 0
    · rw [hHT _ ⟨p, hpT, by simp [hk, hNp]⟩, mul_zero]
    · rw [hFS _ ⟨p, hpS, hk⟩, zero_mul]
  · intro N hN
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V ι' u F H hF hH N]
    rw [Finset.sum_eq_single (fun p => if p ∈ S then N p else 0)]
    · have hfun : (fun i => N i - (fun p => if p ∈ S then N p else 0) i) =
          (fun p => if p ∈ T then N p else 0) := by
        funext p
        by_cases hS : p ∈ S
        · have hT : p ∉ T := Finset.disjoint_left.mp hST hS
          simp only [hS, hT, if_true, if_false, Nat.sub_self]
        · by_cases hT : p ∈ T
          · simp only [hS, hT, if_true, if_false, Nat.sub_zero]
          · have h0 : N p = 0 := hN p (by simp [hS, hT])
            simp only [hS, hT, if_false, h0, Nat.sub_zero]
      exact congrArg (fun g => GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) *
        GlobalTheory.MomN.mahler u H g) hfun
    · intro k hk hne
      by_contra hprod
      have h1 : GlobalTheory.MomN.mahler u F k ≠ 0 := left_ne_zero_of_mul hprod
      have h2 : GlobalTheory.MomN.mahler u H (fun i => N i - k i) ≠ 0 := right_ne_zero_of_mul hprod
      apply hne
      funext p
      rw [Fintype.mem_piFinset] at hk
      have hkp : k p ≤ N p := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hk p))
      by_cases hS : p ∈ S
      · have hT : p ∉ T := Finset.disjoint_left.mp hST hS
        have : N p - k p = 0 := by
          by_contra h
          exact h2 (hHT _ ⟨p, hT, h⟩)
        simp only [hS, if_true]
        omega
      · simp only [hS, if_false]
        by_contra h
        exact h1 (hFS _ ⟨p, hS, h⟩)
    · intro h
      exfalso
      apply h
      rw [Fintype.mem_piFinset]
      intro p
      rw [Finset.mem_range]
      split_ifs <;> omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulOfDisjointSupportStatement
open GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahlerJetCoefficient_mul_of_disjoint_support : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι'] (u : ι' → V) (F H : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ H → ∀ (S T : Finset ι'), Disjoint S T → (∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u F k = 0) → (∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u H k = 0) → (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = 0) ∧ (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) * GlobalTheory.MomN.mahler u H (fun p => if p ∈ T then N p else 0)) := by
  first | exact @GlobalTheory.mahler_mul_of_disjoint_support | exact GlobalTheory.mahler_mul_of_disjoint_support | (intros; apply GlobalTheory.mahler_mul_of_disjoint_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientOfFamilyZeroOffEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientOfFamilyZeroOffEmbedding
open GlobalTheory.MomN
open scoped ContDiff

noncomputable section

namespace GlobalTheory.MomEmbed

open MvPolynomial

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem monoJet_eq_listJet {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (m : κ →₀ ℕ) :
    monoJet v G m = ReciprocityTheory.ChartRestriction.G.PullbackSections.lD G 0 (m.toMultiset.toList.map v) := by
  unfold monoJet
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_eq G 0 _ (List.length_map _)]
  congr 1
  funext i
  simp [List.get_eq_getElem]

theorem monoJet_mapDomain {κ ι' : Type} [Fintype κ] [Fintype ι'] (e : κ ↪ ι') (w : κ → V) (u : ι' → V)
    (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (hw : ∀ i, u (e i) = w i) (m : κ →₀ ℕ) :
    monoJet u G (Finsupp.mapDomain e m) = monoJet w G m := by
  rw [monoJet_eq_listJet, monoJet_eq_listJet]
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_perm (hG.contDiffAt)
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, ← Multiset.map_coe, Multiset.coe_toList,
    Multiset.coe_toList, ← Finsupp.toMultiset_map m e, Multiset.map_map]
  congr 1
  funext i
  exact hw i

theorem mahler_embed : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι']
    (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ i, u (e i) = w i) →
    (∀ p, p ∉ Set.range e → u p = 0) →
    (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u G k = 0) ∧
    (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → GlobalTheory.MomN.mahler u G k = GlobalTheory.MomN.mahler w G (fun i => k (e i))) := by
  intro V _ _ κ ι' _ _ e w u G hG hw hu
  classical
  constructor
  · rintro k ⟨p, hp, hkp⟩
    simp only [GlobalTheory.MomN.mahler]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hkp
    have hP : (∏ i, C (((k i).factorial : ℂ)⁻¹) * Polynomial.aeval (X i : MvPolynomial ι' ℂ) (descPochhammer ℂ (k i))) =
        X p * (C (((k p).factorial : ℂ)⁻¹) *
          Polynomial.aeval (X p : MvPolynomial ι' ℂ) ((descPochhammer ℂ n).comp (Polynomial.X - 1)) *
          ∏ i ∈ Finset.univ.erase p, C (((k i).factorial : ℂ)⁻¹) *
            Polynomial.aeval (X i : MvPolynomial ι' ℂ) (descPochhammer ℂ (k i))) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)]
      simp only [hn, descPochhammer_succ_left, map_mul, Polynomial.aeval_X]
      ring
    rw [hP]
    apply Finset.sum_eq_zero
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul'] at hm
    have hpm : p ∈ m.support := by
      by_contra h
      exact hm (if_neg h)
    have hmem : p ∈ m.toMultiset.toList := by
      rw [Multiset.mem_toList]
      simpa using hpm
    obtain ⟨idx, hidx⟩ := List.get_of_mem hmem
    have hz : monoJet u G m = 0 := by
      unfold monoJet
      exact ContinuousMultilinearMap.map_coord_zero _ idx (by
        show u ((Finsupp.toMultiset m).toList.get idx) = 0
        rw [hidx]
        exact hu p hp)
    rw [hz, mul_zero]
  · intro k hk
    simp only [GlobalTheory.MomN.mahler]
    have hprod : (∏ p : ι', C (((k p).factorial : ℂ)⁻¹) *
        Polynomial.aeval (X p : MvPolynomial ι' ℂ) (descPochhammer ℂ (k p))) =
        rename e (∏ i : κ, C (((k (e i)).factorial : ℂ)⁻¹) *
          Polynomial.aeval (X i : MvPolynomial κ ℂ) (descPochhammer ℂ (k (e i)))) := by
      rw [map_prod]
      symm
      apply Fintype.prod_of_injective e e.injective
      · intro b hb
        simp [hk b hb]
      · intro a
        simp [← Polynomial.aeval_algHom_apply, rename_X]
    rw [hprod, MvPolynomial.support_rename_of_injective e.injective,
      Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective e.injective h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_rename_mapDomain _ e.injective, monoJet_mapDomain e w u G hG hw]

end GlobalTheory.MomEmbed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientOfFamilyZeroOffEmbeddingStatement
open GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahlerJetCoefficient_of_family_zero_off_embedding : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι'] (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ i, u (e i) = w i) → (∀ p, p ∉ Set.range e → u p = 0) → (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u G k = 0) ∧ (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → GlobalTheory.MomN.mahler u G k = GlobalTheory.MomN.mahler w G (fun i => k (e i))) := by
  first | exact @GlobalTheory.MomEmbed.mahler_embed | exact GlobalTheory.MomEmbed.mahler_embed | (intros; apply GlobalTheory.MomEmbed.mahler_embed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfTensorFourthPower
open GlobalTheory.MomN Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.MomRoot

theorem mahler_comp_clm (E V : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (κ : Type) [Fintype κ] (L : E →L[ℂ] V) (u : κ → E) (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (k : κ → ℕ) :
    mahler u (fun z => G (L z)) k = mahler (fun i => L (u i)) G k := by
  unfold GlobalTheory.MomN.mahler
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  unfold GlobalTheory.MomN.monoJet
  have h := L.iteratedFDeriv_comp_right hG (0 : E) (i := m.toMultiset.toList.length) le_top
  change iteratedFDeriv ℂ _ (G ∘ L) 0 _ = _
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]

theorem mahler_embed (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι']
    (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ) (hG : ContDiff ℂ ⊤ G)
    (hu : ∀ i, u (e i) = w i) (hz : ∀ p, p ∉ Set.range e → u p = 0) :
    (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → mahler u G k = 0) ∧
    (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → mahler u G k = mahler w G (fun i => k (e i))) :=
  GlobalTheory.T.mahlerJetCoefficient_of_family_zero_off_embedding V κ ι' e w u G hG hu hz

theorem mahler_mul_disj (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι']
    (u : ι' → V) (F H : V → ℂ) (hF : ContDiff ℂ ⊤ F) (hH : ContDiff ℂ ⊤ H) (S T : Finset ι') (hST : Disjoint S T)
    (hFS : ∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → mahler u F k = 0)
    (hHT : ∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → mahler u H k = 0) :
    (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → mahler u (fun z => F z * H z) N = 0) ∧
    (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) → mahler u (fun z => F z * H z) N =
      mahler u F (fun p => if p ∈ S then N p else 0) * mahler u H (fun p => if p ∈ T then N p else 0)) :=
  GlobalTheory.T.mahlerJetCoefficient_mul_of_disjoint_support V ι' u F H hF hH S T hST hFS hHT

variable {n : Type} [Fintype n]

def sliceL (a : Fin 4) : (Fin 4 × n → ℂ) →L[ℂ] (n → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a, i)

theorem sliceL_apply (a : Fin 4) (z : Fin 4 × n → ℂ) : sliceL a z = slice a z := rfl

def fourBlockInclusionVector (b : Fin 4) (x : n → ℂ) : Fin 4 × n → ℂ := fun z => if z.1 = b then x z.2 else 0

theorem slice_fourBlockInclusionVector (a b : Fin 4) (x : n → ℂ) : slice a (fourBlockInclusionVector b x) = if a = b then x else 0 := by
  funext i; by_cases h : a = b <;> simp [slice, fourBlockInclusionVector, h]

end GlobalTheory.MomRoot

namespace GlobalTheory.MomRoot

theorem jets_root : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : Type) [Fintype n] (ω : ℂ_[q]) (Λ : AddSubgroup (n → ℂ))
    (G : (n → ℂ) → ℂ), ContDiff ℂ ⊤ G → LatInt ι ω (pow4 Λ) (tens4 G) → LatInt ι ω Λ G := by
  intro q _ ι n _ ω Λ G hG hL κ _ v hv
  classical
  set c := ι.symm ω
  rw [GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι (n → ℂ) κ _ G hG]
  intro m
  let U : Fin 4 × κ → (Fin 4 × n → ℂ) := fun p => c • fourBlockInclusionVector p.1 (v p.2)
  have hU : MomInt ι U (tens4 G) := hL (Fin 4 × κ) (fun p => fourBlockInclusionVector p.1 (v p.2)) (fun p a => by
    show slice a (fourBlockInclusionVector p.1 (v p.2)) ∈ Λ
    rw [slice_fourBlockInclusionVector]; split_ifs
    · exact hv _
    · exact Λ.zero_mem)
  have hGa : ∀ a, ContDiff ℂ ⊤ (fun z => G (slice a z)) := fun a => by
    have h : ContDiff ℂ ⊤ (sliceL (n := n) a) := ContinuousLinearMap.contDiff _
    exact hG.comp h
  have ht : tens4 G = fun z => G (slice 0 z) * G (slice 1 z) * G (slice 2 z) * G (slice 3 z) := by
    funext z; simp [tens4, Fin.prod_univ_four]
  have hcd : ContDiff ℂ ⊤ (tens4 G) := by
    rw [ht]; exact (((hGa 0).mul (hGa 1)).mul (hGa 2)).mul (hGa 3)
  have hb := ((GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι _ _ U (tens4 G) hcd).1 hU) (fun p => m p.2)
  let S : Fin 4 → Finset (Fin 4 × κ) := fun a => Finset.univ.filter (fun p => p.1 = a)
  let e : Fin 4 → κ ↪ Fin 4 × κ := fun a => ⟨fun i => (a, i), fun i j h => (Prod.mk.inj h).2⟩
  have hposition : ∀ a, (∀ k : Fin 4 × κ → ℕ, (∃ p, p ∉ S a ∧ k p ≠ 0) → mahler U (fun z => G (slice a z)) k = 0) ∧
      (∀ k : Fin 4 × κ → ℕ, (∀ p, p ∉ S a → k p = 0) →
        mahler U (fun z => G (slice a z)) k = mahler (fun i => c • v i) G (fun i => k (a, i))) := by
    intro a
    have he : ∀ i, e a i = (a, i) := fun _ => rfl
    have hcomp : ∀ k, mahler U (fun z => G (slice a z)) k = mahler (fun p => sliceL a (U p)) G k :=
      fun k => by
        have h := mahler_comp_clm _ _ _ (sliceL a) U G hG k
        simp only [sliceL_apply] at h
        exact h
    have hrange : ∀ p : Fin 4 × κ, p ∈ Set.range (e a) ↔ p ∈ S a := by
      rintro ⟨b, i⟩; simp [Set.mem_range, he, S, eq_comm]
    obtain ⟨h1, h2⟩ := mahler_embed (n → ℂ) κ (Fin 4 × κ) (e a) (fun i => c • v i) (fun p => sliceL a (U p)) G hG
      (fun i => by simp [U, he, sliceL_apply, slice_fourBlockInclusionVector])
      (fun p hp => by
        have : p.1 ≠ a := fun h => hp ((hrange p).2 (by simp [S, h]))
        simp [U, sliceL_apply, slice_fourBlockInclusionVector, Ne.symm this])
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [hcomp]; obtain ⟨p, hp, hk⟩ := hk; exact h1 k ⟨p, by rwa [hrange], hk⟩
    · rw [hcomp]; exact h2 k (fun p hp => hk p (by rwa [← hrange]))
  have dj : ∀ (A : Finset (Fin 4)) (b : Fin 4), b ∉ A → Disjoint (A.biUnion S) (S b) := by
    intro A b hb
    rw [Finset.disjoint_left]; intro p hp hq
    simp only [Finset.mem_biUnion, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp; exact hb (hq ▸ ha)
  have u1 : ({0} : Finset (Fin 4)).biUnion S = S 0 := by simp
  have u2 : ({0, 1} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 := by simp [Finset.biUnion_insert]
  have u3 : ({0, 1, 2} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 ∪ S 2 := by
    simp [Finset.biUnion_insert, Finset.union_assoc]
  have d1 := dj {0} 1 (by decide)
  have d2 := dj {0, 1} 2 (by decide)
  have d3 := dj {0, 1, 2} 3 (by decide)
  rw [u1] at d1; rw [u2] at d2; rw [u3] at d3
  obtain ⟨A1v, A1⟩ := mahler_mul_disj _ _ U _ _ (hGa 0) (hGa 1) (S 0) (S 1) d1 (hposition 0).1 (hposition 1).1
  obtain ⟨A2v, A2⟩ := mahler_mul_disj _ _ U _ _ ((hGa 0).mul (hGa 1)) (hGa 2) (S 0 ∪ S 1) (S 2) d2 A1v (hposition 2).1
  obtain ⟨-, A3⟩ := mahler_mul_disj _ _ U _ _ (((hGa 0).mul (hGa 1)).mul (hGa 2)) (hGa 3)
    (S 0 ∪ S 1 ∪ S 2) (S 3) d3 A2v (hposition 3).1
  have key : mahler U (tens4 G) (fun p => m p.2) = (mahler (fun i => c • v i) G m) ^ 4 := by
    rw [ht, A3 _ ?_, A2 _ ?_, A1 _ ?_, (hposition 0).2 _ ?_, (hposition 1).2 _ ?_, (hposition 2).2 _ ?_, (hposition 3).2 _ ?_]
    · simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      norm_num
      ring
    all_goals
      intro p hp
      rcases p with ⟨b, i⟩
      simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      fin_cases b <;> simp at hp ⊢
  rw [key, map_pow, norm_pow] at hb
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb
end GlobalTheory.MomRoot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfTensorFourthPowerStatement
open GlobalTheory.MomN Formalism.L2.Th1.H
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_of_tensorFourthPower : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : Type) [Fintype n] (ω : ℂ_[q]) (Λ : AddSubgroup (n → ℂ)) (G : (n → ℂ) → ℂ), ContDiff ℂ ⊤ G → LatInt ι ω (pow4 Λ) (tens4 G) → LatInt ι ω Λ G := by
  first | exact @GlobalTheory.MomRoot.jets_root | exact GlobalTheory.MomRoot.jets_root | (intros; apply GlobalTheory.MomRoot.jets_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaBaseVectorTranslatesIntegral
noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_of_analytic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℂ}
    (h : AnalyticOnNhd ℂ f Set.univ) : ContDiff ℂ ⊤ f :=
  contDiffOn_univ.1 (h.contDiffOn uniqueDiffOn_univ)

theorem contDiff_opU_one (L : PeriodPair) (s : ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.F.opU L s f) := by
  have hd : Differentiable ℂ (Formalism.L2.Th1.F.opU L s f) := by
    have h1 : Differentiable ℂ (fun z : ℂ => f (z + s)) := hf.comp (differentiable_id.add_const s)
    have h2 : Differentiable ℂ (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z s
        - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L s s / 2)) := by
      unfold Formalism.L2.Th1.F.herm
      fun_prop
    exact h1.mul h2
  exact hd.contDiff

theorem norm_sqrt_inv {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (hm : Nat.Coprime m q) :
    ‖ι (((Real.sqrt m : ℝ) : ℂ)⁻¹)‖ = 1 := by
  have h1 : (((Real.sqrt m : ℝ) : ℂ)) ^ 2 = (m : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg m)]; simp
  have h2 : ‖ι ((Real.sqrt m : ℝ) : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_natCast]
    exact GlobalTheory.MomOne.Basic.norm_nat_eq_one hm.symm
  have h3 : ‖ι ((Real.sqrt m : ℝ) : ℂ)‖ = 1 := by
    have := norm_nonneg (ι ((Real.sqrt m : ℝ) : ℂ))
    nlinarith [sq_nonneg (‖ι ((Real.sqrt m : ℝ) : ℂ)‖ - 1), sq_nonneg (‖ι ((Real.sqrt m : ℝ) : ℂ)‖ + 1)]
  rw [map_inv₀, norm_inv, h3, inv_one]

theorem norm_root {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) :
    ‖ι z‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm).1 (by rw [← norm_pow, ← map_pow, hz, map_one, norm_one])

theorem translates_latInt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (t : D.what₂.Tau → ℂ) (n : ℕ), Nat.Coprime n q → (n : ℂ) • t ∈ B.lamM → LatInt ι (Ω / ι δ₀) B.lamM (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
  intro D cc δ B hcc hδ q _ hq2 hjac hcop ι δ₀ θ Ω hPer t n hn hnt
  obtain ⟨g, e, hS, hidx, he, hten⟩ := GlobalTheory.T.exists_standard_isometry_fourthPower_split_prime D cc δ B hcc hδ q hq2 hjac hcop ι

  have hmem : B.thMM ∈ Formalism.L2.Th1.H.Th (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))
      (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))) B.lamM :=
    (thM_spec B.L B.ω₀ B.cq B.lamM B.gC B.kappa (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) B.kappa_ne_zero).1
  have hUs : ContDiff ℂ ⊤ (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) :=
    contDiff_of_analytic (Formalism.L2.Th1.H.opUAnalytic (D.what₂.Tau → ℂ) _ t B.thMM hmem.1)
  have hthd : Differentiable ℂ B.th0 := (Formalism.L2.Th1.F.th0Basic B.L B.ω₀ hS.per hS.half).1

  obtain ⟨S, hSr⟩ := (Formalism.L2.Th1.H.repsExist _ _ _ hS.idx₁).1
  have hshape := Formalism.L2.Th1.H.quadraticSemicharacter_identity_reformulated₂ B.L B.ω₀ D.what₂.Tau (hOne B.L D.what₂.Tau) B.lamM _ _ g hS e B.thMM hten S hSr t
  have hidxC : Nat.Coprime (Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau))
      (Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) q :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hidx).symm
  set Im := Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM) with hIm
  set St := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hSt
  set idx := Formalism.L2.Th1.H.relIdx St Im with hidxdef
  set v : Fin 4 × D.what₂.Tau → ℂ := g (fun w => t w.2) with hv
  set ω : ℂ_[q] := Ω / ι δ₀ with hω
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : q = 1 := by simpa using hn
    exact (Fact.out : q.Prime).one_lt.ne' h1

  have hnv : (n : ℂ) • v ∈ Im := by
    refine AddSubgroup.mem_map.2 ⟨(n : ℂ) • (fun w : Fin 4 × D.what₂.Tau => t w.2), fun a => hnt, ?_⟩
    show g ((n : ℂ) • fun w : Fin 4 × D.what₂.Tau => t w.2) = (n : ℂ) • v
    rw [map_smul]

  have hord : ∀ x ∈ S, ∀ w, ((n * idx : ℕ) : ℂ) * (v w + x w) ∈ B.L.lattice := by
    intro x hx w
    have h1 : (n : ℂ) • (v + x) ∈ Im := by
      rw [smul_add]
      refine add_mem hnv ?_
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hSr.1 x hx) n
    have h2 := Formalism.L2.Th1.H.relIdx_smul_mem St Im h1
    have h3 := ((AddSubgroup.mem_pi Set.univ).1 h2) w (Set.mem_univ _)
    have e1 : ((n * idx : ℕ) : ℂ) * (v w + x w) = (((idx : ℕ) : ℂ) • (n : ℂ) • (v + x)) w := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      push_cast
      ring
    rw [e1]
    exact h3
  have hNq : Nat.Coprime (n * idx) q := Nat.Coprime.mul_left hn hidxC

  have hfac : ∀ x ∈ S, ∀ w,
      LatInt ι ω St (fun y : Fin 4 × D.what₂.Tau → ℂ => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) := by
    intro x hx w
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ (Fin 4 × D.what₂.Tau → ℂ) ω (lamOf D cc δ) St
      (ContinuousLinearMap.proj w) _ (contDiff_opU_one B.L _ hthd) ?_
      (GlobalTheory.T.cm_theta_translates_prime_to_q_integral D cc δ B hcc hδ q hq2 hjac hcop ι δ₀ θ Ω hPer _ (n * idx) hNq (hord x hx w))
    intro y hy
    refine ⟨1, Nat.coprime_one_left q, ?_⟩
    rw [one_smul, ← B.lat]
    exact ((AddSubgroup.mem_pi Set.univ).1 hy) w (Set.mem_univ _)
  have hcd : ∀ (x : Fin 4 × D.what₂.Tau → ℂ) (w : Fin 4 × D.what₂.Tau),
      ContDiff ℂ ⊤ (fun y : Fin 4 × D.what₂.Tau → ℂ => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) :=
    fun x w => (contDiff_opU_one B.L _ hthd).comp (contDiff_apply ℂ (fun _ => ℂ) w)
  have hprod : ∀ x : Fin 4 × D.what₂.Tau → ℂ, ContDiff ℂ ⊤ (fun y : Fin 4 × D.what₂.Tau → ℂ =>
      ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) :=
    fun x => contDiff_prod fun w _ => hcd x w

  have hP : ∀ x ∈ S, LatInt ι ω St (fun y : Fin 4 × D.what₂.Tau → ℂ =>
      ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) := fun x hx =>
    (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (Fin 4 × D.what₂.Tau → ℂ) ω St).1 (Fin 4 × D.what₂.Tau)
      (fun w y => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) (hcd x) (hfac x hx)

  set r : (Fin 4 × D.what₂.Tau → ℂ) → ℂ := fun x => e * ((Real.sqrt idx : ℝ) : ℂ)⁻¹
      * Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) x
      * Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.H.altE (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) v x : ℂ)) with hr
  have hrn : ∀ x ∈ S, ‖ι (r x)‖ ≤ 1 := by
    intro x hx
    have hx2 := hSr.1 x hx
    have hb : ‖ι (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) x)‖ = 1 := by
      rcases hS.betaSemi.1 x hx2 with h | h <;> simp [h]
    have hph : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I
        * (Formalism.L2.Th1.H.altE (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) v x : ℂ)))‖ = 1 :=
      norm_root ι (m := 2 * n) (by omega)
        (Formalism.L2.Th1.H.phase_root_selfDual _ Im hS.selfDual n hnv hx2)
    simp only [hr, map_mul, norm_mul, he, norm_sqrt_inv ι hidxC, hb, hph, one_mul, le_refl]
  set G : (Fin 4 × D.what₂.Tau → ℂ) → ℂ := fun y =>
    ∑ x ∈ S, r x * ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w) with hG
  have hGd : ContDiff ℂ ⊤ G :=
    ContDiff.sum fun x _ => contDiff_const.mul (hprod x)
  have hGl : LatInt ι ω St G :=
    (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (Fin 4 × D.what₂.Tau → ℂ) ω St).2 _ S r _ (fun x _ => hprod x) hrn hP

  have hpull : LatInt ι ω (Formalism.L2.Th1.H.pow4 B.lamM)
      (fun z => G (LinearMap.toContinuousLinearMap (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) z)) := by
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι _ _ ω St _ _ G hGd ?_ hGl
    intro x hx
    refine ⟨idx, hidxC, ?_⟩
    have h1 : g x ∈ Im := AddSubgroup.mem_map.2 ⟨x, hx, rfl⟩
    have h2 := Formalism.L2.Th1.H.relIdx_smul_mem St Im h1
    rw [Nat.cast_smul_eq_nsmul] at h2
    exact h2
  have hfun : (fun z => G (LinearMap.toContinuousLinearMap (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) z))
      = Formalism.L2.Th1.H.tens4 (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
    funext z
    have hz := hshape (g z)
    rw [LinearEquiv.symm_apply_apply] at hz
    rw [hz]
    rfl
  rw [hfun] at hpull
  exact GlobalTheory.T.latticeJetsAreBoundedMoments_of_tensorFourthPower q ι D.what₂.Tau ω B.lamM _ hUs hpull

end GlobalTheory.MomN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaBaseVectorTranslatesIntegralStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTheta_baseVector_translates_integral : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (t : D.what₂.Tau → ℂ) (n : ℕ), Nat.Coprime n q → (n : ℂ) • t ∈ B.lamM → LatInt ι (Ω / ι δ₀) B.lamM (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
  first | exact @GlobalTheory.MomN.translates_latInt | exact GlobalTheory.MomN.translates_latInt | (intros; apply GlobalTheory.MomN.translates_latInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseThetaTensorPowerTranslatesIntegral
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_opU_of_analytic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Formalism.L2.Th1.H.Sesq V) (x : V) {F : V → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.H.opU H x F) := by
  have h1 : ContDiff ℂ ⊤ F := contDiffOn_univ.1 (hF.contDiffOn uniqueDiffOn_univ)
  let f : V →ₗ[ℂ] ℂ :=
    { toFun := fun z => H z x
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hl : ContDiff ℂ ⊤ (fun z => H z x) := (LinearMap.toContinuousLinearMap f).contDiff
  have h2 : ContDiff ℂ ⊤ (fun z => F (z + x)) := h1.comp (contDiff_id.add contDiff_const)
  have h3 : ContDiff ℂ ⊤ (fun z => Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)) :=
    ((contDiff_const.mul hl).sub contDiff_const).cexp
  exact h2.mul h3

theorem latInt_U_thZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (N N' : ℕ) (s : VC D N N'), TorsPrime D q (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) s → LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (U D B.tor s (B.thZero N N')) := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hcop ι δ₀ θ Ω hP N N' s hs
  have hS := B.stdOK hcc hδ
  have han : AnalyticOnNhd ℂ B.thMM Set.univ := (B.thMM_spec hS).1.1
  have hLat : La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N' := B.lat0OK N N'
  have hA : area (lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  set G : Fin N' → Fin N → (D.what₂.Tau → ℂ) → ℂ := fun i j =>
    Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ i j) B.thMM with hG
  have hU : U D B.tor s (B.thZero N N') = fun z => ∏ i, ∏ j, G i j (entry D.what₂.Tau N N' i j z) := by
    funext z
    rw [U_eq]
    show Formalism.L2.Th1.H.opU (formV (area (lamOf D cc δ)) D.what₂.Tau N N') s (tensPow B.thMM N N') z = _
    rw [hA, opU_tensPow]
    rfl
  have hGc : ∀ i j, ContDiff ℂ ⊤ (G i j) := fun i j => contDiff_opU_of_analytic _ _ han
  have hEc : ∀ i j, ContDiff ℂ ⊤ (fun z : VC D N N' => G i j (entry D.what₂.Tau N N' i j z)) :=
    fun i j => (hGc i j).comp (entry D.what₂.Tau N N' i j).contDiff
  obtain ⟨n, -, hnq, hns⟩ := hs
  rw [hLat] at hns
  have hF : ∀ i j, LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (fun z => G i j (entry D.what₂.Tau N N' i j z)) := by
    intro i j
    have hm : LatInt ι (Ω / ι δ₀) B.lamM (G i j) := by
      refine GlobalTheory.T.cmTheta_baseVector_translates_integral D cc δ B hcc hδ q hq2 hsplit hcop ι δ₀ θ Ω hP (fun τ => s τ i j) n hnq ?_
      have := hns i j
      convert this using 1
      funext τ
      simp [nsmul_eq_mul]
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (D.what₂.Tau → ℂ) (VC D N N') (Ω / ι δ₀) B.lamM
      (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (entry D.what₂.Tau N N' i j) (G i j) (hGc i j) ?_ hm
    intro x hx
    rw [hLat] at hx
    exact ⟨1, Nat.coprime_one_left q, by rw [one_smul]; exact hx i j⟩
  rw [hU]
  refine (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).1 (Fin N')
    (fun i z => ∏ j, G i j (entry D.what₂.Tau N N' i j z)) (fun i => ?_) (fun i => ?_)
  · exact contDiff_prod fun j _ => hEc i j
  · exact (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).1 (Fin N)
      (fun j z => G i j (entry D.what₂.Tau N N' i j z)) (hEc i) (hF i)

end GlobalTheory.MomN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseThetaTensorPowerTranslatesIntegralStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_base_theta_tensor_power_translates_integral : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (N N' : ℕ) (s : VC D N N'), TorsPrime D q (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) s → LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (U D B.tor s (B.thZero N N')) := by
  first | exact @GlobalTheory.MomN.latInt_U_thZero | exact GlobalTheory.MomN.latInt_U_thZero | (intros; apply GlobalTheory.MomN.latInt_U_thZero <;> assumption)
end
