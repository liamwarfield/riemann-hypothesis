module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionAbsSumBoundOfTwoRowBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSumsBoundWithExpLoss
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSumsBoundWithExpLoss
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem rpow_le_rpow_both {x y u w : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hu : 0 ≤ u) (huw : u ≤ w) :
    x ^ u ≤ y ^ w :=
  (Real.rpow_le_rpow_of_exponent_le hx huw).trans
    (Real.rpow_le_rpow (by linarith) hxy (hu.trans huw))

theorem bigH_one_le (C : ℝ) (hC : 0 ≤ C) (m f : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    1 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
  exact Real.one_le_rpow hb (by positivity)

theorem bigH_mono {C D : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D) (m f : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH D m f b := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
  apply Real.rpow_le_rpow_of_exponent_le hb
  have : (0:ℝ) ≤ (m:ℝ)^2 * f := by positivity
  nlinarith

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem xiHyp_mono {C D : ℝ} (hC : 1 ≤ C) (hCD : C ≤ D) {k m f : ℕ} {b v NT : ℝ} {Xi : ℕ → ℝ}
    (hb : 1 ≤ b) (hNT : 1 ≤ NT) (h : XiHyp C k m f b v NT Xi) : XiHyp D k m f b v NT Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hD0 : (0:ℝ) ≤ D := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHD1 := bigH_one_le D hD0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  refine ⟨fun s hs hsk => ?_, fun s hs => ?_⟩
  · obtain ⟨h0, h1⟩ := h.1 s hs hsk
    refine ⟨h0, h1.trans ?_⟩
    have e1 : bigH C m f b ^ C ≤ bigH D m f b ^ D := rpow_le_rpow_both hH1 hHm hC0 hCD
    have e2 : C ^ (s * k * f) ≤ D ^ (s * k * f) := pow_le_pow_left₀ hC0 hCD _
    exact mul_le_mul e1 e2 (by positivity) (by positivity)
  · obtain ⟨h0, h1⟩ := h.2 s hs
    refine ⟨h0, h1.trans ?_⟩
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have e1 : (C * k) ^ (k * f) ≤ (D * k) ^ (k * f) :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCD hk0) _
    have a1 : 1 ≤ bigH C m f b ^ (C * m) := Real.one_le_rpow hH1 (by positivity)
    have a2 : bigH C m f b ^ (C * m) ≤ bigH D m f b ^ (D * m) :=
      rpow_le_rpow_both hH1 hHm (by positivity) (mul_le_mul_of_nonneg_right hCD hm0)
    have e2 : (bigH C m f b ^ (C * m) * NT) ^ (C * k) ≤ (bigH D m f b ^ (D * m) * NT) ^ (D * k) := by
      apply rpow_le_rpow_both
      · nlinarith
      · exact mul_le_mul_of_nonneg_right a2 (by linarith)
      · positivity
      · exact mul_le_mul_of_nonneg_right hCD hk0
    exact mul_le_mul e1 e2 (by positivity) (by positivity)

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem params_mono {C D K K₀ : ℝ} (hC : 1 ≤ C) (hCD : C ≤ D) (hK : K ≤ K₀) {k m f : ℕ} {b g v NT : ℝ}
    (h : Params C K₀ k m f b g v NT 1) : Params D K k m f b g v NT 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hX : (0:ℝ) ≤ (m:ℝ) ^ 5 * f * Real.log b := by positivity
  refine ⟨h1, h2, h3, h4, h5, ?_, h7, h8, h9, ?_, le_rfl, ?_⟩
  · have := mul_le_mul_of_nonneg_right hK hX
    nlinarith
  · refine h10.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_)
    have : (0:ℝ) ≤ (m:ℝ) * f := by positivity
    nlinarith
  · have : (0:ℝ) ≤ D := by linarith
    exact Real.one_le_exp (by positivity)

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

theorem gam_absorb {C Gam : ℝ} (hC : 0 ≤ C) {k f : ℕ} (hf : 1 ≤ f) (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    C ^ (k * f) * Gam ≤ (Real.exp 1 * C) ^ (k * f) := by
  rw [mul_pow, ← Real.exp_nat_mul, mul_one, mul_comm (Real.exp _)]
  refine mul_le_mul_of_nonneg_left (hG.trans (Real.exp_le_exp.2 ?_)) (by positivity)
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  nlinarith

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem ndRow_mono {C Gam : ℝ} (hC : 1 ≤ C) {k m f s : ℕ} {b g v : ℝ} {Xi : ℕ → ℝ}
    (hf : 1 ≤ f) (hb : 1 ≤ b) (hg : 0 < g) (hv : 0 ≤ v) (hXi : 0 ≤ Xi s)
    (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    ndRow C k m f s b g v Gam Xi ≤ ndRow (Real.exp 1 * C) k m f s b g v 1 Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD0 : (0:ℝ) ≤ Real.exp 1 * C := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  have hHDpos : 0 < bigH (Real.exp 1 * C) m f b := lt_of_lt_of_le zero_lt_one (hH1.trans hHm)
  have hHCpos : 0 < bigH C m f b := lt_of_lt_of_le zero_lt_one hH1
  have e0 : 0 ≤ (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s := by positivity
  have eH : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) ≤
      bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    apply rpow_le_rpow_both hH1 hHm (by positivity)
    have : (0:ℝ) ≤ ((s : ℝ) + m) * (m : ℝ) ^ 2 := by positivity
    nlinarith
  have eP : (C * s * f) ^ (6 * s * f) ≤ (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0:ℝ) ≤ (s : ℝ) * f := by positivity
    nlinarith
  have eG := gam_absorb hC0 hf hG (k := k)
  unfold ndRow
  calc (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam
      = ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (C ^ (k * f) * Gam) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) := by ring
    _ ≤ ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (Real.exp 1 * C) ^ (k * f) *
        bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) *
        (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
      have hH0 : 0 ≤ bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) :=
        le_trans zero_le_one (Real.one_le_rpow hH1 (by positivity))
      gcongr
    _ = _ := by ring

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem degRow_mono {C Gam : ℝ} (hC : 1 ≤ C) {k m f s : ℕ} {b g v : ℝ} {Xi : ℕ → ℝ}
    (hf : 1 ≤ f) (hb : 1 ≤ b) (hg : 0 < g) (hv : 0 ≤ v) (hXi : 0 ≤ Xi s)
    (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    degRow C k m f s b g v Gam Xi ≤ degRow (Real.exp 1 * C) k m f s b g v 1 Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD0 : (0:ℝ) ≤ Real.exp 1 * C := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  have hHDpos : 0 < bigH (Real.exp 1 * C) m f b := lt_of_lt_of_le zero_lt_one (hH1.trans hHm)
  have hHCpos : 0 < bigH C m f b := lt_of_lt_of_le zero_lt_one hH1
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb
  have e0 : 0 ≤ (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s := by positivity
  have eH : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) ≤
      bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    apply rpow_le_rpow_both hH1 hHm (by positivity)
    have : (0:ℝ) ≤ ((s : ℝ) + m) * (m : ℝ) ^ 2 := by positivity
    nlinarith
  have eP : (C * s * f) ^ (6 * s * f) ≤ (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0:ℝ) ≤ (s : ℝ) * f := by positivity
    nlinarith
  have eE : Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) ≤
      Real.exp (Real.exp 1 * C * (m : ℝ) ^ 6 * f * Real.log b) := by
    apply Real.exp_le_exp.2
    have : (0:ℝ) ≤ (m : ℝ) ^ 6 * f * Real.log b := by positivity
    nlinarith
  have eQ : (C / k) ^ (k * f) ≤ (Real.exp 1 * C / k) ^ (k * f) := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right hCD (Nat.cast_nonneg k)
  have eG := gam_absorb hC0 hf hG (k := k)
  have hH0 : 0 ≤ bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) :=
    le_trans zero_le_one (Real.one_le_rpow hH1 (by positivity))
  unfold degRow
  calc (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam *
        Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f)
      = ((2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (C ^ (k * f) * Gam) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) *
        Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f) := by ring
    _ ≤ ((2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (Real.exp 1 * C) ^ (k * f) *
        bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) *
        (Real.exp 1 * C * s * f) ^ (6 * s * f) *
        Real.exp (Real.exp 1 * C * (m : ℝ) ^ 6 * f * Real.log b) * (Real.exp 1 * C / k) ^ (k * f) := by
      gcongr
    _ = _ := by ring

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg


open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem corankSums_expLoss : ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ),
    Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k m f b g v NT 1 → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k m f b v NT Xi → 0 ≤ Gam →
    Gam ≤ Real.exp ((k : ℝ) / 8) →
    ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Gam Xi ≤ (Real.sqrt g)⁻¹ ^ (k * f) ∧
    ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k m f s b g v Gam Xi ≤
      Real.exp (-((k : ℝ) * f * Real.log k) / 2) := by
  intro C hC
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD : 1 ≤ Real.exp 1 * C := hC.trans hCD
  obtain ⟨K1, H1⟩ := Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe (Real.exp 1 * C) hD
  obtain ⟨K2, H2⟩ := Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe (Real.exp 1 * C) hD
  refine ⟨max K1 K2, ?_⟩
  intro k m f b g v NT Gam Xi hP hXi _hG0 hG
  obtain ⟨hm4, hmf, hfk, hb2, hg8, -, hv1, -, hNT1, -⟩ := id hP
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hf : 1 ≤ f := by omega
  have hk : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkb : 0 < (k:ℝ) * b := mul_pos (by linarith) (by linarith)
  have hg : 0 < g := lt_of_lt_of_le (pow_pos hkb 8) hg8
  have hv : (0:ℝ) ≤ v := by linarith
  have P1 := params_mono hC hCD (le_max_left K1 K2) hP
  have P2 := params_mono hC hCD (le_max_right K1 K2) hP
  have X' := xiHyp_mono hC hCD hb1 hNT1 hXi
  have hXs : ∀ s ∈ Finset.Icc 2 k, 0 ≤ Xi s := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    by_cases h2 : s + 2 ≤ k
    · exact (hXi.1 s hs.1 h2).1
    · exact (hXi.2 s (by omega)).1
  refine ⟨?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun s hs => ?_) (H1 k m f b g v NT 1 Xi P1 X')
    exact ndRow_mono hC hf hb1 hg hv (hXs s hs) hG
  · have E2 := H2 k m f b g v NT 1 Xi P2 X'
    rw [one_pow, inv_one, mul_one] at E2
    refine le_trans (Finset.sum_le_sum fun s hs => ?_) E2
    exact degRow_mono hC hf hb1 hg hv (hXs s hs) hG

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSumsBoundWithExpLossStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corankSums_bound_with_expLoss : ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ), Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k m f b g v NT 1 → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k m f b v NT Xi → 0 ≤ Gam → Gam ≤ Real.exp ((k : ℝ) / 8) → ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Gam Xi ≤ (Real.sqrt g)⁻¹ ^ (k * f) ∧ ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k m f s b g v Gam Xi ≤ Real.exp (-((k : ℝ) * f * Real.log k) / 2) := by
  first | exact @GlobalTheory.Core.Deg.corankSums_expLoss | exact GlobalTheory.Core.Deg.corankSums_expLoss | (intros; apply GlobalTheory.Core.Deg.corankSums_expLoss <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSizeHypothesisExplicitConstantSiegelMass
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSizeHypothesisExplicitConstantSiegelMass
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg
theorem xiSizes_explicit : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), 1 ≤ Cl → Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (Cnt.NT D u) (BridgeLemma.XiB D large₂ u C) := by
  intro hS C hC D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hCl hH
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hmax : max 1 (1 / Cl) ≤ 1 := max_le le_rfl (by rw [div_le_one (by linarith)]; exact hCl)
  have hM2 := Formalism.MainNotions.BridgeLemma₂.plane_mass_bound_parameters D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 8
    (le_trans (mul_le_mul_of_nonneg_left hmax (by norm_num)) (by norm_num))
  have hX := Formalism.MainNotions.BridgeLemma.first_bound_of_mass_ratio D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 8 408
    (Formalism.MainNotions.BridgeLemma.lattice_count_first_of_siegel hS D) hM2 (by norm_num) le_rfl hCl
  have hCX : |(408 : ℝ)| * max 1 |Real.exp 1 * Real.pi| ≤ C := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 408), abs_of_pos (by positivity), max_eq_right he]; exact hC
  have hXi := Formalism.MainNotions.BridgeLemma.xiHyp_of_stX D large₂ hH hX hCX (by linarith)
  rw [← Formalism.MainNotions.BridgeLemma.d_m_eq D]
  exact hXi
end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSizeHypothesisExplicitConstantSiegelMassStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corankSizeHypothesis_explicitConstant_siegelMass : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), 1 ≤ Cl → Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (Cnt.NT D u) (BridgeLemma.XiB D large₂ u C) := by
  first | exact @GlobalTheory.Core.Deg.xiSizes_explicit | exact GlobalTheory.Core.Deg.xiSizes_explicit | (intros; apply GlobalTheory.Core.Deg.xiSizes_explicit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairAbsCorankGeTwoLeSumCorankClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairAbsCorankGeTwoLeSumCorankClasses
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem pairAbs_big_le_sum_classes : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (k : ℕ) (B : ℕ → ℝ), X.AbsConv → (∀ p ∈ X.big X.nzSet, X.s0 p.1 p.2 ≤ k) → (∀ s, 2 ≤ s → s ≤ k → Formalism.L2.SG.LoopsCut.ClassLe X (Formalism.L2.SG.LoopsCut.bigS X s) (B s)) → X.pairAbs (X.big X.nzSet) ≤ ∑ s ∈ Finset.Icc 2 k, B s := by
  intro τ Rw I H H₁ _ _ _ _ _ X k B hA hk hS
  have hG : 0 ≤ X.Gam1 := hA.2.2.le
  have hv : Summable (fun t => ‖X.vec t‖) := hA.2.1
  have hcov : X.big X.nzSet ⊆
      (⋃ s ∈ Finset.Icc 2 k, Formalism.L2.SG.LoopsCut.bigS X s) ∪ (∅ : Set (τ × τ)) := by
    intro p hp
    left
    exact Set.mem_iUnion₂.2 ⟨X.s0 p.1 p.2, Finset.mem_Icc.2 ⟨hp.2, hk p hp⟩, ⟨hp.1, rfl⟩⟩
  have hc := Formalism.L2.SG.LoopsCut.ampSum_cover X hv (Finset.Icc 2 k) (Formalism.L2.SG.LoopsCut.bigS X) ∅
    (X.big X.nzSet) hcov
  have h0 : Formalism.L2.SG.RowsOther.ampSum X (∅ : Set (τ × τ)) = 0 := by
    unfold Formalism.L2.SG.RowsOther.ampSum; simp
  rw [h0, add_zero] at hc
  calc X.pairAbs (X.big X.nzSet)
      ≤ X.Gam1 * Formalism.L2.SG.RowsOther.ampSum X (X.big X.nzSet) :=
        Formalism.L2.SG.RowsOther.pairAbs_le_ampSum X hG _ (Formalism.L2.SG.LoopsCut.amp_summable X hv _)
    _ ≤ X.Gam1 * ∑ s ∈ Finset.Icc 2 k, Formalism.L2.SG.RowsOther.ampSum X (Formalism.L2.SG.LoopsCut.bigS X s) :=
        mul_le_mul_of_nonneg_left hc hG
    _ = ∑ s ∈ Finset.Icc 2 k, X.Gam1 * Formalism.L2.SG.RowsOther.ampSum X (Formalism.L2.SG.LoopsCut.bigS X s) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ s ∈ Finset.Icc 2 k, B s :=
        Finset.sum_le_sum fun s hs => hS s (Finset.mem_Icc.1 hs).1 (Finset.mem_Icc.1 hs).2

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairAbsCorankGeTwoLeSumCorankClassesStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairAbs_corank_ge_two_le_sum_corankClasses : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (k : ℕ) (B : ℕ → ℝ), X.AbsConv → (∀ p ∈ X.big X.nzSet, X.s0 p.1 p.2 ≤ k) → (∀ s, 2 ≤ s → s ≤ k → Formalism.L2.SG.LoopsCut.ClassLe X (Formalism.L2.SG.LoopsCut.bigS X s) (B s)) → X.pairAbs (X.big X.nzSet) ≤ ∑ s ∈ Finset.Icc 2 k, B s := by
  first | exact @GlobalTheory.Core.Deg.pairAbs_big_le_sum_classes | exact GlobalTheory.Core.Deg.pairAbs_big_le_sum_classes | (intros; apply GlobalTheory.Core.Deg.pairAbs_big_le_sum_classes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionAbsSumBoundOfTwoRowBounds
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem collS_of_rowBounds : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ CT C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → CT ≤ C → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), thr ≤ C' → thr ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv → TieAt hF hI large₂ u T Z → UnitaryVolumeMass.FormAt D u → BridgeLemma.RowsND T Z C → BridgeLemma.RowsDeg T Z C → CollS Y u := by
  intro hS CT C hC hCT
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hC1 : (1 : ℝ) ≤ C := by nlinarith
  obtain ⟨K₀, hK⟩ := GlobalTheory.T.corankSums_bound_with_expLoss C hC1
  refine ⟨max K₀ 4, ?_⟩
  intro D large₂ X Y hF hI u T Z C' Cl Cg cb Cu cT C0 hC' hCl hH hCc hAbs hTie hFo hn hd
  have hK₀ : K₀ ≤ C' := le_trans (le_max_left _ _) hC'
  have hC'1 : (1 : ℝ) ≤ C' := by linarith [le_max_right K₀ 4]
  have hCl4 : (4 : ℝ) ≤ Cl := le_trans (le_max_right _ _) hCl
  have hHy := Formalism.MainNotions.count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 1 hH.2.1 hH.1 hH.2.2 (by linarith) hC'1 le_rfl u
  have hXi := GlobalTheory.T.corankSizeHypothesis_explicitConstant_siegelMass hS C hC D large₂ u u C' Cl Cg cb Cu cT CT C0 1 (by linarith) hHy
  have hP := Formalism.L2.SG.LoopsCut.params_at hH X u hCl4 hCT hC1 hK₀
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b D large₂
  have hP1 : Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v
      (Cnt.NT D u) 1 := by
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, _, _⟩ := hP
    refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, le_rfl, ?_⟩
    apply Real.one_le_exp
    have hl : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
    have hC0 : (0 : ℝ) ≤ C := by linarith
    positivity
  have hGam0 : 0 ≤ GamS D large₂ := (Real.exp_pos _).le
  have hGam8 : GamS D large₂ ≤ Real.exp ((D.R.k : ℝ) / 8) := by
    unfold GamS
    apply Real.exp_le_exp.2
    have h1 : 8 * large₂.CGam ≤ C' := hH.1.1
    have h2 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.2.1
    have hL := Formalism.MainNotions.BridgeLemma.d_one_le_L D large₂
    have hM : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
    nlinarith
  obtain ⟨hND, hDG⟩ := hK D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v (Cnt.NT D u) (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) hP1 hXi hGam0 hGam8
  obtain ⟨hJ, hW, hFC, _, _, _, _⟩ := hTie
  have hG := Formalism.L2.SG.LoopTieOf.gammaFixed_of_hypotheses Y hH
  have hm := Formalism.MainNotions.BridgeLemma.d_m_eq D
  have hg : (X.B.g : ℝ) = gg D := by rw [X.g_eq]; unfold gg; push_cast; ring
  have hcls : ∀ s, 2 ≤ s → s ≤ D.R.k → Formalism.L2.SG.LoopsCut.ClassLe (Y.tO u u) (Formalism.L2.SG.LoopsCut.bigS (Y.tO u u) s)
      ((fun s : ℕ => (D.duS u : ℝ) *
        (Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
                  (BridgeLemma.XiB D large₂ u C) * BridgeLemma.rDD D u +
          Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
            (BridgeLemma.XiB D large₂ u C))) s) := by
    intro s h2 hk
    have base := Formalism.L2.SG.LoopTieOf.gam_mul_le hG Z hFo
      (Formalism.L2.SG.LoopTieOf.classS_le T hJ hW hFC Z C hn hd s h2 hk)
    rw [hm, ← hg] at base
    exact base
  have habs := GlobalTheory.T.pairAbs_corank_ge_two_le_sum_corankClasses _ _ _ _ _ (Y.tO u u) D.R.k _ hAbs
    (fun p _ => Formalism.L2.SG.LoopsCut.corank_le_k Y u u p.1 p.2) hcls
  have hdd : ddC X Y u u = (D.duS u : ℝ) * BridgeLemma.rDD D u := Formalism.L2.SG.LoopTieOf.ddC_eq hCc u u
  have hdu : duC X Y u = (D.duS u : ℝ) := hCc.2.2.1 u
  have hdr0 : 0 ≤ (D.duS u : ℝ) * BridgeLemma.rDD D u := hdd ▸ dd_nonneg hCc u u
  have hd0 : (0 : ℝ) ≤ (D.duS u : ℝ) := Nat.cast_nonneg _
  have hgg : ((X.B.g : ℕ) : ℝ) = (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by rw [X.g_eq]; push_cast; ring
  unfold CollS
  rw [hdd, hdu]
  set d : ℝ := (D.duS u : ℝ) with hdef
  set r : ℝ := BridgeLemma.rDD D u with hrdef
  set N := fun s : ℕ => Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) with hN
  set G := fun s : ℕ => Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) with hGd
  have hsum : ∑ s ∈ Finset.Icc 2 D.R.k, d * (N s * r + G s) =
      d * r * ∑ s ∈ Finset.Icc 2 D.R.k, N s + d * ∑ s ∈ Finset.Icc 2 D.R.k, G s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  calc _ ≤ ∑ s ∈ Finset.Icc 2 D.R.k, d * (N s * r + G s) := habs
    _ = d * r * ∑ s ∈ Finset.Icc 2 D.R.k, N s + d * ∑ s ∈ Finset.Icc 2 D.R.k, G s := hsum
    _ ≤ d * r * (√(X.B.g : ℝ))⁻¹ ^ (D.R.k * D.R.f) +
        d * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k) / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hND hdr0) (mul_le_mul_of_nonneg_left hDG hd0)
    _ = _ := by rw [hgg]; ring

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionAbsSumBoundOfTwoRowBoundsStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.collisionAbsSum_bound_of_two_rowBounds : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ CT C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → CT ≤ C → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), thr ≤ C' → thr ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv → TieAt hF hI large₂ u T Z → UnitaryVolumeMass.FormAt D u → BridgeLemma.RowsND T Z C → BridgeLemma.RowsDeg T Z C → CollS Y u := by
  first | exact @GlobalTheory.Core.Deg.collS_of_rowBounds | exact GlobalTheory.Core.Deg.collS_of_rowBounds | (intros; apply GlobalTheory.Core.Deg.collS_of_rowBounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateCollisionRowBoundAtParametersStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateCollisionRowBoundAtParams
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Deg

theorem rowsDeg_at_record : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → CT ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → 2 * C2 ≤ C → |Ca| ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), 3 * |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsDeg T Z C := by
  intro CT cH cV Ca C2 Ch c C k2 hCT k3 k4 hCh hcC hCsq1 hC2 hCa D large₂ u T Z C' Cl Cg cb Cu cT C0 h3C hH hC3 hHH hV hA hS hTP hG0 hE
  have hc0 : 0 ≤ c := by linarith
  have hC1 : 1 ≤ C := k2.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by nlinarith
  have hHHc : UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 c :=
    BridgeLemma₂.rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) hHH
  have hK := BridgeLemma₂.rows_KBound_of Z hH hHHc k2 hCT
  have hr0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [BridgeLemma₂.rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast BridgeLemma₂.rows_f_pos D
  have hL1 : 1 ≤ large₂.sc.L := BridgeLemma.d_one_le_L D large₂
  have hkm : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have hk5 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.1.2.1
  have ha2 : |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2 ≤ D.R.k := by
    refine le_trans ?_ hk5
    have e1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e4 : (D.R.m : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 := by positivity
    have e2 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ))) (by linarith : 0 ≤ large₂.sc.L - 1)]
    have hab := abs_nonneg C2
    have hP : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by linarith
    calc |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2
        = |C2| * ((D.R.m : ℝ) ^ 2 + 2 * (D.R.m : ℝ) ^ 4) := by ring
      _ ≤ |C2| * (3 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hab
      _ = (3 * |C2|) * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
      _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := mul_le_mul_of_nonneg_right h3C hP
      _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * D.R.k) + 4 * BridgeLemma₂.pairCountExponent D c D.R.k +
    4 * (c * (D.R.rS : ℝ) ^ 2) + (|C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2) / 2 +
    12 * ((D.R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := BridgeLemma₂.pairCountExponent_nonneg D hc0 D.R.k
    positivity
  have hqb := BridgeLemma₂.rows_q_bound (m := D.R.m) (k := D.R.k) (r := D.R.rS) (c := c)
    (cf := Cnt.cF D.R.f) (a2 := |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2)
    (BridgeLemma₂.rows_m_cast _) hr0 hkm hc0 (BridgeLemma₂.rows_cF_le hH) ha2
  have hqb' : ((D.R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * D.R.k * (D.R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold BridgeLemma₂.pairCountExponent; exact hqb
  have hra0 : 0 ≤ ((D.R.rS : ℝ) + 1) * a := by positivity
  have hyp : BridgeLemma₂.rows_Hyps Z C' Cl Cg cb Cu cT CT C0 1 c (9 * c + 3) Ca C2 Ch 1 1
      ⌈((D.R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := hC3
      hHH := hHHc
      hV := BridgeLemma₂.rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) hV
      hDEC := hA.2.2
      ha := hS.1
      hb := hS.2.1
      hp := hA.1
      hpp := hA.2.1
      h6 := hS.2.2.1
      hδ := zero_le_one
      hThA := BridgeLemma.word_theorem_a_admissible D u u
      hT := hTP
      hG0 := hG0
      hE := hE
      hc := hc0
      hCh := hCh
      hdim := BridgeLemma₂.rows_dim_pos Z hH.1 (hS.2.2.2.2 hH.1 u)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine BridgeLemma₂.rows_RowsDeg_record _ hyp hK k2 hcC hC1 hCsq hC2 hCa ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil (((D.R.rS : ℝ) + 1) * a)
  have h2 : (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 ≤
      (|C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2) / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * ((D.R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = ((D.R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end GlobalTheory.Core.Deg
end
end

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerateCollision_rowBound_at_sizeData : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → CT ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → 2 * C2 ≤ C → |Ca| ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), 3 * |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsDeg T Z C := by
  first | exact @GlobalTheory.Core.Deg.rowsDeg_at_record | exact GlobalTheory.Core.Deg.rowsDeg_at_record | (intros; apply GlobalTheory.Core.Deg.rowsDeg_at_record <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NondegenerateCollisionRowBoundAtParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NondegenerateCollisionRowBoundAtParameters
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Deg

section SlopeTestRemainingChoices
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂

theorem rowsND_one_record : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsND T Z C := by
  intro CT cH cV Ca C2 Ch c C hc1 hcH hcV hCh hcC hCC D large₂ u T Z C' Cl Cg cb Cu cT C0 hC2 hH hC3 hHH hVol hAmp hSm
    hTP hG0 hE
  have hc0 : 0 ≤ c := by linarith
  have hC1 : 1 ≤ C := hc1.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by nlinarith
  have hr0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hL1 := d_one_le_L D large₂
  have hkm : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have hk5 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.1.2.1
  have ha2 : |C2| * (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    refine le_trans ?_ hk5
    have hC'0 : 0 ≤ C' := (abs_nonneg C2).trans hC2
    have e1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e2 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 := by positivity
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ))) (by linarith : 0 ≤ large₂.sc.L - 1)]
    have e3 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
    calc |C2| * (D.R.m : ℝ) ^ 2 ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) :=
          mul_le_mul hC2 (e1.trans e2) (by positivity) hC'0
      _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k +
    4 * (c * (D.R.rS : ℝ) ^ 2) + |C2| * (D.R.m : ℝ) ^ 2 / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := pairCountExponent_nonneg D hc0 D.R.k
    positivity
  have hqb := rows_q_bound (m := D.R.m) (k := D.R.k) (r := D.R.rS) (c := c)
    (cf := cF D.R.f) (a2 := |C2| * (D.R.m : ℝ) ^ 2) (rows_m_cast _) hr0 hkm hc0 (rows_cF_le hH) ha2
  have hqb' : ((D.R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * D.R.k * (D.R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold pairCountExponent; exact hqb
  have hra0 : 0 ≤ ((D.R.rS : ℝ) + 1) * a := by positivity
  have hyp : rows_Hyps Z C' Cl Cg cb Cu cT CT C0 1 c (9 * c + 3) Ca C2 Ch 1 1
      ⌈((D.R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := hC3
      hHH := rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) hHH
      hV := rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) hVol
      hDEC := hAmp.2.2
      ha := hSm.1
      hb := hSm.2.1
      hp := hAmp.1
      hpp := hAmp.2.1
      h6 := hSm.2.2.1
      hδ := zero_le_one
      hThA := word_theorem_a_admissible D u u
      hT := hTP
      hG0 := hG0
      hE := hE
      hc := hc0
      hCh := hCh
      hdim := rows_dim_pos Z hH.1 (hSm.2.2.2.2 hH.1 u)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine rows_RowsND_record _ hyp le_rfl hcC hC1 hCsq ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil (((D.R.rS : ℝ) + 1) * a)
  have h2 : C2 * (D.R.m : ℝ) ^ 2 / 2 ≤ |C2| * (D.R.m : ℝ) ^ 2 / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * ((D.R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = ((D.R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end SlopeTestRemainingChoices

end GlobalTheory.Core.Deg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NondegenerateCollisionRowBoundAtParametersStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerateCollision_rowBound_at_parameters : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsND T Z C := by
  first | exact @GlobalTheory.Core.Deg.rowsND_one_record | exact GlobalTheory.Core.Deg.rowsND_one_record | (intros; apply GlobalTheory.Core.Deg.rowsND_one_record <;> assumption)
end
end

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem collS_on : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ S : Set ℝ, AmpOn S → CountBoundOn S → SmallOn S → TieOn S → On S CollS := by
  intro hSMR S hAmp hCnt hSmall hTie
  intro Cg cb Cu cT CT hcb hcT
  obtain ⟨c3, cH, thr1, hC⟩ := hCnt Cg cb Cu cT CT
  obtain ⟨cV, thr2, hT⟩ := hTie Cg cb Cu cT CT
  obtain ⟨Ca, C2, Ch, -, hCh, hA⟩ := hAmp Cg cb Cu cT CT hcb hcT
  set c : ℝ := max (max (max (max c3 1) CT) (|cH| + 2)) (|cV| + 2) with hc
  have hc3 : c3 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcT' : CT ≤ c := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcH : |cH| + 2 ≤ c := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcV : |cV| + 2 ≤ c := le_max_right _ _
  set C : ℝ := max (max (max (max (max c (4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2))) (2 * C2)) |Ca|)
    (408 * (Real.exp 1 * Real.pi))) CT with hCdef
  have hCc : c ≤ C := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hC4 : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hC2 : 2 * C2 ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hCa : |Ca| ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC408 : 408 * (Real.exp 1 * Real.pi) ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCT : CT ≤ C := le_max_right _ _
  obtain ⟨thr3, hA3⟩ := hA (9 * c + 3) 1 one_pos
  obtain ⟨thr4, hS⟩ := hSmall Cg cb Cu cT CT 1 hcb hcT one_pos
  obtain ⟨thr5, hsum⟩ := GlobalTheory.T.collisionAbsSum_bound_of_two_rowBounds hSMR CT C hC408 hCT
  refine ⟨max (max (max (max (max thr1 thr2) thr3) thr4) thr5) (max (3 * |C2|) 4), ?_⟩
  intro C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u hCG hTies hadm hH0 hConc hAbs
  have hle : ∀ {x : ℝ}, max (max (max (max (max thr1 thr2) thr3) thr4) thr5) (max (3 * |C2|) 4) ≤ x →
      thr1 ≤ x ∧ thr2 ≤ x ∧ thr3 ≤ x ∧ thr4 ≤ x ∧ thr5 ≤ x ∧ 3 * |C2| ≤ x ∧ 4 ≤ x := by
    intro x hx
    simp only [max_le_iff] at hx
    exact ⟨hx.1.1.1.1.1, hx.1.1.1.1.2, hx.1.1.1.2, hx.1.1.2, hx.1.2, hx.2.1, hx.2.2⟩
  obtain ⟨h1', h2', h3', h4', h5', h6', h7'⟩ := hle hC'
  obtain ⟨h1l, h2l, h3l, h4l, h5l, -, h7l⟩ := hle hCl
  have hCnt' := hC C0 hC0 C' Cl h1' h1l D large₂ u
  have hc3' := hCnt'.1 c hc3
  obtain ⟨T, Z, hTA, hVol⟩ := hT C0 hC0 C' Cl h2' h2l D large₂ X Y hF hI u hTies hH0 hConc
  have hAmpAt := hA3 C0 hC0 C' Cl h3' h3l D large₂ hCG hTies hadm hConc.2.2.2.2.2.2.2
  have hSm := hS C0 hC0 C' Cl h4' h4l D large₂ hTies hadm
  have hHyp : Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 :=
    Formalism.MainNotions.count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 1 hH0.2.1 hH0.1 hH0.2.2 (by linarith) (by linarith) le_rfl u
  have hC2' : |C2| ≤ C' := by have := abs_nonneg C2; linarith
  have hDeg := GlobalTheory.T.degenerateCollision_rowBound_at_sizeData CT cH cV Ca C2 Ch c C hc1 hcT' hcH hcV hCh hCc hC4 hC2 hCa D large₂ u T Z C' Cl Cg cb Cu cT C0
    h6' hHyp hc3' hCnt'.2 hVol hAmpAt hSm hTA.2.2.2.1 hTA.2.2.2.2.1 hTA.2.2.2.2.2.1
  have hND := GlobalTheory.T.nondegenerateCollision_rowBound_at_parameters CT cH cV Ca C2 Ch c C hc1 hcH hcV hCh hCc hC4 D large₂ u T Z C' Cl Cg cb Cu cT C0
    hC2' hHyp hc3' hCnt'.2 hVol hAmpAt hSm hTA.2.2.2.1 hTA.2.2.2.2.1 hTA.2.2.2.2.2.1
  exact hsum D large₂ X Y hF hI u T Z C' Cl Cg cb Cu cT C0 h5' h5l hH0 hConc hAbs hTA (hSm.2.2.2.2 hH0 u) hND hDeg

end GlobalTheory.Core.Deg
