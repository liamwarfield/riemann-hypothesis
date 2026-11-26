module

public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BeBessel
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.QuadAOf
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup

@[expose] public section

section -- merged from CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.QuadBOf
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

namespace G

set_option maxHeartbeats 800000 in
theorem quadB_of (hNI : NormInv) (hGS : GrowthS) (hGG : GrowthG) (hDD : CompanionTheory.D.Upq.BesselFunctionalConstruction.DecDD) (hIn : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs) {k r : ℕ}
    {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    {u : Fin k → ℝ} {νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hS1 : Side k r ε lam h σ w0 D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq)
    {l : H → Wp}
    (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN x y = (innerSL ℂ (l y)).smulRight (l x)) :
    ∫⁻ zz, ∫⁻ zz', ∫⁻ s,
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW D.μN) ∂νq ∂νq < ⊤ := by
  have hS1' := hS1
  obtain ⟨hl, hds, -, hG, hw0, hz1, hT, -, hπ, hW, hN, hGm, hq⟩ := hS1'
  have : SigmaFinite D.μW := hW.1
  have : SigmaFinite D.μN := hN.1
  have : SigmaFinite D.μG := hGm.1
  have hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hGm.2.2.1
  have hw0DD := cmHalfIntegralGenerator_mem_algebraicClosure hds w0
  have hf1 := DDSmoothness.muSof_facts hW hN
  have hae1 := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hf1.1 hf1.2 hq
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  swap
  · push Not at hA
    calc _ ≤ ∫⁻ zz, (0 : ℝ≥0∞) ∂νq := by
          apply lintegral_mono_ae
          filter_upwards [hae1] with zz hzz
          simp [hA _ (dd_stable hds hzz w0 hw0DD)]
      _ < ⊤ := by simp
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨e0, he0, hee0⟩ := coef_ext hds w0 w0
  obtain ⟨e1, he1, hee1⟩ := coef_ext hds v w0
  obtain ⟨C0, hC0⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD
    w0 hw0DD
  obtain ⟨C1, hC1⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv
  have hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee0 y hy]; exact hC0 y hy
  have hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee1 y hy]; exact hC1 y hy
  have h4 := gap4 hG
  have hAG := ag_nonneg k r
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  obtain ⟨ee, heedef⟩ : ∃ ee : ℝ, ee = AG k r + 1 := ⟨_, rfl⟩
  have hee0' : 0 ≤ ee := by rw [heedef]; linarith
  have heea : ee ≤ aOf r h := by rw [heedef]; linarith
  have hLs : ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-ee)‖ₑ ∂(D.μW.prod D.μN) < ⊤ :=
    (hGS k r D.z D.μW D.μN D.μG νq ee hz1 hT hW hN hGm hq (by rw [heedef]; linarith)).hasFiniteIntegral
  obtain ⟨Ls, hLsdef⟩ : ∃ Ls : ℝ≥0∞, Ls = ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-ee)‖ₑ ∂(D.μW.prod D.μN) :=
    ⟨_, rfl⟩
  rw [← hLsdef] at hLs
  have hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ ∂D.μG < ⊤ :=
    (hGG k r D.μG _ hGm (by rw [heedef]; linarith)).hasFiniteIntegral
  have hpUH : ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    (prod_ae hW hN).mono fun p hp => DDSmoothness.uh_mul hp.1.1 hp.2.1
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ≥0∞, K1 = ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ := ⟨_, rfl⟩
  have hK : K1 * K1 ≠ ⊤ := by rw [hK1]; simp [ENNReal.mul_eq_top]
  have hA1m := Aext_meas he1
  have hI1m := Iint_meas hA1m (D.μW.prod D.μN)
  obtain ⟨LL, hLL⟩ : ∃ LL : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, LL = Lam1 e0 (D.μW.prod D.μN) := ⟨_, rfl⟩
  have hLLm : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => LL t.1 t.2) := by
    rw [hLL]; exact measurable_lambda_integral he0 (D.μW.prod D.μN)
  have step1 : ∀ᵐ zz ∂νq, ∀ᵐ zz' ∂νq, ∫⁻ s,
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW D.μN) ≤
      (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) := by
    filter_upwards [hae1] with zz hzz
    filter_upwards [hae1] with zz' hzz'
    have bl : ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz := by
      rw [hK1]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz
    have bl' : ‖l (σ (Matrix.of zz') w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz' := by
      rw [hK1]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz'
    have hc : ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ ≠ ⊤ :=
      ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
    have hqi := quad_inner1 hds w0 he0 hee0 hf1.2 hzz hzz'
    rw [← hLL] at hqi
    simp only [← enorm_eq_nnnorm]
    calc ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ ∂(muSof D.μW D.μN)
        = ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) ∂(muSof D.μW D.μN) :=
          lintegral_congr fun s => mul_assoc _ _ _
      _ = (∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof D.μW D.μN)) *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) := lintegral_mul_const' _ _ hc
      _ = LL zz zz' * (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) := by rw [hqi]
      _ ≤ LL zz zz' * ((K1 * Iint (Aext e1) (D.μW.prod D.μN) zz) * (K1 * Iint (Aext e1) (D.μW.prod D.μN) zz')) := by
          gcongr
      _ = (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) := by
          ring
  have hinvR : ∀ zz, ∀ᵐ z ∂νq, ∀ᵐ q ∂(D.μW.prod D.μN),
      LL zz (fun i j => (Matrix.of q.1 * Matrix.of q.2 * Matrix.of z) i j) = LL zz z := by
    intro zz
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (ae_mem_UWset_and_mem_Nset D).mono
      fun q hq0 => lambda_right_translation he0 D.haarW D.haarN hz1 hT hq0.1 hq0.2 zz z
  have hinvL : ∀ᵐ z ∂νq, ∀ᵐ p ∂(D.μW.prod D.μN),
      (∫⁻ y, Aext e1 y * LL (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) y ∂D.μG) =
        ∫⁻ y, Aext e1 y * LL z y ∂D.μG := by
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (prod_ae hW hN).mono
      fun p hp0 => lintegral_congr fun y => by rw [lambda_left_translation he0 hW hN hz1 hp0.1 hp0.2 z y]
  have hLz : ∀ zz, Measurable (fun y => LL zz y) := fun zz => hLLm.comp (measurable_const.prodMk measurable_id)
  have hΦm : Measurable (fun x => ∫⁻ y, Aext e1 y * LL x y ∂D.μG) :=
    ((hA1m.comp measurable_snd).mul hLLm).lintegral_prod_right'
  obtain ⟨Fx, hFx⟩ : ∃ Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Fx = fun x => ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ :=
    ⟨_, rfl⟩
  have hFxm : Measurable Fx := by
    rw [hFx]; exact (((gN_cont.comp mt_cont).measurable).pow_const _).enorm
  have hKg' : ∫⁻ x, Fx x ∂D.μG < ⊤ := by rw [hFx]; exact hKg
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ≥0∞, c = ENNReal.ofReal |C1| * ENNReal.ofReal |C1| * (ENNReal.ofReal |C0| * Ls) :=
    ⟨_, rfl⟩
  have hc : c ≠ ⊤ := by
    rw [hcdef]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLs.ne)
  have hgpos : ∀ x : Mx k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → 0 < B.gN x :=
    fun x hx => lt_of_lt_of_le one_pos ((hNI k r).2 x hx).2
  have hpt : ∀ᵐ x ∂D.μG, Aext e1 x * ∫⁻ y, Aext e1 y * LL x y ∂D.μG ≤ ∫⁻ y, c * (Fx x * Fx y) ∂D.μG := by
    filter_upwards [hGc] with x hx
    rw [← lintegral_const_mul' (Aext e1 x) _ (by unfold Aext; exact enorm_ne_top)]
    apply lintegral_mono_ae
    filter_upwards [hGc] with y hy
    have hL := lambda_integral_bound hNI hb0e hee0' heea hpUH hx hy
    rw [← hLL, ← hLsdef] at hL
    have hx0 := hgpos _ hx
    have hy0 := hgpos _ hy
    have w1 := e_weight (b := ee) hb1 hx hx0
    have w2 := e_weight (b := ee) hb1 hy hy0
    have split : ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ ee) =
        ENNReal.ofReal |C0| * (ENNReal.ofReal (B.gN (Matrix.of x) ^ ee) * ENNReal.ofReal (B.gN (Matrix.of y) ^ ee)) := by
      rw [Real.mul_rpow hx0.le hy0.le, ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _)]
    have hFxx : Fx x = ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ := by rw [hFx]
    have hFxy : Fx y = ‖B.gN (Matrix.of y) ^ (-(aOf r h - ee))‖ₑ := by rw [hFx]
    calc Aext e1 x * (Aext e1 y * LL x y)
        ≤ Aext e1 x * (Aext e1 y * (ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ ee) * Ls)) := by
          gcongr
      _ = (Aext e1 x * ENNReal.ofReal (B.gN (Matrix.of x) ^ ee)) *
            (Aext e1 y * ENNReal.ofReal (B.gN (Matrix.of y) ^ ee)) * (ENNReal.ofReal |C0| * Ls) := by
          rw [split]; ring
      _ ≤ (ENNReal.ofReal |C1| * Fx x) * (ENNReal.ofReal |C1| * Fx y) * (ENNReal.ofReal |C0| * Ls) := by
          rw [hFxx, hFxy]
          exact mul_le_mul' (mul_le_mul' w1 w2) le_rfl
      _ = c * (Fx x * Fx y) := by rw [hcdef]; ring
  calc _ ≤ ∫⁻ zz, ∫⁻ zz', (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz *
          (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) ∂νq ∂νq :=
        lintegral_mono_ae (step1.mono fun zz h => lintegral_mono_ae h)
    _ = (K1 * K1) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz *
          ∫⁻ zz', Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz' ∂νq ∂νq :=
        pull2 _ _ _ hK (fun zz => hI1m.mul (hLz zz))
    _ = (K1 * K1) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz * ∫⁻ y, Aext e1 y * LL zz y ∂D.μG ∂νq := by
        congr 1; apply lintegral_congr; intro zz; congr 1
        exact unfold_Iint hq hA1m (hLz zz) (hinvR zz)
    _ = (K1 * K1) * ∫⁻ x, Aext e1 x * ∫⁻ y, Aext e1 y * LL x y ∂D.μG ∂D.μG := by
        congr 1
        exact unfold_Iint hq hA1m hΦm hinvL
    _ ≤ (K1 * K1) * ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂D.μG ∂D.μG := by
        gcongr 1
        exact lintegral_mono_ae hpt
    _ = (K1 * K1) * (c * ((∫⁻ x, Fx x ∂D.μG) * ∫⁻ y, Fx y ∂D.μG)) := by rw [final2 Fx hFxm hc]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK)
          (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (ENNReal.mul_lt_top hKg' hKg'))

end G

end Formalism.FourierDecayAlt.P.S3dx4

end
end

section -- merged from CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BeConv
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P
open Formalism.QuantumDeterminants

namespace G

theorem bessel_integral_convergence_of_growth (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  obtain ⟨hHC, hσ, hgap, hOK, hw0, hz, hT, hc, hπ, hW, hN, hG, hQ⟩ := hS
  have hσ' : Formalism.MainNotions.S.IsDSHpk k r ε lam σ := hσ
  have hw0' : Formalism.MainNotions.S.IsLowUnitH k r ε lam σ w0 := hw0
  have : SigmaFinite μN := hN.1
  set a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h with ha_def
  have ha1 : 1 + Formalism.FourierDecayAlt.ThreeDimData.AG k r < a := one_add_AG_lt_aOf hOK
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have ha : 1 ≤ a := by linarith
  have hM := Formalism.MainNotions.MeasFS.measF_side hz hT hπ hW hN
  have hgr0 := hGS k r z μW μN μG νq (a - 1) hz hT hW hN hG hQ (by linarith)
  have hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a))
      (μW.prod μN) := by
    simpa only [neg_sub] using hgr0
  have hDI : PI.WBL.Cv.BeC.DecInf σ a := by
    intro v0 hv0
    obtain ⟨C, Ws, hWs, hb⟩ := hIn.2.1 k r ε lam h H σ hHC hσ hgap hOK v0 hv0
    refine ⟨C, Ws, hWs, fun w hw x hx => ?_⟩
    have e := hb w hw x hx
    simp only [dsigW_eq_bessel_integrability] at e
    exact e
  have hB := PI.WBL.Cv.BeC.beConv_of_low z c π μW μN σ a (PI.WBL.Cv.grpAll k r z)
    (PI.WBL.Cv.sigAll k r ε lam H σ hσ') (PI.WBL.Cv.piAll k r z u Wp π hz hT hπ) (PI.WBL.Cv.psiAll k r z c hz) hM
    (fun w => Formalism.MainNotions.LeviCoordinates.discrete_series_continuousOn hσ' w) ha hgr hDI hw0'

  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ :=
    hIn.2.2.1 k r ε lam H σ hHC hσ w0 (Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0')
  have hDDs : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    have hle : Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0 ≤ Formalism.MainNotions.DoubleDerivativeSmoothness.smoothSub σ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, hg, rfl⟩
      exact Formalism.MainNotions.LeviCoordinates.smooth_vectors_translate_unitary (fun _ ha _ hb => Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ' ha hb) hw0s hg
    intro v hv; exact hle hv
  have hAs : ∀ v, Formalism.FourierDecayAlt.ThreeDimData.IsAdm σ w0 v → v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    rintro v (hv | hv)
    · exact hDDs v hv
    · exact hIn.2.2.1 k r ε lam H σ hHC hσ v hv
  obtain ⟨h1, -, h3, -, h5, h6⟩ := hB
  refine ⟨fun x hx v hv => h1 x hx v hv, fun v hv g hg m hm x hx => ?_, fun x hx v hv => h6 x hx v hv,
    fun x hx v hv => ⟨h1 v (hAs v hv) x (Or.inl hx), h5 x (Or.inl hx) v (hAs v hv)⟩⟩
  have e := h3 g hg m hm x hx v hv
  rw [ContinuousLinearMap.smul_comp] at e
  exact e

end G

end Formalism.FourierDecayAlt.P

end
end

section -- merged from CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.NormId
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS
open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW Formalism.MainNotions.InverseNormDecayBounds Formalism.MainNotions.BridgeLemma₄
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

namespace G

theorem normIdSm_of (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) (hGG : Formalism.FourierDecayAlt.ThreeDimData.GrowthG) (hMS : MeasSideP) :
    CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm := by
  intro hIn hSch k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hSide x hx v hv ξ
  obtain ⟨hDL, hDI, hKS, -⟩ := hIn
  obtain ⟨hlam, hds, hgap, hOK, hw0, hz, hT, hc, hπ, hμW, hμN, hμG, hq⟩ := hSide
  have : SigmaFinite μW := hμW.1
  have : SigmaFinite μN := hμN.1
  have hds' : IsDSHpk k r ε lam σ := hds
  have hHaar : IsHaarOn (UH (Hpk k r)) μG := hμG
  have hq' : IsQuotMeas μG (muSof μW μN) νq := hq
  have hGr := Cv.grpAll k r z
  have hSg := Cv.sigAll k r ε lam H σ hds'
  have hPi := Cv.piAll k r z u Wp π hz hT hπ
  have hPs := Cv.psiAll k r z c hz
  have hM := hMS k r z u Wp π μW μN hz hT hπ hμW hμN
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hds hμG
  have hS : SchurOn μG σ := ⟨d, hd, hSd⟩
  set a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h with ha_def
  obtain ⟨ha1, hAG, hAS⟩ := thresholds hOK.2.2.1
  have hb : 0 ≤ a - 1 := by linarith
  have hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-((a - 1) / 2))) μG :=
    hGG k r μG _ hμG hAG
  have hSS : Integrable (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-((a - 1) / 2))) (μW.prod μN) :=
    hGS k r z μW μN μG νq _ hz hT hμW hμN hμG hq hAG
  obtain ⟨P, hP, hn1, hmem⟩ := hw0
  have hw0' : IsLowUnitH k r ε lam σ w0 := ⟨P, hP, hn1, hmem⟩
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn1
    exact zero_ne_one hn1
  have hK0 : IsKFinHpk (k := k) (r := r) σ w0 := Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0'
  have hsm0 : w0 ∈ smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hlam hds w0 hK0
  have hD : DiagonalMatrixCoefficientPowerDecay σ w0 a := hDL k r hOK.1 ε lam h H σ hlam hds hgap hOK.2.1 P hP w0 w0 hmem hmem
  have hI : DecInfU σ a := hDI k r ε lam h H σ hlam hds hgap hOK

  have hB : (∀ y ∈ smoothVecs (k := k) (r := r) σ, DecBd σ (a - 1) v y) ∧ DecBd σ (a - 1) v v := by
    rcases hv with hvD | hvK
    · exact ⟨fun y hy => decBd_DD_left hds' hSg hb (decBd_of_decInfU hI hK0 hy) v hvD,
        decBd_mono (by linarith) (decDD hds' (by linarith) hD v hvD v hvD)⟩
    · have hvs : v ∈ smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hlam hds v hvK
      exact ⟨fun y hy => decBd_of_decInfU hI hvK hy, decBd_of_decInfU hI hvK hvs⟩
  have hfd : ∀ y : H, y ≠ 0 → fdegH μG σ y = d := fun y hy => fdegH_eq ⟨hd, hSd⟩ hy

  obtain ⟨-, heq0, him⟩ := normId_gen_bd hds' hHaar hq' hGr hSg hPi hPs hM hS hw0ne hb (hB.1 w0 hsm0) hB.2
    hGg hSS ξ
  have hre : 0 ≤ (⟪ξ, PI.WBL.be z c π μW μN σ v v ξ⟫_ℂ).re := by
    have h0 : 0 ≤ ∫ y, ‖PI.WBL.be z c π μW μN σ (σ (Matrix.of y) w0) v ξ‖ ^ 2 ∂νq :=
      integral_nonneg fun _ => by positivity
    rw [heq0, hfd w0 hw0ne, hn1, re_inner_swap] at h0
    have : 0 ≤ (⟪ξ, PI.WBL.be z c π μW μN σ v v ξ⟫_ℂ).re / d := by simpa using h0
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hd))
  refine ⟨?_, him, hre⟩
  have hfd0 : PI.BesselPeriodGGP.fdegH μG σ w0 = d := hfd w0 hw0ne
  rw [hfd0]
  by_cases hx0 : x = 0
  · subst hx0
    have e0 : Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN 0 v = 0 := by
      simp [Formalism.FourierDecayAlt.ThreeDimData.be, Formalism.FourierDecayAlt.ThreeDimData.beInt]
    unfold PI.BesselPeriodGGP.l2SG
    simp [e0]
  · obtain ⟨hint, heq, -⟩ := normId_gen_bd hds' hHaar hq' hGr hSg hPi hPs hM hS hx0 hb (hB.1 x hx) hB.2
      hGg hSS ξ
    rw [hfd x hx0, re_inner_swap] at heq
    unfold PI.BesselPeriodGGP.l2SG
    show ∫⁻ y, (‖PI.WBL.be z c π μW μN σ (σ (Matrix.of y) x) v ξ‖₊ : ℝ≥0∞) ^ 2 ∂νq =
      ENNReal.ofReal (‖x‖ ^ 2 * (⟪ξ, PI.WBL.be z c π μW μN σ v v ξ⟫_ℂ).re / d)
    rw [← heq, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)]
    apply lintegral_congr
    intro y
    simp only [ENNReal.ofReal_pow, norm_nonneg, ofReal_norm, enorm_eq_nnnorm]

end G

end PI.WBL.NIS

end
end

section -- merged from CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.DoubleCosetDecomposition
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P
open Formalism.QuantumDeterminants

namespace G

theorem double_coset_decomposition : CompanionTheory.D.Upq.BesselFunctionalConstruction.DecDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS x hx y hy
  obtain ⟨hHC, hσ, hgap, hOK, hw0, -⟩ := hS
  have hσ' : Formalism.MainNotions.S.IsDSHpk k r ε lam σ := hσ
  obtain ⟨P, hP, hw⟩ := hw0
  obtain ⟨C, hC⟩ := hIn.1 k r hOK.1 ε lam h H σ hHC hσ hgap hOK.2.1 P hP w0 w0 hw.2 hw.2
  have hD : Formalism.MainNotions.InverseNormDecayBounds.DiagonalMatrixCoefficientPowerDecay σ w0 (Formalism.FourierDecayAlt.ThreeDimData.aOf r h) := ⟨C, fun g hg => hC g hg⟩
  have hh : 0 ≤ h := le_trans (by positivity) hOK.2.1
  have ha : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := div_nonneg hh (by positivity)
  exact Formalism.MainNotions.InverseNormDecayBounds.decDD hσ' ha hD x hx y hy

end G

end Formalism.FourierDecayAlt.P

end
end

section -- merged from CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingFromL2
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section
set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
open Formalism.FourierDecayAlt.ThreeDimData

namespace G

theorem bessel_nonvanishing_from_L2 : CompanionTheory.D.Upq.BesselFunctionalConstruction.BesselNonvanishingReduction := by
  classical
  intro hSch hNI hGS hGG hDD hBC hInp _ k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS W hWc hWeq
    hRe hpos hfin
  by_contra hcon
  push_neg at hcon
  obtain ⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩ := hS
  have hS' : Side k r ε lam h σ w0 z c u π μW μN μG νq :=
    ⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩
  have := hWh.1; have := hNh.1; have := hGh.1
  have hsm := DDSmoothness.DD_smooth hInp.2.2.1 hlam hσ hw0
  have memDD : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ DDsp σ w0 :=
    fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  obtain ⟨hS0, hSc⟩ := DDSmoothness.muSof_facts hWh hNh
  have hνae := DDSmoothness.ae_UH_of_quot hGh.2.2.1 hS0 hSc hq
  have hBC' := hBC hInp k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS'
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w0

  have hW0 : ∀ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x0 = 0 := by
    intro x0 hx0
    obtain ⟨hI, hR⟩ := hRe x0 hx0
    rw [← hR]
    unfold PI.BesselPeriodGGP.rconv
    apply ext_inner_left ℂ
    intro η
    rw [inner_zero_right, ← integral_inner hI η]
    obtain ⟨hxi, hxx, hxx'⟩ := uh_inv hx0
    set U : Set (Formalism.QuantumDeterminants.Mt k r) := {g | Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU
    have hUm : MeasurableSet U := (isClosed_UH.preimage hof).measurableSet
    let Φ : Formalism.QuantumDeterminants.Mt k r → ℂ := fun g =>
      ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g) • W (Matrix.of g)⟫_ℂ
    let Φ' : Formalism.QuantumDeterminants.Mt k r → ℂ := U.piecewise Φ (fun _ => 0)
    have hΦc : ContinuousOn Φ U := by
      have hm : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U :=
        (continuous_const.matrix_mul hof).continuousOn
      have hmaps : Set.MapsTo (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U
          (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := fun g hg => DDSmoothness.uh_mul hxi hg
      have he : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r =>
          PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g)) U := by
        unfold PI.BesselPeriodGGP.eFun
        exact continuousOn_const.mul (continuous_star.comp_continuousOn
          (continuousOn_const.inner (hcs.comp hm hmaps)))
      have hWc' : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of g)) U :=
        hWc.comp hof.continuousOn (fun g hg => hg)
      exact continuousOn_const.inner (he.smul hWc')
    have hΦm : Measurable Φ' := hΦc.measurable_piecewise continuousOn_const hUm
    have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x0) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x0) := continuous_const.matrix_mul hof
      exact this.measurable
    have htrans : (fun g : Formalism.QuantumDeterminants.Mt k r =>
        ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) =ᵐ[μG]
        Φ' ∘ Formalism.QuantumDeterminants.lmulM x0 := by
      filter_upwards [hGae] with g hg
      have hxg : x0 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hx0 hg
      have hmem : Formalism.QuantumDeterminants.lmulM x0 g ∈ U := hxg
      simp only [Function.comp, Φ', Set.piecewise, hmem, if_true, Φ]
      show _ = ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (x0 * Matrix.of g)) • W (x0 * Matrix.of g)⟫_ℂ
      rw [← Matrix.mul_assoc, hxx', Matrix.one_mul]
    have hmapEq : μG.map (Formalism.QuantumDeterminants.lmulM x0) = μG := hGh.2.2.2 x0 hx0
    have hΦint : Integrable Φ' μG := by
      have h1 : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
          ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) μG :=
        (innerSL ℂ η).integrable_comp hI
      have h2 : Integrable (Φ' ∘ Formalism.QuantumDeterminants.lmulM x0) μG := h1.congr htrans
      rw [← integrable_map_measure hΦm.aestronglyMeasurable hlm.aemeasurable, hmapEq] at h2
      exact h2
    rw [integral_congr_ae htrans]
    show ∫ a, Φ' (Formalism.QuantumDeterminants.lmulM x0 a) ∂μG = 0
    rw [← integral_map hlm.aemeasurable hΦm.aestronglyMeasurable, hmapEq]
    have : SFinite (muSof μW μN) := by unfold muSof; infer_instance
    refine quot_zero hq Φ' hΦm hΦint ?_
    filter_upwards [hνae] with x hx
    have hpm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
      have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
      have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
      have h3 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
          (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := h1.matrix_mul h2
      exact h3.measurable
    have hFm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => Φ' (mulMt s x)) :=
      hΦm.comp (measurable_mulMt.comp (measurable_id.prodMk measurable_const))
    unfold muSof
    rw [integral_map hpm.aemeasurable hFm.aestronglyMeasurable]
    set u' := σ (Matrix.of x) w0 with hu'
    set v' := σ x0 w0 with hv'
    have hu'DD : u' ∈ DDsp σ w0 := memDD _ hx
    have hv'DD : v' ∈ DDsp σ w0 := memDD _ hx0
    have hI2 : Integrable (beInt z c π σ u' v') (μW.prod μN) := hBC'.1 u' (hsm _ hu'DD) v' (Or.inl hv'DD)
    have hval : ∀ᵐ p ∂(μW.prod μN), Φ' (mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) =
        ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℝ) : ℂ) * ⟪beInt z c π σ u' v' p η, W (Matrix.of x)⟫_ℂ := by
      filter_upwards [hPae] with p hp
      have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
      have hsx : Matrix.of p.1 * Matrix.of p.2 * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
        DDSmoothness.uh_mul hs hx
      have hmem : mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x ∈ U := hsx
      simp only [Φ', Set.piecewise, hmem, if_true, Φ]
      show ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) •
          W (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)⟫_ℂ = _
      rw [hWeq _ hp.1 _ hp.2 _ hx]
      have hdet : IsUnit x0.det := Matrix.isUnit_det_of_right_inverse hxx
      have eσ : σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0 =
          σ x0⁻¹ (σ (Matrix.of p.1 * Matrix.of p.2) u') := by
        rw [Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hxi hsx, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hs hx]; rfl
      have eA : ⟪w0, σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0⟫_ℂ =
          ⟪v', σ (Matrix.of p.1 * Matrix.of p.2) u'⟫_ℂ := by
        rw [eσ, sigma_inner hσ hxi, Matrix.nonsing_inv_nonsing_inv x0 hdet]
      unfold PI.BesselPeriodGGP.eFun beInt
      rw [eA, inner_smul_right, inner_smul_right, piW_inner hT hπ hp.1, ContinuousLinearMap.smul_apply,
        inner_smul_left]
      simp only [map_mul, Complex.star_def, Complex.conj_conj]
      ring
    rw [integral_congr_ae hval, integral_const_mul]
    have hf : Integrable (fun p => beInt z c π σ u' v' p η) (μW.prod μN) :=
      (ContinuousLinearMap.apply ℂ Wp η).integrable_comp hI2
    have hinner : ∫ p, ⟪beInt z c π σ u' v' p η, W (Matrix.of x)⟫_ℂ ∂(μW.prod μN) =
        ⟪be z c π σ μW μN u' v' η, W (Matrix.of x)⟫_ℂ := by
      have e2 : be z c π σ μW μN u' v' η = ∫ p, beInt z c π σ u' v' p η ∂(μW.prod μN) :=
        ContinuousLinearMap.integral_apply hI2 η
      rw [e2, ← inner_conj_symm, ← integral_inner hf (W (Matrix.of x)), ← integral_conj]
      congr 1
      funext p
      rw [inner_conj_symm]
    rw [hinner, hcon u' hu'DD v' hv'DD]
    simp

  have hl0 : PI.BesselPeriodGGP.l2SG νq W = 0 := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hνae] with x hx
    rw [hW0 _ hx]; simp
  rw [hl0] at hpos
  exact lt_irrefl _ hpos

end G

end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

end
end

section -- merged from CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.VanishingOfL2Equivariant
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section
set_option maxHeartbeats 3200000

namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData

namespace G

theorem vanishing_of_L2_equivariant {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hIn : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs)
    (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq)
    {x : H} (hx : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) {v : H} (hv : IsAdm σ w0 v)
    (hl : ∀ ξ : Wp, PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v ξ) = 0) :
    be z c π σ μW μN x v = 0 := by
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, hBC2, hBC3, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  let K := Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
  let F : Mx k r → Wp := fun g => be z c π σ μW μN (σ g x) v ξ
  have hc : ContinuousOn F K :=
    (hBC3 x hx v hv).clm_apply continuousOn_const
  have heq : ∀ hh ∈ Formalism.QuantumDeterminants.UWset k r z,
      ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ K,
        F (hh * n * g) = Formalism.QuantumDeterminants.psi k r z c n • π hh (F g) := by
    intro hh hhW n hn g hg
    have hhn : hh * n ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhW.1 hn.1
    have hm : σ (hh * n * g) = (σ (hh * n)).comp (σ g) := TranslationBesselVanishing.sigma_mul hσ hhn hg
    dsimp only [F]
    rw [hm, ContinuousLinearMap.comp_apply,
      hBC2 v hv hh hhW n hn (σ g x) (TranslationBesselVanishing.smooth_translate hσ hx hg)]
    rfl
  classical
  let S : Set (Formalism.QuantumDeterminants.Mt k r) := {g | Matrix.of g ∈ K}
  let G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    S.indicator fun g => (‖F (Matrix.of g)‖₊ : ℝ≥0∞) ^ 2
  have hSm : MeasurableSet S := uh_meas
  have hGc : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r =>
      (‖F (Matrix.of g)‖₊ : ℝ≥0∞) ^ 2) S :=
    (ENNReal.continuous_pow 2).comp_continuousOn
      ((ENNReal.continuous_coe.comp continuous_nnNorm).comp_continuousOn hc)
  have hGm : Measurable G := hGc.measurable_piecewise continuousOn_const hSm
  have hGzero {g : Formalism.QuantumDeterminants.Mt k r} (hg : g ∈ S) :
      G g = 0 ↔ F (Matrix.of g) = 0 := by
    simp [G, Set.indicator_of_mem hg]
  have hνint : ∫⁻ g, G g ∂νq = 0 := by
    apply nonpos_iff_eq_zero.mp
    calc
      ∫⁻ g, G g ∂νq ≤ PI.BesselPeriodGGP.l2SG νq F :=
        lintegral_mono (Set.indicator_le_self S _)
      _ = 0 := hl ξ
  have hmu := DDSmoothness.muSof_facts hW hN
  have hνS : ∀ᵐ g ∂νq, g ∈ S := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have := hW.1
  have := hN.1
  have hWae :
      ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hW.2.2.1)
  have hNae :
      ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 hN.2.2.1)
  have hμint : ∫⁻ g, G g ∂μG = 0 := by
    rw [hq G hGm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hνS, (lintegral_eq_zero_iff hGm).mp hνint] with g hg hg0
    let mulPair (p : Formalism.QuantumDeterminants.Mt k r ×
        Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r :=
      fun i j => (Matrix.of p.1 * Matrix.of p.2) i j
    let mulRight (s : Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r :=
      fun i j => (Matrix.of s * Matrix.of g) i j
    have hmul : Continuous mulPair := continuous_fst.matrix_mul continuous_snd
    have hright : Continuous mulRight := continuous_id.matrix_mul continuous_const
    change (∫⁻ s, (G ∘ mulRight) s ∂Measure.map mulPair (μW.prod μN)) = 0
    rw [lintegral_map (hGm.comp hright.measurable) hmul.measurable]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hWae, hNae] with p hpW hpN
    apply (hGzero (DDSmoothness.uh_mul (DDSmoothness.uh_mul hpW.1 hpN.1) hg)).mpr
    change F (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) = 0
    rw [heq (Matrix.of p.1) hpW (Matrix.of p.2) hpN (Matrix.of g) hg,
      (hGzero hg).mp hg0, map_zero, smul_zero]
  have hμS : ∀ᵐ g ∂μG, g ∈ S := ae_iff.2 hG.2.2.1
  have hμF : ∀ᵐ g ∂μG, F (Matrix.of g) = 0 := by
    filter_upwards [hμS, (lintegral_eq_zero_iff hGm).mp hμint] with g hg hg0
    exact (hGzero hg).mp hg0
  have hF1 : F 1 = 0 := by
    by_contra hne
    obtain ⟨V, hVo, hV⟩ := (continuousOn_iff'.mp hc) {0}ᶜ isOpen_compl_singleton
    have h1V : (1 : Mx k r) ∈ V := by
      have h1 : (1 : Mx k r) ∈ F ⁻¹' {0}ᶜ ∩ K :=
        ⟨hne, Formalism.QuantumDeterminants.WeylGroupFacts.uh_one⟩
      rw [hV] at h1
      exact h1.1
    have hVae : ∀ᵐ g : Formalism.QuantumDeterminants.Mt k r ∂μG, Matrix.of g ∉ V := by
      filter_upwards [hμS, hμF] with g hg hg0 hgV
      have hg' : Matrix.of g ∈ V ∩ K := ⟨hgV, hg⟩
      rw [← hV] at hg'
      exact hg'.1 hg0
    have hVnull : μG (Matrix.of ⁻¹' V) = 0 := by
      change μG {g | Matrix.of g ∈ V} = 0
      simpa only [not_not] using ae_iff.mp hVae
    let O (g : K) : Set (Formalism.QuantumDeterminants.Mt k r) :=
      Formalism.QuantumDeterminants.lmulM (g : Mx k r)⁻¹ ⁻¹' (Matrix.of ⁻¹' V)
    have hlmul (a : Mx k r) : Continuous (Formalism.QuantumDeterminants.lmulM a) :=
      continuous_const.matrix_mul continuous_id
    have hVo' : IsOpen (Matrix.of ⁻¹' V : Set (Formalism.QuantumDeterminants.Mt k r)) :=
      hVo.preimage continuous_id
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable O
      (fun g => hVo'.preimage (hlmul (g : Mx k r)⁻¹))
    have hOnull (g : K) : μG (O g) = 0 := by
      dsimp only [O]
      rw [← Measure.map_apply (hlmul (g : Mx k r)⁻¹).measurable hVo'.measurableSet,
        hG.2.2.2 _ (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv g.2), hVnull]
    have hSnull : μG S = 0 := by
      refine measure_mono_null (t := ⋃ g ∈ T, O g) ?_
        ((measure_biUnion_null_iff hTc).mpr fun g _ => hOnull g)
      intro g hg
      rw [hT]
      refine Set.mem_iUnion.mpr ⟨⟨Matrix.of g, hg⟩, ?_⟩
      change (Matrix.of g)⁻¹ * Matrix.of g ∈ V
      rw [Matrix.nonsing_inv_mul (Matrix.of g)
        (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg)]
      exact h1V
    apply hG.2.1
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self S]
    exact measure_union_null hSnull hG.2.2.1
  have hσ1 : σ 1 = 1 := by
    obtain ⟨P, hP, hD⟩ := hσ
    have hPu := Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hP.2)
    simpa [Matrix.nonsing_inv_mul P hPu] using hD.2.2.1.1.1
  simpa [F, hσ1] using hF1

theorem zeroCaseDD_of (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hNI : CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm) (hSch : SchurH) : CompanionTheory.D.Upq.BesselFunctionalConstruction.ZeroCaseDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inl hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inl hv) ξ).1, hDD v hv v hv]
  simp

theorem zeroCase_of (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hNI : CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm) (hSch : SchurH) : CompanionTheory.D.Upq.BesselFunctionalConstruction.ZeroCase := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  have hA := zeroCaseDD_of hBC hNI hSch hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hDD
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hIn.2.2.1 k r ε lam H σ hlam hσ v hv

  have hB : ∀ u ∈ DDsp σ w0, be z c π σ μW μN u v = 0 := by
    intro u hu
    have h1 : be z c π σ μW μN v u = 0 := hA u hu v hvs
    have h2 := (hBC4 u hu v (Or.inr hv)).2
    rw [h1] at h2
    have h3 := congrArg ContinuousLinearMap.adjoint h2
    rwa [ContinuousLinearMap.adjoint_adjoint, map_zero] at h3

  have hw0n : ‖w0‖ = 1 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    exact hn1
  have hw0ne : w0 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw0n; exact zero_ne_one hw0n
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hdeg : PI.BesselPeriodGGP.fdegH μG σ w0 = d := DDSmoothness.fdeg_eq hd hSd hw0ne
  have hw0DD : w0 ∈ DDsp σ w0 := by
    refine Submodule.subset_span ⟨1, Formalism.QuantumDeterminants.WeylGroupFacts.uh_one, ?_⟩
    have hσ1 : σ 1 = 1 := by
      obtain ⟨P, hP, hD⟩ := hσ
      have hPu := Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hP.2)
      simpa [Matrix.nonsing_inv_mul P hPu] using hD.2.2.1.1.1
    simp [hσ1]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 w0 hw0DD
  have hmu := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hC : ∀ ξ : Wp, ⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ = 0 := by
    intro ξ
    obtain ⟨hNv, him, hre⟩ := hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS w0 hw0s v (Or.inr hv) ξ
    have hL : PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g w0) v ξ) = 0 := by
      unfold PI.BesselPeriodGGP.l2SG
      refine (lintegral_congr_ae (hae.mono fun g hg => ?_)).trans lintegral_zero
      have hgD : σ (Matrix.of g) w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨Matrix.of g, hg, rfl⟩
      simp [hB _ hgD]
    rw [hL, hdeg, hw0n] at hNv
    have h0 : 1 ^ 2 * (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re / d ≤ 0 := ENNReal.ofReal_eq_zero.mp hNv.symm
    have hre0 : (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re = 0 := by
      have : (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re ≤ 0 := by
        rw [one_pow, one_mul] at h0
        exact (div_nonpos_iff.mp h0).elim (fun h => absurd h.2 (not_le.mpr hd)) (fun h => h.1)
      linarith
    exact Complex.ext hre0 him
  have hvv : be z c π σ μW μN v v = 0 := by
    have hlin : (be z c π σ μW μN v v : Wp →ₗ[ℂ] Wp) = 0 := by
      rw [← inner_map_self_eq_zero]
      intro ξ
      rw [← inner_conj_symm]
      simp [hC ξ]
    ext ξ
    have := LinearMap.congr_fun hlin ξ
    simpa using this

  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inr hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inr hv) ξ).1, hvv]
  simp

end G

end UnipotentHaarMeasurability

end Formalism.FourierDecayAlt.P

end
end

section -- merged from CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.KFinFormOf
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness

theorem bessel_add {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ}
    {σ : Mx k r → (H →L[ℂ] H)} {π : Mx k r → (Wp →L[ℂ] Wp)} {B B' : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B)
    (hB' : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B') :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun x => B x + B' x) := by
  obtain ⟨a1, a2, a3, C, Ws, hWs, hC⟩ := hB
  obtain ⟨b1, b2, b3, C', Ws', hWs', hC'⟩ := hB'
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun g hg m hm v hv => ?_, |C| + |C'|, Ws ++ Ws',
    fun W hW => (List.mem_append.1 hW).elim (hWs W) (hWs' W), fun v hv => ?_⟩
  · simp only [a1 v hv w hw, b1 v hv w hw]; abel
  · simp only [a2 c v hv, b2 c v hv, smul_add]
  · simp only [a3 g hg m hm v hv, b3 g hg m hm v hv, map_add (f := _), smul_add]
  · have hnn : ∀ L : List (List (Mx k r)),
        0 ≤ (L.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W v‖).sum := fun L =>
      List.sum_nonneg fun t ht => by
        obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht
        exact norm_nonneg _
    rw [List.map_append, List.sum_append]
    have h1 := (hC v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hnn Ws))
    have h2 := (hC' v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (hnn Ws'))
    have h3 := mul_nonneg (abs_nonneg C) (hnn Ws')
    have h4 := mul_nonneg (abs_nonneg C') (hnn Ws)
    refine (norm_add_le _ _).trans ?_
    nlinarith

theorem kFinForm_of (hBC : BeConv) (hBB : BeBessel) : KFinForm := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hl _ hid v hv x hx
  have hK := hIn.2.2.1
  have hvs := hK k r ε lam H σ hS.1 hS.2.1 v hv
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  have hB := bessel_add
    (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inr hv) ξ)
    (bessel_smul hl (-⟪l v, ξ⟫_ℂ))
  have h0 := bessel_ne_zero_of_cyclic_orbit (Sm.smoothCyc_of_kFinSmooth hK) hK k r ε lam H σ w0 Wp z c π hS.1
    hS.2.1 hS.2.2.2.2.1 _ hB (fun y hy => by
      have hadj := (hBC4 y hy v (Or.inr hv)).2
      refine ext_inner_left ℂ fun η => ?_
      have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN y v) ξ η
      rw [hadj, hid v hvs y hy] at e
      simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left,
        inner_conj_symm] at e
      rw [inner_add_right, ← e, inner_smul_right, inner_zero_right]
      ring) x hx
  rw [neg_smul, add_neg_eq_zero] at h0
  rw [h0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

end CompanionTheory.D.Upq.BesselFunctionalConstruction

end
end

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt.P

theorem decDD : DecDD := G.double_coset_decomposition
theorem beConv : BeConv := G.bessel_integral_convergence_of_growth growth_spherical_bound
theorem beBessel : BeBessel := PI.WBL.S5.G.beBessel_of growth_spherical_bound
theorem normIdSm : NormIdSm :=
  PI.WBL.NIS.G.normIdSm_of growth_spherical_bound growth_group_bound PI.WBL.NIS.measSideP
theorem kFinForm : KFinForm := kFinForm_of beConv beBessel
theorem zeroCase : ZeroCase := UnipotentHaarMeasurability.G.zeroCase_of beConv normIdSm schur_hermitian
theorem zeroCaseDD : ZeroCaseDD := UnipotentHaarMeasurability.G.zeroCaseDD_of beConv normIdSm schur_hermitian
theorem ooConv : OOConv :=
  S3dx4.G.ooConv_of schur_hermitian normIdSm norm_inverse_bound growth_group_bound decDD beConv
theorem quadConv : QuadConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe'
  exact ⟨fun γ hγ => S3dx4.G.quadA_of schur_hermitian normIdSm norm_inverse_bound growth_group_bound
      decDD beConv hIn D hS1 hS2 hbe hbe' hγ,
    S3dx4.G.quadB_of norm_inverse_bound growth_spherical_bound growth_group_bound decDD hIn D hS1 hbe⟩
theorem bessel_nonvanishing_L2 : BesselNonvanishingL2 :=
  MatrixMultiplicationContinuity.G.bessel_nonvanishing_from_L2 schur_hermitian norm_inverse_bound growth_spherical_bound
    growth_group_bound decDD beConv

end CompanionTheory.D.Upq.BesselFunctionalConstruction
