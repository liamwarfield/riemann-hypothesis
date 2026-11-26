module

public import Formalism.LocalToGlobal.GlobalTheory.FamCol
public import Formalism.GL3MeanSquares.HookFormulaTorsion.PsiZeroIntegral
public import Formalism.GL3MeanSquares.HookFormulaTorsion.CharacterEstimateOfHypothesis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContour
public import Formalism.LocalToGlobal.GlobalTheory.GL2.Statement
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZAll
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMain
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTFinal
public import Formalism.PadicSubsetSums.CentralIdempotents.StretchedExponentialDominance
public import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
public import Formalism.SharpRestriction.GlobalSchurBounds.LossesSmallShares

@[expose] public section

section -- merged from Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied
namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses

open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

theorem discriminant_windows_iff : WindowsDIff := by
  intro P e K
  constructor
  · rintro ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, Co0, CoK, Y1, YX, bo0, bosb⟩
    have h0 : (0 : ℝ) ≤ (P.x ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have hβ : (0 : ℝ) ≤ K * (P.x ^ 2)⁻¹ := mul_nonneg (by linarith) h0
    exact ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, le_refl (0 : ℝ), hβ, Co0, CoK, Y1, YX, le_refl (0 : ℝ), h0, bo0, bosb⟩
  · rintro ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, -, -, Co0, CoK, Y1, YX, -, -, bo0, bosb⟩
    exact ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, Co0, CoK, Y1, YX, bo0, bosb⟩

theorem discriminant_windows_of : WindowsDOf := by
  rintro P e K ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
    ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, -, -, Co0, CoK, Y1, YX, -, -, bo0, bosb⟩
  exact ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
    ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, Co0, CoK, Y1, YX, bo0, bosb⟩

lemma logdiv_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) / (p : ℝ) :=
  div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem out_discriminant_bound : OutD := by
  intro τ Ps PR cl TT TTp BAD m a R hm ha hT2 hBad
  have hco : ∀ p : ℕ, 0 ≤ 4 * m * a * (Real.log p / p) := fun p => by
    have := logdiv_nonneg p
    positivity
  have h1 : ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
      4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) ≤
      ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        (if p ∈ PR then 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ)
          else 0) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    have hb := hBad p hp.1 hp.2
    by_cases hps : p ∈ PR
    · rw [if_pos hps]
      refine mul_le_mul_of_nonneg_left ?_ (hco p)
      have hsub : TT \ TTp p ⊆ TT.filter fun t => BAD p t := by
        intro t ht
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_sdiff.1 ht).1, (hb t ht).2⟩
      exact_mod_cast Finset.card_le_card hsub
    · rw [if_neg hps]
      have hemp : TT \ TTp p = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        exact hps (hb t ht).1
      rw [hemp]; simp
  have h2 : ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        (if p ∈ PR then 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ)
          else 0) ≤
      ∑ p ∈ PR, 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => mul_nonneg (hco p) (Nat.cast_nonneg _))
    intro p hp
    exact (Finset.mem_filter.1 hp).2
  have h3 : ∑ p ∈ PR, 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) =
      4 * a * m * badPrimeLogWeightedCount PR TT BAD := by
    unfold badPrimeLogWeightedCount
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have h4 : 4 * a * m * badPrimeLogWeightedCount PR TT BAD ≤ 4 * a * m * R :=
    mul_le_mul_of_nonneg_left hT2 (by positivity)
  linarith

theorem second_discriminant_bound : SecondD := by
  intro Ps cand cl Sig θ m T a R hm hT ha hSig hW hcl
  have h1 := second_term_le Ps cand cl Sig θ m T a hm hT ha hcl
  have hc : 0 ≤ 2 * a * m * T := by positivity
  have h2 : ∑ p ∈ cand, (if θ < Sig p then 4 * (m * T * a) * Real.log p / p else 0) ≤
      2 * a * m * T * lhsW cand θ Sig := by
    unfold lhsW
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hl := logdiv_nonneg p
    have hs := hSig p hp
    have h0 : 0 ≤ 2 * a * m * T * (Real.log p / p * (4 * Sig p)) := by positivity
    split_ifs
    · have e : 2 * a * m * T * (Real.log p / p * (2 + 4 * Sig p)) =
          4 * (m * T * a) * Real.log p / p + 2 * a * m * T * (Real.log p / p * (4 * Sig p)) := by ring
      rw [e]; linarith
    · rw [zero_add]; exact h0
  have h3 := mul_le_mul_of_nonneg_left hW hc
  linarith

theorem io_discriminant_bound : IoD := by
  intro cand Sig io θ m T a R hm hT ha hW hio
  have hc : 0 ≤ a * m * T := by positivity
  have h2 : ∑ p ∈ cand, Real.log p * io p ≤ a * m * T * lhsW cand θ Sig := by
    unfold lhsW
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have h := mul_le_mul_of_nonneg_left (hio p hp) (Real.log_natCast_nonneg p)
    have hl := logdiv_nonneg p
    have hi : (0 : ℝ) ≤ (if θ < Sig p then (2 : ℝ) else 0) := by split_ifs <;> norm_num
    have h0 : 0 ≤ a * m * T * (Real.log p / p * (if θ < Sig p then (2 : ℝ) else 0)) := by positivity
    have e : a * m * T * (Real.log p / p * ((if θ < Sig p then (2 : ℝ) else 0) + 4 * Sig p)) =
        Real.log p * (2 * Sig p * (2 * (m * T * a) / p)) +
          a * m * T * (Real.log p / p * (if θ < Sig p then (2 : ℝ) else 0)) := by ring
    rw [e]; linarith
  have h3 := mul_le_mul_of_nonneg_left hW hc
  linarith

lemma sizeOut_core {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tOutD P m T ≤ sg P K * unitU P m T := by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tOutD unitU
  have h9 := F.xpos
  have hpow : P.x ^ (-2 + P.ε) = P.x⁻¹ ^ 2 * z := by
    rw [Real.rpow_add h9, Real.rpow_neg h9.le, ← F.hz, Real.rpow_ofNat, F.r2]
  have key : 4 * P.a * P.x ^ (-2 + P.ε) ≤ sg P K * P.b := by
    rw [F.ha, hpow]
    calc 4 * (P.x * P.b) * (P.x⁻¹ ^ 2 * z)
        = P.b * (4 / 100 * (P.x * P.x⁻¹)) * (100 * z ^ 1 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.zr0 1) (F.zr_sg (by norm_num))
  have := scale2 hm hT key
  linarith

lemma size_ninth_power_bound {P : Par} {e K : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) :
    2 * P.a * (P.x ^ 9)⁻¹ ≤ sg P K * P.b := by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hr0 := F.rpos
  have hr1 : P.x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ F.x1
  have h7 : P.x⁻¹ ^ 7 ≤ 1 := pow_le_one₀ hr0.le hr1
  have h70 : 0 ≤ P.x⁻¹ ^ 7 := pow_nonneg hr0.le 7
  rw [F.ha, ← inv_pow]
  calc 2 * (P.x * P.b) * P.x⁻¹ ^ 9
      = P.b * (2 / 100 * (P.x * P.x⁻¹) * P.x⁻¹ ^ 7) * (100 * z ^ 0 * P.x⁻¹) := by ring
    _ ≤ sg P K * P.b := by
        rw [F.xr]
        exact F.close_sg (by linarith) (by linarith) (F.zr0 0) (F.zr_sg (by norm_num))

lemma sizeSecond_core {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tSecondD P m T ≤ sg P K * unitU P m T := by
  unfold tSecondD unitU
  have := scale2 hm hT (size_ninth_power_bound hW hL)
  linarith

lemma sizeIo_core {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tIoD P m T ≤ sg P K * unitU P m T := by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have h0 : 0 ≤ P.a * (P.x ^ 9)⁻¹ := mul_nonneg F.apos.le (inv_nonneg.2 (pow_nonneg F.xpos.le 9))
  have key : P.a * (P.x ^ 9)⁻¹ ≤ sg P K * P.b := by
    have := size_ninth_power_bound hW hL
    linarith
  unfold tIoD unitU
  have := scale2 hm hT key
  linarith

lemma size_core {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tDetD P m T ≤ (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P m T := by
  have a1 := size_floors_bound P e K m T hW hL hm hT
  have a2 := size_cp_bucket_bound P e K m T hW hL hm hT
  have a3 := size_prime_low_bound P e K m T hW hL hm hT
  have a4 := size_prime_high_bound P e K m T hW hL hm hT
  have a5 := size_or_bucket_bound P e K m T hW hL hm hT
  have a6 := sizeOut_core hW hL hm hT
  have a7 := size_orders_bucket_bound P e K m T hW hL hm hT
  have a8 := size_band_bound P e K m T hW hL hm hT
  have a9 := size_high_bucket_bound P e K m T hW hL hm hT
  have a10 := size_discriminant_bound P e K m T hW hL hm hT
  have a11 := sizeSecond_core hW hL hm hT
  unfold tDetD
  linarith

lemma joint_core : ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord → Windows P e K →
    LargeX P.x P.ε e K →
    ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D →
      ExplicitLossAndPrimeLogSumBounds P K Ps cand J TT io D ∧ ExcessAndPrimeLogSumUnitBounds P Ps cand J TT io D := by
  obtain ⟨C₁, hC₁⟩ := first_kind_bound
  refine ⟨max C₁ 0, le_max_right _ _, ?_⟩
  intro P e K hCord hW hL ι κ τ U Ps cand PR J TT BAD Sig io D hS
  obtain ⟨hTT, hPs, hSig0, hWW, hT2, hio, hAll⟩ := hS
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, -⟩ :=
    side_condition_of_windows P e K hW hL
  have hm : (0 : ℝ) ≤ (J.card : ℝ) := Nat.cast_nonneg _
  have hT : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hTT
  have hT0 : (0 : ℝ) ≤ (TT.card : ℝ) := Nat.cast_nonneg _
  have ha0 : 0 ≤ P.a := F.apos.le
  have hU := unitU_nonneg (P := P) hm hT
  have hA : ∀ υ, (D υ).ASK P.d Ps J TT - (D υ).Ga J ≤
      (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P J.card TT.card := by
    intro υ
    obtain ⟨hLed, hFirst, hSecond, hBad⟩ := hAll υ
    obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
    have led := loss_bound ι κ τ (D υ).W (D υ).below (D υ).l Ps (D υ).cl J TT (D υ).TTp
      (D υ).Iex (D υ).at_ (D υ).wz (D υ).Id (D υ).wd P.d (D υ).gainW (D υ).tauW
      (D υ).gain (D υ).tau (D υ).lo (D υ).fl P.a P.th P.wpp P.Xpp P.Xp P.C P.f P.N P.Sk P.Q₁ P.Q₂
      P.lx P.La P.k P.K₀ (D υ).L₁ P.p₀ l1 (fun p hp => (hPs p hp).1) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
      s11 s12 s13 s14 s15 s16 s17 s18 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
    have out := out_discriminant_bound τ Ps PR (D υ).cl TT (D υ).TTp BAD J.card P.a _ hm ha0 hT2 hBad
    have first := first_le hC₁ (by rw [hCord]; exact le_max_left _ _) hW hL Ps (D υ).cl hPs hFirst
      J.card TT.card hm hT0
    have second := second_discriminant_bound Ps cand (D υ).cl Sig P.θ J.card TT.card P.a _ hm hT0 ha0 hSig0 hWW hSecond
    have size := size_core hW hL hm hT
    unfold tDetD tFloors tCp tPrLow tPrHigh tOr tHigh tD tOutD tSecondD at size
    unfold LD.ASK LD.Ga
    linarith
  have hI : ∀ υ, ∑ p ∈ cand, Real.log p * io υ p ≤ sg P K * unitU P J.card TT.card := by
    intro υ
    have h := io_discriminant_bound cand Sig (io υ) P.θ J.card TT.card P.a _ hm hT0 ha0 hWW (hio υ)
    have size := sizeIo_core hW hL hm hT
    unfold tIoD at size
    linarith
  refine ⟨⟨hA, hI⟩, fun υ => (hA υ).trans ?_, fun υ => (hI υ).trans ?_⟩
  · have h1 : 2 * Real.log 4 * P.C + 13 * sg P K ≤ 3 * P.C + 13 := by
      have := mul_le_mul_of_nonneg_right (show 2 * Real.log 4 ≤ 3 by linarith [log_four_le_three_halves]) F.C0
      linarith [F.sg1]
    exact mul_le_mul_of_nonneg_right h1 hU
  · have := mul_le_mul_of_nonneg_right F.sg1 hU
    linarith

theorem joint_discriminant_bound : LossBoundsUnderSizeWindows := by
  obtain ⟨Cord, h0, h⟩ := joint_core
  refine ⟨Cord, h0, ?_⟩
  intro P e K hC hW hL ι κ τ U Ps cand PR J TT BAD Sig io D hS
  exact (h (clr P) e K hC ((discriminant_windows_iff P e K).1 hW) hL ι κ τ U Ps cand PR J TT BAD Sig io D hS).2

theorem joint_discriminant_eventually : LossBoundsEventually := by
  obtain ⟨Cord, h0, h⟩ := joint_discriminant_bound
  refine ⟨Cord, h0, ?_⟩
  intro ε e K hε hε4
  obtain ⟨x₀, hx₀⟩ := large_x_eventually ε e K hε hε4
  refine ⟨x₀, ?_⟩
  intro P hPε hPC hx hW
  exact h P e K hPC hW (by rw [hPε]; exact hx₀ _ hx)

end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
section -- merged from Formalism.LocalToGlobal.GlobalTheory.FamColC
open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamColC

open Formalism Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.FamCol

section Obj

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

structure RowTr [Fintype I] (C : ColObj K I) (R : RowArg C) (x ε : ℝ) : Prop where
  X' : ∀ w, IsUnit (R.X' w).det
  Y : ∀ u, IsUnit (R.Y u).det
  Y' : IsUnit R.Y'.det
  cc_fg : R.cc.FG
  cc_span : Submodule.span K (R.cc : Set R.Wd) = ⊤
  into : ∀ u, (C.Npr u).map ((R.B u).restrictScalars (𝓞 K)) ≤ R.cc
  ht : ∀ u, R.B u ≠ 0 → htMap (C.M u).b (C.M u).X R.b' R.X' (R.B u) ≤ R.h u
  block : ∀ u (k : R.κ) (j : (C.M u).ι), R.Ball u (Sum.inl k) j =
    (R.Y'⁻¹ * (LinearMap.toMatrix (C.M u).b R.b' (R.B u)).map R.v.embedding * R.Y u) k j
  γ : ∀ u, 0 < R.γ u
  Ball : ∀ u, R.Ball u = R.Bf u * C.Vr u R.v
  η0_ge : -1 ≤ R.η0
  η0_le : R.η0 ≤ LChain6.E8 x ε
  η1_le : R.η1 ≤ LChain6.E8 x ε
  exponent_bound_ter : 0 ≤ R.e0
  sqrt_error_le_half : Real.sqrt R.e0 ≤ LChain6.E8 x ε
  inputS : MatrixLatticeEstimates.InputSG R.Bf R.γ C.Dstar R.η0 R.η1 R.e0
  irr : (1 - LChain6.E7 x ε) * (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (Fintype.card R.κ : ℝ)

end Obj

section Fam7

variable {H : Type} {W : H → Type}

end Fam7

section Collected

open Formalism.L2.Indef Formalism.L2.DIV Formalism.DivisionValues

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}
  {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}

end Collected

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.LChain6

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end Family

section Core

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.LChain6

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end Core

end Formalism.L2.GlobalTheoryTheory.FamColC

end
end

open NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ConcN

open Formalism Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.FamCol

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

def IrrAt {C : ColObj K I} (R : RowArg C) (x ε : ℝ) : Prop :=
  (1 - LChain6.E7 x ε) * (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (Fintype.card R.κ : ℝ)

def CountAt {C : ColObj K I} (R : RowArg C) (εC W₁ W₂ : ℝ) : Prop :=
  ∃ PP₁ PP₂ D₁ D₂ Dstar : ℝ, 0 ≤ εC ∧ εC < 1 ∧ 0 < Dstar ∧
    0 ≤ PP₁ ∧ PP₁ ≤ W₁ ∧ 0 ≤ PP₂ ∧ PP₂ ≤ W₂ ∧
    |(Fintype.card (R.κ ⊕ R.κ₁) : ℝ) - Dstar| ≤ εC * Dstar ∧
    |D₁ - PP₁ * Dstar| ≤ εC * (PP₁ * Dstar) ∧ |D₂ - PP₂ * Dstar| ≤ εC * (PP₂ * Dstar) ∧
    (Fintype.card R.κ₁ : ℝ) ≤ D₁ + D₂

end Defs

def NumbersAt (x ε εC C W₁ W₂ : ℝ) : Prop :=
  0 ≤ εC ∧ εC ≤ 1 / 2 ∧ W₁ ≤ x ^ C * Real.exp (-(x ^ (ε / 6))) ∧ W₂ ≤ x ^ C * Real.exp (-(x ^ (ε / 6)))

def NumbersDominantLarge : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ C ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop, ∀ εC W₁ W₂ : ℝ,
    NumbersAt x ε εC C W₁ W₂ → (1 + εC) / (1 - εC) * (W₁ + W₂) ≤ LChain6.E7 x ε

def Wg (f m N g q₁ d : ℕ) : ℝ :=
  3 * (f : ℝ) / (g : ℝ) +
    23 * (f : ℝ) * Real.log (g : ℝ) / Real.sqrt (g : ℝ) +
    2 * (f : ℝ) * (m : ℝ) * (1 / (4 * ((min q₁ d : ℕ) : ℝ)) + (1 + Real.log (N : ℝ)) / ((g : ℝ) - 1)) +
    (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f +
    Real.exp (-(f : ℝ) / (5 * Real.log (N : ℝ)))

def epsC (c : ℝ) (N f : ℕ) : ℝ := Real.exp (-(c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ)))

def SizesAt (x ε Cs : ℝ) (f m N g q₁ d : ℕ) : Prop :=
  Real.exp (8 * x ^ ε) ≤ (g : ℝ) ∧ x ^ 2 ≤ (f : ℝ) ∧ (f : ℝ) ≤ x ^ Cs ∧ (m : ℝ) ≤ x ^ Cs ∧
    100 ≤ N ∧ (N : ℝ) ≤ x ^ Cs ∧ Real.exp (x ^ (ε / 6)) ≤ ((min q₁ d : ℕ) : ℝ)

def WeightNumbersBound : Prop :=
  ∀ ε Cs : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℝ in Filter.atTop, ∀ f m N g q₁ d : ℕ,
    SizesAt x ε Cs f m N g q₁ d → Wg f m N g q₁ d ≤ x ^ (3 * Cs + 3) * Real.exp (-(x ^ (ε / 6)))

def EpsilonBoundLargeX : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ x : ℝ in Filter.atTop, ∀ N f : ℕ, 100 ≤ N → x ^ 2 ≤ (f : ℝ) → epsC c N f ≤ 1 / 2

def CountBoundForCompatibleRows {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} {C : ColObj K I} (R : RowArg C)
    {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
    (e₁ e₂ : HH →ₗ[k] HH) (εC W₁ W₂ : ℝ) : Prop :=
  e₁ ∘ₗ e₁ = e₁ ∧ e₂ ∘ₗ e₂ = e₂ ∧ e₁ ∘ₗ e₂ = e₂ ∘ₗ e₁ ∧
  Module.finrank k HH = Fintype.card (R.κ ⊕ R.κ₁) ∧
  Module.finrank k (LinearMap.range (e₁ + e₂ - e₁ ∘ₗ e₂)) = Fintype.card R.κ₁ ∧
  ∃ PP₁ PP₂ Dstar : ℝ, 0 ≤ εC ∧ εC < 1 ∧ 0 < Dstar ∧
    0 ≤ PP₁ ∧ PP₁ ≤ W₁ ∧ 0 ≤ PP₂ ∧ PP₂ ≤ W₂ ∧
    |(Module.finrank k HH : ℝ) - Dstar| ≤ εC * Dstar ∧
    |(Module.finrank k (LinearMap.range e₁) : ℝ) - PP₁ * Dstar| ≤ εC * (PP₁ * Dstar) ∧
    |(Module.finrank k (LinearMap.range e₂) : ℝ) - PP₂ * Dstar| ≤ εC * (PP₂ * Dstar)

section Rec

open Formalism.BasicNotions Formalism.MainNotions

def CountBoundForCompatibleRowsRecursive (D : D7) {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH]
    [FiniteDimensional k HH] (e₁ e₂ : HH →ₗ[k] HH) (εC W₁ W₂ : ℝ) : Prop :=
  e₁ ∘ₗ e₁ = e₁ ∧ e₂ ∘ₗ e₂ = e₂ ∧ e₁ ∘ₗ e₂ = e₂ ∘ₗ e₁ ∧
  Module.finrank k HH = D.what₂.Dall ∧
  D.what₂.Drows + Module.finrank k (LinearMap.range (e₁ + e₂ - e₁ ∘ₗ e₂)) = D.what₂.Dall ∧
  ∃ PP₁ PP₂ Dstar : ℝ, 0 ≤ εC ∧ εC < 1 ∧ 0 < Dstar ∧
    0 ≤ PP₁ ∧ PP₁ ≤ W₁ ∧ 0 ≤ PP₂ ∧ PP₂ ≤ W₂ ∧
    |(Module.finrank k HH : ℝ) - Dstar| ≤ εC * Dstar ∧
    |(Module.finrank k (LinearMap.range e₁) : ℝ) - PP₁ * Dstar| ≤ εC * (PP₁ * Dstar) ∧
    |(Module.finrank k (LinearMap.range e₂) : ℝ) - PP₂ * Dstar| ≤ εC * (PP₂ * Dstar)

def SizesRec (D : D7) (x ε Cs : ℝ) : Prop :=
  ∀ j : Fin 2, SizesAt x ε Cs D.R.f D.R.m D.R.r (D.host.g j) D.host.q D.host.d

def IrreducibleOfCompatibleForms : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BadRankUnion → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps) (k : Type) [Field k]
    (HH : ∀ x, Fm.Ix x → Type) [∀ x i, AddCommGroup (HH x i)] [∀ x i, Module k (HH x i)]
    [∀ x i, FiniteDimensional k (HH x i)] (e₁ e₂ : ∀ x i, HH x i →ₗ[k] HH x i),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SizesRec (Fm.D x i) x Fm.ez Cs ∧
      CountBoundForCompatibleRowsRecursive (Fm.D x i) (HH x i) (e₁ x i) (e₂ x i) (epsC c (Fm.D x i).R.r (Fm.D x i).R.f)
        (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 0) (Fm.D x i).host.q (Fm.D x i).host.d)
        (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 1) (Fm.D x i).host.q (Fm.D x i).host.d)) →
    LinkIRR Fm

end Rec

section Inputs

open Formalism.BasicNotions Formalism.MainNotions

def CountRec {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
    (e₁ e₂ : HH →ₗ[k] HH) (εC : ℝ) (PP : Fin 2 → ℝ) : Prop :=
  0 ≤ εC ∧ εC < 1 ∧ ∃ Dstar : ℝ, 0 < Dstar ∧
    |(Module.finrank k HH : ℝ) - Dstar| ≤ εC * Dstar ∧
    |(Module.finrank k (LinearMap.range e₁) : ℝ) - PP 0 * Dstar| ≤ εC * (PP 0 * Dstar) ∧
    |(Module.finrank k (LinearMap.range e₂) : ℝ) - PP 1 * Dstar| ≤ εC * (PP 1 * Dstar)

end Inputs

section AllRowsIn

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders

def DstarE {D : D7} (A : AllRows D) (e : A.B.I.Gf → ℂ) : ℝ :=
  A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund e

def CountAllRows {D : D7} (A : AllRows D) (εC : ℝ) : Prop :=
  0 ≤ εC ∧ εC < 1 ∧ 0 < DstarE A A.B.e ∧
    ∀ (k : Fin 2) (S : Set (Tup D k)),
      |(A.dimT (cyl D k S) : ℝ) - DstarE A (A.eT (cyl D k S))| ≤ εC * DstarE A (A.eT (cyl D k S))

def WeightAllRows {D : D7} (A : AllRows D) : Prop :=
  (∀ (k : Fin 2) v f, 0 ≤ wtOf D k (A.eVec k v) f) ∧
    ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) →
      locShare D A.eVec k S ≤ Wg D.R.f D.R.m D.R.r (D.host.g k) D.host.q D.host.d

def FamilyIrreducibleOfCountWeightSizes : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i),
      LabelCountGoodInjective A ∧
      CountAllRows A (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧
      WeightAllRows A ∧
      SizesRec (Fm.D x i) x Fm.ez Cs) →
    LinkIRR Fm

end AllRowsIn

end Formalism.L2.GlobalTheoryTheory.ConcN
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.LossRequirementsOfSmallShares
section -- merged from Formalism.LocalToGlobal.GlobalTheory.SmallShareWeightExists
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss7

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds Formalism.LFunctionChainParameters.SmallOrderPrimeLosses Formalism.L2.GlobalTheoryTheory.Loss

def LossSettingFamily : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (X : G.Inst D L) (K : G.Consts) (Cr C bo : ℝ) (P : Par),
    PtH X K Cr → LinkG_at X K C bo → ParTie P L K C bo Cr → 0 ≤ bo → 0 ≤ L.LaG → L.sc.p0 D.R.k ≤ L.sc.X' →
    D.host.TT.Nonempty → ChBadp_at X → ChW_at X K →
    PrimeClassLossHypotheses P (PsAt L) (sAt L K) (largeOrderResiduePrimes L) (SizeData₂.lifts D) (TTv D) (badAt X)
      (fun p => G.Sig X K (G.aL L) (G.bL L) p) (fun (_ : Unit) p => G.ioP X K (G.aL L) (G.bL L) p)
      (fun _ => ldAt X K C bo)

def ThickDensitySizeWindowsForAllFamilies : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps), ChosenTT Fm → ChosenBadp Fm → LinkG Fm → Lnk.LossesSmallShares Fm

end Formalism.L2.GlobalTheoryTheory.Loss7

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss7

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds Formalism.LFunctionChainParameters.SmallOrderPrimeLosses Formalism.L2.GlobalTheoryTheory.Loss

section AtRecord

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts)

theorem cands_eq : cands L K = sAt L K := rfl

theorem card_lifts (D : D7) : (SizeData₂.lifts D).card = D.R.m := by
  simp [SizeData₂.lifts]

theorem card_TTv (D : D7) : (TTv D).card = D.host.TT.card := by
  have h := pb_sum_TTv (D := D) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_coe] at h
  exact_mod_cast h


open Classical in
theorem bad_card_at (p : ℕ) : ((TTv D).filter (fun n => badAt X p n)).card = (badTops X p).card := by
  have h := pb_sum_TTv (D := D) (fun n => if badAt X p n then (1 : ℝ) else 0)
  rw [Finset.sum_boole] at h
  have h2 : (∑ t : D.host.TT, if badAt X p (t : D.R.A).val then (1 : ℝ) else 0) = ((badTops X p).card : ℝ) := by
    rw [badTops, Finset.card_filter]
    push_cast
    rw [← Finset.sum_coe_sort D.host.TT]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [badAt, pb_cast]
  exact_mod_cast h.trans h2

end AtRecord

theorem loss_setting_family : LossSettingFamily := by
  classical
  intro D L X K Cr C bo P H hG tie hbo hLa hp0 hTT hB hW
  obtain ⟨-, -, -, -, -, -, -, ea, -, eθ⟩ := side_at X K Cr C bo H P tie hbo hLa hp0
  have hx0 : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hSig : ∀ p, 0 ≤ G.Sig X K (G.aL L) (G.bL L) p :=
    fun p => Lnk.Sig_nonneg X K H.Knn H.kapI _ _ p
  refine ⟨?_, ?_, fun p _ => hSig p, ?_, ?_, ?_, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · unfold TTv; exact hTT.image _
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_PsAt hp
    exact ⟨h1, fun h => two_not_inert _ (h ▸ h2)⟩
  · unfold ChW_at at hW
    unfold lhsW
    rw [eθ, tie.x, ← cands_eq]
    have e9 : L.sc.x ^ (-9 : ℝ) = (L.sc.x ^ 9)⁻¹ := by
      rw [Real.rpow_neg hx0.le]
      congr 1
      exact_mod_cast Real.rpow_natCast L.sc.x 9
    rw [← e9]
    exact hW
  · unfold ChBadp_at at hB
    unfold badPrimeLogWeightedCount
    rw [card_TTv, tie.x, tie.ε]
    simp only [bad_card_at]
    exact hB
  · intro _ p _
    have h := Lnk.ioP_le X K p (hG.2.1 p) (hSig p)
    rw [card_lifts, card_TTv, ea]
    exact h
  · exact lossHyp_at X K Cr C bo H hG P tie hbo hLa hp0
  · exact firstHyp_at X K Cr C bo H (T_not_inert _) P tie
  · intro p _ h
    obtain ⟨h1, h2⟩ := second_spec X K p h
    rw [eθ]
    exact ⟨(mem_sAt K).mpr h1, h2⟩
  · intro p hp h n hn
    have hn' : n ∈ TTv D ∧ n ∉ (ldAt X K C bo).TTp p := by
      simpa only [Finset.mem_sdiff] using hn
    exact unserved_bad X K Cr C bo H (T_not_inert _) p hp h n (Finset.mem_sdiff.mpr hn')

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem losses_of_small_share_weight (hTT : ChosenTT Fm) (hBad : ChosenBadp Fm) (hG : LinkG Fm) : Lnk.LossesSmallShares Fm := by
  classical
  obtain ⟨Cord, hCord, hJ⟩ := joint_discriminant_eventually
  obtain ⟨xT, hTT⟩ := hTT
  obtain ⟨xB, hBad⟩ := hBad
  obtain ⟨C, xG, δ, hδ, hG⟩ := hG
  obtain ⟨xA, hAsk⟩ := Lnk.askIsF Fm
  obtain ⟨e, K, x0, hW⟩ := windows_ev Fm C 0 Cord hCord δ hδ
  have heps : 0 < eps := Lnk.fam_eps_pos Fm
  have heps4 : eps < 1 / 4 := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.eps_lt
    rw [Fm.L_eps 0 i] at this
    linarith
  obtain ⟨x1, hJ'⟩ := hJ eps e K heps heps4
  refine ⟨3 * |K| + 13, max (max x0 xT) (max xB (max xG (max xA x1))), by positivity, fun x hxx i hWi => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxx
  have eT : x ≥ xT := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxx
  have eB : x ≥ xB := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxx
  have eG : x ≥ xG := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hxx
  have eA : x ≥ xA := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
    (le_max_right _ _)) hxx
  have e1 : x1 ≤ x := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
    (le_max_right _ _)) hxx
  obtain ⟨hx, h3, hW⟩ := hW x e0
  obtain ⟨hW, hp0⟩ := hW i
  set bo : ℝ := (Fm.L x i).sc.b ^ δ x with hbo
  have hbo0 : 0 ≤ bo := Real.rpow_nonneg (Real.exp_pos _).le _
  set P : Par := par Fm x i C bo 0 Cord with hP
  have tie : ParTie P (Fm.L x i) Fm.GK C bo Fm.Cr := parTie (i0 := i) hx i C bo 0 Cord
  have hH : PtH (Fm.Gx x i) Fm.GK Fm.Cr := ptH Fm hx h3 i
  have hLa : 0 ≤ (Fm.L x i).LaG := by
    have h1 := (Fm.sizes x hx i).2.2.2.2.2.2.2.2.1.1
    exact le_trans (Real.rpow_nonneg (lt_trans one_pos (Fm.L x i).sc.one_lt_alt).le _) h1
  have hne : (Fm.D x i).host.TT.Nonempty := by
    rw [← Finset.card_pos]
    have h1 := (hTT x eT i).1
    have hx0 : 0 < (Fm.L x i).sc.x := lt_trans one_pos (Fm.L x i).sc.one_lt_alt
    have h2 : 0 < (Fm.L x i).sc.delta1 * (Fm.D x i).R.n / 2 := by
      have : 0 < (Fm.L x i).sc.delta1 := Real.rpow_pos_of_pos hx0 _
      have h4 : (0 : ℝ) < (Fm.D x i).R.n := lt_of_lt_of_le one_pos (Lnk.one_le_n _)
      positivity
    exact_mod_cast lt_of_lt_of_le h2 h1
  have hS := loss_setting_family (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK Fm.Cr C bo P hH (hG x eG i) tie hbo0 hLa hp0 hne
    (hBad x eB i) hWi
  have hPx : P.x = x := Fm.L_x x i hx
  have hPe : P.ε = eps := Fm.L_eps x i
  obtain ⟨hc1, hc2⟩ := hJ' P hPe rfl (by rw [hPx]; exact e1) (discriminant_windows_of P e K hW) ℕ ℕ ℕ Unit _ _ _ _ _ _ _ _ _ hS
  have hPC0 : 0 ≤ P.C := le_max_right _ _
  have hPCK : P.C ≤ K := hW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hU : unitU P (SizeData₂.lifts (Fm.D x i)).card (TTv (Fm.D x i)).card =
      ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b := by
    unfold unitU; rw [card_lifts, card_TTv, pd_b tie]
  have hU0 : 0 ≤ ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hone : (Fm.L x i).sc.x ^ ((0 : ℝ) * (Fm.L x i).sc.eps) = 1 := by rw [zero_mul, Real.rpow_zero]
  have hKabs : K ≤ |K| := le_abs_self K
  have hbig : (3 * P.C + 13) * (((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b) ≤
      (3 * |K| + 13) * (Fm.D x i).host.TT.card * (Fm.D x i).R.m * (Fm.L x i).sc.b *
        (Fm.L x i).sc.x ^ ((0 : ℝ) * (Fm.L x i).sc.eps) := by
    rw [hone, mul_one]
    have := mul_le_mul_of_nonneg_right (show 3 * P.C + 13 ≤ 3 * |K| + 13 by linarith) hU0
    simpa [mul_assoc] using this
  have hsmall : ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b ≤
      (3 * P.C + 13) * (((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b) := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 3 * P.C + 13 by linarith) hU0
    linarith
  constructor
  · have h2 := hc2 ()
    rw [IO_at (Fm.Gx x i) Fm.GK Fm.Cr hH, hU] at h2
    linarith
  · intro e' m' AD N TT' a w hr hAD hcut
    rw [hAsk x eA i e' m' AD N TT' a w hr hAD hcut]
    have h1 := hc1 ()
    rw [Ga_at (Fm.Gx x i) Fm.GK Fm.Cr C bo hH, hU, tie.d, ASK_at (Fm.Gx x i) Fm.GK Fm.Cr C bo hH] at h1
    linarith

end Family

theorem stLoss7 : ThickDensitySizeWindowsForAllFamilies := fun _ Fm h1 h2 h3 => losses_of_small_share_weight Fm h1 h2 h3

section Size

variable {D : D7} {L : SizeData₂ D}

end Size

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem loss_requirements_of_small_shares (C0 CH : ℝ) (h : ChosenE Fm C0 CH) (hW : ChosenWall Fm) : WeightVectorSmallSharesSeven Fm C0 CH := by
  obtain ⟨C5, c6, Cb, h5, h6, hb, hT2, hTT, hBad, hQD, hThin, hPr, hCode⟩ := h
  exact ⟨C5, c6, h5, h6, Lnk.thick_density_of_construction Fm hT2, hTT, Lnk.chosenBadp_of_old Fm Cb hb.le hTT hBad,
    chosenWS_of_wall (Fm := Fm) hW, hQD, hThin, hPr, hCode⟩

end Family

end Formalism.L2.GlobalTheoryTheory.Loss7

end
end
