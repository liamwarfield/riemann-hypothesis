module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthFourDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsHorizontalLiftOfLenThreeOfUp

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsFractionInFrame
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem ArcLengthFourSecond.isUnit_ps (W : LocWach PD LL O v n) (hR : GS.RD W) (t : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (ps W t)) := by
  have hp : PD.p.Prime := by
    first
      | exact PD.hp.out
      | exact PD.hp
      | exact PD.p_prime
      | exact PD.prime
      | exact PD.hprime
      | exact Fact.out
  obtain ⟨⟨w1, hw1⟩, ⟨w2, hw2⟩, -, -⟩ := hR
  have hπ0 : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw1, map_mul, map_pow]
    exact (w1.isUnit.map _).mul (W.EE_π.pow _)
  have hq0 : IsUnit (algebraMap (LetA O n) W.EE (qA W)) := by
    have h := congrArg (algebraMap (LetA O n) W.EE) hw2
    rw [map_mul, map_mul, map_pow] at h
    have hφ : IsUnit (algebraMap (LetA O n) W.EE (W.φA W.π₀)) := by
      rw [show algebraMap (LetA O n) W.EE (W.φA W.π₀) = W.φE (algebraMap (LetA O n) W.EE W.π₀) from
        (W.φE_ext W.π₀).symm]
      exact hπ0.map W.φE
    rw [h] at hφ
    have h3 := isUnit_of_mul_isUnit_right hφ
    exact (isUnit_pow_iff (by have := hp.two_le; omega)).1 h3
  induction t with
  | zero => simpa [ps] using hq0
  | succ t ih =>
    have e : algebraMap (LetA O n) W.EE (ps W (t + 1)) = W.φE (algebraMap (LetA O n) W.EE (ps W t)) := by
      rw [ps, ps, pow_succ', AlgHom.mul_apply]
      exact (W.φE_ext _).symm
    rw [e]
    exact ih.map W.φE

theorem ArcLengthFourSecond.cst_add [IsDomain O] [IsDiscreteValuationRing O] {W : LocWach PD LL O v n} (Br : PhiBridge W)
    (F G : PowerSeries O) : Br.cst (F + G) = Br.cst F + Br.cst G := by
  show (fun _ => Br.ι (F + G) : LetA O n) = (fun _ => Br.ι F : LetA O n) + (fun _ => Br.ι G : LetA O n)
  rw [map_add (f := _)]
  rfl

theorem exists_fraction_in_frame [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hinj : Function.Injective (algebraMap O LL))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (c : ZMod n) (wa Bn η s : ℕ) (hBn : 1 ≤ Bn) (x₀ : O) :
    ∃ (fa : W.EE) (si : ℕ), InFr W c 1 (ps W 2 ^ wa) fa ∧
      InFr W c (ps W 1 ^ Bn * ps W 0 ^ η) (ps W 2 ^ wa)
        (lE W s * fa - lE W (s - si) * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀)) ∧
      (wa : ℝ) - (Bn : ℝ) / PD.p - (η : ℝ) / (PD.p : ℝ) ^ 2 - 1 ≤ si := by
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T hT hO hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hR := GS.ringData_of_caseA_of_p9 W hcase hP9
  set y : ℝ := (wa : ℝ) - (Bn : ℝ) / PD.p - (η : ℝ) / (PD.p : ℝ) ^ 2 with hy
  set si : ℕ := ⌊y⌋₊ with hsi
  have hk : eO (O := O) PD.p * si ≤
      ⌈(eO (O := O) PD.p : ℝ) * ((wa : ℝ) - Bn / PD.p - η / (PD.p : ℝ) ^ 2)⌉₊ := by
    rw [← hy]
    by_cases h0 : 0 ≤ y
    · have h1 : (si : ℝ) ≤ y := Nat.floor_le h0
      have h2 : ((eO (O := O) PD.p * si : ℕ) : ℝ) ≤ (eO (O := O) PD.p : ℝ) * y := by
        push_cast; exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      exact_mod_cast h2.trans (Nat.le_ceil _)
    · have : si = 0 := Nat.floor_eq_zero.mpr (by linarith)
      rw [this, mul_zero]; exact Nat.zero_le _
  have hmem := Br.P.c3b hϖ wa Bn η (Or.inl hBn) (eO (O := O) PD.p * si) hk
  have hspan := span_C_l_pow hϖ Br.P.hl0 si
  obtain ⟨r, hr⟩ : ∃ r : PowerSeries O,
      r * (PowerSeries.C ((PD.p : ℕ) : O)) ^ si = (PowerSeries.C ϖ) ^ (eO (O := O) PD.p * si) := by
    have : (PowerSeries.C ϖ : PowerSeries O) ^ (eO (O := O) PD.p * si) ∈
        Ideal.span {(PowerSeries.C ((PD.p : ℕ) : O) : PowerSeries O) ^ si} := by
      rw [hspan]; exact Ideal.subset_span rfl
    exact Ideal.mem_span_singleton'.mp this
  obtain ⟨α', β, hαβ⟩ := Ideal.mem_span_pair.mp hmem
  have hD : ps W 2 ^ wa = lA W ^ si * Br.cst (α' * r) + ps W 1 ^ Bn * ps W 0 ^ η * Br.cst β := by
    have e0 : ps W 0 = qA W := by simp [ps]
    have e2 : Br.cst (Br.P.p 2 ^ wa) =
        Br.cst ((α' * r) * PowerSeries.C ((PD.p : ℕ) : O) ^ si + β * (Br.P.p 1 ^ Bn * PowerSeries.X ^ η)) := by
      rw [← hαβ, ← hr]; congr 1; ring
    simp only [ArcLengthFourSecond.cst_add, Br.cst_mul, Br.cst_pow] at e2
    rw [← Br.ps_eq, ← Br.ps_eq, ← Br.qA_eq, ← Br.lA_eq, ← e0] at e2
    rw [e2, Br.cst_mul]; ring
  set e₄ := s - si with he₄
  set t := e₄ + si - s with ht
  have hexp : lA W ^ s * lA W ^ t = lA W ^ e₄ * lA W ^ si := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hUn : IsUnit (algebraMap (LetA O n) W.EE (ps W 2 ^ wa)) := by
    rw [map_pow]; exact (ArcLengthFourSecond.isUnit_ps W hR 2).pow _
  set u : LetA O n := lA W ^ t * (algebraMap O (LetA O n) x₀ * Br.cst (α' * r)) with hu
  have hu_mem : u ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.pow_mem ArcLengthFourSecond.lA_mem t) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x₀) (Br.cst_mem _))
  set fa : W.EE := ((hUn.unit⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (letE c * 1 * u) with hfa
  have hfaD : algebraMap (LetA O n) W.EE (ps W 2 ^ wa) * fa = algebraMap (LetA O n) W.EE (letE c * 1 * u) := by
    rw [hfa, ← mul_assoc, IsUnit.mul_val_inv hUn, one_mul]
  set u₂ : LetA O n := -(lA W ^ e₄ * (algebraMap O (LetA O n) x₀ * Br.cst β)) with hu₂
  have hu₂_mem : u₂ ∈ W.AΔ :=
    W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.pow_mem ArcLengthFourSecond.lA_mem e₄) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x₀) (Br.cst_mem _)))
  refine ⟨fa, si, ⟨u, hu_mem, hfaD⟩, ⟨u₂, hu₂_mem, ?_⟩, ?_⟩
  · calc algebraMap (LetA O n) W.EE (ps W 2 ^ wa) *
          (lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀))
        = lE W s * (algebraMap (LetA O n) W.EE (ps W 2 ^ wa) * fa) -
            lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀) *
              algebraMap (LetA O n) W.EE (ps W 2 ^ wa) := by ring
      _ = algebraMap (LetA O n) W.EE (lA W ^ s) * algebraMap (LetA O n) W.EE (letE c * 1 * u) -
            algebraMap (LetA O n) W.EE (lA W ^ e₄) * (algebraMap (LetA O n) W.EE (letE c) *
              algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x₀)) *
              algebraMap (LetA O n) W.EE (ps W 2 ^ wa) := by
          rw [hfaD, ArcLengthFourSecond.lE_eq, ArcLengthFourSecond.lE_eq, IsScalarTower.algebraMap_apply O (LetA O n) W.EE x₀]
      _ = algebraMap (LetA O n) W.EE (lA W ^ s * (letE c * 1 * u) -
            lA W ^ e₄ * (letE c * algebraMap O (LetA O n) x₀) * ps W 2 ^ wa) := by
          simp only [map_mul, map_sub]
      _ = algebraMap (LetA O n) W.EE (letE c * (ps W 1 ^ Bn * ps W 0 ^ η) * u₂) := by
          congr 1
          rw [hD, hu, hu₂]
          linear_combination ((letE c : LetA O n) * algebraMap O (LetA O n) x₀ * Br.cst (α' * r)) * hexp
  · have := Nat.lt_floor_add_one y
    rw [← hsi] at this
    linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem exists_liftsAt_le_of_len_three_of_up [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hU : up (c - 2) = true)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hth : Formalism.MainNotions.LiftingTheory.AI W F (c - 2) + η + 2 * (arcOf b w S η up size).σ PD.p + 2 ≤ size (c - 2)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 18 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁  := by
  classical
  have hp11 : 11 ≤ PD.p := hB.1
  have hSet := hB.2.1
  have hl5 : 5 ≤ PD.p := by omega
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hSet.2.1
  have hηs : ∀ i, η < size i := hSet.2.2.1
  have hup1 : up (c - 1) = false := by
    have h := (halt (c - 2)).1
    have e : c - 2 + 1 = c - 1 := by ring
    rw [e, hU] at h
    simpa using h
  have hup0 : up c = true := by
    have h := (halt (c - 1)).1
    have e : c - 1 + 1 = c := by ring
    rw [e, hup1] at h
    simpa using h
  have hty0 : (arcOf b w S η up size).ty (c - ((0 : ℕ) : ZMod n)) = .up (size c) := by
    simp [arcOf, hup0]
  have hty1 : (arcOf b w S η up size).ty (c - ((1 : ℕ) : ZMod n)) = .down (size (c - 1)) := by
    simp [arcOf, hup1]
  have hty2 : (arcOf b w S η up size).ty (c - ((2 : ℕ) : ZMod n)) = .up (size (c - 2)) := by
    simp [arcOf, hU]
  have hthick : ∀ t < (arcOf b w S η up size).len c, ((arcOf b w S η up size).ty (c - (t : ZMod n))).thick := by
    intro t _
    simp only [arcOf]
    split <;> rfl
  have hps : ∀ t, ps W t ∈ W.AΔ := fun t => GS.ps_mem W t
  have hnn : nnDen W (arcOf b w S η up size) c = ps W 0 ^ size c * ps W 2 ^ size (c - 2) := by
    unfold nnDen prodTy
    rw [hlen]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [hty0, hty1, hty2]
    simp

  obtain ⟨κ, x, hx⟩ := hf.2 1 (by rw [hlen]; norm_num) (size (c - 1)) hty1
  obtain ⟨s, hs, hdvd⟩ := arc_length_four_denominator W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2
    hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb halt hsm hlen hU
    hOK hσ κ x hx
  obtain ⟨x₀, hx₀⟩ := hdvd

  have hBn : 1 ≤ size (c - 1) + S := by have := hηs (c - 1); omega
  obtain ⟨fa, si, hfa1, hfa2, hsi⟩ := exists_fraction_in_frame W hcase hP9 hO hinj T₁ hW₁.1 c (size (c - 2)) (size (c - 1) + S) η s hBn x₀

  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hlt, hpr⟩ := exists_horizontal_lift_of_len_three_of_up W hcase F hB CR hWR hW₁ hW₂ hArc hR2 hO hOv hinj hP9 hSec hHF hFL
    c hc bb sol hbb k₀ hk₀ halt hlen hU hOK hth
  set σ := (arcOf b w S η up size).σ PD.p with hσdef
  set e₄ := s - si with he₄

  have hfaC : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ fa (2 * σ + 1 + σ) := by
    refine liftsAt_thin_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv
      hinj hArc hW₁ hW₂ hbb {2} ?_ b₁ sol₁ hb₁ c₁ (2 * σ + 1) ?_ hpr fa ?_ ?_ ?_
    · intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      exact ⟨by rw [hlen]; norm_num, _, hty2⟩
    · intro t ht bs hbs
      rw [Finset.mem_singleton] at ht
      subst ht
      rw [hty2] at hbs
      cases hbs
      exact hlt
    · simp only [Finset.prod_singleton, hty2]
      exact hfa1
    · intro t ht bs hbs
      rw [hlen] at ht
      interval_cases t
      · rw [hty0] at hbs; cases hbs
      · rw [hty1] at hbs
        cases hbs
        simp only [Finset.prod_singleton, hty2]
        refine ⟨s, ((PD.p : ℕ) : O) ^ e₄ * x₀, ?_⟩
        have e : lE W s * fa - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE (((PD.p : ℕ) : O) ^ e₄ * x₀) =
            lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀) := by
          rw [map_mul, map_pow, map_natCast]; unfold lE; ring
        rw [e]
        exact ArcLengthFourSecond.inFr_num_left hfa2 (W.AΔ.pow_mem (hps 0) _)
      · rw [hty2] at hbs; cases hbs
    · intro t ht hnt bs hbs
      rw [hlen] at ht
      interval_cases t
      · rw [hty0] at hbs
        cases hbs
        simp only [Finset.prod_singleton, hty2]
        refine ⟨s, ((PD.p : ℕ) : O) ^ e₄ * x₀, ?_⟩
        have e : lE W s * fa - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE (((PD.p : ℕ) : O) ^ e₄ * x₀) =
            lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀) := by
          rw [map_mul, map_pow, map_natCast]; unfold lE; ring
        rw [e]
        exact ArcLengthFourSecond.inFr_num_right hfa2 (W.AΔ.pow_mem (hps 1) _)
      · rw [hty1] at hbs; cases hbs
      · exact absurd (Finset.mem_singleton_self 2) hnt

  have hfa_nn : InFr W c 1 (nnDen W (arcOf b w S η up size) c) fa := by
    rw [hnn]; exact ArcLengthFourSecond.inFr_den_mul _ hfa1 (W.AΔ.pow_mem (hps 0) _)
  have hgN : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ (lE W e₄ * f - fa) (rr + σ) := by
    refine liftsAt_thick_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv
      hinj hArc hArcL hNN hW₁ hW₂ hsur rr hkill hbb hk₀ _ (ArcLengthFourSecond.inFr_sub (ArcLengthFourSecond.inFr_lE e₄ hf.1) hfa_nn) ?_
    intro t ht bs hbs
    rw [hlen] at ht
    interval_cases t
    · rw [hty0] at hbs; cases hbs
    · rw [hty1] at hbs
      cases hbs
      have hnum : ps W 1 ^ (size (c - 1) + (arcOf b w S η up size).S) ∈ PiPs W :=
        Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self 1))) _
      refine ArcLengthFourSecond.inFr_sat W hcase hP9 hinj hnum (ArcLengthFourSecond.inFr_sub (ArcLengthFourSecond.inFr_lE e₄ hf.1) hfa_nn) ⟨κ + s, ?_⟩
      have h2 : InFr W c (ps W 1 ^ (size (c - 1) + S)) (nnDen W (arcOf b w S η up size) c)
          (lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀)) := by
        rw [hnn]; exact ArcLengthFourSecond.inFr_den_mul _ (ArcLengthFourSecond.inFr_num_left hfa2 (W.AΔ.pow_mem (hps 0) _)) (W.AΔ.pow_mem (hps 0) _)
      have hxE : lE W s * algebraMap O W.EE x = lE W κ * algebraMap O W.EE x₀ := by
        have := congrArg (algebraMap O W.EE) hx₀
        rw [map_mul, map_mul, map_pow, map_pow, map_natCast] at this
        unfold lE; exact this
      have e : lE W (κ + s) * (lE W e₄ * f - fa) =
          lE W (s + e₄) * (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x) -
          lE W κ * (lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀)) := by
        unfold lE at hxE ⊢
        linear_combination (((PD.p : ℕ) : W.EE) ^ e₄ * algebraMap (LetA O n) W.EE (letE c)) * hxE
      rw [e]
      exact ArcLengthFourSecond.inFr_sub (ArcLengthFourSecond.inFr_lE _ hx) (ArcLengthFourSecond.inFr_lE _ h2)
    · rw [hty2] at hbs; cases hbs

  have hE1 : rr + σ ≤ rr + 3 * σ + 1 := by omega
  have hE2 : 2 * σ + 1 + σ ≤ rr + 3 * σ + 1 := by omega
  have hsum := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀
    (LiftsAt.liftsAt_mono W (arcOf b w S η up size) F c bb sol k₀ hE1 hgN)
    (LiftsAt.liftsAt_mono W (arcOf b w S η up size) F c bb sol k₀ hE2 hfaC)
  rw [sub_add_cancel] at hsum
  refine ⟨rr + 3 * σ + 1 + e₄, ?_, ?_⟩
  ·
    have hT : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i := by
      refine ⟨c, ?_⟩
      have h1 : (1 : ℕ) ∉ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
        apply Nat.notMem_of_lt_sInf
        have := hlen
        simp only [arcOf] at this
        rw [this]; norm_num
      simp only [Set.mem_setOf_eq, le_refl, true_and, not_not, Nat.cast_one, sub_add_cancel] at h1
      exact h1
    rw [sigma_eq_of_thick_letter PD.p b w S η size hT] at hrr hσ hs hsm ⊢
    have hb1 : 1 ≤ b := by
      obtain ⟨-, -, -, -, -, -, h1⟩ := CaseA.sg_ge PD.p (b + η + S) w S η hp11 (by
        have := hηs c; have := hT; obtain ⟨i, hi⟩ := hT; have := hηs i; have := hi.2; omega)
      have : (1 : ℝ) ≤ b := by linarith
      exact_mod_cast this
    have hsi' : (size (c - 2) : ℝ) - ((size (c - 1) : ℝ) + S) / PD.p - η / (PD.p : ℝ) ^ 2 - 1 ≤ si := by
      push_cast at hsi; exact hsi
    exact arc_length_four_cost_bound PD.p hp11 b w (size (c - 2)) S η hb1 ((size (c - 1) : ℝ) + S) s si rr σ hs hsi' hrr hσ
  · have e : lE W (rr + 3 * σ + 1 + e₄) * f = lE W (rr + 3 * σ + 1) * (lE W e₄ * f) := by
      unfold lE; ring
    obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := hsum
    exact ⟨w₁, z, h1, h2, h3, h4, by rw [e]; exact h5⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
