module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeFirstLevel
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeFirstLift
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FrobeniusRelationCombination

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeExistsLambdaNearHorizontal
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

theorem ring_identity_lambda_terms {R : Type} [CommRing R] (L Φ G a B J : R) (s1 s k1 E K S : ℕ) (hK : K = k1 + E)
    (hS : S = s1 + s) (H : L ^ s * Φ * G = (a * L ^ E + B * J) * G) :
    L ^ K * (L ^ s1 * G * a) - L ^ S * (Φ * (L ^ k1 * G)) = J * (-(L ^ s1 * L ^ k1 * G * B)) := by
  subst hK hS
  linear_combination (-(L ^ s1 * L ^ k1)) * H

theorem arc_length_three_exists_lambda_near_horizontal [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))  :
    ∃ (lam : W.DD T₂) (κ : ℕ) (Hh : W.DD T₂), InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam ∧
      InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam) ∧
      IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh ∧
      ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh)) := by
  set A := arcOf b w S η up size with hAdef
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hp2 : PD.p ≠ 2 := hcase.2.2
  have hT₂ : IsCrys PD T₂.ρ := hW₂.1
  have hC := Formalism.MainNotions.UnusedSlot80.Relay2.ctx_of W hinj hOv hP9 hH hTr hcase T₂ hT₂
  have h9 := (Formalism.MainNotions.LiftingTheory.frame_p9A W hP9 hcase T₂ hT₂).1
  have hM : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p :=
    Formalism.MainNotions.UnusedSlot80.Relay2.arith_M PD.p A.G₀ A.h hl hOK.2.2.2.2.2.1
  have hHc := hH hcase T₂ hT₂ c'
  have hbd : ∀ r m, Formalism.MainNotions.LiftingTheory.Bd W r (sol k₀ r m) := fun r m =>
    (hHc.2.2.2.2 d bb hbb.1 sol hbb.2).1 k₀ r m
  have h4 := hHc.2.2.2.1
  have hg : ∀ r m, ∃ o : O, algebraMap O LL o =
      (PD.p : LL) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r * sol k₀ r m :=
    fun r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hOv r (h4 r) _ (hbd r m)
  choose g hg using hg
  set M := A.M PD.p with hMdef
  set JJ1 := Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M with hJJ1
  have hdec : ∀ r, ∃ a ∈ W.AΔ, ∃ B' ∈ W.AΔ, ∀ m,
      ((PD.p : ℕ) : LetA O n) ^ Formalism.NOK.sigNOK PD.p (2 * A.G₀) M 1 * ((W.φA ^ 1) W.π₀) ^ r *
          algebraMap O (LetA O n) (g r m) =
        (a * ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r + B' * JJ1) *
          algebraMap O (LetA O n) (g r m) := by
    intro r
    obtain ⟨a, ha, B', hB', h⟩ := Formalism.MainNotions.LiftingTheory.tr_trunc_int W h9 hp2 1 (2 * A.G₀) M r le_rfl
    exact ⟨a, ha, B', hB', fun m => by rw [h]; rfl⟩
  choose a ha B' hB' heq using hdec
  set σ := A.σ PD.p with hσdef
  set sg := Formalism.NOK.sigNOK PD.p (2 * A.G₀) M 1 with hsg
  have hsgσ : sg ≤ σ := Formalism.MainNotions.UnusedSlot80.Relay2.sig_le A PD.p
  set κ := Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M with hκ
  let y : ℕ → Fin d → O := fun r m => ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g r m
  have hy : ∀ r < M, ∀ m, algebraMap O LL (y r m) = (PD.p : LL) ^ κ * sol k₀ r m := by
    intro r hr m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [y, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hyA : ∀ r m, algebraMap O (LetA O n) (y r m) =
      lA W ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * algebraMap O (LetA O n) (g r m) := by
    intro r m; simp only [y, map_mul, map_pow, map_natCast]; rfl
  let β : Fin d → W.DD T₂ := fun m => ((W.φD T₂) ^ 1) (bb m)
  have hβ : ∀ m, β m ∈ Pp W T₂ c' 1 := fun m => Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T₂ c' 1 (hbb.1.1 m)
  have hlA : lA W ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.Relay2.lA_mem W
  have hcoef : ∀ r m, lA W ^ (σ - sg) * algebraMap O (LetA O n) (g r m) * a r ∈ W.AΔ :=
    fun r m => W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hlA _) (W.AΔ.algebraMap_mem _)) (ha r)
  set lam₀ : W.DD T₂ := ∑ r ∈ Finset.range M, ∑ m,
    (lA W ^ (σ - sg) * algebraMap O (LetA O n) (g r m) * a r) • β m with hl0
  have hlam₀ : lam₀ ∈ Pp W T₂ c' 1 := by
    rw [hl0]
    exact AddSubgroup.sum_mem _ fun r _ => AddSubgroup.sum_mem _ fun m _ =>
      Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T₂ c' 1 (hcoef r m) _ (hβ m)
  set Z : W.DD T₂ := ∑ r ∈ Finset.range M, ∑ m,
    (-(lA W ^ (σ - sg) * lA W ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) *
      algebraMap O (LetA O n) (g r m) * B' r)) • β m with hZdef
  have hZ : Z ∈ Pp W T₂ c' 1 := by
    rw [hZdef]
    exact AddSubgroup.sum_mem _ fun r _ => AddSubgroup.sum_mem _ fun m _ =>
      Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T₂ c' 1 (W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem
        (W.AΔ.pow_mem hlA _) (W.AΔ.pow_mem hlA _)) (W.AΔ.algebraMap_mem _)) (hB' r))) _ (hβ m)
  set Hh : W.DD T₂ := ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T₂ bb (y r) with hHh
  have hφS : ((W.φD T₂) ^ 1) Hh = ∑ r ∈ Finset.range M, ∑ m,
      (((W.φA ^ 1) W.π₀) ^ r * algebraMap O (LetA O n) (y r m)) • β m := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hHh, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, map_pow, Formalism.MainNotions.LiftingTheory.vecB, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, ← algebraMap_smul (LetA O n) (y r m), smul_smul]
  have key : lA W ^ κ • lam₀ - lA W ^ σ • ((W.φD T₂) ^ 1) Hh = JJ1 • Z := by
    rw [hφS, hl0, hZdef, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, smul_smul, smul_smul, ← sub_smul]
    congr 1
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl (Finset.mem_range.1 hr).le
    have := ring_identity_lambda_terms (lA W) (((W.φA ^ 1) W.π₀) ^ r)
      (algebraMap O (LetA O n) (g r m)) (a r) (B' r) JJ1
      (σ - sg) sg (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) κ σ
      (by omega) (by omega) (heq r m)
    rw [hyA]
    linear_combination this
  obtain ⟨x, hx, hxe⟩ := (hbb.2 k₀).1 M κ y hy
  rw [smul_zero, sub_zero, ← hHh] at hxe
  have hγφ : ∀ (e : ℕ) (z : W.DD T₂), W.γ T₂ (((W.φD T₂) ^ e) z) = ((W.φD T₂) ^ e) (W.γ T₂ z) :=
    fun e z => Formalism.MainNotions.UnusedSlot80.Relay2.γ_φpow W T₂ W.gam e z
  have hA1 : InFP W T₂ c' 1 JJ1 (W.γ T₂ (((W.φD T₂) ^ 1) Hh) - ((W.φD T₂) ^ 1) Hh) := by
    rw [hγφ, ← map_sub, hxe]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.phij_pi0pow W T₂ c' hC.hπ hC.Tr2 1 (2 * A.G₀) M hM hx
  obtain ⟨ka, hka, -, hγπ⟩ := gamma_pi0_eq_pi0_mul_one_add_unit_mul_q W hcase hP9
  have hqA : qA W ∈ W.AΔ := W.AΔ.add_mem hC.hπ hlA
  have hγJJ : W.γA W.gam JJ1 = JJ1 * ((1 + ka * qA W) ^ M * (1 + W.π₀ * ka) ^ (2 * A.G₀)) := by
    have hq : W.γA W.gam (Formalism.MainNotions.LiftingTheory.pk W 0) = Formalism.MainNotions.LiftingTheory.pk W 0 * (1 + W.π₀ * ka) := by
      have e1 : Formalism.MainNotions.LiftingTheory.pk W 0 = W.π₀ + lA W := by simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, lA]
      have e2 : W.γA W.gam (lA W) = lA W := by simp [lA]
      rw [e1, map_add (f := _), e2, hγπ]
      simp only [qA]
      ring
    simp only [hJJ1, Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, map_mul, map_pow, hq, hγπ, mul_pow]
    ring
  have hu : (1 + ka * qA W) ^ M * (1 + W.π₀ * ka) ^ (2 * A.G₀) ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem hka hqA)) _)
      (W.AΔ.pow_mem (W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem hC.hπ hka)) _)
  have hγsm : ∀ (f : LetA O n) (z : W.DD T₂), W.γ T₂ (f • z) = W.γA W.gam f • W.γ T₂ z := by
    intro f z
    show W.γD T₂ W.gam (f • z) = W.γA W.gam f • W.γD T₂ W.gam z
    rw [← algebraMap_smul W.EE f z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have hJZ : InFP W T₂ c' 1 JJ1 (W.γ T₂ (JJ1 • Z) - JJ1 • Z) := by
    rw [hγsm, hγJJ, mul_smul, ← smul_sub]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T₂ c' 1 JJ1
      (sub_mem (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T₂ c' 1 hu _
        (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_γ W T₂ c' 1 _ hZ)) hZ)
  have hkey' : lA W ^ κ • lam₀ = lA W ^ σ • ((W.φD T₂) ^ 1) Hh + JJ1 • Z := by
    rw [← key]; abel
  have hγl : InFP W T₂ c' 1 JJ1 (lA W ^ κ • (W.γ T₂ lam₀ - lam₀)) := by
    have e : lA W ^ κ • (W.γ T₂ lam₀ - lam₀) =
        lA W ^ σ • (W.γ T₂ (((W.φD T₂) ^ 1) Hh) - ((W.φD T₂) ^ 1) Hh) +
          (W.γ T₂ (JJ1 • Z) - JJ1 • Z) := by
      rw [smul_sub, ← Formalism.MainNotions.UnusedSlot80.Relay2.γ_lsmul, hkey', map_add (f := _), Formalism.MainNotions.UnusedSlot80.Relay2.γ_lsmul,
        smul_sub]
      abel
    rw [e]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T₂ c' 1 JJ1
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_lA_pow_smul W T₂ c' 1 JJ1 σ hA1) hJZ
  have hsub : W.γ T₂ lam₀ - lam₀ ∈ Pp W T₂ c' 1 :=
    sub_mem (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_γ W T₂ c' 1 _ hlam₀) hlam₀
  obtain ⟨Y, hY, hYe⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.satP_JJ W hSatP hcase hC.hπ T₂ hT₂ c' 1 (2 * A.G₀) M _
    hsub κ hγl
  have hφ2 : ∀ z : W.DD T₂, ((W.φD T₂) ^ 2) z = ((W.φD T₂) ^ 1) (((W.φD T₂) ^ 1) z) := fun z => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_add]; rfl
  have hφP : ∀ z ∈ Pp W T₂ c' 1, ((W.φD T₂) ^ 1) z ∈ Pp W T₂ c' 2 := by
    refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T₂ c' 1 (fun z => ((W.φD T₂) ^ 1) z ∈ Pp W T₂ c' 2) ?_ ?_ ?_ ?_
    · rw [map_zero]; exact (Pp W T₂ c' 2).zero_mem
    · intro z z' hz hz'; rw [map_add (f := _)]; exact (Pp W T₂ c' 2).add_mem hz hz'
    · intro z hz; rw [map_neg]; exact (Pp W T₂ c' 2).neg_mem hz
    · intro f hf z hz
      rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, ← hφ2]
      exact Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T₂ c' 2 (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W hf 1) hz
  refine ⟨((W.φD T₂) ^ 1) lam₀, κ, Hh, ?_, ?_, ⟨y, hy, rfl⟩, 0, ?_⟩
  · exact ⟨_, hφP _ hlam₀, (one_smul _ _).symm⟩
  · refine ⟨((W.φD T₂) ^ 1) Y, hφP _ hY, ?_⟩
    rw [hγφ, ← map_sub, hYe, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, pow_one W.φA]
  · refine ⟨((W.φD T₂) ^ 1) Z, hφP _ hZ, ?_⟩
    rw [pow_zero, one_smul, hφ2, ← Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul, ← Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul,
      ← map_sub, key, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, pow_one W.φA]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeLeValuationConstantTerm
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

theorem arc_length_three_le_valuation_constant_term [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (f₂ : W.EE) (hf₂ : InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂) (κ₀ : ℕ) (X₀ : O) (hX₀ : InFr W c (ps W 0 ^ (size c + S)) (ps W 1 ^ size (c - 1))
      (lE W κ₀ * f₂ - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₀)) :
    ∀ r : ℚ, v (algebraMap O LL X₀) = ((r : ℚ) : WithTop ℚ) →
      ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c + S : ℕ) : ℝ) / PD.p - ((size c + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 - 2 -
        Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ))) + κ₀ ≤ (r : ℝ) := by
  intro r hr
  classical
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨hcr, -⟩ := hW₁
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hcr hO hinj
  obtain ⟨hl11, hSet, -, hη20, hS20, -⟩ := hB
  obtain ⟨-, -, hsz, -⟩ := hSet

  have hthick : ∀ d : ℕ, 1 ≤ d → d < 3 →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1) := by
    intro d hd1 hd3
    by_contra hnt
    have hmem : d ∈ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} :=
      ⟨hd1, hnt⟩
    have hle := Nat.sInf_le hmem
    have hlen' : (arcOf b w S η up size).len c =
        sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := rfl
    rw [hlen'] at hlen
    omega
  have ht1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    have h := hthick 2 (by norm_num) (by norm_num)
    have e2 : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
    rwa [e2] at h
  have ht0 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c := by
    have h := hthick 1 le_rfl (by norm_num)
    have e1 : c - ((1 : ℕ) : ZMod n) + 1 = c := by push_cast; ring
    rwa [e1] at h
  have hh : (arcOf b w S η up size).h = b + η + S := by
    show Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = _
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
    rw [if_pos ⟨c - 1, ht1⟩]
  have hη1 := hsz (c - 1)
  have hη0 := hsz c
  have hB1 : 1 ≤ size c + S := by omega
  have hb1 : 1 ≤ size (c - 1) := by omega
  have hB11 : size c + S ≤ 11 * size (c - 1) := by
    obtain ⟨h1, -⟩ := ht1
    obtain ⟨-, h2⟩ := ht0
    omega

  simp only [Br.ps_eq, ← Br.cst_pow] at hf₂ hX₀
  obtain ⟨U₁, U₂, hU⟩ := Br.inFr_const c hf₂ hX₀
  have hp0 : Br.P.p 0 = PowerSeries.X := rfl
  rw [hp0] at hU

  by_cases hx0 : X₀ = 0
  · rw [hx0, map_zero, AddValuation.map_zero] at hr
    exact (WithTop.top_ne_coe hr).elim
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨nn, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨vl, hvl⟩ := l_eq_unit_mul_pow hϖ Br.P.hl0
  obtain ⟨e, he⟩ : ∃ e, e = eO (O := O) PD.p := ⟨_, rfl⟩
  rw [← he] at hvl

  have hunit : ∀ y : Oˣ, v (algebraMap O LL (y : O)) = 0 := by
    intro y
    have h1 := hO y
    have h2 := hO (↑y⁻¹ : O)
    have h3 : v (algebraMap O LL (y : O)) + v (algebraMap O LL (↑y⁻¹ : O)) = 0 := by
      rw [← AddValuation.map_mul, ← _root_.map_mul, Units.mul_inv, _root_.map_one,
        AddValuation.map_one]
    exact le_antisymm (le_of_le_of_eq (le_add_of_nonneg_right h2) h3) h1
  have hϖ0 : v (algebraMap O LL ϖ) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    intro h
    exact hϖ.ne_zero (hinj (by rw [h, _root_.map_zero]))
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hϖ0
  have hvl1 : (((e : ℚ) * d : ℚ) : WithTop ℚ) = 1 := by
    have h := W.v_l
    rw [← map_natCast (algebraMap O LL), hvl, _root_.map_mul, _root_.map_pow,
      AddValuation.map_mul, AddValuation.map_pow, hunit, ← hd, zero_add] at h
    rw [← h, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hEd : (e : ℚ) * d = 1 := by exact_mod_cast hvl1
  have hrv : (r : ℚ) = nn * d := by
    have h := hr
    rw [hxu, _root_.map_mul, _root_.map_pow, AddValuation.map_mul, AddValuation.map_pow, hunit,
      ← hd, zero_add, ← WithTop.coe_nsmul, nsmul_eq_mul] at h
    exact_mod_cast h.symm

  obtain ⟨k₃, hk₃⟩ : ∃ k : ℕ, k = ⌈(e : ℝ) * (((size (c - 2) + S : ℕ) : ℝ) -
      ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) ^ 2)⌉₊ := ⟨_, rfl⟩
  have hc3 := Br.P.c3a hϖ (size (c - 2) + S) (size c + S) hB1 k₃ (by rw [← he]; exact hk₃.le)
  obtain ⟨α₁, β₁, hαβ⟩ := Ideal.mem_span_pair.mp hc3
  have hF1 : (e : ℝ) * (((size (c - 2) + S : ℕ) : ℝ) -
      ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) ^ 2) ≤ k₃ := by
    rw [hk₃]; exact Nat.le_ceil _

  have hc2 := Br.P.constant_le_rpow_of_three_le hϖ (size c + S) (size (c - 1)) hB1 hb1
  rw [← he] at hc2
  have hL : (11 : ℝ) ≤ ((PD.p : ℕ) : ℝ) := by exact_mod_cast hl11
  have hL1 : (1 : ℝ) < ((PD.p : ℕ) : ℝ) := by linarith
  have hy1 : (1 : ℝ) ≤ ((size (c - 1) : ℕ) : ℝ) := by exact_mod_cast hb1
  have hBl : ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) ≤ ((size (c - 1) : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    have : ((size c + S : ℕ) : ℝ) ≤ 11 * ((size (c - 1) : ℕ) : ℝ) := by exact_mod_cast hB11
    nlinarith
  have hlog0 : 0 ≤ Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ) := Real.logb_nonneg hL1 hy1
  have hbr : 0 ≤ ((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) + 2 +
      Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ) := by linarith
  rw [max_eq_right hbr] at hc2
  have hE0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hF2 : ((e * κ₀ + k₃ : ℕ) : ℝ) - nn ≤ (e : ℝ) * (((size (c - 1) : ℕ) : ℝ) -
      ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) + 2 +
      Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ)) := by
    by_cases hlt : nn < e * κ₀ + k₃
    · obtain ⟨m, hm⟩ : ∃ m, e * κ₀ + k₃ = nn + m := ⟨e * κ₀ + k₃ - nn, by omega⟩
      have hpw : (PowerSeries.C ϖ) ^ (e * κ₀) * (PowerSeries.C ϖ) ^ k₃ =
          (PowerSeries.C ϖ) ^ nn * (PowerSeries.C ϖ) ^ m := by
        rw [← pow_add, ← pow_add, hm]
      rw [hvl, hxu, _root_.map_mul, _root_.map_mul, _root_.map_pow, _root_.map_pow, mul_pow,
        ← pow_mul, ← hαβ] at hU
      have hdist := (ContPA.dist_X_pow (O := O) (size c + S)).1
      have hdvd := ContM_cancel_unif hϖ hdist nn
        (x := PowerSeries.C (u : O) * Br.P.p 1 ^ size (c - 1) -
          (PowerSeries.C ϖ) ^ m * (PowerSeries.C (vl : O) ^ κ₀ * α₁ * U₁))
        (a := PowerSeries.C (vl : O) ^ κ₀ * (PowerSeries.C ϖ) ^ (e * κ₀) * β₁ * U₁ - U₂)
        (by linear_combination hU + PowerSeries.C (vl : O) ^ κ₀ * α₁ * U₁ * hpw)
      obtain ⟨γ, hγ⟩ := hdvd
      have hu1 : PowerSeries.C (↑u⁻¹ : O) * PowerSeries.C (u : O) = 1 := by
        rw [← _root_.map_mul, Units.inv_mul, _root_.map_one]
      have hmem : Br.P.p 1 ^ size (c - 1) ∈
          Ideal.span {PowerSeries.C ϖ ^ m, (PowerSeries.X : PowerSeries O) ^ (size c + S)} := by
        refine Ideal.mem_span_pair.mpr ⟨PowerSeries.C (↑u⁻¹ : O) *
          (PowerSeries.C (vl : O) ^ κ₀ * α₁ * U₁), PowerSeries.C (↑u⁻¹ : O) * γ, ?_⟩
        linear_combination (-PowerSeries.C (↑u⁻¹ : O)) * hγ + Br.P.p 1 ^ size (c - 1) * hu1
      have hcont := (Cont.mem_iff_le ϖ _ _ m).mp hmem
      rw [← ENat.natCast_toNat hc2.1] at hcont
      have hmle : (m : ℝ) ≤
          ((cont ϖ (PowerSeries.X ^ (size c + S)) (Br.P.p 1 ^ size (c - 1))).toNat : ℝ) := by
        exact_mod_cast hcont
      have : ((e * κ₀ + k₃ : ℕ) : ℝ) - nn = m := by rw [hm]; push_cast; ring
      rw [this]
      exact hmle.trans hc2.2
    · have : ((e * κ₀ + k₃ : ℕ) : ℝ) - nn ≤ 0 := by
        have : e * κ₀ + k₃ ≤ nn := by omega
        have : ((e * κ₀ + k₃ : ℕ) : ℝ) ≤ nn := by exact_mod_cast this
        linarith
      exact this.trans (mul_nonneg hE0 hbr)

  rw [hh]
  have hlog : Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ) ≤
      Real.logb ((PD.p : ℕ) : ℝ) (2 * ((b + η + S : ℕ) : ℝ)) := by
    have h2h : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ b + η + S by obtain ⟨-, h2⟩ := ht1; omega)
    apply (Real.logb_le_logb hL1 (by linarith) (by linarith)).mpr
    obtain ⟨-, h2⟩ := ht1
    have : size (c - 1) ≤ 2 * (b + η + S) := by omega
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_left hlog hE0
  have hEd' : (e : ℝ) * (d : ℝ) = 1 := by exact_mod_cast hEd
  have hrv' : ((r : ℚ) : ℝ) = (nn : ℝ) * (d : ℝ) := by exact_mod_cast hrv
  have hd0 : (0 : ℝ) < d := by
    rcases lt_or_ge 0 (d : ℝ) with h | h
    · exact h
    · nlinarith
  push_cast at hF1 hF2 h3 ⊢
  have hmain : (e : ℝ) * ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c : ℝ) + S) / PD.p -
      ((size c : ℝ) + S) / (PD.p : ℝ) ^ 2 - 2 - Real.logb PD.p (2 * ((b : ℝ) + η + S)) + κ₀) ≤ nn := by
    linear_combination hF1 + hF2 + h3
  rw [hrv']
  calc _ = ((e : ℝ) * ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c : ℝ) + S) / PD.p -
      ((size c : ℝ) + S) / (PD.p : ℝ) ^ 2 - 2 - Real.logb PD.p (2 * ((b : ℝ) + η + S)) + κ₀)) * d := by
        rw [mul_comm (e : ℝ), mul_assoc, hEd', mul_one]
    _ ≤ (nn : ℝ) * d := mul_le_mul_of_nonneg_right hmain hd0.le

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

theorem arc_length_three_exists_liftsAt_scalar_mul [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (f₂ : W.EE) (hf₂ : InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂)
    (hf₂0 : ∃ (κ : ℕ) (X₀ : O), InFr W c (ps W 0 ^ (size c + S)) (ps W 1 ^ size (c - 1))
      (lE W κ * f₂ - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₀)) :
    ∃ (e : ℕ) (t₃ : O), (e : ℝ) ≤ 6 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
      (∃ r : ℚ, v (algebraMap O LL t₃) = ((r : ℚ) : WithTop ℚ) ∧ (r : ℝ) ≤ 14 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size) ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ (algebraMap O W.EE t₃ * f₂) e := by
  obtain ⟨κ₀, X₀, hX₀⟩ := hf₂0
  have hx0 := arc_length_three_le_valuation_constant_term W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy f₂ hf₂ κ₀ X₀ hX₀
  obtain ⟨lam, κ, Hh, hlam, hlamγ, hHh, h4a⟩ := arc_length_three_exists_lambda_near_horizontal W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy
  obtain ⟨n₁, E, hn₁, hE, hmap⟩ := arc_length_three_first_level W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy lam hlam hlamγ κ Hh hHh h4a
  obtain ⟨y₁, σ₁, hy₁⟩ := arc_length_three_first_lift W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy lam hlam hlamγ κ Hh hHh h4a n₁ E hn₁ hmap
  exact arc_length_three_final_bound W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy f₂ hf₂ κ₀ X₀ hX₀ hx0 lam hlam hlamγ κ Hh hHh h4a n₁ E hn₁ hmap hE y₁ σ₁ hy₁

end Formalism.MainNotions.N.FrobeniusPowerSeries
