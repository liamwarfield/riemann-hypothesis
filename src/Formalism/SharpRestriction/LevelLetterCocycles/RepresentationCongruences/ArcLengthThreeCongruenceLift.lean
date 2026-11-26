module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
public import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPowSmulEqPiPowSmulOfTwistSub
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYCA

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem sum_split {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (π : R) (f : ℕ → M)
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ r ∈ Finset.range N, π ^ r • f r = π • ∑ r ∈ Finset.range (N - 1), π ^ r • f (r + 1) + f 0 := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ', Nat.add_sub_cancel, Finset.smul_sum, pow_zero, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pow_succ, mul_comm, mul_smul]

section Gen
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

theorem g_step (L π g h a : R) (k k₂ r m : ℕ) (E γE x x' z : M)
    (hkx : L ^ k • (g • E) = π ^ r • x)
    (hzE : L ^ k₂ • (g • (γE - E)) = (π ^ r * π * π ^ m) • z)
    (h1x : L ^ k • ((g * (1 + π * h)) • γE) - π ^ r • x = a • (π ^ r • x) + π ^ (r + 1) • x') :
    π ^ r • (L ^ k₂ • (a • x) - π • (L ^ k₂ • (h • x) + L ^ k • ((1 + π * h) • (π ^ m • z)) -
      L ^ k₂ • x')) = 0 := by
  linear_combination (norm := module) (-(L ^ k₂)) • h1x + (L ^ k * (1 + π * h)) • hzE +
    (L ^ k₂ * (1 + π * h)) • hkx

theorem g_fin (L π g ε a : R) (k k₂ r : ℕ) (E x y : M) (hkx : L ^ k • (g • E) = π ^ r • x)
    (h4 : L ^ k₂ • (a • x) = π • y) :
    (L ^ (k + k₂) * (ε * a)) • (g • E) = π ^ (r + 1) • (ε • y) := by
  linear_combination (norm := module) (L ^ k₂ * ε * a) • hkx + (π ^ r * ε) • h4

theorem g_A (L π q P2 p1 aJ t : R) (κ' b1 κ κ₁ E σ e : ℕ) (FX FX' FD Fn Fz lam φHh y4 : M)
    (E1 : FX = π • FX' + L ^ κ₁ • FD) (E2 : Fn = FD + π • Fz)
    (E3 : q ^ b1 • Fn = L ^ E • (p1 ^ e • lam))
    (E4 : L ^ κ' • (L ^ κ • lam - L ^ σ • φHh) = (π * aJ) • y4)
    (ht : L ^ b1 * p1 ^ e - L ^ e * q ^ b1 = π * t) :
    L ^ κ' • ((q ^ b1 * P2) • (L ^ (b1 + κ) • FX - L ^ (κ₁ + E + σ + e) • φHh)) =
      π • ((L ^ (κ₁ + E) * L ^ b1 * p1 ^ e * aJ) • (P2 • y4) +
        (L ^ (κ' + b1 + κ) * (q ^ b1 * P2)) • (FX' - L ^ κ₁ • Fz) +
        (L ^ (κ₁ + E + κ' + σ) * t) • (P2 • φHh)) := by
  have key : L ^ κ' • ((q ^ b1 * P2) • (L ^ (b1 + κ) • FX - L ^ (κ₁ + E + σ + e) • φHh)) =
      π • ((L ^ (κ₁ + E) * L ^ b1 * p1 ^ e * aJ) • (P2 • y4) +
        (L ^ (κ' + b1 + κ) * (q ^ b1 * P2)) • (FX' - L ^ κ₁ • Fz)) +
      (L ^ (κ₁ + E + κ' + σ) * (L ^ b1 * p1 ^ e - L ^ e * q ^ b1)) • (P2 • φHh) := by
    linear_combination (norm := module) (L ^ κ' * (q ^ b1 * P2) * L ^ (b1 + κ)) • E1 -
    (L ^ κ' * (q ^ b1 * P2) * L ^ (b1 + κ + κ₁)) • E2 + (L ^ κ' * P2 * L ^ (b1 + κ + κ₁)) • E3 +
    (P2 * L ^ (b1 + κ₁ + E) * p1 ^ e) • E4
  rw [key, ht]
  module

theorem g_B (L π q P2 u3 Pk : R) (b1 κ c Rr R' M' : ℕ) (FX γFX Fx φHh γφHh φxH : M)
    (B1 : γFX - FX = (π ^ Rr * π ^ R') • Fx)
    (B2 : γφHh - φHh = (u3 * (π ^ Rr * π ^ M') * Pk) • φxH) :
    (q ^ b1 * P2) • (L ^ (b1 + κ) • γFX - L ^ c • γφHh - (L ^ (b1 + κ) • FX - L ^ c • φHh)) =
      π ^ Rr • ((L ^ (b1 + κ) * π ^ R' * (q ^ b1 * P2)) • Fx -
        (L ^ c * u3 * π ^ M' * Pk * q ^ b1) • (P2 • φxH)) := by
  linear_combination (norm := module) (q ^ b1 * P2 * L ^ (b1 + κ)) • B1 - (q ^ b1 * P2 * L ^ c) • B2

theorem g_K (L g π qB : R) (kU κ₁ b1 κ σ₁ E σ e₁ e₂ : ℕ) (Fy FZ φFX φφHh φV : M)
    (hrelF : L ^ κ₁ • Fy + (π * qB) • FZ = L ^ σ₁ • φFX)
    (hφV : φV = L ^ (b1 + κ) • φFX - L ^ (κ₁ + E + σ + (e₁ + e₂)) • φφHh) :
    L ^ (kU + κ₁) • g • (L ^ (b1 + κ) • Fy - L ^ (σ₁ + E + σ + e₁ + e₂) • φφHh) =
      L ^ σ₁ • (L ^ kU • (g • φV)) - (L ^ (kU + b1 + κ) * g * π) • (qB • FZ) := by
  rw [hφV]
  linear_combination (norm := module) (L ^ (kU + b1 + κ) * g) • hrelF

end Gen

variable (W : LocWach PD LL O v n)

theorem γ_mul_form {g g' h h' : LetA O n} (hg : W.γA W.gam g = g * (1 + W.π₀ * h))
    (hg' : W.γA W.gam g' = g' * (1 + W.π₀ * h')) :
    W.γA W.gam (g * g') = g * g' * (1 + W.π₀ * (h + h' + W.π₀ * h * h')) := by
  rw [map_mul, hg, hg']; ring

theorem γ_pow_form {g h : LetA O n} (hh : h ∈ W.AΔ) (hπ : W.π₀ ∈ W.AΔ)
    (hg : W.γA W.gam g = g * (1 + W.π₀ * h)) (k : ℕ) :
    ∃ h' ∈ W.AΔ, W.γA W.gam (g ^ k) = g ^ k * (1 + W.π₀ * h') := by
  induction k with
  | zero => exact ⟨0, W.AΔ.zero_mem, by simp⟩
  | succ k ih =>
    obtain ⟨h', hh', e⟩ := ih
    refine ⟨h' + h + W.π₀ * h' * h, ?_, ?_⟩
    · exact W.AΔ.add_mem (W.AΔ.add_mem hh' hh) (W.AΔ.mul_mem (W.AΔ.mul_mem hπ hh') hh)
    · rw [pow_succ, γ_mul_form W e hg]

theorem exists_pow_smul_eq_pi_pow_smul_of_twist_sub (T : LocLat G Qp LL O) (hC : Formalism.MainNotions.UnusedSlot80.Relay2.Ctx W T) (c : ZMod n)
    (g₀ h : LetA O n) (hh : h ∈ W.AΔ)
    (hγg : W.γA W.gam g₀ = g₀ * (1 + W.π₀ * h)) (R : ℕ) (E : W.DD T)
    (hE : ∃ (k : ℕ) (E' : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c E' ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ • E')
    (hγ : ∃ (k : ℕ) (z : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c z ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • (W.γ T E - E)) = W.π₀ ^ R • z) :
    ∃ (k : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ ^ R • x := by
  obtain ⟨k₂, z, hz, hzE⟩ := hγ
  have hπ : W.π₀ ∈ W.AΔ := hC.hπ
  have key : ∀ r, 1 ≤ r → r ≤ R → ∃ (k : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ ^ r • x := by
    intro r hr1
    induction r with
    | zero => omega
    | succ r ih =>
      intro hrR
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0
        obtain ⟨k, E', hE', hk⟩ := hE
        exact ⟨k, E', hE', by rw [hk, zero_add, pow_one]⟩
      obtain ⟨k, x, hx, hkx⟩ := ih hpos (by omega)
      obtain ⟨x', hx', h1x⟩ := hC.H1 c r x hx
      obtain ⟨e, he⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.principal_unit_pow_sub_one_dvd W hC.inj hC.O2 r (hC.H2 r hpos)
      set a : LetA O n := algebraMap O (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1) with ha
      rw [← algebraMap_smul (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1), ← ha] at h1x
      have hγx : W.γ T (W.π₀ ^ r • x) =
          Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • ((g₀ * (1 + W.π₀ * h)) • W.γ T E) := by
        rw [← hkx, Formalism.MainNotions.UnusedSlot80.Relay2.γ_lsmul, ← hγg]
        congr 1
        exact Formalism.MainNotions.LiftingTheory.frame_γD_smul W T W.gam g₀ E
      rw [hγx] at h1x
      have hR : W.π₀ ^ R = W.π₀ ^ r * W.π₀ * W.π₀ ^ (R - (r + 1)) := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hR] at hzE
      obtain ⟨y, hy⟩ : ∃ y : W.DD T, y = Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • (h • x) +
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • ((1 + W.π₀ * h) • (W.π₀ ^ (R - (r + 1)) • z)) -
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • x' := ⟨_, rfl⟩
      have h3 : W.π₀ ^ r • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • (a • x) - W.π₀ • y) = 0 := by
        rw [hy]; exact g_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ hkx hzE h1x
      have h4 := Formalism.MainNotions.LiftingTheory.frame_π₀_inj W T hC.hw r _ h3
      rw [sub_eq_zero] at h4
      have h1h : (1 + W.π₀ * h) ∈ W.AΔ := W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem hπ hh)
      have hyN : Formalism.MainNotions.LiftingTheory.InNΔi W T c y := by
        rw [hy]
        refine Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W T c (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_add W T c ?_ ?_)
          (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ hx')
        · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c hh hx)
        · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c h1h
            (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (W.AΔ.pow_mem hπ _) hz))
      obtain ⟨ε, hε⟩ : ∃ ε : LetA O n, ε = algebraMap O (LetA O n) e := ⟨_, rfl⟩
      have he' : ε * a = Formalism.MainNotions.ArcLiftingSetup.lA W ^ (1 + padicValNat PD.p r) := by
        rw [hε, ha, ← map_mul, he, map_pow, map_natCast]; rfl
      refine ⟨k + k₂ + (1 + padicValNat PD.p r), ε • y,
        Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (by rw [hε]; exact W.AΔ.algebraMap_mem e) hyN, ?_⟩
      rw [pow_add, ← he']
      exact g_fin _ _ _ _ _ _ _ _ _ _ _ hkx h4
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0
    obtain ⟨k, E', hE', hk⟩ := hE
    exact ⟨k, W.π₀ • E', Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c hπ hE', by rw [hk, pow_zero, one_smul]⟩
  · exact key R hpos le_rfl

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYCA
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

theorem arc_length_three_congruence_lift [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (n₁ : W.DD T₁) (E : ℕ) (hn₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) n₁)
    (hmap : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) ∧ W.map F n₁ = (((PD.p : ℕ) : LetA O n) ^ E) • (s • lam))
    (d : ℕ) (b₁ : Fin d → W.DD T₁) (sol₁ : Fin d → ℕ → Fin d → LL) (c₀ : Fin d → O) (z₁ : W.DD T₁)
    (R₀ σ₁ κ₁ : ℕ) (yy : ℕ → Fin d → O) (X₁ x₁ y₁ Z : W.DD T₁)
    (hb₁ : IsHor W T₁ (c - 1) b₁ sol₁)
    (hz₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) z₁) (hn₁c : n₁ = Formalism.MainNotions.LiftingTheory.vecB W T₁ b₁ c₀ + W.π₀ • z₁)
    (hR₀ : size c + S ≤ (PD.p - 1) * R₀) (hR₁ : 1 ≤ R₀)
    (hyy : ∀ r < R₀, ∀ m, algebraMap O LL (yy r m) = (PD.p : LL) ^ κ₁ * ∑ k, algebraMap O LL (c₀ k) * sol₁ k r m)
    (hX₁e : X₁ = ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T₁ b₁ (yy r))
    (hX₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) X₁) (hx₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x₁)
    (hγX : W.γ T₁ X₁ - X₁ = W.π₀ ^ R₀ • x₁) (hy₁ : InFP W T₁ (c - 1) 1 1 y₁) (hZ : InFP W T₁ (c - 1) 1 1 Z)
    (hrel : lA W ^ κ₁ • y₁ + (W.π₀ * qA W ^ (size c + S)) • Z = lA W ^ σ₁ • W.φD T₁ X₁) :
      ∃ g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}, ∃ κ' : ℕ,
        InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) (lA W ^ κ' • g • (lA W ^ (size (c - 1) + κ) • W.map F y₁ -
          lA W ^ (σ₁ + E + (arcOf b w S η up size).σ PD.p + size (c - 2) + S) • ((W.φD T₂) ^ 3) Hh)) := by
  set A := arcOf b w S η up size with hA
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  set MA := A.M PD.p with hMA
  set σA := A.σ PD.p with hσA
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hT₂ : IsCrys PD T₂.ρ := hW₂.1
  have hC := Formalism.MainNotions.UnusedSlot80.Relay2.ctx_of W hinj hOv hP9 hH hTr hcase T₂ hT₂
  have hπ : W.π₀ ∈ W.AΔ := hC.hπ
  have hlA : lA W ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.Relay2.lA_mem W
  have hqA : qA W ∈ W.AΔ := W.AΔ.add_mem hπ hlA
  have hps : ∀ s, ps W s ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hπ
  have hpk : ∀ k, Formalism.MainNotions.LiftingTheory.pk W k ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.Relay2.pk_mem_AΔ W hπ
  have hc'2 : c' + ((2 : ℕ) : ZMod n) = c - 1 := by rw [hc', hlen]; push_cast; ring

  have hR9 := (Formalism.MainNotions.LiftingTheory.frame_p9A W hP9 hcase T₂ hT₂).1
  have h5 := hP5 T₂ _ _ hT₂ (Formalism.MainNotions.UnusedSlot80.PhiPowers.jumpsLet_of_win W A hOK T₂ hW₂)
  obtain ⟨Gb, hGb⟩ : ∃ Gb : ℕ, Gb = Formalism.MainNotions.UnusedSlot80.PhiPowers.Mw A.G₀ A.S A.η (A.ty (c' + ((1 : ℕ) : ZMod n))) +
      Formalism.MainNotions.UnusedSlot80.PhiPowers.Mw A.G₀ A.S A.η (A.ty (c' + ((2 : ℕ) : ZMod n))) := ⟨_, rfl⟩
  have hMb : ∀ k : ℕ, 1 ≤ k → k ≤ 2 →
      (fun i => Formalism.MainNotions.UnusedSlot80.PhiPowers.Mw A.G₀ A.S A.η (A.ty i)) (c' + (k : ZMod n)) ≤ Gb := by
    intro k h1 h2
    rw [hGb]
    rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left _ _
  obtain ⟨P2, hP2e⟩ : ∃ P2 : LetA O n, P2 = ∏ s ∈ Finset.range 2, ps W s ^ Gb := ⟨_, rfl⟩
  have hP2 : P2 ∈ W.AΔ := by rw [hP2e]; exact W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (hps s) _
  have hP2' : P2 = qA W ^ Gb * ps W 1 ^ Gb := by
    rw [hP2e, Finset.prod_range_succ, Finset.prod_range_one]
    simp only [ps, pow_zero, pow_one, AlgHom.one_apply]
  have hcont : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c' x →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (P2 • ((W.φD T₂) ^ 2) x) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Formalism.MainNotions.UnusedSlot80.PhiPowers.prodPs_mem W hcase.2.1 hR9 T₂ h5 c' Gb 2 hMb x hx
    rw [hc'2, ← hP2e] at h2
    rw [← hP2e] at h1
    exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_of W T₂ (c - 1) h1 h2
  have hcontP : ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T₂ c' 2, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (P2 • y) := by
    refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T₂ c' 2 (fun y => Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (P2 • y))
      ?_ ?_ ?_ ?_
    · simpa using Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_zero W T₂ (c - 1)
    · intro x y hx hy
      rw [smul_add]; exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_add W T₂ _ hx hy
    · intro x hx
      rw [smul_neg, ← neg_one_smul O (P2 • x)]
      exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_osmul W T₂ _ _ hx
    · intro a ha x hx
      rw [smul_comm]
      exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T₂ _ ha (hcont x hx)

  have hvecN : ∀ {T : LocLat G Qp LL O} {i : ZMod n} {dd : ℕ} (bq : Fin dd → W.DD T),
      (∀ m, Formalism.MainNotions.LiftingTheory.InNΔi W T i (bq m)) → ∀ y : Fin dd → O,
        Formalism.MainNotions.LiftingTheory.InNΔi W T i (Formalism.MainNotions.LiftingTheory.vecB W T bq y) := by
    intro T i dd bq hbq y
    exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W T i _ _ fun m _ =>
      Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_osmul W T i _ (hbq m)
  obtain ⟨yH, hyH, hHe⟩ := hHh
  have hHN : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c' Hh := by
    rw [hHe]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W T₂ c' _ _ fun r _ =>
      Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T₂ c' (W.AΔ.pow_mem hπ r) (hvecN bb hbb.1.1 (yH r))
  obtain ⟨xH, hxH, hxHe⟩ := (hbb.2 k₀).1 MA κ yH hyH
  rw [← hHe, smul_zero, sub_zero] at hxHe

  have hs0 : ∀ k, sol₁ k 0 = Pi.single k 1 := fun k => (hb₁.2 k).2
  have hyy0 : yy 0 = fun m => ((PD.p : ℕ) : O) ^ κ₁ * c₀ m := by
    funext m
    apply hinj
    rw [hyy 0 hR₁ m, map_mul, map_pow, map_natCast]
    congr 1
    simp [hs0, Pi.single_apply]
  obtain ⟨D₁, hD₁⟩ : ∃ D₁, D₁ = Formalism.MainNotions.LiftingTheory.vecB W T₁ b₁ c₀ := ⟨_, rfl⟩
  obtain ⟨X₁', hX₁'⟩ : ∃ X', X' = ∑ r ∈ Finset.range (R₀ - 1),
      W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T₁ b₁ (yy (r + 1)) := ⟨_, rfl⟩
  have hX₁d : X₁ = W.π₀ • X₁' + lA W ^ κ₁ • D₁ := by
    rw [hX₁e, DYCA.sum_split W.π₀ _ R₀ hR₁, hX₁', hD₁, hyy0, ← Formalism.MainNotions.UnusedSlot80.Relay2.lsmul_eq W T₁]
    simp only [Formalism.MainNotions.LiftingTheory.vecB, Finset.smul_sum, mul_smul]
  have hX₁'N : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) X₁' := by
    rw [hX₁']
    exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W T₁ (c - 1) _ _ fun r _ =>
      Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T₁ _ (W.AΔ.pow_mem hπ r) (hvecN b₁ hb₁.1.1 _)
  have E1 : W.map F X₁ = W.π₀ • W.map F X₁' + lA W ^ κ₁ • W.map F D₁ := by
    rw [hX₁d, map_add (f := _), Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul W F, Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul W F]
  have E2 : W.map F n₁ = W.map F D₁ + W.π₀ • W.map F z₁ := by
    rw [hn₁c, ← hD₁, map_add (f := _), Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul W F]

  obtain ⟨uq, huq⟩ := (lemG_units W hcase hP9 hT₂ hO hOv hinj).2.1
  obtain ⟨sE, hsE⟩ : ∃ sE : W.EE, sE = (↑uq⁻¹ : W.EE) ^ size (c - 1) *
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) := ⟨_, rfl⟩
  have hsq : algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * sE =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) := by
    rw [hsE, map_pow (algebraMap (LetA O n) W.EE) (qA W), ← huq, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  have E3 : qA W ^ size (c - 1) • W.map F n₁ = lA W ^ E • (ps W 1 ^ (size (c - 2) + S) • lam) := by
    rw [(hmap sE hsq).2, smul_comm (qA W ^ size (c - 1)) (((PD.p : ℕ) : LetA O n) ^ E) (sE • lam),
      ← algebraMap_smul W.EE (qA W ^ size (c - 1)) (sE • lam), smul_smul, hsq, algebraMap_smul]
    rfl

  obtain ⟨κ', y4, hy4, h4e⟩ := h4a
  have hM1 : 1 ≤ MA := Formalism.MainNotions.UnusedSlot80.Relay2.M_pos A PD.p
  obtain ⟨u1, hu1, -, -, -, hT1⟩ := hC.Tr2 1 MA
  simp only [pow_one, Finset.prod_range_one] at hT1
  obtain ⟨aJ, haJe⟩ : ∃ aJ : LetA O n, aJ = u1 * W.π₀ ^ (MA - 1) *
      Formalism.MainNotions.LiftingTheory.pk W 0 ^ ((PD.p - 1) * MA) * W.φA (Formalism.MainNotions.LiftingTheory.pk W 0) ^ (2 * A.G₀) := ⟨_, rfl⟩
  have haJ : aJ ∈ W.AΔ := by
    rw [haJe]
    exact W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hu1 (W.AΔ.pow_mem hπ _)) (W.AΔ.pow_mem (hpk 0) _))
      (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_mem_AΔ W (hpk 0)) _)
  have hφJJ : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) MA) = W.π₀ * aJ := by
    rw [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, map_mul, map_pow, map_pow, hT1, haJe]
    have e0 : W.π₀ ^ MA = W.π₀ * W.π₀ ^ (MA - 1) := by rw [← pow_succ']; congr 1 <;> omega
    rw [e0]; ring
  rw [hφJJ] at h4e

  obtain ⟨u2, hu2, -, -, -, hT2⟩ := hC.Tr2 1 1
  simp only [pow_one, Finset.prod_range_one, mul_one] at hT2
  have hql : qA W - lA W = W.π₀ := by simp [qA]
  have hp1l : ps W 1 - lA W = W.π₀ * (u2 * Formalism.MainNotions.LiftingTheory.pk W 0 ^ (PD.p - 1)) := by
    have e0 : ps W 1 = W.φA W.π₀ + lA W := by simp only [ps, pow_one, qA, map_add (f := _), lA, map_natCast]
    rw [e0, hT2]; ring
  have g1 := geom_sum₂_mul (ps W 1) (lA W) (size (c - 2) + S)
  have g2 := geom_sum₂_mul (qA W) (lA W) (size (c - 1))
  rw [hp1l] at g1
  rw [hql] at g2
  obtain ⟨t, ht⟩ : ∃ t : LetA O n, t = lA W ^ size (c - 1) *
      (∑ i ∈ Finset.range (size (c - 2) + S), ps W 1 ^ i * lA W ^ (size (c - 2) + S - 1 - i)) *
        (u2 * Formalism.MainNotions.LiftingTheory.pk W 0 ^ (PD.p - 1)) -
      lA W ^ (size (c - 2) + S) *
        (∑ i ∈ Finset.range (size (c - 1)), qA W ^ i * lA W ^ (size (c - 1) - 1 - i)) := ⟨_, rfl⟩
  have htE : lA W ^ size (c - 1) * ps W 1 ^ (size (c - 2) + S) -
      lA W ^ (size (c - 2) + S) * qA W ^ size (c - 1) = W.π₀ * t := by
    rw [ht]
    linear_combination (-(lA W ^ size (c - 1))) * g1 + (lA W ^ (size (c - 2) + S)) * g2
  have htA : t ∈ W.AΔ := by
    rw [ht]
    refine W.AΔ.sub_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hlA _) ?_)
      (W.AΔ.mul_mem hu2 (W.AΔ.pow_mem (hpk 0) _))) (W.AΔ.mul_mem (W.AΔ.pow_mem hlA _) ?_)
    · exact W.AΔ.sum_mem fun i _ => W.AΔ.mul_mem (W.AΔ.pow_mem (hps 1) _) (W.AΔ.pow_mem hlA _)
    · exact W.AΔ.sum_mem fun i _ => W.AΔ.mul_mem (W.AΔ.pow_mem hqA _) (W.AΔ.pow_mem hlA _)

  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : LetA O n, g₀ = qA W ^ size (c - 1) * P2 := ⟨_, rfl⟩
  have hg₀A : g₀ ∈ W.AΔ := by rw [hg₀]; exact W.AΔ.mul_mem (W.AΔ.pow_mem hqA _) hP2
  obtain ⟨V, hV⟩ : ∃ V : W.DD T₂, V = lA W ^ (size (c - 1) + κ) • W.map F X₁ -
      lA W ^ (κ₁ + E + σA + (size (c - 2) + S)) • ((W.φD T₂) ^ 2) Hh := ⟨_, rfl⟩
  have hEA := DYCA.g_A (lA W) W.π₀ (qA W) P2 (ps W 1) aJ t κ' (size (c - 1)) κ κ₁ E σA
    (size (c - 2) + S) _ _ _ _ _ _ _ _ E1 E2 E3 h4e htE
  rw [← hg₀, ← hV] at hEA
  have hmemA : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1)
      ((lA W ^ (κ₁ + E) * lA W ^ size (c - 1) * ps W 1 ^ (size (c - 2) + S) * aJ) • (P2 • y4) +
        (lA W ^ (κ' + size (c - 1) + κ) * g₀) • (W.map F X₁' - lA W ^ κ₁ • W.map F z₁) +
        (lA W ^ (κ₁ + E + κ' + σA) * t) • (P2 • ((W.φD T₂) ^ 2) Hh)) := by
    refine Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_add W T₂ _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_add W T₂ _ ?_ ?_) ?_
    · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T₂ _ (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem
        (W.AΔ.pow_mem hlA _) (W.AΔ.pow_mem hlA _)) (W.AΔ.pow_mem (hps 1) _)) haJ) (hcontP y4 hy4)
    · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T₂ _ (W.AΔ.mul_mem (W.AΔ.pow_mem hlA _) hg₀A)
        (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W T₂ _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W F hW₁.1 hW₂.1 _ hX₁'N)
          (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T₂ _ _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W F hW₁.1 hW₂.1 _ hz₁)))
    · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T₂ _ (W.AΔ.mul_mem (W.AΔ.pow_mem hlA _) htA)
        (hcont Hh hHN)

  obtain ⟨R, hRdef⟩ : ∃ R, R = min R₀ MA := ⟨_, rfl⟩
  have hRR₀ : R ≤ R₀ := by rw [hRdef]; exact min_le_left _ _
  have hRM : R ≤ MA := by rw [hRdef]; exact min_le_right _ _
  obtain ⟨u3, hu3, -, -, -, hT3⟩ := hC.Tr2 2 MA
  have B1 : W.γ T₂ (W.map F X₁) - W.map F X₁ = W.π₀ ^ R₀ • W.map F x₁ := by
    have e0 := W.map_γ F W.gam X₁
    rw [show W.γ T₂ (W.map F X₁) = W.γD T₂ W.gam (W.map F X₁) from rfl, ← e0, ← map_sub,
      show W.γD T₁ W.gam X₁ - X₁ = W.γ T₁ X₁ - X₁ from rfl, hγX, Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul W F]
  have B2 : W.γ T₂ (((W.φD T₂) ^ 2) Hh) - ((W.φD T₂) ^ 2) Hh =
      (u3 * W.π₀ ^ MA * ∏ k ∈ Finset.range 2, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * MA)) •
        ((W.φD T₂) ^ 2) xH := by
    rw [show W.γ T₂ (((W.φD T₂) ^ 2) Hh) = W.γD T₂ W.gam (((W.φD T₂) ^ 2) Hh) from rfl,
      Formalism.MainNotions.UnusedSlot80.Relay2.γ_φpow, ← map_sub,
      show W.γD T₂ W.gam Hh - Hh = W.γ T₂ Hh - Hh from rfl, hxHe,
      Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, map_pow, hT3]
  have e1 : W.π₀ ^ R₀ = W.π₀ ^ R * W.π₀ ^ (R₀ - R) := by rw [← pow_add]; congr 1 <;> omega
  have e2 : W.π₀ ^ MA = W.π₀ ^ R * W.π₀ ^ (MA - R) := by rw [← pow_add]; congr 1 <;> omega
  rw [e1] at B1
  rw [e2] at B2
  have hBeq : lA W ^ 0 • (g₀ • (W.γ T₂ V - V)) = W.π₀ ^ R •
      ((lA W ^ (size (c - 1) + κ) * W.π₀ ^ (R₀ - R) * g₀) • W.map F x₁ -
        (lA W ^ (κ₁ + E + σA + (size (c - 2) + S)) * u3 * W.π₀ ^ (MA - R) *
          (∏ k ∈ Finset.range 2, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * MA)) * qA W ^ size (c - 1)) •
          (P2 • ((W.φD T₂) ^ 2) xH)) := by
    rw [pow_zero, one_smul, hV, map_sub, Formalism.MainNotions.UnusedSlot80.Relay2.γ_lsmul, Formalism.MainNotions.UnusedSlot80.Relay2.γ_lsmul, hg₀]
    exact DYCA.g_B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B1 B2
  have hmemB : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1)
      ((lA W ^ (size (c - 1) + κ) * W.π₀ ^ (R₀ - R) * g₀) • W.map F x₁ -
        (lA W ^ (κ₁ + E + σA + (size (c - 2) + S)) * u3 * W.π₀ ^ (MA - R) *
          (∏ k ∈ Finset.range 2, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * MA)) * qA W ^ size (c - 1)) •
          (P2 • ((W.φD T₂) ^ 2) xH)) := by
    refine Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W T₂ _ ?_ ?_
    · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T₂ _ (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hlA _)
        (W.AΔ.pow_mem hπ _)) hg₀A) (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W F hW₁.1 hW₂.1 _ hx₁)
    · refine Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T₂ _ ?_ (hcont xH hxH)
      exact W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hlA _) hu3)
        (W.AΔ.pow_mem hπ _)) (W.AΔ.prod_mem fun k _ => W.AΔ.pow_mem (hpk k) _)) (W.AΔ.pow_mem hqA _)

  obtain ⟨κa, hκa, -, hγπ⟩ := gamma_pi0_eq_pi0_mul_one_add_unit_mul_q W hcase hP9
  obtain ⟨gp, hgp, hγp⟩ := gamma_level_eq_mul W hcase hP9 1 le_rfl
  have hγl : W.γA W.gam (lA W) = lA W := by simp [lA]
  have hγq : W.γA W.gam (qA W) = qA W * (1 + W.π₀ * κa) := by
    have hqd : qA W = W.π₀ + lA W := rfl
    rw [hqd, map_add (f := _), hγπ, hγl, hqd]; ring
  have hγp' : W.γA W.gam (ps W 1) = ps W 1 * (1 + W.π₀ * (qA W * gp)) := by rw [hγp]; ring
  obtain ⟨h1, hh1, eh1⟩ := DYCA.γ_pow_form W hκa hπ hγq (size (c - 1))
  obtain ⟨h2, hh2, eh2⟩ := DYCA.γ_pow_form W hκa hπ hγq Gb
  obtain ⟨h3, hh3, eh3⟩ := DYCA.γ_pow_form W (W.AΔ.mul_mem hqA hgp) hπ hγp' Gb
  have eh23 := DYCA.γ_mul_form W eh2 eh3
  have eh123 := DYCA.γ_mul_form W eh1 eh23
  rw [← hP2', ← hg₀] at eh123
  have hh23 : h2 + h3 + W.π₀ * h2 * h3 ∈ W.AΔ :=
    W.AΔ.add_mem (W.AΔ.add_mem hh2 hh3) (W.AΔ.mul_mem (W.AΔ.mul_mem hπ hh2) hh3)
  have hh123 : h1 + (h2 + h3 + W.π₀ * h2 * h3) + W.π₀ * h1 * (h2 + h3 + W.π₀ * h2 * h3) ∈ W.AΔ :=
    W.AΔ.add_mem (W.AΔ.add_mem hh1 hh23) (W.AΔ.mul_mem (W.AΔ.mul_mem hπ hh1) hh23)

  obtain ⟨kU, xU, hxU, hU⟩ := DYCA.exists_pow_smul_eq_pi_pow_smul_of_twist_sub W T₂ hC (c - 1) g₀ _ hh123 eh123 R V
    ⟨κ', _, hmemA, hEA⟩ ⟨0, _, hmemB, hBeq⟩

  have hφs : ∀ (a : LetA O n) (x : W.DD T₂), W.φD T₂ (a • x) = W.φA a • W.φD T₂ x := fun a x => by
    simpa using Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul W T₂ 1 a x
  have hφl : ∀ (k : ℕ) (x : W.DD T₂), W.φD T₂ (lA W ^ k • x) = lA W ^ k • W.φD T₂ x := fun k x => by
    rw [hφs, map_pow]; simp [lA]
  have hφU := congrArg (W.φD T₂) hU
  rw [hφl, hφs, hφs, map_pow] at hφU
  obtain ⟨u4, hu4, -, -, -, hT4⟩ := hC.Tr2 1 R
  simp only [pow_one, Finset.prod_range_one] at hT4
  rw [hT4] at hφU
  have hpk0 : Formalism.MainNotions.LiftingTheory.pk W 0 = qA W := by
    simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, qA, lA]
  have hBh : size c + S ≤ A.h := by
    have h8 := hOK.2.2.2.2.2.2.2.1 c
    rcases Bool.eq_false_or_eq_true (up c) with hu | hu <;>
      simpa [hA, arcOf, hu, Formalism.MainNotions.LocalTheoryWindows.LT.thick, Formalism.MainNotions.LocalTheoryWindows.LT.size] using h8
  have hMB : size c + S ≤ (PD.p - 1) * MA := by
    have := Formalism.MainNotions.UnusedSlot80.Relay2.arith_h PD.p A.h hl
    rw [hMA]; unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.M
    exact hBh.trans this.le
  have hRB : size c + S ≤ (PD.p - 1) * R := by
    rcases le_total R₀ MA with h | h
    · rw [hRdef, min_eq_left h]; exact hR₀
    · rw [hRdef, min_eq_right h]; exact hMB
  have hsplit : qA W ^ ((PD.p - 1) * R) =
      qA W ^ (size c + S) * qA W ^ ((PD.p - 1) * R - (size c + S)) := by
    rw [← pow_add]; congr 1 <;> omega
  have hInU : InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) (lA W ^ kU • (W.φA g₀ • W.φD T₂ V)) := by
    rw [hφU, hpk0, hsplit]
    refine ⟨(u4 * W.π₀ ^ R * qA W ^ ((PD.p - 1) * R - (size c + S))) • W.φD T₂ xU,
      Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T₂ _ 1 (W.AΔ.mul_mem (W.AΔ.mul_mem hu4 (W.AΔ.pow_mem hπ _))
        (W.AΔ.pow_mem hqA _)) _ (by simpa using Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T₂ (c - 1) 1 hxU), ?_⟩
    rw [smul_smul]; congr 1; ring

  have hφq : W.φA (qA W) = ps W 1 := by simp only [ps, pow_one]
  have hφp1 : W.φA (ps W 1) = ps W 2 := by simp only [ps, sq, pow_one, AlgHom.mul_apply]
  have hgcl : W.φA g₀ ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} := by
    rw [hg₀, hP2', map_mul, map_mul, map_pow, map_pow, map_pow, hφq, hφp1]
    have m1 : ps W 1 ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} :=
      Submonoid.subset_closure ⟨1, le_rfl, rfl⟩
    have m2 : ps W 2 ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} :=
      Submonoid.subset_closure ⟨2, by norm_num, rfl⟩
    exact Submonoid.mul_mem _ (Submonoid.pow_mem _ m1 _)
      (Submonoid.mul_mem _ (Submonoid.pow_mem _ m1 _) (Submonoid.pow_mem _ m2 _))
  refine ⟨W.φA g₀, hgcl, kU + κ₁, ?_⟩
  have hrelF := congrArg (W.map F) hrel
  simp only [map_add (f := _), Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul W F, W.map_φ] at hrelF
  have hφV : W.φD T₂ V = lA W ^ (size (c - 1) + κ) • W.φD T₂ (W.map F X₁) -
      lA W ^ (κ₁ + E + σA + (size (c - 2) + S)) • W.φD T₂ (((W.φD T₂) ^ 2) Hh) := by
    rw [hV, map_sub, hφl, hφl]
  have hφ3 : ((W.φD T₂) ^ 3) Hh = W.φD T₂ (((W.φD T₂) ^ 2) Hh) :=
    Formalism.MainNotions.UnusedSlot80.PhiPowers.pow_apply_succ W T₂ 2 Hh
  have hFZ : W.map F Z ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T₂ (c - 1) 1 :=
    Formalism.MainNotions.UnusedSlot80.Relay2.mem_Pp_of_inMultiple W T₂ _ 1 W.AΔ.one_mem (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_map W F hW₁.1 hW₂.1 _ 1 1 hZ)
  rw [hφ3, DYCA.g_K (lA W) (W.φA g₀) W.π₀ (qA W ^ (size c + S)) kU κ₁ (size (c - 1)) κ σ₁ E σA
    (size (c - 2)) S _ _ _ _ _ hrelF hφV]
  refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_sub W T₂ _ 1 _ (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_lA_pow_smul W T₂ _ 1 _ σ₁ hInU) ?_
  refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T₂ _ 1 _ ?_ (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T₂ _ 1 _ hFZ)
  exact W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hlA _)
    (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_mem_AΔ W hg₀A)) hπ

end Formalism.MainNotions.N.FrobeniusPowerSeries
