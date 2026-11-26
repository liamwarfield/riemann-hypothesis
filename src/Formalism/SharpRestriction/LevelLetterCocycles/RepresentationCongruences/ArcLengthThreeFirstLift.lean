module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeCongruenceLift

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeGammaFirstLift
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

theorem arc_length_three_gamma_first_lift [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (R₀ σ₁ κ₁ : ℕ) (X₁ x₁ y₁ Z : W.DD T₁) (hR₀ : size c + S ≤ (PD.p - 1) * R₀) (hR₁ : 1 ≤ R₀)
    (hX₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) X₁) (hx₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x₁)
    (hγX : W.γ T₁ X₁ - X₁ = W.π₀ ^ R₀ • x₁) (hy₁ : InFP W T₁ (c - 1) 1 1 y₁) (hZ : InFP W T₁ (c - 1) 1 1 Z)
    (hrel : lA W ^ κ₁ • y₁ + (W.π₀ * qA W ^ (size c + S)) • Z = lA W ^ σ₁ • W.φD T₁ X₁) :
    InI W T₁ c y₁ ∧ InFNc W T₁ c 1 (qA W ^ (size c + S) • y₁) := by
  have hT : IsCrys PD T₁.ρ := hW₁.1
  have hR : GS.RD W := NTB.ringData_of_crystalline W hcase hP9 T₁ hT
  obtain ⟨y, hyP, hyy⟩ := hy₁
  rw [one_smul] at hyy
  subst hyy
  obtain ⟨Zp, hZP, hZZ⟩ := hZ
  rw [one_smul] at hZZ
  subst hZZ
  have hLD := DYB.Pp_le_HLD W T₁ (c - 1) hyP
  rw [sub_add_cancel] at hLD

  have hup : up c = false := by
    have h1 := (halt (c - 2)).1
    have h2 := (halt (c - 1)).1
    have e1 : c - 2 + 1 = c - 1 := by ring
    rw [e1, hD] at h1
    rw [sub_add_cancel] at h2
    cases hc1 : up (c - 1) <;> simp_all

  have hJL : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₁ (fun i => if up i then η else size i + S)
      (fun i => if up i then size i + S else η) := by
    intro τ i hτ a ha
    have h := hW₁.2 i τ hτ a ha
    have hok := hOK.2.2.2.2.1 i
    simp only [arcOf] at h hok
    cases hi : up i <;> simp [hi, Formalism.MainNotions.LocalTheoryWindows.LT.win, Formalism.MainNotions.LocalTheoryWindows.LT.ok] at h hok ⊢ <;> omega
  have h5 := (hP5 T₁ _ _ hT hJL).1 c
  simp only [hup, Bool.false_eq_true, ↓reduceIte] at h5
  have hring := ((hP9 T₁ hT hcase.2.1 hcase.2.2).2.2 (NTB.finrank_one W hcase)).1
  obtain ⟨wq, hwq⟩ := hring.2.2.2.2.1
  have hQ : W.Q = (wq : LetA O n) * qA W := by
    have hQq : W.Q = W.q := by
      unfold LocWach.Q
      rw [hcase.2.1]
      simp
    rw [hQq, hwq]
    congr 1
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  have hq : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x → qA W ^ (size c + S) • W.φD T₁ x ∈ W.N T₁ := by
    intro x hx
    have h := h5 x hx.2
    rw [hQ, mul_pow, mul_smul] at h
    have h' := (W.N T₁).smul_mem (((wq⁻¹ : (LetA O n)ˣ) : LetA O n) ^ (size c + S)) h
    rwa [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at h'

  have hγP : W.γ T₁ y₁ - y₁ ∈ Pp W T₁ (c - 1) 1 := sub_mem (DYB.Pp_γ W T₁ (c - 1) hyP) hyP
  obtain ⟨w, hwΔ, hwφ⟩ := NTB.w_mem hR
  obtain ⟨u, huΔ, hγπ⟩ := GS.gamma_pi0_eq_pi0_mul_unit hR
  obtain ⟨r, rfl⟩ : ∃ r, R₀ = r + 1 := ⟨R₀ - 1, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, (PD.p - 1) * (r + 1) = (size c + S) + t := ⟨_, (Nat.add_sub_of_le hR₀).symm⟩
  have hπΔ := GS.π₀_mem W
  have hqΔ := GS.qA_mem W
  have hlΔ : lA W ∈ W.AΔ := NTB.lA_mem'
  have ha₁ : lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hlΔ _) (W.AΔ.pow_mem hwΔ _))
      (W.AΔ.pow_mem hπΔ _)) (W.AΔ.pow_mem hqΔ _)
  have hu' : (1 + (u : LetA O n) * qA W) * (1 + (u : LetA O n) * W.π₀) ^ (size c + S) ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.add_mem (W.AΔ.one_mem) (W.AΔ.mul_mem huΔ hqΔ))
      (W.AΔ.pow_mem (W.AΔ.add_mem (W.AΔ.one_mem) (W.AΔ.mul_mem huΔ hπΔ)) _)
  have hbrP : (lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t) • W.φD T₁ x₁ -
      (((1 + (u : LetA O n) * qA W) * (1 + (u : LetA O n) * W.π₀) ^ (size c + S)) • W.γ T₁ Z - Z) ∈
      Pp W T₁ (c - 1) 1 := by
    refine sub_mem (AddSubgroup.subset_closure ⟨_, ha₁, x₁, hx₁, by rw [pow_one]⟩)
      (sub_mem (DYB.Pp_smul W T₁ (c - 1) hu' (DYB.Pp_γ W T₁ (c - 1) hZP)) hZP)
  have e1 : W.γ T₁ (lA W ^ κ₁ • y₁) = lA W ^ κ₁ • W.γ T₁ y₁ := by
    rw [DYB.γ_smulA, DYB.γA_lA_pow]
  have e2 : lA W ^ κ₁ • y₁ = lA W ^ σ₁ • W.φD T₁ X₁ - (W.π₀ * qA W ^ (size c + S)) • Z :=
    eq_sub_of_add_eq hrel
  have e3 : W.γ T₁ (W.φD T₁ X₁) =
      W.φD T₁ X₁ + ((w : LetA O n) * W.π₀ * qA W ^ (PD.p - 1)) ^ (r + 1) • W.φD T₁ x₁ := by
    have h1 : W.γ T₁ (W.φD T₁ X₁) = W.φD T₁ (W.γ T₁ X₁) := (W.φγ_comm T₁ W.gam X₁).symm
    rw [h1, ← hwφ, ← map_pow, ← DYB.φD_smulA, ← map_add (f := _), ← hγX, add_sub_cancel]
  have e4 : W.γ T₁ ((W.π₀ * qA W ^ (size c + S)) • Z) =
      ((W.π₀ * qA W ^ (size c + S)) * ((1 + (u : LetA O n) * qA W) *
        (1 + (u : LetA O n) * W.π₀) ^ (size c + S))) • W.γ T₁ Z := by
    rw [DYB.γ_smulA, map_mul, map_pow, hγπ, GS.γqA hγπ, mul_pow]
    congr 1
    ring
  have e5 : W.γ T₁ (lA W ^ σ₁ • W.φD T₁ X₁) = lA W ^ σ₁ • W.γ T₁ (W.φD T₁ X₁) := by
    rw [DYB.γ_smulA, DYB.γA_lA_pow]
  have hscal : ((w : LetA O n) * W.π₀ * qA W ^ (PD.p - 1)) ^ (r + 1) =
      W.π₀ * qA W ^ (size c + S) * ((w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t) := by
    rw [mul_pow, mul_pow, ← pow_mul, ht, pow_add]
    ring
  have hkey : lA W ^ κ₁ • (W.γ T₁ y₁ - y₁) = (W.π₀ * qA W ^ (size c + S)) •
      ((lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t) • W.φD T₁ x₁ -
        (((1 + (u : LetA O n) * qA W) * (1 + (u : LetA O n) * W.π₀) ^ (size c + S)) • W.γ T₁ Z -
          Z)) := by
    rw [smul_sub, ← e1, e2, map_sub, e5, e3, e4, hscal]
    simp only [smul_add, smul_sub, smul_smul]
    rw [show lA W ^ σ₁ * (W.π₀ * qA W ^ (size c + S) * ((w : LetA O n) ^ (r + 1) * W.π₀ ^ r *
        qA W ^ t)) = W.π₀ * qA W ^ (size c + S) * (lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) *
        W.π₀ ^ r * qA W ^ t) by ring]
    abel
  have hfP : W.π₀ * qA W ^ (size c + S) ∈ PiPs W := by
    have h0 : ps W 0 = qA W := by simp [ps]
    exact (PiPs W).mul_mem (Submonoid.subset_closure (Set.mem_insert _ _))
      ((PiPs W).pow_mem (Submonoid.subset_closure (Set.mem_insert_of_mem _ ⟨0, h0⟩)) _)
  obtain ⟨tt, httP, htt⟩ := hSatP hcase T₁ (c - 1) 1 (W.π₀ * qA W ^ (size c + S)) 1 hT hfP
    (PiPs W).one_mem (W.γ T₁ y₁ - y₁) ⟨_, hγP, rfl⟩ ⟨κ₁, _, hbrP, hkey⟩
  have httq := DYB.Pp_qpow W T₁ (c - 1) _ hq httP
  have httL := DYB.Pp_le_HLD W T₁ (c - 1) httP
  rw [sub_add_cancel] at httL
  refine ⟨⟨hLD.1, hLD.2, qA W ^ (size c + S) • tt, httq, ?_, ?_⟩,
    qA W ^ (size c + S) • y₁, DYB.Pp_qpow W T₁ (c - 1) _ hq hyP, ?_, (one_smul _ _).symm⟩
  · rw [smul_smul, mul_comm, ← smul_smul, httL.1]
  · rw [htt, smul_smul]
  · rw [smul_smul, mul_comm, ← smul_smul, hLD.1]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeBuildFirstLift
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SmulOMem
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.QALetterNe
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem phi_smul (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  show W.φD T (a • x) = (letφ W.φ₀ a) • W.φD T x
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]

variable {W} [IsDomain O] [FiniteDimensional Qp LL]

theorem π₀_letter_ne (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : W.π₀ j ≠ 0 := by
  obtain ⟨w, hw⟩ := hR.1
  intro h0
  have h1 : W.π₀ j = (w : LetA O n) j * PowerSeries.X ^ (PD.p - 1) := by
    rw [hw, Pi.mul_apply, Pi.pow_apply]
    rfl
  rw [h1] at h0
  have hu : IsUnit ((w : LetA O n) j) := w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) j)
  have hX : (PowerSeries.X : PowerSeries O) ^ (PD.p - 1) ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  exact hX (hu.mul_right_eq_zero.mp h0)

theorem cancel_π₀ (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) {x y : LetA O n} (h : W.π₀ * x = W.π₀ * y) : x = y := by
  funext j
  have h' := congrFun h j
  simp only [Pi.mul_apply] at h'
  exact mul_left_cancel₀ (π₀_letter_ne hR j) h'

theorem qA_letter_cc (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : constantCoeff (qA W j) = ((PD.p : ℕ) : O) := by
  obtain ⟨w, hw⟩ := hR.1
  have hp2 : 2 ≤ PD.p := PD.hp.two_le
  have h1 : qA W j = (w : LetA O n) j * PowerSeries.X ^ (PD.p - 1) + ((PD.p : ℕ) : PowerSeries O) := by
    show W.π₀ j + (lA W) j = _
    rw [hw, Pi.mul_apply, Pi.pow_apply]
    rfl
  rw [h1, map_add (f := _), map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero, zero_add,
    map_natCast]

theorem qA_letter_ne (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : qA W j ≠ 0 := by
  intro h
  have hc := qA_letter_cc hR j
  rw [h, map_zero] at hc
  have hv := W.v_l
  have h0 : ((PD.p : ℕ) : LL) = 0 := by
    rw [← map_natCast (algebraMap O LL), ← hc, map_zero]
  rw [h0, AddValuation.map_zero] at hv
  simp at hv

theorem w_mem (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) :
    ∃ w ∈ W.AΔ, IsUnit w ∧ W.φA W.π₀ = w * W.π₀ * qA W ^ (PD.p - 1) := by
  obtain ⟨w, hw⟩ := hR.2.1
  have hinv : ∀ g, g ∈ W.DelF → g⁻¹ ∈ W.DelF := by
    intro g hg
    obtain ⟨k, hk, hk'⟩ := (W.DelF_def g).1 hg
    exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hk', inv_one]⟩
  have hmul : ∀ a b, a ∈ W.DelF → b ∈ W.DelF → a * b ∈ W.DelF := by
    intro a b ha hb
    obtain ⟨k, hk, hk'⟩ := (W.DelF_def a).1 ha
    obtain ⟨m, hm, hm'⟩ := (W.DelF_def b).1 hb
    refine (W.DelF_def _).2 ⟨k * m, Nat.mul_pos hk hm, ?_⟩
    rw [mul_pow, pow_mul, hk', one_pow, one_mul, mul_comm k m, pow_mul, hm', one_pow]
  have hπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := by
    intro δ hδ
    funext i
    show W.γ₀ δ W.π₀₁ = W.π₀₁
    unfold Formalism.BasicNotions.LocWach.π₀₁
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sub, map_one, map_natCast, map_sum]
    congr 1
    have hsum : ∀ x ∈ W.DelF, W.γ₀ δ (W.γ₀ x (1 + PowerSeries.X)) = W.γ₀ (δ * x) (1 + PowerSeries.X) := by
      intro x _
      rw [map_mul, AlgHom.mul_apply]
    rw [Finset.sum_congr rfl hsum]
    refine Finset.sum_equiv (Equiv.mulLeft δ) (fun g => ?_) (fun g _ => rfl)
    constructor
    · intro hg
      exact hmul δ g hδ hg
    · intro hg
      have := hmul δ⁻¹ (δ * g) (hinv δ hδ) hg
      rwa [inv_mul_cancel_left] at this
  have hq : ∀ δ ∈ W.DelF, W.γA δ (qA W) = qA W := by
    intro δ hδ
    show W.γA δ (W.π₀ + lA W) = W.π₀ + lA W
    rw [map_add (f := _), hπ δ hδ]
    congr 1
    show W.γA δ ((PD.p : ℕ) : LetA O n) = ((PD.p : ℕ) : LetA O n)
    exact map_natCast _ _
  have hc : ∀ δ (a : LetA O n), W.γA δ (W.φA a) = W.φA (W.γA δ a) := by
    intro δ a
    funext i
    show W.γ₀ δ (W.φ₀ (a (i - 1))) = W.φ₀ (W.γ₀ δ (a (i - 1)))
    rw [W.γ₀_comm]
  refine ⟨w, ?_, w.isUnit, hw⟩
  show ∀ δ ∈ W.DelF, W.γA δ (w : LetA O n) = w
  intro δ hδ
  have e1 := congrArg (W.γA δ) hw
  rw [hc, hπ δ hδ, map_mul, map_mul, map_pow, hπ δ hδ, hq δ hδ, hw] at e1
  funext j
  have e2 := congrFun e1 j
  simp only [Pi.mul_apply, Pi.pow_apply] at e2
  have hne : W.π₀ j * qA W j ^ (PD.p - 1) ≠ 0 :=
    mul_ne_zero (π₀_letter_ne hR j) (pow_ne_zero _ (qA_letter_ne hR j))
  apply mul_left_cancel₀ hne
  linear_combination -e2

theorem coord_mod (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) {T : LocLat G Qp LL O} {i : ZMod n} {d : ℕ} {b : Fin d → W.DD T}
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i b) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    ∃ (c₀ : Fin d → O) (z : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T i z ∧
      x = Formalism.MainNotions.LiftingTheory.vecB W T b c₀ + W.π₀ • z := by
  obtain ⟨a, ⟨haA, hxa⟩, -⟩ := hb.2 x hx
  choose F hF using fun m => hR.2.2.2 (a m) (haA m).1
  have hs : HasSubst W.π₀₁ := HasSubst.of_constantCoeff_zero' (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀₁_cc hR)
  let c₀ : Fin d → O := fun m => constantCoeff (F m i)
  let g : Fin d → PowerSeries O := fun m => substAlgHom hs (mk fun k => coeff (k + 1) (F m i))
  let a' : Fin d → LetA O n := fun m => Pi.single i (g m)
  have hzero : ∀ m, ∀ j, j ≠ i → a m j = 0 := by
    intro m j hj
    have := congrFun (haA m).2 j
    simp only [Pi.mul_apply, letE, Pi.single_apply, hj, if_false, zero_mul] at this
    exact this.symm
  have key : ∀ m, a m = algebraMap O (LetA O n) (c₀ m) * letE i + W.π₀ * a' m := by
    intro m
    funext j
    by_cases hj : j = i
    · subst hj
      have e1 : a m j = substAlgHom hs (F m j) := by rw [hF m j, coe_substAlgHom]; rfl
      rw [e1]
      conv_lhs => rw [eq_shift_mul_X_add_const (F m j)]
      rw [map_add (f := _), map_mul, substAlgHom_X hs]
      have e2 : substAlgHom hs (C (constantCoeff (F m j))) = C (constantCoeff (F m j)) := by
        rw [coe_substAlgHom, subst_C]
        rfl
      rw [e2]
      show _ = (algebraMap O (LetA O n) (c₀ m)) j * (letE (O := O) j : LetA O n) j + W.π₀ j * a' m j
      have e3 : (algebraMap O (LetA O n) (c₀ m)) j = C (c₀ m) := rfl
      simp only [e3, letE, a', g, c₀, Pi.single_eq_same, mul_one]
      show _ = C (constantCoeff (F m j)) + W.π₀₁ * _
      ring
    · simp only [Pi.add_apply, Pi.mul_apply, letE, Pi.single_apply, hj, if_false, mul_zero, a', zero_add, hzero m j hj]
  have h1 : ∀ m, W.π₀ * a' m = a m - algebraMap O (LetA O n) (c₀ m) * letE i := by
    intro m
    rw [key m]
    ring
  refine ⟨c₀, ∑ m, a' m • b m, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Submodule.sum_mem _ fun m _ => (W.N T).smul_mem _ (hb.1 m).1.1
  · intro δ hδ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γD_smulA, (hb.1 m).1.2 δ hδ]
    congr 1
    apply cancel_π₀ hR
    calc W.π₀ * W.γA δ (a' m) = W.γA δ (W.π₀ * a' m) := by
          rw [map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀_mem W δ hδ]
      _ = W.γA δ (a m - algebraMap O (LetA O n) (c₀ m) * letE i) := by rw [h1]
      _ = a m - algebraMap O (LetA O n) (c₀ m) * letE i := by
          rw [map_sub, map_mul, (haA m).1 δ hδ, AlgHom.commutes, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γA_letE]
      _ = W.π₀ * a' m := (h1 m).symm
  · refine ⟨∑ m, a' m • b m, Submodule.sum_mem _ fun m _ => (W.N T).smul_mem _ (hb.1 m).1.1, ?_⟩
    show (letE i : LetA O n) • (∑ m, a' m • b m) = ∑ m, a' m • b m
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [letE, a']
    · simp [letE, a', hj]
  · rw [hxa]
    simp only [Formalism.MainNotions.LiftingTheory.vecB]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hlet : (letE i : LetA O n) • b m = b m := Formalism.MainNotions.N.FrobeniusPowerSeries.TypesD.nl_letter W (hb.1 m).2
    rw [key m, add_smul, mul_smul, hlet, algebraMap_smul, mul_smul]

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Imports
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYAb

open Finset

theorem split {R : Type*} [CommRing R] (π q l : R) (hq : q = π + l) (e B r : ℕ) :
    π ^ (r + 1) * q ^ (e * (r + 1)) =
      (∑ k ∈ (range (r + 1)).filter (fun k => k + e * (r + 1) < B),
        (-1 : R) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * π * q ^ (k + e * (r + 1))) +
      π * q ^ B * ∑ k ∈ (range (r + 1)).filter (fun k => ¬ k + e * (r + 1) < B),
        (-1 : R) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * q ^ (k + e * (r + 1) - B) := by
  have hπ : π = q + (-l) := by rw [hq]; ring
  have h1 : π ^ (r + 1) * q ^ (e * (r + 1)) = π * q ^ (e * (r + 1)) * (q + (-l)) ^ r := by
    rw [← hπ]; ring
  rw [h1, add_pow, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not (range (r + 1))
    (fun k => k + e * (r + 1) < B), Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow]
    ring
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : B ≤ k + e * (r + 1) := by
      simp only [Finset.mem_filter] at hk
      omega
    have hq' : q ^ (k + e * (r + 1)) = q ^ B * q ^ (k + e * (r + 1) - B) := by
      rw [← pow_add]; congr 1; omega
    rw [neg_pow]
    calc π * q ^ (e * (r + 1)) * (q ^ k * ((-1) ^ (r - k) * l ^ (r - k)) * (r.choose k : R))
        = (-1) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * π * q ^ (k + e * (r + 1)) := by ring
      _ = π * q ^ B * ((-1) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * q ^ (k + e * (r + 1) - B)) := by
        rw [hq']; ring

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYAb
end

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYAc

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

theorem int_of_bd (W : LocWach PD LL O v n)
    (hH4 : ∀ r : ℕ, ((r + padicValNat PD.p r.factorial : ℕ) : ℚ) ≤ r * PD.p / ((PD.p : ℚ) - 1))
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    {r a : ℕ} {s : LL} (hs : Formalism.MainNotions.LiftingTheory.Bd W r s) (ha : (r : ℚ) * PD.p / ((PD.p : ℚ) - 1) ≤ a) :
    ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ a * s := by
  have hc : (((r + padicValNat PD.p r.factorial : ℕ) : ℚ)) ≤ a := (hH4 r).trans ha
  apply hOv
  rw [AddValuation.map_mul, Formalism.MainNotions.LiftingTheory.tr_v_pow W a]
  unfold Formalism.MainNotions.LiftingTheory.Bd at hs
  by_cases htop : v s = ⊤
  · rw [htop, WithTop.add_top]
    exact le_top
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hq] at hs ⊢
    have hq' : -((r + padicValNat PD.p r.factorial : ℕ) : ℚ) ≤ q := WithTop.coe_le_coe.mp hs
    rw [← WithTop.coe_add, ← WithTop.coe_zero]
    exact WithTop.coe_le_coe.mpr (by linarith)

theorem smulA_mem (W : LocWach PD LL O v n) {T : LocLat G Qp LL O} {i : ZMod n} {a : LetA O n}
    (ha : a ∈ W.AΔ) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (a • x) := by
  exact ⟨Formalism.MainNotions.LiftingTheory.invariant_smul_mem_invariants' W T a ha x hx.1, (W.Nl T i).smul_mem a hx.2⟩

theorem smulO_mem (W : LocWach PD LL O v n) {T : LocLat G Qp LL O} {i : ZMod n} (a : O)
    {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (a • x) := by
  exact ⟨(W.NΔ T).smul_mem a hx.1, ((W.Nl T i).restrictScalars O).smul_mem a hx.2⟩

theorem sum_mem' (W : LocWach PD LL O v n) {T : LocLat G Qp LL O} {i : ZMod n} {ι : Type*} (s : Finset ι)
    (f : ι → W.DD T) (hf : ∀ j ∈ s, Formalism.MainNotions.LiftingTheory.InNΔi W T i (f j)) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T i (∑ j ∈ s, f j) := by
  exact ⟨(W.NΔ T).sum_mem fun j hj => (hf j hj).1, (W.Nl T i).sum_mem fun j hj => (hf j hj).2⟩

theorem build [IsDomain O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    {T : LocLat G Qp LL O} (hT : IsCrys PD T.ρ) (i : ZMod n) {d : ℕ} (b₁ : Fin d → W.DD T)
    (sol₁ : Fin d → ℕ → Fin d → LL) (hb₁ : IsHor W T i b₁ sol₁) (n₁ : W.DD T)
    (hn₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T i n₁) (Bq : ℕ) (hBq : 1 ≤ Bq) (hl5 : 5 ≤ PD.p) :
    ∃ (c₀ : Fin d → O) (z₁ : W.DD T) (R₀ σ₁ κ₁ : ℕ) (yy : ℕ → Fin d → O) (X₁ x₁ y₁ Z : W.DD T),
      Formalism.MainNotions.LiftingTheory.InNΔi W T i z₁ ∧ n₁ = Formalism.MainNotions.LiftingTheory.vecB W T b₁ c₀ + W.π₀ • z₁ ∧
      Bq ≤ (PD.p - 1) * R₀ ∧ 1 ≤ R₀ ∧ ((σ₁ : ℝ) ≤ (Bq : ℝ) / ((PD.p : ℝ) - 1) + 1) ∧
      (∀ r < R₀, ∀ m, algebraMap O LL (yy r m) = (PD.p : LL) ^ κ₁ * ∑ k, algebraMap O LL (c₀ k) * sol₁ k r m) ∧
      X₁ = ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (yy r) ∧
      Formalism.MainNotions.LiftingTheory.InNΔi W T i X₁ ∧ Formalism.MainNotions.LiftingTheory.InNΔi W T i x₁ ∧ W.γ T X₁ - X₁ = W.π₀ ^ R₀ • x₁ ∧
      InFP W T i 1 1 y₁ ∧ InFP W T i 1 1 Z ∧
      lA W ^ κ₁ • y₁ + (W.π₀ * qA W ^ Bq) • Z = lA W ^ σ₁ • W.φD T X₁ := by
  classical
  obtain ⟨c₀, z₁, hz₁, hn₁eq⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa.coord_mod hR hb₁.1 hn₁
  obtain ⟨-, -, -, hH4, hH5⟩ := hH hcase T hT i
  have hBd : ∀ k r m, Formalism.MainNotions.LiftingTheory.Bd W r (sol₁ k r m) := (hH5 d b₁ hb₁.1 sol₁ hb₁.2).1
  have hp5 : (5 : ℝ) ≤ PD.p := by exact_mod_cast hl5
  have hp5q : (5 : ℚ) ≤ PD.p := by exact_mod_cast hl5

  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℕ, R₀ = ⌈(Bq : ℝ) / ((PD.p : ℝ) - 1)⌉₊ := ⟨_, rfl⟩
  have hR₀le : (Bq : ℝ) / ((PD.p : ℝ) - 1) ≤ R₀ := hR₀ ▸ Nat.le_ceil _
  have hR₀lt : (R₀ : ℝ) < (Bq : ℝ) / ((PD.p : ℝ) - 1) + 1 := hR₀ ▸ Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg _) (by linarith))
  have hBqR : (1 : ℝ) ≤ Bq := by exact_mod_cast hBq
  have hBR' : (Bq : ℝ) ≤ ((PD.p : ℝ) - 1) * R₀ := by
    rw [div_le_iff₀ (by linarith)] at hR₀le; linarith
  have hBR : Bq ≤ (PD.p - 1) * R₀ := by
    have h2 : ((PD.p - 1 : ℕ) : ℝ) = (PD.p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have : (Bq : ℝ) ≤ ((PD.p - 1 : ℕ) : ℝ) * (R₀ : ℝ) := by rw [h2]; exact hBR'
    exact_mod_cast this
  have hR1 : 1 ≤ R₀ := by
    rcases Nat.eq_zero_or_pos R₀ with h0 | h0
    · rw [h0] at hBR'; simp at hBR'; linarith
    · exact h0

  have hys : ∀ k r m, r < R₀ → ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ (2 * R₀) * sol₁ k r m := by
    intro k r m hr
    apply int_of_bd W hH4 hOv (hBd k r m)
    have hr' : (r : ℚ) + 1 ≤ R₀ := by exact_mod_cast hr
    rw [div_le_iff₀ (by linarith)]
    push_cast
    have h1 : (r : ℚ) * PD.p ≤ R₀ * PD.p := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (0 : ℚ) ≤ R₀ * (PD.p - 2) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  choose! ys hys' using hys
  set yy : ℕ → Fin d → O := fun r m => ∑ k, c₀ k * ys k r m with hyydef
  have hyy : ∀ r < R₀, ∀ m, algebraMap O LL (yy r m) =
      (PD.p : LL) ^ (2 * R₀) * ∑ k, algebraMap O LL (c₀ k) * sol₁ k r m := by
    intro r hr m
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hyydef, map_sum, map_mul, hys' _ _ _ hr, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hyy0 : ∀ m, yy 0 m = (PD.p : O) ^ (2 * R₀) * c₀ m := by
    intro m
    apply hinj
    rw [hyy 0 (by omega) m, map_mul, map_pow, map_natCast]
    congr 1
    simp [(hb₁.2 _).2, Pi.single_apply]

  have hX : ∀ k, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x ∧
      W.γ T (∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (ys k r)) -
        (∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (ys k r)) = W.π₀ ^ R₀ • x := by
    intro k
    obtain ⟨x, hx, hxe⟩ := (hb₁.2 k).1 R₀ (2 * R₀) (ys k) (fun r hr m => hys' k r m hr)
    exact ⟨x, hx, by rw [← hxe, smul_zero, sub_zero]⟩
  choose xk hxk hxke using hX
  have hvec : ∀ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i (Formalism.MainNotions.LiftingTheory.vecB W T b₁ y) := fun y =>
    sum_mem' W _ _ fun m _ => smulO_mem W _ (hb₁.1.1 m)
  have hπ₀ := Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀_mem W
  have hq := Formalism.MainNotions.N.FrobeniusPowerSeries.GS.qA_mem W
  have hXeq : ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (yy r) =
      ∑ k, c₀ k • ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (ys k r) := by
    simp only [Formalism.MainNotions.LiftingTheory.vecB, hyydef, Finset.smul_sum, Finset.sum_smul]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul]
    exact smul_comm _ _ _
  obtain ⟨wv, hwA, -, hw⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa.w_mem hR
  have hLA : lA W ∈ W.AΔ := by
    show ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
    exact Subalgebra.natCast_mem _ _
  have hLc : ∀ j : ℕ, algebraMap O (LetA O n) ((PD.p : O) ^ j) = lA W ^ j := by
    intro j; rw [map_pow, map_natCast]; rfl

  have hos : ∀ r' k m, r' + 1 < R₀ → k ≤ r' → k + (PD.p - 1) * (r' + 1) < Bq →
      ∃ o : O, o * (PD.p : O) ^ (2 * R₀) = (PD.p : O) ^ (R₀ + (r' - k)) * yy (r' + 1) m := by
    intro r' k m hr hk hkB
    have hint : ∀ k', ∃ o' : O, algebraMap O LL o' = (PD.p : LL) ^ (R₀ + (r' - k)) * sol₁ k' (r' + 1) m := by
      intro k'
      apply int_of_bd W hH4 hOv (hBd k' (r' + 1) m)
      have he : ((PD.p - 1 : ℕ) : ℚ) = (PD.p : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hkB' : (k : ℚ) + ((PD.p : ℚ) - 1) * (r' + 1) + 1 ≤ Bq := by
        have : (k + (PD.p - 1) * (r' + 1) + 1 : ℕ) ≤ Bq := hkB
        have := (Nat.cast_le (α := ℚ)).2 this
        push_cast [he] at this
        linarith
      have hBRq : (Bq : ℚ) ≤ ((PD.p : ℚ) - 1) * R₀ := by exact_mod_cast hBR'
      have hkr : (k : ℚ) ≤ r' := by exact_mod_cast hk
      have hsub : (((r' - k : ℕ)) : ℚ) = r' - k := by rw [Nat.cast_sub hk]
      rw [div_le_iff₀ (by linarith)]
      push_cast [hsub]
      nlinarith [mul_nonneg (show (0:ℚ) ≤ (PD.p : ℚ) - 2 by linarith) (show (0:ℚ) ≤ r' - k by linarith)]
    choose o' ho' using hint
    refine ⟨∑ k', c₀ k' * o' k', hinj ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_pow, map_natCast, map_sum, ho', hyydef, hys' _ _ _ hr, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => by ring
  choose! o ho using hos

  set e := PD.p - 1 with he
  set L := lA W with hL
  set cO := algebraMap O (LetA O n) with hcO
  obtain ⟨Y, hYdef⟩ : ∃ Y : Fin d → LetA O n, Y = fun m => cO ((PD.p : O) ^ R₀ * c₀ m) +
    ∑ r' ∈ Finset.range (R₀ - 1), wv ^ (r' + 1) *
      ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => k + e * (r' + 1) < Bq),
        (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * W.π₀ * qA W ^ (k + e * (r' + 1)) *
          cO (o r' k m) := ⟨_, rfl⟩
  obtain ⟨Zc, hZdef⟩ : ∃ Zc : Fin d → LetA O n, Zc = fun m =>
    ∑ r' ∈ Finset.range (R₀ - 1), wv ^ (r' + 1) * cO ((PD.p : O) ^ R₀ * yy (r' + 1) m) *
      ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => ¬ k + e * (r' + 1) < Bq),
        (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * L ^ (r' - k) *
          qA W ^ (k + e * (r' + 1) - Bq) := ⟨_, rfl⟩
  have hY : ∀ m, Y m ∈ W.AΔ := by
    intro m
    rw [hYdef]
    refine add_mem (Subalgebra.algebraMap_mem _ _) (sum_mem fun r' _ => mul_mem (pow_mem hwA _)
      (sum_mem fun k _ => mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _)
        (Subalgebra.natCast_mem _ _)) hπ₀) (pow_mem hq _)) (Subalgebra.algebraMap_mem _ _)))
  have hZ : ∀ m, Zc m ∈ W.AΔ := by
    intro m
    rw [hZdef]
    refine sum_mem fun r' _ => mul_mem (mul_mem (pow_mem hwA _) (Subalgebra.algebraMap_mem _ _))
      (sum_mem fun k _ => mul_mem (mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _)
        (Subalgebra.natCast_mem _ _)) (pow_mem hLA _)) (pow_mem hq _))

  have hterm : ∀ r' ∈ Finset.range (R₀ - 1), ∀ m,
      L ^ R₀ * ((W.φA W.π₀) ^ (r' + 1) * cO (yy (r' + 1) m)) =
        L ^ (2 * R₀) * (wv ^ (r' + 1) *
          ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => k + e * (r' + 1) < Bq),
            (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * W.π₀ * qA W ^ (k + e * (r' + 1)) *
              cO (o r' k m)) +
        (W.π₀ * qA W ^ Bq) * (wv ^ (r' + 1) * cO ((PD.p : O) ^ R₀ * yy (r' + 1) m) *
          ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => ¬ k + e * (r' + 1) < Bq),
            (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * L ^ (r' - k) *
              qA W ^ (k + e * (r' + 1) - Bq)) := by
    intro r' hr' m
    have hr'' : r' + 1 < R₀ := by simp only [Finset.mem_range] at hr'; omega
    have e1 : (wv * W.π₀ * qA W ^ e) ^ (r' + 1) =
        wv ^ (r' + 1) * (W.π₀ ^ (r' + 1) * qA W ^ (e * (r' + 1))) := by
      rw [mul_pow, mul_pow, ← pow_mul]; ring
    have hsplit := Formalism.MainNotions.N.FrobeniusPowerSeries.DYAb.split W.π₀ (qA W) L rfl e Bq r'
    have hlow : L ^ R₀ * wv ^ (r' + 1) * cO (yy (r' + 1) m) *
        (∑ k ∈ (Finset.range (r' + 1)).filter (fun k => k + e * (r' + 1) < Bq),
          (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * L ^ (r' - k) * W.π₀ *
            qA W ^ (k + e * (r' + 1))) =
        L ^ (2 * R₀) * (wv ^ (r' + 1) *
          ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => k + e * (r' + 1) < Bq),
            (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * W.π₀ * qA W ^ (k + e * (r' + 1)) *
              cO (o r' k m)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      have hoL := congrArg cO (ho r' k m hr'' (by omega) hk.2)
      simp only [map_mul, map_pow, map_natCast] at hoL
      have hLp : ((PD.p : ℕ) : LetA O n) = L := rfl
      rw [hLp] at hoL
      linear_combination (-(wv ^ (r' + 1) * (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) *
        W.π₀ * qA W ^ (k + e * (r' + 1)))) * hoL
    calc L ^ R₀ * ((W.φA W.π₀) ^ (r' + 1) * cO (yy (r' + 1) m))
        = L ^ R₀ * wv ^ (r' + 1) * cO (yy (r' + 1) m) *
            (∑ k ∈ (Finset.range (r' + 1)).filter (fun k => k + e * (r' + 1) < Bq),
              (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * L ^ (r' - k) * W.π₀ *
                qA W ^ (k + e * (r' + 1))) +
          (W.π₀ * qA W ^ Bq) * (L ^ R₀ * wv ^ (r' + 1) * cO (yy (r' + 1) m) *
            ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => ¬ k + e * (r' + 1) < Bq),
              (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * L ^ (r' - k) *
                qA W ^ (k + e * (r' + 1) - Bq)) := by
          rw [hw, e1, hsplit]; ring
      _ = _ := by
          rw [hlow, map_mul, hLc]
          ring
  have hid : ∀ m, L ^ (2 * R₀) * Y m + (W.π₀ * qA W ^ Bq) * Zc m =
      L ^ R₀ * ∑ r ∈ Finset.range R₀, (W.φA W.π₀) ^ r * cO (yy r m) := by
    intro m
    rw [show Finset.range R₀ = Finset.range ((R₀ - 1) + 1) by rw [Nat.sub_add_cancel hR1],
      Finset.sum_range_succ', pow_zero, one_mul, hyy0, mul_add, Finset.mul_sum,
      Finset.sum_congr rfl fun r' hr' => hterm r' hr' m, Finset.sum_add_distrib, hYdef, hZdef]
    simp only [mul_add, Finset.mul_sum, map_mul, hLc]
    ring

  refine ⟨c₀, z₁, R₀, R₀, 2 * R₀, yy,
    ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (yy r), ∑ k, c₀ k • xk k,
    ∑ m, Y m • W.φD T (b₁ m), ∑ m, Zc m • W.φD T (b₁ m),
    hz₁, hn₁eq, hBR, hR1, hR₀lt.le, hyy, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sum_mem' W _ _ fun r _ => smulA_mem W (pow_mem hπ₀ r) (hvec _)
  · exact sum_mem' W _ _ fun k _ => smulO_mem W _ (hxk k)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hXeq, map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, ← smul_sub, hxke k]
      exact smul_comm _ _ _
  · refine ⟨_, AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure
      ⟨Y m, hY m, b₁ m, hb₁.1.1 m, by rw [pow_one]⟩, by rw [one_smul]⟩
  · refine ⟨_, AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure
      ⟨Zc m, hZ m, b₁ m, hb₁.1.1 m, by rw [pow_one]⟩, by rw [one_smul]⟩
  · have hφX : W.φD T (∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (yy r)) =
        ∑ m, (∑ r ∈ Finset.range R₀, (W.φA W.π₀) ^ r * cO (yy r m)) • W.φD T (b₁ m) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa.phi_smul, Formalism.MainNotions.LiftingTheory.vecB, map_pow, map_smul,
        Finset.smul_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
      rw [← algebraMap_smul (LetA O n) (yy r m), smul_smul]
    rw [hφX, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, smul_smul, smul_smul, ← add_smul, hid m]

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYAc
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

theorem arc_length_three_build_first_lift [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) ∧ W.map F n₁ = (((PD.p : ℕ) : LetA O n) ^ E) • (s • lam)) :
    ∃ (d : ℕ) (b₁ : Fin d → W.DD T₁) (sol₁ : Fin d → ℕ → Fin d → LL) (c₀ : Fin d → O) (z₁ : W.DD T₁)
      (R₀ σ₁ κ₁ : ℕ) (yy : ℕ → Fin d → O) (X₁ x₁ y₁ Z : W.DD T₁),
      IsHor W T₁ (c - 1) b₁ sol₁ ∧
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) z₁ ∧ n₁ = Formalism.MainNotions.LiftingTheory.vecB W T₁ b₁ c₀ + W.π₀ • z₁ ∧
      size c + S ≤ (PD.p - 1) * R₀ ∧ 1 ≤ R₀ ∧ ((σ₁ : ℝ) ≤ ((size c + S : ℕ) : ℝ) / ((PD.p : ℝ) - 1) + 1) ∧
      (∀ r < R₀, ∀ m, algebraMap O LL (yy r m) = (PD.p : LL) ^ κ₁ * ∑ k, algebraMap O LL (c₀ k) * sol₁ k r m) ∧
      X₁ = ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T₁ b₁ (yy r) ∧
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) X₁ ∧ Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x₁ ∧ W.γ T₁ X₁ - X₁ = W.π₀ ^ R₀ • x₁ ∧
      InFP W T₁ (c - 1) 1 1 y₁ ∧ InFP W T₁ (c - 1) 1 1 Z ∧
      lA W ^ κ₁ • y₁ + (W.π₀ * qA W ^ (size c + S)) • Z = lA W ^ σ₁ • W.φD T₁ X₁ := by
  obtain ⟨hp11, ⟨-, -, hηs, -⟩, -⟩ := hB
  have hl5 : 5 ≤ PD.p := by omega
  have hR := Formalism.MainNotions.N.FrobeniusPowerSeries.GS.ringData_of_caseA_of_p9 W hcase hP9
  obtain ⟨d₁, b₁, sol₁, hb₁⟩ := hHF hcase hl5 _ hOK T₁ hW₁ (c - 1)
  obtain ⟨c₀, z₁, R₀, σ₁, κ₁, yy, X₁, x₁, y₁, Z, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.DYAc.build W hcase hR hH hOv hinj hW₁.1 (c - 1) b₁ sol₁ hb₁ n₁ hn₁ (size c + S)
      (by have := hηs c; omega) hl5
  exact ⟨d₁, b₁, sol₁, c₀, z₁, R₀, σ₁, κ₁, yy, X₁, x₁, y₁, Z, hb₁, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13⟩

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

theorem arc_length_three_first_lift [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (n₁ : W.DD T₁) (E : ℕ) (hn₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) n₁)
    (hmap : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) ∧ W.map F n₁ = (((PD.p : ℕ) : LetA O n) ^ E) • (s • lam)) :
    ∃ (y₁ : W.DD T₁) (σ₁ : ℕ), ((σ₁ : ℝ) ≤ ((size c + S : ℕ) : ℝ) / ((PD.p : ℝ) - 1) + 1) ∧
      InFP W T₁ (c - 1) 1 1 y₁ ∧ InI W T₁ c y₁ ∧ InFNc W T₁ c 1 (qA W ^ (size c + S) • y₁) ∧
      ∃ g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}, ∃ κ' : ℕ,
        InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) (lA W ^ κ' • g • (lA W ^ (size (c - 1) + κ) • W.map F y₁ -
          lA W ^ (σ₁ + E + (arcOf b w S η up size).σ PD.p + size (c - 2) + S) • ((W.φD T₂) ^ 3) Hh)) := by
  obtain ⟨d, b₁, sol₁, c₀, z₁, R₀, σ₁, κ₁, yy, X₁, x₁, y₁, Z, hb₁, hz₁, hn₁c, hR₀, hR₁, hσ₁, hyy, hX₁e, hX₁, hx₁, hγX, hy₁, hZ, hrel⟩ :=
    arc_length_three_build_first_lift W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hP5 Cb hCb halt hsm hlen hD hOK hσ hy lam hlam hlamγ κ Hh hHh h4a n₁ E hn₁ hmap
  obtain ⟨hI, hFc⟩ := arc_length_three_gamma_first_lift W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hP5 Cb hCb halt hsm hlen hD hOK hσ hy lam hlam hlamγ κ Hh hHh h4a n₁ E hn₁ hmap R₀ σ₁ κ₁ X₁ x₁ y₁ Z hR₀ hR₁ hX₁ hx₁ hγX hy₁ hZ hrel
  obtain ⟨g, hg, κ', hcong⟩ := arc_length_three_congruence_lift W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hP5 Cb hCb halt hsm hlen hD hOK hσ hy lam hlam hlamγ κ Hh hHh h4a n₁ E hn₁ hmap d b₁ sol₁ c₀ z₁ R₀ σ₁ κ₁ yy X₁ x₁ y₁ Z hb₁ hz₁ hn₁c hR₀ hR₁ hyy hX₁e hX₁ hx₁ hγX hy₁ hZ hrel
  exact ⟨y₁, σ₁, hσ₁, hy₁, hI, hFc, g, hg, κ', hcong⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
