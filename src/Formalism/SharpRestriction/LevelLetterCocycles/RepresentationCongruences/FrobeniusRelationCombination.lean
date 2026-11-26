module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeInFPSmulPhiLambda
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeRepresentation

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InFNcOfInFPOfArcSigmaLe
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

theorem inFNc_of_inFP_of_arc_sigma_le [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    ∀ x : W.DD T₂, InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) x → InFNc W T₂ c 1 x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨qA W ^ (size c + S) • y, ?_, ?_, (one_smul _ _).symm⟩
  · refine DYB.Pp_qpow (W := W) T₂ (c - 1) (size c + S) ?_ hy
    intro z hz
    obtain ⟨-, hs, hp2⟩ := id hcase
    obtain ⟨hcr, hWj⟩ := id hW₂
    obtain ⟨-, -, h9one⟩ := hP9 T₂ hcr hs hp2
    obtain ⟨hring, -⟩ := h9one (NTB.finrank_one W hcase)
    obtain ⟨-, -, -, -, ⟨u, hu⟩, -⟩ := hring
    have hq : W.q = (u : LetA O n) * qA W := by
      rw [hu]
      congr 1
      funext i
      simp [DeltaInvariantLattices.Eat, qA, lA]
    have hQ : W.Q = W.q := by
      simp [LocWach.Q, hs]
    obtain ⟨-, hS, -⟩ := hB
    unfold TruncatedSeriesCountingBounds.HidaSetting at hS
    obtain ⟨-, -, hηs, -⟩ := hS
    have hJ : DeltaInvariantLattices.JumpsLet W T₂ (fun i => size i + S) (fun i => size i + S) := by
      intro τ i hτ a ha
      have h2 := hWj i τ hτ a ha
      have hη := hηs i
      cases hup : up i <;> simp [arcOf, hup, LocalTheoryWindows.LT.win] at h2 <;>
        simp only [Set.mem_Icc, Nat.cast_add] <;> omega
    have h5 : W.Q ^ (size c + S) • W.φD T₂ z ∈ W.N T₂ :=
      (hP5 T₂ (fun i => size i + S) (fun i => size i + S) hcr hJ).1 c z hz.2
    rw [hQ, hq] at h5
    have h6 := Submodule.smul_mem (W.N T₂) ((↑(u⁻¹) : LetA O n) ^ (size c + S)) h5
    rw [smul_smul, ← mul_pow, ← mul_assoc, Units.inv_mul, one_mul] at h6
    exact h6
  · have hH := DYB.Pp_le_HLD (W := W) T₂ (c - 1) hy
    obtain ⟨h, -⟩ := hH
    rw [sub_add_cancel] at h
    rw [smul_smul, mul_comm, ← smul_smul, h]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.QPowMemOfGenerator
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitOfResidueConstNeZero
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup PowerSeries

section PS

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {l : ℕ} [Fact l.Prime]

def residueConst : O⟦X⟧ →+* IsLocalRing.ResidueField O :=
  (IsLocalRing.residue O).comp (PowerSeries.constantCoeff (R := O))

theorem residueConst_apply (f : O⟦X⟧) :
    residueConst f = IsLocalRing.residue O (PowerSeries.constantCoeff f) := rfl

theorem residueConst_X_eq_zero : residueConst (X : O⟦X⟧) = 0 := by
  rw [residueConst_apply]
  simp

theorem residueConst_phi_eq (P : PhiData O l) (f : O⟦X⟧) : residueConst (P.φ f) = residueConst f := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hCa : ∀ a : O, P.φ (C a) = C a := by
    intro a
    first
    | exact P.φ.commutes a
    | simpa using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply'] using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply] using P.φ.commutes a
  have hX : residueConst (P.φ X) = 0 := by
    have h6 : P.φ (X - C (l : O)) = P.u * (X - C (l : O)) * X ^ (l - 1) := P.6
    rw [map_sub, hCa] at h6
    have h6' : P.φ X = P.u * (X - C (l : O)) * X ^ (l - 1) + C (l : O) := by rw [← h6]; ring
    rw [h6', map_add (f := _), map_mul, map_pow, residueConst_X_eq_zero, zero_pow (by omega), mul_zero, zero_add,
      residueConst_apply, PowerSeries.constantCoeff_C]
    exact (IsLocalRing.residue_eq_zero_iff _).2 P.4
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const f]
  rw [map_add (f := _), map_mul, map_add (f := _), map_mul, hX, mul_zero, zero_add, hCa]
  rw [residueConst_apply, residueConst_apply, PowerSeries.constantCoeff_C]

theorem level_poly_decomposition (P : PhiData O l) (s : ℕ) (hs : 1 ≤ s) :
    ∃ e h : O⟦X⟧, P.p s = C (l : O) * e + X ^ l * h ∧ residueConst e ≠ 0 := by
  unfold PhiData.p
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hCa : ∀ a : O, P.φ (C a) = C a := by
    intro a
    first
    | exact P.φ.commutes a
    | simpa using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply'] using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply] using P.φ.commutes a
  have hκC : residueConst (C (l : O)) = 0 := by
    rw [residueConst_apply, PowerSeries.constantCoeff_C]
    exact (IsLocalRing.residue_eq_zero_iff _).2 P.4
  have hκXl : residueConst ((X : O⟦X⟧) ^ l) = 0 := by
    rw [map_pow, residueConst_X_eq_zero, zero_pow (by omega)]
  have hmul : ∀ a b a' b' : O⟦X⟧, ∃ a'' b'' : O⟦X⟧,
      (C (l : O) * a + X ^ l * b) * (C (l : O) * a' + X ^ l * b') = C (l : O) * a'' + X ^ l * b'' ∧
      residueConst a'' = 0 := by
    intro a b a' b'
    refine ⟨a * C (l : O) * a' + a * X ^ l * b' + X ^ l * b * a', X ^ l * b * b', by ring, ?_⟩
    simp only [map_add (f := _), map_mul, hκC, hκXl, mul_zero, zero_mul, add_zero]
  have hpow : ∀ a b : O⟦X⟧, ∀ m, 2 ≤ m → ∃ a' b' : O⟦X⟧,
      (C (l : O) * a + X ^ l * b) ^ m = C (l : O) * a' + X ^ l * b' ∧ residueConst a' = 0 := by
    intro a b m hm
    induction m, hm using Nat.le_induction with
    | base => rw [pow_two]; exact hmul a b a b
    | succ m hm ih =>
      obtain ⟨a', b', he, hk⟩ := ih
      obtain ⟨a'', b'', he', hk'⟩ := hmul a' b' a b
      exact ⟨a'', b'', by rw [pow_succ, he, he'], hk'⟩
  have hXl : (X : O⟦X⟧) ^ l = X * X ^ (l - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h6 : P.φ (X - C (l : O)) = P.u * (X - C (l : O)) * X ^ (l - 1) := P.6
  rw [map_sub, hCa] at h6
  have hφX : P.φ X = C (l : O) * (1 - P.u * X ^ (l - 1)) + X ^ l * P.u := by
    have h6' : P.φ X = P.u * (X - C (l : O)) * X ^ (l - 1) + C (l : O) := by rw [← h6]; ring
    rw [h6', hXl]
    ring
  induction s, hs using Nat.le_induction with
  | base =>
    refine ⟨1 - P.u * X ^ (l - 1), P.u, by rw [Function.iterate_one, hφX], ?_⟩
    rw [map_sub, map_one, map_mul, map_pow, residueConst_X_eq_zero, zero_pow (by omega), mul_zero, sub_zero]
    exact one_ne_zero
  | succ s hs ih =>
    obtain ⟨e, h, he, hk⟩ := ih
    obtain ⟨a', b', hab, hka⟩ := hpow (1 - P.u * X ^ (l - 1)) P.u l hl2
    refine ⟨P.φ e + a' * P.φ h, b' * P.φ h, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', he, map_add (f := _), map_mul, map_mul, hCa, map_pow, hφX, hab]
      ring
    · rw [map_add (f := _), map_mul, hka, zero_mul, add_zero, residueConst_phi_eq]
      exact hk

theorem isUnit_of_residueConst_ne_zero {e : O⟦X⟧} (hκ : residueConst e ≠ 0) : IsUnit e := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [residueConst_apply] at hκ
  by_contra h
  exact hκ ((IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h))

theorem l_pow_mem_span_level_X_pow (P : PhiData O l) (s : ℕ) (hs : 1 ≤ s) (B : ℕ) :
    ∃ a b : O⟦X⟧, C (l : O) ^ B = a * P.p s + b * X ^ B := by
  obtain ⟨e, h, hp, he⟩ := level_poly_decomposition P s hs
  obtain ⟨u, hu⟩ := isUnit_of_residueConst_ne_zero he
  obtain ⟨k, hk⟩ := sub_dvd_pow_sub_pow (C (l : O) * e) (-(X ^ l * h)) B
  rw [sub_neg_eq_add, ← hp] at hk
  have hl : B ≤ l * B := Nat.le_mul_of_pos_left B (Fact.out : l.Prime).pos
  refine ⟨k * (↑u⁻¹ : O⟦X⟧) ^ B, X ^ (l * B - B) * (-h) ^ B * (↑u⁻¹ : O⟦X⟧) ^ B, ?_⟩
  have hy : (-(X ^ l * h) : O⟦X⟧) ^ B = X ^ (l * B - B) * (-h) ^ B * X ^ B := by
    rw [mul_assoc, mul_comm ((-h) ^ B), ← mul_assoc, ← pow_add, Nat.sub_add_cancel hl, pow_mul,
      ← mul_pow, neg_mul_eq_mul_neg]
  have hue : (C (l : O) * e) ^ B * (↑u⁻¹ : O⟦X⟧) ^ B = C (l : O) ^ B := by
    rw [← mul_pow, mul_assoc, ← hu, Units.mul_inv, mul_one]
  calc C (l : O) ^ B = (C (l : O) * e) ^ B * (↑u⁻¹ : O⟦X⟧) ^ B := hue.symm
    _ = (P.p s * k + (-(X ^ l * h)) ^ B) * (↑u⁻¹ : O⟦X⟧) ^ B := by rw [← hk, sub_add_cancel]
    _ = _ := by rw [hy]; ring

end PS

section Bridge

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem powerSeriesConst_add {W : LocWach PD LL O v n} (Br : PhiBridge W) (F F' : PowerSeries O) :
    Br.cst (F + F') = Br.cst F + Br.cst F' := by
  unfold PhiBridge.cst
  funext x
  first
  | exact map_add Br.ι F F'
  | exact Br.ι.map_add F F'
  | simp

theorem l_pow_mem_levels_q_pow_ideal {W : LocWach PD LL O v n} (Br : PhiBridge W) (Bq : ℕ) {g : LetA O n}
    (hg : g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}) :
    g ∈ W.AΔ ∧ ∃ N : ℕ, ∃ a ∈ W.AΔ, ∃ b ∈ W.AΔ, lA W ^ N = a * g + b * qA W ^ Bq := by
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  have key : ∃ F : PowerSeries O, g = Br.cst F ∧
      ∃ N : ℕ, ∃ a b : PowerSeries O, C ((PD.p : ℕ) : O) ^ N = a * F + b * X ^ Bq := by
    induction hg using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨a, b, hab⟩ := l_pow_mem_span_level_X_pow Br.P k hk Bq
      exact ⟨Br.P.p k, Br.ps_eq k, Bq, a, b, hab⟩
    | one =>
      exact ⟨1, Br.cst_one.symm, 0, 1, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨F₁, rfl, N₁, a₁, b₁, h₁⟩ := hx
      obtain ⟨F₂, rfl, N₂, a₂, b₂, h₂⟩ := hy
      refine ⟨F₁ * F₂, (Br.cst_mul F₁ F₂).symm, N₁ + N₂, a₁ * a₂,
        b₁ * a₂ * F₂ + a₁ * F₁ * b₂ + b₁ * b₂ * X ^ Bq, ?_⟩
      rw [pow_add, h₁, h₂]
      ring
  obtain ⟨F, rfl, N, a, b, h⟩ := key
  refine ⟨Br.cst_mem F, N, Br.cst a, Br.cst_mem a, Br.cst b, Br.cst_mem b, ?_⟩
  rw [Br.lA_eq, Br.qA_eq, ← Br.cst_pow, ← Br.cst_pow, ← Br.cst_mul, ← Br.cst_mul,
    ← powerSeriesConst_add, h]

end Bridge

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

theorem q_pow_mem_of_generator [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    {T : LocLat G Qp LL O} (hT : IsCrys PD T.ρ) (i : ZMod n) (Bq : ℕ) (g : LetA O n) (hg : g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k})
    (x : W.DD T) (hx : InFP W T i 1 1 x) (hgx : ∃ k : ℕ, InFP W T i 1 (qA W ^ Bq) (lA W ^ k • g • x)) :
    InFP W T i 1 (qA W ^ Bq) x := by

  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T hT hO hinj
  obtain ⟨-, N, a, ha, b, hb, hN⟩ := l_pow_mem_levels_q_pow_ideal Br Bq hg
  obtain ⟨k, z, hz, hkz⟩ := hgx
  have hx1 : x ∈ Pp W T i 1 := by
    obtain ⟨y, hy, hxy⟩ := hx
    rw [hxy, one_smul]
    exact hy
  have hlx : lA W ^ k • x ∈ Pp W T i 1 := by
    rw [show lA W ^ k = ((PD.p ^ k : ℕ) : LetA O n) by simp [lA], Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx1 _
  have hqPi : qA W ^ Bq ∈ PiPs W := by
    apply Submonoid.pow_mem
    unfold PiPs
    exact Submonoid.subset_closure (Set.mem_insert_of_mem _ ⟨0, by simp [ps]⟩)
  have h1 : InFP W T i 1 1 ((1 : LetA O n) • x) := by
    rw [one_smul]
    exact hx

  have key : lA W ^ (k + N) • x = qA W ^ Bq • (a • z + b • (lA W ^ k • x)) := by
    calc lA W ^ (k + N) • x = (a * g + b * qA W ^ Bq) • (lA W ^ k • x) := by
          rw [← hN, smul_smul, ← pow_add, Nat.add_comm k N]
      _ = a • (lA W ^ k • g • x) + b • (qA W ^ Bq • (lA W ^ k • x)) := by
          rw [add_smul, mul_smul, mul_smul, smul_comm g (lA W ^ k) x]
      _ = qA W ^ Bq • (a • z + b • (lA W ^ k • x)) := by
          rw [hkz, smul_add, smul_comm a, smul_comm b]
  have hmem : a • z + b • (lA W ^ k • x) ∈ Pp W T i 1 :=
    add_mem (DYB.Pp_smul W T i ha hz) (DYB.Pp_smul W T i hb hlx)
  exact hSatP hcase T i 1 (qA W ^ Bq) 1 hT hqPi (one_mem _) x h1
    ⟨k + N, by unfold InFP; exact ⟨_, hmem, key⟩⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeMapLattice
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

theorem arc_length_three_map_lattice [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    ∀ x : W.DD T₁, InFP W T₁ (c - 1) 1 1 x → InFP W T₂ (c - 1) 1 1 (W.map F x) := by
  rintro x ⟨y, hy, rfl⟩
  have hN : ∀ x' : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x' → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (W.map F x') := by
    intro x' hx'
    refine ⟨TypesA.map_NΔ W F hW₁.1 hW₂.1 hx'.1, ?_⟩
    obtain ⟨m, hm, hmx⟩ := Submodule.mem_map.1 hx'.2
    refine Submodule.mem_map.2 ⟨W.map F m, W.map_N F hW₁.1 hW₂.1 m hm, ?_⟩
    rw [← hmx]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [TypesA.map_smulA]
  have h : Pp W T₁ (c - 1) 1 ≤ (Pp W T₂ (c - 1) 1).comap (W.map F).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, x', hx', rfl⟩
    show W.map F (a • ((W.φD T₁) ^ 1) x') ∈ Pp W T₂ (c - 1) 1
    rw [pow_one, TypesA.map_smulA, W.map_φ]
    exact AddSubgroup.subset_closure ⟨a, ha, W.map F x', hN x' hx', by rw [pow_one]⟩
  refine ⟨W.map F y, h hy, ?_⟩
  rw [one_smul, one_smul]

theorem arc_length_three_annihilate [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    ∀ u : W.DD T₂, InFNc W T₂ c 1 u → ∃ u₁ : W.DD T₁, InFNc W T₁ c 1 u₁ ∧ InI W T₁ c u₁ ∧
      W.map F u₁ = lA W ^ rr • u := by
  rintro u ⟨y, hy, hyc, rfl⟩
  have hT₁ : IsCrys PD T₁.ρ := hW₁.1
  obtain ⟨h9c, -⟩ := NTB.p9mod_of W hcase hP9 T₁ hT₁
  have hΔ : IsUnit (((PD.p - 1 : ℕ) : O)) := by
    rw [← h9c]; exact (lemG_units W hcase hP9 hT₁ hO hOv hinj).2.2
  obtain ⟨x, hx, hxc, hFx⟩ := NTB.delta_lift W hcase hP9 F hT₁ hΔ c rr (hkill c hc) hy hyc
  refine ⟨x, ⟨x, hx, hxc, (one_smul _ _).symm⟩, NTB.InI_of_N W hcase hP9 hT₁ c hx hxc, ?_⟩
  rw [hFx, one_smul]
  rfl

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 TypesA

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem frobenius_relation_combination {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (L q g₁ g₂ t B' aX : R)
    (κ₂ κ₁' κ₀ κ b₁ σ σ₁ E w S : ℕ) (V FY Φ y₂ y₃ : M)
    (h₂ : L ^ κ₂ • g₂ • (L ^ (κ₀ + κ) • V - L ^ σ • aX • Φ) = q • y₂)
    (h₃ : L ^ κ₁' • g₁ • (L ^ (b₁ + κ) • FY - L ^ (σ₁ + E + σ + w + S) • Φ) = q • y₃)
    (hrel : t * aX * L ^ b₁ = B' * L ^ (κ₀ + σ₁ + E + w + S)) :
    L ^ (κ₂ + κ₁' + κ₀ + κ + b₁) • (g₁ * g₂) • (t • V - B' • FY) =
      q • ((g₁ * t * L ^ (κ₁' + b₁)) • y₂ - (g₂ * B' * L ^ (κ₂ + κ₀)) • y₃) := by
  have hrelV : (t * aX * L ^ b₁) • Φ = (B' * L ^ (κ₀ + σ₁ + E + w + S)) • Φ := by rw [hrel]
  linear_combination (norm := module) (g₁ * t * L ^ (κ₁' + b₁)) • h₂ - (g₂ * B' * L ^ (κ₂ + κ₀)) • h₃ +
    (g₁ * g₂ * L ^ (κ₁' + κ₂) * L ^ σ) • hrelV

theorem arc_length_three_final_bound [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
      (lE W κ₀ * f₂ - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₀))
    (hx0 : ∀ r : ℚ, v (algebraMap O LL X₀) = ((r : ℚ) : WithTop ℚ) →
      ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c + S : ℕ) : ℝ) / PD.p - ((size c + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 - 2 -
        Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ))) + κ₀ ≤ (r : ℝ))
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (n₁ : W.DD T₁) (E : ℕ) (hn₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) n₁)
    (hmap : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) ∧ W.map F n₁ = (((PD.p : ℕ) : LetA O n) ^ E) • (s • lam)) (hE : (E : ℝ) ≤ 8 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (y₁ : W.DD T₁) (σ₁ : ℕ) (hy₁ : ((σ₁ : ℝ) ≤ ((size c + S : ℕ) : ℝ) / ((PD.p : ℝ) - 1) + 1) ∧
      InFP W T₁ (c - 1) 1 1 y₁ ∧ InI W T₁ c y₁ ∧ InFNc W T₁ c 1 (qA W ^ (size c + S) • y₁) ∧
      ∃ g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}, ∃ κ' : ℕ,
        InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) (lA W ^ κ' • g • (lA W ^ (size (c - 1) + κ) • W.map F y₁ -
          lA W ^ (σ₁ + E + (arcOf b w S η up size).σ PD.p + size (c - 2) + S) • ((W.φD T₂) ^ 3) Hh))) :
    ∃ (e : ℕ) (t₃ : O), (e : ℝ) ≤ 6 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
      (∃ r : ℚ, v (algebraMap O LL t₃) = ((r : ℚ) : WithTop ℚ) ∧ (r : ℝ) ≤ 14 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size) ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ (algebraMap O W.EE t₃ * f₂) e := by
  classical
  obtain ⟨hσ₁, hy₁P, hy₁I, hy₁N, g₁, hg₁, κ₁', hY⟩ := hy₁
  have hn₂ : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) :=
    fun s h => (hmap s h).1
  obtain ⟨hv₂P, g₂, hg₂, κ₂, hV⟩ := arc_length_three_inFP_smul_phi_lambda W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy f₂ hf₂ κ₀ X₀ hX₀ lam hlam hlamγ κ Hh hHh h4a hn₂
  obtain ⟨⟨a₀, ha₀, hΛf⟩, hφl, hrep⟩ := arc_length_three_representation W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy f₂ hf₂ lam hlam hlamγ κ Hh hHh h4a

  have hB' := hB
  obtain ⟨hl11, hSet, -, hη20, hS20, -⟩ := hB'
  have hthick : ∀ d : ℕ, 1 ≤ d → d < 3 → Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1) := by
    intro d hd1 hd3
    by_contra hnt
    have hmem : d ∈ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := ⟨hd1, hnt⟩
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
  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
    rw [if_pos ⟨c - 1, ht1⟩]
  have hSgEq : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    unfold Formalism.MainNotions.N.Ln17.Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg
    rw [hhB]
  have hp : (11 : ℝ) ≤ (PD.p : ℝ) := by exact_mod_cast hl11

  set σ := (arcOf b w S η up size).σ PD.p with hσdef
  set D₁ : ℕ := κ₀ + σ₁ + E + size (c - 2) + S with hD₁
  have hvp : v ((PD.p : ℕ) : LL) = 1 := by exact_mod_cast W.v_l
  have hp0 : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hvp; exact WithTop.top_ne_coe hvp
  obtain ⟨t₃, B', hrel, r₃, hr₃, hr₃b⟩ : ∃ t₃ B' : O,
      t₃ * X₀ * ((PD.p : ℕ) : O) ^ size (c - 1) = B' * ((PD.p : ℕ) : O) ^ D₁ ∧
      ∃ r : ℚ, v (algebraMap O LL t₃) = ((r : ℚ) : WithTop ℚ) ∧ (r : ℝ) ≤ 14 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
    have hvcalc : ∀ (k : ℕ) (x : LL) (r : ℚ), v x = ((r : ℚ) : WithTop ℚ) →
        v (((PD.p : ℕ) : LL) ^ k * x⁻¹) = ((((k : ℚ) - r) : ℚ) : WithTop ℚ) := by
      intro k x r hr
      rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_inv, hvp, hr]
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
        nsmul_one, sub_eq_add_neg]
    have hσ0 : (0 : ℝ) ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
      have : (0 : ℝ) ≤ (σ : ℝ) := Nat.cast_nonneg _
      linarith [hσ]
    by_cases hX : X₀ = 0
    · refine ⟨1, 0, by rw [hX]; ring, 0, ?_, ?_⟩
      · rw [map_one, AddValuation.map_one, WithTop.coe_zero]
      · push_cast; linarith
    have hXLL : algebraMap O LL X₀ ≠ 0 := fun h => hX (hinj (by rw [h, map_zero]))
    have hne : v (algebraMap O LL X₀) ≠ ⊤ := by
      intro h; exact hXLL ((AddValuation.top_iff v).1 h)
    obtain ⟨rX, hrX⟩ := WithTop.ne_top_iff_exists.1 hne
    have hrX0 : (0 : ℚ) ≤ rX := by
      have h0 := hO X₀; rw [← hrX] at h0; exact_mod_cast h0
    have hx0' := hx0 rX hrX.symm
    by_cases hlt : rX < ((D₁ + σ : ℕ) : ℚ) - (size (c - 1) : ℚ)
    · have hk : size (c - 1) ≤ D₁ + σ := by
        have : ((size (c - 1) : ℕ) : ℚ) ≤ ((D₁ + σ : ℕ) : ℚ) := by linarith
        exact_mod_cast this
      have hv1 := hvcalc (D₁ + σ - size (c - 1)) (algebraMap O LL X₀) rX hrX.symm
      obtain ⟨t₃, ht₃⟩ := hOv (((PD.p : ℕ) : LL) ^ (D₁ + σ - size (c - 1)) * (algebraMap O LL X₀)⁻¹) (by
        rw [hv1]
        have : (0 : ℚ) ≤ ((D₁ + σ - size (c - 1) : ℕ) : ℚ) - rX := by
          rw [Nat.cast_sub hk]; push_cast at hlt ⊢; linarith
        exact_mod_cast this)
      refine ⟨t₃, ((PD.p : ℕ) : O) ^ σ, ?_, ((D₁ + σ - size (c - 1) : ℕ) : ℚ) - rX, by rw [ht₃, hv1], ?_⟩
      · apply hinj
        simp only [map_mul, map_pow, map_natCast, ht₃]
        field_simp
        rw [← pow_add, ← pow_add, Nat.sub_add_cancel hk, add_comm]
      · have hb1 : 1 ≤ b := by
          have hh1 : 1 ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := hOK.2.2.2.2.2.2.1
          have hlog : 0 ≤ Real.logb PD.p (2 * ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℕ) : ℝ)) :=
            Real.logb_nonneg (by linarith) (by
              have : (1 : ℝ) ≤ ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℕ) : ℝ) := by exact_mod_cast hh1
              linarith)
          have hSg1 : 1 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
            unfold Formalism.MainNotions.N.Ln17.Sg
            have h1 : (0 : ℝ) ≤ ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 := by positivity
            have h2 : (0 : ℝ) ≤ ((w : ℝ) + S + η) / PD.p := by positivity
            linarith
          have : (160 : ℝ) ≤ b := by linarith [hsm]
          exact_mod_cast (by linarith : (1 : ℝ) ≤ b)
        have hAh : ((arcOf b w S η up size).h : ℕ) = b + η + S := hhB
        have hBle : ((size c + S : ℕ) : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by
          have := ht0.2
          exact_mod_cast (by omega : size c + S ≤ b + η + S)
        have hv' : ((size (c - 2) : ℝ) + S - size (c - 1)) + ((size c + S : ℕ) : ℝ) / PD.p -
            ((size c + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 - 2 - Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ)) ≤
            (rX : ℝ) - κ₀ := by
          rw [hAh] at hx0'; linarith
        have hE' : (E : ℝ) ≤ 8 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by rw [← hSgEq]; exact hE
        have hσ' : (σ : ℝ) ≤ 3 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by rw [← hSgEq]; exact hσ
        have h10 := Formalism.MainNotions.N.FrobeniusPowerSeries.sub_le_fourteen_mul_errorScale PD.p hl11 b w S η hb1 (σ₁ : ℝ) (E : ℝ) (σ : ℝ)
          ((size c + S : ℕ) : ℝ) (size (c - 2) : ℝ) (size (c - 1) : ℝ) ((rX : ℝ) - κ₀) (Nat.cast_nonneg _) hBle hσ₁
          hE' hσ' hv'
        rw [hSgEq]
        have hcast : ((D₁ + σ - size (c - 1) : ℕ) : ℝ) =
            (κ₀ : ℝ) + σ₁ + E + size (c - 2) + S + σ - size (c - 1) := by
          rw [Nat.cast_sub hk, hD₁]; push_cast; ring
        have hq : ((((D₁ + σ - size (c - 1) : ℕ) : ℚ) - rX : ℚ) : ℝ) =
            ((D₁ + σ - size (c - 1) : ℕ) : ℝ) - (rX : ℝ) := by push_cast; ring
        rw [hq, hcast]
        linarith
    · have hv2 : v (algebraMap O LL X₀ * ((PD.p : ℕ) : LL) ^ size (c - 1) * (((PD.p : ℕ) : LL) ^ D₁)⁻¹) =
          (((rX + size (c - 1) - D₁ : ℚ)) : WithTop ℚ) := by
        rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_inv,
          AddValuation.map_pow, hvp, ← hrX]
        rw [← WithTop.coe_one, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
          ← WithTop.coe_add, ← WithTop.coe_add, nsmul_one, nsmul_one]
        congr 1; ring
      obtain ⟨B', hB'⟩ := hOv (algebraMap O LL X₀ * ((PD.p : ℕ) : LL) ^ size (c - 1) * (((PD.p : ℕ) : LL) ^ D₁)⁻¹) (by
        rw [hv2]
        have : (0 : ℚ) ≤ rX + size (c - 1) - D₁ := by
          push_cast at hlt; push Not at hlt
          have : (0 : ℚ) ≤ (σ : ℚ) := Nat.cast_nonneg _
          linarith
        exact_mod_cast this)
      refine ⟨1, B', ?_, 0, ?_, ?_⟩
      · apply hinj
        simp only [map_mul, map_pow, map_natCast, map_one, hB']
        field_simp
      · rw [map_one, AddValuation.map_one, WithTop.coe_zero]
      · push_cast; linarith

  set V : W.DD T₂ := f₂ • W.φD T₂ lam with hVdef
  set Φ : W.DD T₂ := ((W.φD T₂) ^ 3) Hh with hΦdef
  set De : W.DD T₂ := algebraMap O (LetA O n) t₃ • V - algebraMap O (LetA O n) B' • W.map F y₁ with hDedef
  have hDeP : InFP W T₂ (c - 1) 1 1 De :=
    inMultiple_sub W (inMultiple_smul W (algebraMap_mem_invariants W t₃) hv₂P)
      (inMultiple_smul W (algebraMap_mem_invariants W B') (arc_length_three_map_lattice W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy y₁ hy₁P))
  have hPsA : ∀ g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}, g ∈ W.AΔ := by
    intro g hg
    refine (Submonoid.closure_le (S := W.AΔ.toSubmonoid)).2 ?_ hg
    rintro _ ⟨k, -, rfl⟩
    exact ps_mem W k
  have hDe0 : ∃ k : ℕ, InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) (lA W ^ k • (g₁ * g₂) • De) := by
    obtain ⟨y₂, hy₂, hy₂e⟩ := hV
    obtain ⟨y₃, hy₃, hy₃e⟩ := hY
    have hrelL : algebraMap O (LetA O n) t₃ * algebraMap O (LetA O n) X₀ * lA W ^ size (c - 1) =
        algebraMap O (LetA O n) B' * lA W ^ D₁ := by
      have := congrArg (algebraMap O (LetA O n)) hrel
      simpa only [map_mul, map_pow, map_natCast, lA] using this
    have hrelL' : algebraMap O (LetA O n) t₃ * algebraMap O (LetA O n) X₀ * lA W ^ size (c - 1) =
        algebraMap O (LetA O n) B' * lA W ^ (κ₀ + σ₁ + E + size (c - 2) + S) := by
      rw [hrelL, hD₁]
    rw [← algebraMap_smul_eq_smul W X₀ Φ] at hy₂e
    refine ⟨κ₂ + κ₁' + κ₀ + κ + size (c - 1),
      (g₁ * algebraMap O (LetA O n) t₃ * lA W ^ (κ₁' + size (c - 1))) • y₂ -
        (g₂ * algebraMap O (LetA O n) B' * lA W ^ (κ₂ + κ₀)) • y₃, ?_, ?_⟩
    · exact sub_mem
        (Pp_smul W (W.AΔ.mul_mem (W.AΔ.mul_mem (hPsA g₁ hg₁) (algebraMap_mem_invariants W t₃)) (lA_pow_mem W _)) hy₂)
        (Pp_smul W (W.AΔ.mul_mem (W.AΔ.mul_mem (hPsA g₂ hg₂) (algebraMap_mem_invariants W B')) (lA_pow_mem W _)) hy₃)
    · rw [hDedef]
      exact frobenius_relation_combination (lA W) (qA W ^ (size c + S)) g₁ g₂ (algebraMap O (LetA O n) t₃) (algebraMap O (LetA O n) B')
        (algebraMap O (LetA O n) X₀) κ₂ κ₁' κ₀ κ (size (c - 1)) σ σ₁ E (size (c - 2)) S V (W.map F y₁) Φ y₂ y₃
        hy₂e hy₃e hrelL'
  have hDeq := q_pow_mem_of_generator W hcase hP9 hSatP hO hOv hinj hW₂.1 (c - 1) (size c + S) (g₁ * g₂)
    (Submonoid.mul_mem _ hg₁ hg₂) De hDeP hDe0
  have hDeN := inFNc_of_inFP_of_arc_sigma_le W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy De hDeq
  obtain ⟨De₁, hDe₁N, hDe₁I, hFDe₁⟩ := arc_length_three_annihilate W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy De hDeN
  set tt : O := ((PD.p : ℕ) : O) ^ rr * B' with htt
  have hFw : W.map F (De₁ + algebraMap O (LetA O n) tt • y₁) =
      algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ rr * t₃) • V := by
    have hlA : lA W = algebraMap O (LetA O n) ((PD.p : ℕ) : O) := by simp [lA]
    rw [map_add (f := _), map_smulA W F, hFDe₁, hDedef, htt, map_mul, map_mul, map_pow, ← hlA]
    simp only [smul_sub, mul_smul]
    abel
  refine ⟨rr + σ, t₃, ?_, ⟨r₃, hr₃, hr₃b⟩, ?_⟩
  · push_cast; linarith [hrr, hσ]
  · have h0 : ps W 0 = qA W := by simp [ps]
    have hqA : qA W ∈ W.AΔ := h0 ▸ ps_mem W 0
    have hΛV : abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c) • V = a₀ • W.φD T₂ lam := by
      rw [hVdef, ← algebraMap_smul W.EE (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c)) (f₂ • W.φD T₂ lam), smul_smul, hΛf,
        algebraMap_smul]
    unfold LiftsAt
    refine ⟨De₁ + algebraMap O (LetA O n) tt • y₁, 0, InI_add W hDe₁I (inI_algebraMap_smul W tt hy₁I),
      ⟨qA W ^ (size c + S), ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [← h0]; exact Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_range_self (f := ps W) 0)) _
    · rw [smul_add]
      refine InFNc_add W (InFNc_smul W (W.AΔ.pow_mem hqA _) hDe₁N) ?_
      rw [smul_comm]
      exact InFNc_smul W (algebraMap_mem_invariants W tt) hy₁N
    · rw [hFw, smul_comm, hΛV]
      exact inMultiple_smul W (algebraMap_mem_invariants W _) (inMultiple_smul W ha₀ hφl)
    · exact ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩
    · rw [sub_zero, hFw]
      have h6 := repVV_smul_invariant W (algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ rr * t₃)) (algebraMap_mem_invariants W _) hrep
      refine RepVV_congr W h6 rfl fun k => ?_
      split_ifs
      · simp only [lE, ← IsScalarTower.algebraMap_apply, map_mul, map_pow, map_natCast]; ring
      · rw [mul_zero]

end Formalism.MainNotions.N.FrobeniusPowerSeries
