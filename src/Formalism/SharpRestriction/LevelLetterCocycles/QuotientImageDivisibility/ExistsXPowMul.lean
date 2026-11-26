module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Pi0PowSmulInjective

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem exists_X_pow_mul (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (w : ℕ) (u : PowerSeries LL), PowerSeries.constantCoeff u ≠ 0 ∧ f = PowerSeries.X ^ w * u := by
  have hex : ∃ w, PowerSeries.coeff w f ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (PowerSeries.ext fun w => by simpa using h w)
  obtain ⟨w, h1, hmin⟩ : ∃ w, PowerSeries.coeff w f ≠ 0 ∧ ∀ m < w, PowerSeries.coeff m f = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by
      have := Nat.find_min hex hm
      push Not at this
      exact this⟩
  have hdvd : PowerSeries.X ^ w ∣ f := PowerSeries.X_pow_dvd_iff.2 hmin
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨w, u, ?_, hu⟩
  rw [hu, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h1
  exact h1

theorem smulS_div {m : ℤ} {e : ℤ → V} (he : LB m e) (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (m' : ℤ) (d : ℤ → V), LB m' d ∧ smulS f d = e := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  set e' : ℤ → V := fun k => e (k + w) with he'
  have hLB' : LB (m - w) e' := fun k hk => he _ (by omega)
  refine ⟨m - w, smulS u⁻¹ e', LB_smulS hLB' _, ?_⟩
  rw [smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ hu,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

theorem smulS_inj {m : ℤ} {d d' : ℤ → V} (hd : LB m d) (hd' : LB m d') (f : PowerSeries LL)
    (hf : f ≠ 0) (h : smulS f d = smulS f d') : d = d' := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  have h0 : smulS (PowerSeries.X ^ w * u) (d - d') = 0 := by
    rw [smulS_sub hd hd', h, sub_self]
  rw [smulS_mul (LB_sub hd hd'), smulS_X_pow (LB_smulS (LB_sub hd hd') _)] at h0
  have h1 : smulS u (d - d') = 0 := by
    funext k
    have := congrFun h0 (k + w)
    simpa using this
  have h2 := smulS_inv (LB_sub hd hd') u hu
  rw [h1] at h2
  have h3 : smulS u⁻¹ (0 : ℤ → V) = 0 := by
    funext k
    simp [smulS]
  rw [h3] at h2
  exact sub_eq_zero.1 h2.symm

theorem smulS_comm {m : ℤ} {d : ℤ → V} (hd : LB m d) (f g : PowerSeries LL) :
    smulS f (smulS g d) = smulS g (smulS f d) := by
  rw [← smulS_mul hd, ← smulS_mul hd, mul_comm]

theorem smulS_mem {m : ℤ} {d : ℤ → V} (hd : LB m d) (D : Submodule LL V) (hD : ∀ k, d k ∈ D)
    (f : PowerSeries LL) (k : ℤ) : smulS f d k ∈ D := by
  have := Dg_smulS (Fil := fun _ : ℤ => D) (fun _ _ _ => le_rfl) hd (s := 0)
    (fun k => hD k) f k
  simpa using this

end Div

section Exp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem conv_eq {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv f d = smulS f d := rfl

theorem p_ne_zero_LL (W' : LocWach PD LL O v n) : (PD.p : LL) ≠ 0 := by
  intro h
  have := W'.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this

theorem eat_qp :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      Formalism.MainNotions.LiftingTheory.qp W := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀]

theorem expRing_of (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := by
  intro hA i ζ hζ
  have hs : W.s = 1 := hA.2.1
  have hp := p_ne_zero_LL W
  obtain ⟨u₀, hu₀, hq⟩ := MC.lev_q_eq W i hζ hp
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [eat_qp] at hw

  have hqp : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W) =
      (W.lev i ζ ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * u₀) * PowerSeries.X := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
      rw [hw, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e, map_mul, hq]
    ring
  have hunit : IsUnit (W.lev i ζ ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * u₀) :=
    ((Units.isUnit _).map _).mul
      (PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 hu₀))
  have hcq : PowerSeries.constantCoeff (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W)) = 0 := by
    rw [hqp, map_mul, PowerSeries.constantCoeff_X, mul_zero]
  have hcpi : PowerSeries.constantCoeff (W.lev i ζ W.π₀) = -(PD.p : LL) := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = W.π₀ + ((PD.p : ℕ) : LetA O n) := rfl
    rw [e, map_add (f := _), map_natCast, map_add (f := _), map_natCast] at hcq
    linear_combination hcq
  refine ⟨⟨_, hunit, hqp⟩, hcpi, ?_⟩

  obtain ⟨w', hw'⟩ := hR.2.2.2.2.2.1
  rw [eat_qp] at hw'
  have hp1 : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
  have hcφ : PowerSeries.constantCoeff (W.lev i ζ (W.φA W.π₀)) = 0 := by
    rw [hw', map_mul, map_mul, map_pow, map_mul, map_mul, map_pow, hcq,
      zero_pow (by omega), mul_zero]
  have e2 : Formalism.MainNotions.LiftingTheory.pk W 1 = W.φA W.π₀ + ((PD.p : ℕ) : LetA O n) := by
    simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, map_natCast]
  rw [e2, PowerSeries.isUnit_iff_constantCoeff, map_add (f := _), map_natCast, map_add (f := _), hcφ, zero_add,
    map_natCast]
  exact isUnit_iff_ne_zero.2 hp

def GamN : Prop :=
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : ↥(W.N T)) (hx : W.γ T (x : W.DD T) ∈ W.N T) (k : ℤ),
      W.levN T i ζ ⟨W.γ T x, hx⟩ k = (algebraMap O LL (W.χΓ W.gam : O)) ^ k • W.levN T i ζ x k

def GamA : Prop :=
  ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ f : LetA O n,
    W.lev i ζ (W.γA W.gam f) = PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev i ζ f)

theorem gam_of_tie (hs : W.s = 1) {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) : GamN W ∧ GamA W := by
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - ((1 : ℕ) : LL)) := by
    simp only [Nat.cast_one]
    rw [W.gam_gen, hs, Nat.cast_one]
  refine ⟨fun T hT i ζ hζ x hx k => ?_, fun i ζ hζ f => ?_⟩
  · rw [C.levN_eq, C.levN_eq]
    have e := C.levB_Γ T hT W.gam i ζ ζ 1 1 (by rwa [pow_one]) hv (by rw [pow_one]) x hx k
    have e' : (⟨W.γ T x, hx⟩ : ↥(W.N T)) = ⟨W.γD T W.gam x, hx⟩ := rfl
    rw [e', e, map_smul]
  · exact C.lev_Γ W.gam i ζ ζ 1 1 (by rwa [pow_one]) hv (by rw [pow_one]) f

end Exp

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsInIInPNPowSmulSubMap
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Core

variable (W : LocWach PD LL O v n)

theorem qp_mem_AΔ (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ :=
  W.AΔ.add_mem hR.1 (W.AΔ.natCast_mem _)

theorem inI_qpphi [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    {c : ZMod n} {kB : ℕ} (hM : ∀ z ∈ W.Nl T (c - 1), W.Q ^ kB • W.φD T z ∈ W.N T)
    {x : W.DD T} (hxN : x ∈ W.N T) (hxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) x) (pad : ℕ) :
    Formalism.MainNotions.CrystallineLiftingInputs.InI W T c (((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T x)) := by
  obtain ⟨hN, -⟩ := cmp_qpphi W T hs hR h3 hM hxN hxD.1
  set z := ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T x) with hz
  have hzN : z ∈ W.N T := by
    rw [hz, ← algebraMap_smul (LetA O n)]; exact (W.N T).smul_mem _ hN
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T δ z = z := by
    intro δ hδ
    rw [hz, map_smul, Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', ← W.φγ_comm, hxD.2 δ hδ,
      (W.AΔ.pow_mem (qp_mem_AΔ W hR) kB) δ hδ]
  have hzl : (letE c : LetA O n) • z = z := by
    rw [hz, osmul_comm W T, aself_comm W T, letter_phi W T c hxD.1]
  refine ⟨⟨hzl, hzΔ⟩, ⟨0, 0, by simpa using hzN⟩, ?_⟩
  obtain ⟨x', hx', he⟩ := hmod.2 z ⟨hzN, hzΔ⟩
  exact ⟨x', hx'.1, hx'.2, by rw [pow_one]; exact he⟩

theorem exists_inI_inPN_pow_smul_sub_map [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (h3₁ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₁) (h3₂ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₂)
    (hmod₁ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₁ W.π₀) (hmod₂ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₂ W.π₀)
    {c : ZMod n} {kB : ℕ}
    (hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ kB • W.φD T₁ z ∈ W.N T₁)
    (hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ kB • W.φD T₂ z ∈ W.N T₂)
    {y : W.DD T₂} (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) {d1 d2 d3 : T₂.V ⊗[Qp] B}
    {s₁ s₂ bb hh e pad : ℕ} {k : ℤ}
    (h1 : (PD.p : LL) ^ s₁ • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y =
      (PD.p : LL) ^ kB • φVB PD (LL := LL) (V := T₂.V) d1)
    (h2 : (PD.p : LL) ^ bb • d1 = φVB PD (LL := LL) (V := T₂.V) d2)
    (h3 : (PD.p : LL) ^ s₂ • d2 = (PD.p : LL) ^ hh • φVB PD (LL := LL) (V := T₂.V) d3)
    (hG : (PD.p : LL) ^ k • φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) d3) ∈
      Formalism.MainNotions.CrystallineLiftingInputs.DlatImg W F (c - 1))
    (hexp : (e : ℤ) + hh = pad + k + bb) :
    ∃ x : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c x ∧
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x) := by
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  obtain ⟨n', hn'N, hmN, hn'D, hcmp⟩ := hG
  set x := ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T₁ n') with hxdef
  refine ⟨x, inI_qpphi W hs hR T₁ h3₁ hmod₁ hM₁ hn'N hn'D pad, ?_⟩
  have hyN : y ∈ W.N T₂ := NDl_N W T₂ hy
  have hyl : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c y := NDl_DL W T₂ hy

  have hml : (letE (c - 1) : LetA O n) • W.map F n' = W.map F n' := by
    rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hn'D.1]
  obtain ⟨hqN, hqc⟩ := cmp_qpphi W T₂ hs hR h3₂ hM₂ hmN hml
  have hFx : W.map F x = ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T₂ (W.map F n')) := by
    rw [hxdef, Formalism.MainNotions.UnusedSlot80.ArcC.map_smulO, Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, W.map_φ]
  have hFxN : W.map F x ∈ W.N T₂ := by
    rw [hFx, ← algebraMap_smul (LetA O n)]; exact (W.N T₂).smul_mem _ hqN
  have hxI := inI_qpphi W hs hR T₁ h3₁ hmod₁ hM₁ hn'N hn'D pad
  have hFxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c (W.map F x) := by
    refine ⟨by rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hxI.1.1], fun δ hδ => ?_⟩
    rw [← W.map_γ, hxI.1.2 δ hδ]
  have hpyN : ((PD.p : O) ^ (e + s₁ + s₂)) • y ∈ W.N T₂ := by
    rw [← algebraMap_smul (LetA O n)]; exact (W.N T₂).smul_mem _ hyN
  have hzmem : ((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c :=
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).sub_mem ((Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).smul_mem _ hy) ⟨hFxN, hFxD⟩
  refine ker_NDl W T₂ c h3₂ hmod₂ hR hzmem ?_

  have hsub : Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x) =
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (((PD.p : O) ^ (e + s₁ + s₂)) • y) - Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (W.map F x) := by
    have := cmpD_add W T₂ ((W.N T₂).sub_mem hpyN hFxN) hFxN
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  rw [hsub, sub_eq_zero, cmpD_osmul W T₂ _ hyN, hFx, cmpD_osmul W T₂ _ hqN, hqc,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T₂ hmN, ← hcmp, map_pow, map_pow, map_natCast]

  have hsc : (PD.p : LL) ^ e * (PD.p : LL) ^ hh = (PD.p : LL) ^ bb * ((PD.p : LL) ^ pad * (PD.p : LL) ^ k) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hp,
      ← zpow_add₀ hp, ← zpow_add₀ hp]
    congr 1
    omega
  have key : (PD.p : LL) ^ (e + s₂) • d1 = ((PD.p : LL) ^ pad * (PD.p : LL) ^ k) •
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) d3) := by
    apply smul_right_injective _ (pow_ne_zero bb hp)
    simp only
    rw [smul_comm, h2, pow_add, mul_smul, ← map_smul, h3, map_smul, smul_smul, smul_smul, hsc]
  rw [pow_add, pow_add, mul_smul, mul_smul, smul_comm ((PD.p : LL) ^ s₁), h1, ← mul_smul,
    ← pow_add, smul_comm, ← map_smul, key, map_smul, map_smul, smul_smul]
  simp only [smul_smul]
  congr 1
  ring

end Core

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RhoLiftOf
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem rhoLift_of [NeZero n] (W : LocWach PD LL O v n) (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W)
    (hF : Formalism.MainNotions.CrystallineLiftingInputs.FTool W) (hK : W.ClKNat) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Formalism.MainNotions.RamifiedCoefficientChains.S9.RhoLift W := by
  intro d T₁ T₂ F b S η m hS c hc w u κ k hu hR hcong
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  have hn : Even n := hS.2.2.1
  obtain ⟨hc1, hc2, -⟩ := hS.2.2.2.2.2.1
  have hcE : (c.val + d) % 2 = 0 := (Finset.mem_filter.1 hc).2
  have hTC : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p 1 (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S)) η
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.sigC PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S) η) :=
    Or.inl ⟨rfl, Nat.le_add_left _ _, rfl⟩
  have T2 := hT2 hA hp11 1 _ η _ hTC

  have hwin : ∀ i a, a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i →
      -((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ) ≤ a := by
    intro i a ha
    have hbi : b i ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ i)
    have hη := rk_eta_lt W hS i
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    unfold Formalism.MainNotions.RamifiedCoefficientChains.hpar
    split_ifs at ha <;> simp only [Set.mem_union, Set.mem_Icc] at ha <;> push_cast at ha ⊢ <;> omega
  have hwinU : ∀ c' : ZMod n, (c'.val + d) % 2 = 0 → ∀ a,
      a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η (c' + 1) → -(η : ℤ) ≤ a := by
    intro c' hc' a ha
    have hpar' := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d c'
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    rw [if_neg (by omega)] at ha
    simp only [Set.mem_union, Set.mem_Icc] at ha
    push_cast at ha
    omega
  have hJ1 : ∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i →
      JumpsInV PD T₁.ρ τ (Set.Ici (-((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ))) :=
    fun i τ hτ a ha => hwin i a (hS.2.2.2.2.2.2.1 i τ hτ a ha)
  have hJ1U : ∀ (c' : ZMod n) τ, (c'.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c' + 1) →
      JumpsInV PD T₁.ρ τ (Set.Ici (-(η : ℤ))) :=
    fun c' τ hc' hτ a ha => hwinU c' hc' a (hS.2.2.2.2.2.2.1 (c' + 1) τ hτ a ha)
  have hJ2 : ∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i →
      JumpsInV PD T₂.ρ τ (Set.Ici (-((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ))) :=
    fun i τ hτ a ha => hwin i a (rk_jumps₂ W hE hC hQ hS i τ hτ a ha)
  have hJ2U : ∀ (c' : ZMod n) τ, (c'.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c' + 1) →
      JumpsInV PD T₂.ρ τ (Set.Ici (-(η : ℤ))) :=
    fun c' τ hc' hτ a ha => hwinU c' hc' a (rk_jumps₂ W hE hC hQ hS (c' + 1) τ hτ a ha)
  have F1 := hF d T₁ T₂ F b S η m hS T₁ hc1 hJ1 hJ1U
  have F2 := hF d T₁ T₂ F b S η m hS T₂ hc2 hJ2 hJ2U
  dsimp only at F1 F2
  obtain ⟨-, -, F1c3, F1c4, F1c5⟩ := F1
  obtain ⟨-, -, F2c3, F2c4, -⟩ := F2

  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hA.1).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  have hring := (((h9 T₁ hc1) hA.2.1 hA.2.2).2.2 hfin).1
  have hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := hring.1
  have hu0 : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1) := hring.2.2.1

  obtain ⟨hwI, hκ, z, x, htr, hx1, hx2, hcl⟩ := hR
  obtain ⟨zu, hzu⟩ := (T2.1 T₁ hc1 c).1 u hu
  obtain ⟨⟨xu, hxu1, hxu2⟩, -⟩ := F1c5 c u zu hcE hu hzu
  have hxuΔ := ((RL.mem_Z1DΔ_iff W T₁ _).1 xu.2).2
  have hxΔ := ((RL.mem_Z1DΔ_iff W T₂ _).1 x.2).2
  have hzuL : (letE (c + 1) : LetA O n) • zu = zu := RL.trunc_letter W T₁ c hu.1.1 hzu
  have hDLu : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₁ (c + 1) (xu : W.DD T₁ × W.DD T₁).1 := by
    refine ⟨by rw [hxu1]; exact hzuL, fun δ hδ => (hxuΔ δ hδ).1⟩
  have hPu : Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T₁ zu :=
    RL.trunc_polesFin W T₁ c η _ hu hzuL ((T2.1 T₁ hc1 c).2.1 u zu hu hzu).1
      (fun y hy hyl => F1c4 c y hcE hy hyl)
  have hH1f : W.clK T₁ xu ∈ latticeFiniteCohomology PD T₁.L := (F1c3 (c + 1) xu hDLu hxu2).2 (by rw [hxu1]; exact hPu)

  have hIu2 : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ c (W.map F u) := RL.inI_map W F hc1 hc2 hu
  obtain ⟨z2, hz2⟩ := (T2.1 T₂ hc2 c).1 _ hIu2
  obtain ⟨p1, hp1, e1⟩ := T2.2 T₁ T₂ F hc1 hc2 c u zu z2 hu hzu hz2
  have hIw3 : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ c (((PD.p : O) ^ k) • w + (-1 : O) • W.map F u) :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_add W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_smul W T₂ _ hwI)
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_smul W T₂ _ hIu2)
  obtain ⟨z3, hz3⟩ := (T2.1 T₂ hc2 c).1 _ hIw3
  obtain ⟨p2, hp2, e2⟩ := (T2.1 T₂ hc2 c).2.2.2.1 ((PD.p : O) ^ k) (-1) w (W.map F u) z z2 z3
    hwI hIu2 htr hz2 hz3
  have hw3PN : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ k) • w + (-1 : O) • W.map F u) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    exact hcong
  obtain ⟨p3, hp3, e3⟩ := (T2.1 T₂ hc2 c).2.2.2.2.1 _ z3 hIw3 hw3PN hz3
  have hD1 : ((PD.p : O) ^ k) • z - W.map F zu =
      Formalism.MainNotions.CrystallineLiftingInputs.fMX W (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S)) η • (p3 - p2 - p1) := by
    rw [smul_sub, smul_sub, ← e1, ← e2, ← e3, neg_one_smul]
    abel
  have hP : p3 - p2 - p1 ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ c 1 :=
    Submodule.sub_mem _ (Submodule.sub_mem _ hp3 hp2) hp1
  have hY : Formalism.MainNotions.LiftingTheory.qp W ^ η • (p3 - p2 - p1) ∈ W.N T₂ :=
    F2c4 c _ hcE (RL.pullJ_le_φpull W T₂ c hP) (RL.pullJ_letter W T₂ c hP)
  have hD1Δ : ∀ δ ∈ W.DelF, W.γD T₂ δ (((PD.p : O) ^ k) • z - W.map F zu) =
      ((PD.p : O) ^ k) • z - W.map F zu := by
    intro δ hδ
    rw [map_sub, map_smul, ← W.map_γ, ← hx1, (hxΔ δ hδ).1, ← hxu1, (hxuΔ δ hδ).1]
  have hD1PN : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S))
      (((PD.p : O) ^ k) • z - W.map F zu) :=
    RL.inPN_of_inv W T₂ hu0 hΔπ _ hY (by rw [hD1, Formalism.MainNotions.CrystallineLiftingInputs.fMX, mul_smul]) hD1Δ

  let yu : ↥(W.wachCocyclesDelta T₂) := ⟨_, RL.map_mem_Z1DΔ W F xu⟩
  have hnat : F.H1map (W.clK T₁ xu) = W.clK T₂ yu := hK F xu yu rfl
  have hdd1 : ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).1 =
      ((PD.p : O) ^ k) • z - W.map F zu := by
    simp [yu, hx1, hxu1]
  have hdd2 : ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).2 =
      ((PD.p : O) ^ k) • (x : W.DD T₂ × W.DD T₂).2 + (-1 : O) • W.map F (xu : W.DD T₁ × W.DD T₁).2 := by
    simp [yu, sub_eq_add_neg]
  have hDL2 : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (c + 1)
      ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).1 := by
    rw [hdd1]
    refine ⟨?_, hD1Δ⟩
    rw [smul_sub, smul_comm, RL.trunc_letter W T₂ c hwI.1.1 htr, ← RL.map_smulA, hzuL]
  have hPN2 : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S))
      ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).2 := by
    rw [hdd2]
    exact Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ _ hx2)
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ _ (RL.inPN_map W F hc1 hc2 hxu2))
  have hz0 : W.clK T₂ (((PD.p : O) ^ k) • x - yu) = 0 :=
    (F2c3 (c + 1) _ hDL2 hPN2).1 (by rw [hdd1]; exact hD1PN)
  have hcls : ((PD.p : O) ^ k) • W.clK T₂ x = F.H1map (W.clK T₁ xu) := by
    have e : W.clK T₂ (((PD.p : O) ^ k) • x - yu) =
        ((PD.p : O) ^ k) • W.clK T₂ x - W.clK T₂ yu :=
      ((W.clK T₂).map_sub _ _).trans (congrArg (· - W.clK T₂ yu) ((W.clK T₂).map_smul _ _))
    rw [e] at hz0
    rw [hnat]
    exact sub_eq_zero.1 hz0
  have hmk : (Submodule.Quotient.mk (((PD.p : O) ^ k) • (⟨κ, hκ⟩ : ↥(latticeCocycles T₂.L))) : LatticeCohomology T₂.L) =
      F.H1map (W.clK T₁ xu) := by
    rw [Submodule.Quotient.mk_smul, ← hcl, hcls]
  exact RL.mem_ImF_of_cls F _ ⟨_, hH1f, hmk.symm⟩

theorem rhoLift_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hT : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))],
      Formalism.MainNotions.CrystallineLiftingInputs.TTool2 ((HW l).W K 1 LL hg) ∧ Formalism.MainNotions.CrystallineLiftingInputs.FTool ((HW l).W K 1 LL hg)) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.rhoLift D HW F := by
  intro l _ K LL hg _
  intro d T₁ T₂ F' b S η m hS
  have h1 := hA.1 l K 1 LL hg
  have h11 := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have h17 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l K 1 LL hg
  have hp11 : 11 ≤ ((D.loc l).PD K).p := hS.2.1
  have hK : ((HW l).W K 1 LL hg).ClKNat := h17.2 fun h2 => absurd h2 (by omega)
  exact rhoLift_of _ (hT l K LL hg).1 (hT l K LL hg).2 hK h1.2.2.2.2.2.2.2.2.1 h11.1 h11.2.1
    h11.2.2 d T₁ T₂ F' b S η m hS

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end
