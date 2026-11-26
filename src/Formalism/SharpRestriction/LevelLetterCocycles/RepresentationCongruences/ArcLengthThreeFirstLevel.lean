module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsLiftMapEqPrimePowSmul
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RepVVSmulA
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsCyclotomicCharQuotient

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeHypSecond
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_hyp_second (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (A : ArcP n) (c : ZMod n) (hlen : A.len c = 3) {T₂ : LocLat G Qp LL O}
    (hT₂ : IsCrys PD T₂.ρ) (Mi' hi' : ZMod n → ℕ) (hJL : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ Mi' hi') {b₁ w' A₀ : ℕ}
    (hM1 : Mi' (c - 2) = w' + A.S) (hM2 : Mi' (c - 1) = A.η)
    (hN : b₁ + A₀ + A.η ≤ (PD.p - 1) * A.M PD.p) (hM : 1 ≤ A.M PD.p) (lam : W.DD T₂)
    (hlamγ : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)))
      (W.γ T₂ lam - lam))
    (s : W.EE) (hs : algebraMap (LetA O n) W.EE (qA W ^ b₁) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (w' + A.S))) :
    ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) y ∧
      W.γE W.gam s • (W.γ T₂ lam - lam) = (W.π₀ * qA W ^ A₀) • y := by
  classical
  have hR := GS.ringData_of_caseA_of_p9 W hcase hP9
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  have e1 : c - 2 - 1 = c' := by rw [hc', hlen]; push_cast; ring
  have e2 : c - 1 - 1 = c - 2 := by ring
  have e3 : c' + ((2 : ℕ) : ZMod n) = c - 1 := by rw [hc', hlen]; push_cast; ring
  have e4 : c' + ((1 : ℕ) : ZMod n) = c - 2 := by rw [hc', hlen]; push_cast; ring

  have hK : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hcase.1).finrank_eq, Module.finrank_self]
  have h9 := hP9 T₂ hT₂ hcase.2.1 hcase.2.2
  have hring := (h9.2.2 hK).1
  obtain ⟨wq, hwq⟩ := hring.2.2.2.2.1
  have hq : W.q = (wq : LetA O n) * qA W := by
    rw [hwq]
    congr 1
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  have hQ : W.Q = (wq : LetA O n) * qA W := by
    unfold LocWach.Q
    rw [hcase.2.1]
    simp [hq]
  have h5 := hP5 T₂ Mi' hi' hT₂ hJL
  have hφs : ∀ (a : LetA O n) (y : W.DD T₂), W.φD T₂ (a • y) = W.φA a • W.φD T₂ y := by
    intro a y
    rw [← algebraMap_smul W.EE a y, W.φD_smul, ← algebraMap_smul W.EE (W.φA a)]
    congr 1
    exact W.φE_ext a
  have hps1 : ps W 1 = W.φA (qA W) := by simp [ps]
  have hqmem : qA W ∈ W.AΔ := GS.qA_mem W
  have hp1mem : ps W 1 ∈ W.AΔ := GS.ps_mem W 1

  have hgen : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c' x →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x) := by
    intro x hx
    obtain ⟨hxΔ, hxl⟩ := hx
    have hxlet := TypesD.nl_letter W hxl
    have h1 := h5.1 (c - 2) x (by rw [e1]; exact hxl)
    rw [hM1] at h1
    have hl1 : (letE (c - 2) : LetA O n) • (W.Q ^ (w' + A.S) • W.φD T₂ x) = W.Q ^ (w' + A.S) • W.φD T₂ x := by
      rw [smul_comm]
      congr 1
      have := TypesD.φD_letter W hxlet
      rwa [show c' + 1 = c - 2 by rw [← e4]; push_cast; ring] at this
    have hletφ : (letE (c - 2) : LetA O n) • W.φD T₂ x = W.φD T₂ x := by
      have := TypesD.φD_letter W hxlet
      rwa [show c' + 1 = c - 2 by rw [← e4]; push_cast; ring] at this
    have hz1 : W.Q ^ (w' + A.S) • W.φD T₂ x ∈ W.Nl T₂ (c - 2) := ⟨_, h1, by simp [hletφ]⟩
    have h2 := h5.1 (c - 1) _ (by rw [e2]; exact hz1)
    rw [hM2, hφs] at h2
    set u : (LetA O n)ˣ := wq ^ A.η * (Units.map (W.φA : LetA O n →* LetA O n) wq) ^ (w' + A.S) with hu
    have hE : ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x) =
        ((u⁻¹ : (LetA O n)ˣ) : LetA O n) • (W.Q ^ A.η • (W.φA (W.Q ^ (w' + A.S)) • W.φD T₂ (W.φD T₂ x))) := by
      rw [smul_smul, smul_smul, pow_two, Module.End.mul_apply]
      congr 1
      rw [hQ, map_pow, map_mul, hps1, hu]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, mul_pow]
      have h1' : ((u⁻¹ : (LetA O n)ˣ) : LetA O n) * (u : LetA O n) = 1 := Units.inv_mul u
      rw [hu] at h1'
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe] at h1'
      linear_combination (-(qA W ^ A.η * W.φA (qA W) ^ (w' + A.S))) * h1'
    have hEN : (qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x ∈ W.N T₂ := by
      rw [hE]; exact (W.N T₂).smul_mem _ h2
    have hlet2 := TypesD.φDpow_letter W hxlet 2
    rw [e3] at hlet2
    have hEl : (letE (c - 1) : LetA O n) • ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x) =
        (qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x := by
      rw [smul_comm, hlet2]
    have hamem : qA W ^ A.η * ps W 1 ^ (w' + A.S) ∈ W.AΔ :=
      W.AΔ.mul_mem (W.AΔ.pow_mem hqmem _) (W.AΔ.pow_mem hp1mem _)
    have hΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ (((W.φD T₂) ^ 2) x) = ((W.φD T₂) ^ 2) x := by
      intro δ hδ
      rw [pow_two, Module.End.mul_apply, ← W.φγ_comm, ← W.φγ_comm, hxΔ.2 δ hδ]
    refine ⟨⟨hEN, fun δ hδ => ?_⟩, ⟨_, hEN, by simp [hlet2]⟩⟩
    rw [ArcLengthTwo.γD_smulA W T₂ δ, hΔ δ hδ]
    have ha' : W.γA δ (qA W ^ A.η * ps W 1 ^ (w' + A.S)) = qA W ^ A.η * ps W 1 ^ (w' + A.S) := hamem δ hδ
    rw [ha']

  obtain ⟨z₀, hz₀, hz₀eq⟩ := hlamγ
  have hPall : ∀ z ∈ Pp W T₂ c' 2,
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • z) := by
    intro z hz
    unfold Pp at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hz
      rw [smul_comm]
      exact inNΔi_smulA W T₂ (c - 1) hα (hgen x hx)
    | zero => rw [smul_zero]; exact ⟨(W.NΔ T₂).zero_mem, (W.Nl T₂ (c - 1)).zero_mem⟩
    | add z z' _ _ h h' => rw [smul_add]; exact inNΔi_add W T₂ (c - 1) h h'
    | neg z _ h => rw [smul_neg]; exact ⟨(W.NΔ T₂).neg_mem h.1, (W.Nl T₂ (c - 1)).neg_mem h.2⟩
  have hPz := hPall z₀ hz₀

  obtain ⟨r₀, -, r₀', hr₀', hrr₀, hγ₀⟩ := GS.psγ hR 0
  obtain ⟨r₁, hr₁, -, -, -, hγ₁⟩ := GS.psγ hR 1
  have hps0 : ps W 0 = qA W := by simp [ps]
  rw [hps0] at hγ₀
  have hγs : algebraMap (LetA O n) W.EE (qA W ^ b₁) * W.γE W.gam s =
      algebraMap (LetA O n) W.EE (r₀' ^ b₁ * (r₁ * ps W 1) ^ (w' + A.S)) := by
    have h := congrArg (W.γE W.gam) hs
    rw [map_mul, GS.γE_ι, GS.γE_ι, map_pow (W.γA W.gam), map_pow (W.γA W.gam), hγ₀, hγ₁] at h
    have hq' : qA W ^ b₁ = r₀' ^ b₁ * (r₀ * qA W) ^ b₁ := by
      rw [mul_pow, ← mul_assoc, ← mul_pow, mul_comm r₀' r₀, hrr₀, one_pow, one_mul]
    rw [hq', map_mul, mul_assoc, h, ← map_mul]

  obtain ⟨w₁, hw₁⟩ := hR.2.1
  have hJJ : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)) =
      (w₁ : LetA O n) ^ A.M PD.p * W.π₀ ^ A.M PD.p * qA W ^ ((PD.p - 1) * A.M PD.p) * ps W 1 ^ (2 * A.G₀) := by
    have hpk : Formalism.MainNotions.LiftingTheory.pk W 0 = qA W := by simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, qA, lA]
    simp only [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, hpk, map_mul, map_pow, hw₁, hps1]
    rw [pow_mul]
    try ring
  have hw₁mem : (w₁ : LetA O n) ∈ W.AΔ := by
    refine GS.quot_mem W (W.AΔ.mul_mem (GS.π₀_mem W) (W.AΔ.pow_mem hqmem _))
      (by rw [map_mul, map_pow]; exact (GS.isUnit_π₀ hR).mul ((GS.isUnit_qA hR).pow (PD.p - 1))) ?_
    have : W.π₀ * qA W ^ (PD.p - 1) * (w₁ : LetA O n) = W.φA W.π₀ := by rw [hw₁]; ring
    rw [this]
    exact GS.φpow_mem W 1 (GS.π₀_mem W)
  set N := (PD.p - 1) * A.M PD.p with hNdef
  set M := A.M PD.p with hMdef
  set V : LetA O n := (w₁ : LetA O n) ^ M * r₀' ^ b₁ * r₁ ^ (w' + A.S) with hV
  have hVmem : V ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hw₁mem _)
    (W.AΔ.pow_mem (GS.mem_invariants_of_mem_S1 W hr₀') _)) (W.AΔ.pow_mem (GS.mem_invariants_of_mem_S1 W hr₁) _)
  set C : LetA O n := W.π₀ ^ (M - 1) * qA W ^ (N - b₁ - A₀ - A.η) * ps W 1 ^ (2 * A.G₀) * V with hC
  have hCmem : C ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (GS.π₀_mem W) _)
    (W.AΔ.pow_mem hqmem _)) (W.AΔ.pow_mem hp1mem _)) hVmem
  refine ⟨C • ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • z₀), inNΔi_smulA W T₂ (c - 1) hCmem hPz, ?_⟩
  have hL : W.γE W.gam s • (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M) • z₀) =
      (W.γE W.gam s * algebraMap (LetA O n) W.EE (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M))) • z₀ := by
    rw [← algebraMap_smul W.EE (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M)) z₀, smul_smul]
  have hRt : (W.π₀ * qA W ^ A₀) • (C • ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • z₀)) =
      algebraMap (LetA O n) W.EE (W.π₀ * qA W ^ A₀ * (C * (qA W ^ A.η * ps W 1 ^ (w' + A.S)))) • z₀ := by
    rw [smul_smul, smul_smul, algebraMap_smul, mul_assoc]
  rw [hz₀eq, hL, hRt, hJJ]
  congr 1
  have hπ : W.π₀ ^ M = W.π₀ * W.π₀ ^ (M - 1) := by
    rw [← pow_succ']; (try congr 1); (try omega)
  have hqN : qA W ^ N = qA W ^ A₀ * qA W ^ (N - b₁ - A₀ - A.η) * qA W ^ A.η * qA W ^ b₁ := by
    rw [← pow_add, ← pow_add, ← pow_add]; (try congr 1); (try omega)
  rw [hπ, hqN]
  have : W.γE W.gam s * algebraMap (LetA O n) W.EE ((w₁ : LetA O n) ^ M * (W.π₀ * W.π₀ ^ (M - 1)) *
      (qA W ^ A₀ * qA W ^ (N - b₁ - A₀ - A.η) * qA W ^ A.η * qA W ^ b₁) * ps W 1 ^ (2 * A.G₀)) =
      algebraMap (LetA O n) W.EE ((w₁ : LetA O n) ^ M * (W.π₀ * W.π₀ ^ (M - 1)) *
      (qA W ^ A₀ * qA W ^ (N - b₁ - A₀ - A.η) * qA W ^ A.η) * ps W 1 ^ (2 * A.G₀)) *
      (algebraMap (LetA O n) W.EE (qA W ^ b₁) * W.γE W.gam s) := by
    simp only [map_mul]; ring
  rw [this, hγs, ← map_mul]
  congr 1
  rw [hC, hV]
  ring

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeHypFirst
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_hyp_first (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl5 : 5 ≤ PD.p)
    (hArc : ArcCore W) (hFL : ArcFilLowCore W) (A : ArcP n) (hOK : A.OK) (c : ZMod n) (hc : c ∈ A.cuts)
    (hlen : A.len c = 3) (hj : A.j = 1) {b₁ w' : ℕ} (hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up b₁)
    (hty2 : A.ty (c - 2) = Formalism.MainNotions.LocalTheoryWindows.LT.down w')
    {T₂ : LocLat G Qp LL O} (hW₂ : Win W A T₂) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hFil : dv W T₂ (A.len c) bb (Pi.single k₀ 1) ∈ FilS W T₂ c 1 b₁)
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2 1 lam) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol (A.M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2
      (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)))
      (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ (A.σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (s : W.EE) (hs : algebraMap (LetA O n) W.EE (qA W ^ b₁) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (w' + A.S))) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) := by
  classical
  have hj2 : A.j ≤ 2 := by rw [hj]; norm_num
  have h2l : 2 ≤ A.len c := by rw [hlen]; norm_num
  obtain ⟨⟨u, hu, hJJ⟩, hT⟩ := hArc hcase hl5 A hOK c hc 2 hj2 h2l
  obtain ⟨-, -, -, hfr⟩ := hT T₂ hW₂
  obtain ⟨-, -, hc3, -, -, -, hcrit⟩ := hfr d bb sol hbb
  have hFL' := hFL hcase hl5 A hOK c hc 2 hj2 h2l T₂ hW₂ d bb sol hbb (Pi.single k₀ 1) 1 (by norm_num)
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  set a : ZMod n := c' + ((2 : ℕ) : ZMod n) with ha_def
  have ha : a = c - 1 := by rw [ha_def, hc', hlen]; push_cast; ring
  set Λ : LetA O n := abelian₂ W A a 2 with hΛdef
  have hps0 : ps W 0 = qA W := by simp [ps]
  have hHs0 : A.Hs a 2 0 = A.h := by
    unfold ArcP.Hs
    rw [if_neg]
    push Not
    refine ⟨?_, by rw [hj]; norm_num⟩
    rw [Nat.cast_zero, sub_zero, ha, hty1]
    intro h; cases h
  have hHs1 : A.Hs a 2 1 = A.G₀ := by
    unfold ArcP.Hs
    rw [if_pos (Or.inr (by rw [hj]))]
  have hΛ : Λ = qA W ^ A.h * ps W 1 ^ A.G₀ := by
    rw [hΛdef, abelian₂, Finset.prod_range_succ, Finset.prod_range_one, hHs0, hHs1, hps0]
  have hb1h : b₁ + A.S ≤ A.h := by
    have := hOK.2.2.2.2.2.2.2.1 (c - 1) (by rw [hty1]; rfl)
    rwa [hty1] at this
  have hw'η : A.η < w' := by
    have := hOK.2.2.2.2.1 (c - 2)
    rwa [hty2] at this
  have hqmem : qA W ∈ W.AΔ := by rw [← hps0]; exact TypesA.ps_mem W 0
  set R : LetA O n := qA W ^ (A.h - b₁) * ps W 1 ^ (A.G₀ + (w' + A.S)) with hRdef
  have hRmem : R ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hqmem _) (W.AΔ.pow_mem (TypesA.ps_mem W 1) _)
  have hΛs : (algebraMap (LetA O n) W.EE) Λ * s = (algebraMap (LetA O n) W.EE) R := by
    have hq : qA W ^ A.h = qA W ^ (A.h - b₁) * qA W ^ b₁ := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    calc (algebraMap (LetA O n) W.EE) Λ * s = (algebraMap (LetA O n) W.EE) (qA W ^ (A.h - b₁) * ps W 1 ^ A.G₀) * ((algebraMap (LetA O n) W.EE) (qA W ^ b₁) * s) := by
          rw [hΛ, hq]; simp only [map_mul]; ring
      _ = (algebraMap (LetA O n) W.EE) (qA W ^ (A.h - b₁) * ps W 1 ^ A.G₀) * (algebraMap (LetA O n) W.EE) (ps W 1 ^ (w' + A.S)) := by rw [hs]
      _ = (algebraMap (LetA O n) W.EE) R := by rw [hRdef]; simp only [pow_add, map_mul]; ring
  have hΛx : Λ • (s • lam) = R • lam := by
    rw [← algebraMap_smul W.EE Λ (s • lam), smul_smul, hΛs, algebraMap_smul]
  have hInFP : InFP W T₂ c' 2 1 (Λ • (s • lam)) := by
    rw [hΛx]
    obtain ⟨y, hy, rfl⟩ := hlam
    exact ⟨R • y, TypesA.Pp_smul W hRmem hy, by rw [one_smul, one_smul]⟩
  have hΛmem : Λ ∈ W.AΔ := TypesA.Ps_mem W (TC.lam_mem_Ps W A a 2)
  have hletmem : (letE a : LetA O n) ∈ W.AΔ := TypesD.letE_mem W a

  obtain ⟨-, -, κ₁, κ₁', Hh1, a1, hHh1, -, -⟩ := hc3 (fun k => if k = k₀ then (algebraMap (LetA O n) W.EE) (letE a) else 0) (by
    intro k
    by_cases hk : k = k₀
    · simp only [if_pos hk]
      exact ⟨Λ, hΛmem, by rw [← map_mul]; congr 1; ring⟩
    · simp only [if_neg hk]
      exact ⟨0, W.AΔ.zero_mem, by simp⟩)
  set σ := A.σ PD.p with hσdef
  obtain ⟨κ', y, hy, hyeq⟩ := h4a
  rw [hj] at hJJ
  have hJJ' : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)) = W.π₀ * Λ ^ 2 * u := by
    rw [← hJJ]; simp
  have hlet2 : (letE a : LetA O n) • ((W.φD T₂) ^ 2) Hh = ((W.φD T₂) ^ 2) Hh :=
    TypesD.φDpow_letter W (TypesD.horTr_letter W hbb hHh) 2
  have hφl : ((W.φD T₂) ^ 2) (lA W ^ κ₁ • Hh) = lA W ^ κ₁ • ((W.φD T₂) ^ 2) Hh := by
    rw [← TypesA.pO_smul, map_smul, TypesA.pO_smul]
  have hRep : RepVV W T₂ c' 2 (A.M PD.p) Λ bb sol (lA W ^ 0 • (s • lam))
      (fun k => if k = k₀ then (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s else 0) := by
    refine ⟨κ + κ₁, κ', fun k => if k = k₀ then lA W ^ κ₁ • Hh else lA W ^ κ • Hh1 k,
      fun k => if k = k₀ then letE a * R * lA W ^ σ else 0, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = k₀
      · subst hk; simp only [if_pos rfl]; exact TypesA.IsHorTr_smul W κ₁ hHh
      · simp only [if_neg hk]; rw [add_comm]; exact TypesA.IsHorTr_smul W κ (hHh1 k)
    · intro k
      by_cases hk : k = k₀
      · simp only [if_pos hk]
        refine ⟨W.AΔ.mul_mem (W.AΔ.mul_mem hletmem hRmem) (TypesA.lA_pow_mem W σ), ?_⟩
        rw [TC.lE_eq W σ]
        rw [show (algebraMap (LetA O n) W.EE) Λ * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) Λ * s) by ring, hΛs]
        simp only [map_mul]; ring
      · simp only [if_neg hk]; exact ⟨W.AΔ.zero_mem, by simp⟩
    · have hsum : ∑ k, (if k = k₀ then letE a * R * lA W ^ σ else 0) •
          ((W.φD T₂) ^ 2) (if k = k₀ then lA W ^ κ₁ • Hh else lA W ^ κ • Hh1 k) =
          (R * lA W ^ σ * lA W ^ κ₁) • ((W.φD T₂) ^ 2) Hh := by
        rw [Finset.sum_eq_single k₀ (fun k _ hk => by simp only [if_neg hk, zero_smul]) (by simp)]
        rw [if_pos rfl, if_pos rfl]
        rw [hφl, smul_smul, show letE a * R * lA W ^ σ * lA W ^ κ₁ = (R * lA W ^ σ * lA W ^ κ₁) * letE a by ring,
          mul_smul, hlet2]
      rw [hsum, pow_zero, one_smul, hΛx]
      refine ⟨(u * (R * lA W ^ κ₁)) • y, TypesA.Pp_smul W (W.AΔ.mul_mem hu (W.AΔ.mul_mem hRmem
        (TypesA.lA_pow_mem W κ₁))) hy, ?_⟩
      have e1 : lA W ^ κ' • (lA W ^ (κ + κ₁) • R • lam - (R * lA W ^ σ * lA W ^ κ₁) • ((W.φD T₂) ^ 2) Hh) =
          (R * lA W ^ κ₁) • (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ σ • ((W.φD T₂) ^ 2) Hh)) := by
        simp only [smul_sub, smul_smul]
        congr 2 <;> ring
      rw [e1, hyeq, hJJ', smul_smul, smul_smul]
      congr 1
      ring
  have hfr : ∀ m, InFr W a 1 Λ (if m = k₀ then (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s else 0) := by
    intro m
    by_cases hm : m = k₀
    · simp only [if_pos hm]
      refine ⟨R * lA W ^ σ, W.AΔ.mul_mem hRmem (TypesA.lA_pow_mem W σ), ?_⟩
      rw [TC.lE_eq W σ]
      rw [show (algebraMap (LetA O n) W.EE) Λ * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) Λ * s) by ring, hΛs]
      simp only [map_mul, map_one]; ring
    · simp only [if_neg hm]; exact ⟨0, W.AΔ.zero_mem, by simp⟩
  have hN : InFNc W T₂ a 1 (s • lam) := by
    refine (hcrit (s • lam) 0 _ hInFP hRep hfr).2 ⟨0, 1, fun _ => (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s,
      fun _ => Pi.single k₀ 1, fun _ t => if t = 0 then -(b₁ : ℤ) else ((w' + A.S : ℕ) : ℤ),
      fun _ => ⟨?_, ?_⟩, fun k => ?_⟩
    · refine ⟨lA W ^ σ, TypesA.lA_pow_mem W σ, ?_⟩
      have e1 : (-(b₁ : ℤ)).toNat = 0 := by omega
      have e2 : (-(-(b₁ : ℤ))).toNat = b₁ := by omega
      have e3 : (((w' + A.S : ℕ) : ℤ)).toNat = w' + A.S := by omega
      have e4 : (-(((w' + A.S : ℕ) : ℤ))).toNat = 0 := by omega
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_ne_zero, ↓reduceIte,
        e1, e2, e3, e4, pow_zero, one_mul, mul_one, hps0]
      rw [TC.lE_eq W σ]
      simp only [map_mul]
      rw [show (algebraMap (LetA O n) W.EE) (qA W ^ b₁) * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) (qA W ^ b₁) * s)
        by ring, hs]
      ring
    · intro t ht
      interval_cases t
      · simp only [↓reduceIte, neg_neg]
        rw [hlen, show (3 : ℕ) = 2 + 1 from rfl, ArcLengthTwo.dv_succ] at hFil
        rw [ArcLengthTwo.dvO_single]
        exact ArcLengthTwo.filS_φ_inv W T₂ (by rw [ha]; push_cast; ring) hFil
      · simp only [one_ne_zero, ↓reduceIte]
        refine hFL'.1 _ fun x hx => ?_
        have e : a - ((1 : ℕ) : ZMod n) = c - 2 := by rw [ha]; push_cast; ring
        rw [e, hty2] at hx
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hx
        push_cast
        omega
    · simp only [Fin.sum_univ_one, lE, pow_zero, one_mul]
      by_cases hk : k = k₀
      · subst hk; simp
      · simp [if_neg hk, Pi.single_apply, hk]
  obtain ⟨y, hyΔ, hyl, hxy⟩ := hN
  rw [← ha, hxy, one_smul]
  exact ⟨hyΔ, ⟨y, hyΔ.1, by simpa using hyl⟩⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.NumericBoundExponentEg
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

theorem numeric_bound_two_a_le_b1 (l : ℕ) (hl : 11 ≤ l) (b wm S η b₁ H : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hb₁ : b ≤ b₁) (hH : H ≤ b + 2 * η + S)
    (hsm : 40 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg l (b + η + S) wm S η ≤ (b : ℝ) / 4) (a : ℝ)
    (ha : a ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1) :
    2 * a + η + 1 ≤ (b₁ : ℝ) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hηR : 20 * (η : ℝ) ≤ b := by exact_mod_cast hη
  have hSR : 20 * (S : ℝ) ≤ b := by exact_mod_cast hS
  have hb₁R : (b : ℝ) ≤ b₁ := by exact_mod_cast hb₁
  have hHR : (H : ℝ) ≤ b + 2 * η + S := by exact_mod_cast hH
  have hcW := cW_le l hl (b + η + S) η H (by omega) (by omega)
  have hlog0 : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
    Real.logb_nonneg (by linarith) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) η, Nat.cast_nonneg (α := ℝ) S])
  have hSg : Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) + 1 ≤ Sg l (b + η + S) wm S η := by
    unfold Sg
    have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ ((wm : ℝ) + S + η) / l := by positivity
    linarith
  have hfrac : (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 ≤ (H : ℝ) * (21 / 100) := by
    rw [div_le_iff₀ (by nlinarith)]
    have h3 : (2 * (l : ℝ) - 1) ≤ 21 / 100 * ((l : ℝ) - 1) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hl') (by linarith : (0 : ℝ) ≤ l - 1)]
    nlinarith [Nat.cast_nonneg (α := ℝ) H]
  have hη0 := Nat.cast_nonneg (α := ℝ) η
  have hS0 := Nat.cast_nonneg (α := ℝ) S
  linarith

theorem numeric_bound_exponent_eg (l : ℕ) (hl : 11 ≤ l) (b wm S η b₁ H : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hb₁ : b ≤ b₁) (hb₁' : b₁ ≤ b + η) (hH : H ≤ b + 2 * η + S) (A : ℕ)
    (ha : (A : ℝ) ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1) :
    (EG l A S η b₁ : ℝ) ≤ 8 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg l (b + η + S) wm S η := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hl0 : (0 : ℝ) < l - 1 := by linarith
  have hcW : (0 : ℝ) ≤ (cW l H : ℝ) := Nat.cast_nonneg _
  have hHl : (0 : ℝ) ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have ha' : max (A : ℝ) 1 ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1 :=
    max_le ha (by linarith)
  have h5 := div_add_logb_le_eight_mul_errorScale l hl b wm S η b₁ H hb hη hS hwm hb₁ hb₁' hH (max (A : ℝ) 1) (le_max_right _ _) ha'
  have hmono : ((3 * (A : ℝ) + S + 2 * η : ℝ) - 2) / ((l : ℝ) - 1) ≤
      (3 * max (A : ℝ) 1 + S + 2 * η - 2) / ((l : ℝ) - 1) := by
    apply div_le_div_of_nonneg_right _ hl0.le
    linarith [le_max_left (A : ℝ) 1]
  have hSg : 0 ≤ Sg l (b + η + S) wm S η := by
    unfold Sg
    have h0 : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
      Real.logb_nonneg hl1 (by
        push_cast
        have : (1 : ℝ) ≤ b := by exact_mod_cast hb
        linarith [Nat.cast_nonneg (α := ℝ) η, Nat.cast_nonneg (α := ℝ) S])
    have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ ((wm : ℝ) + S + η) / l := by positivity
    linarith
  unfold EG
  by_cases hY : 0 ≤ ((3 * (A : ℝ) + S + 2 * η : ℝ) - 2) / ((l : ℝ) - 1) + Real.logb l ((b₁ : ℝ) + η - 1)
  · exact (Nat.floor_le hY).trans (by linarith)
  · rw [Nat.floor_of_nonpos (not_le.1 hY).le, Nat.cast_zero]
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

theorem arc_length_three_first_level [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh))) :
    ∃ (n₁ : W.DD T₁) (E : ℕ), Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) n₁ ∧ (E : ℝ) ≤ 8 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
      ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
        algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) ∧ W.map F n₁ = (((PD.p : ℕ) : LetA O n) ^ E) • (s • lam) := by
  classical
  set A := arcOf b w S η up size with hAdef
  have hB' := hB
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB'
  obtain ⟨-, hSur, hηs, hJA, -, hnt, -⟩ := hSet
  have hl5 : 5 ≤ PD.p := by omega

  have hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 3 := hlen
  have hne : {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Nat.sInf_empty] at hlen'
    omega
  have hm2 := Nat.notMem_of_lt_sInf (s := {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)})
    (m := 2) (by rw [hlen']; norm_num)
  have e2 : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
  have hT1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    by_contra hcon
    exact hm2 ⟨by norm_num, by rw [e2]; exact hcon⟩
  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c - 1, hT1⟩]
  have eSg : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    rw [show Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size =
      Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) w S η from rfl, hhB]
  have e21 : c - 2 + 1 = c - 1 := by ring
  have hup1 : up (c - 1) = true := by
    have := (halt (c - 2)).1; rw [e21, hD] at this
    cases h : up (c - 1) <;> simp_all
  have hty : ∀ i, A.ty i = if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i) :=
    fun i => rfl
  have hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1)) := by rw [hty, hup1]; rfl
  have hty2 : A.ty (c - 2) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - 2)) := by rw [hty, hD]; rfl
  have hb1 : 1 ≤ b := by have := hηs (c - 1); have := hT1.2; omega

  have hFil : dv W T₂ (A.len c) bb (Pi.single k₀ 1) ∈ FilS W T₂ c 1 (size (c - 1)) :=
    hk₀ 1 (by rw [hlen]; norm_num) (size (c - 1)) (by rw [Nat.cast_one]; exact hty1)
  have hH1 : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) :=
    fun s hs => arc_length_three_hyp_first W hcase hl5 hArc hFL A hOK c hc hlen rfl hty1 hty2 hW₂ bb sol hbb k₀ hFil lam hlam κ Hh
      hHh h4a s hs

  have hR := GS.ringData_of_caseA_of_p9 W hcase hP9
  have hqU : IsUnit (algebraMap (LetA O n) W.EE (qA W ^ size (c - 1))) := by
    rw [map_pow]; exact (GS.isUnit_qA hR).pow _
  obtain ⟨uq, huq⟩ := hqU
  set s₀ : W.EE := ((uq⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) with hs₀
  have hs₀eq : algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s₀ =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) := by
    rw [hs₀, ← huq, ← mul_assoc, Units.mul_inv, one_mul]
  have huniq : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → s = s₀ := by
    intro s hs
    have h := hs.trans hs₀eq.symm
    rw [← huq] at h
    exact (Units.mul_right_inj uq).1 h

  let Mi' : ZMod n → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod n → ℕ := fun i => if up i then size i + S else η
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi' := by
    intro i τ hτ a ha
    have h1 := hJA i τ hτ a ha
    have h2 := hηs i
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hAS : A.S = S := rfl
  have hAη : A.η = η := rfl
  have hAG : A.G₀ = w + S := rfl
  have hJ₂ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ Mi' hi' := by
    intro τ i hτ a ha
    have h1 := hW₂.2 i τ hτ a ha
    have h2 := hηs i
    rw [hty i] at h1
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union,
        Set.mem_Icc, hAS, hAη, hAG] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc, hAS, hAη, hAG] at h1 ⊢
      push_cast
      omega
  have hwid : ∀ i, Mi' i + hi' i = size i + S + η := by
    intro i
    cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hsz : ∀ i, size i ≤ b + η := by
    intro i
    by_cases ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i
    · exact ht.2
    · have := hnt i ht; omega
  have hHle : Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' ≤ b + 2 * η + S :=
    Finset.sup_le fun k _ => by rw [hwid]; have := hsz (k : ZMod n); omega
  obtain ⟨-, hKA, -, hKr, -, -, hAr, -⟩ := hWR hcase T₁ T₂ F Mi' hi' hSur hJ (c - 1)
  set Ai := Formalism.MainNotions.LiftingTheory.AI W F (c - 1) with hAidef
  set ri := Formalism.MainNotions.LiftingTheory.rI W F (c - 1) with hridef
  set b₁ := size (c - 1) with hb₁def
  have hcW : (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) = (cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) := rfl
  rw [hcW] at hAr
  have hsm' : 40 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η ≤ (b : ℝ) / 4 := by rw [← eSg]; exact hsm
  have hk6 := numeric_bound_two_a_le_b1 PD.p hp11 b w S η b₁ _ hb1 hηb hSb hwb hT1.1 hHle hsm' ((Ai + ri : ℕ) : ℝ) hAr
  have hb : 2 * (Ai + ri) + η + 1 ≤ b₁ := by
    have : ((2 * (Ai + ri) + η + 1 : ℕ) : ℝ) ≤ b₁ := by push_cast at hk6 ⊢; linarith
    exact_mod_cast this
  have hE := numeric_bound_exponent_eg PD.p hp11 b w S η b₁ _ hb1 hηb hSb hwb hT1.1 hT1.2 hHle (Ai + ri) hAr

  have hl0 : ((PD.p : ℕ) : O) ≠ 0 := GS.p_ne_zero W
  haveI : CharZero O := charZero_of_prime_ne_zero W hO hl0
  have hA4 := gamma_q_expansion_of_points W hcase hP9 hO hOv hinj Pt hPtEx
  obtain ⟨dop₁, hd₁⟩ := exists_gamma_sub_one_div_pi0 W hP9 hcase T₁
  obtain ⟨dop₂, hd₂⟩ := exists_gamma_sub_one_div_pi0 W hP9 hcase T₂
  obtain ⟨cc, hcc⟩ := exists_cyclotomic_char_quotient W hcase hOv hinj
  have hU : Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt W T₁ (c - 1) ((Set.Icc (b₁ : ℤ) (b₁ + S)) ∪ Set.Icc (-(η : ℤ)) η) := by
    have := hJA (c - 1)
    rw [hup1, if_pos rfl] at this
    exact this
  have hCONS : ∀ y : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) (qA W ^ (Ai + ri) • y) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) (Polynomial.aeval dop₁ (TruncatedCoefficientPoly cc b₁ S η (Ai + ri)) y) := by
    rcases Nat.eq_zero_or_pos (Ai + ri) with h0 | hpos
    · intro y hy
      rw [h0, pow_zero, one_smul] at hy
      have h1 : TruncatedCoefficientPoly cc b₁ S η (Ai + ri) = 1 := by rw [h0]; simp [TruncatedCoefficientPoly, TruncationIndexSet]
      rw [h1, map_one]
      exact hy
    · refine hC4 hcase T₁ hW₁.1 (c - 1) (Ai + ri) hpos dop₁ hd₁ cc hcc (TruncationIndexSet b₁ S η (Ai + ri))
        (fun τ a j hτ ha hj1 hj2 => ?_)
      have hmem := hU τ hτ a ha
      refine Finset.mem_image.2 ⟨(a, (j : ℤ)), Finset.mem_product.2 ⟨?_,
        Finset.mem_Icc.2 ⟨by dsimp only; exact_mod_cast hj1, by dsimp only; exact_mod_cast hj2⟩⟩, rfl⟩
      simp only [Set.mem_union, Set.mem_Icc] at hmem
      simp only [winU, Finset.mem_union, Finset.mem_Icc]
      exact hmem
  have hs' : ps W 1 ^ (size (c - 2) + S) ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k} :=
    Submonoid.pow_mem _ (Submonoid.subset_closure (show ps W 1 ∈ {x | ∃ k ≥ 1, x = ps W k} from ⟨1, le_rfl, rfl⟩)) _

  have hM1 : Mi' (c - 2) = size (c - 2) + A.S := by simp only [Mi', hD, Bool.false_eq_true, if_false]; rfl
  have hM2 : Mi' (c - 1) = A.η := by simp only [Mi', hup1, if_true]; rfl
  have hAh : A.h = b + η + S := hhB
  have hN : b₁ + (Ai + ri) + A.η ≤ (PD.p - 1) * A.M PD.p := by
    have h1 := Nat.lt_mul_div_succ (2 * A.h) (show 0 < PD.p - 1 by omega)
    have h2 : A.M PD.p = 2 * A.h / (PD.p - 1) + 1 := rfl
    rw [h2, hAη]
    have := hT1.2
    generalize (PD.p - 1) * (2 * A.h / (PD.p - 1) + 1) = Z at h1 ⊢
    omega
  have hM : 1 ≤ A.M PD.p := by
    show 1 ≤ 2 * A.h / (PD.p - 1) + 1
    exact Nat.le_add_left _ _
  have hH2 := arc_length_three_hyp_second W hcase hP9 hP5 A c hlen hW₂.1 Mi' hi' hJ₂ hM1 hM2 hN hM lam hlamγ s₀ hs₀eq

  obtain ⟨x₁, hx₁, hmap⟩ := existsLiftMapEqPrimePowSmul W hcase hP9 (c - 1) F hSur hW₁.1 hW₂.1 Ai ri hKA hKr b₁ S η hU hb
    (gamma_pi0_eq_pi0_mul_one_add_unit_mul_q W hcase hP9) (fun k hk => gamma_level_eq_mul W hcase hP9 k hk) hA4 hl0 hO hOv hinj
    (gamma_sub_self_mem_pi0_lattice W hP9 hcase (c - 1) T₁ hW₁.1) (gamma_sub_self_mem_pi0_lattice W hP9 hcase (c - 1) T₂ hW₂.1)
    dop₁ hd₁ dop₂ hd₂ cc hcc hCONS s₀ (ps W 1 ^ (size (c - 2) + S)) hs' hs₀eq lam (hH1 s₀ hs₀eq) hH2
  refine ⟨x₁, EG PD.p (Ai + ri) S η b₁, hx₁, ?_, fun s hs => ?_⟩
  · rw [eSg]; exact hE
  · obtain rfl := huniq s hs
    exact ⟨hH1 s₀ hs₀eq, hmap⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
