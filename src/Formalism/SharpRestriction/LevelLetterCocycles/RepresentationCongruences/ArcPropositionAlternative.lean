module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LenTLeThree
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthOneOrTwoCaseB
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsLiftsAtArcOfOfUpEqFalse
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsExponentLeAndLiftsAtArc
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThinLetterTypeBis
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeCaseC
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeCaseD

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcSingleTypeBound
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcBasic
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

theorem arcBasic [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi) :
    let A := arcOf b w S η up size
    A.OK ∧ (∑ c ∈ A.cuts, A.len c) = n ∧
    (Alt b η up size → ∀ c ∈ A.cuts, A.len c ≤ 3) ∧
    (∀ R : ℕ, 1 ≤ R → One b η R up size → ∀ c ∈ A.cuts, A.len c ≤ R) ∧
    (A.σ PD.p : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size :=
  SetupA.arcBasic_core W F hB

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

namespace A1

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem cmpD_add' {x y : W.DD T} (hx : x ∈ W.N T) (hy : y ∈ W.N T) :
    cmpD W T (x + y) = cmpD W T x + cmpD W T y := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hx, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hy,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).add_mem hx hy)]
  rw [← map_add (f := _)]
  rfl

theorem cmpD_sum' {ι : Type} (s : Finset ι) (y : ι → W.DD T) (hy : ∀ k ∈ s, y k ∈ W.N T) :
    cmpD W T (∑ k ∈ s, y k) = ∑ k ∈ s, cmpD W T (y k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (W.N T).zero_mem]
    exact map_zero (W.cmp T)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      cmpD_add' W T (hy a (Finset.mem_insert_self a s))
        (Submodule.sum_mem _ fun k hk => hy k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hy k (Finset.mem_insert_of_mem hk)]

theorem cmpD_smul_letter' (i : ZMod n) (a : LetA O n) {w : W.DD T} (hw : w ∈ W.N T)
    (hwi : (letE i : LetA O n) • w = w) :
    cmpD W T (a • w) = algebraMap O LL (PowerSeries.constantCoeff (a i)) • cmpD W T w := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hw, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).smul_mem a hw)]
  exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T i a w hw hwi

end A1

theorem arc_single_type_bound [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f)
    (hone : ∀ s < (arcOf b w S η up size).len c, up (c - (s : ZMod n)) = up c) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 6 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  have hbas := arcBasic W F hB
  dsimp only at hbas
  obtain ⟨hOK, -, -, -, hσ⟩ := hbas
  have hl : 5 ≤ PD.p := by have := hB.1; omega
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hB.2.1.2.1
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    by_cases h : up (c - (s : ZMod n)) = true <;> simp [arcOf, h, Formalism.MainNotions.LocalTheoryWindows.LT.thick]
  refine ⟨rr + (arcOf b w S η up size).σ PD.p, by push_cast; linarith, ?_⟩
  cases hup : up c
  ·
    have hdn : ∀ s < (arcOf b w S η up size).len c,
        (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s : ZMod n))) := by
      intro s hs
      have h1 : up (c - (s : ZMod n)) = false := (hone s hs).trans hup
      simp [arcOf, h1]
    have hnn : nnDen W (arcOf b w S η up size) c = 1 := by
      unfold nnDen prodTy
      apply Finset.prod_eq_one
      intro s hs
      rw [hdn s (Finset.mem_range.1 hs)]
      simp
    have hcut' : c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) ∈ (arcOf b w S η up size).cuts :=
      (hOK.2.2.1 c hc).2.2.1
    obtain ⟨d₁, b₁, sol₁, hb₁⟩ :=
      hHF hcase hl _ hOK T₁ hW₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))
    obtain ⟨x₁, hx₁, hx₁eq⟩ := hArcL hcase T₁ T₂ F hsur _ rr ((arcOf b w S η up size).len c)
      (hkill _ hcut') (bb k₀) (hbb.1.1 k₀)
    obtain ⟨a, ⟨-, hxa⟩, -⟩ := hb₁.1.2 x₁ hx₁
    have hb₁N : ∀ m, b₁ m ∈ W.N T₁ := fun m => (hb₁.1.1 m).1.1
    have hb₁l : ∀ m, (letE (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) : LetA O n) • b₁ m = b₁ m :=
      fun m => Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T₁ _ (hb₁.1.1 m).2
    have hcmp : cmpD W T₁ x₁ = ∑ m, algebraMap O LL (PowerSeries.constantCoeff
        (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)))) • cmpD W T₁ (b₁ m) := by
      rw [hxa, A1.cmpD_sum' W T₁ _ _ (fun m _ => (W.N T₁).smul_mem _ (hb₁N m))]
      exact Finset.sum_congr rfl fun m _ =>
        A1.cmpD_smul_letter' W T₁ _ (a m) (hb₁N m) (hb₁l m)
    have e1 : dvO W T₁ ((arcOf b w S η up size).len c) b₁ (fun m => PowerSeries.constantCoeff
        (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)))) =
        ((φVB PD (LL := LL) (V := T₁.V)) ^ ((arcOf b w S η up size).len c)) (cmpD W T₁ x₁) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hcmp, map_sum]
      simp only [map_smul]
      rfl
    have e2 : dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1) =
        ((φVB PD (LL := LL) (V := T₂.V)) ^ ((arcOf b w S η up size).len c)) (cmpD W T₂ (bb k₀)) := by
      unfold dv
      rw [Finset.sum_eq_single k₀ (fun m _ hm => by simp [hm]) (by simp)]
      simp
    have hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ ((arcOf b w S η up size).len c) b₁ (fun m =>
        PowerSeries.constantCoeff (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))))) =
        ((PD.p : LL) ^ rr) • dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1) := by
      rw [e1, e2, hx₁eq]
    refine liftsAt_thin_letter_type W _ F c bb sol k₀ hOK hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
      hW₁ hW₂ hbb ∅ (by simp) b₁ sol₁ hb₁ _ rr (by simp) hpr f ?_ ?_ ?_
    · have h := hf.1
      rw [hnn] at h
      rw [Finset.prod_empty]
      exact h
    · intro s hs bs hbs
      obtain ⟨κ, x, hx⟩ := hf.2 s hs bs hbs
      rw [hnn] at hx
      exact ⟨κ, x, by rw [Finset.prod_empty]; exact hx⟩
    · intro s hs _ bs hbs
      rw [hdn s hs] at hbs
      simp at hbs
  ·
    refine liftsAt_thick_letter_type W _ F c bb sol k₀ hOK hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
      hArcL hNN hW₁ hW₂ hsur rr hkill hbb hk₀ f hf.1 ?_
    intro s hs bs hbs
    have h1 : up (c - (s : ZMod n)) = true := (hone s hs).trans hup
    simp [arcOf, h1] at hbs

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthTwoCaseDown
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLenTwoThickLetters
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.HmaxLe
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem hmax_le' [NeZero n] (Mi hi : ZMod n → ℕ) (j : ZMod n) :
    Mi j + hi j ≤ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  have h := Finset.le_sup (f := fun k : ℕ => Mi k + hi k) (Finset.mem_range.2 (ZMod.val_lt j))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

theorem aI_le [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) (c : ZMod n)
    (hct : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c) (hc1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c + 1)) :
    (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) ≤
      ((size c : ℝ) + S + η) / PD.p + 2 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB
  obtain ⟨hcase, hSur, hηs, hJA, -, hnt, -⟩ := hSet
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
  have hwid : ∀ i, Mi' i + hi' i = size i + S + η := by
    intro i
    cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hsz : ∀ i, size i ≤ b + η := by
    intro i
    by_cases ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i
    · exact ht.2
    · have := hnt i ht; omega
  have hHle : Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' ≤ (b + η + S) + η :=
    Finset.sup_le fun k _ => by rw [hwid]; have := hsz (k : ZMod n); omega
  obtain ⟨hs, -⟩ := hWR hcase T₁ T₂ F Mi' hi' hSur hJ (c - 1)
  have hcW : (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) =
      (cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) := rfl
  have e0 : c - 1 + ((0 + 1 : ℕ) : ZMod n) = c := by push_cast; ring
  have e1 : c - 1 + ((1 + 1 : ℕ) : ZMod n) = c + 1 := by push_cast; ring
  have hc1w : size (c + 1) ≤ w := hnt (c + 1) hc1
  have ht := tsum_three PD.p hp11
    (fun a => ((Mi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) + hi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) +
      Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((((size c + S + η : ℕ) : ℝ)) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((((w + S + η : ℕ) : ℝ)) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' : ℝ) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    (fun a => by positivity)
    (by
      show _ + _ + _ ≤ _
      rw [e0, hwid, hcW])
    (by
      show _ + _ + _ ≤ _
      rw [e1, hwid, hcW]
      have : ((size (c + 1) + S + η : ℕ) : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := by
        exact_mod_cast (by omega : size (c + 1) + S + η ≤ w + S + η)
      linarith)
    (fun a _ => by
      have := hmax_le' Mi' hi' (c - 1 + ((a + 1 : ℕ) : ZMod n))
      have h' : (((Mi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) + hi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)) ≤
          Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' := by exact_mod_cast this
      show _ + _ + _ ≤ _
      rw [hcW]; linarith)
  have hst := hs.trans ht
  have hx : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hA : (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.sI W F (c - 1) : ℝ) / ((PD.p : ℝ) - 1) + 1 := by
    unfold Formalism.MainNotions.LiftingTheory.AI
    have h0 : 0 ≤ (Formalism.MainNotions.LiftingTheory.sI W F (c - 1) : ℝ) / ((PD.p : ℝ) - 1) :=
      div_nonneg (Nat.cast_nonneg _) (by linarith)
    exact (Nat.ceil_lt_add_one h0).le
  have hη1 : η + 1 ≤ b + η + S := by have := hηs c; have := hct.2; omega
  have key := Aa_cut_le PD.p hp11 (b + η + S) w S η (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') (size c + S + η)
    (w + S + η) hη1 hHle (by have := hct.2; omega) le_rfl _ _ hst hA
  have ec : (((size c + S + η : ℕ) : ℝ)) = (size c : ℝ) + S + η := by push_cast; ring
  rw [ec] at key
  exact key

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DenBound
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open PowerSeries Formalism.MainNotions.N.FrobeniusPowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem den_bound {l : ℕ} [Fact l.Prime] (P : PhiData O l) (y B κ : ℕ) (hy : 1 ≤ y) (hB : 1 ≤ B)
    (x : O) (U₁ U₂ : O⟦X⟧)
    (h : P.p 1 ^ y * C x = C (l : O) ^ κ * 1 * U₁ - X ^ B * U₂) :
    (l : O) ^ (κ - ⌈max 0 ((y : ℝ) - B / l + 2 + Real.logb l y)⌉₊) ∣ x ∧
      (l * y < B → (l : O) ^ κ ∣ x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨u, hu⟩ := l_eq_unit_mul_pow hϖ P.hl0
  set e := eO (O := O) l with he
  have hdiv : ∀ k : ℕ, ϖ ^ (e * k) ∣ x → (l : O) ^ k ∣ x := by
    rintro k ⟨z, hz⟩
    refine ⟨((↑(u⁻¹) : O)) ^ k * z, ?_⟩
    have hone : (↑u : O) ^ k * (↑(u⁻¹) : O) ^ k = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
    rw [hz, hu, mul_pow, ← pow_mul]
    linear_combination (-(ϖ ^ (e * k) * z)) * hone
  set de := ⌈max 0 ((y : ℝ) - B / l + 2 + Real.logb l y)⌉₊ with hde
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨dvd_zero _, fun _ => dvd_zero _⟩
  obtain ⟨v, ε, hxe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  by_cases hv : e * κ ≤ v
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hv
    have h1 : (l : O) ^ κ ∣ x := hdiv κ ⟨↑ε * ϖ ^ t, by rw [hxe, ht, pow_add]; ring⟩
    exact ⟨(pow_dvd_pow _ (Nat.sub_le _ _)).trans h1, fun _ => h1⟩
  push_neg at hv
  set k := e * κ - v with hk
  have hdist := (ContPA.dist_X_pow (O := O) B).1

  have hmem : P.p 1 ^ y ∈ Ideal.span {C ϖ ^ k, (X : O⟦X⟧) ^ B} := by
    have hvk : v + k = e * κ := by omega
    have hlO : (l : O) ^ κ = ϖ ^ v * (ϖ ^ k * (↑u : O) ^ κ) := by
      rw [hu, mul_pow, ← pow_mul, ← hvk, pow_add]; ring
    have hlk : (C (l : O) : O⟦X⟧) ^ κ = C ϖ ^ v * (C ϖ ^ k * C ((↑u : O) ^ κ)) := by
      rw [← map_pow, hlO, map_mul, map_mul, map_pow, map_pow]
    have hc : C ϖ ^ v * (P.p 1 ^ y * C (↑ε : O) - C ϖ ^ k * (C ((↑u : O) ^ κ) * U₁)) =
        (-U₂) * (X : O⟦X⟧) ^ B := by
      have hxC : (C x : O⟦X⟧) = C (↑ε : O) * C ϖ ^ v := by rw [hxe, map_mul, map_pow]
      rw [hxC, hlk] at h
      linear_combination h
    obtain ⟨z, hz⟩ := ContM_cancel_unif hϖ hdist v hc
    have hε : P.p 1 ^ y = C ϖ ^ k * (C ((↑u : O) ^ κ) * U₁ * C (↑(ε⁻¹) : O)) +
        (X : O⟦X⟧) ^ B * (z * C (↑(ε⁻¹) : O)) := by
      have hεε : (C (↑ε : O) : O⟦X⟧) * C (↑(ε⁻¹) : O) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      linear_combination (-(P.p 1 ^ y)) * hεε + C (↑(ε⁻¹) : O) * hz
    rw [hε]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  have hkc := (mem_iff_le_cont hϖ hdist _ k).1 hmem
  constructor
  · obtain ⟨hne, hle⟩ := P.constant_le_rpow_of_three_le hϖ B y hB hy
    have hkc' : k ≤ (cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat := by
      rw [← ENat.coe_toNat hne] at hkc
      exact_mod_cast hkc
    have hr : max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) ≤ (de : ℝ) := Nat.le_ceil _
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hkr : (k : ℝ) ≤ (e : ℝ) * de := by
      have := mul_le_mul_of_nonneg_left hr he0
      have hk' : (k : ℝ) ≤ ((cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat : ℝ) := by exact_mod_cast hkc'
      linarith
    have hkn : k ≤ e * de := by exact_mod_cast hkr
    apply hdiv
    have hle2 : e * (κ - de) ≤ v := by rw [Nat.mul_sub]; omega
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle2
    exact ⟨↑ε * ϖ ^ t, by rw [hxe, ht, pow_add]; ring⟩
  · intro hlt
    have h0 := P.cont_X_pow_pow_eq_zero_of_gt hϖ B y hB hy hlt
    rw [h0] at hkc
    have : k = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hkc
    omega

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
end
end

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem arc_len_two_thick_letters [NeZero n] {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ} (c : ZMod n)
    (hlen : (arcOf b w S η up size).len c = 2) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
  set s := {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} with hs
  have hlen' : sInf s = 2 := hlen
  have hne : s.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Nat.sInf_empty] at hlen'
    norm_num at hlen'
  have h2 : 2 ∈ s := hlen' ▸ Nat.sInf_mem hne
  have h1 : 1 ∉ s := fun h => by
    have := Nat.sInf_le h
    omega
  constructor
  · by_contra hT
    apply h1
    refine ⟨le_rfl, ?_⟩
    simpa using hT
  · have h22 := h2.2
    convert h22 using 2
    push_cast
    ring

theorem lifts_scale (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) {f : W.EE}
    {e k : ℕ} (h : LiftsAt W A F c bb sol k₀ (lE W k * f) e) : LiftsAt W A F c bb sol k₀ f (e + k) := by
  obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := h
  refine ⟨w₁, z, h1, h2, h3, h4, ?_⟩
  have he : lE W (e + k) * f = lE W e * (lE W k * f) := by
    simp only [lE, pow_add, mul_assoc]
  have hfun : (fun kk => if kk = k₀ then lE W (e + k) * f else 0) =
      (fun kk => if kk = k₀ then lE W e * (lE W k * f) else 0) := funext fun kk => by rw [he]
  rw [hfun]
  exact h5

theorem lE_alg (W : LocWach PD LL O v n) (k : ℕ) :
    lE W k = algebraMap (LetA O n) W.EE (lA W ^ k) := by
  simp only [lE, lA, map_pow, map_natCast]

theorem algO (W : LocWach PD LL O v n) (x : O) :
    algebraMap O W.EE x = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x) := IsScalarTower.algebraMap_apply O (LetA O n) W.EE x

theorem den_step [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (Br : Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge W) (c : ZMod n) (y Bq κ : ℕ)
    (hy : 1 ≤ y) (hBq : 1 ≤ Bq) (f : W.EE) (x : O)
    (hf : InFr W c 1 (ps W 1 ^ y) f)
    (hx : InFr W c (ps W 0 ^ Bq) (ps W 1 ^ y)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ (de : ℕ) (x' : O), de ≤ ⌈max 0 ((y : ℝ) - Bq / PD.p + 2 + Real.logb PD.p y)⌉₊ ∧
      (PD.p * y < Bq → de = 0) ∧
      InFr W c 1 (ps W 1 ^ y) (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') ∧
      InFr W c (ps W 0 ^ Bq) (ps W 1 ^ y)
        (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') := by
  haveI := Fact.mk PD.hp
  set P := Br.P
  have hp0 : P.p 0 = X := rfl
  have hps : ∀ s k, ps W s ^ k = Br.cst (P.p s ^ k) := by
    intro s k; rw [Br.cst_pow, Br.ps_eq]
  have h1 : (1 : LetA O n) = Br.cst 1 := Br.cst_one.symm
  rw [hps, h1] at hf
  rw [hps, hps, hp0] at hx
  obtain ⟨U₁, U₂, hU⟩ := Br.inFr_const c hf hx
  obtain ⟨hd1, hd2⟩ := den_bound P y Bq κ hy hBq x U₁ U₂ hU
  set D := ⌈max 0 ((y : ℝ) - Bq / PD.p + 2 + Real.logb PD.p y)⌉₊ with hD
  set de : ℕ := if PD.p * y < Bq then 0 else min D κ with hde
  have hxd : ((PD.p : ℕ) : O) ^ (κ - de) ∣ x := by
    rw [hde]; split_ifs with hlt
    · simpa using hd2 hlt
    · have : κ - min D κ = κ - D := by omega
      rw [this]; exact hd1
  have hdeκ : de ≤ κ := by rw [hde]; split_ifs <;> omega
  obtain ⟨x', hx'⟩ := hxd
  refine ⟨de, x', ?_, ?_, ?_⟩
  · rw [hde]; split_ifs <;> omega
  · intro hlt; rw [hde, if_pos hlt]
  obtain ⟨u₁, hu₁, hfu⟩ := hf
  obtain ⟨F₁, hF₁⟩ := Br.range u₁ hu₁ c
  set G : PowerSeries O := C ((PD.p : ℕ) : O) ^ de * F₁ - P.p 1 ^ y * C x' with hG
  have hletu : (letE c : LetA O n) * u₁ = letE c * Br.cst F₁ := by
    funext i
    by_cases hi : i = c
    · subst hi; simp [letE, hF₁, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst]
    · simp [letE, Pi.single_apply, hi]
  have e1 : (letE c : LetA O n) * Br.cst G =
      lA W ^ de * (letE c * Br.cst 1 * u₁) - Br.cst (P.p 1 ^ y) * (letE c * algebraMap O (LetA O n) x') := by
    rw [Br.cst_one, mul_one, hletu, hG, Br.lA_eq, ← Br.cst_pow, ← Br.cst_C]
    funext i
    simp only [Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, Pi.mul_apply, Pi.sub_apply, map_sub, map_mul, map_pow]
    ring
  have hkey : algebraMap (LetA O n) W.EE (Br.cst (P.p 1 ^ y)) *
      (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') =
      algebraMap (LetA O n) W.EE (letE c * Br.cst G) := by
    rw [algO, e1]
    simp only [map_sub, map_mul] at hfu ⊢
    rw [← lE_alg]
    linear_combination (lE W de) * hfu
  refine ⟨⟨Br.cst G, Br.cst_mem G, ?_⟩, ?_⟩
  · rw [hps 1 y, hkey, mul_one]
  have hscale : lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x =
      lE W (κ - de) * (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') := by
    have hj' : lE W κ = lE W (κ - de) * lE W de := by
      unfold lE; rw [← pow_add, Nat.sub_add_cancel hdeκ]
    rw [hx', map_mul, map_pow, map_natCast, hj']
    unfold lE
    ring
  obtain ⟨u₂, hu₂, hxu⟩ := hx
  have hxu2 : algebraMap (LetA O n) W.EE (lA W ^ (κ - de) * (letE c * Br.cst G)) =
      algebraMap (LetA O n) W.EE (letE c * Br.cst (X ^ Bq) * u₂) := by
    rw [map_mul, ← hkey, ← lE_alg, ← hxu, hscale]
    ring
  have hxc := congrFun (W.EE_inj hxu2) c
  obtain ⟨F₂, hF₂⟩ := Br.range u₂ hu₂ c
  have hιeq : Br.ι (C ((PD.p : ℕ) : O) ^ (κ - de) * G) = Br.ι (X ^ Bq * F₂) := by
    have e2 : (lA W ^ (κ - de) * (letE c * Br.cst G) : LetA O n) c = Br.ι (C ((PD.p : ℕ) : O) ^ (κ - de) * G) := by
      rw [Br.lA_eq, ← Br.cst_pow]
      simp [letE, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, map_mul]
    have e3 : (letE c * Br.cst (X ^ Bq) * u₂ : LetA O n) c = Br.ι (X ^ Bq * F₂) := by
      simp [letE, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, hF₂, map_mul]
    rw [← e2, ← e3, hxc]
  have hGB := Br.inj hιeq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨u, hu⟩ := l_eq_unit_mul_pow hϖ P.hl0
  have hmem : C ϖ ^ (eO (O := O) PD.p * (κ - de)) * (C ((↑u : O) ^ (κ - de)) * G) ∈
      Ideal.span {(X : O⟦X⟧) ^ Bq} := by
    have : C ϖ ^ (eO (O := O) PD.p * (κ - de)) * (C ((↑u : O) ^ (κ - de)) * G) = X ^ Bq * F₂ := by
      rw [← hGB, hu]
      simp only [map_mul, map_pow, mul_pow, ← pow_mul]
      ring
    rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hmem2 := Cont.mem_of_pow_mul_mem hϖ (ContPA.dist_X_pow (O := O) Bq).1 _ _ hmem
  obtain ⟨U', hU'⟩ := Ideal.mem_span_singleton'.mp hmem2
  have hone : (C ((↑(u⁻¹) : O) ^ (κ - de)) : O⟦X⟧) * C ((↑u : O) ^ (κ - de)) = 1 := by
    rw [← map_mul, ← mul_pow, Units.inv_mul, one_pow, map_one]
  have hG2 : G = X ^ Bq * (C ((↑(u⁻¹) : O) ^ (κ - de)) * U') := by
    linear_combination (-G) * hone + (-(C ((↑(u⁻¹) : O) ^ (κ - de)) : O⟦X⟧)) * hU'
  refine ⟨Br.cst (C ((↑(u⁻¹) : O) ^ (κ - de)) * U'), Br.cst_mem _, ?_⟩
  rw [hps 1 y, hps 0 Bq, hp0, hkey, hG2, Br.cst_mul, mul_assoc]

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
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

theorem arc_length_two_case_down [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = false) (h2b : size (c - 1) ≤ Formalism.MainNotions.LiftingTheory.AI W F (c - 1) + η) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 15 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  classical
  have hB' := hB
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB
  obtain ⟨-, hSur, hηs, -, -, hnt, -⟩ := hSet
  have hl5 : 5 ≤ PD.p := by omega
  obtain ⟨hct, hcm⟩ := ArcLengthTwo.arc_len_two_thick_letters c hlen
  have hc1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c + 1) := by
    have h := hc
    simp only [arcOf, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hupm : up (c - 1) = true := by
    cases h : up (c - 1)
    · exact absurd (h.trans hup.symm) hdiff
    · rfl
  have hty0 : (arcOf b w S η up size).ty c = Formalism.MainNotions.LocalTheoryWindows.LT.down (size c) := by
    simp [arcOf, hup]
  have hty1 : (arcOf b w S η up size).ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1)) := by
    simp [arcOf, hupm]
  have hnn : nnDen W (arcOf b w S η up size) c = ps W 1 ^ size (c - 1) := by
    unfold nnDen prodTy
    rw [hlen, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
    simp [hty0, hty1]
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    simp only [arcOf]
    split <;> rfl
  obtain ⟨κ, x, hx⟩ := hf.2 0 (by rw [hlen]; norm_num) (size c) (by simpa using hty0)
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hW₁.1 hO hinj
  have hy1 : 1 ≤ size (c - 1) := by have := hηs (c - 1); omega
  obtain ⟨de, x', hde, hde0, hg1, hg2⟩ := ArcLengthTwo.den_step W Br c (size (c - 1)) (size c + S) κ hy1
    (by have := hηs c; omega) f x (by rw [← hnn]; exact hf.1) (by rw [← hnn]; exact hx)
  set g := lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x' with hgdef
  have hdown : ∀ s < (arcOf b w S η up size).len c, ∀ bs,
      (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + (arcOf b w S η up size).S)) (nnDen W (arcOf b w S η up size) c) g := by
    intro s hs bs hbs
    rw [hlen] at hs
    interval_cases s
    · simp only [Nat.cast_zero, sub_zero, hty0, Formalism.MainNotions.LocalTheoryWindows.LT.down.injEq] at hbs
      subst hbs
      rw [hnn]
      exact hg2
    · simp [hty1] at hbs
  have hgl : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ g (rr + (arcOf b w S η up size).σ PD.p) :=
    liftsAt_thick_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL
      hO hOv hinj hArc hArcL hNN hW₁ hW₂ hSur rr hkill hbb hk₀ g (by rw [hnn]; exact hg1) hdown
  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩ := constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5
    hHF hArcL hW₁ hSur rr hkill hbb
  have hcst : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ (algebraMap O W.EE x')
      (rr + (arcOf b w S η up size).σ PD.p) :=
    liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL
      hFL hO hOv hinj hArc hArcL hW₁ hW₂ hSur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr x'
  have hcst' : LiftsAt W (arcOf b w S η up size) F c bb sol k₀
      (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') (rr + (arcOf b w S η up size).σ PD.p) :=
    LiftsAtT.letter W (arcOf b w S η up size) F c bb sol k₀ hbb hcst
  have hsum := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀ hcst' hgl
  have esum : algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x' + g = lE W de * f := by
    rw [hgdef]; ring
  rw [esum] at hsum
  have hfin := ArcLengthTwo.lifts_scale W (arcOf b w S η up size) F c bb sol k₀ hsum
  refine ⟨rr + (arcOf b w S η up size).σ PD.p + de, ?_, hfin⟩

  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c, hct⟩]
  have hSgeq : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    unfold Formalism.MainNotions.N.Ln17.Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg; rw [hhB]
  rw [hSgeq] at hrr hσ ⊢
  set Sg' := Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η with hSg'
  have hx11 : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hSg1 : 1 ≤ Sg' := by
    rw [hSg']; unfold Formalism.MainNotions.N.FrobeniusPowerSeries.Sg
    have hh1 : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by
      have := hηs c; have := hct.2; exact_mod_cast (by omega : 1 ≤ b + η + S)
    have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ ((w : ℝ) + S + η) / PD.p := by positivity
    have h3 : 0 ≤ Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ)) :=
      Real.logb_nonneg (by linarith) (by linarith)
    linarith
  have hband0 : 0 ≤ bandI PD.p b w S η size Cb := by unfold bandI; split_ifs <;> norm_num
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg _
  have hηb0 : 0 ≤ (η : ℝ) * bandI PD.p b w S η size Cb := mul_nonneg hη0 hband0
  push_cast
  rcases lt_or_ge (PD.p * size (c - 1)) (size c + S) with hlt | hge
  · rw [hde0 hlt]; push_cast; linarith
  have hb1 : 1 ≤ b := by have := hηs c; have := hct.2; omega
  have hw' : size (c - 1) ≤ w := hnt (c - 1) hcm
  have hAI := ArcLengthTwo.aI_le W F hB' CR hWR c hct hc1
  have hwA : (size (c - 1) : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) + η := by exact_mod_cast h2b
  obtain ⟨k1, k2⟩ := case2b PD.p hp11 b w (size (c - 1)) S η (size c) hb1 hηb hSb hwb hw' hy1 hct.1 hct.2
    _ hAI hwA
  have hDle : (de : ℝ) ≤ η + 5 * Sg' := by
    have hm0 : 0 ≤ max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ)) := le_max_left _ _
    have hc' := Nat.ceil_lt_add_one hm0
    have hde' : (de : ℝ) ≤ (⌈max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ))⌉₊ : ℝ) := by exact_mod_cast hde
    have hmax : max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ)) ≤ η + 5 * Sg' - 1 := by
      apply max_le (by linarith)
      push_cast
      linarith
    linarith
  by_cases hband : Formalism.MainNotions.TruncatedSeriesCountingBounds.Band PD.p b S η size
      (Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb
  · have h1 : bandI PD.p b w S η size Cb = 1 := by unfold bandI; rw [if_pos hband]
    rw [h1]; linarith
  · have h0 : bandI PD.p b w S η size Cb = 0 := by unfold bandI; rw [if_neg hband]
    rw [hhB] at hband
    have hnb := fun hle => hband ⟨c - 1, hcm, Or.inl (by rw [sub_add_cancel]; exact hct), hle⟩
    have hη4 := k2 Cb hCb hge hnb
    rw [h0]; linarith

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

private theorem sg_nonneg_of {x sg : ℝ} (h0 : 0 ≤ x) (h : x ≤ 3 * sg) : 0 ≤ sg := by linarith

private theorem bandI_nonneg (l b w S η : ℕ) (size : ZMod n → ℕ) (Cb : ℝ) :
    0 ≤ bandI l b w S η size Cb := by
  unfold bandI; split_ifs <;> norm_num

theorem arc_length_one_two_theorem [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 15 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨hOK, -, -, -, hσ⟩ := arcBasic W F hB
  have hSg : 0 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := sg_nonneg_of (Nat.cast_nonneg _) hσ
  have hbd : 0 ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) (bandI_nonneg _ _ _ _ _ _ _)
  cases hup : up c with
  | true =>
    by_cases h1b : PD.p * (size (c - 1) + S + η) + η < size c
    · obtain ⟨e, he, hl⟩ := arc_length_one_or_two_case_b W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb hlen hdiff hOK hσ hup h1b
      exact ⟨e, by linarith, hl⟩
    · obtain ⟨e, he, hl⟩ := arc_length_one_or_two_case_c W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb hlen hdiff hOK hσ hup h1b
      exact ⟨e, by linarith, hl⟩
  | false =>
    by_cases h2a : Formalism.MainNotions.LiftingTheory.AI W F (c - 1) + η + 1 ≤ size (c - 1)
    · obtain ⟨e, he, hl⟩ := exists_liftsAt_arcOf_of_up_eq_false W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb hlen hdiff hOK hσ hup h2a
      exact ⟨e, by linarith, hl⟩
    · obtain ⟨e, he, hl⟩ := arc_length_two_case_down W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb hlen hdiff hOK hσ hup (by omega)
      exact ⟨e, by linarith, hl⟩

theorem exists_liftsAt_of_arc_len_three_of_up [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hlen : (arcOf b w S η up size).len c = 3) (hU : up (c - 2) = true) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 34 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨hOK, -, -, -, hσ⟩ := arcBasic W F hB
  have hSg : 0 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := sg_nonneg_of (Nat.cast_nonneg _) hσ
  have hbd : 0 ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) (bandI_nonneg _ _ _ _ _ _ _)
  by_cases hth : size (c - 2) < Formalism.MainNotions.LiftingTheory.AI W F (c - 2) + η + 2 * (arcOf b w S η up size).σ PD.p + 2
  · exact exists_exponent_le_and_liftsAt_arc W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb halt hsm hlen hU hOK hσ hth
  · obtain ⟨e, he, hl⟩ := exists_liftsAt_le_of_len_three_of_up W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb halt hsm hlen hU hOK hσ (by omega)
    exact ⟨e, by linarith, hl⟩

theorem arc_length_three_theorem [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 22 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨hOK, -, -, -, hσ⟩ := arcBasic W F hB
  have hSg : 0 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := sg_nonneg_of (Nat.cast_nonneg _) hσ
  have hbd : 0 ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) (bandI_nonneg _ _ _ _ _ _ _)
  by_cases hy : size (c - 1) < PD.p * (size (c - 2) + S + η)
  · exact arc_length_three_case_d W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy
  · obtain ⟨e, he, hl⟩ := arc_length_three_case_c W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ (by omega)
    exact ⟨e, by linarith, hl⟩

theorem arc_proposition_alternative [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hscope : (arcOf b w S η up size).len c ≤ 2 ∨ 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨hOK, -, hlen3, -, hσ⟩ := arcBasic W F hB
  have hSg : 0 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := sg_nonneg_of (Nat.cast_nonneg _) hσ
  have hbd : 0 ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) (bandI_nonneg _ _ _ _ _ _ _)
  have hSg1 : 1 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
    unfold Formalism.MainNotions.N.Ln17.Sg
    have h1 : (0 : ℝ) ≤ (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (PD.p : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ ((w : ℝ) + S + η) / PD.p := by positivity
    have h3 : (0 : ℝ) ≤ Real.logb PD.p (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := by
      rcases Nat.eq_zero_or_pos (TruncatedSeriesCountingBounds.hB b w S η size) with h0 | hpos
      · simp [h0]
      · apply Real.logb_nonneg
        · have : (2 : ℝ) ≤ PD.p := by
            have h11 : 11 ≤ PD.p := hB.1
            exact_mod_cast (by omega : 2 ≤ PD.p)
          linarith
        · have : (1 : ℝ) ≤ (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) := by exact_mod_cast hpos
          linarith
    linarith
  have hl1 : 1 ≤ (arcOf b w S η up size).len c := (hOK.2.2.1 c hc).1
  have hl3 : (arcOf b w S η up size).len c ≤ 3 := hlen3 halt c hc
  rcases (show (arcOf b w S η up size).len c = 1 ∨ (arcOf b w S η up size).len c = 2 ∨ (arcOf b w S η up size).len c = 3 by omega) with h | h | h
  · obtain ⟨e, he, hl⟩ := arc_single_type_bound W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf (by
      intro s hs
      have : s = 0 := by omega
      subst this
      simp)
    exact ⟨e, by linarith, hl⟩
  · have hdiff : up (c - 1) ≠ up c := by
      have := (halt (c - 1)).1
      simp only [sub_add_cancel] at this
      exact fun h => this h.symm
    obtain ⟨e, he, hl⟩ := arc_length_one_two_theorem W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb h hdiff
    exact ⟨e, by linarith, hl⟩
  · have hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4 := by
      rcases hscope with h' | h'
      · omega
      · exact h'
    cases hU : up (c - 2) with
    | false =>
      obtain ⟨e, he, hl⟩ := arc_length_three_theorem W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm h hU
      exact ⟨e, by linarith, hl⟩
    | true =>
      obtain ⟨e, he, hl⟩ := exists_liftsAt_of_arc_len_three_of_up W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb halt hsm h hU
      exact ⟨e, by linarith, hl⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
