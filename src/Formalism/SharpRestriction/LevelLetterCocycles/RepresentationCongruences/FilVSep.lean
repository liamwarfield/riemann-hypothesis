module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ContentStep

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FilVSep
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup
open scoped TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem filV_sep {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (z : V ⊗[Qp] BdR) (hz : ∀ a : ℤ, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  classical
  let bV := Module.Free.chooseBasis Qp V
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hco : ∀ (a : ℤ) (w : V ⊗[Qp] BdR), w ∈ FilV PD (LL := LL) (V := V) a →
      ∀ j, E w j ∈ PD.Fil a := by
    intro a w hw
    obtain ⟨y, rfl⟩ := hw
    induction y using TensorProduct.induction_on with
    | zero => intro j; simp
    | tmul x f =>
      intro j
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        Submodule.coe_subtype, E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul,
        Finsupp.mapRange_apply]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ f.2
    | add x y hx hy =>
      intro j
      rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]
      exact (PD.Fil a).add_mem (hx j) (hy j)
  have h0 : E z = 0 := by
    ext j
    exact PD.Fil_sep _ fun a => hco a z (hz a) j
  simpa using congrArg E.symm h0

theorem filS_top (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (A : ArcP n)
    (T : LocLat G Qp LL O) (hW : Win W A T) (a : ZMod n) (s : ℕ) (u : ℤ)
    (hu : ∀ x ∈ (A.ty (a - (s : ZMod n))).win A.G₀ A.S A.η, x < u) :
    FilS W T a s u = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨hxF, hxL⟩ := Submodule.mem_inf.mp hx
  suffices hx0 : x = 0 by simp [hx0]
  set i : ZMod n := a - (s : ZMod n) with hi
  obtain ⟨hbij, -, -⟩ := hcase
  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij
  let τ : K →ₐ[Qp] LL := (W.emb i).comp e.symm.toAlgHom
  have hez : ∀ z : K₀, e z = algebraMap K₀ K z := fun z => rfl
  have hover : ∀ z : K₀, τ (algebraMap K₀ K z) = W.emb i z := by
    intro z
    have : e.symm (algebraMap K₀ K z) = z := by
      rw [← hez, AlgEquiv.symm_apply_apply]
    show W.emb i (e.symm (algebraMap K₀ K z)) = W.emb i z
    rw [this]
  have hOver : Formalism.MainNotions.LiftingTheory.Over W τ i := by
    ext z
    exact hover z
  have hJ := hW.2 i τ hOver
  have hE : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
    Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T i τ hover hbij.2 ⟨x, hxL, rfl⟩
  have hV : ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) u :=
    (Submodule.mem_inf.mp hxF).2
  have hall : ∀ k : ℕ, ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ (u + k) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, add_zero]
      exact Submodule.mem_inf.mpr ⟨hE, hV⟩
    | succ k ih =>
      have heq : FildR PD T.ρ τ (u + k + 1) = FildR PD T.ρ τ (u + k) := by
        by_contra h
        have := hu _ (hJ (u + k) h)
        omega
      rw [Nat.cast_succ, ← add_assoc, heq]
      exact ih
  have hallV : ∀ b : ℤ, ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) b := by
    intro b
    by_cases h : b ≤ u
    · exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti h hV
    · have hk := (Submodule.mem_inf.mp (hall (b - u).toNat)).2
      have : u + ((b - u).toNat : ℤ) = b := by omega
      rwa [this] at hk
  have h0 := filV_sep _ hallV
  exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (h0.trans (map_zero _).symm)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThinLetterType
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

theorem arc_letter_type_eq_ite [NeZero n] {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ} (i : ZMod n) :
    (arcOf b w S η up size).ty i = if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i) :=
  rfl

theorem arc_length_two_reduction [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂)
    (hArc : ArcCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK)
    (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = false)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O)
    (hlt : dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁ ∈ FilS W T₁ c 1 (size (c - 1)))
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁) =
      ((PD.p : LL) ^ (2 * (arcOf b w S η up size).σ PD.p)) •
        dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 9 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  set A := arcOf b w S η up size with hA
  have hup1 : up (c - 1) = true := by
    cases h : up (c - 1) <;> simp_all
  have hty0 : A.ty c = Formalism.MainNotions.LocalTheoryWindows.LT.down (size c) := by
    rw [hA, arc_letter_type_eq_ite, hup]; rfl
  have hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1)) := by
    rw [hA, arc_letter_type_eq_ite, hup1]; rfl
  have hl5 : 5 ≤ PD.p := by have := hB.1; omega
  have hcase : Formalism.MainNotions.LiftingTheory.CaseA W := hB.2.1.1
  have hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick := by
    intro s _
    rw [hA, arc_letter_type_eq_ite]
    split_ifs <;> rfl
  have hden : nnDen W A c = ps W 1 ^ size (c - 1) := by
    simp only [nnDen, prodTy, hlen, Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      sub_zero, Nat.cast_one, hty0, hty1, pow_zero, one_mul]
  obtain ⟨hf1, hf2⟩ := hf
  have hL := liftsAt_thin_letter_type W A F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
    hW₁ hW₂ hbb ({1} : Finset ℕ) (by
      intro s hs
      rw [Finset.mem_singleton] at hs
      subst hs
      refine ⟨by omega, size (c - 1), ?_⟩
      rw [Nat.cast_one, hty1]) b₁ sol₁ hb₁ c₁ (2 * A.σ PD.p) (by
      intro s hs bs hbs
      rw [Finset.mem_singleton] at hs
      subst hs
      rw [Nat.cast_one, hty1] at hbs
      cases hbs
      exact hlt) hpr f (by
      simpa [Nat.cast_one, hty1, ← hden] using hf1) (by
      intro s hs bs hbs
      obtain ⟨κ, x, hx⟩ := hf2 s hs bs hbs
      refine ⟨κ, x, ?_⟩
      simpa [Nat.cast_one, hty1, ← hden] using hx) (by
      intro s hs hs1 bs hbs
      have hs0 : s = 0 := by
        rw [Finset.mem_singleton] at hs1
        omega
      subst hs0
      rw [Nat.cast_zero, sub_zero, hty0] at hbs
      cases hbs)
  refine ⟨2 * A.σ PD.p + A.σ PD.p, ?_, hL⟩
  push_cast
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthOneOrTwoCaseC
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsLE
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthOneTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem lifts_lE (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)
    {f : W.EE} {k e : ℕ} (h : LiftsAt W A F c b sol k₀ (lE W k * f) e) :
    LiftsAt W A F c b sol k₀ f (k + e) := by
  unfold LiftsAt at h ⊢
  obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := h
  refine ⟨w₁, z, h1, h2, h3, h4, ?_⟩
  have hl : lE W e * (lE W k * f) = lE W (k + e) * f := by
    unfold lE
    ring
  rw [hl] at h5
  exact h5

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthOneTwo
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

theorem arc_length_one_or_two_case_c [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hup : up c = true) (hnb : ¬ (PD.p * (size (c - 1) + S + η) + η < size c)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 9 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  classical
  haveI : Fact PD.p.Prime := Fact.mk PD.hp
  obtain ⟨hl11, hSet, h20w, h20η, h20S, -⟩ := hB
  obtain ⟨-, hsur, hsize, -, -, hnt, -⟩ := hSet
  have hl5 : 5 ≤ PD.p := by omega

  have hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 2 := hlen
  have hne : {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Nat.sInf_empty] at hlen'
    exact absurd hlen' (by norm_num)
  have h2mem := Nat.sInf_mem hne
  rw [hlen'] at h2mem
  have hnt1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    have e : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
    have := h2mem.2
    rwa [e] at this
  have hthc : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c := by
    by_contra h
    have h1 : (1 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} :=
      ⟨le_refl 1, by simpa using h⟩
    have := Nat.sInf_le h1
    omega
  have hup1 : up (c - 1) = false := by
    rw [hup] at hdiff; simpa using hdiff
  have htyc : (arcOf b w S η up size).ty c = Formalism.MainNotions.LocalTheoryWindows.LT.up (size c) := by
    simp [arcOf, hup]
  have hty1 : (arcOf b w S η up size).ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - 1)) := by
    simp [arcOf, hup1]
  have hps0 : ps W 0 = qA W := by simp [ps]
  have hnn : nnDen W (arcOf b w S η up size) c = qA W ^ size c := by
    unfold nnDen prodTy
    rw [hlen, Finset.prod_range_succ, Finset.prod_range_one]
    simp only [Nat.cast_zero, sub_zero, Nat.cast_one, htyc, hty1, hps0, pow_zero, mul_one]
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    show (if up (c - (s : ZMod n)) then Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - (s : ZMod n)))
      else Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s : ZMod n)))).thick = true
    split_ifs <;> rfl

  obtain ⟨hf1, hf2⟩ := hf
  rw [hnn] at hf1
  obtain ⟨κ, x, hκx⟩ := hf2 1 (by rw [hlen]; norm_num) (size (c - 1)) (by simpa using hty1)
  rw [hnn] at hκx
  change InFr W c (ps W 1 ^ (size (c - 1) + S)) (qA W ^ size c) _ at hκx
  have hw1 : 1 ≤ size (c - 1) := by have := hsize (c - 1); omega
  have hwle : size (c - 1) ≤ w := hnt (c - 1) hnt1
  have hb1 : 1 ≤ b := by omega
  have hb₀1 : 1 ≤ size c := by have := hsize c; omega

  obtain ⟨x'', hx''⟩ := ArcLengthOneTwo.content_step W hcase hP9 hO c (size c) (size (c - 1) + S) κ (by omega) f x
    hf1 hκx
  have hxE : ∀ z : O, algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) z) = algebraMap O W.EE z :=
    fun z => (IsScalarTower.algebraMap_apply O (LetA O n) W.EE z).symm
  have hlE : ∀ k : ℕ, algebraMap (LetA O n) W.EE (lA W ^ k) = lE W k := by
    intro k; simp [lA, lE]
  have hg1 : InFr W c 1 (nnDen W (arcOf b w S η up size) c)
      (lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * f -
        algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x'') := by
    rw [hnn]
    obtain ⟨u₀, hu₀, e1⟩ := hf1
    refine ⟨lA W ^ ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) * u₀ - qA W ^ size c * algebraMap O (LetA O n) x'',
      Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ _) _) hu₀)
        (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (GS.qA_mem W) _) (Subalgebra.algebraMap_mem _ _)), ?_⟩
    simp only [map_mul, map_sub, map_one, mul_one, hlE, hxE] at e1 ⊢
    linear_combination lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * e1
  have hgdown : ∀ s < (arcOf b w S η up size).len c, ∀ bs,
      (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + (arcOf b w S η up size).S)) (nnDen W (arcOf b w S η up size) c)
        (lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * f -
          algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x'') := by
    intro s hs bs hbs
    rw [hlen] at hs
    interval_cases s
    · simp [htyc] at hbs
    · simp only [Nat.cast_one, hty1, Formalism.MainNotions.LocalTheoryWindows.LT.down.injEq] at hbs
      subst hbs
      rw [hnn]
      exact hx''

  have hNg := liftsAt_thick_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0
    hSec hGL hFL hO hOv hinj hArc hArcL hNN hW₁ hW₂ hsur rr hkill hbb hk₀ _ hg1 hgdown
  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩ := constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5
    hHF hArcL hW₁ hsur rr hkill hbb
  have hC := liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0
    hSec hGL hFL hO hOv hinj hArc hArcL hW₁ hW₂ hsur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr x''
  have hCL := LiftsAtT.letter W (arcOf b w S η up size) F c bb sol k₀ hbb hC
  have hsum := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀ hNg hCL
  rw [sub_add_cancel] at hsum
  have hfin := ArcLengthOneTwo.lifts_lE W (arcOf b w S η up size) F c bb sol k₀ hsum
  refine ⟨ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) + (rr + (arcOf b w S η up size).σ PD.p), ?_, hfin⟩

  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c, hthc⟩]
  have hSgeq : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    rw [CaseA.sg_eq]; unfold Formalism.MainNotions.N.Ln17.Sg; rw [hhB]; push_cast; ring
  rw [hSgeq] at hrr hσ ⊢
  obtain ⟨-, -, -, -, a5, a6, a7⟩ := CaseA.sg_ge PD.p (b + η + S) w S η hl11 (by omega)
  have hde := ArcLengthOneTwo.deA_le (l := PD.p) (size c) (size (c - 1) + S) (by omega) hb₀1
  have hband0 : 0 ≤ bandI PD.p b w S η size Cb := by unfold bandI; split_ifs <;> norm_num
  have hηb : (0 : ℝ) ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) hband0
  have hlr1 : (1 : ℝ) < PD.p := by exact_mod_cast (by omega : 1 < PD.p)
  have hlr0 : (0 : ℝ) < PD.p := by linarith
  push_cast
  by_cases h1c : PD.p * (size (c - 1) + S) ≤ size c
  · have hc1 := case1c PD.p hl11 b w (size (c - 1)) S η (size c) hb1 h20η h20S h20w hwle hthc.1 hthc.2 h1c
      (Nat.le_of_not_lt hnb) (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) : ℝ) (by push_cast at hde; exact hde)
    have hBand : Formalism.MainNotions.TruncatedSeriesCountingBounds.Band PD.p b S η size (Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb :=
      ⟨c - 1, hnt1, Or.inl (by rw [sub_add_cancel]; exact hthc), by rw [hhB]; exact hc1.2 Cb hCb⟩
    have hbandI : bandI PD.p b w S η size Cb = 1 := by unfold bandI; rw [if_pos hBand]
    rw [hbandI]
    linarith [hc1.1]
  · have hlt : (size c : ℝ) / PD.p < (size (c - 1) : ℝ) + S := by
      rw [div_lt_iff₀ hlr0]
      have : size c < PD.p * (size (c - 1) + S) := Nat.lt_of_not_le h1c
      have hr : ((size c : ℕ) : ℝ) < ((PD.p * (size (c - 1) + S) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hr
      linarith
    have hlog0 : 0 ≤ Real.logb PD.p (size c : ℝ) := Real.logb_nonneg hlr1 (by exact_mod_cast hb₀1)
    have hlogle : Real.logb PD.p (size c : ℝ) ≤ Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ)) := by
      apply Real.logb_le_logb_of_le hlr1 (by exact_mod_cast (by omega : 0 < size c))
      have : (size c : ℝ) ≤ b + η := by exact_mod_cast hthc.2
      push_cast
      have : (0 : ℝ) ≤ S := Nat.cast_nonneg _
      linarith
    have hmax : max 0 ((size c : ℝ) / PD.p - ((size (c - 1) + S : ℕ) : ℝ) + 2 + Real.logb PD.p (size c)) ≤
        2 + Real.logb PD.p (size c) := by
      push_cast
      exact max_le (by linarith) (by linarith)
    have hη0 : (0 : ℝ) ≤ η * (PD.p : ℝ)⁻¹ := mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 hlr0.le)
    linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
