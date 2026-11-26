module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitPi0InEE
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantsTypeT
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

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

theorem N_typeT [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCoreT W) (hGL : ArcGamLiftCoreT W) (hFL : ArcFilLowCoreT W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLppT W A T₂ c b k₀)
    (f : W.EE) (hf : InFr W c 1 (nnDen W A c) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c) f) :
    LiftsAtT W A F c b sol k₀ f (rr + A.σ PD.p) := by
  have hR := NTB.ringData_of_crystalline (hcase := hcase) (hP9 := hP9) (T := T₂) (hT := And.left hW₂)
  have hΔ := NTB.isUnit_prime_sub_one (W := W) (hl := hl) (hOv := hOv) (hinj := hinj)
  have hfnn := NTB.nn_of (hcase := hcase) (hP9 := hP9) (hinj := hinj) (hR := hR) (A := A) (c := c)
    (hthick := hthick) (f := f) (hf := hf) (hdown := hdown)
  exact NTB.ntype_core (hcase := hcase) (hl := hl) (hP9 := hP9) (A := A) (hA := hA) (c := c)
    (hc := hc) (F := F) (hArc := hArc) (hNN := hNN) (hW₁ := hW₁) (hW₂ := hW₂) (hΔ := hΔ) (rr := rr)
    (hrr := hrr c hc) (b := b) (sol := sol) (k₀ := k₀) (hb := hb) (hk₀ := hk₀) (f := f) (hfnn := hfnn)

theorem constants_typeT (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCoreT W) (hGL : ArcGamLiftCoreT W) (hFL : ArcFilLowCoreT W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLppT W A T₂ c b k₀)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ rr) • dv W T₂ (A.len c) b (Pi.single k₀ 1)) (x : O) :
    LiftsAtT W A F c b sol k₀ (algebraMap O W.EE x) (rr + A.σ PD.p) := by
  refine NTB.letter_const (A := A) (F := F) (c := c) (b := b) (sol := sol) (k₀ := k₀) (hb := hb)
    (x := x) (h := ?_)
  refine TC.C_typeT_of (hA := hA) (hc := hc) (hthick := hthick) (hcase := hcase) (hl := hl)
    (hP9 := hP9) (hSec := hSec) (hGL := hGL) (hFL := hFL) (hArc := hArc) (hW₁ := hW₁) (hW₂ := hW₂)
    (hb := hb) (Si := ∅) (hSi := by simp) (b₁ := b₁) (sol₁ := sol₁) (hb₁ := hb₁) (c₁ := c₁)
    (s₀ := rr) (hlt := by simp) (hpr := hpr) (hf := ?_) (hdown := ?_) (hup := ?_)
  · rw [Finset.prod_empty]
    unfold InFr
    refine ⟨algebraMap O (LetA O n) x, ?_, ?_⟩
    · simp
    · simp [IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  · intro s _ bs _
    refine ⟨0, x, ?_⟩
    unfold InFr
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [lE]
  · intro s _ _ bs _
    refine ⟨0, x, ?_⟩
    unfold InFr
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [lE]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CTypeT
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

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

theorem C_typeT (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCoreT W) (hGL : ArcGamLiftCoreT W) (hFL : ArcFilLowCoreT W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol)
    (Si : Finset ℕ) (hSi : ∀ s ∈ Si, s < A.len c ∧ ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O) (s₀ : ℕ)
    (hlt : ∀ s ∈ Si, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T₁ (A.len c) b₁ c₁ ∈ FilS W T₁ c s bs)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ s₀) • dv W T₂ (A.len c) b (Pi.single k₀ 1))
    (f : W.EE) (hf : InFr W c 1 (∏ s ∈ Si, ps W s ^ (match A.ty (c - (s : ZMod n)) with
        | .up bs => bs | _ => 0)) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x))
    (hup : ∀ s < A.len c, s ∉ Si → ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ A.η) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    LiftsAtT W A F c b sol k₀ f (s₀ + A.σ PD.p) :=
  TC.C_typeT_of W A F c b sol k₀ hA hc hthick hcase hl hP9 hSec hGL hFL hArc hW₁ hW₂ hb Si hSi b₁ sol₁ hb₁ c₁ s₀
    hlt hpr f hf hdown hup

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

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

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

theorem LiftsAt.liftsAt_mono {f : W.EE} {e e' : ℕ} (he : e ≤ e') (h : LiftsAt W A F c b sol k₀ f e) :
    LiftsAt W A F c b sol k₀ f e' :=
  LiftsAtT.mono W A F c b sol k₀ he h

theorem LiftsAt.add_proof {f f' : W.EE} {e : ℕ} (h : LiftsAt W A F c b sol k₀ f e)
    (h' : LiftsAt W A F c b sol k₀ f' e) : LiftsAt W A F c b sol k₀ (f + f') e :=
  LiftsAtT.add W A F c b sol k₀ h h'

theorem liftsAt_thick_letter_type [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLpp W A T₂ c b k₀)
    (f : W.EE) (hf : InFr W c 1 (nnDen W A c) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c) f) :
    LiftsAt W A F c b sol k₀ f (rr + A.σ PD.p) :=
  N_typeT W A F c b sol k₀ hA hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hArcL hNN hW₁ hW₂
    hsur rr hrr hb hk₀ f hf hdown

theorem liftsAt_constants_type (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLpp W A T₂ c b k₀)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ rr) • dv W T₂ (A.len c) b (Pi.single k₀ 1)) (x : O) :
    LiftsAt W A F c b sol k₀ (algebraMap O W.EE x) (rr + A.σ PD.p) :=
  constants_typeT W A F c b sol k₀ hA hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hArcL
    hW₁ hW₂ hsur rr hrr hb hk₀ b₁ sol₁ hb₁ c₁ hpr x

theorem liftsAt_thin_letter_type (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol)
    (Si : Finset ℕ) (hSi : ∀ s ∈ Si, s < A.len c ∧ ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O) (s₀ : ℕ)
    (hlt : ∀ s ∈ Si, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T₁ (A.len c) b₁ c₁ ∈ FilS W T₁ c s bs)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ s₀) • dv W T₂ (A.len c) b (Pi.single k₀ 1))
    (f : W.EE) (hf : InFr W c 1 (∏ s ∈ Si, ps W s ^ (match A.ty (c - (s : ZMod n)) with
        | .up bs => bs | _ => 0)) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x))
    (hup : ∀ s < A.len c, s ∉ Si → ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ A.η) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    LiftsAt W A F c b sol k₀ f (s₀ + A.σ PD.p) :=
  C_typeT W A F c b sol k₀ hA hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hW₁ hW₂ hb Si hSi
    b₁ sol₁ hb₁ c₁ s₀ hlt hpr f hf hdown hup

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PpLeHLD
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYB

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

variable (W : LocWach PD LL O v n)

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem γ_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  show W.γD T W.gam (a • x) = W.γA W.gam a • W.γD T W.gam x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem γA_lA_pow (k : ℕ) : W.γA W.gam (lA W ^ k) = lA W ^ k := by
  unfold lA
  rw [map_pow, map_natCast]

def HLD (T : LocLat G Qp LL O) (c : ZMod n) : AddSubgroup (W.DD T) where
  carrier := {x | (letE (O := O) c : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := ⟨smul_zero _, fun δ _ => map_zero _⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [smul_add, hx1, hy1], fun δ hδ => by rw [map_add (f := _), hx2 δ hδ, hy2 δ hδ]⟩
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [smul_neg, hx1], fun δ hδ => by rw [map_neg, hx2 δ hδ]⟩

theorem Pp_le_HLD (T : LocLat G Qp LL O) (c : ZMod n) : Pp W T c 1 ≤ HLD W T (c + 1) := by
  have hφE : W.φA (letE (O := O) c) = letE (c + 1) := by
    funext k
    unfold letE LocWach.φA letφ
    change W.φ₀ ((Pi.single c 1 : LetA O n) (k - 1)) = (Pi.single (c + 1) 1 : LetA O n) k
    by_cases hk : k = c + 1
    · subst hk
      simp
    · have hk' : k - 1 ≠ c := by
        intro h'
        apply hk
        rw [← h', sub_add_cancel]
      rw [Pi.single_eq_of_ne hk', Pi.single_eq_of_ne hk, map_zero]
  have hid : ∀ d : ZMod n, (letE (O := O) d : LetA O n) * letE d = letE d := by
    intro d
    funext k
    unfold letE
    by_cases hk : k = d
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  unfold Pp
  rw [AddSubgroup.closure_le]
  rintro z ⟨a, ha, x, ⟨hxN, hxl⟩, rfl⟩
  obtain ⟨_, hxD⟩ : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hxN
  obtain ⟨y, _, rfl⟩ := hxl
  simp only [pow_one, LinearMap.smul_apply, LinearMap.id_apply] at hxD ⊢
  change _ ∧ _
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [φD_smulA W T, hφE]
    simp only [smul_smul]
    congr 1
    linear_combination a * hid (c + 1)
  · rw [hsl, ← W.φγ_comm, hxD δ hδ, ha δ hδ]

theorem Pp_smul (T : LocLat G Qp LL O) (c : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T}
    (hy : y ∈ Pp W T c 1) : a • y ∈ Pp W T c 1 := by
  unfold Pp at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    exact ⟨a * b, W.AΔ.mul_mem ha hb, x, hx, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

theorem InNΔi_γ (T : LocLat G Qp LL O) (c : ZMod n) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (W.γ T x) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨hN, hD⟩ : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := h1
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have hγE : W.γA W.gam (letE (O := O) c) = letE c := by
    funext k
    unfold letE LocWach.γA letγ
    change W.γ₀ W.gam ((Pi.single c 1 : LetA O n) k) = (Pi.single c 1 : LetA O n) k
    by_cases hk : k = c
    · subst hk
      simp
    · rw [Pi.single_eq_of_ne hk, map_zero]
  refine ⟨?_, ?_⟩
  · show W.γD T W.gam x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (W.γD T W.gam x) = W.γD T W.gam x
    refine ⟨W.N_Γ T W.gam x hN, fun δ hδ => ?_⟩
    rw [← W.γD_mul, mul_comm, W.γD_mul, hD δ hδ]
  · obtain ⟨y, hy, rfl⟩ := h2
    refine ⟨W.γD T W.gam y, W.N_Γ T W.gam y hy, ?_⟩
    show (letE c • LinearMap.id) (W.γD T W.gam y) = W.γD T W.gam ((letE c • LinearMap.id) y)
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [hsl, hγE]

theorem Pp_γ (T : LocLat G Qp LL O) (c : ZMod n) {y : W.DD T} (hy : y ∈ Pp W T c 1) :
    W.γ T y ∈ Pp W T c 1 := by
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have hcomm : ∀ (g h : W.Gam) (a : LetA O n), W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
    intro g h a
    funext k
    unfold LocWach.γA letγ
    change W.γ₀ g (W.γ₀ h (a k)) = W.γ₀ h (W.γ₀ g (a k))
    rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]
  unfold Pp at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨W.γA W.gam a, ?_, W.γ T x, InNΔi_γ W T c hx, ?_⟩
    · show ∀ δ ∈ W.DelF, W.γA δ (W.γA W.gam a) = W.γA W.gam a
      intro δ hδ
      rw [hcomm, ha δ hδ]
    · show W.γD T W.gam (a • (W.φD T ^ 1) x) = W.γA W.gam a • (W.φD T ^ 1) (W.γD T W.gam x)
      rw [pow_one, hsl, W.φγ_comm]
  | zero => rw [map_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [map_add (f := _)]; exact add_mem hu hw
  | neg u _ hu => rw [map_neg]; exact neg_mem hu

theorem Pp_qpow (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ)
    (hq : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x → qA W ^ k • W.φD T x ∈ W.N T) {y : W.DD T}
    (hy : y ∈ Pp W T c 1) : qA W ^ k • y ∈ W.NΔ T := by
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have htor : ∀ g h : W.Gam, g ∈ W.DelF → h ∈ W.DelF → g * h ∈ W.DelF := by
    intro g h hg hh
    rw [W.DelF_def] at hg hh ⊢
    obtain ⟨a, ha, hga⟩ := hg
    obtain ⟨b, hb, hhb⟩ := hh
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_mul, hga, one_pow, mul_comm a b, pow_mul, hhb, one_pow, one_mul]
  have hinv : ∀ g : W.Gam, g ∈ W.DelF → g⁻¹ ∈ W.DelF := by
    intro g hg
    rw [W.DelF_def] at hg ⊢
    obtain ⟨a, ha, hga⟩ := hg
    exact ⟨a, ha, by rw [inv_pow, hga, inv_one]⟩
  have hπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := by
    intro δ hδ
    funext k
    unfold LocWach.γA letγ LocWach.π₀
    change W.γ₀ δ W.π₀₁ = W.π₀₁
    unfold LocWach.π₀₁
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sub, map_one, map_natCast, map_sum]
    congr 1
    have hm : ∀ δ' : W.Gam, W.γ₀ δ (W.γ₀ δ' (1 + PowerSeries.X)) = W.γ₀ (δ * δ') (1 + PowerSeries.X) :=
      fun δ' => by rw [map_mul, AlgHom.mul_apply]
    simp only [hm]
    exact Finset.sum_nbij' (δ * ·) (δ⁻¹ * ·) (fun a ha => htor δ a hδ ha)
      (fun a ha => htor _ a (hinv δ hδ) ha) (fun a _ => inv_mul_cancel_left δ a)
      (fun a _ => mul_inv_cancel_left δ a) (fun a _ => rfl)
  have hqΔ : ∀ δ ∈ W.DelF, W.γA δ (qA W) = qA W := by
    intro δ hδ
    unfold qA lA
    rw [map_add (f := _), hπ δ hδ, map_natCast]
  unfold Pp at hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨_, hxD⟩ : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hx.1
    have hN : qA W ^ k • W.φD T x ∈ W.N T := hq x hx
    rw [pow_one, smul_smul, mul_comm (qA W ^ k) a, ← smul_smul]
    show a • qA W ^ k • W.φD T x ∈ W.N T ∧
      ∀ δ ∈ W.DelF, W.γD T δ (a • qA W ^ k • W.φD T x) = a • qA W ^ k • W.φD T x
    refine ⟨(W.N T).smul_mem a hN, fun δ hδ => ?_⟩
    rw [hsl, hsl, ← W.φγ_comm, hxD δ hδ, ha δ hδ, map_pow, hqΔ δ hδ]
  | zero => rw [smul_zero]; exact (W.NΔ T).zero_mem
  | add u w _ _ hu hw => rw [smul_add]; exact (W.NΔ T).add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact (W.NΔ T).neg_mem hu

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYB

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLenLeOneOfNoThick
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem ro_le_arc_len : ∀ {n : ℕ} (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n),
    Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c ≤ A.len c := by
  intro n A c
  unfold Formalism.MainNotions.LocalTheoryWindows.ro Formalism.MainNotions.LocalTheoryWindows.thickLv
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem arc_len_le_one_of_no_thick : ∀ {n : ℕ} [NeZero n] (b w S η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ)
    (h : ¬ ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) (c : ZMod n),
    (arcOf b w S η up size).len c ≤ 1 := by
  intro n _ b w S η up size h c
  unfold arcOf
  dsimp only
  refine Nat.sInf_le ?_
  rw [Set.mem_ofPred_eq]
  exact ⟨le_rfl, fun ht => h ⟨_, ht⟩⟩

end Formalism.MainNotions.N.Ln17
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsAdicCompleteOfIdealPowLe
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem isAdicComplete_of_ideal_pow_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Ideal R) [hJ : IsAdicComplete J M] (e : ℕ) (he : 1 ≤ e) (hJI : J ≤ I) (hIJ : I ^ e ≤ J) :
    IsAdicComplete I M := by
  have mono : ∀ {A B : Ideal R}, A ≤ B → ∀ n : ℕ, A ^ n ≤ B ^ n := by
    intro A B h n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact Ideal.mul_mono ih h
  have hIJn : ∀ n : ℕ, I ^ (e * n) ≤ J ^ n := fun n => by
    rw [pow_mul]
    exact mono hIJ n
  have hJIn : ∀ n : ℕ, J ^ n ≤ I ^ n := fun n => mono hJI n
  have hle : ∀ n : ℕ, n ≤ e * n := fun n => by nlinarith
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    exact hJ.haus' x fun n => (hx (e * n)).mono (Submodule.smul_mono_left (hIJn n))
  · intro f hf
    obtain ⟨L, hL⟩ := hJ.prec' (fun k => f (e * k)) (fun {m n} hmn =>
      (hf (Nat.mul_le_mul le_rfl hmn)).mono (Submodule.smul_mono_left (hIJn m)))
    refine ⟨L, fun n => ?_⟩
    exact (hf (hle n)).trans ((hL n).mono (Submodule.smul_mono_left (hJIn n)))

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem isAdicComplete_integers_local : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l),
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  intro l _ LL
  have hc : IsAdicComplete (Ideal.span {((l : ℕ) : ↥(OL LL))}) ↥(OL LL) :=
    Formalism.MainNotions.LiftingTheory.phib_OL_complete LL

  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h
    simp only [map_natCast, ZeroMemClass.coe_zero] at h'
    have hp : (l : ℕ) ≠ 0 := (Fact.out : l.Prime).ne_zero
    exact hp (by exact_mod_cast h')
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hmax : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan : Ideal.span {((l : ℕ) : ↥(OL LL))} = IsLocalRing.maximalIdeal ↥(OL LL) ^ k := by
    rw [hmax, Ideal.span_singleton_pow, hk, Ideal.span_singleton_mul_left_unit u.isUnit]

  have hk1 : 1 ≤ k := by
    by_contra hlt
    have hk0 : k = 0 := by omega
    have htop : Ideal.span {((l : ℕ) : ↥(OL LL))} = ⊤ := by
      rw [hspan, hk0, pow_zero, Ideal.one_eq_top]
    have h10 : (1 : ↥(OL LL)) = 0 := by
      apply hc.haus' 1
      intro m
      rw [SModEq.sub_mem, htop, Ideal.top_pow, Submodule.top_smul]
      exact Submodule.mem_top
    exact one_ne_zero h10
  refine isAdicComplete_of_ideal_pow_le (IsLocalRing.maximalIdeal ↥(OL LL))
    (Ideal.span {((l : ℕ) : ↥(OL LL))}) k hk1 ?_ ?_
  · rw [hspan]
    calc IsLocalRing.maximalIdeal ↥(OL LL) ^ k ≤ IsLocalRing.maximalIdeal ↥(OL LL) ^ 1 :=
          Ideal.pow_le_pow_right hk1
      _ = IsLocalRing.maximalIdeal ↥(OL LL) := pow_one _
  · rw [hspan]

end Formalism.MainNotions.N.Ln17
end
end
