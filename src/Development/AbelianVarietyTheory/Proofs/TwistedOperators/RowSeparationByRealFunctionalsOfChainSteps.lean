module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LevelGroupLifts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSeparationByRealFunctionalsOfChainSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSeparationByRealFunctionalsOfChainSteps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows

namespace WeakSepPf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)


variable (G) in
theorem nonempty_coreVol : Nonempty (CoreVol G) := ⟨fun i => (GlobalTheory.Unf.Inhab.nonempty_vol (G.V (.core i))).some⟩

theorem rapidDec_of_rapidRow {M : Vol G} {u : GA D (Yc D 0) → ℂ} (h : RapidRow W M u) : RapidDec (Yc D 0) u :=
  h (fun _ => 0) (fun _ => default) 0 (Nat.zero_le _)

theorem rapidDec_of_reach {v : CoreVol G} {F : Fn G (.core 0)} (h : F ∈ Reach W v) : RapidDec (G.V (.core 0)) F := by
  obtain ⟨Ψ, hΨ, rfl, -⟩ := h
  exact hΨ.1 0 (Nat.zero_le _)

theorem integrableOn_corePeriod_rapidlyDecreasing {M : Vol G} (hM : M.IsRow) {F : Fn G (.core 0)}
    (hF : RapidDec (G.V (.core 0)) F) {u : GA D (Yc D 0) → ℂ} (hu : RapidDec (Yc D 0) u) :
    IntegrableOn (fun h => F (stabilizerEmbedding G.sp.dec0 h) * u h) (M.fd (.grid 0 0)) (M.ν (.grid 0 0)) := by
  obtain ⟨h1, h2⟩ := (hM.row 0 (Nat.zero_le _)).haar_fund
  obtain ⟨C, hC⟩ := hF.2.2 0
  exact RapidDec.integrableOn_mul_of_le (V := Yc D 0) (f := fun h => F (stabilizerEmbedding G.sp.dec0 h)) hu h1 h2
    ((hF.2.1.comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding G.sp.dec0)).aestronglyMeasurable) (C := C) (A := 0)
    fun g => by simpa using hC _

theorem exists_reach_of_span {M : Vol G} (hM : M.IsRow) {v : CoreVol G}
    {u : GA D (Yc D 0) → ℂ} (hu : RapidDec (Yc D 0) u) {F : Fn G (.core 0)} (hF : F ∈ Submodule.span ℂ (Reach W v))
    (h0 : per0 G M F u ≠ 0) : ∃ F' ∈ Reach W v, per0 G M F' u ≠ 0 := by
  by_contra hn
  push_neg at hn
  have key : IntegrableOn (fun h => F (stabilizerEmbedding G.sp.dec0 h) * u h) (M.fd (.grid 0 0)) (M.ν (.grid 0 0)) ∧
      per0 G M F u = 0 := by
    clear h0
    induction hF using Submodule.span_induction with
    | mem x hx => exact ⟨integrableOn_corePeriod_rapidlyDecreasing hM (rapidDec_of_reach W hx) hu, hn x hx⟩
    | zero => exact ⟨by simp only [Pi.zero_apply, zero_mul]; exact integrableOn_zero, by simp [per0]⟩
    | add x y _ _ hx hy =>
      have e : (fun h => (x + y) (stabilizerEmbedding G.sp.dec0 h) * u h) =
          fun h => x (stabilizerEmbedding G.sp.dec0 h) * u h + y (stabilizerEmbedding G.sp.dec0 h) * u h := by
        funext h; simp [add_mul]
      refine ⟨e ▸ hx.1.add hy.1, ?_⟩
      have a := hx.2
      have b := hy.2
      unfold per0 at a b ⊢
      erw [e, integral_add hx.1 hy.1, a, b, add_zero]
    | smul c x _ hx =>
      have e : (fun h => (c • x) (stabilizerEmbedding G.sp.dec0 h) * u h) = fun h => c * (x (stabilizerEmbedding G.sp.dec0 h) * u h) := by
        funext h; simp [mul_assoc]
      refine ⟨e ▸ hx.1.const_mul c, ?_⟩
      have a := hx.2
      unfold per0 at a ⊢
      erw [e, integral_const_mul, a, mul_zero]
  exact h0 key.2

end WeakSepPf

theorem weakSep_of_steps : SizeGap → CoreModels → RowRapid → PeriodNe → CoreOnto → Ascent → WeakSep := by
  intro hs h1 h2 h3 h4 h5 ε CF hCF
  obtain ⟨x, hx⟩ := h3 ε CF hCF
  obtain ⟨x', hx'⟩ := hs ε
  refine ⟨max x x', fun D large₂ e a b T L μ0 hL G W M hM M₀ hc0 t ht t0 w w0 => ?_⟩
  have q := offQ_of_sizeRows b
  have s := hx' D large₂ e (le_trans (le_max_right _ _) a) b
  obtain ⟨MP, hMP⟩ := h1 D q T L μ0 hL _ G W M hM 0 (Nat.zero_le _)
  obtain ⟨y, hy, v, hv, hp⟩ := hx D large₂ e (le_trans (le_max_left _ _) a) b T L μ0 hL G W M hM M₀ MP t ht t0 w w0
  obtain ⟨vol⟩ := WeakSepPf.nonempty_coreVol G
  have hr := (h2 D q s T L μ0 hL _ rfl G W M hM M₀ hc0 t ht w).1
  obtain ⟨F, ⟨Ψ, hΨ, rfl, c, hcol, ξ, hξ⟩, hF⟩ := WeakSepPf.exists_reach_of_span W hM (WeakSepPf.rapidDec_of_rapidRow W hr)
    (h4 D q s T L μ0 hL _ rfl G W M hM vol MP hMP y hy v hv) hp
  obtain ⟨ρ, Φ, hB⟩ := h5 D q T L μ0 hL _ G W M hM vol Ψ hΨ _ hr hF
  exact ⟨ρ, ξ, c, hcol, Φ, by rw [fPsiPhi, ← hξ]; exact hB⟩

end GlobalTheory.SepRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSeparationByRealFunctionalsOfChainStepsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowSeparation_by_realFunctionals_of_chain_steps : SizeGap → CoreModels → RowRapid → PeriodNe → CoreOnto → Ascent → WeakSep := by
  first | exact @GlobalTheory.SepRows.weakSep_of_steps | exact GlobalTheory.SepRows.weakSep_of_steps | (intros; apply GlobalTheory.SepRows.weakSep_of_steps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodsOnLineOfInvLine
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def InvLine (ch : Choice R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (S : Sizes) (P : ι → Entries S), (∀ τ, (P τ).Good) ∧
    ∃ e : PolCol ch.G × PolRow ch.G → OM P, ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
        ∃ l ∈ invFun (omRep P), ∀ Q, defPer t ch.S.toGridChoice M Q d (colFn ch a) (formTop ch t y) = l (e Q)

theorem periodsOnLine_of_invLine (hL : OneLine) (ch : Choice R) (h : InvLine ch) : PeriodsOnLine ch := by
  obtain ⟨ι, _, _, S, P, hP, e, he⟩ := h
  have : Module.Free ℂ (invFun (omRep P)) := Module.Free.of_divisionRing ℂ _
  obtain ⟨L0, -, hL0⟩ := finrank_eq_one_iff'.1 (hL ι S P hP)
  refine ⟨fun Q => L0.1 (e Q), fun t a hS β hβ M hM τ hτ d hd y => ?_⟩
  obtain ⟨l, hl, hle⟩ := he t a hS β hβ M hM τ hτ d hd y
  obtain ⟨c, hc⟩ := hL0 ⟨l, hl⟩
  refine ⟨c, fun Q => ?_⟩
  have hc' : c • L0.1 = l := congrArg Subtype.val hc
  rw [hle Q, ← hc']
  rfl

end GlobalTheory.RowReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierShiftedLatticeAwayFromPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierShiftedLatticeAwayFromPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrOffShift

theorem algebraMap_mem_conjI {D : D7} (I : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.F)
    (h : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ I) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ conjI I := by
  apply Ideal.subset_span
  refine ⟨_, h, ?_⟩
  have h2 := GlobalTheory.Ker.MovLev.bar_algebraMap (D := D) s
  have h3 := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) h2
  simp only [Lev.bar] at h3
  have h4 := IsCMField.coe_ringOfIntegersComplexConj D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s)
  exact h3.symm.trans h4

theorem shift_mult : ∀ (D : D7) (r : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (L : Lt D.host.E r) (w : HeightOneSpectrum (𝓞 D.host.F)), (∀ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → ∀ u ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) L, ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • u ∈ L := by
  intro D r Pg Q L w hne u hu
  classical
  have hex : ∀ PP ∈ Pg ∪ Q, ∃ s : 𝓞 D.host.F,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ PP.asIdeal ∧ s ∉ w.asIdeal := by
    intro PP hPP
    by_contra hcon
    push_neg at hcon
    apply hne PP hPP
    have hle : (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal ≤ w.asIdeal := by
      intro s hs
      exact hcon s hs
    exact HeightOneSpectrum.ext
      ((HeightOneSpectrum.isMaximal _).eq_of_le w.isPrime.ne_top hle)
  choose! tf htf1 htf2 using hex
  refine ⟨∏ PP ∈ Pg ∪ Q, tf PP, ?_, ?_⟩
  · have : ∏ PP ∈ Pg ∪ Q, tf PP ∈ w.asIdeal.primeCompl :=
      Submonoid.prod_mem _ (fun c hc => htf2 c hc)
    exact this
  · have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP)
        ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
      rw [map_prod]
      exact Ideal.prod_mem_prod (fun PP hPP => algebraMap_mem_conjI (D := D) _ _ (htf1 PP hPP))
    have h1 := hu _ (algebraMap_mem_conjI (D := D) _ _ hmem)
    exact Submodule.smul_le_right h1

end GlobalTheory.TrOffShift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierShiftedLatticeAwayFromPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplier_shifted_lattice_away_from_places : ∀ (D : D7) (r : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (L : Lt D.host.E r) (w : HeightOneSpectrum (𝓞 D.host.F)), (∀ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → ∀ u ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) L, ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • u ∈ L := by
  first | exact @GlobalTheory.TrOffShift.shift_mult | exact GlobalTheory.TrOffShift.shift_mult | (intros; apply GlobalTheory.TrOffShift.shift_mult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPartNeBotPositiveDimension
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
noncomputable section

namespace GlobalTheory.RowsPartNe


open GlobalTheory.Mem.RowSides in
theorem jX_injective_of_models {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (hM : R.IsModels) (t : T) :
    Function.Injective (R.jX t) := by
  intro f g hfg
  refine semi_injective_of_basis (A.MtildeCSD t).basis (R.B.R t).pres.extL
    (classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R t).pres).2.1.1 ?_
  exact (hM.jX t f).symm.trans ((congrArg (R.HX t).e hfg).trans (hM.jX t g))

theorem exists_rowPart_ne_bot_positiveDimension : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → ∃ p, R.EEp3 p ≠ ⊥ := by
  intro hH hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hIn hGE hPos
  by_contra hne
  push_neg at hne
  have hcar := GlobalTheory.Hk3.carries_of_rows_top hP hH R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hP D) hOk hC hEx hIn hGE hPos
  have hc0 : ∀ c, R.EEc c = ⊥ := by
    intro c
    by_contra h
    obtain ⟨p, hp⟩ := hcar c h
    have hle : R.EEc c ≤ R.EEp3 p := by
      unfold RealDat3.EEp3
      exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.EEc c) c hp le_rfl
    rw [hne p, le_bot_iff] at hle
    exact h hle
  obtain ⟨hCore, hSF, hEq, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  obtain ⟨h, -, -, htop, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 hCore
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP R.toRealDat) R.SF hSF
  have hbot : (⊤ : Submodule ℂ R.HE.H) = ⊥ := by
    rw [← htop]
    simp only [← hEq, hc0, iSup_bot]
  have hzero : ∀ x : R.HE.H, x = 0 := fun x => by
    have hx : x ∈ (⊤ : Submodule ℂ R.HE.H) := Submodule.mem_top
    rw [hbot] at hx
    exact (Submodule.mem_bot ℂ).1 hx
  have hM := (RealDat3.characterisation_of_weak hC hEx).models
  have hL : R.toRealDat.LPos F.lv2 := fun b => by
    cases b
    · exact hPos false
    · exact hPos true
  refine (GlobalTheory.QPosCompare.lPos_iff_ne_bot R.toRealDat F.lv2).1 hL false ?_
  have hZ : (R.toRealDat.toCx F.lv2).Z A3.A.μ0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have hy0 : y = 0 := hzero (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y)
    rw [hy0, map_zero] at hy
    have h1 : R.jX A3.A.μ0 x = 0 := hy.symm
    rw [Submodule.mem_bot]
    exact jX_injective_of_models hM A3.A.μ0 (h1.trans (map_zero _).symm)
  rw [hZ]
  exact BlockDat.good_part_coordinates_bot _ _

end GlobalTheory.RowsPartNe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteAdeleOfSplitPlacesIdempotentSum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteAdeleOfSplitPlacesIdempotentSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumFinAdele

theorem exists_finAdele_of_idemSum : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∃ σ : Af D.host.F, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) = e + cA D e ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ P, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → evalV D.host.F w σ = 0) ∧ ∀ PP ∈ P, evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) σ = 1 := by
  intro D P e he
  have he' := he
  obtain ⟨⟨es, hes, rfl⟩, hz⟩ := he
  have hex : ∀ PP ∈ P, ∃ α : Af D.host.F,
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = es PP + cA D (es PP) ∧
      evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) α = 1 ∧
      ∀ v', v' ≠ HeightOneSpectrum.under (𝓞 D.host.F) PP → evalV D.host.F v' α = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, v, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hv := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP v ε (hes PP hPP) hε a3
    obtain ⟨α, rfl, h1, h2⟩ := hε
    exact ⟨α, a3.symm, hv ▸ h1, hv ▸ h2⟩
  choose! α hα using hex
  have hsum : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (∑ PP ∈ P, α PP)) =
      ∑ PP ∈ P, es PP + cA D (∑ PP ∈ P, es PP) := by
    have hp : pairA D.host.F 0 (∑ PP ∈ P, α PP) = ∑ PP ∈ P, pairA D.host.F 0 (α PP) := by
      have hadd : ∀ a b : Af D.host.F, pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b :=
        fun a b => Prod.ext (add_zero 0).symm rfl
      exact map_sum (AddMonoidHom.mk' (pairA D.host.F 0) hadd) α P
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hp, map_sum, map_sum (cA D), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun PP hPP => (hα PP hPP).1
  refine ⟨∑ PP ∈ P, α PP, hsum, ?_, ?_⟩
  · intro w hw
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun PP hPP => (hα PP hPP).2.2 w (hw PP hPP).symm
  · intro PP hPP
    have h1 := GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one P _ he' PP hPP
    rw [← hsum] at h1
    have h2 : (evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) (∑ PP ∈ P, α PP)) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : Fv D.host.F _ ⊗[D.host.F] D.host.E) := h1
    haveI : Module.Free D.host.F (Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) :=
      Module.Free.of_divisionRing _ _
    haveI : Module.Flat D.host.F (Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) := Module.Flat.of_free
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
      (A := Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    apply hinj
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeLeft_apply, h2]
    rfl

end GlobalTheory.IdemSumFinAdele

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteAdeleOfSplitPlacesIdempotentSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdele_of_splitPlaces_idempotentSum : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∃ σ : Af D.host.F, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) = e + cA D e ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ P, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → evalV D.host.F w σ = 0) ∧ ∀ PP ∈ P, evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) σ = 1 := by
  first | exact @GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum | exact GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum | (intros; apply GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralUnitDeterminantAtIdempotentResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralUnitDeterminantAtIdempotentResidue
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabDet

theorem toEAf_detAt_mem {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β)
    (e : AE D) (he : e * e = e) :
    toEAf D ((GlobalTheory.VecInv.detAt e he V g : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨a, ha, -⟩ := GlobalTheory.VecInv.exists_det_int hg
  have hE : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he]))
  have hd := GlobalTheory.VecInv.isDetAt_detAt e he V g
  unfold IsDetAt at hd
  rw [hd, map_add (f := _), map_mul, map_sub, map_one, ← ha]
  exact add_mem (mul_mem hE a.2) (sub_mem (one_mem _) hE)

theorem toEAf_detAt {D : D7} (V : HSp D) (g : GA D V) (e : AE D) (he : e * e = e) :
    toEAf D ((GlobalTheory.VecInv.detAt e he V g : (AE D)ˣ) : AE D) =
      toEAf D e * toEAf D (Formalism.L2.Theta.mt V g).det + (1 - toEAf D e) := by
  have hd := GlobalTheory.VecInv.isDetAt_detAt e he V g
  unfold IsDetAt at hd
  rw [hd, map_add (f := _), map_mul, map_sub, map_one]

theorem map_eq_of_idem {R K : Type} [Ring R] [Ring K] (S : Subring R) (f : S →+* K) (x ε a : S) (h1 : f ε = 1)
    (hx : (x : R) = (ε : R) * (a : R) + (1 - (ε : R))) : f a = f x := by
  have hx' : x = ε * a + (1 - ε) := Subtype.ext (by push_cast; exact hx)
  rw [hx', map_add (f := _), map_mul, map_sub, map_one, h1]
  simp

theorem toEAf_detAt_inv_mem {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β)
    (e : AE D) (he : e * e = e) :
    toEAf D (((GlobalTheory.VecInv.detAt e he V g)⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [← map_inv (GlobalTheory.VecInv.detAt e he V) g]
  exact toEAf_detAt_mem (by rw [map_inv]; exact inv_mem hg) e he

theorem res_detAt {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β)
    (e : AE D) (he : e * e = e) (PP : Pl D.host.E) (hP : Formalism.L2.NTheta.IsIdemAt e PP) :
    ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) =
      resS D.host.F PP ⟨toEAf D ((GlobalTheory.VecInv.detAt e he V g : (AE D)ˣ) : AE D), toEAf_detAt_mem hg e he⟩ := by
  obtain ⟨a, ha, hred⟩ := GlobalTheory.VecInv.exists_det_int hg
  obtain ⟨hE, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP hP
  rw [hred PP]
  refine map_eq_of_idem _ (resS D.host.F PP) _ ⟨toEAf D e, hE⟩ a h1 ?_
  show toEAf D _ = toEAf D e * (a : Lev.EAf D) + (1 - toEAf D e)
  rw [toEAf_detAt V g e he, ha]

theorem exists_detAt_int : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V), finE V g ∈ St β → ∀ e : AE D, e * e = e → ∃ x : (AE D)ˣ, IsDetAt e V g x ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP : Pl D.host.E, Formalism.L2.NTheta.IsIdemAt e PP → ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ := by
  intro D V β g hg e he
  exact ⟨GlobalTheory.VecInv.detAt e he V g, GlobalTheory.VecInv.isDetAt_detAt e he V g,
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (toEAf_detAt_mem hg e he),
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (toEAf_detAt_inv_mem hg e he),
    toEAf_detAt_mem hg e he, fun PP hP => res_detAt hg e he PP hP⟩

end GlobalTheory.StabDet

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralUnitDeterminantAtIdempotentResidueStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralUnit_determinantAtIdempotent_residue : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V), finE V g ∈ St β → ∀ e : AE D, e * e = e → ∃ x : (AE D)ˣ, IsDetAt e V g x ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP : Pl D.host.E, Formalism.L2.NTheta.IsIdemAt e PP → ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ := by
  first | exact @GlobalTheory.StabDet.exists_detAt_int | exact GlobalTheory.StabDet.exists_detAt_int | (intros; apply GlobalTheory.StabDet.exists_detAt_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperLeftBlockEqSubmatrixOfRankEq
noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoActRoad

section Lattice

variable {D : D7} {V : HSp D}

variable {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

theorem le_of_half {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} {Pg : Finset (Pl D.host.E)}
    (h : l.Mb = ∏ w ∈ Pg, w.asIdeal) {w : Pl D.host.E} (hw : w ∈ Pg) : l.Mb ≤ w.asIdeal :=
  h.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hw))

end Lattice

section Group

variable {D : D7} {V : HSp D} (β : GL (Fin V.rank) (EAf D))

variable {β} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

theorem liftsExist_of_half (hβ : IsSDFrame V β Λ 1) (l : Level H) (L : LevDat D.host.E ℂ V.rank) (hQ : L.Q = ∅)
    (h : l.Mb = ∏ w ∈ L.Pg, w.asIdeal) : LiftsExist V β L := by
  obtain ⟨c, hc⟩ := hβ
  refine GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP h1 PP' h' => ?_) (hQ ▸ Finset.disjoint_empty_right _)
  rcases h' with h' | h'
  · exact GlobalTheory.LevelAction.not_isConjPl l (le_of_half h h1) (le_of_half h h')
  · exact absurd (hQ ▸ h') (Finset.notMem_empty _)

end Group

section Record

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


open Classical in
theorem exists_half_prod {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (hM : l.M = D.host.g 0 * D.host.g 1) :
    (∀ Pg : Finset (Pl D.host.E), (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → l.Mb = ∏ w ∈ Pg, w.asIdeal) ∧
      ∃ Pg : Finset (Pl D.host.E), l.Mb = ∏ w ∈ Pg, w.asIdeal := by
  have hprod := l.prod
  rw [hM] at hprod
  have hs : Squarefree l.Mb := (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (l.Mb * _)).of_mul_left
  refine ⟨fun Pg h => GlobalTheory.CoverHalf.eq_prod_of_squarefree hs _ h,
    (Ideal.finite_factors hs.ne_zero).toFinset, GlobalTheory.CoverHalf.eq_prod_of_squarefree hs _ fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]

theorem mem_Pg_iff {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (w : Pl D.host.E) :
    w ∈ L.Pg ↔ (GlobalTheory.HalfOnRecord.designLevel L.C.P).Mb ≤ w.asIdeal := by
  rw [hL.Pg, GlobalTheory.HalfOnRecord.designLevel_Mb, GlobalTheory.CoverHalf.prod_map_le_iff]
  rfl

theorem designLevel_prod {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) :
    (GlobalTheory.HalfOnRecord.designLevel L.C.P).Mb = ∏ w ∈ L.Pg, w.asIdeal :=
  (exists_half_prod _ rfl).1 _ (mem_Pg_iff hL)

theorem levelLiftsExist_gridVertexSpaces {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) :
    LiftsExist (Wc D i) (L.βW i) (L.datWp i L.triv) :=
  liftsExist_of_half (hL.βW i) (GlobalTheory.HalfOnRecord.designLevel L.C.P) _ rfl (designLevel_prod hL)

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

end Record

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

open GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts (LevGrp IsGeoRep UnitConstEquivariant)
open GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv (Cusp IsGeo ReadTwist KeepsIntegral ConstEquiv GeoActAt)

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}

end Main

end GlobalTheory.GeoActRoad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridRouteKernelEqDetCharactersMulThetaKerne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridRouteKernelEqDetCharactersMulThetaKerne
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict.ExactBig

variable {D : D7}

theorem exists_change {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ₁ χ' : (AE D)ˣ →* Circle}
    {ω₁ : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (H₁ : IsWeilDatumO ψ S T χ₁ χ' ω₁)
    (hχ : IsHeckeChar D χ) (rχ : ResEta D χ S.rank) :
    ∃ ω, IsWeilDatumO ψ S T χ χ' ω ∧ ∀ u g y, IsDetRoot T g y → ω₁ (u, g) = (((χ₁ / χ) y : Circle) : ℂ) • ω (u, g) := by
  have r0 : ResEta D (χ * χ₁⁻¹) 0 :=
    Formalism.L2.Theta.resEta_parity (Formalism.L2.Theta.resEta_mul rχ (Formalism.L2.Theta.resEta_inv H₁.resS)) (by omega)
  have r1 : ResEta D 1 0 := ⟨r0.1, fun _ _ _ => by simp⟩
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  obtain ⟨ω, H, hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H₁.std S T χ₁ χ' (χ * χ₁⁻¹) 1 ω₁ H₁
    (GlobalTheory.WeilChange.hecke_mul hχ (GlobalTheory.WeilChange.hecke_inv H₁.hecS)) h1 r0 r1
  have e : χ₁ * (χ * χ₁⁻¹) = χ := by rw [mul_comm χ, mul_inv_cancel_left]
  rw [e, mul_one] at H
  refine ⟨ω, H, fun u g y hy => ?_⟩
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D S u
  have e1 : (χ₁ / χ) y * (((1 : (AE D)ˣ →* Circle) x)⁻¹ * (χ * χ₁⁻¹) y) = 1 := by
    rw [MonoidHom.one_apply, inv_one, one_mul, ← MonoidHom.mul_apply, ← mul_assoc, div_mul_cancel, mul_inv_cancel,
      MonoidHom.one_apply]
  rw [hv u g x y hx hy, smul_smul, ← Circle.coe_mul, e1, Circle.coe_one, one_smul]

theorem seesaw_exact {ψ : AddChar (AF D.host.F) ℂ} {S A B : HSp D} {χ χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle}
    {ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)} {ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)}
    {ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ)}
    (H₁ : IsWeilDatumO ψ S A χ₁ χ₁' ω₁) (H₂ : IsWeilDatumO ψ S B χ₂ χ₂' ω₂)
    (H : IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ (χ₁' * χ₂') ω)
    {φ : WO S A → ℂ} {φ' : WO S B → ℂ} (hφ : IsThetaFunO ψ S A φ) (hφ' : IsThetaFunO ψ S B φ')
    (u : GA D S) (g : GA D A) (g₁ : GA D B) {x y : (AE D)ˣ} (hx : IsDetRoot A g x) (hy : IsDetRoot B g₁ y) :
    thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ' = (((χ₁ / χ) x : Circle) : ℂ) * (((χ₂ / χ) y : Circle) : ℂ) *
      thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') := by
  obtain ⟨o₁, K₁, e₁⟩ := exists_change H₁ H.hecS H.resS
  obtain ⟨o₂, K₂, e₂⟩ := exists_change H₂ H.hecS H.resS
  have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ H.std _ A B (GlobalTheory.BiTransfer.sumDec A B) S).om_box χ χ₁' χ₂' ω o₁
    o₂ H K₁ K₂ u g g₁ φ φ' hφ hφ'
  simp only [thetaKO]
  rw [← GlobalTheory.SeesawSumTarget.emb_sumDec, ← GlobalTheory.SeesawSumTarget.boxT_sumDec, key, GlobalTheory.MixModel.OrthDec.boxT_zero,
    e₁ u g x hx, e₂ u g₁ y hy]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem adjoint_exact {ψ : AddChar (AF D.host.F) ℂ} {S B : HSp D} {χB χS : (AE D)ˣ →* Circle}
    {ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)} (H : IsWeilDatumO ψ B S χB χS ω₂) :
    ∃ ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ),
      IsWeilDatumO ψ (negSp S) B χS⁻¹ χB⁻¹ ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  have hψ := H.std
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂),
    GlobalTheory.ConjWeil.weil_conjSource D ψ S B _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ B S _ _ ω₂ H),
    fun f hf => ?_⟩
  have e : (fun y : WO (negSp S) B => f (adjM S B y)) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.AdjSwap.dagger_eq_adjM]
  rw [e]
  have h1 : IsThetaFunO ψ S B (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) :=
    ((GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ B S).2.2.1 f).2 hf
  refine ⟨((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S B).1 _).2.2 h1, fun g₁ u => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂) (negGA S u, g₁) _ 0 = ω₂ (g₁, u) f 0
  rw [GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.AdjSwap.dagger_eq_adjM, adjM_zero]

theorem attChr_eq {C : Type} [CommGroup C] (χ η : C) (n : ℕ) :
    Formalism.IndefR.Lift.attChr χ η n = χ / η ^ (n % 2) := by
  unfold Formalism.IndefR.Lift.attChr
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]; simp
  · rw [if_pos h, Nat.odd_iff.1 h]; simp [div_eq_mul_inv]

theorem kerBig_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerBig W Θ g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ) := by
  intro D T L sc G μ₀ hL W t i j ωA hA B ρ Θ Θ' hΘ g g₁ u
  have hd := isThetaFunO_of_isMatched hL W B ρ t i j Θ Θ' hΘ
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, hω₂, hadj⟩ := adjoint_exact h2
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  obtain ⟨s, hs⟩ := odd_sLen D
  obtain ⟨t', ht⟩ := D.R.t_odd
  have pW : (G.V (.grid (i + 1) (j + 1))).rank % 2 = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
    rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
    simp only [rankV, add_mul, one_mul]
    omega
  have pV : (G.V (.grid i (j + 1))).rank % 2 = (G.V (.grid (i + 1) j)).rank % 2 := by
    rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
    simp only [rankV, add_mul, one_mul]
    omega
  have cT : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j =
      G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹ := by
    simp only [GridData.chrT, GridData.chrS, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha]
    rw [pV, mul_div_mul_right_eq_div, ← div_eq_mul_inv, div_div_div_cancel_right]
  have cV : G.chrS (.chi i (j + 1)) / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = (L.eta ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j))⁻¹ := by
    simp only [GridData.chrS, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta]
    rw [pW, two_mul, pow_add, div_div, mul_left_comm, div_mul_cancel_left]
  have cV₁ : (G.chrT (.mu t (i + 1) j))⁻¹ / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j =
      (L.mu t (j + 1) * G.ch.chi (D.R.m - i))⁻¹ := by
    simp only [GridData.chrT, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta]
    rw [pW, inv_div, div_div, ← mul_assoc, div_mul_cancel_right]
  rw [cT] at hA
  let S := G.V (.grid (↑i + 1) (↑j + 1))
  let A := G.V (.grid (↑i) (↑j + 1))
  let Bs := G.V (.grid (↑i + 1) ↑j)
  have hA' : IsWeilDatumO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs) _ _ (ωA.toSgn true) := hA
  have e : ∀ d ∈ Θ.support, W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ * ωA (u, GlobalTheory.SquareComm.blk A Bs (g, g₁))
        (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) 0 := fun d hdm => by
    have k := seesaw_exact h1 hω₂ hA' (hd d hdm).1 (hadj _ (hd d hdm).2).1 (negGA S u) g g₁
      (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose_spec (GlobalTheory.RecDict.exists_isDetRoot D _ g₁).choose_spec
    rw [(hadj _ (hd d hdm).2).2, cV, cV₁] at k
    exact k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [thetaKO, GlobalTheory.SquareDict.datumA, kerBig, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hdm => ?_
  rw [e d hdm]
  ring

end GlobalTheory.SquareDict.ExactBig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridRouteKernelEqDetCharactersMulThetaKerneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGridRouteKernel_eq_detCharacters_mul_thetaKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerBig W Θ g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ) := by
  first | exact @GlobalTheory.SquareDict.ExactBig.kerBig_eq | exact GlobalTheory.SquareDict.ExactBig.kerBig_eq | (intros; apply GlobalTheory.SquareDict.ExactBig.kerBig_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedMatrixGroupOfLocalMultiplier
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedMatrixGroupOfLocalMultiplier
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatPoint

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem ev_apply (v : HeightOneSpectrum (𝓞 F)) (x : Af F) : evalV F v x = x v := rfl

theorem val_coe_one (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    Valued.v (algebraMap F (Af F) (t : F) v) = 1 := by
  rw [GlobalTheory.Ker.MovLev.val_coe]; exact v.intValuation_eq_one_iff.2 ht

theorem coe_ne_zero (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    algebraMap F (Af F) (t : F) v ≠ 0 := fun h0 => by
  have := val_coe_one t v ht
  rw [h0, map_zero] at this
  exact zero_ne_one this

theorem div_int {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F)
    (t : 𝓞 F) (ht : t ∉ v.asIdeal) : x * (algebraMap F (Af F) (t : F) v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [map_mul, map_inv₀, val_coe_one t v ht, inv_one, mul_one]
  exact hx

def mulG (I : Ideal (𝓞 F)) : AddSubgroup (Af F) :=
  AddSubgroup.closure {x | ∃ t ∈ I, ∃ β ∈ intAf F, x = algebraMap F (Af F) (t : F) * β}

theorem mem_mulG (I : Ideal (𝓞 F)) {γ : Af F} (hγ : γ ∈ intAf F)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), evalV F w γ = 0 ∨ ∃ t ∈ I, t ∉ w.asIdeal) : γ ∈ mulG I := by
  by_cases h0 : γ = 0
  · rw [h0]; exact zero_mem _
  obtain ⟨w₀, hw₀⟩ : ∃ w, γ w ≠ 0 := by
    by_contra H
    push_neg at H
    exact h0 (FiniteAdeleRing.ext F fun v => H v)
  obtain ⟨t₁, ht₁I, ht₁w⟩ := (h w₀).resolve_left hw₀
  have ht₁0 : t₁ ≠ 0 := fun e => ht₁w (e ▸ w₀.asIdeal.zero_mem)
  have hspan : Ideal.span {t₁} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ht₁0
  set Z := (Ideal.finite_factors hspan).toFinset with hZdef
  have hZ : ∀ v, v ∈ Z ↔ t₁ ∈ v.asIdeal := fun v => by
    rw [hZdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have h' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t ∈ I, γ v = 0 ∨ t ∉ v.asIdeal := fun v =>
    (h v).elim (fun e => ⟨0, I.zero_mem, Or.inl e⟩) fun ⟨t, ht, hv⟩ => ⟨t, ht, Or.inr hv⟩
  choose τ hτI hτ using h'
  obtain ⟨c, hc, hc'⟩ : ∃ c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F,
      (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ∀ v, algebraMap F (Af F) (τ v : F) v * c v = γ v := by
    refine ⟨fun v => if γ v = 0 then 0 else γ v * (algebraMap F (Af F) (τ v : F) v)⁻¹, fun v => ?_, fun v => ?_⟩
    · dsimp only
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ ((hτ v).resolve_left hv)
    · dsimp only
      split_ifs with hv
      · rw [mul_zero, hv]
      · rw [mul_comm, mul_assoc, inv_mul_cancel₀ (coe_ne_zero _ _ ((hτ v).resolve_left hv)), mul_one]
  have hb₁ : ∀ v : HeightOneSpectrum (𝓞 F),
      (if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹) ∈ v.adicCompletionIntegers F :=
    fun v => by
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ hv
  obtain ⟨β₁, hβ₁, eβ₁⟩ : ∃ β₁ : Af F, β₁ ∈ intAf F ∧
      ∀ v, β₁ v = if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹ :=
    ⟨GlobalTheory.Ker.MovLev.ofInt _ hb₁, fun v => hb₁ v, fun _ => rfl⟩
  have hbw : ∀ w v : HeightOneSpectrum (𝓞 F), (if v = w then c v else 0) ∈ v.adicCompletionIntegers F :=
    fun w v => by
      split_ifs
      exacts [hc v, zero_mem _]
  have hβex : ∀ w : HeightOneSpectrum (𝓞 F), ∃ β : Af F, β ∈ intAf F ∧ ∀ v, β v = if v = w then c v else 0 :=
    fun w => ⟨GlobalTheory.Ker.MovLev.ofInt _ (hbw w), fun v => hbw w v, fun _ => rfl⟩
  choose β hβ eβ using hβex
  have e : γ = algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w := by
    refine FiniteAdeleRing.ext F fun v => ?_
    change evalV F v γ = evalV F v (algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, map_mul]
    simp only [map_mul, ev_apply, eβ₁, eβ]
    by_cases hv : t₁ ∈ v.asIdeal
    · have hvZ : v ∈ Z := (hZ v).2 hv
      rw [Finset.sum_eq_single v (fun w _ hwv => by rw [if_neg (Ne.symm hwv), mul_zero])
        (fun hn => absurd hvZ hn), if_pos hv, if_pos rfl, mul_zero, zero_add, hc']
    · rw [Finset.sum_eq_zero (fun w hw => by
        have hne : v ≠ w := fun e => hv (e ▸ (hZ w).1 hw)
        rw [if_neg hne, mul_zero]), if_neg hv, add_zero, mul_comm, mul_assoc,
        inv_mul_cancel₀ (coe_ne_zero _ _ hv), mul_one]
  rw [e]
  refine add_mem (AddSubgroup.subset_closure ⟨t₁, ht₁I, β₁, hβ₁, rfl⟩) (sum_mem fun w _ => ?_)
  exact AddSubgroup.subset_closure ⟨τ w, hτI w, β w, hβ w, rfl⟩

theorem pairA_mul_tmul {E : Type} [Field E] [Algebra F E] (s : F) (β : Af F) (x : E) :
    pairA F 0 (algebraMap F (Af F) s * β) ⊗ₜ[F] x = pairA F 0 β ⊗ₜ[F] (algebraMap F E s * x) := by
  have h : pairA F 0 (algebraMap F (Af F) s * β) = s • pairA F 0 β :=
    Prod.ext (by change (0 : Ainf F) = s • 0; rw [smul_zero]) (by change _ = s • β; rw [Algebra.smul_def]; rfl)
  rw [h, TensorProduct.smul_tmul, Algebra.smul_def]

end Gen

theorem mem_hatA_of_div : ∀ (D : D7) (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)), (∀ (c : 𝓞 D.host.F), ∀ y ∈ A, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ A) → ∀ γ ∈ intAf D.host.F, ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (∀ w : HeightOneSpectrum (𝓞 D.host.F), evalV D.host.F w γ = 0 ∨ ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ (algebraMap D.host.F D.host.E (t : D.host.F)) • y ∈ A) → (Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a : WO S T) ∈ hatA S T A := by
  intro D S T A hA γ hγ y hy
  let I : Ideal (𝓞 D.host.F) :=
    { carrier := {t | algebraMap D.host.F D.host.E (t : D.host.F) • y ∈ A}
      add_mem' := fun {a b} ha hb => by
        change algebraMap D.host.F D.host.E ((a : D.host.F) + (b : D.host.F)) • y ∈ A
        rw [map_add (f := _), add_smul]
        exact add_mem ha hb
      zero_mem' := by
        change algebraMap D.host.F D.host.E (0 : D.host.F) • y ∈ A
        rw [map_zero, zero_smul]
        exact zero_mem _
      smul_mem' := fun c {x} hx => by
        change algebraMap D.host.F D.host.E ((c : D.host.F) * (x : D.host.F)) • y ∈ A
        rw [map_mul, mul_smul]
        exact hA c _ hx }
  have hmem := mem_mulG I hγ fun w => (hy w).imp id fun ⟨t, ht, hA'⟩ => ⟨t, hA', ht⟩
  let f : Af D.host.F →+ WO S T :=
    { toFun := fun α => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a
      map_zero' := Matrix.ext fun a k => by
        change pairA D.host.F 0 0 ⊗ₜ[D.host.F] y k a = 0
        exact TensorProduct.zero_tmul _ _
      map_add' := fun α β => Matrix.ext fun a k => by
        change pairA D.host.F 0 (α + β) ⊗ₜ[D.host.F] y k a =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a + pairA D.host.F 0 β ⊗ₜ[D.host.F] y k a
        rw [← TensorProduct.add_tmul]
        congr 1
        exact Prod.ext (add_zero 0).symm rfl }
  have hle : mulG I ≤ (hatA S T A).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨t, ht, β, hβ, rfl⟩
    refine AddSubgroup.subset_closure ⟨β, hβ, _, ht, ?_⟩
    refine Matrix.ext fun a k => ?_
    change pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (t : D.host.F) * β) ⊗ₜ[D.host.F] y k a =
      pairA D.host.F 0 β ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) • y) k a
    rw [pairA_mul_tmul, Matrix.smul_apply, smul_eq_mul]
  exact hle hmem

end GlobalTheory.HatPoint

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedMatrixGroupOfLocalMultiplierStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedMatrixGroup_of_local_multiplier : ∀ (D : D7) (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)), (∀ (c : 𝓞 D.host.F), ∀ y ∈ A, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ A) → ∀ γ ∈ intAf D.host.F, ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (∀ w : HeightOneSpectrum (𝓞 D.host.F), evalV D.host.F w γ = 0 ∨ ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ (algebraMap D.host.F D.host.E (t : D.host.F)) • y ∈ A) → (Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a : WO S T) ∈ hatA S T A := by
  first | exact @GlobalTheory.HatPoint.mem_hatA_of_div | exact GlobalTheory.HatPoint.mem_hatA_of_div | (intros; apply GlobalTheory.HatPoint.mem_hatA_of_div <;> assumption)
end
end
