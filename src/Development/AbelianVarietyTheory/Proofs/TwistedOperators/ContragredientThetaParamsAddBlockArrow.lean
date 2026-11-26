module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDataAtRealPlaceNegFirstLowEndLtCloud
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrow
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.GridParD

open GlobalTheory.SignedHC Finset

theorem pairPar_X : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i < D.R.m → j ≤ D.R.m →
    PairPar (GlobalTheory.SignedHC.flip (parV D (i + 1) j τ)) (parV D i j τ) (att (cen D τ (D.R.m - i)) (rkV D (i + 1) j))
      (att (cen D τ (D.R.m - i)) (rkV D i j)) := by
  intro D hS i j τ hi hj
  have hnear := grid_nearMid D τ
  have hB1 := gridDataAtRealPlace_neg_firstLowEnd_lt_cloud D τ
  have hbe := grid_hbe D τ
  have heb := grid_heb D τ
  have hbb := grid_hbb D τ hS
  have hga := grid_hga D τ
  have hN0 : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
  have hs2 : ((grid D τ).s : ℚ) + 2 ≤ (grid D τ).ga := by linarith
  have hsOdd := odd_sLen D
  have hle := entries_parD_le (grid D τ) hi hj hnear hB1 hbe hs2
  have hgap : ∀ i', GapOver ((grid D τ).parD i' j) (2 * (bigN D : ℚ) ^ 3) := fun i' =>
    gapOver_parD (grid D τ) i' j hN0 hnear hB1 heb hbb hga
  have hlt : ∀ x ∈ (grid D τ).parD i j, x.1 + ((sLen D : ℚ) + 1) / 2 ≤ (cen D τ (D.R.m - i) : ℚ) := fun x hx =>
    hle x.1 (fst_mem_entries hx)
  have hs0 : (0 : ℚ) ≤ sLen D := by positivity
  set c : ℚ := (cen D τ (D.R.m - i) : ℚ) with hc
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδdef
  set δ' : ℚ := if Odd (i + 1 + j) then -(1 / 2) else 0 with hδ'def
  have e1 : Odd (i + 1 + j) ↔ ¬ Odd (i + j) := by
    rw [show i + 1 + j = (i + j) + 1 by ring]; exact Nat.odd_add_one
  have hδ : att c (rkV D (i + 1) j) = c + δ := by
    by_cases h : Odd (i + j)
    · simp [att, odd_rkV_iff, e1, h, hδdef, sub_eq_add_neg]
    · simp [att, odd_rkV_iff, e1, h, hδdef]
  have hδ' : att c (rkV D i j) = c + δ' := by
    by_cases h : Odd (i + j)
    · simp [att, odd_rkV_iff, e1, h, hδ'def]
    · simp [att, odd_rkV_iff, e1, h, hδ'def, sub_eq_add_neg]
  have key : partner (sLen D) false (c + δ) (c + δ') (shift δ ((grid D τ).parD i j)) =
      flip (shift δ' ((grid D τ).parD (i + 1) j)) := by
    rw [parD_succ _ hi]
    ext y
    simp only [partner, Finset.mem_union, Finset.mem_image, mem_flip, mem_shift, mem_plus]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩)
      · have := hlt _ hx
        left
        rw [if_pos (by simp only at this; linarith)]
        simp only [Bool.not_not]
        convert hx using 2
        ring
      · right
        refine ⟨?_, rfl⟩
        show z - δ' ∈ TPar.block c (sLen D)
        exact sub_mem_block.2 (by simpa [add_comm] using hz)
    · rintro (h | ⟨h1, h2⟩)
      · left
        refine ⟨(y.1 - δ' + δ, !y.2), by simpa using h, ?_⟩
        have := hlt _ h
        rw [if_pos (by simp only at this ⊢; linarith)]
        ext
        · simp only; ring
        · simp
      · right
        refine ⟨y.1, ?_, ?_⟩
        · have : y.1 - δ' ∈ TPar.block c (sLen D) := h1
          simpa [add_comm] using sub_mem_block.1 this
        · ext
          · rfl
          · simpa using h2
  refine ⟨sLen D, flip (shift δ' ((grid D τ).parD (i + 1) j)), shift δ ((grid D τ).parD i j), ?_, rfl, Or.inr ?_⟩
  · exact flip_dualPar _
  · rw [hδ, hδ', ← key]
    have hX : ((grid D τ).parD i j).Nonempty :=
      ⟨((grid D τ).v 2, true), GridData.mem_parD.2 (Or.inl ⟨GridData.mem_cloud.2 ⟨2, le_rfl, (grid D τ).two_le_k, rfl⟩, rfl⟩)⟩
    have hinj : Function.Injective fun x : ℚ × Bool => (x.1 + δ, x.2) := by
      intro a b e
      simp only [Prod.mk.injEq, add_left_inj] at e
      exact Prod.ext e.1 e.2
    have hcard : (shift δ ((grid D τ).parD i j)).card + sLen D ≤ bigN D := by
      rw [shift, card_image_of_injective _ hinj]
      have h1 := card_parD_le (grid D τ) (i := i) (j := j) hi.le
      have h2 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
      have h3 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
      have hr : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
      change _ ≤ D.R.r + j * D.R.t + i * sLen D at h1
      unfold bigN
      nlinarith
    have hN : 1800 < bigN D := by
      have := hS.1
      have hr : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
      unfold bigN
      nlinarith
    refine GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter (sLen D) false (c + δ) (c + δ') _ (bigN D) (by unfold sLen; omega) (hX.image _)
      (GapOver.isRegular hN0 (gapOver_shift δ (hgap i))) ?_ ?_ hcard hN (gapOver_shift δ (hgap i))
      (by rw [key]; exact gapOver_flip (gapOver_shift δ' (hgap (i + 1))))
    · intro x hx
      obtain ⟨sg, hsg⟩ := mem_entries.1 hx
      have h := mem_shift.1 hsg
      obtain ⟨z, hz⟩ := int_of_mem_entries_parD (grid D τ) D.R.t_odd hsOdd (fst_mem_entries h)
      obtain ⟨w, hw⟩ := hsOdd
      simp only at hz
      refine ⟨z - cen D τ (D.R.m - i) - (w + 1), ?_⟩
      rw [hw]
      push_cast
      linarith
    · intro x hx
      obtain ⟨sg, hsg⟩ := mem_entries.1 hx
      have h := hlt _ (mem_shift.1 hsg)
      simp only at h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith

end GlobalTheory.GridParD

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_addBlockArrow : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i < D.R.m → j ≤ D.R.m → PairPar (GlobalTheory.SignedHC.flip (parV D (i + 1) j τ)) (parV D i j τ) (att (cen D τ (D.R.m - i)) (rkV D (i + 1) j)) (att (cen D τ (D.R.m - i)) (rkV D i j)) := by
  first | exact @GlobalTheory.GridParD.pairPar_X | exact GlobalTheory.GridParD.pairPar_X | (intros; apply GlobalTheory.GridParD.pairPar_X <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedThetaCharactersRestrictionRamification
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedThetaCharactersRestrictionRamification
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSplitChars
open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E]

theorem twVal_of_unit (χ : HChar E) (w : ℝ) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) (hk : P.valuation E (k : E) = 1) :
    twVal χ w P k = ((χ.locK P k : ℂˣ) : ℂ) := by
  have h0 : Formalism.L2.Host.ordF P k = 0 := by simp [Formalism.L2.Host.ordF, hk]
  simp [twVal, h0]

theorem isClopen_oneUnits (P : HeightOneSpectrum (𝓞 E)) :
    IsClopen {x : (P.adicCompletion E)ˣ | Valued.v ((x : P.adicCompletion E) - 1) < 1} := by
  have := (Valued.isClopen_ball (P.adicCompletion E) (r := 1)).preimage
      (f := fun x : (P.adicCompletion E)ˣ => (x : P.adicCompletion E) - 1)
      ((Units.continuous_val (M := P.adicCompletion E)).sub continuous_const)
  convert this using 1
  ext x
  simp

theorem tameAt_of_locK (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ u : Eˣ, P.valuation E ((u : E) - 1) < 1 → χ.locK P u = 1) : χ.TameAt P := by
  have key : ∀ x : (P.adicCompletion E)ˣ, Valued.v ((x : P.adicCompletion E) - 1) < 1 → χ.loc P x = 1 := by
    intro x
    refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin P).induction_on
      (p := fun x => Valued.v ((x : P.adicCompletion E) - 1) < 1 → χ.loc P x = 1) x ?_ fun k hk => h k ?_
    · exact isClosed_imp (isClopen_oneUnits P).2
        (isClosed_eq (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele P)) continuous_const)
    · have e : ((GlobalTheory.Mem.Chr.atFin P k : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1 =
          algebraMap E (P.adicCompletion E) ((k : E) - 1) := by
        rw [map_sub, map_one]; rfl
      rwa [e, Formalism.UG.P.levelaf_valued_algebraMap] at hk
  intro x _ hx
  refine key x (lt_of_le_of_lt hx ?_)
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.2 (by norm_num)

theorem locK_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ)
    (hk : P.valuation E (k : E) = 1) : ((χ'.locK P k : ℂˣ) : ℂ) = s ((χ.locK P k : ℂˣ) : ℂ) := by
  have := h P k
  rwa [twVal_of_unit _ _ _ _ hk, twVal_of_unit _ _ _ _ hk] at this

theorem unrAt_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') {P : HeightOneSpectrum (𝓞 E)}
    (hu : χ.UnrAt P) : χ'.UnrAt P :=
  GlobalTheory.EtaConjType.unrAt_of_locK χ' P fun u hu' => Units.ext (by
    rw [locK_conj h P u hu', GlobalTheory.NormOneUnit.locK_unr hu hu', Units.val_one, map_one])

theorem tameAt_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') {P : HeightOneSpectrum (𝓞 E)}
    (ht : χ.TameAt P) : χ'.TameAt P := by
  refine tameAt_of_locK χ' P fun u hu => Units.ext ?_
  have h1 : P.valuation E ((1 : Eˣ) : E) = 1 := by simp
  have hu1 : P.valuation E (u : E) = 1 := by
    have := Valuation.map_eq_of_sub_lt (P.valuation E) (x := 1) (y := (u : E)) (by rwa [map_one])
    rwa [map_one] at this
  rw [locK_conj h P u hu1, GlobalTheory.NormOneUnit.locK_tame ht h1 (by simpa using hu), map_one, Units.val_one, map_one]


open Classical in
theorem conj_chars_res : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ i t s cμ cη m, IsConjChars R i t s cμ cη m → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP)) ∧ (∀ Z : Finset (Pl D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ Z) → GlobalTheory.StepLaw.UnrOff cμ Z ∧ GlobalTheory.StepLaw.UnrOff (cμ * cη⁻¹) Z) ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ finS R t → UnrAt cμ w ∧ UnrAt (cμ * cη⁻¹) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t s cμ cη m hc
  obtain ⟨μ', η', hμ, hη, ecμ, ecη, hres⟩ := hc
  obtain ⟨-, p1, p2, p3⟩ := GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T R.toLevCh A.μ0 hL t
  have uη : ∀ P, η'.UnrAt P := fun P => unrAt_conj hη (R.C.isEta.unr P)
  have uμ : ∀ P : Pl D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) →
      μ'.UnrAt P := fun P hP => unrAt_conj hμ (((p3 P hP).2 i).mul (p3 P hP).1)
  have tμ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → μ'.TameAt PP := by
    intro PP hPP
    refine tameAt_conj hμ ?_
    rcases hPP with hP | hP
    · exact ((R.C.isMu0 i).tame PP).mul ((p1 PP hP).levelLe 1)
    · exact ((p2 PP hP i).levelLe 1).mul (hL.xi_tame t PP)
  have rη : ∀ PP, GlobalTheory.StepLaw.ResAt cη⁻¹ PP 1 := fun PP => by
    have := ((GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D cη η' ecη PP).2 (uη PP)).inv
    rwa [inv_one] at this
  have uoη : ∀ Z, GlobalTheory.StepLaw.UnrOff cη Z := fun Z v ε hε _ =>
    GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cη η' ecη v ε hε fun P _ => uη P
  refine ⟨fun PP hPP => ?_, fun Z hZ => ?_, fun w hw => ?_⟩
  · have h1 := (GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D cμ μ' ecμ PP).1 (m PP) (tμ PP hPP) (hres PP hPP)
    refine ⟨h1, ?_⟩
    have := h1.mul (rη PP)
    rwa [mul_one] at this
  · have h1 : GlobalTheory.StepLaw.UnrOff cμ Z := fun v ε hε hv =>
      GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cμ μ' ecμ v ε hε fun P hP => uμ P fun PP hPP => hP ▸ hv PP (hZ PP hPP)
    exact ⟨h1, h1.mul (uoη Z).inv⟩
  · have hw' : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ w.under (𝓞 D.host.F) := fun PP hPP he =>
      hw (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, he⟩)
    have h1 : UnrAt cμ w := (unrAt_iff_of_chrEq ecμ w).2 (uμ w hw')
    exact ⟨h1, h1.mul ((unrAt_iff_of_chrEq ecη w).2 (uη w)).inv⟩

end GlobalTheory.ConjSplitChars

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedThetaCharactersRestrictionRamificationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ i t s cμ cη m, IsConjChars R i t s cμ cη m → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP)) ∧ (∀ Z : Finset (Pl D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ Z) → GlobalTheory.StepLaw.UnrOff cμ Z ∧ GlobalTheory.StepLaw.UnrOff (cμ * cη⁻¹) Z) ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ finS R t → UnrAt cμ w ∧ UnrAt (cμ * cη⁻¹) w := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t s cμ cη m hc
  obtain ⟨μ', η', hμ, hη, ecμ, ecη, hres⟩ := hc
  obtain ⟨-, p1, p2, p3⟩ := GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T R.toLevCh A.μ0 hL t
  have uη : ∀ P, η'.UnrAt P := fun P => GlobalTheory.ConjSplitChars.unrAt_conj hη (R.C.isEta.unr P)
  have uμ : ∀ P : Pl D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) →
      μ'.UnrAt P := fun P hP => GlobalTheory.ConjSplitChars.unrAt_conj hμ (((p3 P hP).2 i).mul (p3 P hP).1)
  have tμ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → μ'.TameAt PP := by
    intro PP hPP
    refine GlobalTheory.ConjSplitChars.tameAt_conj hμ ?_
    rcases hPP with hP | hP
    · exact ((R.C.isMu0 i).tame PP).mul ((p1 PP hP).levelLe 1)
    · exact ((p2 PP hP i).levelLe 1).mul (hL.xi_tame t PP)
  have rη : ∀ PP, GlobalTheory.StepLaw.ResAt cη⁻¹ PP 1 := fun PP => by
    have := ((GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D cη η' ecη PP).2 (uη PP)).inv
    rwa [inv_one] at this
  have uoη : ∀ Z, GlobalTheory.StepLaw.UnrOff cη Z := fun Z v ε hε _ =>
    GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cη η' ecη v ε hε fun P _ => uη P
  refine ⟨fun PP hPP => ?_, fun Z hZ => ?_, fun w hw => ?_⟩
  · have h1 := (GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D cμ μ' ecμ PP).1 (m PP) (tμ PP hPP) (hres PP hPP)
    refine ⟨h1, ?_⟩
    have := h1.mul (rη PP)
    rwa [mul_one] at this
  · have h1 : GlobalTheory.StepLaw.UnrOff cμ Z := fun v ε hε hv =>
      GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cμ μ' ecμ v ε hε fun P hP => uμ P fun PP hPP => hP ▸ hv PP (hZ PP hPP)
    exact ⟨h1, h1.mul (uoη Z).inv⟩
  · have hw' : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ w.under (𝓞 D.host.F) := fun PP hPP he =>
      hw (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, he⟩)
    have h1 : UnrAt cμ w := (unrAt_iff_of_chrEq ecμ w).2 (uμ w hw')
    exact ⟨h1, h1.mul ((unrAt_iff_of_chrEq ecη w).2 (uη w)).inv⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartMemCompactOfIsotropicAnnihilator
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalTestMatrixIsolatesEntry
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalTestMatrixIsolatesEntry
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EntryTest

theorem exists_left_inv {K : Type} [Field K] {m n : ℕ} (P : Matrix (Fin m) (Fin n) K) (h : P.rank = n) :
    ∃ P' : Matrix (Fin n) (Fin m) K, P' * P = 1 := by
  have hker : LinearMap.ker P.mulVecLin = ⊥ := by
    have e := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [← Matrix.rank, h, Module.finrank_fin_fun] at e
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective P.mulVecLin hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' P, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' P = P.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

theorem exists_right_inv {K : Type} [Field K] {m n : ℕ} (Q : Matrix (Fin m) (Fin n) K) (h : Q.rank = m) :
    ∃ Q' : Matrix (Fin n) (Fin m) K, Q * Q' = 1 := by
  have hrange : LinearMap.range Q.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, h, Module.finrank_fin_fun]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Q.mulVecLin hrange
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' Q, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' Q = Q.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

variable {D : D7}

theorem hO_test (V W : HSp D) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (x : WO V W) :
    hO V W x ((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) = ∑ a, ∑ d, incA D (N a d) * x d a := by
  have h1 : V.gram⁻¹ * (V.gram * N * W.gram⁻¹) * W.gram = N := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit W), Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  have hc : ∀ b c, cA D (((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) c b) = incA D ((V.gram * N * W.gram⁻¹) b c) := by
    intro b c
    rw [Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, Matrix.of_apply, star_star]
  unfold hO
  simp only [hc]
  generalize V.gram * N * W.gram⁻¹ = M at h1
  subst h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_emb_single (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (i : Fin a) (j : Fin b)
    (e : D.host.E) (hN : Q * N * P = Matrix.single j i e) (y : Mx D a b) :
    ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k = incA D e * y i j := by
  have h1 : ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k =
      (N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h2 : N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y =
      N.map (incA D) * (P.map (incA D) * y) * Q.map (incA D) := by
    simp only [GlobalTheory.IsoMean.emb, Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hN]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem entry : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (i : Fin a) (j : Fin b) (c : D.host.E), ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E, ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) = r * Algebra.trace (AF D.host.F) (AE D) (incA D c * y i j) := by
  intro D V W a b P Q hP hQ i j c
  obtain ⟨P', hP'⟩ := exists_left_inv P hP
  obtain ⟨Q', hQ'⟩ := exists_right_inv Q hQ
  set N := Q' * Matrix.single j i (D.host.xi0⁻¹ * c) * P' with hNdef
  have hN : Q * N * P = Matrix.single j i (D.host.xi0⁻¹ * c) := by
    rw [hNdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul, Matrix.mul_assoc, hP', Matrix.mul_one]
  refine ⟨Matrix.of fun q p => star ((V.gram * N * W.gram⁻¹) p q), fun y r => ?_⟩
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, GlobalTheory.FinTranslate.symplOH_smul_right, ← mul_add,
    GlobalTheory.SplitScalar.symplOH_add_self]
  congr 1
  rw [symplO, hO_test, sum_emb_single V W P Q N i j _ hN y, ← mul_assoc, ← map_mul,
    mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]

end GlobalTheory.EntryTest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalTestMatrixIsolatesEntryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_test_matrix_isolates_entry : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (i : Fin a) (j : Fin b) (c : D.host.E), ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E, ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) = r * Algebra.trace (AF D.host.F) (AE D) (incA D c * y i j) := by
  first | exact @GlobalTheory.EntryTest.entry | exact GlobalTheory.EntryTest.entry | (intros; apply GlobalTheory.EntryTest.entry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartMemCompactOfIsotropicAnnihilator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanAnnih

theorem finPart_mem_compact : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧ ∀ y : Mx D a b, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W (GlobalTheory.IsoMean.emb V W P Q y) u) = 1) → y.map (finPart D) ∈ K := by
  intro D V W a b P Q hP hQ ψ hψ U hU
  obtain ⟨d, c, e, hce⟩ := GlobalTheory.T.finitePart_eq_sum_trace_traceDualBasis D
  have hm : ∀ p : Fin a × Fin b × Fin d, ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E,
      ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) =
        r * Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1) :=
    fun p => GlobalTheory.T.exists_rational_test_matrix_isolates_entry D V W a b P Q hP hQ p.1 p.2.1 (c p.2.2)
  choose m hm using hm
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  let φ : (Fin a × Fin b × Fin d) → Af D.host.F → WO V W :=
    fun p t => (pairA D.host.F 0 t) • (m p).map (incA D)
  have hpair : Continuous fun t : Af D.host.F => pairA D.host.F 0 t := continuous_const.prodMk continuous_id
  have hφ : ∀ p, Continuous (φ p) := fun p =>
    Continuous.smul (f := fun t : Af D.host.F => pairA D.host.F 0 t) (g := fun _ => (m p).map (incA D)) hpair continuous_const
  have hφ0 : ∀ p, φ p 0 = 0 := fun p => by
    have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
    simp only [φ, this, zero_smul]
  have hO : (⋂ p, φ p ⁻¹' (U : Set (WO V W))) ∈ nhds (0 : Af D.host.F) :=
    Filter.iInter_mem.2 fun p => (hφ p).continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by rw [hφ0]; exact U.zero_mem))
  obtain ⟨K₀, hK₀, hmem⟩ := GlobalTheory.T.exists_compact_annihilator_finiteAdeles_stdChar D ψ hψ _ hO
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : ContinuousSMul (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousSMul _ _
  haveI : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousAdd (Af D.host.F) _
  let g : (Fin a × Fin b × Fin d → Af D.host.F) → Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun z => Matrix.of fun i j => ∑ l, z (i, j, l) ⊗ₜ[D.host.F] e l
  have hg : Continuous g := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun z : Fin a × Fin b × Fin d → Af D.host.F => ∑ l, z (i, j, l) ⊗ₜ[D.host.F] e l
    refine continuous_finsetSum _ fun l _ => ?_
    have : (fun z : Fin a × Fin b × Fin d → Af D.host.F => z (i, j, l) ⊗ₜ[D.host.F] e l) =
        fun z => z (i, j, l) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] e l) := by
      funext z; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Continuous.smul (continuous_apply (A := fun _ : Fin a × Fin b × Fin d => Af D.host.F) (i, j, l))
      (continuous_const (y := ((1 : Af D.host.F) ⊗ₜ[D.host.F] e l)))
  refine ⟨g '' Set.pi Set.univ (fun _ => K₀), (isCompact_univ_pi fun _ => hK₀).image hg, fun y hy =>
    ⟨fun p => sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1)),
      fun p _ => hmem _ fun t ht => ?_, ?_⟩⟩
  · have hu : φ p t ∈ U := Set.mem_iInter.1 ht p
    have hinf : (φ p t).map (infPart D) = 0 := by
      ext k l
      simp only [φ, Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply]
      change infPart D (pairA D.host.F 0 t • ((1 : AF D.host.F) ⊗ₜ[D.host.F] m p k l)) = 0
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change (fstA D.host.F (pairA D.host.F 0 t)) ⊗ₜ[D.host.F] (m p k l) = 0
      exact TensorProduct.zero_tmul _ _
    have h1 := hy _ hu hinf
    simp only [φ] at h1
    rw [hm] at h1
    convert h1 using 2
    exact Prod.ext (zero_mul _).symm rfl
  · ext i j
    simp only [g, Matrix.of_apply, Matrix.map_apply]
    rw [hce]

end GlobalTheory.IsoMeanAnnih
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartMemCompactOfIsotropicAnnihilatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_mem_compact_of_isotropicAnnihilator : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧ ∀ y : Mx D a b, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W (GlobalTheory.IsoMean.emb V W P Q y) u) = 1) → y.map (finPart D) ∈ K := by
  first | exact @GlobalTheory.IsoMeanAnnih.finPart_mem_compact | exact GlobalTheory.IsoMeanAnnih.finPart_mem_compact | (intros; apply GlobalTheory.IsoMeanAnnih.finPart_mem_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparate
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparate
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSeparate

open GlobalTheory.IdemModTwo

theorem sum_incA_inv_mul {D : D7} (W : HSp D) (p i : Fin W.rank) :
    ∑ k, incA D (W.gram⁻¹ p k) * incA D (W.gram k i) = if p = i then 1 else 0 := by
  have h1 : (∑ k, incA D (W.gram⁻¹ p k) * incA D (W.gram k i)) = incA D ((W.gram⁻¹ * W.gram) p i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum (incA D)]
    exact Finset.sum_congr rfl fun k _ => ((incA D).map_mul _ _).symm
  rw [h1, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit W), Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _


set_option maxHeartbeats 1000000 in
theorem exists_pair_entry {D : D7} {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)}
    {e : AE D} (he : SplitAt D v e) (W : HSp D) {r : ℕ} (p : Fin W.rank) (q : Fin r) (c : Fv D.host.F v) :
    ∃ a : Mx D W.rank r, IsHalf e a ∧ ∀ t : Mx D W.rank r,
      halfPair W a t = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * t p q := by
  let a : Mx D W.rank r := Matrix.of fun k j => if j = q then
    incA D (star (W.gram⁻¹ p k)) * incA D (star D.host.xi0⁻¹) * fj D (singleV D.host.F v c) * e else 0
  have hca : ∀ k, cA D (a k q) = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * incA D (W.gram⁻¹ p k) := by
    intro k
    show cA D (if q = q then _ else 0) = _
    rw [if_pos rfl, map_mul, map_mul, map_mul, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.cA_incA, star_star, star_star,
      cA_fj]
    ring
  refine ⟨a, fun k j => ?_, fun t => ?_⟩
  · show e * a k j = a k j
    simp only [a, Matrix.of_apply]
    split_ifs
    · rw [mul_left_comm, he.1]
    · rw [mul_zero]
  have hG := sum_incA_inv_mul W p
  unfold halfPair
  calc ∑ i, ∑ j, ∑ k, cA D (a k j) * incA D (W.gram k i) * t i j
      = ∑ i, incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * (if p = i then 1 else 0) * t i q :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_eq_single q (fun j _ hj => Finset.sum_eq_zero fun k _ => by
            rw [show a k j = 0 from if_neg hj, map_zero, zero_mul, zero_mul]) (fun h => absurd (Finset.mem_univ q) h)]
          rw [← hG i, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by rw [hca]; ring
    _ = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * t p q := by
      rw [Finset.sum_eq_single p (fun i _ hi => by rw [if_neg (Ne.symm hi), mul_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ p) h), if_pos rfl, mul_one]

end GlobalTheory.HalfSeparate

namespace GlobalTheory.HalfSeparate

open GlobalTheory.IdemModTwo


set_option maxHeartbeats 1000000 in
theorem exists_open_separated : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (e : AE D), IsSplitIdem D e → ∀ U : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (U : Set (halfMx (cA D e) W.rank r)) → ∃ L : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ L ≤ U ∧ ∀ x, x ∉ L → ∃ a : halfMx e W.rank r, (∀ l ∈ L, ψ (halfSympl W (a : Mx D W.rank r) (l : Mx D W.rank r)) = 1) ∧ ψ (halfSympl W (a : Mx D W.rank r) (x : Mx D W.rank r)) ≠ 1 := by
  intro D ψ hψ W r e hε U hU
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  have he' := he.conj
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  let sg : Fv D.host.F v →+ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F := AddMonoidHom.ofMapSub (singleV D.host.F v) (singleV_sub D v)
  let ι : Fv D.host.F v →+ AF D.host.F := AddMonoidHom.mk' (fun y => pairA D.host.F 0 (sg y)) fun a b => by
    rw [map_add (f := _)]; exact Prod.ext (add_zero _).symm rfl
  have hι : Continuous ι := Continuous.prodMk continuous_const (GlobalTheory.SplitAnnihilator.continuous_singleV D.host.F v)
  have hψc : Continuous fun x => ψ (ι x) := hψ.1.1.comp hι

  obtain ⟨ε0, hε0, hψε⟩ : ∃ ε > 0, ∀ x : Fv D.host.F v, ‖x‖ < ε → ψ (ι x) = 1 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hψc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun x hx => GlobalTheory.ThetaStalk.eq_one_of_pow_near fun n => ?_⟩
    have := h (x := n • x) (by
      rw [dist_zero_right]; exact (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx)
    rwa [map_zero, AddChar.map_zero_eq_one, dist_eq_norm, map_nsmul, AddChar.map_nsmul_eq_pow] at this
  obtain ⟨y1, hy1⟩ : ∃ y, ψ (ι y) ≠ 1 := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v

  let G := Fin W.rank × Fin r → Fv D.host.F v
  let J : G →+ Mx D W.rank r := AddMonoidHom.mk' (fun y => Matrix.of fun i k => fj D (sg (y (i, k))) * cA D e)
    fun a b => by
      ext i k
      simp only [G, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul]
  have hJ : Continuous J := continuous_matrix fun i k =>
    ((IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))).comp
      (hι.comp (continuous_apply (i, k)))).mul continuous_const
  have hJh : ∀ y, J y ∈ halfMx (cA D e) W.rank r := fun y i k => by
    show cA D e * (_ * cA D e) = _ * cA D e
    rw [mul_left_comm, he'.1]
  let J' : G →+ halfMx (cA D e) W.rank r := J.codRestrict (halfMx (cA D e) W.rank r) hJh
  have hJ' : Continuous J' := hJ.subtype_mk _
  have hJs : Function.Surjective J' := fun u => by
    choose y hy using fun p : Fin W.rank × Fin r => he'.exists_scalar ((u : Mx D W.rank r) p.1 p.2)
    exact ⟨y, Subtype.ext (Matrix.ext fun i k => (hy (i, k)).symm.trans (u.2 i k))⟩
  have : T2Space (halfMx (cA D e) W.rank r) := t2Space_halfAdelicMatrixAddSubgroup (cA D e) W.rank r
  have : LocallyCompactSpace (halfMx (cA D e) W.rank r) := lcHalf (cA D e) W.rank r
  have : R1Space (halfMx (cA D e) W.rank r) := T2Space.r1Space
  have : BaireSpace (halfMx (cA D e) W.rank r) := BaireSpace.of_t2Space_locallyCompactSpace
  have hopen : IsOpenMap J' := AddMonoidHom.isOpenMap_of_sigmaCompact J' hJs hJ'
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hJ') 0 (by
    show J' 0 ∈ U
    rw [map_zero]; exact U.zero_mem)

  have hR : 0 ≤ ‖y1‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  let LG : AddSubgroup G :=
    { carrier := {y | ∀ p, ∀ c : Fv D.host.F v, ‖c‖ ≤ ‖y1‖ / ρ → ψ (ι (c * y p)) = 1}
      add_mem' := fun {a b} ha hb p c hc => by
        rw [Pi.add_apply, mul_add, map_add (f := _), AddChar.map_add_eq_mul, ha p c hc, hb p c hc, one_mul]
      zero_mem' := fun p c _ => by rw [Pi.zero_apply, mul_zero, map_zero, AddChar.map_zero_eq_one]
      neg_mem' := fun {a} ha p c hc => by
        have h := ψ.map_add_eq_mul (ι (c * (-a) p)) (ι (c * a p))
        rw [← map_add (f := _), Pi.neg_apply, mul_neg, neg_add_cancel, map_zero, AddChar.map_zero_eq_one, ha p c hc,
          mul_one] at h
        rw [Pi.neg_apply, mul_neg]
        exact h.symm }
  have hLGopen : IsOpen (LG : Set G) := by
    refine AddSubgroup.isOpen_of_mem_nhds LG (g := 0) (Metric.mem_nhds_iff.2 ⟨ε0 / (‖y1‖ / ρ + 1), by positivity,
      fun y hy p c hc => hψε _ ?_⟩)
    have hy' : ‖y‖ < ε0 / (‖y1‖ / ρ + 1) := mem_ball_zero_iff.1 hy
    rw [lt_div_iff₀ (by positivity)] at hy'
    calc ‖c * y p‖ = ‖c‖ * ‖y p‖ := norm_mul _ _
      _ ≤ ‖y1‖ / ρ * ‖y‖ := mul_le_mul hc (norm_le_pi_norm y p) (norm_nonneg _) hR
      _ ≤ ‖y‖ * (‖y1‖ / ρ + 1) := by nlinarith [norm_nonneg y]
      _ < ε0 := hy'
  have hLGsmall : ∀ y ∈ LG, ‖y‖ < ρ := fun y hy => (pi_norm_lt_iff hρ).2 fun p => by
    by_contra hn
    push_neg at hn
    have hp : 0 < ‖y p‖ := hρ.trans_le hn
    have h := hy p (y1 / y p) (by rw [norm_div]; exact div_le_div_of_nonneg_left (norm_nonneg _) hρ hn)
    rw [div_mul_cancel₀ _ (norm_pos_iff.1 hp)] at h
    exact hy1 h
  refine ⟨LG.map J', by rw [AddSubgroup.coe_map]; exact hopen _ hLGopen, ?_, fun x hx => ?_⟩
  · rw [AddSubgroup.map_le_iff_le_comap]
    intro y hy
    exact hball (mem_ball_zero_iff.2 (hLGsmall y hy))
  obtain ⟨y, rfl⟩ := hJs x
  have hy : ¬ ∀ p, ∀ c : Fv D.host.F v, ‖c‖ ≤ ‖y1‖ / ρ → ψ (ι (c * y p)) = 1 :=
    fun h => hx (AddSubgroup.mem_map_of_mem _ h)
  push_neg at hy
  obtain ⟨p, c, hc, hne⟩ := hy
  obtain ⟨a, ha, hpair⟩ := exists_pair_entry he W p.1 p.2 c
  have key : ∀ y', ψ (halfSympl W a (J y')) = ψ (ι (c * y' p)) := fun y' => by
    congr 1
    have h1 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]
    have h2 : incA D D.host.xi0 * halfPair W a (J y') =
        fj D (singleV D.host.F v c) * cA D e * (fj D (singleV D.host.F v (y' p)) * cA D e) := by
      rw [hpair]
      show incA D D.host.xi0 * (incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e *
        (fj D (singleV D.host.F v (y' p)) * cA D e)) = _
      linear_combination (fj D (singleV D.host.F v c) * cA D e * (fj D (singleV D.host.F v (y' p)) * cA D e)) * h1
    rw [halfSympl, h2]
    exact GlobalTheory.SplitAnnihilator.trace_split he' c (y' p)
  refine ⟨⟨a, ha⟩, fun l hl => ?_, (key y).trans_ne hne⟩
  obtain ⟨y', hy', rfl⟩ := AddSubgroup.mem_map.1 hl
  exact (key y').trans (hy' p c hc)

end GlobalTheory.HalfSeparate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_half_characters_separate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (e : AE D), IsSplitIdem D e → ∀ U : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (U : Set (halfMx (cA D e) W.rank r)) → ∃ L : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ L ≤ U ∧ ∀ x, x ∉ L → ∃ a : halfMx e W.rank r, (∀ l ∈ L, ψ (halfSympl W (a : Mx D W.rank r) (l : Mx D W.rank r)) = 1) ∧ ψ (halfSympl W (a : Mx D W.rank r) (x : Mx D W.rank r)) ≠ 1 := by
  first | exact @GlobalTheory.HalfSeparate.exists_open_separated | exact GlobalTheory.HalfSeparate.exists_open_separated | (intros; apply GlobalTheory.HalfSeparate.exists_open_separated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonLevelGrowthExponentGKMap
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteLeOfGKStableDiscreteSeriesModelStatement
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_le_of_gKStable_discreteSeriesModel : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (W : Submodule ℂ (M.H τ)), W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → (∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W) → (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W) → W ≠ ⊥ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ W := by
  first | exact @GlobalTheory.HCModIrred.kFin_le_of_stable | exact GlobalTheory.HCModIrred.kFin_le_of_stable | (intros; apply GlobalTheory.HCModIrred.kFin_le_of_stable <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonLevelGrowthExponentGKMap
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GKUnif

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def Good (θ : InfFam D) (V : HSp D) (U : Subgroup (GA D V)) (N : ℕ) (φ : GA D V → ℂ) : Prop :=
  (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N φ ≠ ⊤

variable {θ : InfFam D} {U : Subgroup (GA D V)} {N : ℕ} {φ ψ : GA D V → ℂ}

theorem good_add (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) (hs' : ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V)
    (h : Good θ V U N φ) (h' : Good θ V U N ψ) : Good θ V U N (φ + ψ) :=
  ⟨fun k hk hk' g => by simp only [Pi.add_apply, h.1 k hk hk' g, h'.1 k hk hk' g],
    fun d => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h.2 d, h'.2 d⟩) (GlobalTheory.Size.growthSob_add_le hs hs' d N)⟩

theorem good_smul (c : ℂ) (h : Good θ V U N φ) : Good θ V U N (c • φ) :=
  ⟨fun k hk hk' g => by simp only [Pi.smul_apply, h.1 k hk hk' g],
    fun d => by rw [GlobalTheory.Size.growthSob_smul]; exact ENNReal.mul_ne_top enorm_ne_top (h.2 d)⟩

theorem good_zero : Good θ V U N 0 := by
  have h := good_smul (θ := θ) (U := U) (N := N) (φ := 0) 0
  rw [zero_smul] at h
  refine h ⟨fun _ _ _ _ => rfl, fun d => ?_⟩
  have e := GlobalTheory.Size.growthSob_smul (θ := θ) (V := V) (φ := 0) 0 d N
  rw [zero_smul, enorm_zero, zero_mul] at e
  rw [e]; exact ENNReal.zero_ne_top

theorem good_Rder (hθ : IsInfFam θ) (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (h : Good θ V U N φ) :
    Good θ V U N (Rder θ V τ X φ) := by
  refine ⟨fun k hk hk' g => ?_, fun d => ?_⟩
  · have e : rTr V k φ = φ := funext (h.1 k hk hk')
    have := congrFun (GlobalTheory.Size.Rder_rTr_fin (θ := θ) hk' τ X φ) g
    rw [e] at this
    exact this.symm
  · rw [← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX φ]
    have hB : ∀ a b, ‖X a b‖ₑ ≤ ∑ a', ∑ b', ‖X a' b'‖ₑ := fun a b =>
      (Finset.single_le_sum (f := fun b' => ‖X a b'‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ b)).trans
        (Finset.single_le_sum (f := fun a' => ∑ b', ‖X a' b'‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ a))
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.Size.Translate.growthSob_RderC_le hθ hs τ hB d N)
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ (h.2 (d + 1)))
    exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ => enorm_ne_top

theorem good_rTr (hθ : IsInfFam θ) (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) {h : GA D V} (hh : h ∈ GinfC V)
    (hg : Good θ V U N φ) : Good θ V U N (rTr V h φ) := by
  refine ⟨fun k hk hk' g => ?_, fun d => ?_⟩
  · show φ (g * k * h) = φ (g * h)
    rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V hh hk', ← mul_assoc, hg.1 k hk hk']
  · obtain ⟨C, m, hC⟩ := GlobalTheory.Size.Translate.growthSob_rTr_le D θ hθ V d N
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (hg.2 d)) (hC h hh φ hs)

theorem conj_mem_lieSet (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : M.fr τ * X * (M.fr τ)⁻¹ ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ) := by
  have hX' : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  rw [← M.fr_gram τ] at hX'
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h2 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) = 0
  have e : (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) =
      ((M.fr τ)⁻¹)ᴴ * (Xᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
        (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * X) * (M.fr τ)⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_one, hc]
  rw [e, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem dRep_mem_kFin (hHC : GlobalTheory.Published.HarishChandraModules) (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {w : M.H τ}
    (hw : w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) : dRep (M.rep τ) X w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hd : dRep (M.rep τ) X w = dRep (M.σ τ) (M.fr τ * X * (M.fr τ)⁻¹) w := by
    unfold dRep
    congr 1
    funext t
    show M.σ τ (M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹) w = _
    rw [← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]
  rw [hd]
  exact GlobalTheory.TypeSum.isKFin_dRep _ _ _ _ hstd w hw _ (conj_mem_lieSet M τ hX)

end GlobalTheory.GKUnif

namespace GlobalTheory.GKUnif

theorem exists_level_exponent : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ →
    ∃ (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) ∧
      ∀ u, (∀ k ∈ U, k ∈ GfC V → ∀ g, T₀ u (g * k) = T₀ u g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T₀ u) ≠ ⊤ := by
  intro hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀
  have hne : ∀ τ, ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, w ≠ 0 := fun τ => by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
    exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  choose u₀ hu₀ using hne
  obtain ⟨U, hU, hUl⟩ := (hT₀.1 u₀).level
  obtain ⟨N, hN⟩ := GlobalTheory.Size.exists_growthSob_ne_top (hT₀.2.1 u₀) (hT₀.2.2.2.2.1 u₀)
  have hsm : ∀ u, T₀ u ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := hT₀.2.1
  suffices key : ∀ s : Finset D.what₂.Tau, ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (∀ τ ∉ s, u τ = u₀ τ) →
      Good θ V U N (T₀ u) from
    ⟨U, N, hU, fun u => key Finset.univ u (fun τ h => absurd (Finset.mem_univ τ) h)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro u hu
    have : u = u₀ := funext fun τ => hu τ (Finset.notMem_empty τ)
    subst this
    exact ⟨hUl, hN⟩
  | insert τ s hτ ih =>
    intro u hu
    let Wk : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) :=
      { carrier := {w | Good θ V U N (T₀ (Function.update u τ w))}
        add_mem' := fun {a b} ha hb => by
          show Good θ V U N (T₀ (Function.update u τ (a + b)))
          rw [T₀.map_update_add]
          exact good_add (hsm _) (hsm _) ha hb
        zero_mem' := by
          show Good θ V U N (T₀ (Function.update u τ 0))
          rw [T₀.map_update_zero]
          exact good_zero
        smul_mem' := fun c a ha => by
          show Good θ V U N (T₀ (Function.update u τ (c • a)))
          rw [T₀.map_update_smul]
          exact good_smul c ha }
    let W : Submodule ℂ (M.H τ) := Wk.map (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).subtype
    have hmemW : ∀ y : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, y ∈ Wk → (y : M.H τ) ∈ W := fun y hy => ⟨y, hy, rfl⟩
    have hWk : ∀ w ∈ W, ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, y ∈ Wk ∧ (y : M.H τ) = w := by
      rintro w ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    have hle : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := Submodule.map_subtype_le _ _
    have hlie : ∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W := by
      intro X hX w hw
      obtain ⟨y, hy, rfl⟩ := hWk w hw
      let y' : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := ⟨dRep (M.rep τ) X y, dRep_mem_kFin hHC M τ hX y.2⟩
      refine hmemW y' ?_
      have e := hT₀.2.2.2.2.2.2.2 τ X hX (Function.update u τ y) y' (by simp [y'])
      rw [Function.update_idem] at e
      show Good θ V U N (T₀ (Function.update u τ y'))
      rw [e]
      exact good_Rder hθ (hsm _) hX hy
    have hK : ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W := by
      intro k hk w hw
      obtain ⟨y, hy, rfl⟩ := hWk w hw
      let y' : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := ⟨M.rep τ k y, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.rep_mem_kFin M τ hk y.2⟩
      refine hmemW y' ?_
      have e := hT₀.2.2.2.2.2.2.1 τ k hk (Function.update u τ y) y' (by simp [y'])
      rw [Function.update_idem] at e
      show Good θ V U N (T₀ (Function.update u τ y'))
      rw [e]
      exact good_rTr hθ (hsm _) (GlobalTheory.PointAtPlaceHom.atTau_mem V τ k) hy
    have h0 : u₀ τ ∈ Wk := by
      show Good θ V U N (T₀ (Function.update u τ (u₀ τ)))
      refine ih _ fun τ' h' => ?_
      by_cases e : τ' = τ
      · subst e; simp
      · rw [Function.update_of_ne e]
        exact hu τ' (by simp [e, h'])
    have hWne : W ≠ ⊥ := fun hb => hu₀ τ (Subtype.ext (by
      have := hmemW _ h0
      rw [hb] at this
      simpa using this))
    have hall := GlobalTheory.T.kFinite_le_of_gKStable_discreteSeriesModel hHC D V S M τ W hle hlie hK hWne
    obtain ⟨y, hy, hyu⟩ := hWk _ (hall (u τ).2)
    have : y = u τ := Subtype.ext hyu
    subst this
    have e : Function.update u τ (u τ) = u := Function.update_eq_self τ u
    have hy' : Good θ V U N (T₀ (Function.update u τ (u τ))) := hy
    rwa [e] at hy'

end GlobalTheory.GKUnif

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonLevelGrowthExponentGKMapStatement
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_level_growth_exponent_gKMap : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ → ∃ (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) ∧ ∀ u, (∀ k ∈ U, k ∈ GfC V → ∀ g, T₀ u (g * k) = T₀ u g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T₀ u) ≠ ⊤ := by
  first | exact @GlobalTheory.GKUnif.exists_level_exponent | exact GlobalTheory.GKUnif.exists_level_exponent | (intros; apply GlobalTheory.GKUnif.exists_level_exponent <;> assumption)
end
end
