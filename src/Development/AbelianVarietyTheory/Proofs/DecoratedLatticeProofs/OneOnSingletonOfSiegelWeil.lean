module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProof
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowGen1POfConstantsAndPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowGen1POfSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenericTermsPointsAgreeGroupSumsCorankOne
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem genericTerms_points_agree_groupSums_corankOne : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ), (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ) ∧ (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ) ∧ (∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν = grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν) ∧ ((∀ t ∈ (Y.tO u u).genSet, J2of Y u u νL (ptPN t) = 0 → (Y.tO u u).vec t = 0) → PN.AmpInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)) := by
  intro D X Y u νL νB ng
  have hs : (genT (scT (Y.tO u u))).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hs' : (genT (Y.tO u u)).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hA : ∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨cls1 Y u t, nmlOf Y u u t, t, hs ▸ ht, hv, rfl, hp, rfl⟩
  have hB : ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs'] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨clsG Y u t, nmlOf Y u u t, t, hs' ▸ ht, hv, rfl, hp, rfl⟩
  have hG : ∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν =
      grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν := by
    intro c γ ν
    unfold PN.grp grpF
    rw [hs]
    rfl
  refine ⟨fun γ => (hA γ).trans (hB γ).symm, hA, hG, ?_⟩
  intro h
  have hJ : ∀ γ, 0 ≤ J2of Y u u νL γ := fun γ => J2of_nonneg Y u u νL γ
  have hV : ∀ c γ ν, J2of Y u u νL γ = 0 → grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν = 0 := by
    intro c γ ν h0
    unfold grpF
    have hz : ∀ t, ((Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}).indicator
        (Y.tO u u).vec t = 0 := by
      intro t
      by_cases ht : t ∈ (Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}
      · rw [Set.indicator_apply, if_pos ht]
        exact h t ht.1 (by rw [ht.2.2.1]; exact h0)
      · rw [Set.indicator_apply, if_neg ht]
    simp only [hz, tsum_zero]
  refine ⟨fun c γ ν => ?_, hJ, fun c γ ν => ?_⟩
  · show 0 ≤ a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν
    unfold a2F
    exact div_nonneg (by positivity) (hJ γ)
  · rw [hG]
    show ‖grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν‖ ^ 2 ≤
      a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν * J2of Y u u νL γ
    unfold a2F
    by_cases h0 : J2of Y u u νL γ = 0
    · rw [hV c γ ν h0]; simp
    · rw [div_mul_cancel₀ _ h0]

end GlobalTheory.Core.One
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
open Formalism.L2.SG.Pf

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scT_sc_genSet {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) :
    (scT X).sc (scT X).genSet = X.one X.genSet := by
  ext p
  simp only [PB.Terms.one, PB.Terms.sc, PB.Terms.allPairs, Set.mem_setOf_eq]
  exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, trivial⟩⟩

theorem rowGen1P_of_steps (hCh : PN.NGChain) (hC : StepClass1) (hN : StepNormals1) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLoc1) (hTB : GlobalTheory.SnPos.StepThmBGP) : RowGen1P := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨CB, hCB, a₁, b₁, hTB2⟩ := hTB Cg cb Cw cT CT C0 hcb hcT (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, a₂, b₂, hS2⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  obtain ⟨a₃, b₃, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨a₄, b₄, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨a₅, b₅, hH2⟩ := stepHeightG_of_normOne hO Cg cb Cw cT CT C0
  obtain ⟨a₆, b₆, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨a₇, b₇, hT2⟩ := hTi Cg cb Cw cT CT C0
  obtain ⟨a₈, b₈, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨a₉, b₉, hV2⟩ := hV Cg cb Cw cT CT C0
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh meanAmplitudeGeneric_holds C1 C0n (C1 + C0n + 38) CB CSt Cgs CTs
    hCB hCSt hCg hCT le_rfl
  refine ⟨Cn, hCn, max a₀ (max a₁ (max a₂ (max a₃ (max a₄ (max a₅ (max a₆ (max a₇ (max a₈ a₉)))))))),
    max b₀ (max b₁ (max b₂ (max b₃ (max b₄ (max b₅ (max b₆ (max b₇ (max b₈ b₉)))))))),
    fun C' Cl e1 e2 D large₂ X Y u hTies hH0 hSt hT ha => ?_⟩
  simp only [max_le_iff] at e1 e2
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := e1
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := e2
  have hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hH0, hSt, hT⟩
  obtain ⟨hb, X0, ψ, hTie⟩ := hT2 C' Cl p7 q7 D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl p6 q6 D large₂ X Y u u hc hb X0 ψ hTie
  have hBk' : MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) (Irat * kapU D) (Ire * kapU D) :=
    massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨ν, hν⟩ := hE2 C' Cl p8 q8 D large₂ X Y u u hc
  obtain ⟨s, hs1, hs0, hsb, hLe⟩ :=
    hL2 C' Cl p0 q0 D large₂ X Y u hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  have hSum := hTB2 C' Cl p1 q1 D large₂ X Y u hTies hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  generalize bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq = B at hBk' hLe
  have hSz := hS2 C' Cl p2 q2 D large₂ X Y u u hc
  have hrd : 0 < D.host.rdE := by
    obtain ⟨-, -, hrd, -⟩ := hSz
    have hv : 2 * D.host.v = D.host.rdE := by simp only [Formalism.BasicNotions.Host.v]; ring
    rwa [hv] at hrd
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk'
  set ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA * 2 *
      HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ PN.eN D.R.rS *
      nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u : ℕ)) γ with hng
  obtain ⟨hPt, -, -, hAmp⟩ := GlobalTheory.Core.One.genericTerms_points_agree_groupSums_corankOne D X Y u (sc s ν) ν ng
  have hVan : ∀ t ∈ (Y.tO u u).genSet, J2of Y u u (sc s ν) (ptPN t) = 0 → (Y.tO u u).vec t = 0 := by
    intro t ht h0
    obtain ⟨g, hg⟩ := J2of_sc Y u u s ν (ptPN t)
    rw [hg] at h0
    have hp : (0 : ℝ) < (s g : ℝ) ^ 2 := by have := hs0 g; positivity
    exact hV2 C' Cl p9 q9 D large₂ X Y u hc ν hν t ht ((mul_eq_zero.1 h0).resolve_left hp.ne')
  have hIn : GenInputs (scT (Y.tO u u)) (NOf1 Y u (sc s ν) ν ng) D.R.f C1 C0n (C1 + C0n + 38) CB large₂.sc.b
      (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
      (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f))
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) 2 (Ire * kapU D) := by
    refine ⟨hC D X Y u hT _ _ _, hAmp hVan, hN2 C' Cl p3 q3 D large₂ X Y u hc _ _ _, ?_,
      localInputG_of_le _ _ _ _ _ hLe (fun γ => rfl), ?_, ?_, ?_, ?_⟩
    · exact fun γ hγ => hP2 C' Cl p4 q4 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun γ hγ => measureInputG_sc Y u s ν _ hsb ng γ ((hPt γ).1 hγ)
    · exact fun γ _ => ⟨nPt_nonneg _ hrd _ _ γ, le_rfl⟩
    · exact fun γ hγ => hH2 C' Cl p5 q5 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun S hS => hSum (sc s ν) ng S (fun γ hγ => (hPt γ).1 (hS γ hγ))
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (scT (Y.tO u u)) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOf1 Y u (sc s ν) ν ng) _ B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) 2 (Irat * kapU D) (Ire * kapU D)
  rw [hcard] at key
  have r := key ha hG hNI hFI (ngSizes_of hSz hb0 le_rfl zero_le_two le_rfl) hIn
  rw [hdd] at r
  unfold PB.Terms.RowMain at r
  rw [scT_sc_genSet] at r
  exact r

end GlobalTheory.Core.One
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamGen1
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOneOfSameFlagDoubleCoset
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
  Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One

namespace GlobalTheory.Core.OneCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem frame_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ F) a = γ (frame F a) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  induction a using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem Xflag_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) =
    (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem orth_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (x : S.V)
    (hx : x ∈ orth S (Xsp (mapLF γ F))) : γ.symm x ∈ orth S (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro y hy
  have hy' : γ y ∈ Xsp (mapLF γ F) := by
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]; simpa using hy
  have := hx (γ y) hy'
  rw [← hγ y (γ.symm x)]
  simpa using this

end Gen

theorem conj_mem_NRat {D : D7} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : LFlag (D.sp.Y 0) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : n ∈ NRat F) : γ * n * γ⁻¹ ∈ NRat (mapLF γ F) := by
  obtain ⟨hn0, hn1, hn2⟩ := hn
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hn0) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ), ?_, ?_⟩
  · intro j x hx
    rw [Xflag_mapLF γ hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, hn1 j y hy, ?_⟩
    show γ (n y - y) = γ (n (γ.symm (γ y))) - γ y
    simp
  · intro x hx
    have h := hn2 _ (orth_mapLF γ hγ F x hx)
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]
    show γ.symm (γ (n (γ.symm x)) - x) ∈ Xsp F
    simpa using h

theorem corankOne_of_same_flagDoubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      nmlOf Y u u' t = nmlOf Y u u' t' → (Y.tO u u').s0 t t' = 1 := by
  intro D X Y u u' t t' hG hr hn
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hlat : Submodule.IsFullLattice D.host.E t.lam :=
    { toIsLattice := hrow.2.1.1
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular
        (VS D).hT (VS D).herm (VS D).nondeg hrow.2.1.1 hrow.2.1.2.1 }
  have hLF : IsLift t.lam (lf D (X.Fu u)) := hrow.2.1.2.2.1
  have hLt : IsLift t.lam t.frame := t.rep.2.2.2.2.1
  have hLt' : IsLift t'.lam t'.frame := t'.rep.2.2.2.2.1
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]; exact hG
  have hone : ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
    fun F => ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j x _ => by simp, fun x _ => by simp⟩
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hn]; exact ⟨1, hone _, 1, hone _, by simp⟩
  obtain ⟨n, hn1, n', hn2, heq⟩ := hmem
  have hm : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame := conj_mem_NRat t.lin t.rep.2.2.1 _ n' hn2
  have hβ : t'.lin * t.lin⁻¹ = n * (t.lin * n' * t.lin⁻¹) := by rw [heq]; group
  have hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a) := by
    intro a
    unfold GTerm.frame
    rw [frame_mapLF t'.lin t'.rep.2.2.1, frame_mapLF t.lin t.rep.2.2.1, ← hβ]
    show t'.lin _ = t'.lin (t.lin.symm (t.lin _))
    simp
  have hTh := GlobalTheory.DcosetCompl.th_eq_hp D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  rw [← hβ] at hTh
  have hs0 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t'.frame (t'.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF hLt hGv).2 hTh
  show s0T t t' = 1
  unfold s0T
  rw [if_pos ⟨hlam, hlam'⟩]
  exact hs0

end GlobalTheory.Core.OneCoset
end
end

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem famGen1 : CorankOneIsEquivalenceOnRow → FamGen1 := by
  intro hE D X Y u hT
  obtain ⟨hrefl0, hsym, htr⟩ := hE D X Y u u hT
  have hnz : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t ∈ (Y.tO u u).nzSet := fun t ht => ht.1
  have hG : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u).G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  have hrefl : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t ∈ cls1 Y u t :=
    fun t ht => ⟨ht, rfl, hrefl0 t (hnz t ht)⟩
  have hrow : ∀ t t' : TauC Y u u, t' ∈ cls1 Y u t → (Y.tO u u).rowOf t' = (Y.tO u u).rowOf t :=
    fun t t' h => h.2.1
  have hsub : ∀ t ∈ (Y.tO u u).genSet, ∀ t' ∈ (Y.tO u u).genSet,
      (Y.tO u u).rowOf t = (Y.tO u u).rowOf t' → (Y.tO u u).s0 t t' = 1 →
      cls1 Y u t' ⊆ cls1 Y u t := by
    intro t ht t' ht' hr hs x hx
    obtain ⟨hxg, hxr, hxs⟩ := hx
    exact ⟨hxg, hxr.trans hr.symm, htr t (hnz t ht) t' (hnz t' ht') x (hnz x hxg) hr hxr.symm hs hxs⟩
  refine ⟨?_, ?_, ?_⟩
  · ext t
    simp [setQ, Formalism.FourierDecayAlt.PB.Terms.genSet]
  · intro t ht t' ht' hn
    constructor
    · intro he
      have : t' ∈ cls1 Y u t := he ▸ hrefl t' ht'
      exact (hrow t t' this).symm
    · intro hr
      have hs := GlobalTheory.Core.OneCoset.corankOne_of_same_flagDoubleCoset D X Y u u t t' (hG t ht) hr hn
      have hs' := hsym t (hnz t ht) t' (hnz t' ht') hr hs
      exact Set.Subset.antisymm (hsub t' ht' t ht hr.symm hs') (hsub t ht t' ht' hr hs)
  · intro t ht t' ht' he
    have : t' ∈ cls1 Y u t := he ▸ hrefl t' ht'
    exact (hrow t t' this).symm

end GlobalTheory.Core.One
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfGenericCorankOne
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
  Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One

namespace GlobalTheory.Core.One.NormalsProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.NGCut.NormalVectorPairings Formalism.L2.SG.Pf.MainEqNml

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def IsGenericCorankOneTerm (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u) : Prop :=
  t ∈ (Y.tO u u).genSet ∧ (Y.tO u u).vec t ≠ 0 ∧ cls1 Y u t = c ∧ ptPN t = γ

theorem occurs_iff_generic_corank_one (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν ↔ ∃ t, IsGenericCorankOneTerm Y u c γ t ∧ nmlOf Y u u t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    rw [genT_ngSet] at h1
    exact ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    refine ⟨t, ?_, h2, h3, h4, h5⟩
    rw [genT_ngSet]
    exact h1

variable {Y u}

theorem related_of_generic_corank_one (hE : CorankOneIsEquivalenceOnRow) (hT : ConcTie X Y) {c : Set (TauC Y u u)} {γ : PN.Pts D.host.E D.R.rS}
    {t0 t : TauC Y u u} (h0 : IsGenericCorankOneTerm Y u c γ t0) (h : IsGenericCorankOneTerm Y u c γ t) : RelC Y u u t0 t := by
  have hrefl : (Y.tO u u).s0 t t = 1 := (hE D X Y u u hT).1 t h.1.1
  have ht : t ∈ cls1 Y u t := ⟨h.1, rfl, hrefl⟩
  rw [h.2.2.1, ← h0.2.2.1] at ht
  exact ⟨ht.2.1, ht.2.2⟩

theorem isPoint_of_generic_corank_one {νL νB : X.B.I.Ginf → Measure X.B.I.Ginf} {ng : PN.Pts D.host.E D.R.rS → ℝ}
    {c : Set (TauC Y u u)} {γ : PN.Pts D.host.E D.R.rS} {t : TauC Y u u} (h : IsGenericCorankOneTerm Y u c γ t) :
    PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ :=
  ⟨clsG Y u t, nmlOf Y u u t, (occ_iffG Y u νL νB ng _ γ _).2 ⟨t, ⟨h.1, h.2.1, rfl, h.2.2.2⟩, rfl⟩⟩

end GlobalTheory.Core.One.NormalsProof

namespace GlobalTheory.Core.One.NormalsProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.NGCut.NormalVectorPairings Formalism.L2.SG.Pf.MainEqNml Formalism.L2.SG.NGCut.NormalInvariants

def NmlInvOne : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
        (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS),
        (∃ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν) →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ →
        ∃ (J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (m m' : D.host.E)
          (κ : NuC D → D.host.E × D.host.E),
          J ≠ 0 ∧ J' ≠ 0 ∧ m ≠ 0 ∧ m' ≠ 0 ∧
          (∀ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν →
            (κ ν).1 ∈ J ∧ (κ ν).1 * star (κ ν).1 = m ∧ (κ ν).2 ∈ J' ∧ (κ ν).2 * star (κ ν).2 = m') ∧
          (∀ ν₁ ν₂, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν₁ →
            PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν₂ → κ ν₁ = κ ν₂ → ν₁ = ν₂) ∧
          |((Algebra.norm ℚ m : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 2 ∧
          |((Algebra.norm ℚ m' : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 2

theorem nmlInvOne_of (hE : CorankOneIsEquivalenceOnRow) (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : NmlInvOne := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a1, b1, H1⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨a2, b2, H2⟩ := hI Cg cb Cw cT CT C0
  obtain ⟨a3, b3, H3⟩ := hS Cg cb Cw cT CT C0
  refine ⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u hctx νL νB ng c γ hocc hNG => ?_⟩
  have hC1 : a1 ≤ C' := le_trans (le_max_left _ _) hC
  have hC2 : a2 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : a3 ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hl1 : b1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hl2 : b2 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hl3 : b3 ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  have hT : ConcTie X Y := hctx.2.2
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occurs_iff_generic_corank_one Y u νL νB ng c γ ν0).1 hν0
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u := fun ν =>
    if h : ∃ t, IsGenericCorankOneTerm Y u c γ t ∧ nmlOf Y u u t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν →
      IsGenericCorankOneTerm Y u c γ (pick ν) ∧ nmlOf Y u u (pick ν) = ν := by
    intro ν hν
    have h := (occurs_iff_generic_corank_one Y u νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u t0 (pick ν), coefA' Y u u t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (related_of_generic_corank_one hE hT ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (related_of_generic_corank_one hE hT ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (related_of_generic_corank_one hE hT ht0 hp1) (related_of_generic_corank_one hE hT ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end GlobalTheory.Core.One.NormalsProof

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.NGCut.NormalVectorPairings Formalism.L2.SG.Pf.MainEqNml Formalism.L2.SG.NGCut.NormalInvariants GlobalTheory.Core.One.NormalsProof

theorem stepNormals1_of : CorankOneIsEquivalenceOnRow → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt →
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep → Formalism.L2.SG.NGCut.NormalInvariants.NormCount → StepNormOneG → StepNormals1 := by
  intro hE hL hI hS hB hO
  have hA := nmlInvOne_of hE hL hI hS
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0
  obtain ⟨o₀, p₀, hO2⟩ := hO Cg cb Cw cT CT C0
  refine ⟨max a₀ o₀, max b₀ p₀, fun C' Cl h1 h2 D large₂ X Y u hc νL νB ng => ?_⟩
  intro cl γ S hS
  have hrd := rd_one_le D
  have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
  have hstand := hc.2.1
  show (S.card : ℝ) ≤ ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
    (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f)) *
    NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6
  have eR : (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
      (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f)) *
      ((((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ) ^ 6 =
      (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6 := by
    have hR := rd_cancel D
    calc _ = (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
          (((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) ^ 6) *
          ((((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6) := by
          ring
      _ = _ := by rw [hR, one_mul]
  rw [hv, ngPt_eq, eR]
  have hT1 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.1
  have hT2 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.2.1
  rcases S.eq_empty_or_nonempty with hSe | ⟨ν0, hν0⟩
  · rw [hSe]
    simp only [Finset.card_empty, Nat.cast_zero]
    refine mul_nonneg (pow_nonneg (by nlinarith) _) ?_
    rw [show PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6 = (PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 3) ^ 2 by ring]
    exact sq_nonneg _
  have hocc : ∃ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) cl γ ν := ⟨ν0, hS ν0 hν0⟩
  obtain ⟨t0, ht0, -⟩ := (occurs_iff_generic_corank_one Y u νL νB ng cl γ ν0).1 (hS ν0 hν0)
  have hIsPt : PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ := isPoint_of_generic_corank_one ht0
  have hNG0 := (hO2 C' Cl (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2) D large₂ X Y u hc
    νL νB ng γ hIsPt).1
  obtain ⟨J, J', m, m', κ, hJ, hJ', hm, hm', hmem, hinj, hN, hN'⟩ :=
    hA2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u hc νL νB ng cl γ hocc hNG0
  have hNG := hNG0
  rw [ngPt_eq] at hNG
  have hP1 : 1 ≤ PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ := by
    have hX : 1 ≤ (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := one_le_pow₀ (one_le_pow₀ hrd)
    have hpos : 0 < (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := lt_of_lt_of_le one_pos hX
    rw [inv_mul_eq_div, le_div_iff₀ hpos, one_mul] at hNG
    linarith
  let T1 := S.image (fun ν => (κ ν).1)
  let T2 := S.image (fun ν => (κ ν).2)
  have hcard : S.card ≤ T1.card * T2.card := by
    calc S.card = (S.image κ).card :=
          (Finset.card_image_of_injOn fun a ha b hb h => hinj a b (hS a ha) (hS b hb) h).symm
      _ ≤ (T1 ×ˢ T2).card := Finset.card_le_card (by
          intro p hp
          obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
          exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hν, Finset.mem_image_of_mem _ hν⟩)
      _ = T1.card * T2.card := Finset.card_product _ _
  have hB1 := hB D J m hJ hm T1 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).1, (hmem ν (hS ν hν)).2.1⟩)
  have hB2 := hB D J' m' hJ' hm' T2 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).2.2.1, (hmem ν (hS ν hν)).2.2.2⟩)
  have hJp : 0 < ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J) (Ne.symm h0)
    exact_mod_cast this
  have hJp' : 0 < ((FractionalIdeal.absNorm J' : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J' ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J') (Ne.symm h0)
    exact_mod_cast this
  generalize PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ = P at hN hN' hP1 ⊢
  generalize ((Tu D u : ℕ) : ℝ) = T at hN hN' hT1 hT2 ⊢
  generalize ((FractionalIdeal.absNorm J : ℚ) : ℝ) = nJ at hB1 hN hJp
  generalize ((FractionalIdeal.absNorm J' : ℚ) : ℝ) = nJ' at hB2 hN' hJp'
  generalize |((Algebra.norm ℚ m : ℚ) : ℝ)| = nm at hB1 hN
  generalize |((Algebra.norm ℚ m' : ℚ) : ℝ)| = nm' at hB2 hN'
  have hc1 : (T1.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB1.trans (mul_le_mul_of_nonneg_left hN (by positivity))
    have h' : (T1.card : ℝ) * nJ ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  have hc2 : (T2.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB2.trans (mul_le_mul_of_nonneg_left hN' (by positivity))
    have h' : (T2.card : ℝ) * nJ' ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ' ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  calc (S.card : ℝ) ≤ (T1.card : ℝ) * T2.card := by exact_mod_cast hcard
    _ ≤ _ := count_bound D.R.f T T P _ _ hT1 hT2 hP1 hc1 hc2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end GlobalTheory.Core.One
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLoc1OfFam
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem stepLoc1_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFam1) : StepLoc1 := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
    Ire hBk ν hν
  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := by
    obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH
    dsimp only at hH
    obtain ⟨-, -, h3, h4, -⟩ := hH
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
    omega
  have hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS ((39 : ℕ) : ℝ) := by
    have := hQ5 D hk4
    exact_mod_cast this
  exact ⟨s, hs1, hs0, hsb, localLeG_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩

end GlobalTheory.Core.One
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpQNotEqAmpG
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem ampQ_not_eq_ampG {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ Not L = ampG L := by
  funext d
  unfold ampQ ampG
  rw [Finset.sum_eq_single_of_mem ∅ (by simp) (fun A hA h => absurd (by simp at hA; exact hA.2) h)]
  simp

private theorem hasPt_of_isPt {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS)
    (h : PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ) : HasPt Y u u (Y.tO u u).genSet γ := by
  obtain ⟨c, n, t, ht, hv, -, hp, -⟩ := h
  rw [genT_ngSet] at ht
  exact ⟨t, ht, hv, hp⟩

theorem stepFam1_of : (∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) → Formalism.L2.SG.FamDefs.HTie → FamGen1 → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam → StepFam1 := by
  intro hG6 hH hF hG5 hW hG4 hE Cg cb Cw cT CT C0
  obtain ⟨CSt, hCSt, a4, b4, h4⟩ := hG4 Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH2⟩ := hH Cg cb Cw cT CT C0
  obtain ⟨a5, b5, h5⟩ := hG5 Cg cb Cw cT CT C0
  obtain ⟨aW, bW, hW2⟩ := hW Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE2⟩ := hE Cg cb Cw cT CT C0
  refine ⟨9, CSt, hCSt, max a4 (max aH (max a5 (max aW aE))), max b4 (max bH (max b5 (max bW bE))),
    fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν => ?_⟩
  simp only [max_le_iff] at e1 e2
  obtain ⟨e1a, e1b, e1c, e1d, e1e⟩ := e1
  obtain ⟨e2a, e2b, e2c, e2d, e2e⟩ := e2
  have hQ := hF D X Y u hc.2.2
  obtain ⟨s, hs1, hs0, hsb, htie⟩ :=
    h4 C' Cl e1a e2a D large₂ X Y u u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  refine ⟨s, hs1, hs0, hsb, fun γ hγ S => ?_⟩
  have hP := hasPt_of_isPt Y u _ _ _ γ hγ
  obtain ⟨Fm, hFT, hRel, hTerm, hDs, hrw⟩ := hE2 C' Cl e1e e2e D large₂ X Y u u hc _ _ _ _ hQ γ hP
  have hG5Fm := Formalism.L2.SG.FamDefs.orbitFamilyIdentity_at_volume hFT (h5 C' Cl e1c e2c D large₂ X Y u u hc _ _ _ _ hQ γ hP Fm hFT)
  obtain ⟨hWpos, hWle⟩ := hW2 C' Cl e1d e2d D large₂ X Y u u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk
    _ _ _ _ hQ γ hP Fm hFT hRel hTerm hG5Fm
  refine ⟨Fm, Formalism.L2.SG.FamDefs.famOKS_of (NOf1 Y u (sc s ν) ν (fun _ => 0)) γ S _ (fun L => ampG L) Fm hFT
    hRel hTerm hDs hrw (hG6 D (Formalism.L2.SG.FamDefs.four_rank_add_seven_le_k hc)) hG5Fm
    (hH2 C' Cl e1b e2b D large₂ X Y u u hc _ _ _ γ Fm hFT) hWpos hWle (fun x _ => ?_)⟩
  have h := htie _ _ _ _ hQ γ hP Fm hFT x.1 x.2
  rw [ampQ_not_eq_ampG] at h
  exact h

end GlobalTheory.Core.One
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepClass1Of
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem stepClass1_of (h : CorankOneIsEquivalenceOnRow) : StepClass1 := by
  intro D X Y u hc νL νB ng
  obtain ⟨hR, hS, hT⟩ := h D X Y u u hc
  have hsub : ∀ t ∈ (Y.tO u u).genSet, t ∈ (Y.tO u u).nzSet := fun t ht => ht.1
  intro t ht t' ht'
  rw [genT_ngSet] at ht ht'
  change t ∈ (Y.tO u u).genSet at ht
  change t' ∈ (Y.tO u u).genSet at ht'
  have es : (genT (scT (Y.tO u u))).s0 t t' = 1 ↔ (Y.tO u u).s0 t t' = 1 := by
    simp only [genT, scT, and_true]
    by_cases hc : (Y.tO u u).s0 t t' = 1
    · simp [hc]
    · simp [hc]
  show ((scT (Y.tO u u)).rowOf t = (scT (Y.tO u u)).rowOf t' ∧ (genT (scT (Y.tO u u))).s0 t t' = 1) ↔
    cls1 Y u t = cls1 Y u t'
  rw [es]
  change ((Y.tO u u).rowOf t = (Y.tO u u).rowOf t' ∧ (Y.tO u u).s0 t t' = 1) ↔ cls1 Y u t = cls1 Y u t'
  constructor
  · rintro ⟨hr, h1⟩
    have b1 := hS t (hsub t ht) t' (hsub t' ht') hr h1
    ext x
    simp only [cls1, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr, hT t' (hsub t' ht') t (hsub t ht) x (hsub x hx) hr.symm hrx.symm b1 hx1⟩
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr.symm, hT t (hsub t ht) t' (hsub t' ht') x (hsub x hx) hr hrx.symm h1 hx1⟩
  · intro hc
    have hm : t' ∈ cls1 Y u t' := ⟨ht', rfl, hR t' (hsub t' ht')⟩
    rw [← hc] at hm
    exact ⟨hm.2.1.symm, hm.2.2⟩

end GlobalTheory.Core.One
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOneIsEquivalenceNonzeroGramTerms
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One


open Formalism.L2.SG.NGCut.CorankRelation in
theorem corankOne_isEquivalence_nonzeroGram_terms : CorankOneIsEquivalenceOnRow := by
  intro D X Y u u' _hT
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t ∈ (Y.tO u u').nzSet, Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro t ht h
    apply ht
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]
  have hlat : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      Submodule.IsFullLattice D.host.E t.lam := fun t => ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      IsLift t.lam (lf D (X.Fu u)) := fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), IsLift t.lam t.frame :=
    fun t => t.rep.2.2.2.2.1
  refine ⟨fun t ht => ?_, fun t ht t' ht' hr h1 => ?_, fun t ht t' ht' t'' ht'' hr1 hr2 h1 h2 => ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨rfl, rfl⟩, mul_inv_cancel]
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t.frame 1 (hLF t) (hLt t) (hGv t ht)).2
      (Th_one _ _ _)
  · have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' ⊢
    rw [if_pos ⟨hlam, hlam'⟩] at h1'
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    have hth := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
    have hsym := Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
      (hGv t ht) (hGv t' ht') (frame_mem_iff t t') hth
    have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
    rw [hinv] at hsym
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' ht')).2 hsym
  · have hl1 : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl1' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl2 : t'.lam = t''.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have hl2' : t'.lam' = t''.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    have h2' : Formalism.L2.SG.TermOp.s0T t' t'' = 1 := h2
    show Formalism.L2.SG.TermOp.s0T t t'' = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' h2' ⊢
    rw [if_pos ⟨hl1, hl1'⟩] at h1'
    rw [if_pos ⟨hl2, hl2'⟩, ← hl1] at h2'
    rw [if_pos ⟨hl1.trans hl2, hl1'.trans hl2'⟩]
    have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
    have hth1 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hth2 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t''.frame _ (hLF t) hL'
      (hGv t' ht')).1 h2'
    have htr := Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹) (t''.lin * t'.lin⁻¹)
      (fun x hx => (frame_mem_iff t' t'' x).1 hx) hth1 hth2
    have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
    rw [hmul] at htr
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t''.frame _ (hLF t) (hLt t) (hGv t ht)).2 htr

end GlobalTheory.Core.One
end

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem rowGen1P_of_siegelWeil_of_points : PI.VolStabS.MassDataS.SWXS → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine →
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep → StepPointsG → StepNormOneG → TieOfCtx →
    StepChoiceConstantsC → StepPinExists → GlobalTheory.SnPos.StepThmBGP → RowGen1P := by
  intro hSW hLine hInt hSep hPts hN1 hTie hCh hPin hThm
  have hEq : CorankOneIsEquivalenceOnRow := corankOne_isEquivalence_nonzeroGram_terms
  have hFam : FamGen1 := famGen1 hEq
  have hStepFam : StepFam1 :=
    stepFam1_of (fun D hk F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP R d0 h0 d t ht Y0 hZ =>
      GlobalTheory.mass_pairingClass_bounds M hM H D.R.rS D.R.k P hk hV hP R d0 h0 d t ht Y0 _ rfl hZ _ rfl) GlobalTheory.HTieLeaf.main hFam
      GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof (GlobalTheory.WeightsFamPf.weightsFam_of hSW) GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude GlobalTheory.SnFam.existFam
  have hLoc : StepLoc1 :=
    stepLoc1_of_fam (fun D => ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1) hStepFam
  have hNml : StepNormals1 :=
    GlobalTheory.Core.One.stepNormals1_of hEq hLine hInt hSep Formalism.L2.SG.NGCut.NormalCount.NormCount_holds hN1
  have hVan : StepTermVanishG :=
    Formalism.L2.SG.Pf.MainEqVanish.stepTermVanishG_of_form (Formalism.L2.SG.Pf.formGC_of_rel Formalism.L2.SG.Pf.formRelC_holds)
  exact rowGen1P_of_steps Formalism.FourierDecayAlt.P.norm_chain (stepClass1_of hEq) hNml hPts hN1 hTie hCh hPin hVan hLoc hThm

end GlobalTheory.Core.One
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalCountLineIntegralitySeparation
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalCountLineIntegralitySeparation
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem normalCountSteps : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep :=
  ⟨Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine_holds, Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds,
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep_holds⟩

end GlobalTheory.Core.One
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalCountLineIntegralitySeparationStatement
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalCount_line_integrality_separation : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep := by
  first | exact @GlobalTheory.Core.One.normalCountSteps | exact GlobalTheory.Core.One.normalCountSteps | (intros; apply GlobalTheory.Core.One.normalCountSteps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneOnSingletonOfRows
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Diag

theorem mR_eq_m (D : D7) : Formalism.L2.SG.RowsConc.mR D = (D.R.m : ℝ) := by
  have h : 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  unfold Formalism.L2.SG.RowsConc.mR
  rw [h]

theorem log_b_eq (D : D7) (large₂ : SizeData₂ D) : Real.log large₂.sc.b = large₂.sc.L := by
  unfold Formalism.BasicNotions.Scale.b
  exact Real.log_exp _

theorem gamB_eq_gamL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : gamB D large₂ C = gamL D large₂.sc.L C := by
  unfold gamB gamL
  rw [mR_eq_m, log_b_eq]

theorem epsNG_le_gamL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : epsNG D large₂ C ≤ gamL D large₂.sc.L C := by
  unfold epsNG
  have h1 : ((2 : ℝ) ^ (D.R.k - 2 * D.R.rS - 5))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : Real.exp (C * Formalism.L2.SG.RowsConc.mR D ^ 5 * D.R.f * Real.log large₂.sc.b) = gamL D large₂.sc.L C := by
    unfold gamL
    rw [mR_eq_m, log_b_eq]
  rw [h2]
  exact mul_le_of_le_one_left (Real.exp_pos _).le h1

theorem oneOn_singleton_of_rows :
    (RowGen1P → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true) ∧ (GlobalTheory.NGRow.RowNGP → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} false) := by
  constructor
  · intro hG c Cg cb Cu cT CT hcb hcT
    obtain ⟨CB, hCB, C'₀, Cl₀, H⟩ := hG Cg cb Cu cT CT c hcb hcT
    refine ⟨CB, hCB, max (max C'₀ Cl₀) 3, ?_⟩
    intro C0 hC0 C' Cl h1 h2 D large₂ X Y u hT hH hC ha
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    have a1 : C'₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    have b1 : Cl₀ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have b3 : (2 : ℝ) < Cl := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h2)
    have hs : Formalism.MainNotions.S.Cnt.Stand D u u := Formalism.MainNotions.Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hH.2.1 hH.1 b3 u u
    have r := H C' Cl a1 b1 D large₂ X Y u hT hH hs hC ha
    unfold GeneratorBoundAt at r
    rw [gamB_eq_gamL] at r
    rw [if_pos rfl]
    exact r
  · intro hN c Cg cb Cu cT CT hcb hcT
    obtain ⟨C4, hC4, C'₀, Cl₀, H⟩ := hN Cg cb Cu cT CT c hcb hcT
    refine ⟨C4, hC4, max (max C'₀ Cl₀) 3, ?_⟩
    intro C0 hC0 C' Cl h1 h2 D large₂ X Y u hT hH hC ha
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    have a1 : C'₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    have b1 : Cl₀ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have b3 : (2 : ℝ) < Cl := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h2)
    have hs : Formalism.MainNotions.S.Cnt.Stand D u u := Formalism.MainNotions.Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hH.2.1 hH.1 b3 u u
    have r : (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).ngSet) ≤ epsNG D large₂ C4 * ddC X Y u u :=
      H C' Cl a1 b1 D large₂ X Y u u hT hH hs hC ha
    rw [if_neg Bool.false_ne_true]
    exact r.trans (mul_le_mul_of_nonneg_right (epsNG_le_gamL D large₂ C4) (Formalism.L2.SG.RowsConc.dd_nonneg hC u u))

end GlobalTheory.Core.Diag
end
end

namespace GlobalTheory.Core.Diag

theorem oneOn_singleton_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.Pf.BDat.StepThmBG → Formalism.L2.SG.RowsPos.RowNGP →
      ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false := by
  intro h hB hTB hN c
  have hT : GlobalTheory.SnPos.StepThmBGP := by
    intro Cg cb Cw cT CT C0 _ _ A
    obtain ⟨CB, h0, a, b, H⟩ := hTB Cg cb Cw cT CT C0 A
    exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u _ => H C' Cl h1 h2 D large₂ X Y u⟩
  obtain ⟨_h1, _h2, h3, h4, h5, h6, _h7, _h8, _h9⟩ := GlobalTheory.T.equalWords_nonGeneric_estimates_chain
  have hG : GlobalTheory.Core.One.RowGen1P :=
    GlobalTheory.Core.One.rowGen1P_of_siegelWeil_of_points (GlobalTheory.St.swxs_of_siegelWeil h)
      GlobalTheory.T.normalCount_line_integrality_separation.1 GlobalTheory.T.normalCount_line_integrality_separation.2.1 GlobalTheory.T.normalCount_line_integrality_separation.2.2 h3 h4 h5 hB h6 hT
  exact ⟨oneOn_singleton_of_rows.1 hG c, oneOn_singleton_of_rows.2 hN c⟩

end GlobalTheory.Core.Diag
