module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleJOfRestricted
public import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.RBDGam

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure RecTAlt (ex : Extra D L hT Gi Gl K Y cX) where
  T : _root_.Formalism.L2.TiedDataSKAlt ex
  pin : _root_.Formalism.L2.Rows.RowPinMinAlt T
  joints : _root_.Formalism.L2.JointsSAlt T.toTiedDataS
  host : _root_.Formalism.L2.HostDatumSelfDual T.toTiedDataS
  weq : Theta.WeilCompatibleEquivariance T.toTiedDataS.theta.W
def ExtraDataRecursive (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (_root_.Formalism.L2.RecTAlt ex)
theorem ExtraDataRecursive.tiedSK {ex : Extra D L hT Gi Gl K Y cX} (h : _root_.Formalism.L2.ExtraDataRecursive ex) : _root_.Formalism.L2.ExtraDataSelfDualKernel ex :=
  let ⟨R⟩ := h; ⟨R.T⟩
end
def SecondLayerFamilyClass : FamClass := fun {_} Fm =>
  (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataRecursive (Fm.ex x hx i)) ∧ _root_.Formalism.L2.LinkedFamiliesAligned' Fm
theorem SecondLayerFamilyClass.c2sk {eps : ℝ} {Fm : FamP eps} (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : _root_.Formalism.L2.LinkedFamiliesKernelFrame' Fm := by
  obtain ⟨⟨x0, h⟩, _⟩ := h
  exact ⟨x0, fun x hx hx0 i => (h x hx hx0 i).tiedSK⟩
theorem SecondLayerFamilyClass.c2s {eps : ℝ} {Fm : FamP eps} (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : _root_.Formalism.L2.SecondChernLinkedClass Fm := h.c2sk.c2s
theorem group_compatibility_of_second_layer_family {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : G.GroupCompatibilityFamily Fm := _root_.Formalism.L2.gTiedF_of_C2S_alt Fm h.c2s
end Formalism.L2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StmtJHolds
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpLemmaAOfAdmissible
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Classical
variable {D : D7}
theorem jumpLemma_a_of_admissible_alt_alt {L : SizeData₂ D} (hP : AdmPar L) (hG2 : _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D) (hCr : CrysIffWD D.nd D.naut)
    (hG2g : _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D) (hDi : AdmDict D) (hRd : AdmRead D) : ConclusionJa D := by
  obtain ⟨ep, hdict⟩ := hDi
  refine ⟨ep, ?_⟩
  intro i r hr w hw C τ
  obtain ⟨hInd, ⟨g, hg⟩, hread⟩ := hRd i r hr w hw C τ
  obtain ⟨ρ, hρ⟩ := exists_placeOf (D := D) g
  have hRA : ReadAt D i (gEmb C τ) g ρ := ⟨hg, hρ⟩
  obtain ⟨sg, cτ, hsU, hsD, hJ0, hchi⟩ := hdict i (gEmb C τ) g ρ hRA
  obtain ⟨hχdR, hχJ⟩ := hchi w hInd
  rw [Multiset.map_eq_singleton] at hχJ
  obtain ⟨c, hc, hcq⟩ := hχJ
  have hjr := D.nd.j_range i
  have hF := jFacts_of hP (D.nd.j i) hjr.1 hjr.2 ρ
  set up := decide (TypeU D ep g) with hup
  have hsU' : up = true → sg = 1 := fun h => hsU (by simpa [hup] using h)
  have hsD' : up = false → sg = -1 := fun h => hsD (by simpa [hup] using h)
  have hx : ∀ x, D.naut.IsdRW i (rQ D i r x) w ∧
      D.naut.jumpsW i (rQ D i r x) (gEmb C τ) = D.naut.locAutHodgeTateWeightsLevelZero i (gEmb C τ) := by
    intro x
    by_cases hl : D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1
    · have h := _root_.UpperTheory.GalS.g2g' hG2g i r hr hl w hw x
      exact ⟨h.1, h.2 _ hInd⟩
    · push Not at hl
      have h := _root_.UpperTheory.GalS.g2a' (hG2 i r hr) w hw hl.1 hl.2 x
      have hcont := SumRepresentations.contQ_of_continuous D.nd D.naut i (r x) (hr x).1
      exact ⟨((hCr i _ _ w hw hcont).1 h.1).1, h.2 _ hInd⟩
  have hkey : ∀ a : ℤ, (((D.naut.locAutHodgeTateWeightsLevelZero i (gEmb C τ)).count (a + c) : ℕ) : ℤ) =
      if (a : ℚ) ∈ JJ D up (D.nd.j i) ρ then 1 else 0 :=
    count_key hF _ sg cτ c up hsU' hsD' hJ0 hcq
  have hTw : ∀ x (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
      if (a : ℚ) ∈ JJ D up (D.nd.j i) ρ then 1 else 0 := by
    intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    rw [(h1 a).1, (hx x).2, hkey]
  have hDu : ∀ x (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
      if (a : ℚ) ∈ dualS (JJ D up (D.nd.j i) ρ) then 1 else 0 := by
    intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    rw [(h1 a).2, (hx x).2, dualS_int, ← hkey]
    congr 3; ring
  refine ⟨g, ρ, hRA, ?_, ?_⟩
  · intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    refine ⟨?_, hTw x a, ?_, hDu x a⟩
    · rw [h2 _ (Or.inl rfl) a, hTw x a]; exact ite_ne_zero_iff' _
    · rw [h2 _ (Or.inr rfl) a, hDu x a]; exact ite_ne_zero_iff' _
  · intro ρπ π hπ hdec a
    obtain ⟨h1, h2, h3⟩ := hread π (hx π).1 hχdR c hc
    have hW : ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a =
        if (a : ℚ) ∈ JW D up (D.nd.j i) ρ then 1 else 0 := by
      intro a
      rw [(h3 ρπ hπ hdec a).1, hTw π a]
      by_cases hb : (a : ℚ) ∈ blockJ D
      · have hb' := (block_mem_iff (D := D) a).1 hb
        rw [if_pos (block_sub_JJ up _ ρ _ hb), if_pos hb', if_neg (block_not_mem_JW hF up _ hb)]
        simp
      · have hb' : ¬ (0 ≤ a ∧ a < (D.R.t : ℤ)) := fun h => hb ((block_mem_iff a).2 h)
        rw [if_neg hb', sub_zero]
        simp only [JJ_iff_JW hF up _ hb]
    have hT : ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a =
        if (a : ℚ) ∈ dualS (JW D up (D.nd.j i) ρ) then 1 else 0 := by
      intro a
      rw [(h3 ρπ hπ hdec a).2.1, hW, dualS_int]
    refine ⟨?_, hW a, ?_, hT a⟩
    · rw [(h3 ρπ hπ hdec a).2.2.1, hW a]; exact ite_ne_zero_iff' _
    · rw [(h3 ρπ hπ hdec a).2.2.2, hT a]; exact ite_ne_zero_iff' _
end GlobalTheory.JumpSets
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section HC
variable {R : Ranks} (P : HCParam R)
end HC
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section JB
variable {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau}
end JB
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section Core
variable {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau}
end Core
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Classical
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
theorem stmtJ_holds_alt (D : D7) : @_root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D := by
  intro L hA
  obtain ⟨hG2, hCr, hG2g, hDi, hRd, hP⟩ := hA
  have hF : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ := fun j h1 h2 ρ => jFacts_of hP j h1 h2 ρ
  have hpar : L.etaSz + D.R.t + L.Sc ≤ L.sc.b := by
    have := L.Sc_pos; have := L.etaSz_pos
    have : (0 : ℝ) ≤ D.R.t := by positivity
    linarith [hP.1, hP.2.1]
  exact ⟨_root_.GlobalTheory.JumpSets.jumpLemma_a_of_admissible_alt_alt hP hG2 hCr hG2g hDi hRd, jumpSetBound_of_realPlaceFacts hF, jumpSetCloud_of_realPlaceFacts hF, jumpSetDistinct_of_realPlaceFacts hF,
    jumpSetEta_of_realPlaceFacts hF hpar D.R.t_odd.pos L.Sc_pos L.etaSz_pos, jumpSetFinal_of_realPlaceFacts hF, jumpSetGap_of_realPlaceFacts hF⟩
end GlobalTheory.JumpSets
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.JumpStatement
theorem holds_all_alt : ∀ D : D7, @_root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D := _root_.GlobalTheory.JumpSets.stmtJ_holds_alt
end GlobalTheory.JumpStatement
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAllStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jump_closed_forall_d7 : ∀ D : D7, @_root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D := by
  first | exact @_root_.GlobalTheory.JumpStatement.holds_all_alt | exact _root_.GlobalTheory.JumpStatement.holds_all_alt | (intros; apply _root_.GlobalTheory.JumpStatement.holds_all_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GammaSizeOfParameters
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions
noncomputable section
namespace Formalism.L2.DIV.Cons
open Formalism.L2.DIV Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
theorem gamma_size_of_sizeData_alt {Tk : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (hR : _root_.Formalism.L2.Rows.RowSideDeterminedAlt Tk P) (hTf : Finite P.T) (hSG : SizeG L)
    (hSC : SizeCond L) (Del h0 : ℕ) (Nc : ℝ) (hNc : 0 ≤ Nc) (C : ℝ) (hC : 0 ≤ C) (hF : FactDGam D C) :
    DGamSize P.A3.A P.P0 P.ψ0 (ofRecord D L Del h0) Nc hTf 1 (2 + 9 * C) :=
  dGamSize_record_one P.A3.A P.P0 P.ψ0 hTf L hSG hSC Del h0 Nc hNc P.tied.div.grp.card D.u₀ hR.gamDvd.2 C hC hF
end Formalism.L2.DIV.Cons
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamPointsWeightJumps
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal
noncomputable section
namespace UpperTheory.GalS
theorem de_rham_points_weight_jumps_alt (D : D7) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h2' : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D)
    (hC : UpperTheory.GalC.CutRec D) : (∀ i r, GoodR D.nd i r → G2a D.nd D.naut i r) ∧ DeRhamJumpsDistinctCondition D := by
  have h2 := _root_.UpperTheory.GalS.weak' h2'
  have all : ∀ i r, GoodR D.nd i r → ∀ x, ∀ w ∈ placesOver D.host.E (D.nd.l i),
      D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
    intro i r hr x w hw
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hB⟩ := h1 i P
    have hn : Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) := by
      have hg : ∀ k, D.nd.l i = D.host.g k → Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) := fun k hk => by
        have hw' : w ∈ placesOver D.host.E (D.host.g k) := hk ▸ hw
        rw [hB.2.2.2.1 w (GlobalTheory.DepthZeroType.isSplitPl_of_over D k w hw')]
        exact hC i P (by rw [hP]; simp) k w hw'
      by_cases a : D.nd.l i = D.host.g 0
      · exact hg 0 a
      by_cases b : D.nd.l i = D.host.g 1
      · exact hg 1 b
      exact .of_unr (Parts.iso_unr_l D i P Pa w hB hw a b)
    have h := compatR D h0 h2 h5 i r hr x P Pa hP hB w hw hn
    exact ⟨h.1, h.2.2⟩
  exact ⟨fun i r hr => (Parts.crys_unram_of_lgc D h0 h1 (Parts.lgc D h0 h2 h5) i r fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hr x)).1,
    fun i r hr _ w hw x => all i r hr x w hw, fun i r hr => Parts.constituentCondition_of_hodgeJumps D h0 i r hr (all i r hr)⟩
end UpperTheory.GalS
end
end
end
