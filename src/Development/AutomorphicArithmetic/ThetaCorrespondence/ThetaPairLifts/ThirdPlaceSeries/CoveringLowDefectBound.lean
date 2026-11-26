module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuLowerBoundLastIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDimensionLogBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelIsWhit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefCaseCore
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefCaseCore
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefCore
theorem defCase_core_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → DefCase (p.T.U ((i : ℕ) + 1)) (xiR D) ∧ Finite (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ Nonempty (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ (∀ σ, GoodEmb p.T.Q.c σ → ∀ g, (p.T.dict ((i : ℕ) + 1) σ g).2 ∈ ((p.T.U ((i : ℕ) + 1) σ).X (p.T.dict ((i : ℕ) + 1) σ g).1).dom) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M _ hm _ hW _ hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  obtain ⟨hp, hq, hr⟩ := hW.sig
  have hk := D.R.m_add_three_le_k
  have hq0 : (p.T.Q.Dw ((i : ℕ) + 1)).q = 0 := by
    have : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [hq]; rfl
    simpa [dat, hm] using this
  have hp1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p := by
    have : (dat p i).p = D.R.k + ((i : ℕ) + 1) - 1 := by rw [hp]; rfl
    simp only [dat] at this
    omega
  refine ⟨⟨hq0, hp1, ?_, hJ.pins.2.1.2, hF, hJ.unf _ hj, ?_⟩, CompFin.finite_comp _ _, ?_, ?_⟩
  · exact goodAt_of_two_primes hJ.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  · exact (GlobalTheory.LevGeo.laws_core D p.T _ hJ hj).xiAbs
  · exact (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ _ _ (by omega)).1
  · intro σ hσ g
    exact GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.dict_mem_dom p.T hJ _ hj σ hσ g
end GlobalTheory.DefCore
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefCaseCoreStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → DefCase (p.T.U ((i : ℕ) + 1)) (xiR D) ∧ Finite (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ Nonempty (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ (∀ σ, GoodEmb p.T.Q.c σ → ∀ g, (p.T.dict ((i : ℕ) + 1) σ g).2 ∈ ((p.T.U ((i : ℕ) + 1) σ).X (p.T.dict ((i : ℕ) + 1) σ g).1).dom) := by
  first | exact @_root_.GlobalTheory.DefCore.defCase_core_alt | exact _root_.GlobalTheory.DefCore.defCase_core_alt | (intros; apply _root_.GlobalTheory.DefCore.defCase_core_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefectBoundOfConnected
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigSlopeLe
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeBase
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqOneOfLevCong
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqOneOfLevCong
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseLevelInj
open Formalism.BasicNotions.TH _root_.Formalism.L2.Theta Formalism.IndefR
end GlobalTheory.BaseLevelInj
set_option maxHeartbeats 1000000 in
open GlobalTheory.BaseLevelInj in
theorem GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ g : (p.F.lv2.lvl false).P, (∀ x : (p.T.Q.Dw ((i : ℕ) + 1)).La, (p.O i).lev (g : p.P.Gp) x - x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) → g = 1 := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF g hg
  obtain ⟨κ, hlift, happ⟩ := (p.pins i).2.lift.lev (g : p.P.Gp)
  have hβ := p.charW.base.lev.βW i
  have hSt := Formalism.L2.DIV.parLev_St hlift.2.1
  have hfc := GlobalTheory.LevelAction.finCong_of_mem_St hβ hSt
  have hι := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hMb : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb := by
    have h0 : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := Ideal.mem_span_singleton_self _
    rw [← p.T.Q.l.prod] at h0
    exact (Ideal.mul_le_inf.trans inf_le_left : p.T.Q.l.Mb * _ ≤ p.T.Q.l.Mb) h0
  have h4 := GlobalTheory.T.levelMove_lift_congruent_mod_ideal (Wc D i) (iotaW p.T i) hι p.T.Q.l.M p.T.Q.l.Mb (Mfr p.T.Q.l) p.T.Q.l.coprime hMb κ hfc
    ((p.O i).lev (g : p.P.Gp)) happ hg
  have h3 := GlobalTheory.T.adelicCongruence_selfDual_of_principalLattice (Wc D i) _ _ h4
  rw [← GlobalTheory.PrincInLevel.eq_latC hβ] at h3
  have h2 := hatL_cong_of_hat (Wc D i) κ _ _ h3
  have hfr : Formalism.L2.DIV.IsFrame (p.R.βW i) (p.R.ΛW i) := by obtain ⟨c, h, -⟩ := hβ; exact h
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hred : ∀ PP ∈ p.R.Pg, Formalism.L2.DIV.redFn (p.R.βW i) PP (Formalism.IndefR.Lev.finE (Wc D i) κ) = 1 := by
    intro PP hP
    refine GlobalTheory.T.frameReduction_eq_one_of_congruent_mod_ideal _ _ _ hfr hSt _ h2 PP ?_
    rw [hhalf]
    exact Ideal.prod_le_inf.trans (Finset.inf_le hP)
  have hT1 : Formalism.L2.DIV.rTup (p.R.βW i) (p.R.datWp i p.R.triv) (Formalism.IndefR.Lev.finE (Wc D i) κ) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (p.R.βW i) PP.1 _) = 1
    rw [hred PP.1 PP.2]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  have he : p.R.eG (g : p.P.Gp) = 1 := by rw [← hlift.2.2]; exact hT1
  have : (g : p.P.Gp) = 1 := by rw [← map_one p.R.eG] at he; exact p.R.eG.injective he
  exact Subtype.ext this
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqOneOfLevCongStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_lev_sub_mem_Mb_gram : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ g : (p.F.lv2.lvl false).P, (∀ x : (p.T.Q.Dw ((i : ℕ) + 1)).La, (p.O i).lev (g : p.P.Gp) x - x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) → g = 1 := by
  first | exact @_root_.GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb | exact _root_.GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb | (intros; apply _root_.GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnipModHalf
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnipModHalf
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.LevelUnip
section Res
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
end Res
variable {D : D7}
end GlobalTheory.LevelUnip
open GlobalTheory.LevelUnip in
theorem GlobalTheory.LevelUnip.unip_mod_half_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ (g : (p.F.lv2.lvl false).P) (z : (p.T.Q.Dw ((i : ℕ) + 1)).La), z ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) → (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) z ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF g z hz
  obtain ⟨κ, hk, hf⟩ := (p.pins i).2.lift.lev g
  have hB := p.charW.base
  obtain ⟨ψ0, -, hlev, -⟩ := hB.grp.levels
  have hL := hB.lev
  have hu : p.R.eG g ∈ (p.R.levR p.F.lv2 false).H := by
    show p.R.eG.symm.toMonoidHom (p.R.eG g) ∈ (p.F.lv2.lvl false).P
    simp
  have hun : ∀ PP, p.R.eG g PP ∈ unip (kP PP.1) D.R.r := by
    rw [hlev] at hu
    exact fun PP => (Subgroup.mem_pi _).1 hu PP (Set.mem_univ _)
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hemb := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hβ := hL.βW i
  have hr := rank_Wc (D := D) i
  have hkSt := parLev_St hk.2.1
  have hred : ∀ P ∈ p.R.Pg, (((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
      Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) - 1) ^ D.R.r = 0 := by
    intro P hP
    have hb := blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)
    have e : upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) = p.R.eG g ⟨P, hP⟩ :=
      congrFun hk.2.2 ⟨P, hP⟩
    have hU := hun ⟨P, hP⟩
    rw [← e] at hU
    have hv := upper_block_val_submatrix (p.R.datWp i p.R.triv).hr hb
    have hent : ∀ a c : Fin (Wc D i).rank,
        ((upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) : GL (Fin D.R.r) (kP P)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP P)) (Fin.cast hr a) (Fin.cast hr c) =
        ((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
          Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) a c := by
      intro a c
      exact (congrFun (congrFun hv (Fin.cast hr a)) (Fin.cast hr c)).trans rfl
    rw [← hr]
    apply sub_one_pow_eq_zero'
    · intro a c hca
      rw [← hent]
      exact hU.1 (show ((Fin.cast hr c : Fin D.R.r) : ℕ) < (Fin.cast hr a : Fin D.R.r) from hca)
    · intro a
      rw [← hent]
      exact hU.2 _
  have hp : p.T.Q.l.Mb * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := p.T.Q.l.prod
  have hp' : (∏ P ∈ p.R.Pg, P.asIdeal) * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by
    rw [← hhalf]; exact hp
  have hI : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb :=
    (hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)
  have hc : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤ := p.T.Q.l.coprime
  have hcong := fun b (hb : b ∈ Mfr p.T.Q.l) => exists_pow_cong hβ p.R.Pg hp' hkSt hred hb
  have hpow := approx_pow hemb (sub_one_mulVec_mem hβ hkSt) hf D.R.r
  have h0 : ∀ a ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La),
      ∃ w ∈ latGHat (Wc D i) 1, finVec (Wc D i) (iotaW p.T i ((0 : (p.T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] _) a)) -
        (0 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
          finVec (Wc D i) (iotaW p.T i a) = p.T.Q.l.M • w := by
    intro a _
    refine ⟨0, zero_mem _, ?_⟩
    funext j
    simp [finVec]
  have := GlobalTheory.LevelUnique.sub_mem_of_approx hemb (lt_of_lt_of_le (by norm_num) p.T.Q.l.three_le) hI hc hcong hpow h0 z
  simpa using this
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnipModHalfStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lev_sub_one_pow_mem_level_multiple : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ (g : (p.F.lv2.lvl false).P) (z : (p.T.Q.Dw ((i : ℕ) + 1)).La), z ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) → (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) z ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
  first | exact @_root_.GlobalTheory.LevelUnip.unip_mod_half_alt | exact _root_.GlobalTheory.LevelUnip.unip_mod_half_alt | (intros; apply _root_.GlobalTheory.LevelUnip.unip_mod_half_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeBase
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefFree
theorem free_base_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by omega⟩
  have hpq : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p + (p.T.Q.Dw ((i : ℕ) + 1)).q := by
    have h1 := (p.fw.laws.pins.2.2.2 _ hj).1
    have h2 := D.R.m_add_three_le_k
    rw [h1]
    simp only [Ranks.sigW]
    omega
  have hun : ∀ (g : (p.F.lv2.lvl false).P) (x : (p.T.Q.Dw ((i : ℕ) + 1)).La),
      (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) :=
    fun g x => mem_smul_top_of_coprime _ _ (by rw [sup_comm]; exact p.T.Q.l.coprime) _
      (_root_.GlobalTheory.T.lev_sub_one_pow_mem_level_multiple p i PP A M hR hi hG hW hH hF g) x
  exact GlobalTheory.T.free_action_framedPoints_of_unipotent_mod_two_primes D.host.E p.T.Q.H (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
    (p.F.lv2.lvl false).P (fun g => (p.O i).lev (g : p.P.Gp)) D.R.r (D.host.g 0) (D.host.g 1)
    (p.T.Q.l.Mb ⊔ Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.E)}) (p.T.Q.l.Mb ⊔ Ideal.span {((D.host.g 1 : ℕ) : 𝓞 D.host.E)})
    hpq (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
    (sup_span_ne_top _ (D.host.g_prime 0) (by rw [hM]; exact dvd_mul_right _ _))
    (sup_span_ne_top _ (D.host.g_prime 1) (by rw [hM]; exact dvd_mul_left _ _))
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    le_sup_left le_sup_left (fun g x => Submodule.smul_mono_left le_sup_left (hun g x))
    (fun g x => Submodule.smul_mono_left le_sup_left (hun g x)) (_root_.GlobalTheory.T.eq_one_of_lev_sub_mem_Mb_gram p i PP A M hR hi hG hW hH hF)
end GlobalTheory.DefFree
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeBaseStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freePt_last_index_of_fnAlgClosed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  first | exact @_root_.GlobalTheory.DefFree.free_base_alt | exact _root_.GlobalTheory.DefFree.free_base_alt | (intros; apply _root_.GlobalTheory.DefFree.free_base_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigSlopeLe
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefEig
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem actKeeps_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') : ActKeeps (κ := p.κ) p.O i := fun g f hf => by
  obtain ⟨cc, ph, hO⟩ := (hp.oneMap i).1
  obtain ⟨k, hk, -⟩ := (p.pins i).2.lift.lev g
  exact (hO.1 g k hk f hf).1
theorem exists_chi_algebraMap_eq_FW_chi_mul_psi_inv (p : PtAt ex Csz) (i : Fin D.R.m) (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) :
    ∃ χ : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ, ∀ u, algebraMap p.T.Q.c.F D.what₂.LL (χ u : p.T.Q.c.F) =
      (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) := by
  have hv := _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt p i hp.1 hp.2
  choose b hb using hv
  have hinj : Function.Injective (algebraMap p.T.Q.c.F D.what₂.LL) := (algebraMap p.T.Q.c.F D.what₂.LL).injective
  have hb0 : ∀ u, b u ≠ 0 := fun u h => by
    have := hb u
    rw [h, map_zero] at this
    exact Units.ne_zero _ this.symm
  refine ⟨{ toFun := fun u => Units.mk0 (b u) (hb0 u), map_one' := ?_, map_mul' := ?_ }, fun u => hb u⟩
  · refine Units.ext (hinj ?_)
    simp [hb]
  · intro u v
    refine Units.ext (hinj ?_)
    simp only [Units.val_mk0, Units.val_mul, map_mul, hb, Subgroup.coe_mul, MonoidHom.inv_apply]
    push_cast
    ring
set_option maxHeartbeats 1000000 in
theorem exists_finite_group_lev_char_slope : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∃ (G : Type) (_ : Group G) (_ : Finite G) (lev : G → ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La) × ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La)) (χ : G →* (p.T.Q.c.F)ˣ), ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ slope_sq (normW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)) (eigLat (p.T.U ((i : ℕ) + 1)) lev χ (Gk p i)) ≤ muCore p i := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hp hi hG hW hH hF
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.DefEig.exists_chi_algebraMap_eq_FW_chi_mul_psi_inv p i hp
  have hK := _root_.GlobalTheory.DefEig.actKeeps_alt p i hp.1
  have hρ := (p.rhoGeo i).1 hK
  have hsm : ∀ (u : (p.F.lv2.lvl false).P) (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n),
      ((p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f) : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) =
        (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
          ((p.fw.e i f : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) := fun u f => by
    rw [LinearEquiv.map_smul, Submodule.coe_smul, ← hχ u, algebraMap_smul]
  refine ⟨(p.F.lv2.lvl false).P, inferInstance, inferInstance, fun g => (p.O i).lev2 (g : p.P.Gp), χ, actLev_levB p i,
    _root_.GlobalTheory.T.freePt_last_index_of_fnAlgClosed p i PP A M hp hi hG hW hH hF, le_of_eq ?_⟩
  have hAB : ((eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ).comap
        (cuspW (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.T.U ((i : ℕ) + 1)) (Gk p i)).subtype).restrictScalars (𝓞 p.T.Q.c.F) =
      ((Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)).comap (VK p.fw i).subtype).restrictScalars (𝓞 p.T.Q.c.F) := by
    ext x
    change (x : p.T.R ((i : ℕ) + 1)) ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔
      (x : p.T.R ((i : ℕ) + 1)) ∈ Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)
    have hx : (x : p.T.R ((i : ℕ) + 1)) ∈ p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n := by
      exact (cuspW_wtZ (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c) (U := p.T.U ((i : ℕ) + 1))
        (wtA (p.κ i)) (p.κ i).n).le x.2
    constructor
    · intro h
      rw [mem_eigSub_iff] at h
      apply Submodule.subset_span
      refine ⟨hx, fun u => ?_⟩
      obtain ⟨hf', h2⟩ := hρ (u : p.P.Gp) ⟨x, hx⟩
      rw [← h2]
      have h3 : (⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) (x : p.T.R ((i : ℕ) + 1)), hf'⟩ :
          p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n) = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨x, hx⟩ :=
        Subtype.ext (h u)
      exact (congrArg (fun y => ((p.fw.e i y : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL)) h3).trans (hsm u ⟨x, hx⟩)
    · intro h
      refine Submodule.span_le.2 ?_ h
      rintro f ⟨hf, hT⟩
      rw [SetLike.mem_coe, mem_eigSub_iff]
      intro u
      obtain ⟨hf', h2⟩ := hρ (u : p.P.Gp) ⟨f, hf⟩
      have h4 : (p.R.FW i).ρ (u : p.P.Gp) ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) =
          (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
            ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) := hT u
      have h5 : (p.fw.e i ⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f, hf'⟩) =
          p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨f, hf⟩) := by
        exact Subtype.ext (h2.trans (h4.trans (hsm u ⟨f, hf⟩).symm))
      exact congrArg Subtype.val ((p.fw.e i).injective h5)
  have key : eigLat (p.T.U ((i : ℕ) + 1)) (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ (Gk p i) =
      latTypeK p.fw p.F.lv2 i :=
    congrArg (latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ⊓ ·) hAB
  rw [muCore, ← key]
end GlobalTheory.DefEig
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigSlopeLeStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_group_actLev_char : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∃ (G : Type) (_ : Group G) (_ : Finite G) (lev : G → ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La) × ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La)) (χ : G →* (p.T.Q.c.F)ˣ), ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ slope_sq (normW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)) (eigLat (p.T.U ((i : ℕ) + 1)) lev χ (Gk p i)) ≤ muCore p i := by
  first | exact @_root_.GlobalTheory.DefEig.exists_finite_group_lev_char_slope | exact _root_.GlobalTheory.DefEig.exists_finite_group_lev_char_slope | (intros; apply _root_.GlobalTheory.DefEig.exists_finite_group_lev_char_slope <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatExistsAtCore
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DegLieCore
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DegLieCore
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FlatCore
namespace GlobalTheory.DefCoreLie
end GlobalTheory.DefCoreLie
namespace GlobalTheory.DefCoreLie
theorem degLie_core_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ (Z : Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) (P : PtData Z) (τ : Psi p.T.Q.H), P.degLie τ.1 = -flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hm hG hW hN hF Z P τ
  obtain ⟨hDC, -, -, -⟩ := _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom p i PP A M hR hm hG hW hN hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  have hL : Laws (p.T.U ((i : ℕ) + 1)) (xiR D) := GlobalTheory.LawsCore.laws_core D p.T hJ _ hj hF
  obtain ⟨_, χ, hχ, hOm, -, hH⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q hJ.pins.1 p.Del p.h0
  have hFr := frameDeg_def GlobalTheory.T.cmObject_definite_lieEigenLattice_degree_difference D.host.E p.T.Q.H hH χ hχ _ _ _ _ _ _ _ hL hDC.q
  obtain ⟨s⟩ := GlobalTheory.FlatLine.Definite.nonempty_flatSec (p.T.U ((i : ℕ) + 1)) (xiR D) hDC.q hDC.p hDC.good hDC.unf hDC.geo Z τ
  have h := (hFr Z τ (ArchSec.ofConst s.toFrame) s.toFrame.rho_vw fun w v hv => by
      have h1 := s.toFrame.val_eq hv
      rw [Pi.zero_apply, zero_add] at h1
      exact h1).2
  rw [(GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree _ _ _ _ _ _ _ _ _ hDC Z P).1 τ s, s.deg_eq_toFrame, flatDegVal, ← hOm, ← h]
  rfl
end GlobalTheory.DefCoreLie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DegLieCoreStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degLie_eq_neg_flatDegVal_at_last_index : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ (Z : Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) (P : PtData Z) (τ : Psi p.T.Q.H), P.degLie τ.1 = -flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm := by
  first | exact @_root_.GlobalTheory.DefCoreLie.degLie_core_alt | exact _root_.GlobalTheory.DefCoreLie.degLie_core_alt | (intros; apply _root_.GlobalTheory.DefCoreLie.degLie_core_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatExistsAtCore
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefFlat
theorem flatExistsAt_core_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → FlatExistsAt (p.T.U ((i : ℕ) + 1)) (xiR D) (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF
  obtain ⟨hDC, -, -, -⟩ := _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom p i PP A M hR hi hG hW hH hF
  intro Z τ
  refine ⟨GlobalTheory.FlatLine.Definite.nonempty_flatSec _ _ hDC.q hDC.p hDC.good hDC.unf hDC.geo Z τ, fun s => ?_⟩
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_definiteRationalPointData_component _ _ _ _ _ _ _ _ _ hDC Z
  have h1 := (GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree _ _ _ _ _ _ _ _ _ hDC Z P).1 τ s
  have h2 := _root_.GlobalTheory.T.degLie_eq_neg_flatDegVal_at_last_index p i PP A M hR hi hG hW hH hF Z P τ
  rw [neg_neg]
  linarith
end GlobalTheory.DefFlat
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatExistsAtCoreStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatExistsAt_last_index_of_fnAlgClosed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → FlatExistsAt (p.T.U ((i : ℕ) + 1)) (xiR D) (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) := by
  first | exact @_root_.GlobalTheory.DefFlat.flatExistsAt_core_alt | exact _root_.GlobalTheory.DefFlat.flatExistsAt_core_alt | (intros; apply _root_.GlobalTheory.DefFlat.flatExistsAt_core_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsDefinedOfNotFunctionFieldAlgClosed
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FnAlgClosedCore
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CoreDesc
theorem fnAlgClosed_core_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hR : _root_.GlobalTheory.CovTop.RowsTAlt p) (j : ℕ) (hj : InR D j) : FnAlgClosed (Xo := (p.T.Q.Xo j)) (c := p.T.Q.c) := by
  have hc := hR.1.ties.core
  have hpin : p.T.Q.Pins := hc.laws.pins
  have hpos : 0 < D.host.g 0 * D.host.g 1 * D.host.pde :=
    Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) D.host.pde_prime.pos
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins D p.T.Q hpin hc.canon _ hpos hc.field₁.curve j hj p.T.Q.l
    (p.T.Q.Xo j) p.T.Q.c hpin.2.1.2 ?_ rfl
  rw [hpin.2.1.1]
  exact Dvd.intro _ rfl
end GlobalTheory.CoreDesc
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CoreDesc
theorem isDefined_of_not_functionField_algClosed_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → ¬ FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  intro _
  refine ⟨0, 0, le_rfl, ?_⟩
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A hR _ _ _ _ hF
  exact (hF (_root_.GlobalTheory.CoreDesc.fnAlgClosed_core_alt p hR _ ⟨Nat.succ_pos _, i.isLt⟩)).elim
end GlobalTheory.CoreDesc
end
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_defBound_sub_unitError_le_muCore_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → ¬ FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  first | exact @_root_.GlobalTheory.CoreDesc.isDefined_of_not_functionField_algClosed_alt | exact _root_.GlobalTheory.CoreDesc.isDefined_of_not_functionField_algClosed_alt | (intros; apply _root_.GlobalTheory.CoreDesc.isDefined_of_not_functionField_algClosed_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovTop.DefCore
theorem defect_bound_of_connected_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  intro _hP
  refine ⟨0, 0, le_rfl, ?_⟩
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A hp hi hg hw hh hF
  obtain ⟨hdef, hfin, hne, hdict⟩ := _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom p i PP A 0 hp hi hg hw hh hF
  obtain ⟨G, _, _, lev, χ, hact, hfree, hsl⟩ := _root_.GlobalTheory.T.exists_finite_group_actLev_char p i PP A 0 hp hi hg hw hh hF
  have hflat := _root_.GlobalTheory.T.flatExistsAt_last_index_of_fnAlgClosed p i PP A 0 hp hi hg hw hh hF
  have h := (GlobalTheory.T.eigenlattice_slope_lower_bound_definite_case D _ _ _ _ _ _ (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) G lev χ
    (wtA (p.κ i)) (p.κ i).n _ hdef hfin hne hdict hact hfree hw.dom hg.2.2.2 hflat).2
  unfold Gk at hsl
  linarith
theorem lifts_two_mul_defBound_sub_unitE_le_muCore : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → GramAt p i → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm) - C * unitE p ≤ muCore p i := by
  intro hP
  obtain ⟨M1, C1, hC1, h1⟩ := _root_.GlobalTheory.CovTop.DefCore.defect_bound_of_connected_alt hP
  obtain ⟨M2, C2, hC2, h2⟩ := _root_.GlobalTheory.T.two_defBound_sub_unitError_le_muCore_alt hP
  have hW : _root_.GlobalTheory.CovTop.LiftWeightNumerator := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  have hH1 : _root_.GlobalTheory.CovTop.HostNAlt M1 := _root_.GlobalTheory.CovTop.Sizes.hostN_alt M1
  have hH2 : _root_.GlobalTheory.CovTop.HostNAlt M2 := _root_.GlobalTheory.CovTop.Sizes.hostN_alt M2
  unfold _root_.GlobalTheory.CovTop.LiftsCondition _root_.GlobalTheory.CovTop.LiftWeightNumerator _root_.GlobalTheory.CovTop.HostNAlt at *
  refine Closed.imp ((hW.and hH1).and hH2) ?_
  rintro eps Fm CH - ⟨⟨⟨Cw, -, xw, hw⟩, ⟨A1, -, x1, ha1⟩⟩, ⟨A2, -, x2, ha2⟩⟩
  refine ⟨max C1 C2, le_max_of_le_left hC1, max (max xw x1) x2, fun x hx hle ι p hp i hi hg => ?_⟩
  have hle1 : xw ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hle2 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have hle3 : x2 ≤ x := le_trans (le_max_right _ _) hle
  have w := hw x hx hle1 ι p hp i
  have a1 := ha1 x hx hle2 ι p hp i
  have a2 := ha2 x hx hle3 ι p hp i
  have hu := unitE_nonneg p i _ _ _ w a1
  by_cases hF : FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c)
  · have := h1 p i _ _ hp hi hg w a1 hF
    nlinarith [le_max_left C1 C2]
  · have := h2 p i _ _ hp hi hg w a2 hF
    nlinarith [le_max_right C1 C2]
end GlobalTheory.CovTop.DefCore
end
end
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_defBound_sub_le_muCore_of_gramAt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → GramAt p i → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm) - C * unitE p ≤ muCore p i := by
  first | exact @_root_.GlobalTheory.CovTop.DefCore.lifts_two_mul_defBound_sub_unitE_le_muCore | exact _root_.GlobalTheory.CovTop.DefCore.lifts_two_mul_defBound_sub_unitE_le_muCore | (intros; apply _root_.GlobalTheory.CovTop.DefCore.lifts_two_mul_defBound_sub_unitE_le_muCore <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParametersScaleRankGapBounds
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParametersScaleRankGapBounds
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovTop.DefSizes
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.DefSizes
namespace GlobalTheory.CovTop.DefSizes
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.DefSizes
namespace GlobalTheory.CovTop.DefSizes
theorem parameters_scale_rank_gap_bounds :
    _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → |(ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| *
      (∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) -
        (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1) τ : ℝ)|) +
      (∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)) +
      ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd (Fm.D x ι).host.E| ≤
      C * unitE p := by
  have hdim : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ w : ℤ,
      (GlobalTheory.DualWeyl.dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := fun n la h => (GlobalTheory.T.dualWeyl_dim_formula_duality_bound n la h).2.2
  have H := Closed.and _root_.GlobalTheory.CovTop.WtShape.wtN_z (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1)
  simp only [_root_.GlobalTheory.CovTop.LiftWeightNumerator, _root_.GlobalTheory.CovTop.HostNAlt, _root_.GlobalTheory.CovTop.LiftsCondition] at H
  unfold _root_.GlobalTheory.CovTop.LiftsCondition
  refine Closed.imp H ?_
  intro eps Fm CH _ h
  obtain ⟨⟨C1, -, hw⟩, ⟨A, -, hh⟩⟩ := h
  obtain ⟨x0, h⟩ := _root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and hw hh
  exact ⟨35, by norm_num, x0, fun x hx hle ι p hp i _ =>
    sizes_at p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i) (Fm.sizes x hx ι) hdim⟩
end GlobalTheory.CovTop.DefSizes
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParametersScaleRankGapBoundsStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_dimension_log_bound' : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → |(ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| * (∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) - (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1) τ : ℝ)|) + (∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)) + ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd (Fm.D x ι).host.E| ≤ C * unitE p := by
  first | exact @_root_.GlobalTheory.CovTop.DefSizes.parameters_scale_rank_gap_bounds | exact _root_.GlobalTheory.CovTop.DefSizes.parameters_scale_rank_gap_bounds | (intros; apply _root_.GlobalTheory.CovTop.DefSizes.parameters_scale_rank_gap_bounds <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.DefLow
theorem covering_low_defect_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.LowDefectCondition := by
  intro hP hG hA
  have hc := _root_.GlobalTheory.T.two_mul_defBound_sub_le_muCore_of_gramAt hP
  refine Closed.imp ((hA.and (hG.and (_root_.GlobalTheory.CovTop.WtShape.wtN_z.and _root_.GlobalTheory.T.weight_dimension_log_bound'))).and hc) fun Fm CH _ h => ?_
  obtain ⟨⟨⟨CA, hCA, xA, eA⟩, ⟨CG, -, xG, eG⟩, ⟨CW, -, xW, eW⟩, ⟨C3, hC3, x3, e3⟩⟩, ⟨C₀, hC₀, x0, h1⟩⟩ := h
  refine ⟨CA + C3 + C₀, by positivity, max (max (max xA xG) (max xW x3)) x0,
    fun x hx hle' ι p hp i hi => ?_⟩
  have hle := le_trans (le_max_left _ _) hle'
  have l0 : x0 ≤ x := le_trans (le_max_right _ _) hle'
  have lA : xA ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have lG : xG ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have lW : xW ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have l3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle
  have a := eA x hx lA ι p hp i
  have g := eG x hx lG ι p hp i
  have w := eW x hx lW ι p hp i
  have s := e3 x hx l3 ι p hp i hi
  have c := h1 x hx l0 ι p hp i hi g
  have hk := (Fm.D x ι).R.m_add_three_le_k
  have q0 : (dat p i).q = 0 := by
    rw [w.sig.2.1]; unfold Ranks.sigW; simp only; omega
  have p1 : 1 ≤ (dat p i).p := by
    rw [w.sig.1]; unfold Ranks.sigW; simp only; omega
  have ar := GlobalTheory.T.two_definiteBound_ge_anchoredMainTerm_sub_crude_errors _ _ (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1)
    (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm q0 p1 (p.κ i).n_even
  have a1 := a.1
  simp only [q0, Nat.cast_zero, sub_zero] at a1
  rw [abs_le] at a1
  unfold LowAt
  linarith [a1.1, a1.2]
end GlobalTheory.CovTop.DefLow
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowDef_of_gram_of_anchor : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.LowDefectCondition := by
  first | exact @_root_.GlobalTheory.CovTop.DefLow.covering_low_defect_alt | exact _root_.GlobalTheory.CovTop.DefLow.covering_low_defect_alt | (intros; apply _root_.GlobalTheory.CovTop.DefLow.covering_low_defect_alt <;> assumption)
end
end
