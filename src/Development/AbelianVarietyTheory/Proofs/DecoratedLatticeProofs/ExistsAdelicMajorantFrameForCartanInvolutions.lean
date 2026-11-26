module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutions
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.MajFrame

theorem exists_maj_cart : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → ∃ a : GL (Fin A.rank) (AE D), IsMaj A a ∧ ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1 := by
  intro D θ A sA hθ hs
  obtain ⟨a, ha, -, hfs⟩ := GlobalTheory.Doubling.exists_isMaj_frameInv_eq hθ hs
  refine ⟨a, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ
  rw [← hfs τ, GlobalTheory.Doubling.frameInv]
  have : (compAt θ τ a.1)ᴴ * (gramAt D A τ * (compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D A τ)) * compAt θ τ a.1 =
      ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) := by
    simp only [Matrix.mul_assoc]
  rw [this, hε, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp

end GlobalTheory.Core.Rk.MajFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutionsStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicMajorantFrame_for_cartanInvolutions : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → ∃ a : GL (Fin A.rank) (AE D), IsMaj A a ∧ ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1 := by
  first | exact @GlobalTheory.Core.Rk.MajFrame.exists_maj_cart | exact GlobalTheory.Core.Rk.MajFrame.exists_maj_cart | (intros; apply GlobalTheory.Core.Rk.MajFrame.exists_maj_cart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SignEquivInl
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RealData

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def signEquiv {n : ℕ} (ε : Fin n → Bool) {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) : Fin n ≃ Fin p ⊕ Fin q :=
  (Equiv.sumCompl fun a => ε a = true).symm.trans
    (Equiv.sumCongr (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; exact hp))
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simpa using hq)))

theorem signEquiv_inl {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) (i : Fin p) : ε ((signEquiv ε hp hq).symm (Sum.inl i)) = true := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.sumCompl_apply_inl]
  generalize (Fintype.equivFinOfCardEq (α := {a // ε a = true}) _).symm i = x
  exact x.2

theorem signEquiv_inr {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) (i : Fin q) : ε ((signEquiv ε hp hq).symm (Sum.inr i)) = false := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.sumCompl_apply_inr]
  generalize (Fintype.equivFinOfCardEq (α := {a // ¬ ε a = true}) _).symm i = x
  simpa using x.2

theorem card_true (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (Finset.univ.filter fun a => M.ε τ a = true).card = (V.sig (tauE D τ)).1 := by
  have h1 := GlobalTheory.TowerSplit.hasSignature_of_model M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ)] at h1
  exact (Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 (hV (tauE D τ))).1

theorem card_false (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (Finset.univ.filter fun a => M.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  have h1 := GlobalTheory.TowerSplit.hasSignature_of_model M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ)] at h1
  exact (Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 (hV (tauE D τ))).2

def sortedFrame (M : DSModel V S) (hV : V.SigOK) : GlobalTheory.Mem.Th.CptF V := fun τ =>
  (M.fr τ).submatrix (signEquiv (M.ε τ) (card_true M hV τ) (card_false M hV τ)).symm id

theorem Jpq_submatrix {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) :
    (Formalism.UG.Jpq p q).submatrix (signEquiv ε hp hq) (signEquiv ε hp hq) = Formalism.REAL.Jm ε := by
  ext a b
  simp only [submatrix_apply, Formalism.REAL.Jm, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    rcases h1 : signEquiv ε hp hq a with i | i
    · have := signEquiv_inl hp hq i
      rw [← h1, Equiv.symm_apply_apply] at this
      simp [Formalism.UG.Jpq, this]
    · have := signEquiv_inr hp hq i
      rw [← h1, Equiv.symm_apply_apply] at this
      simp [Formalism.UG.Jpq, this]
  · have hne : signEquiv ε hp hq a ≠ signEquiv ε hp hq b := (signEquiv ε hp hq).injective.ne hab
    rw [if_neg hab]
    rcases h1 : signEquiv ε hp hq a with i | i <;> rcases h2 : signEquiv ε hp hq b with j | j <;> rw [h1, h2] at hne <;>
      simp_all [Formalism.UG.Jpq, Matrix.one_apply]

end GlobalTheory.ChainOnto.RealData

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstOccurrenceRuleThetaChainStepBothDirections
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstOccurrenceRuleThetaChainStepBothDirections
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepRule

theorem rulePar_of_pairPar {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X)
    {S S' : SPar} {aS aT : ℚ} (h : PairPar S S' aS aT) : RulePar X S S' aS aT := by
  have far : ∀ {t : ℕ} {al be ga de : List ℚ}, GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (signed (al ++ be) (ga ++ de) aT) →
      ¬ ∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2 := by
    rintro t al be ga de hF ⟨a, ha⟩
    have hm : (((t : ℚ) + 1) / 2, a.isLeft) ∈ GlobalTheory.SignedHC.ofIx (lamA al be ga de) :=
      Finset.mem_image.2 ⟨a, Finset.mem_univ _, by rw [ha]⟩
    rw [lamA, GlobalTheory.SignedHC.mem_ofIx_ofBlocks (by simp) (by simp)] at hm
    have : ∃ s, (((t : ℚ) + 1) / 2 + aT, s) ∈ signed (al ++ be) (ga ++ de) aT := by
      rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨true, Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
      · exact ⟨false, Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
    have := hF _ (GlobalTheory.SignedHC.mem_entries.2 this)
    rw [add_sub_cancel_right, abs_of_nonneg (by positivity)] at this
    linarith
  have hb : ∀ t, (block t).length = t := fun t => by simp [block]
  obtain ⟨t, P, P', e, e', ⟨⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩, hF⟩ | ⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩⟩ := h
  all_goals
    have ht := hd.1.1
    have hn := hd.1.2.1
    obtain ⟨-, p1, p2, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hd.1
    obtain ⟨-, p3, -⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hd.1
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp [hb]; omega, by simp,
      ⟨by omega, by omega, p1, p2, (h3.1 t al be ga de hd).2.1, (h3.1 t al be ga de hd).2.2,
        h5.1 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp, by simp [hb]; omega,
      ⟨by omega, by omega, p1, p3, (h3.2 t al be ga de hd).2.1, (h3.2 t al be ga de hd).2.2,
        h5.2 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamA' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp [hb]; omega, by simp, by simp, by simp,
      ⟨by omega, by omega, p2, p1, sw.1 (h3.1 t al be ga de hd).1, sw.2.1 (h3.1 t al be ga de hd).2.2,
        sw.2.2 (h4.1 t al be ga de hd)⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamM' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp, by simp [hb]; omega, by simp, by simp,
      ⟨by omega, by omega, p3, p1, sw.1 (h3.2 t al be ga de hd).1, sw.2.1 (h3.2 t al be ga de hd).2.2,
        sw.2.2 (h4.2 t al be ga de hd)⟩, e, e'⟩

theorem rulePar_step : ∀ (D : D7) (X : ProvA), Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X →
    ∀ k : Fin D.R.m, ChainPar D k → ∀ τ, RulePar X (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ) (expS D k τ) (expT D k τ) ∧
      RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) := by
  intro D X h3 h4 h5 k hk τ
  obtain ⟨al, be, ga, de, hd, hfar, e0, e1⟩ := hk τ
  have hT : ThetaPar D.R.t (parA (Ptw D) k τ) (parA (Ptw D) (k + 1) τ) (expT D k τ) (expS D k τ) :=
    ⟨al, be, ga, de, e0, Or.inl ⟨hd, e1⟩⟩
  have hF : GlobalTheory.SignedHC.FarFrom (expT D k τ) (((D.R.t : ℚ) + 3) / 2) (parA (Ptw D) k τ) := by
    intro x hx
    obtain ⟨s, hs⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    rw [e0] at hs
    have : ∃ y ∈ al ++ be ++ ga ++ de, x = y + expT D k τ := by
      rcases Finset.mem_union.1 hs with h | h
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
    obtain ⟨y, hy, rfl⟩ := this
    rw [add_sub_cancel_right]
    exact hfar y hy
  exact ⟨rulePar_of_pairPar h3 h4 h5 ⟨D.R.t, _, _, rfl, rfl, Or.inl ⟨hT, hF⟩⟩,
    rulePar_of_pairPar h3 h4 h5 ⟨D.R.t, _, _, rfl, rfl, Or.inr hT⟩⟩

end GlobalTheory.StepRule

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstOccurrenceRuleThetaChainStepBothDirectionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOccurrenceRule_thetaChainStep_both_directions : ∀ (D : D7) (X : ProvA), Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → ∀ k : Fin D.R.m, ChainPar D k → ∀ τ, RulePar X (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ) (expS D k τ) (expT D k τ) ∧ RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) := by
  first | exact @GlobalTheory.StepRule.rulePar_step | exact GlobalTheory.StepRule.rulePar_step | (intros; apply GlobalTheory.StepRule.rulePar_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPoints
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem mult_equiv_real : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ (v : M.Vec) (b : GinfC V), ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)) (v τ : M.H τ)) ∧ ∀ U ∈ Mult θ M J χ, U w = rTr V (b : GA D V) (U v) := by
  intro D θ V Sp M J χ hθ v b
  classical
  let g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)
  have hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (b : GA D V) τ
  have hsm : ∀ τ, M.rep τ (g τ) (v τ : M.H τ) ∈ M.sm τ := fun τ =>
    GlobalTheory.SmoothStable.rep_mem_sm D V Sp M τ (g τ) (hg τ) _ (v τ).2
  have hb : GlobalTheory.AdelicScalar.realElt θ V g = (b : GA D V) := by
    have hR := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
    refine hR.2.2.1 _ (GlobalTheory.RealLift.prodAt_mem θ V _ g) _ b.2 fun τ => ?_
    have e := GlobalTheory.RealLift.infMat_prodAt hθ V (u := g) hg τ _ (Finset.nodup_toList Finset.univ)
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at e
    exact e
  refine ⟨fun τ => ⟨_, hsm τ⟩, fun τ => rfl, fun U hU => ?_⟩
  rw [GlobalTheory.RealEquiv.mult_realElt D V Sp θ M J χ U hU g hg v _ (fun τ => rfl), hb]

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_equivariant_real_points : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ (v : M.Vec) (b : GinfC V), ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)) (v τ : M.H τ)) ∧ ∀ U ∈ Mult θ M J χ, U w = rTr V (b : GA D V) (U v) := by
  exact @_root_.GlobalTheory.ChainOnto.mult_equiv_real
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierCoefficientBessel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.PhCol

variable {D : D7}

theorem one_le_level (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem one_mem_level (X : HidaSetting D) : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
  refine ⟨(Formalism.UG.stabGL X.B.I.Lf).one_mem, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  have h1 : X.B.I.fmat 1 = 1 := rfl
  rw [h1, sub_self, Matrix.zero_mulVec, smul_zero]

theorem psiInfU_of_mem_Hinf (X : HidaSetting D) (u : D.what₂.Word) (η : X.B.I.Ginf) (hη : η ∈ Hinf X u) :
    X.psiInfU u η = 1 := by
  have e := Formalism.L2.SG.PoincareInHH.Cut.psiInf_mul_H X u 1 η hη
  rw [one_mul] at e
  rw [e]
  exact Formalism.L2.SG.CovariantRepresentation.psiInfU_one X u

theorem castGA_mem_rat {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    x ∈ I.GFset ↔ castGA e x ∈ I'.GFset := by
  subst e; rfl

theorem iotaX_mem_rat (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (g : GA D (D.sp.Y 0))
    (hg : g ∈ GQ (D.sp.Y 0)) : iotaX X h g ∈ X.B.I.GFset := by
  have e : iotaX X h g = castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D g) := rfl
  rw [e]
  exact (castGA_mem_rat h.symm _).1 ((Formalism.IndefR.RationalEmbedding.iota_rat D g).1 hg)

theorem Ph_of_dec (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (y : X.B.I.GA)
    (n : X.B.I.Gf) (hh : Hfin X u) (k : X.B.I.Gf) (hd : IsDec X u y.2 n hh k) :
    Ph X u hK T y = phVal X u hK T y.1 n hh k := by
  have hex : ∃ n h k, IsDec X u y.2 n h k := ⟨n, hh, k, hd⟩
  unfold Ph
  rw [dite_eq_left hex]
  exact Formalism.L2.SG.Pf.phWellDef_holds X u T y.1 y.2 _ n _ k _ hh hex.choose_spec.choose_spec.choose_spec hd

variable {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

theorem continuous_toH (B : SBes X h u ψ A) : Continuous B.toH := by
  have he : Continuous (embA B.d B.o) := by
    have e : (embA B.d B.o : GA D A → GA D (D.sp.Y 0)) = fun a => B.d.emb0 (B.o.emb (a, 1)) := rfl
    rw [e]
    exact B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hc : Continuous fun a => iotaX X h (embA B.d B.o a) := (iotaX X h).continuous.comp he
  unfold SBes.toH
  exact (hc.fst.subtype_mk _).prodMk (hc.snd.subtype_mk _)

theorem continuous_col (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (ξ : X.Vpi u) :
    Continuous fun p : Hinf X u × Hfin X u => (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ p := by
  obtain ⟨hT1, hT2⟩ := T.2
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  rw [continuous_iff_continuousAt]
  intro p0
  have hπ : Continuous fun η : Hinf X u => X.piU u η ξ :=
    ((X.piU_rep u).2.2.2.2 ξ).comp_continuous continuous_subtype_val (fun η => hinf_le_sinf X u _ η.2)
  let L : X.Vpi u →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Hinf X u × Hfin X u => ℂ) ((1 : Hinf X u), p0.2)).comp
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ))
  have hG : Continuous fun p : Hinf X u × Hfin X u => L (X.piU u p.1 ξ) :=
    L.continuous_of_finiteDimensional.comp (hπ.comp continuous_fst)
  have hUo : IsOpen {p : Hinf X u × Hfin X u |
      (X.xu u)⁻¹ * ((p0.2⁻¹ * p.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g} := by
    refine (X.B.I.topf_open X.B.g (one_le_level X)).preimage ?_
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_const.mul continuous_snd))).mul
      continuous_const
  have hp0 : p0 ∈ {p : Hinf X u × Hfin X u |
      (X.xu u)⁻¹ * ((p0.2⁻¹ * p.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g} := by
    show (X.xu u)⁻¹ * ((p0.2⁻¹ * p0.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g
    rw [inv_mul_cancel]
    simpa using one_mem_level X
  refine hG.continuousAt.congr (Filter.eventually_of_mem (hUo.mem_nhds hp0) fun p hp => ?_)
  obtain ⟨η, k⟩ := p
  have hp' : (X.xu u)⁻¹ * ((p0.2⁻¹ * k : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g := hp
  obtain ⟨hK2, hχ⟩ := hL.1 _ hp'
  let κ : Ku X u hK := ⟨p0.2⁻¹ * k, hK2⟩
  have e1 : ((η, k) : Hinf X u × Hfin X u) = (η, p0.2) * (1, ((κ : Hfin X u))) := by
    ext
    · simp
    · simp [κ]
  have e2 : ((η, p0.2) : Hinf X u × Hfin X u) = (1, p0.2) * (η, 1) := by
    ext <;> simp
  have hψ : ((psiK X u hK κ : ℂˣ) : ℂ) = 1 := hχ
  show L (X.piU u η ξ) = (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (η, k)
  rw [e1, (hT1 ξ).2 (η, p0.2) κ, hψ, one_mul, e2, ← hT2 η ξ (1, p0.2)]
  rfl

end GlobalTheory.Core.Mi.PhCol

namespace GlobalTheory.Core.Mi.PhCol

theorem ph_colForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK),
    (∀ ξ, IsContAut A (B.colForm T.1 ξ)) ∧ ∀ n ∈ flagN B.d, ∀ (a : GA D A) (y : X.B.I.Ginf),
      Ph X u hK T (iotaX X h (n * embA B.d B.o a) * (y, X.xu u)) =
        star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) * B.colForm T.1 (X.Wu u y) a := by
  intro D X h u ψ A B hK T
  obtain ⟨hT1, hT2⟩ := T.2
  refine ⟨fun ξ => ⟨fun γ hγ g => ?_, ?_⟩, fun n hn a y => ?_⟩
  ·
    have hrat : embA B.d B.o γ ∈ GQ (D.sp.Y 0) := by
      have e : embA B.d B.o γ = B.d.emb0 (B.o.emb (γ, 1)) := rfl
      rw [e]
      exact B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))
    have hr := iotaX_mem_rat X h _ hrat
    have hH := (B.tieH (embA B.d B.o γ)).1 ⟨γ, rfl⟩
    let γ' : Gam X u := ⟨iotaX X h (embA B.d B.o γ), Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_prod.2 hH⟩⟩
    have e : B.toH (γ * g) = (iotaI X u γ', iotaF X u γ') * B.toH g := by
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext
      · show (iotaX X h (embA B.d B.o (γ * g))).1 = (iotaX X h (embA B.d B.o γ)).1 * (iotaX X h (embA B.d B.o g)).1
        rw [map_mul, map_mul, Prod.fst_mul]
      · show (iotaX X h (embA B.d B.o (γ * g))).2 = (iotaX X h (embA B.d B.o γ)).2 * (iotaX X h (embA B.d B.o g)).2
        rw [map_mul, map_mul, Prod.snd_mul]
    show (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (B.toH (γ * g)) =
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (B.toH g)
    rw [e]
    exact (hT1 ξ).1 γ' (B.toH g)
  ·
    exact (continuous_col hK T ξ).comp (continuous_toH B)
  ·
    obtain ⟨hn1, hn2⟩ := (B.tieN n).1 hn
    obtain ⟨ha1, ha2⟩ := (B.tieH (embA B.d B.o a)).1 ⟨a, rfl⟩
    set m := iotaX X h n with hm
    set b := iotaX X h (embA B.d B.o a) with hb
    have e : iotaX X h (n * embA B.d B.o a) * (y, X.xu u) = (m.1 * b.1 * y, m.2 * b.2 * X.xu u * 1) := by
      rw [map_mul, ← hm, ← hb]
      ext <;> simp [mul_assoc]
    have hd : IsDec X u (m.1 * b.1 * y, m.2 * b.2 * X.xu u * 1).2 m.2 ⟨b.2, ha2⟩ 1 :=
      ⟨hn2, one_mem_level_subgroup X, rfl⟩
    rw [e, Ph_of_dec X u hK T _ _ _ _ hd]
    unfold phVal
    have hm1S : m.1 ∈ X.SinfU u := fun v => (hn1 v).1
    have hb1S : b.1 ∈ X.SinfU u := hinf_le_sinf X u _ ha1
    have hW : X.Wu u (m.1 * b.1 * y) = X.psiInfU u m.1 • X.piU u b.1 (X.Wu u y) := by
      rw [mul_assoc, (X.Wu_spec u).1 m.1 hm1S, (X.piU_rep u).2.2.2.1 m.1 hn1, ContinuousLinearMap.one_apply,
        (X.Wu_spec u).1 b.1 hb1S]
      have hpsi : X.psiInfU u b.1 = 1 := psiInfU_of_mem_Hinf X u b.1 ha1
      change X.psiInfU u m.1 • (X.psiInfU u b.1 • X.piU u b.1 (X.Wu u y)) = _
      rw [hpsi, one_smul]
    have hC : (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.piU u b.1 (X.Wu u y)) (1, ⟨b.2, ha2⟩) =
        B.colForm T.1 (X.Wu u y) a := by
      have := hT2 ⟨b.1, ha1⟩ (X.Wu u y) (1, ⟨b.2, ha2⟩)
      refine this.trans ?_
      show (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y) ((1, ⟨b.2, ha2⟩) * (⟨b.1, ha1⟩, 1)) =
        (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y) (B.toH a)
      refine congrArg ((T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y)) ?_
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext
      · show (1 : X.B.I.Ginf) * b.1 = (iotaX X h (embA B.d B.o a)).1
        rw [one_mul]
      · show b.2 * (1 : X.B.I.Gf) = (iotaX X h (embA B.d B.o a)).2
        rw [mul_one]
    rw [hW, map_smul, Pi.smul_apply, smul_eq_mul, hC, chi2_apply_one X hK, B.tieψ n hn]
    ring

end GlobalTheory.Core.Mi.PhCol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PiTensorInner

variable {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

def ellA (a : ∀ i, E i) : (⨂[ℂ] i, E i) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap fun i => innerₛₗ ℂ (a i))

theorem ellA_tprod (a b : ∀ i, E i) : ellA a (PiTensorProduct.tprod ℂ b) = ∏ i, ⟪a i, b i⟫_ℂ := by
  simp [ellA]

theorem prod_inner_update [DecidableEq ι] (a b : ∀ i, E i) (i : ι) (z : E i) :
    ∏ j, ⟪Function.update a i z j, b j⟫_ℂ = ⟪z, b i⟫_ℂ * ∏ j ∈ Finset.univ \ {i}, ⟪a j, b j⟫_ℂ := by
  have : (fun j => ⟪Function.update a i z j, b j⟫_ℂ) = Function.update (fun j => ⟪a j, b j⟫_ℂ) i ⟪z, b i⟫_ℂ := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this, Finset.prod_update_of_mem (Finset.mem_univ i)]

theorem ellA_update_add [DecidableEq ι] (a : ∀ i, E i) (i : ι) (x y : E i) :
    ellA (Function.update a i (x + y)) = ellA (Function.update a i x) + ellA (Function.update a i y) := by
  apply PiTensorProduct.ext
  ext b
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, ellA_tprod, prod_inner_update, inner_add_left, add_mul]

theorem ellA_update_smul [DecidableEq ι] (a : ∀ i, E i) (i : ι) (c : ℂ) (x : E i) :
    ellA (Function.update a i (c • x)) = conj c • ellA (Function.update a i x) := by
  apply PiTensorProduct.ext
  ext b
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.smul_apply, ellA_tprod, prod_inner_update, inner_smul_left, smul_eq_mul, mul_assoc]

def ellC (a : ∀ i, E i) : (⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ :=
  (starLinearEquiv ℂ : ℂ ≃ₗ⋆[ℂ] ℂ).toLinearMap.comp (ellA a)

theorem ellC_apply (a : ∀ i, E i) (w : ⨂[ℂ] i, E i) : ellC a w = conj (ellA a w) := rfl

theorem ellC_tprod (a b : ∀ i, E i) : ellC a (PiTensorProduct.tprod ℂ b) = ∏ i, ⟪b i, a i⟫_ℂ := by
  rw [ellC_apply, ellA_tprod, map_prod]; simp

def ellM : (∀ i, E i) →ₘₗ[ℂ] ((⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ) where
  toFun := ellC
  map_update_add' a i x y := by
    ext w; simp [ellC_apply, ellA_update_add]
  map_update_smul' a i c x := by
    ext w; simp [ellC_apply, ellA_update_smul]

def ipT : (⨂[ℂ] i, E i) →ₗ[ℂ] (⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ := PiTensorProduct.lift ellM

theorem ipT_tprod (a b : ∀ i, E i) :
    ipT (PiTensorProduct.tprod ℂ a) (PiTensorProduct.tprod ℂ b) = ∏ i, ⟪b i, a i⟫_ℂ := by
  simp [ipT, ellM, ellC_tprod]

theorem ipT_herm (w w' : ⨂[ℂ] i, E i) : ipT w w' = conj (ipT w' w) := by
  induction w using PiTensorProduct.induction_on generalizing w' with
  | smul_tprod r a =>
    induction w' using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, ipT_tprod, smul_eq_mul, map_mul, map_prod, inner_conj_symm,
        RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.conj_conj]
      ring
    | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), LinearMap.add_apply, map_add (f := _)]
  | add x y hx hy => simp [map_add (f := _), LinearMap.add_apply, hx, hy]

end GlobalTheory.PiTensorInner

noncomputable section

namespace GlobalTheory.PiTensorInner

variable {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

theorem ipT_map {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]
    (f : ∀ i, G i →ₗ[ℂ] E i) (hf : ∀ i x y, ⟪f i x, f i y⟫_ℂ = ⟪x, y⟫_ℂ) (x y : ⨂[ℂ] i, G i) :
    ipT (PiTensorProduct.map f x) (PiTensorProduct.map f y) = ipT x y := by
  induction x using PiTensorProduct.induction_on generalizing y with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, PiTensorProduct.map_tprod, ipT_tprod, hf]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]

theorem ipT_pos_fd [∀ i, FiniteDimensional ℂ (E i)] (x : ⨂[ℂ] i, E i) (hx : x ≠ 0) : 0 < (ipT x x).re := by
  classical
  let e := fun i => stdOrthonormalBasis ℂ (E i)
  let B := Basis.piTensorProduct fun i => (e i).toBasis
  have hB : ∀ p q, ipT (B p) (B q) = if p = q then 1 else 0 := by
    intro p q
    simp only [B, Basis.piTensorProduct_apply, OrthonormalBasis.coe_toBasis, ipT_tprod]
    split_ifs with h
    · subst h; simp [OrthonormalBasis.inner_eq_ite]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [OrthonormalBasis.inner_eq_ite, Ne.symm hi])
  set c := B.repr x
  have hsum : ipT x x = ∑ p, c p * conj (c p) := by
    conv_lhs => rw [← B.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hB, smul_eq_mul]
    simp [Finset.mul_sum, c]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hc : c ≠ 0 := by
    intro h; apply hx
    rw [← B.sum_repr x]; simp [c] at h; simp [h]
  obtain ⟨p, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra h; push_neg at h; exact hc (Finsupp.ext h)
  rw [hsum, Complex.re_sum]
  refine Finset.sum_pos' (fun q _ => ?_) ⟨p, Finset.mem_univ p, ?_⟩
  · rw [Complex.mul_conj]; simp [Complex.normSq_nonneg]
  · rw [Complex.mul_conj]; simpa using Complex.normSq_pos.mpr hp

end GlobalTheory.PiTensorInner

noncomputable section

namespace GlobalTheory.PiTensorInner

variable {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

theorem exists_fd (w : ⨂[ℂ] i, E i) : ∃ F : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (F i)) ∧
    ∃ w₀ : ⨂[ℂ] i, F i, PiTensorProduct.map (fun i => (F i).subtype) w₀ = w := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    refine ⟨fun i => ℂ ∙ a i, fun i => inferInstance, r • PiTensorProduct.tprod ℂ (fun i => ⟨a i, Submodule.mem_span_singleton_self _⟩), ?_⟩
    simp
  | add x y hx hy =>
    obtain ⟨F₁, h₁, x₀, rfl⟩ := hx
    obtain ⟨F₂, h₂, y₀, rfl⟩ := hy
    refine ⟨fun i => F₁ i ⊔ F₂ i, fun i => inferInstance,
      PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_left : F₁ i ≤ F₁ i ⊔ F₂ i)) x₀ +
      PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_right : F₂ i ≤ F₁ i ⊔ F₂ i)) y₀, ?_⟩
    rw [map_add (f := _), ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    rfl

theorem ipT_pos (w : ⨂[ℂ] i, E i) (hw : w ≠ 0) : 0 < (ipT w w).re := by
  obtain ⟨F, hF, w₀, rfl⟩ := exists_fd w
  have h0 : w₀ ≠ 0 := by rintro rfl; exact hw (map_zero _)
  rw [ipT_map (fun i => (F i).subtype) (fun i x y => rfl)]
  exact ipT_pos_fd w₀ h0

end GlobalTheory.PiTensorInner

namespace GlobalTheory.ChainOnto

theorem exists_ipD_smT : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ ipD : SmT M →ₗ[ℂ] SmT M →ₗ⋆[ℂ] ℂ,
    (∀ v v' : M.Vec, ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') = ∏ τ, ⟪(v' τ : M.H τ), (v τ : M.H τ)⟫_ℂ) ∧
    (∀ w w', ipD w w' = conj (ipD w' w)) ∧ ∀ w, w ≠ 0 → 0 < (ipD w w).re := by
  intro D V S M
  exact ⟨GlobalTheory.PiTensorInner.ipT, fun v v' => GlobalTheory.PiTensorInner.ipT_tprod v v', GlobalTheory.PiTensorInner.ipT_herm,
    GlobalTheory.PiTensorInner.ipT_pos⟩

end GlobalTheory.ChainOnto
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inner_product_smooth_vectors_tensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ ipD : SmT M →ₗ[ℂ] SmT M →ₗ⋆[ℂ] ℂ, (∀ v v' : M.Vec, ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') = ∏ τ, ⟪(v' τ : M.H τ), (v τ : M.H τ)⟫_ℂ) ∧ (∀ w w', ipD w w' = conj (ipD w' w)) ∧ ∀ w, w ≠ 0 → 0 < (ipD w w).re := by
  first | exact @GlobalTheory.ChainOnto.exists_ipD_smT | exact GlobalTheory.ChainOnto.exists_ipD_smT | (intros; apply GlobalTheory.ChainOnto.exists_ipD_smT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandra
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandra
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finDim_of_levFacts : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, LevFacts D → FinDim D := by
  intro hP D hL c hc j hj s hs
  have h1 := (hL c hc j hj s hs).1
  have : FiniteDimensional ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)) :=
    GlobalTheory.MultFinite.hcFinite hP hc.inf h1
  exact Module.Finite.map _ _

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandraStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainCuspSpaceFiniteDim_of_harishChandra : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, LevFacts D → FinDim D := by
  first | exact @GlobalTheory.ChainOnto.finDim_of_levFacts | exact GlobalTheory.ChainOnto.finDim_of_levFacts | (intros; apply GlobalTheory.ChainOnto.finDim_of_levFacts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueEqDivMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueEqDivMul
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem holValueAt_eq_div_mul : ∀ (Z L d Y : ℂ → ℂ) (s₀ z l : ℂ) (s₁ : ℝ), 0 < s₀.re → s₁ < s₀.re → AnalyticOnNhd ℂ d (rightOf 0) → (∀ s : ℂ, 0 < s.re → d s ≠ 0) → DifferentiableOn ℂ Y (rightOf s₁) → EqRight Z (fun s => L s / d s * Y s) → HolValueAt Z s₀ z → HolValueAt L s₀ l → z = l / d s₀ * Y s₀ := by
  intro Z L d Y s₀ z l s₁ h0 h1 hd hd0 hY e hZ hL
  exact (hZ.congr e).unique ((hL.div (holValueAt_self hd h0) (hd0 _ h0)).mul
    (holValueAt_self (hY.analyticOnNhd (isOpen_rightOf s₁)) h1))

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueEqDivMulStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicContinuationValue_eq_div_mul : ∀ (Z L d Y : ℂ → ℂ) (s₀ z l : ℂ) (s₁ : ℝ), 0 < s₀.re → s₁ < s₀.re → AnalyticOnNhd ℂ d (rightOf 0) → (∀ s : ℂ, 0 < s.re → d s ≠ 0) → DifferentiableOn ℂ Y (rightOf s₁) → EqRight Z (fun s => L s / d s * Y s) → HolValueAt Z s₀ z → HolValueAt L s₀ l → z = l / d s₀ * Y s₀ := by
  first | exact @GlobalTheory.Core.Rk.IP.holValueAt_eq_div_mul | exact GlobalTheory.Core.Rk.IP.holValueAt_eq_div_mul | (intros; apply GlobalTheory.Core.Rk.IP.holValueAt_eq_div_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterInjectivePlacewise
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterInjectivePlacewise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem chainPar_inj_at (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : chainPar c B k w = chainPar c B' k w) : B w = B' w := by
  induction k with
  | zero => simpa [chainPar] using h
  | succ k ih =>
    apply ih
    rw [chainPar_succ, chainPar_succ] at h
    simp only [stepPar] at h
    have h2 := add_right_cancel h
    exact Multiset.map_injective (mul_right_injective _) h2

theorem chainPar_inj : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)),
    chainPar c B k w = chainPar c B' k w → B w = B' w :=
  chainPar_inj_at

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterInjectivePlacewiseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChainHeckeParameter_injective_placewise : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  first | exact @GlobalTheory.ChainOnto.chainPar_inj | exact GlobalTheory.ChainOnto.chainPar_inj | (intros; apply GlobalTheory.ChainOnto.chainPar_inj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizesLe
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

namespace GlobalTheory.Core.Rk.HdGap

theorem bOne_eq (D : D7) (τ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    bOne D τ (j + 1) = (((D.hc τ).b ⟨j, hj⟩ : ℚ) : ℝ) := by
  unfold bOne
  rw [dite_eq_left (by omega)]
  rfl

theorem gap_of {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m) :
    Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤
      (((D.hc τ).b ⟨j + 1, hj⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := H
  have h := hg τ (j + 1) (by omega) (by omega)
  rwa [bOne_eq D τ (j + 1) hj, bOne_eq D τ j (by omega)] at h

theorem scale_of {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hCl : 1801 ≤ Cl)
    (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT) :
    1801 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ∧ 1801 ≤ D.R.r := by
  obtain ⟨hL, -, hmf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClm, -⟩ := H
  have hm : 1801 ≤ D.R.m := by exact_mod_cast hCl.trans hClm
  have hk := D.R.m_add_three_le_k
  refine ⟨?_, by unfold Ranks.r; omega⟩
  have hf1 : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
    exact_mod_cast this
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf1
  have hr : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have h1 : 1 ≤ (D.R.f : ℝ) ^ 5 * L := by nlinarith
  calc 1801 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := by nlinarith
    _ = Cl * (D.R.r : ℝ) ^ 19 * 1 := by ring
    _ ≤ Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * L) := by
        apply mul_le_mul_of_nonneg_left h1; nlinarith
    _ = _ := by ring

end GlobalTheory.Core.Rk.HdGap
end
