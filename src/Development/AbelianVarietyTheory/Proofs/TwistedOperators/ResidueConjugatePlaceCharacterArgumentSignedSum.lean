module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInte

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianDualBasisStabiliseStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianDualBasisStabilise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf

theorem cpt_cP_eq_zero_of_orth {D : D7} {PP : Pl D.host.E} {e : EAf D} (ho : e * GlobalTheory.StdFrames.sg D e = 0)
    (h1 : GlobalTheory.StdFrames.cpt PP e = 1) : GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP) e = 0 := by
  have h2 := GlobalTheory.StdFrames.cpt_sg_eq_zero (Q := GlobalTheory.IdemSupport.cP PP) (z := 1 - e)
    (by rw [GlobalTheory.StdFrames.cP_cP, RingHom.map_sub, h1, RingHom.map_one, sub_self])
  rw [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, sub_eq_zero] at h2
  have h3 := congrArg (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP)) ho
  rwa [RingHom.map_mul, ← h2, mul_one, RingHom.map_zero] at h3

theorem resT_eq_zero_of_fixed {D : D7} {Q : Pl D.host.E} {e x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (he : GlobalTheory.StdFrames.cpt Q e = 0) (hf : x = e * x) : resT Q x = 0 := by
  unfold resT
  rw [dite_eq_left hx]
  refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt Q ⟨x, hx⟩).2 ?_
  have h0 : GlobalTheory.StdFrames.cpt Q x = 0 := by rw [hf, RingHom.map_mul, he, zero_mul]
  show Valued.v (GlobalTheory.StdFrames.cpt Q x) < 1
  rw [h0, Valuation.map_zero]
  exact zero_lt_one

theorem resT_cP_hT_bwd_eq_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ PP : Pl D.host.E, GlobalTheory.SeeConjChar.sideAt X h PP = true → ∀ M ∈ St β, ∀ i j : Fin D.R.k, GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j))) = 0 := by
  intro D X h β hF PP hs M hM i j
  have hb := X.vectorsInLattice.2.2
  have ho := X.ew_orth
  have hw := X.bwd_w i
  have h1 : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by
    unfold sideAt at hs
    simpa only [decide_eq_true_eq] using hs
  have hfix : ∀ v, hA X.B.I (X.bwd i) v = X.ew * hA X.B.I (X.bwd i) v := fun v => by
    conv_lhs => rw [hw, unitaryCongruence.hA_smul_left, unitaryCongruence.sigA_sigA]
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hb ho hfix
  subst h
  have hv := (hb j).1
  rw [GlobalTheory.SeeMatchOnto.Lf_eq] at hv
  have hv2 := (GlobalTheory.SeeMatchOnto.mem_hatL_iff_of_St hF hM _).1 hv
  have hv3 := (GlobalTheory.SeeMatchOnto.Lf_eq (D := D)).ge hv2
  have hint := unitaryCongruence.hA_int _ (hb i).2 hv3
  exact ⟨hint, resT_eq_zero_of_fixed hint (cpt_cP_eq_zero_of_orth ho h1) (hfix _)⟩

end GlobalTheory.SeeConjChar
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_conjugatePlace_hermitian_dualBasis_stabiliser_eq_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ PP : Pl D.host.E, GlobalTheory.SeeConjChar.sideAt X h PP = true → ∀ M ∈ St β, ∀ i j : Fin D.R.k, GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j))) = 0 := by
  first | exact @GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero | exact GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero | (intros; apply GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceFormFlagPairingIntegralOnFrameLatti
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceFormFlagPairingIntegralOnFrameLatti
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjChar
open Classical

theorem hT_pairAt_int : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ (PP : Pl D.host.E) (a : Fin (Yc D 0).rank) (z : Fin (Yc D 0).rank → EAf D), (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D X h β hβ PP a z hz
  have hLf := GlobalTheory.KgFrame.Lf_eq D
  have hzL : z ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := by
    rw [hLf]
    exact (hβ z).2 hz
  set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf} with hS
  have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
    show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
    exact zero_mem _
  obtain ⟨hef, hz0, hbw⟩ := X.vectorsInLattice
  have he : ∀ a, e0T X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
  have hf : ∀ a, f0T X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
  have hb : ∀ a, bwT X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
  have hbd : ∀ a, bwdT X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
  have hzz : z0T X h ∈ S := GlobalTheory.SeeConjRead.cast_mem_Lf h X.z0 hz0
  have hv : pairAt X h PP a ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := by
    show pairAt X h PP a ∈ S
    unfold pairAt
    split_ifs
    · exact GlobalTheory.SeeConjRead.flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz a
    · exact GlobalTheory.SeeConjRead.flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun i => hb _) hzz a
  unfold hT
  exact intAf_cast X h _ (Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (GlobalTheory.SeeConjRead.cast_mem_Lf h.symm _ hv)
    (GlobalTheory.SeeConjRead.cast_mem_Lf h.symm _ hzL))

end GlobalTheory.SeeConjChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceFormFlagPairingIntegralOnFrameLattiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.otherInstanceForm_flagPairing_integral_on_frameLattice : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ (PP : Pl D.host.E) (a : Fin (Yc D 0).rank) (z : Fin (Yc D 0).rank → EAf D), (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.SeeConjChar.hT_pairAt_int | exact GlobalTheory.SeeConjChar.hT_pairAt_int | (intros; apply GlobalTheory.SeeConjChar.hT_pairAt_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianFormAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianFormAdjoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjAdj
open GlobalTheory.SeeConjChar Matrix
variable {D : D7}

theorem hform_unitary {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J : Matrix n n A) {M : GL n A} (hM : M ∈ Formalism.UG.UJ σ J) (u v : n → A) :
    Formalism.UG.hform σ J (M.val *ᵥ u) (M.val *ᵥ v) = Formalism.UG.hform σ J u v := by
  have e2 : ∀ a b, Formalism.UG.hform σ J a b = (σ ∘ a) ⬝ᵥ J *ᵥ b := by
    intro a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : σ ∘ (M.val *ᵥ u) = (σ ∘ u) ᵥ* Formalism.UG.cT σ M.val := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  have hM' : Formalism.UG.cT σ M.val * J * M.val = J := hM
  rw [e2, e2, e3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM']

theorem eq_of_kill {R : Type} [CommRing R] (PP : Pl D.host.E) (f : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R)
    (hf : ∀ p ∈ PP.asIdeal, f (oToS D.host.F D.host.E p) = 0) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (b : 𝓞 D.host.E) (hb : s - oToS D.host.F D.host.E b ∈ idS D.host.F PP.asIdeal) :
    f s = f (oToS D.host.F D.host.E b) := by
  have hle : idS D.host.F PP.asIdeal ≤ RingHom.ker f := by
    unfold idS
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    exact hf p hp
  have := hle hb
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  exact this

theorem ext_oToS {R : Type} [CommRing R] (PP : Pl D.host.E) (f g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R)
    (hfg : ∀ a, f (oToS D.host.F D.host.E a) = g (oToS D.host.F D.host.E a))
    (hg : ∀ p ∈ PP.asIdeal, g (oToS D.host.F D.host.E p) = 0) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    f s = g s := by
  obtain ⟨bq, hb⟩ := cmpS_surj (F := D.host.F) PP.asIdeal PP.ne_bot (Ideal.Quotient.mk _ s)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
  change Ideal.Quotient.mk _ (oToS D.host.F D.host.E b) = _ at hb
  have hb' : s - oToS D.host.F D.host.E b ∈ idS D.host.F PP.asIdeal := by
    rw [← Ideal.Quotient.eq]
    exact hb.symm
  have h1 := eq_of_kill PP f (fun p hp => (hfg p).trans (hg p hp)) s b hb'
  have h2 := eq_of_kill PP g hg s b hb'
  rw [h1, h2, hfg]

noncomputable def cjS (D : D7) : Formalism.L2.Herm.intAf D.host.F D.host.E →+* Formalism.L2.Herm.intAf D.host.F D.host.E :=
  (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D).restrict (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Herm.intAf D.host.F D.host.E)
    (fun _ h => GlobalTheory.AdIsom.cjA_mem h)

theorem cjS_oToS (a : 𝓞 D.host.E) :
    cjS D (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (GlobalTheory.IdemSupport.cO D a) := Subtype.ext rfl

theorem resT_cjA (PP : Pl D.host.E) (z : EAf D) :
    resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z) = conjRes PP (resT PP z) := by
  by_cases hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E
  · have hz' : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.AdIsom.cjA_mem hz
    rw [resT, dite_eq_left hz', resT, dite_eq_left hz]
    let f1 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
      (resS D.host.F (GlobalTheory.IdemSupport.cP PP)).comp (cjS D)
    let f2 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
      (conjRes PP).toRingHom.comp (resS D.host.F PP)
    have hO : ∀ a : 𝓞 D.host.E, f1 (oToS D.host.F D.host.E a) = f2 (oToS D.host.F D.host.E a) := by
      intro a
      show resS D.host.F (GlobalTheory.IdemSupport.cP PP) (cjS D (oToS D.host.F D.host.E a)) =
        conjRes PP (resS D.host.F PP (oToS D.host.F D.host.E a))
      rw [cjS_oToS, resS_oToS, resS_oToS]
      exact (Ideal.quotientEquiv_mk _ _ _ _ _).symm
    have hg : ∀ p ∈ PP.asIdeal, f2 (oToS D.host.F D.host.E p) = 0 := by
      intro p hp
      show conjRes PP (resS D.host.F PP (oToS D.host.F D.host.E p)) = 0
      rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    have hfin := ext_oToS PP f1 f2 hO hg ⟨z, hz⟩
    have e : (⟨GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z, hz'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = cjS D ⟨z, hz⟩ := Subtype.ext rfl
    rw [e]
    exact hfin
  · have hz' : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z ∉ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun h => hz (GlobalTheory.AdIsom.cjA_mem_iff.1 h)
    rw [resT, dite_eq_right hz', resT, dite_eq_right hz, map_zero]

theorem resCP_adjoint : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) (κ : GA D (Yc D 0)) (x y : Fin (Yc D 0).rank → EAf D), (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y)) = GlobalTheory.SeeConjChar.conjRes PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x))) := by
  intro D X h PP κ x y
  have hH : ∀ u v, GlobalTheory.SeeConjChar.hT X h u v =
      Formalism.UG.hform (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D) ((Yc D 0).gram.map (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D)) u v := by
    intro u v
    obtain ⟨⟨I⟩⟩ := X
    dsimp only at h
    subst h
    rfl
  have hU : finE (Yc D 0) κ ∈
      Formalism.UG.UJ (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D) ((Yc D 0).gram.map (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D)) := by
    have hf := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    rw [(Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ] at hf
    have := ((Formalism.IndefR.RationalEmbedding.iota D κ).2).2
    exact hf ▸ this
  have key : GlobalTheory.SeeConjChar.hT X h x ((finE (Yc D 0) κ).val *ᵥ y) =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D (GlobalTheory.SeeConjChar.hT X h y (((finE (Yc D 0) κ)⁻¹).val *ᵥ x)) := by
    rw [hH, hH]
    have e1 : x = (finE (Yc D 0) κ).val *ᵥ (((finE (Yc D 0) κ)⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have e2 := GlobalTheory.AdIsom.cjA_hA (Yc D 0) (((finE (Yc D 0) κ)⁻¹).val *ᵥ x) y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.hA] at e2
    rw [e2]
    conv_lhs => rw [e1]
    exact hform_unitary _ _ hU _ _
  rw [key]
  exact ⟨GlobalTheory.AdIsom.cjA_mem_iff, resT_cjA PP _⟩

end GlobalTheory.SeeConjAdj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianFormAdjointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_conjugatePlace_hermitianForm_adjoint : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) (κ : GA D (Yc D 0)) (x y : Fin (Yc D 0).rank → EAf D), (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y)) = GlobalTheory.SeeConjChar.conjRes PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x))) := by
  first | exact @GlobalTheory.SeeConjAdj.resCP_adjoint | exact GlobalTheory.SeeConjAdj.resCP_adjoint | (intros; apply GlobalTheory.SeeConjAdj.resCP_adjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateResidueFlagTermsReindexSymmetricEdge
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateResidueFlagTermsReindexSymmetricEdge
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjComb

open Classical

theorem sum_eq_of_inj {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (F : α → M) (G : β → M)
    (φ : α → β) (hφ : Function.Injective φ) (hval : ∀ x, F x = G (φ x)) (hs : ∀ b, G b ≠ 0 → ∃ x, φ x = b) :
    ∑ x, F x = ∑ b, G b :=
  Finset.sum_bij_ne_zero (fun x _ _ => φ x) (fun _ _ _ => Finset.mem_univ _) (fun _ _ _ _ _ _ h => hφ h)
    (fun b _ hb => by
      obtain ⟨x, rfl⟩ := hs b hb
      exact ⟨x, Finset.mem_univ _, by rw [hval]; exact hb, rfl⟩)
    (fun x _ _ => hval x)

theorem conj_residue_reindex : ∀ {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (ρ k : ℕ), n = 2 * ρ + k + 1 → r = n → ∀ U : GL (Fin n) κ, upperLeftBlock hr U ∈ unip κ r → ∀ (s : Bool) (fF fN : Fin ρ → Fin n) (gB : Fin k → Fin n), (∀ a, (fF a).1 = 2 * ρ + k - a.1) → (∀ a, (fN a).1 = if a.1 + 1 < ρ then 2 * ρ + k - (a.1 + 1) else ρ + k) → (∀ i, (gB i).1 = ρ + k - 1 - i.1) → (∑ a, (sgnD ρ k (fN a) : κ) * (U⁻¹).val (fN a) (fF a)) + (∑ i : Fin k, if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = ∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then ((GlobalTheory.SeeConjChar.wB ρ k s i j : ℤ) : κ) * (upperLeftBlock hr U).val i j else 0 := by
  intro κ _ n r hr ρ k hn hrn U hU s fF fN gB hfF hfN hgB
  subst hrn
  have hm : U ∈ blockTri (κ := κ) (blk2 r) := fun i j h => absurd h (by simp [blk2, i.2, j.2])
  have hR : upperLeftBlock hr U = U := Units.ext (Matrix.ext fun i j => by rw [upper_block_val_submatrix hr hm]; rfl)
  rw [hR] at hU ⊢
  have hUi : U⁻¹ ∈ unip κ r := inv_mem hU
  have hinv : ∀ p q : Fin r, q.1 = p.1 + 1 → (U⁻¹).val p q = - U.val p q := by
    intro p q hpq
    have hlt : p < q := by rw [Fin.lt_def]; omega
    have h := unip_mul_entry hUi hU hlt (fun l h1 h2 => by
      rw [Fin.lt_def] at h1 h2; omega)
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (ne_of_lt hlt)] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  obtain ⟨φ, hφl, hφr⟩ : ∃ φ : Fin ρ ⊕ Fin k → Fin r × Fin r, (∀ a, φ (Sum.inl a) = (fN a, fF a)) ∧
      (∀ i, φ (Sum.inr i) = (⟨ρ + k - 2 - i.1, by omega⟩, gB i)) := ⟨Sum.elim _ _, fun _ => rfl, fun _ => rfl⟩
  refine Eq.trans (Fintype.sum_sum_type (Sum.elim _ _)).symm ?_
  rw [← Fintype.sum_prod_type']
  refine sum_eq_of_inj _ _ φ ?_ ?_ ?_
  · rintro (a|i) (b|j) h
    · rw [hφl, hφl, Prod.mk.injEq] at h
      have h1 := hfF a; have h2 := hfF b; have h3 := congrArg Fin.val h.2
      exact congrArg Sum.inl (Fin.ext (by have := a.2; have := b.2; omega))
    · rw [hφl, hφr, Prod.mk.injEq] at h
      have h1 := hfF a; have h2 := hgB j; have h3 := congrArg Fin.val h.2
      exfalso; have := a.2; have := j.2; omega
    · rw [hφr, hφl, Prod.mk.injEq] at h
      have h1 := hfF b; have h2 := hgB i; have h3 := congrArg Fin.val h.2
      exfalso; have := b.2; have := i.2; omega
    · rw [hφr, hφr, Prod.mk.injEq] at h
      have h1 := hgB i; have h2 := hgB j; have h3 := congrArg Fin.val h.2
      exact congrArg Sum.inr (Fin.ext (by have := i.2; have := j.2; omega))
  · rintro (a|i)
    · rw [hφl]
      simp only [Sum.elim_inl]
      have h1 := hfF a; have h2 := hfN a; have ha := a.2
      by_cases hc : a.1 + 1 < ρ
      · rw [if_pos hc] at h2
        have hq : (fF a).1 = (fN a).1 + 1 := by omega
        have hs : symEdge ρ k (fN a) (fF a) := Or.inl ⟨hq, by omega, by omega⟩
        have hw : GlobalTheory.SeeConjChar.wB ρ k s (fN a) (fF a) = -1 := by
          unfold GlobalTheory.SeeConjChar.wB; split_ifs <;> omega
        have hd : (sgnD ρ k (fN a) : κ) = 1 := by unfold sgnD; rw [if_neg (by omega)]
        rw [if_pos hs, hw, hd, hinv _ _ hq]; push_cast; ring
      · rw [if_neg hc] at h2
        have hq : (fF a).1 = (fN a).1 + 1 := by omega
        have hs : symEdge ρ k (fN a) (fF a) := Or.inl ⟨hq, by omega, by omega⟩
        have hw : GlobalTheory.SeeConjChar.wB ρ k s (fN a) (fF a) = 1 := by
          unfold GlobalTheory.SeeConjChar.wB; split_ifs <;> omega
        have hd : (sgnD ρ k (fN a) : κ) = -1 := by unfold sgnD; rw [if_pos h2]
        rw [if_pos hs, hw, hd, hinv _ _ hq]; push_cast; ring
    · rw [hφr]
      show (if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = _
      have h1 := hgB i; have hi2 := i.2
      by_cases hi : i.1 + 1 < k
      · rw [dite_eq_left hi]
        have h3 := hgB ⟨i.1 + 1, hi⟩
        dsimp only at h3
        have hg : gB ⟨i.1 + 1, hi⟩ = ⟨ρ + k - 2 - i.1, by omega⟩ := Fin.ext (by dsimp only; omega)
        have hq : (gB i).1 = (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 := by dsimp only; omega
        have hs : symEdge ρ k (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) := Or.inl ⟨hq, by dsimp only; omega, by dsimp only; omega⟩
        have hd : (sgnD ρ k (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) : κ) = 1 := by
          unfold sgnD; rw [if_neg (by dsimp only; omega)]
        rw [hg, if_pos hs, hd, hinv _ _ hq]
        cases s
        · have hw : GlobalTheory.SeeConjChar.wB ρ k false (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) = -1 := by
            unfold GlobalTheory.SeeConjChar.wB
            rw [if_neg (show ¬ ((⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 < ρ) by dsimp only; omega), if_pos (show (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 < ρ + k by dsimp only; omega)]; rfl
          rw [hw]; simp
        · have hw : GlobalTheory.SeeConjChar.wB ρ k true (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) = 0 := by
            unfold GlobalTheory.SeeConjChar.wB
            rw [if_neg (show ¬ ((⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 < ρ) by dsimp only; omega), if_pos (show (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 < ρ + k by dsimp only; omega)]; rfl
          rw [hw]; simp
      · rw [dite_eq_right hi, if_neg]
        rintro (⟨h4, h5, h6⟩ | ⟨h4, h5⟩) <;> dsimp only at h4 h5 <;> omega
  · rintro ⟨p, q⟩ hne
    dsimp only at hne
    by_cases hs : symEdge ρ k p q
    swap
    · exact absurd (if_neg hs) hne
    rw [if_pos hs] at hne
    have hw : GlobalTheory.SeeConjChar.wB ρ k s p q ≠ 0 := fun h => hne (by rw [h]; simp)
    unfold GlobalTheory.SeeConjChar.wB at hw
    have hp2 := p.2; have hq2 := q.2
    rcases hs with ⟨hq, hp1, hp3⟩ | ⟨hp, hq⟩
    · by_cases h1 : p.1 < ρ
      · simp [h1] at hw
      by_cases h2 : p.1 + 1 < ρ + k
      · refine ⟨Sum.inr ⟨ρ + k - 2 - p.1, by omega⟩, ?_⟩
        rw [hφr, Prod.mk.injEq]
        have h3 := hgB ⟨ρ + k - 2 - p.1, by omega⟩
        dsimp only at h3
        exact ⟨Fin.ext (by dsimp only; omega), Fin.ext (by omega)⟩
      by_cases h3 : p.1 = ρ + k
      · refine ⟨Sum.inl ⟨ρ - 1, by omega⟩, ?_⟩
        rw [hφl, Prod.mk.injEq]
        have h4 := hfN ⟨ρ - 1, by omega⟩; have h5 := hfF ⟨ρ - 1, by omega⟩
        dsimp only at h4 h5
        rw [if_neg (by omega)] at h4
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · refine ⟨Sum.inl ⟨2 * ρ + k - 1 - p.1, by omega⟩, ?_⟩
        rw [hφl, Prod.mk.injEq]
        have h4 := hfN ⟨2 * ρ + k - 1 - p.1, by omega⟩; have h5 := hfF ⟨2 * ρ + k - 1 - p.1, by omega⟩
        dsimp only at h4 h5
        rw [if_pos (by omega)] at h4
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    · simp [show p.1 < ρ by omega] at hw

end GlobalTheory.SeeConjComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateResidueFlagTermsReindexSymmetricEdgeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateResidue_flagTerms_reindex_symmetricEdge : ∀ {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (ρ k : ℕ), n = 2 * ρ + k + 1 → r = n → ∀ U : GL (Fin n) κ, upperLeftBlock hr U ∈ unip κ r → ∀ (s : Bool) (fF fN : Fin ρ → Fin n) (gB : Fin k → Fin n), (∀ a, (fF a).1 = 2 * ρ + k - a.1) → (∀ a, (fN a).1 = if a.1 + 1 < ρ then 2 * ρ + k - (a.1 + 1) else ρ + k) → (∀ i, (gB i).1 = ρ + k - 1 - i.1) → (∑ a, (sgnD ρ k (fN a) : κ) * (U⁻¹).val (fN a) (fF a)) + (∑ i : Fin k, if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = ∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then ((GlobalTheory.SeeConjChar.wB ρ k s i j : ℤ) : κ) * (upperLeftBlock hr U).val i j else 0 := by
  first | exact @GlobalTheory.SeeConjComb.conj_residue_reindex | exact GlobalTheory.SeeConjComb.conj_residue_reindex | (intros; apply GlobalTheory.SeeConjComb.conj_residue_reindex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueOtherInstanceFormFrameStabilizerMulVec
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueOtherInstanceFormFrameStabilizerMulVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem cast_hA_add {I J : Formalism.MainNotions.S.AutInst} (e : I = J) (y z z' : Formalism.L2.SG.HidaSetting.VA J) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) (z + z'))) =
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z)) +
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z')) := by
  subst e
  simp only [cast_eq]
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem cast_hA_smul {I J : Formalism.MainNotions.S.AutInst} (e : I = J) (c : TensorProduct J.F J.E (Formalism.MainNotions.S.Af J.F))
    (y z : Formalism.L2.SG.HidaSetting.VA J) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) (c • z))) =
    c * cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z)) := by
  subst e
  simp only [cast_eq]
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hT_add' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (y z z' : Fin (Yc D 0).rank → EAf D) : hT X h y (z + z') = hT X h y z + hT X h y z' :=
  cast_hA_add h y z z'

theorem hT_smul' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (c : EAf D) (y z : Fin (Yc D 0).rank → EAf D) : hT X h y (c • z) = c * hT X h y z :=
  cast_hA_smul h c y z

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar
open Classical
theorem resT_of_mem' {D : D7} (PP : Pl D.host.E) (x : EAf D) (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resT PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := dif_pos hx
end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar.ResStab

open Classical Matrix

theorem mem_res_eq {R k : Type} [CommRing R] [CommRing k] {S : Subring R} (ρ : S →+* k) {x : R} (s : S)
    (hx : x = s) : ∃ hm : x ∈ S, ρ ⟨x, hm⟩ = ρ s := by
  subst hx
  exact ⟨s.2, rfl⟩

theorem res_conj_mulVec {R k : Type} [CommRing R] [CommRing k] (S : Subring R) (ρ : S →+* k) (r : R → k) (hr : ∀ x (hx : x ∈ S), r x = ρ ⟨x, hx⟩) {n : ℕ}
    (f : (Fin n → R) → R) (hadd : ∀ z z', f (z + z') = f z + f z') (hsmul : ∀ (c : R) z, f (c • z) = c * f z) (β : GL (Fin n) R) (Y : Matrix (Fin n) (Fin n) S) (w : Fin n → Fin n → R)
    (N : Matrix (Fin n) (Fin n) R)
    (hNY : N = (β : Matrix (Fin n) (Fin n) R) * Y.map S.subtype * ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))
    (hw : ∀ i j, ∃ hm : (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w j) i ∈ S,
      ρ ⟨_, hm⟩ = if i = j then 1 else 0)
    (hf : ∀ z, (∀ i, (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ z) i ∈ S) → f z ∈ S) (j : Fin n) :
    ∃ hx : f (N *ᵥ w j) ∈ S,
      ρ ⟨_, hx⟩ = ∑ l, r (f (w l)) * ρ (Y l j) := by
  subst hNY
  set B : Matrix (Fin n) (Fin n) R := (β : Matrix (Fin n) (Fin n) R) with hB
  set Bi : Matrix (Fin n) (Fin n) R := ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hBi
  have hBiB : Bi * B = 1 := by rw [hBi, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBBi : B * Bi = 1 := by rw [hBi, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one]

  let b : Fin n → Fin n → R := fun m i => B i m
  have hb : ∀ m, Bi *ᵥ b m = Pi.single m 1 := by
    intro m
    have : b m = B *ᵥ Pi.single m 1 := by
      funext i
      simp [b, Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, hBiB, Matrix.one_mulVec]
  have ht : ∀ m, f (b m) ∈ S := by
    intro m
    refine hf _ fun i => ?_
    rw [hb m]
    by_cases hi : i = m
    · subst hi; simp only [Pi.single_eq_same]; exact S.one_mem
    · rw [Pi.single_eq_of_ne hi]; exact S.zero_mem
  let t : Fin n → S := fun m => ⟨f (b m), ht m⟩

  have hdec : ∀ z, f z = ∑ m, (Bi *ᵥ z) m * f (b m) := by
    intro z
    have hz : z = ∑ m, (Bi *ᵥ z) m • b m := by
      funext i
      have := congrFun (show B *ᵥ (Bi *ᵥ z) = z by rw [Matrix.mulVec_mulVec, hBBi, Matrix.one_mulVec]) i
      rw [← this, Finset.sum_apply]
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, b]
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    let fl : (Fin n → R) →ₗ[R] R := ⟨⟨f, hadd⟩, hsmul⟩
    show fl z = _
    conv_lhs => rw [hz]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  have hval : ∀ z (v : Fin n → S), (∀ m, (Bi *ᵥ z) m = v m) → f z = ((∑ m, v m * t m : S) : R) := by
    intro z v hv
    rw [hdec z]
    push_cast
    exact Finset.sum_congr rfl fun m _ => by rw [hv m]

  let c : Fin n → Fin n → S := fun l i => ⟨(Bi *ᵥ w l) i, (hw i l).1⟩
  have hc : ∀ l i, ρ (c l i) = if i = l then 1 else 0 := fun l i => (hw i l).2

  have hwl : ∀ l, r (f (w l)) = ρ (t l) := by
    intro l
    obtain ⟨hm, e⟩ := mem_res_eq ρ _ (hval (w l) (c l) fun m => rfl)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hr _ hm, e, map_sum]
    simp only [map_mul, hc]
    simp

  have hN : ∀ m, (Bi *ᵥ ((B * Y.map S.subtype * Bi) *ᵥ w j)) m = ((∑ i, Y m i * c j i : S) : R) := by
    intro m
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBiB, Matrix.one_mul, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Subring.coe_subtype, c]
    push_cast
    rfl
  obtain ⟨hm, e⟩ := mem_res_eq ρ _ (hval _ (fun m => ∑ i, Y m i * c j i) hN)
  refine ⟨hm, ?_⟩
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hwl, map_sum, map_mul, hc]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end GlobalTheory.SeeConjChar.ResStab

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem resT_hT_mulVec_stab : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D), RedIs β PP w → ∀ N ∈ St β, ∀ y : Fin (Yc D 0).rank → EAf D, (∀ z : Fin (Yc D 0).rank → EAf D, (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h y z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ j, GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j))) = ∑ l, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (w l)) * (redFn β PP N).val l j := by
  intro D X h β PP w hw N hN y hy j
  obtain ⟨Y, rfl⟩ := hN
  have hval : (Formalism.L2.DIV.frGL β Y).val =
      β.val * Y.val.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).val := by
    simp only [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul]
    rfl
  have hred : ∀ l, ((Formalism.L2.DIV.redFn β PP (Formalism.L2.DIV.frGL β Y)).val l j) =
      Formalism.L2.DIV.resS D.host.F PP (Y.val l j) := by
    intro l
    rw [Formalism.L2.DIV.redFn_frGL]
    rfl
  obtain ⟨hm, e⟩ := ResStab.res_conj_mulVec (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.DIV.resS D.host.F PP) (resT PP) (resT_of_mem' PP)
    (hT X h y) (hT_add' X h y) (fun c z => hT_smul' X h c y z) β Y.val w _ hval hw hy j
  refine ⟨hm, ?_⟩
  exact (resT_of_mem' PP _ hm).trans (e.trans (Finset.sum_congr rfl fun l _ =>
    congrArg (fun t => resT PP (hT X h y (w l)) * t) (hred l).symm))

end GlobalTheory.SeeConjChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueOtherInstanceFormFrameStabilizerMulVecStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_otherInstanceForm_frameStabilizer_mulVec : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D), RedIs β PP w → ∀ N ∈ St β, ∀ y : Fin (Yc D 0).rank → EAf D, (∀ z : Fin (Yc D 0).rank → EAf D, (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h y z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ j, GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j))) = ∑ l, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (w l)) * (redFn β PP N).val l j := by
  first | exact @GlobalTheory.SeeConjChar.resT_hT_mulVec_stab | exact GlobalTheory.SeeConjChar.resT_hT_mulVec_stab | (intros; apply GlobalTheory.SeeConjChar.resT_hT_mulVec_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueOtherInstanceFormFlagPairingEqSignedDelta
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueOtherInstanceFormFlagPairingEqSignedDelta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem hT_eq_hY {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (x y : Fin (Yc D 0).rank → EAf D) : hT X h x y = hY D x y := by
  rcases X with ⟨⟨I⟩⟩
  dsimp only at h ⊢
  subst h
  rfl

theorem hY_pair_flag_int {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (PP : Pl D.host.E) (a c : Fin (Yc D 0).rank) :
    hY D (pairAt X h PP a) (flagAt X h PP c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨β₀, h₀⟩ := GlobalTheory.StdFrames.exists_base (Yc D 0)
  have hU := GlobalTheory.StdFrames.unimod_of_isSD (GlobalTheory.StdFrames.isSD_one h₀)
  have hF : ∀ i j, ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    have hF : Formalism.L2.DIV.IsFrame β₀ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := h₀ ▸ GlobalTheory.StdFrames.isFrame_lat β₀
    have hLf := GlobalTheory.KgFrame.Lf_eq D
    have key : ∀ v : Fin (Yc D 0).rank → EAf D, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf →
        Matrix.mulVec (β₀⁻¹).val v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro v hv
      rw [hLf] at hv
      exact (hF v).1 hv i
    set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf}
    have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
      show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
      exact zero_mem _
    obtain ⟨hef, hz, hbw⟩ := X.vectorsInLattice
    have he : ∀ a, e0T X h a ∈ S := cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
    have hf : ∀ a, f0T X h a ∈ S := cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
    have hb : ∀ a, bwT X h a ∈ S := cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
    have hbd : ∀ a, bwdT X h a ∈ S := cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
    have hzz : z0T X h ∈ S := cast_mem_Lf h X.z0 hz
    refine ⟨?_, ?_⟩
    · rw [colMat_entry]
      apply key
      unfold flagAt
      split_ifs
      · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf hb hzz j
      · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf (fun a => hbd _) hzz j
    · rw [colMat_entry]
      apply key
      unfold pairAt
      split_ifs
      · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz j
      · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun a => hb _) hzz j
  set U := colMat (pairAt X h PP) with hUdef
  set W := colMat (flagAt X h PP) with hWdef
  set J := GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram with hJ
  have e1 : hY D (pairAt X h PP a) (flagAt X h PP c) = (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a c := by
    simp only [Matrix.mul_apply, Formalism.UG.hform, Formalism.UG.cT, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply, hY]
    rw [Finset.sum_comm]
    rfl
  set A' := (β₀⁻¹).val * U with hAdef
  set B' := (β₀⁻¹).val * W with hBdef
  set G' := Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val with hGdef
  have hU' : U = β₀.val * A' := by rw [hAdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hW' : W = β₀.val * B' := by rw [hBdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hX' : Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W = Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A' * G' * B' := by
    rw [hGdef, hU', hW', GlobalTheory.StdFrames.cT_mul']
    simp only [Matrix.mul_assoc]
  rw [e1, hX']
  simp only [Matrix.mul_apply]
  refine sum_mem fun j _ => mul_mem (sum_mem fun i _ => mul_mem ?_ ?_) ?_
  · exact Formalism.UG.P.csDual_sig_mem _ (hF i a).2
  · exact hU.1 i j
  · exact (hF j c).1

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem resT_hT_pair_flag : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → ∀ PP ∈ R.Pg, ∀ a c : Fin (Yc D 0).rank, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) (flagAt X h PP c)) = if a = c then sgnD D.R.rS D.R.k a else 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R X h hL PP hPP a c
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    obtain ⟨l, hl⟩ := (hL.Pg PP).1 hPP
    have := R.C.P.overP hl
    rw [Nat.cast_mul]
    fin_cases l
    · exact PP.asIdeal.mul_mem_right _ this
    · exact PP.asIdeal.mul_mem_left _ this
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    have e := X.n_eq
    rw [h] at e
    have e2 := Formalism.L2.DIV.ranks_r_sym D
    change (Formalism.L2.SG.InstExistsPf.instOf D).n = _
    omega
  have hsm : SmallAt PP (hY D (pairAt X h PP a) (flagAt X h PP c) - if a = c then sgnD D.R.rS D.R.k a else 0) := by
    by_cases he : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1
    · unfold pairAt flagAt
      rw [if_pos he, if_pos he]
      exact flagV_pair_table (hY D) (SmallAt PP) _ _ _ hn _ _ _ _ _ (pairTable_of_cpt_one X h PP hg he) a c
    · unfold pairAt flagAt
      rw [if_neg he, if_neg he]
      exact flagV_pair_table (hY D) (SmallAt PP) _ _ _ hn _ _ _ _ _ (pairTable_rev X h PP hg he) a c
  have hint := hY_pair_flag_int X h PP a c
  have hs : (if a = c then sgnD D.R.rS D.R.k a else 0 : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    unfold sgnD
    split_ifs
    exacts [neg_mem (one_mem _), one_mem _, zero_mem _]
  have key : Formalism.L2.DIV.resS D.host.F PP ⟨_, hint⟩ - Formalism.L2.DIV.resS D.host.F PP ⟨_, hs⟩ = 0 := by
    rw [← map_sub]
    exact (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).2 hsm
  have hres : Formalism.L2.DIV.resS D.host.F PP ⟨_, hs⟩ = if a = c then sgnD D.R.rS D.R.k a else 0 := by
    by_cases hac : a = c
    · subst hac
      by_cases hz : a.1 = D.R.rS + D.R.k
      · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = -1 := Subtype.ext (by simp [sgnD, hz])
        rw [e, map_neg, map_one]
        simp [sgnD, hz]
      · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 := Subtype.ext (by simp [sgnD, hz])
        rw [e, map_one]
        simp [sgnD, hz]
    · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 0 := Subtype.ext (by simp [hac])
      rw [e, map_zero]
      simp [hac]
  unfold resT
  rw [hT_eq_hY, dite_eq_left hint, ← hres]
  exact sub_eq_zero.1 key

end GlobalTheory.SeeConjChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueOtherInstanceFormFlagPairingEqSignedDeltaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_otherInstanceForm_flagPairing_eq_signedDelta : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → ∀ PP ∈ R.Pg, ∀ a c : Fin (Yc D 0).rank, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) (flagAt X h PP c)) = if a = c then sgnD D.R.rS D.R.k a else 0 := by
  first | exact @GlobalTheory.SeeConjChar.resT_hT_pair_flag | exact GlobalTheory.SeeConjChar.resT_hT_pair_flag | (intros; apply GlobalTheory.SeeConjChar.resT_hT_pair_flag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceCharacterArgumentSignedSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar.AtConj

theorem resT_of_mem {D : D7} (PP : Pl D.host.E) {x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resT PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := by
  unfold resT; rw [dite_eq_left hx]

theorem resT_zero {D : D7} (PP : Pl D.host.E) : resT PP (0 : EAf D) = 0 := by
  rw [resT_of_mem PP (zero_mem _)]
  exact map_zero (Formalism.L2.DIV.resS D.host.F PP)

theorem resT_add {D : D7} (PP : Pl D.host.E) {x y : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hy : y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resT PP (x + y) = resT PP x + resT PP y := by
  rw [resT_of_mem PP hx, resT_of_mem PP hy, resT_of_mem PP (add_mem hx hy)]
  exact map_add (Formalism.L2.DIV.resS D.host.F PP) ⟨x, hx⟩ ⟨y, hy⟩

theorem resT_sum {D : D7} (PP : Pl D.host.E) {ι : Type} [Fintype ι] (f : ι → EAf D)
    (hf : ∀ i, f i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resT PP (∑ i, f i) = ∑ i, resT PP (f i) := by
  have hs : (∑ i, f i) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := sum_mem fun i _ => hf i
  rw [resT_of_mem PP hs]
  have e : (⟨∑ i, f i, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ i, (⟨f i, hf i⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) := by
    apply Subtype.ext
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  exact Finset.sum_congr rfl fun i _ => (resT_of_mem PP (hf i)).symm

theorem flagV_f {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ + k < i.1) (h2 : i.1 < 2 * ρ + k + 1) :
    GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = f ⟨2 * ρ + k - i.1, by omega⟩ := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h2]

theorem symmetricFlagBasisVectors_apply_middle {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : i.1 = ρ + k) : GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = z := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h1]

theorem flagV_b {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ ≤ i.1) (h2 : i.1 < ρ + k) : GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = b ⟨i.1 - ρ, by omega⟩ := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_left h2]

end GlobalTheory.SeeConjChar.AtConj

open GlobalTheory.SeeConjChar GlobalTheory.SeeConjChar.AtConj

theorem GlobalTheory.SeeConjChar.resT_cP_argT : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = GlobalTheory.SeeConjChar.conjRes PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wB D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hGrp β hβ hred PP hP κ hS hK2
  classical
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    have e := X.n_eq
    rw [h] at e
    have e2 := Formalism.L2.DIV.ranks_r_sym D
    change (Formalism.L2.SG.InstExistsPf.instOf D).n = _
    omega
  have hrn : D.R.r = (Yc D 0).rank := by
    have e := X.n_eq
    rw [h] at e
    change D.R.r = (Formalism.L2.SG.InstExistsPf.instOf D).n
    omega
  have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
  have hU : upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unip (kP PP) D.R.r :=
    unipCol_le _ _ _ (((GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions R F X h hL hGrp β hβ hred κ hK hS).1 hK2) PP hP)
  have hMinv : (finE (Yc D 0) κ)⁻¹ ∈ St β := inv_mem hS
  have hredinv : redFn β PP (finE (Yc D 0) κ)⁻¹ = (redFn β PP (finE (Yc D 0) κ))⁻¹ := extendOne_inv _ hS
  have hC : ∀ a j, hT X h (flagAt X h PP j) (Matrix.mulVec (finE (Yc D 0) κ).val (pairAt X h PP a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (hT X h (flagAt X h PP j) (Matrix.mulVec (finE (Yc D 0) κ).val (pairAt X h PP a))) =
        conjRes PP ((sgnD D.R.rS D.R.k a : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val a j) := by
    intro a j
    have c1 := GlobalTheory.T.residue_conjugatePlace_hermitianForm_adjoint X h PP κ (flagAt X h PP j) (pairAt X h PP a)
    have c2 := GlobalTheory.T.residue_otherInstanceForm_frameStabilizer_mulVec X h β PP (flagAt X h PP) (hred PP hP) _ hMinv (pairAt X h PP a) (GlobalTheory.T.otherInstanceForm_flagPairing_integral_on_frameLattice X h β hβ PP a) j
    refine ⟨c1.1.2 c2.1, ?_⟩
    rw [c1.2, c2.2, hredinv]
    congr 1
    simp only [GlobalTheory.T.residue_otherInstanceForm_flagPairing_eq_signedDelta R X h hL PP hP a, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  let fF : Fin D.R.rS → Fin (Yc D 0).rank := fun a => ⟨2 * D.R.rS + D.R.k - a.1, by have := a.2; omega⟩
  let fN : Fin D.R.rS → Fin (Yc D 0).rank := fun a =>
    ⟨if a.1 + 1 < D.R.rS then 2 * D.R.rS + D.R.k - (a.1 + 1) else D.R.rS + D.R.k, by have := a.2; split_ifs <;> omega⟩
  let gB : Fin D.R.k → Fin (Yc D 0).rank := fun i => ⟨D.R.rS + D.R.k - 1 - i.1, by have := i.2; omega⟩
  have hF : ∀ a, f0T X h a = flagAt X h PP (fF a) := by
    intro a
    have ha := a.2
    have e : (fF a).1 = 2 * D.R.rS + D.R.k - a.1 := rfl
    have h1 : D.R.rS + D.R.k < (fF a).1 := by omega
    have h2 : (fF a).1 < 2 * D.R.rS + D.R.k + 1 := by omega
    unfold flagAt
    split_ifs <;> rw [flagV_f _ _ _ _ _ h1 h2] <;> congr 1 <;> ext <;> simp only [e] <;> omega
  have hNx : ∀ a, Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a = pairAt X h PP (fN a) := by
    intro a
    have ha := a.2
    have e : (fN a).1 = if a.1 + 1 < D.R.rS then 2 * D.R.rS + D.R.k - (a.1 + 1) else D.R.rS + D.R.k := rfl
    unfold Formalism.L2.SG.HidaSetting.nxt
    by_cases hlt : a.1 + 1 < D.R.rS
    · rw [dite_eq_left hlt]
      rw [if_pos hlt] at e
      have h1 : D.R.rS + D.R.k < (fN a).1 := by omega
      have h2 : (fN a).1 < 2 * D.R.rS + D.R.k + 1 := by omega
      unfold pairAt
      split_ifs <;> rw [flagV_f _ _ _ _ _ h1 h2] <;> congr 1 <;> ext <;> simp only [e] <;> omega
    · rw [dite_eq_right hlt]
      rw [if_neg hlt] at e
      unfold pairAt
      split_ifs <;> rw [symmetricFlagBasisVectors_apply_middle _ _ _ _ _ e]
  have hBd : GlobalTheory.SeeConjChar.sideAt X h PP ≠ true → ∀ i, bwdT X h i = flagAt X h PP (gB i) := by
    intro hs i
    have hi := i.2
    have e : (gB i).1 = D.R.rS + D.R.k - 1 - i.1 := rfl
    have hs' : ¬ GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by simpa [GlobalTheory.SeeConjChar.sideAt] using hs
    unfold flagAt
    rw [if_neg hs', flagV_b _ _ _ _ _ (by omega) (by omega)]
    congr 1; ext; simp only [e, Fin.val_rev]; omega
  have hBw : GlobalTheory.SeeConjChar.sideAt X h PP ≠ true → ∀ i : Fin D.R.k, bwT X h i = pairAt X h PP (gB i) := by
    intro hs i
    have hi := i.2
    have e : (gB i).1 = D.R.rS + D.R.k - 1 - i.1 := rfl
    have hs' : ¬ GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by simpa [GlobalTheory.SeeConjChar.sideAt] using hs
    unfold pairAt
    rw [if_neg hs', flagV_b _ _ _ _ _ (by omega) (by omega)]
    congr 1; ext; simp only [e, Fin.val_rev]; omega

  have hfterm : ∀ a, hT X h (f0T X h a) (Matrix.mulVec (finE (Yc D 0) κ).val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (hT X h (f0T X h a) (Matrix.mulVec (finE (Yc D 0) κ).val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a))) =
        conjRes PP ((sgnD D.R.rS D.R.k (fN a) : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val (fN a) (fF a)) := by
    intro a
    rw [hF a, hNx a]
    exact hC _ _
  have hbterm : ∀ i : Fin D.R.k, (if hi : i.1 + 1 < D.R.k then hT X h (bwdT X h i) (Matrix.mulVec (finE (Yc D 0) κ).val (bwT X h ⟨i.1 + 1, hi⟩)) else 0) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (if hi : i.1 + 1 < D.R.k then hT X h (bwdT X h i) (Matrix.mulVec (finE (Yc D 0) κ).val (bwT X h ⟨i.1 + 1, hi⟩)) else 0) =
        conjRes PP (if hi : i.1 + 1 < D.R.k then (if GlobalTheory.SeeConjChar.sideAt X h PP then 0 else (sgnD D.R.rS D.R.k (gB ⟨i.1 + 1, hi⟩) : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) := by
    intro i
    by_cases hi : i.1 + 1 < D.R.k
    · rw [dite_eq_left hi, dite_eq_left hi]
      by_cases hs : GlobalTheory.SeeConjChar.sideAt X h PP = true
      · rw [if_pos hs]
        obtain ⟨h1, h2⟩ := GlobalTheory.T.residue_conjugatePlace_hermitian_dualBasis_stabiliser_eq_zero X h β hβ PP hs _ hS i ⟨i.1 + 1, hi⟩
        exact ⟨h1, by rw [h2, map_zero]⟩
      · rw [if_neg hs, hBd hs i, hBw hs ⟨i.1 + 1, hi⟩]
        exact hC _ _
    · rw [dite_eq_right hi, dite_eq_right hi]
      exact ⟨zero_mem _, by rw [map_zero, resT_zero]⟩
  unfold argT
  set_option synthInstance.maxHeartbeats 100000 in
    rw [resT_add _ (sum_mem fun a _ => (hfterm a).1) (sum_mem fun i _ => (hbterm i).1), resT_sum _ _ (fun a => (hfterm a).1),
    resT_sum _ _ (fun i => (hbterm i).1), Finset.sum_congr rfl fun a _ => (hfterm a).2,
    Finset.sum_congr rfl fun i _ => (hbterm i).2, ← map_sum, ← map_sum, ← map_add]
  congr 1
  exact GlobalTheory.T.conjugateResidue_flagTerms_reindex_symmetricEdge (r_le_Y (D := D) 0) D.R.rS D.R.k hn hrn _ hU (GlobalTheory.SeeConjChar.sideAt X h PP) fF fN gB (fun a => rfl) (fun a => rfl) (fun i => rfl)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceCharacterArgumentSignedSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_conjugatePlace_characterArgument_signedSum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = GlobalTheory.SeeConjChar.conjRes PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wB D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  first | exact @GlobalTheory.SeeConjChar.resT_cP_argT | exact GlobalTheory.SeeConjChar.resT_cP_argT | (intros; apply GlobalTheory.SeeConjChar.resT_cP_argT <;> assumption)
end
