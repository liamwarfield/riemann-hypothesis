module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMoveArgumentsLastRowVertex
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConjLevelMovesVacuumByCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingColumnArgsMovedPointConjAtPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionMovesStandardVacuumTopNodeEqCharSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTupleHeckeCharacterDetIdeleEqProdLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtIdempotentIdempotentPartCompon
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtIdempotentIdempotentPartCompon
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
noncomputable section

namespace GlobalTheory.TopLevelInv

variable {D : D7}

theorem infPart_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) : infPart D e = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hs := map_sum (infPart D).toAddMonoidHom es P
  change (infPart D).toAddMonoidHom _ = 0
  rw [hs]
  exact Finset.sum_eq_zero fun PP hPP =>
    (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) (hes PP hPP)).1

open Classical in
theorem cpt_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hs := map_sum ((GlobalTheory.StdFrames.cpt Q).comp (toEAf D)).toAddMonoidHom es P
  change ((GlobalTheory.StdFrames.cpt Q).comp (toEAf D)).toAddMonoidHom _ = _
  rw [hs]
  have h : ∀ PP ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (es PP)) = if PP = Q then 1 else 0 := fun PP hPP => by
    by_cases hQ : PP = Q
    · subst hQ; rw [if_pos rfl]; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).1
    · rw [if_neg hQ]; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).2 Q (Ne.symm hQ)
  calc _ = ∑ PP ∈ P, (if PP = Q then (1 : Q.adicCompletion D.host.E) else 0) := Finset.sum_congr rfl h
    _ = _ := by rw [Finset.sum_ite_eq']

theorem cpt_one_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∈ P) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = 1 := by
  classical
  rw [cpt_of_isIdemSum he, if_pos hQ]

theorem cpt_zero_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∉ P) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = 0 := by
  classical
  rw [cpt_of_isIdemSum he, if_neg hQ]

theorem map_unitMix_of_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (e x : R) (h : φ e = 0) :
    φ (e * x + (1 - e)) = 1 := by
  rw [map_add (f := _), map_mul, map_sub, map_one, h]; ring

set_option maxHeartbeats 1000000 in
theorem detAt_cutPart_parts {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (V : HSp D) (g : GA D V) :
    infPart D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D) = 1 ∧
    (∀ Q ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V
      (cutPart (e + cA D e) V g) : AE D)) = ((Formalism.L2.Theta.mt V g).map fun z => GlobalTheory.StdFrames.cpt Q (toEAf D z)).det) ∧
    ∀ Q ∉ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V
      (cutPart (e + cA D e) V g) : AE D)) = 1 := by
  have hee : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have hc : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hc
  have hval : (GlobalTheory.VecInv.detAt e hee V (cutPart (e + cA D e) V g) : AE D) =
      e * (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det + (1 - e) := rfl
  rw [hval]
  have hinf := infPart_of_isIdemSum he
  refine ⟨?_, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hinf, zero_mul, zero_add, sub_zero]
  · let φ : AE D →+* Q.adicCompletion D.host.E := (GlobalTheory.StdFrames.cpt Q).comp (toEAf D)
    have h1 : φ e = 1 := cpt_one_of_isIdemSum he hQ
    have h2 : φ (cA D e) = 0 := by
      have := congrArg φ hc
      rwa [RingHom.map_mul, RingHom.map_zero, h1, one_mul] at this
    have h3 : φ (e + cA D e) = 1 := by rw [RingHom.map_add (f := _), h1, h2, add_zero]
    change φ _ = ((Formalism.L2.Theta.mt V g).map φ).det
    rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h1, one_mul, sub_self, add_zero,
      RingHom.map_det, mt_cutPart hf.1 hf.2]
    congr 1
    refine Matrix.ext fun i j => ?_
    change φ ((e + cA D e) * Formalism.L2.Theta.mt V g i j + (1 - (e + cA D e)) * (1 : Matrix _ _ (AE D)) i j) = φ (Formalism.L2.Theta.mt V g i j)
    rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h3, one_mul, sub_self,
      zero_mul, add_zero]
  · let φ : AE D →+* Q.adicCompletion D.host.E := (GlobalTheory.StdFrames.cpt Q).comp (toEAf D)
    have h1 : φ e = 0 := cpt_zero_of_isIdemSum he hQ
    change φ _ = 1
    exact map_unitMix_of_zero φ e _ h1

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtIdempotentIdempotentPartComponStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantIdeleAtIdempotent_idempotentPart_components : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (V : HSp D) (g : GA D V), infPart D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D) = 1 ∧ (∀ Q ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D)) = ((Formalism.L2.Theta.mt V g).map fun z => GlobalTheory.StdFrames.cpt Q (toEAf D z)).det) ∧ ∀ Q ∉ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D)) = 1 := by
  first | exact @GlobalTheory.TopLevelInv.detAt_cutPart_parts | exact GlobalTheory.TopLevelInv.detAt_cutPart_parts | (intros; apply GlobalTheory.TopLevelInv.detAt_cutPart_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTupleHeckeCharacterDetIdeleEqProdLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.TopLevelInv

theorem chrEq_mu_succ_succ : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (j : ℕ), j + 1 < D.R.m → ChrEq (L.mu t (j + 1 + 1)) (muBase L (j + 1 + 1) * L.xiH t) ∧ ∀ P, (muBase L (j + 1 + 1) * L.xiH t).TameAt P := by
  intro D T L μ₀ hL t j hj
  have hm : ChrEq (L.mu0 (j + 1 + 1)) (muBase L (j + 1 + 1)) := by
    have := hL.mu0 ⟨j + 1, hj⟩
    simpa [muBase, hj] using this
  refine ⟨GlobalTheory.TowerCharRead.chrEq_mul hm (hL.xi t), fun P => ?_⟩
  have h1 : (muBase L (j + 1 + 1)).TameAt P := by
    rw [muBase, dite_eq_left hj]; exact (L.C.isMu0 ⟨j + 1, hj⟩).tame P
  exact Formalism.L2.Host.HChar.LevelLe.mul h1 (hL.xi_tame t P)

theorem mu_detAt_eq_prod_loc : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he
  obtain ⟨hχ, htame⟩ := chrEq_mu_succ_succ hL t j hj
  obtain ⟨hinf, hin, hout⟩ := GlobalTheory.T.determinantIdeleAtIdempotent_idempotentPart_components he (G.V (.top (j + 1)))
    ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))
  rw [GlobalTheory.T.unitaryIdeleChar_eq_prod_loc_of_tameAt hχ (locPl G t) (fun P _ => htame P) (fun P => gdet (kapAt S t j hj k P)) _ hinf
    (fun P hP => (hin P hP).trans (GlobalTheory.T.det_unitaryConj_atPlace_eq_det_latticeBasisComponent S t j hj k _ P)) hout]
  rw [← Finset.prod_coe_sort]
  rfl

end GlobalTheory.TopLevelInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTupleHeckeCharacterDetIdeleEqProdLocalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridTupleHeckeCharacter_detIdele_eq_prod_local : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TopLevelInv.mu_detAt_eq_prod_loc | exact GlobalTheory.TopLevelInv.mu_detAt_eq_prod_loc | (intros; apply GlobalTheory.TopLevelInv.mu_detAt_eq_prod_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacePartFixesStandardVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacePartFixesStandardVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.OffPartVac

theorem unrOff_mu_locPl {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (j : Fin D.R.m) {e : AE D} (he : IsIdemSum e (locPl G t)) : Formalism.IndefR.Fin.UnrOff e (L.mu t ((j : ℕ) + 1)) := by

  have hbase : GlobalTheory.VecInv.UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1)) := by
    refine GlobalTheory.ChrOff.unrOff_of_unrAt D _ (L.C.mu0 j) (locPl G t) e (hL.mu0 j) he ?_
    intro Q hQ hQc
    by_cases hg : ∀ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal
    · exact (L.C.isMu0 j).unr Q hg
    · exfalso
      push Not at hg
      obtain ⟨k, hk⟩ := hg
      have hk' := (GlobalTheory.FunObj.Good.natCast_mem_under Q (D.host.g k)).2 hk
      have hS1 : Q.under (𝓞 D.host.F) ∈ S1 D := by
        rw [GlobalTheory.ChiGrid.S1_mem_OmF]
        fin_cases k
        · exact Or.inl hk'
        · exact Or.inr (Or.inl hk')
      have hS0 : Q.under (𝓞 D.host.F) ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)
      have hW0 : G.pl.w (Q.under (𝓞 D.host.F)) ∈ G.pl.W0 := by
        classical
        exact Finset.mem_image_of_mem _ hS0
      have hw : G.pl.w (Q.under (𝓞 D.host.F)) ∈ locPl G t := GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inl hW0)
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP (G.pl.under_w hS0).symm with h | h
      · exact hQ (by rw [h]; exact hw)
      · exact hQc _ hw ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 h)

  have htw : GlobalTheory.VecInv.UnrOff (e + cA D e) (L.xi t) := by
    refine GlobalTheory.ChrOff.unrOff_of_unrAt D _ (L.xiH t) (locPl G t) e (hL.xi t) he ?_
    intro Q hQ hQc
    by_contra hr
    rcases (hL.Q_ram t Q).1 hr with hq | ⟨Q', hQ', hc⟩
    · exact hQ (GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inr hq))
    · exact hQc Q' (GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inr hQ')) hc
  intro x h1 h2 h3 h4
  show (L.mu0 ((j : ℕ) + 1) * L.xi t) x = 1
  rw [MonoidHom.mul_apply, hbase x h1 h2 h3 h4, htw x h1 h2 h3 h4, one_mul]

private theorem cut_one_sub_eq_resG_one_sub_of_isIdempotentElem {D : D7} (V : HSp D) {ε : AF D.host.F} (hε : IsIdempotentElem ε) {f : AE D}
    (hf : algebraMap (AF D.host.F) (AE D) ε = f) (g : GA D V) :
    cutPart (1 - f) V g = Formalism.IndefR.Fin.LevelGroupLemmas.resG V (1 - ε) g := by
  have hid : IsIdempotentElem (1 - ε) := hε.one_sub
  have ha : algebraMap (AF D.host.F) (AE D) (1 - ε) = 1 - f := by rw [map_sub, map_one, hf]
  have h1 : (1 - f) * (1 - f) = 1 - f := by rw [← ha, ← map_mul, hid.eq]
  have h2 : cA D (1 - f) = 1 - f := by rw [← ha, GlobalTheory.IdemSupport.cA_algebraMap]
  apply Subtype.ext
  apply Units.ext
  change Formalism.L2.Theta.mt V _ = Formalism.L2.Theta.mt V _
  rw [mt_cutPart h1 h2, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG' hid, ha]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem cut_conj_unipotent_mem_St_succ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.top (j + 1))) (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) {e : AE D}
    (he : IsIdemSum e (locPl G t)) :
    Lev.finE (G.V (.top (j + 1))) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1)))
      ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))
      ∈ Formalism.L2.DIV.St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) := by
  have hlev : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) _ _ := hk
  refine GlobalTheory.OffPartLattice.finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (finG (G.V (.top (j + 1))) k) _ ?_ he ?_
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, finG, MonoidHom.comp_apply, Subgroup.coe_subtype]
  · intro Q hQ
    have h2 := (Subgroup.mem_inf.1 hlev).2
    exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 Q) hQ)

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.OffPartLattice in
theorem offPart_fixes_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))), 1) (S.Z.vac (.top t (j + 1))) = S.Z.vac (.top t (j + 1)) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he

  have hv := S.Z.vac_is (.top t (j + 1)) hj
  unfold IsVacO at hv
  obtain ⟨_, hv2⟩ := hv
  obtain ⟨_, hθ, hlat, _, hcov, hnrm⟩ := hv2

  obtain ⟨⟨es, hes, hesum⟩, hc⟩ := id he
  have hε : IsIdempotentElem (Formalism.IndefR.Fin.LevelGroupLemmas.epsP (locPl G t)) :=
    Formalism.IndefR.Fin.LevelGroupLemmas.isIdempotentElem_placeIdempotent hes hesum hc _ subset_rfl
  have halg := Formalism.IndefR.Fin.LevelGroupLemmas.algebraMap_epsP hes hesum
  set ε := Formalism.IndefR.Fin.LevelGroupLemmas.epsP (locPl G t)
  have hid : IsIdempotentElem (1 - ε) := hε.one_sub

  have hle1 : j + 1 ≤ D.R.m := by omega
  have hle2 : j + 1 + 1 ≤ D.R.m := hj
  have hr1 := rank_top G hle1
  have hr2 := rank_top G hle2

  set V := G.V (.top (j + 1))
  set g : GA D V := (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D V)
  have hgf : g ∈ GfC V := ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2
  have hcut : cutPart (1 - (e + cA D e)) V g = Formalism.IndefR.Fin.LevelGroupLemmas.resG V (1 - ε) g :=
    cut_one_sub_eq_resG_one_sub_of_isIdempotentElem V hε halg g

  have hnodd : ¬ Odd (G.pS (Pair.top t (j + 1))).rank := by
    rw [Nat.not_odd_iff_even]
    change Even (G.V (.top (j + 1))).rank
    rw [hr1]
    exact rankX_even D _
  have hnodd' : ¬ Odd (G.pT (Pair.top t (j + 1))).rank := by
    rw [Nat.not_odd_iff_even]
    change Even (G.V (.top (j + 1 + 1))).rank
    rw [hr2]
    exact rankX_even D _
  have hmu : Formalism.IndefR.Fin.UnrOff e (L.mu t (j + 1 + 1)) := unrOff_mu_locPl G hL t ⟨j + 1, hj⟩ he
  have hchS : G.chrS (Pair.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, hnodd, if_false]
    rfl
  have hchT : G.chrT (Pair.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, hnodd', if_false]
    rfl

  have hfrS := isFrame_moved (S.N.latS (Pair.top t (j + 1))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE V (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hle1) (S.N.u_lat (.top (j + 1)) hle1)
  have hfrT := isFrame_moved (S.N.latT (Pair.top t (j + 1))) (G.Λ (.top (j + 1 + 1))) (S.βp (j + 1 + 1))
    (Lev.finE (G.V (.top (j + 1 + 1))) (S.N.u (.top (j + 1 + 1))).1) (S.βp_is (j + 1 + 1) hle2)
    (S.N.u_lat (.top (j + 1 + 1)) hle2)
  have hst := cut_conj_unipotent_mem_St_succ S j hj k hk he

  have hVF := Formalism.IndefR.Fin.LevelGroupLemmas.vacFixOff (Formalism.IndefR.Fin.splitLinF D) (Formalism.IndefR.Fin.placeModelAtF D)
    (Formalism.IndefR.Fin.splitOrInert D)
  have hW := W.om_is (Pair.top t (j + 1)) hle2
  refine hVF W.ψ _ _ _ _ _ hW (GlobalTheory.InertAll.inertAllO D _ _ _ _ _ _ hW) ?_ ?_ _ _
    (GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ hle1))
    (GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ hle2))
    _ _ hfrS hfrT (locPl G t) e he (by rw [hchS]; exact hmu) (by rw [hchT]; exact hmu) _ hθ hlat ?_ _ 1 ?_
    (Subgroup.one_mem _) hst (by rw [map_one]; exact Subgroup.one_mem _) ?_ ?_
  · change (G.V (.top (j + 1))).rank ≠ (G.V (.top (j + 1 + 1))).rank
    rw [hr1, hr2]
    unfold GlobalTheory.ChiGrid.rankX
    rw [add_mul (j + 1) 1, one_mul]
    generalize (j + 1) * (D.R.t + 1) = a
    omega
  · left
    change Even (G.V (.top (j + 1))).rank
    rw [hr1]
    exact rankX_even D _
  · obtain ⟨⟨μ, 𝓕⟩, hμ⟩ := hcov
    exact ⟨μ, 𝓕, hμ, hnrm ⟨μ, 𝓕⟩ hμ⟩
  · change cutPart (1 - (e + cA D e)) V g ∈ GfC V
    rw [hcut]
    exact Formalism.IndefR.Fin.LevelGroupLemmas.resG_mem_GfC V hid hgf
  · intro i j'
    change (e + cA D e) * (Formalism.L2.Theta.mt V (cutPart (1 - (e + cA D e)) V g) - 1) i j' = 0
    rw [hcut, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG_sub hid, ← mul_assoc, ← halg, ← map_mul, mul_sub, mul_one, hε.eq,
      sub_self, map_zero, zero_mul]
  · intro i j'
    simp [Formalism.L2.Theta.mt]

end GlobalTheory.OffPartVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacePartFixesStandardVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offPlacePart_fixes_standardVacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))), 1) (S.Z.vac (.top t (j + 1))) = S.Z.vac (.top t (j + 1)) := by
  first | exact @GlobalTheory.OffPartVac.offPart_fixes_vac | exact GlobalTheory.OffPartVac.offPart_fixes_vac | (intros; apply GlobalTheory.OffPartVac.offPart_fixes_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusConjLevelDetEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusConjLevelDetEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.DetIdeleUnit

open _root_.Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem val_eq_one_of_le {a b : WithZero (Multiplicative ℤ)} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 :=
  le_antisymm ha (by
    calc (1 : WithZero (Multiplicative ℤ)) = a * b := h.symm
      _ ≤ a := mul_le_of_le_one_right' hb)

theorem valued_isInt {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Fv D.host.F v}
    (h : GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) x) : Valued.v x ≤ 1 := by
  obtain ⟨o, rfl⟩ := h
  exact o.2

theorem chart_val_eq_one {es : AE D} {PP : Pl D.host.E} (he : IsIdemAt es PP) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart es v π) {c c' : AE D} (hcc : c * c' = 1)
    (hc : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : Valued.v (π c) = 1 := by
  obtain ⟨φ, hφ, hint, -⟩ := GlobalTheory.ChartLevels.chart_levels D es PP v π he hπ
  have hc' : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c')) = 1 := by
    have h1 : GlobalTheory.StdFrames.cpt PP (toEAf D c) * GlobalTheory.StdFrames.cpt PP (toEAf D c') = 1 := by
      rw [← map_mul, ← map_mul, hcc, map_one, map_one]
    have h2 := congrArg Valued.v h1
    rw [map_mul, hc, one_mul, map_one] at h2
    exact h2
  have key : ∀ y : AE D, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D y)) = 1 → Valued.v (π y) ≤ 1 := by
    intro y hy
    rw [← hφ]
    refine valued_isInt ((hint _).1 ((GlobalTheory.AdIsom.mem_OA _).2 fun Q => ?_))
    rw [map_mul]
    by_cases hQ : Q = PP
    · subst hQ; rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).1, one_mul, hy]
    · rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 Q hQ, zero_mul, map_zero]; exact zero_le'
  refine val_eq_one_of_le (key c hc) (key c' hc') ?_
  rw [← map_mul, ← map_mul, hcc, map_one, map_one]

theorem absFin_single {es : AE D} {PP : Pl D.host.E} (he : IsIdemAt es PP) (u : (AE D)ˣ) (c : AE D)
    (hu : (u : AE D) = es * c + (1 - es)) (c' : AE D) (hcc : c * c' = 1)
    (hc : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D u = 1 := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart es he.1
  have hee : es * es = es := he.1.1
  have hu1 : (1 - es) * (u : AE D) = 1 - es := by rw [hu]; linear_combination (1 - c) * hee
  rw [GlobalTheory.SplitLinear.absFin_split D es v π he.1 hπ u hu1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  have hπu : π (u : AE D) = π c := by
    rw [hu, map_add (f := _), map_mul, map_sub, map_one, hπ.map_e hee, one_mul, sub_self, add_zero]
  change ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v (π (u : AE D)))) = 1
  rw [hπu, chart_val_eq_one he hπ hcc hc, WithZero.log_one, zpow_zero]

theorem absFin_idemSum_eq_one {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (x : (AE D)ˣ) (c c' : AE D)
    (hcc : c * c' = 1) (hx : (x : AE D) = e * c + (1 - e))
    (hc : ∀ PP ∈ P, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = 1 := by
  obtain ⟨⟨es, hes, hae⟩, -⟩ := he
  let u : {PP // PP ∈ P} → (AE D)ˣ := fun PP =>
    { val := es PP.1 * c + (1 - es PP.1)
      inv := es PP.1 * c' + (1 - es PP.1)
      val_inv := GlobalTheory.SplitIdeleModulus.unit_aux (hes PP.1 PP.2).1.1 hcc
      inv_val := GlobalTheory.SplitIdeleModulus.unit_aux (hes PP.1 PP.2).1.1 (by rw [mul_comm]; exact hcc) }
  have hx' : x = ∏ PP ∈ P.attach, u PP := by
    apply Units.ext
    rw [hx, Units.coe_prod]
    change _ = ∏ PP ∈ P.attach, (fun PP => es PP * c + (1 - es PP)) PP.1
    rw [Finset.prod_attach P (fun PP => es PP * c + (1 - es PP)),
      GlobalTheory.SplitIdeleModulus.prod_idem hes _ P subset_rfl, hae]
  let A : (AE D)ˣ →* ℝ := ⟨⟨GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D, GlobalTheory.SplitIdeleModulus.absFin_one'⟩, GlobalTheory.SplitLinear.absFin_mul⟩
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = A x := rfl
  rw [hA, hx', map_prod]
  exact Finset.prod_eq_one fun PP _ => absFin_single (hes PP.1 PP.2) (u PP) c rfl c' hcc (hc PP.1 PP.2)

end GlobalTheory.DetIdeleUnit

theorem GlobalTheory.DetIdeleUnit.cpt_gdet_kapAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
  ((gdet (GlobalTheory.TopLevelInv.kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) = GlobalTheory.StdFrames.cpt w ((finG (G.V (.top (j + 1))) k).val.det) := by
  have hu : IsUnit ((S.βp (j + 1)).val.det) := (Matrix.GeneralLinearGroup.det (S.βp (j + 1))).isUnit
  have ha : ((S.βp (j + 1)).val.map (GlobalTheory.StdFrames.cpt w)).det ≠ 0 := by
    intro h0; apply (hu.map (GlobalTheory.StdFrames.cpt w)).ne_zero; rw [RingHom.map_det]; exact h0
  unfold GlobalTheory.TopLevelInv.kapAt inBasis
  simp [gdet, GlobalTheory.StepData.reGL, Matrix.GeneralLinearGroup.det, GlobalTheory.StdFrames.loc, RingHom.map_det]
  rw [mul_right_comm, inv_mul_cancel₀ ha, one_mul]

theorem GlobalTheory.DetIdeleUnit.valued_eq_one_of_valuation {D : D7} {w : Pl D.host.E} (y : Kw w) (h : ValuativeRel.valuation (Kw w) y = 1) : Valued.v y = 1 := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  first
  | exact e.eq_one_iff_eq_one.1 h
  | exact le_antisymm (e.le_one_iff_le_one.1 h.le) (e.one_le_iff_one_le.1 h.ge)

namespace GlobalTheory.DetIdeleUnit

open _root_.Formalism.L2.NTheta (IsIdemAt)
open GlobalTheory.ExpansionInvariance

variable {D : D7}

theorem det_mt_conj (V : HSp D) (h k : GA D V) :
    (Formalism.L2.Theta.mt V (h⁻¹ * k * h)).det = (Formalism.L2.Theta.mt V k).det := by
  rw [GlobalTheory.IdemSupport.mt_mul, GlobalTheory.IdemSupport.mt_mul, Matrix.det_mul, Matrix.det_mul,
    mul_comm (Formalism.L2.Theta.mt V h⁻¹).det, mul_assoc, ← Matrix.det_mul, ← GlobalTheory.IdemSupport.mt_mul, inv_mul_cancel,
    GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one, mul_one]

theorem cpt_det_cutPart {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P)
    (V : HSp D) (g : GA D V) :
    GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det) =
      GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V g).det) := by
  have hee : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have hc0 : e * cA D e = 0 := he.2
  obtain ⟨hf1, hf2⟩ := idem_conj_sum hee hc0
  obtain ⟨⟨es, hes, hae⟩, -⟩ := id he
  let ψ : AE D →+* Kw PP := (GlobalTheory.StdFrames.cpt PP).comp (toEAf D)
  have hψe : ψ e = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hae, map_sum, Finset.sum_eq_single PP]
    · exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).1
    · intro Q hQ hne
      exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).2 PP (Ne.symm hne)
    · intro h; exact absurd hPP h
  have hψc : ψ (cA D e) = 0 := by
    have := congrArg ψ hc0
    rwa [map_mul, hψe, one_mul, map_zero] at this
  have hψa : ψ (e + cA D e) = 1 := by rw [map_add (f := _), hψe, hψc, add_zero]
  show ψ _ = ψ _
  rw [RingHom.map_det, RingHom.map_det, mt_cutPart hf1 hf2]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
    map_mul, map_sub, map_one, hψa, hψe, hψc, one_mul, sub_self, zero_mul, add_zero]

theorem absFin_detAt_cutPart {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (hee : e * e = e) (V : HSp D)
    (g : GA D V) (hg : ∀ PP ∈ P, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V g).det)) = 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e hee V (cutPart (e + cA D e) V g)) = 1 :=
  absFin_idemSum_eq_one he _ (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det
    (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)⁻¹).det
    (by rw [← Matrix.det_mul, ← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]) rfl
    (fun PP hPP => by rw [cpt_det_cutPart he hPP]; exact hg PP hPP)

end GlobalTheory.DetIdeleUnit

open GlobalTheory.DetIdeleUnit in
theorem GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1 := by
  intro D T L sc G W U S t μ₀ hμ ht Φ β j hj k hk e he
  refine absFin_detAt_cutPart he _ _ _ fun PP hPP => ?_
  have h1 := GlobalTheory.TopLevelInv.valuation_gdet_kapAt S hj hk ⟨PP, hPP⟩
  rw [cpt_gdet_kapAt] at h1
  have h2 := valued_eq_one_of_valuation _ h1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, det_mt_conj]
  rw [RingHom.map_det]
  exact h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusConjLevelDetEqOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteIdeleModulus_conjLevelDet_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1 := by
  first | exact @GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one | exact GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one | (intros; apply GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionMovesStandardVacuumTopNodeEqCharSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.TopLevelInv

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove in
theorem vac_high_law (hA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))), 1) (S.Z.vac (.top t (j + 1))) = S.Z.vac (.top t (j + 1))) (hC1 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1) (hC2 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ)) : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hce : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hce
  have hW := W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hvac := S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hS := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m by omega))
  have hT := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
  set g : GA D (G.V (.top (j + 1))) := ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) with hgdef
  have key := GlobalTheory.SplitLinear.splitLinearModel D W.ψ _ _ _ _ _ hW _ _ hS hT (locPl G t) e he _ hvac.2.theta hvac.2.lat 1
    one_ne_zero Tm hTm (cutPart (e + cA D e) _ g) 1 (suppAt_cutPart hee hce _ g) (GlobalTheory.SplitLinear.suppAt_one e _) _ _
    (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) _ (GlobalTheory.isSBHalf_halfInd e _)
  have hvacTm : Tm (halfInd e (stdLatO S (.top t (j + 1)))) = S.Z.vac (.top t (j + 1)) := by
    have := hTm.vac
    rwa [one_smul] at this
  have hr1 : Even (G.V (.top (j + 1 + 1))).rank := by
    rw [GlobalTheory.FunObj.rank_top G (j := j + 1 + 1) (by omega)]; exact GlobalTheory.FunObj.rankX_even D (j + 1 + 1)
  have hr0 : Even (G.V (.top (j + 1))).rank := by
    rw [GlobalTheory.FunObj.rank_top G (j := j + 1) (by omega)]; exact GlobalTheory.FunObj.rankX_even D (j + 1)
  have hTc : G.chrT (.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]
  have hc : ((splitFacO (G.chrS (.top t (j + 1) : Pair T)) (G.chrT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ)) =
      ∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ) := by
    have h1 : GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1 = 1 := map_one _
    have h2 := hC1 S hL ht j hj k hk e he
    have h3 := hC2 S hL ht j hj k hk e he
    rw [h1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac, h2, hTc]
    simp only [splitFacO, map_one, mul_one, Real.one_rpow, Complex.ofReal_one, Circle.coe_inv]
    have h4 : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    simp only [h4, Real.one_rpow, mul_one, Complex.ofReal_one]
    have h5 : ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g)) : Circle) : ℂ) =
        ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := h3
    rw [h5, ← Finset.prod_inv_distrib]
    simp only [Units.val_inv_eq_inv_val]
  calc W.om (.top t (j + 1)) (g, 1) (S.Z.vac (.top t (j + 1)))
      = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1)
          (W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) _ g, 1) (S.Z.vac (.top t (j + 1)))) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, ← cutPart_mul hf]
    _ = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1) (S.Z.vac (.top t (j + 1))) := by
        rw [hA S hL ht j hj k hk e he]
    _ = _ := by
        rw [← hvacTm]
        erw [key]
        rw [← hc]
        conv_rhs => rw [← map_smul]
        congr 1
        funext x
        rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitLinear.subst_eq, halfInd_cutPart hee hce]
        rfl

theorem vac_move_high_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) :=
  vac_high_law (by intros; apply GlobalTheory.T.offPlacePart_fixes_standardVacuum <;> assumption) (by intros; apply GlobalTheory.T.finiteIdeleModulus_conjLevelDet_eq_one <;> assumption)
    (by intros; apply GlobalTheory.T.gridTupleHeckeCharacter_detIdele_eq_prod_local <;> assumption)

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionMovesStandardVacuumTopNodeEqCharSmulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_moves_standardVacuum_topNode_eq_char_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  first | exact @GlobalTheory.TopLevelInv.vac_move_high_eq | exact GlobalTheory.TopLevelInv.vac_move_high_eq | (intros; apply GlobalTheory.TopLevelInv.vac_move_high_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionLocalInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopLevelInv

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {Γ : Grid k}

theorem isAdmissible_flips {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e) :
    ∀ (l : List (ℕ × ℕ)) (St : Γ.PiLocalization₂), (∀ x ∈ l, CondLE ϖ e (Γ.nu x.1 x.2)) → CanFlip St.path l →
      (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) → St.IsAdmissible .one ϖ e →
      (St.flips .one ψ ϖ e l).IsAdmissible .one ϖ e := by
  intro l
  induction l with
  | nil => intro St _ _ _ hT; exact hT
  | cons x l ih =>
    intro St hν hc hJ hT
    obtain _ | ⟨hp, hc'⟩ := hc
    refine ih (St.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (GlobalTheory.T.splitThetaGrid_isAdmissible_flipTensor ψ ϖ e hϖ hψ he St x (hν x List.mem_cons_self) hp hJ hT)
    change IsOpen (Γ.flipLevel x.1 x.2 St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ Γ.flipLevel x.1 x.2 St.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

omit [MeasurableSpace k] [BorelSpace k] in
theorem prod_edgeFactor_col {j : ℕ} (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k)
    (hg : valuation k (gdet g : k) = 1) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (Γ.m, j + 1) g))).prod =
      (Γ.mu (j + 1) (gdet g) : ℂ) * (((Γ.mu (j + 1 + 1) (gdet g))⁻¹ : ℂˣ) : ℂ) := by
  have hd : ∀ Y, gdet ((Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) Y) = if Y = (Γ.m, j + 1) then gdet g else 1 := fun Y => by
    split_ifs with h
    · subst h; simp
    · simp [h]
  have hv : ∀ Y, valuation k (((if Y = (Γ.m, j + 1) then gdet g else 1 : kˣ)⁻¹ : kˣ) : k) = 1 := fun Y => by
    split_ifs
    · rw [Units.val_inv_eq_inv_val, map_inv₀, hg, inv_one]
    · simp
  have hf : ∀ b, Γ.edgeFactor .one (Pi.mulSingle (Γ.m, j + 1) g) b =
      (Γ.kappa b b.src (if b.src = (Γ.m, j + 1) then gdet g else 1) : ℂ) *
        (((Γ.kappa b b.tgt (if b.tgt = (Γ.m, j + 1) then gdet g else 1))⁻¹ : ℂˣ) : ℂ) := fun b => by
    simp only [Grid.edgeFactor, Assignment.read, gdet_invT, hd, apow_of_valuation_eq_one (hv _), mul_one]
  rw [oppositePath, List.map_append, List.prod_append, List.map_map, List.map_map, List.map_reverse, List.prod_reverse,
    List.prod_eq_one, one_mul, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  · simp only [Function.comp, hf, Finset.prod_mul_distrib]
    rw [Finset.prod_eq_single j, Finset.prod_eq_single (j + 1)]
    · simp only [if_true, Grid.kappa, Grid.blockChar, MonoidHom.div_apply]
      simp only [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
      field_simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h; omega
    · intro b _ hb; simp [hb]
    · intro h; simp at h; omega
  · intro c hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
    simp [hf, show Γ.m ≠ j + 1 by omega]

theorem datum_colMove (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] {J : Γ.Level} (keep : Bool)
    (ρ : Reps hs J) {F : Γ.Args → ℂ} (hF : Γ.IsAdmissible .one (oppositePath Γ.m) J F) (β : Cosets hs J) {j : ℕ}
    (hj : j + 1 < Γ.m) (hJ : J (Γ.m, j + 1) ≤ KO k _) {κ : GL (Fin (topRank Γ (j + 1))) k}
    (hκ : κ ∈ (unfTerm ψ ν keep ρ F β).pr (j + 1) j.succ_pos hj) (x : ColArgs Γ) (y : RowArgs Γ) :
    (Γ.mu (j + 1) (gdet κ) : ℂ) * (((Γ.mu (j + 1 + 1) (gdet κ))⁻¹ : ℂˣ) : ℂ) *
      (unfTerm ψ ν keep ρ F β).datum (colMove j κ x) y = (unfTerm ψ ν keep ρ F β).datum x y := by
  obtain ⟨u, hu, v, hv, h, hdet⟩ := exists_of_mem_symPr hs hj hκ
  have hu1 : valuation k (gdet u : k) = 1 := valuation_gdet_of_mem_KO (hJ hu)
  set h' := ρ.elt β
  set g := h' (Γ.m, j + 1) * u * (h' (Γ.m, j + 1))⁻¹ with hg
  have hgd : gdet g = gdet κ := by
    rw [← gdet_toFrame hs hj, h, gdet_mul, gdet_of_mem_symN hv, one_mul, gdet_embX]
  have hin : (Γ.m, j + 1) ∈ innerVertices (oppositePath Γ.m) := by
    obtain ⟨m, hm⟩ : ∃ m, Γ.m = m + 1 := ⟨Γ.m - 1, by omega⟩
    refine List.mem_map.2 ⟨.theta Γ.m j, ?_, rfl⟩
    rw [oppositePath, List.tail_append_of_ne_nil (by simp; omega)]
    exact List.mem_append_right _ (by simp; omega)
  have hcomm : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) * h' = h' * Pi.mulSingle (Γ.m, j + 1) u := by
    funext Y
    by_cases hY : Y = (Γ.m, j + 1)
    · subst hY; simp [hg]
    · simp [hY]
  have hinv : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (Γ.m, j + 1) g) (Γ.pathAct .one (oppositePath Γ.m) h' F) =
      Γ.pathAct .one (oppositePath Γ.m) h' F := by
    rw [← Grid.pathAct_mul, hcomm, Grid.pathAct_mul, hF _ hin u hu]
  have hmv : moved Γ keep h' F = fun z => ((Γ.mu (j + 1) (gdet κ) : ℂ) * (((Γ.mu (j + 1 + 1) (gdet κ))⁻¹ : ℂˣ) : ℂ)) *
      moved Γ keep h' F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) z) := by
    funext z
    have := congrFun hinv z
    rw [Grid.pathAct, prod_edgeFactor_col hj g (by rw [hgd, hdet, hu1]), hgd] at this
    rw [moved, moved, ← this]
    ring
  change _ * flatTensor hs ψ ν (moved Γ keep h' F) _ _ = flatTensor hs ψ ν (moved Γ keep h' F) _ _
  rw [← GlobalTheory.T.flatTensor_moveArguments_lastRow_vertex hs ψ ν (moved Γ keep h' F) j hj g κ (by rw [hdet, hu1]) v hv h x y]
  conv_rhs => rw [hmv]
  simp only [flatTensor, flatIntegrand, mul_assoc, integral_const_mul]

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem isAdmissible_Tflip {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    (locGrid G t w).IsAdmissible .one (oppositePath D.R.m) (givenLevel G t w) (Tflip W B t Φ w) := by
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square i hi j hj).condν
  rw [← (flipStage_path_level t w B W Φ).1, ← (flipStage_path_level t w B W Φ).2]
  exact (isAdmissible_flips h00.unif h00.cond h00.one_le (flipOrder D.R.m) (givenStage t w B Φ) hν (canFlip_flipOrder _).1
    (fun X => GivenAdm.givenLevel_open hL hw X) (GivenAdm.givenStage_isAdmissible hL B t Φ hw)).invariant

theorem vac_ne_zero (S : GridChoice W U) {p : Pair T} (hp : DefPair D.R.m p) : S.Z.vac p ≠ 0 := fun h0 => by
  obtain ⟨⟨q, hq⟩, hall⟩ := (S.Z.vac_is p hp).2.norm
  have := hall q hq
  rw [h0] at this
  simp [nrm2] at this

theorem smul_unique {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (om : H →* Module.End ℂ M) {f f' : M} (hf : f ≠ 0)
    {g : H} {c c' : ℂ} (h : om g f = c • f') (h' : om g f = c' • f') : c = c' := by
  have hf' : f' ≠ 0 := fun h0 => hf (by
    have := congrArg (om g⁻¹) h
    rwa [h0, smul_zero, map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this)
  exact smul_left_injective ℂ hf' (h.symm.trans h')

theorem local_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}, β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    (∀ d ∈ τ.support, ∀ j', (d.1 j').e = e) →
    ∀ (T₁ : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)) (T₂ : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ)),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) T₁ →
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) T₂ →
    ∀ c₁ c₂ : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c₁ • T₁ (fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x)) →
      W.om (.top t (j + 1)) (((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        c₂ • T₂ (fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x)) →
    ∀ (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (c₁ * c₂) * (∏ j', movedFn S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) j' (x j')) * ∏ i, (d.2 i).fn (y i)) =
        τ.sum fun d a => a * (∏ j', (d.1 j').fn (x j')) * ∏ i, (d.2 i).fn (y i) := by
  intro D T L sc G W U S t μ₀ hL hde hc ht Φ β τ _ hexp j hj k hk e he hte T₁ T₂ hT₁ hT₂ c₁ c₂ hc₁ hc₂ x y
  classical
  have e₁ := smul_unique _ (vac_ne_zero S (p := .top t j) (show j + 1 ≤ D.R.m by omega)) hc₁
    (GlobalTheory.T.weil_conj_level_moves_vacuum_by_character S hL ht j hj k hk e he T₁ hT₁)
  have e₂ := smul_unique _ (vac_ne_zero S (p := .top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)) hc₂
    (GlobalTheory.T.weilAction_moves_standardVacuum_topNode_eq_char_smul S hL ht j hj k hk e he T₂ hT₂)
  obtain ⟨e', -, hsupp, hF⟩ := hexp
  set g : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hg
  have hhalf : ∀ j', IsHalf e' (movedPt t j hj g x j') ↔ IsHalf e' (x j') := fun j' => by
    rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
    · simp only [movedPt, Function.update_self]; exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
    · simp only [movedPt, Function.update_of_ne h1, Function.update_self]; exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    · simp only [movedPt, Function.update_of_ne h1, Function.update_of_ne h2]
  have hL' : (τ.sum fun d a => a * (c₁ * c₂) * (∏ j', movedFn S d j hj g j' (x j')) * ∏ i, (d.2 i).fn (y i)) =
      c₁ * c₂ * τ.sum fun d a => a * (∏ j', (d.1 j').fn (movedPt t j hj g x j')) * ∏ i, (d.2 i).fn (y i) := by
    simp only [Finsupp.sum, Finset.mul_sum, movedFn_apply]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hL']
  have hzero : ∀ x' : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)),
      ¬ ((∀ j', IsHalf e' (x' j')) ∧ ∀ i, IsHalf e' (y i)) →
      (τ.sum fun d a => a * (∏ j', (d.1 j').fn (x' j')) * ∏ i, (d.2 i).fn (y i)) = 0 := fun x' hx' => by
    refine Finset.sum_eq_zero fun d hd => ?_
    by_contra h0
    refine hx' ⟨fun j' => ?_, fun i => ?_⟩
    · rw [← ((hsupp d hd).1 j').2.1]
      exact (d.1 j').sb.1 _ fun h => h0 (by beta_reduce; rw [Finset.prod_eq_zero (f := fun j' => (d.1 j').fn (x' j')) (Finset.mem_univ j') h]; simp)
    · rw [← ((hsupp d hd).2 i).2.1]
      exact (d.2 i).sb.1 _ fun h => h0 (by beta_reduce; rw [Finset.prod_eq_zero (f := fun i => (d.2 i).fn (y i)) (Finset.mem_univ i) h]; simp)
  by_cases hx : (∀ j', IsHalf e' (x j')) ∧ ∀ i, IsHalf e' (y i)
  · rw [hF _ y (fun j' => (hhalf j').2 (hx.1 j')) hx.2, hF x y hx.1 hx.2, e₁, e₂, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.T.unfoldingColumnArgs_movedPoint_conj_atPlace S ht j hj k w.1 w.2 x]
    haveI := (isUnitVol_unitVol w.1).1
    exact datum_colMove (Γ := locGrid G t w.1) one_le_sLen _ _ _ _ (isAdmissible_Tflip hL W S.B t Φ hde hc w.2) (β w) hj
      (givenLevel_col t w.1 j).le (kapAt_mem S hj hk w) _ _
  · rw [hzero x hx, hzero _ fun h => hx ⟨fun j' => (hhalf j').1 (h.1 j'), h.2⟩, mul_zero]

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionLocalInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingExpansion_productFunction_localInvariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}, β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    (∀ d ∈ τ.support, ∀ j', (d.1 j').e = e) →
    ∀ (T₁ : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)) (T₂ : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ)),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) T₁ →
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) T₂ →
    ∀ c₁ c₂ : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c₁ • T₁ (fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x)) →
      W.om (.top t (j + 1)) (((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        c₂ • T₂ (fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x)) →
    ∀ (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (c₁ * c₂) * (∏ j', movedFn S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) j' (x j')) * ∏ i, (d.2 i).fn (y i)) =
        τ.sum fun d a => a * (∏ j', (d.1 j').fn (x j')) * ∏ i, (d.2 i).fn (y i) := by
  first | exact @GlobalTheory.TopLevelInv.local_invariant | exact GlobalTheory.TopLevelInv.local_invariant | (intros; apply GlobalTheory.TopLevelInv.local_invariant <;> assumption)
end
