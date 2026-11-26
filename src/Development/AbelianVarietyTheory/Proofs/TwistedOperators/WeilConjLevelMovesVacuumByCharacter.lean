module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LawStep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtEnlargePlaceIdempotentLatticeIndicator
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseIdempotentOfSplitIdempotentSum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseIdempotentOfSplitIdempotentSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

namespace GlobalTheory.IdemSumF

theorem exists_idem_below : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D}, IsIdemSum e P →
    ∃ ε : AF D.host.F, IsIdempotentElem ε ∧ algebraMap (AF D.host.F) (AE D) ε = e + cA D e :=
  fun he => Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_eps he

end GlobalTheory.IdemSumF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseIdempotentOfSplitIdempotentSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseIdempotent_of_splitIdempotentSum : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D}, IsIdemSum e P →
    ∃ ε : AF D.host.F, IsIdempotentElem ε ∧ algebraMap (AF D.host.F) (AE D) ε = e + cA D e := by
  first | exact @GlobalTheory.IdemSumF.exists_idem_below | exact GlobalTheory.IdemSumF.exists_idem_below | (intros; apply GlobalTheory.IdemSumF.exists_idem_below <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedConjugateFixesStandardVacuumTopPair
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedConjugateFixesStandardVacuumTopPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
noncomputable section

namespace GlobalTheory.TopLevelInv

section Unr

variable {D : D7}

theorem unrOff_mul' {e : AE D} {χ χ' : (AE D)ˣ →* Circle} (h : Formalism.IndefR.Fin.UnrOff e χ)
    (h' : Formalism.IndefR.Fin.UnrOff e χ') : Formalism.IndefR.Fin.UnrOff e (χ * χ') :=
  fun x h1 h2 h3 h4 => by rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, one_mul]

theorem unrOff_inv' {e : AE D} {χ : (AE D)ˣ →* Circle} (h : Formalism.IndefR.Fin.UnrOff e χ) :
    Formalism.IndefR.Fin.UnrOff e χ⁻¹ :=
  fun x h1 h2 h3 h4 => by rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

theorem pg_near_locPl {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    {PP : Pl D.host.E} (h : PP ∈ L.Pg) : ∃ w ∈ locPl G t, PP = w ∨ PP = GlobalTheory.IdemSupport.cP w := by
  classical
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
  have hm := GlobalTheory.LevelRamif.typePrime_mem hk
  set v := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hv
  have hvk : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    rwa [map_natCast]
  have hS1 : v ∈ S1 D := by
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hvk
    · exact Or.inr (Or.inl hvk)
  have hS0 : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)
  refine ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hS0), ?_⟩
  exact GlobalTheory.IdemSupport.eq_or_eq_cP (by rw [G.pl.under_w hS0])

theorem conjPrime_conjPrime₂ (P : HeightOneSpectrum (𝓞 D.host.E)) : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO])

theorem unrOff_mu_locPl {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}
    (hL : L.Is μ₀) (j : Fin D.R.m) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    Formalism.IndefR.Fin.UnrOff e (L.mu t ((j : ℕ) + 1)) ∧ Formalism.IndefR.Fin.UnrOff e L.eta := by
  classical
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ hL t j
  have hmu : Formalism.IndefR.Fin.UnrOff e (L.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e (hL.mu0 j) he fun PP' h1 h2 => by
      refine h4 PP' (fun h => ?_) fun PP h h' => ?_
      · obtain ⟨w, hw, hw'⟩ := pg_near_locPl G hL t h
        rcases hw' with rfl | rfl
        · exact h1 hw
        · exact h2 w hw ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 rfl)
      · obtain ⟨w, hw, hw'⟩ := pg_near_locPl G hL t h
        have e1 := (GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h'
        rcases hw' with rfl | rfl
        · exact h2 PP hw h'
        · rw [conjPrime_conjPrime₂] at e1
          exact h1 (e1 ▸ hw)
  have hxi : Formalism.IndefR.Fin.UnrOff e (L.xi t) :=
    GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e (hL.xi t) he fun PP' h1 h2 => by
      by_contra hn
      rcases (hL.Q_ram t PP').1 hn with h | ⟨PP, h, h'⟩
      · exact h1 (Finset.mem_union_right _ h)
      · exact h2 PP (Finset.mem_union_right _ h) h'
  exact ⟨unrOff_mul' hmu hxi, GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e hL.eta he fun PP' _ _ => L.C.isEta.unr PP'⟩

end Unr


set_option maxHeartbeats 1000000 in
theorem vacFix_conjPt_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ e : AE D, IsIdemSum e (locPl G t) → ∀ ε : AF D.host.F, IsIdempotentElem ε →
    algebraMap (AF D.host.F) (AE D) ε = e + cA D e →
    W.om (.top t j) (1, resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) (S.Z.vac (.top t j)) =
      S.Z.vac (.top t j) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he ε hε halg
  have hε' : IsIdempotentElem (1 - ε) := hε.one_sub
  have hdp : DefPair D.R.m (.top t j : Pair T) := by show j + 1 ≤ D.R.m; omega
  have hW := W.om_is (.top t j) (by simp only [Pair.InRange, Node.InRange]; omega)
  have hv := S.Z.vac_is _ hdp
  have hdS : DefNode D.R.m (.top j) := by show j ≤ D.R.m; omega
  have hdT : DefNode D.R.m (.top (j + 1)) := by show j + 1 ≤ D.R.m; omega
  have hS := S.N.selfDual (X := .top j) hdS
  have hT := S.N.selfDual (X := .top (j + 1)) hdT
  have hfS := GlobalTheory.OffPartLattice.isFrame_moved (colLat (S.N.fr (.top j))) (G.Λ (.top j)) (S.βp j)
    (Lev.finE (G.V (.top j)) (S.N.u (.top j)).1) (S.βp_is j hdS) (S.N.u_lat _ hdS)
  have hfT := GlobalTheory.OffPartLattice.isFrame_moved (colLat (S.N.fr (.top (j + 1)))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hdT) (S.N.u_lat _ hdT)
  have hrkS : (G.V (.top j)).rank = rankX D j := (G.isV (X := .top j) hdS fun _ e => by cases e).rank
  have hrkT : (G.V (.top (j + 1))).rank = rankX D (j + 1) := (G.isV (X := .top (j + 1)) hdT fun _ e => by cases e).rank
  have hrk : (G.V (.top j)).rank ≠ (G.V (.top (j + 1))).rank := by
    intro h
    rw [hrkS, hrkT] at h
    simp only [rankX, add_mul, one_mul] at h
    omega
  have hev : Even (G.V (.top j)).rank := hrkS ▸ even_rankX D j
  obtain ⟨hμ, hη⟩ := unrOff_mu_locPl G hL ⟨j, by omega⟩ he
  have hatt : ∀ n, Formalism.IndefR.Fin.UnrOff e (Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta n) := by
    intro n
    unfold Formalism.IndefR.Lift.attChr
    split_ifs
    · exact unrOff_mul' hμ (unrOff_inv' hη)
    · exact hμ
  have hn : ∃ (μ : Measure (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (𝓕 : Set (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))),
      IsCovolOne (ratL (G.pT (.top t j : Pair T)) (G.pS (.top t j : Pair T))) μ 𝓕 ∧
        nrm2 μ 𝓕 (S.Z.vac (.top t j)) = 1 := by
    obtain ⟨⟨p, hp⟩, hall⟩ := hv.2.norm
    exact ⟨p.1, p.2, hp, hall p hp⟩

  have hf := GlobalTheory.ExpansionInvariance.idem_conj_sum (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2
  have h2 := GlobalTheory.ExpansionInvariance.idem_compl hf
  have hcut : resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k) =
      GlobalTheory.ExpansionInvariance.cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) (conjPt S j k) := by
    apply Formalism.IndefR.Fin.LevelGroupLemmas.gaExt
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG _ hε', GlobalTheory.ExpansionInvariance.mt_cutPart h2.1 h2.2, map_sub, map_one, halg]
    unfold Formalism.IndefR.Fin.LevelGroupLemmas.resM
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hSt : Lev.finE (G.V (.top (j + 1))) (resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) ∈
      St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) := by
    have hk2 : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) (fun w => topRank_eq G t w hj.le)
        (fun w => (S.term t Φ β w).pr _ j.succ_pos hj) := hk
    rw [hcut]
    exact GlobalTheory.OffPartLattice.finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1))
      (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (finG (G.V (.top (j + 1))) k) (conjPt S j k)
      (by simp only [conjPt, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]; rfl) he (fun Q hQ => by
        have h3 := (Subgroup.mem_inf.1 hk2).2
        rw [Subgroup.mem_iInf] at h3
        have h4 := h3 Q
        rw [Subgroup.mem_iInf] at h4
        exact Subgroup.mem_comap.1 (h4 hQ))
  have hP : ∀ a b, (e + cA D e) * (mt (G.V (.top (j + 1))) (resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) - 1) a b = 0 := by
    intro a b
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG_sub hε' _ a b, ← mul_assoc, map_sub, map_one, halg]
    have h0 : (e + cA D e) * (1 - (e + cA D e)) = 0 := by
      linear_combination (-1 : AE D) * hf.1
    rw [h0, zero_mul]
  exact Formalism.IndefR.Fin.LevelGroupLemmas.vacFixOff (Formalism.IndefR.Fin.splitLinF D) (Formalism.IndefR.Fin.placeModelAtF D)
    (Formalism.IndefR.Fin.splitOrInert D) W.ψ _ _ _ _ _ hW (GlobalTheory.InertAll.inertAllO D _ _ _ _ _ _ hW) hrk (Or.inl hev) _ _ hS hT _ _
    hfS hfT (locPl G t) e he (hatt _) (hatt _) _ hv.2.theta hv.2.lat hn 1 _ (one_mem _)
    (Formalism.IndefR.Fin.LevelGroupLemmas.resG_mem_GfC _ hε' (SetLike.coe_mem _)) (by rw [map_one]; exact one_mem _) hSt
    (fun a b => by rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', sub_self, Matrix.zero_apply, mul_zero]) hP

end GlobalTheory.TopLevelInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedConjugateFixesStandardVacuumTopPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncatedConjugate_fixes_standardVacuum_topPair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ e : AE D, IsIdemSum e (locPl G t) → ∀ ε : AF D.host.F, IsIdempotentElem ε →
    algebraMap (AF D.host.F) (AE D) ε = e + cA D e →
    W.om (.top t j) (1, resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) (S.Z.vac (.top t j)) =
      S.Z.vac (.top t j) := by
  first | exact @GlobalTheory.TopLevelInv.vacFix_conjPt_off | exact GlobalTheory.TopLevelInv.vacFix_conjPt_off | (intros; apply GlobalTheory.TopLevelInv.vacFix_conjPt_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusProdLocalUnitIdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusProdLocalUnitIdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

noncomputable section

namespace GlobalTheory.ProductIdeleModulus

theorem exists_under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact bot_le
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQc, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
  refine ⟨⟨Q, hQ.isPrime, hQ0⟩, ?_⟩
  ext1
  exact hQc

theorem valuation_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x = 1 ↔ Valued.v x = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

theorem norm_comp_le_one {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : GlobalTheory.IdemSupport.Comp D Φ)
    {z : AE D} (hz : finPart D z ∈ intAE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
      ((Algebra.norm (AF D.host.F) z).2 (Q.under (𝓞 D.host.F)))) ≤ 1 := by
  have hm : finPart D (z * cA D z) ∈ intAE D := by
    rw [map_mul]
    exact GlobalTheory.SplitLatBasis.mul_mem_intAE D hz (GlobalTheory.IdemSupport.finPart_cA_mem hz)
  have h := (hΦ.int _).1 hm Q
  rw [← GlobalTheory.SplitDetCharacter.algebraMap_norm, hΦ.base] at h
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h

theorem absFin_eq_one_of_int {D : D7} (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D)
    (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin
  refine (finprod_congr fun v => ?_).trans finprod_one
  obtain ⟨Q, rfl⟩ := exists_under_eq (E := D.host.E) v
  have a1 := norm_comp_le_one hΦ h1 Q
  have a2 := norm_comp_le_one hΦ h2 Q
  have hn : Algebra.norm (AF D.host.F) (x : AE D) * Algebra.norm (AF D.host.F) ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hprod : Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
        ((Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)))) *
      Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
        ((Algebra.norm (AF D.host.F) ((x⁻¹ : (AE D)ˣ) : AE D)).2 (Q.under (𝓞 D.host.F)))) = 1 := by
    rw [← map_mul, ← map_mul]
    have : (Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)) *
        (Algebra.norm (AF D.host.F) ((x⁻¹ : (AE D)ˣ) : AE D)).2 (Q.under (𝓞 D.host.F)) = 1 := by
      have := congrArg (fun a : AF D.host.F => a.2 (Q.under (𝓞 D.host.F))) hn
      exact this
    rw [this, map_one, map_one]
  have hv1 : Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
      ((Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)))) = 1 :=
    le_antisymm a1 (hprod.symm.le.trans (mul_le_of_le_one_right' a2))
  have hv := (GlobalTheory.TwU.IntegralHilbert90Unramified.locMap_val_eq_one_iff Q _).1 hv1
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D (Q.under (𝓞 D.host.F)) x : (Fv D.host.F (Q.under (𝓞 D.host.F)))ˣ) :
      Fv D.host.F (Q.under (𝓞 D.host.F))) = (Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)) := rfl
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, e, hv]

end GlobalTheory.ProductIdeleModulus

namespace GlobalTheory.TopLevelInv

theorem absFin_prod_locIdele_unit : ∀ {D : D7} (P : Finset (Pl D.host.E)) (y : ∀ w : P, (Kw w.1)ˣ),
    (∀ w, valuation (Kw w.1) (y w : Kw w.1) = 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (∏ w : P, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) = 1 := by
  intro D P y hy
  have hone : ∀ w : P, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) = 1 := by
    intro w
    have hv : Valued.v ((y w : Kw w.1)) = 1 := (GlobalTheory.ProductIdeleModulus.valuation_eq_one_iff w.1 _).1 (hy w)
    refine GlobalTheory.ProductIdeleModulus.absFin_eq_one_of_int _ ((GlobalTheory.LFun.EulerTie.locIdele_int_iff w.1 (y w)).2 hv.le) ?_
    rw [← map_inv]
    refine (GlobalTheory.LFun.EulerTie.locIdele_int_iff w.1 (y w)⁻¹).2 ?_
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  refine Finset.prod_induction _ (fun z => GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D z = 1)
    (fun a b ha hb => by rw [GlobalTheory.SplitLinear.absFin_mul, ha, hb, one_mul]) ?_ (fun w _ => hone w)
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusProdLocalUnitIdelesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteIdeleModulus_prod_localUnitIdeles : ∀ {D : D7} (P : Finset (Pl D.host.E)) (y : ∀ w : P, (Kw w.1)ˣ),
    (∀ w, valuation (Kw w.1) (y w : Kw w.1) = 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (∏ w : P, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) = 1 := by
  first | exact @GlobalTheory.TopLevelInv.absFin_prod_locIdele_unit | exact GlobalTheory.TopLevelInv.absFin_prod_locIdele_unit | (intros; apply GlobalTheory.TopLevelInv.absFin_prod_locIdele_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConjLevelMovesVacuumByCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt resG_compl suppAt_resG isDetAt_detAt resG_one resG_mul actO_actO isHalf_actO)

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem omega_conj_vac_low: ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      W.om (.top t j) (1, (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        (∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he Tm hTm
  change W.om (.top t j) (1, conjPt S j k) (S.Z.vac (.top t j)) = _ • Tm fun x => halfInd e (stdLatO S (.top t j))
    (actO _ _ 1⁻¹ (conjPt S j k)⁻¹ x)
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have he2 : e * e = e := ho.idem
  have hc : e * cA D e = 0 := he.2
  obtain ⟨ε, hε, halg⟩ := GlobalTheory.T.exists_baseIdempotent_of_splitIdempotentSum he
  have hε' : IsIdempotentElem (1 - ε) := hε.one_sub
  have hsplit : (((1 : GA D (G.V (.top j))), conjPt S j k) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) =
      (1, resG _ ε (conjPt S j k)) * (1, resG _ (1 - ε) (conjPt S j k)) := by
    rw [Prod.mk_mul_mk, one_mul, resG_compl _ hε]
  have hdp : DefPair D.R.m (.top t j : Pair T) := by show j + 1 ≤ D.R.m; omega
  have hW := W.om_is (.top t j) (by simp only [Pair.InRange, Node.InRange]; omega)
  have hv := S.Z.vac_is _ hdp
  have hS := S.N.selfDual (X := .top j) (by show j ≤ D.R.m; omega)
  have hT := S.N.selfDual (X := .top (j + 1)) (by show j + 1 ≤ D.R.m; omega)
  have hlaw := GlobalTheory.SplitLinear.law_orth hW hS hT ho hc hv.2.theta hv.2.lat one_ne_zero hTm
    (GlobalTheory.SplitLinear.suppAt_one e _) (suppAt_resG _ hε (conjPt S j k) halg.symm) (isDetAt_detAt he2 _ 1)
    (isDetAt_detAt he2 _ (resG _ ε (conjPt S j k)))
  have hvac : Tm (halfInd e (stdLatO S (.top t j))) = S.Z.vac (.top t j) := by
    have := hTm.vac; rwa [one_smul] at this
  rw [hsplit, map_mul, Module.End.mul_apply, GlobalTheory.T.truncatedConjugate_fixes_standardVacuum_topPair S hL ht j hj k hk e he ε hε halg]
  conv_lhs => rw [← hvac]
  refine (hlaw (halfInd e (stdLatO S (.top t j))) (isSBHalf_halfInd e _)).trans ?_
  congr 1
  · rw [detAt_one' he2, detAt_resG_eq he2 hc hε halg, GlobalTheory.T.detIdele_conjugatedTopPoint_eq_prod_local S ht j hj k e he]
    unfold GlobalTheory.SplitLinear.fac
    simp only [splitFacO, map_one, inv_one, one_mul]
    rw [GlobalTheory.T.topPairSourceChar_prod_localIdeles G hL j hj]
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    have hm : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1
        (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w))) = 1 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac
      rw [GlobalTheory.T.finiteIdeleModulus_prod_localUnitIdeles _ _ (valuation_gdet_kapAt S hj hk), h1, Real.one_rpow, Real.one_rpow, mul_one]
    rw [hm, Complex.ofReal_one, mul_one]
  · congr 1
    funext x
    apply halfInd_congr
    by_cases hx : IsHalf e x
    · have hinv : (conjPt S j k)⁻¹ = resG _ (1 - ε) (conjPt S j k)⁻¹ * (resG _ ε (conjPt S j k))⁻¹ := by
        rw [← resG_inv_eq hε', ← _root_.mul_inv_rev, resG_compl _ hε]
      have key : actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1⁻¹ (conjPt S j k)⁻¹ x =
          actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1⁻¹ (resG _ ε (conjPt S j k))⁻¹ x :=
        calc _ = actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (1 * 1⁻¹)
              (resG _ (1 - ε) (conjPt S j k)⁻¹ * (resG _ ε (conjPt S j k))⁻¹) x := by rw [one_mul, ← hinv]
          _ = actO _ _ 1 (resG _ (1 - ε) (conjPt S j k)⁻¹)
              (actO _ _ 1⁻¹ (resG _ ε (conjPt S j k))⁻¹ x) := (actO_actO _ _ _ _ _).symm
          _ = _ := actO_one_resG_compl he2 hc hε halg _ _ ((isHalf_actO _ _ _).2 hx)
      rw [key]
    · constructor <;> rintro ⟨-, h⟩ <;> exact absurd ((isHalf_actO _ _ _).1 h) hx

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConjLevelMovesVacuumByCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_conj_level_moves_vacuum_by_character : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      W.om (.top t j) (1, (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        (∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  first | exact @GlobalTheory.TopLevelInv.omega_conj_vac_low | exact GlobalTheory.TopLevelInv.omega_conj_vac_low | (intros; apply GlobalTheory.TopLevelInv.omega_conj_vac_low <;> assumption)
end
