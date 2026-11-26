module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SummableLogAlpD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBPf
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Pass

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bbtop_eq_one_of {w : Point D.host.E (D.R.rS + 1)} {p : PlF D} {τ : Option ((M p).Cls D.R.rS)}
    (hs : HasSum (fL M δ (D.mem u).A.T (D.mem u').A.T p w τ) (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ))
    (hi : ∀ O, fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
      if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w then 1 else 0) :
    BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ = 1 := by
  have e : fL M δ (D.mem u).A.T (D.mem u').A.T p w τ =
      fun O => if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w then (1 : ℂ) else 0 := funext hi
  rw [e] at hs
  exact hs.unique (hasSum_ite_eq _ _)

theorem partnerSumC_of {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hL : LocOrbSum M δ u u') (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hK : ScalKind u u' F0 what₂) (hF : EligFinite u u' F0 what₂) (hP : PartnerTupleSum M δ u u' F0 what₂) :
    PartnerSumC δ M (PairVal.vRdef D u u' F0 what₂ δ M) (thT M δ) := by
  intro γ w hγ w' hG'
  by_cases hk : kind w' = kind w
  swap
  · have h0 : (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ // Corank.TermScal D γ γ' ∧ EligAt γ' w'} =>
        PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ'.1 w') = 0 := by
      funext γ'
      exact absurd (hK γ γ'.1 w w' hγ γ'.2.2 γ'.2.1).symm hk
    rw [h0]
    unfold BBG
    rw [if_neg hk]
    exact hasSum_zero
  obtain ⟨S, hS⟩ := hU w' hG'
  have hRf := hR γ w hγ
  obtain ⟨hres, hsum⟩ := hP γ w hγ w' hG' hk
  have hoff : ∀ p ∉ S ∪ hRf.toFinset, ∀ O, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) O =
      if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w' then 1 else 0 := by
    intro p hp O
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ h)
    have hth : thT M δ γ p = θ0 p := by
      by_contra h
      exact hp (Finset.mem_union_right _ (hRf.mem_toFinset.2 h))
    rw [((hS p hpS).2 _ O).1]
    simp only [hth, and_true]
  have hfin : Finite {γ' : TermDef.Term D u u' F0 what₂ // Corank.TermScal D γ γ' ∧ EligAt γ' w'} :=
    (Set.Finite.subset (s := {γ' : TermDef.Term D u u' F0 what₂ | EligAt γ' w'})
      (t := {γ' : TermDef.Term D u u' F0 what₂ | Corank.TermScal D γ γ' ∧ EligAt γ' w'}) (hF w')
      fun γ' h => h.2).to_subtype
  let cls : {γ' : TermDef.Term D u u' F0 what₂ // Corank.TermScal D γ γ' ∧ EligAt γ' w'} →
      Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w') := fun y => ⟨locT M δ y.1, hres y.1 y.2.1 y.2.2⟩
  have hF' : ∀ g : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun y : {y // cls y = g} => PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) y.1.1 w')
        (∏ᶠ p, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (g.1 p)) := by
    intro g
    have h2 := (Equiv.subtypeSubtypeEquivSubtypeInter (fun γ' : TermDef.Term D u u' F0 what₂ =>
      Corank.TermScal D γ γ' ∧ EligAt γ' w') (fun γ' => locT M δ γ' = g.1)).hasSum_iff.2 (hsum g)
    have h3 := (Equiv.subtypeEquivRight (p := fun y => cls y = g) (q := fun y => locT M δ y.1 = g.1)
      (fun y => Subtype.ext_iff)).hasSum_iff.2 h2
    exact h3
  have hmain := hasSum_passage (fun y : {γ' : TermDef.Term D u u' F0 what₂ // Corank.TermScal D γ γ' ∧ EligAt γ' w'} =>
      PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) y.1 w') cls _ hF'
    (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w') (Equiv.refl _)
    (fun p => fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p))
    (fun p => BBtop M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p)) (S ∪ hRf.toFinset)
    (fun g => rfl) hoff (fun p _ => (hL w' hG' p _).1) (fun p _ => (hL w' hG' p _).2.1)
  convert hmain using 1
  unfold BBG
  rw [if_pos hk]
  apply finprod_eq_prod_of_mulSupport_subset
  intro p hp
  by_contra hS'
  exact (Function.mem_mulSupport.1 hp) (bbtop_eq_one_of (hL w' hG' p _).1 (hoff p hS'))

theorem fiberCntC_of {L : CntLocal.LocSp D M} {nc : ℝ} (hnc : CntLocal.Formula δ L u u' F0 what₂ nc)
    {ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]} (hϖ : ∀ p, Irreducible (ϖ p)) {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hL : LocOrbSum M δ u u') (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hF : EligFinite u u' F0 what₂) (hQ : FiberTupleSum M δ L u u' F0 what₂) (hT : ThSome M δ u u' F0 what₂) :
    FiberCntC δ M (PairVal.vRdef D u u' F0 what₂ δ M) nc (thT M δ) (dnT M δ L ϖ) := by
  intro w hG γ₀ w₀ hγ₀
  by_cases hk : kind w = kind w₀
  swap
  · have h0 : (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
        EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀} =>
        (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ.1 w) = 0 := by
      funext γ
      exact absurd γ.2.2.1 hk
    rw [h0]
    unfold BBG
    rw [if_neg hk, mul_zero]
    exact hasSum_zero
  obtain ⟨S, hS⟩ := hU w hG
  have hRf := hR γ₀ w₀ hγ₀
  obtain ⟨hres, hsum⟩ := hQ nc hnc ϖ hϖ w hG γ₀ w₀ hγ₀ hk
  have hpS : ∀ p ∉ S ∪ hRf.toFinset, p ∉ S := fun p hp h => hp (Finset.mem_union_left _ h)
  have hth : ∀ p ∉ S ∪ hRf.toFinset, thT M δ γ₀ p = θ0 p := by
    intro p hp
    by_contra h
    exact hp (Finset.mem_union_right _ (hRf.mem_toFinset.2 h))
  have hoffg : ∀ p ∉ S ∪ hRf.toFinset, ∀ O, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) O =
      if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w then 1 else 0 := by
    intro p hp O
    rw [((hS p (hpS p hp)).2 _ O).2]
    simp only [hth p hp, and_true]
  have hofff : ∀ p ∉ S ∪ hRf.toFinset, ∀ O, fL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) O =
      if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w then 1 else 0 := by
    intro p hp O
    rw [((hS p (hpS p hp)).2 _ O).1]
    simp only [hth p hp, and_true]
  have hfin : Finite {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀} :=
    (Set.Finite.subset (s := {γ : TermDef.Term D u u' F0 what₂ | EligAt γ w})
      (t := {γ : TermDef.Term D u u' F0 what₂ | EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀}) (hF w)
      fun γ h => h.1).to_subtype
  let cls : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀} →
      Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w) := fun y => ⟨locT M δ y.1, hres y.1 y.2.1⟩
  have hF' : ∀ g : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun y : {y // cls y = g} =>
          (PairVal.massTerm y.1.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) y.1.1 w)
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (g.1 p)) := by
    intro g
    have h2 := (Equiv.subtypeSubtypeEquivSubtypeInter (fun γ : TermDef.Term D u u' F0 what₂ =>
      EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) (fun γ => locT M δ γ = g.1)).hasSum_iff.2 (hsum g)
    have h3 := (Equiv.subtypeEquivRight (p := fun y => cls y = g) (q := fun y => locT M δ y.1 = g.1)
      (fun y => Subtype.ext_iff)).hasSum_iff.2 h2
    exact h3
  refine hasSum_of_fiber _ cls _ hF' ?_
  have h := (hasSum_rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w)
    (fun p => gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p))
    (fun p => BBtop M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) / Pf.autP M p (thT M δ γ₀ p))
    (S ∪ hRf.toFinset) hoffg (fun p _ => ((hL w hG p _).2.2 (hT γ₀ w₀ hγ₀ p)).1)
    (fun p _ => ((hL w hG p _).2.2 (hT γ₀ w₀ hγ₀ p)).2)).mul_left
      ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ))
  have hB : BBG M δ (D.mem u).A.T (D.mem u').A.T w (kind w₀) (thT M δ γ₀) =
      ∏ p ∈ S ∪ hRf.toFinset, BBtop M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) := by
    unfold BBG
    rw [if_pos hk]
    apply finprod_eq_prod_of_mulSupport_subset
    intro p hp
    by_contra hp'
    exact (Function.mem_mulSupport.1 hp) (bbtop_eq_one_of (hL w hG p _).1 (hofff p hp'))
  have hA : Pf.autR M (thT M δ γ₀) = ∏ p ∈ S ∪ hRf.toFinset, Pf.autPR M p (thT M δ γ₀ p) := by
    unfold Pf.autR
    apply finprod_eq_prod_of_mulSupport_subset
    intro p hp
    by_contra hp'
    apply (Function.mem_mulSupport.1 hp)
    have h1 : Pf.autP M p (thT M δ γ₀ p) = 1 := by
      rw [hth p hp']
      exact (hS p (hpS p hp')).1
    rw [← Pf.autP_ofReal] at h1
    exact_mod_cast h1
  have hval : (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
      (((Pf.autR M (thT M δ γ₀))⁻¹ : ℝ) : ℂ) * BBG M δ (D.mem u).A.T (D.mem u').A.T w (kind w₀) (thT M δ γ₀) =
      (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
        ∏ p ∈ S ∪ hRf.toFinset,
          BBtop M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) / Pf.autP M p (thT M δ γ₀ p) := by
    rw [hB, hA]
    push_cast
    rw [Finset.prod_div_distrib]
    simp only [Pf.autP_ofReal]
    ring
  rw [hval]
  exact h

theorem restricted_of {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hL : LocOrbSum M δ u u') (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hG : AtPtG u u' F0 what₂) :
    ∀ θ0' : ∀ p, Option ((M p).Cls D.R.rS),
      (∀ w, ∃ S : Finset (PlF D), Pf.UnramOff M δ (D.mem u).A.T (D.mem u').A.T θ0' S w) →
      ∀ (γ : TermDef.Term D u u' F0 what₂) w, EligAt γ w → Pf.Restricted θ0' (thT M δ γ) := by
  intro θ0' hθ γ w hγ
  have hGw := hG γ w hγ.2
  obtain ⟨S1, h1⟩ := hθ w
  obtain ⟨S2, h2⟩ := hU w hGw
  have heq : ∀ p ∉ S1 ∪ S2, θ0' p = θ0 p := by
    intro p hp
    have hp1 : p ∉ S1 := fun h => hp (Finset.mem_union_left _ h)
    have hp2 : p ∉ S2 := fun h => hp (Finset.mem_union_right _ h)
    have hb : BBtop M δ (D.mem u).A.T (D.mem u').A.T p w (θ0 p) = 1 := by
      refine bbtop_eq_one_of (hL w hGw p (θ0 p)).1 fun O => ?_
      rw [((h2 p hp2).2 (θ0 p) O).1]
      simp only [and_true]
    have hb' := (h1 p hp1).2 (θ0 p)
    rw [hb] at hb'
    by_contra hne
    rw [if_neg (Ne.symm hne)] at hb'
    exact one_ne_zero hb'
  refine ((hR γ w hγ).union (S1 ∪ S2).finite_toSet).subset ?_
  intro p hp
  by_cases hpS : p ∈ S1 ∪ S2
  · exact Or.inr hpS
  · left
    intro h
    apply hp
    rw [h, heq p hpS]

theorem tprod_nonneg' {ι : Type*} (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) : 0 ≤ ∏' i, f i := by
  by_cases h : Multipliable f
  · exact ge_of_tendsto' h.hasProd fun s => Finset.prod_nonneg fun i _ => hf i
  · rw [tprod_eq_one_of_not_multipliable h]
    exact zero_le_one

theorem dens_nonneg (L : CntLocal.LocSp D M) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) :
    ∀ d ∈ DataInst.densSet L δ ϖ u u' F0 what₂, 0 ≤ d := by
  rintro d ⟨Z, -, rfl⟩
  exact tprod_nonneg' _ fun p => by
    unfold CntLocal.densP Formalism.MainNotions.S.Loc.HermSp.dens
    positivity

theorem eligFinite_of (hfin : TermDef.TermsAtFinite D u u') (hsig : (VS D).SigOK) (hrows : IsRowReps D F0 what₂) :
    EligFinite u u' F0 what₂ := fun w =>
  (TermDef.term_atPt_finite hfin hsig F0 what₂ hrows w).subset fun _ h => h.2

theorem rowsDatum_at {L : CntLocal.LocSp D M} (h : CutAt M δ L u u' F0 what₂) (hF : EligFinite u u' F0 what₂)
    (hrows : IsRowReps D F0 what₂)
    (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (hϖ : ∀ p, Irreducible (ϖ p))
    (nc : ℝ) (hnc : CntLocal.Formula δ L u u' F0 what₂ nc) :
    (∀ d ∈ DataInst.densSet L δ ϖ u u' F0 what₂, 0 ≤ d) ∧
      ∃ (th : TermDef.Term D u u' F0 what₂ → ∀ p, Option ((M p).Cls D.R.rS)) (dn : TermDef.Term D u u' F0 what₂ → ℝ),
        (∀ θ0 : ∀ p, Option ((M p).Cls D.R.rS),
          (∀ w, ∃ S : Finset (PlF D), Pf.UnramOff M δ (D.mem u).A.T (D.mem u').A.T θ0 S w) →
          ∀ γ w, EligAt γ w → Pf.Restricted θ0 (th γ)) ∧
        (∀ γ w, EligAt γ w → dn γ ∈ DataInst.densSet L δ ϖ u u' F0 what₂) ∧
        PartnerSumC δ M (PairVal.vRdef D u u' F0 what₂ δ M) th ∧
        FiberCntC δ M (PairVal.vRdef D u u' F0 what₂ δ M) nc th dn := by
  obtain ⟨hL, hK, hC, hP, hQ, hNR, hT, θ0, hU, hR⟩ := h
  have hD := dnInDens_of hNR hrows
  have hG := atPtG_holds u u' F0 what₂
  refine ⟨dens_nonneg L ϖ, thT M δ, dnT M δ L ϖ, restricted_of hL hU hR hG, fun γ w hγ => ?_,
    partnerSumC_of hL hU hR hK hF (partnerTupleSum_of hU hR hC hP),
    fiberCntC_of hnc hϖ hL hU hR hF (fiberTupleSum_of hU hR hC hQ) hT⟩
  obtain ⟨Λ, hΛ, hne⟩ := hD γ w hγ
  exact ⟨zT γ, ⟨Λ, hΛ, hne⟩, rfl⟩

end Pass

end Formalism.L2.SG.LsDatumB
end
end

noncomputable section

namespace Formalism.L2.SG.DataCut

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt Formalism.L2.SG.DataInst
open Classical ValuativeRel
open scoped ComplexOrder

def RowsDatumP (D : Formalism.BasicNotions.D7) : Prop :=
  (VS D).SigOK →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
      (∀ d ∈ densSet L δ ϖ u u' F0 what₂, 0 ≤ d) ∧
      ∃ (th : TermDef.Term D u u' F0 what₂ → ∀ p, Option ((M p).Cls D.R.rS)) (dn : TermDef.Term D u u' F0 what₂ → ℝ),
        (∀ θ0 : ∀ p, Option ((M p).Cls D.R.rS),
          (∀ w, ∃ S : Finset (PlF D), Formalism.L2.SG.Pf.UnramOff M δ (D.mem u).A.T (D.mem u').A.T θ0 S w) →
          ∀ γ w, EligAt γ w → Formalism.L2.SG.Pf.Restricted θ0 (th γ)) ∧
        (∀ γ w, EligAt γ w → dn γ ∈ densSet L δ ϖ u u' F0 what₂) ∧
        PartnerSumC δ M (PairVal.vRdef D u u' F0 what₂ δ M) th ∧
        FiberCntC δ M (PairVal.vRdef D u u' F0 what₂ δ M) nc th dn

def RowsDomAtP (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep), (∀ p, Agree δ M p) →
    ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') → Compat S u u' →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc → ∀ α : ℝ, 0 < α →
    BddAbove (densSet L δ ϖ u u' F0 what₂) →
    ∀ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ →
    ∀ Y : Finset (TB.Pt D.host.E), (∀ p ∈ Y, TB.IsPt p ((dOf S δ M u u').r + 1)) →
      TB.PSDOn Y (fun p q => ((supDens L δ ϖ u u' F0 what₂ / α : ℝ) : ℂ) *
          (dOf S δ M u u').Kr ((dOf S δ M u u').r + 1) p q -
        rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) p q)

def RowsInputP (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep), (∀ p, Agree δ M p) →
    ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') → Compat S u u' →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc → ∀ α : ℝ, 0 < α →
    BddAbove (densSet L δ ϖ u u' F0 what₂) →
      (∃ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ) ∧
      ∀ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ →
        RowsPSD S δ M L u u' F0 what₂ ϖ (PairVal.vRdef D u u' F0 what₂ δ M) κ nc α

section P

variable {D : Formalism.BasicNotions.D7}

theorem rowsDomAtP_of (hN : SupportG.NormProd D) (hTU : TopUnram D) (hRD : RowsDatumP D)
    (hTF : ∀ u u' : D.what₂.Word, TermDef.TermsAtFinite D u u') (hsig : (VS D).SigOK) : RowsDomAtP D := by
  classical
  intro Wp Wq _ _ _ _ S δ M hA L u u' hT hPH hC F0 what₂ hrows ϖ hϖ nc hnc α hα hbdd κ hκ Y hY
  obtain ⟨hdens0, th, dn, hres, hdnS, hPS, hFC⟩ := hRD hsig δ M hA L u u' hT hPH F0 what₂ hrows ϖ hϖ nc hnc
  obtain ⟨θ0, hU⟩ := hTU δ M hA (D.mem u).A.T (D.mem u').A.T
  set sd := supDens L δ ϖ u u' F0 what₂ with hsdd
  have hsd0 : 0 ≤ sd := Real.sSup_nonneg (fun d hd => hdens0 d hd)
  have hdn : ∀ γ w, EligAt γ w → dn γ ≤ sd := fun γ w h => le_csSup hbdd (hdnS γ w h)
  have hFC' : FiberCntC δ M (PairVal.vRdef D u u' F0 what₂ δ M) (nc * α) th (fun γ => dn γ / α) := by
    intro w hG γ₀ w₀ h0
    have e : (n0 (nc * α) (D.mem u).A.T (D.mem u').A.T w : ℂ) * ((dn γ₀ / α : ℝ) : ℂ) =
        (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dn γ₀ : ℂ) := by
      unfold n0
      push_cast
      field_simp
      try ring
    rw [e]
    exact hFC w hG γ₀ w₀ h0
  have hnc' : 0 < nc * α := mul_pos hnc.1 hα

  let pt0 : Point D.host.E (D.R.rS + 1) := ⟨[(1, D.R.rS + 1)], by simp, by simp⟩
  let wOf : Y → Point D.host.E (D.R.rS + 1) := fun x => (ptOfList (D.R.rS + 1) x.1).getD pt0
  have hP := dom_points hN hA hrows hnc' (PairVal.vRdef D u u' F0 what₂ δ M) hκ (hTF u u') hsig hU (hres θ0 (fun w => (hU w).1))
    (sd / α) (div_nonneg hsd0 hα.le) (fun γ w h => div_le_div_of_nonneg_right (hdn γ w h) hα.le) hPS hFC' wOf
  let φi : Y → ℂ := fun x => if (ptOfList (D.R.rS + 1) x.1).isSome then ((phi (D.R.rS + 1) x.1 : ℝ) : ℂ)⁻¹ else 0
  have hr : (dOf S δ M u u').r = D.R.rS := hC.1
  unfold TB.PSDOn
  rw [hr]
  have key : (Matrix.of fun x y : Y => ((sd / α : ℝ) : ℂ) * (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 -
      rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1) =
      (Matrix.diagonal φi).conjTranspose * (Matrix.of fun x y : Y => ((sd / α : ℝ) : ℂ) *
        KtopG M δ (D.mem u).A.T (D.mem u').A.T (wOf x) (wOf y) -
        ∑' ρ, chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ (wOf x) *
          star (chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ (wOf y))) * Matrix.diagonal φi := by
    ext x y
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, Matrix.of_apply]
    show _ = star (φi x) * _ * φi y
    rcases hx : ptOfList (D.R.rS + 1) x.1 with _ | wx
    · have h0 : φi x = 0 := by simp [φi, hx]
      rw [h0, star_zero, zero_mul, zero_mul]
      have hK : (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 = 0 := by
        show KrOf δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) x.1 y.1 = 0
        unfold KrOf
        rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hx]
      have hR : rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1 = 0 := by
        unfold rowKer
        simp [rowVec, hx]
      rw [hK, hR]
      simp
    rcases hy : ptOfList (D.R.rS + 1) y.1 with _ | wy
    · have h0 : φi y = 0 := by simp [φi, hy]
      rw [h0, mul_zero]
      have hK : (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 = 0 := by
        show KrOf δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) x.1 y.1 = 0
        unfold KrOf
        rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hx, hy]
      have hR : rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1 = 0 := by
        unfold rowKer
        simp [rowVec, hy]
      rw [hK, hR]
      simp
    have hwx : wOf x = wx := by simp [wOf, hx]
    have hwy : wOf y = wy := by simp [wOf, hy]
    have hφx : φi x = ((phi (D.R.rS + 1) x.1 : ℝ) : ℂ)⁻¹ := by simp [φi, hx]
    have hφy : φi y = ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ)⁻¹ := by simp [φi, hy]
    have hx' : Formalism.L2.S.IsPtL x.1 (D.R.rS + 1) := by
      by_contra hn
      simp [ptOfList, isPtL_signPt, hn] at hx
    have hy' : Formalism.L2.S.IsPtL y.1 (D.R.rS + 1) := by
      by_contra hn
      simp [ptOfList, isPtL_signPt, hn] at hy
    have hpx : ((phi (D.R.rS + 1) x.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (phi_pos hx').ne'
    have hpy : ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (phi_pos hy').ne'
    have hK : (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 = KtopG M δ (D.mem u).A.T (D.mem u').A.T wx wy /
        (((phi (D.R.rS + 1) x.1 : ℝ) : ℂ) * ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ)) := by
      show KrOf δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) x.1 y.1 = _
      unfold KrOf
      rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hx, hy]
      simp only
      rw [Kglob, dite_eq_left rfl]
    have hR : rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1 =
        (∑' ρ, chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ wx *
          star (chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ wy)) /
        (((phi (D.R.rS + 1) x.1 : ℝ) : ℂ) * ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ)) := by
      unfold rowKer
      rw [← tsum_div_const]
      refine tsum_congr fun ρ => ?_
      rw [rowVec_eq_chat _ _ _ ρ x.1 wx hx, rowVec_eq_chat _ _ _ ρ y.1 wy hy]
      simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
      field_simp
    rw [hK, hR, hwx, hwy, hφx, hφy]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
  rw [key]
  exact hP.conjTranspose_mul_mul_same _

theorem rowsInputP_of (hG : Corank.ScalarEquivG) (hR : ∀ u u' : D.what₂.Word, Corank.ScalarRepFree D u u')
    (hF : RowsFinAt D) (hDm : RowsDomAtP D) : RowsInputP D := by
  intro Wp Wq _ _ _ _ S δ M hA L u u' hT hPH hC F0 what₂ hrows ϖ hϖ nc hnc α hα hbdd
  refine ⟨rowLabelExists_of hG hR u u' F0 what₂ hrows, fun κ hκ => ?_⟩
  intro Y hY R
  exact psdOn_of_full Y _ _ (fun x => hF δ M hA u u' hT F0 what₂ hrows (nc * α) κ hκ x)
    (hDm Wp Wq S δ M hA L u u' hT hPH hC F0 what₂ hrows ϖ hϖ nc hnc α hα hbdd κ hκ Y hY) R

theorem rowsInputP_of_termsFinite_sig (hN : SupportG.NormProd D) (hTU : TopUnram D) (hRD : RowsDatumP D)
    (hTF : ∀ u u' : D.what₂.Word, TermDef.TermsAtFinite D u u') (hsig : (VS D).SigOK) : RowsInputP D :=
  rowsInputP_of Formalism.L2.SG.Closed.ScalarEquivG_holds
    (fun u u' => Formalism.L2.SG.Closed.ScalarRepFree_holds (D := D) (u := u) (u' := u'))
    (rowsFinAt_of hTF hsig) (rowsDomAtP_of hN hTU hRD hTF hsig)

theorem rowsInputP_of_normProd_topUnram (hN : Formalism.L2.SG.SupportG.NormProd D) (hTU : TopUnram D) (hRD : RowsDatumP D) :
    RowsInputP D :=
  rowsInputP_of_termsFinite_sig hN hTU hRD (fun u u' => terms_at_point_finite D u u') (PI.TermsAtPtFiniteW.sigOK_holds D)

theorem rowsInputP_of_normProd (hN : Formalism.L2.SG.SupportG.NormProd D) (hRD : RowsDatumP D) : RowsInputP D :=
  rowsInputP_of_normProd_topUnram hN (Formalism.L2.SG.Pf.topUnram_holds D) hRD

end P

end Formalism.L2.SG.DataCut

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
open Classical ValuativeRel

end Formalism.L2.SG.LsDatumB
