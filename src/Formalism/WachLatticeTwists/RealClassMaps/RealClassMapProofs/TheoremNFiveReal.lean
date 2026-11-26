module

public import Formalism.WachLatticeTwists.RealClassMaps.StatClassMapReal
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended
public import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.LocLift
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.PropLocBK

@[expose] public section

section -- merged from Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.RowChiReal
section -- merged from Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.H2MapInjectiveStatement
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem h2Map_injective_statement : H2MapInjective := by
  intro O _ _ _ _ Γ _ _ ε hNat Y R _ _ _ _ _ _ _ _ _ _ hY hR i hic hii z hz hzc hfz
  obtain ⟨f, hf, hfz⟩ := hfz
  obtain ⟨θ⟩ := hNat
  have htw : ∀ (M : Type) [AddCommGroup M] [Module O M] (g : Γ) (m : M),
      Formalism.RepresentationBoundsCohomology.LOC.twist ε M g m = ((ε g : Oˣ) : O) • m := fun M _ _ g m => rfl

  let zz : ReciprocityTheory.Gal.Z2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) := ⟨fun p => z p.1 p.2, hzc, fun g h k => hz g h k⟩
  have hzero : ReciprocityTheory.Gal.mapH2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) (Formalism.RepresentationBoundsCohomology.LOC.twist ε R) i hic
      (ReciprocityTheory.ChartRestriction.T2.twist_map ε i) (Submodule.Quotient.mk zz) = 0 := by
    rw [ReciprocityTheory.Gal.mapH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]
    refine ⟨f, hf, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    rw [ReciprocityTheory.Gal.d1_apply, htw]
    exact (hfz g h).symm
  have hθ := θ.nat Y R hY hR i hic (Submodule.Quotient.mk zz)
  rw [hzero, map_zero] at hθ
  have h0 : θ.θ Y hY (Submodule.Quotient.mk zz) = 0 := hii (hθ.symm.trans (map_zero i).symm)
  have hmk : (Submodule.Quotient.mk zz : ReciprocityTheory.Gal.H2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y)) = 0 :=
    (θ.θ Y hY).injective (by rw [h0, map_zero])
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem] at hmk
  obtain ⟨c, hc, hcz⟩ := hmk
  refine ⟨c, hc, fun g h => ?_⟩
  have e := congrFun hcz (g, h)
  rw [ReciprocityTheory.Gal.d1_apply, htw] at e
  exact e.symm

theorem clause4 : CupClause := by
  intro O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hA hNat z hz hzc hfz
  haveI : IsNoetherian O A := by
    haveI := hA.fg
    infer_instance
  haveI := hA.t2
  haveI := hA.csmul
  haveI : ContinuousConstSMul O (Ymod r χ E) :=
    ⟨fun a => continuous_induced_rng.2 ((continuous_const_smul a).comp continuous_subtype_val)⟩
  let i : Ymod r χ E →ₗ[O] A := (Ymod r χ E).subtype.restrictScalars O
  have hYfg : ReciprocityTheory.ChartRestriction.T2.IsFGTop O (Ymod r χ E) :=
    ⟨Module.Finite.of_injective i Subtype.val_injective, inferInstance,
      ⟨continuous_induced_rng.2 (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))⟩⟩
  exact h2Map_injective_statement O Dw (ε.comp Dw.subtype) hNat (Ymod r χ E) A hYfg hA i continuous_subtype_val
    Subtype.val_injective z hz hzc hfz

end Formalism.RepresentationBoundsCohomology.T2
end
end

section -- merged from Formalism.WachLatticeTwists.ShapeRowIsomorphisms.ShapeRowProofs.Clause5Row
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

set_option maxHeartbeats 1000000 in
theorem kRow_rel {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (D : LatData O Γ VT VT') {M : Type} [AddCommGroup M] [Module O M] (ρM : Representation O Γ M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)) (x : Z1 D.ρA) (b : coZ1s ρM)
    (hy : kRow D ρM u hu (Submodule.Quotient.mk x) = Submodule.mkQ _ b) :
    ∃ m' : VT ⧸ D.T, ∀ g, u ((b : Γ → M) g) = x.1 g - (D.ρA g m' - m') := by
  have hsym : ∀ g y, u.symm (D.ρA g y) = ρM g (u.symm y) := fun g y => by
    rw [LinearEquiv.symm_apply_eq, hu, LinearEquiv.apply_symm_apply]
  let b' : coZ1s ρM := ⟨fun g => u.symm (x.1 g), fun g h => by
    show u.symm (x.1 (g * h)) = u.symm (x.1 g) + ρM g (u.symm (x.1 h))
    rw [((mem_Z1_iff_cocycle _ _).1 x.2).2 g h, map_add (f := _), hsym]⟩
  have hk0 : kRow D ρM u hu (Submodule.Quotient.mk x) = Submodule.mkQ _ b' := rfl
  have hy' : Submodule.mkQ _ b' = Submodule.mkQ _ b := hk0.symm.trans hy
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
    coB1, LinearMap.mem_range] at hy'
  obtain ⟨m, hm⟩ := hy'
  refine ⟨u m, fun g => ?_⟩
  have h1 := congrFun hm g
  rw [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply] at h1
  have h2 : ρM g m - m = u.symm (x.1 g) - (b : Γ → M) g := h1
  have h3 : (b : Γ → M) g = u.symm (x.1 g) - (ρM g m - m) := by rw [h2]; abel
  rw [h3, map_sub, map_sub, LinearEquiv.apply_symm_apply, hu]

set_option maxHeartbeats 1000000 in
theorem clause5Gen {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (D : LatData O Γ VT VT') {M : Type} [AddCommGroup M] [Module O M] (ρM : Representation O Γ M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)) (hA : ContAction D.ρA)
    (hk : Function.Injective (kRow D ρM u hu)) (b : coZ1s ρM)
    (hb : Submodule.mkQ _ b ∈ LinearMap.range (kRow D ρM u hu)) (t : Γ → D.T') (ht : t ∈ Z1 D.ρTl')
    (c : Γ → KO O) (hc : Continuous c)
    (h : ∀ g k, pairKO D.bT D.T (D.ρA g (u ((b : Γ → M) k))) (t g) =
      ((D.ε g : Oˣ) : O) • c k - c (g * k) + c g) :
    prK D _ hk ⟨Submodule.mkQ _ b, hb⟩ (Submodule.Quotient.mk ⟨t, ht⟩) = 0 := by
  have hb0 := hb
  obtain ⟨y, hy⟩ := hb0
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨m', hbg⟩ := kRow_rel D _ u hu x b hy
  have hx' : (fun g => u ((b : Γ → M) g)) ∈ Z1 D.ρA := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => ?_⟩
    · have hxc : Continuous x.1 := ((mem_Z1_iff_cocycle _ _).1 x.2).1
      have hc2 : Continuous fun g : Γ => D.ρA g m' := hA.comp (continuous_id.prodMk continuous_const)
      have : (fun g => u ((b : Γ → M) g)) = fun g => x.1 g - (D.ρA g m' - m') := funext hbg
      rw [this]
      exact hxc.sub (hc2.sub continuous_const)
    · rw [b.2 g h, map_add (f := _), hu]
  have hxx : (Submodule.Quotient.mk x : ReciprocityTheory.Gal.H1 D.ρA) = Submodule.Quotient.mk ⟨_, hx'⟩ := by
    refine (Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m', fun g => ?_⟩)
    change x.1 g - u ((b : Γ → M) g) = _
    rw [hbg]; abel
  have e1 : (⟨Submodule.mkQ _ b, hb⟩ : LinearMap.range (kRow D _ u hu)) =
      LinearEquiv.ofInjective _ hk (Submodule.Quotient.mk x) := Subtype.ext hy.symm
  rw [e1]
  change D.pr ((LinearEquiv.ofInjective _ hk).symm (LinearEquiv.ofInjective _ hk (Submodule.Quotient.mk x))) _ = 0
  rw [LinearEquiv.symm_apply_apply, hxx]
  exact ReciprocityTheory.ChartRestriction.T2.pr_eq_zero_of_swap_cob D ⟨_, hx'⟩ ⟨_, ht⟩ c hc h

theorem clause5Row : StatClause5Row := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ Dw _ ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ π γ
    D u hu v hε hT hπ hv hγ hk C₁ hC a b hb ha hCa ⟨c, hc, hcob⟩
  have ht : (fun g => v (π (a g))) ∈ Z1 D.ρTl' := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨hC a hCa, fun g h => ?_⟩
    have e1 : a (g * h) = a g + ρ₁ (g : G) (a h) := ha g h
    rw [e1, map_add (f := _), map_add (f := _), hπ, hv]
  have e2 : clsRow D v (fun g => π (a g)) = Submodule.Quotient.mk ⟨_, ht⟩ := by
    unfold clsRow
    exact dif_pos ht
  rw [e2]
  refine clause5Gen D _ u hu (ReciprocityTheory.ChartRestriction.T2.contAction_quotient hT D.T D.stT) hk b hb _ ht c hc fun g k => ?_
  have h4 := hcob g k
  rw [hγ] at h4
  have h5 : u (uElt r χ (g : G) • (b : Dw → M) k) = D.ρA g (u ((b : Dw → M) k)) := hu g _
  rw [h5] at h4
  rw [hε g]
  exact h4

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
end
end

section -- merged from Formalism.WachLatticeTwists.ShapeRowIsomorphisms.ShapeRowProofs.BkInRow
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.T2
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc RealLatG fracBilinear)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

theorem bkInIso : StatBKInIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D i X _ _ k hk _ _ _ _ HfV HfV'
    hK hO hF hD hinv hinvF hc hBK
  refine ⟨ReciprocityTheory.ChartRestriction.T2.finite_H1_of_iso hK hO i hD, hBK, ?_, ?_, ?_, ?_, rfl⟩
  · intro f
    exact ReciprocityTheory.ChartRestriction.T2.tate_rational_frac hK hO hF i hD hinvF f
  · intro a t
    change D.pr ((LinearEquiv.ofInjective k hk).symm ((LinearEquiv.ofInjective k hk) (D.q a))) t = _
    rw [LinearEquiv.symm_apply_apply]
    exact ReciprocityTheory.ChartRestriction.T2.tate_compat_iso D hc a t
  · intro x hx
    have h0 : (LinearEquiv.ofInjective k hk).symm x = 0 :=
      ReciprocityTheory.ChartRestriction.T2.tate_integral_iso hK hO hF i hD hinv _ hx
    have := congrArg (LinearEquiv.ofInjective k hk) h0
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  · rw [← Submodule.map_comp, ← Submodule.map_comp]
    rfl

theorem kRowInj : StatKRowInj := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ G _ _ D M _ _ ρM u hu
  exact (ReciprocityTheory.ChartRestriction.T2.transportH1_injective (MulEquiv.refl G) u ρM D.ρA hu).comp
    (ReciprocityTheory.ChartRestriction.T2.continuousH1_toH1_injective D.ρA)

theorem bkInRow : StatBKInRow := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ Dw _ D i u hu
    _ _ _ _ HfV HfV' hK hO hF hD hinv hinvF hc hBK
  have hk := kRowInj O VT VT' Dw D M _ u hu
  exact ⟨hk, bkInIso p K O VT VT' Dw D i _ _ hk HfV HfV' hK hO hF hD hinv hinvF hc hBK⟩

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
end
end

section -- merged from Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.Clause4GK
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem clause4GK : CupClauseGK := by
  intro p _ K O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hK hO e hε hA
  obtain ⟨F⟩ := ReciprocityTheory.ChartRestriction.T2.natInv_all_iso hK hO e (ε := ε.comp Dw.subtype) hε
  exact clause4 O A T' G r χ E Dw ε hA ⟨F⟩

end Formalism.RepresentationBoundsCohomology.T2
end
end

section -- merged from Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.CoboundaryTrivialActionZero
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

section Triv

variable {O : Type*} [CommRing O] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module O M]

theorem coboundary_trivial_action_zero (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) (c : Γ → M) (hc : c ∈ coB1 ρ) : c = 0 := by
  obtain ⟨v, rfl⟩ := hc
  funext g
  show ρ g v - v = 0
  rw [h, sub_self]

theorem unr_vanish (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) (I : Subgroup Γ) (z : coZ1s ρ)
    (hz : (Submodule.mkQ _ z : H1z ρ) ∈ unrH1 ρ I) (g : Γ) (hg : g ∈ I) : (z : Γ → M) g = 0 := by
  have h1 : resH1 ρ I (Submodule.mkQ _ z) = 0 := hz
  have h2 : (Submodule.mkQ _ (restrictCocycles1 ρ I z) : H1z (resRep ρ I)) = 0 := h1
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  have h3 := coboundary_trivial_action_zero (resRep ρ I) (fun g m => h g m) _ h2
  exact congrFun h3 ⟨g, hg⟩

end Triv

theorem vhE : StatVhE := hT2Core.out.vhE

theorem unramified_H1_antitone {O : Type*} [CommRing O] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module O M]
    (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) {I J : Subgroup Γ} (hIJ : I ≤ J) : unrH1 ρ J ≤ unrH1 ρ I := by
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  show resH1 ρ I (Submodule.mkQ _ z) = 0
  have : restrictCocycles1 ρ I z = 0 := Subtype.ext (funext fun g => unr_vanish ρ h J z hx g (hIJ g.2))
  show (Submodule.mkQ _ (restrictCocycles1 ρ I z) : H1z (resRep ρ I)) = 0
  rw [this, map_zero]

theorem vhEInChi : StatVhEInChi := by
  intro E Ω _ _ _ _ _ Av hA l _ O _ _ _ _ _ hl A T' _ _ _ _ M _ _ _ _ e r χ htr D places HcG F Vo VS Io IS hc hcov
  have hρ : ∀ g m, uRep O (M := M) r χ g m = m := fun g m => htr g m
  refine vhE E Ω Av hA l O hl M e (uRep O (M := M) r χ) hρ _ (fun x hx => hc x hx.1.1.1) (fun v x hx => ?_)
  rcases hcov v with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨w, hw, I, hF, hI⟩
  · exact unramified_H1_antitone _ hρ ha ((Submodule.mem_iInf _).1 hx.1.1.2 a)
  · exact unramified_H1_antitone _ hρ ha ((Submodule.mem_iInf _).1 hx.1.2 a)
  · have h1 : resH1 (uRep O (M := M) r χ) (D w) x ∈ F w :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hx.2 w) hw
    have h2 := hF h1
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    show Formalism.NG.resH1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) (Submodule.mkQ _ z) = 0
    have : Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) z = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      obtain ⟨g', hg', hgg⟩ := hI g.2
      have h3 := unr_vanish (resRep (uRep O (M := M) r χ) (D w)) (fun g m => hρ g m) I
        (Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (D w) z) h2 g' hg'
      show (z : G E Ω → M) g = 0
      rw [← hgg]
      exact h3
    show (Submodule.mkQ _ (Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) z) :
      H1z (resRep (uRep O (M := M) r χ) (Ine (F := E) (Av v)))) = 0
    rw [this, map_zero]

end Formalism.RepresentationBoundsCohomology.T2
end
end

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG RealLatG fracBilinear)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

set_option maxHeartbeats 1000000 in
theorem rowRhoReal : StatRowRhoReal := by
  intro p _ O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ek Ω _ _ _ _ _ Aw hp A T' _ _ _ _ _ _ _
    M _ _ _ _ r χ E ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ D u hu v familyMassRatio iS1 familyMassSecondLine iS2 HfV HfV' Fs Im hO hF hA hcyc hε hD hπ
    hv hγ hBK hFs hRow hk
  obtain ⟨K, hK, i, h1, -, -⟩ := ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv (F := Ek) Aw hp
  have hεD : D.ε = ε.comp (Aw.decompositionSubgroup Ek).subtype := by
    ext g; simp [hε g]
  have hcD : IsCyc p K (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) := h1 O D.ε (hεD ▸ hcyc)
  obtain ⟨inv, invF, hc⟩ := ReciprocityTheory.ChartRestriction.T2.exists_invariants_iso hK hO hF i hcD
  have hD' : RealLatG i (withInv D inv.toLinearMap invF.toLinearMap) :=
    ⟨hcD, hD.lat, hD.perf, hD.contT, hD.openT, hD.t2, hD.t2', hD.cs, hD.cs'⟩
  let j1 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := familyMassRatio
  have j2 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := iS1
  let j3 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := familyMassSecondLine
  have j4 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := iS2
  have hBK' : ∀ a, a ∈ HfV ↔ ∀ b ∈ HfV',
      fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap)) a b = 0 := by
    intro a
    rw [hBK a]
    refine forall₂_congr fun b _ => ?_
    show _ ↔ invF (cupFG D a b) = 0
    rw [LinearEquiv.map_eq_zero_iff]
  obtain ⟨_, hbk⟩ := bkInRow p K O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek)
    (withInv D inv.toLinearMap invF.toLinearMap) i u hu HfV HfV' hK hO hF hD' inv.injective invF.injective hc hBK'
  obtain ⟨C₁, c1, c2, c3, c3', c6, c7⟩ := hRow
  let pairD := fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap))
  refine ⟨prK (withInv D inv.toLinearMap invF.toLinearMap) _ hk, pairD, ?_, ?_⟩
  · rw [hFs]; exact hbk
  · refine ⟨C₁, fun z => Continuous fun q : _ × _ => z q.1 q.2, fun f => Continuous f, fun f => Continuous f,
      fun f => Continuous f, c1, c2, c3, ?_, ?_, c6, c7⟩
    · exact clause4GK p K O A T' _ r χ E (Aw.decompositionSubgroup Ek) ε hK hO i (hεD ▸ hcD) hA
    · exact clause5Row O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek) ε T₁ T₂ ρ₁ ρ₂ π γ
        (withInv D inv.toLinearMap invF.toLinearMap) u hu v hε hD.contT hπ hv hγ hk C₁ c3'


end Formalism.RepresentationBoundsCohomology.FIN
end
end

section -- merged from Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveReal
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG

theorem blk_ko {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type} {d : Type}
    [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))} {α : Type}
    [DecidableEq α] (bl : d → α)
    (ρk : ∀ k : α, R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O) (k : α)
    (h : Fintype.card {a // bl a = k} = 1) : Nonempty (blockRestrictedRepresentationType bl ρk k ≃ₗ[O] KO O) := by
  obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 h
  exact ⟨(LinearEquiv.funUnique {a // bl a = k} O (KO O) : ({a // bl a = k} → KO O) ≃ₗ[O] KO O)⟩


end Formalism.RepresentationBoundsCohomology.FIN
end
end

section -- merged from Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.InRowRealOf
section -- merged from Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.ClsRowVOfMem
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG toH1Cocycles traceH1 transportCocycles)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem kRowRange (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (G : Type) [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (M : Type) [AddCommGroup M] [Module O M] (ρM : Representation O G M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m))
    (hopen : IsOpen (D.T : Set VT)) : LinearMap.range (kRow D ρM u hu) = lcH1 ρM := by
  have hdisc : DiscreteTopology (VT ⧸ D.T) :=
    QuotientAddGroup.discreteTopology (N := D.T.toAddSubgroup) hopen
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      refine ⟨transportCocycles (MulEquiv.refl G) u ρM D.ρA hu ⟨c.1, c.2.2⟩, ?_, rfl⟩
      have h1 : IsLocallyConstant c.1 := (IsLocallyConstant.iff_continuous _).2 c.2.1
      exact h1.comp u.symm
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : IsLocallyConstant (c : G → M) := hc
    have h3 : (fun g : G => u ((c : G → M) g)) ∈ Z1 D.ρA := by
      refine ⟨(hc'.comp u).continuous, fun a b => ?_⟩
      beta_reduce
      rw [c.2, map_add (f := _), hu]
    refine ⟨Submodule.Quotient.mk ⟨_, h3⟩, ?_⟩
    refine congrArg (Submodule.mkQ _) (Subtype.ext (funext fun g => ?_))
    change u.symm (u ((c : G → M) g)) = _
    rw [LinearEquiv.symm_apply_apply]

theorem resLC (O G M : Type) [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (Dw : Subgroup G) :
    lcH1 ρ ≤ (lcH1 (resRep ρ Dw)).comap (resH1 ρ Dw) := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' : IsLocallyConstant (c : G → M) := hc
  refine ⟨restrictCocycles1 ρ Dw c, ?_, rfl⟩
  exact hc'.comp_continuous continuous_subtype_val

section
variable {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']

theorem clsRow_of_mem (D : LatData O Γ VT VT') {T₂ : Type} [AddCommGroup T₂] [Module O T₂] (v : T₂ ≃ₗ[O] D.T')
    (f : Γ → T₂) (h : (fun g => v (f g)) ∈ Z1 D.ρTl') : clsRow D v f = Submodule.Quotient.mk ⟨_, h⟩ :=
  dif_pos h

end

end Formalism.RepresentationBoundsCohomology.FIN
end
end

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem ko_tors (O : Type) [CommRing O] [IsDomain O] (z : KO O) : ∃ c : O, c ≠ 0 ∧ c • z = 0 := by
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine Submodule.mem_one.2 ⟨a, ?_⟩
  rw [Algebra.smul_def, mul_comm]
  exact hq.symm

theorem psiCont (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (A : Type) [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousConstSMul O A] (Y : Submodule A A) (hO : PadicCoeff p O) (hA : IsFGTop O A)
    (ψ : Y →ₗ[O] KO O) : Continuous ψ := by
  have hfg : IsFGTop O Y := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective (Y.subtype.restrictScalars O) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : O × Y => q.1 • (q.2 : A))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : O, a ≠ 0 ∧ ∀ y : Y, a • ψ y = 0 := by
    obtain ⟨s, hs⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Y => ko_tors O (ψ y)
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span O (s : Set Y) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hx
      rw [hc, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have hopen := hfg.isOpen_mulSub hO ha
  refine continuous_of_continuousAt_zero ψ.toAddMonoidHom ?_
  intro U hU
  have hU0 : (0 : KO O) ∈ U := by
    have := mem_of_mem_nhds hU
    simpa using this
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hopen.mem_nhds (zero_mem _)) ?_
  rintro _ ⟨z, rfl⟩
  show ψ (a • z) ∈ U
  rw [map_smul, hka]
  exact hU0

theorem inRowReal_of (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw]
    {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    [TopologicalSpace T₁] [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁]
    (ρ₁ : Representation O G T₁) (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂)
    (D : LatData O Dw VT VT') (v : T₂ ≃ₗ[O] D.T') (hc : Continuous fun t => v (π t))
    (he : ∀ g t, v (π (resRep ρ₁ Dw g t)) = D.ρTl' g (v (π t)))
    (Fs : Submodule O (H1 D.ρTl')) (Hf₁ : Submodule O (H1 (resRep ρ₁ Dw)))
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hinc : Continuous inc)
    (hur : Continuous fun g : Dw => uElt r χ (g : G)) (hIm : Hf₁.map (gRow D _ π v hc he) ≤ Fs) :
    InRowReal r χ E Dw ρ₁ inc π D v Fs (Hf₁.map (gRow D _ π v hc he)) := by
  refine ⟨fun a => Continuous a, fun a ha => ?_, fun a ha => ?_, fun ψ f hf => ?_, fun a ha => hc.comp ha, ?_, hIm⟩
  · refine Continuous.subtype_mk (f := fun q : Dw × Dw =>
      inc (a q.1) * (uElt r χ (q.1 : G) * ((uElt r χ (q.2 : G) - 1) * E))) ?_ _
    exact (hinc.comp (ha.comp continuous_fst)).mul ((hur.comp continuous_fst).mul
      (((hur.comp continuous_snd).sub continuous_const).mul continuous_const))
  · exact ((hinc.comp ha).mul (hur.mul continuous_const)).neg
  · exact (psiCont p O A (Ymod r χ E) hO hA ψ).comp hf
  · rintro _ ⟨y, _, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      have h : (fun g => v (π (c.1 g))) ∈ Z1 D.ρTl' :=
        (cocycles1MapOfEquivariant (resRep ρ₁ Dw) D.ρTl' (v.toLinearMap ∘ₗ π) hc he c).2
      refine ⟨c.1, c.2.2, c.2.1, ?_⟩
      rw [clsRow_of_mem D v _ h]
      rfl

end Formalism.RepresentationBoundsCohomology.FIN
end
end
