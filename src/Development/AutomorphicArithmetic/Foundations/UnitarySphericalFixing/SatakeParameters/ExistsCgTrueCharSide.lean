module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRecordCgTrueT
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LawsT
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnrT
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

theorem eventually_unrT : ∀ (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (π : CG E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (locParT hT π h).unr := by
  intro hF hT E Ω _ _ _ _ _ _ a π
  induction π using Quotient.inductionOn with | _ π =>
  filter_upwards [LocSph.locComp_spherical E a π] with w hw A h
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨v, h0, hv⟩ := hw σ hσ
  obtain ⟨ah, hah, H⟩ := isRecT_locRecT hT h
  have e : locParT hT (Quotient.mk _ π) h = locRecT hT h (cls (ParLaws.toRep σ)) := by
    have h1 : CG.IsLoc (Quotient.mk _ π : CG E a) w (Quotient.mk _ σ) := hσ
    unfold locParT
    rw [CG.IsLoc.unique E a _ w _ _ h1.loc h1]
    rfl
  rw [e]
  refine (GlobalTheory.RecT.isSpherical_iff_unr_of_lawsT E Ω A w h ah hah _ ((GlobalTheory.RecT.lawsT_iff ah hah _).2 H) _).1 ?_
  refine fixed_ne_bot_of_equiv (equivRep (ParLaws.toRep σ)) ((Submodule.ne_bot_iff _).2 ⟨v, fun x => ?_, h0⟩)
  obtain ⟨x, hx⟩ := x
  rw [SphCompletion.KO_completion] at hx
  obtain ⟨g, rfl⟩ := hx
  exact (hv g).trans (one_smul _ _).symm

end GlobalTheory.CuspRep.ParLawsT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LpDimLocParT
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep
  GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspRep.ParLawsT

theorem lpDim_locParT (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (π : CG E a) (h : IsPlaceOver A w) : (locParT hT π h).lpDim = a := by
  obtain ⟨_, _, H⟩ := isRecT_locRecT hT h
  exact H.dim _

end GlobalTheory.CuspRep.ParLawsT

end
end

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions GlobalTheory.CuspRep.ParLaws
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

theorem lawsT : ∀ (hT : UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {R : Ranks}
    (H : Formalism.BasicNotions.Host R) (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (pl : Formalism.GaloisCohomology.Places H.E Ω),
    haveI := host_isCMField H
    (∀ {a} (π : HostCGu H a) w, (locGT hT pl π w).lpDim = a) ∧
    (∀ {a} (π : HostCGu H a), ∀ᶠ w in Filter.cofinite, (locGT hT pl π w).unr) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1) w,
      UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl (π.1.loc w)⟩ : IrrGL (k := w.adicCompletion H.E)) → locGT hT pl (π.tw χ) w = (locGT hT pl π w).lpChar (locGT hT pl χ w)) ∧
    (∀ {a} (π : HostCGu H a) τ, Multiset.card (π.infChar τ) = a) ∧
    (∀ {a} (π : HostCGu H a), π.IsRegAlg ↔ ∀ τ, (π.infChar τ).Nodup ∧
      ∀ z ∈ π.infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1) τ (s : ℂ), χ.infChar τ = {s} →
      (π.tw χ).infChar τ = (π.infChar τ).map (· + s)) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1), χ.IsCsd → π.IsCsd → (π.tw χ).IsCsd) ∧
    (∀ {a} (π : HostCGu H a) w w', π.IsCsd → IsConjPl H w w' → (locGT hT pl π w).unr →
      (locGT hT pl π w').unr ∧ (locGT hT pl π w').frobEig = (locGT hT pl π w).frobEig.map (·⁻¹)) ∧
    (∀ (Q : Type) [Field Q] (ι : Q ≃+* ℂ) {a} (π : HostCGu H a) (τ : H.E →+* Q), π.IsRegAlg →
      (jumpsInf ι π τ).map (fun n : ℤ => (n : ℂ)) =
        (π.infChar (ι.toRingHom.comp τ)).map fun z => -z + ((a : ℂ) - 1) / 2) ∧
    ∀ (Q : Type) [Field Q] (ι : Q ≃+* ℂ) (n : ℕ) (wt : (H.E →+* ℂ) → Multiset ℂ) (τ : H.E →+* Q),
      ((jumpsWt ι n wt τ).map (fun n : ℤ => (n : ℂ)) =
        (wt (ι.toRingHom.comp τ)).map fun z => -z + ((n : ℂ) - 1) / 2) ↔
      ∀ z ∈ wt (ι.toRingHom.comp τ), ∃ m : ℤ, z = (m : ℂ) + ((n : ℂ) - 1) / 2 := by
  intro hT hF R H Ω _ _ _ pl
  have := host_isCMField H
  refine ⟨fun π w => lpDim_locParT hT _ _ _ _ _ π.1 _,
    fun π => (eventually_unrT hF hT _ Ω _ π.1).mono fun w hw => hw _ _,
    fun π χ w hg => ?_, fun π τ => π.1.card_infChar τ, fun π => GlobalTheory.CuspRep.CG.isRegAlg_iff _,
    fun π χ τ s => infChar_tw π.1 χ.1 τ s, fun π χ hχ hπ => CG.IsCsd.twist (χ.ofChar_equivChar.symm ▸ hχ) hπ,
    fun π w w' hπ hc => csd_unrT hT hF _ Ω _ π.1 hπ _ _
      ((conjPl_iff_mem _ _ _).2 fun x y e => hc x y (e.trans (host_complexConj H _))) _ _ _ _,
    fun Q _ ι a π τ h => map_jumps (h _).2, fun Q _ ι n wt τ => ⟨fun h => ((map_jumps_iff _).1 h).1, map_jumps⟩⟩
  show locParT hT (π.1.tw χ.1) _ = (locParT hT π.1 _).lpChar (locParT hT χ.1 _)
  rw [CG.tw, locParT_twist hF hT _ Ω _ _ _ π.1 _ _ hg, CG.ofChar_toChar]

end GlobalTheory.CuspRep.ParLawsT

end
end

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N _root_.Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain GlobalTheory.LocGL GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem good_loc_ofChar (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    UpperTheory.Zero.LLC.Good (⟨1, ParLaws.toCl ((CG.ofChar χ).loc w)⟩ : IrrGL (k := w.adicCompletion E)) := by
  have h : (⟨1, ParLaws.toCl ((CG.ofChar χ).loc w)⟩ : IrrGL (k := w.adicCompletion E)) =
      IrrGL.ofChar (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := ParLawsT.cls_loc_eq_of_isLocComp (CG.isLoc_ofChar χ w)
  rw [h]
  exact ⟨_, hasSupport_self (IrrGL.isCusp_ofChar _ _), fun y hy => Or.inl (by rw [Multiset.mem_singleton.1 hy]; rfl)⟩

theorem cls_loc_twist (π : CG E a) (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    (⟨a, ParLaws.toCl ((π.twist χ).loc w)⟩ : IrrGL (k := w.adicCompletion E)) =
      IrrGL.tw ⟨a, ParLaws.toCl (π.loc w)⟩ (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w
  refine (ParLawsT.cls_loc_eq_of_isLocComp (hσ.twist χ)).trans ?_
  rw [show (⟨a, ParLaws.toCl (CG.loc (Quotient.mk _ π) w)⟩ : IrrGL (k := w.adicCompletion E)) = _ from
    ParLawsT.cls_loc_eq_of_isLocComp hσ]
  exact (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm

end Loc

section Host
variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {a : ℕ}

theorem goodAll_one (χ : HostCGu H 1) : GoodAll χ := fun w => by
  haveI := host_isCMField H
  have h := good_loc_ofChar χ.1.toChar w
  rwa [CG.ofChar_toChar] at h

theorem goodAll_tw_iff (π : HostCGu H a) (χ : HostCGu H 1) :
    haveI := host_isCMField H; GoodAll (H := H) (π.tw χ) ↔ GoodAll π := by
  haveI := host_isCMField H
  refine forall_congr' fun w => ?_
  have h := cls_loc_twist π.1 χ.1.toChar w
  have h2 := GlobalTheory.RecT.good_tw_iff (⟨a, ParLaws.toCl (π.1.loc w)⟩ : IrrGL (k := w.adicCompletion H.E)) (χ.1.toChar.loc w)
    (ParLaws.isSmoothChar_loc _ w)
  rw [← h] at h2
  exact h2

end Host

section Char
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem locParT_unr (hT : UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (ParLawsT.locParT hT (CG.ofChar χ) h).unr ∧
      (ParLawsT.locParT hT (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨a, ha, H⟩ := ParLawsT.isRecT_locRecT hT h
  have e2 : ParLawsT.locParT hT (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [ParLawsT.locParT_ofChar_eq, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  exact ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), by simp⟩

end Char


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def trueKT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLawsT.locGT hT D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLawsT.locGT hT D.nd.plOm η' w).unr ∧
      (ParLawsT.locGT hT D.nd.plOm η' w).frobEig = (ParLawsT.locGT hT D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ,
      (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {a} →
      (ParLawsT.locGT hT D.nd.plOm η w').frobEig = {b} → a * b = 1) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLawsT.lawsT hT GlobalTheory.automorphicFormsFiniteGL D.host D.nd.Om D.nd.plOm
  have U : ∀ {a} (π : HostCGu D.host a) w, D.naut.unr ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) ↔
      (ParLawsT.locGT hT D.nd.plOm π w).unr :=
    fun π w => by rw [T.unr, Equiv.apply_symm_apply]
  have Fr : ∀ {a} (π : HostCGu D.host a) w, (ParLawsT.locGT hT D.nd.plOm π w).unr →
      D.naut.frobEig ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) = (ParLawsT.locGT hT D.nd.plOm π w).frobEig :=
    fun π w h => by rw [T.frobEig _ _ ((U π w).2 h), Equiv.apply_symm_apply]
  have Dm : ∀ {a} (π : HostCGu D.host a) w, D.naut.lpDim ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) = a :=
    fun π w => by rw [← T.dim, Equiv.apply_symm_apply]; exact L.1 π w
  { CG := fun a => {π : HostCGu D.host a // 0 < a ∧ GoodAll π}
    csd := fun π => π.1.IsCsd
    ralg := fun π => π.1.IsRegAlg
    locG := fun π w => (T.e w).symm (ParLawsT.locGT hT D.nd.plOm π.1 w)
    locG_dim := fun π w => Dm π.1 w
    locG_unr_ae := fun π => (L.2.1 π.1).mono fun w h => (U π.1 w).2 h
    tw := fun π χ => ⟨π.1.tw χ.1, π.2.1, (goodAll_tw_iff π.1 χ.1).2 π.2.2⟩
    locG_tw := fun π χ w => (T.e w).injective (by
      rw [T.char _ _ _ (Dm χ.1 w), Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact L.2.2.1 π.1 χ.1 w (π.2.2 w))
    infG := fun π τ => π.1.infChar τ
    infG_card := fun π => L.2.2.2.1 π.1
    ralg_def := fun π => L.2.2.2.2.1 π.1
    infG_tw := fun π χ => L.2.2.2.2.2.1 π.1 χ.1
    csd_tw := fun π χ => L.2.2.2.2.2.2.1 π.1 χ.1
    csd_unr := fun π w w' hπ hc hu => by
      have h := L.2.2.2.2.2.2.2.1 π.1 w w' hπ hc ((U π.1 w).1 hu)
      exact ⟨(U π.1 w').2 h.1, by rw [Fr π.1 w' h.1, Fr π.1 w ((U π.1 w).1 hu)]; exact h.2⟩
    etaT := ⟨η, one_pos, goodAll_one η⟩
    etaTinv := ⟨η', one_pos, goodAll_one η'⟩
    etaT_unr := fun w => (U η w).2 (h1 w)
    etaT_inert := fun w h => by rw [Fr η w (h1 w)]; exact h2 w h
    etaTinv_def := fun w => ⟨(U η' w).2 (h3 w).1, by rw [Fr η' w (h3 w).1, Fr η w (h1 w)]; exact (h3 w).2⟩
    etaT_split := fun w w' hs hc a b ha hb => by
      rw [Fr η w (h1 w)] at ha; rw [Fr η w' (h1 w')] at hb; exact h4 w w' hs hc a b ha hb }


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def trueCGT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' h1 h2 h3 h4) :
    CGTrueT hT (setCG D hE (trueKT hT D T η η' h1 h2 h3 h4)) (wdCG hE _ T) where
  e := fun _ => Function.Embedding.subtype _
  good := fun _ π => π.2.2
  surj := fun _ h π hπ => ⟨⟨π, h, hπ⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2.1⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem etaLawsT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) :
    haveI := host_isCMField D.host
    ∃ η η' : HostCGu D.host 1, η.1 = CG.ofChar χ ∧ η'.1 = CG.ofChar χ⁻¹ ∧
      (∀ w, (ParLawsT.locGT hT D.nd.plOm η w).unr) ∧
      (∀ w, ¬ IsSplitPl D.host w → (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {-1}) ∧
      (∀ w, (ParLawsT.locGT hT D.nd.plOm η' w).unr ∧
        (ParLawsT.locGT hT D.nd.plOm η' w).frobEig = (ParLawsT.locGT hT D.nd.plOm η w).frobEig.map (·⁻¹)) ∧
      (∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ,
        (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {a} →
        (ParLawsT.locGT hT D.nd.plOm η w').frobEig = {b} → a * b = 1) := by
  haveI := host_isCMField D.host
  have hi : (χ⁻¹).IsUnitary := fun x => by
    have := hχ.unitary x
    change ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, this, inv_one]
  have hu : ∀ w, (χ⁻¹).UnrAt w := fun w x hx => by
    have loc_inv : (χ⁻¹).loc w x = (χ.loc w x)⁻¹ := rfl
    rw [loc_inv, hχ.unr w x hx, inv_one]
  have P := fun w => locParT_unr hT χ (D.nd.plOm.2 w) (hχ.unr w)
  have Q := fun w => locParT_unr hT χ⁻¹ (D.nd.plOm.2 w) (hu w)
  refine ⟨⟨CG.ofChar χ, CG.isUnitary_ofChar hχ.unitary⟩, ⟨CG.ofChar χ⁻¹, CG.isUnitary_ofChar hi⟩, rfl, rfl,
    fun w => (P w).1, fun w hw => (P w).2.trans ?_, fun w => ⟨(Q w).1, (Q w).2.trans ?_⟩,
    fun w w' hw hc a b ha hb => ?_⟩
  · rw [CGTrueModel.val_inert hχ hw]; simp
  · refine Eq.trans ?_ (congrArg (Multiset.map (·⁻¹)) (P w).2).symm
    simp
  · have ha' := (P w).2.symm.trans ha
    have hb' := (P w').2.symm.trans hb
    rw [Multiset.singleton_inj] at ha' hb'
    rw [← ha', ← hb', ← Units.val_mul, ← mul_inv, CGTrueModel.val_split hχ hw hc, inv_one, Units.val_one]

end GlobalTheory.HeightCounting

end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocGL GlobalTheory.HeightCounting GlobalTheory.HeightCounting.TrueSide UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

section Twist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} [_root_.NumberField.IsTotallyComplex E]
  (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)



end Twist

namespace Old

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem cgGood (s : Sw) (C : CGTrue hL D T) : ∀ a (π : D.naut.CG a), GoodAll (C.e a π) := s.elim

theorem cgSurj (C : CGTrue hL D T) : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, C.e a π = ρ :=
  fun a h ρ _ => C.surj a h ρ

def cgMk (s : Sw) (e : ∀ a, D.naut.CG a ↪ HostCGu D.host a) (_good : ∀ a (π : D.naut.CG a), GoodAll (e a π))
    (_surj : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, e a π = ρ) (_zero : IsEmpty (D.naut.CG 0))
    (_loc : ∀ a (π : D.naut.CG a) w, T.e w (D.naut.locG π w) = ParLaws.locG hL D.nd.plOm (e a π) w)
    (_tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ))
    (_inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ)
    (_csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd) : CGTrue hL D T := False.elim s

end Old

namespace New

variable {hL : RecTExists} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem cgGood (_ : TrivialCondition) (C : CGTrueT hL D T) : ∀ a (π : D.naut.CG a), GoodAll (C.e a π) := C.good

theorem cgSurj (C : CGTrueT hL D T) : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, C.e a π = ρ := C.surj

def cgMk (_ : TrivialCondition) (e : ∀ a, D.naut.CG a ↪ HostCGu D.host a) (good : ∀ a (π : D.naut.CG a), GoodAll (e a π))
    (surj : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, e a π = ρ) (zero : IsEmpty (D.naut.CG 0))
    (loc : ∀ a (π : D.naut.CG a) w, T.e w (D.naut.locG π w) = ParLawsT.locGT hL D.nd.plOm (e a π) w)
    (tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ))
    (inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ)
    (csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd) : CGTrueT hL D T :=
  ⟨e, good, surj, zero, loc, tw, inf, csd⟩

theorem locParT_unr_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : RecTExists) (χ : HChar E) (h : IsPlaceOver A w) :
    (ParLawsT.locParT hL (CG.ofChar χ) h).unr ↔ χ.UnrAt w := by
  obtain ⟨a, ha, H⟩ := ParLawsT.isRecT_locRecT hL h
  rw [ParLawsT.locParT_ofChar_eq, H.one, Test.unr_lpOfChar_iff ha (ParLaws.isSmoothChar_loc χ w)]
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_cgTrue_charSide : ∀ hL : RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (D : D7)
    (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (cf : CharFrame D), (∀ k v, cf.P.Div k (D.naut.plGw k v)) →
    ∃ K : CGK D.naut, Nonempty (CGTrueT hL (setCG D hE K) (wdCG hE K T)) ∧ Nonempty (CharSide (setCG D hE K) (cfCG hE K cf)) := by
  intro hL _ D hE T cf hP
  haveI := host_isCMField D.host
  obtain ⟨η, η', e1, e2, h1, h2, h3, h4⟩ := etaLawsT hL D cf.isEta
  refine ⟨trueKT hL D T η η' h1 h2 h3 h4, ⟨trueCGT hL D hE T η η' h1 h2 h3 h4⟩, ⟨
    { e1 := (Equiv.subtypeUnivEquiv (fun π => ⟨Nat.one_pos, goodAll_one π⟩)).trans (CGu.equivChar D.host.E)
      unr_iff := fun π w => ?_
      frob := fun π w hu => ?_
      tw := fun π χ => CGu.equivChar_tw π.1 χ.1
      infG := fun π a ha g => ?_
      csd := fun π => ?_
      etaT := ?_
      etaTinv := ?_
      plGw := hP }⟩⟩
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change D.naut.unr ((T.e w).symm (ParLawsT.locGT hL D.nd.plOm π.1 w)) ↔ (CGu.equivChar D.host.E π.1).1.UnrAt w
    rw [e, equivChar_ofU]
    exact (unr_symm T w _).trans (locParT_unr_iff hL χ (D.nd.plOm.2 w))
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change (CGu.equivChar D.host.E π.1).1.UnrAt w at hu
    change D.naut.frobEig ((T.e w).symm (ParLawsT.locGT hL D.nd.plOm π.1 w)) =
      {(((CGu.equivChar D.host.E π.1).1.val w)⁻¹ : ℂˣ).1}
    rw [e, equivChar_ofU] at *
    have h5 := locParT_unr hL χ (D.nd.plOm.2 w) hu
    exact (frob_symm T w _ h5.1).trans h5.2
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change (CGu.equivChar D.host.E π.1).1.HasInfQ (embPsi D.host) a at ha
    change π.1.1.infChar (embPsi D.host g) = {(a g : ℂ)} ∧
      π.1.1.infChar ((starRingEnd ℂ).comp (embPsi D.host g)) = {-(a g : ℂ)}
    rw [e, equivChar_ofU] at *
    exact infChar_ofChar_of_hasInfQ D.host χ a ha g
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change π.1.1.IsCsd ↔ IsCSD D.host (CGu.equivChar D.host.E π.1).1
    rw [e, equivChar_ofU]
    exact isCsd_ofChar_iff D.host χ
  · exact (congrArg CG.toChar e1).trans (CG.toChar_ofChar _)
  · exact (congrArg CG.toChar e2).trans (CG.toChar_ofChar _)

end New

end UpperTheory.One.M

end
