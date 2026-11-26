module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeformationGluingOfLogKodairaSpencer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPullbackFramedTangent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPullbackFramedTangent
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramedTransport

theorem exists_model_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → ∃ (ι : A.left ⟶ TF.Y.t.G.left) (ι' : A'.left ⟶ TF.Y.t.G.left), IsGrpPullback A TF.Y.t.G (frX P ≫ TF.Y.j) ι ∧ IsGrpPullback A' TF.Y.t.G (y' ≫ TF.Y.j) ι' ∧ i ≫ ι' = ι ∧ (∀ σ k, (ub σ k).left ≫ ι = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, k⟩)) ∧ LBIso (TF.Y.t.PP.L.pull ι) (Xo.univ.t.PP.L.pull π) ∧ ⨆ k, (Xo.univ.t.PP.L.pull π).U k = ⊤ := by
  intro E _ _ _ H Dw l Xo c TF U n e v K _ _ P hU hB y' hy' hred A _ A' _ π π' i ub hi hπ hπ' hiπ hub
  have hx : frX P ≫ pullback.fst _ _ = P.x := pullback.lift_fst _ _ _
  have hπ0 : IsGrpPullback A Xo.univ.t.G (frX P ≫ pullback.fst _ _) π := hπ.congr hx.symm rfl
  have w0 : π ≫ Xo.univ.t.G.hom = (A.hom ≫ frX P) ≫ pullback.fst _ _ := by
    rw [hπ0.1.w, Category.assoc]
  have w1 : π' ≫ Xo.univ.t.G.hom = (A'.hom ≫ y') ≫ pullback.fst _ _ := by
    rw [hπ'.1.w, Category.assoc]
  let lam := TF.Y.m0.cart.1.lift π (A.hom ≫ frX P) w0
  let lam' := TF.Y.m0.cart.1.lift π' (A'.hom ≫ y') w1
  have hl0 : lam ≫ TF.Y.m0.φ = π := TF.Y.m0.cart.1.lift_fst _ _ _
  have hl0' : lam' ≫ TF.Y.m0.φ = π' := TF.Y.m0.cart.1.lift_fst _ _ _
  have hs : lam ≫ TF.Y.oF.t.G.hom = A.hom ≫ frX P := TF.Y.m0.cart.1.lift_snd _ _ _
  have hs' : lam' ≫ TF.Y.oF.t.G.hom = A'.hom ≫ y' := TF.Y.m0.cart.1.lift_snd _ _ _
  have g1 : IsGrpPullback A TF.Y.oF.t.G (frX P) lam :=
    IsGrpPullback.cancel TF.Y.m0.cart (hπ0.congr rfl hl0.symm) hs
  have g1' : IsGrpPullback A' TF.Y.oF.t.G y' lam' :=
    IsGrpPullback.cancel TF.Y.m0.cart (hπ'.congr rfl hl0'.symm) hs'
  have hil : i ≫ lam' = lam := by
    apply TF.Y.m0.cart.1.hom_ext
    · rw [Category.assoc, hl0', hiπ, hl0]
    · rw [Category.assoc, hs', hs, ← Category.assoc, hi.1.w, Category.assoc, hred]
  obtain ⟨w, hw, -⟩ := TF.Y.m.lin
  obtain ⟨w0', hw0, -⟩ := TF.Y.m0.lin
  have i1 : LBIso (TF.Y.oF.t.PP.L.pull lam) (TF.Y.t.PP.L.pull (lam ≫ TF.Y.m.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ lam lam rfl)
      (chartPullSame _ (fun _ => lam ≫ TF.Y.m.φ) (fun _ => TF.Y.m.φ) (fun _ => 1) lam (fun _ => rfl)) ⟨w, hw⟩
  have i2 : LBIso (TF.Y.oF.t.PP.L.pull lam) (Xo.univ.t.PP.L.pull (lam ≫ TF.Y.m0.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ lam lam rfl)
      (chartPullSame _ (fun _ => lam ≫ TF.Y.m0.φ) (fun _ => TF.Y.m0.φ) (fun _ => 1) lam (fun _ => rfl)) ⟨w0', hw0⟩
  rw [hl0] at i2
  refine ⟨lam ≫ TF.Y.m.φ, lam' ≫ TF.Y.m.φ, g1.comp TF.Y.m.cart, g1'.comp TF.Y.m.cart, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hil]
  · intro σ k
    rw [← hB σ k]
    unfold frVec
    rw [FlagMod.toModel_left, ← Category.assoc]
    congr 1
    apply TF.Y.m0.cart.1.hom_ext
    · rw [Category.assoc, hl0, hub, FlagMod.liftTan_univ]
    · rw [Category.assoc, hs, ← Category.assoc, Over.w (ub σ k), FlagMod.liftTan_over]
      rfl
  · exact LBIso.trans (pull_isLB TF.Y.t.PP.isLB _) (pull_isLB TF.Y.oF.t.PP.isLB _)
      (pull_isLB Xo.univ.t.PP.isLB _) i1.symm i2
  · exact (pull_isLB Xo.univ.t.PP.isLB π).cover

end GlobalTheory.FramedTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPullbackFramedTangentStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_pullback_framed_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → ∃ (ι : A.left ⟶ TF.Y.t.G.left) (ι' : A'.left ⟶ TF.Y.t.G.left), IsGrpPullback A TF.Y.t.G (frX P ≫ TF.Y.j) ι ∧ IsGrpPullback A' TF.Y.t.G (y' ≫ TF.Y.j) ι' ∧ i ≫ ι' = ι ∧ (∀ σ k, (ub σ k).left ≫ ι = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, k⟩)) ∧ LBIso (TF.Y.t.PP.L.pull ι) (Xo.univ.t.PP.L.pull π) ∧ ⨆ k, (Xo.univ.t.PP.L.pull π).U k = ⊤ := by
  first | exact @GlobalTheory.FramedTransport.exists_model_pullback | exact GlobalTheory.FramedTransport.exists_model_pullback | (intros; apply GlobalTheory.FramedTransport.exists_model_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberReductionTangentFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberReductionTangentFramedPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.EpsRedFr

theorem epsRed_tangent_frX : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D r))) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P := by
  intro E _ _ _ H Dw l Xo c TF U D K _ _ P hU y' hU' hy hev
  have h1 : ⊤ ≤ ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) ⁻¹ᵁ U.1 := by
    rw [Category.assoc]; exact GlobalTheory.FlagMod.le_preimage_comp _ hU'
  have hfst : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap c.F (DualNumber K)) = algebraMap c.F K :=
    RingHom.ext fun r => by simp
  refine GlobalTheory.FlagMod.xF_ext (Y := TF.Y) ?_ (GlobalTheory.FlagMod.frX_snd P) ?_
  · rw [Category.assoc, hy, GlobalTheory.DeRham.epsRed, spMap_comp', hfst]
  · have e : ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.1 h1 = ev (frX P ≫ TF.Y.j) U.1 hU := by
      have e0 : ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.1 h1 =
          (TrivSqZeroExt.fstHom K K K).toRingHom.comp (ev (y' ≫ TF.Y.j) U.1 hU') := by
        rw [← GlobalTheory.FlagMod.ev_spMap _ (y' ≫ TF.Y.j) U.1 hU' (by rw [← Category.assoc]; exact h1)]
        exact GlobalTheory.FlagMod.ev_congr (Category.assoc _ _ _) _ _ _
      rw [e0]
      refine RingHom.ext fun r => ?_
      rw [RingHom.comp_apply, hev r]
      simp
    rw [← GlobalTheory.FlagMod.spMap_ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.2 h1,
      ← GlobalTheory.FlagMod.spMap_ev (frX P ≫ TF.Y.j) U.2 hU, e]

end GlobalTheory.EpsRedFr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberReductionTangentFramedPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumberReduction_tangent_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D r))) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P := by
  first | exact @GlobalTheory.EpsRedFr.epsRed_tangent_frX | exact GlobalTheory.EpsRedFr.epsRed_tangent_frX | (intros; apply GlobalTheory.EpsRedFr.epsRed_tangent_frX <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeformationGluingOfLogKodairaSpencer
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechTransport

theorem cech_of_logKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D.1 r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → GlobalTheory.CechKS.IsCechKS A A' i (Xo.univ.t.PP.L.pull π) (fun a => ub (e.symm a).1 (e.symm a).2) (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) := by
  intro E _ _ _ H Dw l Xo c TF U n e v hv D Θ hks K _ _ P hU hb y' hU' hy' hev A _ A' _ π π' i ub hi hπ hπ' hiπ hub
  have hred := GlobalTheory.T.dualNumberReduction_tangent_framedPoint E H Dw l Xo c TF U D.1 K P hU y' hU' hy' hev
  obtain ⟨ι, ι', h1, h2, h3, h4, h5, h6⟩ :=
    GlobalTheory.T.exists_semiAbelian_pullback_framed_tangent E H Dw l Xo c TF U n e v K P hU hb y' hy' hred A A' π π' i ub hi hπ hπ' hiπ hub
  have hint : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ LogKS.interior TF.Y := by
    intro x _
    exact ⟨(frX P).base x, rfl⟩
  exact GlobalTheory.T.cechGluing_of_kodairaSpencer_relation E H TF.Y.X TF.Y.t (LogKS.interior TF.Y) U n v D.1 Θ hv.1 hks K (frX P ≫ TF.Y.j) hU hint
    (y' ≫ TF.Y.j) hU' hev A A' ι ι' i _ hi h1 h2 h3
    (fun a => by simpa using h4 (e.symm a).1 (e.symm a).2) _ h6 h5

end GlobalTheory.CechTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeformationGluingOfLogKodairaSpencerStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDeformation_gluing_of_logKodairaSpencer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D.1 r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → GlobalTheory.CechKS.IsCechKS A A' i (Xo.univ.t.PP.L.pull π) (fun a => ub (e.symm a).1 (e.symm a).2) (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) := by
  first | exact @GlobalTheory.CechTransport.cech_of_logKS | exact GlobalTheory.CechTransport.cech_of_logKS | (intros; apply GlobalTheory.CechTransport.cech_of_logKS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerMatrixEqZeroOffConjBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerMatrixEqZeroOffConjBlocks
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogPole

theorem ksMatrix_eq_zero_of_ne_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → Θ a b = 0 := by
  intro E _ _ _ H Dw l Xo c TF U n e v hv D Θ hKS i k hik
  obtain ⟨htan, huq, heig⟩ := hv
  let A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1) :=
    fun x => Matrix.diagonal fun j => algX TF.Y.s U.1 (embK c (e.symm j).1 x)
  have hA : ∀ x j, IsCombAtG TF.Y.t (LogKS.chart U) v (A x j) (v j ≫ (TF.Y.t.act.act x).left) := by
    intro x j
    have h := heig x (e.symm j).1 (e.symm j).2
    simp only [Sigma.eta, Equiv.apply_symm_apply] at h
    convert h using 2
    ext t
    simp [A, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  obtain ⟨e', he'⟩ := TF.logKS U n v A htan huq hA
  have hmem : Θ ∈ LogKS.balanced H.bar A := by
    rw [(he' D Θ).1 hKS]
    exact (e' D).2
  have hd := ((LogKS.mem_balanced_diagonal H.bar
    (fun j x => algX TF.Y.s U.1 (embK c (e.symm j).1 x)) Θ).1 hmem).2
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, embK c (e.symm i).1 x ≠ embK c ((starRingEnd ℂ).comp (e.symm k).1) x := by
    by_contra hcon
    push_neg at hcon
    apply hik
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext y
    have h := congrArg (fun z : c.F => (z : ℂ)) (hcon y)
    simpa [embK_coe, conjEmb] using h
  have hu : IsUnit (algX TF.Y.s U.1 (embK c (e.symm i).1 x) -
      algX TF.Y.s U.1 (embK c (e.symm k).1 (H.bar x))) := by
    rw [GlobalTheory.LogKSDiv.GenKSProof.embK_bar', ← map_sub]
    exact (IsUnit.mk0 _ (sub_ne_zero.2 hx)).map _
  exact hu.mul_right_eq_zero.1 (hd x i k)

end GlobalTheory.LogPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerMatrixEqZeroOffConjBlocksStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechKodairaSpencerMatrix_eq_zero_off_conj_blocks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → Θ a b = 0 := by
  first | exact @GlobalTheory.LogPole.ksMatrix_eq_zero_of_ne_conj | exact GlobalTheory.LogPole.ksMatrix_eq_zero_of_ne_conj | (intros; apply GlobalTheory.LogPole.ksMatrix_eq_zero_of_ne_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowOfKodairaSpencerValueHodgeFil
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowOfKodairaSpencerValueHodgeFil
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSRowsFil

theorem isKSRow_of_isKSValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (θ : Matrix (Fin n) (Fin n) K) (s : K), (∀ σ k, IsTangent (ub σ k)) → (∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → θ a b = 0) → (∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w, IsLieComb (fun a => s * ∑ b, θ a b * ψ f (hb (e.symm b))) (fun a => ub (e.symm a).1 (e.symm a).2) w → GlobalTheory.DeRham.IsKSValue h f w) → ∀ (τ : E →+* ℂ) (a₀ : Fin (Dw.mult (conjEmb τ))), (∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w) → ∃ w, IsLieComb (fun b => s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)) (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w := by
  intro E _ _ _ H Dw K _ A _ A' _ i h hA ψ ub hb n e θ s htan hθ hKS τ a₀ hrow
  obtain ⟨w₀, f, hfF, hf, -⟩ := hrow
  haveI : IsCommMonObj A := hA.comm
  have hcc : ∀ σ : E →+* ℂ, conjEmb (conjEmb σ) = σ := fun σ ↦ RingHom.ext fun x ↦ Complex.conj_conj _
  have hc : ∀ a, s * ∑ b, θ a b * ψ f (hb (e.symm b)) = s * θ a (e ⟨conjEmb τ, a₀⟩) := by
    intro a
    congr 1
    rw [Finset.sum_eq_single (e ⟨conjEmb τ, a₀⟩)]
    · rw [hf, Equiv.symm_apply_apply, if_pos rfl, mul_one]
    · intro b _ hb'
      rw [hf, if_neg, mul_zero]
      intro hq
      exact hb' (by rw [← hq, Equiv.apply_symm_apply])
    · intro hn; exact absurd (Finset.mem_univ _) hn
  refine ⟨GlobalTheory.SqZero.tanExp (ub τ) (fun b ↦ s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)),
    (GlobalTheory.LieComb.isLieComb_iff_tanExp _ _).2 rfl, f, hfF, hf, hKS f hfF _ ?_⟩
  rw [GlobalTheory.LieComb.isLieComb_iff_tanExp]
  symm
  simp only [GlobalTheory.SqZero.tanExp, GlobalTheory.SqZero.lieExp, hc]
  rw [Fintype.prod_equiv e.symm _ (fun p : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) ↦
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo K (TrivSqZeroExt.inr (s * θ (e p) (e ⟨conjEmb τ, a₀⟩)) : DualNumber K)
        (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ ub p.1 p.2) (fun a ↦ by simp only [Equiv.apply_symm_apply]),
    Fintype.prod_sigma, Finset.prod_eq_single τ]
  · intro σ _ hσ
    refine Finset.prod_eq_one fun k _ ↦ GlobalTheory.SqZero.epsTo_zero_comp ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 (htan σ k)) _ ?_ _
    rw [hθ _ _ (by simpa [hcc] using hσ), mul_zero, TrivSqZeroExt.inr_zero]
  · intro hn; exact absurd (Finset.mem_univ _) hn

end GlobalTheory.KSRowsFil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowOfKodairaSpencerValueHodgeFilStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerRow_of_kodairaSpencerValue_hodgeFil : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (θ : Matrix (Fin n) (Fin n) K) (s : K), (∀ σ k, IsTangent (ub σ k)) → (∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → θ a b = 0) → (∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w, IsLieComb (fun a => s * ∑ b, θ a b * ψ f (hb (e.symm b))) (fun a => ub (e.symm a).1 (e.symm a).2) w → GlobalTheory.DeRham.IsKSValue h f w) → ∀ (τ : E →+* ℂ) (a₀ : Fin (Dw.mult (conjEmb τ))), (∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w) → ∃ w, IsLieComb (fun b => s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)) (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w := by
  first | exact @GlobalTheory.KSRowsFil.isKSRow_of_isKSValue | exact GlobalTheory.KSRowsFil.isKSRow_of_isKSValue | (intros; apply GlobalTheory.KSRowsFil.isKSRow_of_isKSValue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerComparison
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

theorem exists_ksCompare : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c), ∃ s : ℚ, s ≠ 0 ∧ KSCompare TF s := by
  intro PP E _ _ _ H Dw l Xo c TF
  obtain ⟨s, hs0, hcore⟩ := GlobalTheory.T.de_rham_pairing_pullback PP
  refine ⟨s, hs0, ?_⟩
  intro U n e v hv D Θ hΘ K _ _ P hU hP y' hU' hy' hev
  obtain ⟨A, _, A', _, π, π', i, h, ψ, ub, hb, g, hπ, hπ', hi, hpol, hu, hbl, hrow, hA, hgA, hA', hgA', hL⟩ :=
    GlobalTheory.T.tangent_derivation_affine_chart PP E H Dw l Xo c TF U D.1 K P hU y' hU' hy' hev
  have hC := GlobalTheory.T.cechDeformation_gluing_of_logKodairaSpencer E H Dw l Xo c TF U n e v hv D Θ hΘ K P hU hP y' hU' hy' hev A A' π π' i ub h hπ hπ' hi hu
  have hbal := GlobalTheory.T.cechKodairaSpencerMatrix_eq_zero_off_conj_blocks E H Dw l Xo c TF U n e v hv D Θ hΘ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hK := hcore K A A' i h g hA hgA hA' hgA' _ hL ψ hpol n (fun a => ub (e.symm a).1 (e.symm a).2)
    (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) (fun a => (hbl _ _).1) hC
    (fun b => hb (e.symm b)) (fun b => hbl _ _)
  refine ⟨A, inferInstance, A', inferInstance, π, π', i, h, ψ, ub, hb, hπ, hπ', hi, hpol, hu, fun σ k => hbl σ k,
    fun τ a => ?_⟩
  exact GlobalTheory.T.kodairaSpencerRow_of_kodairaSpencerValue_hodgeFil E H Dw K A A' i h hA ψ ub hb n e _ (s : K) (fun σ k => (hbl σ k).1)
    (fun a b hab => by simp only [Matrix.of_apply, hbal a b hab, map_zero]) hK τ.1 a (hrow τ a)

end GlobalTheory.LogPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerComparisonStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_comparison : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c), ∃ s : ℚ, s ≠ 0 ∧ KSCompare TF s := by
  first | exact @GlobalTheory.LogPole.exists_ksCompare | exact GlobalTheory.LogPole.exists_ksCompare | (intros; apply GlobalTheory.LogPole.exists_ksCompare <;> assumption)
end
