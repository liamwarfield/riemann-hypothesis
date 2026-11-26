module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigAgree
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportLabel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportLabel
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
namespace GlobalTheory.LabelTransport
set_option maxHeartbeats 2000000 in
theorem is_split_of_hk3_good_transport_label : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (sp : SplitPlace D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (sp.w.under (𝓞 D.host.F)) → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) sp.w d → ∃ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) ∧ (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧ {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite ∧ ∀ (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) (c : ℂ), (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d, X.fn hμ j f (g * γ) = c • X.fn hμ j f g) → NG.heckeD (P.M.loc i).J Ds ((P.M.loc i).real (hj ▸ f)) = c • (P.M.loc i).real (hj ▸ f) := by
  intro _ hL D P X hA _ _ _ i hμ j hj sp _ _ hJ d hd
  classical
  obtain ⟨e, f, ϖ, α, -, hef, -, -, -, -, -, -, -, hRs, hR1, hR2⟩ := GlobalTheory.SphLabelOps.sphOp_rep hd
  have hsupp := suppF_iff_trivOutside D sp hA.hF _ _ (hA.PV j) (hA.stdV j) e f hef
  have hpre : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d,
      (hA.PV j).ψ (Formalism.IndefR.principalLevelFrame.pre (hA.PV j) γ) = γ := by
    intro γ hγ
    have h := (hA.PV j).onto γ (hR1 γ hγ).1
    rw [Formalism.IndefR.principalLevelFrame.pre, dite_eq_left h]
    exact h.choose_spec
  obtain ⟨Ds, d1, d2, d3, d4⟩ := coset_transport (hA.PV j).ψ (GlobalTheory.InertSph.Gv D.host.E D.R.nV sp.v)
    (Umax D.host.E D.R.nV) (P.M.loc i).J {k | k ∈ Formalism.L2.Theta.KsphC (Formalism.IndefR.Links.Vc D j) ∅ ∧ Formalism.IndefR.Mult.SuppF (Formalism.IndefR.Links.Vc D j) f k} α (GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d)
    (fun x => and_congr ((hA.stdV j).2 x).symm (hsupp x)) (fun k hk => (hA.PV j).onto k hk.1.1)
    (fun x hx => (hJ x hx).1) (Formalism.IndefR.principalLevelFrame.pre (hA.PV j))
    (fun γ hγ => ⟨hpre γ hγ, (hsupp _).1 (by rw [hpre γ hγ]; exact hRs γ hγ)⟩) (fun γ hγ => (hR1 γ hγ).2) hR2
  refine ⟨Ds, d1, d2, d3, fun φ c hc => ?_⟩
  have key : ∀ (k : ℕ) (ek : j.1 + 1 = k) (k1 : 1 ≤ k) (k2 : k ≤ D.R.m) (g : GAf D.host.E D.R.nV),
      ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d,
        (P.M (D.nd.mu i) k k1 k2).real (ek ▸ φ) (g * Formalism.IndefR.principalLevelFrame.pre (hA.PV j) γ) =
        c • (P.M (D.nd.mu i) k k1 k2).real (ek ▸ φ) g := by
    intro k ek k1 k2 g
    subst ek
    have hr := hA.real (D.nd.mu i) hμ j φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hr g, ← map_smul, ← hc, map_sum]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hr, ← mul_assoc, map_mul, hpre γ hγ]
  have hty : (P.M.loc i).real (hj ▸ φ) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]
    exact ⟨_, rfl⟩
  funext g
  refine (d4 _ ((P.M.loc i).real (hj ▸ φ)) (fun x κ hκ hκ' => ?_) g).trans (key _ hj _ _ g)
  have h := congrFun (hty.2 ⟨κ, hκ⟩) x
  rw [(hJ κ hκ').2 hκ, Units.val_one, one_smul] at h
  exact h
end GlobalTheory.LabelTransport
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportLabelStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_split_of_hk3_good_at_split_place : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (sp : SplitPlace D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (sp.w.under (𝓞 D.host.F)) → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) sp.w d → ∃ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) ∧ (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧ {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite ∧ ∀ (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) (c : ℂ), (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d, X.fn hμ j f (g * γ) = c • X.fn hμ j f g) → NG.heckeD (P.M.loc i).J Ds ((P.M.loc i).real (hj ▸ f)) = c • (P.M.loc i).real (hj ▸ f) := by
  first | exact @_root_.GlobalTheory.LabelTransport.is_split_of_hk3_good_transport_label | exact _root_.GlobalTheory.LabelTransport.is_split_of_hk3_good_transport_label | (intros; apply _root_.GlobalTheory.LabelTransport.is_split_of_hk3_good_transport_label <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerExtra
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerExtra
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.LocEigAgree
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite → (∀ σ σ', IsLocS (P.H.av.S i Q) sp σ → IsLocS (P.H.av.S i Q') sp σ' → GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ') → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → ∀ F' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q'), F' ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F' ≠ 0 → ∀ c c' : ℂ, NG.heckeD (P.M.loc i).J Ds F = c • F → NG.heckeD (P.M.loc i).J Ds F' = c' • F' → c = c' := by
  intro _hAF hL D P i Q Q' sp hJ Ds hDs hbi hfin hcls F hF hFT hF0 F' hF' hF'T hF'0 c c' hc hc'
  classical
  have hK : ∀ f ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ,
      ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ f = f := by
    intro f hf κ hκ
    obtain ⟨h1, h2⟩ := hJ κ hκ.2
    have hJκ : κ ∈ (P.M.loc i).J := h1.2 hκ.1
    have e := hf.2 ⟨κ, hJκ⟩
    rw [h2 hJκ] at e
    simpa using e
  have hJU : ∀ x ∈ Ds, ∀ x' ∈ Ds, (x⁻¹ * x' ∈ (P.M.loc i).J ↔ x⁻¹ * x' ∈ Umax D.host.E D.R.nV) :=
    fun x hx x' hx' => (hJ _ (GlobalTheory.HeckeScalarAll.trivOutside_mul (GlobalTheory.HeckeScalarAll.trivOutside_inv (hDs x hx))
      (hDs x' hx'))).1
  have hfinU : ((fun x : GAf D.host.E D.R.nV => (x : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV)) '' Ds).Finite := by
    let φ : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J → GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV := fun c =>
      if hc : ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c then (hc.choose : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV) else ((1 : GAf D.host.E D.R.nV) : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV)
    refine (hfin.image φ).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Ds, (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) := ⟨x, hx, rfl⟩
    refine ⟨(x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J), ⟨x, hx, rfl⟩, ?_⟩
    simp only [φ, dif_pos hc]
    have h1 := hc.choose_spec.2
    rw [QuotientGroup.eq] at h1
    exact QuotientGroup.eq.2 ((hJU _ hc.choose_spec.1 _ hx).1 h1)
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_reps (Umax D.host.E D.R.nV) Ds hfinU
  have hH : ∀ f : GAf D.host.E D.R.nV → (P.M.loc i).wt.W, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ f = f) →
      NG.heckeD (P.M.loc i).J Ds f = ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ f := by
    intro f hf
    have hf' : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → NG.rt D.host.E D.R.nV κ f = f :=
      fun κ hκ ht => hf κ ⟨hκ, ht⟩
    have e1 : NG.heckeD (P.M.loc i).J Ds f = NG.heckeD (Umax D.host.E D.R.nV) Ds f := by
      funext g
      simp only [NG.heckeD]
      refine GlobalTheory.HeckeScalarAll.finsum_cosets_eq (P.M.loc i).J (Umax D.host.E D.R.nV) Ds (fun x => f (g * x)) hJU ?_
      intro x hx x' hx' hu
      have ht := GlobalTheory.HeckeScalarAll.trivOutside_mul (GlobalTheory.HeckeScalarAll.trivOutside_inv (hDs x hx)) (hDs x' hx')
      have h1 := congrFun (hf' _ hu ht) (g * x)
      simp only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at h1
      rw [mul_assoc, mul_inv_cancel_left] at h1
      exact h1.symm
    rw [e1]
    exact GlobalTheory.HeckeScalarSph.heckeD_eq_sum (v := sp.v) hDs hR1 hR2 hf'
  obtain ⟨cX, hcX⟩ := GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) sp Ds hDs hbi R hR1 hR2
  obtain ⟨cX', hcX'⟩ := GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible D.host.E D.R.nV _ _ _ (P.H.av.irr i Q') sp Ds hDs hbi R hR1 hR2
  have hcI := GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) _ R cX hcX
  have hcI' := GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart D.host.E D.R.nV _ _ _ (P.H.av.irr i Q') _ R cX' hcX'
  have hc1 : c = cX := by
    have e1 := hc
    rw [hH F (hK F hFT), hcI F hF (hK F hFT)] at e1
    exact smul_left_injective ℂ hF0 e1.symm
  have hc2 : c' = cX' := by
    have e1 := hc'
    rw [hH F' (hK F' hF'T), hcI' F' hF' (hK F' hF'T)] at e1
    exact smul_left_injective ℂ hF'0 e1.symm
  rw [hc1, hc2]
  let π : NG.AutRep D.host.E D.R.nV := ⟨(P.M.loc i).wt, P.H.av.S i Q, P.H.av.irr i Q⟩
  let π' : NG.AutRep D.host.E D.R.nV := ⟨(P.M.loc i).wt, P.H.av.S i Q', P.H.av.irr i Q'⟩
  obtain ⟨σ, hσ⟩ := GlobalTheory.LocCompSplit.exists_isLocS π sp
  obtain ⟨σ', hσ'⟩ := GlobalTheory.LocCompSplit.exists_isLocS π' sp
  have hcl := hcls σ σ' hσ hσ'
  obtain ⟨E⟩ : Nonempty (σ.ρ.Equiv σ'.ρ) := by
    have h2 : σ.cl = σ'.cl := eq_of_heq (Sigma.mk.inj hcl).2
    exact GlobalTheory.SmGL.IrrRep.cl_eq_iff.1 h2
  have hσ0 := hσ
  obtain ⟨ι, T0, hι, hιc, hT0i, hT0S, hT0e⟩ := hσ
  obtain ⟨ι', T0', hι', hιc', hT0i', hT0S', hT0e'⟩ := hσ'
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique _ sp ι ι' hι hι' hιc hιc'
  obtain ⟨a, ha0, hafix⟩ := GlobalTheory.T.splitLocalComponent_has_fixedVector_of_isotypic D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) sp σ hσ0 ι hι hιc F hF hF0 (hK F hFT)
  have hT0H : ∀ v, T0 (∑ γ ∈ R, σ.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) v) =
      ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ (T0 v) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hT0e γ (hDs γ (hR1 γ hγ)) v
  have hT0H' : ∀ v, T0' (∑ γ ∈ R, σ'.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) v) =
      ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ (T0' v) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hT0e' γ (hDs γ (hR1 γ hγ)) v
  have hT0fix : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ (T0 a) = T0 a := by
    intro κ hκ
    rw [← hT0e κ hκ.2 a, hafix κ hκ]
  have hHa : ∑ γ ∈ R, σ.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) a = cX • a := by
    apply hT0i
    rw [hT0H, map_smul]
    exact hcX (T0 a) (hT0S a) hT0fix
  have hE : ∀ g v, E.toLinearEquiv (σ.ρ g v) = σ'.ρ g (E.toLinearEquiv v) := fun g v =>
    LinearMap.congr_fun (E.isIntertwining' g) v
  have ha'0 : E.toLinearEquiv a ≠ 0 := fun h => ha0 (E.toLinearEquiv.injective (by rw [h, map_zero]))
  have hHa' : ∑ γ ∈ R, σ'.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) (E.toLinearEquiv a) =
      cX • E.toLinearEquiv a := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← hE, ← map_sum, hHa, map_smul]
  have hT0fix' : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v,
      NG.rt D.host.E D.R.nV κ (T0' (E.toLinearEquiv a)) = T0' (E.toLinearEquiv a) := by
    intro κ hκ
    rw [← hT0e' κ hκ.2, ← hE, hafix κ hκ]
  have key := hcX' (T0' (E.toLinearEquiv a)) (hT0S' _) hT0fix'
  rw [← hT0H', hHa', map_smul] at key
  have hne : T0' (E.toLinearEquiv a) ≠ 0 := fun h => ha'0 (hT0i' (by rw [h, map_zero]))
  exact smul_left_injective ℂ hne key
end GlobalTheory.LocEigAgree
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerExtraStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_support_at_split_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite → (∀ σ σ', IsLocS (P.H.av.S i Q) sp σ → IsLocS (P.H.av.S i Q') sp σ' → GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ') → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → ∀ F' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q'), F' ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F' ≠ 0 → ∀ c c' : ℂ, NG.heckeD (P.M.loc i).J Ds F = c • F → NG.heckeD (P.M.loc i).J Ds F' = c' • F' → c = c' := by
  first | exact @_root_.GlobalTheory.LocEigAgree.main_alt_alt | exact _root_.GlobalTheory.LocEigAgree.main_alt_alt | (intros; apply _root_.GlobalTheory.LocEigAgree.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigAgree
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigAgree
end GlobalTheory.EigAgree
theorem GlobalTheory.EigAgree.eig_agree_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) (Q Q' : D.naut.AV i), D.naut.ptV i Q = some x → D.naut.ptV i Q' = some x → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ f₁ f₂ : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f₁ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → (hj ▸ f₂ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q' → f₁ ≠ 0 → f₂ ≠ 0 → ∀ c₁ c₂ : ℂ, (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c₁ • X.fn hμ j f₁ g) → (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c₂ • X.fn hμ j f₂ g) → c₁ = c₂ := by
  intro hAF hL D P X hA h41 h7 htie i hμ j hj x Q Q' hQ hQ' Pp hG hS hPS hPQ d hd f₁ f₂ hf₁ hf₂ h0₁ h0₂ c₁ c₂ e1 e2
  have hsplit : IsSplitPl D.host Pp := GlobalTheory.OffBad.isSplitPl_of_isSplit D Pp hS
  have hloc : D.naut.locV i Q Pp = D.naut.locV i Q' Pp :=
    (((h41 i).2.1 Q Q' (by rw [hQ]; exact Option.some_ne_none x) (hQ.trans hQ'.symm)).2 Pp hPS hPQ).1 hsplit
  obtain ⟨sp, hspw, hJ⟩ := _root_.GlobalTheory.OffBad.offbad_alt hAF hL D P X hA h41 h7 htie i Pp hG hS
  subst hspw
  obtain ⟨Ds, hD1, hD2, hD3, hDt⟩ := _root_.GlobalTheory.T.is_split_of_hk3_good_at_split_place hAF hL D P X hA h41 h7 htie i hμ j hj sp hG hS hJ d hd
  have E1 := hDt f₁ c₁ e1
  have E2 := hDt f₂ c₂ e2
  have m1 : (P.M.loc i).real (hj ▸ f₁) ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have := P.H.av.typeV i Q ▸ hf₁
    exact this
  have m2 : (P.M.loc i).real (hj ▸ f₂) ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q') := by
    have := P.H.av.typeV i Q' ▸ hf₂
    exact this
  have t1 : (P.M.loc i).real (hj ▸ f₁) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ :=
    (P.M.loc i).real_range ▸ LinearMap.mem_range_self _ _
  have t2 : (P.M.loc i).real (hj ▸ f₂) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ :=
    (P.M.loc i).real_range ▸ LinearMap.mem_range_self _ _
  have n1 : (P.M.loc i).real (hj ▸ f₁) ≠ 0 := fun h =>
    GlobalTheory.EigAgree.cast_ne_zero hj f₁ h0₁ ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  have n2 : (P.M.loc i).real (hj ▸ f₂) ≠ 0 := fun h =>
    GlobalTheory.EigAgree.cast_ne_zero hj f₂ h0₂ ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  exact _root_.GlobalTheory.T.double_coset_support_at_split_alt hAF hL D P i Q Q' sp hJ Ds hD1 hD2 hD3
    (fun σ σ' h h' => _root_.UpperTheory.One.M.cls_eq_of_locV_eq' hL D P i Q Q' sp σ σ' h h' hloc) _ m1 t1 n1 _ m2 t2 n2 c₁ c₂ E1 E2
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigAgreeStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_equal_eigen_match_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) (Q Q' : D.naut.AV i), D.naut.ptV i Q = some x → D.naut.ptV i Q' = some x → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ f₁ f₂ : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f₁ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → (hj ▸ f₂ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q' → f₁ ≠ 0 → f₂ ≠ 0 → ∀ c₁ c₂ : ℂ, (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c₁ • X.fn hμ j f₁ g) → (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c₂ • X.fn hμ j f₂ g) → c₁ = c₂ := by
  first | exact @_root_.GlobalTheory.EigAgree.eig_agree_alt | exact _root_.GlobalTheory.EigAgree.eig_agree_alt | (intros; apply _root_.GlobalTheory.EigAgree.eig_agree_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OffBad
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodNotMemBadPl
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodNotMemBadPl
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GoodOffBad
theorem good_not_mem_badPl_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), Formalism.L2.NG.OverPl Pp v → v ∉ Formalism.L2.badPl D i := by
  intro hL D P X i _ w hG v hov
  have hlev := X.recR.base.lev
  have hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i) := by
    rcases D.what₂.muAt_or (D.nd.w i) with h | h
    · exact absurd h (D.nd.w_tw i)
    · rw [h, D.nd.mu_w i]
  have hxi := X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)
  have hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra hn
    rcases (hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr hPP)).2 hc
  rw [hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i] at hunr
  have hψ := X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i] at hψ
  set δ := X.R.C.delAt (D.nd.l i) with hδdef
  set ψ := X.Tp.psi (D.nd.w i) with hψdef
  set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef
  have hd : IsDelta (H := D.host) p δ := by
    rw [hδdef, hpdef, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x := fun _ => rfl
  have hnp : ¬ OverP D.host p w := by
    intro hw
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 : 15 ∣ D.nd.l i ^ a := by
      refine (hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_
      have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
      have h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1 := by
        have := congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha
        simpa [HChar.loc] using this
      have h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1 := by rw [h1, one_pow]
      rwa [mul_pow, h2, mul_one] at h3
    have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
    have h3 : 3 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
      (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    have h5 : 5 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq (by norm_num) hl).1
      ((show (5 : ℕ).Prime by norm_num).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    omega
  have hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hw
    have hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k) := D.nd.g_split k
    rcases (GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩
    · exact (hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl
    · exact (hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc
  have hnQ : w ∉ D.nd.Q i := by
    intro hQ
    rw [P.Q_eq i] at hQ
    refine (hψ.ram w).1 ?_ hQ
    intro x hx
    have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
    rw [hd.unr w hnp x hx, one_mul] at h1
    exact h1
  have hnp' : w ∉ placesOver D.host.E p := hnp
  rintro ⟨w', hover, hw'⟩
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE w w' (hover.trans hov.symm) with e | e
  · subst e
    rcases hw' with hQ | ⟨k, hg⟩ | hpd
    · exact hnQ hQ
    · exact hng k hg
    · exact hnp' hpd
  · subst e
    rcases hw' with hQ | ⟨k, hg⟩ | hpd
    · exact hnQ (P.H.hecke.Q_conj i _ w (isConjPl_conjPlE_left w) hQ)
    · exact hng k ((conjPlE_mem_placesOver w _).1 hg)
    · exact hnp' ((conjPlE_mem_placesOver w _).1 hpd)
end GlobalTheory.GoodOffBad
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodNotMemBadPlStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_below_good_not_mem_badPl : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), Formalism.L2.NG.OverPl Pp v → v ∉ Formalism.L2.badPl D i := by
  exact @_root_.GlobalTheory.GoodOffBad.good_not_mem_badPl_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OffBad
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SummandEig
theorem offBad_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), Formalism.L2.NG.OverPl Pp v → v ∉ Formalism.L2.badPl D i := _root_.GlobalTheory.T.place_below_good_not_mem_badPl
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj Q Pp hG hS d hd
  obtain ⟨s, α, hov, hα, hR1, hR2⟩ := frameReps D (Formalism.IndefR.Links.Vc D j) D.R.nV hAg.hF (hAg.PV j) (hAg.stdV j) Pp hS d hd
  obtain ⟨c, hc1⟩ := irrScalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s α hα _ _ _ hR1 hR2
  have hc := isoScalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s.v _ _ _ c hc1
  have hsB : s.v ∉ Formalism.L2.badPl D i := _root_.GlobalTheory.SummandEig.offBad_alt hL D P X i hμ Pp hG s.v hov
  refine ⟨c, fun f' hf' g => ?_⟩
  have hFI : (P.M.loc i).real (hj ▸ f') ∈ Formalism.L2.NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have h := hf'
    rw [P.H.av.typeV i Q] at h
    exact h
  have hFT : (P.M.loc i).real (hj ▸ f') ∈ Formalism.L2.NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]
    exact ⟨_, rfl⟩
  have hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      Formalism.L2.NG.rt D.host.E D.R.nV κ ((P.M.loc i).real (hj ▸ f')) = (P.M.loc i).real (hj ▸ f') := by
    intro κ hκ ht
    have ht' : TrivOutside (Formalism.L2.badPl D i)ᶜ κ := fun v hv => ht v fun h => hv (by
      rw [Set.mem_singleton_iff.1 h]
      exact hsB)
    obtain ⟨h1, h2⟩ := P.H.hecke.J_hyp i κ ht'
    have hJ : κ ∈ (P.M.loc i).J := h1.2 hκ
    have e := hFT.2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  have hkey := cast_sum P.M (D.nd.mu i) hj _ _ (by omega) (by omega) f' _ _ c (hc _ hFI hfix)
  have hreal : ∀ w, hAg.eW (D.nd.mu i) hμ j (X.fn hμ j f' ((hAg.PV j).ψ w)) =
      (P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f' (hAg.a j * w) := by
    intro w
    rw [hAg.real (D.nd.mu i) hμ j f' (hAg.a j * w), inv_mul_cancel_left]
  have hfin : ∀ w, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' ((hAg.PV j).ψ w * γ) =
      c • X.fn hμ j f' ((hAg.PV j).ψ w) := by
    intro w
    apply (hAg.eW (D.nd.mu i) hμ j).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul, hreal]
    have e1 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, hAg.eW (D.nd.mu i) hμ j (X.fn hμ j f' ((hAg.PV j).ψ w * γ)) =
        Formalism.L2.NG.rt D.host.E D.R.nV (Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ)
          ((P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f') (hAg.a j * w) := by
      intro γ hγ
      have e2 : (hAg.PV j).ψ w * γ = (hAg.PV j).ψ (w * Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ) := by
        rw [map_mul, Formalism.IndefR.principalLevelFrame.pre_spec (hAg.PV j) (rep_mem _ Pp d hγ)]
      rw [e2, hreal]
      show _ = (P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f' (hAg.a j * w * Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ)
      rw [mul_assoc]
    rw [Finset.sum_congr rfl e1, ← Finset.sum_apply, hkey]
    rfl
  obtain ⟨a₀, ha₀, k, hk, rfl⟩ := (GlobalTheory.T.adelicUnitary_real_mul_finite_decomposition D (Formalism.IndefR.Links.Vc D j)).1 g
  obtain ⟨w, rfl⟩ := (hAg.PV j).onto k hk
  obtain ⟨y, hy, -⟩ := X.existsUnique_vec hμ j f'
  have hw := hfin w
  rw [← hy] at hw ⊢
  have e1 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
      X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w * γ) =
        (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := fun γ hγ =>
    (congrArg (X.R.extV j (X.tupT (D.nd.mu i)) y) (mul_assoc _ _ _)).trans
      (extV_inf X j _ y ha₀ (mul_mem ((hAg.PV j).into w) (rep_mem _ Pp d hγ)))
  calc ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w * γ)
      = ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
          (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := Finset.sum_congr rfl e1
    _ = (X.R.cV j).ρ a₀⁻¹ (∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
          X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := (map_sum _ _ _).symm
    _ = (X.R.cV j).ρ a₀⁻¹ (c • X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w)) := congrArg _ hw
    _ = c • (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w)) := map_smul _ _ _
    _ = c • X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w) :=
      congrArg _ (extV_inf X j _ y ha₀ ((hAg.PV j).into w)).symm
end GlobalTheory.SummandEig
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OffBadStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplit_at_good_place_of_used0_av : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g :=
  _root_.GlobalTheory.SummandEig.main_alt_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodNotMemSQ
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodNotMemSQ
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GoodOffLoc
theorem good_not_mem_S_Q_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Pp ∉ D.nd.S i ∧ Pp ∉ D.nd.Q i := by
  intro _ hL D P X hA i _ w hG
  have hlev := X.recR.base.lev
  have hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i) := by
    rcases D.what₂.muAt_or (D.nd.w i) with h | h
    · exact absurd h (D.nd.w_tw i)
    · rw [h, D.nd.mu_w i]
  have hxi := X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)
  have hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra hn
    rcases (hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr hPP)).2 hc
  rw [hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i] at hunr
  have hψ := X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i] at hψ
  set δ := X.R.C.delAt (D.nd.l i) with hδdef
  set ψ := X.Tp.psi (D.nd.w i) with hψdef
  set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef
  have hd : IsDelta (H := D.host) p δ := by
    rw [hδdef, hpdef, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x := fun _ => rfl
  have hnp : ¬ OverP D.host p w := by
    intro hw
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 : 15 ∣ D.nd.l i ^ a := by
      refine (hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_
      have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
      have h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1 :=
        (MonoidHom.pow_apply ..).symm.trans
          (congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha)
      have h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1 := by rw [h1, one_pow]
      rwa [mul_pow, h2, mul_one] at h3
    have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
    have h3 : 3 = D.nd.l i :=
      Nat.prime_eq_prime_of_dvd_pow Nat.prime_three hl (dvd_trans (by norm_num) h15)
    have h5 : 5 = D.nd.l i :=
      Nat.prime_eq_prime_of_dvd_pow Nat.prime_five hl (dvd_trans (by norm_num) h15)
    omega
  have hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hw
    have hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k) := D.nd.g_split k
    rcases (GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩
    · exact (hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl
    · exact (hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc
  refine ⟨fun hS => ?_, fun hQ => ?_⟩
  · rcases ((D.nd.S_def i w).1 hS).1 with h | h | h
    · exact hng 0 h
    · exact hng 1 h
    · exact hnp h
  · rw [P.Q_eq i] at hQ
    refine (hψ.ram w).1 ?_ hQ
    intro x hx
    have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
    rw [hd.unr w hnp x hx, one_mul] at h1
    exact h1
end GlobalTheory.GoodOffLoc
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodNotMemSQStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_place_not_mem_S_and_Q_of_used0 : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Pp ∉ D.nd.S i ∧ Pp ∉ D.nd.Q i := by
  first | exact @_root_.GlobalTheory.GoodOffLoc.good_not_mem_S_Q_alt | exact _root_.GlobalTheory.GoodOffLoc.good_not_mem_S_Q_alt | (intros; apply _root_.GlobalTheory.GoodOffLoc.good_not_mem_S_Q_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandEigen
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigSplit
theorem placesOff_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Pp ∉ D.nd.S i ∧ Pp ∉ D.nd.Q i := _root_.GlobalTheory.T.good_place_not_mem_S_and_Q_of_used0
theorem is_split_of_hk3_good_summand_eigen : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := _root_.GlobalTheory.T.isSplit_at_good_place_of_used0_av
theorem eigenAgree_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) (Q Q' : D.naut.AV i), D.naut.ptV i Q = some x → D.naut.ptV i Q' = some x → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ f₁ f₂ : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f₁ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → (hj ▸ f₂ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q' → f₁ ≠ 0 → f₂ ≠ 0 → ∀ c₁ c₂ : ℂ, (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c₁ • X.fn hμ j f₁ g) → (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c₂ • X.fn hμ j f₂ g) → c₁ = c₂ := _root_.GlobalTheory.T.points_equal_eigen_match_alt
theorem is_split_of_hk3_good_uniform_in_x : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ Q : D.naut.AV i, D.naut.ptV i Q = some x → ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj x Pp hG hS hPS hPQ d hd
  by_cases hex : ∃ (Q0 : D.naut.AV i) (f0 : D.what₂.Mt (D.nd.mu i) (j.1 + 1)), D.naut.ptV i Q0 = some x ∧
      (hj ▸ f0 : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q0 ∧ f0 ≠ 0
  · obtain ⟨Q0, f0, hQ0, hf0, hf00⟩ := hex
    obtain ⟨c0, hc0⟩ := _root_.GlobalTheory.EigSplit.is_split_of_hk3_good_summand_eigen hAF hL D P X hAg h41 h7 hTie i hμ j hj Q0 Pp hG hS d hd
    refine ⟨c0, fun Q hQ f' hf' => ?_⟩
    obtain ⟨cQ, hcQ⟩ := _root_.GlobalTheory.EigSplit.is_split_of_hk3_good_summand_eigen hAF hL D P X hAg h41 h7 hTie i hμ j hj Q Pp hG hS d hd
    by_cases hf'0 : f' = 0
    · subst hf'0; exact eig_zero X hμ j Pp d c0
    · have := _root_.GlobalTheory.EigSplit.eigenAgree_alt hAF hL D P X hAg h41 h7 hTie i hμ j hj x Q0 Q hQ0 hQ Pp hG hS hPS hPQ d hd f0 f' hf0 hf'
        hf00 hf'0 c0 cQ (hc0 f0 hf0) (hcQ f' hf')
      rw [this]; exact hcQ f' hf'
  · refine ⟨0, fun Q hQ f' hf' => ?_⟩
    have hf'0 : f' = 0 := by
      by_contra hne; exact hex ⟨Q, f', hQ, hf', hne⟩
    subst hf'0; exact eig_zero X hμ j Pp d 0
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, h Pp (Finsupp.single d 1) y = c • y := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj x hx f hf y hy hy0 h hh Pp hG hS d hd
  have hA := _root_.GlobalTheory.EigSplit.placesOff_alt hAF hL D P X hAg i hμ Pp hG
  have hu := _root_.GlobalTheory.EigSplit.is_split_of_hk3_good_uniform_in_x hAF hL D P X hAg h41 h7 hTie i hμ j hj x Pp hG hS hA.1 hA.2 d hd
  have hfE := alongEig X i hμ j hj x Pp d hu.choose hu.choose_spec _ hf f rfl
  refine ⟨hu.choose, transport X j _ h hh Pp hG d y hu.choose fun g => ?_⟩
  rw [hy]
  exact hfE g
end GlobalTheory.EigSplit
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandEigenStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eigen_compatibility_first_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, h Pp (Finsupp.single d 1) y = c • y := by
  first | exact @_root_.GlobalTheory.EigSplit.main_alt_alt | exact _root_.GlobalTheory.EigSplit.main_alt_alt | (intros; apply _root_.GlobalTheory.EigSplit.main_alt_alt <;> assumption)
end
end
