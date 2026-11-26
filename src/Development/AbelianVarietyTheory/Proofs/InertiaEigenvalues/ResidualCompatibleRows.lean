module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfIota
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvariantFormBoundedCongruence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftFormsAdelicDecoratedLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqUnitMulCentralTranslateLiftVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationExtendsByNewTuplesKeepingLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualCompatibleRows
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairsOfTransport
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.LiftPoint

noncomputable section

namespace GlobalTheory.ResLoc

theorem exists_point (D : D7) (M : MtFam D) (HT : HeckeTied D M) (AV : AVTied D M) (NL : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw NL.B)
    (i : D.nd.Loc) (P : D.naut.AV i) : ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i),
      ∃ (hμ' : D.nd.mu i = D.nd.mu i') (hj' : D.nd.j i = D.nd.j i') (P' : D.naut.AV i') (x' : D.nd.X i'),
        (D.naut.typeV i P).map (GlobalTheory.EtaJoin.TypeSum.eqvMt hμ' hj').toLinearMap = D.naut.typeV i' P' ∧
        D.naut.ptV i' P' = some x' := by
  classical
  have h : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hj1 := (D.nd.j_range i).1
  have hj2 := (D.nd.j_range i).2
  have hw : LocPl D (D.nd.j i) (D.nd.w i) := locPl_of_mem D h
  have hμ : D.nd.mu i = D.what₂.muTw (D.nd.w i) := D.nd.mu_w i
  obtain ⟨y0, hy0, hy0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i P)
  have hr0 : (M.loc i).real y0 ≠ 0 := fun h0 => hy0ne ((M.loc i).real_inj (h0.trans (map_zero _).symm))

  have hinjO : Function.Injective (iotaO D.nd D.naut i) := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))
  have hiotaC : ∀ z, iotaO D.nd D.naut i z = NL.iotaC _ _ (NL.phO _ _ i h z) := NL.iotaC_coh _ _ i h
  have hinjC : Function.Injective (NL.iotaC (D.nd.j i) (D.nd.w i)) := by
    intro a b hab
    have e2 : (NL.phO _ _ i h).symm a = (NL.phO _ _ i h).symm b := hinjO (by
      rw [hiotaC, hiotaC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; exact hab)
    simpa using congrArg (NL.phO _ _ i h) e2
  let φ : FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = NL.iotaC _ _ z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (NL.phK _ _ i h).toRingHom = (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, NL.phK_alg, hφalg]
    rw [← hiotaC]
    rfl
  have hφ : ∀ y, φ (NL.B.ec _ _ y) = D.what₂.embLL y := by
    intro y
    rw [← NL.phK_emb _ _ i h y, ← D.naut.iota_LL i y]
    exact congrArg (fun f : FractionRing (D.nd.O i) →+* ℂ => f (D.nd.embK i y)) hφK

  have HS := GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places D M HT AV i
  have key : ∀ v k, GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k →
      ∃ κ : NL.B.Oc (D.nd.j i) (D.nd.w i), ∀ (s : SplitPlace D.host.E)
        (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
        ∀ y ∈ D.naut.typeV i P, NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = φ (algebraMap _ _ κ) • (M.loc i).real y := by
    intro v k hvk
    obtain ⟨hv, hk1, hk2⟩ := (genAt_iff NL h v k).2 hvk
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
    obtain ⟨c, hcP⟩ := HS P v k s ϖ hv hc hu hk1 hk2
    obtain ⟨tC, htC1, htC2⟩ := tC_exists D M NL.B hstd (D.nd.j i) (D.nd.w i) (D.nd.mu i) hμ hj1 hj2 hw φ hφ v k hvk
    have ht0 : tC y0 = c • y0 := by
      apply (M.loc i).real_inj
      have e0 := htC2 s ϖ hc hu (tN_lin D M HT NL h v k s ϖ hvk hc hu) y0
      change NG.tN (M.loc i).J s ϖ k ((M.loc i).real y0) = (M.loc i).real (tC y0) at e0
      rw [← e0, hcP y0 hy0, map_smul]
    obtain ⟨κ, hκ⟩ := htC1 c y0 hy0ne ht0
    refine ⟨κ, fun s' ϖ' hc' hu' y hy => ?_⟩
    obtain ⟨c', hcP'⟩ := HS P v k s' ϖ' hv hc' hu' hk1 hk2
    have e1 := htC2 s' ϖ' hc' hu' (tN_lin D M HT NL h v k s' ϖ' hvk hc' hu') y0
    change NG.tN (M.loc i).J s' ϖ' k ((M.loc i).real y0) = (M.loc i).real (tC y0) at e1
    rw [hcP' y0 hy0, ht0, map_smul] at e1
    have hcc : c' = c := smul_left_injective ℂ hr0 e1
    rw [hcP' y hy, hcc, hκ]
  let κF : PlE D.host → ℕ → NL.B.Oc (D.nd.j i) (D.nd.w i) := fun v k =>
    if hvk : GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k then
      Classical.choose (key v k hvk) else 0
  have hκF : ∀ v k (hvk : GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
        ∀ y ∈ D.naut.typeV i P, NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) =
          φ (algebraMap _ _ (κF v k)) • (M.loc i).real y := by
    intro v k hvk
    simp only [κF, dif_pos hvk]
    exact Classical.choose_spec (key v k hvk)

  obtain ⟨e, hene, he⟩ := GlobalTheory.PtLocalEig.eig_descends D M NL.B (D.nd.j i) (D.nd.w i) (D.nd.mu i) hj1 hj2 hμ φ hφ
    (fun v k => algebraMap _ _ (κF v k)) y0 hy0ne (by
      intro v k hvk
      obtain ⟨hv, -, -⟩ := (genAt_iff NL h v k).2 hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
      exact ⟨s, ϖ, hc, hu, tN_lin D M HT NL h v k s ϖ hvk hc hu, hκF v k hvk s ϖ hc hu y0 hy0⟩)
  have hinjK : Function.Injective (algebraMap (NL.B.Oc (D.nd.j i) (D.nd.w i))
      (FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)))) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := GlobalTheory.PtLocalEig.pt_of_eigvec (heckeGens NL.B (D.nd.j i) (D.nd.w i)) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨κF v k, he v k hvk⟩)
  have hψv : ∀ v k (hvk : GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = κF v k := by
    intro v k hvk
    apply hinjK
    have h1 := hψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have h2 := he v k hvk
    change NL.B.hK _ _ v k e = _ at h1
    rw [h2] at h1
    exact (smul_left_injective _ hene h1).symm
  have hW : NCov.W (heckeAlg NL.B _ _) (NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3

  obtain ⟨i', hi', hmx⟩ := NL.mx_all (D.nd.j i) (D.nd.w i) hj1 hj2 (D.nd.w_tw i) (NCov.cls ψ)
    (NCov.cls_isMaximal ψ)
  obtain ⟨e1, e2⟩ := (D.nd.locs_mem _ _ i').1 hi'
  have hμ' : D.nd.mu i = D.nd.mu i' := by rw [D.nd.mu_w i, D.nd.mu_w i', e2]
  have hj' : D.nd.j i = D.nd.j i' := e1.symm
  let x' : D.nd.X i' := (NL.ptX _ _ i' hi').symm ⟨ψ, hmx.symm, hW⟩
  obtain ⟨P', hP'⟩ := GlobalTheory.EtaJoin.TypeSum.typeV_of_transport AV i' hμ' hj' hj1 hj2 (AV.S i P) (AV.irr i P)
    (by
      change (NG.isoTyp (M.loc i).wt.ρ (AV.S i P)).comap (M.loc i).real ≠ ⊥
      rw [← AV.typeV i P]; exact D.naut.typeV_ne i P)
  change Submodule.map _ ((NG.isoTyp (M.loc i).wt.ρ (AV.S i P)).comap (M.loc i).real) = _ at hP'
  rw [← AV.typeV i P] at hP'
  refine ⟨i', hi', hμ', hj', P', x', hP', ?_⟩
  refine ptV_of_transport AV i' P' x' hμ' hj' hj1 hj2 _ hP' ?_
  intro v k s ϖ hv' hc hu hk1 hk2 y hy
  have hvk := (genAt_iff NL hi' v k).1 ⟨hv', hk1, hk2⟩
  change NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = _ • (M.loc i).real y
  rw [hκF v k hvk s ϖ hc hu y hy]
  congr 1
  rw [NL.iotaC_coh _ _ i' hi', NL.ptX_hT _ _ i' hi' x' v k hvk]
  show φ (algebraMap _ _ (κF v k)) = NL.iotaC _ _ (((NL.ptX _ _ i' hi') ((NL.ptX _ _ i' hi').symm ⟨ψ, hmx.symm, hW⟩)).1 _)
  rw [Equiv.apply_symm_apply, hφalg]
  show NL.iotaC _ _ (κF v k) = NL.iotaC _ _ (ψ ⟨NL.B.hK _ _ v k, _⟩)
  rw [hψv v k hvk]

theorem pairs_of_transport {D : D7} (i' : D.nd.Loc) (P' : D.naut.AV i') {μ : D.what₂.Tup} {j : ℕ} (hμ : μ = D.nd.mu i')
    (hj : j = D.nd.j i') (V : Submodule ℂ (D.what₂.Mt μ j))
    (hV : V.map (GlobalTheory.EtaJoin.TypeSum.eqvMt hμ hj).toLinearMap = D.naut.typeV i' P') {σ : D.what₂.FT}
    (h : ∃ f ∈ D.what₂.isot j σ, ∃ F ∈ V, inner ℂ F (D.what₂.thetaT μ j f) ≠ 0) : GlobalTheory.ThetaExh.Pairs D.nd D.naut i' σ P' := by
  subst hμ; subst hj
  rw [GlobalTheory.EtaJoin.TypeSum.map_eqvMt_self] at hV
  subst hV
  exact h

theorem exists_pair_point (D : D7) (M : MtFam D) (HT : HeckeTied D M) (AV : AVTied D M) (NL : NormalizedLocalCompatibility D M)
    (hstd : HeckeStdTw NL.B) (i : D.nd.Loc) (σ : D.what₂.FT)
    (h : ∃ f ∈ D.what₂.isot (D.nd.j i) σ, D.what₂.thetaT (D.nd.mu i) (D.nd.j i) f ≠ 0) :
    ∃ (i' : D.nd.Loc) (P' : D.naut.AV i') (x' : D.nd.X i'), D.nd.j i' = D.nd.j i ∧ D.nd.w i' = D.nd.w i ∧
      GlobalTheory.ThetaExh.Pairs D.nd D.naut i' σ P' ∧ D.naut.ptV i' P' = some x' := by
  obtain ⟨f, hf, hθ⟩ := h
  obtain ⟨P, F, hF, hFf⟩ := GlobalTheory.Proof.HoweThetaLiftComponents.exists_inner_ne_zero (D.naut.typeV i) (D.naut.typeV_top i) _ hθ
  obtain ⟨i', hi', hμ, hj, P', x', hP', hx'⟩ := exists_point D M HT AV NL hstd i P
  obtain ⟨e1, e2⟩ := (D.nd.locs_mem _ _ i').1 hi'
  exact ⟨i', P', x', e1, e2, pairs_of_transport i' P' hμ hj _ hP' ⟨f, hf, F, hF, hFf⟩, hx'⟩

theorem exists_thetaT_ne {D : D7} (hd : DV.LamDef D) {μ : D.what₂.Tup} {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {σ : D.what₂.FT}
    (hσ : D.what₂.isot j σ ≠ ⊥) (hp : 0 < D.what₂.lamP μ j σ) : ∃ f ∈ D.what₂.isot j σ, D.what₂.thetaT μ j f ≠ 0 := by
  by_contra hn
  push Not at hn
  rw [hd μ j h1 h2 σ hσ, DV.lamTr_of_scalar D μ j σ 0 hσ fun x hx => by rw [hn x hx]; simp] at hp
  exact lt_irrefl _ hp

end GlobalTheory.ResLoc

end
end

noncomputable section

namespace GlobalTheory.ResLoc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 _root_.Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)

theorem continuous_qCast {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (ι : Qbar p ≃+* ℂ) {Y : Type} [TopologicalSpace Y]
    {f : Y → Qbar q} (hf : Continuous f) : Continuous fun y => ι.symm (qCast h ι (f y)) := by
  subst h
  simpa [qCast] using hf

def plL {D : D7} (L : LocAll (lay0 D)) (Pl : PlSide D) : PlSide (withLoc L) := ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩




end GlobalTheory.ResLoc

namespace GlobalTheory.ResLoc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG


end GlobalTheory.ResLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompAtEqOneOfTameAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain

noncomputable section
namespace GlobalTheory.AVGood

theorem compAt_eq_one_of_tameAt {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (χ : HChar L)
    (hχ : χ.TameAt s.w) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (hξ : NG.IsCompAt χ s ξ)
    (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ)
    (hu : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) < 1) : ξ u = 1 := by
  obtain ⟨ξ', hξ', hv⟩ := GlobalTheory.T.tame_heckeCharacter_split_place_local_component L s χ hχ
  have e : ξ = ξ' := GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique L χ s ξ ξ' hξ hξ'
  have hu1 : Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 := by
    have h := Valuation.map_one_add_of_lt (Valued.v : Valuation (s.v.adicCompletion (maximalRealSubfield L)) _) hu
    rwa [add_sub_cancel] at h
  rw [e, hv u 1 1 (by simp) hu1 (by simpa using hu), map_one]

theorem tameAtG_of_tameAt (D : D7) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (h : ∀ (i : D.nd.Loc) (j : Fin D.R.m) (k : Fin 2) (v : D.nd.PlG k), (tup (D.nd.mu i) j).TameAt (D.naut.plGw k v)) :
    TameAtG D tup := by
  intro i j k v s ξ hw hξ u hu
  exact compAt_eq_one_of_tameAt s _ (hw ▸ h i j k v) ξ hξ u hu

theorem tameAtG_of_tupTied (D : D7) (cf : CharFrame D) {C : NChoice D} (tp : TupTied D cf C) : TameAtG D tp.tup :=
  tameAtG_of_tameAt D tp.tup fun i j _ _ x hx hx' => by
    change (cf.mu0 j).loc _ x * (tp.xi (D.nd.mu i)).loc _ x = 1
    rw [(cf.isMu0 j).tame _ x hx hx', tp.xi_tame _ _ x hx hx', one_mul]
end GlobalTheory.AVGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftEqMultiplePrincipalLevelClassSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftEqMultiplePrincipalLevelClassSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftClassSumPrinc

theorem isReps_mul_central {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) {I : Type} (y : I → G)
    {z : G} (hz : z ∈ Subgroup.center G) (hy : Bridge.IsReps ι J y) : Bridge.IsReps ι J fun i => y i * z := by
  have hc : ∀ a : G, a * z = z * a := fun a => ((Subgroup.mem_center_iff.1 hz) a)
  intro h
  obtain ⟨i, ⟨γ, k, hk⟩, hu⟩ := hy (h * z⁻¹)
  refine ⟨i, ⟨γ, k, ?_⟩, fun i' ⟨γ', k', hk'⟩ => hu i' ⟨γ', k', ?_⟩⟩
  · calc h = h * z⁻¹ * z := by group
      _ = ι γ * y i * k * z := by rw [hk]
      _ = ι γ * y i * (z * k) := by rw [mul_assoc _ (k : G) z, hc (k : G)]
      _ = ι γ * (y i * z) * k := by simp only [mul_assoc]
  · have hc' : ∀ a : G, a * z⁻¹ = z⁻¹ * a := fun a => ((Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hz)) a)
    rw [hk', mul_assoc _ (k' : G) z⁻¹, hc' (k' : G)]
    group

theorem stab_mul_central {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) (y : G) {z : G}
    (hz : z ∈ Subgroup.center G) : Bridge.stab ι J (y * z) = Bridge.stab ι J y := by
  have hc : ∀ a : G, a * z = z * a := fun a => ((Subgroup.mem_center_iff.1 hz) a)
  ext γ
  rw [Bridge.mem_stab, Bridge.mem_stab]
  have e : (y * z)⁻¹ * ι γ * (y * z) = y⁻¹ * ι γ * y :=
    calc (y * z)⁻¹ * ι γ * (y * z) = z⁻¹ * ((y⁻¹ * ι γ * y) * z) := by group
      _ = z⁻¹ * (z * (y⁻¹ * ι γ * y)) := by rw [hc (y⁻¹ * ι γ * y)]
      _ = y⁻¹ * ι γ * y := by group
  rw [e]

theorem map_mem_center {G H : Type} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) {z : G}
    (hz : z ∈ Subgroup.center G) : f z ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff]
  intro a
  obtain ⟨a', rfl⟩ := hf a
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) a']

theorem twist_good_of {D : D7} (ψ : Twist D Circle) (hQ : ψ.Q = ∅) (hc : ψ.chi = 1) : ψ.Good := by
  obtain ⟨Q, chi, res⟩ := ψ
  dsimp only at hQ hc
  subst hQ hc
  exact ⟨by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ, fun _ => rfl, fun _ => rfl, splitSet_empty, fun _ _ _ _ _ => rfl,
    fun _ h => absurd h (Finset.notMem_empty _)⟩

theorem lev_eq_of {F E LL : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [CommRing LL] {n : ℕ} (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F))
    (L L' : LevDat E LL n) (hr : L.r = L'.r) (ht : L.t = L'.t) (hP : L.Pg = L'.Pg) (hQ : L.Q = L'.Q)
    (hH : L.P.H = ⊥) (hH' : L'.P.H = ⊥) : lev hc J β L = lev hc J β L' := by
  obtain ⟨r, hr0, t, s, Pg, Q, P, cg, xq⟩ := L
  obtain ⟨r', hr0', t', s', Pg', Q', P', cg', xq'⟩ := L'
  dsimp only at hr ht hP hQ hH hH'
  subst hr ht hP hQ
  ext x
  rw [mem_lev, mem_lev, hH, hH', Subgroup.mem_bot, Subgroup.mem_bot]
  rfl


open GlobalTheory.ConjTwist in
theorem ser_transl {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    {χS χT : (AE D)ˣ →* Circle} (hom : IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT (R.ωP i t)) (hθ : IsInfFam R.θ)
    (hv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)) {k : GA D (Vc D i)} (hk : k ∈ GfC (Vc D i)) (c : ℂ)
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)) :
    ser R i t (c • R.ωP i t (k, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * k) w g := by
  simp only [ser, thetaKO]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ (R.ωP i t) hom R.θ hθ k hk 1
    (one_mem _) _ _ _ _ (R.vP i t) _ hv, map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one,
    smul_eq_mul]


open GlobalTheory.ConjTwist GlobalTheory.FlatVecSum in
theorem sum_eq_classSum {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (j : Fin D.R.m) (t : T0)
    {B : Base (Vc D j) (Wc D j)} (hB : BaseOf R j B) (ψ : Twist D Circle) {c0 : ℂ} (hc0 : c0 ≠ 0) {z' : GA D (Vc D j)}
    (hz' : z' ∈ GfC (Vc D j)) (hzc : Formalism.IndefR.FWT.fin (Vc D j) z' ∈ Subgroup.center (Bridge.Gf (Vc D j)))
    (hflat : c0 • R.ωP j t (z', 1) (R.vP j t) = (princ B).vecFlat ψ)
    {χS χT : (AE D)ˣ →* Circle} (hom : IsWeilDatumO R.ψ (Vc D j) (Wc D j) χS χT (R.ωP j t)) (hθ : IsInfFam R.θ)
    (hv : IsThetaFunO R.ψ (Vc D j) (Wc D j) (R.vP j t)) {m : ℕ} (h₀ : Fin m → GA D (Vc D j))
    (J : Subgroup (Bridge.Gf (Vc D j))) (hrel : ((princ B).levJ ψ).relIndex J = 1) (Ef : Bridge.Gf (Vc D j) → (R.cV j).W)
    (u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ) (g : GA D (Wc D j)) :
    ∑ k, ((((princ B).levJ ψ).relIndex J : ℕ) : ℂ)⁻¹ *
        ((Nat.card (Bridge.stab (Bridge.ratF (Vc D j)) ((princ B).levJ ψ) (Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z'))) : ℕ) : ℂ)⁻¹ *
        thetaKO (R.ωP j t) (h₀ k * z') g
          ((pureTensorO R.ψ R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (R.MW j (sg0 D A))) (R.BV j) (onb (R.MW j (sg0 D A)))
            (R.vP j t) ∘ₗ R.ioP j (PiTensorProduct.tprod ℂ u)) (Ef (Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')))) =
      (c0⁻¹ • (princ B).classSum (R.ωP j t) ψ h₀
        (fun h => R.ioP j (PiTensorProduct.tprod ℂ u) (Ef (h * Formalism.IndefR.FWT.fin (Vc D j) z')))) g := by
  rw [Pi.smul_apply, Base.classSum_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfin1 : Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z') = finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z' :=
    map_mul _ _ _
  rw [Pi.smul_apply, smul_eq_mul, hrel, Nat.cast_one, inv_one, one_mul, hfin1, stab_mul_central _ _ _ hzc,
    show (princ B).F = B.F from rfl, hB.series_eq_ser, ← hflat, ser_transl R j t hom hθ hv hz', mul_left_comm _ c0,
    ← mul_assoc c0⁻¹ c0, inv_mul_cancel₀ hc0, one_mul]
  rfl


open Classical GlobalTheory.ConjTwist GlobalTheory.FlatVecSum in
theorem thF_eq_classSum_princ : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ (y : (X.R.HV j t).H) (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
    ∃ (m : ℕ) (h₀ : Fin m → GA D (Vc D j)) (c : ℂ) (z : Bridge.Gf (Vc D j)),
      IsClassSystem (Vc D j) ((GlobalTheory.FlatVecSum.princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1)) h₀ ∧ z ∈ Subgroup.center (Bridge.Gf (Vc D j)) ∧
      X.R.thF j t y (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) =
        c • (GlobalTheory.FlatVecSum.princ (Y.Z.ρ.B i j b)).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) h₀
          (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) := by
  intro D X E Y i j b t hxi hQ y u
  have hB : BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) := GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have he : (Y.Z.ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  have hone : (Y.Z.ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).Good := twist_good_of _ he hone
  have hadm : (Y.Z.ρ.B i j b).admitted (Y.Z.ρ.tw i b 0 ∅ 1).Q := by rw [he]; exact Base.admissible_empty_of_good hG
  have htup : IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Y.Z.ρ.tw i b 0 ∅ 1) t :=
    ⟨by rw [hxi, hone, mul_one], by rw [hQ, he, Finset.union_empty]⟩
  obtain ⟨⟨f, hf⟩, -⟩ := GlobalTheory.FlatVecExist.flatVec_existsUnique D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC X.guard j t
  obtain ⟨z', c0, hz', hc0, hfz⟩ :=
    GlobalTheory.T.flatVector_eq_unit_mul_centralTranslate_liftVector D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC X.guard j t (X.std j) f hf
  have hflat : f = (princ (Y.Z.ρ.B i j b)).vecFlat (Y.Z.ρ.tw i b 0 ∅ 1) :=
    eq_vecFlat_princ hB htup hC.lev hG hψ hadm hf

  have hβ : (princ (Y.Z.ρ.B i j b)).F.βS = X.R.βV j := hB.βS
  have hrW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have hrV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hJ : (princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1) =
      (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J := by
    unfold Base.levJ
    rw [hβ, GlobalTheory.LiftClassSumPrinc.lev_eq_of _ _ _ ((princ (Y.Z.ρ.B i j b)).levS (Y.Z.ρ.tw i b 0 ∅ 1))
      (Formalism.IndefR.Lev.flag1L (X.R.datVt j t)) (by show (Wc D j).rank = D.R.r; exact hrW)
      (by show (Vc D j).rank - (Wc D j).rank = D.R.t; omega) (by show (Y.Z.ρ.B i j b).G.Pg = X.R.Pg; exact hB.Pg)
      (by show (Y.Z.ρ.B i j b).de.Q ∪ (Y.Z.ρ.tw i b 0 ∅ 1).Q = X.R.Q t; rw [he, Finset.union_empty, hQ]) rfl rfl]
    rfl
  have hrel : ((princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1)).relIndex
      (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J = 1 := Subgroup.relIndex_eq_one.2 hJ.ge
  refine (exists_isClassSystem (princ (Y.Z.ρ.B i j b)) (princ_good hG).frame (Y.Z.ρ.tw i b 0 ∅ 1)).elim fun m hm =>
    hm.elim fun h₀ hcs => ?_
  have hzc : Formalism.IndefR.FWT.fin (Vc D j) z' ∈ Subgroup.center (Bridge.Gf (Vc D j)) :=
    GlobalTheory.LiftClassSumPrinc.map_mem_center (finHom (Vc D j)).rangeRestrict (MonoidHom.rangeRestrict_surjective _) hz'.1
  refine ⟨m, h₀, c0⁻¹, Formalism.IndefR.FWT.fin (Vc D j) z', hcs, hzc, ?_⟩
  have hfin1 : ∀ k, Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z') = finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z' :=
    fun k => map_mul _ _ _
  have hy : Bridge.IsReps (Bridge.ratF (Vc D j)) ((princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1))
      (fun k => Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')) := by
    rw [show (fun k => Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')) = fun k => finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z'
      from funext hfin1]
    exact GlobalTheory.LiftClassSumPrinc.isReps_mul_central _ _ _ hzc hcs.reps
  have hh : ∀ k, h₀ k * z' ∈ GfC (Vc D j) := fun k => mul_mem (hcs.fin k) hz'.2.1
  have hθ : IsInfFam X.R.θ := hC.models.inf
  have hvθ : IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (X.R.vP j t) :=
    GlobalTheory.AdTh.MinorWeight.pure_one _ (X.R.vP j t) ▸ hC.thP.pt_theta j t 1
  funext g
  refine (hC.thP.thF j t).elim fun thP hPF => ?_
  have hx : (X.R.HV j t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
      (levEnv _ (X.R.βV j) (X.R.datVt j t)).J (levEnv _ (X.R.βV j) (X.R.datVt j t)).χ :=
    (hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)
  have hfin : ∀ k ∈ GfC (Vc D j), ∀ hk : Formalism.IndefR.FWT.fin (Vc D j) k ∈ Formalism.IndefR.FWT.levJ X.R.toRealDat j t, ∀ P,
      X.R.ωP j t (k, 1) (X.R.ptP j t P) =
      (((levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨Formalism.IndefR.FWT.fin (Vc D j) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • X.R.ptP j t P :=
    fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite X.R.ψ X.R.θ (Vc D j) (Wc D j) _ _ (X.R.ωP j t) hC.models.inf
      (hC.thP.ωP j t) _ _ _ _ _ (hC.thP.pt_theta j t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC j t k (X.std j) hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hC.thP.ωP j t) (D.sp.V_sig _) (hC.models.vpos j) (X.R.cV j) (hC.models.cV j)
    (X.R.βV j) (X.R.datVt j t) (fun _ => Iff.rfl) hx
    (pureTensorO X.R.ψ X.R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (X.R.MW j (sg0 D X.A3.A))) (X.R.BV j)
      (onb (X.R.MW j (sg0 D X.A3.A))) (X.R.vP j t) ∘ₗ X.R.ioP j (PiTensorProduct.tprod ℂ u)) (fun w => hC.thP.pt_theta j t _)
    (fun a ha w => (hC.thP.ioP j t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hC.models.νV j t) _ (Fin m) (fun k => h₀ k * z') hJ.le (by rw [hrel]; exact one_ne_zero) hy hh g
  have h1 := congrFun (hPF.2 y u) g
  have h2 := hPF.1.eq ((X.R.extV j t).rangeRestrict y) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans ?_)))
  · rfl
  exact sum_eq_classSum X.R.toRealDat j t hB (Y.Z.ρ.tw i b 0 ∅ 1) hc0.1 hz'.2.1 hzc (hfz.symm.trans hflat) (hC.thP.ωP j t) hθ
    hvθ h₀ _ hrel ((X.R.HV j t).e y) u g

end GlobalTheory.LiftClassSumPrinc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftEqMultiplePrincipalLevelClassSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_eq_multiple_principalLevel_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ (y : (X.R.HV j t).H) (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
    ∃ (m : ℕ) (h₀ : Fin m → GA D (Vc D j)) (c : ℂ) (z : Bridge.Gf (Vc D j)),
      IsClassSystem (Vc D j) ((GlobalTheory.FlatVecSum.princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1)) h₀ ∧ z ∈ Subgroup.center (Bridge.Gf (Vc D j)) ∧
      X.R.thF j t y (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) =
        c • (GlobalTheory.FlatVecSum.princ (Y.Z.ρ.B i j b)).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) h₀
          (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) := by
  first | exact @GlobalTheory.LiftClassSumPrinc.thF_eq_classSum_princ | exact GlobalTheory.LiftClassSumPrinc.thF_eq_classSum_princ | (intros; apply GlobalTheory.LiftClassSumPrinc.thF_eq_classSum_princ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistConjugateTuplesSameRealisationExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOneOfChrEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

open _root_.Formalism.L2.Host

variable {D : D7} {T N : Type}

theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

theorem trivOn_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ : HChar E}
    (h : χ.TrivOn F) (a : ℕ) : (χ ^ a).TrivOn F := by
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · have h1 := h.1 v k
    simp only [HChar.resFin, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [locK_pow]
    rw [Finset.prod_pow, h1, one_pow]
  · have h1 := h.2 w k
    simp only [HChar.resInf, HChar.locInf, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [pow_apply']
    rw [Finset.prod_pow, h1, one_pow]

theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) : (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) : ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

theorem pow_eq_one_of_chrEq {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn : χ.OrderDvd n) :
    c ^ n = 1 := by
  have h1 := chrEq_pow h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

theorem exists_pow_aut (τ : ℂ ≃+* ℂ) {n : ℕ} (hn : 0 < n) : ∃ a, a < n ∧ ∀ z : ℂ, z ^ n = 1 → τ z = z ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨a, ha, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ (Complex.exp (2 * Real.pi * Complex.I / n)))
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  refine ⟨a, ha, fun z hz => ?_⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  rw [map_pow, ← h, ← pow_mul, ← pow_mul, mul_comm a b]

theorem exists_conj_pow {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) : ∃ n : ℕ, ∀ τ : ℂ ≃+* ℂ, ∃ a, a < n ∧
    (∀ x, (((L.xi t ^ a) x : Circle) : ℂ) = τ ((L.xi t x : Circle) : ℂ)) ∧ ∃ b, (L.xiH t ^ a) ^ b = L.xiH t := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : ∀ x, ((L.xi t x : Circle) : ℂ) ^ n = 1 := fun x => by
    have := DFunLike.congr_fun (pow_eq_one_of_chrEq (hL.xi t) ho) x
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have h2 : ∀ a x, (((L.xi t ^ a) x : Circle) : ℂ) = ((L.xi t x : Circle) : ℂ) ^ a := fun a x => by
    rw [MonoidHom.pow_apply]; exact map_pow Circle.coeHom _ _
  refine ⟨n, fun τ => ?_⟩
  obtain ⟨a, ha, h⟩ := exists_pow_aut τ hn
  obtain ⟨b, -, h'⟩ := exists_pow_aut τ.symm hn
  refine ⟨a, ha, fun x => by rw [h2, h _ (h1 x)], b, ?_⟩
  have e : (L.xi t ^ a) ^ b = L.xi t := MonoidHom.ext fun x => Circle.ext (by
    rw [← pow_mul, h2, pow_mul, ← h _ (h1 x), ← h' _ (by rw [← map_pow, h1, map_one]), RingEquiv.symm_apply_apply])
  exact GlobalTheory.ChrEqUnique.hchar_unique D (L.xi t) _ _ (e ▸ chrEq_pow (chrEq_pow (hL.xi t) a) b) (hL.xi t)

end GlobalTheory.ConjExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwLevPow
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwLevPow

theorem val_pow {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (a : ℕ) (v) :
    (χ ^ a).val v = χ.val v ^ a :=
  GlobalTheory.ConjExt.locK_pow χ a v _

theorem twLev_pow : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E)) (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      GlobalTheory.BigOn.Exp.TwConj.TwLev R χ xi Q xiR → ∀ a b : ℕ, (χ ^ a) ^ b = χ →
      GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ ^ a) (xi ^ a) Q (fun PP => xiR PP ^ a) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC χ xi Q xiR h a b hab

  have hQ0 : ∀ PP, PP ∉ R.Q A.μ0 := fun PP hPP =>
    ((hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP)) (by rw [hC.lev.xi_base]; intro x _; rfl)
  refine
    { xi := GlobalTheory.ConjExt.chrEq_pow h.xi a
      xi_fin := ?_
      xi_triv := GlobalTheory.ConjExt.trivOn_pow h.xi_triv a
      xi_tame := fun v x h1 h2 => by
        rw [GlobalTheory.ConjExt.loc_pow, h.xi_tame v x h1 h2, one_pow]
      Q_pl := h.Q_pl
      Q_off := h.Q_off
      Q_de := h.Q_de
      Q_ram := fun PP => Iff.trans
        (not_congr ⟨fun hu => hab ▸ GlobalTheory.ConjExt.unrAt_pow hu b, fun hu => GlobalTheory.ConjExt.unrAt_pow hu a⟩) (h.Q_ram PP)
      xiR := fun PP hP c k u h1 h2 => by
        show (xiR PP ^ a) u = (χ ^ a).locK PP k
        rw [GlobalTheory.ConjExt.locK_pow, MonoidHom.pow_apply, h.xiR PP hP c k u h1 h2]
      roots := h.roots
      muVal := ?_
      half := h.half
      guard := h.guard }
  · obtain ⟨n, hn, ho⟩ := h.xi_fin
    refine ⟨n, hn, ?_⟩
    show (χ ^ a) ^ n = 1
    rw [← pow_mul, mul_comm, pow_mul, show χ ^ n = 1 from ho, one_pow]
  · intro i P hP
    obtain ⟨x, hx⟩ := h.muVal i P hP
    have hP0 : Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q A.μ0 : Set (Pl D.host.E))) := by
      refine ⟨hP.1, fun hm => ?_, fun Q' hQ' => ?_⟩
      · rcases hm with hm | hm
        · exact hP.2.1 (Or.inl hm)
        · exact hQ0 _ hm
      · rcases hQ' with hQ' | hQ'
        · exact hP.2.2 Q' (Or.inl hQ')
        · exact absurd hQ' (hQ0 _)
    obtain ⟨g, c0R, c0L, ht⟩ := hC.fam.tie
    have hy := hC.fam.muVal i A.μ0 P ((ht.ok A.μ0 P).2 hP0)
    rw [hC.lev.xi_base, mul_one] at hy
    set y : D.what₂.LLˣ := A.muVal i A.μ0 P
    refine ⟨y * (y⁻¹ * x) ^ a, ?_⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, map_mul, map_pow, map_mul, Units.val_inv_eq_inv_val,
      map_inv₀, hx, hy, Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_mul, val_pow]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [inv_mul_cancel_left₀ (Units.ne_zero _)]

end GlobalTheory.TwLevPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistConjugateTuplesSameRealisationExtension
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj


open Classical in
theorem hasTuples_of_conj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (ψ ψ' : Twist D Circle) (t : T0) (τ : ℂ ≃+* ℂ), IsTupOf R B ψ t → ConjChar τ ψ ψ' → FixDat B τ →
      GlobalTheory.BigOn.Exp.TwConj.HasTuples T R κ v₀ O ph j B ψ ψ' := by
  intro hDS hCW h1 h2 h3 D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B hH hL ψ ψ' t τ ht hc hf
  have hC := hL.1
  obtain ⟨n, hn⟩ := GlobalTheory.ConjExt.exists_conj_pow hC.lev t
  obtain ⟨a, -, ha, b, hb⟩ := hn τ
  have hxi' : B.de.chi * ψ'.chi = R.xi t ^ a := by
    refine MonoidHom.ext fun x => Circle.ext ?_
    rw [ha x, ht.1]
    simp only [MonoidHom.mul_apply, Circle.coe_mul, map_mul, hf.1, hc.2]
  have hQ' : R.Q t = B.de.Q ∪ ψ'.Q := by rw [hc.1, ht.2]
  by_cases hχ : R.xiH t ^ a = R.xiH t
  · have e : R.xi t ^ a = R.xi t :=
      GlobalTheory.ChrEqUnique.idc_unique D _ _ _ (GlobalTheory.ConjExt.chrEq_pow (hC.lev.xi t) a) (by rw [hχ]; exact hC.lev.xi t)
    exact hasTuples_of_laws hL Ext.refl ht ⟨by rw [hxi', e], hQ'⟩
  · have h0 : R.xiH t ≠ 1 := fun h => hχ (by rw [h, one_pow])
    have h0a : R.xiH t ^ a ≠ 1 := fun h => h0 (by rw [← hb, h, one_pow])
    have hlev := twLev_of_core hC hL.2.2.2.2.1 t
    have hleva := GlobalTheory.TwLevPow.twLev_pow R F hC _ _ _ _ hlev a b hb
    obtain ⟨A0, R0, F0, v0, O0, hL0, hE0, hxi0, htr⟩ := GlobalTheory.BaseRestrict.restrict_to_base T R F κ v₀ O ph j B hL
    have hT0 := htr _ _ _ _ hlev
    have hT0a := htr _ _ _ _ hleva
    obtain ⟨T', A', R', F', v', O', hL', hE', htup⟩ := GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws h1 h2 h3 hDS hCW T R0 F0 κ v0 O0 ph j B hH hL0 Bool
      (fun b => if b then R.xiH t ^ a else R.xiH t) (fun b => if b then R.xi t ^ a else R.xi t) (fun _ => R.Q t)
      (fun b => if b then (fun PP => R.xiR t PP ^ a) else R.xiR t)
      (fun b => by cases b <;> assumption)
      (fun x y hxy => by
        cases x <;> cases y
        · rfl
        · exact absurd hxy.symm hχ
        · exact absurd hxy hχ
        · rfl)
      (fun b t0 => by rw [hxi0]; cases b; exacts [h0, h0a])
      (fun p hp => by
        obtain ⟨𝔭, h𝔭, h𝔭'⟩ := hT0.Q_de p hp
        exact ⟨𝔭, h𝔭, fun _ => h𝔭'⟩)
    obtain ⟨s, hs1, hs2⟩ := htup false
    obtain ⟨s', hs1', hs2'⟩ := htup true
    exact hasTuples_of_laws hL' (hE0.trans hE') (t := s) (t' := s')
      ⟨hs1.trans ht.1, hs2.trans ht.2⟩ ⟨hs1'.trans hxi'.symm, hs2'.trans hQ'⟩

end GlobalTheory.BigOn.Exp.TwConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistConjugateTuplesSameRealisationExtensionStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_conjugate_tuples_same_realisation_extension : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (ψ ψ' : Twist D Circle) (t : T0) (τ : ℂ ≃+* ℂ), IsTupOf R B ψ t → ConjChar τ ψ ψ' → FixDat B τ →
      GlobalTheory.BigOn.Exp.TwConj.HasTuples T R κ v₀ O ph j B ψ ψ' := by
  first | exact @GlobalTheory.BigOn.Exp.TwConj.hasTuples_of_conj | exact GlobalTheory.BigOn.Exp.TwConj.hasTuples_of_conj | (intros; apply GlobalTheory.BigOn.Exp.TwConj.hasTuples_of_conj <;> assumption)
end
end
