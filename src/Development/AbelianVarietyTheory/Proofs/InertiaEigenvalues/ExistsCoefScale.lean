module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfCore
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIoLFRecIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefScale
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatConj

open MvPolynomial


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.SeriesTie.Scale in
theorem exists_coef_scale : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κw v₀) → IoExt R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x : VsV D i ℂ, R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∈ B.valSpace) ∧ ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O hC _ hio i hO c hc u hu B hB hBo
  have hcV : (R.cV i).Is := hC.models.cV i
  have hinf : IsInfFam R.θ := hBo.θ ▸ hB.frame.vac.2.inf

  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hO.2.lift.c0
  have hfield : (inC (O i).c').comp (O i).jL = D.what₂.embLL := hO.2.lift.field
  obtain ⟨e, he0, he⟩ := GlobalTheory.CoefReal.exists_real_model (Vc D i) R.θ (R.cV i) (lamV D i) (c0L i) hinf hcV (hft.mapL i)
  have hce : c = e.toLinearMap := by
    refine LinearMap.ext_on_range (GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamV D i)) fun k => ?_
    obtain ⟨v', hv', hv0⟩ := hbc (bVV D.what₂.LL (lamV D i) k)
    refine (hc v' _ ?_).trans (hv0.trans (he0 _).symm)
    change MvPolynomial.map D.what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]

  obtain ⟨u', w₀, hu', -, hw⟩ := FWT.IsChosenExtremalVector.io _ hO.2.lift.v0 hio
  have huu : u' = u := funext fun ρ => Subtype.ext ((hu' ρ).trans (hu ρ).symm)
  rw [huu] at hw

  have hT := io_act hC.lev hC.thP hB hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)
  have hlam : B.w.lam = lamV D i := hBo.lam
  have hΔ : B.w.delta (Wc D i).rank = RealDat.Delta i := hBo.delta
  have hpq := GlobalTheory.CoefLatConj.pq_le hB
  have hirr : ∀ U : Submodule ℂ (R.cV i).W, (∀ h : GinfC (Vc D i), U.map ((R.cV i).ρ h) ≤ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hcV.2.2.2.2 U fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hcV.1 k hk, mul_one]
      exact hU ⟨a, ha⟩
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) i
  set x := PiTensorProduct.tprod ℂ u
  have hharm : ∀ w, R.ioP i x w ∈ harm (Wc D i).rank B.w B.F.BS := by
    rcases hirr ((harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x)) (fun h => by
      rintro _ ⟨w, hw', rfl⟩
      rw [Submodule.mem_comap, hT h h.2]
      exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x) := by
        rw [Submodule.mem_comap, hw, ← hΔ]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h ▸ Submodule.mem_top : w ∈ (harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x))

  haveI := hcV.2.2.2.1
  obtain ⟨κ, hcc⟩ := GlobalTheory.T.schur_equivariant_maps_proportional (GinfC (Vc D i)) (R.cV i).W (GLR D (Vc D i).rank → ℂ) (fun h => (R.cV i).ρ h)
    (fun h => LinearMap.funLeft ℂ ℂ fun y => (realGL R.θ (Vc D i) h)⁻¹ * y)
    (harmFn (Wc D i).rank B.w B.F.BS ∘ₗ R.ioP i x) (coefLin (lamV D i) ∘ₗ e.symm.toLinearMap) hirr
    ((coefLin_injective _).comp e.symm.injective)
    (by
      rintro _ ⟨w, rfl⟩
      have h1 : harmFn (Wc D i).rank B.w B.F.BS (R.ioP i x w) ∈
          (harm (Wc D i).rank B.w B.F.BS).map (harmFn (Wc D i).rank B.w B.F.BS) := Submodule.mem_map_of_mem (hharm w)
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt hpq, hlam] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨G', rfl⟩
      exact ⟨e G', congrArg (coefLin _) (e.symm_apply_apply G')⟩)
    (fun h w => funext fun y => by
      change harmFn _ B.w B.F.BS (R.ioP i x ((R.cV i).ρ h w)) y = harmFn _ B.w B.F.BS (R.ioP i x w) _
      rw [hT h h.2, ← hBo.θ]
      exact harmFn_fockGL _ _ _ _ _)
    (fun h w => funext fun y => by
      obtain ⟨v, rfl⟩ := e.surjective w
      change coefLin _ (e.symm ((R.cV i).ρ h (e v))) y = coefLin _ (e.symm (e v)) _
      rw [he h h.2, e.symm_apply_apply, e.symm_apply_apply]
      exact coefFn_translate _ _ _ _)
  subst hce
  refine ⟨κ, fun h0 => hΔ0 ?_, fun y => hharm _, fun y => ?_⟩
  · have h1 := LinearMap.congr_fun hcc w₀
    rw [h0, zero_smul, LinearMap.comp_apply, hw] at h1
    exact GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt hpq _ (hw ▸ hharm w₀) h1
  · have h1 := LinearMap.congr_fun hcc (e y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
    exact h1


set_option maxHeartbeats 4000000 in
theorem coefLat_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κw v₀) → IoExt R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) ∧ (∀ P ∈ B.valSpace, ∃! x : VsV D i ℂ, P = R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) ∧ ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (Oc : Subring ℂ), IsCoefRing σ emb Oc → (∀ h : Bridge.Gf (Vc D i), B.coefLat σ emb Oc h = Submodule.span Oc {P | ∃ Fv ∈ nabAtr emb (lamV D i) (B.latAt h), P = R.ioP i (PiTensorProduct.tprod ℂ u) (c (κ⁻¹ • GlobalTheory.CoefModel.mapVV σ (lamV D i) Fv))}) ∧ ∀ τ : ℂ ≃+* ℂ, (∀ a : K, τ (σ a) = σ a) → (∀ (h : Bridge.Gf (Vc D i)) (x x' : VsV D i ℂ), ConjVec i τ x x' → (R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∈ B.coefLat σ emb Oc h ↔ R.ioP i (PiTensorProduct.tprod ℂ u) (c ((τ κ / κ) • x')) ∈ B.coefLat σ emb (Oc.map (τ : ℂ →+* ℂ)) h)) ∧ ∀ (ψ1 ψ1' : Twist D Circle), ψ1.Good → ψ1'.Good → ConjChar τ ψ1 ψ1' → FixDat B τ → ∀ f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank, (∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∧ f' h = R.ioP i (PiTensorProduct.tprod ℂ u) (c ((τ κ / κ) • x'))) → (f ∈ B.mtLat σ emb Oc ψ1 ↔ f' ∈ B.mtLat σ emb (Oc.map (τ : ℂ →+* ℂ)) ψ1') := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O hC hFW hio i hO c hc u hu B hB hBo
  obtain ⟨κ, hκ0, hval, hκ⟩ := exists_coef_scale D G Pl0 T0 A T R F κw v₀ O hC hFW hio i hO c hc u hu B hB hBo
  let Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank := R.ioP i (PiTensorProduct.tprod ℂ u) ∘ₗ c
  have hlam := hBo.lam
  refine ⟨κ, hκ0, hκ, existsUnique_eq Φ hB hlam hκ0 hval hκ, fun K _ _ σ emb Oc hcoef =>
    ⟨fun h => coefLat_eq_span Φ hB hlam hκ0 hval hκ σ emb Oc h,
      fun τ hτ => ⟨fun h x x' hx => conj_mem_iff Φ hlam hκ0 hval hκ σ emb Oc τ hτ h hx, ?_⟩⟩⟩
  intro ψ1 ψ1' h1 h1' hcc hfd f f' hff
  constructor
  · exact GlobalTheory.MtLatConj.mtLat_conj D i B hB hlam Φ κ hκ0 hval hκ K σ emb Oc hcoef τ hτ ψ1 ψ1' h1 h1' hcc hfd f f' hff
  · intro hf'
    have hτ' : ∀ a : K, τ.symm (σ a) = σ a := fun a => by rw [τ.symm_apply_eq, hτ]
    have hcoef' : IsCoefRing σ emb (Oc.map (τ : ℂ →+* ℂ)) :=
      ⟨hcoef.emb, fun a => Subring.mem_map.2 ⟨_, hcoef.int a, hτ _⟩⟩
    have hOO : (Oc.map (τ : ℂ →+* ℂ)).map (τ.symm : ℂ →+* ℂ) = Oc := by
      ext z
      constructor
      · intro hz
        obtain ⟨_, hw, rfl⟩ := Subring.mem_map.1 hz
        obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 hw
        simpa using hb
      · intro hz
        exact Subring.mem_map.2 ⟨τ z, Subring.mem_map.2 ⟨z, hz, rfl⟩, by simp⟩
    have hτ0 : τ.symm κ ≠ 0 := (map_ne_zero _).2 hκ0
    have key := GlobalTheory.MtLatConj.mtLat_conj D i B hB hlam Φ κ hκ0 hval hκ K σ emb (Oc.map (τ : ℂ →+* ℂ)) hcoef' τ.symm hτ' ψ1' ψ1 h1' h1
      hcc.symm hfd.symm f' f (fun h => by
        obtain ⟨x, x', hx, e1, e2⟩ := hff h
        have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext hx
        have e3 : GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D i) ((τ κ / κ) • x') = (κ / τ.symm κ) • x := by
          rw [map_smulₛₗ, hx', mapVV_symm_mapVV]
          congr 1
          simp [map_div₀]
        refine ⟨(τ κ / κ) • x', (κ / τ.symm κ) • x, (congrArg Subtype.val e3).symm, e2, ?_⟩
        rw [e1, smul_smul, show τ.symm κ / κ * (κ / τ.symm κ) = 1 by field_simp, one_smul]
        rfl) hf'
    rwa [hOO] at key

end GlobalTheory.CoefLatConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverIsDictionaryFrameCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverIsDictionaryFrameCompatible
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem relab_and_goodEmb_of_inc {D : D7} (T : CoreJ D) (j : ℕ) (C : Cover T j T.σ₀) (hinc : C.σ₂.comp C.inc = T.σ₀) :
    (∀ τ, relab C.d.c₂ C.σ₂ τ = τ) ∧ GoodEmb C.d.c₂ C.σ₂ := by
  have key : ∀ (z : ℂ) (hz : z ∈ T.Q.c.F) (hz2 : z ∈ C.d.c₂.F), C.σ₂ ⟨z, hz2⟩ = z := by
    intro z hz hz2
    have h1 : (⟨z, hz2⟩ : C.d.c₂.F) = C.inc ⟨z, hz⟩ := Subtype.ext rfl
    have h2 : C.σ₂ (C.inc ⟨z, hz⟩) = T.σ₀ ⟨z, hz⟩ := by rw [← RingHom.comp_apply, hinc]
    rw [h1, h2]
    rfl
  refine ⟨fun τ => RingHom.ext fun x => key _ (T.Q.c.conj τ x) _, ?_⟩
  have hz : T.Q.H.rt0 ∈ T.Q.c.F := GlobalTheory.coe_baseKA_rho T.Q.l ▸ T.Q.c.le (baseKA T.Q.l).ρ.2
  have hz2 : T.Q.H.rt0 ∈ C.d.c₂.F := GlobalTheory.coe_baseKA_rho C.d.l₂ ▸ C.d.c₂.le (baseKA C.d.l₂).ρ.2
  have e : (IntermediateField.inclusion C.d.c₂.le) (baseKA C.d.l₂).ρ = ⟨T.Q.H.rt0, hz2⟩ :=
    Subtype.ext (GlobalTheory.coe_baseKA_rho C.d.l₂)
  unfold GoodEmb
  rw [RingHom.comp_apply]
  erw [e]
  exact key _ hz hz2

theorem isDict_cover_of_isUnif {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (W : HSp D)
    (hV : T.V j T.σ₀ = W) (hr : W.rank = D.R.r) (C : Cover T j T.σ₀) (hC : C.IsUnif) (hGE : GoodEmb C.d.c₂ C.σ₂) :
    IsDict C.U₂ W hr (castDict hV C.dict₂) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j)
        (T.x₀ j T.σ₀) := by
  subst hV
  obtain ⟨-, -, -, hU, -, hr', g, e, F, ik, φ, th, hMW, hth, hDL⟩ := hC
  have hP := hL.pins
  have hg := T.toCore.good_σ₀
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  have hio := GlobalTheory.TupleCover.iotaOK_and_frame T hL j hj _ hg _ rfl hr
  refine ⟨hU, hio.1, fun k => ⟨hMW k, fun τ => ?_, ?_⟩, fun k τ hτ => ?_, g, e, F, ik, φ, th, hth, hDL⟩
  · rw [(hU.2.1 k).2 τ]
    exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ, fun ⟨ρ, h⟩ => h ▸ hP.1.2.2.2 ρ⟩
  · have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
    obtain ⟨w⟩ := nonempty_uw hU'
    have h1 : (C.U₂.X k).κ0 = 2 * (C.U₂.X k).ξ0 :=
      (GlobalTheory.Dict.uw_lattice _ _ _ _ _ _ _ _ _ ((Formalism.L2.PjFree.goodEmb_iff _).2 hGE) hU' hr1 w k).1
    rw [h1, (hMW k).2, mul_neg]
  · rw [(hMW k).1, (hU.2.1 k).1]
    exact hio.2 τ (((hU.2.1 k).2 τ).1 hτ)


set_option maxHeartbeats 1000000 in
theorem cover_dict_frameTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → IsDict C.U₂ (Wc D i) (rank_Wc i) (castDict hV C.dict₂) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) ∧ FrameTie C.U₂ (Wc D i) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) ∧ (∀ τ, relab C.d.c₂ C.σ₂ τ = τ) ∧ GoodEmb C.d.c₂ C.σ₂ := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL _ _ _ hmod _ hT i _ hV C hC
  have hj := inR i
  have hinc : C.σ₂.comp C.inc = T.σ₀ := hC.2.2.1
  obtain ⟨hrel, hGE⟩ := relab_and_goodEmb_of_inc T _ C hinc
  have hD := isDict_cover_of_isUnif T hL _ hj _ hV (rank_Wc i) C hC hGE
  have hU := hD.1
  have hP := hL.pins
  have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hP.2.2.2 _ hj).1
  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  have hε : ∀ ρ a, (R.MW i (sg0 D A)).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun ρ a => by
    rw [hmod.order i ρ a, hdp,
      show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
  refine ⟨hD, fun k => ⟨isInvOf_cart _ _ _ hx (by have := hU.1; have := (hU.2.1 k).1; omega) hε,
    fun hq => isBasOf_onb _ _ _ hx hq hε⟩, hrel, hGE⟩

end GlobalTheory.LevelSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverIsDictionaryFrameCompatibleStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedCover_isDictionary_frameCompatible : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → IsDict C.U₂ (Wc D i) (rank_Wc i) (castDict hV C.dict₂) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) ∧ FrameTie C.U₂ (Wc D i) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) ∧ (∀ τ, relab C.d.c₂ C.σ₂ τ = τ) ∧ GoodEmb C.d.c₂ C.σ₂ := by
  first | exact @GlobalTheory.LevelSeries.cover_dict_frameTie | exact GlobalTheory.LevelSeries.cover_dict_frameTie | (intros; apply GlobalTheory.LevelSeries.cover_dict_frameTie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapCommutesFieldAutomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapCommutesFieldAutomorphism
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IoConj

section General

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {c : Coeff l} (j : c.F →+* c.F) {n : ℕ}

theorem gaStar_map (hj : ∀ σ x, j (embF c σ x) = embF c σ x) (ga : Matrix (Fin n) (Fin n) E)
    (P : MvPolynomial (LtN Dw n) c.F) :
    Formalism.L2.Pj.gaStar c ga (map j P) = map j (Formalism.L2.Pj.gaStar c ga P) := by
  induction P using MvPolynomial.induction_on with
  | C x => rw [map_C, Formalism.L2.Pj.gaStar, aeval_C, aeval_C, algebraMap_eq, map_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.L2.Pj.gaStar, aeval_X, letB, map_sum, map_mul, map_C, map_X, hj]

theorem pG_map (a : (E →+* ℂ) × ℕ → ℕ) : map j (pG (Dw := Dw) c a n) = pG (Dw := Dw) c a n := by
  have h : ∀ s i hi col, minorPolynomial (Dw := Dw) (n := n) c s i hi col = map j (minorPolynomial c s i hi col) := by
    intro s i hi col
    unfold minorPolynomial
    rw [RingHom.map_det]
    congr 1
    ext p q : 2
    simp
  symm
  unfold pG
  simp only [map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
  congr 1
  split_ifs
  · exact h _ _ _ _
  · exact h _ _ _ _
  · rw [map_zero]

theorem rhoM_map (hj : ∀ σ x, j (embF c σ x) = embF c σ x) {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))
    (lam : Ix → DomWeight n) (ga : Matrix (Fin n) (Fin n) E) (v v' : VVc c lam)
    (h : (v' : Pol c.F Ix n) = map j (v : Pol c.F Ix n)) :
    (rhoM c (fun t => embF c (pl t)) lam ga v' : Pol c.F Ix n) =
      map j (rhoM c (fun t => embF c (pl t)) lam ga v : Pol c.F Ix n) := by
  unfold rhoM
  split_ifs with hg
  · show actP lam _ (v' : Pol c.F Ix n) = map _ (actP lam _ (v : Pol c.F Ix n))
    rw [h]
    refine GlobalTheory.IoExtend.polyAction_map _ lam _ _ (fun t => ?_) _
    refine Matrix.ext fun a b => ?_
    exact (hj (pl t) _).symm
  · simp

theorem exists_stable (hj : ∀ σ x, j (embF c σ x) = embF c σ x) {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))
    (hpl : Function.Injective pl) (hin : ∀ σ, InPsi H σ ↔ ∃ t, σ = pl t)
    (lam : Ix → DomWeight n) (a : (E →+* ℂ) × ℕ → ℕ) (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam)
    (h : IoLFRec c (fun t => embF c (pl t)) lam a io hw) :
    ∃ N : Submodule c.F (VVc c lam), hw ∈ N ∧
      (∀ ga : Matrix (Fin n) (Fin n) E, gaᴴ * ga = 1 → ∀ v ∈ N, rhoM c (fun t => embF c (pl t)) lam ga v ∈ N) ∧
      ∀ v ∈ N, ∀ v' : VVc c lam, (v' : Pol c.F Ix n) = map j (v : Pol c.F Ix n) → io v' = map j (io v) := by
  obtain ⟨hok, cga, h⟩ := h
  let e : Ix ≃ GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights.Psi H := Equiv.ofBijective (fun t => ⟨pl t, (hin _).2 ⟨t, rfl⟩⟩)
    ⟨fun s t hst => hpl (congrArg Subtype.val hst), fun σ => by
      obtain ⟨t, ht⟩ := (hin σ.1).1 σ.2
      exact ⟨t, Subtype.ext ht.symm⟩⟩
  obtain ⟨ha, d, -, hd⟩ := GlobalTheory.LFCompare.pins_of_ioLF Dw c n e a lam io hw cga hok h
  have hcga : ∀ ga : Matrix (Fin n) (Fin n) E, gaᴴ * ga = 1 → j (cga ga) = cga ga := fun ga hga => by
    rw [hd ga hga, GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights.vacChar, map_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [map_zpow₀]
    exact congrArg (· ^ _) (hj _ _)
  obtain ⟨-, -, -, h4, -, -, h7, -⟩ := h
  let up : VVc c lam → VVc c lam := fun v => ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV j lam _ v.2⟩
  refine ⟨
    { carrier := {v | io (up v) = map j (io v)}
      add_mem' := fun {v w} hv hw' => ?_
      zero_mem' := ?_
      smul_mem' := fun s v hv => ?_ }, ?_, fun ga hga v hv => ?_, fun v hv v' hv' => ?_⟩
  · have e1 : up (v + w) = up v + up w := Subtype.ext (map_add (map j) _ _)
    show io (up (v + w)) = _
    rw [e1, map_add (f := _), map_add (f := _), map_add (f := _), show io (up v) = _ from hv, show io (up w) = _ from hw']
  · have e1 : up 0 = 0 := Subtype.ext (map_zero (map j))
    show io (up 0) = _
    rw [e1, map_zero, map_zero]
  · set_option synthInstance.maxHeartbeats 200000 in
    have e1 : up (s • v) = j s • up v := Subtype.ext (GlobalTheory.IoExtend.map_smul' j s _)
    show io (up (s • v)) = _
    rw [e1, map_smul, map_smul, GlobalTheory.IoExtend.map_smul', show io (up v) = _ from hv]
  · have e1 : up hw = hw := by
      apply Subtype.ext
      show map j (hw : Pol c.F Ix n) = _
      rw [show (hw : Pol c.F Ix n) = _ from hok, GlobalTheory.Proof.TensorMapDescent.map_ten]
      simp only [Formalism.L2.DIV.map_extremal]
    show io (up hw) = _
    rw [e1, h7, pG_map]
  · have e1 : up (rhoM c (fun t => embF c (pl t)) lam ga v) = rhoM c (fun t => embF c (pl t)) lam ga (up v) :=
      Subtype.ext (rhoM_map j hj pl lam ga v (up v) rfl).symm
    show io (up _) = _
    rw [e1, h4 ga hga, h4 ga hga, GlobalTheory.IoExtend.map_smul', hcga ga hga, show io (up v) = _ from hv, gaStar_map j hj]
  · rw [show v' = up v from Subtype.ext hv']
    exact hv

theorem eq_top_of_span {K X M : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup M] [Module ℂ M]
    {σ : K →+* ℂ} (c0 : X →ₛₗ[σ] M)
    (hli : ∀ (m : ℕ) (b : Fin m → X), LinearIndependent K b → LinearIndependent ℂ (fun k => c0 (b k)))
    (N : Submodule K X) (hN : Submodule.span ℂ (c0 '' (N : Set X)) = ⊤) : N = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := N.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
  obtain ⟨B, hB⟩ := GlobalTheory.AdTh.PhaseMap.exists_ext (N := ℂ) c0 hli
    { toFun := fun v => σ (f v)
      map_add' := fun v w => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun s v => by rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul] }
  replace hB : ∀ v, B (c0 v) = σ (f v) := hB
  have h1 : Submodule.span ℂ (c0 '' (N : Set X)) ≤ LinearMap.ker B := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    show B (c0 v) = 0
    rw [hB, show f v = 0 from hf hv, map_zero]
  refine hf0 (LinearMap.ext fun v => ?_)
  have h2 : B (c0 v) = 0 := h1 (hN ▸ Submodule.mem_top)
  rw [hB] at h2
  exact (map_eq_zero σ).1 h2

end General

section Main

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


set_option maxHeartbeats 1600000 in
theorem io_map_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) → M.io x' = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io x) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hfw i Tp tup O hO τ ta hta hfix x x' hx
  obtain ⟨fw⟩ := hfw
  have hT : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hθ : IsInfFam R.θ := hR.models.inf
  have hc : (R.cV i).Is := hR.models.cV i
  have hP := (GlobalTheory.AdTh.RecPair.isPair_record_ofCore D G Pl0 T0 A _ R F hR i A.μ0 hO.lift.std).1
  obtain ⟨n1, n2, -, n4⟩ := GlobalTheory.AdTh.coefMap_norm_equivariant_basis_ofCore D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hO
  obtain ⟨-, r2, -⟩ := GlobalTheory.RatGen.rational_points_generate D (Vc D i) (R.cV i) (hR.models.vpos i) hP.sigV hc
  obtain ⟨-, -, w1, -, -⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)
  have hj : ∀ σ y, (ta : O.c'.F →+* O.c'.F) (embF O.c' σ y) = embF O.c' σ y := fun σ y =>
    Subtype.ext ((hta _).trans (hfix.host σ y))
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_stable (ta : O.c'.F →+* O.c'.F) hj (tauE D) (GlobalTheory.SmoothForms.RealPts.tauE_injective D) w1
    (lamV D i) (wtA (κ i)) O.io O.hw hO.io
  haveI : FiniteDimensional O.c'.F (VsV D i O.c'.F) := Module.Finite.of_basis (Formalism.L2.DIV.bVV O.c'.F (lamV D i))
  have htop : N = ⊤ := by
    refine eq_top_of_span O.c0' n4 N ((r2 _ fun γ => ?_).resolve_left fun h0 => ?_)
    · obtain ⟨γE, -, -, h1, -, -, -, h5, -⟩ := GlobalTheory.AdTh.PhaseMap.rat_parts hθ hP.std γ
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨_, hN2 _ h5 v hv, n2 γ γE h1 v⟩
    · have h1 : O.c0' O.hw ∈ Submodule.span ℂ (O.c0' '' (N : Set _)) := Submodule.subset_span ⟨_, hN1, rfl⟩
      rw [h0, Submodule.mem_bot] at h1
      rw [h1, norm_zero] at n1
      exact zero_ne_one n1
  exact hN3 x (htop ▸ Submodule.mem_top) x' hx

end Main

end GlobalTheory.IoConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapCommutesFieldAutomorphismStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientMap_commutes_fieldAutomorphism : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) → M.io x' = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io x) := by
  first | exact @GlobalTheory.IoConj.io_map_conj | exact GlobalTheory.IoConj.io_map_conj | (intros; apply GlobalTheory.IoConj.io_map_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPullbackMemBoundedCuspidalHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPullbackMemBoundedCuspidalHolomorphic
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverHol
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X₂.Gm u w := by
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← Matrix.one_mulVec u, ← Matrix.one_mulVec w, ← h1]
  rw [CompactEntryBounds.hermC_expand X, CompactEntryBounds.hermC_expand X₂]
  simp only [hγ, Matrix.one_mulVec]

theorem col_mul (A Y : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col (A * Y) c = A *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col Y c := by
  funext i; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gram_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (γ.map τ * Y) = ReciprocityTheory.ChartRestriction.G.FD.gram τ X₂.Gm Y := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply]
  rw [col_mul, col_mul, hermC_move X X₂ hγ]

def majM (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p : ℕ) (hp : p ≤ r) (M : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → ℂ) : ℝ :=
  2 * (∑ a : Fin p, ∑ b : Fin p,
    hermC τ G v (ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hp a)) *
      ((ReciprocityTheory.ChartRestriction.G.FD.gram τ G M).submatrix (Fin.castLE hp) (Fin.castLE hp))⁻¹ a b *
      conj (hermC τ G v (ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hp b)))).re - (hermC τ G v v).re

theorem maj_eq (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ v = majM τ.1 X.Gm X.p0 X.p0_le (mat x τ) v := rfl

omit [NumberField E] [IsCMField E] in
theorem majM_congr (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {p q : ℕ} (hp : p ≤ r) (hq : q ≤ r) (h : p = q)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) : majM τ G p hp M v = majM τ G q hq M v := by
  subst h; rfl

theorem majM_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ) {p : ℕ} (hp : p ≤ r)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    majM τ X.Gm p hp (γ.map τ * M) (γ.map τ *ᵥ v) = majM τ X₂.Gm p hp M v := by
  unfold majM
  simp only [col_mul, hermC_move X X₂ hγ, gram_move X X₂ hγ]

theorem maj_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (hp : X.p0 = X₂.p0)
    (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ)
    (hrel : mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩) (v : Fin r → E) :
    X.maj x' ⟨τ, h₁⟩ (Data.emb τ (γ *ᵥ v)) = X₂.maj x ⟨τ, h₂⟩ (Data.emb τ v) := by
  rw [maj_eq, maj_eq, hrel, ← ReciprocityTheory.ChartRestriction.G.AR.Inst.emb_mulVec, majM_move X X₂ hγ]
  exact majM_congr _ _ _ _ hp _ _

theorem dmin_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w)
    (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ)
    (hrel : mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩) (i : Fin (r + 1)) :
    dmin X.Gm x' ⟨τ, h₁⟩ i = dmin X₂.Gm x ⟨τ, h₂⟩ i := by
  unfold dmin
  rw [hrel, gram_move X X₂ hγ]

theorem pnorm_move (X X₂ : Data E r) (hΨ : ∀ τ, τ ∈ X₂.Ψ ↔ τ ∈ X.Ψ) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (la : Wt X.Ψ r) (la₂ : Wt X₂.Ψ r)
    (hla : ∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ) i, la₂ ⟨τ, h₂⟩ i = la ⟨τ, h₁⟩ i)
    (P : Frame X.Ψ r → ℂ) (P₂ : Frame X₂.Ψ r → ℂ) (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r)
    (hrel : ∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩)
    (u : ℂ) (hu : ‖u‖ = 1) (hP : P₂ x = u * P x') :
    X₂.pnorm la₂ P₂ x = X.pnorm la P x' := by
  unfold Data.pnorm
  rw [hP, norm_mul, hu, one_mul]
  congr 1
  refine Fintype.prod_equiv (Equiv.subtypeEquivRight hΨ) _ _ (fun τ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h₁ : τ.1 ∈ X.Ψ := (hΨ τ.1).1 τ.2
  show _ = ‖dmin X.Gm x' ⟨τ.1, h₁⟩ i.succ / dmin X.Gm x' ⟨τ.1, h₁⟩ i.castSucc‖ ^ (-(la ⟨τ.1, h₁⟩ i : ℝ) / 2)
  rw [dmin_move X X₂ hγ x x' τ.1 τ.2 h₁ (hrel τ.1 τ.2 h₁), dmin_move X X₂ hγ x x' τ.1 τ.2 h₁ (hrel τ.1 τ.2 h₁),
    ← hla τ.1 τ.2 h₁ i]

theorem exists_firstMinimumSq_bound_of_rationalIsometry (X X₂ : Data E r) (hr : 0 < r) (hΨ : ∀ τ, τ ∈ X₂.Ψ ↔ τ ∈ X.Ψ) (γ : GL (Fin r) E)
    (hΛ : (X.Λ : Set (Fin r → E)) = (γ : Matrix (Fin r) (Fin r) E).mulVec '' (X₂.Λ : Set (Fin r → E)))
    (hγ : ∀ v w, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) =
      herm X₂.Gm v w) (hp : X.p0 = X₂.p0) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ X₂.dom, ∀ x' ∈ X.dom,
      (∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩) →
      X.firstMinimumSq x' ≤ K * X₂.firstMinimumSq x := by
  set K : ℝ := 1 + ∑ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ with hKdef
  have hc2 : ∀ τ : X₂.Ψ, 0 < X₂.c τ := fun τ => IsotropicThreshold.c_pos X₂ τ
  have hKτ : ∀ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ ≤ K * X₂.c τ := by
    intro τ
    have h1 : X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ ≤ K := by
      have := Finset.single_le_sum (f := fun τ : X₂.Ψ => X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ)
        (fun τ _ => (div_pos (IsotropicThreshold.c_pos X _) (hc2 τ)).le) (Finset.mem_univ τ)
      linarith
    rwa [div_le_iff₀ (hc2 τ)] at h1
  have hK : 0 < K := by
    have := Finset.sum_nonneg (fun τ (_ : τ ∈ (Finset.univ : Finset X₂.Ψ)) =>
      (div_pos (IsotropicThreshold.c_pos X ⟨τ.1, (hΨ τ.1).1 τ.2⟩) (hc2 τ)).le)
    linarith
  refine ⟨K, hK, fun x hx x' hx' hrel => ?_⟩
  obtain ⟨w₀, hw₀, hw₀0⟩ := ReciprocityTheory.ChartRestriction.G.AR.Inst.lam_ne X₂ hr
  unfold Data.firstMinimumSq
  set S := {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x' τ (Data.emb τ.1 v)} with hS
  set S₂ := {t | ∃ v ∈ X₂.Λ, v ≠ 0 ∧ t = ∑ τ, X₂.c τ * X₂.maj x τ (Data.emb τ.1 v)} with hS₂
  have hSb : BddBelow S := ⟨0, by
    rintro _ ⟨v, -, hv0, rfl⟩
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (IsotropicThreshold.c_pos X τ).le
      (X.maj_pos hx' τ (emb_ne_zero τ.1 hv0)).le⟩
  have hS₂ne : S₂.Nonempty := ⟨_, w₀, hw₀, hw₀0, rfl⟩
  have key : sInf S / K ≤ sInf S₂ := by
    refine le_csInf hS₂ne ?_
    rintro _ ⟨w, hw, hw0, rfl⟩
    rw [div_le_iff₀ hK]
    have hγw : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ X.Λ := by
      have : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ (X.Λ : Set (Fin r → E)) := by
        rw [hΛ]; exact ⟨w, hw, rfl⟩
      exact this
    have hγw0 : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ≠ 0 := by
      intro h0
      apply hw0
      have e : (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) = w := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← e, h0, Matrix.mulVec_zero]
    refine (csInf_le hSb ⟨_, hγw, hγw0, rfl⟩).trans ?_
    have hre : ∑ τ : X.Ψ, X.c τ * X.maj x' τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) =
        ∑ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ * X₂.maj x τ (Data.emb τ.1 w) := by
      refine (Fintype.sum_equiv (Equiv.subtypeEquivRight hΨ) _ _ (fun τ => ?_)).symm
      show X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ * X₂.maj x τ (Data.emb τ.1 w) = X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ *
        X.maj x' ⟨τ.1, (hΨ τ.1).1 τ.2⟩ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w))
      rw [maj_move X X₂ hγ hp x x' τ.1 τ.2 ((hΨ τ.1).1 τ.2) (hrel τ.1 τ.2 _)]
    rw [hre, Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => ?_
    have hm := (X₂.maj_pos hx τ (emb_ne_zero τ.1 hw0)).le
    calc _ ≤ (K * X₂.c τ) * X₂.maj x τ (Data.emb τ.1 w) := mul_le_mul_of_nonneg_right (hKτ τ) hm
      _ = _ := by ring
  rwa [div_le_iff₀ hK, mul_comm] at key

theorem cover_pull_holSub0 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ ∈ holSub0 C.U₂.X (laU C.U₂ a n) := by
  intro D T hL j hj σ hσ C hC a n hDom f hf hfh f₂ hf₂ hP
  refine Submodule.mem_inf.2 ⟨holCusp_mem_holSub _ _ (fun k₂ => ?_), rdU_mem_offZero _ _⟩
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ
  have hS := Formalism.L2.Pj.abelian₂.holSub_SS ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _ _ (Submodule.mem_inf.1 hfh).1
  obtain ⟨k, γ, hΛ, hh, -, u, hu1, hx⟩ := GlobalTheory.CoverConst.cover_scalar_const D T hL j hj σ hσ C hC n k₂
  obtain ⟨hΨ, hla⟩ := GlobalTheory.CoverConst.psi_and_weight_eq D T hL j hj σ hσ C hC k₂ k
  have hp : ((T.U j σ).X k).p0 = (C.U₂.X k₂).p0 := ((hU₁.2.1 k).1).trans ((hU₂.2.1 k₂).1).symm
  let G : Frame (C.U₂.X k₂).Ψ D.R.r → Frame ((T.U j σ).X k).Ψ D.R.r := fun x τ =>
    ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ :
      Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hGrel : ∀ x (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ),
      mat (G x) ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩ :=
    fun _ _ _ _ => rfl
  have hG : ∀ x ∈ (C.U₂.X k₂).dom, G x ∈ ((T.U j σ).X k).dom ∧
      rdU C.U₂ f₂ k₂ x = u * rdU (T.U j σ) f k (G x) := fun x hxd =>
    ⟨(hx x (G x) hxd (hGrel x)).1, (hx x (G x) hxd (hGrel x)).2 a hDom f hf f₂ hf₂ hP⟩
  have hpn : ∀ x ∈ (C.U₂.X k₂).dom, (C.U₂.X k₂).pnorm (laU C.U₂ a n k₂) (rdU C.U₂ f₂ k₂) x =
      ((T.U j σ).X k).pnorm (laU (T.U j σ) a n k) (rdU (T.U j σ) f k) (G x) := fun x hxd =>
    pnorm_move _ _ hΨ hh _ _ (fun τ h₂ h₁ i => hla a n τ h₂ h₁ i) _ _ x (G x) (hGrel x) u hu1 (hG x hxd).2
  have hsec := hU₂.2.2.2.2.1 a n hDom f₂ hf₂ k₂
  obtain ⟨B, hB⟩ := (hS k).1.2
  have hbdd : (C.U₂.X k₂).IsBddSec (laU C.U₂ a n k₂) (rdU C.U₂ f₂ k₂) :=
    ⟨hsec, B, fun x hxd => (hpn x hxd).trans_le (hB _ (hG x hxd).1)⟩
  by_cases hr : 0 < D.R.r
  · obtain ⟨c₀, hc₀, hgt⟩ := ReciprocityTheory.ChartRestriction.G.FD.spectralGap_holds D.R.r _ _ _ (hS k)
    obtain ⟨C₁, hC₁⟩ := ReciprocityTheory.ChartRestriction.G.FD.cuspidalDecay_holds D.R.r _ _ _ c₀ hc₀.le hgt
    obtain ⟨K, hK, hle⟩ := exists_firstMinimumSq_bound_of_rationalIsometry _ _ hr hΨ γ hΛ hh hp
    refine GlobalTheory.CuspUnif.mem_SS_of_decay _ hr _ _ hbdd (C := |C₁|) (c := 2 * Real.pi * c₀ / K) (by positivity)
      fun x hxd => ?_
    have hGd := (hG x hxd).1
    have hl : 0 < ((T.U j σ).X k).firstMinimumSq (G x) := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom _ hr hGd)
    have hl₂ : 0 < (C.U₂.X k₂).firstMinimumSq x := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom _ hr hxd)
    have hle' := hle x hxd (G x) hGd (hGrel x)
    rw [hpn x hxd]
    refine (hC₁ (G x) hGd).trans ?_
    refine mul_le_mul (le_abs_self _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg _)
    have hq : 2 * Real.pi * c₀ / K / (C.U₂.X k₂).firstMinimumSq x ≤ 2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x) := by
      rw [div_div, div_le_div_iff₀ (by positivity) hl]
      exact mul_le_mul_of_nonneg_left hle' (by positivity)
    have e1 : -2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x) =
        -(2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x)) := by ring
    rw [e1, neg_div]
    exact neg_le_neg hq
  · refine ⟨hbdd, fun ξ hξ x _ => ?_⟩
    exfalso
    apply hξ.2.2
    funext i
    exact absurd i.2 (by omega)

end GlobalTheory.CoverHol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPullbackMemBoundedCuspidalHolomorphicStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverPullback_mem_boundedCuspidalHolomorphic : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ ∈ holSub0 C.U₂.X (laU C.U₂ a n) := by
  first | exact @GlobalTheory.CoverHol.cover_pull_holSub0 | exact GlobalTheory.CoverHol.cover_pull_holSub0 | (intros; apply GlobalTheory.CoverHol.cover_pull_holSub0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTieMoveOfPin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem heckeTie_of_same {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (h3 : GlobalTheory.TwistChoice.SameForms Y Y')
    (hsp : HEq D.sp D'.sp) {ρ : Setup X} {ρ' : Setup X'} {i : X.Tw} {i' : X'.Tw} (hi : HEq i i')
    {j : Fin D.R.m} {j' : Fin D'.R.m} (hj : (j : ℕ) = j') {b : Bool}
    (hmu : HEq (ρ.B i j b).mu (ρ'.B i' j' b).mu) (hlev : HEq (ρ.levK i j b) (ρ'.levK i' j' b))
    (r : Rd ρ Y i j b) (r' : Rd ρ' Y' i' j' b)
    (hR : ∀ (f : Y.Fm i ((j : ℕ) + 1) b) (f' : Y'.Fm i' ((j' : ℕ) + 1) b), HEq f f' → HEq (r' f') (r f))
    (ht : HeckeTie r) : HeckeTie r' := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3 hsp
  subst a1; subst a2; subst a3; subst hsp
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  subst hi
  obtain rfl : j = j' := Fin.ext hj
  have e : ∀ x, r' x = r x := fun x => eq_of_heq (hR x x HEq.rfl)
  have hmu' : (ρ'.B i j b).mu = (ρ.B i j b).mu := eq_of_heq hmu.symm
  have hlev' : ρ'.levK i j b = ρ.levK i j b := eq_of_heq hlev.symm
  have hk : ∀ k P R z F, ρ'.hecke i j b k P R z F = ρ.hecke i j b k P R z F := fun k P R z F => by
    funext x
    rw [Setup.hecke_apply, Setup.hecke_apply, hmu']
  have hd : ∀ k P α R z, ρ'.IsHeckeDatum i j b k P α R z ↔ ρ.IsHeckeDatum i j b k P α R z := fun k P α R z =>
    ⟨fun d => ⟨d.1, hlev' ▸ d.2, d.3⟩, fun d => ⟨d.1, hlev'.symm ▸ d.2, d.3⟩⟩
  have ha : ∀ k P f g, HeckeAt r' k P f g ↔ HeckeAt r k P f g := fun k P f g =>
    ⟨fun hg α R z d => by have := hg α R z ((hd k P α R z).2 d); rwa [e, e, hk] at this,
      fun hg α R z d => by rw [e, e, hk]; exact hg α R z ((hd k P α R z).1 d)⟩
  intro k P hkP f hf
  exact (ha k P f _).2 (ht k P hkP f (by obtain ⟨g, hg⟩ := hf; exact ⟨g, (ha k P f g).1 hg⟩))

theorem heckeTie_move_of_pin : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw},
    (∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) (b : Bool),
      HEq (ρ.B i j b).mu (ρ'.B i' (h.cm j) b).mu ∧ HEq (ρ.levK i j b) (ρ'.levK i' (h.cm j) b)) →
    ∀ (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' →
      ∀ (j : Fin D.R.m) b, HeckeTie (rd i j b) → HeckeTie (rd' i' (h.cm j) b) := by
  intro D D' ι e h ρ ρ' hB rd rd' hr i i' hi j b ht
  have hR : ∀ (f : D.nexp.Fm i ((j : ℕ) + 1) b) (f' : D'.nexp.Fm i' ((h.cm j : ℕ) + 1) b), HEq f f' →
      HEq (rd' i' (h.cm j) b f') (rd i j b f) := fun f f' hf => by
    have h1 : h.fmCast hi ((j : ℕ) + 1) b f = f' := eq_of_heq ((h.fmCast_heq hi _ b f).trans hf)
    rw [← h1]
    exact hr i i' hi j b f
  exact heckeTie_of_same h.gal h.set h.frm h.sp hi (h.cm_val j).symm (hB i i' hi j b).1 (hB i i' hi j b).2
    (rd i j b) (rd' i' (h.cm j) b) hR ht


set_option maxHeartbeats 4000000 in
theorem SameData.mu_levK {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
    {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (hs : SameData ρ ρ') (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i')
    (j : Fin D.R.m) (b : Bool) :
    HEq (ρ.B i j b).mu (ρ'.B i' (h.cm j) b).mu ∧ HEq (ρ.levK i j b) (ρ'.levK i' (h.cm j) b) := by
  have hj : (j : ℕ) = h.cm j := rfl
  generalize h.cm j = j' at hj
  obtain ⟨r, rfl⟩ := h.exists_rest
  cases SameData.eq_up r hs
  cases hi
  cases (Fin.ext hj : j = j')
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem heckeTie_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameData ρ ρ' →
    ∀ (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' →
      ∀ (j : Fin D.R.m) b, HeckeTie (rd i j b) → HeckeTie (rd' i' (h.cm j) b) :=
  fun h _ _ hs => heckeTie_move_of_pin h (hs.mu_levK h)

end GlobalTheory.TwInputs.Move

end
end
