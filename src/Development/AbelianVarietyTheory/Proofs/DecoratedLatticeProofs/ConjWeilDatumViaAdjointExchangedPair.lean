module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLaw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicEqComponentAtPlaceMulOffPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjAdjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.PairLift

variable {D : D7}

theorem dagger_eq (S T : HSp D) (x : WO S T) : dagger S T x = adjO T S x := by
  simp only [dagger, adjO, giA, gA, adj, Matrix.mul_assoc]
  rfl

theorem cj_dagger (S T : HSp D) (f : WO S T → ℂ) : cj (dagger T S) f = dag S T f := by
  funext y; simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dag, dagger_eq]

theorem conjAdjoint_apply {S T : HSp D} (om : Rep S T) (g : GA D T) (h : GA D S) (f : WO T S → ℂ) :
    conjAdjoint om (g, h) f = dag S T (om (h, g) (dag T S f)) := by
  show cj (dagger T S) (om (h, g) (cj (dagger S T) f)) = _
  rw [cj_dagger, cj_dagger]

theorem chi_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (hR : ResEta D χ n) (y : (AE D)ˣ) :
    χ (Units.map (cA D).toMonoidHom y) = (χ y)⁻¹ := by
  obtain ⟨⟨η, hη⟩, hall⟩ := hR
  have hprod : y * Units.map (cA D).toMonoidHom y =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y) := by
    apply Units.ext
    rw [GlobalTheory.Mem.EtaTilde.idF_norm]
    rfl
  have h1 : χ y * χ (Units.map (cA D).toMonoidHom y) = 1 := by
    rw [← map_mul, hprod, hall η hη, hη.2.2.1, one_pow]
  exact eq_inv_of_mul_eq_one_right h1

theorem isSplitIdem_conj {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

theorem suppAt_conj {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [cA_cA, add_comm]
  exact h i j

theorem det_inv_eq (V : HSp D) (g : GA D V) : (mt V g⁻¹).det = cA D (mt V g).det := by
  have h1 : (giA V).det * (gA V).det = 1 := by rw [← Matrix.det_mul, giA_mul_gA, Matrix.det_one]
  rw [mt_inv, Matrix.det_mul, Matrix.det_mul, adj, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  linear_combination ((mt V g).map (cA D)).det * h1

theorem isDetAt_conj {e : AE D} (he : e * e = e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    IsDetAt (cA D e) V g (Units.map (cA D).toMonoidHom x⁻¹) := by
  have hd : (mt V g⁻¹).det * (mt V g).det = 1 := by rw [← Matrix.det_mul, mt_inv_mul, Matrix.det_one]
  have hz : ((x⁻¹ : (AE D)ˣ) : AE D) = e * (mt V g⁻¹).det + (1 - e) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hx]
    linear_combination e * hd + ((mt V g⁻¹).det * (mt V g).det - (mt V g⁻¹).det - (mt V g).det + 1) * he
  show cA D ((x⁻¹ : (AE D)ˣ) : AE D) = cA D e * (mt V g).det + (1 - cA D e)
  rw [hz, map_add (f := _), map_mul, map_sub, map_one, det_inv_eq, cA_cA]

end GlobalTheory.ConjAdjWeil

namespace GlobalTheory.ConjAdjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.PairLift

theorem isWeilDatumO_conjAdjoint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ T S χT χS (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) := by
  intro D ψ S T χS χT om hw
  have hS : AdjLaw ψ S T := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std S T
  have hT : AdjLaw ψ T S := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std T S
  have thB : ∀ f : WO T S → ℂ, IsThetaFunO ψ T S f → IsThetaFunO ψ S T (dag T S f) := hT.theta
  have thA : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ T S (dag S T f) := hS.theta
  have key : ∀ (g : GA D T) (h : GA D S) (f : WO T S → ℂ),
      conjAdjoint om (g, h) f = dag S T (om (h, g) (dag T S f)) := fun g h f => conjAdjoint_apply om g h f
  have dd : ∀ f : WO T S → ℂ, dag S T (dag T S f) = f := fun f => by
    funext y; simp only [dag, hT.invol, Complex.conj_conj]
  have d0 : adjO S T 0 = 0 := by
    have := hS.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have d0' : adjO T S 0 = 0 := by
    have := hT.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  refine ⟨hw.std, hw.hecT, hw.hecS, hw.resT, hw.resS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨g, h⟩ f hf
    rw [key]
    exact thA _ (hw.om_pres _ _ (thB f hf))
  · intro g h w₀ f hf
    have e1 : dag T S (heisO ψ T S w₀ f) = heisO ψ S T (adjO S T w₀) (dag T S f) := by
      rw [hT.Heisenberg₂, hT.invol]
    rw [key, key, e1, hw.om_heis _ _ _ _ (thB f hf), ← hS.act, ← hS.Heisenberg₂]
  · intro γ hγ γ' hγ' f hf
    rw [key]
    have := hw.om_aut γ' hγ' γ hγ (dag T S f) (thB f hf)
    simp only [dag] at this ⊢
    rw [d0, this, d0', Complex.conj_conj]
  · intro f hf w
    have e : (fun p : GA D T × GA D S => conjAdjoint om p f w) =
        fun p => starRingEnd ℂ (om (Prod.swap p) (dag T S f) (adjO S T w)) := by
      funext p
      obtain ⟨g, h⟩ := p
      rw [key]
      rfl
    rw [e]
    exact Complex.continuous_conj.comp ((hw.om_cont _ (thB f hf) _).comp continuous_swap)
  · intro μ 𝓕 hμ h𝓕 p f hf
    obtain ⟨g, h⟩ := p
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : BorelSpace (WO T S) := ⟨rfl⟩
    let dE : WO T S ≃+ WO S T :=
      { toFun := adjO S T, invFun := adjO T S, left_inv := hT.invol, right_inv := hS.invol, map_add' := hS.add }
    let hE : WO S T ≃ₜ WO T S :=
      { toFun := adjO T S, invFun := adjO S T, left_inv := hS.invol, right_inv := hT.invol,
        continuous_toFun := hT.cont, continuous_invFun := hS.cont }
    set ν : Measure (WO S T) := μ.map dE with hν
    have hνH : ν.IsAddHaarMeasure := dE.isAddHaarMeasure_map μ hS.cont hT.cont
    have hfm : Measurable (adjO T S) := hT.cont.measurable
    have hdm : Measurable (adjO S T) := hS.cont.measurable
    have hmp : MeasurePreserving (adjO T S) ν μ := by
      refine ⟨hfm, ?_⟩
      rw [hν, Measure.map_map hfm (show Measurable dE from hdm)]
      have : adjO T S ∘ dE = id := funext fun w => hT.invol w
      rw [this, Measure.map_id]
    have hemb : MeasurableEmbedding (adjO T S) := hE.measurableEmbedding
    have hfd : IsAddFundamentalDomain (ratL T S) (adjO T S ⁻¹' 𝓕) ν := by
      refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving
        (e := fun γ : ratL S T => (⟨adjO S T γ, (hS.rat γ).2 γ.2⟩ : ratL T S)) ⟨?_, ?_⟩ ?_
      · intro a b hab
        have := congrArg (fun z : ratL T S => adjO T S (z : WO S T)) hab
        simp only [hT.invol] at this
        exact Subtype.ext this
      · intro b
        refine ⟨⟨adjO T S b, (hT.rat b).2 b.2⟩, Subtype.ext ?_⟩
        exact hS.invol b
      · intro γ x
        show adjO T S (adjO S T (γ : WO T S) + x) = (γ : WO T S) + adjO T S x
        rw [hT.add, hT.invol]
    calc ∫⁻ w in 𝓕, ‖conjAdjoint om (g, h) f w‖ₑ ^ 2 ∂μ
        = ∫⁻ w in 𝓕, (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T w) ∂μ := by
          congr 1
          funext w
          rw [key]
          simp [dag]
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T (adjO T S z)) ∂ν :=
          (hmp.setLIntegral_comp_preimage_emb hemb (fun w => (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T w)) 𝓕).symm
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, ‖om (h, g) (dag T S f) z‖ₑ ^ 2 ∂ν := by simp only [hS.invol]
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, ‖dag T S f z‖ₑ ^ 2 ∂ν := hw.om_unit ν _ hνH hfd (h, g) _ (thB f hf)
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, (fun w => ‖f w‖ₑ ^ 2) (adjO T S z) ∂ν := by
          congr 1
          funext z
          simp [dag]
      _ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := hmp.setLIntegral_comp_preimage_emb hemb (fun w => ‖f w‖ₑ ^ 2) 𝓕
  · intro e he g h hsg hsh x y hx hy
    obtain ⟨r, hr, hℓ⟩ := hw.om_split (cA D e) (isSplitIdem_conj he) h g (suppAt_conj hsh) (suppAt_conj hsg) _ _
      (isDetAt_conj he.1 hy) (isDetAt_conj he.1 hx)
    refine ⟨r, hr, fun ℓ hinv f hf => ?_⟩
    have dadd : ∀ a b : WO S T → ℂ, dag S T (a + b) = dag S T a + dag S T b := fun a b => by
      funext z; simp [dag]
    have dsmul : ∀ (c : ℂ) (a : WO S T → ℂ), dag S T (c • a) = starRingEnd ℂ c • dag S T a := fun c a => by
      funext z; simp [dag]
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => starRingEnd ℂ (ℓ (dag S T F))
        map_add' := fun a b => by simp only [dadd, map_add (f := _)]
        map_smul' := fun c a => by
          simp only [dsmul, map_smul, smul_eq_mul, map_mul, RingHom.id_apply, Complex.conj_conj] }
    have hinv' : ∀ u : WO S T, (∀ i j, cA D (cA D e) * u i j = u i j) → ∀ F, IsThetaFunO ψ S T F →
        ℓ' (heisO ψ S T u F) = ℓ' F := by
      intro u hu F hF
      have hu' : IsHalf e u := fun i j => by have := hu i j; rwa [cA_cA] at this
      have e2 : dag S T (heisO ψ S T u F) = heisO ψ T S (adjO T S u) (dag S T F) := by rw [hS.Heisenberg₂, hS.invol]
      show starRingEnd ℂ (ℓ (dag S T (heisO ψ S T u F))) = starRingEnd ℂ (ℓ (dag S T F))
      rw [e2, hinv _ (hT.half e u hu') _ (thA F hF)]
    have main := hℓ ℓ' hinv' (dag T S f) (thB f hf)
    have m2 : starRingEnd ℂ (ℓ (dag S T (om (h, g) (dag T S f)))) =
        (r : ℂ) * (splitFacO χS χT (Units.map (cA D).toMonoidHom y⁻¹) (Units.map (cA D).toMonoidHom x⁻¹) : ℂ) *
          starRingEnd ℂ (ℓ f) := by
      have := main
      simp only [ℓ', LinearMap.coe_mk, AddHom.coe_mk, dd] at this
      exact this
    have hconj := congrArg (starRingEnd ℂ) m2
    rw [Complex.conj_conj] at hconj
    have hfac : (splitFacO χS χT (Units.map (cA D).toMonoidHom y⁻¹) (Units.map (cA D).toMonoidHom x⁻¹))⁻¹ =
        splitFacO χT χS x y := by
      unfold splitFacO
      rw [chi_conj hw.resT, chi_conj hw.resS, map_inv, map_inv, inv_inv, inv_inv, _root_.mul_inv_rev, inv_inv]
    rw [key, hconj, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, ← Circle.coe_inv_eq_conj, hfac]

end GlobalTheory.ConjAdjWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ T S χT χS (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) := by
  first | exact @GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint | exact GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint | (intros; apply GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLaws
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf.SupFin

theorem supSob_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D), (∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k f ≠ ⊤) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), (∀ U : AddSubgroup (WO S T), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, dRho (heisO ψ S T) θ τ z f ∈ GlobalTheory.Size.thetaLevel ψ S T U) ∧ ∃ C : ℝ≥0, ∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k (dRho (heisO ψ S T) θ τ z f) ≤ C * supSob ψ θ (k + 1) f) ∧ ∀ k (f g : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → supSob ψ θ k (f + g) ≤ supSob ψ θ k f + supSob ψ θ k g ∧ supSob ψ θ k (c • f) = ‖c‖ₑ * supSob ψ θ k f := by
  intro D ψ hψ θ hθ S T
  have ha : ∀ g g' : WO S T → ℂ, (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) (g + g') ≤
      (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g + (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g' :=
    GlobalTheory.Size.SupWord.supN_add_le
  have hs : ∀ (c : ℂ) (g : WO S T → ℂ), (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) (c • g) =
      ‖c‖ₑ * (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g := GlobalTheory.Size.SupWord.supN_smul
  refine ⟨fun k f hf => ?_, fun τ z => ⟨fun U f hf => GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ hf τ z, ?_⟩,
    fun k f g c hf hg => ⟨GlobalTheory.Size.SupWord.ws_add_le hψ hθ ha hf hg k, GlobalTheory.Size.SupWord.ws_smul hs k c f⟩⟩
  · refine GlobalTheory.Size.wordSum_ne_top_iff.2 fun l _ => ?_
    obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.Size.theta_word hψ hθ l hf)
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) (iSup_le fun w => ?_)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hC w)
  · refine ⟨Real.toNNReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)), fun k f hf => ?_⟩
    exact GlobalTheory.Size.SupWord.ws_dRho_le hψ hθ ha hs hf τ z k

end GlobalTheory.Unf.SupFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D), (∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k f ≠ ⊤) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), (∀ U : AddSubgroup (WO S T), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, dRho (heisO ψ S T) θ τ z f ∈ GlobalTheory.Size.thetaLevel ψ S T U) ∧ ∃ C : ℝ≥0, ∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k (dRho (heisO ψ S T) θ τ z f) ≤ C * supSob ψ θ (k + 1) f) ∧ ∀ k (f g : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → supSob ψ θ k (f + g) ≤ supSob ψ θ k f + supSob ψ θ k g ∧ supSob ψ θ k (c • f) = ‖c‖ₑ * supSob ψ θ k f := by
  first | exact @GlobalTheory.Unf.SupFin.supSob_laws | exact GlobalTheory.Unf.SupFin.supSob_laws | (intros; apply GlobalTheory.Unf.SupFin.supSob_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.RapidDecay.cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay :=
  GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.T.cuspidal_moderateGrowth_rapidDecay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_forms_rapid_decay : GlobalTheory.Published.CuspRapidDecay := by
  first | exact @GlobalTheory.RapidDecay.cuspRapidDecay | exact GlobalTheory.RapidDecay.cuspRapidDecay | (intros; apply GlobalTheory.RapidDecay.cuspRapidDecay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.CommIntBdd

theorem om_integral_comm_dom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (m : Measure U) [SFinite m] (F : U → WO S T → ℂ) (p : GA D S × GA D T) (β : U → ℝ), (∀ u, IsThetaFunO ψ S T (F u)) → Continuous (Function.uncurry F) → Continuous (fun q : U × WO S T => om p (F q.1) q.2) → Integrable β m → (∀ u w, ‖F u w‖ ≤ β u ∧ ‖om p (F u) w‖ ≤ β u) → IsThetaFunO ψ S T (fun w => ∫ u, F u w ∂m) → ∀ w, om p (fun w' => ∫ u, F u w' ∂m) w = ∫ u, om p (F u) w ∂m := by
  intro D ψ S T χS χT om hom U _ _ _ _ m _ F p β hF hFc hOc hβ hdom hG w
  have hψ := hom.std
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.Size.exists_isCovolOne S T
  haveI hfin : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  set G : WO S T → ℂ := fun w => ∫ u, F u w ∂m with hGdef
  set H : WO S T → ℂ := fun w => ∫ u, om p (F u) w ∂m with hHdef
  have hHc : Continuous H := by
    refine continuous_of_dominated (bound := β) (fun x => ?_) (fun x => ?_) hβ ?_
    · exact (hOc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => (hdom u x).2
    · exact Filter.Eventually.of_forall fun u => hOc.comp (continuous_const.prodMk continuous_id)
  have hHb : ∀ x, ‖H x‖ ≤ ∫ u, β u ∂m := fun x =>
    norm_integral_le_of_norm_le hβ (Filter.Eventually.of_forall fun u => (hdom u x).2)
  have hOG := hom.om_pres p _ hG
  set q : WO S T → ℂ := fun x => om p G x - H x with hqdef
  have hq : q = 0 := by
    refine GlobalTheory.T.eq_zero_of_orthogonal_all_thetaFunctions D ψ hψ S T μ 𝓕 hμ h𝓕 q (hOG.cont.sub hHc) ?_ ?_
    · intro γ x
      have e1 := hOG.quasi γ x
      have e2 : H (ratW T S γ + x) = ψ (-(symplOH S T (ratW T S γ) x)) * H x := by
        simp only [hHdef]
        rw [← integral_const_mul]
        congr 1
        funext u
        exact (hom.om_pres p _ (hF u)).quasi γ x
      simp only [hqdef]
      rw [e1, e2]
      ring
    · intro f hf

      haveI : SecondCountableTopology (WO S T) := i3
      obtain ⟨CG, hCG⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hOG
      have hf0 := hom.om_pres p⁻¹ f hf
      have hff0 : om p (om p⁻¹ f) = f := by
        change (om p * om p⁻¹) f = f
        rw [← map_mul, mul_inv_cancel, map_one]; rfl
      set f0 := om p⁻¹ f with hf0def
      obtain ⟨C0, hC0⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf0
      obtain ⟨Cf, hCf⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf
      have hint : ∀ (g h : WO S T → ℂ) (a b : ℝ), Continuous g → Continuous h → (∀ x, ‖g x‖ ≤ a) →
          (∀ x, ‖h x‖ ≤ b) → Integrable (fun x => g x * star (h x)) (μ.restrict 𝓕) := by
        intro g h a b hg hh ha hb
        refine Integrable.mono' (integrable_const (a * b)) (hg.mul hh.star).aestronglyMeasurable
          (ae_of_all _ fun x => ?_)
        rw [norm_mul, norm_star]
        exact mul_le_mul (ha x) (hb x) (norm_nonneg _) ((norm_nonneg _).trans (ha x))
      have hprod : ∀ (K : U → WO S T → ℂ) (h : WO S T → ℂ) (b : ℝ), Continuous (fun z : U × WO S T => K z.1 z.2) →
          (∀ u x, ‖K u x‖ ≤ β u) → Continuous h → (∀ x, ‖h x‖ ≤ b) →
          Integrable (Function.uncurry fun x u => K u x * star (h x)) ((μ.restrict 𝓕).prod m) := by
        intro K h b hK hKb hh hb
        refine Integrable.mono' (((integrable_const b).mul_prod hβ)) ?_ (ae_of_all _ fun z => ?_)
        · exact ((hK.comp (continuous_snd.prodMk continuous_fst)).mul (hh.comp continuous_fst).star).aestronglyMeasurable
        · show ‖K z.2 z.1 * star (h z.1)‖ ≤ b * β z.2
          rw [norm_mul, norm_star, mul_comm b]
          exact mul_le_mul (hKb z.2 z.1) (hb z.1) (norm_nonneg _) ((norm_nonneg _).trans (hKb z.2 z.1))
      have hsc := fun g g' (hg : IsThetaFunO ψ S T g) (hg' : IsThetaFunO ψ S T g') =>
        GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om p) (hom.om_pres p) (hom.om_unit μ 𝓕 hμ h𝓕 p) g g' hg hg'
      have A : ∫ x in 𝓕, om p G x * star (f x) ∂μ = ∫ x in 𝓕, G x * star (f0 x) ∂μ := by
        rw [← hff0]; exact hsc G f0 hG hf0
      have B : ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
        calc ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, ∫ u, F u x * star (f0 x) ∂m ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show (∫ u, F u x ∂m) * star (f0 x) = ∫ u, F u x * star (f0 x) ∂m
              rw [integral_mul_const]
          _ = ∫ u, ∫ x in 𝓕, F u x * star (f0 x) ∂μ ∂m :=
              integral_integral_swap (hprod F f0 C0 hFc (fun u x => (hdom u x).1) hf0.cont hC0)
          _ = ∫ u, ∫ x in 𝓕, om p (F u) x * star (f x) ∂μ ∂m := by
              refine integral_congr_ae (ae_of_all _ fun u => ?_)
              rw [← hff0]; exact (hsc (F u) f0 (hF u) hf0).symm
          _ = ∫ x in 𝓕, ∫ u, om p (F u) x * star (f x) ∂m ∂μ :=
              (integral_integral_swap (hprod (fun u => om p (F u)) f Cf hOc (fun u x => (hdom u x).2) hf.cont hCf)).symm
          _ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show ∫ u, om p (F u) x * star (f x) ∂m = (∫ u, om p (F u) x ∂m) * star (f x)
              rw [integral_mul_const]
      have i1 := hint (om p G) f CG Cf hOG.cont hf.cont hCG hCf
      have i2 := hint H f (∫ u, β u ∂m) Cf hHc hf.cont hHb hCf
      simp only [hqdef, sub_mul]
      rw [integral_sub i1 i2, A, B, sub_self]
  have := congrFun hq w
  simp only [hqdef, Pi.zero_apply, sub_eq_zero] at this
  exact this

theorem om_integral_comm_bdd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Ω : Type) [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] (m : Measure Ω) [IsFiniteMeasure m] (F : Ω → WO S T → ℂ) (p : GA D S × GA D T), (∀ a, IsThetaFunO ψ S T (F a)) → (Continuous fun q : Ω × WO S T => F q.1 q.2) → (∃ C : ℝ, ∀ a x, ‖F a x‖ ≤ C) → (Continuous fun q : Ω × WO S T => om p (F q.1) q.2) → (∃ C : ℝ, ∀ a x, ‖om p (F a) x‖ ≤ C) → IsThetaFunO ψ S T (fun x => ∫ a, F a x ∂m) → ∀ x, om p (fun y => ∫ a, F a y ∂m) x = ∫ a, om p (F a) x ∂m := by
  intro D ψ S T χS χT om hom Ω _ _ _ _ m _ F p hF hFc hFb hOc hOb hG x
  obtain ⟨C1, hC1⟩ := hFb
  obtain ⟨C2, hC2⟩ := hOb
  exact om_integral_comm_dom D ψ S T χS χT om hom Ω m F p (fun _ => max C1 C2) hF hFc hOc
    (integrable_const _) (fun a w => ⟨(hC1 a w).trans (le_max_left _ _), (hC2 a w).trans (le_max_right _ _)⟩) hG x

end GlobalTheory.CommIntBdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Ω : Type) [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] (m : Measure Ω) [IsFiniteMeasure m] (F : Ω → WO S T → ℂ) (p : GA D S × GA D T), (∀ a, IsThetaFunO ψ S T (F a)) → (Continuous fun q : Ω × WO S T => F q.1 q.2) → (∃ C : ℝ, ∀ a x, ‖F a x‖ ≤ C) → (Continuous fun q : Ω × WO S T => om p (F q.1) q.2) → (∃ C : ℝ, ∀ a x, ‖om p (F a) x‖ ≤ C) → IsThetaFunO ψ S T (fun x => ∫ a, F a x ∂m) → ∀ x, om p (fun y => ∫ a, F a y ∂m) x = ∫ a, om p (F a) x ∂m := by
  first | exact @GlobalTheory.CommIntBdd.om_integral_comm_bdd | exact GlobalTheory.CommIntBdd.om_integral_comm_bdd | (intros; apply GlobalTheory.CommIntBdd.om_integral_comm_bdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Pointwise

noncomputable section

namespace GlobalTheory.MajSum

variable {D : D7}

theorem realSize_add_le (θ : InfFam D) {m n : ℕ} (x y : Mx D m n) :
    realSize θ (x + y) ≤ realSize θ x + realSize θ y := by
  unfold realSize
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have : Formalism.IndefR.Datum.compAt θ τ (x + y) i j =
      Formalism.IndefR.Datum.compAt θ τ x i j + Formalism.IndefR.Datum.compAt θ τ y i j := by
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add (infPart D), RingHom.map_add (θ τ)]
  rw [this]
  exact norm_add_le _ _

theorem maj_le_shift (θ : InfFam D) {m n : ℕ} (K C : Set (Mx D m n)) (N : ℕ) (γ w : Mx D m n)
    (hwC : w ∈ C) (hw : realSize θ w ≤ 1) :
    maj θ K N γ ≤ 2 ^ N * maj θ (K + C) N (γ + w) := by
  unfold maj
  by_cases hγ : InBox K γ
  · have hbox : InBox (K + C) (γ + w) := by
      obtain ⟨k, hk, hk0⟩ := hγ
      refine ⟨k + w, Set.add_mem_add hk hwC, ?_⟩
      have : γ + w - (k + w) = γ - k := by abel
      rw [this]; exact hk0
    rw [if_pos hγ, if_pos hbox]
    have h0 := realSize_nonneg θ γ
    have h1 := realSize_nonneg θ (γ + w)
    have h2 : 1 + realSize θ (γ + w) ≤ 2 * (1 + realSize θ γ) := by
      have := realSize_add_le θ γ w; linarith
    have hp : (0:ℝ) < (1 + realSize θ (γ + w)) ^ N := by positivity
    have hq : (0:ℝ) < (1 + realSize θ γ) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]
    calc (1 + realSize θ (γ + w)) ^ N ≤ (2 * (1 + realSize θ γ)) ^ N := by gcongr
      _ = 2 ^ N * (1 + realSize θ γ) ^ N := by rw [mul_pow]
  · rw [if_neg hγ]
    have := maj_nonneg θ (K + C) N (γ + w)
    unfold maj at this
    positivity

end GlobalTheory.MajSum

namespace GlobalTheory.MajSum

theorem realSize_zero {D : D7} (θ : InfFam D) {m n : ℕ} : realSize θ (0 : Mx D m n) = 0 := by
  have h : ∀ τ (i : Fin m) (j : Fin n), Formalism.IndefR.Datum.compAt θ τ (0 : Mx D m n) i j = 0 := by
    intro τ i j
    show θ τ (infPart D 0) = 0
    rw [RingHom.map_zero (infPart D), RingHom.map_zero (θ τ)]
  unfold realSize
  simp only [h, norm_zero, Finset.sum_const_zero]


set_option synthInstance.maxHeartbeats 400000 in
theorem tsum_maj_ne_top : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K →
    (∑' y : ratMx D m n, ENNReal.ofReal (maj θ K N y)) ≠ ⊤ := by
  intro D θ hθ m n
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let μ : Measure (Mx D m n) := Measure.addHaar
  have hcont : Continuous (realSize θ : Mx D m n → ℝ) :=
    ((GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ).1 m n ∅ isCompact_empty).2.1
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_majorant_coordinate_coset_measure D θ hθ m n (fun _ _ => True) 0 μ inferInstance
    (Filter.Eventually.of_forall fun x i j h => (h trivial).elim)
    (fun t _ => by
      have e : (fun x : Mx D m n => x + t) = fun x => t + x := funext fun x => add_comm x t
      rw [e]; exact map_add_left_eq_self μ t)
  refine ⟨N, fun K hK => ?_⟩

  obtain ⟨U, hUo, hU⟩ : ∃ U : Set (Mx D m n), IsOpen U ∧ ∀ γ ∈ ratMx D m n, γ ∈ U ↔ γ = 0 := by
    have h0 : IsOpen ({0} : Set (ratMx D m n)) := @isOpen_discrete (ratMx D m n) _ i5 _
    obtain ⟨U, hUo, hUe⟩ := isOpen_induced_iff.mp h0
    refine ⟨U, hUo, fun γ hγ => ?_⟩
    have := Set.ext_iff.mp hUe ⟨γ, hγ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    rw [this]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h0U : (0 : Mx D m n) ∈ U := (hU 0 (zero_mem _)).2 rfl
  have hsub : {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} ∈ nhds ((0 : Mx D m n), (0 : Mx D m n)) := by
    have hc : Continuous fun p : Mx D m n × Mx D m n => p.1 - p.2 := continuous_fst.sub continuous_snd
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hUo.mem_nhds h0U
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hsub
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (0 : Mx D m n)
  have hR : {w : Mx D m n | realSize θ w < 1} ∈ nhds (0 : Mx D m n) := by
    refine (isOpen_lt hcont continuous_const).mem_nhds ?_
    show realSize θ (0 : Mx D m n) < 1
    rw [realSize_zero]; exact one_pos
  set W := interior (A ∩ B ∩ C ∩ {w : Mx D m n | realSize θ w < 1}) with hWdef
  have hW0 : (0 : Mx D m n) ∈ W :=
    mem_interior_iff_mem_nhds.2 (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hA hB) hC) hR)
  have hμW : μ W ≠ 0 := (isOpen_interior.measure_pos μ ⟨0, hW0⟩).ne'

  let s : ratMx D m n → Set (Mx D m n) := fun γ => (fun x => -(γ : Mx D m n) + x) ⁻¹' W
  have hs : ∀ γ, MeasurableSet (s γ) := fun γ =>
    (isOpen_interior.preimage (continuous_const.add continuous_id)).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro γ γ' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    have hxA : -(γ : Mx D m n) + x ∈ A := (interior_subset hx).1.1.1
    have hxB : -(γ' : Mx D m n) + x ∈ B := (interior_subset hx').1.1.2
    have hmem : (-(γ : Mx D m n) + x, -(γ' : Mx D m n) + x) ∈ {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} :=
      hAB ⟨hxA, hxB⟩
    simp only [Set.mem_setOf_eq] at hmem
    have e : -(γ : Mx D m n) + x - (-(γ' : Mx D m n) + x) = (γ' : Mx D m n) - γ := by abel
    rw [e] at hmem
    have := (hU _ (sub_mem γ'.2 γ.2)).1 hmem
    exact Subtype.ext (sub_eq_zero.1 this).symm
  set K' := K + C
  have hK' : IsCompact K' := hK.add hCc
  have hfin : ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ < ⊤ := (hN K' hK').lintegral_lt_top
  have key : ∀ γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ) * μ W ≤
      2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := by
    intro γ
    calc ENNReal.ofReal (maj θ K N γ) * μ W = ∫⁻ _x in s γ, ENNReal.ofReal (maj θ K N γ) ∂μ := by
          rw [setLIntegral_const]
          congr 1
          exact (measure_preimage_add μ (-(γ : Mx D m n)) W).symm
      _ ≤ ∫⁻ x in s γ, 2 ^ N * ENNReal.ofReal (maj θ K' N x) ∂μ := by
          refine setLIntegral_mono' (hs γ) fun x hx => ?_
          have hw := interior_subset hx
          have h1 := maj_le_shift θ K C N (γ : Mx D m n) (-(γ : Mx D m n) + x) hw.1.2 (le_of_lt hw.2)
          rw [add_neg_cancel_left] at h1
          calc ENNReal.ofReal (maj θ K N γ) ≤ ENNReal.ofReal (2 ^ N * maj θ K' N x) :=
                ENNReal.ofReal_le_ofReal h1
            _ = 2 ^ N * ENNReal.ofReal (maj θ K' N x) := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      _ = 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hsum : (∑' γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ)) * μ W ≤
      2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ := by
    rw [← ENNReal.tsum_mul_right]
    calc _ ≤ ∑' γ : ratMx D m n, 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ :=
          ENNReal.tsum_le_tsum key
      _ = 2 ^ N * ∑' γ : ratMx D m n, ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := ENNReal.tsum_mul_left
      _ = 2 ^ N * ∫⁻ x in ⋃ γ, s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := by rw [lintegral_iUnion hs hdisj]
      _ ≤ 2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ := by
          gcongr; exact Measure.restrict_le_self
  intro htop
  rw [htop, ENNReal.top_mul hμW] at hsum
  exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hfin).ne (top_le_iff.1 hsum)

end GlobalTheory.MajSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTopStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_adelicMatrixSchwartzMajorant_rational_ne_top : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K → (∑' y : ratMx D m n, ENNReal.ofReal (maj θ K N y)) ≠ ⊤ := by
  first | exact @GlobalTheory.MajSum.tsum_maj_ne_top | exact GlobalTheory.MajSum.tsum_maj_ne_top | (intros; apply GlobalTheory.MajSum.tsum_maj_ne_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGoodCompatThree
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.StdPos

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix

section Pure

variable {R : Type} [CommRing R] (s : R →+* R) {n r m : ℕ} (J : Matrix (Fin n) (Fin n) R)

end Pure

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n r m : ℕ}
  (J : Matrix (Fin n) (Fin n) E)







end Lattice

end GlobalTheory.RegSch.StdPos

namespace GlobalTheory.RegSch

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix StdPos

theorem exists_good_frameLat (D : D7) (V : HSp D) : ∃ a, Lvl.Good (⟨frameLat V, a⟩ : Lvl V) :=
  (exists_isMaj V).imp fun _ h => ⟨isLattice_frameLat_host V, SelfDual.isSelfDualAt_frameLat D V, h⟩

end GlobalTheory.RegSch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSelfDualLatticeAtPlaceIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSelfDualLatticeAtPlaceIntegral
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IwaPlace.SDBound

variable {D : D7}

theorem exists_nat_mul_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

theorem exists_nat_mul_isIntegral_fin {n : ℕ} (z : Fin n → Fin n → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ l k, IsIntegral ℤ ((d : D.host.E) * z l k) := by
  classical
  choose c hc hi using fun p : Fin n × Fin n => exists_nat_mul_isIntegral (z p.1 p.2)
  refine ⟨∏ p, c p, Finset.prod_pos fun p _ => hc p, fun l k => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ c (Finset.mem_univ (l, k)), Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi (l, k))
  rw [← Int.cast_natCast]
  exact isIntegral_algebraMap (R := ℤ)

theorem finPart_incA_mem {o : D.host.E} (ho : IsIntegral ℤ o) : finPart D (incA D o) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, ⟨o, ho⟩, rfl⟩

theorem hermAt_single (S : HSp D) (y : Fin S.rank → AE D) (k : Fin S.rank) (a : AE D) :
    hermAt S y (Pi.single k a) = cA D a * (gA S *ᵥ y) k := by
  unfold hermAt
  rw [Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, RingHom.map_zero]
    simp only [zero_mul, Finset.sum_const_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

theorem exists_mul_mem_intAt : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ →
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Λ, ∀ i, (N : AE D) * y i ∈ intAt D (· = v) := by
  intro D S v Λ ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨ε, hc, hε, hact⟩ := LocSD.exists_idem v
  obtain ⟨d, hd, hint⟩ := exists_nat_mul_isIntegral_fin (fun l k => (S.gram)⁻¹ l k)
  refine ⟨d * m, Nat.mul_pos hd hm, fun y hy l => ⟨Ideal.mul_mem_left _ _ (hsupp y hy l), ?_⟩⟩
  have key : ∀ k, finPart D ((m : AE D) * (gA S *ᵥ y) k) ∈ intAE D := fun k => by
    have hx : (m : AE D) • (Pi.single k ε : Fin S.rank → AE D) ∈ Λ := by
      refine hmul _ fun i => ?_
      by_cases hi : i = k
      · rw [hi, Pi.single_eq_same]; exact hε
      · rw [Pi.single_eq_of_ne hi]; exact ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
    have h1 := (((hdual y (hsupp y hy)).1 hy) _ hx).2
    rwa [← Pi.single_smul', smul_eq_mul, hermAt_single, RingHom.map_mul (cA D), map_natCast, hc, mul_assoc,
      hact _ (mulVec_mem_idAt _ (hsupp y hy) k)] at h1
  have e1 : y l = ∑ k, incA D ((S.gram)⁻¹ l k) * (gA S *ᵥ y) k := by
    have : giA S *ᵥ (gA S *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, giA_mul_gA, Matrix.one_mulVec]
    exact (congrFun this l).symm
  have e2 : ((d * m : ℕ) : AE D) * y l =
      ∑ k, incA D ((d : D.host.E) * (S.gram)⁻¹ l k) * ((m : AE D) * (gA S *ᵥ y) k) := by
    rw [e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.map_mul, map_natCast, Nat.cast_mul]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_sum]
  refine sum_mem fun k _ => ?_
  rw [RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (finPart_incA_mem (hint l k)) (key k)

end GlobalTheory.IwaPlace.SDBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSelfDualLatticeAtPlaceIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_mul_selfDualLatticeAtPlace_integral : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ → ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Λ, ∀ i, (N : AE D) * y i ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.IwaPlace.SDBound.exists_mul_mem_intAt | exact GlobalTheory.IwaPlace.SDBound.exists_mul_mem_intAt | (intros; apply GlobalTheory.IwaPlace.SDBound.exists_mul_mem_intAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLawStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMaps_heisenbergTranslation_law : ∀ D : D7, GlobalTheory.FinPl.FlatShift D := by
  first | exact @GlobalTheory.FlatShiftPf.flatShift | exact GlobalTheory.FlatShiftPf.flatShift | (intros; apply GlobalTheory.FlatShiftPf.flatShift <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualLatticeCosetIndicatorIsSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualLatticeCosetIndicatorIsSchwartzBruhat
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetSB

theorem cosetInd_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    (f : Module.Dual 𝓀[k] (Red L)), cosetInd q L f ∈ SB (n → k) := by
  intro k _ _ _ _ n _ _ q L _ f
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  by_cases hex : ∃ F : n → k, Lifts L F f
  · obtain ⟨F, hF⟩ := hex
    have e : cosetInd q L f = fun η => dualInd L (η - q.inv • F) := by
      funext η
      rw [← GlobalTheory.FinPl.CosetPairing.cosetInd_add q hF (η - q.inv • F), sub_add_cancel]
    rw [e]
    exact GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.Comm.dualInd_mem L) (s := fun η => η + q.inv • F)
      (by fun_prop) (by fun_prop) fun η => sub_add_cancel η _
  · have e : cosetInd q L f = 0 := by
      classical
      funext η
      unfold cosetInd
      rw [ite_eq_right fun ⟨F, hF, _⟩ => hex ⟨F, hF⟩]
      rfl
    rw [e]
    exact (SB (n → k)).zero_mem

end GlobalTheory.FinPl.CosetSB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualLatticeCosetIndicatorIsSchwartzBruhatStatement
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] (f : Module.Dual 𝓀[k] (Red L)), cosetInd q L f ∈ SB (n → k) := by
  first | exact @GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB | exact GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB | (intros; apply GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableSchwartzMajorantPullbackUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableSchwartzMajorantPullbackUnitriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
namespace GlobalTheory.Unf

theorem pull_integrable : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m ρ : ℕ) (vU : VolU D ρ) (x : Matrix (Fin m) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∃ N : ℕ, ∀ K : Set (Mx D m ρ), IsCompact K → Integrable (fun u : UX D ρ => maj θ K N ((rat x : Mx D m ρ) ⬝ u.1.1)) vU.ν := by
  intro D θ hθ m ρ vU x hx
  have hH : vU.ν.IsHaarMeasure := vU.unit.1
  obtain ⟨hf, hfin, hinv⟩ := GlobalTheory.T.haar_adelicUpperUnitriangular_entry_translate_invariant D ρ vU.ν hH
  have hae : ∀ᵐ y ∂(Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) vU.ν), ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j := by
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
    have hS : MeasurableSet {y : Mx D ρ ρ | ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j} := by
      have hc : IsClosed {y : Mx D ρ ρ | ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j} := by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
          isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
      exact hc.measurableSet
    rw [ae_map_iff hf.aemeasurable hS]
    refine ae_of_all _ fun u i j hij => ?_
    have hU := (GlobalTheory.UniIndexPrime.mem_uniSub u.1).1 u.2
    rcases lt_or_eq_of_le (not_lt.1 hij) with h | h
    · rw [Matrix.one_apply_ne h.ne']
      exact hU.1 i j h
    · subst h
      rw [Matrix.one_apply_eq]
      exact hU.2 _
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_majorant_coordinate_coset_measure D θ hθ ρ ρ (fun i j => i < j) 1 _ hfin hae hinv
  obtain ⟨hmaj, hmove⟩ := GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ
  refine ⟨N, fun K hK => ?_⟩
  obtain ⟨K', hK', hb⟩ := hmove m ρ ρ x hx K hK
  obtain ⟨C, hC⟩ := hb N
  have h1 : Integrable (maj θ K' N) (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) vU.ν) := hN K' hK'
  have h2 : Integrable (fun u : UX D ρ => maj θ K' N (u.1.1 : Mx D ρ ρ)) vU.ν :=
    (integrable_map_measure ((hmaj ρ ρ K' hK').2.2.1 N).aestronglyMeasurable hf.aemeasurable).1 h1
  have hmul : Measurable (fun y : Mx D ρ ρ => (rat x : Mx D m ρ) ⬝ y) := by
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : BorelSpace (Mx D m ρ) := ⟨rfl⟩
    exact (continuous_const.matrix_mul continuous_id).measurable
  refine (h2.const_mul C).mono' (((hmaj m ρ K hK).2.2.1 N).comp (hmul.comp hf)).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (maj_nonneg θ K N _)]
  exact hC _

end GlobalTheory.Unf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableSchwartzMajorantPullbackUnitriangularStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_schwartzMajorant_pullback_unitriangular : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m ρ : ℕ) (vU : VolU D ρ) (x : Matrix (Fin m) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∃ N : ℕ, ∀ K : Set (Mx D m ρ), IsCompact K → Integrable (fun u : UX D ρ => maj θ K N ((rat x : Mx D m ρ) ⬝ u.1.1)) vU.ν := by
  first | exact @GlobalTheory.Unf.pull_integrable | exact GlobalTheory.Unf.pull_integrable | (intros; apply GlobalTheory.Unf.pull_integrable <;> assumption)
end
end
