module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRestrictedProductTupleMeasureMapLeftRightActio
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreMeasureInvariantOrbitFiniteNonz
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreMeasureInvariantOrbitFiniteNonz
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.StdProp

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_sigR [TopologicalSpace R] [IsTopologicalRing R] : Continuous (sigR R σ) := by
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  exact this

theorem continuous_qR [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 := continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem measurableSet_fibre [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [SecondCountableTopology R] (c : R) :
    MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E | qR R σ J (X 0) = c} :=
  (isClosed_eq (continuous_qR R σ J) continuous_const).measurableSet

omit [FiniteDimensional F E] in
theorem smul_eq_lrAct {n : ℕ} (g : HA R σ J) :
    (fun X : Fin n → Fin M → R ⊗[F] E => g • X) = lrAct (HA.mat R σ J g).val 1 := by
  funext X a
  show (HA.mat R σ J g).val.mulVec (X a) = _
  simp [lrAct, Matrix.one_apply]

end Local

theorem stdX_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → IsStdX s σ J β ν → ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 ∧ IsInvTup (AF F) σ J ν ∧ OnOrbit (AF F) σ J x ν ∧ IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM d b s M J x β ν hJ hβ hx ⟨mi, mv, hi, hv, hP⟩
  obtain ⟨nI, nV⟩ := nice_ainf_fv F
  obtain ⟨qloc, gloc⟩ := q_and_unitary_local_components F E σ M J
  have hβu : IsUnit β := Ne.isUnit hβ
  have bI := GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ (Ainf F) nI M J _ _ _ mi s.haar_nuI (hβu.map _) hi
  have bV := fun v => GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ (Fv F v) (nV v) M J _ _ _ (mv v) (s.haar_nuV v)
    (hβu.map _) (hv v)
  have pI := GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Ainf F) nI M J x β _ _ mi hJ hβ hx s.haar_lamI s.haar_nuI hi
  have pV := fun v => GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Fv F v) (nV v) M J x β _ _ (mv v) hJ hβ hx
    (s.haar_lamV v) (s.haar_nuV v) (hv v)
  obtain ⟨hfin, hne, huniq, hsupp⟩ := GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 M ν mi mv hP
  have h1 : ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 := by
    have := hsupp {X | qR (Ainf F) σ J (X 0) = algebraMap F _ β}
      (fun v => {X | qR (Fv F v) σ J (X 0) = algebraMap F _ β})
      (measurableSet_fibre _ σ J _) (fun v => measurableSet_fibre _ σ J _) bI.1 (fun v => (bV v).1)
    refine measure_mono_null (fun X hX => ?_) this
    exact fun h => hX ((qloc (X 0) β).2 h)
  refine ⟨h1, ?_, ?_, hfin, hne pI.2.2 fun v => (pV v).2.2⟩
  · intro g
    obtain ⟨⟨gi, hgi⟩, hgv⟩ := gloc g
    have hT := GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction F E d b 1 M ν mi mv (HA.mat (AF F) σ J g) 1 hP
    have e1 : mi.map (lrAct ((HA.mat (AF F) σ J g).val.map prInf)
        ((1 : GL (Fin 1) (AF F ⊗[F] E)).val.map prInf)) = mi := by
      rw [← hgi, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), ← smul_eq_lrAct]
      exact pI.1 gi
    have e2 : (fun v => (mv v).map (lrAct ((HA.mat (AF F) σ J g).val.map (prV v))
        ((1 : GL (Fin 1) (AF F ⊗[F] E)).val.map (prV v)))) = mv := by
      funext v
      obtain ⟨gv, hgv⟩ := hgv v
      rw [← hgv, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), ← smul_eq_lrAct]
      exact (pV v).1 gv
    rw [e1, e2, Units.val_one, ← smul_eq_lrAct] at hT
    exact huniq _ hT
  · refine measure_mono_null (fun X hX => ?_) h1
    exact fun h => hX (GlobalTheory.T.witt_theorem_adelic_one_vector F E σ hCM M J x β hJ hβ hx X h)

end GlobalTheory.GaugeEx.StdProp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreMeasureInvariantOrbitFiniteNonzStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → IsStdX s σ J β ν → ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 ∧ IsInvTup (AF F) σ J ν ∧ OnOrbit (AF F) σ J x ν ∧ IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 := by
  first | exact @GlobalTheory.GaugeEx.StdProp.stdX_props | exact GlobalTheory.GaugeEx.StdProp.stdX_props | (intros; apply GlobalTheory.GaugeEx.StdProp.stdX_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnOfCoord
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilTransport

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem integral_transport {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalAddGroup X] [IsTopologicalAddGroup Y] [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (E : X ≃+ Y) (hc : Continuous E) (hc' : Continuous E.symm) (LX : AddSubgroup X) (LY : AddSubgroup Y)
    (hL : ∀ x, x ∈ LX ↔ E x ∈ LY) {f g : Y → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ (μ : Measure X) (𝓕 : Set X), μ.IsAddHaarMeasure → IsAddFundamentalDomain LX 𝓕 μ →
      ∫⁻ w in 𝓕, ‖f (E w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖g (E w)‖ₑ ^ 2 ∂μ)
    (μ : Measure Y) (𝓕 : Set Y) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain LY 𝓕 μ) :
    ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖g w‖ ^ 2 ∂μ := by
  let M : X ≃ᵐ Y := (⟨E.toEquiv, hc, hc'⟩ : X ≃ₜ Y).toMeasurableEquiv
  have hM : MeasurePreserving M (μ.map E.symm) μ :=
    (⟨M.symm.measurable, rfl⟩ : MeasurePreserving M.symm μ (μ.map E.symm)).symm M.symm
  have h1 : (μ.map E.symm).IsAddHaarMeasure := E.symm.isAddHaarMeasure_map μ hc' hc
  have h2 : IsAddFundamentalDomain LX (M ⁻¹' 𝓕) (μ.map E.symm) := by
    refine h𝓕.preimage_of_equiv hM.quasiMeasurePreserving
      (e := fun y : LY => (⟨E.symm y, (hL _).2 (by simp)⟩ : LX)) ⟨fun a b hab => ?_, fun x => ?_⟩ fun y x => ?_
    · exact Subtype.ext (E.symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨E x, (hL _).1 x.2⟩, Subtype.ext (E.symm_apply_apply _)⟩
    · show E (E.symm y + x) = y + E x
      simp
  have key : ∀ k : Y → ℂ, Continuous k →
      ∫ w in 𝓕, ‖k w‖ ^ 2 ∂μ = (∫⁻ w in M ⁻¹' 𝓕, ‖k (E w)‖ₑ ^ 2 ∂(μ.map E.symm)).toReal := fun k hk => by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖k w‖ ^ 2) (Filter.Eventually.of_forall fun w => by positivity)
      (hk.norm.pow 2).measurable.aestronglyMeasurable]
    congr 1
    rw [← hM.setLIntegral_comp_preimage_emb M.measurableEmbedding (fun w => ENNReal.ofReal (‖k w‖ ^ 2)) 𝓕]
    refine lintegral_congr fun w => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rfl
  rw [key f hf, key g hg, h _ _ h1 h2]

structure IsCoord (S T V W : HSp D) (E : WO S T ≃+ WA V W) : Prop where
  cont : Continuous E
  cont' : Continuous E.symm
  sympl : ∀ x y, symplOH S T x y = symplH V W (E x) (E y)
  rat : ∀ x, x ∈ ratL T S ↔ E x ∈ ratL V W
  inf : ∀ x : WO S T, x.map (infPart D) = 0 ↔ (E x).map (infPart D) = 0
  fin : ∀ x : WO S T, x.map (finPart D) = 0 ↔ (E x).map (finPart D) = 0
  part : ∀ (a : AE D) (x : WO S T), (∀ i j, a * x i j = x i j) → ∀ i j, a * E x i j = E x i j

namespace IsCoord

variable {S T V W : HSp D} {E : WO S T ≃+ WA V W} (hE : IsCoord S T V W E) (ψ : AddChar (AF D.host.F) ℂ)

include hE

theorem heis_comp (u : WO S T) (f : WA V W → ℂ) : Heisenberg₂ ψ V W (E u) f ∘ E = heisO ψ S T u (f ∘ E) := by
  funext w
  simp only [Function.comp_apply, Heisenberg₂, heisO, hE.sympl, map_add (f := _)]

theorem theta_iff (f : WA V W → ℂ) : IsThetaFunO ψ S T (f ∘ E) ↔ IsThetaFun ψ V W f := by
  constructor
  · intro hf
    refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
    · obtain ⟨δ, hδ⟩ := (hE.rat (E.symm (ratW V W γ))).2 (by rw [E.apply_symm_apply]; exact ⟨γ, rfl⟩)
      have hδ' : ratW T S δ = E.symm (ratW V W γ) := hδ
      have := hf.quasi δ (E.symm w)
      simpa only [hδ', Function.comp_apply, map_add (f := _), hE.sympl, E.apply_symm_apply] using this
    · obtain ⟨U, hU, hfix⟩ := hf.level
      refine ⟨U.comap E.symm.toAddMonoidHom, hU.preimage hE.cont', fun u hu h0 => ?_⟩
      have := hfix (E.symm u) hu ((hE.inf _).2 (by rwa [E.apply_symm_apply]))
      rw [← hE.heis_comp, E.apply_symm_apply] at this
      exact E.surjective.injective_comp_right this
    · have := hf.cont.comp hE.cont'
      simpa only [Function.comp_def, E.apply_symm_apply] using this
    · have := hf.smooth k (E.symm.toAddMonoidHom.comp L) (hE.cont'.comp hL)
        (fun t => (hE.fin _).2 (by simpa using h0 t)) (E.symm w)
      simpa using this
  · intro hf
    refine ⟨fun γ w => ?_, ?_, hf.cont.comp hE.cont, fun k L hL h0 w => ?_⟩
    · obtain ⟨δ, hδ⟩ := (hE.rat (ratW T S γ)).1 ⟨γ, rfl⟩
      have hδ' : ratW V W δ = E (ratW T S γ) := hδ
      have := hf.quasi δ (E w)
      simpa only [hδ', Function.comp_apply, map_add (f := _), hE.sympl] using this
    · obtain ⟨U, hU, hfix⟩ := hf.level
      refine ⟨U.comap E.toAddMonoidHom, hU.preimage hE.cont, fun u hu h0 => ?_⟩
      rw [← hE.heis_comp, hfix (E u) hu ((hE.inf _).1 h0)]
    · have := hf.smooth k (E.toAddMonoidHom.comp L) (hE.cont.comp hL) (fun t => (hE.fin _).1 (h0 t)) (E w)
      simpa using this

end IsCoord

theorem exists_isWeilOn_of_coord {S T V W : HSp D} {E : WO S T ≃+ WA V W} (hE : IsCoord S T V W E)
    {ψ : AddChar (AF D.host.F) ℂ} {χS χT χ χ' : IdC D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (j : GA D V × GA D W →* GA D S × GA D T) (hj : Continuous j)
    (hact : ∀ g h x, E (actO S T (j (g, h)).1 (j (g, h)).2 x) = actHom V W g h (E x))
    (hrat : ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, (j (γ, γ')).1 ∈ GQ S ∧ (j (γ, γ')).2 ∈ GQ T)
    (hsp : ∀ e g h, SuppAt e V g → SuppAt e W h → ∀ x y, IsDetAt e V g x → IsDetAt e W h y →
      ∃ x' y', SuppAt e S (j (g, h)).1 ∧ SuppAt e T (j (g, h)).2 ∧ IsDetAt e S (j (g, h)).1 x' ∧
        IsDetAt e T (j (g, h)).2 y' ∧ splitFacO χS χT x' y' = splitFac V W χ χ' x y) :
    ∃ om', IsWeilOn ψ V W χ χ' om' := by
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  let P : (WA V W → ℂ) ≃ₗ[ℂ] (WO S T → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ E.toEquiv
  have hP : ∀ f, P f = f ∘ E := fun _ => rfl
  have hPs : ∀ f, P.symm f ∘ E = f := fun f => P.apply_symm_apply f
  have th : ∀ Φ : ThS ψ V W, IsThetaFunO ψ S T (Φ.1 ∘ E) := fun Φ => (hE.theta_iff ψ _).2 (mem_ThS.1 Φ.2)
  have th' : ∀ f, IsThetaFunO ψ S T f → P.symm f ∈ ThS ψ V W := fun f hf =>
    mem_ThS.2 ((hE.theta_iff ψ _).1 (by rwa [hPs]))
  have pres : ∀ p, ∀ f ∈ ThS ψ V W, P.symm.conj (om (j p)) f ∈ ThS ψ V W := fun p f hf =>
    th' _ (H.om_pres _ _ (th ⟨f, hf⟩))
  let om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W) :=
    { toFun := fun p => (P.symm.conj (om (j p))).restrict (pres p)
      map_one' := LinearMap.ext fun Φ => Subtype.ext (by
        show P.symm (om (j 1) (P Φ.1)) = Φ.1
        rw [map_one, map_one, Module.End.one_apply, P.symm_apply_apply])
      map_mul' := fun p q => LinearMap.ext fun Φ => Subtype.ext (by
        show P.symm (om (j (p * q)) (P Φ.1)) = P.symm (om (j p) (P (P.symm (om (j q) (P Φ.1)))))
        rw [map_mul, map_mul, Module.End.mul_apply, P.apply_symm_apply]) }
  have ho : ∀ p (Φ : ThS ψ V W), (om' p Φ).1 ∘ E = om (j p) (Φ.1 ∘ E) := fun p Φ => hPs _
  refine ⟨om', fun g h w₀ Φ Φ' e => ?_, fun γ hγ γ' hγ' Φ => ?_, fun Φ w => ?_, fun μ 𝓕 hμ h𝓕 p Φ => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩
  · obtain ⟨u, rfl⟩ := E.surjective w₀
    refine E.surjective.injective_comp_right ?_
    show (om' (g, h) Φ').1 ∘ E = Heisenberg₂ ψ V W (actHom V W g h (E u)) (om' (g, h) Φ).1 ∘ E
    rw [← hact, hE.heis_comp, ho, ho, e, hE.heis_comp]
    exact H.om_heis _ _ u _ (th Φ)
  · have h1 := congrFun (ho (γ, γ') Φ) 0
    have h2 := H.om_aut _ (hrat γ hγ γ' hγ').1 _ (hrat γ hγ γ' hγ').2 _ (th Φ)
    have h3 := h1.trans h2
    simpa only [Function.comp_apply, map_zero] using h3
  · obtain ⟨u, rfl⟩ := E.surjective w
    exact ((H.om_cont _ (th Φ) u).comp hj).congr fun p => (congrFun (ho p Φ) u).symm
  · refine @integral_transport (WO S T) (WA V W) _ _ _ _ _ _ (borel _) (borel _) (@BorelSpace.mk _ _ (borel _) rfl)
      (@BorelSpace.mk _ _ (borel _) rfl) E hE.cont hE.cont' (ratL T S) (ratL V W) hE.rat _ _
      (mem_ThS.1 (om' p Φ).2).cont (mem_ThS.1 Φ.2).cont (fun ν 𝓖 hν h𝓖 => ?_) μ 𝓕 hμ h𝓕
    have := H.om_unit ν 𝓖 hν h𝓖 (j p) _ (th Φ)
    rw [← ho] at this
    exact this
  · obtain ⟨x', y', k1, k2, k3, k4, k5⟩ := hsp e g h hg hh x y hx hy
    obtain ⟨r, hr, hℓ⟩ := H.om_split e he _ _ k1 k2 x' y' k3 k4
    refine ⟨r, hr, fun ℓ hinv Φ => ?_⟩
    obtain ⟨L, hL⟩ := LinearMap.exists_extend ℓ
    have hL' : ∀ Ψ : ThS ψ V W, L Ψ.1 = ℓ Ψ := fun Ψ => LinearMap.congr_fun hL Ψ
    have key := hℓ (L ∘ₗ P.symm.toLinearMap) (fun u hu f hf => ?_) _ (th Φ)
    · rw [k5] at key
      have e1 : L (P.symm (Φ.1 ∘ E)) = ℓ Φ := by rw [← hP, P.symm_apply_apply, hL']
      rw [← hL', ← e1]
      exact key
    · have e2 : P.symm (heisO ψ S T u f) = Heisenberg₂ ψ V W (E u) (P.symm f) := by
        rw [LinearEquiv.symm_apply_eq, hP, hE.heis_comp, hPs]
      have m1 := th' f hf
      have m2 : Heisenberg₂ ψ V W (E u) (P.symm f) ∈ ThS ψ V W :=
        mem_ThS.2 (GlobalTheory.Mem.ThetaClosed.isThetaFun_heis H.std (mem_ThS.1 m1) _)
      show L (P.symm (heisO ψ S T u f)) = L (P.symm f)
      rw [e2]
      exact (hL' ⟨_, m2⟩).trans ((hinv (E u) (hE.part _ u hu) ⟨_, m1⟩ ⟨_, m2⟩ rfl).trans (hL' ⟨_, m1⟩).symm)

theorem gram_mul_gramInv (V : HSp D) : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedSmall.gramInv_mul V)

def mulGramInv (S T : HSp D) : WO S T ≃+ WA T S where
  toFun x := HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) ((S.gram⁻¹).map (incA D))
  invFun x := HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (S.gram.map (incA D))
  left_inv x := by
    show x * _ * _ = x
    rw [Matrix.mul_assoc, GlobalTheory.OrientedSmall.gramInv_mul, Matrix.mul_one]
  right_inv x := by
    show x * _ * _ = x
    rw [Matrix.mul_assoc, gram_mul_gramInv, Matrix.mul_one]
  map_add' x y := Matrix.add_mul _ _ _

theorem map_mulGramInv {R : Type} [CommRing R] (φ : AE D →+* R) (S T : HSp D) (x : WO S T) :
    x.map φ = 0 ↔ (mulGramInv S T x).map φ = 0 := by
  constructor
  · intro h
    exact (Matrix.map_mul (f := φ)).trans (by rw [h, Matrix.zero_mul])
  · intro h
    rw [← (mulGramInv S T).symm_apply_apply x]
    exact (Matrix.map_mul (f := φ)).trans (by rw [h, Matrix.zero_mul])

theorem isCoord_large (S T : HSp D) (hr : S.rank < T.rank) : IsCoord S T T S (mulGramInv S T) := {
  cont := continuous_id.matrix_mul continuous_const
  cont' := continuous_id.matrix_mul continuous_const
  sympl x y := by
    rw [← GlobalTheory.WeilTieCheck.symplH_transpose T S hr.ne']
    unfold symplOH symplH
    rw [(GlobalTheory.OrientedSmall.bridgeSmall D S T hr.le).1]
    rfl
  rat x := by
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨γ * S.gram⁻¹, Matrix.map_mul (f := incA D)⟩
    · rintro ⟨γ, hγ⟩
      refine ⟨γ * S.gram, (Matrix.map_mul (f := incA D)).trans ?_⟩
      rw [← (mulGramInv S T).symm_apply_apply x, ← hγ]
      rfl
  inf := map_mulGramInv _ S T
  fin := map_mulGramInv _ S T
  part a x h i j := by
    show a * ∑ k, x i k * incA D (S.gram⁻¹ k j) = ∑ k, x i k * incA D (S.gram⁻¹ k j)
    simp only [Finset.mul_sum, ← mul_assoc, h] }

theorem isCoord_small (S T : HSp D) (hr : S.rank < T.rank) :
    IsCoord S T S T ((mulGramInv S T).trans (Matrix.transposeAddEquiv _ _ _)) := {
  cont := (isCoord_large S T hr).cont.matrix_transpose
  cont' := (isCoord_large S T hr).cont'.comp continuous_id.matrix_transpose
  sympl x y := ((isCoord_large S T hr).sympl x y).trans (GlobalTheory.WeilTieCheck.symplH_transpose T S hr.ne' _ _).symm
  rat x := ((isCoord_large S T hr).rat x).trans
    ⟨fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩, fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩⟩
  inf x := ((isCoord_large S T hr).inf x).trans
    ⟨fun h => congrArg Matrix.transpose h, fun h => congrArg Matrix.transpose h⟩
  fin x := ((isCoord_large S T hr).fin x).trans
    ⟨fun h => congrArg Matrix.transpose h, fun h => congrArg Matrix.transpose h⟩
  part a x h i j := (isCoord_large S T hr).part a x h j i }

theorem weilCoreEx_of_datum : ∀ D : D7, (∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : IdC D), IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ om, Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT om) → WeilCoreEx D := by
  intro D hO ψ hψ
  have key : ∀ (V W : HSp D) (χ χ' : IdC D), ∃ om, admitted V W χ χ' → IsWeilOn ψ V W χ χ' om := by
    intro V W χ χ'
    by_cases ha : admitted V W χ χ'
    swap
    · exact ⟨1, fun h => absurd h ha⟩
    obtain ⟨hne, h1, h2, h3, h4⟩ := ha
    suffices h : ∃ om, IsWeilOn ψ V W χ χ' om from h.imp fun _ h _ => h
    rcases lt_or_gt_of_ne hne with hr | hr
    · obtain ⟨om, H⟩ := hO ψ hψ V W χ χ' h1.1 h2.1 h3 h4
      refine exists_isWeilOn_of_coord (isCoord_small V W hr) H (MonoidHom.id _) continuous_id
        (fun g h x => (GlobalTheory.OrientedSmall.bridgeSmall D V W hr.le).2 g h x) (fun _ a _ b => ⟨a, b⟩)
        fun e g h hg hh x y hx hy => ⟨x, y, hg, hh, hx, hy, ?_⟩
      unfold splitFacO splitFac
      rw [if_pos hr.le]
    · obtain ⟨om, H⟩ := hO ψ hψ W V χ' χ h2.1 h1.1 h4 h3
      refine exists_isWeilOn_of_coord (isCoord_large W V hr) H ((MonoidHom.snd _ _).prod (MonoidHom.fst _ _)) continuous_swap
        (fun g h x => ?_) (fun _ a _ b => ⟨b, a⟩) fun e g h hg hh x y hx hy => ⟨y, x, hh, hg, hy, hx, ?_⟩
      · have e1 := (GlobalTheory.OrientedSmall.bridgeSmall D W V hr.le).2 h g x
        have e2 := actHom_swap V W hne g h (mulGramInv W V x)
        exact Matrix.transpose_injective (e1.trans e2)
      · unfold splitFacO splitFac
        rw [if_neg (not_le.2 hr), mul_comm]
  choose om hom using key
  exact ⟨⟨om, hom⟩⟩

end GlobalTheory.Mem.WeilTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardLevelMoveIncidenceOfPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardLevelMoveIncidenceOfPairs
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke

section
variable {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
  [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']

theorem mem_loc_map_equiv (res : R →+* k) (g : V ≃ₗ[R] V) (M : Submodule R V) (y : V) :
    y ∈ loc res (M.map (g : V →ₗ[R] V)) ↔ g.symm y ∈ loc res M := by
  rw [mem_loc, mem_loc]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [Submodule.mem_map_equiv, map_smul]

theorem act_pairOf_value (res : R →+* k) (g : V ≃ₗ[R] V) (M M' : Submodule R V) (pr : M →+ W) (pr' : M' →+ W')
    (φ : Module.Dual k W) (φ' : Module.Dual k W')
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z)
    (t : R) (z : M) (e : V) (he : t • e = z.1) (h1 : φ (pr z) = 1)
    (hm : e ∈ loc res (M'.map (g : V →ₗ[R] V)))
    (h : ∀ (x : M') (hx : t • g x.1 ∈ M), φ' (pr' x) = φ (pr ⟨_, hx⟩)) :
    ((pairOf res M' pr' φ').act g).f e = 1 := by
  rw [mem_loc_map_equiv] at hm
  obtain ⟨s, hs0, hx⟩ := (mem_loc _ _ _).1 hm
  have e1 : t • g (s • g.symm e) = (s • z : M).1 := by
    rw [map_smul, g.apply_symm_apply, smul_comm, he]; rfl
  have hx2 : t • g (s • g.symm e) ∈ M := by rw [e1]; exact (s • z).2
  have h2 := h ⟨_, hx⟩ hx2
  have e2 : (⟨_, hx2⟩ : M) = s • z := Subtype.ext e1
  rw [locExt_spec res M' pr' hs' _ hm s hx, map_smul, e2, hs, map_smul, h1] at h2
  show φ' (locExt res M' pr' (g.symm e)) = 1
  exact smul_right_injective k hs0 h2

end

set_option maxHeartbeats 1000000 in
theorem up_move_incidence : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (z : ↥(Ld D u i hi c)) (γ : GL (Fin (D.R.N i)) D.host.E), (D.fm u).fv i v c (P.pr v c z) = 1 → loc (A.res v) (mulLat γ.1 (clsCrd D u i hi c')) = loc (A.res v) (Ld D u i hi c) → loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (Ld D u i hi c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) → (∀ (x : ↥(Ld D u i hi c')) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1 *ᵥ x.1) ∈ Ld D u i hi c), (D.fm u).fv i v c' (P.pr v c' x) = (D.fm u).fv i v c (P.pr v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).IsKer (pc P v c).L ∧ ∃ e, ((pc P v c').act (glE γ)).f e = 1 ∧ locExt (A.res v) (Ld D u i hi c) (P.pr v c) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • e) = P.pr v c z := by
  intro D u A i hi P K v c c' z γ h1 h2 h3 h4
  have hT : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have he : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1) = z.1 := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hT, one_smul]
  refine ⟨fun y => ?_, (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1, ?_, ?_⟩
  · rw [Pr.mem_act]
    have h5 := pc_isKer P K v c' ((glE γ).symm y)
    rw [GlobalTheory.T.classLattice_sup_primeDual_localization_eq D u A i hi K v c', ← mem_loc_map_equiv, map_glE, h2] at h5
    exact h5
  · refine act_pairOf_value (A.res v) (glE γ) _ _ (P.pr v c) (P.pr v c') _ _ (P.pr_smul v c) (P.pr_smul v c')
      _ z _ he h1 ?_ h4
    rw [map_glE, h3]
    exact le_loc _ _ (Submodule.mem_sup_right (Submodule.subset_span rfl))
  · rw [he]; exact locExt_coe _ _ _ (P.pr_smul v c) z

end GlobalTheory.LevelHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardLevelMoveIncidenceOfPairsStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardLevelMove_incidence_of_pairs : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (z : ↥(Ld D u i hi c)) (γ : GL (Fin (D.R.N i)) D.host.E), (D.fm u).fv i v c (P.pr v c z) = 1 → loc (A.res v) (mulLat γ.1 (clsCrd D u i hi c')) = loc (A.res v) (Ld D u i hi c) → loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (Ld D u i hi c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) → (∀ (x : ↥(Ld D u i hi c')) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1 *ᵥ x.1) ∈ Ld D u i hi c), (D.fm u).fv i v c' (P.pr v c' x) = (D.fm u).fv i v c (P.pr v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).IsKer (pc P v c).L ∧ ∃ e, ((pc P v c').act (glE γ)).f e = 1 ∧ locExt (A.res v) (Ld D u i hi c) (P.pr v c) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • e) = P.pr v c z := by
  first | exact @GlobalTheory.LevelHecke.up_move_incidence | exact GlobalTheory.LevelHecke.up_move_incidence | (intros; apply GlobalTheory.LevelHecke.up_move_incidence <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInvariantHaarFamilyAdelicUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInvariantHaarFamilyAdelicUnitary
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open Formalism.UG (cT cT_mul cT_one bc UJ)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeRef

section Cong

variable {A : Type} [CommRing A] {M : ℕ} (s : A →+* A)

def act (J : Matrix (Fin M) (Fin M) A) (P : GL (Fin M) A) : Matrix (Fin M) (Fin M) A :=
  cT s (P : Matrix (Fin M) (Fin M) A) * J * (P : Matrix (Fin M) (Fin M) A)

theorem act_one (J : Matrix (Fin M) (Fin M) A) : act s J 1 = J := by
  simp [act, cT_one]

theorem act_mul (J : Matrix (Fin M) (Fin M) A) (P Q : GL (Fin M) A) :
    act s J (P * Q) = act s (act s J P) Q := by
  simp only [act, Units.val_mul, cT_mul, Matrix.mul_assoc]

def cong (M : ℕ) : Setoid (Matrix (Fin M) (Fin M) A) where
  r J J' := ∃ P : GL (Fin M) A, J' = act s J P
  iseqv := ⟨fun J => ⟨1, (act_one s J).symm⟩,
    fun ⟨P, h⟩ => ⟨P⁻¹, by rw [h, ← act_mul, mul_inv_cancel, act_one]⟩,
    fun ⟨P, h⟩ ⟨Q, h'⟩ => ⟨P * Q, by rw [h', h, act_mul]⟩⟩

end Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}

omit [NumberField E] in
theorem frameRel_iff (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (g : HA (AF F) σ J)
    (g' : HA (AF F) σ J') : FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g g' ↔
      HA.mat (AF F) σ J' g' = (bc (inclR (AF F)) P)⁻¹ * HA.mat (AF F) σ J g * bc (inclR (AF F)) P := by
  rw [mul_assoc, eq_inv_mul_iff_mul_eq, eq_comm, ← Units.val_inj]
  rfl

omit [NumberField E] in
theorem bc_mem {J : Matrix (Fin M) (Fin M) E} {u : GL (Fin M) E} (hu : act (σ : E →+* E) J u = J) :
    bc (inclR (AF F)) u ∈ HR (AF F) σ J := by
  show cT (sigR (AF F) σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) * J.map (inclR (AF F)) *
    (u : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) = J.map (inclR (AF F))
  have h : cT (sigR (AF F) σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) =
      (cT (σ : E →+* E) (u : Matrix (Fin M) (Fin M) E)).map (inclR (AF F)) := by
    ext i j
    simp [cT, sigR, inclR]
  rw [h, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun X : Matrix (Fin M) (Fin M) E => X.map (inclR (F := F) (AF F))) hu

def IsTransport (σ : E →ₐ[F] E) (J₀ J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)) : Prop :=
  ∃ (P : GL (Fin M) E) (e : HA (AF F) σ J₀ ≃* HA (AF F) σ J), J = act (σ : E →+* E) J₀ P ∧
    (∀ g, FrameRel J₀ J (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ μ = Measure.haar.map e

theorem frame (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (h : J' = act (σ : E →+* E) J P) :
    (∃ e : HA (AF F) σ J ≃* HA (AF F) σ J', ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧
    ∀ e : HA (AF F) σ J ≃* HA (AF F) σ J', (∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) →
      Continuous e ∧ Continuous e.symm :=
  ⟨(GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) M J J' P h).1.exists, (GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) M J J' P h).2⟩

theorem IsTransport.isHaar {J₀ J : Matrix (Fin M) (Fin M) E} {μ : Measure (HA (AF F) σ J)}
    (h : IsTransport σ J₀ J μ) : μ.IsHaarMeasure := by
  obtain ⟨P, e, hJ, he, rfl⟩ := h
  obtain ⟨h1, h2⟩ := (frame J₀ J P hJ).2 e he
  exact e.isHaarMeasure_map _ h1 h2

theorem IsTransport.map_eq (hσ : IsCMExt F E σ) {J₀ J J' : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (HA (AF F) σ J')}
    (h : IsTransport σ J₀ J μ) (h' : IsTransport σ J₀ J' μ') {P : GL (Fin M) E} (hP : J' = act (σ : E →+* E) J P)
    (e : HA (AF F) σ J ≃* HA (AF F) σ J') (he : ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) :
    μ.map e = μ' := by
  haveI := h.isHaar
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hσ
  haveI : μ.IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ (GlobalTheory.HermLineZeros.conj_invol hσ) (δ := σ d - d)
      (sub_ne_zero.2 hd) (by rw [map_sub, GlobalTheory.HermLineZeros.conj_invol hσ, neg_sub]) hJ μ
  obtain ⟨P₁, e₁, hJ₁, he₁, hμ⟩ := h
  obtain ⟨P₂, e₂, hJ₂, he₂, rfl⟩ := h'
  have hu : act (σ : E →+* E) J (P₁⁻¹ * P₂ * P⁻¹) = J := by
    conv_lhs => rw [hJ₁, ← act_mul, ← mul_assoc, mul_inv_cancel_left, act_mul, ← hJ₂, hP, ← act_mul,
      mul_inv_cancel, act_one]
  let u : HA (AF F) σ J := (⟨_, bc_mem hu⟩ : HR (AF F) σ J)
  have hc := ((frame J J' P hP).2 e he).1.measurable
  have hc₁ := ((frame J₀ J P₁ hJ₁).2 e₁ he₁).1.measurable
  have key : (e₂ : _ → _) = e ∘ ((fun x => x * u) ∘ (fun x => u⁻¹ * x)) ∘ e₁ := by
    funext g
    apply Subtype.ext
    have a := (frameRel_iff _ _ _ _ _).1 (he₂ g)
    have b := (frameRel_iff _ _ _ _ _).1 (he (u⁻¹ * e₁ g * u))
    have c := (frameRel_iff _ _ _ _ _).1 (he₁ g)
    refine a.trans (Eq.trans ?_ b.symm)
    show _ = _ * ((bc (inclR (AF F)) (P₁⁻¹ * P₂ * P⁻¹))⁻¹ * HA.mat (AF F) σ J (e₁ g) *
      bc (inclR (AF F)) (P₁⁻¹ * P₂ * P⁻¹)) * _
    rw [c]
    simp only [map_mul, map_inv]
    group
  have hl := measurable_const_mul u⁻¹
  have hr := measurable_mul_const u
  rw [key, ← Measure.map_map hc ((hr.comp hl).comp hc₁), ← Measure.map_map (hr.comp hl) hc₁, ← hμ,
    ← Measure.map_map hr hl, map_mul_left_eq_self, map_mul_right_eq_self]

theorem exists_isTransport (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    ∃ μ, IsTransport σ (Quotient.mk (cong (σ : E →+* E) M) J).out J μ := by
  obtain ⟨P, hP⟩ := Quotient.mk_out (s := cong (σ : E →+* E) M) J
  obtain ⟨e, he⟩ := (frame (σ := σ) _ J P hP).1
  exact ⟨_, P, e, hP, he, rfl⟩

theorem exists_isHaar_basisInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ G : GaugeFam F E σ, G.IsHaar ∧ G.BasisInv := by
  intro F E _ _ _ _ _ σ hσ
  choose μ hμ using fun (M : ℕ) (J : Matrix (Fin M) (Fin M) E) => exists_isTransport σ J
  refine ⟨⟨μ⟩, fun M J _ => (hμ M J).isHaar, fun M J J' P hJ hP => ⟨(frame J J' P hP).1, fun e he => ?_⟩⟩
  have h' := hμ M J'
  rw [← Quotient.sound (s := cong (σ : E →+* E) M) (a := J) (b := J') ⟨P, hP⟩] at h'
  exact (hμ M J).map_eq hσ hJ h' hP e he

end GlobalTheory.GaugeRef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInvariantHaarFamilyAdelicUnitaryStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basisInvariant_haar_family_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ G : GaugeFam F E σ, G.IsHaar ∧ G.BasisInv := by
  first | exact @GlobalTheory.GaugeRef.exists_isHaar_basisInv | exact GlobalTheory.GaugeRef.exists_isHaar_basisInv | (intros; apply GlobalTheory.GaugeRef.exists_isHaar_basisInv <;> assumption)
end
end
