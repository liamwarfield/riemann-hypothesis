module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryOperatorCommutesSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformArchimedeanCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientConjugateThetaForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryStandardCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryStandardCharacter
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.SplitScalar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open scoped Classical in
theorem proj_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem apply_ne_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (T : G →* Module.End ℂ V) (q : G) {f : V}
    (hf : f ≠ 0) : T q f ≠ 0 := fun h => hf (by
  have e : T q⁻¹ (T q f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← e, h, map_zero])

variable {σ : E →ₐ[F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem at_inv {JB : Matrix β β (AE F E)} {g : UG (cA σ) JB}
    (hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)) : At (evI F) (((g⁻¹).1 : Matrix β β (AE F E)) - 1) := by
  intro u hu
  have e : ((g⁻¹).1 : Matrix β β (AE F E)) - 1 = -(((g⁻¹).1 : Matrix β β (AE F E)) * ((g.1 : Matrix β β (AE F E)) - 1)) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have : ((g⁻¹).1 : Matrix β β (AE F E)) * (g.1 : Matrix β β (AE F E)) = 1 := by
      rw [Subgroup.coe_inv, Units.inv_mul]
    rw [this]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

theorem at_mul {JB : Matrix β β (AE F E)} {g h : UG (cA σ) JB}
    (hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)) (hh : At (evI F) ((h.1 : Matrix β β (AE F E)) - 1)) :
    At (evI F) (((g * h).1 : Matrix β β (AE F E)) - 1) := by
  intro u hu
  have e : ((g * h).1 : Matrix β β (AE F E)) - 1 =
      (g.1 : Matrix β β (AE F E)) * ((h.1 : Matrix β β (AE F E)) - 1) + ((g.1 : Matrix β β (AE F E)) - 1) := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, ← Matrix.mul_smul, hh u hu, hg u hu, Matrix.mul_zero, add_zero]

theorem actB_actB_inv {JB : Matrix β β (AE F E)} (g : UG (cA σ) JB) (x : Matrix α β (AE F E)) :
    actB (cA σ) g (actB (cA σ) g⁻¹ x) = x := by
  unfold actB
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]

theorem splittings_differ_by_character : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  intro hP F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d om ω₀ hψ hom hω hcont
  have key : ∀ g : UG (cA σ) JB, ∃ z : ℂ, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
      ∀ φ ∈ schA F κ, om g φ = z • ω₀ g φ := by
    intro g
    by_cases hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)
    swap
    · exact ⟨1, fun h => absurd h hg⟩
    have hgi := at_inv hg
    obtain ⟨z, hz⟩ := GlobalTheory.T.unitary_operator_commutes_schrodinger hP F κ ψ hψ (om g * ω₀ g⁻¹)
      (fun φ hφ => hom.pres g _ ((hω _ hgi).1 φ hφ))
      (fun w φ hφ => by
        have e1 : schr ψ w φ = d.rho ψ (d.e.symm w) φ := by simp [Darboux.rho]
        rw [Module.End.mul_apply, Module.End.mul_apply, e1, (hω _ hgi).2.1 _ φ hφ,
          hom.impl g _ _ ((hω _ hgi).1 φ hφ), actB_actB_inv]
        simp [Darboux.rho])
      (fun μ hμ φ hφ => by
        rw [Module.End.mul_apply, hom.unit μ hμ g _ ((hω _ hgi).1 φ hφ), (hω _ hgi).2.2 μ hμ φ hφ])
    refine ⟨z, fun _ φ hφ => ?_⟩
    have := hz (ω₀ g φ) ((hω g hg).1 φ hφ)
    rwa [Module.End.mul_apply, ← Module.End.mul_apply (ω₀ g⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  choose z hz using key
  by_cases h0 : ∃ φ₀ ∈ schA F κ, φ₀ ≠ 0
  swap
  · push_neg at h0
    refine ⟨fun _ => 1, fun g _ φ hφ => ?_, fun _ _ _ _ => by simp, continuousOn_const, fun _ _ => one_ne_zero⟩
    rw [h0 φ hφ, map_zero, map_zero, smul_zero]
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  refine ⟨z, hz, fun g h hg hh => ?_, fun g hg => ?_, fun g hg h0 => ?_⟩
  · have hgh := at_mul hg hh
    apply smul_left_injective ℂ (apply_ne_zero ω₀ (g * h) hne)
    show z (g * h) • ω₀ (g * h) φ₀ = (z g * z h) • ω₀ (g * h) φ₀
    rw [← hz _ hgh φ₀ hφ₀, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz h hh φ₀ hφ₀, map_smul,
      hz g hg _ ((hω h hh).1 φ₀ hφ₀), smul_smul, mul_comm]
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (apply_ne_zero ω₀ g hne)
    have hl := proj_mem_adm F κ x
    have c1 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g := hcont _ hl φ₀ hφ₀ g hg
    have c2 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g :=
      (hom.cont _ hl φ₀ hφ₀).continuousWithinAt
    have hx' : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ g φ₀) ≠ 0 := hx
    have c3 := c2.div c1 hx'
    have hq : ∀ q, At (evI F) ((q.1 : Matrix β β (AE F E)) - 1) →
        (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) ≠ 0 →
        z q = (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀) /
          (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) := by
      intro q hqS hq0
      rw [hz q hqS φ₀ hφ₀, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hq0]
    refine c3.congr_of_eventuallyEq ?_ (hq g hg hx')
    filter_upwards [Filter.Tendsto.eventually_ne c1 hx', self_mem_nhdsWithin] with q hq0 hqS
    exact hq q hqS hq0
  · have := hz g hg φ₀ hφ₀
    rw [h0, zero_smul] at this
    exact apply_ne_zero om g hne this

end GlobalTheory.SplitScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryStandardCharacterStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_unitary_standard_character : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  first | exact @GlobalTheory.SplitScalar.splittings_differ_by_character | exact GlobalTheory.SplitScalar.splittings_differ_by_character | (intros; apply GlobalTheory.SplitScalar.splittings_differ_by_character <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfBaseTupleIdentityRowSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfBaseTupleIdentityRowSpan
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

variable {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)


set_option maxHeartbeats 1000000 in
theorem pins_merge_of_clauses (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {ι x₀}
    (hsrc : ∀ j, (src j).Pins κ v₀ ι x₀)
    (hlift : ThPinsR R i jL₃ (inC c₃) v₀ c0₃ ι C.Q.l.M (Mfr C.Q.l) lev)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c fun g => (lev g, LinearMap.id))
    (hio : IoLFRec c₃ (fun τ => embF c₃ (tauE D τ)) (lamV D i) (wtA κ) io₃ hw₃)
    (hh : ∀ j, ∃ J', RepsR R i (tup j) (h j) ((src j).bad ()) J' ((src j).Lh ()) ((src j).gam ()) ((src j).vol ()))
    (c0 : ℂ) (hc0 : ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) (cs : J → ℂ) (hu : ∀ j, (u j : ℂ) * cs j = c0)
    (hcs : ∀ j, CXiAt (Wc D i) (rank_Wc i) (inC (src j).c') ((src j).dδ ()) ((src j).U₂ ()) ((src j).dict₂ ()) ι x₀
      ((src j).xi ()) (cs j)) :
    (merge src c₃ h₃ hs jL₃ hV₃ c0₃ lev io₃ hw₃ u h v₀).Pins κ v₀ ι x₀ := by
  have hu0 : ∀ j, u j ≠ 0 := fun j h0 => by
    obtain ⟨m, hm, e⟩ := hc0
    rw [← hu j, h0] at e
    simp [hm.ne'] at e
  refine ⟨hlift, fun j => ⟨?_, ((hsrc j).tuple ()).B, ((hsrc j).tuple ()).xi, ((hsrc j).tuple ()).phi, ((hsrc j).tuple ()).half⟩,
    ⟨hact, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ h₃ _ _ hact).1⟩, fun j => (hsrc j).bad (), fun j => (hsrc j).reps (),
    fun j => ⟨fun k => congrArg (incF _ c₃ (hs j)) (((hsrc j).ep ()).1 k), epIs_map (hs j) ((hsrc j).ep ()).2⟩, hio,
    fun j k q => phiHat_covBC (hs j) _ (u j) _ _ q ((hsrc j).w () k q),
    fun j => covPin_covBC (hs j) _ (hu0 j) ((hsrc j).cov ()), ?_, fun j => (hsrc j).model₂ ()⟩
  · obtain ⟨J', hr⟩ := hh j
    obtain ⟨_, _, _, hT, hc⟩ := hlift.c0
    exact ⟨h j, J', repsR_map _ hr,
      GlobalTheory.RationalValues.placeEx R i jL₃ (inC c₃) (tup j) (h j) c0₃ hMo.jV hT hc hL hW hF.pl_onto hF.muVal,
      thAdIs_thAdOf R i (tup j) (h j) c0₃ hMo.HV hr.2.2.1 hr.2.2.2.2.2.1 v₀, fun _ => Iff.rfl⟩
  · refine (cXiVal_iff _ _ _ _ _ _ _ _ _).2 ⟨c0, hc0, fun j => ?_⟩
    rw [← hu j]
    exact GlobalTheory.OneMapAll.cXiAt_covBC D _ _ _ _ _ _ _ _ (hs j) _ _ _ (u j) _ _ _ _ _ _ ((hsrc j).cov ()).1.2.2.2.2.2.2.2.1 (hcs j)

end Merge

section Row

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

variable {T R κ v₀}


set_option maxHeartbeats 1600000 in
theorem exists_extension_of_clauses (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    {i : Fin D.R.m} {ι x₀}
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (O' : OMDat T.toCore R i T0 id) (hle : O.c'.F ≤ O'.c'.F)
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) (hO' : O'.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) :
    ∃ (M : OMDat T.toCore R i (Option T0) (fun o => o.getD A.μ0)) (h₁ : O.c'.F ≤ M.c'.F), M.lev = O.lev ∧
      M.Pins (κ i) (v₀ i (sg0 D A)) ι x₀ ∧
      ∀ x, O.Plc () x → ∃ x', M.Plc none x' ∧ M.thAd none x' = O.thAd () x ∧
        ∀ f ∈ sec _ O.c' (wtA (κ i)) (Vc D i).rank, IsSum O () x f → IsSum M none x' (rulBC h₁ f) := by
  obtain ⟨a, ha, hca⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO.cxi
  obtain ⟨b, hb, hcb⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO'.cxi
  obtain ⟨c₃, h', haF, hbF⟩ := exists_coeff_roots O'.c' ha hb
  have hb0 : b ≠ 0 := fun h0 => by
    obtain ⟨m, hm, e⟩ := hb
    simp [h0, hm.ne'] at e
  have h₁ : O.c'.F ≤ c₃.F := hle.trans h'
  have h₃ : T.Q.c.F ≤ c₃.F := O.hle.trans h₁
  have hV₃ : T.V ((i : ℕ) + 1) (sOv T.toCore c₃ h₃) = Wc D i := by
    rw [sOv_eq, ← sOv_eq T.toCore O.c' O.hle]; exact O.hV
  obtain ⟨c0₃, hc0⟩ := exists_coef_ext (incF O.c' c₃ h₁) (σ := inC O.c') (inC c₃) (fun _ => rfl) (lamV D i) O.c0'
  obtain ⟨io₃, hw₃, hio, hover⟩ := GlobalTheory.IoExtend.exists_ioLFRec_over _ _ _ _ O.c' c₃ h₁ _ _ (tauE D) (lamV D i) (wtA (κ i)) O.io O.hw hO.io
  have hlift : ThPinsR R i ((incF O.c' c₃ h₁).comp O.jL) (inC c₃) (v₀ i (sg0 D A)) c0₃ ι T.Q.l.M (Mfr T.Q.l) O.lev := by
    refine ⟨(RingHom.ext fun _ => rfl : _ = (inC O.c').comp O.jL).trans hO.lift.field, hO.lift.std, hO.lift.v0, ?_,
      hO.lift.lev⟩
    obtain ⟨g, r, c0L, hT, hc⟩ := hO.lift.c0
    refine ⟨g, r, c0L, hT, fun v => ?_⟩
    obtain ⟨v', hv', e⟩ := hc v
    obtain ⟨v'', hv''⟩ := GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) v'
    exact ⟨v'', by rw [hv'', hv', MvPolynomial.map_map], (hc0 v' v'' hv'').trans e⟩
  obtain ⟨h₀, J₀, hr₀, -, hth₀, hpl₀⟩ := (hO.tuple ()).reps
  choose hh Jt hrt _ using fun t => (hO'.tuple t).reps
  let src : ∀ o : Option T0, OMDat T.toCore R i Unit (fun _ => o.getD A.μ0) := fun o =>
    match o with
    | none => O
    | some t => comap O' (fun _ => t)
  have hs : ∀ o, (src o).c'.F ≤ c₃.F := fun o =>
    match o with
    | none => h₁
    | some _ => h'
  let u : Option T0 → c₃.F := fun o =>
    match o with
    | none => 1
    | some _ => ⟨a, haF⟩ / ⟨b, hbF⟩
  let h : ∀ o, (src o).Cl' () → GA D (Vc D i) := fun o =>
    match o with
    | none => h₀
    | some t => hh t
  have hP := pins_merge_of_clauses src c₃ h₃ hs _ hV₃ c0₃ O.lev io₃ hw₃ u h (v₀ i (sg0 D A)) hL hW hF hMo
    (fun o => match o with
      | none => hO
      | some t => pins_comap (fun _ => t) hO') hlift hO.act.1 hio
    (fun o => match o with
      | none => ⟨J₀, hr₀⟩
      | some t => ⟨Jt t, hrt t⟩) a ha (fun o => o.elim a fun _ => b)
    (fun o => match o with
      | none => one_mul a
      | some _ => div_mul_cancel₀ a hb0)
    (fun o => match o with
      | none => hca ()
      | some t => hcb t)
  refine ⟨_, h₁, rfl, hP, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := (hpl₀ x).1 hx
  choose x' hx' using fun k => GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) (x k)
  have hy' : Place R i A.μ0 h₀ c0₃ (jVx R i A.μ0 y) x' := fun k => (hy k).trans (hc0 _ _ (hx' k)).symm
  refine ⟨x', ⟨y, hy'⟩, (thAdIs_thAdOf R i A.μ0 h₀ c0₃ hMo.HV hr₀.2.2.1 hr₀.2.2.2.2.2.1 _ _ _ hy').trans
    (hth₀ _ _ hy).symm, fun f hf hfx => ?_⟩
  exact isThClsD_covBC_one h₁ (O.dδ ()) rfl _ _ _ _ _ _ O.io io₃ x x' (fun k => hover _ _ (hx' k))
    (hO.cov ()).1.2.2.2.2.2.2.2.1 hf hfx

variable (T R κ v₀)

theorem oneMapRowR_of_clauses (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)
    (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    (hpins : OMPins T R κ v₀ O i) (htie : PhaseTie T R κ v₀ O ph i)
    (hrow0 : OneMapRow0 T R κ v₀ O i) (hex : PinnedDataExist T R κ v₀ i) (hid : IdentityRow T R κ v₀ i)
    (hspan : ClassSumsSpan (O i) (κ i)) : OneMapRowR T R κ v₀ O ph i := by
  refine ⟨hrow0, fun hG => ?_⟩
  obtain ⟨O', hLL', hP'⟩ := hex hG
  have hP := hpins.2
  rw [show O'.s0 = T.σ₀ from sOv_eq _ _ _] at hP'
  rw [show (O i).s0 = T.σ₀ from sOv_eq _ _ _] at hP
  obtain ⟨M, h₁, hlev, hM, hext⟩ := exists_extension_of_clauses hL hW hF hMo (O i) O' (hpins.1.le.trans hLL') hP hP'
  have hLM : D.what₂.embLL.toRatAlgHom.fieldRange ≤ M.c'.F := hpins.1.ge.trans h₁
  rw [← show M.s0 = T.σ₀ from sOv_eq _ _ _] at hM
  obtain ⟨cc', ph', hrow⟩ := hid _ _ M hLM hM
  exact ⟨comap M some, hLM, pins_comap some hM, oneMapOf_comap some
    (oneMapOf_of_extends (O i) M none h₁ hlev hM hext hspan (T.cE ((i : ℕ) + 1)) (htie hrow0) hrow)⟩

end Row

end GlobalTheory.OneMapAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfBaseTupleIdentityRowSpanStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMapRow_of_baseTuple_identityRow_span : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRow0 T R κ v₀ O i → GlobalTheory.OneMapAll.PinnedDataExist T R κ v₀ i → GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → OneMapRowR T R κ v₀ O ph i := by
  first | exact @GlobalTheory.OneMapAll.oneMapRowR_of_clauses | exact GlobalTheory.OneMapAll.oneMapRowR_of_clauses | (intros; apply GlobalTheory.OneMapAll.oneMapRowR_of_clauses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformRationalDarbouxCm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformRationalDarbouxCm
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaTrContCM

theorem continuous_thetaTr_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hs hψ JA JB ξ hA hBm κ _ co hco φ hφ
  exact GlobalTheory.ThetaTrContF.continuous_thetaTrF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hs JA JB ξ hA hBm κ co hco φ hφ

end GlobalTheory.ThetaTrContCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformRationalDarbouxCmStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_thetaTransform_rationalDarboux_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  first | exact @GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm | exact GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm | (intros; apply GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignForWeilModelFamily
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.DatumFourier

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.DatumFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

theorem isThPVecOf_empty {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT Pg Q ξ ξ' f₀ f}
    (hQ : Q = ∅) (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ f₀ f) :
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ' f₀ f := by
  subst hQ
  have e : ∀ y, omegaQ (a := T.rank) (b := S.rank) ∅ T.rank ξ' (-1) y = omegaQ ∅ T.rank ξ (-1) y := fun y => by
    simp [omegaQ]
  unfold IsThPVecOf at h ⊢
  simp only [e]
  exact h


end GlobalTheory.GalOne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedModelThetaFunctionBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedModelThetaFunctionBounded
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.TowerFD

theorem thetaFunOF_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
      ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ ψ f → ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hψ f hf
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  have hmem : ratWF (Matrix.of fun i j => c (w i j)) + w ∈
      (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) : Set (WOF F E nS nT)) :=
    fun i _ j _ => hc (w i j)
  have h := hC _ hmem
  have hq := hf.quasi (Matrix.of fun i j => c (w i j)) w
  have h2 : ‖f w‖ = ‖f (ratWF (Matrix.of fun i j => c (w i j)) + w)‖ := by
    rw [hq, norm_mul, hψ.2.1, one_mul]
  exact h2.trans_le h

end GlobalTheory.TowerFD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedModelThetaFunctionBoundedStatement
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orientedModelThetaFunction_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
      ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ ψ f → ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  first | exact @GlobalTheory.TowerFD.thetaFunOF_bounded | exact GlobalTheory.TowerFD.thetaFunOF_bounded | (intros; apply GlobalTheory.TowerFD.thetaFunOF_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformRealLinesCmExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformRealLinesCmExtension
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

namespace GlobalTheory.ThetaSmoothCM

theorem contDiff_thetaTr_real_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
            ∀ w, ContDiff ℝ ∞ fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (w + L t) := by
  intro F E _ _ _ _ _ σ B hgood nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ hψ JA JB ξ hJA hJB κ _ co hrat φ hφ k L hLc hLf w
  exact GlobalTheory.T.contDiff_thetaTransform_archimedean_cm F E σ B hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA JB ξ hJA hJB κ co hrat φ hφ k L hLc hLf w

end GlobalTheory.ThetaSmoothCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformRealLinesCmExtensionStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_thetaTransform_realLines_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
            ∀ w, ContDiff ℝ ∞ fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (w + L t) := by
  first | exact @GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM | exact GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM | (intros; apply GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalDarbouxQuasiInvariantCm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalDarbouxQuasiInvariantCm
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaQuasiRatCM

theorem thetaTr_ratWF_add_quasi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (Formalism.IndefR.DatumF.ratWF γ + w) =
              B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ w := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hξ hψ JA JB ξ hA hJB κ _ co hrat φ hφ γ w
  exact GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hξ JA JB ξ hA hJB κ co hrat φ hφ γ w

end GlobalTheory.ThetaQuasiRatCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalDarbouxQuasiInvariantCmStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_rationalDarboux_quasiInvariant_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (Formalism.IndefR.DatumF.ratWF γ + w) =
              B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ w := by
  first | exact @GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi | exact GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi | (intros; apply GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformHasLevelCmExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformHasLevelCmExtension
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaLevelCM

theorem thetaTr_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 →
              Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) =
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ hψ JA JB ξ hA hJB κ _ co hco φ hφ
  exact GlobalTheory.ThetaLevelF.thetaTr_levelF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hJB κ co hco φ hφ

end GlobalTheory.ThetaLevelCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformHasLevelCmExtensionStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_hasLevel_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 →
              Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) =
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ := by
  first | exact @GlobalTheory.ThetaLevelCM.thetaTr_level | exact GlobalTheory.ThetaLevelCM.thetaTr_level | (intros; apply GlobalTheory.ThetaLevelCM.thetaTr_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationFifth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.IoExtConj

open GlobalTheory.AdTh.IoExtPf
open scoped Classical

theorem deltaConj_ne {D : D7} (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : deltaConj (D := D) i σ ≠ 0 := by
  refine delta_ne _ _ _ _ (fun τ => ?_) ((rank_Wc i).le.trans (r_le_V i))
  show ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 ≤ _
  rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2, rank_Wc]
  have := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem exists_unit_of_isIoW {D : D7} {V W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (hs : LowSm M)
    (hl : ExtLine M) (c : CoefA V) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)) (Δ : PolF D W.rank V.rank) (hΔ : pt Δ ≠ 0)
    (hwt : ∀ (τ : D.what₂.Tau) (a : Fin W.rank → ℝ), ω (1, atTau θ W τ ((M.fr τ)⁻¹ *
      Matrix.diagonal (fun j => Complex.exp ((a j : ℂ) * Complex.I)) * M.fr τ)) (pt Δ) =
        Complex.exp (((∑ j, extWt M τ j * a j : ℝ) : ℂ) * Complex.I) • pt Δ)
    (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank) (h : IsIoW θ M c ω pt Δ io)
    (v' : ∀ ρ, lowT M ρ) (hv' : IsExtVec M (fun ρ => v' ρ)) :
    ∃ w : c.W, ‖w‖ = 1 ∧ io (PiTensorProduct.tprod ℂ v') w = Δ := by
  obtain ⟨-, hK, v, w, hv1, hw1, hio⟩ := h
  let f : LowT M →ₗ[ℂ] (WO V W → ℂ) := pt ∘ₗ io.flip w
  have hf : ∀ x, f x = pt (io x w) := fun x => rfl
  have hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [hf, hio]
    exact hΔ
  have hv : IsExtVec M (fun ρ => v ρ) := by
    refine fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩
    have hm := GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2
    let u : lowT M τ := ⟨⟨_, hs τ hm⟩, hm⟩
    have h1 := hK τ _ ha v u rfl w
    rw [hio, hwt τ a, ← hio, ← hf, ← hf] at h1
    have h2 := inj_factor M hs hl τ f (fun k => ω (1, atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)))
      (fun k hk v u hu => hK τ k hk v u hu w) v hv0
      (u - Complex.exp (((∑ j, extWt M τ j * a j : ℝ) : ℂ) * Complex.I) • v τ) (by
        rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1,
          RingHom.id_apply, sub_self])
    exact congrArg (fun y : lowT M τ => ((y : M.sm τ) : M.H τ)) (sub_eq_zero.1 h2)
  choose a ha1 ha using hl _ _ hv hv'
  have e : v' = fun ρ => a ρ • v ρ := funext fun ρ => Subtype.ext (ha ρ)
  have hn : ‖∏ ρ, a ρ‖ = 1 := by simp [norm_prod, ha1]
  have h0 : ∏ ρ, a ρ ≠ 0 := fun h => by simp [h] at hn
  refine ⟨(∏ ρ, a ρ)⁻¹ • w, by rw [norm_smul, norm_inv, hn, hw1]; simp, ?_⟩
  rw [e, MultilinearMap.map_smul_univ, map_smul, map_smul, LinearMap.smul_apply, smul_smul]
  simp only [RingHom.id_apply, inv_mul_cancel₀ h0, one_smul, hio]

end GlobalTheory.GalOne.IoExtConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationSixth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Rebase

open GlobalTheory.ConjLiftUnique

theorem rebase_gen {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {S : D.what₂.Tau → SPar} {M : DSModel W S}
    (hω : IsWeilDatumO ψ V W χV χW ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK)
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) 1) (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c : CoefA V}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (cart M τ)) f)
    {BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {p : D.what₂.Tau → ℕ} (hB : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (B τ) (p τ))
    (hO : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (onb M τ) (p τ))
    (hinj : Function.Injective (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f)) {Δ : PolF D W.rank V.rank}
    {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank}
    (hio : IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f) Δ io) :
    ∃ io' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
      IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f) Δ io' ∧
      ∀ x w, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) =
        pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (io' x w) := by
  classical
  have hk : ∀ τ, ∃ k ∈ Formalism.REAL.Kset (M.ε τ), B τ = onb M τ * k := fun τ => by
    obtain ⟨k, hk, -, k2, -⟩ := exists_kset (M.fr_unit τ) (M.fr_gram τ) (hO τ) (hB τ)
    refine ⟨k, hk, k2.trans ?_⟩
    unfold onb
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), Matrix.mul_one]
  choose k hk hBk using hk
  obtain ⟨s, hs⟩ : ∃ s : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank, ∀ P,
      pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f P =
        pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (s P) := by
    obtain rfl : B = fun τ => onb M τ * k τ := funext hBk
    have h := GlobalTheory.FockSubst.pureTensorO_subst D ψ θ V W S M BV f k
      (fun τ b a => if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) hω.std hθ hV hf hk fun _ _ _ => rfl
    generalize MvPolynomial.aeval (R := ℂ) (S₁ := MvPolynomial (FVar D W.rank V.rank) ℂ) _ = s at h
    exact ⟨s.toLinearMap, h⟩
  have e0 : ∀ x w, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (io.compr₂ s x w) =
      pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) := fun x w => (hs _).symm
  refine ⟨io.compr₂ s, ⟨fun u hu x w => by rw [e0, e0, hio.1 u hu],
    fun τ k hk v u hu w => by rw [e0, e0, hio.2.1 τ k hk v u hu], ?_⟩, fun x w => (e0 x w).symm⟩
  have t1 := GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M) B hf
  let F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W :=
    io.compr₂ ((pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f).codRestrict (thetaSub ψ V W) t1)
  have f1 : ∀ x w, (F x w).1 = pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) := fun _ _ => rfl
  clear_value F
  have hF : Eqv θ ω F := ⟨fun u hu x w => by rw [f1, f1, hio.1 u hu],
    fun τ k hk v u hu w => by rw [f1, f1, hio.2.1 τ k hk v u hu]⟩
  obtain ⟨v₀, w₀, n1, n2, e⟩ := hio.2.2
  obtain ⟨v₁, l, n3, hl, e1⟩ := exists_move hω hθ kV kW hV h1 h2 hF hf hv hB hO Δ n1 ((f1 _ w₀).trans (congrArg _ e))
  have l0 : l ≠ 0 := fun h => by simp [h] at hl
  refine ⟨v₁, l⁻¹ • w₀, n3, by rw [norm_smul, norm_inv, hl, n2, inv_one, one_mul], hinj ?_⟩
  rw [map_smul, map_smul, e0, ← f1, e1, smul_smul, inv_mul_cancel₀ l0, one_smul]

end GlobalTheory.GalOne.Rebase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthPeriodicOfCosetIndicatorExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthPeriodicOfCosetIndicatorExpansion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem nsmul_mem_of_isCosetDatum {t : T} {p : Pair T} {k : ℕ} {d : FinDatum G t p} (h : IsCosetDatum k d)
    {x : WO (G.pS p) (G.pT p)} (hx : d.fn x ≠ 0) : k • x ∈ pairLat G p := by
  obtain ⟨x₀, -, h1, hfn⟩ := h
  rw [hfn] at hx
  obtain ⟨u, hu, -, rfl⟩ := Set.mem_of_indicator_ne_zero hx
  rw [nsmul_add]
  exact add_mem h1 (nsmul_mem (nsmul_mem hu k) k)

theorem fn_add_nsmul_of_isCosetDatum {t : T} {p : Pair T} {k : ℕ} {d : FinDatum G t p} (h : IsCosetDatum k d)
    {u : WO (G.pS p) (G.pT p)} (hu : u ∈ pairLat G p) (hu' : IsHalf d.e u) (x : WO (G.pS p) (G.pT p)) :
    d.fn (x + k • u) = d.fn x := by
  obtain ⟨x₀, -, -, hfn⟩ := h
  rw [hfn]
  by_cases hx : x ∈ halfCoset d.e (pairLat G p) k x₀
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((add_nsmul_mem_halfCoset_iff hu hu').2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (add_nsmul_mem_halfCoset_iff hu hu').1 hx)]

theorem depthOK_of_isCosetExpansion : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) (τ : PureDat G t →₀ ℂ), IsCosetExpansion S t Φ β k τ → ∃ e, IsIdemSum e (locPl G t) ∧ ExpWith S t Φ β e τ ∧ DepthOK S t Φ β e k := by
  intro D T L sc G W U S t Φ β k τ h
  obtain ⟨-, ⟨e, he, hP, hsum⟩, hcos⟩ := h
  refine ⟨e, he, ⟨hP, hsum⟩, ?_, ?_⟩
  · intro x y hx hy hne
    unfold flatProd at hne
    rw [← hsum x y hx hy] at hne
    obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    beta_reduce at hne
    have h1 : ∏ j, (d.1 j).fn (x j) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero, zero_mul])
    have h2 : ∏ i, (d.2 i).fn (y i) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    rw [Finset.prod_ne_zero_iff] at h1 h2
    exact ⟨fun j => nsmul_mem_of_isCosetDatum ((hcos d hd).1 j) (h1 j (Finset.mem_univ _)),
      fun i => nsmul_mem_of_isCosetDatum ((hcos d hd).2 i) (h2 i (Finset.mem_univ _))⟩
  · intro x u y v hx hy hu hv
    have hx' : ∀ j, IsHalf e ((x + k • u) j) := fun j a b => by
      show e * (x j + k • u j) a b = (x j + k • u j) a b
      rw [Matrix.add_apply, mul_add, hx j a b, isHalf_nsmul_of k (hu j).1 a b]
    have hy' : ∀ i, IsHalf e ((y + k • v) i) := fun i a b => by
      show e * (y i + k • v i) a b = (y i + k • v i) a b
      rw [Matrix.add_apply, mul_add, hy i a b, isHalf_nsmul_of k (hv i).1 a b]
    unfold flatProd
    rw [← hsum _ _ hx' hy', ← hsum x y hx hy]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hx1 : ∀ j, (d.1 j).fn ((x + k • u) j) = (d.1 j).fn (x j) := fun j =>
      fn_add_nsmul_of_isCosetDatum ((hcos d hd).1 j) (hu j).2 (((hP d hd).1 j).2.1 ▸ (hu j).1) (x j)
    have hy1 : ∀ i, (d.2 i).fn ((y + k • v) i) = (d.2 i).fn (y i) := fun i =>
      fn_add_nsmul_of_isCosetDatum ((hcos d hd).2 i) (hv i).2 (((hP d hd).2 i).2.1 ▸ (hv i).1) (y i)
    simp only [hx1, hy1]

end GlobalTheory.DepthUnf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthPeriodicOfCosetIndicatorExpansionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthPeriodic_of_cosetIndicatorExpansion : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) (τ : PureDat G t →₀ ℂ), IsCosetExpansion S t Φ β k τ → ∃ e, IsIdemSum e (locPl G t) ∧ ExpWith S t Φ β e τ ∧ DepthOK S t Φ β e k := by
  first | exact @GlobalTheory.DepthUnf.depthOK_of_isCosetExpansion | exact GlobalTheory.DepthUnf.depthOK_of_isCosetExpansion | (intros; apply GlobalTheory.DepthUnf.depthOK_of_isCosetExpansion <;> assumption)
end
end
