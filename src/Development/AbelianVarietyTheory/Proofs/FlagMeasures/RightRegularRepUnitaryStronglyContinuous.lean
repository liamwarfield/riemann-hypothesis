module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarMeasureGramGL2ActionTensor
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueGlobalLatticeOfLocalLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

namespace GlobalTheory.RightRegFund

theorem isRightReg_props (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (hR : I.IsRightReg μf fund R) :
    R 1 = 1 ∧ (∀ g h, R (g * h) = R g * R h) ∧ (∀ g F, ‖R g F‖ = ‖F‖) ∧
      (∀ F, Continuous fun g => R g F) ∧ ∀ F : I.L2 μf fund,
        (∀ᵐ y ∂(I.muA μf), ∀ γ ∈ I.GFset, I.ext F (γ * y) = I.ext F y) ∧
          AEStronglyMeasurable (I.ext F) (I.muA μf) := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.T.finiteAdelicUnitary_congruenceTopology I
  obtain ⟨Γ, hΓ, hc, -, hfd⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain I
  obtain ⟨hl, hrt, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant I μf
  have hD := hfd μf fund hfund
  have : BorelSpace I.GA := inferInstance
  have : (I.muA μf).IsMulLeftInvariant := ⟨hl⟩
  have : (I.muA μf).IsMulRightInvariant := ⟨hrt⟩
  have : IsFiniteMeasureOnCompacts (I.muA μf) := by
    unfold AutInst.muA; infer_instance
  have hr : ∀ y, ∃ γ : Γ, I.rep fund y = (γ : I.GA) * y ∧ I.rep fund y ∈ fund := by
    intro y
    have h := hfund.2.1 y
    have e : I.rep fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  refine ⟨map_one hD hfund.1 hr hR, map_mul hD hfund.1 hr hR, norm_map hD hfund.1 hr hR,
    continuous_map hD hfund.1 hr hR, fun F => ⟨?_, ?_⟩⟩
  · refine (ae_good hD).mono fun y hy γ hγ => ?_
    have hm : γ ∈ (Γ : Set I.GA) := hΓ ▸ hγ
    unfold AutInst.ext
    rw [rep_mul hr hy ⟨γ, hm⟩]
  · exact aestronglyMeasurable_comp_rep hD hfund.1 hr (Lp.stronglyMeasurable F)

theorem rightReg_unitary_continuous : ∀ B : RowsAut, B.R 1 = 1 ∧ (∀ g h, B.R (g * h) = B.R g * B.R h) ∧ (∀ g F, ‖B.R g F‖ = ‖F‖) ∧ (∀ F, Continuous fun g => B.R g F) ∧ ∀ F : B.I.L2 B.μf B.fund, (∀ᵐ y ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, B.I.ext F (γ * y) = B.I.ext F y) ∧ AEStronglyMeasurable (B.I.ext F) (B.I.muA B.μf) :=
  fun B => isRightReg_props B.I B.μf B.fund B.fund_spec B.R B.R_spec

end GlobalTheory.RightRegFund
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuousStatement
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous : ∀ B : RowsAut, B.R 1 = 1 ∧ (∀ g h, B.R (g * h) = B.R g * B.R h) ∧ (∀ g F, ‖B.R g F‖ = ‖F‖) ∧ (∀ F, Continuous fun g => B.R g F) ∧ ∀ F : B.I.L2 B.μf B.fund, (∀ᵐ y ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, B.I.ext F (γ * y) = B.I.ext F y) ∧ AEStronglyMeasurable (B.I.ext F) (B.I.muA B.μf) := by
  first | exact @GlobalTheory.RightRegFund.rightReg_unitary_continuous | exact GlobalTheory.RightRegFund.rightReg_unitary_continuous | (intros; apply GlobalTheory.RightRegFund.rightReg_unitary_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Classical in
private theorem algebraMap_trace_eq_add_of_ne_id {F E : Type} [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] (h2 : Module.finrank F E = 2) (σ : E →ₐ[F] E)
    (hσ : σ ≠ AlgHom.id F E) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hτ : τ ≠ 1 := by
    intro h
    apply hσ
    ext y
    have := congrArg (fun f : E ≃ₐ[F] E => f y) h
    simpa [τ] using this
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, τ} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2,
      Finset.card_pair (Ne.symm hτ)]
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hτ)]
  simp [τ]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Classical in
private theorem ne_id_of_embedding_conj {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
    (hE : IsTotallyComplex E) (σ : E →ₐ[F] E)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) :
    σ ≠ AlgHom.id F E := by
  intro h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := hE.isComplex w
  rw [InfinitePlace.isComplex_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hσ w.embedding x
  rw [h] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm


open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Classical in
theorem _root_.GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) →
      ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ hCM hU
  obtain ⟨-, hE, h2, hσ⟩ := hCM
  have hD := (_root_.GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hU
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have := coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)
    rw [hD, FractionalIdeal.coeIdeal_top] at this
    exact inv_eq_one.mp this.symm
  have key : ∀ a : F, (∀ b : 𝓞 E, a * Algebra.trace F E (algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range) →
      a ∈ (algebraMap (𝓞 F) F).range := by
    intro a ha
    have hmem : algebraMap F E a ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual (fun h => by
        simpa using congrArg (fun J : FractionalIdeal (𝓞 E)⁰ E => (1 : E) ∈ J) h)]
      intro y hy
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
      rw [Algebra.traceForm_apply, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
      exact ha b
    rw [hdual] at hmem
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
    have hint : IsIntegral ℤ (algebraMap F E a) := by
      rw [← hb]
      exact b.isIntegral_coe
    have hint' : IsIntegral ℤ a :=
      (isIntegral_algebraMap_iff ).1 hint
    exact ⟨⟨a, hint'⟩, rfl⟩
  set I : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E)) with hI
  have hItop : I = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hne
    have hp0 : p ≠ ⊥ := (Ideal.bot_lt_of_maximal p (RingOfIntegers.not_isField F)).ne'
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hp0 hp.ne_top
    apply hx1
    obtain ⟨r, hr⟩ := key x (by
      intro b
      have ht : Algebra.intTrace (𝓞 F) (𝓞 E) b ∈ p := hIp ⟨b, rfl⟩
      have hmem := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hp0)).1 hx
        _ (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 F)⁰ ht)
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
      refine ⟨r, ?_⟩
      rw [hr, Algebra.algebraMap_intTrace (K := F) (L := E)])
    rw [← hr]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨r, rfl⟩
  have h1 : (1 : 𝓞 F) ∈ I := hItop ▸ Submodule.mem_top
  obtain ⟨θ, hθ⟩ := h1
  refine ⟨θ, ?_⟩
  rw [← algebraMap_trace_eq_add_of_ne_id h2 σ (ne_id_of_embedding_conj hE σ hσ)]
  have := Algebra.algebraMap_intTrace (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E) θ
  rw [hθ, map_one] at this
  rw [← this]
  exact map_one _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.LatLoc

theorem isLattice_map {E V W : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (f : V ≃ₗ[E] W) (Λ : Submodule (𝓞 E) V) (h : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (Λ.map ((f : V →ₗ[E] W).restrictScalars (𝓞 E))) := by
  exact Submodule.IsLattice.of_fg E (h.fg.map _)

variable {D : D7}

def cE (D : D7) : (VS D).V ≃ₗ[D.host.E] (Fin (nV D) → D.host.E) := (VS D).frame.equivFun

def cL (Λ : LV D) : Submodule (𝓞 D.host.E) (Fin (nV D) → D.host.E) :=
  Λ.map (((cE D) : (VS D).V →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))

theorem baseChange_eq (Z : LocDat D) (p : PlF D) (x : (VS D).V) : baseChange₂ D p x = (GlobalTheory.HL.placesOf Z).bc p (cE D x) := rfl

theorem localLattice_eq (Z : LocDat D) (p : PlF D) (Λ : LV D) : lattice₂ D Z.M p Λ = (GlobalTheory.HL.placesOf Z).lat p (cL Λ) := by
  unfold lattice₂ GlobalTheory.HL.Places.lat cL
  rw [Submodule.map_coe, Set.image_image]
  rfl

theorem cL_injective : Function.Injective (cL (D := D)) := by
  intro Λ₁ Λ₂ h
  have := congrArg (Submodule.comap (((cE D) : (VS D).V →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))) h
  unfold cL at this
  rwa [Submodule.comap_map_eq_of_injective (by exact (cE D).injective),
    Submodule.comap_map_eq_of_injective (by exact (cE D).injective)] at this

theorem std_finite (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) :
    {p | lattice₂ D Z.M p Λ ≠ Submodule.span ((GlobalTheory.HL.placesOf Z).L p).O
      (Set.range fun i => (Pi.single i 1 : Fin (nV D) → ((GlobalTheory.HL.placesOf Z).loc p).Ep))}.Finite := by
  have hc : Submodule.IsFullLattice D.host.E (cL Λ) := by
    refine { toIsLattice := isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E ((cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (cE D).surjective
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (cL Λ) hc).2.2
  simp only [localLattice_eq]
  exact this

theorem lattices_local_global : ∀ (D : D7) (Z : LocDat D), (∀ Λ₁ Λ₂ : LV D, Submodule.IsFullLattice D.host.E Λ₁ →
    Submodule.IsFullLattice D.host.E Λ₂ → {p | lattice₂ D Z.M p Λ₁ ≠ lattice₂ D Z.M p Λ₂}.Finite ∧
      ((∀ p, lattice₂ D Z.M p Λ₁ = lattice₂ D Z.M p Λ₂) → Λ₁ = Λ₂)) ∧
    ∀ (Λ₀ : LV D), Submodule.IsFullLattice D.host.E Λ₀ → ∀ Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p),
      (∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤) →
      {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite →
      ∃ Λ : LV D, Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ = Lp p := by
  intro D Z
  refine ⟨fun Λ₁ Λ₂ h₁ h₂ => ⟨?_, fun h => ?_⟩, fun Λ₀ h₀ Lp hL hfin => ?_⟩
  · refine ((std_finite Z Λ₁ h₁).union (std_finite Z Λ₂ h₂)).subset fun p hp => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hp (hc.1.trans hc.2.symm)
  · apply cL_injective
    have hc (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) :
        Submodule.IsFullLattice D.host.E (cL Λ) := by
      refine { toIsLattice := isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
      change Submodule.span D.host.E ((cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
      rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
      exact (cE D).surjective
    have r₁ := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (cL Λ₁) (hc Λ₁ h₁)).1
    have r₂ := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (cL Λ₂) (hc Λ₂ h₂)).1
    ext x
    rw [r₁, r₂]
    refine forall_congr' fun p => ?_
    rw [← localLattice_eq, ← localLattice_eq, h p]
  · obtain ⟨Γ, ⟨hΓ, hΓp⟩, -⟩ := GlobalTheory.T.exists_unique_global_lattice_of_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) Lp (fun p => hL p)
      (((std_finite Z Λ₀ h₀).union hfin).subset fun p hp => by
        by_contra hc
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
        exact hp (hc.2.trans hc.1))
    refine ⟨Γ.map (((cE D).symm : (Fin (nV D) → D.host.E) →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E)),
      isLattice_map _ _ hΓ, fun p => ?_⟩
    rw [localLattice_eq, ← hΓp p]
    congr 1
    unfold cL
    rw [← Submodule.map_comp]
    convert Submodule.map_id Γ
    ext x
    simp

end GlobalTheory.Unfold.LatLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrincipleStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattice_local_global_principle : ∀ (D : D7) (Z : LocDat D), (∀ Λ₁ Λ₂ : LV D, Submodule.IsFullLattice D.host.E Λ₁ → Submodule.IsFullLattice D.host.E Λ₂ → {p | lattice₂ D Z.M p Λ₁ ≠ lattice₂ D Z.M p Λ₂}.Finite ∧ ((∀ p, lattice₂ D Z.M p Λ₁ = lattice₂ D Z.M p Λ₂) → Λ₁ = Λ₂)) ∧ ∀ (Λ₀ : LV D), Submodule.IsFullLattice D.host.E Λ₀ → ∀ Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p), (∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤) → {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite → ∃ Λ : LV D, Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ = Lp p := by
  first | exact @GlobalTheory.Unfold.LatLoc.lattices_local_global | exact GlobalTheory.Unfold.LatLoc.lattices_local_global | (intros; apply GlobalTheory.Unfold.LatLoc.lattices_local_global <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace GlobalTheory.TypeAsm.HostArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem places : GlobalTheory.DegVol.IsPlaces (embS D) := by
  have := D.host.toHostAx.isCMField_hostE
  have : IsGalois ℚ D.host.E := D.host.toHostAx.hostE_isGalois
  have hcc : ∀ g : D.R.GG, (D.R.toFrame.cc * g).1.2 = - g.1.2 := by
    intro g
    simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
  have hemb : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      embS D τ x = D.host.φ₀ (D.host.gal.symm (D.eTau τ : D.R.GG) x) := fun _ _ => rfl
  have hconj : ∀ y : D.host.E, D.host.φ₀ (D.host.conj y) = starRingEnd ℂ (D.host.φ₀ y) :=
    fun y => D.host.toHostAx.conjE_apply _ y
  refine ⟨fun τ a => D.sp.cm.cmUnram.2.1 _ a, fun w => ?_⟩

  have key : ∀ τ₁ τ₂ : D.what₂.Tau, NumberField.InfinitePlace.mk (embS D τ₁) =
      NumberField.InfinitePlace.mk (embS D τ₂) → τ₁ = τ₂ := by
    intro τ₁ τ₂ h
    rw [NumberField.InfinitePlace.mk_eq_iff] at h
    have h1 := (D.eTau τ₁).2
    have h2 := (D.eTau τ₂).2
    rw [Formalism.HC.Frame.mem_Psi_iff] at h1 h2
    apply D.eTau.injective
    apply Subtype.ext
    apply D.host.gal.symm.injective
    rcases h with h | h
    · ext x
      apply D.host.φ₀.injective
      have := DFunLike.congr_fun h x
      rwa [hemb, hemb] at this
    · exfalso
      have heq : D.host.conj * D.host.gal.symm (D.eTau τ₁ : D.R.GG) =
          D.host.gal.symm (D.eTau τ₂ : D.R.GG) := by
        ext x
        apply D.host.φ₀.injective
        have := DFunLike.congr_fun h x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq, hemb, hemb] at this
        rw [AlgEquiv.mul_apply, hconj]
        exact this
      have h3 := congrArg (fun g : D.R.GG => g.1.2) (congrArg D.host.gal heq)
      simp only [map_mul, MulEquiv.apply_symm_apply] at h3
      rw [show D.host.gal D.host.conj = D.R.toFrame.cc from D.host.gal.apply_symm_apply _,
        hcc, h1, h2] at h3
      exact absurd h3 (by decide)

  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ)
    D.host.φ₀ w.embedding (Subsingleton.elim _ _)
  have hwρ : ∀ x, D.host.φ₀ (σ.symm x) = w.embedding x := fun x => by rw [← hσ]; rfl
  have hex : ∃ τ : D.what₂.Tau, NumberField.InfinitePlace.mk (embS D τ) = w := by
    by_cases hgP : D.host.gal σ.symm ∈ D.R.Psi
    · refine ⟨D.eTau.symm ⟨_, hgP⟩, ?_⟩
      have : embS D (D.eTau.symm ⟨_, hgP⟩) = w.embedding := by
        ext x
        rw [hemb, Equiv.apply_symm_apply]
        simp only [MulEquiv.symm_apply_apply]
        exact hwρ x
      rw [this, NumberField.InfinitePlace.mk_embedding]
    · have hg' : D.R.toFrame.cc * D.host.gal σ.symm ∈ D.R.Psi := by
        rw [Formalism.HC.Frame.mem_Psi_iff] at hgP ⊢
        rw [hcc]
        rcases Int.units_eq_one_or (D.host.gal σ.symm).1.2 with h | h
        · exact absurd h hgP
        · rw [h, neg_neg]
      refine ⟨D.eTau.symm ⟨_, hg'⟩, ?_⟩
      have : embS D (D.eTau.symm ⟨_, hg'⟩) = NumberField.ComplexEmbedding.conjugate w.embedding := by
        ext x
        rw [hemb, Equiv.apply_symm_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]
        simp only [map_mul, MulEquiv.symm_apply_apply, AlgEquiv.mul_apply]
        rw [show D.host.gal.symm D.R.toFrame.cc = D.host.conj from rfl, hconj, hwρ]
      rw [this, NumberField.InfinitePlace.mk_conjugate_eq, NumberField.InfinitePlace.mk_embedding]
  obtain ⟨τ, hτ⟩ := hex
  exact ⟨τ, hτ, fun τ' hτ' => key τ' τ (hτ'.trans hτ.symm)⟩

theorem finrank_eq : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.toHostAx.finrank_cmField]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring

theorem fDeg_eq : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := by
  have := D.host.toHostAx.isCMField_hostE
  have h1 := NumberField.IsTotallyComplex.finrank (K := D.host.E)
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  omega

end GlobalTheory.TypeAsm.HostArith

namespace GlobalTheory.TypeAsm.HostArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem vInv_eq : Formalism.HermitianLatticesTheory.vInv D.host.E = D.host.v := by
  have h1 := GlobalTheory.TypeAsm.HostArith.fDeg_eq D
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  unfold Formalism.HermitianLatticesTheory.vInv Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
  rw [h1, h2]
  push_cast
  rfl

theorem finrank_O : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
  have := D.host.toHostAx.isCMField_hostE
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _

private theorem absNorm_dI_eq_abs_discr_of_discr_eq_sq (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) :
    (Ideal.absNorm (dI D) : ℝ) = |(NumberField.discr D.host.E : ℝ)| := by
  have := D.host.toHostAx.isCMField_hostE
  unfold dI
  rw [Ideal.absNorm_algebraMap, GlobalTheory.TypeAsm.HostArith.finrank_O,
    NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F), hd]
  push_cast
  rw [abs_pow, Nat.cast_natAbs, Int.cast_abs]

private theorem one_le_host_v : 1 ≤ D.host.v := by
  have h := D.host.toHostAx.der.rd_sq_ge
  have ho : (1 : ℝ) ≤ D.R.toFrame.ord := by exact_mod_cast D.R.toFrame.ord_pos
  have hrd : D.host.rdE = D.host.toHostRaw.rd := rfl
  have hnn : 0 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.rdE; positivity
  rw [← hrd] at h
  unfold Formalism.BasicNotions.Host.v
  nlinarith

theorem absNorm_dI (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) :
    (Ideal.absNorm (dI D) : ℝ) = (2 * D.host.v) ^ (2 * D.R.f) := by
  rw [absNorm_dI_eq_abs_discr_of_discr_eq_sq D hd]
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  have hf : (0 : ℝ) < ((2 * D.R.f : ℕ) : ℝ) := by
    rw [← h2]; exact_mod_cast Module.finrank_pos
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  rw [hv]
  unfold Formalism.BasicNotions.Host.rdE
  rw [h2, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div,
    inv_mul_cancel₀ hf.ne', Real.rpow_one]

theorem dI_star : ∀ x ∈ dI D, ∃ y ∈ dI D, (y : D.host.E) = star (x : D.host.E) := by
  have := D.host.toHostAx.isCMField_hostE
  intro x hx

  have key : dI D ≤ Ideal.comap (NumberField.IsCMField.ringOfIntegersComplexConj D.host.E) (dI D) := by
    show Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) _ ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    simp only [Ideal.mem_comap]
    rw [AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hi
  exact ⟨NumberField.IsCMField.ringOfIntegersComplexConj D.host.E x, key hx, rfl⟩

theorem dI_ne_bot (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) : dI D ≠ ⊥ := by
  intro h
  have h1 := absNorm_dI D hd
  rw [h, Ideal.absNorm_bot, Nat.cast_zero] at h1
  have hv := one_le_host_v D
  have : (0 : ℝ) < (2 * D.host.v) ^ (2 * D.R.f) := pow_pos (by linarith) _
  linarith

theorem rank_VS : Module.finrank D.host.E (VS D).V = 2 * D.R.rS + D.R.k + 1 := by
  rw [(VS D).rank_eq]
  have h := D.sp.Y_rank 0 (Nat.zero_le _)
  obtain ⟨j, hj⟩ := D.R.m_even
  have hm2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS] at h ⊢
  show (D.sp.Y 0).rank = _
  rw [h]
  omega

theorem two_le_gS : 2 ≤ gS D := by
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  show 2 ≤ D.host.g 0 * D.host.g 1
  nlinarith

private theorem card_Tau_eq_f : Fintype.card D.what₂.Tau = D.R.f := by
  have hP := (HostArith.places D).2
  have hb : Function.Bijective (fun τ => NumberField.InfinitePlace.mk (embS D τ)) :=
    ⟨fun a b h => (hP _).unique h rfl, fun w => (hP w).exists⟩
  rw [Fintype.card_of_bijective hb]
  exact HostArith.fDeg_eq D

end GlobalTheory.TypeAsm.HostArith

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hostC : HostC := by
  intro D large₂ hStd
  obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩ := hStd
  obtain ⟨⟨-, hD0, -⟩, -⟩ := hK
  obtain ⟨-, -, -, -, -, -, -, -, hsplit, -⟩ := hD0
  have hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 := D.host.toHostAx.der.discr_sq
  exact ⟨D.sp.cm.cmUnram, HostArith.places D, HostArith.vInv_eq D, HostArith.one_le_host_v D,
    HostArith.fDeg_eq D, HostArith.card_Tau_eq_f D, HostArith.finrank_eq D, HostArith.dI_ne_bot D hd,
    HostArith.dI_star D, HostArith.absNorm_dI D hd, HostArith.rank_VS D, HostArith.two_le_gS D,
    fun u => ⟨(D.mem u).A.T_prime, (hsplit u).1⟩⟩

end GlobalTheory.TypeAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHostFieldArithmeticConditions : GlobalTheory.TypeAsm.HostC := by
  first | exact @GlobalTheory.TypeAsm.hostC | exact GlobalTheory.TypeAsm.hostC | (intros; apply GlobalTheory.TypeAsm.hostC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

def FlagPairStabilizer {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Subgroup (GV D) where
  carrier := H0 F F'
  one_mem' := ⟨Subgroup.one_mem _, fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun i => ?_, fun i => ?_⟩
    · show a (b _) = _
      rw [hb1, ha1]
    · show a (b _) = _
      rw [hb2, ha2]
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    refine ⟨Subgroup.inv_mem _ ha, fun i => ?_, fun i => ?_⟩
    · conv_lhs => rw [← ha1 i]
      show a.symm (a _) = _
      simp
    · conv_lhs => rw [← ha2 i]
      show a.symm (a _) = _
      simp

theorem mem_H0sub {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (h : GV D) : h ∈ FlagPairStabilizer F F' ↔ h ∈ H0 F F' := Iff.rfl

end GlobalTheory.Unfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLattices
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatLocMove

variable {D : D7}

theorem isLattice_gmap' (g : GV D) (A : LV D) (hA : Submodule.IsLattice D.host.E A) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g A) := by
  exact Submodule.IsLattice.of_fg _ (hA.fg.map _)

theorem finrank_Vp_eq (p : PlF D) : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

end GlobalTheory.RatLocMove

namespace GlobalTheory.RatLocMove

open GlobalTheory.LocExt

variable {D : D7}

theorem localExtension_isometryFixingFrames_mem_localUnitary {u u' : D.what₂.Word}
    (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS)
    (hB : Based Z FP (Tu D u) (Tu D u') F F') (h : GV D) (hh : h ∈ H0 F F') (p : PlF D)
    (g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hg : Ext p h g') : g' ∈ (FP p).UW0 := by
  obtain ⟨hiso, hF, hF'⟩ := hh
  obtain rfl := locEquiv_unique p h g' hg
  refine Subgroup.subset_closure ⟨locEquiv_unitary Z p h hiso, fun b => ⟨?_, ?_⟩⟩
  · rw [(hB p).1]
    show locEquiv p h (frFac Z.δ p b • baseChange₂ D p (frame F b)) = _
    rw [map_smul, locEquiv_ext p h, hF b]
    rfl
  · rw [(hB p).2.1]
    show locEquiv p h (frFac Z.δ p b • baseChange₂ D p (frame F' b)) = _
    rw [map_smul, locEquiv_ext p h, hF' b]
    rfl

theorem rat_ext_moves : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → (∀ (g : GV D) (p : PlF D), ∃! g', Ext p g g') ∧ (∀ h ∈ H0 F F', ∀ p g', Ext p h g' → g' ∈ (FP p).UW0) ∧ (∀ (g : GV D) p g' (Λ : LV D), Ext p g g' → lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap g Λ) = LocNG.img g' (lattice₂ D Z.M p Λ)) ∧ ∀ h ∈ H0 F F', ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ y', LocOver (Formalism.HermitianLatticesTheory.gmap h Λ) y' ∧ RMoves h y y' := by
  intro D X Y u u' F F' w _ _ Z FP hB hRel
  refine ⟨fun g p => ⟨locEquiv p g, locEquiv_ext p g, fun g' h => locEquiv_unique p g g' h⟩,
    fun h hh p g' hg => localExtension_isometryFixingFrames_mem_localUnitary F F' Z FP hB h hh p g' hg, ?_, ?_⟩
  · intro g p g' Λ hg
    obtain rfl := locEquiv_unique p g g' hg
    exact (locEquiv_img Z p g Λ).symm
  · intro h hh Λ y hov
    have hmem : ∀ p, locEquiv p h ∈ (FP p).UW0 := fun p =>
      localExtension_isometryFixingFrames_mem_localUnitary F F' Z FP hB h hh p _ (locEquiv_ext p h)
    have hact := fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
      (finrank_Vp_eq p) (hRel p)
    choose act hmv _ using hact
    let y' : Dat Z FP := fun p => (act p).smul ⟨locEquiv p h, hmem p⟩ (y p)
    have hmoves : ∀ p, LocNG.Datum.Moves (locEquiv p h) (y p) (y' p) := fun p =>
      ((hmv p) ⟨locEquiv p h, hmem p⟩ (y p) (y' p)).2 rfl
    refine ⟨y', ⟨isLattice_gmap' h Λ hov.1, fun p => ?_⟩, fun p => ⟨locEquiv p h, locEquiv_ext p h, hmoves p⟩⟩
    obtain ⟨τ, hτ, hL⟩ := hov.2 p
    have hm := (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
      (finrank_Vp_eq p) (hRel p) (locEquiv p h) (hmem p) (y p) (y' p) τ hτ (hmoves p)).1
    refine ⟨_, hm, ?_⟩
    show LocNG.img (locEquiv p h) τ.abelian₂ = _
    rw [hL, locEquiv_img Z p h Λ]

end GlobalTheory.RatLocMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLatticesStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → (∀ (g : GV D) (p : PlF D), ∃! g', Ext p g g') ∧ (∀ h ∈ H0 F F', ∀ p g', Ext p h g' → g' ∈ (FP p).UW0) ∧ (∀ (g : GV D) p g' (Λ : LV D), Ext p g g' → lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap g Λ) = LocNG.img g' (lattice₂ D Z.M p Λ)) ∧ ∀ h ∈ H0 F F', ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ y', LocOver (Formalism.HermitianLatticesTheory.gmap h Λ) y' ∧ RMoves h y y' := by
  first | exact @GlobalTheory.RatLocMove.rat_ext_moves | exact GlobalTheory.RatLocMove.rat_ext_moves | (intros; apply GlobalTheory.RatLocMove.rat_ext_moves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.TauLipschitz

theorem trunc_pos (I : AutInst) (hn : 1 ≤ I.n) (x : I.GA) : 0 < tau1 I x :=
  lt_min (by norm_num) ((GlobalTheory.CountSteps.steps I x 1 one_pos).2.2.2.2.2.2.2.2 hn).1

theorem log_trunc_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 ∈ I.Kset) :
    Real.log (tau1 I x) - dSum I g.1 / I.f ≤ Real.log (tau1 I (x * g)) := by
  have h := GlobalTheory.LeastVar.truncatedLeastLatticeSize_rightTranslate_lower_bound I hn x g hg
  have hx := trunc_pos I hn x
  have h2 := Real.log_le_log (mul_pos hx (Real.exp_pos _)) h
  rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  unfold dSum
  linarith

theorem dSum_inv (I : AutInst) (hn : 1 ≤ I.n) (g : I.GA) : dSum I (g⁻¹).1 = dSum I g.1 := by
  unfold dSum
  refine Finset.sum_congr rfl fun v _ => ?_
  exact ((GlobalTheory.Count.Cartan.cartan_distances I.n (I.ε v)).2.1 (g.1 v) (g.1 v) hn).2.1

theorem tauLip : TauLip := by
  intro I hn
  refine ⟨trunc_pos I hn, (GlobalTheory.LeastVar.least_variation_continuity I hn).2.2, ?_, ?_⟩
  · rintro a ⟨γ, h1, h2, h3⟩ x
    unfold tau1
    rw [(GlobalTheory.PointEquivariance.equivariance I x γ a h1 h2 h3).2.2.1]
  · intro x g hg
    obtain ⟨-, -, -, -, -, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
    have hg' : (g⁻¹).2 ∈ I.Kset := by
      rw [← hK] at hg ⊢
      exact K.inv_mem hg
    have h1 := log_trunc_le I hn x g hg
    have h2 := log_trunc_le I hn (x * g) g⁻¹ hg'
    rw [mul_inv_cancel_right, dSum_inv I hn] at h2
    rw [abs_le]
    constructor <;> linarith

end GlobalTheory.TauLipschitz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzPropertiesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties : TauLip := by
  first | exact @GlobalTheory.TauLipschitz.tauLip | exact GlobalTheory.TauLipschitz.tauLip | (intros; apply GlobalTheory.TauLipschitz.tauLip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuous
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.RightRegProps


open GlobalTheory.RightRegFund in
theorem rightReg_unitary_mul_continuous : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → R 1 = ContinuousLinearMap.id ℂ _ ∧ (∀ x y, R (x * y) = (R x).comp (R y)) ∧ (∀ x F, ‖R x F‖ = ‖F‖) ∧ ∀ F, Continuous fun x => R x F := by
  intro I μf _ _ fund hfund R hR
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨Γ, hΓ, hc, -, hfd⟩ := GlobalTheory.RatDiscrete.rational_points I
  obtain ⟨hl, hrt, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf
  have hD := hfd μf fund hfund
  have : BorelSpace I.GA := inferInstance
  have : (I.muA μf).IsMulLeftInvariant := ⟨hl⟩
  have : (I.muA μf).IsMulRightInvariant := ⟨hrt⟩
  have : IsFiniteMeasureOnCompacts (I.muA μf) := by
    unfold AutInst.muA; infer_instance
  have hr : ∀ y, ∃ γ : Γ, I.rep fund y = (γ : I.GA) * y ∧ I.rep fund y ∈ fund := by
    intro y
    have h := hfund.2.1 y
    have e : I.rep fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  exact ⟨GlobalTheory.RightRegFund.map_one hD hfund.1 hr hR, GlobalTheory.RightRegFund.map_mul hD hfund.1 hr hR,
    GlobalTheory.RightRegFund.norm_map hD hfund.1 hr hR, GlobalTheory.RightRegFund.continuous_map hD hfund.1 hr hR⟩

end GlobalTheory.RightRegProps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuousStatement
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightRegularRepresentation_unitary_mul_continuous : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → R 1 = ContinuousLinearMap.id ℂ _ ∧ (∀ x y, R (x * y) = (R x).comp (R y)) ∧ (∀ x F, ‖R x F‖ = ‖F‖) ∧ ∀ F, Continuous fun x => R x F := by
  first | exact @GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous | exact GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous | (intros; apply GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ExtContRep

theorem comp_rep_ae_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Set G) (hΓ : Γ.Countable) (D : Set G) (hD : MeasurableSet D)
    (r : G → G) (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ r y ∈ D) (F f : G → ℂ)
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (h : F =ᵐ[μ.restrict D] f) :
    (fun y => F (r y)) =ᵐ[μ] f := by
  have h1 : ∀ᵐ x ∂μ, x ∈ D → F x = f x := (ae_restrict_iff' hD).1 h
  have h2 : ∀ᵐ x ∂μ, ∀ γ ∈ Γ, γ * x ∈ D → F (γ * x) = f (γ * x) :=
    (ae_ball_iff hΓ).2 fun γ _ => (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae h1
  filter_upwards [h2] with x hx
  obtain ⟨γ, hγ, e, hm⟩ := hr x
  rw [e] at hm ⊢
  rw [hx γ hγ hm, hf γ hγ]

theorem ae_ae_mul {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (μ ν : Measure G)
    [μ.IsMulLeftInvariant] [SFinite μ] [SFinite ν] (p : G → Prop) (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, p (m * x) := by
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have h0 : ∀ᵐ x ∂μ, x ∉ Z := measure_eq_zero_iff_ae_notMem.1 hZ0
  have hm : MeasurableSet {z : G × G | z.2 * z.1 ∉ Z} :=
    (measurable_snd.mul measurable_fst) hZm.compl
  have h1 : ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, m * x ∉ Z :=
    (Measure.ae_ae_comm (p := fun x m => m * x ∉ Z) hm).2
      (Filter.Eventually.of_forall fun m =>
        (measurePreserving_mul_left μ m).quasiMeasurePreserving.ae h0)
  filter_upwards [h1] with x hx
  filter_upwards [hx] with m hmx
  by_contra hp
  exact hmx (hZ hp)

theorem ext_ae_eq_contRep : ∀ (B : RowsAut) (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), IsContRep B y f → B.I.ext y =ᵐ[B.I.muA B.μf] f ∧ (∀ f', IsContRep B y f' → f' = f) ∧ (∀ g, IsContRep B (B.R g y) (fun x => f (x * g))) ∧ ∀ ν : Measure B.I.GA, IsFiniteMeasure ν → ∀ᵐ x ∂(B.I.muA B.μf), ∀ᵐ m ∂ν, B.I.ext y (m * x) = f (m * x) := by
  intro B y f hf
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨Γ, hΓ, hc, -, -⟩ := GlobalTheory.RatDiscrete.rational_points B.I
  obtain ⟨hl, hrt, -, -, hop⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : (B.I.muA B.μf).IsMulRightInvariant := ⟨hrt⟩
  have : (B.I.muA B.μf).IsOpenPosMeasure := ⟨fun U hU hne => (hop U hU hne).ne'⟩
  have : SFinite (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  have hcount : B.I.GFset.Countable := by
    rw [← hΓ]; exact Set.countable_coe_iff.1 hc
  have hr : ∀ z, ∃ γ ∈ B.I.GFset, B.I.rep B.fund z = γ * z ∧ B.I.rep B.fund z ∈ B.fund := by
    intro z
    have h := B.fund_spec.2.1 z
    have e : B.I.rep B.fund z = h.choose * z := by
      unfold AutInst.rep; exact dif_pos h
    exact ⟨h.choose, h.choose_spec.1, e, e ▸ h.choose_spec.2⟩
  have key : ∀ f', IsContRep B y f' → B.I.ext y =ᵐ[B.I.muA B.μf] f' := fun f' hf' =>
    comp_rep_ae_eq (B.I.muA B.μf) _ hcount _ B.fund_spec.1 _ hr _ f' hf'.2.1 hf'.2.2
  refine ⟨key f hf, fun f' hf' => ?_, fun g => ⟨?_, ?_, ?_⟩, fun ν hν => ?_⟩
  · exact (Continuous.ae_eq_iff_eq (B.I.muA B.μf) hf'.1 hf.1).1 ((key f' hf').symm.trans (key f hf))
  · exact hf.1.comp (continuous_id.mul continuous_const)
  · intro γ hγ x
    simp only [mul_assoc]
    exact hf.2.1 γ hγ _
  · refine (B.R_spec g y).trans (ae_restrict_of_ae ?_)
    exact (measurePreserving_mul_right (B.I.muA B.μf) g).quasiMeasurePreserving.ae (key f hf)
  · exact ae_ae_mul (B.I.muA B.μf) ν (fun x => B.I.ext y x = f x) (key f hf)

end GlobalTheory.ExtContRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OfClassification
namespace GlobalTheory.DiscreteSeriesConsequences

theorem of_classification : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Dec.LowKMultOne ∧ GlobalTheory.Dec.DSInfChar ∧
    GlobalTheory.Dec.DSExists ∧ GlobalTheory.Dec.DSUnique ∧ GlobalTheory.Published.DiscreteSeriesUpqExists := by
  intro h
  obtain ⟨hE, -, hU, hI, hM, -, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass (GlobalTheory.Published.discreteSeriesClassification_iff.1 h)
  exact ⟨hM, hI, hE, hU, GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE⟩

end GlobalTheory.DiscreteSeriesConsequences
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelic
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.RatDiscrete

theorem subgroup_countable_discrete : ∀ (I : AutInst), (∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset) ∧ I.GFset.Countable ∧ ∀ C : Set I.GA, IsCompact C → (I.GFset ∩ C).Finite :=
  fun I => ⟨⟨ratSub I, rfl⟩, countable_GFset I,
    fun _ hC => Set.inter_comm _ _ ▸ finite_inter I hC⟩

end GlobalTheory.RatDiscrete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelicStatement
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoints_countable_discrete_subgroup_adelic : ∀ (I : AutInst), (∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset) ∧ I.GFset.Countable ∧ ∀ C : Set I.GA, IsCompact C → (I.GFset ∩ C).Finite := by
  first | exact @GlobalTheory.RatDiscrete.subgroup_countable_discrete | exact GlobalTheory.RatDiscrete.subgroup_countable_discrete | (intros; apply GlobalTheory.RatDiscrete.subgroup_countable_discrete <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqCHolds
noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eqC_holds : EqC := by
  intro D X Y u t₁ t₂ h1 h2 h
  obtain ⟨l, m, l', m', c⟩ := t₁
  obtain ⟨l₂, m₂, l₂', m₂', c₂⟩ := t₂
  simp only at h1 h2
  subst h1 h2
  have hc : c = c₂ := by
    rw [← Quot.out_eq c, ← Quot.out_eq c₂]
    exact Quot.sound h
  subst hc
  rfl
end GlobalTheory.TypeAsm
end
end
