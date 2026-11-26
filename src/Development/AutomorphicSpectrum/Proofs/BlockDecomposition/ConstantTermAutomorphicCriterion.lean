module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion
noncomputable section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology

namespace GlobalTheory.CompanionTheory.CTFin.Central

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_unip_mul {r : ℕ} {φ : Sm E a} (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set f₀ := JointCont.finPart g x₀
  have hc : Continuous (fun x : BlockIx a r → Ad E => f₀⁻¹ * JointCont.finPart g x) :=
    continuous_const.mul (JointCont.continuous_finPart g)
  have h1 : finRep E a (f₀⁻¹ * f₀) φ = φ := by rw [inv_mul_cancel]; simp
  have hev : ∀ᶠ x in 𝓝 x₀, chart φ.1 (finGL E a f₀) (toL (JointCont.infPart g x).val) = φ.1 (unip x * g) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hφ.mem_nhds h1)] with x hx
    have hx' : finRep E a (f₀⁻¹ * JointCont.finPart g x) φ = φ := hx
    have e : unip x * g = finGL E a f₀ * infGL E a (JointCont.infPart g x) * finGL E a (f₀⁻¹ * JointCont.finPart g x) := by
      rw [JointCont.unip_mul_eq, mul_assoc, infGL_comm, ← mul_assoc, ← map_mul (finGL E a), mul_inv_cancel_left]
    rw [chart_val, e]
    exact (congrArg (fun ψ : Sm E a => ψ.1 (finGL E a f₀ * infGL E a (JointCont.infPart g x))) hx').symm
  have hA : ContinuousAt (fun x : BlockIx a r → Ad E => chart φ.1 (finGL E a f₀) (toL (JointCont.infPart g x).val)) x₀ :=
    ContinuousAt.comp (g := chart φ.1 (finGL E a f₀))
      ((φ.2 _).continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _)))
      (JointCont.continuous_infPart g).continuousAt
  exact hA.congr hev

theorem exists_bound_unip_mul {r : ℕ} {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    ∃ C, ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * g)‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hKc : IsCompact (Set.univ.pi fun _ : BlockIx a r => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (continuous_unip_mul (r := r) hφ g).continuousOn
  refine ⟨C, fun x => ?_⟩
  choose q hq using fun p => hcov (x p)
  have hx : x = (fun p => algebraMap E (Ad E) (q p)) + fun p => x p - algebraMap E (Ad E) (q p) := by
    funext p
    show x p = algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p))
    exact (add_sub_cancel _ _).symm
  have hper : φ.1 (unip x * g) = φ.1 (unip (fun p => x p - algebraMap E (Ad E) (q p)) * g) := by
    conv_lhs => rw [hx]
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  rw [hper]
  exact hC _ fun p _ => hq p

theorem integrable_unip_mul {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx a r → Ad E))
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Integrable (fun x => φ.1 (unip x * g)) (μ.restrict 𝓕) := by
  have hfin := covol_lt_top μ 𝓕 h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := exists_bound_unip_mul (r := r) hl hφ g
  exact Integrable.of_bound (continuous_unip_mul hφ g).aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem ct_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → (∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ (X : Lie E a) (g : GA E a), (lie E a X F).1 g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ) → ∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ z ∈ Zalg E a, ∀ g, (z F).1 g = ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hμ h𝓕 hlie
  haveI := hμ
  let P : Sm E a → Prop := fun φ =>
    (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ}
  have hadd : ∀ φ ψ : Sm E a, P φ → P ψ → P (φ + ψ) := fun φ ψ h1 h2 =>
    ⟨fun γ g => by
      change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
      rw [h1.1, h2.1],
     (GlobalTheory.PRep.smoothPart (finRep E a)).add_mem (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h1.2)
       (show ψ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h2.2)⟩
  have hsmul : ∀ (c : ℂ) (φ : Sm E a), P φ → P (c • φ) := fun c φ h1 =>
    ⟨fun γ g => by
      change c • φ.1 _ = c • φ.1 _
      rw [h1.1],
     (GlobalTheory.PRep.smoothPart (finRep E a)).smul_mem c (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h1.2)⟩
  have hint : ∀ ψ : Sm E a, P ψ → ∀ g, Integrable (fun x => ψ.1 (unip x * g)) (μ.restrict 𝓕) :=
    fun ψ h g => integrable_unip_mul μ 𝓕 h𝓕 h.1 h.2 g
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {T | ∀ φ, P φ → P (T φ) ∧ ∀ F : Sm E a, (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
          ∀ g, (T F).1 g = ∫ x in 𝓕, (T φ).1 (unip x * g) ∂μ}
      mul_mem' := fun {T₁ T₂} hT₁ hT₂ φ hφ => by
        obtain ⟨h1, e1⟩ := hT₂ φ hφ
        obtain ⟨h2, e2⟩ := hT₁ _ h1
        exact ⟨h2, fun F hF g => e2 (T₂ F) (e1 F hF) g⟩
      add_mem' := fun {T₁ T₂} hT₁ hT₂ φ hφ => by
        obtain ⟨h1, e1⟩ := hT₁ φ hφ
        obtain ⟨h2, e2⟩ := hT₂ φ hφ
        refine ⟨hadd _ _ h1 h2, fun F hF g => ?_⟩
        change (T₁ F).1 g + (T₂ F).1 g = ∫ x in 𝓕, ((T₁ φ).1 (unip x * g) + (T₂ φ).1 (unip x * g)) ∂μ
        rw [integral_add (hint _ h1 g) (hint _ h2 g), e1 F hF g, e2 F hF g]
      algebraMap_mem' := fun c φ hφ => by
        refine ⟨by rw [Module.algebraMap_end_apply]; exact hsmul c φ hφ, fun F hF g => ?_⟩
        rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
        change c • F.1 g = ∫ x in 𝓕, c • φ.1 (unip x * g) ∂μ
        rw [integral_smul, hF g] }
  have hL : ∀ X, lie E a X ∈ S := fun X φ hφ =>
    ⟨⟨fun γ g => GlobalTheory.SpehInfChar.lie_leftInv (ratGL E a).range X
        (fun u hu g' => by obtain ⟨γ', rfl⟩ := MonoidHom.mem_range.1 hu; exact hφ.1 γ' g') _ ⟨γ, rfl⟩ g,
      GlobalTheory.SpehInfChar.lie_mem_smoothPart X (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from hφ.2)⟩,
     fun F hF g => hlie φ F hφ.1 hφ.2 hF X g⟩
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  intro φ F hl hlev hF z hz g
  have hzS : z ∈ S := by
    refine (Algebra.adjoin_le (S := S) ?_) hz
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hzS φ ⟨hl, hlev⟩).2 F hF g

end GlobalTheory.CompanionTheory.CTFin.Central
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterionStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_automorphic_criterion : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → (∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ (X : Lie E a) (g : GA E a), (lie E a X F).1 g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ) → ∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ z ∈ Zalg E a, ∀ g, (z F).1 g = ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Central.ct_Zalg | exact GlobalTheory.CompanionTheory.CTFin.Central.ct_Zalg | (intros; apply GlobalTheory.CompanionTheory.CTFin.Central.ct_Zalg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEuclideanModel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEuclideanModel
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

noncomputable section

namespace GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ}

def dualCoord (E : KMod n) :
    (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) where
  toFun ξ := WithLp.toLp 2 fun i => ξ (stdOrthonormalBasis ℂ E.V i)
  map_add' x y := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp
  invFun v := ∑ i, v i • innerSL ℂ (stdOrthonormalBasis ℂ E.V i)
  left_inv ξ := by
    ext x
    have hx := (stdOrthonormalBasis ℂ E.V).sum_repr' x
    conv_rhs => rw [← hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, mul_comm]
  right_inv v := by
    ext j
    have ho := (stdOrthonormalBasis ℂ E.V).orthonormal
    simp [orthonormal_iff_ite.mp ho]

theorem norm_dualCoord (E : KMod n) (ξ : E.V →L[ℂ] ℂ) : ‖dualCoord E ξ‖ = ‖ξ‖ := by
  set r := (InnerProductSpace.toDual ℂ E.V).symm ξ with hr
  have h1 : ‖r‖ = ‖ξ‖ := (InnerProductSpace.toDual ℂ E.V).symm.norm_map ξ
  have h2 : ‖(stdOrthonormalBasis ℂ E.V).repr r‖ = ‖r‖ :=
    (stdOrthonormalBasis ℂ E.V).repr.norm_map r
  rw [← h1, ← h2, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : (dualCoord E ξ) i = ξ (stdOrthonormalBasis ℂ E.V i) := rfl
  rw [h3, OrthonormalBasis.repr_apply_apply, ← InnerProductSpace.toDual_symm_apply (𝕜 := ℂ), ← hr,
    norm_inner_symm]

def dualAct (E : KMod n) : (E.V →L[ℂ] E.V) →ₗ[ℂ]
    (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) where
  toFun T := LinearMap.toContinuousLinearMap
    ((dualCoord E).toLinearMap ∘ₗ
      (((ContinuousLinearMap.compL ℂ E.V E.V ℂ).flip T : (E.V →L[ℂ] ℂ) →L[ℂ] (E.V →L[ℂ] ℂ)) :
        (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ∘ₗ (dualCoord E).symm.toLinearMap)
  map_add' S T := by
    ext v : 1
    simp
  map_smul' c T := by
    ext v : 1
    simp

theorem dualAct_apply (E : KMod n) (T : E.V →L[ℂ] E.V) (v) :
    dualAct E T v = dualCoord E ((dualCoord E).symm v ∘L T) := by
  simp [dualAct]

theorem continuous_unitary_inv :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => k⁻¹ := by
  refine Continuous.subtype_mk (p := (· ∈ Matrix.unitaryGroup (Fin n) ℂ)) ?_ _
  simpa using (continuous_subtype_val.star :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => star k.1)

theorem dualRep_exists {n : ℕ} (E : KMod n) :
    ∃ (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))
      (ρ' : Matrix.unitaryGroup (Fin n) ℂ →*
        (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
          EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))),
      Continuous ρ' ∧ (∀ k v, ‖ρ' k v‖ = ‖v‖) ∧ ∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ) := by
  have hact : ∀ k ξ, dualAct E (E.ρ k⁻¹) (dualCoord E ξ) = dualCoord E (ξ ∘L E.ρ k⁻¹) := by
    intro k ξ
    rw [dualAct_apply, LinearEquiv.symm_apply_apply]
  let ρ' : Matrix.unitaryGroup (Fin n) ℂ →*
      (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
        EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) :=
    { toFun := fun k => dualAct E (E.ρ k⁻¹)
      map_one' := by
        ext1 v
        rw [dualAct_apply, inv_one, map_one]
        change dualCoord E ((dualCoord E).symm v ∘L ContinuousLinearMap.id ℂ E.V) = v
        rw [ContinuousLinearMap.comp_id, LinearEquiv.apply_symm_apply]
      map_mul' := by
        intro k l
        ext1 v
        obtain ⟨ξ, rfl⟩ := (dualCoord E).surjective v
        rw [ContinuousLinearMap.mul_apply, hact l, hact k, hact (k * l), _root_.mul_inv_rev, map_mul]
        rfl }
  refine ⟨dualCoord E, ρ', ?_, ?_, fun k ξ => (hact k ξ).symm⟩
  · have h1 : Continuous (dualAct E) := LinearMap.continuous_of_finiteDimensional _
    exact h1.comp (E.cont.comp continuous_unitary_inv)
  · intro k v
    obtain ⟨ξ, rfl⟩ := (dualCoord E).surjective v
    have hle : ∀ (l : Matrix.unitaryGroup (Fin n) ℂ) (η : E.V →L[ℂ] ℂ), ‖η ∘L E.ρ l‖ ≤ ‖η‖ := by
      intro l η
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      simpa [E.iso] using η.le_opNorm (E.ρ l x)
    have hback : (ξ ∘L E.ρ k⁻¹) ∘L E.ρ k = ξ := by
      ext x
      have : E.ρ k⁻¹ (E.ρ k x) = x := by
        have h := congrArg (fun T : E.V →L[ℂ] E.V => T x) (E.ρ.map_mul k⁻¹ k)
        simpa using h.symm
      simp [this]
    have h2 : ‖ξ ∘L E.ρ k⁻¹‖ = ‖ξ‖ := by
      refine le_antisymm (hle _ _) ?_
      calc ‖ξ‖ = ‖(ξ ∘L E.ρ k⁻¹) ∘L E.ρ k‖ := by rw [hback]
        _ ≤ _ := hle _ _
    change ‖dualAct E (E.ρ k⁻¹) (dualCoord E ξ)‖ = _
    rw [hact, norm_dualCoord, norm_dualCoord, h2]

end GlobalTheory.CompanionTheory.RealCount
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEuclideanModelStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_euclidean_model : ∀ {n : ℕ} (E : KMod n), ∃ (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) (ρ' : Matrix.unitaryGroup (Fin n) ℂ →* (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))), Continuous ρ' ∧ (∀ k v, ‖ρ' k v‖ = ‖v‖) ∧ ∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.dualRep_exists | exact GlobalTheory.CompanionTheory.RealCount.dualRep_exists | (intros; apply GlobalTheory.CompanionTheory.RealCount.dualRep_exists <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentSurjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentSurjective
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir.GpExists

section Entries

variable {k : Type} [Field k]

theorem unip_apply_of_ne_last (n : ℕ) (v : Multiplicative (Fin n → k)) (p q : Fin (n + 1)) (hq : q ≠ Fin.last n) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p q =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p q := by
  show (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) p q = _
  simp [GlobalTheory.BZMir.colMat, hq]

theorem unip_apply_last_last (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  show (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.last n) (Fin.last n) = 1
  simp [GlobalTheory.BZMir.colMat]

end Entries

theorem blockIndex_false_val (m j : ℕ) (a : Fin m) : (eGP m j ⟨false, a⟩ : Fin (m + j + 1)).val = a.val := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.stdSum]

theorem blockIndex_true_val (m j : ℕ) (b : Fin (j + 1)) : (eGP m j ⟨true, b⟩ : Fin (m + j + 1)).val = m + b.val := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.stdSum]

end GlobalTheory.CompanionTheory.BZMir.GpExists

namespace GlobalTheory.CompanionTheory.BZMir

open GpExists

theorem exists_gpProj_unip (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (u : Mir k j) (hu : u ∈ MirUin k j) :
    ∃ v : MirabolicParabolic k m j, (v : Mir k (m + j)) ∈ MirUin k (m + j) ∧ gpProj k m j v = (1, u) := by
  have hu' : (u : GL (Fin (j + 1)) k) ∈ GlobalTheory.BZMir.MirU k j := by
    unfold GlobalTheory.BZMir.MirUin at hu
    exact Subgroup.mem_subgroupOf.1 hu
  unfold GlobalTheory.BZMir.MirU at hu'
  rw [MonoidHom.mem_range] at hu'
  obtain ⟨w, hw⟩ := hu'
  set v' : Multiplicative (Fin (m + j) → k) :=
    Multiplicative.ofAdd (Fin.append (0 : Fin m → k) (Multiplicative.toAdd w)) with hv'
  have hU : GlobalTheory.BZMir.unip k (m + j) v' ∈ GlobalTheory.BZMir.MirU k (m + j) := by
    unfold GlobalTheory.BZMir.MirU
    exact MonoidHom.mem_range.2 ⟨v', rfl⟩
  have hM : GlobalTheory.BZMir.unip k (m + j) v' ∈ GlobalTheory.BZMir.Mir k (m + j) :=
    GlobalTheory.BZMir.MirU_le_Mir k (m + j) hU
  have hP : (⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩ : GlobalTheory.BZMir.Mir k (m + j)) ∈
      GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
    unfold GlobalTheory.BZMir.Leib.MirabolicParabolic
    rw [Subgroup.mem_comap]
    show GlobalTheory.BZMir.unip k (m + j) v' ∈ _
    refine (GlobalTheory.SmGL.mem_parab_two k).2 (fun b a => ?_)
    rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last]
    · exact Matrix.one_apply_ne (fun h => by simpa using Equiv.injective _ h)
    · exact GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a
  refine ⟨⟨⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩, hP⟩, ?_, ?_⟩
  · unfold GlobalTheory.BZMir.MirUin
    exact Subgroup.mem_subgroupOf.2 hU
  apply Prod.ext
  · apply Units.ext
    ext a a'
    simp only [GlobalTheory.BZMir.Leib.gpProj, MonoidHom.prod_apply, MonoidHom.comp_apply,
      Pi.evalMonoidHom_apply]
    rw [GlobalTheory.SmGL.leviProj_apply]
    change ((GlobalTheory.BZMir.unip k (m + j) v' : GL (Fin (m + j + 1)) k) :
      Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _ = _
    rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a')]
    by_cases h : a = a'
    · subst h
      simp
    · rw [Matrix.one_apply_ne ((GlobalTheory.BZMir.Leib.eGP m j).injective.ne (by simpa using h)),
        Units.val_one, Matrix.one_apply_ne h]
  · apply Subtype.ext
    apply Units.ext
    ext b b'
    first
    | (show ((GlobalTheory.SmGL.leviProj k (GlobalTheory.BZMir.Leib.eGP m j)
          (GlobalTheory.BZMir.Leib.hgpIncl k m j ⟨⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩, hP⟩) true :
          GL _ k) : Matrix _ _ k) b b' = _
       rw [GlobalTheory.SmGL.leviProj_apply])
    | (simp only [GlobalTheory.BZMir.Leib.gpProj, MonoidHom.prod_apply, MonoidHom.codRestrict_apply,
          MonoidHom.coe_codRestrict, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Subgroup.coe_mk]
       rw [GlobalTheory.SmGL.leviProj_apply])
    change ((GlobalTheory.BZMir.unip k (m + j) v' : GL (Fin (m + j + 1)) k) :
      Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _ = _
    rw [← hw]
    induction b' using Fin.lastCases with
    | last =>
      rw [GlobalTheory.BZMir.Leib.blockIndex_true_last]
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.BZMir.Leib.blockIndex_true_last, GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_last_last,
          GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_last_last]
      | cast i =>
        have hidx : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i⟩ = Fin.castSucc (Fin.natAdd m i) :=
          Fin.ext (by simp [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_true_val])
        rw [hidx, GlobalTheory.BZMir.unip_apply_castSucc_last, GlobalTheory.BZMir.unip_apply_castSucc_last, hv']
        simp
    | cast i =>
      have hne : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i⟩ ≠ Fin.last (m + j) :=
        fun h => Fin.castSucc_ne_last i ((GlobalTheory.BZMir.Leib.blockIndex_true_eq_last_iff m j _).1 h)
      rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ hne,
        GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ (Fin.castSucc_ne_last i)]
      by_cases h : b = Fin.castSucc i
      · subst h
        simp
      · rw [Matrix.one_apply_ne ((GlobalTheory.BZMir.Leib.eGP m j).injective.ne (by simpa using h)),
          Matrix.one_apply_ne h]

end GlobalTheory.CompanionTheory.BZMir

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentSurjectiveStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_unipotent_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (u : Mir k j), u ∈ MirUin k j → ∃ v : MirabolicParabolic k m j, (v : Mir k (m + j)) ∈ MirUin k (m + j) ∧ gpProj k m j v = (1, u) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip | exact GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip | (intros; apply GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.IwJac

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

variable {k n}

def tor (ϖ : kˣ) (x : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => ϖ ^ x i

end GlobalTheory.CompanionTheory.IwJac

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSingleNonzeroFactorEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSingleNonzeroFactorEquiv
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd.ProdSingle

theorem prodIrr_single : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (Y : Fin h → IrrGL (k := k)) (hd : ∑ a, (Y a).1 = N) (i₀ : Fin h), (∀ i, i ≠ i₀ → (Y i).1 = 0) → ∃ z : IrrCl (GL (Fin N) k), (⟨N, z⟩ : IrrGL (k := k)) = Y i₀ ∧ Nonempty ((prodIrr Y hd).Equiv z.rep.ρ) := by
  intro k _ _ _ _ h N Y hd i₀ h0
  have hN : (Y i₀).1 = N := by
    rw [← hd]
    exact (Finset.sum_eq_single i₀ (fun i _ hi => h0 i hi) (fun hi => absurd (Finset.mem_univ _) hi)).symm
  subst hN
  refine ⟨(Y i₀).2, Sigma.eta _, ?_⟩
  have hd' : ∑ a : Fin 1, (Y ((fun _ : Fin 1 => i₀) a)).1 = (Y i₀).1 := by simp
  obtain ⟨e₁⟩ := GlobalTheory.T.induced_product_drop_zero_factors Y hd (fun _ : Fin 1 => i₀) (Subsingleton.strictMono _)
    (fun j hj => ⟨0, by
      by_contra hne
      exact hj (h0 j (fun e => hne e.symm))⟩) hd'
  obtain ⟨e₂⟩ := nonempty_equiv_prodIrr_one (Y i₀) hd'
  exact ⟨e₁.trans e₂.symm⟩

end GlobalTheory.CompanionTheory.FineProd.ProdSingle
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSingleNonzeroFactorEquivStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_single_nonzero_factor_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (Y : Fin h → IrrGL (k := k)) (hd : ∑ a, (Y a).1 = N) (i₀ : Fin h), (∀ i, i ≠ i₀ → (Y i).1 = 0) → ∃ z : IrrCl (GL (Fin N) k), (⟨N, z⟩ : IrrGL (k := k)) = Y i₀ ∧ Nonempty ((prodIrr Y hd).Equiv z.rep.ρ) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single | exact GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single | (intros; apply GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
noncomputable section

open Matrix Finset

namespace GlobalTheory.CompanionTheory.RealCount.Tope

variable {n : ℕ}

abbrev LP (n : ℕ) := AddMonoidAlgebra ℂ (Fin n → ℤ)

def chr (z : Fin n → ℂˣ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun μ := ∏ a, ((z a ^ (Multiplicative.toAdd μ a) : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' μ ν := by
    simp only [toAdd_mul, Pi.add_apply, _root_.zpow_add, Units.val_mul, Finset.prod_mul_distrib]

def evL (z : Fin n → ℂˣ) : LP n →ₐ[ℂ] ℂ := AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (chr z)

def altL (m : Fin n → ℤ) : LP n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • AddMonoidAlgebra.single (fun i => m (σ i)) (1 : ℂ)

def delZ (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def pPL (n : ℕ) : LP n :=
  ∏ a : Fin n, ∏ b : Fin n, (1 + AddMonoidAlgebra.single (Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) (1 : ℂ))

def frL (n : ℕ) : LP n →ₐ[ℂ] LP n :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (2 • AddMonoidHom.id (Fin n → ℤ))

def cPoly (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) : LP n :=
  ∑ μ ∈ s, AddMonoidAlgebra.single μ (c μ)

end GlobalTheory.CompanionTheory.RealCount.Tope
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeStable
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount.KHw

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)

variable {n : ℕ}

section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

theorem glRel_kF {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have c1 := h.comm a b c d
  have c2 := h.comm c d a b
  have key : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add, c1, ← c2]
    abel
  rw [key, h1, h2]
  simp only [kF]
  split_ifs <;> abel

end

end GlobalTheory.CompanionTheory.RealCount.KHw
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetRepsUnipotent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemInfConjOfIsDom
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_mem_inf_conj_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∀ y ∈ D.J,
      ∃ a ∈ D.J ⊓ D.N, a⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht y hy
  obtain ⟨c, hc, b, hb, a, ha, rfl⟩ := D.fact_up y hy
  have hb' : b ∈ D.J := (Subgroup.mem_inf.1 hb).1
  have ha' : a ∈ D.J := (Subgroup.mem_inf.1 ha).1
  have hbt : (t : G)⁻¹ * b * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.2 b hb).2).1
  have hat : (t : G)⁻¹ * a * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.1 a ha)).1
  have he : c⁻¹ * (c * b * a) = b * a := by group
  refine ⟨c, hc, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [he]
    exact D.J.mul_mem hb' ha'
  · rw [he, Subgroup.mem_map]
    refine ⟨((t : G)⁻¹ * b * t) * ((t : G)⁻¹ * a * t), D.J.mul_mem hbt hat, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.CompanionTheory.Casselman
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetRepsUnipotent
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_fin_coset_reps_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G,
      (∀ i, x i ∈ D.J ⊓ D.N) ∧
        ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht
  exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps G D.J
    (D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom) (D.J ⊓ D.N)
    D.isCompact_J (GlobalTheory.CompanionTheory.TopGroup.inter_conj_isOpen G D.J D.isOpen_J (t : G)) inf_le_left inf_le_left
    (exists_mem_inf_conj_of_isDom G D t ht)

end GlobalTheory.CompanionTheory.Casselman
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetRepsUnipotentStatement
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_coset_reps_unipotent : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ D.J ⊓ D.N) ∧ ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom | exact GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom | (intros; apply GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFundamentalDomainGL
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMeasurableIsFundamentalDomain
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.LatticeFD

theorem exists_measurable_isFundamentalDomain (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ)
    [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] :
    ∃ 𝓕 : Set (GA E N), MeasurableSet 𝓕 ∧ ∀ μ : Measure (GA E N), IsFundamentalDomain (latticeGL E N) 𝓕 μ :=
  ⟨GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E N), GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom _,
    fun μ => GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ⟩

end GlobalTheory.CompanionTheory.LatticeFD

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFundamentalDomainGL
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc

theorem exists_isFundamentalDomain_of_isSqInt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
      (μ : Measure (GA E N)) [μ.IsHaarMeasure] (φ : GA E N → ℂ), IsSqInt φ →
      ∃ F : Set (GA E N), IsFundamentalDomain (latticeGL E N) F μ := by
  intro E _ _ _ N _ _ μ _ φ _
  obtain ⟨F, -, hF⟩ := GlobalTheory.CompanionTheory.LatticeFD.exists_measurable_isFundamentalDomain E N
  exact ⟨F, hF μ⟩

end GlobalTheory.CompanionTheory.FinDisc

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFundamentalDomainGLStatement
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamental_domain_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (φ : GA E N → ℂ), IsSqInt φ →
  ∃ F : Set (GA E N), IsFundamentalDomain (latticeGL E N) F μ := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.exists_isFundamentalDomain_of_isSqInt | exact GlobalTheory.CompanionTheory.FinDisc.exists_isFundamentalDomain_of_isSqInt | (intros; apply GlobalTheory.CompanionTheory.FinDisc.exists_isFundamentalDomain_of_isSqInt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateUnramifiedDegreeOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateUnramifiedDegreeOne
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem lt_local_artin_inertia : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {Ωv : Type} [Field Ωv] [ValuativeRel Ωv] [TopologicalSpace Ωv] [IsValuativeTopology Ωv]
    [Algebra F Ωv] [ValuativeExtension F Ωv] [IsSepClosure F Ωv] [IsSepClosed Ωv]
    {π : 𝒪[F]} (hπ : Irreducible π) {f : PowerSeries 𝒪[F]} (hf : IsLubinTateSeries π f)
    (u : 𝒪[F]ˣ) (τ : Ωv ≃ₐ[F] Ωv), unramifiedDegree F Ωv τ = 1 →
    (∀ n, ∀ x ∈ lubinTateTorsion Ωv (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = (u : 𝒪[F]) • x) →
    ∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension F Ωv),
    ((localArtinMap F Ωv (unitsIncl F u⁻¹) ⟨y, hy⟩ : maximalAbelianExtension F Ωv) : Ωv) = τ y := by
  intro F _ _ _ _ Ωv _ _ _ _ _ _ _ _ π hπ f hf u τ hτd hτ y hy
  obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
  obtain ⟨n, m, h⟩ := exists_le_lubinTateField_sup_unramifiedTower hπ hf L
  have hE := isUnramifiedSubextension_unramifiedTower (K := F) (Ω := Ωv) m
  have := hE.1
  have := hE.isGalois
  have hab := isAbelianGalois_lubinTateField_sup hπ hf n.succ_pos hE
  have key := restrictAb_localArtinMap_lubinTate hπ hf n.succ_pos (unramifiedTower F Ωv m)
    hE.le_maximalUnramifiedExtension u⁻¹ 0 τ (by rw [hτd]; simp)
    (by intro x hx; rw [inv_inv]; exact hτ _ x hx)
  have hx : unitUniformizerPow hπ u⁻¹ 0 = unitsIncl F u⁻¹ := by
    rw [unitUniformizerPow_eq, zpow_zero, one_mul]
  rw [hx] at key
  have h2 := congrArg (fun σ => ((σ ⟨y, h hyL⟩ : (lubinTateField Ωv hπ hf (n + 1) ⊔ unramifiedTower F Ωv m : IntermediateField F Ωv)) : Ωv)) key
  simp only [restrictAb_apply, AlgEquiv.restrictNormalHom_apply] at h2
  exact h2

end GlobalTheory.CompanionTheory.LTLink
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateUnramifiedDegreeOneStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_unramified_degree_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {Ωv : Type} [Field Ωv] [ValuativeRel Ωv] [TopologicalSpace Ωv] [IsValuativeTopology Ωv]
    [Algebra F Ωv] [ValuativeExtension F Ωv] [IsSepClosure F Ωv] [IsSepClosed Ωv]
    {π : 𝒪[F]} (hπ : Irreducible π) {f : PowerSeries 𝒪[F]} (hf : IsLubinTateSeries π f)
    (u : 𝒪[F]ˣ) (τ : Ωv ≃ₐ[F] Ωv), unramifiedDegree F Ωv τ = 1 →
    (∀ n, ∀ x ∈ lubinTateTorsion Ωv (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = (u : 𝒪[F]) • x) →
    ∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension F Ωv),
    ((localArtinMap F Ωv (unitsIncl F u⁻¹) ⟨y, hy⟩ : maximalAbelianExtension F Ωv) : Ωv) = τ y := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia | exact GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia | (intros; apply GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotient
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.ContraSub

open GlobalTheory.ContraRefl

section General

variable {G V X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

def incl {π : Representation ℂ G V} (S : Subrepresentation π) :
    S.toRepresentation.IntertwiningMap π where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := by ext _; rfl

theorem isSmooth_sub {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) :
    IsSmooth S.toRepresentation := fun x => by
  have : {g : G | S.toRepresentation g x = x} = {g : G | π g x.1 = x.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact hπ x.1

theorem contraMap_incl_surjective
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) :
    Function.Surjective (contraMap (incl S)) := by
  intro l
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra S.toRepresentation l).mem_nhds (by simp))
  have hlK : l ∈ fixed (contra S.toRepresentation) K := mem_fix.2 fun h hh => hKs hh
  obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend (l : Module.Dual ℂ S.toSubmodule)
  obtain ⟨l', h1, h2⟩ := exists_fixed_contra hπ ho hc (l₀ ∘ₗ (fixed π K).subtype)
  have hl'K : l' ∈ fixed (contra π) K := mem_fix.2 h1
  refine ⟨l', Subtype.ext (form_ext (isSmooth_sub hπ S) hc (fun h hh w => ?_) (fun h hh w => ?_)
    fun w hw => ?_)⟩
  · exact invariant_of_fixed ⟨l', hl'K⟩ h hh (w : V)
  · exact invariant_of_fixed ⟨l, hlK⟩ h hh w
  · have hwK : (w : V) ∈ fixed π K :=
      mem_fix.2 fun h hh => congrArg Subtype.val (mem_fix.1 hw h hh)
    have e1 := h2 ⟨w, hwK⟩
    have e2 := LinearMap.congr_fun hl₀ w
    exact e1.trans e2

theorem contraMap_injective {Y : Type} [AddCommGroup Y] [Module ℂ Y] {σ : Representation ℂ G X}
    {τ : Representation ℂ G Y} (f : σ.IntertwiningMap τ) (hf : Function.Surjective f) :
    Function.Injective (contraMap f) := by
  intro l l' h
  refine Subtype.ext (LinearMap.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := hf y
  exact LinearMap.congr_fun (congrArg Subtype.val h) x

theorem isSubquotient_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {σ : Representation ℂ G X} {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (h : IsSubquotient σ ρ) : IsSubquotient (contra σ) (contra ρ) := by
  obtain ⟨S, f, hf⟩ := h
  exact (IsSubquotient.of_injective (contraMap f) (contraMap_injective f hf)).trans
    (IsSubquotient.of_surjective (contraMap (incl S)) (contraMap_incl_surjective hG hρ S))

end General

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin N) k) V) (ρ : Representation ℂ (GL (Fin N) k) W),
    IsSmooth σ → IsSmooth ρ → IsSubquotient σ ρ → IsSubquotient (contra σ) (contra ρ) := by
  intro k _ _ _ _ N V W _ _ _ _ σ ρ _ hρ h
  refine isSubquotient_contra (fun U hU => ?_) hρ h
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin N) U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end GlobalTheory.CompanionTheory.ContraSub
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensorRank

theorem rank_piTensorProduct_le_one {α : Type} [Fintype α] (M : α → Type)
    [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)]
    (h : ∀ a, Module.rank ℂ (M a) ≤ 1) : Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  choose v₀ hv₀ using fun a => rank_le_one_iff.mp (h a)
  rw [rank_le_one_iff]
  refine ⟨PiTensorProduct.tprod ℂ v₀, fun x => ?_⟩
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r f
    choose c hc using fun a => hv₀ a (f a)
    refine ⟨r * ∏ a, c a, ?_⟩
    have hf : f = fun a => c a • v₀ a := funext fun a => (hc a).symm
    rw [hf, MultilinearMap.map_smul_univ, mul_smul]
    simp only [RingHom.id_apply]
  · rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by rw [add_smul, hr, hs]⟩

end GlobalTheory.CompanionTheory.TensorRank
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOneStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_rank_le_one : ∀ {α : Type} [Fintype α] (M : α → Type) [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)], (∀ a, Module.rank ℂ (M a) ≤ 1) → Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one | exact GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one | (intros; apply GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOne
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgGu

theorem rank_twJacquet_multiProd_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (ψ : AddChar k Circle) (hc : Continuous ψ)
    (h1 : ψ ≠ 1) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : ∀ a, IsSmooth (π a))
    (hr : ∀ a, Module.rank ℂ (TwJacquet (π a) (unipB k (Fin (d a))) (whitChar ψ (d a))) ≤ 1) :
    Module.rank ℂ (TwJacquet (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  obtain ⟨e⟩ := hH ψ hc h1 h N d hd X π hs
  exact e.rank_eq.le.trans (GlobalTheory.T.tensor_product_rank_le_one _ hr)

theorem rank_twJacquet_prodIrr_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k →
    ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k))
      (hd : ∑ a, (x a).1 = N),
      Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  intro k _ _ _ _ hH hR ψ hc h1 h N x hd
  exact rank_twJacquet_multiProd_le_one hH ψ hc h1 h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V)
    (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)
    (fun a => hR ψ hc h1 (x a).1 (x a).2.rep.V (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)

end GlobalTheory.CompanionTheory.RgGu

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOneStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_rank_product_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one | exact GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one | (intros; apply GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one <;> assumption)
end
end
