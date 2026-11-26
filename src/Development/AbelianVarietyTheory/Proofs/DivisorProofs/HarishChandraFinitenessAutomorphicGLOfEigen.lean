module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeRealSpecialUnitaryEqFlagDomainMass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessAutomorphicGLOfEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalMatrixCoefficientSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalMatrixCoefficientSpan
namespace GlobalTheory.Proof.CoeffSpan

theorem finiteDimensional_coeffSpan (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun φ k => φ (ρ k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    refine ⟨{ toFun := fun A => ℓ (A w), map_add' := fun A B => by simp, map_smul' := fun c A => by simp }, ?_⟩
    rfl
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.Proof.CoeffSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalMatrixCoefficientSpanStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_matrixCoefficientSpan : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W), FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first | exact @GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan | exact GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan | (intros; apply GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessAutomorphicGLOfEigen
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

theorem automorphicFormsFiniteGL_of_core (h : CoreFiniteGL) : GlobalTheory.Published.AutomorphicFormsFiniteGL := by
  intro E _ _ _ a L hL W _ _ _ ρ _ c
  classical
  haveI hW' : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := GlobalTheory.T.finiteDimensional_matrixCoefficientSpan _ W ρ
  let χ : Module.End ℂ (Sm E a) → ℂ := fun z =>
    if hz : ∃ s : ℂ, ∀ φ : Sm E a, (∀ τ u, cap τ u φ = c τ u • φ) → z φ = s • φ then hz.choose else 0
  have hsub : GlobalTheory.Published.AutFinGL.forms L ρ c ⊆ formsGL E a L (GlobalTheory.Published.AutFin.coeffSpan ρ) {χ} 1 := by
    rintro φ ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, χ, rfl, ?_⟩
    intro zs hlen hzs
    match zs, hlen with
    | [z], _ =>
      have hz : z ∈ Zalg E a := hzs z (List.mem_singleton_self z)
      have hex := GlobalTheory.T.center_acts_by_scalar_on_eigenforms E a c z hz
      have hχ : χ z = hex.choose := dif_pos hex
      simp only [List.foldr_cons, List.foldr_nil]
      rw [hχ, hex.choose_spec φ h4, sub_self]
  have hfin := h E a L hL (GlobalTheory.Published.AutFin.coeffSpan ρ) hW' {χ} (Set.finite_singleton χ) 1
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

end GlobalTheory.HCF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessAutomorphicGLOfEigenStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_finiteness_automorphic_GL_of_eigen : GlobalTheory.HCF.CoreFiniteGL → GlobalTheory.Published.AutomorphicFormsFiniteGL := by
  first | exact @GlobalTheory.HCF.automorphicFormsFiniteGL_of_core | exact GlobalTheory.HCF.automorphicFormsFiniteGL_of_core | (intros; apply GlobalTheory.HCF.automorphicFormsFiniteGL_of_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyFiniteSubgroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyFiniteSubgroupScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbelianQuotientField

open AffineQuotient AbelianQuotient


set_option backward.isDefEq.respectTransparency false in
theorem exists_quotient : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A), IsMonHom i → Mono i → IsFinite H.hom → ∃ (A' : Over (Sp K)) (_ : GrpObj A'), IsAbelianScheme A' ∧ ∃ q : A ⟶ A', IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsPullback i (toUnit H) q η[A'] := by
  intro K _ _ A _ hA H _ i hi hmono hfin
  have := hA.comm
  have := hA.proper
  have := hA.smooth
  have := hA.geomConnected
  have hflat : Flat H.hom := inferInstance
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := GlobalTheory.FiniteFlatKilled.main K H hfin hflat
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsFinite (𝟙 A ^ N : A ⟶ A).left := GlobalTheory.T.isFinite_mulByNat_abelianVariety K A hA N hN
  have : IsFinite H.hom := hfin
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra K H
  have hi' : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf
    (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal)
    (e.hom ≫ i) (𝟙 A ^ N) (by
      rw [comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
        ← comp_pow i, hi', comp_one, comp_one, _root_.one_mul])
  have hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
    refine h₅.of_iso (whiskerRightIso e A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]
  have : Flat q.left := h₃
  have : Surjective q.left := h₄
  have : IsFinite q.left := h₂
  have : IsFinite π.left := h₁
  obtain ⟨inst, hcomm, hhom, hker⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, ?_, q, hhom, h₂, h₃, h₄, hker⟩
  have hπ : π.left ≫ A.hom = Q.hom := Over.w π
  have : IsSeparated Q.hom := by rw [← hπ]; infer_instance
  have : LocallyOfFiniteType Q.hom := by rw [← hπ]; infer_instance
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩

end GlobalTheory.AbelianQuotientField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyFiniteSubgroupSchemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_abelianVariety_finite_subgroupScheme : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A), IsMonHom i → Mono i → IsFinite H.hom → ∃ (A' : Over (Sp K)) (_ : GrpObj A'), IsAbelianScheme A' ∧ ∃ q : A ⟶ A', IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsPullback i (toUnit H) q η[A'] := by
  first | exact @GlobalTheory.AbelianQuotientField.exists_quotient | exact GlobalTheory.AbelianQuotientField.exists_quotient | (intros; apply GlobalTheory.AbelianQuotientField.exists_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactNormalSubgroupFibration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactNormalSubgroupFibration
open MeasureTheory

noncomputable section

namespace GlobalTheory.Cusp.Shear

theorem isHaarMeasure_map_prodHomeo : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N]
    [LocallyCompactSpace N'] (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → ∀ (μ : MeasureTheory.Measure V), μ.IsAddHaarMeasure →
      (((MeasureTheory.Measure.haar : MeasureTheory.Measure N').prod μ).map
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker)).IsHaarMeasure := by
  intro G _ _ _ _ _ _ _ Γ N N' _ _ _ hle hn hc hc' V _ _ _ _ _ _ _ _ s π hs hsc hπc hπmul hπs hker hsmul μ hμ
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he_def
  set P : Measure (N' × V) := (Measure.haar : Measure N').prod μ with hP
  set ν : Measure N := P.map e with hν
  haveI := hc'.isMulRightInvariant (Measure.haar : Measure N')
  have hem : Measurable e := e.continuous.measurable
  haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map P e
  haveI : ν.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective

  haveI hR : ν.IsMulRightInvariant := ⟨fun n₀ => by
    set z₀ := e.symm n₀
    have hz₀ : ((n₀ : N) : G) = (z₀.1 : G) * s z₀.2 := by
      rw [← prodHomeo_apply hle hs hsc hπc hπmul hπs hker z₀]; simp [z₀, e]
    let c : V → N' := fun v => ⟨s v * z₀.1 * (s v)⁻¹, hn _ (hs v) _ z₀.1.2⟩
    have hcc : Continuous c := by fun_prop
    let T' : V × N' → V × N' := fun p => (p.1 + z₀.2, p.2 * c p.1)
    have hT' : MeasurePreserving T' (μ.prod (Measure.haar : Measure N')) (μ.prod (Measure.haar : Measure N')) :=
      (measurePreserving_add_right μ z₀.2).skew_product (g := fun v m => m * c v)
        (by apply Continuous.measurable; fun_prop)
        (.of_forall fun v => map_mul_right_eq_self _ _)
    have hT : MeasurePreserving (Prod.swap ∘ T' ∘ Prod.swap) P P :=
      Measure.measurePreserving_swap.comp (hT'.comp Measure.measurePreserving_swap)
    have hcomm : (fun n => n * n₀) ∘ e = e ∘ (Prod.swap ∘ T' ∘ Prod.swap) := by
      funext ⟨m, v⟩
      apply Subtype.ext
      change ((m : G) * s v) * (n₀ : G) = ((m * c v : N') : G) * s (v + z₀.2)
      rw [hz₀, hsmul, Subgroup.coe_mul]
      change _ = (m : G) * (s v * (z₀.1 : G) * (s v)⁻¹) * (s v * s z₀.2)
      group
    rw [hν, Measure.map_map (measurable_mul_const n₀) hem, hcomm, ← Measure.map_map hem hT.measurable, hT.map_eq]⟩
  haveI : IsFiniteMeasureOnCompacts ν.inv := Measure.IsFiniteMeasureOnCompacts.map ν (Homeomorph.inv N)
  haveI : ν.inv.IsOpenPosMeasure := (Homeomorph.inv N).continuous.isOpenPosMeasure_map (Homeomorph.inv N).surjective
  haveI : ν.inv.IsHaarMeasure := {}
  haveI := hc.isMulRightInvariant ν.inv
  have hL : ν.IsMulLeftInvariant := by rw [← Measure.inv_inv ν]; infer_instance
  exact {}

end GlobalTheory.Cusp.Shear

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactNormalSubgroupFibrationStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_normal_subgroup_fibration : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N]
    [LocallyCompactSpace N'] (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → ∀ (μ : MeasureTheory.Measure V), μ.IsAddHaarMeasure →
      (((MeasureTheory.Measure.haar : MeasureTheory.Measure N').prod μ).map
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker)).IsHaarMeasure := by
  first | exact @GlobalTheory.Cusp.Shear.isHaarMeasure_map_prodHomeo | exact GlobalTheory.Cusp.Shear.isHaarMeasure_map_prodHomeo | (intros; apply GlobalTheory.Cusp.Shear.isHaarMeasure_map_prodHomeo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorUnramifiedFrobTwistIterateDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobQIterateSelf
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem frobQ_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ x : Qr p r, (⇑(frobQ p r))^[r] x = x := by
  intro p _ r hr x
  have h : (⇑(frobQ p r) : Qr p r → Qr p r) = ⇑(GlobalTheory.LKLoc.frobR p (Q0 p) r) := rfl
  rw [h]
  exact GlobalTheory.LKLoc.frobR_iterate_self p (Q0 p) (by infer_instance) r hr x

end GlobalTheory.LKRes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorUnramifiedFrobTwistIterateDegree
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem tensorMap_id_iterate_eq_self {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : B →ₐ[R] B) (r : ℕ) (hf : ∀ b, (⇑f)^[r] b = b) (x : A ⊗[R] B) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id R A) f))^[r] x = x := by
  set e := Algebra.TensorProduct.map (AlgHom.id R A) f
  have ht : ∀ k (a : A) (b : B), (⇑e)^[k] (a ⊗ₜ[R] b) = a ⊗ₜ[R] (⇑f)^[k] b := by
    intro k a b
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      simp [e]
  have hadd : ∀ k (x y : A ⊗[R] B), (⇑e)^[k] (x + y) = (⇑e)^[k] x + (⇑e)^[k] y := by
    intro k x y
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_add (f := _), Function.iterate_succ_apply',
        Function.iterate_succ_apply']
  have hzero : ∀ k, (⇑e)^[k] (0 : A ⊗[R] B) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
  induction x using TensorProduct.induction_on with
  | zero => exact hzero r
  | tmul a b => rw [ht, hf]
  | add x y hx hy => rw [hadd, hx, hy]

theorem sigKQ_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ),
    0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x := by
  intro p _ K r hr x
  exact tensorMap_id_iterate_eq_self (A := K) (frobQ p r) r (frobQ_iterate_self p r hr) x

end GlobalTheory.LKRes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorUnramifiedFrobTwistIterateDegreeStatement
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x := by
  first | exact @GlobalTheory.LKRes.sigKQ_iterate_self | exact GlobalTheory.LKRes.sigKQ_iterate_self | (intros; apply GlobalTheory.LKRes.sigKQ_iterate_self; all_goals assumption)
end
end

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem sigRes_iterate_val (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (n r k : ℕ) (g : GL (Fin n) (KQ p K r)) (i j : Fin n) :
    (((⇑(sigRes p K n r))^[k] g : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j =
      (⇑(sigKQ p K r))^[k] ((g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

theorem sigRes_iterate_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ), 0 < r → ∀ g : GL (Fin n) (KQ p K r), (⇑(sigRes p K n r))^[r] g = g := by
  intro p _ K n r hr g
  apply Units.ext
  ext i j
  rw [sigRes_iterate_val]
  exact GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree p K r hr _

end GlobalTheory.LKRes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassBoundOfTamagawaUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassBoundOfTamagawaUnitary
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.UCls

theorem massBound_of_tamagawa : GlobalTheory.Published.TamagawaSpecialUnitary → GlobalTheory.UCls.MassBound := by
  intro hT E _ _ _ r M h m G Λ Ψ X g x0 FF hr hM hU hSD htor hUA hdist hX
  classical
  set Cc : ℝ := ((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E with hCc
  set P0 : ℝ := (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E with hP0
  set R : ℝ := rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) with hR
  set K : ℝ := (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R * P0 with hK
  have hCpos : 0 < Cc := pow_pos (mul_pos (mul_pos (by positivity) (by positivity))
    (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r)))) _
  have hprod : 0 ≤ ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i :=
    Finset.prod_nonneg fun i _ => tsum_nonneg fun n => by positivity
  have hP0nn : 0 ≤ P0 := pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hprod) _
  have hRnn : 0 ≤ R := Real.rpow_nonneg (by unfold rdE; exact Real.rpow_nonneg (by unfold dE; positivity) _) _
  have hP0le : P0 ≤ Cc := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hprod) (GlobalTheory.volumeConstant_le r hr) _
  have hKnn : 0 ≤ K := by positivity
  have hdet : ∀ i, ∀ γ ∈ (X i).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := fun i =>
    GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three E r M (X i) hM (by rw [(hX i).1]; exact (hX i).2.2.2.1)
  let cv : Fin m → ℝ≥0∞ := fun i => covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
    (riemHaar (X i).Ψ (X i).Gm (x0 i))
  have hV1 : ∀ i, ENNReal.ofReal Cc * muF (X i) (x0 i) (FF i) = cv i := fun i =>
    GlobalTheory.T.covolume_realSpecialUnitary_eq_flagDomain_mass E r (X i) (x0 i) (FF i) (by omega) (hdet i) (hX i).2.2.2.2.1 (hX i).2.2.2.2.2
  have hTA : ∀ i, IsTA (IsCMField.complexConj E) (g i).det := fun i => GlobalTheory.T.isTA_conj_det_of_isUA_cm E r G (g i) hSD.2.1 (hUA i)
  let f : Fin m → Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1 := fun i => Quot.mk _ ⟨(g i).det, hTA i⟩
  have hQfin : Finite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    have h1 : torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M = ⊤ := ENat.card_eq_top_of_infinite
    rw [h1] at htor
    exact absurd htor (by simp)
  have hcard : (Finset.univ.image f).card ≤ h := by
    have h1 : (Finset.univ.image f).card ≤ Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) := by
      haveI := Fintype.ofFinite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1)
      rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    have h2 : ((Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) : ℕ) : ℕ∞) ≤ h := by
      rw [← ENat.card_eq_coe_natCard]; exact htor
    exact h1.trans (by exact_mod_cast h2)
  have hfib : ∀ q ∈ Finset.univ.image f, ∑ i ∈ Finset.univ.filter (fun i => f i = q), cv i ≤ ENNReal.ofReal K := by
    intro q hq
    obtain ⟨i0, -, hi0⟩ := Finset.mem_image.1 hq
    refine GlobalTheory.T.unitary_frames_strong_approximation hT E r M m G Λ Ψ X g x0 _ (g i0) hr hM hU hSD (hUA i0) hUA ?_ (fun i _ j _ => hdist i j)
      (fun i _ => ⟨(hX i).1, (hX i).2.1, (hX i).2.2.1, (hX i).2.2.2.1, (hX i).2.2.2.2.1⟩)
    intro i hi
    have hfi : f i0 = f i := by rw [hi0, (Finset.mem_filter.1 hi).2]
    exact GlobalTheory.T.equivalence_generated_torus_rel E r M G (Λ : Set (Fin r → E)) ⟨(g i0).det, hTA i0⟩ ⟨(g i).det, hTA i⟩ (Quot.eqvGen_exact hfi)
  have hsum : ∑ i, cv i ≤ ENNReal.ofReal (h * K) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image f) (g := f)
      (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))]
    calc _ ≤ ∑ q ∈ Finset.univ.image f, ENNReal.ofReal K := Finset.sum_le_sum hfib
      _ = ((Finset.univ.image f).card : ℝ≥0∞) * ENNReal.ofReal K := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (h : ℝ≥0∞) * ENNReal.ofReal K := by gcongr
      _ = ENNReal.ofReal (h * K) := by rw [ENNReal.ofReal_mul (p := (h : ℝ)) (by positivity), ENNReal.ofReal_natCast]
  have hmu : ∀ i, muF (X i) (x0 i) (FF i) = cv i / ENNReal.ofReal Cc := by
    intro i
    rw [ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hCpos).ne' ENNReal.ofReal_ne_top]
    exact hV1 i
  calc ∑ i, muF (X i) (x0 i) (FF i) = (∑ i, cv i) * (ENNReal.ofReal Cc)⁻¹ := by
        simp only [hmu, div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ENNReal.ofReal (h * K) * (ENNReal.ofReal Cc)⁻¹ := by gcongr
    _ = ENNReal.ofReal (h * K / Cc) := by rw [ENNReal.ofReal_div_of_pos hCpos, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal (massBd E r M h) := by
        apply ENNReal.ofReal_le_ofReal
        have hA : 0 ≤ (h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R := by positivity
        have hq : P0 / Cc ≤ 1 := (div_le_one hCpos).2 hP0le
        calc (h : ℝ) * K / Cc = ((h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R) * (P0 / Cc) := by
              rw [hK]; ring
          _ ≤ ((h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R) * 1 := mul_le_mul_of_nonneg_left hq hA
          _ ≤ 2 * (h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R := by nlinarith
          _ = massBd E r M h := rfl

end GlobalTheory.UCls
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassBoundOfTamagawaUnitaryStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_bound_of_tamagawa_unitary : GlobalTheory.Published.TamagawaSpecialUnitary → GlobalTheory.UCls.MassBound := by
  first | exact @GlobalTheory.UCls.massBound_of_tamagawa | exact GlobalTheory.UCls.massBound_of_tamagawa | (intros; apply GlobalTheory.UCls.massBound_of_tamagawa <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactFibrationSectionMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactFibrationSectionMeasure
open MeasureTheory

namespace GlobalTheory.Cusp.Shear

theorem isFundamentalDomain_image_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  intro G _ _ _ _ _ _ Γ N N' hle hn V _ _ _ _ _ Λ s π hs hsc hπc hπmul hπs hker hsadd hsΓ hπΓ
    A B hAm hBm hA hB ν
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he
  have himg : e '' (A ×ˢ B) = e.symm ⁻¹' (A ×ˢ B) := by
    ext n; constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro h; exact ⟨e.symm n, h, by simp⟩
  have efst : ∀ n : N, (((e.symm n).1 : N') : G) = (n : G) * (s (π n))⁻¹ := fun n => rfl
  have esnd : ∀ n : N, (e.symm n).2 = π n := fun n => rfl
  refine IsFundamentalDomain.mk' ?_ ?_
  · rw [himg]; exact (e.symm.continuous.measurable (hAm.prod hBm)).nullMeasurableSet
  · intro x
    have hmemS : ∀ n : N, n ∈ e '' (A ×ˢ B) ↔ (e.symm n).1 ∈ A ∧ (e.symm n).2 ∈ B := by
      intro n; rw [himg]; rfl
    have hfst : ∀ g : N, (((e.symm (g * x)).1 : N') : G) =
        (g : G) * (s (π g))⁻¹ * (s (π g) * ((x : G) * (s (π x))⁻¹) * (s (π g))⁻¹) := by
      intro g
      rw [efst, hπmul, hsadd]
      simp only [Subgroup.coe_mul]
      group
    have hsnd : ∀ g : N, (e.symm (g * x)).2 = π g + π x := fun g => by rw [esnd, hπmul]
    let c : V → N' := fun w => ⟨s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹,
      hn (s w) (hs w) _ (mul_inv_mem hs hπmul hπs hker x)⟩
    obtain ⟨w, hwB, hwu⟩ := hB (π x)
    obtain ⟨δ, hδA, hδu⟩ := hA (c w)
    have hδΓ : ((δ : N') : G) ∈ Γ := Subgroup.mem_subgroupOf.1 δ.2
    let γ0 : Γ.subgroupOf N := ⟨⟨((δ : N') : G) * s w, N.mul_mem (hle (δ : N').2) (hs w)⟩,
      Subgroup.mem_subgroupOf.2 (Γ.mul_mem hδΓ (hsΓ w w.2))⟩
    have hπγ0 : π (γ0 : N) = w := by
      have h : (γ0 : N) = ⟨((δ : N') : G), hle (δ : N').2⟩ * ⟨s w, hs w⟩ := rfl
      rw [h, hπmul, hπs ⟨s w, hs w⟩ w rfl, (hker _).2 (δ : N').2, zero_add]
    refine ⟨γ0, ?_, ?_⟩
    · show (γ0 : N) * x ∈ _
      rw [hmemS, hsnd, hπγ0]
      refine ⟨?_, hwB⟩
      have h : (e.symm ((γ0 : N) * x)).1 = (δ : N') * c w := by
        apply Subtype.ext
        rw [hfst, hπγ0]
        show ((δ : N') : G) * s w * (s w)⁻¹ * _ = ((δ : N') : G) * (s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹)
        group
      rw [h]; exact hδA
    · intro γ hγ
      have hγ' : (γ : N) * x ∈ e '' (A ×ˢ B) := hγ
      rw [hmemS, hsnd] at hγ'
      obtain ⟨hγA, hγB⟩ := hγ'
      have hγΓ : ((γ : N) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      have hw : (⟨π (γ : N), hπΓ γ hγΓ⟩ : Λ) = w := hwu _ hγB
      have hwv : π (γ : N) = w := congrArg Subtype.val hw
      have hδN' : ((γ : N) : G) * (s w)⁻¹ ∈ N' := hwv ▸ mul_inv_mem hs hπmul hπs hker γ
      let δγ : Γ.subgroupOf N' := ⟨⟨((γ : N) : G) * (s w)⁻¹, hδN'⟩,
        Subgroup.mem_subgroupOf.2 (Γ.mul_mem hγΓ (Γ.inv_mem (hsΓ w w.2)))⟩
      have h : (δγ : N') * c w = (e.symm ((γ : N) * x)).1 := by
        apply Subtype.ext
        rw [hfst, hwv]
        rfl
      have hδe : δγ = δ := hδu δγ (by show (δγ : N') * c w ∈ A; rw [h]; exact hγA)
      have hv : ((γ : N) : G) * (s w)⁻¹ = ((δ : N') : G) := by
        rw [← hδe]
      apply Subtype.ext; apply Subtype.ext
      show ((γ : N) : G) = ((δ : N') : G) * s w
      rw [← hv]; group

end GlobalTheory.Cusp.Shear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactFibrationSectionMeasureStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_fibration_section_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  first | exact @GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod | exact GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod | (intros; apply GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionSumEmbeddingsEigenspace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionSumEmbeddingsEigenspace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section
namespace GlobalTheory.UPel.HT.LieType


open Polynomial in
theorem toLin'_map_aeval_int {F : Type} [Field F] [NumberField F] {g : ℕ}
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (x : 𝓞 F) (p : ℤ[X]) :
    Matrix.toLin' (φ (aeval x p)) = aeval (Matrix.toLin' (φ x)) (p.map (algebraMap ℤ ℂ)) := by
  have h1 : φ (aeval x p) = aeval (φ x) p := (Polynomial.aeval_algHom_apply φ.toIntAlgHom x p).symm
  rw [h1, ← Polynomial.aeval_map_algebraMap ℂ (φ x) p]
  exact (Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)) (φ x) _).symm


open Polynomial in
theorem trace_eq_sum_finrank_eigSp : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ)
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F),
    (φ c).trace = ∑ τ : F →+* ℂ, (Module.finrank ℂ (eigSp φ τ) : ℂ) * τ (c : F) := by
  intro F _ _ g φ c
  classical
  obtain ⟨α, hinj, ⟨f, hf0, hfmap⟩, hmul⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := F) (F := ℂ)
    (RingHom.id ℂ) (fun τ => τ.comp (algebraMap (𝓞 F) F)) (fun _ _ => rfl)
  simp only [RingHom.comp_apply] at hinj hfmap
  set L : Module.End ℂ (Fin g → ℂ) := Matrix.toLin' (φ α) with hL

  have hLf : aeval L (∏ τ : F →+* ℂ, (X - C (τ ((α : 𝓞 F) : F)))) = 0 := by
    rw [← hfmap, ← algebraMap_int_eq, hL, ← toLin'_map_aeval_int, hf0, map_zero, map_zero]
  have hss : L.IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero ?_ hLf
    exact (Polynomial.separable_prod_X_sub_C_iff'.2 fun x _ y _ h => hinj h).squarefree

  have hW : ∀ τ : F →+* ℂ, eigSp φ τ = L.eigenspace (τ ((α : 𝓞 F) : F)) := by
    intro τ
    ext u
    rw [Module.End.mem_eigenspace_iff, mem_eigSp, hL, Matrix.toLin'_apply]
    refine ⟨fun h => h α, fun h c' => ?_⟩
    obtain ⟨N, p, hN, hp⟩ := hmul c'
    have hNC : (N : ℂ) ≠ 0 := Int.cast_ne_zero.2 hN
    have key : φ ((N : 𝓞 F) * c') *ᵥ u = τ (((N : 𝓞 F) * c' : 𝓞 F) : F) • u := by
      rw [hp, ← Matrix.toLin'_apply, toLin'_map_aeval_int]
      by_cases hu : u = 0
      · simp [hu]
      have hev : L.HasEigenvector (τ ((α : 𝓞 F) : F)) u :=
        ⟨Module.End.mem_eigenspace_iff.2 (by rw [hL, Matrix.toLin'_apply]; exact h), hu⟩
      rw [← hL, Module.End.aeval_apply_of_hasEigenvector hev]
      congr 1
      have h2 : (τ.comp (algebraMap (𝓞 F) F)) (aeval α p) = aeval ((τ.comp (algebraMap (𝓞 F) F)) α) p :=
        (Polynomial.aeval_algHom_apply (τ.comp (algebraMap (𝓞 F) F)).toIntAlgHom α p).symm
      simp only [RingHom.comp_apply] at h2
      rw [RingOfIntegers.coe_eq_algebraMap, h2, Polynomial.eval_map_algebraMap]
    have e1 : φ ((N : 𝓞 F) * c') = (N : ℂ) • φ c' := by
      rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    have e2 : τ (((N : 𝓞 F) * c' : 𝓞 F) : F) = (N : ℂ) * τ (c' : F) := by
      simp
    rw [e1, e2, Matrix.smul_mulVec, mul_smul] at key
    exact smul_right_injective _ hNC key

  have hind : iSupIndep (eigSp φ) := by
    have := iSupIndep.comp (Module.End.eigenspaces_iSupIndep L) hinj
    convert this using 1
    funext τ
    exact hW τ
  have htop : ⨆ τ, eigSp φ τ = ⊤ := by
    rw [eq_top_iff, ← hss.iSup_eigenspace_eq_top, iSup_le_iff]
    intro m
    by_cases hm : L.eigenspace m = ⊥
    · rw [hm]; exact bot_le
    · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      have hev : L.HasEigenvector m u := ⟨hu, hu0⟩
      have h0 := Module.End.aeval_apply_of_hasEigenvector hev
        (p := ∏ τ : F →+* ℂ, (X - C (τ ((α : 𝓞 F) : F))))
      rw [hLf, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h0
      have hroot := h0.resolve_right hu0
      rw [eval_prod, Finset.prod_eq_zero_iff] at hroot
      obtain ⟨τ, -, hτ⟩ := hroot
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hτ
      rw [hτ, ← hW τ]
      exact le_iSup (eigSp φ) τ
  have hint : DirectSum.IsInternal (eigSp φ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have hmaps : ∀ τ, Set.MapsTo (Matrix.toLin' (φ c)) (eigSp φ τ) (eigSp φ τ) := by
    intro τ u hu
    have hu' := (mem_eigSp φ τ u).1 hu
    show Matrix.toLin' (φ c) u ∈ eigSp φ τ
    rw [Matrix.toLin'_apply, hu' c]
    exact (eigSp φ τ).smul_mem _ hu
  rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_sum_trace_restrict hint hmaps]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hres : (Matrix.toLin' (φ c)).restrict (hmaps τ) = τ (c : F) • LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have hv := (mem_eigSp φ τ v).1 v.2
    show Matrix.toLin' (φ c) (v : Fin g → ℂ) = τ (c : F) • (v : Fin g → ℂ)
    rw [Matrix.toLin'_apply, hv c]
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

end GlobalTheory.UPel.HT.LieType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionSumEmbeddingsEigenspaceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F), (φ c).trace = ∑ τ : F →+* ℂ, (Module.finrank ℂ (eigSp φ τ) : ℂ) * τ (c : F) := by
  first | (exact @GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp) | (exact GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp) | (intros; apply GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompAtMtMul
namespace GlobalTheory.UnitaryChar

section Mat

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : ℕ}

theorem root {S A : Matrix (Fin n) (Fin n) ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hA : A.PosSemidef)
    (h : A * S * A = S) : ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R * R = A ∧ R * S * R = S := by
  obtain ⟨R, hR, hRR, hu⟩ : ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R * R = A ∧
      ∀ T : Matrix (Fin n) (Fin n) ℂ, T.PosSemidef → T * T = A → R = T :=
    ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      fun T hT e => CFC.sqrt_unique e hT.nonneg⟩
  have a1 : R * (R * (S * A * S)) = 1 := by
    rw [← Matrix.mul_assoc, hRR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, h1]
  have a2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (Matrix.isUnit_det_of_right_inverse a1)
  have a3 : R⁻¹ * R⁻¹ = S * A * S := by
    calc R⁻¹ * R⁻¹ = R⁻¹ * R⁻¹ * (R * (R * (S * A * S))) := by rw [a1, Matrix.mul_one]
      _ = R⁻¹ * (R⁻¹ * R) * R * (S * A * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [a2, Matrix.mul_one, a2, Matrix.one_mul]
  have a4 : R = S * R⁻¹ * S := by
    refine hu _ ?_ ?_
    · have := hR.inv.conjTranspose_mul_mul_same S
      rwa [h2] at this
    · calc S * R⁻¹ * S * (S * R⁻¹ * S) = S * (R⁻¹ * (S * S) * R⁻¹) * S := by simp only [Matrix.mul_assoc]
        _ = (S * S) * A * (S * S) := by rw [h1, Matrix.mul_one, a3, ← h1]; simp only [Matrix.mul_assoc]
        _ = A := by rw [h1, Matrix.mul_one, Matrix.one_mul]
  refine ⟨R, hR, hRR, ?_⟩
  calc R * S * R = S * R⁻¹ * S * S * R := by rw [← a4]
    _ = S * (R⁻¹ * (S * S) * R) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h1, Matrix.mul_one, a2, Matrix.mul_one]

theorem polar_std {S U : Matrix (Fin n) (Fin n) ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hU : Uᴴ * S * U = S) :
    ∃ K Q : Matrix (Fin n) (Fin n) ℂ, Kᴴ * S * K = S ∧ S * K = K * S ∧ Qᴴ * S * Q = S ∧ S * Q * S * Q = 1 ∧
      U = K * Q * Q := by
  have hS : ∀ X : Matrix (Fin n) (Fin n) ℂ, S * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b1 : (S * Uᴴ * S) * U = 1 := by
    rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hU, h1]
  have b2 : U * S * Uᴴ = S := by
    have := congrArg (· * S) (mul_eq_one_comm.1 b1)
    simpa only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨P, hP, hPP, hPS⟩ := root h1 h2 (Matrix.posSemidef_conjTranspose_mul_self U) (by
    calc Uᴴ * U * S * (Uᴴ * U) = Uᴴ * (U * S * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = S := by rw [b2, hU])
  obtain ⟨Q, hQ, hQQ, hQS⟩ := root h1 h2 hP hPS
  have hP' : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (S * (P * X)) = S * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPS]
  have c0 : (U * (S * P * S))ᴴ = S * P * S * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, h2, hP.isHermitian.eq, Matrix.mul_assoc]
  have c1 : (U * (S * P * S))ᴴ * S * (U * (S * P * S)) = S := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * S * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU]; simp only [Matrix.mul_assoc, hS, hP']
  have c2 : (U * (S * P * S))ᴴ * (U * (S * P * S)) = 1 := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hPP]; simp only [Matrix.mul_assoc, hS, hP', h1]
  refine ⟨U * (S * P * S), Q, c1, ?_, by rw [hQ.isHermitian.eq, hQS], ?_, ?_⟩
  · generalize U * (S * P * S) = K at c1 c2
    calc S * K = (K * Kᴴ) * S * K := by rw [mul_eq_one_comm.1 c2, Matrix.one_mul]
      _ = K * (Kᴴ * S * K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [c1]
  · rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hQS, h1]
  · rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_assoc, Matrix.mul_assoc S, Matrix.mul_assoc S, hPS, h1, Matrix.mul_one]

theorem polar {G s u : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.IndefR.Datum.IsCartanInv G s) (hu : uᴴ * G * u = G) :
    ∃ k q : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G ∧ s * k = k * s ∧ qᴴ * G * q = G ∧ s * q * s * q = 1 ∧
      u = k * q * q := by
  obtain ⟨h1, h2, h3⟩ := h
  have hG : Gᴴ = G := by
    have e : sᴴ * Gᴴ = G * s := by rw [← Matrix.conjTranspose_mul, h3.isHermitian.eq]
    have e1 : sᴴ * sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    rw [← Matrix.one_mul Gᴴ, ← e1, Matrix.mul_assoc, e, ← Matrix.mul_assoc, h2]
  obtain ⟨B, hB, hBB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, Bᴴ = B ∧ B * B = G * s :=
    ⟨CFC.sqrt (G * s), (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ h3.posSemidef.nonneg⟩
  have hd : IsUnit B.det := by
    have : IsUnit (B * B).det := by rw [hBB]; exact (Matrix.isUnit_iff_isUnit_det _).1 h3.isUnit
    rw [Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨C, hC, i1, i2⟩ : ∃ C : Matrix (Fin n) (Fin n) ℂ, Cᴴ = C ∧ B * C = 1 ∧ C * B = 1 :=
    ⟨B⁻¹, by rw [Matrix.conjTranspose_nonsing_inv, hB], Matrix.mul_nonsing_inv B hd, Matrix.nonsing_inv_mul B hd⟩
  have j1 : ∀ X : Matrix (Fin n) (Fin n) ℂ, B * (C * X) = X := fun X => by
    rw [← Matrix.mul_assoc, i1, Matrix.one_mul]
  have j2 : ∀ X : Matrix (Fin n) (Fin n) ℂ, C * (B * X) = X := fun X => by
    rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  obtain ⟨S, hs, hGS⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, s = C * S * B ∧ G = B * S * B :=
    ⟨B * s * C, by simp only [Matrix.mul_assoc, j2, i2, Matrix.mul_one], by
      simp only [Matrix.mul_assoc, i2, Matrix.mul_one]
      rw [← Matrix.mul_assoc, hBB, Matrix.mul_assoc, h1, Matrix.mul_one]⟩
  have hS : S = C * G * C := by rw [hGS]; simp only [Matrix.mul_assoc, j2, i1, Matrix.mul_one]
  have s1 : S * S = 1 := by
    have := congrArg (fun X => B * X * C) h1
    simpa only [hs, Matrix.mul_assoc, j1, i1, Matrix.mul_one] using this
  have s2 : Sᴴ = S := by
    rw [hS]; simp only [Matrix.conjTranspose_mul, hC, hG, Matrix.mul_assoc]
  have tr : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * S * X = S → (C * X * B)ᴴ * G * (C * X * B) = G := fun X hX => by
    calc _ = B * (Xᴴ * S * X) * B := by
          rw [hGS]; simp only [Matrix.conjTranspose_mul, hC, hB, Matrix.mul_assoc, j1, j2]
      _ = G := by rw [hX, hGS]
  obtain ⟨K, Q, k1, k2, q1, q2, e⟩ := polar_std (U := B * u * C) s1 s2 (by
    calc _ = C * (uᴴ * (B * S * B) * u) * C := by
          simp only [Matrix.conjTranspose_mul, hC, hB, Matrix.mul_assoc]
      _ = S := by rw [← hGS, hu, ← hS])
  refine ⟨C * K * B, C * Q * B, tr K k1, ?_, tr Q q1, ?_, ?_⟩
  · have := congrArg (fun X => C * X * B) k2
    simpa only [hs, Matrix.mul_assoc, j1] using this
  · have := congrArg (fun X => C * X * B) q2
    simpa only [hs, Matrix.mul_assoc, j1, Matrix.one_mul, i2] using this
  · have := congrArg (fun X => C * X * B) e
    simpa only [Matrix.mul_assoc, j1, j2, i2, Matrix.mul_one] using this

end Mat

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem compAt_mt_mul {D : D7} (θ : InfFam D) (W : HSp D) (τ : D.what₂.Tau) (g g' : GA D W) :
    compAt θ τ (Formalism.L2.Theta.mt W (g * g')) =
      compAt θ τ (Formalism.L2.Theta.mt W g) * compAt θ τ (Formalism.L2.Theta.mt W g') :=
  Matrix.map_mul (L := Formalism.L2.Theta.mt W g) (M := Formalism.L2.Theta.mt W g') (f := (θ τ).comp (infPart D))

theorem compAt_mt_one {D : D7} (θ : InfFam D) (W : HSp D) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 :=
  Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem ext_real {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) {g g' : GA D W} (hg : g ∈ GinfC W)
    (hg' : g' ∈ GinfC W) (h : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W g) = compAt θ τ (Formalism.L2.Theta.mt W g')) :
    g = g' := by
  refine mul_inv_eq_one.1 ((GlobalTheory.UnitarySplit.real_finite_split D W).2.2.1 _ (mul_mem hg (inv_mem hg'))
    ((GlobalTheory.SmoothForms.RealPts.glue θ hθ W).1 _ fun τ => ?_))
  show compAt θ τ (Formalism.L2.Theta.mt W (g * g'⁻¹)) = 1
  rw [compAt_mt_mul, h, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]

theorem char_eq_one : ∀ (D : D7) (θ : InfFam D) (W : HSp D), IsInfFam θ → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ c : GA D W → ℂ, (∀ u ∈ GinfC W, ∀ u' ∈ GinfC W, c (u * u') = c u * c u') → (∀ u ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W u) = compAt θ τ (Formalism.L2.Theta.mt W u) * s τ) → c u = 1) → ∀ u ∈ GinfC W, c u = 1 := by
  intro D θ W hθ s hs c hm hK u hu
  have gl : ∀ x : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ τ, (x τ)ᴴ * gramAt D W τ * x τ = gramAt D W τ) →
      ∃ g ∈ GinfC W, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W g) = x τ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ W).2
  choose k q k1 k2 q1 q2 e using fun τ => polar (u := compAt θ τ (Formalism.L2.Theta.mt W u)) (hs τ)
    (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W u τ)
  obtain ⟨k', hk, ek⟩ := gl k k1
  obtain ⟨q', hq, eq⟩ := gl q q1
  obtain ⟨σ, hσ, eσ⟩ := gl s fun τ => (hs τ).2.1
  have ck : c k' = 1 := hK _ hk fun τ => by rw [ek, k2]
  have cσ : c σ = 1 := hK _ hσ fun τ => by rw [eσ]
  have c1 : c 1 = 1 := hK _ (one_mem _) fun τ => by rw [compAt_mt_one, Matrix.mul_one, Matrix.one_mul]
  have e1 : u = k' * q' * q' := ext_real hθ W hu (mul_mem (mul_mem hk hq) hq) fun τ => by
    rw [compAt_mt_mul, compAt_mt_mul, ek, eq, e]
  have e2 : σ * q' * σ * q' = 1 := ext_real hθ W (mul_mem (mul_mem (mul_mem hσ hq) hσ) hq) (one_mem _) fun τ => by
    rw [compAt_mt_mul, compAt_mt_mul, compAt_mt_mul, eσ, eq, q2, compAt_mt_one]
  rw [← e2, hm _ (mul_mem (mul_mem hσ hq) hσ) _ hq, hm _ (mul_mem hσ hq) _ hσ, hm _ hσ _ hq, cσ, one_mul,
    mul_one] at c1
  rw [e1, hm _ (mul_mem hk hq) _ hq, hm _ hk _ hq, ck, one_mul, c1]

end GlobalTheory.UnitaryChar
end
