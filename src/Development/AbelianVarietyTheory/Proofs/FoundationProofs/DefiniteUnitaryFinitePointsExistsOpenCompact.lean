module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompact
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
open Matrix

noncomputable section

namespace GlobalTheory.DefU.FinCompact

theorem exists_open_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) ∧ IsCompact (K : Set (finU (E := E) (n := n))) := by
  intro E _ _ _ n
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  let K : Subgroup (finU (E := E) (n := n)) := U0.comap p
  have hKo : IsOpen (K : Set (finU (E := E) (n := n))) := hU0o.preimage hp
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  have hfc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E n
    exact isClosed_eq (hc.comp continuous_subtype_val) continuous_const
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hfc.isClosedEmbedding_subtypeVal
  refine ⟨K, hKo, IsCompact.of_isClosed_subset (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL))
    (Subgroup.isClosed_of_isOpen K hKo) fun x hx => ⟨p x, hx, ?_⟩⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

end GlobalTheory.DefU.FinCompact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompactStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) ∧ IsCompact (K : Set (finU (E := E) (n := n))) := by
  first | exact @GlobalTheory.DefU.FinCompact.exists_open_compact | exact GlobalTheory.DefU.FinCompact.exists_open_compact | (intros; apply GlobalTheory.DefU.FinCompact.exists_open_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutFormUCoef
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.EquivCoef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {X : Type} [AddCommGroup X] [Module ℂ X]

def coefL (R : UA E n →* Module.End ℂ X) (F : UA E n → X) : Module.Dual ℂ X →ₗ[ℂ] (UA E n → ℂ) where
  toFun μ := fun g => μ (R g⁻¹ (F g))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isAutFormU_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (X : Type) [AddCommGroup X]
    [Module ℂ X] [FiniteDimensional ℂ X] (R : UA E n →* Module.End ℂ X) (F : UA E n → X),
    (∀ k ∈ finU (E := E) (n := n), R k = 1) → (∀ (u : X) (ℓ : Module.Dual ℂ X), Continuous fun g => ℓ (R g u)) →
    (∀ y ∈ infU E n, ∀ g, F (g * y) = F g) → (∀ γ ∈ ratU E n, ∀ g, F (γ * g) = R γ (F g)) →
    (∀ᶠ y in 𝓝 (1 : UA E n), ∀ g, F (g * y) = F g) →
    ∀ ℓ : Module.Dual ℂ X, IsAutFormU fun g => ℓ (R g⁻¹ (F g)) := by
  intro E _ _ _ n X _ _ _ R F hfin hcont hinf hrat hsm ℓ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA E n => ℓ (R g⁻¹ (F g0)) := (hcont (F g0) ℓ).comp continuous_inv
    refine hc.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA E n => g0⁻¹ * g) (𝓝 g0) (𝓝 1) := by
      have : Continuous fun g : UA E n => g0⁻¹ * g := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using this.tendsto g0
    filter_upwards [ht.eventually hsm] with g hg
    have e := hg g0
    rw [mul_inv_cancel_left] at e
    change ℓ (R g⁻¹ (F g0)) = ℓ (R g⁻¹ (F g))
    rw [e]
  · intro γ hγ g
    change ℓ (R (γ * g)⁻¹ (F (γ * g))) = ℓ (R g⁻¹ (F g))
    rw [hrat γ hγ g, _root_.mul_inv_rev, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (R γ⁻¹), ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  · let φ : UA E n → ℂ := fun g => ℓ (R g⁻¹ (F g))
    let H : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | RU E n (k : UA E n) φ = φ}
        mul_mem' := fun {a b} ha hb => by
          change RU E n ((a : UA E n) * b) _ = _
          rw [← GlobalTheory.DefU.RU_RU, hb, ha]
        one_mem' := by
          change RU E n 1 _ = _
          rw [map_one]; rfl
        inv_mem' := fun {a} ha => by
          change RU E n ((a : UA E n)⁻¹) _ = _
          conv_lhs => rw [← ha]
          change RU E n ((a : UA E n)⁻¹) (RU E n (a : UA E n) _) = _
          rw [GlobalTheory.DefU.RU_RU, inv_mul_cancel, map_one]; rfl }
    have hnb : {k : finU (E := E) (n := n) | ∀ g, F (g * (k : UA E n)) = F g} ∈ 𝓝 (1 : finU (E := E) (n := n)) :=
      (continuous_subtype_val.tendsto (1 : finU (E := E) (n := n))).eventually hsm
    refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hnb fun k hk => ?_)
    change RU E n (k : UA E n) φ = φ
    funext g
    change ℓ (R (g * (k : UA E n))⁻¹ (F (g * k))) = ℓ (R g⁻¹ (F g))
    rw [hk g, _root_.mul_inv_rev, map_mul, hfin _ ((finU (E := E) (n := n)).inv_mem k.2), one_mul]
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (coefL R F)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨ℓ ∘ₗ R (k : UA E n)⁻¹, ?_⟩
    funext g
    change ℓ (R (k : UA E n)⁻¹ (R g⁻¹ (F g))) = ℓ (R (g * (k : UA E n))⁻¹ (F (g * k)))
    rw [hinf _ k.2 g, _root_.mul_inv_rev, map_mul, Module.End.mul_apply]

end GlobalTheory.EquivCoef
end
end
