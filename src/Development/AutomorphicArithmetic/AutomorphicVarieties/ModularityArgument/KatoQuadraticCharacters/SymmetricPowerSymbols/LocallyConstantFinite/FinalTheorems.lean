module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheorem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfMemInvMem
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixingSubgroupOfIntermediateFieldProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixingSubgroupOfIntermediateFieldProperties
open Polynomial

noncomputable section

namespace GlobalTheory.K4.Geo

open Topology GlobalTheory.NeedB

theorem mem_fixingSubgroup_adjoin_of {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (S : Set Ω)
    (g : Ω ≃ₐ[k] Ω) (hg : ∀ x ∈ S, g x = x) : g ∈ (IntermediateField.adjoin k S).fixingSubgroup := by
  have hle : IntermediateField.adjoin k S ≤ IntermediateField.fixedField (fixingSubgroup (Ω ≃ₐ[k] Ω) S) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (mem_fixingSubgroup_iff _).1 hf x hx
  exact (IntermediateField.le_iff_le _ _).1 hle ((mem_fixingSubgroup_iff _).2 fun x hx => hg x hx)

theorem valuation_lt_one_iff' {Ω : Type} [Field Ω] (B : ValuationSubring Ω) (y : Ω) :
    B.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ B := by
  by_cases hy : y = 0
  · simp [hy]
  · have h0 : B.valuation y ≠ 0 := by simpa using hy
    rw [← B.valuation_le_one_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0)]
    simp [hy, not_le]

variable (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω]

def equiv : (Ω ≃ₐ[K] Ω) ≃* GlobalTheory.K4.geo F K Ω where
  toFun g := ⟨g.restrictScalars F, (GlobalTheory.K4.TopW.mem_geo (K := K) _).2 fun z => g.commutes z⟩
  invFun h := AlgEquiv.ofRingEquiv (f := (h : Ω ≃ₐ[F] Ω).toRingEquiv)
    (fun z => (GlobalTheory.K4.TopW.mem_geo (K := K) _).1 h.2 z)
  left_inv g := by ext x; rfl
  right_inv h := by ext x; rfl
  map_mul' g g' := by ext x; rfl

variable [Algebra.IsAlgebraic F Ω]

theorem continuous_restrict :
    Continuous (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 hU
  obtain ⟨S, hS⟩ : E.FG := IntermediateField.fg_of_fg_toSubalgebra _
    (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hE))
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := F) K
  have hfd : FiniteDimensional K (IntermediateField.adjoin K (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsIntegral.isIntegral x)
  refine Filter.mem_of_superset ((IntermediateField.adjoin K (S : Set Ω)).fixingSubgroup_isOpen.mem_nhds
    (Subgroup.one_mem _)) ?_
  intro g hg
  apply hEU
  rw [← hS]
  apply mem_fixingSubgroup_adjoin_of
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (IntermediateField.subset_adjoin _ _ hx)

theorem continuous_symm : Continuous (equiv F K Ω).symm := by
  apply continuous_of_continuousAt_one (equiv F K Ω).symm
  rw [ContinuousAt, map_one]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).1 hU
  obtain ⟨S, hS⟩ : E.FG := IntermediateField.fg_of_fg_toSubalgebra _
    (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hE))
  have hfd : FiniteDimensional F (IntermediateField.adjoin F (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsIntegral.isIntegral x)
  refine (mem_nhds_subtype _ _ _).2 ⟨_, (IntermediateField.adjoin F (S : Set Ω)).fixingSubgroup_isOpen.mem_nhds
    (Subgroup.one_mem _), ?_⟩
  intro h hh
  simp only [Set.mem_preimage] at hh ⊢
  apply hEU
  rw [← hS]
  apply mem_fixingSubgroup_adjoin_of
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x (IntermediateField.subset_adjoin _ _ hx)

theorem continuous_equiv : Continuous (equiv F K Ω) :=
  continuous_induced_rng.2 (continuous_restrict F K Ω)

end GlobalTheory.K4.Geo

theorem GlobalTheory.K4.geo_facts : ∀ (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [Algebra.IsAlgebraic F Ω],
 (∀ g : Ω ≃ₐ[F] Ω, g ∈ GlobalTheory.K4.geo F K Ω ↔ ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) ∧
 (∃ e : (Ω ≃ₐ[K] Ω) ≃* GlobalTheory.K4.geo F K Ω, (∀ g x, ((e g : GlobalTheory.K4.geo F K Ω) : Ω ≃ₐ[F] Ω) x = g x) ∧ Continuous e ∧ Continuous e.symm) ∧
 (Normal F K → (GlobalTheory.K4.geo F K Ω).Normal) ∧ (IsGalois K Ω → IsCompact (GlobalTheory.K4.geo F K Ω : Set (Ω ≃ₐ[F] Ω))) ∧
 (∀ (B : ValuationSubring Ω) (r g : Ω ≃ₐ[F] Ω), GlobalTheory.NeedB.Inert B r → GlobalTheory.NeedB.Inert (B.comap (g : Ω →+* Ω)) (g⁻¹ * r * g)) := by
  intro F K Ω _ _ _ _ _ _ _ _
  refine ⟨fun g => GlobalTheory.K4.TopW.mem_geo g, ⟨GlobalTheory.K4.Geo.equiv F K Ω, fun g x => rfl, GlobalTheory.K4.Geo.continuous_equiv F K Ω,
    GlobalTheory.K4.Geo.continuous_symm F K Ω⟩, fun _ => ⟨fun n hn g => GlobalTheory.K4.TopW.conj_mem_geo g hn⟩, fun _ => ?_, ?_⟩
  · have hr : (GlobalTheory.K4.geo F K Ω : Set (Ω ≃ₐ[F] Ω)) =
        Set.range (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
      ext h
      constructor
      · intro hh
        exact ⟨(GlobalTheory.K4.Geo.equiv F K Ω).symm ⟨h, hh⟩, AlgEquiv.ext fun _ => rfl⟩
      · rintro ⟨g, rfl⟩
        exact (GlobalTheory.K4.Geo.equiv F K Ω g).2
    rw [hr]
    exact isCompact_range (GlobalTheory.K4.Geo.continuous_restrict F K Ω)
  · intro B r g hr x hx
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap] at hx
    have h1 := hr _ ((B.valuation_le_one_iff _).2 hx)
    rw [GlobalTheory.K4.Geo.valuation_lt_one_iff'] at h1
    rw [GlobalTheory.K4.Geo.valuation_lt_one_iff']
    have key : (g : Ω →+* Ω) ((g⁻¹ * r * g) x - x) = r ((g : Ω →+* Ω) x) - (g : Ω →+* Ω) x := by
      simp [AlgEquiv.mul_apply]
    rcases h1 with h0 | h0
    · left
      apply g.injective
      have : g ((g⁻¹ * r * g) x - x) = 0 := by simpa using key.trans h0
      rw [this, map_zero]
    · right
      intro hm
      apply h0
      rw [ValuationSubring.mem_comap, map_inv₀, key] at hm
      exact hm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixingSubgroupOfIntermediateFieldPropertiesStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixingSubgroupOfIntermediateField_properties : ∀ (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [Algebra.IsAlgebraic F Ω],
 (∀ g : Ω ≃ₐ[F] Ω, g ∈ GlobalTheory.K4.geo F K Ω ↔ ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) ∧
 (∃ e : (Ω ≃ₐ[K] Ω) ≃* GlobalTheory.K4.geo F K Ω, (∀ g x, ((e g : GlobalTheory.K4.geo F K Ω) : Ω ≃ₐ[F] Ω) x = g x) ∧ Continuous e ∧ Continuous e.symm) ∧
 (Normal F K → (GlobalTheory.K4.geo F K Ω).Normal) ∧ (IsGalois K Ω → IsCompact (GlobalTheory.K4.geo F K Ω : Set (Ω ≃ₐ[F] Ω))) ∧
 (∀ (B : ValuationSubring Ω) (r g : Ω ≃ₐ[F] Ω), GlobalTheory.NeedB.Inert B r → GlobalTheory.NeedB.Inert (B.comap (g : Ω →+* Ω)) (g⁻¹ * r * g)) := by
  first | exact @GlobalTheory.K4.geo_facts | exact GlobalTheory.K4.geo_facts | (intros; apply GlobalTheory.K4.geo_facts <;> assumption)
end
end

open Polynomial

namespace GlobalTheory.K4

theorem kum_congr_base {K₁ K₂ Ω : Type*} [Field K₁] [Field K₂] [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω] {N : ℕ}
    (ζ θ : Ω) (g : Ω ≃ₐ[K₁] Ω) (g' : Ω ≃ₐ[K₂] Ω) (h : ∀ x, g x = g' x) :
    GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum (N := N) ζ θ g' := by
  have e : g θ = g' θ := h θ
  unfold GlobalTheory.NeedB.kum
  rw [e]

theorem valuation_eq_one_of_mem_inv_mem {Ω : Type*} [Field Ω] (B : ValuationSubring Ω) {x : Ω} (hx : x ∈ B)
    (hx' : x⁻¹ ∈ B) (h0 : x ≠ 0) : B.valuation x = 1 := by
  have h1 : B.valuation x ≤ 1 := (B.valuation_le_one_iff x).2 hx
  have h2 : B.valuation x⁻¹ ≤ 1 := (B.valuation_le_one_iff _).2 hx'
  have h3 : B.valuation x * B.valuation x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = B.valuation x * B.valuation x⁻¹ := h3.symm
    _ ≤ B.valuation x * 1 := by gcongr
    _ = B.valuation x := mul_one _

theorem mem_of_isIntegral_of_le {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω] (B : ValuationSubring Ω)
    (hB : ∀ p : R, algebraMap R Ω p ∈ B) {x : Ω} (hx : IsIntegral R x) : x ∈ B := by
  obtain ⟨p, hpm, hp⟩ := hx
  let φ : R →+* B := (algebraMap R Ω).codRestrict B hB
  have hcomp : (algebraMap B Ω).comp φ = algebraMap R Ω := by
    ext r
    rfl
  have hB' : IsIntegral B x := ⟨p.map φ, hpm.map φ, by rw [Polynomial.eval₂_map, hcomp]; exact hp⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := B) (K := Ω)).1 hB'
  rw [← hy]
  exact y.2

theorem thmA_on_open_geo : GlobalTheory.NeedB.ThmA → ∀ (k F Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field Ω] [Algebra F (RatFunc k)] [Algebra (RatFunc k) Ω] [Algebra F Ω] [IsScalarTower F (RatFunc k) Ω] [Algebra k[X] Ω] [IsScalarTower k[X] (RatFunc k) Ω] [IsAlgClosure (RatFunc k) Ω] [Algebra.IsAlgebraic F Ω] (N : ℕ) [NeZero N] (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (U : Subgroup (Ω ≃ₐ[F] Ω)), IsOpen (U : Set (Ω ≃ₐ[F] Ω)) → ∀ α β : Ω, α ≠ 0 → β ≠ 0 → IsIntegral k[X] α → IsIntegral k[X] α⁻¹ → IsIntegral k[X] β → IsIntegral k[X] β⁻¹ →
 (∀ g ∈ U, g (α ^ N) = α ^ N ∧ g (β ^ N) = β ^ N) →
 ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N, IsLocallyConstant (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) ∧
  (∀ g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ h ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, GlobalTheory.NeedB.kum (N := N) ζ α g * GlobalTheory.NeedB.kum ζ β h = η₀ h - η₀ (g * h) + η₀ g) ∧
  ∀ r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ B : ValuationSubring Ω, (∀ p : k[X], algebraMap k[X] Ω p ∈ B) → GlobalTheory.NeedB.Inert B r → η₀ r = 0 ∧ r α = α ∧ r β = β := by
  intro hA k F Ω _ _ _ _ _ _ _ _ _ _ _ _ _ N _ ζ hζ U hU α β hα0 hβ0 hαi hαi' hβi hβi' hUfix
  classical
  obtain ⟨-, ⟨e, he, hec, -⟩, -, -, -⟩ := GlobalTheory.T.fixingSubgroupOfIntermediateField_properties F (RatFunc k) Ω
  let U' : Subgroup (Ω ≃ₐ[RatFunc k] Ω) :=
    U.comap ((GlobalTheory.K4.geo F (RatFunc k) Ω).subtype.comp e.toMonoidHom)
  have hU'mem : ∀ g, g ∈ U' ↔ ((e g : GlobalTheory.K4.geo F (RatFunc k) Ω) : Ω ≃ₐ[F] Ω) ∈ U := fun g => Iff.rfl
  have hU'open : IsOpen (U' : Set (Ω ≃ₐ[RatFunc k] Ω)) :=
    (continuous_subtype_val.comp hec).isOpen_preimage _ hU
  let K' : IntermediateField (RatFunc k) Ω := IntermediateField.fixedField U'
  have hfixle : U' ≤ K'.fixingSubgroup := (IntermediateField.le_iff_le U' K').1 le_rfl
  haveI : FiniteDimensional (RatFunc k) K' :=
    (InfiniteGalois.isOpen_iff_finite K').1 (Subgroup.isOpen_mono hfixle hU'open)
  haveI : IsScalarTower F K' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k[X] K' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsAlgClosure K' Ω :=
    ⟨IsAlgClosure.isAlgClosed (RatFunc k), Algebra.IsAlgebraic.tower_top (K := RatFunc k) K'⟩
  obtain ⟨-, ⟨e', he', -, hesc'⟩, -, -, -⟩ := GlobalTheory.T.fixingSubgroupOfIntermediateField_properties F K' Ω
  have hφ : ∀ g (hg : g ∈ GlobalTheory.K4.geo F K' Ω) x, (e'.symm ⟨g, hg⟩) x = g x := by
    intro g hg x
    have := he' (e'.symm ⟨g, hg⟩) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hsub : ∀ g, g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U → g ∈ GlobalTheory.K4.geo F K' Ω := by
    intro g hg
    rw [Subgroup.mem_inf] at hg
    rw [GlobalTheory.K4.TopW.mem_geo]
    intro x
    have h1 : e.symm ⟨g, hg.1⟩ ∈ U' := by
      rw [hU'mem, MulEquiv.apply_symm_apply]
      exact hg.2
    have h2 := (IntermediateField.mem_fixedField_iff U' (x : Ω)).1 x.2 _ h1
    have h3 : (e.symm ⟨g, hg.1⟩) (x : Ω) = g x := by
      have := he (e.symm ⟨g, hg.1⟩) (x : Ω)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [IntermediateField.algebraMap_apply, ← h3]
    exact h2
  have hfixK' : ∀ z : Ω, (∀ g ∈ U, g z = z) → z ∈ K' := by
    intro z hz
    refine (IntermediateField.mem_fixedField_iff U' z).2 fun f hf => ?_
    have := hz _ ((hU'mem f).1 hf)
    rw [he] at this
    exact this
  have hαK : α ^ N ∈ K' := hfixK' _ fun g hg => (hUfix g hg).1
  have hβK : β ^ N ∈ K' := hfixK' _ fun g hg => (hUfix g hg).2
  have hint : ∀ {θ : Ω} (hθ : θ ^ N ∈ K'), IsIntegral k[X] θ → IsIntegral k[X] θ⁻¹ →
      (⟨θ ^ N, hθ⟩ : K') ∈ FunctionField.ringOfIntegers k K' ∧
        (⟨θ ^ N, hθ⟩ : K')⁻¹ ∈ FunctionField.ringOfIntegers k K' := by
    intro θ hθ h1 h2
    constructor
    · refine (mem_integralClosure_iff _ _).2 ?_
      refine (isIntegral_algebraMap_iff (B := Ω)).1 ?_
      exact h1.pow N
    · refine (mem_integralClosure_iff _ _).2 ?_
      refine (isIntegral_algebraMap_iff (B := Ω)).1 ?_
      rw [map_inv₀, IntermediateField.algebraMap_apply, ← inv_pow]
      exact h2.pow N
  have hne : ∀ {θ : Ω} (hθ : θ ^ N ∈ K'), θ ≠ 0 → (⟨θ ^ N, hθ⟩ : K') ≠ 0 := by
    intro θ hθ h0 h
    exact pow_ne_zero N h0 (congrArg Subtype.val h)
  obtain ⟨-, -, -, -, η, hηlc, hηco, hηin⟩ :=
    hA k K' Ω N ζ (Nat.pos_of_ne_zero (NeZero.ne N)) hζ ⟨α ^ N, hαK⟩ ⟨β ^ N, hβK⟩ α β (hne hαK hα0) (hne hβK hβ0)
      (hint hαK hαi hαi').1 (hint hαK hαi hαi').2 (hint hβK hβi hβi').1 (hint hβK hβi hβi').2 rfl rfl
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N,
      ∀ g (hg : g ∈ GlobalTheory.K4.geo F K' Ω), η₀ g = η (e'.symm ⟨g, hg⟩) :=
    ⟨fun g => if hg : g ∈ GlobalTheory.K4.geo F K' Ω then η (e'.symm ⟨g, hg⟩) else 0, fun g hg => dif_pos hg⟩
  refine ⟨η₀, ?_, ?_, ?_⟩
  · have hfun : (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) =
        η ∘ e'.symm ∘ (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => (⟨g.1, hsub _ g.2⟩ : GlobalTheory.K4.geo F K' Ω)) := by
      funext g
      exact hη₀ _ _
    rw [hfun]
    exact hηlc.comp_continuous (hesc'.comp (continuous_subtype_val.subtype_mk _))
  · intro g hg h hh
    have hgh := mul_mem hg hh
    rw [hη₀ _ (hsub _ hg), hη₀ _ (hsub _ hh), hη₀ _ (hsub _ hgh),
      kum_congr_base ζ α g (e'.symm ⟨g, hsub _ hg⟩) (fun x => (hφ _ _ x).symm),
      kum_congr_base ζ β h (e'.symm ⟨h, hsub _ hh⟩) (fun x => (hφ _ _ x).symm)]
    have hm : e'.symm ⟨g * h, hsub _ hgh⟩ = e'.symm ⟨g, hsub _ hg⟩ * e'.symm ⟨h, hsub _ hh⟩ := by
      rw [← map_mul]
      rfl
    rw [hm]
    exact hηco _ _
  · intro r hr B hB hinert
    have hmemB : ∀ {x : Ω}, IsIntegral k[X] x → x ∈ B := fun hx => mem_of_isIntegral_of_le B hB hx
    have hNk : (N : k) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    have hk : (N : k[X]) * C ((N : k)⁻¹) = 1 := by
      rw [← map_natCast C N, ← C_mul, mul_inv_cancel₀ hNk, C_1]
    have h1 : (N : Ω) * algebraMap k[X] Ω (C ((N : k)⁻¹)) = 1 := by
      rw [← map_natCast (algebraMap k[X] Ω) N, ← map_mul, hk, map_one]
    have hNΩ : (N : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hvN : B.valuation (N : Ω) = 1 := by
      refine valuation_eq_one_of_mem_inv_mem B ?_ ?_ hNΩ
      · rw [← map_natCast (algebraMap k[X] Ω) N]
        exact hB _
      · rw [← eq_inv_of_mul_eq_one_right h1]
        exact hB _
    have hroot : ∀ θ : Ω, θ ≠ 0 → IsIntegral k[X] θ → IsIntegral k[X] θ⁻¹ → r (θ ^ N) = θ ^ N → r θ = θ := by
      intro θ h0 hi hi' hfix
      refine GlobalTheory.T.inert_apply_eq_of_pow_fixed_of_valuation_one F Ω B r N 1 θ (Nat.pos_of_ne_zero (NeZero.ne N)) hvN hinert (map_one r) one_ne_zero hfix ?_
      rw [one_pow, div_one]
      refine valuation_eq_one_of_mem_inv_mem B (hmemB (hi.pow N)) ?_ (pow_ne_zero N h0)
      rw [← inv_pow]
      exact hmemB (hi'.pow N)
    rw [Subgroup.mem_inf] at hr
    refine ⟨?_, hroot α hα0 hαi hαi' (hUfix r hr.2).1, hroot β hβ0 hβi hβi' (hUfix r hr.2).2⟩
    have hr' : r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U := Subgroup.mem_inf.2 hr
    rw [hη₀ _ (hsub _ hr')]
    refine hηin B ?_ _ ?_
    · intro x hx
      refine hmemB ?_
      exact ((mem_integralClosure_iff _ _).1 hx).algebraMap
    · intro x hx
      rw [hφ]
      exact hinert x hx

end GlobalTheory.K4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.Imports
open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

theorem UpperTheory.V.Z.Kato.Sym.PE.alg :
    UpperTheory.V.Z.Kato.Sym.PE.Alg := by
  intro Ω _ _ _ ε X
  have hinj : Function.Injective (pj X) :=
    (io X).injective.comp (transcendental_iff_injective.1 (jK_transcendental X))
  let φ : RatFunc Ω →+* Kb X := IsFractionRing.lift hinj
  have hφ : ∀ p : Polynomial Ω, φ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = pj X p := fun p => IsFractionRing.lift_algebraMap hinj p
  refine ⟨φ, hφ, ?_⟩
  have hinj0 : Function.Injective (aeval X.jK : Polynomial Ω →ₐ[Ω] X.K).toRingHom := transcendental_iff_injective.1 (jK_transcendental X)
  let ψ : RatFunc Ω →+* X.K := IsFractionRing.lift hinj0
  have hψ : ∀ p : Polynomial Ω, ψ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = aeval X.jK p := fun p => IsFractionRing.lift_algebraMap hinj0 p
  letI : Algebra (RatFunc Ω) X.K := ψ.toAlgebra
  have hc : φ = algebraMap (RatFunc Ω) (Kb X) := RingHom.ext fun z => by
    change φ z = io X (ψ z)
    rw [← RatFunc.num_div_denom z, map_div₀, map_div₀, map_div₀, hφ, hφ, hψ, hψ]
    rfl
  have hle : ∀ y ∈ IntermediateField.adjoin Ω {X.jK}, y ∈ ψ.fieldRange := fun y hy => by
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff Ω y).1 hy
    exact ⟨algebraMap _ _ r / algebraMap _ _ s, by rw [map_div₀, hψ, hψ]⟩
  haveI : Algebra.IsAlgebraic (RatFunc Ω) X.K := ⟨fun f => by
    obtain ⟨p, hp, he⟩ := X.alg_j f
    have hl : p.map (algebraMap _ X.K) ∈ lifts ψ := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [coeff_map]
      exact hle _ (p.coeff n).2
    obtain ⟨q, hq⟩ := (mem_lifts _).1 hl
    refine ⟨q, ?_, ?_⟩
    · rintro rfl
      rw [Polynomial.map_zero] at hq
      exact hp ((Polynomial.map_eq_zero _).1 hq.symm)
    · change eval₂ ψ f q = 0
      rw [← eval_map, hq, eval_map]
      exact he⟩
  have hA := Algebra.IsAlgebraic.trans (RatFunc Ω) X.K (Kb X)
  refine @Algebra.IsAlgebraic.mk _ _ _ _ φ.toAlgebra fun z => ?_
  obtain ⟨p, hp, he⟩ := hA.isAlgebraic z
  refine ⟨p, hp, ?_⟩
  change eval₂ φ z p = 0
  rw [hc]
  exact he
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.Integ
open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

theorem UpperTheory.V.Z.Kato.Sym.PE.integ :
    UpperTheory.V.Z.Kato.Sym.PE.Integ := by
  intro Ω _ _ _ ε X m hm u z hu hz
  have key : ∀ w : X.K, IsU X w → (pj X).IsIntegralElem (io X w) := by
    intro w hw
    let φ : Polynomial Ω →+* X.K := (aeval X.jK).toRingHom
    have hmem : w ∈ (integralClosure (Subring.closure (φ.range : Set X.K)) X.K).toSubring := by
      rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
      rintro ⟨V, hV⟩
      have hov : X.OverY V := ⟨fun c => hV ⟨C c, by simp [φ]⟩, hV ⟨Polynomial.X, by simp [φ]⟩⟩
      exact (V.valuation_le_one_iff w).1 (hw.2 V hov).le
    obtain ⟨p, hp, hpw⟩ := hmem
    have hle : Subring.closure (φ.range : Set X.K) ≤ φ.range := Subring.closure_le.2 subset_rfl
    have hlift : p.map (algebraMap (Subring.closure (φ.range : Set X.K)) X.K) ∈ lifts φ := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [coeff_map]
      exact RingHom.mem_range.1 (hle (p.coeff n).2)
    obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift (hp.map _)
    refine ⟨Q, hQm, ?_⟩
    show eval₂ ((io X).comp φ) (io X w) Q = 0
    rw [← hom_eval₂, ← eval_map, hQ, eval_map, hpw, _root_.map_zero]
  have hu0 : io X u ≠ 0 := (_root_.map_ne_zero _).2 hu.1
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hz
    exact hu0 hz.symm
  have hinv : IsU X u⁻¹ := ⟨inv_ne_zero hu.1, fun W hW => by rw [map_inv₀, hu.2 W hW, inv_one]⟩
  refine ⟨hz0, ?_, ?_⟩
  · letI := (pj X).toAlgebra
    refine IsIntegral.of_pow hm ?_
    rw [hz]
    exact key u hu
  · letI := (pj X).toAlgebra
    refine IsIntegral.of_pow hm ?_
    rw [inv_pow, hz, ← map_inv₀]
    exact key _ hinv
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFinAlt
open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

theorem UpperTheory.V.Z.Kato.Sym.PE.lcFin :
    UpperTheory.V.Z.Kato.Sym.PE.LcFin := by
  classical
  intro F E A _ _ _ _ U hU η hη
  have hS : ∀ g : U, IsOpen {x : Gal(E/F) | x ∈ U ∧ η x = η g} := by
    intro g
    have := hU.isOpenMap_subtype_val _ (hη.isOpen_fiber (η g))
    convert this using 1
    ext x
    constructor
    · rintro ⟨hx, hxg⟩
      exact ⟨⟨x, hx⟩, hxg, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  have hN : ∀ g : U, ∃ L : IntermediateField F E, FiniteDimensional F L ∧
      (L.fixingSubgroup : Set Gal(E/F)) ⊆
        {y | (g : Gal(E/F)) * y ∈ U ∧ η ((g : Gal(E/F)) * y) = η g} := by
    intro g
    rw [← krullTopology_mem_nhds_one_iff]
    refine IsOpen.mem_nhds ((hS g).preimage (continuous_const.mul continuous_id)) ?_
    simp [g.2]
  choose L hLfd hLsub using hN
  have hfg : ∀ g : U, ∃ s : Finset E,
      Submodule.span F (s : Set E) = Subalgebra.toSubmodule (L g).toSubalgebra := by
    intro g
    haveI := hLfd g
    exact (Submodule.fg_iff_finiteDimensional _).2 (inferInstanceAs (FiniteDimensional F (L g)))
  choose s hs using hfg
  have hcpt : IsCompact (U : Set Gal(E/F)) := (Subgroup.isClosed_of_isOpen U hU).isCompact
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover
    (fun g : U => {x : Gal(E/F) | (g : Gal(E/F))⁻¹ * x ∈ (L g).fixingSubgroup})
    (fun g => by
      haveI := hLfd g
      exact (IntermediateField.fixingSubgroup_isOpen (L g)).preimage
        (continuous_const.mul continuous_id))
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simp [one_mem]⟩)
  refine ⟨t.biUnion s, ?_⟩
  intro h hh h' hh' hag
  obtain ⟨g, hgt, hg⟩ := Set.mem_iUnion₂.1 (ht hh)
  have hg0 : (g : Gal(E/F))⁻¹ * h ∈ (L g).fixingSubgroup := hg
  have hsame : ∀ x ∈ L g, h x = h' x := by
    intro x hx
    have hx' : x ∈ Submodule.span F (s g : Set E) := by
      rw [hs g]
      exact hx
    exact LinearMap.eqOn_span' (f := h.toLinearMap) (g := h'.toLinearMap)
      (fun b hb => hag b (Finset.mem_biUnion.2 ⟨g, hgt, hb⟩)) hx'
  have hg' : (g : Gal(E/F))⁻¹ * h' ∈ (L g).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg0 ⊢
    intro x hx
    rw [AlgEquiv.mul_apply, ← hsame x hx, ← AlgEquiv.mul_apply]
    exact hg0 x hx
  have e1 := (hLsub g hg0).2
  have e2 := (hLsub g hg').2
  simp only [mul_inv_cancel_left] at e1 e2
  rw [e1, e2]
end

open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

namespace UpperTheory.V.Z.Kato.Sym.PE

private def FinalTheorems : Prop :=
  ∀ (k F Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field Ω] [Algebra F (RatFunc k)] [Algebra (RatFunc k) Ω] [Algebra F Ω] [IsScalarTower F (RatFunc k) Ω] [Algebra k[X] Ω] [IsScalarTower k[X] (RatFunc k) Ω] [IsAlgClosure (RatFunc k) Ω] [Algebra.IsAlgebraic F Ω] (N : ℕ) [NeZero N] (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (U : Subgroup (Ω ≃ₐ[F] Ω)), IsOpen (U : Set (Ω ≃ₐ[F] Ω)) → ∀ α β : Ω, α ≠ 0 → β ≠ 0 → IsIntegral k[X] α → IsIntegral k[X] α⁻¹ → IsIntegral k[X] β → IsIntegral k[X] β⁻¹ → (∀ g ∈ U, g (α ^ N) = α ^ N ∧ g (β ^ N) = β ^ N) → ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N, IsLocallyConstant (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) ∧ (∀ g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ h ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, GlobalTheory.NeedB.kum (N := N) ζ α g * GlobalTheory.NeedB.kum ζ β h = η₀ h - η₀ (g * h) + η₀ g) ∧ ∀ r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ B : ValuationSubring Ω, (∀ p : k[X], algebraMap k[X] Ω p ∈ B) → GlobalTheory.NeedB.Inert B r → η₀ r = 0 ∧ r α = α ∧ r β = β

private theorem existsUnique_eq_primitiveRoot_pow_mul_of_pow_eq {E : Type} [Field E] {m : ℕ} [NeZero m] {ζ a c : E}
    (hζ : IsPrimitiveRoot ζ m) (ha : a ≠ 0) (hc : c ^ m = a ^ m) :
    ∃! i : ZMod m, c = ζ ^ i.val * a := by
  have h1 : (c / a) ^ m = 1 := by rw [div_pow, hc, div_self (pow_ne_zero _ ha)]
  obtain ⟨k, hk, hk'⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hck : c = ζ ^ k * a := by rw [hk', div_mul_cancel₀ _ ha]
  refine ⟨(k : ZMod m), ?_, ?_⟩
  · show c = ζ ^ (k : ZMod m).val * a
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
    exact hck
  · intro j hj
    have e : ζ ^ j.val = ζ ^ k := mul_right_cancel₀ ha (hj.symm.trans hck)
    have := hζ.pow_inj (ZMod.val_lt j) hk e
    rw [← ZMod.natCast_zmod_val j, this]

private theorem etaEx_of (hS : FinalTheorems) (hA : Alg) (hI : Integ) (hL : LcFin) : EtaEx := by
  intro Ω _ _ _ ε X m hm u v a b hu hv ha hb
  obtain ⟨φ, hφ, halg⟩ := hA Ω ε X
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  haveI : NeZero m := ⟨hm.ne'⟩
  letI alg1 : Algebra (RatFunc Ω) (Kb X) := φ.toAlgebra
  letI alg2 : Algebra (Polynomial Ω) (Kb X) := (pj X).toAlgebra
  haveI tw : IsScalarTower (Polynomial Ω) (RatFunc Ω) (Kb X) :=
    IsScalarTower.of_algebraMap_eq fun p => (hφ p).symm
  haveI : IsAlgClosed (Kb X) := by unfold Kb; infer_instance
  haveI : IsAlgClosure (RatFunc Ω) (Kb X) := ⟨inferInstance, halg⟩
  haveI : IsGalois (RatFunc Ω) (Kb X) := inferInstance
  let L := IntermediateField.adjoin (RatFunc Ω) ({io X u, io X v} : Set (Kb X))
  haveI : FiniteDimensional (RatFunc Ω) L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (halg.isAlgebraic x).isIntegral)
  have hU : IsOpen (L.fixingSubgroup : Set (Kb X ≃ₐ[RatFunc Ω] Kb X)) :=
    IntermediateField.fixingSubgroup_isOpen L
  have hζ : IsPrimitiveRoot (zt X m) m :=
    (isPrimitiveRoot_eOm ε hm.ne').map_of_injective
      (f := (algebraMap X.K (Kb X)).comp (algebraMap Ω X.K)) (RingHom.injective _)
  obtain ⟨ha0, haI, haI'⟩ := hI Ω ε X m hm u a hu ha
  obtain ⟨hb0, hbI, hbI'⟩ := hI Ω ε X m hm v b hv hb
  have hinL : ∀ g ∈ L.fixingSubgroup, g (io X u) = io X u ∧ g (io X v) = io X v := by
    intro g hg
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hg
    exact ⟨hg _ (IntermediateField.subset_adjoin _ _ (by simp)),
      hg _ (IntermediateField.subset_adjoin _ _ (by simp))⟩
  have hfix : ∀ g ∈ L.fixingSubgroup, g (a ^ m) = a ^ m ∧ g (b ^ m) = b ^ m := by
    intro g hg
    rw [ha, hb]
    exact hinL g hg
  obtain ⟨η₀, hlc, hcoc, hunr⟩ :=
    hS Ω (RatFunc Ω) (Kb X) m (zt X m) hζ L.fixingSubgroup hU a b ha0 hb0 haI haI' hbI hbI' hfix
  have hgeo : ∀ G : Kb X ≃ₐ[RatFunc Ω] Kb X, G ∈ GlobalTheory.K4.geo (RatFunc Ω) (RatFunc Ω) (Kb X) := by
    intro G
    unfold GlobalTheory.K4.geo
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨r, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact G.commutes r
  have hmem : ∀ G : Kb X ≃ₐ[RatFunc Ω] Kb X, G (io X u) = io X u → G (io X v) = io X v →
      G ∈ GlobalTheory.K4.geo (RatFunc Ω) (RatFunc Ω) (Kb X) ⊓ L.fixingSubgroup := by
    intro G hu' hv'
    refine Subgroup.mem_inf.mpr ⟨hgeo G, ?_⟩
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    have e := IntermediateField.adjoin_algHom_ext (RatFunc Ω)
      (φ₁ := (G.toAlgHom).comp L.val) (φ₂ := L.val) (by
        rintro x (rfl | rfl)
        · exact hu'
        · exact hv')
    exact AlgHom.congr_fun e ⟨y, hy⟩
  obtain ⟨B, hB⟩ := hL (RatFunc Ω) (Kb X) (ZMod m) _ (by
    have : GlobalTheory.K4.geo (RatFunc Ω) (RatFunc Ω) (Kb X) ⊓ L.fixingSubgroup = L.fixingSubgroup :=
      inf_eq_right.mpr fun G _ => hgeo G
    rw [this]
    exact hU) η₀ hlc
  have hcomm : ∀ g : RingAut (Kb X),
      (∀ c : Ω, g (io X (algebraMap Ω X.K c)) = io X (algebraMap Ω X.K c)) →
      g (io X X.jK) = io X X.jK → ∀ r, g (φ r) = φ r := by
    intro g h1 h2
    have e : (g.toRingHom.comp φ).comp (algebraMap (Polynomial Ω) (RatFunc Ω)) =
        φ.comp (algebraMap (Polynomial Ω) (RatFunc Ω)) := by
      apply Polynomial.ringHom_ext
      · intro c
        show g (φ (algebraMap (Polynomial Ω) (RatFunc Ω) (Polynomial.C c))) =
          φ (algebraMap (Polynomial Ω) (RatFunc Ω) (Polynomial.C c))
        rw [hφ]
        show g (io X (Polynomial.aeval X.jK (Polynomial.C c))) = io X (Polynomial.aeval X.jK (Polynomial.C c))
        rw [Polynomial.aeval_C]
        exact h1 c
      · show g (φ (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)) =
          φ (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)
        rw [hφ]
        show g (io X (Polynomial.aeval X.jK Polynomial.X)) = io X (Polynomial.aeval X.jK Polynomial.X)
        rw [Polynomial.aeval_X]
        exact h2
    have e2 := IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial Ω)) e
    intro r
    exact RingHom.congr_fun e2 r
  have hk : ∀ (g : RingAut (Kb X)) (G : Kb X ≃ₐ[RatFunc Ω] Kb X), (∀ x, G x = g x) →
      ∀ x : Kb X, x ≠ 0 → g (x ^ m) = x ^ m → ka X m x g = GlobalTheory.NeedB.kum (zt X m) x G := by
    intro g G hG x hx0 hxm
    obtain ⟨i, hi, huniq⟩ := existsUnique_eq_primitiveRoot_pow_mul_of_pow_eq (c := g x) hζ hx0 (by rw [← map_pow, hxm])
    unfold ka lg GlobalTheory.NeedB.kum
    rw [hG, dif_pos ⟨i, hi⟩]
    exact (huniq _ (Classical.epsilon_spec (p := fun j : ZMod m => g x = zt X m ^ j.val * x) ⟨i, hi⟩)).trans
      (huniq _ (Exists.choose_spec (⟨i, hi⟩ : ∃ j : ZMod m, g x = zt X m ^ j.val * x))).symm
  classical
  refine ⟨fun g => if hg : ∀ r, g (φ r) = φ r then η₀ (AlgEquiv.ofRingEquiv (f := g) hg) else 0,
    ?_, ?_, ?_⟩
  · intro g h hg hh
    unfold InU at hg hh
    obtain ⟨g1, g2, g3, g4⟩ := hg
    obtain ⟨h1, h2, h3, h4⟩ := hh
    have cg := hcomm g g1 g2
    have ch := hcomm h h1 h2
    have cgh : ∀ r, (g * h) (φ r) = φ r := fun r => by
      show g (h (φ r)) = φ r
      rw [ch, cg]
    have hGH : AlgEquiv.ofRingEquiv (f := g * h) cgh =
        AlgEquiv.ofRingEquiv (f := g) cg * AlgEquiv.ofRingEquiv (f := h) ch := by
      ext x
      rfl
    simp only [dif_pos cg, dif_pos ch, dif_pos cgh]
    rw [hGH, hk g (AlgEquiv.ofRingEquiv (f := g) cg) (fun _ => rfl) a ha0 (by rw [ha]; exact g3),
      hk h (AlgEquiv.ofRingEquiv (f := h) ch) (fun _ => rfl) b hb0 (by rw [hb]; exact h4)]
    exact hcoc _ (hmem _ g3 g4) _ (hmem _ h3 h4)
  · unfold LC
    refine ⟨B, ?_⟩
    intro h h' hh hh' hBB
    unfold InD at hh hh'
    have ch := hcomm h (fun c => hh _) (hh _)
    have ch' := hcomm h' (fun c => hh' _) (hh' _)
    simp only [dif_pos ch, dif_pos ch']
    exact hB _ (hmem _ (hh u) (hh v)) _ (hmem _ (hh' u) (hh' v)) hBB
  · unfold Unr
    intro B h hY hh hin
    unfold InD at hh
    unfold Tower.OverY at hY
    have ch := hcomm h (fun c => hh _) (hh _)
    simp only [dif_pos ch]
    refine (hunr (AlgEquiv.ofRingEquiv (f := h) ch) (hmem _ (hh u) (hh v)) B ?_ hin).1
    intro p
    show io X (Polynomial.aeval X.jK p) ∈ B
    have : Polynomial.aeval X.jK p ∈ B.comap (io X) := by
      refine Polynomial.induction_on p (fun c => ?_) (fun p q hp hq => ?_) (fun n c _ => ?_)
      · rw [Polynomial.aeval_C]
        exact hY.1 c
      · rw [map_add (f := _)]
        exact add_mem hp hq
      · rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
        exact mul_mem (hY.1 c) (pow_mem hY.2 _)
    exact this

theorem etaEx : EtaEx := etaEx_of (GlobalTheory.K4.thmA_on_open_geo GlobalTheory.KummerCob.thmA) alg integ lcFin

end UpperTheory.V.Z.Kato.Sym.PE
