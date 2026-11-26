module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
namespace GlobalTheory.PiIsotypic

open Representation

theorem nontrivial_of_isIrreducible {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  haveI := h
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.ext (Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule K V))).symm)

theorem exists_irreducible_subrep {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank K S.toSubmodule = m :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ →
      Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  refine ⟨S, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule K S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'⟩
  refine ⟨fun T => ?_⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      have h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥ := h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h2
    have h1 := hmin T' hT'
    have h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 : T.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))
    exact Subrepresentation.toSubmodule_injective h3

def subrepOrderIso {K G V V' : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (σ : Representation K G V) (τ : Representation K G V')
    (e : V ≃ₗ[K] V') (he : ∀ g v, τ g (e v) = e (σ g v)) :
    Subrepresentation σ ≃o Subrepresentation τ where
  toFun T := ⟨T.toSubmodule.map (e : V →ₗ[K] V'), by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨σ g v, T.apply_mem_toSubmodule g hv, (he g v).symm⟩⟩
  invFun U := ⟨U.toSubmodule.comap (e : V →ₗ[K] V'), by
    intro g v hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    rw [← he]
    exact U.apply_mem_toSubmodule g hv⟩
  left_inv T := Subrepresentation.ext (Submodule.comap_map_eq_of_injective e.injective _)
  right_inv U := Subrepresentation.ext (Submodule.map_comap_eq_of_surjective e.surjective _)
  map_rel_iff' {a b} := by
    show a.toSubmodule.map (e : V →ₗ[K] V') ≤ b.toSubmodule.map (e : V →ₗ[K] V') ↔
      a.toSubmodule ≤ b.toSubmodule
    exact Submodule.map_le_map_iff_of_injective e.injective _ _

theorem isIrreducible_of_linearEquiv {K G V V' : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [AddCommGroup V'] [Module K V'] (σ : Representation K G V)
    (τ : Representation K G V') (e : V ≃ₗ[K] V') (he : ∀ g v, τ g (e v) = e (σ g v))
    (h : σ.IsIrreducible) : τ.IsIrreducible := by
  haveI := h
  exact (subrepOrderIso σ τ e he).symm.isSimpleOrder

end GlobalTheory.PiIsotypic

namespace GlobalTheory.PiIsotypic

open Representation

theorem isotypic_factor_of_isIrreducible_pi : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  intro ι _ _ G _ _ W _ _ _ ρ hρ i
  classical
  haveI : Nontrivial W := nontrivial_of_isIrreducible ρ hρ
  let ρi : Representation ℂ (G i) W := ρ.comp (MonoidHom.mulSingle G i)
  obtain ⟨S, hS⟩ := exists_irreducible_subrep ρi
  let n := Module.finrank ℂ S.toSubmodule
  let e : S.toSubmodule ≃ₗ[ℂ] (Fin n → ℂ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [n])
  let τ : Representation ℂ (G i) (Fin n → ℂ) :=
    { toFun := fun g => e.toLinearMap ∘ₗ S.toRepresentation g ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hτe : ∀ g v, τ g (e v) = e (S.toRepresentation g v) := by
    intro g v; simp [τ]
  have hτ : τ.IsIrreducible := isIrreducible_of_linearEquiv S.toRepresentation τ e hτe hS
  let φ0 : (Fin n → ℂ) →ₗ[ℂ] W := S.toSubmodule.subtype ∘ₗ e.symm.toLinearMap
  have hφ0 : ∀ g z, φ0 (τ g z) = ρ (Pi.mulSingle i g) (φ0 z) := by
    intro g z
    simp [φ0, τ]
    rfl
  have hinj : Function.Injective φ0 :=
    Subtype.val_injective.comp e.symm.injective
  refine ⟨n, τ, hτ, ⟨φ0, hinj, hφ0⟩, ?_⟩
  set T : Set W := {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W,
    (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} with hTdef
  have hstab : ∀ g y, y ∈ T → ρ g y ∈ T := by
    rintro g y ⟨φ, hφ, hy⟩
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
    let g' : ∀ j, G j := g * Pi.mulSingle i (g i)⁻¹
    have hcomm : ∀ h : G i, g' * Pi.mulSingle i h = Pi.mulSingle i h * g' := by
      intro h
      funext j
      by_cases hj : j = i
      · subst hj
        simp [g']
      · simp [g', Pi.mulSingle_eq_of_ne hj]
    have hg : g = g' * Pi.mulSingle i (g i) := by
      simp only [g', mul_assoc, ← Pi.mulSingle_mul, inv_mul_cancel, Pi.mulSingle_one, mul_one]
    refine ⟨ρ g' ∘ₗ φ, ?_, LinearMap.mem_range.2 ⟨τ (g i) z, ?_⟩⟩
    · intro h z'
      simp only [LinearMap.comp_apply]
      rw [hφ, ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    · simp only [LinearMap.comp_apply]
      rw [hφ, ← Module.End.mul_apply, ← map_mul, ← hg]
  let U : Subrepresentation ρ := ⟨Submodule.span ℂ T, fun g v hv => by
    have hle : Submodule.span ℂ T ≤ (Submodule.span ℂ T).comap (ρ g) :=
      Submodule.span_le.2 (fun y hy => Submodule.subset_span (hstab g y hy))
    exact hle hv⟩
  haveI := hρ
  rcases eq_bot_or_eq_top U with h | h
  · exfalso
    have hspan : Submodule.span ℂ T = ⊥ := congrArg Subrepresentation.toSubmodule h
    haveI : Nontrivial (Fin n → ℂ) := nontrivial_of_isIrreducible τ hτ
    obtain ⟨z, hz⟩ := exists_ne (0 : Fin n → ℂ)
    have hmem : φ0 z ∈ Submodule.span ℂ T :=
      Submodule.subset_span ⟨φ0, hφ0, LinearMap.mem_range.2 ⟨z, rfl⟩⟩
    rw [hspan, Submodule.mem_bot] at hmem
    exact hz (hinj (by rw [hmem, map_zero]))
  · exact congrArg Subrepresentation.toSubmodule h

end GlobalTheory.PiIsotypic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroupsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypic_factor_of_isIrreducible_pi_finite_groups : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  first | exact @GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | exact GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | (intros; apply GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbits
open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory
namespace OrbitUnfold

variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}

def pull (𝓕 : Set H) (g : H) : Set H := (fun h => g * h) ⁻¹' 𝓕

theorem _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull (hF : IsFundamentalDomain Γ 𝓕 ν) (g : H) :
    NullMeasurableSet (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 g) ν :=
  hF.nullMeasurableSet.preimage (measurePreserving_mul_left ν g).quasiMeasurePreserving

theorem _root_.GlobalTheory.OrbitUnfold.aedisjoint_pull (hF : IsFundamentalDomain Γ 𝓕 ν) {a b : Γ}
    (hab : a ≠ b) :
    AEDisjoint ν (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (a : H)) (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (b : H)) := by
  have key : ∀ c : Γ, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (c : H) = c⁻¹ • 𝓕 := fun c => by
    ext x
    simp [_root_.GlobalTheory.OrbitUnfold.pull, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  rw [key, key]
  exact hF.aedisjoint (inv_injective.ne hab)

theorem _root_.GlobalTheory.OrbitUnfold.setIntegral_pull (g : H) (f : H → ℂ) :
    ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setIntegral_preimage_emb (measurableEmbedding_mulLeft g) f 𝓕

theorem _root_.GlobalTheory.OrbitUnfold.setLIntegral_pull (g : H) (f : H → ℝ≥0∞) :
    ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫⁻ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft g) f 𝓕

theorem _root_.GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull (hF : IsFundamentalDomain Γ 𝓕 ν)
    (y₀ : Y) {O : Set Y}
    [Countable O] (hO : ∀ γ : Γ, γ • y₀ ∈ O) (σ : O → Γ) (hσ : ∀ a : O, σ a • y₀ = a) :
    IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype)
      (⋃ a : O, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν := by
  refine ⟨.iUnion (fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _), ?_, ?_⟩
  ·
    filter_upwards [hF.ae_covers] with x ⟨γ, hγ⟩
    let a : O := ⟨γ • y₀, hO γ⟩
    have hs : (σ a)⁻¹ * γ ∈ MulAction.stabilizer Γ y₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ a]
    refine ⟨⟨Γ.subtype ((σ a)⁻¹ * γ), Subgroup.mem_map_of_mem _ hs⟩, Set.mem_iUnion.2 ⟨a, ?_⟩⟩
    simpa [_root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def, mul_assoc] using hγ
  ·
    rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hst
    have hset : ∀ (u : Γ) (hu : u ∈ MulAction.stabilizer Γ y₀) (a : O),
        (⟨Γ.subtype u, Subgroup.mem_map_of_mem _ hu⟩ :
            (MulAction.stabilizer Γ y₀).map Γ.subtype) •
          _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H) = (σ a * u⁻¹)⁻¹ • 𝓕 := by
      intro u hu a
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem, _root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def,
        mul_assoc]
    simp only [Function.onFun, Set.smul_set_iUnion, hset s hs, hset t ht]
    refine AEDisjoint.iUnion_left_iff.2 fun a => AEDisjoint.iUnion_right_iff.2 fun b => ?_
    refine hF.aedisjoint (inv_injective.ne fun h => hst ?_)
    have hab : a = b := by
      apply Subtype.ext
      have h1 := congrArg (· • y₀) h
      simp only [mul_smul] at h1
      rwa [inv_smul_eq_iff.2 hs.symm, inv_smul_eq_iff.2 ht.symm, hσ, hσ] at h1
    subst hab
    have : s = t := inv_injective (mul_left_cancel h)
    subst this
    rfl

private theorem selfEquivSigmaOrbits_symm_mk {G X : Type} [Group G] [MulAction G X]
    (ω : MulAction.orbitRel.Quotient G X) (x : MulAction.orbit G ω.out) :
    (MulAction.selfEquivSigmaOrbits G X).symm ⟨ω, x⟩ = x := rfl

theorem _root_.GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H)
      [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y]
      [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ,
      (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) →
      ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ →
      (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν →
        IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) →
      ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  intro H _ _ _ ν _ Γ _ Y _ _ 𝓕 hF Φ hmeas hinv hfin hzero
  have horbit : ∀ y₀ : Y, ∑' a : MulAction.orbit Γ y₀, ∫ h in 𝓕, Φ a h ∂ν = 0 := by
    intro y₀
    have hO : ∀ γ : Γ, γ • y₀ ∈ MulAction.orbit Γ y₀ := fun γ => MulAction.mem_orbit y₀ γ
    choose σ hσ using fun a : MulAction.orbit Γ y₀ =>
      (MulAction.mem_orbit_iff.1 a.2 : ∃ g : Γ, g • y₀ = a)
    have hT := _root_.GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull hF y₀ hO σ hσ
    have hshift : ∀ a : MulAction.orbit Γ y₀, ∀ h, Φ a ((σ a : H) * h) = Φ y₀ h := fun a h => by
      rw [← hinv (σ a) y₀ h, hσ]
    have hpt : ∀ a : MulAction.orbit Γ y₀,
        ∫ h in 𝓕, Φ a h ∂ν = ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), Φ y₀ h ∂ν := by
      intro a
      rw [← _root_.GlobalTheory.OrbitUnfold.setIntegral_pull (σ a : H) (Φ a)]
      simp only [hshift]
    have hlpt : ∀ a : MulAction.orbit Γ y₀,
        ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ‖Φ a h‖ₑ ∂ν := by
      intro a
      rw [← _root_.GlobalTheory.OrbitUnfold.setLIntegral_pull (σ a : H) (fun h => ‖Φ a h‖ₑ)]
      simp only [hshift]
    have hσinj : Function.Injective σ := fun a b hab =>
      Subtype.ext (by rw [← hσ a, ← hσ b, hab])
    have hdisj : Pairwise (Function.onFun (AEDisjoint ν)
        fun a : MulAction.orbit Γ y₀ => _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) :=
      fun a b hab => _root_.GlobalTheory.OrbitUnfold.aedisjoint_pull hF (hσinj.ne hab)
    have hint : IntegrableOn (Φ y₀)
        (⋃ a : MulAction.orbit Γ y₀, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν := by
      refine ⟨(hmeas y₀).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ h in ⋃ a : MulAction.orbit Γ y₀, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν
          ≤ ∑' a : MulAction.orbit Γ y₀, ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν :=
            lintegral_iUnion_le _ _
        _ = ∑' a : MulAction.orbit Γ y₀, ∫⁻ h in 𝓕, ‖Φ a h‖ₑ ∂ν := by simp only [hlpt]
        _ ≤ ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν :=
            (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective Subtype.val_injective _); exact _root_.le_rfl)
        _ < ⊤ := lt_top_iff_ne_top.2 hfin
    simp only [hpt]
    rw [← integral_iUnion_ae (fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hdisj hint]
    exact hzero y₀ _ hT hint
  have hsum : Summable fun y => ∫ h in 𝓕, Φ y h ∂ν := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun y => ?_
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono (ENNReal.ne_top_of_tsum_ne_top hfin y)
      (enorm_integral_le_lintegral_enorm _)
  have hs' := ((MulAction.selfEquivSigmaOrbits Γ Y).symm.summable_iff
    (f := fun y => ∫ h in 𝓕, Φ y h ∂ν)).2 hsum
  rw [← (MulAction.selfEquivSigmaOrbits Γ Y).symm.tsum_eq (fun y => ∫ h in 𝓕, Φ y h ∂ν)]
  simp only [Function.comp_def] at hs'
  rw [Summable.tsum_sigma hs']
  simp only [Function.comp_apply, selfEquivSigmaOrbits_symm_mk, horbit, tsum_zero]

end OrbitUnfold
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbitsStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_setIntegral_fundamentalDomain_eq_zero_by_orbits : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν → IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) → ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  first | exact @GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | exact GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | (intros; apply GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroup
open MeasureTheory

namespace GlobalTheory

theorem unfold_tsum_along_subgroup : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (𝓕 : Set H), IsFundamentalDomain (Γ.comap ι) 𝓕 ν → ∀ (f : G → ℂ) (φ : H → ℂ), (∀ γ : G, Measurable fun h => f (γ * ι h)) → Measurable φ → (∀ γ ∈ Γ.comap ι, ∀ h, φ (γ * h) = φ h) → (∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, ‖f ((q.out : Γ) * ι h) * φ h‖ₑ ∂ν) ≠ ⊤ → IntegrableOn (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) 𝓕 ν ∧ HasSum (fun q : Γ ⧸ ι.range.subgroupOf Γ => ∫ h, f ((q.out : Γ) * ι h) * φ h ∂ν) (∫ h in 𝓕, (∑' γ : Γ, f (γ * ι h)) * φ h ∂ν) := by
  intro G H _ _ _ _ ν _ ι hι Γ _ 𝓕 h𝓕 f φ hf hφ hφinv hT
  haveI : MeasurableConstSMul (Γ.comap ι) H := ⟨fun g => measurable_const_mul (g : H)⟩
  haveI : SMulInvariantMeasure (Γ.comap ι) H ν := ⟨fun g s _ => measure_preimage_mul ν (g : H) s⟩
  haveI : Countable (Γ.comap ι) := by
    refine Function.Injective.countable (f := fun δ : Γ.comap ι => (⟨ι δ, δ.2⟩ : Γ)) ?_
    intro a b hab
    exact Subtype.ext (hι (congrArg Subtype.val hab))
  let e : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι → Γ := fun p => (p.1.out : Γ) * ⟨ι p.2, p.2.2⟩
  have hmemK : ∀ δ : Γ.comap ι, (⟨ι δ, δ.2⟩ : Γ) ∈ ι.range.subgroupOf Γ := fun δ => by
    rw [Subgroup.mem_subgroupOf]; exact ⟨δ, rfl⟩
  have he_inj : Function.Injective e := by
    rintro ⟨q, δ⟩ ⟨q', δ'⟩ h
    have hq : ∀ q δ, (QuotientGroup.mk (e (q, δ)) : Γ ⧸ ι.range.subgroupOf Γ) = q := by
      intro q δ
      show (QuotientGroup.mk ((q.out : Γ) * ⟨ι δ, δ.2⟩) : Γ ⧸ ι.range.subgroupOf Γ) = q
      rw [QuotientGroup.mk_mul_of_mem _ (hmemK δ)]
      exact QuotientGroup.out_eq' q
    have hqq : q = q' := by rw [← hq q δ, ← hq q' δ', h]
    subst hqq
    have h2 := mul_left_cancel h
    have h3 : ι δ = ι δ' := congrArg Subtype.val h2
    rw [Prod.mk.injEq]
    exact ⟨rfl, Subtype.ext (hι h3)⟩
  have he_surj : Function.Surjective e := by
    intro γ
    set q : Γ ⧸ ι.range.subgroupOf Γ := QuotientGroup.mk γ with hqdef
    have hm : (q.out : Γ)⁻¹ * γ ∈ ι.range.subgroupOf Γ := by
      apply QuotientGroup.eq.1
      rw [QuotientGroup.out_eq']
    rw [Subgroup.mem_subgroupOf] at hm
    obtain ⟨y, hy⟩ := hm
    have hyΓ : ι y ∈ Γ := by rw [hy]; exact ((q.out : Γ)⁻¹ * γ).2
    refine ⟨(q, ⟨y, hyΓ⟩), ?_⟩
    apply Subtype.ext
    show ((q.out : Γ) : G) * ι y = γ
    rw [hy]
    simp
  let eq := Equiv.ofBijective e ⟨he_inj, he_surj⟩
  let F : Γ → H → ℂ := fun γ h => f ((γ : G) * ι h) * φ h
  let g : Γ ⧸ ι.range.subgroupOf Γ → H → ℂ := fun q h => f (((q.out : Γ) : G) * ι h) * φ h
  have hkey : ∀ q (δ : Γ.comap ι) h, F (e (q, δ)) h = g q (δ • h) := by
    intro q δ h
    show f ((((q.out : Γ) : G) * ι δ) * ι h) * φ h = f (((q.out : Γ) : G) * ι ((δ : H) * h)) * φ ((δ : H) * h)
    rw [map_mul, mul_assoc, hφinv δ δ.2 h]
  have hFm : ∀ γ, Measurable (F γ) := fun γ => (hf γ).mul hφ
  have hgm : ∀ q, Measurable (g q) := fun q => (hf _).mul hφ
  have hA : ∀ q, ∫⁻ h, ‖g q h‖ₑ ∂ν = ∑' δ : Γ.comap ι, ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν := by
    intro q
    rw [h𝓕.lintegral_eq_tsum'' (fun h => ‖g q h‖ₑ)]
    simp_rw [hkey]
  have hsumF : ∑' γ : Γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν = ∑' q, ∫⁻ h, ‖g q h‖ₑ ∂ν := by
    rw [← eq.tsum_eq]
    calc ∑' p, ∫⁻ h in 𝓕, ‖F (eq p) h‖ₑ ∂ν
        = ∑' q, ∑' δ : Γ.comap ι, ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν :=
          ENNReal.tsum_prod (f := fun q δ => ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν)
      _ = _ := by simp_rw [hA]
  have hT' : ∑' γ : Γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν ≠ ⊤ := by rw [hsumF]; exact hT
  have hfun : (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) = fun h => ∑' γ : Γ, F γ h :=
    funext fun h => tsum_mul_right.symm
  have hint : IntegrableOn (fun h => ∑' γ : Γ, F γ h) 𝓕 ν := by
    refine ⟨(AEMeasurable.tsum fun γ => (hFm γ).aemeasurable).aestronglyMeasurable, ?_⟩
    show ∫⁻ h in 𝓕, ‖∑' γ : Γ, F γ h‖ₑ ∂ν < ⊤
    calc ∫⁻ h in 𝓕, ‖∑' γ : Γ, F γ h‖ₑ ∂ν ≤ ∫⁻ h in 𝓕, ∑' γ, ‖F γ h‖ₑ ∂ν :=
          lintegral_mono fun h => enorm_tsum_le_tsum_enorm
      _ = ∑' γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν := lintegral_tsum fun γ => (hFm γ).aemeasurable.enorm
      _ < ⊤ := lt_top_iff_ne_top.2 hT'
  have hsumm : Summable fun γ : Γ => ∫ h in 𝓕, F γ h ∂ν := by
    refine Summable.of_norm ?_
    have h1 : ∑' γ : Γ, ‖∫ h in 𝓕, F γ h ∂ν‖ₑ ≠ ⊤ :=
      ne_top_of_le_ne_top hT' (ENNReal.tsum_le_tsum fun γ => enorm_integral_le_lintegral_enorm _)
    simp only [enorm_eq_nnnorm] at h1
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)
  have hI : ∫ h in 𝓕, (∑' γ : Γ, F γ h) ∂ν = ∑' γ : Γ, ∫ h in 𝓕, F γ h ∂ν :=
    integral_tsum (fun γ => (hFm γ).aestronglyMeasurable) hT'
  have hgint : ∀ q, Integrable (g q) ν := fun q =>
    ⟨(hgm q).aestronglyMeasurable,
      lt_of_le_of_lt (ENNReal.le_tsum (f := fun q => ∫⁻ h, ‖g q h‖ₑ ∂ν) q) (lt_top_iff_ne_top.2 hT)⟩
  have hs : Summable (fun p : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι => ∫ h in 𝓕, F (eq p) h ∂ν) :=
    (eq.summable_iff).2 hsumm
  have hinner : ∀ q, HasSum (fun δ : Γ.comap ι => ∫ h in 𝓕, F (e (q, δ)) h ∂ν) (∫ h, g q h ∂ν) := by
    intro q
    have h1 := (hs.prod_factor q).hasSum
    rw [h𝓕.integral_eq_tsum'' (g q) (hgint q)]
    simp_rw [← hkey]
    exact h1
  have htot : HasSum (fun p : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι => ∫ h in 𝓕, F (eq p) h ∂ν)
      (∫ h in 𝓕, (∑' γ : Γ, F γ h) ∂ν) := by
    rw [hI]; exact (eq.hasSum_iff).2 hsumm.hasSum
  rw [hfun]
  exact ⟨hint, htot.prod_fiberwise hinner⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroupStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (𝓕 : Set H), IsFundamentalDomain (Γ.comap ι) 𝓕 ν → ∀ (f : G → ℂ) (φ : H → ℂ), (∀ γ : G, Measurable fun h => f (γ * ι h)) → Measurable φ → (∀ γ ∈ Γ.comap ι, ∀ h, φ (γ * h) = φ h) → (∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, ‖f ((q.out : Γ) * ι h) * φ h‖ₑ ∂ν) ≠ ⊤ → IntegrableOn (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) 𝓕 ν ∧ HasSum (fun q : Γ ⧸ ι.range.subgroupOf Γ => ∫ h, f ((q.out : Γ) * ι h) * φ h ∂ν) (∫ h in 𝓕, (∑' γ : Γ, f (γ * ι h)) * φ h ∂ν) := by
  first | exact @GlobalTheory.unfold_tsum_along_subgroup | exact GlobalTheory.unfold_tsum_along_subgroup | (intros; apply GlobalTheory.unfold_tsum_along_subgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMatrixOneParameterGroupEqExp
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsUnitIntegral
open NormedSpace Filter Topology

namespace GlobalTheory.ExponentialIntegralUnits

universe u_1

variable {𝔸 : Type u_1} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasDerivAt_primitive (M : ℝ → 𝔸) (hc : Continuous M) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, M s) (M t) t := by
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem exists_isUnit_integral (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1) :
    ∃ δ : ℝ, IsUnit (∫ s in (0 : ℝ)..δ, M s) := by
  have hd := (hasDerivAt_primitive M hc 0).tendsto_slope_zero
  rw [h0] at hd
  have hev := hd.eventually (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨δ, hδU, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0' : δ ≠ 0 := Set.mem_compl_singleton_iff.1 hδ0
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at hδU
  refine ⟨δ, ?_⟩
  have e : (∫ s in (0 : ℝ)..δ, M s) = algebraMap ℝ 𝔸 δ * (δ⁻¹ • ∫ s in (0 : ℝ)..δ, M s) := by
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ0', one_smul]
  rw [e]
  exact ((isUnit_iff_ne_zero.2 hδ0').map (algebraMap ℝ 𝔸)).mul hδU

theorem mul_integral (M : ℝ → 𝔸) (hc : Continuous M)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) (t δ : ℝ) :
    M t * (∫ s in (0 : ℝ)..δ, M s)
      = (∫ s in (0 : ℝ)..(t + δ), M s) - ∫ s in (0 : ℝ)..t, M s := by
  have hL := ((ContinuousLinearMap.mul ℝ 𝔸) (M t)).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
  simp only [ContinuousLinearMap.mul_apply'] at hL
  rw [← hL]
  simp_rw [← hadd]
  rw [intervalIntegral.integral_comp_add_left (fun s => M s) t, add_zero,
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _) (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _)]

theorem exists_hasDerivAt (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t : ℝ, HasDerivAt M (M t * X) t := by
  obtain ⟨δ, hA⟩ := exists_isUnit_integral M hc h0
  have hAA : (∫ s in (0 : ℝ)..δ, M s) * ↑(hA.unit⁻¹) = 1 := hA.mul_val_inv
  refine ⟨(M δ - 1) * ↑(hA.unit⁻¹), fun t => ?_⟩
  have hM : ∀ u, M u = ((∫ s in (0 : ℝ)..(u + δ), M s) - ∫ s in (0 : ℝ)..u, M s) * ↑(hA.unit⁻¹) := fun u => by
    rw [← mul_integral M hc hadd u δ, mul_assoc, hAA, mul_one]
  have hP : HasDerivAt (fun u => ∫ s in (0 : ℝ)..(u + δ), M s) (M (t + δ)) t := by
    exact (hasDerivAt_primitive M hc (t + δ)).comp_add_const t δ
  have hF := (hP.sub (hasDerivAt_primitive M hc t)).mul_const (↑(hA.unit⁻¹) : 𝔸)
  have hF' := hF.congr_of_eventuallyEq (Eventually.of_forall hM)
  refine hF'.congr_deriv ?_
  rw [hadd, ← mul_assoc, mul_sub, mul_one]

theorem exists_exp_eq (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M (0 : ℝ) = (1 : 𝔸))
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t : ℝ, NormedSpace.exp (t • X) = M t := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨X, hX⟩ := exists_hasDerivAt M hc h0 hadd
  refine ⟨X, fun t => ?_⟩
  have hN : ∀ u : ℝ, HasDerivAt (fun v => M v * NormedSpace.exp (v • (-X))) 0 u := fun u => by
    have h3 := (hX u).mul (hasDerivAt_exp_smul_const (-X) u)
    refine h3.congr_deriv ?_
    have hcomm : Commute (NormedSpace.exp (u • (-X))) X :=
      (((Commute.refl X).neg_left).smul_left u).exp_left
    rw [mul_neg, hcomm.eq, mul_neg, ← mul_assoc, add_neg_cancel]
  have hconst : ∀ u, M u * NormedSpace.exp (u • (-X)) = 1 := fun u => by
    have h4 := is_const_of_deriv_eq_zero (fun v => (hN v).differentiableAt) (fun v => (hN v).deriv) u 0
    rw [h4, h0, zero_smul, NormedSpace.exp_zero, one_mul]
  have hinv : NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X) = 1 := by
    rw [← NormedSpace.exp_add_of_commute ((((Commute.refl X).neg_left).smul_left t).smul_right t), smul_neg,
      neg_add_cancel, NormedSpace.exp_zero]
  calc NormedSpace.exp (t • X) = (M t * NormedSpace.exp (t • (-X))) * NormedSpace.exp (t • X) := by
        rw [hconst t, one_mul]
    _ = M t := by rw [mul_assoc, hinv, mul_one]

end GlobalTheory.ExponentialIntegralUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMatrixOneParameterGroupEqExp
open scoped Matrix
open Filter Topology

namespace GlobalTheory

theorem banach_oneParamGroup_eq_exp {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1)
    (hm : ∀ s t, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t, NormedSpace.exp (t • X) = M t := by
  apply _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> assumption

theorem matrix_oneParamGroup_eq_exp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℝ), Continuous M → M 0 = 1 → (∀ s t, M (s + t) = M s * M t) →
    ∃ X : Matrix ι ι ℝ, ∀ t, M t = NormedSpace.exp (t • X) := by
  intro ι _ _ M hc h0 hm
  letI : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  obtain ⟨X, hX⟩ := banach_oneParamGroup_eq_exp M hc h0 hm
  exact ⟨X, fun t => (hX t).symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMatrixOneParameterGroupEqExpStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_matrix_oneParameterGroup_eq_exp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℝ → Matrix ι ι ℝ), Continuous M → M 0 = 1 → (∀ s t, M (s + t) = M s * M t) → ∃ X : Matrix ι ι ℝ, ∀ t, M t = NormedSpace.exp (t • X) := by
  first | exact @GlobalTheory.matrix_oneParamGroup_eq_exp | exact GlobalTheory.matrix_oneParamGroup_eq_exp | (intros; apply GlobalTheory.matrix_oneParamGroup_eq_exp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessOfOpenSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessOfOpenSubgroup
open MeasureTheory

namespace GlobalTheory

theorem _root_.GlobalTheory.fourier_uniqueness_of_openSubgroup : ∀ {H A : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsAddHaarMeasure] [AddCommGroup A] (χ : A → H → ℂ), (∀ a s t, χ a (s + t) = χ a s * χ a t) → (∀ a, χ a 0 = 1) → (∀ t, χ 0 t = 1) → (∀ a b t, χ (a + b) t = χ a t * χ b t) → ∀ L : AddSubgroup H, IsOpen (L : Set H) → (∀ x, x ∉ L → ∃ a, (∀ l ∈ L, χ a l = 1) ∧ χ a x ≠ 1) → ∀ (φ : H → ℂ) (Kc : Set H), IsCompact Kc → (∀ t, t ∉ Kc → φ t = 0) → (∀ t, ∀ l ∈ L, φ (t + l) = φ t) → (∀ a, (∀ l ∈ L, χ a l = 1) → ∫ t, χ a t * φ t ∂μ = 0) → φ = 0 := by
  intro H A _ _ _ _ _ μ _ _ χ hs ha0 h0t hadd L hL hsep φ Kc hK hsupp hφL hint
  by_contra hφ
  obtain ⟨t₀, ht₀⟩ : ∃ t, φ t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (funext h)
  have hχne : ∀ a s, χ a s ≠ 0 := fun a s h => by
    have := hs a s (-s)
    rw [add_neg_cancel, ha0, h, zero_mul] at this
    exact one_ne_zero this
  haveI : DiscreteTopology (H ⧸ L) := QuotientAddGroup.discreteTopology hL
  have hTfin : (QuotientAddGroup.mk '' Kc : Set (H ⧸ L)).Finite :=
    (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  let r : H ⧸ L → H := Quotient.out
  have hr : ∀ t : H, ∃ l ∈ L, r (t : H ⧸ L) = t + l := fun t => by
    obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add L t
    exact ⟨l, l.2, hl⟩
  have hmkr : ∀ q : H ⧸ L, ((r q : H) : H ⧸ L) = q := fun q => Quotient.out_eq q
  have hpre : ∀ q : H ⧸ L, (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) : Set H) =
      (fun h => -r q + h) ⁻¹' (L : Set H) := by
    intro q
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← hmkr q]
    rw [eq_comm]
    exact QuotientAddGroup.eq
  have hmeas : ∀ q : H ⧸ L, μ (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))) = μ L := by
    intro q
    rw [hpre, measure_preimage_add]
  have hmset : ∀ q : H ⧸ L, MeasurableSet (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))) := by
    intro q
    rw [hpre]
    exact (hL.preimage (continuous_const_add (-r q))).measurableSet
  have hLtop : μ L < ⊤ := by
    have hsub : (QuotientAddGroup.mk ⁻¹' ({(t₀ : H ⧸ L)} : Set (H ⧸ L))) ⊆ Kc := by
      intro x hx
      by_contra hxK
      have hx' : -t₀ + x ∈ L := QuotientAddGroup.eq.mp hx.symm
      have := hφL t₀ _ hx'
      rw [add_neg_cancel_left, hsupp x hxK] at this
      exact ht₀ this.symm
    rw [← hmeas (t₀ : H ⧸ L)]
    exact (measure_mono hsub).trans_lt hK.measure_lt_top
  have hLpos : 0 < μ.real L := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hL.measure_pos μ ⟨0, L.zero_mem⟩).ne' hLtop.ne
  have hχL : ∀ a, (∀ l ∈ L, χ a l = 1) → ∀ t l, l ∈ L → χ a (t + l) = χ a t := by
    intro a ha t l hl
    rw [hs, ha l hl, mul_one]
  have hsum : ∀ a, (∀ l ∈ L, χ a l = 1) →
      ∑ q ∈ hTfin.toFinset, χ a (r q) * φ (r q) = 0 := by
    intro a ha
    have hpt : (fun t => χ a t * φ t) = fun t => ∑ q ∈ hTfin.toFinset,
        (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))).indicator
          (fun _ => χ a (r q) * φ (r q)) t := by
      funext t
      obtain ⟨l, hl, hrt⟩ := hr t
      by_cases htT : (t : H ⧸ L) ∈ (QuotientAddGroup.mk '' Kc : Set (H ⧸ L))
      · rw [Finset.sum_eq_single (t : H ⧸ L)]
        · rw [Set.indicator_of_mem (show t ∈ QuotientAddGroup.mk ⁻¹' ({(t : H ⧸ L)} : Set (H ⧸ L)) from rfl), hrt, hχL a ha t l hl, hφL t l hl]
        · intro q _ hq
          exact Set.indicator_of_notMem (show t ∉ QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) from
            fun h => hq (Set.mem_singleton_iff.mp h).symm) _
        · intro h
          exact absurd (hTfin.mem_toFinset.mpr htT) h
      · have htK : t ∉ Kc := fun h => htT ⟨t, h, rfl⟩
        rw [hsupp t htK, mul_zero]
        symm
        refine Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem
          (show t ∉ QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) from fun h => htT ?_) _
        rw [show (t : H ⧸ L) = q from Set.mem_singleton_iff.mp h]
        exact hTfin.mem_toFinset.mp hq
    have hI := hint a ha
    rw [hpt, MeasureTheory.integral_finsetSum] at hI
    · simp_rw [integral_indicator_const _ (hmset _), measureReal_def, hmeas,
        ← measureReal_def] at hI
      rw [← Finset.smul_sum] at hI
      exact (smul_eq_zero.mp hI).resolve_left hLpos.ne'
    · intro q _
      refine IntegrableOn.integrable_indicator ?_ (hmset q)
      exact integrableOn_const (by rw [hmeas]; exact hLtop.ne)
  let A' : AddSubmonoid A :=
    { carrier := {a | ∀ l ∈ L, χ a l = 1}
      zero_mem' := fun l _ => h0t l
      add_mem' := fun {a b} ha hb l hl => by rw [hadd, ha l hl, hb l hl, mul_one] }
  let f : H ⧸ L → (Multiplicative A' →* ℂ) := fun q =>
    { toFun := fun g => χ ((Multiplicative.toAdd g : A') : A) (r q)
      map_one' := h0t _
      map_mul' := fun g g' => hadd _ _ _ }
  have hfinj : Function.Injective f := by
    intro q q' hqq
    by_contra hne
    have hx : r q - r q' ∉ L := by
      intro hx
      apply hne
      rw [← hmkr q, ← hmkr q']
      refine QuotientAddGroup.eq.mpr ?_
      have := L.neg_mem hx
      rwa [neg_sub, ← neg_add_eq_sub] at this
    obtain ⟨a, ha, hax⟩ := hsep _ hx
    have hval := DFunLike.congr_fun hqq (Multiplicative.ofAdd (⟨a, ha⟩ : A'))
    change χ a (r q) = χ a (r q') at hval
    apply hax
    have e : χ a (r q) = χ a (r q - r q') * χ a (r q') := by rw [← hs, sub_add_cancel]
    rw [hval] at e
    exact mul_right_cancel₀ (hχne a (r q')) (by rw [one_mul]; exact e.symm)
  have hli : LinearIndependent ℂ
      (fun q : hTfin.toFinset => (f q : Multiplicative A' → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative A') ℂ).comp (fun q : hTfin.toFinset => f q)
      (hfinj.comp Subtype.val_injective)
  have hzero := Fintype.linearIndependent_iff.mp hli (fun q => φ (r q)) (by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h := hsum _ (Multiplicative.toAdd g).2
    rw [← Finset.sum_coe_sort] at h
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h
    exact mul_comm _ _)
  have ht₀T : (t₀ : H ⧸ L) ∈ hTfin.toFinset :=
    hTfin.mem_toFinset.mpr ⟨t₀, by_contra fun h => ht₀ (hsupp t₀ h), rfl⟩
  have h0 := hzero ⟨_, ht₀T⟩
  obtain ⟨l, hl, hrt⟩ := hr t₀
  change φ (r (t₀ : H ⧸ L)) = 0 at h0
  rw [hrt, hφL t₀ l hl] at h0
  exact ht₀ h0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessOfOpenSubgroupStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_integral_char_eq_zero_of_periodic_open : ∀ {H A : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsAddHaarMeasure] [AddCommGroup A] (χ : A → H → ℂ), (∀ a s t, χ a (s + t) = χ a s * χ a t) → (∀ a, χ a 0 = 1) → (∀ t, χ 0 t = 1) → (∀ a b t, χ (a + b) t = χ a t * χ b t) → ∀ L : AddSubgroup H, IsOpen (L : Set H) → (∀ x, x ∉ L → ∃ a, (∀ l ∈ L, χ a l = 1) ∧ χ a x ≠ 1) → ∀ (φ : H → ℂ) (Kc : Set H), IsCompact Kc → (∀ t, t ∉ Kc → φ t = 0) → (∀ t, ∀ l ∈ L, φ (t + l) = φ t) → (∀ a, (∀ l ∈ L, χ a l = 1) → ∫ t, χ a t * φ t ∂μ = 0) → φ = 0 := by
  first | exact @GlobalTheory.fourier_uniqueness_of_openSubgroup | exact GlobalTheory.fourier_uniqueness_of_openSubgroup | (intros; apply GlobalTheory.fourier_uniqueness_of_openSubgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro
open scoped Matrix

namespace GlobalTheory.RealWeil

theorem mem_sp_of_exp_mem_symplecticGroup (l : Type) [Fintype l] [DecidableEq l]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0:ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᵀ)) (NormedSpace.exp ((0:ℝ) • Xᵀ) * Xᵀ) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᵀ 0
  have h3 := (h1.mul_const (Matrix.J l ℝ)).mul h2
  have h4 : ((fun t : ℝ => NormedSpace.exp (t • X) * Matrix.J l ℝ) * fun t : ℝ => NormedSpace.exp (t • Xᵀ)) = fun _ => Matrix.J l ℝ := by
    funext t
    have := SymplecticGroup.mem_iff.1 (h t)
    rw [← Matrix.exp_transpose, Matrix.transpose_smul] at this
    exact this
  rw [h4] at h3
  have h5 := h3.unique (hasDerivAt_const (0:ℝ) (Matrix.J l ℝ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h5
  have hJ := Matrix.J_squared l ℝ
  have h6 : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * (-X) := by
    have h7 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ = 0 := by
      rw [h5]; simp
    have h8 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ
        = Matrix.J l ℝ * X * (Matrix.J l ℝ * Matrix.J l ℝ) + (Matrix.J l ℝ * Matrix.J l ℝ) * Xᵀ * Matrix.J l ℝ := by
      noncomm_ring
    rw [h8, hJ] at h7
    simp only [mul_neg, mul_one, neg_mul, one_mul] at h7 ⊢
    rw [← neg_add, neg_eq_zero] at h7
    exact eq_neg_of_add_eq_zero_right h7
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  exact h6

end GlobalTheory.RealWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymplecticLieAlgebraOfExpSmulMemSymplecticGroStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup : ∀ (l : Type) [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), (∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) → X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  first | exact @GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup | exact GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup | (intros; apply GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermiteReductionUnipotent
namespace GlobalTheory

theorem hermite_reduction_column {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R)
    (r : Fin n → R → R) (hb : ∀ i j, j < i → b i j = 0) (hr : ∀ i y, b i i ∣ y - r i y)
    (j : Fin n) (m : ℕ) :
    ∃ x : Fin n → R, x j = 1 ∧ (∀ l, j < l → x l = 0) ∧
      ∀ i : Fin n, i < j → (j : ℕ) ≤ i + m → ∃ y, b.mulVec x i = r i y := by
  induction m with
  | zero =>
    refine ⟨Pi.single j 1, by simp, fun l hl => by simp [hl.ne'], fun i hi hj => ?_⟩
    exact absurd (Fin.lt_def.1 hi) (by omega)
  | succ m ih =>
    obtain ⟨x, hx1, hx0, hx⟩ := ih
    by_cases h : ∃ k : Fin n, (j : ℕ) = k + m + 1
    · obtain ⟨k, hk⟩ := h
      obtain ⟨z, hz⟩ := hr k (b.mulVec x k)
      have hkj : k < j := Fin.lt_def.2 (by omega)
      have key : ∀ i, b.mulVec (x - Pi.single k z) i = b.mulVec x i - b i k * z := by
        intro i
        rw [Matrix.mulVec_sub, Pi.sub_apply]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      refine ⟨x - Pi.single k z, ?_, fun l hl => ?_, fun i hi hj => ?_⟩
      · simp [hx1, hkj.ne']
      · simp [hx0 l hl, (hkj.trans hl).ne']
      · rw [key]
        by_cases hik : i = k
        · subst hik
          exact ⟨b.mulVec x i, by rw [← hz]; ring⟩
        · have hne : (i : ℕ) ≠ k := fun e => hik (Fin.ext e)
          have hki : k < i := Fin.lt_def.2 (by omega)
          rw [hb i k hki, zero_mul, sub_zero]
          exact hx i hi (by omega)
    · refine ⟨x, hx1, hx0, fun i hi hj => hx i hi ?_⟩
      by_contra hc
      exact h ⟨i, by omega⟩

theorem hermite_reduction_unipotent :
    ∀ (R : Type) [CommRing R] (n : ℕ) (b : Matrix (Fin n) (Fin n) R) (r : Fin n → R → R),
      (∀ i j, j < i → b i j = 0) → (∀ i y, b i i ∣ y - r i y) →
      ∃ u : Matrix (Fin n) (Fin n) R, (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        ∀ i j, i < j → ∃ y, (b * u) i j = r i y := by
  intro R _ n b r hb hr
  choose x hx1 hx0 hx using fun j : Fin n => hermite_reduction_column b r hb hr j n
  refine ⟨Matrix.of fun i j => x j i, fun i j h => hx0 j i h, fun i => hx1 i, fun i j h => ?_⟩
  obtain ⟨y, hy⟩ := hx j i h (by have := j.2; omega)
  exact ⟨y, by rw [← hy]; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]⟩

end GlobalTheory
end
