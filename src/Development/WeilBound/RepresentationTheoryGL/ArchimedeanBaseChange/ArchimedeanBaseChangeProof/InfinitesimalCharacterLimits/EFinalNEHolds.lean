module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.EFinalOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.IsometrySymmetry.IsoVSymm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SeparationHolds

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitVectorIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalPairTyped
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalPairTyped
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.FdPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_eq_prodSpan (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ = prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro F ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩
  · refine Submodule.span_mono ?_
    rintro F ⟨_, ⟨φ₁, h₁, rfl⟩, _, ⟨φ₂, h₂, rfl⟩, rfl⟩
    exact ⟨φ₁, h₁, φ₂, h₂, rfl⟩

theorem map_typed {N : ℕ} (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E)))
    (W : Submodule ℂ (Kinf E N → ℂ)) :
    U.map (Sm E N).subtype ⊓ typeF K W = (typed U K W).map (Sm E N).subtype := by
  ext f
  constructor
  · rintro ⟨⟨φ, hφ, rfl⟩, hS⟩
    exact ⟨φ, ⟨hφ, hS⟩, rfl⟩
  · rintro ⟨φ, ⟨hφ, hS⟩, rfl⟩
    exact ⟨⟨φ, hφ, rfl⟩, hS⟩

theorem slice_left {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (y : GA E b) : (fun x => F (x, y)) ∈ typeF K₁ W₁ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have := hF.1 u hu 1 K₂.one_mem (g, y)
    simpa using this
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
      { toFun := fun f k => f (k, 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hL : Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}
        ≤ W₁.comap L := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨w₁, h₁, w₂, h₂, rfl⟩
      have : L (fun k => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁ := by
        funext k
        simp [L, mul_comm]
      show L _ ∈ W₁
      rw [this]
      exact W₁.smul_mem _ h₁
    have := hL (hF.2 (g, y))
    simpa [L] using this

theorem slice_right {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (x : GA E a) : (fun y => F (x, y)) ∈ typeF K₂ W₂ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have := hF.1 1 K₁.one_mem u hu (x, g)
    simpa using this
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ) :=
      { toFun := fun f k => f (1, k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hL : Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}
        ≤ W₂.comap L := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨w₁, h₁, w₂, h₂, rfl⟩
      have : L (fun k => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂ := by
        funext k
        simp [L]
      show L _ ∈ W₂
      rw [this]
      exact W₂.smul_mem _ h₂
    have := hL (hF.2 (x, g))
    simpa [L] using this

theorem finiteDimensional_pairSpace_inf_typeHF : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E)))
    (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)),
    FiniteDimensional ℂ (typed U₁ K₁ W₁) → FiniteDimensional ℂ (typed U₂ K₂ W₂) →
    FiniteDimensional ℂ ((pairSpace U₁ U₂ ⊓ typeHF K₁ K₂ W₁ W₂ : Submodule ℂ (H E a b → ℂ))) := by
  intro E _ _ _ a b U₁ U₂ K₁ K₂ W₁ W₂ h₁ h₂
  have f₁ : FiniteDimensional ℂ (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁ : Submodule ℂ (GA E a → ℂ)) := by
    rw [map_typed]; infer_instance
  have f₂ : FiniteDimensional ℂ (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂ : Submodule ℂ (GA E b → ℂ)) := by
    rw [map_typed]; infer_instance
  haveI hfd := GlobalTheory.T.finiteDimensional_prodSpan (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁) (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂) f₁ f₂
  refine Submodule.finiteDimensional_of_le (S₂ := prodSpan (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁)
    (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂)) ?_
  rintro F ⟨hU, hT⟩
  rw [SetLike.mem_coe, pairSpace_eq_prodSpan] at hU
  exact GlobalTheory.T.mem_prodSpan_inf _ _ _ _ F hU (fun y => slice_left hT y) (fun x => slice_right hT x)

end GlobalTheory.CompanionTheory.LimV.FdPair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalPairTypedStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_pair_typed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ (typed U₁ K₁ W₁) → FiniteDimensional ℂ (typed U₂ K₂ W₂) → FiniteDimensional ℂ ((pairSpace U₁ U₂ ⊓ typeHF K₁ K₂ W₁ W₂ : Submodule ℂ (H E a b → ℂ))) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.FdPair.finiteDimensional_pairSpace_inf_typeHF | exact GlobalTheory.CompanionTheory.LimV.FdPair.finiteDimensional_pairSpace_inf_typeHF | (intros; apply GlobalTheory.CompanionTheory.LimV.FdPair.finiteDimensional_pairSpace_inf_typeHF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedExtension
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem typed_tw_finite {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z : ℂ)
    (H : ∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)),
      IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U K W))
    (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (hW : FiniteDimensional ℂ W) :
    FiniteDimensional ℂ (typed (tw U z) K W) := by
  have hK₀ : IsOpen ((K ⊓ KO E N : Subgroup (GL (Fin N) (Af E))) : Set (GL (Fin N) (Af E))) := by
    rw [Subgroup.coe_inf]
    exact hK.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E N)
  have hfin := H (K ⊓ KO E N) W hK₀ hW
  have hflat : FlatFn (absFn (E := E) N (-z)) := GlobalTheory.T.flat_absolute_character N (-z)
  have hval : ∀ (φ : Sm E N) x, (mulChi N (GlobalTheory.CuspRep.Model.absC E (-z)) φ).1 x =
      absFn N (-z) x * φ.1 x := fun φ x => by
    simp only [mulChi_apply, absFn]
    exact mul_comm _ _
  have hfinv : ∀ (g : GA E N), ∀ u ∈ KO E N, absFn (E := E) N (-z) (g * finGL E N u) = absFn N (-z) g := by
    intro g u hu
    have := hflat.rinv g 1 u hu
    simpa [cf] using this
  have hkinv : ∀ (g : GA E N) (k : Kinf E N),
      absFn (E := E) N (-z) (g * infGL E N (Unitary.toUnits k)) = absFn N (-z) g := by
    intro g k
    have := hflat.rinv g k 1 (one_mem _)
    simpa [cf] using this
  let L : Sm E N ≃ₗ[ℂ] Sm E N := mulChi N (GlobalTheory.CuspRep.Model.absC E (-z))
  have hle : (typed (tw U z) K W).map (L : Sm E N →ₗ[ℂ] Sm E N) ≤ typed U (K ⊓ KO E N) W := by
    rintro _ ⟨φ, ⟨⟨ψ, hψ, rfl⟩, hlev, htype⟩, rfl⟩
    set φ : Sm E N := mulChi N (GlobalTheory.CuspRep.Model.absC E z) ψ with hφ
    have hL : ∀ x, (L φ).1 x = absFn N (-z) x * φ.1 x := hval φ
    refine ⟨?_, ?_, ?_⟩
    · have hback : L φ = ψ := by
        refine Subtype.ext (funext fun x => ?_)
        have e : ∀ s : ℂ, ((chiDet N (GlobalTheory.CuspRep.Model.absC E s) x : ℂˣ) : ℂ) =
            Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x)) := fun _ => rfl
        rw [hL, hφ, mulChi_apply, absFn, e, e, mul_left_comm, ← Complex.exp_add]
        simp
      show L φ ∈ U
      rw [hback]
      exact hψ
    · intro u hu g
      have h2 : φ.1 (g * finGL E N u) = φ.1 g := hlev u hu.1 g
      show (L φ).1 (g * finGL E N u) = (L φ).1 g
      rw [hL, hL, hfinv g u hu.2, h2]
    · intro g
      have h3 : (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W := htype g
      have h4 : (fun k : Kinf E N => (L φ).1 (g * infGL E N (Unitary.toUnits k))) =
          absFn N (-z) g • (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) := by
        funext k
        rw [hL, hkinv g k]
        rfl
      show (fun k : Kinf E N => (L φ).1 (g * infGL E N (Unitary.toUnits k))) ∈ W
      rw [h4]
      exact W.smul_mem _ h3
  have h1 : FiniteDimensional ℂ ((typed (tw U z) K W).map (L : Sm E N →ₗ[ℂ] Sm E N)) :=
    Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (L.submoduleMap (typed (tw U z) K W)).symm

end GlobalTheory.CompanionTheory.LimV
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedExtensionStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_typed_extension : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (z : ℂ), (∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U K W)) → ∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed (tw U z) K W) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.typed_tw_finite | exact GlobalTheory.CompanionTheory.LimV.typed_tw_finite | (intros; apply GlobalTheory.CompanionTheory.LimV.typed_tw_finite <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRescaledConvergentSubsequence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRescaledConvergentSubsequence
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimVec

theorem normalised_subseq_limit : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (g : ℕ → M), (∀ k, g k ≠ 0) → ∃ (c : ℕ → ℂ) (φ : ℕ → ℕ) (G : M), StrictMono φ ∧ G ≠ 0 ∧ ∀ ℓ : Module.Dual ℂ M, Tendsto (fun k => c k * ℓ (g (φ k))) atTop (𝓝 (ℓ G)) := by
  intro M _ _ _ g hg
  let e : M ≃ₗ[ℂ] (Fin (Module.finrank ℂ M) → ℂ) := (Module.finBasis ℂ M).equivFun
  let s : ℕ → ℂ := fun k => ((‖e (g k)‖⁻¹ : ℝ) : ℂ)
  have hv : ∀ k, e (g k) ≠ 0 := fun k h => hg k (by simpa using h)
  have hmem : ∀ k, s k • e (g k) ∈ Metric.sphere (0 : Fin (Module.finrank ℂ M) → ℂ) 1 := by
    intro k
    have hn : ‖e (g k)‖ ≠ 0 := norm_ne_zero_iff.mpr (hv k)
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp only [s, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn
  obtain ⟨v, hvs, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin (Module.finrank ℂ M) → ℂ) 1).tendsto_subseq hmem
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hvs
    simp at hvs
  refine ⟨fun k => s (φ k), φ, e.symm v, hφ, by simpa using hv0, fun ℓ => ?_⟩
  let L : (Fin (Module.finrank ℂ M) → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ e.symm.toLinearMap
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have h := (hL.tendsto v).comp hlim
  have hfun : (L ∘ ((fun k => s k • e (g k)) ∘ φ)) = fun k => s (φ k) * ℓ (g (φ k)) := by
    funext k
    simp [L]
  rw [hfun] at h
  simpa [L] using h

end GlobalTheory.CompanionTheory.LimVec
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRescaledConvergentSubsequenceStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescaled_convergent_subsequence : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (g : ℕ → M), (∀ k, g k ≠ 0) → ∃ (c : ℕ → ℂ) (φ : ℕ → ℕ) (G : M), StrictMono φ ∧ G ≠ 0 ∧ ∀ ℓ : Module.Dual ℂ M, Tendsto (fun k => c k * ℓ (g (φ k))) atTop (𝓝 (ℓ G)) := by
  first | exact @GlobalTheory.CompanionTheory.LimVec.normalised_subseq_limit | exact GlobalTheory.CompanionTheory.LimVec.normalised_subseq_limit | (intros; apply GlobalTheory.CompanionTheory.LimVec.normalised_subseq_limit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableInducedSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableInducedSpan
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem act_fin_val {N : ℕ} (g : GL (Fin N) (Af E)) (φ : Sm E N) (x : GA E N) :
    (act (.fin g) φ).1 x = φ.1 (x * finGL E N g) := rfl

theorem memInd2_act_fin {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)}
    (g : GL (Fin (r + s)) (Af E)) {φ : Sm E (r + s)} (h : MemInd2 U₁ U₂ φ) :
    MemInd2 U₁ U₂ (act (.fin g) φ) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x y => ?_, fun k g' => ?_⟩
  · rw [act_fin_val, act_fin_val, mul_assoc, h1]
  · convert h2 k (g' * g) using 2 with m
    rw [act_fin_val, map_mul, mul_assoc, mul_assoc]

theorem indSpan_finStable (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) :
    FinStable (indSpan U₁ U₂) := by
  intro g φ hφ
  change φ ∈ Submodule.span ℂ _ at hφ
  change _ ∈ Submodule.span ℂ _
  induction hφ using Submodule.span_induction with
  | mem φ h => exact Submodule.subset_span (memInd2_act_fin g h)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end GlobalTheory.CompanionTheory.LimV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableInducedSpanStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finStable_induced_span : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), FinStable (indSpan U₁ U₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.indSpan_finStable | exact GlobalTheory.CompanionTheory.LimV.indSpan_finStable | (intros; apply GlobalTheory.CompanionTheory.LimV.indSpan_finStable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSpaceCarriesFlat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSpaceCarriesFlat
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

section PairCarry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem FlatFn.fin_inv {N : ℕ} {e : GA E N → ℂ} (he : FlatFn e) (x : GA E N) {u : GL (Fin N) (Af E)}
    (hu : u ∈ KO E N) : e (x * finGL E N u) = e x := by
  have h := he.rinv x 1 u hu
  simpa [cf] using h

theorem FlatFn.inf_inv {N : ℕ} {e : GA E N → ℂ} (he : FlatFn e) (x : GA E N) (k : Kinf E N) :
    e (x * infGL E N (Unitary.toUnits k)) = e x := by
  have h := he.rinv x k 1 (one_mem _)
  simpa [cf] using h

theorem mul_mem_pairSpace (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a))
    (U₂ U₂' : Submodule ℂ (Sm E b)) (F : H E a b → ℂ) (c₁ : Carries e₁ U₁ U₁') (c₂ : Carries e₂ U₂ U₂')
    (hF : F ∈ pairSpace U₁ U₂) : (fun x => e₁ x.1 * e₂ x.2 * F x) ∈ pairSpace U₁' U₂' := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hG
    obtain ⟨ψ₁, k₁, i₁⟩ := c₁ φ₁ h₁
    obtain ⟨ψ₂, k₂, i₂⟩ := c₂ φ₂ h₂
    refine Submodule.subset_span ⟨ψ₁, k₁, ψ₂, k₂, funext fun x => ?_⟩
    simp only [i₁, i₂]
    ring
  | zero =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (0 : H E a b → ℂ) x) = 0 := by
      funext x; simp
    rw [this]
    exact Submodule.zero_mem _
  | add G G' _ _ h h' =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (G + G') x) =
        (fun x => e₁ x.1 * e₂ x.2 * G x) + fun x => e₁ x.1 * e₂ x.2 * G' x := by
      funext x; simp only [Pi.add_apply]; ring
    rw [this]
    exact Submodule.add_mem _ h h'
  | smul c G _ h =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (c • G) x) = c • fun x => e₁ x.1 * e₂ x.2 * G x := by
      funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact Submodule.smul_mem _ c h

theorem pair_carry (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a))
    (U₂ U₂' : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ)
    (f₁ : FlatFn e₁) (f₂ : FlatFn e₂) (c₁ : Carries e₁ U₁ U₁') (c₂ : Carries e₂ U₂ U₂')
    (hF : F ∈ pairSpace U₁ U₂) (hT : TypeH K₁ K₂ W₁ W₂ F) :
    (fun x => e₁ x.1 * e₂ x.2 * F x) ∈
      (pairSpace U₁' U₂' ⊓ typeHF (K₁ ⊓ KO E a) (K₂ ⊓ KO E b) W₁ W₂ : Submodule ℂ (H E a b → ℂ)) := by
  refine Submodule.mem_inf.2 ⟨mul_mem_pairSpace e₁ e₂ U₁ U₁' U₂ U₂' F c₁ c₂ hF, ?_, fun x => ?_⟩
  · intro u₁ hu₁ u₂ hu₂ x
    have h₁ : e₁ (x * (finGL E a u₁, finGL E b u₂)).1 = e₁ x.1 := f₁.fin_inv x.1 hu₁.2
    have h₂ : e₂ (x * (finGL E a u₁, finGL E b u₂)).2 = e₂ x.2 := f₂.fin_inv x.2 hu₂.2
    show e₁ (x * (finGL E a u₁, finGL E b u₂)).1 * e₂ (x * (finGL E a u₁, finGL E b u₂)).2 *
      F (x * (finGL E a u₁, finGL E b u₂)) = e₁ x.1 * e₂ x.2 * F x
    rw [h₁, h₂, hT.1 u₁ hu₁.1 u₂ hu₂.1 x]
  · have h : (fun k : Kinf E a × Kinf E b =>
        (fun y : H E a b => e₁ y.1 * e₂ y.2 * F y)
          (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) =
        (e₁ x.1 * e₂ x.2) • fun k : Kinf E a × Kinf E b =>
          F (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) := by
      funext k
      have h₁ : e₁ (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))).1 = e₁ x.1 :=
        f₁.inf_inv x.1 k.1
      have h₂ : e₂ (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))).2 = e₂ x.2 :=
        f₂.inf_inv x.2 k.2
      simp only [Pi.smul_apply, smul_eq_mul, h₁, h₂]
    rw [h]
    exact Submodule.smul_mem _ _ (hT.2 x)

end PairCarry

end GlobalTheory.CompanionTheory.LimV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSpaceCarriesFlatStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_space_carries_flat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ), FlatFn e₁ → FlatFn e₂ → Carries e₁ U₁ U₁' → Carries e₂ U₂ U₂' → F ∈ pairSpace U₁ U₂ → TypeH K₁ K₂ W₁ W₂ F → (fun x => e₁ x.1 * e₂ x.2 * F x) ∈ (pairSpace U₁' U₂' ⊓ typeHF (K₁ ⊓ KO E a) (K₂ ⊓ KO E b) W₁ W₂ : Submodule ℂ (H E a b → ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.pair_carry | exact GlobalTheory.CompanionTheory.LimV.pair_carry | (intros; apply GlobalTheory.CompanionTheory.LimV.pair_carry <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwist
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwist
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

theorem carries_tw {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (e : GA E N → ℂ)
    (U U' : Submodule ℂ (Sm E N)) (z : ℂ) (h : Carries e U U') : Carries e (tw U z) (tw U' z) := by
  rintro _ ⟨ψ, hψ, rfl⟩
  obtain ⟨ψ', hψ', hx⟩ := h ψ hψ
  refine ⟨mulChi N (Model.absC E z) ψ', ⟨ψ', hψ', rfl⟩, fun x => ?_⟩
  simp only [LinearEquiv.coe_coe, mulChi_apply, hx, mul_assoc]

end GlobalTheory.CompanionTheory.LimV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_twist : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (e : GA E N → ℂ) (U U' : Submodule ℂ (Sm E N)) (z : ℂ), Carries e U U' → Carries e (tw U z) (tw U' z) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.carries_tw | exact GlobalTheory.CompanionTheory.LimV.carries_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.carries_tw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableTwist
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableTwist
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem finStable_tw {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z : ℂ) (h : FinStable U) : FinStable (tw U z) := by
  rintro g _ ⟨ψ, hψ, rfl⟩
  exact ⟨_, U.add_mem (U.smul_mem _ (h g ψ hψ)) (U.smul_mem _ hψ), (act_mulChi _ (.fin g) ψ).symm⟩

end GlobalTheory.CompanionTheory.LimV
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableTwistStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finStable_twist : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (z : ℂ), FinStable U → FinStable (tw U z) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.finStable_tw | exact GlobalTheory.CompanionTheory.LimV.finStable_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.finStable_tw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedDiscrete
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedDiscrete
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.FdV

open GlobalTheory.CompanionTheory.AdmDiscFin GlobalTheory.LevelTypeProj

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem continuous_sliceTC (φ : Sm E N) (g : GA E N) :
    Continuous fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k)) := by
  have h1 : Continuous fun k : Kinf E N => (Unitary.toUnits k : GL (Fin N) (Cinf E)) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have e : (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) =
      fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin N) (Cinf E)).val) := by
    funext k
    rw [chart_val]
  rw [e]
  have hc : ContinuousOn (chart φ.1 g) (invSet E N) := (φ.2 g).continuousOn
  have h3' : Continuous fun k : Kinf E N =>
      ((Unitary.toUnits k : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) :=
    (Units.continuous_val (M := Matrix (Fin N) (Fin N) (Cinf E))).comp h1
  have h3 : Continuous fun k : Kinf E N =>
      toL ((Unitary.toUnits k : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) := h3'
  exact hc.comp_continuous h3 fun k => val_mem_invSet _

theorem fd_typed {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (V : Submodule ℂ (Sm E N))
    (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (hV : IsDiscrete V)
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (hW : FiniteDimensional ℂ W) :
    FiniteDimensional ℂ (typed V K W) := by
  haveI := hW
  obtain ⟨ψ, hψV, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot
  have hadm : PrAdm.SupSpansPsiPart V ψ = V :=
    (hV.irred _ (PrAdm.admissible_span_le V ψ) (PrAdm.isStable_admissible_span hV.stable ψ)).resolve_left fun h => hψ0 (by
      have h2 := PrAdm.mem_admissible_span_self hψV
      rw [h] at h2
      simpa using h2)
  let Y : Submodule ℂ (Kinf E N → ℂ) := Submodule.span ℂ
    {f | ∃ φ : Sm E N, φ ∈ typed V K W ∧ ∃ g : GA E N, f = fun k => φ.1 (g * infGL E N (Unitary.toUnits k))}
  have hYW : Y ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, hφ, g, rfl⟩
    exact hφ.2.2 g
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYW
  have hYl : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y := by
    intro f hf k
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, hφ, g, rfl⟩ := hf
      refine Submodule.subset_span ⟨φ, hφ, g * infGL E N (Unitary.toUnits k), funext fun x => ?_⟩
      simp only [map_mul, mul_assoc]
    | zero => exact Y.zero_mem
    | add x y _ _ hx hy => exact Y.add_mem hx hy
    | smul r x _ hx => exact Y.smul_mem r hx
  have hYc : ∀ f ∈ Y, Continuous f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, -, g, rfl⟩ := hf
      exact continuous_sliceTC φ g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  have hF := PrAdm.finiteDimensional_admissible_isotypic hV.aut (hV.aut ψ hψV) hK (dualRep Y hYl) (isContRep_dualRep Y hYl hYc)
  rw [hadm] at hF
  refine Submodule.finiteDimensional_of_le (S₂ := V ⊓ typePart K (dualRep Y hYl)) ?_
  intro φ hφ
  refine ⟨hφ.1, fun k hk => Subtype.ext (funext fun g => hφ.2.1 k hk g), fun g => ?_⟩
  exact le_coeffSpan_dualRep Y hYl (Submodule.subset_span ⟨φ, hφ, g, rfl⟩)

end GlobalTheory.CompanionTheory.LimV.FdV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedDiscreteStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_typed_discrete : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (V : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)), IsDiscrete V → IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed V K W) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.FdV.fd_typed | exact GlobalTheory.CompanionTheory.LimV.FdV.fd_typed | (intros; apply GlobalTheory.CompanionTheory.LimV.FdV.fd_typed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitVectorIdentity
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

section Tree

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def indFin {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) :=
  Submodule.span ℂ {φ | MemInd2 U₁ U₂ φ ∧ φ ∈ finVec (cptRep E (r + s))}

theorem indFin_le {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : indFin U₁ U₂ ≤ indSpan U₁ U₂ :=
  Submodule.span_mono fun _ h => h.1

theorem memInd2_of_indSpan {r s : ℕ} {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indSpan U₁ U₂) : MemInd2 U₁ U₂ φ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => add_mem (hx.2 k g) (hy.2 k g)⟩
    change x.1 _ + y.1 _ = x.1 g + y.1 g
    rw [hx.1, hy.1]
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => Submodule.smul_mem _ c (hx.2 k g)⟩
    change c * x.1 _ = c * x.1 g
    rw [hx.1]

theorem finVec_of_indFin {r s : ℕ} {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indFin U₁ U₂) : φ ∈ finVec (cptRep E (r + s)) :=
  (Submodule.span_le (s := {x | MemInd2 U₁ U₂ x ∧ x ∈ finVec (cptRep E (r + s))})
    (p := finVec (cptRep E (r + s)))).2
    (fun x (hx : MemInd2 U₁ U₂ x ∧ x ∈ finVec (cptRep E (r + s))) => hx.2) h

theorem mem_indFin {r s : ℕ} {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h₁ : MemInd2 U₁ U₂ φ) (h₂ : φ ∈ finVec (cptRep E (r + s))) : φ ∈ indFin U₁ U₂ :=
  Submodule.subset_span ⟨h₁, h₂⟩

theorem finStable_indFin {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) :
    FinStable (indFin U₁ U₂) := by
  intro g φ hφ
  refine mem_indFin (memInd2_of_indSpan (GlobalTheory.T.finStable_induced_span U₁ U₂ g φ (indFin_le _ _ hφ))) ?_
  have h1 := finVec_rt (finVec_of_indFin hφ) 1 g
  have e : rt E (r + s) (cf (r + s) 1 g) φ = act (.fin g) φ := by
    refine Subtype.ext (funext fun x => ?_)
    rw [cf, show (Unitary.toUnits (1 : Kinf E (r + s))) = 1 from map_one _, map_one, one_mul]
    rfl
  rwa [e] at h1

theorem mul_mem_Sm {N : ℕ} {e f : GA E N → ℂ} (he : e ∈ Sm E N) (hf : f ∈ Sm E N) : (fun x => e x * f x) ∈ Sm E N := by
  intro g
  refine ((he g).mul (hf g)).congr fun x hx => ?_
  have hx' : IsUnit (Matrix.of x) := hx
  simp [chart, hx']

def mulOp {N : ℕ} {e : GA E N → ℂ} (he : e ∈ Sm E N) : Sm E N →ₗ[ℂ] Sm E N where
  toFun φ := ⟨fun x => e x * φ.1 x, mul_mem_Sm he φ.2⟩
  map_add' φ ψ := Subtype.ext (funext fun x => mul_add _ _ _)
  map_smul' c φ := Subtype.ext (funext fun x => mul_left_comm _ _ _)

theorem carries_indFin {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (U₁ U₁' : Submodule ℂ (Sm E r))
    (U₂ U₂' : Submodule ℂ (Sm E s)) (h₁ : FlatFn e₁) (h₂ : FlatFn e₂) (a₁ : FinStable U₁) (a₁' : FinStable U₁')
    (a₂ : FinStable U₂) (a₂' : FinStable U₂') (c₁ : Carries e₁ U₁ U₁') (c₂ : Carries e₂ U₂ U₂') :
    Carries (nodeFn e₁ e₂) (indFin U₁ U₂) (indFin U₁' U₂') := by
  intro φ hφ
  obtain ⟨φ', h', he⟩ := GlobalTheory.T.carries_induced_node e₁ e₂ U₁ U₁' U₂ U₂' h₁ h₂ a₁ a₁' a₂ a₂' c₁ c₂ φ (indFin_le _ _ hφ)
  refine ⟨φ', mem_indFin (memInd2_of_indSpan h') ?_, he⟩
  have hF := GlobalTheory.T.flat_node_function e₁ e₂ h₁ h₂
  have hv : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k φ)) := finVec_of_indFin hφ
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k φ)).map (mulOp hF.sm)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine ⟨cptRep E (r + s) k φ, Submodule.subset_span ⟨k, rfl⟩, Subtype.ext (funext fun x => ?_)⟩
  have e0 : x * infGL E (r + s) (Unitary.toUnits k) = x * cf (r + s) k 1 := by
    rw [cf, map_one, mul_one]
  change nodeFn e₁ e₂ x * φ.1 (x * infGL E (r + s) (Unitary.toUnits k)) =
    φ'.1 (x * infGL E (r + s) (Unitary.toUnits k))
  rw [he, e0, hF.rinv x k 1 (one_mem _)]

theorem fd_rank_zero (U : Submodule ℂ (Sm E 0)) : FiniteDimensional ℂ U := by
  haveI : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  haveI : Finite (GA E 0) := Finite.of_subsingleton
  infer_instance
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem strip_node_inv {r s : ℕ} (a : Tr E r) (b : Tr E s) : ∀ {N : ℕ} (u : Tr E N), N = r + s →
    HEq u.strip (Tr.node a.strip b.strip) → ∃ (u₁ : Tr E r) (u₂ : Tr E s), HEq u (Tr.node u₁ u₂) ∧
      u₁.strip = a.strip ∧ u₂.strip = b.strip := by
  intro N u
  cases u with
  | leaf V z =>
    intro hN h
    exact Tr.noConfusion rfl HEq.rfl HEq.rfl HEq.rfl hN h
  | @node r' s' u₁ u₂ =>
    intro hN h
    simp only [Tr.strip] at h
    refine Tr.noConfusion rfl HEq.rfl HEq.rfl HEq.rfl hN h fun hr hs h₁ h₂ => ?_
    subst hr hs
    exact ⟨u₁, u₂, HEq.rfl, eq_of_heq h₁, eq_of_heq h₂⟩

theorem strip_node {r s : ℕ} (a : Tr E r) (b : Tr E s) (u : Tr E (r + s)) (h : u.strip = (Tr.node a b).strip) :
    ∃ (u₁ : Tr E r) (u₂ : Tr E s), u = Tr.node u₁ u₂ ∧ u₁.strip = a.strip ∧ u₂.strip = b.strip := by
  obtain ⟨u₁, u₂, h1, h2, h3⟩ := strip_node_inv a b u rfl (heq_of_eq h)
  exact ⟨u₁, u₂, eq_of_heq h1, h2, h3⟩

theorem strip_leaf {N : ℕ} (V : Submodule ℂ (Sm E N)) (z : ℂ) (u : Tr E N) (h : u.strip = (Tr.leaf V z).strip) :
    ∃ z', u = Tr.leaf V z' := by
  have key : ∀ {M : ℕ} (u : Tr E M), ∀ (hM : M = N), HEq u.strip (Tr.leaf V (0 : ℂ)) → ∃ z', HEq u (Tr.leaf V z') := by
    intro M u
    cases u with
    | leaf V' z' =>
      intro hM h
      simp only [Tr.strip] at h
      refine Tr.noConfusion rfl HEq.rfl HEq.rfl HEq.rfl hM h fun hn hV _ => ?_
      subst hn
      obtain rfl := eq_of_heq hV
      exact ⟨z', HEq.rfl⟩
    | node u₁ u₂ =>
      intro hM h
      exact Tr.noConfusion rfl HEq.rfl HEq.rfl HEq.rfl hM h
  obtain ⟨z', h1⟩ := key u rfl (heq_of_eq h)
  exact ⟨z', eq_of_heq h1⟩

theorem disc_of_good {N : ℕ} (s : Tr E N) : s.Good → s.Disc := by
  induction s with
  | leaf V z =>
    intro h
    simp only [Tr.Good] at h
    simp only [Tr.Disc]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1⟩
  | node a b iha ihb =>
    intro h
    simp only [Tr.Good] at h
    simp only [Tr.Disc]
    exact ⟨iha h.1, ihb h.2⟩

theorem space_leaf {N : ℕ} (V : Submodule ℂ (Sm E N)) (z : ℂ) : (Tr.leaf V z).space = tw V z := by
  rw [Tr.space]

theorem space_node {r s : ℕ} (a : Tr E r) (b : Tr E s) :
    (Tr.node a b).space = indFin (tw a.space ((s : ℂ) / 2)) (tw b.space (-(r : ℂ) / 2)) := by
  rw [Tr.space]
  rfl

theorem treestable {N : ℕ} (t : Tr E N) : t.Disc → FinStable t.space := by
  induction t with
  | leaf V z =>
    intro ht
    simp only [Tr.Disc] at ht
    rw [space_leaf]
    rcases ht with ⟨-, rfl, -⟩ | ht
    · exact GlobalTheory.T.finStable_twist _ z fun _ _ _ => trivial
    · exact GlobalTheory.T.finStable_twist V z fun g φ hφ => ht.2.stable (.fin g) φ hφ
  | node a b _ _ =>
    intro _
    rw [space_node]
    exact finStable_indFin _ _

theorem treefd {N : ℕ} (t : Tr E N) : t.Disc → ∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)),
    IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed t.space K W) := by
  induction t with
  | leaf V z =>
    intro ht
    simp only [Tr.Disc] at ht
    rw [space_leaf]
    rcases ht with ⟨rfl, -, -⟩ | ht
    · intro K W _ _
      exact fd_rank_zero _
    · exact GlobalTheory.T.finiteDimensional_typed_extension V z fun K W hK hW => GlobalTheory.T.finiteDimensional_typed_discrete V K W ht.2 hK hW
  | @node r' s' a b iha ihb =>
    intro ht
    simp only [Tr.Disc] at ht
    rw [space_node]
    intro K W hK hW
    haveI := GlobalTheory.T.finiteDimensional_typed_node (tw a.space ((s' : ℂ) / 2)) (tw b.space (-(r' : ℂ) / 2)) (GlobalTheory.T.finiteDimensional_typed_extension _ _ (iha ht.1))
      (GlobalTheory.T.finiteDimensional_typed_extension _ _ (ihb ht.2)) K W hK hW
    have hle : typed (indFin (tw a.space ((s' : ℂ) / 2)) (tw b.space (-(r' : ℂ) / 2))) K W ≤
        typed (indSpan (tw a.space ((s' : ℂ) / 2)) (tw b.space (-(r' : ℂ) / 2))) K W :=
      inf_le_inf_right _ (indFin_le _ _)
    exact Submodule.finiteDimensional_of_le hle

theorem twists_length {N : ℕ} (s : Tr E N) : ∀ (t : Tr E N), t.strip = s.strip → t.twists.length = s.twists.length := by
  induction s with
  | leaf V z =>
    intro t h
    obtain ⟨z', rfl⟩ := strip_leaf V z t h
    rfl
  | node a b iha ihb =>
    intro t h
    obtain ⟨u₁, u₂, rfl, h1, h2⟩ := strip_node a b t h
    simp only [Tr.twists, List.length_append, iha _ h1, ihb _ h2]

theorem treeflat {N : ℕ} (s : Tr E N) : ∀ (t : ℕ → Tr E N), s.Disc → (∀ k, (t k).Disc) → (∀ k, (t k).strip = s.strip) →
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0))) →
    ∃ e : ℕ → GA E N → ℂ, (∀ k, FlatFn (e k)) ∧ (∀ k, Carries (e k) (t k).space s.space) ∧
      ∀ x, Tendsto (fun k => e k x) atTop (𝓝 1) := by
  induction s with
  | @leaf M V z =>
    intro t _ _ hst hz
    choose zk hzk using fun k => strip_leaf V z (t k) (hst k)
    obtain rfl : t = fun k => Tr.leaf V (zk k) := funext hzk
    refine ⟨fun k => absFn M (z - zk k), fun k => GlobalTheory.T.flat_absolute_character M _, fun k => ?_, fun x => ?_⟩
    · simp only [space_leaf]
      exact GlobalTheory.T.carries_twist_absolute_character V (zk k) z
    · refine GlobalTheory.T.tendsto_absolute_character_one M x _ ?_
      have h0 := hz 0
      simp only [Tr.twists, List.getD_cons_zero] at h0
      simpa using (tendsto_const_nhds (x := z)).sub h0
  | @node r s' a b iha ihb =>
    intro t hs ht hst hz
    simp only [Tr.Disc] at hs
    choose u₁ u₂ hu h1 h2 using fun k => strip_node a b (t k) (hst k)
    obtain rfl : t = fun k => Tr.node (u₁ k) (u₂ k) := funext hu
    simp only [Tr.Disc] at ht
    have hd₁ : ∀ k, (u₁ k).Disc := fun k => (ht k).1
    have hd₂ : ∀ k, (u₂ k).Disc := fun k => (ht k).2
    have hl₁ : ∀ k, (u₁ k).twists.length = a.twists.length := fun k => twists_length a _ (h1 k)
    have hz₁ : ∀ i, Tendsto (fun k => ((u₁ k).twists.getD i 0)) atTop (𝓝 (a.twists.getD i 0)) := by
      intro i
      by_cases hi : i < a.twists.length
      · have h3 := hz i
        simp only [Tr.twists] at h3
        rw [List.getD_append _ _ _ _ hi] at h3
        exact h3.congr fun k => List.getD_append _ _ _ _ (by rw [hl₁]; exact hi)
      · have e1 : ∀ k, (u₁ k).twists.getD i 0 = 0 := fun k =>
          List.getD_eq_default _ _ (by rw [hl₁]; omega)
        rw [List.getD_eq_default _ _ (by omega)]
        simp only [e1]
        exact tendsto_const_nhds
    have hz₂ : ∀ i, Tendsto (fun k => ((u₂ k).twists.getD i 0)) atTop (𝓝 (b.twists.getD i 0)) := by
      intro i
      have h3 := hz (a.twists.length + i)
      simp only [Tr.twists] at h3
      rw [List.getD_append_right _ _ _ _ (by omega)] at h3
      simp only [Nat.add_sub_cancel_left] at h3
      refine h3.congr fun k => ?_
      rw [List.getD_append_right _ _ _ _ (by rw [hl₁]; omega), hl₁]
      simp only [Nat.add_sub_cancel_left]
    obtain ⟨e₁, he₁, hc₁, hl₁'⟩ := iha u₁ hs.1 hd₁ h1 hz₁
    obtain ⟨e₂, he₂, hc₂, hl₂'⟩ := ihb u₂ hs.2 hd₂ h2 hz₂
    refine ⟨fun k => nodeFn (e₁ k) (e₂ k), fun k => GlobalTheory.T.flat_node_function _ _ (he₁ k) (he₂ k), fun k => ?_, fun x => ?_⟩
    · rw [space_node, space_node]
      exact carries_indFin _ _ _ _ _ _ (he₁ k) (he₂ k) (GlobalTheory.T.finStable_twist _ _ (treestable _ (hd₁ k)))
        (GlobalTheory.T.finStable_twist _ _ (treestable _ hs.1)) (GlobalTheory.T.finStable_twist _ _ (treestable _ (hd₂ k)))
        (GlobalTheory.T.finStable_twist _ _ (treestable _ hs.2)) (GlobalTheory.T.carries_twist _ _ _ _ (hc₁ k)) (GlobalTheory.T.carries_twist _ _ _ _ (hc₂ k))
    · have h3 := (hl₁' (leviOf x).1).mul (hl₂' (leviOf x).2)
      rw [one_mul] at h3
      exact h3

end Tree

theorem limVec : PositivityTheory.Rg.BcB.SpectralAccumulation.LimVec := by
  intro _ E _ _ _ a b ι _ t₁ t₂ s₁ s₂ K₁ K₂ W₁ W₂ C lam lam₀ f hK₁ hK₂ hW₁ hW₂ _hC hs₁ hs₂ hd₁ hd₂ hst₁ hst₂ hz₁ hz₂
    hf0 hfm hfT hfe hlam
  have hD₁ : s₁.Disc := disc_of_good s₁ hs₁
  have hD₂ : s₂.Disc := disc_of_good s₂ hs₂
  obtain ⟨e₁, he₁, hc₁, hl₁⟩ := treeflat s₁ t₁ hD₁ hd₁ hst₁ hz₁
  obtain ⟨e₂, he₂, hc₂, hl₂⟩ := treeflat s₂ t₂ hD₂ hd₂ hst₂ hz₂
  have hO₁ : IsOpen ((K₁ ⊓ KO E a : Subgroup _) : Set (GL (Fin a) (Af E))) :=
    hK₁.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a)
  have hO₂ : IsOpen ((K₂ ⊓ KO E b : Subgroup _) : Set (GL (Fin b) (Af E))) :=
    hK₂.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E b)
  let X : Submodule ℂ (H E a b → ℂ) :=
    pairSpace s₁.space s₂.space ⊓ typeHF (K₁ ⊓ KO E a) (K₂ ⊓ KO E b) W₁ W₂
  haveI : FiniteDimensional ℂ X :=
    GlobalTheory.T.finiteDimensional_pair_typed _ _ _ _ _ _ (treefd s₁ hD₁ _ _ hO₁ hW₁) (treefd s₂ hD₂ _ _ hO₂ hW₂)
  let EE : ℕ → H E a b → ℂ := fun k x => e₁ k x.1 * e₂ k x.2
  have hEne : ∀ k x, EE k x ≠ 0 := fun k x => mul_ne_zero ((he₁ k).ne _) ((he₂ k).ne _)
  have hmem : ∀ k i, (fun x => EE k x * f k i x) ∈ X := fun k i =>
    GlobalTheory.T.pair_space_carries_flat (e₁ k) (e₂ k) _ _ _ _ K₁ K₂ W₁ W₂ _ (he₁ k) (he₂ k) (hc₁ k) (hc₂ k) (hfm k i) (hfT k i)
  let gM : ℕ → (ι → X) := fun k i => ⟨_, hmem k i⟩
  have hne : ∀ k, gM k ≠ 0 := by
    intro k h
    apply hf0 k
    funext i x
    have h1 : EE k x * f k i x = 0 := congrFun (congrArg Subtype.val (congrFun h i)) x
    exact (mul_eq_zero.1 h1).resolve_left (hEne k x)
  obtain ⟨c, φ, G, hφ, hG, hlim⟩ := GlobalTheory.T.exists_rescaled_convergent_subsequence gM hne
  let F : ι → H E a b → ℂ := fun i => (G i).1
  have hev : ∀ i x, Tendsto (fun k => c k * (EE (φ k) x * f (φ k) i x)) atTop (𝓝 (F i x)) := by
    intro i x
    exact hlim ((LinearMap.proj x) ∘ₗ X.subtype ∘ₗ (LinearMap.proj i))
  have hE1 : ∀ x, Tendsto (fun k => EE (φ k) x) atTop (𝓝 1) := fun x => by
    have h1 := (hl₁ x.1).mul (hl₂ x.2)
    rw [one_mul] at h1
    exact h1.comp hφ.tendsto_atTop
  have hft : ∀ i x, Tendsto (fun k => c k * f (φ k) i x) atTop (𝓝 (F i x)) := by
    intro i x
    have h2 := ((hE1 x).inv₀ one_ne_zero).mul (hev i x)
    simp only [inv_one, one_mul] at h2
    refine h2.congr fun k => ?_
    have h3 := hEne (φ k) x
    field_simp
  refine ⟨F, ?_, fun i => (G i).2.1, fun i => ⟨?_, (G i).2.2.2⟩, fun h hh => ?_⟩
  · intro h
    apply hG
    funext i
    exact Subtype.ext (congrFun h i)
  · intro u₁ hu₁ u₂ hu₂ x
    refine tendsto_nhds_unique (hft i _) ((hft i x).congr fun k => ?_)
    rw [(hfT _ i).1 u₁ hu₁ u₂ hu₂ x]
  · funext i x
    have hA : Tendsto (fun k => heckeAct h (fun j y => c k * f (φ k) j y) i x) atTop (𝓝 (heckeAct h F i x)) := by
      simp only [heckeAct, Finsupp.sum]
      exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun g _ => (hft j _).const_mul _
    have hB : ∀ k, heckeAct h (fun j y => c k * f (φ k) j y) i x = lam (φ k) h * (c k * f (φ k) i x) := by
      intro k
      have h1 : heckeAct h (f (φ k)) i x = lam (φ k) h * f (φ k) i x :=
        congrFun (congrFun (hfe (φ k) h hh) i) x
      have h2 : heckeAct h (fun j y => c k * f (φ k) j y) i x = c k * heckeAct h (f (φ k)) i x := by
        simp only [heckeAct, Finsupp.sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun g _ => ?_
        ring
      rw [h2, h1]
      ring
    have hC : Tendsto (fun k => lam (φ k) h * (c k * f (φ k) i x)) atTop (𝓝 (lam₀ h * F i x)) :=
      ((hlam h hh).comp hφ.tendsto_atTop).mul (hft i x)
    exact tendsto_nhds_unique (hA.congr hB) hC

end GlobalTheory.CompanionTheory.LimV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitVectorIdentityStatement
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_vector_identity : PositivityTheory.Rg.BcB.SpectralAccumulation.LimVec := by
  first | exact @GlobalTheory.CompanionTheory.LimV.limVec | exact GlobalTheory.CompanionTheory.LimV.limVec | (intros; apply GlobalTheory.CompanionTheory.LimV.limVec <;> assumption)
end PositivityTheory.Rg.BcB.SpectralAccumulation
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.EisensteinFinalOfSeparation
namespace PositivityTheory.Rg.BcB.SpectralAccumulation

theorem eisenstein_final_of_separation (hS : Sep4) : EFinal :=
  eFinal_of hS FiniteDiscreteTypes.finDisc (GlobalTheory.T.limit_vector_identity : LimVec)

end PositivityTheory.Rg.BcB.SpectralAccumulation
end

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

theorem eFinal_holds : EFinal := eisenstein_final_of_separation Cz.separation_holds

end PositivityTheory.Rg.BcB.SpectralAccumulation
