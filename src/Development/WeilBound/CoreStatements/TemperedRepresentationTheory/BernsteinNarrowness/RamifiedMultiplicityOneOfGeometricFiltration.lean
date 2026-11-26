module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiag
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KCoinvOfNarrow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SoCoinvOfNarrow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMultiplicityOneIrreducibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCharOfCondLE
open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitNarrow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitDict PositivityTheory.ThK.SplitAsm

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_of_condLE {ϖ : kˣ} {e : ℕ} {χ : kˣ →* ℂˣ} (h : CondLE ϖ e χ) : IsSmoothChar χ := by
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have h1 : IsOpen (({x : kˣ | (x : k) ∈ (𝒪[k] : Set k)} ∩ {x : kˣ | ((x⁻¹ : kˣ) : k) ∈ (𝒪[k] : Set k)}) ∩
      {x : kˣ | ((x : k) - 1) * (((ϖ ^ e : kˣ) : k))⁻¹ ∈ (𝒪[k] : Set k)}) :=
    ((ho.preimage Units.continuous_val).inter (ho.preimage Units.continuous_coe_inv)).inter
      (ho.preimage ((Units.continuous_val.sub continuous_const).mul continuous_const))
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (h1.mem_nhds ?_) ?_)
  · refine ⟨⟨one_mem 𝒪[k], by simpa using one_mem 𝒪[k]⟩, ?_⟩
    simpa using zero_mem 𝒪[k]
  · rintro x ⟨⟨hx, hx'⟩, hx''⟩
    have a1 : valuation k (x : k) ≤ 1 := hx
    have a2 : valuation k ((x⁻¹ : kˣ) : k) ≤ 1 := hx'
    have a3 : valuation k (((x : k) - 1) * (((ϖ ^ e : kˣ) : k))⁻¹) ≤ 1 := hx''
    have hc : valuation k (((ϖ ^ e : kˣ) : k)) ≠ 0 := by simp
    refine h x ⟨le_antisymm a1 ?_, ?_⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀] at a2
      exact (inv_le_one₀ (zero_lt_iff.2 (by simp))).1 a2
    · rw [map_mul, map_inv₀] at a3
      have a4 := (mul_inv_le_iff₀ (zero_lt_iff.2 hc)).1 a3
      rwa [one_mul] at a4

def IndIrredNarrow : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ), IsSmoothChar α → IsSmoothChar β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
    a' < a → ∀ N : Submodule ℂ (GL (Fin (a + a')) k → ℂ), N ≤ indSp a a' α β → (∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) →
      N = ⊥ ∨ N = indSp a a' α β

theorem indIrredNarrow_of
    (NB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
      (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
      (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) : IndIrredNarrow := by
  intro k _ _ _ _ a a' α β sα sβ hα hβ hlt N hN hr
  by_cases h0 : N = ⊥
  · exact Or.inl h0
  refine Or.inr (le_antisymm hN ?_)
  obtain ⟨F, hFN, hF0⟩ := (Submodule.ne_bot_iff N).1 h0
  have hI : (parInd (two (stdE a a')) (rhoD a a' α β)).IsIrreducible :=
    NB k a a' α β sα sβ hα hβ (Or.inl hlt.ne')
  let S : Subrepresentation (parInd (two (stdE a a')) (rhoD a a' α β)) :=
    ⟨N.comap (toFn a a' α β), fun g f hf => hr g _ hf⟩
  rcases hI.eq_bot_or_eq_top S with e | e
  · obtain ⟨f, rfl⟩ := exists_toFn (hN hFN)
    have hf : f ∈ S.toSubmodule := hFN
    rw [e] at hf
    have hf0 : f = 0 := hf
    exact absurd (by rw [hf0, map_zero]) hF0
  · intro G hG
    obtain ⟨f, rfl⟩ := exists_toFn hG
    have hf : f ∈ S.toSubmodule := by rw [e]; trivial
    exact hf

theorem irred_of_setting (hI : IndIrredNarrow) {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ} (H : HidaSetting a a' ϖ α β ν)
    (N : Submodule ℂ (GL (Fin (a + a')) k → ℂ)) (hN : N ≤ indSp a a' α β) (hst : ∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) :
    N = ⊥ ∨ N = indSp a a' α β := by
  obtain ⟨e, h1, h2⟩ := H.cond
  exact hI k a a' α β (isSmoothChar_of_condLE h1) (isSmoothChar_of_condLE h2) H.unitα H.unitβ H.lt N hN hst

theorem onto_of_irred (hI : IndIrredNarrow) {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ} (H : HidaSetting a a' ϖ α β ν)
    {X : Type} [TopologicalSpace X] (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hadd : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁) (hmem : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ)) (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) :
    ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by
  have h0 : p 0 = 0 := by
    have := hadd 0 (zero_mem _) 0 (zero_mem _) 1
    simpa using this
  let N : Submodule ℂ (GL (Fin (a + a')) k → ℂ) :=
    { carrier := {F | ∃ Φ ∈ SB X, p Φ = F}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩
        exact ⟨Φ + Φ₁, add_mem hΦ hΦ₁, by simpa using hadd Φ hΦ Φ₁ hΦ₁ 1⟩
      zero_mem' := ⟨0, zero_mem _, h0⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, rfl⟩
        exact ⟨c • Φ, (SB X).smul_mem c hΦ, by simpa [h0] using hadd 0 (zero_mem _) Φ hΦ c⟩ }
  rcases irred_of_setting hI H N (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hmem Φ hΦ)
    (by rintro h₁ _ ⟨Φ, hΦ, rfl⟩; exact heq Φ hΦ h₁) with h | h
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    exact absurd ((Submodule.eq_bot_iff N).1 h _ ⟨Φ, hΦ, rfl⟩) hne
  · intro F hF
    rw [← h] at hF
    exact hF

end Local

section Ram

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace

theorem ramMaps_of (hI : IndIrredNarrow) : RamMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν H hν
  exact ⟨fun _ h _ h₁ c => pRam_add H hν h h₁ c, fun _ h _ h₁ c => pRam'_add H h h₁ c, fun _ h => pRam_mem H hν h,
    fun _ h => pRam'_mem H h, fun _ h g => pRam_inv H hν h g, fun Ψ _ g => pRam'_inv Ψ g, fun Φ _ h => pRam_equiv Φ h,
    fun Ψ _ h => pRam'_equiv Ψ h,
    onto_of_irred hI H _ (fun _ h _ h₁ c => pRam_add H hν h h₁ c) (fun _ h => pRam_mem H hν h)
      (fun Φ h h₁ => ⟨_, omA_mem_SB ν β 1 h₁ h, pRam_equiv Φ h₁⟩) (pRam_ne_zero H),
    onto_of_irred hI H _ (fun _ h _ h₁ c => pRam'_add H h h₁ c) (fun _ h => pRam'_mem H h)
      (fun Ψ h h₁ => ⟨_, omB_mem_SB ν α 1 h₁ h, pRam'_equiv Ψ h₁⟩) (pRam'_ne_zero H)⟩

end Ram

section Fin

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.KCo PositivityTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] PositivityTheory.ThK.SplitAsm.measFv PositivityTheory.ThK.SplitAsm.borelFv

theorem finRam_of (hR : RamMaps) (hRN : RamNonzero) (hI : IndIrredNarrow) (hD : Dict) (hAU : ActsUniq) (hC : ChrFacts) :
    FinRam := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  have hP : v ∈ B.P := hT.chars.sub hv
  obtain ⟨hα, hβ, hν, hcond, hram, -⟩ := hC F E B X a a' v (B.τ ⟨v, hP⟩) hT.chars
  have hS : HidaSetting a a' (unifAt v) (chrW X.α (B.τ ⟨v, hP⟩)) (chrW X.β (B.τ ⟨v, hP⟩)) (chrW X.ν (B.τ ⟨v, hP⟩)) :=
    ⟨GlobalTheory.SplitFlip.exists_isUnif.choose_spec, hα, hβ, hν, hT.geo.lt, hT.geo.even, hcond⟩
  obtain ⟨hlin, hlin', hmem, hmem', hinv, hinv', heq, heq', hon, hon'⟩ := hR (Fv F v) a a' _ _ _ _ hS (hram hv)
  obtain ⟨Φ0, hΦ0, hnz⟩ := hRN (Fv F v) a a' _ _ _ _ hS (hram hv)
  obtain ⟨b, b', c, ι, ι', gl, gl', hl, hW, hB, hbas, hvac, hvac', hRg, hRh, hRg', hRh', hhl⟩ :=
    hD F E σ B a a' G X om om' hT v (B.τ ⟨v, hP⟩)
  obtain ⟨rfl, rfl, rfl⟩ := hbas hP rfl
  obtain ⟨p, p', hp, hp', hon1, hon1', hinv1, hinv1', heq1, hnt, hirr1⟩ := core hAU v G om om' _ _ _ (indSp a a' _ _)
    (pRam a a' (unifAt v) (chrW X.ν (B.τ ⟨v, hP⟩)) (chrW X.β (B.τ ⟨v, hP⟩)))
    (pRam' a a' (chrW X.ν (B.τ ⟨v, hP⟩)) (chrW X.α (B.τ ⟨v, hP⟩)))
    (fun Φ h Φ₁ h₁ => hlin Φ h Φ₁ h₁) (fun Φ h Φ₁ h₁ => hlin' Φ h Φ₁ h₁)
    (fun Φ h => hmem Φ h) (fun Φ h => hmem' Φ h) (fun Φ h => hinv Φ h)
    (fun Φ h => hinv' Φ h) (fun Φ h => heq Φ h) (fun Φ h => heq' Φ h)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon y hy; exact ⟨Φ, h, r⟩)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon' y hy; exact ⟨Φ, h, r⟩) ⟨Φ0, hΦ0, hnz⟩
    (fun N hN hst => irred_of_setting hI hS N hN hst) ι ι' hW.bij hB.bij gl gl' hl hRg hRh hRg' hRh' hhl
  refine ⟨oneMaps v _ p p', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneMaps_p]; exact hon1
  · rw [oneMaps_p']; exact hon1'
  · rw [oneMaps_p]; exact hinv1
  · rw [oneMaps_p']; exact hinv1'
  · rw [oneMaps_p, oneMaps_p']; exact heq1
  · exact hnt
  · rw [oneMaps_p]; exact hirr1
  · intro hv'; exact absurd hv hv'
  · intro hv' _
    refine ⟨ι, ι', hW, hB, hvac, hvac', fun φ hφ φ' hφ' => ?_⟩
    rw [oneMaps_p, oneMaps_p']
    refine ⟨fun h => ?_, fun h => Subtype.ext ?_⟩
    · have := congrArg Subtype.val h
      erw [hp φ hφ, hp' φ' hφ'] at this
      exact this
    · erw [hp φ hφ, hp' φ' hφ']
      exact h

end Fin

theorem finRam_of_narrow :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
      (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
      (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) → PositivityTheory.ThK.FinRam :=
  fun NB => finRam_of (ramMaps_of (indIrredNarrow_of NB)) ramified_map_ne_zero (indIrredNarrow_of NB) split_place_dictionary
    PositivityTheory.KCo.action_uniqueness split_character_facts

end GlobalTheory.CompanionTheory.SplitNarrow
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Imports
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdmissibleDegenerate
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenSeries

theorem isAdmissible_degenerate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ →
    IsAdmissible (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  intro k _ _ _ _ a b χ₁ χ₂ _ _
  exact GlobalTheory.SmGL.ParIndAdm.isAdmissible_parInd _ _

end GlobalTheory.CompanionTheory.DegenSeries
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialSubrepresentation
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.DegPrinSeries

theorem nontrivial_subrepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → Nontrivial (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))) := by
  intro k _ _ _ _ a b χ₁ χ₂ hχ₁ hχ₂
  have hdetChar : ∀ (m : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ →
      GlobalTheory.PRep.IsSmooth (GlobalTheory.SmGL.detRep (Fin m) χ) := by
    intro m χ hχ
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ) := by
      rw [Units.continuous_iff]
      constructor
      · have hval : (Units.val ∘ (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ)) =
            fun g : GL (Fin m) k => Matrix.det (g : Matrix (Fin m) (Fin m) k) := by
          funext g
          exact Matrix.GeneralLinearGroup.val_det_apply g
        rw [hval]
        exact Units.continuous_val.matrix_det
      · have hinv : (fun g : GL (Fin m) k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
            fun g => Matrix.det ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) := by
          funext g
          rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [hinv]
        exact Units.continuous_coe_inv.matrix_det
    unfold GlobalTheory.SmGL.detRep
    rw [GlobalTheory.SmGL.isSmooth_ofChar_iff]
    unfold GlobalTheory.SmGL.IsSmoothChar at hχ ⊢
    exact hc.isOpen_preimage _ hχ
  have hsmooth := GlobalTheory.SmGL.isSmooth_comp
    (GlobalTheory.SmGL.isSmooth_extTensor (hdetChar a χ₁ hχ₁) (hdetChar b χ₂ hχ₂))
    (GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm.toMonoidHom
    (by exact (continuous_apply Bool.false).prodMk (continuous_apply Bool.true))
  have hu : ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (TensorProduct.lid ℂ ℂ) h0
    simp at this
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : a + b = a + b))) _
    hsmooth ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
  refine ⟨⟨⟨⊥, fun g ⦃v⦄ hv => ?_⟩, ⟨⊤, fun _ ⦃_⦄ _ => Submodule.mem_top⟩, fun hEq => ?_⟩⟩
  · rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  · have hsub := congrArg Subrepresentation.toSubmodule hEq
    have hf : f = 0 := (Submodule.mem_bot ℂ).1 (Submodule.eq_top_iff'.1 hsub f)
    rw [hf] at hf1
    apply hu
    rw [← hf1]
    first
    | rfl
    | simp

end GlobalTheory.CompanionTheory.DegPrinSeries
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharacters
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorScalarDiagonal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorScalarDiagonal
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CellDiag

def evalOne {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W) :
    smoothPart (ind H σ) →ₗ[ℂ] W :=
  (LinearMap.proj (1 : G)).comp ((indSpace H σ).subtype.comp (smoothPart (ind H σ)).subtype)

theorem evalOne_injective {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (hH : H = ⊤) (σ : Representation ℂ H W) :
    Function.Injective (evalOne H σ) := by
  subst hH
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro v hv
  have h0 : (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 1 = 0 := hv
  have hmem : ∀ (h : (⊤ : Subgroup G)) (x : G),
      (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 (↑h * x) =
        σ h ((v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 x) :=
    (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).2
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have key : (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 x =
      σ ⟨x, Subgroup.mem_top x⟩ ((v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 1) := by
    have := hmem ⟨x, Subgroup.mem_top x⟩ 1
    rwa [mul_one] at this
  rw [key, h0, map_zero]
  first
  | rfl
  | simp

theorem dichotomy {V X T : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup T] [Module ℂ T] [Module.Finite ℂ X] (hX : Module.finrank ℂ X ≤ 1)
    (hT : Module.finrank ℂ T = 1) (ι : V →ₗ[ℂ] X) (hι : Function.Injective ι)
    (φ ψ : V →ₗ[ℂ] T) : φ = 0 ∨ ∃ c : ℂ, ψ = c • φ := by
  classical
  by_cases hφ : φ = 0
  · exact Or.inl hφ
  right
  haveI : Module.Finite ℂ V := Module.Finite.of_injective ι hι
  have hV : Module.finrank ℂ V ≤ 1 := (LinearMap.finrank_le_finrank_of_injective hι).trans hX
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hφ (LinearMap.ext hne)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (map_zero φ)
  haveI : Nontrivial V := ⟨⟨v, 0, hv0⟩⟩
  have hV1 : Module.finrank ℂ V = 1 := le_antisymm hV Module.finrank_pos
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (φ v) hv).mp hT (ψ v)
  refine ⟨c, LinearMap.ext fun w => ?_⟩
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).mp hV1 w
  first
  | (rw [← ht, map_smul, map_smul, LinearMap.smul_apply, ← hc]; done)
  | (rw [← ht, ← hc]; simp [smul_comm])
  | (subst ht; simp [← hc, smul_smul, mul_comm])

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sizeMatrix_true_false {a b : ℕ}
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (h : B.1 false true = 0) :
    B.1 true false = 0 := by
  have hr := B.2.1 false
  have hc := B.2.2 false
  first
  | (rw [Fintype.sum_bool] at hr hc; omega)
  | (simp only [Fintype.sum_bool] at hr hc; omega)

theorem relParab_eq_top {a b : ℕ}
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (h : B.1 false true = 0)
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j) :
    relParab k (c := fun j i => Fin (B.1 i j)) g = ⊤ := by
  have h' := GlobalTheory.CompanionTheory.CellDiag.sizeMatrix_true_false B h
  rw [eq_top_iff]
  intro x _
  rw [GlobalTheory.SmGL.relParab, Subgroup.mem_pi]
  intro j _
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro p q i i' hqp
  rw [Bool.lt_iff] at hqp
  obtain ⟨rfl, rfl⟩ := hqp
  exfalso
  cases j
  · have := i.isLt
    omega
  · have := i'.isLt
    omega

theorem diag_cell_at_most_one_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true = 0 → (∀ φ ψ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ B f g h φ ψ
  have hT : Module.finrank ℂ (ℂ ⊗[ℂ] ℂ) = 1 := by
    first
    | rw [Module.finrank_tensorProduct, Module.finrank_self]
    | simp [Module.finrank_tensorProduct]
    | simp
  refine GlobalTheory.CompanionTheory.CellDiag.dichotomy ?_ hT
    (GlobalTheory.CompanionTheory.CellDiag.evalOne _ _)
    (GlobalTheory.CompanionTheory.CellDiag.evalOne_injective _ (GlobalTheory.CompanionTheory.CellDiag.relParab_eq_top (k := k) B h g) _)
    φ.toLinearMap ψ.toLinearMap
  first
  | exact (Submodule.finrank_quotient_le _).trans hT.le
  | exact (Submodule.finrank_quotient_le _).trans (le_of_eq hT)
  | (refine (Submodule.finrank_quotient_le _).trans ?_; simp)

end GlobalTheory.CompanionTheory.CellDiag
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorScalarDiagonalStatement
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_functor_scalar_diagonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true = 0 → (∀ φ ψ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.CellDiag.diag_cell_at_most_one_map | exact GlobalTheory.CompanionTheory.CellDiag.diag_cell_at_most_one_map | (intros; apply GlobalTheory.CompanionTheory.CellDiag.diag_cell_at_most_one_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotient
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Filtration

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

noncomputable def descend (f : π.IntertwiningMap σ) (B A : Subrepresentation π)
    (h : ∀ v ∈ A.toSubmodule, f v = 0) : (subQuot B A).IntertwiningMap σ where
  toLinearMap := Submodule.liftQ _ (f.toLinearMap ∘ₗ B.toSubmodule.subtype) (fun v hv => h v.1 hv)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    ext v
    exact f.isIntertwining _ _ g v.1

theorem vanish_step (f : π.IntertwiningMap σ) {A B : Subrepresentation π}
    (hA : ∀ v ∈ A.toSubmodule, f v = 0)
    (hz : ∀ φ : (subQuot B A).IntertwiningMap σ, φ.toLinearMap = 0) :
    ∀ v ∈ B.toSubmodule, f v = 0 := by
  intro v hv
  have h1 := LinearMap.congr_fun (hz (GlobalTheory.CompanionTheory.Filtration.descend f B A hA)) (Submodule.Quotient.mk ⟨v, hv⟩)
  have h2 : (GlobalTheory.CompanionTheory.Filtration.descend f B A hA).toLinearMap (Submodule.Quotient.mk ⟨v, hv⟩) = f v := by
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Filtration.descend, Submodule.liftQ_apply]
  rw [← h2, h1, LinearMap.zero_apply]

theorem vanish_climb {N : ℕ} (S : Fin (N + 1) → Subrepresentation π) (f : π.IntertwiningMap σ)
    (lo : ℕ) (hlo : lo < N + 1)
    (h0 : ∀ v ∈ (S ⟨lo, hlo⟩).toSubmodule, f v = 0) (hi : ℕ) (hle : lo ≤ hi) :
    ∀ (hhi : hi < N + 1),
      (∀ t : Fin N, lo ≤ t.val → t.val < hi →
        ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) →
      ∀ v ∈ (S ⟨hi, hhi⟩).toSubmodule, f v = 0 := by
  induction hi, hle using Nat.le_induction with
  | base =>
    intro _ _
    exact h0
  | succ k hk ih =>
    intro hhi hz
    have hkN : k < N := Nat.lt_of_succ_lt_succ hhi
    have ih' := ih (Nat.lt_succ_of_lt hkN)
      (fun t h1 h2 => hz t h1 (Nat.lt_succ_of_lt h2))
    exact GlobalTheory.CompanionTheory.Filtration.vanish_step f
      (A := S (⟨k, hkN⟩ : Fin N).castSucc) (B := S (⟨k, hkN⟩ : Fin N).succ) ih'
      (hz ⟨k, hkN⟩ hk (Nat.lt_succ_self k))

theorem intertwining_proportional :
    ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ G V) (σ : Representation ℂ G W) (N : ℕ)
      (S : Fin (N + 1) → Subrepresentation π), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ →
      ∀ t₀ : Fin N,
        (∀ φ ψ : (subQuot (S t₀.succ) (S t₀.castSucc)).IntertwiningMap σ,
          φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) →
        (∀ t : Fin N, t ≠ t₀ →
          ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) →
        ∀ φ ψ : π.IntertwiningMap σ,
          φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  intro G V W _ _ _ _ _ π σ N S _ hS0 hST t₀ hmult hzero φ ψ
  have happ : ∀ (f : π.IntertwiningMap σ) (v : V), f.toLinearMap v = f v :=
    fun f v => Representation.IntertwiningMap.toLinearMap_apply π σ f v
  have hbot : ∀ f : π.IntertwiningMap σ, ∀ v ∈ (S ⟨0, Nat.succ_pos N⟩).toSubmodule, f v = 0 := by
    intro f v hv
    have e0 : (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)) = 0 := by
      first
        | exact Fin.mk_zero
        | exact Fin.ext (by simp)
    rw [e0, hS0] at hv
    have hv0 : v = 0 := by
      first
        | exact (Submodule.mem_bot ℂ).1 hv
        | exact hv
        | simpa using hv
        | exact (Submodule.mem_bot ℂ).1
            ((bot_le : (⊥ : Subrepresentation π) ≤
              ⟨⊥, fun g w hw => by rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _⟩) hv)
    rw [hv0, ← happ, map_zero]
  have htop : ∀ v : V, v ∈ (S (Fin.last N)).toSubmodule := by
    intro v
    rw [hST]
    first
      | exact Submodule.mem_top
      | trivial
      | exact (le_top : (⟨⊤, fun _ _ _ => Submodule.mem_top⟩ : Subrepresentation π) ≤ ⊤)
          (Submodule.mem_top (x := v))
      | simp
  have hlow : ∀ f : π.IntertwiningMap σ, ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0 := fun f =>
    GlobalTheory.CompanionTheory.Filtration.vanish_climb S f 0 (Nat.succ_pos N) (hbot f)
      t₀.val (Nat.zero_le _) (Nat.lt_succ_of_lt t₀.isLt)
      (fun t _ ht => hzero t (by rintro rfl; exact lt_irrefl _ ht))
  have hup : ∀ f : π.IntertwiningMap σ, (∀ v ∈ (S t₀.succ).toSubmodule, f v = 0) → ∀ v, f v = 0 := by
    intro f hf v
    have h := GlobalTheory.CompanionTheory.Filtration.vanish_climb S f (t₀.val + 1)
      (Nat.succ_lt_succ t₀.isLt) hf N t₀.isLt (Nat.lt_succ_self N)
      (fun t h1 _ => hzero t (by rintro rfl; exact Nat.not_succ_le_self _ h1))
    exact h v (htop v)
  have hdesc : ∀ (f : π.IntertwiningMap σ) (hf : ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0) (v : V)
      (hv : v ∈ (S t₀.succ).toSubmodule),
      (GlobalTheory.CompanionTheory.Filtration.descend f (S t₀.succ) (S t₀.castSucc) hf).toLinearMap
        (Submodule.Quotient.mk ⟨v, hv⟩) = f v := by
    intro f hf v hv
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Filtration.descend, Submodule.liftQ_apply]
  rcases hmult (GlobalTheory.CompanionTheory.Filtration.descend φ (S t₀.succ) (S t₀.castSucc) (hlow φ))
      (GlobalTheory.CompanionTheory.Filtration.descend ψ (S t₀.succ) (S t₀.castSucc) (hlow ψ)) with h | ⟨c, hc⟩
  · left
    apply LinearMap.ext
    intro v
    rw [LinearMap.zero_apply, happ]
    refine hup φ ?_ v
    intro w hw
    rw [← hdesc φ (hlow φ) w hw, h, LinearMap.zero_apply]
  · right
    refine ⟨c, ?_⟩
    let χ : π.IntertwiningMap σ :=
      { toLinearMap := ψ.toLinearMap - c • φ.toLinearMap
        isIntertwining' := fun g => by
          first
            | rw [LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_sub, LinearMap.comp_smul,
                ψ.isIntertwining' g, φ.isIntertwining' g]
            | (ext v
               have h1 := LinearMap.congr_fun (ψ.isIntertwining' g) v
               have h2 := LinearMap.congr_fun (φ.isIntertwining' g) v
               simp only [LinearMap.comp_apply] at h1 h2
               simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2,
                 map_sub, map_smul]) }
    have hχ : ∀ v, χ v = ψ v - c • φ v := by
      intro v
      rw [← happ, ← happ, ← happ]
      rfl
    have hχS : ∀ v ∈ (S t₀.succ).toSubmodule, χ v = 0 := by
      intro v hv
      rw [hχ, ← hdesc ψ (hlow ψ) v hv, ← hdesc φ (hlow φ) v hv, hc, LinearMap.smul_apply, sub_self]
    apply LinearMap.ext
    intro v
    have h := hup χ hχS v
    rw [hχ, sub_eq_zero] at h
    rw [LinearMap.smul_apply, happ, happ]
    exact h

end GlobalTheory.CompanionTheory.Filtration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotientStatement
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_unique_subquotient : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (σ : Representation ℂ G W) (N : ℕ) (S : Fin (N + 1) → Subrepresentation π), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ t₀ : Fin N, (∀ φ ψ : (subQuot (S t₀.succ) (S t₀.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) → (∀ t : Fin N, t ≠ t₀ → ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) → ∀ φ ψ : π.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  first | exact @GlobalTheory.CompanionTheory.Filtration.intertwining_proportional | exact GlobalTheory.CompanionTheory.Filtration.intertwining_proportional | (intros; apply GlobalTheory.CompanionTheory.Filtration.intertwining_proportional <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharacters
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem proportional_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ')
    (h : ∀ φ ψ : τ'.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap)
    (φ ψ : τ.IntertwiningMap σ) :
    φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  rcases h (φ.comp E.symm.toIntertwiningMap) (ψ.comp E.symm.toIntertwiningMap) with h0 | ⟨c, hc⟩
  · left
    ext v
    have := LinearMap.congr_fun h0 (E v)
    simpa using this
  · right
    refine ⟨c, ?_⟩
    ext v
    have := LinearMap.congr_fun hc (E v)
    simpa using this

theorem eq_zero_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ') (h : ∀ φ : τ'.IntertwiningMap σ, φ.toLinearMap = 0)
    (φ : τ.IntertwiningMap σ) : φ.toLinearMap = 0 := by
  ext v
  have := LinearMap.congr_fun (h (φ.comp E.symm.toIntertwiningMap)) (E v)
  simpa using this

theorem exists_diagonal_sizeMatrix (a b : ℕ) :
    ∃ D : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)),
      ∀ B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)), B = D ↔ B.1 false true = 0 := by
  have card_f : Fintype.card (Two (Fin a) (Fin b) false) = a := Fintype.card_fin a
  have card_t : Fintype.card (Two (Fin a) (Fin b) true) = b := Fintype.card_fin b
  refine ⟨⟨fun i j => if i = j then (if i then b else a) else 0, ?_, ?_⟩, fun B => ⟨?_, ?_⟩⟩
  · intro i; cases i <;> simp [card_f, card_t]
  · intro j; cases j <;> simp [card_f, card_t]
  · rintro rfl; simp
  · intro hB
    have r0 := B.2.1 false
    have r1 := B.2.1 true
    have c0 := B.2.2 false
    have c1 := B.2.2 true
    simp only [Fintype.sum_bool, card_f, card_t] at r0 r1 c0 c1
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> simp <;> omega


set_option maxHeartbeats 600000 in
theorem mackey_maps_proportional : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (SmGL.jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ hJ h₁ h₂ u₁ u₂ hne
  have hc : Continuous (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom :=
    continuous_prodMk.2 ⟨continuous_apply _, continuous_apply _⟩
  have hsm : IsSmooth ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
      ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ hc
  obtain ⟨N, bb, hb⟩ := hJ Bool Bool (Fin (a + b)) (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))
    (two (stdSum (rfl : a + b = a + b))) (two (stdSum (rfl : a + b = a + b)))
  obtain ⟨S, hm, hbot, htop, hE⟩ := hb (TensorProduct ℂ ℂ ℂ) _ hsm
  obtain ⟨D, hD⟩ := exists_diagonal_sizeMatrix a b
  obtain ⟨t₀, ht₀⟩ := bb.surjective D
  refine GlobalTheory.T.filtration_unique_subquotient _ ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) N S hm hbot htop t₀ ?_ ?_
  · exact proportional_of_equiv (hE t₀ (SizeMatrix.nonempty_rows (bb t₀)).some (SizeMatrix.nonempty_cols (bb t₀)).some).some
      (GlobalTheory.T.cell_functor_scalar_diagonal k a b χ₁ χ₂ (bb t₀) _ _ ((hD _).1 ht₀))
  · intro t ht
    exact eq_zero_of_equiv (hE t (SizeMatrix.nonempty_rows (bb t)).some (SizeMatrix.nonempty_cols (bb t)).some).some
      (GlobalTheory.T.cell_functor_nonscalar_offdiag k a b χ₁ χ₂ h₁ h₂ u₁ u₂ hne (bb t) _ _ fun h0 =>
        ht (bb.injective (((hD _).2 h0).trans ht₀.symm)))

end GlobalTheory.CompanionTheory.SmGL.Bernstein
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharactersStatement
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_induced_two_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional | exact GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional | (intros; apply GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedTwoCharactersNotScalar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedTwoCharactersNotScalar
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SplitFrob

section Proj

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem isCompl_toSubmodule {S S' : Subrepresentation π} (h : IsCompl S S') :
    IsCompl S.toSubmodule S'.toSubmodule := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf, disjoint_iff.mp h.1]
    try rfl
  · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup, codisjoint_iff.mp h.2]
    try rfl

def proj {S S' : Subrepresentation π} (h : IsCompl S S') : V →ₗ[ℂ] V :=
  S.toSubmodule.subtype ∘ₗ
    Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h)

theorem proj_left {S S' : Subrepresentation π} (h : IsCompl S S') {v : V} (hv : v ∈ S.toSubmodule) :
    proj h v = v := by
  show S.toSubmodule.subtype
    (Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h) v) = v
  simp only [Submodule.projectionOnto_apply_of_mem_left _ hv, Submodule.subtype_apply]

theorem proj_right {S S' : Subrepresentation π} (h : IsCompl S S') {v : V}
    (hv : v ∈ S'.toSubmodule) : proj h v = 0 := by
  show S.toSubmodule.subtype
    (Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h) v) = 0
  simp only [Submodule.projectionOnto_apply_of_mem_right _ hv, map_zero]

theorem proj_comm {S S' : Subrepresentation π} (h : IsCompl S S') (g : G) (v : V) :
    proj h (π g v) = π g (proj h v) := by
  have htop : S.toSubmodule ⊔ S'.toSubmodule = ⊤ := (isCompl_toSubmodule h).sup_eq_top
  have hv : v ∈ S.toSubmodule ⊔ S'.toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [map_add (f := _), proj_left h hx, proj_right h hy, proj_left h (S.apply_mem_toSubmodule g hx),
    proj_right h (S'.apply_mem_toSubmodule g hy), add_zero]

end Proj

section Induced

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {X : Type} [AddCommGroup X] [Module ℂ X]

def ev (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) : IndSp e ρ →ₗ[ℂ] X where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_unip (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) {u : GL n k}
    (hu : u ∈ unipRad k e) (f : IndSp e ρ) : ev e ρ (parInd e ρ u f) = ev e ρ f := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hu
  rw [MonoidHom.mem_ker] at hp
  have h := f.1.2 p 1
  rw [MonoidHom.comp_apply, hp, map_one, Module.End.one_apply, mul_one] at h
  show f.1.1 (1 * ((parab k e).subtype p)) = f.1.1 1
  rw [one_mul]
  exact h

theorem ev_levi (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) (g : Levi k m)
    (f : IndSp e ρ) :
    ev e ρ (parInd e ρ (leviEmb k e g) f) = (deltaHalf k m g : ℂ) • ρ g (ev e ρ f) := by
  have hmem := leviEmb_mem_parab k e g
  have h := f.1.2 ⟨leviEmb k e g, hmem⟩ 1
  rw [mul_one, MonoidHom.comp_apply, leviProj_leviEmb] at h
  show f.1.1 (1 * leviEmb k e g) = (deltaHalf k m g : ℂ) • ρ g (f.1.1 1)
  rw [one_mul]
  exact h

theorem exists_ev_ne (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) {f : IndSp e ρ}
    (hf : f ≠ 0) : ∃ g, ev e ρ (parInd e ρ g f) ≠ 0 := by
  by_contra hcon
  apply hf
  apply Subtype.ext
  apply Subtype.ext
  funext g
  by_contra hg
  exact hcon ⟨g, by
    change f.1.1 (1 * g) ≠ 0
    rw [one_mul]
    exact hg⟩

variable {e : (Σ a, m a) ≃ n} {ρ : Representation ℂ (Levi k m) X}

def lam {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') : IndSp e ρ →ₗ[ℂ] X :=
  ev e ρ ∘ₗ proj h

theorem lam_apply {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (f : IndSp e ρ) :
    lam h f = ev e ρ (proj h f) := rfl

theorem lam_twKer {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') :
    twKer (parInd e ρ) (unipRad k e) 1 ≤ LinearMap.ker (lam h) := by
  unfold GlobalTheory.PRep.twKer
  refine Submodule.span_le.mpr ?_
  rintro w ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul,
    lam_apply, lam_apply, proj_comm, ev_unip e ρ u.2, sub_self]

def frob {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') :
    (SmGL.jac e (parInd e ρ)).IntertwiningMap ρ where
  toLinearMap := (twKer (parInd e ρ) (unipRad k e) 1).liftQ (lam h) (lam_twKer h)
  isIntertwining' g := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show (twKer (parInd e ρ) (unipRad k e) 1).liftQ (lam h) (lam_twKer h)
        (SmGL.jac e (parInd e ρ) g (Submodule.Quotient.mk v)) = ρ g (lam h v)
    rw [jac_mk, ← Submodule.Quotient.mk_smul, Submodule.liftQ_apply, map_smul, lam_apply, proj_comm,
      ev_levi, lam_apply, smul_smul]
    simp

theorem frob_mk {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (v : IndSp e ρ) :
    (frob h).toLinearMap (Submodule.Quotient.mk v) = lam h v := rfl

theorem exists_lam_ne {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (hS : S ≠ ⊥) :
    ∃ v ∈ S.toSubmodule, lam h v ≠ 0 := by
  have hS0 : S.toSubmodule ≠ ⊥ := by
    intro h0
    apply hS
    apply Subrepresentation.ext
    rw [h0]
    try rfl
  obtain ⟨f, hfS, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨g, hg⟩ := exists_ev_ne e ρ hf0
  refine ⟨parInd e ρ g f, S.apply_mem_toSubmodule g hfS, ?_⟩
  rw [lam_apply, proj_left h (S.apply_mem_toSubmodule g hfS)]
  exact hg

theorem not_dichotomy {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (hS : S ≠ ⊥)
    (hS' : S' ≠ ⊥) :
    ¬ (∀ φ ψ : (SmGL.jac e (parInd e ρ)).IntertwiningMap ρ,
      φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro hd
  obtain ⟨v, hvS, hv⟩ := exists_lam_ne h hS
  obtain ⟨w, hwS', hw⟩ := exists_lam_ne h.symm hS'
  rcases hd (frob h) (frob h.symm) with h0 | ⟨c, hc⟩
  · apply hv
    rw [← frob_mk h v, h0, LinearMap.zero_apply]
  · have e1 : lam h.symm v = c • lam h v := by
      rw [← frob_mk h.symm v, hc, LinearMap.smul_apply, frob_mk]
    rw [lam_apply, proj_right h.symm hvS, map_zero] at e1
    rcases smul_eq_zero.mp e1.symm with hc0 | hc0
    · apply hw
      rw [← frob_mk h.symm w, hc, hc0, zero_smul, LinearMap.zero_apply]
    · exact hv hc0

end Induced

theorem not_dichotomy_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (W W' : Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))), IsCompl W W' → W ≠ ⊥ → W' ≠ ⊥ → ¬ (∀ φ ψ : (SmGL.jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ W W' h hW hW'
  exact not_dichotomy h hW hW'

end GlobalTheory.CompanionTheory.SplitFrob
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedTwoCharactersNotScalarStatement
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_two_characters_not_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (W W' : Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))), IsCompl W W' → W ≠ ⊥ → W' ≠ ⊥ → ¬ (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.SplitFrob.not_dichotomy_det | exact GlobalTheory.CompanionTheory.SplitFrob.not_dichotomy_det | (intros; apply GlobalTheory.CompanionTheory.SplitFrob.not_dichotomy_det <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitarisableDegenerateSeries
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenerateSeries

theorem isUnitarisable_degenerateSeries (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (_ : IsSmoothChar χ₁)
    (_ : IsSmoothChar χ₂) (h₁ : IsUnitaryChar χ₁) (h₂ : IsUnitaryChar χ₂) :
    IsUnitarisable (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  apply GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₁ _
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₂ _

end GlobalTheory.CompanionTheory.DegenerateSeries
end
end

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem prod₂_detRep_isIrreducible :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      JacquetOfInducedFiltration k) →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ →
      IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) →
      (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible := by
  intro hJ k _ _ _ _ a b χ₁ χ₂ s₁ s₂ u₁ u₂ hne
  haveI := GlobalTheory.CompanionTheory.DegPrinSeries.nontrivial_subrepresentation k a b χ₁ χ₂ s₁ s₂
  show IsSimpleOrder (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b)))
    ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)))
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hc⟩ := GlobalTheory.T.admissible_unitary_semisimple _ (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k (a + b))
    (GlobalTheory.CompanionTheory.DegenSeries.isAdmissible_degenerate k a b χ₁ χ₂ s₁ s₂)
    (GlobalTheory.CompanionTheory.DegenerateSeries.isUnitarisable_degenerateSeries k a b χ₁ χ₂ s₁ s₂ u₁ u₂) W
  by_contra h
  push_neg at h
  have hW' : W' ≠ ⊥ := by
    rintro rfl
    exact h.2 (eq_top_of_isCompl_bot hc)
  exact GlobalTheory.T.induced_two_characters_not_scalar k a b χ₁ χ₂ W W' hc h.1 hW'
    (GlobalTheory.T.jacquet_induced_two_characters k a b χ₁ χ₂ (hJ k) s₁ s₂ u₁ u₂ hne)

end GlobalTheory.CompanionTheory.SmGL.Bernstein
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace PositivityTheory.BernsteinRamification

def NarrowBern : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible

theorem narrowBern (hG : GlobalTheory.Published.GeometricLemmaFiltration) : NarrowBern :=
  GlobalTheory.CompanionTheory.SmGL.Bernstein.prod₂_detRep_isIrreducible hG

theorem kCoinv_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) (hD : PositivityTheory.KCo.DictSt) : GlobalTheory.ThK.KCoinv :=
  GlobalTheory.CompanionTheory.KCoNarrow.kCoinv_of_narrow (narrowBern hG) hD

theorem soCoinv_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) (hK : GlobalTheory.ThK.KFin) : PositivityTheory.ThKF.SoCoinv :=
  GlobalTheory.CompanionTheory.SoCoinvNarrow.soCoinv_of_narrow (narrowBern hG) hK

theorem ramifiedMultiplicityOne_of_geometricFiltration (hG : GlobalTheory.Published.GeometricLemmaFiltration) : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne :=
  GlobalTheory.CompanionTheory.BernNarrow.first_cohomology_ramified_narrow (narrowBern hG)

theorem finRam_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) : PositivityTheory.ThK.FinRam :=
  GlobalTheory.CompanionTheory.SplitNarrow.finRam_of_narrow (narrowBern hG)

theorem finSplit_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) : PositivityTheory.ThK.FinSplit :=
  GlobalTheory.CompanionTheory.BernBridge.Split.finSplit_of_narrow (narrowBern hG)

end PositivityTheory.BernsteinRamification
