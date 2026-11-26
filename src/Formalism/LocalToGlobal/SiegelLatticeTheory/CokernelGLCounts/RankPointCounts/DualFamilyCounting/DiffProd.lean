module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Assemble
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def VolOrdV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, ¬ TypAt X v →
    localVolumeUnit X ψ v / ZZX X u u' ψ v =
      absV v (dV v) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3))

def VolTypV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → ∀ v : PlX X, TypAt X v → localVolumeUnit X ψ v / ZZX X u u' ψ v = (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))

def OmV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X,
    (omAt X.B.I.cm.sig X.B.I.J ψ v ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
        Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal =
      absV v (dV v) ^ ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2) *
        aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u')

def CondAll : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    IsStdChar ψ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x : Fv F v),
      (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔ dV v * x ∈ v.adicCompletionIntegers F

def DiffProd : Prop :=
  HasProd (fun v : PlX X => absV v (dV v)) (|(NumberField.discr X.B.I.F : ℝ)|⁻¹)

end Loc

end Formalism.L2.SG.Pf.NcVal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocalOfFam
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LeDualFOfGram
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem isLattice_span {ι' : Type} [Finite ι'] (β : ι' → V)
    (hβ : Submodule.span K (Set.range β) = ⊤) :
    Submodule.IsFullLattice K (Submodule.span (𝓞 K) (Set.range β)) := by
  let : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range β)) :=
    Submodule.IsLattice.of_fg K (Submodule.fg_span (Set.finite_range β))
  exact { span_eq_top := (Submodule.span_span_of_tower (𝓞 K) K (Set.range β)).trans hβ }

def rdualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (y : V) : Submodule (𝓞 K) V :=
  (locF 𝔭 (1 : Submodule (𝓞 K) K)).comap ((h y).restrictScalars (𝓞 K))

def ldualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (x : V) : Submodule (𝓞 K) V where
  carrier := {y | h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add (f := _), LinearMap.add_apply] at *
    exact Submodule.add_mem _ ha hb
  smul_mem' := by
    intro c z hz
    simp only [Set.mem_ofPred_eq] at *
    obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
    rw [← algebraMap_smul K c z, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      ← hr, ← smul_eq_mul, algebraMap_smul]
    exact Submodule.smul_mem _ r hz

theorem le_dualF_of_gram (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {𝔭 : Ideal (𝓞 F)}
    (hp : 𝔭.IsPrime) {ι' : Type} (β : ι' → V)
    (hβ : ∀ i j, h (β i) (β j) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    locF 𝔭 (Submodule.span (𝓞 K) (Set.range β)) ≤
      dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range β))) := by
  have key : ∀ y ∈ Submodule.span (𝓞 K) (Set.range β), ∀ x ∈ Submodule.span (𝓞 K) (Set.range β),
      h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro y hy x hx
    have hx' : Submodule.span (𝓞 K) (Set.range β) ≤ rdualF h 𝔭 y := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hy' : Submodule.span (𝓞 K) (Set.range β) ≤ ldualF h 𝔭 (β j) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hβ i j
      exact hy' hy
    exact hx' hx
  intro x hx
  show ∀ y ∈ _, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp _ x).1 hx
  obtain ⟨s, hs, hsy⟩ := (LocF.mem_locF_iff hp _ y).1 hy
  have := key _ hsy _ htx
  rw [localizedQuotients.form_smul hF] at this
  obtain ⟨u, hu, hux⟩ := (LocF.mem_locF_iff hp _ _).1 this
  refine (LocF.mem_locF_iff hp _ _).2 ⟨u * (s * t), fun hm => ?_, ?_⟩
  · rcases hp.mem_or_mem hm with h1 | h1
    · exact hu h1
    · exact (hp.mem_or_mem h1).elim hs ht
  · rw [Algebra.smul_def] at hux ⊢
    rw [map_mul, map_mul] at hux ⊢
    simpa [mul_assoc, mul_comm, mul_left_comm] using hux

end Formalism.L2.SG.Pf.GluingBases
end
end

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def glueFam (K : Type) {F V : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup V] [Module K V]
    (𝔭 : Ideal (𝓞 F)) {n m : ℕ} (b : Fin n → V) (a : Fin n → 𝓞 F) (π : 𝓞 F) (w : Fin m → V)
    (τ : Fin n → Fin m) : Fin n ⊕ Fin m → V :=
  Sum.elim (fun i => if vF 𝔭 (a i) = 0 then b i else
    ((algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i)) • (b i + w (τ i))) w

def FamTop : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) = ⊤

def FamGram : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      ∀ i j, h (glueFam K 𝔭 b a π w τ i) (glueFam K 𝔭 b a π w τ j) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)

def FamDual : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ)))) ≤
        locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ)))

def FamMeet : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ))) ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M

theorem glueAssemble_of (h0 : FamTop) (h1 : FamGram) (h2 : FamDual) (h3 : FamMeet) :
    GlueAssemble := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  refine ⟨locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ))),
    ⟨_, (isLattice_span _ (h0 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg)).toIsLattice, rfl⟩,
    le_antisymm (h2 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg)
      (le_dualF_of_gram hF h h𝔭.isPrime _ (h1 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg)),
    h3 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg⟩

theorem glueLocal_of_fam (hJ : JordanExists) (hV : GlueVecs) (h0 : FamTop) (h1 : FamGram)
    (h2 : FamDual) (h3 : FamMeet) : Formalism.L2.SG.Pf.G7.GlueLocal :=
  glueLocal_of_of hJ hV (glueAssemble_of h0 h1 h2 h3)

end Formalism.L2.SG.Pf.GluingBases
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsGlueDataPre
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def IsGlueDataPre {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) {n m : ℕ} (a : Fin n → 𝓞 F)
    (π : 𝓞 F) (w : Fin m → V) (c : Fin m → F) (τ : Fin n → Fin m) : Prop :=
  (∀ j, w j ∈ orthK h U) ∧ (∀ j k, j ≠ k → h (w j) (w k) = 0) ∧
  (∀ j, h (w j) (w j) = algebraMap F K (c j) ∧ c j ≠ 0) ∧
  (∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) ∧
  (∃ s₀ : 𝓞 F, IsUnif0 𝔭 π s₀) ∧
  (∀ i, vF 𝔭 (a i) ≠ 0 →
    InP 𝔭 (2 * vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i)))) ∧
  (∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m) ∧
  (∀ j : Fin m, (j : ℕ) + 1 < m → (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) →
    InP 𝔭 0 (algebraMap F K (c j)) ∧ InP 𝔭 0 (algebraMap F K (c j)⁻¹))

def GlueVecsPre : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
      ∃ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
        (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueDataPre h U 𝔭 a π w c τ

def LastRescale : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueDataPre h U 𝔭 a π w c τ →
      ∃ (w' : Fin (finrank K (orthK h U)) → V) (c' : Fin (finrank K (orthK h U)) → F),
        IsGlueData h U 𝔭 a π w' c' τ

theorem glueVecs_of (h1 : GlueVecsPre) (h2 : LastRescale) : GlueVecs := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  obtain ⟨π, w, c, τ, hg⟩ := h1 K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  obtain ⟨w', c', hg'⟩ := h2 K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg
  exact ⟨π, w', c', τ, hg'⟩

end Formalism.L2.SG.Pf.GluingBases
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittOEv
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Matrix Formalism.L2.SG.Pf.NcS.KfOrbPf
open scoped TensorProduct

section OEvRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem oev_inclR (o : 𝓞 E) : inclR (F := F) (Fv F v) (o : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨o, trivial, rfl⟩

theorem oev_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have h := oev_inclR (F := F) (E := E) v 1
  simpa using h

theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  unfold OEv at hx hy ⊢
  rw [SetLike.mem_coe] at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, -, rfl⟩ := hb
      exact Submodule.subset_span ⟨a * b, trivial, by simp [map_mul]⟩
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      show _ * ((c : Fv F v) • y) ∈ _
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c h
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    show ((c : Fv F v) • x) * y ∈ _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c h

theorem sigR_smul' (σ : E →ₐ[F] E) (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, TensorProduct.smul_tmul']
  | add x y h1 h2 => rw [smul_add, map_add (f := _), h1, h2, map_add (f := _), smul_add]

theorem oev_sigR (σ : E →ₐ[F] E) {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  unfold OEv at hx ⊢
  rw [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    refine Submodule.subset_span
      ⟨⟨σ a, map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)⟩, trivial, ?_⟩
    simp [sigR, inclR]
    rfl
  | zero => simp
  | add x y _ _ h1 h2 => rw [map_add (f := _)]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    show sigR (Fv F v) σ ((c : Fv F v) • x) ∈ _
    rw [sigR_smul']
    exact Submodule.smul_mem _ c h

def oevRing : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := oev_mul v
  one_mem' := oev_one v
  add_mem' := fun hx hy => Submodule.add_mem _ hx hy
  zero_mem' := Submodule.zero_mem _
  neg_mem' := fun hx => Submodule.neg_mem _ hx

theorem mem_std_of_oev {n : ℕ} (y : Fin n → Fv F v ⊗[F] E) (hy : ∀ i, y i ∈ OEv (E := E) v) :
    y ∈ latLoc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  have hsingle : ∀ (i : Fin n) (z : Fv F v ⊗[F] E), z ∈ OEv (E := E) v → Pi.single i z ∈ latLoc (E := E) v
      ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
    intro i z hz
    change z ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨o, -, rfl⟩ := hw
      refine Submodule.subset_span ⟨Pi.single i (o : E), ?_, ?_⟩
      · rw [SetLike.mem_coe, MassDataMassesW.KCptW.stdSub, Submodule.mem_pi]
        intro k _
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · funext k
        by_cases hk : k = i
        · subst hk; simp [ratV]
        · simp [ratV, hk]
    | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
    | add w w' _ _ h1 h2 => rw [Pi.single_add]; exact Submodule.add_mem _ h1 h2
    | smul c w _ h =>
      have : (Pi.single i (c • w) : Fin n → Fv F v ⊗[F] E) = c • (Pi.single i w : Fin n → Fv F v ⊗[F] E) := by
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      rw [this]
      exact Submodule.smul_mem _ c h
  rw [← Finset.univ_sum_single y]
  exact Submodule.sum_mem _ fun i _ => hsingle i (y i) (hy i)

theorem ev_oev (x : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, inclR (F := F) (Fv F v) x ∈ OEv (E := E) v := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsIntegral.isIntegral x).isAlgebraic
  obtain ⟨N, hN0, hNx⟩ := halg.exists_integral_multiple
  let o : 𝓞 E := ⟨N • x, hNx⟩
  filter_upwards [ev_int (F := F) ((N : F)⁻¹)] with v hv
  have e : inclR (F := F) (Fv F v) x =
      (⟨algebraMap F (Fv F v) ((N : F)⁻¹), hv⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E) := by
    show _ = algebraMap F (Fv F v) ((N : F)⁻¹) • inclR (F := F) (Fv F v) (N • x)
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, map_zsmul, zsmul_eq_mul, ← mul_assoc, ← map_intCast (algebraMap F (Fv F v ⊗[F] E)), ← map_mul,
      inv_mul_cancel₀ (Int.cast_ne_zero.2 hN0), map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (oev_inclR v o)

theorem oev_smul' {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {z : Fv F v ⊗[F] E}
    (hz : z ∈ OEv (E := E) v) : r • z ∈ OEv (E := E) v :=
  Submodule.smul_mem _ (⟨r, hr⟩ : v.adicCompletionIntegers F) hz

end OEvRing

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RieszHermitianHolds
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def SummandLoc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    ∀ X : Submodule K V, ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ Λ : Submodule (𝓞 K) V,
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      ∃ π : V →ₗ[K] V, (∀ v, π v ∈ X) ∧ (∀ x ∈ X, π x = x) ∧ ∀ y ∈ Λ, π y ∈ Λ

def RieszH : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ f : V →ₗ[K] K, ∃ x : V, ∀ y, h x y = f y

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem coe_algebraMap_OF (t : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 K) t : 𝓞 K) : K) = algebraMap F K (t : F) := by
  change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]

theorem form_mem_locF_of (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) {v y : V}
    (hv : v ∈ locF 𝔭 (dualIn h X L)) (hy : y ∈ locF 𝔭 L) : h y v ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have := h𝔭
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 L y).1 hy
  obtain ⟨u, hu, huv⟩ := (LocalSpans.mem_locF 𝔭 _ v).1 hv
  have H := (mem_dual_iff.1 huv.2) _ hty
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨t * u, fun hm => (h𝔭.mem_or_mem hm).elim ht hu, ?_⟩
  have hst : starRingEnd K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) := by
    have e := coe_algebraMap_OF (K := K) t
    change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _ at e
    rw [e, starRingEnd_apply]
    exact (hF _).2 ⟨_, rfl⟩
  rw [form_ozmul_right, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, hst, algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) (h y v)] at H
  rw [map_mul, mul_smul, smul_comm]
  exact H

theorem riesz_hermitian_holds : RieszH := by
  intro K V _ _ _ _ _ h _ hnd f
  classical
  let b := Module.finBasis K V
  let Φ : (Fin (finrank K V) → K) →ₗ[K] Module.Dual K V :=
    { toFun := fun c => ∑ i, c i • h (b i)
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have hΦ : ∀ c, h (∑ i, star (c i) • b i) = Φ c := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Φ, map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have hx : (∑ i, star (c i) • b i) = 0 := by
      apply hnd
      intro y
      rw [hΦ, hc]
      rfl
    funext i
    have := Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => star (c i)) hx i
    simpa using this
  have hsurj : Function.Surjective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_fin_fun, Subspace.dual_finrank_eq]
  obtain ⟨c, hc⟩ := hsurj f
  exact ⟨∑ i, star (c i) • b i, fun y => by rw [hΦ, hc]⟩

theorem mem_of_smul_mem {X : Submodule K V} {𝔭 : Ideal (𝓞 F)} {u : 𝓞 F} (hu : u ∉ 𝔭) {v : V}
    (hv : algebraMap (𝓞 F) (𝓞 K) u • v ∈ X) : v ∈ X := by
  have hu0 : (u : F) ≠ 0 := by
    intro e
    apply hu
    have : u = 0 := RingOfIntegers.ext (by simpa using e)
    rw [this]
    exact 𝔭.zero_mem
  have hc0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) ≠ 0 := by
    have e := coe_algebraMap_OF (K := K) u
    change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) = _ at e
    rw [e]
    exact (map_ne_zero _).2 hu0
  have h1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) • v ∈ X := by
    rw [algebraMap_smul]
    exact hv
  have := X.smul_mem (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u))⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

theorem projOnto_of (hS : SummandLoc) (hR : RieszH) : ProjOnto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd X Y hc hXY L hL 𝔭 h𝔭 Λ hΛ0 hΛd hΛX v hv
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨π, hπX, hπid, hπΛ⟩ := hS K F V X 𝔭 h𝔭 Λ hΛ0
  obtain ⟨x, hx⟩ := hR K V h hs hnd ((h v).comp π)
  have key : ∀ y, h y x = h (π y) v := by
    intro y
    rw [← hs.eq x y, hx y, LinearMap.comp_apply, hs.eq v (π y)]
  have hvX : v ∈ X := by
    obtain ⟨u, hu, huv⟩ := (LocalSpans.mem_locF 𝔭 _ v).1 hv
    exact mem_of_smul_mem hu huv.1
  have hxΛ : x ∈ Λ := by
    rw [← hΛd]
    show ∀ y ∈ Λ, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
    intro y hy
    rw [key]
    have : π y ∈ locF 𝔭 L := by
      rw [← hΛX]
      exact ⟨hπΛ y hy, hπX y⟩
    exact form_mem_locF_of hF hp hv this
  refine ⟨x, hxΛ, ?_⟩
  set w := X.projection Y hc x - v with hw
  have hwX : w ∈ X := X.sub_mem (Submodule.projection_apply_mem hc x) hvX
  have hw0 : w = 0 := by
    apply hnd
    intro z
    have ez := Submodule.projection_add_projection_eq_self hc z
    rw [← ez, map_add (f := _)]
    have h1 : h w (Y.projection X hc.symm z) = 0 := hXY w hwX _ (Submodule.projection_apply_mem _ z)
    have hzX : X.projection Y hc z ∈ X := Submodule.projection_apply_mem hc z
    have ex := Submodule.projection_add_projection_eq_self hc x
    have e3 : h (X.projection Y hc z) (X.projection Y hc x) = h (X.projection Y hc z) x := by
      conv_rhs => rw [← ex]
      rw [map_add (f := _), hXY _ hzX _ (Submodule.projection_apply_mem _ x), add_zero]
    have h2 : h (X.projection Y hc z) w = 0 := by
      rw [hw, map_sub, e3, key, hπid _ hzX, sub_self]
    rw [h1, add_zero, ← hs.eq (X.projection Y hc z) w, h2, map_zero]
  exact sub_eq_zero.mp hw0

end Formalism.L2.SG.Pf.G6
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanSSelf
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem unit_ne {a : K} {k : ℕ} (hu : IsUnitIn S (a * (π ^ k)⁻¹)) : a ≠ 0 := by
  intro ha
  apply hu.1
  rw [ha, zero_mul]

private theorem mem_iff_lemma {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i := Iff.rfl

theorem spanS_empty {ι : Type} [Fintype ι] [IsEmpty ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ v = 0 := by
  rw [mem_iff_lemma]
  constructor
  · rintro ⟨c, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨0, fun _ => S.zero_mem, by simp⟩

theorem mem_spanS_self {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → V) (i : ι) :
    b i ∈ spanS S b := by
  refine (mem_iff_lemma b (b i)).2 ⟨fun j => if j = i then 1 else 0, fun j => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · simp [ite_smul]

theorem core_empty {ι : Type} [Fintype ι] [IsEmpty ι] (b b' : ι → V) {φ : V ≃ₗ[K] V}
    (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ Submodule.span K (Set.range b), h w v = 0) → g v = φ v) ∧
      ∀ v, v ∈ spanS S b ↔ g v ∈ spanS S b' := by
  refine ⟨φ, hφ, fun v _ => rfl, fun v => ?_⟩
  rw [spanS_empty b v, spanS_empty b' (φ v)]
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    apply φ.injective
    rw [h0, map_zero]

private theorem span_ne_eq_cutW_of_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι] {f : ι → V}
    (ho : ∀ i j, i ≠ j → h (f i) (f j) = 0) {i₀ : ι} (hf0 : h (f i₀) (f i₀) ≠ 0) :
    Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => f i)) =
      cutW h (Submodule.span K (Set.range f)) (f i₀) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show f i ∈ Submodule.span K (Set.range f) ⊓ LinearMap.ker (h (f i₀))
    exact Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨i, rfl⟩,
      LinearMap.mem_ker.2 (ho i₀ i (Ne.symm i.2))⟩
  · intro v hv
    have hv' : v ∈ Submodule.span K (Set.range f) ⊓ LinearMap.ker (h (f i₀)) := hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv'
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv1
    have ha0 : a i₀ = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.mem_ker, map_sum, Finset.sum_eq_single i₀] at hv2
      · rw [map_smul, smul_eq_mul] at hv2
        exact (mul_eq_zero.1 hv2).resolve_right hf0
      · intro i _ hi
        rw [map_smul, ho i₀ i (Ne.symm hi), smul_zero]
      · intro h'
        exact absurd (Finset.mem_univ i₀) h'
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, ha0, zero_smul, zero_add]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem mem_spanS_iff_smul_add_mem_spanS_ne {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → V) (i₀ : ι)
    (v : V) : v ∈ spanS S f ↔
      ∃ a ∈ S, ∃ w ∈ spanS S (fun i : {i // i ≠ i₀} => f i), v = a • f i₀ + w := by
  rw [mem_iff_lemma]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c i₀, hc i₀, ∑ i : {i // i ≠ i₀}, c i • f i,
      (mem_iff_lemma _ _).2 ⟨fun i => c i, fun i => hc i, rfl⟩, ?_⟩
    exact Fintype.sum_eq_add_sum_subtype_ne _ i₀
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [mem_iff_lemma] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    refine ⟨fun i => if hi : i = i₀ then a else d ⟨i, hi⟩, fun i => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact ha
      · exact hd _
    · rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
      dsimp only
      rw [dite_eq_left rfl]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dite_eq_right i.2]

theorem core_of_split (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hsp : SplitAt S π h) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ n →
    ∀ (b b' : ι → V) (e : ι → ℕ) (φ : V ≃ₗ[K] V),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i j, i ≠ j → h (b' i) (b' j) = 0) →
    (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, IsUnitIn S (h (b' i) (b' i) * (π ^ e i)⁻¹)) → φ ∈ Formalism.HermitianLatticesTheory.isom h →
    (∀ v, v ∈ Submodule.span K (Set.range b) ↔ φ v ∈ Submodule.span K (Set.range b')) →
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ Submodule.span K (Set.range b), h w v = 0) → g v = φ v) ∧
      ∀ v, v ∈ spanS S b ↔ g v ∈ spanS S b' := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ hcard b b' e φ _ _ _ _ hφ _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (Nat.le_zero.1 hcard)
    exact core_empty b b' hφ
  | succ n ih =>
    intro ι _ _ hcard b b' e φ ho ho' hu hu' hφ hW
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact core_empty b b' hφ
    obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
    have hb0 : b i₀ ∈ Submodule.span K (Set.range b) := Submodule.subset_span ⟨i₀, rfl⟩
    have hξ : φ (b i₀) ∈ Submodule.span K (Set.range b') := (hW _).1 hb0
    have hφn : h (φ (b i₀)) (φ (b i₀)) = h (b i₀) (b i₀) := hφ (b i₀) (b i₀)
    obtain ⟨c, hoc, huc, hcc, hspc, hiffc⟩ := hsp ι b' e i₀ ho' hu'
      (fun i => hmin i (Finset.mem_univ i)) (φ (b i₀)) hξ (by rw [hφn]; exact hu i₀)
    have hWc : ∀ v, v ∈ Submodule.span K (Set.range b) ↔
        φ v ∈ Submodule.span K (Set.range c) := by
      intro v
      rw [hspc]
      exact hW v
    obtain ⟨φ', hφ', hφ'0, hcut, hagree⟩ := exists_prep hs hd hφ hWc hb0
      (Submodule.subset_span ⟨i₀, rfl⟩) (by rw [hcc, hφn])
    have hA : h (b i₀) (b i₀) ≠ 0 := unit_ne (hu i₀)
    have hC : h (c i₀) (c i₀) ≠ 0 := unit_ne (huc i₀)
    have hcardS : Fintype.card {i // i ≠ i₀} ≤ n := by
      have := Fintype.card_subtype_lt (p := fun i => i ≠ i₀) (x := i₀) (by simp)
      omega
    have hWbb : ∀ v, v ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)) ↔
        φ' v ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => c i)) := by
      intro v
      rw [span_ne_eq_cutW_of_orthogonal ho hA, span_ne_eq_cutW_of_orthogonal hoc hC]
      exact hcut v
    obtain ⟨g, hg, hgagree, hgiff⟩ := ih {i // i ≠ i₀} hcardS (fun i => b i) (fun i => c i)
      (fun i => e i) φ' (fun i j hij => ho i j (fun h' => hij (Subtype.ext h')))
      (fun i j hij => hoc i j (fun h' => hij (Subtype.ext h'))) (fun i => hu i) (fun i => huc i)
      hφ' hWbb
    have hperp : ∀ w ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)),
        h w (b i₀) = 0 := by
      intro w hw
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun i _ => by
        rw [map_smulₛₗ, LinearMap.smul_apply, ho i i₀ i.2, smul_zero]
    have hg0 : g (b i₀) = c i₀ := by rw [hgagree _ hperp, hφ'0]
    refine ⟨g, hg, fun v hv => ?_, fun v => ?_⟩
    · have hv' : ∀ w ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)), h w v = 0 :=
        fun w hw => hv w (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩) hw)
      rw [hgagree v hv', hagree v hv]
    · rw [← hiffc, mem_spanS_iff_smul_add_mem_spanS_ne b i₀, mem_spanS_iff_smul_add_mem_spanS_ne c i₀]
      constructor
      · rintro ⟨a, ha, w, hw, rfl⟩
        refine ⟨a, ha, g w, (hgiff w).1 hw, ?_⟩
        rw [map_add (f := _), map_smul, hg0]
      · rintro ⟨a, ha, u, hu2, huv⟩
        refine ⟨a, ha, g.symm u, (hgiff _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hu2), ?_⟩
        apply g.injective
        rw [huv, map_add (f := _), map_smul, hg0, LinearEquiv.apply_symm_apply]

end

end Formalism.L2.SG.Pf.G3
end
end
