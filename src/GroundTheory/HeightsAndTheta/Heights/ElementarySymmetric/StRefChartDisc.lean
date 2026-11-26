module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StNbarLeviChartReg
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StRefChartDisc
section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StProjChartHolo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart)

def ProjChartHolo.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)), IsCompatChart M.atlas e →
    ∀ γ : ℂ → (Σ k, ι k) → ℂ, AnalyticAt ℂ γ 0 → (∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ mcPts (mCoordIdeal D.y)) →
      M.proj (γ 0) ∈ e.source → AnalyticAt ℂ (fun s => e (M.proj (γ s))) 0

end GroundTheory.Heights₂.Heights.NineStatements
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology

def RefChartDisc.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (S : LogLogRegularisationSetting M D.Xo (muLine H)) (k : Fin S.R.N) (γ : ℂ → (Σ k, ι k) → ℂ), AnalyticAt ℂ γ 0 →
    (∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ mcPts (mCoordIdeal D.y)) → M.proj (γ 0) ∈ (S.R.chart k).source →
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∀ᶠ s in 𝓝 (0 : ℂ),
        Real.log (S.ref.h (γ s)) = S.R.q k (S.R.chart k (M.proj (γ s))) - (G s).re

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFlZArithVar
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FlZArithVar

section Rename

variable {K : Type} [Fintype K] {ι ι' : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]


omit [Fintype K] in
theorem isMultiHomog_rename_sigma (e : ∀ k, ι k ≃ ι' k) {g : MRing ι} {a : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (Equiv.sigmaCongrRight e) g : MRing ι') a := by
  classical
  intro m hm k
  rw [support_rename_of_injective (Equiv.sigmaCongrRight e).injective, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  have h1 : ∀ i : ι' k, Finsupp.mapDomain (Equiv.sigmaCongrRight e) m0 ⟨k, i⟩ = m0 ⟨k, (e k).symm i⟩ := by
    intro i
    have : (⟨k, i⟩ : Σ k, ι' k) = Equiv.sigmaCongrRight e ⟨k, (e k).symm i⟩ := by simp
    rw [this, Finsupp.mapDomain_apply_of_injective (Equiv.sigmaCongrRight e).injective]
  simp only [h1]
  rw [Equiv.sum_comp (e k).symm (fun j => m0 ⟨k, j⟩)]
  exact hg m0 hm0 k

theorem isArithVar_comap_rename_sigma (e : ∀ k, ι k ≃ ι' k) {P : Ideal (MRing ι')} {d : ℕ}
    (hP : IsArithVar P d) :
    IsArithVar (P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι')) d := by
  obtain ⟨hne, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  let E : MRing ι ≃+* MRing ι' := (renameEquiv ℤ (Equiv.sigmaCongrRight e)).toRingEquiv
  have hQ : P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι') = P.map E.symm := by
    rw [Ideal.map_symm]
    rfl
  have hEs : ∀ g, E.symm g = rename (Equiv.sigmaCongrRight fun k => (e k).symm) g := by
    intro g
    show (renameEquiv ℤ (Equiv.sigmaCongrRight e)).symm g = _
    rw [renameEquiv_symm, Equiv.sigmaCongrRight_symm]
    rfl
  refine ⟨hne, ⟨?_, ⟨E.symm '' S, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact Ideal.comap_isPrime _ _
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hS g hg
    exact ⟨a, by rw [hEs]; exact isMultiHomog_rename_sigma (fun k => (e k).symm) ha⟩
  · rw [hQ, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨(e k).symm i, fun hj => hi ?_⟩
    rw [Ideal.mem_comap] at hj
    simpa using hj
  · have h : Ideal.comap (C : ℤ →+* MRing ι)
        (P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι')) =
        Ideal.comap (C : ℤ →+* MRing ι') P := by
      ext x
      simp only [Ideal.mem_comap, rename_C]
    unfold IsHorizontal
    rw [h]
    exact hhor
  · rw [← hdim]
    refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ P E ?_)
    show P = Ideal.map (E : MRing ι →+* MRing ι') (Ideal.comap (E : MRing ι →+* MRing ι') P)
    exact (Ideal.map_comap_of_surjective (E : MRing ι →+* MRing ι') E.surjective P).symm

end Rename

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)



end FlZArithVar

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
