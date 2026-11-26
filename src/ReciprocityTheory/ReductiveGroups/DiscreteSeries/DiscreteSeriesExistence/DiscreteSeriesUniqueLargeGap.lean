module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AllSmoothOfKType
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigCas
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_casOnSmooth (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : CasOnSmooth ε lam (sigLam ε Ψ v₀) :=
  casOnSmooth_of_isDS (isDS_sigLam hgap hP hv₀) hgap

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigKfin
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothRestrict
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isSmoothVecU_restrict {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (hSG : ∀ g ∈ UJset ε, ∀ x ∈ S, σ g x ∈ S) (x : S) :
    IsSmoothVecU ε (fun g => (S.orthogonalProjectionOnto ∘L σ g ∘L S.subtypeL : S →L[ℂ] S)) x ↔
      IsSmoothVecU ε σ (x : H) := by
  set P := S.orthogonalProjectionOnto
  have hP : ∀ w : H, w ∈ S → ((P w : S) : H) = w := by
    intro w hw
    have e : P w = ⟨w, hw⟩ := by
      first
        | exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨w, hw⟩ : S)
        | exact Submodule.orthogonalProjection_mem_subspace_eq_self (⟨w, hw⟩ : S)
        | exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := S) ⟨w, hw⟩ : _)
        | (show P ((⟨w, hw⟩ : S) : H) = ⟨w, hw⟩; simp [P])
    rw [e]
  constructor
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hFe⟩ := h g₀ hg₀
    refine ⟨U, fun g => ((F g : S) : H), hU, hg₀U, (S.subtypeL.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hg
    have e1 := hFe g hgU hg
    have hmem : σ g (x : H) ∈ S := hSG g hg x x.2
    dsimp only at e1 ⊢
    rw [← e1]
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact (hP _ hmem).symm
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hFe⟩ := h g₀ hg₀
    refine ⟨U, fun g => P (F g), hU, hg₀U, (P.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hg
    have e1 := hFe g hgU hg
    dsimp only at e1 ⊢
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [e1]

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_kfin_smooth (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (x : Hlam ε Ψ v₀) (hx : x ∈ kfinLam ε Ψ v₀) :
    IsSmoothVecU ε (sigLam ε Ψ v₀) x := by

  obtain ⟨w, -, hw⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hx)
  have hsm : IsSmoothVecU ε (rreg ε) ((x : Hlam ε Ψ v₀) : L2 ε) := by
    have hw' : (w : L2 ε) = (x : L2 ε) := hw
    rw [← hw']
    exact (mem_smD_iff ε (rreg ε) _).mp w.2

  exact (isSmoothVecU_restrict (rreg_isURepOn ε) (Hlam ε Ψ v₀)
    (rreg_mem_Hlam hgap hP hv₀) x).mpr hsm

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

theorem stdGap_of_mir {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hlam : Formalism.QuantumDeterminants.IsHCParam lam)
    (hh : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hlt : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) : StdGap ε lam := ⟨hlam.1, h, hh, hlt⟩

theorem all_smooth_of_kType {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    {σ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hDS : Formalism.MainNotions.S.IsDS ε lam σ)
    (hK : ∀ k : S7.KG ε, σ (S7.toMK k) = T.op k) (v : T.V) : IsSmoothVecU ε σ v := by
  obtain ⟨-, -, hσ, hirr, -, ⟨S, hS⟩, -⟩ := hDS
  have hinv : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ w ∈ smD ε σ, σ g w ∈ smD ε σ := by
    intro g hg w hw
    rw [mem_smD_iff] at hw ⊢
    unfold IsSmoothVecU at hw ⊢
    let _ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
    let _ : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
    intro g₀ hg₀
    obtain ⟨U, F, hU, hmem, hF, hEq⟩ := hw (g₀ * g) (pdA_inUJ_mul hg₀ hg)
    let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)
    have hL : ∀ x, L x = x * g := fun x => rfl
    refine ⟨L ⁻¹' U, F ∘ L, hU.preimage L.continuous, by simpa [hL] using hmem,
      hF.comp L.contDiff.contDiffOn (fun x hx => hx), ?_⟩
    intro x hx hxUJ
    have hx' : x * g ∈ U := by simpa [hL] using hx
    have hrep := hσ.1.2 x hxUJ g hg
    simp only [Function.comp_apply, hL]
    rw [← hEq (x * g) hx' (pdA_inUJ_mul hxUJ hg)]
    show σ x (σ g w) = σ (x * g) w
    rw [hrep]
    rfl
  have hne : smD ε σ ≠ ⊥ := by
    obtain ⟨V, -, hV0, -⟩ := exists_datum_of_isKTypeOf hσ hS
    intro hbot
    apply hV0
    have : Subsingleton (smD ε σ) := by
      rw [hbot]
      infer_instance
    exact Subsingleton.elim _ _
  have hcl : IsClosed ((smD ε σ : Submodule ℂ T.V) : Set T.V) := Submodule.closed_of_finiteDimensional _
  rcases hirr (smD ε σ) hcl hinv with h | h
  · exact absurd h hne
  · have hv : v ∈ smD ε σ := by
      rw [h]
      exact Submodule.mem_top
    exact (mem_smD_iff ε σ v).mp hv

theorem dsExistsG (hS7 : ∀ m : ℕ, S7.PsiExistsStatement m) :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
          (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) < h →
        ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
          (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
          Formalism.MainNotions.S.IsDS ε lam σ ∧ CasOnSmooth ε lam σ ∧
          (∀ S S' : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S →
            Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S') ∧
          (∀ μ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} :
            Submodule ℂ H)) ∧
          (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε σ S →
            ∀ v ∈ S, IsSmoothVecU ε σ v) := by
  intro n ε lam hlam h hh hmax
  have h1 : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h := lt_of_le_of_lt (le_max_left _ _) hmax
  have h2 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) < h :=
    lt_of_le_of_lt (le_max_right _ _) hmax
  have hgap : StdGap ε lam := stdGap_of_mir hlam hh h1
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  rcases Nat.eq_zero_or_pos (S7.q0 ε) with hq | hq
  · have hm : min (pOf ε) (qOf ε) = 0 := hq
    have hpq : pOf ε = 0 ∨ qOf ε = 0 := by omega
    obtain ⟨σ, hDS, hcas, hK⟩ := isDS_compact hpq hlam T
    refine ⟨T.V, inferInstance, inferInstance, σ, hDS, hcas, ?_, ?_, ?_⟩
    · intro S S' hS hS'
      exact lowKMultOne_of_cas hDS hgap hcas S S' hS hS'
    · intro μ
      infer_instance
    · intro S _ _ v _
      exact all_smooth_of_kType T hDS hK v
  · have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
      have hs : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
      have hn : 0 ≤ (n : ℝ) * S7.q0 ε := by positivity
      nlinarith
    obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor (hS7 n) T hlam hh hq h8
    have hv₀ : T.w ≠ 0 := by
      intro h0
      have h1' := T.w_norm
      rw [h0, norm_zero] at h1'
      exact zero_ne_one h1'
    refine ⟨Hlam ε Ψ T.w, inferInstance, inferInstance, sigLam ε Ψ T.w, ?_, ?_, ?_, ?_, ?_⟩
    · exact isDS_sigLam hgap hP hv₀
    · exact sigLam_casOnSmooth hgap hP hv₀
    · intro S S' hS hS'
      obtain ⟨-, huniq⟩ := sigLam_lowK hgap hP hv₀
      rw [huniq S hS, huniq S' hS']
    · exact sigLam_admissible hgap hP hv₀
    · intro S hSf hSK v hv
      exact sigLam_kfin_smooth hgap hP hv₀ v (sigLam_kfin hgap hP hv₀ S hSf hSK hv)

theorem lowKMultOneG_of_cas :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h →
      CasOnSmooth ε lam σ →
      ∀ S S' : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S →
        Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S' := by
  intro n ε lam H _ _ σ hlam hDS h hh hlt hcas S S' hS hS'
  have : CompleteSpace H := hDS.1
  exact lowKMultOne_of_cas hDS (stdGap_of_mir hlam hh hlt) hcas S S' hS hS'

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

theorem final_lowKMultOneG :
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → (N : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h →
      ∀ S S' : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S →
        Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S' := by
  intro N ε lam H _ _ σ hHC hDS h hgap hlt S S' hS hS'
  haveI : CompleteSpace H := hDS.1
  exact lowKMultOneG_of_cas N ε lam H σ hHC hDS h hgap hlt
    (casOnSmooth_of_isDS hDS ⟨hHC.1, h, hgap, hlt⟩) S S' hS hS'

theorem final_deg_DSUniqG :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h →
        ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x, U (σ g x) = σ' g (U x) := by
  intro n ε lam H H' _ _ _ _ _ _ σ σ' hHC hDS hDS' h hgap hlt
  exact (isDS_props_of_gap n ε lam hHC h hgap hlt H σ hDS).2.2.2.2 H' σ' hDS'

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem final_cayley_facts {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) :
    Pᴴ * P = 1 ∧ P * Pᴴ = 1 ∧ P⁻¹ = Pᴴ ∧ P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ = Formalism.REAL.Jm ε := by
  obtain ⟨⟨-, hJ⟩, hU⟩ := hP
  have h1 : Pᴴ * P = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have h2 : P * Pᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  refine ⟨h1, h2, Matrix.inv_eq_left_inv h1, ?_⟩
  rw [← hJ]
  calc P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ = (P * Pᴴ) * Formalism.REAL.Jm ε * (P * Pᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.one_mul, Matrix.mul_one]

theorem final_conj_mem {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * g * Pᴴ ∈ Formalism.MainNotions.S.UJset ε := by
  obtain ⟨-, -, -, h4⟩ := final_cayley_facts hP
  obtain ⟨⟨-, hJ⟩, -⟩ := hP
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * g * Pᴴ) = Formalism.REAL.Jm ε
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc P * (gᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * g * Pᴴ)
      = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by simp only [Matrix.mul_assoc]
    _ = P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by rw [hJ, hg']
    _ = Formalism.REAL.Jm ε := h4

theorem final_c_mem {P P' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (hP' : Formalism.MainNotions.S.IsCayleyU k r ε P') :
    P' * Pᴴ ∈ Formalism.MainNotions.S.UJset ε := by
  obtain ⟨-, -, -, h4⟩ := final_cayley_facts hP
  obtain ⟨⟨-, hJ'⟩, -⟩ := hP'
  show (P' * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P' * Pᴴ) = Formalism.REAL.Jm ε
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc P * P'ᴴ * Formalism.REAL.Jm ε * (P' * Pᴴ) = P * (P'ᴴ * Formalism.REAL.Jm ε * P') * Pᴴ := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hJ']; exact h4

end Cayley

theorem discrete_series_unique_large_gap :
    ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDSHpk k r ε lam σ →
      ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
        (σ' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDSHpk k r ε lam σ' →
      ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x) := by
  intro k r ε lam hHC h hgap hbd H _ _ _ σ hσ H' _ _ _ σ' hσ'
  obtain ⟨P, hP, hds⟩ := hσ
  obtain ⟨P', hP', hds'⟩ := hσ'
  obtain ⟨U, hU⟩ := final_deg_DSUniqG (2 * r + k + 1) ε lam H H' (fun g => σ (P⁻¹ * g * P))
    (fun g => σ' (P'⁻¹ * g * P')) hHC hds hds' h hgap hbd
  obtain ⟨h1, h2, h3, -⟩ := final_cayley_facts hP
  obtain ⟨h1', h2', h3', -⟩ := final_cayley_facts hP'
  have kP : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have kP' : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P'ᴴ * (P' * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have hU' : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : H, U (σ (P⁻¹ * g * P) x) = σ' (P'⁻¹ * g * P') (U x) := hU
  have hrep : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) (fun g => σ' (P'⁻¹ * g * P')) := hds'.2.2.1
  have hmul : ∀ a ∈ Formalism.MainNotions.S.UJset ε, ∀ b ∈ Formalism.MainNotions.S.UJset ε, ∀ y : H',
      σ' (P'⁻¹ * (a * b) * P') y = σ' (P'⁻¹ * a * P') (σ' (P'⁻¹ * b * P') y) := by
    intro a ha b hb y
    exact congrArg (fun T : H' →L[ℂ] H' => T y) (hrep.1.2 a ha b hb)
  have hnorm : ∀ a ∈ Formalism.MainNotions.S.UJset ε, ∀ y : H', ‖σ' (P'⁻¹ * a * P') y‖ = ‖y‖ := hrep.2.1
  have hone : σ' 1 = 1 := by
    have h0 : σ' (P'⁻¹ * 1 * P') = 1 := hrep.1.1
    rwa [Matrix.mul_one, h3', h1'] at h0
  have hc : P' * Pᴴ ∈ Formalism.MainNotions.S.UJset ε := final_c_mem hP hP'
  have hci : P * P'ᴴ ∈ Formalism.MainNotions.S.UJset ε := final_c_mem hP' hP
  let f : H' →ₗᵢ[ℂ] H' :=
    { toLinearMap := (σ' (P'⁻¹ * (P' * Pᴴ) * P')).toLinearMap
      norm_map' := hnorm _ hc }
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨σ' (P'⁻¹ * (P * P'ᴴ) * P') y, ?_⟩
    show σ' (P'⁻¹ * (P' * Pᴴ) * P') (σ' (P'⁻¹ * (P * P'ᴴ) * P') y) = y
    rw [← hmul _ hc _ hci]
    have e : P'⁻¹ * (P' * Pᴴ * (P * P'ᴴ)) * P' = 1 := by
      rw [h3']
      simp only [Matrix.mul_assoc, kP, kP', h1, h1', Matrix.mul_one]
    rw [e, hone]
    rfl
  refine ⟨U.trans (LinearIsometryEquiv.ofSurjective f hsurj), ?_⟩
  intro g hg x
  show σ' (P'⁻¹ * (P' * Pᴴ) * P') (U (σ g x)) = σ' g (σ' (P'⁻¹ * (P' * Pᴴ) * P') (U x))
  have hgP : P * g * Pᴴ ∈ Formalism.MainNotions.S.UJset ε := final_conj_mem hP hg
  have hgP' : P' * g * P'ᴴ ∈ Formalism.MainNotions.S.UJset ε := final_conj_mem hP' hg
  have eσ : σ g = σ (P⁻¹ * (P * g * Pᴴ) * P) := by
    congr 1
    rw [h3]
    simp only [Matrix.mul_assoc, kP, h1, Matrix.mul_one]
  have eσ' : σ' g = σ' (P'⁻¹ * (P' * g * P'ᴴ) * P') := by
    congr 1
    rw [h3']
    simp only [Matrix.mul_assoc, kP', h1', Matrix.mul_one]
  have e2 : (P' * Pᴴ) * (P * g * Pᴴ) = (P' * g * P'ᴴ) * (P' * Pᴴ) := by
    simp only [Matrix.mul_assoc, kP, kP']
  rw [eσ, hU' _ hgP, eσ', ← hmul _ hc _ hgP, ← hmul _ hgP' _ hc, e2]

end ReciprocityTheory.ChartRestriction.DS
