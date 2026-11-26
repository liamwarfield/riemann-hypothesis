module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLatticeEmbedding
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainIffPosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameChangeUnitary
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTranslatedRiemannLattice
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicAdaptedFrameOnBall
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusHolomorphicPotentialChange

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMajorantOfPositiveFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMajorantOfPositiveFrame
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ComplexOrder

section Conj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev cj (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := A.map (starRingEnd ℂ)

theorem cj_cj (A : Matrix ι ι ℂ) : cj (cj A) = A := by
  ext i k; simp [cj]

theorem cj_injective : Function.Injective (cj : Matrix ι ι ℂ → Matrix ι ι ℂ) :=
  Function.LeftInverse.injective cj_cj

theorem cj_mul (A B : Matrix ι ι ℂ) : cj (A * B) = cj A * cj B := Matrix.map_mul

theorem cj_eq (A : Matrix ι ι ℂ) : cj A = Aᴴᵀ := by
  ext i k; simp [cj]

theorem cj_inv (A : Matrix ι ι ℂ) : cj A⁻¹ = (cj A)⁻¹ := by
  rw [cj_eq, cj_eq, conjTranspose_nonsing_inv, transpose_nonsing_inv]

theorem cj_conjTranspose (A : Matrix ι ι ℂ) : cj Aᴴ = (cj A)ᴴ := by
  ext i k; simp [cj]

theorem posDef_cj {P : Matrix ι ι ℂ} (h : P.PosDef) : (cj P).PosDef := by
  have : cj P = Pᵀ := by rw [cj_eq, h.1.eq]
  rw [this]
  exact h.transpose

theorem cj_mulVec (A : Matrix ι ι ℂ) (v : ι → ℂ) : cj A *ᵥ star v = star (A *ᵥ v) := by
  ext i; simp [cj, mulVec, dotProduct, map_sum]

theorem re_term_cj (P G : Matrix ι ι ℂ) (v : ι → ℂ) :
    (star (G *ᵥ star v) ⬝ᵥ (cj P *ᵥ (G *ᵥ star v))).re = (star (cj G *ᵥ v) ⬝ᵥ (P *ᵥ (cj G *ᵥ v))).re := by
  have hu : G *ᵥ star v = star (cj G *ᵥ v) := by
    rw [← cj_mulVec, cj_cj]
  rw [hu, cj_mulVec, star_dotProduct_star, dotProduct_comm]
  simp

theorem stab_iff_cj (P G : Matrix ι ι ℂ) :
    (G.map (starRingEnd ℂ))ᵀ * cj P * G = cj P ↔ (cj G)ᴴ * P * cj G = P := by
  have h : (G.map (starRingEnd ℂ))ᵀ * cj P * G = cj ((cj G)ᴴ * P * cj G) := by
    rw [cj_mul, cj_mul, cj_conjTranspose, cj_cj]
    rfl
  rw [h]
  exact cj_injective.eq_iff

end Conj

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

omit [IsCMField E] in
theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (a : E) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

omit [IsCMField E] in
theorem embOf_comp (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (by
    ext a; simpa using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) a)

omit [IsCMField E] in
theorem embOf_injective : Function.Injective (embOf : (𝓞 E →+* ℂ) → (E →+* ℂ)) := by
  intro s s' h
  ext a
  have := congrArg (fun φ : E →+* ℂ => φ (a : E)) h
  simpa [embOf_coe] using this

theorem plc_bijective (F : UnivFam E Ψ j j' n g Λ) : Function.Bijective (plc F) := by
  have hcm := F.cm
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact hcm.1 (embOf_injective h)
    · exfalso
      have hs : F.σ τ' = (starRingEnd ℂ).comp (F.σ τ) := by
        ext a
        have := congrArg (fun φ : E →+* ℂ => φ (a : E)) h
        simpa [embOf_coe, ComplexEmbedding.conjugate_coe_eq] using this.symm
      exact ((hcm.2 (F.σ τ)).1 ⟨τ, rfl⟩) ⟨τ', hs⟩
  · intro w
    set s : 𝓞 E →+* ℂ := w.embedding.comp (algebraMap (𝓞 E) E) with hs
    by_cases h : ∃ τ, F.σ τ = s
    · obtain ⟨τ, hτ⟩ := h
      refine ⟨τ, ?_⟩
      rw [plc, hτ, hs, embOf_comp, InfinitePlace.mk_embedding]
    · have h2 : ∃ τ, F.σ τ = (starRingEnd ℂ).comp s := by
        by_contra h3
        exact h ((hcm.2 s).2 h3)
      obtain ⟨τ, hτ⟩ := h2
      refine ⟨τ, ?_⟩
      have he : embOf (F.σ τ) = ComplexEmbedding.conjugate w.embedding := by
        rw [hτ]
        have : (starRingEnd ℂ).comp s =
            (ComplexEmbedding.conjugate w.embedding).comp (algebraMap (𝓞 E) E) := by
          ext a; simp [hs, ComplexEmbedding.conjugate_coe_eq]
        rw [this, embOf_comp]
      rw [plc, he, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem emb_ne (F : UnivFam E Ψ j j' n g Λ) (τ : Ψ) (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) :=
  (InfinitePlace.embedding_mk_eq (embOf (F.σ τ))).resolve_left h

def atPlc (F : UnivFam E Ψ j j' n g Λ) (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (τ : Ψ) :
    Matrix (Fin (j + j')) (Fin (j + j')) ℂ := by
  classical
  exact if (plc F τ).embedding = embOf (F.σ τ) then Pt τ else cj (Pt τ)

variable {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem gramAt_of_eq {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) = C.gr τ := by
  rw [gramAt, h]; rfl

theorem gramAt_of_ne {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) = cj (C.gr τ) := by
  rw [gramAt, emb_ne F τ h]
  ext i k
  simp [LatEmb.gr, ComplexEmbedding.conjugate_coe_eq]

theorem vecAt_of_eq (x : Λ) {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x) (plc F τ) = C.vec x τ := by
  ext i
  simp [vecAt, LatEmb.vec, h]

theorem vecAt_of_ne (x : Λ) {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x) (plc F τ) = star (C.vec x τ) := by
  ext i
  simp [vecAt, LatEmb.vec, emb_ne F τ h, ComplexEmbedding.conjugate_coe_eq]

theorem tm_of_eq (a : C.Arch) {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    C.tm a τ = ((a : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) := by
  rw [LatEmb.tm, tauMat, if_pos h]

theorem tm_of_ne (a : C.Arch) {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    C.tm a τ = cj ((a : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) := by
  rw [LatEmb.tm, tauMat, if_neg h]

theorem atPlc_of_eq (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) {τ : Ψ}
    (h : (plc F τ).embedding = embOf (F.σ τ)) : atPlc F Pt τ = Pt τ := by
  rw [atPlc]; exact if_pos h

theorem atPlc_of_ne (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) {τ : Ψ}
    (h : (plc F τ).embedding ≠ embOf (F.σ τ)) : atPlc F Pt τ = cj (Pt τ) := by
  rw [atPlc]; exact if_neg h

def majOf (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) : Majorant C.h (Pi.basisFun E (Fin (j + j'))) where
  P w := atPlc F Pt ((Equiv.ofBijective _ (plc_bijective F)).symm w)
  posDef w := by
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    have hτ : (Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ) = τ :=
      Equiv.ofBijective_symm_apply_apply _ _ _
    rw [hτ]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h]; exact hP τ
    · rw [atPlc_of_ne Pt h]; exact posDef_cj (hP τ)
  siegel w := by
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    have hτ : (Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ) = τ :=
      Equiv.ofBijective_symm_apply_apply _ _ _
    rw [hτ]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h, gramAt_of_eq C h]; exact hS τ
    · rw [atPlc_of_ne Pt h, gramAt_of_ne C h, ← cj_inv, ← cj_mul, ← cj_mul, hS τ]

theorem majOf_P (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (τ : Ψ) : (majOf C Pt hP hS).P (plc F τ) = atPlc F Pt τ := by
  show atPlc F Pt ((Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ)) = _
  rw [Equiv.ofBijective_symm_apply_apply]

theorem majOf_term (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (a : C.Arch) (x : Λ) (τ : Ψ) :
    (star (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x)) (plc F τ)) ⬝ᵥ
      ((majOf C Pt hP hS).P (plc F τ) *ᵥ invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x)) (plc F τ))).re =
    (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re := by
  rw [majOf_P]
  by_cases h : (plc F τ).embedding = embOf (F.σ τ)
  · rw [atPlc_of_eq Pt h, tm_of_eq C _ h, ← vecAt_of_eq C x h]
    rfl
  · rw [atPlc_of_ne Pt h, tm_of_ne C _ h, ← re_term_cj, ← vecAt_of_ne C x h]
    rfl

theorem majOf_len (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (a : C.Arch) (x : Λ) :
    (majOf C Pt hP hS).len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x))) ^ 2 =
      ∑ τ, (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re := by
  rw [Majorant.len, Real.sq_sqrt]
  · rw [← (Equiv.ofBijective _ (plc_bijective F)).sum_comp]
    exact Finset.sum_congr rfl fun τ _ => majOf_term C Pt hP hS a x τ
  · exact Finset.sum_nonneg fun w _ => ((majOf C Pt hP hS).posDef w).posSemidef.re_dotProduct_nonneg _

theorem majOf_stab (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (c : C.Arch) :
    c ∈ (majOf C Pt hP hS).stab ↔ ∀ τ, (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ := by
  have hloc : ∀ τ, ((((c : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)).map
        (starRingEnd ℂ))ᵀ * (majOf C Pt hP hS).P (plc F τ) *
        ((c : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) =
        (majOf C Pt hP hS).P (plc F τ) ↔ (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ := by
    intro τ
    rw [majOf_P]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h, tm_of_eq C _ h]
      rfl
    · rw [atPlc_of_ne Pt h, tm_of_ne C _ h]
      exact stab_iff_cj _ _
  rw [Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi]
  constructor
  · intro hc τ
    exact (hloc τ).1 (mem_unitaryGroupMatrix.1 (hc (plc F τ) (Set.mem_univ _)))
  · intro hc w _
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    exact mem_unitaryGroupMatrix.2 ((hloc τ).2 (hc τ))

end Arch

theorem exists_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F)
    (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (Pt τ).PosDef) →
    (∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) →
    ∃ M : Majorant C.h (Pi.basisFun E (Fin (j + j'))),
      (∀ (a : C.Arch) (x : Λ), M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x))) ^ 2 =
        ∑ τ, (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re) ∧
      ∀ c : C.Arch, c ∈ M.stab ↔ ∀ τ, (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ :=
  by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C Pt hP hS
  exact ⟨majOf C Pt hP hS, majOf_len C Pt hP hS, majOf_stab C Pt hP hS⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMajorantOfPositiveFrameStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_majorant_of_positive_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (Pt τ).PosDef) → (∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) → ∃ M : Majorant C.h (Pi.basisFun E (Fin (j + j'))), (∀ (a : C.Arch) (x : Λ), M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x))) ^ 2 = ∑ τ, (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re) ∧ ∀ c : C.Arch, c ∈ M.stab ↔ ∀ τ, (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj.exists_majorant | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj.exists_majorant | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj.exists_majorant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitaryRepresentation
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitaryRepresentation
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic

theorem conj_unitary {ι : Type} [Fintype ι] (M G : Matrix ι ι ℂ)
    (h : (M.map (starRingEnd ℂ))ᵀ * G.map (starRingEnd ℂ) * M = G.map (starRingEnd ℂ)) :
    (M.map (starRingEnd ℂ))ᴴ * G * M.map (starRingEnd ℂ) = G := by
  have h2 := congrArg (fun X : Matrix ι ι ℂ => X.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul] at h2
  have e1 : (G.map (starRingEnd ℂ)).map (starRingEnd ℂ) = G := by ext i k; simp
  have e2 : ((M.map (starRingEnd ℂ))ᵀ).map (starRingEnd ℂ) = (M.map (starRingEnd ℂ))ᴴ := by
    ext i k; simp [Matrix.conjTranspose_apply]
  rw [e1, e2] at h2
  exact h2

theorem tm_basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), (∀ (a b : C.Arch) τ, C.tm (a * b) τ = C.tm a τ * C.tm b τ) ∧ (∀ τ, C.tm 1 τ = 1) ∧ (∀ (a : C.Arch) τ, (C.tm a τ)ᴴ * C.gr τ * C.tm a τ = C.gr τ) ∧ ∀ τ, Continuous fun a : C.Arch => C.tm a τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b τ
    simp only [LatEmb.tm, tauMat]
    split_ifs with h
    · simp
    · simp [Matrix.map_mul]
  · intro τ
    simp only [LatEmb.tm, tauMat]
    split_ifs with h
    · simp
    · simp
  · intro a τ
    have hm := mem_archUnitary.1 a.2 (plc F τ)
    simp only [LatEmb.tm, tauMat, LatEmb.gr]
    by_cases h0 : (plc F τ).embedding = embOf (F.σ τ)
    · rw [if_pos h0]
      rw [gramAt, h0] at hm
      have e : ((a.1 (plc F τ) : GL (Fin (j + j')) ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)ᴴ =
          (((a.1 (plc F τ) : GL (Fin (j + j')) ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ).map
            (starRingEnd ℂ))ᵀ := by
        ext i k; simp [Matrix.conjTranspose_apply]
      rw [e]
      exact hm
    · have h' : (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) :=
        (InfinitePlace.embedding_mk_eq (embOf (F.σ τ))).resolve_left h0
      rw [if_neg h0]
      apply conj_unitary
      have e : gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) =
          ((gram C.h.toSesq (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))).map (starRingEnd ℂ) := by
        rw [gramAt, h']
        ext i k
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [e] at hm
      exact hm
  · intro τ
    simp only [LatEmb.tm, tauMat]
    have hc : Continuous fun a : C.Arch =>
        ((a.1 (plc F τ) : GL _ ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) :=
      Units.continuous_val.comp ((continuous_apply (plc F τ)).comp continuous_subtype_val)
    split_ifs with h
    · exact hc
    · exact hc.matrix_map Complex.continuous_conj

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitaryRepresentationStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_unitary_representation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), (∀ (a b : C.Arch) τ, C.tm (a * b) τ = C.tm a τ * C.tm b τ) ∧ (∀ τ, C.tm 1 τ = 1) ∧ (∀ (a : C.Arch) τ, (C.tm a τ)ᴴ * C.gr τ * C.tm a τ = C.gr τ) ∧ ∀ τ, Continuous fun a : C.Arch => C.tm a τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic.tm_basic | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic.tm_basic | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic.tm_basic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanActionOnLatticeVectors
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanActionOnLatticeVectors
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem tm_archEmbed_mulVec_vec (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ)
    (C : LatEmb F) (γ : C.h.unitaryGroup) (x : Λ) (τ : Ψ) :
    C.tm (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ) τ *ᵥ C.vec x τ =
      fun i => embOf (F.σ τ)
        (((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) i) := by
  set b := Pi.basisFun E (Fin (j + j')) with hb
  set G : GL (Fin (j + j')) E := (unitaryGroupEquivMatrix C.h b γ).1 with hG
  have hGM : (G : Matrix (Fin (j + j')) (Fin (j + j')) E) =
      LinearMap.toMatrix b b (((γ : C.h.unitaryGroup) :
        (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) : (Fin (j + j') → E) →ₗ[E] (Fin (j + j') → E)) :=
    unitaryGroupEquivMatrix_apply C.h b γ
  have hact : ∀ v : Fin (j + j') → E, (G : Matrix (Fin (j + j')) (Fin (j + j')) E) *ᵥ v =
      ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) v := by
    intro v
    rw [hGM, hb, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_mulVec]
    rfl
  have htm : C.tm (archEmbed C.h b γ) τ =
      (G : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) := by
    have hw : ∀ w : InfinitePlace E,
        (((archEmbed C.h b γ : archUnitary C.h b) : InfinitePlace E → GL (Fin (j + j')) ℂ) w :
          Matrix (Fin (j + j')) (Fin (j + j')) ℂ) =
        (G : Matrix (Fin (j + j')) (Fin (j + j')) E).map w.embedding := fun w => rfl
    unfold LatEmb.tm tauMat
    split_ifs with h
    · rw [hw, h]
    · rw [hw]
      rcases InfinitePlace.embedding_mk_eq (embOf (F.σ τ)) with h' | h'
      · exact absurd h' h
      · have h'' : (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) := h'
        rw [h'']
        ext a c
        simp [ComplexEmbedding.conjugate_coe_eq]
  rw [htm]
  funext i
  have := RingHom.map_mulVec (embOf (F.σ τ)) (G : Matrix (Fin (j + j')) (Fin (j + j')) E) (C.e x) i
  rw [hact] at this
  rw [this]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanActionOnLatticeVectorsStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_action_on_lattice_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (γ : C.h.unitaryGroup) (x : Λ) (τ : Ψ), C.tm (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ) τ *ᵥ C.vec x τ = fun i => embOf (F.σ τ) (((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_archEmbed_mulVec_vec | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_archEmbed_mulVec_vec | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_archEmbed_mulVec_vec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroContinuous
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

open Matrix GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem IsSgU.det_toBlocks₁₁_ne_zero {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) :
    u.toBlocks₁₁.det ≠ 0 := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, u = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩
  rw [toBlocks_fromBlocks₁₁]
  unfold IsSgU sgI at hu
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at hu
  have h := (fromBlocks_inj.1 hu).1
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg] at h
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have h1 : -(Cᴴ *ᵥ (C *ᵥ v)) = v := by
    have h2 := congrArg (fun M => M *ᵥ v) h
    simp only [Matrix.add_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hAv,
      Matrix.mulVec_zero, zero_add] at h2
    exact h2
  have h3 : star v ⬝ᵥ v = -(star (C *ᵥ v) ⬝ᵥ (C *ᵥ v)) := by
    calc star v ⬝ᵥ v = star v ⬝ᵥ (-(Cᴴ *ᵥ (C *ᵥ v))) := by rw [h1]
      _ = -(star (C *ᵥ v) ⬝ᵥ (C *ᵥ v)) := by
        rw [dotProduct_neg, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have h4 : 0 ≤ star v ⬝ᵥ v := dotProduct_star_self_nonneg v
  have h5 : 0 ≤ star (C *ᵥ v) ⬝ᵥ (C *ᵥ v) := dotProduct_star_self_nonneg _
  have h6 : star v ⬝ᵥ v = 0 := le_antisymm (by rw [h3]; exact neg_nonpos.2 h5) h4
  exact hv (dotProduct_star_self_eq_zero.1 h6)

theorem moebW_zero (u : Matrix (Sg j j') (Sg j j') ℂ) : moebW u 0 = u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ := by
  simp [moebW]

theorem continuous_matrix_inv {X m : Type} [TopologicalSpace X] [Fintype m] [DecidableEq m]
    {A : X → Matrix m m ℂ} (hA : Continuous A) (hd : ∀ x, (A x).det ≠ 0) :
    Continuous fun x => (A x)⁻¹ := by
  have h : (fun x => (A x)⁻¹) = fun x => ((A x).det)⁻¹ • (A x).adjugate := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hA.matrix_det.inv₀ hd).smul hA.matrix_adjugate

theorem continuous_moebBall_zero (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (X : Type) [TopologicalSpace X] (f : X → Ψ → Matrix (Sg j j') (Sg j j') ℂ)
    (hc : ∀ τ, Continuous fun x => f x τ) (hu : ∀ x τ, IsSgU (f x τ)) :
    Continuous fun x => moebBall q (f x) 0 := by
  have hb : ∀ τ, (ballMat q 0 τ)ᵀ = 0 := by
    intro τ
    ext a b
    simp [ballMat]
  refine continuous_pi fun k => ?_
  simp only [moebBall, ballPt, hb, moebW_zero]
  set τ := (q.symm k).1
  have h11 : Continuous fun x => (f x τ).toBlocks₁₁ :=
    continuous_matrix fun a b => (hc τ).matrix_elem _ _
  have h21 : Continuous fun x => (f x τ).toBlocks₂₁ :=
    continuous_matrix fun a b => (hc τ).matrix_elem _ _
  have hm := h21.matrix_mul (continuous_matrix_inv h11 fun x => (hu x τ).det_toBlocks₁₁_ne_zero)
  exact hm.matrix_elem _ _

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroContinuousStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_mobius_zero_continuous : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (X : Type) [TopologicalSpace X] (f : X → Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, Continuous fun x => f x τ) → (∀ x τ, IsSgU (f x τ)) → Continuous fun x => moebBall q (f x) 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitarySurjective
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitarySurjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

section TmSurj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem embOf_coe (s : 𝓞 E →+* ℂ) (x : 𝓞 E) : embOf s (x : E) = s x :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) x


omit [IsCMField E] in
theorem embOf_restrict (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext x
  simpa using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) x


omit [IsCMField E] in
theorem embOf_conj (s : 𝓞 E →+* ℂ) : embOf ((starRingEnd ℂ).comp s) = ComplexEmbedding.conjugate (embOf s) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext x
  have h1 := embOf_coe ((starRingEnd ℂ).comp s) x
  have h2 := embOf_coe s x
  simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq]
  change embOf ((starRingEnd ℂ).comp s) (x : E) = starRingEnd ℂ (embOf s (x : E))
  rw [h1, h2]; rfl


omit [IsCMField E] in
theorem embOf_inj {s s' : 𝓞 E →+* ℂ} (h : embOf s = embOf s') : s = s' := by
  ext x
  rw [← embOf_coe s, ← embOf_coe s', h]

variable {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem plc_bijective (F : UnivFam E Ψ j j' n g Λ) : Function.Bijective (plc F) := by
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact F.cm.1 (embOf_inj h)
    · exfalso
      rw [← embOf_conj] at h
      have h' := embOf_inj h
      exact (F.cm.2 (F.σ τ)).1 ⟨τ, rfl⟩ ⟨τ', h'.symm⟩
  · intro w
    by_cases hs : ∃ τ, F.σ τ = w.embedding.comp (algebraMap (𝓞 E) E)
    · obtain ⟨τ, hτ⟩ := hs
      refine ⟨τ, ?_⟩
      simp only [plc, hτ, embOf_restrict, InfinitePlace.mk_embedding]
    · have := not_imp_not.2 (F.cm.2 (w.embedding.comp (algebraMap (𝓞 E) E))).2 hs
      obtain ⟨τ, hτ⟩ := not_not.1 this
      refine ⟨τ, ?_⟩
      have : embOf (F.σ τ) = ComplexEmbedding.conjugate w.embedding := by
        rw [hτ, ← RingHom.comp_assoc, embOf_restrict]; rfl
      simp only [plc, this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

end TmSurj

theorem tm_surj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (b : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (b τ)ᴴ * C.gr τ * b τ = C.gr τ) → ∃ a : C.Arch, ∀ τ, C.tm a τ = b τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C b hb
  classical
  have hbij := plc_bijective F
  let e : Ψ ≃ InfinitePlace E := Equiv.ofBijective (plc F) hbij
  have he : ∀ τ, e.symm (plc F τ) = τ := fun τ => e.symm_apply_apply τ
  have hw : ∀ w, plc F (e.symm w) = w := fun w => e.apply_symm_apply w
  let v := Pi.basisFun E (Fin (j + j'))
  let M : InfinitePlace E → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun w =>
    if w.embedding = embOf (F.σ (e.symm w)) then b (e.symm w) else (b (e.symm w)).map (starRingEnd ℂ)
  have hct : ∀ X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ := fun X => by
    ext i k; simp [Matrix.conjTranspose_apply]
  have hM : ∀ w, ((M w).map (starRingEnd ℂ))ᵀ * gramAt C.h v w * M w = gramAt C.h v w := by
    intro w
    have hτ := hb (e.symm w)
    rw [hct]
    by_cases hc : w.embedding = embOf (F.σ (e.symm w))
    · have hg : gramAt C.h v w = C.gr (e.symm w) := by
        simp only [gramAt, LatEmb.gr, hc]; rfl
      simp only [M, if_pos hc, hg]
      exact hτ
    · have hconj : w.embedding = ComplexEmbedding.conjugate (embOf (F.σ (e.symm w))) := by
        have h1 : InfinitePlace.mk (embOf (F.σ (e.symm w))) = InfinitePlace.mk w.embedding := by
          rw [InfinitePlace.mk_embedding]; exact hw w
        rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
        · exact absurd h.symm hc
        · exact h.symm
      have hg : gramAt C.h v w = (C.gr (e.symm w)).map (starRingEnd ℂ) := by
        ext i k
        simp only [gramAt, LatEmb.gr, Matrix.map_apply, hconj]
        rfl
      have h2 := congrArg (fun X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ => X.map (starRingEnd ℂ)) hτ
      simp only [Matrix.map_mul] at h2
      have h3 : ((b (e.symm w)).map (starRingEnd ℂ))ᴴ = ((b (e.symm w))ᴴ).map (starRingEnd ℂ) := by
        ext i k; simp [Matrix.conjTranspose_apply]
      simp only [M, if_neg hc, hg]
      rw [h3]
      exact h2
  have hH : ∀ w, IsUnit (gramAt C.h v w).det := by
    intro w
    have := (isUnit_det_gram C.h v).map w.embedding
    rw [RingHom.map_det] at this
    exact this
  let a : InfinitePlace E → GL (Fin (j + j')) ℂ := fun w =>
    Matrix.nonsingInvUnit (M w) (isUnit_det_of_unitary (starRingEnd ℂ) (hH w) (hM w))
  have ha : a ∈ C.Arch := mem_archUnitary.2 fun w => hM w
  refine ⟨⟨a, ha⟩, fun τ => ?_⟩
  have haM : ∀ w, (a w : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) = M w := fun w => rfl
  simp only [LatEmb.tm, tauMat, haM, M, he]
  by_cases hc : (plc F τ).embedding = embOf (F.σ τ)
  · simp only [if_pos hc]
  · simp only [if_neg hc]
    ext i k
    simp

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitarySurjectiveStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_unitary_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (b : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (b τ)ᴴ * C.gr τ * b τ = C.gr τ) → ∃ a : C.Arch, ∀ τ, C.tm a τ = b τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_surj | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_surj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_surj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGroupDictionary
noncomputable section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem eqvBy_symm {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R R' : RiemLat E g Λ} (h : R.EqvBy R' 1) : R'.EqvBy R 1 := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k.symm, fun x => ?_⟩
  have := hk x
  simp only [LinearEquiv.coe_one, id_eq] at this ⊢
  rw [this, LinearEquiv.symm_apply_apply]

theorem zero_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by
    ext a b
    simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

theorem star_mulVec_dot {m k : Type} [Fintype m] [Fintype k] (c : Matrix m k ℂ) (y : k → ℂ) :
    star (c *ᵥ y) ⬝ᵥ (c *ᵥ y) = star y ⬝ᵥ ((cᴴ * c) *ᵥ y) := by
  rw [star_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star y) cᴴ]

theorem groupDict_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ)
    (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ), Nonempty (GroupDict F) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ H F
  classical
  obtain ⟨C⟩ := GlobalTheory.T.exists_lattice_embedding E Ψ j j' n g Λ H F
  have h0 : (0 : Fin n → ℂ) ∈ ballDom F.q := zero_mem_ballDom F.q
  have hform : ∀ t, (F.R t).form = F.form := F.form_eq
  obtain ⟨A0, hA0⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R 0) (hform 0) (F.sig 0 h0)
  have fct := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A0 τ) (hA0.unit τ)
  obtain ⟨hmul, hone, huni, hcont⟩ := GlobalTheory.T.archimedean_unitary_representation E Ψ j j' n g Λ F C
  have hinv : ∀ (a : C.Arch) τ, C.tm a τ * C.tm a⁻¹ τ = 1 := by
    intro a τ
    rw [← hmul, mul_inv_cancel, hone]
  have hinv' : ∀ (a : C.Arch) τ, C.tm a⁻¹ τ * C.tm a τ = 1 := by
    intro a τ
    rw [← hmul, inv_mul_cancel, hone]
  let Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun τ => (C.cinv (A0 τ) τ)ᴴ * C.cinv (A0 τ) τ
  obtain ⟨M, hMlen, hMstab⟩ := GlobalTheory.T.exists_majorant_of_positive_frame E Ψ j j' n g Λ F C Pt (fun τ => (fct τ).2.2.1) (fun τ => (fct τ).2.2.2.1)

  have hrot : ∀ a : C.Arch, ∃ R' : RiemLat E g Λ, R'.form = (F.R 0).form ∧ R'.B = (F.R 0).B ∧
      (∀ x, R'.P x = C.perExt (F.R 0) fun τ => C.tm a⁻¹ τ *ᵥ C.vec x τ) ∧
      C.IsAdapted R' (fun τ => C.tm a τ * A0 τ) := by
    intro a
    obtain ⟨R', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_translated_riemann_lattice E Ψ j j' n g Λ F C (F.R 0) (C.tm a) (C.tm a⁻¹) (hform 0) (hinv a)
      (huni a)
    exact ⟨R', h1, h2, h3, h4 A0 hA0⟩
  choose rot rform rB rP rad using hrot
  have rform' : ∀ a, (rot a).form = F.form := fun a => (rform a).trans (hform 0)
  have rsig : ∀ a, (rot a).HasSig F.σ j j' := by
    intro a
    have := F.sig 0 h0
    unfold RiemLat.HasSig at this ⊢
    rw [rB a]
    exact this
  have hu : ∀ a, ∃! t, t ∈ ballDom F.q ∧ (F.R t).EqvBy (rot a) 1 := fun a => F.univ (rot a) (rform' a) (rsig a)
  have hex := fun a => (hu a).exists
  choose π hπ using hex
  have huniq : ∀ a t, t ∈ ballDom F.q → (F.R t).EqvBy (rot a) 1 → π a = t := fun a t ht he =>
    (hu a).unique (hπ a) ⟨ht, he⟩
  have radπ : ∀ a, C.IsAdapted (F.R (π a)) (fun τ => C.tm a τ * A0 τ) := fun a =>
    GlobalTheory.T.adapted_frame_of_equivalent E Ψ j j' n g Λ F C (rot a) (F.R (π a)) _ (rad a) (eqvBy_symm (hπ a).2)
  have aUnit : ∀ (a : C.Arch) τ, (C.tm a τ * A0 τ)ᴴ * C.sgr τ * (C.tm a τ * A0 τ) = sgI j j' := fun a τ =>
    ((fct τ).2.2.2.2.1 _ _ (hinv a τ) (huni a τ)).1
  have aCinv : ∀ (a : C.Arch) τ, C.cinv (C.tm a τ * A0 τ) τ = C.cinv (A0 τ) τ * C.tm a⁻¹ τ := fun a τ =>
    ((fct τ).2.2.2.2.1 _ _ (hinv a τ) (huni a τ)).2.1
  let u : C.Arch → Ψ → Matrix (Sg j j') (Sg j j') ℂ := fun a τ => C.cinv (A0 τ) τ * (C.tm a τ * A0 τ)
  have uU : ∀ a τ, IsSgU (u a τ) := fun a τ => ((fct τ).2.2.2.2.1 _ _ (hinv a τ) (huni a τ)).2.2.1
  have uMul : ∀ a b τ, u (a * b) τ = u a τ * u b τ := by
    intro a b τ
    have h1 : A0 τ * C.cinv (A0 τ) τ = 1 := (fct τ).2.1
    show C.cinv (A0 τ) τ * (C.tm (a * b) τ * A0 τ) = C.cinv (A0 τ) τ * (C.tm a τ * A0 τ) * (C.cinv (A0 τ) τ * (C.tm b τ * A0 τ))
    rw [hmul]
    have e : C.cinv (A0 τ) τ * (C.tm a τ * A0 τ) * (C.cinv (A0 τ) τ * (C.tm b τ * A0 τ)) =
        C.cinv (A0 τ) τ * C.tm a τ * ((A0 τ * C.cinv (A0 τ) τ) * (C.tm b τ * A0 τ)) := by
      simp only [Matrix.mul_assoc]
    rw [e, h1, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨Z, G₁, hZ, hG₁, hZeq, hpot⟩ := GlobalTheory.T.holomorphic_adapted_frame_on_ball E Ψ j j' n g Λ F C A0 hA0
  have hZπ : ∀ a, Z (π a) = moebBall F.q (u a) 0 := fun a => hZeq _ (hπ a).1 _ (radπ a)

  have hsurj : ∀ t ∈ ballDom F.q, ∃ a, π a = t := by
    intro t ht
    obtain ⟨At, hAt⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R t) (hform t) (F.sig t ht)
    obtain ⟨a, ha⟩ := GlobalTheory.T.archimedean_unitary_surjective E Ψ j j' n g Λ F C (fun τ => At τ * C.cinv (A0 τ) τ)
      (fun τ => (fct τ).2.2.2.2.2 _ (hAt.unit τ))
    have hAa : (fun τ => C.tm a τ * A0 τ) = At := by
      funext τ
      rw [ha τ, Matrix.mul_assoc, (fct τ).1, Matrix.mul_one]
    have h1 := rad a
    rw [hAa] at h1
    exact ⟨a, huniq a t ht (GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C (F.R t) (rot a) At (hform t) (rform' a) hAt h1)⟩

  let v : C.Arch → C.Arch → Ψ → Matrix (Sg j j') (Sg j j') ℂ := fun a b τ =>
    C.cinv (C.tm a τ * A0 τ) τ * (C.tm b τ * A0 τ)
  have vEq : ∀ a b τ, v a b τ = u (a⁻¹ * b) τ := by
    intro a b τ
    show C.cinv (C.tm a τ * A0 τ) τ * (C.tm b τ * A0 τ) = C.cinv (A0 τ) τ * (C.tm (a⁻¹ * b) τ * A0 τ)
    rw [aCinv, hmul]
    simp only [Matrix.mul_assoc]
  have hfib1 : ∀ a b, π a = π b ↔ ∀ τ, (v a b τ)ᴴ * v a b τ = 1 := by
    intro a b
    have key := GlobalTheory.T.adapted_frame_change_unitary E Ψ j j' n g Λ F C (F.R (π a)) _ (fun τ => C.tm b τ * A0 τ) (hform _) (radπ a) (aUnit b)
    rw [← show (C.IsAdapted (F.R (π a)) (fun τ => C.tm b τ * A0 τ)) ↔ π a = π b from ?_]
    · exact key
    constructor
    · intro h
      exact (huniq b (π a) (hπ a).1 (GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C (F.R (π a)) (rot b) _ (hform _) (rform' b) h (rad b))).symm
    · intro h
      rw [h]
      exact radπ b
  have hfib2 : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ M.stab := by
    intro a b
    rw [hfib1, hMstab]
    refine forall_congr' fun τ => ?_
    rw [vEq]
    exact ((fct τ).2.2.2.2.1 _ _ (hinv _ τ) (huni _ τ)).2.2.2
  have hfib3 : ∀ a b, Z (π a) = Z (π b) → π a = π b := by
    intro a b h
    rw [hZπ, hZπ] at h
    rw [hfib1]
    have hb : (fun τ => u a τ * u (a⁻¹ * b) τ) = u b := by
      funext τ
      rw [← uMul, mul_inv_cancel_left]
    have := (GlobalTheory.T.ball_mobius_zero_eq_iff_unitary Ψ j j' n F.q (u a) (u (a⁻¹ * b)) (uU a) (uU _)).1 (by rw [hb]; exact h)
    intro τ
    rw [vEq]
    exact this τ
  have hbij : Set.BijOn Z (ballDom F.q) (ballDom F.q) := by
    have hmaps : Set.MapsTo Z (ballDom F.q) (ballDom F.q) := by
      intro t ht
      obtain ⟨a, rfl⟩ := hsurj t ht
      rw [hZπ]
      exact (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n F.q (u a) (uU a)).2.1 h0
    refine ⟨hmaps, ?_, ?_⟩
    · intro t ht t' ht' h
      obtain ⟨a, rfl⟩ := hsurj t ht
      obtain ⟨b, rfl⟩ := hsurj t' ht'
      exact hfib3 a b h
    · intro s hs
      obtain ⟨w, hw, hws⟩ := GlobalTheory.T.ball_mobius_transitive Ψ j j' n F.q s hs
      obtain ⟨a, ha⟩ := GlobalTheory.T.archimedean_unitary_surjective E Ψ j j' n g Λ F C (fun τ => (A0 τ * w τ) * C.cinv (A0 τ) τ) (fun τ => by
        refine (fct τ).2.2.2.2.2 _ ?_
        have hw' := hw τ
        unfold IsSgU at hw'
        rw [← hw', ← (hA0.unit τ)]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc])
      have hua : u a = w := by
        funext τ
        show C.cinv (A0 τ) τ * (C.tm a τ * A0 τ) = w τ
        rw [ha τ, Matrix.mul_assoc (A0 τ * w τ), (fct τ).1, Matrix.mul_one, ← Matrix.mul_assoc, (fct τ).1, Matrix.one_mul]
      refine ⟨π a, (hπ a).1, ?_⟩
      rw [hZπ, hua, hws]
  obtain ⟨Y, hY, hYZ⟩ := GlobalTheory.T.ball_automorphism_inverse_exists Ψ j j' n F.q Z G₁ hZ hbij hG₁ hpot
  have hπY : ∀ a, π a = Y (moebBall F.q (u a) 0) := fun a => by
    rw [← hZπ, (hYZ _ (hπ a).1).2.2]
  have hucont : Continuous fun a : C.Arch => moebBall F.q (u a) 0 := by
    refine GlobalTheory.T.ball_mobius_zero_continuous Ψ j j' n F.q C.Arch u (fun τ => ?_) uU
    exact continuous_const.matrix_mul ((hcont τ).matrix_mul continuous_const)
  have hmem : ∀ a, moebBall F.q (u a) 0 ∈ ballDom F.q := fun a =>
    (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n F.q (u a) (uU a)).2.1 h0
  obtain ⟨α, hα⟩ := GlobalTheory.T.lattice_stabilizer_equiv_automorphisms E Ψ j j' n g Λ F C
  refine ⟨{ h := C.h, e := C.e, e_inj := C.e_inj, e_smul := C.e_smul, Dn := C.Dn, integral := C.integral, orth := C.orth,
            M := M, κ := 2 * C.c, κ_pos := by have := C.c_pos; positivity, π := π, π_cont := ?_, π_range := ?_,
            π_fibre := hfib2, len := ?_, α := α, α_eq := hα, α_act := ?_, act := ?_ }⟩
  · have : π = fun a => Y (moebBall F.q (u a) 0) := funext hπY
    rw [this]
    exact hY.continuousOn.comp_continuous hucont hmem
  · ext t
    constructor
    · rintro ⟨a, rfl⟩
      exact (hπ a).1
    · intro ht
      exact hsurj t ht
  · intro a x
    rw [GlobalTheory.T.normSq_eq_adapted_frame_sum E Ψ j j' n g Λ F C _ _ (hform _) (radπ a) x, hMlen a x]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [aCinv, ← Matrix.mulVec_mulVec, star_mulVec_dot]
  · intro γ a
    obtain ⟨k₁, hk₁⟩ := (hπ a).2
    obtain ⟨k₂, hk₂⟩ := (hπ (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ * a)).2
    refine ⟨k₁.trans k₂.symm, fun x => ?_⟩
    have e1 : (rot (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ * a)).P ((α γ).1 x) = (rot a).P x := by
      rw [rP, rP]
      congr 1
      funext τ
      have hv : C.vec ((α γ).1 x) τ = C.tm (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ) τ *ᵥ C.vec x τ := by
        rw [GlobalTheory.T.archimedean_action_on_lattice_vectors E Ψ j j' n g Λ F C]
        funext i
        show embOf (F.σ τ) (C.e ((α γ).1 x) i) = _
        rw [hα]
      rw [hv, Matrix.mulVec_mulVec, ← hmul, _root_.mul_inv_rev, inv_mul_cancel_right]
    have e2 := hk₂ ((α γ).1 x)
    have e3 := hk₁ x
    simp only [LinearEquiv.coe_one, id_eq] at e2 e3
    rw [e1, e3] at e2
    simp only [LinearEquiv.trans_apply]
    rw [e2, LinearEquiv.symm_apply_apply]
  · intro a₀
    obtain ⟨hm1, hm2, G₂, hG₂, hpot₂⟩ := GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n F.q (u a₀) (uU a₀)
    have hZm : Set.MapsTo Z (ballDom F.q) (ballDom F.q) := hbij.mapsTo
    have hYm : Set.MapsTo Y (ballDom F.q) (ballDom F.q) := fun t ht => (hYZ t ht).1
    have hAm : Set.MapsTo (fun t => Y (moebBall F.q (u a₀) (Z t))) (ballDom F.q) (ballDom F.q) := fun t ht =>
      hYm (hm2 (hZm ht))
    have hAd : DifferentiableOn ℂ (fun t => Y (moebBall F.q (u a₀) (Z t))) (ballDom F.q) :=
      hY.comp (hm1.comp hZ hZm) (hm2.comp hZm)
    refine ⟨fun t => Y (moebBall F.q (u a₀) (Z t)),
      fun t => G₁ t + G₂ (Z t) - G₁ (Y (moebBall F.q (u a₀) (Z t))), hAd,
      (hG₁.add (hG₂.comp hZ hZm)).sub (hG₁.comp hAd hAm), ?_, ?_⟩
    · intro a
      show π (a₀ * a) = Y (moebBall F.q (u a₀) (Z (π a)))
      rw [hπY (a₀ * a), hZπ a, ← GlobalTheory.T.ball_mobius_mul Ψ j j' n F.q (u a₀) (u a) (uU a₀) (uU a) 0 h0]
      congr 2
      funext τ
      exact uMul a₀ a τ
    · intro t ht
      have hs := hZm ht
      have hA := hAm ht
      have e1 := hpot _ hA
      have e2 : Z (Y (moebBall F.q (u a₀) (Z t))) = moebBall F.q (u a₀) (Z t) := (hYZ _ (hm2 hs)).2.1
      rw [e2, hpot₂ _ hs, hpot t ht] at e1
      simp only [Complex.add_re, Complex.sub_re]
      linarith

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGroupDictionaryStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_group_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ), Nonempty (GroupDict F) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.groupDict_nonempty | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.groupDict_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.groupDict_nonempty <;> assumption)
end
