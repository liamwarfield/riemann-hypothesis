module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalleyStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTopStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfSUnitLocalSquareFiniteRealPlaces
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem mem_normSub_of_isSquare {F L : Type} [Field F] [CharZero F] [Field L] (φ : F →+* L)
    (δ : Fˣ) (h : IsSquare (φ (δ : F))) (x : Fˣ) : x ∈ normSub φ (δ : F) := by
  obtain ⟨c, hc⟩ := h
  have hδ : φ (δ : F) ≠ 0 := (map_ne_zero φ).mpr δ.ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hc
    exact hδ hc
  have h2 : (2 : L) ≠ 0 := by
    have : φ 2 ≠ 0 := (map_ne_zero φ).mpr two_ne_zero
    rwa [map_ofNat] at this
  rw [mem_normSub]
  refine ⟨(φ (x : F) + 1) / 2, (φ (x : F) - 1) / (2 * c), ?_⟩
  rw [hc]
  field_simp
  ring

theorem isSquare_of_mem_locSq : ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ → ∀ y ∈ sUnits F (S ∪ T), y ∈ locSq F S → IsSquare (y : F) := by
  intro F _ _ _ S T hS hT y hy hloc
  by_contra hns
  apply GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top F y (S ∪ T) (hS.mono Finset.subset_union_left) hy hns
  rw [eq_top_iff, ← hT]
  refine sup_le_sup_left ?_ _
  intro x hx
  rw [finSq, Subgroup.mem_iInf] at hx
  rw [locSq, Subgroup.mem_inf, finSq, Subgroup.mem_iInf, Subgroup.mem_iInf] at hloc
  obtain ⟨hlocS, hlocR⟩ := hloc
  rw [locNorm, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_iInf]
  refine ⟨fun v => ?_, fun σ => ?_⟩
  · rw [Subgroup.mem_iInf]
    intro hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · exact mem_normSub_of_isSquare _ y
        ((mem_sqSub _ _).mp (Subgroup.mem_iInf.mp (hlocS v) hvS)) x
    · exact sqSub_le_normSub _ _ (Subgroup.mem_iInf.mp (hx v) hvT)
  · exact mem_normSub_of_isSquare _ y ((mem_sqSub _ _).mp (hlocR σ)) x

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotIsSquareAdicCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotIsSquareAdicCompletion
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem normSub_eq_top_of_isSquare_image {F L : Type} [Field F] [Field L] [CharZero L]
    (φ : F →+* L) (δ : F) (hδ : δ ≠ 0) (h : IsSquare (φ δ)) (x : Fˣ) : x ∈ normSub φ δ := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hδ ((map_eq_zero φ).1 (by simpa using hr))
  refine ⟨(φ x + 1) / 2, (φ x - 1) / (2 * r), ?_⟩
  rw [hr]
  field_simp
  ring

theorem exists_not_mem_not_isSquare_completion :
    ∀ (F : Type) [Field F] [NumberField F] (u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), u ≠ 0 → ¬ IsSquare u → ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  classical
  intro F _ _ u S₀ hu hns
  by_contra hcon
  push Not at hcon
  have hle : ∀ S, locNorm F u S₀ ≤ locNorm F u S := by
    intro S x hx
    rw [locNorm, Subgroup.mem_inf] at hx ⊢
    refine ⟨?_, hx.2⟩
    have h1 := hx.1
    simp only [Subgroup.mem_iInf] at h1 ⊢
    intro v _
    by_cases hv : v ∈ S₀
    · exact h1 v hv
    · haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      exact normSub_eq_top_of_isSquare_image _ u hu (hcon v hv) x
  have hidx := (GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension F u S₀ hu).1
  haveI : (locNorm F u S₀).FiniteIndex := ⟨hidx⟩
  haveI : Fintype (Fˣ ⧸ locNorm F u S₀) := Fintype.ofFinite _
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F
    (insert (Units.mk0 u hu)
      (Finset.univ.image (fun q : Fˣ ⧸ locNorm F u S₀ => q.out))) S₀
  obtain ⟨S, hS, hadm⟩ := exists_admissible_superset_finite_places F S₁
  have hX := hS₁ S hS
  refine GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top F (Units.mk0 u hu) S hadm (hX _ (Finset.mem_insert_self _ _)) hns ?_
  rw [eq_top_iff]
  intro x _
  have hy : (QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out ∈ sUnits F S :=
    hX _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hz : ((QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out)⁻¹ * x ∈ locNorm F u S₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have hx : x = (QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out *
      (((QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out)⁻¹ * x) := by
    rw [mul_inv_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup hy (hle S hz)

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotIsSquareAdicCompletionStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_not_isSquare_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), u ≠ 0 → ¬ IsSquare u → ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  first | exact @GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion | exact GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion | (intros; apply GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTranspose
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleMatrixSetTransposeImage
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleMatrixSetTransposeImage
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private noncomputable def dotPerp (U : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) :=
  U.dualAnnihilator.comap (dotProductEquiv ℂ ι).toLinearMap

private theorem mem_dotPerp (U : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) :
    v ∈ dotPerp U ↔ ∀ w ∈ U, v ⬝ᵥ w = 0 := by
  simp [dotPerp, Submodule.mem_dualAnnihilator, dotProductEquiv]

private theorem dotPerp_isCompl {U U' : Submodule ℂ (ι → ℂ)} (h : IsCompl U U') :
    IsCompl (dotPerp U) (dotPerp U') :=
  (Submodule.orderIsoMapComap (dotProductEquiv ℂ ι)).symm.isCompl (Subspace.isCompl_dualAnnihilator h)

private theorem dotPerp_dotPerp (U : Submodule ℂ (ι → ℂ)) : dotPerp (dotPerp U) = U := by
  ext v
  constructor
  · intro hv
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := U), Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨w, rfl⟩ := (dotProductEquiv ℂ ι).surjective φ
    have h := (mem_dotPerp _ v).1 hv w hφ
    rw [dotProduct_comm] at h
    simpa [dotProductEquiv] using h
  · intro hv
    rw [mem_dotPerp]
    intro w hw
    rw [dotProduct_comm]
    exact (mem_dotPerp _ w).1 hw v hv

private theorem dotPerp_invariant (U : Submodule ℂ (ι → ℂ)) (g : Matrix ι ι ℂ)
    (h : ∀ v ∈ U, g *ᵥ v ∈ U) : ∀ v ∈ dotPerp U, gᵀ *ᵥ v ∈ dotPerp U := by
  intro v hv
  rw [mem_dotPerp] at hv ⊢
  intro w hw
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  exact hv _ (h w hw)

theorem ss_transpose :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), SS Γ → SS (Matrix.transpose '' Γ) := by
  intro ι _ _ Γ hΓ W hW
  obtain ⟨U', hU', hc⟩ := hΓ (dotPerp W) (fun g hg => by
    simpa using dotPerp_invariant W gᵀ (hW _ ⟨g, hg, rfl⟩))
  refine ⟨dotPerp U', ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact dotPerp_invariant U' g (hU' g hg)
  · have := dotPerp_isCompl hc
    rwa [dotPerp_dotPerp] at this

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleMatrixSetTransposeImageStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompletelyReducibleMatrixSet_transpose_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), SS Γ → SS (Matrix.transpose '' Γ) := by
  first | exact @GlobalTheory.ClassFin.ss_transpose | exact GlobalTheory.ClassFin.ss_transpose | (intros; apply GlobalTheory.ClassFin.ss_transpose <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTranspose
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_semisimple_rep_tpow {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]
    (ρ : G →* Matrix ι ι ℂ) (h : SS (Set.range ρ)) (n : ℕ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (r : Representation ℂ G V)
      (b : Module.Basis (Fin n → ι) ℂ V),
      r.IsSemisimpleRepresentation ∧ ∀ g, LinearMap.toMatrix b b (r g) = tpow n (ρ g) := by
  induction n with
  | zero =>
    have hm : ∀ g : G, LinearMap.toMatrix (Pi.basisFun ℂ (Fin 0 → ι)) (Pi.basisFun ℂ (Fin 0 → ι))
        (Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g) = 1 := by
      intro g
      have : Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g = LinearMap.id := by
        ext v; simp
      rw [this, LinearMap.toMatrix_id]
    refine ⟨(Fin 0 → ι) → ℂ, inferInstance, inferInstance, Representation.trivial ℂ G _,
      Pi.basisFun ℂ _, ?_, ?_⟩
    · rw [← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation (Fin 0 → ι) G _ _ (Pi.basisFun ℂ _)]
      intro W _
      obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
      refine ⟨W', ?_, hW'⟩
      rintro _ ⟨g, rfl⟩ v hv
      simpa only [hm, Matrix.one_mulVec] using hv
    · intro g
      rw [hm]
      ext a b
      have : a = b := Subsingleton.elim _ _
      subst this
      simp [tpow]
  | succ n ih =>
    obtain ⟨V, _, _, r, b, hr, hb⟩ := ih
    let r₁ : Representation ℂ G (ι → ℂ) :=
      (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)).toAlgHom.toMonoidHom.comp ρ
    have h₁ : ∀ g, LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (r₁ g) = ρ g := by
      intro g
      change LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (Matrix.toLin' (ρ g)) = ρ g
      rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    have hs₁ : r₁.IsSemisimpleRepresentation := by
      rw [← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation ι G _ _ (Pi.basisFun ℂ _)]
      simpa only [h₁] using h
    haveI : FiniteDimensional ℂ V := Module.Finite.of_basis b
    let e : ι × (Fin n → ι) ≃ (Fin (n + 1) → ι) := Fin.consEquiv fun _ => ι
    refine ⟨(ι → ℂ) ⊗[ℂ] V, inferInstance, inferInstance, r₁.tprod r,
      ((Pi.basisFun ℂ ι).tensorProduct b).reindex e,
      GlobalTheory.T.isSemisimpleRepresentation_tprod_chevalley G _ r₁ V r hs₁ hr, ?_⟩
    intro g
    have ht : LinearMap.toMatrix ((Pi.basisFun ℂ ι).tensorProduct b) ((Pi.basisFun ℂ ι).tensorProduct b)
        ((r₁.tprod r) g) = ρ g ⊗ₖ tpow n (ρ g) := by
      rw [Representation.tprod_apply, TensorProduct.toMatrix_map, h₁, hb]
    ext a c
    have := congrFun (congrFun ht (e.symm a)) (e.symm c)
    rw [LinearMap.toMatrix_apply] at this ⊢
    rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, this]
    simp [e, tpow, Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]

theorem ss_tpow_transpose : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)),
    IsPre Γ → SS Γ → ∀ n : ℕ, SS ((fun g => (tpow n g)ᵀ) '' Γ) := by
  intro ι _ _ Γ hΓ hs n
  obtain ⟨G, _, ρ, rfl⟩ := GlobalTheory.T.exists_group_hom_range_eq_of_isPre ι Γ hΓ
  obtain ⟨V, _, _, r, b, hr, hb⟩ := exists_semisimple_rep_tpow ρ hs n
  have h := GlobalTheory.T.isCompletelyReducibleMatrixSet_transpose_image _ _ ((GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation _ G V r b).2 hr)
  simp only [hb] at h
  rw [← Set.range_comp] at h ⊢
  exact h

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTransposeStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completelyReducible_kroneckerPower_transpose : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ n : ℕ, SS ((fun g => (tpow n g)ᵀ) '' Γ) := by
  first | exact @GlobalTheory.ClassFin.ss_tpow_transpose | exact GlobalTheory.ClassFin.ss_tpow_transpose | (intros; apply GlobalTheory.ClassFin.ss_tpow_transpose <;> assumption)
end
end
