module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.LowestKTypeIntertwinerExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.NormPsiGen
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.SchurOrthogonalityWhittaker
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.MeasurableEmbeddingLeftMulOfIsUnit
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

variable {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem measurableEmbedding_leftMul_of_isUnit {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : IsUnit g) :
    MeasurableEmbedding (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) g) := by
  obtain ⟨u, rfl⟩ := hg
  let e : Formalism.QuantumDeterminants.Mt k r ≃ₜ Formalism.QuantumDeterminants.Mt k r :=
    { toFun := Formalism.QuantumDeterminants.lmulM (u : Matrix _ _ ℂ)
      invFun := Formalism.QuantumDeterminants.lmulM ((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ)
      left_inv := fun x => by
        change ((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) * ((u : Matrix _ _ ℂ) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun x => by
        change (u : Matrix _ _ ℂ) * (((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      continuous_toFun := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      continuous_invFun := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id }
  exact e.toMeasurableEquiv.measurableEmbedding

theorem adjoint_comp_self_of_isometry (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) :
    (ContinuousLinearMap.adjoint A).comp A = 1 := by
  let L : V →ₗᵢ[ℂ] V := { toLinearMap := (A : V →ₗ[ℂ] V), norm_map' := hA }
  ext v
  refine ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  exact L.inner_map_map y v

theorem opNorm_le_one_of_isometry_alt (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) : ‖A‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hA, one_mul]

theorem schur_orthogonality_unitary_rep (G : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) [IsProbabilityMeasure μ]
    (hG0 : μ {x | Matrix.of x ∉ G} = 0) (hGu : ∀ g ∈ G, IsUnit g)
    (hinv : ∀ g ∈ G, μ.map (Formalism.QuantumDeterminants.lmulM g) = μ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (V →L[ℂ] V))
    (hmul : ∀ g ∈ G, ∀ h ∈ G, σ (g * h) = σ g * σ h) (hunit : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ V, (∀ g ∈ G, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hmeas : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => σ (Matrix.of x)) μ) [Nontrivial V]
    (u u' v v' : V) :
    ∫ x, ⟪v', σ (Matrix.of x) u⟫_ℂ * ⟪σ (Matrix.of x) u', v⟫_ℂ ∂μ =
      ⟪v', v⟫_ℂ * ⟪u', u⟫_ℂ / (Module.finrank ℂ V : ℂ) := by
  classical
  set A : V →L[ℂ] V := (innerSL ℂ u').smulRight u with hA
  set F : Formalism.QuantumDeterminants.Mt k r → (V →L[ℂ] V) := fun x =>
    (σ (Matrix.of x)).comp (A.comp (ContinuousLinearMap.adjoint (σ (Matrix.of x)))) with hF
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ G := by
    rw [ae_iff]; simpa using hG0
  have hFm : AEStronglyMeasurable F μ := by
    have hc : Continuous (fun S : V →L[ℂ] V => S.comp (A.comp (ContinuousLinearMap.adjoint S))) :=
      continuous_id.clm_comp (continuous_const.clm_comp
        (ContinuousLinearMap.adjoint : (V →L[ℂ] V) ≃ₗᵢ⋆[ℂ] (V →L[ℂ] V)).continuous)
    exact hc.comp_aestronglyMeasurable hmeas
  have hFb : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖A‖ := hae.mono fun x hx => by
    have h1 := opNorm_le_one_of_isometry_alt _ (hunit _ hx)
    have h2 : ‖ContinuousLinearMap.adjoint (σ (Matrix.of x))‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact h1
    calc ‖F x‖ ≤ ‖σ (Matrix.of x)‖ * (‖A‖ * ‖ContinuousLinearMap.adjoint (σ (Matrix.of x))‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖A‖ * 1) := by gcongr
      _ = ‖A‖ := by ring
  have hFi : Integrable F μ := Integrable.of_bound hFm ‖A‖ hFb
  have hFzi : ∀ z, Integrable (fun x => F x z) μ := fun z => hFi.apply_continuousLinearMap z
  set B : V →L[ℂ] V := ∫ x, F x ∂μ with hB
  have happ : ∀ z, B z = ∫ x, F x z ∂μ := fun z => ContinuousLinearMap.integral_apply hFi z
  have hadj : ∀ g ∈ G, (ContinuousLinearMap.adjoint (σ g)).comp (σ g) = 1 :=
    fun g hg => adjoint_comp_self_of_isometry _ (hunit g hg)
  have hcomm : ∀ g ∈ G, ∀ z, σ g (B z) = B (σ g z) := by
    intro g hg z
    rw [happ, happ, ← ContinuousLinearMap.integral_comp_comm _ (hFzi z)]
    have key : ∀ᵐ x ∂μ, σ g (F x z) = F (Formalism.QuantumDeterminants.lmulM g x) (σ g z) := hae.mono fun x hx => by
      have e : Matrix.of (Formalism.QuantumDeterminants.lmulM g x) = g * Matrix.of x := rfl
      simp only [hF, e, hmul g hg _ hx]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]
      simp only [ContinuousLinearMap.comp_apply]
      have := congrArg (fun T : V →L[ℂ] V => T z) (hadj g hg)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
      rw [this]
    rw [integral_congr_ae key]
    conv_rhs => rw [← hinv g hg]
    rw [(measurableEmbedding_leftMul_of_isUnit (hGu g hg)).integral_map]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ z, B z = c • z := by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (B : Module.End ℂ V)
    refine ⟨c, fun z => ?_⟩
    have hS : ∀ g ∈ G, ∀ v ∈ Module.End.eigenspace (B : Module.End ℂ V) c,
        σ g v ∈ Module.End.eigenspace (B : Module.End ℂ V) c := by
      intro g hg v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      change B (σ g v) = c • σ g v
      rw [← hcomm g hg]
      change σ g ((B : Module.End ℂ V) v) = c • σ g v
      rw [hv, map_smul]
    rcases hirr _ hS with h | h
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have hv1 := hv.apply_eq_smul
      have hv0 := hv.2
      have : v ∈ Module.End.eigenspace (B : Module.End ℂ V) c := Module.End.mem_eigenspace_iff.2 hv1
      rw [h, Submodule.mem_bot] at this
      exact hv0 this
    · have : z ∈ Module.End.eigenspace (B : Module.End ℂ V) c := h ▸ Submodule.mem_top
      exact Module.End.mem_eigenspace_iff.1 this
  have hd0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have htr : c * (Module.finrank ℂ V : ℂ) = ⟪u', u⟫_ℂ := by
    let tr : (V →L[ℂ] V) →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ))
    have htrv : ∀ T : V →L[ℂ] V, tr T = LinearMap.trace ℂ V (T : V →ₗ[ℂ] V) := fun T => rfl
    have h1 : tr B = ∫ x, tr (F x) ∂μ := (ContinuousLinearMap.integral_comp_comm tr hFi).symm
    have h2 : ∀ᵐ x ∂μ, tr (F x) = ⟪u', u⟫_ℂ := hae.mono fun x hx => by
      rw [htrv]
      have e1 : ((F x : V →L[ℂ] V) : V →ₗ[ℂ] V) =
          ((σ (Matrix.of x)).comp A : V →ₗ[ℂ] V) ∘ₗ
            (ContinuousLinearMap.adjoint (σ (Matrix.of x)) : V →ₗ[ℂ] V) := rfl
      rw [e1, LinearMap.trace_comp_comm']
      have e2 : (ContinuousLinearMap.adjoint (σ (Matrix.of x)) : V →ₗ[ℂ] V) ∘ₗ
          ((σ (Matrix.of x)).comp A : V →ₗ[ℂ] V) = (A : V →ₗ[ℂ] V) := by
        have := hadj _ hx
        ext y
        have h3 := congrArg (fun T : V →L[ℂ] V => T (A y)) this
        simpa using h3
      rw [e2]
      have e3 : (A : V →ₗ[ℂ] V) = ((innerSL ℂ u' : V →L[ℂ] ℂ) : V →ₗ[ℂ] ℂ).smulRight u := by
        ext y; rfl
      rw [e3, LinearMap.trace_smulRight]
      rfl
    have h3 : tr B = c * (Module.finrank ℂ V : ℂ) := by
      have eB : B = c • (1 : V →L[ℂ] V) := by ext z; simp [hc z]
      rw [htrv, eB]
      simp [LinearMap.trace_one]
    rw [← h3, h1, integral_congr_ae h2, integral_const]
    simp
  have hfin : ⟪v', B v⟫_ℂ = ∫ x, ⟪v', σ (Matrix.of x) u⟫_ℂ * ⟪σ (Matrix.of x) u', v⟫_ℂ ∂μ := by
    rw [happ, ← integral_inner (hFzi v)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF, hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      map_smul, inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
    ring
  rw [← hfin, hc, inner_smul_right]
  have hc' : c = ⟪u', u⟫_ℂ / (Module.finrank ℂ V : ℂ) := by
    rw [← htr]; field_simp
  rw [hc']
  ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS Formalism.QuantumDeterminants

variable {k r : ℕ}

theorem clm_continuousOn {X : Type*} [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (σ : X → (V →L[ℂ] V)) (s : Set X)
    (h : ∀ v, ContinuousOn (fun g => σ g v) s) : ContinuousOn σ s := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_clm_apply.2 fun v => continuousOn_iff_continuous_domRestrict.1 (h v)

theorem isClosed_UW : IsClosed {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)} := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have e : {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)} =
      {x | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} ∩
        ((⋂ a : Fin r, ({x | Matrix.of x *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {x | Matrix.of x *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩
          {x | Matrix.of x *ᵥ z0 k r = z0 k r}) := by
    ext x
    simp only [UWset, UH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter (isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc)
    continuous_const) (IsClosed.inter (isClosed_iInter fun a => IsClosed.inter ?_ ?_) ?_)
  · exact isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const

theorem blk_cont : Continuous (fun x : Mt k r => StandardBasisEmbedding.blk (k := k) (r := r) (Matrix.of x)) := by
  refine continuous_pi fun q => continuous_pi fun q' => ?_
  exact (continuous_apply _).comp (continuous_apply _)

theorem uw_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UWset k r (z0 k r)) :
    g⁻¹ = Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) ∧ IsUnit g := by
  have hu := StandardBasisEmbedding.blk_unitary hg
  have h1 : g * Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) = 1 := by
    have e := StandardBasisEmbedding.eq_blockW hg
    rw [show g * Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) =
        Formalism.MainNotions.S.blockW k r (StandardBasisEmbedding.blk g) * Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) from by rw [← e]]
    rw [← StandardBasisEmbedding.blockW_mul, Unitary.mul_star_self_of_mem hu, StandardBasisEmbedding.blockW_one]
  exact ⟨Matrix.inv_eq_right_inv h1, ⟨⟨g, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩⟩

theorem schur_orthogonality_whittaker {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {u : Fin k → ℝ}
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Vp →L[ℂ] Vp)) {ξ : Vp}
    {μW : Measure (Mt k r)} (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P)
    (hπ : Formalism.MainNotions.S.IsHCTypeU k u (fun h => π (Formalism.MainNotions.S.blockW k r h))) (hξn : ‖ξ‖ = 1)
    (hξ : Formalism.MainNotions.S.IsWtOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) (fun h => π (Formalism.MainNotions.S.blockW k r h))
      (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) ξ)
    (hΛ : ∀ a : Fin k, Λ ⟨a.val, by omega⟩ = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u a)
    (hμW : Formalism.MainNotions.S.IsHaarOn (UWset k r (z0 k r)) μW) (hμ1 : μW Set.univ = 1) (Y : T.V) :
    ∫ x, ⟪ξ, π (Matrix.of x)⁻¹ ξ⟫_ℂ * ⟪T.w, HW.torepSig T (P * Matrix.of x * P⁻¹) Y⟫_ℂ ∂μW =
      (Module.finrank ℂ Vp : ℂ)⁻¹ * ⟪T.w, Y⟫_ℂ := by
  classical
  set π' : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp) := fun h => π (Formalism.MainNotions.S.blockW k r h) with hπ'
  have hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true := fun a ha => cay_eps hP hW a ha
  have hΛ' : ∀ q : Fin k, Λ (fI k r q) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u q := fun q => hΛ q
  have : FiniteDimensional ℂ Vp := hπ.2.1
  have : Nontrivial Vp := hπ.1
  have : IsProbabilityMeasure μW := ⟨hμ1⟩
  obtain ⟨U, α, hint, hα⟩ := lowestKType_intertwiner_exists T hε hΛ' π' hπ hξ
  have hUR := hπ.2.2.1
  have hπadj : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ a b : Vp, ⟪a, π' h b⟫_ℂ = ⟪π' (star h) a, b⟫_ℂ := by
    intro h hh a b
    have hs : star h ∈ Matrix.unitaryGroup (Fin k) ℂ := Unitary.star_mem hh
    have hinv : π' (star h) (π' h b) = b := by
      have := hUR.1.2 _ (unit_uj hs) _ (unit_uj hh)
      rw [Unitary.star_mul_self_of_mem hh, hUR.1.1] at this
      have := congrArg (fun A : Vp →L[ℂ] Vp => A b) this
      simpa using this.symm
    let Lm : Vp →ₗᵢ[ℂ] Vp := { toLinearMap := (π' (star h) : Vp →ₗ[ℂ] Vp), norm_map' := hUR.2.1 _ (unit_uj hs) }
    have := Lm.inner_map_map a (π' h b)
    change ⟪π' (star h) a, π' (star h) (π' h b)⟫_ℂ = _ at this
    rw [hinv] at this
    exact this.symm
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hα
    have : U ξ = 0 := Subtype.ext hα
    rw [LinearIsometryEquiv.map_eq_zero_iff] at this
    rw [this, norm_zero] at hξn
    exact zero_ne_one hξn
  set η : Vp := α⁻¹ • ξ with hηdef
  have hη : (U η : T.V) = T.w := by
    rw [hηdef, map_smul, Submodule.coe_smul, hα, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  set Y' : Vp := U.symm ((spanW (k := k) (r := r) T).orthogonalProjectionOnto Y) with hY'
  have hproj : ∀ s : spanW (k := k) (r := r) T,
      ⟪(s : T.V), Y⟫_ℂ = ⟪s, (spanW (k := k) (r := r) T).orthogonalProjectionOnto Y⟫_ℂ := by
    intro s
    have h0 : ⟪(s : T.V), Y - ((spanW (k := k) (r := r) T).orthogonalProjectionOnto Y : T.V)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal s.2 ((spanW (k := k) (r := r) T).sub_starProjection_mem_orthogonal Y)
    rw [inner_sub_right, sub_eq_zero] at h0
    rw [h0]
    rfl
  have hUY : ∀ a : Vp, ⟪(U a : T.V), Y⟫_ℂ = ⟪a, Y'⟫_ℂ := by
    intro a
    rw [hproj, ← U.inner_map_map a Y', hY', U.apply_symm_apply]
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r (z0 k r) := by
    rw [ae_iff]; simpa using hμW.2.2.1
  have hpt : ∀ᵐ x ∂μW, ⟪ξ, π (Matrix.of x)⁻¹ ξ⟫_ℂ * ⟪T.w, HW.torepSig T (P * Matrix.of x * P⁻¹) Y⟫_ℂ =
      ⟪η, π (Matrix.of x) Y'⟫_ℂ * ⟪π (Matrix.of x) ξ, ξ⟫_ℂ := hae.mono fun x hx => by
    have hu : StandardBasisEmbedding.blk (Matrix.of x) ∈ Matrix.unitaryGroup (Fin k) ℂ := StandardBasisEmbedding.blk_unitary hx
    have hx' : Matrix.of x = Formalism.MainNotions.S.blockW k r (StandardBasisEmbedding.blk (Matrix.of x)) := StandardBasisEmbedding.eq_blockW hx
    have h1 : π (Matrix.of x)⁻¹ = π' (star (StandardBasisEmbedding.blk (Matrix.of x))) := by rw [(uw_inv hx).1]
    have h2 : HW.torepSig T (P * Matrix.of x * P⁻¹) = rhoK (k := k) (r := r) T (StandardBasisEmbedding.blk (Matrix.of x)) := by
      rw [rhoK, ← cay_kE hP hW, ← hx']
    have h3 : π (Matrix.of x) = π' (StandardBasisEmbedding.blk (Matrix.of x)) := by
      rw [hπ']; exact congrArg π hx'
    rw [h1, h2, h3]
    rw [rhoK_adj T hε hu, ← hη, hint _ (Unitary.star_mem hu), hUY, ← hπadj _ hu]
    rw [hπadj _ (Unitary.star_mem hu), star_star, mul_comm]
  rw [integral_congr_ae hpt]
  have hmul : ∀ g ∈ UWset k r (z0 k r), ∀ h ∈ UWset k r (z0 k r), π (g * h) = π g * π h := by
    intro g hg h hh
    have e1 := StandardBasisEmbedding.eq_blockW hg
    have e2 := StandardBasisEmbedding.eq_blockW hh
    rw [e1, e2, ← StandardBasisEmbedding.blockW_mul]
    exact hUR.1.2 _ (unit_uj (StandardBasisEmbedding.blk_unitary hg)) _ (unit_uj (StandardBasisEmbedding.blk_unitary hh))
  have hunit : ∀ g ∈ UWset k r (z0 k r), ∀ v, ‖π g v‖ = ‖v‖ := by
    intro g hg v
    rw [StandardBasisEmbedding.eq_blockW hg]
    exact hUR.2.1 _ (unit_uj (StandardBasisEmbedding.blk_unitary hg)) v
  have hirr : ∀ S : Submodule ℂ Vp, (∀ g ∈ UWset k r (z0 k r), ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    exact hπ.2.2.2.2.2.1 S le_top (fun g hg v hv => hS _ (StandardBasisEmbedding.mem_UW hg.1) v hv)
  have hmeas : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)) μW := by
    have hc : ContinuousOn (fun x : Mt k r => π' (StandardBasisEmbedding.blk (Matrix.of x))) {x | Matrix.of x ∈ UWset k r (z0 k r)} :=
      (clm_continuousOn π' _ hUR.2.2).comp blk_cont.continuousOn (fun x hx => unit_uj (StandardBasisEmbedding.blk_unitary hx))
    have h1 := hc.aestronglyMeasurable (μ := μW) isClosed_UW.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)}) hae] at h1
    exact h1.congr (hae.mono fun x hx => (congrArg π (StandardBasisEmbedding.eq_blockW hx)).symm)
  rw [schur_orthogonality_unitary_rep (UWset k r (z0 k r)) μW hμW.2.2.1 (fun g hg => (uw_inv hg).2) (fun g hg => hμW.2.2.2 g hg)
    π hmul hunit hirr hmeas Y' ξ ξ η]
  have e1 : ⟪η, ξ⟫_ℂ = (starRingEnd ℂ) α⁻¹ := by
    rw [hηdef, inner_smul_left, inner_self_eq_norm_sq_to_K, hξn]; simp
  have e2 : ⟪ξ, Y'⟫_ℂ = (starRingEnd ℂ) α * ⟪T.w, Y⟫_ℂ := by
    rw [← hUY, hα, inner_smul_left]
  rw [e1, e2, map_inv₀]
  have hc0 : (starRingEnd ℂ) α ≠ 0 := by simpa using hα0
  field_simp

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS Formalism.QuantumDeterminants

variable {k r : ℕ}

theorem inUJ_kmul {ε : Fin (2 * r + k + 1) → Bool} {κ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hκ : κ ∈ Kset ε) : inUJ ε (κ * g) ↔ inUJ ε g := by
  have hJ : κᴴ * Jm ε * κ = Jm ε := HW.torep_inUJ ε hκ
  unfold inUJ
  rw [Matrix.conjTranspose_mul]
  have e : gᴴ * κᴴ * Jm ε * (κ * g) = gᴴ * (κᴴ * Jm ε * κ) * g := by simp only [Matrix.mul_assoc]
  rw [e, hJ]

theorem psiM_zero {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : ¬ inUJ ε g) :
    S7.PsiM T μ g = 0 := by
  unfold S7.PsiM
  rw [dite_eq_right]
  rintro ⟨k', X, hX, rfl⟩
  exact hg (S7.inUJ_kexp k' hX)

theorem psiM_K {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) {κ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hκ : κ ∈ Kset ε)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    S7.PsiM T μ (κ * g) = HW.torepSig T κ * S7.PsiM T μ g := by
  by_cases hg : inUJ ε g
  · have h := S7.psiM_equiv T μ (HW.torepK ε hκ) 1 hg
    rw [HW.toMK_torepK] at h
    have h1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
    rw [h1, Matrix.mul_one] at h
    rw [h, HW.torepSig_of_mem T hκ]
    have : T.op 1 = 1 := by simp [S7.KType.op]
    rw [this, mul_one]
  · rw [psiM_zero T μ hg, psiM_zero T μ (fun h => hg ((inUJ_kmul hκ).1 h)), mul_zero]

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) : Continuous (Formalism.MainNotions.S.psiGen k r z c) := by
  unfold Formalism.MainNotions.S.psiGen
  have h : ∀ a : Fin r, Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      Formalism.MainNotions.S.ellA k r z g a) := by
    intro a
    unfold Formalism.MainNotions.S.ellA
    split_ifs
    · exact (continuous_apply _).comp (continuous_apply _)
    · simp only [Matrix.mulVec, dotProduct]
      exact continuous_finsetSum _ fun j _ =>
        (continuous_id.matrix_elem _ j).mul continuous_const
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (h a)))))

theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ‖Formalism.MainNotions.S.psiGen k r z c g‖ = 1 := by
  unfold Formalism.MainNotions.S.psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem coef_meas {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) (hcont : ContinuousOn (S7.PsiM T μ) (UJset ε)) (v w : T.V) :
    Measurable (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) := by
  classical
  set s : Set (Mt k r) := {M | inUJ ε (Matrix.of M)}
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have hs : IsClosed s :=
    isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const
  have hΦ : ContinuousOn (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) s := by
    have h1 : ContinuousOn (fun M : Mt k r => S7.PsiM T μ (Matrix.of M)) s :=
      hcont.comp hc.continuousOn (fun M hM => hM)
    exact continuousOn_const.inner (h1.clm_apply continuousOn_const)
  have he : (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) =
      s.piecewise (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) (fun _ => 0) := by
    funext M
    by_cases hM : M ∈ s
    · rw [Set.piecewise_eq_of_mem _ _ _ hM]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hM, psiM_zero T μ hM]; simp
  rw [he]
  exact hΦ.measurable_piecewise continuousOn_const hs.measurableSet

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS Formalism.QuantumDeterminants SchurOrthogonalityLemmas

theorem b7b : WhittakerSchurOrthogonality := by
  intro k r ε Λ T μ P u c Vp _ _ _ π ξ μW μN _ hP hW hπ hξn hξ hΛ hμW hμ1 _ hcont hint
  classical
  set ψ := Formalism.MainNotions.S.psiGen k r (z0 k r) c with hψ
  set π' : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp) := fun h => π (Formalism.MainNotions.S.blockW k r h) with hπ'
  have hUR := hπ.2.2.1
  have : FiniteDimensional ℂ Vp := hπ.2.1
  have : IsProbabilityMeasure μW := ⟨hμ1⟩
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r (z0 k r) := by
    rw [ae_iff]; simpa using hμW.2.2.1
  have haeP : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r (z0 k r) :=
    Measure.quasiMeasurePreserving_fst.ae hae
  set F : Mt k r × Mt k r → Vp := fun p =>
    psiCoef T μ P T.w T.w ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1)) •
      chiInv ψ π (Matrix.of p.1) (Matrix.of p.2) ξ with hF
  have hA : aaFun T μ P μW μN ψ π T.w T.w ξ 1 1 = ∫ p, F p ∂(μW.prod μN) := rfl
  have hK : ∀ h : Mt k r, Matrix.of h ∈ UWset k r (z0 k r) → P * Matrix.of h * P⁻¹ ∈ Kset ε := by
    intro h hh
    rw [StandardBasisEmbedding.eq_blockW hh, cay_kE hP hW]
    exact kE_mem_Kset (fun a ha => cay_eps hP hW a ha) (StandardBasisEmbedding.blk_unitary hh)
  have hPsi : ∀ h m : Mt k r, Matrix.of h ∈ UWset k r (z0 k r) →
      S7.PsiM T μ (P * (Matrix.of h * Matrix.of m) * P⁻¹) =
        HW.torepSig T (P * Matrix.of h * P⁻¹) * S7.PsiM T μ (P * Matrix.of m * P⁻¹) := by
    intro h m hh
    have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
    have e : P * (Matrix.of h * Matrix.of m) * P⁻¹ = (P * Matrix.of h * P⁻¹) * (P * Matrix.of m * P⁻¹) := by
      have : (P * Matrix.of h * P⁻¹) * (P * Matrix.of m * P⁻¹) =
          P * Matrix.of h * (P⁻¹ * P) * Matrix.of m * P⁻¹ := by simp only [Matrix.mul_assoc]
      rw [this, Matrix.nonsing_inv_mul _ hu]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [e, psiM_K T μ (hK h hh)]
  have hunit : ∀ g ∈ UWset k r (z0 k r), ∀ v, ‖π g v‖ = ‖v‖ := by
    intro g hg v
    rw [StandardBasisEmbedding.eq_blockW hg]
    exact hUR.2.1 _ (unit_uj (StandardBasisEmbedding.blk_unitary hg)) v
  have hinvG : ∀ h : Mt k r, Matrix.of h ∈ UWset k r (z0 k r) → (Matrix.of h)⁻¹ ∈ UWset k r (z0 k r) := by
    intro h hh
    rw [(uw_inv hh).1]
    exact StandardBasisEmbedding.mem_UW (Unitary.star_mem (StandardBasisEmbedding.blk_unitary hh))
  have hFm : AEStronglyMeasurable F (μW.prod μN) := by
    have hc0 : Continuous (fun p : Mt k r × Mt k r =>
        (P * ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1)) * P⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
      fun_prop
    have hc1 : Continuous (fun p : Mt k r × Mt k r =>
        (Matrix.of.symm (P * ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1)) * P⁻¹) : Mt k r)) := by
      exact hc0
    have h1 : Measurable (fun p : Mt k r × Mt k r =>
        psiCoef T μ P T.w T.w ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1))) := by
      exact (coef_meas T μ hcont T.w T.w).comp hc1.measurable
    have h2 : Continuous (fun p : Mt k r × Mt k r => star (ψ (Matrix.of p.2))) :=
      continuous_star.comp ((psiGen_cont _ _).comp continuous_snd)
    have h3 : AEStronglyMeasurable (fun p : Mt k r × Mt k r => π (Matrix.of p.1)⁻¹ ξ) (μW.prod μN) := by
      have hc : ContinuousOn (fun x : Mt k r => π' (star (StandardBasisEmbedding.blk (Matrix.of x))) ξ)
          {x | Matrix.of x ∈ UWset k r (z0 k r)} :=
        (hUR.2.2 ξ).comp blk_cont.star.continuousOn
          (fun x hx => unit_uj (Unitary.star_mem (StandardBasisEmbedding.blk_unitary hx)))
      have h0 := hc.aestronglyMeasurable (μ := μW) isClosed_UW.measurableSet
      rw [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)}) hae] at h0
      have h0' : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)⁻¹ ξ) μW :=
        h0.congr (hae.mono fun x hx => by dsimp only; rw [(uw_inv hx).1])
      exact h0'.comp_fst
    exact h1.aestronglyMeasurable.smul (h2.aestronglyMeasurable.smul h3)
  have hFb : ∀ᵐ p ∂(μW.prod μN), ‖F p‖ ≤ ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ := haeP.mono fun p hp => by
    simp only [hF, chiInv, psiCoef, inv_one, Matrix.one_mul, Matrix.mul_one]
    rw [hPsi _ _ hp, norm_smul, norm_smul, norm_star, hψ, norm_psiGen, one_mul, hunit _ (hinvG _ hp), hξn, mul_one]
    have hA1 : ‖HW.torepSig T (P * Matrix.of p.1 * P⁻¹)‖ ≤ 1 :=
      opNorm_le_one_of_isometry_alt _ ((HW.torep_isURepOn T).2.1 _ (hK _ hp))
    calc ‖⟪T.w, (HW.torepSig T (P * Matrix.of p.1 * P⁻¹) * S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)) T.w⟫_ℂ‖
        ≤ ‖T.w‖ * ‖(HW.torepSig T (P * Matrix.of p.1 * P⁻¹) * S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)) T.w‖ :=
          norm_inner_le_norm _ _
      _ ≤ 1 * (‖HW.torepSig T (P * Matrix.of p.1 * P⁻¹) * S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ * 1) := by
          rw [T.w_norm]
          gcongr
          calc _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
            _ = _ := by rw [T.w_norm]
      _ ≤ ‖HW.torepSig T (P * Matrix.of p.1 * P⁻¹)‖ * ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ := by
          rw [one_mul, mul_one]; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ := by gcongr
      _ = _ := one_mul _
  have hFi : Integrable F (μW.prod μN) := by
    have hφ : Integrable (fun p : Mt k r × Mt k r => ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖) (μW.prod μN) := by
      have := (integrable_const (1 : ℝ) (μ := μW)).mul_prod hint
      simpa using this
    exact hφ.mono' hFm hFb
  rw [hA, ← integral_inner hFi ξ, integral_prod_symm _ (hFi.const_inner ξ)]
  have hin : ∀ m : Mt k r, ∫ h, ⟪ξ, F (h, m)⟫_ℂ ∂μW =
      (Module.finrank ℂ Vp : ℂ)⁻¹ * (psiCoef T μ P T.w T.w (Matrix.of m) * starRingEnd ℂ (ψ (Matrix.of m))) := by
    intro m
    have hpt : ∀ᵐ h ∂μW, ⟪ξ, F (h, m)⟫_ℂ = starRingEnd ℂ (ψ (Matrix.of m)) *
        (⟪ξ, π (Matrix.of h)⁻¹ ξ⟫_ℂ * ⟪T.w, HW.torepSig T (P * Matrix.of h * P⁻¹)
          (S7.PsiM T μ (P * Matrix.of m * P⁻¹) T.w)⟫_ℂ) := hae.mono fun h hh => by
      simp only [hF, chiInv, psiCoef, inv_one, Matrix.one_mul, Matrix.mul_one, inner_smul_right]
      have e : ∀ (A B : T.V →L[ℂ] T.V) (v : T.V), (A * B) v = A (B v) := fun _ _ _ => rfl
      rw [hPsi _ _ hh, e, show star (ψ (Matrix.of m)) = starRingEnd ℂ (ψ (Matrix.of m)) from rfl]
      ring
    rw [integral_congr_ae hpt, integral_const_mul, schur_orthogonality_whittaker T π hP hW hπ hξn hξ hΛ hμW hμ1]
    simp only [psiCoef]
    ring
  simp only [hin]
  rw [integral_const_mul]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
