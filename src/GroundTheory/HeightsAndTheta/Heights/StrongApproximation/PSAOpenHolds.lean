module

public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAOpenHolds
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem map_inclA_mem_SU {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by
  obtain ⟨hdet, hform⟩ := hγ
  have hsig : ∀ y : E, sigA c (inclA F E y) = inclA F E (c y) := by
    intro y
    simp [sigA, inclA, Algebra.TensorProduct.map_tmul]
  have hmap : (γ.map (inclA F E)).map (sigA c) = (γ.map c.toRingHom).map (inclA F E) := by
    ext i j
    simp [hsig]
  refine ⟨?_, ?_⟩
  · rw [show (γ.map (inclA F E)).det = inclA F E γ.det from (RingHom.map_det _ _).symm, hdet, map_one]
  · rw [hmap, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hform]

theorem SAOpenHolds.proof (hSA : SAHolds.Statement) (hTop : AETopologicalRing.Statement) :
    SAOpenHolds.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ hdet hiso _ _ Kg hKsub h1 _ hinv hO x hx
  obtain ⟨O, hOopen, hOK⟩ := hO
  have hxdet : IsUnit x.det := by rw [hx.1]; exact isUnit_one

  have hcont : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) :=
    ((hTop F E c h2 hc).2.2.2 N (J.map (inclA F E))).1.comp
      (continuous_const.prodMk continuous_id)
  have hUopen : IsOpen ((fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) ⁻¹' O) :=
    hOopen.preimage hcont
  have h1O : (1 : Matrix (Fin N) (Fin N) (AE F E)) ∈ O := by
    rw [← hOK] at h1; exact h1.1
  have hxU : x ∈ (fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) ⁻¹' O := by
    change x⁻¹ * x ∈ O
    rw [nonsing_inv_mul x hxdet]; exact h1O
  have hcl := hSA F E c h2 hc N J hJ hdet hiso hx
  obtain ⟨_, hyU, ⟨γ, hγ, rfl⟩⟩ := mem_closure_iff.1 hcl _ hUopen hxU
  have hγA := map_inclA_mem_SU c J hγ
  set k := x⁻¹ * γ.map (inclA F E) with hk
  have hkSU : k ∈ SU (sigA c) (J.map (inclA F E)) :=
    mul_mem_SU (inv_mem_SU _ _ hx) hγA
  have hkK : k ∈ Kg := by rw [← hOK]; exact ⟨hyU, hkSU⟩
  have hkdet : IsUnit k.det := by rw [hkSU.1]; exact isUnit_one
  refine ⟨γ, hγ, k⁻¹, hinv k hkK, ?_⟩
  have hxk : x * k = γ.map (inclA F E) := by
    rw [hk, ← Matrix.mul_assoc, mul_nonsing_inv x hxdet, Matrix.one_mul]
  rw [← hxk, Matrix.mul_assoc, mul_nonsing_inv k hkdet, Matrix.mul_one]

end GroundTheory.Heights₂.Heights.StrongApprox
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PHypPairExists
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix ReciprocityTheory.ChartRestriction.G.SA

theorem HypPairExists.proof : HypPairExists.Statement := by
  intro E _ σ hσ h2 N J hJ hdet e he0 hee

  have hw : ∃ j, ∑ i, e i * J i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : e ᵥ* J = 0 := by
      ext j
      simpa [vecMul, dotProduct] using h j
    apply he0
    calc e = e ᵥ* (J * J⁻¹) := by rw [mul_nonsing_inv J hdet, vecMul_one]
      _ = (e ᵥ* J) ᵥ* J⁻¹ := by rw [vecMul_vecMul]
      _ = 0 := by rw [h0, zero_vecMul]
  obtain ⟨j, hj⟩ := hw
  have hsingle : hf σ J e (Pi.single j 1) = ∑ i, e i * J i j := by
    simp only [hf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp

  obtain ⟨a, hea⟩ : ∃ a : Fin N → E, hf σ J e a = 1 :=
    ⟨σ (∑ i, e i * J i j)⁻¹ • Pi.single j 1, by
      rw [hf_smul_right, hsingle, hσ, inv_mul_cancel₀ hj]⟩
  have hae : hf σ J a e = 1 := by
    rw [← hf_symm hσ hJ, hea, map_one]
  have haa : σ (hf σ J a a) = hf σ J a a := hf_symm hσ hJ a a
  set t : E := -(hf σ J a a) / 2 with ht_def
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have ht : t + σ t = -(hf σ J a a) := by
    rw [ht_def, map_div₀, map_neg, haa, hσ2]
    field_simp
    ring
  refine ⟨a + t • e, ?_, ?_⟩
  · rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right,
      hf_smul_right, hea, hae, hee]
    linear_combination ht
  · rw [hf_add_right, hf_smul_right, hea, hee, mul_zero, add_zero]

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAHolds
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem SAHolds.of_neighbourhoods_truncation (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement := by
  classical
  intro F E _ _ _ _ _ c hrk hc N J hJ hdet hiso _ _ x hx
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  obtain ⟨hN1, hN2⟩ := hNb F E c hrk hc
  change x ∈ Cl c J
  rw [Cl, ← closure_closure, mem_closure_iff_nhds]
  intro U hU
  have hU' : (fun M => x + M) ⁻¹' U ∈ 𝓝 (0 : Matrix (Fin N) (Fin N) (AE F E)) := by
    have hcont : Continuous (fun M : Matrix (Fin N) (Fin N) (AE F E) => x + M) :=
      continuous_const.add continuous_id
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨S₀, hS₀⟩ := hN1 N _ hU'
  choose T hT using fun p : Fin N × Fin N => hN2 (x p.1 p.2)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ Finset.univ.biUnion T with hSdef
  obtain ⟨t1, t2, -, t4⟩ := hTr F E c hrk hc N J hJ hdet hiso S x
  refine ⟨trunc E S x, ?_, t4 hx⟩
  have hmem : x + (trunc E S x - x) ∈ U := by
    apply hS₀
    intro i j
    have hS : ∀ v ∈ S, compAt E v ((trunc E S x - x) i j) = 0 := by
      intro v hv
      have h := congrFun (congrFun (t1 v hv) i) j
      simp only [Matrix.map_apply] at h
      rw [Matrix.sub_apply, map_sub, h, sub_self]
    refine ⟨fun v hv => hS v (Finset.mem_union_left _ hv), fun v hv => ?_⟩
    by_cases hvS : v ∈ S
    · rw [hS v hvS]; exact zero_mem _
    · have h := congrFun (congrFun (t2 v hvS) i) j
      simp only [Matrix.map_apply] at h
      have hvT : v ∉ T (i, j) := fun h' =>
        hvS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, h'⟩))
      have hx' : compAt E v (x i j) ∈ intAt E v := hT (i, j) v hvT
      rw [Matrix.sub_apply, map_sub, h]
      refine sub_mem ?_ hx'
      rw [Matrix.one_apply]
      split_ifs
      · exact AddSubgroup.subset_closure
          ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩
      · exact zero_mem _
  simpa using hmem

theorem SAHolds.proof (_hHyp : HypPairExists.Statement) (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement :=
  SAHolds.of_neighbourhoods_truncation hNb hTr

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PAETopologicalRing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem AETopologicalRing.aut_mul_self (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) :
    c * c = 1 := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  by_contra h
  have hc2 : c * c ≠ c := fun h' => hc (by simpa using congrArg (c⁻¹ * ·) h')
  have hcard : ({1, c, c * c} : Finset (E ≃ₐ[F] E)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hc2)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hc, Ne.symm h⟩
  have hle := Finset.card_le_univ ({1, c, c * c} : Finset (E ≃ₐ[F] E))
  have := AlgEquiv.card_le (F := F) (K := E)
  omega

theorem AETopologicalRing.exists_anti (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) :
    ∃ δ : E, c δ = -δ ∧ δ ≠ 0 := by
  have hcc := AETopologicalRing.aut_mul_self c h2 hc
  obtain ⟨x, hx⟩ : ∃ x, c x ≠ x := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  refine ⟨x - c x, ?_, sub_ne_zero.2 (Ne.symm hx)⟩
  have hx2 : c (c x) = x := by rw [← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]
  rw [map_sub, hx2]
  ring


omit [NumberField F] in
theorem AETopologicalRing.linearIndependent_one_anti (c : E ≃ₐ[F] E) {δ : E} (hδ : c δ = -δ)
    (h0 : δ ≠ 0) : LinearIndependent F ![(1 : E), δ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
  have h' := congrArg c hst
  simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hδ, map_zero] at h'
  have ht : algebraMap F E t = 0 := by
    have : (2 * δ) * algebraMap F E t = 0 := by linear_combination hst - h'
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero h0)
  have ht' : t = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).1 ht
  subst ht'
  simp only [map_zero, zero_mul, add_zero] at hst
  exact ⟨(map_eq_zero_iff _ (algebraMap F E).injective).1 hst, rfl⟩

def AETopologicalRing.sigALinear (c : E ≃ₐ[F] E) :
    AE F E →ₗ[FiniteAdeleRing (𝓞 F) F] AE F E :=
  LinearMap.baseChange (FiniteAdeleRing (𝓞 F) F) c.toLinearMap

omit [NumberField E] in
theorem AETopologicalRing.sigALinear_apply (c : E ≃ₐ[F] E) (a : AE F E) :
    AETopologicalRing.sigALinear c a = sigA c a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end


open scoped RestrictedProduct in
theorem AETopologicalRing.t2Space_finiteAdeleRing (F : Type) [Field F] [NumberField F] :
    T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem AETopologicalRing.proof : AETopologicalRing.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have : IsTopologicalRing (AE F E) :=
    IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (AE F E)
  have hσ : Continuous (sigA c) := by
    have := IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F)
      (AETopologicalRing.sigALinear c)
    convert this using 1
    funext a
    exact (AETopologicalRing.sigALinear_apply c a).symm
  obtain ⟨δ, hδ, h0⟩ := AETopologicalRing.exists_anti c h2 hc
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank (AETopologicalRing.linearIndependent_one_anti c hδ h0)
      (by simp [h2])
  let B := Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b
  have hB0 : B 0 = (1 : AE F E) := by
    simp [B, b, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.one_def]
  have hB1 : B 1 = inclA F E δ := by
    simp [B, b, Algebra.TensorProduct.basis_apply]
    rfl
  have := AETopologicalRing.t2Space_finiteAdeleRing F
  have : T2Space (AE F E) := T2Space.of_injective_continuous B.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F) B.equivFun.toLinearMap)
  refine ⟨inferInstance, hσ, ⟨δ, hδ, fun a => ⟨(B.repr a 0, B.repr a 1), ?_, ?_⟩⟩, fun N J => ?_⟩
  · have := B.sum_repr a
    rw [Fin.sum_univ_two, hB0, hB1] at this
    exact this.symm
  · rintro ⟨p₁, p₂⟩ hp
    rw [hp, ← hB0, ← hB1]
    simp
  · have hmul : Continuous (fun p : Matrix (Fin N) (Fin N) (AE F E) × Matrix (Fin N) (Fin N) (AE F E) =>
        p.1 * p.2) := continuous_fst.matrix_mul continuous_snd
    have hform : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => gᵀ * J * g.map (sigA c)) :=
      (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul (continuous_id.matrix_map hσ)
    have hdet : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => g.det) := continuous_id.matrix_det
    exact ⟨hmul, hform, hdet, (isClosed_eq hdet continuous_const).inter (isClosed_eq hform continuous_const)⟩

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PClosureIsSubmonoid
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem invol_of_quadratic {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) : c (c x) = x := by
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) :=
    Fintype.one_lt_card_iff.2 ⟨c, 1, hc⟩
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := le_antisymm hle hge
  have hsq : c ^ 2 = 1 := hcard ▸ pow_card_eq_one
  have := congrArg (fun g : E ≃ₐ[F] E => g x) hsq
  simpa [pow_two] using this

theorem sigA_inclA_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

theorem map_mem_SU_AE {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by
  obtain ⟨hdet, hJ⟩ := hγ
  refine ⟨?_, ?_⟩
  · have h := (RingHom.map_det (inclA F E) γ).symm
    rw [hdet, map_one] at h
    exact h
  · have hmap : (γ.map (inclA F E)).map (sigA c) = (γ.map c.toRingHom).map (inclA F E) := by
      ext i j; simp [sigA_inclA_gen]
    rw [hmap, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hJ]

theorem ClosureIsSubmonoid.proof (h₁ : AETopologicalRing.Statement) (h₂ : EichlerDense.Statement) :
    ClosureIsSubmonoid.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ _ e f he hff hef _ _
  have hσ : ∀ x, c.toRingHom (c.toRingHom x) = x := invol_of_quadratic c h2 hc
  have hJ' : Jᵀ = J.map c.toRingHom := hJ
  obtain ⟨-, -, -, hmat⟩ := h₁ F E c h2 hc
  obtain ⟨hmul, -, -, hclosed⟩ := hmat N (J.map (inclA F E))
  obtain ⟨hde, hdf⟩ := h₂ F E c h2 hc N J hJ e f he hff hef
  set ι : Matrix (Fin N) (Fin N) E → Matrix (Fin N) (Fin N) (AE F E) := fun γ => γ.map (inclA F E)
  have himg : ι '' SU c.toRingHom J ⊆ SU (sigA c) (J.map (inclA F E)) := by
    rintro _ ⟨γ, hγ, rfl⟩; exact map_mem_SU_AE c J hγ
  refine ⟨closure_minimal himg hclosed, ?_, ?_, ?_⟩
  · apply subset_closure
    exact ⟨1, one_mem_SU, by simp⟩
  · intro a ha b hb
    refine map_mem_closure₂ hmul ha hb ?_
    rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
    exact ⟨γ * δ, mul_mem_SU hγ hδ, by simp [Matrix.map_mul]⟩
  · have hsub : ∀ {a b : Fin N → E}, hf c.toRingHom J a a = 0 →
        closure (ι '' eichAlong c.toRingHom J a b) ⊆ Cl c J := fun ha =>
      closure_mono (Set.image_mono (eichAlong_sub hσ hJ' ha))
    rintro M (hM | hM)
    · exact hsub he (hde hM)
    · exact hsub hff (hdf hM)

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PLocalRingHypotheses
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

theorem LocalRingHypotheses.proof : LocalRingHypotheses.Statement := by
  intro F E _ _ _ _ _ c h2 hc v
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ h2

  have hcc : ∀ x, c (c x) = x := by
    have hcard : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
    have hpos := orderOf_pos c
    have hle : orderOf c ≤ Fintype.card (E ≃ₐ[F] E) := orderOf_le_card_univ
    have hne : orderOf c ≠ 1 := fun h => hc (orderOf_eq_one_iff.mp h)
    have ho : orderOf c = 2 := by omega
    intro x
    have h := pow_orderOf_eq_one c
    rw [ho, pow_two] at h
    exact DFunLike.congr_fun h x
  have htmul : ∀ (a : v.adicCompletion F) (b : E), sigV c v (a ⊗ₜ b) = a ⊗ₜ c b := by
    intro a b
    simp [sigV]
  have hsig_incl : ∀ x : E, sigV c v (inclV E v x) = inclV E v (c x) := by
    intro x
    simp [inclV, htmul]

  have hinv : ∀ x, sigV c v (sigV c v x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [htmul, htmul, hcc]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

  obtain ⟨α, hα⟩ : ∃ α, c α ≠ α := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  set β : E := α - c α with hβdef
  have hcβ : c β = -β := by simp [hβdef, hcc]
  have hβ0 : β ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have h2k : (2 : v.adicCompletion F) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2]
    exact fun h => h2F ((algebraMap F (v.adicCompletion F)).injective (h.trans (map_zero _).symm))

  set t : Kv E v := (1 : v.adicCompletion F) ⊗ₜ β with htdef
  have ht : IsUnit t :=
    (isUnit_iff_ne_zero.mpr hβ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] Kv E v)
  have hσt : sigV c v t = -t := by rw [htdef, htmul, hcβ, TensorProduct.tmul_neg]

  have hli : LinearIndependent F ![(1 : E), β] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    have hsu' : algebraMap F E s + algebraMap F E u * β = 0 := by
      simpa [Algebra.smul_def] using hsu
    have hc' : algebraMap F E s + algebraMap F E u * -β = 0 := by
      have := congrArg c hsu'
      rwa [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcβ, map_zero] at this
    have hs : algebraMap F E (2 * s) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination hsu' + hc'
    have hs0 : s = 0 := by
      have := (algebraMap F E).injective (hs.trans (map_zero _).symm)
      exact (mul_eq_zero.mp this).resolve_left h2F
    subst hs0
    rw [map_zero, zero_add] at hsu'
    have hu : algebraMap F E u = 0 := (mul_eq_zero.mp hsu').resolve_right hβ0
    exact ⟨rfl, (algebraMap F E).injective (hu.trans (map_zero _).symm)⟩
  let B : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ∀ i, B i = ![(1 : E), β] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  let BK : Module.Basis (Fin 2) (v.adicCompletion F) (Kv E v) := Algebra.TensorProduct.basis _ B

  have hdecomp : ∀ x : Kv E v, ∃ a b : v.adicCompletion F,
      x = algebraMap _ _ a + algebraMap _ _ b * t := by
    intro x
    refine ⟨BK.repr x 0, BK.repr x 1, ?_⟩
    conv_lhs => rw [← BK.sum_repr x]
    rw [Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def]
    simp [BK, Algebra.TensorProduct.basis_apply, hB, htdef]
  have hinj : Function.Injective (algebraMap (v.adicCompletion F) (Kv E v)) := by
    have : Nontrivial (Kv E v) := ⟨⟨0, t, (ht.ne_zero).symm⟩⟩
    exact (algebraMap (v.adicCompletion F) (Kv E v)).injective

  have hfix : ∀ x, sigV c v x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion F) (Kv E v)) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, b, rfl⟩ := hdecomp x
      rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσt] at hx
      have h2b : algebraMap _ (Kv E v) (2 * b) * t = 0 := by
        rw [map_mul, map_ofNat]
        linear_combination -hx
      have hb : b = 0 := by
        have := (ht.mul_left_eq_zero).mp h2b
        rw [← map_zero (algebraMap (v.adicCompletion F) (Kv E v))] at this
        exact (mul_eq_zero.mp (hinj this)).resolve_left h2k
      exact ⟨a, by simp [hb]⟩
    · rintro ⟨a, rfl⟩
      exact AlgHom.commutes _ a

  have hrank : Module.finrank (v.adicCompletion F) (Kv E v) = 2 := by
    rw [Module.finrank_baseChange, h2]

  have hred : IsReduced (Kv E v) := by
    have : Algebra.IsSeparable F E := inferInstance
    have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
    exact Algebra.FormallyUnramified.isReduced_of_field (v.adicCompletion F) (Kv E v)
  refine ⟨hinv, hfix, hrank, hred, h2k, hsig_incl, ?_⟩
  intro N J x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, hsig_incl]
  rfl

end GroundTheory.Heights₂.Heights.StrongApprox
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEichlerDense
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

namespace EichlerDense

section Ring

variable {R : Type*} [CommRing R] {N : ℕ}

def param (σ : R →+* R) (J : Matrix (Fin N) (Fin N) R) (e f : Fin N → R) (κ : R)
    (p : (Fin N → R) × R) : Matrix (Fin N) (Fin N) R :=
  eich σ J e (perpProj σ J e f p.1)
    (p.2 - σ p.2 - κ * hf σ J (perpProj σ J e f p.1) (perpProj σ J e f p.1))

theorem hf_map {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (x y : Fin N → R) :
    hf σ' (J.map φ) (φ ∘ x) (φ ∘ y) = φ (hf σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [hf, map_sum, map_mul, hφ]

theorem eich_map {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (e u : Fin N → R) (c : R) :
    (eich σ J e u c).map φ = eich σ' (J.map φ) (φ ∘ e) (φ ∘ u) (φ c) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [eich, vecMulVec_apply, mulVec, dotProduct, map_sum, hφ, Matrix.one_apply, apply_ite φ]

theorem param_map {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (e f : Fin N → R) (κ : R)
    (p : (Fin N → R) × R) :
    (param σ J e f κ p).map φ = param σ' (J.map φ) (φ ∘ e) (φ ∘ f) (φ κ) (φ ∘ p.1, φ p.2) := by
  have hP : φ ∘ perpProj σ J e f p.1 = perpProj σ' (J.map φ) (φ ∘ e) (φ ∘ f) (φ ∘ p.1) := by
    funext i
    simp only [perpProj, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
      map_mul, hf_map σ σ' φ hφ]
  rw [param, param, eich_map σ σ' φ hφ, ← hP, map_sub, map_sub, map_mul, hφ, hf_map σ σ' φ hφ]

variable {σ : R →+* R} (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin N) (Fin N) R} (hJ : Jᵀ = J.map σ)
  {e f : Fin N → R} {κ : R} (hκ : κ + κ = 1) (hσκ : σ κ = κ)
include hσ hJ hκ hσκ

theorem param_mem
    (hP : ∀ u, hf σ J (perpProj σ J e f u) e = 0 ∧ hf σ J (perpProj σ J e f u) f = 0)
    (p : (Fin N → R) × R) : param σ J e f κ p ∈ eichAlong σ J e f := by
  refine ⟨perpProj σ J e f p.1, _, (hP p.1).1, (hP p.1).2, ?_, rfl⟩
  have hh := hf_symm hσ hJ (perpProj σ J e f p.1) (perpProj σ J e f p.1)
  rw [map_sub, map_sub, map_mul, hσ, hσκ, hh]
  linear_combination (-(hf σ J (perpProj σ J e f p.1) (perpProj σ J e f p.1))) * hκ


omit hσ hJ in
theorem eq_param
    (hfix : ∀ u, hf σ J u e = 0 → hf σ J u f = 0 → perpProj σ J e f u = u)
    {M : Matrix (Fin N) (Fin N) R} (hM : M ∈ eichAlong σ J e f) : ∃ p, M = param σ J e f κ p := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  refine ⟨(u, κ * c), ?_⟩
  simp only [param, hfix u hue huf]
  congr 1
  rw [map_mul, hσκ]
  linear_combination κ * hc - c * hκ

end Ring

section Top

variable {X : Type*} [TopologicalSpace X] {S : Type*} [CommRing S] [TopologicalSpace S]
  [IsTopologicalRing S] {N : ℕ} {σ : S →+* S}

theorem continuous_hf (hσ : Continuous σ) (J : Matrix (Fin N) (Fin N) S) {x y : X → Fin N → S}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun t => hf σ J (x t) (y t) := by
  unfold hf
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_apply i).comp hx).mul continuous_const).mul
    (hσ.comp ((continuous_apply j).comp hy))

theorem continuous_eich (hσ : Continuous σ) (J : Matrix (Fin N) (Fin N) S) (e : Fin N → S)
    {g : X → Fin N → S} {k : X → S} (hg : Continuous g) (hk : Continuous k) :
    Continuous fun t => eich σ J e (g t) (k t) := by
  have hσg : Continuous fun t => σ ∘ g t :=
    continuous_pi fun i => hσ.comp ((continuous_apply i).comp hg)
  unfold eich
  fun_prop

end Top

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem c_invol (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) :
    c (c x) = x := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) := by
    rw [← Finset.card_pair (Ne.symm hc)]
    exact Finset.card_le_univ _
  have hsq : c ^ 2 = 1 := by
    rw [← le_antisymm hle hge]
    exact pow_card_eq_one
  have := congrArg (fun g : E ≃ₐ[F] E => g x) hsq
  simpa [pow_two] using this

omit [NumberField E] in
theorem sigA_inclA' (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

omit [NumberField E] in
theorem sigA_invol' (c : E ≃ₐ[F] E) (hc2 : ∀ x, c (c x) = x) (a : AE F E) :
    sigA c (sigA c a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigA, Algebra.TensorProduct.map_tmul, hc2]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem along (hT : AETopologicalRing.Statement) (hD : EDenseInAE.Statement)
    (hO : OrthProjection.Statement) (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (N : ℕ) (J : Matrix (Fin N) (Fin N) E) (hJ : Jᵀ = J.map c) (e f : Fin N → E)
    (he : hf c.toRingHom J e e = 0) (hff : hf c.toRingHom J f f = 0) (hef : hf c.toRingHom J e f = 1)
    [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)] :
    eichAlong (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) ⊆
      closure ((fun γ : Matrix (Fin N) (Fin N) E => γ.map (inclA F E)) ''
        eichAlong c.toRingHom J e f) := by
  obtain ⟨hring, hσc, -, -⟩ := hT F E c h2 hc
  have hc2 : ∀ x, c.toRingHom (c.toRingHom x) = x := c_invol c h2 hc
  have hσA : ∀ x, sigA c (sigA c x) = x := sigA_invol' c (c_invol c h2 hc)
  have hφ : ∀ x, inclA F E (c.toRingHom x) = sigA c (inclA F E x) := fun x => (sigA_inclA' c x).symm
  have hJA : (J.map (inclA F E))ᵀ = (J.map (inclA F E)).map (sigA c) := by
    ext i j
    have := congrFun (congrFun hJ i) j
    simp only [transpose_apply, map_apply] at this ⊢
    rw [this, sigA_inclA']
  have hκ : (2 : E)⁻¹ + (2 : E)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ two_ne_zero]
  have hcκ : c.toRingHom (2 : E)⁻¹ = (2 : E)⁻¹ := by rw [map_inv₀, map_ofNat]
  have hκA : inclA F E (2 : E)⁻¹ + inclA F E (2 : E)⁻¹ = 1 := by rw [← map_add (f := _), hκ, map_one]
  have hσκA : sigA c (inclA F E (2 : E)⁻¹) = inclA F E (2 : E)⁻¹ := by rw [← hφ, hcκ]
  have heA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ e) = 0 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, he, map_zero]
  have hffA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ f) (inclA F E ∘ f) = 0 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, hff, map_zero]
  have hefA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) = 1 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, hef, map_one]
  obtain ⟨hP1, hP2⟩ := hO
  obtain ⟨-, -, hPE, -⟩ := hP1 E c.toRingHom hc2 N J hJ e f he hff hef
  obtain ⟨-, -, -, hfixA⟩ := hP1 (AE F E) (sigA c) hσA N (J.map (inclA F E)) hJA _ _ heA hffA hefA
  obtain ⟨hPcont, -⟩ := hP2 F E c h2 hc N J e f
  have hcont : Continuous (param (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f)
      (inclA F E (2 : E)⁻¹)) := by
    have hu : Continuous fun p : (Fin N → AE F E) × AE F E =>
        perpProj (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) p.1 :=
      hPcont.comp continuous_fst
    exact continuous_eich hσc _ _ hu ((continuous_snd.sub (hσc.comp continuous_snd)).sub
      (continuous_const.mul (continuous_hf hσc _ hu hu)))
  have hdense : DenseRange (Prod.map (Pi.map fun _ : Fin N => inclA F E) (inclA F E)) :=
    (DenseRange.piMap fun _ => hD F E c h2 hc).prodMap (hD F E c h2 hc)
  intro M hM
  obtain ⟨p, rfl⟩ := eq_param hκA hσκA hfixA hM
  refine map_mem_closure hcont (hdense p) ?_
  rintro _ ⟨⟨w, t⟩, rfl⟩
  exact ⟨param c.toRingHom J e f (2 : E)⁻¹ (w, t), param_mem hc2 hJ hκ hcκ hPE (w, t),
    param_map c.toRingHom (sigA c) (inclA F E) hφ J e f (2 : E)⁻¹ (w, t)⟩

end Field

end EichlerDense

theorem EichlerDense.proof (h₁ : AETopologicalRing.Statement) (h₂ : EDenseInAE.Statement)
    (h₃ : OrthProjection.Statement) : EichlerDense.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ e f he hff hef _ _
  have hfe : hf c.toRingHom J f e = 1 :=
    hf_fe (fun x => EichlerDense.c_invol c h2 hc x) hJ he hff hef
  exact ⟨EichlerDense.along h₁ h₂ h₃ c h2 hc N J hJ e f he hff hef,
    EichlerDense.along h₁ h₂ h₃ c h2 hc N J hJ f e hff he hfe⟩

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end
