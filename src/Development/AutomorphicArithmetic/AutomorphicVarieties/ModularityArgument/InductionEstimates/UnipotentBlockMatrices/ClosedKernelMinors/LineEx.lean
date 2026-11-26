module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ContLv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.RepZero
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem fd_pts {X : Type} (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ (a : ℕ) (x : Fin a → Fin a → X), ∀ f ∈ E, (∀ i p, f (x i p) = 0) → ∀ u, f u = 0 := by
  obtain ⟨a, b, φ, ψ, x, y, s, t, -, -, h⟩ := tens E (⊤ : Submodule ℂ (Unit → ℂ))
  refine ⟨a, x, fun f hf h0 u => ?_⟩
  have := h (fun u _ => f u) (fun _ => hf) (fun _ => Submodule.mem_top) u ()
  simpa [h0] using this

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem rep_zero (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) :
    ∃ v ∈ τ, Reps μ v fun _ => 0 := by
  refine ⟨0, τ.zero_mem, ?_⟩
  filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ)
    (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
  exact hy

private theorem rep_add (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) {φ ψ : G1 K n → ℂ}
    (h₁ : ∃ v ∈ τ, Reps μ v φ) (h₂ : ∃ v ∈ τ, Reps μ v ψ) : ∃ v ∈ τ, Reps μ v fun y => φ y + ψ y := by
  obtain ⟨v, hv, h₁⟩ := h₁
  obtain ⟨w, hw, h₂⟩ := h₂
  refine ⟨v + w, τ.add_mem hv hw, ?_⟩
  filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_add v w), h₁, h₂] with y hy a b
  rw [← a, ← b]
  exact hy

private theorem rep_smul (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (c : ℂ) {φ : G1 K n → ℂ}
    (h₁ : ∃ v ∈ τ, Reps μ v φ) : ∃ v ∈ τ, Reps μ v fun y => c * φ y := by
  obtain ⟨v, hv, h₁⟩ := h₁
  refine ⟨c • v, τ.smul_mem c hv, ?_⟩
  filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_smul c v), h₁] with y hy a
  rw [← a]
  exact hy

private theorem fix_int (D : TypeDat K n) {f : G1 K n → ℂ} (hf : Continuous f) (g : G1 K n) :
    Integrable (fun k => D.e k * f (g * k)) D.ν := by
  haveI := D.prob
  haveI : IsFiniteMeasure D.ν := MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure D.ν
  haveI : IsFiniteMeasureOnCompacts D.ν := ⟨fun _ _ => measure_lt_top _ _⟩
  have hc : Continuous fun k => D.e k * f (g * k) := D.cont.mul (hf.comp (continuous_const.mul continuous_id))
  have hU := (typeFin D).1
  have h1 : IntegrableOn (fun k => D.e k * f (g * k)) (D.U : Set (G1 K n)) D.ν :=
    hc.continuousOn.integrableOn_compact hU
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem D.supp] at h1

private theorem cosets (D : TypeDat K n) :
    ∃ s : Finset (G1 K n), (∀ k ∈ s, k ∈ KG K n) ∧ ∀ k ∈ KG K n, ∃ j ∈ s, ∃ u ∈ D.U, k = j * u := by
  obtain ⟨O, hO, hU⟩ := D.isOpen
  have hK : IsCompact (KG K n : Set (G1 K n)) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1
  have h1 : ((1 : G1 K n) : AdelicGLn.AdelicGL K n) ∈ O := ((hU 1).1 D.U.one_mem).1
  obtain ⟨s, hs, hcov⟩ := hK.elim_nhds_subcover
    (fun j => {g : G1 K n | ((j⁻¹ * g : G1 K n) : AdelicGLn.AdelicGL K n) ∈ O}) (fun j _ => by
      refine IsOpen.mem_nhds (hO.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id))) ?_
      simpa using h1)
  refine ⟨s, hs, fun k hk => ?_⟩
  obtain ⟨j, hj, hkj⟩ := Set.mem_iUnion₂.1 (hcov hk)
  refine ⟨j, hj, j⁻¹ * k, (hU _).2 ⟨hkj, ?_⟩, by group⟩
  exact (KG K n).mul_mem ((KG K n).inv_mem (hs j hj)) hk

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.secFD :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ →
      ∃ S : Submodule ℂ (G1 K (2 + 2) → ℂ), FiniteDimensional ℂ S ∧ ∀ f, f ∈ S ↔ IsSec τ₁ τ₂ f ∧ D.Fix f := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ D h₁ h₂
  let S : Submodule ℂ (G1 K (2 + 2) → ℂ) :=
    { carrier := {f | D.Fix f ∧ Continuous f ∧ (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ (∀ X g, f (nn X * g) = f g) ∧
        (∀ t g, f (lv 1 1 t * g) = f g) ∧ Slices τ₁ τ₂ f}
      zero_mem' := ⟨fun g => by simp, continuous_const, ⟨0, fun g => by simp⟩, fun _ _ => rfl, fun _ _ => rfl,
        fun g => ⟨fun _ => rep_zero μ₂ τ₁, fun _ => rep_zero μ₂ τ₂⟩⟩
      add_mem' := by
        rintro f f' ⟨a1, a2, ⟨C, a3⟩, a4, a5, a6⟩ ⟨b1, b2, ⟨C', b3⟩, b4, b5, b6⟩
        refine ⟨fun g => ?_, a2.add b2, ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (a3 g) (b3 g))⟩,
          fun X g => by simp only [Pi.add_apply, a4, b4], fun t g => by simp only [Pi.add_apply, a5, b5],
          fun g => ⟨fun m => rep_add μ₂ τ₁ ((a6 g).1 m) ((b6 g).1 m), fun m => rep_add μ₂ τ₂ ((a6 g).2 m) ((b6 g).2 m)⟩⟩
        simp only [Pi.add_apply, mul_add]
        rw [integral_add (fix_int D a2 g) (fix_int D b2 g), a1 g, b1 g]
      smul_mem' := by
        rintro c f ⟨a1, a2, ⟨C, a3⟩, a4, a5, a6⟩
        refine ⟨fun g => ?_, a2.const_smul c, ⟨‖c‖ * C, fun g => ?_⟩,
          fun X g => by simp only [Pi.smul_apply, a4], fun t g => by simp only [Pi.smul_apply, a5],
          fun g => ⟨fun m => rep_smul μ₂ τ₁ c ((a6 g).1 m), fun m => rep_smul μ₂ τ₂ c ((a6 g).2 m)⟩⟩
        · simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
          rw [integral_const_mul, a1 g]
        · rw [Pi.smul_apply, norm_smul]
          exact mul_le_mul_of_nonneg_left (a3 g) (norm_nonneg c) }
  refine ⟨S, ?_, fun f => ⟨fun hf => ⟨(secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hf.1).2 hf.2, hf.1⟩,
    fun hf => ⟨hf.2, (secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hf.2).1 hf.1⟩⟩⟩
  obtain ⟨E₁, E₂, hE₁, hE₂, -, -, hE⟩ := secStr μ₂ τ₁ τ₂ D h₁ h₂
  obtain ⟨-, -, A, hA, -, hAf⟩ := typeFin D
  obtain ⟨a, x, hx⟩ := fd_pts E₁
  obtain ⟨b, y, hy⟩ := fd_pts E₂
  obtain ⟨c, z, hz⟩ := fd_pts A
  obtain ⟨s, -, hs⟩ := cosets D
  let pts : (Fin a × Fin a) × (Fin b × Fin b) × s × (Fin c × Fin c) → G1 K (2 + 2) := fun p =>
    lv (x p.1.1 p.1.2) (y p.2.1.1 p.2.1.2) 0 * (p.2.2.1 : G1 K (2 + 2)) * (z p.2.2.2.1 p.2.2.2.2 : G1 K (2 + 2))
  refine FiniteDimensional.of_injective ((LinearMap.funLeft ℂ ℂ pts).comp S.subtype) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  rintro ⟨f, a1, a2, a3, a4, a5, a6⟩ hf
  have h0 : ∀ p, f (pts p) = 0 := fun p => congrFun hf p
  have h1 : ∀ i p j q, ∀ k ∈ KG K (2 + 2), f (lv (x i p) (y j q) 0 * k) = 0 := by
    intro i p j q k hk
    obtain ⟨w, hw, u, hu, rfl⟩ := hs k hk
    rw [← mul_assoc]
    exact hz _ (hAf f a2 a1 (lv (x i p) (y j q) 0 * w)) (fun r r' => h0 ((i, p), (j, q), ⟨w, hw⟩, (r, r'))) ⟨u, hu⟩
  have h2 : ∀ m₁ m₂, ∀ k ∈ KG K (2 + 2), f (lv m₁ m₂ 0 * k) = 0 := by
    intro m₁ m₂ k hk
    have hk' := hE f a2 a1 a6 k hk
    exact hy _ (hk'.2 m₁) (fun j q => hx _ (hk'.1 (y j q)) (fun i p => h1 i p j q k hk) m₁) m₂
  apply Subtype.ext
  funext g
  obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
  have hl : lv m₁ m₂ t = lv 1 1 t * lv m₁ m₂ 0 := by
    rw [(blkLaws (K := K)).2.1]; simp
  change f _ = 0
  rw [mul_assoc, a4, hl, mul_assoc, a5, h2 m₁ m₂ k hk]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.IsoExt
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem gramExt {ι E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (a : ι → E) (b : ι → H)
    (hd : Dense ((Submodule.span ℂ (Set.range a) : Submodule ℂ E) : Set E))
    (hg : ∀ i j, ⟪b i, b j⟫_ℂ = ⟪a i, a j⟫_ℂ) : ∃ J : E →ₗᵢ[ℂ] H, ∀ i, J (a i) = b i := by
  let A := Finsupp.linearCombination ℂ a
  let B := Finsupp.linearCombination ℂ b
  have hden : DenseRange A := by
    have : Set.range A = ((Submodule.span ℂ (Set.range a) : Submodule ℂ E) : Set E) := by
      rw [← Finsupp.range_linearCombination, LinearMap.coe_range]
    rw [DenseRange, this]; exact hd
  have hin : ∀ x y, ⟪B x, B y⟫_ℂ = ⟪A x, A y⟫_ℂ := by
    intro x y
    simp only [A, B, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hg]
  have hn : ∀ x, ‖B x‖ = ‖A x‖ := by
    intro x
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hin]
  have hb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C * ‖A x‖ := ⟨1, fun x => by rw [one_mul, hn]⟩
  have h1 : ∀ x, (B.extendOfNorm A) (A x) = B x := fun x => LinearMap.extendOfNorm_eq hden hb x
  refine ⟨⟨(B.extendOfNorm A).toLinearMap, fun u => ?_⟩, fun i => ?_⟩
  · refine hden.induction_on (p := fun u => ‖(B.extendOfNorm A) u‖ = ‖u‖) u ?_ ?_
    · exact isClosed_eq (B.extendOfNorm A).continuous.norm continuous_norm
    · intro x; rw [h1, hn]
  · have := h1 (Finsupp.single i 1)
    simpa [A, B] using this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.isoExt :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (d : ℕ) (T : (ℝ → ℂ) → Eu d → H),
      (∀ β β' v v', Continuous β → HasCompactSupport β → Continuous β' → HasCompactSupport β' → ⟪T β v, T β' v'⟫_ℂ = (∫ t, conj (β t) * β' t) * ⟪v, v'⟫_ℂ) →
      ∃ J : L (Eu d) →ₗᵢ[ℂ] H, ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ᵐ x : ℝ, u x = β x • v) → J u = T β v := by
  intro H _ _ _ d T hT
  let ι := {p : (ℝ → ℂ) × Eu d × L (Eu d) //
    Continuous p.1 ∧ HasCompactSupport p.1 ∧ ∀ᵐ x : ℝ, p.2.2 x = p.1 x • p.2.1}
  obtain ⟨J, hJ⟩ := gramExt (ι := ι) (fun p => p.1.2.2) (fun p => T p.1.1 p.1.2.1) (by
    have h := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.denseCc d).1
    refine h.mono (SetLike.coe_subset_coe.2 (Submodule.span_mono ?_))
    rintro u ⟨β, v, h⟩
    exact ⟨⟨(β, v, u), h⟩, rfl⟩) (by
    rintro ⟨⟨β, v, u⟩, h1, h2, h3⟩ ⟨⟨β', v', u'⟩, h1', h2', h3'⟩
    dsimp only at *
    rw [hT β β' v v' h1 h2 h1' h2', MeasureTheory.L2.inner_def, ← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [h3, h3'] with x e e'
    rw [e, e', inner_smul_left, inner_smul_right, mul_assoc])
  exact ⟨J, fun β v u h1 h2 h3 => hJ ⟨(β, v, u), h1, h2, h3⟩⟩
end

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem frame_ex {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (B : V → V → ℂ)
    (hlin : ∀ f ∈ S, ∀ f' ∈ S, ∀ f'' ∈ S, ∀ a : ℂ, B f (a • f' + f'') = a * B f f' + B f f'')
    (hsym : ∀ f ∈ S, ∀ f' ∈ S, conj (B f f') = B f' f)
    (hpos : ∀ f ∈ S, f ≠ 0 → 0 < (B f f).re) :
    ∃ (d : ℕ) (sec : Eu d →ₗ[ℂ] V), Function.Injective sec ∧ LinearMap.range sec = S ∧
      ∀ v v', B (sec v) (sec v') = ⟪v, v'⟫_ℂ := by
  have h0 : ∀ f ∈ S, B f 0 = 0 := by
    intro f hf
    have h := hlin f hf 0 S.zero_mem 0 S.zero_mem 1
    simp only [smul_zero, add_zero, one_mul] at h
    simpa using h
  let core : InnerProductSpace.Core ℂ S :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => hsym _ y.2 _ x.2
      re_inner_nonneg := fun x => by
        by_cases hx : (x : V) = 0
        · show 0 ≤ (B x x).re
          have : B x x = 0 := by
            have := h0 _ x.2
            rw [← hx] at this
            simpa [hx] using this
          simp [this]
        · exact (hpos _ x.2 hx).le
      add_left := fun x y z => by
        show B ((x : V) + y) z = B x z + B y z
        have h := hlin _ z.2 _ x.2 _ y.2 1
        rw [one_smul, one_mul] at h
        rw [← hsym _ z.2 _ (S.add_mem x.2 y.2), h, map_add (f := _), hsym _ z.2 _ x.2, hsym _ z.2 _ y.2]
      smul_left := fun x y r => by
        show B (r • (x : V)) y = conj r * B x y
        have h := hlin _ y.2 _ x.2 _ S.zero_mem r
        rw [add_zero, h0 _ y.2, add_zero] at h
        rw [← hsym _ y.2 _ (S.smul_mem r x.2), h, map_mul, hsym _ y.2 _ x.2]
      definite := fun x hx => by
        by_contra hne
        have h := hpos _ x.2 (fun h => hne (Subtype.ext h))
        have hx' : B x x = 0 := hx
        rw [hx'] at h
        simp at h }
  letI : NormedAddCommGroup S := @InnerProductSpace.Core.toNormedAddCommGroup ℂ S _ _ _ core
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore core.toCore
  let e := (stdOrthonormalBasis ℂ S).repr.symm
  refine ⟨Module.finrank ℂ S, S.subtype ∘ₗ (e.toLinearEquiv : _ →ₗ[ℂ] S), ?_, ?_, ?_⟩
  · exact S.injective_subtype.comp e.injective
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  · intro v v'
    exact e.inner_map_map v v'

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.lineEx :
    LineExC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) :=
    ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.mp hK
  haveI : LocallyCompactSpace (KG K (2 + 2)) := hK.isClosed.locallyCompactSpace
  let κ : Measure (KG K (2 + 2)) := Measure.haar
  obtain ⟨⟨c, hc⟩, hvol⟩ := unf μ μ₂ κ
  obtain ⟨S, hfd, hS⟩ := secFD μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂
  have hsf : ∀ f ∈ S, SFun f := fun f hf =>
    secFun μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ f ((hS f).1 hf).1 ((hS f).1 hf).2
  have hsl : ∀ f ∈ S, Slices τ₁ τ₂ f := fun f hf =>
    ((secCrit μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ f ((hS f).1 hf).2).1 ((hS f).1 hf).1).2.2.2.2
  obtain ⟨hz, hl, hp, -⟩ := pmLaws μ₂ κ
  obtain ⟨d, sec, hinj, hr, hB⟩ := frame_ex S
    (fun f f' => ((c * volN K : ℝ) : ℂ) * ∫ k : KG K (2 + 2), pm μ₂ f f' k k ∂κ)
    (fun f hf f' hf' f'' hf'' a => by
      rw [(hl f f' f'' (hsf f hf) (hsf f' hf') (hsf f'' hf'') a).1]; ring)
    (fun f hf f' hf' => by
      rw [map_mul, (hl f f' f' (hsf f hf) (hsf f' hf') (hsf f' hf') 1).2, Complex.conj_ofReal])
    (fun f hf h => by
      rw [Complex.re_ofReal_mul]
      exact mul_pos (mul_pos hc.1 hvol) (hp f (hsf f hf) h))
  have hmem : ∀ v, sec v ∈ S := fun v => hr ▸ LinearMap.mem_range_self sec v
  have hex : ∀ (β : ℝ → ℂ) (v : Eu d), ∃ w : L2 μ, Continuous β → HasCompactSupport β → Reps μ w (theta β (sec v)) := by
    intro β v
    by_cases h : Continuous β ∧ HasCompactSupport β
    · obtain ⟨h1, h2, h3⟩ := bfFun (sec v) β (hsf _ (hmem v)) h.1 h.2
      obtain ⟨w, hw⟩ := ((thBasic μ _ h1.cont h1.rat h2).2.2.2 h3).2.2
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨0, fun a b => (h ⟨a, b⟩).elim⟩
  choose T hT using hex
  obtain ⟨J, hJ⟩ := isoExt d T (by
    intro β β' v v' h1 h2 h3 h4
    rw [pairF μ μ₂ κ c hc (sec v) (sec v') β β' (hsf _ (hmem v)) (hsf _ (hmem v')) h1 h2 h3 h4 _ _
      (hT β v h1 h2) (hT β' v' h3 h4), ← hB v v']
    have h0 : ∀ x y, pw μ₂ (sec v) (sec v') x y = 0 := fun x y =>
      (hz τ₁ τ₂ τ₁ τ₂ _ _ (hsf _ (hmem v)) (hsf _ (hmem v')) (hsl _ (hmem v)) (hsl _ (hmem v')) x y).2 hP.orth
    simp only [h0, mul_zero, integral_zero, add_zero]
    push_cast
    ring)
  refine ⟨d, ⟨⟨sec, hinj, fun f => by rw [hr]; exact hS f, J, ?_⟩⟩⟩
  intro β v u h1 h2 hu
  rw [hJ β v u h1 h2 hu]
  exact hT β v h1 h2
