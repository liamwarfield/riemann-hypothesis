module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaTraceValuesAtComplexPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyAppellHumbertFramePullEqTransitionMu
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyAppellHumbertFramePullEqTransitionMu
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section

namespace GlobalTheory.HeckeEx

theorem frame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  intro E _ _ _ H Dw l Xo yx zx p ψp b g Λ Λ' e e' h hΛ hhe hhe' hadd hker hψ hΛΛ' hbn hbc hb0 hbd
    Hm χl fr hH hd hn hc h0 ha Hm' χl' fr' hHH hd' hc' h0' ha' w i j hi hj
  have e0 : e 0 = 1 := hker 0 (zero_mem Λ)
  have hpow : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n := by
    intro n z
    induction n with
    | zero => rw [Nat.cast_zero, zero_smul, e0, pow_zero]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have e'0 : e' 0 = 1 := by rw [← map_zero h, hψ, e0, map_one]
  have hpa : ∀ a ∈ Λ, (p : ℂ) • a ∈ Λ := fun a haa => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem haa p
  have per : ∀ a ∈ Λ, ∀ z, e (z + a) = e z := fun a haa z => by rw [hadd, hker a haa]; exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hsm : ∀ z a, hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a) = (p : ℂ) ^ 2 * hermForm Hm z a := fun z a => by
    rw [GlobalTheory.UnitFrameGen.hermForm_smul_left, GlobalTheory.UnitFrameGen.hermForm_smul_right, star_natCast]; ring
  have ho1 : ∀ V, IsOpen {z | ⊤ ≤ (e z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe V 0).1
  have ho1' : ∀ V, IsOpen {z | ⊤ ≤ (e' z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe' V 0).1
  have hch : Continuous h := h.toLinearMap.continuous_of_finiteDimensional
  have dh : Differentiable ℂ (fun z => h z) := (LinearMap.toContinuousLinearMap h.toLinearMap).differentiable
  have dsm : Differentiable ℂ (fun z : Fin g → ℂ => (p : ℂ) • z) := differentiable_id.const_smul (p : ℂ)
  have key := GlobalTheory.UnitFrameGen.frames_eq Λ hΛ
    (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι =>
      {w | ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.1 ∧ ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.2})
    (fun q => ((ho1' _).preimage hch).inter ((ho1 _).preimage (continuous_const_smul (p : ℂ))))
    (fun z => by
      obtain ⟨i', hi'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e' (h z)).left
      obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e ((p : ℂ) • z)).left
      exact ⟨(i', j'), hi', hj'⟩)
    (fun q a haa z hz => by
      refine ⟨?_, ?_⟩
      · rw [hψ, per a haa, ← hψ]; exact hz.1
      · rw [smul_add, per _ (hpa a haa)]; exact hz.2)
    (fun q z => b q.1 q.2 (e z) * fr q.2 ((p : ℂ) • z)) (fun q z => fr' q.1 (h z))
    (fun q q' z => valAt' (e' (h z)).left (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
      (Xo.univ.t.PP.L.g q.1 q'.1).val)
    (fun a z => Real.exp (Real.pi * (hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a)).re +
      Real.pi / 2 * (hermForm Hm ((p : ℂ) • a) ((p : ℂ) • a)).re))
    (fun q => ((hbd q.1 q.2).mono fun z hz => ⟨by rw [← hψ]; exact hz.1, by rw [← hpow]; exact hz.2⟩).mul
      ((hd q.2).comp dsm.differentiableOn fun z hz => hz.2))
    (fun q => (hd' q.1).comp dh.differentiableOn fun z hz => hz.1)
    (fun q z hz => mul_ne_zero (hbn q.1 q.2 (e z) (by rw [← hψ]; exact hz.1) (by rw [← hpow]; exact hz.2))
      (hn q.2 _ hz.2))
    (fun q q' z h1 h2 => by
      have e1 := hc q.2 q'.2 ((p : ℂ) • z) ((top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      have e2 := hbc q.1 q.2 q'.1 q'.2 (e z)
        (by rw [← hψ]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩)
        (by rw [← hpow]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      rw [hpow] at e1
      rw [hψ, e1]
      linear_combination e2 * fr q'.2 ((p : ℂ) • z))
    (fun q q' z h1 h2 => hc' q.1 q'.1 (h z) ((top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩))
    (fun q hz => by
      have z1 := hz.1
      have z2 := hz.2
      rw [map_zero] at z1
      rw [smul_zero] at z2
      rw [map_zero, smul_zero, h0' _ z1, h0 _ z2, e0]
      rw [e'0] at z1
      rw [e0] at z2
      exact hb0 q.1 q.2 z1 z2)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm _ _ _ _ _ (ha _ (hpa a haa) q.2 ((p : ℂ) • z)).1
        ((ha _ (hpa a haa) q.2 _).2 hz.2)
      rw [per a haa, smul_add, norm_mul, norm_mul, this]; ring)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm' _ _ _ _ _ (ha' _ (hΛΛ' a haa) q.1 (h z)).1
        ((ha' _ (hΛΛ' a haa) q.1 (h z)).2 hz.1)
      rw [hHH, hHH] at this
      rw [map_add (f := _), this, hsm, hsm])
  exact key (i, j) w ⟨hi, hj⟩

end GlobalTheory.HeckeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyAppellHumbertFramePullEqTransitionMuStatement
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_appellHumbertFrame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  first | exact @GlobalTheory.HeckeEx.frame_pull_eq_transition_mul | exact GlobalTheory.HeckeEx.frame_pull_eq_transition_mul | (intros; apply GlobalTheory.HeckeEx.frame_pull_eq_transition_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFrames
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section
namespace GlobalTheory.HeckeValueId

theorem core (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (P : Ideal (𝓞 E)) (p i : ℕ)
    (yx zx : Sp ℂ ⟶ Xo.X) (ys : LB.Sec (PPx yx)) (zs : LB.Sec (PPx zx)) (C : Subgroup (Over.mk yx ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom yx ⟶ pullback Xo.univ.t.G.hom zx)
    (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G))
    (cr : Fin (Ideal.absNorm P ^ i) → (Over.mk yx ⟶ Xo.univ.t.G))
    (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ) (t0 : ℂ)
    (hp : p.Prime) (hC2 : ∀ a ∈ C, a ^ p ^ 2 = 1) (hk : IsHkIsog p yx zx C ψ ψp)
    (hr : GlobalTheory.ThetaTrace.IsRepsModTors C p cr)
    (hb0 : ∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0)
    (hbt : ∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a)
    (hbr : ∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (hbh : ∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hbv : ∀ (a : Over.mk yx ⟶ Xo.univ.t.G) q (jm : Fin (Ideal.absNorm P ^ i) → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U q →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk zx)) (ψp a)).left ((PPx zx).U (fun _ => q)) (zs.f (fun _ => q)) =
        ∑ m, b q (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk yx)) ((cr m * a) ^ p)).left ((PPx yx).U (fun _ => jm m)) (ys.f (fun _ => jm m)))
    (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (i₁ i₂ : Fin F.n) (Pm : (F.Di i₁).La →+ (Fin g → ℂ)) (Pm' : (F.Di i₂).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i₁) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm)
    (hP' : IsPeriod (F.Di i₂) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm')
    (hu : yx = F.u i₁ Pm) (hu' : zx = F.u i₂ Pm')
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hH : Hm.IsHermitian)
    (him : ∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di i₁).EF a b)
    (hd : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hn : ∀ j z, ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (hc : ∀ j j' z, ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex i₁ Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z)
    (h0 : ∀ j, ⊤ ≤ (F.ex i₁ Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (ha : ∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a)))
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx yx),
      pt ≫ Formalism.L2.PjFree.gxFst yx = (F.ex i₁ Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd yx = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx yx).U (fun _ => j)) (ys.f (fun _ => j)) = θ z * fr j z)
    (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ' : (Fin g → ℂ) → ℂ)
    (him' : ∀ a b, (hermForm Hm' (Pm' a) (Pm' b)).im = (F.Di i₂).EF a b)
    (hd' : ∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hc' : ∀ j j' z, ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (F.ex i₂ Pm' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr' j' z)
    (h0' : ∀ j, ⊤ ≤ (F.ex i₂ Pm' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (ha' : ∀ a j z, ‖χl' (Pm' a)‖ = 1 ∧ (⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' (Pm' a) * Complex.exp (Real.pi * hermForm Hm' z (Pm' a) +
        Real.pi / 2 * hermForm Hm' (Pm' a) (Pm' a)) * fr' j (z + Pm' a)))
    (hv' : ∀ j z (pt : Sp ℂ ⟶ Gx zx),
      pt ≫ Formalism.L2.PjFree.gxFst zx = (F.ex i₂ Pm' z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd zx = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx zx).U (fun _ => j)) (zs.f (fun _ => j)) = t0 * (θ' z * fr' j z)) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (wm : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)),
      (∀ a, ∃ b, h (Pm a) = Pm' b) ∧ (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) ∧
      (∀ m, ∃ b, h (wm m) = Pm' b) ∧
      ∀ w, ∃ j, ⊤ ≤ (F.ex i₂ Pm' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j ∧
        t0 * θ' (h w) * fr' j (h w) = ∑ m, θ ((p : ℂ) • (w + wm m)) * fr' j (h w + h (wm m)) := by
  subst hu hu'
  have hCk : ψp.ker = C := hk.2.2.2.2.2.1
  obtain ⟨gam, h, hg1, hg2, -, hex⟩ := GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog E H Dw l Xo _ g _ F i₁ i₂ Pm Pm' p C
    ψ ψp hP hP' hp hC2 hk
  have eadd := F.ex_add i₁ Pm hP
  have eadd' := F.ex_add i₂ Pm' hP'
  have eker := F.ex_ker i₁ Pm hP
  have eker' := F.ex_ker i₂ Pm' hP'
  have hspan : Submodule.span ℝ (Pm.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hP.2.2.2.1
  have hsmul : ∀ (d : ℂ) z w, hermForm (d • Hm) z w = d * hermForm Hm z w := fun d z w => by
    simp only [hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin g) (Fin g) ℂ, ∀ z, M *ᵥ z = h z :=
    ⟨LinearMap.toMatrix' h.toLinearMap, fun z => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hpR : ((p : ℂ) ^ 2) = (((p : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hHH : ∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w := by
    have key := GlobalTheory.UnitFrameGen.hermForm_eq_of_im _ hspan (((p : ℂ) ^ 2) • Hm) Hm' M (by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      rw [hM, hM, ← hg2, ← hg2, him', hg1, hsmul, hpR, Complex.im_ofReal_mul, him]
      push_cast; ring)
    intro z w
    rw [← hM, ← hM, key, hsmul]
  have hpow : ∀ (m : ℕ) w, F.ex i₁ Pm (m • w) = F.ex i₁ Pm w ^ m := fun m w => by
    induction m with
    | zero => rw [zero_smul, pow_zero]; exact (eker 0).2 ⟨0, map_zero Pm⟩
    | succ m ih => rw [succ_nsmul, eadd, ih, pow_succ]
  have hL : ∀ a ∈ Pm.range, h a ∈ Pm'.range := by
    rintro _ ⟨a, rfl⟩; exact ⟨gam a, hg2 a⟩
  have hhol := GlobalTheory.ClassUniq.isHolTo_ex F i₁ Pm hP
  have hhol' := GlobalTheory.ClassUniq.isHolTo_ex F i₂ Pm' hP'
  have hfr := GlobalTheory.T.heckeIsogeny_appellHumbertFrame_pull_eq_transition_mul E H Dw l Xo (F.u i₁ Pm) (F.u i₂ Pm') p ψp b g Pm.range Pm'.range (F.ex i₁ Pm)
    (F.ex i₂ Pm') h hspan hhol hhol' eadd (fun a ha => (eker a).2 ha) hex hL hb0 hbt hbr (hbh g _ hhol) Hm χl fr hH
    hd hn hc h0 (by rintro _ ⟨a, rfl⟩ j z; exact ha a j z) Hm' χl' fr' hHH hd' hc' h0'
    (by rintro _ ⟨a, rfl⟩ j z; exact ha' a j z)
  choose wm hwm using fun m => F.ex_onto i₁ Pm hP (cr m)
  have hwmΛ : ∀ m, ∃ b', h (wm m) = Pm' b' := fun m => by
    have e1 : F.ex i₂ Pm' (h (wm m)) = 1 := by
      rw [hex, hwm, ← MonoidHom.mem_ker, hCk]; exact hr.1 m
    obtain ⟨b', hb'⟩ := (eker' _).1 e1
    exact ⟨b', hb'.symm⟩
  refine ⟨h, wm, fun a => ⟨gam a, (hg2 a).symm⟩, hHH, hwmΛ, fun w => ?_⟩
  obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex i₂ Pm' (h w)).left
  refine ⟨j, hj, ?_⟩
  have hjz : ⊤ ≤ (ψp (F.ex i₁ Pm w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [← hex]; exact hj
  choose jm hjm using fun m => GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((cr m * F.ex i₁ Pm w) ^ p).left
  have hsum := hbv (F.ex i₁ Pm w) j jm hjz hjm
  have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk (F.u i₂ Pm'))) (ψp (F.ex i₁ Pm w)))
  have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk (F.u i₂ Pm'))) (ψp (F.ex i₁ Pm w)))
  rw [← hex] at hsum e1 e2
  rw [hv' j (h w) _ e1 e2 hj] at hsum
  rw [_root_.mul_assoc, hsum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hq : cr m * F.ex i₁ Pm w = F.ex i₁ Pm (w + wm m) := by rw [← hwm, ← eadd, add_comm]
  have hpw : F.ex i₁ Pm (w + wm m) ^ p = F.ex i₁ Pm ((p : ℂ) • (w + wm m)) := by
    rw [Nat.cast_smul_eq_nsmul, hpow]
  have hjm' := hjm m
  rw [hq, hpw] at hjm' ⊢
  have f1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk (F.u i₁ Pm))) (F.ex i₁ Pm ((p : ℂ) • (w + wm m))))
  have f2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk (F.u i₁ Pm))) (F.ex i₁ Pm ((p : ℂ) • (w + wm m))))
  rw [hv (jm m) _ _ f1 f2 hjm']
  obtain ⟨b', hb'⟩ := hwmΛ m
  have hjw : ⊤ ≤ (F.ex i₂ Pm' (h (w + wm m))).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [map_add (f := _), eadd', hb', (eker' _).2 ⟨b', rfl⟩, _root_.mul_one]; exact hj
  have hf := hfr (w + wm m) j (jm m) hjw hjm'
  rw [map_add (f := _)] at hf
  rw [hf]; ring

theorem hecke_theta_value_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U →
  ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
    admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z →
  ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)) (Pm' : (F.Di (ik k')).La →+ (Fin g → ℂ)),
    IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm →
    IsPeriod (F.Di (ik k')) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm' →
    (U.un k x).x = F.u (ik k) Pm → (U.un k' x').x = F.u (ik k') Pm' →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ' : (Fin g → ℂ) → ℂ),
    Hm'.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) →
    (∀ a b, (hermForm Hm' (Pm' a) (Pm' b)).im = (F.Di (ik k')).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (F.ex (ik k') Pm' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k') Pm' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' (U.un k' x').x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl' (Pm' a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' (Pm' a) * Complex.exp (Real.pi * hermForm Hm' z (Pm' a) +
        Real.pi / 2 * hermForm Hm' (Pm' a) (Pm' a)) * fr' j (z + Pm' a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k' x').x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k' x').x = (F.ex (ik k') Pm' z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k' x').x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k' x').x).U (fun _ => j)) ((U.un k' x').s.f (fun _ => j)) = θ' z * fr' j z) →
  ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (wm : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)),
    (∀ a, ∃ b, h (Pm a) = Pm' b) ∧ (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) ∧
    (∀ m, ∃ b, h (wm m) = Pm' b) ∧
    ∀ w, ∃ j, ⊤ ≤ (F.ex (ik k') Pm' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j ∧
      Formalism.L2.PjFree.toC (t none : CAt σ) * θ' (h w) * fr' j (h w) =
        ∑ m, θ ((p : ℂ) • (w + wm m)) * fr' j (h w + h (wm m)) := by
  intro E _ _ _ H Dw l Xo c σ r U _ _ P p i k k' x x' C z t hA hK hz hb g e F ik Pm Pm' hP hP' hu hu'
    Hm χl fr θ hH _ him hd hn hc h0 ha hv Hm' χl' fr' θ' _ _ him' hd' _ hc' h0' ha' hv'
  obtain ⟨ψ, ψp, n, cr, b, hk, hr, hb0, hbt, hbr, hbh, hbv⟩ := GlobalTheory.T.heckeThetaTrace_values_at_complexPoints E H Dw l Xo c σ p (U.un k x) z C hz
  have hcard : n = Ideal.absNorm P ^ i := by
    letI := fieldCAt σ
    haveI := algClosedCAt σ
    exact GlobalTheory.ThetaTrace.card_reps hA.2.2.1.pos hK hr
  subst hcard
  obtain ⟨hzx, -, hbc⟩ := hb
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) (U.un k' x').x z.x
      (U.un k' x').s z.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hv'' : ∀ j w (pt : Sp ℂ ⟶ Gx z.x), pt ≫ Formalism.L2.PjFree.gxFst z.x = (F.ex (ik k') Pm' w).left →
      pt ≫ Formalism.L2.PjFree.gxSnd z.x = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex (ik k') Pm' w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx z.x).U (fun _ => j)) (z.s.f (fun _ => j)) =
        Formalism.L2.PjFree.toC (t none : CAt σ) * (θ' w * fr' j w) := by
    intro j w pt e1 e2 hj
    have hw0' : (F.ex (ik k') Pm' w).left ≫ Xo.univ.t.G.hom = ((U.un k' x').x : Sp ℂ ⟶ Xo.X) :=
      (Over.w (F.ex (ik k') Pm' w)).trans hu'.symm
    exact GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hzx _ _ _ hbc'
      (Over.homMk (F.ex (ik k') Pm' w).left hw0') j _ _
      (fun pt' h1 h2 => hv' j w pt' h1 h2 hj)
      (fun pt' h1 h2 => by
        obtain rfl : pt' = pt := Limits.pullback.hom_ext (h2.trans e2.symm) (h1.trans e1.symm)
        rfl)
  exact core E H Dw l Xo c σ P p i (U.un k x).x z.x (U.un k x).s z.s C ψ ψp cr b _ hA.2.2.1
    (fun a ha => GlobalTheory.HkPts.pow_eq_one hA.2.2.2.1 hK ha) hk hr hb0 hbt hbr hbh hbv g e F (ik k) (ik k') Pm Pm' hP hP'
    hu (hzx.trans hu') Hm χl fr θ hH him hd hn hc h0 ha hv Hm' χl' fr' θ' him' hd' hc' (by rw [hzx]; exact h0') ha' hv''

end GlobalTheory.HeckeValueId
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFramesStatement
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_theta_value_identity_unitFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U →
  ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
    admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z →
  ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)) (Pm' : (F.Di (ik k')).La →+ (Fin g → ℂ)),
    IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm →
    IsPeriod (F.Di (ik k')) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm' →
    (U.un k x).x = F.u (ik k) Pm → (U.un k' x').x = F.u (ik k') Pm' →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ' : (Fin g → ℂ) → ℂ),
    Hm'.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) →
    (∀ a b, (hermForm Hm' (Pm' a) (Pm' b)).im = (F.Di (ik k')).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (F.ex (ik k') Pm' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k') Pm' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' (U.un k' x').x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl' (Pm' a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' (Pm' a) * Complex.exp (Real.pi * hermForm Hm' z (Pm' a) +
        Real.pi / 2 * hermForm Hm' (Pm' a) (Pm' a)) * fr' j (z + Pm' a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k' x').x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k' x').x = (F.ex (ik k') Pm' z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k' x').x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k' x').x).U (fun _ => j)) ((U.un k' x').s.f (fun _ => j)) = θ' z * fr' j z) →
  ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (wm : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)),
    (∀ a, ∃ b, h (Pm a) = Pm' b) ∧ (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) ∧
    (∀ m, ∃ b, h (wm m) = Pm' b) ∧
    ∀ w, ∃ j, ⊤ ≤ (F.ex (ik k') Pm' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j ∧
      Formalism.L2.PjFree.toC (t none : CAt σ) * θ' (h w) * fr' j (h w) =
        ∑ m, θ ((p : ℂ) • (w + wm m)) * fr' j (h w + h (wm m)) := by
  first | exact @GlobalTheory.HeckeValueId.hecke_theta_value_identity | exact GlobalTheory.HeckeValueId.hecke_theta_value_identity | (intros; apply GlobalTheory.HeckeValueId.hecke_theta_value_identity <;> assumption)
end
