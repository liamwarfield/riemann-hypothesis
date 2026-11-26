module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompare
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineOfKeyDegree
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ShortVectorOfSubmodule
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyDegreeOfBadReduction
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymStability
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymDivisible
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.SaOpen

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginPointCompare
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginPointCompare
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrArch

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_h_torus (A : HermLine ι) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {w : (Σ k, ι k) → ℂ}
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * w p) = ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ + Real.log (A.h w) := by
  have h0 : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [A.smul c w hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (h0 k))
    (A.pos w hw).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (h0 k))]
  simp only [Real.log_zpow]

theorem log_sub_of_sameOrbit {A B : HermLine ι} (hAB : A.a = B.a) {z w : (Σ k, ι k) → ℂ}
    (h : SameOrbit z w) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h w) - Real.log (B.h w) := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [log_h_torus A hc hw, log_h_torus B hc hw, hAB]
  ring

theorem log_add_sum_of_sameOrbit {α : Type} (T : Finset α) {A : HermLine ι} (B : α → HermLine ι)
    (hA : A.a = -∑ j ∈ T, (B j).a) {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z) =
      Real.log (A.h w) + ∑ j ∈ T, Real.log ((B j).h w) := by
  obtain ⟨c, hc, rfl⟩ := h
  simp only [log_h_torus _ hc hw, Finset.sum_add_distrib]
  have h1 : ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ =
      -∑ j ∈ T, ∑ k, ((B j).a k : ℝ) * Real.log ‖c k‖ := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA, Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum, neg_mul, Finset.sum_mul]
  rw [h1]
  ring

end Lines

theorem defect_eq_regWeight_add_bracket :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (x : o.Re.R.X) (x' : o₀.Re.R.X) (w₁ : (Σ k, M.ι k) → ℂ) (w₂ : (Σ k, R.ι k) → ℂ) (v : RootIx D → ℝ) (t : ℝ), 0 < t → t ≤ Sys.t₀ → w₁ ∈ mcPts M.P → w₂ ∈ mcPts R.P → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) w₁ → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') w₂ → o.Re.π x = o₀.Re.π x' → o.Re.π x ∈ Sys.open' → (∀ r, 0 < v r ∧ v r * (o₀.sing r).h w₂ = (o.sing r).h w₁) → ∀ (τ : CMType H) (p : Fin (D.p + D.q)), -∑ k ∈ Finset.Iic p, (Real.log ((M.x t (τ, k)).h w₁) - Real.log ((R.x 1 (τ, k)).h w₂) - Real.log (v (τ, k))) = Sys.phT (some (τ, p)) t (o.Re.π x) + (Real.log ((o₀.Re.ref (some (τ, p))).h w₂) + ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h w₂)) := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ x x' w₁ w₂ v t ht0 htle hw₁ hw₂ hx hx' hπ hop hv τ p
  have hop₀ : o₀.Re.π x' ∈ Sys.open' := hπ ▸ hop

  have hreg := o.fund_reg τ p t ht0 htle w₁ hw₁
  have hline := o.Re.line_eq (some (τ, p)) t ht0 htle x
  have hsc := log_sub_of_sameOrbit (o.Re.line_deg (some (τ, p)) t) hx hw₁.1

  have hs := o.fund_sing τ p x hop
  have hs₀ := o₀.fund_sing τ p x' hop₀
  have hdeg : ∀ (N : Top.RootModel (CMType H) (D.p + D.q)) (S' : Finset ℕ) (Fx' : FixedData Y Sys)
      (q : RootOrigin Y S' N Fx'),
      (q.Re.ref (some (τ, p))).a = -∑ k ∈ Finset.Iic p, (q.sing (τ, k)).a := by
    intro N S' Fx' q
    rw [q.fund_deg τ p]
    simp only [q.sing_deg]
  have hb := log_add_sum_of_sameOrbit (Finset.Iic p) (fun k => o.sing (τ, k)) (hdeg _ _ _ o) hx hw₁.1
  have hb₀ := log_add_sum_of_sameOrbit (Finset.Iic p) (fun k => o₀.sing (τ, k)) (hdeg _ _ _ o₀) hx' hw₂.1

  have hsum : ∑ k ∈ Finset.Iic p, Real.log ((o.sing (τ, k)).h w₁) =
      ∑ k ∈ Finset.Iic p, Real.log (v (τ, k)) + ∑ k ∈ Finset.Iic p, Real.log ((o₀.sing (τ, k)).h w₂) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨h0, h1⟩ := hv (τ, k)
    rw [← h1, Real.log_mul h0.ne' ((o₀.sing (τ, k)).pos w₂ hw₂.1).ne']
  rw [hπ] at hs hline
  simp only [Finset.sum_sub_distrib]
  rw [hπ]
  linarith

end GlobalTheory.CompanionTheory.Ar.OrArch
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginPointCompareStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_point_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (x : o.Re.R.X) (x' : o₀.Re.R.X) (w₁ : (Σ k, M.ι k) → ℂ) (w₂ : (Σ k, R.ι k) → ℂ) (v : RootIx D → ℝ) (t : ℝ), 0 < t → t ≤ Sys.t₀ → w₁ ∈ mcPts M.P → w₂ ∈ mcPts R.P → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) w₁ → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') w₂ → o.Re.π x = o₀.Re.π x' → o.Re.π x ∈ Sys.open' → (∀ r, 0 < v r ∧ v r * (o₀.sing r).h w₂ = (o.sing r).h w₁) → ∀ (τ : CMType H) (p : Fin (D.p + D.q)), -∑ k ∈ Finset.Iic p, (Real.log ((M.x t (τ, k)).h w₁) - Real.log ((R.x 1 (τ, k)).h w₂) - Real.log (v (τ, k))) = Sys.phT (some (τ, p)) t (o.Re.π x) + (Real.log ((o₀.Re.ref (some (τ, p))).h w₂) + ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h w₂)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrArch.defect_eq_regWeight_add_bracket | exact GlobalTheory.CompanionTheory.Ar.OrArch.defect_eq_regWeight_add_bracket | (intros; apply GlobalTheory.CompanionTheory.Ar.OrArch.defect_eq_regWeight_add_bracket <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsLeft
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLineLargeDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyBadReductionHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyBadReductionHolds
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KP

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem key_bad : KeyBadSt := PositivityTheory.HtPt.Kftwo.kp

end GlobalTheory.CompanionTheory.Ar.Sl.KP
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyBadReductionHoldsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.key_bad_reduction_holds : KeyBadSt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KP.key_bad | exact GlobalTheory.CompanionTheory.Ar.Sl.KP.key_bad | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KP.key_bad <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLargeDegreeLine
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLargeDegreeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.TopSlope

open GroundTheory.Heights₂.Heights.ComplexAt

theorem tmul_eq_smul_one {K : Type} [Field K] (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module (𝓞 K) M]
    (z : ComplexAt σ) (m : M) :
    (z ⊗ₜ[𝓞 K] m : Fibre σ M) = ((ofComplex σ).symm z : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] m) := by
  rw [smul_tmul', ComplexAt.complex_smul_def, AlgEquiv.apply_symm_apply, _root_.mul_one]

theorem exists_isometric_ext {K L' : Type} [Field K] [NumberField K] [Field L'] [NumberField L'] [Algebra K L']
    (B : HermitianBundle.{0} K) (B' : HermitianBundle.{0} L')
    (io : B.carrier →ₛₗ[algebraMap (𝓞 K) (𝓞 L')] B'.carrier)
    (hio : ∀ (σ' : L' →+* ℂ) (x y : B.carrier),
      ((B'.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io y) : ℂ) =
        ((B.metric.form (σ'.comp (algebraMap K L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 K] x)
          ((1 : ComplexAt _) ⊗ₜ[𝓞 K] y) : ℂ)) :
    ∃ Φ : (B.baseChange L').carrier →+ B'.carrier, ∀ (σ' : L' →+* ℂ) (x y : (B.baseChange L').carrier),
      ((B'.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] Φ x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] Φ y) : ℂ) =
        (((B.baseChange L').metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] x)
          ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] y) : ℂ) := by
  let f : 𝓞 L' →+ B.carrier →+ B'.carrier :=
    { toFun := fun a => (DistribSMul.toAddMonoidHom B'.carrier a).comp io.toAddMonoidHom
      map_zero' := by ext e; simp
      map_add' := by intro a b; ext e; simp [add_smul] }
  have hf : ∀ (r : 𝓞 K) (a : 𝓞 L') (e : B.carrier), f (r • a) e = f a (r • e) := by
    intro r a e
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_comp, Function.comp_apply,
      DistribSMul.toAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe, LinearMap.map_smulₛₗ,
      Algebra.smul_def, mul_smul, smul_comm a]
  let Φ0 : 𝓞 L' ⊗[𝓞 K] B.carrier →+ B'.carrier := TensorProduct.liftAddHom f hf
  have hΦ : ∀ (a : 𝓞 L') (e : B.carrier), Φ0 (a ⊗ₜ e) = a • io e := fun a e => by
    simp [Φ0, f, TensorProduct.liftAddHom_tmul]
  refine ⟨Φ0, fun σ' => ?_⟩
  have hL : ∀ u v : B'.carrier, ((B'.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] u)
      ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] v) : ℂ) = inner ℂ (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ u))
      (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ v)) := fun _ _ => rfl
  have hR : ∀ u v : 𝓞 L' ⊗[𝓞 K] B.carrier, (((B.baseChange L').metric.form σ').inner
      ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] u) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] v) : ℂ) =
      inner ℂ (FibreSpace.equiv B.metric _ (baseChangeCoord σ' ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] u)))
        (FibreSpace.equiv B.metric _ (baseChangeCoord σ' ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] v))) := fun _ _ => rfl
  have hB : ∀ u v : B.carrier, inner ℂ (FibreSpace.equiv B.metric (σ'.comp (algebraMap K L')) (1 ⊗ₜ u))
      (FibreSpace.equiv B.metric _ (1 ⊗ₜ v)) = inner ℂ (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ io u))
      (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ io v)) := fun u v => (hio σ' u v).symm
  have h1 : ∀ (a : 𝓞 L') (e : B.carrier), ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] Φ0 (a ⊗ₜ e)) =
      (σ' (a : L')) • ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io e) := by
    intro a e
    rw [hΦ, ← smul_tmul, tmul_eq_smul_one]
    congr 1
    rw [smul_def, _root_.mul_one, AlgEquiv.symm_apply_apply]
  have h2 : ∀ (a : 𝓞 L') (e : B.carrier), baseChangeCoord σ' ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] (a ⊗ₜ e)) =
      (σ' (a : L')) • ((1 : ComplexAt (σ'.comp (algebraMap K L'))) ⊗ₜ[𝓞 K] e) := by
    intro a e
    rw [baseChangeCoord_tmul, tmul_eq_smul_one]
    congr 1
    show σ' (a : L') * 1 = σ' (a : L')
    rw [_root_.mul_one]
  have key : ∀ x y : 𝓞 L' ⊗[𝓞 K] B.carrier,
      inner ℂ (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ Φ0 x)) (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ Φ0 y)) =
      inner ℂ (FibreSpace.equiv B.metric _ (baseChangeCoord σ' ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] x)))
        (FibreSpace.equiv B.metric _ (baseChangeCoord σ' ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] y))) := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, tmul_zero, inner_zero_left]
    | add x x' hx hx' => simp only [map_add (f := _), tmul_add, inner_add_left, hx, hx']
    | tmul a e =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, tmul_zero, inner_zero_right]
      | add y y' hy hy' => simp only [map_add (f := _), tmul_add, inner_add_right, hy, hy']
      | tmul b e' =>
        rw [h1, h1, h2, h2, map_smul, map_smul, map_smul, map_smul, inner_smul_left, inner_smul_left,
          inner_smul_right, inner_smul_right, hB]
  intro x y
  exact (hL _ _).trans ((key x y).trans (hR x y).symm)

end GlobalTheory.CompanionTheory.Ar.Sl.TopSlope

namespace GlobalTheory.CompanionTheory.Ar.Sl.TopSlope

theorem slopeBound (hS7 : LineOfLargeDegree.Statement) (hKey : KeyDegSt) : SlopeBoundSt ∧ Prov.LemmaS := by
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.line_of_key_degree hKey
  have hS : SlopeBoundSt := by
    refine ⟨C + 2, by linarith, ?_⟩
    intro E _ _ _ H L _ _ t tK m princ B MB fib
    let D : PPData H L := ⟨t, tK, m, princ, B, MB, fib⟩
    set ℓ := Real.log (2 + (Module.finrank (𝓞 L) B.carrier : ℝ) + max (-B.normDegree ⊤) 0) with hℓ
    have hpos : 0 ≤ max (-B.normDegree ⊤) 0 := le_max_right _ _
    have hℓ2 : Real.log 2 ≤ ℓ := by
      apply Real.log_le_log (by norm_num)
      have : (0 : ℝ) ≤ (Module.finrank (𝓞 L) B.carrier : ℝ) := Nat.cast_nonneg _
      linarith
    have hℓ0 : 2 / 3 ≤ ℓ := by
      have := Real.log_two_gt_d9
      linarith
    have hg : Real.log (Module.finrank (𝓞 L) B.carrier : ℝ) ≤ ℓ := by
      rcases Nat.eq_zero_or_pos (Module.finrank (𝓞 L) B.carrier) with h | h
      · rw [h, Nat.cast_zero, Real.log_zero]; linarith
      · apply Real.log_le_log (by exact_mod_cast h)
        linarith
    simp only [HermitianBundle.slopeMax]
    refine iSup₂_le fun F hF => ?_
    rw [EReal.coe_le_coe_iff]
    obtain ⟨L', iF, iN, iA, x, -, hx⟩ := GlobalTheory.CompanionTheory.Ar.Lines.short_vector_of_submodule hS7 L B F hF
    obtain ⟨⟨D', e⟩⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').1
    obtain ⟨hg', hh', io, -, -, hio⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').2 D' e
    obtain ⟨Φ, hΦ⟩ := exists_isometric_ext D.B D'.B io hio
    have hlen : ∀ σ : L' →+* ℂ, D'.len σ (Φ x) = Real.sqrt ((((B.baseChange L').metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 L'] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L'] x) : ℂ).re) := by
      intro σ
      simp only [PPData.len]
      rw [hΦ]
    have hline : -mean L' (fun σ => Real.log (D'.len σ (Φ x))) ≤ C * ℓ := by
      by_cases h0 : Φ x = 0
      · have hz : ∀ σ : L' →+* ℂ, D'.len σ (Φ x) = 0 := by
          intro σ
          simp only [PPData.len, h0, tmul_zero]
          have : ((D'.B.metric.form σ).inner (0 : Fibre σ D'.B.carrier) 0 : ℂ) = 0 :=
            inner_zero_left (𝕜 := ℂ) (x := (0 : FibreSpace D'.B.metric σ))
          rw [this, Complex.zero_re, Real.sqrt_zero]
        simp only [hz, Real.log_zero, mean, Finset.sum_const_zero, zero_div, neg_zero]
        exact mul_nonneg hC0 (by linarith)
      · have := hC E H L' D' (Φ x) h0
        rw [hg', hh'] at this
        exact this
    simp only [hlen] at hline
    have hexp : (C + 2) * ℓ = C * ℓ + 2 * ℓ := by ring
    rw [hexp]
    linarith
  exact ⟨hS, hS⟩

end GlobalTheory.CompanionTheory.Ar.Sl.TopSlope
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLargeDegreeLineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_bound_of_large_degree_line : LineOfLargeDegree.Statement → KeyDegSt → SlopeBoundSt ∧ Prov.LemmaS := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TopSlope.slopeBound | exact GlobalTheory.CompanionTheory.Ar.Sl.TopSlope.slopeBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TopSlope.slopeBound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLineLargeDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem slopeBound_and_lemmaS_of_siegel :
    LineOfLargeDegree.Statement → SlopeBoundSt ∧ Prov.LemmaS := fun hS =>
  GlobalTheory.T.slope_bound_of_large_degree_line hS (GlobalTheory.T.key_degree_of_bad_reduction GlobalTheory.T.key_bad_reduction_holds)

end GlobalTheory.CompanionTheory.Ar.Sl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLineLargeDegreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_bound_of_line_large_degree : LineOfLargeDegree.Statement → SlopeBoundSt ∧ Prov.LemmaS := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel | exact GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianStatementHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianStatementHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem saStatement_holds : ReciprocityTheory.ChartRestriction.G.SA.SAStatement := PositivityTheory.EqVol.sa

end GlobalTheory.CompanionTheory.Ar.Link
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianStatementHoldsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semi_abelian_statement_holds : ReciprocityTheory.ChartRestriction.G.SA.SAStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.saStatement_holds | exact GlobalTheory.CompanionTheory.Ar.Link.saStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.saStatement_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsLeft
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem given_of_inputs : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → Top.Given :=
  fun hModel hKey hSAH hSegre hResK hFar hGaga hLLD hPB hHS hAn hNine =>
    ⟨hModel, hKey, hSAH, hSegre, hResK, GlobalTheory.T.semi_abelian_statement_holds, hFar, hGaga, (GlobalTheory.T.slope_bound_of_line_large_degree hLLD).1, hPB, hHS, hAn, hNine,
      GroundTheory.Heights₂.Heights.AntisymPerturbation.proof (GroundTheory.Heights₂.Heights.AntisymStability.proof GroundTheory.Heights₂.Heights.AntisymDivisible.proof)⟩

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsLeftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.final_theorem_of_inputs_left : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → Top.Given := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.given_of_inputs | exact GlobalTheory.CompanionTheory.Ar.Top.given_of_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.given_of_inputs <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareThird
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareThird
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.ALine

section Cross

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Cmp

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] {Ω : Type} [Field Ω]

theorem cross_mem (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ b₁ : ι₁ k₁) (a₂ b₂ : ι₂ k₂)
    (h : y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ = y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩) :
    (X (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) * X (joinInr ι₁ ι₂ ⟨k₂, b₂⟩) +
        -(X (joinInl ι₁ ι₂ ⟨k₁, b₁⟩) * X (joinInr ι₁ ι₂ ⟨k₂, a₂⟩)) : MRing (joinIdx ι₁ ι₂)) ∈
      mCoordIdeal (joinVec y₁ y₂) := by
  classical
  have hl : ∀ a : ι₁ k₁, IsMultiHomog (X (joinInl ι₁ ι₂ ⟨k₁, a⟩) : MRing (joinIdx ι₁ ι₂))
      (Pi.single (Sum.inl k₁) 1) := fun a => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inl k₁) a
  have hr : ∀ a : ι₂ k₂, IsMultiHomog (X (joinInr ι₁ ι₂ ⟨k₂, a⟩) : MRing (joinIdx ι₁ ι₂))
      (Pi.single (Sum.inr k₂) 1) := fun a => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inr k₂) a
  refine Small.LineModel.mem_of_aeval _
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhAdd (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul (hl a₁) (hr b₂))
      (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhNeg (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul (hl b₁) (hr a₂)))) ?_
  simp only [map_add (f := _), map_neg, map_mul, aeval_X]
  show y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ + -(y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩) = 0
  rw [h]; ring

theorem cross_eq (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ b₁ : ι₁ k₁) (a₂ b₂ : ι₂ k₂)
    (h : y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ = y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩)
    {L : Type} [Field L] {z : (Σ k, joinIdx ι₁ ι₂ k) → L}
    (hz : z ∈ Small.ptsOver L (mCoordIdeal (joinVec y₁ y₂))) :
    z (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) * z (joinInr ι₁ ι₂ ⟨k₂, b₂⟩) =
      z (joinInl ι₁ ι₂ ⟨k₁, b₁⟩) * z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩) := by
  have h0 := hz.2 _ (cross_mem y₁ y₂ a₁ b₁ a₂ b₂ h)
  simp only [map_add (f := _), map_neg, map_mul, aeval_X] at h0
  linear_combination h0

theorem hasVal_one (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ : ι₁ k₁) (a₂ : ι₂ k₂) (h : y₁ ⟨k₁, a₁⟩ = y₂ ⟨k₂, a₂⟩)
    (d : K₁ ⊕ K₂ → ℤ) (hd₁ : d (Sum.inl k₁) = 1) (hd₂ : d (Sum.inr k₂) = -1)
    (hd : ∀ k, k ≠ Sum.inl k₁ → k ≠ Sum.inr k₂ → d k = 0)
    {L : Type} [Field L] (z : (Σ k, joinIdx ι₁ ι₂ k) → L)
    (hz : z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩) ≠ 0) :
    Small.HasVal (joinVec y₁ y₂) d 1 z
      (z (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) / z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩)) := by
  classical
  refine ⟨Pi.single (Sum.inl k₁) 1, Pi.single (Sum.inr k₂) 1, X (joinInl ι₁ ι₂ ⟨k₁, a₁⟩),
    X (joinInr ι₁ ι₂ ⟨k₂, a₂⟩), ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inl k₁) a₁,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inr k₂) a₂, fun k => ?_, ?_, ?_, ?_⟩
  · by_cases e₁ : k = Sum.inl k₁
    · subst e₁; simp [hd₁]
    · by_cases e₂ : k = Sum.inr k₂
      · subst e₂; simp [hd₂]
      · simp [hd k e₁ e₂, e₁, e₂]
  · simp only [aeval_X, one_mul]
    exact h
  · simpa only [aeval_X] using hz
  · simp only [aeval_X]
    field_simp

end Cross

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 ∧ ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), ∀ v : ℂ, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 w v → M.A.h (fun p => w (Cmp.joinInl M.ι R.ι p)) = ‖v‖ * R.A.h (fun p => w (Cmp.joinInr M.ι R.ι p)) := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi
  classical
  have hy : ∀ a, M.y ⟨o.k₀, o.ix a⟩ = i (R.y ⟨o₀.k₀, o₀.ix a⟩) := fun a => by
    rw [o.y_eq, o₀.y_eq, ← hi]; rfl
  have hd₁ : Ht.joinDeg M R none (Sum.inl o.k₀) = 1 := o.A_deg.1
  have hd₂ : Ht.joinDeg M R none (Sum.inr o₀.k₀) = -1 := by
    show -(R.A.a o₀.k₀) = -1
    rw [o₀.A_deg.1]
  have hd : ∀ k, k ≠ Sum.inl o.k₀ → k ≠ Sum.inr o₀.k₀ → Ht.joinDeg M R none k = 0 := by
    rintro (k | k) h₁ h₂
    · exact o.A_deg.2 k fun e => h₁ (congrArg _ e)
    · show -(R.A.a k) = 0
      rw [o₀.A_deg.2 k fun e => h₂ (congrArg _ e), neg_zero]
  have hval : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L) (a : Fin (Fx.m + 1)),
      z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 →
      Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 z
        (z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) / z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩)) :=
    fun L _ z a hz => hasVal_one M.y (fun p => i (R.y p)) (o.ix a) (o₀.ix a) (hy a) _ hd₁ hd₂ hd z hz
  have hcr : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) → ∀ a b : Fin (Fx.m + 1),
      z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) * z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b⟩) =
        z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b⟩) * z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) :=
    fun L _ z hz a b => cross_eq M.y (fun p => i (R.y p)) (o.ix a) (o.ix b) (o₀.ix a) (o₀.ix b) (by
      show M.y _ * i (R.y _) = M.y _ * i (R.y _)
      rw [hy a, hy b, mul_comm]) hz
  have hexR : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) →
      ∃ a : Fin (Fx.m + 1), z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 := by
    intro L _ z hz
    obtain ⟨p, hp⟩ := hz.1 (Sum.inr o₀.k₀)
    have e : o₀.ix (o₀.ix.symm p) = p := o₀.ix.apply_symm_apply p
    exact ⟨o₀.ix.symm p, fun h0 =>
      hp ((congrArg (fun x : R.ι o₀.k₀ => z ⟨Sum.inr o₀.k₀, x⟩) e.symm).trans h0)⟩
  have hexM : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) →
      ∃ a : Fin (Fx.m + 1), z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) ≠ 0 := by
    intro L _ z hz
    obtain ⟨p, hp⟩ := hz.1 (Sum.inl o.k₀)
    have e : o.ix (o.ix.symm p) = p := o.ix.apply_symm_apply p
    exact ⟨o.ix.symm p, fun h0 =>
      hp ((congrArg (fun x : M.ι o.k₀ => z ⟨Sum.inl o.k₀, x⟩) e.symm).trans h0)⟩
  have hne : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) → ∀ a : Fin (Fx.m + 1),
      z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 → z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) ≠ 0 := by
    intro L _ z hz a ha h0
    obtain ⟨b, hb⟩ := hexM L z hz
    have h1 := hcr L z hz b a
    rw [h0, zero_mul] at h1
    exact mul_ne_zero hb ha h1
  refine ⟨fun L _ _ z hz => ?_, fun w hw v hv => ?_⟩
  · obtain ⟨a, ha⟩ := hexR L z hz
    exact ⟨_, div_ne_zero (hne L z hz a ha) ha, hval L z a ha⟩
  · obtain ⟨a, ha⟩ := hexR ℂ w hw
    have hv' := Small.LineModel.hasVal_unique _ _ _ hw hv (hval ℂ w a ha)
    have hvne : v ≠ 0 := hv' ▸ div_ne_zero (hne ℂ w hw a ha) ha
    have hblock : ∀ b : Fin (Fx.m + 1), w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b⟩) =
        v * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b⟩) := by
      intro b
      rw [hv', div_mul_eq_mul_div, eq_div_iff ha]
      exact hcr ℂ w hw b a
    obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main (CMType H) (D.p + D.q) M R i).2.2.1 ℂ w hw
    rw [Small.LineModel.ptsOver_complex] at h1 h2
    let c : R.K → ℂ := fun k => if k = o₀.k₀ then v else 1
    have hc : ∀ k, c k ≠ 0 := by
      intro k
      by_cases hk : k = o₀.k₀
      · simpa [c, hk] using hvne
      · simp [c, hk]
    have e1 := o.A_h _ h1
    have e2 := o₀.A_h _ (mcPts_smul R.arith.2.1.2.1 c hc h2)
    have e3 := R.A.smul c (fun p => w (Cmp.joinInr M.ι R.ι p)) hc
    have e4 : (∏ k, ‖c k‖ ^ R.A.a k) = ‖v‖ := by
      rw [Finset.prod_eq_single o₀.k₀]
      · simp [c, o₀.A_deg.1]
      · intro k _ hk
        simp [c, hk, o₀.A_deg.2 k hk]
      · simp
    rw [e1, ← e4, ← e3, e2]
    congr 1
    funext b
    simpa [c] using hblock b

end GlobalTheory.CompanionTheory.Ar.Ht.ALine
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareThirdStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_compare_third : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 ∧ ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), ∀ v : ℂ, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 w v → M.A.h (fun p => w (Cmp.joinInl M.ι R.ι p)) = ‖v‖ * R.A.h (fun p => w (Cmp.joinInr M.ι R.ι p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.ALine.main | exact GlobalTheory.CompanionTheory.Ar.Ht.ALine.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.ALine.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareSecond
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareSecond
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.JoinPts

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_zero_of_mem (y : (Σ k, ι k) → Ω) {g : MRing ι} (h : g ∈ mCoordIdeal y) : aeval y g = 0 := by
  have h0 : mConeMap y g = 0 := (RingHom.mem_ker).1 h
  have e : ((aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ).comp (mConeMap y) =
      aeval y := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap]
  rw [← e, AlgHom.comp_apply, h0, map_zero]

theorem aeval_map_hom {Ω' : Type} [Field Ω'] (i : Ω →+* Ω') (y : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (fun p => i (y p)) g = i (aeval y g) := by
  have e : (aeval (fun p => i (y p)) : MRing ι →ₐ[ℤ] Ω') = (i.toIntAlgHom).comp (aeval y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp
  rw [e]
  rfl

theorem cross_mem (y : (Σ k, ι k) → Ω) (p q p' q' : Σ k, ι k) (hp : p'.1 = p.1) (hq : q'.1 = q.1)
    (h : y p * y q' = y p' * y q) :
    (X p * X q' - X p' * X q : MRing ι) ∈ mCoordIdeal y := by
  refine (RingHom.mem_ker).2 ?_
  have e : (C (y p) * C (y q') : MvPolynomial K Ω) = C (y p') * C (y q) := by
    rw [← C_mul, ← C_mul, h]
  have hx : mConeMap y (X p * X q' - X p' * X q : MRing ι) =
      C (y p) * X p.1 * (C (y q') * X q'.1) - C (y p') * X p'.1 * (C (y q) * X q.1) := by
    simp [mConeMap]
  rw [hx, hp, hq]
  linear_combination (X p.1 * X q.1) * e

theorem exists_smul_of_cross {κ : Type} {u v : κ → ℂ} (hv : v ≠ 0) (h : ∀ a b, u a * v b = u b * v a) :
    ∃ t : ℂ, u = t • v := by
  obtain ⟨b, hb⟩ := Function.ne_iff.1 hv
  have hb' : v b ≠ 0 := hb
  refine ⟨u b / v b, funext fun a => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  exact h a b

end Forms

theorem coordsAt_smul {X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X'} {K : Type}
    {ι : K → Type} {y : (Σ k, ι k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X'} {w : (Σ k, ι k) → ℂ}
    (h : CoordsAt ξ y z w) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : CoordsAt ξ y z (fun p => c p.1 * w p) := by
  refine ⟨fun k => ?_, fun k a ha => ?_⟩
  · obtain ⟨a, ha⟩ := h.1 k
    exact ⟨a, (isUnit_iff_ne_zero.2 (hc k)).mul ha⟩
  · have ha' : IsUnit (w ⟨k, a⟩) := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul ha.ne_zero)
    obtain ⟨hy, hr⟩ := h.2 k a ha'
    refine ⟨hy, fun i => ?_⟩
    obtain ⟨r, h1, h2⟩ := hr i
    refine ⟨r, h1, ?_⟩
    show c k * w ⟨k, i⟩ = r * (c k * w ⟨k, a⟩)
    rw [h2]
    ring

section Origin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {M : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}

theorem mono_coeff (c : Coeff l) : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { }
  have := IsPreimmersion.of_isLocalization (S := c.F) (nonZeroDivisors (𝓞 c.F))
  exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F))))

theorem exists_form (o : RootOrigin Y S M Fx) :
    ∃ b : MRing M.ι, aeval M.y b ≠ 0 ∧ ∀ w ∈ mcPts M.P, aeval w b ≠ 0 →
      ∃ z : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X, CoordsAt o.𝔐.ξ M.y z w ∧ o.𝔐.Interior z := by
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨-, ⟨x, hx⟩, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) _ Y S M.Ω M.K M.ι M.y o.𝔐 hinj
  obtain ⟨b, d, hd, hb, hw⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l Xo c (𝓞 c.F) _ Y S M.Ω M.K M.ι M.y o.𝔐 x hx (mono_coeff c)
  refine ⟨b, fun h => hb (Small.LineModel.mem_of_aeval M.y hd h), fun w hw' hne => hw w hw' ?_⟩
  rw [Cmp.evC, Small.LineModel.eval_map_eq]
  exact hne

theorem exists_lift (o : RootOrigin Y S M Fx) (hJ : o.Re.J = ⊤) {w : (Σ k, M.ι k) → ℂ} (hw : w ∈ mcPts M.P)
    {z : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X} (hz : CoordsAt o.𝔐.ξ M.y z w) (hI : o.𝔐.Interior z) :
    ∃ x : o.Re.R.X, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) w ∧ o.Re.π x ∈ Sys.open' ∧
      ∃ t : ℂ, Fx.pt (o.Re.π x) = t • fun a => w ⟨o.k₀, o.ix a⟩ := by
  have hnot : w ∉ mcPts o.Re.J := by
    rw [hJ]
    intro h
    have := h.2 1 Submodule.mem_top
    simp at this
  obtain ⟨x, hx⟩ := o.Re.R.surj w hw hnot
  obtain ⟨k, hk, hxw⟩ := id hx
  refine ⟨x, hx, ?_, ?_⟩
  · have hC : CoordsAt o.𝔐.ξ M.y z (o.Re.R.lift x x) := by
      rw [hxw]
      exact coordsAt_smul hz hk
    exact (o.interior x z hC).1 hI
  · obtain ⟨α, hα, h⟩ := TowerOriginModel.pi_pt_ne o x
    refine ⟨α⁻¹ * k o.k₀, funext fun a => ?_⟩
    have h1 := congrFun h a
    rw [hxw] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_assoc, h1, inv_mul_cancel_left₀ hα]

end Origin

theorem join_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → o.Re.J = ⊤ → o₀.Re.J = ⊤ → ∃ f : MRing (Cmp.joinIdx M.ι R.ι), f ∉ mCoordIdeal (Ht.joinOf M R i) ∧ ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∃ (x : o.Re.R.X) (x' : o₀.Re.R.X) (z₁ : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ o₀.𝔐.X), ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧ o.Re.π x = o₀.Re.π x' ∧ o.Re.π x ∈ Sys.open' ∧ CoordsAt o.𝔐.ξ M.y z₁ (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧ CoordsAt o₀.𝔐.ξ R.y z₂ (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧ o.𝔐.Interior z₁ ∧ o₀.𝔐.Interior z₂ := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi hJ hJ₀
  classical
  obtain ⟨b, hb, hbw⟩ := exists_form o
  obtain ⟨b₀, hb₀, hbw₀⟩ := exists_form o₀
  have eL : (Ht.joinOf M R i) ∘ Cmp.joinInl M.ι R.ι = M.y := rfl
  have eR : (Ht.joinOf M R i) ∘ Cmp.joinInr M.ι R.ι = fun p => i (R.y p) := rfl
  refine ⟨rename (Cmp.joinInl M.ι R.ι) b * rename (Cmp.joinInr M.ι R.ι) b₀, fun h => ?_, fun w hw hf => ?_⟩
  · have h0 := aeval_eq_zero_of_mem _ h
    rw [map_mul, aeval_rename, aeval_rename, eL, eR, aeval_map_hom] at h0
    exact (mul_ne_zero hb ((map_ne_zero i).2 hb₀)) h0
  · obtain ⟨hw₁, hw₂⟩ := (GlobalTheory.T.join_model_points_project (CMType H) (D.p + D.q) M R i).2.2.1 ℂ w hw
    rw [Small.LineModel.ptsOver_complex] at hw₁ hw₂
    rw [Cmp.evC, Small.LineModel.eval_map_eq, map_mul, aeval_rename, aeval_rename] at hf
    obtain ⟨z₁, hz₁, hI₁⟩ := hbw _ hw₁ (left_ne_zero_of_mul hf)
    obtain ⟨z₂, hz₂, hI₂⟩ := hbw₀ _ hw₂ (right_ne_zero_of_mul hf)
    obtain ⟨x, hx, hxo, t, ht⟩ := exists_lift o hJ hw₁ hz₁ hI₁
    obtain ⟨x', hx', -, t', ht'⟩ := exists_lift o₀ hJ₀ hw₂ hz₂ hI₂
    refine ⟨x, x', z₁, z₂, hx, hx', ?_, hxo, hz₁, hz₂, hI₁, hI₂⟩
    have hcross : ∀ a b', w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b'⟩) =
        w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b'⟩) * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) := by
      intro a b'
      have hm := cross_mem (Ht.joinOf M R i) (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩)
        (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b'⟩)
        (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b'⟩) rfl rfl (by
          show M.y _ * i (R.y _) = M.y _ * i (R.y _)
          have hg : ∀ u, i (o₀.g u) = o.g u := fun u => congrArg (fun φ : Fx.Ωf →+* M.Ω => φ u) hi
          rw [o.y_eq, o.y_eq, o₀.y_eq, o₀.y_eq, hg, hg]
          ring)
      have h0 := hw.2 _ hm
      simp only [map_sub, map_mul, aeval_X] at h0
      exact sub_eq_zero.1 h0
    obtain ⟨s, hs⟩ := exists_smul_of_cross (u := Fx.pt (o.Re.π x)) (v := Fx.pt (o₀.Re.π x')) (Fx.pt_ne _)
      (fun a b' => by
        rw [ht, ht']
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (t * t') * hcross a b')
    exact Fx.pt_inj _ _ s hs

end GlobalTheory.CompanionTheory.Ar.JoinPts
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareSecondStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_compare_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → o.Re.J = ⊤ → o₀.Re.J = ⊤ → ∃ f : MRing (Cmp.joinIdx M.ι R.ι), f ∉ mCoordIdeal (Ht.joinOf M R i) ∧ ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∃ (x : o.Re.R.X) (x' : o₀.Re.R.X) (z₁ : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ o₀.𝔐.X), ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧ o.Re.π x = o₀.Re.π x' ∧ o.Re.π x ∈ Sys.open' ∧ CoordsAt o.𝔐.ξ M.y z₁ (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧ CoordsAt o₀.𝔐.ξ R.y z₂ (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧ o.𝔐.Interior z₁ ∧ o₀.𝔐.Interior z₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.JoinPts.join_points | exact GlobalTheory.CompanionTheory.Ar.JoinPts.join_points | (intros; apply GlobalTheory.CompanionTheory.Ar.JoinPts.join_points <;> assumption)
end
end
