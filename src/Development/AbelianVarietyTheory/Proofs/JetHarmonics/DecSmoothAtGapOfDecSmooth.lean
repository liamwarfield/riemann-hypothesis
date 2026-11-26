module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.KFinDecayOfDecInf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InvariantOperatorValueTriangularChange
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecSmoothAtGapOfDecSmooth
section -- merged from Development.AbelianVarietyTheory.BlockTheory.JetGauges.SideNormalisedGap
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap

open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU IsOrthProjOnto InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def dimV (k r : ℕ) : ℝ := 2 * (r : ℝ) + k + 1

def decExp (r : ℕ) (h : ℝ) : ℝ := h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))

def decConst (r : ℕ) (h : ℝ) : ℝ := Real.exp (h / (16 * ((r : ℝ) + 1)))

def dimN (k r : ℕ) : ℝ := (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2

def thrG (k r : ℕ) : ℝ := 4 * ((k : ℝ) + r) * ((r : ℝ) + 1)

def thrS (k r : ℕ) : ℝ := (dimV k r - 1) * dimN k r

def propExp (r : ℕ) : ℝ := 2 * ((r : ℝ) ^ 2 + r + 1)

def thrSS (k r : ℕ) : ℝ := 2 * propExp r * thrS k r + 1

def DecGap (k r : ℕ) (h : ℝ) : Prop := 120 * dimV k r * ((r : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤ h

def Size (k r : ℕ) (h : ℝ) : Prop :=
  DecGap k r h ∧ 16 * dimV k r ^ 5 * Real.sqrt (2 * ((r : ℝ) + 1)) ≤ h

def Thresholds (k r : ℕ) (a : ℝ) : Prop :=
  thrG k r < a / 2 ∧ thrS k r < a / 2 ∧ thrSS k r + thrG k r + 1 ≤ a ∧ thrS k r < a - 1

def mulP {k r : ℕ} (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

theorem measurable_mulP {k r : ℕ} : Measurable (mulP (k := k) (r := r)) := by
  unfold mulP
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  fun_prop

def muS {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) := (μW.prod μN).map mulP

section Side

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

def IsSide (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r)) : Prop :=
  1 ≤ k ∧
  (IsHCParam lam ∧ IsDSHpk k r ε lam σ ∧ GapAtLeast ε lam h) ∧
  IsLowUnitH k r ε lam σ w₀ ∧
  (inWb k r z ∧ 0 < Tz k r z) ∧
  c ≠ 0 ∧
  (IsHCParam u ∧ IsHCTypeW k r z u π) ∧
  (PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW ∧ PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN ∧
    PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) ∧
  (SigmaFinite ν ∧ PI.BesselPeriodGGP.IsQuotMeas μG (muS μW μN) ν)

def IsSideNormalised (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r)) : Prop :=
  IsSide k r ε lam h σ w₀ z c u π μW μN μG ν ∧ μW Set.univ = 1

def KFinDecay (k r : ℕ) (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ v v' : H, IsKFinHpk (k := k) (r := r) σ v → IsKFinHpk (k := k) (r := r) σ v' →
    ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪v', σ x v⟫_ℂ‖ ≤ C * gN x ^ (-a)

def wordSeminorm {k r : ℕ} (σ : Mat k r → (H →L[ℂ] H)) (Ws : List (List (Mat k r))) (w : H) : ℝ :=
  (Ws.map fun D => ‖dsigW (k := k) (r := r) σ D w‖).sum

end Side

def DecKFin : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → DecGap k r h →
    KFinDecay k r σ (decExp r h)

def DecSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ),
    IsHCParam lam → IsDSHpk k r ε lam σ → KFinDecay k r σ a →
    ∀ v₀ : H, IsKFinHpk (k := k) (r := r) σ v₀ →
      ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ D ∈ Ws, ∀ X ∈ D, InLieHpk k r X) ∧
        ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
          ‖⟪v₀, σ x w⟫_ℂ‖ ≤ C * wordSeminorm σ Ws w * gN x ^ (1 - a)

end GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SigmaFiniteOfPosLintegralNeTop
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.QuotientMeasureSigmaFinite

theorem sigmaFinite_of_pos_lintegral_ne_top {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {g : X → ℝ≥0∞} (hg : Measurable g) (hpos : ∀ x, g x ≠ 0) (hfin : ∫⁻ x, g x ∂ν ≠ ∞) :
    SigmaFinite ν := by
  refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    have h0 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
    have h1 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
    exact (meas_ge_le_lintegral_div hg.aemeasurable h0 h1).trans_lt (ENNReal.div_lt_top hfin h0)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hpos x)
    refine Set.mem_sUnion.2 ⟨_, ⟨n, rfl⟩, ?_⟩
    show ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x
    exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le

theorem measurable_mul_pair (k r : ℕ) :
    Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem sigmaFinite_of_isQuotMeas {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    [SigmaFinite μG] [SFinite μS] (hS : μS ≠ 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS ν) : SigmaFinite ν := by
  obtain ⟨h, hpos, hmeas, hint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hne : ∀ y, h y ≠ 0 := fun y => (hpos y).ne'
  have hF : Measurable fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ((h (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) : NNReal) : ℝ≥0∞) :=
    (measurable_coe_nnreal_ennreal.comp hmeas).comp (measurable_mul_pair k r)
  have hq' : ∫⁻ x, (h x : ℝ≥0∞) ∂μG =
      ∫⁻ x, (∫⁻ s, (h (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS) ∂ν :=
    hq _ (measurable_coe_nnreal_ennreal.comp hmeas)

  refine sigmaFinite_of_pos_lintegral_ne_top
    (g := fun x => ∫⁻ s, (h (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS)
    hF.lintegral_prod_right' ?_ ?_
  · intro x hx
    have hfm : Measurable fun s : Formalism.QuantumDeterminants.Mt k r =>
        ((h (fun i j => (Matrix.of s * Matrix.of x) i j) : NNReal) : ℝ≥0∞) :=
      (measurable_coe_nnreal_ennreal.comp hmeas).comp
        (Measurable.of_eval fun i => Measurable.of_eval fun j => by
          simp only [Matrix.mul_apply, Matrix.of_apply]
          fun_prop)
    rw [lintegral_eq_zero_iff hfm] at hx
    apply hS
    rw [← Measure.measure_univ_eq_zero]
    have h0 := ae_iff.1 hx
    simpa [hne] using h0
  · rw [← hq']
    exact (hint.trans ENNReal.one_lt_top).ne

end GlobalTheory.QuotientMeasureSigmaFinite
end

noncomputable section

namespace GlobalTheory.SideCompare

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
open PI.BesselPeriodGGP (IsHaarOn IsQuotMeas)
open Formalism.FourierDecayAlt GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap (Mat decExp decConst dimV dimN thrG thrS thrSS propExp DecGap Size Thresholds muS mulP IsSide
  IsSideNormalised KFinDecay wordSeminorm DecKFin DecSmooth)

theorem sigmaFinite_of_isQuotMeas {k r : ℕ} {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS]
    (hS : μS ≠ 0) (hq : IsQuotMeas μG μS ν) : SigmaFinite ν := by
  first
  | (rename_i h_5 h_6; revert k r μG μS ν h_5 h_6 hS hq; exact @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas)
  | exact @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
  | exact _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
  | (apply _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas ..)

theorem muS_ne_zero {k r : ℕ} {μW μN : Measure (Mt k r)} [SFinite μN] (hW : μW ≠ 0) (hN : μN ≠ 0) :
    muS μW μN ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero] at *
  unfold muS
  rw [Measure.map_apply SideNormalisedGap.measurable_mulP MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
    Measure.prod_prod]
  exact mul_ne_zero hW hN

section Side

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
  (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
  (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r))

end Side

section Decay

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end Decay

end GlobalTheory.SideCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqZeroOfFischSelf
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RowSpan

open MvPolynomial Formalism.L2.Pj

variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]

section Fischer

variable {σ : Type}

end Fischer

section Lower

variable {σ : Type} (w : σ → ℕ)

end Lower

theorem rowInv_map [Infinite k] {K : Type} [Field K] (φ : k →+* K) {P : MvPolynomial (Letter T r n) k}
    (hP : RowInv r n k P) : RowInv r n K (map φ P) := by
  classical
  intro σ i i' hi t
  have := GlobalTheory.RowTriangular.eval₂_shift ((C : K →+* MvPolynomial (Letter T r n) K).comp φ) hP σ i i' hi (C t) X
    (fun ℓ => rowShift r n K σ i i' t (X ℓ)) (fun b => by simp [rowShift]) (fun ℓ hℓ => by
      rw [rowShift, aeval_X, if_neg hℓ])
  have e : ∀ Q : MvPolynomial (Letter T r n) k, rowShift r n K σ i i' t (map φ Q) =
      eval₂Hom ((C : K →+* MvPolynomial (Letter T r n) K).comp φ) (fun ℓ => rowShift r n K σ i i' t (X ℓ)) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => simp [rowShift]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p s hp => simp only [map_mul, hp, map_X, eval₂Hom_X']
  rw [e, this, map_eq_eval₂Hom_C_comp]

end GlobalTheory.RowSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelCoverDatumSimilitudeAdjointTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelCoverDatumSimilitudeAdjointTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DatumCoverAdjoint

open GlobalTheory.DatumInverseCharacter

theorem span_image_sup_eq_top {R M J : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Ideal R)
    (φ : M →ₗ[R] M) (hφ : ∀ a, ∃ b, φ b - a ∈ (K • ⊤ : Submodule R M)) (x : J → M) (s : Set J)
    (h : Submodule.span R (x '' s) ⊔ (K • ⊤ : Submodule R M) = ⊤) :
    Submodule.span R ((fun i => φ (x i)) '' s) ⊔ (K • ⊤ : Submodule R M) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨b, hb⟩ := hφ a
  have h1 : φ b ∈ Submodule.map φ (Submodule.span R (x '' s) ⊔ (K • ⊤ : Submodule R M)) :=
    Submodule.mem_map_of_mem (by rw [h]; exact Submodule.mem_top)
  rw [Submodule.map_sup, Submodule.map_span, Set.image_image, Submodule.map_smul''] at h1
  have h2 : φ b ∈ Submodule.span R ((fun i => φ (x i)) '' s) ⊔ (K • ⊤ : Submodule R M) :=
    SetLike.le_def.1 (sup_le_sup le_rfl (Submodule.smul_mono le_rfl le_top)) h1
  have := sub_mem h2 (Submodule.mem_sup_right hb)
  rwa [sub_sub_cancel] at this

theorem datum_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → d.l₂.Mb = l.Mb * d.I → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, (∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) → ∃ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → ∃ x0' : Fin n → Dw.La, AdmX (l := l) rk x0' ∧ ∀ q : Fin n → LevQ Dw d.l₂, d.w x0 (fun b => σq.symm (q b)) = d.w x0' q := by
  intro E _ _ _ H Dw l Xo c n d hM hb ph ψ x₀ hpin g hg
  obtain ⟨-, -, -, -, -, hφ⟩ := hpin
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM₁ : 0 < l.M := by have := l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hb
  have hspan : ∀ (l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H),
      ((l'.M : ℕ) : 𝓞 E) ∈ l'.Mb * l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := fun l' => by
    rw [l'.prod]; exact Ideal.mem_span_singleton_self _
  have hbI : d.l₂.Mb ≤ d.I := hb ▸ (Ideal.mul_le_inf.trans inf_le_right)
  have hbM : d.l₂.Mb ≤ l.Mb := hb ▸ (Ideal.mul_le_inf.trans inf_le_left)
  have hmb : ((d.l₂.M : ℕ) : 𝓞 E) ∈ d.l₂.Mb := (Ideal.mul_le_inf.trans inf_le_left) (hspan d.l₂)
  have hmJ : ((d.l₂.M : ℕ) : 𝓞 E) ∈ Mfr l :=
    Ideal.map_mono hbM ((Ideal.mul_le_inf.trans inf_le_right) (hspan d.l₂))
  obtain ⟨g', hg'⟩ := g.inv d.l₂.M hM₂
  set f := g.f d.l₂.M with hf
  obtain ⟨σ, hσ⟩ := exists_quot_equiv Dw hmb f g' hg'
  obtain ⟨fa, hfa⟩ := exists_adjoint Dw f
  obtain ⟨ga, hga⟩ := exists_adjoint Dw g'
  have hsurj : ∀ a, ∃ b, ga b - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := fun a =>
    ⟨fa a, mem_of_modN Dw hmJ (modN_of_dvd Dw hM₂ fun v => by
      rw [map_sub, LinearMap.sub_apply, hga, hfa, ← map_sub]
      exact dvd_of_modN Dw a (hg' v).2)⟩
  refine ⟨σ.toEquiv, hσ, fun rk x0 hx => ⟨fun b => ga (x0 b),
    span_image_sup_eq_top (Mfr l) ga hsurj x0 _ hx, fun q => ?_⟩⟩
  have hq : ∀ b, f (levRep (σ.toEquiv.symm (q b))) - levRep (q b) ∈ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro b
    rw [← Submodule.Quotient.eq, ← hσ, levRep_spec, levRep_spec]
    exact σ.apply_symm_apply _
  have hz : zetaM c ^ pairL (l := l) x0 (fun b => levRep (σ.toEquiv.symm (q b))) =
      zetaM c ^ pairL (l := l) (fun b => ga (x0 b)) (fun b => levRep (q b)) := by
    refine zpow_congr hM₁ (root_pow c dvd_rfl) ?_
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [hga, g'.map_smul, ← map_sub, ← smul_sub]
    refine dvd_right Dw l.prod (cSep_mem l) _ ?_
    set a := levRep (σ.toEquiv.symm (q b))
    have h1 : g' (f a - levRep (q b)) ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := g') (hq b)
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono hbM le_top this
    have h2 : g' (f a) - a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) :=
      mem_of_modN Dw (hbM hmb) (hg' a).1
    have := sub_mem h1 h2
    convert this using 1
    rw [map_sub]
    abel
  have hroot := root_pow d.c₂ (N := d.pd) (hM ▸ Dvd.intro_left _ rfl)
  have hδ : d.eF (d.φδ (fun b => σ.toEquiv.symm (q b))) = d.eF (d.φδ q) := by
    rw [hφ, hφ]
    refine finsum_congr fun x => ?_
    congr 1
    refine zpow_congr hpd hroot ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [← map_sub, ← smul_sub]
    refine dvd_right Dw hIJ (cHalf_mem d.I) _ ?_
    have := sub_mem (Submodule.smul_mono hbI le_rfl (hq b)) (hg (levRep (σ.toEquiv.symm (q b))))
    convert this using 1
    abel
  unfold DeltaDat.w
  rw [hz, map_mul, map_mul, hδ]

end GlobalTheory.DatumCoverAdjoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelCoverDatumSimilitudeAdjointTransportStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCoverDatum_similitude_adjoint_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → d.l₂.Mb = l.Mb * d.I → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, (∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) → ∃ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → ∃ x0' : Fin n → Dw.La, AdmX (l := l) rk x0' ∧ ∀ q : Fin n → LevQ Dw d.l₂, d.w x0 (fun b => σq.symm (q b)) = d.w x0' q := by
  first | exact @GlobalTheory.DatumCoverAdjoint.datum_adjoint | exact GlobalTheory.DatumCoverAdjoint.datum_adjoint | (intros; apply GlobalTheory.DatumCoverAdjoint.datum_adjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimir
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRow
open Formalism.REAL

namespace GlobalTheory

theorem capelli_comatrix_last_row (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → A) (hE : GlRel E) (u : ℂ) (c : Fin (n + 1)) :
    ∑ l : Fin (n + 1), (((-1 : ℤ) ^ (n + (l : ℕ)) : ℤ) : A) *
        (qminor E Fin.castSucc (Fin.succAbove l) (u - 1) * Tm E u c l) =
      if c = Fin.last n then qdet E u else 0 := by
  have h := Formalism.FourierDecayAlt.P.expansion_last_line A (n + 1) n E hE
    (Fin.snoc (α := fun _ => Fin (n + 1)) Fin.castSucc c) id u
  have h1 : (Fin.snoc (α := fun _ => Fin (n + 1)) Fin.castSucc c : Fin (n + 1) → Fin (n + 1)) ∘
      Fin.castSucc = Fin.castSucc := by
    funext k
    simp
  rw [h1, Fin.snoc_last] at h
  simp only [Function.id_comp, id] at h
  rw [← h]
  split_ifs with hc
  · subst hc
    unfold qdet
    congr 1
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k <;> simp
  · obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.mpr hc
    exact quantumMinor_eq_zero_of_row_eq qSkewRow E _ _ u c'.castSucc (Fin.last n) hc (by simp)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimir
open Formalism.REAL

namespace GlobalTheory

theorem comatrix_last_row_inverts_casimir
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ)
    (hE : GlRel E) (hdet : ∀ w v, qdet E w v = (∏ j, (w + m j)) • v)
    (hOm : ∀ y b, Om y b = ∑ c, E c b (y c)) :
    ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V),
      (∀ u x, K u ((u - 0) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧
      ∀ u v, K u (PiLp.single 2 (Fin.last n) v) =
        qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) v := by
  let Q : ℂ → Fin (n + 1) → Module.End ℂ V := fun u l =>
    (((-1 : ℤ) ^ (n + (l : ℕ)) : ℤ) : Module.End ℂ V) *
      qminor E Fin.castSucc (Fin.succAbove l) (u - 1)
  let K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V) := fun u =>
    ∑ l, (Q u l) ∘ₗ (PiLp.projₗ 2 (fun _ : Fin (n + 1) => V) l)
  have hK : ∀ u x, K u x = ∑ l, Q u l (x l) := by
    intro u x
    simp only [K, LinearMap.sum_apply, LinearMap.comp_apply, PiLp.projₗ_apply]
  refine ⟨K, fun u x => ?_, fun u v => ?_⟩
  · have h1 : ∀ l, ((u - 0) • x + Om x) l = ∑ c, Tm E u c l (x c) := by
      intro l
      simp only [Tm, sub_zero, PiLp.add_apply, PiLp.smul_apply, hOm, LinearMap.add_apply,
        Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single l]
      · simp
      · intro c _ hc
        simp [hc]
      · simp
    rw [hK]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [h1, map_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ c, ∑ l, Q u l (Tm E u c l (x c)) =
        (if c = Fin.last n then qdet E u else 0 : Module.End ℂ V) (x c) := by
      intro c
      rw [← capelli_comatrix_last_row _ n E hE u c, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Q, Module.End.mul_apply]
    simp only [h2]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [hdet]
    · intro c _ hc
      simp [hc]
    · simp
  · rw [hK, Finset.sum_eq_single (Fin.last n)]
    · have h3 : qminor E Fin.castSucc Fin.castSucc (u - 1) =
          qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) := by
        simp only [qdet, qminor, Tm, id, Fin.castSucc_inj]
      have h4 : ((-1 : ℤ) ^ (n + n)) = 1 := by
        rw [← two_mul, pow_mul]; simp
      simp only [Q, Fin.succAbove_last, h3, Fin.val_last, h4, Int.cast_one, one_mul,
        PiLp.single_eq_same]
    · intro c _ hc
      simp [PiLp.single_eq_of_ne, hc]
    · simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimirStatement
open Formalism.REAL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V), (∀ u x, K u ((u - 0) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧ ∀ u v, K u (PiLp.single 2 (Fin.last n) v) = qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) v := by
  first | exact @GlobalTheory.comatrix_last_row_inverts_casimir | exact GlobalTheory.comatrix_last_row_inverts_casimir | (intros; apply GlobalTheory.comatrix_last_row_inverts_casimir <;> assumption)
end
end
