module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightLowerBoundChartNorm
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureBasis

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

theorem le_wchart_one {X : Scheme.{0}} (L : LB X) (i : L.ι) :
    L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

def SameSec {X : Scheme.{0}} {L : LB X} (s : Out.H0 L 1) (th : L.Sec) : Prop :=
  ∀ i, th.f i = (X.presheaf.map (homOfLE (le_wchart_one L i)).op).hom (s.f fun _ => i)

def NonVan {S Y : Scheme.{0}} (p : Y ⟶ S) {M : LB Y} (s : M.Sec) : Prop :=
  ∀ b : S, ∃ y : Y, p y = b ∧ y ∈ Out.nonzeroLocus s

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVar
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem flagged_model_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) [Nonempty K], Function.Injective β → Birational y ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) + 1) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl _ hβ
  obtain ⟨-, ⟨x, hx⟩, hchar, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
  have hA := GlobalTheory.T.generic_trdeg_eq_dimension E H D l Xo c O β Y 𝔐.Ω₀ 𝔐.ξ₀ Ω x 𝔐.fn hβ 𝔐.gen₀ (hx ▸ 𝔐.fn_over)
  letI : Algebra 𝔐.Ω₀ Ω := 𝔐.fn.toAlgebra
  have hB := GlobalTheory.T.generic_flag_trdeg_formula 𝔐.Ω₀ Ω Fl.Li₀ 𝔐.Li Fl.j (CMType H ⊕ CMType H) (labelRk D) Fl.V₀ Fl.b Fl.deg Fl.generic
  haveI : CharZero 𝔐.Ω₀ := (RingHom.charZero_iff 𝔐.fn.injective).mpr hchar
  haveI : FaithfulSMul ℤ 𝔐.Ω₀ := (faithfulSMul_iff_algebraMap_injective ℤ 𝔐.Ω₀).mpr Int.cast_injective
  haveI : FaithfulSMul 𝔐.Ω₀ Ω := (faithfulSMul_iff_algebraMap_injective 𝔐.Ω₀ Ω).mpr 𝔐.fn.injective
  have htow := trdeg_add_eq ℤ 𝔐.Ω₀ (A := Ω)
  rw [hA, hB] at htow
  have hcard : Fintype.card (CMType H) = Module.finrank ℚ E / 2 := by
    rw [Fintype.card_eq_nat_card]; exact GlobalTheory.PeriodCoord.card_cmType H
  have harith : D.dim + ∑ σ : CMType H ⊕ CMType H, labelRk D σ * (labelRk D σ - 1) / 2 =
      Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) := by
    have h1 : (D.p + D.q) * (D.p + D.q - 1) / 2 = D.p * (D.p - 1) / 2 + D.q * (D.q - 1) / 2 + D.p * D.q := by
      rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right, Nat.add_choose_eq]
      simp [Finset.Nat.antidiagonal_succ, Finset.sum_range_succ]
      ring
    rw [Fintype.sum_sum_type, h1, Datum.dim, ← hcard]
    simp [Finset.sum_const, Finset.card_univ, labelRk]
    ring
  have htr : Algebra.trdeg ℤ Ω = ((Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) : ℕ) : Cardinal) := by
    rw [← htow, ← harith]; push_cast; rfl
  exact GlobalTheory.T.birational_of_transcendence_degree 𝔐.X Ω 𝔐.ξ K J y _ 𝔐.tie htr

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVarStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_birational_arith_var : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) [Nonempty K], Function.Injective β → Birational y ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.flagged_model_dim | exact GlobalTheory.CompanionTheory.Ar.flagged_model_dim | (intros; apply GlobalTheory.CompanionTheory.Ar.flagged_model_dim <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScaling
section -- merged from Development.WeilBound.CoreStatements.AmpleLineBundles.LineHtInvariantBaseChangeScaling
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace CoverDenseAlt

theorem finsum_block {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']
    {J : Type} [Fintype J] (x : J → L) (hx : x ≠ 0) (c : L') (hc : c ≠ 0) :
    ∑ᶠ v : FinitePlace L', Real.log (⨆ i, v (c * algebraMap L L' (x i))) =
      -(∑ σ : L' →+* ℂ, Real.log ‖σ c‖) +
        Module.finrank L L' * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (x i)) := by
  have hy : (fun i => algebraMap L L' (x i)) ≠ 0 := by
    intro h
    apply hx
    funext i
    exact (map_eq_zero_iff _ (algebraMap L L').injective).1 (congrFun h i)
  have key : ∀ v : FinitePlace L', Real.log (⨆ i, v (c * algebraMap L L' (x i))) =
      Real.log (v c) + Real.log (⨆ i, v (algebraMap L L' (x i))) := by
    intro v
    have hvc : 0 < v c := FinitePlace.pos_iff.2 hc
    have h1 : (⨆ i, v (c * algebraMap L L' (x i))) = v c * ⨆ i, v (algebraMap L L' (x i)) := by
      rw [Real.mul_iSup_of_nonneg hvc.le]
      refine iSup_congr fun i => ?_
      exact map_mul v _ _
    rw [h1, Real.log_mul hvc.ne' (GroundTheory.Heights₂.Heights.iSup_place_pos hy v).ne']
  rw [finsum_congr key, finsum_add_distrib (SecLow.log_support_finite hc)
    (GroundTheory.Heights₂.Heights.support_log_iSup_place_finite hy), SecLow.product_formula c hc,
    GroundTheory.Heights₂.Heights.finsum_log_iSup_algebraMap hx]

theorem lineHt_invariant_base_change_scaling : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (L : Type) [Field L] [NumberField L] (L' : Type) [Field L'] [NumberField L'] (e : L →+* L') (w : (Σ k, ι k) → L) (c : K → L'), (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ k, c k ≠ 0) → lineHt A L' (fun p => c p.1 * e (w p)) = lineHt A L w := by
  intro K _ ι _ A L _ _ L' _ _ e w c hw hc
  letI : Algebra L L' := e.toAlgebra
  haveI : IsScalarTower ℚ L L' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have hyk : ∀ k, (fun i => w ⟨k, i⟩) ≠ 0 := by
    intro k h
    obtain ⟨i, hi⟩ := hw k
    exact hi (congrFun h i)
  have hyk' : ∀ k, (fun i => c k * algebraMap L L' (w ⟨k, i⟩)) ≠ 0 := by
    intro k h
    obtain ⟨i, hi⟩ := hw k
    have h2 := congrFun h i
    simp only [Pi.zero_apply, mul_eq_zero, hc k, false_or] at h2
    exact hi ((map_eq_zero_iff _ (algebraMap L L').injective).1 h2)
  have fin' : (∑ᶠ v : FinitePlace L', ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (c k * e (w ⟨k, i⟩)))) =
      ∑ k, (A.a k : ℝ) * (-(∑ σ : L' →+* ℂ, Real.log ‖σ (c k)‖) +
        Module.finrank L L' * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩))) := by
    rw [finsum_sum_comm]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_finsum]
      congr 1
      exact finsum_block _ (hyk k) _ (hc k)
    · intro k _
      exact (GroundTheory.Heights₂.Heights.support_log_iSup_place_finite (hyk' k)).subset
        (Function.support_mul_subset_right _ _)
  have finL : (∑ᶠ v : FinitePlace L, ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) =
      ∑ k, (A.a k : ℝ) * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) := by
    rw [finsum_sum_comm]
    · exact Finset.sum_congr rfl fun k _ => (mul_finsum _ _).symm
    · intro k _
      exact (GroundTheory.Heights₂.Heights.support_log_iSup_place_finite (hyk k)).subset
        (Function.support_mul_subset_right _ _)
  have arch' : ∀ σ : L' →+* ℂ, Real.log (A.h fun p => σ (c p.1 * e (w p))) =
      ∑ k, (A.a k : ℝ) * Real.log ‖σ (c k)‖ +
        Real.log (A.h fun p => (σ.comp (algebraMap L L')) (w p)) := by
    intro σ
    have hσc : ∀ k, σ (c k) ≠ 0 := fun k => (map_ne_zero σ).2 (hc k)
    have hpos : 0 < A.h fun p => (σ.comp (algebraMap L L')) (w p) := by
      refine A.pos _ fun k => ?_
      obtain ⟨i, hi⟩ := hw k
      exact ⟨i, (map_ne_zero _).2 hi⟩
    have hs := A.smul (fun k => σ (c k)) (fun p => (σ.comp (algebraMap L L')) (w p)) hσc
    have hfun : (fun p : (Σ k, ι k) => σ (c p.1 * e (w p))) =
        fun p => σ (c p.1) * (σ.comp (algebraMap L L')) (w p) := by
      funext p
      rw [map_mul]
      rfl
    have hne : ∀ k ∈ Finset.univ, ‖σ (c k)‖ ^ A.a k ≠ 0 :=
      fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hσc k))
    rw [hfun, hs, Real.log_mul (Finset.prod_ne_zero_iff.2 hne) hpos.ne', Real.log_prod hne]
    simp only [Real.log_zpow]
  have archSum : ∑ σ : L' →+* ℂ, Real.log (A.h fun p => σ (c p.1 * e (w p))) =
      ∑ k, (A.a k : ℝ) * ∑ σ : L' →+* ℂ, Real.log ‖σ (c k)‖ +
        Module.finrank L L' * ∑ τ : L →+* ℂ, Real.log (A.h fun p => τ (w p)) := by
    rw [Finset.sum_congr rfl fun σ _ => arch' σ, Finset.sum_add_distrib, Finset.sum_comm,
      GroundTheory.Heights₂.Heights.sum_embeddings_restrict (fun τ => Real.log (A.h fun p => τ (w p)))]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  have hmul := Module.finrank_mul_finrank ℚ L L'
  have hpos' : 0 < Module.finrank ℚ L' := Module.finrank_pos
  have hposL : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hn : (Module.finrank L L' : ℝ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at hmul
    omega
  have hnL : (Module.finrank ℚ L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hposL.ne'
  have hsplit : (∑ k, (A.a k : ℝ) * (-(∑ σ : L' →+* ℂ, Real.log ‖σ (c k)‖) +
        Module.finrank L L' * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)))) =
      -(∑ k, (A.a k : ℝ) * ∑ σ : L' →+* ℂ, Real.log ‖σ (c k)‖) +
        Module.finrank L L' * ∑ k, (A.a k : ℝ) * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  show (Module.finrank ℚ L' : ℝ)⁻¹ *
      ((∑ᶠ v : FinitePlace L', ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (c k * e (w ⟨k, i⟩)))) +
        ∑ σ : L' →+* ℂ, Real.log (A.h fun p => σ (c p.1 * e (w p)))) =
    (Module.finrank ℚ L : ℝ)⁻¹ *
      ((∑ᶠ v : FinitePlace L, ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
        ∑ τ : L →+* ℂ, Real.log (A.h fun p => τ (w p)))
  rw [fin', archSum, finL, hsplit, ← hmul]
  push_cast
  field_simp
  ring

end CoverDenseAlt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScaling
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht

theorem lineHt_map_scale : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (L : Type) [Field L] [NumberField L] (L' : Type) [Field L'] [NumberField L'] (e : L →+* L') (w : (Σ k, ι k) → L) (c : K → L'), (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ k, c k ≠ 0) → lineHt A L' (fun p => c p.1 * e (w p)) = lineHt A L w :=
  @CoverDenseAlt.lineHt_invariant_base_change_scaling

end GlobalTheory.CompanionTheory.Ar.Ht
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScalingStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_height_invariant_scaling : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (L : Type) [Field L] [NumberField L] (L' : Type) [Field L'] [NumberField L'] (e : L →+* L') (w : (Σ k, ι k) → L) (c : K → L'), (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ k, c k ≠ 0) → lineHt A L' (fun p => c p.1 * e (w p)) = lineHt A L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale | exact GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalBoundHeightCompare
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalBoundHeightCompare
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.UnitHt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_inv_section {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} (hu : u ≠ 0) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {val : 𝕜} (hv : val ≠ 0)
    (h : HasVal y a u z val) : HasVal y (-a) u⁻¹ z val⁻¹ := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  have hfy : aeval y f ≠ 0 := fun h0 =>
    hfz (hz.2 f ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).2 h0))
  refine ⟨dh, dg, f, g, hf, hg, fun k => ?_, ?_, ?_, ?_⟩
  · have := hd k
    simp only [Pi.neg_apply]
    omega
  · rw [hy, inv_mul_cancel_left₀ hu]
  · rw [hgz]
    exact mul_ne_zero hv hfz
  · rw [hgz, inv_mul_cancel_left₀ hv]


omit [∀ k, Fintype (ι k)] in
theorem ptHt_neg (a : K → ℤ) (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, ι k) → L) :
    ptHt (fun k => (((-a) k : ℤ) : ℝ)) (fun z => -φ z) L w = -ptHt (fun k => (a k : ℝ)) φ L w := by
  have e : ∀ v : FinitePlace L, ∑ k, (((-a) k : ℤ) : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) =
      (-1 : ℝ) • ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) := fun v => by
    rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  simp only [ptHt, e]
  rw [← smul_finsum, Finset.sum_neg_distrib, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Ht.UnitHt


open GlobalTheory.CompanionTheory.Ar.Ht.UnitHt in
theorem GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω) (c : ℝ), VertBound y a u c → ∀ (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 → HasVal y a u w val → |ptHt (fun k => (a k : ℝ)) φ L w - (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖)| ≤ c := by
  intro K _ ι _ Ω _ y d hAr hB a u c hV φ L _ _ w hw val hv hval
  obtain ⟨hu, q, m, hq, hm, hlog, h1, h2⟩ := hV
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : Real.log m / q ≤ c := by
    rw [div_le_iff₀ hq']
    linarith
  have b₁ := SecLow.height_ge_of_section K ι Ω y d hAr hB a u q m hq hm h1 φ L w hw val hv hval
  have b₂ := SecLow.height_ge_of_section K ι Ω y d hAr hB (-a) u⁻¹ q m hq hm h2 (fun z => -φ z) L w hw val⁻¹
    (inv_ne_zero hv) (UnitHt.hasVal_inv_section hu hw hv hval)
  rw [UnitHt.ptHt_neg] at b₂
  have e : ∑ σ : L →+* ℂ, (-φ (fun p => σ (w p)) - Real.log ‖σ val⁻¹‖) =
      -∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_inv₀, norm_inv, Real.log_inv]
    ring
  rw [e, mul_neg] at b₂
  rw [abs_le]
  constructor <;> linarith
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalBoundHeightCompareStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_bound_height_compare : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω) (c : ℝ), VertBound y a u c → ∀ (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 → HasVal y a u w val → |ptHt (fun k => (a k : ℝ)) φ L w - (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖)| ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound | exact GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyGen

variable {R : Type} [CommRing R] {Y : Scheme.{0}}

def SecMod (_p : Y ⟶ Sp R) (M : LB Y) : Type := M.Sec

variable {p : Y ⟶ Sp R} {M : LB Y}

theorem SecMod.ext {s t : SecMod p M} (h : ∀ i, LB.Sec.f s i = LB.Sec.f t i) : s = t := by
  obtain ⟨f, hf⟩ := s
  obtain ⟨g, hg⟩ := t
  obtain rfl : f = g := funext h
  rfl

def constHom (p : Y ⟶ Sp R) (U : Y.Opens) : R →+* Γ(Y, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem constHom_apply (U : Y.Opens) (a : R) : constHom p U a = constFn p U a := rfl

theorem res_constFn {U V : Y.Opens} (h : V ≤ U) (a : R) :
    (Y.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  have e : p.appLE ⊤ U (fun _ _ => trivial) ≫ Y.presheaf.map (homOfLE h).op = p.appLE ⊤ V (fun _ _ => trivial) :=
    Scheme.Hom.appLE_map p _ _
  exact congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) e

instance : Add (SecMod p M) where
  add s t := ⟨fun i => LB.Sec.f s i + LB.Sec.f t i, fun i j => by
    rw [map_add (f := _), map_add (f := _), LB.Sec.compat s, LB.Sec.compat t, mul_add]⟩

instance : Zero (SecMod p M) where
  zero := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, MulZeroClass.mul_zero]⟩

instance : Neg (SecMod p M) where
  neg s := ⟨fun i => - LB.Sec.f s i, fun i j => by rw [map_neg, map_neg, LB.Sec.compat s, mul_neg]⟩

instance : AddCommGroup (SecMod p M) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := SecMod.ext fun i => _root_.add_assoc _ _ _
  zero_add a := SecMod.ext fun i => zero_add _
  add_zero a := SecMod.ext fun i => add_zero _
  neg_add_cancel a := SecMod.ext fun i => neg_add_cancel _
  add_comm a b := SecMod.ext fun i => add_comm _ _

theorem zero_f (i : M.ι) : LB.Sec.f (0 : SecMod p M) i = 0 := rfl

instance : Module R (SecMod p M) where
  smul a s := ⟨fun i => constFn p _ a * LB.Sec.f s i, fun i j => by
    rw [map_mul, map_mul, res_constFn, res_constFn, LB.Sec.compat s, mul_left_comm]⟩
  one_smul s := SecMod.ext fun i => by
    show constFn p _ 1 * _ = _
    rw [← constHom_apply, map_one, _root_.one_mul]
  mul_smul a b s := SecMod.ext fun i => by
    show constFn p _ (a * b) * _ = constFn p _ a * (constFn p _ b * _)
    rw [← constHom_apply, ← constHom_apply, ← constHom_apply, map_mul, _root_.mul_assoc]
  smul_zero a := SecMod.ext fun i => MulZeroClass.mul_zero _
  smul_add a s t := SecMod.ext fun i => mul_add _ _ _
  add_smul a b s := SecMod.ext fun i => by
    show constFn p _ (a + b) * _ = constFn p _ a * _ + constFn p _ b * _
    rw [← constHom_apply, ← constHom_apply, ← constHom_apply, map_add (f := _), add_mul]
  zero_smul s := SecMod.ext fun i => by
    show constFn p _ 0 * _ = 0
    rw [← constHom_apply, map_zero, MulZeroClass.zero_mul]

theorem smul_f (a : R) (s : SecMod p M) (i : M.ι) :
    LB.Sec.f (a • s : SecMod p M) i = constFn p _ a * LB.Sec.f s i := rfl

theorem eq_zero_of_smul_eq_zero [IsDomain R] [Flat p] {a : R} (ha : a ≠ 0) {s : SecMod p M}
    (h : a • s = 0) : s = 0 := by
  apply SecMod.ext
  intro i
  apply fn_ext
  intro y hy
  apply cst_regular p y ha
  have e := congrArg (gs (𝟙 Y) y (M.U i)) (congrArg (fun s : SecMod p M => LB.Sec.f s i) h)
  simp only [smul_f, zero_f] at e
  rw [gs_mul _ y _ hy, gs_constFn p _ _ y hy, Category.id_comp] at e
  have z : gs (𝟙 Y) y (M.U i) (0 : Γ(Y, M.U i)) = 0 := by
    rw [gs_eq _ y _ hy]
    exact map_zero (CommRingCat.Hom.hom (Y.presheaf.germ (𝟙 Y ⁻¹ᵁ M.U i) y hy))
  show cst p y a * _ = cst p y a * gs (𝟙 Y) y (M.U i) (0 : Γ(Y, M.U i))
  rw [z, MulZeroClass.mul_zero]
  exact e.trans z

end GlobalTheory.CompanionTheory.Ar.Sl.KeyGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsUnitValues
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsUnitValues
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.OrArch.Ext

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem continuousAt_metric (A : HermLine ι) (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContinuousAt A.h z :=
  hA.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hz)

theorem continuous_aeval_form (g : MRing ι) : Continuous fun z : (Σ k, ι k) → ℂ => aeval z g := by
  have := MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) g)
  simpa only [Small.LineModel.eval_map_eq] using this

theorem continuousAt_log_metric {σ : Type} (A : HermLine ι) (hA : IsSmoothHerm A) (c : (Σ k, ι k) → σ)
    {z : σ → ℂ} (hz : ∀ k, ∃ i, z (c ⟨k, i⟩) ≠ 0) :
    ContinuousAt (fun w : σ → ℂ => Real.log (A.h fun p => w (c p))) z := by
  have h1 : ContinuousAt (fun w : σ → ℂ => A.h fun p => w (c p)) z :=
    ContinuousAt.comp (g := A.h) (f := fun (w : σ → ℂ) p => w (c p)) (continuousAt_metric A hA hz)
      (continuous_pi fun p => continuous_apply _).continuousAt
  exact h1.log (A.pos _ hz).ne'

end General

theorem line_smooth {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : Top.RootModel Ψ N) (t : ℝ)
    (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem archBetween_of_off_form : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : Top.RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Top.Wt Ψ N) (s lo hi : ℝ) (f : MRing (Cmp.joinIdx M.ι R.ι)), f ∉ mCoordIdeal (Ht.joinOf M R i) → (∀ j, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j)) → (∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∀ val : Option (Ψ × Fin N) → ℂ, (∀ j, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j) w (val j)) → ∑ j, M.coef lam s j * (Real.log ((M.line t j).h (fun p => w (Cmp.joinInl M.ι R.ι p))) - Real.log ((R.line 1 j).h (fun p => w (Cmp.joinInr M.ι R.ι p))) - Real.log ‖val j‖) ∈ Set.Icc lo hi) → Ht.ArchBetween M R i u t lam s lo hi := by
  intro Ψ _ _ N M R i u t lam s lo hi f hf hu hb z hz val hval
  have hcl := GlobalTheory.T.complex_points_dense_nonvanishing (M.K ⊕ R.K) (Cmp.joinIdx M.ι R.ι) (mCoordIdeal (Ht.joinOf M R i)) _ f
    (GlobalTheory.T.join_model_points_project Ψ N M R i).1 hf
  have hzc := hcl (by rwa [← Small.LineModel.ptsOver_complex])
  have hne : ∀ j, val j ≠ 0 := by
    intro j
    obtain ⟨v, hv0, hv⟩ := hu j ℂ z hz
    rwa [Small.LineModel.hasVal_unique _ _ _ hz (hval j) hv]
  choose dg dh g h hg hh hd e n v using hval
  have hq : ∀ j, aeval z (g j) / aeval z (h j) = val j := fun j => by
    rw [v j, mul_div_assoc, div_self (n j), mul_one]
  let Fn : ((Σ k, Cmp.joinIdx M.ι R.ι k) → ℂ) → ℝ := fun w =>
    ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => w (Cmp.joinInl M.ι R.ι p)) -
      Real.log ((R.line 1 j).h fun p => w (Cmp.joinInr M.ι R.ι p)) -
        Real.log ‖aeval w (g j) / aeval w (h j)‖)
  have hcont : ContinuousAt Fn z := by
    refine tendsto_finsetSum _ fun j _ => ?_
    have h1 := continuousAt_log_metric (M.line t j) (line_smooth M t j) (Cmp.joinInl M.ι R.ι)
      (z := z) fun k => hz.1 (Sum.inl k)
    have h2 := continuousAt_log_metric (R.line 1 j) (line_smooth R 1 j) (Cmp.joinInr M.ι R.ι)
      (z := z) fun k => hz.1 (Sum.inr k)
    have h3 : ContinuousAt (fun w : (Σ k, Cmp.joinIdx M.ι R.ι k) → ℂ =>
        Real.log ‖aeval w (g j) / aeval w (h j)‖) z := by
      refine ContinuousAt.log ?_ ?_
      · exact (((continuous_aeval_form (g j)).continuousAt).div
          ((continuous_aeval_form (h j)).continuousAt) (n j)).norm
      · rw [hq j]
        exact norm_ne_zero_iff.mpr (hne j)
    exact continuousAt_const.mul ((h1.sub h2).sub h3)
  have hev : ∀ᶠ w in 𝓝[{w | w ∈ mcPts (mCoordIdeal (Ht.joinOf M R i)) ∧ Cmp.evC w f ≠ 0}] z,
      Fn w ∈ Set.Icc lo hi := by
    have hV : ∀ᶠ w in 𝓝 z, ∀ j, aeval w (h j) ≠ 0 := by
      rw [Filter.eventually_all]
      intro j
      exact (continuous_aeval_form (h j)).continuousAt.eventually_ne (n j)
    filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with w hw hS
    have hwp : w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)) := by
      rw [Small.LineModel.ptsOver_complex]
      exact hS.1
    exact hb w hwp hS.2 (fun j => aeval w (g j) / aeval w (h j)) fun j =>
      ⟨dg j, dh j, g j, h j, hg j, hh j, hd j, e j, hw j, (div_mul_cancel₀ _ (hw j)).symm⟩
  haveI hnb : (𝓝[{w | w ∈ mcPts (mCoordIdeal (Ht.joinOf M R i)) ∧ Cmp.evC w f ≠ 0}] z).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hzc
  have hmem : Fn z ∈ Set.Icc lo hi :=
    isClosed_Icc.mem_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
  have hFn : Fn z = ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => z (Cmp.joinInl M.ι R.ι p)) -
      Real.log ((R.line 1 j).h fun p => z (Cmp.joinInr M.ι R.ι p)) - Real.log ‖val j‖) :=
    Finset.sum_congr rfl fun j _ => by rw [hq j]
  rwa [hFn] at hmem

end GlobalTheory.CompanionTheory.Ar.OrArch.Ext
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsUnitValuesStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_coords_unit_values : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : Top.RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Top.Wt Ψ N) (s lo hi : ℝ) (f : MRing (Cmp.joinIdx M.ι R.ι)), f ∉ mCoordIdeal (Ht.joinOf M R i) → (∀ j, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j)) → (∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∀ val : Option (Ψ × Fin N) → ℂ, (∀ j, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j) w (val j)) → ∑ j, M.coef lam s j * (Real.log ((M.line t j).h (fun p => w (Cmp.joinInl M.ι R.ι p))) - Real.log ((R.line 1 j).h (fun p => w (Cmp.joinInr M.ι R.ι p))) - Real.log ‖val j‖) ∈ Set.Icc lo hi) → Ht.ArchBetween M R i u t lam s lo hi := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrArch.Ext.archBetween_of_off_form | exact GlobalTheory.CompanionTheory.Ar.OrArch.Ext.archBetween_of_off_form | (intros; apply GlobalTheory.CompanionTheory.Ar.OrArch.Ext.archBetween_of_off_form <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeneratorRatioUnitExists
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeneratorRatioUnitExists
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Ratio

variable {X Y F Y' Z : Scheme.{0}} {L : LB X} {M : LB Y} {f : F ⟶ X} {g : F ⟶ Y}

theorem gm_pull_g (N : LB X) (f : F ⟶ X) (ψ : Z ⟶ F) (z : Z) (a b : N.ι) (ha : f (ψ z) ∈ N.U a)
    (hb : f (ψ z) ∈ N.U b) :
    gm ψ z ((N.pull f).U (fun _ => a) ⊓ (N.pull f).U (fun _ => b)) ((N.pull f).g (fun _ => a) (fun _ => b)) =
      gm (ψ ≫ f) z _ (N.g a b) := by
  have hp : ψ z ∈ (N.pull f).U (fun _ => a) ⊓ (N.pull f).U (fun _ => b) := ⟨mem_pull.2 ha, mem_pull.2 hb⟩
  show gm ψ z _ (∏ _k : PUnit, (res _ (pullU f _ (N.g a b))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res ψ z _ hp _).trans (gm_pull ψ f z (N.U a ⊓ N.U b) ⟨ha, hb⟩ _)

theorem gm_w_trans {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen) (ψ : Z ⟶ F) (z : Z) {a a' : L.ι} {b b' : M.ι}
    (ha : f (ψ z) ∈ L.U a) (ha' : f (ψ z) ∈ L.U a') (hb : g (ψ z) ∈ M.U b) (hb' : g (ψ z) ∈ M.U b') :
    gm ψ z ((M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a)) (w.s (fun _ => b, fun _ => a)) =
      gm (ψ ≫ g) z _ (M.g b b') * (gm (ψ ≫ f) z _ (L.g a a'))⁻¹ *
        gm ψ z ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')) (w.s (fun _ => b', fun _ => a')) := by
  have hm : ψ z ∈ (M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a) ⊓
      ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')) :=
    ⟨⟨mem_pull.2 hb, mem_pull.2 ha⟩, mem_pull.2 hb', mem_pull.2 ha'⟩
  have e := congrArg (gm ψ z ((M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a) ⊓
      ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')))) (hw (fun _ => b, fun _ => a) (fun _ => b', fun _ => a'))
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res ψ z _ hm _))))
  show gm ψ z _ (res _ ((M.pull g).g (fun _ => b) (fun _ => b')) * (res _ ((L.pull f).g (fun _ => a) (fun _ => a')))⁻¹) = _
  rw [map_mul, map_inv, gm_res ψ z _ hm, gm_res ψ z _ hm, gm_pull_g M g ψ z b b' hb hb', gm_pull_g L f ψ z a a' ha ha']

variable {K : Type} [Fintype K]

def rW (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y) (φ : K → (Y' ⟶ F)) (p : K → L.ι) (q : K → M.ι) : Y'.Opens :=
  LB.wchart L (fun k => φ k ≫ f) p ⊓ LB.wchart M (fun k => φ k ≫ g) q

theorem rW_le (φ : K → (Y' ⟶ F)) (p : K → L.ι) (q : K → M.ι) (k : K) :
    rW L M f g φ p q ≤ φ k ⁻¹ᵁ ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) :=
  fun _ hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy.2 k), mem_pull.2 (Set.mem_iInter.1 hy.1 k)⟩

def rLoc (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (p : K → L.ι) (q : K → M.ι) : Γ(Y', rW L M f g φ p q)ˣ :=
  res inf_le_left (c.s p) *
    (∏ k, res (rW_le φ p q k) (pullU (φ k) _ (w.s (fun _ => q k, fun _ => p k))) ^ ε k) *
    (res inf_le_right (b.s q))⁻¹

def rVal (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → M.ι) : (Z.presheaf.stalk z)ˣ :=
  gm r z (LB.wchart L (fun k => φ k ≫ f) p) (c.s p) *
    (∏ k, gm (r ≫ φ k) z ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) (w.s (fun _ => q k, fun _ => p k)) ^ ε k) *
    (gm r z (LB.wchart M (fun k => φ k ≫ g) q) (b.s q))⁻¹

theorem gm_rLoc (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → M.ι) (hz : r z ∈ rW L M f g φ p q) :
    gm r z _ (rLoc w φ ε c b p q) = rVal w φ ε c b r z p q := by
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) ?_))
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hz _))))
  exact (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
    ((gm_res r z _ hz _).trans (gm_pull r (φ k) z _ (rW_le φ p q k hz) _))))

theorem comm_group_ratio_cancel {A : Type} [CommGroup A] (tl tm c' w' b' tm' tl' : A) (h1 : tl = tl') (h2 : tm = tm') :
    (tl * c') * (tm' * tl'⁻¹ * w') * (tm * b')⁻¹ = c' * w' * b'⁻¹ := by
  subst h1 h2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem rVal_indep {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen)
    (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    {c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)} {b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε)}
    (hc : c.IsGen) (hb : b.IsGen) (r : Z ⟶ Y') (z : Z) {p p' : K → L.ι} {q q' : K → M.ι}
    (hz : r z ∈ rW L M f g φ p q) (hz' : r z ∈ rW L M f g φ p' q') :
    rVal w φ ε c b r z p q = rVal w φ ε c b r z p' q' := by
  have e : ∀ k, gm (r ≫ φ k) z ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) (w.s (fun _ => q k, fun _ => p k)) =
      gm ((r ≫ φ k) ≫ g) z _ (M.g (q k) (q' k)) * (gm ((r ≫ φ k) ≫ f) z _ (L.g (p k) (p' k)))⁻¹ *
        gm (r ≫ φ k) z ((M.pull g).U (fun _ => q' k) ⊓ (L.pull f).U (fun _ => p' k)) (w.s (fun _ => q' k, fun _ => p' k)) :=
    fun k => gm_w_trans hw (r ≫ φ k) z (Set.mem_iInter.1 hz.1 k) (Set.mem_iInter.1 hz'.1 k)
      (Set.mem_iInter.1 hz.2 k) (Set.mem_iInter.1 hz'.2 k)
  unfold rVal
  rw [gen_trans hc r z hz.1 hz'.1, gen_trans hb r z hz.2 hz'.2, Finset.prod_congr rfl fun k _ => by rw [e k]]
  simp only [mul_zpow, Finset.prod_mul_distrib, inv_zpow, Finset.prod_inv_distrib]
  refine comm_group_ratio_cancel _ _ _ _ _ _ _ ?_ ?_
  · simp only [trF, Category.assoc]
  · simp only [trF, Category.assoc]

theorem exists_unit_ratio_of_generators (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen)
    (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    {c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)} {b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε)}
    (hc : c.IsGen) (hb : b.IsGen) : ∃ u : Γ(Y', ⊤)ˣ, Tr w φ _ _ ε c b u := by
  obtain ⟨u, hu⟩ := glue_unit (X := Y') ⊤ (fun i : (K → L.ι) × (K → M.ι) => rW L M f g φ i.1 i.2) (fun _ => le_top)
    (fun y _ => by
      choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
      choose I' hI' using fun χ : Y' ⟶ Y => exists_chart hM (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun k => I (φ k ≫ f), fun k => I' (φ k ≫ g)),
        Set.mem_iInter.2 fun k => hI _, Set.mem_iInter.2 fun k => hI' _⟩)
    (fun i => rLoc w φ ε c b i.1 i.2)
    (fun i j y hy => by
      rw [gm_rLoc w φ ε c b (𝟙 Y') y _ _ hy.1, gm_rLoc w φ ε c b (𝟙 Y') y _ _ hy.2]
      exact rVal_indep hw φ ε hc hb (𝟙 Y') y hy.1 hy.2)
  refine ⟨u, fun Z r z JL JM hJL hJM => ?_⟩
  have hz : r z ∈ rW L M f g φ (fun k => JL ((r ≫ φ k) ≫ f)) (fun k => JM ((r ≫ φ k) ≫ g)) :=
    ⟨Set.mem_iInter.2 fun k => hJL _, Set.mem_iInter.2 fun k => hJM _⟩
  have e := gm_rLoc w φ ε c b r z _ _ hz
  rw [← hu (_, _), gm_res r z _ hz] at e
  rw [val_of c r z JL (fun k => JL ((r ≫ φ k) ≫ f)) (fun k => by rw [Category.assoc]),
    val_of b r z JM (fun k => JM ((r ≫ φ k) ≫ g)) (fun k => by rw [Category.assoc])]
  exact mul_inv_eq_iff_eq_mul.1 e.symm

theorem exists_ratio_iso : ∀ (X Y F : Scheme.{0}) (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y), L.IsLB → M.IsLB →
    ∀ (w : LB.Iso (L.pull f) (M.pull g)), w.IsGen → ∀ (Y' : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y' ⟶ F))
    (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε))
    (b : LB.Gen (LB.LinComb M φM ε)), (∀ i, φ i ≫ f = φL i) → (∀ i, φ i ≫ g = φM i) → c.IsGen → b.IsGen →
    ∃ u : Γ(Y', ⊤)ˣ, Tr w φ φL φM ε c b u := by
  intro X Y F L M f g hL hM w hw Y' K _ φ φL φM ε c b h₁ h₂ hc hb
  obtain rfl : (fun k => φ k ≫ f) = φL := funext h₁
  obtain rfl : (fun k => φ k ≫ g) = φM := funext h₂
  exact exists_unit_ratio_of_generators hL hM hw φ ε hc hb

end Ratio

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeneratorRatioUnitExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_ratio_unit_exists : ∀ (X Y F : Scheme.{0}) (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y), L.IsLB → M.IsLB → ∀ (w : LB.Iso (L.pull f) (M.pull g)), w.IsGen → ∀ (Y' : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y' ⟶ F)) (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε)) (b : LB.Gen (LB.LinComb M φM ε)), (∀ i, φ i ≫ f = φL i) → (∀ i, φ i ≫ g = φM i) → c.IsGen → b.IsGen → ∃ u : Γ(Y', ⊤)ˣ, Tr w φ φL φM ε c b u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.exists_ratio_iso | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.exists_ratio_iso | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.exists_ratio_iso <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResidueHodgeLatticeAdaptedBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResidueHodgeLatticeAdaptedBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

private theorem isUnit_det_of_linearIndependent_frame {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (a b : Fin n → W) (h : ∀ i, a i = ∑ k, M i k • b k)
    (ha : LinearIndependent C a) : IsUnit M.det := by
  by_contra hM
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr (by simpa [isUnit_iff_ne_zero] using hM)
  apply hc0
  have hsum : ∑ i, c i • a i = 0 := by
    simp_rw [h, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.sum_smul]
    have hk := congrFun hc k
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hk
    rw [hk, zero_smul]
  exact funext (Fintype.linearIndependent_iff.mp ha c hsum)

private theorem eq_sum_inv_smul_of_eq_sum_smul {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (hM : IsUnit M.det) (a b : Fin n → W) (h : ∀ i, a i = ∑ k, M i k • b k) :
    ∀ i, b i = ∑ k, M⁻¹ i k • a k := by
  intro i
  simp_rw [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul M hM, Matrix.one_apply, ite_smul,
    one_smul, zero_smul]
  simp

private theorem eq_sum_mul_smul_of_eq_sum_smul_of_eq_sum_smul {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) C) (N : Matrix (Fin m) (Fin m) C) (x : Fin n → W) (y z : Fin m → W)
    (hx : ∀ i, x i = ∑ k, M i k • y k) (hy : ∀ i, y i = ∑ k, N i k • z k) :
    ∀ i, x i = ∑ k, (M * N) i k • z k := by
  intro i
  rw [hx]
  simp_rw [hy, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem det_evaluated_frame : ∀ (E : Type) [Field E] [NumberField E] (C A : Type) [Field C] [CharZero C] [CommRing A] [Algebra A C]
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (g p q : ℕ) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C)))
    (tC : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (b₁ v : Fin p → Fin g → C) (b₂ w : Fin q → Fin g → C)
    (u : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (Ap : Matrix (Fin (p + q)) (Fin (p + q)) C)
    (P : Matrix (Fin p) (Fin p) C) (Q : Matrix (Fin q) (Fin q) C) (gm : C),
    (∀ a y, (ρHC a y).1 = ρC a y.1) → (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A C).range) → HT.IsFreeOn ρHC HV tC →
    IsAdapted ρHC σ b₁ b₂ u → (∀ i, v i = ∑ k, P i k • b₁ k) → (∀ i, w i = ∑ k, Q i k • b₂ k) →
    LinearIndependent C b₁ → (∀ i, HT.eigProj ρHC σ (tC i) = ∑ k, Ap i k • u k) →
    (∀ (v' : Fin p → Fin g → C) (w' : Fin q → Fin g → C)
      (u' : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (B : Matrix (Fin (p + q)) (Fin (p + q)) C),
      LinearIndependent C v' → Submodule.span A (Set.range v') = HT.eigSub ρC σ (stdLat A C g) →
      LinearIndependent C w' → Submodule.span A (Set.range w') = HT.eigSub ρC σ' (stdLat A C g) →
      IsAdapted ρHC σ v' w' u' → LinearIndependent C (fun i => ∑ k, B i k • u' k) →
      Submodule.span A (Set.range fun i => ∑ k, B i k • u' k) = HT.eigQuot ρHC σ HV →
      ∃ ε : Aˣ, B.det = algebraMap A C ε * gm) →
    LinearIndependent C v → Submodule.span C (Set.range v) = HT.eigSp ρC σ →
    Submodule.span A (Set.range v) = HT.eigSub ρC σ (stdLat A C g) →
    LinearIndependent C w → Submodule.span C (Set.range w) = HT.eigSp ρC σ' →
    Submodule.span A (Set.range w) = HT.eigSub ρC σ' (stdLat A C g) →
    ∃ ε : Aˣ, Ap.det * Q.det = algebraMap A C ε * gm * P.det := by
  intro E _ _ C A _ _ _ _ bar σ σ' g p q ρC ρHC HV tC b₁ v b₂ w u Ap P Q gm h1 h2 h3 h4 hA hfree had hvP hwQ hb₁
    hAp H hv hvspan hvA hw hwspan hwA
  obtain ⟨u', hu'ad, -, hu'span⟩ :=
    GlobalTheory.T.hermitian_signature_basis E C (Fin g → C) ρC ρHC bar σ σ' p q v w h1 h2 h3 h4 hv hvspan hw hwspan
  have hP := isUnit_det_of_linearIndependent_frame P v b₁ hvP hv
  have hQ := isUnit_det_of_linearIndependent_frame Q w b₂ hwQ hw
  obtain ⟨B0, hB0, hB0det⟩ := GlobalTheory.T.adapted_bases_change_by_block_matrices E C (Fin g → C) ρHC σ p q v b₁ w b₂ u' u P⁻¹ Q⁻¹ hu'ad had hv
    hu'span (eq_sum_inv_smul_of_eq_sum_smul P hP v b₁ hvP) (eq_sum_inv_smul_of_eq_sum_smul Q hQ w b₂ hwQ)
  have hcomb := eq_sum_mul_smul_of_eq_sum_smul_of_eq_sum_smul Ap B0 (fun i => HT.eigProj ρHC σ (tC i)) u u' hAp hB0
  have hfam : (fun i => ∑ k, (Ap * B0) i k • u' k) = fun i => HT.eigProj ρHC σ (tC i) :=
    funext fun i => (hcomb i).symm
  have hli : LinearIndependent C (fun i => HT.eigProj ρHC σ (tC i)) :=
    GlobalTheory.CompanionTheory.Ar.Flat.HodgeDeterminantLattice.linearIndependent_eigProj σ hfree
  have hsp : Submodule.span A (Set.range fun i => HT.eigProj ρHC σ (tC i)) = HT.eigQuot ρHC σ HV :=
    (GlobalTheory.CompanionTheory.Ar.Flat.HodgeDeterminantLattice.eigQuot_eq_span σ hfree hA).symm
  obtain ⟨ε, hε⟩ := H v w u' (Ap * B0) hv hvA hw hwA hu'ad (by rw [hfam]; exact hli) (by rw [hfam]; exact hsp)
  refine ⟨ε, ?_⟩
  rw [Matrix.det_mul] at hε
  rw [Matrix.det_nonsing_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Ring.inverse_eq_inv] at hB0det
  have hPd : P.det ≠ 0 := hP.ne_zero
  have hQd : Q.det ≠ 0 := hQ.ne_zero
  have hB : B0.det = Q.det * (P.det)⁻¹ := by
    rw [← hB0det, _root_.mul_comm Q.det, _root_.mul_assoc, inv_mul_cancel₀ hQd, _root_.mul_one]
  calc Ap.det * Q.det = Ap.det * B0.det * P.det := by
        rw [hB, _root_.mul_assoc, _root_.mul_assoc, inv_mul_cancel₀ hPd, _root_.mul_one]
    _ = algebraMap A C ε * gm * P.det := by rw [hε]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResidueHodgeLatticeAdaptedBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_hodge_lattice_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] (C A : Type) [Field C] [CharZero C] [CommRing A] [Algebra A C]
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (g p q : ℕ) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C)))
    (tC : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (b₁ v : Fin p → Fin g → C) (b₂ w : Fin q → Fin g → C)
    (u : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (Ap : Matrix (Fin (p + q)) (Fin (p + q)) C)
    (P : Matrix (Fin p) (Fin p) C) (Q : Matrix (Fin q) (Fin q) C) (gm : C),
    (∀ a y, (ρHC a y).1 = ρC a y.1) → (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A C).range) → HT.IsFreeOn ρHC HV tC →
    IsAdapted ρHC σ b₁ b₂ u → (∀ i, v i = ∑ k, P i k • b₁ k) → (∀ i, w i = ∑ k, Q i k • b₂ k) →
    LinearIndependent C b₁ → (∀ i, HT.eigProj ρHC σ (tC i) = ∑ k, Ap i k • u k) →
    (∀ (v' : Fin p → Fin g → C) (w' : Fin q → Fin g → C)
      (u' : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (B : Matrix (Fin (p + q)) (Fin (p + q)) C),
      LinearIndependent C v' → Submodule.span A (Set.range v') = HT.eigSub ρC σ (stdLat A C g) →
      LinearIndependent C w' → Submodule.span A (Set.range w') = HT.eigSub ρC σ' (stdLat A C g) →
      IsAdapted ρHC σ v' w' u' → LinearIndependent C (fun i => ∑ k, B i k • u' k) →
      Submodule.span A (Set.range fun i => ∑ k, B i k • u' k) = HT.eigQuot ρHC σ HV →
      ∃ ε : Aˣ, B.det = algebraMap A C ε * gm) →
    LinearIndependent C v → Submodule.span C (Set.range v) = HT.eigSp ρC σ →
    Submodule.span A (Set.range v) = HT.eigSub ρC σ (stdLat A C g) →
    LinearIndependent C w → Submodule.span C (Set.range w) = HT.eigSp ρC σ' →
    Submodule.span A (Set.range w) = HT.eigSub ρC σ' (stdLat A C g) →
    ∃ ε : Aˣ, Ap.det * Q.det = algebraMap A C ε * gm * P.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame <;> assumption)
end
end
