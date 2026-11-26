module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityOfBallPotential
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetCoverOfArithmeticVariety

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.ContDiffAtBallPot
noncomputable section

namespace SheetDecomposition

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ENNReal ComplexOrder

theorem hasSum_sheets {X M : Type*} [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M] {np : ℕ}
    (FF : Fin np → Set X) (pc : ℕ → Fin np) (B : ℕ → Set X) (d : Fin np → ℕ)
    (hB : ∀ m, B m ⊆ FF (pc m)) (g : Fin np → X → M) (t : X)
    (ht : ∀ k, t ∈ FF k → {m | pc m = k ∧ t ∈ B m}.encard = d k) :
    HasSum (fun m => (B m).indicator (g (pc m)) t) (∑ k, d k • (FF k).indicator (g k) t) := by
  classical
  have hfin : ∀ k, {m | pc m = k ∧ t ∈ B m}.Finite := by
    intro k
    by_cases hk : t ∈ FF k
    · exact Set.finite_of_encard_eq_coe (ht k hk)
    · apply Set.Finite.subset Set.finite_empty
      intro m hm
      simp only [Set.mem_empty_iff_false]
      exact hk (hm.1 ▸ hB m hm.2)
  have hS : {m | t ∈ B m}.Finite := by
    have hU : {m | t ∈ B m} = ⋃ k, {m | pc m = k ∧ t ∈ B m} := by
      ext m
      simp
    rw [hU]
    exact Set.finite_iUnion hfin
  set s := hS.toFinset with hs
  have hzero : ∀ m ∉ s, (B m).indicator (g (pc m)) t = 0 := by
    intro m hm
    rw [Set.Finite.mem_toFinset] at hm
    exact Set.indicator_of_notMem (show t ∉ B m from hm) _
  suffices hsum : ∑ k, d k • (FF k).indicator (g k) t = ∑ m ∈ s, (B m).indicator (g (pc m)) t by
    rw [hsum]
    exact hasSum_sum_of_ne_finset_zero hzero
  have h1 : ∑ m ∈ s, (B m).indicator (g (pc m)) t = ∑ m ∈ s, g (pc m) t :=
    Finset.sum_congr rfl (fun m hm => Set.indicator_of_mem (show t ∈ B m from hS.mem_toFinset.mp hm) _)
  rw [h1, ← Finset.sum_fiberwise s pc (fun m => g (pc m) t)]
  apply Finset.sum_congr rfl
  intro k _
  have h2 : ∑ m ∈ s with pc m = k, g (pc m) t = ∑ m ∈ s with pc m = k, g k t :=
    Finset.sum_congr rfl (fun m hm => by rw [(Finset.mem_filter.mp hm).2])
  rw [h2, Finset.sum_const]
  by_cases hk : t ∈ FF k
  · rw [Set.indicator_of_mem hk]
    congr 1
    have hset : ((s.filter (fun m => pc m = k)) : Set ℕ) = {m | pc m = k ∧ t ∈ B m} := by
      ext m
      simp [s, and_comm]
    have hc := ht k hk
    rw [← hset, Set.encard_coe_eq_coe_finsetCard] at hc
    exact_mod_cast hc.symm
  · rw [Set.indicator_of_notMem hk, smul_zero]
    have he : s.filter (fun m => pc m = k) = ∅ := by
      ext m
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, s, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq]
      intro hm h
      exact hk (h ▸ hB m hm)
    rw [he, Finset.card_empty, zero_smul]

theorem sum_sheets {X : Type*} [MeasurableSpace X] (μ : Measure X) {np : ℕ}
    (FF : Fin np → Set X) (pc : ℕ → Fin np) (B : ℕ → Set X) (d : Fin np → ℕ)
    (hF : ∀ k, MeasurableSet (FF k)) (hBm : ∀ m, MeasurableSet (B m))
    (hB : ∀ m, B m ⊆ FF (pc m)) (f : Fin np → X → ℝ)
    (hc : ∀ k, ∀ᵐ t ∂μ, t ∈ FF k → {m | pc m = k ∧ t ∈ B m}.encard = d k)
    (hf : ∀ k, IntegrableOn (f k) (FF k) μ) :
    Summable (fun m => ∫ t in B m, |f (pc m) t| ∂μ) ∧
      ∑' m, ∫ t in B m, f (pc m) t ∂μ = ∑ k, (d k : ℝ) * ∫ t in FF k, f k t ∂μ := by
  classical
  set F : ℕ → X → ℝ := fun m => (B m).indicator (f (pc m)) with hFdef
  have hFint : ∀ m, Integrable (F m) μ := fun m =>
    ((hf (pc m)).mono_set (hB m)).integrable_indicator (hBm m)
  have hInt : ∀ m, ∫ t in B m, f (pc m) t ∂μ = ∫ t, F m t ∂μ := fun m =>
    (integral_indicator (hBm m)).symm
  have hIntAbs : ∀ m, ∫ t in B m, |f (pc m) t| ∂μ = (∫⁻ t, ‖F m t‖ₑ ∂μ).toReal := by
    intro m
    rw [← integral_norm_eq_lintegral_enorm (hFint m).aestronglyMeasurable, ← integral_indicator (hBm m)]
    congr 1
    ext t
    by_cases ht : t ∈ B m <;> simp [F, ht, Real.norm_eq_abs]
  have hae : ∀ᵐ t ∂μ, ∀ k, t ∈ FF k → {m | pc m = k ∧ t ∈ B m}.encard = d k := ae_all_iff.mpr hc
  have hmeas : ∀ k, AEMeasurable (fun t => (d k : ℝ≥0∞) * (FF k).indicator (fun x => ‖f k x‖ₑ) t) μ := by
    intro k
    apply AEMeasurable.const_mul
    exact (aemeasurable_indicator_iff (hF k)).mpr (hf k).aestronglyMeasurable.enorm
  have hlin : ∑' m, ∫⁻ t, ‖F m t‖ₑ ∂μ = ∑ k, (d k : ℝ≥0∞) * ∫⁻ t in FF k, ‖f k t‖ₑ ∂μ := by
    rw [← lintegral_tsum (fun m => (hFint m).aestronglyMeasurable.enorm)]
    have hae1 : ∀ᵐ t ∂μ, ∑' m, ‖F m t‖ₑ =
        ∑ k, (d k : ℝ≥0∞) * (FF k).indicator (fun x => ‖f k x‖ₑ) t := by
      filter_upwards [hae] with t ht
      have h := hasSum_sheets FF pc B d hB (fun k x => ‖f k x‖ₑ) t ht
      simp only [nsmul_eq_mul] at h
      rw [← h.tsum_eq]
      congr 1
      ext m
      by_cases hm : t ∈ B m <;> simp [F, hm]
    rw [lintegral_congr_ae hae1, lintegral_finsetSum' _ (fun k _ => hmeas k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_indicator (hF k)]
  have hne : ∑' m, ∫⁻ t, ‖F m t‖ₑ ∂μ ≠ ⊤ := by
    rw [hlin]
    exact (ENNReal.sum_lt_top.mpr fun k _ =>
      ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (hf k).hasFiniteIntegral).ne
  constructor
  · simp_rw [hIntAbs]
    exact ENNReal.summable_toReal hne
  · simp_rw [hInt]
    rw [← integral_tsum (fun m => (hFint m).aestronglyMeasurable) hne]
    have hae2 : ∀ᵐ t ∂μ, ∑' m, F m t = ∑ k, (d k : ℝ) * (FF k).indicator (f k) t := by
      filter_upwards [hae] with t ht
      have h := (hasSum_sheets FF pc B d hB f t ht).tsum_eq
      simpa only [nsmul_eq_mul] using h
    rw [integral_congr_ae hae2,
      integral_finsetSum _ (fun k _ => ((hf k).integrable_indicator (hF k)).const_mul _)]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, integral_indicator (hF k)]

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem contDiff_ballDet (q : Ψ × Fin j × Fin j' ≃ Fin n) (τ : Ψ) :
    ContDiff ℝ 2 fun t => (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det := by
  have hent : ∀ a b, ContDiff ℝ 2 fun t : Fin n → ℂ =>
      ((1 - (ballMat q t τ)ᴴ * ballMat q t τ : Matrix (Fin j') (Fin j') ℂ)) a b := by
    intro a b
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, ballMat, Matrix.of_apply]
    apply contDiff_const.sub
    apply ContDiff.sum
    intro c _
    apply ContDiff.mul
    · exact (Complex.conjCLE.contDiff).comp (contDiff_apply ℝ (fun _ => ℂ) _)
    · exact contDiff_apply ℝ (fun _ => ℂ) _
  simp only [Matrix.det_apply]
  apply ContDiff.sum
  intro σ _
  apply ContDiff.const_smul
  apply contDiff_prod
  intro i _
  exact hent _ _

theorem contDiffAt_ballPot (q : Ψ × Fin j × Fin j' ≃ Fin n) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    ContDiffAt ℝ 2 (fun t' => ballPot q t' / 2) t := by
  refine ContDiffAt.div_const (ContDiffAt.neg (ContDiffAt.sum fun τ _ => ?_)) _
  refine ContDiffAt.log (Complex.reCLM.contDiff.comp (contDiff_ballDet q τ)).contDiffAt ?_
  exact (Complex.pos_iff.1 (ht τ).det_pos).1.ne'

theorem zero_mem_ballDom (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by ext a b; simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

theorem ballDens_zero (q : Ψ × Fin j × Fin j' ≃ Fin n) : ballDens q 0 = 1 := by
  have : ∀ τ, ballMat q 0 τ = 0 := fun τ => by ext a b; simp [ballMat]
  simp [ballDens, ballPot, this]

theorem ballPot_renumber {Ψ' : Type} [Fintype Ψ'] (e : Ψ ≃ Ψ') (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (q' : Ψ' × Fin j × Fin j' ≃ Fin n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ t, ballPot q t = ballPot q' (fun i => t (σ i)) := by
  refine ⟨q'.symm.trans ((Equiv.prodCongr e.symm (Equiv.refl _)).trans q), fun t => ?_⟩
  have hB : ∀ τ', ballMat q' (fun i => t ((q'.symm.trans
      ((Equiv.prodCongr e.symm (Equiv.refl _)).trans q)) i)) τ' = ballMat q t (e.symm τ') := by
    intro τ'
    ext a b
    simp [ballMat]
  simp only [ballPot, hB]
  congr 1
  exact (Equiv.sum_comp e.symm
    (fun τ => Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re)).symm

theorem norm_det_perm (σ : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    ‖LinearMap.det ((fderiv ℂ (fun (t : Fin n → ℂ) i => t (σ i)) t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ = 1 := by
  set L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' (σ.permMatrix ℂ)) with hLdef
  have hL : (fun (t : Fin n → ℂ) i => t (σ i)) = ⇑L := by
    funext s
    simp [L, Matrix.toLin'_apply, Matrix.permMatrix_mulVec]
    rfl
  rw [hL, L.fderiv]
  have hdet : LinearMap.det (L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
    simp [L, LinearMap.det_toLin', Matrix.det_permutation]
  rw [hdet]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

end SheetDecomposition
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace SheetDecomposition

theorem densU : ∃ κ : ℕ → ℕ → ℕ → ℝ, (∀ f j j', 0 < κ f j j') ∧
    ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n), ∀ t ∈ ballDom q,
      maDensity (fun (_ : Fin n) t' => ballPot q t' / 2) t = κ (Fintype.card Ψ) j j' * ballDens q t := by
  have hq : ∀ f j j' : ℕ, Nonempty (Fin f × Fin j × Fin j' ≃ Fin (f * j * j')) := fun f j j' =>
    ⟨Fintype.equivFinOfCardEq (by simp [_root_.mul_assoc])⟩
  choose κ hκ hκ' using fun f j j' : ℕ => GlobalTheory.T.monge_ampere_density_of_ball_potential (Fin f) j j' (f * j * j') (hq f j j').some
  refine ⟨κ, hκ, fun Ψ _ j j' n q t ht => ?_⟩
  obtain rfl : n = Fintype.card Ψ * j * j' := by
    have := Fintype.card_congr q
    simpa [_root_.mul_assoc] using this.symm
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.monge_ampere_density_of_ball_potential Ψ j j' _ q
  rw [hc t ht]
  congr 1
  have h0 := hc 0 (zero_mem_ballDom q)
  have h1 := hκ' (Fintype.card Ψ) j j' 0 (zero_mem_ballDom _)
  rw [ballDens_zero, _root_.mul_one] at h0 h1
  rw [← h0, ← h1]
  obtain ⟨σ, hσ⟩ := ballPot_renumber (Fintype.equivFin Ψ) q (hq (Fintype.card Ψ) j j').some
  have h2 := GlobalTheory.T.monge_ampere_density_change_of_variables _ (fun t' => ballPot (hq (Fintype.card Ψ) j j').some t' / 2) (fun t' => ballPot q t' / 2)
    (fun t i => t (σ i)) (fun _ => 0) 0
    (analyticAt_pi_iff.2 fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (σ i)).analyticAt 0)
    analyticAt_const (contDiffAt_ballPot _ (zero_mem_ballDom _))
    (Eventually.of_forall fun t' => by simp [hσ t'])
  rw [h2, norm_det_perm, one_pow, _root_.one_mul]
  rfl

theorem norm_det_id (n : ℕ) (t : Fin n → ℂ) :
    ‖LinearMap.det ((fderiv ℂ (fun t : Fin n → ℂ => t) t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ = 1 :=
  norm_det_perm (Equiv.refl _) t

theorem transferU : ∃ κ : ℕ → ℕ → ℕ → ℝ, (∀ f j j', 0 < κ f j j') ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or) (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ Dc.f Dc.j Dc.j' * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t := by
  obtain ⟨κ, hκ, hd⟩ := densU
  refine ⟨κ, hκ, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q G Gk hG hGk hint
  have hdens : ∀ m, ∀ t ∈ Q.V m, maDensity (fun (_ : Fin Dc.n) t' => Real.log ((muLine Hd).h (Q.γ m t'))) t =
      κ Dc.f Dc.j Dc.j' * ballDens (Q.F (Q.pc m)).q t := by
    intro m t ht
    obtain ⟨g, hg, hev⟩ := Q.pot m t ht
    have h2 := GlobalTheory.T.monge_ampere_density_change_of_variables _ (fun t' => ballPot (Q.F (Q.pc m)).q t' / 2)
      (fun t' => Real.log ((muLine Hd).h (Q.γ m t'))) (fun t => t) g t analyticAt_id hg
      (contDiffAt_ballPot _ (Q.V_sub m ht)) hev
    rw [h2, norm_det_id, one_pow, _root_.one_mul]
    exact hd _ _ _ _ _ t (Q.V_sub m ht)
  have hsm : ∀ m, ContDiffOn ℝ 2 (fun t => Real.log ((muLine Hd).h (Q.γ m t))) (Q.V m) := by
    intro m t ht
    obtain ⟨g, hg, hev⟩ := Q.pot m t ht
    have hψ : ContDiffAt ℝ 2 (fun y => (g y).re) t :=
      Complex.reCLM.contDiff.contDiffAt.comp t (hg.contDiffAt.restrict_scalars ℝ)
    exact (((contDiffAt_ballPot _ (Q.V_sub m ht)).add hψ).congr_of_eventuallyEq hev).contDiffWithinAt
  have heq : ∀ m, Set.EqOn
      (fun t => G (Q.γ m t) * maDensity (fun (_ : Fin Dc.n) t' => Real.log ((muLine Hd).h (Q.γ m t'))) t)
      (fun t => κ Dc.f Dc.j Dc.j' * (Gk (Q.pc m) t * ballDens (Q.F (Q.pc m)).q t)) (Q.B m) := by
    intro m t ht
    have hV := (Q.cover.meas m).2 ht
    simp only
    rw [hdens m t hV, hGk m t hV]
    ring
  have hint' : ∀ k, IntegrableOn (fun t => κ Dc.f Dc.j Dc.j' * (Gk k t * ballDens (Q.F k).q t)) (Q.FF k) :=
    fun k => (hint k).const_mul _
  obtain ⟨hs1, hs2⟩ := sum_sheets volume Q.FF Q.pc Q.B Q.d (fun k => (Q.fund k).1) (fun m => (Q.cover.meas m).1)
    Q.B_sub (fun k t => κ Dc.f Dc.j Dc.j' * (Gk k t * ballDens (Q.F k).q t)) Q.count hint'
  have key := GlobalTheory.T.sheet_cover_of_arithmetic_variety K J (mCoordIdeal Dc.y) Dc.n Dc.nCharts Dc.Bd Dc.chart Q.V Q.B Q.γ (muLine Hd) G Dc.arith
    (fun z hz => by
      obtain ⟨a, t, ht, cc, hc, rfl⟩ := Dc.chart_cover z hz
      exact ⟨a, t, ht, _, rfl, cc, hc, rfl⟩)
    Q.cover hsm hG
    (fun m => ((hint' (Q.pc m)).mono_set (Q.B_sub m)).congr_fun (heq m).symm (Q.cover.meas m).1)
    (hs1.congr fun m => setIntegral_congr_fun (Q.cover.meas m).1 fun t ht => congrArg abs (heq m ht).symm)
  refine key.trans ?_
  rw [tsum_congr fun m => setIntegral_congr_fun (Q.cover.meas m).1 (heq m), hs2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  ring

theorem sheet_pieces_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t := by
  obtain ⟨κ, hκ, h⟩ := transferU
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q
  exact ⟨κ Dc.f Dc.j Dc.j', hκ _ _ _, h E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q⟩

end SheetDecomposition
