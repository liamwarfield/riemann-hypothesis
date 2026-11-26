module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscCoverLatticeBasisRealHolomorphic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixBoundaryExtensionMonodromyPosSemidef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalSymplecticBasisAdaptedCoisotropicStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefImPartOnPolydiscOfPuncturedCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodChartHolomorphicLatticeFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodFrameOfHolomorphicLatticeFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodFrameOfHolomorphicLatticeFamily
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PeriodFrame.exists_frame_of_latFam : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (d ρ₁ : ℝ) (P τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (Δ : (Fin n → ℂ) → Matrix {j : Fin g // rk ≤ j.val} {j : Fin g // rk ≤ j.val} ℂ), 0 < ρ₁ ∧ ρ₁ ≤ 1 ∧ 0 < d ∧ rk ≤ g ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, IsUnit (P z).det) ∧ (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) ∧ (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (((τ s).map Complex.im).map Complex.ofReal)⁻¹) ∧ ContinuousOn Δ (Metric.ball 0 ρ₁) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, ((Δ z).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).submatrix Subtype.val Subtype.val = Δ (logExp a s)) ∧ (∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 ρ₁) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).mulVec (fun j => (v j : ℂ)) = F (logExp a s)) := by
  intro n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlamc hlam hH htor
  obtain ⟨hDo, hDc, hDan, hDmaps⟩ := GlobalTheory.logDom_chart_props n a
  have hlogc : Continuous (logExp a : (Fin n → ℂ) → Fin n → ℂ) :=
    continuous_iff_continuousAt.2 fun s => (hDan s).continuousAt
  set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀def
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_ofPred_eq]
    intro k
    by_cases h : (k : ℕ) < a <;> simp [s₀, h]
  obtain ⟨hr, hlamR, hlamD⟩ := GlobalTheory.T.punctPolydiscCover_latticeBasis_real_holomorphic n a g r K lam hK hlamc hlam
  have hlB : ∀ b ∈ logDom n a, IsLatBasis (K (logExp a b)) (lam b) := fun b hb => ⟨hlamR b hb, (hlam b hb).2.2⟩
  have hmemL : ∀ b ∈ logDom n a, ∀ i, lam b i ∈ K (logExp a b) := fun b hb i =>
    ((hlam b hb).2.2 _).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  have hpre : _root_.IsPreconnected (logDom n a) := hDc.isPreconnected
  have hζc : ContinuousOn (fun s => ζ (logExp a s)) (logDom n a) := hζ.continuousOn.comp hlogc.continuousOn hDmaps
  have hcex' : ∀ i : Fin r₀, ∃ m : Fin r → ℤ, ∀ b ∈ logDom n a, ζ (logExp a b) i = ∑ j, m j • lam b j := fun i =>
    GlobalTheory.ShFam.Hor.LogCh.exists_const_coords n g r (logDom n a) (fun b => K (logExp a b)) lam
      (fun b => ζ (logExp a b) i) s₀ hpre hlamc ((continuous_apply i).comp_continuousOn hζc) hlB
      (fun b hb => hζK _ (hDmaps hb) i) hs₀
  have hcex : ∃ c : Matrix (Fin r₀) (Fin r) ℤ, ∀ i, ∀ b ∈ logDom n a, ζ (logExp a b) i = ∑ j, c i j • lam b j := by
    choose c hc using hcex'
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hcex
  have hsh := fun (k : Fin a) (s : Fin n → ℂ) (hs : s ∈ logDom n a) => GlobalTheory.PeriodFrame.shift_mem ha k hs
  have hTex' : ∀ (k : Fin a) (i : Fin r), ∃ m : Fin r → ℤ, ∀ b ∈ logDom n a,
      lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i = ∑ j, m j • lam b j := fun k i =>
    GlobalTheory.ShFam.Hor.LogCh.exists_const_coords n g r (logDom n a) (fun b => K (logExp a b)) lam
      (fun b => lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i) s₀ hpre hlamc
      ((continuous_apply i).comp_continuousOn
        (hlamc.comp (continuous_id.add continuous_const).continuousOn fun b hb => (hsh k b hb).1))
      hlB (fun b hb => by rw [← (hsh k b hb).2]; exact hmemL _ (hsh k b hb).1 i) hs₀
  have hTex : ∃ T : Fin a → Matrix (Fin r) (Fin r) ℤ, ∀ k i, ∀ b ∈ logDom n a,
      lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i = ∑ j, T k i j • lam b j := by
    choose T hT using hTex'
    exact ⟨T, hT⟩
  obtain ⟨T, hT⟩ := hTex
  obtain ⟨Hm₀, hH₀h, hH₀p, hH₀l⟩ := hH s₀ hs₀
  have hM₀ := hH₀l s₀ hs₀ rfl
  have hMa : Mᵀ = -M := GlobalTheory.T.hermForm_im_intMatrix_transpose_neg g r Hm₀ (lam s₀) M hH₀h hM₀
  have hMd : M.det ≠ 0 :=
    GlobalTheory.det_ne_zero_of_im_hermForm_eq_int g r Hm₀ (lam s₀) M hH₀p (hlamR s₀ hs₀) (hlam s₀ hs₀).2.1 hM₀
  have hTM : ∀ k, T k * M * (T k)ᵀ = M := by
    intro k
    have h1 := GlobalTheory.T.hermForm_im_intCombination_eq_conj_mul g r r Hm₀ (lam s₀) (lam (s₀ + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)))
      (T k) M (fun i => hT k i s₀ hs₀) hM₀
    have h2 := hH₀l _ (hsh k s₀ hs₀).1 (hsh k s₀ hs₀).2
    ext i j
    have h3 := (h1 i j).symm.trans (h2 i j)
    exact_mod_cast h3
  have hcT : ∀ k, c * T k = c := fun k =>
    GlobalTheory.T.coeffMatrix_mul_eq_of_same_intCombinations g r r₀ (lam s₀) (lam (s₀ + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)))
      (ζ (logExp a s₀)) c (T k) (hlam s₀ hs₀).1 (fun i => hT k i s₀ hs₀) (fun i => hc i s₀ hs₀)
      (fun i => by rw [← (hsh k s₀ hs₀).2]; exact hc i _ (hsh k s₀ hs₀).1)
  have hcLI : LinearIndependent ℚ (fun i j => (c i j : ℚ)) :=
    GlobalTheory.rowsInd_rat_of_real g r r₀ (lam s₀) (ζ (logExp a s₀)) c (hζi _ (hDmaps hs₀)) (fun i => hc i s₀ hs₀)
  have hco := GlobalTheory.CoisoCount.coisotropic_of_torsion_count r r₀ M c hMd hcLI (by
    intro N hN
    obtain ⟨S, hcard, hS⟩ := htor N hN
    refine ⟨S, by rw [hr]; exact hcard, fun u u' hu => ?_⟩
    obtain ⟨m, hm⟩ := hS u u' hu s₀ hs₀ Hm₀ hM₀
    rw [GlobalTheory.T.hermForm_im_intCombination_dotProduct g r r₀ Hm₀ (lam s₀) (ζ (logExp a s₀)) c M (fun i => hc i s₀ hs₀) hM₀ u u'] at hm
    exact ⟨m, by exact_mod_cast hm⟩)
  obtain ⟨rk, α, φ, β, gm, dl, hrk, hN1, hN2, hN3, hN4, hN5, hN6, hN7⟩ := GlobalTheory.T.exists_rational_symplecticBasis_adapted_coisotropic g r r₀ M c hr hMa hMd hcLI hco
  choose b hb using fun k => GlobalTheory.T.intIsometry_fixing_rowSpace_symplectic_shift g r r₀ rk M (T k) c α φ β hr hMa (hTM k) (hcT k) hN1 hN2 hN3 hN5
  obtain ⟨D, Bz, hD, hBz⟩ := GlobalTheory.T.exists_common_denominator_rat_matrices a g b
  have hBzs : ∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → Bz k j l = 0 := by
    intro k j l h
    have h1 := hBz k j l
    rw [(hb k).1 j l h, mul_zero] at h1
    exact_mod_cast h1
  have hPeq : ∀ s ∈ logDom n a, GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α =
      GlobalTheory.PeriodFrame.combMat (lam s) (α * c.map (Int.cast : ℤ → ℚ)) :=
    fun s hs => GlobalTheory.PeriodFrame.combMat_comb _ _ c α (fun i => hc i s hs)
  have hRie : ∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧
      IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det ∧ (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).IsSymm ∧
      ((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).PosDef ∧
      (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α)ᵀᴴ =
        ((D : ℝ) : ℂ) • (((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).map Complex.ofReal)⁻¹ := by
    intro s hs
    obtain ⟨Hm, h1, h2, h3⟩ := hH s hs
    refine ⟨Hm, h3 s hs rfl, ?_⟩
    unfold GlobalTheory.PeriodFrame.perTau
    rw [hPeq s hs]
    exact GlobalTheory.T.riemannRelations_rationalCombinationFrame g r Hm M (lam s) _ φ D hD h1 h2 (hlamR s hs) (h3 s hs rfl) hN1 hN2 hN3
  have hdet : ∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det := fun s hs => by
    obtain ⟨_, _, h, _⟩ := hRie s hs
    exact h
  obtain ⟨hPd, hτd⟩ := GlobalTheory.T.differentiableOn_rationalFrame_periodMatrix_logCover n a g r₀ r ζ lam α φ D hζ hlamD hdet
  have hτsm : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).IsSymm ∧
      ((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).PosDef := fun s hs _ => by
    obtain ⟨_, _, _, h1, h2, _⟩ := hRie s hs
    exact ⟨h1, h2⟩
  have hmono : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∀ k : Fin a,
      GlobalTheory.PeriodFrame.perTau a ζ lam α φ D (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) =
        GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s + (Bz k).map (Int.cast : ℤ → ℂ) := by
    intro s hs _ k
    unfold GlobalTheory.PeriodFrame.perTau
    rw [(hsh k s hs).2, hPeq s hs,
      GlobalTheory.PeriodFrame.combMat_comb (lam (s + _)) (lam s) (T k) φ (fun i => hT k i s hs), (hb k).2]
    exact GlobalTheory.PeriodFrame.combMat_shift (lam s) _ φ (b k) D (Bz k) (hPeq s hs ▸ hdet s hs) (hBz k)
  obtain ⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩ :=
    GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef n a g ha 1 (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D) Bz one_pos le_rfl hτd hτsm hmono
  have hPu : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det :=
    GlobalTheory.T.isUnit_det_rational_combination_frame_closed_ball n a g r₀ r ha ζ lam c α φ gm dl rk D τ₀ Bz hD hζ hstd (fun s hs i => hc i s hs) hN7 hN6 hdet hτ₀d
      hBzs hτ₀e
  have hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 1) := fun j l => (hτ₀d j l).continuousOn
  have hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
        (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) =
        (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
          (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) := by
    intro s hs hz
    rw [hτ₀e s hs hz]
    ext ⟨j, hj⟩ ⟨l, hl⟩
    simp [Matrix.sum_apply, hBzs _ j l (Or.inl hj)]
  refine ⟨rk, (D : ℝ), 1, fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α, GlobalTheory.PeriodFrame.perTau a ζ lam α φ D, Bz,
    fun z => (τ₀ z).submatrix Subtype.val Subtype.val, one_pos, le_rfl, by exact_mod_cast hD, hrk, hPd, hPu, hτd,
    hτsm, hmono, hBzs, ?_, ?_, ?_, hagree, ?_⟩
  · intro s hs hz Hm hHm
    obtain ⟨Hm', h1, _, _, _, h5⟩ := hRie s hs
    have hHH : Hm = Hm' :=
      GlobalTheory.T.complexMatrix_eq_of_hermForm_im_eq_real_span g r Hm Hm' (lam s) (hlam s hs).2.1 (fun i j => (hHm i j).trans (h1 i j).symm)
    subst hHH
    exact h5
  · exact continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1
  · refine GlobalTheory.T.posDef_imPart_on_polydisc_of_punctured_cover n a {j : Fin g // rk ≤ j.val} (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
      (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g))
      (fun j l => hτ₀d j.1 l.1) ?_
    intro s hs
    rw [← hagree s hs (hDmaps hs)]
    exact (hτsm s hs (hDmaps hs)).2.submatrix Subtype.val_injective
  · exact GlobalTheory.T.not_periodMatrix_intVec_continuous_boundary n a g r₀ r K ζ lam M c α φ rk D hK hζ hζK hζ0 (fun s hs => ⟨hlamR s hs, (hlam s hs).2.2⟩)
      (fun s hs i => hc i s hs) hMa hN3 hN4 hD hdet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodFrameOfHolomorphicLatticeFamilyStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodFrame_of_holomorphicLatticeFamily : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (d ρ₁ : ℝ) (P τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (Δ : (Fin n → ℂ) → Matrix {j : Fin g // rk ≤ j.val} {j : Fin g // rk ≤ j.val} ℂ), 0 < ρ₁ ∧ ρ₁ ≤ 1 ∧ 0 < d ∧ rk ≤ g ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, IsUnit (P z).det) ∧ (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) ∧ (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (((τ s).map Complex.im).map Complex.ofReal)⁻¹) ∧ ContinuousOn Δ (Metric.ball 0 ρ₁) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, ((Δ z).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).submatrix Subtype.val Subtype.val = Δ (logExp a s)) ∧ (∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 ρ₁) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).mulVec (fun j => (v j : ℂ)) = F (logExp a s)) := by
  first | exact @GlobalTheory.PeriodFrame.exists_frame_of_latFam | exact GlobalTheory.PeriodFrame.exists_frame_of_latFam | (intros; apply GlobalTheory.PeriodFrame.exists_frame_of_latFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodChartHolomorphicLatticeFamily
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ShFam.Hor.LogCh.exists_periodChart_of_latFam : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ d : ℝ), 0 < ρ ∧ ρ ≤ 1 ∧ 0 < d ∧ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ρ⁻¹ • logExp a s))⁻¹ := by
  intro n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor
  obtain ⟨rk, d, ρ, P, τ, B, Δ, hρ, hρ1, hd, hrk, hP, hPdet, hτd, hτs, hτm, hB, hPH, hΔc, hΔp, hτΔ, hcl⟩ :=
    GlobalTheory.T.exists_periodFrame_of_holomorphicLatticeFamily n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor
  obtain ⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩ := GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef n a g ha ρ τ B hρ hρ1 hτd hτs hτm
  have hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 ρ) := fun j l => (hτ₀d j l).continuousOn
  have hmv : ∀ (k : Fin a) (v : Fin g → ℤ), ((B k).map (Int.cast : ℤ → ℂ)).mulVec (fun j => (v j : ℂ)) =
      fun i => (((B k).mulVec v i : ℤ) : ℂ) := by
    intro k v; ext i; simp [Matrix.mulVec, dotProduct]
  have htoric : (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix
      (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef := by
    by_contra hnot
    obtain ⟨v, hv0, hvs, hBv⟩ := GlobalTheory.T.exists_common_int_kernel_psd_block_not_posDef a g rk B hpsd hB hnot
    refine hcl v hv0 hvs (fun z => (τ₀ z).mulVec (fun j => (v j : ℂ))) ?_ ?_
    · refine continuousOn_pi.2 fun j => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact continuousOn_finsetSum _ fun l _ => (hcont j l).mul continuousOn_const
    · intro s hs hz
      rw [hτ₀e s hs hz, Matrix.add_mulVec]
      have h0 : (∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)).mulVec
          (fun j => (v j : ℂ)) = 0 := by
        rw [Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Matrix.smul_mulVec, hmv, hBv k]
        ext i; simp
      rw [h0, add_zero]
  have hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ →
      (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val = Δ (logExp a s) := by
    intro s hs hz
    rw [← hτΔ s hs hz, hτ₀e s hs hz]
    ext ⟨j, hj⟩ ⟨l, hl⟩
    simp [Matrix.sum_apply, hB _ j l (Or.inl hj)]
  have heq := GlobalTheory.T.eqOn_ball_of_eqOn_punctPolydiscCoveringExp_image n a ρ _
    (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val) Δ hρ1
    (continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1) hΔc hagree
  have habel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix
      (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef := by
    intro z hz
    have h1 := hΔp z hz
    rw [← heq z hz] at h1
    exact h1
  obtain ⟨hPC, hY⟩ := GlobalTheory.T.periodChart_rescale_ball_to_unitPolydisc n a g rk ha ρ τ₀ B hρ hρ1 hrk hτ₀d hτ₀s hpsd hB htoric habel
  refine ⟨rk, _, B, P, ρ, d, hρ, hρ1, hd, hPC, hP, hPdet, ?_⟩
  intro s hs hz Hm hHm
  have hnz : ∀ i : Fin a, logExp a s (Fin.castLE ha i) ≠ 0 := by
    intro i
    simp only [logExp, Fin.coe_castLE, i.isLt, if_true]
    exact Complex.exp_ne_zero _
  rw [hPH s hs hz Hm hHm, hY _ hnz]
  congr 2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram
  congr 1
  rw [← GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period ha τ₀ B (logExp a s) (fun k => s (Fin.castLE ha k)) ?_]
  · rw [hτ₀e s hs hz]; rfl
  · intro i
    simp only [logExp, Fin.coe_castLE, i.isLt, if_true]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodChartHolomorphicLatticeFamilyStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodChart_holomorphicLatticeFamily : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ d : ℝ), 0 < ρ ∧ ρ ≤ 1 ∧ 0 < d ∧ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ρ⁻¹ • logExp a s))⁻¹ := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_periodChart_of_latFam | exact GlobalTheory.ShFam.Hor.LogCh.exists_periodChart_of_latFam | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_periodChart_of_latFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRiemannFormPeriodChartGenericFibre
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerChart

theorem hermForm_pull' {g g' : ℕ} (M : Matrix (Fin g') (Fin g) ℂ) (Hm : Matrix (Fin g') (Fin g') ℂ) (z w : Fin g → ℂ) :
    hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (M *ᵥ z) (M *ᵥ w) := by
  have : Mᵀᴴ *ᵥ (star w) = star (M *ᵥ w) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose]
    rfl
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem exists_logExp_eq (n a : ℕ) (z : Fin n → ℂ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1)
    (hnz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : ∃ s ∈ logDom n a, logExp a s = z := by
  refine ⟨fun k => if (k : ℕ) < a then Complex.log (z k) else z k, fun k => ?_, funext fun k => ?_⟩
  · have hk1 : ‖z k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 hz) k
    by_cases hk : (k : ℕ) < a
    · simp only [hk, if_true]
      rw [Complex.log_re]
      exact Real.log_neg (norm_pos_iff.2 (hnz k hk)) hk1
    · simp only [hk, if_false]
      exact hk1
  · by_cases hk : (k : ℕ) < a
    · simp only [logExp, hk, if_true]
      exact Complex.exp_log (hnz k hk)
    · simp only [logExp, hk, if_false]

theorem exists_riemann_period_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (d : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ 0 < d ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ((((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU x₀
  obtain ⟨n, a₁, g, r₀, e, ex, ζ, hx₀, he0, hEC, hbd, hsurj, hζan, hζli, hζK, hζB, hζC, hζstd⟩ :=
    GlobalTheory.T.exists_framedChart_exponential_toroidalModel E H Dw l Xo c O β Y T σ x₀
  have hEC' := hEC
  obtain ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩ := hEC'
  let a := min a₁ n
  have ha : a ≤ n := min_le_right _ _
  have hka : ∀ k : Fin n, ((k : ℕ) < a ↔ (k : ℕ) < a₁) := fun k => by
    simp only [a, lt_min_iff, k.isLt, and_true]
  have hsymm : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source := fun z hz =>
    e.map_target (by rw [htarget]; exact hz)
  have hExpAt : ∀ x ∈ e.source, IsExpAt T.Z.t (x.1 ≫ genι T.Z) (ex x) := fun x hx =>
    ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩
  have hzero : ∀ x ∈ e.source, ex x 0 = 1 := fun x hx => by
    have := hadd x hx 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hHol : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ)
      (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e.symm zw.1) zw.2).left) := htarget ▸ hjoint
  have hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsHolTo Set.univ (fun w => (ex (e.symm z) w).left) :=
    fun z hz => by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (z, w)) hHol isOpen_univ
        ((differentiableOn_const z).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hz (Set.mem_univ w)
      dsimp only at this
      exact this
  have h0 : e.symm 0 = x₀ := by rw [← he0]; exact e.left_inv hx₀
  have hmem0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hinner : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → Inner (e.symm z) :=
    fun z hz hnz => (hbd _ (hsymm z hz)).2 fun k hk => by
      rw [e.right_inv (by rw [htarget]; exact hz)]
      exact hnz k ((hka k).2 hk)
  let K : (Fin n → ℂ) → Set (Fin g → ℂ) := fun z => {w | ex (e.symm z) w = 1}
  let Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop := fun N z v w c =>
    GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm z) ((N : ℂ)⁻¹ • v)) (ex (e.symm z) ((N : ℂ)⁻¹ • w)) (unitOn c)
  have hLF : IsLatFam (Metric.ball 0 1) K :=
    GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H T.Z.X T.Z.t n g (Metric.ball 0 1) (fun z => (e.symm z).1 ≫ genι T.Z) (fun z => ex (e.symm z))
      Metric.isOpen_ball hHol fun z hz => hExpAt _ (hsymm z hz)
  have hB0 : IsLatBasis (K 0) (ζ 0) := by
    show IsLatBasis {w | ex (e.symm 0) w = 1} (ζ 0)
    rw [h0]
    exact hζB
  have hP1 : ∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c' := fun N z v w c c' h h' =>
    unitOn_injective (h.unique h')
  have hP2 : ∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ)
      (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → _root_.IsPreconnected B → DifferentiableOn ℂ φ B →
      Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B →
      (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B →
      Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c := by
    intro m N B φ v w c b₀ b₁ hN hB hBc hφ hφm hv hw hK hb₀ hb₁ h
    have h1 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • v b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hv)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    have h2 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • w b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hw)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    dsimp only at h1 h2
    exact GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family T.Z.X T.Z.t.G T.Z.t.PP T.Z.t.cub m N B (fun b => (e.symm (φ b)).1 ≫ genι T.Z)
      (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • v b)) (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • w b)) c b₀ b₁ hN hB hBc
      h1 h2
      (fun b hb => ⟨pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).1,
        pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).2⟩) hb₀ hb₁ h
  have hP3 : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
        Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧
        ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z →
          Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
            (Complex.exp_ne_zero _)) := by
    intro z hz hnz
    obtain ⟨-, Hm, hH, hpos, hspan, hint, hw⟩ := GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g (e.symm z) (ex (e.symm z))
      (hinner z hz hnz) (hExpAt _ (hsymm z hz)) (hslice z hz)
    exact ⟨Hm, hH, hpos, hspan, fun v hv w hw' => hint v w hv hw', fun N v w hN hv hw' => hw N v w _ hN hv hw' rfl⟩
  have hP4 : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → Pair N 0 (∑ j, u j • ζ 0 j) (∑ j, u' j • ζ 0 j) 1 := by
    intro N hN
    have hsl : IsHolTo Set.univ (fun w => (ex x₀ w).left) := by
      have := hslice 0 hmem0
      rw [h0] at this
      exact this
    obtain ⟨Tt, hT1, hT2, hTc⟩ := GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint E H T.Z.X T.Z.t (x₀.1 ≫ genι T.Z) g N (ex x₀) hN (hExpAt x₀ hx₀) hsurj hsl
    obtain ⟨S, hSc, hS⟩ := GlobalTheory.T.torsion_count_through_exponential_lattice_kernel _ g r₀ N (ex x₀) (ζ 0) Tt hN (hadd x₀ hx₀) hsurj hζB hT1 hTc
    refine ⟨S, hSc, fun u u' hu => ?_⟩
    show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, u j • ζ 0 j))
      (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, u' j • ζ 0 j)) (unitOn 1)
    rw [h0, unitOn_one]
    exact hT2 _ (hS u hu) _ (pow_eq_one_of_map _ (hadd x₀ hx₀) (hzero x₀ hx₀) hN ((hζB.2 _).2 ⟨u', rfl⟩))
  obtain ⟨r, lam, M, hc, hs, -, hMv, hrad⟩ :=
    GlobalTheory.ShFam.Hor.LogCh.ConstForm.constForm n a g r₀ K ζ Pair hLF hζan hζli hζK hB0 hζC hζstd hP1 hP2 hP3 hP4
  have hM' : ∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧
      (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
      ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j := by
    intro s hsD
    have hz1 : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
      intro k
      have hk := hsD k
      by_cases h : (k : ℕ) < a
      · simp only [h, if_true] at hk
        simp only [logExp, h, if_true, Complex.norm_exp]
        exact Real.exp_lt_one_iff.2 hk
      · simp only [h, if_false] at hk
        simpa only [logExp, h, if_false] using hk
    have hnz : ∀ k : Fin n, (k : ℕ) < a → logExp a s k ≠ 0 := fun k hk => by
      simp only [logExp, hk, if_true]
      exact Complex.exp_ne_zero _
    obtain ⟨Hm, hH, hpos, -, hint, hw⟩ := hP3 _ hz1 hnz
    refine ⟨Hm, hH, hpos, fun s' hs' he => hMv s' hs' Hm ?_ ?_⟩
    · rw [he]; exact hint
    · rw [he]; exact hw
  obtain ⟨rk, τ₀, B, P, ρ, d, hρ, hρ1, hd, hPC, hPd, hPu, hrel⟩ :=
    GlobalTheory.T.exists_periodChart_holomorphicLatticeFamily n a g r₀ r ha K ζ lam M hLF hζan hζli hζK hB0 hζstd hc hs hM' hrad
  obtain ⟨ch, hch, hchs, hchρ⟩ := GlobalTheory.ShFam.Hor.LogCh.isExpChart_rescale E H Dw l Xo c O β T.Z σ n g e ex P ρ hEC hρ hρ1 hPd hPu
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hcard : Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = g := by
    let z₁ : Fin n → ℂ := fun _ => (1 / 2 : ℂ)
    have hz₁ : z₁ ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
      rw [mem_ball_zero_iff]
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 fun k => ?_) (by norm_num)
      simp [z₁]
    exact (GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g (e.symm z₁) (ex (e.symm z₁))
      (hinner z₁ hz₁ fun k _ => by simp [z₁]) (hExpAt _ (hsymm z₁ hz₁)) (hslice z₁ hz₁)).1
  have hex : ∀ x ∈ ch.source, ∀ k, e x k = (ρ : ℂ) * ch x k := fun x hx k => by
    rw [hchρ x hx]
    simp [Complex.real_smul]
  have hx₀ch : x₀ ∈ ch.source := (hchs x₀).2 ⟨hx₀, by rw [he0]; exact Metric.mem_ball_self hρ⟩
  refine ⟨n, a, ha, g, rk, τ₀, B, ch, fun x v => ex x (P (e x) *ᵥ v), d, hPC, hch, hx₀ch, ?_, hcard, hd, ?_, ?_⟩
  · funext k
    have := hex x₀ hx₀ch k
    rw [he0] at this
    exact ((mul_eq_zero.1 this.symm).resolve_left hρ0)
  · intro x hx
    have hxe := ((hchs x).1 hx).1
    rw [hbd x hxe]
    constructor
    · intro h i hi
      apply h (Fin.castLE ha i) ((hka _).1 (by simp))
      rw [hex x hx, hi, mul_zero]
    · intro h k hk hk0
      apply h ⟨k, (hka k).2 hk⟩
      rw [hex x hx] at hk0
      exact (mul_eq_zero.1 hk0).resolve_left hρ0
  · intro x hx hin
    have hxe := ((hchs x).1 hx).1
    have hzb := ((hchs x).1 hx).2
    have hz1 : e x ∈ Metric.ball (0 : Fin n → ℂ) 1 := by rw [← htarget]; exact e.map_source hxe
    have hnz : ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0 := fun k hk =>
      (hbd x hxe).1 hin k ((hka k).1 hk)
    obtain ⟨s, hsD, hsz⟩ := exists_logExp_eq n a (e x) hz1 hnz
    have hsl : IsHolTo Set.univ (fun w => (ex x w).left) := by
      have := hslice (e x) hz1
      rw [e.left_inv hxe] at this
      exact this
    obtain ⟨-, Hm, hH, hpos, -, hint, hweil⟩ :=
      GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g x (ex x) hin (hExpAt x hxe) hsl
    have hKz : ∀ w, w ∈ K (logExp a s) ↔ ex x w = 1 := fun w => by
      rw [hsz]
      show ex (e.symm (e x)) w = 1 ↔ _
      rw [e.left_inv hxe]
    have hlamrel := hMv s hsD Hm (fun v hv w hw => hint v w ((hKz v).1 hv) ((hKz w).1 hw))
      (fun N v w hN hv hw => by
        show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm (logExp a s)) ((N : ℂ)⁻¹ • v))
          (ex (e.symm (logExp a s)) ((N : ℂ)⁻¹ • w)) _
        rw [hsz, e.left_inv hxe]
        exact hweil N v w _ hN ((hKz v).1 hv) ((hKz w).1 hw) rfl)
    have key := hrel s hsD (hsz ▸ hzb) Hm hlamrel
    have hchx : ρ⁻¹ • e x = ch x := by rw [hchρ x hx, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    rw [hsz, hchx] at key
    rw [← key]
    have hPinj : Function.Injective (P (e x)).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hPu _ hzb))
    refine ⟨Matrix.isHermitian_mul_mul_conjTranspose _ hH, fun u hu => ?_, fun v w hv hw => ?_,
      fun k v w ζ' hk hv hw hζ' => ?_⟩
    · rw [hermForm_pull']
      exact hpos _ (fun h0' => hu (hPinj (by rw [h0', Matrix.mulVec_zero])))
    · rw [hermForm_pull']
      exact hint _ _ hv hw
    · rw [hermForm_pull'] at hζ'
      have e1 : ∀ u : Fin g → ℂ, P (e x) *ᵥ ((k : ℂ)⁻¹ • u) = (k : ℂ)⁻¹ • (P (e x) *ᵥ u) := fun u =>
        Matrix.mulVec_smul _ _ _
      show GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x (P (e x) *ᵥ ((k : ℂ)⁻¹ • v))) (ex x (P (e x) *ᵥ ((k : ℂ)⁻¹ • w))) (unitOn ζ')
      rw [e1, e1]
      exact hweil k _ _ ζ' hk hv hw hζ'

end GlobalTheory.ShFam.Hor.LogCh.PerChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRiemannFormPeriodChartGenericFibreStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_riemannForm_periodChart_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (d : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ 0 < d ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ((((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_riemann_period_chart | exact GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_riemann_period_chart | (intros; apply GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_riemann_period_chart <;> assumption)
end
