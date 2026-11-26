module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFromOrbitCharts
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecond
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartNinth

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFifth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedFrameValueFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedFrameValueFormula
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem sameOrbit_sqZ_of_flags : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (zb₂ : (Σ k, baseIdx ι M.blk k) → ℂ) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) (H U : Ψ → Matrix (Fin N) (Fin N) ℂ) (V : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.blk (τ, a) = some k₀ → baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) → SameOrbit zb₂ (baseOf M k₀ z) → (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) → IsBlockDiag j V → V.BlockTriangular id → (∀ c ∈ stepCols N j a, V c c ≠ 0) → (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (H p.1 * U p.1) I (stepCols N j p.2)) → (∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (H τ * (1 + Matrix.single cb ca t) * V) I (stepCols N j a)) → SameOrbit (sqZ M F zb₂ H k₀ τ ca cb t) z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a k₀ ca cb F zb₂ z H U V t hτ hz hG ho hU hV hVt hVd h1 h2
  have hval : ∀ s, valAt M.x s zb₂ = valAt M.x s (baseOf M k₀ z) := fun s =>
    CovMap.LocImg.valAt_orbit ho hz s
  have block : ∀ o : Option K, ∃ c : ℂ, c ≠ 0 ∧ ∀ m : ι (o.getD k₀),
      sqZ M F zb₂ H k₀ τ ca cb t ⟨o, m⟩ = c * z ⟨o, m⟩ := by
    rintro (_ | k)
    · have e : ∃ p, M.blk p = some k₀ := ⟨_, hτ⟩
      have hc : e.choose = (τ, a) := M.blk_inj _ _ k₀ e.choose_spec hτ
      obtain ⟨α, hα, hm⟩ := (WSq.Pts.step_mul_right M.j_le a hV hVt hVd
        (fun m : ι k₀ => sndPt k₀ z ⟨k₀, m⟩)
        (fun m I => valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z))).1 h2
      refine ⟨α⁻¹, inv_ne_zero hα, fun m => ?_⟩
      have hs : sqZ M F zb₂ H k₀ τ ca cb t ⟨none, m⟩ =
          ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
            minorIJ (H τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) := by
        show flagZ M F zb₂ (Function.update H τ (H τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩ = _
        refine (dif_pos e).trans ?_
        simp only [hc, Function.update_self, hval]
      have hn : z ⟨none, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
          minorIJ (H τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) :=
        (WSq.Pts.snd_self z m).symm.trans (hm m)
      rw [hs, hn, inv_mul_cancel_left₀ hα]
    · by_cases e : ∃ p, M.blk p = some k
      · obtain ⟨α, hα, hm⟩ := (WSq.Pts.step_mul_right M.j_le e.choose.2 (hU e.choose.1).1 (hU e.choose.1).2.1
          (fun c _ => (hU e.choose.1).2.2 c) (fun m : ι k => fstPt k₀ z ⟨k, m⟩)
          (fun m I => valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z))).1 (h1 e.choose k e.choose_spec)
        refine ⟨α⁻¹, inv_ne_zero hα, fun m => ?_⟩
        have hs : sqZ M F zb₂ H k₀ τ ca cb t ⟨some k, m⟩ =
            ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) *
              minorIJ (H e.choose.1) I (stepCols N j e.choose.2) := by
          show flagZ M F zb₂ H ⟨k, m⟩ = _
          refine (dif_pos e).trans ?_
          simp only [hval]
        have hn : z ⟨some k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) *
            minorIJ (H e.choose.1) I (stepCols N j e.choose.2) := hm m
        rw [hs, hn, inv_mul_cancel_left₀ hα]
      · obtain ⟨c, hc, hcz⟩ := ho
        have hk : ∀ p, M.blk p ≠ some k := fun p hp => e ⟨p, hp⟩
        refine ⟨c ⟨k, hk⟩, hc _, fun m => ?_⟩
        show flagZ M F zb₂ H ⟨k, m⟩ = _
        refine (dif_neg e).trans ?_
        rw [hcz]
        rfl
  choose c hc hcz using block
  exact ⟨c, hc, funext fun p => hcz p.1 p.2⟩

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedFrameValueFormulaStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_frame_value_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (zb₂ : (Σ k, baseIdx ι M.blk k) → ℂ) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) (H U : Ψ → Matrix (Fin N) (Fin N) ℂ) (V : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.blk (τ, a) = some k₀ → baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) → SameOrbit zb₂ (baseOf M k₀ z) → (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) → IsBlockDiag j V → V.BlockTriangular id → (∀ c ∈ stepCols N j a, V c c ≠ 0) → (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (H p.1 * U p.1) I (stepCols N j p.2)) → (∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (H τ * (1 + Matrix.single cb ca t) * V) I (stepCols N j a)) → SameOrbit (sqZ M F zb₂ H k₀ τ ca cb t) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.sameOrbit_sqZ_of_flags | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.sameOrbit_sqZ_of_flags | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.sameOrbit_sqZ_of_flags <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartTenth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartTenth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto

section Scale

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

def normScale (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) : Option K → ℂ
  | some k => if h : ∀ p, M.blk p ≠ some k then c ⟨k, h⟩ else 1
  | none => 1

theorem normScale_ne (M : FlagModel y Ψ N j) {c : NonPluckerBlocks M.blk → ℂ} (hc : ∀ k, c k ≠ 0) (o : Option K) :
    normScale M c o ≠ 0 := by
  cases o with
  | none => exact one_ne_zero
  | some k =>
    by_cases h : ∀ p, M.blk p ≠ some k
    · show dite _ _ _ ≠ 0
      rw [dite_eq_left h]
      exact hc ⟨k, h⟩
    · show dite _ _ _ ≠ 0
      rw [dite_eq_right h]
      exact one_ne_zero

theorem normScale_base (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) (k : NonPluckerBlocks M.blk) :
    normScale M c (some k.1) = c k := by
  simp [normScale, k.2]

theorem normScale_step (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) : normScale M c (some k) = 1 := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
  show dite _ _ _ = 1
  rw [dite_eq_right h]

end Scale

theorem norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) ∧ SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) ∧ ∃ (h' : Ψ → Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h' p.1) I (stepCols N j p.2)) ∧ ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (h' τ * (1 + Matrix.single cb ca t')) I (stepCols N j a) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hctx z hzO
  obtain ⟨hb, hba, hk₀, hca, hcb, hAV, hF, hBC, hr, -, -⟩ := hctx
  obtain ⟨hz, hsrc, hV₀, -, -⟩ := hzO
  have z₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y) :=
    CPts.comp_mem_mcPts (Pts.isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz
  have hbm : baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) := CPts.base_mem M z₀
  obtain ⟨hblm, hbl1, hblG, horb⟩ := hBC.2.2.2.2 _ hV₀
  rw [(Rb.A.chart kb).left_inv hsrc] at horb
  have horbit : SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) :=
    orbit_trans (orbit_symm horb) (hr _ hbm)
  have hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) := by
    rwa [← CovMap.mCoordIdeal_eq_of_sameOrbit horbit]
  refine ⟨hbm, hG, horbit, ?_⟩
  obtain ⟨c, hc, hce⟩ := id horbit
  let z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun q => normScale M c q.1 * z q
  have hz' : z' ∈ mcPts (wP M τ a k₀ ca cb) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal _) _ (normScale_ne M hc) hz
  have hbase : basePart M.blk (fstPt k₀ z') = bl (Rb.A.chart kb (r (baseOf M k₀ z))) := by
    rw [hce]
    funext q
    show normScale M c (some q.1.1) * z _ = c q.1 * z _
    rw [normScale_base]
  have hval : ∀ s : M.Ω, valAt M.x s (basePart M.blk (fstPt k₀ z')) = valAt M.x s (baseOf M k₀ z) := fun s => by
    rw [hbase]
    exact CovMap.LocImg.valAt_orbit horbit hbm s
  obtain ⟨h', t', H, H'⟩ := (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk₀ hca hcb hAV F z' hF
    (by rw [hbase]; exact hblm) (by rw [hbase]; exact hblG) (by rw [hbase]; exact hbl1)).1 hz'
  refine ⟨h', t', H.2.1, fun p k hp => ?_, ?_⟩
  · obtain ⟨α, hα, e⟩ := H.2.2 p k hp
    refine ⟨α, hα, fun m => ?_⟩
    have e' := e m
    simp only [hval] at e'
    rw [← e']
    show z _ = normScale M c (some k) * z _
    rw [normScale_step M c hp, one_mul]
  · obtain ⟨α, hα, e⟩ := H'.2.2 (τ, a) k₀ hk₀
    refine ⟨α, hα, fun m => ?_⟩
    have e' := e m
    rw [Pts.basePart_snd M hk₀] at e'
    simp only [hval, Function.update_self] at e'
    rw [← e', Pts.snd_self, Pts.snd_self]
    show z _ = 1 * z _
    rw [one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartTenthStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_tenth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) ∧ SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) ∧ ∃ (h' : Ψ → Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h' p.1) I (stepCols N j p.2)) ∧ ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (h' τ * (1 + Matrix.single cb ca t')) I (stepCols N j a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.norm | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.norm | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.norm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LUTwistRefactorization
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LUTwistRefactorization
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv

theorem lastCol_mem {N j : ℕ} {a ca : Fin N} (hj : j ≤ N) (hca : (ca : ℕ) = lastCol N j a) :
    ca ∈ stepCols N j a ∧ ∀ r ∈ stepCols N j a, r ≤ ca := by
  unfold lastCol at hca
  refine ⟨?_, ?_⟩
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  · intro r hr
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [Fin.le_iff_val_le_val]
    split_ifs at hca hr <;> omega

theorem transv_mul_transv {N : ℕ} {ca cb : Fin N} (hne : ca ≠ cb) (s : ℂ) :
    (1 + Matrix.single cb ca s) * (1 + Matrix.single cb ca (-s)) = (1 : Matrix (Fin N) (Fin N) ℂ) := by
  rw [add_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_of_ne s cb ca cb hne (-s), add_zero,
    add_assoc, ← Matrix.single_add, neg_add_cancel, Matrix.single_zero, add_zero]

theorem main : ∀ (N j : ℕ) (a ca cb : Fin N) (L U : Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), j ≤ N → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → minorIJ (L * U * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 → ∃ (t : ℂ) (V : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c ∈ stepCols N j a, V c c ≠ 0) ∧ U * (1 + Matrix.single cb ca t') = (1 + Matrix.single cb ca t) * V := by
  intro N j a ca cb L U t' hj hca hcb hblk hL hLu hU hUt hUd hmin
  have hne : ca ≠ cb := by
    intro h
    have h1 := congrArg Fin.val h
    omega
  obtain ⟨hcaS, hmax⟩ := lastCol_mem hj hca
  have hLM : L * U * (1 + Matrix.single cb ca t') = L * (U * (1 + Matrix.single cb ca t')) :=
    Matrix.mul_assoc _ _ _
  set M := U * (1 + Matrix.single cb ca t') with hMdef
  have hMe : ∀ x y, M x y = U x y + if y = ca then U x cb * t' else 0 := by
    intro x y
    rw [hMdef, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    split_ifs with hy
    · rw [hy, Matrix.mul_single_apply_same]
    · rw [Matrix.mul_single_apply_of_ne t' cb ca x y hy U]
  have hUz : ∀ x y : Fin N, y < x → U x y = 0 := fun x y h => hUt (show id y < id x from h)
  have hMut : ∀ x y : Fin N, y < x → x ≠ cb → M x y = 0 := by
    intro x y hxy hx
    rw [hMe, hUz x y hxy]
    split_ifs with hy
    · rw [hy] at hxy
      have h1 : cb < x := by
        rw [Fin.lt_iff_val_lt_val] at hxy ⊢
        have h2 : (x : ℕ) ≠ cb := fun h => hx (Fin.ext h)
        omega
      rw [hUz x cb h1]
      simp
    · simp
  have hMca : M ca ca ≠ 0 := by
    intro h0
    apply hmin
    rw [hLM]
    unfold minorIJ
    rw [dite_eq_left rfl]
    set f := (stepCols N j a).orderEmbOfFin (rfl : (stepCols N j a).card = (stepCols N j a).card) with hf
    have hfmem : ∀ r, f r ∈ stepCols N j a := fun r => Finset.orderEmbOfFin_mem _ _ r
    have hSmap : Finset.univ.map f.toEmbedding = stepCols N j a := Finset.map_orderEmbOfFin_univ _ _
    have hrange : Set.range f = ↑(stepCols N j a) := Finset.range_orderEmbOfFin _ _
    have hprod : (L * M).submatrix f f = L.submatrix f f * M.submatrix f f := by
      ext p q
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      have hfpS := hfmem p
      have hz : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ stepCols N j a → L (f p) i * M i (f q) = 0 := by
        intro i _ hi
        by_cases hic : (ca : ℕ) < i
        · have hfp := hmax (f p) hfpS
          have hlt : f p < i := by
            rw [Fin.le_iff_val_le_val] at hfp
            rw [Fin.lt_iff_val_lt_val]
            omega
          rw [hLu.2 (f p) i hlt, zero_mul]
        · have hLz : L (f p) i = 0 := by
            apply hL
            intro hiff
            simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hi hfpS
            unfold lastCol at hca
            split_ifs at hi hfpS hca
            · have h3 := hiff.mpr (by omega)
              omega
            · omega
          rw [hLz, zero_mul]
      have hm := Finset.sum_map Finset.univ f.toEmbedding (fun x => L (f p) x * M x (f q))
      rw [hSmap] at hm
      rw [← Finset.sum_subset (Finset.subset_univ (stepCols N j a)) hz]
      exact hm
    have hUT : (M.submatrix f f).IsUpperTriangular := by
      intro p q hpq
      rw [Matrix.submatrix_apply]
      have hfpcb : f p ≠ cb := by
        intro hfp
        have h4 := hmax (f p) (hfmem p)
        rw [hfp, Fin.le_iff_val_le_val] at h4
        omega
      exact hMut (f p) (f q) (f.strictMono hpq) hfpcb
    have hdetM : (M.submatrix f f).det = 0 := by
      rw [Matrix.det_of_upperTriangular hUT]
      obtain ⟨p0, hp0⟩ : ∃ p0, f p0 = ca := by
        have h1 : ca ∈ Set.range f := by
          rw [hrange]
          exact hcaS
        exact h1
      exact Finset.prod_eq_zero (Finset.mem_univ p0) (by rw [Matrix.submatrix_apply, hp0]; exact h0)
    rw [hprod, Matrix.det_mul, hdetM, mul_zero]
  have hMb : ∀ x y : Fin N, ¬((x : ℕ) < N - j ↔ (y : ℕ) < N - j) → M x y = 0 := by
    intro x y hxy
    rw [hMe, hU x y hxy]
    split_ifs with hy
    · rw [hy] at hxy
      rw [hU x cb (fun h => hxy (h.trans hblk.symm))]
      simp
    · simp
  set t := M cb ca / M ca ca with ht
  have hVe : ∀ x y, ((1 + Matrix.single cb ca (-t)) * M) x y = M x y + if x = cb then -t * M ca y else 0 := by
    intro x y
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    split_ifs with hx
    · rw [hx, Matrix.single_mul_apply_same]
    · rw [Matrix.single_mul_apply_of_ne (-t) cb ca x y hx M]
  refine ⟨t, (1 + Matrix.single cb ca (-t)) * M, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [hVe, hMb x y hxy]
    split_ifs with hx
    · rw [hx] at hxy
      rw [hMb ca y (fun h => hxy (hblk.symm.trans h))]
      simp
    · simp
  · intro x y hxy
    change y < x at hxy
    rw [hVe]
    by_cases hx : x = cb
    · rw [if_pos hx, hx]
      rw [hx] at hxy
      by_cases hy : y = ca
      · rw [hy, ht, neg_mul, div_mul_cancel₀ _ hMca, add_neg_cancel]
      · have hylt : y < ca := by
          rw [Fin.lt_iff_val_lt_val] at hxy ⊢
          have h2 : (y : ℕ) ≠ ca := fun h => hy (Fin.ext h)
          omega
        rw [hMe cb y, if_neg hy, hUz cb y hxy, hMe ca y, if_neg hy, hUz ca y hylt]
        simp
    · rw [if_neg hx, add_zero]
      exact hMut x y hxy hx
  · intro c hc
    rw [hVe]
    have hcle := hmax c hc
    have hccb : c ≠ cb := by
      intro h
      rw [h, Fin.le_iff_val_le_val] at hcle
      omega
    rw [if_neg hccb, add_zero]
    by_cases hcc : c = ca
    · rw [hcc]
      exact hMca
    · rw [hMe, if_neg hcc, add_zero]
      exact hUd c
  · rw [← Matrix.mul_assoc, transv_mul_transv hne t, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LUTwistRefactorizationStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.LU_twist_refactorization : ∀ (N j : ℕ) (a ca cb : Fin N) (L U : Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), j ≤ N → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → minorIJ (L * U * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 → ∃ (t : ℂ) (V : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c ∈ stepCols N j a, V c c ≠ 0) ∧ U * (1 + Matrix.single cb ca t') = (1 + Matrix.single cb ca t) * V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFifth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, wRho M Rb τ k₀ ca cb F kb r h ε z ∈ wD ε V ∧ SameOrbit (wPhi M F bl h ε k₀ τ ca cb (wRho M Rb τ k₀ ca cb F kb r h ε z)) z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hctx z hz
  have hctx' := hctx
  obtain ⟨hb, hab, hk, hca, hcb, hy, hF, hBC, hr, hrc, hh⟩ := hctx'
  obtain ⟨hmem, hsrc, hV, hden, hden2⟩ := hz
  obtain ⟨hzb, hG, horb, h', t', hh', Hf, Hs⟩ := GlobalTheory.T.flag_adjacent_chart_tenth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hctx z
    ⟨hmem, hsrc, hV, hden, hden2⟩
  have hS := Pts.same_summand hb hab hca hcb
  have hj := M.j_le
  set zb := baseOf M k₀ z with hzbdef
  set w := wRho M Rb τ k₀ ca cb F kb r h ε z with hw
  have hwB : wB ε w = Rb.A.chart kb (r zb) := by
    funext i
    simp [wB, hw, wRho, zb]
  have hwL : ∀ q, wL ε w q = lowRead M F zb h (fstPt k₀ z) q.1.1 q.1.2.1 q.1.2.2 := fun q => by
    simp [wL, hw, wRho, zb]
  have hwT : wT ε w = lowRead M F zb h (sndPt k₀ z) τ cb ca - lowRead M F zb h (fstPt k₀ z) τ cb ca := by
    simp [wT, hw, wRho, zb]
  refine ⟨show wB ε w ∈ V by rw [hwB]; exact hV, ?_⟩
  have hdu : ∀ τ', IsUnit (h τ').det := fun τ' => (hh τ').2.isUnit
  let G : Ψ → Matrix (Fin N) (Fin N) ℂ := fun τ' => (h τ')⁻¹ * h' τ'
  have hGb : ∀ τ', IsBlockDiag j (G τ') := fun τ' => ((hh τ').1.inv (hdu τ')).mul (hh' τ').1
  have hinvd : ∀ τ', ((h τ')⁻¹).det ≠ 0 := fun τ' h0 => by
    have h1 := Matrix.det_nonsing_inv_mul_det (h τ') (hdu τ')
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hGd : ∀ τ', (G τ').det ≠ 0 := fun τ' => by
    show ((h τ')⁻¹ * h' τ').det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hinvd τ') (hh' τ').2
  have hmin : ∀ τ' i, IsProperStep N j i → minorIJ (G τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
    intro τ' i hi h0
    obtain ⟨k, hp⟩ : ∃ k, M.blk (τ', i) = some k := Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    obtain ⟨α, hα, hz₁⟩ := Hf (τ', i) k hp
    refine hden (τ', i) k hp ?_
    rw [GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M F zb (τ', i) k (h' τ') (h τ')⁻¹ (fstPt k₀ z) α _ hF hzb hG hp (hh' τ').1 hz₁]
    show α * minorIJ (G τ') _ _ = 0
    rw [h0, mul_zero]
  choose L U hLb hLu hUb hUt hUd hLU using fun τ' => GlobalTheory.T.block_LU_factorization N j (G τ') hj (hGb τ') (hGd τ') (hmin τ')
  have hhL : ∀ τ', h τ' * (L τ' * U τ') = h' τ' := fun τ' => by
    rw [← hLU]
    exact Matrix.mul_nonsing_inv_cancel_left _ _ (hdu τ')
  have hlow : ∀ τ' (a' b' : Fin N), b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) →
      lowRead M F zb h (fstPt k₀ z) τ' a' b' = L τ' a' b' := fun τ' a' b' e e' =>
    GlobalTheory.T.frame_LU_minor_value K ι Φ y Ψ N j M F zb h τ' a' b' (fstPt k₀ z) (h' τ') (L τ') (U τ') hF hzb hG (hh' τ').1 (hLU τ')
      (hLb τ') (hLu τ') (hUb τ') (hUt τ') (fun c _ => hUd τ' c) e e' (fun k hp => Hf (τ', stepOf N j b') k hp)
  have hlm : ∀ τ', lowMat (wL ε w) τ' = L τ' := fun τ' => by
    ext a' b'
    unfold lowMat
    split_ifs with e e'
    · rw [hwL]
      exact hlow τ' a' b' e.1 e.2
    · rw [e', (hLu τ').1]
    · rcases lt_or_gt_of_ne e' with e' | e'
      · exact ((hLu τ').2 _ _ e').symm
      · exact ((hLb τ') _ _ fun e'' => e ⟨e', e''⟩).symm
  obtain ⟨α₂, hα₂, hz₂⟩ := Hs
  have hne2 : minorIJ (L τ * U τ * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 := by
    intro h0
    refine hden2 ?_
    rw [GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M F zb (τ, a) k₀ (h' τ * (1 + Matrix.single cb ca t')) (h τ)⁻¹ (sndPt k₀ z) α₂ _ hF hzb hG hk
      ((hh' τ).1.mul (Pts.transv_block hS t')) hz₂, ← Matrix.mul_assoc]
    show α₂ * minorIJ (G τ * _) _ _ = 0
    rw [hLU, h0, mul_zero]
  obtain ⟨t, Vm, hVb, hVt, hVd, hUV⟩ := GlobalTheory.T.LU_twist_refactorization N j a ca cb (L τ) (U τ) t' hj hca hcb hS (hLb τ) (hLu τ) (hUb τ) (hUt τ)
    (hUd τ) hne2
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hstep : stepOf N j ca = a := by
    have := a.2
    apply Fin.ext
    simp only [stepOf, hca, lastCol]
    split_ifs <;> omega
  have hcc : ∀ c, c ∈ stepCols N j (stepOf N j ca) → Vm c c ≠ 0 := fun c hc => hVd c (hstep ▸ hc)
  have hLe : ∀ r c, (L τ * (1 + Matrix.single cb ca t)) r c = L τ r c + if c = ca then L τ r cb * t else 0 := by
    intro r c
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    congr 1
    by_cases e : c = ca
    · subst e
      simp [Matrix.mul_single_apply_same]
    · rw [if_neg e, Matrix.mul_single_apply_of_ne _ _ _ _ _ e]
  have hL2 : IsLowerUni (L τ * (1 + Matrix.single cb ca t)) := by
    refine ⟨fun r => ?_, fun r c e => ?_⟩
    · rw [hLe, (hLu τ).1]
      split_ifs with e
      · rw [e, (hLu τ).2 _ _ hlt, zero_mul, add_zero]
      · rw [add_zero]
    · rw [hLe, (hLu τ).2 _ _ e]
      split_ifs with e'
      · rw [(hLu τ).2 r cb (e.trans (e' ▸ hlt)), zero_mul, add_zero]
      · rw [add_zero]
  have hL2c : (L τ * (1 + Matrix.single cb ca t)) cb ca = L τ cb ca + t := by
    rw [hLe, if_pos rfl, (hLu τ).1, one_mul]
  have hsnd : lowRead M F zb h (sndPt k₀ z) τ cb ca = L τ cb ca + t := by
    rw [← hL2c]
    refine GlobalTheory.T.frame_LU_minor_value K ι Φ y Ψ N j M F zb h τ cb ca (sndPt k₀ z) (h' τ * (1 + Matrix.single cb ca t')) _ Vm hF hzb hG
      ((hh' τ).1.mul (Pts.transv_block hS t')) ?_ ((hLb τ).mul (Pts.transv_block hS t)) hL2 hVb hVt hcc hlt hS.symm ?_
    · rw [← Matrix.mul_assoc]
      show G τ * _ = _
      rw [hLU, Matrix.mul_assoc, hUV, Matrix.mul_assoc]
    · intro k hp
      rw [hstep, hk] at hp
      obtain rfl := Option.some.inj hp
      exact ⟨α₂, hα₂, by rw [hstep]; exact hz₂⟩
  have hwt : wT ε w = t := by
    rw [hwT, hsnd, hlow τ cb ca hlt hS.symm]
    ring
  have hHU : ∀ τ', (fun τ' => wH h ε τ' w) τ' * U τ' = h' τ' := fun τ' => by
    show h τ' * lowMat (wL ε w) τ' * U τ' = _
    rw [hlm, Matrix.mul_assoc, hhL]
  show SameOrbit (sqZ M F (bl (wB ε w)) (fun τ' => wH h ε τ' w) k₀ τ ca cb (wT ε w)) z
  rw [hwB, hwt]
  refine GlobalTheory.T.twisted_frame_value_formula K ι Φ y Ψ N j M τ a k₀ ca cb F _ z _ U Vm t hk hzb hG horb
    (fun τ' => ⟨hUb τ', hUt τ', hUd τ'⟩) hVb hVt hVd (fun p k hp => ?_) ⟨α₂, hα₂, fun m => ?_⟩
  · rw [hHU]
    exact Hf p k hp
  · have e : (fun τ' => wH h ε τ' w) τ * (1 + Matrix.single cb ca t) * Vm = h' τ * (1 + Matrix.single cb ca t') := by
      rw [← hHU τ, Matrix.mul_assoc, Matrix.mul_assoc, hUV]
    rw [e]
    exact hz₂ m

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFifthStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_fifth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, wRho M Rb τ k₀ ca cb F kb r h ε z ∈ wD ε V ∧ SameOrbit (wPhi M F bl h ε k₀ τ ca cb (wRho M Rb τ k₀ ca cb F kb r h ε z)) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsResolution
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
open GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem sameOrbit_baseOf {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (baseOf M k₀ z) (baseOf M k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k.1), fun k => hc _, rfl⟩

theorem sameOrbit_fstPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem sameOrbit_sndPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hc _, hc _]
  · funext p
    obtain ⟨k, m⟩ := p
    by_cases e : k = k₀
    · subst e
      simp only [sndPt, Function.comp, v₁_self, if_true]
    · simp only [sndPt, Function.comp, v₁_ne (show (⟨k, m⟩ : Σ k, ι k).1 ≠ k₀ from e), if_neg e]

theorem not_mem_mcPts_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

theorem fibreSquare_atlas : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∃ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb hb hab hk hca hcb hy hd
  have hA := (GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).1
  obtain ⟨ε⟩ := GlobalTheory.T.flag_dimension_index_equiv Ψ N j n d M.j_le hd
  have hcov := GlobalTheory.T.flag_adjacent_arithmetic_height K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb hb hab hk hca hcb hy
  have mk : ∀ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h →
      ∃ C : OrbitChart (wP M τ a k₀ ca cb) (d + 2), C.D = wD ε V ∧ C.φ = wPhi M F bl h ε k₀ τ ca cb ∧
        C.O = wO M Rb τ a k₀ ca cb F kb V r h := by
    intro F kb V bl r h hc
    have hV : IsOpen V := hc.2.2.2.2.2.2.2.1.1
    have hh := GlobalTheory.T.flag_adjacent_chart_first K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hm := GlobalTheory.T.wPhi_mem_mcPts_wP K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hr := GlobalTheory.T.flag_adjacent_chart_fourth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have ho := GlobalTheory.T.flag_adjacent_chart_fifth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hO := GlobalTheory.T.flag_adjacent_chart_sixth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hc
    have hb' := GlobalTheory.T.flag_adjacent_chart_seventh K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have ht := GlobalTheory.T.flag_adjacent_chart_eighth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hi := GlobalTheory.T.flag_adjacent_chart_ninth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    exact ⟨{ D := wD ε V
             isOpen_D := hV.preimage (continuous_pi fun i => continuous_apply _)
             φ := wPhi M F bl h ε k₀ τ ca cb
             holo := hh
             mem := hm
             O := wO M Rb τ a k₀ ca cb F kb V r h
             O_open := hO
             O_orbit := fun z hz z' hz' e => (hb' z hz z' hz' e).1
             ρ := wRho M Rb τ k₀ ca cb F kb r h ε
             ρ_cont := ht
             ρ_orbit := fun z hz z' hz' e => (hb' z hz z' hz'.1 e).2
             φ_mem_O := fun w hw => (hr w hw).1
             ρ_φ := fun w hw => (hr w hw).2
             ρ_mem := fun z hz => (ho z hz).1
             φ_ρ := fun z hz => (ho z hz).2
             immersion := hi }, rfl, rfl, rfl⟩
  obtain ⟨R, hR⟩ := GlobalTheory.T.log_resolution_from_orbit_charts (Option K) (fun o => ι (o.getD k₀)) (wP M τ a k₀ ca cb) (d + 2) hA.1 hA.2.1.2.1
    (fun h => hA.2.1.1.ne_top (top_le_iff.mp h)) (fun z hz => by
      obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov z hz
      obtain ⟨C, -, -, hO⟩ := mk F kb V bl r h hc
      exact ⟨C, hO ▸ hzO⟩)

  have key : ∀ x : R.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin (d + 2) → ℂ)),
      IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h ∧ IsCompatChart R.A ψ ∧ ψ.target = wD ε V ∧ x ∈ ψ.source ∧
        ∀ x' ∈ ψ.source, SameOrbit (wPhi M F bl h ε k₀ τ ca cb (ψ x')) (R.lift x' x') := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov _ (R.mem x x (R.mem_U x))
    obtain ⟨C, hD, hφ, hO⟩ := mk F kb V bl r h hc
    obtain ⟨ψ, h1, h2, h3, h4⟩ := hR C ⟨_, R.mem x x (R.mem_U x)⟩
    exact ⟨F, kb, V, bl, r, h, ψ, hc, h1, h2.trans hD, (h3 x).2 (hO ▸ hzO), fun x' hx' => hφ ▸ h4 x' hx'⟩

  have hbase : ∀ x : R.X, ∃ x' : Rb.X, SameOrbit (Rb.lift x' x') (baseOf M k₀ (R.lift x x)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB := hc.2.2.2.2.2.2.2.1
    have hw : ψ x ∈ wD ε V := hT ▸ ψ.map_source hx
    have hE := (GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).2 _ hw
    refine ⟨(Rb.A.chart kb).symm (wB ε (ψ x)), orbit_trans (hB.2.2.2.2 _ hw).2.2.2 ?_⟩
    have := sameOrbit_baseOf M (hs x hx)
    rwa [hE.2.1] at this
  choose pr hpr using hbase
  have hcoord : ∀ (x : R.X) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin (d + 2) → ℂ)),
      IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ψ.target = wD ε V → x ∈ ψ.source →
      SameOrbit (wPhi M F bl h ε k₀ τ ca cb (ψ x)) (R.lift x x) →
      pr x ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x) i = ψ x (ε (Sum.inl i)) := by
    intro x F kb V bl r h ψ hc hT hx hs
    have hB := hc.2.2.2.2.2.2.2.1
    have hw : ψ x ∈ wD ε V := hT ▸ ψ.map_source hx
    have hE := (GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).2 _ hw
    have h1 : SameOrbit (bl (wB ε (ψ x))) (baseOf M k₀ (R.lift x x)) := by
      have := sameOrbit_baseOf M hs
      rwa [hE.2.1] at this
    have h2 := orbit_trans (hB.2.2.2.2 _ hw).2.2.2 (orbit_trans h1 (orbit_symm (hpr x)))
    have h3 : (Rb.A.chart kb).symm (wB ε (ψ x)) = pr x := Rb.inj _ _ (not_mem_mcPts_top _) h2
    have hwt : wB ε (ψ x) ∈ (Rb.A.chart kb).target := hB.2.1 hw
    rw [← h3]
    exact ⟨(Rb.A.chart kb).map_target hwt, fun i => by
      rw [(Rb.A.chart kb).right_inv hwt]
      rfl⟩
  refine ⟨R, pr, ?_, hpr, fun x => ?_⟩
  · refine GlobalTheory.T.holoMap_of_local_product_charts (d + 2) n R.X Rb.X R.A Rb.A pr fun x => ?_
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, hC, hT, hx, hs⟩ := key x
    exact ⟨ψ, kb, fun i => ε (Sum.inl i), hC, hx, fun x' hx' => hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx')⟩
  · obtain ⟨F, kb, V, bl, r, h, ψ, hc, hC, hT, hx, hs⟩ := key x
    have hE := GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hB := hc.2.2.2.2.2.2.2.1
    refine ⟨ψ, kb, ⟨fun i => ε (Sum.inl i), fun i i' e => Sum.inl_injective (ε.injective e)⟩, ε (Sum.inr (Sum.inr ())), F,
      fun τ' => wH h ε τ', hx, hC, hc.2.2.2.2.2.2.1, fun i e => Sum.inl_ne_inr (ε.injective e), fun x' hx' =>
        hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx'), fun τ' r' s' => hT ▸ hE.1 τ' r' s', fun x' hx' => ?_⟩
    have hw : ψ x' ∈ wD ε V := hT ▸ ψ.map_source hx'
    obtain ⟨e1, e2, e3⟩ := hE.2 _ hw
    have h1 := sameOrbit_baseOf M (hs x' hx')
    rw [e2] at h1
    refine ⟨e1, ?_, fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb (ψ x')), sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb (ψ x')),
      sameOrbit_fstPt (hs x' hx'), sameOrbit_sndPt (hs x' hx'), e3⟩
    have h2 : mCoordIdeal (bl (wB ε (ψ x'))) = mCoordIdeal (basePart M.blk (fstPt k₀ (R.lift x' x'))) :=
      GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit h1
    exact h2 ▸ (hB.2.2.2.2 _ hw).2.2.1

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsResolutionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_rows_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∃ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.fibreSquare_atlas | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.fibreSquare_atlas | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.fibreSquare_atlas <;> assumption)
end
