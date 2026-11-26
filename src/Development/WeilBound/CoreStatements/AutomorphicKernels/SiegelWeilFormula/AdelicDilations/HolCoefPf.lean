module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CharacterW1TraceExp

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.WeightFactorDilation
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem stab_diag {n : ℕ} (i₀ : Fin n) (dv : Fin n → ℂ) (hdv : ∀ k, k ≠ i₀ → dv k = 1)
    (β : Matrix (Fin n) (Fin n) ℂ) (hr : ∀ l, β i₀ l = 0) (hc : ∀ k, β k i₀ = 0) :
    (Matrix.diagonal dv)ᴴ * β * Matrix.diagonal dv = β := by
  ext k l
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hk : k = i₀
  · subst hk; rw [hr]; simp
  · by_cases hl : l = i₀
    · subst hl; rw [hc]; simp
    · rw [Pi.star_apply, hdv k hk, hdv l hl]; simp

theorem stab_row {n : ℕ} (i₀ : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k l, k ≠ i₀ → M k l = 0)
    (β : Matrix (Fin n) (Fin n) ℂ) (hr : ∀ l, β i₀ l = 0) (hc : ∀ k, β k i₀ = 0) :
    (1 + M)ᴴ * β * (1 + M) = β := by
  have h1 : β * M = 0 := by
    ext k l
    rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
    · rw [hc]; simp
    · intro p _ hp; rw [hM p l hp, mul_zero]
    · simp
  have h2 : Mᴴ * β = 0 := by
    ext k l
    rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
    · rw [hr]; simp
    · intro p _ hp; rw [Matrix.conjTranspose_apply, hM p k hp, star_zero, zero_mul]
    · simp
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.one_mul, Matrix.mul_one, h1, h2, Matrix.zero_mul, add_zero]

theorem det_row {n : ℕ} (i₀ : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k l, k ≠ i₀ → M k l = 0)
    (h0 : M i₀ i₀ = 0) : (1 + M).det = 1 := by
  have e : M = Matrix.replicateCol Unit (Pi.single i₀ (1 : ℂ)) * Matrix.replicateRow Unit (M i₀) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton]
    by_cases hk : k = i₀
    · subst hk; simp
    · rw [hM k l hk, Pi.single_eq_of_ne hk, zero_mul]
  rw [e, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_single, h0, zero_mul, add_zero]

theorem blocks_of_inG {n : ℕ} (a a' : Matrix (Fin n) (Fin n) ℂ) (h : InG (Matrix.fromBlocks a 0 0 a')) : aᴴ * a' = 1 := by
  unfold InG JJ at h
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
  simp at h
  exact h.1

theorem weight_factor_blocks {n : ℕ} (pp qq : ℕ) (e : ℤ) (y : GR n) (a a' : Matrix (Fin n) (Fin n) ℂ)
    (hy : mR y = Matrix.fromBlocks a 0 0 a') :
    F0 pp qq e y = (a.det * a'.det) ^ e * (a'.det ^ (-(pp : ℤ)) * a'.det ^ (-(qq : ℤ))) := by
  unfold F0 f0 u1 u2
  rw [hy, Matrix.det_fromBlocks_zero₂₁, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  simp

theorem weight_factor_det_one {n : ℕ} (pp qq : ℕ) (e : ℤ) (y : GR n) (a a' : Matrix (Fin n) (Fin n) ℂ)
    (hy : mR y = Matrix.fromBlocks a 0 0 a') (ha : a.det = 1) : F0 pp qq e y = 1 := by
  have hG : InG (Matrix.fromBlocks a 0 0 a') := hy ▸ y.2
  have h1 := congrArg Matrix.det (blocks_of_inG a a' hG)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, ha, star_one, one_mul, Matrix.det_one] at h1
  rw [weight_factor_blocks pp qq e y a a' hy, ha, h1]
  simp

theorem weight_factor_dilation {n : ℕ} (i₀ : Fin n) (τ : ℝ) (y : GR n) (hy : IsDil (Pi.single i₀ 1) τ y) (pp qq : ℕ) (e : ℤ) :
    F0 pp qq e y = Complex.exp (τ * ((pp + qq : ℕ) : ℂ)) := by
  have hd1 : (Matrix.diagonal fun j => ((Real.exp (τ * (Pi.single i₀ (1 : ℝ) : Fin n → ℝ) j) : ℝ) : ℂ)).det = Complex.exp τ := by
    rw [Matrix.det_diagonal, Finset.prod_eq_single i₀]
    · simp [Complex.ofReal_exp]
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  have hd2 : (Matrix.diagonal fun j => ((Real.exp (-(τ * (Pi.single i₀ (1 : ℝ) : Fin n → ℝ) j)) : ℝ) : ℂ)).det = Complex.exp (-τ) := by
    rw [Matrix.det_diagonal, Finset.prod_eq_single i₀]
    · simp [Complex.ofReal_exp]
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  rw [weight_factor_blocks pp qq e y _ _ hy, hd1, hd2, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_zpow, one_mul]
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end PositivityTheory.SiegelWeilFormula.AStep

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem holPhi (H : Hyps) {d : SD σ} (R : RD d) (w : InfinitePlace F) {nb lam 𝓖}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (A : d.G → ℂ) (hAc : Continuous A)
    (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g) (pp qq : ℕ) (e : ℤ)
    (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) (x' : d.G) :
    IsHolW pp qq e fun y => fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) := by
  have hc' := hc
  obtain ⟨hN, -, -, h1⟩ := hc'
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ d.ok.frame
  obtain ⟨-, -, hTG, -, -, -⟩ := H.auxEx F E σ d
  have := hTG
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std
  have hnbc := kfour.nb_continuous hσ d.ok.frame hN
  let u : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have huc : Continuous u := kfour.continuous_chr hψ.1 T.1.1
  let γf : nA σ d.Y d.b → nA σ d.Y d.b := fun β => Classical.choose (hKc β)
  have hγ : ∀ β, γf β ∈ nF σ d.Y d.b ∧ γf β + β ∈ K := fun β => Classical.choose_spec (hKc β)
  let c : nA σ d.Y d.b → d.G := fun β => nb (γf β + β) * x'
  have key : ∀ β (g : d.G), A (c β * g) = A (nb β * (x' * g)) := by
    intro β g
    show A (nb (γf β + β) * x' * g) = _
    rw [KSing.nb_add d hN, mul_assoc, mul_assoc, hAi _ (KSing.nb_rat d hN (hγ β).1)]
  have : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hC : IsCompact ((fun k => nb k * x') '' K) := hK.image (hnbc.mul continuous_const)
  have hmeas : ∀ y, AEStronglyMeasurable (fun β => A (c β * R.ι w y) * u β) (lam.restrict 𝓖) := by
    intro y
    have e : (fun β => A (c β * R.ι w y) * u β) = fun β => A (nb β * (x' * R.ι w y)) * u β :=
      funext fun β => by rw [key]
    rw [e]
    exact ((hAc.comp (hnbc.mul continuous_const)).mul huc).aestronglyMeasurable
  have := H.holT.2 d.n pp qq e d.G (R.ι w) (R.cont w) A hAc hA (nA σ d.Y d.b) (lam.restrict 𝓖) c u _ hC
    (fun β => ⟨_, (hγ β).2, rfl⟩) (fun β => (hψ.2.1 _).le) hmeas
  convert this using 2 with y
  simp only [fc]
  congr 1
  funext β
  rw [key]

theorem holCoef_pf (H : Hyps) {d : SD σ} (R : RD d) (L : LD d) (w : InfinitePlace F) {nb lam 𝓖}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b}
    {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (A : d.G → ℂ) (hAc : Continuous A) (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g)
    (pp qq : ℕ) (e : ℤ) (hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) :
    (∀ τ (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w y * x) = Complex.exp (τ * d.m) * fc d.B.ψ d.b nb lam 𝓖 A T x) ∧
    ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ u x, fc d.B.ψ d.b nb lam 𝓖 A T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 A T x := by
  have hc' := hc
  obtain ⟨hN, -, -, -⟩ := hc'
  have hr : ∀ l, betaW d R w T L.i₀ l = 0 := fun l => by
    simp [betaW, SD.cw, Matrix.map_apply, (hT.1 l).1]
  have hcol : ∀ k, betaW d R w T k L.i₀ = 0 := fun k => by
    simp [betaW, SD.cw, Matrix.map_apply, (hT.1 k).2]
  have hchar : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (h : Matrix (Fin d.n) (Fin d.n) ℂ) (xN y : GR d.n),
      h.IsHermitian → mR xN = nU h → fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xN * y)) =
        Complex.exp (Complex.I * (betaW d R w T * h).trace) * fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) := by
    intro x' hx' h xN y hh hxN
    obtain ⟨β₁, hι, hBw, hBu, hBf⟩ := nbw1 d R w hN xN h hxN
    rw [map_mul, ← mul_assoc, hx' xN, hι, mul_assoc, KSing.fc_shift d hc A hAi T β₁,
      character_w1_trace_exp d R w T β₁ h hh hBw hBu hBf]
  have hright : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ)
      (xx y : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' → aᴴ * betaW d R w T * a = betaW d R w T →
      fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xx * y)) = F0 pp qq e xx * fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) :=
    fun x' hx' => H.holT.1 d.n pp qq e _ (holPhi H R w hc T A hAc hAi pp qq e hA x') (betaW d R w T) (hchar x' hx')
  have hleft : ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ) (xx : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' →
      aᴴ * betaW d R w T * a = betaW d R w T →
      ∀ x, fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w xx * x) = F0 pp qq e xx * fc d.B.ψ d.b nb lam 𝓖 A T x := by
    intro a a' xx hxx hs x
    obtain ⟨x', y₀, rfl, hx'⟩ := decW_pf R w x
    rw [← mul_assoc, ← hx' xx, mul_assoc, ← map_mul, hright x' hx' a a' xx y₀ hxx hs]
  refine ⟨fun τ y hy x => ?_, fun uM ν 𝓤 hu u x => ?_⟩
  · rw [hleft _ _ y hy (stab_diag L.i₀ _ (fun k hk => by simp [Pi.single_eq_of_ne hk]) _ hr hcol) x,
      weight_factor_dilation L.i₀ τ y hy]
    congr 2
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · have h0 := Krd.zeta_ne R.hζ
    refine (H.uEx F E σ d R L).2 uM ν 𝓤 hu w _ (fcCont d hc T A hAc hAi)
      (fun u hu' x => (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT A hAc hAi u hu' x) ?_ u x
    intro u y huy x
    rw [huy]
    obtain ⟨a', ha'⟩ := hu.1 u
    set S := ∑ j, Matrix.single L.i₀ (L.em j) (u j) with hS
    have hne : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
    set M := d.cw w S with hMdef
    have hM : ∀ k l, k ≠ L.i₀ → M k l = 0 := by
      intro k l hk
      simp [hMdef, hS, SD.cw, Matrix.map_apply, Matrix.sum_apply, Ne.symm hk]
    have hM0 : M L.i₀ L.i₀ = 0 := by
      simp [hMdef, hS, SD.cw, Matrix.map_apply, Matrix.sum_apply, hne]
    have hmy : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y)) * dZ d.n R.ζ⁻¹ := by
      rw [KSplitW.cw_iota]
      simp only [← Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.one_mul]
      rw [Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.mul_one]
    rw [← huy, ha'] at hmy
    have hy : mR y = Matrix.fromBlocks (1 + M) 0 0 ((R.ζ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ)) * d.cw w a' *
        (R.ζ⁻¹ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ))) := by
      rw [hmy, hMdef]
      simp [dZ, SD.cw, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_add (f := _)]
    rw [hleft _ _ y hy (stab_row L.i₀ M hM _ hr hcol) x, weight_factor_det_one pp qq e y _ _ hy (det_row L.i₀ M hM hM0), one_mul]

end PositivityTheory.SiegelWeilFormula.AStep

end
