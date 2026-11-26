module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.BigProjP
public import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.UnitaryMatrixCoefficientDecay

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.IntegralGermIndependentOfSystem
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

def IntegralGermIndependentOfSystem : Prop := ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → ∀ {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)) (σ : Matrix (Fin r) (Fin r) ℂ → (B →L[ℂ] B)) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (ν : Measure (UJ ε')) [ν.IsHaarMeasure] (dπ dσ : ℝ), IsU (onU ε π) → IsU (onU ε' σ) → IsFd μ (onU ε π) dπ → IsFd ν (onU ε' σ) dσ → ∀ i : B →L[ℂ] A, IsIsoMap (onU ε' σ) (res ι π) i → ∀ (v₀ : A) (w : B), ‖v₀‖ = 1 → ‖w‖ = 1 → ∀ Y₁ K D : ℝ, 1 ≤ Y₁ → 0 < K → ∫⁻ g, ENNReal.ofReal (nsq (umat g⁻¹ *ᵥ z) * ‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (Y₁ / 2) * ∫⁻ g, ENNReal.ofReal (‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ → ENNReal.ofReal dπ * μ {g | hs (umat g) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2} ≤ ENNReal.ofReal K → 1 / dσ ≤ D * ν.real (ball ε' 1) → ∃ g₀ : UJ ε, hs (umat g₀) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2 ∧ 1 ≤ 4 * D * K * ‖ContinuousLinearMap.adjoint i (π (umat g₀) v₀)‖ ^ 2

def EmbSt : Prop := (∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), Fits ε ε' e → ∃ ι : UJ ε' →* UJ ε, (∀ h, umat (ι h) = GlobalTheory.CompanionTheory.PairingAnalysis.emb e (um h)) ∧ IsStdStab ε ε' ι (Pi.single (zi e) 1) ∧ ∀ h : Matrix (Fin n) (Fin n) ℂ, incl e * h * (incl e)ᴴ + vecMulVec (Pi.single (zi e) (1 : ℂ)) (star (Pi.single (zi e) (1 : ℂ) : Fin (n + 1) → ℂ)) = GlobalTheory.CompanionTheory.PairingAnalysis.emb e h) ∧ (∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m), nsq (g *ᵥ Pi.single j 1) = colSq g j) ∧ (∀ {m : ℕ} (ε : Fin m → Bool) {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)), IsURepOn (UJset ε) π → IsU (onU ε π)) ∧ ∀ {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)) (μ : Measure (UJ ε)), μ.IsHaarMeasure → IsHCParam lam → IsDS ε lam π → μ.IsMulRightInvariant ∧ (∃ d, IsFdeg μ π d ∧ IsFd μ (onU ε π) d) ∧ ∃ v ∈ lowKSub ε lam π, ‖v‖ = 1

theorem num_C {n : ℕ} {x : ℝ} (hn : 1 ≤ n) (hx : 3 ≤ x) (hnx : (n : ℝ) ≤ x) :
    Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ (12 * (n + 1) ^ 2) ≤
      x ^ (30 * (n + 1) ^ 2) := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ x := (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hx
  have e1 : Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) =
      (n : ℝ) ^ (6 * (n + 1) ^ 2) * Real.exp 1 ^ (12 * (n + 1) ^ 2) := by
    rw [Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_log (pow_pos h0 (6 * (n + 1) ^ 2)), Real.log_pow]
    push_cast
    rw [mul_one]
  rw [e1, show 30 * (n + 1) ^ 2 = 6 * (n + 1) ^ 2 + 12 * (n + 1) ^ 2 + 12 * (n + 1) ^ 2 by ring, pow_add x, pow_add x]
  gcongr

theorem num_D {n : ℕ} {x : ℝ} (hx : 16 ≤ x) (hnx : (n : ℝ) ≤ x) :
    (x ^ (30 * (n + 1) ^ 2)) ^ 2 * (2 * (16 * (n : ℝ) ^ 2) ^ (2 * n ^ 2)) ≤ x ^ (67 * (n + 1) ^ 2) := by
  have h1 : (1 : ℝ) ≤ x := by linarith
  have h2 : 16 * (n : ℝ) ^ 2 ≤ x ^ 3 := by
    rw [pow_succ' x 2]; gcongr
  calc _ ≤ (x ^ (30 * (n + 1) ^ 2)) ^ 2 * (x * (x ^ 3) ^ (2 * n ^ 2)) := by gcongr; linarith
    _ = x ^ (60 * (n + 1) ^ 2 + 1 + 6 * n ^ 2) := by rw [← pow_mul, ← pow_mul, ← pow_succ', ← pow_add]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ h1 (by
      have a1 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have a2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)

theorem num_Y {N : ℕ} {x : ℝ} (hN : 1 ≤ N) (hx : 9 ≤ x) (hnx : (N : ℝ) ≤ x) :
    64 * (N : ℝ) * ((N : ℝ) + 2 * x ^ (8 * N)) ^ 2 ≤ x ^ (20 * N) := by
  have h1 : (1 : ℝ) ≤ x := by linarith
  have h2 : (N : ℝ) ≤ x ^ (8 * N) := hnx.trans (le_self_pow₀ h1 (by omega))
  calc _ ≤ x ^ 2 * x * (3 * x ^ (8 * N)) ^ 2 := by gcongr <;> nlinarith
    _ = 9 * x ^ (16 * N + 3) := by ring
    _ ≤ x * x ^ (16 * N + 3) := by gcongr
    _ = x ^ (16 * N + 4) := by ring
    _ ≤ _ := pow_le_pow_right₀ h1 (by omega)

theorem num_V {N : ℕ} {B x : ℝ} (hN : 3 ≤ N) (hB : 2 ≤ B) (hx : x = 8 * N * B) :
    (4 * N * (Real.sqrt N + 1) * x ^ (10 * N) / ((100 * N * (B + 1)) ^ 2)⁻¹) ^ (2 * N ^ 2) ≤ x ^ (24 * N ^ 3) := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 25 ≤ x := by rw [hx]; nlinarith
  have a1 : 4 * (N : ℝ) ≤ x := by rw [hx]; nlinarith
  have a2 : Real.sqrt N + 1 ≤ x := by
    have : Real.sqrt N ≤ N := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    linarith
  have a3 : 100 * N * (B + 1) ≤ x ^ 2 := by
    have : 100 * N * (B + 1) ≤ 25 * x := by rw [hx]; nlinarith
    nlinarith
  rw [div_inv_eq_mul]
  calc _ ≤ (x * x * x ^ (10 * N) * (x ^ 2) ^ 2) ^ (2 * N ^ 2) := by gcongr
    _ = x ^ ((10 * N + 6) * (2 * N ^ 2)) := by rw [pow_mul x (10 * N + 6)]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by nlinarith [Nat.mul_le_mul_right (N ^ 2) hN])


end PositivityTheory.UnitaryDecomposition.X4
end
end

section -- merged from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.Imports
section -- merged from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.HsTrace
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

theorem hs_trace {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : (hs X : ℂ) = trace (Xᴴ * X) := by
  simp only [hs, trace, diag_apply, Matrix.mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem jm_ct {m : ℕ} (ε : Fin m → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1; funext a
  simp only [Pi.star_apply]; split_ifs <;> simp

theorem stab : ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → IsNormEmb ι ∧ (∀ h, hs (umat (ι h)) = hs (umat h) + 1) ∧ ∀ g : UJ ε, umat g *ᵥ z = z → ∃ h, ι h = g := by
  intro n r ε ε' ι z ⟨F, hF, FF, Fz, hz⟩
  set Z : Matrix (Fin n) Unit ℂ := replicateCol Unit z with hZ
  have col : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin n) ℂ), M * Z = replicateCol Unit (M *ᵥ z) := fun M => by
    ext i j; simp [hZ, Matrix.mul_apply, mulVec, dotProduct]
  have FZ : Fᴴ * Z = 0 := by rw [col, Fz]; ext; simp
  have ZF : Zᴴ * F = 0 := by simpa using congrArg conjTranspose FZ
  have ZZ : Zᴴ * Z = 1 := by
    ext i j
    have : ((nsq z : ℝ) : ℂ) = 1 := by rw [hz]; simp
    simp only [hZ, Matrix.mul_apply, conjTranspose_apply, replicateCol_apply, Complex.star_def, Complex.conj_mul', Subsingleton.elim i j,
      one_apply_eq]
    rw [← this, GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq]; push_cast; rfl
  have S : F * Fᴴ + Z * Zᴴ = 1 := by
    have e : Fin n ≃ Fin r ⊕ Unit := Fintype.equivOfCardEq (by simp [← hF.codim])
    have h1 : (fromCols F Z)ᴴ * fromCols F Z = 1 := by
      rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, FF, FZ, ZF, ZZ, fromBlocks_one]
    have h2 := (mul_eq_one_comm_of_equiv e.symm).1 h1
    rwa [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows] at h2
  have FJZ : Fᴴ * Jm ε * Z = 0 := by rw [col, hF.perp]; ext; simp
  have ZJF : Zᴴ * Jm ε * F = 0 := by
    have := congrArg conjTranspose FJZ
    simpa [jm_ct, Matrix.mul_assoc] using this
  have ZJZ : Zᴴ * Jm ε * Z = 1 := by
    ext i j
    rw [Matrix.mul_assoc, col, Subsingleton.elim i j, one_apply_eq, ← hF.one]
    simp [hZ, mul_apply, dotProduct]
  have JZ : Jm ε * Z = Z := by
    rw [← Matrix.one_mul (Jm ε * Z), ← S, Matrix.add_mul, Matrix.mul_assoc F, Matrix.mul_assoc Z, ← Matrix.mul_assoc Fᴴ,
      ← Matrix.mul_assoc Zᴴ, FJZ, ZJZ]; simp
  have A : ∀ h, umat (ι h) = F * umat h * Fᴴ + Z * Zᴴ := fun h => by
    rw [← Matrix.mul_one (umat (ι h)), ← S, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hF.act, col, hF.fix]
  have hsF : ∀ M : Matrix (Fin r) (Fin r) ℂ, trace ((F * M * Fᴴ)ᴴ * (F * M * Fᴴ)) = trace (Mᴴ * M) := fun M => by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Fᴴ F, FF, Matrix.one_mul, trace_mul_comm]
    simp only [Matrix.mul_assoc, FF, Matrix.mul_one]
  have cA : Continuous fun h => umat (ι h) := by
    simp only [A]
    exact ((continuous_const.matrix_mul Formalism.MainNotions.BridgeCSchur.continuous_umat).matrix_mul continuous_const).add continuous_const
  refine ⟨⟨?_, fun h => ?_⟩, fun h => ?_, fun g hg => ?_⟩
  · refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cA, ?_⟩)
    have : Continuous fun h => umat (ι h⁻¹) := cA.comp continuous_inv
    exact this.congr fun h => by rw [map_inv]; rfl
  · have : umat (ι h) - 1 = F * (umat h - 1) * Fᴴ := by
      rw [A, ← S, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
    exact_mod_cast (by rw [hs_trace, hs_trace, this, hsF] : (hs (umat (ι h) - 1) : ℂ) = hs (umat h - 1))
  · have : (hs (umat (ι h)) : ℂ) = hs (umat h) + 1 := by
      rw [hs_trace, hs_trace, A, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add,
        trace_add, hsF]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Fᴴ Z, FZ, ← Matrix.mul_assoc Zᴴ F, ZF, ← Matrix.mul_assoc Zᴴ Z, ZZ, Matrix.one_mul]
      simp [trace_mul_comm Z, ZZ]
    exact_mod_cast this
  · have gZ : umat g * Z = Z := by rw [col, hg]
    have gJ : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
    have ZgF : Zᴴ * (umat g * F) = 0 := by
      have h1 : Zᴴ = Zᴴ * (umat g)ᴴ * Jm ε := by
        rw [← conjTranspose_mul, gZ, ← jm_ct ε, ← conjTranspose_mul, JZ]
      calc _ = Zᴴ * (umat g)ᴴ * Jm ε * (umat g * F) := by rw [← h1]
        _ = Zᴴ * ((umat g)ᴴ * Jm ε * umat g) * F := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [gJ, ZJF]
    have gF : umat g * F = F * (Fᴴ * (umat g * F)) := by
      conv_lhs => rw [← Matrix.one_mul (umat g * F), ← S, Matrix.add_mul, Matrix.mul_assoc Z, ZgF, Matrix.mul_zero, add_zero,
        Matrix.mul_assoc]
    set h := Fᴴ * (umat g * F) with hh
    have hU : inUJ ε' h := by
      show hᴴ * Jm ε' * h = Jm ε'
      calc hᴴ * Jm ε' * h = (F * h)ᴴ * Jm ε * (F * h) := by
            rw [← hF.gram]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = Fᴴ * ((umat g)ᴴ * Jm ε * umat g) * F := by rw [← gF]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [gJ, hF.gram]
    refine ⟨indefiniteUnitaryMk ε' h hU, Subtype.ext (Units.ext ?_)⟩
    show umat _ = umat g
    rw [A, show umat (indefiniteUnitaryMk ε' h hU) = h from rfl, ← gF]
    conv_rhs => rw [← Matrix.mul_one (umat g), ← S, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gZ]

end PositivityTheory.UnitaryDecomposition.X4
end
end

section -- merged from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.IsFdAbs
section -- merged from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.Unfold
open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

theorem unfold : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] (ι : H →* G), Continuous ι → ∀ (F : G → ENNReal), Measurable F → ∀ (S C : Set G) (U : Set H), MeasurableSet S → MeasurableSet C → MeasurableSet U → (∀ g ∈ S, ∃ h₀ : H, ∀ u ∈ U, (ι (h₀ * u))⁻¹ * g ∈ C) → ∀ s : ENNReal, (∀ c ∈ C, ∫⁻ h, F (ι h * c) ∂ν ≤ s) → ν U * ∫⁻ g in S, F g ∂μ ≤ μ C * s := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ ι hι F hF S C U hS hC hU hSC s hs
  have hind : Measurable (C.indicator (1 : G → ENNReal)) := measurable_one.indicator hC
  have hin : ∀ g : G, Measurable (fun h : H => C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g)) :=
    fun g => hind.comp (((hι.inv).mul continuous_const).measurable)
  have step1 : ∀ g ∈ S, ν U ≤ ∫⁻ h, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) ∂ν := by
    intro g hg
    obtain ⟨h₀, hh₀⟩ := hSC g hg
    have hT : MeasurableSet ((fun h => h₀⁻¹ * h) ⁻¹' U) := measurable_const_mul h₀⁻¹ hU
    calc ν U = ν ((fun h => h₀⁻¹ * h) ⁻¹' U) := (measure_preimage_mul ν h₀⁻¹ U).symm
      _ = ∫⁻ h, ((fun h => h₀⁻¹ * h) ⁻¹' U).indicator 1 h ∂ν := (lintegral_indicator_one hT).symm
      _ ≤ ∫⁻ h, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) ∂ν := by
        refine lintegral_mono fun h => ?_
        by_cases hm : h ∈ (fun h => h₀⁻¹ * h) ⁻¹' U
        · have hc := hh₀ _ hm
          simp only [mul_inv_cancel_left] at hc
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem hc]
          simp
        · rw [Set.indicator_of_notMem hm]
          exact bot_le
  calc ν U * ∫⁻ g in S, F g ∂μ = ∫⁻ g in S, ν U * F g ∂μ := (lintegral_const_mul _ hF).symm
    _ = ∫⁻ g, S.indicator (fun g => ν U * F g) g ∂μ := (lintegral_indicator hS _).symm
    _ ≤ ∫⁻ g, ∫⁻ h, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) * F g ∂ν ∂μ := by
        refine lintegral_mono fun g => ?_
        by_cases hg : g ∈ S
        · rw [Set.indicator_of_mem hg, lintegral_mul_const _ (hin g)]
          exact mul_le_mul' (step1 g hg) le_rfl
        · rw [Set.indicator_of_notMem hg]
          exact bot_le
    _ = ∫⁻ h, ∫⁻ g, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) * F g ∂μ ∂ν := by
        refine lintegral_lintegral_swap ?_
        exact ((hind.comp (((hι.comp continuous_snd).inv.mul continuous_fst).measurable)).mul
          (hF.comp measurable_fst)).aemeasurable
    _ = ∫⁻ h, ∫⁻ c, C.indicator (1 : G → ENNReal) c * F (ι h * c) ∂μ ∂ν := by
        refine lintegral_congr fun h => ?_
        rw [← lintegral_mul_left_eq_self _ (ι h)]
        simp only [inv_mul_cancel_left]
    _ = ∫⁻ c, ∫⁻ h, C.indicator (1 : G → ENNReal) c * F (ι h * c) ∂ν ∂μ := by
        refine lintegral_lintegral_swap ?_
        exact ((hind.comp measurable_snd).mul
          (hF.comp ((hι.comp continuous_fst).mul continuous_snd).measurable)).aemeasurable
    _ = ∫⁻ c, C.indicator (1 : G → ENNReal) c * ∫⁻ h, F (ι h * c) ∂ν ∂μ := by
        refine lintegral_congr fun c => ?_
        exact lintegral_const_mul _ (hF.comp (hι.mul continuous_const).measurable)
    _ ≤ ∫⁻ c, C.indicator (1 : G → ENNReal) c * s ∂μ := by
        refine lintegral_mono fun c => ?_
        by_cases hc : c ∈ C
        · rw [Set.indicator_of_mem hc]
          simpa using hs c hc
        · rw [Set.indicator_of_notMem hc]
          simp
    _ = μ C * s := by
        rw [lintegral_mul_const _ hind, lintegral_indicator_one hC]

end PositivityTheory.UnitaryDecomposition.X4
end

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

theorem hs_nonneg' {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hs a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem hs_mul_le' {m : ℕ} (a b : Matrix (Fin m) (Fin m) ℂ) : hs (a * b) ≤ hs a * hs b := by
  unfold hs
  rw [Finset.sum_comm (f := fun i j => ‖b i j‖ ^ 2), Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.mul_apply]
  refine (pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq ?_)) 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a i k‖) fun k => ‖b k j‖)
  simp only [norm_mul]

theorem umat_inv' {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : umat g⁻¹ = Jm ε * (umat g)ᴴ * Jm ε := by
  have hg : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h1 : umat g * umat g⁻¹ = 1 := g.1.mul_inv
  calc umat g⁻¹ = Jm ε * ((umat g)ᴴ * Jm ε * umat g) * umat g⁻¹ := by rw [hg, Jm_mul_self, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem hs_inv' {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hs (umat g⁻¹) = hs (umat g) := by
  rw [umat_inv']
  unfold hs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_star]
  split_ifs <;> simp

theorem hs_le_of_sub {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) : hs a ≤ 2 * hs (a - 1) + 2 * m := by
  have h1 : hs (1 : Matrix (Fin m) (Fin m) ℂ) = m := by
    unfold hs
    simp [Matrix.one_apply, apply_ite, Finset.sum_ite_eq]
  rw [← h1]
  unfold hs
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h : ‖a i j‖ ≤ ‖(a - 1) i j‖ + ‖(1 : Matrix (Fin m) (Fin m) ℂ) i j‖ := by
    refine le_trans (le_of_eq ?_) (norm_add_le _ _)
    simp
  nlinarith [norm_nonneg (a i j), norm_nonneg ((a - 1) i j), norm_nonneg ((1 : Matrix (Fin m) (Fin m) ℂ) i j),
    sq_nonneg (‖(a - 1) i j‖ - ‖(1 : Matrix (Fin m) (Fin m) ℂ) i j‖)]

theorem continuous_hs {X : Type} [TopologicalSpace X] {m : ℕ} {f : X → Matrix (Fin m) (Fin m) ℂ} (hf : Continuous f) :
    Continuous fun x => hs (f x) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hf.matrix_elem i j).norm.pow 2

theorem isU_adj {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {ρ : Γ → (A →L[ℂ] A)} (h : IsU ρ) (g : Γ) (x y : A) : ⟪x, ρ g y⟫_ℂ = ⟪ρ g⁻¹ x, y⟫_ℂ := by
  have hx : x = ρ g (ρ g⁻¹ x) := by
    rw [← ContinuousLinearMap.mul_apply, ← h.mul, mul_inv_cancel, h.one]; rfl
  conv_lhs => rw [hx]
  exact (LinearIsometry.mk (ρ g : A →ₗ[ℂ] A) (h.norm g)).inner_map_map _ y

theorem isFd_abs {Γ : Type} [MeasurableSpace Γ] {ν : Measure Γ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {ρ : Γ → (A →L[ℂ] A)} {d : ℝ} (h : IsFd ν ρ d) (x y : A) :
    ∫⁻ g, ENNReal.ofReal (‖⟪y, ρ g x⟫_ℂ‖ ^ 2) ∂ν = ENNReal.ofReal (‖x‖ ^ 2 * ‖y‖ ^ 2 / d) := by
  obtain ⟨hi, he⟩ := h.2 x y x y
  have hf : (fun g => ⟪y, ρ g x⟫_ℂ * star ⟪y, ρ g x⟫_ℂ) = fun g => ((‖⟪y, ρ g x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hf] at hi he
  have hi' : Integrable (fun g => ‖⟪y, ρ g x⟫_ℂ‖ ^ 2) ν := by simpa using hi.norm
  rw [← ofReal_integral_eq_lintegral_ofReal hi' (.of_forall fun _ => by positivity)]
  congr 1
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at he
  simp only [Complex.coe_algebraMap] at he
  exact_mod_cast he

theorem standard_stabiliser_bound (hst : ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → IsNormEmb ι ∧ (∀ h, hs (umat (ι h)) = hs (umat h) + 1) ∧ ∀ g : UJ ε, umat g *ᵥ z = z → ∃ h, ι h = g) (hbo : ∀ {n : ℕ} (ε : Fin n → Bool) (z y : Fin n → ℂ), star z ⬝ᵥ (Jm ε *ᵥ z) = 1 → nsq z = 1 → star y ⬝ᵥ (Jm ε *ᵥ y) = 1 → ∃ g : UJ ε, umat g *ᵥ z = y ∧ hs (umat g) ≤ 16 * ((n : ℝ) + nsq y) ^ 2) : ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → ∀ {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)) (σ : Matrix (Fin r) (Fin r) ℂ → (B →L[ℂ] B)) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (ν : Measure (UJ ε')) [ν.IsHaarMeasure] (dπ dσ : ℝ), IsU (onU ε π) → IsU (onU ε' σ) → IsFd μ (onU ε π) dπ → IsFd ν (onU ε' σ) dσ → ∀ i : B →L[ℂ] A, IsIsoMap (onU ε' σ) (res ι π) i → ∀ (v₀ : A) (w : B), ‖v₀‖ = 1 → ‖w‖ = 1 → ∀ Y₁ K D : ℝ, 1 ≤ Y₁ → 0 < K → ∫⁻ g, ENNReal.ofReal (nsq (umat g⁻¹ *ᵥ z) * ‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (Y₁ / 2) * ∫⁻ g, ENNReal.ofReal (‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ → ENNReal.ofReal dπ * μ {g | hs (umat g) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2} ≤ ENNReal.ofReal K → 1 / dσ ≤ D * ν.real (ball ε' 1) → ∃ g₀ : UJ ε, hs (umat g₀) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2 ∧ 1 ≤ 4 * D * K * ‖ContinuousLinearMap.adjoint i (π (umat g₀) v₀)‖ ^ 2 := by
  intro n r ε ε' ι z hz A B _ _ _ _ _ _ π σ μ _ ν _ dπ dσ hπ hσ fπ fσ i hi v₀ w hv hw Y₁ K D hY hK hM hV hD
  obtain ⟨⟨hc, hne⟩, -, hsur⟩ := hst ι z hz
  obtain ⟨Fr, hFr, -, -, hz1⟩ := hz
  have hn : (1 : ℝ) ≤ n := by have := hFr.codim; exact_mod_cast (by omega : 1 ≤ n)
  have cu : Continuous fun g : UJ ε => umat g := Formalism.MainNotions.BridgeCSchur.continuous_umat
  have cu' : Continuous fun g : UJ ε' => umat g := Formalism.MainNotions.BridgeCSchur.continuous_umat
  by_contra hcon
  push Not at hcon
  set P := ContinuousLinearMap.adjoint i with hP
  set F : UJ ε → ENNReal := fun g => ENNReal.ofReal (‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) with hF
  have hFm : Measurable F := ((continuous_const.inner (hπ.cont v₀)).norm.pow 2).measurable.ennreal_ofReal
  set S : Set (UJ ε) := {g | nsq (umat g⁻¹ *ᵥ z) ≤ Y₁} with hS
  have cn : Continuous fun g : UJ ε => nsq (umat g⁻¹ *ᵥ z) :=
    continuous_finsetSum _ fun a _ => ((continuous_apply a).comp ((cu.comp continuous_inv).matrix_mulVec continuous_const)).norm.pow 2
  have hSm : MeasurableSet S := (isClosed_le cn continuous_const).measurableSet
  have hCm : MeasurableSet {g : UJ ε | hs (umat g) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2} :=
    (isClosed_le (continuous_hs cu) continuous_const).measurableSet
  have hUm : MeasurableSet (ball ε' 1) := (isClosed_le (continuous_hs (cu'.sub continuous_const)) continuous_const).measurableSet
  have hσ0 : 0 < 1 / dσ := one_div_pos.2 fσ.1
  have hU0 : 0 ≤ ν.real (ball ε' 1) := measureReal_nonneg
  have hDU : 0 < D * ν.real (ball ε' 1) := hσ0.trans_le hD
  have hUp : 0 < ν.real (ball ε' 1) := lt_of_le_of_ne hU0 fun e => by rw [← e, mul_zero] at hDU; exact lt_irrefl _ hDU
  have hD0 : 0 < D := (mul_pos_iff_of_pos_right hUp).1 hDU
  have hI : ∫⁻ g, F g ∂μ = ENNReal.ofReal (1 / dπ) := by
    have := isFd_abs fπ v₀ (i w)
    rwa [hv, hi.2, hw, one_pow, mul_one] at this
  have key := unfold μ ν ι hc F hFm S _ (ball ε' 1) hSm hCm hUm (fun g hg => ?_)
    (ENNReal.ofReal (1 / (4 * D * K) / dσ)) fun c hcC => ?_
  · have hsplit := lintegral_add_compl F (μ := μ) hSm
    have hb : ENNReal.ofReal Y₁ * ∫⁻ g in Sᶜ, F g ∂μ ≤ ENNReal.ofReal (Y₁ / 2) * ENNReal.ofReal (1 / dπ) := by
      rw [← hI]
      refine le_trans ?_ hM
      rw [← lintegral_const_mul _ hFm]
      refine le_trans (setLIntegral_mono' hSm.compl fun g hg => ?_) (setLIntegral_le_lintegral _ _)
      rw [hF, ← ENNReal.ofReal_mul (by linarith)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_of_lt (not_le.1 hg)) (by positivity))
    rw [hI] at hsplit
    have ta : ∫⁻ g in S, F g ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsplit ▸ le_self_add)
    have tb : ∫⁻ g in Sᶜ, F g ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsplit ▸ le_add_self)
    have hπ0 : 0 < 1 / dπ := one_div_pos.2 fπ.1
    have r1 := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add ta tb, ENNReal.toReal_ofReal hπ0.le] at r1
    have r2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hb
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal hπ0.le] at r2
    have r3 : 1 / dπ / 2 ≤ (∫⁻ g in S, F g ∂μ).toReal := by
      have : (∫⁻ g in Sᶜ, F g ∂μ).toReal ≤ 1 / dπ / 2 := le_of_mul_le_mul_left (by linarith) (by linarith : 0 < Y₁)
      linarith
    have k2 : ENNReal.ofReal dπ * (ν (ball ε' 1) * ∫⁻ g in S, F g ∂μ) ≤
        ENNReal.ofReal K * ENNReal.ofReal (1 / (4 * D * K) / dσ) :=
      (mul_le_mul_right key _).trans (by rw [← mul_assoc]; exact mul_le_mul_left hV _)
    have r4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) k2
    have hp : 0 ≤ 1 / (4 * D * K) / dσ := div_nonneg (by positivity) fσ.1.le
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal fπ.1.le,
      ENNReal.toReal_ofReal hK.le, ENNReal.toReal_ofReal hp] at r4
    have r5 : K * (1 / (4 * D * K) / dσ) = 1 / dσ / (4 * D) := by have := fσ.1; field_simp
    have r6 : 1 / dσ / (4 * D) ≤ ν.real (ball ε' 1) / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have r7 : ν.real (ball ε' 1) / 2 ≤ dπ * (ν.real (ball ε' 1) * (∫⁻ g in S, F g ∂μ).toReal) := by
      calc ν.real (ball ε' 1) / 2 = dπ * (ν.real (ball ε' 1) * (1 / dπ / 2)) := by have := fπ.1; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r3 hU0) fπ.1.le
    have r8 : (ν (ball ε' 1)).toReal = ν.real (ball ε' 1) := rfl
    rw [r8, r5] at r4
    linarith
  · have hy : star (umat g⁻¹ *ᵥ z) ⬝ᵥ (Jm ε *ᵥ (umat g⁻¹ *ᵥ z)) = 1 := by
      have hg' : (umat g⁻¹)ᴴ * Jm ε * umat g⁻¹ = Jm ε := (g⁻¹).2
      rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, hg', hFr.one]
    obtain ⟨gy, hgy, hgn⟩ := hbo ε z _ hFr.one hz1 hy
    obtain ⟨h₀, hh⟩ := hsur (g * gy) (by
      have e1 : umat (g * gy) = umat g * umat gy := rfl
      have e2 : umat g * umat g⁻¹ = 1 := g.1.mul_inv
      rw [e1, ← mulVec_mulVec, hgy, mulVec_mulVec, e2, one_mulVec])
    refine ⟨h₀, fun u hu => ?_⟩
    have e : (ι (h₀ * u))⁻¹ * g = (ι u)⁻¹ * gy⁻¹ := by rw [map_mul, hh]; group
    show hs (umat _) ≤ _
    rw [e, show umat ((ι u)⁻¹ * gy⁻¹) = umat (ι u)⁻¹ * umat gy⁻¹ from rfl]
    refine (hs_mul_le' _ _).trans ?_
    rw [hs_inv', hs_inv']
    have b1 : hs (umat (ι u)) ≤ 4 * n := by
      have := hs_le_of_sub (umat (ι u))
      have h2 : hs (umat u - 1) ≤ 1 ^ 2 := hu
      rw [hne] at this
      linarith
    have n0 : 0 ≤ nsq (umat g⁻¹ *ᵥ z) := Finset.sum_nonneg fun _ _ => by positivity
    have b2 : hs (umat gy) ≤ 16 * ((n : ℝ) + Y₁) ^ 2 :=
      hgn.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by have : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (umat g⁻¹ *ᵥ z) ≤ Y₁ := hg; linarith) 2) (by norm_num))
    calc _ ≤ 4 * n * (16 * ((n : ℝ) + Y₁) ^ 2) := mul_le_mul b1 b2 (hs_nonneg' _) (by linarith)
      _ = _ := by ring
  · have e : ∀ h : UJ ε', F (ι h * c) = ENNReal.ofReal (‖⟪w, onU ε' σ h (P (π (umat c) v₀))⟫_ℂ‖ ^ 2) := fun h => by
      have a1 : π (umat (ι h * c)) v₀ = onU ε π (ι h) (π (umat c) v₀) := DFunLike.congr_fun (hπ.mul (ι h) c) v₀
      have a2 : onU ε π (ι h)⁻¹ (i w) = i (onU ε' σ h⁻¹ w) := by rw [← map_inv]; exact (hi.1 h⁻¹ w).symm
      simp only [hF]
      rw [a1, isU_adj hπ, a2, isU_adj hσ, hP, ContinuousLinearMap.adjoint_inner_right]
    simp only [e]
    rw [isFd_abs fσ, hw, one_pow, mul_one]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ fσ.1.le)
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact (hcon c hcC).le

end PositivityTheory.UnitaryDecomposition.X4
end

section -- merged from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.ReflEx
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

private theorem star_dotProduct_Jm_mulVec_comm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n → ℂ) :
    star (star a ⬝ᵥ (Jm ε *ᵥ b)) = star b ⬝ᵥ (Jm ε *ᵥ a) := by
  simp only [Jm, dotProduct, mulVec_diagonal, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

theorem refl_ex {n : ℕ} (ε : Fin n → Bool) (z y : Fin n → ℂ) (hz : star z ⬝ᵥ (Jm ε *ᵥ z) = 1) (hy : star y ⬝ᵥ (Jm ε *ᵥ y) = 1)
    (c : ℝ) (hc : c ≤ 0) (hyz : star y ⬝ᵥ (Jm ε *ᵥ z) = c) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, inUJ ε R ∧ R *ᵥ z = y ∧ hs R ≤ 2 * n + 2 * nsq (y - z) ^ 2 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ℂ, w = y - z := ⟨_, rfl⟩
  rw [← hw]
  have hzy : star z ⬝ᵥ (Jm ε *ᵥ y) = c := by
    rw [← star_dotProduct_Jm_mulVec_comm, hyz, Complex.star_def, Complex.conj_ofReal]
  have hq : star w ⬝ᵥ (Jm ε *ᵥ w) = 2 - 2 * (c : ℂ) := by
    rw [hw, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hy, hz, hyz, hzy]
    ring
  have hwz : star w ⬝ᵥ (Jm ε *ᵥ z) = c - 1 := by
    rw [hw, star_sub, sub_dotProduct, hyz, hz]
  have hpos : (0 : ℝ) < 2 - 2 * c := by linarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = 2 / (2 - 2 * c) := ⟨_, rfl⟩
  have hk : k * (2 - 2 * c) = 2 := by rw [hkdef, div_mul_cancel₀ _ (ne_of_gt hpos)]
  have hk0 : 0 < k := by rw [hkdef]; exact div_pos (by norm_num) hpos
  have hk1 : k ≤ 1 := by nlinarith
  have hkC : (k : ℂ) * (2 - 2 * (c : ℂ)) = 2 := by exact_mod_cast hk
  have hq' : (star w ᵥ* Jm ε) ⬝ᵥ w = 2 - 2 * (c : ℂ) := by rw [← dotProduct_mulVec, hq]
  have hbj : ∀ j, ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖ ^ 2 = k ^ 2 * ‖w j‖ ^ 2 := by
    intro j
    simp only [Pi.smul_apply, smul_eq_mul, Jm, vecMul_diagonal, norm_mul, Pi.star_apply, norm_star,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0]
    split_ifs <;> simp <;> ring
  have h1 : ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = n := by
    simp [Matrix.one_apply, apply_ite]
  have h2 : ∑ i : Fin n, ∑ j : Fin n, ‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2) = k ^ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2 := by
    simp only [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  refine ⟨1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)), ?_, ?_, ?_⟩
  · show (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)))ᴴ * Jm ε * (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε))) = Jm ε
    have hsb : star ((k : ℂ) • (star w ᵥ* Jm ε)) = (k : ℂ) • (Jm ε *ᵥ w) := by
      rw [star_smul, Matrix.star_vecMul, star_star, Jm_conjTranspose, Complex.star_def, Complex.conj_ofReal]
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_vecMulVec, hsb]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul,
      Matrix.mul_vecMulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, hq']
    ext i j
    simp only [Matrix.sub_apply, vecMulVec_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination ((k : ℂ) * ((Jm ε *ᵥ w) i * (star w ᵥ* Jm ε) j)) * hkC
  · have hkc : (k : ℂ) * ((c : ℂ) - 1) = -1 := by linear_combination (-1 / 2 : ℂ) * hkC
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_dotProduct,
      ← dotProduct_mulVec, hwz, smul_eq_mul, hkc, hw]
    ext i
    simp
  · calc hs (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)))
        = ∑ i, ∑ j, ‖(1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε))) i j‖ ^ 2 := rfl
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (2 * ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
            + 2 * (‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2))) := by
        gcongr with i _ j _
        rw [Matrix.sub_apply, vecMulVec_apply]
        have h3 := norm_sub_le ((1 : Matrix (Fin n) (Fin n) ℂ) i j) (w i * ((k : ℂ) • (star w ᵥ* Jm ε)) j)
        rw [norm_mul] at h3
        have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        have hp : (‖w i‖ * ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖) ^ 2 = ‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2) := by
          rw [mul_pow, hbj]
        nlinarith [sq_nonneg (‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ - ‖w i‖ * ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖)]
      _ = 2 * n + 2 * (k ^ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2) := by
        rw [← h1, ← h2]
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * n + 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2 := by
        have hk2 : k ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hk2 (sq_nonneg (GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w))]

private theorem nsq_sub_le_two_mul_add {n : ℕ} (a b : Fin n → ℂ) :
    GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (a - b) ≤ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq a + 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq b := by
  unfold GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  gcongr with i _
  simp only [Pi.sub_apply]
  have h := norm_sub_le (a i) (b i)
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]

private theorem nsq_nonneg_hilbert_schmidt_traces {n : ℕ} (a : Fin n → ℂ) : 0 ≤ GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq a :=
  Finset.sum_nonneg fun i _ => by positivity

theorem boost : ∀ {n : ℕ} (ε : Fin n → Bool) (z y : Fin n → ℂ), star z ⬝ᵥ (Jm ε *ᵥ z) = 1 → nsq z = 1 → star y ⬝ᵥ (Jm ε *ᵥ y) = 1 → ∃ g : UJ ε, umat g *ᵥ z = y ∧ hs (umat g) ≤ 16 * ((n : ℝ) + nsq y) ^ 2 := by
  classical
  intro n ε z y hz hnz hy
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hz
    · exact h
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = star y ⬝ᵥ (Jm ε *ᵥ z) := ⟨_, rfl⟩
  obtain ⟨u, hu1, hua⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ star u * a = -(‖a‖ : ℂ) := by
    by_cases h0 : a = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn0 : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      have hsq : star a * a = (‖a‖ : ℂ) ^ 2 := by rw [Complex.star_def, Complex.conj_mul']
      refine ⟨-(a / (‖a‖ : ℂ)), ?_, ?_⟩
      · rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_ne_zero_iff.mpr h0)]
      · rw [star_neg, star_div₀, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, neg_mul,
          div_mul_eq_mul_div, hsq, sq, mul_div_assoc, div_self hn0, mul_one]
  have hu2 : star u * u = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hu1]
    simp
  have hy' : star (u • y) ⬝ᵥ (Jm ε *ᵥ (u • y)) = 1 := by
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hy, smul_eq_mul,
      smul_eq_mul, mul_one, hu2]
  have hyz' : star (u • y) ⬝ᵥ (Jm ε *ᵥ z) = ((-‖a‖ : ℝ) : ℂ) := by
    rw [star_smul, smul_dotProduct, ← ha, smul_eq_mul, hua]
    push_cast
    ring
  obtain ⟨R, hR, hRz, hRs⟩ := refl_ex ε z (u • y) hz hy' (-‖a‖) (by simp) hyz'
  have hR' : Rᴴ * Jm ε * R = Jm ε := hR
  have hg : (star u • R)ᴴ * Jm ε * (star u • R) = Jm ε := by
    rw [conjTranspose_smul, star_star]
    simp only [Matrix.smul_mul, Matrix.mul_smul, hR', smul_smul]
    rw [hu2, one_smul]
  have hinv : (Jm ε * (star u • R)ᴴ * Jm ε) * (star u • R) = 1 := by
    rw [show Jm ε * (star u • R)ᴴ * Jm ε * (star u • R)
        = Jm ε * ((star u • R)ᴴ * Jm ε * (star u • R)) by simp only [Matrix.mul_assoc], hg, Jm_mul_self]
  refine ⟨⟨⟨star u • R, Jm ε * (star u • R)ᴴ * Jm ε, mul_eq_one_comm.mp hinv, hinv⟩, hg⟩, ?_, ?_⟩
  · show (star u • R) *ᵥ z = y
    rw [Matrix.smul_mulVec, hRz, smul_smul, hu2, one_smul]
  · show hs (star u • R) ≤ 16 * ((n : ℝ) + GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y) ^ 2
    have hsu : hs (star u • R) = hs R := by
      simp [hs, Matrix.smul_apply, norm_mul, norm_star, hu1]
    have hnu : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (u • y) = GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y := by
      simp [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, norm_mul, hu1]
    have hD := nsq_sub_le_two_mul_add (u • y) z
    rw [hnu, hnz] at hD
    have hD0 := nsq_nonneg_hilbert_schmidt_traces (u • y - z)
    have hs0 := nsq_nonneg_hilbert_schmidt_traces y
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (u • y - z) ^ 2 ≤ (2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y + 2 * 1) ^ 2 :=
      pow_le_pow_left₀ hD0 hD 2
    rw [hsu]
    nlinarith

end PositivityTheory.UnitaryDecomposition.X4
end
end

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

theorem g0 : ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → ∀ {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)) (σ : Matrix (Fin r) (Fin r) ℂ → (B →L[ℂ] B)) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (ν : Measure (UJ ε')) [ν.IsHaarMeasure] (dπ dσ : ℝ), IsU (onU ε π) → IsU (onU ε' σ) → IsFd μ (onU ε π) dπ → IsFd ν (onU ε' σ) dσ → ∀ i : B →L[ℂ] A, IsIsoMap (onU ε' σ) (res ι π) i → ∀ (v₀ : A) (w : B), ‖v₀‖ = 1 → ‖w‖ = 1 → ∀ Y₁ K D : ℝ, 1 ≤ Y₁ → 0 < K → ∫⁻ g, ENNReal.ofReal (nsq (umat g⁻¹ *ᵥ z) * ‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (Y₁ / 2) * ∫⁻ g, ENNReal.ofReal (‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ → ENNReal.ofReal dπ * μ {g | hs (umat g) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2} ≤ ENNReal.ofReal K → 1 / dσ ≤ D * ν.real (ball ε' 1) → ∃ g₀ : UJ ε, hs (umat g₀) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2 ∧ 1 ≤ 4 * D * K * ‖ContinuousLinearMap.adjoint i (π (umat g₀) v₀)‖ ^ 2 := standard_stabiliser_bound stab boost

end PositivityTheory.UnitaryDecomposition.X4
end

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.A.Pf

theorem conv_of {Γ : Type} [Group Γ] [TopologicalSpace Γ] [MeasurableSpace Γ] (ν : Measure Γ) {A : Type}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] (σ : Γ → (A →L[ℂ] A)) (d : ℝ) (hσ : IsU σ) (hd : IsFd ν σ d)
    (w : A) (hw : ‖w‖ = 1) (x : Γ) :
    ∫ g, star ⟪w, σ g w⟫_ℂ * star ⟪w, σ (g⁻¹ * x) w⟫_ℂ ∂ν = ((d⁻¹ : ℝ) : ℂ) * star ⟪w, σ x w⟫_ℂ := by
  have hip : ∀ (g : Γ) (a b : A), ⟪σ g a, σ g b⟫_ℂ = ⟪a, b⟫_ℂ := by
    intro g a b
    let L : A →ₗᵢ[ℂ] A := { toLinearMap := (σ g).toLinearMap, norm_map' := hσ.norm g }
    exact L.inner_map_map a b
  have key : ∀ g : Γ, star ⟪w, σ (g⁻¹ * x) w⟫_ℂ = ⟪σ x w, σ g w⟫_ℂ := by
    intro g
    have h1 : σ (g⁻¹ * x) w = σ g⁻¹ (σ x w) := by
      rw [hσ.mul]; rfl
    have h2 : σ g (σ g⁻¹ (σ x w)) = σ x w := by
      rw [← ContinuousLinearMap.mul_apply, ← hσ.mul, mul_inv_cancel, hσ.one]; rfl
    rw [h1, ← hip g, h2, ← starRingEnd_apply, inner_conj_symm]
  have hint := (hd.2 w (σ x w) w w).2
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hc : ⟪σ x w, w⟫_ℂ = star ⟪w, σ x w⟫_ℂ := by
    rw [← starRingEnd_apply, inner_conj_symm]
  calc ∫ g, star ⟪w, σ g w⟫_ℂ * star ⟪w, σ (g⁻¹ * x) w⟫_ℂ ∂ν
        = ∫ g, ⟪σ x w, σ g w⟫_ℂ * star ⟪w, σ g w⟫_ℂ ∂ν := by
          congr 1; funext g; rw [key g, mul_comm]
    _ = ⟪w, w⟫_ℂ * ⟪σ x w, w⟫_ℂ / (d : ℂ) := hint
    _ = ((d⁻¹ : ℝ) : ℂ) * star ⟪w, σ x w⟫_ℂ := by
          rw [hww, hc]; push_cast; ring

theorem isFd_of_schurK {m : ℕ} {ε : Fin m → Bool} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)} {ν : Measure (UJ ε)} {κ : ℝ} (hK : PositivityTheory.RgHe.SchurK ε σ ν κ) :
    IsFd ν (onU ε σ) κ⁻¹ := by
  refine ⟨inv_pos.mpr hK.1, fun v w v' w' => ?_⟩
  obtain ⟨hi, he⟩ := hK.2 v w v' w'
  refine ⟨hi, ?_⟩
  have e2 : ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((κ⁻¹ : ℝ) : ℂ) = (κ : ℂ) * (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ) := by
    push_cast; rw [div_inv_eq_mul]; ring
  rw [e2]
  exact he

set_option maxHeartbeats 1600000 in
theorem bigProjP_of (hg0 : PositivityTheory.UnitaryDecomposition.X4.IntegralGermIndependentOfSystem) (hem : PositivityTheory.UnitaryDecomposition.X4.EmbSt) : MomentP → Analysis → BigProjP := by
  intro hM hA
  obtain ⟨hVol, hDec, hIntR, hHInt, hDUp, hLip⟩ := hA
  intro n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hDSπ hDSσ
  intro κ hK w hw hw1 hwi i η hiso hint hη hηi hηint v hv hv1
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hem
  obtain ⟨ι, hιum, hιstd, -⟩ := hE1 ε ε' e hF
  have hn2 : 2 ≤ n := hP.two
  have hB : 100 * ((n : ℝ) + 1) ^ 3 ≤ B := by
    obtain ⟨a, ha⟩ := hP.neg
    have hne : ε a ≠ ε (zi e) := by rw [ha, hF.1]; simp
    have h1 := hP.gap a (zi e) hne
    have h2 := hP.bd a
    have h3 := hP.bd (zi e)
    have h4 : |lam a - lam (zi e)| ≤ |lam a| + |lam (zi e)| := abs_sub _ _
    linarith
  have hn3 : (3 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have h27 : (3 : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 := pow_le_pow_left₀ (by norm_num) hn3 3
  have hB2 : (2 : ℝ) ≤ B := by linarith
  set x : ℝ := 8 * ((n : ℝ) + 1) * B with hx
  have hx16 : (16 : ℝ) ≤ x := by rw [hx]; nlinarith
  have hxn : ((n : ℝ) + 1) ≤ x := by rw [hx]; nlinarith
  have hx0 : 0 < x := by linarith
  have hUπ : IsU (onU ε π) := hE3 ε π hDSπ.2.2.1
  have hUσ : IsU (onU ε' σ) := hE3 ε' σ hDSσ.2.2.1
  haveI hμ : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  obtain ⟨-, ⟨dπ, hFdeg, hFd⟩, -⟩ := hE4 ε lam π (muG ε) hμ hP.hc hDSπ
  have hFdσ : IsFd ν (onU ε' σ) κ⁻¹ := isFd_of_schurK hK
  have hIso : IsIsoMap (onU ε' σ) (res ι π) i := by
    refine ⟨fun h y => ?_, hiso⟩
    show i (σ (um h) y) = π (umat (ι h)) (i y)
    rw [hιum]
    exact hint h y
  have hIt : Intertw ε' e π σ (ContinuousLinearMap.adjoint i) := by
    refine ⟨?_, fun h y => ?_⟩
    · rw [LinearIsometryEquiv.norm_map]
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by rw [hiso, one_mul])
    · apply ext_inner_left ℂ
      intro z
      rw [ContinuousLinearMap.adjoint_inner_right]
      have a1 := UnitaryDecomposition.X4.isU_adj hUπ (ι h) (i z) y
      have a2 := UnitaryDecomposition.X4.isU_adj hUσ h z (ContinuousLinearMap.adjoint i y)
      have e1 : onU ε π (ι h) = π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (um h)) := by
        show π (umat (ι h)) = _
        rw [hιum]
      have e2 : onU ε π (ι h)⁻¹ (i z) = i (σ (um h⁻¹) z) := by
        rw [← map_inv]
        show π (umat (ι h⁻¹)) (i z) = _
        rw [hιum, hint]
      rw [e1] at a1
      rw [a1, e2, ← ContinuousLinearMap.adjoint_inner_right]
      exact a2.symm
  have hconv : ∀ y : UJ ε', ∫ h, starRingEnd ℂ ⟪w, σ (um h) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um (h⁻¹ * y)) w⟫_ℂ ∂ν
      = (κ : ℂ) * starRingEnd ℂ ⟪w, σ (um y) w⟫_ℂ := by
    intro y
    have := conv_of ν (onU ε' σ) κ⁻¹ hUσ hFdσ w hw1 y
    rw [inv_inv] at this
    exact this
  have hmom := hM n ε lam ε' mu B e H H' π σ ν hν hF hP hDSπ hDSσ (ContinuousLinearMap.adjoint i) w κ hIt hw1
    (by rw [ContinuousLinearMap.adjoint_adjoint, hiso, hw1]) hK.1 hwi hconv
    ⟨η, hη, by rw [ContinuousLinearMap.adjoint_adjoint]; exact hηi,
      by rw [ContinuousLinearMap.adjoint_adjoint]; exact hηint⟩ v hv hv1
  rw [ContinuousLinearMap.adjoint_adjoint] at hmom
  have hone : σ (um (1 : UJ ε')) = 1 := hUσ.one
  have hhs1 : hs (um (1 : UJ ε')) ≤ (n : ℝ) := by
    have h1 : um (1 : UJ ε') = 1 := rfl
    rw [h1]
    simp only [hs, Matrix.one_apply]
    have h2 : ∀ i j : Fin n, ‖(if i = j then (1 : ℂ) else 0)‖ ^ 2 = if i = j then (1 : ℝ) else 0 := by
      intro i j; split_ifs <;> simp
    simp only [h2, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact le_rfl
  have hgap' : GapAtLeast ε' mu (200 * ((n + 1 : ℕ) : ℝ) ^ 3) := by
    push_cast; exact hP.gap'
  have hdec : ∀ g : UJ ε', ‖⟪w, σ (um g) w⟫_ℂ‖ ≤ Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n
      + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ (12 * (n + 1) ^ 2) * hs (um g) ^ (-(6 * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    intro g
    have := hDec n (n + 1) ε' mu H' σ (by omega) (by omega) hP.hc' hDSσ hgap' w hw hw1 1 n hhs1 g
    rw [hone] at this
    simpa only [ContinuousLinearMap.one_apply] using this
  have hC := UnitaryDecomposition.X4.num_C (n := n) (x := x) (by omega) (by linarith) (by linarith)
  have hsnn : ∀ g : UJ ε', 0 ≤ hs (um g) := fun g =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  have hφb : ∀ g : UJ ε', ‖⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ‖
      ≤ (x ^ (30 * (n + 1) ^ 2)) ^ 2 * hs (um g) ^ (-(2 * (6 * ((n + 1 : ℕ) : ℝ) ^ 2))) := by
    intro g
    have hc := le_trans (hdec g) (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (hsnn g) _))
    have hn0 := norm_nonneg ⟪w, σ (um g) w⟫_ℂ
    have e1 : ‖⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ‖ = ‖⟪w, σ (um g) w⟫_ℂ‖ ^ 2 := by
      rw [norm_mul, RCLike.norm_conj, sq]
    have e2 : hs (um g) ^ (-(2 * (6 * ((n + 1 : ℕ) : ℝ) ^ 2)))
        = (hs (um g) ^ (-(6 * ((n + 1 : ℕ) : ℝ) ^ 2))) ^ 2 := by
      rw [← Real.rpow_mul_natCast (hsnn g)]
      congr 1
      push_cast
      ring
    rw [e1, e2, ← mul_pow]
    exact pow_le_pow_left₀ hn0 hc 2
  have hc1 : Continuous fun g : UJ ε' => ⟪w, σ (um g) w⟫_ℂ :=
    continuous_const.inner (by exact hUσ.cont w : Continuous fun g : UJ ε' => σ (um g) w)
  have hφc : Continuous fun g : UJ ε' => ⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ :=
    hc1.mul (Complex.continuous_conj.comp hc1)
  have ha : ((n : ℕ) : ℝ) ^ 2 + 1 ≤ 2 * (6 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    push_cast; nlinarith
  obtain ⟨-, hIφ⟩ := hIntR n ε' ν hν (by omega) _ _ _ hφc ha hφb
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  have hκφ : κ ≤ ∫ g, ‖⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ‖ ∂ν := by
    have h := (hK.2 w w w w).2
    rw [hww, mul_one, mul_one] at h
    have h2 : ∫ g, ⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ ∂ν = (κ : ℂ) := h
    have h3 := norm_integral_le_integral_norm (μ := ν)
      (fun g : UJ ε' => ⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ)
    rw [h2, Complex.norm_real, Real.norm_eq_abs] at h3
    exact le_trans (le_abs_self κ) h3
  have hD : 1 / κ⁻¹ ≤ x ^ (67 * (n + 1) ^ 2) * ν.real (ball ε' 1) := by
    rw [one_div, inv_inv]
    have hnd := UnitaryDecomposition.X4.num_D (n := n) (x := x) hx16 (by linarith)
    have hνr : 0 ≤ ν.real (ball ε' 1) := measureReal_nonneg
    calc κ ≤ _ := hκφ
      _ ≤ _ := hIφ
      _ ≤ _ := mul_le_mul_of_nonneg_right hnd hνr
  have hY := UnitaryDecomposition.X4.num_Y (N := n + 1) (x := x) (by omega) (by linarith) (by push_cast; linarith)
  have hB1 : 0 < B + 1 := by linarith
  have hδ : 0 < ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹ := by positivity
  have hδ2 : ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹ ≤ 2 := by
    have h1 : (1 : ℝ) ≤ (100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2 := by
      apply one_le_pow₀
      push_cast
      nlinarith
    have := inv_le_one_of_one_le₀ h1
    linarith
  have hV := UnitaryDecomposition.X4.num_V (N := n + 1) (B := B) (x := x) (by omega) hB2 (by rw [hx]; push_cast; ring)
  have hgap100 : GapAtLeast ε lam (100 * ((n + 1 : ℕ) : ℝ) ^ 3) := by
    intro a b hab
    refine le_trans ?_ (hP.gap a b hab)
    push_cast
    nlinarith
  have hDU := hDUp (n + 1) ε lam B H π (muG ε) dπ hμ (by omega) hP.hc hDSπ hP.bd hgap100 hFdeg
  have hvol : ENNReal.ofReal dπ * muG ε {g : UJ ε | hs (umat g) ≤ 64 * ((n + 1 : ℕ) : ℝ)
      * (((n + 1 : ℕ) : ℝ) + 2 * x ^ (8 * (n + 1))) ^ 2} ≤ ENNReal.ofReal (4 * x ^ (24 * (n + 1) ^ 3)) := by
    have hsub : {g : UJ ε | hs (umat g) ≤ 64 * ((n + 1 : ℕ) : ℝ)
        * (((n + 1 : ℕ) : ℝ) + 2 * x ^ (8 * (n + 1))) ^ 2} ⊆ {g : UJ ε | hs (um g) ≤ (x ^ (10 * (n + 1))) ^ 2} := by
      intro g hg
      simp only [Set.mem_setOf_eq] at hg ⊢
      rw [← pow_mul]
      have e : 10 * (n + 1) * 2 = 20 * (n + 1) := by ring
      rw [e]
      exact le_trans hg hY
    have h1 := measure_mono (μ := muG ε) hsub
    have h2 := hVol (n + 1) ε (muG ε) hμ (by omega) _ (x ^ (10 * (n + 1))) hδ hδ2 (by positivity)
    calc ENNReal.ofReal dπ * muG ε {g : UJ ε | hs (umat g) ≤ 64 * ((n + 1 : ℕ) : ℝ)
          * (((n + 1 : ℕ) : ℝ) + 2 * x ^ (8 * (n + 1))) ^ 2}
        ≤ ENNReal.ofReal dπ * (ENNReal.ofReal ((4 * ((n + 1 : ℕ) : ℝ) * (√((n + 1 : ℕ) : ℝ) + 1)
            * x ^ (10 * (n + 1)) / ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹) ^ (2 * (n + 1) ^ 2))
            * muG ε (ball ε ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹)) := by gcongr; exact h1.trans h2
      _ = ENNReal.ofReal ((4 * ((n + 1 : ℕ) : ℝ) * (√((n + 1 : ℕ) : ℝ) + 1)
            * x ^ (10 * (n + 1)) / ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹) ^ (2 * (n + 1) ^ 2))
            * (ENNReal.ofReal dπ * muG ε (ball ε ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹)) := by ring
      _ ≤ ENNReal.ofReal ((4 * ((n + 1 : ℕ) : ℝ) * (√((n + 1 : ℕ) : ℝ) + 1)
            * x ^ (10 * (n + 1)) / ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹) ^ (2 * (n + 1) ^ 2)) * 4 :=
          by gcongr
      _ ≤ ENNReal.ofReal (x ^ (24 * (n + 1) ^ 3)) * 4 := by gcongr
      _ = ENNReal.ofReal (4 * x ^ (24 * (n + 1) ^ 3)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_comm]
  have hY1 : (1 : ℝ) ≤ 2 * x ^ (8 * (n + 1)) := by
    have : (1 : ℝ) ≤ x ^ (8 * (n + 1)) := one_le_pow₀ (by linarith)
    linarith
  have hK0 : (0 : ℝ) < 4 * x ^ (24 * (n + 1) ^ 3) := by positivity
  have hmomG : ∫⁻ g : UJ ε, ENNReal.ofReal (GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (umat g⁻¹ *ᵥ Pi.single (zi e) 1)
        * ‖⟪i w, π (umat g) v⟫_ℂ‖ ^ 2) ∂muG ε
      ≤ ENNReal.ofReal (2 * x ^ (8 * (n + 1)) / 2)
        * ∫⁻ g : UJ ε, ENNReal.ofReal (‖⟪i w, π (umat g) v⟫_ℂ‖ ^ 2) ∂muG ε := by
    have e1 : ∀ g : UJ ε, GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (umat g⁻¹ *ᵥ Pi.single (zi e) 1) = colSq (um g⁻¹) (zi e) :=
      fun g => hE2 _ _
    have e2 : 2 * x ^ (8 * (n + 1)) / 2 = x ^ (8 * (n + 1)) := by ring
    simp_rw [e1, e2]
    exact hmom
  obtain ⟨g₀, hg1, hg2⟩ := hg0 ι (Pi.single (zi e) 1) hιstd π σ (muG ε) ν dπ κ⁻¹ hUπ hUσ hFd hFdσ i hIso
    v w hv1 hw1 (2 * x ^ (8 * (n + 1))) (4 * x ^ (24 * (n + 1) ^ 3)) (x ^ (67 * (n + 1) ^ 2)) hY1 hK0
    hmomG hvol hD
  refine ⟨g₀, le_trans hg1 hY, ?_⟩
  have hg2' : 1 ≤ 4 * x ^ (67 * (n + 1) ^ 2) * (4 * x ^ (24 * (n + 1) ^ 3))
      * ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2 := hg2
  have ht0 : 0 ≤ ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ := norm_nonneg _
  have hM0 : 0 < x ^ (100 * (n + 1) ^ 3) := pow_pos hx0 _
  have elog : 100 * ((n : ℝ) + 1) ^ 3 * Real.log x = Real.log (x ^ (100 * (n + 1) ^ 3)) := by
    rw [Real.log_pow]; push_cast; ring
  rw [elog, Real.exp_neg, Real.exp_log hM0]
  have hA0 : 0 ≤ x ^ (67 * (n + 1) ^ 2) := pow_nonneg hx0.le _
  have hC0 : 0 ≤ x ^ (24 * (n + 1) ^ 3) := pow_nonneg hx0.le _
  have hnat : 1 + 67 * (n + 1) ^ 2 + 24 * (n + 1) ^ 3 ≤ 100 * (n + 1) ^ 3 * 2 := by
    have h1 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    linarith
  have hbig : 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) ≤ (x ^ (100 * (n + 1) ^ 3)) ^ 2 := by
    rw [← pow_mul]
    calc 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3)
        ≤ x * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx16 hA0) hC0
      _ = x ^ (1 + 67 * (n + 1) ^ 2 + 24 * (n + 1) ^ 3) := by rw [pow_add, pow_add, pow_one]
      _ ≤ x ^ (100 * (n + 1) ^ 3 * 2) := pow_le_pow_right₀ (by linarith) hnat
  by_contra hlt
  push_neg at hlt
  have hsq : ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2 < ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2 :=
    pow_lt_pow_left₀ hlt ht0 (by norm_num)
  have hp : 0 < 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) :=
    mul_pos (mul_pos (by norm_num) (pow_pos hx0 _)) (pow_pos hx0 _)
  have s1 := mul_lt_mul_of_pos_left hsq hp
  have s2 : 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) * ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2
      ≤ (x ^ (100 * (n + 1) ^ 3)) ^ 2 * ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2 :=
    mul_le_mul_of_nonneg_right hbig (sq_nonneg _)
  have s3 : (x ^ (100 * (n + 1) ^ 3)) ^ 2 * ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hM0.ne', one_pow]
  have s4 : 4 * x ^ (67 * (n + 1) ^ 2) * (4 * x ^ (24 * (n + 1) ^ 3))
      * ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2
      = 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3)
      * ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2 := by ring
  rw [s4] at hg2'
  exact absurd (lt_of_le_of_lt hg2' (lt_of_lt_of_le s1 (s2.trans s3.le))) (lt_irrefl 1)

theorem bigProjP : MomentP → Analysis → BigProjP := bigProjP_of PositivityTheory.UnitaryDecomposition.X4.g0 PositivityTheory.UnitaryDecomposition.X4.emb

end PositivityTheory.RgHe.A.Pf
