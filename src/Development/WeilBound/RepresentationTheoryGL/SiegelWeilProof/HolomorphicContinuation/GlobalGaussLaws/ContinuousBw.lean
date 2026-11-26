module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellT
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfolding
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FibFact
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositivityTheory.Rg.Sw.Glob.Fib

variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X]
  [BorelSpace X]

theorem fib_meas (μ : Measure X) [μ.IsAddRightInvariant] (π : X →+ (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) →+ X) (hπs : ∀ u, π (s u) = u) (g : X → ℝ≥0∞) (hg : Measurable g)
    (hgs : ∀ z u, g (z + s u) = g z)
    (hloc : ∀ K : Set (Fin m → Fin n → ℂ), IsCompact K → ∫⁻ z, K.indicator 1 (π z) * g z ∂μ ≠ ∞) :
    ∃ c : ℝ≥0, (μ.withDensity g).map π = c • (volume : Measure (Fin m → Fin n → ℂ)) := by
  set ν : Measure (Fin m → Fin n → ℂ) := (μ.withDensity g).map π with hν
  have hπm : Measurable π := hπ.measurable
  have hint : ∀ a : (Fin m → Fin n → ℂ) → ℝ≥0∞, Measurable a → ∫⁻ u, a u ∂ν = ∫⁻ z, a (π z) * g z ∂μ := by
    intro a ha
    rw [hν, lintegral_map ha hπm]
    have e := lintegral_withDensity_eq_lintegral_mul μ hg (ha.comp hπm)
    simp only [Function.comp_def] at e
    rw [e]
    congr 1; ext z; simp [mul_comm]
  have hinv : ν.IsAddLeftInvariant := by
    refine ⟨fun u => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add u) hA, ← lintegral_indicator_one (measurable_const_add u hA),
      ← lintegral_indicator_one hA, hint _ (measurable_one.indicator (measurable_const_add u hA)),
      hint _ (measurable_one.indicator hA)]
    have key : ∀ z, ((fun x => u + x) ⁻¹' A).indicator 1 (π z) * g z =
        (fun z => A.indicator 1 (π z) * g z) (z + s u) := by
      intro z
      simp only [map_add (f := _), hπs, hgs]
      congr 1
      by_cases h : u + π z ∈ A
      · simp [Set.indicator, h, add_comm]
      · simp [Set.indicator, h, add_comm]
    simp_rw [key]
    exact lintegral_add_right_eq_self (fun z => A.indicator 1 (π z) * g z) (s u)
  have hfc : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [← lintegral_indicator_one hK.measurableSet, hint _ (measurable_one.indicator hK.measurableSet)]
    exact (hloc K hK).lt_top
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact ⟨Measure.addHaarScalarFactor ν volume, Measure.isAddLeftInvariant_eq_smul ν volume⟩

end PositivityTheory.Rg.Sw.Glob.Fib
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PsiInnerSIns
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousInsT
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PsiEqOfFin
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR thetaC eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

variable {D : D7}


set_option synthInstance.maxHeartbeats 400000 in
theorem incl_trA (z : AE D) : algebraMap (AF D.host.F) (AE D) (trA z) = z + cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [trA]
  | tmul a e =>
    simp only [trA]
    rw [GlobalTheory.SplitAdeleTrace.trace_baseChange_tmul (AF D.host.F) a e]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h : (Algebra.trace D.host.F D.host.E e : D.host.E) = e + star e := GlobalTheory.TraceAddStar.trace_eq_add_star e
    calc (a * algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e)) ⊗ₜ[D.host.F] (1 : D.host.E)
        = a ⊗ₜ[D.host.F] ((Algebra.trace D.host.F D.host.E e : D.host.F) : D.host.E) := by
          rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]; rfl
      _ = a ⊗ₜ[D.host.F] e + cA D (a ⊗ₜ[D.host.F] e) := by
          rw [h, TensorProduct.tmul_add]; rfl
  | add x y hx hy =>
    simp only [trA, map_add (f := _)] at hx hy ⊢
    rw [hx, hy]; abel


set_option synthInstance.maxHeartbeats 400000 in
theorem psi_eq_of_fin {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) (a : AF D.host.F) (ha : finPart D (algebraMap (AF D.host.F) (AE D) a) = 0) :
    ψ a = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, (l τ : ℂ) * psiT D τ (algebraMap (AF D.host.F) (AE D) a)) := by
  have hsnd : sndA D.host.F a = 0 := by
    apply Algebra.TensorProduct.includeLeft_injective (S := Af D.host.F) (algebraMap D.host.F D.host.E).injective
    rw [map_zero]
    exact ha
  have ha' : a = pairA D.host.F (fstA D.host.F a) 0 := Prod.ext rfl hsnd
  have h1 : ψ a = psiInf D.host.F ψ (fstA D.host.F a) := by
    conv_lhs => rw [ha']
    rfl
  rw [h1, hl, eq_thetaC D hθ]
  rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem psi_trA_tau {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) (τ : D.what₂.Tau) (z : AE D) (hz : ∀ τ', τ' ≠ τ → psiT D τ' z = 0)
    (hzf : finPart D z = 0) :
    ψ (trA z) = Complex.exp (Complex.I * ((4 * Real.pi * l τ : ℝ) : ℂ) * ((psiT D τ z).re : ℂ)) := by
  have hfin : finPart D (algebraMap (AF D.host.F) (AE D) (trA z)) = 0 := by
    rw [incl_trA, RingHom.map_add (f := _), hzf, cA, Formalism.IndefR.Eqv.finPart_sigR, hzf, RingHom.map_zero, add_zero]
  rw [psi_eq_of_fin hθ hl _ hfin, incl_trA]
  have hs : ∑ τ', (l τ' : ℂ) * psiT D τ' (z + cA D z) = (l τ : ℂ) * (2 * ((psiT D τ z).re : ℂ)) := by
    rw [Finset.sum_eq_single τ]
    · rw [RingHom.map_add (f := _), cA, psiT_sigR, Complex.add_conj]; push_cast; ring
    · intro τ' _ hne
      rw [RingHom.map_add (f := _), cA, psiT_sigR, hz τ' hne, map_zero, add_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ τ) h
  rw [hs]
  congr 1
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.FTP
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR psiT_inclR thetaC eq_thetaC glueA splitInv psiT_glueA finPart_glueA ae_ext'
  continuous_glueA continuous_splitInv continuous_psiT)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

open Classical

variable {D : D7} {m n : ℕ}

def insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then v i j else 0) 0

theorem psiT_insT (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    psiT D τ' (insT τ v i j) = if τ' = τ then v i j else 0 := psiT_glueA D τ' _ 0

theorem finPart_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    finPart D (insT τ v i j) = 0 := finPart_glueA D _ 0

theorem insT_add (τ : D.what₂.Tau) (v w : Matrix (Fin m) (Fin n) ℂ) : insT (D := D) τ (v + w) = insT τ v + insT τ w := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [Matrix.add_apply, RingHom.map_add (f := _), psiT_insT, psiT_insT, psiT_insT]
    split_ifs <;> simp
  · rw [Matrix.add_apply, RingHom.map_add (f := _), finPart_insT, finPart_insT, finPart_insT, add_zero]

theorem insT_zero (τ : D.what₂.Tau) : insT (D := D) (m := m) (n := n) τ 0 = 0 := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [psiT_insT, Matrix.zero_apply, Matrix.zero_apply, RingHom.map_zero]
    split_ifs <;> rfl
  · rw [finPart_insT, Matrix.zero_apply, RingHom.map_zero]

theorem continuous_insT (τ : D.what₂.Tau) : Continuous (insT (D := D) (m := m) (n := n) τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D 0).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

theorem compAt_insT {θ : InfFam D} (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) :
    compAt θ τ' (insT τ v) = if τ' = τ then v else 0 := by
  rw [eq_thetaC D hθ]
  ext i j
  show psiT D τ' (insT τ v i j) = _
  rw [psiT_insT]
  split_ifs <;> rfl

theorem finMap_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : (insT (D := D) τ v).map (finPart D) = 0 := by
  ext i j; exact finPart_insT τ v i j

def sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →+ Mx D m n where
  toFun u := insT τ (fr * Matrix.of u)
  map_zero' := by simp [insT_zero]
  map_add' u v := by
    rw [show Matrix.of (u + v) = Matrix.of u + Matrix.of v from rfl, Matrix.mul_add, insT_add]


set_option synthInstance.maxHeartbeats 400000 in
def piF (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : Mx D m n →+ (Fin m → Fin n → ℂ) where
  toFun y := Matrix.of.symm (fr⁻¹ * compAt θ τ y)
  map_zero' := by
    ext i j
    simp [compAt]
  map_add' y y' := by
    have h : compAt θ τ (y + y') = compAt θ τ y + compAt θ τ y' := by
      ext i j; simp only [compAt, Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _)]
    ext i j
    simp only [h, Matrix.mul_add]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem piF_sIns {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ}
    (hfr : IsUnit fr.det) (u : Fin m → Fin n → ℂ) : piF θ τ fr (sIns (D := D) τ fr u) = u := by
  show Matrix.of.symm (fr⁻¹ * compAt θ τ (insT τ (fr * Matrix.of u))) = u
  rw [compAt_insT hθ, if_pos rfl, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr, Matrix.one_mul]
  rfl

theorem continuous_piF {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (piF (n := n) θ τ fr) := by
  have h : Continuous fun y : Mx D m n => (fr⁻¹ * compAt θ τ y : Matrix (Fin m) (Fin n) ℂ) := by
    refine Continuous.matrix_mul continuous_const ?_
    rw [eq_thetaC D hθ]
    exact Continuous.matrix_map continuous_id (Formalism.IndefR.Eqv.continuous_psiT (D := D) τ)
  exact h

theorem continuous_sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (sIns (D := D) (n := n) τ fr) := by
  show Continuous fun u : Fin m → Fin n → ℂ => insT τ (fr * Matrix.of u)
  exact (continuous_insT τ).comp (Continuous.matrix_mul continuous_const continuous_id)

end PositivityTheory.Rg.Sw.Glob.FTP
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR psiT_inclR thetaC eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

open Classical

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
theorem map_inner (V : HSp D) (τ : D.what₂.Tau) (x y : Mx D V.rank n) :
    (inner V x y).map (psiT D τ) = (x.map (psiT D τ))ᴴ * (gramAt D V τ * y.map (psiT D τ)) := by
  have h1 : (adj x).map (psiT D τ) = (x.map (psiT D τ))ᴴ := by
    ext i j
    simp only [adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    exact psiT_sigR D τ (x j i)
  have h2 : (gA V).map (psiT D τ) = gramAt D V τ := by
    ext i j
    simp only [gA, rat, Matrix.map_apply, gramAt]
    exact psiT_inclR D τ _
  show (adj x * (gA V * y)).map (psiT D τ) = _
  rw [Matrix.map_mul, Matrix.map_mul, h1, h2]

set_option synthInstance.maxHeartbeats 400000 in
theorem psiT_trace {a : ℕ} (τ : D.what₂.Tau) (M : Matrix (Fin a) (Fin a) (AE D)) :
    psiT D τ (Matrix.trace M) = Matrix.trace (M.map (psiT D τ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

set_option synthInstance.maxHeartbeats 400000 in
theorem finPart_trace {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D)) :
    finPart D (Matrix.trace M) = Matrix.trace (M.map (finPart D)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

set_option synthInstance.maxHeartbeats 400000 in
theorem finMap_inner (V : HSp D) (x y : Mx D V.rank n) (hy : y.map (finPart D) = 0) :
    (inner V x y).map (finPart D) = 0 := by
  show (adj x * (gA V * y)).map (finPart D) = 0
  rw [Matrix.map_mul, Matrix.map_mul, hy, Matrix.mul_zero, Matrix.mul_zero]


set_option synthInstance.maxHeartbeats 400000 in
theorem psi_inner_sIns {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    (x : Mx D V.rank n) (u : Fin V.rank → Fin n → ℂ) :
    ψ (trA (Matrix.trace (inner V x (sIns τ fr u)))) =
      Complex.exp (Complex.I * ((2 * tLoc l τ : ℝ) : ℂ) *
        (((Matrix.of (piF θ τ fr x))ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℂ)) := by
  have hins : ∀ τ', (sIns (D := D) τ fr u).map (psiT D τ') = if τ' = τ then fr * Matrix.of u else 0 := by
    intro τ'
    have := compAt_insT (D := D) hθ τ τ' (fr * Matrix.of u)
    rw [eq_thetaC D hθ] at this
    exact this
  rw [psi_trA_tau hθ hl τ]
  · congr 2
    · simp only [tLoc]; push_cast; ring
    · rw [psiT_trace, map_inner, hins, if_pos rfl]
      congr 2
      obtain ⟨hdet, hg, -⟩ := hfr
      have hx : Matrix.of (piF θ τ fr x) = fr⁻¹ * x.map (psiT D τ) := by
        rw [eq_thetaC D hθ] ; rfl
      rw [hx, ← hg, Matrix.conjTranspose_mul]
      have hinv : (fr⁻¹)ᴴ * frᴴ = 1 := by
        rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (fr⁻¹)ᴴ frᴴ, hinv, Matrix.one_mul]
  · intro τ' hne
    rw [psiT_trace, map_inner, hins, if_neg hne, Matrix.mul_zero, Matrix.mul_zero, Matrix.trace_zero]
  · rw [finPart_trace, finMap_inner V x (sIns τ fr u) (finMap_insT τ (fr * Matrix.of u)), Matrix.trace_zero]

end PositivityTheory.Rg.Sw.Glob.FTP
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (a b : Mx D m n) :
    compAt θ τ (a + b) = compAt θ τ a + compAt θ τ b := by
  ext i j; simp only [compAt, Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _)]

set_option synthInstance.maxHeartbeats 400000 in
theorem finMap_add (a b : Mx D m n) : (a + b).map (finPart D) = a.map (finPart D) + b.map (finPart D) := by
  ext i j; simp only [Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _)]

theorem away_add {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ) (y : Mx D m n) (u : Fin m → Fin n → ℂ) :
    Ψ (y + sIns τ fr u) = Ψ y := by
  refine hΨ.1 _ _ (fun τ' hne => ?_) ?_
  · rw [compAt_add, show sIns (D := D) τ fr u = insT τ (fr * Matrix.of u) from rfl, compAt_insT hθ, ite_eq_right hne,
      add_zero]
  · rw [finMap_add, show sIns (D := D) τ fr u = insT τ (fr * Matrix.of u) from rfl, finMap_insT, add_zero]

theorem cont_of_away {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ) : Continuous Ψ := by
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) 1 one_pos
  have hmem := hΨ.2 (gs 1) ⟨S, funext hS⟩
  have hc := GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ ⟨_, hmem⟩
  have hg : Continuous fun x : Mx D m n => gs (n := n) 1 (fr⁻¹ * compAt θ τ x) := by
    have h1 : Continuous fun x : Mx D m n => (S (piF θ τ fr x)) := S.continuous.comp (continuous_piF hθ τ fr)
    refine h1.congr fun x => ?_
    rw [hS]; rfl
  have hne : ∀ x : Mx D m n, gs (n := n) 1 (fr⁻¹ * compAt θ τ x) ≠ 0 := fun x => Complex.exp_ne_zero _
  have e : Ψ = fun x => tens θ τ fr (gs 1) Ψ x / gs (n := n) 1 (fr⁻¹ * compAt θ τ x) := by
    funext x
    simp only [tens]
    field_simp [hne x]
  rw [e]
  exact hc.div hg hne

def Bw (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) : ℂ :=
  Ψ y * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x (y - sIns τ fr (piF θ τ fr y)))))

theorem Bw_add {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hdet : IsUnit fr.det) (ψ : AddChar (AF D.host.F) ℂ) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    (x y : Mx D V.rank n) (u : Fin V.rank → Fin n → ℂ) :
    Bw ψ V θ τ fr Ψ x (y + sIns τ fr u) = Bw ψ V θ τ fr Ψ x y := by
  have e : y + sIns τ fr u - sIns τ fr (piF θ τ fr (y + sIns τ fr u)) = y - sIns τ fr (piF θ τ fr y) := by
    rw [map_add (piF θ τ fr), piF_sIns hθ τ hdet, map_add (sIns τ fr)]
    abel
  unfold Bw
  rw [away_add hθ hΨ, e]

set_option synthInstance.maxHeartbeats 800000 in
theorem continuous_Bw {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) (x : Mx D V.rank n) :
    Continuous (Bw ψ V θ τ fr Ψ x) := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : ContinuousSub (Mx D V.rank n) := inferInstance
  refine (cont_of_away hθ hΨ).mul ?_
  have htr : Continuous (trA (D := D)) := by
    have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    exact IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hinner : Continuous (fun y : Mx D V.rank n => GlobalTheory.StdUnn.inner V x y) := by
    unfold GlobalTheory.StdUnn.inner
    exact continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id)
  have h := hψ.1.comp (htr.comp hinner.matrix_trace)
  exact h.comp (continuous_id.sub ((continuous_sIns τ fr).comp (continuous_piF hθ τ fr)))

theorem norm_Bw {V : HSp D} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) :
    ‖Bw ψ V θ τ fr Ψ x y‖ = ‖Ψ y‖ := by
  unfold Bw; rw [norm_mul, hψ.2.1, mul_one]

end PositivityTheory.Rg.Sw.Glob.FTH
