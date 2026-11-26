module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousBw

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtNeg
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.InvEqWww
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtSubSIns
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousKer
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SchDecay
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IntegrableRho
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FtLocEqKer
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

def ker (ε : Fin m → Bool) (t : ℝ) (v u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ) * (((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℂ))

theorem ftLoc_eq_ker (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (v : Fin m → Fin n → ℂ) :
    ftLoc ε t f v = ∫ u, f u * ker ε t v u := rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem integrand_eq {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) :
    tens θ τ fr f Ψ y * ψ (trA (Matrix.trace (inner V x y))) =
      (f (piF θ τ fr y) * ker ε (tLoc l τ) (piF θ τ fr x) (piF θ τ fr y)) * Bw ψ V θ τ fr Ψ x y := by
  have hsplit : inner V x y = inner V x (y - sIns τ fr (piF θ τ fr y)) + inner V x (sIns τ fr (piF θ τ fr y)) := by
    rw [← GlobalTheory.CompanionTheory.EisCovar.Weyl.inner_add_right, sub_add_cancel]
  have hψ2 : ψ (trA (Matrix.trace (inner V x y))) =
      ψ (trA (Matrix.trace (inner V x (y - sIns τ fr (piF θ τ fr y))))) *
        ψ (trA (Matrix.trace (inner V x (sIns τ fr (piF θ τ fr y))))) := by
    rw [hsplit, Matrix.trace_add, GlobalTheory.CompanionTheory.EisCovar.Weyl.trA_add, AddChar.map_add_eq_mul]
  rw [hψ2, psi_inner_sIns hθ hl hfr]
  have hp : (fr⁻¹ * compAt θ τ y : Matrix (Fin V.rank) (Fin n) ℂ) = piF θ τ fr y := rfl
  unfold Bw tens ker
  rw [hp]
  ring

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def rr (m n : ℕ) : ℝ := ((Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 : ℕ) : ℝ)

theorem integrable_rho : Integrable (fun u : Fin m → Fin n → ℂ => (1 + ‖u‖) ^ (-rr m n)) := by
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  apply integrable_one_add_norm
  unfold rr; push_cast; linarith


set_option synthInstance.maxHeartbeats 400000 in
theorem hloc_away {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    (K : Set (Fin m → Fin n → ℂ)) (hK : IsCompact K) :
    ∫⁻ z, K.indicator 1 (piF θ τ fr z) * ‖Ψ z‖ₑ ∂μ ≠ ∞ := by
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) 1 one_pos
  have hmem := hΨ.2 (gs 1) ⟨S, funext hS⟩
  have hI := GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ μ ⟨_, hmem⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hgc : Continuous fun u : Fin m → Fin n → ℂ => ‖gs (n := n) 1 u‖ :=
    continuous_norm.comp (S.continuous.congr fun u => hS u)
  obtain ⟨u0, -, hu0⟩ := hK.exists_isMinOn hne hgc.continuousOn
  have hδ : 0 < ‖gs (n := n) 1 u0‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hle : ∀ z, K.indicator 1 (piF θ τ fr z) * ‖Ψ z‖ₑ ≤
      ENNReal.ofReal (‖gs (n := n) 1 u0‖)⁻¹ * ‖tens θ τ fr (gs 1) Ψ z‖ₑ := by
    intro z
    by_cases hz : piF θ τ fr z ∈ K
    · rw [Set.indicator_of_mem hz, Pi.one_apply, one_mul]
      have h1 : tens θ τ fr (gs 1) Ψ z = gs (n := n) 1 (piF θ τ fr z) * Ψ z := rfl
      rw [h1, enorm_mul, ← mul_assoc]
      conv_lhs => rw [← one_mul ‖Ψ z‖ₑ]
      gcongr
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [← div_eq_inv_mul, one_le_div hδ]
      exact hu0 hz
    · rw [Set.indicator_of_notMem hz, zero_mul]; exact zero_le
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.hasFiniteIntegral.ne


set_option synthInstance.maxHeartbeats 800000 in
theorem hint_int {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure]
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (x : Mx D V.rank n) :
    Integrable (fun z => (1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n) * ‖Bw ψ V θ τ fr Ψ x z‖) μ := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hΨc := cont_of_away hθ hΨ
  have hπ := continuous_piF (n := n) hθ τ fr
  obtain ⟨c, hc⟩ := Fib.fib_meas μ (piF θ τ fr) hπ (sIns τ fr) (piF_sIns hθ τ hdet) (fun z => ‖Ψ z‖ₑ)
    hΨc.enorm.measurable (fun z u => by simp only [away_add hθ hΨ]) (hloc_away hθ μ hΨ)
  have hρc : Continuous fun u : Fin V.rank → Fin n → ℂ => (1 + ‖u‖) ^ (-rr V.rank n) :=
    (continuous_const.add continuous_norm).rpow_const fun u => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg u)).ne'
  refine ⟨((hρc.comp hπ).mul (continuous_Bw hθ hψ hΨ x).norm).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have e1 : ∀ z, ‖(1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n) * ‖Bw ψ V θ τ fr Ψ x z‖‖ₑ =
      ENNReal.ofReal ((1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n)) * ‖Ψ z‖ₑ := by
    intro z
    rw [enorm_mul, norm_Bw hψ, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm (Ψ z), Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      enorm_norm, ofReal_norm_eq_enorm]
  simp_rw [e1]
  have e2 : ∫⁻ z, ENNReal.ofReal ((1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n)) * ‖Ψ z‖ₑ ∂μ =
      ∫⁻ u, ENNReal.ofReal ((1 + ‖u‖) ^ (-rr V.rank n)) ∂((μ.withDensity fun z => ‖Ψ z‖ₑ).map (piF θ τ fr)) := by
    rw [lintegral_map (f := fun u : Fin V.rank → Fin n → ℂ => ENNReal.ofReal ((1 + ‖u‖) ^ (-rr V.rank n)))
      (ENNReal.measurable_ofReal.comp hρc.measurable) hπ.measurable]
    have e := lintegral_withDensity_eq_lintegral_mul μ hΨc.enorm.measurable
      ((ENNReal.measurable_ofReal.comp hρc.measurable).comp hπ.measurable)
    simp only [Function.comp_def] at e
    rw [e]
    congr 1; ext z; simp [mul_comm]
  rw [e2, hc, lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have hI := (integrable_rho (m := V.rank) (n := n)).hasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) hI
  congr 1; ext u
  rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def Pk (μ : Measure (Mx D m n)) (π : Mx D m n → (Fin m → Fin n → ℂ)) (B : Mx D m n → ℂ) (κ : ℂ) : Prop :=
  ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a → (∃ C, ∀ u, ‖a u‖ ≤ C * (1 + ‖u‖) ^ (-rr m n)) →
    ∫ z, a (π z) * B z ∂μ = κ * ∫ u, a u

def kap (μ : Measure (Mx D m n)) (π : Mx D m n → (Fin m → Fin n → ℂ)) (B : Mx D m n → ℂ) : ℂ :=
  Classical.epsilon (Pk μ π B)

set_option synthInstance.maxHeartbeats 800000 in
theorem kap_spec {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure]
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (x : Mx D V.rank n) :
    Pk μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x) (kap μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x)) := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  apply Classical.epsilon_spec
  have hρc : Continuous fun u : Fin V.rank → Fin n → ℂ => (1 + ‖u‖) ^ (-rr V.rank n) :=
    (continuous_const.add continuous_norm).rpow_const fun u => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg u)).ne'
  exact LocCellT.tauFact μ (piF θ τ fr) (continuous_piF hθ τ fr) (sIns τ fr)
    (fun z u => by rw [map_add (piF θ τ fr), piF_sIns hθ τ hdet]) (Bw ψ V θ τ fr Ψ x)
    (continuous_Bw hθ hψ hΨ x).measurable (fun z u => Bw_add hθ hdet ψ hΨ x z u)
    (fun u => (1 + ‖u‖) ^ (-rr V.rank n)) hρc (fun u => Real.rpow_pos_of_pos (by positivity) _)
    (hint_int hθ hdet μ hΨ hψ x)

theorem sch_decay (f : (Fin m → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    ∃ C, ∀ u, ‖f u‖ ≤ C * (1 + ‖u‖) ^ (-rr m n) := by
  obtain ⟨S, rfl⟩ := hf
  set k : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hk
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (Fin m → Fin n → ℂ) ℂ) S, fun u => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl S u
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖u‖) ^ k := by positivity
  have e : (1 + ‖u‖) ^ (-rr m n) = ((1 + ‖u‖) ^ k)⁻¹ := by
    rw [rr, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact h

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

theorem norm_ker (ε : Fin m → Bool) (t : ℝ) (v u : Fin m → Fin n → ℂ) : ‖ker ε t v u‖ = 1 := by
  unfold ker
  rw [show Complex.I * ((2 * t : ℝ) : ℂ) * ((((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℝ) : ℂ) =
      ((2 * t * ((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_ker (ε : Fin m → Bool) (t : ℝ) (v : Fin m → Fin n → ℂ) : Continuous (ker ε t v) := by
  unfold ker
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp ?_)))
  have h2 : Continuous fun u : Fin m → Fin n → ℂ => Matrix.of u := continuous_id
  have h : Continuous fun u : Fin m → Fin n → ℂ => ((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u) :=
    continuous_const.matrix_mul h2
  exact h.matrix_trace

def Aw (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (μ : Measure (Mx D V.rank n)) (Ψ : Mx D V.rank n → ℂ) :
    Mx D V.rank n → ℂ :=
  fun x => kap μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x)


set_option synthInstance.maxHeartbeats 400000 in
theorem weyl_tens {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {l : D.what₂.Tau → ℝ} (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr) {χ : (AE D)ˣ →* Circle}
    (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure] {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) (Ψ : Mx D V.rank n → ℂ)
    (hΨ : AwayCls θ τ fr Ψ) (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 =
      tens θ τ fr (fun u => 1 * ftLoc ε (tLoc l τ) f u) (Aw ψ V θ τ fr μ Ψ) := by
  funext x
  rw [hω.weyl w hw]
  have e1 : ∀ y, (⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ : schwartzA θ V.rank n).1 y * ψ (trA (Matrix.trace (inner V x y))) =
      (fun u => f u * ker ε (tLoc l τ) (piF θ τ fr x) u) (piF θ τ fr y) * Bw ψ V θ τ fr Ψ x y :=
    fun y => integrand_eq hθ hl hfr f Ψ x y
  simp_rw [e1]
  obtain ⟨S, hS⟩ := hf
  have hfc : Continuous f := hS ▸ S.continuous
  obtain ⟨C, hC⟩ := sch_decay f ⟨S, hS⟩
  have hk := kap_spec hθ hfr.1 μ hΨ hψ x (fun u => f u * ker ε (tLoc l τ) (piF θ τ fr x) u)
    ((hfc.mul (continuous_ker ε (tLoc l τ) (piF θ τ fr x))).measurable)
    ⟨C, fun u => by rw [norm_mul, norm_ker, mul_one]; exact hC u⟩
  rw [hk]
  simp only [tens, Aw, ftLoc_eq_ker, one_mul]
  rw [mul_comm]
  rfl

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC mat_ext psiT_sigR finPart_sigR)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
theorem compAt_sub_sIns {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    (hdet : IsUnit fr.det) (y : Mx D m n) :
    (y - sIns τ fr (piF θ τ fr y)).map (psiT D τ) = 0 := by
  have hp : Matrix.of (piF θ τ fr y) = fr⁻¹ * compAt θ τ y := rfl
  rw [Matrix.map_sub (psiT D τ) (fun a b => map_sub (psiT D τ) a b), ← PlaceFactsH.compAt_eq_psiT hθ,
    ← PlaceFactsH.compAt_eq_psiT hθ, show sIns (D := D) τ fr (piF θ τ fr y) = insT τ (fr * Matrix.of (piF θ τ fr y)) from rfl,
    compAt_insT hθ, if_pos rfl, hp, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, sub_self]


set_option synthInstance.maxHeartbeats 400000 in
theorem inner_away {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} (x x' z : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D))
    (hz : z.map (psiT D τ) = 0) : inner V x z = inner V x' z := by
  apply mat_ext D
  · intro τ''
    rw [map_inner, map_inner]
    by_cases h : τ'' = τ
    · subst h; rw [hz, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_zero]
    · have := hx τ'' h
      rw [eq_thetaC D hθ] at this
      change x.map (psiT D τ'') = x'.map (psiT D τ'') at this
      rw [this]
  · have ha : (adj x).map (finPart D) = (adj x').map (finPart D) := by
      ext i j
      simp only [adj, Matrix.map_apply, Matrix.transpose_apply, cA]
      rw [finPart_sigR, finPart_sigR]
      congr 1
      exact congrFun (congrFun hf j) i
    show (adj x * (gA V * z)).map (finPart D) = (adj x' * (gA V * z)).map (finPart D)
    rw [Matrix.map_mul, ha, ← Matrix.map_mul]

end PositivityTheory.Rg.Sw.Glob.FTH
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

open PositivityTheory.Rg.Sw.Glob.FTP PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Classical

variable {D : D7} {n m : ℕ}

theorem Aw_away {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D V.rank n)) (Ψ : Mx D V.rank n → ℂ) (x x' : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D)) :
    Aw ψ V θ τ fr μ Ψ x = Aw ψ V θ τ fr μ Ψ x' := by
  have e : Bw ψ V θ τ fr Ψ x = Bw ψ V θ τ fr Ψ x' := by
    funext y
    unfold Bw
    rw [inner_away hθ x x' _ hx hf (compAt_sub_sIns hθ hdet y)]
  unfold Aw
  rw [e]

set_option maxHeartbeats 800000 in
theorem mat_ww (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : mat (w * w) = blk4 (-1) 0 0 (-1) := by
  rw [mat_mul', hw, submatrix_fromBlocks_mul]
  simp

set_option maxHeartbeats 800000 in
theorem inv_eq_www (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : w⁻¹ = w * w * w := by
  apply mat_inj
  rw [GlobalTheory.CompanionTheory.EisCovar.Weyl.mat_inv_eq w hw, mat_mul', mat_ww w hw, hw, submatrix_fromBlocks_mul]
  simp

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Classical

variable {D : D7} {n m : ℕ}

set_option maxHeartbeats 800000 in
theorem ww_act {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) :
    ∃ c₀ : ℂ, ∀ (Φ : schwartzA θ V.rank n) x, (ω (w * w) Φ).1 x = c₀ * Φ.1 (-x) := by
  refine ⟨(χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin n) (AE D))) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin n) (AE D)))) ((V.rank : ℂ) / 2), fun Φ x => ?_⟩
  have hm : mat (w * w) = blk4 (-1 : GL (Fin n) (AE D)).1 0 0 (adj ((-1 : GL (Fin n) (AE D))⁻¹).1) := by
    rw [mat_ww w hw, inv_neg_one, Units.val_neg, Units.val_one, adj_neg, adj_one]
  rw [hω.levi (w * w) (-1) hm Φ x]
  congr 2
  rw [Units.val_neg, Units.val_one]
  exact congrArg _ ((Matrix.mul_neg x 1).trans (by rw [Matrix.mul_one]))

set_option synthInstance.maxHeartbeats 400000 in
theorem compAt_neg (θ : InfFam D) (τ : D.what₂.Tau) (x : Mx D m n) : compAt θ τ (-x) = -compAt θ τ x := by
  ext i j; simp only [compAt, Matrix.map_apply, Matrix.neg_apply, RingHom.map_neg]

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open Classical

set_option synthInstance.maxHeartbeats 400000 in
theorem fTfact : FTfact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι ctx w hw
  have hθ := ctx.hθ
  have hψ := ctx.hψ
  have hl := ctx.hl
  have hfr := ctx.hfr
  have hω := ctx.hω
  obtain ⟨𝓕, hcov⟩ := ctx.hμ
  have : μ.IsAddHaarMeasure := hcov.1
  have ht : tLoc l τ ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (lNe D ψ θ l hψ hθ hl τ)
  have hmt : -tLoc l τ ≠ 0 := neg_ne_zero.2 ht
  obtain ⟨c₀, hc₀⟩ := FTH.ww_act hω w hw
  refine ⟨1, FTH.Aw ψ V θ τ fr μ, fun Ψ x => c₀ * FTH.Aw ψ V θ τ fr μ Ψ (-x), one_ne_zero, fun Ψ hΨ => ?_⟩
  have hW : ∀ f (hf : IsSch f), (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 =
      tens θ τ fr (fun u => 1 * ftLoc ε (tLoc l τ) f u) (FTH.Aw ψ V θ τ fr μ Ψ) :=
    fun f hf => FTH.weyl_tens hθ hψ hl hfr μ hω w hw Ψ hΨ f hf
  have hWi : ∀ f (hf : IsSch f), (ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 =
      tens θ τ fr (fun u => (1 : ℂ)⁻¹ * ftLoc ε (-tLoc l τ) f u) (fun x => c₀ * FTH.Aw ψ V θ τ fr μ Ψ (-x)) := by
    intro f hf
    rw [FTH.inv_eq_www w hw, map_mul]
    funext x
    rw [Module.End.mul_apply, hc₀, congrFun (hW f hf) (-x)]
    simp only [tens, FTH.compAt_neg, Matrix.mul_neg, inv_one, one_mul]
    have h := FTD.ftLoc_neg ε (tLoc l τ) f (fr⁻¹ * compAt θ τ x)
    erw [h]
    ring
  have hneg : ∀ x x' : Mx D V.rank n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') →
      x.map (finPart D) = x'.map (finPart D) →
      (∀ τ', τ' ≠ τ → compAt θ τ' (-x) = compAt θ τ' (-x')) ∧ (-x).map (finPart D) = (-x').map (finPart D) := by
    intro x x' hx hf
    refine ⟨fun τ' h => by rw [FTH.compAt_neg, FTH.compAt_neg, hx τ' h], ?_⟩
    ext i j
    have := congrFun (congrFun hf i) j
    simp only [Matrix.map_apply, Matrix.neg_apply, RingHom.map_neg] at this ⊢
    rw [this]
  refine ⟨⟨fun x x' hx hf => FTH.Aw_away hθ hfr.1 ψ μ Ψ x x' hx hf, fun g hg => ?_⟩,
    ⟨fun x x' hx hf => ?_, fun g hg => ?_⟩, fun f hf => ⟨FTD.isSch_ftLoc ε _ ht 1 f hf,
      FTD.isSch_ftLoc ε _ hmt (1 : ℂ)⁻¹ f hf, hW f hf, hWi f hf⟩⟩
  · obtain ⟨f, hf, hfg⟩ := FTD.ftLoc_surj ε (tLoc l τ) ht g hg
    have e : tens θ τ fr g (FTH.Aw ψ V θ τ fr μ Ψ) = (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 := by
      rw [hW f hf, ← hfg]; simp only [one_mul]
    rw [e]; exact (ω w _).2
  · obtain ⟨h1, h2⟩ := hneg x x' hx hf
    show c₀ * FTH.Aw ψ V θ τ fr μ Ψ (-x) = c₀ * FTH.Aw ψ V θ τ fr μ Ψ (-x')
    rw [FTH.Aw_away hθ hfr.1 ψ μ Ψ (-x) (-x') h1 h2]
  · obtain ⟨f, hf, hfg⟩ := FTD.ftLoc_surj ε (-tLoc l τ) hmt g hg
    have e : tens θ τ fr g (fun x => c₀ * FTH.Aw ψ V θ τ fr μ Ψ (-x)) = (ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 := by
      rw [hWi f hf, ← hfg]; simp only [inv_one, one_mul]
    rw [e]; exact (ω w⁻¹ _).2

end PositivityTheory.Rg.Sw.Glob
