module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.JPMemAwayP
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory

theorem haarLie_isHaarOn_Nset : ∀ (k r : ℕ) (κ : ENNReal), 0 < κ → κ < ⊤ →
    IsHaarOn (Nset k r) (haarLie (Nset k r) κ) :=
  fun k r κ h0 h1 => Formalism.MainNotions.BridgeCSB.haarLieN k r κ h0.ne' h1.ne

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarLie_isHaarOn_unipotentRadical : ∀ (k r : ℕ) (κ : ENNReal), 0 < κ → κ < ⊤ → IsHaarOn (Nset k r) (haarLie (Nset k r) κ) := by
  first | exact @GlobalTheory.haarLie_isHaarOn_Nset | exact GlobalTheory.haarLie_isHaarOn_Nset | (intros; apply GlobalTheory.haarLie_isHaarOn_Nset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponents
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem split_components :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] v.adicCompletion F), y ∈ loc v L ↔ (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2) ∧ (∀ g : GL (Fin n) (v.adicCompletion F), ∃! h : UPts cm.sig J (v.adicCompletion F), bc ((RingHom.fst _ _).comp sp.toRingHom) h.1 = g) ∧ ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).1 = ∑ i, ∑ j, (sp (x i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet v sp hsig hdiag
  refine ⟨?_, ?_, ?_⟩
  · intro L y
    refine ⟨fun hy => ⟨⟨y, hy, fun _ => rfl⟩, y, hy, fun _ => rfl⟩, ?_⟩
    rintro ⟨⟨y₁, h₁, e₁⟩, y₂, h₂, e₂⟩
    have hint : ∀ x, x ∈ intV E v ↔
        (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
      split_integral_local F E v sp hdiag
    have ha : sp.symm (1, 0) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
    have hb : sp.symm (0, 1) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩
    have hm := (loc v L).add_mem ((loc v L).smul_mem ⟨_, ha⟩ h₁) ((loc v L).smul_mem ⟨_, hb⟩ h₂)
    have hy : y = (⟨_, ha⟩ : intV E v) • y₁ + (⟨_, hb⟩ : intV E v) • y₂ := by
      funext b
      apply sp.injective
      change sp (y b) = sp (sp.symm (1, 0) * y₁ b + sp.symm (0, 1) * y₂ b)
      rw [map_add (f := _), map_mul, map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      ext
      · simp [e₁ b]
      · simp [e₂ b]
    rw [hy]; exact hm
  · intro g
    obtain ⟨e, he⟩ := Formalism.L2.G.exists_locGL cm.sig J hJ (isUnit_iff_ne_zero.2 hdet) _ sp hsig
    refine ⟨e.symm g, ?_, fun h hh => ?_⟩
    · exact (he _).symm.trans (e.apply_symm_apply g)
    · rw [MulEquiv.eq_symm_apply]
      exact (he _).trans hh
  · intro x y
    unfold hR hform
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponentsStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_lattice_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] v.adicCompletion F), y ∈ loc v L ↔ (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2) ∧ (∀ g : GL (Fin n) (v.adicCompletion F), ∃! h : UPts cm.sig J (v.adicCompletion F), bc ((RingHom.fst _ _).comp sp.toRingHom) h.1 = g) ∧ ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).1 = ∑ i, ∑ j, (sp (x i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
  first | exact @GlobalTheory.St.G.split_components | exact GlobalTheory.St.G.split_components | (intros; apply GlobalTheory.St.G.split_components <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
noncomputable section

namespace GlobalTheory.GaugeQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal

variable {P Q P' Q' : ℕ}

def hsDist (g : UpqT P Q) : ℝ := ∑ i, ∑ j, ‖(UpqT.mat g - 1) i j‖ ^ 2

def ptSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) : ℝ :=
  ‖y (e none) - 1‖ ^ 2 + 2 * ∑ i, ‖y (e (some i))‖ ^ 2

def tanSq (t : ℝ × Sp P' Q') : ℝ := t.1 ^ 2 + 2 * ∑ i, ‖t.2 i‖ ^ 2

def gaussSp (y : Sp P Q) : ℝ := Real.exp (-∑ i, ‖y i‖ ^ 2)

def ballVol (d : ℕ) (r : ℝ) : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)

def HasEuclDensity (μ : Measure (UpqT P Q)) : Prop :=
  Tendsto (fun r : ℝ => μ {g | hsDist g < r ^ 2} / ballVol ((P + Q) ^ 2) r) (𝓝[>] 0) (𝓝 1)

theorem _root_.GlobalTheory.GaugeQuot.hsDist_nonneg (g : _root_.Formalism.BasicNotions.UpqT P Q) : 0 ≤ _root_.GlobalTheory.GaugeQuot.hsDist g := by
  unfold _root_.GlobalTheory.GaugeQuot.hsDist
  positivity

theorem _root_.GlobalTheory.GaugeQuot.continuous_hsDist : Continuous (_root_.GlobalTheory.GaugeQuot.hsDist : _root_.Formalism.BasicNotions.UpqT P Q → ℝ) := by
  have hmat : Continuous (_root_.Formalism.BasicNotions.UpqT.mat : _root_.Formalism.BasicNotions.UpqT P Q → _) := _root_.GlobalTheory.UpqTopology.continuous_mat
  unfold _root_.GlobalTheory.GaugeQuot.hsDist
  fun_prop

theorem _root_.GlobalTheory.GaugeQuot.ptSq_nonneg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) : 0 ≤ _root_.GlobalTheory.GaugeQuot.ptSq e y := by
  unfold _root_.GlobalTheory.GaugeQuot.ptSq
  positivity

theorem _root_.GlobalTheory.GaugeQuot.continuous_ptSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (_root_.GlobalTheory.GaugeQuot.ptSq e) := by
  unfold _root_.GlobalTheory.GaugeQuot.ptSq
  fun_prop

theorem _root_.GlobalTheory.GaugeQuot.tanSq_nonneg (t : ℝ × _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P' Q') :
    0 ≤ _root_.GlobalTheory.GaugeQuot.tanSq t := by
  unfold _root_.GlobalTheory.GaugeQuot.tanSq
  positivity

theorem _root_.GlobalTheory.GaugeQuot.continuous_tanSq :
    Continuous (_root_.GlobalTheory.GaugeQuot.tanSq : ℝ × _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P' Q' → ℝ) := by
  unfold _root_.GlobalTheory.GaugeQuot.tanSq
  fun_prop

theorem _root_.GlobalTheory.GaugeQuot.continuous_gaussSp :
    Continuous (_root_.GlobalTheory.GaugeQuot.gaussSp : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → ℝ) := by
  unfold _root_.GlobalTheory.GaugeQuot.gaussSp
  fun_prop

theorem _root_.GlobalTheory.GaugeQuot.ballVol_mul (d : ℕ) (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    _root_.GlobalTheory.GaugeQuot.ballVol d (t * r) = ENNReal.ofReal (t ^ d) * _root_.GlobalTheory.GaugeQuot.ballVol d r := by
  unfold _root_.GlobalTheory.GaugeQuot.ballVol
  rw [Measure.addHaar_ball_mul_of_pos _ _ ht, finrank_euclideanSpace_fin]

theorem _root_.GlobalTheory.GaugeQuot.ballVol_ne_zero (d : ℕ) {r : ℝ} (hr : 0 < r) :
    _root_.GlobalTheory.GaugeQuot.ballVol d r ≠ 0 :=
  (Metric.measure_ball_pos volume _ hr).ne'

theorem _root_.GlobalTheory.GaugeQuot.ballVol_ne_top (d : ℕ) (r : ℝ) : _root_.GlobalTheory.GaugeQuot.ballVol d r ≠ ⊤ :=
  measure_ball_lt_top.ne

end GlobalTheory.GaugeQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfLowest
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfOfIsDS
open MeasureTheory Formalism.MainNotions.S

namespace GlobalTheory.LowestVectorDegree

theorem fdegOf_eq {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ} (h : IsFdeg (Formalism.REAL.muG ε) σ d) {w : H} (hw : w ≠ 0) :
    fdegOf (Formalism.REAL.muG ε) σ w = d := by
  obtain ⟨hd, h⟩ := h
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hsq : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 := (h w w w w).2
  simp only [hsq] at h1
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
    rw [h1]
    push_cast
    rw [← pow_add]
    rfl
  have h3 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = ‖w‖ ^ 4 / d := by exact_mod_cast h2
  unfold fdegOf
  rw [h3]
  have h4 : ‖w‖ ^ 4 ≠ 0 := by positivity
  field_simp

theorem isFdeg_fdegOf_of_isDS {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) {w : H}
    (hw : ‖w‖ = 1) : IsFdeg (Formalism.REAL.muG ε) σ (fdegOf (Formalism.REAL.muG ε) σ w) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS n ε lam H σ hσ 1 one_pos
  have hd' : IsFdeg (Formalism.REAL.muG ε) σ d := by simpa using hd
  rw [fdegOf_eq hd' hw0]
  exact hd'

end GlobalTheory.LowestVectorDegree
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.LowestVectorDegree

theorem isFdeg_fdegOf_lowest : ∀ (D : D7) (X : HidaSetting D) (v : InfinitePlace X.B.I.F),
    IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) :=
  fun _ X v => isFdeg_fdegOf_of_isDS (X.ds v) (X.low v).1

end GlobalTheory.LowestVectorDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
open MeasureTheory FourierTransform Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.SelfDualDiagReal

theorem selfDual_of_transport {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (B : V → V → ℝ) (hs : ∀ x y, B x y = B y x) (T R : V ≃L[ℝ] E)
    (hR : ∀ x y, B x y = inner ℝ (T x) (R y)) (μ : Measure V) [hμ : μ.IsAddHaarMeasure]
    (a b : ℂ) (hab : a * b = 1) (haI : ∀ g : E → ℂ, ∫ x, g (T x) ∂μ = a * ∫ w, g w)
    (hbI : ∀ g : E → ℂ, ∫ x, g (R x) ∂μ = b * ∫ w, g w) :
    SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ))) := by
  refine ⟨hμ, ?_⟩
  intro Φ hΦc hΦs hint z
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hab

  set ψ : E → ℂ := fun w => Φ (T.symm w) with hψdef
  set φ : E → ℂ := fun w => ψ (-w) with hφdef
  have hφc : Continuous φ := hΦc.comp (T.symm.continuous.comp continuous_neg)
  have hφs : HasCompactSupport φ :=
    (hΦs.comp_homeomorph T.symm.toHomeomorph).comp_homeomorph (Homeomorph.neg E)
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφs
  have hψφ : 𝓕⁻ ψ = 𝓕 φ := Real.fourierInv_eq_fourier_comp_neg ψ

  have hhat : ∀ y, ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ
      = a * 𝓕⁻ ψ (R y) := by
    intro y
    have h := haI (fun w => ψ w * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ w (R y) : ℝ) : ℂ)))
    simp only [hψdef, ContinuousLinearEquiv.symm_apply_apply] at h
    simp_rw [hR]
    rw [h, Real.fourierInv_eq']
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hint' : Integrable (fun y => 𝓕⁻ ψ (R y)) μ := by
    have h2 : (fun y => 𝓕⁻ ψ (R y)) = fun y => a⁻¹ *
        ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ := by
      funext y
      rw [hhat y, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    rw [h2]
    exact hint.const_mul _
  obtain ⟨c, -, -, hiff⟩ := GlobalTheory.exists_pos_integral_comp_equiv_haar R μ
  have hFi : Integrable (𝓕 φ) := by
    rw [← hψφ]
    exact (hiff _).1 hint'
  have hinv : 𝓕⁻ (𝓕⁻ ψ) = φ := by
    rw [hψφ]
    exact hφc.fourierInv_fourier_eq hφi hFi
  have hsym : ∀ y, B y z = inner ℝ (R y) (T z) := fun y => by
    rw [hs, hR, real_inner_comm]
  have hlast : ∫ u, 𝓕⁻ ψ u * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))
      = 𝓕⁻ (𝓕⁻ ψ) (T z) := by
    rw [Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  calc _ = ∫ y, (fun u => a * (𝓕⁻ ψ u *
          Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ)))) (R y) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [hhat y, hsym y, mul_assoc]
    _ = b * ∫ u, a * (𝓕⁻ ψ u *
          Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))) :=
          hbI (fun u => a * (𝓕⁻ ψ u *
            Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))))
    _ = (a * b) * φ (T z) := by
        rw [integral_const_mul, hlast, hinv]
        ring
    _ = Φ (-z) := by
        rw [hab, one_mul, hφdef, hψdef]
        simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply]

theorem exists_diag_equiv (κ : Type) [Fintype κ] (d : κ → ℝ) (hd : ∀ k, d k ≠ 0) :
    ∃ D : (κ → ℝ) ≃L[ℝ] (κ → ℝ), (∀ y k, D y k = d k * y k) ∧
      ∀ g : (κ → ℝ) → ℂ, ∫ x, g (D x) = ((|∏ k, d k|⁻¹ : ℝ) : ℂ) * ∫ w, g w := by
  classical
  set f : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) := Matrix.toLin' (Matrix.diagonal d) with hf
  have hdet : LinearMap.det f = ∏ k, d k := by
    rw [hf, LinearMap.det_toLin', Matrix.det_diagonal]
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hd k
  set D : (κ → ℝ) ≃L[ℝ] (κ → ℝ) := (LinearMap.equivOfDetNeZero f hne).toContinuousLinearEquiv
    with hDdef
  have hDf : ∀ x, D x = f x := fun x => rfl
  refine ⟨D, ?_, ?_⟩
  · intro y k
    rw [hDf, hf, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  · intro g
    have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (κ → ℝ)) hne
    have hcoe : (⇑D.toHomeomorph : (κ → ℝ) → (κ → ℝ)) = ⇑f := rfl
    have h := D.toHomeomorph.measurableEmbedding.integral_map (μ := (volume : Measure (κ → ℝ))) g
    rw [hcoe, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), hdet,
      abs_inv] at h
    calc ∫ x, g (D x) = ∫ x, g (f x) := rfl
      _ = _ := by rw [← h, Complex.real_smul]

theorem exists_euclid_equiv (κ : Type) [Fintype κ] :
    ∃ T : (κ → ℝ) ≃L[ℝ] EuclideanSpace ℝ κ, (∀ x y, inner ℝ (T x) (T y) = ∑ k, x k * y k) ∧
      ∀ g : EuclideanSpace ℝ κ → ℂ, ∫ x, g (T x) = ∫ w, g w := by
  refine ⟨(EuclideanSpace.equiv κ ℝ).symm, ?_, ?_⟩
  · intro x y
    simp [PiLp.inner_apply, mul_comm]
  · intro g
    exact (PiLp.volume_preserving_toLp κ).integral_comp
      (MeasurableEquiv.toLp 2 (κ → ℝ)).measurableEmbedding g

theorem selfDual_diag (κ : Type) [Fintype κ] (d : κ → ℝ) (hd : ∀ k, d k ≠ 0) :
    SelfDual (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)))
      (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) := by
  obtain ⟨D, hD, hDI⟩ := exists_diag_equiv κ d hd
  obtain ⟨T, hT, hTI⟩ := exists_euclid_equiv κ
  set s : ℝ := ∏ k, √|d k| with hsdef
  have hs0 : 0 < s := Finset.prod_pos fun k _ => Real.sqrt_pos.2 (abs_pos.2 (hd k))
  have hsq : s * s = |∏ k, d k| := by
    rw [Finset.abs_prod, hsdef, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => Real.mul_self_sqrt (abs_nonneg _)
  have hr : |∏ k, d k| ≠ 0 := abs_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => hd k)
  have : (ENNReal.ofReal s • (volume : Measure (κ → ℝ))).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul _ (by simpa using hs0) ENNReal.ofReal_ne_top
  have hint : ∀ g : (κ → ℝ) → ℂ,
      ∫ x, g x ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) = (s : ℂ) * ∫ x, g x := by
    intro g
    rw [integral_smul_measure, ENNReal.toReal_ofReal hs0.le, Complex.real_smul]
  have hsym : ∀ x y : κ → ℝ, ∑ k, d k * (x k * y k) = ∑ k, d k * (y k * x k) := by
    intro x y
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hR : ∀ x y : κ → ℝ, ∑ k, d k * (x k * y k) = inner ℝ (T x) ((D.trans T) y) := by
    intro x y
    rw [ContinuousLinearEquiv.trans_apply, hT]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD]
    ring
  have hab : (s : ℂ) * ((s : ℂ) * ((|∏ k, d k|⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [← mul_assoc, ← Complex.ofReal_mul, hsq, ← Complex.ofReal_mul, mul_inv_cancel₀ hr,
      Complex.ofReal_one]
  have haI : ∀ g : EuclideanSpace ℝ κ → ℂ,
      ∫ x, g (T x) ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) = (s : ℂ) * ∫ w, g w := by
    intro g
    rw [hint, hTI]
  have hbI : ∀ g : EuclideanSpace ℝ κ → ℂ,
      ∫ x, g ((D.trans T) x) ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) =
        ((s : ℂ) * ((|∏ k, d k|⁻¹ : ℝ) : ℂ)) * ∫ w, g w := by
    intro g
    rw [hint]
    simp only [ContinuousLinearEquiv.trans_apply]
    rw [hDI (fun x => g (T x)), hTI]
    ring
  exact selfDual_of_transport (V := κ → ℝ) (E := EuclideanSpace ℝ κ)
    (fun x y => ∑ k, d k * (x k * y k)) hsym T (D.trans T) hR _ _ _ hab haI hbI

theorem eq_of_selfDual_diag : ∀ (κ : Type) [Fintype κ] (d : κ → ℝ), (∀ k, d k ≠ 0) →
    ∀ μ : Measure (κ → ℝ), SelfDual μ (fun x y => Complex.exp
      (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) →
      μ = ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)) := by
  intro κ _ d hd μ hμ
  classical
  have hν := selfDual_diag κ d hd
  have : (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ))).IsAddHaarMeasure := hν.1
  let Bl : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => ∑ k, d k * (x k * y k))
    (fun x x' y => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun x y y' => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
  have hBl : ∀ x y, Bl x y = ∑ k, d k * (x k * y k) := fun x y => rfl
  have hsymm : ∀ x y, Bl x y = Bl y x := fun x y => by
    rw [hBl, hBl]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hnd : ∀ x, (∀ y, Bl x y = 0) → x = 0 := by
    intro x hx
    funext k
    have h := hx (Pi.single k 1)
    rw [hBl] at h
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    exact (mul_eq_zero.1 h).resolve_left (hd k)
  obtain ⟨-, hsch⟩ := GlobalTheory.fourier_inversion_haar_symm_form Bl hsymm hnd
    (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ))) inferInstance
  obtain ⟨u, -, hu_cs, hu_sm, -, hu0⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (x := (0 : κ → ℝ)) (s := Set.univ) Filter.univ_mem
  have hΦcs : HasCompactSupport (⇑Complex.ofRealCLM ∘ u) := hu_cs.comp_left (map_zero _)
  have hΦsm := Complex.ofRealCLM.contDiff.comp hu_sm
  have hI := (hsch (hΦcs.toSchwartzMap hΦsm)).2
  exact SelfDual.eq_of_test hν hμ (⇑Complex.ofRealCLM ∘ u) hΦsm.continuous hΦcs hI 0
    (by simp [hu0])

end GlobalTheory.SelfDualDiagReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonalStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_measure_real_diagonal : ∀ (κ : Type) [Fintype κ] (d : κ → ℝ), (∀ k, d k ≠ 0) → ∀ μ : Measure (κ → ℝ), SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) → μ = ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)) := by
  first | exact @GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag | exact GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag | (intros; apply GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdDiffEqProdFactorial
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FormalDegreeDatum

theorem inUJ_of_cayley {n : ℕ} (ε : Fin n → Bool) (P Q G : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (h1 : Pᴴ * Formalism.REAL.Jm ε * P = G) (h2 : Qᴴ * Formalism.REAL.Jm ε * Q = G) :
    Formalism.REAL.inUJ ε (Q * P⁻¹) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  unfold Formalism.REAL.inUJ
  have : (Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (Q * P⁻¹) = (P⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * P⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [this, h2, ← h1]
  have : (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [this, hPP]; simp

theorem fdeg_of_conj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsMulLeftInvariant]
    (σ₀ σ₁ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (a : Formalism.REAL.UJ ε)
    (hc : ∀ g : Formalism.REAL.UJ ε, σ₀ (umat g) = σ₁ (umat (a * g * a⁻¹)))
    (hu : IsURepOn (UJset ε) σ₁) (d : ℝ) (hd : IsFdeg μ σ₀ d) (w : H) (hw : w ≠ 0) :
    ‖w‖ ^ 4 / ∫ g, ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2 ∂μ = d := by
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hmul : ∀ g h : Formalism.REAL.UJ ε, σ₁ (umat (g * h)) w = σ₁ (umat g) (σ₁ (umat h) w) := by
    intro g h
    have := hu.1.2 _ (hmem g) _ (hmem h)
    have e : umat (g * h) = umat g * umat h := rfl
    rw [e, this]; rfl
  have hv : ‖σ₁ (umat a) w‖ = ‖w‖ := hu.2.1 _ (hmem a) w
  set v := σ₁ (umat a) w with hvdef
  have h1 : ∫ g, ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2 ∂μ = ∫ g, ‖coefOn σ₀ v w g‖ ^ 2 ∂μ := by
    rw [← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2) a]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [coefOn, hc, hvdef, ← hmul]
    rw [inv_mul_cancel_right]
  have h2 := (hd.2 v w v w).2
  have h3 : ∀ g : Formalism.REAL.UJ ε, coefOn σ₀ v w g * star (coefOn σ₀ v w g) =
      ((‖coefOn σ₀ v w g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h3] at h2
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hv] at h2
  have h4 : ∫ g, ‖coefOn σ₀ v w g‖ ^ 2 ∂μ = ‖w‖ ^ 2 * ‖w‖ ^ 2 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    simp
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hd0 : d ≠ 0 := hd.1.ne'
  rw [h1, h4]
  field_simp

end GlobalTheory.FormalDegreeDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexCoordinatesMeasurePreserving
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexCoordinatesMeasurePreserving
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.ReImVolume

noncomputable def reImLinear (ι : Type) (n : ℕ) :
    (ι → Fin n → ℂ) ≃ₗ[ℝ] (ι × Fin n × Bool → ℝ) where
  toFun y p := if p.2.2 then (y p.1 p.2.1).re else (y p.1 p.2.1).im
  invFun x v i := ⟨x (v, i, true), x (v, i, false)⟩
  map_add' y z := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp
  map_smul' c y := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp
  left_inv y := by
    funext v i
    simp
  right_inv x := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp

theorem volume_re_im (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume {z : ℂ | z.re ∈ A ∧ z.im ∈ B} = volume A * volume B := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (hA.prod hB).nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_prod] at h
  rw [← h]
  rfl

theorem measurePreserving_reImLinear (ι : Type) [Fintype ι] (n : ℕ) :
    MeasurePreserving (reImLinear ι n) volume volume := by
  have hm : Measurable (reImLinear ι n) :=
    (reImLinear ι n).toLinearMap.continuous_of_finiteDimensional.measurable
  refine ⟨hm, ?_⟩
  rw [volume_pi (α := fun _ : ι × Fin n × Bool => ℝ)]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (reImLinear ι n) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun v => Set.univ.pi fun i =>
        {z : ℂ | z.re ∈ s (v, i, true) ∧ z.im ∈ s (v, i, false)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_setOf_eq]
    constructor
    · intro h v i
      exact ⟨h (v, i, true), h (v, i, false)⟩
    · rintro h ⟨v, i, _ | _⟩
      · exact (h v i).2
      · exact (h v i).1
  rw [hpre, volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool, volume_re_im _ _ (hs _) (hs _)]

theorem exists_reIm_measurePreserving :
    ∀ (ι : Type) [Fintype ι] (n : ℕ), ∃ T : (ι → Fin n → ℂ) ≃ₜ+ (ι × Fin n × Bool → ℝ),
      MeasurePreserving T volume volume ∧
        ∀ y v i, T y (v, i, true) = (y v i).re ∧ T y (v, i, false) = (y v i).im := by
  intro ι _ n
  let L := (reImLinear ι n).toContinuousLinearEquiv
  refine ⟨{ toAddEquiv := (reImLinear ι n).toAddEquiv
            continuous_toFun := L.continuous
            continuous_invFun := L.symm.continuous }, ?_, fun y v i => ⟨rfl, rfl⟩⟩
  exact measurePreserving_reImLinear ι n

end GlobalTheory.ReImVolume
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexCoordinatesMeasurePreservingStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_coordinates_measure_preserving : ∀ (ι : Type) [Fintype ι] (n : ℕ), ∃ T : (ι → Fin n → ℂ) ≃ₜ+ (ι × Fin n × Bool → ℝ), MeasurePreserving T volume volume ∧ ∀ y v i, T y (v, i, true) = (y v i).re ∧ T y (v, i, false) = (y v i).im := by
  first | exact @GlobalTheory.ReImVolume.exists_reIm_measurePreserving | exact GlobalTheory.ReImVolume.exists_reIm_measurePreserving | (intros; apply GlobalTheory.ReImVolume.exists_reIm_measurePreserving <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapPairingBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapPairingBound
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DatumOfPeriods

section

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma dsigW_eq (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ w v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v)
    rw [ih]; rfl

lemma isBesselMapSm_smul {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {l : H → Wp}
    (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π l) (a : ℂ) :
    Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun v => a • l v) := by
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun g hg m hm v hv => ?_, ‖a‖ * C, Ws, h4, fun v hv => ?_⟩
  · simp only [h1 v hv w hw, smul_add]
  · simp only [h2 c v hv]; rw [smul_comm]
  · simp only [h3 g hg m hm v hv, map_smul]; rw [smul_comm]
  · simp only [dsigW_eq, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h5 v hv) (norm_nonneg _)

lemma l2SG_sqrt_smul_eq_ofReal_mul {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (n : ℕ) (c : ℝ)
    (h : l2SG ν F = ENNReal.ofReal c) :
    l2SG ν (fun g => ((Real.sqrt n : ℝ) : ℂ) • F g) = ENNReal.ofReal (c * n) := by
  have e : ∀ y : Wp, ((‖((Real.sqrt n : ℝ) : ℂ) • y‖₊ : ℝ≥0∞)) ^ 2 = (n : ℝ≥0∞) * (‖y‖₊ : ℝ≥0∞) ^ 2 := by
    intro y
    have : ‖((Real.sqrt n : ℝ) : ℂ)‖₊ ^ 2 = (n : NNReal) := by
      apply NNReal.eq
      simp [Real.sq_sqrt, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [nnnorm_smul, ENNReal.coe_mul, mul_pow, ← ENNReal.coe_pow, this, ENNReal.coe_natCast]
  unfold l2SG at h ⊢
  simp only [e]
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n), h, mul_comm c, ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ENNReal.ofReal_natCast]

end

theorem exists_goodS : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDS (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  intro hH D τ w w' θ W lam R _ l l' dd _ _ hR hl hl' hdd hn hn'
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨P, hP, hD⟩ := hR.2
  have hD' : Formalism.MainNotions.S.IsDS (epsSH D.R) lam (fun g => R.σ (P⁻¹ * g * P)) := hD
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ hD' _ (D.s.cdScale_pos _ (epsSH D.R))
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hD'
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hvs : v ∈ R.sm :=
    ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK _ _ _ lam R hR P hP S hS.1 hS.2.1).1 v hvS).2
  refine ⟨{ H := R.H, σ := R.σ, B := fun x => ((Real.sqrt (Module.finrank ℂ W.Wp : ℕ) : ℝ) : ℂ) • l x,
            B' := fun x => ((Real.sqrt (Module.finrank ℂ W.Wq : ℕ) : ℝ) : ℂ) • l' x,
            v0 := v, cN := ‖v‖ ^ 2 / dd, deg := d },
    hR.1, hR.2, isBesselMapSm_smul hl _, isBesselMapSm_smul hl' _, hvs, hv0, ⟨P, hP, ?_⟩,
    div_pos (pow_pos (norm_pos_iff.2 hv0) 2) hdd, l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn v hvs),
    l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn' v hvs), P, hP.1, hd⟩
  exact (le_sSup (s := {S | IsKTypeOf (epsSH D.R) (fun g => R.σ (P⁻¹ * g * P)) (Formalism.QuantumDeterminants.lowK (epsSH D.R) lam) S}) hS) hvS

end GlobalTheory.DatumOfPeriods
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapPairingBoundStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_map_pairing_bound : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDS (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  first | exact @GlobalTheory.DatumOfPeriods.exists_goodS | exact GlobalTheory.DatumOfPeriods.exists_goodS | (intros; apply GlobalTheory.DatumOfPeriods.exists_goodS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLeOfDiag
open NumberField Formalism.BasicNotions

namespace GlobalTheory.SA.AmbSig

open Matrix Module

theorem card_le_of_diag {p q d : ℕ} (N : Matrix (Fin p ⊕ Fin q) (Fin d) ℂ) (δ : Fin d → ℂ)
    (hδ : ∀ j, (δ j).re ≤ 0) (hN : Nᴴ * Formalism.UG.Jpq p q * N = diagonal δ)
    (hinj : ∀ c, N *ᵥ c = 0 → c = 0) : d ≤ q := by
  classical

  let f : (Fin d → ℂ) →ₗ[ℂ] (Fin q → ℂ) :=
    LinearMap.funLeft ℂ ℂ (Sum.inr : Fin q → Fin p ⊕ Fin q) ∘ₗ Matrix.mulVecLin N
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun c hc => ?_
    set w := N *ᵥ c with hw
    have hr : ∀ i, w (Sum.inr i) = 0 := fun i => congrFun hc i

    have hform : star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w) = star c ⬝ᵥ (diagonal δ *ᵥ c) := by
      rw [← hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      conv_rhs => rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hleft : (star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w)).re = ∑ i, Complex.normSq (w (Sum.inl i)) := by
      unfold Formalism.UG.Jpq
      rw [Matrix.fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type, hr, Complex.mul_re, Complex.normSq_apply]
    have hright : (star c ⬝ᵥ (diagonal δ *ᵥ c)).re = ∑ j, (δ j).re * Complex.normSq (c j) := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.normSq_apply]
      ring
    have hnn : ∀ i, 0 ≤ Complex.normSq (w (Sum.inl i)) := fun i => Complex.normSq_nonneg _
    have hsum : ∑ i, Complex.normSq (w (Sum.inl i)) ≤ 0 := by
      rw [← hleft, hform, hright]
      exact Finset.sum_nonpos fun j _ =>
        mul_nonpos_of_nonpos_of_nonneg (hδ j) (Complex.normSq_nonneg _)
    have hl : ∀ i, w (Sum.inl i) = 0 := fun i =>
      Complex.normSq_eq_zero.1 (le_antisymm
        ((Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)).trans hsum) (hnn i))
    apply hinj
    funext x
    cases x with
    | inl i => exact hl i
    | inr i => exact hr i
  simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem hT_eq_sum {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ b, (∑ a, star (S.frame.repr x a) * S.gram a b) * S.frame.repr y b := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  simp only [HSpace.gram]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem amb_of_sig : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (k r : ℕ),
    GlobalTheory.SA.CMStar E → S.SigOK → (∀ τ : E →+* ℂ, S.sig τ = (k + r, r + 1)) → GlobalTheory.SA.Amb S k r := by
  intro E _ _ _ S k r hcm hok hsig

  have hfac : ∀ τ : E →+* ℂ, S.rank = k + r + (r + 1) ∧
      ∃ A : Matrix (Fin (k + r) ⊕ Fin (r + 1)) (Fin S.rank) ℂ,
        Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A = S.gram.map τ ∧
        ∃ B : Matrix (Fin S.rank) (Fin (k + r) ⊕ Fin (r + 1)) ℂ, B * A = 1 := by
    intro τ
    have h := hok τ
    rw [hsig τ] at h
    obtain ⟨h1, ⟨A, hA⟩, h3⟩ :=
      GlobalTheory.Mem.SignatureFactor.exists_factor S.rank (k + r) (r + 1) _ h
    obtain ⟨B, -, hBA⟩ := h3 A hA
    exact ⟨h1.symm, A, hA, B, hBA⟩
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine ⟨hcm, ?_, ?_⟩
  · rw [S.rank_eq, (hfac τ₀).1]
    ring
  · intro τ U hU
    classical
    obtain ⟨-, A, hA, B, hBA⟩ := hfac τ

    let F : U →ₗ[E] U →ₛₗ[starRingEnd E] E := S.hT.flip.domRestrict₁₂ U U
    have hF : ∀ x y, starRingEnd E (F x y) = F y x := fun x y => S.herm.eq (y : S.V) (x : S.V)
    obtain ⟨u, hu⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (E := E) (c := starRingEnd E)
      two_ne_zero (Module.finrank E U) F hF rfl

    let v : Fin (Module.finrank E U) → Fin S.rank → E := fun j => S.frame.repr (u j : S.V)
    have hv : LinearIndependent E v := by
      have hker : LinearMap.ker (S.frame.equivFun.toLinearMap ∘ₗ U.subtype) = ⊥ :=
        LinearMap.ker_eq_bot.2 (S.frame.equivFun.injective.comp Subtype.val_injective)
      exact u.linearIndependent.map' _ hker
    letI : Algebra E ℂ := τ.toAlgebra
    haveI : FaithfulSMul E ℂ := (faithfulSMul_iff_algebraMap_injective E ℂ).2 τ.injective
    have hvC : LinearIndependent ℂ (fun j => algebraMap E ℂ ∘ v j) :=
      linearIndependent_algebraMap_comp_iff.2 hv
    let C : Matrix (Fin S.rank) (Fin (Module.finrank E U)) ℂ := Matrix.of fun a j => τ (v j a)
    refine card_le_of_diag (A * C) (fun j => τ (S.hT (u j : S.V) (u j : S.V)))
      (fun j => hU _ (u j).2) ?_ ?_
    · have hsplit : (A * C)ᴴ * Formalism.UG.Jpq (k + r) (r + 1) * (A * C) =
          Cᴴ * (Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A) * C := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hsplit, hA]
      ext i j
      have hij : τ (S.hT (u i : S.V) (u j : S.V)) = (Cᴴ * S.gram.map τ * C) i j := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hT_eq_sum, map_sum, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, map_sum, Matrix.mul_apply]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        simp [C, v, hcm τ]
      rw [← hij, Matrix.diagonal_apply]
      split_ifs with h
      · rw [h]
      · have h0 : F (u j) (u i) = 0 := hu j i (Ne.symm h)
        simp only [F, LinearMap.domRestrict₁₂_apply, LinearMap.flip_apply] at h0
        rw [h0, map_zero]
    · intro c hc
      have hCc : C *ᵥ c = 0 := by
        rw [← Matrix.mulVec_mulVec] at hc
        rw [← Matrix.one_mulVec (C *ᵥ c), ← hBA, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
      have hlin := Fintype.linearIndependent_iff.1 hvC c (by
        rw [← hCc]
        funext a
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, C, mul_comm, RingHom.algebraMap_toAlgebra])
      funext j
      exact hlin j

end GlobalTheory.SA.AmbSig
end
