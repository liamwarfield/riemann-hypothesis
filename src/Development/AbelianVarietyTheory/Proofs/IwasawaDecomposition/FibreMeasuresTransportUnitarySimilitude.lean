module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitude
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitude
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem isFibreFamily_transport {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure V) (ν : Measure R) (q q₂ : V → R) (e : V ≃ₜ V) (u : Rˣ) (a d : ℝ≥0) (hd : d ≠ 0)
    (hμ : μ = a • μ.map e) (hν : ν = d • ν.map (fun z => (u : R) * z))
    (hq : ∀ v, q₂ (e v) = u * q v) (fib : R → Measure V)
    (h : IsFibreFamily μ q id Set.univ ν {c | IsUnit c} fib) :
    IsFibreFamily μ q₂ id Set.univ ν {c | IsUnit c}
      (fun b => (a * d⁻¹) • (fib ((u⁻¹ : Rˣ) * b)).map e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hmu : MeasurableEmbedding (fun z : R => (u : R) * z) :=
    (Homeomorph.smul u : R ≃ₜ R).measurableEmbedding
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc _ => ?_⟩
  · rw [Measure.smul_apply, hme.map_apply]
    have : e ⁻¹' (q₂ ⁻¹' {id b} ∩ Set.univ)ᶜ = (q ⁻¹' {id ((u⁻¹ : Rˣ) * b)} ∩ Set.univ)ᶜ := by
      ext v
      simp [hq, Units.eq_inv_mul_iff_mul_eq]
    rw [this, h1, smul_zero]
  · have h2' := h2 (φ ∘ e) (hφ.comp e.measurable)
    simp only [Measure.restrict_univ, Function.comp] at h2' ⊢
    have hL : ∫⁻ v, φ v ∂μ = (a : ℝ≥0∞) * ∫⁻ v, φ (e v) ∂μ := by
      conv_lhs => rw [hμ]
      rw [lintegral_smul_measure, hme.lintegral_map, ENNReal.smul_def, smul_eq_mul]
    rw [hL, h2']
    conv_rhs => rw [hν]
    rw [lintegral_smul_measure, hmu.lintegral_map]
    simp only [lintegral_smul_measure, hme.lintegral_map, Units.inv_mul_cancel_left,
      ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul]
    congr 2
    field_simp
  · obtain ⟨h4, h5⟩ := h3 (φ ∘ e) (hφ.comp e.continuous) (hc.comp_homeomorph e) (Set.subset_univ _)
    have hmem : ∀ b ∈ {c : R | IsUnit c}, ((u⁻¹ : Rˣ) : R) * b ∈ {c : R | IsUnit c} :=
      fun b hb => (Units.isUnit _).mul hb
    refine ⟨fun b hb => ?_, ?_⟩
    · exact (hme.integrable_map_iff.2 (h4 _ (hmem b hb))).smul_measure_nnreal
    · simp only [integral_smul_nnreal_measure, hme.integral_map]
      exact (h5.comp (continuous_const.mul continuous_id).continuousOn hmem).const_smul _

theorem lrAct_one_right {S : Type} [CommRing S] {n M : ℕ} (g : Matrix (Fin M) (Fin M) S)
    (X : Fin n → Fin M → S) : lrAct g 1 X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

theorem exists_homeomorph_lrAct {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    {n M : ℕ} (g : Matrix (Fin M) (Fin M) S) (hg : IsUnit g.det) :
    ∃ e : (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S), ⇑e = lrAct g 1 := by
  refine ⟨{ toFun := fun X a => g.mulVec (X a)
            invFun := fun X a => g⁻¹.mulVec (X a)
            left_inv := fun X => ?_
            right_inv := fun X => ?_
            continuous_toFun := continuous_pi fun a =>
              continuous_const.matrix_mulVec (continuous_apply a)
            continuous_invFun := continuous_pi fun a =>
              continuous_const.matrix_mulVec (continuous_apply a) }, ?_⟩
  · funext a
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg]
  · funext a
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hg]
  · funext X
    rw [lrAct_one_right]
    rfl

theorem fibAt_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J J₂ : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β c : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit g.det → IsUnit c → (∀ z, qR R σ J₂ (g.mulVec z) = c * qR R σ J z) → FibAt R σ J (tupMeas lam 1 M) ν β m → FibAt R σ J₂ (tupMeas lam 1 M) ν (c * β) ((modu (R ⊗[F] E) g.det * (modu R c)⁻¹) • m.map (lrAct g 1)) := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hR M J J₂ lam ν β c m g hlam hν hg hc hq hfib
  obtain ⟨fib, hfib, rfl⟩ := hfib
  obtain ⟨hA, hred, -⟩ := GlobalTheory.T.tensor_niceRing_artinian_reduced_openUnits F E R hR
  have hμ := GlobalTheory.T.vectorTupleProductMeasure_two_sided_action (R ⊗[F] E) hA hred lam hlam 1 M g 1 hg (by simp)
  rw [Matrix.det_one, (modu_basic (R ⊗[F] E)).2.2.1, one_pow, mul_one, pow_one] at hμ
  obtain ⟨e, he⟩ := exists_homeomorph_lrAct (n := 1) g hg
  obtain ⟨hpos, hν'⟩ := (modu_basic R).1 c hc
  obtain ⟨u, rfl⟩ := hc
  rw [← he] at hμ ⊢
  refine ⟨_, isFibreFamily_transport _ ν _ _ e u _ _ hpos.ne' hμ (hν' ν hν) (fun X => ?_) fib hfib, ?_⟩
  · rw [he, lrAct_one_right]
    exact hq _
  · simp only [Units.inv_mul_cancel_left]

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitudeStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreMeasures_transport_unitary_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J J₂ : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β c : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit g.det → IsUnit c → (∀ z, qR R σ J₂ (g.mulVec z) = c * qR R σ J z) → FibAt R σ J (tupMeas lam 1 M) ν β m → FibAt R σ J₂ (tupMeas lam 1 M) ν (c * β) ((modu (R ⊗[F] E) g.det * (modu R c)⁻¹) • m.map (lrAct g 1)) := by
  first | exact @GlobalTheory.GaugeEx.fibAt_similitude | exact GlobalTheory.GaugeEx.fibAt_similitude | (intros; apply GlobalTheory.GaugeEx.fibAt_similitude <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOThZeroTriv
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker Complex Classical
open Formalism.L2.Th1.H (matH alphaQ qOf opU slice pow4)
open scoped BigOperators ComplexConjugate Real

namespace WeilVac

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem kappa_ne_zero {γ₀ : IsoK D} (k : KapChoice γ₀) : k.kappa ≠ 0 := by
  refine finprod_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun p => zpow_ne_zero _ ?_
  intro h0
  have h1 := k.rt_pow p p.2.1 p.2.2
  have hpi : k.pi p ≠ 0 := by
    intro h
    have h2 := k.pi_gen p p.2.1 p.2.2
    rw [h, Ideal.span_singleton_zero] at h2
    exact pow_ne_zero _ (k.pp p).ne_bot h2
  have hE : (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) ≠ 0 := by
    set_option synthInstance.maxHeartbeats 200000 in
      simpa using hpi
  rw [h0, zero_pow (mul_ne_zero two_ne_zero (classNumber_ne_zero _))] at h1
  exact div_ne_zero ((map_ne_zero _).2 hE) ((map_ne_zero _).2 ((map_ne_zero _).2 hE)) h1.symm

theorem thMM_spec (B : Formalism.L2.Ker.Base D cc δ) (h : B.StdOK) : B.IsThMM B.thMM ∧ B.thMM ≠ 0 := by
  obtain ⟨e, u⟩ := ThetaVec.thetaVector _ _ _ _ _ _ _ _ h _ (kappa_ne_zero B.kc)
  have h1 : B.IsThMM B.thMM := Classical.epsilon_spec (p := IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa) e
  exact ⟨h1, (u _ h1.1 h1.2).1⟩

theorem areaOK (B : Formalism.L2.Ker.Base D cc δ) : B.AreaOK := by
  rw [Formalism.L2.Ker.Base.AreaOK, ThetaVec.area_eq]
  exact GlobalTheory.OddTheta.area_eq B.L _ fun z => by rw [← B.lat]; rfl

theorem q_int (B : Formalism.L2.Ker.Base D cc δ) (h : B.StdOK) {x : D.what₂.Tau → ℂ} (hx : x ∈ B.lamM) :
    ∃ m : ℤ, qOf B.cq (matH (hOne B.L D.what₂.Tau)) x = m := by
  have hs : ∀ a, slice a (0 : Fin 4 × D.what₂.Tau → ℂ) = 0 := fun _ => rfl
  have h1 := h.betaSemi.1 (B.gC (ThetaVec.ins 0 x)) ⟨ThetaVec.ins 0 x, fun a => by
    rw [ThetaVec.slice_ins]; split_ifs; exacts [hx, B.lamM.zero_mem], rfl⟩
  rw [h.betaAlpha, ← mul_self_eq_one_iff] at h1
  simp only [ThetaVec.slice_ins, Fin.prod_univ_four, hs, h.alpha0, Fin.isValue, if_true, Fin.reduceEq, if_false,
    mul_one] at h1
  rw [alphaQ, ← Complex.exp_add, Complex.exp_eq_one_iff] at h1
  obtain ⟨m, hm⟩ := h1
  refine ⟨m, ?_⟩
  have : (qOf B.cq (matH (hOne B.L D.what₂.Tau)) x : ℂ) = m := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    linear_combination hm
  exact_mod_cast this

theorem entry_mem (B : Formalism.L2.Ker.Base D cc δ) {N N' : ℕ} {x : VC D N N'}
    (hx : x ∈ La D (tor0 D cc δ) (stdL D N) (stdL D N')) : x ∈ powLat B.lamM N N' := by
  refine (AddSubgroup.closure_le _).2 ?_ hx
  rintro _ ⟨w, hw, A, hA, rfl⟩ i j
  exact AddSubgroup.subset_closure ⟨w, hw, A i j, (GlobalTheory.OddGenus.mem_iff_entries D N N' A).1 hA i j, rfl⟩

theorem Hf_eq (B : Formalism.L2.Ker.Base D cc δ) {N N' : ℕ} (z w : VC D N N') :
    Hf D (tor0 D cc δ) z w =
      ∑ i, ∑ j, matH (hOne B.L D.what₂.Tau) (fun τ => z τ i j) (fun τ => w τ i j) := by
  have hA : area (tor0 D cc δ).abelian₂ = latticeArea B.L := (areaOK B).trans (ThetaVec.area_eq _)
  have e : ∀ u v : D.what₂.Tau → ℂ, matH (hOne B.L D.what₂.Tau) u v =
      ∑ τ, u τ * conj (v τ) / (latticeArea B.L : ℂ) := fun u v => ThetaVec.stdH_apply B.L u v
  simp only [e, Hf, hA, Finset.sum_div]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem thZero_mem (B : Formalism.L2.Ker.Base D cc δ) (h : B.StdOK) (N N' : ℕ) :
    B.thZero N N' ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N') := by
  have hθ := (thMM_spec B h).1.1
  refine ⟨?_, fun x hx z => ?_⟩
  · have hd : Differentiable ℂ B.thMM := differentiableOn_univ.1 hθ.1.differentiableOn
    unfold Formalism.L2.Ker.Base.thZero tensPow
    fun_prop
  · have hx' := entry_mem B hx
    choose m hm using fun i j => q_int B h (hx' i j)
    have h1 : Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = ((∑ i, ∑ j, m i j : ℤ) : ℝ) := by
      rw [Hf_eq B]
      push_cast
      simp only [Complex.re_sum, Finset.mul_sum, ← hm]
      rfl
    have h2 : al D (tor0 D cc δ) x = ∏ i, ∏ j, alphaQ B.cq (matH (hOne B.L D.what₂.Tau)) fun τ => x τ i j := by
      rw [al, h1, round_intCast, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      simp only [alphaQ, hm, ← Complex.exp_sum, ← Finset.mul_sum]
      congr 1
      push_cast
      ring
    rw [h2, U, Hf_eq B, Hf_eq B]
    simp only [Formalism.L2.Ker.Base.thZero, tensPow, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, Complex.exp_sum,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hθ.2 _ (hx' i j) fun τ => z τ i j

end WeilVac

open WeilVac

end GlobalTheory.Mem.Col2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumEqTraceOriented
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.OrientedSmall

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem sum_eq_trace_oriented (P : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (x y : Matrix (Fin m) (Fin n) R) :
    ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * K e d * x d a = (P * (y.map c)ᵀ * K * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ e, ∑ d, P a b * c (y e b) * K e d * x d a
      = ∑ e, ∑ b, ∑ d, P a b * c (y e b) * K e d * x d a := Finset.sum_comm
    _ = ∑ e, ∑ d, ∑ b, P a b * c (y e b) * K e d * x d a := Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem trace_coord (J P : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (hPJ : P * J = 1) (hP : P.map c = Pᵀ) (x y : Matrix (Fin m) (Fin n) R) :
    (P * (y.map c)ᵀ * K * x).trace = ((((y * P)ᵀ).map c)ᵀ * Jᵀ * (x * P)ᵀ * Kᵀ).trace := by
  have e1 : Jᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPJ, Matrix.transpose_one]
  rw [Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_mul, hP, Matrix.transpose_mul]
  calc (P * (y.map c)ᵀ * K * x).trace
      = (P * (y.map c)ᵀ * (K * x)).trace := by simp only [Matrix.mul_assoc]
    _ = (K * x * (P * (y.map c)ᵀ)).trace := Matrix.trace_mul_comm _ _
    _ = (K * x * (P * (y.map c)ᵀ))ᵀ.trace := (Matrix.trace_transpose _).symm
    _ = (y.map c * Pᵀ * xᵀ * Kᵀ).trace := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = (y.map c * Pᵀ * (Jᵀ * Pᵀ) * xᵀ * Kᵀ).trace := by rw [e1, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem act_coord (J P g g' : Matrix (Fin n) (Fin n) R) (h : Matrix (Fin m) (Fin m) R)
    (hPJ : P * J = 1) (hg : (g.map c)ᵀ * J * g = J) (hgg : g * g' = 1) (x : Matrix (Fin m) (Fin n) R) :
    (h * x * g' * P)ᵀ = g.map c * (x * P)ᵀ * hᵀ := by
  have hJP : J * P = 1 := mul_eq_one_comm.1 hPJ
  have key : g' * P = P * (g.map c)ᵀ := by
    calc g' * P = (P * J) * g' * P := by rw [hPJ, Matrix.one_mul]
      _ = P * ((g.map c)ᵀ * J * g) * g' * P := by rw [hg]
      _ = P * (g.map c)ᵀ * (J * ((g * g') * P)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgg, Matrix.one_mul, hJP, Matrix.mul_one]
  rw [Matrix.mul_assoc (h * x), key]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end Generic

variable {D : D7}

theorem cA_incA (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, incA, inclR, CMData.sig, starRingEnd_apply]

theorem gram_conjTranspose (V : HSp D) : V.gramᴴ = V.gram := by
  refine Matrix.ext fun i j => ?_
  exact V.herm.eq (V.frame j) (V.frame i)

theorem gramInv_mul (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gramInv_map (V : HSp D) :
    ((V.gram⁻¹).map (incA D)).map (cA D) = ((V.gram⁻¹).map (incA D))ᵀ := by
  have h : (V.gram⁻¹)ᴴ = V.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_conjTranspose]
  ext i j
  have := congrFun (congrFun h j) i
  rw [Matrix.conjTranspose_apply] at this
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  rw [cA_incA, this]

theorem mt_mul_inv (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem hO_eq (S T : HSp D) (hr : S.rank ≤ T.rank) (x y : WO S T) :
    hO S T x y = hHom S T (toTWsmall S T y) (toTWsmall S T x) := by
  unfold hO hHom
  rw [if_pos hr]
  have s := sum_eq_trace (cA D) (S.gram.map (incA D)) (T.gram.map (incA D))
    (toTWsmall S T y) (toTWsmall S T x)
  have s' := sum_eq_trace_oriented (cA D) ((S.gram⁻¹).map (incA D)) (T.gram.map (incA D)) x y
  simp only [Matrix.map_apply] at s s'
  rw [s, s']
  exact trace_coord (cA D) _ _ _ (gramInv_mul S) (gramInv_map S) x y

theorem bridgeSmall (D : D7) : BridgeSmall D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · unfold symplO sympl
    rw [hO_eq S T hr]
  · unfold actHom
    rw [if_pos hr]
    exact act_coord (cA D) _ _ _ _ _ (gramInv_mul S) (mt_rel S g) (mt_mul_inv S g) x

end GlobalTheory.OrientedSmall

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
noncomputable section

open AlgebraicGeometry CategoryTheory Limits Topology Filter TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Points

namespace GlobalTheory.ProperPoints

section Ultrapower

variable {I F : Type} [NormedField F] (𝒰 : Ultrafilter I)

def bddRing (F : Type) [NormedField F] : ValuationSubring ((𝒰 : Filter I).Germ F) where
  carrier := {a | ∃ (M : ℝ) (f : I → F), a = (f : (𝒰 : Filter I).Germ F) ∧ ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ M}
  mul_mem' := by
    rintro _ _ ⟨M, f, rfl, hf⟩ ⟨N, g, rfl, hg⟩
    refine ⟨M * N, f * g, rfl, ?_⟩
    filter_upwards [hf, hg] with i h1 h2
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  one_mem' := ⟨1, 1, rfl, Eventually.of_forall fun i => by simp⟩
  add_mem' := by
    rintro _ _ ⟨M, f, rfl, hf⟩ ⟨N, g, rfl, hg⟩
    refine ⟨M + N, f + g, rfl, ?_⟩
    filter_upwards [hf, hg] with i h1 h2
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  zero_mem' := ⟨0, 0, rfl, Eventually.of_forall fun i => by simp⟩
  neg_mem' := by
    rintro _ ⟨M, f, rfl, hf⟩
    refine ⟨M, -f, rfl, ?_⟩
    filter_upwards [hf] with i h1
    simpa using h1
  mem_or_inv_mem' := by
    intro a
    induction a using Germ.inductionOn with
    | h f =>
      by_cases h : ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ 1
      · exact Or.inl ⟨1, f, rfl, h⟩
      · refine Or.inr ⟨1, f⁻¹, rfl, ?_⟩
        filter_upwards [Ultrafilter.eventually_not.2 h] with i hi
        rw [Pi.inv_apply, norm_inv]
        exact inv_le_one_of_one_le₀ (not_le.1 hi).le

def constBdd (F : Type) [NormedField F] : F →+* bddRing 𝒰 F where
  toFun a := ⟨((fun _ => a : I → F) : (𝒰 : Filter I).Germ F), ‖a‖, _, rfl, Eventually.of_forall fun _ => le_rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable [ProperSpace F]

theorem exists_tendsto (a : bddRing 𝒰 F) : ∃ c : F, (a : (𝒰 : Filter I).Germ F).Tendsto (𝓝 c) := by
  obtain ⟨_, M, f, rfl, hf⟩ := a
  obtain ⟨c, -, hc⟩ := (isCompact_closedBall (0 : F) M).ultrafilter_le_nhds (𝒰.map f) (by
    rw [le_principal_iff]
    exact hf.mono fun i hi => by simpa using hi)
  exact ⟨c, hc⟩

theorem tendsto_choose (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) :
    Tendsto f 𝒰 (𝓝 (exists_tendsto 𝒰 a).choose) := by
  have h := (exists_tendsto 𝒰 a).choose_spec
  generalize (exists_tendsto 𝒰 a).choose = c at h ⊢
  rwa [hf] at h

theorem choose_eq (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) {c : F}
    (hc : Tendsto f 𝒰 (𝓝 c)) : (exists_tendsto 𝒰 a).choose = c :=
  tendsto_nhds_unique (tendsto_choose 𝒰 a f hf) hc

def stdPart (F : Type) [NormedField F] [ProperSpace F] : bddRing 𝒰 F →+* F where
  toFun a := (exists_tendsto 𝒰 a).choose
  map_one' := choose_eq 𝒰 1 (fun _ => 1) rfl tendsto_const_nhds
  map_zero' := choose_eq 𝒰 0 (fun _ => 0) rfl tendsto_const_nhds
  map_mul' := by
    rintro a b
    obtain ⟨_, f, hf, -⟩ := a.2
    obtain ⟨_, g, hg, -⟩ := b.2
    exact choose_eq 𝒰 _ (f * g) (by rw [Germ.coe_mul, ← hf, ← hg]; rfl)
      ((tendsto_choose 𝒰 a f hf).mul (tendsto_choose 𝒰 b g hg))
  map_add' := by
    rintro a b
    obtain ⟨_, f, hf, -⟩ := a.2
    obtain ⟨_, g, hg, -⟩ := b.2
    exact choose_eq 𝒰 _ (f + g) (by rw [Germ.coe_add, ← hf, ← hg]; rfl)
      ((tendsto_choose 𝒰 a f hf).add (tendsto_choose 𝒰 b g hg))

theorem tendsto_stdPart (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) :
    Tendsto f 𝒰 (𝓝 (stdPart 𝒰 F a)) := tendsto_choose 𝒰 a f hf

theorem stdPart_constBdd (a : F) : stdPart 𝒰 F (constBdd 𝒰 F a) = a :=
  choose_eq 𝒰 _ (fun _ => a) rfl tendsto_const_nhds

end Ultrapower

theorem valR_mul_pow {C : Type} [CommRing C] {X : Scheme.{0}} {U V : X.Opens} (h : Γ(X, U))
    (hV : X.basicOpen h ≤ V) (f : Γ(X, V)) (n : ℕ) (a : Γ(X, U))
    (ha : (X.presheaf.map (homOfLE hV).op).hom f * algebraMap Γ(X, U) Γ(X, X.basicOpen h) h ^ n =
      algebraMap Γ(X, U) Γ(X, X.basicOpen h) a)
    (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ X.basicOpen h) : valR y V f * valR y U h ^ n = valR y U a := by
  have h1 := congrArg (valR y (X.basicOpen h)) ha
  rw [valR_mul y _ hy, valR_pow y _ hy, valR_res y hV hy] at h1
  have h2 : ∀ t : Γ(X, U), valR y (X.basicOpen h) (algebraMap Γ(X, U) Γ(X, X.basicOpen h) t) =
      valR y U t := fun t => valR_res y (X.basicOpen_le h) hy t
  rwa [h2, h2] at h1

section Limit

variable {I F : Type} [Field F] (𝒰 : Ultrafilter I) {X : Scheme.{0}} (e : I → (Sp F ⟶ X)) {U : X.Opens}

def germVal (hl : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ U) : Γ(X, U) →+* (𝒰 : Filter I).Germ F where
  toFun f := ((fun i => valR (e i) U f : I → F) : (𝒰 : Filter I).Germ F)
  map_one' := Germ.coe_eq.2 (hl.mono fun _ hi => valR_one _ U hi)
  map_mul' f g := Germ.coe_eq.2 (hl.mono fun _ hi => valR_mul _ U hi f g)
  map_zero' := Germ.coe_eq.2 (hl.mono fun _ hi => valR_zero _ U hi)
  map_add' f g := Germ.coe_eq.2 (hl.mono fun _ hi => valR_add _ U hi f g)

theorem exists_germPoint [CompactSpace X] : ∃ ξ : Sp ((𝒰 : Filter I).Germ F) ⟶ X, ∀ V : X.Opens, ⊤ ≤ ξ ⁻¹ᵁ V →
    (∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ V) ∧
      ∀ f : Γ(X, V), valR ξ V f = ((fun i => valR (e i) V f : I → F) : (𝒰 : Filter I).Germ F) := by
  obtain ⟨z, hz⟩ : ∃ z : X, Tendsto (fun i => e i (IsLocalRing.closedPoint F)) 𝒰 (𝓝 z) :=
    ⟨_, (𝒰.map fun i => e i (IsLocalRing.closedPoint F)).le_nhds_lim⟩
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial
  have hl : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ U :=
    (hz.eventually (U.isOpen.mem_nhds hzU)).mono fun i hi => (le_preimage_iff _ _).2 hi
  let ξ : Sp ((𝒰 : Filter I).Germ F) ⟶ X := Spec.map (CommRingCat.ofHom (germVal 𝒰 e hl)) ≫ hU.fromSpec
  have hξ : ⊤ ≤ ξ ⁻¹ᵁ U := le_preimage_specMap_fromSpec hU _
  have hval : ∀ f, valR ξ U f = germVal 𝒰 e hl f := fun f => by
    rw [valR_eq ξ U hξ, valMap_specMap_fromSpec]
    rfl
  refine ⟨ξ, fun V hV => ?_⟩
  obtain ⟨h, hhV, hh⟩ := hU.exists_basicOpen_le (V := V) ⟨_, (le_preimage_iff ξ V).1 hV⟩
    ((le_preimage_iff ξ U).1 hξ)
  have hξh : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen h := (le_preimage_iff ξ _).2 hh
  have hne : germVal 𝒰 e hl h ≠ 0 := by
    rw [← hval]
    exact ((le_preimage_basicOpen_iff ξ hξ h).1 hξh).ne_zero
  have hl' : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ X.basicOpen h := by
    have h0 : ¬ ∀ᶠ i in (𝒰 : Filter I), valR (e i) U h = 0 := fun h0 => hne (Germ.coe_eq.2 h0)
    filter_upwards [hl, Ultrafilter.eventually_not.2 h0] with i h1 h2
      using (le_preimage_basicOpen_iff _ h1 h).2 (Ne.isUnit h2)
  refine ⟨hl'.mono fun i hi => le_preimage_mono _ hhV hi, fun f => ?_⟩
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((X.presheaf.map (homOfLE hhV).op).hom f)
  have h1 := valR_mul_pow h hhV f n a ha ξ hξh
  rw [hval, hval] at h1
  apply mul_right_cancel₀ (pow_ne_zero n hne)
  rw [h1, ← map_pow]
  refine Germ.coe_eq.2 ?_
  filter_upwards [hl, hl'] with i h2 h3
  have := valR_mul_pow h hhV f n a ha (e i) h3
  rw [← valR_pow _ _ h2] at this
  exact this.symm

end Limit

theorem compactSpace_pts {F : Type} [NormedField F] [ProperSpace F] {X : Scheme.{0}} (p : X ⟶ Sp F)
    [UniversallyClosed p] : CompactSpace (Pts p) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  refine ⟨isCompact_iff_ultrafilter_le_nhds.2 fun 𝒰 _ => ?_⟩
  obtain ⟨ξ, hξ⟩ := exists_germPoint 𝒰 (fun x : Pts p => x.1)
  have hE : ValuativeCriterion.Existence p :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed p) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) p).1
  have hw : ξ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (bddRing 𝒰 F) ((𝒰 : Filter (Pts p)).Germ F))) ≫
      spMap (constBdd 𝒰 F) := by
    rw [← Spec.map_comp, ← Spec.map_preimage (ξ ≫ p)]
    congr 1
    ext a
    refine (valR_constFn p ξ ⊤ (le_preimage_top _) a).symm.trans ?_
    rw [(hξ ⊤ (le_preimage_top _)).2]
    exact Germ.coe_eq.2 (Eventually.of_forall fun x => valR_constFn_of_section p x.1 x.2 ⊤ (le_preimage_top _) a)
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Sp (bddRing 𝒰 F) ⟶ X,
      spMap (algebraMap (bddRing 𝒰 F) ((𝒰 : Filter (Pts p)).Germ F)) ≫ l = ξ ∧ l ≫ p = spMap (constBdd 𝒰 F) := by
    obtain ⟨⟨l, hl, hl'⟩⟩ := (hE
      { R := bddRing 𝒰 F, K := (𝒰 : Filter (Pts p)).Germ F, i₁ := ξ, i₂ := spMap (constBdd 𝒰 F),
        commSq := ⟨hw⟩ }).exists_lift
    exact ⟨l, hl, hl'⟩
  have hx : (spMap (stdPart 𝒰 F) ≫ l) ≫ p = 𝟙 _ := by
    rw [Category.assoc, hl₂, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact stdPart_constBdd 𝒰 a
  refine ⟨⟨_, hx⟩, trivial, ?_⟩
  obtain ⟨V, hV, hlV, -⟩ := exists_isAffineOpen_le (C := bddRing 𝒰 F) l (le_preimage_top _)
  have hξV : ⊤ ≤ ξ ⁻¹ᵁ V := hl₁ ▸ le_preimage_comp _ l hlV (le_preimage_top _)
  have H : Tendsto (fun x : Pts p => x.1) 𝒰 (𝓝 (spMap (stdPart 𝒰 F) ≫ l)) := by
    refine tendsto_of_isAffineOpen hV (le_preimage_comp _ l hlV (le_preimage_top _)) (hξ V hξV).1 fun f => ?_
    rw [valR_spMap_comp _ l V hlV]
    refine tendsto_stdPart 𝒰 _ _ ?_
    rw [← (hξ V hξV).2, ← hl₁, valR_spMap_comp _ l V hlV]
    rfl
  exact tendsto_id'.1 (tendsto_subtype_rng.2 H)

end GlobalTheory.ProperPoints
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaHaarModulusCmFieldElement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaHaarModulusCmFieldElement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem algebraMap_eq_inclR_mul_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (u : E) (k : F) (hk : algebraMap F E k = u * σ u) :
    algebraMap R (R ⊗[F] E) (algebraMap F R k) = inclR R u * sigR R σ (inclR R u) := by
  have h1 : sigR R σ (inclR R u) = inclR R (σ u) := by
    simp [sigR, inclR]
  rw [h1, ← map_mul, ← hk, ← IsScalarTower.algebraMap_apply]
  exact ((Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes k).symm

theorem prod_modu_inclR : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ u : E, u ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u)).Finite ∧ modu (Ainf F ⊗[F] E) (inclR (Ainf F) u) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) = 1 := by
  intro F E _ _ _ _ _ σ h u hu
  haveI := h.1
  obtain ⟨k, hk⟩ := GlobalTheory.HermLineZeros.exists_of_fixed h (u * σ u) (by
    rw [map_mul, GlobalTheory.HermLineZeros.conj_invol h, mul_comm])
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact mul_ne_zero hu ((map_ne_zero σ).2 hu) hk.symm
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) =
      modu (Fv F v) (algebraMap F (Fv F v) k) := fun v =>
    (GlobalTheory.T.haarModulus_tensor_eq_modulus_norm F E σ h (Fv F v) _ _ (hu.isUnit.map _)
      (algebraMap_eq_inclR_mul_sigR σ _ u k hk)).2
  have hi : modu (Ainf F ⊗[F] E) (inclR (Ainf F) u) = modu (Ainf F) (algebraMap F (Ainf F) k) :=
    (GlobalTheory.T.haarModulus_tensor_eq_modulus_norm F E σ h (Ainf F) _ _ (hu.isUnit.map _)
      (algebraMap_eq_inclR_mul_sigR σ _ u k hk)).2
  simp only [hv, hi]
  exact GlobalTheory.T.haarModulus_product_formula_totallyReal F k hk0

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaHaarModulusCmFieldElementStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_formula_haarModulus_cmField_element : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ u : E, u ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u)).Finite ∧ modu (Ainf F ⊗[F] E) (inclR (Ainf F) u) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) = 1 := by
  first | exact @GlobalTheory.GaugeEx.prod_modu_inclR | exact GlobalTheory.GaugeEx.prod_modu_inclR | (intros; apply GlobalTheory.GaugeEx.prod_modu_inclR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightedProjectiveEmbeddingSep
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

namespace GlobalTheory.AmpleSeparateOverRing

theorem isSeparated_toSpecZ (R : Type) [CommRing R] (n : ℕ) :
    IsSeparated (specZIsTerminal.from (PSpace R n)) := by
  have : IsProper (PSpace.str R n) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R n
  rw [specZIsTerminal.hom_ext (specZIsTerminal.from (PSpace R n)) (PSpace.str R n ≫ specZIsTerminal.from _)]
  infer_instance

theorem exists_ample_model (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R)
    (ι : Type) (L : ι → LB X) (hL : ∀ i, (L i).IsLB) (M : ι → ℕ)
    (t : ∀ i, Fin (M i + 1) → (L i).Sec)
    (ht : ∀ i, ⨆ m, nonzeroLocus (t i m) = ⊤) (w : ι → ℕ) (hw : ∀ i, 1 ≤ w i)
    (T : Finset ι) :
    ∃ (Q : Scheme.{0}) (Ψ : X ⟶ Q) (r : Q ⟶ Sp R) (N : LB Q) (hN : IsAmpleLB N), IsSeparated r ∧
      Ψ ≫ r = f ∧
      CechPic.cls (N.pull Ψ) (LB.isLB_pull hN.isLB Ψ) = ∑ i ∈ T, (w i : ℤ) • CechPic.cls (L i) (hL i) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (a a' : Sp K ⟶ X), a ≫ Ψ = a' ≫ Ψ →
        a ≫ f = a' ≫ f ∧ ∀ i ∈ T,
          a ≫ ProjSpace.toProj f (t i) (ht i) = a' ≫ ProjSpace.toProj f (t i) (ht i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨Sp R, f, 𝟙 _, LB.triv _, isAmpleLB_of_isAffine (LB.isLB_triv _), inferInstance,
      Category.comp_id _, ?_, ?_⟩
    · rw [Finset.sum_empty]
      exact map_zero (CechPic.pull f)
    · intro K _ _ a a' h
      exact ⟨h, by simp⟩
  | insert i T hi ih =>
    obtain ⟨Q, Ψ, r, N, hN, hr, hΨ, hc, hinj⟩ := ih
    have hO1 := ProjSpace.O1_isLB R (M i)
    have hO : IsAmpleLB (lbPow (ProjSpace.O1 R (M i)) (w i)) :=
      (isAmpleLB_pow_iff hO1 (hw i)).2 (isAmple_projective_O_one R (M i))
    have : IsSeparated (specZIsTerminal.from (PSpace R (M i))) := isSeparated_toSpecZ R (M i)
    have hNp := LB.isLB_pull hN.isLB (pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i))))
    have hOq := LB.isLB_pull hO.isLB (pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i))))
    have hN' := CechPic.isLB_tens hNp hOq
    have hA : IsAmpleLB (CechPic.tens
        (N.pull (pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))))
        ((lbPow (ProjSpace.O1 R (M i)) (w i)).pull
          (pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))))) := by
      refine hN.box hO hN' (IsPullback.of_hasPullback _ _) ?_
      refine (CechPic.cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN' hNp) hOq)).1 ?_
      rw [CechPic.cls_div (LB.isLB_div hN' hNp) hOq, CechPic.cls_div hN' hNp, CechPic.cls_tens hNp hOq]
      abel
    refine ⟨_, pullback.lift Ψ (ProjSpace.toProj f (t i) (ht i)) (specZIsTerminal.hom_ext _ _),
      pullback.fst _ _ ≫ r, _, hA, inferInstance, by rw [← Category.assoc, pullback.lift_fst, hΨ], ?_, ?_⟩
    · rw [Finset.sum_insert hi, ← hc]
      have e := (CechPic.cls_eq_iff (LB.isLB_pull hO1 (ProjSpace.toProj f (t i) (ht i))) (hL i)).2
        (ProjSpace.lbIso_pullback_O1_toProj f (t i) (ht i))
      rw [← e, CechPic.cls_pull hN' _, CechPic.cls_tens hNp hOq, map_add (f := _), CechPic.cls_pull hN.isLB,
        CechPic.cls_pull hO.isLB, ← CechPic.pull_comp, ← CechPic.pull_comp, pullback.lift_fst,
        pullback.lift_snd, CechPic.cls_lbPow hO1, map_nsmul, CechPic.cls_pull hN.isLB,
        CechPic.cls_pull hO1, add_comm, natCast_zsmul]
    · intro K _ _ a a' h
      have h1 : a ≫ Ψ = a' ≫ Ψ := by
        have := congrArg (· ≫ pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))) h
        simp only [Category.assoc] at this
        rwa [pullback.lift_fst] at this
      have h2 : a ≫ ProjSpace.toProj f (t i) (ht i) = a' ≫ ProjSpace.toProj f (t i) (ht i) := by
        have := congrArg (· ≫ pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))) h
        simp only [Category.assoc] at this
        rwa [pullback.lift_snd] at this
      obtain ⟨e1, e2⟩ := hinj K a a' h1
      refine ⟨e1, fun j hj => ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact h2
      · exact e2 j hj

end GlobalTheory.AmpleSeparateOverRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizer
noncomputable section

namespace GlobalTheory.LevelUnram

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem exists_mul_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R) (hP : P.IsPrime) (t : R)
    (ht : t ∈ P) (ht2 : t ∉ P ^ 2) (a : R) (ha : a ∈ P) : ∃ s b, s ∉ P ∧ s * a = t * b := by
  obtain ⟨I, hI⟩ : P ∣ Ideal.span {t} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact ht
  have hIP : ¬ I ≤ P := by
    intro h
    apply ht2
    rw [← Ideal.span_singleton_le_iff_mem, hI, sq]
    exact Ideal.mul_mono_right h
  obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.1 hIP
  have h1 : a * s ∈ Ideal.span {t} := by rw [hI]; exact Ideal.mul_mem_mul ha hs
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 h1
  exact ⟨s, b, hsP, by rw [mul_comm, hb]⟩

variable {E : Type} [Field E] [NumberField E]

theorem absNorm_span_invol (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) :
    Ideal.absNorm (Ideal.span {s a}) = Ideal.absNorm (Ideal.span {a}) := by
  let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom s s (RingHom.ext hs) (RingHom.ext hs)
  let e' : 𝓞 E ≃ₐ[ℤ] 𝓞 E := AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv e' a)

theorem notMem_sq {ι : Type} [Fintype ι] (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) (p : ℕ) (hp : p.Prime)
    (ha : a * s a = (p : 𝓞 E)) (hcard : 2 * Fintype.card ι = Module.finrank ℚ E) (P : ι → Ideal (𝓞 E))
    (hmax : ∀ i, (P i).IsMaximal) (hinj : Function.Injective P) (haP : ∀ i, a ∈ P i)
    (hN : ∀ i, Ideal.absNorm (P i) = p) (i : ι) (hsa : s a ∉ P i) : (p : 𝓞 E) ∉ P i ^ 2 := by
  classical
  intro hmem
  have hnorm : Ideal.absNorm (Ideal.span {a}) = p ^ Fintype.card ι := by
    have h1 : Ideal.absNorm (Ideal.span {a}) ^ 2 = (p ^ Fintype.card ι) ^ 2 := by
      rw [← pow_mul, mul_comm, hcard, ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, ← ha,
        ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_invol s hs, sq]
    exact Nat.pow_left_injective two_ne_zero h1
  have ha2 : a ∈ P i ^ 2 := by
    obtain ⟨y, m, hm, h⟩ := (hmax i).exists_inv hsa
    have h1 : a = y * (p : 𝓞 E) + m * a := by
      rw [← ha]
      linear_combination (-a) * h
    rw [h1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) ?_
    rw [sq]
    exact Ideal.mul_mem_mul hm (haP i)
  have hcop : ∀ j k, j ≠ k → IsCoprime (P j) (P k) := fun j k hjk =>
    Ideal.isCoprime_iff_sup_eq.2 ((hmax j).coprime_of_ne (hmax k) (fun h => hjk (hinj h)))
  have hd1 : P i ^ 2 ∣ Ideal.span {a} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact ha2
  have hd2 : ∏ j ∈ Finset.univ.erase i, P j ∣ Ideal.span {a} := by
    refine Finset.prod_dvd_of_coprime (fun j _ k _ hjk => hcop j k hjk) ?_
    intro j _
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact haP j
  have hc : IsCoprime (P i ^ 2) (∏ j ∈ Finset.univ.erase i, P j) :=
    IsCoprime.pow_left (IsCoprime.prod_right fun j hj => hcop i j (Finset.ne_of_mem_erase hj).symm)
  have hd := map_dvd Ideal.absNorm (hc.mul_dvd hd1 hd2)
  rw [hnorm, map_mul, map_pow, map_prod, hN i,
    Finset.prod_congr rfl (fun j _ => hN j), Finset.prod_const, ← pow_add,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
  have h3 := Finset.card_erase_add_one (Finset.mem_univ i)
  rw [Finset.card_univ] at h3
  omega

theorem finrank_E (D : D7) : 2 * D.R.f = Module.finrank ℚ D.host.E := by
  letI := D.host.cmStar
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have h2 : Module.finrank ℚ D.host.F = D.R.f := by
    rw [D.host.finrank_hostF, Ranks.f, Ranks.n]
  rw [D.sp.cm.deg2, h2] at h1
  omega

theorem unram (D : D7) (u : D.what₂.Word) (A : AtTTied u) (v : (D.mem u).A.vT) :
    Unram (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (sigD D : D.host.E →+* D.host.E)
  have hsc : ∀ x, (s x : D.host.E) = D.host.conj (x : D.host.E) := fun x => forms_involution_eq_host_conj _
  have hs : ∀ x, s (s x) = x := fun x => RingOfIntegers.ext (by rw [hsc, hsc, host_conj_involutive])
  have ha : A.piU * s A.piU = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have := A.piU_norm
    rw [← hsc] at this
    simpa using this
  have hT0 : A.res v (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) = 0 := by
    rw [← ha, map_mul, A.res_pi, zero_mul]
  have h2 := notMem_sq s hs A.piU _ (D.mem u).A.T_prime ha (by rw [(D.mem u).A.card_vT]; exact finrank_E D)
    (fun w => RingHom.ker (A.res w)) (fun w => RingHom.ker_isMaximal_of_surjective _ (A.res_surj w))
    (fun w w' h => by
      apply A.eV.injective
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      ext x
      have h' : RingHom.ker (A.res w) = RingHom.ker (A.res w') := h
      rw [A.res_v, A.res_v, ← RingHom.mem_ker, ← RingHom.mem_ker, h'])
    (fun w => A.res_pi w)
    (fun w => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_congr (RingHom.quotientKerEquivOfSurjective (A.res_surj w)).toEquiv, Nat.card_eq_fintype_card,
        (D.mem u).A.card_Fv w])
    v (A.res_conj v _ (hsc _))
  exact ⟨hT0, fun a h => exists_mul_eq _ (RingHom.ker_isPrime _) _ hT0 h2 a h⟩

end GlobalTheory.LevelUnram

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizerStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_unramifiedUniformizer : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (v : (D.mem u).A.vT), Unram (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  first | exact @GlobalTheory.LevelUnram.unram | exact GlobalTheory.LevelUnram.unram | (intros; apply GlobalTheory.LevelUnram.unram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicFormValuesNearPointSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicFormValuesNearPointSpec
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.ValAt

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem atV_mul {v : HeightOneSpectrum (𝓞 F)} {η η' : GA σ J} (h : AtV v η) (h' : AtV v η') : AtV v (η * η') := by
  intro v' hv'
  rw [Subgroup.coe_mul, map_mul, h v' hv', h' v' hv', one_mul]

theorem atV_inv {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J} (h : AtV v η) : AtV v η⁻¹ := by
  intro v' hv'
  rw [Subgroup.coe_inv, map_inv, h v' hv', inv_one]

theorem inv_loc {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hb : v ∉ bad) (g) (hg : g ∈ AdFun S emb) (x κ : GA σ J) (hκ : AtV v κ)
    (hU : bc (prV (E := E) v) κ.1 ∈ S.Uloc v) : g (x * κ) = g x := by
  have hm : κ.1 ∈ S.U := by
    refine (S.U_eq _).2 ⟨κ.2, fun v' => ?_⟩
    by_cases h : v' = v
    · subst h; exact hU
    · rw [hκ v' h]; exact Subgroup.one_mem _
  have hc : S.chi ⟨κ.1, hm⟩ = 1 := S.chi_triv _ (fun v' hv' => hκ v' (fun h => hb (h ▸ hv')))
  funext y
  have := hg 1 (Subgroup.one_mem _) x (x * κ) ⟨κ.1, hm⟩ (by rw [map_one, one_mul]; rfl) y y
    (fun τ => by simp [atInf])
  rw [this, hc, Units.val_one, one_mul]

theorem val_self {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : Type} [Field k]
    (p : GA σ J → Pr (𝓞 E) (Fin n → E) k) (hb : v ∉ bad) (hp : PMap S v hv p) (g) (hg : g ∈ AdFun S emb)
    (x η : GA σ J) (hη : AtV v η) : valAt v p g x (p (x * η)) = g (x * η) := by
  have h : ∃ η', AtV v η' ∧ p (x * η') = p (x * η) := ⟨η, hη, rfl⟩
  unfold valAt
  rw [dite_eq_left h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  generalize h.choose = η0 at h1 h2
  have e : x * η = x * η0 * (η0⁻¹ * η) := by group
  rw [e]
  refine (inv_loc S emb v hb g hg _ _ (atV_mul (atV_inv h1) hη) ?_).symm
  exact (hp.2.1 (x * η0) _).1 (by rw [← e, h2])

end

theorem valAt_spec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ g ∈ AdFun S emb, (∀ x η : GA σ J, AtV v η → valAt v p g x (p (x * η)) = g (x * η)) ∧ (∀ x η : GA σ J, AtV v η → valAt v p g (x * η) = valAt v p g x) ∧ ∀ (a : ℤ) (δ x : GA σ J) (q : Pr (𝓞 E) (Fin n → E) k), (a : k) ≠ 0 → IsDia S v hv a δ → valAt v p g x (q.dil (a : k)) = valAt v p (fun y => g (y * δ)) x q := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hp g hg
  have key := val_self S emb v hv p hb hp g hg
  refine ⟨key, fun x η hη => ?_, fun a δ x q ha hδ => ?_⟩
  · funext q
    by_cases h : ∃ η', AtV v η' ∧ p (x * η * η') = q
    · obtain ⟨η', h1, rfl⟩ := h
      rw [key _ _ h1, mul_assoc, key _ _ (atV_mul hη h1)]
    · have h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q := by
        rintro ⟨η', h1, h2⟩
        refine h ⟨η⁻¹ * η', atV_mul (atV_inv hη) h1, ?_⟩
        rw [← h2]; congr 1; group
      unfold valAt
      rw [dite_eq_right h, dite_eq_right h']
  · have hδv : AtV v δ := hδ.1
    by_cases h : ∃ η', AtV v η' ∧ p (x * η') = q
    · have hR : valAt v p (fun y => g (y * δ)) x q = g (x * h.choose * δ) := by
        unfold valAt
        rw [dite_eq_left h]
      obtain ⟨h1, h2⟩ := h.choose_spec
      rw [hR]
      generalize h.choose = η0 at h1 h2
      rw [← h2, ← hp.2.2 _ δ a hδ, mul_assoc, key _ _ (atV_mul h1 hδv)]
    · have h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q.dil (a : k) := by
        rintro ⟨η', h1, h2⟩
        refine h ⟨η' * δ⁻¹, atV_mul h1 (atV_inv hδv), ?_⟩
        have h3 := hp.2.2 (x * (η' * δ⁻¹)) δ a hδ
        have e : x * (η' * δ⁻¹) * δ = x * η' := by group
        rw [e, h2] at h3
        have h4 := congrArg (Pr.dil (a : k)⁻¹) h3
        rw [Pr.dil_dil, Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one, Pr.dil_one] at h4
        exact h4.symm
      unfold valAt
      rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.LevelHecke.ValAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicFormValuesNearPointSpecStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicForm_values_near_point_spec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ g ∈ AdFun S emb, (∀ x η : GA σ J, AtV v η → valAt v p g x (p (x * η)) = g (x * η)) ∧ (∀ x η : GA σ J, AtV v η → valAt v p g (x * η) = valAt v p g x) ∧ ∀ (a : ℤ) (δ x : GA σ J) (q : Pr (𝓞 E) (Fin n → E) k), (a : k) ≠ 0 → IsDia S v hv a δ → valAt v p g x (q.dil (a : k)) = valAt v p (fun y => g (y * δ)) x q := by
  first | exact @GlobalTheory.LevelHecke.ValAt.valAt_spec | exact GlobalTheory.LevelHecke.ValAt.valAt_spec | (intros; apply GlobalTheory.LevelHecke.ValAt.valAt_spec <;> assumption)
end
end
