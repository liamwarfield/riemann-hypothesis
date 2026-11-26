module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSections
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfCommuteOfSeparable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.TorusCh

def IsPol {K : Type} [Field K] {n : ℕ} (γ e : Matrix (Fin n) (Fin n) K) : Prop := ∃ f : K[X], e = aeval γ f

structure IsPrim {K : Type} [Field K] {n : ℕ} (γ e : Matrix (Fin n) (Fin n) K) : Prop where
  pol : IsPol γ e
  idem : e * e = e
  ne : e ≠ 0
  inv : ∀ h : K[X], aeval γ h * e ≠ 0 → ∃ h' : K[X], aeval γ h' * (aeval γ h * e) = e

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def sg (d : GL (Fin n) E) (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  d.val * (X.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val

def rm (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (Ad E) := X.map (algebraMap E (Ad E))

def chi (e : Matrix (Fin n) (Fin n) E) (t : GA E n) : Ad E := (1 + rm e * (t.val - 1)).det

def lam (e : Matrix (Fin n) (Fin n) E) (t : GA E n) : ℝ := logAbs (chi e t)

section Pol

variable {K : Type} [Field K] {n : ℕ}

theorem pol_comm (γ a b : Matrix (Fin n) (Fin n) K) (ha : IsPol γ a) (hb : IsPol γ b) : a * b = b * a := by
  obtain ⟨f, rfl⟩ := ha
  obtain ⟨g, rfl⟩ := hb
  rw [← map_mul, mul_comm, map_mul]

theorem isPol_iff (γ e : Matrix (Fin n) (Fin n) K) : IsPol γ e ↔ e ∈ Algebra.adjoin K {γ} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨fun ⟨f, h⟩ => ⟨f, h.symm⟩, fun ⟨f, h⟩ => ⟨f, h.symm⟩⟩

theorem img_of_pol (γ : GL (Fin n) K) (p : Matrix (Fin n) (Fin n) K) (hp : IsPol γ.val p) :
    img γ (LinearMap.range (Matrix.toLin' p)) = LinearMap.range (Matrix.toLin' p) := by
  have hc : γ.val * p = p * γ.val := pol_comm γ.val _ _ ⟨X, (aeval_X _).symm⟩ hp
  have hs : LinearMap.range (Matrix.toLin' γ.val) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ⟨(γ⁻¹ : GL (Fin n) K).val *ᵥ y, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  unfold img
  rw [← LinearMap.range_comp, ← Matrix.toLin'_mul, hc, Matrix.toLin'_mul, LinearMap.range_comp, hs, Submodule.map_top]

theorem mem_range_idem {a : Matrix (Fin n) (Fin n) K} (ha : a * a = a) (w : Fin n → K) :
    w ∈ LinearMap.range (Matrix.toLin' a) ↔ a *ᵥ w = w := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ha]
  · intro h
    exact ⟨w, by rw [Matrix.toLin'_apply, h]⟩

theorem mul_eq_of_range_le {a b : Matrix (Fin n) (Fin n) K} (hb : b * b = b)
    (h : LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b)) : b * a = a := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  have h1 : a *ᵥ y ∈ LinearMap.range (Matrix.toLin' b) := h ⟨y, by rw [Matrix.toLin'_apply]⟩
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  exact (mem_range_idem hb _).1 h1

theorem idem_facts (γ a b : Matrix (Fin n) (Fin n) K) (ha : IsPol γ a) (hb : IsPol γ b)
    (ha2 : a * a = a) (hb2 : b * b = b) :
    (LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b) → a * b = a) ∧
    (LinearMap.range (Matrix.toLin' a) = LinearMap.range (Matrix.toLin' b) → a = b) ∧
    LinearMap.range (Matrix.toLin' (a * b)) =
      LinearMap.range (Matrix.toLin' a) ⊓ LinearMap.range (Matrix.toLin' b) := by
  have hc := pol_comm γ a b ha hb
  refine ⟨fun h => by rw [hc]; exact mul_eq_of_range_le hb2 h, fun h => ?_, ?_⟩
  · have h1 := mul_eq_of_range_le hb2 h.le
    have h2 := mul_eq_of_range_le ha2 h.ge
    rw [← h1, ← hc, h2]
  · apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      refine ⟨⟨b *ᵥ y, ?_⟩, ⟨a *ᵥ y, ?_⟩⟩
      · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hc]
    · rintro w ⟨h1, h2⟩
      have h1' := (mem_range_idem ha2 w).1 h1
      have h2' := (mem_range_idem hb2 w).1 h2
      refine ⟨w, ?_⟩
      rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, h2', h1']

end Pol

section Chi

theorem uu_mul {R : Type} [Ring R] (A t t' : R) (hA : A * A = A) (ht : t * A = A * t) :
    (1 + A * (t - 1)) * (1 + A * (t' - 1)) = 1 + A * (t * t' - 1) := by
  have h1 : (t - 1) * A = A * (t - 1) := by rw [sub_mul, mul_sub, ht, one_mul, mul_one]
  have h2 : A * (t - 1) * (A * (t' - 1)) = A * (t - 1) * (t' - 1) := by
    calc A * (t - 1) * (A * (t' - 1)) = A * ((t - 1) * A) * (t' - 1) := by simp only [mul_assoc]
      _ = (A * A) * (t - 1) * (t' - 1) := by rw [h1]; simp only [mul_assoc]
      _ = _ := by rw [hA]
  rw [mul_add, add_mul, add_mul, h2]
  noncomm_ring

theorem uu_add {R : Type} [Ring R] (A B x : R) (hAB : A * B = 0) (hx : x * B = B * x) :
    (1 + A * x) * (1 + B * x) = 1 + (A + B) * x := by
  have h2 : A * x * (B * x) = 0 := by
    calc A * x * (B * x) = A * (x * B) * x := by simp only [mul_assoc]
      _ = (A * B) * x * x := by rw [hx]; simp only [mul_assoc]
      _ = 0 := by rw [hAB]; simp
  rw [mul_add, add_mul, add_mul, h2]
  noncomm_ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem rm_mul (a b : Matrix (Fin n) (Fin n) E) : rm (a * b) = rm a * rm b := Matrix.map_mul

theorem rm_add (a b : Matrix (Fin n) (Fin n) E) : rm (a + b) = rm a + rm b := by
  ext i j; simp [rm]

theorem rm_zero : rm (0 : Matrix (Fin n) (Fin n) E) = 0 := by
  ext i j; simp [rm]

theorem comm_inv {e : Matrix (Fin n) (Fin n) E} {t : GA E n} (ht : t.val * rm e = rm e * t.val) :
    (t⁻¹ : GA E n).val * rm e = rm e * (t⁻¹ : GA E n).val := by
  calc (t⁻¹ : GA E n).val * rm e = (t⁻¹ : GA E n).val * (rm e * (t.val * (t⁻¹ : GA E n).val)) := by
        rw [Units.mul_inv, mul_one]
    _ = (t⁻¹ : GA E n).val * (t.val * rm e) * (t⁻¹ : GA E n).val := by
        rw [ht]; simp only [mul_assoc]
    _ = rm e * (t⁻¹ : GA E n).val := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem chi_mul (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t t' : GA E n)
    (ht : t.val * rm e = rm e * t.val) : chi e (t * t') = chi e t * chi e t' := by
  unfold chi
  rw [← Matrix.det_mul, uu_mul (rm e) t.val t'.val (by rw [← rm_mul, he]) ht, Units.val_mul]

theorem chi_one (e : Matrix (Fin n) (Fin n) E) : chi e (1 : GA E n) = 1 := by
  simp [chi]

theorem chi_isUnit (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n)
    (ht : t.val * rm e = rm e * t.val) : IsUnit (chi e t) :=
  IsUnit.of_mul_eq_one (chi e t⁻¹) (by rw [← chi_mul e he t _ ht, mul_inv_cancel, chi_one])

theorem lam_mul (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t t' : GA E n) (ht : t.val * rm e = rm e * t.val)
    (ht' : t'.val * rm e = rm e * t'.val) : lam e (t * t') = lam e t + lam e t' := by
  unfold lam
  rw [chi_mul e he t t' ht]
  exact GlobalTheory.CompanionTheory.LogAbs.logAbs_mul _ _ (chi_isUnit e he t ht) (chi_isUnit e he t' ht')

theorem lam_inv (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n) (ht : t.val * rm e = rm e * t.val) :
    lam e t⁻¹ = - lam e t := by
  have h := lam_mul e he t t⁻¹ ht (comm_inv ht)
  have h0 : lam e (1 : GA E n) = 0 := by
    rw [lam, chi_one, ← map_one (algebraMap E (Ad E))]
    exact GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap 1 one_ne_zero
  rw [mul_inv_cancel, h0] at h
  linarith

theorem lam_zero (t : GA E n) : lam (0 : Matrix (Fin n) (Fin n) E) t = 0 := by
  have h1 : chi (0 : Matrix (Fin n) (Fin n) E) t = algebraMap E (Ad E) 1 := by
    simp [chi, rm_zero]
  rw [lam, h1]
  exact GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap 1 one_ne_zero

theorem chi_add (a b : Matrix (Fin n) (Fin n) E) (hab : a * b = 0) (t : GA E n)
    (hb : t.val * rm b = rm b * t.val) : chi (a + b) t = chi a t * chi b t := by
  unfold chi
  have h1 : (t.val - 1) * rm b = rm b * (t.val - 1) := by rw [sub_mul, mul_sub, hb, one_mul, mul_one]
  rw [← Matrix.det_mul, uu_add (rm a) (rm b) _ (by rw [← rm_mul, hab, rm_zero]) h1, rm_add]

theorem lam_sum {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) E) (hf : ∀ i ∈ s, f i * f i = f i)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) (t : GA E n) (ht : ∀ i ∈ s, t.val * rm (f i) = rm (f i) * t.val) :
    lam (∑ i ∈ s, f i) t = ∑ i ∈ s, lam (f i) t := by
  classical
  have key : (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, f i ∧
      t.val * rm (∑ i ∈ s, f i) = rm (∑ i ∈ s, f i) * t.val ∧ lam (∑ i ∈ s, f i) t = ∑ i ∈ s, lam (f i) t := by
    induction s using Finset.induction_on with
    | empty => simp [rm_zero, lam_zero]
    | insert a s ha ih =>
      obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
        (fun i hi => ht i (Finset.mem_insert_of_mem hi))
      have haa := hf a (Finset.mem_insert_self _ _)
      have hta := ht a (Finset.mem_insert_self _ _)
      have hl : f a * ∑ i ∈ s, f i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => ho a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
      have hr : (∑ i ∈ s, f i) * f a = 0 := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_zero fun i hi => ho i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self _ _)
          (fun h => ha (h ▸ hi))
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine ⟨?_, ?_, ?_⟩
      · rw [add_mul, mul_add, mul_add, hl, hr, haa, h1]; simp
      · rw [rm_add, mul_add, add_mul, hta, h2]
      · unfold lam at h3 ⊢
        rw [chi_add _ _ hl t h2, GlobalTheory.CompanionTheory.LogAbs.logAbs_mul _ _ (chi_isUnit _ haa t hta) (chi_isUnit _ h1 t h2), h3]
  exact key.2.2

theorem lam_rat (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (r : GL (Fin n) E)
    (hr : (ratGL E n r).val * rm e = rm e * (ratGL E n r).val) : lam e (ratGL E n r) = 0 := by
  have h1 : chi e (ratGL E n r) = algebraMap E (Ad E) (1 + e * (r.val - 1)).det := by
    have : 1 + rm e * ((ratGL E n r).val - 1) = (1 + e * (r.val - 1)).map (algebraMap E (Ad E)) := by
      have h2 : (ratGL E n r).val = r.val.map (algebraMap E (Ad E)) := rfl
      rw [h2]
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [rm, Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, apply_ite, map_sum]
    rw [chi, this]
    exact (RingHom.map_det _ _).symm
  have h2 := chi_isUnit e he _ hr
  rw [h1] at h2
  rw [lam, h1]
  refine GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap _ fun h0 => ?_
  rw [h0, map_zero] at h2
  obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact (h2.map (cV v)).ne_zero (map_zero _)

end Chi

end GlobalTheory.CompanionTheory.TorusCh

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnFderivApply
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.RCalc.ByParts

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integral_deriv_eq_zero {Γ V : Type*} [TopologicalSpace Γ] [SecondCountableTopology Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] {μ : Measure Γ} [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F F' : ℝ → Γ → V} {K : Set Γ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) (C : ℝ)
    (hc : ∀ t ∈ Metric.ball (0 : ℝ) ε, Continuous (F t)) (hc' : Continuous (F' 0))
    (hd : ∀ y, ∀ t ∈ Metric.ball (0 : ℝ) ε, HasDerivAt (fun s => F s y) (F' t y) t)
    (hz : ∀ y, y ∉ K → F 0 y = 0)
    (hz' : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ y, y ∉ K → F' t y = 0)
    (hb : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ y ∈ K, ‖F' t y‖ ≤ C)
    (hconst : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∫ y, F t y ∂μ = ∫ y, F 0 y ∂μ) :
    ∫ y, F' 0 y ∂μ = 0 := by
  have hs : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ :=
    eventually_of_mem hs fun t ht => (hc t ht).aestronglyMeasurable
  have hint : Integrable (F 0) μ :=
    (hc 0 (Metric.mem_ball_self hε)).integrable_of_hasCompactSupport (HasCompactSupport.intro hK hz)
  have hbi : Integrable (K.indicator fun _ => C) μ :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖F' t y‖ ≤ K.indicator (fun _ => C) y :=
    ae_of_all _ fun y t ht => by
      by_cases hy : y ∈ K
      · simpa [hy] using hb t ht y hy
      · simp [hy, hz' t ht y hy]
  have h1 := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hint hc'.aestronglyMeasurable hbound hbi
    (ae_of_all _ hd)).2
  have h2 : HasDerivAt (fun t => ∫ y, F t y ∂μ) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (∫ y, F 0 y ∂μ)).congr_of_eventuallyEq ?_
    exact eventually_of_mem hs hconst
  exact h1.unique h2

theorem continuousOn_fderiv_apply {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace P] {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {S : Set P} {A B : P → E} (hA : ContinuousOn A S) (hB : ContinuousOn B S) (hm : MapsTo A S U) :
    ContinuousOn (fun p => fderiv ℝ f (A p) (B p)) S := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact (h1.continuousOn.comp hA hm).clm_apply hB

theorem hasDerivAt_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (g v : E) (t : ℝ) (hf : DifferentiableAt ℝ f (g + t • v)) :
    HasDerivAt (fun s : ℝ => f (g + s • v)) (fderiv ℝ f (g + t • v) v) t := by
  have h2 : HasDerivAt (fun s : ℝ => g + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add g
  exact hf.hasFDerivAt.comp_hasDerivAt t h2

variable {n : ℕ}

def c (X : Mat n) (t : ℝ) : Mat n := 1 + t • X

theorem continuous_c (X : Mat n) : Continuous (c X) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem c_zero (X : Mat n) : c X 0 = 1 := by simp [c]

theorem mul_c (y X : Mat n) (t : ℝ) : y * c X t = y + t • (y * X) := by
  simp [c, mul_add]

theorem exists_eps (X : Mat n) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, c X t ∈ GLs n := by
  have h : IsOpen (c X ⁻¹' GLs n) := isOpen_GLs.preimage (continuous_c X)
  have h0 : (0 : ℝ) ∈ c X ⁻¹' GLs n := by simp [c_zero, GLs]
  obtain ⟨ε, hε, h'⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (h.mem_nhds h0)
  exact ⟨ε, hε, h'⟩

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem mul_mem_GLs' {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem inv_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  have h : x.det ≠ 0 := hx
  simp [GLs, Matrix.det_nonsing_inv, h]

def toG {x : Mat n} (hx : x ∈ GLs n) : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx

theorem secondCountable_G : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem lg_le_lg_mul (hL : LgFacts) (y : G n) {x : Mat n} (hx : x ∈ GLs n) : lg y.val ≤ lg (y.val * x) + lg x := by
  obtain ⟨hsub, hinv, -⟩ := hL n
  have hdet : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have e : y.val = (y.val * x) * x⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  calc lg y.val = lg ((y.val * x) * x⁻¹) := by rw [← e]
    _ ≤ lg (y.val * x) + lg x⁻¹ := hsub _ (mul_mem_GLs' (val_mem_GLs y) hx) _ (inv_mem_GLs hx)
    _ = lg (y.val * x) + lg x := by rw [hinv x hx]

theorem fderiv_eq_zero_far (hL : LgFacts) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V} {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → f y = 0) {x : Mat n} (hx : x ∈ GLs n) (hlg : R < lg x) : fderiv ℝ f x = 0 := by
  obtain ⟨-, -, -, hsm, -⟩ := hL n
  have ho : IsOpen (GLs n ∩ lg ⁻¹' Ioi R) := hsm.continuousOn.isOpen_inter_preimage isOpen_GLs isOpen_Ioi
  have he : f =ᶠ[𝓝 x] fun _ => (0 : V) :=
    eventually_of_mem (ho.mem_nhds ⟨hx, hlg⟩) fun y hy => hR y hy.1 hy.2
  rw [he.fderiv_eq]
  simp

theorem ibp_of (hL : LgFacts) (hU : Unimod) : IBP := by
  intro n _ _ μ _ V _ _ _ f hf hC X
  obtain ⟨R, hR⟩ := hC
  obtain ⟨-, -, -, hsm, hcpt, -⟩ := hL n
  haveI := (hU n μ).1
  haveI : SecondCountableTopology (G n) := secondCountable_G
  obtain ⟨ε, hε, hcε⟩ := exists_eps X
  have hball : ∀ t ∈ Metric.ball (0 : ℝ) ε, c X t ∈ GLs n := fun t ht => hcε t (Metric.ball_subset_closedBall ht)
  have hmem : ∀ (y : G n), ∀ t ∈ Metric.closedBall (0 : ℝ) ε, y.val * c X t ∈ GLs n :=
    fun y t ht => mul_mem_GLs' (val_mem_GLs y) (hcε t ht)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, lg (c X t) ≤ C₀ := by
    have hcont : ContinuousOn (fun t => lg (c X t)) (Metric.closedBall (0 : ℝ) ε) :=
      hsm.continuousOn.comp (continuous_c X).continuousOn hcε
    obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℝ) ε).bddAbove_image hcont
    exact ⟨C₀, fun t ht => hC₀ (mem_image_of_mem _ ht)⟩
  set K : Set (G n) := {y : G n | lg y.val ≤ R + C₀} with hKdef
  have hK : IsCompact K := hcpt (R + C₀)
  have hfar : ∀ (y : G n), y ∉ K → ∀ t ∈ Metric.closedBall (0 : ℝ) ε, R < lg (y.val * c X t) := by
    intro y hy t ht
    have h1 : R + C₀ < lg y.val := not_le.1 hy
    have h2 := lg_le_lg_mul hL y (hcε t ht)
    have h3 := hC₀ t ht
    linarith
  have hvalc : Continuous fun y : G n => y.val := Units.continuous_val
  obtain ⟨C, hCb⟩ : ∃ C, ∀ p ∈ K ×ˢ Metric.closedBall (0 : ℝ) ε,
      ‖fderiv ℝ f (p.1.val * c X p.2) (p.1.val * X)‖ ≤ C := by
    have hcont : ContinuousOn (fun p : G n × ℝ => fderiv ℝ f (p.1.val * c X p.2) (p.1.val * X))
        (K ×ˢ Metric.closedBall (0 : ℝ) ε) := by
      refine continuousOn_fderiv_apply isOpen_GLs hf ?_ ?_ ?_
      · exact ((hvalc.comp continuous_fst).mul ((continuous_c X).comp continuous_snd)).continuousOn
      · exact ((hvalc.comp continuous_fst).mul continuous_const).continuousOn
      · exact fun p hp => hmem p.1 p.2 hp.2
    exact (hK.prod (isCompact_closedBall (0 : ℝ) ε)).exists_bound_of_continuousOn hcont
  have key := integral_deriv_eq_zero (μ := μ) (F := fun t (y : G n) => f (y.val * c X t))
    (F' := fun t (y : G n) => fderiv ℝ f (y.val * c X t) (y.val * X)) hK hε C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [c_zero, Rd] using key
  · intro t ht
    exact hf.continuousOn.comp_continuous (hvalc.mul continuous_const)
      fun y => hmem y t (Metric.ball_subset_closedBall ht)
  · refine continuousOn_univ.1 (continuousOn_fderiv_apply isOpen_GLs hf ?_ ?_ ?_)
    · exact (hvalc.mul continuous_const).continuousOn
    · exact (hvalc.mul continuous_const).continuousOn
    · exact fun y _ => hmem y 0 (Metric.mem_closedBall_self hε.le)
  · intro y t ht
    have hd : DifferentiableAt ℝ f (y.val + t • (y.val * X)) := by
      rw [← mul_c]
      exact differentiableAt_of_smooth hf (hmem y t (Metric.ball_subset_closedBall ht))
    have := hasDerivAt_line (y.val) (y.val * X) t hd
    have e1 : (fun s : ℝ => f (y.val * c X s)) = fun s : ℝ => f (y.val + s • (y.val * X)) := by
      funext s; rw [mul_c]
    show HasDerivAt (fun s : ℝ => f (y.val * c X s)) (fderiv ℝ f (y.val * c X t) (y.val * X)) t
    rw [e1, mul_c]
    exact this
  · intro y hy
    exact hR _ (hmem y 0 (Metric.mem_closedBall_self hε.le)) (hfar y hy 0 (Metric.mem_closedBall_self hε.le))
  · intro t ht y hy
    have ht' := Metric.ball_subset_closedBall ht
    simp only [fderiv_eq_zero_far hL hR (hmem y t ht') (hfar y hy t ht'), ContinuousLinearMap.zero_apply]
  · intro t ht y hy
    exact hCb (y, t) ⟨hy, Metric.ball_subset_closedBall ht⟩
  · intro t ht
    have h0 := integral_mul_right_eq_self (μ := μ) (fun y : G n => f y.val) (toG (hball t ht))
    simpa [toG, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible, c_zero] using h0

end GlobalTheory.CompanionTheory.RCalc.ByParts

theorem GlobalTheory.CompanionTheory.RCalc.ibp : GlobalTheory.CompanionTheory.RCalc.IBP :=
  GlobalTheory.CompanionTheory.RCalc.ByParts.ibp_of GlobalTheory.T.length_function_facts_hold GlobalTheory.T.general_linear_group_unimodular
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleLeviTransport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleLeviTransport
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.ParIndBridge

theorem parInd_equiv_parabolicInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((parInd e ρ).Equiv (parabolicInd k N β (ρ.comp φ.symm.toMonoidHom))) := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ W _ _ ρ
  have hP : parab k e = blockUpper k N β := GlobalTheory.T.parabolic_eq_block_upper k e β hβ
  have h12 : ∀ {p : GL (Fin N) k}, p ∈ parab k e → p ∈ blockUpper k N β := fun h => hP ▸ h
  have h21 : ∀ {p : GL (Fin N) k}, p ∈ blockUpper k N β → p ∈ parab k e := fun h => hP ▸ h
  have hchar : ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β) (w : W),
      (deltaHalf k m (leviProj k e ⟨p, h1⟩) : ℂ) • ρ (leviProj k e ⟨p, h1⟩) w =
        sqrtModular k N β ⟨p, h2⟩ •
          ρ (φ.symm (GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩)) w := by
    intro p h1 h2 w
    have hL := GlobalTheory.T.parabolic_levi_projection k e β hβ φ hφ p h1 h2
    rw [← hL, MulEquiv.symm_apply_apply, GlobalTheory.T.modulus_character_levi k e β hβ φ hφ, hL,
      GroundTheory.Automorphic.Parabolic.sqrtModular_leviProj]
  let σ := ρ.comp φ.symm.toMonoidHom
  let E : IndSp e ρ ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.parabolicIndSpace k N β σ :=
    { toFun := fun f => ⟨f.1.1, fun p g => by
          have h := parInd_law e ρ f ⟨p.1, h21 p.2⟩ g
          refine h.trans ?_
          exact hchar p.1 (h21 p.2) p.2 _,
        GroundTheory.Automorphic.stabilizerOf (GlobalTheory.PRep.ind (parab k e)
          ((SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e))) f.1, f.2, fun x hx g => by
          have h := GroundTheory.Automorphic.mem_stabilizerOf.1 hx
          exact congrFun (congrArg Subtype.val h) g⟩
      invFun := fun f => ⟨⟨f.1, fun p g => by
          have h := f.2.1 ⟨p.1, h12 p.2⟩ g
          refine h.trans ?_
          exact (hchar p.1 p.2 (h12 p.2) _).symm⟩, by
          obtain ⟨-, K, hK, hf⟩ := f.2
          refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds (one_mem K)) fun x hx => ?_)
          exact Subtype.ext (funext fun g => hf x hx g)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Representation.Equiv.mk E fun g => LinearMap.ext fun f => Subtype.ext (funext fun x => rfl)⟩

end GlobalTheory.CompanionTheory.ParIndBridge
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleLeviTransportStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInd_equiv_levi_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((parInd e ρ).Equiv (parabolicInd k N β (ρ.comp φ.symm.toMonoidHom))) := by
  first | exact @GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd | exact GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd | (intros; apply GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumProdEqPow
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailExtra
theorem UpperTheory.Reformulated.B.Yvb3.main :
    ∀ (g : ℤ → ENNReal) (n : ℕ), ∑' (m : Fin n → ℤ), ∏ i : Fin n, g (m i) = (∑' (k : ℤ), g k) ^ n := by
  intro g n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ℤ)).tsum_eq]
    have h : ∀ p : ℤ × (Fin n → ℤ),
        (∏ i : Fin (n+1), g ((Fin.consEquiv (fun _ : Fin (n+1) => ℤ)) p i)) = g p.1 * ∏ i : Fin n, g (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [Fin.consEquiv]
    simp_rw [h]
    rw [ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin n → ℤ) => g a * ∏ i : Fin n, g (b i))]
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right, pow_succ']
end

noncomputable section

open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LatticeSum

theorem tsum_prod_eq_pow (g : ℤ → ℝ≥0∞) (n : ℕ) :
    ∑' m : Fin n → ℤ, ∏ i, g (m i) = (∑' k, g k) ^ n :=
  _root_.UpperTheory.Reformulated.B.Yvb3.main g n

def wt (k : ℤ) : ℝ := ((1 + |(k : ℝ)|) ^ 2)⁻¹

theorem wt_nonneg (k : ℤ) : 0 ≤ wt k := by
  unfold wt; positivity

theorem summable_nat_wt : Summable fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have h : Summable fun k : ℕ => ((k : ℝ) ^ 2)⁻¹ := by
    simpa [one_div] using (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have h1 := (summable_nat_add_iff 1).2 h
  simpa using h1

theorem summable_wt : Summable wt := by
  apply Summable.of_nat_of_neg
  · refine summable_nat_wt.congr fun k => ?_
    simp [wt, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_comm]
  · refine summable_nat_wt.congr fun k => ?_
    simp [wt, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_comm]

theorem pointwise_le (n M : ℕ) (h : 2 * n ≤ M) (m : Fin n → ℤ) :
    (1 + ‖fun i => (m i : ℝ)‖) ^ (-(M : ℤ)) ≤ ∏ i, wt (m i) := by
  set N : ℝ := 1 + ‖fun i => (m i : ℝ)‖ with hN
  have hN1 : 1 ≤ N := by
    have := norm_nonneg (fun i => (m i : ℝ))
    linarith
  have hN0 : 0 < N := by linarith
  have hle : ∏ i, (1 + |(m i : ℝ)|) ^ 2 ≤ N ^ M := by
    calc ∏ i, (1 + |(m i : ℝ)|) ^ 2 ≤ ∏ _i : Fin n, N ^ 2 := by
          apply Finset.prod_le_prod₀
          · intro i _; positivity
          · intro i _
            have h1 : |(m i : ℝ)| ≤ ‖fun i => (m i : ℝ)‖ := by
              simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun i => (m i : ℝ)) i
            have h2 : 1 + |(m i : ℝ)| ≤ N := by rw [hN]; linarith
            exact pow_le_pow_left₀ (by positivity) h2 2
      _ = N ^ (2 * n) := by simp [Finset.prod_const, pow_mul]
      _ ≤ N ^ M := pow_le_pow_right₀ hN1 h
  have hpos : 0 < ∏ i, (1 + |(m i : ℝ)|) ^ 2 := Finset.prod_pos fun i _ => by positivity
  have hw : ∏ i, wt (m i) = (∏ i, (1 + |(m i : ℝ)|) ^ 2)⁻¹ := by
    simp only [wt, Finset.prod_inv_distrib]
  rw [hw, zpow_neg, zpow_natCast]
  exact inv_anti₀ hpos hle

theorem latSum : PositivityTheory.Rg.BcB.E1.LatSum := by
  intro n M h
  have hS : ∑' k, ENNReal.ofReal (wt k) ≠ ⊤ := summable_wt.tsum_ofReal_ne_top
  have hle : ∑' m : Fin n → ℤ, ENNReal.ofReal ((1 + ‖fun i => (m i : ℝ)‖) ^ (-(M : ℤ))) ≤
      ∑' m : Fin n → ℤ, ∏ i, ENNReal.ofReal (wt (m i)) := by
    refine ENNReal.tsum_le_tsum fun m => ?_
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => wt_nonneg (m i)]
    exact ENNReal.ofReal_le_ofReal (pointwise_le n M h m)
  exact ne_top_of_le_ne_top (ENNReal.pow_ne_top hS)
    (hle.trans_eq (tsum_prod_eq_pow (fun k => ENNReal.ofReal (wt k)) n))

end GlobalTheory.CompanionTheory.LatticeSum

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCVPosIdele
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.TorNorm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem norm_cV (v : InfinitePlace E) (u : Ad E) : ‖cV v u‖ = ‖u.1 v‖ :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v))) _

theorem cW_posIdele (w : HeightOneSpectrum (𝓞 E)) (ρ : ℝ) (hρ : 0 < ρ) :
    cW w ((posIdele (K := E) ρ hρ : (Ad E)ˣ) : Ad E) = 1 :=
  posIdele_finite ρ hρ w

theorem norm_cV_posIdele (v : InfinitePlace E) (ρ : ℝ) (hρ : 0 < ρ) :
    ‖cV v ((posIdele (K := E) ρ hρ : (Ad E)ˣ) : Ad E)‖ = ρ := by
  rw [norm_cV]; exact norm_posIdele_infinite ρ hρ v

theorem two_card : 2 * (Fintype.card (InfinitePlace E) : ℝ) = Module.finrank ℚ E := by
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero]
  push_cast; ring

theorem logAbs_of (u : Ad E) (t : ℝ) (h1 : ∀ v, ‖cV v u‖ = Real.exp t) (h2 : ∀ w, ‖cW w u‖ = 1) :
    logAbs u = Module.finrank ℚ E * t := by
  have : ∀ v : InfinitePlace E, Real.log (‖cV v u‖ ^ 2) = 2 * t := fun v => by
    rw [h1, Real.log_pow, Real.log_exp]; norm_num
  simp only [logAbs, this, h2, Real.log_one, finsum_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_zero]
  rw [← two_card]; ring

theorem tor_neg {n : ℕ} (x : Fin n → ℝ) : (An.tor E x : GA E n)⁻¹ = An.tor E (-x) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  have : ∀ i, posIdele (K := E) (Real.exp ((-x) i)) (Real.exp_pos _) * posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) = 1 := fun i => by
    have h : (⟨Real.exp ((-x) i), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) *
        ⟨Real.exp (x i), Real.exp_pos _⟩ = 1 := by
      apply Subtype.ext
      simp [← Real.exp_add]
    have := congrArg (posIdeleHom E) h
    simpa only [map_mul, map_one, posIdeleHom_apply] using this
  change diagUnits n _ * diagUnits n _ = 1
  rw [← map_mul]
  convert map_one (diagUnits n (R := Ad E))
  exact funext this

theorem logSizeM_tor {n : ℕ} (x : Fin n → ℝ) :
    logSizeM (An.tor E x : GA E n).val ≤ Module.finrank ℚ E * ‖x‖ := by
  have entry : ∀ i j, (An.tor E x : GA E n).val i j =
      if i = j then ((posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ) : Ad E) else 0 := fun i j => by
    change (diagUnits n _ : GL (Fin n) (Ad E)).val i j = _
    rw [coe_diagUnits, Matrix.diagonal_apply]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have inf : ∀ v : InfinitePlace E,
      Real.posLog (⨆ p : Fin n × Fin n, ‖cV v ((An.tor E x : GA E n).val p.1 p.2)‖ ^ 2) ≤ 2 * ‖x‖ := fun v => by
    have hle : (⨆ p : Fin n × Fin n, ‖cV v ((An.tor E x : GA E n).val p.1 p.2)‖ ^ 2) ≤ Real.exp (2 * ‖x‖) := by
      refine Real.iSup_le (fun p => ?_) (Real.exp_pos _).le
      rw [entry]
      split_ifs
      · rw [norm_cV_posIdele, ← Real.exp_nat_mul]
        have : x p.1 ≤ ‖x‖ := (le_abs_self _).trans (norm_le_pi_norm x p.1)
        exact Real.exp_le_exp.2 (by push_cast; linarith)
      · simp [(Real.exp_pos _).le]
    calc _ ≤ Real.posLog (Real.exp (2 * ‖x‖)) :=
          Real.posLog_le_posLog (le_trans (by norm_num) (Real.iSup_nonneg fun _ => by positivity)) hle
      _ = 2 * ‖x‖ := by
          rw [Real.posLog, Real.log_exp]
          exact max_eq_right (by positivity)
  have fin : ∀ w : HeightOneSpectrum (𝓞 E),
      Real.posLog (⨆ p : Fin n × Fin n, ‖cW w ((An.tor E x : GA E n).val p.1 p.2)‖) = 0 := fun w => by
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)]
    refine Real.iSup_le (fun p => ?_) zero_le_one
    rw [entry]
    split_ifs
    · rw [cW_posIdele, norm_one]
    · simp
  unfold logSizeM
  simp only [fin, finsum_zero, add_zero]
  calc _ ≤ ∑ _v : InfinitePlace E, 2 * ‖x‖ := Finset.sum_le_sum fun v _ => inf v
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← two_card]; ring

theorem logAbs_det_tor {n : ℕ} (x : Fin n → ℝ) :
    logAbs (An.tor E x : GA E n).val.det = Module.finrank ℚ E * ∑ i, x i := by
  have d : (An.tor E x : GA E n).val.det =
      ∏ i, ((posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ) : Ad E) := by
    change (diagUnits n _ : GL (Fin n) (Ad E)).val.det = _
    rw [coe_diagUnits, det_diagonal]
  rw [d]
  refine logAbs_of _ _ (fun v => ?_) (fun w => ?_)
  · rw [map_prod, norm_prod, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => norm_cV_posIdele v _ _
  · rw [map_prod, norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [cW_posIdele, norm_one]

theorem torNorm : LogAbsBasic → TorNorm := fun _ E _ _ _ =>
  ⟨fun t => logAbs_of _ t (fun v => norm_cV_posIdele v _ _) (fun w => by rw [cW_posIdele, norm_one]),
    fun n x => ⟨logAbs_det_tor x, by
      have h1 := logSizeM_tor (E := E) x
      have h2 := logSizeM_tor (E := E) (-x)
      rw [norm_neg] at h2
      rw [logSize, tor_neg]
      linarith⟩⟩

end GlobalTheory.CompanionTheory.TorNorm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalChangeOfVariables
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.NilChangeVar

namespace GlobalTheory.CompanionTheory.LocVan

theorem nilChange_of_flag : NilChange := by
  intro n d W₁ W₂ hreg _ hle h1 h2
  let L : nilrad W₁ W₂ ≃ₗ[ℝ] nilrad W₁ W₂ :=
    LinearEquiv.ofInjectiveEndo (slinN d h1 h2 - LinearMap.id) (slinN_injective d h1 h2 hreg)
  have hLval (X : nilrad W₁ W₂) : (L X).1 = slin d X.1 - X.1 := by
    simp only [L, LinearEquiv.coe_ofInjectiveEndo, LinearMap.sub_apply, LinearMap.id_apply,
      Submodule.coe_sub] <;> rfl
  have hLc : Continuous L := L.toContinuousLinearEquiv.continuous
  let Q : nilrad W₁ W₂ → nilrad W₁ W₂ := fun X =>
    ⟨quad d X.1, two_mem hle (quadratic_term_nilradical_mem d h1 h2 X.2).1 (quadratic_term_nilradical_mem d h1 h2 X.2).2⟩
  have hQc : Continuous Q :=
    Continuous.subtype_mk ((continuous_quad d).comp continuous_subtype_val) _
  have hLF : ∀ y ∈ nilrad2 W₁ W₂, L y ∈ nilrad2 W₁ W₂ := fun y hy => by
    have hT := semilinear_term_nilradical_mem d h1 h2 hy.1 hy.2
    refine ⟨fun z => ?_, fun z hz => ?_⟩
    · rw [hLval, Matrix.sub_mulVec]
      exact W₁.sub_mem (hT.1 z) (hy.1 z)
    · rw [hLval, Matrix.sub_mulVec, hT.2 z hz, hy.2 z hz, sub_zero]
  have hQF : ∀ X, Q X ∈ nilrad2 W₁ W₂ := fun X => quadratic_term_nilradical_mem d h1 h2 X.2
  have hQinv : ∀ X, ∀ Y ∈ nilrad2 W₁ W₂, Q (X + Y) = Q X := fun X Y hY =>
    Subtype.ext (quad_add d h1 h2 X.2 hle hY.1 hY.2)
  refine ⟨fun X => L X + Q X, hLc.add hQc, fun X => ?_, ?_⟩
  · rw [eq_inv_mul_iff_mul_eq]
    refine Units.ext ?_
    have e : (uOf (L X + Q X)).val = 1 + (slin d X.1 - X.1 + quad d X.1) := by
      rw [uOf_val, Submodule.coe_add, hLval]
    rw [Units.val_mul, e]
    exact twist_val d h1 h2 (uOf X) X.1 X.2 rfl
  · intro _ _ ν _
    obtain ⟨Φ, c, _, hΦ, hmap⟩ := exists_homeo_map_eq_smul ν (nilrad2 W₁ W₂) L hLF Q hQc hQF hQinv
    refine ⟨c, ?_⟩
    have e : (fun X => L X + Q X) = Φ := funext fun X => (hΦ X).symm
    rw [e]
    exact hmap

end GlobalTheory.CompanionTheory.LocVan
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalHHermScal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def scalH (σ : E →ₐ[F] E) {n : ℕ} (l : R) (S : HermR R σ n) : HermR R σ n :=
  ⟨(algebraMap R (R ⊗[F] E) l) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h : sigR R σ (algebraMap R (R ⊗[F] E) l) = algebraMap R (R ⊗[F] E) l := by
      simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h, S.2 a b]⟩

theorem scalH_coe (σ : E →ₐ[F] E) {n : ℕ} (l : R) (S : HermR R σ n) :
    (scalH R σ l S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      (algebraMap R (R ⊗[F] E) l) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl

theorem scalH_hermScal (σ : E →ₐ[F] E) (l s : R) :
    scalH R σ l (hermScal R σ s) = hermScal R σ (l * s) := by
  apply Subtype.ext
  funext a b
  change (algebraMap R (R ⊗[F] E) l) * (s ⊗ₜ[F] (1 : E)) = (l * s) ⊗ₜ[F] (1 : E)
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

end Alg

theorem euler_move_c : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → ∀ κ : ℝ≥0, IsEulerProd b I κ minf m → IsEulerProd b (I.map e) κ minf' m' := by
  intro F E _ _ _ _ _ σ hcm d b n M I mi mi' m m' e ei ev me mei mev hpr hG ci c hc h1 h2 hf κ hE
  have tr : ∀ (J : Measure (Fin n → Fin M → AF F ⊗[F] E)) (a : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (w : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsEulerProd b J κ a w ↔ IsEulerProd b J 1 (κ • a) w := fun J a w => by
    have e1 : ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞, ∫⁻ X, φ X ∂(κ • a) = (κ : ℝ≥0∞) * ∫⁻ X, φ X ∂a := fun φ => by
      rw [ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul]
    simp only [IsEulerProd, e1, ENNReal.coe_one, one_mul, mul_assoc]
  rw [tr] at hE ⊢
  refine PositivityTheory.PlacePermOperatorBicommutantSpan.euler_move F E σ hcm d b n M I _ _ m m' e ei ev me mei mev hpr hG ci c hc ?_ h2 hf hE
  rw [Measure.map_smul κ mei.aemeasurable, h1, smul_comm]

end GlobalTheory.CompanionTheory.SW.MassSimil

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureIndependentChoices
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureIndependentChoices
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThetaIndep

theorem thetaMeas_gram_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕₂ n T
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact n
  have hrat := (GlobalTheory.T.gram_matrix_local_global F E σ hcm M J hJ n 0 T).2
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n {X | gramE σ J X = T}
  have hl' := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ' 𝓕' hμ' h𝓕₂ n {X | gramE σ J X = T}
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  have hfin := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  have : μ'.IsHaarMeasure := hμ'
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1
  have h𝓕₁ : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  have h0 := (GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕₁ hfin).1
  have hsm : μ' = Measure.haarScalarFactor μ' μ • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hc0 : Measure.haarScalarFactor μ' μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne'
  set c : ℝ≥0 := Measure.haarScalarFactor μ' μ with hc
  have hac : μ ≪ μ' := by
    rw [hsm]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)
  have h𝓕₃ : IsFundamentalDomain Γ 𝓕' μ' := h𝓕₂
  have h𝓕₄ : IsFundamentalDomain Γ 𝓕' μ := h𝓕₃.mono hac
  have hmass : μ 𝓕 = μ 𝓕' := h𝓕₁.measure_eq h𝓕₄
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [hl _ hΦ, hl' _ hΦ]
  set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : {X | gramE σ J X = T},
    Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf
  have hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g := fun γ g => by
    choose t ht using fun X : {X | gramE σ J X = T} => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := n) γ⁻¹ X.1
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
    have hT : ∀ X, gramE σ J (t X) = T := fun X =>
      Matrix.map_injective hinj (by simp only [← hrat, ← ht', ag]; rw [hrat, X.2])
    have hti : Function.Injective fun X => (⟨t X, hT X⟩ : {X | gramE σ J X = T}) := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact Subtype.ext (hri h1)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)
    rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']
  have hinv : ∀ (γ : Γ) g, f (γ • g) = f g := fun γ g =>
    (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))
  have hint : ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g in 𝓕', f g ∂μ := h𝓕₁.setLIntegral_eq h𝓕₄ f hinv
  have hcE0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  have hcT : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [hint, hsm, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply, ← hmass]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl hcE0) (Or.inl hcT)]
  calc _ = ((c : ℝ≥0∞)⁻¹ * c) * ((μ 𝓕)⁻¹ * ∫⁻ g in 𝓕', f g ∂μ) := by rw [ENNReal.inv_mul_cancel hcE0 hcT, one_mul]
    _ = _ := by ring

end GlobalTheory.CompanionTheory.SW.ThetaIndep

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureIndependentChoicesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_independent_choices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | exact GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep <;> assumption)
end
end
