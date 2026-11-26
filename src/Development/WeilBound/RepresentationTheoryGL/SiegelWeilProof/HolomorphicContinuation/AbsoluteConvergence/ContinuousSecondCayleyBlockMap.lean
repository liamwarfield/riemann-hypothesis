module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

def KMat (n : ℕ) : Set (M2 n) := {M | Mᴴ * M = 1 ∧ Mᴴ * JJ n * M = JJ n}

theorem isCompact_KMat : IsCompact (KMat n) := by
  have hsub : KMat n ⊆ Set.pi univ (fun _ : Fin n ⊕ Fin n => Set.pi univ (fun _ : Fin n ⊕ Fin n => Metric.closedBall (0:ℂ) 1)) := by
    intro M hM
    have hU : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hM.1
    intro i _ j _
    simpa using entry_norm_bound_of_unitary hU i j
  have hc : IsCompact (Set.pi univ (fun _ : Fin n ⊕ Fin n => Set.pi univ (fun _ : Fin n ⊕ Fin n => Metric.closedBall (0:ℂ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))
  refine hc.of_isClosed_subset ?_ hsub
  have hA : Continuous fun M : M2 n => Mᴴ * M :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  have hB : Continuous fun M : M2 n => Mᴴ * JJ n * M :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact (isClosed_eq hA continuous_const).inter (isClosed_eq hB continuous_const)

theorem isCompact_KR : IsCompact ((KR n : Subgroup (GR n)) : Set (GR n)) := by
  let φ : KMat n → GR n := fun M =>
    ⟨⟨M.1, M.1ᴴ, (mul_eq_one_comm).mp M.2.1, M.2.1⟩, M.2.2⟩
  have hφ : Continuous φ :=
    Continuous.subtype_mk (Units.continuous_iff.mpr
      ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩) _
  have hK : IsCompact (univ : Set (KMat n)) := isCompact_iff_isCompact_univ.mp isCompact_KMat
  have himg : φ '' univ = ((KR n : Subgroup (GR n)) : Set (GR n)) := by
    ext k
    constructor
    · rintro ⟨M, -, rfl⟩
      exact ⟨M.2.2, M.2.1⟩
    · intro hk
      refine ⟨⟨mR k, hk.2, hk.1⟩, trivial, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
  rw [← himg]
  exact hK.image hφ

instance compactSpace_KR_far : CompactSpace (KR n) := isCompact_iff_compactSpace.mp isCompact_KR

theorem continuous_first_cayley_block_map : Continuous (fun M : M2 n => u1 M) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply]
  fun_prop

theorem continuous_second_cayley_block_map : Continuous (fun M : M2 n => u2 M) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply]
  fun_prop

theorem det_mR_ne (g : GR n) : (mR g).det ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit).ne_zero

theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hm : Continuous (mR : GR n → M2 n) := continuous_mR
  have hd : Continuous fun g : GR n => (mR g).det := hm.matrix_det
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := (continuous_first_cayley_block_map.comp hm).matrix_det
  have h2 : Continuous fun g : GR n => (u2 (mR g)).det := (continuous_second_cayley_block_map.comp hm).matrix_det
  unfold F0 f0
  exact (hd.zpow₀ e fun g => Or.inl (det_mR_ne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (hD n g).1).mul (h2.zpow₀ _ fun g => Or.inl (hD n g).2))

theorem weight_factor_ne_zero (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  unfold F0 f0
  refine mul_ne_zero (zpow_ne_zero _ (det_mR_ne g)) (mul_ne_zero (zpow_ne_zero _ (hD n g).1) (zpow_ne_zero _ (hD n g).2))

theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (hD n g).1) 2)

theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := (continuous_first_cayley_block_map.comp continuous_mR).matrix_det
  unfold hLoc
  exact (h1.norm.pow 2).inv₀ fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hD n g).1)

end PositivityTheory.Rg.Sw.AbsSt.Far
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightC
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GlobCore
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

structure GlobCore (ε : Fin m → Bool) (c : ℝ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (ρ : GR n → PX m n →ₗ[ℂ] PX m n)
    (G : Type) [Group G] [TopologicalSpace G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
    (sec I : PX m n →ₗ[ℂ] (G → ℂ)) : Prop where
  ιcont : Continuous ι
  split : ∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
    ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ ∀ P, sec P (x * ι y') = S * sL P y'
  Icont : Continuous (I 1)
  Ileft : ∀ γ ∈ Γ, ∀ g, I 1 (γ * g) = I 1 g
  Ik : ∀ P g (k : GR n), InK (mR k) → I P (g * ι k) = I (ρ k P) g
  Iinv : ∀ g a b P, I (hOp ε c a b P) g = 0
  Idil : ∀ (g : G) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ t, IsDil X t (a t)) → ∃ (U : Set ℂ) (F : GR n → ℂ → ℂ), IsOpen U ∧
    (∀ t : ℝ, (t : ℂ) ∈ U) ∧ ContinuousOn (fun y : GR n × ℂ => F y.1 y.2) (univ ×ˢ U) ∧ ∀ y, DifferentiableOn ℂ (F y) U ∧
      (∀ t : ℝ, F y t = I 1 (g * ι (y * a t))) ∧ ∀ r : ℕ, iteratedDeriv r (F y) 0 = I ((dil c X ^ r) 1) (g * ι y)
  eis : ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G → ℂ) (σ : ℝ), IsOpen U ∧ GlobalTheory.Cont.IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (E · g) U) ∧ ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ) ∧
    (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) ∧
    ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
        ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g q‖ ≤ u q) ∧
      ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g

end PositivityTheory.Rg.Sw.AbsSt
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def FarRightC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)), GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I →
      ∃ σ : ℝ, (∀ Q g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z Q) g) (GlobalTheory.Cont.rightOf σ)) ∧
        (∀ Q g (z : ℂ), σ < z.re → Summable fun q => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q) ∧
        ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (ν : Measure (KR n)) (κ : KR n → ℂ) (N : ℕ) (yy : Fin N → GR n)
          (QQ : Fin N → PX m n) (M : ℂ → Matrix (Fin N) (Fin N) ℂ), IsFiniteMeasure ν → Continuous κ →
          (∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
              F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y') →
          ∀ (z : ℂ), σ < z.re → ∀ (g : G) (i : Fin N),
            ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
              ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g

def TSGenC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)), GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I →
      ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (W : Submodule ℂ (PX m n)), FiniteDimensional ℂ W →
        (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) → ∀ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν →
        Continuous κ → (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) →
        (∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y) →
        ∀ (g : G) (y : GR n) (Q : PX m n), Q ∈ W → (∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * y) ∂ν = sL Q y') →
          ∫ k, κ k * I 1 (g * ι ((k : GR n) * y)) ∂ν = I Q g

def VacData {n : ℕ} {m : ℕ} {G : Type} [Group G] [TopologicalSpace G] (Pp Γ : Subgroup G) (s₀ : ℂ) (Ht : G → ℝ≥0)
    (sec I : PX m n →ₗ[ℂ] (G → ℂ)) : Prop :=
  ∃ (r : ℝ) (F : ℂ → G → ℂ), 0 < r ∧ ContinuousOn (fun y : ℂ × G => F y.1 y.2) (Metric.ball s₀ r ×ˢ univ) ∧
    (∀ g, DifferentiableOn ℂ (F · g) (Metric.ball s₀ r)) ∧ (∀ g, F s₀ g = I 1 g) ∧
    ∀ g, ∀ z ∈ Metric.ball s₀ r, GlobalTheory.Cont.HolValueAt
      (fun w => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (w - s₀) * sec 1 x) g) z (F z g)

def GenCore : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)), GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I → VacData Pp Γ s₀ Ht sec I →
      ∀ P g, GlobalTheory.Cont.HolValueAt
        (fun z => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec P x) g) s₀ (I P g)

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ImportsAlt
noncomputable section

open MeasureTheory Set Filter Topology GlobalTheory.Cont

namespace PositivityTheory.Rg.Sw.AbsSt

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousGramX
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem scal_zero (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) : scal (aH X 0) y = y := by
  funext a j; simp [scal, aH]

theorem continuous_scal (α : Fin n → ℝ) : Continuous (scal (m := m) α) :=
  continuous_pi fun a => continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

theorem continuous_gs (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  unfold gs; fun_prop

theorem continuous_gramX (ε : Fin m → Bool) : Continuous (gramX (n := n) ε) :=
  continuous_pi fun i => continuous_pi fun j => continuous_evX _

theorem prod_aH (X : Fin n → ℝ) (h : ℝ) :
    (∏ j, aH X h j ^ (2 * m) : ℝ) = Real.exp (2 * (h * ((m : ℝ) * ∑ j, X j))) := by
  simp only [aH, ← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

theorem gaussPart : GaussPart := by
  intro m n ε c t hc X b hb Q
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  set E : (Fin m → Fin n → ℂ) → ℂ := fun y => Complex.exp (Complex.I * t * (b * gramX ε y).trace) with hEdef
  have hE : ∀ y, ‖E y‖ = 1 := fun y => norm_phase t _ (trace_im ε y hb)
  have hEc : Continuous E := by
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    exact (continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace
  set A : ℝ := (m : ℝ) * ∑ j, X j with hA
  set P' : PX m n := dil c X Q - ((m : ℂ) * ∑ j, (X j : ℂ)) • Q with hP'
  let φ : ℝ → (Fin m → Fin n → ℂ) → ℂ := fun s y => evX Q (scal (aH X s) y) * gs c (scal (aH X s) y) * E y
  let φ' : ℝ → (Fin m → Fin n → ℂ) → ℂ := fun s y => evX P' (scal (aH X s) y) * gs c (scal (aH X s) y) * E y
  have hφc : ∀ (P : PX m n) (s : ℝ), Continuous fun y => evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y :=
    fun P s => (((continuous_evX P).comp (continuous_scal _)).mul ((continuous_gs c).comp (continuous_scal _))).mul hEc
  have hH : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hint : Integrable (fun y : Fin m → Fin n → ℂ => (1 + ‖y‖) ^ (-r)) := by
    have : ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ)) < r := by rw [hr]; linarith
    exact integrable_one_add_norm this
  have hdomI : ∀ (P : PX m n), ∃ K : ℝ, ∀ s : ℝ, |s| < 1 → ∀ y,
      ‖evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y‖ ≤ K * (1 + ‖y‖) ^ (-r) := by
    intro P
    obtain ⟨K, -, hK⟩ := dom_bound c hc X P
    exact ⟨K, fun s hs y => by rw [norm_mul, hE, mul_one]; exact hK s hs y⟩
  have hintP : ∀ (P : PX m n) (s : ℝ), |s| < 1 →
      Integrable fun y => evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y := by
    intro P s hs
    obtain ⟨K, hK⟩ := hdomI P
    exact Integrable.mono' (hint.const_mul K) (hφc P s).aestronglyMeasurable
      (Eventually.of_forall fun y => hK s hs y)

  have key : ∀ h : ℝ, Complex.exp (-((h * A : ℝ) : ℂ)) * secN ε c t Q (bS X h b) =
      Complex.exp (((h * A : ℝ) : ℂ)) * ∫ y, φ h y := by
    intro h
    have hpos : ∀ j, 0 < aH X h j := fun j => Real.exp_pos _
    have h1 : secN ε c t Q (bS X h b) = ((∏ j, aH X h j ^ (2 * m) : ℝ) : ℂ) * ∫ y, φ h y := by
      unfold secN
      rw [integral_scal (aH X h) hpos]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [φ, hEdef, trace_scal]
    rw [h1, prod_aH, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hA]; push_cast; ring

  obtain ⟨K, hK⟩ := hdomI P'
  have hΨ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := φ) (F' := φ') (x₀ := (0 : ℝ))
    (bound := fun y => K * (1 + ‖y‖) ^ (-r)) (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun s => (hφc Q s).aestronglyMeasurable)
    (hintP Q 0 (by simp)) ((hφc P' 0).aestronglyMeasurable)
    (Eventually.of_forall fun y s hs => hK s (by simpa [Real.dist_eq] using hs) y) (hint.const_mul K)
    (Eventually.of_forall fun y s _ => by
      have := (hasDerivAt_phi c X Q y s).mul_const (E y)
      refine this.congr_deriv ?_
      simp only [φ', hP', evX_eq, map_sub, smul_eval])

  have hexp : HasDerivAt (fun h : ℝ => Complex.exp (((h * A : ℝ) : ℂ))) (Complex.exp (((0 * A : ℝ) : ℂ)) * (A : ℂ)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const A).ofReal_comp).cexp.congr_deriv (by simp)
  have hF := hexp.mul hΨ.2
  have hfun : (fun h : ℝ => Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b)) =
      fun h => Complex.exp (((h * A : ℝ) : ℂ)) * ∫ y, φ h y := funext key
  rw [hfun]
  refine hF.congr_deriv ?_

  have hφ0 : ∀ y, φ 0 y = evX Q y * gs c y * E y := fun y => by simp only [φ, scal_zero]
  have hφ'0 : ∀ y, φ' 0 y = evX P' y * gs c y * E y := fun y => by simp only [φ', scal_zero]
  have hI1 := hintP Q 0 (by simp)
  have hI2 := hintP P' 0 (by simp)
  simp only [scal_zero] at hI1 hI2
  have hdil : ∀ y, evX (dil c X Q) y * gs c y * E y =
      ((m : ℂ) * ∑ j, (X j : ℂ)) * (evX Q y * gs c y * E y) + evX P' y * gs c y * E y := by
    intro y
    simp only [hP', evX_eq, map_sub, smul_eval]
    ring
  unfold secN
  simp only [hφ0, hφ'0, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]
  rw [integral_congr_ae (Eventually.of_forall hdil), integral_add (hI1.const_mul _) hI2, integral_const_mul]
  simp only [hEdef, hA]
  push_cast
  ring

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LamCont
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LamLocal
noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ}
  {sL : PX m n →ₗ[ℂ] (GR n → ℂ)} {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ}
  {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

def invSub (Γ : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {F | Continuous F ∧ ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g}
  add_mem' := fun {F F'} hF hF' => ⟨hF.1.add hF'.1, fun γ hγ g => by simp [hF.2 γ hγ g, hF'.2 γ hγ g]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  smul_mem' := fun a F hF => ⟨hF.1.const_smul a, fun γ hγ g => by simp [hF.2 γ hγ g]⟩

theorem lam_zero (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) : l 0 = 0 := by
  obtain ⟨C, -, hC⟩ := hG.Λbd l hl
  have h0 := hC 0 0 continuous_const (fun _ _ _ => rfl) (fun x _ => by simp)
  exact norm_le_zero_iff.mp h0

theorem lam_smul (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) (a : ℂ) (F : G → ℂ)
    (hF : Continuous F) (hFi : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) : l (fun g => a * F g) = a * l F := by
  have h := hG.Λadd l hl a F 0 hF continuous_const hFi (fun _ _ _ => rfl)
  rw [lam_zero hG l hl, add_zero, add_zero] at h
  have hfun : (fun g => a * F g) = a • F := by
    funext g
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact h

theorem lam_local (hBH : BanachHol) (hFL : FactorL) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G → ℂ} {σ : ℝ} (hUo : IsOpen U) (hUr : GlobalTheory.Cont.IsRightDomain U)
    (hs : s₀ ∈ U) (hd : d ≠ 0) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ))
    (hEinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g)
    (hEr : ∀ z : ℂ, σ < z.re → ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) g)
    (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H s₀ ∧ H s₀ = l (I 1) ∧ ∀ᶠ z in 𝓝[≠] s₀, l (E z) = d.eval z * H z := by
  obtain ⟨C, hCc, hCb⟩ := hG.Λbd l hl
  obtain ⟨L, hL⟩ := hFL G (invSub Γ) l C hCc (fun F hF => hF.1)
    (fun a F hF F' hF' => hG.Λadd l hl a F F' hF.1 hF'.1 hF.2 hF'.2)
    (fun F hF M hM => hCb F M hF.1 hF.2 hM)
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hEcont : ∀ z ∈ U, Continuous (E z) := by
    intro z hzU
    exact hEc.comp_continuous (continuous_const.prodMk continuous_id) (fun g => ⟨hzU, mem_univ g⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := hBH C U (fun z x => E z x) hUo
    (hEc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩))
    (fun x => hEh x)
  have hfeq : ∀ z ∈ U, l (E z) = L (Φ z) := by
    intro z hzU
    have hmem : E z ∈ invSub Γ := ⟨hEcont z hzU, hEinv z hzU⟩
    rw [hL (E z) hmem (hEcont z hzU)]
    congr 1
    ext x
    rw [hΦ z hzU x]
    rfl
  have hfan : AnalyticOnNhd ℂ (fun z => l (E z)) U :=
    ((L.differentiable.comp_differentiableOn hΦd).congr hfeq).analyticOnNhd hUo
  obtain ⟨H, hHext, hHan, hHval⟩ := hG.Λval l hl
  refine ⟨H, hHan, hHval, ?_⟩
  have hext1 : GlobalTheory.Cont.IsExtAt (fun z => l (E z)) s₀ (fun z => l (E z)) :=
    (GlobalTheory.Cont.IsHolExt.isMerExt ⟨hUr, hfan, ⟨0, fun _ _ => rfl⟩⟩).isExtAt hs
  have hpoly : GlobalTheory.Cont.IsExtAt (fun z => d.eval z) s₀ (fun z => d.eval z) :=
    (GlobalTheory.Cont.IsHolExt.isMerExt ⟨hUr, fun z _ => (Polynomial.differentiable d).analyticAt z,
      ⟨0, fun _ _ => rfl⟩⟩).isExtAt hs
  have hmul := hpoly.mul hHext
  have hright : GlobalTheory.Cont.EqRight (fun z => l (E z))
      (fun s => d.eval s * l (GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (s - s₀) * sec 1 x))) := by
    obtain ⟨σ₁, hσ₁⟩ := hUr.1
    refine ⟨max σ σ₁, fun z hzr => ?_⟩
    have hzr' : max σ σ₁ < z.re := hzr
    have hz1 : σ < z.re := lt_of_le_of_lt (le_max_left _ _) hzr'
    have hzU : z ∈ U := hσ₁ (show σ₁ < z.re from lt_of_le_of_lt (le_max_right _ _) hzr')
    show l (E z) = d.eval z * l (GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z))
    obtain ⟨cs, hcsdef⟩ : ∃ cs, cs = GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) := ⟨_, rfl⟩
    rw [← hcsdef]
    have hE : ∀ g, E z g = d.eval z * cs g := by
      intro g
      rw [hEr z hz1 g, hcsdef]
    by_cases hd0 : d.eval z = 0
    · have hE0 : E z = 0 := funext fun g => by rw [hE g, hd0, zero_mul]; rfl
      rw [hE0, lam_zero hG l hl, hd0, zero_mul]
    · have hcs : cs = fun g => (d.eval z)⁻¹ * E z g := by
        funext g
        rw [hE g, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
      have hcsc : Continuous cs := by
        rw [hcs]
        exact continuous_const.mul (hEcont z hzU)
      have hcsi : ∀ γ ∈ Γ, ∀ g, cs (γ * g) = cs g := by
        intro γ hγ g
        rw [hcs]
        simp only
        rw [hEinv z hzU γ hγ g]
      have hEf : E z = fun g => d.eval z * cs g := funext hE
      rw [hEf, lam_smul hG l hl _ cs hcsc hcsi]
  exact (hext1.congr hright).eventuallyEq hmul

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ}
  {sL : PX m n →ₗ[ℂ] (GR n → ℂ)} {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ}
  {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem lam_cont (hBH : BanachHol) (hFL : FactorL) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) {B : Set ℂ} (hB : IsOpen B) {w : ℂ} (hw : w ∈ B) (F : ℂ → G → ℂ)
    (hFc : ContinuousOn (fun y : ℂ × G => F y.1 y.2) (B ×ˢ univ)) (hFh : ∀ g, DifferentiableOn ℂ (F · g) B)
    (hFi : ∀ z ∈ B, ∀ γ ∈ Γ, ∀ g, F z (γ * g) = F z g) : ContinuousAt (fun z => l (F z)) w := by
  obtain ⟨C, hCc, hCb⟩ := hG.Λbd l hl
  obtain ⟨L, hL⟩ := hFL G (invSub Γ) l C hCc (fun F hF => hF.1)
    (fun a F hF F' hF' => hG.Λadd l hl a F F' hF.1 hF'.1 hF.2 hF'.2)
    (fun F hF M hM => hCb F M hF.1 hF.2 hM)
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hFcont : ∀ z ∈ B, Continuous (F z) := by
    intro z hzB
    exact hFc.comp_continuous (continuous_const.prodMk continuous_id) (fun g => ⟨hzB, mem_univ g⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := hBH C B (fun z x => F z x) hB
    (hFc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩))
    (fun x => hFh x)
  have hfeq : ∀ z ∈ B, l (F z) = L (Φ z) := by
    intro z hzB
    have hmem : F z ∈ invSub Γ := ⟨hFcont z hzB, hFi z hzB⟩
    rw [hL (F z) hmem (hFcont z hzB)]
    congr 1
    ext x
    rw [hΦ z hzB x]
    rfl
  have hd : DifferentiableOn ℂ (fun z => l (F z)) B :=
    (L.differentiable.comp_differentiableOn hΦd).congr hfeq
  exact (hd.differentiableAt (hB.mem_nhds hw)).continuousAt

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end
