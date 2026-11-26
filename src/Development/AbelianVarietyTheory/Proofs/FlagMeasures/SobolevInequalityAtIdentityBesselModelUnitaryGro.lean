module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevValueAtOneFixedCompactDiagSignUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevValueAtOneFixedCompactDiagSignUnitary
open MeasureTheory Matrix Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.SobolevHaar

theorem ofReal_list_sum_le {α : Type} (S : List α) (f : α → ℝ) :
    ENNReal.ofReal (S.map f).sum ≤ (S.map fun a => ENNReal.ofReal (f a)).sum := by
  induction S with
  | nil => simp
  | cons a S ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

private theorem ofReal_integral_le_lintegral_ofReal {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)).le
  · rw [integral_undef hi]
    simp

theorem sobolev_at_one_compact : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ) (Q : Set (Formalism.REAL.UJ ε)), IsCompact Q ∧ (∀ l ∈ S, ∀ X ∈ l, Formalism.REAL.inG ε X) ∧ 0 ≤ C ∧ ∀ F : List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε)) → (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X → ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0) → ENNReal.ofReal (‖F [] 1‖ ^ 2) ≤ ENNReal.ofReal C * (S.map fun l => ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
  intro n ε

  obtain ⟨E, hE, hON, -⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  obtain ⟨s, hs, hsmall⟩ := exists_small n
  obtain ⟨c, -, hc, -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge n ε
  have hEl : ∀ i, E i ∈ GlobalTheory.GaugeConst.lieJ ε := fun i => GlobalTheory.GaugeConst.mem_lieJ.2 (hE i).1
  have hsm : ∀ (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ), (t : ℂ) • X = t • X := by
    intro t X
    ext a b
    simp [Complex.real_smul]

  obtain ⟨cu, hcuM, hcuc⟩ : ∃ cu : Fin (n ^ 2) → ℝ → Formalism.REAL.UJ ε,
      (∀ i t, umat (cu i t) = NormedSpace.exp ((t : ℂ) • E i)) ∧ ∀ i, Continuous (cu i) := by
    refine ⟨fun i t => GlobalTheory.GaugeConst.expJ ε (t • ⟨E i, hEl i⟩), fun i t => ?_, fun i => ?_⟩
    · rw [hsm]
      exact GlobalTheory.GaugeConst.uMat_expJ ε (t • ⟨E i, hEl i⟩)
    · exact (GlobalTheory.GaugeConst.continuous_expJ ε).comp (continuous_id.smul continuous_const)
  have hu1 : umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  have humul : ∀ x y : Formalism.REAL.UJ ε, umat (x * y) = umat x * umat y := fun _ _ => rfl
  have hinj : Function.Injective (fun x : Formalism.REAL.UJ ε => umat x) :=
    GlobalTheory.GaugeConst.uMat_injective ε
  have hcu0 : ∀ i, cu i 0 = 1 := by
    intro i
    apply hinj
    show umat (cu i 0) = umat 1
    rw [hcuM, hu1]
    simp
  have hcuadd : ∀ i a b, cu i (a + b) = cu i a * cu i b := by
    intro i a b
    apply hinj
    show umat (cu i (a + b)) = umat (cu i a * cu i b)
    rw [humul, hcuM, hcuM, hcuM, Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl (E i)).smul_left _).smul_right _)

  have hlist : ∀ l : List (Formalism.REAL.UJ ε), umat l.prod = (l.map fun x => umat x).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.prod_cons, humul, ih, List.map_cons, List.prod_cons]
  have hΘ : ∀ t : Fin (n ^ 2) → ℝ, umat ((List.ofFn fun i => cu i (t i)).prod) =
      (List.ofFn fun i => NormedSpace.exp ((t i : ℂ) • E i)).prod := by
    intro t
    rw [hlist, List.map_ofFn]
    simp only [Function.comp_def, hcuM]
  have hΘc : Continuous fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod :=
    GlobalTheory.continuous_prod_ofFn_curves (n ^ 2) cu hcuc
  obtain ⟨K, hchart⟩ : ∃ K : ℝ, ∀ Φ : Formalism.REAL.UJ ε → ENNReal, Measurable Φ →
      ∫⁻ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          Φ ((List.ofFn fun i => cu i (t i)).prod) ≤
        ENNReal.ofReal K * ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
          Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s), Φ y ∂(Formalism.REAL.muG ε) :=
    ⟨_, GlobalTheory.ProductChart.lintegral_chart_le n ε c s E
      (fun t => (List.ofFn fun i => cu i (t i)).prod) hc (fun i => (hE i).1) hON hs hsmall hΘ⟩

  have hD : ∀ i, ∀ v ∈ {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y},
      E i :: v ∈ {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y} := by
    intro i v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    · exact (hE i).1
    · exact hv Y hY
  obtain ⟨S, C0, hSA, hC0, hbound⟩ :=
    cube_sum {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y} [] (by simp) s hs
      (n ^ 2) cu (fun i v => E i :: v) (fun i => ⟨hcuc i, hcu0 i, hcuadd i⟩) hD
  refine ⟨S, C0 * max K 0,
    (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
      Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
    (isCompact_univ_pi fun _ => isCompact_Icc).image hΘc,
    fun l hl => (hSA l hl : ∀ Y ∈ l, Formalism.REAL.inG ε Y),
    mul_nonneg hC0 (le_max_right _ _), ?_⟩
  intro F hFc hFd
  have hmem : ∀ x : Formalism.REAL.UJ ε, umat x ∈ UJset ε := fun x => x.2
  have hFrc : ∀ v : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ v, Formalism.REAL.inG ε Y) →
      Continuous fun x : Formalism.REAL.UJ ε => F v (umat x) := fun v hv =>
    (hFc v hv).comp_continuous (GlobalTheory.GaugeConst.continuous_uMat ε) hmem
  have hFrd : ∀ v : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ v, Formalism.REAL.inG ε Y) →
      ∀ (i : Fin (n ^ 2)) (x : Formalism.REAL.UJ ε),
        HasDerivAt (fun t => F v (umat (x * cu i t))) (F (E i :: v) (umat x)) 0 := by
    intro v hv i x
    have h := hFd v hv (E i) (hE i).1 (umat x) (hmem x)
    have he : (fun t : ℝ => F v (umat (x * cu i t))) =
        fun t : ℝ => F v (umat x * NormedSpace.exp ((t : ℂ) • E i)) := by
      funext t
      rw [humul, hcuM]
    rw [he]
    exact h
  have hb : ‖F [] 1‖ ^ 2 ≤ C0 * (S.map fun v =>
      ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum :=
    hbound (fun v x => F v (umat x)) hFrc hFrd
  have hpt : ∀ v ∈ S,
      ENNReal.ofReal (∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2) ≤
      ENNReal.ofReal K * ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
          Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε) := by
    intro v hv
    have hcont := hFrc v (hSA v hv)
    have hmeas : Measurable fun y : Formalism.REAL.UJ ε => ENNReal.ofReal (‖F v (umat y)‖ ^ 2) :=
      (ENNReal.continuous_ofReal.comp (hcont.norm.pow 2)).measurable
    have h1 := ofReal_integral_le_lintegral_ofReal
      (volume.restrict (Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s)))
      (fun t => ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2) (fun t => sq_nonneg _)
    have h2 := hchart (fun y => ENNReal.ofReal (‖F v (umat y)‖ ^ 2)) hmeas
    exact h1.trans h2
  calc ENNReal.ofReal (‖F [] 1‖ ^ 2)
      ≤ ENNReal.ofReal (C0 * (S.map fun v =>
          ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
            ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum) :=
        ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal C0 * ENNReal.ofReal (S.map fun v =>
          ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
            ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum :=
        ENNReal.ofReal_mul hC0
    _ ≤ ENNReal.ofReal C0 * (S.map fun v => ENNReal.ofReal K *
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        gcongr
        exact (ofReal_list_sum_le _ _).trans (List.sum_le_sum hpt)
    _ = ENNReal.ofReal C0 * ENNReal.ofReal K * (S.map fun v =>
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        rw [List.sum_map_mul_left, mul_assoc]
    _ ≤ ENNReal.ofReal (C0 * max K 0) * (S.map fun v =>
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        rw [ENNReal.ofReal_mul hC0]
        gcongr
        exact le_max_left _ _

end GlobalTheory.SobolevHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevValueAtOneFixedCompactDiagSignUnitaryStatement
open MeasureTheory Matrix Formalism.MainNotions.S
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_valueAtOne_fixedCompact_diagSignUnitary : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ) (Q : Set (Formalism.REAL.UJ ε)), IsCompact Q ∧ (∀ l ∈ S, ∀ X ∈ l, Formalism.REAL.inG ε X) ∧ 0 ≤ C ∧ ∀ F : List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε)) → (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X → ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0) → ENNReal.ofReal (‖F [] 1‖ ^ 2) ≤ ENNReal.ofReal C * (S.map fun l => ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
  first | exact @GlobalTheory.SobolevHaar.sobolev_at_one_compact | exact GlobalTheory.SobolevHaar.sobolev_at_one_compact | (intros; apply GlobalTheory.SobolevHaar.sobolev_at_one_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnitaryHaarTransportDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnitaryHaarTransportDiagonal
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped ENNReal

noncomputable section

namespace GlobalTheory.HaarTransport

theorem isMatGroup_UH_of_sq {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) : PI.IsMatGroup (UH H) := by
  refine ⟨?_, ?_, fun a ha b hb => ?_, fun g hg => ?_⟩
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · show (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * H * 1 = H
    simp
  · have ha' : aᴴ * H * a = H := ha
    have hb' : bᴴ * H * b = H := hb
    show (a * b)ᴴ * H * (a * b) = H
    calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [ha', hb']
  · have hg' : gᴴ * H * g = H := hg
    have h1 : (H * gᴴ * H) * g = 1 := by
      rw [Matrix.mul_assoc H, Matrix.mul_assoc H, hg', hH]
    have hu : IsUnit g.det := Matrix.isUnit_det_of_left_inverse h1
    refine ⟨?_, Matrix.mul_nonsing_inv _ hu⟩
    show (g⁻¹)ᴴ * H * g⁻¹ = H
    calc (g⁻¹)ᴴ * H * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * H * g) * g⁻¹ := by rw [hg']
      _ = (g * g⁻¹)ᴴ * H * (g * g⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [Matrix.mul_nonsing_inv _ hu]; simp

theorem haar_transport : ∀ (k r : ℕ) (μG : Measure (Mt k r)) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r),
    IsHaarOn (GG k r) μG → IsUnit P.det → Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r →
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) = c * ∫⁻ x, φ x ∂μG := by
  intro k r μG ε P hμ hP hH
  have hce := Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) (P := P) Formalism.REAL.uJEmb hP
  have hm := hce.continuous.measurable
  have hme := hce.measurableEmbedding
  have hG : PI.IsMatGroup (GG k r) := isMatGroup_UH_of_sq _ (hpkFacts k r).2.1
  have hmem : ∀ y, Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P y) ∈ GG k r := fun y =>
    (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_range_iff Formalism.REAL.uJEmb uHConj hP hH _).1 ⟨y, rfl⟩
  have hν : PI.IsHaarOnM (GG k r) ((Formalism.REAL.muG ε).map (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P)) := by
    refine ⟨hme.sigmaFinite_map, ?_, ?_, ?_⟩
    · exact (Measure.map_ne_zero_iff hm.aemeasurable).2 (NeZero.ne _)
    · have hcl : IsClosed {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r} := hG.1
      show (Measure.map _ _) {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r}ᶜ = 0
      rw [Measure.map_apply hm hcl.measurableSet.compl]
      have : Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P ⁻¹' {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r}ᶜ = ∅ := by
        ext y; simpa using hmem y
      rw [this, measure_empty]
    · intro a ha
      obtain ⟨u, hu⟩ := (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_range_iff Formalism.REAL.uJEmb uHConj hP hH a).2 ha
      subst hu
      have hl : Measurable (PI.lmulQ (m := 2 * r + k + 1) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u)) :=
        (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_cont (k := k) (r := r) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u)).measurable
      rw [Measure.map_map hl hm]
      have e : PI.lmulQ (m := 2 * r + k + 1) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u) ∘ Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P =
          Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P ∘ (fun v => u * v) := by
        funext v; exact Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_phi hP u v
      rw [e, ← Measure.map_map hm (measurable_const_mul u), map_mul_left_eq_self]
  have hμ' : PI.IsHaarOnM (GG k r) μG := hμ
  obtain ⟨c, -, hct, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ μG hG hμ').1 _ hν
  refine ⟨c, hct.ne, fun φ hφ => ?_⟩
  have h1 : ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) =
      ∫⁻ y, φ (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P y) ∂(Formalism.REAL.muG ε) := rfl
  rw [h1, ← lintegral_map hφ hm, hc, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.HaarTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnitaryHaarTransportDiagonalStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselUnitary_haar_transport_diagonal : ∀ (k r : ℕ) (μG : Measure (Mt k r)) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r), IsHaarOn (GG k r) μG → IsUnit P.det → Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) = c * ∫⁻ x, φ x ∂μG := by
  first | exact @GlobalTheory.HaarTransport.haar_transport | exact GlobalTheory.HaarTransport.haar_transport | (intros; apply GlobalTheory.HaarTransport.haar_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightDerivativeSmoothOnIndefiniteUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightDerivativeSmoothOnIndefiniteUnitaryGroup
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ContDiff

open scoped Nat Topology

noncomputable section

namespace GlobalTheory.RightDerivSmooth

variable {n : ℕ}


set_option backward.isDefEq.respectTransparency false in
theorem exp_intertwine (Y Z H : Matrix (Fin n) (Fin n) ℂ) (h : Y * H = H * Z) :
    NormedSpace.exp Y * H = H * NormedSpace.exp Z := by
  have hp : ∀ m : ℕ, Y ^ m * H = H * Z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have h1 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) (NormedSpace.exp Y * H) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y).mul_right H
  have h2 : HasSum (fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m)) (H * NormedSpace.exp Z) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Z).mul_left H
  have e : (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) = fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m) := by
    funext m
    rw [Matrix.smul_mul, hp, Matrix.mul_smul]
  rw [e] at h1
  exact h1.unique h2


set_option backward.isDefEq.respectTransparency false in
theorem inUH_exp {H X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    inUH H (NormedSpace.exp ((t : ℂ) • X)) := by
  have hY : ((t : ℂ) • X)ᴴ * H + H * ((t : ℂ) • X) = 0 := by
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hX, smul_zero]
  generalize (t : ℂ) • X = Y at hY
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  have h1 : Yᴴ * H = H * (-Y) := by
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hY
  rw [← Matrix.exp_conjTranspose, exp_intertwine _ _ _ h1, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

theorem inUH_mul {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha', hb']


set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  open scoped Matrix.Norms.Operator in
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  open scoped Matrix.Norms.Operator in
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_mul_exp (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_entry X k j).const_mul _

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_local {H X g : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (hg : inUH H g)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (e : ∀ h ∈ U, inUH H h → f h = F h) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hc := hasDerivAt_mul_exp g X
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hd : HasFDerivAt F (fderiv ℝ F g) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [h0]
    exact ((hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) hc
  refine h1.congr_of_eventuallyEq ?_
  have h2 : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hc.continuousAt.eventually (hU.mem_nhds (by simpa only [h0] using hgU))
  filter_upwards [h2] with t ht
  exact e _ ht (inUH_mul hg (inUH_exp hX t))

end GlobalTheory.RightDerivSmooth

section
open GlobalTheory.RightDerivSmooth
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


set_option backward.isDefEq.respectTransparency false in
theorem GlobalTheory.RightDerivSmooth.right_derivative_smooth_on_unitary_group : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f →
    ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 := by
  intro n H X E _ _ f hX hf
  have hder : ∀ g, inUH H g → ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), ∃ F : Matrix (Fin n) (Fin n) ℂ → E,
      IsOpen U ∧ g ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ (∀ h ∈ U, inUH H h → f h = F h) ∧
      ∀ h ∈ U, inUH H h → rdM X f h = fderiv ℝ F h (h * X) ∧
        HasDerivAt (fun t : ℝ => f (h * NormedSpace.exp ((t : ℂ) • X))) (rdM X f h) 0 := by
    intro g hg
    obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
    refine ⟨U, F, hU, hgU, hF, e, fun h hhU hh => ?_⟩
    have hd := hasDerivAt_local hX hh hU hhU hF e
    have hr : rdM X f h = fderiv ℝ F h (h * X) := hd.deriv
    exact ⟨hr, hr ▸ hd⟩
  refine ⟨?_, ?_, fun g hg => ?_⟩
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, e, -⟩ := hder g hg
    have hFc : ContinuousWithinAt F {g | inUH H g} g :=
      ((hF.continuousOn).continuousAt (hU.mem_nhds hgU)).continuousWithinAt
    refine hFc.congr_of_eventuallyEq ?_ (e g hgU hg)
    filter_upwards [inter_mem_nhdsWithin {g | inUH H g} (hU.mem_nhds hgU)] with h hh
    exact e h hh.2 hh.1
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, -, hr⟩ := hder g hg
    refine ⟨U, fun h => fderiv ℝ F h (h * X), hU, hgU, ?_, fun h hhU hh => (hr h hhU hh).1⟩
    have h1 : ContDiffOn ℝ ∞ (fun h => fderiv ℝ F h) U := hF.fderiv_of_isOpen hU (le_of_eq rfl)
    have h2 : ContDiff ℝ ∞ (fun h : Matrix (Fin n) (Fin n) ℂ => h * X) :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff
    exact h1.clm_apply h2.contDiffOn
  · obtain ⟨U, F, hU, hgU, hF, -, hr⟩ := hder g hg
    exact (hr g hgU hg).2

end

theorem GlobalTheory.rdM_smoothOnH : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f →
    ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 :=
  fun n H X E _ _ f hX hf => GlobalTheory.RightDerivSmooth.right_derivative_smooth_on_unitary_group n H X E f hX hf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightDerivativeSmoothOnIndefiniteUnitaryGroupStatement
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f → ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧ ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 := by
  first | exact @GlobalTheory.rdM_smoothOnH | exact GlobalTheory.rdM_smoothOnH | (intros; apply GlobalTheory.rdM_smoothOnH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevInequalityAtIdentityBesselModelUnitaryGro
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff ENNReal

namespace GlobalTheory.SobAtOne

theorem ofReal_list_sum {α : Type*} (S : List α) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ENNReal.ofReal (S.map g).sum = (S.map fun a => ENNReal.ofReal (g a)).sum := by
  induction S with
  | nil => simp
  | cons a S ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.ofReal_add (hg a) (List.sum_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact hg b), ih]

theorem sobolev_at_one_G : ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GG k r) μG → ∃ (C : ℝ)
    (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsCompact K₀ ∧ (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧
    ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B),
      SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C * (Ws.map fun ws =>
        ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum := by
  intro k r μG hμ
  obtain ⟨-, -, -, ε, -, P, hPd, hPJ⟩ := hpkFacts k r
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hPd
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  obtain ⟨S, C, Q, hQ, hS, hC, hsob⟩ := GlobalTheory.T.sobolev_valueAtOne_fixedCompact_diagSignUnitary (2 * r + k + 1) ε
  obtain ⟨c, hc, hB⟩ := GlobalTheory.T.besselUnitary_haar_transport_diagonal k r μG ε P hμ hPd hPJ
  let cj : Mat k r → Mat k r := fun Y => P⁻¹ * Y * P
  have hcjc : Continuous cj := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let ψ : Formalism.REAL.UJ ε → Mt k r := fun y => Matrix.of.symm (cj (umat y))
  have hψc : Continuous ψ := hcjc.comp (Units.continuous_val.comp continuous_subtype_val)
  have hmemG : ∀ g : Mat k r, Formalism.REAL.inUJ ε g → cj g ∈ GG k r := by
    intro g hg
    show cj g ∈ UH (Hpk k r)
    rw [uHConj _ ε (Hpk k r) P hPd hPJ]
    have e : P * cj g * P⁻¹ = g := by
      simp only [cj, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
      rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
    rw [e]; exact hg
  have hlie : ∀ X, Formalism.REAL.inG ε X → InLieHpk k r (cj X) := by
    intro X hX
    have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
    have e1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPP, conjTranspose_one]
    show (P⁻¹ * X * P)ᴴ * Hpk k r + Hpk k r * (P⁻¹ * X * P) = 0
    rw [← hPJ]
    calc (P⁻¹ * X * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) + Pᴴ * Formalism.REAL.Jm ε * P * (P⁻¹ * X * P)
        = Pᴴ * (Xᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (P * P⁻¹) * X) * P := by
          simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [e1, hPP, Matrix.mul_one, Matrix.mul_one, hX', Matrix.mul_zero, Matrix.zero_mul]
  have hwm : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ Y ∈ l.map cj, InLieHpk k r Y := by
    intro l hl Y hY
    obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
    exact hlie Z (hl Z hZ)
  have hK₀ : IsCompact (ψ '' Q) := hQ.image hψc
  have hK₀G : ∀ x ∈ ψ '' Q, Matrix.of x ∈ GG k r := by
    rintro _ ⟨y, -, rfl⟩
    change Matrix.of (Matrix.of.symm (cj (umat y))) ∈ GG k r
    rw [Equiv.apply_symm_apply]
    exact hmemG _ y.2
  have hfin : IsFiniteMeasureOnCompacts μG := by
    obtain ⟨hG, -⟩ := closedSub_groups k r (bvec (wI k r (Fin.last k))) (fun i hi => by
      simp only [bvec, wI]
      rw [Pi.single_apply, if_neg]
      intro h; rw [h] at hi; simp at hi) (by
      have h : herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) =
          Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
        simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [Tz, h]
      simp [Hpk, wI])
    exact ⟨fun K hK => (haarOn_locFinite_openPos k r (GG k r) μG hG hμ).1 K hK⟩
  refine ⟨C * c.toReal, S.map (List.map cj), ψ '' Q, hK₀, ?_, ?_⟩
  · intro ws hws X hX
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hws
    exact hwm l (hS l hl) X hX
  intro B _ _ _ f hf
  have hword : ∀ l : List (Mat k r), (∀ Y ∈ l, InLieHpk k r Y) → SmoothOnH (Hpk k r) (rdWord l f) := by
    intro l
    induction l with
    | nil => intro _; exact hf
    | cons X l ih =>
      intro hl
      exact (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) X B (rdWord l f) (hl X List.mem_cons_self)
        (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY))).2.1
  have hcont : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) →
      ContinuousOn (rdWord (l.map cj) f) (GG k r) := fun l hl =>
    (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) 0 B _ (by simp) (hword _ (hwm l hl))).1
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hI : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) →
      ContinuousOn (fun x : Mt k r => ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2) (ψ '' Q) := fun l hl =>
    (((hcont l hl).comp hof.continuousOn fun x hx => hK₀G x hx).norm).pow 2
  have hnn : 0 ≤ C * c.toReal * ((S.map (List.map cj)).map fun ws =>
      ∫ x in ψ '' Q, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum :=
    mul_nonneg (mul_nonneg hC ENNReal.toReal_nonneg) (List.sum_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact integral_nonneg fun _ => by positivity)
  by_cases h0 : f 1 = 0
  · rw [h0, norm_zero]; simpa using hnn
  haveI : Nontrivial B := ⟨⟨f 1, 0, h0⟩⟩
  obtain ⟨ℓ, hℓ1, hℓ⟩ := exists_dual_vector' ℂ (f 1)
  let F : List (Mat k r) → Mat k r → ℂ := fun l g => ℓ (rdWord (l.map cj) f (cj g))
  have hFc : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε) := fun l hl =>
    ℓ.continuous.comp_continuousOn ((hcont l hl).comp hcjc.continuousOn fun g hg => hmemG g hg)
  have hFd : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X →
      ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0 := by
    intro l hl X hX g hg
    have hA := (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) (cj X) B (rdWord (l.map cj) f) (hlie X hX) (hword _ (hwm l hl))).2.2
      (cj g) (hmemG g hg)
    have h2 := (ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    have e : ∀ t : ℝ, cj (g * NormedSpace.exp ((t : ℂ) • X)) = cj g * NormedSpace.exp ((t : ℂ) • cj X) := by
      intro t
      have e2 : (t : ℂ) • cj X = P⁻¹ * ((t : ℂ) • X) * P := by
        simp only [cj, Matrix.mul_smul, Matrix.smul_mul]
      rw [e2, Matrix.exp_conj' P _ hPu]
      simp only [cj, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P P⁻¹, hPP, Matrix.one_mul]
    have e3 : (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) = (ℓ.restrictScalars ℝ) ∘
        (fun t : ℝ => rdWord (l.map cj) f (cj g * NormedSpace.exp ((t : ℂ) • cj X))) := by
      funext t; simp only [F, Function.comp_apply, e]; rfl
    rw [e3]; exact h2
  have key := hsob F hFc hFd
  have hF1 : ‖F [] 1‖ = ‖f 1‖ := by
    have : cj 1 = 1 := by simp [cj, hPP']
    simp only [F, List.map_nil, this]
    show ‖ℓ (f 1)‖ = ‖f 1‖
    rw [hℓ]; simp
  rw [hF1] at key
  have hstep : ∀ l ∈ S, ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε) ≤
      c * ENNReal.ofReal (∫ x in ψ '' Q, ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2 ∂μG) := by
    intro l hlS
    have hl := hS l hlS
    classical
    set φ : Mt k r → ℝ≥0∞ := (ψ '' Q).indicator
      (fun x => ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2)) with hφ
    have hφm : Measurable φ := by
      have := ContinuousOn.measurable_piecewise (f := fun x : Mt k r =>
        ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2)) (g := 0)
        (ENNReal.continuous_ofReal.comp_continuousOn (hI l hl)) continuousOn_const hK₀.isClosed.measurableSet
      rwa [Set.piecewise_eq_indicator] at this
    have hint : IntegrableOn (fun x : Mt k r => ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2) (ψ '' Q) μG :=
      (hI l hl).integrableOn_compact hK₀
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => by positivity),
      ← lintegral_indicator hK₀.isClosed.measurableSet, ← hφ, ← hB φ hφm]
    refine le_trans ?_ (setLIntegral_le_lintegral Q _)
    refine setLIntegral_mono (hφm.comp hψc.measurable) fun y hy => ?_
    have hψy : ψ y ∈ ψ '' Q := ⟨y, hy, rfl⟩
    have hφy : φ (ψ y) = ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of (ψ y))‖ ^ 2) := by
      rw [hφ]; exact Set.indicator_of_mem hψy _
    show _ ≤ φ (ψ y)
    rw [hφy]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    have : (Matrix.of (ψ y) : Mat k r) = cj (umat y) := by
      change Matrix.of (Matrix.of.symm (cj (umat y))) = _
      exact Equiv.apply_symm_apply _ _
    rw [this]
    refine (ℓ.le_opNorm _).trans ?_
    rw [hℓ1, one_mul]
  have hsum := List.sum_le_sum hstep
  rw [List.sum_map_mul_left, ← ofReal_list_sum S _ (fun l => integral_nonneg fun _ => by positivity)] at hsum
  have htot : ENNReal.ofReal (‖f 1‖ ^ 2) ≤ ENNReal.ofReal C * (c * ENNReal.ofReal
      ((S.map fun l => ∫ x in ψ '' Q, ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2 ∂μG).sum)) := key.trans (by gcongr)
  conv_rhs at htot => rw [← ENNReal.ofReal_toReal hc]
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hC, ← mul_assoc] at htot
  rw [List.map_map] at hnn ⊢
  exact (ENNReal.ofReal_le_ofReal_iff hnn).1 htot

end GlobalTheory.SobAtOne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevInequalityAtIdentityBesselModelUnitaryGroStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_inequality_at_identity_besselModelUnitaryGroup : ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GG k r) μG → ∃ (C : ℝ) (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsCompact K₀ ∧ (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C * (Ws.map fun ws => ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum := by
  first | exact @GlobalTheory.SobAtOne.sobolev_at_one_G | exact GlobalTheory.SobAtOne.sobolev_at_one_G | (intros; apply GlobalTheory.SobAtOne.sobolev_at_one_G <;> assumption)
end
