module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodizationIntegralUnfolding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodizationIntegralUnfolding
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Lattice

theorem tsum_setIntegral_sub_rat : ∀ (D : D7) (m r : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r)), IsCovolOne (ratMx D m r) μr 𝓕r →
    ∀ f : Mx D m r → ℂ, Continuous f → ∀ B : ℝ≥0, (∀ y, ∑' p : Matrix (Fin m) (Fin r) D.host.E, ‖f (y - rat p)‖ₑ ≤ B) →
      Integrable f μr ∧ ∑' p : Matrix (Fin m) (Fin r) D.host.E, ∫ y in 𝓕r, f (y - rat p) ∂μr = ∫ t, f t ∂μr := by
  intro D m r μr 𝓕r h f hf B hB
  obtain ⟨hHaar, hFD, hvol⟩ := h
  haveI := hHaar
  haveI : BorelSpace (Mx D m r) := ⟨rfl⟩
  haveI : Countable D.host.E :=
    Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin m) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin m → Fin r → D.host.E))
  have hinc : Function.Injective (Formalism.L2.Theta.incA D) := by
    have h0 : Function.Injective (algebraMap ↥D.host.F (AF ↥D.host.F)) :=
      NumberField.AdeleRing.algebraMap_injective _ _
    exact Algebra.TensorProduct.includeRight_injective h0
  have hmem : ∀ p : Matrix (Fin m) (Fin r) D.host.E, rat p ∈ ratMx D m r :=
    fun p => AddMonoidHom.mem_range.mpr ⟨p, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Matrix (Fin m) (Fin r) D.host.E ≃ ratMx D m r,
      ∀ p, ((e p : ratMx D m r) : Mx D m r) = rat p := by
    refine ⟨Equiv.ofBijective (fun p => ⟨rat p, hmem p⟩) ⟨fun p q hpq => ?_, fun g => ?_⟩, fun p => rfl⟩
    · have h2 : p.map (Formalism.L2.Theta.incA D) = q.map (Formalism.L2.Theta.incA D) :=
        congrArg Subtype.val hpq
      exact Matrix.map_injective hinc h2
    · obtain ⟨p, hp⟩ := AddMonoidHom.mem_range.mp g.2
      exact ⟨p, Subtype.ext hp⟩
  haveI : Countable (ratMx D m r) := Countable.of_equiv _ e
  haveI : VAddInvariantMeasure (ratMx D m r) (Mx D m r) μr :=
    ⟨fun c s _ => measure_preimage_add μr (c : Mx D m r) s⟩
  have hv : ∀ (p : Matrix (Fin m) (Fin r) D.host.E) (x : Mx D m r), -(e p) +ᵥ x = x - rat p := by
    intro p x
    change ((-(e p) : ratMx D m r) : Mx D m r) + x = x - rat p
    rw [AddSubgroup.coe_neg, he]
    exact neg_add_eq_sub (rat p) x
  haveI : ContinuousSub (Mx D m r) := IsTopologicalAddGroup.to_continuousSub
  have hmeas : ∀ p : Matrix (Fin m) (Fin r) D.host.E, Measurable (fun x => ‖f (x - rat p)‖ₑ) :=
    fun p => (hf.comp (continuous_id.sub continuous_const)).measurable.enorm
  have hlin : ∫⁻ x, ‖f x‖ₑ ∂μr ≤ B := by
    rw [hFD.lintegral_eq_tsum', ← e.tsum_eq]
    simp_rw [hv]
    rw [← lintegral_tsum (fun p => (hmeas p).aemeasurable)]
    calc ∫⁻ x in 𝓕r, ∑' p, ‖f (x - rat p)‖ₑ ∂μr ≤ ∫⁻ _ in 𝓕r, (B : ℝ≥0∞) ∂μr :=
          lintegral_mono fun x => hB x
      _ = B := by rw [lintegral_const, Measure.restrict_apply_univ, hvol, mul_one]
  have hint : Integrable f μr := ⟨hf.aestronglyMeasurable, lt_of_le_of_lt hlin ENNReal.coe_lt_top⟩
  refine ⟨hint, ?_⟩
  rw [hFD.integral_eq_tsum' f hint, ← e.tsum_eq]
  simp_rw [hv]

end GlobalTheory.CompanionTheory.EisUnfold.Lattice
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodizationIntegralUnfoldingStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodization_integral_unfolding : ∀ (D : D7) (m r : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r)), IsCovolOne (ratMx D m r) μr 𝓕r →
    ∀ f : Mx D m r → ℂ, Continuous f → ∀ B : ℝ≥0, (∀ y, ∑' p : Matrix (Fin m) (Fin r) D.host.E, ‖f (y - rat p)‖ₑ ≤ B) →
      Integrable f μr ∧ ∑' p : Matrix (Fin m) (Fin r) D.host.E, ∫ y in 𝓕r, f (y - rat p) ∂μr = ∫ t, f t ∂μr := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Lattice.tsum_setIntegral_sub_rat | exact GlobalTheory.CompanionTheory.EisUnfold.Lattice.tsum_setIntegral_sub_rat | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Lattice.tsum_setIntegral_sub_rat <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterIntegralOrthogonality
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterIntegralOrthogonality
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Orth

variable {D : D7}

theorem trA_incA_eq (e : D.host.E) :
    trA (incA D e) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  have h : LinearMap.mulLeft (AF D.host.F) (incA D e) =
      LinearMap.baseChange (AF D.host.F) (LinearMap.mulLeft D.host.F e) := by
    ext b
    simp [TensorProduct.AlgebraTensorModule.curry_apply, incA, inclR, LinearMap.baseChange_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
  simp only [trA, Algebra.trace_apply]
  change LinearMap.trace _ _ (LinearMap.mulLeft (AF D.host.F) (incA D e)) =
    algebraMap _ _ (LinearMap.trace _ _ (LinearMap.mulLeft D.host.F e))
  rw [h, LinearMap.trace_baseChange]

theorem trA_smul_half (x : AF D.host.F) :
    trA (x • half D) = x := by
  have hE := D.host.toHostAx.der.finrank_E
  have hF := D.host.toHostAx.der.finrank_F
  have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
  have htow := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    rw [hF] at hpos htow
    rw [hE] at htow
    have h4 : 2 * D.R.ord * Module.finrank D.host.F D.host.E = 2 * D.R.ord * 2 := by
      rw [htow]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  have hhalf : trA (half D) = 1 := by
    rw [half, trA_incA_eq]
    have : (1 / 2 : D.host.E) = algebraMap D.host.F D.host.E (1 / 2) := by
      rw [map_div₀, map_one, map_ofNat]
    rw [this, Algebra.trace_algebraMap, h2]
    norm_num
  have hlin : trA (x • half D) = x * trA (half D) := by
    simp only [trA, map_smul, smul_eq_mul]
  rw [hlin, hhalf, mul_one]

theorem inner_rat_eq (V : HSp D) {s : ℕ} (q : Matrix (Fin V.rank) (Fin s) D.host.E) (y : Mx D V.rank s) :
    GlobalTheory.StdUnn.inner V (rat q) y = rat (qᴴ * V.gram) ⬝ y := by
  simp only [GlobalTheory.StdUnn.inner]
  rw [← rat_conjTranspose, gA, ← Matrix.mul_assoc, ← rat_mul]

theorem chi_add (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {s : ℕ} (x y u : Mx D V.rank s) :
    ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x (y + u)))) =
      ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x y))) * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x u))) := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_add, Matrix.trace_add, trA, map_add (f := _), AddChar.map_add_eq_mul]

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) {γ : Mx D V.rank s} (hγ : γ ∈ ratMx D V.rank s) :
    ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) γ))) = 1 := by
  obtain ⟨g, rfl⟩ := mem_ratMx.mp hγ
  have htr : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E), Matrix.trace (rat M) = incA D (Matrix.trace M) := by
    intro n M
    set_option synthInstance.maxHeartbeats 100000 in
      simp [rat, Matrix.trace, map_sum]
  rw [inner_rat_eq]
  change ψ (trA (Matrix.trace (rat (qᴴ * V.gram) * rat g))) = 1
  rw [← rat_mul, htr, trA_incA_eq]
  exact hψ.2.2.1 _

theorem exists_chi_ne_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    {q : Matrix (Fin V.rank) (Fin s) D.host.E} (hq : q ≠ 0) :
    ∃ u : Mx D V.rank s, ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) u))) ≠ 1 := by
  obtain ⟨x, hx⟩ := hψ.2.2.2
  have hM : qᴴ * V.gram ≠ 0 := by
    intro h
    apply hq
    have h1 : qᴴ = 0 := by
      rw [← Matrix.mul_nonsing_inv_cancel_right V.gram qᴴ (gram_isUnit_det V), h, Matrix.zero_mul]
    simpa using congrArg Matrix.conjTranspose h1
  obtain ⟨i, j, hij⟩ : ∃ i j, (qᴴ * V.gram) i j ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hM (Matrix.ext hne)
  have key : ∀ (A : Mx D s V.rank) (c : AE D), Matrix.trace (A * Matrix.single j i c) = A i j * c := by
    intro A c
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  refine ⟨Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D)), ?_⟩
  rw [inner_rat_eq]
  change ψ (trA (Matrix.trace (rat (qᴴ * V.gram) *
      Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D))))) ≠ 1
  rw [key, show rat (qᴴ * V.gram) i j = incA D ((qᴴ * V.gram) i j) from rfl, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ hij, map_one, one_mul, trA_smul_half]
  exact hx

theorem orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (s : ℕ)
    (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)), IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ q : Matrix (Fin V.rank) (Fin s) D.host.E,
      (q = 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 1) ∧
      (q ≠ 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 0) := by
  intro D ψ hψ V s μs 𝓕s hcov q
  constructor
  · rintro rfl
    have h0 : ∀ y : Mx D V.rank s, ψ (trA (Matrix.trace (inner V (rat (0 : Matrix (Fin V.rank) (Fin s) D.host.E)) y))) = 1 := by
      intro y
      simp [GlobalTheory.StdUnn.inner, rat_zero, adj_zero, trA]
    simp_rw [h0]
    rw [MeasureTheory.setIntegral_const]
    simp [Measure.real, hcov.2.2]
  · intro hq
    obtain ⟨u, hu⟩ := exists_chi_ne_one hψ V hq
    set φ : Mx D V.rank s → ℂ := fun y => ψ (trA (Matrix.trace (inner V (rat q) y))) with hφ
    have hper : ∀ γ ∈ ratMx D V.rank s, ∀ a, φ (γ + a) = φ a := by
      intro γ hγ a
      simp only [hφ]
      rw [chi_add, chi_rat hψ V q hγ, one_mul]
    have h1 := covolOne_integral_add hcov φ hper u
    have h2 : ∀ a, φ (a + u) = φ u * φ a := by
      intro a
      simp only [hφ]
      rw [chi_add, mul_comm]
    simp only [h2] at h1
    rw [MeasureTheory.integral_const_mul] at h1
    have h3 : (φ u - 1) * ∫ y in 𝓕s, φ y ∂μs = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hu
    · exact h

end GlobalTheory.CompanionTheory.EisUnfold.Orth

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterIntegralOrthogonalityStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_integral_orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (s : ℕ)
    (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)), IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ q : Matrix (Fin V.rank) (Fin s) D.host.E,
      (q = 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 1) ∧
      (q ≠ 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 0) := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality | exact GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfolding
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

namespace Core

variable {D : D7}

theorem continuous_trA_AE : Continuous (trA (D := D)) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))

theorem continuous_halfTr_AE : Continuous (halfTr (D := D)) := by
  unfold halfTr
  exact continuous_const.mul continuous_trA_AE

theorem continuous_inner_pair (V : HSp D) {n : ℕ} {X : Type*} [TopologicalSpace X] {u v : X → Mx D V.rank n}
    (hu : Continuous u) (hv : Continuous v) : Continuous fun x => inner V (u x) (v x) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold StdUnn.inner
  exact (continuous_adj.comp hu).matrix_mul (continuous_const.matrix_mul hv)

theorem continuous_colJoin_left {X : Type*} [TopologicalSpace X] {m r s : ℕ} {u : X → Mx D m r} (hu : Continuous u)
    (v : Mx D m s) : Continuous fun x => colJoin (u x) v := by
  refine continuous_matrix fun i k => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [colJoin_castAdd]
    exact hu.matrix_elem i j
  · simp only [colJoin_natAdd]
    exact continuous_const

theorem continuous_quad (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) :
    Continuous fun t : Mx D V.rank r =>
      ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_halfTr_AE.comp
    (continuous_const.matrix_mul (continuous_inner_pair V continuous_id continuous_id)).matrix_trace)

theorem continuous_lin (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (x : Mx D V.rank s) :
    Continuous fun y : Mx D V.rank s => ψ (trA (Matrix.trace (inner V x y))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_trA_AE.comp
    (continuous_inner_pair V continuous_const continuous_id).matrix_trace)

theorem enorm_char (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (x : AF D.host.F) : ‖ψ x‖ₑ = 1 := by
  rw [← ofReal_norm_eq_enorm, hψ.2.1, ENNReal.ofReal_one]

theorem join_mul_eq {m r s : ℕ} (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (p : Matrix (Fin m) (Fin r) D.host.E) (q : Matrix (Fin m) (Fin s) D.host.E) (y : Mx D m r) :
    HMul.hMul (colJoin (rat p - y) (rat q)) (rat a) =
      rat (colJoin p q * a) + -(HMul.hMul (colJoin y (0 : Mx D m s)) (rat a) : Mx D m (r + s)) := by
  have h : colJoin (rat p - y) (rat q) = colJoin (rat p) (rat q) - colJoin y (0 : Mx D m s) := by
    rw [← colJoin_sub, sub_zero]
  rw [h, Matrix.sub_mul, rat_mul, rat_colJoin, sub_eq_add_neg]

theorem join_mul_injective {m r s : ℕ} {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det) :
    Function.Injective fun pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E =>
      colJoin pq.1 pq.2 * a := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  have h' : colJoin p q = colJoin p' q' := by
    have := congrArg (· * a⁻¹) h
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv a ha] using this
  obtain ⟨h1, h2⟩ := colJoin_injective h'
  rw [h1, h2]

theorem tsum_join_le {m r s : ℕ} {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det)
    {Φ : Mx D m (r + s) → ℂ} {B : ℝ≥0}
    (hB : ∀ w, ∑' ξ : Matrix (Fin m) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) (y : Mx D m r) :
    ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
      ‖Φ (HMul.hMul (colJoin (rat pq.1 - y) (rat pq.2)) (rat a))‖ₑ ≤ B := by
  set w : Mx D m (r + s) := -(HMul.hMul (colJoin y (0 : Mx D m s)) (rat a) : Mx D m (r + s)) with hw
  calc ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
        ‖Φ (HMul.hMul (colJoin (rat pq.1 - y) (rat pq.2)) (rat a))‖ₑ
      = ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
          (fun ξ : Matrix (Fin m) (Fin (r + s)) D.host.E => ‖Φ (rat ξ + w)‖ₑ) (colJoin pq.1 pq.2 * a) := by
        refine tsum_congr fun pq => ?_
        simp only [join_mul_eq, hw]
    _ ≤ ∑' ξ : Matrix (Fin m) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective (join_mul_injective (m := m) ha) (fun ξ : Matrix (Fin m) (Fin (r + s)) D.host.E => ‖Φ (rat ξ + w)‖ₑ)
    _ ≤ B := hB w

theorem countable_mat (D : D7) (m n : ℕ) : Countable (Matrix (Fin m) (Fin n) D.host.E) := by
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  exact inferInstanceAs (Countable (Fin m → Fin n → D.host.E))

theorem enorm_cellTerm (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (Φ : Mx D V.rank (r + s) → ℂ) (p : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) :
    ‖cellTerm ψ V b a Φ p q y₁ y₂‖ₑ = ‖Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a))‖ₑ := by
  simp only [cellTerm, enorm_mul, enorm_char ψ hψ, one_mul]

def cellRest (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r))) *
    Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a))

theorem continuous_cellRest (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    {Φ : Mx D V.rank (r + s) → ℂ} (hΦ : Continuous Φ) (p : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) : Continuous (cellRest ψ V b a Φ p q) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, -⟩ := lattice_Mx D V.rank r
  haveI : ContinuousSub (Mx D V.rank r) := IsTopologicalAddGroup.to_continuousSub
  have h1 : Continuous fun y₁ : Mx D V.rank r => y₁ - rat p := continuous_id.sub continuous_const
  have h2 : Continuous fun y₁ : Mx D V.rank r => rat p - y₁ :=
    (continuous_const (y := rat p)).sub continuous_id
  exact ((continuous_quad ψ hψ V b).comp h1).mul
    (hΦ.comp ((continuous_colJoin_left h2 _).matrix_mul continuous_const))

def cellZero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ) (t : Mx D V.rank r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
    Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a))

theorem cellRest_zero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (y : Mx D V.rank r) :
    cellRest ψ V b a Φ p 0 y = cellZero ψ V b a Φ (y - rat p) := by
  simp only [cellRest, cellZero, rat_zero, neg_sub]

theorem continuous_cellZero (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    {Φ : Mx D V.rank (r + s) → ℂ} (hΦ : Continuous Φ) : Continuous (cellZero (s := s) ψ V b a Φ) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, -⟩ := lattice_Mx D V.rank r
  exact (continuous_quad ψ hψ V b).mul
    (hΦ.comp ((continuous_colJoin_left continuous_neg _).matrix_mul continuous_const))

theorem tsum_cellZero_le (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det)
    {Φ : Mx D V.rank (r + s) → ℂ} {B : ℝ≥0}
    (hB : ∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) (y : Mx D V.rank r) :
    ∑' p : Matrix (Fin V.rank) (Fin r) D.host.E, ‖cellZero (s := s) ψ V b a Φ (y - rat p)‖ₑ ≤ B := by
  have hinj : Function.Injective fun p : Matrix (Fin V.rank) (Fin r) D.host.E =>
      ((p, 0) : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E) :=
    fun _ _ h => congrArg Prod.fst h
  refine le_trans (le_of_eq (tsum_congr fun p => ?_))
    ((ENNReal.tsum_comp_le_tsum_of_injective hinj _).trans (tsum_join_le (s := s) ha hB y))
  simp only [cellZero, enorm_mul, enorm_char ψ hψ, one_mul, neg_sub, rat_zero]

end Core

theorem integral_cells_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (μr : Measure (Mx D V.rank r)) (𝓕r : Set (Mx D V.rank r)) (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)),
    IsCovolOne (ratMx D V.rank r) μr 𝓕r → IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ Φ : Mx D V.rank (r + s) → ℂ, Continuous Φ →
    ∀ B : ℝ≥0, (∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) →
      ∫ z in 𝓕r ×ˢ 𝓕s, ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
          cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂(μr.prod μs) =
        ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr := by
  intro D ψ hψ V r s μr 𝓕r μs 𝓕s hr hs b a ha Φ hΦ B hB
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, -, -⟩ := lattice_Mx D V.rank s
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank s) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  haveI := Core.countable_mat D V.rank r
  haveI := Core.countable_mat D V.rank s
  haveI : IsFiniteMeasure (μr.restrict 𝓕r) := ⟨by simp [hr.2.2]⟩
  haveI : IsFiniteMeasure (μs.restrict 𝓕s) := ⟨by simp [hs.2.2]⟩
  rw [← Measure.prod_restrict]
  have hνu : ((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
    simp [hr.2.2, hs.2.2]
  have hform : ∀ (pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E)
      (z : Mx D V.rank r × Mx D V.rank s), cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 =
        Core.cellRest ψ V b a Φ pq.1 pq.2 z.1 * ψ (trA (Matrix.trace (inner V (rat pq.2) z.2))) :=
    fun pq z => mul_comm _ _
  have hcont : ∀ pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      Continuous fun z : Mx D V.rank r × Mx D V.rank s => cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 := fun pq => by
    simp only [hform]
    exact ((Core.continuous_cellRest ψ hψ V b a hΦ pq.1 pq.2).comp continuous_fst).mul
      ((Core.continuous_lin ψ hψ V (rat pq.2)).comp continuous_snd)
  have hsum : ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      ∫⁻ z, ‖cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2‖ₑ ∂((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) ≠ ∞ := by
    rw [← lintegral_tsum fun pq => (hcont pq).enorm.measurable.aemeasurable]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono (g := fun _ => (B : ℝ≥0∞)) fun z => ?_)
    · simp [hνu]
    · simp only [Core.enorm_cellTerm ψ hψ]
      exact Core.tsum_join_le ha hB z.1
  rw [integral_tsum (fun pq => (hcont pq).aestronglyMeasurable) hsum]
  have hterm : ∀ pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      ∫ z, cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) =
        (∫ y in 𝓕r, Core.cellRest ψ V b a Φ pq.1 pq.2 y ∂μr) *
          ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat pq.2) y))) ∂μs := fun pq => by
    simp only [hform]
    exact integral_prod_mul (Core.cellRest ψ V b a Φ pq.1 pq.2)
      (fun y => ψ (trA (Matrix.trace (inner V (rat pq.2) y))))
  simp only [hterm]
  have hinj : Function.Injective fun p : Matrix (Fin V.rank) (Fin r) D.host.E =>
      ((p, 0) : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E) :=
    fun _ _ h => congrArg Prod.fst h
  rw [← hinj.tsum_eq]
  · obtain ⟨-, hu⟩ := GlobalTheory.CompanionTheory.EisUnfold.Lattice.tsum_setIntegral_sub_rat D V.rank r μr 𝓕r hr (Core.cellZero (s := s) ψ V b a Φ)
      (Core.continuous_cellZero ψ hψ V b a hΦ) B (Core.tsum_cellZero_le ψ hψ V b ha hB)
    refine Eq.trans (tsum_congr fun p => ?_) hu
    simp only [(GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality D ψ hψ V s μs 𝓕s hs 0).1 rfl, mul_one, Core.cellRest_zero]
  · rintro ⟨p, q⟩ hne
    by_cases hq : q = 0
    · exact ⟨p, by rw [hq]⟩
    · exact absurd (by simp only [(GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality D ψ hψ V s μs 𝓕s hs q).2 hq, mul_zero]) hne

end GlobalTheory.CompanionTheory.EisUnfold

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfoldingStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_coefficient_block_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (μr : Measure (Mx D V.rank r)) (𝓕r : Set (Mx D V.rank r)) (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)),
    IsCovolOne (ratMx D V.rank r) μr 𝓕r → IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ Φ : Mx D V.rank (r + s) → ℂ, Continuous Φ →
    ∀ B : ℝ≥0, (∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) →
      ∫ z in 𝓕r ×ˢ 𝓕s, ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
          cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂(μr.prod μs) =
        ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq | exact GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq <;> assumption)
end
end
