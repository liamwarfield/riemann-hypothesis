module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfolding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBounded
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBounded
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

private theorem exists_isCompact_sub_incA_mem (D : D7) :
    ∃ C : Set (AE D), IsCompact C ∧ ∀ z : AE D, ∃ x : D.host.E, z - incA D x ∈ C := by
  classical
  obtain ⟨K0, hK0, hK0'⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F
  let b := Module.finBasis D.host.F D.host.E
  let bA := Algebra.TensorProduct.basis (AF D.host.F) b
  let e : AE D ≃ₗ[AF D.host.F] (Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := bA.equivFun
  have he : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap
      (e.symm : (Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) →ₗ[AF D.host.F] AE D)
  have h1 : ∀ x : Fin (Module.finrank D.host.F D.host.E) → D.host.F,
      e.symm (fun i => algebraMap D.host.F (AF D.host.F) (x i)) = incA D (∑ i, x i • b i) := by
    intro x
    rw [show incA D (∑ i, x i • b i) = (1 : AF D.host.F) ⊗ₜ[D.host.F] (∑ i, x i • b i) from rfl,
      TensorProduct.tmul_sum]
    simp only [e, Module.Basis.equivFun_symm_apply, bA, Algebra.TensorProduct.basis_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algebraMap_smul, TensorProduct.tmul_smul]
  refine ⟨e.symm '' Set.univ.pi (fun _ => K0), (isCompact_univ_pi fun _ => hK0).image he, ?_⟩
  intro z
  choose x hx using fun i => hK0' (e z i)
  refine ⟨∑ i, x i • b i, fun i => e z i - algebraMap D.host.F (AF D.host.F) (x i), fun i _ => hx i, ?_⟩
  have hv : (fun i => e z i - algebraMap D.host.F (AF D.host.F) (x i)) =
      e z - fun i => algebraMap D.host.F (AF D.host.F) (x i) := rfl
  rw [hv, map_sub, LinearEquiv.symm_apply_apply, h1]

theorem schwartzA_continuous_and_tsum_enorm_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n →
    Continuous φ ∧ ∃ B : ℝ≥0, ∀ w : Mx D m n, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖φ (rat ξ + w)‖ₑ ≤ B := by
  intro D θ hθ m n φ hφ
  have hSB := GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ hφ
  obtain ⟨hcont, K, hK, hKb⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ hSB
  refine ⟨hcont, ?_⟩
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨C, hC, hCz⟩ := exists_isCompact_sub_incA_mem D
  choose xf hxf using hCz
  let Q : Set (Mx D m n) := {w | ∀ i j, w i j ∈ C}
  have hQ : IsCompact Q := by
    have h := isCompact_univ_pi (fun (_ : Fin m) => isCompact_univ_pi (fun (_ : Fin n) => hC))
    have hQeq : Q = (Set.univ.pi fun (_ : Fin m) => Set.univ.pi fun (_ : Fin n) => C) := by
      ext w
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [hQeq]
    exact h
  obtain ⟨b, hbs, hb⟩ := hN K Q hK hQ
  obtain ⟨c, hc⟩ := hKb N
  set c' : ℝ := max c 0 with hc'
  refine ⟨Real.toNNReal (c' * ∑' ξ, b ξ), fun w => ?_⟩
  let ξ0 : Matrix (Fin m) (Fin n) D.host.E := Matrix.of fun i j => xf (w i j)
  let x0 : Mx D m n := w - rat ξ0
  have hx0 : x0 ∈ Q := fun i j => hxf (w i j)
  have hb0 : ∀ ξ, 0 ≤ b ξ := fun ξ => (GlobalTheory.Unf.maj_nonneg θ K N _).trans (hb x0 hx0 ξ)
  have hrat : ∀ ξ, rat ξ + w = x0 + rat (ξ + ξ0) := by
    intro ξ
    ext i j
    simp only [x0, rat, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, map_add (f := _)]
    abel
  have hpt : ∀ ξ, ‖φ (rat ξ + w)‖ₑ ≤ ENNReal.ofReal (c' * b (ξ + ξ0)) := by
    intro ξ
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [hrat ξ]
    calc ‖φ (x0 + rat (ξ + ξ0))‖ ≤ c * GlobalTheory.Unf.maj θ K N (x0 + rat (ξ + ξ0)) := hc _
      _ ≤ c' * GlobalTheory.Unf.maj θ K N (x0 + rat (ξ + ξ0)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (GlobalTheory.Unf.maj_nonneg _ _ _ _)
      _ ≤ c' * b (ξ + ξ0) := mul_le_mul_of_nonneg_left (hb x0 hx0 _) (le_max_right _ _)
  calc ∑' ξ, ‖φ (rat ξ + w)‖ₑ ≤ ∑' ξ, ENNReal.ofReal (c' * b (ξ + ξ0)) := ENNReal.tsum_le_tsum hpt
    _ = ∑' η, ENNReal.ofReal (c' * b η) :=
      (Equiv.addRight ξ0).tsum_eq (fun η => ENNReal.ofReal (c' * b η))
    _ = ENNReal.ofReal (∑' η, c' * b η) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun η => mul_nonneg (le_max_right _ _) (hb0 η)) (hbs.mul_left c')).symm
    _ = ((Real.toNNReal (c' * ∑' ξ, b ξ) : ℝ≥0) : ℝ≥0∞) := by
      rw [tsum_mul_left]
      rfl

end GlobalTheory.CompanionTheory.EisUnfold
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBoundedStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_lattice_sum_bounded : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n →
    Continuous φ ∧ ∃ B : ℝ≥0, ∀ w : Mx D m n, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖φ (rat ξ + w)‖ₑ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le | exact GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneColumnJoinProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneColumnJoinProduct
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.ProdCovol

open scoped Pointwise

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := _root_.GlobalTheory.TwistHaar.isAddFundamentalDomain_prod (A := A) (B := B) (Γ := Γ) (Δ := Δ) (μ := μ) (ν := ν) (s := s) (t := t) hs ht

variable {D : D7} {m r s : ℕ}

def joinAdd (D : D7) (m r s : ℕ) : Mx D m r × Mx D m s ≃+ Mx D m (r + s) :=
  { joinEquiv with map_add' := fun a b => colJoin_add a.1 b.1 a.2 b.2 }

theorem joinAdd_apply (z : Mx D m r × Mx D m s) : joinAdd D m r s z = colJoin z.1 z.2 := rfl

theorem continuous_joinAdd : Continuous (joinAdd D m r s) := by
  refine continuous_matrix fun i k => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · have : (fun z : Mx D m r × Mx D m s => joinAdd D m r s z i (Fin.castAdd s j)) = fun z => z.1 i j :=
      funext fun z => colJoin_castAdd z.1 z.2 i j
    rw [this]
    exact (continuous_apply_apply i j).comp continuous_fst
  · have : (fun z : Mx D m r × Mx D m s => joinAdd D m r s z i (Fin.natAdd r j)) = fun z => z.2 i j :=
      funext fun z => colJoin_natAdd z.1 z.2 i j
    rw [this]
    exact (continuous_apply_apply i j).comp continuous_snd

theorem continuous_joinAdd_symm : Continuous (joinAdd D m r s).symm := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_matrix fun i j => continuous_apply_apply i (Fin.castAdd s j)
  · exact continuous_matrix fun i j => continuous_apply_apply i (Fin.natAdd r j)

theorem joinAdd_mem_iff (z : Mx D m r × Mx D m s) :
    joinAdd D m r s z ∈ ratMx D m (r + s) ↔ z ∈ (ratMx D m r).prod (ratMx D m s) := by
  rw [AddSubgroup.mem_prod]
  constructor
  · rintro h
    obtain ⟨γ, hγ⟩ := mem_ratMx.1 h
    refine ⟨mem_ratMx.2 ⟨colL γ, ?_⟩, mem_ratMx.2 ⟨colR γ, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun hγ i) (Fin.castAdd s j)
      rw [joinAdd_apply, colJoin_castAdd] at this
      exact this
    · ext i j
      have := congrFun (congrFun hγ i) (Fin.natAdd r j)
      rw [joinAdd_apply, colJoin_natAdd] at this
      exact this
  · rintro ⟨h1, h2⟩
    obtain ⟨p, hp⟩ := mem_ratMx.1 h1
    obtain ⟨q, hq⟩ := mem_ratMx.1 h2
    exact mem_ratMx.2 ⟨colJoin p q, by rw [rat_colJoin, hp, hq, joinAdd_apply]⟩

theorem isCovolOne_colJoin : ∀ (D : D7) (m r s : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r))
    (μs : Measure (Mx D m s)) (𝓕s : Set (Mx D m s)), IsCovolOne (ratMx D m r) μr 𝓕r → IsCovolOne (ratMx D m s) μs 𝓕s →
    IsCovolOne (ratMx D m (r + s)) ((μr.prod μs).map fun z => colJoin z.1 z.2)
      ((fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) '' (𝓕r ×ˢ 𝓕s)) := by
  intro D m r s μr 𝓕r μs 𝓕s hr hs
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := lattice_Mx D m r
  obtain ⟨b1, b2, b3, b4, b5, -⟩ := lattice_Mx D m s
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := lattice_Mx D m (r + s)
  haveI : BorelSpace (Mx D m r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m s) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m (r + s)) := ⟨rfl⟩
  obtain ⟨hHr, hFr, h1r⟩ := hr
  obtain ⟨hHs, hFs, h1s⟩ := hs
  haveI := hHr
  haveI := hHs
  let e := joinAdd D m r s
  have he : Continuous e := continuous_joinAdd
  have he' : Continuous e.symm := continuous_joinAdd_symm
  let f : (Mx D m r × Mx D m s) ≃ₜ Mx D m (r + s) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hemb : MeasurableEmbedding e := f.measurableEmbedding
  have hfun : (fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) = e := rfl
  rw [hfun]
  refine ⟨e.isAddHaarMeasure_map _ he he', ?_, ?_⟩
  · let g : ratMx D m (r + s) ≃ (ratMx D m r).prod (ratMx D m s) :=
      { toFun := fun γ => ⟨e.symm γ, (joinAdd_mem_iff _).1 (by
          change e (e.symm γ) ∈ _
          rw [e.apply_symm_apply]; exact γ.2)⟩
        invFun := fun γ => ⟨e γ, (joinAdd_mem_iff _).2 γ.2⟩
        left_inv := fun γ => Subtype.ext (e.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (e.symm_apply_apply _) }
    refine (isAddFundamentalDomain_prod hFr hFs).image_of_equiv e.toEquiv ?_ g fun γ x => ?_
    · refine ⟨he'.measurable.aemeasurable, ?_⟩
      have : ((μr.prod μs).map e).map e.symm = μr.prod μs := by
        rw [Measure.map_map he'.measurable he.measurable]
        have : (e.symm ∘ e : Mx D m r × Mx D m s → Mx D m r × Mx D m s) = id := funext e.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change e (e.symm γ + x) = γ + e x
      rw [map_add (f := _), e.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ e.injective, Measure.prod_prod, h1r, h1s, one_mul]

end GlobalTheory.CompanionTheory.EisUnfold.ProdCovol

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneColumnJoinProductStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_one_column_join_product : ∀ (D : D7) (m r s : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r)) (μs : Measure (Mx D m s))
    (𝓕s : Set (Mx D m s)), IsCovolOne (ratMx D m r) μr 𝓕r → IsCovolOne (ratMx D m s) μs 𝓕s →
    IsCovolOne (ratMx D m (r + s)) ((μr.prod μs).map fun z => colJoin z.1 z.2)
      ((fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) '' (𝓕r ×ˢ 𝓕s)) := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.ProdCovol.isCovolOne_colJoin | exact GlobalTheory.CompanionTheory.EisUnfold.ProdCovol.isCovolOne_colJoin | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.ProdCovol.isCovolOne_colJoin <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilActionBlockMatrixComponents
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilActionBlockMatrixComponents
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Parts

section Field

variable {K : Type} [Field K]

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem extB_castAdd {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i j : Fin r) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) (Fin.castAdd s i) (Fin.castAdd s j) = b i j := by
  simp [extB]

theorem extB_natAdd_left {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i : Fin s) (j : Fin (r + s)) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) (Fin.natAdd r i) j = 0 := by
  simp [extB]

theorem extB_natAdd_right {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i : Fin (r + s)) (j : Fin s) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) i (Fin.natAdd r j) = 0 := by
  simp [extB]

theorem eId_mul_extB {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) :
    eId K (r + s) r * extB b = extB b := by
  ext i j
  rw [eId, Matrix.diagonal_mul]
  by_cases h : (i : ℕ) < r
  · simp [h]
  · simp [h, extB]

theorem representation_matrix_block_form (σ : K →+* K) {r s : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) K) :
    repMat σ b a = blk4 ((1 - eId K (r + s) r) * a)
        (((1 - eId K (r + s) r) * extB b + eId K (r + s) r) * (cT σ a)⁻¹)
        (-(eId K (r + s) r * a))
        ((1 - eId K (r + s) r - extB b) * (cT σ a)⁻¹) := by
  simp only [repMat, wr, nB, mA]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have h : -eId K (r + s) r * extB b + (1 - eId K (r + s) r) * 1 =
      1 - eId K (r + s) r - extB b := by
    rw [Matrix.neg_mul, eId_mul_extB, Matrix.mul_one]
    abel
  rw [h]
  simp

end Field

variable {D : D7}

theorem block_matrix_map {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map (incA D) = blk4 (a.map (incA D)) (b.map (incA D)) (c.map (incA D)) (d.map (incA D)) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem xPart_zy_mul {m n : ℕ} (y : Mx D m n) (A B C E' : Mx D n n) :
    xPart (HMul.hMul (zy y) (blk4 A B C E') : Mx D m (n + n)) = HMul.hMul y C := by
  ext i j
  simp only [xPart, zy, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [Fintype.sum_equiv finSumFinEquiv.symm _
    (fun t => Sum.elim (fun _ => (0 : AE D)) (y i) t * Matrix.fromBlocks A B C E' t (Sum.inl j))
    (fun _ => rfl), Fintype.sum_sum_type]
  simp

theorem yPart_zy_mul {m n : ℕ} (y : Mx D m n) (A B C E' : Mx D n n) :
    yPart (HMul.hMul (zy y) (blk4 A B C E') : Mx D m (n + n)) = HMul.hMul y E' := by
  ext i j
  simp only [yPart, zy, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [Fintype.sum_equiv finSumFinEquiv.symm _
    (fun t => Sum.elim (fun _ => (0 : AE D)) (y i) t * Matrix.fromBlocks A B C E' t (Sum.inr j))
    (fun _ => rfl), Fintype.sum_sum_type]
  simp

theorem colJoin_mul_eId {m r s : ℕ} (y₁ : Mx D m r) (y₂ : Mx D m s) :
    (HMul.hMul (colJoin y₁ y₂) ((eId D.host.E (r + s) r).map (incA D)) : Mx D m (r + s)) =
      colJoin y₁ (0 : Mx D m s) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [eId, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply]
  · simp [eId, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply]

theorem colJoin_mul_extB {m r s : ℕ} (y₁ : Mx D m r) (y₂ : Mx D m s) (b : Matrix (Fin r) (Fin r) D.host.E) :
    (HMul.hMul (colJoin y₁ y₂) ((extB b : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E).map (incA D)) : Mx D m (r + s)) =
      colJoin (HMul.hMul y₁ (rat b) : Mx D m r) (0 : Mx D m s) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [Matrix.mul_apply, Fin.sum_univ_add, extB_castAdd, extB_natAdd_left, rat]
  · simp [Matrix.mul_apply, Fin.sum_univ_add, extB_natAdd_right]

theorem parts : ∀ (D : D7) (m r s : ℕ) (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (y₁ : Mx D m r) (y₂ : Mx D m s),
    xPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        -HMul.hMul (colJoin y₁ (0 : Mx D m s)) (rat a) ∧
      yPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) := by
  intro D m r s b a y₁ y₂
  set e := eId D.host.E (r + s) r with he
  set y : Mx D m (r + s) := colJoin y₁ y₂ with hy
  have hmap : ∀ X : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E,
      X.map (incA D) = (incA D).mapMatrix X := fun _ => rfl
  rw [representation_matrix_block_form, block_matrix_map, xPart_zy_mul, yPart_zy_mul]
  constructor
  · have h1 : (-(e * a)).map (incA D) = -(e.map (incA D) * rat a) := by
      simp only [hmap, map_neg, map_mul]; rfl
    rw [h1, Matrix.mul_neg, ← Matrix.mul_assoc, colJoin_mul_eId]
  · have h2 : ((1 - e - extB b) * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹).map (incA D) =
        (1 - e.map (incA D) - (extB b : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E).map (incA D)) *
          rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹ := by
      simp only [hmap, map_sub, map_mul, map_one]; rfl
    rw [h2, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, hy, colJoin_mul_eId,
      colJoin_mul_extB, ← colJoin_sub, ← colJoin_sub]
    congr 2
    · simp
    · simp

end GlobalTheory.CompanionTheory.EisUnfold.Parts
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilActionBlockMatrixComponentsStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_action_block_matrix_components : ∀ (D : D7) (m r s : ℕ) (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (y₁ : Mx D m r) (y₂ : Mx D m s),
    xPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        -HMul.hMul (colJoin y₁ (0 : Mx D m s)) (rat a) ∧
      yPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Parts.parts | exact GlobalTheory.CompanionTheory.EisUnfold.Parts.parts | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Parts.parts <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHermitianIntegralUnfolding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHermitianIntegralUnfolding
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.NegStep

theorem integral_neg_of_secondCountable {G E : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → E) :
    ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  have : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  exact integral_neg_eq_self f μ

theorem colJoin_zero_mul {R : Type*} [NonUnitalNonAssocSemiring R] {m r s : ℕ} (p : Matrix (Fin m) (Fin r) R)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) R) (c : Matrix (Fin r) (Fin (r + s)) R)
    (h : ∀ j : Fin r, a (Fin.castAdd s j) = c j) :
    colJoin p (0 : Matrix (Fin m) (Fin s) R) * a = p * c := by
  ext i k
  simp [Matrix.mul_apply, Fin.sum_univ_add, h]

theorem inner_neg_neg {D : D7} (V : HSp D) {n : ℕ} (t : Mx D V.rank n) : inner V (-t) (-t) = inner V t t := by
  unfold GlobalTheory.StdUnn.inner
  rw [adj_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem integral_colJoin_neg_eq_J : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (r s : ℕ) (μr : Measure (Mx D V.rank r))
    (𝓕r : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μr 𝓕r →
    ∀ (c : Matrix (Fin r) (Fin (r + s)) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsCompl c a →
    ∀ (b : HermE D r) (Φ : Mx D V.rank (r + s) → ℂ),
      ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr = J ψ V μr (pull c Φ) b := by
  intro D ψ V r s μr 𝓕r hcov c a hca b Φ
  obtain ⟨h1, h2, h3, h4, -⟩ := lattice_Mx D V.rank r
  have hB : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  have hH : μr.IsAddHaarMeasure := hcov.1
  have hrow : ∀ j : Fin r, rat a (Fin.castAdd s j) = rat c j := by
    intro j
    have := hca.2 (Fin.castAdd s j) j.isLt
    funext k
    show incA D (a (Fin.castAdd s j) k) = incA D (c j k)
    rw [this]
    rfl
  have key : ∀ t : Mx D V.rank r,
      ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) =
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))) (-t) := by
    intro t
    have e : (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a) : Mx D V.rank (r + s)) = HMul.hMul (-t) (rat c) :=
      colJoin_zero_mul (-t) (rat a) (rat c) hrow
    show _ = Φ (HMul.hMul (-t) (rat c)) * _
    rw [e, inner_neg_neg, mul_comm]
  exact (integral_congr_ae (Filter.Eventually.of_forall key)).trans
    (integral_neg_of_secondCountable (E := ℂ) μr
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))))

end GlobalTheory.CompanionTheory.EisUnfold.NegStep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHermitianIntegralUnfoldingStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_hermitian_integral_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (r s : ℕ) (μr : Measure (Mx D V.rank r))
    (𝓕r : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μr 𝓕r →
    ∀ (c : Matrix (Fin r) (Fin (r + s)) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsCompl c a →
    ∀ (b : HermE D r) (Φ : Mx D V.rank (r + s) → ℂ),
      ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr = J ψ V μr (pull c Φ) b := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J | exact GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumPartialFourierUnfolding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumPartialFourierUnfolding
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Period

variable {D : D7}

theorem rat_sub' {m n : ℕ} (p p₀ : Matrix (Fin m) (Fin n) D.host.E) :
    (rat (p - p₀) : Mx D m n) = rat p - rat p₀ := by
  ext i j
  simp [rat]

theorem psi_inner_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (q q₀ : Matrix (Fin V.rank) (Fin s) D.host.E) :
    ψ (trA (Matrix.trace (inner V (rat q) (rat q₀)))) = 1 := by
  have h : (inner V (rat q) (rat q₀) : Mx D s s) = rat (qᴴ * (V.gram * q₀)) := by
    change (adj (rat q) ⬝ (gA V ⬝ rat q₀) : Mx D s s) = rat (qᴴ * (V.gram * q₀))
    rw [rat_mul, rat_mul, rat_conjTranspose, gA]
  have ht : ∀ M : Matrix (Fin s) (Fin s) D.host.E,
      Matrix.trace (rat M : Mx D s s) = incA D (Matrix.trace M) := fun M => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rat, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [h, ht, GlobalTheory.CompanionTheory.ThetaInv.trA_incA]
  exact hψ.2.2.1 _

theorem inner_add_right' (V : HSp D) {s : ℕ} (x y z : Mx D V.rank s) :
    (inner V x (y + z) : Mx D s s) = inner V x y + inner V x z := by
  change (adj x ⬝ (gA V ⬝ (y + z)) : Mx D s s) = adj x ⬝ (gA V ⬝ y) + adj x ⬝ (gA V ⬝ z)
  simp [Matrix.mul_add]

theorem trA_add' (x y : AE D) : trA (x + y) = trA x + trA y := by
  simp [trA]

theorem term_shift {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (Φ : Mx D V.rank (r + s) → ℂ)
    (p p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) :
    cellTerm ψ V b a Φ p q (y₁ + rat p₀) (y₂ + rat q₀) = cellTerm ψ V b a Φ (p - p₀) q y₁ y₂ := by
  have e₁ : y₁ + rat p₀ - rat p = y₁ - rat (p - p₀) := by rw [rat_sub']; abel
  have e₂ : rat p - (y₁ + rat p₀) = rat (p - p₀) - y₁ := by rw [rat_sub']; abel
  have e₃ : ψ (trA (Matrix.trace (inner V (rat q) (y₂ + rat q₀)))) =
      ψ (trA (Matrix.trace (inner V (rat q) y₂))) := by
    rw [inner_add_right', Matrix.trace_add, trA_add', AddChar.map_add_eq_mul, psi_inner_rat hψ, mul_one]
  unfold cellTerm
  rw [e₁, e₂, e₃]

theorem tsum_cellTerm_add_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s),
    ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 (y₁ + rat p₀) (y₂ + rat q₀) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂ := by
  intro D ψ hψ V r s b a Φ p₀ q₀ y₁ y₂
  simp only [term_shift hψ]
  exact (Equiv.prodCongr (Equiv.subRight p₀) (Equiv.refl _)).tsum_eq
    (fun pq => cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂)

end GlobalTheory.CompanionTheory.EisUnfold.Period

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumPartialFourierUnfoldingStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sum_shift_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s),
    ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 (y₁ + rat p₀) (y₂ + rat q₀) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂ := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Period.tsum_cellTerm_add_rat | exact GlobalTheory.CompanionTheory.EisUnfold.Period.tsum_cellTerm_add_rat | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Period.tsum_cellTerm_add_rat <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinUnfoldingSecondTerm
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

theorem unfold2 : Unfold2 := by
  intro D ψ hψ θ hθ V n r hrn μ 𝓕 hμ μr h𝓕r c a hca b Φ hΦ
  obtain ⟨𝓕r, hμr⟩ := h𝓕r
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn
  obtain ⟨μs, 𝓕s, hμs⟩ := exists_isCovolOne D V.rank s
  obtain ⟨hΦc, B, hB⟩ := GlobalTheory.T.schwartz_lattice_sum_bounded D θ hθ V.rank (r + s) Φ hΦ
  have ha : IsUnit a.det := hca.1

  let e : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E ≃
      Matrix (Fin V.rank) (Fin (r + s)) D.host.E :=
    joinEquiv.trans
      { toFun := fun ξ => ξ * a
        invFun := fun ξ => ξ * a⁻¹
        left_inv := fun ξ => Matrix.mul_nonsing_inv_cancel_right a ξ ha
        right_inv := fun ξ => Matrix.nonsing_inv_mul_cancel_right a ξ ha }
  set T : Mx D V.rank (r + s) → ℂ := fun y => ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E,
    Heisenberg₂ ψ V (HMul.hMul (zy y) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D))) Φ
      (ξ.map (incA D)) with hT
  have hform : ∀ y₁ y₂, T (colJoin y₁ y₂) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b.1 a Φ pq.1 pq.2 y₁ y₂ := by
    intro y₁ y₂
    obtain ⟨hx, hy⟩ := GlobalTheory.T.weil_action_block_matrix_components D V.rank r s b.1 a y₁ y₂
    rw [hT]
    dsimp only
    rw [← e.tsum_eq]
    exact tsum_congr fun pq => GlobalTheory.T.block_weil_action_theta_unfolding D ψ hψ V r s b.1 b.2 a ha Φ y₁ y₂ _ hx hy pq.1 pq.2
  have hper : ∀ γ ∈ ratMx D V.rank (r + s), ∀ y, T (γ + y) = T y := by
    intro γ hγ y
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    rw [← colJoin_colL_colR g, ← colJoin_colL_colR y, rat_colJoin, ← colJoin_add, hform, hform,
      add_comm (rat (colL g)), add_comm (rat (colR g))]
    exact GlobalTheory.T.lattice_sum_shift_invariant D ψ hψ V r s b.1 a Φ (colL g) (colR g) (colL y) (colR y)
  have hE := GlobalTheory.T.covolume_one_column_join_product D V.rank r s μr 𝓕r μs 𝓕s hμr hμs
  show ∫ y in 𝓕, T y ∂μ = _
  rw [covolOne_integral_eq hE hμ T hper]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D V.rank s
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D V.rank (r + s)
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank s) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank (r + s)) := ⟨rfl⟩
  have hc : Continuous fun z : Mx D V.rank r × Mx D V.rank s => colJoin z.1 z.2 := by
    refine continuous_matrix fun i k => ?_
    simp only [colJoin, Matrix.of_apply]
    rcases finSumFinEquiv.symm k with j | j
    · exact (continuous_apply_apply i j).comp continuous_fst
    · exact (continuous_apply_apply i j).comp continuous_snd
  have hc' : Continuous fun y : Mx D V.rank (r + s) => ((colL y, colR y) : Mx D V.rank r × Mx D V.rank s) := by
    refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_)
    · exact continuous_apply_apply i (Fin.castAdd s j)
    · exact continuous_apply_apply i (Fin.natAdd r j)
  let hj : (Mx D V.rank r × Mx D V.rank s) ≃ₜ Mx D V.rank (r + s) :=
    { (joinEquiv : (Mx D V.rank r × Mx D V.rank s) ≃ Mx D V.rank (r + s)) with
      continuous_toFun := hc
      continuous_invFun := hc' }
  have hmp : MeasurePreserving hj.toMeasurableEquiv (μr.prod μs)
      ((μr.prod μs).map fun z => colJoin z.1 z.2) := ⟨hj.toMeasurableEquiv.measurable, rfl⟩
  have h1 := hmp.setIntegral_image_emb hj.toMeasurableEquiv.measurableEmbedding T (𝓕r ×ˢ 𝓕s)
  erw [h1]
  have h2 : ∀ z : Mx D V.rank r × Mx D V.rank s, T (hj.toMeasurableEquiv z) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b.1 a Φ pq.1 pq.2 z.1 z.2 := fun z => hform z.1 z.2
  simp only [h2]
  rw [GlobalTheory.T.eisenstein_coefficient_block_unfolding D ψ hψ V r s μr 𝓕r μs 𝓕s hμr hμs b.1 a ha Φ hΦc B hB]
  exact GlobalTheory.T.eisenstein_hermitian_integral_unfolding D ψ V r s μr 𝓕r hμr c a hca b Φ

end GlobalTheory.CompanionTheory.EisUnfold

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinUnfoldingSecondTermStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_unfolding_second_term : PositivityTheory.GramSchwartzFunctions.EC.Unfold2 := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.unfold2 | exact GlobalTheory.CompanionTheory.EisUnfold.unfold2 | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.unfold2 <;> assumption)
end
