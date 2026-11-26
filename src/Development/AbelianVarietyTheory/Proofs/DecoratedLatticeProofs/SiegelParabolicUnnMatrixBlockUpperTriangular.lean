module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjStabilizersSelfDualLatticesUnramifiedStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.LeftInvSect
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem rat_mat {γ : G D n} (h : γ ∈ GF D n) :
    ∃ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) := by
  obtain ⟨x, -, hx⟩ := h
  exact ⟨x.1, (congrArg Units.val hx).symm⟩

theorem det_rat {γ : G D n} (h : γ ∈ GF D n) (a : GL (Fin n) (AE D)) (ha : blkA (mat γ) = a.1) :
    ∃ u : D.host.Eˣ, Matrix.GeneralLinearGroup.det a = Units.map (incA D).toMonoidHom u := by
  haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
  haveI : Nontrivial (AE D) := inferInstance
  obtain ⟨x, hx⟩ := rat_mat h
  have e : ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = incA D (blkA x).det := by
    rw [RingHom.map_det]
    change a.1.det = _
    rw [← ha, hx]; rfl
  have h0 : (blkA x).det ≠ 0 := fun h0 => Units.ne_zero _ (e.trans (by rw [h0, map_zero]))
  exact ⟨Units.mk0 _ h0, Units.ext e⟩

theorem siegelParabolicUnn_matrix_blockUpperTriangular {p : G D n} (hp : p ∈ P D n) : ∃ b d, mat p = blk4 (blkA (mat p)) b 0 d := by
  refine ⟨((mat p).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    ((mat p).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · exact lower_eq_zero hp i j
  · rfl

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : G D n) = 1 := rfl

theorem levi_mul_inv (a : GL (Fin n) (AE D)) :
    (blk4 a.1 0 0 (adj (a⁻¹).1) : Mx D (n + n) (n + n)) * blk4 (a⁻¹).1 0 0 (adj a.1) = 1 := by
  have h2 : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by rw [← adj_mul]; simp [adj_one]
  simp [submatrix_fromBlocks_mul, h2, block_matrix_one, -Matrix.coe_units_inv]

theorem exists_levi_unip {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D)) (ha' : blkA (mat p) = a.1) :
    ∃ (m u : G D n) (b : Mx D n n), p = m * u ∧ mat m = blk4 a.1 0 0 (adj (a⁻¹).1) ∧ mat u = blk4 1 b 0 1 := by
  obtain ⟨m, hm⟩ := exists_levi a
  obtain ⟨m', hm'⟩ := exists_levi a⁻¹
  obtain ⟨b, d, hb⟩ := siegelParabolicUnn_matrix_blockUpperTriangular hp
  rw [ha'] at hb
  rw [inv_inv] at hm'
  have hu : mat (m' * p) = blk4 1 ((a⁻¹).1 * b) 0 (adj a.1 * d) := by
    rw [mat_mul, hm', hb, submatrix_fromBlocks_mul]
    simp [-Matrix.coe_units_inv]
  have hd : (adj a.1 : Mx D n n) * d = 1 := by
    have h : adj (mat (m' * p)) * JR (AF D.host.F) (Jst D n) * mat (m' * p) = JR (AF D.host.F) (Jst D n) := (m' * p).2
    rw [JR_Jst, hu] at h
    generalize (adj a.1 : Mx D n n) * d = d' at h ⊢
    generalize (a⁻¹).1 * b = b' at h
    simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_one, adj_zero, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, mul_neg,
      neg_mul, neg_zero] at h
    exact (blockMatrixTwoByTwoFin_injective h).2.1
  have hmm : m * m' = 1 := mat_inj (by rw [mat_mul, mat_one, hm, hm', levi_mul_inv])
  refine ⟨m, m' * p, (a⁻¹).1 * b, by rw [← mul_assoc, hmm, one_mul], hm, by rw [hu, hd]⟩

theorem exists_blkA {p : G D n} (hp : p ∈ P D n) : ∃ a : GL (Fin n) (AE D), blkA (mat p) = a.1 :=
  ⟨levi (D := D) (n := n) ⟨p, hp⟩, rfl⟩

theorem height_inv (hI : ∀ g : G D n, ∃ p ∈ P D n, ∃ k ∈ K D n, g = p * k) {H : G D n → ℝ≥0} (hH : IsHeight H)
    {γ : G D n} (hp : γ ∈ P D n) (a : GL (Fin n) (AE D)) (ha : blkA (mat γ) = a.1)
    (h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1) (g : G D n) : H (γ * g) = H g := by
  obtain ⟨p, hp', k, hk, rfl⟩ := hI g
  obtain ⟨c, hc⟩ := exists_blkA hp'
  have e : blkA (mat (γ * p)) = (a * c).1 := by rw [blkA_mul hp', ha, hc, Units.val_mul]
  rw [← mul_assoc, hH _ ((P D n).mul_mem hp hp') (a * c) e k hk, hH p hp' c hc k hk, map_mul, map_mul, h1, one_mul]

theorem leftInv_sect : ∀ (D : D7) (n : ℕ), (∀ g : GlobalTheory.StdUnn.G D n, ∃ p ∈ GlobalTheory.StdUnn.P D n, ∃ k ∈ GlobalTheory.StdUnn.K D n, g = p * k) → ∀ (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n)), IsHeckeChar D χ → GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ H : GlobalTheory.StdUnn.G D n → ℝ≥0, GlobalTheory.StdUnn.IsHeight H → ∀ (Φ : GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n) (z : ℂ), GlobalTheory.AutomorphicL2Unitary.LeftInv (GlobalTheory.StdUnn.P D n ⊓ GlobalTheory.StdUnn.GF D n) (GlobalTheory.StdUnn.sect ω H Φ z) := by
  intro D n hI V ψ χ θ μ ω hχ hω H hH Φ z γ hγ g
  obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a, ha⟩ := exists_blkA hp
  obtain ⟨u, hu⟩ := det_rat hr a ha
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact absE_inclR u
  have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact hχ.2 u
  have hHe : H (γ * g) = H g := height_inv hI hH hp a ha h1 g
  have hW : (ω (γ * g) Φ).1 0 = (ω g Φ).1 0 := by
    obtain ⟨m, v, b, e, hm, hv⟩ := exists_levi_unip hp a ha
    have e' : ω (γ * g) Φ = ω m (ω v (ω g Φ)) := by
      rw [e, map_mul, map_mul]; rfl
    have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
    have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
    rw [e', hω.levi m _ hm, h1, h2, z1, hω.unip v b hv, z2]
    simp [halfTr, npow]
  simp only [sect, hHe, hW]

end GlobalTheory.StdUnn.LeftInvSect
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Iwasawa

theorem exists_mul_of_rank (D : D7) (A : HSp D) (g : GlobalTheory.StdUnn.G D A.rank) :
    ∃ p ∈ GlobalTheory.StdUnn.P D A.rank, ∃ k ∈ GlobalTheory.StdUnn.K D A.rank, g = p * k := by
  obtain ⟨μ, hμ, hconj⟩ := GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ hμ
  obtain ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj A
  obtain ⟨p, hp⟩ := hconj A a ha κ hκ
  obtain ⟨q, k, hk, hqk⟩ := (GlobalTheory.Eis.isIwasawa_Khat (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha)).1
    (κ.symm g * (p : GA D (dblSp A))⁻¹)
  refine ⟨κ ((q : GA D (dblSp A)) * p), ?_, κ ((p : GA D (dblSp A))⁻¹ * k * p), (hp k).1 hk, ?_⟩
  · exact (GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ hμ κ hκ _).1 (Subgroup.mul_mem _ q.2 p.2)
  · have h1 : κ.symm g = (q : GA D (dblSp A)) * k * p := by
      rw [← hqk, inv_mul_cancel_right]
    have h2 : (q : GA D (dblSp A)) * p * ((p : GA D (dblSp A))⁻¹ * k * p) = (q : GA D (dblSp A)) * k * p := by
      group
    rw [← map_mul, h2, ← h1, MulEquiv.apply_symm_apply]

theorem exists_mul : ∀ (D : D7) (n : ℕ) (g : GlobalTheory.StdUnn.G D n),
    ∃ p ∈ GlobalTheory.StdUnn.P D n, ∃ k ∈ GlobalTheory.StdUnn.K D n, g = p * k :=
  fun D n g => exists_mul_of_rank D (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n) g

end GlobalTheory.StdUnn.Iwasawa
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
noncomputable section

namespace GlobalTheory.AnnihBox

variable {D : D7}

theorem cA_smul (r : AF D.host.F) (z : AE D) : cA D (r • z) = r • cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, sigR, TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]

def cALin (D : D7) : AE D →ₗ[AF D.host.F] AE D where
  toFun := cA D
  map_add' := map_add _
  map_smul' := cA_smul

theorem continuous_cA' : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap (cALin D)

theorem infPart_cA_eq (a : AE D) : infPart D (cA D a) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D a) := by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [cA, sigR, infPart]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

theorem infPart_cA' (a : AE D) (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  rw [infPart_cA_eq, h, map_zero]

theorem symplO_extX_extY_single (S S₀ T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Mx D T.rank ρ)
    (i : Fin T.rank) (j : Fin ρ) (c : AE D) :
    symplO S T (d.extX T x) (d.extY T (Matrix.single i j (cA D c))) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (gA T ⬝ x) i j * c) := by
  have h := d.hO_ext T x 0 0 (Matrix.single i j (cA D c)) 0 0
  simp only [map_zero, add_zero, zero_add] at h
  have h0 : hO S₀ T (0 : WO S₀ T) 0 = 0 := by simp [hO]
  have hp : pairS T (0 : Mx D T.rank ρ) 0 = 0 := by simp [pairS, adj]
  rw [h0, hp, add_zero, add_zero] at h
  have ha : adj (Matrix.single i j (cA D c)) = Matrix.single j i c := by
    ext a b
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
    by_cases h1 : i = b <;> by_cases h2 : j = a <;> simp [h1, h2, GlobalTheory.DualPairCheck.cA_cA]
  unfold symplO
  rw [h, pairS, ha, Matrix.trace_single_mul, smul_eq_mul]
  ring_nf

set_option synthInstance.maxHeartbeats 400000 in
theorem map_finPart_mul_map {n m : ℕ} (M : Mx D n n) (c : AE D) (z : Mx D n m)
    (hz : ∀ i j, finPart D (z i j) = 0) : (M ⬝ z.map (fun w => c * w)).map (finPart D) = 0 := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.map_apply, Matrix.mul_apply, map_sum (finPart D), Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.map_apply, RingHom.map_mul, RingHom.map_mul, hz l j, mul_zero, mul_zero]

end GlobalTheory.AnnihBox


open GlobalTheory.AnnihBox in
theorem GlobalTheory.AnnihBox.annihilator_inBox : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ x : Mx D T.rank ρ, (∀ a : Mx D T.rank ρ, a.map (infPart D) = 0 → d.extY T a ∈ U → ψ (symplO S T (d.extX T x) (d.extY T a)) = 1) → InBox K x := by
  intro D ψ hψ S S₀ T ρ d U hU
  let g : Fin T.rank → Fin ρ → (AE D →+ Mx D T.rank ρ) := fun i j =>
    { toFun := fun c => Matrix.single i j (cA D c)
      map_zero' := by simp
      map_add' := fun a b => by simp [Matrix.single_add] }
  have hg : ∀ i j, Continuous (g i j) := fun i j => by
    show Continuous fun c => Matrix.single i j (cA D c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.single_apply]
    split_ifs
    · exact continuous_cA'
    · exact continuous_const
  let f : Fin T.rank → Fin ρ → (AE D →+ WO S T) := fun i j => (d.extY T).comp (g i j)
  have hf : ∀ i j, Continuous (f i j) := fun i j => by
    show Continuous fun c => d.extY T (g i j c)
    simp only [HypDec.extY_apply]
    exact (hg i j).matrix_mul continuous_const
  have hK := fun i j => GlobalTheory.T.stdChar_annihilator_openSubgroup_finPart_compact D ψ hψ (U.comap (f i j)) (hU.preimage (hf i j))
  choose K hKc hK using hK
  let R : Mx D T.rank ρ → Mx D T.rank ρ := fun k => giA T ⬝ k.map (fun z => incA D D.host.xi0⁻¹ * z)
  have hR : Continuous R :=
    continuous_const.matrix_mul (continuous_id.matrix_map (continuous_const.mul continuous_id))
  refine ⟨R '' (Set.univ.pi fun i => Set.univ.pi fun j => K i j : Set (Mx D T.rank ρ)),
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => hKc i j).image hR, ?_⟩
  intro x hx
  have hy : ∀ i j, ∃ k ∈ K i j, finPart D (incA D D.host.xi0 * (gA T ⬝ x) i j - k) = 0 := fun i j =>
    hK i j _ fun c hc hc0 => by
      have h1 : (Matrix.single i j (cA D c)).map (infPart D) = 0 := by
        ext a b
        simp only [Matrix.map_apply, Matrix.single_apply, Matrix.zero_apply]
        split_ifs
        · exact infPart_cA' c hc0
        · exact map_zero _
      have h2 := hx (Matrix.single i j (cA D c)) h1 hc
      rwa [symplO_extX_extY_single] at h2
  choose k hk hk0 using hy
  refine ⟨R (Matrix.of k), ⟨Matrix.of k, fun i _ j _ => hk i j, rfl⟩, ?_⟩
  have hsub : ∀ a b : Mx D T.rank ρ, R (a - b) = R a - R b := fun a b => by
    simp only [R]
    rw [← Matrix.mul_sub]
    congr 1
    ext i j
    simp [mul_sub]
  have hx' : R (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ x) i j) = x := by
    simp only [R]
    have e : (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ x) i j).map (fun z => incA D D.host.xi0⁻¹ * z) =
        gA T ⬝ x := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul]
    rw [e, giA_gA_cancel]
  have e : x - R (Matrix.of k) = R (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ x) i j - k i j) := by
    have hm : (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ x) i j - k i j) =
        (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ x) i j) - Matrix.of k := Matrix.ext fun _ _ => rfl
    rw [hm, hsub, hx']
  exact (congrArg (fun y => y.map (finPart D)) e).trans (map_finPart_mul_map _ _ _ fun i j => hk0 i j)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBoxStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAnnihilator_open_subgroup_in_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ x : Mx D T.rank ρ, (∀ a : Mx D T.rank ρ, a.map (infPart D) = 0 → d.extY T a ∈ U → ψ (symplO S T (d.extX T x) (d.extY T a)) = 1) → InBox K x := by
  first | exact @GlobalTheory.AnnihBox.annihilator_inBox | exact GlobalTheory.AnnihBox.annihilator_inBox | (intros; apply GlobalTheory.AnnihBox.annihilator_inBox <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryConjSelfDualMajorantLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryConjSelfDualMajorantLevels
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EisCont.LevelConj

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)


omit [NumberField E] in
theorem exists_proj_eq (x : ∀ v, GLoc σ J v) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ g : GAd σ J, (∀ v ∈ S, proj σ J v g = x v) ∧ (∀ v ∉ S, proj σ J v g = 1) ∧ ∀ w, projArch σ J w g = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨g, h1, h2, h3⟩ := ih
    refine ⟨emb σ J u (x u) * g, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [map_mul]
      by_cases e : v = u
      · subst e
        rw [proj_emb_self, h2 v hu, mul_one]
      · rw [proj_emb_ne σ J e, one_mul, h1 v ((Finset.mem_insert.1 hv).resolve_left e)]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, proj_emb_ne σ J hv.1, one_mul, h2 v hv.2]
    · rw [map_mul, projArch_emb, one_mul, h3]


omit [NumberField E] in
theorem exists_projArch_eq (x : ∀ w, GArch σ J w) (S : Finset (InfinitePlace F)) :
    ∃ g : GAd σ J, (∀ w ∈ S, projArch σ J w g = x w) ∧ (∀ w ∉ S, projArch σ J w g = 1) ∧ ∀ v, proj σ J v g = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨g, h1, h2, h3⟩ := ih
    refine ⟨embArch σ J u (x u) * g, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [map_mul]
      by_cases e : v = u
      · subst e
        rw [projArch_embArch_self, h2 v hu, mul_one]
      · rw [projArch_embArch_ne σ J e, one_mul, h1 v ((Finset.mem_insert.1 hv).resolve_left e)]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, projArch_embArch_ne σ J hv.1, one_mul, h2 v hv.2]
    · rw [map_mul, proj_embArch, one_mul, h3]

private theorem eventually_latLoc_eq_std_of_selfDual {L : Submodule (𝓞 E) (Fin n → E)}
    (hJ : J.det ≠ 0) (hL : Submodule.IsLattice E L) (hdual : ∀ v, IsSelfDualAt σ J L v) :
    ∀ᶠ v in cofinite, latLoc F L v = latLoc F (stdLattice E n) v := by
  have hstd : Submodule.IsFullLattice E (stdLattice E n) := isLattice_stdLattice
  filter_upwards [eventually_latLoc_le (F := F) hL.fg hstd.span_eq_top,
    AdelicU.SelfDual.eventually_isSelfDualAt (σ := σ) hJ hstd] with v hle hv
  apply le_antisymm hle
  intro y hy
  rw [hdual v]
  rw [hv] at hy
  exact fun x hx => hy x (hle hx)

omit [NumberField E] in
theorem exists_conj_of_local {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hlat : ∀ᶠ v in cofinite, latLoc F L v = latLoc F L' v)
    (a a' : GL (Fin n) (AF F ⊗[F] E))
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : GLoc σ J v, ∀ k : GLoc σ J v,
      k ∈ stabLoc σ J L' v ↔ g⁻¹ * k * g ∈ stabLoc σ J L v)
    (hi : ∀ w : InfinitePlace F, ∃ g : GArch σ J w, ∀ k : GArch σ J w,
      k ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a') ↔
        g⁻¹ * k * g ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a)) :
    ∃ g : GAd σ J, ∀ k : GAd σ J, k ∈ levelAll σ J L' a' ↔ g⁻¹ * k * g ∈ levelAll σ J L a := by
  choose x hx using hf
  choose y hy using hi
  have hS := Filter.eventually_cofinite.1 hlat
  obtain ⟨g, g1, g2, g3⟩ := exists_proj_eq σ J x hS.toFinset
  obtain ⟨h, h1, -, h3⟩ := exists_projArch_eq σ J y Finset.univ
  refine ⟨g * h, fun k => ?_⟩
  rw [mem_levelAll, mem_levelAll]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [map_mul, map_mul, map_inv, map_mul, h3, mul_one]
    by_cases hv : v ∈ hS.toFinset
    · rw [g1 v hv]
      exact hx v _
    · have e : latLoc F L v = latLoc F L' v := by simpa using hv
      rw [g2 v hv, inv_one, one_mul, mul_one, mem_stabLoc, mem_stabLoc, e]
  · rw [map_mul, map_mul, map_inv, map_mul, g3, one_mul, h1 w (Finset.mem_univ w)]
    exact hy w _

end Glue

theorem exists_conj : ∀ (D : D7) (T : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a a' : GL (Fin T.rank) (AE D)), IsLevel T L a → IsLevel T L' a' → ∃ g : GA D T, ∀ k : GA D T, k ∈ lev T L' a' ↔ g⁻¹ * k * g ∈ lev T L a := by
  intro D T L L' a a' h h'
  have hc := isCMExt_host D
  have hJ := isHermND_gram T
  have hf := fun v => GlobalTheory.T.exists_conj_stabilizers_selfDual_lattices_unramified D.host.F D.host.E D.sp.cm.sig hc (GlobalTheory.HeckeAdjoint.unramified_host D) T.rank T.gram
    hJ L L' h.lat h'.lat v (h.dual v) (h'.dual v)
  have hi := fun w => GlobalTheory.T.archimedean_majorant_stabilisers_conjugate D.host.F D.host.E D.sp.cm.sig hc T.rank T.gram hJ a a' h.maj h'.maj w
  have hlat : ∀ᶠ v in cofinite, latLoc D.host.F L v = latLoc D.host.F L' v := by
    filter_upwards [eventually_latLoc_eq_std_of_selfDual D.sp.cm.sig T.gram hJ.2 h.lat h.dual,
      eventually_latLoc_eq_std_of_selfDual D.sp.cm.sig T.gram hJ.2 h'.lat h'.dual] with v hv hv'
    exact hv.trans hv'.symm
  obtain ⟨g, hg⟩ := exists_conj_of_local D.sp.cm.sig T.gram hlat a a' hf hi
  exact ⟨g, fun k => hg k⟩

end GlobalTheory.EisCont.LevelConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryConjSelfDualMajorantLevelsStatement
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_unitary_conj_selfDual_majorant_levels : ∀ (D : D7) (T : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a a' : GL (Fin T.rank) (AE D)), IsLevel T L a → IsLevel T L' a' → ∃ g : GA D T, ∀ k : GA D T, k ∈ lev T L' a' ↔ g⁻¹ * k * g ∈ lev T L a := by
  first | exact @GlobalTheory.EisCont.LevelConj.exists_conj | exact GlobalTheory.EisCont.LevelConj.exists_conj | (intros; apply GlobalTheory.EisCont.LevelConj.exists_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.FlagAct


variable {D : D7} {c : Com D} {s : PiLocalization₂ D}

theorem not_isConjPl_of_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∀ PP ∈ P, ∀ PP' ∈ P, ¬ Lev.IsConjPl PP PP' := by
  classical
  intro PP hP PP' hP' hc
  obtain ⟨⟨es, hes, he⟩, h0⟩ := h
  have hsum : ∑ x ∈ P ×ˢ P, es x.1 * cA D (es x.2) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_product, ← h0, he, map_sum, Finset.sum_mul_sum]
  have hidem : ∀ x ∈ P ×ˢ P,
      (es x.1 * cA D (es x.2)) * (es x.1 * cA D (es x.2)) = es x.1 * cA D (es x.2) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hx
    rw [mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]
  have horth : es PP * cA D (es PP') = 0 :=
    GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) (ι := Pl D.host.E × Pl D.host.E)
      (fun n z hn hz => GlobalTheory.PlaceVec.natCast_mul_eq_zero (D := D) n z hn hz) (fun x => es x.1 * cA D (es x.2)) (P ×ˢ P)
      hidem hsum (PP, PP') (Finset.mem_product.2 ⟨hP, hP'⟩)
  have hfw : ∀ x, x ∈ PP.asIdeal → Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal := by
    intro x hx
    obtain ⟨c', hc', hcv⟩ := hc x hx
    have e1 : c' = Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext hcv
    rw [← e1]; exact hc'
  have hiff : ∀ x, x ∈ PP.asIdeal ↔ Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal := by
    have hle : PP.asIdeal ≤ PP'.asIdeal.comap (Formalism.L2.Col.cO D.host.E) := fun x hx => hfw x hx
    haveI := PP'.isPrime
    have heq := PP.isMaximal.eq_of_le (Ideal.IsPrime.comap (Formalism.L2.Col.cO D.host.E)).ne_top hle
    intro x
    rw [heq]
    exact Ideal.mem_comap
  have hconj := GlobalTheory.MovedIdem.isIdemAt_conj (hes PP' hP') hiff
  have heq : es PP = cA D (es PP') :=
    (GlobalTheory.ExportSeries.idemAt_eq (hes PP hP)).symm.trans (GlobalTheory.ExportSeries.idemAt_eq hconj)
  have hz : es PP = 0 := by
    calc es PP = es PP * es PP := ((hes PP hP).1.1).symm
      _ = es PP * cA D (es PP') := congrArg (es PP * ·) heq
      _ = 0 := horth
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
  have h3 := ((hes PP hP).2 x hx0).1 hxP
  rw [hz, zero_mul, map_zero] at h3
  exact h3 (zero_mem _)

theorem liftsExist_stage {c : Com D} (hc : c.Is) {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) :
    Lev.LiftsExist s.V s.β s.L := by
  obtain ⟨N, hN, -⟩ := hs.base
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  obtain ⟨e, he⟩ := hc.split
  have hnc := not_isConjPl_of_idemSum he
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  refine GlobalTheory.ParahoricLift.liftsExist s.V s.β s.L s.Λ N hN (fun PP hP PP' hP' => ?_) ?_
  · rw [hPg] at hP
    rw [hPg, hQ] at hP'
    rcases hP' with h | h
    · exact hnc PP hP PP' h
    · exact absurd h (Finset.notMem_empty _)
  · rw [hQ]; exact Finset.disjoint_empty_right _

end GlobalTheory.ChainOnto.FlagAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastOpPf

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

theorem cA_mem_idAt {P : Pl D → Prop} {a : AE D} (h : a ∈ idAt D P) : cA D a ∈ idAt D P := by
  obtain ⟨ε, -, hc, -, hε, -⟩ := (localComponents D P).1
  rw [hε] at h ⊢
  conv_rhs => rw [← h]
  rw [map_mul, hc]

theorem mxAt_adj {P : Pl D → Prop} {m n : ℕ} {x : Mx D m n} (hx : MxAt P x) : MxAt P (adj x) := fun i j => by
  have := cA_mem_idAt (hx j i)
  simpa [adj] using this

theorem mxAt_mul_l {P : Pl D → Prop} {l m n : ℕ} (A : Mx D l m) {x : Mx D m n} (hx : MxAt P x) : MxAt P (A * x) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hx k j)

theorem mxAt_mul_r {P : Pl D → Prop} {l m n : ℕ} {x : Mx D l m} (hx : MxAt P x) (A : Mx D m n) : MxAt P (x * A) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hx i k)

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : MxAt P x) : MxAt P (c • x) :=
  fun i j => Ideal.mul_mem_left _ _ (hx i j)

theorem mxAt_add {P : Pl D → Prop} {m n : ℕ} {x y : Mx D m n} (hx : MxAt P x) (hy : MxAt P y) : MxAt P (x + y) :=
  fun i j => add_mem (hx i j) (hy i j)

theorem mxAt_zero {P : Pl D → Prop} {m n : ℕ} : MxAt P (0 : Mx D m n) := fun _ _ => zero_mem _

theorem combAt_single {P : Pl D → Prop} {S T : HSp D} {z : WO S T} (hz : MxAt P z) (c : ℂ) :
    CombAt P (Finsupp.single z c) := fun u hu => by
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]; exact hz

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ z ∈ c.support, c z * heisO ψ S T z f w := by
  simp [comb, Finset.sum_apply, smul_eq_mul]

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (z : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single z c) f = c • heisO ψ S T z f := by
  by_cases hc : c = 0
  · subst hc; simp [comb]
  · simp [comb, Finsupp.support_single_ne_zero _ hc]

theorem symplOH_zero_right (S T : HSp D) (w : WO S T) : symplOH S T w 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem ofAdj_starAdj (S T : HSp D) (x : WO S T) : ofAdj S T (starAdj S T x) = x := by
  have h : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, ← map_mul]
    rw [show -D.host.xi0⁻¹ * -D.host.xi0 = 1 by rw [neg_mul_neg]; exact inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]
    exact map_one _
  rw [ofAdj, starAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h,
    one_smul, Matrix.mul_assoc, Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

def invLine {m n : ℕ} (τ : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E := fun i j => (τ j i)⁻¹

theorem mul_invLine {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (hL : L.rank = 1) (hL'' : L''.rank = 1)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) : τ * invLine τ = 1 := by
  have hsub : ∀ a b : Fin L.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  have hsub'' : ∀ a b : Fin L''.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  let k0 : Fin L''.rank := ⟨0, by omega⟩
  have hne : ∀ i, τ i k0 ≠ 0 := by
    intro i hi
    have h0 : τ = 0 := by
      funext a b
      rw [hsub a i, hsub'' b k0]; exact hi
    rw [h0, Matrix.mul_zero, Matrix.mul_zero] at hτ
    have hc : (-(D.host.xi0 * star D.host.xi0)) ≠ 0 := by
      have := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
      simpa using this
    have hg : L''.gram = 0 := by
      have := hτ.symm
      rwa [smul_eq_zero, or_iff_right hc] at this
    haveI : Nonempty (Fin L''.rank) := ⟨k0⟩
    exact Formalism.L2.Theta.gram_det_ne L'' (by rw [hg, Matrix.det_zero])
  funext i j
  rw [hsub j i, Matrix.one_apply_eq, Matrix.mul_apply, Finset.sum_eq_single k0 (fun b _ hb => absurd (hsub'' b k0) hb)
    (fun h => absurd (Finset.mem_univ _) h)]
  show τ i k0 * (τ i k0)⁻¹ = 1
  exact mul_inv_cancel₀ (hne i)

def kapInv {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (b : WO L S) : WO S L'' :=
  (rat (invLine τ) : Mx D L''.rank L.rank) * starAdj L S b

theorem kap_kapInv {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (hL : L.rank = 1) (hL'' : L''.rank = 1)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) (b : WO L S) :
    kap τ S (kapInv τ S b) = b := by
  rw [kap, kapInv, ← Matrix.mul_assoc, ← rat_mul, mul_invLine τ hL hL'' hτ, rat_one, Matrix.one_mul, ofAdj_starAdj]

theorem mxAt_kapInv {P : Pl D → Prop} {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D)
    {b : WO L S} (hb : MxAt P b) : MxAt P (kapInv τ S b) :=
  mxAt_mul_l _ (mxAt_smul _ (mxAt_mul_l _ (mxAt_mul_r (mxAt_adj hb) _)))

theorem mxAt_kap {P : Pl D → Prop} {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D)
    {w : WO S L''} (hw : MxAt P w) : MxAt P (kap τ S w) :=
  mxAt_smul _ (mxAt_mul_l _ (mxAt_mul_r (mxAt_adj (mxAt_mul_l _ hw)) _))

theorem kap_add {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w w' : WO S L'') :
    kap τ S (w + w') = kap τ S w + kap τ S w' := by
  rw [kap, kap, kap, ← GlobalTheory.LinkKappa.ofAdj_add, Matrix.mul_add]

theorem symplOH_kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) (w w' : WO S L'') :
    symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := by
  have hτ' : τᴴ * (L.gram * τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; congr 1; push_cast; ring
  have h := GlobalTheory.LinkKappa.symplO_ofAdj L L'' S τ (-1) hτ' w w'
  unfold symplOH
  rw [kap, kap, h]
  push_cast; ring

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem lastBi_apply {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (u : WO A S) (v : WO S X) :
    lastBi o o'' τ Ξ Φ₂ u v = Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := rfl

theorem heisO_split {V₀ A L S L'' : HSp D} (o : OrthDec V₀ A L) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (ψ : AddChar (AF D.host.F) ℂ)
    (Ξ : WO V₀ S → ℂ) (x u : WO A S) (y w : WO S L'') :
    heisO ψ V₀ S ((o.resS S).symm (x, kap τ S y)) Ξ ((o.resS S).symm (u, kap τ S w)) =
      ψ (symplOH A S u x) * ψ (symplOH S L'' w y) * Ξ ((o.resS S).symm (u + x, kap τ S (w + y))) := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← map_add (f := _), Prod.mk_add_mk, kap_add,
    symplOH_kap τ hτ, AddChar.map_add_eq_mul]

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem biComb_lastBi {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (ψ : AddChar (AF D.host.F) ℂ)
    (d : WO A S →₀ ℂ) (d' : WO S X →₀ ℂ) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) :
    biComb ψ A S X d d' (lastBi o o'' τ Ξ Φ₂) = ∑ p ∈ d.support ×ˢ d'.support,
      lastBi o o'' τ (comb ψ V₀ S (Finsupp.single ((o.resS S).symm (p.1, kap τ S (o''.resT S p.2).2)) (d p.1 * d' p.2)) Ξ)
        (comb ψ S T (Finsupp.single (o''.resT S p.2).1 1) Φ₂) := by
  funext u v
  simp only [Finset.sum_apply, lastBi_apply, comb_single, Pi.smul_apply, smul_eq_mul, one_mul, heisO_split o τ hτ]
  simp only [biComb, comb_apply]
  simp only [heisO, lastBi_apply, map_add (f := _), Prod.fst_add, Prod.snd_add, o''.symplOH_resT, AddChar.map_add_eq_mul]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem lastBi_comb {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (hL : L.rank = 1) (hL'' : L''.rank = 1)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (ψ : AddChar (AF D.host.F) ℂ)
    (e : WO V₀ S →₀ ℂ) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) :
    lastBi o o'' τ (comb ψ V₀ S e Ξ) Φ₂ = ∑ z ∈ e.support, biComb ψ A S X (Finsupp.single (o.resS S z).1 (e z))
      (Finsupp.single ((o''.resT S).symm (0, kapInv τ S (o.resS S z).2)) 1) (lastBi o o'' τ Ξ Φ₂) := by
  funext u v
  simp only [Finset.sum_apply]
  rw [lastBi_apply, comb_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hz : (o.resS S).symm ((o.resS S z).1, kap τ S (kapInv τ S (o.resS S z).2)) = z := by
    rw [kap_kapInv τ hL hL'' hτ, Prod.mk.eta, AddEquiv.symm_apply_apply]
  have hK := heisO_split o τ hτ ψ Ξ (o.resS S z).1 u (kapInv τ S (o.resS S z).2) (o''.resT S v).2
  rw [hz] at hK
  rw [hK]
  simp only [biComb, comb_single, Pi.smul_apply, smul_eq_mul, one_mul, heisO, lastBi_apply, map_add (f := _),
    AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero, o''.symplOH_resT, symplOH_zero_right,
    AddChar.map_add_eq_mul, AddChar.map_zero_eq_one]
  ring

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem sum_equivFin {α M : Type} [AddCommMonoid M] (s : Finset α) (f : α → M) :
    ∑ p ∈ s, f p = ∑ i : Fin s.card, f (s.equivFin.symm i : α) :=
  (Finset.sum_coe_sort s f).symm.trans (Equiv.sum_comp s.equivFin.symm (fun p : s => f p)).symm

theorem lastOp : ∀ D : D7, GlobalTheory.FinPl.LastOp D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ P
  refine ⟨fun e he => ?_, fun d d' hd hd' => ?_⟩
  · refine ⟨⟨e.support.card, fun i => Finsupp.single (o.resS S (e.support.equivFin.symm i : WO V₀ S)).1
        (e (e.support.equivFin.symm i : WO V₀ S)), fun i => Finsupp.single ((o''.resT S).symm
        (0, kapInv τ S (o.resS S (e.support.equivFin.symm i : WO V₀ S)).2)) 1⟩, fun i => ⟨?_, ?_⟩, fun Ξ Φ₂ => ?_⟩
    · exact combAt_single (mxAt_mul_r (he _ (e.support.equivFin.symm i).2) _) _
    · refine combAt_single ?_ 1
      rw [OrthDec.resT_symm_apply]
      exact mxAt_add (mxAt_mul_l _ mxAt_zero) (mxAt_mul_l _ (mxAt_kapInv τ S (mxAt_mul_r (he _ (e.support.equivFin.symm i).2) _)))
    · rw [lastBi_comb o o'' τ hL hL'' hτ ψ e Ξ Φ₂, sum_equivFin]
      rfl
  · refine ⟨(d.support ×ˢ d'.support).card,
      fun i => Finsupp.single ((o.resS S).symm (((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).1,
        kap τ S (o''.resT S ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).2).2))
        (d ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).1 *
          d' ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).2),
      fun i => Finsupp.single (o''.resT S ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).2).1 1,
      fun i => ⟨?_, ?_⟩, fun Ξ Φ₂ => ?_⟩
    · have hp := Finset.mem_product.1 ((d.support ×ˢ d'.support).equivFin.symm i).2
      refine combAt_single ?_ _
      rw [OrthDec.resS_symm_apply]
      exact mxAt_add (mxAt_mul_r (hd _ hp.1) _) (mxAt_mul_r (mxAt_kap τ S (mxAt_mul_l _ (hd' _ hp.2))) _)
    · have hp := Finset.mem_product.1 ((d.support ×ˢ d'.support).equivFin.symm i).2
      exact combAt_single (mxAt_mul_l _ (hd' _ hp.2)) _
    · rw [biComb_lastBi o o'' τ hτ ψ d d' Ξ Φ₂, sum_equivFin]

end GlobalTheory.LastOpPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatumStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSaw_combinations_operatorDatum : ∀ D : D7, GlobalTheory.FinPl.LastOp D := by
  first | exact @GlobalTheory.LastOpPf.lastOp | exact GlobalTheory.LastOpPf.lastOp | (intros; apply GlobalTheory.LastOpPf.lastOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodClassesGiveTailReading
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodClassesGiveTailReading
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem tailRd_of_clsT : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsT ρ t), A.Is → t.cP ≠ 0 → t.TailRd := by
  intro D c t ρ A hA hcP n h ψ hψ ψ' hψ' a H F
  have e1 := hA.tail n h ψ hψ F
  have e2 := hA.tail n h ψ' hψ' F
  have key : ∀ β (x : A.cl), A.ell n h β x F (ρ.low n h fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) =
      a * A.ell n h β x F (ρ.low n h fun z => t.rd n β ψ' ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) := by
    intro β x
    have : (fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) =
        a • (fun z => t.rd n β ψ' ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) := by
      funext z
      rw [H β ((ρ.fr n).symm z)]
      rfl
    rw [this, map_smul, map_smul, smul_eq_mul]
  simp_rw [key] at e1
  have e3 : t.cP * t.tail n h ψ F = t.cP * (a * t.tail n h ψ' F) := by
    rw [← e1, mul_left_comm t.cP a, ← e2]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  exact mul_left_cancel₀ hcP e3

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodClassesGiveTailReadingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastPeriodClasses_give_tailReading : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsT ρ t), A.Is → t.cP ≠ 0 → t.TailRd := by
  first | exact @GlobalTheory.SeeSaw.tailRd_of_clsT | exact GlobalTheory.SeeSaw.tailRd_of_clsT | (intros; apply GlobalTheory.SeeSaw.tailRd_of_clsT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawScalarFormsContinuousAutomorphicCentral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawScalarFormsContinuousAutomorphicCentral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem RealD.r_center_scalar {c : Comm D} (ρ : RealD c) (hρ : ρ.Is) (j : ℕ) (hj : j ≤ D.R.m) {z : GA D (c.X j)}
    (hz : z ∈ GinfC (c.X j)) (hzc : z ∈ Subgroup.center (GA D (c.X j))) (τ : D.what₂.Tau) :
    ρ.r j hj z τ = (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) • (1 : Matrix (Fin (ρ.N j)) (Fin (ρ.N j)) ℂ) := by
  have hu := hρ.uni j hj
  obtain ⟨ζ, hζ⟩ := GlobalTheory.CenterScalar.scalar_of_comm_unitary (ρ.r j hj z τ) fun U hU => by
    obtain ⟨k, hk⟩ := hu.onto (fun _ => U) fun _ => (Matrix.mem_unitaryGroup_iff').2 hU
    have e1 := hu.mul k ⟨z, hz⟩ τ
    have e2 := hu.mul ⟨z, hz⟩ k τ
    have hkz : (k * ⟨z, hz⟩ : GinfC (c.X j)) = ⟨z, hz⟩ * k :=
      Subtype.ext ((Subgroup.mem_center_iff.1 hzc) k.1)
    rw [hkz, e2] at e1
    have hk' : ρ.r j hj k.1 τ = U := congrFun hk τ
    rw [hk'] at e1
    exact e1.symm
  rcases Nat.eq_zero_or_pos (ρ.N j) with h0 | hpos
  · ext a
    exact absurd a.2 (by omega)
  · rw [hζ, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
      mul_div_assoc, div_self (by exact_mod_cast hpos.ne'), mul_one]

theorem rdX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → RdX t := by
  intro D c 𝒯 t hc _ hP j hj
  obtain ⟨ρ, hρ, H⟩ := hP
  refine ⟨fun z => ∏ τ, (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) ^ (∑ i, (ρ.lam j τ).w i), fun s ψ hψ α y => ?_⟩
  obtain ⟨⟨A, hA⟩, -⟩ := H s
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c (t s) ρ A hc hρ hA.1 j hj ψ hψ α
  refine ⟨h1 y, fun z hz hzc g => ?_⟩
  have hdet : ∀ τ, IsUnit (ρ.r j hj z τ).det := fun τ =>
    Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 ((hρ.uni j hj).uni ⟨z, hz⟩ τ))
  set w := (ρ.fr j y).tr (ρ.r j hj z) hdet with hw
  have e1 : (t s).rd j α ψ y (g * z) = (t s).rd j α ψ ((ρ.fr j).symm w) g :=
    h3 y _ g z hz (by rw [Equiv.apply_symm_apply]; exact Frames.isTr_tr _ hdet _)
  have e2 := (GlobalTheory.KJInf.valC_poly _ _ _ _ |>.2.2.2) _ (h4 g) (fun τ => Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) (ρ.fr j y) w
    (fun τ => by
      show ρ.r j hj z τ * (ρ.fr j y).1 τ = _
      conv_lhs => rw [ρ.r_center_scalar hρ j hj hz hzc τ]
      rw [Matrix.smul_mul, Matrix.one_mul])
  simp only [Equiv.symm_apply_apply] at e2
  rw [e1, e2]

end GlobalTheory.SeeSaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawScalarFormsContinuousAutomorphicCentralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_scalarForms_continuous_automorphic_central : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → RdX t := by
  first | exact @GlobalTheory.SeeSaw.rdX_of_clsPinD | exact GlobalTheory.SeeSaw.rdX_of_clsPinD | (intros; apply GlobalTheory.SeeSaw.rdX_of_clsPinD <;> assumption)
end
end
