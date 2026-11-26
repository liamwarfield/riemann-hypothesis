module

public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.CompactStandardSubgroup.KCptPf

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {nb : nA σ Y b → G2 σ Y}

instance aeBorel : BorelSpace (AE F E) := ⟨rfl⟩

instance matSC : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) := by
  have : SecondCountableTopology (AE F E) := GlobalTheory.EisBL.AETop.secondCountableAE
  exact inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
instance matBorel : BorelSpace (Matrix (Fin n) (Fin n) (AE F E)) := by
  have : SecondCountableTopology (AE F E) := GlobalTheory.EisBL.AETop.secondCountableAE
  exact inferInstanceAs (BorelSpace (Fin n → Fin n → AE F E))
instance nATop : IsTopologicalAddGroup (nA σ Y b) := by
  have : IsTopologicalRing (AE F E) := GlobalTheory.EisBL.AETop.ringAE
  infer_instance
instance nASC : SecondCountableTopology (nA σ Y b) := TopologicalSpace.Subtype.secondCountableTopology _
instance nABorel : BorelSpace (nA σ Y b) := Subtype.borelSpace _

theorem matrix_eq_inFrame_conj (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) :
    mat2 x = incM F b.1 * inFrame b x * incM F (b⁻¹).1 := by
  show mat2 x = incM F b.1 * (incM F (b⁻¹).1 * mat2 x * incM F b.1) * incM F (b⁻¹).1
  simp only [Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.mul_one]
  rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.one_mul]

theorem inFrame_injective (b : GL (Fin n ⊕ Fin n) E) : Function.Injective (inFrame (σ := σ) (Y := Y) b) := by
  intro x y h
  have e : mat2 x = mat2 y := by rw [matrix_eq_inFrame_conj b x, matrix_eq_inFrame_conj b y, h]
  exact Subtype.ext (Units.ext e)

theorem nb_add (h : IsNMap b nb) (β β' : nA σ Y b) : nb (β + β') = nb β * nb β' := by
  apply inFrame_injective b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, h, h, h, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem nb_zero (h : IsNMap b nb) : nb 0 = 1 := by
  apply inFrame_injective b
  rw [h, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  simp

theorem nb_comm (h : IsNMap b nb) (β β' : nA σ Y b) : nb β * nb β' = nb β' * nb β := by
  rw [← nb_add h, ← nb_add h, add_comm]

theorem nb_neg (h : IsNMap b nb) (β : nA σ Y b) : nb (-β) = (nb β)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← nb_add h, neg_add_cancel, nb_zero h]

theorem matrix_of_unipotent_frame (h : IsNMap b nb) (β : nA σ Y b) :
    mat2 (nb β) = incM F b.1 * Matrix.fromBlocks 1 β.1 0 1 * incM F (b⁻¹).1 := by
  rw [matrix_eq_inFrame_conj b, h]

theorem continuous_nb (h : IsNMap b nb) : Continuous nb := by
  have : IsTopologicalRing (AE F E) := GlobalTheory.EisBL.AETop.ringAE
  have hc : Continuous fun β : nA σ Y b => incM F b.1 * Matrix.fromBlocks 1 β.1 0 1 * incM F (b⁻¹).1 :=
    (continuous_const.matrix_mul (Continuous.matrix_fromBlocks continuous_const continuous_subtype_val
      continuous_const continuous_const)).matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact hc.congr fun β => (matrix_of_unipotent_frame h β).symm
  · refine (hc.comp continuous_neg).congr fun β => ?_
    show _ = mat2 (nb β)⁻¹
    rw [← nb_neg h, matrix_of_unipotent_frame h]
    rfl

theorem nmat_form (e : AE F E) (β : Matrix (Fin n) (Fin n) (AE F E)) :
    (Matrix.fromBlocks 1 β 0 1)ᵀ * jw n e * (Matrix.fromBlocks 1 β 0 1).map (cA σ) =
      Matrix.fromBlocks 0 1 (e • 1) (e • β.map (cA σ) + βᵀ) := by
  simp only [jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_one,
    Matrix.transpose_zero]
  have h1 : (1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = 0 := Matrix.map_zero _ (map_zero _)
  rw [h1, h0]
  simp

theorem mem_nA_iff {ε : ℤˣ} (hε : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (β : Matrix (Fin n) (Fin n) (AE F E)) : β ∈ nA σ Y b ↔ βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ)) := by
  refine ⟨fun hβ => ?_, fun hβ => ?_⟩
  · induction hβ using AddSubgroup.closure_induction with
    | mem β h =>
      obtain ⟨x, hx⟩ := h
      have h2 := frame_eq hε x
      rw [hx, nmat_form] at h2
      have h3 := (Matrix.fromBlocks_inj.1 h2).2.2.2
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
      exact h3
    | zero => simp
    | add β β' _ _ h h' =>
      rw [Matrix.transpose_add, h, h', Matrix.map_add _ (map_add _), smul_add, neg_add]
    | neg β _ h =>
      rw [Matrix.transpose_neg, h, Matrix.map_neg _ (map_neg _), smul_neg]
  · obtain ⟨x, hx⟩ := exists_of_frame hε (Matrix.fromBlocks 1 β 0 1) (Matrix.fromBlocks 1 (-β) 0 1)
      (by simp [Matrix.fromBlocks_multiply]) (by
        rw [nmat_form, hβ, add_neg_cancel]
        rfl)
    exact AddSubgroup.subset_closure ⟨x, hx⟩

theorem mem_nF_iff {ν : nA σ Y b} : ν ∈ nF σ Y b ↔ ∃ T : Matrix (Fin n) (Fin n) E, ν.1 = incM F T := by
  refine ⟨fun hν => ?_, fun hν => AddSubgroup.subset_closure hν⟩
  induction hν using AddSubgroup.closure_induction with
  | mem _ h => exact h
  | zero => exact ⟨0, by simp [incM]⟩
  | add _ _ _ _ h h' =>
    obtain ⟨T, hT⟩ := h
    obtain ⟨T', hT'⟩ := h'
    exact ⟨T + T', by rw [AddSubgroup.coe_add, hT, hT']; simp [incM, Matrix.map_add (f := _)]⟩
  | neg _ _ h =>
    obtain ⟨T, hT⟩ := h
    exact ⟨-T, by rw [AddSubgroup.coe_neg, hT]; simp [incM, Matrix.map_neg]⟩

theorem rat_of_inFrame {x : G2 σ Y} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} (h : inFrame b x = incM F M) :
    x ∈ rat2 σ Y := by
  have hinv : incM F M * inFrame b x⁻¹ = 1 := by
    rw [← h, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hdet : M.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hinv
    rw [Matrix.det_mul, Matrix.det_one, incM, show (M.map (inclR (F := F) (AF F))).det = inclR (F := F) (AF F) M.det from
      (RingHom.map_det _ M).symm, h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  let g : GL (Fin n ⊕ Fin n) E := b * Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet * b⁻¹
  refine Subgroup.mem_subgroupOf.2 ⟨g, Units.ext ?_⟩
  show (g.1).map (inclR (F := F) (AF F)) = mat2 x
  rw [matrix_eq_inFrame_conj b x, h]
  simp only [g, Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.map_mul]
  rfl

theorem nb_rat (h : IsNMap b nb) {ν : nA σ Y b} (hν : ν ∈ nF σ Y b) : nb ν ∈ rat2 σ Y := by
  obtain ⟨T, hT⟩ := mem_nF_iff.1 hν
  refine rat_of_inFrame (b := b) (M := Matrix.fromBlocks 1 T 0 1) ?_
  rw [h, hT]
  simp [incM, Matrix.fromBlocks_map]

instance countable_nF : Countable (nF σ Y b) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  refine Function.Injective.countable (f := fun ν : nF σ Y b => Classical.choose (mem_nF_iff.1 ν.2)) ?_
  intro x y hxy
  have hx := Classical.choose_spec (mem_nF_iff.1 x.2)
  have hy := Classical.choose_spec (mem_nF_iff.1 y.2)
  apply Subtype.ext; apply Subtype.ext
  rw [hx, hy]
  exact congrArg _ hxy

theorem trace_inclR (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem tt_rat (M : Matrix (Fin n) (Fin n) E) :
    Algebra.trace (AF F) (AE F E) (incM F M).trace = algebraMap F (AF F) (Algebra.trace F E M.trace) := by
  rw [← trace_inclR]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [incM, Matrix.trace, map_sum]

theorem psi_rat {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (T ν : nF σ Y b) :
    ψ (Algebra.trace (AF F) (AE F E) (T.1.1 * ν.1.1).trace) = 1 := by
  obtain ⟨A, hA⟩ := mem_nF_iff.1 T.2
  obtain ⟨B, hB⟩ := mem_nF_iff.1 ν.2
  rw [hA, hB, incM, incM, ← Matrix.map_mul, ← incM, tt_rat]
  exact hψ.2.1 _

end PositivityTheory.SiegelWeilFormula.kunf

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.FrameInvPf
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

theorem jw_sq_ks {R : Type} [CommRing R] (n : ℕ) (e : R) : jw n e * jw n e = e • 1 := by
  rw [jw, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  simp

private theorem map_jw_eq_self_of_involution {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ x, s (s x) = x) {n : ℕ} (e : R)
    (hse : s e = e) : (jw n e).map s = jw n e := by
  unfold jw
  rw [Matrix.fromBlocks_map]
  congr 1
  · ext i j; simp
  · ext i j; simp [Matrix.one_apply]
  · ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.smul_apply, h, hse]
  · ext i j; simp

theorem frame_inv_pf {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ x, s (s x) = x) {n : ℕ} (e : R) (he : e * e = 1)
    (hse : s e = e) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hM : Mᵀ * jw n e * M.map s = jw n e) :
    M * Matrix.fromBlocks (M.toBlocks₂₂.map s)ᵀ (e • (M.toBlocks₁₂.map s)ᵀ) (e • (M.toBlocks₂₁.map s)ᵀ)
      (M.toBlocks₁₁.map s)ᵀ = 1 ∧
    Matrix.fromBlocks (M.toBlocks₂₂.map s)ᵀ (e • (M.toBlocks₁₂.map s)ᵀ) (e • (M.toBlocks₂₁.map s)ᵀ)
      (M.toBlocks₁₁.map s)ᵀ * M = 1 := by
  set N := Matrix.fromBlocks (M.toBlocks₂₂.map s)ᵀ (e • (M.toBlocks₁₂.map s)ᵀ) (e • (M.toBlocks₂₁.map s)ᵀ)
      (M.toBlocks₁₁.map s)ᵀ with hN
  have hss : (M.map s).map s = M := by ext i j; simp [hs]
  have hM' : (M.map s)ᵀ * jw n e * M = jw n e := by
    have := congrArg (fun X => X.map s) hM
    simp only [Matrix.map_mul, Matrix.transpose_map, map_jw_eq_self_of_involution s hs e hse, hss] at this
    simpa [Matrix.transpose_map] using this
  have hJ : jw n e * jw n e = e • 1 := jw_sq_ks n e
  have hK : N = e • (jw n e * (M.map s)ᵀ * jw n e) := by
    conv_rhs => rw [← Matrix.fromBlocks_toBlocks (M.map s)]
    simp only [jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, hN]
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, smul_smul, he]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp
  have h1 : N * M = 1 := by
    rw [hK, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (M.map s)ᵀ, hM', hJ,
      smul_smul, he, one_smul]
  exact ⟨mul_eq_one_comm.mp h1, h1⟩

end PositivityTheory.SiegelWeilFormula.kunf

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.TBlkEqTFMulProdTV
noncomputable section

open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.BRoad
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.kunf.SecA

attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem isCompact_stdK' (B : Base F E) (Y : Spc F E n) (hB : B.IsGood σ) (b : GL (Fin n ⊕ Fin n) E)
    (K : Subgroup (G2 σ Y)) (hK : IsStdK (σ := σ) (Y := Y) B b K) : IsCompact (K : Set (G2 σ Y)) := by
  obtain ⟨Φ, hΦ, eΦ⟩ := GlobalTheory.ThK.Dbl.St.exists_section hB.cm B.emb
  have hI : IsCompact (intHat F E : Set (AE F E)) := isCompact_intHat
  have hfe : finOne F = GlobalTheory.ThK.Dbl.St.eF F := rfl
  set T : Set (AE F E) := Φ '' Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1) + (intHat F E : Set (AE F E))
    with hTdef
  have hT : IsCompact T := ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).image hΦ).add hI
  have hentry : ∀ k ∈ K, ∀ i j, inFrame b k i j ∈ T := by
    intro k hk i j
    obtain ⟨h1, h2⟩ := (hK k).1 hk
    rw [eΦ (inFrame b k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      have hu : (inFrame b k).map (piInf (B.emb w)) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ :=
        Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose]; exact h1 w)
      exact entry_norm_bound_of_unitary hu i j
    · rw [← hfe]
      exact h2 k (Set.mem_insert _ _) i j
  set S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
    (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) => incM F b.1 * M * incM F (b⁻¹).1) '' Set.univ.pi (fun _ => Set.univ.pi fun _ => T) with hSdef
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hT).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  have hmat : ∀ k ∈ K, mat2 k ∈ S := fun k hk => ⟨inFrame b k, fun i _ j _ => hentry k hk i j, by
    show incM F b.1 * (incM F (b⁻¹).1 * mat2 k * incM F b.1) * incM F (b⁻¹).1 = mat2 k
    simp only [Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.one_mul]⟩
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have hIc := hI.isClosed
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := Y) b
  have hKset : (K : Set (G2 σ Y)) =
      (⋂ w, {k | (inFrame b k).map (piInf (B.emb w)) * ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, {k : G2 σ Y | finOne F • inFrame b k i j ∈ intHat F E}) ∩
          (⋂ i, ⋂ j, {k : G2 σ Y | finOne F • inFrame b k⁻¹ i j ∈ intHat F E})) := by
    ext k
    simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.forall_mem_insert,
      Set.mem_singleton_iff, forall_eq]
  have hKc : IsClosed (K : Set (G2 σ Y)) := by
    rw [hKset]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_))
    · exact (hfr.matrix_map (hp w)).matrix_mul (hfr.matrix_map (hp w)).matrix_conjTranspose
    · exact (hfr.matrix_elem i j).const_smul (finOne F)
    · exact ((hfr.comp continuous_inv).matrix_elem i j).const_smul (finOne F)
  exact GlobalTheory.ThK.Dbl.St.isCompact_of_units (UG (cA σ) (dbl (incM F Y.J))) (GlobalTheory.EisBL.DoubledGroupTopology.isClosed_doubled_group σ Y) K hKc S hS
    fun k hk => ⟨hmat k hk, hmat k⁻¹ (K.inv_mem hk)⟩

variable {Y : Spc F E n}

def tBlk (p : G2 σ Y) : Matrix (Fin n) (Fin n) (AE F E) := (mat2 p * dC n (AE F E)).toRows₁

theorem tBlk_eq_tF_mul_prod_tV {p : G2 σ Y} {t : GL (Fin n) (AE F E)} (hp : IsPar p t) : tBlk p = t.1 := by
  rw [tBlk, isPar_iff.1 hp]
  simp [dC, diagCols, Matrix.fromRows_mul]

theorem continuous_levi_block : Continuous (tBlk (σ := σ) (Y := Y)) := by
  have hm : Continuous fun g : G2 σ Y => mat2 g := Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun g : G2 σ Y => mat2 g * dC n (AE F E) := hm.matrix_mul continuous_const
  exact continuous_pi fun i => continuous_pi fun j => h1.matrix_elem (Sum.inl i) j

def uDet (p : par2 σ Y) : (AE F E)ˣ where
  val := (tBlk p.1).det
  inv := (tBlk p.1⁻¹).det
  val_inv := by
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 p.2
    rw [tBlk_eq_tF_mul_prod_tV ht, tBlk_eq_tF_mul_prod_tV ht.inv, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  inv_val := by
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 p.2
    rw [tBlk_eq_tF_mul_prod_tV ht, tBlk_eq_tF_mul_prod_tV ht.inv, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

theorem uDet_eq {p : par2 σ Y} {t : GL (Fin n) (AE F E)} (hp : IsPar p.1 t) : uDet p = Matrix.GeneralLinearGroup.det t :=
  Units.ext (by simp [uDet, tBlk_eq_tF_mul_prod_tV hp])

theorem continuous_uDet : Continuous (uDet (σ := σ) (Y := Y)) := by
  rw [Units.continuous_iff]
  refine ⟨(continuous_levi_block.comp continuous_subtype_val).matrix_det, ?_⟩
  exact (continuous_levi_block.comp (continuous_inv.comp continuous_subtype_val)).matrix_det

end PositivityTheory.SiegelWeilFormula.kunf.SecA

end
end
