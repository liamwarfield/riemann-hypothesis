module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatHatStabiliserIffComplementFrameRel
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatHatStabiliserIffComplementFrameRel
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.StabFrame

section Lin

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_mulVec_eq (σ : E →ₐ[F] E) {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin M) (Fin M') E) (N : Matrix (Fin M') (Fin M) E) (hN : N * B = 1) (x : Fin M → E)
    (hM : M' + 1 = M) (hB : ∀ j, hE σ J x (fun i => B i j) = 0) (hx : hE σ J x x ≠ 0) :
    (∀ z, hE σ J x (B *ᵥ z) = 0) ∧ ∀ y, hE σ J x y = 0 → B *ᵥ (N *ᵥ y) = y := by
  let φ : (Fin M → E) →ₗ[E] E :=
    { toFun := fun y => hE σ J x y
      map_add' := fun y z => by
        simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring }
  have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker φ := by
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hB j
  have hinj : Function.Injective B.mulVecLin := fun z w h => by
    have := congrArg (N *ᵥ ·) h
    simpa [Matrix.mulVec_mulVec, hN] using this
  have h1 : Module.finrank E (LinearMap.range B.mulVecLin) = M' := by
    rw [LinearMap.finrank_range_of_inj hinj]; simp
  have hlt : LinearMap.ker φ < ⊤ := lt_top_iff_ne_top.2 fun h => hx (by
    have : x ∈ LinearMap.ker φ := h ▸ Submodule.mem_top
    exact this)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_top, Module.finrank_fin_fun] at h2
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨fun z => hle ⟨z, rfl⟩, fun y hy => ?_⟩
  have : y ∈ LinearMap.range B.mulVecLin := heq ▸ hy
  obtain ⟨z, rfl⟩ := this
  simp [Matrix.mulVec_mulVec, hN]

theorem map_mulVec_tmul (R : Type) [CommRing R] [Algebra F R] {m n : ℕ} (C : Matrix (Fin m) (Fin n) E)
    (a : R) (z : Fin n → E) :
    C.map (inclR (F := F) R) *ᵥ (fun i => a ⊗ₜ[F] z i) = fun i => a ⊗ₜ[F] (C *ᵥ z) i := by
  funext i
  simp [Matrix.mulVec, dotProduct, inclR, TensorProduct.tmul_sum]

variable [NumberField F]

theorem mulVec_mem_latHat {m n : ℕ} (C : Matrix (Fin m) (Fin n) E) {S : Set (Fin n → E)}
    {T : Set (Fin m → E)} (h : ∀ z ∈ S, C *ᵥ z ∈ T) {y : Fin n → Af F ⊗[F] E} (hy : y ∈ latHat F E S) :
    C.map (inclR (F := F) (Af F)) *ᵥ y ∈ latHat F E T := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h z hz, map_mulVec_tmul _ C a z⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg]; exact neg_mem hy

theorem mulVec_eq_of_mem_latHat {n : ℕ} (C : Matrix (Fin n) (Fin n) E) {S : Set (Fin n → E)}
    (h : ∀ z ∈ S, C *ᵥ z = z) {y : Fin n → Af F ⊗[F] E} (hy : y ∈ latHat F E S) :
    C.map (inclR (F := F) (Af F)) *ᵥ y = y := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    rw [map_mulVec_tmul, h z hz]
  | zero => rw [Matrix.mulVec_zero]
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | neg y _ hy => rw [Matrix.mulVec_neg, hy]

theorem stabHat_iff {M M' : ℕ} (B : Matrix (Fin M) (Fin M') E) (N : Matrix (Fin M') (Fin M) E)
    (hN : N * B = 1) {P : Set (Fin M → E)} {L' : Set (Fin M' → E)} (h1 : ∀ z, z ∈ L' ↔ B *ᵥ z ∈ P)
    (h2 : ∀ y ∈ P, B *ᵥ (N *ᵥ y) = y) (a b : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (a' b' : Matrix (Fin M') (Fin M') (Af F ⊗[F] E)) (hb : b * a = 1) (hb' : a' * b' = 1)
    (hr : a * B.map (inclR (F := F) (Af F)) = B.map (inclR (F := F) (Af F)) * a') :
    StabHat F P a ↔ StabHat F L' a' := by
  set Bf := B.map (inclR (F := F) (Af F)) with hBf
  set Nf := N.map (inclR (F := F) (Af F)) with hNf
  have hNB : Nf * Bf = 1 := by
    rw [hBf, hNf, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBm : ∀ z ∈ latHat F E L', Bf *ᵥ z ∈ latHat F E P := fun z hz =>
    mulVec_mem_latHat B (fun w hw => (h1 w).1 hw) hz
  have hNm : ∀ y ∈ latHat F E P, Nf *ᵥ y ∈ latHat F E L' := fun y hy =>
    mulVec_mem_latHat N (fun w hw => (h1 _).2 (by rw [h2 w hw]; exact hw)) hy
  have hBN : ∀ y ∈ latHat F E P, Bf *ᵥ (Nf *ᵥ y) = y := fun y hy => by
    rw [Matrix.mulVec_mulVec, hBf, hNf, ← Matrix.map_mul]
    exact mulVec_eq_of_mem_latHat _ (fun w hw => by rw [← Matrix.mulVec_mulVec]; exact h2 w hw) hy
  have hiff : ∀ z, z ∈ latHat F E L' ↔ Bf *ᵥ z ∈ latHat F E P := fun z =>
    ⟨hBm z, fun hz => by simpa [Matrix.mulVec_mulVec, hNB] using hNm _ hz⟩
  have hcomm : ∀ z, a *ᵥ (Bf *ᵥ z) = Bf *ᵥ (a' *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hr]
  refine ⟨fun h z => ?_, fun h y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · rw [hiff, hiff, ← hcomm]
    exact h _
  · rw [← hBN y hy, hcomm]
    exact hBm _ ((h _).1 (hNm y hy))
  · have e1 : a' *ᵥ (b' *ᵥ (Nf *ᵥ (a *ᵥ y))) = Nf *ᵥ (a *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hb', Matrix.one_mulVec]
    have e2 : y = Bf *ᵥ (b' *ᵥ (Nf *ᵥ (a *ᵥ y))) := by
      have := congrArg (b *ᵥ ·) (hcomm (b' *ᵥ (Nf *ᵥ (a *ᵥ y))))
      simp only [e1, hBN _ hy] at this
      rw [Matrix.mulVec_mulVec _ b a, Matrix.mulVec_mulVec _ b a, hb, Matrix.one_mulVec,
        Matrix.one_mulVec] at this
      exact this.symm
    rw [e2]
    exact hBm _ ((h _).2 (by rw [e1]; exact hNm _ hy))

def finPt (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA (AF F) σ J) : HA (Af F) σ J :=
  (⟨Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (HA.mat (AF F) σ J g), by
    have hg : Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J g).1 * JR (AF F) J * (HA.mat (AF F) σ J g).1 =
      JR (AF F) J := (show HR (AF F) σ J from g).2
    have := GlobalTheory.UnitarySplit.map_cond _ _ _ (GlobalTheory.UnitarySplit.map_sig (sndA F) σ) (JR (AF F) J)
      (HA.mat (AF F) σ J g).1
    rw [hg, GlobalTheory.UnitarySplit.map_JR] at this
    exact this.symm⟩ : HR (Af F) σ J)

theorem map_snd_incl {m n : ℕ} (C : Matrix (Fin m) (Fin n) E) :
    (C.map (inclR (F := F) (AF F))).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom =
      C.map (inclR (F := F) (Af F)) := by
  ext i j
  simp [inclR]

end Lin

theorem stab_iff_of_frameRel : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin M → E)) (L' : Set (Fin M' → E)), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → (∀ y, y ∈ L' ↔ B *ᵥ y ∈ L) → ∀ (g : HA (AF F) σ J) (g' : HA (AF F) σ J'), g ∈ Hstab (AF F) σ J x → FrameRel J J' B g g' → (g ∈ stab σ J (L : Set (Fin M → E)) ↔ g' ∈ stab σ J' L') := by
  intro H F E _ _ _ _ _ σ hCM hu M M' J J' B x hM hJ hJ' hBJ hB hx L L' hL β hβ hxL hq hL' g g' hg hr
  let p := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  have hN : (J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)) * B = 1 := by
    rw [Matrix.mul_assoc, hBJ, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hJ'.2)]
  obtain ⟨k1, k2⟩ := exists_mulVec_eq σ J B _ hN (x 0) hM hB hx
  have h3 := (H F E σ hCM hu M J hJ L hL β hβ (x 0) hxL hq).2.2
  have hgf : finPt σ J g ∈ Hstab (Af F) σ J (fun _ => x 0) := by
    have e : (HA.mat (AF F) σ J g).1 *ᵥ (fun i => inclR (AF F) (x 0 i)) = fun i => inclR (AF F) (x 0 i) :=
      congrFun (MulAction.mem_stabilizer_iff.1 hg) 0
    have e' : (p ∘ fun i => inclR (AF F) (x 0 i)) = fun i => inclR (Af F) (x 0 i) := by
      funext i
      simp [p, inclR]
    refine MulAction.mem_stabilizer_iff.2 (funext fun _ => funext fun i => ?_)
    have := RingHom.map_mulVec p (HA.mat (AF F) σ J g).1 (fun i => inclR (AF F) (x 0 i)) i
    rw [e, e'] at this
    exact this.symm.trans (congrFun e' i)
  have h4 : StabHat F (L : Set (Fin M → E)) (finMat σ J g) ↔
      StabHat F (perpIn σ J L (x 0)) (finMat σ J g) := by
    have := SetLike.ext_iff.1 h3 (finPt σ J g)
    rw [Subgroup.mem_inf, Subgroup.mem_inf, and_iff_left hgf, and_iff_left hgf] at this
    exact this
  refine h4.trans (stabHat_iff (P := perpIn σ J L (x 0)) B _ hN (fun z => (hL' z).trans ⟨fun h => ⟨h, k1 z⟩, fun h => h.1⟩)
    (fun y hy => k2 y hy.2) _ (finMat σ J g⁻¹) _ (finMat σ J' g'⁻¹) ?_ ?_ ?_)
  · rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, inv_mul_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  · rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, mul_inv_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  · have : ((HA.mat (AF F) σ J g).1 * B.map (inclR (AF F))).map p =
        (B.map (inclR (AF F)) * (HA.mat (AF F) σ J' g').1).map p := congrArg (fun X => Matrix.map X p) hr
    have := (Matrix.map_mul (f := p)).symm.trans (this.trans (Matrix.map_mul (f := p)))
    rw [map_snd_incl] at this
    exact this

end GlobalTheory.StabFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatHatStabiliserIffComplementFrameRelStatement
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latHat_stabiliser_iff_complement_frameRel : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin M → E)) (L' : Set (Fin M' → E)), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → (∀ y, y ∈ L' ↔ B *ᵥ y ∈ L) → ∀ (g : HA (AF F) σ J) (g' : HA (AF F) σ J'), g ∈ Hstab (AF F) σ J x → FrameRel J J' B g g' → (g ∈ stab σ J (L : Set (Fin M → E)) ↔ g' ∈ stab σ J' L') := by
  first | exact @GlobalTheory.StabFrame.stab_iff_of_frameRel | exact GlobalTheory.StabFrame.stab_iff_of_frameRel | (intros; apply GlobalTheory.StabFrame.stab_iff_of_frameRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClosedEmbeddingOfIsStabilizerEmbeddingUpq
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClosedEmbeddingOfIsStabilizerEmbeddingUpq
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabEmbClosed

theorem isClosedEmbedding_conj_fromBlocks {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m (n ⊕ Unit) ℂ) (N : Matrix (n ⊕ Unit) m ℂ) (hNM : N * M = 1) :
    IsClosedEmbedding
      (fun X : Matrix n n ℂ => M * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * N) := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun Y : Matrix m m ℂ => (N * Y * M).toBlocks₁₁) ?_ ?_ ?_
  · intro X
    have : N * (M * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * N) * M
        = fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) := by
      calc _ = (N * M) * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * (N * M) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hNM, Matrix.one_mul, Matrix.mul_one]
    simp only [this, toBlocks_fromBlocks₁₁]
  · have h : Continuous fun Y : Matrix m m ℂ => N * Y * M :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h.matrix_submatrix Sum.inl Sum.inl
  · exact (continuous_const.matrix_mul
      (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
        continuous_const)).matrix_mul continuous_const

theorem isClosedEmbedding_of_isStabEmb : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ (x₀ : Fin P ⊕ Fin Q → ℂ), star x₀ ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x₀ ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb x₀ j → IsClosedEmbedding j := by
  intro P Q P' Q' hd x₀ hx j hj
  obtain ⟨C, hC, hCx, hj⟩ := hj
  obtain ⟨N, B, hNM, hMN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hd hx hC hCx
  have key : ∀ g : UpqT P' Q', (j g).mat =
      C.fromCols (replicateCol Unit x₀) * fromBlocks g.mat 0 0 (1 : Matrix Unit Unit ℂ) * N := by
    intro g
    obtain ⟨h1, h2⟩ := hj g
    have h3 : (j g).mat * replicateCol Unit x₀ = replicateCol Unit x₀ := by
      rw [← replicateCol_mulVec, h1]
    have h4 : (j g).mat * C.fromCols (replicateCol Unit x₀) =
        C.fromCols (replicateCol Unit x₀) * fromBlocks g.mat 0 0 (1 : Matrix Unit Unit ℂ) := by
      rw [mul_fromCols, fromCols_mul_fromBlocks, h2, h3]
      simp
    rw [← h4, Matrix.mul_assoc, hMN, Matrix.mul_one]
  refine IsClosedEmbedding.of_comp
    (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P) (Q := Q)).isEmbedding ?_
  have := (isClosedEmbedding_conj_fromBlocks _ N hNM).comp
    (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P') (Q := Q'))
  convert this using 1
  funext g
  exact key g

end GlobalTheory.StabEmbClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClosedEmbeddingOfIsStabilizerEmbeddingUpqStatement
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_of_isStabilizerEmbeddingUpq : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ (x₀ : Fin P ⊕ Fin Q → ℂ), star x₀ ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x₀ ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb x₀ j → IsClosedEmbedding j := by
  first | exact @GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb | exact GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb | (intros; apply GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMeasurableRealOrbitMapOfAdelicOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMeasurableRealOrbitMapOfAdelicOrbit
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.RealOrbitMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_homeomorph (h : IsCMExt F E σ) {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) :
    ∃ Φ : (Ainf F ⊗[F] E) ≃ₜ (I → ℂ), ∀ z ρ, Φ z ρ = θ ρ z := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e₀⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e₀.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e₀.secondCountableTopology
  have hb := infEmb_bijective h hτ hθ
  let Θ : Ainf F ⊗[F] E →+ (I → ℂ) := (Pi.ringHom θ).toAddMonoidHom
  have hΘ : Continuous Θ := continuous_pi fun ρ => infEmb_continuous (hθ ρ)
  have ho : IsOpenMap Θ := AddMonoidHom.isOpenMap_of_sigmaCompact Θ hb.2 hΘ
  exact ⟨(Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho, fun _ _ => rfl⟩

theorem mat_inv_mul {P Q : ℕ} (t : UpqT P Q) : UpqT.mat t⁻¹ * UpqT.mat t = 1 :=
  Units.inv_mul (show Formalism.UG.Upq P Q from t).1

theorem theta_projInf {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) :
    (fun i => θ (projInf (h • ratTup (F := F) (AF F) x) 0 i)) = infMat σ J θ h *ᵥ fun i => τ (x 0 i) := by
  funext i
  let p : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have e := RingHom.map_mulVec (θ.comp p) (HA.mat (AF F) σ J h).1 (ratTup (F := F) (AF F) x 0) i
  refine e.trans ?_
  have e2 : (θ.comp p) ∘ ratTup (F := F) (AF F) x 0 = fun i => τ (x 0 i) := by
    funext j
    rw [← hθ.1]
    show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (1 ⊗ₜ x 0 j)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [e2]
  rfl

theorem realOrbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)), IsCMFam τ → ∀ (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ) (J : Matrix (Fin M) (Fin M) E) (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ), (∀ ρ, N ρ * A ρ = 1) → (∀ ρ, A ρ * N ρ = 1) → ∀ x : Fin 1 → Fin M → E, AllSome (fun pt : (I → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E) => ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) fun pt => Measurable pt ∧ (∀ g g', (∀ ρ, UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i)) = UpqT.mat (g' ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) → pt g = pt g') ∧ ∀ (h : HA (AF F) σ J) (t : I → UpqT P Q), (∀ ρ, UpqT.mat (t ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) → pt t = projInf (h⁻¹ • ratTup (F := F) (AF F) x) := by
  intro F E _ _ _ _ _ σ hcm I _ τ hτ θ hθ M P Q J A N hl hr x
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph hcm hτ hθ
  let v : (I → UpqT P Q) → I → Fin P ⊕ Fin Q → ℂ := fun g ρ => UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))
  have key : ∀ (Y : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : I → Fin P ⊕ Fin Q → ℂ),
      (∀ ρ, infCoord (θ ρ) (A ρ) Y = w ρ) ↔ Y = fun _ i => Φ.symm fun ρ => (N ρ *ᵥ w ρ) i := by
    intro Y w
    constructor
    · intro hY
      funext a i
      obtain rfl : a = 0 := Subsingleton.elim _ _
      apply Φ.injective
      rw [Φ.apply_symm_apply]
      funext ρ
      rw [hΦ, ← hY ρ, infCoord, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
    · rintro rfl ρ
      have : (fun i => θ ρ (Φ.symm fun ρ => (N ρ *ᵥ w ρ) i)) = N ρ *ᵥ w ρ := by
        funext i
        rw [← hΦ, Φ.apply_symm_apply]
      rw [infCoord, this, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]
  refine ⟨⟨fun g _ i => Φ.symm fun ρ => (N ρ *ᵥ v g ρ) i, fun g => (key _ (v g)).2 rfl⟩, fun pt hpt => ?_⟩
  have hpt' : ∀ g, pt g = fun _ i => Φ.symm fun ρ => (N ρ *ᵥ v g ρ) i := fun g => (key _ (v g)).1 (hpt g)
  refine ⟨?_, fun g g' hg => ?_, fun h t ht => ?_⟩
  · haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
    haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
    haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    haveI : SecondCountableTopology (UpqT P Q) :=
      (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
    rw [show pt = _ from funext hpt']
    refine Measurable.of_eval fun _ => Measurable.of_eval fun i => Continuous.measurable ?_
    refine Φ.symm.continuous.comp (continuous_pi fun ρ => (continuous_apply i).comp (f := fun a => N ρ *ᵥ v a ρ) ?_)
    exact continuous_const.matrix_mulVec
      ((GlobalTheory.VolPairExists.continuous_mat.comp (continuous_apply ρ).inv).matrix_mulVec continuous_const)
  · rw [hpt', hpt', show v g = v g' from funext hg]
  · rw [hpt']
    refine ((key _ (v t)).1 fun ρ => ?_).symm
    have e : A ρ * infMat σ J (θ ρ) h⁻¹ = UpqT.mat (t ρ)⁻¹ * A ρ := by
      calc A ρ * infMat σ J (θ ρ) h⁻¹
          = UpqT.mat (t ρ)⁻¹ * (UpqT.mat (t ρ) * A ρ) * infMat σ J (θ ρ) h⁻¹ := by
            rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
        _ = UpqT.mat (t ρ)⁻¹ * A ρ := by
            rw [ht, Matrix.mul_assoc, Matrix.mul_assoc, ← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, mul_inv_cancel,
              Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_one, Matrix.mul_one]
    rw [infCoord, theta_projInf (hθ ρ), Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]

end GlobalTheory.RealOrbitMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMeasurableRealOrbitMapOfAdelicOrbitStatement
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_realOrbitMap_of_adelicOrbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)), IsCMFam τ → ∀ (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ) (J : Matrix (Fin M) (Fin M) E) (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ), (∀ ρ, N ρ * A ρ = 1) → (∀ ρ, A ρ * N ρ = 1) → ∀ x : Fin 1 → Fin M → E, AllSome (fun pt : (I → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E) => ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) fun pt => Measurable pt ∧ (∀ g g', (∀ ρ, UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i)) = UpqT.mat (g' ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) → pt g = pt g') ∧ ∀ (h : HA (AF F) σ J) (t : I → UpqT P Q), (∀ ρ, UpqT.mat (t ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) → pt t = projInf (h⁻¹ • ratTup (F := F) (AF F) x) := by
  first | exact @GlobalTheory.RealOrbitMap.realOrbit | exact GlobalTheory.RealOrbitMap.realOrbit | (intros; apply GlobalTheory.RealOrbitMap.realOrbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormAndSelfDualLatticeInFrameCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormAndSelfDualLatticeInFrameCoords
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.FrameDict

theorem form_coords {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (W : Formalism.BasicNotions.HSpace E) (x y : Fin W.rank → E) :
    hE cm.sig W.gram x y = W.hT (∑ i, x i • W.frame i) (∑ i, y i • W.frame i) := by
  have hs : ∀ a : E, (cm.sig : E →+* E) a = star a := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul,
    LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, hs,
    Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_one_iff {E : Type} [Field E] [NumberField E] (z : E) :
    z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨z, h⟩, rfl⟩

theorem dict : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (W : HSpace E), (∀ a b : W.V, hE cm.sig W.gram (fun i => W.frame.repr a i) (fun i => W.frame.repr b i) = W.hT a b) ∧ ∃ L : Submodule (𝓞 E) (Fin W.rank → E), IsSelfDualLat cm.sig W.gram L ∧ (L : Set (Fin W.rank → E)) = latC W := by
  intro F E _ _ _ _ _ _ cm W
  refine ⟨fun a b => ?_, ?_⟩
  · rw [form_coords, W.frame.sum_repr, W.frame.sum_repr]
  obtain ⟨L, hfg, hsp, hL⟩ := exists_lattice W
  refine ⟨L, ⟨hfg, hsp, fun y => ?_⟩, hL⟩
  have hmem : ∀ x : Fin W.rank → E, x ∈ L ↔ ∑ i, x i • W.frame i ∈ W.L0 := fun x => by
    rw [← SetLike.mem_coe, hL]; rfl
  have hu : ∀ v : W.V, (∀ u ∈ W.L0, W.hT u v ∈ (1 : Submodule (𝓞 E) E)) ↔ v ∈ W.L0 := fun v => by
    have h : Formalism.HermitianLatticesTheory.dual W.hT W.L0 = W.L0 := W.baseLattice_isUnimodular
    conv_rhs => rw [← h]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
  rw [hmem, ← hu]
  constructor
  · intro h x hx
    rw [form_coords, ← mem_one_iff]
    exact h _ ((hmem x).1 hx)
  · intro h u hu'
    have := h (fun i => W.frame.repr u i) (by rw [hmem, W.frame.sum_repr]; exact hu')
    rw [form_coords, W.frame.sum_repr, ← mem_one_iff] at this
    exact this

end GlobalTheory.FrameDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormAndSelfDualLatticeInFrameCoordsStatement
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_and_selfDual_lattice_in_frame_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (W : HSpace E), (∀ a b : W.V, hE cm.sig W.gram (fun i => W.frame.repr a i) (fun i => W.frame.repr b i) = W.hT a b) ∧ ∃ L : Submodule (𝓞 E) (Fin W.rank → E), IsSelfDualLat cm.sig W.gram L ∧ (L : Set (Fin W.rank → E)) = latC W := by
  first | exact @GlobalTheory.FrameDict.dict | exact GlobalTheory.FrameDict.dict | (intros; apply GlobalTheory.FrameDict.dict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MapRestrictLatticeStabiliserMeasureEqCompactDual
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MapRestrictLatticeStabiliserMeasureEqCompactDual
noncomputable section

namespace GlobalTheory.VolStabImage

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem map_restrict_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), M = P + Q → ∀ (J : Matrix (Fin M) (Fin M) E), J.det ≠ 0 → ∀ (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∀ (L : Set (Fin M → E)), MeasurableSet (stab σ J L : Set (HA (AF F) σ J)) → ∀ (cd : CDHaar) (μ : Measure (HA (AF F) σ J)), (∀ B : I → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) → μ {h | StabHat F L (finMat σ J h) ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat σ J (θ ρ) h} = ∏ ρ, cd.cd P Q (B ρ)) → (∃ N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ, (∀ ρ, N ρ * A ρ = 1) ∧ ∀ ρ, A ρ * N ρ = 1) ∧ ∃ ψ : HA (AF F) σ J →* (I → UpqT P Q), Continuous ψ ∧ (∀ h ρ, UpqT.mat (ψ h ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) ∧ (μ.restrict (stab σ J L)).map ψ = Measure.pi fun _ => cd.cd P Q := by
  intro F E _ _ _ _ _ σ hcm I _ τ θ hθ M P Q hM J hJ A hA L hL cd μ hμ
  have hd : ∀ ρ, IsUnit (J.map (τ ρ)).det := fun ρ => by
    have : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
    rw [this]
    exact ((map_ne_zero (τ ρ)).2 hJ).isUnit
  let N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ := fun ρ => (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q)
  have hl : ∀ ρ, N ρ * A ρ = 1 := fun ρ => by
    change (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q) * A ρ = 1
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ (hd ρ)]
  have e : Fin M ≃ (Fin P ⊕ Fin Q) := Fintype.equivOfCardEq (by simpa using hM)
  have hr : ∀ ρ, A ρ * N ρ = 1 := fun ρ => (Matrix.mul_eq_one_comm_of_equiv e).1 (hl ρ)
  refine ⟨⟨N, hl, hr⟩, ?_⟩
  choose ψ hψ hψm using fun ρ => GlobalTheory.VolPairExists.exists_hom _ (continuous_infMat J (hθ ρ))
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul σ J (θ ρ)) (infMat_unitary J hcm (hθ ρ)) (hA ρ) (hl ρ) (hr ρ)
  have hψA : ∀ h ρ, UpqT.mat (ψ ρ h) * A ρ = A ρ * infMat σ J (θ ρ) h := fun h ρ => by
    rw [hψm, Matrix.mul_assoc, hl, Matrix.mul_one]
  have hc : Continuous (MonoidHom.pi ψ) := continuous_pi hψ
  refine ⟨MonoidHom.pi ψ, hc, hψA, ?_⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (UpqT P Q) :=
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (UpqT P Q) :=
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  have := cd.haar P Q
  refine (Measure.pi_eq fun B hB => ?_).symm
  have hm : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hB
  rw [Measure.map_apply hc.measurable hm, Measure.restrict_apply (hc.measurable hm), ← hμ B hB]
  congr 1
  ext h
  refine and_comm.trans (and_congr Iff.rfl ?_)
  rw [Set.mem_preimage, Set.mem_univ_pi]
  refine forall_congr' fun ρ => ⟨fun hb => ⟨_, hb, hψA h ρ⟩, ?_⟩
  rintro ⟨b, hb, hbA⟩
  have : b = ψ ρ h := GlobalTheory.VolPairExists.mat_injective (by
    rw [hψm, ← hbA, Matrix.mul_assoc, hr, Matrix.mul_one])
  subst this
  exact hb

end GlobalTheory.VolStabImage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MapRestrictLatticeStabiliserMeasureEqCompactDualStatement
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_restrict_latticeStabiliser_measure_eq_compactDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), M = P + Q → ∀ (J : Matrix (Fin M) (Fin M) E), J.det ≠ 0 → ∀ (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∀ (L : Set (Fin M → E)), MeasurableSet (stab σ J L : Set (HA (AF F) σ J)) → ∀ (cd : CDHaar) (μ : Measure (HA (AF F) σ J)), (∀ B : I → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) → μ {h | StabHat F L (finMat σ J h) ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat σ J (θ ρ) h} = ∏ ρ, cd.cd P Q (B ρ)) → (∃ N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ, (∀ ρ, N ρ * A ρ = 1) ∧ ∀ ρ, A ρ * N ρ = 1) ∧ ∃ ψ : HA (AF F) σ J →* (I → UpqT P Q), Continuous ψ ∧ (∀ h ρ, UpqT.mat (ψ h ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) ∧ (μ.restrict (stab σ J L)).map ψ = Measure.pi fun _ => cd.cd P Q := by
  first | exact @GlobalTheory.VolStabImage.map_restrict_stab | exact GlobalTheory.VolStabImage.map_restrict_stab | (intros; apply GlobalTheory.VolStabImage.map_restrict_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnfoldingKernelLevelSubgroupBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnfoldingKernelLevelSubgroupBruhat
open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

namespace GlobalTheory

theorem exists_unfoldingKernel_levelSubgroup_bruhat : ∀ (G G' T T' : Type) [Group G] [Group G'] [Group T] [Group T'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableSpace T] [MeasurableSpace T'] [MeasurableMul G'] [MeasurableMul T] [MeasurableInv T'] (μ : Measure G) (μ' : Measure G') [μ'.IsMulLeftInvariant] (m : Measure T) (m' : Measure T') [m'.IsInvInvariant] (K : Subgroup G) (K' : Subgroup G'), MeasurableSet (K : Set G) → MeasurableSet (K' : Set G') → ∀ (φ : G' →* G) (ψ : G →* T) (ψ' : G' →* T') (j : T' →* T), Measurable ψ → Measurable ψ' → Measurable j → (∀ g, φ g ∈ K ↔ g ∈ K') → (∀ g, ψ (φ g) = j (ψ' g)) → (μ.restrict K).map ψ = m → (μ'.restrict K').map ψ' = m' → ∀ (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∀ (f : T → ℝ≥0∞), Measurable f → (∀ s t, f (j s * t) = f t) → ∀ ν, IsQuotientMeasure j m' m ν → ∃ u : G → ℝ≥0∞, Measurable u ∧ ∫⁻ h, u h ∂μ = ∫⁻ c, f (Quotient.out c) ∂ν ∧ ∀ h, ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ' = {h | ∃ g, (φ g)⁻¹ * h ∈ K}.indicator 1 h * f (ψ h) := by
  intro G G' T T' _ _ _ _ _ _ _ _ _ _ _ μ μ' _ m m' _ K K' hK hK' φ ψ ψ' j hψ hψ' hj hφK hcomm
    hm hm' b hb hb1 f hf hfinv ν hν
  have hbf : Measurable fun t => b t * f t := hb.mul hf
  refine ⟨(K : Set G).indicator (fun h => b (ψ h) * f (ψ h)), (hbf.comp hψ).indicator hK, ?_, ?_⟩
  · rw [lintegral_indicator hK, ← lintegral_map hbf hψ, hm, hν _ hbf]
    refine lintegral_congr fun c => ?_
    simp only [hfinv]
    rw [lintegral_mul_const _ (f := fun s => b (j s * Quotient.out c))
      (hb.comp (hj.mul_const _)), hb1, one_mul]
  · intro h
    by_cases hh : ∃ g, (φ g)⁻¹ * h ∈ K
    · obtain ⟨g₀, hk⟩ := hh
      have hmem : h ∈ {h | ∃ g, (φ g)⁻¹ * h ∈ K} := ⟨g₀, hk⟩
      rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
      obtain ⟨k, rfl⟩ : ∃ k, h = φ g₀ * k := ⟨(φ g₀)⁻¹ * h, by simp⟩
      rw [inv_mul_cancel_left] at hk
      rw [← lintegral_mul_left_eq_self _ g₀]
      have hF : Measurable fun s : T' => b (j s⁻¹ * ψ k) :=
        hb.comp ((hj.comp measurable_inv).mul_const _)
      have key : ∀ g, (K : Set G).indicator (fun h => b (ψ h) * f (ψ h))
          ((φ (g₀ * g))⁻¹ * (φ g₀ * k)) =
          (K' : Set G').indicator (fun g => b (j (ψ' g)⁻¹ * ψ k) * f (ψ k)) g := by
        intro g
        have e : (φ (g₀ * g))⁻¹ * (φ g₀ * k) = (φ g)⁻¹ * k := by
          rw [map_mul]; group
        have e2 : ψ ((φ g)⁻¹ * k) = j (ψ' g)⁻¹ * ψ k := by
          rw [map_mul, map_inv, hcomm, map_inv]
        rw [e]
        by_cases hg : g ∈ K'
        · have : (φ g)⁻¹ * k ∈ (K : Set G) := K.mul_mem (K.inv_mem ((hφK g).2 hg)) hk
          rw [Set.indicator_of_mem this, Set.indicator_of_mem (show g ∈ (K' : Set G') from hg),
            e2, hfinv]
        · have : (φ g)⁻¹ * k ∉ (K : Set G) := fun hx =>
            hg ((hφK g).1 (K.inv_mem_iff.1 ((K.mul_mem_cancel_right hk).1 hx)))
          rw [Set.indicator_of_notMem this,
            Set.indicator_of_notMem (show g ∉ (K' : Set G') from hg)]
      simp only [key]
      rw [lintegral_indicator hK',
        ← lintegral_map (f := fun s : T' => b (j s⁻¹ * ψ k) * f (ψ k)) (hF.mul_const _) hψ', hm',
        lintegral_mul_const _ hF, lintegral_inv_eq_self (fun s => b (j s * ψ k)), hb1, one_mul,
        map_mul, hcomm, hfinv]
    · have hmem : h ∉ {h | ∃ g, (φ g)⁻¹ * h ∈ K} := hh
      rw [Set.indicator_of_notMem hmem, zero_mul]
      have : ∀ g, (K : Set G).indicator (fun h => b (ψ h) * f (ψ h)) ((φ g)⁻¹ * h) = 0 :=
        fun g => Set.indicator_of_notMem (fun hx => hh ⟨g, hx⟩) _
      simp only [this, lintegral_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnfoldingKernelLevelSubgroupBruhatStatement
open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unfoldingKernel_levelSubgroup_bruhat_alt : ∀ (G G' T T' : Type) [Group G] [Group G'] [Group T] [Group T'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableSpace T] [MeasurableSpace T'] [MeasurableMul G'] [MeasurableMul T] [MeasurableInv T'] (μ : Measure G) (μ' : Measure G') [μ'.IsMulLeftInvariant] (m : Measure T) (m' : Measure T') [m'.IsInvInvariant] (K : Subgroup G) (K' : Subgroup G'), MeasurableSet (K : Set G) → MeasurableSet (K' : Set G') → ∀ (φ : G' →* G) (ψ : G →* T) (ψ' : G' →* T') (j : T' →* T), Measurable ψ → Measurable ψ' → Measurable j → (∀ g, φ g ∈ K ↔ g ∈ K') → (∀ g, ψ (φ g) = j (ψ' g)) → (μ.restrict K).map ψ = m → (μ'.restrict K').map ψ' = m' → ∀ (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∀ (f : T → ℝ≥0∞), Measurable f → (∀ s t, f (j s * t) = f t) → ∀ ν, IsQuotientMeasure j m' m ν → ∃ u : G → ℝ≥0∞, Measurable u ∧ ∫⁻ h, u h ∂μ = ∫⁻ c, f (Quotient.out c) ∂ν ∧ ∀ h, ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ' = {h | ∃ g, (φ g)⁻¹ * h ∈ K}.indicator 1 h * f (ψ h) := by
  first | exact @GlobalTheory.exists_unfoldingKernel_levelSubgroup_bruhat | exact GlobalTheory.exists_unfoldingKernel_levelSubgroup_bruhat | (intros; apply GlobalTheory.exists_unfoldingKernel_levelSubgroup_bruhat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralTsumOrbitUnfold
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralTsumOrbitUnfold
open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory

theorem lintegral_tsum_orbit_unfold (G G' V X : Type) [Group G] [Group G'] [MeasurableSpace G]
    [MeasurableSpace G'] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul G'] [MulAction G V]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (μ' : Measure G') [SFinite μ']
    [μ'.IsMulLeftInvariant] (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] [Countable Γ']
    (𝓕 : Set G) (𝓕' : Set G') (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (h𝓕' : IsFundamentalDomain Γ' 𝓕' μ') (φ : G' →* G) (hφm : Measurable φ)
    (hφi : Function.Injective φ) (hΓ : ∀ g, φ g ∈ Γ ↔ g ∈ Γ') (x : V)
    (hst : φ.range = MulAction.stabilizer G x) (c : X → V) (hc : Function.Injective c)
    (hcr : ∀ y, y ∈ Set.range c ↔ ∃ γ ∈ Γ, γ • x = y) (u : G → ℝ≥0∞) (hu : Measurable u)
    (Φ : V → ℝ≥0∞) (hΦ : ∀ h : G, Φ (h⁻¹ • x) = ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ') :
    ∫⁻ h in 𝓕, ∑' i, Φ (h⁻¹ • c i) ∂μ = μ' 𝓕' * ∫⁻ h, u h ∂μ := by
  haveI : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : MeasurableConstSMul Γ' G' := ⟨fun γ => measurable_const_mul (γ : G')⟩
  haveI : SMulInvariantMeasure Γ G μ :=
    ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  haveI : SMulInvariantMeasure Γ' G' μ' :=
    ⟨fun γ s _ => measure_preimage_mul μ' (γ : G') s⟩
  have hex : ∀ i, ∃ γ ∈ Γ, γ • x = c i := fun i => (hcr _).1 ⟨i, rfl⟩
  choose γ hγ hγx using hex
  have hfix : ∀ g, φ g • x = x := fun g => by
    have : φ g ∈ MulAction.stabilizer G x := hst ▸ ⟨g, rfl⟩
    exact this
  let f : X × Γ' → Γ := fun p => ⟨γ p.1 * φ p.2, Γ.mul_mem (hγ _) ((hΓ _).2 p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ hab
      have h1 : γ i * φ a = γ j * φ b := congrArg Subtype.val hab
      have h2 : i = j := by
        apply hc
        have := congrArg (· • x) h1
        simpa [mul_smul, hfix, hγx] using this
      subst h2
      have h3 : a = b := Subtype.ext (hφi (mul_left_cancel h1))
      rw [h3]
    · rintro ⟨δ, hδ⟩
      obtain ⟨i, hi⟩ := (hcr (δ • x)).2 ⟨δ, hδ, rfl⟩
      have h1 : (γ i)⁻¹ * δ ∈ φ.range := by
        rw [hst, MulAction.mem_stabilizer_iff, mul_smul, ← hi, ← hγx, inv_smul_smul]
      obtain ⟨a, ha⟩ := h1
      have ha' : a ∈ Γ' := (hΓ a).1 (ha ▸ Γ.mul_mem (Γ.inv_mem (hγ i)) hδ)
      refine ⟨(i, ⟨a, ha'⟩), Subtype.ext ?_⟩
      show γ i * φ a = δ
      rw [ha, mul_inv_cancel_left]
  let F : G → ℝ≥0∞ := fun h => ∫⁻ g in 𝓕', u ((φ g)⁻¹ * h) ∂μ'
  have hK : Measurable (fun p : G × G' => u ((φ p.2)⁻¹ * p.1)) :=
    hu.comp (((hφm.comp measurable_snd).inv).mul measurable_fst)
  have hF : Measurable F := hK.lintegral_prod_right'
  have step : ∀ h : G, ∑' i, Φ (h⁻¹ • c i) = ∑' δ : Γ, F (δ⁻¹ • h) := by
    intro h
    rw [← (Equiv.ofBijective f hf).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun i => ?_
    have h1 : h⁻¹ • c i = ((γ i)⁻¹ * h)⁻¹ • x := by
      rw [mul_inv_rev, inv_inv, mul_smul, hγx]
    rw [h1, hΦ, h𝓕'.lintegral_eq_tsum'']
    refine tsum_congr fun a => ?_
    refine lintegral_congr fun g => ?_
    congr 1
    show (φ ((a : G') * g))⁻¹ * ((γ i)⁻¹ * h) = (φ g)⁻¹ * ((γ i * φ a)⁻¹ * h)
    simp [mul_assoc]
  simp_rw [step]
  rw [lintegral_tsum (f := fun (δ : Γ) h => F (δ⁻¹ • h)) (fun δ => (hF.comp (measurable_const_smul δ⁻¹)).aemeasurable),
    ← h𝓕.lintegral_eq_tsum' F]
  show ∫⁻ h, ∫⁻ g in 𝓕', u ((φ g)⁻¹ * h) ∂μ' ∂μ = _
  rw [lintegral_lintegral_swap hK.aemeasurable]
  simp_rw [lintegral_mul_left_eq_self u]
  rw [setLIntegral_const, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralTsumOrbitUnfoldStatement
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_tsum_orbit_unfold_alt : ∀ (G G' V X : Type) [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul G'] [MulAction G V] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (μ' : Measure G') [SFinite μ'] [μ'.IsMulLeftInvariant] (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] [Countable Γ'] (𝓕 : Set G) (𝓕' : Set G'), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ' 𝓕' μ' → ∀ (φ : G' →* G), Measurable φ → Function.Injective φ → (∀ g, φ g ∈ Γ ↔ g ∈ Γ') → ∀ (x : V), φ.range = MulAction.stabilizer G x → ∀ (c : X → V), Function.Injective c → (∀ y, y ∈ Set.range c ↔ ∃ γ ∈ Γ, γ • x = y) → ∀ (u : G → ℝ≥0∞), Measurable u → ∀ (Φ : V → ℝ≥0∞), (∀ h : G, Φ (h⁻¹ • x) = ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ') → ∫⁻ h in 𝓕, ∑' i, Φ (h⁻¹ • c i) ∂μ = μ' 𝓕' * ∫⁻ h, u h ∂μ := by
  first | exact @GlobalTheory.lintegral_tsum_orbit_unfold | exact GlobalTheory.lintegral_tsum_orbit_unfold | (intros; apply GlobalTheory.lintegral_tsum_orbit_unfold <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizer
noncomputable section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.VolumeUnfolding

theorem exists_perp_matrix {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (W W' : HSpace E) (ι : W'.V →ₗ[E] W.V) (x : W.V)
    (hι : HSpace.IsIsomEmb W' W ι) (hr : LinearMap.range ι = LinearMap.ker (W.hT x))
    (hL : ∀ y, y ∈ W'.L0 ↔ ι y ∈ W.L0) :
    ∃ B : Matrix (Fin W.rank) (Fin W'.rank) E, Formalism.UG.cT (cm.sig : E →+* E) B * W.gram * B = W'.gram ∧
      (∀ j, hE cm.sig W.gram (coordTup W x 0) (fun i => B i j) = 0) ∧
      ∀ y, y ∈ latC W' ↔ B *ᵥ y ∈ latC W := by
  have hd := (GlobalTheory.T.hermitian_form_and_selfDual_lattice_in_frame_coords F E cm W).1
  refine ⟨Matrix.of fun i j => W.frame.repr (ι (W'.frame j)) i, ?_, fun j => ?_, fun y => ?_⟩
  · ext a b
    have := hd (ι (W'.frame a)) (ι (W'.frame b))
    rw [hι] at this
    refine Eq.trans ?_ this
    simp only [hE, Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm
  · have h : ι (W'.frame j) ∈ LinearMap.ker (W.hT x) := hr ▸ LinearMap.mem_range_self _ _
    exact (hd x (ι (W'.frame j))).trans h
  · refine (hL _).trans (iff_of_eq (congrArg (· ∈ W.L0) ?_))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← W.frame.sum_repr (ι (W'.frame j)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]

theorem perp_matrix_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M M' : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    {J' : Matrix (Fin M') (Fin M') E} {B : Matrix (Fin M) (Fin M') E} {x : Fin M → E}
    (hB : Formalism.UG.cT (σ : E →+* E) B * J * B = J') (hx : ∀ j, hE σ J x (fun i => B i j) = 0) (τ : E →+* ℂ) :
    (B.map τ)ᴴ * J.map τ * B.map τ = J'.map τ ∧ ((B.map τ)ᴴ * J.map τ) *ᵥ (fun i => τ (x i)) = 0 := by
  have e : (B.map τ)ᴴ = (Formalism.UG.cT (σ : E →+* E) B).map τ := by
    ext i j
    exact (h.2.2.2 τ _).symm
  refine ⟨by rw [e, ← hB, Matrix.map_mul, Matrix.map_mul], funext fun j => ?_⟩
  have h1 := congrArg (fun z => star (τ z)) (hx j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, star_sum, star_mul', map_zero, star_zero] at h1
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Finset.sum_mul, Pi.zero_apply]
  rw [← h1]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h2 : τ ((σ : E →+* E) (x a)) = star (τ (x a)) := h.2.2.2 τ _
  rw [h2, star_star, ← h.2.2.2 τ (J a b), hJ.1 b a]
  ring

section Real

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ}

omit [NumberField E] in
theorem proj_incl (hθ : IsInfEmb τ θ) (z : E) :
    (θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom) (inclR (AF F) z) = τ z := by
  rw [← hθ.1 z]
  simp [inclR]

omit [NumberField E] in
theorem infMat_fix (hθ : IsInfEmb τ θ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {x : Fin 1 → Fin M → E}
    {g : HA (AF F) σ J} (hg : g ∈ Hstab (AF F) σ J x) :
    infMat σ J θ g *ᵥ (fun i => τ (x 0 i)) = fun i => τ (x 0 i) := by
  funext i
  let p := θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have h1 := congrArg p (congrFun (congrFun hg 0) i)
  have h2 := RingHom.map_mulVec p (HA.mat _ _ _ g).1 (ratTup (F := F) (AF F) x 0) i
  have h3 : p ∘ ratTup (F := F) (AF F) x 0 = fun i => τ (x 0 i) := funext fun i => proj_incl hθ _
  rw [h3] at h2
  exact h2.symm.trans (h1.trans (proj_incl hθ _))

omit [NumberField E] in
theorem infMat_frame (hθ : IsInfEmb τ θ) {M M' : ℕ} {J : Matrix (Fin M) (Fin M) E} {J' : Matrix (Fin M') (Fin M') E}
    {B : Matrix (Fin M) (Fin M') E} {g : HA (AF F) σ J} {g' : HA (AF F) σ J'} (hg : FrameRel J J' B g g') :
    infMat σ J θ g * B.map τ = B.map τ * infMat σ J' θ g' := by
  let p := θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have h3 : (B.map (inclR (AF F))).map p = B.map τ := Matrix.ext fun _ _ => proj_incl hθ _
  rw [← h3]
  exact (Matrix.map_mul (f := p)).symm.trans ((congrArg (fun m => m.map p) hg).trans (Matrix.map_mul (f := p)))

end Real

theorem rational_orbit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (W : HSpace E) (x : W.V) {β : E} (hx : W.hT x x = β) (hβ : β ≠ 0) :
    Function.Injective (fun x' : {x' : W.V // W.hT x' x' = β} => ratTup (F := F) (AF F) (coordTup W x'.1)) ∧
    ∀ y, y ∈ Set.range (fun x' : {x' : W.V // W.hT x' x' = β} => ratTup (F := F) (AF F) (coordTup W x'.1)) ↔
      ∃ γ ∈ ratPts (AF F) cm.sig W.gram, γ • ratTup (F := F) (AF F) (coordTup W x) = y := by
  have hd := (GlobalTheory.T.hermitian_form_and_selfDual_lattice_in_frame_coords F E cm W).1
  have hxx : hE cm.sig W.gram (coordTup W x 0) (coordTup W x 0) = β := (hd x x).trans hx
  obtain ⟨hw1, hw2⟩ := GlobalTheory.T.rational_vectors_same_length_one_unitary_orbit F E cm.sig (isCMExt cm) _ W.gram (isHermND cm W) (coordTup W x) (hxx ▸ hβ)
  refine ⟨fun a b hab => ?_, fun y => Iff.trans ⟨?_, ?_⟩ (hw2 y)⟩
  · exact Subtype.ext (W.frame.repr.injective (Finsupp.ext (congrFun (congrFun (hw1 hab) 0))))
  · rintro ⟨x', rfl⟩
    exact ⟨coordTup W x'.1, ((hd x'.1 x'.1).trans x'.2).trans hxx.symm, rfl⟩
  · rintro ⟨x', h1, rfl⟩
    have e : coordTup W (W.frame.equivFun.symm (x' 0)) = x' := by
      funext a i
      rw [Subsingleton.elim a 0]
      exact congrFun (W.frame.equivFun.apply_symm_apply (x' 0)) i
    refine ⟨⟨W.frame.equivFun.symm (x' 0), ?_⟩, congrArg _ e⟩
    rw [← e] at h1
    exact (hd _ _).symm.trans (h1.trans hxx)

theorem unramified_host (D : D7) : UnramifiedAtFinite D.host.F D.host.E := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  have hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  intro P hP _
  exact Algebra.unramified_iff_forall.1 hU ⟨P, hP⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unfoldAt (hT : StabTransitive) (D : D7) (W W' : HSpace D.host.E) (P Q P' Q' : ℕ)
    (hc : P' + Q' + 1 = P + Q) (hs : W.SigOK) (hPQ : ∀ τ, W.sig τ = (P, Q)) (hs' : W'.SigOK)
    (hPQ' : ∀ τ, W'.sig τ = (P', Q')) (β : D.host.F) (hβ : β = 1 ∨ β = -1) (x : W.V)
    (hx : W.hT x x = algebraMap _ _ β) (hxL : x ∈ W.L0) (ι : W'.V →ₗ[D.host.E] W.V)
    (hι : HSpace.IsIsomEmb W' W ι) (hr : LinearMap.range ι = LinearMap.ker (W.hT x))
    (hL : ∀ y, y ∈ W'.L0 ↔ ι y ∈ W.L0) : UnfoldAt D W W' P Q P' Q' (algebraMap _ _ β) x := by
  intro μ μ' 𝓕 𝓕' hμ hμ' h𝓕 h𝓕' _ _
  have hcm := isCMExt D.sp.cm
  have hJ := isHermND D.sp.cm W
  have hJ' := isHermND D.sp.cm W'
  have hτ : IsCMFam (embOf D) := GlobalTheory.Mem.Vol.isCMFam_host D.R D.host _ D.eTau
  have hβ0 : algebraMap D.host.F D.host.E β ≠ 0 := by rcases hβ with rfl | rfl <;> simp
  obtain ⟨τ₀⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hM : W.rank = P + Q := by have := sig_sum W hs τ₀; rw [hPQ] at this; exact this.symm
  have hM' : W'.rank = P' + Q' := by have := sig_sum W' hs' τ₀; rw [hPQ'] at this; exact this.symm
  have hMM : W'.rank + 1 = W.rank := by omega
  obtain ⟨hd, L, hLs, hLc⟩ := GlobalTheory.T.hermitian_form_and_selfDual_lattice_in_frame_coords _ _ D.sp.cm W
  obtain ⟨-, L', hLs', hLc'⟩ := GlobalTheory.T.hermitian_form_and_selfDual_lattice_in_frame_coords _ _ D.sp.cm W'
  obtain ⟨B, hB, hBx, hBL⟩ := exists_perp_matrix D.sp.cm W W' ι x hι hr hL
  have hxx : hE D.sp.cm.sig W.gram (coordTup W x 0) (coordTup W x 0) = algebraMap _ _ β := (hd x x).trans hx
  have hx0 : hE D.sp.cm.sig W.gram (coordTup W x 0) (coordTup W x 0) ≠ 0 := hxx ▸ hβ0
  have hxL' : coordTup W x 0 ∈ L := by
    rw [← SetLike.mem_coe, hLc]
    change ∑ i, W.frame.repr x i • W.frame i ∈ W.L0
    rwa [W.frame.sum_repr]
  refine ⟨hμ.2.1, fun θ hθ => ⟨(hμ.2.2 θ hθ).1, fun A hA => ?_⟩⟩
  have hAx : ∀ ρ, star (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ
      (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) ≠ 0 := fun ρ h0 => by
    have := (GlobalTheory.UnfoldingCompare.norm_coords W (embOf D ρ) (GlobalTheory.UnfoldingCompare.emb_star D _) (A ρ) (hA ρ) x).symm.trans h0
    rw [hx] at this
    exact hβ0 ((map_eq_zero _).1 this)
  have hBτ := fun ρ => perp_matrix_map hcm hJ hB hBx (embOf D ρ)
  refine ⟨?_, fun j hj => ?_⟩
  · have key : ∀ ρ, ∃ j : UpqT P' Q' →* UpqT P Q,
        IsStabEmb (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) j := fun ρ => by
      have h1 := hs' (embOf D ρ)
      rw [hPQ'] at h1
      obtain ⟨A', N', hA', -, hr'⟩ := GlobalTheory.VolPairExists.exists_frame h1
      have e1 : (A ρ * B.map (embOf D ρ) * N')ᴴ * Formalism.UG.Jpq P Q * A ρ =
          N'ᴴ * ((B.map (embOf D ρ))ᴴ * W.gram.map (embOf D ρ)) := by
        rw [← hA ρ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      have e2 : (A ρ * B.map (embOf D ρ) * N')ᴴ * Formalism.UG.Jpq P Q * (A ρ * B.map (embOf D ρ) * N') =
          Formalism.UG.Jpq P' Q' := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.mul_assoc N'ᴴ, (hBτ ρ).1,
          GlobalTheory.VolPairExists.conj_frame hA' hr']
      have e3 : ((A ρ * B.map (embOf D ρ) * N')ᴴ * Formalism.UG.Jpq P Q) *ᵥ
          (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) = 0 := by
        rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, (hBτ ρ).2, Matrix.mulVec_zero]
      obtain ⟨j, hj⟩ := GlobalTheory.UnfoldingCompare.exists_stab_hom hc (hAx ρ) e2 e3
      exact ⟨j, _, e2, e3, hj⟩
    choose j hj using key
    exact ⟨j, hj⟩
  have : ∀ P Q, IsTopologicalGroup (UpqT P Q) := fun P Q => inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  have : ∀ P Q, T2Space (UpqT P Q) := fun P Q => inferInstanceAs (T2Space (Formalism.UG.Upq P Q))
  have : ∀ P Q, BorelSpace (UpqT P Q) := fun P Q => ⟨rfl⟩
  have : ∀ P Q, LocallyCompactSpace (UpqT P Q) := fun P Q =>
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : ∀ P Q, SecondCountableTopology (UpqT P Q) := fun P Q =>
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  have := D.cd.haar
  have := fun P Q => GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q (D.cd.cd P Q) (D.cd.haar P Q)
  have := fun P Q => GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant (D.cd.cd P Q)
  have hjc : IsClosedEmbedding (piEmb j) :=
    IsClosedEmbedding.piMap fun ρ => GlobalTheory.T.isClosedEmbedding_of_isStabilizerEmbeddingUpq P Q P' Q' hc _ (hAx ρ) (j ρ) (hj ρ)
  have hjm := hjc.continuous.measurable
  obtain ⟨b, hb, hb1⟩ := GlobalTheory.T.exists_bruhatFunction_of_closedEmbedding _ _ (piEmb j) hjc (Measure.pi fun _ => D.cd.cd P' Q')
  refine ⟨GlobalTheory.T.exists_isQuotientMeasure_of_bruhat _ _ (piEmb j) hjm _ _ b hb hb1, fun ν hν => ?_⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary _ _ D.sp.cm.sig W.rank W.gram
  obtain ⟨i1', i2', i3'⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary _ _ D.sp.cm.sig W'.rank W'.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig W.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig W.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig W'.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig W'.gram
  have := hμ.1
  have := hμ'.1
  have hK := (isOpen_stab (σ := D.sp.cm.sig) W.gram L hLs.1 hLs.2.1).measurableSet
  have hK' := (isOpen_stab (σ := D.sp.cm.sig) W'.gram L' hLs'.1 hLs'.2.1).measurableSet
  have hdet' : ∀ ρ, (W'.gram.map (embOf D ρ)).det ≠ 0 := fun ρ => by
    have : (W'.gram.map (embOf D ρ)).det = embOf D ρ W'.gram.det := ((embOf D ρ).map_det W'.gram).symm
    rw [this]
    exact (map_ne_zero _).2 hJ'.2
  choose A' hA' hAj using fun ρ => GlobalTheory.T.exists_complement_frame_compatible_stabilizerEmbedding P Q P' Q' _ _ hc hM' _ _ _ _ (A ρ) (hA ρ) (hBτ ρ).1 (hdet' ρ)
    (hBτ ρ).2 (hAx ρ) (j ρ) (hj ρ)
  obtain ⟨⟨N, hN, hN'⟩, ψ, hψ, hψA, hψm⟩ := GlobalTheory.T.map_restrict_latticeStabiliser_measure_eq_compactDual _ _ _ hcm _ (embOf D) θ hθ _ P Q hM W.gram hJ.2 A hA L hK D.cd μ
    (by rw [hLc]; exact (hμ.2.2 θ hθ).2 A hA)
  obtain ⟨-, ψ', hψ', hψA', hψm'⟩ := GlobalTheory.T.map_restrict_latticeStabiliser_measure_eq_compactDual _ _ _ hcm _ (embOf D) θ hθ _ P' Q' hM' W'.gram hJ'.2 A' hA' L' hK' D.cd μ'
    (by rw [hLc']; exact (hμ'.2.2 θ hθ).2 A' hA')
  obtain ⟨hpt, hpt'⟩ := GlobalTheory.T.exists_measurable_realOrbitMap_of_adelicOrbit _ _ _ hcm _ (embOf D) hτ θ hθ _ P Q W.gram A N hN hN' (coordTup W x)
  refine ⟨hpt, fun pt hp Φi hΦ => ?_⟩
  obtain ⟨hpm, hpi, hph⟩ := hpt' pt hp
  obtain ⟨φ, hφc, hφi, hφr, hφB, hφΓ⟩ := GlobalTheory.T.exists_adelic_unitary_complement_range_stabiliser _ _ _ hcm _ _ W.gram W'.gram B (coordTup W x) hMM hJ hJ' hB hBx hx0
  have hφx : ∀ g, φ g ∈ Hstab (AF D.host.F) D.sp.cm.sig W.gram (coordTup W x) := fun g => hφr ▸ ⟨g, rfl⟩
  have hφψ : ∀ g, ψ (φ g) = piEmb j (ψ' g) := fun g => funext fun ρ =>
    hAj ρ _ _ _ _ (infMat_fix (hθ ρ) (hφx g)) (infMat_frame (hθ ρ) (hφB g)) (hψA (φ g) ρ) (hψA' g ρ)
  obtain ⟨u, hu, hu1, hu2⟩ := GlobalTheory.T.exists_unfoldingKernel_levelSubgroup_bruhat_alt _ _ _ _ μ μ' _ _ _ _ hK hK' φ ψ ψ' (piEmb j) hψ.measurable hψ'.measurable hjm
    (fun g => GlobalTheory.T.latHat_stabiliser_iff_complement_frameRel hT _ _ _ hcm (unramified_host D) _ _ W.gram W'.gram B (coordTup W x) hMM hJ hJ' hB hBx hx0 L L'
      hLs β hβ hxL' hxx (fun y => by rw [hLc', ← SetLike.mem_coe, hLc]; exact hBL y) _ g (hφx g) (hφB g))
    hφψ hψm hψm' b hb hb1 (fun t => Φi (pt t)) (hΦ.comp hpm)
    (fun s t => congrArg Φi (hpi _ _ fun ρ => (hj ρ).inv_mul_fix (s ρ) (t ρ))) ν hν
  obtain ⟨hw1, hw2⟩ := rational_orbit D.sp.cm W x hx hβ0
  have : Countable (ratPts (AF D.host.F) D.sp.cm.sig W.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have : Countable (ratPts (AF D.host.F) D.sp.cm.sig W'.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  rw [← hu1]
  refine GlobalTheory.T.lintegral_tsum_orbit_unfold_alt _ _ _ {x' : W.V // W.hT x' x' = algebraMap _ _ β} μ μ' (ratPts _ _ _) (ratPts _ _ _) 𝓕 𝓕' h𝓕 h𝓕' φ
    hφc.measurable hφi hφΓ _ hφr
    (fun x' => ratTup (F := D.host.F) (AF D.host.F) (coordTup W x'.1)) hw1 hw2 u hu
    (phiLat (L0c D W) Φi) fun h => ?_
  · rw [hu2, hph h (ψ h) (hψA h)]
    refine congrArg (· * _) ?_
    have h1 := GlobalTheory.T.finPart_inv_smul_mem_latHat_iff_stab_mul_level hT _ _ _ hcm (unramified_host D) _ W.gram hJ L hLs β hβ (coordTup W x) hxL' hxx h
    have h2 : (L : Set _) = L0c D W := hLc
    rw [← h2]
    refine Set.indicator_eq_indicator (h1.trans ⟨?_, ?_⟩) rfl
    · rintro ⟨a, ha, h3⟩
      obtain ⟨g, rfl⟩ : a ∈ φ.range := hφr ▸ ha
      exact ⟨g, h3⟩
    · rintro ⟨g, h3⟩
      exact ⟨_, hφx g, h3⟩

theorem unfolding : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures → GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar →
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.Unfolding D := by
  intro _ _ hT D W P Q hs hPQ _ s hs1 x hx hxL W' ι hι hr hs' hPQ' hL
  cases s
  · have h1 : 1 ≤ Q := by simpa using hs1
    have := unfoldAt hT D W W' P Q P (Q - 1) (by omega) hs hPQ hs' hPQ' (-1) (Or.inr rfl) x
      (by rw [map_neg, map_one]; exact hx) hxL ι hι hr hL
    rwa [map_neg, map_one] at this
  · have h1 : 1 ≤ P := by simpa using hs1
    have := unfoldAt hT D W W' P Q (P - 1) Q (by omega) hs hPQ hs' hPQ' 1 (Or.inl rfl) x
      (by rw [map_one]; exact hx) hxL ι hι hr hL
    rwa [map_one] at this

end GlobalTheory.VolumeUnfolding
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizerStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryUnfolding_volume_vectorStabilizer : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures → GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar → GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.Unfolding D := by
  first | exact @GlobalTheory.VolumeUnfolding.unfolding | exact GlobalTheory.VolumeUnfolding.unfolding | (intros; apply GlobalTheory.VolumeUnfolding.unfolding <;> assumption)
end
