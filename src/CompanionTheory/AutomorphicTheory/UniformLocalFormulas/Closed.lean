module

public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformRestrictionOfEnergy
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibFibC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootMeasureIndependentOfChoicesStatement
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.RealObjInInfinityXJsz
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.ThmBFinal

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformRestrictionOfFiniteEnergy
section -- merged from CompanionTheory.AutomorphicTheory.UniformLocalFormulas.CovarianceFormula
section -- merged from CompanionTheory.AutomorphicTheory.UniformLocalFormulas.MeasConjM
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P WlocSk.NB
open scoped ENNReal Kronecker

noncomputable section

namespace Formalism.MainStatements.RowRest

variable {k r : ℕ}

def rowM (r : ℕ) (ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Matrix (CI k r) (CI k r) ℂ :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ νᵀ) 0 0 1)

theorem rowM_det (ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (rowM r ν).det = ν.det ^ r := by
  unfold rowM
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_kronecker]
  simp

theorem rowM_A (ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : CI k r → ℂ) (p : UP r) :
    (rowM r ν *ᵥ x) (Sum.inl p) = x (Sum.inl p) := by
  simp [rowM, Matrix.fromBlocks_mulVec]

theorem rowM_K (ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : CI k r → ℂ) (p : UP r) :
    (rowM r ν *ᵥ x) (Sum.inr (Sum.inr p)) = x (Sum.inr (Sum.inr p)) := by
  simp [rowM, Matrix.fromBlocks_mulVec]

theorem rowM_B (ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : CI k r → ℂ) (a : Fin r) (j : Fin (k + 1)) :
    (rowM r ν *ᵥ x) (Sum.inr (Sum.inl (a, j))) = ∑ c, x (Sum.inr (Sum.inl (a, c))) * ν c j := by
  simp only [rowM, Matrix.fromBlocks_mulVec, Sum.elim_inr, Sum.elim_inl, Matrix.zero_mulVec, zero_add, add_zero]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, mul_comm]

theorem rowM_mp {ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hν : Complex.normSq ν.det = 1) :
    MeasurePreserving (fun x : CI k r → ℂ => rowM r ν *ᵥ x) volume volume := by
  let L : (CI k r → ℂ) →ₗ[ℝ] (CI k r → ℂ) := (Matrix.toLin' (rowM r ν)).restrictScalars ℝ
  have hd : LinearMap.det L = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', rowM_det, Algebra.norm_complex_apply, map_pow, hν, one_pow]
  refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (CI k r → ℂ)) (f := L) (by rw [hd]; exact one_ne_zero)
  rw [hd] at this
  show Measure.map L volume = volume
  simpa using this

theorem meas_conjM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Measurable (conjM (k := k) (r := r) a) := by
  have : Continuous (conjM (k := k) (r := r) a) := by
    show Continuous fun x : Mt k r => (a * (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * a⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    exact (continuous_const.matrix_mul (continuous_id : Continuous fun x : Mt k r => x)).matrix_mul continuous_const
  exact this.measurable

theorem conj_uwb {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hρ : ρ ∈ B2.UWb k r) :
    (haarLie (Nset k r) 1).map (conjM ρ) = haarLie (Nset k r) 1 := by
  have hρ0 : ρ ∈ UWset k r 0 := ⟨hρ.1, hρ.2, by simp⟩
  obtain ⟨μ, hμ, rfl⟩ := (TwoByOneBlock.UWb_iff ρ).1 hρ
  have hνU : (μ⁻¹)ᴴ * Hb k * μ⁻¹ = Hb k := (TwoByOneBlock.UHb_inv hμ).2
  have hν : Complex.normSq (μ⁻¹).det = 1 := by
    have h := congrArg Matrix.det hνU
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
    have h0 : (Hb k).det ≠ 0 := TwoByOneBlock.Hb_unit.ne_zero
    have h2 : ((Complex.normSq (μ⁻¹).det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      refine mul_right_cancel₀ h0 ?_
      rw [RCLike.star_def] at h
      linear_combination h
    exact_mod_cast h2
  let Φ : (CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => phi0 t.1 t.2
  have hΦc : Continuous Φ := continuous_nilpotent_chart
  have hΦ : Measurable Φ := hΦc.measurable
  have hmp := (rowM_mp (r := r) hν).prod (MeasurePreserving.id (volume : Measure (Fin r → ℝ)))
  have key : conjM (B2.embWb k r μ) ∘ Φ = Φ ∘ Prod.map (fun x : CI k r → ℂ => rowM r μ⁻¹ *ᵥ x) id := by
    funext t
    set g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := phi0 t.1 t.2 with hg
    have hN : B2.embWb k r μ * g * (B2.embWb k r μ)⁻¹ ∈ Nset k r :=
      PI.QuotSetU.UnitaryGroupMassFormula.SW.uw_conj_N hρ0 (test_vector_mem_schwartz_bruhat t.1 t.2)
    show B2.embWb k r μ * g * (B2.embWb k r μ)⁻¹ = phi0 (rowM r μ⁻¹ *ᵥ t.1) t.2
    rw [← nilpotent_chart_left_inverse hN, TwoByOneBlock.emb_inv hμ]
    set g' := B2.embWb k r μ * g * B2.embWb k r μ⁻¹ with hg'
    have ho : ∀ i j, ¬ TwoByOneBlock.mid k r i → ¬ TwoByOneBlock.mid k r j → g' i j = g i j := fun i j hi hj => by
      rw [hg', TwoByOneBlock.mul_emb_out _ _ _ _ hj, TwoByOneBlock.emb_mul_out _ _ _ _ hi]
    have hm : mof g' = mof g := by
      have e1 : bF g' = bF g := by ext a b; exact ho _ _ (TwoByOneBlock.esI_out a) (TwoByOneBlock.esI_out b)
      have e2 : bC g' = bC g := by ext a b; exact ho _ _ (TwoByOneBlock.eI_out a) (TwoByOneBlock.esI_out b)
      unfold mof; rw [e1, e2]
    obtain ⟨p1, p2⟩ := nilpotent_chart_right_inverse t.1 t.2
    rw [← hg] at p1 p2
    congr 1
    · funext i
      rcases i with p | ⟨a, j⟩ | p
      · rw [rowM_A, ← p1]; exact ho _ _ (TwoByOneBlock.eI_out _) (TwoByOneBlock.eI_out _)
      · rw [rowM_B, ← p1]
        show g' (eI k r a) (wI k r j) = _
        rw [hg', TwoByOneBlock.mul_emb_mid]
        exact Finset.sum_congr rfl fun c _ => by rw [TwoByOneBlock.emb_mul_out _ _ _ _ (TwoByOneBlock.eI_out a)]; rfl
      · rw [rowM_K, ← p1]
        show kof g' _ _ = kof g _ _
        unfold kof; rw [hm]
    · rw [← p2]; unfold psiR; rw [hm]
  have hH : haarLie (Nset k r) 1 = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) •
      (volume : Measure ((CI k r → ℂ) × (Fin r → ℝ))).map Φ := Formalism.L2.SG.Pf.NcReal.JX.exponential_chart_haar k r
  rw [hH, Measure.map_smul _ (meas_conjM _).aemeasurable, Measure.map_map (meas_conjM _) hΦ, key, ← Measure.map_map hΦ hmp.measurable]
  exact congrArg (fun m => ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • Measure.map Φ m) hmp.map_eq

theorem aDil_e (t : ℝ) (a : Fin r) :
    B.aDil k r t *ᵥ bvec (eI k r a) = ((t : ℂ) ^ (r - a.val)) • bvec (eI k r a) := by
  unfold B.aDil bvec
  rw [Matrix.diagonal_mulVec_single, ← Pi.single_smul']
  have : (eI k r a).val < r := a.isLt
  rw [if_pos this]
  simp [eI]

theorem aDil_f (t : ℝ) (a : Fin r) :
    B.aDil k r t *ᵥ bvec (esI k r a) = ((t : ℂ) ^ (r - a.val))⁻¹ • bvec (esI k r a) := by
  unfold B.aDil bvec
  rw [Matrix.diagonal_mulVec_single, ← Pi.single_smul']
  have := a.isLt
  have h1 : ¬ (esI k r a).val < r := by simp only [esI]; omega
  have h2 : ¬ (esI k r a).val ≤ r + k := by simp only [esI]; omega
  have h3 : (esI k r a).val - (r + k) = r - a.val := by simp only [esI]; omega
  rw [if_neg h1, if_neg h2, h3]
  simp

theorem conj_levi {d : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hd : d ∈ UH (Hpk k r)) {t : ℝ} (ht : 0 < t)
    (he : ∀ a : Fin r, d *ᵥ bvec (eI k r a) = ((t : ℂ) ^ (r - a.val)) • bvec (eI k r a))
    (hf : ∀ a : Fin r, d *ᵥ bvec (esI k r a) = ((t : ℂ) ^ (r - a.val))⁻¹ • bvec (esI k r a)) :
    (haarLie (Nset k r) 1).map (conjM d) = ENNReal.ofReal ((t ^ B.kap k r)⁻¹) • haarLie (Nset k r) 1 := by
  have hG := unitary_group_closed k r
  have ha : B.aDil k r t ∈ B.GV k r := B4.aDil_mem k r t ht.ne'
  have htc : ∀ a : Fin r, ((t : ℂ) ^ (r - a.val)) ≠ 0 := fun a => pow_ne_zero _ (by exact_mod_cast ht.ne')
  have hi := B2x7.aDil_inv_mul k r t ht.ne'
  have hρ : (B.aDil k r t)⁻¹ * d ∈ B2.UWb k r := by
    refine ⟨hG.mul_mem _ (hG.inv_mem _ ha) _ hd, fun a => ⟨?_, ?_⟩⟩
    · rw [← Matrix.mulVec_mulVec, he, ← aDil_e, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
    · rw [← Matrix.mulVec_mulVec, hf, ← aDil_f, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  have e : conjM (k := k) (r := r) d = conjM (B.aDil k r t) ∘ conjM ((B.aDil k r t)⁻¹ * d) := by
    funext x
    show d * Matrix.of x * d⁻¹ =
      B.aDil k r t * ((B.aDil k r t)⁻¹ * d * Matrix.of x * ((B.aDil k r t)⁻¹ * d)⁻¹) * (B.aDil k r t)⁻¹
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hG.unit _ ha)]
    simp only [Matrix.mul_assoc]
    rw [B2x7.aDil_mul_inv k r t ht.ne', Matrix.mul_one, ← Matrix.mul_assoc (B.aDil k r t), B2x7.aDil_mul_inv k r t ht.ne',
      Matrix.one_mul]
  rw [e, ← Measure.map_map (meas_conjM _) (meas_conjM _), conj_uwb hρ]
  exact dilation_jacobian_unipotent k r _ (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _
    (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top)) t ht

end Formalism.MainStatements.RowRest
end
end

open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj.InfCut
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem place_eq {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (wf : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0)
    (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Q' : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (h2 : Q * Q' = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) {t : ℝ} (ht : 0 < t)
    (hc : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = (t : ℂ) ^ (r - (a : ℕ)) • e a ∧
      Q *ᵥ Pi.single (esI k r a) 1 = (star ((t : ℂ) ^ (r - (a : ℕ))))⁻¹ • f a) (κ : ℝ≥0∞) :
    (haarLie (Nset k r) κ).comap (fun γ : Formalism.REAL.UJ ε => (Matrix.of.symm (trG Q Q' γ) : Mt k r)) =
      (κ * ENNReal.ofReal ((t ^ B.kap k r)⁻¹)) • refNg hn ε e f wf (z0v T z) := by
  subst hn
  have hF := JX.isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hF
  have emb' : MeasurableEmbedding (cM (ε := ε) Q' Q) := cM_measEmb (A' := Q) (B' := Q') h2 h2
  set P := Qm e f wf (z0v T z) with hP
  set P' := Qi ε e f wf (z0v T z) with hP'
  have p1 : P' * P = 1 := Qi_mul_Qm hF
  have p2 : P * P' = 1 := Qm_mul_Qi hF
  have hdi : (P' * Q)⁻¹ = Q' * P := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, h2, Matrix.one_mul, p1]
  have hd : P' * Q ∈ UH (Hpk k r) := by
    show (P' * Q)ᴴ * Hpk k r * (P' * Q) = Hpk k r
    calc _ = Qᴴ * (P'ᴴ * Hpk k r * P') * Q := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [QiHQi hF, hg]
  have hmap := conj_levi hd ht
    (fun a => by
      show (P' * Q) *ᵥ Pi.single _ 1 = _
      rw [← Matrix.mulVec_mulVec, (hc a).1, Matrix.mulVec_smul, ← Qm_e (e := e) (f := f) (wf := wf) (z0 := z0v T z) a,
        Matrix.mulVec_mulVec, p1, Matrix.one_mulVec])
    (fun a => by
      show (P' * Q) *ᵥ Pi.single _ 1 = _
      rw [← Matrix.mulVec_mulVec, (hc a).2, Matrix.mulVec_smul, ← Qm_f (e := e) (f := f) (wf := wf) (z0 := z0v T z) a,
        Matrix.mulVec_mulVec, p1, Matrix.one_mulVec]
      simp)
  have hcomp : cM (ε := ε) P' P = conjM (P' * Q) ∘ cM (ε := ε) Q' Q := by
    funext g
    show P' * uMat g * P = P' * Q * (Q' * uMat g * Q) * (P' * Q)⁻¹
    rw [hdi]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q' P, h2, Matrix.one_mul, ← Matrix.mul_assoc Q Q', h2, Matrix.one_mul]
  have hu : IsUnit (P' * Q).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hd
  have hinj : Function.Injective (conjM (k := k) (r := r) (P' * Q)) := fun x y h => by
    have h' : P' * Q * Matrix.of x * (P' * Q)⁻¹ = P' * Q * Matrix.of y * (P' * Q)⁻¹ := h
    have := congrArg (fun m => (P' * Q)⁻¹ * m * (P' * Q)) h'
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] at this
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one] at this
    exact this
  have hκ : haarLie (Nset k r) κ = κ • haarLie (Nset k r) 1 := by simp [haarLie]
  ext s hs
  show (haarLie (Nset k r) κ).comap (cM (ε := ε) Q' Q) s =
    ((κ * ENNReal.ofReal ((t ^ B.kap k r)⁻¹)) • (haarLie (Nset k r) 1).comap (cM (ε := ε) P' P)) s
  rw [emb'.comap_apply, Measure.smul_apply, emb.comap_apply, hκ, Measure.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  congr 1
  have h3 := congrArg (fun m : Measure (Mt k r) => m (cM (ε := ε) P' P '' s)) hmap
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  rw [← h3, Measure.map_apply (meas_conjM _) (emb.measurableSet_image.2 hs), hcomp, Set.image_comp,
    Set.preimage_image_eq _ hinj]

theorem pi_smul {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    Measure.pi (fun i => c • μ i) = c ^ Fintype.card ι • Measure.pi μ := by
  lift c to ℝ≥0 using hc
  have : ∀ i, SigmaFinite ((c : ℝ≥0∞) • μ i) := fun i => inferInstanceAs (SigmaFinite (c • μ i))
  refine Measure.pi_eq fun s _ => ?_
  simp [Measure.pi_pi, Finset.prod_mul_distrib]

theorem kap_real (k r : ℕ) :
    (B.kap k r : ℝ) = (4 * (r : ℝ) ^ 3 + 6 * (r : ℝ) ^ 2 + 2 * r) / 3 + k * ((r : ℝ) ^ 2 + r) := by
  have hs : B.kap k r = ∑ j ∈ Finset.range r, 2 * (2 * (j + 1) + k) * (j + 1) := by
    unfold B.kap Mdim
    rw [Fin.sum_univ_eq_sum_range (fun a => 2 * (2 * (r - a) + k + 1 - 1) * (r - a)) r, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    rw [show r - (r - 1 - j) = j + 1 by omega]
    rfl
  rw [hs]
  clear hs
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Nat.cast_add, ih]; push_cast; ring

def iF {D : D7} (X : HidaSetting D) : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective
    ((X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F (fun a => (X.ιE_F _).2 ⟨a, rfl⟩))
    ⟨fun a b h => by
      have h' := congrArg Subtype.val h
      simp only [RingHom.codRestrict_apply, RingHom.coe_comp, Function.comp_apply] at h'
      exact (algebraMap X.B.I.F X.B.I.E).injective (X.ιE.injective h'),
     fun y => by
      obtain ⟨a, ha⟩ := (X.ιE_F y.1).1 y.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring_nf

theorem disc_rd (D : D7) (X : HidaSetting D) : |((NumberField.discr X.B.I.F : ℤ) : ℝ)| = D.host.rdE ^ D.R.f := by
  refine Formalism.L2.SG.Pf.Carrier.EnergyMS.discRd_of (fun D X => ?_) finrank_E D X
  have hE : NumberField.discr X.B.I.E = NumberField.discr D.host.E :=
    NumberField.discr_eq_discr_of_ringEquiv X.B.I.E X.ιE
  have hF : NumberField.discr X.B.I.F = NumberField.discr D.host.F :=
    NumberField.discr_eq_discr_of_ringEquiv X.B.I.F (iF X)
  rw [hE, hF, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq]
  push_cast
  rw [abs_pow]

theorem covariance_formula : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := by
  intro D X Y θ C u hθ
  set ρ : ℝ := 2 * D.host.v with hρ
  have hρ1 : 1 ≤ ρ := Formalism.L2.SG.Pf.LoopBCovN.rdE_ge_one D
  have hρ0 : 0 < ρ := by linarith
  have hrd : D.host.rdE = ρ := by rw [hρ]; unfold Formalism.BasicNotions.Host.v; ring
  have hfr : frS D = ((ρ⁻¹ : ℝ) : ℂ) := by
    unfold frS Formalism.BasicNotions.Host.ka
    congr 1
    have hv : D.host.v ≠ 0 := by intro h; rw [hρ, h] at hρ0; simp at hρ0
    rw [hρ]
    field_simp
  set c : ℝ≥0∞ := Formalism.MainNotions.S.kapN D θ * ENNReal.ofReal (((ρ⁻¹) ^ B.kap D.R.k D.R.rS)⁻¹) with hcdef
  have hloc : ∀ (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F), vOf X τ = v →
      Formalism.L2.SG.Pf.AmpWinLoc.muNl C τ v = c • refNX X u v := by
    rintro τ v rfl
    obtain ⟨-, h2, hg, hcol⟩ := C.isT τ
    rw [hfr] at hcol
    exact place_eq (nX X) _ (eV X _) (ProductExactness.pV X _) (X.wfr u _) (ProductExactness.zV X u _) (ProductExactness.Tw_pos u) (fX_ee X _) (fX_ff X _)
      (fX_ef X _) (fX_ww X u _) (fX_ew X u _) (fX_fw X u _) (fX_ez X u _) (fX_fz X u _) (frame_real_z_z_eq_neg X u _) (fX_zw X u _)
      (C.Q τ) (C.Qi τ) h2 hg (inv_pos.2 hρ0) (fun a => hcol a a rfl) _
  have hv : Formalism.L2.SG.Pf.AmpWinGlob.muNv C = fun v => c • refNX X u v :=
    funext fun v => hloc (X.pl v) v (X.pl.symm_apply_apply v)
  have hsf : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muNv C v) := fun v => by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w →
        SigmaFinite (Formalism.L2.SG.Pf.AmpWinLoc.muNl C τ w) := by
      rintro τ w rfl
      exact Formalism.L2.SG.Pf.AmpWinLoc.sf_muNl C τ hθ
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  have : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
      (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X u v)).1
  obtain ⟨hemb, hmapT⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C hsf hθ
  have hcov : Formalism.L2.SG.LoopTerm.dnB D θ (Formalism.L2.SG.LoopTerm.trInf C '' Y.FN u) =
      Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C) (Y.FN u) := by
    rw [← hmapT, hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  have hce : c = ENNReal.ofReal (ρ ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * ρ ^ (B.kap D.R.k D.R.rS : ℝ)) := by
    rw [hcdef, inv_pow, inv_inv, Real.rpow_natCast, ENNReal.ofReal_mul (by positivity)]
    rfl
  have href := covol_refN (covolN_of_coordCovol (coordCovol_of kapLaw_holds NOf.nofib_holds CovB.blockCovol_holds))
    refNBox_holds X u u (Y.FN u) (Y.FN_fund u)
  have hcard : Fintype.card (InfinitePlace X.B.I.F) = Fintype.card D.what₂.Tau := Fintype.card_congr X.pl
  have hf : D.R.f = Fintype.card D.what₂.Tau := D.what₂.card_Tau.symm
  unfold Formalism.L2.SG.LoopTerm.covN
  rw [hcov, hv, pi_smul _ (by rw [hce]; exact ENNReal.ofReal_ne_top), Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    href, disc_rd D X, hrd, hf, hcard, hce, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ← Real.rpow_natCast ρ, ← Real.rpow_mul hρ0.le, mul_comm ((Fintype.card D.what₂.Tau : ℕ) : ℝ), Real.rpow_mul hρ0.le,
    Real.rpow_natCast (ρ ^ Formalism.L2.SG.Pf.LsNc5.covolumeExponent D.R.rS D.R.k), ← mul_pow]
  congr 1
  have e : Formalism.L2.SG.Pf.LoopBCovN.eN D = -((D.R.rS : ℝ) * D.R.k) + (B.kap D.R.k D.R.rS : ℝ) +
      Formalism.L2.SG.Pf.LsNc5.covolumeExponent D.R.rS D.R.k := by
    rw [kap_real]
    unfold Formalism.L2.SG.Pf.LoopBCovN.eN Formalism.L2.SG.Pf.LsNc5.covolumeExponent
    ring
  rw [e, Real.rpow_add hρ0, Real.rpow_add hρ0]
  ring

end Formalism.MainStatements.RowRest
end
end

section -- merged from CompanionTheory.AutomorphicTheory.UniformLocalFormulas.RankOneTermInvariant
noncomputable section

open scoped Classical ENNReal InnerProductSpace
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.RealObj Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocJEq Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.RealConjugatorData

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ka_pos (D : D7) : 0 < D.host.ka := by
  have := rdE_pos D
  unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
  positivity

variable {D : D7} {X : HidaSetting D}

theorem upd_mem (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) {s : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ JointQuot.NV X u v) :
    Function.update (1 : X.B.I.Ginf) v s ∈ X.NinfU u := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [Function.update_self]
    exact hs
  · rw [Function.update_of_ne hw]
    have h1 : uMat ((1 : X.B.I.Ginf) w) = 1 := rfl
    rw [h1]
    refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> simp

theorem wloc_N (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) {s : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ JointQuot.NV X u v)
    (a : Formalism.REAL.UJ (X.B.I.ε v)) :
    X.Wloc u v (s * a) = JointQuot.psiU X u (Function.update 1 v s) • X.Wloc u v a := by
  obtain ⟨x0, hx0⟩ := EnergyPfLoc.wu_ne X u
  set S : X.B.I.Ginf := Function.update 1 v s with hSdef
  have hS : S ∈ X.NinfU u := upd_mem u v hs
  have hmul : S * Function.update x0 v a = Function.update x0 v (s * a) := by
    funext w
    by_cases hw : w = v
    · subst hw
      simp [S]
    · simp [S, Function.update_of_ne hw]
  have hW : X.Wu u (S * Function.update x0 v a) = JointQuot.psiU X u S • X.Wu u (Function.update x0 v a) := by
    rw [(X.Wu_spec u).1 S (fun v => (hS v).1) _, (X.piU_rep u).2.2.2.1 S hS]
    rfl
  have hK : (∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ) ≠ 0 := by
    have h0 := EnergyPfLoc.inner_upd X u v x0 (x0 v) (x0 v)
    rw [Function.update_eq_self] at h0
    have hne : ⟪X.Wu u x0, X.Wu u x0⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx0
    rw [h0] at hne
    exact right_ne_zero_of_mul hne
  have key : ∀ b, ⟪X.Wloc u v b, X.Wloc u v (s * a) - JointQuot.psiU X u S • X.Wloc u v a⟫_ℂ = 0 := by
    intro b
    have h1 := EnergyPfLoc.inner_upd X u v x0 b (s * a)
    rw [← hmul, hW, inner_smul_right, EnergyPfLoc.inner_upd, ← mul_assoc] at h1
    rw [inner_sub_right, inner_smul_right, mul_right_cancel₀ hK h1, sub_self]
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
  nth_rewrite 1 [inner_sub_left]
  rw [inner_smul_left, key, key, mul_zero, sub_zero]

theorem rank_one_term_invariant (u u' : D.what₂.Word) {w : Point D.host.E (D.R.rS + 1)} (hw : JointQuot.OkPt X u u' w)
    (v : InfinitePlace X.B.I.F) {s : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ JointQuot.StV X u u' (gamW X u u' w) v)
    (z : Formalism.REAL.UJ (X.B.I.ε v)) :
    TermOp.rk1 (X.Wloc u v (s * z)) (X.Wloc u' v ((gamW X u u' w v)⁻¹ * (s * z))) =
      TermOp.rk1 (X.Wloc u v z) (X.Wloc u' v ((gamW X u u' w v)⁻¹ * z)) := by
  set γ := gamW X u u' w with hγ
  have he : (γ v)⁻¹ * (s * z) = ((γ v)⁻¹ * s * γ v) * ((γ v)⁻¹ * z) := by group
  have hc : γ⁻¹ * Function.update (1 : X.B.I.Ginf) v s * γ = Function.update (1 : X.B.I.Ginf) v ((γ v)⁻¹ * s * γ v) := by
    funext x
    by_cases hx : x = v
    · subst hx
      simp
    · simp [Function.update_of_ne hx]
  have hrel := JointQuot.stRel_holds X u u' w hw (Function.update 1 v s)
    ⟨upd_mem u v hs.1, by rw [hc]; exact upd_mem u' v hs.2⟩
  rw [hc] at hrel
  rw [he, wloc_N u v hs.1, wloc_N u' v hs.2, JointQuot.rankOneInnerOperator_smul_smul_eq_mul_conj_smul, hrel, one_smul]

variable {θ : ℝ} (C : Choice X θ)

theorem cMr_smap (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (s z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (Matrix.of (cMr C γ τ s) * Matrix.of (Smap C τ (γ (vOf X τ)) z) : MatKR D.R.k D.R.rS) =
      Matrix.of (Smap C τ (γ (vOf X τ)) (s * z)) := by
  rw [smap_val, smap_val]
  show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * (uMat (γ (vOf X τ)) * C.Q τ) *
      (C.Qi τ * (uMat (γ (vOf X τ))⁻¹ * uMat z) * C.Q τ * (C.y τ)⁻¹) =
    C.Qi τ * (uMat (γ (vOf X τ))⁻¹ * (uMat s * uMat z)) * C.Q τ * (C.y τ)⁻¹
  rw [uMat_inv']
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), (C.isT τ).2.1, Matrix.one_mul, ← Matrix.mul_assoc (uMat (γ (vOf X τ))) (uMat (γ (vOf X τ)))⁻¹, RealConjugatorData.uMat_mul_inv, Matrix.one_mul]

theorem map_smap (τ : D.what₂.Tau) (g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (Smap C τ g) = muGB X (C.Q τ) (C.Qi τ) τ := by
  have : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  set y' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := ujOf' _ (y_facts C τ).1 with hy'
  have e : Smap C τ g = (fun γ => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) γ)) ∘ (fun x => x * y') ∘ fun x => g⁻¹ * x := by
    funext z
    show Matrix.of.symm (C.Qi τ * umat (g⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) =
      Matrix.of.symm (C.Qi τ * (umat (g⁻¹ * z) * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)) * C.Q τ)
    congr 1
    simp only [Matrix.mul_assoc]
    rw [(C.isT τ).1, Matrix.mul_one]
  have hm : Measurable fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) γ) := by
    refine Continuous.measurable ?_
    unfold trG
    exact (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul continuous_const
  rw [e, ← Measure.map_map hm ((measurable_mul_const _).comp (measurable_const_mul _)),
    ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self, map_mul_right_eq_self]
  rfl

theorem quot_push (γ : X.B.I.Ginf) (τ : D.what₂.Tau) {μR ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))}
    (h : IsQuotLoc μR ν) :
    IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μR.map (cMr C γ τ)) (ν.map (Smap C τ (γ (vOf X τ)))) := by
  intro f hf
  have he := smap_measEmb C τ (γ (vOf X τ))
  rw [← map_smap C τ (γ (vOf X τ)), he.lintegral_map, he.lintegral_map]
  refine (h _ (hf.comp he.measurable)).trans (lintegral_congr fun x => ?_)
  rw [(cMr_measEmb C γ τ).lintegral_map]
  refine lintegral_congr fun s => ?_
  exact congrArg f (cMr_smap C γ τ s x).symm

theorem mem_range (τ : D.what₂.Tau) (g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) {x : MatKR D.R.k D.R.rS}
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : x ∈ Set.range (Smap C τ g) := by
  rw [range_smap]
  have h1 := transp_mem C τ ((Formalism.FourierDecayAlt.P.unitary_group_closed D.R.k D.R.rS).mul_mem _ hx _ (C.y_mem τ))
  have e : C.Q τ * Matrix.of x * C.y τ * C.Qi τ = C.Q τ * (x * C.y τ) * C.Qi τ := by
    rw [← Matrix.mul_assoc]; rfl
  show umat g * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset _
  rw [e]
  exact (g * ujOf' _ h1).2

theorem root_push (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, IsPtRep X u u' w g) (τ : D.what₂.Tau)
    {μR : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))}
    (hc : μR (JointQuot.StV X u u' (gamW X u u' w) (vOf X τ))ᶜ = 0)
    (hp : μR.map (JointQuot.stCoordV X u' w (gamW X u u' w) (vOf X τ)) = JointQuot.muStabV X w) :
    IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (ptLoc D τ w) (JointAmplitudePoints.gamP C u u' w τ)
      (μR.map (cMr C (gamW X u u' w) τ)) := by
  set γ := gamW X u u' w with hγ
  have hemb := cMr_measEmb C γ τ
  have hN1 : (1 : MatKR D.R.k D.R.rS) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS :=
    (Formalism.FourierDecayAlt.P.unipotent_radical_closed D.R.k D.R.rS).one_mem
  have hid : (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = id := by
    funext x i j
    simp
  refine ⟨1, hN1, 1, hN1, JointAmplitudePoints.gamP C u u' w τ, by simp, RelPtR.zhatO_gamP C u u' w hw τ, μR.map (cMr C γ τ), ?_, ?_,
    by rw [hid, Measure.map_id]⟩
  · rw [hemb.map_apply]
    apply measure_mono_null _ hc
    intro y hy
    change y ∉ JointQuot.StV X u u' γ (vOf X τ)
    intro hyS
    exact hy ((stV_iff C γ τ u u' y).1 hyS)
  · have hcomp : rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ cMr C γ τ =
        (fun (y : FreeE w → ℂ) i => (1 : ℂ) * y (RootPatterns.idxF τ w i)) ∘ JointQuot.stCoordV X u' w γ (vOf X τ) := by
      funext y i
      have h := congrFun (congrFun (RootPatterns.stCoordV_comp C u' w γ τ) y) (RootPatterns.idxF τ w i)
      simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply] at h
      simp only [Function.comp_apply, one_mul]
      exact h.symm
    have hst : Measurable (JointQuot.stCoordV X u' w γ (vOf X τ)) := by
      refine Continuous.measurable ?_
      unfold JointQuot.stCoordV hJ
      fun_prop
    have hGm : Measurable fun (y : FreeE w → ℂ) (i : ↥(rootPat (ptLoc D τ w))) => (1 : ℂ) * y (RootPatterns.idxF τ w i) :=
      Measurable.of_eval fun q => measurable_const.mul (measurable_pi_apply _)
    rw [Measure.map_map (RootPatterns.rootCoords_cont _ _ _ _).measurable hemb.measurable, hcomp,
      ← Measure.map_map hGm hst, hp]
    unfold JointQuot.muStabV
    rw [PiMeasureScaling.pi_reindex_scale (RootPatterns.idxF τ w) _ ENNReal.ofReal_ne_top (fun _ => (1 : ℂ)) fun _ => one_ne_zero]
    congr 1
    have hka : 0 < D.host.ka := ka_pos D
    have hg : (X.B.g : ℝ) = gg D := by rw [X.g_eq, gg]; push_cast; rfl
    have hg0 : 0 < gg D := by
      have a := (D.host.g_prime 0).pos
      have b := (D.host.g_prime 1).pos
      unfold gg
      positivity
    have e : 2 * D.host.ka / gg D / (2 * Real.pi) = D.host.ka / gg D / Real.pi := by field_simp
    rw [hg, e, ENNReal.ofReal_pow (by positivity)]
    simp

theorem use₇ (hB : WuBessel C) (u u' : D.what₂.Word)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hP : ∀ w, JointQuot.OkPt X u u' w → JointQuot.LocPin X u u' w νl) : LocNorm.LocUniqP u u' C hB νl := by
  intro w hb hw τ
  have hok : JointQuot.OkPt X u u' w := ⟨hw, OOCoreHilbertSchmidt.gxPos_holds u u' w hb hw⟩
  obtain ⟨μR, hH, hQ, hp⟩ := hP w hok (vOf X τ)
  set γ := gamW X u u' w with hγ
  obtain ⟨hz, hT⟩ := zTr C u τ
  obtain ⟨hz', hT'⟩ := zTr C u' τ
  have hTu : ∀ u0 : D.what₂.Word, 0 < Tr D u0 := fun u0 => Nat.cast_pos.2 (D.mem u0).A.T_prime.pos
  have hg : JointAmplitudePoints.gamP C u u' w τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _
  have hex : ∃ ν, RMeas D (locW C u u' τ) (JointAmplitudePoints.gamP C u u' w τ) 1 ν :=
    RMeasP.rMeas_exact D (locW C u u' τ) hz (hT.symm ▸ hTu u) hz' (hT'.symm ▸ hTu u') (haarTr C τ) (ptLoc D τ w) _ hg
      (RelPtR.zhatO_gamP C u u' w hw τ)
  have h1 : RMeas D (locW C u u' τ) (JointAmplitudePoints.gamP C u u' w τ) 1 (JointAmplitudePoints.nu1P C u u' w τ) := by
    unfold JointAmplitudePoints.nu1P
    rw [dite_eq_left hex]
    exact hex.choose_spec
  obtain ⟨p, μ₁, hr1, hq1⟩ := h1
  rw [ENNReal.ofReal_one, one_smul] at hq1
  have hG : Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (JointAmplitudePoints.gamP C u u' w τ) ≠ 0 := by
    rw [RelPtR.gf_gamP C u u' w hw τ]
    exact (hb.2 τ).ne'
  obtain ⟨-, hμ, hHaar⟩ := GlobalTheory.T.besselRootMeasure_independent_of_choices D _ _ _ _ _ _ _ hz hz' (hT.symm ▸ hTu u) (hT'.symm ▸ hTu u') hg hG
    (ka_pos D) hr1 (root_push C u u' w hw τ hH.2.2.1 hp)
  have hq2 := quot_push C γ τ hQ
  rw [← hμ] at hq2
  obtain ⟨hcl, hun⟩ := GlobalTheory.T.unipotentRadical_inter_conjugate_closed_unimodular D.R.k D.R.rS _ hg
  have := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ))
  set F : MatKR D.R.k D.R.rS → (X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)) := fun x =>
    (innerSL ℂ ((locS hB u u' τ).Φ' x)).smulRight ((locS hB u u' τ).Φ (JointAmplitudePoints.gamP C u u' w τ * x)) with hF
  have hFS : ∀ z, F (Smap C τ (γ (vOf X τ)) z) = sclOf hB u u' τ •
      TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) ((γ (vOf X τ))⁻¹ * z)) :=
    fun z => integrand_S C hB u u' τ (γ (vOf X τ)) z
  have hFc : ContinuousOn F (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) := by
    refine ContinuousOn.mono (s := Set.range (Smap C τ (γ (vOf X τ)))) ?_ fun x hx => mem_range C τ _ hx
    refine continuousOn_iff_continuous_restrict.2 ?_
    have hemb : Continuous fun z => F (Smap C τ (γ (vOf X τ)) z) := by
      rw [funext hFS]
      exact (rank_one_continuous (X.Wloc_cont u (vOf X τ))
        ((X.Wloc_cont u' (vOf X τ)).comp (continuous_const.mul continuous_id))).const_smul (sclOf hB u u' τ)
    refine (hemb.comp (smapInv_cont C τ (γ (vOf X τ)))).congr ?_
    rintro ⟨_, z, rfl⟩
    have : smapInv C τ (γ (vOf X τ)) ⟨_, z, rfl⟩ = z := by
      apply Subtype.ext
      apply Units.ext
      show umat (γ (vOf X τ)) * (C.Q τ * Matrix.of (Smap C τ (γ (vOf X τ)) z) * C.y τ * C.Qi τ) = umat z
      rw [smap_val, back_smap]
    simp only [Function.comp_apply, this]
    rfl
  have hFi : ∀ ρ ∈ Rset D.R.k D.R.rS (JointAmplitudePoints.gamP C u u' w τ), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      F (ρ * x) = F x := by
    intro ρ hρ x hx
    obtain ⟨z, rfl⟩ := mem_range C τ (γ (vOf X τ)) hx
    obtain ⟨s, rfl⟩ := rset_range C γ τ ρ hρ
    have hs := (stV_iff C γ τ u u' s).2 hρ
    have e := cMr_smap C γ τ s z
    refine (congrArg F e).trans ?_
    refine (hFS (s * z)).trans ?_
    rw [rank_one_term_invariant u u' hok _ hs z]
    exact (hFS z).symm
  have hI := (GlobalTheory.T.integral_eq_of_quotientMeasures_besselUnitary D.R.k D.R.rS _ _ _ _ _ hcl (haarTr C τ) hHaar (hun _ hHaar) hq1 hq2 _ F hFc hFi).2
  exact congrArg (fun A => hsNormSq (((cOf hB u τ : ℝ) : ℂ)⁻¹ • A)) hI

end Formalism.MainStatements.RowRest
end
end

namespace Formalism.MainStatements.RowRest

theorem uniqOfPin : UniqOfPin := fun _ _ _ _ C hB u u' νl hP => use₇ C hB u u' νl hP

theorem uniform_restriction_of_finite_energy (hE : EnergyFin) : Formalism.L2.SG.Pf.ThmBChain6.AmplitudeBoundsAllChoicesUniform :=
  uniform_restriction_of_energy covariance_formula uniqOfPin hE

end Formalism.MainStatements.RowRest
end

section -- merged from CompanionTheory.AutomorphicTheory.UniformLocalFormulas.StepThmBPinnedCOfN
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.BDat Formalism.L2.SG.ThmBUseR
  Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BDatR Formalism.L2.SG.Pf.GoodS Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev AN {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (dg : D.what₂.Tau → ℝ) :
    ∀ τ, LocS (WX C u u' τ) := fun τ => { locS hB u u' τ with deg := dg τ }

theorem goodW_all {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    GoodW D τ u u' θ (WX C u u' τ) :=
  goodW_of C u u' τ (colsTypeTr C u τ) (colsTypeTr C u' τ) (zTr C u τ) (zTr C u' τ) (haarTr C τ)

theorem goodS_deg {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hLF : LocFactor C) (hB : WuBessel C) (u u' : D.what₂.Word)
    (τ : D.what₂.Tau) : ∃ d : ℝ, GoodS D (lamD D τ) (AN hB u u' (fun _ => d) τ) := by
  have hsm := WuDec.lowSmoothSK (dsTr C τ) (isLowUnitH_base_vector C τ)
  have hLu := l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ
  have hLu' := l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u' τ
  set v := vOf X τ
  have hd : (0 : ℝ) < Module.finrank ℂ (X.Vloc u v) := by exact_mod_cast finrank_pos u v
  have hd' : (0 : ℝ) < Module.finrank ℂ (X.Vloc u' v) := by exact_mod_cast finrank_pos u' v
  have hL : 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := ENNReal.toReal_pos hLu.1 hLu.2.ne
  have hL' : 0 < (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal := ENNReal.toReal_pos hLu'.1 hLu'.2.ne
  have hc : 0 < cOf hB u τ := div_pos hL hd
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
  have hε : ∀ i, epsSH D.R i = X.B.I.ε v (Fin.cast (Choice.n_eq' X).symm i) := fun i => by
    rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl)
  have hF := Choice.fdegHpk_tr (Choice.n_eq' X) (X.B.I.ε v) (epsSH D.R) hε (X.B.σ v) (X.ds v).2.2.1
    (Formalism.L2.SG.Pf.RowDictPf.fdeg_of_schur X Formalism.L2.SG.Pf.RowDictPf.schur_orthogonality_discrete_series v)
    (C.Q τ) (C.Qi τ) (C.isT τ).2.1 (C.isT τ).2.2.1 P hP
  have hF2 := Formalism.L2.SG.Pf.RowDictPf.isFdeg_smul (D.s.cdScale_pos _ (epsSH D.R)) hF
  refine ⟨_, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, Formalism.L2.SG.Pf.dsTr C τ, (hB u τ).choose_spec.1,
    isBesselMapSm_smul _ (hB u' τ).choose_spec.1, hsm, v0_ne C τ, C.y_low τ, hc, ?_, ?_, P, hP.1, hF2⟩
  · show l2SG (C.nuS u τ) (phiOf hB u τ) = ENNReal.ofReal (cOf hB u τ * Module.finrank ℂ (X.Vloc u v))
    rw [Formalism.L2.SG.LocWSOf.cOf, div_mul_cancel₀ _ hd.ne', ENNReal.ofReal_toReal hLu.2.ne]
  · show l2SG (C.nuS u' τ) (fun m => sclOf hB u u' τ • phiOf hB u' τ m) =
      ENNReal.ofReal (cOf hB u τ * Module.finrank ℂ (X.Vloc u' v))
    rw [l2SG_const_smul, sclOf]
    set a := cOf hB u τ * (Module.finrank ℂ (X.Vloc u' v) : ℝ) / (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal
      with ha
    have ha0 : 0 ≤ a := div_nonneg (mul_nonneg hc.le hd'.le) hL'.le
    have hnorm : (‖((Real.sqrt a : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal a := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ha0]
    rw [hnorm, ← ENNReal.ofReal_toReal hLu'.2.ne, ← ENNReal.ofReal_mul ha0, ha, div_mul_cancel₀ _ hL'.ne']

theorem ties_coreN {τ₀ Rw I₀ H H₁ : Type} [Fintype I₀] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (XT : Formalism.FourierDecayAlt.PB.Terms τ₀ Rw I₀ H H₁)
    {Cl' Nu : Type} (N : Formalism.FourierDecayAlt.PN.NGData τ₀ D.host.E D.R.rS Cl' Nu)
    {large₂ : SizeData₂ D} {X : HidaSetting D} (u u' : D.what₂.Word)
    {C' Cl Cg cb Cw cT CT C0 C1 Ca Ch Cs Cβ Cb Cn Ire : ℝ} (A : ℕ)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0) (hTT : HypTT D u u') (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (hAmp : Formalism.MainNotions.S.Bridge.AmpIsBessel D large₂ C' Cl Cg cb Cw cT CT C0 0 C1 Ca)
    (hStd : Formalism.MainNotions.S.Bridge.StdOfHyp D large₂ C' Cl Cg cb Cw cT CT C0 Ch Cs Cs Cβ)
    (hTF : Formalism.MainNotions.TFrameOfHyp D large₂ C' Cl Cg cb Cw cT CT C0)
    (hpt : Formalism.L2.SG.ThmBUse.PtTie XT N (D.mem u).A.T (D.mem u').A.T)
    (hwt : Formalism.L2.SG.ThmBUse.WtTie XT N (D.mem u).A.T (D.mem u').A.T A 1)
    (hIre : 0 ≤ Ire) {θ : ℝ} (Cc : Choice X θ) (hBs : WuBessel Cc) (hθ0 : 0 < θ) (hθw : normWin D large₂ C1 θ)
    (dg : D.what₂.Tau → ℝ) (hAg : ∀ τ, GoodS D (lamD D τ) (AN hBs u u' dg τ))
    {Cfac : ℝ} (hCfac : 0 ≤ Cfac)
    (hJF : JointAmplitudeFactorizationRotated XT N large₂ C1 (WX Cc u u') (AX hBs u u') (D.mem u).A.T (D.mem u').A.T Cfac)
    (hNF : ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
        (∀ τ, IsSection D.R.k D.R.rS (WX Cc u u' τ).z (WX Cc u u' τ).z' (sec τ)) →
        ENNReal.ofReal Cfac * ∏ τ, MMv D u u' (AX hBs u u' τ) (sec τ) ≤
          ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire))
    (hCs : 0 ≤ Cs) (hka : 0 < Formalism.MainNotions.S.Bridge.kaS D) (hβ : 0 ≤ Cβ) :
    TiesR XT N Ch Cs (D.mem u).A.T (D.mem u').A.T (large₂.sc.b ^ Cβ) A Cb
      (Real.exp ((max 0 Cb * Cβ + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire) := by
  have hWg : ∀ τ, GoodW D τ u u' θ (WX Cc u u' τ) := fun τ =>
    goodW_all Cc u u' τ
  have hv : 0 < D.host.v := by
    unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
    have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
    linarith
  have hS := hStd hH
  have hF := hTF hH
  let I : AmpIn large₂ C1 Ca u u' θ hT hT' := ampInOf hAmp hH hTT hθw hT hT' (WX Cc u u') (AN hBs u u' dg) hWg hAg
  have hok : ∀ τ, LocOk D Ch Cs (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) (large₂.sc.b ^ Cβ) (kaRe D) := fun τ =>
    locOk_locB D τ u u' θ (WX Cc u u' τ) (AN hBs u u' dg τ) (hWg τ) (hAg τ) hT hT' hka hv hθ0 (hS τ u u').1 (hF u) (hF u')
  have hCj : 0 ≤ Cfac * ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) :=
    mul_nonneg hCfac (Finset.prod_nonneg fun τ _ => mul_nonneg (I.hK τ).le
      (Real.rpow_nonneg (by unfold Scale.b; positivity) _))
  exact ⟨bdOf I.toInputs hok, 1, _, zero_le_one, hCj,
    gaps_bdOf I.toInputs hok (fun τ => (hS τ u u').2) hCs le_rfl, hpt, hwt,
    jointAmplitude_bound_rotated XT N I hok hka hCfac hJF,
    normTie_bdOf I hok hCfac hIre hβ (hNF I.sec I.sec_spec)⟩

def RowDataN (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∃ dg : D.what₂.Tau → ℝ, ∀ τ, GoodS D (lamD D τ) (AN hB u u' dg τ)) ∧
    JointAmplitudePoints.RMeasExP u u' C ∧ JointAmplitudePoints.LocalAmplitudesPositive Y u u' ν C hB ∧ JointAmplitudePoints.ThetaWinP Y u u' ν C hB large₂ C1 ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

def RowDataUnifN : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → RowDataN large₂ Y u u' ν C1 Cn Ire

theorem rowDataUnifN_of_6 (hBW : BesselOfW) (hR : ThmBChain6.AmplitudeBoundsAllChoicesUniform) : RowDataUnifN := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, Cn, a, b, h2⟩ := hR Cg cb Cw cT CT C0
  refine ⟨C1, Cn, max a 29, max b 16, fun C' Cl h1 h3 D large₂ X Y u u' hc hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hO ν hp => ?_⟩
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D :=
    Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hc.1.1 (le_trans (le_max_right _ _) h3) (le_trans (le_max_right _ _) h1)
  obtain ⟨hIre, θ, hθ, hw, hrest⟩ := h2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h3) D large₂ X Y u u'
    hc hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hO ν hp
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨Cc⟩ := choiceExists X θ hθ
  have hLF := LocF.locFactor_holds hG Cc
  have hB : WuBessel Cc := wuBesselOfLoc_all Cc hG hBW hLF (fun τ => dsTr Cc τ) (fun τ => haarTr Cc τ)
    (fun u τ => colsTypeTr Cc u τ)
  obtain ⟨⟨νl, hQ, hU⟩, hK, hWK, hN⟩ := hrest Cc hB
  have hJ := OOCore3.jFactPK_of_core Y u u' ν Cc hB large₂ C1 (OOCore3.ooCorePK_of Y u u' ν Cc hB large₂ C1 νl hQ
    (LocNorm.locNormPK_of Y u u' Cc hB large₂ C1 νl hU (fun w τ => LocJEq.integrand_aesm Cc hB u u' τ _ _) hK hWK))
  choose dg hdg using goodS_deg hLF hB u u'
  exact ⟨hIre, θ, Cc, hB, hθ, hw, ⟨dg, hdg⟩, RMeasP.rMeasExP_of_goodW Cc u u' (goodW_all Cc u u'),
    OOCore3.localAmplitudesPositive_of_kernel Y u u' ν Cc hB large₂ C1 hJ, OOCore3.thetaWinP_of_K Y u u' ν Cc hB large₂ C1 hJ, hN⟩

theorem stepThmBPinnedC_ofN (hB : JointNormBoundRotatedUniform) (hA : AmpUnif) (hP : PtUnif)
    (hR : RowDataUnifN) : StepThmBPinnedC := by
  intro Cg cb Cw cT CT C0 A
  obtain ⟨C1, Cn, c₀, d₀, hR2⟩ := hR Cg cb Cw cT CT C0
  obtain ⟨Ca, -, a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0 C1
  obtain ⟨g₀, h₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨Cb, Cg₀, hB1⟩ := hB (A : ℝ) (|CT| + 1 / 8 + 2 * |Cg|) (Nat.cast_nonneg A)
  have hCB : 0 ≤ max 0 Cb * max 2 Cw + |Ca| + |Cn| := by
    have h1 : 0 ≤ max 0 Cb := le_max_left _ _
    have h2 : 0 ≤ max 2 Cw := le_trans (by norm_num) (le_max_left _ _)
    have := mul_nonneg h1 h2
    positivity
  refine ⟨max 0 Cb * max 2 Cw + |Ca| + |Cn|, hCB, max a₀ (max c₀ g₀),
    max 8 (max (128 * max Cg₀ 0) (max b₀ (max d₀ h₀))), ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u u' hctx hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBO ν hpin νL ng
  have hC'a : a₀ ≤ C' := le_trans (le_max_left _ _) hC'
  have hC'c : c₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC'
  have hC'g : g₀ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC'
  have hCl8 : 8 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCls : 128 * max Cg₀ 0 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hClb : b₀ ≤ Cl :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hCl
  have hCld : d₀ ≤ Cl := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)) hCl
  have hClh : h₀ ≤ Cl := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)) hCl
  have hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 := hctx.1
  have hTT := hypTT_of hctx.2.1
  obtain ⟨hT, hT'⟩ := tr_pos hctx.2.1
  have hm := cl_le_m hH
  have hs0 : 0 ≤ max Cg₀ 0 := le_max_right _ _
  have hmR : (128 : ℝ) * |max Cg₀ 0| ≤ D.R.m := by rw [abs_of_nonneg hs0]; linarith
  have hmR' : |max Cg₀ 0| ≤ D.R.m := by rw [abs_of_nonneg hs0]; linarith
  have hβ2 : (2 : ℝ) ≤ max 2 Cw := le_max_left _ _
  have hCh0 : (0 : ℝ) ≤ |CT| + 1 / 8 + 2 * |Cg| := by positivity
  have hChT : CT ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by
    have h1 : |CT| + 1 / 8 + 2 * |Cg| ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by nlinarith
    have h2 : CT ≤ |CT| + 1 / 8 + 2 * |Cg| := by have := le_abs_self CT; have := abs_nonneg Cg; linarith
    linarith
  have hChg : 1 / 8 + 2 * Cg ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by
    have h1 : |CT| + 1 / 8 + 2 * |Cg| ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by nlinarith
    have h2 : 1 / 8 + 2 * Cg ≤ |CT| + 1 / 8 + 2 * |Cg| := by have := le_abs_self Cg; have := abs_nonneg CT; linarith
    linarith
  have hStd := Formalism.MainNotions.BridgeLemma.stdOfHyp_rec D large₂ C' Cl Cg cb Cw cT CT C0 (|CT| + 1 / 8 + 2 * |Cg|) (max Cg₀ 0)
    (max Cg₀ 0) (max 2 Cw) hCl8 hCh0 hβ2 (le_max_right _ _) hChT hChg hmR hmR'
  have hka := (Formalism.MainNotions.BridgeLemma.std_kaS hH hCl8).1
  obtain ⟨hIre, θ, Cc, hBs, hθ0, hθw, ⟨dg, hAg⟩, hM, hPp, hTh, hNF⟩ :=
    hR2 C' Cl hC'c hCld D large₂ X Y u u' hctx hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBO ν hpin
  have hTB : 0 ≤ Real.exp ((max 0 Cb * max 2 Cw + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f *
      Real.log large₂.sc.b) * Ire := mul_nonneg (Real.exp_pos _).le hIre
  exact pointSum_of_B3R (Y.tO u u') (NOf2 Y u u' νL ν ng) (hB1 (max Cg₀ 0) (le_max_left _ _) D)
    (fun γ => Formalism.L2.SG.ThmBUse.J2of_nonneg' Y u u' ν γ) hTB
    (ties_coreN (Y.tO u u') (NOf2 Y u u' νL ν ng) u u' A hH hTT hT hT' (hA2 C' Cl hC'a hClb D large₂) hStd
      (fun _ => hctx.2.2.2.2.2.2.2.2.2) (point_amplitude_relation_normalized Y u u' (hP2 C' Cl hC'g hClh D large₂ X Y u u' hctx) νL ν ng)
      (Formalism.L2.SG.ThmBUse.weight_normalized Formalism.L2.SG.Pf.weightConclusion Y u u' νL ν ng A) hIre Cc hBs hθ0 hθw dg hAg zero_le_one
      (jointAmplitudeFactorizationRotated_of Y u u' large₂ C1 Cc hBs ν νL ng (RelPtR.relPtExPR_holds Cc u u') hM hPp hTh)
      (fun sec hs => by rw [ENNReal.ofReal_one, one_mul]; exact hNF sec hs) hs0 hka (by linarith))

theorem stepThmBG_ofN (hB : JointNormBoundRotatedUniform) (hA : AmpUnif) (hP : PtUnifG)
    (hR : RowDataUnifN) : StepThmBG := by
  intro Cg cb Cw cT CT C0 A
  obtain ⟨C1, Cn, c₀, d₀, hR2⟩ := hR Cg cb Cw cT CT C0
  obtain ⟨Ca, -, a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0 C1
  obtain ⟨g₀, h₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨Cb, Cg₀, hB1⟩ := hB (A : ℝ) (|CT| + 1 / 8 + 2 * |Cg|) (Nat.cast_nonneg A)
  have hCB : 0 ≤ max 0 Cb * max 2 Cw + |Ca| + |Cn| := by
    have h1 : 0 ≤ max 0 Cb := le_max_left _ _
    have h2 : 0 ≤ max 2 Cw := le_trans (by norm_num) (le_max_left _ _)
    have := mul_nonneg h1 h2
    positivity
  refine ⟨max 0 Cb * max 2 Cw + |Ca| + |Cn|, hCB, max a₀ (max c₀ g₀),
    max 8 (max (128 * max Cg₀ 0) (max b₀ (max d₀ h₀))), ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBO ν hpin νL ng
  have hC'a : a₀ ≤ C' := le_trans (le_max_left _ _) hC'
  have hC'c : c₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC'
  have hC'g : g₀ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC'
  have hCl8 : 8 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCls : 128 * max Cg₀ 0 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hClb : b₀ ≤ Cl :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hCl
  have hCld : d₀ ≤ Cl := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)) hCl
  have hClh : h₀ ≤ Cl := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)) hCl
  have hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 := hctx.1
  have hTT := hypTT_of hctx.2.1
  obtain ⟨hT, -⟩ := tr_pos hctx.2.1
  have hm := cl_le_m hH
  have hs0 : 0 ≤ max Cg₀ 0 := le_max_right _ _
  have hmR : (128 : ℝ) * |max Cg₀ 0| ≤ D.R.m := by rw [abs_of_nonneg hs0]; linarith
  have hmR' : |max Cg₀ 0| ≤ D.R.m := by rw [abs_of_nonneg hs0]; linarith
  have hβ2 : (2 : ℝ) ≤ max 2 Cw := le_max_left _ _
  have hCh0 : (0 : ℝ) ≤ |CT| + 1 / 8 + 2 * |Cg| := by positivity
  have hChT : CT ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by
    have h1 : |CT| + 1 / 8 + 2 * |Cg| ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by nlinarith
    have h2 : CT ≤ |CT| + 1 / 8 + 2 * |Cg| := by have := le_abs_self CT; have := abs_nonneg Cg; linarith
    linarith
  have hChg : 1 / 8 + 2 * Cg ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by
    have h1 : |CT| + 1 / 8 + 2 * |Cg| ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by nlinarith
    have h2 : 1 / 8 + 2 * Cg ≤ |CT| + 1 / 8 + 2 * |Cg| := by have := le_abs_self Cg; have := abs_nonneg CT; linarith
    linarith
  have hStd := Formalism.MainNotions.BridgeLemma.stdOfHyp_rec D large₂ C' Cl Cg cb Cw cT CT C0 (|CT| + 1 / 8 + 2 * |Cg|) (max Cg₀ 0)
    (max Cg₀ 0) (max 2 Cw) hCl8 hCh0 hβ2 (le_max_right _ _) hChT hChg hmR hmR'
  have hka := (Formalism.MainNotions.BridgeLemma.std_kaS hH hCl8).1
  obtain ⟨hIre, θ, Cc, hBs, hθ0, hθw, ⟨dg, hAg⟩, hM, hPp, hTh, hNF⟩ :=
    hR2 C' Cl hC'c hCld D large₂ X Y u u hctx hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBO ν hpin
  have hTB : 0 ≤ Real.exp ((max 0 Cb * max 2 Cw + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f *
      Real.log large₂.sc.b) * Ire := mul_nonneg (Real.exp_pos _).le hIre
  exact pointSum_of_B3R (genT (Y.tO u u)) (NOfG Y u νL ν ng) (hB1 (max Cg₀ 0) (le_max_left _ _) D)
    (fun γ => Formalism.L2.SG.ThmBUse.J2of_nonneg' Y u u ν γ) hTB
    (ties_coreN (genT (Y.tO u u)) (NOfG Y u νL ν ng) u u A hH hTT hT hT (hA2 C' Cl hC'a hClb D large₂) hStd
      (fun _ => hctx.2.2.2.2.2.2.2.2.2) (ptTie_NOfG Y u (hP2 C' Cl hC'g hClh D large₂ X Y u hctx) νL ν ng)
      (wtTie_NOfG Y u νL ν ng A) hIre Cc hBs hθ0 hθw dg hAg zero_le_one
      (ThmBChainG.jointAmplitudeRotated_generic Y u large₂ C1 Cc hBs ν νL ng (RelPtR.relPtExPR_holds Cc u u) hM hPp hTh)
      (fun sec hs => by rw [ENNReal.ofReal_one, one_mul]; exact hNF sec hs) hs0 hka (by linarith))

end Formalism.MainStatements.RowRest
end
end

open Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.Pf

namespace Formalism.MainStatements.RowRest

theorem energyFin : EnergyFin := by
  intro D hG X u u' h
  have h1 := (EnergyConvJ.BM.realObj_inInfinityX_jsz CompanionTheory.Lime.BM.uniqGap_holds hG X u u' 1 one_pos).2.2
  rw [realObj_inNuX X u u' 1, h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (MassDataPos.cooOf_pos X u u')).ne'] at h1
  exact ENNReal.ofReal_ne_top (top_le_iff.1 h1)

theorem uniform_restriction_bound : ThmBChain6.AmplitudeBoundsAllChoicesUniform := uniform_restriction_of_finite_energy energyFin

theorem analytic_pinnedTheoremB_uniform : NGAnalytic.StepThmBPinnedC :=
  stepThmBPinnedC_ofN (ThmBChain.theoremB_uniform_rotated CompanionTheory.WaveGrid.weighted_bound_rotated_uniform) CompanionTheory.Lime.BM.ampUnif_holds
    PointUniformity.ptUnif' (rowDataUnifN_of_6 Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds uniform_restriction_bound)

theorem bDat_theoremB_global : BDat.StepThmBG :=
  stepThmBG_ofN (ThmBChain.theoremB_uniform_rotated CompanionTheory.WaveGrid.weighted_bound_rotated_uniform) CompanionTheory.Lime.BM.ampUnif_holds
    PointUniformity.ptUnifG (rowDataUnifN_of_6 Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds uniform_restriction_bound)

end Formalism.MainStatements.RowRest
