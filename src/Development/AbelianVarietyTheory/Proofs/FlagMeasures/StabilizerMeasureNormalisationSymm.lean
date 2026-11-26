module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjLebesgueCommonStabilizerNormalForm
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundIpow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageEqOfMemLowKSubStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.StabMeas

variable {k r : ℕ}

theorem cont_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem cont_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem meas_conj (a : Mat k r) : Measurable (conjM a : Mt k r → Mt k r) :=
  (cont_conj a).measurable

theorem meas_lmul (a : Mat k r) : Measurable (lmulM a : Mt k r → Mt k r) :=
  (cont_lmul a).measurable

theorem conj_conj (a b : Mat k r) : (conjM a : Mt k r → Mt k r) ∘ conjM b = conjM (a * b) := by
  funext x
  show a * (b * Matrix.of x * b⁻¹) * a⁻¹ = a * b * Matrix.of x * (a * b)⁻¹
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

theorem conj_one (x : Mt k r) : conjM 1 x = x := by
  show (1 : Mat k r) * Matrix.of x * 1⁻¹ = Matrix.of x
  simp

theorem map_conj_conj (a b : Mat k r) (μ : Measure (Mt k r)) :
    (μ.map (conjM b)).map (conjM a) = μ.map (conjM (a * b)) := by
  rw [Measure.map_map (meas_conj a) (meas_conj b), conj_conj]

def conjEquiv {a : Mat k r} (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM a
  invFun := conjM a⁻¹
  left_inv x := by
    have := congrFun (conj_conj a⁻¹ a) x
    rw [Matrix.nonsing_inv_mul _ ha, conj_one] at this
    exact this
  right_inv x := by
    have := congrFun (conj_conj a a⁻¹) x
    rw [Matrix.mul_nonsing_inv _ ha, conj_one] at this
    exact this
  measurable_toFun := meas_conj a
  measurable_invFun := meas_conj a⁻¹

theorem conj_back {a : Mat k r} (ha : IsUnit a.det) (s : Mat k r) : a * (a⁻¹ * s * a) * a⁻¹ = s := by
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ ha]

theorem haar_conj {a : Mat k r} (ha : IsUnit a.det) {S S' : Set (Mat k r)} (hS : ∀ x, a * x * a⁻¹ ∈ S' ↔ x ∈ S)
    {μ : Measure (Mt k r)} (h : IsHaarOn S μ) (h' : IsUnimod S μ) :
    IsHaarOn S' (μ.map (conjM a)) ∧ IsUnimod S' (μ.map (conjM a)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := h'
  have hb : ∀ s ∈ S', a⁻¹ * s * a ∈ S := fun s hs => (hS _).1 (by rwa [conj_back ha])
  refine ⟨⟨?_, ?_, ?_, fun s hs => ?_⟩, fun s hs => ?_, ?_⟩
  · exact (conjEquiv ha).measurableEmbedding.sigmaFinite_map
  · intro h0
    exact h2 ((Measure.map_eq_zero_iff (meas_conj a).aemeasurable).1 h0)
  · have := (conjEquiv ha).map_apply (μ := μ) {x | Matrix.of x ∉ S'}
    refine this.trans ?_
    rw [← h3]
    congr 1
    ext x
    exact not_congr (hS (Matrix.of x))
  · conv_rhs => rw [← h4 _ (hb s hs)]
    rw [Measure.map_map (meas_lmul _) (meas_conj a), Measure.map_map (meas_conj a) (meas_lmul _)]
    congr 1
    funext x
    show s * (a * Matrix.of x * a⁻¹) = a * (a⁻¹ * s * a * Matrix.of x) * a⁻¹
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ ha]
  · conv_rhs => rw [← h5 _ (hb s hs)]
    rw [Measure.map_map (continuous_rmulM _).measurable (meas_conj a),
      Measure.map_map (meas_conj a) (continuous_rmulM _).measurable]
    congr 1
    funext x
    show (a * Matrix.of x * a⁻¹) * s = a * (Matrix.of x * (a⁻¹ * s * a)) * a⁻¹
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]
  · conv_rhs => rw [← h6]
    rw [Measure.map_map measurable_invM (meas_conj a), Measure.map_map (meas_conj a) measurable_invM]
    congr 1
    funext x
    show (a * Matrix.of x * a⁻¹)⁻¹ = a * (Matrix.of x)⁻¹ * a⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc]

theorem haar_smul {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) (h' : IsUnimod S μ) {s : ℝ} (hs : 0 < s) :
    IsHaarOn S (ENNReal.ofReal s • μ) ∧ IsUnimod S (ENNReal.ofReal s • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := h'
  refine ⟨⟨?_, ?_, ?_, fun s hs => ?_⟩, fun s hs => ?_, ?_⟩
  · exact inferInstanceAs (SigmaFinite (s.toNNReal • μ))
  · intro h0
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) h0
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
      ENNReal.ofReal_eq_zero, Measure.measure_univ_eq_zero] at this
    rcases this with h | h
    · exact absurd h (not_le.2 hs)
    · exact h2 h
  · rw [Measure.smul_apply, h3, smul_zero]
  · rw [Measure.map_smul _ (meas_lmul s).aemeasurable, h4 s hs]
  · rw [Measure.map_smul _ (continuous_rmulM s).measurable.aemeasurable, h5 s hs]
  · rw [Measure.map_smul _ measurable_invM.aemeasurable, h6]

theorem isClosedSub_Rset {γ : Mat k r} (hγ : γ ∈ GG k r) : IsClosedSub k r (Rset k r γ) := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  have hu := isUnit_det_of_mem_GG hγ
  refine ⟨fun x hx => n1 hx.1, ?_, ⟨n3, ?_⟩, fun a ha b hb => ⟨n4 _ ha.1 _ hb.1, ?_⟩, fun a ha => ⟨n5 _ ha.1, ?_⟩⟩
  · have hc : Continuous fun x : Mat k r => γ * x * γ⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := n2.inter (n2.preimage hc)
    exact this
  · rwa [Matrix.mul_one, Matrix.mul_nonsing_inv _ hu]
  · convert n4 _ ha.2 _ hb.2 using 1
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  · convert n5 _ ha.2 using 1
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc]

theorem conj_mem_Nset {n : Mat k r} (hn : n ∈ Nset k r) (x : Mat k r) : n * x * n⁻¹ ∈ Nset k r ↔ x ∈ Nset k r := by
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  have hu := isUnit_det_of_mem_GG (n1 hn)
  refine ⟨fun h => ?_, fun h => n4 _ (n4 _ hn _ h) _ (n5 _ hn)⟩
  convert n4 _ (n4 _ (n5 _ hn) _ h) _ hn using 1
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem conj_mem_Rset {n₁ n₂ : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (g x : Mat k r) :
    n₂⁻¹ * x * n₂⁻¹⁻¹ ∈ Rset k r (n₁ * g * n₂) ↔ x ∈ Rset k r g := by
  have hu := isUnit_det_of_mem_GG (isClosedSub_Nset.1 h₂)
  have e : n₁ * g * n₂ * (n₂⁻¹ * x * n₂⁻¹⁻¹) * (n₁ * g * n₂)⁻¹ = n₁ * (g * x * g⁻¹) * n₁⁻¹ := by
    rw [Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  show (_ ∧ _) ↔ (_ ∧ _)
  rw [e, conj_mem_Nset h₁, conj_mem_Nset (isClosedSub_Nset.2.2.2.2 _ h₂)]

theorem dmin_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {n₁ n₂ : Mat k r}
    (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (g : Mat k r) (l : Fin (r + 2)) :
    Dmin k r z z' (n₁ * g * n₂) l = Dmin k r z z' g l :=
  Formalism.QuantumDeterminants.dInv k r z z' hz hz' n₁ ⟨1, (isClosedSub_UWset z).2.2.1, n₁, h₁, (Matrix.one_mul _).symm⟩
    n₂ ⟨1, (isClosedSub_UWset z').2.2.1, n₂, h₂, (Matrix.one_mul _).symm⟩ g l

theorem stabilizer_measure_normalisation : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → γ ∈ GG k r ∧ IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ IsNormalFormStabilizerMeasure k r hj z' z γ⁻¹ s (μR.map (conjM γ)) ∧ 0 < Dj k r hj z z' γ ∧ Dj k r hj z' z γ⁻¹ = Dj k r hj z z' γ ∧ ∀ De, DeOK k r z z' γ De → DeOK k r z' z γ⁻¹ De := by
  rintro k r j hj z z' γ s μR hs ⟨hz, hz', hT, n₁, h₁, n₂, h₂, g₀, β, c, hg, rfl, rfl⟩
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  obtain ⟨a1, -, a3, a4, -, a6, -⟩ := GlobalTheory.T.normalFormFlagZero_middle_inverse_minor_orthogonal k r j hj z z' g₀ β c hz hz' hT hg
  obtain ⟨b1, b2⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r j hj z z' g₀ β c hz hz' hT hg
  have c1 := GlobalTheory.T.map_conj_lebesgueCommonStabilizerNormalForm k r j hj z z' g₀ β c hz hz' hT hg
  have hγ : n₁ * g₀ * n₂ ∈ GG k r :=
    isClosedSub_GG.2.2.2.1 _ (isClosedSub_GG.2.2.2.1 _ (n1 h₁) _ hg.1) _ (n1 h₂)
  have hinv : (n₁ * g₀ * n₂)⁻¹ = n₂⁻¹ * g₀⁻¹ * n₁⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  obtain ⟨d1, d2⟩ := haar_smul b1 b2 hs
  obtain ⟨e1, e2⟩ := haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ h₂))) (conj_mem_Rset h₁ h₂ g₀) d1 d2
  have hD : ∀ l, ‖Dmin k r z' z (n₁ * g₀ * n₂)⁻¹ l‖ = ‖Dmin k r z z' (n₁ * g₀ * n₂) l‖ := fun l => by
    rw [hinv, dmin_N hz' hz (n5 _ h₂) (n5 _ h₁), dmin_N hz hz' h₁ h₂, a6]
  refine ⟨hγ, isClosedSub_Rset hγ, e1, e2,
    ⟨hz', hz, a1 ▸ hT, n₂⁻¹, n5 _ h₂, n₁⁻¹, n5 _ h₁, g₀⁻¹, β, c⁻¹, a3, hinv, ?_⟩, ?_, hD _, fun De h => ⟨h.1, ?_⟩⟩
  · rw [map_conj_conj, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_of_mem_GG (n1 h₂)), ← map_conj_conj,
      Measure.map_smul _ (meas_conj g₀).aemeasurable, c1, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 h₁))]
  · unfold Dj at a4 ⊢
    rwa [dmin_N hz hz' h₁ h₂]
  · intro l hl h0
    rw [hD]
    refine h.2 l hl fun h' => h0 ?_
    rw [← norm_eq_zero, hD, h', norm_zero]

end GlobalTheory.Amp.StabMeas
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymmStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_measure_normalisation_symm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → γ ∈ GG k r ∧ IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ IsNormalFormStabilizerMeasure k r hj z' z γ⁻¹ s (μR.map (conjM γ)) ∧ 0 < Dj k r hj z z' γ ∧ Dj k r hj z' z γ⁻¹ = Dj k r hj z z' γ ∧ ∀ De, DeOK k r z z' γ De → DeOK k r z' z γ⁻¹ De := by
  first | exact @GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation | exact GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation | (intros; apply GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeLatIn
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain
open scoped ENNReal Classical

namespace GlobalTheory.Mass.DetAgree

section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem genIdxH_eq_idxN {A B : Submodule (𝓞 K) V} (hBA : B ≤ A) (h0 : idxN A B ≠ 0) :
    Lat.genIdxH A B = (idxN A B : ℝ) := by
  obtain ⟨k, hk, hc⟩ := Formalism.LFunctionChainParameters.LLcv.card_pLen _ A B hBA rfl h0
  let e : HeightOneSpectrum (𝓞 K) ≃ {p : Ideal (𝓞 K) // p.IsMaximal} :=
    { toFun := fun P => ⟨P.asIdeal, P.isMaximal⟩
      invFun := fun p => ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hl : ∀ P : HeightOneSpectrum (𝓞 K), (haveI := P.isPrime; lidx P.asIdeal A B) = (k (e P) : ℤ) := by
    intro P
    have a := hk (e P)
    unfold Formalism.LFunctionChainParameters.LLcv.pLen at a
    unfold lidx
    rw [inf_eq_right.mpr hBA, indexBasic_locLen_self]
    unfold locLen
    erw [a]
    simp
  unfold Lat.genIdxH
  simp only [hl, zpow_natCast]
  have := finprod_comp_equiv (f := fun w : {p : Ideal (𝓞 K) // p.IsMaximal} =>
    ((Ideal.absNorm w.1 : ℕ) : ℝ) ^ k w) e
  refine this.trans ?_
  rw [idxN, hc, finprod_eq_prod_of_mulSupport_subset (s := k.support), Finsupp.prod, Nat.cast_prod]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [Nat.cast_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h
    apply hw
    simp [h]

variable [Module K V] [IsScalarTower (𝓞 K) K V]

theorem span_inf_eq (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L) (U : Submodule K V) :
    Submodule.span K ((L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = U := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => hx.2) fun u hu => ?_
  obtain ⟨r, hr, hru⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS (K := K) L (x := u) (by rw [hL.span_eq_top]; trivial)
  have h1 : algebraMap (𝓞 K) K r ≠ 0 := by simpa using nonZeroDivisors.ne_zero hr
  have h2 : r • u ∈ Submodule.span K ((L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) :=
    Submodule.subset_span ⟨hru, (U.restrictScalars (𝓞 K)).smul_mem r hu⟩
  rw [← algebraMap_smul K r] at h2
  exact (Submodule.smul_mem_iff _ h1).1 h2

theorem isLattice_latIn (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L) (U : Submodule K V) :
    Submodule.IsFullLattice K (latIn U L) := by
  haveI : Submodule.IsLattice K (latIn U L) := by
    apply Submodule.IsLattice.of_fg K
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact hL.fg.of_le (Submodule.map_comap_le _ _)
  refine ⟨?_⟩
  apply Submodule.map_injective_of_injective U.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  refine (congrArg (Submodule.span K) ?_).trans (span_inf_eq L hL U)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨hx, hxU⟩
    exact ⟨⟨x, hxU⟩, hx, rfl⟩

variable [StarRing K]

theorem nondeg_of_pd {h : V →ₗ⋆[K] V →ₗ[K] K} (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have key : ∀ x, h x x = 0 → x = 0 := fun x hx => by
    by_contra h0
    have := hp τ x h0
    rw [hx] at this
    simp at this
  exact ⟨fun x hx => key x (hx x), fun x hx => key x (hx x)⟩

theorem idxN_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L)
    (U : Submodule K V) :
    idxN (Lat.dualInH h (L ⊓ U.restrictScalars (𝓞 K))) (L ⊓ U.restrictScalars (𝓞 K)) =
      discN (hRes h U) (latIn U L) := by
  have e1 : (L ⊓ U.restrictScalars (𝓞 K)).toAddSubgroup =
      (latIn U L).toAddSubgroup.map U.subtype.toAddMonoidHom := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
  have e2 : (Lat.dualInH h (L ⊓ U.restrictScalars (𝓞 K))).toAddSubgroup =
      (dual (hRes h U) (latIn U L)).toAddSubgroup.map U.subtype.toAddMonoidHom := by
    unfold Lat.dualInH
    rw [span_inf_eq L hL U]
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, h2⟩, (dualBasic_mem_dual _ _ _).2 fun y hy => ?_, rfl⟩
      exact (dualBasic_mem_dual _ _ _).1 h1 y ⟨hy, y.2⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(dualBasic_mem_dual _ _ _).2 fun z hz => ?_, y.2⟩
      exact (dualBasic_mem_dual _ _ _).1 hy ⟨z, hz.2⟩ hz.1
  rw [discN, idxN, idxN, e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ U.injective_subtype]

theorem discGen_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hle : L ≤ dual h L) (e : ℕ) :
    Cnt.DiscGen h L e ↔ ∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  set D := dual h L with hD
  set q : D →ₗ[𝓞 K] Cnt.discMod h L := (L.comap D.subtype).mkQ with hq
  have key : ∀ s : Finset D, Submodule.span (𝓞 K) ((s.image q : Finset _) : Set (Cnt.discMod h L)) = ⊤ ↔
      D = L ⊔ Submodule.span (𝓞 K) ((s.image D.subtype : Finset V) : Set V) := by
    intro s
    rw [Finset.coe_image, Finset.coe_image, ← Submodule.map_span, ← Submodule.map_span, hq,
      Submodule.map_mkQ_eq_top, ← (Submodule.map_injective_of_injective D.injective_subtype).eq_iff,
      Submodule.map_sup, Submodule.map_comap_subtype, inf_eq_right.2 hle, Submodule.map_top,
      Submodule.range_subtype, eq_comm]
  constructor
  · rintro ⟨s, hs, hsp⟩
    have hsurj : Function.Surjective q := Submodule.mkQ_surjective _
    refine ⟨(s.image (Function.surjInv hsurj)).image D.subtype,
      Finset.card_image_le.trans (Finset.card_image_le.trans hs), (key _).1 ?_⟩
    rw [Finset.image_image, (Function.rightInverse_surjInv hsurj).comp_eq_id, Finset.image_id, hsp]
  · rintro ⟨t, ht, hsp⟩
    have htD : ∀ x ∈ t, x ∈ D := fun x hx => by
      rw [hsp]; exact Submodule.mem_sup_right (Submodule.subset_span hx)
    have ee : (t.subtype (· ∈ D)).image D.subtype = t := by
      ext x
      simp only [Finset.mem_image, Finset.mem_subtype]
      exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨⟨x, htD x hx⟩, hx, rfl⟩⟩
    refine ⟨(t.subtype (· ∈ D)).image q, Finset.card_image_le.trans ?_, (key _).2 (by rw [ee]; exact hsp)⟩
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans ht

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → Lat.latDetH h L ^ 2 = (discN h L : ℝ) ∧ 0 < Lat.latDetH h L ∧ (∀ j de : ℕ, Cnt.cntPrim h L j de = (primSp h L j (de ^ 2)).encard) ∧ (∀ e : ℕ, Cnt.DiscGen h L e ↔ (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V))) ∧ ∀ (U : Submodule K V), Lat.latDetH h (L ⊓ U.restrictScalars (𝓞 K)) ^ 2 = (discN (hRes h U) (latIn U L) : ℝ) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL
  have hFull : Submodule.IsFullLattice K L := hL.1
  have hle : L ≤ dual h L := fun x hx => (dualBasic_mem_dual _ _ _).2 fun y hy => hL.2 y hy x hx
  have hn := nondeg_of_pd hp
  have h0 := (DiscOrder.main K V h hK hs hn L hL).1
  have hd : Lat.dualInH h L = dual h L := by
    unfold Lat.dualInH
    rw [hFull.span_eq_top]
    simp
  have h1 : Lat.latDetH h L = Real.sqrt (discN h L : ℝ) := by
    rw [Lat.latDetH, hd, genIdxH_eq_idxN hle h0, discN]
  have hU : ∀ U : Submodule K V, Lat.latDetH h (L ⊓ U.restrictScalars (𝓞 K)) =
      Real.sqrt (discN (hRes h U) (latIn U L) : ℝ) := by
    intro U
    have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
    have hpU : PD (hRes h U) := fun τ x hx => hp τ x fun e => hx (Subtype.ext e)
    have hI : IsIntLat (hRes h U) (latIn U L) :=
      ⟨isLattice_latIn L hFull U, fun x hx y hy => hL.2 x hx y hy⟩
    have n0 := (DiscOrder.main K U _ hK hsU (nondeg_of_pd hpU) _ hI).1
    rw [← idxN_dualInH h L hFull U] at n0 ⊢
    rw [Lat.latDetH, genIdxH_eq_idxN _ n0]
    intro x hx
    exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hL.2 y hy.1 x hx.1, Submodule.subset_span hx⟩
  refine ⟨by rw [h1, Real.sq_sqrt (Nat.cast_nonneg _)], ?_, fun j de => ?_, discGen_iff h L hle,
    fun U => by rw [hU, Real.sq_sqrt (Nat.cast_nonneg _)]⟩
  · rw [h1]
    exact Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero h0)
  · have hinj : Function.Injective fun U : Submodule K V => L ⊓ U.restrictScalars (𝓞 K) :=
      Function.LeftInverse.injective (g := fun M : Submodule (𝓞 K) V => Submodule.span K (M : Set V))
        (span_inf_eq L hFull)
    have hsq : ∀ n : ℕ, Real.sqrt (n : ℝ) = de ↔ n = de ^ 2 := fun n => by
      rw [Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast Iff.rfl
    rw [Cnt.cntPrim, ← hinj.encard_image]
    congr 1
    ext M
    constructor
    · rintro ⟨⟨-, a⟩, b, c⟩
      refine ⟨Submodule.span K (M : Set V), ⟨b, ?_⟩, a.symm⟩
      rw [← hsq, ← hU, ← a, c]
    · rintro ⟨U, ⟨a, b⟩, rfl⟩
      refine ⟨⟨inf_le_left, ?_⟩, ?_, ?_⟩
      · simp only
        rw [span_inf_eq L hFull]
      · simp only
        rw [span_inf_eq L hFull, a]
      · simp only
        rw [hU, hsq, b]

end GlobalTheory.Mass.DetAgree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerNormalFormBlockUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerNormalFormBlockUnitriangular
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.StabNormal

variable {k r : ℕ}

theorem xstJ_self : XstJ k r r = Xst k r := by
  unfold XstJ Xst
  congr 1
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, a.2⟩, rfl⟩

theorem isNormal0_iff {β : Fin r → ℕ} {g : Mat k r} (z' : Fin (2 * r + k + 1) → ℂ) :
    IsNormal0 k r le_rfl β 1 (g *ᵥ z') z' g ↔ IsNormal k r β g := by
  constructor
  · rintro ⟨hg, -, -, -, -, hX, -, hB⟩
    refine ⟨hg, fun a => ?_, hB⟩
    rw [← xstJ_self]
    exact hX a a.2
  · rintro ⟨hg, hX, hB⟩
    refine ⟨hg, by simp, by simp, hB.1, fun a b hb => absurd b.2 (not_lt.2 hb), fun a _ => ?_,
      fun a ha => absurd a.2 (not_lt.2 ha), hB⟩
    rw [xstJ_self]
    exact hX a

theorem pTop_self (q : PTop k r r) : pTop k r r q = 1 := by
  have h1 : (fun a : Fin r => if h : r ≤ a.val then q.1 ⟨a, h⟩ else 0) = 0 :=
    funext fun a => dif_neg (not_le.2 a.2)
  have h2 : (fun p : UT r => if h : r ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) = 0 :=
    funext fun p => dif_neg (not_le.2 p.1.1.2)
  have h3 : (fun a : Fin r => if h : r ≤ a.val then q.2.2 ⟨a, h⟩ else 0) = 0 :=
    funext fun a => dif_neg (not_le.2 a.2)
  have hs : skewM (0 : UT r → ℂ) (0 : Fin r → ℝ) = 0 := by
    ext a b
    simp only [skewM]
    split_ifs <;> simp
  show pEl k r (fun a : Fin r => if h : r ≤ a.val then q.1 ⟨a, h⟩ else 0)
      (skewM (fun p : UT r => if h : r ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0)
        (fun a : Fin r => if h : r ≤ a.val then q.2.2 ⟨a, h⟩ else 0)) = 1
  rw [h1, h2, h3, hs]
  exact Rad.pEl_zero

theorem rEl_self (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r r) : rEl k r r β q = uEmb k r (upperIn β q.1) := by
  show uEmb k r (upperIn β q.1) * pTop k r r q.2 = _
  rw [pTop_self, mul_one]

theorem range_rEl (β : Fin r → ℕ) :
    Set.range (rEl k r r β) = Set.range fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
  ext m
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, (rEl_self β q).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, 0), rEl_self β (x, 0)⟩

theorem volume_pTop : (volume : Measure (PTop k r r)) Set.univ = 1 := by
  haveI : IsEmpty {a : Fin r // r ≤ a.val} := ⟨fun a => absurd a.2 (not_le.2 a.1.2)⟩
  haveI : IsEmpty {p : UT r // r ≤ p.1.1.val} := ⟨fun p => absurd p.2 (not_le.2 p.1.1.1.2)⟩
  rw [← Set.univ_prod_univ, Measure.volume_eq_prod, Measure.prod_prod, ← Set.univ_prod_univ,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp [volume_pi, Measure.pi_univ]

theorem lebesgueCommonStabilizerNormalForm_full_eq (β : Fin r → ℕ) : lebR0 k r r β = lebR k r β := by
  have hc : Continuous fun x : UTin β → ℂ => Matrix.of.symm (uEmb k r (upperIn β x)) := by
    have h := (RConj.continuous_rEl (k := k) (r := r) r β).comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : UTin β → ℂ => (0 : PTop k r r)))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have := h.matrix_elem i j
    simpa [Function.comp_def, rEl_self] using this
  have hf : (fun q : (UTin β → ℂ) × PTop k r r => Matrix.of.symm (rEl k r r β q)) =
      (fun x : UTin β → ℂ => Matrix.of.symm (uEmb k r (upperIn β x))) ∘ Prod.fst := by
    funext q
    simp [rEl_self]
  rw [lebR0, lebR, hf, ← Measure.map_map hc.measurable measurable_fst, Measure.volume_eq_prod,
    Measure.map_fst_prod, volume_pTop, one_smul]

theorem tz_last : 0 < Tz k r (bvec (wI k r (Fin.last k))) := by
  have hv : (wI k r (Fin.last k)).val = r + k := rfl
  have hH : Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) = -1 := by
    unfold Hpk
    rw [hv]
    simp
  have he : herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) =
      Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
    simp [herm, bvec, Matrix.mulVec_single, dotProduct, Pi.single_apply]
  unfold Tz
  rw [he, hH]
  norm_num

theorem stabiliser_normal : ∀ (k r : ℕ) (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ → Rset k r g₀ = Set.range (fun x : UTin β → ℂ => uEmb k r (upperIn β x)) ∧ IsClosedSub k r (Rset k r g₀) ∧ IsHaarOn (Rset k r g₀) (lebR k r β) ∧ IsUnimod (Rset k r g₀) (lebR k r β) ∧ IsNormal k r β g₀⁻¹ ∧ (lebR k r β).map (conjM g₀) = lebR k r β := by
  intro k r g₀ β hN
  obtain ⟨w, hw⟩ : ∃ w : Fin (2 * r + k + 1) → ℂ, w = bvec (wI k r (Fin.last k)) := ⟨_, rfl⟩
  have h0 : IsNormal0 k r le_rfl β 1 (g₀ *ᵥ w) w g₀ := (isNormal0_iff w).2 hN
  have hwW : inWb k r w := hw ▸ NfMid.inWb_bvec _
  have hzW : inWb k r (g₀ *ᵥ w) := NfMid.inWb_mulVec h0 hwW
  have hT : 0 < Tz k r (g₀ *ᵥ w) := by
    rw [← NfMid.tz_eq h0, hw]
    exact tz_last
  obtain ⟨hR, hC⟩ := GlobalTheory.T.commonStabilizerSet_eq_range_normalForm k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  obtain ⟨hH, hU⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  have hM := RConj.lebR0_map_conjM_eq_of_isNormalZero k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  rw [lebesgueCommonStabilizerNormalForm_full_eq] at hH hU hM
  rw [range_rEl] at hR
  refine ⟨hR, hC, hH, hU, ?_, hM⟩
  have hi := NfMid.isNormal0_inv h0
  rw [inv_one] at hi
  have hback : g₀⁻¹ *ᵥ (g₀ *ᵥ w) = w := NfMid.inv_mul_vec hN.1 w
  have hi' : IsNormal0 k r le_rfl β 1 (g₀⁻¹ *ᵥ (g₀ *ᵥ w)) (g₀ *ᵥ w) g₀⁻¹ := by
    rw [hback]
    exact hi
  exact (isNormal0_iff (g₀ *ᵥ w)).1 hi'

end GlobalTheory.Amp.StabNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerNormalFormBlockUnitriangularStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular : ∀ (k r : ℕ) (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ → Rset k r g₀ = Set.range (fun x : UTin β → ℂ => uEmb k r (upperIn β x)) ∧ IsClosedSub k r (Rset k r g₀) ∧ IsHaarOn (Rset k r g₀) (lebR k r β) ∧ IsUnimod (Rset k r g₀) (lebR k r β) ∧ IsNormal k r β g₀⁻¹ ∧ (lebR k r β).map (conjM g₀) = lebR k r β := by
  first | exact @GlobalTheory.Amp.StabNormal.stabiliser_normal | exact GlobalTheory.Amp.StabNormal.stabiliser_normal | (intros; apply GlobalTheory.Amp.StabNormal.stabiliser_normal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingEntriesInf
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepAverage

theorem isClosedEmbedding_entries {n : ℕ} (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) := by
  have key := (uJEmb n ε).1
  exact key

theorem isClosedEmbedding_entries_inf (I : AutInst) :
    Topology.IsClosedEmbedding (fun g : I.Ginf =>
      (fun v i j => uMat (g v) i j : InfinitePlace I.F → Fin I.n → Fin I.n → ℂ)) := by
  have h : ∀ v : InfinitePlace I.F, Topology.IsClosedEmbedding
      (fun g : Formalism.REAL.UJ (I.ε v) => (fun i j => uMat g i j : Fin I.n → Fin I.n → ℂ)) :=
    fun v => isClosedEmbedding_entries (I.ε v)
  exact Topology.IsClosedEmbedding.piMap h

theorem integrable_loc {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {F : (Fin n → Fin n → ℂ) → ℂ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w) (muG ε) := by
  have hemb := isClosedEmbedding_entries ε
  have hrep : Continuous (fun g : UJ ε => σ (umat g) w) :=
    (hσ.2.2 w).comp_continuous hemb.continuous (fun g => g.2)
  have hcs : HasCompactSupport (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w) :=
    (hc.comp_isClosedEmbedding hemb).smul_right
  exact ((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs

theorem integrable_inf (B : RowsAut) (hσ : IsURep B.σs) (w : B.Hs)
    {F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w) (muInf B.I) := by
  have hemb := isClosedEmbedding_entries_inf B.I
  have hrep : Continuous (fun g : B.I.Ginf => B.σs g w) := hσ.2.2.2 w
  have hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v) := rfl
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by
    rw [hμ]
    infer_instance
  have hcs : HasCompactSupport (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w) :=
    (hc.comp_isClosedEmbedding hemb).smul_right
  exact ((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs

theorem tens_average (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) (hσ : IsURep B.σs)
    (w : ∀ v, B.H v) (F : InfinitePlace B.I.F → (Fin B.I.n → Fin B.I.n → ℂ) → ℂ)
    (hF : ∀ v, ContDiff ℝ ∞ (F v)) (hc : ∀ v, HasCompactSupport (F v)) :
    ∃ G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      B.tens (fun v => ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v) ∂(muG (B.I.ε v))) =
        ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I) := by
  classical
  obtain ⟨hin, hact, hden⟩ := B.tens_spec
  set G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun x => ∏ v, F v (x v) with hGdef
  have hGs : ContDiff ℝ ∞ G :=
    contDiff_prod (fun v _ => (hF v).comp (contDiff_apply ℝ (fun _ => (Fin B.I.n → Fin B.I.n → ℂ)) v))
  have hGc : HasCompactSupport G := by
    refine HasCompactSupport.intro' (isCompact_univ_pi fun v => hc v)
      (isClosed_set_pi fun v _ => isClosed_tsupport (F v)) ?_
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨v, hv⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)
  refine ⟨G, hGs, hGc, ?_⟩
  refine eq_of_inner_eq_on_dense_span hden ?_
  rintro y ⟨x, rfl⟩
  have hloc : ∀ v, ⟪x v, ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v)
        ∂(muG (B.I.ε v))⟫_ℂ =
      ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) * ⟪x v, B.σ v (umat g) (w v)⟫_ℂ ∂(muG (B.I.ε v)) := by
    intro v
    rw [← integral_inner (integrable_loc (hU v) (w v) (hF v).continuous (hc v))]
    simp only [inner_smul_right]
  have hglob : ⟪B.tens x, ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I)⟫_ℂ =
      ∫ g : B.I.Ginf, ∏ v, (F v (fun i j => uMat (g v) i j) * ⟪x v, B.σ v (uMat (g v)) (w v)⟫_ℂ)
        ∂(muInf B.I) := by
    rw [← integral_inner (integrable_inf B hσ (B.tens w) hGs.continuous hGc)]
    congr 1
    funext g
    rw [inner_smul_right, hact, hin, Finset.prod_mul_distrib]
  have hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v) := rfl
  have hprod := integral_fintype_prod_eq_prod (μ := fun v => muG (B.I.ε v))
    (fun v (h : UJ (B.I.ε v)) => F v (fun i j => uMat h i j) * ⟪x v, B.σ v (uMat h) (w v)⟫_ℂ)
  rw [hglob, hin, hμ]
  refine Eq.trans ?_ hprod.symm
  exact Finset.prod_congr rfl (fun v _ => hloc v)

theorem exists_smooth_average : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  intro hSL B d hd P u hu
  have hσ : IsURep B.σs := (tensorRep B d hd).1
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => (hd v).2.1.2.2.1

  let Av : B.Hs → Prop := fun y => ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ,
    ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)
  have hzero : Av 0 := by
    refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_⟩
    simp only [zero_smul, integral_zero]
  have hadd : ∀ a b, Av a → Av b → Av (a + b) := by
    rintro a b ⟨F₁, hF₁, hc₁, rfl⟩ ⟨F₂, hF₂, hc₂, rfl⟩
    refine ⟨F₁ + F₂, hF₁.add hF₂, hc₁.add hc₂, ?_⟩
    rw [← integral_add (integrable_inf B hσ _ hF₁.continuous hc₁)
      (integrable_inf B hσ _ hF₂.continuous hc₂)]
    congr 1
    funext g
    rw [Pi.add_apply, add_smul]
  have hsmul : ∀ (c : ℂ) a, Av a → Av (c • a) := by
    rintro c a ⟨F₁, hF₁, hc₁, rfl⟩
    refine ⟨fun x => c * F₁ x, contDiff_const.mul hF₁, hc₁.mul_left, ?_⟩
    rw [← integral_smul]
    congr 1
    funext g
    rw [mul_smul]

  have hbase : ∀ x : ∀ v, B.H v, (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (B.tens x) := by
    intro x hx
    have hloc : ∀ v, ∃ F : (Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        x v = ∫ g : UJ (B.I.ε v), F (fun i j => umat g i j) • B.σ v (umat g) (B.w v) ∂(muG (B.I.ε v)) := by
      intro v
      have hlow := (hd v).2.2.1
      have hw0 : B.w v ≠ 0 := by
        intro h0
        have h1 := hlow.1
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have hK := (hSL B.I.n (B.I.ε v) (B.lam v) (hd v).1 (B.H v) (B.σ v) (hd v).2.1).1
      exact GlobalTheory.T.exists_smooth_average_eq_of_mem_lowKSub' B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (B.w v) (hU v) hK hlow.2 hw0 (x v) (hx v)
    choose Fl hFl hcl hxl using hloc
    obtain ⟨G, hG, hcG, hEq⟩ := tens_average B hU hσ B.w Fl hFl hcl
    refine ⟨G, hG, hcG, ?_⟩
    rw [← hEq]
    congr 1
    funext v
    exact hxl v

  have hstep : ∀ (E : gInf B) y, Av y → Av (dAct B E y) := by
    rintro E y ⟨F₁, hF₁, hc₁, rfl⟩
    obtain ⟨F', hF', hc', hder⟩ := GlobalTheory.T.hasDerivAt_completedTensorOrbit_smoothAverage B F₁ E (B.tens B.w) hσ hF₁ hc₁
    exact ⟨F', hF', hc', hder.deriv⟩
  have hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (x : ∀ v, B.H v),
      (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (wordAct B l (B.tens x)) := by
    intro l x hx
    induction l with
    | nil => exact hbase x hx
    | cons X l ih => exact hstep (atPlace B X.1 X.2) _ ih
  have hu' : u ∈ Submodule.span ℂ {y | ∃ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v)))
      (x : ∀ v, B.H v), l.length ≤ P ∧ (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) ∧
        y = wordAct B l (B.tens x)} := hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, x, -, hx, rfl⟩ := hy
    exact hword l x hx
  | zero => exact hzero
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c a ha

end GlobalTheory.StepAverage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistance
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec

namespace GlobalTheory.Dec.BoundedDistance

theorem bound_le (s la R : ℝ) (m f : ℕ) (hs : 1 ≤ s) (hla : 0 < la) (hla1 : la ≤ 1) (hR : 0 ≤ R) (hf : 0 < f) :
    (1 + 2 * s * Real.exp (R / f) / la) ^ (2 * (m * f)) ≤ (3 * s / la) ^ (2 * m * f) * Real.exp (2 * (m : ℝ) * R) := by
  have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have he : 1 ≤ Real.exp (R / f) := Real.one_le_exp (div_nonneg hR (Nat.cast_nonneg _))

  have hone : 1 ≤ s * Real.exp (R / f) / la := by
    rw [le_div_iff₀ hla]
    nlinarith
  have hbase0 : 0 ≤ 1 + 2 * s * Real.exp (R / f) / la := by positivity
  have hbase : 1 + 2 * s * Real.exp (R / f) / la ≤ 3 * s / la * Real.exp (R / f) := by
    have h3 : 3 * s / la * Real.exp (R / f) =
        s * Real.exp (R / f) / la + 2 * s * Real.exp (R / f) / la := by ring
    linarith
  have hk : 2 * (m * f) = 2 * m * f := by ring
  rw [hk]
  calc (1 + 2 * s * Real.exp (R / f) / la) ^ (2 * m * f)
      ≤ (3 * s / la * Real.exp (R / f)) ^ (2 * m * f) := pow_le_pow_left₀ hbase0 hbase _
    _ = (3 * s / la) ^ (2 * m * f) * Real.exp (2 * (m : ℝ) * R) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp

theorem countRat : CountRat := by
  intro I x y r hn hr
  obtain ⟨hfin, hcard⟩ := GlobalTheory.RationalCount.count_le I x y r hn hr
  have hx := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x
  have hy := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn y

  have hx2 : tau1 I x ≤ 1 / 2 := by unfold tau1; exact min_le_left _ _
  have hy2 : tau1 I y ≤ 1 / 2 := by unfold tau1; exact min_le_left _ _
  have hs : (1 : ℝ) ≤ Real.sqrt I.n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hf : 0 < I.f := Module.finrank_pos
  have hla1 : tau1 I x * tau1 I y ≤ 1 := by nlinarith
  have key := bound_le (Real.sqrt I.n) (tau1 I x * tau1 I y) (∑ v, r v) (I.n ^ 2) I.f hs
    (mul_pos hx hy) hla1 (Finset.sum_nonneg fun v _ => hr v) hf
  push_cast at key
  exact ⟨hfin, hcard.trans key⟩

end GlobalTheory.Dec.BoundedDistance
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistanceStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_rational_elements_bounded_distance : CountRat := by
  first | exact @GlobalTheory.Dec.BoundedDistance.countRat | exact GlobalTheory.Dec.BoundedDistance.countRat | (intros; apply GlobalTheory.Dec.BoundedDistance.countRat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicOrthogonalStabilizerEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicOrthogonalStabilizerEmbedding
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem exists_stab_emb_baseChange {E R : Type} [Field E] [StarRing E] [CommRing R] (φ : E →+* R)
    (σ : R →+* R) (hσ : ∀ a, σ (φ a) = φ (star a)) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (J' : Matrix (Fin m) (Fin m) E) (x : Fin n → E) (A : Matrix (Fin n) (Fin m) E)
    (hn : m + 1 = n) (hJ : Jᴴ = J) (hd : J'.det ≠ 0) (hx : star x ⬝ᵥ (J *ᵥ x) ≠ 0)
    (hxA : star x ᵥ* (J * A) = 0) (hA : Aᴴ * J * A = J') :
    ∃ j : Formalism.UG.UJ σ (J'.map φ) →* Formalism.UG.UJ σ (J.map φ),
      (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ (fun i => φ (x i)) = (fun i => φ (x i)) ∧
        ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * A.map φ =
          A.map φ * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)) ∧
      ∀ h : Formalism.UG.UJ σ (J.map φ),
        ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ (fun i => φ (x i)) = (fun i => φ (x i)) →
          h ∈ j.range := by
  obtain ⟨u, A', h1, h2, h3, h4, h5, h6⟩ := exists_dual_of_anisotropic_orthogonal E n m J J' x A hn hJ hd hx hxA hA
  have hsx : (fun i => σ (φ (x i))) = φ ∘ star x := by
    funext i; simp [hσ]
  have hcT : Formalism.UG.cT σ (A.map φ) = (Aᴴ).map φ := by
    ext i j; simp [Formalism.UG.cT, hσ]
  have mv : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin b → E),
      M.map φ *ᵥ (φ ∘ v) = φ ∘ (M *ᵥ v) := by
    intro a b M v; funext i; exact (RingHom.map_mulVec φ M v i).symm
  have vm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin a → E),
      (φ ∘ v) ᵥ* M.map φ = φ ∘ (v ᵥ* M) := by
    intro a b M v; funext i; exact (RingHom.map_vecMul φ M v i).symm
  have z : ∀ {a : ℕ}, φ ∘ (0 : Fin a → E) = 0 := by
    intro a; funext i; simp
  have k1 : A'.map φ * A.map φ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have k2 : A'.map φ *ᵥ (φ ∘ x) = 0 := by rw [mv, h2, z]
  have k3 : (φ ∘ u) ᵥ* A.map φ = 0 := by rw [vm, h3, z]
  have k4 : (φ ∘ u) ⬝ᵥ (φ ∘ x) = 1 := by rw [← RingHom.map_dotProduct, h4, map_one]
  have k5 : vecMulVec (φ ∘ x) (φ ∘ u) + A.map φ * A'.map φ = 1 := by
    rw [← Matrix.map_one φ (map_zero φ) (map_one φ), ← h5, ← Matrix.map_mul]
    ext i j; simp [vecMulVec_apply, Matrix.mul_apply]
  obtain ⟨j, hj, hr⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer R σ n m (J.map φ) (J'.map φ) (φ ∘ x) (φ ∘ u) (A.map φ) (A'.map φ)
    (by
      change IsUnit ((fun i => σ (φ (x i))) ⬝ᵥ _)
      rw [hsx, mv, ← RingHom.map_dotProduct]
      exact (IsUnit.mk0 _ hx).map φ)
    (by
      change (fun i => σ (φ (x i))) ᵥ* _ = 0
      rw [hsx, ← Matrix.map_mul, vm, hxA, z])
    (by rw [hcT, mv, mv, h6, z])
    (by rw [hcT, ← Matrix.map_mul, ← Matrix.map_mul, hA])
    k1 k2 k3 k4 k5
  refine ⟨j, fun g => ⟨?_, ?_⟩, hr⟩
  · change _ *ᵥ (φ ∘ x) = φ ∘ x
    rw [hj, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, k2, Matrix.mulVec_zero, add_zero,
      Matrix.vecMulVec_mulVec, k4]
    simp
  · rw [hj, Matrix.add_mul, Matrix.mul_assoc, k1, Matrix.mul_one, Matrix.vecMulVec_mul, k3]
    ext a b; simp [vecMulVec_apply]

theorem exists_finEmb : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∃ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf ∧ ∀ h : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → h ∈ jf.range := by
  intro I D s x A xf h
  obtain ⟨hn, hx, hxA, hA, -, -⟩ := h
  have hσ : ∀ a : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    have : I.cm.sig a = star a := rfl
    simp [Formalism.UG.sigR, Formalism.UG.inclE, this]
  have hx' : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hx]; cases s <;> simp [sgn]
  exact exists_stab_emb_baseChange (Formalism.UG.inclE (F := I.F) (Af I.F)) (Formalism.UG.sigR I.cm.sig (Af I.F)) hσ
    I.J D.J x A hn I.J_herm D.J_det hx' hxA hA

end GlobalTheory.StabUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicOrthogonalStabilizerEmbeddingStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelic_orthogonal_stabilizer_embedding : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∃ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf ∧ ∀ h : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → h ∈ jf.range := by
  first | exact @GlobalTheory.StabUnfold.exists_finEmb | exact GlobalTheory.StabUnfold.exists_finEmb | (intros; apply GlobalTheory.StabUnfold.exists_finEmb <;> assumption)
end
end
