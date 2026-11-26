module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.MeasurePreservingOfAddEquiv

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.AnnihilatorDuality
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin.DualA

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc Filter Topology
open scoped TensorProduct Matrix


open Classical in
theorem setIntegral_char_subgroup {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (ν : Measure G) [ν.IsAddRightInvariant] (Λ : AddSubgroup G) (hΛ : MeasurableSet (Λ : Set G))
    (χ : G → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) :
    ∫ x in (Λ : Set G), χ x ∂ν = if ∀ x ∈ Λ, χ x = 1 then ((ν.real Λ : ℝ) : ℂ) else 0 := by
  split_ifs with h
  · rw [setIntegral_congr_fun hΛ (fun x hx => h x hx), setIntegral_const]
    simp
  · push Not at h
    obtain ⟨x0, hx0, hne⟩ := h
    have h3 : ∀ x, (Λ : Set G).indicator χ (x + x0) = χ x0 * (Λ : Set G).indicator χ x := by
      intro x
      simp only [Set.indicator]
      by_cases hx : x ∈ Λ
      · have : x + x0 ∈ Λ := Λ.add_mem hx hx0
        simp only [SetLike.mem_coe, hx, this, if_true, hχ, mul_comm]
      · have : x + x0 ∉ Λ := fun h' => hx (by simpa using Λ.sub_mem h' hx0)
        simp only [SetLike.mem_coe, hx, this, if_false, mul_zero]
    have key : ∫ x in (Λ : Set G), χ x ∂ν = χ x0 * ∫ x in (Λ : Set G), χ x ∂ν := by
      calc ∫ x in (Λ : Set G), χ x ∂ν = ∫ x, (Λ : Set G).indicator χ x ∂ν := (integral_indicator hΛ).symm
        _ = ∫ x, (Λ : Set G).indicator χ (x + x0) ∂ν := (integral_add_right_eq_self _ x0).symm
        _ = ∫ x, χ x0 * (Λ : Set G).indicator χ x ∂ν := by simp_rw [h3]
        _ = χ x0 * ∫ x, (Λ : Set G).indicator χ x ∂ν := integral_const_mul _ _
        _ = χ x0 * ∫ x in (Λ : Set G), χ x ∂ν := by rw [integral_indicator hΛ]
    have : (1 - χ x0) * ∫ x in (Λ : Set G), χ x ∂ν = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (sub_eq_zero.1 h1).symm hne
    · exact h1

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance secondCountable_mat (v : HeightOneSpectrum (𝓞 F)) (p q : ℕ) :
    SecondCountableTopology (Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E)) :=
  inferInstanceAs (SecondCountableTopology (Fin p → Fin q → Fv F v ⊗[F] E))

instance secondCountable_herm (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (n : ℕ) :
    SecondCountableTopology (HermR (Fv F v) σ n) :=
  TopologicalSpace.Subtype.secondCountableTopology (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))

section Pair

variable (R : Type) [CommRing R] [Algebra F R] {n : ℕ}

theorem trPair_comm (S T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : trPair R S T = trPair R T S := by
  unfold trPair
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem trPair_add_right (S T T' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair R S (T + T') = trPair R S T + trPair R S T' := by
  unfold trPair
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem trPair_neg_right (S T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : trPair R S (-T) = -trPair R S T := by
  unfold trPair
  simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, map_neg]

theorem trPair_sub_right (S T T' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair R S (T - T') = trPair R S T - trPair R S T' := by
  rw [sub_eq_add_neg, trPair_add_right, trPair_neg_right, ← sub_eq_add_neg]

theorem trPair_add_left (S S' T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair R (S + S') T = trPair R S T + trPair R S' T := by
  rw [trPair_comm, trPair_add_right, trPair_comm R T, trPair_comm R T]

theorem trPair_zero_right (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : trPair R S 0 = 0 := by
  unfold trPair; simp

end Pair

theorem sigma_invol' (σ : E →ₐ[F] E) (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (x : E) :
    σ (σ x) = x := by
  let τ := (Classical.arbitrary (InfinitePlace E)).embedding
  apply τ.injective
  rw [hσ, hσ, star_star]

theorem sigR_invol' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem gramR_mem' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  intro a b
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j; simp [JR, inclR, sigR, hJ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, hform, map_sum, map_mul, sigR_invol' R σ hσ, hJR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {v : HeightOneSpectrum (𝓞 F)}

theorem exists_entry_ge {p q : ℕ} {x : Fin p → Fin q → Fv F v ⊗[F] E} (h : 0 < nM v x) :
    ∃ i j, nM v x ≤ nA v (x i j) := by
  by_contra hne
  push Not at hne
  have h' : ‖(fun i j => crd v (x i j))‖ < nM v x := by
    rw [pi_norm_lt_iff h]
    intro i
    rw [pi_norm_lt_iff h]
    intro j
    exact hne i j
  exact lt_irrefl _ h'

section Inv

theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) t) = algebraMap (Fv F v) (Fv F v ⊗[F] E) t := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [sigR]

theorem sigR_smul (σ : E →ₐ[F] E) (t : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (t • x) = t • sigR (Fv F v) σ x := by
  rw [Algebra.smul_def, map_mul, sigR_algebraMap, ← Algebra.smul_def]

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (Fv F v) σ) := by
  let f : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
    { toFun := sigR (Fv F v) σ, map_add' := map_add _, map_smul' := fun t x => sigR_smul σ t x }
  exact IsModuleTopology.continuous_of_linearMap f

theorem isClosed_HermR' (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) := by
  have : (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) =
      ⋂ a, ⋂ b, {S | sigR (Fv F v) σ (S b a) = S a b} := by
    ext S; simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq ((continuous_sigR σ).comp ((continuous_apply a).comp (continuous_apply b)))
      ((continuous_apply b).comp (continuous_apply a))

theorem trace_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (x : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ x) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x := by
  let f : (Fv F v ⊗[F] E) →ₐ[Fv F v] (Fv F v ⊗[F] E) := Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ
  have hf : ∀ y, f y = sigR (Fv F v) σ y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => rfl
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]
  have hinv : Function.Involutive f := fun y => by
    rw [hf, hf]; exact sigR_invol' (Fv F v) σ hσ y
  have h := Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective f hinv.bijective) x
  rwa [AlgEquiv.ofBijective_apply, hf] at h

theorem trPair_smul_left {n : ℕ} (t : Fv F v) (S T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    trPair (Fv F v) (t • S) T = t * trPair (Fv F v) S T := by
  unfold trPair
  simp only [Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul]
  ring

theorem half_mul_two : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
  rw [show (2 : Fv F v) = algebraMap F (Fv F v) 2 from (map_ofNat _ 2).symm, ← map_mul]
  norm_num

theorem trPair_herm {n : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (X D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hD : D ∈ HermR (Fv F v) σ n) :
    trPair (Fv F v) (X + (X.map (sigR (Fv F v) σ))ᵀ) D =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ a, ∑ c, X a c * D c a) := by
  have hD' : ∀ a b, sigR (Fv F v) σ (D b a) = D a b := hD
  have h2 : ∑ a, ∑ c, sigR (Fv F v) σ (X c a) * D c a =
      ∑ a, ∑ c, sigR (Fv F v) σ (X a c) * sigR (Fv F v) σ (D c a) := by
    rw [Finset.sum_comm]; simp_rw [hD']
  have h1 : ∑ a, ∑ c, (X + (X.map (sigR (Fv F v) σ))ᵀ) a c * D c a =
      (∑ a, ∑ c, X a c * D c a) + sigR (Fv F v) σ (∑ a, ∑ c, X a c * D c a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, add_mul, Finset.sum_add_distrib, map_sum,
      map_mul]
    rw [h2]
  unfold trPair
  rw [h1, map_add (f := _), trace_sigR σ hσ, ← two_mul, ← mul_assoc, half_mul_two, one_mul]

end Inv

variable (v)

def ballH (σ : E →ₐ[F] E) (n : ℕ) (R : ℝ) (hR : 0 ≤ R) : AddSubgroup (HermR (Fv F v) σ n) where
  carrier := {b | nM v b.1 ≤ R}
  zero_mem' := by
    show nM v (0 : Fin n → Fin n → Fv F v ⊗[F] E) ≤ R
    rw [nM_zero]; exact hR
  add_mem' := fun {a b} ha hb => (nM_add_le a.1 b.1).trans (max_le ha hb)
  neg_mem' := fun {a} ha => (le_of_eq (nM_neg (v := v) (a.1 : Fin n → Fin n → Fv F v ⊗[F] E))).trans ha

theorem coe_ballH (σ : E →ₐ[F] E) (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (ballH v σ n R hR : Set (HermR (Fv F v) σ n)) = Subtype.val ⁻¹' {x | nM v x ≤ R} := rfl

theorem isCompact_ballH (σ : E →ₐ[F] E) (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (ballH v σ n R hR : Set (HermR (Fv F v) σ n)) := by
  rw [coe_ballH]
  exact (isClosed_HermR' σ n).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_ballM R)

theorem isOpen_ballH (σ : E →ₐ[F] E) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    IsOpen (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)) := by
  rw [coe_ballH]
  exact IsOpen.preimage (X := HermR (Fv F v) σ n) continuous_subtype_val (isOpen_ballM (v := v) (p := n) (q := n) hR)

theorem perp_bound (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (n : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ R : ℝ, 0 < R → ∀ D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), D ∈ HermR (Fv F v) σ n →
      (∀ b : HermR (Fv F v) σ n, nM v b.1 ≤ R → psiV F ψ v (trPair (Fv F v) b.1 D) = 1) → nM v D ≤ C₀ / R := by
  obtain ⟨y0, hy0⟩ := exists_psiV_ne_one (v := v) hcm hψ
  obtain ⟨c, hc, htr⟩ := exists_trace_ge (E := E) v
  obtain ⟨Cσ, hCσ0, hCσ⟩ := exists_nA_sig v σ
  have hσ : ∀ x, σ (σ x) = x := sigma_invol' σ hcm.2.2.2
  have hy0n : 0 < ‖y0‖ := by
    rw [norm_pos_iff]; rintro rfl; exact hy0 (psiV_zero ψ)
  set C1 : ℝ := max 1 Cσ with hC1
  have hC1pos : 0 < C1 := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨‖y0‖ * C1 / c, by positivity, ?_⟩
  intro R hR D hD hperp
  by_contra hlt
  push Not at hlt
  have hpos : 0 < nM v D := lt_of_le_of_lt (by positivity) hlt
  have key : ‖y0‖ * C1 < c * nM v D * R := by
    rw [div_lt_iff₀ hR, div_lt_iff₀ hc] at hlt; linarith
  obtain ⟨i, j, hij⟩ := exists_entry_ge hpos
  obtain ⟨a', ha'1, ha'2⟩ := htr (D i j)
  set w := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a' * D i j) with hw
  have hwpos : c * nM v D ≤ ‖w‖ := le_trans (mul_le_mul_of_nonneg_left hij hc.le) ha'2
  have hcD : 0 < c * nM v D := mul_pos hc hpos
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwpos; linarith
  let X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := Matrix.of fun a b => if a = j ∧ b = i then a' else 0
  let M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := X + (X.map (sigR (Fv F v) σ))ᵀ
  let t : Fv F v := y0 / w
  have hX : ∀ a b, nA v (X a b) ≤ 1 := by
    intro a b
    simp only [X, Matrix.of_apply]
    split_ifs
    · exact ha'1
    · rw [nA_zero]; exact zero_le_one
  have hMle : nM v M ≤ C1 := by
    refine (nM_le_iff (v := v) (x := (M : Fin n → Fin n → Fv F v ⊗[F] E)) hC1pos.le).2 ?_
    intro a b
    simp only [M, Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine (nA_add_le _ _).trans (max_le ((hX a b).trans (le_max_left _ _)) ?_)
    calc nA v (sigR (Fv F v) σ (X b a)) ≤ Cσ * nA v (X b a) := hCσ _
      _ ≤ Cσ * 1 := mul_le_mul_of_nonneg_left (hX b a) hCσ0
      _ = Cσ := mul_one _
      _ ≤ C1 := le_max_right _ _
  have hM : t • M ∈ HermR (Fv F v) σ n := by
    intro a b
    simp only [M, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, sigR_smul, map_add (f := _),
      sigR_invol' (Fv F v) σ hσ]
    rw [add_comm]
  have hnM : nM v (t • M) ≤ R := by
    have e1 : nM v (t • M) = ‖t‖ * nM v M := nM_smul t M
    rw [e1, norm_div]
    calc ‖y0‖ / ‖w‖ * nM v M ≤ ‖y0‖ / ‖w‖ * C1 := by gcongr
      _ ≤ ‖y0‖ / (c * nM v D) * C1 := by gcongr
      _ ≤ R := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hcD]; linarith
  have hsum : ∑ a, ∑ c, X a c * D c a = a' * D i j := by
    simp [X, Matrix.of_apply, ite_and]
  have hval : trPair (Fv F v) (t • M) D = y0 := by
    rw [trPair_smul_left, trPair_herm σ hσ X D hD, hsum, ← hw]
    exact div_mul_cancel₀ y0 hw0
  have h := hperp ⟨t • M, hM⟩ hnM
  rw [hval] at h
  exact hy0 h

section Units

variable {v}

theorem continuous_algNorm : Continuous (fun x : Fv F v ⊗[F] E => Algebra.norm (Fv F v) x) := by
  classical
  let b := bA E v
  have h : (fun x : Fv F v ⊗[F] E => Algebra.norm (Fv F v) x) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun x : Fv F v ⊗[F] E => Algebra.leftMulMatrix b x i j) =
      fun x => (b.coord i) ((LinearMap.mulRight (Fv F v) (b j)) x) := by
    funext x; rw [Algebra.leftMulMatrix_eq_repr_mul]; rfl
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight (Fv F v) (b j)))

theorem isUnit_iff_algNorm (x : Fv F v ⊗[F] E) : IsUnit x ↔ IsUnit (Algebra.norm (Fv F v) x) := by
  constructor
  · intro h; exact h.map (Algebra.norm (Fv F v))
  · intro h
    have h1 : IsUnit (Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) x) := by
      rw [LinearMap.isUnit_iff_isUnit_det]; exact h
    obtain ⟨u, hu⟩ := h1
    have key := LinearMap.congr_fun u.mul_inv 1
    rw [hu] at key
    exact IsUnit.of_mul_eq_one _ (by simpa using key)

theorem isOpen_unitHerm' (σ : E →ₐ[F] E) (n : ℕ) :
    IsOpen {S : HermR (Fv F v) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} := by
  have hU : IsOpen {x : Fv F v ⊗[F] E | IsUnit x} := by
    have : {x : Fv F v ⊗[F] E | IsUnit x} = (fun x => Algebra.norm (Fv F v) x) ⁻¹' {r | r ≠ 0} := by
      ext x; simp [isUnit_iff_algNorm]
    rw [this]; exact isOpen_ne.preimage continuous_algNorm
  exact (hU.preimage continuous_id.matrix_det).preimage continuous_subtype_val

theorem exists_ballH_sub {σ : E →ₐ[F] E} {n : ℕ} {T : HermR (Fv F v) σ n} {U : Set (HermR (Fv F v) σ n)}
    (hU : U ∈ 𝓝 T) : ∃ r > 0, ∀ S : HermR (Fv F v) σ n, nM v (S.1 - T.1) ≤ r → S ∈ U := by
  rw [mem_nhds_subtype] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  have h0 : {x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | T.1 + x ∈ W} ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) _) := by
    have hc : Continuous fun x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) => T.1 + x := continuous_const.add continuous_id
    have := hc.continuousAt (x := 0) (by simpa using hW)
    exact this
  obtain ⟨r, hr, hsub⟩ := exists_ballM_subset (v := v) (p := n) (q := n) h0
  refine ⟨r, hr, fun S hS => hWU ?_⟩
  have h1 : T.1 + (S.1 - T.1) ∈ W := hsub (show nM v (S.1 - T.1 : Fin n → Fin n → Fv F v ⊗[F] E) ≤ r from hS)
  rwa [add_sub_cancel] at h1

end Units

section Cont

variable {v}

theorem continuous_trace : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))

theorem continuous_trPair {n : ℕ} {α : Type*} [TopologicalSpace α] {f g : α → Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => trPair (Fv F v) (f a) (g a) := by
  unfold trPair
  refine continuous_const.mul (continuous_trace.comp ?_)
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp hf)).mul
    ((continuous_apply i).comp ((continuous_apply j).comp hg))

theorem continuous_gramR' (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun X : Fin n → Fin M → Fv F v ⊗[F] E => gramR (Fv F v) σ J X) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gramR, hR, hform]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_sigR σ).comp ((continuous_apply i).comp (continuous_apply a))).mul
    continuous_const).mul ((continuous_apply j).comp (continuous_apply b))

end Cont

end PositivityTheory.SiegelWeilFormula.SwLocFin.DualA
end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin.DualA

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {n : ℕ} {ψ : AddChar (AF F) ℂ}
  {v : HeightOneSpectrum (𝓞 F)} {μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)} {νv : Measure (HermR (Fv F v) σ n)}
  {Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ}

theorem uu_eq (T b : HermR (Fv F v) σ n) :
    uu σ J ψ v μv Φv T b =
      ∫ Y, Φv Y * psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)) ∂μv := by
  unfold uu jtR
  rw [← integral_mul_const]
  congr 1; funext Y
  rw [mul_assoc, ← psiV_add, trPair_sub_right, trPair_comm (Fv F v) T.1 b.1, sub_eq_add_neg]

theorem psiV_trPair_add_left (ψ : AddChar (AF F) ℂ) (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (b b' : HermR (Fv F v) σ n) :
    psiV F ψ v (trPair (Fv F v) (b + b').1 S) = psiV F ψ v (trPair (Fv F v) b.1 S) * psiV F ψ v (trPair (Fv F v) b'.1 S) := by
  rw [← psiV_add, ← trPair_add_left]; rfl

variable {lam : Measure (Fin n → Fv F v ⊗[F] E)} {L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)}
  {g : HermR (Fv F v) σ n → ℂ} {T : HermR (Fv F v) σ n}

def setP (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (HermR (Fv F v) σ n)) (T : HermR (Fv F v) σ n) : Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
  {Y | ∀ b ∈ Λ, psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)) = 1}

theorem isClosed_setP (hψ : IsCharAF F ψ) (Λ : Set (HermR (Fv F v) σ n)) (T : HermR (Fv F v) σ n) :
    IsClosed (setP σ J ψ v Λ T) := by
  have : setP σ J ψ v Λ T = ⋂ b ∈ Λ, {Y | psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)) = 1} := by
    ext Y; simp [setP]
  rw [this]
  exact isClosed_biInter fun b _ => isClosed_eq ((continuous_psiV hψ).comp
    (continuous_trPair continuous_const ((continuous_gramR' σ J).sub continuous_const))) continuous_const

theorem setIntegral_uu (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) (R : ℝ) (hR : 0 < R) :
    ∫ b in (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)), uu σ J ψ v μv Φv T b ∂νv =
      ((νv.real (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) *
        ∫ Y in setP σ J ψ v (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)) T, Φv Y ∂μv := by
  have := h.sdH.1
  have := h.sdW.1
  set Λ := ballH v σ n R hR.le with hΛdef
  have hΛc : IsCompact (Λ : Set (HermR (Fv F v) σ n)) := isCompact_ballH v σ n R hR.le
  have hΛm : MeasurableSet (Λ : Set (HermR (Fv F v) σ n)) := hΛc.isClosed.measurableSet
  have hfin : νv (Λ : Set (HermR (Fv F v) σ n)) < ⊤ := hΛc.measure_lt_top
  haveI : IsFiniteMeasure (νv.restrict (Λ : Set (HermR (Fv F v) σ n))) := isFiniteMeasure_restrict.2 hfin.ne
  let f : HermR (Fv F v) σ n → (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun b Y => Φv Y * psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1))
  have hΦc : Continuous Φv := h.sb.1.continuous
  have hΦi : Integrable Φv μv := hΦc.integrable_of_hasCompactSupport h.sb.2
  have hψc := continuous_psiV (v := v) h.chr
  have hfc : Continuous (Function.uncurry f) :=
    (hΦc.comp continuous_snd).mul (hψc.comp (continuous_trPair (continuous_subtype_val.comp continuous_fst)
      (((continuous_gramR' σ J).comp continuous_snd).sub continuous_const)))
  have hint : Integrable (Function.uncurry f) ((νv.restrict (Λ : Set (HermR (Fv F v) σ n))).prod μv) := by
    refine Integrable.mono' ((integrable_const (1 : ℂ)).mul_prod hΦi).norm hfc.aestronglyMeasurable ?_
    filter_upwards with p
    simp [f, Function.uncurry, norm_psiV h.chr]
  have hPm : MeasurableSet (setP σ J ψ v (Λ : Set (HermR (Fv F v) σ n)) T) :=
    (isClosed_setP h.chr _ T).measurableSet
  calc ∫ b in (Λ : Set (HermR (Fv F v) σ n)), uu σ J ψ v μv Φv T b ∂νv
      = ∫ b in (Λ : Set (HermR (Fv F v) σ n)), ∫ Y, f b Y ∂μv ∂νv := by
        congr 1; funext b; exact uu_eq T b
    _ = ∫ Y, ∫ b in (Λ : Set (HermR (Fv F v) σ n)), f b Y ∂νv ∂μv := integral_integral_swap hint
    _ = ∫ Y, ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) *
          (setP σ J ψ v (Λ : Set (HermR (Fv F v) σ n)) T).indicator Φv Y ∂μv := by
        congr 1; funext Y
        simp only [f]
        rw [integral_const_mul, setIntegral_char_subgroup νv Λ hΛm
          (fun b => psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)))
          (fun b b' => psiV_trPair_add_left ψ _ b b')]
        by_cases hP : ∀ b ∈ Λ, psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)) = 1
        · rw [if_pos hP, Set.indicator_of_mem (show Y ∈ setP σ J ψ v (Λ : Set (HermR (Fv F v) σ n)) T from
            fun b hb => hP b hb)]
          ring
        · rw [if_neg hP, Set.indicator_of_notMem (show Y ∉ setP σ J ψ v (Λ : Set (HermR (Fv F v) σ n)) T from
            fun h' => hP fun b hb => h' b hb)]
          ring
    _ = ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) *
          ∫ Y in setP σ J ψ v (Λ : Set (HermR (Fv F v) σ n)) T, Φv Y ∂μv := by
        rw [integral_const_mul, integral_indicator hPm]

def perpH (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (HermR (Fv F v) σ n)) :
    Set (HermR (Fv F v) σ n) :=
  {D | ∀ b ∈ Λ, psiV F ψ v (trPair (Fv F v) b.1 D.1) = 1}

theorem isClosed_perpH (hψ : IsCharAF F ψ) (Λ : Set (HermR (Fv F v) σ n)) : IsClosed (perpH σ ψ v Λ) := by
  have : perpH σ ψ v Λ = ⋂ b ∈ Λ, {D : HermR (Fv F v) σ n | psiV F ψ v (trPair (Fv F v) b.1 D.1) = 1} := by
    ext D; simp [perpH]
  rw [this]
  exact isClosed_biInter fun b _ => isClosed_eq ((continuous_psiV hψ).comp
    (continuous_trPair continuous_const continuous_subtype_val)) continuous_const

theorem perpH_subset {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hperp : ∀ R : ℝ, 0 < R → ∀ D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), D ∈ HermR (Fv F v) σ n →
      (∀ b : HermR (Fv F v) σ n, nM v b.1 ≤ R → psiV F ψ v (trPair (Fv F v) b.1 D) = 1) → nM v D ≤ C₀ / R)
    (R : ℝ) (hR : 0 < R) :
    perpH σ ψ v (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)) ⊆
      (ballH v σ n (C₀ / R) (div_nonneg hC₀ hR.le) : Set (HermR (Fv F v) σ n)) :=
  fun D hD => hperp R hR D.1 D.2 (fun b hb => hD b hb)

theorem isCompact_perpH (hψ : IsCharAF F ψ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hperp : ∀ R : ℝ, 0 < R → ∀ D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), D ∈ HermR (Fv F v) σ n →
      (∀ b : HermR (Fv F v) σ n, nM v b.1 ≤ R → psiV F ψ v (trPair (Fv F v) b.1 D) = 1) → nM v D ≤ C₀ / R)
    (R : ℝ) (hR : 0 < R) : IsCompact (perpH σ ψ v (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n))) :=
  (isCompact_ballH v σ n (C₀ / R) (div_nonneg hC₀ hR.le)).of_isClosed_subset (isClosed_perpH hψ _)
    (perpH_subset hC₀ hperp R hR)

theorem vol_mul_vol_perp (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) (R : ℝ) (hR : 0 < R) :
    νv.real (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)) *
      νv.real (perpH σ ψ v (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n))) = 1 := by
  have := h.sdH.1
  obtain ⟨C₀, hC₀, hperp⟩ := perp_bound v σ h.cm h.chr n
  set Λ := ballH v σ n R hR.le with hΛdef
  have hΛc : IsCompact (Λ : Set (HermR (Fv F v) σ n)) := isCompact_ballH v σ n R hR.le
  have hΛo : IsOpen (Λ : Set (HermR (Fv F v) σ n)) := isOpen_ballH v σ n R hR
  have hΛm : MeasurableSet (Λ : Set (HermR (Fv F v) σ n)) := hΛc.isClosed.measurableSet
  have hPc : IsCompact (perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n))) := isCompact_perpH h.chr hC₀ hperp R hR
  have hPm : MeasurableSet (perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n))) := hPc.isClosed.measurableSet
  let Φ0 : HermR (Fv F v) σ n → ℂ := (Λ : Set (HermR (Fv F v) σ n)).indicator (fun _ => 1)
  have hΦ0c : Continuous Φ0 := IsClopen.continuous_indicator ⟨hΛc.isClosed, hΛo⟩ continuous_const
  have hΦ0s : HasCompactSupport Φ0 := HasCompactSupport.intro hΛc (fun x hx => Set.indicator_of_notMem hx _)
  have hhat : (fun y => ∫ x, Φ0 x * psiV F ψ v (pairHerm (Fv F v) σ n x y) ∂νv) =
      (perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n))).indicator
        (fun _ => ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ)) := by
    funext y
    have e1 : ∫ x, Φ0 x * psiV F ψ v (pairHerm (Fv F v) σ n x y) ∂νv =
        ∫ x in (Λ : Set (HermR (Fv F v) σ n)), psiV F ψ v (trPair (Fv F v) x.1 y.1) ∂νv := by
      rw [← integral_indicator hΛm]
      congr 1; funext x
      simp only [Φ0]
      by_cases hx : x ∈ (Λ : Set (HermR (Fv F v) σ n))
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]; rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
    rw [e1, setIntegral_char_subgroup νv Λ hΛm (fun x => psiV F ψ v (trPair (Fv F v) x.1 y.1))
      (fun b b' => psiV_trPair_add_left ψ y.1 b b')]
    by_cases hy : ∀ x ∈ Λ, psiV F ψ v (trPair (Fv F v) x.1 y.1) = 1
    · rw [if_pos hy, Set.indicator_of_mem (show y ∈ perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n)) from
        fun b hb => hy b hb)]
    · rw [if_neg hy, Set.indicator_of_notMem (show y ∉ perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n)) from
        fun h' => hy fun b hb => h' b hb)]
  have hint : Integrable (fun y => ∫ x, Φ0 x * psiV F ψ v (pairHerm (Fv F v) σ n x y) ∂νv) νv := by
    rw [hhat]
    exact (integrable_indicator_iff hPm).2 (integrableOn_const hPc.measure_lt_top.ne)
  have key := h.sdH.2 Φ0 hΦ0c hΦ0s hint 0
  have hhat' := congrFun hhat
  simp only [] at key hhat'
  simp only [hhat'] at key
  have h0 : ∀ y : HermR (Fv F v) σ n, psiV F ψ v (pairHerm (Fv F v) σ n y 0) = 1 := by
    intro y
    show psiV F ψ v (trPair (Fv F v) y.1 (0 : HermR (Fv F v) σ n).1) = 1
    rw [AddSubgroup.coe_zero, trPair_zero_right, psiV_zero]
  simp only [h0, mul_one, neg_zero] at key
  have hΦ00 : Φ0 0 = 1 := by
    simp only [Φ0]
    exact Set.indicator_of_mem (show (0 : HermR (Fv F v) σ n) ∈ (Λ : Set (HermR (Fv F v) σ n)) from Λ.zero_mem) _
  rw [integral_indicator hPm, setIntegral_const, hΦ00] at key
  have key' : ((νv.real (perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n))) * νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_mul]; simpa [Complex.real_smul] using key
  rw [mul_comm]
  exact_mod_cast key'

theorem setP_eq (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) (Λ : Set (HermR (Fv F v) σ n)) :
    setP σ J ψ v Λ T =
      gramR (Fv F v) σ J ⁻¹' (Subtype.val '' {S : HermR (Fv F v) σ n | S - T ∈ perpH σ ψ v Λ}) := by
  have hσ : ∀ x, σ (σ x) = x := sigma_invol' σ h.cm.2.2.2
  ext Y
  constructor
  · intro hY
    exact ⟨⟨gramR (Fv F v) σ J Y, gramR_mem' (Fv F v) σ hσ J h.herm.1 Y⟩, fun b hb => hY b hb, rfl⟩
  · rintro ⟨S, hS, hSY⟩ b hb
    have h1 := hS b hb
    show psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)) = 1
    rw [← hSY]
    exact h1

end PositivityTheory.SiegelWeilFormula.SwLocFin.DualA

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
  PositivityTheory.SiegelWeilFormula.SwLocFin.DualA
open scoped TensorProduct Matrix

theorem dualP : DualP := by
  intro F E _ _ _ _ _ σ M J n ψ v μv νv lam L₁ L₂ Φv g T h
  have := h.sdH.1
  obtain ⟨C₀, hC₀, hperp⟩ := perp_bound v σ h.cm h.chr n
  set B := {S : HermR (Fv F v) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} with hBdef
  have hBo : IsOpen B := isOpen_unitHerm' σ n
  have hTB : T ∈ B := h.unit
  have hgc : ContinuousAt g T := (h.dens.1).continuousAt (hBo.mem_nhds hTB)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hU : {S | S ∈ B ∧ g S ∈ Metric.ball (g T) (ε / 2)} ∈ 𝓝 T :=
    Filter.inter_mem (hBo.mem_nhds hTB) (hgc.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε)))
  obtain ⟨r, hr, hsub⟩ := exists_ballH_sub hU
  refine ⟨max 1 (C₀ / r), fun R hR => ?_⟩
  have hR1 : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hR)
  have hCr : C₀ / R ≤ r := by
    rw [div_le_iff₀ hR1]
    have := (div_le_iff₀ hr).1 (le_trans (le_max_right _ _) hR)
    linarith
  set Λ := ballH v σ n R hR1.le with hΛdef
  set P := perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n)) with hPdef
  set C := {S : HermR (Fv F v) σ n | S - T ∈ P} with hCdef
  have hCsub : ∀ S ∈ C, S ∈ B ∧ g S ∈ Metric.ball (g T) (ε / 2) := fun S hS =>
    hsub S ((perpH_subset hC₀ hperp R hR1 hS).trans hCr)
  have hPc : IsCompact P := isCompact_perpH h.chr hC₀ hperp R hR1
  have hCc : IsCompact C := by
    have : C = (fun S => S - T) ⁻¹' P := rfl
    rw [this]; exact (Homeomorph.subRight T).isCompact_preimage.2 hPc
  have hνC : νv.real C = νv.real P := by
    have : C = (fun S => S + (-T)) ⁻¹' P := by ext S; simp [C, sub_eq_add_neg]
    simp only [Measure.real]
    rw [this, measure_preimage_add_right]
  have hvol : νv.real (Λ : Set (HermR (Fv F v) σ n)) * νv.real P = 1 := vol_mul_vol_perp h R hR1
  have hdens := h.dens.2 C hCc (fun S hS => (hCsub S hS).1)
  have hval : ∫ b in (Λ : Set (HermR (Fv F v) σ n)), uu σ J ψ v μv Φv T b ∂νv =
      ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) * ∫ b in C, g b ∂νv := by
    rw [setIntegral_uu h R hR1, setP_eq h, hdens]
  have hgi : IntegrableOn g C νv :=
    (h.dens.1.mono (fun S hS => (hCsub S hS).1)).integrableOn_compact hCc
  have hci : IntegrableOn (fun _ => g T) C νv := integrableOn_const hCc.measure_lt_top.ne
  have hdiff : ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) * ∫ b in C, g b ∂νv - g T =
      ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) * ∫ b in C, (g b - g T) ∂νv := by
    rw [integral_sub hgi hci, setIntegral_const, mul_sub, hνC, Complex.real_smul, ← mul_assoc,
      ← Complex.ofReal_mul, hvol, Complex.ofReal_one, one_mul]
  have hbound : ‖∫ b in C, (g b - g T) ∂νv‖ ≤ ε / 2 * νv.real C := by
    refine norm_setIntegral_le_of_norm_le_const hCc.measure_lt_top (fun S hS => ?_)
    have := (hCsub S hS).2
    rw [Metric.mem_ball, dist_eq_norm] at this
    exact this.le
  rw [dist_eq_norm]
  show ‖∫ b in (Λ : Set (HermR (Fv F v) σ n)), uu σ J ψ v μv Φv T b ∂νv - g T‖ < ε
  rw [hval, hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg measureReal_nonneg]
  calc νv.real (Λ : Set (HermR (Fv F v) σ n)) * ‖∫ b in C, (g b - g T) ∂νv‖
      ≤ νv.real (Λ : Set (HermR (Fv F v) σ n)) * (ε / 2 * νv.real C) :=
        mul_le_mul_of_nonneg_left hbound measureReal_nonneg
    _ = ε / 2 * (νv.real (Λ : Set (HermR (Fv F v) σ n)) * νv.real P) := by rw [hνC]; ring
    _ = ε / 2 := by rw [hvol, mul_one]
    _ < ε := half_lt_self hε

end PositivityTheory.SiegelWeilFormula.SwLocFin
