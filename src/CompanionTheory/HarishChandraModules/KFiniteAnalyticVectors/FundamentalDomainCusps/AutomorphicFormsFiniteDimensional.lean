module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LocalPointData
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.FiniteDimensionalFromLinearForms
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ParabolicSubgroupDecomposition
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LogBallEstimates
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.RealParabolicDecomposition

@[expose] public section

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.CuspidalAtInfinityOf
open MeasureTheory Topology Filter Set Matrix NumberField
open scoped ENNReal Pointwise

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows Formalism.MainNotions.LeviCoordinates

theorem cuspidal_at_infinity_of : Sel → Avg → NWSub → RealPar → ParPi → Transp → GamSub → GeoInf → CuspInf := by
  classical
  intro hSel hAvg hNW hRP hPi hT hGam hGeo I M hM ph hph hconv U hU
  obtain ⟨K, hKn, hKU, hK⟩ := local_compact_nhds hU
  obtain ⟨C, hC, hy⟩ := hGeo I M hM (interior K) (interior_mem_nhds.2 hKn)
  refine ⟨C, hC, fun y => (hy y).imp_right ?_⟩
  rintro ⟨W, hW0, hWi, hcov⟩
  obtain ⟨-, -, -, hperp, hne, -⟩ := hT I
  have hiso : ∀ v, Isot (Formalism.REAL.Jm (I.ε v)) (Wv I W v) := fun v => by
    unfold Isot
    rw [← hperp]
    exact Submodule.span_mono (image_mono hWi)
  choose Nv hNv using fun v => (hNW _ _ _ (hiso v)).2
  let N : Subgroup I.Ginf := Subgroup.pi univ Nv
  have hNm : ∀ g, g ∈ N ↔ g ∈ NInf I W := fun g => by
    simp only [N, Subgroup.mem_pi, mem_univ, forall_true_left, NInf, mem_ofPred_eq, ← hNv, SetLike.mem_coe]
  have hNc : IsClosed (N : Set I.Ginf) := by
    rw [Subgroup.coe_pi]
    exact isClosed_set_pi fun v _ => by rw [hNv]; exact (hNW _ _ _ (hiso v)).1
  obtain ⟨Γ, hΓ, hΓd⟩ := hGam I M
  have hc : Continuous fun m : I.Ginf => y⁻¹ * m * y := by fun_prop
  have hcK : IsCompact ((fun m : I.Ginf => y⁻¹ * m * y) ⁻¹' K) :=
    (((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)).isCompact_preimage).2 hK
  obtain ⟨ν, hν, hνV, hinv⟩ := hAvg I.Ginf N (Γ ⊓ N) hNc inf_le_right
    (fun B hB => (hΓd B hB).subset fun x hx => ⟨hx.1, hx.2.1⟩) ((fun m => y⁻¹ * m * y) ⁻¹' interior K)
    (isOpen_interior.preimage hc)
    (hcK.of_isClosed_subset isClosed_closure (closure_minimal (preimage_mono interior_subset) hcK.isClosed))
    fun m hm => by
      obtain ⟨γ, hγ, hγN, h⟩ := hcov m ((hNm m).1 hm)
      exact ⟨γ, ⟨hΓ.ge hγ, (hNm γ).2 hγN⟩, h⟩
  refine ⟨ν, hν, hνV.mono fun m hm => hKU (interior_subset hm), fun u hu huΓ hrep x => ?_⟩
  obtain ⟨huc, B, hB⟩ := id hu
  have hc2 : Continuous fun p : I.Ginf × I.Ginf => u (p.1 * p.2) := huc.comp continuous_mul
  let F : I.Ginf → ℂ := fun x => ∫ m, u (m * x) ∂ν
  have hFb : BC F := ⟨continuous_of_dominated (bound := fun _ => B)
      (fun x => (hc2.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (fun x => Eventually.of_forall fun _ => hB _) (integrable_const _)
      (Eventually.of_forall fun m => hc2.comp (continuous_const.prodMk continuous_id)),
    B, fun x => by simpa using norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall fun m => hB (m * x))⟩
  have hFN : LInv N F := fun m hm x => hinv u hu (fun γ hγ => huΓ γ (by rw [← hΓ]; exact hγ.1)) m hm x
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  obtain ⟨a, Ht, P⟩ := hRP _ _ _ (hne v₀ W hW0) (hiso v₀) (Nv v₀) (hNv v₀)
  have h0 := hSel I.Ginf (muInf I) ph hph hconv _ _ _ (hPi _ _ v₀ _ a Ht P) F hFb (by
    rintro _ ⟨m, hm, rfl⟩
    refine hFN _ fun v _ => ?_
    by_cases hv : v = v₀
    · subst hv; simpa using hm
    · simp [Pi.mulSingle_eq_of_ne hv]) x
  have hI : Integrable (fun p : I.Ginf × I.Ginf => ph p.2 * u (p.1 * x * p.2)) (ν.prod (muInf I)) :=
    (hph.comp_snd ν).mul_bdd
      (huc.comp (by fun_prop) : Continuous fun p : I.Ginf × I.Ginf => u (p.1 * x * p.2)).aestronglyMeasurable
      (Eventually.of_forall fun _ => hB _)
  rw [← h0, integral_congr_ae (Eventually.of_forall fun m => hrep (m * x)), integral_integral_swap hI]
  simp only [F, integral_const_mul, mul_assoc]

theorem level_structure_of : LevelOf := by
  intro I e hlc hs
  let K : Subgroup I.Gf := (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype
  have hK : IsCompact (K : Set I.Gf) := PI.WAU.maximal_compact_isCompact I
  have hKo : IsOpen (K : Set I.Gf) := Formalism.L2.SG.Pf.kset_open I
  let Kp : Subgroup I.Gf :=
    { carrier := {k | k ∈ K ∧ ∀ x, e (k * x) = e x}
      mul_mem' := fun ha hb => ⟨K.mul_mem ha.1 hb.1, fun x => by rw [mul_assoc, ha.2, hb.2]⟩
      one_mem' := ⟨K.one_mem, fun x => by rw [one_mul]⟩
      inv_mem' := fun {k} hk => ⟨K.inv_mem hk.1, fun x => by rw [← hk.2 (k⁻¹ * x), mul_inv_cancel_left]⟩ }
  have h1 : ∀ᶠ k in 𝓝 (1 : I.Gf), ∀ x ∈ (K : Set I.Gf), e (k * x) = e x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have a1 := (hlc.comp_continuous (continuous_mul (M := I.Gf))).eventually_eq (1, x)
    have a2 := (hlc.comp_continuous (continuous_snd (X := I.Gf))).eventually_eq (1, x)
    filter_upwards [a1, a2] with p h1 h2
    simp only [Function.comp_apply, one_mul] at h1 h2
    rw [h1, h2]
  have hop : IsOpen (Kp : Set I.Gf) := by
    refine Kp.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [h1, hKo.mem_nhds K.one_mem] with k hk hkK
    refine ⟨hkK, fun x => ?_⟩
    by_cases hx : x ∈ K
    · exact hk x hx
    · have a1 : e x = 0 := by by_contra h; exact hx (hs x h)
      have a2 : e (k * x) = 0 := by by_contra h; exact hx ((K.mul_mem_cancel_left hkK).1 (hs _ h))
      rw [a1, a2]
  exact ⟨Kp, hop, hK.of_isClosed_subset (Kp.isClosed_of_isOpen hop) fun k hk => hk.1, fun k hk => hk.2⟩

end CompanionTheory.D.gk.RF
end
end

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.SecondOrderExpAtInfinitePlace
section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.NilpotentSubgroupRepresentation
open Matrix

noncomputable section

namespace CompanionTheory.D.gk.RF

variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}

omit [StarRing K] in
theorem mat_extC {A B : Matrix (Fin n) (Fin n) K} (h : ∀ z, A *ᵥ z = B *ᵥ z) : A = B :=
  Matrix.ext fun i j => by simpa using congrFun (h (Pi.single j 1)) i

theorem Lowers.triple {A B C : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B)
    (hC : Lowers J W C) : A * (B * C) = 0 :=
  mat_extC fun z => by rw [← mulVec_mulVec, ← mulVec_mulVec, hA.1 _ (hB.2.1 _ (hC.2.2 z)), zero_mulVec]

theorem Lowers.add {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) : Lowers J W (A + B) :=
  ⟨fun w hw => by rw [add_mulVec, hA.1 w hw, hB.1 w hw, add_zero],
    fun z hz => by rw [add_mulVec]; exact W.add_mem (hA.2.1 z hz) (hB.2.1 z hz),
    fun z => by rw [add_mulVec]; exact (perp J W).add_mem (hA.2.2 z) (hB.2.2 z)⟩

theorem Lowers.smul {A : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (c : K) : Lowers J W (c • A) :=
  ⟨fun w hw => by rw [smul_mulVec, hA.1 w hw, smul_zero],
    fun z hz => by rw [smul_mulVec]; exact W.smul_mem c (hA.2.1 z hz),
    fun z => by rw [smul_mulVec]; exact (perp J W).smul_mem c (hA.2.2 z)⟩

theorem Lowers.neg {A : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) : Lowers J W (-A) := by
  simpa using hA.smul (-1)

theorem Lowers.mul_perp {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) :
    (∀ z ∈ perp J W, (A * B) *ᵥ z = 0) ∧ ∀ z, (A * B) *ᵥ z ∈ W :=
  ⟨fun z hz => by rw [← mulVec_mulVec, hA.1 _ (hB.2.1 z hz)],
    fun z => by rw [← mulVec_mulVec]; exact hA.2.1 _ (hB.2.2 z)⟩

theorem lowers_of_Z (hW : Isot J W) {Z : Matrix (Fin n) (Fin n) K} (h1 : ∀ z ∈ perp J W, Z *ᵥ z = 0)
    (h2 : ∀ z, Z *ᵥ z ∈ W) : Lowers J W Z :=
  ⟨fun w hw => h1 w (hW hw), fun z _ => h2 z, fun z => hW (h2 z)⟩

theorem Lowers.mul (hW : Isot J W) {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) :
    Lowers J W (A * B) := lowers_of_Z hW (hA.mul_perp hB).1 (hA.mul_perp hB).2

variable [CharZero K]

theorem second_order_exp_mul {X Y : Matrix (Fin n) (Fin n) K} (hX : Lowers J W X) (hY : Lowers J W Y) :
    ex2 X * ex2 Y = 1 + X + Y + (2 : K)⁻¹ • (X * X) + X * Y + (2 : K)⁻¹ • (Y * Y) := by
  have t1 := hX.triple hX hY
  have t2 := hX.triple hY hY
  simp only [ex2, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, t1, t2, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, smul_zero, add_zero]
  abel

omit [CharZero K] in
theorem star_half : star (2 : K)⁻¹ = (2 : K)⁻¹ := by rw [star_inv₀, star_ofNat]

omit [CharZero K] in
theorem skew_eq {X : Matrix (Fin n) (Fin n) K} (h : Xᴴ * J + J * X = 0) : Xᴴ * J = -(J * X) :=
  eq_neg_of_add_eq_zero_left h

omit [CharZero K] in
theorem skew_mul {X Y : Matrix (Fin n) (Fin n) K} (hX : Xᴴ * J + J * X = 0) (hY : Yᴴ * J + J * Y = 0) :
    (X * Y)ᴴ * J = J * (Y * X) := by
  rw [conjTranspose_mul, Matrix.mul_assoc, skew_eq hX, Matrix.mul_neg, ← Matrix.mul_assoc, skew_eq hY,
    Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

theorem nilpotent_lie_algebra : NilpAlg := by
  intro K _ _ _ n J W _ _ hW
  have inv : ∀ X, Lowers J W X → ex2 X * ex2 (-X) = 1 := fun X hX => by
    rw [second_order_exp_mul hX hX.neg]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    module
  have hneg : ∀ X, InL J W X → InL J W (-X) := fun X hX =>
    ⟨by rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX.1, neg_zero], hX.2.neg⟩
  refine ⟨fun X hX => ⟨?_, ?_, inv X hX.2, hneg X hX⟩, fun g hg hA => ?_, fun X Y hX hY => ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩,
    fun Z hZ => ⟨⟨hZ.1, lowers_of_Z hW hZ.2.1 hZ.2.2⟩, ⟨?_, fun z hz => ?_, fun z => ?_⟩, fun X hX => ⟨?_, ?_⟩⟩⟩
  · have h1 : (ex2 X)ᴴ * J = J * ex2 (-X) := by
      simp only [ex2, conjTranspose_add, conjTranspose_one, conjTranspose_smul, star_half, add_mul, mul_add,
        smul_mul_assoc, mul_smul_comm, skew_mul hX.1 hX.1, skew_eq hX.1, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    have h2 := inv _ hX.2.neg
    rw [neg_neg] at h2
    rw [h1, Matrix.mul_assoc, h2, Matrix.mul_one]
  · have : ex2 X - 1 = X + (2 : K)⁻¹ • (X * X) := by unfold ex2; abel
    rw [this]
    exact hX.2.add ((hX.2.mul hW hX.2).smul _)
  · obtain ⟨A, rfl⟩ : ∃ A, g = 1 + A := ⟨g - 1, by abel⟩
    rw [add_sub_cancel_left] at hA
    have t := hA.triple hA hA
    have h1 : (Aᴴ * J + J * (A - A * A)) * (1 + A) = 0 := by
      have e : (1 + A)ᴴ * J * (1 + A) - J = 0 := by rw [hg, sub_self]
      rw [← e]
      simp only [conjTranspose_add, conjTranspose_one, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_assoc, t,
        Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero]
      abel
    have h2 : (1 + A) * (1 - A + A * A) = 1 := by
      simp only [mul_add, add_mul, mul_sub, t, Matrix.one_mul, Matrix.mul_one]
      abel
    have h3 : Aᴴ * J = -(J * (A - A * A)) := by
      have := congrArg (· * (1 - A + A * A)) h1
      simp only [Matrix.mul_assoc _ (1 + A), h2, Matrix.mul_one, Matrix.zero_mul] at this
      exact eq_neg_of_add_eq_zero_left this
    have h4 : (A * A)ᴴ * J = J * (A * A) := by
      rw [conjTranspose_mul, Matrix.mul_assoc, h3, Matrix.mul_neg, ← Matrix.mul_assoc, h3]
      simp only [Matrix.neg_mul, neg_neg, mul_sub, sub_mul, Matrix.mul_assoc, t, Matrix.mul_zero, sub_zero,
        neg_zero]
    refine ⟨A + (-(2 : K)⁻¹) • (A * A), ⟨?_, hA.add ((hA.mul hW hA).smul _)⟩, ?_⟩
    · simp only [conjTranspose_add, conjTranspose_smul, star_neg, star_half, add_mul, mul_add, smul_mul_assoc,
        mul_smul_comm, h3, h4, mul_sub]
      module
    · simp only [ex2, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, t, Matrix.mul_zero,
        smul_zero, add_zero]
      module
  · exact ⟨by rw [conjTranspose_add, add_mul, mul_add, skew_eq hX.1, skew_eq hY.1]; abel, hX.2.add hY.2⟩
  · simp only [conjTranspose_smul, conjTranspose_sub, star_half, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub,
      skew_mul hX.1 hY.1, skew_mul hY.1 hX.1]
    module
  · intro z hz
    rw [smul_mulVec, sub_mulVec, (hX.2.mul_perp hY.2).1 z hz, (hY.2.mul_perp hX.2).1 z hz, sub_zero, smul_zero]
  · intro z
    rw [smul_mulVec, sub_mulVec]
    exact W.smul_mem _ (W.sub_mem ((hX.2.mul_perp hY.2).2 z) ((hY.2.mul_perp hX.2).2 z))
  · have a := hX.2
    have b := hY.2
    rw [second_order_exp_mul a b]
    simp only [ex2, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc,
      a.triple a a, a.triple a b, a.triple b a, a.triple b b, b.triple a a, b.triple a b, b.triple b a,
      b.triple b b, Matrix.mul_zero, smul_zero, sub_zero, add_zero, sub_self]
    module
  · rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hZ.1, neg_zero]
  · rw [neg_mulVec, hZ.2.1 z hz, neg_zero]
  · rw [neg_mulVec]; exact W.neg_mem (hZ.2.2 z)
  · exact mat_extC fun z => by rw [← mulVec_mulVec, hZ.2.1 _ (hX.2.2.2 z), zero_mulVec]
  · exact mat_extC fun z => by rw [← mulVec_mulVec, hX.2.1 _ (hZ.2.2 z), zero_mulVec]

end CompanionTheory.D.gk.RF

namespace CompanionTheory.D.gk.RF

variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}

theorem xw_mulVec (w b z : Fin n → K) : xw J w b *ᵥ z = hf J b z • w - hf J w z • b := by
  simp only [xw, sub_mulVec, vecMulVec_mulVec, hf, dotProduct_mulVec, op_smul_eq_smul]

theorem hf_star (hJ : Jᴴ = J) (x y : Fin n → K) : star (hf J x y) = hf J y x := by
  unfold hf
  rw [← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec]

theorem hf_sub_right (x y z : Fin n → K) : hf J x (y - z) = hf J x y - hf J x z := by
  simp only [hf, mulVec_sub, dotProduct_sub]

theorem hf_smul_right (c : K) (x y : Fin n → K) : hf J x (c • y) = c * hf J x y := by
  simp only [hf, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hf_sum_right {ι : Type} (s : Finset ι) (x : Fin n → K) (y : ι → Fin n → K) :
    hf J x (∑ i ∈ s, y i) = ∑ i ∈ s, hf J x (y i) := by
  simp only [hf, mulVec_sum, dotProduct_sum]

theorem hf_add_leftC (x y z : Fin n → K) : hf J (x + y) z = hf J x z + hf J y z := by
  simp only [hf, star_add, add_dotProduct]

theorem hf_neg_left (x z : Fin n → K) : hf J (-x) z = -hf J x z := by
  simp only [hf, star_neg, neg_dotProduct]

theorem hf_smul_leftC (c : K) (x y : Fin n → K) : hf J (c • x) y = star c * hf J x y := by
  simp only [hf, star_smul, smul_dotProduct, smul_eq_mul]

theorem hf_sum_left {ι : Type} (s : Finset ι) (x : ι → Fin n → K) (y : Fin n → K) :
    hf J (∑ i ∈ s, x i) y = ∑ i ∈ s, hf J (x i) y := by
  simp only [hf, star_sum, sum_dotProduct]

theorem hf_skew {X : Matrix (Fin n) (Fin n) K} (h : Xᴴ * J + J * X = 0) (x y : Fin n → K) :
    hf J (X *ᵥ x) y = -hf J x (X *ᵥ y) := by
  unfold hf
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, skew_eq h, neg_mulVec, dotProduct_neg, mulVec_mulVec]

theorem skew_of_hf {X : Matrix (Fin n) (Fin n) K} (h : ∀ x y, hf J (X *ᵥ x) y = -hf J x (X *ᵥ y)) :
    Xᴴ * J + J * X = 0 := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  unfold hf at this
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← dotProduct_neg, ← neg_mulVec] at this
  have e : star (Pi.single i 1 : Fin n → K) = Pi.single i 1 := by
    ext k; by_cases hk : k = i <;> simp [hk]
  simp only [e, mulVec_single_one, single_one_dotProduct, Matrix.col_apply, Matrix.neg_apply] at this
  simp [this]

theorem skew_xw (hJ : Jᴴ = J) (w b : Fin n → K) : (xw J w b)ᴴ * J + J * xw J w b = 0 :=
  skew_of_hf fun x y => by
    rw [xw_mulVec, xw_mulVec, sub_eq_add_neg, hf_add_leftC, hf_neg_left, hf_smul_leftC, hf_smul_leftC, hf_sub_right,
      hf_smul_right, hf_smul_right, hf_star hJ, hf_star hJ]
    ring

theorem perp_symm (hJ : Jᴴ = J) {b w : Fin n → K} (hb : b ∈ perp J W) (hw : w ∈ W) : hf J b w = 0 := by
  rw [← hf_star hJ, hb w hw, star_zero]

theorem mem_perp_spanC {ι : Type} {w : ι → Fin n → K} {z : Fin n → K} (h : ∀ i, hf J (w i) z = 0) :
    z ∈ perp J (Submodule.span K (Set.range w)) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_leftC, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_leftC, ha, mul_zero]

theorem exists_dual (hJ : Jᴴ = J) (hd : IsUnit J.det) {κ : Type} [Fintype κ] [DecidableEq κ] {v : κ → Fin n → K}
    (hv : LinearIndependent K v) : ∃ u : κ → Fin n → K, ∀ i j, hf J (u i) (v j) = if i = j then 1 else 0 := by
  have hk : LinearMap.ker (Fintype.linearCombination K v) = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hv c hc)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨fun i => J⁻¹ *ᵥ star fun k => g (Pi.single k 1) i, fun i j => ?_⟩
  have h1 : g (v j) = Pi.single j 1 := by
    have := LinearMap.congr_fun hg (Pi.single j 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have h2 : (J⁻¹)ᴴ = J⁻¹ := by rw [conjTranspose_nonsing_inv, hJ]
  unfold hf
  rw [star_mulVec, star_star, h2, dotProduct_mulVec, vecMul_vecMul, nonsing_inv_mul J hd, vecMul_one]
  have h3 : v j = ∑ k, v j k • (Pi.single k 1 : Fin n → K) := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  have h4 := congrFun h1 i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h3, map_sum, Finset.sum_apply] at h4
  rw [Pi.single_apply] at h4
  rw [← h4]
  simp only [dotProduct, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem rep_basis [CharZero K] (hJ : Jᴴ = J) (hd : IsUnit J.det) (hW : Isot J W) {κ : Type} [Fintype κ]
    [DecidableEq κ] {v : κ → Fin n → K} (hv : LinearIndependent K v) (hs : Submodule.span K (Set.range v) = W)
    {X : Matrix (Fin n) (Fin n) K} (hX : InL J W X) :
    ∃ b : κ → Fin n → K, (∀ k, b k ∈ perp J W) ∧ ((∀ z, X *ᵥ z ∈ W) → ∀ k, b k ∈ W) ∧ X = ∑ k, xw J (v k) (b k) := by
  obtain ⟨u, hu⟩ := exists_dual hJ hd hv
  have hu' : ∀ i j, hf J (v i) (u j) = if i = j then 1 else 0 := fun i j => by
    rw [← hf_star hJ, hu]; by_cases h : i = j <;> simp [h, eq_comm]
  have hvW : ∀ k, v k ∈ W := fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩
  have hexp : ∀ w ∈ W, ∑ i, hf J (u i) w • v i = w := by
    intro w hw
    rw [← hs] at hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
    simp only [hf_sum_right, hf_smul_right, hu, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  let s : κ → κ → K := fun i k => hf J (u i) (X *ᵥ u k)
  have hss : ∀ i k, star (s k i) = -s i k := fun i k => by
    simp only [s]; rw [hf_star hJ, hf_skew hX.1]
  let b : κ → Fin n → K := fun k => -(X *ᵥ u k) + ∑ i, ((2 : K)⁻¹ * s i k) • v i
  have hsum : ∀ k, ∑ i, ((2 : K)⁻¹ * s i k) • v i ∈ W := fun k =>
    W.sum_mem fun i _ => W.smul_mem _ (hvW i)
  refine ⟨b, fun k => (perp J W).add_mem ((perp J W).neg_mem (hX.2.2.2 _)) (hW (hsum k)),
    fun h k => W.add_mem (W.neg_mem (h _)) (hsum k), ?_⟩
  have e1 : ∀ z ∈ perp J W, (∑ k, xw J (v k) (b k)) *ᵥ z = X *ᵥ z := fun z hz => by
    rw [sum_mulVec, ← hexp _ (hX.2.2.1 z hz)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [xw_mulVec, hz _ (hvW k), zero_smul, sub_zero]
    simp only [b]
    rw [hf_add_leftC, hz _ (hsum k), add_zero, hf_neg_left, hf_skew hX.1, neg_neg]
  have e2 : ∀ j, (∑ k, xw J (v k) (b k)) *ᵥ u j = X *ᵥ u j := fun j => by
    have hb : ∀ k, hf J (b k) (u j) = (2 : K)⁻¹ * s k j := fun k => by
      simp only [b]
      rw [hf_add_leftC, hf_neg_left, hf_skew hX.1, neg_neg, hf_sum_left]
      simp only [hf_smul_leftC, hu', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        star_mul', star_half, hss]
      show s k j + _ = _
      ring
    rw [sum_mulVec]
    simp only [xw_mulVec, hb, hu', ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    simp only [b]
    abel
  refine mat_extC fun z => ?_
  have hz : z - ∑ j, hf J (v j) z • u j ∈ perp J W := by
    rw [← hs]
    refine mem_perp_spanC fun i => ?_
    simp only [hf_sub_right, hf_sum_right, hf_smul_right, hu', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_self]
  rw [← sub_add_cancel z (∑ j, hf J (v j) z • u j), mulVec_add, mulVec_add, e1 _ hz, mulVec_sum, mulVec_sum]
  simp only [mulVec_smul, e2]

theorem rep_span [CharZero K] (hJ : Jᴴ = J) (hd : IsUnit J.det) (hW : Isot J W) {d : ℕ} {w : Fin d → Fin n → K}
    (hs : Submodule.span K (Set.range w) = W) {X : Matrix (Fin n) (Fin n) K} (hX : InL J W X) :
    ∃ b : Fin d → Fin n → K, (∀ k, b k ∈ perp J W) ∧ ((∀ z, X *ᵥ z ∈ W) → ∀ k, b k ∈ W) ∧
      X = ∑ k, xw J (w k) (b k) := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K w
  have := Fintype.ofInjective a ha
  obtain ⟨b, h1, h2, h3⟩ := rep_basis hJ hd hW hli (hsp.trans hs) hX
  have hP : ∀ (S : Submodule K (Fin n → K)), (∀ k, b k ∈ S) → ∀ i, Function.extend a b 0 i ∈ S := fun S h i => by
    by_cases hi : ∃ k, a k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [ha.extend_apply]; exact h k
    · rw [Function.extend_apply' _ _ _ hi]; exact S.zero_mem
  refine ⟨Function.extend a b 0, hP _ h1, fun h => hP _ (h2 h), h3.trans ?_⟩
  refine Fintype.sum_of_injective a ha _ _ (fun i hi => ?_) fun k => by rw [ha.extend_apply]; rfl
  rw [Function.extend_apply' _ _ _ hi]
  simp [xw]

theorem nilpotent_subgroup_representation : NilpRep := by
  intro K _ _ _ n J W hJ hd hW d w hs
  have hwW : ∀ k, w k ∈ W := fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩
  have sk : ∀ b : Fin d → Fin n → K, (∑ i, xw J (w i) (b i))ᴴ * J + J * ∑ i, xw J (w i) (b i) = 0 := fun b => by
    rw [conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => skew_xw hJ _ _
  refine ⟨fun b hb => ⟨sk b, fun z hz => ?_, fun z hz => ?_, fun z => ?_⟩, fun b hb => ⟨sk b, fun z hz => ?_,
    fun z => ?_⟩, fun X hX => ?_, fun X hX => ?_⟩
  · rw [sum_mulVec]
    exact Finset.sum_eq_zero fun i _ => by
      rw [xw_mulVec, perp_symm hJ (hb i) hz, hW hz _ (hwW i), zero_smul, zero_smul, sub_zero]
  · rw [sum_mulVec]
    exact W.sum_mem fun i _ => by
      rw [xw_mulVec, hz _ (hwW i), zero_smul, sub_zero]; exact W.smul_mem _ (hwW i)
  · rw [sum_mulVec]
    exact (perp J W).sum_mem fun i _ => by
      rw [xw_mulVec]
      exact (perp J W).sub_mem ((perp J W).smul_mem _ (hW (hwW i))) ((perp J W).smul_mem _ (hb i))
  · rw [sum_mulVec]
    exact Finset.sum_eq_zero fun i _ => by
      rw [xw_mulVec, hz _ (hwW i), hz _ (hb i), zero_smul, zero_smul, sub_zero]
  · rw [sum_mulVec]
    exact W.sum_mem fun i _ => by
      rw [xw_mulVec]; exact W.sub_mem (W.smul_mem _ (hwW i)) (W.smul_mem _ (hb i))
  · obtain ⟨b, h1, -, h3⟩ := rep_span hJ hd hW hs hX
    exact ⟨b, h1, h3⟩
  · obtain ⟨b, -, h2, h3⟩ := rep_span hJ hd hW hs ⟨hX.1, lowers_of_Z hW hX.2.1 hX.2.2⟩
    exact ⟨b, h2 hX.2.2, h3⟩

theorem successive_minima_gap : Gap := by
  classical
  intro K _ n A ν s₀ η hs hη hη1 ⟨u₀, hu₀, hne, hν⟩
  let S : ℕ → Set (Fin n → K) := fun j => {u | u ∈ A ∧ ν u ≤ s₀ * η ^ j}
  let Wj : ℕ → Submodule K (Fin n → K) := fun j => Submodule.span K (S j)
  have hmono : ∀ j, Wj (j + 1) ≤ Wj j := fun j => Submodule.span_mono fun u hu =>
    ⟨hu.1, hu.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη.le hη1.le (Nat.le_succ j)) hs.le)⟩
  have hnz : ∀ j ≤ n + 1, Wj j ≠ ⊥ := fun j hj h => hne (by
    have : u₀ ∈ Wj j := Submodule.subset_span ⟨hu₀, hν.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη.le hη1.le hj) hs.le)⟩
    rwa [h, Submodule.mem_bot] at this)
  have hex : ∃ j ≤ n, Wj (j + 1) = Wj j := by
    by_contra hc
    push Not at hc
    have : ∀ j ≤ n + 1, Module.finrank K (Wj j) + j ≤ n := by
      intro j hj
      induction j with
      | zero => simpa using (Wj 0).finrank_le
      | succ j ih =>
        have h1 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono j) (hc j (by omega)))
        have h2 := ih (by omega)
        omega
    have := this (n + 1) le_rfl
    omega
  obtain ⟨j, hj, he⟩ := hex
  obtain ⟨B, hBS, hBsp, hli⟩ := exists_linearIndependent K (S (j + 1))
  have hfin : B.Finite := hli.setFinite
  have := hfin.fintype
  let e := Fintype.equivFin B
  have hr : Set.range (fun i => ((e.symm i : B) : Fin n → K)) = B := by
    rw [show (fun i => ((e.symm i : B) : Fin n → K)) = Subtype.val ∘ e.symm from rfl, e.symm.surjective.range_comp,
      Subtype.range_coe]
  refine ⟨s₀ * η ^ j, by positivity, mul_le_of_le_one_right hs.le (pow_le_one₀ hη.le hη1.le), _,
    fun i => e.symm i, by simpa using hli.fintype_card_le_finrank, fun i => ⟨(hBS (e.symm i).2).1,
      (hBS (e.symm i).2).2.trans (le_of_eq (by ring))⟩, ?_, fun u hu hut => ?_⟩
  · rw [hr, hBsp]; exact hnz (j + 1) (by omega)
  · rw [hr, hBsp]
    show u ∈ Wj (j + 1)
    rw [he]
    exact Submodule.subset_span ⟨hu, hut⟩

end CompanionTheory.D.gk.RF
end
end

open Matrix MeasureTheory NumberField Topology

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows

section Loc

variable {n : ℕ} {ε : Fin n → Bool}

theorem Jm_hermC (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

theorem Jm_det (ε : Fin n → Bool) : IsUnit (Formalism.REAL.Jm ε).det := by
  unfold Formalism.REAL.Jm
  rw [det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro a _
  by_cases h : ε a <;> simp [h]

theorem uMat_mul' (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_inv_mulC (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul', inv_mul_cancel]; rfl

theorem uMat_mul_invC (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul', mul_inv_cancel]; rfl

theorem hf_uMatC (g : Formalism.REAL.UJ ε) (a z : Fin n → ℂ) :
    hf (Formalism.REAL.Jm ε) (uMat g *ᵥ a) (uMat g *ᵥ z) = hf (Formalism.REAL.Jm ε) a z := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  unfold hf
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h]

theorem conj_xw (g : Formalism.REAL.UJ ε) (w b : Fin n → ℂ) :
    uMat g⁻¹ * xw (Formalism.REAL.Jm ε) w b * uMat g = xw (Formalism.REAL.Jm ε) (uMat g⁻¹ *ᵥ w) (uMat g⁻¹ *ᵥ b) := by
  have key : ∀ a z, hf (Formalism.REAL.Jm ε) (uMat g⁻¹ *ᵥ a) z = hf (Formalism.REAL.Jm ε) a (uMat g *ᵥ z) := fun a z => by
    rw [← hf_uMatC g, mulVec_mulVec, uMat_mul_invC, one_mulVec]
  refine mat_extC fun z => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, xw_mulVec, xw_mulVec, key, key, mulVec_sub, mulVec_smul, mulVec_smul]

theorem second_order_exp_conj (g : Formalism.REAL.UJ ε) (X : Matrix (Fin n) (Fin n) ℂ) :
    uMat g⁻¹ * ex2 X * uMat g = ex2 (uMat g⁻¹ * X * uMat g) := by
  have : uMat g⁻¹ * X * uMat g * (uMat g⁻¹ * X * uMat g) = uMat g⁻¹ * (X * X) * uMat g := by
    calc _ = uMat g⁻¹ * X * (uMat g * uMat g⁻¹) * X * uMat g := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [uMat_mul_invC, Matrix.mul_one, Matrix.mul_assoc (uMat g⁻¹) X X]
  simp only [ex2, this, mul_add, add_mul, Matrix.mul_one, uMat_inv_mulC, mul_smul_comm, smul_mul_assoc]

theorem norm_xw_le (w b : Fin n → ℂ) (i j : Fin n) : ‖xw (Formalism.REAL.Jm ε) w b i j‖ ≤ 2 * (‖w‖ * ‖b‖) := by
  have h1 : ‖(if ε j then 1 else -1 : ℂ)‖ = 1 := by split_ifs <;> simp
  simp only [xw, Formalism.REAL.Jm, Matrix.sub_apply, vecMulVec_apply, vecMul_diagonal]
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, h1, mul_one, Pi.star_apply, norm_star]
  have a := norm_le_pi_norm w
  have c := norm_le_pi_norm b
  have e1 := mul_le_mul (a i) (c j) (norm_nonneg _) (norm_nonneg _)
  have e2 := mul_le_mul (c i) (a j) (norm_nonneg _) (norm_nonneg _)
  linarith

theorem norm_second_order_exp_sub_one_le {A : Matrix (Fin n) (Fin n) ℂ} {a : ℝ} (h : ∀ i j, ‖A i j‖ ≤ a) (i j : Fin n) :
    ‖(ex2 A - 1) i j‖ ≤ a + n * a ^ 2 := by
  have e : ex2 A - 1 = A + (2 : ℂ)⁻¹ • (A * A) := by unfold ex2; abel
  have h0 : 0 ≤ a := (norm_nonneg _).trans (h i j)
  have h2 : ‖(A * A) i j‖ ≤ n * a ^ 2 := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (a ^ 2) fun k _ => ?_).trans (by simp))
    rw [norm_mul, _root_.sq]
    exact mul_le_mul (h _ _) (h _ _) (norm_nonneg _) h0
  rw [e, Matrix.add_apply, Matrix.smul_apply]
  refine (norm_add_le _ _).trans (add_le_add (h i j) ?_)
  rw [norm_smul, norm_inv, Complex.norm_two]
  nlinarith [norm_nonneg ((A * A) i j)]

end Loc

section XW

variable {K : Type} [Field K] [StarRing K] {n : ℕ} (J : Matrix (Fin n) (Fin n) K)

theorem xw_add (w b b' : Fin n → K) : xw J w (b + b') = xw J w b + xw J w b' :=
  mat_extC fun z => by
    rw [add_mulVec, xw_mulVec, xw_mulVec, xw_mulVec, hf_add_leftC, add_smul, smul_add]; abel

theorem xw_nat (w b : Fin n → K) (k : ℕ) : xw J w ((k : K) • b) = (k : K) • xw J w b :=
  mat_extC fun z => by
    rw [smul_mulVec, xw_mulVec, xw_mulVec, hf_smul_leftC, star_natCast, smul_sub, smul_smul, smul_smul, smul_smul,
      mul_comm (hf J w z)]

theorem smul_xw (c : K) (w b : Fin n → K) : c • xw J w b = xw (c • J) w b := by
  simp only [xw, vecMul_smul, vecMulVec_smul, smul_sub]

end XW

variable (I : AutInst)

theorem P_det (v : InfinitePlace I.F) : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)

theorem atM_add (v : InfinitePlace I.F) (A B : Matrix (Fin I.n) (Fin I.n) I.E) :
    atM I v (A + B) = atM I v A + atM I v B := by
  simp only [atM, Matrix.map_add _ (map_add (I.φ v)), mul_add, add_mul]

theorem atM_neg (v : InfinitePlace I.F) (A : Matrix (Fin I.n) (Fin I.n) I.E) : atM I v (-A) = -atM I v A := by
  simp only [atM, Matrix.map_neg _ (map_neg (I.φ v)), Matrix.mul_neg, Matrix.neg_mul]

theorem atM_sum (v : InfinitePlace I.F) {ι : Type} (s : Finset ι) (A : ι → Matrix (Fin I.n) (Fin I.n) I.E) :
    atM I v (∑ i ∈ s, A i) = ∑ i ∈ s, atM I v (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [atM]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, atM_add, ih]

theorem second_order_exp_at_infinite_place (v : InfinitePlace I.F) (X : Matrix (Fin I.n) (Fin I.n) I.E) : atM I v (ex2 X) = ex2 (atM I v X) := by
  have h1 : atM I v 1 = 1 := by
    simp only [atM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, nonsing_inv_mul _ (P_det I v)]
  have h2 : atM I v (X * X) = atM I v X * atM I v X := by
    simp only [atM, Matrix.map_mul, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (P_det I v)]
  have h3 : ∀ A, atM I v ((2 : I.E)⁻¹ • A) = (2 : ℂ)⁻¹ • atM I v A := fun A => by
    have : ((2 : I.E)⁻¹ • A).map (I.φ v) = (2 : ℂ)⁻¹ • A.map (I.φ v) := by
      ext i j; simp [map_ofNat]
    simp only [atM, this, mul_smul_comm, smul_mul_assoc]
  rw [ex2, atM_add, atM_add, h1, h3, h2, ex2]

theorem atV_addC (v : InfinitePlace I.F) (a b : Fin I.n → I.E) : atV I v (a + b) = atV I v a + atV I v b := by
  simp only [atV, ← mulVec_add]; congr 1; funext i; simp

theorem atV_smulC (v : InfinitePlace I.F) (c : I.E) (a : Fin I.n → I.E) : atV I v (c • a) = I.φ v c • atV I v a := by
  simp only [atV, ← mulVec_smul]; congr 1; funext i; simp

theorem atV_zero (v : InfinitePlace I.F) : atV I v 0 = 0 := by
  simpa using atV_smulC I v 0 0

theorem Wv_span (v : InfinitePlace I.F) {ι : Type} (w : ι → Fin I.n → I.E) :
    Submodule.span ℂ (Set.range fun i => atV I v (w i)) = Wv I (Submodule.span I.E (Set.range w)) v := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨w i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [atV_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [atV_addC]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [atV_smulC]; exact Submodule.smul_mem _ _ ha

theorem exists_denC : ∃ c : ℕ, 1 ≤ c ∧ ∀ i j, IsIntegral ℤ (((c : I.E) • I.J) i j) := by
  classical
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := I.E)
    (Finset.univ.image fun p : Fin I.n × Fin I.n => I.J p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i j => ?_⟩
  have h1 := h _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  rw [Matrix.smul_apply, smul_eq_mul, Nat.cast_natAbs]
  rcases abs_choice y with e | e <;> rw [e]
  · simpa using h1
  · simpa using h1.neg

theorem int_xw {J : Matrix (Fin I.n) (Fin I.n) I.E} (hJ : ∀ i j, IsIntegral ℤ (J i j)) {w b : Fin I.n → I.E}
    (hw : w ∈ IntV I) (hb : b ∈ IntV I) (i j : Fin I.n) : IsIntegral ℤ (xw J w b i j) := by
  have hs : ∀ a : I.E, IsIntegral ℤ a → IsIntegral ℤ (star a) := fun a ha =>
    ha.map (starRingEnd I.E).toIntAlgHom
  simp only [xw, Matrix.sub_apply, vecMulVec_apply, vecMul, dotProduct, Pi.star_apply]
  exact ((hw i).mul (IsIntegral.sum _ fun k _ => (hs _ (hb k)).mul (hJ k j))).sub
    ((hb i).mul (IsIntegral.sum _ fun k _ => (hs _ (hw k)).mul (hJ k j)))

theorem second_order_exp_congruence (M : ℕ) {Y : Matrix (Fin I.n) (Fin I.n) I.E} (hY : ∀ i j, IsIntegral ℤ (Y i j)) :
    Cong I M (ex2 (((2 * M : ℕ) : I.E) • Y)) := by
  intro i j
  refine ⟨2 * Y i j + 2 * M * (Y * Y) i j, ?_, ?_⟩
  · have h2 : IsIntegral ℤ (2 : I.E) := by exact_mod_cast isIntegral_natCast (R := ℤ) (B := I.E) 2
    refine (h2.mul (hY i j)).add ((h2.mul (isIntegral_natCast M)).mul ?_)
    rw [Matrix.mul_apply]
    exact IsIntegral.sum _ fun k _ => (hY _ _).mul (hY _ _)
  · simp only [ex2, smul_mul_assoc, mul_smul_comm, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring

theorem exists_gam (hT : Transp) (M c : ℕ) (hc : ∀ i j, IsIntegral ℤ (((c : I.E) • I.J) i j)) {d : ℕ}
    {w β : Fin d → Fin I.n → I.E} (hw : ∀ i, w i ∈ IntV I) (hβ : ∀ i, β i ∈ IntV I)
    (hW : Isot I.J (Submodule.span I.E (Set.range w))) (hβW : ∀ i, β i ∈ perp I.J (Submodule.span I.E (Set.range w))) :
    ∃ γ ∈ GamSet I M, ∀ v, uMat (γ v) =
      ex2 (-∑ i, xw (Formalism.REAL.Jm (I.ε v)) (atV I v (w i)) (((2 * M * c : ℕ) : ℂ) • atV I v (β i))) := by
  obtain ⟨hJ, -, -, -, -, -, hxw, hU⟩ := hT I
  have hd : IsUnit I.J.det := isUnit_iff_ne_zero.2 I.J_det
  obtain ⟨a1, -, -, -⟩ := nilpotent_lie_algebra I.E I.n I.J _ hJ hd hW
  let X := ∑ i, xw I.J (w i) (((2 * M * c : ℕ) : I.E) • β i)
  have hX : InL I.J _ X := (nilpotent_subgroup_representation I.E I.n I.J _ hJ hd hW d w rfl).1 _ fun i => Submodule.smul_mem _ _ (hβW i)
  let Y := ∑ i, xw ((c : I.E) • I.J) (w i) (β i)
  have hY : ∀ i j, IsIntegral ℤ (Y i j) := fun i j => by
    simp only [Y, Matrix.sum_apply]
    exact IsIntegral.sum _ fun k _ => int_xw I hc (hw k) (hβ k) i j
  have hXY : X = ((2 * M : ℕ) : I.E) • Y := by
    simp only [X, Y, xw_nat]
    simp only [Finset.smul_sum, ← smul_xw, smul_smul, Nat.cast_mul]
  obtain ⟨-, -, i1, hN⟩ := a1 X hX
  obtain ⟨u2, -, i2, -⟩ := a1 _ hN
  rw [neg_neg] at i2
  let γ : GL (Fin I.n) I.E := ⟨ex2 (-X), ex2 X, i2, i1⟩
  have hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := u2
  obtain ⟨g, hg⟩ := hU γ hγ
  refine ⟨g, ⟨γ, ⟨hγ, ?_, ?_⟩, hg⟩, fun v => ?_⟩
  · show Cong I M (ex2 (-X))
    rw [hXY, ← smul_neg]
    exact second_order_exp_congruence I M fun i j => (hY i j).neg
  · show Cong I M (ex2 X)
    rw [hXY]
    exact second_order_exp_congruence I M hY
  · rw [hg]
    show atM I v (ex2 (-X)) = _
    simp only [second_order_exp_at_infinite_place, atM_neg, X, atM_sum, hxw, atV_smulC, map_natCast]

theorem split_cov {y : I.Ginf} {S : Submodule I.E (Fin I.n → I.E)} {ρ : ℝ} (h : Covers I y S ρ) {k : ℕ} (hk : k ≠ 0)
    {d : ℕ} (b : InfinitePlace I.F → Fin d → Fin I.n → ℂ) (hb : ∀ v i, b v i ∈ Wv I S v) :
    ∃ β : Fin d → Fin I.n → I.E, (∀ i, β i ∈ IntV I ∧ β i ∈ S) ∧
      ∀ v i, ‖uMat (y v)⁻¹ *ᵥ (b v i - (k : ℂ) • atV I v (β i))‖ ≤ k * ρ := by
  choose β h1 h2 h3 using fun i => h (fun v => (k : ℂ)⁻¹ • b v i) fun v => Submodule.smul_mem _ _ (hb v i)
  refine ⟨β, fun i => ⟨h1 i, h2 i⟩, fun v i => ?_⟩
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have h4 := (norm_le_pi_norm _ v).trans (h3 i)
  simp only [Pi.sub_apply, vecAt, ← mulVec_sub] at h4
  have e : b v i - (k : ℂ) • atV I v (β i) = (k : ℂ) • ((k : ℂ)⁻¹ • b v i - atV I v (β i)) := by
    rw [smul_sub, smul_inv_smul₀ hk']
  rw [e, mulVec_smul, norm_smul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg k)

theorem atV_mem {S : Submodule I.E (Fin I.n → I.E)} {u : Fin I.n → I.E} (hu : u ∈ S) (v : InfinitePlace I.F) :
    atV I v u ∈ Wv I S v := Submodule.subset_span ⟨u, hu, rfl⟩

theorem nilpotent_cover_of : Transp → GamSub → NilpAlg → NilpRep → NCover := by
  intro hT hG hA hR I M hM
  obtain ⟨c, hc1, hc⟩ := exists_denC I
  obtain ⟨Γ, hΓ, -⟩ := hG I M
  set k : ℕ := 2 * M * c with hk
  have hk0 : k ≠ 0 := by positivity
  set Kc : ℝ := 4 * I.n * k
  refine ⟨Kc + I.n * Kc ^ 2 + 1, by positivity, fun y d w s ρ hd hs hρ hsρ hw hW hc1 hc2 m hm => ?_⟩
  set W := Submodule.span I.E (Set.range w)
  have hperp := (hT I).2.2.2.1
  have hWv : ∀ v, Isot (Formalism.REAL.Jm (I.ε v)) (Wv I W v) := fun v => by
    rw [Isot, ← hperp]; exact Submodule.span_mono (Set.image_mono hW)
  have A := fun v => hA ℂ I.n _ _ (Jm_hermC (I.ε v)) (Jm_det _) (hWv v)
  have R := fun v => hR ℂ I.n _ _ (Jm_hermC (I.ε v)) (Jm_det _) (hWv v) d _ (Wv_span I v w)
  choose X hX hmX using fun v => (A v).2.1 (uMat (m v)) (m v).2 (hm v)
  choose b hb hXb using fun v => (R v).2.2.1 _ (hX v)
  obtain ⟨β, hβ, hβr⟩ := split_cov I hc2 hk0 b fun v i => by rw [hperp]; exact hb v i
  obtain ⟨γ₁, hγ₁, e₁⟩ := exists_gam I hT M c hc (fun i => (hw i).1) (fun i => (hβ i).1) hW fun i => (hβ i).2
  let X₁ := fun v => ∑ i, xw (Formalism.REAL.Jm (I.ε v)) (atV I v (w i)) ((k : ℂ) • atV I v (β i))
  have hX₁ : ∀ v, InL (Formalism.REAL.Jm (I.ε v)) (Wv I W v) (-X₁ v) := fun v =>
    ((A v).1 _ ((R v).1 _ fun i => Submodule.smul_mem _ _ (by rw [← hperp]; exact atV_mem I (hβ i).2 v))).2.2.2
  choose b' hb' hZ using fun v => (R v).2.2.2 _ ((A v).2.2.1 _ _ (hX₁ v) (hX v)).2.1
  obtain ⟨β', hβ', hβr'⟩ := split_cov I hc1 hk0 b' hb'
  obtain ⟨γ₂, hγ₂, e₂⟩ := exists_gam I hT M c hc (fun i => (hw i).1) (fun i => (hβ' i).1) hW fun i => hW (hβ' i).2
  let Z₁ := fun v => ∑ i, xw (Formalism.REAL.Jm (I.ε v)) (atV I v (w i)) ((k : ℂ) • atV I v (β' i))
  have hZ₁ : ∀ v, InZ (Formalism.REAL.Jm (I.ε v)) (Wv I W v) (-Z₁ v) := fun v =>
    ((A v).2.2.2 _ ((R v).2.1 _ fun i => Submodule.smul_mem _ _ (atV_mem I (hβ' i).2 v))).2.1
  have cen : ∀ v Y, InL (Formalism.REAL.Jm (I.ε v)) (Wv I W v) Y →
      InL (Formalism.REAL.Jm (I.ε v)) (Wv I W v) (-Z₁ v + Y) ∧ ex2 (-Z₁ v) * ex2 Y = ex2 (-Z₁ v + Y) := fun v Y hY => by
    obtain ⟨h1, -, h2⟩ := (A v).2.2.2 _ (hZ₁ v)
    obtain ⟨h3, -, h4⟩ := (A v).2.2.1 _ _ h1 hY
    rw [(h2 Y hY).1, (h2 Y hY).2, sub_zero, smul_zero, add_zero] at h4
    exact ⟨h3, h4⟩
  refine ⟨γ₂ * γ₁, by rw [← hΓ] at hγ₁ hγ₂ ⊢; exact Γ.mul_mem hγ₂ hγ₁, fun v => ?_, fun v i j => ?_⟩
  · show Lowers _ _ (uMat (γ₂ v) * uMat (γ₁ v) - 1)
    rw [e₁, e₂, (cen v _ (hX₁ v)).2]
    exact ((A v).1 _ (cen v _ (hX₁ v)).1).2.1
  · obtain ⟨h1, h2, h3⟩ := (A v).2.2.1 _ _ (hX₁ v) (hX v)
    have h4 := ((A v).2.2.1 _ _ h1 ((A v).2.2.2 _ h2).1).1
    let r : Fin d → Fin I.n → ℂ := fun i =>
      (b v i - (k : ℂ) • atV I v (β i)) + (b' v i - (k : ℂ) • atV I v (β' i))
    have e : -Z₁ v + (-X₁ v + X v + (2 : ℂ)⁻¹ • (-X₁ v * X v - X v * -X₁ v)) =
        ∑ i, xw (Formalism.REAL.Jm (I.ε v)) (atV I v (w i)) (r i) := by
      rw [hZ v]
      nth_rewrite 1 [hXb v]
      have : ∀ (u p q : Fin I.n → ℂ), xw (Formalism.REAL.Jm (I.ε v)) u (p - q) =
          xw (Formalism.REAL.Jm (I.ε v)) u p - xw (Formalism.REAL.Jm (I.ε v)) u q := fun u p q => by
        rw [eq_sub_iff_add_eq, ← xw_add, sub_add_cancel]
      simp only [r, xw_add, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, X₁, Z₁]
      abel
    have e' : uMat ((y⁻¹ * (γ₂ * γ₁ * m) * y) v) =
        ex2 (∑ i, xw (Formalism.REAL.Jm (I.ε v)) (vecAt I y (w i) v) (uMat (y v)⁻¹ *ᵥ r i)) := by
      show uMat (y v)⁻¹ * (uMat (γ₂ v) * uMat (γ₁ v) * uMat (m v)) * uMat (y v) = _
      rw [e₁, e₂, hmX, Matrix.mul_assoc (ex2 _), h3, (cen v _ h4).2, e, second_order_exp_conj, Finset.mul_sum, Finset.sum_mul]
      simp only [conj_xw, vecAt]
    have hb1 : ∀ i j, ‖(∑ l, xw (Formalism.REAL.Jm (I.ε v)) (vecAt I y (w l) v) (uMat (y v)⁻¹ *ᵥ r l)) i j‖ ≤
        Kc * (s * ρ) := fun i j => by
      rw [Matrix.sum_apply]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (4 * k * (s * ρ)) fun l _ => ?_).trans ?_)
      · refine (norm_xw_le _ _ _ _).trans ?_
        have q1 := (norm_le_pi_norm _ v).trans (hw l).2
        have q2 : ‖uMat (y v)⁻¹ *ᵥ r l‖ ≤ 2 * (k * ρ) := by
          simp only [r]
          rw [mulVec_add]
          exact (norm_add_le _ _).trans (by linarith [hβr v l, hβr' v l])
        have := mul_le_mul q1 q2 (norm_nonneg _) hs
        linarith
      · rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hd' : (d : ℝ) ≤ I.n := by exact_mod_cast hd
        have : 0 ≤ 4 * (k : ℝ) * (s * ρ) := by positivity
        calc (d : ℝ) * (4 * k * (s * ρ)) ≤ I.n * (4 * k * (s * ρ)) := mul_le_mul_of_nonneg_right hd' this
          _ = _ := by ring
    rw [e']
    refine (norm_second_order_exp_sub_one_le hb1 i j).trans ?_
    have h0 : 0 ≤ s * ρ := mul_nonneg hs hρ
    have h5 : (s * ρ) ^ 2 ≤ s * ρ := by nlinarith
    have h6 : (I.n : ℝ) * Kc ^ 2 * (s * ρ) ^ 2 ≤ I.n * Kc ^ 2 * (s * ρ) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    nlinarith

theorem exists_kappa {U : Set I.Ginf} (hU : U ∈ 𝓝 (1 : I.Ginf)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ g : I.Ginf, (∀ v i j, ‖(uMat (g v) - 1) i j‖ ≤ κ) → g ∈ U := by
  let f : I.Ginf → (InfinitePlace I.F → Fin I.n → Fin I.n → ℂ) := fun g v => uMat (g v)
  have hf : IsInducing f := IsInducing.piMap fun v => (Formalism.REAL.isClosedEmbeddingMatrix I.n (I.ε v)).1.isInducing
  rw [hf.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨κ, hκ, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
  refine ⟨κ, hκ, fun g hg => hVU (hb ?_)⟩
  rw [mem_closedBall_iff_norm]
  exact (pi_norm_le_iff_of_nonneg hκ.le).2 fun v => (pi_norm_le_iff_of_nonneg hκ.le).2 fun i =>
    (pi_norm_le_iff_of_nonneg hκ.le).2 fun j => hg v i j

theorem Covers.mono {I : AutInst} {y : I.Ginf} {S : Submodule I.E (Fin I.n → I.E)} {ρ ρ' : ℝ} (h : Covers I y S ρ)
    (hρ : ρ ≤ ρ') : Covers I y S ρ' := fun b hb => by
  obtain ⟨u, h1, h2, h3⟩ := h b hb
  exact ⟨u, h1, h2, h3.trans hρ⟩

theorem reduction_geometry_at_infinity : Gap → ShortIsot → CovSpan → CovPerp → Mahler → NCover → GeoInf := by
  intro hGap hSI hCS hCP hMa hNC I M hM U hU
  obtain ⟨κ, hκ, hκU⟩ := exists_kappa I hU
  obtain ⟨s₁, hs₁, hSI⟩ := hSI I
  obtain ⟨C₁, hC₁, hCS⟩ := hCS I
  obtain ⟨C₂, hC₂, hCP⟩ := hCP I
  obtain ⟨C₃, hC₃, hNC⟩ := hNC I M hM
  set s₀ := min s₁ 1
  have hs₀ : 0 < s₀ := lt_min hs₁ one_pos
  obtain ⟨η, hη, hη1, hηa, hηb, hηc⟩ : ∃ η : ℝ, 0 < η ∧ η < 1 ∧ 2 * C₁ * η ≤ 1 ∧ (C₁ + C₂) * η ≤ 1 ∧
      C₃ * ((C₁ + C₂) * η) ≤ κ := by
    have t : ∀ a : ℝ, Filter.Tendsto (fun η : ℝ => a * η) (𝓝[>] 0) (𝓝 0) := fun a => by
      simpa using ((continuous_const_mul a).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    obtain ⟨η, h0, h1, h2, h3, h4⟩ := (Filter.Eventually.and (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
      (((t 1).eventually (gt_mem_nhds one_pos)).and (((t (2 * C₁)).eventually (ge_mem_nhds one_pos)).and
      (((t (C₁ + C₂)).eventually (ge_mem_nhds one_pos)).and ((t (C₃ * (C₁ + C₂))).eventually (ge_mem_nhds hκ)))))).exists
    exact ⟨η, h0, by simpa using h1, h2, h3, by rwa [← mul_assoc]⟩
  have he : 0 < s₀ * η ^ (I.n + 1) := by positivity
  obtain ⟨C, hC, hMa⟩ := hMa I M hM (C₂ / (s₀ * η ^ (I.n + 1)))
  refine ⟨C, hC, fun y => ?_⟩
  by_cases hc : ∃ u ∈ IntV I, u ≠ 0 ∧ ‖vecAt I y u‖ ≤ s₀ * η ^ (I.n + 1)
  · right
    obtain ⟨t, ht, hts, d, w, hd, hw, hne, hall⟩ := hGap I.E I.n (IntV I) (fun u => ‖vecAt I y u‖) s₀ η hs₀ hη hη1 hc
    have ht1 : t ≤ 1 := hts.trans (min_le_right _ _)
    have hs : η * t ≤ s₁ := (mul_le_of_le_one_left ht.le hη1.le).trans (hts.trans (min_le_left _ _))
    have hI : Isot I.J (Submodule.span I.E (Set.range w)) := Submodule.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      exact mem_perp_spanC fun i => hSI y _ (hw i).1 _ (hw j).1 ((hw i).2.trans hs) ((hw j).2.trans hs))
    have c1 := hCS y d w (η * t) hd (by positivity) hw
    have c2 := hCP y _ _ t ht (by nlinarith) c1 fun u hu hn => by
      by_contra h
      exact hn (hall u hu (not_le.1 h).le)
    have hρ : η * t * (C₁ * (η * t) + C₂ / t) ≤ (C₁ + C₂) * η := by
      have e : η * t * (C₁ * (η * t) + C₂ / t) = C₁ * η * (η * t * t) + C₂ * η := by field_simp
      have : η * t * t ≤ 1 := mul_le_one₀ (mul_le_one₀ hη1.le ht.le ht1) ht.le ht1
      have := mul_le_of_le_one_right (by positivity : 0 ≤ C₁ * η) this
      rw [e]; linarith
    refine ⟨_, hne, hI, fun m hm => ?_⟩
    obtain ⟨γ, h1, h2, h3⟩ := hNC y d w (η * t) (C₁ * (η * t) + C₂ / t) hd (by positivity) (by positivity)
      (hρ.trans hηb) hw hI (c1.mono (le_add_of_nonneg_right (by positivity)))
      (c2.mono (le_add_of_nonneg_left (by positivity))) m hm
    exact ⟨γ, h1, h2, hκU _ fun v i j =>
      (h3 v i j).trans ((mul_le_mul_of_nonneg_left hρ hC₃.le).trans hηc)⟩
  · left
    push Not at hc
    have c0 : Covers I y ⊥ 0 := fun b hb => ⟨0, fun _ => isIntegral_zero, Submodule.zero_mem _, by
      have h0 : ∀ v, atV I v 0 = 0 := atV_zero I
      have hb0 : ∀ v, b v = 0 := fun v => by
        have := hb v
        simpa [Wv, h0] using this
      have : (fun v => uMat (y v)⁻¹ *ᵥ b v) - vecAt I y 0 = 0 := by
        funext v; simp [vecAt, hb0, h0]
      rw [this, norm_zero]⟩
    have c2 := hCP y ⊥ 0 _ he (by linarith) c0 fun u hu hn => (hc u hu fun h => hn (by simp [h])).le
    have e : perp I.J (⊥ : Submodule I.E (Fin I.n → I.E)) = ⊤ := eq_top_iff.2 fun z _ w hw => by
      rw [(Submodule.mem_bot I.E).1 hw]; simp [hf]
    exact hMa y (e ▸ c2)

end CompanionTheory.D.gk.RF
end
end

namespace CompanionTheory.D.gk.RF

theorem gamSub : GamSub := by
  exact arithmetic_subgroup_of_transport transport_to_standard_form

theorem geoInf : GeoInf := by
  have hT : Transp := transport_to_standard_form
  have hG : GamSub := arithmetic_subgroup_of_transport hT
  exact reduction_geometry_at_infinity successive_minima_gap (short_isotropic_vector_of hT) covolume_span (covolume_orthogonal_complement hT)
    (mahler_compactness_of hT hG) (nilpotent_cover_of hT hG nilpotent_lie_algebra nilpotent_subgroup_representation)

theorem cuspInf : CuspInf :=
  cuspidal_at_infinity_of selP (averaging_of_fundamental_domain fundamental_domain_inclusion) unipotent_radical_subgroup real_parabolic_decomposition parabolic_subgroup_decomposition transport_to_standard_form gamSub geoInf

theorem automorphic_forms_finite_dimensional : Formalism.L2.SG.RowsDef.RowsFinDim := by
  exact rowsFinDim_of discrete_series_bound_of_inputs finite_dimensional_from_linear_forms (adelic_cusp_of_infinite_cusp cuspInf congruence_subgroup_compact_open)
    (fundamental_domain_discrete_of gamSub) level_structure_of convolution_operator_representation representation_of_convolution

end CompanionTheory.D.gk.RF
