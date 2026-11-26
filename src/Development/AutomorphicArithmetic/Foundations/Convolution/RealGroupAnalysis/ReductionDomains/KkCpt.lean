module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkFin
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.kkFin :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (k : G1 F) (v : HeightOneSpectrum (𝓞 F)), IntAt v k ↔ Reduction.finAt v (gl k) ∈ GLnLocal.integralGL (v.adicCompletion F) 2 := by
  intro F _ _ k v
  have hinv : (Reduction.finAt v (gl k))⁻¹ = Reduction.finAt v (gl k⁻¹) := by
    have e : ∀ g : GL (Fin 2) (A F), Reduction.finAt v g = Matrix.GeneralLinearGroup.map (Reduction.finEval v) g := by
      intro g; ext i j; rfl
    rw [e, e, ← map_inv, ← map_inv]
  have hent : ∀ (g : G1 F) i j, (Reduction.finAt v (gl g)) i j = (g i j).2 v := fun _ _ _ => rfl
  rw [GLnLocal.mem_integralGL_iff, hinv]
  simp only [hent, GroundTheory.Global.mem_valuationInteger_iff]
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  intro i j
  have e : (k⁻¹ : G1 F).1 = !![k.1 1 1, -k.1 0 1; -k.1 1 0, k.1 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  have hn : ∀ a b, (-(k.1 a b)).2 v ∈ v.adicCompletionIntegers F := fun a b =>
    neg_mem (h a b)
  show ((k⁻¹ : G1 F).1 i j).2 v ∈ _
  rw [e]
  fin_cases i <;> fin_cases j
  · exact h 1 1
  · exact hn 0 1
  · exact hn 1 0
  · exact h 0 0
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.EntryMul
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem real_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (∀ z : Fin n → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z) ↔ M * Mᵀ = 1 := by
  constructor
  · intro h
    have hq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z := by
      intro z
      have h2 := congrArg (· ^ 2) (h z)
      simp only [Reduction.euclidNorm_sq, Real.norm_eq_abs, sq_abs] at h2
      simpa only [dotProduct, sq] using h2
    have hb : ∀ x z : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (z ᵥ* M) = x ⬝ᵥ z := by
      intro x z
      have h1 := hq (x + z)
      rw [add_vecMul] at h1
      simp only [add_dotProduct, dotProduct_add, hq] at h1
      rw [dotProduct_comm (z ᵥ* M), dotProduct_comm z x] at h1
      linarith
    ext i j
    have h3 := hb (Pi.single i 1) (Pi.single j 1)
    rw [single_one_vecMul, single_one_vecMul, single_one_dotProduct] at h3
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [transpose_apply]
    refine Eq.trans h3 ?_
    simp [Pi.single_apply]
  · intro h z
    refine Reduction.euclidNorm_vecMul_unitary ?_ z
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    exact h

private theorem entry_mul {F : Type} [Field F] [NumberField F] (k : G1 F) (w : InfinitePlace F) (i j : Fin 2) :
    ((k.1 * k.1ᵀ) i j).1 w = ∑ l, (k i l).1 w * (k j l).1 w := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  rfl

private theorem entry_one {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem place_iff {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (k : G1 F) (w : InfinitePlace F) :
    Reduction.infAt w (gl k) ∈ Reduction.archCompact w ↔
      ∀ i j, ((k.1 * k.1ᵀ) i j).1 w = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w := by
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) with hψdef
  have hψ : ∀ z, ‖ψ.toRingHom z‖ = ‖z‖ := fun z =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero
      (map_zero _) z
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => ψ ((k i j).1 w)
  have e : ∀ z : Fin 2 → w.Completion,
      (fun j => ψ.toRingHom ((z ᵥ* (Reduction.infAt w (gl k) : Matrix (Fin 2) (Fin 2) w.Completion)) j)) =
        (fun i => ψ.toRingHom (z i)) ᵥ* M := by
    intro z
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [vecMul, dotProduct, map_sum, map_mul]
    rfl
  have key : ∀ i j, (M * Mᵀ) i j = ψ (((k.1 * k.1ᵀ) i j).1 w) := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [entry_mul, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  have key1 : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = ψ (((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w) := by
    intro i j
    rw [entry_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h1 : Reduction.infAt w (gl k) ∈ Reduction.archCompact w ↔
      ∀ z : Fin 2 → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z := by
    rw [Reduction.mem_archCompact]
    constructor
    · intro h z
      have hz : z = fun i => ψ.toRingHom (ψ.symm (z i)) := funext fun i => (ψ.apply_symm_apply _).symm
      rw [hz, ← e, Reduction.euclidNorm_map _ hψ, Reduction.euclidNorm_map _ hψ, h]
    · intro h z
      rw [← Reduction.euclidNorm_map _ hψ, e, h, Reduction.euclidNorm_map _ hψ]
  rw [h1, real_iff]
  constructor
  · intro h i j
    apply ψ.injective
    rw [← key, ← key1, h]
  · intro h
    ext i j
    rw [key, key1, h i j]

theorem UpperTheory.ConvolutionTheory.R2.M.kkInf :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ k : G1 F, InfOrth k ↔ ∀ w, Reduction.infAt w (gl k) ∈ Reduction.archCompact w := by
  intro F _ _ _ k
  simp only [place_iff, InfOrth]
  exact ⟨fun h w i j => congrFun (h i j) w, fun h i j => funext fun w => h w i j⟩
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.kkCpt :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], KK F = (M.Ks F : Set (G1 F)) ∧ IsCompact (KK F) := by
  intro F _ _ _
  have h1 : KK F = (M.Ks F : Set (G1 F)) := by
    ext g
    change (InfOrth g ∧ ∀ v, IntAt v g) ↔ gl g ∈ Reduction.maxCompact (K := F) (n := 2)
    rw [Reduction.mem_maxCompact, UpperTheory.ConvolutionTheory.R2.M.kkInf F g]
    exact and_congr_right fun _ => forall_congr' fun v => UpperTheory.ConvolutionTheory.R2.M.kkFin F g v
  refine ⟨h1, ?_⟩
  have hC := Reduction.isCompact_maxCompact (K := F) (n := 2)
  have hD := hC.image (Units.continuous_val)
  have h2 := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hD
  have h3 : KK F = (fun g : G1 F => g.1) ⁻¹' (Units.val '' (Reduction.maxCompact (K := F) (n := 2) : Set (GL (Fin 2) (A F)))) := by
    rw [h1]
    ext g
    constructor
    · intro hg
      exact ⟨gl g, hg, rfl⟩
    · rintro ⟨u, hu, huv⟩
      have : u = gl g := Units.ext huv
      subst this
      exact hu
  rw [h3]
  exact h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CdMeas
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.cdMeas :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (t : (A F)ˣ), MeasurePreserving (cD t) M₀.μ M₀.μ := by
  intro F _ _ M₀ t
  haveI := M₀.haar
  haveI := M₀.right
  have hm : ∀ s : (A F)ˣ, Measurable (cD s : G1 F → G1 F) := fun s => (M.continuous_cD s).measurable
  let e : G1 F ≃ₜ* G1 F :=
    { toFun := cD t
      invFun := cD t⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      map_mul' := M.cD_mul t
      continuous_toFun := M.continuous_cD t
      continuous_invFun := M.continuous_cD t⁻¹ }
  haveI : (M₀.μ.map (cD t)).IsHaarMeasure := e.isHaarMeasure_map M₀.μ
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, M₀.μ.map (cD t) = c • M₀.μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (M₀.μ.map (cD t)) M₀.μ⟩
  have h2 : M₀.μ.map (cD (t * t)) = M₀.μ := by
    have : (cD (t * t) : G1 F → G1 F) = (fun g => g * mD t) ∘ (fun g => (mD t)⁻¹ * g) := by
      funext g; exact M.cD_sq t g
    rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _),
      map_mul_left_eq_self, map_mul_right_eq_self]
  have h3 : M₀.μ.map (cD (t * t)) = (c * c) • M₀.μ := by
    have : (cD (t * t) : G1 F → G1 F) = cD t ∘ cD t := by
      funext g; exact (M.cD_cD t t g).symm
    rw [this, ← Measure.map_map (hm t) (hm t), hc,
      Measure.map_smul c (hm t).aemeasurable, hc, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G1 F)
  have hpos : M₀.μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds M₀.μ hK1).ne'
  have hfin : M₀.μ K ≠ ∞ := hK.measure_lt_top.ne
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) * M₀.μ K = M₀.μ K := by
    have := congrArg (fun m : Measure (G1 F) => m K) (h3.symm.trans h2)
    simpa [ENNReal.smul_def] using this
  have h5 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := by
    have h6 : ((c * c : ℝ≥0) : ℝ≥0∞) * M₀.μ K = 1 * M₀.μ K := by rw [h4, one_mul]
    exact (ENNReal.mul_left_inj hpos hfin).1 h6
  have h7 : c * c = 1 := by exact_mod_cast h5
  have h8 : c = 1 := by
    have := (mul_self_eq_one_iff (a := (c : ℝ))).1 (by exact_mod_cast h7)
    rcases this with h | h
    · exact_mod_cast h
    · have := c.coe_nonneg; linarith
  refine ⟨hm t, ?_⟩
  rw [hc, h8, one_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtEx
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtEx :
    ∀ (F : Type) [Field F] [NumberField F], ∃ β : G1 F → ℝ≥0∞, M.NWt β := by
  intro F _ _
  have hinj : Function.Injective (fun ξ : F => (nU (rt ξ : A F) : G1 F)) := by
    intro a b h
    have h1 : (nU (rt a : A F) : G1 F) 0 1 = (nU (rt b : A F) : G1 F) 0 1 := by
      rw [show (nU (rt a : A F) : G1 F) = nU (rt b : A F) from h]
    have h2 : (rt a : A F) = rt b := by simpa [nU] using h1
    exact AdeleRing.algebraMap_injective (𝓞 F) F h2
  let N : Subgroup (G1 F) :=
    { carrier := Set.range fun ξ : F => (nU (rt ξ : A F) : G1 F)
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by simp only [rt, map_add (f := _), M.nU_add]⟩
      one_mem' := ⟨0, by simp only [rt, map_zero, M.nU_zero]⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, by simp only [rt, map_neg, M.nU_neg]⟩ }
  have hle : N ≤ Gam F := by
    rintro _ ⟨ξ, rfl⟩
    exact M.nU_rt_mem ξ
  haveI : DiscreteTopology N :=
    DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  obtain ⟨D, hD, hu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup N
  refine ⟨D.indicator 1, measurable_one.indicator hD, fun g => ?_⟩
  obtain ⟨n, hn, huniq⟩ := hu g
  obtain ⟨ξ₀, hξ₀⟩ := n.2
  have hn' : (nU (rt ξ₀ : A F) : G1 F) * g ∈ D := by
    have : (n : G1 F) * g ∈ D := hn
    rwa [← hξ₀] at this
  rw [tsum_eq_single ξ₀]
  · rw [Set.indicator_of_mem hn']
    rfl
  · intro ξ hξ
    refine Set.indicator_of_notMem (fun hmem => hξ ?_) _
    have h1 : (⟨nU (rt ξ : A F), ⟨ξ, rfl⟩⟩ : N) = n := huniq _ hmem
    have h2 : (nU (rt ξ : A F) : G1 F) = n := congrArg Subtype.val h1
    exact hinj (h2.trans hξ₀.symm)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorHomeo
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem mem_bor_iff {F : Type} [Field F] [NumberField F] (g : G1 F) :
    g ∈ M.Bor F ↔ g 1 0 = 0 := by
  constructor
  · intro h
    exact h (show (id (0 : Fin 2)) < id (1 : Fin 2) by decide)
  · intro h i j hij
    have hij' : j < i := hij
    have hi : i = 1 := by omega
    have hj : j = 0 := by omega
    subst hi hj
    exact h

private theorem nm_val {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (b : A F) :
    (nU b * mD a).1 = !![(a : A F), b * ((a⁻¹ : (A F)ˣ) : A F); 0, ((a⁻¹ : (A F)ˣ) : A F)] := by
  rw [M.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem upperTriangular_diagonal_product {F : Type} [Field F] [NumberField F] (g : G1 F) (h : g 1 0 = 0) :
    g 0 0 * g 1 1 = 1 := by
  have hd := g.det_coe
  rw [Matrix.det_fin_two] at hd
  have h' : g.1 1 0 = 0 := h
  rw [h', mul_zero, sub_zero] at hd
  exact hd

private def dg {F : Type} [Field F] [NumberField F] (g : M.Bor F) : IdeleGroup F :=
  ⟨g.1 0 0, g.1 1 1, upperTriangular_diagonal_product g.1 ((mem_bor_iff g.1).1 g.2),
    (mul_comm _ _).trans (upperTriangular_diagonal_product g.1 ((mem_bor_iff g.1).1 g.2))⟩

theorem UpperTheory.ConvolutionTheory.R2.M.borHomeo :
    ∀ (F : Type) [Field F] [NumberField F], IsClosed (M.Bor F : Set (G1 F)) ∧ ∃ e : IdeleGroup F × A F ≃ₜ M.Bor F, ∀ p, (e p : G1 F) = nU p.2 * mD p.1 := by
  intro F _ _
  refine ⟨?_, ?_⟩
  · have : (M.Bor F : Set (G1 F)) = {g | g 1 0 = 0} := Set.ext mem_bor_iff
    rw [this]
    exact isClosed_eq (M.continuous_entry 1 0) continuous_const
  · have hmem : ∀ p : IdeleGroup F × A F, nU p.2 * mD p.1 ∈ M.Bor F := fun p => by
      rw [mem_bor_iff]
      show (nU p.2 * mD p.1).1 1 0 = 0
      rw [nm_val]
      simp
    refine ⟨{ toFun := fun p => ⟨nU p.2 * mD p.1, hmem p⟩
              invFun := fun g => (dg g, g.1 0 1 * g.1 0 0)
              left_inv := ?_
              right_inv := ?_
              continuous_toFun := ?_
              continuous_invFun := ?_ }, fun p => rfl⟩
    · rintro ⟨a, b⟩
      have e00 : (nU b * mD a) 0 0 = (a : A F) := by
        show (nU b * mD a).1 0 0 = _
        rw [nm_val]; simp
      have e01 : (nU b * mD a) 0 1 = b * ((a⁻¹ : (A F)ˣ) : A F) := by
        show (nU b * mD a).1 0 1 = _
        rw [nm_val]; simp
      refine Prod.ext (Units.ext e00) ?_
      show (nU b * mD a) 0 1 * (nU b * mD a) 0 0 = b
      rw [e00, e01, mul_assoc, Units.inv_mul, mul_one]
    · rintro ⟨g, hg⟩
      have h10 := (mem_bor_iff g).1 hg
      have hd := upperTriangular_diagonal_product g h10
      refine Subtype.ext (Subtype.ext ?_)
      show (nU (g 0 1 * g 0 0) * mD (dg ⟨g, hg⟩)).1 = g.1
      rw [nm_val]
      have hinv : (((dg ⟨g, hg⟩)⁻¹ : (A F)ˣ) : A F) = g 1 1 := rfl
      have hval : ((dg ⟨g, hg⟩ : (A F)ˣ) : A F) = g 0 0 := rfl
      rw [hinv, hval]
      ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · show g 0 1 * g 0 0 * g 1 1 = g 0 1
        rw [mul_assoc, hd, mul_one]
      · exact h10.symm
      · rfl
    · exact Continuous.subtype_mk
        ((M.continuous_nU.comp continuous_snd).mul (M.continuous_mD.comp continuous_fst)) _
    · have c : ∀ i j, Continuous fun g : M.Bor F => g.1 i j := fun i j =>
        (M.continuous_entry i j).comp continuous_subtype_val
      exact (Units.continuous_iff.2 ⟨c 0 0, c 1 1⟩).prodMk ((c 0 1).mul (c 0 0))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RowCosets
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private def upS {F : Type} [Field F] (ξ : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, ξ; 0, 1], by simp [Matrix.det_fin_two]⟩

private theorem upS_val {F : Type} [Field F] (ξ : F) : (upS ξ).1 = !![1, ξ; 0, 1] := rfl

private theorem ratS_upS {F : Type} [Field F] [NumberField F] (ξ : F) : ratS F (upS ξ) = nU (rt ξ) :=
  M.ratS_up ξ

private theorem specialLinear_upper_unipotent {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (h0 : g.1 1 0 = 0) (h1 : g.1 1 1 = 1) : g = upS (g.1 0 1) := by
  have hd := g.det_coe
  rw [Matrix.det_fin_two, h0, h1] at hd
  have hd' : g.1 0 0 = 1 := by simpa using hd
  refine Subtype.ext ?_
  change g.1 = (upS (g.1 0 1)).1
  rw [upS_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, hd']

private theorem ratS_inj {F : Type} [Field F] [NumberField F] :
    Function.Injective (ratS F) := by
  intro a b h
  have hinj : Function.Injective (algebraMap F (A F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  refine Subtype.ext ?_
  ext i j
  apply hinj
  have h2 := congrArg (fun g : G1 F => g.1 i j) h
  simpa [M.val_ratS] using h2

private theorem row_up {F : Type} [Field F] (ξ : F) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (upS ξ * g).1 1 = g.1 1 := by
  ext j
  change ((upS ξ).1 * g.1) 1 j = _
  rw [upS_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.ConvolutionTheory.R2.M.rowCosets :
    ∀ (F : Type) [Field F] [NumberField F], (∃ σ, M.RowSec (F := F) σ) ∧ ∀ σ, M.RowSec (F := F) σ → ∀ γ : Gam F, ∃! p : {r : Fin 2 → F // r ≠ 0} × F, (γ : G1 F) = nU (rt p.2) * ratS F (σ p.1) := by
  intro F _ _
  refine ⟨?_, ?_⟩
  · have hex : ∀ r : {r : Fin 2 → F // r ≠ 0}, ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, g.1 1 = r.1 := by
      rintro ⟨r, hr⟩
      by_cases hc : r 0 = 0
      · have hd : r 1 ≠ 0 := fun hd => hr (by ext i; fin_cases i <;> simp [hc, hd])
        refine ⟨⟨!![(r 1)⁻¹, 0; r 0, r 1], by simp [Matrix.det_fin_two, hd]⟩, ?_⟩
        ext i; fin_cases i <;> simp
      · refine ⟨⟨!![0, -(r 0)⁻¹; r 0, r 1], by simp [Matrix.det_fin_two, hc]⟩, ?_⟩
        ext i; fin_cases i <;> simp
    choose σ hσ using hex
    exact ⟨σ, hσ⟩
  · rintro σ hσ ⟨_, γ0, rfl⟩
    have hr : γ0.1 1 ≠ 0 := by
      intro h
      have hd := γ0.det_coe
      rw [Matrix.det_fin_two] at hd
      have h0 : γ0.1 1 0 = 0 := congrFun h 0
      have h1 : γ0.1 1 1 = 0 := congrFun h 1
      simp [h0, h1] at hd
    obtain ⟨r, hrdef⟩ : ∃ r : {r : Fin 2 → F // r ≠ 0}, r = ⟨γ0.1 1, hr⟩ := ⟨_, rfl⟩
    have hs : (σ r).1 1 = γ0.1 1 := by rw [hσ r, hrdef]
    have hs0 : (σ r).1 1 0 = γ0.1 1 0 := congrFun hs 0
    have hs1 : (σ r).1 1 1 = γ0.1 1 1 := congrFun hs 1
    have hdet : (σ r).1 0 0 * (σ r).1 1 1 - (σ r).1 0 1 * (σ r).1 1 0 = 1 := by
      have hd := (σ r).det_coe
      rwa [Matrix.det_fin_two] at hd
    have e0 : (γ0 * (σ r)⁻¹).1 1 0 = 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp [hs0, hs1]
      ring
    have e1 : (γ0 * (σ r)⁻¹).1 1 1 = 1 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp
      linear_combination hdet - (σ r).1 0 0 * hs1 + (σ r).1 0 1 * hs0
    obtain ⟨ξ, hξ⟩ : ∃ ξ : F, γ0 * (σ r)⁻¹ = upS ξ := ⟨_, specialLinear_upper_unipotent _ e0 e1⟩
    have hγ : γ0 = upS ξ * σ r := by
      rw [← hξ, inv_mul_cancel_right]
    refine ⟨(r, ξ), ?_, ?_⟩
    · show ratS F γ0 = nU (rt ξ) * ratS F (σ r)
      conv_lhs => rw [hγ]
      rw [map_mul, ratS_upS]
    · rintro ⟨r', ξ'⟩ heq
      have heq' : ratS F γ0 = nU (rt ξ') * ratS F (σ r') := heq
      rw [← ratS_upS, ← map_mul] at heq'
      have hγ' := ratS_inj heq'
      have hrr : r' = r := by
        refine Subtype.ext ?_
        rw [← hσ r', ← row_up ξ' (σ r'), ← hγ', hrdef]
      subst hrr
      have hU : upS ξ = upS ξ' := mul_right_cancel (hγ.symm.trans hγ')
      have hξξ : ξ = ξ' := by
        have h2 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g.1 0 1) hU
        simpa [upS_val] using h2
      rw [hξξ]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IwDens
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.iwDens :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F), ∃ ρ : Measure (IdeleGroup F × G1 F), SFinite ρ ∧ (∀ u : G1 F → ℝ≥0∞, Measurable u → ∫⁻ p, u (mD p.1 * p.2) ∂ρ = M.J0 M₀ u) ∧ ∀ u : IdeleGroup F × G1 F → ℂ, (Integrable u ρ ↔ Integrable (fun p => (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p) M₀.ν) ∧ ∫ p, u p ∂ρ = ∫ p, (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p ∂M₀.ν := by
  intro F _ _ M₀
  have hfm : Measurable (fun p : IdeleGroup F × G1 F => Real.toNNReal ((ab p.1)⁻¹ ^ 2)) :=
    (((M.continuous_ab.measurable.comp measurable_fst).inv).pow_const 2).real_toNNReal
  have hwm : Measurable (fun p : IdeleGroup F × G1 F => M.wt p.1) :=
    M.measurable_wt.comp measurable_fst
  have hsm : ∀ (u : IdeleGroup F × G1 F → ℂ) (p : IdeleGroup F × G1 F),
      Real.toNNReal ((ab p.1)⁻¹ ^ 2) • u p = (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p := by
    intro u p
    rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), Complex.real_smul]
  haveI : IsProbabilityMeasure M₀.κ := M₀.prob
  haveI : SFinite M₀.ν := by unfold Meas.ν; infer_instance
  refine ⟨M₀.ν.withDensity fun p => (Real.toNNReal ((ab p.1)⁻¹ ^ 2) : ℝ≥0∞), inferInstance, ?_, ?_⟩
  · intro u _
    have h := lintegral_withDensity_eq_lintegral_mul_non_measurable M₀.ν hwm
      (Eventually.of_forall fun p => ENNReal.ofReal_lt_top) (fun p => u (mD p.1 * p.2))
    exact h
  · intro u
    refine ⟨?_, ?_⟩
    · rw [integrable_withDensity_iff_integrable_smul hfm]
      simp only [hsm]
    · rw [integral_withDensity_eq_integral_smul hfm]
      simp only [hsm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtA
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtA :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (β u : G1 F → ℝ≥0∞) (c : ℝ≥0∞), Measurable β → (∀ g, ∫⁻ b, β (nU b * g) ∂(adeleMeasure F) = c) → Measurable u → (∀ b g, u (nU b * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = c * M.J0 M₀ u := by
  intro F _ _ M₀ β u c hβ hc hu hinv
  haveI := M₀.prob
  have hm : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    ((M.continuous_mD.comp continuous_fst).mul continuous_snd).measurable
  have hJ : Measurable fun p : IdeleGroup F × G1 F => M.wt p.1 * u (mD p.1 * p.2) :=
    (M.measurable_wt.comp measurable_fst).mul (hu.comp hm)
  have hin : ∀ (a : IdeleGroup F) (k : G1 F),
      ∫⁻ b, u (nU b * mD a * k) * β (nU b * mD a * k) * ENNReal.ofReal ((ab a)⁻¹ ^ 2) ∂(adeleMeasure F)
        = c * (M.wt a * u (mD a * k)) := by
    intro a k
    have h1 : ∀ b, u (nU b * mD a * k) * β (nU b * mD a * k) * ENNReal.ofReal ((ab a)⁻¹ ^ 2)
        = (M.wt a * u (mD a * k)) * β (nU b * (mD a * k)) := fun b => by
      rw [mul_assoc (nU b), hinv, M.wt]; ring
    simp_rw [h1]
    have hb : Measurable fun b : A F => β (nU b * (mD a * k)) :=
      hβ.comp ((M.continuous_nU.mul continuous_const).measurable)
    rw [lintegral_const_mul _ hb, hc, mul_comm]
  have hk : Measurable fun k : G1 F => ∫⁻ a, M.wt a * u (mD a * k) ∂(ideleMeasure F) :=
    hJ.lintegral_prod_left'
  have hsec : ∀ k : G1 F, Measurable fun a : IdeleGroup F => M.wt a * u (mD a * k) :=
    fun k => M.measurable_wt.mul (hu.comp ((M.continuous_mD.mul continuous_const).measurable))
  rw [M₀.iwasawa (fun g => u g * β g) (hu.mul hβ), M.J0, Meas.ν, lintegral_prod_symm _ hJ.aemeasurable,
    ← lintegral_const_mul _ hk]
  refine lintegral_congr fun k => ?_
  rw [← lintegral_const_mul _ (hsec k)]
  exact lintegral_congr fun a => hin a k
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtOne
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtOne :
    ∀ (F : Type) [Field F] [NumberField F] (β : G1 F → ℝ≥0∞), M.NWt β → ∀ g, ∫⁻ b, β (nU b * g) ∂(adeleMeasure F) = 1 := by
  intro F _ _ β hβ g
  obtain ⟨hm, hs⟩ := hβ
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let e : F → AdeleRing.principalSubgroup (𝓞 F) F := fun ξ => ⟨rt ξ, ξ, rfl⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b h
      exact AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h)
    · rintro ⟨_, ξ, rfl⟩
      exact ⟨ξ, rfl⟩
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := he.surjective.countable
  have hfd := isAddFundamentalDomain_fundamentalSet F
  have hf : Measurable fun b : A F => β (nU b * g) :=
    hm.comp (M.continuous_nU.mul continuous_const).measurable
  rw [hfd.lintegral_eq_tsum'' (fun b => β (nU b * g)), ← lintegral_tsum]
  · have hone : ∀ x : A F,
        ∑' k : AdeleRing.principalSubgroup (𝓞 F) F, β (nU (k +ᵥ x) * g) = 1 := by
      intro x
      rw [← (Equiv.ofBijective e he).tsum_eq, ← hs (nU x * g)]
      refine tsum_congr fun ξ => ?_
      change β (nU (rt ξ + x) * g) = _
      rw [M.nU_add, mul_assoc]
    simp only [hone, lintegral_const, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter,
      adeleMeasure_fundamentalSet, one_mul]
  · intro k
    exact (hf.comp (measurable_const_vadd k)).aemeasurable
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.SumSide
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.sumSide :
    ∀ (X ι : Type) [MeasurableSpace X] [Countable ι] (m : Measure X) (e : ι → X → X), (∀ i, Measurable (e i)) → (∀ u : X → ℝ≥0∞, Measurable u → ∫⁻ x, u x ∂(Measure.sum fun i => m.map (e i)) = ∫⁻ x, ∑' i, u (e i x) ∂m) ∧ ∀ u : X → ℂ, Measurable u → Integrable u (Measure.sum fun i => m.map (e i)) → (∀ᵐ x ∂m, Summable fun i => ‖u (e i x)‖) ∧ Integrable (fun x => ∑' i, u (e i x)) m ∧ ∫ x, ∑' i, u (e i x) ∂m = ∫ x, u x ∂(Measure.sum fun i => m.map (e i)) := by
  intro X ι _ _ m e he
  have hL : ∀ u : X → ℝ≥0∞, Measurable u →
      ∫⁻ x, u x ∂(Measure.sum fun i => m.map (e i)) = ∫⁻ x, ∑' i, u (e i x) ∂m := by
    intro u hu
    have hm : ∀ i, AEMeasurable (fun x => u (e i x)) m := fun i => (hu.comp (he i)).aemeasurable
    rw [lintegral_sum_measure, lintegral_tsum hm]
    exact tsum_congr fun i => lintegral_map hu (he i)
  refine ⟨hL, fun u hu hint => ?_⟩
  have hum : Measurable fun x => ‖u x‖ₑ := hu.enorm
  have hfin : ∫⁻ x, ∑' i, ‖u (e i x)‖ₑ ∂m < ⊤ := by
    rw [← hL _ hum]
    exact hint.2
  have hmeas : Measurable fun x => ∑' i, ‖u (e i x)‖ₑ :=
    Measurable.tsum fun i => hum.comp (he i)
  have hsum : ∀ᵐ x ∂m, Summable fun i => ‖u (e i x)‖ := by
    filter_upwards [ae_lt_top hmeas hfin.ne] with x hx
    have h1 : ∑' i, ((‖u (e i x)‖₊ : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := hx.ne
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)
  have hsm : ∀ i, AEStronglyMeasurable (fun x => u (e i x)) m := fun i =>
    (hu.comp (he i)).aestronglyMeasurable
  have hlim : ∀ᵐ x ∂m, Tendsto (fun s : Finset ι => ∑ i ∈ s, u (e i x)) atTop
      (𝓝 (∑' i, u (e i x))) := by
    filter_upwards [hsum] with x hx
    exact hx.of_norm.hasSum
  have hae : AEStronglyMeasurable (fun x => ∑' i, u (e i x)) m :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s : Finset ι => Finset.aestronglyMeasurable_fun_sum s fun i _ => hsm i) hlim
  have hI : Integrable (fun x => ∑' i, u (e i x)) m := by
    refine ⟨hae, lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin⟩
    exact enorm_tsum_le_tsum_enorm
  refine ⟨hsum, hI, ?_⟩
  have hne : ∑' i, ∫⁻ x, ‖u (e i x)‖ₑ ∂m ≠ ⊤ := by
    have hm : ∀ i, AEMeasurable (fun x => ‖u (e i x)‖ₑ) m := fun i =>
      (hum.comp (he i)).aemeasurable
    rw [← lintegral_tsum hm]
    exact hfin.ne
  rw [integral_tsum hsm hne, integral_sum_measure hint]
  exact tsum_congr fun i => (integral_map (he i).aemeasurable hu.aestronglyMeasurable).symm
end
