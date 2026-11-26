module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorExtendsHyperbolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderVolumeAlmostAll
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderVolumeAlmostAll
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit

theorem lam_map_mul {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    [lam.IsAddHaarMeasure] (x : Fv F v) (hx : x ≠ 0) :
    lam.map (fun y => x * y) = (‖x‖₊)⁻¹ • lam := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu : IsUnit x := hx.isUnit
  have hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = ‖x‖ := by
    have h := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v x hx
    have he : Units.mk0 x hx = hu.unit := by
      ext
      simp
    rw [he] at h
    exact congrArg (fun z : ℝ≥0 => (z : ℝ)) h
  have hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = (‖x‖₊)⁻¹ := by
    rw [map_inv]
    apply NNReal.coe_injective
    push_cast
    rw [hc]
  have hm : Measurable fun y : Fv F v => x * y := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  open scoped Pointwise in
  have e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, hc']
  rfl

theorem norm_le_of_val_lt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v)
    (hx : x ≠ 0) (h : Valued.v x < 1) : ‖x‖ ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hv : Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log h0).symm
  set n : ℤ := WithZero.log (Valued.v x) with hn
  have hlt : n < 0 := by
    rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    exact h
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := GlobalTheory.CompanionTheory.SW.Growth.two_le_norm v
  rw [FinitePlace.norm_def, hv, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  change ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n ≤ _
  have h1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)
  calc ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ h1 (by omega)
    _ = _ := by rw [zpow_neg_one, one_div]

theorem fibre_zero_image_mul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (N : ℕ) (hN : 1 ≤ N) (J : Matrix (Fin N) (Fin N) E) (hJ : IsHermND σ J)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    (hlam : IsStdV v lam) (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E))
    (hm : IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m)
    (u : (Fv F v ⊗[F] E)ˣ) (B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E)) (hB : MeasurableSet B) :
    m 0 ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (u : Fv F v ⊗[F] E) * X a i) '' B) =
      ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ (N - 1) : ℝ≥0) : ℝ≥0∞) * m 0 B := by
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  set s : Fv F v := Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) with hs
  have hsu : IsUnit s := u.isUnit.map (Algebra.norm (Fv F v))
  have hs0 : s ≠ 0 := hsu.ne_zero
  have hN' : algebraMap (Fv F v) (Fv F v ⊗[F] E) s = (u : Fv F v ⊗[F] E) * sigR (Fv F v) σ u :=
    GlobalTheory.Doubling.algebraMap_norm_eq hσ _
  set q : ℝ≥0 := ‖s‖₊ with hq
  have hq0 : q ≠ 0 := by rw [hq]; exact nnnorm_ne_zero_iff.2 hs0
  have hsigs : sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) s) = algebraMap (Fv F v) (Fv F v ⊗[F] E) s := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => (u : Fv F v ⊗[F] E)
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact u.isUnit
  let T : (Fin 1 → Fin N → Fv F v ⊗[F] E) → Fin 1 → Fin N → Fv F v ⊗[F] E :=
    fun X a i => (u : Fv F v ⊗[F] E) * X a i
  let Ti : (Fin 1 → Fin N → Fv F v ⊗[F] E) → Fin 1 → Fin N → Fv F v ⊗[F] E :=
    fun X a i => ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * X a i
  have hrm : (fun X : Fin 1 → Fin N → Fv F v ⊗[F] E => rmul (Fv F v) X g) = T := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, T]
    rw [Subsingleton.elim p 0, mul_comm]
  have hTc : Continuous T := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hTic : Continuous Ti := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hTT : ∀ X, T (Ti X) = X := by
    intro X; funext a i; simp [T, Ti]
  have hTiT : ∀ X, Ti (T X) = X := by
    intro X; funext a i; simp [T, Ti]
  have hWb : BorelSpace (Fin 1 → Fin N → Fv F v ⊗[F] E) := by infer_instance
  have hTm : Measurable T := hTc.measurable
  have hTim : Measurable Ti := hTic.measurable
  have himg : ∀ C : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), T '' C = Ti ⁻¹' C := by
    intro C
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      simpa [hTiT] using hY
    · intro hX
      exact ⟨Ti X, hX, hTT X⟩
  have himg' : ∀ C : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), T ⁻¹' C = Ti '' C := by
    intro C
    ext X
    constructor
    · intro hX
      exact ⟨T X, hX, hTiT X⟩
    · rintro ⟨Y, hY, rfl⟩
      simpa [hTT] using hY
  have hnorm_inv : ‖Algebra.norm (Fv F v) ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)‖₊ = q⁻¹ := by
    have h1 : Algebra.norm (Fv F v) ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * s = 1 := by
      rw [hs, ← map_mul, Units.inv_mul, map_one]
    have h2 := congrArg (fun x : Fv F v => ‖x‖₊) h1
    simp only [nnnorm_mul, nnnorm_one] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hmu : (coordW (Fv F v) b lam 1 N).map (fun X => rmul (Fv F v) X g) =
      (q⁻¹ ^ N) • coordW (Fv F v) b lam 1 N := by
    rw [hrm]
    ext C hC
    rw [Measure.map_apply hTm hC, himg', Measure.smul_apply]
    have := GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul F E σ hσ N d b v lam hlam u⁻¹ C hC
    rw [show (Ti '' C) = ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin N) =>
      ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * X p k) '' C) from rfl, this, hnorm_inv, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S =>
    ⟨fun i j => algebraMap (Fv F v) (Fv F v ⊗[F] E) s * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j, by
      intro a c
      have := S.2 a c
      simp only [map_mul, hsigs]
      rw [this]⟩
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) s * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := fun _ _ _ => rfl
  have hτm : Measurable τ := by
    obtain ⟨-, -, -, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Fv F v) 1
    haveI := hBH
    refine Continuous.measurable ?_
    refine Continuous.subtype_mk ?_ _
    refine continuous_matrix fun i j => ?_
    exact continuous_const.mul ((continuous_apply_apply i j).comp continuous_subtype_val)
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g := by
    intro S
    ext i j
    rw [hτe, hN']
    simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, g, Matrix.of_apply]
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    ring
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam s hs0 q⁻¹ (lam_map_mul v lam s hs0) τ hτm hτe
  have hfree : IsOpen {X : Fin 1 → Fin N → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m (hW 1 N) (hH 1) hm hfree g hg τ hτ _ _ hmu hc 0
  have hτ0 : τ 0 = 0 := by
    apply Subtype.ext
    funext i j
    change algebraMap (Fv F v) (Fv F v ⊗[F] E) s * 0 = 0
    rw [mul_zero]
  rw [hτ0, hrm] at key
  have hTB : MeasurableSet (T '' B) := by
    rw [himg]; exact hTim hB
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin N → Fv F v ⊗[F] E) => μ' (T '' B)) key
  simp only [Measure.smul_apply, Measure.map_apply hTm hTB] at key2
  have hpre : T ⁻¹' (T '' B) = B := by
    rw [himg, ← Set.preimage_comp]
    have : Ti ∘ T = id := funext hTiT
    rw [this, Set.preimage_id]
  rw [hpre] at key2
  have hcoe : (q : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hq0
  change m 0 (T '' B) = _
  simp only [ENNReal.smul_def, smul_eq_mul] at key2
  have e1 : ((q ^ N : ℝ≥0) : ℝ≥0∞) * ((q⁻¹ ^ N : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.coe_mul, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, ENNReal.coe_one]
  have e2 : ((q ^ N : ℝ≥0) : ℝ≥0∞) * ((q⁻¹ : ℝ≥0) : ℝ≥0∞) = ((q ^ (N - 1) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_assoc, mul_inv_cancel₀ hq0, mul_one]
  calc m 0 (T '' B) = ((q ^ N : ℝ≥0) : ℝ≥0∞) * (((q⁻¹ ^ N : ℝ≥0) : ℝ≥0∞) * m 0 (T '' B)) := by
        rw [← mul_assoc, e1, one_mul]
    _ = _ := by rw [key2, ← mul_assoc, e2]

theorem val_eq_one_eventually {F : Type} [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) a) = 1 := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 F) a
  have h2 := HeightOneSpectrum.Support.finite (𝓞 F) a⁻¹
  refine Filter.eventually_cofinite.2 ((h1.union h2).subset ?_)
  intro v hv
  by_contra hc
  have hc1 : ¬ 1 < v.valuation F a := fun h => hc (Or.inl h)
  have hc2 : ¬ 1 < v.valuation F a⁻¹ := fun h => hc (Or.inr h)
  apply hv
  rw [GlobalTheory.CompanionTheory.SW.Growth.val_alg]
  have hne : v.valuation F a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  rw [not_lt] at hc1 hc2
  rw [map_inv₀] at hc2
  exact le_antisymm hc1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 hc2)

theorem norm_le_of_nonunit (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (d : ℕ) (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E),
      (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) →
      ∀ c : O, ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) →
        ‖Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E)‖ ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hb1 : b.repr 1 ≠ 0 := by
    intro h
    exact one_ne_zero (b.repr.map_eq_zero_iff.1 h)
  obtain ⟨k0, hk0⟩ : ∃ k, b.repr 1 k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hb1 (Finsupp.ext hcon)
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ hσ d b, val_eq_one_eventually _ hk0]
    with v hgood hv O hO c hc hcu
  obtain ⟨O', hO', hσO', -⟩ := hgood
  set s : Fv F v := Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E) with hs
  have hs0 : s ≠ 0 := (hcu.map (Algebra.norm (Fv F v))).ne_zero
  have hN' : algebraMap (Fv F v) (Fv F v ⊗[F] E) s = (c : Fv F v ⊗[F] E) * sigR (Fv F v) σ c :=
    GlobalTheory.Doubling.algebraMap_norm_eq hσ _
  have hσc : sigR (Fv F v) σ c ∈ O :=
    (hO _).2 ((hO' _).1 (hσO' _ ((hO' _).2 ((hO _).1 c.2))))
  have hy : algebraMap (Fv F v) (Fv F v ⊗[F] E) s ∈ O := by
    rw [hN']
    exact O.mul_mem c.2 hσc
  have hrepr : ∀ (r : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d),
      (Algebra.TensorProduct.basis (Fv F v) b).repr (algebraMap (Fv F v) (Fv F v ⊗[F] E) r * y) k =
        r * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
    intro r y k
    rw [← Algebra.smul_def, map_smul]
    rfl
  have hone : (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k0 =
      algebraMap F (Fv F v) (b.repr 1 k0) := by
    rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]
    simp
  have hs1 : Valued.v s ≤ 1 := by
    have h := (hO _).1 hy k0
    rw [← mul_one (algebraMap (Fv F v) (Fv F v ⊗[F] E) s), hrepr, hone,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hv, mul_one] at h
    exact h
  have hlt : Valued.v s < 1 := by
    refine lt_of_le_of_ne hs1 fun h1 => hc ?_
    have hw : algebraMap (Fv F v) (Fv F v ⊗[F] E) s⁻¹ * sigR (Fv F v) σ c ∈ O := by
      refine (hO _).2 fun k => ?_
      have h := (hO _).1 hσc k
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h ⊢
      rw [hrepr, map_mul, map_inv₀, h1, inv_one, one_mul]
      exact h
    have hcw : c * (⟨_, hw⟩ : O) = 1 := by
      apply Subtype.ext
      change (c : Fv F v ⊗[F] E) * (algebraMap (Fv F v) (Fv F v ⊗[F] E) s⁻¹ * sigR (Fv F v) σ c) = 1
      rw [mul_left_comm, ← hN', ← map_mul, inv_mul_cancel₀ hs0, map_one]
    exact IsUnit.of_mul_eq_one _ hcw
  exact norm_le_of_val_lt v s hs0 hlt

theorem fibre_zero_image_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), IsHermND σ J → 3 ≤ N → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (c : O), ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) → ∀ B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), MeasurableSet B → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * X a i) '' B) ≤ ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) B := by
  intro F E _ _ _ _ _ σ hσ N J hJ hN d b
  filter_upwards [norm_le_of_nonunit F E σ hσ d b] with v hv O hO lam hlam m hm h₂ c hc hcu B hB
  have hn := hv O hO c hc hcu
  obtain ⟨u, hu⟩ := hcu
  have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0 := by
    apply Subtype.ext
    funext i j
    simp [hermOf]
  rw [h0]
  have key := fibre_zero_image_mul F E σ hσ N (by omega) J hJ d b v lam hlam m hm u B hB
  rw [hu] at key
  rw [key]
  gcongr
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  set x : ℝ := ‖Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E)‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast GlobalTheory.CompanionTheory.SW.Growth.two_le_norm v
  have hq1 : 1 / (Ideal.absNorm v.asIdeal : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hx1 : x ≤ 1 := hn.trans hq1
  calc x ^ (N - 1) ≤ x ^ 2 := pow_le_pow_of_le_one hx0 hx1 (by omega)
    _ ≤ (1 / (Ideal.absNorm v.asIdeal : ℝ)) ^ 2 := pow_le_pow_left₀ hx0 hn 2
    _ = 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by rw [one_div_pow]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderVolumeAlmostAllStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_volume_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), IsHermND σ J → 3 ≤ N → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (c : O), ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) → ∀ B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), MeasurableSet B → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * X a i) '' B) ≤ ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) B := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderTwoPrimesAlmostAll
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderTwoPrimesAlmostAll
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.SW.QuadMaxIdeal

section Quad

variable {R O : Type} [CommRing R] [CommRing O] [IsLocalRing R] (ι : R →+* O) (δ : O) (D : R)


omit [IsLocalRing R] in
theorem isUnit_of_norm (hδ : δ * δ = ι D) (p q : R) (h : IsUnit (p ^ 2 - D * q ^ 2)) :
    IsUnit (ι p + ι q * δ) := by
  obtain ⟨w, hw⟩ := h.exists_right_inv
  refine IsUnit.of_mul_eq_one ((ι p - ι q * δ) * ι w) ?_
  have h1 : ι (p ^ 2 - D * q ^ 2) * ι w = 1 := by rw [← map_mul, hw, map_one]
  simp only [map_sub, map_mul, map_pow] at h1
  linear_combination h1 - (ι q) ^ 2 * ι w * hδ

theorem isUnit_add_mem {u x : R} (hu : IsUnit u) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (u + x) := by
  by_contra h
  have h1 : u + x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have h2 : u ∈ IsLocalRing.maximalIdeal R := by
    simpa using Ideal.sub_mem _ h1 hx
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 hu

theorem isUnit_of_not_mem {x : R} (hx : x ∉ IsLocalRing.maximalIdeal R) : IsUnit x := by
  by_contra h
  exact hx ((IsLocalRing.mem_maximalIdeal _).2 h)

theorem map_mem (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    {P : Ideal O} (hP : P.IsMaximal) {r : R} (hr : r ∈ IsLocalRing.maximalIdeal R) :
    ι r ∈ P := by
  by_contra hn
  obtain ⟨y, i, hi, e⟩ := hP.exists_inv hn
  obtain ⟨a, b, rfl⟩ := hsp y
  have hi' : i = ι (1 - a * r) + ι (-(b * r)) * δ := by
    simp only [map_sub, map_mul, map_neg, map_one]
    linear_combination e
  have hu : IsUnit ((1 - a * r) ^ 2 - D * (-(b * r)) ^ 2) := by
    have e1 : (1 - a * r) ^ 2 - D * (-(b * r)) ^ 2 =
        1 + r * (a ^ 2 * r - 2 * a - D * b ^ 2 * r) := by ring
    rw [e1]
    exact isUnit_add_mem isUnit_one (Ideal.mul_mem_right _ _ hr)
  have hiu : IsUnit i := by
    rw [hi']
    exact isUnit_of_norm ι δ D hδ _ _ hu
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hi hiu)

theorem eq_span_of_factor (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (s c : R) (π' : O) (hm : IsLocalRing.maximalIdeal R = Ideal.span {c})
    (hfac : (δ - ι s) * π' = ι c) {P : Ideal O} (hP : P.IsMaximal) (hπ : δ - ι s ∈ P) :
    P = Ideal.span {δ - ι s} := by
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 hπ)
  intro y hy
  obtain ⟨p, q, rfl⟩ := hsp y
  have hr : ι (p + q * s) ∈ P := by
    have e : ι (p + q * s) = (ι p + ι q * δ) - ι q * (δ - ι s) := by
      simp only [map_add (f := _), map_mul]; ring
    rw [e]
    exact P.sub_mem hy (P.mul_mem_left _ hπ)
  have hm' : p + q * s ∈ IsLocalRing.maximalIdeal R := by
    by_contra hn
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hr ((isUnit_of_not_mem hn).map ι))
  rw [hm, Ideal.mem_span_singleton'] at hm'
  obtain ⟨a, ha⟩ := hm'
  have h1 : ι a * ι c = ι p + ι q * ι s := by
    rw [← map_mul, ha, map_add (f := _), map_mul]
  refine Ideal.mem_span_singleton'.2 ⟨ι q + ι a * π', ?_⟩
  linear_combination (ι a) * hfac + h1

theorem eq_span_of_nonsquare (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hsq : ∀ e : R, e ^ 2 - D ∉ IsLocalRing.maximalIdeal R)
    {P : Ideal O} (hP : P.IsMaximal) : P = Ideal.span {ι ϖ} := by
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 (map_mem ι δ D hδ hsp hP hϖm))
  intro y hy
  obtain ⟨p, q, rfl⟩ := hsp y
  have hN : p ^ 2 - D * q ^ 2 ∈ IsLocalRing.maximalIdeal R := by
    by_contra hn
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hy
      (isUnit_of_norm ι δ D hδ p q (isUnit_of_not_mem hn)))
  have hq : q ∈ IsLocalRing.maximalIdeal R := by
    by_contra hn
    obtain ⟨w, hw⟩ := (isUnit_of_not_mem hn).exists_right_inv
    apply hsq (p * w)
    have e : (p * w) ^ 2 - D = w ^ 2 * (p ^ 2 - D * q ^ 2) := by
      linear_combination (D * (q * w + 1)) * hw
    rw [e]
    exact Ideal.mul_mem_left _ _ hN
  have hp : p ∈ IsLocalRing.maximalIdeal R := by
    have h1 : p ^ 2 ∈ IsLocalRing.maximalIdeal R := by
      have e : p ^ 2 = (p ^ 2 - D * q ^ 2) + D * q ^ 2 * 1 := by ring
      rw [e]
      refine Ideal.add_mem _ hN (Ideal.mul_mem_right _ _ ?_)
      exact Ideal.mul_mem_left _ _ (by
        rw [pow_two]; exact Ideal.mul_mem_left _ _ hq)
    exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem 2 h1
  rw [hϖ, Ideal.mem_span_singleton'] at hp hq
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  refine Ideal.mem_span_singleton'.2 ⟨ι a + ι b * δ, ?_⟩
  simp only [map_mul]
  ring

theorem exists_root (hD : IsUnit D) (h2 : IsUnit (2 : R)) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) (e : R)
    (he : e ^ 2 - D ∈ IsLocalRing.maximalIdeal R) :
    ∃ e' : R, IsLocalRing.maximalIdeal R = Ideal.span {e' ^ 2 - D} := by
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have heu : IsUnit e := by
    have h1 : IsUnit (D + (e ^ 2 - D)) := isUnit_add_mem hD he
    have h3 : IsUnit (e ^ 2) := by simpa using h1
    exact (isUnit_pow_iff two_ne_zero).1 h3
  have he' := he
  rw [hϖ, Ideal.mem_span_singleton'] at he'
  obtain ⟨c, hc⟩ := he'
  by_cases hcu : IsUnit c
  · refine ⟨e, ?_⟩
    rw [← hc, Ideal.span_singleton_mul_left_unit hcu, hϖ]
  · have hcm : c ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hcu
    have hu : IsUnit (2 * e + (c + ϖ)) :=
      isUnit_add_mem (h2.mul heu) (Ideal.add_mem _ hcm hϖm)
    refine ⟨e + ϖ, ?_⟩
    have e1 : (e + ϖ) ^ 2 - D = (2 * e + (c + ϖ)) * ϖ := by
      linear_combination -hc
    rw [e1, Ideal.span_singleton_mul_left_unit hu, hϖ]

theorem exists_gens (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (hD : IsUnit D) (h2 : IsUnit (2 : R)) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0) :
    ∃ (π₁ π₂ : O) (c : R), c ≠ 0 ∧ π₁ ∣ ι c ∧ π₂ ∣ ι c ∧
      ∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂} := by
  by_cases hsq : ∃ e : R, e ^ 2 - D ∈ IsLocalRing.maximalIdeal R
  · obtain ⟨e0, he0⟩ := hsq
    obtain ⟨e, hm⟩ := exists_root D hD h2 ϖ hϖ e0 he0
    have hc0 : e ^ 2 - D ≠ 0 := by
      intro h0
      have h1 : ϖ ∈ Ideal.span {e ^ 2 - D} := by
        rw [← hm, hϖ]; exact Ideal.mem_span_singleton_self ϖ
      rw [h0] at h1
      exact hϖ0 (by simpa using h1)
    have f1 : (δ - ι e) * (-(δ - ι (-e))) = ι (e ^ 2 - D) := by
      simp only [map_sub, map_neg, map_pow]
      linear_combination -hδ
    have f2 : (δ - ι (-e)) * (-(δ - ι e)) = ι (e ^ 2 - D) := by
      simp only [map_sub, map_neg, map_pow]
      linear_combination -hδ
    refine ⟨δ - ι e, δ - ι (-e), e ^ 2 - D, hc0, ⟨_, f1.symm⟩, ⟨_, f2.symm⟩, ?_⟩
    intro P hP
    have hcm : e ^ 2 - D ∈ IsLocalRing.maximalIdeal R := by
      rw [hm]; exact Ideal.mem_span_singleton_self _
    have hcP := map_mem ι δ D hδ hsp hP hcm
    have hprod : (δ - ι e) * (δ - ι (-e)) ∈ P := by
      have e1 : (δ - ι e) * (δ - ι (-e)) = -((δ - ι e) * (-(δ - ι (-e)))) := by ring
      rw [e1, f1]
      exact P.neg_mem hcP
    rcases hP.isPrime.mem_or_mem hprod with h | h
    · exact Or.inl (eq_span_of_factor ι δ D hδ hsp e _ _ hm f1 hP h)
    · exact Or.inr (eq_span_of_factor ι δ D hδ hsp (-e) _ _ hm f2 hP h)
  · push_neg at hsq
    exact ⟨ι ϖ, ι ϖ, ϖ, hϖ0, dvd_rfl, dvd_rfl, fun P hP =>
      Or.inl (eq_span_of_nonsquare ι δ D hδ hsp ϖ hϖ hsq hP)⟩

end Quad

section Place

open GlobalTheory.CompanionTheory.SW.GoodRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem at_place {d : ℕ} (b : Module.Basis (Fin d) F E)
    (b₂ : Module.Basis (Fin 2) F E) (D : F) (hb0 : b₂ 0 = 1)
    (hD : b₂ 1 * b₂ 1 = algebraMap F E D) (v : HeightOneSpectrum (𝓞 F))
    (hD1 : Valued.v (algebraMap F (Fv F v) D) = 1)
    (h21 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (hBC : ∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈
      v.adicCompletionIntegers F)
    (hCB : ∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈
      v.adicCompletionIntegers F)
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) :
    ∃ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) ∧
      IsUnit (π₁ : Fv F v ⊗[F] E) ∧ IsUnit (π₂ : Fv F v ⊗[F] E) := by
  set K := Fv F v with hK
  set B := Algebra.TensorProduct.basis K b₂ with hB
  set C := Algebra.TensorProduct.basis K b with hC
  let Rs : Subring K := (v.adicCompletionIntegers F).toSubring
  have hB0 : B 0 = 1 := by
    rw [hB, Algebra.TensorProduct.basis_apply, hb0]; rfl
  have hB1 : B 1 = inclR K (b₂ 1) := by
    rw [hB, Algebra.TensorProduct.basis_apply]; rfl
  have hBD : B 1 * B 1 = algebraMap K (K ⊗[F] E) (algebraMap F K D) := by
    rw [hB1, ← map_mul, hD]
    show (1 : Fv F v) ⊗ₜ[F] algebraMap F E D = (algebraMap F (Fv F v) D) ⊗ₜ[F] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have hDR : algebraMap F K D ∈ Rs := hD1.le
  obtain ⟨O', hOC, hOB'⟩ := exists_subring Rs B C (algebraMap F K D) hB0 hBD hDR
    (fun k j => by
      have := hBC k j
      rwa [show inclR K (b k) = C k by rw [hC, Algebra.TensorProduct.basis_apply]; rfl] at this)
    (fun j k => by
      have := hCB j k
      rwa [show inclR K (b₂ j) = B j by rw [hB, Algebra.TensorProduct.basis_apply]; rfl] at this)
  have hOB : ∀ y, y ∈ O ↔ ∀ j, B.repr y j ∈ Rs := fun y =>
    (hO y).trans ((hOC y).symm.trans (hOB' y))
  have hpq : ∀ p q : K, p ∈ Rs → q ∈ Rs →
      algebraMap K (K ⊗[F] E) p + algebraMap K (K ⊗[F] E) q * B 1 ∈ O := by
    intro p q hp hq
    have h := coord_two B hB0 p q
    refine (hOB _).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [h.1]; exact hp
    · rw [h.2]; exact hq
  have hRmem : ∀ c ∈ Rs, algebraMap K (K ⊗[F] E) c ∈ O := by
    intro c hc
    simpa using hpq c 0 hc Rs.zero_mem
  have hδO : B 1 ∈ O := by
    have := hpq 0 1 Rs.zero_mem Rs.one_mem
    rwa [map_zero, map_one, zero_add, one_mul] at this
  let ι : (v.adicCompletionIntegers F) →+* O :=
    ((algebraMap K (K ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype).codRestrict O
      (fun x => hRmem x x.2)
  let δ : O := ⟨B 1, hδO⟩
  let D' : v.adicCompletionIntegers F := ⟨algebraMap F K D, hDR⟩
  have hδ : δ * δ = ι D' := Subtype.ext hBD
  have hsp : ∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ := fun y => by
    have hy := (hOB y).1 y.2
    exact ⟨⟨_, hy 0⟩, ⟨_, hy 1⟩, Subtype.ext (eq_coord B hB0 y)⟩
  have hunit : ∀ r : v.adicCompletionIntegers F, IsUnit r ↔ Valued.v (r : K) = 1 := fun r =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
  have hv2 : Valued.v (2 : K) = 1 := by simpa [map_ofNat] using h21
  have hDu : IsUnit D' := (hunit D').2 hD1
  have h2u : IsUnit (2 : v.adicCompletionIntegers F) := (hunit 2).2 (by
    rw [show ((2 : v.adicCompletionIntegers F) : K) = 2 from
      map_ofNat (v.adicCompletionIntegers F).subtype 2]
    exact hv2)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  obtain ⟨π₁, π₂, c, hc, d1, d2, hmax⟩ := exists_gens ι δ D' hδ hsp hDu h2u ϖ
    hϖ.maximalIdeal_eq hϖ.ne_zero
  have hcK : (c : K) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have hcu : IsUnit (((ι c : O)) : K ⊗[F] E) :=
    (IsUnit.mk0 (c : K) hcK).map (algebraMap K (K ⊗[F] E))
  have key : ∀ π : O, π ∣ ι c → IsUnit (π : K ⊗[F] E) := by
    rintro π ⟨w, hw⟩
    have h1 : (((ι c : O)) : K ⊗[F] E) = (π : K ⊗[F] E) * (w : K ⊗[F] E) :=
      congrArg Subtype.val hw
    rw [h1] at hcu
    exact isUnit_of_mul_isUnit_left hcu
  exact ⟨π₁, π₂, hmax, key π₁ d1, key π₂ d2⟩

end Place

theorem maximal_ideals : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∃ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) ∧ IsUnit (π₁ : Fv F v ⊗[F] E) ∧ IsUnit (π₂ : Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ h d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    have hreal : w.IsReal := by
      rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun x ↦ ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      change star (w.embedding x) = w.embedding x
      rw [← h.2.2.2, hc]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal
  obtain ⟨D, b₂, hsq, hb0, hσ1, hD⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 hinv hne
  have hD0 : D ≠ 0 := fun h0 => hsq (h0 ▸ IsSquare.zero)
  have I := GlobalTheory.T.integral_almost_all_places F E σ h
  filter_upwards [(I d b).2 D hD0, (I d b).2 2 two_ne_zero,
    Filter.eventually_all.2 fun k => (I 2 b₂).1 (b k),
    Filter.eventually_all.2 fun j => (I d b).1 (b₂ j)] with v hD1 h21 hBC hCB O hO
  exact at_place b b₂ D hb0 hD v hD1 h21 hBC hCB O hO

end GlobalTheory.CompanionTheory.SW.QuadMaxIdeal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderTwoPrimesAlmostAllStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_two_primes_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∃ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) ∧ IsUnit (π₁ : Fv F v ⊗[F] E) ∧ IsUnit (π₂ : Fv F v ⊗[F] E) := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadMaxIdeal.maximal_ideals | exact GlobalTheory.CompanionTheory.SW.QuadMaxIdeal.maximal_ideals | (intros; apply GlobalTheory.CompanionTheory.SW.QuadMaxIdeal.maximal_ideals <;> assumption)
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc

theorem JR_hypOne {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : JR (F := F) R (hypOne J) = hypOne (JR (F := F) R J) := by
  ext i j
  simp only [JR, Matrix.map_apply]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
    simp [hypOne]

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem e0_mem_latV {d : ℕ} (M : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) :
    (e0 (Fv F v ⊗[F] E) M : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) ∈ latV b v := by
  rw [GoodTrans.mem_latV_iff b v O hO]
  intro a i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa [e0] using O.one_mem
  · simpa [e0] using O.zero_mem

theorem primV_subset (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) : primV σ J b v ⊆ latV b v := by
  rintro y ⟨g, hg, rfl⟩
  exact (hg _).2 (e0_mem_latV M b v O hO)

theorem latStab_of_integral (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F)
    (g : GL (Fin M) (Fv F v ⊗[F] E)) (hg : g ∈ HR (Fv F v) σ J)
    (hgO : ∀ i j, (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ O)
    (hgiO : ∀ i j, ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j ∈ O) :
    latStab σ J b v ((⟨g, hg⟩ : HR (Fv F v) σ J) : HA (Fv F v) σ J) := by
  let h' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hact : ∀ (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (a : Fin 1),
      actW (Fv F v) σ J h' X a = (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a :=
    fun _ _ => rfl
  intro X
  rw [GoodTrans.mem_latV_iff b v O hO, GoodTrans.mem_latV_iff b v O hO]
  constructor
  · intro hX a i
    have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ
        ((g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact GoodTrans.mulVec_mem O _ hgiO _ (fun j => by rw [← hact]; exact hX a j) i
  · intro hX a i
    show (actW (Fv F v) σ J h' X a) i ∈ O
    rw [hact]
    exact GoodTrans.mulVec_mem O _ hgO _ (hX a) i

theorem cover_pt (σ : E →ₐ[F] E) {M d : ℕ} (J Ji : Matrix (Fin M) (Fin M) E) (hmul : J * Ji = 1)
    (hJs : ∀ i j, σ (J j i) = J i j)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F)
    (hstab : ∀ y ∈ O, sigR (Fv F v) σ y ∈ O)
    (hss : ∀ y, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y)
    (h2 : IsUnit (2 : O)) (hδ : ∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ)
    (π₁ π₂ : O) (hπ : ∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂})
    (hJO : ∀ i j, inclR (Fv F v) (J i j) ∈ O) (hJiO : ∀ i j, inclR (Fv F v) (Ji i j) ∈ O)
    (X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) (hX : X ∈ latV b v)
    (hg : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (X 0) (X 0) = 0) :
    X ∈ primV σ J b v ∨ ∃ c : O, (c = π₁ ∨ c = π₂) ∧ ¬ IsUnit c ∧
      X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * Y a i) ''
        latV b v := by
  classical
  have hXO := (GoodTrans.mem_latV_iff b v O hO X).1 hX
  let x : Fin (M + 2) → O := fun i => ⟨X 0 i, hXO 0 i⟩
  by_cases hp : ∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P
  · left
    have hJR : JR (F := F) (Fv F v) (hypOne J) = hypOne (JR (F := F) (Fv F v) J) := JR_hypOne _ J
    have hmulT : JR (F := F) (Fv F v) J * JR (F := F) (Fv F v) Ji = 1 := by
      have := congrArg (RingHom.mapMatrix (inclR (Fv F v) (F := F) (E := E))) hmul
      rwa [map_mul, map_one] at this
    obtain ⟨g, hgU, hgx, hgO, hgiO⟩ := GlobalTheory.T.primitive_vector_extends_hyperbolic _ O (sigR (Fv F v) σ) hstab hss h2 hδ π₁ π₂ hπ M
      (JR (Fv F v) J) (JR (Fv F v) Ji) hJO hJiO hmulT
      (fun i j => by
        show sigR (Fv F v) σ (inclR (Fv F v) (J j i)) = inclR (Fv F v) (J i j)
        rw [← hJs i j]
        rfl)
      x hp (by rw [← hJR]; exact hg)
    have hgH : g ∈ HR (Fv F v) σ (hypOne J) := by
      show g ∈ UJ (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J))
      rw [hJR]; exact hgU
    refine ⟨(⟨g, hgH⟩ : HR (Fv F v) σ (hypOne J)),
      latStab_of_integral σ (hypOne J) b v O hO g hgH hgO hgiO, ?_⟩
    funext a
    rw [Fin.fin_one_eq_zero a]
    exact hgx
  · right
    push_neg at hp
    obtain ⟨P, hPm, hP⟩ := hp
    have aux : ∀ c : O, P = Ideal.span {c} → ¬ IsUnit c ∧
        X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * Y a i) ''
          latV b v := by
      intro c hc
      refine ⟨fun hu => hPm.ne_top (by rw [hc]; exact Ideal.span_singleton_eq_top.2 hu), ?_⟩
      have hdiv : ∀ i, ∃ y : O, y * c = x i := fun i => by
        have := hP i
        rw [hc] at this
        exact Ideal.mem_span_singleton'.1 this
      choose y hy using hdiv
      refine ⟨fun _ i => (y i : Fv F v ⊗[F] E), ?_, ?_⟩
      · rw [GoodTrans.mem_latV_iff b v O hO]
        exact fun _ i => (y i).2
      · funext a i
        rw [Fin.fin_one_eq_zero a]
        have := congrArg Subtype.val (hy i)
        simp only [Subring.coe_mul] at this
        show (c : Fv F v ⊗[F] E) * (y i : Fv F v ⊗[F] E) = X 0 i
        rw [mul_comm]
        exact this
    rcases hπ P hPm with h | h
    · exact ⟨π₁, Or.inl rfl, aux _ h⟩
    · exact ⟨π₂, Or.inr rfl, aux _ h⟩

end Place

theorem prim_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, primV σ J b v ⊆ latV b v ∧ ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b lam 1 (M + 2)) (coordHerm (Fv F v) σ b lam 1) m → ∀ h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b, m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) ≤ m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v) + ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) := by
  intro F E _ _ _ _ _ σ h M J hJ hM d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h d b
  have hH := (GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ h M J hJ).1
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ h d b, GlobalTheory.T.local_order_two_primes_almost_all F E σ h d b,
    GlobalTheory.T.local_order_volume_almost_all F E σ h (M + 2) (hypOne J) hH (by omega) d b,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J⁻¹ i j)]
    with v hring h36 h37 hJv hJiv
  obtain ⟨O, hO, hstab, -, h2, hδ, -, -⟩ := hring
  obtain ⟨π₁, π₂, hπ, hu₁, hu₂⟩ := h36 O hO
  refine ⟨primV_subset σ J b v O hO, ?_⟩
  intro lam hlam m hm h₂
  have hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
      rw [hinv]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  have hmeas : MeasurableSet (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ h b 1 (M + 2) v
  set H := hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ with hHdef
  have hnull := hm.1 H
  set Z : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
    (gramR (Fv F v) σ (hypOne J) ⁻¹' {(H : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E))} ∩
      {X | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ with hZ
  have hnull' : m H Z = 0 := hnull
  let Sc : O → Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) := fun c =>
    {X | ¬ IsUnit c ∧ X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i =>
      (c : Fv F v ⊗[F] E) * Y a i) '' latV b v}
  have hbd : ∀ c : O, IsUnit (c : Fv F v ⊗[F] E) → m H (Sc c) ≤
      ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
    intro c hc
    by_cases hu : IsUnit c
    · have : Sc c = ∅ := by ext X; simp [Sc, hu]
      rw [this, measure_empty]
      simp
    · exact (measure_mono fun X (hX : X ∈ Sc c) => hX.2).trans (h37 O hO lam hlam m hm h₂ c hu hc _ hmeas)
  have hcov : (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) ⊆
      ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) ∪ Z := by
    intro X hX
    by_cases hXZ : X ∈ Z
    · exact Or.inr hXZ
    · left
      have hgr : gramR (Fv F v) σ (hypOne J) X = (H : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) := by
        simp only [hZ, Set.mem_compl_iff, not_not] at hXZ
        exact hXZ.1
      have hg : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (X 0) (X 0) = 0 := by
        have := congrFun (congrFun hgr 0) 0
        refine this.trans ?_
        simp [hHdef, hermOf]
      rcases cover_pt σ J J⁻¹ (Matrix.mul_nonsing_inv _ hdet) hJ.1 b v O hO hstab hss h2 hδ π₁ π₂ hπ
        (fun i j => (hO _).2 (hJv i j)) (fun i j => (hO _).2 (hJiv i j)) X hX hg with hp | ⟨c, hc, hn, hi⟩
      · exact Or.inl (Or.inl hp)
      · rcases hc with rfl | rfl
        · exact Or.inl (Or.inr ⟨hn, hi⟩)
        · exact Or.inr ⟨hn, hi⟩
  have hN : ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) =
      ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) +
        ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc m H (latV b v) ≤ m H (((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) ∪ Z) := measure_mono hcov
    _ ≤ m H ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) + m H Z := measure_union_le _ _
    _ = m H ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) := by rw [hnull', add_zero]
    _ ≤ m H (primV σ J b v ∪ Sc π₁) + m H (Sc π₂) := measure_union_le _ _
    _ ≤ m H (primV σ J b v) + m H (Sc π₁) + m H (Sc π₂) := by gcongr; exact measure_union_le _ _
    _ ≤ m H (primV σ J b v) + ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) +
        ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
      gcongr
      · exact hbd _ hu₁
      · exact hbd _ hu₂
    _ = m H (primV σ J b v) + ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
      rw [hN, add_mul, add_assoc]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc
