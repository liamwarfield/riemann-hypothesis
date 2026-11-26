module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHaarParabolicCoordinates
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicCovolumeFinite
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLatticeOrbitsFinite
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerExtra

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineIndexNeZero
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem LineIndexNeZero.proof (E W : Type*) [Field E] [NumberField E] [AddCommGroup W]
    [Module E W] : LineIndexNeZero.Statement E W :=
  _root_.UpperTheory.Reformulated.B.Gub1.proof E W

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedLenSmul
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem WeightedLenSmul.vecAt_smul (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i
  simp [vecAt, map_mul]


omit [NumberField F] [IsTotallyReal F] [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem WeightedLenSmul.invApply_vecAt_smul {h : HermitianForm F E W} {v : Basis ι E W}
    (g : archUnitary h v) (a : E) (x : W) (w : InfinitePlace E) :
    invApply g (vecAt v (a • x)) w = w.embedding a • invApply g (vecAt v x) w := by
  simp only [invApply, WeightedLenSmul.vecAt_smul, Matrix.mulVec_smul]


omit [DecidableEq ι] in
theorem WeightedLenSmul.star_smul_dotProduct_mulVec_smul (P : Matrix ι ι ℂ) (c : ℂ)
    (z : ι → ℂ) :
    star (c • z) ⬝ᵥ (P *ᵥ (c • z)) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (star z ⬝ᵥ (P *ᵥ z)) := by
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, mul_comm c, Complex.star_def, Complex.conj_mul']
  push_cast
  ring


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem WeightedLenSmul.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LenSq.Statement h v) : WeightedLenSmul.Statement h v := by
  intro M g x a
  rw [(h₁ M _).2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [WeightedLenSmul.invApply_vecAt_smul, WeightedLenSmul.star_smul_dotProduct_mulVec_smul,
    Complex.re_ofReal_mul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVolumeFormIntComb
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

theorem VolumeFormIntComb.proof : VolumeFormIntComb.Statement V d := by
  intro o b T
  have hd : finrank ℝ V = d := Fact.out
  let e : Basis (Fin d) ℝ V := Module.finBasisOfFinrankEq ℝ V hd
  have key : ∀ v : Fin d → V, o.volumeForm v = o.volumeForm e * e.det v := by
    intro v
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e o.volumeForm]
    rfl
  have hmat : e.toMatrix (fun i => ∑ j, (T i j : ℝ) • b j) =
      e.toMatrix b * (T.map (Int.cast : ℤ → ℝ))ᵀ := by
    ext k i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Basis.toMatrix_apply, Matrix.mul_apply, map_sum, map_smul, Finset.sum_apply,
      mul_comm]
  rw [key, key b, Basis.det_apply, Basis.det_apply, hmat, det_mul, det_transpose,
    Int.cast_det T]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PEigenReflection
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

private lemma expand_sandwich {ι : Type*} [Fintype ι] [DecidableEq ι] (M X X' Y : Matrix ι ι ℂ) (c a b d : ℂ)
    (h1 : X' * M = a • Y) (h2 : M * X = b • Y) (h3 : X' * M * X = d • Y) :
    (1 - c • X') * M * (1 - c • X) = M + (c * c * d - c * a - c * b) • Y := by
  have e : (1 - c • X') * M * (1 - c • X) =
      M - c • (X' * M) - c • (M * X) + (c * c) • (X' * M * X) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub,
      smul_smul]
    abel
  rw [e, h3, h1, h2]
  simp only [smul_smul, sub_smul]
  abel

theorem EigenReflection.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    EigenReflection.Statement ι := by
  intro H P hmaj ε hε v hv hAv
  obtain ⟨hP, hH, -, hPHP⟩ := hmaj
  have hPh : Pᴴ = P := hP.isHermitian
  have hHh : Hᴴ = H := hH
  set y : ι → ℂ := P *ᵥ v with hy
  set q : ℂ := star v ⬝ᵥ (P *ᵥ v) with hqdef
  have hqpos : 0 < q := hP.dotProduct_mulVec_pos hv
  have hq0 : q ≠ 0 := hqpos.ne'
  have hqstar : star q = q := Complex.conj_eq_iff_im.mpr (Complex.pos_iff.mp hqpos).2.symm
  have hεstar : star ε = ε := by rcases hε with rfl | rfl <;> simp
  set c : ℂ := 2 / q with hc
  have hcstar : star c = c := by rw [hc, star_div₀, hqstar]; simp
  have hcq : c * q = 2 := by rw [hc]; field_simp

  have hwy : star v ᵥ* P = star y := by rw [hy, star_mulVec, hPh]
  have hyv : star y ⬝ᵥ v = q := by rw [← hwy, ← dotProduct_mulVec]

  have hHv : H *ᵥ v = ε • y := by
    have : H *ᵥ v = P *ᵥ ((H⁻¹ * P) *ᵥ v) := by rw [mulVec_mulVec, ← Matrix.mul_assoc, hPHP]
    rw [this, show (H⁻¹ * P) *ᵥ v = ε • v from hAv, mulVec_smul]
  have hvH : star v ᵥ* H = ε • star y := by
    rw [← hHh, ← star_mulVec, hHv, star_smul, hεstar]

  have hR : pReflection P v = 1 - c • vecMulVec v (star y) := by
    rw [pReflection, ← hqdef, ← hc, vecMulVec_mul, hwy]
  have hRh : (pReflection P v)ᴴ = 1 - c • vecMulVec y (star v) := by
    rw [hR, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hcstar,
      conjTranspose_vecMulVec, star_star]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hRh, hR]
    have h1 : vecMulVec y (star v) * P = (1 : ℂ) • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hwy, one_smul]
    have h2 : P * vecMulVec v (star y) = (1 : ℂ) • vecMulVec y (star y) := by
      rw [mul_vecMulVec, ← hy, one_smul]
    have h3 : vecMulVec y (star v) * P * vecMulVec v (star y) = q • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hwy, vecMulVec_mul_vecMulVec, hyv, vecMulVec_smul]
    rw [expand_sandwich P _ _ _ c 1 1 q h1 h2 h3]
    have : c * c * q - c * 1 - c * 1 = 0 := by
      rw [mul_assoc, hcq]; ring
    rw [this, zero_smul, add_zero]
  · rw [hRh, hR]
    have h1 : vecMulVec y (star v) * H = ε • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hvH, vecMulVec_smul]
    have h2 : H * vecMulVec v (star y) = ε • vecMulVec y (star y) := by
      rw [mul_vecMulVec, hHv]
      ext i j
      simp [vecMulVec_apply, mul_assoc]
    have h3 : vecMulVec y (star v) * H * vecMulVec v (star y) = (ε * q) • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hvH, vecMulVec_mul_vecMulVec, smul_dotProduct, hyv, vecMulVec_smul]
      rfl
    rw [expand_sandwich H _ _ _ c ε ε (ε * q) h1 h2 h3]
    have : c * c * (ε * q) - c * ε - c * ε = 0 := by
      have : c * c * (ε * q) = (c * q) * c * ε := by ring
      rw [this, hcq]; ring
    rw [this, zero_smul, add_zero]
  · rw [hR, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hyv]
    rw [op_smul_eq_smul, smul_smul, hcq, two_smul]; abel
  · intro u hu
    have hyu : star y ⬝ᵥ u = 0 := by rw [← hwy, ← dotProduct_mulVec, hu]
    rw [hR, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hyu]
    simp

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegralFamilyBound
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem IntegralFamilyBound.proof (E : Type*) [Field E] [NumberField E] :
    IntegralFamilyBound.Statement E := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = finrank ℚ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let e : Fin (finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    (Fintype.equivFinOfCardEq hcard).symm
  let a : Fin (finrank ℚ E) → 𝓞 E := fun i => RingOfIntegers.basis E (e i)
  refine ⟨∑ i, ∑ σ : E →+* ℂ, ‖σ (a i)‖, a, ?_, ?_⟩
  · have := (integralBasis E).linearIndependent.comp e e.injective
    convert this using 1
    funext i
    simp [a, integralBasis_apply]
  · intro i σ
    calc ‖σ (a i)‖ ≤ ∑ σ' : E →+* ℂ, ‖σ' (a i)‖ :=
          Finset.single_le_sum (f := fun σ' : E →+* ℂ => ‖σ' (a i)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      _ ≤ ∑ j, ∑ σ' : E →+* ℂ, ‖σ' (a j)‖ :=
          Finset.single_le_sum (f := fun j => ∑ σ' : E →+* ℂ, ‖σ' (a j)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMinkowskiVolumeForm
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory Submodule

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

theorem MinkowskiVolumeForm.proof : MinkowskiVolumeForm.Statement V d := by
  classical
  intro o b lam hlam hmin
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have hd : finrank ℝ V = d := Fact.out

  have hcomb : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨z, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hz : z ≠ 0 := by
      rintro rfl
      simp at hx0
    simpa [← Int.cast_smul_eq_zsmul ℝ] using hmin z hz
  have hdisc : DiscreteTopology (span ℤ (Set.range b)) :=
    DiscreteTopology.of_forall_le_norm hlam fun x hx => hcomb x x.2 (by simpa using hx)
  have hZ : LinearIndependent ℤ b := by
    rw [Fintype.linearIndependent_iff]
    intro z hz
    by_contra hne
    have hz' : z ≠ 0 := fun h => hne (fun i => by simp [h])
    have h1 := hmin z hz'
    have h2 : ∑ i, (z i : ℝ) • b i = 0 := by simpa [Int.cast_smul_eq_zsmul] using hz
    rw [h2, norm_zero] at h1
    linarith
  have hR : LinearIndependent ℝ b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc,
      Set.finrank, finrank_span_eq_card hZ]
  have hcard : Fintype.card (Fin d) = finrank ℝ V := by simp [hd]
  let B : Basis (Fin d) ℝ V := Basis.mk hR (hR.span_eq_top_of_card_eq_finrank' hcard).ge
  have hB : ⇑B = b := Basis.coe_mk _ _

  have hF : volume (ZSpan.fundamentalDomain B) = ENNReal.ofReal |o.volumeForm b| := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped B volume), ← o.measure_eq_volume,
      AlternatingMap.measure_parallelepiped, hB]

  let e : OrthonormalBasis (Fin d) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hd)
  set σ : ℝ := lam / Real.sqrt d with hσ
  have hσ0 : 0 ≤ σ := div_nonneg hlam.le (Real.sqrt_nonneg _)
  let φ : V →ₗ[ℝ] (Fin d → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap ∘ₗ e.repr.toLinearEquiv.toLinearMap
  let P : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Ioo (-σ) σ
  let s : Set V := φ ⁻¹' P
  have hs_mem : ∀ v, v ∈ s ↔ ∀ i, |e.repr v i| < σ := by
    intro v
    simp only [s, P, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo, abs_lt]
    rfl
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    rw [hs_mem] at hx ⊢
    intro i
    simpa using hx i
  have hconv : Convex ℝ s := (convex_pi fun _ _ => convex_Ioo _ _).linear_preimage φ
  have hvol : volume s = ENNReal.ofReal (2 * σ) ^ d := by
    have hmp : MeasurePreserving (fun v : V => WithLp.ofLp (e.repr v)) volume volume :=
      (PiLp.volume_preserving_ofLp (Fin d)).comp e.measurePreserving_repr
    rw [show s = (fun v : V => WithLp.ofLp (e.repr v)) ⁻¹' P from rfl,
      hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  by_contra hlt
  push Not at hlt
  have hlt' : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ V < volume s := by
    rw [hd]
    have h : ENNReal.ofReal (|o.volumeForm b| * 2 ^ d) < ENNReal.ofReal ((2 * σ) ^ d) := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), mul_pow, mul_comm]
      exact mul_lt_mul_of_pos_left hlt (by positivity)
    rwa [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (mul_nonneg zero_le_two hσ0),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← hF, ← hvol] at h
  have hcount : Countable (span ℤ (Set.range B)).toAddSubgroup := by
    change Countable (span ℤ (Set.range B))
    infer_instance
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' B volume) hsymm hconv hlt'
  have hx0' : x ≠ 0 := by
    rintro rfl
    exact hx0 rfl
  have h1 : lam ≤ ‖x‖ := hcomb x (by rw [← hB]; exact hxL) hx0'
  have h2 : ‖x‖ < lam := by
    rw [hs_mem] at hxs
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · exact absurd (@Subsingleton.elim _ (finrank_zero_iff.1 (hd.trans hd0)) x 0) hx0'
    · have hσpos : 0 < σ := div_pos hlam (Real.sqrt_pos.2 (by exact_mod_cast hdpos))
      have hsq : (d : ℝ) * σ ^ 2 = lam ^ 2 := by
        rw [hσ, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        field_simp
      rw [← e.repr.norm_map, EuclideanSpace.norm_eq]
      calc Real.sqrt (∑ i, ‖e.repr x i‖ ^ 2) < Real.sqrt (∑ _i : Fin d, σ ^ 2) := by
            apply Real.sqrt_lt_sqrt (by positivity)
            apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hdpos⟩⟩)
            intro i _
            rw [Real.norm_eq_abs, sq_lt_sq, abs_of_pos hσpos, abs_abs]
            exact hxs i
        _ = lam := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsq,
              Real.sqrt_sq hlam.le]
  linarith

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIndexLeDet
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module Matrix

theorem IndexLeDet.proof (E : Type*) [Field E] [NumberField E] : IndexLeDet.Statement E := by
  classical
  intro A hA e a T ha hT
  have hmem : ∀ i, (a i : E) ∈ A := fun i => hA ⟨a i, rfl⟩
  let b : Fin (finrank ℚ E) → A := fun i => ⟨a i, hmem i⟩
  have hb : ∀ i, b i = ∑ j, T i j • e j := by
    intro i
    apply Subtype.ext
    simp [b, hT i]

  have hdet : T.det ≠ 0 := by
    intro h0
    have h0' : ((Int.castRingHom ℚ).mapMatrix T).det = 0 := by
      rw [← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0'
    have hsum : ∑ i, v i • (a i : E) = 0 := by
      calc ∑ i, v i • (a i : E)
          = ∑ i, ∑ j, (v i * (T i j : ℚ)) • (e j : E) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hT i, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
        _ = ∑ j, (∑ i, v i * (T i j : ℚ)) • (e j : E) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_smul]
        _ = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            have := congrFun hv j
            simp only [vecMul, dotProduct, RingHom.mapMatrix_apply, map_apply, eq_intCast,
              Pi.zero_apply] at this
            rw [this, zero_smul]
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.mp ha v hsum i)

  have hliE : LinearIndependent ℤ (fun i => (a i : E)) := ha.restrict_scalars' ℤ
  have hli : LinearIndependent ℤ b :=
    LinearIndependent.of_comp (A.subtype.toIntLinearMap) hliE
  have : Module.Free ℤ A := Module.Free.of_basis e
  have : Module.Finite ℤ A := Module.Finite.of_basis e
  set N := Submodule.span ℤ (Set.range b) with hN
  let bN := Basis.span hli
  have hbN : ((↑) ∘ bN : Fin (finrank ℚ E) → A) = b := funext fun i => congrArg Subtype.val (Basis.span_apply hli i)
  have hcard := Submodule.natAbs_det_basis_change e N bN
  rw [hbN] at hcard
  have hdetb : e.det b = T.det := by
    rw [Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.transpose_apply, Basis.toMatrix_apply, hb i, map_sum]
    simp [Finsupp.single_apply]
  rw [hdetb] at hcard

  have hle : N.toAddSubgroup ≤ (intSubgroup E).addSubgroupOf A := by
    have : N ≤ ((intSubgroup E).addSubgroupOf A).toIntSubmodule := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show b i ∈ (intSubgroup E).addSubgroupOf A
      rw [AddSubgroup.mem_addSubgroupOf]
      exact ⟨a i, rfl⟩
    exact this
  have hidx : N.toAddSubgroup.index = T.det.natAbs := hcard.symm
  have hdvd := AddSubgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  have hle' : (intSubgroup E).relIndex A ≤ T.det.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hdet) hdvd
  calc ((intSubgroup E).relIndex A : ℝ) ≤ (T.det.natAbs : ℝ) := by exact_mod_cast hle'
    _ = |(T.det : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegerSmallAtPlaces
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem IntegerSmallAtPlaces.proof (E : Type*) [Field E] [NumberField E] :
    IntegerSmallAtPlaces.Statement E := by
  intro a ha hlt
  by_contra hne
  let b : 𝓞 E := ⟨a, ha⟩
  have hb : b ≠ 0 := fun h => hne (congrArg Subtype.val h)
  let w : InfinitePlace E := Classical.arbitrary _
  have h1 : 1 ≤ w b := InfinitePlace.one_le_of_lt_one hb (fun z _ => hlt z)
  exact absurd (hlt w) (not_lt.mpr h1)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIsotropicSplit
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix

theorem IsotropicSplit.proof (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : EigenspacesOrthogonal.Statement ι) : IsotropicSplit.Statement ι := by
  intro H P hM z hz
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hA2 : A * A = 1 := by
    rw [hAdef, majInvolution, show H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPHP, nonsing_inv_mul H hdet]
  have hPA : P * A = H := by
    rw [hAdef, majInvolution, ← Matrix.mul_assoc, hPHP]
  have hAA (v : ι → ℂ) : A *ᵥ (A *ᵥ v) = v := by
    rw [mulVec_mulVec, hA2, one_mulVec]
  set a := plusPart H P z with hadef
  set b := minusPart H P z with hbdef
  have ha : A *ᵥ a = a := by
    rw [hadef, plusPart, ← hAdef, mulVec_smul, mulVec_add, hAA, add_comm]
  have hb : A *ᵥ b = -b := by
    rw [hbdef, minusPart, ← hAdef, mulVec_smul, mulVec_sub, hAA, ← smul_neg, neg_sub]
  have hzab : z = a + b := by
    rw [hadef, hbdef, plusPart, minusPart, ← smul_add]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hAzab : A *ᵥ z = a - b := by
    rw [hadef, hbdef, plusPart, minusPart, ← hAdef, ← smul_sub]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hab : star a ⬝ᵥ (P *ᵥ b) = 0 := h₁ H P ⟨hP, hH, hdet, hPHP⟩ a b ha hb
  have hba : star b ⬝ᵥ (P *ᵥ a) = 0 := by
    rw [star_dotProduct, star_mulVec, ← dotProduct_mulVec, hP.1.eq, hab, star_zero]
  refine ⟨ha, hb, ?_⟩
  have h0 : star (a + b) ⬝ᵥ (P *ᵥ (a - b)) = 0 := by
    rw [← hAzab, ← hzab, mulVec_mulVec, hPA, hz]
  rw [star_add, add_dotProduct, mulVec_sub, dotProduct_sub, dotProduct_sub, hab, hba] at h0
  linear_combination h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusIntegralHomogeneous
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {κ : Type*} [Fintype κ]

private lemma weighted_sum_smul (q : κ → ℝ) (t : ℝ) (b : κ → ℂ) :
    ∑ i, q i * ‖(t • b) i‖ ^ 2 = t ^ 2 * ∑ i, q i * ‖b i‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private lemma prod_smul (n : ℕ) {t : ℝ} (ht : 0 < t) (b : κ → ℂ) :
    ∏ i, ‖(t • b) i‖ₑ ^ (2 * n) =
      ENNReal.ofReal (t ^ (2 * n * Fintype.card κ)) * ∏ i, ‖b i‖ₑ ^ (2 * n) := by
  simp_rw [Pi.smul_apply, enorm_smul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul,
    Real.enorm_eq_ofReal ht.le, ENNReal.ofReal_pow ht.le]

private lemma indicator_smul (q : κ → ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) (b : κ → ℂ) :
    {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
        (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) (t • b) =
      ENNReal.ofReal (t ^ (2 * n * Fintype.card κ)) *
        {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b := by
  have hmem : (t • b) ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2} ↔
      b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} := by
    simp only [Set.mem_ofPred_eq, weighted_sum_smul, one_pow]
    exact mul_lt_iff_lt_one_right (by positivity)
  by_cases hb : b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}
  · rw [Set.indicator_of_mem (hmem.2 hb), Set.indicator_of_mem hb, prod_smul n ht]
  · rw [Set.indicator_of_notMem (fun h => hb (hmem.1 h)), Set.indicator_of_notMem hb, mul_zero]

private lemma measurable_integrand (q : κ → ℝ) (n : ℕ) (s : ℝ) :
    Measurable ({b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < s}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n))) := by
  refine Measurable.indicator ?_ ?_
  · exact Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).enorm.pow_const _
  · exact measurableSet_lt (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).norm.pow_const 2)) measurable_const

private lemma finrank_fun_complex : Module.finrank ℝ (κ → ℂ) = 2 * Fintype.card κ := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, mul_comm]

private lemma integral_scaling (q : κ → ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
        (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b =
      (∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
        (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b) *
        ENNReal.ofReal (t ^ ((2 * n + 2) * Fintype.card κ)) := by
  set g : (κ → ℂ) → ℝ≥0∞ := {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
    (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) with hg
  have hpt : ∀ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b =
        ENNReal.ofReal (t ^ (2 * n * Fintype.card κ)) * g (t⁻¹ • b) := by
    intro b
    have h := indicator_smul q n ht (t⁻¹ • b)
    rwa [smul_inv_smul₀ ht.ne'] at h
  have hmeas : Measurable g := measurable_integrand q n _
  have hmap : ∫⁻ b : κ → ℂ, g (t⁻¹ • b) =
      ENNReal.ofReal (t ^ (2 * Fintype.card κ)) * ∫⁻ b, g b := by
    rw [← lintegral_map hmeas (measurable_const_smul _),
      Measure.map_addHaar_smul volume (inv_ne_zero ht.ne'), lintegral_smul_measure,
      finrank_fun_complex, inv_pow, inv_inv, abs_of_pos (by positivity : 0 < t ^ (2 * Fintype.card κ)),
      smul_eq_mul]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    mul_comm, ← ENNReal.ofReal_mul (by positivity), ← pow_add]
  congr 3
  ring

theorem TorusIntegralHomogeneous.proof (κ : Type*) [Fintype κ] :
    TorusIntegralHomogeneous.Statement κ := by
  intro q hq n
  refine ⟨∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b, ?_, ?_, fun t ht => integral_scaling q n ht⟩
  ·
    rw [lintegral_pos_iff_support (measurable_integrand q n _)]
    have hS : 0 ≤ ∑ i, q i := Finset.sum_nonneg fun i _ => (hq i).le
    let V : Set (κ → ℂ) :=
      {b | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} ∩ ⋂ i, {b | b i ≠ 0}
    have hVo : IsOpen V :=
      (isOpen_lt (by fun_prop) continuous_const).inter
        (isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const)
    have hVne : V.Nonempty := by
      have hx : 0 < ((∑ i, q i) + 1)⁻¹ := by positivity
      have h1 : ‖((((∑ i, q i) + 1)⁻¹ : ℝ) : ℂ)‖ = ((∑ i, q i) + 1)⁻¹ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hx.le]
      refine ⟨fun _ => ((((∑ i, q i) + 1)⁻¹ : ℝ) : ℂ), ?_, ?_⟩
      · show ∑ i, q i * ‖((((∑ i, q i) + 1)⁻¹ : ℝ) : ℂ)‖ ^ 2 < 1 ^ 2
        rw [h1, ← Finset.sum_mul, one_pow, inv_pow, ← div_eq_mul_inv,
          div_lt_one (by positivity)]
        nlinarith
      · exact Set.mem_iInter.2 fun i => Complex.ofReal_ne_zero.2 hx.ne'
    refine lt_of_lt_of_le (hVo.measure_pos volume hVne) (measure_mono ?_)
    rintro b ⟨hb1, hb2⟩
    rw [Function.mem_support, Set.indicator_of_mem hb1]
    exact Finset.prod_ne_zero_iff.2 fun i _ =>
      pow_ne_zero _ (enorm_ne_zero.2 (Set.mem_iInter.1 hb2 i))
  ·
    set R : ℝ := ∑ i, (q i)⁻¹ + 1 with hR
    have hR1 : 1 ≤ R := by
      have : 0 ≤ ∑ i, (q i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.2 (hq i)).le
      linarith
    have hbd : ∀ b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}, ∀ i, ‖b i‖ < R := by
      intro b hb i
      have hb' : ∑ j, q j * ‖b j‖ ^ 2 < 1 := by simpa using hb
      have hi : q i * ‖b i‖ ^ 2 < 1 :=
        lt_of_le_of_lt (Finset.single_le_sum (f := fun j => q j * ‖b j‖ ^ 2)
          (fun j _ => mul_nonneg (hq j).le (sq_nonneg _)) (Finset.mem_univ i)) hb'
      have hsq : ‖b i‖ ^ 2 < (q i)⁻¹ := by
        calc ‖b i‖ ^ 2 = (q i)⁻¹ * (q i * ‖b i‖ ^ 2) := by
              rw [← mul_assoc, inv_mul_cancel₀ (hq i).ne', one_mul]
          _ < (q i)⁻¹ * 1 := mul_lt_mul_of_pos_left hi (inv_pos.2 (hq i))
          _ = (q i)⁻¹ := mul_one _
      have hle : (q i)⁻¹ ≤ ∑ j, (q j)⁻¹ :=
        Finset.single_le_sum (f := fun j => (q j)⁻¹) (fun j _ => (inv_pos.2 (hq j)).le)
          (Finset.mem_univ i)
      have hx := norm_nonneg (b i)
      by_contra! h
      nlinarith
    have hsub : {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} ⊆ Metric.ball 0 R := by
      intro b hb
      rw [mem_ball_zero_iff, pi_norm_lt_iff (by linarith)]
      exact hbd b hb
    have hle : {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) ≤
        {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun _ => ∏ _i : κ, ENNReal.ofReal R ^ (2 * n)) := by
      intro b
      by_cases hb : b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
        refine Finset.prod_le_prod' fun i _ => pow_le_pow_left' ?_ _
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbd b hb i).le
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
    calc _ ≤ ∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun _ => ∏ _i : κ, ENNReal.ofReal R ^ (2 * n)) b := lintegral_mono hle
      _ ≤ (∏ _i : κ, ENNReal.ofReal R ^ (2 * n)) *
          volume {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} := lintegral_indicator_const_le _ _
      _ < ⊤ := ENNReal.mul_lt_top
          (ENNReal.prod_lt_top fun i _ => ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          (lt_of_le_of_lt (measure_mono hsub) measure_ball_lt_top)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

section Matrices

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem MajorantBound.full : MajorantBound.Statement ι := MajorantBound.proof ι

theorem EigenspacesOrthogonal.full : EigenspacesOrthogonal.Statement ι :=
  EigenspacesOrthogonal.proof ι

theorem EigenReflection.full : EigenReflection.Statement ι := EigenReflection.proof ι

theorem EigenReflectionMaps.full : EigenReflectionMaps.Statement ι :=
  EigenReflectionMaps.proof ι (EigenReflection.full ι) (EigenspacesOrthogonal.full ι)

theorem IsotropicSplit.full : IsotropicSplit.Statement ι :=
  IsotropicSplit.proof ι (EigenspacesOrthogonal.full ι)

theorem PhaseOnMinus.full : PhaseOnMinus.Statement ι := PhaseOnMinus.proof ι

theorem KTransitive.full : KTransitive.Statement ι :=
  KTransitive.proof ι (IsotropicSplit.full ι) (EigenReflectionMaps.full ι) (PhaseOnMinus.full ι)
    (EigenspacesOrthogonal.full ι)

end Matrices

section Groups

theorem UnfoldOrbit.full (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] :
    UnfoldOrbit.Statement G :=
  UnfoldOrbit.proof G

theorem DiscreteFundamentalDomain.full (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] : DiscreteFundamentalDomain.Statement G :=
  DiscreteFundamentalDomain.proof G

theorem TorusIntegralHomogeneous.full (κ : Type*) [Fintype κ] :
    TorusIntegralHomogeneous.Statement κ :=
  TorusIntegralHomogeneous.proof κ

theorem BoundedIndexSubgroupsFinite.full (G : Type*) [AddCommGroup G] :
    BoundedIndexSubgroupsFinite.Statement G :=
  BoundedIndexSubgroupsFinite.proof G

theorem MinkowskiVolumeForm.full (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) [Fact (finrank ℝ V = d)] : MinkowskiVolumeForm.Statement V d :=
  MinkowskiVolumeForm.proof V d

theorem VolumeFormIntComb.full (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) [Fact (finrank ℝ V = d)] : VolumeFormIntComb.Statement V d :=
  VolumeFormIntComb.proof V d

end Groups

section Numbers

variable (E : Type*) [Field E] [NumberField E]

theorem IntegerSmallAtPlaces.full : IntegerSmallAtPlaces.Statement E := IntegerSmallAtPlaces.proof E

theorem CoeffLatticeBasis.full : CoeffLatticeBasis.Statement E := CoeffLatticeBasis.proof E

theorem IndexLeDet.full : IndexLeDet.Statement E := IndexLeDet.proof E

theorem WeightedNormSq.full : WeightedNormSq.Statement E := WeightedNormSq.proof E

theorem IntegralFamilyBound.full : IntegralFamilyBound.Statement E := IntegralFamilyBound.proof E

theorem WeightedSpaceDim.full [_root_.NumberField.IsTotallyComplex E] : WeightedSpaceDim.Statement E :=
  WeightedSpaceDim.proof E

theorem WeightedIndexBound.full [_root_.NumberField.IsTotallyComplex E] : WeightedIndexBound.Statement E :=
  WeightedIndexBound.proof E (CoeffLatticeBasis.full E) (IndexLeDet.full E) (WeightedNormSq.full E)
    (WeightedSpaceDim.full E) (MinkowskiVolumeForm.full _ _) (VolumeFormIntComb.full _ _)

variable (W : Type*) [AddCommGroup W] [Module E W]

theorem LineIndexNeZero.full : LineIndexNeZero.Statement E W := LineIndexNeZero.proof E W

theorem LineIndexCoeffs.full : LineIndexCoeffs.Statement (E := E) W := LineIndexCoeffs.proof E W

theorem LineCoeffsFG.full : LineCoeffsFG.Statement (E := E) W := LineCoeffsFG.proof W

end Numbers

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)

theorem HermAtPlace.full : HermAtPlace.Statement h v := HermAtPlace.proof h v

theorem GramAtData.full : GramAtData.Statement h v := GramAtData.proof h v

theorem ArchInvariant.full : ArchInvariant.Statement h v := ArchInvariant.proof h v

theorem LenSq.full : LenSq.Statement h v := LenSq.proof h v

theorem VecAtNeZero.full : VecAtNeZero.Statement v := VecAtNeZero.proof v

theorem WeightedLenSmul.full : WeightedLenSmul.Statement h v :=
  WeightedLenSmul.proof h v (LenSq.full h v)

theorem WeightPos.full : WeightPos.Statement h v := WeightPos.proof h v (VecAtNeZero.full v)

theorem MajorantExists.full : MajorantExists.Statement h v :=
  MajorantExists.proof h v (GramAtData.full h v)

theorem ArchLatticeDiscrete.full : ArchLatticeDiscrete.Statement h v := ArchLatticeDiscrete.proof h v

theorem LenCauchySchwarz.full : LenCauchySchwarz.Statement h v := LenCauchySchwarz.proof h v

theorem BoundedInverseCompact.full : BoundedInverseCompact.Statement h v :=
  BoundedInverseCompact.proof h v

theorem GramDetermines.full : GramDetermines.Statement h := GramDetermines.proof h

theorem WittPartner.full : WittPartner.Statement h := WittPartner.proof h

theorem ComplementForm.full : ComplementForm.Statement h := ComplementForm.proof h

theorem IsotropicScaling.full : IsotropicScaling.Statement h :=
  IsotropicScaling.proof h (WittPartner.full h)

theorem HyperbolicPairTransitive.full [FiniteDimensional E W] :
    HyperbolicPairTransitive.Statement h :=
  HyperbolicPairTransitive.proof h

theorem ShortVectorIsotropic.full : ShortVectorIsotropic.Statement h v :=
  ShortVectorIsotropic.proof h v (HermAtPlace.full h v) (GramAtData.full h v) (ArchInvariant.full h v)
    (MajorantBound.full ι) (LenSq.full h v) (IntegerSmallAtPlaces.full E)

theorem ShortestVectorIndex.full : ShortestVectorIndex.Statement h v :=
  ShortestVectorIndex.proof h v (LineIndexCoeffs.full E W) (LineCoeffsFG.full E W)
    (WeightedLenSmul.full h v) (WeightPos.full h v) (WeightedIndexBound.full E)

theorem ParabolicDecomposition.full : ParabolicDecomposition.Statement h v :=
  ParabolicDecomposition.proof h v (KTransitive.full ι) (HermAtPlace.full h v) (GramAtData.full h v)
    (ArchInvariant.full h v) (VecAtNeZero.full v)

end Spaces

section Conditional

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem MahlerCompactness.full_of {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) : MahlerCompactness.Statement h v :=
  MahlerCompactness.proof h v (BoundedGenerators.proof h v hR hA hT) (LenCauchySchwarz.full h v)
    (GramDetermines.full h) (BoundedInverseCompact.full h v)

theorem AdaptedReduction.full_of {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (h : HermitianForm F E W) (hLN : LineNormalForm.Statement h)
    (hCL : ComplementLattice.Statement h) : AdaptedReduction.Statement h :=
  AdaptedReduction.proof h (HyperbolicPairTransitive.full h) hLN hCL

theorem LinePairOrbitsFinite.full_of {W : Type u} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h : HermitianForm F E W)
    (hB : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (hCE : ComplementExtension.Statement h)
    (hLN : LineNormalForm.Statement h) (hCL : ComplementLattice.Statement h) :
    LinePairOrbitsFinite.Statement h :=
  LinePairOrbitsFinite.proof h hB (WittPartner.full h) (ComplementForm.full h) hCE
    (AdaptedReduction.full_of h hLN hCL)

theorem LatticeOrbitsFinite.step_of {W : Type u} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h : HermitianForm F E W)
    (hB : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (hR : ReducedBasisBound.Statement)
    (hA : ArchCovolumeBound.Statement h (Module.finBasis E W))
    (hT : MajorantTransport.Statement h (Module.finBasis E W))
    (hCE : ComplementExtension.Statement h) (hLN : LineNormalForm.Statement h)
    (hCL : ComplementLattice.Statement h) : LatticeOrbitsFinite.Statement h :=
  LatticeOrbitsFinite.proof h (Module.finBasis E W) (MahlerCompactness.full_of h _ hR hA hT)
    (MajorantExists.full h _) (ShortVectorIsotropic.full h _)
    (LinePairOrbitsFinite.full_of h hB hCE hLN hCL)

theorem LatticeOrbitsFiniteBelow.of_steps (hR : ReducedBasisBound.Statement)
    (hA : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchCovolumeBound.Statement h v)
    (hT : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantTransport.Statement h v)
    (hCE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementExtension.Statement h)
    (hLN : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), LineNormalForm.Statement h)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementLattice.Statement h)
    (N : ℕ) : LatticeOrbitsFiniteBelow.{u} F E N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ _ _ h hN
    exact LatticeOrbitsFinite.step_of h (ih _ hN) hR (hA W h _ _) (hT W h _ _) (hCE W h)
      (hLN W h) (hCL W h)

theorem ScalingLaw.full_of {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hP : LinePairOrbitsFinite.Statement h) (hU : UnfoldingIntegral.Statement h v) :
    ScalingLaw.Statement h v :=
  ScalingLaw.proof h v hU
    (VectorOrbitsFinite.proof h hP (IsotropicScaling.full h) (BoundedIndexSubgroupsFinite.full W)
      (LineIndexNeZero.full E W))
    (UnfoldOrbit.full _) (DiscreteFundamentalDomain.full _) (ArchLatticeDiscrete.full h v)

theorem UnfoldingIntegral.full_of {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hUA : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (hHP : HaarParabolicCoordinates.Statement h v) (hSC : StabilizerCovolumeFinite.Statement h v) :
    UnfoldingIntegral.Statement h v :=
  UnfoldingIntegral.proof h v (UnfoldingTorus.proof h v hUA hHP hSC)
    (TorusIntegralHomogeneous.full _) (DiscreteFundamentalDomain.full _)

theorem ArithmeticCovolumeFinite.step_of {W : Type u} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {ι : Type*} [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W)
    (v : Basis ι E W) (hL : LatticeOrbitsFiniteBelow.{u} F E (finrank E W))
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) (hCE : ComplementExtension.Statement h)
    (hLN : LineNormalForm.Statement h) (hCL : ComplementLattice.Statement h)
    (hUA : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (hHP : HaarParabolicCoordinates.Statement h v) (hSC : StabilizerCovolumeFinite.Statement h v)
    (hPB : LatticePointsBelowFinite.Statement h v) : ArithmeticCovolumeFinite.Statement h v :=
  ArithmeticCovolumeFinite.proof h v
    (ScalingLaw.full_of h v (LinePairOrbitsFinite.full_of h hL hCE hLN hCL)
      (UnfoldingIntegral.full_of h v hUA hHP hSC))
    (MahlerCompactness.full_of h v hR hA hT) (ShortVectorIsotropic.full h v)
    (ShortestVectorIndex.full h v) (IntegralFamilyBound.full E) (MajorantExists.full h v)
    (ArchLatticeDiscrete.full h v) hPB

theorem CovolumeFiniteBelow.of_steps (hR : ReducedBasisBound.Statement)
    (hA : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchCovolumeBound.Statement h v)
    (hT : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantTransport.Statement h v)
    (hCE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementExtension.Statement h)
    (hLN : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), LineNormalForm.Statement h)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementLattice.Statement h)
    (hUA : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W) (M : Majorant h v),
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (hHP : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W),
      HaarParabolicCoordinates.Statement h v)
    (hSC : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W),
      CovolumeFiniteBelow.{u} F E (finrank E W) → StabilizerCovolumeFinite.Statement h v)
    (hPB : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W),
      LatticePointsBelowFinite.Statement h v)
    (N : ℕ) : CovolumeFiniteBelow.{u} F E N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ _ _ h n v hN
    exact ArithmeticCovolumeFinite.step_of h v
      (LatticeOrbitsFiniteBelow.of_steps hR hA hT hCE hLN hCL _) hR (hA W h n v) (hT W h n v)
      (hCE W h) (hLN W h) (hCL W h) (hUA W h n v) (hHP W h n v) (hSC W h n v (ih _ hN))
      (hPB W h n v)

theorem AdelicCovolumeFinite.full_of {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {ι : Type*} [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W)
    (v : Basis ι E W) (hL : LatticeOrbitsFinite.Statement h)
    (hC : ArithmeticCovolumeFinite.Statement h v) (hAU : ArchimedeanUnitaryEquiv.Statement h v)
    (hAL : AdelicLatticeDictionary.Statement h v)
    (hDC : DoubleCosetCovolume.Statement (unitaryPoints F E (gram h.toSesq v) 𝔸[F])
      (archUnitary h v) (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) :
    AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.proof h v hL hC hAU hAL hDC

end Conditional

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
