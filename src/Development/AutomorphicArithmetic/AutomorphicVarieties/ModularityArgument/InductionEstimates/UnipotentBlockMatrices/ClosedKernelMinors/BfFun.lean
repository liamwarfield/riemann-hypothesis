module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

theorem bfFun :
    ∀ {K : Type} [Field K] [NumberField K] (f : G1 K (2 + 2) → ℂ) (β : ℝ → ℂ),
      SFun f → Continuous β → HasCompactSupport β →
        PFun (bf β f) ∧ InBand (bf β f) ∧ Decays (bf β f) := by
  intro K _ _ f β hf hβ hc
  obtain ⟨h1, -, h3, h4, -⟩ := hpSpec (K := K)
  obtain ⟨-, -, hl, -⟩ := blkLaws (K := K)
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℂ, w = fun t => β t * Complex.exp ((((2 + 2 : ℕ) : ℝ) / 2 * t : ℝ) : ℂ) := ⟨_, rfl⟩
  have hbf : ∀ g, bf β f g = w (HH g) * f g := fun g => by rw [hw]; rfl
  have hwc : Continuous w := by
    rw [hw]
    exact hβ.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  have hws : HasCompactSupport w := by
    rw [hw]
    exact hc.mul_right
  obtain ⟨B, hB⟩ := hwc.bounded_above_of_compact_support hws
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hn : ∀ (X : UPos (2 + 2) 2 → 𝔸[K]) (g : G1 K (2 + 2)), HH (nn X * g) = HH g := fun X g => by
    have := h1 X 1 1 0 g
    rwa [hl, mul_one, zero_add] at this
  have hm : ∀ (m₁ m₂ : G1 K 2) (g : G1 K (2 + 2)), HH (lv m₁ m₂ 0 * g) = HH g := fun m₁ m₂ g => by
    have := h1 0 m₁ m₂ 0 g
    rwa [mul_assoc, hn, zero_add] at this
  have hle : ∀ g, ‖bf β f g‖ ≤ B * ‖f g‖ := fun g => by
    rw [hbf, norm_mul]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [show bf β f = fun g => w (HH g) * f g from funext hbf]
    exact (hwc.comp h4).mul hf.cont
  · obtain ⟨C, hC⟩ := hf.bdd
    exact ⟨B * C, fun g => (hle g).trans (mul_le_mul_of_nonneg_left (hC g) hB0)⟩
  · intro X g
    rw [hbf, hbf, hn, hf.unip]
  · intro γ hγ g
    rw [hbf, hbf, h3 γ hγ, hf.rat γ hγ]
  · intro g
    simp_rw [hbf, hm]
    rw [integral_const_mul, hf.cusp₁ g, mul_zero]
  · intro g
    simp_rw [hbf, hm]
    rw [integral_const_mul, hf.cusp₂ g, mul_zero]
  · obtain ⟨R, hR⟩ := hws.isCompact.isBounded.exists_norm_le
    refine ⟨R, fun g hg => ?_⟩
    rw [hbf] at hg
    exact hR _ (subset_tsupport w (left_ne_zero_of_mul hg))
  · intro N R
    obtain ⟨C, hC⟩ := hf.dec N R
    refine ⟨B * C, fun x hx => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hC x hx
    refine ⟨γ, hγ, ?_⟩
    refine (mul_le_mul_of_nonneg_right (hle x) (pow_nonneg (AutomorphicForm.height_pos _).le N)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h hB0

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem lf_fin {K : Type} [Field K] [NumberField K] {S : Set 𝔸[K]} (hS : IsCompact S) :
    {k : K | algebraMap K 𝔸[K] k ∈ S}.Finite := by
  have h1 := GroundTheory.Global.discreteTopology_principalSubgroup K
  have h2 := GroundTheory.Global.isClosed_principalSubgroup K
  have h3 : IsCompact ((Subtype.val : NumberField.AdeleRing.principalSubgroup (𝓞 K) K → 𝔸[K]) ⁻¹' S) :=
    h2.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  have h4 := h3.finite_of_discrete
  refine Set.Finite.of_finite_image (f := algebraMap K 𝔸[K]) ((h4.image Subtype.val).subset ?_)
    (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K).injOn
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨⟨_, k, rfl⟩, hk, rfl⟩

private theorem lf_ray (K : Type) [Field K] [NumberField K] (T : ℝ) :
    ∃ Z : Set 𝔸[K], IsCompact Z ∧ ∀ t, T ≤ t →
      ((zt K (-t) : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) 𝔸[K]).det ∈ Z := by
  set e : ℝ := (((2 : ℕ) : ℝ) * Module.finrank ℚ K)⁻¹ with he
  have he0 : 0 ≤ e := by positivity
  let B : Set (InfiniteAdeleRing K) :=
    Set.univ.pi fun w : InfinitePlace K => Metric.closedBall (0 : w.Completion) (Real.exp (-T) ^ e)
  have hB : IsCompact B := isCompact_univ_pi fun w => isCompact_closedBall _ _
  let Z0 : Set 𝔸[K] := B ×ˢ ({1} : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
  have hZ0 : IsCompact Z0 := hB.prod isCompact_singleton
  refine ⟨(fun x => x * x) '' Z0, hZ0.image (continuous_id.mul continuous_id), fun t ht => ?_⟩
  have hp : 0 < Real.exp (-t) ^ e := Real.rpow_pos_of_pos (Real.exp_pos _) e
  refine ⟨(posIdele (K := K) _ hp : GroundTheory.Global.IdeleGroup K), ⟨fun w _ => ?_, ?_⟩, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_posIdele_infinite]
    exact Real.rpow_le_rpow (Real.exp_pos _).le (Real.exp_le_exp.2 (by linarith)) he0
  · exact DFunLike.ext _ _ fun v => posIdele_finite _ hp v
  · rw [← AdelicGLn.coe_det]
    have : zt K (-t) = diagUnits 2 fun _ => posIdele (K := K) _ hp := rfl
    rw [this, det_diagUnits, Fin.prod_univ_two, Units.val_mul]

private theorem lf_minor {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R)
    (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (c : Fin 2 → Fin (2 + 2)) :
    ((unipMatrix X * (blk a b).val * h).submatrix (Fin.natAdd 2) c).det =
      b.val.det * (h.submatrix (Fin.natAdd 2) c).det := by
  rw [← Matrix.det_mul]
  congr 1
  ext i j
  have h1 : ∀ (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (k : Fin (2 + 2)),
      (unipMatrix X * M) (Fin.natAdd 2 i) k = M (Fin.natAdd 2 i) k := by
    intro M k
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro l _
    rw [blockEntry_apply, dite_eq_right, zero_mul]
    simp
  rw [Matrix.submatrix_apply, mul_assoc, h1, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.locFin :
    ∀ {K : Type} [Field K] [NumberField K] (C : Set (G1 K (2 + 2))) (T : ℝ), IsCompact C → {q : Cos K | ∃ g ∈ C, T ≤ HH ((q.out : G1 K (2 + 2)) * g)}.Finite := by
  intro K _ _ C T hC
  obtain ⟨D, hD, -, hxD⟩ := GroundTheory.Global.IdeleGroup.exists_isCompact_normOneSubgroup K
  obtain ⟨Z, hZ, hzZ⟩ := lf_ray K T
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 _).1
  let mn : (Fin 2 → Fin (2 + 2)) → G1 K (2 + 2) → 𝔸[K] := fun c g =>
    (((g : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det
  have hmn : ∀ c, Continuous (mn c) := fun c =>
    ((Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _).matrix_det
  let Φ : (Fin 2 → Fin (2 + 2)) → GroundTheory.Global.IdeleGroup K × 𝔸[K] × G1 K (2 + 2) × G1 K (2 + 2) → 𝔸[K] :=
    fun c p => (p.1 : 𝔸[K]) * p.2.1 * mn c (p.2.2.1 * p.2.2.2⁻¹)
  have hΦ : ∀ c, Continuous (Φ c) := fun c =>
    ((Units.continuous_val.comp continuous_fst).mul continuous_snd.fst).mul
      ((hmn c).comp (continuous_snd.snd.fst.mul continuous_snd.snd.snd.inv))
  have hfin : ∀ c, {k : K | algebraMap K 𝔸[K] k ∈ Φ c '' (D ×ˢ Z ×ˢ (KG K (2 + 2) : Set (G1 K (2 + 2))) ×ˢ C)}.Finite :=
    fun c => lf_fin ((hD.prod (hZ.prod (hK.prod hC))).image (hΦ c))
  have hrat : ∀ q : Cos K, ∃ γ : GL (Fin (2 + 2)) K, AdelicGLn.diagonal K (2 + 2) γ =
      ((q.out : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := fun q => q.out.2
  choose γ hγ using hrat
  have hm : ∀ q c, mn c (q.out : G1 K (2 + 2)) =
      algebraMap K 𝔸[K] ((γ q : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det := by
    intro q c
    simp only [mn]
    rw [← hγ, RingHom.map_det]
    rfl
  have key : ∀ q : Cos K, (∃ g ∈ C, T ≤ HH ((q.out : G1 K (2 + 2)) * g)) → ∃ a : Kˣ, ∀ c,
      algebraMap K 𝔸[K] (a * ((γ q : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det) ∈
        Φ c '' (D ×ˢ Z ×ˢ (KG K (2 + 2) : Set (G1 K (2 + 2))) ×ˢ C) := by
    rintro q ⟨g, hg, hT⟩
    obtain ⟨X, m₁, m₂, t, k, hk, hq⟩ := iwa ((q.out : G1 K (2 + 2)) * g)
    rw [hq, (hpSpec (K := K)).1, ((hpSpec (K := K)).2.1 k hk).1, add_zero] at hT
    have hm2 : AdelicGLn.det K 2 (m₂ : AdelicGLn.AdelicGL K 2) ∈ GroundTheory.Global.IdeleGroup.normOneSubgroup K :=
      mem_normOneGL_iff_detModule.1 m₂.2
    obtain ⟨a, ha⟩ := hxD _ hm2
    refine ⟨a, fun c => ⟨⟨_, ((zt K (-t) : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) 𝔸[K]).det, k, g⟩, ⟨ha, hzZ t hT, hk, hg⟩, ?_⟩⟩
    have hq' : (q.out : G1 K (2 + 2)) = nn X * lv m₁ m₂ t * (k * g⁻¹) := by
      rw [← mul_assoc, ← hq, mul_inv_cancel_right]
    rw [map_mul, ← hm, hq']
    simp only [Φ, mn]
    rw [Subgroup.coe_mul _ (nn X * _), Subgroup.coe_mul _ (nn X), (blkLaws (K := K)).1, Units.val_mul (_ * blk _ _),
      Units.val_mul _ (blk _ _), coe_unipOne, coe_unipGL, lf_minor, Units.val_mul, Units.val_mul (m₂ : AdelicGLn.AdelicGL K 2),
      Matrix.det_mul, GroundTheory.Global.IdeleGroup.coe_diagonal, AdelicGLn.coe_det]
    ring
  choose! a ha using key
  refine Set.Finite.of_finite_image
    (f := fun q c => (a q : K) * ((γ q : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det)
    ((Set.Finite.pi' hfin).subset ?_) ?_
  · rintro _ ⟨q, hq, rfl⟩ c
    exact ha q hq c
  · intro q _ q' _ h
    have h1 := (pluck (γ q') (γ q)).2 (((a q')⁻¹ * a q : Kˣ) : K) fun c => by
      have := congrFun h c
      simp only at this
      rw [Units.val_mul, mul_assoc, this, ← mul_assoc, Units.inv_mul, one_mul]
    rw [← q.out_eq, ← q'.out_eq]
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    rw [(pkLaws (K := K)).1]
    intro i j hi hj
    have h2 : (((q'.out * q.out⁻¹ : Gam K (2 + 2)) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
        AdelicGLn.diagonal K (2 + 2) (γ q' * (γ q)⁻¹) := by
      rw [map_mul, map_inv, hγ, hγ]; rfl
    rw [h2]
    have h3 := AdelicGLn.diagonal_apply K (2 + 2) (γ q' * (γ q)⁻¹) i j
    rw [h1 i j hi hj, map_zero] at h3
    exact h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LongCell
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem lc_inv_compact {K : Type} [Field K] [NumberField K] {B : Set 𝔸[K]} (hB : IsCompact B) {a : ℝ} (ha : 0 < a) :
    ∃ T : Set 𝔸[K], IsCompact T ∧ ∀ u : GroundTheory.Global.IdeleGroup K, (u : 𝔸[K]) ∈ B →
      a ≤ (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) → (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) ≤ 1 →
      ((u⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) ∈ T := by
  obtain ⟨S, hS, hc⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := K) ha 1
  have hci : Continuous fun s : GroundTheory.Global.IdeleGroup K => ((s⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) :=
    Units.continuous_coe_inv
  have hE : IsCompact ((fun p : 𝔸[K] × GroundTheory.Global.IdeleGroup K => p.1 * ((p.2⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K])) '' (B ×ˢ S)) :=
    (hB.prod hS).image (continuous_fst.mul (hci.comp continuous_snd))
  haveI := GroundTheory.Global.t2Space_adeleRing K
  haveI := GroundTheory.Global.discreteTopology_principalSubgroup K
  have hF := ((GroundTheory.Global.isClosed_principalSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hE).finite_of_discrete
  have hF2 := hF.image (fun x : AdeleRing.principalSubgroup (𝓞 K) K => Ring.inverse (x : 𝔸[K]))
  refine ⟨_, (hF2.isCompact.prod hS).image (f := fun p : 𝔸[K] × GroundTheory.Global.IdeleGroup K =>
    p.1 * ((p.2⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K])) (continuous_fst.mul (hci.comp continuous_snd)), fun u hu h1 h2 => ?_⟩
  obtain ⟨c, hcS⟩ := hc u h1 h2
  set d := GroundTheory.Global.IdeleGroup.diagonal K c with hd
  have hmem : ((d⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) ∈ AdeleRing.principalSubgroup (𝓞 K) K := by
    rw [hd, ← map_inv]
    exact ⟨((c⁻¹ : Kˣ) : K), rfl⟩
  refine ⟨((d : 𝔸[K]), d * u), ⟨⟨⟨_, hmem⟩, ⟨((u : 𝔸[K]), d * u), ⟨hu, hcS⟩, ?_⟩, ?_⟩, hcS⟩, ?_⟩
  · change (u : 𝔸[K]) * _ = _
    rw [← Units.val_mul, mul_inv_rev, mul_inv_cancel_left]
  · change Ring.inverse ((d⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) = _
    rw [Ring.inverse_unit, inv_inv]
  · change (d : 𝔸[K]) * _ = _
    rw [← Units.val_mul, mul_inv, mul_inv_cancel_left]

private theorem lc_rows {R : Type} [CommRing R] (X Y : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) (k : GL (Fin (2 + 2)) R)
    (h : wGL R * unipGL X = unipGL Y * blk a b * k) :
    b.val * k.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) = 1 ∧
      ∀ (i j : Fin 2) (hp), X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), hp⟩ =
        (b.val * k.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2)) i j := by
  have hL : ∀ (i : Fin 2) (j : Fin (2 + 2)), (wGL R * unipGL X).val (Fin.natAdd 2 i) j = unipMatrix X (Fin.castAdd 2 i) j := by
    intro i j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [wGL, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, coe_unipGL, Matrix.one_apply, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hU : ∀ (i : Fin 2) (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (j : Fin (2 + 2)),
      (unipMatrix Y * M) (Fin.natAdd 2 i) j = M (Fin.natAdd 2 i) j := by
    intro i M j
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro l _
    rw [blockEntry_apply, dite_eq_right (by simp), zero_mul]
  have hR : ∀ (i : Fin 2) (j : Fin (2 + 2)), (unipGL Y * blk a b * k).val (Fin.natAdd 2 i) j =
      ∑ l, b.val i l * k.val (Fin.natAdd 2 l) j := by
    intro i j
    rw [mul_assoc, Units.val_mul, coe_unipGL, hU, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add]
  have key : ∀ (i : Fin 2) (j : Fin (2 + 2)), ∑ l, b.val i l * k.val (Fin.natAdd 2 l) j = unipMatrix X (Fin.castAdd 2 i) j :=
    fun i j => by rw [← hL, h, hR]
  refine ⟨?_, fun i j hp => ?_⟩
  · ext i j
    rw [Matrix.mul_apply]
    refine (key i (Fin.castAdd 2 j)).trans ?_
    rw [unipMatrix, Matrix.add_apply, blockEntry_apply, dite_eq_right (fun hh => absurd hh.2 (not_le.2 j.2)), add_zero]
    simp [Matrix.one_apply, Fin.ext_iff]
  · rw [Matrix.mul_apply]
    refine Eq.trans ?_ (key i (Fin.natAdd 2 j)).symm
    rw [unipMatrix, Matrix.add_apply, blockEntry_apply, dite_eq_left hp, Matrix.one_apply_ne, zero_add]
    intro e
    have := congrArg Fin.val e
    simp at this
    omega

private theorem lc_adj {R : Type} [CommRing R] (b c : Matrix (Fin 2) (Fin 2) R) (h : b * c = 1) :
    b = b.det • c.adjugate := by
  have h1 : c.adjugate = c.det • b := by
    have := congrArg (· * c.adjugate) h
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul] at this
    exact this.symm
  rw [h1, smul_smul, ← Matrix.det_mul, h, Matrix.det_one, one_smul]

private theorem lc_main {K : Type} [Field K] [NumberField K] (X : UPos (2 + 2) 2 → 𝔸[K]) (k : G1 K (2 + 2)) (hk : k ∈ KG K (2 + 2)) :
    ∃ (b : AdelicGLn.AdelicGL K 2), ∃ k' ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))),
      (detModule K 2 b⁻¹).1 = Real.exp (HH (w0 K * unipOne (K := K) (n := 2 + 2) 2 X * k)) ∧
      (detModule K 2 b⁻¹).1 ≤ 1 ∧
      b.val * k'.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) = 1 ∧
      ∀ (i j : Fin 2) (hp), X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), hp⟩ =
        (b.val * k'.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2)) i j := by
  obtain ⟨Y, m₁, m₂, t, k', hk', e⟩ := iwa (w0 K * unipOne (K := K) (n := 2 + 2) 2 X)
  obtain ⟨h1, h2, -⟩ := hpSpec (K := K)
  obtain ⟨b1, -, -, -, -, -, b2, -⟩ := blkLaws (K := K)
  have hH : HH (w0 K * unipOne (K := K) (n := 2 + 2) 2 X * k) = t := by
    rw [(h2 k hk).2, e, h1, (h2 k' hk').1, add_zero]
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, b1, b2, coe_unipOne] at e'
  obtain ⟨r1, r2⟩ := lc_rows X Y _ _ _ e'
  refine ⟨(m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t), k', hk', ?_, ?_, r1, r2⟩
  · rw [hH, map_inv, map_mul, mem_normOneGL_iff_detModule.1 m₂.2, one_mul, zt, detModule_centralSection two_pos]
    change (Real.exp (-t))⁻¹ = _
    rw [Real.exp_neg, inv_inv]
  · have hs := subDet (2 + 2) (k' : AdelicGLn.AdelicGL K (2 + 2)) hk' (Fin.natAdd 2) (Fin.castAdd 2)
      (Fin.natAdd_injective 2 2) (Fin.castAdd_injective 2 2)
    exact hs.2.2 _ (Units.inv_eq_of_mul_eq_one_right r1)

private noncomputable def lcF {K : Type} [Field K] [NumberField K] (q : 𝔸[K] × AdelicGLn.AdelicGL K (2 + 2)) (p : UPos (2 + 2) 2) : 𝔸[K] :=
  q.1 * ((q.2.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2)).adjugate * q.2.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2))
    ⟨(p.1.1 : ℕ), p.2.1⟩ ⟨(p.1.2 : ℕ) - 2, by have := p.1.2.2; omega⟩

private theorem continuous_lower_left_block {K : Type} [Field K] [NumberField K] :
    Continuous fun k : AdelicGLn.AdelicGL K (2 + 2) => k.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) :=
  Units.continuous_val.matrix_submatrix _ _

private theorem continuous_lower_right_block {K : Type} [Field K] [NumberField K] :
    Continuous fun k : AdelicGLn.AdelicGL K (2 + 2) => k.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2) :=
  Units.continuous_val.matrix_submatrix _ _

private theorem lc_cont {K : Type} [Field K] [NumberField K] : Continuous (lcF (K := K)) := by
  refine continuous_pi fun p => ?_
  unfold lcF
  exact continuous_fst.mul (((continuous_lower_left_block.matrix_adjugate.matrix_mul continuous_lower_right_block).matrix_elem _ _).comp continuous_snd)

private theorem lc_eq {K : Type} [Field K] [NumberField K] (X : UPos (2 + 2) 2 → 𝔸[K]) (b : Matrix (Fin 2) (Fin 2) 𝔸[K])
    (k' : AdelicGLn.AdelicGL K (2 + 2)) (h3 : b * k'.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) = 1)
    (h4 : ∀ (i j : Fin 2) (hp), X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), hp⟩ =
        (b * k'.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2)) i j) : X = lcF (b.det, k') := by
  funext p
  obtain ⟨⟨i, j⟩, hi, hj⟩ := p
  have hj2 := j.2
  have hi' : (i : ℕ) < 2 := hi
  have hj' : 2 ≤ (j : ℕ) := hj
  obtain ⟨i, rfl⟩ : ∃ i' : Fin 2, i = Fin.castAdd 2 i' := ⟨⟨i, hi'⟩, Fin.ext rfl⟩
  obtain ⟨j, rfl⟩ : ∃ j' : Fin 2, j = Fin.natAdd 2 j' := ⟨⟨(j : ℕ) - 2, by omega⟩, Fin.ext (by simp; omega)⟩
  have hb := lc_adj _ _ h3
  rw [h4 i j]
  conv_lhs => rw [hb]
  rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  simp [lcF]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.longCell :
    ∀ {K : Type} [Field K] [NumberField K],
      (∀ (X : UPos (2 + 2) 2 → 𝔸[K]), ∀ k ∈ KG K (2 + 2),
        HH (w0 K * unipOne (K := K) (n := 2 + 2) 2 X * k) ≤ 0) ∧
      ∀ R : ℝ, ∃ C : Set (UPos (2 + 2) 2 → 𝔸[K]), IsCompact C ∧ ∀ X, ∀ k ∈ KG K (2 + 2),
        -R ≤ HH (w0 K * unipOne (K := K) (n := 2 + 2) 2 X * k) → X ∈ C := by
  intro K _ _
  refine ⟨fun X k hk => ?_, fun R => ?_⟩
  · obtain ⟨b, k', -, h1, h2, -⟩ := lc_main X k hk
    rw [h1] at h2
    exact Real.exp_le_one_iff.1 h2
  have hB : IsCompact ((fun k : AdelicGLn.AdelicGL K (2 + 2) => (k.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2)).det) ''
      (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2)))) :=
    (isCompact_maxCompact (K := K) (n := 2 + 2)).image continuous_lower_left_block.matrix_det
  obtain ⟨T, hT, hu⟩ := lc_inv_compact hB (Real.exp_pos (-R))
  refine ⟨lcF '' (T ×ˢ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2)))),
    (hT.prod (isCompact_maxCompact (K := K) (n := 2 + 2))).image lc_cont, fun X k hk hR => ?_⟩
  obtain ⟨b, k', hk', h1, h2, h3, h4⟩ := lc_main X k hk
  have hinv : ((b⁻¹ : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) 𝔸[K]) = k'.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) :=
    Units.inv_eq_of_mul_eq_one_right h3
  have hmem : ((AdelicGLn.det K 2 b : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) ∈ T := by
    have h5 := hu (AdelicGLn.det K 2 b⁻¹) ⟨k', hk', by rw [AdelicGLn.coe_det, hinv]⟩
      ((Real.exp_le_exp.2 hR).trans h1.ge) h2
    rwa [← map_inv, inv_inv] at h5
  rw [AdelicGLn.coe_det] at hmem
  exact ⟨(_, k'), ⟨hmem, hk'⟩, (lc_eq X b.val k' h3 h4).symm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpqMinor
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem hpq_loc {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E) (i j p q : Fin n) :
    ‖(g : Matrix (Fin n) (Fin n) E) i j * (g : Matrix (Fin n) (Fin n) E) p q‖ ≤ locHeight g ^ 2 := by
  rw [norm_mul, sq]
  exact mul_le_mul (norm_apply_le_locHeight g i j) (norm_apply_le_locHeight g p q) (norm_nonneg _) (locHeight_pos g).le

private theorem hpq_minor {K : Type} [Field K] [NumberField K] {n : ℕ} (h : AdelicGLn.AdelicGL K n) (r c : Fin 2 → Fin n)
    (y : GroundTheory.Global.IdeleGroup K) (hy : (y : 𝔸[K]) = ((h : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det) :
    (GroundTheory.Global.IdeleGroup.ideleModule K y : ℝ) ≤ (∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult) * AutomorphicForm.height h ^ 2 := by
  classical
  rw [Matrix.det_fin_two] at hy
  simp only [Matrix.submatrix_apply] at hy
  have hi : ∀ w : InfinitePlace K, ‖(y : 𝔸[K]).1 w‖ ≤ 2 * locHeight (infAt w h) ^ 2 := by
    intro w
    have e : (y : 𝔸[K]).1 w = (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 0) (c 0) * (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 1) (c 1) -
        (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 0) (c 1) * (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 1) (c 0) := by
      rw [hy]; rfl
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hpq_loc (infAt w h) (r 0) (c 0) (r 1) (c 1)
    have h2 := hpq_loc (infAt w h) (r 0) (c 1) (r 1) (c 0)
    linarith
  have hf : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(y : 𝔸[K]).2 v‖ ≤ locHeight (finAt v h) ^ 2 := by
    intro v
    have e : (y : 𝔸[K]).2 v = (finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 0) (c 0) * (finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 1) (c 1) +
        -((finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 0) (c 1) * (finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 1) (c 0)) := by
      rw [hy, sub_eq_add_neg]; rfl
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hpq_loc _ _ _ _ _) ?_)
    rw [norm_neg]
    exact hpq_loc _ _ _ _ _
  set s := (finite_mulSupport_locHeight_finAt h).union (GroundTheory.Global.IdeleGroup.finite_mulSupport_norm y)
  have h1 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), locHeight (finAt v h) = ∏ v ∈ s.toFinset, locHeight (finAt v h) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_union]; exact Or.inl hv
  have h2 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(y : 𝔸[K]).2 v‖ = ∏ v ∈ s.toFinset, ‖(y : 𝔸[K]).2 v‖ :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_union]; exact Or.inr hv
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, AutomorphicForm.height, h1, h2, mul_pow, ← mul_assoc, ← Finset.prod_pow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun w _ => by positivity) fun w _ => ?_)
    (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hf v) (Finset.prod_nonneg fun v _ => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => by positivity)
  rw [← pow_mul, mul_comm w.mult 2, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hi w) _

private theorem hpq_rows {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R)
    (c : Fin 2 → Fin (2 + 2)) :
    (((unipGL X * blk a b : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) * k).submatrix (Fin.natAdd 2) c =
      (b : Matrix (Fin 2) (Fin 2) R) * k.submatrix (Fin.natAdd 2) c := by
  have h1 : ∀ (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (i : Fin 2) j, (unipMatrix X * M) (Fin.natAdd 2 i) j = M (Fin.natAdd 2 i) j := by
    intro M i j
    have : (blockEntry X * M) (Fin.natAdd 2 i) j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [blockEntry_apply, dite_eq_right (by simp), zero_mul]
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, this, add_zero]
  ext i j
  rw [Matrix.submatrix_apply, Units.val_mul, coe_unipGL, mul_assoc, h1, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.hpQht :
    ∀ {K : Type} [Field K] [NumberField K], ∃ c C : ℝ, 0 < c ∧ ∀ g : G1 K (2 + 2), HH g ≤ c * Real.log (qht g) + C := by
  intro K _ _
  set D : ℝ := (∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult) * heightConst K (2 + 2) ^ 2 with hD
  have hc1 := one_le_heightConst (K := K) (n := 2 + 2)
  have hD0 : 0 < D := mul_pos (Finset.prod_pos fun w _ => by positivity) (by positivity)
  refine ⟨2, Real.log D, two_pos, fun g => ?_⟩
  obtain ⟨X, m₁, m₂, t, k, hk, hg⟩ := iwa g
  have ht : HH g = t := by
    rw [hg, (hpSpec (K := K)).1, ((hpSpec (K := K)).2.1 k hk).1, add_zero]
  have key : ∀ γ : Gam K (2 + 2), Real.exp t ≤
      D * AutomorphicForm.height (((γ : G1 K (2 + 2)) * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ 2 := by
    intro γ
    obtain ⟨δ, hδ⟩ : ∃ δ : GL (Fin (2 + 2)) K, AdelicGLn.diagonal K (2 + 2) δ = ((γ⁻¹ : Gam K (2 + 2)) : G1 K (2 + 2)) := (γ⁻¹).2
    set h : AdelicGLn.AdelicGL K (2 + 2) := (((γ : G1 K (2 + 2)) * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) with hh
    set b : AdelicGLn.AdelicGL K 2 := (m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t) with hb
    have hb' : (detModule K 2 b : ℝ) = Real.exp (-t) := by
      rw [hb, map_mul, mem_normOneGL_iff_detModule.1 m₂.2, one_mul, zt, detModule_centralSection two_pos]
    have e1 : AdelicGLn.diagonal K (2 + 2) δ =
        unipGL X * blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) b * ((k : AdelicGLn.AdelicGL K (2 + 2)) * h⁻¹) := by
      rw [← mul_assoc, hb, ← (blkLaws (K := K)).1, ← coe_unipOne, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← hg, hδ, hh]
      simp
    obtain ⟨c, -, hc⟩ := (pluck δ δ).1
    have e2 : algebraMap K 𝔸[K] ((δ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det =
        (b : Matrix (Fin 2) (Fin 2) 𝔸[K]).det * ((((k : AdelicGLn.AdelicGL K (2 + 2)) * h⁻¹ : AdelicGLn.AdelicGL K (2 + 2)) :
          Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det := by
      rw [← Matrix.det_mul, ← hpq_rows X ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) b, ← Units.val_mul, ← e1, RingHom.map_det]
      rfl
    have h3 := hpq_minor ((k : AdelicGLn.AdelicGL K (2 + 2)) * h⁻¹) (Fin.natAdd 2) c
      ((AdelicGLn.det K 2 b)⁻¹ * GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 _ hc)) (by
        rw [Units.val_mul, GroundTheory.Global.IdeleGroup.coe_diagonal, Units.val_mk0, e2, ← AdelicGLn.coe_det, Units.inv_mul_cancel_left])
    rw [map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, mul_one, map_inv, Positive.coe_inv] at h3
    change (detModule K 2 b : ℝ)⁻¹ ≤ _ at h3
    rw [hb', Real.exp_neg, inv_inv] at h3
    have h4 := height_mul_le (k : AdelicGLn.AdelicGL K (2 + 2)) h⁻¹
    rw [height_eq_one_of_mem_maxCompact (k := (k : AdelicGLn.AdelicGL K (2 + 2))) hk, mul_one, height_inv] at h4
    refine h3.trans ?_
    rw [hD, mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le h4 _) (Finset.prod_nonneg fun w _ => by positivity)
  have hs : 0 < Real.sqrt (Real.exp t / D) := Real.sqrt_pos.2 (div_pos (Real.exp_pos t) hD0)
  have hq : Real.sqrt (Real.exp t / D) ≤ qht g := by
    refine le_ciInf fun γ => ?_
    rw [Real.sqrt_le_left (height_pos _).le, div_le_iff₀ hD0, mul_comm]
    exact key γ
  have h5 := Real.log_le_log hs hq
  rw [Real.log_sqrt (div_pos (Real.exp_pos t) hD0).le, Real.log_div (Real.exp_pos t).ne' hD0.ne', Real.log_exp] at h5
  rw [ht]
  linarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PmLaws
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem finFd {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] :
    IsFiniteMeasure (fd μ) := by
  have h := (isFiniteMeasure_quotientMeasure (K := K) (n := n) μ).measure_univ_lt_top
  rw [quotientMeasure_univ μ (isFundamentalDomain_fundamentalDomain _ μ)] at h
  exact ⟨by rwa [Measure.restrict_apply_univ]⟩

private theorem intg {Z E : Type} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [NormedAddCommGroup E] [SecondCountableTopology E]
    (ν : Measure Z) [IsFiniteMeasure ν] {h : Z → E} (hc : Continuous h) {C : ℝ} (hb : ∀ z, ‖h z‖ ≤ C) :
    Integrable h ν :=
  Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hb)

private theorem contInt {Y Z E : Type} [TopologicalSpace Y] [FirstCountableTopology Y] [TopologicalSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    (ν : Measure Z) [IsFiniteMeasure ν] {h : Y × Z → E} (hc : Continuous h) {C : ℝ} (hb : ∀ z, ‖h z‖ ≤ C) :
    Continuous (fun y => ∫ z, h (y, z) ∂ν) ∧ ∀ y, ‖∫ z, h (y, z) ∂ν‖ ≤ C * ν.real univ := by
  refine ⟨continuous_of_dominated (bound := fun _ => C) (fun y => ?_) (fun y => ae_of_all _ fun z => hb _)
    (integrable_const C) (ae_of_all _ fun z => hc.comp (by fun_prop)), fun y => ?_⟩
  · exact (hc.comp (Continuous.prodMk_right y)).aestronglyMeasurable
  · exact norm_integral_le_of_norm_le_const (ae_of_all _ fun z => hb _)

private theorem orth {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} {v w : L2 μ}
    {φ ψ : G1 K n → ℂ} (hv : Reps μ v φ) (hw : Reps μ w ψ) :
    ∫ m, conj (φ m) * ψ m ∂fd μ = ⟪v, w⟫_ℂ := by
  rw [L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hv, ae_restrict_of_ae hw] with y h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

private theorem posFd {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {φ : G1 K n → ℝ} (hc : Continuous φ) {C : ℝ} (hb : ∀ z, ‖φ z‖ ≤ C) (h0 : ∀ z, 0 ≤ φ z)
    (hΓ : ∀ (γ : Gam K n) z, φ (γ * z) = φ z) {z₀ : G1 K n} (hz : φ z₀ ≠ 0) : 0 < ∫ z, φ z ∂fd μ := by
  haveI := finFd μ
  rw [integral_pos_iff_support_of_nonneg h0 (intg _ hc hb), pos_iff_ne_zero]
  intro h
  rw [Measure.restrict_apply hc.isOpen_support.measurableSet] at h
  set_option synthInstance.maxHeartbeats 200000 in
  have := (isFundamentalDomain_fundamentalDomain (Gam K n) μ).measure_zero_of_invariant _ (by
    intro γ
    ext z
    rw [mem_smul_set_iff_inv_smul_mem]
    show φ ((γ⁻¹ : Gam K n) * z) ≠ 0 ↔ φ z ≠ 0
    rw [hΓ]) h
  exact (hc.isOpen_support.measure_pos μ ⟨z₀, hz⟩).ne' this

private theorem bdd2 {K : Type} [Field K] [NumberField K] {f f' : G1 K (2 + 2) → ℂ} (hf : SFun f) (hf' : SFun f') :
    ∃ C : ℝ, ∀ x y, ‖conj (f x) * f' y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨C', hC'⟩ := hf'.bdd
  refine ⟨C * C', fun x y => ?_⟩
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (hC x) (hC' y) (norm_nonneg _) ((norm_nonneg _).trans (hC x))

private theorem core0 {M G : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [TopologicalSpace G] [FirstCountableTopology G] [Mul G] [ContinuousMul G] (ν : Measure M) [IsFiniteMeasure ν]
    {f f' : G → ℂ} (h1 : Continuous f) (h2 : Continuous f') {C : ℝ} (hC : ∀ x y, ‖conj (f x) * f' y‖ ≤ C)
    {a b : M × M → G} (ha : Continuous a) (hb : Continuous b) :
    (∀ x y, Integrable (fun m => conj (f (a m * x)) * f' (b m * y)) (ν.prod ν)) ∧
    Continuous (fun p : G × G => ∫ m₁, ∫ m₂, conj (f (a (m₁, m₂) * p.1)) * f' (b (m₁, m₂) * p.2) ∂ν ∂ν) ∧
    ∃ C : ℝ, ∀ x y, ‖∫ m₁, ∫ m₂, conj (f (a (m₁, m₂) * x)) * f' (b (m₁, m₂) * y) ∂ν ∂ν‖ ≤ C := by
  have hi : ∀ x y, Integrable (fun m => conj (f (a m * x)) * f' (b m * y)) (ν.prod ν) :=
    fun x y => intg _ (by fun_prop) fun _ => hC _ _
  have := contInt (ν.prod ν) (h := fun q : (G × G) × M × M =>
    conj (f (a q.2 * q.1.1)) * f' (b q.2 * q.1.2)) (by fun_prop) fun _ => hC _ _
  simp only [integral_prod _ (hi _ _)] at this
  exact ⟨hi, this.1, _, fun x y => this.2 (x, y)⟩

private theorem core {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    {f f' : G1 K (2 + 2) → ℂ} (hf : SFun f) (hf' : SFun f') {a b : G1 K 2 × G1 K 2 → G1 K (2 + 2)}
    (ha : Continuous a) (hb : Continuous b) :
    (∀ x y, Integrable (fun m => conj (f (a m * x)) * f' (b m * y)) ((fd μ₂).prod (fd μ₂))) ∧
    Continuous (fun p : G1 K (2 + 2) × G1 K (2 + 2) =>
      ∫ m₁, ∫ m₂, conj (f (a (m₁, m₂) * p.1)) * f' (b (m₁, m₂) * p.2) ∂fd μ₂ ∂fd μ₂) ∧
    ∃ C : ℝ, ∀ x y, ‖∫ m₁, ∫ m₂, conj (f (a (m₁, m₂) * x)) * f' (b (m₁, m₂) * y) ∂fd μ₂ ∂fd μ₂‖ ≤ C := by
  haveI := finFd μ₂
  obtain ⟨C, hC⟩ := bdd2 hf hf'
  set_option synthInstance.maxHeartbeats 200000 in
  exact core0 (fd μ₂) hf.cont hf'.cont hC ha hb

private theorem lin0 {M : Type} [MeasurableSpace M] (ν : Measure M) [IsFiniteMeasure ν] (a : ℂ) {u v w : M × M → ℂ}
    (i1 : Integrable (fun m => u m * v m) (ν.prod ν)) (i2 : Integrable (fun m => u m * w m) (ν.prod ν)) :
    ∫ x, ∫ y, u (x, y) * (a * v (x, y) + w (x, y)) ∂ν ∂ν =
      a * ∫ x, ∫ y, u (x, y) * v (x, y) ∂ν ∂ν + ∫ x, ∫ y, u (x, y) * w (x, y) ∂ν ∂ν := by
  have e3 := integral_prod _ ((i1.const_mul a).add i2)
  have e4 := integral_add (i1.const_mul a) i2
  rw [integral_const_mul, integral_prod _ i1, integral_prod _ i2] at e4
  refine Eq.trans ?_ (e3.symm.trans e4)
  simp only [Pi.add_apply, mul_add, mul_left_comm]

private theorem zero0 {M : Type} [MeasurableSpace M] (ν : Measure M) [IsFiniteMeasure ν] {u : M × M → ℂ}
    (i1 : Integrable u (ν.prod ν)) (h : ∀ y, ∫ x, u (x, y) ∂ν = 0) : ∫ x, ∫ y, u (x, y) ∂ν ∂ν = 0 := by
  rw [← integral_prod _ i1, integral_prod_symm _ i1]
  simp only [h, integral_zero]

private theorem contLv {K : Type} [Field K] [NumberField K] : Continuous fun m : G1 K 2 × G1 K 2 => lv m.1 m.2 0 :=
  (blkLaws (K := K)).2.2.2.1.comp (f := fun m : G1 K 2 × G1 K 2 => (m.1, m.2, (0 : ℝ)))
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))

private theorem pos2 {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {F : G1 K n × G1 K n → ℂ} (hc : Continuous F) {C : ℝ} (hC : ∀ z, ‖F z‖ ≤ C)
    (hΓ : ∀ (γ₁ γ₂ : Gam K n) (a b : G1 K n), F ((γ₁ : G1 K n) * a, (γ₂ : G1 K n) * b) = F (a, b))
    {m₁ m₂ : G1 K n} (hz : F (m₁, m₂) ≠ 0) : 0 < ∫ a, ∫ b, ‖F (a, b)‖ ^ 2 ∂fd μ ∂fd μ := by
  haveI := finFd μ
  have hc2 : Continuous fun m => ‖F m‖ ^ 2 := hc.norm.pow 2
  have hb2 : ∀ m, ‖‖F m‖ ^ 2‖ ≤ C ^ 2 := fun m => by
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
  set_option synthInstance.maxHeartbeats 200000 in
  have hin := contInt (fd μ) hc2 hb2
  refine posFd μ hin.1 hin.2 (fun z => integral_nonneg fun _ => sq_nonneg _) (fun γ z => ?_) (z₀ := m₁) (ne_of_gt ?_)
  · refine integral_congr_ae (ae_of_all _ fun b => ?_)
    have := hΓ γ 1 z b
    rw [OneMemClass.coe_one, one_mul] at this
    exact congrArg (fun c : ℂ => ‖c‖ ^ 2) this
  · refine posFd μ (φ := fun b => ‖F (m₁, b)‖ ^ 2) (hc2.comp (Continuous.prodMk_right m₁)) (fun b => hb2 (m₁, b))
      (fun _ => sq_nonneg _) (fun γ b => ?_) (z₀ := m₂) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
    have := hΓ 1 γ m₁ b
    rw [OneMemClass.coe_one, one_mul] at this
    exact congrArg (fun c : ℂ => ‖c‖ ^ 2) this

private theorem posPt {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    {f : G1 K (2 + 2) → ℂ} (hf : SFun f) (hne : f ≠ 0) :
    ∃ k ∈ KG K (2 + 2), 0 < ∫ m₁, ∫ m₂, ‖f (lv m₁ m₂ 0 * k)‖ ^ 2 ∂fd μ₂ ∂fd μ₂ := by
  haveI := finFd μ₂
  have hmul := (blkLaws (K := K)).2.1
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
  obtain ⟨X, m₁, m₂, t, k, hkK, rfl⟩ := iwa g
  refine ⟨k, hkK, ?_⟩
  have hg' : f (lv m₁ m₂ 0 * k) ≠ 0 := by
    rw [← hf.ray t, ← mul_assoc, hmul, one_mul, one_mul, add_zero, ← hf.unip X, ← mul_assoc]
    exact hg
  have hΓ : ∀ (γ₁ γ₂ : Gam K 2) (a b : G1 K 2),
      f (lv ((γ₁ : G1 K 2) * a) ((γ₂ : G1 K 2) * b) 0 * k) = f (lv a b 0 * k) := fun γ₁ γ₂ a b => by
    have hm : nn (0 : unipLattice K (2 + 2) 2).1 * lv (γ₁ : G1 K 2) γ₂ 0 ∈ PK K :=
      ((pkLaws (K := K)).2.1 _).mpr ⟨0, γ₁, γ₂, rfl⟩
    rw [← hf.rat _ hm (lv a b 0 * k), mul_assoc, hf.unip, ← mul_assoc, hmul, add_zero]
  obtain ⟨C, hC⟩ := hf.bdd
  exact pos2 μ₂ (F := fun m : G1 K 2 × G1 K 2 => f (lv m.1 m.2 0 * k)) (hf.cont.comp (contLv.mul continuous_const))
    (fun _ => hC _) hΓ hg'

private theorem contK {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    {f f' : G1 K (2 + 2) → ℂ} (hf : SFun f) (hf' : SFun f') : Continuous fun k : KG K (2 + 2) => pm μ₂ f f' k k :=
  (core μ₂ hf hf' contLv contLv).2.1.comp
    (f := fun k : KG K (2 + 2) => ((k : G1 K (2 + 2)), (k : G1 K (2 + 2))))
    (continuous_subtype_val.prodMk continuous_subtype_val)

private theorem cptK {K : Type} [Field K] [NumberField K] : CompactSpace (KG K (2 + 2)) :=
  isCompact_iff_compactSpace.mp ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 _).1

private theorem intK {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure]
    {f f' : G1 K (2 + 2) → ℂ} (hf : SFun f) (hf' : SFun f') : Integrable (fun k : KG K (2 + 2) => pm μ₂ f f' k k) κ :=
  haveI := cptK (K := K)
  (contK μ₂ hf hf').integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem posK {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure]
    {f : G1 K (2 + 2) → ℂ} (hf : SFun f) (hne : f ≠ 0) : 0 < (∫ k : KG K (2 + 2), pm μ₂ f f k k ∂κ).re := by
  haveI := cptK (K := K)
  obtain ⟨k, hkK, hpos⟩ := posPt μ₂ hf hne
  have hre : ∀ x, (pm μ₂ f f x x).re = ∫ m₁, ∫ m₂, ‖f (lv m₁ m₂ 0 * x)‖ ^ 2 ∂fd μ₂ ∂fd μ₂ := fun x => by
    rw [← Complex.ofReal_re (∫ m₁, ∫ m₂, ‖f (lv m₁ m₂ 0 * x)‖ ^ 2 ∂fd μ₂ ∂fd μ₂)]
    simp only [pm, ← integral_complex_ofReal, Complex.conj_mul', Complex.ofReal_pow]
  rw [← RCLike.re_to_complex, ← integral_re (intK μ₂ κ hf hf)]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (f := fun k : KG K (2 + 2) => (pm μ₂ f f k k).re)
    (Complex.continuous_re.comp (contK μ₂ hf hf))
    (HasCompactSupport.of_compactSpace _) (fun x => ?_) (x := ⟨k, hkK⟩) (ne_of_gt ?_)
  · exact (integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _).trans_eq (hre x).symm
  · exact hpos.trans_eq (hre k).symm

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pmLaws :
    ∀ {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure], (∀ (τ₁ τ₂ ρ₁ ρ₂ : Submodule ℂ (L2 μ₂)) (f f' : G1 K (2 + 2) → ℂ), SFun f → SFun f' → Slices τ₁ τ₂ f → Slices ρ₁ ρ₂ f' → ∀ x y,
        (τ₁ ⟂ ρ₁ → pm μ₂ f f' x y = 0) ∧ (τ₁ ⟂ ρ₂ → pw μ₂ f f' x y = 0)) ∧
      (∀ f f' f'' : G1 K (2 + 2) → ℂ, SFun f → SFun f' → SFun f'' → ∀ a : ℂ,
        ∫ k : KG K (2 + 2), pm μ₂ f (a • f' + f'') k k ∂κ = a * ∫ k : KG K (2 + 2), pm μ₂ f f' k k ∂κ + ∫ k : KG K (2 + 2), pm μ₂ f f'' k k ∂κ ∧
        conj (∫ k : KG K (2 + 2), pm μ₂ f f' k k ∂κ) = ∫ k : KG K (2 + 2), pm μ₂ f' f k k ∂κ) ∧
      (∀ f : G1 K (2 + 2) → ℂ, SFun f → f ≠ 0 → 0 < (∫ k : KG K (2 + 2), pm μ₂ f f k k ∂κ).re) ∧
      ∀ f f' : G1 K (2 + 2) → ℂ, SFun f → SFun f' → Continuous (fun p : G1 K (2 + 2) × G1 K (2 + 2) => pw μ₂ f f' p.1 p.2) ∧ ∃ C : ℝ, ∀ x y, ‖pw μ₂ f f' x y‖ ≤ C := by
  intro K _ _ μ₂ _ κ _
  haveI := finFd μ₂
  have ha := contLv (K := K)
  have hb : Continuous fun m : G1 K 2 × G1 K 2 => lv m.2 m.1 0 :=
    (blkLaws (K := K)).2.2.2.1.comp (f := fun m : G1 K 2 × G1 K 2 => (m.2, m.1, (0 : ℝ)))
      (continuous_snd.prodMk (continuous_fst.prodMk continuous_const))
  refine ⟨fun τ₁ τ₂ ρ₁ ρ₂ f f' hf hf' hs hs' x y => ⟨fun ho => ?_, fun ho => ?_⟩,
    fun f f' f'' hf hf' hf'' a => ⟨?_, ?_⟩, fun f hf hne => posK μ₂ κ hf hne, fun f f' hf hf' => (core μ₂ hf hf' ha hb).2⟩
  · refine zero0 (fd μ₂) ((core μ₂ hf hf' ha ha).1 x y) fun m₂ => ?_
    obtain ⟨v, hv, hr⟩ := (hs x).1 m₂
    obtain ⟨w, hw, hr'⟩ := (hs' y).1 m₂
    exact (orth hr hr').trans (ho.inner_eq hv hw)
  · refine zero0 (fd μ₂) ((core μ₂ hf hf' ha hb).1 x y) fun m₂ => ?_
    obtain ⟨v, hv, hr⟩ := (hs x).1 m₂
    obtain ⟨w, hw, hr'⟩ := (hs' y).2 m₂
    exact (orth hr hr').trans (ho.inner_eq hv hw)
  · rw [← integral_const_mul, ← integral_add ((intK μ₂ κ hf hf').const_mul a) (intK μ₂ κ hf hf'')]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    exact lin0 (fd μ₂) a ((core μ₂ hf hf' ha ha).1 k k) ((core μ₂ hf hf'' ha ha).1 k k)
  · rw [← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only [pm, ← integral_conj, map_mul, RCLike.conj_conj, mul_comm]
end
