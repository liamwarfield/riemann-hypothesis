module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.FnProj0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OrbLift
public import GroundTheory.AutomorphicForms.AdelicDixmierMalliavinProduct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevMulChi
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CptGard
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OrbConv
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem norm_tsum_le_of_encard {I : Type} (u : I → ℂ) (S : Set I) (N : ℕ) (hS : S.encard ≤ N) (M : ℝ)
    (hM : ∀ i, ‖u i‖ ≤ M) (hM0 : 0 ≤ M) (h0 : ∀ i ∉ S, u i = 0) : ‖∑' i, u i‖ ≤ N * M := by
  have hfin : S.Finite := Set.finite_of_encard_le_coe hS
  rw [tsum_eq_sum (s := hfin.toFinset) fun i hi => h0 i (by simpa using hi)]
  have hcard : hfin.toFinset.card ≤ N := by
    rw [hfin.encard_eq_coe_toFinset_card] at hS
    exact_mod_cast hS
  refine (norm_sum_le_of_le _ fun i _ => hM i).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM0

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.orbConv :
    UpperTheory.V.Cj.H.OrbConv := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f f' hf hc hf' hc'
  have hi : Integrable f μ := hf.integrable_of_hasCompactSupport hc
  have hq := GlobalTheory.AutomorphicL2KernelIntegral.integrable_descend_orbitSum (Γ := Γ) hi
  obtain ⟨N, hN⟩ := (locInt G Γ μ).2 (tsupport f) hc
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hb : ∀ g, ‖GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f g‖ ≤ N * M := fun g =>
    norm_tsum_le_of_encard _ _ N (hN g) M (fun _ => hM _) hM0 fun γ h => image_eq_zero_of_notMem_tsupport h
  have h : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ (GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f) := by
    refine ⟨GlobalTheory.AutomorphicL2Unitary.leftInv_orbitSum f, (memLp_two_iff_integrable_sq_norm hq.1).2 ?_⟩
    refine (hq.norm.const_mul (N * M)).mono' (hq.1.norm.pow 2) (Eventually.of_forall fun q => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
  refine ⟨h, funext fun x => ?_⟩
  have hae : ∀ᵐ g ∂μ, GlobalTheory.AutomorphicL2Unitary.lift Γ h.toL2 g = GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f g := by
    filter_upwards [GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.1 h.coeFn_toL2] with g hg
    exact hg.trans (h.1.descend_mk g)
  have hk : Continuous fun y : G => f' (y⁻¹ * x) := by fun_prop
  have hkc : HasCompactSupport fun y : G => f' (y⁻¹ * x) :=
    hc'.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
  have hint : ∀ γ : Γ, Integrable (fun y => f (γ * y) * f' (y⁻¹ * x)) μ := fun γ =>
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hkc.mul_left
  have hfin : {γ : Γ | (γ : G) ∈ tsupport f * (tsupport fun y : G => f' (y⁻¹ * x))⁻¹}.Finite :=
    GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (IsCompact.mul hc (IsCompact.inv hkc))
  have hsum : Summable fun γ : Γ => ∫ y, ‖f (γ * y) * f' (y⁻¹ * x)‖ ∂μ := by
    refine summable_of_hasFiniteSupport (hfin.subset fun γ hγ => ?_)
    by_contra hn
    refine hγ ?_
    have : ∀ y, f (γ * y) * f' (y⁻¹ * x) = 0 := fun y => by
      by_contra hy
      exact hn ⟨_, subset_tsupport f (left_ne_zero_of_mul hy), y⁻¹,
        Set.inv_mem_inv.2 (subset_tsupport _ (right_ne_zero_of_mul hy)), by simp⟩
    simp [this]
  have e1 : ∀ γ : Γ, GlobalTheory.AutomorphicL2Unitary.conv μ f f' (γ * x) = ∫ y, f (γ * y) * f' (y⁻¹ * x) ∂μ := fun γ => by
    unfold GlobalTheory.AutomorphicL2Unitary.conv
    rw [← integral_mul_left_eq_self _ (γ : G)]
    simp [mul_assoc]
  unfold cv
  rw [GlobalTheory.AutomorphicL2Unitary.orbitSum, tsum_congr e1, integral_tsum_of_summable_integral_norm hint hsum]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hy, tsum_mul_right, GlobalTheory.AutomorphicL2Unitary.orbitSum]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.DmTest
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in
private noncomputable def spl : GA E a ≃ₜ* archGroup E a × GL (Fin a) (Af E) where
  toMulEquiv := (AdelicGLn.prodEquiv E a).toMulEquiv.trans
    (MulEquiv.prodCongr (archEquiv E a).toMulEquiv (MulEquiv.refl _))
  continuous_toFun := ((archEquiv E a).continuous.prodMap continuous_id).comp (AdelicGLn.prodEquiv E a).continuous
  continuous_invFun := (AdelicGLn.prodEquiv E a).symm.continuous.comp
    ((archEquiv E a).symm.continuous.prodMap continuous_id)

private theorem spl_symm (x : archGroup E a) (b : GL (Fin a) (Af E)) :
    (spl E a).symm (x, b) = finEmb E a b * infEmb E a x := by
  refine (AdelicGLn.prodEquiv E a).injective ?_
  rw [map_mul, prodEquiv_infEmb, prodEquiv_finEmb, Prod.mk_mul_mk, one_mul, mul_one]
  exact (AdelicGLn.prodEquiv E a).apply_symm_apply _

private theorem spl_fin (b : GL (Fin a) (Af E)) : (spl E a).symm (1, b) = finGL E a b := by
  rw [spl_symm, map_one, mul_one, UpperTheory.V.Fb.finEmb_eq]

private theorem arch_iff (φ : GA E a → ℂ) :
    IsArchSmooth φ ↔ ∀ b, (isExpLieAlgebra E a).IsSmoothFun fun x => φ ((spl E a).symm (x, b)) := by
  simp only [spl_symm]
  refine ⟨fun h b => h (finEmb E a b), fun h g => ?_⟩
  rw [← infEmb_mul_finEmb g, infEmb_mul_finEmb_comm, archSlice_mul]
  exact ((isExpLieAlgebra E a).leftTranslateEnd _ ⟨_, h _⟩).2

variable [_root_.NumberField.IsTotallyComplex E]

private def stab (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | ∀ g, φ.1 (g * finGL E a k) = φ.1 g}
  one_mem' := fun g => by rw [map_one, mul_one]
  mul_mem' := fun {k l} hk hl g => by rw [map_mul, ← mul_assoc, hl, hk]
  inv_mem' := fun {k} hk g => by
    rw [← hk (g * finGL E a k⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

private theorem lev_iff (φ : Sm E a) : HasLev φ ↔ IsOpen (stab φ : Set (GL (Fin a) (Af E))) := by
  have : {k | act (.fin k) φ = φ} = (stab φ : Set (GL (Fin a) (Af E))) := by
    ext k
    exact ⟨fun h g => congrFun (congrArg Subtype.val h) g, fun h => Subtype.ext (funext h)⟩
  rw [HasLev, this]

private theorem smooth_of (φ : Sm E a) (h : HasLev φ) :
    ProdSmooth.IsSmooth (isExpLieAlgebra E a) (spl E a) φ.1 := by
  have ho : IsOpen ((stab φ ⊓ AdelicGLn.integralFiniteGL E a : Subgroup (GL (Fin a) (Af E))) :
      Set (GL (Fin a) (Af E))) := ((lev_iff φ).1 h).inter (AdelicGLn.isOpen_integralFiniteGL E a)
  refine ⟨(arch_iff φ.1).1 (UpperTheory.V.Cm.isArchSmooth_of_mem φ.2), _, ho,
    (AdelicGLn.isCompact_integralFiniteGL E a).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun _ h => h.2,
    fun x v hv => ?_⟩
  rw [spl_fin]
  exact hv.1 x

private theorem test_of (φ : CompactlySupportedContinuousMap (GA E a) ℂ)
    (h : ProdSmooth.IsSmooth (isExpLieAlgebra E a) (spl E a) φ) : ∃ u : Sm E a, IsTest u ∧ u.1 = φ := by
  obtain ⟨h1, V, hV, -, h2⟩ := h
  refine ⟨⟨φ, UpperTheory.V.Cm.mem_Sm_of ((arch_iff _).2 h1)⟩, ⟨φ.hasCompactSupport, ?_⟩, rfl⟩
  rw [lev_iff]
  refine Subgroup.isOpen_mono (H₁ := V) (fun v hv g => ?_) hV
  rw [← spl_fin]
  exact h2 g v hv

end

theorem UpperTheory.V.Cj.H.dmTest :
    UpperTheory.V.Cj.H.DmTest := by
  intro E _ _ _ a μ _ f hf
  let F : CompactlySupportedContinuousMap (GA E a) ℂ := ⟨⟨f.1, ((testOps E a f).1 hf.2).1⟩, hf.1⟩
  obtain ⟨n, φ, ψ, h, e⟩ := GroundTheory.Automorphic.ProdSmooth.exists_sum_conv _ (spl E a) μ F (smooth_of f hf.2)
  choose u hu eu using fun i => test_of (φ i) (h i).1
  choose v hv ev using fun i => test_of (ψ i) (h i).2
  refine ⟨n, u, v, fun i => ⟨hu i, hv i⟩, funext fun x => ?_⟩
  have := congrArg (fun G : CompactlySupportedContinuousMap (GA E a) ℂ => G x) e
  simp only [CompactlySupportedContinuousMap.sum_apply, GroundTheory.Automorphic.conv_apply] at this
  rw [Finset.sum_apply]
  simp only [eu, ev]
  exact this
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
private theorem summable_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {u v : G → ℂ} (hu : HasCompactSupport u)
    (hv : HasCompactSupport v) (x : G) : Summable fun γ : Γ => GlobalTheory.AutomorphicL2Unitary.conv μ u v (γ * x) := by
  obtain ⟨N, hN⟩ := (locInt G Γ μ).2 _ (IsCompact.mul hu hv)
  refine summable_of_hasFiniteSupport ((Set.finite_of_encard_le_coe (hN x)).subset fun γ hγ => ?_)
  by_contra hn
  refine hγ ?_
  have h0 : (fun y => u y * v (y⁻¹ * ((γ : G) * x))) = 0 := by
    funext y
    by_contra hy
    exact hn ⟨y, subset_tsupport u (left_ne_zero_of_mul hy), y⁻¹ * ((γ : G) * x),
      subset_tsupport v (right_ne_zero_of_mul hy), mul_inv_cancel_left _ _⟩
  simp only [GlobalTheory.AutomorphicL2Unitary.conv, h0]
  simp

theorem UpperTheory.V.Cj.H.cptGard :
    UpperTheory.V.Cj.H.CptGard := by
  intro E _ _ _ a μ _ _ φ hl hi C hC hs
  obtain ⟨f, hf, hφ⟩ := orbLift E a φ hl hi C hC hs
  obtain ⟨k, u, v, huv, hsum⟩ := dmTest E a μ f hf
  have hc : ∀ ψ : Sm E a, IsTest ψ → Continuous ψ.1 := fun ψ h => ((testOps E a ψ).1 h.2).1
  choose h hh using fun i => orbConv (GA E a) (latticeGL E a) μ (u i).1 (v i).1 (hc _ (huv i).1) (huv i).1.1
    (hc _ (huv i).2) (huv i).2.1
  have e : φ = ∑ i, (⟨cv (v i).1 (h i).toL2, cvSm E a μ (v i) (huv i).2 _⟩ : Sm E a) := by
    apply Subtype.ext
    rw [hφ, hsum, Submodule.coe_sum]
    funext x
    simp only [Finset.sum_apply, ← hh, GlobalTheory.AutomorphicL2Unitary.orbitSum]
    exact Summable.tsum_finsetSum fun i _ => summable_conv _ μ (huv i).1.1 (huv i).2.1 x
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨v i, (h i).toL2, (huv i).2, rfl⟩
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem lev_mulChi {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (χ : HChar E) (φ : Sm E a)
    (h : HasLev φ) : HasLev (mulChi a χ φ) := by
  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  change IsOpen (S : Set (GL (Fin a) (Af E)))
  refine S.isOpen_of_mem_nhds (g := 1) (mem_of_superset
    ((h.inter (isOpen_ker_chiDet (a := a) χ)).mem_nhds ⟨?_, by simp⟩) ?_)
  · change finRep E a 1 φ = φ
    simp
  · rintro k ⟨hk, hk'⟩
    have e1 : rt E a (finGL E a k) φ = φ := hk
    have e2 : chiDet a χ (finGL E a k) = 1 := hk'
    change rt E a (finGL E a k) (mulChi a χ φ) = mulChi a χ φ
    rw [rt_mulChi, e1, e2, Units.val_one, one_smul]

theorem UpperTheory.V.Cj.H.twCpt :
    UpperTheory.V.Cj.H.TwCpt := by
  intro E _ _ _ a ha μ _ _ r χ hχ φ hl hlev hone ⟨R, hR⟩
  obtain ⟨C, hC, hC'⟩ := (qhtFacts E a).2.2.2 R
  have hz : lie E a (oneL E a) (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ := by
    rw [hχ.2, hone, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, map_zero, zero_smul]
  refine cptGard E a μ _ (lev_mulChi χ φ hlev) (CuspidalL2GL.leftInv_latticeGL (fun γ g => ?_) fun t g => ?_)
    ((fun p : ℝ × GA E a => splitCentre E a p.1 * p.2) '' (Set.Icc (-1 : ℝ) 0 ×ˢ C))
    ((isCompact_Icc.prod hC).image
      ((GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.comp continuous_fst).mul continuous_snd)) fun g hg => ?_
  · rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, hl]
  · rw [aInv E a _ _ hz t g, zero_mul, Complex.exp_zero, one_mul]
  · have h1 : qht g ≤ R := not_lt.1 fun h => hg (by rw [mulChi_apply, hR g h, zero_mul])
    obtain ⟨γ, t, ht⟩ := hC' g h1
    refine ⟨ratGL E a γ * splitCentre E a 1 ^ ⌊t⌋,
      mul_mem (CuspidalL2GL.ratGL_mem_latticeGL γ) (CuspidalL2GL.zpow_mem_latticeGL _),
      (-Int.fract t, ratGL E a γ * splitCentre E a t * g),
      ⟨⟨neg_le_neg (Int.fract_lt_one t).le, neg_nonpos.2 (Int.fract_nonneg t)⟩, ht⟩, ?_⟩
    have e : -Int.fract t + t = ((⌊t⌋ : ℤ) : ℝ) := by rw [Int.fract]; ring
    change splitCentre E a (-Int.fract t) * (ratGL E a γ * splitCentre E a t * g) = _
    rw [← CuspidalL2GL.splitCentre_intCast, ← e, CuspidalL2GL.splitCentre_add, ← mul_assoc, ← mul_assoc,
      CuspidalL2GL.splitCentre_comm (-Int.fract t) (ratGL E a γ), mul_assoc (ratGL E a γ)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevOfMulChi
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem open_fix {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem lev_of_mulChi (χ : HChar E) (φ : Sm E a) (h : HasLev (mulChi a χ φ)) : HasLev φ := by
  have hl : IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} := h
  change IsOpen {k | finRep E a k φ = φ}
  refine open_fix (finRep E a) _ (hl.inter (isOpen_ker_chiDet (a := a) χ)) ⟨by simp, by simp⟩ ?_
  rintro k ⟨h1, h2⟩
  have h1' : rt E a (finGL E a k) (mulChi a χ φ) = mulChi a χ φ := h1
  have h2' : chiDet a χ (finGL E a k) = 1 := h2
  rw [rt_mulChi, h2'] at h1'
  change rt E a (finGL E a k) φ = φ
  apply (mulChi a χ).injective
  simpa using h1'

end

theorem UpperTheory.V.Cj.H.twSq :
    UpperTheory.V.Cj.H.TwSq := by
  intro E _ _ _ a ha μ _ _ r χ hχ φ hφ
  obtain ⟨⟨s, hs⟩, hχ⟩ := hχ
  have hG := gardFacts E a ha μ
  have hlie : ∀ ψ : Sm E a, mulChi a χ ψ ∈ gard μ → ∀ X, mulChi a χ (lie E a X ψ) ∈ gard μ := fun ψ hψ X => by
    have h1 := (hG _ hψ).2.2.2.1 X
    rw [hχ, map_add (f := _), map_smul] at h1
    simpa using (gard μ).sub_mem h1 ((gard μ).smul_mem ((r * ell E a X : ℝ) : ℂ) hψ)
  have hleft : ∀ ψ : Sm E a, mulChi a χ ψ ∈ gard μ → ∀ γ g,
      (mulChi a χ ψ).1 (ratGL E a γ * g) = (mulChi a χ ψ).1 g := fun ψ hψ γ g =>
    (hG _ hψ).2.1.1 _ (CuspidalL2GL.ratGL_mem_latticeGL γ) g
  have key : ∀ ψ : Sm E a, mulChi a χ ψ ∈ gard μ → lie E a (oneL E a) ψ = -(r : ℂ) • ψ → IsSqIntMod ψ := fun ψ hψ hr => by
    have h0 : lie E a (oneL E a) (mulChi a χ ψ) = (0 : ℂ) • mulChi a χ ψ := by
      rw [hχ, hr, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, zero_smul, map_zero]
    have h1 : IsSqInt (mulChi a χ ψ).1 :=
      (CuspidalL2GL.memL2_iff_isSqInt (μ := μ) (ContAut.continuous_of_isOpen_stab E a _ (hG _ hψ).1) (hleft ψ hψ) fun t g => by
        rw [aInv E a _ 0 h0 t g, zero_mul, Complex.exp_zero, one_mul]).1 (hG _ hψ).2.1
    refine ⟨s, χ, hs, ?_⟩
    have e : (fun g => ((chiDet a χ g : ℂˣ) : ℂ) * ψ.1 g) = (mulChi a χ ψ).1 := funext fun g => by
      rw [mulChi_apply, mul_comm]
    rw [e]
    exact h1
  refine ⟨hlie φ hφ, fun hr => ⟨fun γ g => ?_, lev_of_mulChi χ φ (hG _ hφ).1, hr, fun l => ?_⟩⟩
  · have h := hleft φ hφ γ g
    rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul] at h
    exact mul_right_cancel₀ (Units.ne_zero _) h
  · have h : mulChi a χ ((l.map (lie E a)).prod φ) ∈ gard μ ∧
        lie E a (oneL E a) ((l.map (lie E a)).prod φ) = -(r : ℂ) • (l.map (lie E a)).prod φ := by
      induction l with
      | nil => exact ⟨hφ, hr⟩
      | cons X l ih =>
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
        exact ⟨hlie _ ih.1 X, by rw [lie_one_comm, ih.2, map_smul]⟩
    exact key _ h.1 h.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocLimMul
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private noncomputable def cj (χ : HChar E) (T : Module.End ℂ (Sm E a)) : Module.End ℂ (Sm E a) :=
  (mulChi a χ).symm.toLinearMap ∘ₗ T ∘ₗ (mulChi a χ).toLinearMap

private theorem mul_cj (χ : HChar E) (T : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    mulChi a χ (cj χ T φ) = T (mulChi a χ φ) := (mulChi a χ).apply_symm_apply _

private theorem isOp_cj {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) {N : Submodule ℂ (Sm E a)}
    {T : Module.End ℂ (Sm E a)} (hT : IsOp N T) : IsOp (N.comap (mulChi a χ).toLinearMap) (cj χ T) := by
  refine { maps := ?_, lie := ?_, rt := ?_ }
  · intro φ hφ
    change mulChi a χ (cj χ T φ) ∈ N
    rw [mul_cj]
    exact hT.maps _ hφ
  · intro X φ hφ
    apply (mulChi a χ).injective
    have h1 := hT.lie X _ hφ
    have h2 := hχ.2 X (cj χ T φ)
    change lie E a X (T (mulChi a χ φ)) = T (lie E a X (mulChi a χ φ)) at h1
    rw [mul_cj, h1, hχ.2, map_add (f := _), map_add (f := _), map_add (f := _), map_smul, map_smul, map_smul, mul_cj] at h2
    rw [mul_cj]
    exact (add_right_cancel h2).symm
  · intro g φ hφ
    apply (mulChi a χ).injective
    have h1 := hT.rt g _ hφ
    have h2 := rt_mulChi χ g (cj χ T φ)
    change rt E a g (T (mulChi a χ φ)) = T (rt E a g (mulChi a χ φ)) at h1
    rw [mul_cj, h1, rt_mulChi, map_smul, map_smul, map_smul] at h2
    rw [mul_cj]
    exact (smul_right_injective _ (chiDet a χ g).ne_zero h2).symm

private theorem shift_mul {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) (X : Lie E a) (φ : Sm E a) :
    shift (lie E a) 0 X (mulChi a χ φ) = mulChi a χ (shift (lie E a) r X φ) := by
  rw [shift_apply, shift_apply, zero_mul, zero_smul, add_zero, hχ.2, LinearMap.add_apply, LinearMap.smul_apply,
    one_apply_eq_self, Complex.coe_smul]

private theorem casA_mul {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) (c : ℝ) {n : ℕ} (e : Fin n → Herm E a)
    (φ : Sm E a) : casA 0 c e (mulChi a χ φ) = mulChi a χ (casA r c e φ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, mul_apply_eq_comp, LinearMap.smul_apply,
    one_apply_eq_self, map_sub, map_sum, map_smul, shift_mul hχ]

private theorem locLim_mul (χ : HChar E) {f : ℕ → Sm E a} {φ : Sm E a}
    (h : LocLim (fun k => mulChi a χ (f k)) (mulChi a χ φ)) : LocLim f φ := by
  intro C hC
  have hc : Continuous fun g : GA E a => (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (χ.2.1.comp Matrix.GeneralLinearGroup.continuous_det).inv
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  have h1 := h C hC
  rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
  intro ε hε
  have hp : 0 < |B| + 1 := by positivity
  filter_upwards [h1 (ε / (|B| + 1)) (by positivity)] with k hk g hg
  have h2 := hk g hg
  rw [dist_eq_norm, mulChi_apply, mulChi_apply, ← sub_mul, lt_div_iff₀ hp] at h2
  have e : φ.1 g - (f k).1 g = (φ.1 g - (f k).1 g) * (chiDet a χ g : ℂˣ) * (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) :=
    (Units.mul_inv_cancel_right _ _).symm
  rw [dist_eq_norm, e, norm_mul]
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) h2
  exact (hB g hg).trans ((le_abs_self B).trans (le_add_of_nonneg_right zero_le_one))

end

theorem UpperTheory.V.Cj.H.twRes :
    UpperTheory.V.Cj.H.TwRes := by
  intro E _ _ _ a r χ hχ N n e c P Q S h
  refine ⟨cj χ P, fun k => cj χ (Q k), fun k => cj χ (S k), isOp_cj hχ h.opP, fun k => isOp_cj hχ (h.opQ k),
    fun k => isOp_cj hχ (h.opS k), fun k φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · apply (mulChi a χ).injective
    rw [map_sub, ← casA_mul hχ, mul_cj, mul_cj]
    exact h.res k _ hφ
  · apply (mulChi a χ).injective
    rw [map_zero, ← casA_mul hχ, mul_cj]
    exact h.ker _ hφ
  · apply locLim_mul χ
    simp only [mul_cj]
    exact h.lim _ hφ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ChiGrow
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.chiGrow :
    UpperTheory.V.Cj.H.ChiGrow := by
  intro E _ _ _ a χ s _ φ hφ g
  obtain ⟨A, p, hA⟩ := hφ g
  obtain ⟨B, q, hB⟩ := chiDet_growth (a := a) χ⁻¹
  have hback : mulChi a χ⁻¹ (mulChi a χ φ) = φ := by
    rw [← mulChi_mul, mul_inv_cancel, mulChi_one]
  refine ⟨‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (A * B), p + q, fun y => ?_⟩
  have e : φ.1 (g * infGL E a y) = ((chiDet a χ⁻¹ g : ℂˣ) : ℂ) *
      ((mulChi a χ φ).1 (g * infGL E a y) * ((chiDet a χ⁻¹ (infGL E a y) : ℂˣ) : ℂ)) := by
    conv_lhs => rw [← hback, mulChi_apply, map_mul, Units.val_mul]
    ring
  have hprod := mul_le_mul (hA y) (hB y) (norm_nonneg _) ((norm_nonneg _).trans (hA y))
  calc ‖φ.1 (g * infGL E a y)‖
      = ‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (‖(mulChi a χ φ).1 (g * infGL E a y)‖ *
          ‖((chiDet a χ⁻¹ (infGL E a y) : ℂˣ) : ℂ)‖) := by rw [e, norm_mul, norm_mul]
    _ ≤ ‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (A * GlobalTheory.CuspRep.height y ^ p * (B * GlobalTheory.CuspRep.height y ^ q)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := by rw [pow_add]; ring
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.fnProj :
    UpperTheory.V.Cj.H.FnProj := by
  intro E _ _ _ a ha r n e he c
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsHaarMeasure := inferInstanceAs (Measure.haar : Measure (GA E a)).IsHaarMeasure
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Lit.Bor.twEx E a ha r
  obtain ⟨P, Q, S, h⟩ := fnProj0 E a ha μ n e he c
  obtain ⟨P', Q', S', h'⟩ := twRes E a r χ hχ (gard μ) n e c P Q S h
  refine ⟨_, P', Q', S', ⟨fun X φ hφ => (twSq E a ha μ r χ hχ φ hφ).1 X, fun φ hφ => ?_,
    fun φ hφ => (twSq E a ha μ r χ hχ φ hφ).2, fun φ h1 h2 h3 h4 => twCpt E a ha μ r χ hχ φ h1 h2 h3 h4⟩, h'⟩
  obtain ⟨s, hs⟩ := hχ.1
  exact chiGrow E a χ s hs φ (gardFacts E a ha μ _ hφ).2.2.1
