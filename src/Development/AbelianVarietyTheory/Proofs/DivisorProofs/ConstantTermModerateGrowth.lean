module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.ConstTermGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf_alt : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_alt)

theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_mul_left_le {Ω : Set (GL (Fin a) (Cinf E))} (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), height (c * y) ≤ B * height y := by
  have c1 : Continuous fun u : GL (Fin a) (Cinf E) => toL u.val :=
    (Units.continuous_val : Continuous fun u : GL (Fin a) (Cinf E) => u.val)
  have c2 : Continuous fun u : GL (Fin a) (Cinf E) => toL (u⁻¹).val :=
    (Units.continuous_coe_inv : Continuous fun u : GL (Fin a) (Cinf E) => (u⁻¹).val)
  obtain ⟨M1, h1⟩ := hΩ.exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨M2, h2⟩ := hΩ.exists_bound_of_continuousOn c2.continuousOn
  have M0 : (0 : ℝ) ≤ max 0 (max M1 M2) := le_max_left _ _
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  refine ⟨1 + a * max 0 (max M1 M2), by positivity, fun c hc y => ?_⟩
  have m1 : ‖toL c.val‖ ≤ max 0 (max M1 M2) := (h1 c hc).trans ((le_max_left _ _).trans (le_max_right _ _))
  have m2 : ‖toL (c⁻¹).val‖ ≤ max 0 (max M1 M2) := (h2 c hc).trans ((le_max_right _ _).trans (le_max_right _ _))
  have e2 : ((c * y)⁻¹ : GL (Fin a) (Cinf E)).val = (y⁻¹).val * (c⁻¹).val := by
    rw [_root_.mul_inv_rev]; rfl
  have p1 := norm_toL_mul_le c.val y.val
  have p2 := norm_toL_mul_le (y⁻¹).val (c⁻¹).val
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have q1 : (a : ℝ) * (‖toL c.val‖ * ‖toL y.val‖) ≤ a * max 0 (max M1 M2) * ‖toL y.val‖ := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right m1 n1) ha
  have q2 : (a : ℝ) * (‖toL (y⁻¹).val‖ * ‖toL (c⁻¹).val‖) ≤ a * max 0 (max M1 M2) * ‖toL (y⁻¹).val‖ := by
    calc (a : ℝ) * (‖toL (y⁻¹).val‖ * ‖toL (c⁻¹).val‖) ≤ a * (‖toL (y⁻¹).val‖ * max 0 (max M1 M2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m2 n2) ha
      _ = _ := by ring
  have aM : (0 : ℝ) ≤ a * max 0 (max M1 M2) := by positivity
  unfold height
  rw [show toL (c * y).val = toL (c.val * y.val) from rfl, e2]
  nlinarith

theorem uniform_growth (φ : Sm E a) (hopen : IsOpen {k | finRep E a k φ = φ})
    (hgr : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N)
    {Ω : Set (GA E a)} (hΩ : IsCompact Ω) :
    ∃ (C : ℝ) (N : ℕ), ∀ h ∈ Ω, ∀ y, ‖φ.1 (h * infGL E a y)‖ ≤ C * height y ^ N := by
  have hS : ∀ s : GL (Fin a) (Af E), finRep E a s φ = φ → ∀ x, φ.1 (x * finGL E a s) = φ.1 x := fun s hs x => by
    have := congrFun (congrArg Subtype.val hs) x
    exact this
  have hU : ∀ t : GL (Fin a) (Af E), IsOpen ((fun k => t⁻¹ * k) ⁻¹' {k | finRep E a k φ = φ}) := fun t =>
    hopen.preimage (continuous_const.mul continuous_id)
  have hKf : IsCompact (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E) '' Ω) := hΩ.image continuous_mapFin
  obtain ⟨T, hT⟩ := hKf.elim_finite_subcover (fun t => (fun k => t⁻¹ * k) ⁻¹' {k | finRep E a k φ = φ}) hU
    (fun k _ => Set.mem_iUnion.2 ⟨k, by
      change finRep E a (k⁻¹ * k) φ = φ
      rw [inv_mul_cancel, map_one]; rfl⟩)
  choose C N hCN using hgr
  obtain ⟨B, hB0, hB⟩ := height_mul_left_le (hΩ.image (continuous_mapInf (E := E) (a := a)))
  refine ⟨∑ t ∈ T, |C (finGL E a t)| * B ^ N (finGL E a t), ∑ t ∈ T, N (finGL E a t), fun h hh y => ?_⟩
  obtain ⟨t, htT, hkt⟩ := Set.mem_iUnion₂.1 (hT ⟨h, hh, rfl⟩)
  have e : h * infGL E a y = finGL E a t * infGL E a (Matrix.GeneralLinearGroup.map (pInf E) h * y) *
      finGL E a (t⁻¹ * Matrix.GeneralLinearGroup.map (pFin E) h) := by
    apply ga_ext
    · simp only [map_mul, pInf_infGL, pInf_finGL, one_mul, mul_one]
    · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul, mul_one, mul_inv_cancel_left]
  rw [e, hS _ hkt]
  have hcy := hB _ ⟨h, hh, rfl⟩ y
  have h0 := one_le_height (Matrix.GeneralLinearGroup.map (pInf E) h * y)
  have hy := one_le_height y
  calc ‖φ.1 (finGL E a t * infGL E a (Matrix.GeneralLinearGroup.map (pInf E) h * y))‖
      ≤ C (finGL E a t) * height (Matrix.GeneralLinearGroup.map (pInf E) h * y) ^ N (finGL E a t) := hCN _ _
    _ ≤ |C (finGL E a t)| * (B * height y) ^ N (finGL E a t) :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by linarith) hcy _) (pow_nonneg (by linarith) _) (abs_nonneg _)
    _ = |C (finGL E a t)| * B ^ N (finGL E a t) * height y ^ N (finGL E a t) := by ring
    _ ≤ |C (finGL E a t)| * B ^ N (finGL E a t) * height y ^ (∑ t ∈ T, N (finGL E a t)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy
          (Finset.single_le_sum (f := fun t => N (finGL E a t)) (fun _ _ => Nat.zero_le _) htT))
          (mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _))
    _ ≤ (∑ t ∈ T, |C (finGL E a t)| * B ^ N (finGL E a t)) * height y ^ (∑ t ∈ T, N (finGL E a t)) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun t => |C (finGL E a t)| * B ^ N (finGL E a t))
          (fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _)) htT) (pow_nonneg (by linarith) _)

theorem norm_constTerm_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N) →
    ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  intro E _ _ _ a r _ _ μ 𝓕 _ _ h1 φ hleft hopen hgr g
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hc : Continuous fun x : BlockIx a r → Ad E => unip x * g :=
    GlobalTheory.CuspRep.CuspidalL2GL.continuous_unip.mul continuous_const
  obtain ⟨C, N, hC⟩ := uniform_growth φ hopen hgr (hK.image hc)
  refine ⟨C, N, fun y => ?_⟩
  have hb : ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * (g * infGL E a y))‖ ≤ C * height y ^ N := by
    intro x
    obtain ⟨γ, ⟨z, rfl⟩, hγ⟩ := hcov x
    have hu : unip ((AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) z) =
        ratGL E a (unip z) := unip_algebraMap z
    have e : φ.1 (unip (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r) z + x) * g *
        infGL E a y) = φ.1 (unip x * (g * infGL E a y)) := by
      rw [unip_add, hu]
      simp only [mul_assoc]
      exact hleft _ _
    rw [← e]
    exact hC _ ⟨_, hγ, rfl⟩ y
  have hfin : μ 𝓕 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
  calc _ ≤ C * height y ^ N * (μ 𝓕).toReal := norm_setIntegral_le_of_norm_le_const hfin (fun x _ => hb x)
    _ = C * height y ^ N := by rw [h1]; simp

end GlobalTheory.ConstTermGrowth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowthStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_moderate_growth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N) → ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.ConstTermGrowth.norm_constTerm_le | exact GlobalTheory.ConstTermGrowth.norm_constTerm_le | (intros; apply GlobalTheory.ConstTermGrowth.norm_constTerm_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementSecondPolynomial
noncomputable section

namespace GlobalTheory.SplitTransfer

section Abstract

open Formalism.UG GlobalTheory.PRep

theorem heckeVec_indicator {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {x : V} (hx : x ∈ fixed ρ K) {S : Set G} (hm : ∀ g ∈ S, ∀ k ∈ K, g * k ∈ S) (R : Finset ι)
    (g : ι → G) (hR : ∀ i ∈ R, g i ∈ S) (hR' : ∀ y ∈ S, ∃! i, i ∈ R ∧ (g i)⁻¹ * y ∈ K) :
    GlobalTheory.LFun.heckeVec ρ K (Set.indicator S 1) x = ∑ i ∈ R, ρ (g i) x := by
  classical
  have hinj : Set.InjOn (fun i : ι => (g i : G ⧸ K)) R := fun γ hγ δ hδ e =>
    (hR' _ (hR δ hδ)).unique ⟨hγ, QuotientGroup.eq.1 e⟩ ⟨hδ, by simp⟩
  rw [GlobalTheory.LFun.heckeVec, finsum_eq_sum_of_support_subset (s := R.image fun i : ι => (g i : G ⧸ K)),
    Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (g γ)
    rw [hk, Set.indicator_of_mem (hm _ (hR γ hγ) k k.2), map_mul, Module.End.mul_apply,
      GlobalTheory.LGrp.mem_fixed.1 hx _ k.2]
    simp
  · intro c hc
    have : c.out ∈ S := by
      by_contra h0
      exact hc (by simp [h0])
    obtain ⟨γ, ⟨h1, h2⟩, -⟩ := hR' _ this
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, h1, (QuotientGroup.eq.2 h2).trans c.out_eq'⟩)

end Abstract


open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.InertHeckeEigen Formalism.UG GlobalTheory.PRep GlobalTheory.DefU in
theorem heckeVec_eq_of_isCompAlong {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {U : Submodule ℂ (UA L n → ℂ)} (hU : IsAutRepU U) (w : HeightOneSpectrum (𝓞 L)) {H X : Type} [Group H]
    [AddCommGroup X] [Module ℂ X] {K : Subgroup H} (hK : IsCommensurated K) (p : locU n w →* H)
    (hp : Function.Surjective p) (σ : Representation ℂ H X) (hcomp : IsCompAlong U (locU n w) p σ) {h : H → ℂ}
    (hh : h ∈ Hecke ℂ K) {lam : ℂ} (hsat : ∀ v ∈ fixed σ K, v ≠ 0 → GlobalTheory.LFun.heckeVec σ K h v = lam • v)
    {φ : UA L n → ℂ} (hφ : φ ∈ U) (hfix : ∀ x : locU n w, p x ∈ K → RU L n x.val φ = φ) :
    GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) (K.comap p) (fun x => h (p x)) φ = lam • φ := by
  have hfin : {c : locU n w ⧸ K.comap p | h (p c.out) ≠ 0}.Finite :=
    finite_support_comp p hp hh.1 (Formalism.UG.P.finite_support_cosets hK hh.2)
  have hS : ∀ c : locU n w ⧸ K.comap p, (fun x => h (p x)) c.out ≠ 0 → c ∈ hfin.toFinset :=
    fun c hc => hfin.mem_toFinset.2 hc
  let T : (UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    ∑ c ∈ hfin.toFinset, h (p c.out) • (RU L n) (c.out : UA L n)
  have hT : ∀ x, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) (K.comap p) (fun x => h (p x)) x
      = T x := fun x => by
    rw [heckeVec_eq_sum _ _ _ _ hS x]
    simp [T, LinearMap.sum_apply]
  let Z : Submodule ℂ (UA L n → ℂ) :=
    fixed ((RU L n).comp (locU n w).subtype) (K.comap p) ⊓ LinearMap.ker (T - lam • LinearMap.id)
  have hZ' : ∀ x, x ∈ Z ↔ (∀ k ∈ K.comap p, RU L n (k : UA L n) x = x) ∧ T x = lam • x := fun x => by
    simp only [Z, Submodule.mem_inf, GlobalTheory.LGrp.mem_fixed, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  let π : AutSub L n := ⟨U, hU⟩
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hcomp
  have hirr : Representation.IsIrreducible (σ.comp p) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints L n w
  have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA L n) (locU n w) π.V X X π.rep (locU n w).subtype (σ.comp p) (σ.comp p)
    π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA L n → ℂ) :=
    fun i => U.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.comp p) g u) = (RU L n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining (σ.comp p) (π.rep.comp (locU n w).subtype) i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype),
        LinearMap.range i.toLinearMap).map U.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this
  have hZ : ∀ i v, (∀ k ∈ (K.comap p : Set (locU n w)), (σ.comp p) k v = v) → fi i v ∈ Z := by
    intro i v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]; exact Z.zero_mem
    have hvK : v ∈ fixed σ K := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      obtain ⟨x, rfl⟩ := hp k
      exact hv x hk
    refine (hZ' _).2 ⟨fun k hk => (hfi i k v).symm.trans (congrArg (fi i) (hv k hk)), ?_⟩
    have e2 := heckeVec_comp_surj p hp hh.1 σ hvK
    rw [heckeVec_eq_sum _ _ _ _ hS] at e2
    rw [hsat v hvK hv0] at e2
    rw [← hT (fi i v), heckeVec_eq_sum _ _ _ _ hS]
    calc _ = fi i (∑ c ∈ hfin.toFinset, h (p c.out) • (σ.comp p) c.out v) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_smul, hfi]
      _ = lam • fi i v := by rw [e2, map_smul]
  have hZK : ∀ z ∈ Z, ∀ k ∈ (K.comap p : Set (locU n w)), (RU L n).comp (locU n w).subtype k z = z :=
    fun z hz k hk => ((hZ' z).1 hz).1 k hk
  have hφZ := mem_of_mem_iSup ((RU L n).comp (locU n w).subtype) (σ.comp p) hirr fi hfi _ Z hZ hZK φ
    (fun k hk => hfix k hk) hmem
  rw [hT]
  exact ((hZ' φ).1 hφZ).2

end GlobalTheory.SplitTransfer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTransfer

theorem heckeVec_divInd {D : D7} [IsCMField D.host.E] {V : HSp D}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {j : UA D.host.E V.rank ≃ₜ* GA D V} {h₀ : GA D V} (hT : IsTransfer V θ j h₀)
    {P : HeightOneSpectrum (𝓞 D.host.E)} {φ : UA D.host.E V.rank → ℂ}
    (hφ : ∀ x ∈ KP V.rank P, RU D.host.E V.rank x φ = φ) {d : List ℤ} {R : Finset (GA D V)}
    (hR : GlobalTheory.Hk3.SphOp V P d R) :
    GlobalTheory.LFun.heckeVec ((RU D.host.E V.rank).comp (locU V.rank P).subtype)
      ((GlobalTheory.LFun.KGL P (n := V.rank)).comap ((cLoc P).comp (locU V.rank P).subtype))
      (fun x => divInd (Ov D.host.E P) d (((cLoc P).comp (locU V.rank P).subtype) x)) φ =
      ∑ γ ∈ R, RU D.host.E V.rank ((cj j h₀).symm γ) φ := by
  classical
  obtain ⟨h1, h2⟩ := hT.2.2.2.2.2.2.2 P d R hR
  let g : GA D V → locU V.rank P := fun γ =>
    if h : (cj j h₀).symm γ ∈ locU V.rank P then ⟨_, h⟩ else 1
  have hg : ∀ γ ∈ R, (g γ : UA D.host.E V.rank) = (cj j h₀).symm γ := fun γ hγ => by
    simp only [g, dif_pos (h1 γ hγ).1]
  have e : (fun x : locU V.rank P => divInd (Ov D.host.E P) d (((cLoc P).comp (locU V.rank P).subtype) x)) =
      Set.indicator {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)} 1 := by
    funext x
    by_cases hx : HasDiv (Ov D.host.E P) d (cLoc P x.val)
    · rw [Set.indicator_of_mem (s := {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)}) hx]
      exact Set.indicator_of_mem (s := {g | HasDiv (Ov D.host.E P) d g}) hx _
    · rw [Set.indicator_of_notMem (s := {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)}) hx]
      exact Set.indicator_of_notMem (s := {g | HasDiv (Ov D.host.E P) d g}) hx _
  rw [e, heckeVec_indicator (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hφ k.val ⟨k.2, hk⟩) ?_ R g ?_ ?_]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [← hg γ hγ]
    rfl
  · intro x hx k hk
    have := GlobalTheory.SphGal.hasDiv_mul_mul hx (one_mem _) hk
    rw [one_mul] at this
    change HasDiv _ d (cLoc P (x.val * k.val))
    rw [map_mul]
    exact this
  · intro γ hγ
    change HasDiv _ d (cLoc P (g γ).val)
    rw [hg γ hγ]
    exact (h1 γ hγ).2
  · intro y hy
    obtain ⟨γ, ⟨a1, a2⟩, a3⟩ := h2 y.val y.2 hy
    refine ⟨γ, ⟨a1, ?_⟩, fun δ hδ => a3 δ ⟨hδ.1, ?_⟩⟩
    · change cLoc P ((g γ).val⁻¹ * y.val) ∈ GlobalTheory.LFun.KGL P (n := V.rank)
      rw [hg γ a1]
      exact a2.2
    · rw [← hg δ hδ.1]
      exact ⟨((g δ)⁻¹ * y).2, hδ.2⟩

end GlobalTheory.SplitTransfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjRationalPrincipalCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjRationalPrincipalCongruence
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MsRepsFwd

theorem latOf_congr (F E : Type) [Field F] [NumberField F] [Field E] [CharZero E] [Algebra F E]
    (n M : ℕ) (L : Set (Fin n → E)) (g κ : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E))
    (δ : Matrix (Fin n) (Fin n) E) (hinj : Function.Injective (inclR (F := F) (E := E) (Af F)))
    (hκ : ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, κ *ᵥ z - z = M • y)
    (he : δ.map (inclR (F := F) (Af F)) * g = g * κ) :
    ∀ x ∈ GlobalTheory.AdLat.latOf F g L, ∃ y ∈ GlobalTheory.AdLat.latOf F g L, δ *ᵥ x - x = M • y := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hx
  obtain ⟨y, hy, hzy⟩ := hκ z hz
  let i : E →+* GlobalTheory.AdLat.RA F E := inclR (F := F) (Af F)
  have hf : ∀ v : Fin n → E, GlobalTheory.AdLat.fv F v = i ∘ v := fun _ => rfl
  have e1 : i ∘ (δ *ᵥ x) = δ.map i *ᵥ (i ∘ x) := funext fun a => RingHom.map_mulVec i δ x a
  have e2 : i ∘ (δ *ᵥ x) - i ∘ x = M • (g *ᵥ y) := by
    rw [e1, ← hf x, ← hzx, Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, hzy,
      Matrix.mulVec_smul]
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have hx0 : δ *ᵥ x - x = 0 := by
      funext a
      apply hinj
      have e3 := congrFun e2 a
      simp only [Pi.sub_apply, Function.comp, zero_smul, Pi.zero_apply] at e3
      simp only [Pi.sub_apply, Pi.zero_apply, map_sub, map_zero]
      exact e3
    refine ⟨0, ⟨0, zero_mem _, ?_⟩, by rw [hx0, zero_smul]⟩
    rw [Matrix.mulVec_zero]
    funext a
    simp [GlobalTheory.AdLat.fv]
  · have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
    refine ⟨(M : E)⁻¹ • (δ *ᵥ x - x), ⟨y, hy, ?_⟩, by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hME, one_smul]⟩
    rw [hf]
    funext a
    have e3 := congrFun e2 a
    simp only [Pi.sub_apply, Function.comp, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_sub] at e3 ⊢
    rw [e3, ← map_natCast i M, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hME, map_one, one_mul]

theorem herm_mulVec {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G δ : Matrix (Fin r) (Fin r) E)
    (h : δᵀ * G * δ.map cc = G) (x y : Fin r → E) : herm G (δ *ᵥ x) (δ *ᵥ y) = herm G x y := by
  have hh : ∀ u v : Fin r → E, herm G u v = u ⬝ᵥ (G *ᵥ (fun b => cc (v b))) := by
    intro u v
    simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hc : (fun b => cc ((δ *ᵥ y) b)) = δ.map cc *ᵥ (fun b => cc (y b)) := by
    funext b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cc, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hh, hh, hc, dotProduct_comm (δ *ᵥ x), Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm _ x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

end GlobalTheory.MsRepsFwd

namespace GlobalTheory.MsRepsFwd


set_option maxHeartbeats 800000 in
theorem conj_rat_congr : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (x0 : ∀ c, Frame (X c).Ψ V.rank),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ c, x0 c ∈ (X c).dom) →
    (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
      dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th rfl x0 h (dict g).1))⟩) →
    (∀ c, (X c).Gm = -(V.gram)ᵀ) →
    ∀ (k : Comp) (g : GA D V), dict g = ⟨k, x0 k⟩ →
    ∀ Λk : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (Λk : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (finHom V g).1
        (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) →
    ∀ γ ∈ (X k).Γ, ∃ γ' : GL (Fin V.rank) D.host.E,
      (IsUStab (-(V.gram)ᵀ) Λk γ' ∧ ∀ x ∈ Λk, ∃ y ∈ Λk, (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = M • y) ∧
      ∀ (τ : D.host.E →+* ℂ) (hτ : τ ∈ (X k).Ψ), archM V (th k ⟨τ, hτ⟩) g * (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ =
        (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ * archM V (th k ⟨τ, hτ⟩) g := by
  intro D V Comp X dict Kf th M x0 hK hth hD hdom hA hGm k g hg Λk hΛk γ hγ
  classical
  obtain ⟨-, -, -, -, -, hfib⟩ := hD
  obtain ⟨-, hrat, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have hact : ∀ h, ∀ τ, mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ = archM V (th k τ) h * mat (x0 k) τ := by
    intro h τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) h) *
      mat (x0 k) τ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdom k τ).1),
      Matrix.one_mul]
    rfl
  have key : ∀ h ∈ GinfC V, ∃ γ'' ∈ (X k).Γ,
      dict (g * h) = ⟨k, lact γ'' (rmul (x0 k) (archMat V th rfl x0 h k))⟩ := by
    have := hA g
    rw [hg] at this
    exact this
  have h0 := ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.gramE (X k) hγ
  rw [hGm k] at h0
  have h1 : ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map cc)ᵀ * V.gram * γ.1 = V.gram := by
    have := congrArg (fun A => -Aᵀ) h0
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] using this
  have hun : ∀ τ : (X k).Ψ, ((γ.1.map τ.1).map (starRingEnd ℂ))ᵀ * V.gram.map τ.1 *
      γ.1.map τ.1 = V.gram.map τ.1 := by
    intro τ
    have hcc : (γ.1.map τ.1).map (starRingEnd ℂ) = (γ.1.map cc).map τ.1 := by
      ext a b
      exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
    rw [hcc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h1]
  obtain ⟨h, hh, hw⟩ := hsur _ hun
  have hw' : ∀ τ : (X k).Ψ, archM V (th k τ) h = γ.1.map τ.1 := hw
  obtain ⟨γ'', h1', h2⟩ := key h hh
  obtain ⟨γ₀, hγ₀, κ, hκ, hdc⟩ := hfib g (g * h) (by
    rw [hg]
    refine ⟨γ'' * γ, mul_mem h1' hγ, ?_⟩
    rw [h2]
    congr 1
    funext τ
    show γ''.1.map τ.1 * mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ =
      (γ'' * γ).1.map τ.1 * mat (x0 k) τ
    rw [hact, hw', Units.val_mul, Matrix.map_mul, Matrix.mul_assoc])
  obtain ⟨δ, hδ1, hδ2⟩ := hrat γ₀ hγ₀

  have hγ₀' := Subgroup.mem_subgroupOf.1 (show γ₀ ∈ HFinIn (AF D.host.F) _ (HSpace.gram V) from hγ₀)
  obtain ⟨δ', hδ', hδ'e⟩ := Subgroup.mem_map.1 hγ₀'
  haveI : Nontrivial (Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Af D.host.F) (B := D.host.E)
      (algebraMap D.host.F D.host.E).injective).nontrivial
  have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)).injective
  have hfv : (finHom V γ₀).1 = γ₀.1.1.map
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) := rfl
  have hδδ : δ = δ' := by
    apply Units.ext
    apply Matrix.map_injective hinj
    show δ.1.map (inclR (Af D.host.F)) = δ'.1.map (inclR (Af D.host.F))
    rw [← hδ2, hfv, ← hδ'e]
    ext a b
    show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (inclR (AF D.host.F) (δ'.1 a b)) = inclR (Af D.host.F) (δ'.1 a b)
    simp [inclR]
  subst hδδ

  have hLg := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hU : (δ.1.map cc)ᵀ * V.gram * δ.1 = V.gram := by
    change Formalism.UG.cT _ δ.1 * V.gram * δ.1 = V.gram at hδ'
    convert hδ' using 3
    ext a b
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    congr 1
  have hmat : δ.1ᵀ * -(V.gram)ᵀ * δ.1.map cc = -(V.gram)ᵀ := by
    have := congrArg (fun A => -Aᵀ) hU
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] using this

  obtain ⟨-, hκ2⟩ := (hK κ⁻¹).1 (inv_mem hκ)
  obtain ⟨-, hκ3⟩ := (hK κ).1 hκ
  rw [hLg.1] at hκ2 hκ3
  have hh0 : finHom V h = 1 := hh
  have hfin : finHom V γ₀ * finHom V g = finHom V g * finHom V κ⁻¹ := by
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, hh0, mul_one]
  have hfin' : finHom V γ₀⁻¹ * finHom V g = finHom V g * finHom V κ := by
    have : γ₀⁻¹ * g = g * κ * h⁻¹ := by
      calc γ₀⁻¹ * g = γ₀⁻¹ * (g * h) * h⁻¹ := by group
        _ = γ₀⁻¹ * (γ₀ * g * κ) * h⁻¹ := by rw [hdc]
        _ = g * κ * h⁻¹ := by group
    rw [← map_mul, this, map_mul, map_mul, map_inv, hh0, inv_one, mul_one]
  have hd : finHom V γ₀ = Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) δ := Units.ext hδ2
  have he1 : δ.1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V g).1 = (finHom V g).1 * (finHom V κ⁻¹).1 := by
    rw [← hδ2, ← Units.val_mul, hfin, Units.val_mul]
  have he2 : (δ⁻¹).1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V g).1 = (finHom V g).1 * (finHom V κ).1 := by
    have e0 : finHom V γ₀⁻¹ = Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) δ⁻¹ := by
      rw [map_inv, map_inv, hd]
    have e := congrArg Units.val hfin'
    rw [Units.val_mul, Units.val_mul, e0] at e
    exact e
  have C1 := latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V g).1 (finHom V κ⁻¹).1 δ.1 hinj hκ2 he1
  have C2 := latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V g).1 (finHom V κ).1 (δ⁻¹).1 hinj hκ3 he2
  have hmem : ∀ x, x ∈ Λk ↔ x ∈ GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro x
    rw [← SetLike.mem_coe, hΛk]
  have hcong : ∀ x ∈ Λk, ∃ y ∈ Λk, δ.1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C1 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hcong' : ∀ x ∈ Λk, ∃ y ∈ Λk, (δ⁻¹).1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C2 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hstab : ∀ x, x ∈ Λk ↔ δ.1 *ᵥ x ∈ Λk := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong x hx
      rw [show δ.1 *ᵥ x = x + M • y by rw [← e]; abel]
      exact Λk.add_mem hx (nsmul_mem hy M)
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong' _ hx
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at e
      rw [show x = δ.1 *ᵥ x + M • y by rw [← e]; abel]
      exact Λk.add_mem hx (nsmul_mem hy M)

  have hinf : infHom V γ₀ * infHom V g = infHom V g * infHom V h := by
    have h0 : infHom V κ⁻¹ = 1 := ((hK κ⁻¹).1 (inv_mem hκ)).1
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  have hm : ∀ τ a b, archM V (th k τ) (a * b) = archM V (th k τ) a * archM V (th k τ) b := by
    intro τ a b
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  refine ⟨δ, ⟨⟨herm_mulVec _ _ hmat, hstab⟩, hcong⟩, fun τ hτ => ?_⟩
  rw [← hw' ⟨τ, hτ⟩, ← hδ1 ⟨τ, hτ⟩, ← hm, ← hm]
  have e : infHom V (g * h) = infHom V (γ₀ * g) := by rw [map_mul, map_mul, hinf]
  unfold archM
  rw [e]

end GlobalTheory.MsRepsFwd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjRationalPrincipalCongruenceStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticGroup_conj_rational_principalCongruence : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (x0 : ∀ c, Frame (X c).Ψ V.rank),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ c, x0 c ∈ (X c).dom) →
    (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
      dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th rfl x0 h (dict g).1))⟩) →
    (∀ c, (X c).Gm = -(V.gram)ᵀ) →
    ∀ (k : Comp) (g : GA D V), dict g = ⟨k, x0 k⟩ →
    ∀ Λk : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (Λk : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (finHom V g).1
        (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) →
    ∀ γ ∈ (X k).Γ, ∃ γ' : GL (Fin V.rank) D.host.E,
      (IsUStab (-(V.gram)ᵀ) Λk γ' ∧ ∀ x ∈ Λk, ∃ y ∈ Λk, (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = M • y) ∧
      ∀ (τ : D.host.E →+* ℂ) (hτ : τ ∈ (X k).Ψ), archM V (th k ⟨τ, hτ⟩) g * (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ =
        (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ * archM V (th k ⟨τ, hτ⟩) g := by
  first | exact @GlobalTheory.MsRepsFwd.conj_rat_congr | exact GlobalTheory.MsRepsFwd.conj_rat_congr | (intros; apply GlobalTheory.MsRepsFwd.conj_rat_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBLieMemHtLatIffOfPointOver
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
open GlobalTheory.KernelNoTorsion
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.IndepPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}

def ptsHom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (T : Over S) :
    (T ⟶ A) →* (T ⟶ B) :=
  MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y _


variable [IsAlgClosed C] [CharZero C]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]


variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (e : P.T ≃ₗ[ℤ_[p]] P'.T)




end GlobalTheory.CompHt.IndepPoint

namespace GlobalTheory.CompHt

open IndepPoint

end GlobalTheory.CompHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionCls
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.LBDescent

theorem exists_finite_subextension_cls (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (B X : Scheme.{0}) (pB : B ⟶ Sp K) [QuasiCompact pB]
    [QuasiSeparated pB] (p : X ⟶ Sp Ω) (φ : X ⟶ B)
    (hX : IsPullback φ p pB (spMap (algebraMap K Ω))) (L : LB X) (hL : L.IsLB) :
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp F) (φ₁ : X₁ ⟶ B),
        IsPullback φ₁ p₁ pB (spMap (algebraMap K F)) →
        ∀ j : X ⟶ X₁, j ≫ φ₁ = φ → j ≫ p₁ = p ≫ spMap (algebraMap F Ω) →
          ∃ x : CechPic.Pic X₁, CechPic.pull j x = CechPic.cls L hL := by
  obtain ⟨R, M, ρ, ⟨T, hT⟩, hM, h1, h2, hI⟩ := exists_fg_lb pB p φ hX L hL
  let F : IntermediateField K Ω := IntermediateField.adjoin K (T : Set Ω)
  have hle : R ≤ F.toSubalgebra := by
    rw [← hT]
    exact IntermediateField.algebra_adjoin_le_adjoin K _
  refine ⟨F, IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral), ?_⟩
  intro X₁ p₁ φ₁ hX₁ j hj1 hj2
  let ι : R →+* F := (Subalgebra.inclusion hle).toRingHom
  have e1 : spMap ι ≫ spMap (algebraMap K R) = spMap (algebraMap K F) := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have e2 : spMap (algebraMap F Ω) ≫ spMap ι = spMap R.val.toRingHom := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  let q : X₁ ⟶ Limits.pullback pB (spMap (algebraMap K R)) :=
    Limits.pullback.lift φ₁ (p₁ ≫ spMap ι) (by rw [Category.assoc, e1, hX₁.w])
  have hq : j ≫ q = ρ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, hj1, h1]
    · rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, hj2, Category.assoc, e2, h2]
  refine ⟨CechPic.pull q (CechPic.cls M hM), ?_⟩
  rw [← CechPic.pull_comp, hq, ← CechPic.cls_pull hM ρ (pull_isLB hM ρ), eq_comm, CechPic.cls_eq_iff]
  exact hI

end GlobalTheory.LBDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeNonnegZmodFibreOfNefOnFiniteFieldFibr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeNonnegZmodFibreOfNefOnFiniteFieldFibr
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.NefFibPrime

theorem isClosedImmersion_spMap_zmod (p : ℕ) : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
  IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))

theorem topSelf_nonneg_of_nefFib (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q) (p : ℕ)
    [Fact p.Prime] (h : ArInt.NefFib L) (Z : Scheme.{0})
    (i : Z ⟶ pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    0 ≤ topSelfIntersection (ZMod p) ((L.B.pull (pullback.fst (q ≫ spMap (Int.castRingHom k))
      (spMap (Int.castRingHom (ZMod p))))).pull i) 1 := by
  have := isClosedImmersion_spMap_zmod p
  have : IsClosedImmersion (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
  set f := pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))) with hf
  have h1 := h Z (i ≫ f) (ZMod p) hd
  have e : topSelfIntersection (ZMod p) ((L.B.pull f).pull i) 1 = topSelfIntersection (ZMod p) (L.B.pull (i ≫ f)) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod p) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB f) i)
      (fun _ => LB.isLB_pull L.isLB (i ≫ f)) fun _ => ?_
    show pull i (pull f (cls L.B L.isLB)) = pull (i ≫ f) (cls L.B L.isLB)
    rw [← pull_comp]
  rw [e]
  exact h1

end GlobalTheory.NefFibPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeNonnegZmodFibreOfNefOnFiniteFieldFibrStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveDegree_nonneg_zmodFibre_of_nefOnFiniteFieldFibres : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q) (p : ℕ) [Fact p.Prime], ArInt.NefFib L → ∀ (Z : Scheme.{0}) (i : Z ⟶ pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) ((L.B.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))).pull i) 1 := by
  first | exact @GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib | exact GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib | (intros; apply GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTwoSmulMemAdelicLatticeAtFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTwoSmulMemAdelicLatticeAtFinitePlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem evFin_invTwo_mem {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hv2 : Valued.v (2 : Fv F v) = 1 := by
    have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (2 : 𝓞 F)
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h2] at e
    rw [← e]; congr 1; exact (map_ofNat (algebraMap (𝓞 F) (Fv F v)) 2).symm
  have hm : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hvm := congrArg Valued.v hm
  rw [map_mul, hv2, mul_one, map_one] at hvm
  exact hvm.le

theorem invTwo_smul_mem_latAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d)
    (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ z ∈ GlobalTheory.InertSph.latAt W v, (⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ d W v h2 z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨⅟(2 : AF F) * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem (evFin_invTwo_mem v h2) hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.InertSph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTwoSmulMemAdelicLatticeAtFinitePlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d)
    (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ z ∈ GlobalTheory.InertSph.latAt W v, (⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.InertSph.invTwo_smul_mem_latAt | exact GlobalTheory.InertSph.invTwo_smul_mem_latAt | (intros; apply GlobalTheory.InertSph.invTwo_smul_mem_latAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixUnitaryGroupPreservesGram
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixUnitaryGroupPreservesGram
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ArchUnit

theorem gram_archM : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
    Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → ∀ g : GA D V, gram τ (-(V.gram)ᵀ) (archM V θ g) = (-(V.gram)ᵀ).map τ := by
  intro D V τ θ hθ g
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  have hu := GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram τ
    (fun x => IsCMField.complexEmbedding_complexConj D.host.E τ x) θ hθ g
  have hm : archM V θ g = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram θ g := rfl
  rw [hm]
  have h' := congrArg Matrix.transpose hu
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h'
  have hG : (-(V.gram)ᵀ).map τ = -(V.gram.map τ)ᵀ := by
    ext a b
    simp
  have hg : ∀ (G : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
    intro G x
    ext a b
    simp only [gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hg, hG, Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.mul_assoc]
  exact h'

end GlobalTheory.ArchUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixUnitaryGroupPreservesGramStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanMatrix_unitaryGroup_preserves_gram : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
    Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → ∀ g : GA D V, gram τ (-(V.gram)ᵀ) (archM V θ g) = (-(V.gram)ᵀ).map τ := by
  first | exact @GlobalTheory.ArchUnit.gram_archM | exact GlobalTheory.ArchUnit.gram_archM | (intros; apply GlobalTheory.ArchUnit.gram_archM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMulLeOfIsCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMulLeOfIsCompact
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AutGrowth

theorem height_mul_le_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), CuspRep.height (y * c) ≤ B * CuspRep.height y := by
  intro E _ _ _ a Ω hK
  have c1 : Continuous fun u : GL (Fin a) (Cinf E) => toL u.val :=
    (Units.continuous_val : Continuous fun u : GL (Fin a) (Cinf E) => u.val)
  have c2 : Continuous fun u : GL (Fin a) (Cinf E) => toL (u⁻¹).val :=
    (Units.continuous_coe_inv : Continuous fun u : GL (Fin a) (Cinf E) => (u⁻¹).val)
  obtain ⟨M, M0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Ω, ‖toL u.val‖ ≤ M ∧ ‖toL (u⁻¹).val‖ ≤ M := by
    obtain ⟨M1, h1⟩ := hK.exists_bound_of_continuousOn c1.continuousOn
    obtain ⟨M2, h2⟩ := hK.exists_bound_of_continuousOn c2.continuousOn
    refine ⟨max 0 (max M1 M2), le_max_left _ _, fun x hx => ⟨?_, ?_⟩⟩
    · exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  have aM : 0 ≤ (a : ℝ) * M := by positivity
  refine ⟨1 + a * M, by linarith, fun u hu y => ?_⟩
  obtain ⟨m1, m2'⟩ := hM u hu
  have e2 : ((y * u)⁻¹ : GL (Fin a) (Cinf E)).val = (u⁻¹).val * (y⁻¹).val := by
    rw [_root_.mul_inv_rev]; rfl
  have p1 := norm_toL_mul_le y.val u.val
  have p2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have q1 : (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * M * ‖toL y.val‖ := by
    calc (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * (‖toL y.val‖ * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m1 n1) (Nat.cast_nonneg a)
      _ = a * M * ‖toL y.val‖ := by ring
  have q2 : (a : ℝ) * (‖toL (u⁻¹).val‖ * ‖toL (y⁻¹).val‖) ≤ a * M * ‖toL (y⁻¹).val‖ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left m2' (Nat.cast_nonneg a)) n2
  unfold CuspRep.height
  rw [show toL (y * u).val = toL (y.val * u.val) from rfl, e2]
  nlinarith

end GlobalTheory.AutGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMulLeOfIsCompactStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_height_mul_le_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ B : ℝ, 1 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), height (y * c) ≤ B * height y := by
  first | exact @GlobalTheory.AutGrowth.height_mul_le_of_isCompact | exact GlobalTheory.AutGrowth.height_mul_le_of_isCompact | (intros; apply GlobalTheory.AutGrowth.height_mul_le_of_isCompact <;> assumption)
end
end
