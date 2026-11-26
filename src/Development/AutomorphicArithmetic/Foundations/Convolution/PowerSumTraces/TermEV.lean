module

public import Development.AutomorphicArithmetic.TwistedTraces.IsotypicMultiplicityTensorProduct
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocGalEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistY
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsPosConstEigenspaceBoundOfSplitCMDatum
public import Development.AutomorphicArithmetic.TwistedTraces.EigenspaceFactorizationOverNonsplitPlacesCMDatum
public import Development.AutomorphicArithmetic.TwistedTraces.IntegralOpEigenlineScalarOfTwist
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsUniqueEigenlineOfRankOneOccurs
public import Development.AutomorphicArithmetic.TwistedTraces.ArchimedeanBaseChangeTraceComparison

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalEigenspaceInfFixedOffNCMDatum
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section One
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

private theorem mem_eigL' (w : Pl K) (J : Subgroup (Gw n w)) (χ : Gw n w → ℂ) (v : LL μ) :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
    LinearMap.id_apply]

private theorem mem_fixL' (w : Pl K) (J : Subgroup (Gw n w)) (v : LL μ) :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply,
    Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]

private theorem rhoL_comm {w w' : Pl K} (hne : w' ≠ w) (g : Gw n w) (x : Gw n w') (v : LL μ) :
    rhoL μ w' x (rhoL μ w g v) = rhoL μ w g (rhoL μ w' x v) := by
  have h := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' hne g x
  simp only [rhoL, rhoF]
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, ← map_mul, ← map_mul, h]

end One

private theorem kerChr_co {G : Type} [Group G] [TopologicalSpace G] {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (h : IsChr J χ) :
    CO (kerChr J χ h) := by
  have e : (kerChr J χ h : Set G) = (J : Set G) ∩ χ ⁻¹' {1} := rfl
  have ho : IsOpen (χ ⁻¹' {(1 : ℂ)}) := h.1.isOpen_fiber 1
  have hc : IsClosed (χ ⁻¹' {(1 : ℂ)}) := isClosed_singleton.preimage h.1.continuous
  rw [CO, e]
  exact ⟨hJ.1.inter_right hc, hJ.2.inter ho⟩

private theorem exists_ext {A ι : Type*} {B : A → Type*} (f : ι → A) (hf : Function.Injective f) (U : ∀ i, B (f i))
    (d : ∀ a, B a) : ∃ U' : ∀ a, B a, (∀ i, U' (f i) = U i) ∧ ∀ a, a ∉ Set.range f → U' a = d a := by
  have key : ∀ (i j : ι) (hj : f j = f i), (hj ▸ U j : B (f i)) = U i := by
    intro i j hj
    obtain rfl := hf hj
    rfl
  refine ⟨fun a => if h : ∃ i, f i = a then h.choose_spec ▸ U h.choose else d a, fun i => ?_, fun a ha => dif_neg ha⟩
  have h : ∃ j, f j = f i := ⟨i, rfl⟩
  simp only [dif_pos h]
  exact key i _ _

section Two
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q}
variable (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]

private theorem under_of_over {v : Pl F} (u : PlacesOver E v) : u.1.under (𝓞 F) = v := by
  ext1
  exact (Ideal.over_def u.1.asIdeal v.asIdeal).symm

private theorem finite_over (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
  subst hw
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem mem_Zv (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : LL μ →L[ℂ] LL μ) (x : ℝ) (v : LL μ) :
    v ∈ eigIn (V ⊓ offN μ T) O x ↔ v ∈ V ∧ (∀ w : Pl E, w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) → v ∈ eigL μ w (T.J w) (T.χ w)) ∧
      O v = (x : ℂ) • v := by
  simp only [eigIn, offN, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe,
    and_assoc]

private theorem Zv_closed (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (hV : IsClosed (V : Set (LL μ))) (O : LL μ →L[ℂ] LL μ) (x : ℝ) :
    IsClosed (eigIn (V ⊓ offN μ T) O x : Set (LL μ)) := by
  have e : (eigIn (V ⊓ offN μ T) O x : Set (LL μ)) = (V : Set (LL μ)) ∩ ((⋂ w, ⋂ (_ : w.under (𝓞 F) ∉ (nsS T : Set (Pl F))),
      (eigL μ w (T.J w) (T.χ w) : Set (LL μ))) ∩ {v | O v = (x : ℂ) • v}) := by
    ext v
    simp only [SetLike.mem_coe, mem_Zv, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  refine hV.inter (IsClosed.inter ?_ (isClosed_eq O.continuous (continuous_const_smul _)))
  exact isClosed_iInter fun w => isClosed_iInter fun _ =>
    (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) (T.χ w) (T.co w) (T.chr w)).1

end Two

theorem UpperTheory.finiteDimensional_eigenspace_inf_fixed_offN_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
        (ν : Measure (archGroup E n)) [ν.IsHaarMeasure] (a : TI E n) (q : Pl F) (w₀ : PlacesOver E q) (T : Ty σ n q w₀)
        (V : Submodule ℂ (LL μ)), IsSummand μ V → (∀ v ∈ nsS T, ∀ u : PlacesOver E v, u = T.mk' v) → ∀ x : ℝ, x ≠ 0 →
          IsClosed (eigIn (V ⊓ offN μ T) (Oinf μ ν a) x : Set (LL μ)) ∧
          (∀ v ∈ nsS T, ∀ g, ∀ f ∈ eigIn (V ⊓ offN μ T) (Oinf μ ν a) x, rhoL μ (T.mk' v).1 g f ∈ eigIn (V ⊓ offN μ T) (Oinf μ ν a) x) ∧
          ∀ (r : ℕ) (p : Fin r → Pl F), Function.Injective p → (∀ v, v ∈ nsS T ↔ v ∈ Set.range p) →
          ∀ U : ∀ i, Subgroup (Gw n (T.mk' (p i)).1), (∀ i, CO (U i)) →
            FiniteDimensional ℂ ↥(eigIn (V ⊓ offN μ T) (Oinf μ ν a) x ⊓ ⨅ i, fixL μ (T.mk' (p i)).1 (U i)) := by
  intro F E _ _ _ _ _ σ n hn μ _ ν _ a q w₀ T V hV huniq x hx
  refine ⟨Zv_closed μ T V hV.closed _ x, ?_, ?_⟩
  · intro v hv g f hf
    obtain ⟨m, _, -⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx E n hn).2.1 μ ν
    obtain ⟨h1, h2, h3⟩ := (mem_Zv μ T V _ x f).1 hf
    refine (mem_Zv μ T V _ x _).2 ⟨hV.inv _ _ h1, fun w hw => ?_, ?_⟩
    · refine (mem_eigL' μ _ _ _ _).2 fun y hy => ?_
      have hne : w ≠ (T.mk' v).1 := fun h => hw (by rw [h, under_of_over]; exact hv)
      rw [rhoL_comm μ hne, (mem_eigL' μ _ _ _ _).1 (h2 w hw) y hy, map_smul]
    · have hc : Oinf μ ν a (rhoL μ (T.mk' v).1 g f) = rhoL μ (T.mk' v).1 g (Oinf μ ν a f) :=
        DFunLike.congr_fun ((UpperTheory.ConvolutionTheory.Tf.opAlg E n μ ν m).2.2.2.2.2.2.2.2 a (AdelicGLn.localEmbedding (T.mk' v).1 g)).eq f
      rw [hc, h3, map_smul]
  · intro r p hp hpr U hU
    have hfin : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S}.Finite := by
      have : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S} = ⋃ v ∈ insert q T.S, {w : Pl E | w.under (𝓞 F) = v} := by
        ext w
        simp
      rw [this]
      exact (Finset.finite_toSet _).biUnion fun v _ => finite_over v
    set P : Finset (Pl E) := hfin.toFinset with hP
    have hPm : ∀ w, w ∈ P ↔ w.under (𝓞 F) ∈ insert q T.S := fun w => by simp [hP]
    let f : Fin r → Pl E := fun i => (T.mk' (p i)).1
    have hf : Function.Injective f := fun i j hij => hp (by
      have := congrArg (fun w : Pl E => w.under (𝓞 F)) hij
      simpa only [f, under_of_over] using this)
    obtain ⟨U', hU1, hU2⟩ := exists_ext (B := fun w : Pl E => Subgroup (Gw n w)) f hf U
      (fun w => kerChr (T.J w) (T.χ w) (T.chr w))
    have hU' : ∀ w ∈ P, CO (U' w) := fun w _ => by
      by_cases hw : w ∈ Set.range f
      · obtain ⟨i, rfl⟩ := hw
        rw [hU1]
        exact hU i
      · rw [hU2 w hw]
        exact kerChr_co (T.co w) (T.chr w)
    have hoff : ∀ w : Pl E, w ∉ Set.range f → w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) := fun w hw h => by
      have h' : w.under (𝓞 F) ∈ nsS T := h
      have e := huniq _ h' ⟨w, ⟨rfl⟩⟩
      obtain ⟨i, hi⟩ := (hpr _).1 h'
      refine hw ⟨i, ?_⟩
      have e' : w = (T.mk' (w.under (𝓞 F))).1 := congrArg Subtype.val e
      exact (congrArg (fun v => (T.mk' v).1) hi).trans e'.symm
    haveI := UpperTheory.ConvolutionTheory.C.eigAdm E n hn μ ν a x hx P U' hU'
    refine Submodule.finiteDimensional_of_le (fun v hv => ?_)
      (S₂ := eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ P ⊓ ⨅ w ∈ P, fixL μ w (U' w))
    obtain ⟨hZ, hfx⟩ := Submodule.mem_inf.1 hv
    obtain ⟨h1, h2, h3⟩ := (mem_Zv μ T V _ x v).1 hZ
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hV.le h1, ?_⟩, ?_⟩, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, h3]
    · refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun hw => ?_
      have hu : w.under (𝓞 F) ∉ insert q T.S := fun h => hw ((hPm w).2 h)
      have hS : w.under (𝓞 F) ∉ T.S := fun h => hu (Finset.mem_insert_of_mem h)
      obtain ⟨e1, e2⟩ := T.off w hS (fun h => hu (by rw [h]; exact Finset.mem_insert_self _ _))
      have hns : w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) := fun h => hS (Finset.mem_filter.1 h).1
      refine (mem_fixL' μ _ _ _).2 fun y hy => ?_
      rw [(mem_eigL' μ _ _ _ _).1 (h2 w hns) y (e1 ▸ hy), e2]
      simp
    · refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun _ => ?_
      by_cases hw : w ∈ Set.range f
      · obtain ⟨i, rfl⟩ := hw
        rw [hU1]
        exact (Submodule.mem_iInf _).1 hfx i
      · rw [hU2 w hw]
        refine (mem_fixL' μ _ _ _).2 fun y hy => ?_
        rw [(mem_eigL' μ _ _ _ _).1 (h2 w (hoff w hw)) y hy.1, hy.2, one_smul]
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.TrOnProdEigenProjectionsEqTrOnJointEigenspace
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma prj_mem' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (x : H) : prj M x ∈ M := by
  have h : M.topologicalClosure = M := hM.submodule_topologicalClosure_eq
  have h2 : prj M x ∈ M.topologicalClosure := Submodule.starProjection_apply_mem M.topologicalClosure x
  rwa [h] at h2

private lemma prj_orth' (M : Submodule ℂ H) (x : H) {y : H} (hy : y ∈ M) :
    ⟪x - prj M x, y⟫_ℂ = 0 :=
  (Submodule.mem_orthogonal' _ _).1
    (Submodule.sub_starProjection_mem_orthogonal (K := M.topologicalClosure) x) y
    (M.le_topologicalClosure hy)

private lemma prj_eq' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {u v : H} (hv : v ∈ M)
    (ho : ∀ y ∈ M, ⟪u - v, y⟫_ℂ = 0) : prj M u = v := by
  have h : M.topologicalClosure = M := hM.submodule_topologicalClosure_eq
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := M.topologicalClosure)
    (M.le_topologicalClosure hv) fun y hy => ho y (by rwa [h] at hy)

private lemma prj_self' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {v : H} (hv : v ∈ M) :
    prj M v = v :=
  prj_eq' hM hv fun y _ => by simp

private lemma comm_of_stable {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (B B' : H →L[ℂ] H)
    (hadj : ∀ x y, ⟪B x, y⟫_ℂ = ⟪x, B' y⟫_ℂ) (h1 : ∀ v ∈ M, B v ∈ M) (h2 : ∀ v ∈ M, B' v ∈ M) :
    Commute B (prj M) := by
  refine ContinuousLinearMap.ext fun x => ?_
  show B (prj M x) = prj M (B x)
  refine (prj_eq' hM (h1 _ (prj_mem' hM x)) fun y hy => ?_).symm
  rw [← map_sub, hadj]
  exact prj_orth' M x (h2 y hy)

private lemma hs_prj (W : Submodule ℂ H) [FiniteDimensional ℂ W] : IsHilbertSchmidt (prj W) := by
  have hcl := Submodule.closed_of_finiteDimensional W
  let e := stdOrthonormalBasis ℂ W
  have he : Orthonormal ℂ (fun k => ((e k : W) : H)) :=
    e.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  obtain ⟨s, b, hvs, hb⟩ := (he.toSubtypeRange).exists_hilbertBasis_extension
  have hbi : ∀ i, b i = (i : H) := fun i => congrFun hb i
  let f : Fin _ → s := fun k => ⟨(e k : H), hvs (Set.mem_range_self k)⟩
  have hf : Function.Injective f := fun k l h => by
    have : ((e k : W) : H) = (e l : W) := congrArg (fun z : s => (z : H)) h
    exact he.linearIndependent.injective this
  have hbf : ∀ k, b (f k) = (e k : H) := fun k => hbi _
  have hout : ∀ i, i ∉ Set.range f → prj W (b i) = 0 := fun i hi => by
    refine prj_eq' hcl W.zero_mem fun y hy => ?_
    have hy' : (y : H) = ∑ k, ⟪(e k : H), y⟫_ℂ • (e k : H) := by
      have h2 := congrArg Subtype.val (e.sum_repr' (⟨y, hy⟩ : W))
      simpa [Submodule.coe_sum] using h2.symm
    rw [sub_zero, hy', inner_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [inner_smul_right, ← hbf k]
    have : ⟪b i, b (f k)⟫_ℂ = 0 := b.orthonormal.2 fun h => hi ⟨k, h.symm⟩
    rw [this, mul_zero]
  rw [isHilbertSchmidt_iff b]
  have hs : Function.support (fun i => ‖prj W (b i)‖ₑ ^ 2) ⊆ Set.range f := fun i hi => by
    by_contra h
    exact hi (by simp [hout i h])
  rw [← hf.tsum_eq hs, tsum_fintype]
  exact ENNReal.sum_lt_top.2 fun k _ => ENNReal.pow_lt_top enorm_lt_top

private lemma pr_props (Z : Submodule ℂ H) : ∀ (r : ℕ) (E : Fin r → Submodule ℂ H),
    (∀ i, IsClosed (E i : Set H)) → (∀ i j, Commute (prj (E i)) (prj (E j))) →
    (∀ i, ∀ v ∈ Z, prj (E i) v ∈ Z) →
    (∀ u ∈ Z, (List.ofFn fun i => prj (E i)).prod u ∈ Z) ∧
    (∀ u, (List.ofFn fun i => prj (E i)).prod u ∈ ⨅ i, E i) ∧
    ∀ u, ∀ y ∈ ⨅ i, E i, ⟪u - (List.ofFn fun i => prj (E i)).prod u, y⟫_ℂ = 0 := by
  intro r
  induction r with
  | zero =>
    intro E _ _ _
    simp
  | succ r ih =>
    intro E hE hc hs
    obtain ⟨i1, i2, i3⟩ := ih (fun i => E i.succ) (fun i => hE _) (fun i j => hc _ _) (fun i => hs _)
    have hP : ∀ u, (List.ofFn fun i => prj (E i)).prod u =
        prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u) := fun u => by
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    refine ⟨fun u hu => ?_, fun u => ?_, fun u y hy => ?_⟩
    · rw [hP]
      exact hs 0 _ (i1 u hu)
    · rw [hP, Submodule.mem_iInf]
      refine Fin.cases (prj_mem' (hE 0) _) fun j => ?_
      have hx := Submodule.mem_iInf _ |>.1 (i2 u) j
      have h1 : prj (E j.succ) (prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) =
          prj (E 0) (prj (E j.succ) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) :=
        congrArg (fun T : H →L[ℂ] H => T ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) (hc j.succ 0).eq
      rw [prj_self' (hE _) hx] at h1
      rw [← h1]
      exact prj_mem' (hE _) _
    · rw [hP]
      have hy0 : y ∈ E 0 := (Submodule.mem_iInf _).1 hy 0
      have hys : y ∈ ⨅ i : Fin r, E i.succ := (Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).1 hy j.succ
      have e : u - prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u) =
          (u - (List.ofFn fun i : Fin r => prj (E i.succ)).prod u) +
          ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u -
            prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) := by abel
      rw [e, inner_add_left, i3 u y hys, prj_orth' _ _ hy0, add_zero]

private lemma tr_main {Z X Y : Submodule ℂ H} (Pr R : H →L[ℂ] H) [FiniteDimensional ℂ X] (hYX : Y ≤ X)
    (hXZ : X ≤ Z) (hR : ∀ v ∈ Z, R v ∈ Z) (h1 : ∀ u ∈ Z, Pr u ∈ Y)
    (h2 : ∀ u, ∀ y ∈ Y, ⟪u - Pr u, y⟫_ℂ = 0) : trOn X (Pr ∘L R) = trOn Y R := by
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYX
  have hXc := Submodule.closed_of_finiteDimensional X
  have hYc := Submodule.closed_of_finiteDimensional Y
  have e1 : prj X ∘L (Pr ∘L R) ∘L prj X = prj Y ∘L (R ∘L prj X) := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hx : R (prj X v) ∈ Z := hR _ (hXZ (prj_mem' hXc v))
    show prj X (Pr (R (prj X v))) = prj Y (R (prj X v))
    rw [prj_self' hXc (hYX (h1 _ hx)), prj_eq' hYc (h1 _ hx) (h2 _)]
  have e2 : (R ∘L prj X) ∘L prj Y = R ∘L prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    show R (prj X (prj Y v)) = R (prj Y v)
    rw [prj_self' hXc (hYX (prj_mem' hYc v))]
  have e3 : (R ∘L prj Y) ∘L prj Y = R ∘L prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    show R (prj Y (prj Y v)) = R (prj Y v)
    rw [prj_self' hYc (prj_mem' hYc v)]
  have e4 : prj Y ∘L prj Y = prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact prj_self' hYc (prj_mem' hYc v)
  have hT : IsTraceClass (prj Y) := by
    have := isTraceClass_comp (hs_prj Y) (hs_prj Y)
    rwa [show (prj Y).comp (prj Y) = prj Y from e4] at this
  unfold trOn
  rw [e1]
  have a := trace_comp_comm hT (R ∘L prj X)
  have b := trace_comp_comm hT (R ∘L prj Y)
  calc trace (prj Y ∘L R ∘L prj X) = trace ((R ∘L prj X) ∘L prj Y) := a.symm
    _ = trace ((R ∘L prj Y) ∘L prj Y) := by rw [e2, e3]
    _ = trace (prj Y ∘L R ∘L prj Y) := b

end Hilbert

theorem UpperTheory.trOn_prod_eigenProjections_eq_trOn_joint_eigenspace :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (Z : Submodule ℂ (LL μ))
        (r : ℕ) (w : Fin r → Pl K), Function.Injective w → ∀ (J : ∀ i, Subgroup (Gw n (w i))) (χ : ∀ i, Gw n (w i) → ℂ)
        (hc : ∀ i, IsChr (J i) (χ i)) (R : LL μ →L[ℂ] LL μ), (∀ i, CO (J i)) → IsClosed (Z : Set (LL μ)) →
        (∀ i g, ∀ v ∈ Z, rhoL μ (w i) g v ∈ Z) → (∀ v ∈ Z, R v ∈ Z) →
        FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixL μ (w i) (kerChr (J i) (χ i) (hc i))) →
        trOn (Z ⊓ ⨅ i, fixL μ (w i) (kerChr (J i) (χ i) (hc i))) ((List.ofFn fun i => prj (eigL μ (w i) (J i) (χ i))).prod ∘L R) =
          trOn (Z ⊓ ⨅ i, eigL μ (w i) (J i) (χ i)) R := by
  intro K _ _ n μ _ Z r w hw J χ hc R hCO hZ hst hR hfd
  have hB := fun i => UpperTheory.ConvolutionTheory.L1.eigBasic K n μ (w i) (J i) (χ i) (hCO i) (hc i)
  have hF := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have hmul : ∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h' := hF.2.2.2.2.2.1
  have hadjF : ∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹ := hF.2.2.2.2.2.2.2.1
  have hadj : ∀ (u : Pl K) g x y, ⟪rhoL μ u g x, y⟫_ℂ = ⟪x, rhoL μ u g⁻¹ y⟫_ℂ := fun u g x y => by
    have : rhoL μ u g⁻¹ = ContinuousLinearMap.adjoint (rhoL μ u g) := by
      unfold rhoL
      rw [hadjF, map_inv]
    rw [this, ContinuousLinearMap.adjoint_inner_right]
  have hcomZ : ∀ i, Commute (prj Z) (prj (eigL μ (w i) (J i) (χ i))) := fun i =>
    (hB i).2.2.2 (prj Z) fun x _ =>
      (comm_of_stable hZ (rhoL μ (w i) x) (rhoL μ (w i) x⁻¹) (hadj _ x) (hst i x) (hst i x⁻¹)).symm
  have hs : ∀ i, ∀ v ∈ Z, prj (eigL μ (w i) (J i) (χ i)) v ∈ Z := fun i v hv => by
    have h1 : prj Z (prj (eigL μ (w i) (J i) (χ i)) v) = prj (eigL μ (w i) (J i) (χ i)) (prj Z v) :=
      congrArg (fun T : LL μ →L[ℂ] LL μ => T v) (hcomZ i).eq
    rw [prj_self' hZ hv] at h1
    rw [← h1]
    exact prj_mem' hZ _
  have hrho : ∀ i j, i ≠ j → ∀ x y, Commute (rhoL μ (w j) x) (rhoL μ (w i) y) := fun i j hij x y => by
    have hne : w i ≠ w j := fun h => hij (hw h)
    have := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w j)).2.2.2.1 (w i) hne x y
    show rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _
    rw [← hmul, ← hmul, this]
  have hcom : ∀ i j, Commute (prj (eigL μ (w i) (J i) (χ i))) (prj (eigL μ (w j) (J j) (χ j))) := fun i j => by
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact (hB j).2.2.2 _ fun x _ => ((hB i).2.2.2 _ fun y _ => hrho i j hij x y).symm
  obtain ⟨p1, p2, p3⟩ := pr_props Z r (fun i => eigL μ (w i) (J i) (χ i)) (fun i => (hB i).1) hcom hs
  have hle : ∀ i, eigL μ (w i) (J i) (χ i) ≤ fixL μ (w i) (kerChr (J i) (χ i) (hc i)) := fun i v hv => by
    refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 v).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 : rhoL μ (w i) x v = χ i x • v := by
      simpa [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus] using
        (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv x) hx.1
    have h2 : χ i x = 1 := hx.2
    rw [h2, one_smul] at h1
    exact h1
  refine tr_main (Z := Z) _ R (inf_le_inf_left Z (iInf_mono hle)) inf_le_left hR
    (fun u hu => Submodule.mem_inf.2 ⟨p1 u hu, p2 u⟩) fun u y hy => p3 u y (Submodule.mem_inf.1 hy).2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistFactorAlt
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.ConvolutionTheory.C.twistFactor :
    UpperTheory.ConvolutionTheory.C.TwistFactor := by
  intro K _ _ n μ _ V Z r w _ _ τ s I R hV hw hτ hZV hZ0 hZi hadm hRZ hRs hI
  classical
  have hfix : ∀ U : ∀ i, Subgroup (Gw n (w i)),
      (Z ⊓ ⨅ i, fixU (locU μ (w i)) (U i)) = Z ⊓ ⨅ i, fixL μ (w i) (U i) := fun U => by
    simp only [fixU_locU]
  have hinv : ∀ i, (locU μ (w i)).IsInvariant Z := fun i g v hv => hZi i g v hv
  have hcomm : ∀ i j, i ≠ j → ∀ (g : Gw n (w i)) (h : Gw n (w j)) v,
      locU μ (w i) g (locU μ (w j) h v) = locU μ (w j) h (locU μ (w i) g v) := by
    intro i j hij g h v
    have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).2.2.2.1 (w j) (fun e => hij (hw e.symm)) g h
    let ρ := (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom
      (MultiplicityOne.finProj K n) (MultiplicityOne.continuous_finProj (K := K) (n := n))
    change ρ (AdelicGLn.localEmbedding (w i) g) (ρ (AdelicGLn.localEmbedding (w j) h) v) =
      ρ (AdelicGLn.localEmbedding (w j) h) (ρ (AdelicGLn.localEmbedding (w i) g) v)
    simp only [← UnitaryRep.map_mul_apply, hc]
  obtain ⟨c, hc⟩ := UpperTheory.isotypic_multiplicity_tensor_product r (fun i => Gw n (w i)) (LL μ) (fun i => (τ i).V) (fun i => locU μ (w i))
    (fun i => (τ i).ρ) V Z (fun i => (τ i).smooth) (fun i => (τ i).irred) hcomm hZ0 hZV hinv
    (fun i => UpperTheory.summand_le_closure_span_local_type_images K n μ V (w i) (τ i) hV (hτ i)) (fun U hU => by rw [hfix]; exact hadm U hU)
    s I R hRZ (fun i g v hv => hRs i g v hv) hI
  refine ⟨c, ?_⟩
  intro U m φ T t hU hm _ hφ hT ht
  choose A hA hAt using ht
  have hf := fun i => by
    haveI := hm i
    exact UpperTheory.integralOperator_fixed_invariant_of_left_invariant_kernel (Gw n (w i)) (LL μ) (τ i).V (locU μ (w i)) (τ i).ρ (m i) (φ i) (T i) (A i) (U i)
      (fun u v => hT i u v) (hA i) (hφ i)
  have hfin := hc U T A t hU (fun i v => (hf i).1 v) (fun i v hv => (hf i).2.2.1 Z hZ0 (hinv i) v hv)
    (fun i j hij h v => (hf i).2.2.2.1 (locU μ (w j) h)
      (fun g v => hcomm i j hij g h v)
      (fun g v => by rw [UnitaryRep.adjoint_map]; exact hcomm i j hij g h⁻¹ v) v)
    (fun i f hf' x => (hf i).2.2.2.2 f hf' x) (fun i x => (hf i).2.1 x) hAt
  rw [hfix] at hfin
  exact hfin
end

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C.TraceVanishing

private theorem hasFinTrace_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c : ℂ} (b : ℂ) (hb : b ≠ 0)
    (h : HasFinTrace A c) : HasFinTrace (b • A) (b * c) := by
  obtain ⟨hf, rfl⟩ := h
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (b • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((b • A).restrict h1) = b * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    intro R hR h1 h2
    subst hR
    have e : (b • A).restrict h1 = b • A.restrict h2 := rfl
    rw [e, map_smul, smul_eq_mul]
  have hr : LinearMap.range (b • A) = LinearMap.range A := LinearMap.range_smul _ _ hb
  exact ⟨by rw [hr]; exact hf, key _ hr _ _⟩

private theorem isInt_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {A : V →ₗ[ℂ] V} (d : ENNReal) (hdt : d ≠ ⊤)
    (hA : IsIntegralOp m ρ f A) : IsIntegralOp (d • m) ρ f ((d.toReal : ℂ) • A) := fun v l =>
  ⟨(hA v l).1.smul_measure hdt, by
    rw [integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]⟩

private theorem hasTw_smul {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] {m : Measure G} {τ : SmIrr G}
    {I : τ.V ≃ₗ[ℂ] τ.V} {φ : G → ℂ} {t : ℂ} (d : ENNReal) (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (h : HasTwTrace m τ I φ t) : HasTwTrace (d • m) τ I φ ((d.toReal : ℂ) * t) := by
  obtain ⟨B, hB, hF⟩ := h
  have hb : (d.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0, hdt⟩)
  refine ⟨(d.toReal : ℂ) • B, isInt_smul d hdt hB, ?_⟩
  have e : ((d.toReal : ℂ) • B) ∘ₗ (I : τ.V →ₗ[ℂ] τ.V) = (d.toReal : ℂ) • (B ∘ₗ (I : τ.V →ₗ[ℂ] τ.V)) := rfl
  rw [e]
  exact hasFinTrace_smul _ _ hb hF

private theorem exists_enum {α : Type} (A : Finset α) :
    ∃ (r : ℕ) (p : Fin r → α), Function.Injective p ∧ ∀ v, v ∈ A ↔ v ∈ Set.range p := by
  refine ⟨A.card, fun i => (A.equivFin.symm i).1, Subtype.val_injective.comp A.equivFin.symm.injective,
    fun v => ⟨fun hv => ⟨A.equivFin ⟨v, hv⟩, by simp⟩, ?_⟩⟩
  rintro ⟨i, rfl⟩
  exact (A.equivFin.symm i).2

private theorem test_ind {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J : Subgroup G} (hJ : CO J)
    {χ : G → ℂ} (hχ : IsChr J χ) : Test ((J : Set G).indicator fun x => conj (χ x)) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_,
    HasCompactSupport.intro hJ.1 fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (J : Set G)
  · filter_upwards [hJ.2.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hχ.1 x] with y hy hy2
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hy2]
  · have hcl : IsClosed (J : Set G) := Subgroup.isClosed_of_isOpen J hJ.2
    filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem ker_co {G : Type} [Group G] [TopologicalSpace G] {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (h : IsChr J χ) :
    CO (kerChr J χ h) := by
  have e : (kerChr J χ h : Set G) = (J : Set G) ∩ χ ⁻¹' {1} := rfl
  have ho : IsOpen (χ ⁻¹' {(1 : ℂ)}) := h.1.isOpen_fiber 1
  have hc : IsClosed (χ ⁻¹' {(1 : ℂ)}) := isClosed_singleton.preimage h.1.continuous
  rw [CO, e]
  exact ⟨hJ.1.inter_right hc, hJ.2.inter ho⟩

private theorem ker_inv {G : Type} [Group G] [TopologicalSpace G] {J : Subgroup G} {χ : G → ℂ} (h : IsChr J χ)
    (u : G) (hu : u ∈ kerChr J χ h) (g : G) :
    (J : Set G).indicator (fun x => conj (χ x)) (u * g) = (J : Set G).indicator (fun x => conj (χ x)) g := by
  obtain ⟨h1, h2⟩ : u ∈ J ∧ χ u = 1 := hu
  by_cases hg : g ∈ J
  · rw [Set.indicator_of_mem (by exact J.mul_mem h1 hg), Set.indicator_of_mem (by exact hg), h.2.2 u h1 g hg, h2, one_mul]
  · have : u * g ∉ J := fun hh => hg ((Subgroup.mul_mem_cancel_left J h1).1 hh)
    rw [Set.indicator_of_notMem (by exact this), Set.indicator_of_notMem (by exact hg)]

section Hil
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_mem' {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have h : prj V v ∈ V.topologicalClosure := Submodule.starProjection_apply_mem V.topologicalClosure v
  rwa [hc] at h

private theorem prj_self' {V : Submodule ℂ H} {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)

private theorem mem_eigIn' {W : Submodule ℂ H} {A : H →L[ℂ] H} {x : ℝ} {v : H} :
    v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp [eigIn, Module.End.mem_eigenspace_iff]

private theorem trOn_congr {Y : Submodule ℂ H} (hY : IsClosed (Y : Set H)) {A B : H →L[ℂ] H} (h : ∀ v ∈ Y, A v = B v) :
    trOn Y A = trOn Y B := by
  unfold trOn
  congr 1
  ext1 v
  simp only [ContinuousLinearMap.comp_apply]
  rw [h _ (prj_mem' hY v)]

end Hil

section Ops
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

private theorem oloc_comm {w : Pl K} [MeasurableSpace (Gw n w)] {m : Measure (Gw n w)} {ψ : Gw n w → ℂ}
    {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (R : LL μ →L[ℂ] LL μ) (hR : ∀ g, Commute R (rhoL μ w g)) :
    Commute R Bo := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  show ⟪u, R (Bo v)⟫_ℂ = ⟪u, Bo (R v)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left R, h, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ g * _
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hR g).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [this]

private theorem mem_eigL' {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {v : LL μ} :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem mem_fixL' {w : Pl K} {J : Subgroup (Gw n w)} {v : LL μ} :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply,
    Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]

private theorem isClosed_fixL (w : Pl K) (J : Subgroup (Gw n w)) : IsClosed (fixL μ w J : Set (LL μ)) := by
  simp only [fixL, fixF, Submodule.coe_iInf]
  exact isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_eq (rhoF μ u).continuous continuous_id

private theorem eigL_comm {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} (O : LL μ →L[ℂ] LL μ)
    (h : ∀ g, Commute O (rhoL μ w g)) {v : LL μ} (hv : v ∈ eigL μ w J χ) : O v ∈ eigL μ w J χ := by
  rw [mem_eigL'] at hv ⊢
  intro x hx
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (h x).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [← this, hv x hx, map_smul]

private theorem fixL_comm {w : Pl K} {J : Subgroup (Gw n w)} (O : LL μ →L[ℂ] LL μ)
    (h : ∀ g, Commute O (rhoL μ w g)) {v : LL μ} (hv : v ∈ fixL μ w J) : O v ∈ fixL μ w J := by
  rw [mem_fixL'] at hv ⊢
  intro x hx
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (h x).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [← this, hv x hx]

private theorem oinf_comm (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n) (C : LL μ →L[ℂ] LL μ)
    (h : ∀ g, Commute C (rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n g))) : Commute C (Oinf μ ν a) := by
  have key : C ∘L Oinf μ ν a = Oinf μ ν a ∘L C := by
    refine UnitaryRep.comp_integrated_of_mem_intertwiners _ _ ?_ _
    intro x u
    exact DFunLike.congr_fun (h x).eq u
  exact key

private theorem oinf_congr {ν₁ ν₂ : Measure (archGroup K n)} [ν₁.IsHaarMeasure] [ν₂.IsHaarMeasure] (h : ν₁ = ν₂) (β : TI K n) :
    Oinf μ ν₁ β = Oinf μ ν₂ β := by
  subst h; rfl

end Ops

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem under_over' {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem cmp_surj {v : Pl F} (w : PlacesOver E v) (h : ∀ u : PlacesOver E v, u = w) :
    Function.Surjective (GM.cmp (n := n) w) := by
  have hev : Function.Bijective (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) := by
    letI : Unique (PlacesOver E v) := ⟨⟨w⟩, h⟩
    constructor
    · intro a b e
      funext u
      obtain rfl := h u
      exact e
    · intro z
      refine ⟨fun u => (h u).symm ▸ z, ?_⟩
      show ((h w).symm ▸ z : (w.1.adicCompletion E)) = z
      rfl
  let e := RingEquiv.ofBijective _ hev
  intro y
  refine ⟨mapGL n (e.symm : _ →+* _) y, ?_⟩
  exact Units.ext (Matrix.ext fun a b => e.apply_symm_apply _)

variable {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q}

private theorem gal_eq {v : Pl F} (w : PlacesOver E v) (h : ∀ u : PlacesOver E v, u = w) {a b : Gw n w.1 →* Gw n w.1}
    (ha : IsLocGal σ w a) (hb : IsLocGal σ w b) (x : Gw n w.1) : a x = b x := by
  obtain ⟨g, rfl⟩ := cmp_surj w h x
  rw [← ha, ← hb]

private theorem stabV (T : Ty σ n q w₀) (v : Pl F) (h : ∀ u : PlacesOver E v, u = T.mk' v)
    {a : Gw n (T.mk' v).1 →* Gw n (T.mk' v).1} (ha : IsLocGal σ (T.mk' v) a) (x : Gw n (T.mk' v).1) (hx : x ∈ T.J (T.mk' v).1) :
    a x ∈ T.J (T.mk' v).1 ∧ T.χ (T.mk' v).1 (a x) = T.χ (T.mk' v).1 x := by
  obtain ⟨g, rfl⟩ := cmp_surj (T.mk' v) h x
  letI : Unique (PlacesOver E v) := ⟨⟨T.mk' v⟩, h⟩
  have hall : ∀ u : PlacesOver E v, GM.cmp u g ∈ T.J u.1 := fun u => by
    obtain rfl := h u
    exact hx
  obtain ⟨h1, h2⟩ := T.stable v g hall
  rw [finprod_unique, finprod_unique] at h2
  have e : (default : PlacesOver E v) = T.mk' v := rfl
  rw [e] at h2
  rw [← ha]
  exact ⟨h1 _, h2⟩

end Loc

end UpperTheory.ConvolutionTheory.C.TraceVanishing

open UpperTheory.ConvolutionTheory.C.TraceVanishing in
set_option maxHeartbeats 3200000 in
theorem UpperTheory.ConvolutionTheory.C.termEV :
    UpperTheory.ConvolutionTheory.C.TermEV := by
  classical
  intro F E _ _ _ _ _ _ σ hgen k n hk hpr hn μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF harch _ _ m hm q w₀ hq T V hV hVθ
    hrk τ₀ τ g I hocc₀ hocc hI y hy
  have hprime : (Module.finrank F E).Prime := hk ▸ hpr
  have hx : (0 : ℝ) < y ^ (k + 1) := pow_pos hy _
  have hns : ∀ v ∈ nsS T, v ∈ T.S ∧ ¬ GM.Split E v := fun v hv => Finset.mem_filter.1 hv
  have hU : ∀ v ∈ nsS T, ∀ u : PlacesOver E v, u = T.mk' v := fun v hv =>
    (UpperTheory.ConvolutionTheory.C.locGalEx F E σ hprime n v (T.mk' v) (hns v hv).2).1
  obtain ⟨r₁, p₁, hp₁, hpr₁⟩ := exists_enum T.sp
  obtain ⟨r₂, p₂, hp₂, hpr₂⟩ := exists_enum (nsS T)
  have hm₁ : ∀ i, p₁ i ∈ T.sp := fun i => (hpr₁ _).2 ⟨i, rfl⟩
  have hm₂ : ∀ i, p₂ i ∈ nsS T := fun i => (hpr₂ _).2 ⟨i, rfl⟩

  have h0 : ∀ u, m u (T.J u) ≠ 0 := fun u => by
    haveI := hm u
    exact ((T.co u).2.measure_pos (m u) ⟨1, Subgroup.one_mem _⟩).ne'
  have ht : ∀ u, m u (T.J u) ≠ ⊤ := fun u => by
    haveI := hm u
    exact (T.co u).1.measure_lt_top.ne
  have hd0 : ∀ u, (m u (T.J u))⁻¹ ≠ 0 := fun u => ENNReal.inv_ne_zero.2 (ht u)
  have hdt : ∀ u, (m u (T.J u))⁻¹ ≠ ⊤ := fun u => ENNReal.inv_ne_top.2 (h0 u)
  let mm : ∀ u : Pl E, Measure (Gw n u) := fun u => (m u (T.J u))⁻¹ • m u
  let bb : Pl E → ℂ := fun u => (((m u (T.J u))⁻¹.toReal : ℝ) : ℂ)
  have hmmH : ∀ u, (mm u).IsHaarMeasure := fun u => by
    haveI := hm u
    exact Measure.IsHaarMeasure.smul _ (hd0 u) (hdt u)
  have hmm1 : ∀ u, mm u (T.J u) = 1 := fun u => by
    show ((m u (T.J u))⁻¹ • m u) (T.J u) = 1
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (h0 u) (ht u)]
  have hbb : ∀ u, bb u ≠ 0 := fun u => Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0 u, hdt u⟩)
  set x : ℝ := y ^ (k + 1) with hxd
  set Oa := Oinf μ νE aE with hOa
  set O : Fin (k + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a with hO

  obtain ⟨κ, hκ, hK⟩ := UpperTheory.exists_pos_const_eigenspace_bound_of_split_CMDatum F E σ n hn μ νE aE q w₀ hq T hU
  obtain ⟨c₀, hc₀, hTY⟩ := (UpperTheory.ConvolutionTheory.L1.twistY F E σ hgen k n hk hn μ θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq T V hV hVθ
    (fun v hv hs' u => (hrk v hv hs' u).1)).2 y hy
  obtain ⟨c₁, hc₁, hval⟩ := UpperTheory.archimedean_baseChange_trace_comparison F E σ k n hn μ D s hs hposition νF a m hm q w₀ hq T V hV τ₀ τ hocc₀
    (fun v hv => hocc v (Finset.mem_filter.1 hv).1) y hy mm (fun _ => rfl) r₁ p₁ hp₁ hpr₁
  obtain ⟨hθO, hθP⟩ := UpperTheory.galoisTwist_commute_archOperator_and_offProjection F E σ hgen k n μ θ hθ D s hs hposition νE νF b a aE aF harch q w₀ T
  let w : Fin r₂ → Pl E := fun i => (T.mk' (p₂ i)).1
  have hwinj : Function.Injective w := fun i j h => hp₂ (by
    have e : (T.mk' (p₂ i)).1 = (T.mk' (p₂ j)).1 := h
    rw [← under_over' (T.mk' (p₂ i)), e, under_over'])
  have hwm : ∀ i, w i ∉ T.marked := by
    rintro i (h | ⟨v, hv, h⟩)
    · have h1 : p₂ i = q := by
        rw [← under_over' (T.mk' (p₂ i)), show (T.mk' (p₂ i)).1 = w₀.1 from h, under_over']
      exact T.q_not (h1 ▸ (hns _ (hm₂ i)).1)
    · have h1 : p₂ i = v := by
        rw [← under_over' (T.mk' (p₂ i)), show (T.mk' (p₂ i)).1 = (T.mk' v).1 from h, under_over']
      exact (hns _ (hm₂ i)).2 (h1 ▸ (Finset.mem_filter.1 hv).2)
  obtain ⟨hZc, hZs, hZa⟩ := UpperTheory.finiteDimensional_eigenspace_inf_fixed_offN_CMDatum F E σ n hn μ νE aE q w₀ T V hV hU x hx.ne'
  set Z := eigIn (V ⊓ offN μ T) (Oinf μ νE aE) x with hZd
  have hZV : Z ≤ V := fun f hf => (mem_eigIn'.1 hf).1.1
  have hZo : Z ≤ offN μ T := fun f hf => (mem_eigIn'.1 hf).1.2
  have hoffc : IsClosed (offN μ T : Set (LL μ)) := by
    simp only [offN, Submodule.coe_iInf]
    exact isClosed_iInter fun w => isClosed_iInter fun _ => (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w _ _ (T.co w) (T.chr w)).1
  have hθV : ∀ f ∈ V, θ.U f ∈ V := fun f hf => by
    rw [← hVθ]
    exact Submodule.mem_map_of_mem hf
  have hθZ : ∀ f ∈ Z, θ.U f ∈ Z := fun f hf => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := mem_eigIn'.1 hf
    refine mem_eigIn'.2 ⟨⟨hθV f h1, ?_⟩, ?_⟩
    · have := congrArg (fun S : LL μ →L[ℂ] LL μ => S f) hθP.eq
      simp only [ContinuousLinearMap.mul_apply, prj_self' h2] at this
      rw [this]
      exact TraceVanishing.prj_mem' hoffc _
    · have := congrArg (fun S : LL μ →L[ℂ] LL μ => S f) hθO.eq
      simp only [ContinuousLinearMap.mul_apply] at this
      rw [← this, h3, map_smul]
  choose s' hs1 hs2 using fun i => (UpperTheory.ConvolutionTheory.C.locGalEx F E σ hprime n (p₂ i) (T.mk' (p₂ i)) (hns _ (hm₂ i)).2).2
  have hθs : ∀ i g f, θ.U (rhoL μ (w i) g f) = rhoL μ (w i) (s' i g) (θ.U f) := fun i => ((hs2 i) μ θ hθ).1
  have hIs : ∀ i x y, I (p₂ i) ((τ (p₂ i)).ρ x y) = (τ (p₂ i)).ρ (s' i x) (I (p₂ i) y) := fun i x y => by
    have hv := hns _ (hm₂ i)
    have h := hI _ hv.1 hv.2
    have e := gal_eq (T.mk' (p₂ i)) (hU _ (hm₂ i)) h.1 (hs1 i) x
    have e' : (s' i : Gw n (T.mk' (p₂ i)).1 →* Gw n (T.mk' (p₂ i)).1) x = s' i x := rfl
    rw [h.2 x y, e, e']
  have ht0 : ∀ i, ∃ t : ℂ, t ≠ 0 ∧ HasTwTrace (mm (w i)) (τ (p₂ i)) (I (p₂ i))
      ((T.J (w i) : Set (Gw n (w i))).indicator fun x => conj (T.χ (w i) x)) t := by
    intro i
    have hv := hns _ (hm₂ i)
    obtain ⟨h1, h2⟩ := hrk _ hv.1 hv.2 (T.mk' (p₂ i))
    haveI := hmmH (w i)
    obtain ⟨e, he0, he1, he2⟩ := UpperTheory.exists_unique_eigenline_of_rankOne_occurs E n μ V hV (w i) (τ (p₂ i)) (hocc _ hv.1) (T.J (w i)) (T.χ (w i))
      (T.co _) (T.chr _) h1 h2
    obtain ⟨-, -, h3⟩ := UpperTheory.ConvolutionTheory.C.occursBasics E n μ V (w i) (mm (w i)) hV
    obtain ⟨_, A, hA, -⟩ := h3 (τ (p₂ i)) (hocc _ hv.1) _ (test_ind (T.co (w i)) (T.chr (w i)))
    exact UpperTheory.integralOp_eigenline_scalar_of_twist (Gw n (w i)) (mm (w i)) (τ (p₂ i)) (I (p₂ i)) (g (p₂ i)) (T.J (w i)) (T.χ (w i)) A e (T.co _) (T.chr _)
      (hmm1 _) hA he0 he1 he2 (stabV T _ (hU _ (hm₂ i)) (hI _ hv.1 hv.2).1) (hI _ hv.1 hv.2).2
  choose t0 ht0n ht0t using ht0
  have hP0 : ∏ i, t0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht0n i
  have hZ0 : Z ⊓ ⨅ i, eigL μ (w i) (T.J (w i)) (T.χ (w i)) = eigIn (V ⊓ T.typed μ) (Oinf μ νE aE) x := by
    ext f
    simp only [Submodule.mem_inf, Submodule.mem_iInf, hZd, mem_eigIn', offN, Ty.typed]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      refine ⟨⟨h1, fun u => ?_⟩, h3⟩
      by_cases hu : u.under (𝓞 F) ∈ (nsS T : Set (Pl F))
      · obtain ⟨i, hi⟩ := (hpr₂ _).1 hu
        have e : (⟨u, ⟨rfl⟩⟩ : PlacesOver E (u.under (𝓞 F))) = T.mk' (u.under (𝓞 F)) := hU _ hu _
        have e2 : u = w i := by
          show u = (T.mk' (p₂ i)).1
          rw [hi]
          exact congrArg Subtype.val e
        rw [e2]
        exact h4 i
      · exact h2 u hu
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨h1, fun u _ => h2 u⟩, h3⟩, fun i => h2 _⟩
  refine ⟨(κ : ℂ) * x * c₀ * c₁ * (∏ i, bb (w i)) * (∏ i, t0 i)⁻¹, fun hz => ?_, ?_⟩
  · have h1 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have h2 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) hc₀) (hc₁ hz))
      (Finset.prod_ne_zero_iff.2 fun i _ => hbb _)) (inv_ne_zero hP0)
  intro L ψ hfit e l 𝔢 he hsd j sq t hsq htS htN
  obtain ⟨hν, ha, -, hUl, hg, hUq⟩ := hsd
  have hψ₁ : ∀ v ∈ T.sp, Test (ψ v) ∧ ∀ u ∈ T.J (T.mk' v).1, ∀ g, ψ v (u * g) = ψ v g := fun v hv =>
    ⟨hfit.test v (Finset.mem_filter.1 hv).1, fun u hu g => (hfit.inv v hv u hu g).1⟩
  have hB₁ : ∀ i, ∃ B, IsOloc μ (T.mk' (p₁ i)).1 (mm _) (ψ (p₁ i)) B := fun i => by
    haveI := hmmH (T.mk' (p₁ i)).1
    exact (UpperTheory.ConvolutionTheory.C.olocEx E n μ _ (mm _) (ψ (p₁ i)) (hfit.test _ (Finset.mem_filter.1 (hm₁ i)).1)).exists
  have hB₂ : ∀ i, ∃ B, IsOloc μ (T.mk' (p₂ i)).1 (mm _) (ψ (p₂ i)) B := fun i => by
    haveI := hmmH (T.mk' (p₂ i)).1
    exact (UpperTheory.ConvolutionTheory.C.olocEx E n μ _ (mm _) (ψ (p₂ i)) (hfit.test _ (hns _ (hm₂ i)).1)).exists
  choose B₁ hB₁ using hB₁
  choose B₂ hB₂ using hB₂
  have hmmA : ∀ u, (mm u).IsHaarMeasure ∧ mm u (T.J u) = 1 := fun u => ⟨hmmH u, hmm1 u⟩
  obtain ⟨hCa, hCr, hCo, hCV⟩ := UpperTheory.heckeOperator_summand_weight_CMDatum F E σ n μ q w₀ hq T V hV e j r₁ p₁ hm₁ mm hmmA ψ (fun i => hψ₁ _ (hm₁ i)) B₁ hB₁
  obtain ⟨-, hDr, hDo, -⟩ := UpperTheory.heckeOperator_summand_weight_CMDatum F E σ n μ q w₀ hq T V hV e 0 r₁ p₁ hm₁ mm hmmA ψ (fun i => hψ₁ _ (hm₁ i)) B₁ hB₁
  have hD1 : (Uiw μ w₀.1 e ^ 0) ∘L (List.ofFn B₁).prod = (List.ofFn B₁).prod := by
    ext1 f
    simp
  rw [hD1] at hDr hDo
  set C := (Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B₁).prod with hCd
  have hCO : Commute C (Oinf μ νE aE) := oinf_comm μ νE aE C hCa
  have hRZ : ∀ f ∈ Z, (C ∘L θ.U) f ∈ Z := fun f hf => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := mem_eigIn'.1 (hθZ f hf)
    refine mem_eigIn'.2 ⟨⟨hCV _ h1, hCo _ h2⟩, ?_⟩
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S (θ.U f)) hCO.eq
    simp only [ContinuousLinearMap.mul_apply] at this
    show Oinf μ νE aE (C (θ.U f)) = (x : ℂ) • C (θ.U f)
    rw [← this, h3, map_smul]
  have hRs : ∀ i g, ∀ f ∈ Z, (C ∘L θ.U) (rhoL μ (w i) g f) = rhoL μ (w i) (s' i g) ((C ∘L θ.U) f) := fun i g f _ => by
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S (θ.U f)) (hCr _ (hwm i) (s' i g)).eq
    simp only [ContinuousLinearMap.mul_apply] at this
    show C (θ.U (rhoL μ (w i) g f)) = rhoL μ (w i) (s' i g) (C (θ.U f))
    rw [hθs, this]
  obtain ⟨cR, hTF⟩ := UpperTheory.ConvolutionTheory.C.twistFactor E n μ V Z r₂ w (fun i => τ (p₂ i)) s' (fun i => I (p₂ i)) (C ∘L θ.U) hV hwinj
    (fun i => hocc _ (hns _ (hm₂ i)).1) hZV hZc (fun i g f hf => hZs _ (hm₂ i) g f hf)
    (fun U hUc => hZa r₂ p₂ hp₂ hpr₂ U hUc) hRZ hRs hIs
  have hcr : cR * ∏ i, t0 i = c₀ * (c₁ * sq * ∏ v ∈ T.sp, t v) := by
    have e1 := hTF (fun i => kerChr (T.J (w i)) (T.χ (w i)) (T.chr _)) (fun i => mm (w i))
      (fun i => (T.J (w i) : Set (Gw n (w i))).indicator fun x => conj (T.χ (w i) x))
      (fun i => prj (eigL μ (w i) (T.J (w i)) (T.χ (w i)))) t0 (fun i => ker_co (T.co _) (T.chr _)) (fun i => hmmH _)
      (fun i => test_ind (T.co _) (T.chr _)) (fun i => ker_inv (T.chr _))
      (fun i => by
        haveI := hmmH (w i)
        exact (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ (w i) _ _ (T.co _) (T.chr _)).2.2.1 (mm (w i)) (hmm1 _)) ht0t
    have e2 := UpperTheory.trOn_prod_eigenProjections_eq_trOn_joint_eigenspace E n μ Z r₂ w hwinj (fun i => T.J (w i)) (fun i => T.χ (w i)) (fun i => T.chr _) (C ∘L θ.U)
      (fun i => T.co _) hZc (fun i g f hf => hZs _ (hm₂ i) g f hf) hRZ
      (hZa r₂ p₂ hp₂ hpr₂ _ fun i => ker_co (T.co _) (T.chr _))
    have e3 := hTY C hCa hCr
    have e4 := hval ψ hψ₁ e he j sq t hsq htS B₁ hB₁
    rw [← e1, e2, hZ0, e3, e4]

  have hAeq : 𝔢.toAmp.A = Oinf μ νE aE ∘L prj (fixF μ (GM.levE L.UE)) := by
    show Oinf μ 𝔢.ν 𝔢.a₀ ∘L prj (fixF μ 𝔢.U) = _
    rw [ha, hUl, oinf_congr μ hν]
  have hpos : 0 ≤ Oinf μ νE aE := by
    have := 𝔢.pos
    rwa [ha, oinf_congr μ hν] at this
  have hOsa : ContinuousLinearMap.adjoint (Oinf μ νE aE) = Oinf μ νE aE :=
    (IsSelfAdjoint.of_nonneg hpos).adjoint_eq
  have hOF : ∀ h, Commute (Oinf μ νE aE) (rhoF μ h) := fun h =>
    (UpperTheory.ConvolutionTheory.Tf.opAlg E n μ νE MeasureTheory.Measure.haar).2.2.2.2.2.2.2.2 aE h
  have hcp := UpperTheory.ConvolutionTheory.Tf.commPrj E n μ (GM.levE L.UE)
  have hOFx : ∀ v ∈ fixF μ (GM.levE L.UE), Oinf μ νE aE v ∈ fixF μ (GM.levE L.UE) := by
    intro v hv
    refine (hcp.2.1 _).2 fun u hu => ?_
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hOF u).eq
    simp only [ContinuousLinearMap.mul_apply, (hcp.2.1 v).1 hv u hu] at this
    exact this.symm
  obtain ⟨hlc, hlψ, hle⟩ := UpperTheory.eigenspace_factorization_over_nonsplit_places_CMDatum F E σ n q w₀ hq μ T L ψ hfit hU r₂ p₂ hpr₂
  obtain ⟨hNf, hNo⟩ := UpperTheory.prod_localOperators_mem_fixed_and_offN_CMDatum F E σ n μ q w₀ T r₂ p₂ hp₂ hm₂ mm hmmH ψ (fun i => lvN T L (p₂ i)) hlψ B₂ hB₂
  set FN : Submodule ℂ (LL μ) := ⨅ i, fixL μ (T.mk' (p₂ i)).1 (lvN T L (p₂ i)) with hFN
  have hFNc : IsClosed (FN : Set (LL μ)) := by
    rw [hFN, Submodule.coe_iInf]
    exact isClosed_iInter fun i => isClosed_fixL μ _ _
  have hTc : IsClosed ((offN μ T ⊓ FN : Submodule ℂ (LL μ)) : Set (LL μ)) := by
    rw [Submodule.coe_inf]
    exact hoffc.inter hFNc
  have hcomm : ∀ O' : LL μ →L[ℂ] LL μ, (∀ u g, Commute O' (rhoL μ u g)) → ∀ f ∈ offN μ T ⊓ FN, O' f ∈ offN μ T ⊓ FN := by
    intro O' hO' f hf
    obtain ⟨a1, a2⟩ := Submodule.mem_inf.1 hf
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · simp only [offN, Submodule.mem_iInf] at a1 ⊢
      exact fun u hu => eigL_comm μ O' (hO' u) (a1 u hu)
    · rw [hFN, Submodule.mem_iInf] at a2 ⊢
      exact fun i => fixL_comm μ O' (hO' _) (a2 i)
  have hmk : ∀ (P : LL μ →L[ℂ] LL μ), (∀ f ∈ offN μ T, P f ∈ offN μ T) → (∀ u ∉ T.marked, ∀ g, Commute P (rhoL μ u g)) →
      ∀ f ∈ offN μ T ⊓ FN, P f ∈ offN μ T ⊓ FN := by
    intro P h1 h2 f hf
    obtain ⟨a1, a2⟩ := Submodule.mem_inf.1 hf
    refine Submodule.mem_inf.2 ⟨h1 f a1, ?_⟩
    rw [hFN, Submodule.mem_iInf] at a2 ⊢
    exact fun i => fixL_comm μ P (h2 _ (hwm i)) (a2 i)
  have hVc : IsClosed (V : Set (LL μ)) := IsSummandOf.closed hV
  have hS : ∀ f, ((List.ofFn B₁).prod ∘L (List.ofFn B₂).prod ∘L prj (offN μ T)) f ∈ offN μ T ⊓ FN := fun f =>
    hmk _ hDo hDr _ ⟨hNo _ (TraceVanishing.prj_mem' hoffc f), hNf _⟩
  have hUS : ∀ f, (𝔢.Uq 0 ^ j) (((List.ofFn B₁).prod ∘L (List.ofFn B₂).prod ∘L prj (offN μ T)) f) ∈ offN μ T ⊓ FN := fun f => by
    rw [hUq]
    exact hmk C hCo hCr _ ⟨hNo _ (TraceVanishing.prj_mem' hoffc f), hNf _⟩
  have hY : eigIn (V ⊓ (offN μ T ⊓ FN)) (Oinf μ νE aE) x = Z ⊓ FN := by
    ext f
    simp only [Submodule.mem_inf, hZd, mem_eigIn']
    tauto
  haveI hfd : FiniteDimensional ℂ ↥(eigIn (V ⊓ (offN μ T ⊓ FN)) (Oinf μ νE aE) x) := by
    rw [hY]
    exact hZa r₂ p₂ hp₂ hpr₂ _ hlc
  have hred := UpperTheory.trace_eigenspace_of_selfAdjoint_invariant_subspaces (LL μ) (offN μ T ⊓ FN) (fixF μ (GM.levE L.UE)) V hTc hcp.1 hVc hle (Oinf μ νE aE) hOsa
    (hcomm _ fun u g => hOF _) hOFx
    (hcomm _ fun u g => ((UpperTheory.ConvolutionTheory.Tf.innerOps E n μ).2.2.2.1 _ V hVc (IsSummandOf.inv hV)).symm) x (κ : ℂ)
    (𝔢.Uq 0 ^ j) ((List.ofFn B₁).prod ∘L (List.ofFn B₂).prod ∘L prj (offN μ T)) θ.U hfd
    (by
      have := (𝔢.Uq_amp 0).pow_left j
      rwa [hAeq] at this) hS hUS
  have hRop := hK L ψ hfit r₁ p₁ hp₁ hpr₁ r₂ p₂ hp₂ hpr₂ mm hmmA B₁ B₂ hB₁ hB₂ 𝔢.g hg
  have hCB : Commute C (List.ofFn B₂).prod := Commute.list_prod_right _ _ fun Bx hBx => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hBx
    exact oloc_comm μ (hB₂ i) C (fun g => hCr _ (hwm i) g)
  have hZFc : IsClosed ((Z ⊓ FN : Submodule ℂ (LL μ)) : Set (LL μ)) := by
    rw [Submodule.coe_inf]
    exact hZc.inter hFNc
  have hsw : trOn (Z ⊓ FN) ((𝔢.Uq 0 ^ j) ∘L ((List.ofFn B₁).prod ∘L (List.ofFn B₂).prod ∘L prj (offN μ T)) ∘L θ.U) =
      trOn (Z ⊓ FN) ((List.ofFn B₂).prod ∘L (C ∘L θ.U)) := by
    refine trOn_congr hZFc fun f hf => ?_
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S (θ.U f)) hCB.eq
    simp only [ContinuousLinearMap.mul_apply] at this
    simp only [ContinuousLinearMap.comp_apply]
    rw [prj_self' (hZo (hθZ f hf.1)), hUq]
    exact this
  have hTw : ∀ i, HasTwTrace (mm (w i)) (τ (p₂ i)) (I (p₂ i)) (ψ (p₂ i)) (bb (w i) * t (p₂ i)) := fun i =>
    hasTw_smul _ (hd0 _) (hdt _) (htN _ (hns _ (hm₂ i)).1 (hns _ (hm₂ i)).2)
  have hfac := hTF (fun i => lvN T L (p₂ i)) (fun i => mm (w i)) (fun i => ψ (p₂ i)) B₂ (fun i => bb (w i) * t (p₂ i)) hlc
    (fun i => hmmH _) (fun i => hfit.test _ (hns _ (hm₂ i)).1) hlψ hB₂ hTw
  have hprod : ∏ v ∈ T.S, t v = (∏ v ∈ T.sp, t v) * ∏ i, t (p₂ i) := by
    have e2 : nsS T = Finset.univ.image p₂ := by
      ext v
      simp [hpr₂]
    have e3 : ∏ v ∈ nsS T, t v = ∏ i, t (p₂ i) := by
      rw [e2, Finset.prod_image (fun _ _ _ _ h => hp₂ h)]
    rw [← e3]
    exact (Finset.prod_filter_mul_prod_filter_not T.S _ t).symm
  have hcR : cR = c₀ * (c₁ * sq * ∏ v ∈ T.sp, t v) * (∏ i, t0 i)⁻¹ := (eq_mul_inv_iff_mul_eq₀ hP0).2 hcr
  rw [hAeq, hRop, hred, hY, hsw, hfac, hprod, hcR, Finset.prod_mul_distrib]
  ring
