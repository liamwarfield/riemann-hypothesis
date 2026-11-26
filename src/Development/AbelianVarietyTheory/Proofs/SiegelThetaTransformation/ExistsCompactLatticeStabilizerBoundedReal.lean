module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabCompact

theorem exists_compact_of_entries {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (C : Set (R ⊗[F] E)) (hC : IsCompact C) :
    ∃ K : Set (HA R σ J), IsCompact K ∧ ∀ h : HA R σ J, (∀ i j, (HA.mat R σ J h).1 i j ∈ C) → h ∈ K := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  haveI : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  have hc : IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  let S : Set (Matrix (Fin M) (Fin M) (R ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  let f : Matrix (Fin M) (Fin M) (R ⊗[F] E) → (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    fun A => MulOpposite.op (JR (F := F) R J⁻¹ * (Formalism.UG.cT (sigR R σ) A * JR (F := F) R J))
  have hf : Continuous f := MulOpposite.continuous_op.comp (continuous_const.matrix_mul
    ((continuous_id.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ)).matrix_transpose.matrix_mul
      continuous_const))
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (R ⊗[F] E))).comp
    hc.isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage (hS.prod (hS.image hf)), fun h hh => ?_⟩
  have hm : (HA.mat R σ J h).1 ∈ S := fun i _ j _ => hh i j
  refine ⟨hm, (HA.mat R σ J h).1, hm, ?_⟩
  have hu : Formalism.UG.cT (sigR R σ) (HA.mat R σ J h).1 * JR (F := F) R J * (HA.mat R σ J h).1 = JR (F := F) R J := h.2
  have h1 : JR (F := F) R J⁻¹ * JR (F := F) R J = 1 := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.map_one _ (map_zero _) (map_one _)]
  change MulOpposite.op _ = MulOpposite.op ((HA.mat R σ J h)⁻¹).1
  congr 1
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  rw [Matrix.mul_assoc, hu, h1]

theorem exists_compact_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG) :
    ∃ C : Set (Fin M → Af F ⊗[F] E), IsCompact C ∧ ∀ y ∈ latHat F E (L : Set (Fin M → E)), y ∈ C := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  haveI : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have hZ : (L.restrictScalars ℤ).FG := hL.restrictScalars
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  let g : (Fin m → Af F) → Fin M → Af F ⊗[F] E := fun c i => ∑ k, c k ⊗ₜ[F] x k i
  have hg : Continuous g := by
    refine continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    have : (fun c : Fin m → Af F => c k ⊗ₜ[F] x k i) = fun c => c k • ((1 : Af F) ⊗ₜ[F] x k i) := by
      funext c
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    have hk : Continuous fun c : Fin m → Af F => c k := continuous_apply k
    have ho : Continuous fun _ : Fin m → Af F => (1 : Af F) ⊗ₜ[F] x k i := continuous_const
    exact hk.smul ho
  have hI : IsCompact (intAf F) := GlobalTheory.AdeleCocompact.isCompact_integral F
  refine ⟨g '' Set.pi Set.univ fun _ => intAf F, (isCompact_univ_pi fun _ => hI).image hg, fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    have hv' : v ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hv
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv'
    refine ⟨fun k => n k • a, fun k _ w => ?_, ?_⟩
    · rw [map_zsmul]
      exact zsmul_mem (ha w) _
    · funext i
      simp only [g, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  | zero =>
    refine ⟨0, fun k _ w => ?_, ?_⟩
    · rw [Pi.zero_apply, map_zero]
      exact zero_mem _
    · funext i
      simp [g]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    refine ⟨c + d, fun k _ w => ?_, ?_⟩
    · rw [Pi.add_apply, map_add (f := _)]
      exact add_mem (hc k trivial w) (hd k trivial w)
    · funext i
      simp only [g, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨-c, fun k _ w => ?_, ?_⟩
    · rw [Pi.neg_apply, map_neg]
      exact neg_mem (hc k trivial w)
    · funext i
      simp only [g, Pi.neg_apply, TensorProduct.neg_tmul, Finset.sum_neg_distrib]

theorem exists_compact_entries (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) :
    ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧ ∀ A : Matrix (Fin M) (Fin M) (Af F ⊗[F] E),
      (∀ y ∈ latHat F E (L : Set (Fin M → E)), A.mulVec y ∈ latHat F E (L : Set (Fin M → E))) →
      ∀ i j, A i j ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨C, hC, hLC⟩ := exists_compact_latHat F E L hL
  choose d hd hdL using fun j => GlobalTheory.AdLat.OpenLat.exists_denom L hsp (Pi.single j 1)
  refine ⟨⋃ p : Fin M × Fin M, (fun y : Fin M → Af F ⊗[F] E =>
      y p.1 * ((1 : Af F) ⊗ₜ[F] ((d p.2 : E)⁻¹))) '' C,
    isCompact_iUnion fun p => hC.image ((continuous_apply p.1).mul continuous_const), fun A hA i j => ?_⟩
  have h1 : (1 : Af F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _
  have hy : (fun k => (1 : Af F) ⊗ₜ[F] (d j • (Pi.single j 1 : Fin M → E)) k) ∈
      latHat F E (L : Set (Fin M → E)) := AddSubgroup.subset_closure ⟨1, h1, _, hdL j, rfl⟩
  refine Set.mem_iUnion.2 ⟨(i, j), _, hLC _ (hA _ hy), ?_⟩
  have hd0 : (d j : E) ≠ 0 := Nat.cast_ne_zero.2 (hd j).ne'
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hd0]
  rw [← Algebra.TensorProduct.one_def, mul_one]

theorem det_gram_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem exists_compact_adele (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (R : ℝ) (C : Set (Af D.host.F ⊗[D.host.F] D.host.E)) (hC : IsCompact C) :
    ∃ K : Set (AE D), IsCompact K ∧ ∀ z : AE D, finPart D z ∈ C → (∀ ρ, ‖θ ρ (infPart D z)‖ ≤ R) → z ∈ K := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  obtain ⟨s, hs⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let j : Af D.host.F ⊗[D.host.F] D.host.E → AE D := fun w => e.symm (0, w)
  have hj : Continuous j := hc.comp (continuous_const.prodMk continuous_id)
  have hj1 : ∀ w, infPart D (j w) = 0 := fun w =>
    (he (e.symm (0, w))).1.symm.trans (by rw [e.apply_symm_apply])
  have hj2 : ∀ w, finPart D (j w) = w := fun w =>
    (he (e.symm (0, w))).2.symm.trans (by rw [e.apply_symm_apply])
  have hB : IsCompact (Set.pi Set.univ fun _ : D.what₂.Tau => Metric.closedBall (0 : ℂ) R) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine ⟨_, (hB.prod hC).image ((hs.cont.comp continuous_fst).add (hj.comp continuous_snd)), fun z hz hR => ?_⟩
  refine ⟨(fun ρ => θ ρ (infPart D z), finPart D z), ⟨fun ρ _ => mem_closedBall_zero_iff.2 (hR ρ), hz⟩, ?_⟩
  refine sub_eq_zero.1 (hs.ext _ ?_ fun τ => ?_)
  · change finPart D (s (fun ρ => θ ρ (infPart D z)) + j (finPart D z) - z) = 0
    rw [RingHom.map_sub, RingHom.map_add (f := _), hs.fin, hj2, zero_add, sub_self]
  · change θ τ (infPart D (s (fun ρ => θ ρ (infPart D z)) + j (finPart D z) - z)) = 0
    rw [RingHom.map_sub, RingHom.map_add (f := _), hj1, add_zero, RingHom.map_sub, hs.comp, sub_self]

theorem exists_compact_stab : ∀ (D : D7) (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ R : ℝ, ∃ K : Set (GA D V), IsCompact K ∧ ∀ h : GA D V, (∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) → (∀ ρ i j, ‖infMat D.sp.cm.sig V.gram (θ ρ) h i j‖ ≤ R) → h ∈ K := by
  intro D V θ hθ R
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
        let W := Submodule.span D.host.E (V.L0 : Set V.V)
        change W = ⊤
        by_contra h
        let e : V.V ≃ₗ⋆[D.host.E] V.V :=
          (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
        let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
          (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
        have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
            Module.finrank D.host.E V.V := by
          rw [Subspace.dual_finrank_eq]
          exact Submodule.finrank_lt h
        obtain ⟨z, hz, hz₀⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
        have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
          rw [← V.baseLattice_isUnimodular]
          simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
            Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
          intro y hy
          have hzy : V.hT (e z) y = 0 :=
            congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
              (LinearMap.mem_ker.mp hz)
          have hyz : V.hT y (e z) = 0 := by
            have hh := V.herm.eq (e z) y
            simpa [hzy] using hh.symm
          simp [hyz]
        let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
          ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
        let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
        let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
          smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
        exact RingOfIntegers.not_isField D.host.E
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
      rw [hspan]; trivial
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_span] at this
    exact this
  obtain ⟨C, hC, hCe⟩ := exists_compact_entries D.host.F D.host.E L (V.standardTuple_isLattice.fg.map _) hsp
  rw [hL] at hCe
  obtain ⟨C', hC', hCe'⟩ := exists_compact_adele D θ hθ R C hC
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨K, hK, hKe⟩ := exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram (det_gram_ne_zero V) C' hC'
  exact ⟨K, hK, fun h h1 h2 => hKe h fun i j =>
    hCe' _ (hCe _ (fun y hy => (h1 y).1 hy) i j) fun ρ => h2 ρ i j⟩

end GlobalTheory.StabCompact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedRealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_lattice_stabilizer_bounded_real : ∀ (D : D7) (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ R : ℝ, ∃ K : Set (GA D V), IsCompact K ∧ ∀ h : GA D V, (∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) → (∀ ρ i j, ‖infMat D.sp.cm.sig V.gram (θ ρ) h i j‖ ≤ R) → h ∈ K := by
  first | exact @GlobalTheory.StabCompact.exists_compact_stab | exact GlobalTheory.StabCompact.exists_compact_stab | (intros; apply GlobalTheory.StabCompact.exists_compact_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KerReal

open GlobalTheory.FockCompare

variable {D : D7}

theorem infPart_eq_zero {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) (a : AE D)
    (ha : ∀ τ, θ τ (infPart D a) = 0) : infPart D a = 0 := by

  let e0 : AF D.host.F := ((1 : Ainf D.host.F), (0 : Af D.host.F))
  let e : AE D := e0 ⊗ₜ[D.host.F] (1 : D.host.E)
  have hi : infPart D e = 1 := by
    simp only [infPart, e, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq]
    rfl
  have hf : finPart D e = 0 := by
    simp only [finPart, e, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq]
    exact TensorProduct.zero_tmul _ _
  have he : e * a = 0 :=
    h.ext _ (by rw [map_mul, hf, zero_mul]) fun τ => by rw [map_mul, hi, one_mul]; exact ha τ
  calc infPart D a = infPart D (e * a) := by rw [map_mul, hi, one_mul]
    _ = 0 := by rw [he, map_zero]

variable {S T : HSp D}

def realOf (C : Ctx S T) (σ : (D.what₂.Tau → ℂ) →+ AE D) : WR C.X S.rank →+ WO S T where
  toFun v := Matrix.of fun a k => σ fun τ => conj (v (C.m.e τ) k a)
  map_zero' := by
    funext a k
    have : (fun τ : D.what₂.Tau => conj ((0 : WR C.X S.rank) (C.m.e τ) k a)) = 0 := by
      funext τ; simp
    show σ _ = 0
    rw [this, σ.map_zero]
  map_add' x y := by
    funext a k
    have : (fun τ : D.what₂.Tau => conj ((x + y) (C.m.e τ) k a)) =
        (fun τ => conj (x (C.m.e τ) k a)) + fun τ => conj (y (C.m.e τ) k a) := by
      funext τ; simp
    show σ _ = σ _ + σ _
    rw [this, map_add σ]

theorem realPt_apply (C : Ctx S T) (w : WO S T) (s : C.X.Ψ) (k : Fin S.rank) (a : Fin T.rank) :
    C.realPt w s k a = conj (C.θ (C.m.e.symm s) (infPart D (w a k))) := rfl

theorem realPt_add (C : Ctx S T) (w w' : WO S T) : C.realPt (w + w') = C.realPt w + C.realPt w' := by
  funext s k a
  simp only [realPt_apply, Matrix.add_apply, map_add (f := _), Pi.add_apply]

theorem map_actO {B : Type} [CommRing B] (f : AE D →+* B) (h : GA D S) (g : GA D T) (w : WO S T) :
    (actO S T h g w).map f = (mt T g).map f * w.map f * (mt S h⁻¹).map f := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul]

private theorem isLineAt_apply_unique {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) {m n : ℕ}
    {τ : D.what₂.Tau} {z : Matrix (Fin m) (Fin n) ℂ} {L L' : ℝ →+ Mx D m n}
    (hL : IsLineAt θ τ z L) (hL' : IsLineAt θ τ z L') (t : ℝ) : L t = L' t := by
  unfold IsLineAt at hL hL'
  refine Matrix.ext fun a k => sub_eq_zero.mp (h.ext _ ?_ fun τ' => ?_)
  · have h1 := congrFun (congrFun (hL.2.1 t) a) k
    have h2 := congrFun (congrFun (hL'.2.1 t) a) k
    simp only [Matrix.map_apply, Matrix.zero_apply] at h1 h2
    rw [map_sub, h1, h2, sub_zero]
  · have h1 := congrFun (congrFun (hL.2.2 t τ') a) k
    have h2 := congrFun (congrFun (hL'.2.2 t τ') a) k
    simp only [compAt, Matrix.map_apply] at h1 h2
    rw [map_sub, map_sub, h1, h2, sub_self]

theorem real_points : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∃ R : WR C.X S.rank →+ WO S T, Continuous R ∧ Continuous C.realPt ∧ (∀ w w', C.realPt (w + w') = C.realPt w + C.realPt w') ∧ (∀ v, IsRealPt (R v) ∧ C.realPt (R v) = v) ∧ (∀ w, IsRealPt w → R (C.realPt w) = w) ∧ (∀ w, IsFinPt (w - R (C.realPt w))) ∧ (∀ u, IsFinPt u → C.realPt u = 0) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), lineAt C.θ τ z t = R (t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) ∧ ∀ (h : GA D S) (g : GA D T) (w : WO S T), (IsRealPt w → IsRealPt (actO S T h g w)) ∧ (IsFinPt w → IsFinPt (actO S T h g w)) ∧ ∀ τ, compAt C.θ τ (actO S T h g w) = compAt C.θ τ (mt T g) * compAt C.θ τ w * compAt C.θ τ (mt S h⁻¹) := by
  intro D S T C
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf

  have hRfin : ∀ v a k, finPart D (realOf C σ v a k) = 0 := fun v a k =>
    hσ.fin fun τ => conj (v (C.m.e τ) k a)
  have hRcomp : ∀ v a k τ, C.θ τ (infPart D (realOf C σ v a k)) = conj (v (C.m.e τ) k a) :=
    fun v a k τ => hσ.comp (fun τ => conj (v (C.m.e τ) k a)) τ
  have hRreal : ∀ v, IsRealPt (realOf C σ v) := by
    intro v
    show (realOf C σ v).map (finPart D) = 0
    refine Matrix.ext fun a k => ?_
    rw [Matrix.map_apply, hRfin]
    rfl
  have hReal : ∀ v, C.realPt (realOf C σ v) = v := by
    intro v
    funext s k a
    rw [realPt_apply, hRcomp]
    simp
  have hRcont : Continuous (realOf C σ) := by
    refine continuous_pi fun a => continuous_pi fun k => ?_
    exact hσ.cont.comp (continuous_pi fun τ => Complex.continuous_conj.comp
      ((continuous_apply a).comp ((continuous_apply k).comp (continuous_apply (C.m.e τ)))))
  refine ⟨realOf C σ, hRcont, ?_, fun w w' => realPt_add C w w', fun v => ⟨hRreal v, hReal v⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine continuous_pi fun s => continuous_pi fun k => continuous_pi fun a => ?_
    simp only [realPt_apply]
    exact Complex.continuous_conj.comp ((GlobalTheory.FockCompare.continuous_comp C.inf _).comp
      ((continuous_apply k).comp (continuous_apply a)))
  ·
    intro w hw
    have hw' : w.map (finPart D) = 0 := hw
    refine Matrix.ext fun a k => sub_eq_zero.mp (hσ.ext _ ?_ fun τ => ?_)
    · have h1 : finPart D (w a k) = 0 := congrArg (fun M => M a k) hw'
      rw [map_sub, hRfin, h1, sub_zero]
    · rw [map_sub, map_sub, hRcomp, realPt_apply]
      simp
  ·
    intro w
    show (w - realOf C σ (C.realPt w)).map (infPart D) = 0
    refine Matrix.ext fun a k => ?_
    rw [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply]
    refine infPart_eq_zero hσ _ fun τ => ?_
    rw [map_sub, map_sub, hRcomp, realPt_apply]
    simp
  ·
    intro u hu
    have hu' : u.map (infPart D) = 0 := hu
    funext s k a
    have h1 : infPart D (u a k) = 0 := by simpa using congrFun (congrFun hu' a) k
    simp [realPt_apply, h1]
  ·
    intro τ z t
    have hL : IsLineAt C.θ τ z ((realOf C σ).comp
        ((smulAddHom ℝ (WR C.X S.rank)).flip (Pi.single (C.m.e τ) fun k a => conj (z a k)))) := by
      unfold IsLineAt
      refine ⟨hRcont.comp (continuous_id.smul continuous_const), fun t => hRreal _, fun t τ' => ?_⟩
      refine Matrix.ext fun a k => ?_
      simp only [compAt, Matrix.map_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        AddMonoidHom.flip_apply, smulAddHom_apply]
      rw [hRcomp]
      by_cases hτ : τ' = τ
      · subst hτ
        simp [Complex.real_smul]
      · simp [hτ]
    have hE : IsLineAt C.θ τ z (lineAt C.θ τ z) := by
      unfold lineAt
      exact Classical.epsilon_spec ⟨_, hL⟩
    exact isLineAt_apply_unique hσ hE hL t
  ·
    intro h g w
    refine ⟨fun hw => ?_, fun hw => ?_, fun τ => map_actO ((C.θ τ).comp (infPart D)) h g w⟩
    · have hw' : w.map (finPart D) = 0 := hw
      show (actO S T h g w).map (finPart D) = 0
      rw [map_actO, hw', Matrix.mul_zero, Matrix.zero_mul]
    · have hw' : w.map (infPart D) = 0 := hw
      show (actO S T h g w).map (infPart D) = 0
      rw [map_actO, hw', Matrix.mul_zero, Matrix.zero_mul]

end GlobalTheory.KerReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_classicalModel_realVectorSpace : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∃ R : WR C.X S.rank →+ WO S T, Continuous R ∧ Continuous C.realPt ∧ (∀ w w', C.realPt (w + w') = C.realPt w + C.realPt w') ∧ (∀ v, IsRealPt (R v) ∧ C.realPt (R v) = v) ∧ (∀ w, IsRealPt w → R (C.realPt w) = w) ∧ (∀ w, IsFinPt (w - R (C.realPt w))) ∧ (∀ u, IsFinPt u → C.realPt u = 0) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), lineAt C.θ τ z t = R (t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) ∧ ∀ (h : GA D S) (g : GA D T) (w : WO S T), (IsRealPt w → IsRealPt (actO S T h g w)) ∧ (IsFinPt w → IsFinPt (actO S T h g w)) ∧ ∀ τ, compAt C.θ τ (actO S T h g w) = compAt C.θ τ (mt T g) * compAt C.θ τ w * compAt C.θ τ (mt S h⁻¹) := by
  first | exact @GlobalTheory.KerReal.real_points | exact GlobalTheory.KerReal.real_points | (intros; apply GlobalTheory.KerReal.real_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal.Cmp

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C) :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (x : Sp B ⟶ Sp A) : ∃ β : A →+* B, x = spMap β := by
  exact ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩

theorem rho_eq_of_ne (hpq : Dw.p ≠ Dw.q) {l₂ : Geo.Tor.Level H} {Xo₂ : Moduli Dw l₂} {π : Xo₂.X ⟶ Xo.X}
    (m : SABMap Xo₂.univ.t Xo.univ.t π) {k : Type} [Field k] [IsAlgClosed k] {x : Sp k ⟶ Xo₂.X}
    {β : KA l →+* k} {β₂ : KA l₂ →+* k} (h : (x ≫ π) ≫ Xo.s = spMap β) (h₂ : x ≫ Xo₂.s = spMap β₂) :
    β (baseKA l).ρ = β₂ (baseKA l₂).ρ := by
  have : CharZero k := (RingHom.charZero_iff β.injective).mp inferInstance
  have hsq1 : (β (baseKA l).ρ) ^ 2 = -(H.d : k) := by
    have e := congrArg β (baseKA l).ρ_sq
    simpa using e
  have hsq2 : (β₂ (baseKA l₂).ρ) ^ 2 = -(H.d : k) := by
    have e := congrArg β₂ (baseKA l₂).ρ_sq
    simpa using e
  let τE : E →ₐ[ℚ] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let τ : 𝓞 E →+* k := (τE : E →+* k).comp (algebraMap (𝓞 E) E)
  have ht : (τ H.rt) ^ 2 = -(H.d : k) := by
    have e := congrArg τ H.rt_sq
    simpa using e
  have D1 := (Xo.univ.geom k (x ≫ π) β h).1
  have D2 := (Xo₂.univ.geom k x β₂ h₂).1
  have P : ∀ n, LieMult Xo₂.univ.t.act x τ n ↔ LieMult Xo.univ.t.act (x ≫ π) τ n := fun n =>
    GlobalTheory.LiePull.lieMult_pull (𝓞 E) Xo.X Xo₂.X Xo.univ.t.G Xo₂.univ.t.G π m.cm.F Xo.univ.t.act Xo₂.univ.t.act
      m.cart m.act k x τ n
  let b' : Base l₂ k :=
    { unit := fun n hn => (Nat.cast_ne_zero.mpr hn.ne').isUnit
      ρ := β₂ (baseKA l₂).ρ
      ρ_sq := hsq2
      ζ := β₂ (baseKA l₂).ζ
      ζ_prim := (baseKA l₂).ζ_prim.map_of_injective β₂.injective }
  obtain ⟨o', ⟨om⟩⟩ := GlobalTheory.obj_pull E H Dw l₂ (KA l₂) k (baseKA l₂) b' β₂ Xo₂.X (Sp k) Xo₂.s (𝟙 (Sp k)) x rfl rfl
    (by rw [Category.id_comp]; exact h₂) Xo₂.univ
  have P' : ∀ n, LieMult o'.t.act (𝟙 (Sp k)) τ n ↔ LieMult Xo₂.univ.t.act (𝟙 (Sp k) ≫ x) τ n := fun n =>
    GlobalTheory.LiePull.lieMult_pull (𝓞 E) Xo₂.X (Sp k) Xo₂.univ.t.G o'.t.G x om.cm.F Xo₂.univ.t.act o'.t.act
      om.cart om.act k (𝟙 _) τ n
  have U : ∀ n n', LieMult Xo₂.univ.t.act x τ n → LieMult Xo₂.univ.t.act x τ n' → n = n' := by
    intro n n' hn hn'
    have hn2 := (P' n).mpr (by rw [Category.id_comp]; exact hn)
    have hn2' := (P' n').mpr (by rw [Category.id_comp]; exact hn')
    obtain ⟨bn⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff o'.t.act τ n).mp hn2
    obtain ⟨bn'⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff o'.t.act τ n').mp hn2'
    have e := (Module.finrank_eq_card_basis bn).symm.trans (Module.finrank_eq_card_basis bn')
    simpa using e
  by_contra hne
  have h21 : β₂ (baseKA l₂).ρ = -(β (baseKA l).ρ) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq2.trans hsq1.symm) with e | e
    · exact absurd e.symm hne
    · exact e
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (ht.trans hsq1.symm) with e | e
  · have hp : LieMult Xo₂.univ.t.act x τ Dw.p := (P _).mpr ((D1 τ).1 e)
    have hq : LieMult Xo₂.univ.t.act x τ Dw.q := (D2 τ).2 (by rw [e]; exact hne)
    exact hpq (U _ _ hp hq)
  · have e' : τ H.rt = β₂ (baseKA l₂).ρ := e.trans h21.symm
    have hp : LieMult Xo₂.univ.t.act x τ Dw.p := (D2 τ).1 e'
    have hq : LieMult Xo₂.univ.t.act x τ Dw.q := (P _).mpr ((D1 τ).2 (by rw [e']; exact fun h' => hne h'.symm))
    exact hpq (U _ _ hp hq)

private theorem ringHom_KA_ext_of_A_eq_one (hA : l.A = 1) {R : Type} [CommRing R] {β β' : KA l →+* R}
    (h : β (baseKA l).ρ = β' (baseKA l).ρ) : β = β' := by
  have hz : zeta l.A = 1 := by
    rw [hA]
    simp [zeta, Complex.exp_two_pi_mul_I]
  ext ⟨z, hz'⟩
  change z ∈ IntermediateField.adjoin ℚ {H.rt0, zeta l.A} at hz'
  induction hz' using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · have e : (⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩ : KA l) = 1 := Subtype.ext hz
      rw [e, map_one, map_one]
  | algebraMap q =>
    show β (algebraMap ℚ (KA l) q) = β' (algebraMap ℚ (KA l) q)
    exact DFunLike.congr_fun (RingHom.ext_rat (β.comp (algebraMap ℚ (KA l))) (β'.comp (algebraMap ℚ (KA l)))) q
  | add x y hx hy ihx ihy =>
    show β (⟨x, hx⟩ + ⟨y, hy⟩) = β' (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add (f := _), map_add (f := _), ihx, ihy]
  | mul x y hx hy ihx ihy =>
    show β (⟨x, hx⟩ * ⟨y, hy⟩) = β' (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]
  | inv x hx ih =>
    show β (⟨x, hx⟩⁻¹) = β' (⟨x, hx⟩⁻¹)
    by_cases h0 : (⟨x, hx⟩ : KA l) = 0
    · rw [h0, _root_.inv_zero, map_zero, map_zero]
    · have e1 : β ⟨x, hx⟩ * β (⟨x, hx⟩⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
      have e2 : β' ⟨x, hx⟩ * β' (⟨x, hx⟩⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
      calc β (⟨x, hx⟩⁻¹) = β (⟨x, hx⟩⁻¹) * (β' ⟨x, hx⟩ * β' (⟨x, hx⟩⁻¹)) := by rw [e2, mul_one]
        _ = (β ⟨x, hx⟩ * β (⟨x, hx⟩⁻¹)) * β' (⟨x, hx⟩⁻¹) := by rw [← ih]; ring
        _ = β' (⟨x, hx⟩⁻¹) := by rw [e1, one_mul]

theorem emb_ext_of_one (hA : l.A = 1) {k : Type} [Field k] {β β' : KA l →+* k}
    (h : β (baseKA l).ρ = β' (baseKA l).ρ) : β = β' := by
  exact ringHom_KA_ext_of_A_eq_one hA h

def OverBase (d : DeltaDat Xo c n) : Prop :=
  ∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom

theorem point_over_of_ne (hpq : Dw.p ≠ Dw.q) (hA : l.A = 1) (d : DeltaDat Xo c n) (h : KA l ≤ KA d.l₂)
    {K : Type} [Field K] (t : Sp K ⟶ d.Xo₂.X) :
    t ≫ d.r ≫ Xo.s = t ≫ d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom := by
  obtain ⟨γ1, e1⟩ := exists_spMap' (t ≫ d.r ≫ Xo.s)
  obtain ⟨γ2, e2⟩ := exists_spMap' (t ≫ d.Xo₂.s)
  have key : γ1 = γ2.comp (IntermediateField.inclusion h).toRingHom := by
    apply emb_ext_of_one hA
    let ι := algebraMap K (AlgebraicClosure K)
    apply ι.injective
    have e := rho_eq_of_ne hpq d.m (x := spMap ι ≫ t) (β := ι.comp γ1) (β₂ := ι.comp γ2)
      (by simp only [Category.assoc]; rw [e1, spMap_comp']) (by rw [Category.assoc, e2, spMap_comp'])
    exact e
  rw [e1, ← Category.assoc, e2, spMap_comp', key]

theorem overBase_of_ne (hpq : Dw.p ≠ Dw.q) (hA : l.A = 1) (d : DeltaDat Xo c n) : OverBase d := by
  intro h
  have : IsReduced d.Xo₂.X := GlobalTheory.UnivPol.isReduced d.Xo₂
  set f := d.r ≫ Xo.s with hf
  set g := d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom with hg
  have hpt : ∀ p : d.Xo₂.X, d.Xo₂.X.fromSpecResidueField p ≫ f = d.Xo₂.X.fromSpecResidueField p ≫ g :=
    fun p => point_over_of_ne hpq hA d h (K := d.Xo₂.X.residueField p) (d.Xo₂.X.fromSpecResidueField p)
  let φf := ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ f.appTop).hom
  let φg := ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ g.appTop).hom
  have key : ∀ p : d.Xo₂.X, p ∉ d.Xo₂.X.basicOpen (φf (baseKA l).ρ - φg (baseKA l).ρ) := by
    intro p hp
    let t := d.Xo₂.X.fromSpecResidueField p
    have e1 : f.appTop ≫ t.appTop = g.appTop ≫ t.appTop := by
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hpt p]
    have e2 : t.appTop (φf (baseKA l).ρ - φg (baseKA l).ρ) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom (baseKA l).ρ)) e1
    have e3 := Scheme.preimage_basicOpen_top t (φf (baseKA l).ρ - φg (baseKA l).ρ)
    rw [e2, Scheme.basicOpen_zero] at e3
    obtain ⟨q⟩ : Nonempty ↥(Spec (d.Xo₂.X.residueField p)) := ⟨IsLocalRing.closedPoint _⟩
    have hq : q ∈ t ⁻¹ᵁ d.Xo₂.X.basicOpen (φf (baseKA l).ρ - φg (baseKA l).ρ) := by
      rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
      exact hp
    rw [e3] at hq
    simp at hq
  have hφ : φf = φg := by
    apply ringHom_KA_ext_of_A_eq_one hA
    rw [← sub_eq_zero]
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro p hp
    exact (key p hp).elim
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ f.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ g.appTop := CommRingCat.hom_ext hφ
  rw [cancel_epi] at h1
  rw [← cancel_mono (Sp (KA l)).toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h1]

theorem coe_incl {S T : IntermediateField ℚ ℂ} (h : S ≤ T) (t : S) :
    (((IntermediateField.inclusion h).toRingHom t : T) : ℂ) = (t : ℂ) := rfl

theorem eq_incl {S T : IntermediateField ℚ ℂ} (h : S ≤ T) (j : S →+* T) (hj : ∀ t, ((j t : T) : ℂ) = (t : ℂ)) :
    j = (IntermediateField.inclusion h).toRingHom := by
  exact RingHom.ext fun t => Subtype.ext ((hj t).trans (coe_incl h t).symm)

section Reads

variable {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (W : UW U) (k : U.Comp) {a : (E →+* ℂ) × ℕ → ℕ}

variable {U W k}

end Reads

end

end GlobalTheory.ClsVal.Cmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
namespace GlobalTheory.Ker.Mov

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.AdLat.Translate GlobalTheory.SW
open scoped TensorProduct Matrix nonZeroDivisors

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def Into (F : Type) [Field F] [NumberField F] [Algebra F E] (m : Matrix (Fin n) (Fin n) (RA F E))
    (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ z ∈ hat F (L : Set (Fin n → E)), m *ᵥ z ∈ hat F (L' : Set (Fin n → E))

def Onto (F : Type) [Field F] [NumberField F] [Algebra F E] (m : Matrix (Fin n) (Fin n) (RA F E))
    (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ u, u ∈ hat F (L' : Set (Fin n → E)) ↔ ∃ u₀ ∈ hat F (L : Set (Fin n → E)), u = m *ᵥ u₀

theorem into_of_fv {m : Matrix (Fin n) (Fin n) (RA F E)} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ x ∈ L, m *ᵥ fv F x ∈ hat F (L' : Set (Fin n → E))) : Into F m L L' :=
  fun _ hz => mulVec_mem_hat (L := L') (fun x hx => h x hx) hz

theorem onto_iff {m m' : Matrix (Fin n) (Fin n) (RA F E)} (h : m * m' = 1)
    {L L' : Submodule (𝓞 E) (Fin n → E)} : Onto F m L L' ↔ Into F m L L' ∧ Into F m' L' L := by
  have h' : m' * m = 1 := mul_eq_one_comm.1 h
  constructor
  · intro H
    refine ⟨fun z hz => (H _).2 ⟨z, hz, rfl⟩, fun z hz => ?_⟩
    obtain ⟨u, hu, rfl⟩ := (H _).1 hz
    rwa [Matrix.mulVec_mulVec, h', Matrix.one_mulVec]
  · rintro ⟨H, H'⟩ u
    constructor
    · intro hu
      exact ⟨m' *ᵥ u, H' u hu, by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]⟩
    · rintro ⟨u, hu, rfl⟩
      exact H u hu

omit [NumberField E] in
theorem map_mulVec_fv (P : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (P.map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) *ᵥ fv F x = fv F (P *ᵥ x) := by
  funext i
  simp [fv, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

omit [NumberField E] in
theorem fv_eq_zero {x : Fin n → E} (h : fv F x = 0) : x = 0 := by
  haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
    let v : HeightOneSpectrum (𝓞 F) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
    exact zero_ne_one h2
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective
  funext i
  apply hinj
  rw [Pi.zero_apply, map_zero]
  exact congrFun h i

theorem onto_mapL (g : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    Onto F ((g : Matrix (Fin n) (Fin n) E).map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E))
      L (mapL g L) := by
  have hm : ((g : Matrix (Fin n) (Fin n) E).map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) *
      (((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
        fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) = 1 := by
    have := Matrix.map_mul (L := (g : Matrix (Fin n) (Fin n) E))
      (M := ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
      (f := (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom)
    rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this.symm
  refine (onto_iff hm).2 ⟨into_of_fv fun x hx => ?_, into_of_fv ?_⟩
  · rw [map_mulVec_fv]
    exact fv_mem_hat ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [map_mulVec_fv]
    refine fv_mem_hat ?_
    change ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((g : Matrix (Fin n) (Fin n) E) *ᵥ x) ∈ L
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem span_eq_top_of_into {m m' : Matrix (Fin n) (Fin n) (RA F E)} (h : m * m' = 1)
    {L L' : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (H : Into F m L L') : Submodule.span E (L' : Set (Fin n → E)) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨-, -, -, h4⟩ := hat_rational_points_and_approx F E n L hL hs
  let P : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (LinearMap.pi fun _ => φ)
  have hP : ∀ x, P *ᵥ x = fun _ => φ x := fun x => by
    simp only [P, LinearMap.toMatrix'_mulVec]; rfl
  have hz : ∀ z ∈ hat F (L' : Set (Fin n → E)),
      (P.map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) *ᵥ z = 0 := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, -, x, hx, rfl⟩ := hz
      have hx0 : φ x = 0 := hφ (Submodule.subset_span hx)
      rw [gen_eq, Matrix.mulVec_smul, map_mulVec_fv, hP, hx0]
      exact (congrArg _ fv_zero).trans (smul_zero _)
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, add_zero]
    | neg x _ hx => rw [Matrix.mulVec_neg, hx, neg_zero]
  apply hφ0
  have key : ∀ x, (fun _ : Fin n => φ x) = 0 := by
    intro x
    obtain ⟨d, hd, hdx⟩ := h4 (m' *ᵥ fv F x)
    have h1 := hz _ (H _ hdx)
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec (fv F x) m m', h, Matrix.one_mulVec,
      map_mulVec_fv, hP] at h1
    exact fv_eq_zero (F := F) (nsmul_cancel hd (h1.trans (smul_zero d).symm))
  refine (Pi.basisFun E (Fin n)).ext fun i => ?_
  exact congrFun (key _) i

theorem into_smul {m : Matrix (Fin n) (Fin n) (RA F E)} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (H : Into F m L L') (𝔞 : Ideal (𝓞 E)) : Into F m (𝔞 • L) (𝔞 • L') := by
  have : 𝔞 • L ≤ pre m (𝔞 • L') := by
    refine Submodule.smul_le.2 fun a ha x hx => ?_
    rw [mem_pre, show a • x = (a : E) • x from rfl, fv_smul, Matrix.mulVec_smul]
    exact Scale.smul_mem_hat (fun y hy => Submodule.smul_mem_smul ha hy) (H _ (fv_mem_hat hx))
  exact into_of_fv this

theorem into_idq {m : Matrix (Fin n) (Fin n) (RA F E)} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (H : Into F m L L') (𝔞 𝔟 : Ideal (𝓞 E)) (hb : 𝔟 ≠ ⊥) : Into F m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') := by
  refine into_of_fv fun v hv => ?_
  have hI : ((𝔟 : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hb
  have key : ∀ c ∈ (𝔟 : FractionalIdeal (𝓞 E)⁰ E) * (𝔟 : FractionalIdeal (𝓞 E)⁰ E)⁻¹,
      m *ᵥ fv F (c • v) ∈ hat F (idq 𝔞 𝔟 L' : Set (Fin n → E)) := by
    intro c hc
    refine FractionalIdeal.mul_induction_on hc ?_ ?_
    · intro a ha c hc
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
      rw [mul_comm, mul_smul, fv_smul, Matrix.mulVec_smul]
      refine Scale.smul_mem_hat ?_ (into_smul H 𝔞 _ (fv_mem_hat (hv b hb)))
      intro y hy b' hb'
      have hbc : algebraMap (𝓞 E) E b' * c ∈
          (𝔟 : FractionalIdeal (𝓞 E)⁰ E) * (𝔟 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ :=
        FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨b', hb', rfl⟩) hc
      rw [mul_inv_cancel₀ hI, FractionalIdeal.mem_one_iff] at hbc
      obtain ⟨r, hr⟩ := hbc
      have : b' • c • y = r • y := by
        change algebraMap (𝓞 E) E b' • c • y = algebraMap (𝓞 E) E r • y
        rw [smul_smul, hr]
      rw [this]
      exact Submodule.smul_mem _ r hy
    · intro x y hx hy
      rw [add_smul, fv_add, Matrix.mulVec_add]
      exact add_mem hx hy
  have := key 1 (by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _)
  rwa [one_smul] at this

theorem idq_fg {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) (𝔞 𝔟 : Ideal (𝓞 E)) (hb : 𝔟 ≠ ⊥) :
    (idq 𝔞 𝔟 L).FG := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hb' : algebraMap (𝓞 E) E b ≠ 0 := fun h => hb0 (RingOfIntegers.coe_injective (by simpa using h))
  have hinj : Function.Injective (b • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) := by
    intro x y hxy
    exact smul_right_injective _ hb' hxy
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  have hle : (idq 𝔞 𝔟 L).map (b • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_le_right (hx b hb)
  have : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian _ hL
  exact (isNoetherian_submodule.1 this) _ hle

theorem idq_span {L : Submodule (𝓞 E) (Fin n → E)} (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (𝔞 𝔟 : Ideal (𝓞 E)) (ha : 𝔞 ≠ ⊥) : Submodule.span E (idq 𝔞 𝔟 L : Set (Fin n → E)) = ⊤ := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  have ha' : algebraMap (𝓞 E) E a ≠ 0 := fun h => ha0 (RingOfIntegers.coe_injective (by simpa using h))
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro x hx
  have h1 : algebraMap (𝓞 E) E a • x ∈ idq 𝔞 𝔟 L := fun b _ =>
    Submodule.smul_mem _ b (Submodule.smul_mem_smul ha hx)
  have := (Submodule.span E (idq 𝔞 𝔟 L : Set (Fin n → E))).smul_mem (algebraMap (𝓞 E) E a)⁻¹
    (Submodule.subset_span h1)
  rwa [smul_smul, inv_mul_cancel₀ ha', one_smul] at this

theorem onto_laws (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤) (m m' : Matrix (Fin n) (Fin n) (RA F E)) (h : m * m' = 1) :
    (∃ L' : Submodule (𝓞 E) (Fin n → E), (L'.FG ∧ Submodule.span E (L' : Set (Fin n → E)) = ⊤) ∧ Onto F m L L') ∧
    ∀ L' : Submodule (𝓞 E) (Fin n → E), L'.FG → Onto F m L L' →
      Submodule.span E (L' : Set (Fin n → E)) = ⊤ ∧ Onto F m' L' L ∧
      (∀ L'' : Submodule (𝓞 E) (Fin n → E), L''.FG → Onto F m L L'' → L'' = L') ∧
      (∀ m₂ (L'' : Submodule (𝓞 E) (Fin n → E)), Onto F m₂ L' L'' → Onto F (m₂ * m) L L'') ∧
      ∀ 𝔞 𝔟 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → Onto F m (𝔞 • L) (𝔞 • L') ∧
        Onto F m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') ∧ (idq 𝔞 𝔟 L).FG ∧
        Submodule.span E (idq 𝔞 𝔟 L : Set (Fin n → E)) = ⊤ := by
  have h' : m' * m = 1 := mul_eq_one_comm.1 h
  constructor
  · obtain ⟨Λ, -, h2, h3, h4⟩ := exists_lattice_latOf F E n L ⟨m, m', h, h'⟩ hL hs
    refine ⟨Λ, ⟨h2, h3⟩, fun u => ?_⟩
    rw [← SetLike.mem_coe, h4]
    exact ⟨fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩, fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩⟩
  · intro L' hL' H
    obtain ⟨H1, H2⟩ := (onto_iff h).1 H
    have hs' := span_eq_top_of_into h hL hs H1
    refine ⟨hs', (onto_iff h').2 ⟨H2, H1⟩, fun L'' hL'' K => ?_, fun m₂ L'' K u => ?_,
      fun 𝔞 𝔟 ha hb => ⟨(onto_iff h).2 ⟨into_smul H1 𝔞, into_smul H2 𝔞⟩,
        (onto_iff h).2 ⟨into_idq H1 𝔞 𝔟 hb, into_idq H2 𝔞 𝔟 hb⟩, idq_fg hL 𝔞 𝔟 hb, idq_span hs 𝔞 𝔟 ha⟩⟩
    · have hs'' := span_eq_top_of_into h hL hs ((onto_iff h).1 K).1
      ext v
      rw [← (hat_rational_points_and_approx F E n L'' hL'' hs'').1,
        ← (hat_rational_points_and_approx F E n L' hL' hs').1, K, H]
    · rw [K]
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨z, hz, rfl⟩ := (H w).1 hw
        exact ⟨z, hz, Matrix.mulVec_mulVec _ _ _⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨m *ᵥ z, H1 z hz, (Matrix.mulVec_mulVec _ _ _).symm⟩

end GlobalTheory.Ker.Mov

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Ker.isMov_laws : ∀ (D : D7) (k : ℕ) (L : Lt D.host.E k), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin k → D.host.E)) = ⊤) → (∀ v, toAf v ∈ hatV L ↔ v ∈ L) ∧ IsMov 1 L L ∧ (∀ ga : GL (Fin k) D.host.E, IsMov ((ga : Matrix (Fin k) (Fin k) D.host.E).map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) L (mapL ga L)) ∧ ∀ m m' : Matrix (Fin k) (Fin k) (AfE D), m * m' = 1 → (∃ L' : Lt D.host.E k, (L'.FG ∧ Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤) ∧ IsMov m L L') ∧ ∀ L' : Lt D.host.E k, L'.FG → IsMov m L L' → Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤ ∧ IsMov m' L' L ∧ (∀ L'' : Lt D.host.E k, L''.FG → IsMov m L L'' → L'' = L') ∧ (∀ m₂ (L'' : Lt D.host.E k), IsMov m₂ L' L'' → IsMov (m₂ * m) L L'') ∧ ∀ 𝔞 𝔟 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsMov m (𝔞 • L) (𝔞 • L') ∧ IsMov m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') ∧ (idq 𝔞 𝔟 L).FG ∧ Submodule.span D.host.E (idq 𝔞 𝔟 L : Set (Fin k → D.host.E)) = ⊤ := by
  rintro D k L ⟨hL, hs⟩
  refine ⟨(GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E k L hL hs).1, fun u => ?_,
    fun ga => GlobalTheory.Ker.Mov.onto_mapL (F := D.host.F) ga L,
    fun m m' h => GlobalTheory.Ker.Mov.onto_laws (F := D.host.F) L hL hs m m' h⟩
  simp only [Matrix.one_mulVec, exists_eq_right']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicLatticeTransport_laws : ∀ (D : D7) (k : ℕ) (L : Lt D.host.E k), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin k → D.host.E)) = ⊤) → (∀ v, toAf v ∈ hatV L ↔ v ∈ L) ∧ IsMov 1 L L ∧ (∀ ga : GL (Fin k) D.host.E, IsMov ((ga : Matrix (Fin k) (Fin k) D.host.E).map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) L (mapL ga L)) ∧ ∀ m m' : Matrix (Fin k) (Fin k) (AfE D), m * m' = 1 → (∃ L' : Lt D.host.E k, (L'.FG ∧ Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤) ∧ IsMov m L L') ∧ ∀ L' : Lt D.host.E k, L'.FG → IsMov m L L' → Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤ ∧ IsMov m' L' L ∧ (∀ L'' : Lt D.host.E k, L''.FG → IsMov m L L'' → L'' = L') ∧ (∀ m₂ (L'' : Lt D.host.E k), IsMov m₂ L' L'' → IsMov (m₂ * m) L L'') ∧ ∀ 𝔞 𝔟 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsMov m (𝔞 • L) (𝔞 • L') ∧ IsMov m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') ∧ (idq 𝔞 𝔟 L).FG ∧ Submodule.span D.host.E (idq 𝔞 𝔟 L : Set (Fin k → D.host.E)) = ⊤ := by
  first | exact @GlobalTheory.Ker.isMov_laws | exact GlobalTheory.Ker.isMov_laws | (intros; apply GlobalTheory.Ker.isMov_laws <;> assumption)
end
end
