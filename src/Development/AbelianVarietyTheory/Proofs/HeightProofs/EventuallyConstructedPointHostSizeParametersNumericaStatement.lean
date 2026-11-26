module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Formalism.LocalToGlobal.NumberFieldFamilies.IsLocalizedOfSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeParametersNumericaStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_constructedPoint_hostSize_numerical : EvP fun _ K => ∀ β : BPt K, GlobalTheory.FieldSize.HostSz β.D.host β.O.L.sc.L ∧ ∀ C, FieldTies β.D C → NumAtL β.O.L K.s.x := by
  first | exact @GlobalTheory.Plug.eventually_hostSize_and_numAt | exact GlobalTheory.Plug.eventually_hostSize_and_numAt | (intros; apply GlobalTheory.Plug.eventually_hostSize_and_numAt <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MoreOfTiesB
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem more_of_tiesB : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c),
    TiesB D O c b → FieldSmall D O.L → SingleIndexPlacesAreTwisted b → More b := by
  intro D O c b hT hS hW
  obtain ⟨hs, hr⟩ := hT
  refine ⟨hW, ?_, ?_⟩
  · exact GlobalTheory.Plug.coreTies_of_tied D _ _ _ _ O.L O.ex.errX b.T (R2 b) b.P.A3.A.μ0 hs.tied b.charW.base.lev hS
  · exact ⟨hs.series, hs.level, hs.data, hs.psi, hs.psiVal, hs.small, hs.types, hr⟩

end GlobalTheory.PlugPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightRaysOfRayRec
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX
  GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug.RaysW

theorem nonempty_heightOneSpectrum (L : Type) [Field L] [NumberField L] : Nonempty (HeightOneSpectrum (𝓞 L)) := by
  obtain ⟨P, hne, hP⟩ := (Ring.not_isField_iff_exists_prime (R := 𝓞 L)).1 (NumberField.RingOfIntegers.not_isField L)
  exact ⟨⟨P, hP, hne⟩⟩

end GlobalTheory.Plug.RaysW

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.PathCoreConditionsOfParametersFreeConditionsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.PathCoreConditionsOfSizeFreeConditions
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem ties_core_of_tiesB : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c), TiesB D O c b → FieldSmall D O.L →
    CoreTies O.L O.ex.errX b.T b.R.toRealDat ∧ b.T.pb = b.R.C.P.pb ∧ GlobalTheory.GLq.ESerTie D ∧ b.LevelTie ∧ b.DataTie := by
  intro D O c b h hF
  obtain ⟨hT, -⟩ := h
  refine ⟨GlobalTheory.Plug.coreTies_of_tied D _ _ _ _ O.L O.ex.errX b.T b.R.toRealDat _ hT.tied b.charW.base.lev hF,
    hT.tied.core.pb, hT.types.eSerTie, hT.level, hT.data⟩

end GlobalTheory.PlugPt
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pathCoreConditions_of_intrinsicConditions : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c), TiesB D O c b → FieldSmall D O.L → CoreTies O.L O.ex.errX b.T b.R.toRealDat ∧ b.T.pb = b.R.C.P.pb ∧ GlobalTheory.GLq.ESerTie D ∧ b.LevelTie ∧ b.DataTie := by
  first | exact @GlobalTheory.PlugPt.ties_core_of_tiesB | exact GlobalTheory.PlugPt.ties_core_of_tiesB | (intros; apply GlobalTheory.PlugPt.ties_core_of_tiesB <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RayClassFieldsInCoefficientFieldConstructedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RayClassFieldsInCoefficientFieldConstructedPoint
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem rayClassFields_in_coefficients : ∀ (K : Ctx) (β : BPt K), β.Is RayPosition → RayRec β.D β.O.ex.nch := by
  intro K β h
  obtain ⟨X, f, T, c, Y, hY, p, _, _, _, _, _, _, _, _, _⟩ := β
  change RayRec X.toD7 c.O.nch at h
  rw [← hY] at h
  exact h

end GlobalTheory.PlugPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RayClassFieldsInCoefficientFieldConstructedPointStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassFieldsInCoefficientField_constructedPoint : ∀ (K : Ctx) (β : BPt K), β.Is RayPosition → RayRec β.D β.O.ex.nch := by
  first | exact @GlobalTheory.PlugPt.rayClassFields_in_coefficients | exact GlobalTheory.PlugPt.rayClassFields_in_coefficients | (intros; apply GlobalTheory.PlugPt.rayClassFields_in_coefficients <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SeriesUpdatePreservesParametersFreeConditionsRayFielStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SeriesUpdatePreservesParamFreeConditionsRayField
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicThetaSeriesComparisonIndepScalarsErrors
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicThetaSeriesComparisonIndepScalarsErrors
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt.Side


set_option maxHeartbeats 3200000 in
theorem exportTie_upd : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) kap lam err, Nonempty (GlobalTheory.SeriesTie.ExportTie s.YS s.v₀) → Nonempty (GlobalTheory.SeriesTie.ExportTie (s.upd kap lam err).YS (s.upd kap lam err).v₀) := by
  intro D nch s kap lam err ⟨Z⟩
  exact ⟨{
    ρ := Z.ρ
    good := Z.good
    pin := { Z.pin with }
    vec := Z.vec
    ν := Z.ν
    scalar := fun i j b => ⟨(Z.scalar i j b).ne, fun h => (Z.scalar i j b).norm h, fun h => (Z.scalar i j b).rat h⟩
    tie := Z.tie
    hecke := Z.hecke
    univ := Z.univ }⟩

end GlobalTheory.PlugPt.Side
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicThetaSeriesComparisonIndepScalarsErrorsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicThetaSeriesComparison_indep_scalars_errors : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) kap lam err, Nonempty (GlobalTheory.SeriesTie.ExportTie s.YS s.v₀) → Nonempty (GlobalTheory.SeriesTie.ExportTie (s.upd kap lam err).YS (s.upd kap lam err).v₀) := by
  first | exact @GlobalTheory.PlugPt.Side.exportTie_upd | exact GlobalTheory.PlugPt.Side.exportTie_upd | (intros; apply GlobalTheory.PlugPt.Side.exportTie_upd <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt


set_option maxHeartbeats 1000000 in
theorem side_upd_ties_rays : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) (EX : ErrX D) (xd : ThData D) kap lam err,
    (s.Ties EX xd → (s.upd kap lam err).Ties EX xd) ∧ (s.Rays → (s.upd kap lam err).Rays) := by
  intro D nch s EX xd kap lam err
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact
      { frame := h.frame
        tied := h.tied
        series := GlobalTheory.T.adelicThetaSeriesComparison_indep_scalars_errors D nch s kap lam err h.series
        level := h.level
        data := h.data
        psi := h.psi
        psiVal := h.psiVal
        small := h.small
        types := h.types }
  · exact h

end GlobalTheory.PlugPt
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesUpdate_preserves_parameterFreeConditions_rayFields : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) (EX : ErrX D) (xd : ThData D) kap lam err, (s.Ties EX xd → (s.upd kap lam err).Ties EX xd) ∧ (s.Rays → (s.upd kap lam err).Rays) := by
  first | exact @GlobalTheory.PlugPt.side_upd_ties_rays | exact GlobalTheory.PlugPt.side_upd_ties_rays | (intros; apply GlobalTheory.PlugPt.side_upd_ties_rays <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SmallFrameAtColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SmallFrameAtColumn
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2
  GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmallExact

theorem normDescent : ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (n : ℕ)
    (𝔓 : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E), (Ideal.absNorm 𝔓.asIdeal).Prime → 𝔓.asIdeal = Ideal.span {π} →
    π - 1 ∈ Ideal.span {(n : 𝓞 E)} → ∃ 𝔭 : HeightOneSpectrum (𝓞 K),
      𝔓.asIdeal.comap (algebraMap (𝓞 K) (𝓞 E)) = 𝔭.asIdeal ∧ Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal ∧
      ∃ α : 𝓞 K, 𝔭.asIdeal = Ideal.span {α} ∧ α - 1 ∈ Ideal.span {(n : 𝓞 K)} := by
  intro K E _ _ _ _ _ n 𝔓 π hp hπ hπ1
  haveI := 𝔓.isMaximal
  set q := 𝔓.asIdeal with hq
  set p := q.under (𝓞 K) with hpd
  haveI : p.IsMaximal := inferInstance
  have hrel : Ideal.relNorm (𝓞 K) q = p ^ q.inertiaDeg (𝓞 K) := Ideal.relNorm_eq_pow_of_isMaximal q p
  have hab : Ideal.absNorm q = Ideal.absNorm p ^ q.inertiaDeg (𝓞 K) := by
    rw [← map_pow Ideal.absNorm p, ← hrel, Ideal.absNorm_relNorm]
  have h := (Nat.Prime.pow_eq_iff hp).1 hab.symm
  have hne : p ≠ ⊥ := fun h0 => by
    have : Ideal.absNorm p = 0 := by rw [h0]; simp
    rw [this] at h
    exact hp.ne_zero h.1.symm
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, inferInstance, hne⟩
  refine ⟨𝔭, rfl, h.1.symm, Algebra.intNorm (𝓞 K) (𝓞 E) π, ?_, ?_⟩
  · change p = _
    calc p = p ^ q.inertiaDeg (𝓞 K) := by rw [h.2, pow_one]
      _ = Ideal.relNorm (𝓞 K) q := hrel.symm
      _ = _ := by rw [hπ, Ideal.relNorm_singleton]
  · exact Ideal.mem_span_singleton.2
      (GlobalTheory.RayDescent.dvd_intNorm_sub_one K E n π (Ideal.mem_span_singleton.1 hπ1))

theorem rayLe : ∀ (K E L Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] [Algebra K E] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field Ω]
    [Algebra E Ω] [Algebra K Ω] [IsScalarTower K E Ω] (n : ℕ), 0 < n →
    GlobalTheory.FieldSize.IsRay L (Ideal.span {(n : 𝓞 K)}) → ∀ (R : IntermediateField E Ω) [NumberField R] [IsAbelianGalois E R],
    GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 E)}) → ∀ (j : L →ₐ[K] Ω) (x : L), j x ∈ R := by
  intro K E L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n hn hL R _ _ hR j x
  classical
  let b := Module.Free.chooseBasis K L
  let M' : IntermediateField E Ω := IntermediateField.adjoin E (Set.range fun i => j (b i))
  have hint : ∀ z ∈ Set.range (fun i => j (b i)), IsIntegral E z := by
    rintro _ ⟨i, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := K) (b i)).map j).tower_top
  haveI : FiniteDimensional E M' := IntermediateField.finiteDimensional_adjoin hint
  haveI : NumberField M' := NumberField.of_module_finite E M'
  have hmem : ∀ y, j y ∈ M' := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply K E Ω]
    exact mul_mem (M'.algebraMap_mem _) (IntermediateField.subset_adjoin E _ ⟨i, rfl⟩)
  let f : L →ₐ[K] M' :=
    { toFun := fun y => ⟨j y, hmem y⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' := fun y z => Subtype.ext (map_mul j y z)
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun y z => Subtype.ext (map_add j y z)
      commutes' := fun c => Subtype.ext (j.commutes c) }
  have hgen : ∀ (N : Type) [Field N] [Algebra E N] (g g' : M' →ₐ[E] N), (∀ y, g (f y) = g' (f y)) → g = g' := by
    intro N _ _ g g' hg
    refine IntermediateField.adjoin_algHom_ext E fun z hz => ?_
    obtain ⟨i, rfl⟩ := hz
    exact hg (b i)
  have hle : M' ≤ R := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split E Ω R M' ?_
    have hne : Ideal.span {(n : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hn.ne'
    refine (Ideal.finite_factors hne).subset ?_
    rintro 𝔓 ⟨hp, hsplR, hnot⟩
    by_contra hdvd
    apply hnot
    have hn𝔓 : (n : 𝓞 E) ∉ 𝔓.asIdeal := fun h =>
      hdvd (Ideal.dvd_iff_le.2 (Ideal.span_singleton_le_iff_mem _ |>.2 h))
    obtain ⟨π, hπ, hπ1⟩ := (GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff E R n hn hR 𝔓 hn𝔓).1 hsplR
    obtain ⟨𝔭, hover, hnorm, α, hα, hα1⟩ := normDescent K E n 𝔓 π hp hπ hπ1
    have hn𝔭 : (n : 𝓞 K) ∉ 𝔭.asIdeal := fun h => hn𝔓 (by
      rw [← hover, Ideal.mem_comap, map_natCast] at h
      exact h)
    have hsplL := (GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff K L n hn hL 𝔭 hn𝔭).2 ⟨α, hα, hα1⟩
    exact GlobalTheory.SplitCompositum.ncard_eq_finrank_of_generated K E L M' f hgen 𝔭 𝔓 hover hnorm hsplL
  exact hle (hmem x)

theorem rayLeC : ∀ (K E L : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] [Algebra K E] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (n : ℕ), 0 < n →
    GlobalTheory.FieldSize.IsRay L (Ideal.span {(n : 𝓞 K)}) → ∀ (φ : E →+* ℂ) (M : IntermediateField ℚ ℂ),
    GlobalTheory.Mem.Fld.IsRayFieldIn φ (GlobalTheory.Mem.Fld.natIdeal E n) M →
    ∃ j : L →+* ℂ, j.comp (algebraMap K L) = φ.comp (algebraMap K E) ∧ ∀ x, j x ∈ M := by
  intro K E L _ _ _ _ _ _ _ _ _ _ _ n hn hL φ M hM
  obtain ⟨hm, hNF, hray⟩ := hM
  letI := hNF
  letI : Algebra E M := GlobalTheory.Mem.Fld.algOf φ M hm
  letI : Algebra E ℂ := φ.toAlgebra
  letI : Algebra K ℂ := ((algebraMap E ℂ).comp (algebraMap K E)).toAlgebra
  haveI : IsScalarTower K E ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let R : IntermediateField E ℂ := M.toSubfield.toIntermediateField hm
  let e : M ≃ₐ[E] R :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : FiniteDimensional ℚ R := e.toRingEquiv.toRatAlgEquiv.toLinearEquiv.finiteDimensional
  haveI : NumberField R := NumberField.of_module_finite ℚ _
  have hR : GlobalTheory.Mem.Fld.IsRayField E R (GlobalTheory.Mem.Fld.natIdeal E n) := hray.of_algEquiv e
  haveI : IsAbelianGalois E R := hR.1
  let j : L →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hsub := rayLe K E L ℂ n hn hL R hR.2 j
  exact ⟨(j : L →+* ℂ), j.comp_algebraMap, fun x => hsub x⟩

theorem smallHas_of_rayField : GlobalTheory.NT.RayField → ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T)
    (Z : w.Lt), SmallHas (w.D Z) (Fr.at (w.st Z) f) := by
  intro hRF B f T w Z
  have hLL0 : ∀ z ∈ B.fixedCoefficientFieldInComplex, z ∈ (Formalism.L2.Host.embLL0 (w.D Z)).fieldRange := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hKs : ∀ z ∈ B.KsC, z ∈ (Formalism.L2.Host.embLL0 (w.D Z)).fieldRange := fun z hz => hLL0 z (B.KsC_le_LL0C hz)
  refine ⟨w.val _ _ _ _ _ _, ?_, ?_⟩
  · have hN : GlobalTheory.Mem.Fld.modulus B.toPre ≠ 0 := GlobalTheory.Mem.Fld.modulus_ne_zero _
    have hray : w.δ.ray ≤ B.KsC := ((GlobalTheory.Mem.Fld.listField_le_iff _ _).1 (le_of_eq w.exact.symm)).2.2.1
    haveI := GlobalTheory.Mem.NormPrime.isTotallyComplex_K B.host
    have h0 : Ideal.span {((GlobalTheory.Mem.Fld.modulus B.toPre : ℕ) : 𝓞 B.host.K)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN
    obtain ⟨L, _, _, _, hab, hun, hgen, hart⟩ := hRF B.host.K _ h0
    obtain ⟨j, hj, hjM⟩ := rayLeC B.host.K B.host.E L (GlobalTheory.Mem.Fld.modulus B.toPre) (Nat.pos_of_ne_zero hN)
      ⟨hun, hgen, hart⟩ B.host.φ₀ w.δ.ray w.δ.isRay
    exact ⟨L, _, _, _, hab, ⟨hun, hgen, hart⟩, j, hj, fun x => hKs _ (hray (hjM x))⟩
  · intro k z hz
    have hg := B.host.g_prime k
    have hz' : z ∈ GlobalTheory.Mem.Fld.cycField (B.host.g k * (B.host.g k - 1)) :=
      GlobalTheory.Mem.Fld.mem_cycField (mul_ne_zero hg.ne_zero (by have := hg.two_le; omega)) hz
    have hle : GlobalTheory.Mem.Fld.cycField (B.host.g k * (B.host.g k - 1)) ≤ GlobalTheory.Mem.Fld.rootsField B.toPre := by
      fin_cases k
      · exact ((le_sup_right.trans le_sup_left).trans le_sup_left).trans le_sup_left
      · exact (le_sup_right.trans le_sup_left).trans le_sup_left
    exact hKs _ (B.rootsField_le_KsC (hle hz'))

end GlobalTheory.SmallExact

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SmallFrameAtColumnStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_frame_at_column : GlobalTheory.NT.RayField → ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SmallHas (w.D Z) (Fr.at (w.st Z) f) := by
  first | exact @GlobalTheory.SmallExact.smallHas_of_rayField | exact GlobalTheory.SmallExact.smallHas_of_rayField | (intros; apply GlobalTheory.SmallExact.smallHas_of_rayField <;> assumption)
end
end
