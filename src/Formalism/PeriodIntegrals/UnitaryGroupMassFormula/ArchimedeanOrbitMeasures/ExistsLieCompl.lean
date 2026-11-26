module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfStd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RmulFactsHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsLieCompl
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

section Lie

variable {V : Type} [Fintype V] {n : ℕ}

def lieK (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) : Submodule ℝ (V → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
    ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0}
  zero_mem' := by intro v; simp
  add_mem' := by
    intro A B hA hB v
    refine ⟨?_, fun i hi j hj => ?_⟩
    · have e : (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) =
          ((A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * A v) +
            ((B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * B v) := by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
      show (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) = 0
      rw [e, (hA v).1, (hB v).1, add_zero]
    · show A v i j + B v i j = 0
      rw [(hA v).2 i hi j hj, (hB v).2 i hi j hj, add_zero]
  smul_mem' := by
    intro c A hA v
    refine ⟨?_, fun i hi j hj => ?_⟩
    · show (c • A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (c • A v) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hA v).1,
        smul_zero]
    · show c • A v i j = 0
      rw [(hA v).2 i hi j hj, smul_zero]

def entL (V : Type) [Fintype V] (n : ℕ) :
    (V → Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] EuclideanSpace ℂ (V × Fin n × Fin n) :=
  ({ toFun := fun M p => M p.1 p.2.1 p.2.2
     invFun := fun f v i j => f (v, i, j)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } : (V → Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] (V × Fin n × Fin n → ℂ)).trans
    ((EuclideanSpace.equiv (V × Fin n × Fin n) ℂ).toLinearEquiv.restrictScalars ℝ).symm

theorem entL_apply (M : V → Matrix (Fin n) (Fin n) ℂ) (p : V × Fin n × Fin n) :
    (EuclideanSpace.equiv (V × Fin n × Fin n) ℂ) (entL V n M) p = M p.1 p.2.1 p.2.2 := by
  simp [entL] <;> rfl

theorem norm_entL_sq (M : V → Matrix (Fin n) (Fin n) ℂ) :
    ‖entL V n M‖ ^ 2 = ∑ v, ∑ i, ∑ j, ‖M v i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := entL_apply M (v, i, j)
  simp only [EuclideanSpace.equiv] at this
  rw [← this]
  rfl

theorem exists_lieCompl (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)),
      (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧
        ∀ i ∈ S v, ∀ j ∈ S v, L x v i j = 0) ∧
      (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
      ∀ M : V → Matrix (Fin n) (Fin n) ℂ,
        (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0) →
          ∃ x, L x = M := by
  set K' : Submodule ℝ (EuclideanSpace ℂ (V × Fin n × Fin n)) := (lieK ε S).map (entL V n).toLinearMap with hK'
  let b := stdOrthonormalBasis ℝ K'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ K')) →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    (entL V n).symm.toLinearMap ∘ₗ K'.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap
  have hLe : ∀ x, entL V n (L x) = (b.repr.symm x : EuclideanSpace ℂ (V × Fin n × Fin n)) := by
    intro x; simp [L]
  have hLK : ∀ x, L x ∈ lieK ε S := by
    intro x
    obtain ⟨M, hM, hMe⟩ := (b.repr.symm x).2
    have : L x = M := by
      apply (entL V n).injective
      rw [hLe]; exact hMe.symm
    rw [this]; exact hM
  refine ⟨Fin (Module.finrank ℝ K'), inferInstance, L, fun x v => hLK x v, fun x => ?_, fun M hM => ?_⟩
  · rw [← norm_entL_sq, hLe]
    exact congrArg (· ^ 2) (b.repr.symm.norm_map x)
  · have hM' : entL V n M ∈ K' := ⟨M, hM, rfl⟩
    refine ⟨b.repr ⟨entL V n M, hM'⟩, ?_⟩
    apply (entL V n).injective
    rw [hLe, LinearIsometryEquiv.symm_apply_apply]

end Lie

def StdConjEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    ∃ (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)), StdConj X hb u' c S

theorem stdDataEx_of (h : StdConjEx) : StdDataEx := by
  intro D X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨c, S, hc⟩ := h X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨ι, hι, L, h1, h2, h3⟩ := exists_lieCompl X.B.I.ε S
  exact ⟨c, S, ι, hι, L, hc, ⟨h1, h2, h3⟩⟩

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UnitsOpenTens
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPolD
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem gramR_Y0_eq_TI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) :
    gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
  rw [show Y0 X u' = orbM X u' 1 from (one_smul _ _).symm, orbM, gramR_smul, gramR_ratTup]
  rfl

theorem indI_of_gram {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) (Y : TupI X)
    (hY : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _)) :
    Y ∈ IndI X := by
  have e1 := orbM_mem X u' hT hd 1
  have e0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y =
      gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (orbM X u' 1) := by rw [hY, e1.1]
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [e0, e1.1]
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem fib_near (hR : RmulFacts) (hF : FibAllT) (hC : MassDataMassesW.HinfCompact) {D : D7} (X : HidaSetting D)
    (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf
    (hP : PushHyp X u' ψ hT μinf νinf fibInf) (T : HmI X) (a : MfI X) (hunit : IsUnit a)
    (hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X a (Y0 X u')) = (T : Matrix _ _ _))
    (hind : ∀ Y : TupI X, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = (T : Matrix _ _ _) → Y ∈ IndI X) :
    ∃ c : ENNReal, fibInf T = c • X.measG.μGinf.map (fun g => g • rmulT X a (Y0 X u')) := by
  obtain ⟨hmr, hcomp, hsmul, hgram, hcTmul, hcT1, hKm, hrc⟩ := hR X
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hfib := hP.2.2.2.2.2.2
  obtain ⟨hinvT, hlfT⟩ := hF X u' ψ hT μinf νinf fibInf hP T
  set b : MfI X := ↑hunit.unit⁻¹ with hb
  have hab : a * b = 1 := hunit.mul_val_inv
  have hba : b * a = 1 := hunit.val_inv_mul
  have hab' : ∀ Y, rmulT X a (rmulT X b Y) = Y := fun Y => by rw [hcomp, hba, rmulT_one]
  have hba' : ∀ Y, rmulT X b (rmulT X a Y) = Y := fun Y => by rw [hcomp, hab, rmulT_one]
  set ν := (fibInf T).map (rmulT X b) with hν
  have i1 : InvI X ν := by
    intro g
    rw [hν, Measure.map_map (measurable_smul_tupI X g) (hmr b)]
    have : ((fun y => g • y) ∘ rmulT X b) = rmulT X b ∘ (fun y => g • y) := funext fun y => hsmul g b y
    rw [this, ← Measure.map_map (hmr b) (measurable_smul_tupI X g), hinvT g]
  have hS : fibInf T (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1} ∩ IndI X)ᶜ = 0 :=
    hfib.1 T
  have s1 : ν (FbI X u' hT)ᶜ = 0 := by
    rw [hν, Measure.map_apply (hmr b) (measurableSet_FbI X u' hT).compl]
    refine measure_mono_null ?_ hS
    intro y hy hy2
    apply hy
    have hg : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X b y) = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
      rw [hgram, hy2.1, ← hgT, hgram, gramR_Y0_eq_TI X u' hT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hcTmul,
        Matrix.mul_assoc, hab, hcT1, Matrix.one_mul, Matrix.mul_one]
    exact ⟨hg, indI_of_gram X u' hT hd _ hg⟩
  have l1 : LFI X ν := by
    intro K hK hKI
    rw [hν, Measure.map_apply (hmr b) (hKm K hK)]
    have hpre : rmulT X b ⁻¹' K = rmulT X a '' K := by
      ext y
      constructor
      · intro hy; exact ⟨rmulT X b y, hy, hab' y⟩
      · rintro ⟨k, hk, rfl⟩; show rmulT X b (rmulT X a k) ∈ K; rw [hba']; exact hk
    rw [hpre]
    have hcl : IsClosed (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) := by
      haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
      exact isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    have hK2 : IsCompact (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) :=
      (hK.image (hrc a)).inter_right hcl
    calc fibInf T (rmulT X a '' K)
        ≤ fibInf T (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) +
          fibInf T (rmulT X a '' K \ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) :=
          measure_le_inter_add_sdiff _ _ _
      _ = fibInf T (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) := by
          have h0 : fibInf T (rmulT X a '' K \ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) = 0 := by
            refine measure_mono_null ?_ hS
            intro y hy hy2
            exact hy.2 hy2.1
          rw [h0, add_zero]
      _ < ⊤ := hlfT _ hK2 (fun y hy => hind y hy.2)
  obtain ⟨c, -, hc⟩ := orbRep_of_witt wittInf_holds hC X u' ψ hT μinf νinf fibInf hP ν i1 s1 l1
  refine ⟨c, ?_⟩
  have e1 : fibInf T = ν.map (rmulT X a) := by
    rw [hν, Measure.map_map (hmr a) (hmr b)]
    have : rmulT X a ∘ rmulT X b = id := funext hab'
    rw [this, Measure.map_id]
  have e2 : (fun g => g • rmulT X a (Y0 X u')) = rmulT X a ∘ orbM X u' :=
    funext fun g => hsmul g a (Y0 X u')
  rw [e1, hc, Measure.map_smul, e2, Measure.map_map (hmr a) (measurable_orbM X u')]
  exact (hmr a).aemeasurable

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def UnitsOpenTens : Prop := ∀ {D : D7} (X : HidaSetting D), IsOpen {z : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit z}

theorem isUnit_det_TI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) :
    IsUnit (TI X u' hT).1.det := by
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem nearFacts_of (hU : UnitsOpenTens) : NearFacts := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hCh
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨hmr, hcomp, hsmul, hgram, hcTmul, hcT1, -, -⟩ := rmulFacts_holds X
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hdetc : ContinuousAt (fun T => (a T).det) (TI X u' hT) :=
    (continuous_id.matrix_det).continuousAt.comp hCh.2.2.1
  have hU1 : {T | IsUnit (a T).det} ∈ 𝓝 (TI X u' hT) :=
    hdetc.preimage_mem_nhds ((hU X).mem_nhds (by
      show IsUnit (a (TI X u' hT)).det
      rw [hCh.2.1, Matrix.det_one]; exact isUnit_one))
  refine ⟨Ω ∩ {T | IsUnit (a T).det}, Set.inter_subset_left, Filter.inter_mem hCh.1 hU1, fun T hT1 =>
    ⟨(Matrix.isUnit_iff_isUnit_det _).2 hT1.2, fun Y hY => ?_⟩⟩
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [hY, ← hCh.2.2.2 T hT1.1, hgram, gramR_Y0_eq_TI X u' hT, Matrix.det_mul, Matrix.det_mul]
  have hc : (cTI X (a T)).det = sigR (Ainf X.B.I.F) X.B.I.cm.sig (a T).det := by
    rw [cTI, Matrix.det_transpose, RingHom.map_det]
    rfl
  rw [hc]
  exact ((hT1.2.map _).mul (isUnit_det_TI X u' hT hd)).mul hT1.2

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpParts
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Matrix Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
theorem continuous_matExp (n : ℕ) : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
  open scoped Norms.Operator in NormedSpace.exp_continuous

theorem continuous_expU {n : ℕ} (ε : Fin n → Bool) {Y : Type} [TopologicalSpace Y]
    (f : Y → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f)
    (hL : ∀ y, (f y)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * f y = 0) : Continuous (fun y => expU ε (f y)) := by
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · have e : (Units.val ∘ Subtype.val ∘ fun y => expU ε (f y)) = fun y => NormedSpace.exp (f y) :=
      funext fun y => expU_val ε _ (hL y)
    rw [e]
    exact (continuous_matExp n).comp hf
  · have e : (fun x => ((((Subtype.val ∘ fun y => expU ε (f y)) x)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = fun y => NormedSpace.exp (-f y) := by
      funext y
      apply Units.inv_eq_of_mul_eq_one_right
      show (((expU ε (f y) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        NormedSpace.exp (-f y) = 1
      rw [expU_val ε _ (hL y), ← Matrix.exp_add_of_commute (f y) (-f y) (Commute.neg_right (Commute.refl (f y))), add_neg_cancel,
        NormedSpace.exp_zero]
    rw [e]
    exact (continuous_matExp n).comp hf.neg

theorem continuous_kap0_of_lieCompl {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (hL : LieCompl X S L) : Continuous (kap0 X hb c L) := by
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hg : Continuous (fun x => ((fun v => expU (X.B.I.ε v) (L x v)) : X.B.I.Ginf)) :=
    continuous_pi fun v => continuous_expU _ (fun x => L x v) ((continuous_apply v).comp hLc)
      (fun x => (hL.1 x v).1)
  exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul hg).mul continuous_const)

def chiOf {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf) {η : Type}
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (y : EuclideanSpace ℝ η) : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  X.toInf hb (c * (fun v => expU (X.B.I.ε v) (L₁ y v)) * c⁻¹)

def BlockLie {D : D7} (X : HidaSetting D) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {η : Type}
    [Fintype η]
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) :
    Prop :=
  (∀ y v, (L₁ y v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * L₁ y v = 0 ∧
    ∀ i j, (i ∉ S v ∨ j ∉ S v) → L₁ y v i j = 0) ∧
  (∀ y, ∑ v, ∑ i, ∑ j, ‖L₁ y v i j‖ ^ 2 = ‖y‖ ^ 2) ∧
  ∀ M : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
    (∀ v, (M v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * M v = 0 ∧
      ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0) → ∃ y, L₁ y = M

def BlockEx : Prop := ∀ {D : D7} (X : HidaSetting D) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)),
    ∃ (η : Type) (_ : Fintype η)
      (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
      BlockLie X S L₁

def StdCtx {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι η : Type} [Fintype ι] [Fintype η]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) : Prop :=
  (∃ ψ : AddChar (AF X.B.I.F) ℂ, ∃ hT μinf νinf fibInf, PushHyp X u' ψ hT μinf νinf fibInf) ∧
    StdConj X hb u' c S ∧ LieCompl X S L ∧ BlockLie X S L₁

def ChiStab : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∀ y, chiOf X hb c L₁ y ∈
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u')

def GrpDens : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∃ r : ℝ, 0 < r ∧ ∃ d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt d 0 ∧ d 0 = Formalism.MainNotions.S.AutInst.gaugeU X.B.I ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        X.measG.μGinf ((fun p => kap0 X hb c L p.1 * chiOf X hb c L₁ p.2) '' A) = ∫⁻ p in A, ENNReal.ofReal (d p)

def GrpHaarH : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∀ hS : ∀ y, chiOf X hb c L₁ y ∈
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'),
    ∃ (ν : Measure (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) (r : ℝ)
      (e : EuclideanSpace ℝ η → ℝ),
      ν.IsMulLeftInvariant ∧ SFinite ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≠ ⊤ ∧ 0 < r ∧ ContinuousAt e 0 ∧ 0 < e 0 ∧
      (ν Set.univ).toReal / e 0 = Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) ∧
      ∀ s, 0 < s → s ≤ r → ν ((fun y => (⟨chiOf X hb c L₁ y, hS y⟩ :
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) '' ball 0 s) =
        ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)

def GrpInj : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∃ r : ℝ, 0 < r ∧
      (∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r,
        (kap0 X hb c L a)⁻¹ * kap0 X hb c L b ∈
          MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') → a = b) ∧
      Set.InjOn (chiOf X hb c L₁) (ball 0 r)

theorem grpPiecesStd_of (h0 : BlockEx) (hS : ChiStab) (hD : GrpDens) (hH : GrpHaarH) (hI : GrpInj) :
    GrpPiecesStd := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
  obtain ⟨η, hη, L₁, hB⟩ := h0 X S
  have ctx : StdCtx X u' hb c S L L₁ := ⟨⟨ψ, hT, μinf, νinf, fibInf, hP⟩, hc, hL, hB⟩
  have hst := hS X u' hb c S L L₁ ctx
  obtain ⟨r1, hr1, d, hdc, hd0, hdens⟩ := hD X u' hb c S L L₁ ctx
  obtain ⟨ν, r2, e, hL', hSF, h0', hf, hr2, hec, he0, hvol, hνd⟩ := hH X u' hb c S L L₁ ctx hst
  obtain ⟨r3, hr3, hinj, hχi⟩ := hI X u' hb c S L L₁ ctx
  have hr : 0 < min r1 (min r2 r3) := lt_min hr1 (lt_min hr2 hr3)
  have h1 : min r1 (min r2 r3) ≤ r1 := min_le_left _ _
  have h2 : min r1 (min r2 r3) ≤ r2 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min r1 (min r2 r3) ≤ r3 := (min_le_right _ _).trans (min_le_right _ _)
  have hχc : Continuous (fun y => (⟨chiOf X hb c L₁ y, hst y⟩ :
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) := by
    apply Continuous.subtype_mk
    have hLc : Continuous L₁ := L₁.continuous_of_finiteDimensional
    exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul (continuous_pi fun v =>
      continuous_expU _ (fun y => L₁ y v) ((continuous_apply v).comp hLc) (fun y => (hB.1 y v).1))).mul
        continuous_const)
  have hgpos : 0 < Formalism.MainNotions.S.AutInst.gaugeU X.B.I := Finset.prod_pos fun v _ => (hP.2.2.2.1 v).2
  have hdet1 : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).det = 1 := by
    simp [ContinuousLinearMap.det]
  refine ⟨η, hη, fun y => ⟨chiOf X hb c L₁ y, hst y⟩, min r1 (min r2 r3),
    fun p => kap0 X hb c L p.1 * chiOf X hb c L₁ p.2, ball 0 (min r1 (min r2 r3)), d, id,
    fun _ => ContinuousLinearMap.id ℝ _, e, ν, hL', hSF, h0', hf, hr,
    (continuous_kap0_of_lieCompl X hb c S L hL).continuousOn, hχc.continuousOn, ?_, ?_, ?_, ?_, Set.injOn_id _, ?_, ?_, ?_,
    continuousAt_id, ?_, hdc, hec, he0, ?_, ?_⟩
  · intro a ha b hb' hab
    exact hχi (ball_subset_ball h3 ha) (ball_subset_ball h3 hb') (congrArg Subtype.val hab)
  · intro a ha b hb' hm
    exact hinj a (ball_subset_ball h3 ha) b (ball_subset_ball h3 hb') hm
  · intro A hA hAm
    exact hdens A (hA.trans (ball_subset_ball h1)) hAm
  · intro p _
    exact hasFDerivWithinAt_id p _
  · rw [Set.image_id]
  · intro p _
    rfl
  · intro s hs hsr
    exact hνd s hs (hsr.trans h2)
  · simp only [hdet1]
    exact continuousAt_const
  · simp only [hdet1, abs_one, one_mul, id]
    rw [hd0]
    exact hgpos
  · simp only [hdet1, abs_one, one_mul, id]
    rw [hd0, gVal, ← hvol]
    ring


set_option backward.isDefEq.respectTransparency false in
theorem exp_mul_of_mul_eq_zero {n : ℕ} (M P : Matrix (Fin n) (Fin n) ℂ) (hMP : M * P = 0) :
    NormedSpace.exp M * P = P := by
  open scoped Norms.Operator in
  have hs : Summable (fun k : ℕ => ((k.factorial : ℚ)⁻¹) • M ^ k) := NormedSpace.expSeries_summable' (𝕂 := ℚ) M
  rw [NormedSpace.exp_eq_tsum_rat, ← hs.tsum_mul_right P, tsum_eq_single 0]
  · simp
  · intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [smul_mul_assoc, pow_succ, Matrix.mul_assoc, hMP, Matrix.mul_zero, smul_zero]

theorem exp_block_col {n : ℕ} (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) (i : Fin n) (hi : i ∉ S) (j : Fin n) :
    NormedSpace.exp M j i = if j = i then 1 else 0 := by
  have hMP : M * Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) = 0 := by
    ext a b
    rw [Matrix.mul_diagonal]
    by_cases hb : b ∈ S
    · simp [hb]
    · simp [hb, hM a b (Or.inr hb)]
  have h := congrFun (congrFun (exp_mul_of_mul_eq_zero M _ hMP) j) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_apply] at h
  simp only [hi, if_false, mul_one] at h
  rw [h]
  by_cases hji : j = i
  · subst hji
    simp [hi]
  · simp [hji]

theorem chiStab' : ChiStab := by
  intro D X u' hb c S ι η _ _ L L₁ ctx y
  unfold chiOf
  refine (ctx.2.1.2 _).2 fun v i hi j => ?_
  show (((expU (X.B.I.ε v) (L₁ y v) : Formalism.REAL.UJ (X.B.I.ε v)) :
    (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) j i = _
  rw [expU_val _ _ (ctx.2.2.2.1 y v).1]
  exact exp_block_col (S v) _ (ctx.2.2.2.1 y v).2 i hi j

end PI.AprimeInfW
end
end
