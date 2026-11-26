module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceV

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpHaarW
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

def UstdSub {n : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := {g | InStd S g}
  one_mem' := by
    intro i _ j
    show (1 : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [Matrix.one_apply]
  mul_mem' := by
    intro g h hg hh i hi j
    have e : (((g * h : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
          ((h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := rfl
    show (((g * h : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [e, Matrix.mul_apply]
    simp_rw [hh i hi]
    simp [hg i hi j]
  inv_mem' := by
    intro g hg i hi j
    have e : ((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ))⁻¹ := rfl
    have h1 : (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 := Units.inv_mul _
    have h2 := congrFun (congrFun h1 j) i
    rw [Matrix.mul_apply] at h2
    simp_rw [hg i hi] at h2
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply] at h2
    show ((((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [e, h2]

def BlockHaarV : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (S : Finset (Fin n)) (k : ℕ), S.card = k →
    (∀ i ∈ S, ε i = true) → Formalism.MainNotions.S.Gauge.GaugeDens ε →
    ∃ (β : Type) (_ : Fintype β) (L₁ : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
      (P₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ β) (ν : Measure (UstdSub ε S)) (r : ℝ)
      (e : EuclideanSpace ℝ β → ℝ) (hmem : ∀ y, expU ε (L₁ y) ∈ UstdSub ε S),
      (∀ z, P₁ (L₁ z) = z) ∧ (∀ M, InBlock ε S M → L₁ (P₁ M) = M) ∧ (∀ z, InBlock ε S (L₁ z)) ∧
      (∀ z, frob (L₁ z) = ‖z‖ ^ 2) ∧
      ν.IsMulLeftInvariant ∧ IsFiniteMeasure ν ∧ ν Set.univ ≠ 0 ∧ 0 < r ∧ Measurable e ∧ (∀ z, 0 ≤ e z) ∧
      ContinuousAt e 0 ∧ 0 < e 0 ∧ (ν Set.univ).toReal / e 0 = Formalism.MainNotions.S.UnitaryVolumeMass.volU k ∧
      Continuous (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) ∧
      Set.InjOn (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) (ball 0 r) ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ β) r, MeasurableSet A →
        ν ((fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) '' A) = ∫⁻ y in A, ENNReal.ofReal (e y)

theorem grpHaarH_of (hBH : BlockHaarV) : GrpHaarH := by
  intro D X u' hb c S ι η _ _ L L₁ ctx hS
  obtain ⟨⟨ψ', hT, μinf, νinf, fibInf, hP⟩, hc, hL, hB⟩ := ctx
  have hgd : ∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v) := hP.2.2.2.1
  choose β hβ L1 P1 ν r e hmem h1 h2 h3 h4 hνL hνF hν0 hr hem hen hec he0 hrat hcont hinj hdens using
    fun v => hBH X.B.I.n (X.B.I.ε v) (S v) D.R.k (hc.1 v).1 (hc.1 v).2 (hgd v)
  letI : ∀ v, Fintype (β v) := hβ
  have hUJ : ∀ v, SecondCountableTopology (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => Formalism.REAL.instSecondCountableUJ _ _
  have : ∀ v, SecondCountableTopology (UstdSub (X.B.I.ε v) (S v)) := fun v =>
    TopologicalSpace.Subtype.secondCountableTopology ((UstdSub (X.B.I.ε v) (S v) : Set (Formalism.REAL.UJ (X.B.I.ε v))))
  have : ∀ v, OpensMeasurableSpace (UstdSub (X.B.I.ε v) (S v)) := fun v => inferInstance
  have : OpensMeasurableSpace (∀ v, UstdSub (X.B.I.ε v) (S v)) := Pi.opensMeasurableSpace
  have : ∀ v, IsFiniteMeasure (ν v) := hνF
  have : ∀ v, (ν v).IsMulLeftInvariant := hνL
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  obtain ⟨hTyb, hTyn⟩ := coord_facts L₁ (fun v M => InBlock (X.B.I.ε v) (S v) M) L1 P1 h1 h2 h3 h4
    (fun y v => hB.1 y v) (fun y => hB.2.1 y) (fun M hM => hB.2.2 M hM)
  set Ty : EuclideanSpace ℝ η →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (β v)) :=
    LinearMap.pi fun v => (P1 v).comp ((LinearMap.proj v).comp L₁) with hTyd
  have hTym := PI.AprimeInfG.measurePreserving_of_normSq Ty hTyb hTyn
  let Tye : EuclideanSpace ℝ η ≃ᵐ (∀ v, EuclideanSpace ℝ (β v)) :=
    (LinearEquiv.ofBijective Ty hTyb).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hTye : MeasurePreserving Tye volume (Measure.pi fun _ => volume) := hTym
  have hTyv : ∀ y v, L1 v (Ty y v) = L₁ y v := fun y v => h2 v _ (hB.1 y v)

  let ψf : (∀ v, UstdSub (X.B.I.ε v) (S v)) →
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :=
    fun g => ⟨X.toInf hb (c * (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) * c⁻¹),
      (hc.2 _).2 fun v => (g v).2⟩
  let ψm : (∀ v, UstdSub (X.B.I.ε v) (S v)) →ₙ*
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :=
    { toFun := ψf
      map_mul' := fun g h => by
        apply Subtype.ext
        show toInfHom X hb _ = toInfHom X hb _ * toInfHom X hb _
        rw [← map_mul]
        congr 1
        have : (fun v => (((g * h) v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) =
            (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) *
              (fun v => ((h v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) := funext fun v => rfl
        rw [this]
        group }
  have hψc : Continuous ψm := by
    apply Continuous.subtype_mk
    exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul (continuous_pi fun v =>
      continuous_subtype_val.comp (continuous_apply v))).mul continuous_const)
  have hψi : Function.Injective ψm := by
    intro g h he
    have e1 := toInf_injective X hb (congrArg Subtype.val he)
    have e2 : (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) =
        (fun v => ((h v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) := by simpa using e1
    funext v
    exact Subtype.ext (congrFun e2 v)
  have hψs : Function.Surjective ψm := by
    intro hh
    obtain ⟨s, hs⟩ := PI.AprimeInfU.toInf_surjective X hb MassDataMassesW.splitIso_holds
      (hh : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    have hmemS : X.toInf hb (c * (c⁻¹ * s * c) * c⁻¹) ∈
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') := by
      rw [show c * (c⁻¹ * s * c) * c⁻¹ = s by group, hs]
      exact hh.2
    have hstd := (hc.2 _).1 hmemS
    refine ⟨fun v => ⟨(c⁻¹ * s * c) v, hstd v⟩, Subtype.ext ?_⟩
    show X.toInf hb (c * (c⁻¹ * s * c) * c⁻¹) = hh
    rw [show c * (c⁻¹ * s * c) * c⁻¹ = s by group, hs]

  let Φ : ∀ v, EuclideanSpace ℝ (β v) → UstdSub (X.B.I.ε v) (S v) :=
    fun v z => ⟨expU (X.B.I.ε v) (L1 v z), hmem v z⟩
  have hχ : ∀ y, (⟨chiOf X hb c L₁ y, hS y⟩ :
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u')) =
      ψm (fun v => Φ v (Ty y v)) := by
    intro y
    apply Subtype.ext
    show chiOf X hb c L₁ y = X.toInf hb (c * (fun v => expU (X.B.I.ε v) (L1 v (Ty y v))) * c⁻¹)
    unfold chiOf
    simp_rw [hTyv]
  set rr := (insert 1 (Finset.univ.image r)).min' ⟨1, Finset.mem_insert_self _ _⟩ with hrr
  have hrr0 : 0 < rr := by
    have hm := Finset.min'_mem (insert 1 (Finset.univ.image r)) ⟨1, Finset.mem_insert_self _ _⟩
    rcases Finset.mem_insert.1 hm with e' | e'
    · rw [hrr, e']; norm_num
    · obtain ⟨v, -, hv⟩ := Finset.mem_image.1 e'
      rw [hrr, ← hv]; exact hr v
  have hrrv : ∀ v, rr ≤ r v := fun v =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem r (Finset.mem_univ v)))
  have hTyle : ∀ y v, ‖Ty y v‖ ≤ ‖y‖ := by
    intro y v
    have : ‖Ty y v‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [← hTyn y]
      exact Finset.single_le_sum (f := fun v => ‖Ty y v‖ ^ 2) (fun v _ => sq_nonneg _) (Finset.mem_univ v)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have hT0 : ∀ v, Ty 0 v = 0 := fun v => by simp
  have hνu : (Measure.pi ν).map ψm Set.univ = ∏ v, ν v Set.univ := by
    rw [Measure.map_apply hψc.measurable MeasurableSet.univ, Set.preimage_univ, Measure.pi_univ]
  refine ⟨(Measure.pi ν).map ψm, rr, fun y => ∏ v, e v (Ty y v),
    isMulLeftInvariant_map ψm hψc.measurable hψs, inferInstance, ?_, ?_, hrr0, ?_, ?_, ?_, ?_⟩
  · rw [hνu]
    exact Finset.prod_ne_zero_iff.2 fun v _ => hν0 v
  · rw [hνu]
    exact ENNReal.prod_ne_top fun v _ => measure_ne_top _ _
  · refine tendsto_finsetProd _ fun v _ => ?_
    have hv : ContinuousAt (fun y : EuclideanSpace ℝ η => Ty y v) 0 :=
      ((continuous_apply v).comp Ty.continuous_of_finiteDimensional).continuousAt
    have hd : ContinuousAt (e v) (Ty 0 v) := by rw [hT0 v]; exact hec v
    have hdv := ContinuousAt.comp (f := fun y : EuclideanSpace ℝ η => Ty y v) hd hv
    exact hdv
  · simp only [hT0]
    exact Finset.prod_pos fun v _ => he0 v
  · rw [hνu, ENNReal.toReal_prod]
    simp only [hT0]
    rw [← Finset.prod_div_distrib]
    simp only [hrat, Finset.prod_const, Finset.card_univ]
  · intro s hs hsr
    have hB' : Ty '' ball 0 s ⊆ Set.univ.pi fun v => ball 0 (r v) := by
      rintro _ ⟨y, hy, rfl⟩ v -
      exact mem_ball_zero_iff.2 (((hTyle y v).trans_lt (mem_ball_zero_iff.1 hy)).trans_le (hsr.trans (hrrv v)))
    have hΦc : Continuous (fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) :=
      continuous_pi fun v => (hcont v).comp (continuous_apply v)
    have hΦi : Set.InjOn (fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v))
        (Set.univ.pi fun v => ball 0 (r v)) := by
      intro z hz z' hz' he'
      funext v
      exact hinj v (hz v (Set.mem_univ v)) (hz' v (Set.mem_univ v)) (congr_fun he' v)
    have hTA : MeasurableSet (Tye '' ball 0 s) := Tye.measurableSet_image.2 measurableSet_ball
    have hAi : MeasurableSet ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) :=
      hTA.image_of_continuousOn_injOn hΦc.continuousOn (hΦi.mono hB')
    have himg : (fun y => (⟨chiOf X hb c L₁ y, hS y⟩ :
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) '' ball 0 s =
        ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun y _ => hχ y
    have hmeasH : MeasurableSet (ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) ''
        (Tye '' ball 0 s))) := by
      have e3 : ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) =
          (fun y => ψm (fun v => Φ v (Ty y v))) '' ball 0 s := by
        rw [Set.image_image, Set.image_image]
        rfl
      rw [e3]
      refine measurableSet_ball.image_of_continuousOn_injOn ?_ ?_
      · exact (hψc.comp (hΦc.comp Ty.continuous_of_finiteDimensional)).continuousOn
      · intro y hy y' hy' he'
        have e4 := hψi he'
        have e5 : Ty y = Ty y' := hΦi (hB' ⟨y, hy, rfl⟩) (hB' ⟨y', hy', rfl⟩) e4
        exact hTyb.1 e5
    rw [himg, Measure.map_apply hψc.measurable hmeasH, hψi.preimage_image,
      PI.AprimeInfG.pi_chart_dens ν (fun _ => volume) Φ (fun v => (hcont v).measurable) (fun v => ball 0 (r v))
        (fun v => measurableSet_ball) hinj e hem hdens (Tye '' ball 0 s) hB' hTA hAi,
      ← hTye.setLIntegral_comp_emb Tye.measurableEmbedding]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_prod_of_nonneg fun v _ => hen v _]
    rfl

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTop
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEx
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

section Block

variable {V : Type} [Fintype V] {n : ℕ}

def lieB (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) : Submodule ℝ (V → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
    ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0}
  zero_mem' := by intro v; simp
  add_mem' := by
    intro A B hA hB v
    refine ⟨?_, fun i j hij => ?_⟩
    · have e : (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) =
          ((A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * A v) +
            ((B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * B v) := by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
      show (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) = 0
      rw [e, (hA v).1, (hB v).1, add_zero]
    · show A v i j + B v i j = 0
      rw [(hA v).2 i j hij, (hB v).2 i j hij, add_zero]
  smul_mem' := by
    intro c A hA v
    refine ⟨?_, fun i j hij => ?_⟩
    · show (c • A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (c • A v) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hA v).1,
        smul_zero]
    · show c • A v i j = 0
      rw [(hA v).2 i j hij, smul_zero]

theorem exists_lieBlock (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) :
    ∃ (η : Type) (_ : Fintype η) (L : EuclideanSpace ℝ η →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)),
      (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧
        ∀ i j, (i ∉ S v ∨ j ∉ S v) → L x v i j = 0) ∧
      (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
      ∀ M : V → Matrix (Fin n) (Fin n) ℂ,
        (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
          ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0) → ∃ x, L x = M := by
  set K' : Submodule ℝ (EuclideanSpace ℂ (V × Fin n × Fin n)) := (lieB ε S).map (entL V n).toLinearMap with hK'
  let b := stdOrthonormalBasis ℝ K'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ K')) →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    (entL V n).symm.toLinearMap ∘ₗ K'.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap
  have hLe : ∀ x, entL V n (L x) = (b.repr.symm x : EuclideanSpace ℂ (V × Fin n × Fin n)) := by
    intro x; simp [L]
  have hLK : ∀ x, L x ∈ lieB ε S := by
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

end Block

theorem blockEx_holds : BlockEx := by
  intro D X S
  obtain ⟨η, hη, L, h1, h2, h3⟩ := exists_lieBlock X.B.I.ε S
  exact ⟨η, hη, L, h1, h2, h3⟩

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

theorem grpDens_of_exp (hE : ExpProdU) : GrpDens :=
  grpDens_of (ginfDens_of (placeCharts_of (placeChartV_of hE))) unimodInf_holds

theorem grpStd_of_leaves (hE : ExpProdU) (hH : GrpHaarH) : GrpStd :=
  grpStd_of (grpPiecesStd_of blockEx_holds chiStab' (grpDens_of_exp hE) hH grpInj_holds)

theorem grpStd_of_exp_block (hE : ExpProdU) (hBH : BlockHaarV) : GrpStd :=
  grpStd_of_leaves hE (grpHaarH_of hBH)

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GaugeVolU
noncomputable section

namespace PI.AprimeInfW

theorem jm_true (k : ℕ) : Formalism.REAL.Jm (fun _ : Fin k => true) = 1 := by
  simp [Formalism.REAL.Jm]

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEmb
noncomputable section

namespace PI.AprimeInfG

open scoped Matrix

variable {n k : ℕ} {S : Finset (Fin n)}

def emb0 (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if h : i ∈ S ∧ j ∈ S then X (e.symm ⟨i, h.1⟩) (e.symm ⟨j, h.2⟩) else 0

def blockEmbeddingAddHom (e : Fin k ≃ S) : Matrix (Fin k) (Fin k) ℂ →+ Matrix (Fin n) (Fin n) ℂ where
  toFun := emb0 e
  map_zero' := by
    funext i j
    simp [emb0]
  map_add' X Y := by
    funext i j
    simp only [emb0, Matrix.add_apply]
    split_ifs <;> simp

private theorem emb0_apply_coe_coe (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    emb0 e X (e a) (e b) = X a b := by
  simp [emb0]

private theorem emb0_apply_of_left_not_mem (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) {i j : Fin n}
    (hi : i ∉ S) : emb0 e X i j = 0 := by
  simp [emb0, hi]

private theorem emb0_apply_of_right_not_mem (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) {i j : Fin n}
    (hj : j ∉ S) : emb0 e X i j = 0 := by
  simp [emb0, hj]

private theorem exists_equiv_coe_eq_of_mem (e : Fin k ≃ S) {i : Fin n} (hi : i ∈ S) :
    ∃ a, (e a : Fin n) = i :=
  ⟨e.symm ⟨i, hi⟩, by simp⟩

private theorem sum_eq_sum_equiv_of_eq_zero_of_not_mem {M : Type*} [AddCommMonoid M] (e : Fin k ≃ S) (F : Fin n → M)
    (hF : ∀ l, l ∉ S → F l = 0) : ∑ l, F l = ∑ c, F (e c) := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun l _ hl => hF l hl), ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp e (fun x : S => F x)).symm

theorem embed_mul (e : Fin k ≃ S) (X Y : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e (X * Y) = emb0 e X * emb0 e Y := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, Matrix.mul_apply, sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
      · simp only [emb0_apply_coe_coe]
      · intro l hl
        simp [emb0_apply_of_right_not_mem e X hl]
    · rw [emb0_apply_of_right_not_mem e _ hj]
      symm
      exact Finset.sum_eq_zero (fun l _ => by rw [emb0_apply_of_right_not_mem e Y hj, mul_zero])
  · rw [emb0_apply_of_left_not_mem e _ hi]
    symm
    exact Finset.sum_eq_zero (fun l _ => by rw [emb0_apply_of_left_not_mem e X hi, zero_mul])

theorem embed_pow_succ (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (m : ℕ) :
    emb0 e (X ^ (m + 1)) = emb0 e X ^ (m + 1) := by
  induction m with
  | zero => simp only [zero_add, pow_one]
  | succ m ih => rw [pow_succ, embed_mul, ih, ← pow_succ]

private theorem emb0Add_apply (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    blockEmbeddingAddHom e X = emb0 e X :=
  rfl

private theorem emb0_smul (e : Fin k ≃ S) (c : ℂ) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e (c • X) = c • emb0 e X := by
  ext i j
  rw [Matrix.smul_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.smul_apply]
    · rw [emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_right_not_mem e _ hj, smul_zero]
  · rw [emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_left_not_mem e _ hi, smul_zero]

theorem continuous_embed (e : Fin k ≃ S) : Continuous (emb0 e) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : i ∈ S ∧ j ∈ S
  · simp only [emb0, dif_pos h]
    exact continuous_id.matrix_elem _ _
  · simp only [emb0, dif_neg h]
    exact continuous_const


set_option backward.isDefEq.respectTransparency false in
theorem exp_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    NormedSpace.exp (emb0 e X) = emb0 e (NormedSpace.exp X) + (1 - emb0 e 1) := by
  letI : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (emb0 e X)
  have h3 := (h1.map (blockEmbeddingAddHom e) (continuous_embed e)).add
    (hasSum_ite_eq 0 (1 - emb0 e 1))
  refine h2.unique ?_
  convert h3 using 1
  all_goals try rfl
  funext m
  rcases m with _ | m
  · simp [emb0Add_apply]
  · simp [emb0Add_apply, emb0_smul, embed_pow_succ]

def resB (e : Fin k ≃ S) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => M (e a) (e b)

theorem restrict_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : resB e (emb0 e X) = X := by
  ext a b
  exact emb0_apply_coe_coe e X a b

theorem embed_restrict (e : Fin k ≃ S) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) :
    emb0 e (resB e M) = M := by
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe]
      rfl
    · rw [emb0_apply_of_right_not_mem e _ hj, hM i j (Or.inr hj)]
  · rw [emb0_apply_of_left_not_mem e _ hi, hM i j (Or.inl hi)]

theorem embed_conjTranspose (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e Xᴴ = (emb0 e X)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.conjTranspose_apply]
    · rw [emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_left_not_mem e _ hj, star_zero]
  · rw [emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_right_not_mem e _ hi, star_zero]

theorem sum_norm_sq_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    (∑ i, ∑ j, ‖emb0 e X i j‖ ^ 2) = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
  rw [sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
    · simp only [emb0_apply_coe_coe]
    · intro j hj
      simp [emb0_apply_of_right_not_mem e X hj]
  · intro i hi
    simp [emb0_apply_of_left_not_mem e X hi]

end PI.AprimeInfG
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set PI.AprimeInfG
open scoped Matrix

variable {n k : ℕ} {S : Finset (Fin n)}

theorem jm_mul_embed (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    Formalism.REAL.Jm ε * emb0 e X = emb0 e X := by
  funext i j
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul]
  by_cases hi : i ∈ S
  · simp [hε i hi]
  · simp [emb0, hi]

theorem embed_mul_jm (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e X * Formalism.REAL.Jm ε = emb0 e X := by
  funext i j
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal]
  by_cases hj : j ∈ S
  · simp [hε j hj]
  · simp [emb0, hj]

theorem embed_mul_complement (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : emb0 e X * (1 - emb0 e 1) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← embed_mul, Matrix.mul_one, sub_self]

theorem complement_mul_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : (1 - emb0 e 1) * emb0 e X = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, ← embed_mul, Matrix.one_mul, sub_self]

theorem P_mul_P (e : Fin k ≃ S) : (1 - emb0 e 1) * (1 - emb0 e 1 : Matrix (Fin n) (Fin n) ℂ) = 1 - emb0 e 1 := by
  rw [Matrix.mul_sub, Matrix.mul_one, complement_mul_embed, sub_zero]

def blkM (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ := emb0 e X + (1 - emb0 e 1)

theorem blkM_mul (e : Fin k ≃ S) (X Y : Matrix (Fin k) (Fin k) ℂ) : blkM e X * blkM e Y = blkM e (X * Y) := by
  unfold blkM
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, embed_mul_complement, complement_mul_embed, P_mul_P, ← embed_mul]
  abel

theorem blkM_one (e : Fin k ≃ S) : blkM e (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  unfold blkM; abel

theorem blkM_conjTranspose_mul_jm_mul_blkM (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    (blkM e X)ᴴ * Formalism.REAL.Jm ε * blkM e X = emb0 e (Xᴴ * X) + Formalism.REAL.Jm ε * (1 - emb0 e 1) := by
  have hPh : (1 - emb0 e 1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 - emb0 e 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, ← embed_conjTranspose, Matrix.conjTranspose_one]
  have hJP : Formalism.REAL.Jm ε * (1 - emb0 e 1) = (1 - emb0 e 1) * Formalism.REAL.Jm ε := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, jm_mul_embed ε hε, embed_mul_jm ε hε]
  unfold blkM
  rw [Matrix.conjTranspose_add, hPh, ← embed_conjTranspose]
  have e1 : (emb0 e Xᴴ + (1 - emb0 e 1)) * Formalism.REAL.Jm ε * (emb0 e X + (1 - emb0 e 1)) =
      emb0 e Xᴴ * Formalism.REAL.Jm ε * emb0 e X + emb0 e Xᴴ * (Formalism.REAL.Jm ε * (1 - emb0 e 1)) +
        (1 - emb0 e 1) * Formalism.REAL.Jm ε * emb0 e X + (1 - emb0 e 1) * (Formalism.REAL.Jm ε * (1 - emb0 e 1)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [e1, embed_mul_jm ε hε, hJP, ← Matrix.mul_assoc (emb0 e Xᴴ), embed_mul_complement, Matrix.zero_mul,
    Matrix.mul_assoc (1 - emb0 e 1), jm_mul_embed ε hε, complement_mul_embed, ← Matrix.mul_assoc, P_mul_P, ← embed_mul, ← hJP]
  abel

theorem blkM_col (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin n) (hi : i ∉ S) (j : Fin n) :
    blkM e X j i = if j = i then 1 else 0 := by
  simp [blkM, emb0, hi, Matrix.one_apply]

theorem blkM_inj (e : Fin k ≃ S) {X Y : Matrix (Fin k) (Fin k) ℂ} (h : blkM e X = blkM e Y) : X = Y := by
  unfold blkM at h
  have := congrArg (resB e) (add_right_cancel h)
  rwa [restrict_embed, restrict_embed] at this

theorem inUJ_blkM (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ)
    (hX : Xᴴ * X = 1) : Formalism.REAL.inUJ ε (blkM e X) := by
  unfold Formalism.REAL.inUJ
  rw [blkM_conjTranspose_mul_jm_mul_blkM ε hε, hX, Matrix.mul_sub, Matrix.mul_one, jm_mul_embed ε hε]
  abel

def embHom (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Formalism.REAL.UJ (fun _ : Fin k => true) →* UstdSub ε S where
  toFun g :=
    ⟨⟨⟨blkM e ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ),
        blkM e (((g : (Matrix (Fin k) (Fin k) ℂ)ˣ)⁻¹ : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ),
        by rw [blkM_mul, Units.mul_inv, blkM_one], by rw [blkM_mul, Units.inv_mul, blkM_one]⟩,
      inUJ_blkM ε hε e _ (by
        have h := g.2
        change ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) *
          ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ) = Formalism.REAL.Jm (fun _ : Fin k => true) at h
        rwa [jm_true, Matrix.mul_one] at h)⟩,
      fun i hi j => blkM_col e _ i hi j⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact blkM_one e
  map_mul' g h := by
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact (blkM_mul e _ _).symm

theorem embHom_val (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S)
    (g : Formalism.REAL.UJ (fun _ : Fin k => true)) :
    ((((embHom ε hε e g : UstdSub ε S) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      blkM e ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ) := rfl

theorem embHom_injective (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Function.Injective (embHom ε hε e) := by
  intro g h he
  have := congrArg (fun u : UstdSub ε S => (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    Matrix (Fin n) (Fin n) ℂ)) he
  simp only [embHom_val] at this
  exact Subtype.ext (Units.ext (blkM_inj e this))

theorem std_row (ε : Fin n → Bool) (u : UstdSub ε S) (i : Fin n) (hi : i ∉ S) (j : Fin n) (hji : j ≠ i) :
    (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) i j = 0 := by
  set U := (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hU
  set V := ((((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ))⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) with hV
  have hUV : U * (V : Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv _
  have hJ : Uᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε := (u : Formalism.REAL.UJ ε).2
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hW : Formalism.REAL.Jm ε * Uᴴ * Formalism.REAL.Jm ε = (V : Matrix (Fin n) (Fin n) ℂ) := by
    calc Formalism.REAL.Jm ε * Uᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Uᴴ * Formalism.REAL.Jm ε * (U * V) := by
          rw [hUV, Matrix.mul_one]
      _ = Formalism.REAL.Jm ε * (Uᴴ * Formalism.REAL.Jm ε * U) * V := by simp only [Matrix.mul_assoc]
      _ = (V : Matrix (Fin n) (Fin n) ℂ) := by rw [hJ, hJJ, Matrix.one_mul]
  have hcol := (u⁻¹).2 i hi j
  change (V : Matrix (Fin n) (Fin n) ℂ) j i = _ at hcol
  rw [← hW, if_neg hji] at hcol
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at hcol
  have hd : ∀ a : Fin n, (if ε a = true then (1 : ℂ) else -1) ≠ 0 := fun a => by split_ifs <;> norm_num
  have := (mul_eq_zero.1 hcol).resolve_right (hd i)
  have := (mul_eq_zero.1 this).resolve_left (hd j)
  simpa using this

theorem std_eq_blkM (ε : Fin n → Bool) (e : Fin k ≃ S) (u : UstdSub ε S) :
    (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      blkM e (resB e (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
  funext a b
  by_cases hb : b ∈ S
  · by_cases ha : a ∈ S
    · simp [blkM, emb0, resB, ha, hb, Matrix.one_apply]
    · have hab : b ≠ a := fun h => ha (h ▸ hb)
      rw [std_row ε u a ha b hab]
      simp [blkM, emb0, ha, Matrix.one_apply, hab.symm]
  · rw [u.2 b hb a, blkM_col e _ b hb a]

theorem embHom_surjective (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Function.Surjective (embHom ε hε e) := by
  intro u
  set U := (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hU
  set V := ((((u⁻¹ : UstdSub ε S) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hV
  have hUb := std_eq_blkM ε e u
  have hVb := std_eq_blkM ε e u⁻¹
  have hUV : U * V = 1 := Units.mul_inv _
  have hVU : V * U = 1 := Units.inv_mul _
  have h1 : resB e U * resB e V = 1 := by
    apply blkM_inj e
    rw [← blkM_mul, ← hUb, ← hVb, hUV, blkM_one]
  have h2 : resB e V * resB e U = 1 := by
    apply blkM_inj e
    rw [← blkM_mul, ← hUb, ← hVb, hVU, blkM_one]
  have hJ : Uᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε := (u : Formalism.REAL.UJ ε).2
  have hGG : (resB e U)ᴴ * resB e U = 1 := by
    have h3 := blkM_conjTranspose_mul_jm_mul_blkM ε hε e (resB e U)
    rw [← hUb, hJ] at h3
    have h4 : Formalism.REAL.Jm ε = emb0 e 1 + Formalism.REAL.Jm ε * (1 - emb0 e 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, jm_mul_embed ε hε]; abel
    have h5 := add_right_cancel (h4.symm.trans h3)
    have := congrArg (resB e) h5
    rw [restrict_embed, restrict_embed] at this
    exact this.symm
  refine ⟨⟨⟨resB e U, resB e V, h1, h2⟩, ?_⟩, ?_⟩
  · change (resB e U)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) * resB e U = Formalism.REAL.Jm (fun _ : Fin k => true)
    rw [jm_true, Matrix.mul_one, hGG]
  · apply Subtype.ext; apply Subtype.ext; apply Units.ext
    rw [embHom_val]
    exact hUb.symm

def blockEmbeddingLinearMap (e : Fin k ≃ S) : Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := emb0 e
  map_add' := (blockEmbeddingAddHom e).map_add
  map_smul' c X := by
    funext i j
    simp only [emb0, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def resBLin (e : Fin k ≃ S) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ where
  toFun := resB e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def UkChart : Prop := ∀ k : ℕ, Formalism.MainNotions.S.Gauge.GaugeDens (fun _ : Fin k => true) →
    ∃ (α : Type) (_ : Fintype α) (L₀ : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ)
      (P₀ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] EuclideanSpace ℝ α) (r : ℝ) (D : EuclideanSpace ℝ α → ℝ),
      (∀ z, P₀ (L₀ z) = z) ∧
      (∀ M, Mᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) + Formalism.REAL.Jm (fun _ : Fin k => true) * M = 0 → L₀ (P₀ M) = M) ∧
      (∀ z, (L₀ z)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) + Formalism.REAL.Jm (fun _ : Fin k => true) * L₀ z = 0) ∧
      (∀ z, frob (L₀ z) = ‖z‖ ^ 2) ∧ 0 < r ∧ ContinuousAt D 0 ∧
      D 0 = Formalism.MainNotions.S.Gauge.gaugeU (fun _ : Fin k => true) ∧ Measurable D ∧ (∀ z, 0 ≤ D z) ∧
      Set.InjOn (fun z => expU (fun _ : Fin k => true) (L₀ z)) (ball 0 r) ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ α) r, MeasurableSet A →
        Formalism.REAL.muG (fun _ : Fin k => true) ((fun z => expU (fun _ : Fin k => true) (L₀ z)) '' A) =
          ∫⁻ z in A, ENNReal.ofReal (D z)

def GaugeVolUD : Prop := ∀ k : ℕ, Formalism.MainNotions.S.Gauge.GaugeDens (fun _ : Fin k => true) ∧
    Formalism.MainNotions.S.Gauge.muGauge (fun _ : Fin k => true) Set.univ = ENNReal.ofReal (Formalism.MainNotions.S.UnitaryVolumeMass.volU k)

theorem continuous_embHom (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Continuous (embHom ε hε e) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · exact ((continuous_embed e).comp (Units.continuous_val.comp continuous_subtype_val)).add continuous_const
  · exact ((continuous_embed e).comp (Units.continuous_coe_inv.comp continuous_subtype_val)).add continuous_const

theorem blockHaarV_of (hU : UkChart) (hG : GaugeVolUD) : BlockHaarV := by
  intro n ε S k hk hε _
  let e : Fin k ≃ S := (finCongr hk.symm).trans S.equivFin.symm
  obtain ⟨α, hα, L0, P0, r, D, f1, f2, f3, f4, hr, hDc, hD0, hDm, hDn, hinj, hdens⟩ := hU k (hG k).1
  have hJk := jm_true k

  let L₁ : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := (blockEmbeddingLinearMap e).comp L0
  let P₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ α := P0.comp (resBLin e)
  have hL₁ : ∀ y, L₁ y = emb0 e (L0 y) := fun y => rfl
  have hblk : ∀ y, InBlock ε S (L₁ y) := by
    intro y
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [hL₁, ← embed_conjTranspose, embed_mul_jm ε hε, jm_mul_embed ε hε]
      have h := f3 y
      rw [hJk, Matrix.mul_one, Matrix.one_mul] at h
      have := congrArg (emb0 e) h
      rw [show emb0 e (0 : Matrix (Fin k) (Fin k) ℂ) = 0 from (blockEmbeddingAddHom e).map_zero] at this
      rw [← this]
      exact ((blockEmbeddingAddHom e).map_add _ _).symm
    · rw [hL₁]
      rcases hij with hi | hj
      · simp [emb0, hi]
      · simp [emb0, hj]
  have hmem : ∀ y, expU ε (L₁ y) ∈ UstdSub ε S := by
    intro y i hi j
    show ((expU ε (L₁ y) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) j i = _
    rw [expU_val _ _ (hblk y).1]
    exact exp_block_col S _ (hblk y).2 i hi j

  have hchart : ∀ y, embHom ε hε e (expU (fun _ : Fin k => true) (L0 y)) = ⟨expU ε (L₁ y), hmem y⟩ := by
    intro y
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    rw [embHom_val]
    show blkM e (((expU (fun _ : Fin k => true) (L0 y) : Formalism.REAL.UJ _) : (Matrix (Fin k) (Fin k) ℂ)ˣ) :
      Matrix (Fin k) (Fin k) ℂ) = ((expU ε (L₁ y) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    rw [expU_val _ _ (f3 y), expU_val _ _ (hblk y).1, hL₁, exp_embed]
    rfl

  have hgpos : 0 < Formalism.MainNotions.S.Gauge.gaugeU (fun _ : Fin k => true) := (hG k).1.2
  have hvol := (hG k).2
  unfold Formalism.MainNotions.S.Gauge.muGauge at hvol
  rw [Measure.smul_apply, smul_eq_mul] at hvol
  have hfin : Formalism.REAL.muG (fun _ : Fin k => true) Set.univ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simp [hgpos])] at hvol
    exact ENNReal.ofReal_ne_top hvol.symm
  have hpos : Formalism.REAL.muG (fun _ : Fin k => true) Set.univ ≠ 0 :=
    (Measure.measure_univ_pos.2 (NeZero.ne _)).ne'
  have : IsFiniteMeasure (Formalism.REAL.muG (fun _ : Fin k => true)) := ⟨lt_top_iff_ne_top.2 hfin⟩
  have hcE := continuous_embHom ε hε e
  let ν := (Formalism.REAL.muG (fun _ : Fin k => true)).map (embHom ε hε e)
  have hνu : ν Set.univ = Formalism.REAL.muG (fun _ : Fin k => true) Set.univ := by
    rw [Measure.map_apply hcE.measurable MeasurableSet.univ, Set.preimage_univ]
  refine ⟨α, hα, L₁, P₁, ν, r, D, hmem, fun z => ?_, fun M hM => ?_, hblk, fun z => ?_,
    isMulLeftInvariant_map (embHom ε hε e).toMulHom hcE.measurable (embHom_surjective ε hε e), inferInstance,
    ?_, hr, hDm, hDn, hDc, ?_, ?_, ?_, ?_, fun A hA hAm => ?_⟩
  · show P0 (resB e (emb0 e (L0 z))) = z
    rw [restrict_embed, f1]
  · show emb0 e (L0 (P0 (resB e M))) = M
    have hl : (resB e M)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) + Formalism.REAL.Jm (fun _ : Fin k => true) * resB e M = 0 := by
      rw [hJk, Matrix.mul_one, Matrix.one_mul]
      funext a b
      have h := congrFun (congrFun hM.1 (e a)) (e b)
      rw [PI.AprimeInfW.lie_entry] at h
      have ha : ((e a : S) : Fin n) ∈ S := (e a).2
      have hb : ((e b : S) : Fin n) ∈ S := (e b).2
      simp only [hε _ ha, hε _ hb, if_true, mul_one, one_mul] at h
      simpa [resB, Matrix.conjTranspose_apply] using h
    rw [f2 _ hl, embed_restrict e M hM.2]
  · rw [hL₁]
    unfold frob
    rw [sum_norm_sq_embed]
    exact f4 z
  · rw [hνu]; exact hpos
  · rw [hD0]; exact hgpos
  · rw [hνu, hD0]
    have := congrArg ENNReal.toReal hvol
    have hv0 : 0 ≤ Formalism.MainNotions.S.UnitaryVolumeMass.volU k := by
      unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU; exact Finset.prod_nonneg fun i _ => by positivity
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hgpos.le), ENNReal.toReal_ofReal hv0] at this
    rw [← this]
    field_simp
  · exact (continuous_expU ε (fun y => L₁ y) L₁.continuous_of_finiteDimensional fun y => (hblk y).1).subtype_mk _
  · intro y hy y' hy' he'
    apply hinj hy hy'
    apply embHom_injective ε hε e
    rw [hchart, hchart]
    exact he'
  · have himg : (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) '' A =
        embHom ε hε e '' ((fun z => expU (fun _ : Fin k => true) (L0 z)) '' A) := by
      rw [Set.image_image]
      exact Set.image_congr fun y _ => (hchart y).symm
    have hcont : Continuous (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) :=
      (continuous_expU ε (fun y => L₁ y) L₁.continuous_of_finiteDimensional fun y => (hblk y).1).subtype_mk _
    have hinj' : Set.InjOn (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) A := by
      intro y hy y' hy' he'
      apply hinj (hA hy) (hA hy')
      apply embHom_injective ε hε e
      rw [hchart, hchart]
      exact he'
    have hmeas : MeasurableSet ((fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) '' A) :=
      hAm.image_of_continuousOn_injOn hcont.continuousOn hinj'
    rw [Measure.map_apply hcE.measurable hmeas, himg, (embHom_injective ε hε e).preimage_image]
    exact hdens A hA hAm

theorem ukChart_of (hE : ExpProdU) : UkChart := by
  intro k hgd
  obtain ⟨α, β, hα, hβ, L0, P0, L1, P1, r, D, f1, f2, f3, f4, f5, f6, f7, f8, hr, hDc, hD0, hDm, hDn, hc, hinj,
    hdens⟩ := placeChartV_of hE k (fun _ => true) ∅ (fun i hi => absurd hi (Finset.notMem_empty i)) hgd
  have hL1 : ∀ z, L1 z = 0 := by
    intro z
    funext i j
    exact (f7 z).2 i j (Or.inl (Finset.notMem_empty i))
  have hsub : ∀ z : EuclideanSpace ℝ β, z = 0 := by
    intro z
    rw [← f5 z, hL1, map_zero]
  have hβe : IsEmpty β := ⟨fun b => by
    classical
    have := congrFun (congrArg WithLp.ofLp (hsub (EuclideanSpace.single b 1))) b
    simp at this⟩
  have hvolβ : (volume : Measure (EuclideanSpace ℝ β)) Set.univ = 1 := by
    have hmp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp β).measure_preimage
      (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    rw [Set.preimage_univ] at hmp
    rw [hmp, MeasureTheory.volume_pi, Measure.pi_univ]
    simp
  refine ⟨α, hα, L0, P0, r, fun y => D (y, 0), f1, fun M hM => f2 M ⟨hM, fun i hi => absurd hi (Finset.notMem_empty i)⟩,
    fun z => (f3 z).1, f4, hr, ?_, hD0, hDm.comp (measurable_id.prodMk measurable_const), fun z => hDn _, ?_, ?_⟩
  · exact ContinuousAt.comp (f := fun y : EuclideanSpace ℝ α => (y, (0 : EuclideanSpace ℝ β))) hDc
      (continuous_id.prodMk continuous_const).continuousAt
  · intro y hy y' hy' he
    have h1 : ((y, (0 : EuclideanSpace ℝ β)) : EuclideanSpace ℝ α × EuclideanSpace ℝ β) ∈ ball 0 r := by
      rw [mem_ball_zero_iff, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact mem_ball_zero_iff.1 hy
    have h2 : ((y', (0 : EuclideanSpace ℝ β)) : EuclideanSpace ℝ α × EuclideanSpace ℝ β) ∈ ball 0 r := by
      rw [mem_ball_zero_iff, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact mem_ball_zero_iff.1 hy'
    have := hinj h1 h2 (by simp only [hL1, expU_zero, mul_one]; exact he)
    exact congrArg Prod.fst this
  · intro A hA hAm
    have hAU : A ×ˢ (Set.univ : Set (EuclideanSpace ℝ β)) ⊆ ball 0 r := by
      rintro ⟨x, z⟩ ⟨hx, -⟩
      rw [hsub z, mem_ball_zero_iff, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact mem_ball_zero_iff.1 (hA hx)
    have himg : (fun z : EuclideanSpace ℝ α × EuclideanSpace ℝ β =>
        expU (fun _ : Fin k => true) (L0 z.1) * expU (fun _ : Fin k => true) (L1 z.2)) '' (A ×ˢ Set.univ) =
        (fun z => expU (fun _ : Fin k => true) (L0 z)) '' A := by
      ext g
      constructor
      · rintro ⟨⟨x, z⟩, ⟨hx, -⟩, rfl⟩
        exact ⟨x, hx, by simp [hL1, expU_zero]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(x, 0), ⟨hx, Set.mem_univ _⟩, by simp [hL1, expU_zero]⟩
    rw [← himg, hdens _ hAU (hAm.prod MeasurableSet.univ), Measure.volume_eq_prod,
      setLIntegral_prod _ ((hDm.ennreal_ofReal).aemeasurable)]
    refine setLIntegral_congr_fun hAm fun x _ => ?_
    rw [show (fun z : EuclideanSpace ℝ β => ENNReal.ofReal (D (x, z))) = fun _ => ENNReal.ofReal (D (x, 0)) from
      funext fun z => by rw [hsub z], setLIntegral_const, hvolβ, mul_one]

theorem grpStd_full (hE : ExpProdU) (hG : GaugeVolUD) : GrpStd :=
  grpStd_of_exp_block hE (blockHaarV_of (ukChart_of hE) hG)

end PI.AprimeInfW
