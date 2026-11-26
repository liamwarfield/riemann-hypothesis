module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitShear
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.DiagonalPhaseFirstVector

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ParabolicVolume
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem unit_forall {P : Unit → Prop} : (∀ i, P i) ↔ P () := ⟨fun h => h (), fun h _ => h⟩

theorem parabolic_volume : VolPP σ v := by
  intro g r T T' m hS hg hT μ hμ hm l
  obtain ⟨D⟩ := exists_SD hS
  have hp0 : ∀ s t, D.p 0 (D.pt s t) = s := fun s t => (D.p_pt s t).1
  have hp1 : ∀ s t, D.p 1 (D.pt s t) = t := fun s t => (D.p_pt s t).2
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne_zero v hg
  have hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F := natCast_mem _ g
  have hsh : ∀ X : Set (Unit → Fv F v ⊗[F] E), μ ((D.shear id) ⁻¹' X) = μ X :=
    haar_shear μ (D.shear id) (Obox (E := E) v Unit) (obox_compact Unit) (obox_open Unit)
      (obox_nonempty Unit) (D.shear_box id)
  by_cases hl : (l : ℕ) < r
  · have ha : alp v r l ^ 2 ≠ 0 := pow_ne_zero _ (alp_ne_zero v r l)
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' (Set.univ.pi fun _ : Unit =>
          {c | D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈
            OEv (E := E) v}) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_pos hl, unit_forall]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul, D.shear_first_coordinate, D.shear_second_coordinate]
      simp only [map_add (f := _), (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩
        refine ⟨⟨?_, h2⟩, h3, ?_⟩
        · have e1 : alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 0 (c ()) =
              (g : Fv F v) * (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()))) -
                alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 1 (c ()) := by
            field_simp <;> ring
          rw [e1]
          exact sub_mem (mul_mem hgO h3) h2
        · rwa [add_comm (D.p 1 (c ()))]
    have hu : ∀ _ : Unit, IsUnit (D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹)) :=
      fun _ => D.isUnit_pt (mul_ne_zero ha (pow_ne_zero _ (inv_ne_zero hg0))) (mul_ne_zero ha (inv_ne_zero hg0))
    rw [hset, hsh, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt]
    rw [absV_mul, absV_mul, absV_mul, absV_pow, absV_pow, absV_inv]
    have hA := absV_pos v (alp_ne_zero v r l)
    have hG := absV_pos v hg0
    field_simp
  · have hlr : alp v r l = 1 := by unfold alp; rw [if_neg hl]
    obtain ⟨k, hk⟩ := hT
    have hk' : ((T : Fv F v) - (T' : Fv F v)) = (g : Fv F v) * (k : Fv F v) := by
      have := congrArg (Int.cast : ℤ → Fv F v) hk
      push_cast at this
      exact this
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' ((fun w => w + fun _ : Unit => D.pt ((T : Fv F v) + T') (T : Fv F v)) ⁻¹'
          (Set.univ.pi fun _ : Unit =>
            {c | D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹ * c ∈ OEv (E := E) v})) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_neg hl, unit_forall, Pi.add_apply]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul]
      simp only [map_add (f := _), D.shear_first_coordinate, D.shear_second_coordinate, hp0, hp1, map_natCast, (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        refine ⟨?_, h2⟩
        have e1 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') := by ring
        rw [e1]; exact h3
      · rintro ⟨h3, h2⟩
        have e0 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
        refine ⟨⟨?_, h2⟩, by rw [e0]; exact h3, ?_⟩
        · have e1 : (g : Fv F v)⁻¹ * (D.p 0 (c ()) + T) =
              (g : Fv F v) * (((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T'))) -
                (g : Fv F v)⁻¹ * (D.p 1 (c ()) + T) + (g : Fv F v)⁻¹ * ((T : Fv F v) - T') := by
            field_simp <;> ring
          have e2 : (g : Fv F v)⁻¹ * ((T : Fv F v) - T') = (k : Fv F v) := by
            rw [hk']; field_simp
          rw [e1, e2]
          exact add_mem (sub_mem (mul_mem hgO h3) h2) (intCast_mem _ k)
        · have e2 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 1 (c ()) + D.p 0 (c ()) + T + T') =
              ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
          rw [e2]; exact h3
    have hu : ∀ _ : Unit, IsUnit (D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹) :=
      fun _ => D.isUnit_pt (pow_ne_zero _ (inv_ne_zero hg0)) (inv_ne_zero hg0)
    rw [hset, hsh, measure_preimage_add_right, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt, hlr, absV_one]
    rw [absV_mul, absV_pow, absV_inv]
    have hG := absV_pos v hg0
    field_simp

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.IsCompactDbox
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

section Scale

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]

theorem haar_smul_map (μ0 : Measure V) [μ0.IsAddHaarMeasure] (c : Fv F v) (hc : c ≠ 0) :
    (Measure.map (fun x : V => c • x) μ0).IsAddHaarMeasure := by
  let h := Homeomorph.smulOfNeZero (α := V) c hc
  exact Measure.isAddHaarMeasure_map μ0 (DistribSMul.toAddMonoidHom V c)
    (continuous_const_smul c) h.surjective h.isClosedEmbedding.tendsto_cocompact

theorem scale_prod (μ0 : Measure V) [μ0.IsAddHaarMeasure] (c : Fv F v) (hc : c ≠ 0)
    (A B : Set V) (hA : MeasurableSet A) (hB : MeasurableSet B) (hA0 : μ0 A ≠ 0) (hAt : μ0 A ≠ ⊤) :
    μ0 ((fun x : V => c • x) ⁻¹' A) * μ0 ((fun x : V => c⁻¹ • x) ⁻¹' B) = μ0 A * μ0 B := by
  have := haar_smul_map v μ0 c hc
  have := haar_smul_map v μ0 c⁻¹ (inv_ne_zero hc)
  have hm : Measurable fun x : V => c • x := (continuous_const_smul c).measurable
  have hm' : Measurable fun x : V => c⁻¹ • x := (continuous_const_smul c⁻¹).measurable
  obtain ⟨s1, e1⟩ : ∃ s : NNReal, Measure.map (fun x : V => c • x) μ0 = s • μ0 :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ0⟩
  obtain ⟨s2, e2⟩ : ∃ s : NNReal, Measure.map (fun x : V => c⁻¹ • x) μ0 = s • μ0 :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ0⟩
  have hcomp : Measure.map (fun x : V => c⁻¹ • x) (Measure.map (fun x : V => c • x) μ0) = μ0 := by
    rw [Measure.map_map hm' hm]
    have : ((fun x : V => c⁻¹ • x) ∘ fun x : V => c • x) = id := by
      funext x; simp [smul_smul, inv_mul_cancel₀ hc]
    rw [this, Measure.map_id]
  have hss : ((s1 : ENNReal) * s2) * μ0 A = 1 * μ0 A := by
    have h := congrArg (fun m : Measure V => m A) hcomp
    rw [e1, Measure.map_smul s1 hm'.aemeasurable, e2, smul_smul] at h
    rw [one_mul]
    conv_rhs => rw [← h]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul]
  have hs : (s1 : ENNReal) * s2 = 1 := (ENNReal.mul_left_inj hA0 hAt).1 hss
  rw [← Measure.map_apply hm hA, ← Measure.map_apply hm' hB, e1, e2]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  calc (s1 : ENNReal) * μ0 A * (s2 * μ0 B) = ((s1 : ENNReal) * s2) * (μ0 A * μ0 B) := by ring
    _ = μ0 A * μ0 B := by rw [hs, one_mul]

end Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

def Mk (ι : Type) (k : ℕ) : AddSubgroup (ι → Fv F v ⊗[F] E) :=
  (ObS (E := E) v ι).comap (DistribSMul.toAddMonoidHom (ι → Fv F v ⊗[F] E) (piu v ^ k))

theorem coe_Mk (ι : Type) (k : ℕ) : (Mk (E := E) v ι k : Set (ι → Fv F v ⊗[F] E)) =
    (fun x => piu v ^ k • x) ⁻¹' Obox (E := E) v ι := by
  ext x
  rw [← coe_ObS]
  rfl

theorem ann_Mk (ι : Type) [Fintype ι] (k : ℕ) :
    ann (chi (E := E) v ψ ι) (Mk (E := E) v ι k) =
      (fun y => (piu v ^ k)⁻¹ • y) ⁻¹' Dbox (E := E) v ψ ι := by
  have hpk : piu v ^ k ≠ 0 := pow_ne_zero k (piu_ne v)
  rw [← ann_obox]
  ext y
  simp only [Set.mem_preimage, ann, Set.mem_setOf_eq, coe_Mk]
  constructor
  · intro hy x hx
    have := hy ((piu v ^ k)⁻¹ • x) (by simpa [smul_smul, mul_inv_cancel₀ hpk] using hx)
    rwa [chi_smul] at this
  · intro hy x hx
    have := hy (piu v ^ k • x) hx
    rwa [chi_smul, smul_smul, mul_inv_cancel₀ hpk, one_smul] at this

variable (hK : OpenKer v ψ) (hnt : ∃ r, psiV F ψ v r ≠ 1)
include hK hnt

theorem isCompact_dbox (ι : Type) [Fintype ι] : IsCompact (Dbox (E := E) v ψ ι) :=
  isCompact_univ_pi fun _ => conductor_isCompact v ψ hK hnt

omit hnt in
theorem isOpen_dbox (ι : Type) [Fintype ι] : IsOpen (Dbox (E := E) v ψ ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => conductor_isOpen v ψ hK

theorem exists_sd (ι : Type) [Fintype ι] :
    ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (chi (E := E) v ψ ι) := by
  have hpk : ∀ k : ℕ, piu v ^ k ≠ 0 := fun k => pow_ne_zero k (piu_ne v)
  have hψc := continuous_psiV_of v ψ hK
  have hA : MeasurableSet (Obox (E := E) v ι) := (isOpen_obox v ι).measurableSet
  have hB : MeasurableSet (Dbox (E := E) v ψ ι) := (isOpen_dbox v ψ hK ι).measurableSet
  set μ0 : Measure (ι → Fv F v ⊗[F] E) := Measure.addHaar
  have hA0 : μ0 (Obox (E := E) v ι) ≠ 0 :=
    (isOpen_obox v ι).measure_ne_zero μ0 ⟨0, zero_mem_obox v ι⟩
  have hAt : μ0 (Obox (E := E) v ι) ≠ ⊤ := (isCompact_obox v ι).measure_lt_top.ne
  refine PI.OmFibreUniq.W.SdCore.selfDual_of_pairs (chi (E := E) v ψ ι) ?_ (chi_add_left v ψ ι)
    (chi_symm v ψ ι) (fun x y => norm_psiV_of v ψ hK _) (Mk (E := E) v ι) (fun k => ?_)
    (fun k => ?_) (fun k => ?_) (fun k => ?_) (fun y => ?_) (fun U hU => ?_) μ0 (fun k => ?_)
  · exact hψc.comp (continuous_finsetSum _ fun i _ => (continuous_tr v).comp
      (((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)))
  · rw [coe_Mk]
    exact (Homeomorph.smulOfNeZero (α := ι → Fv F v ⊗[F] E) _ (hpk k)).isCompact_preimage.2
      (isCompact_obox v ι)
  · rw [coe_Mk]
    exact (isOpen_obox v ι).preimage (continuous_const_smul _)
  · rw [ann_Mk]
    exact (Homeomorph.smulOfNeZero (α := ι → Fv F v ⊗[F] E) _ (inv_ne_zero (hpk k))).isCompact_preimage.2
      (isCompact_dbox v ψ hK hnt ι)
  · rw [ann_Mk]
    exact (isOpen_dbox v ψ hK ι).preimage (continuous_const_smul _)
  · have ht : Tendsto (fun k : ℕ => piu v ^ k • y) atTop (𝓝 0) := by
      simpa using (piu_tendsto v).smul_const y
    filter_upwards [ht ((isOpen_obox v ι).mem_nhds (zero_mem_obox v ι))] with k hk
    rw [← SetLike.mem_coe, coe_Mk]
    exact hk
  · filter_upwards [tube v (isCompact_dbox v ψ hK hnt ι) hU] with k hk
    rw [ann_Mk]
    intro y hy
    have := hk _ hy
    rwa [smul_smul, mul_inv_cancel₀ (hpk k), one_smul] at this
  · rw [ann_Mk, ann_Mk, coe_Mk, coe_Mk, scale_prod v μ0 _ (hpk k) _ _ hA hB hA0 hAt,
      scale_prod v μ0 _ (hpk 0) _ _ hA hB hA0 hAt]

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
end
end
