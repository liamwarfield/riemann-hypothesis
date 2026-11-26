module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CompCoordMem

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Cols
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.ptN :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : M2 v → ℂ) (X : M2 v),
      (∀ b, ψl v (-(b * X.det)) * Pt a X = Pt (fun m => a (m * !![1, b; 0, 1])) X) ∧
      ∀ s, Pt a (X * !![1, 0; -s, 1]) = Pt (fun m => ψl v (-(s * m.det)) * a m) X := by
  intro F _ _ v a X
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  have hadd := (UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.2.1
  refine ⟨fun b => ?_, fun s => ?_⟩
  · unfold Pt
    rw [← integral_const_mul,
      ← integral_add_right_eq_self (μ := μ2 v) (fun c' => ψl v (-(b * X.det)) *
        (a (cols (fun i => X i 1) c') * ψl v (X 0 0 * c' 1 - X 1 0 * c' 0)))
        (b • fun i => X i 1)]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    have hm : cols (fun i => X i 1) c' * !![1, b; 0, 1]
        = cols (fun i => X i 1) (c' + b • fun i => X i 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cols, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have hp : ψl v (-(b * X.det)) * ψl v (X 0 0 * (c' + b • fun i => X i 1) 1
          - X 1 0 * (c' + b • fun i => X i 1) 0) = ψl v (X 0 0 * c' 1 - X 1 0 * c' 0) := by
      rw [← hadd]
      congr 1
      simp [Matrix.det_fin_two]
      ring
    simp only [hm]
    rw [mul_left_comm, hp]
  · unfold Pt
    rw [show (fun i => (X * !![1, 0; -s, 1]) i 1) = (fun i => X i 1) by
      funext i
      simp [Matrix.mul_apply, Fin.sum_univ_two]]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    have hp : ψl v ((X * !![1, 0; -s, 1]) 0 0 * c' 1 - (X * !![1, 0; -s, 1]) 1 0 * c' 0)
        = ψl v (-(s * (cols (fun i => X i 1) c').det)) * ψl v (X 0 0 * c' 1 - X 1 0 * c' 0) := by
      rw [← hadd]
      congr 1
      simp [cols, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    simp only []
    rw [hp]
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.JmMeasurable
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] {v : P F}

private noncomputable def Jm (c : Fin 2 → Kv v) : Fin 2 → Kv v := ![-c 1, c 0]

private lemma Jm_Jm (c : Fin 2 → Kv v) : Jm (Jm c) = -c := by
  funext i; fin_cases i <;> simp [Jm]

private lemma Jm_measurable : Measurable (Jm (v := v)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · have h : Measurable fun c : Fin 2 → Kv v => -c 1 := measurable_neg.comp (measurable_pi_apply (1 : Fin 2))
    simpa [Jm] using h
  · simpa [Jm] using measurable_pi_apply (0 : Fin 2)

private noncomputable def JmE : (Fin 2 → Kv v) ≃ᵐ (Fin 2 → Kv v) where
  toFun := Jm
  invFun := fun c => -Jm c
  left_inv := fun c => by
    show -Jm (Jm c) = c
    rw [Jm_Jm, neg_neg]
  right_inv := fun c => by
    show Jm (-Jm c) = c
    funext i; fin_cases i <;> simp [Jm]
  measurable_toFun := Jm_measurable
  measurable_invFun := measurable_neg.comp Jm_measurable

private lemma Jm_mp : MeasurePreserving (Jm (v := v)) (μ2 v) (μ2 v) := by
  have hs := measurePreserving_piCongrLeft (α := fun _ : Fin 2 => Kv v)
    (fun _ => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) (Equiv.swap (0 : Fin 2) 1)
  have hn := measurePreserving_pi (fun _ : Fin 2 => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v))
    (fun _ : Fin 2 => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v))
    (f := fun (i : Fin 2) (x : Kv v) => if i = 0 then -x else x) (by
      intro i
      fin_cases i
      · simpa using Measure.measurePreserving_neg _
      · convert MeasurePreserving.id (GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) using 1
        funext x
        simp)
  have h := hn.comp hs
  have hf : Jm (v := v) = (fun (a : Fin 2 → Kv v) (i : Fin 2) => if i = 0 then -a i else a i) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Kv v) (Equiv.swap (0 : Fin 2) 1)) := by
    funext c i
    fin_cases i <;> simp [Jm, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hf]
  exact h

private lemma cols_col (c c' : Fin 2 → Kv v) : (fun i => cols c c' i 1) = c' := by
  funext i; fin_cases i <;> simp [cols]

private lemma sw_cols (p q : Fin 2 → Kv v) : sw (cols p q) = cols q p := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sw, cols]

private lemma sw_sw (m : M2 v) : sw (sw m) = m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sw]

private lemma eq_cols (m : M2 v) : m = cols (fun i => m i 0) (fun i => m i 1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cols]

private lemma sw_continuous : Continuous (sw (v := v)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [sw] <;> fun_prop

private noncomputable def swH : M2 v ≃ₜ M2 v where
  toFun := sw
  invFun := sw
  left_inv := sw_sw
  right_inv := sw_sw
  continuous_toFun := sw_continuous
  continuous_invFun := sw_continuous

private lemma comp_sw_mem {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) : (fun X => a (sw X)) ∈ SB (M2 v) :=
  ⟨ha.1.comp_continuous sw_continuous, ha.2.comp_homeomorph swH⟩

private lemma slice_mem {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) (c : Fin 2 → Kv v) :
    (fun c' => a (cols c c')) ∈ localSchwartzBruhatPi (Kv v) (ι := Fin 2) := by
  have hc : Continuous fun c' : Fin 2 → Kv v => cols c c' := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [cols] <;> fun_prop
  have hr : Continuous fun X : M2 v => (fun i => X i 1 : Fin 2 → Kv v) := by
    refine continuous_pi fun i => ?_
    exact (continuous_id.matrix_elem i 1)
  have he : IsClosedEmbedding fun c' : Fin 2 → Kv v => cols c c' :=
    Function.LeftInverse.isClosedEmbedding (f := fun X : M2 v => (fun i => X i 1 : Fin 2 → Kv v))
      (fun c' => cols_col c c') hr hc
  exact ⟨ha.1.comp_continuous hc, ha.2.comp_isClosedEmbedding he⟩

private lemma Pt_cols (a : M2 v → ℂ) (c₁ c : Fin 2 → Kv v) :
    Pt a (cols c₁ c) = localFourierPi (localAdelicChar F v) (fun c' => a (cols c c')) (Jm c₁) := by
  simp only [Pt, localFourierPi, cols_col]
  unfold μ2
  refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
  have h : c₁ 0 * c' 1 - c₁ 1 * c' 0 = ∑ i, c' i * Jm c₁ i := by
    simp [Jm, Fin.sum_univ_two]; ring
  simp only [ψl]
  rw [← h]
  simp [cols]

private lemma fourier_rot (G : (Fin 2 → Kv v) → ℂ) (q : Fin 2 → Kv v) :
    localFourierPi (localAdelicChar F v) (fun c => G (Jm c)) (Jm q) =
      localFourierPi (localAdelicChar F v) G (-q) := by
  have h := (Jm_mp (v := v)).integral_comp (JmE (v := v)).measurableEmbedding
    (fun y => G y * ((localAdelicChar F v (∑ i, y i * (-q) i) : Circle) : ℂ))
  change ∫ x, G (Jm x) * ((localAdelicChar F v (∑ i, x i * Jm q i) : Circle) : ℂ) ∂(μ2 v) =
    ∫ y, G y * ((localAdelicChar F v (∑ i, y i * (-q) i) : Circle) : ℂ) ∂(μ2 v)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  have : ∑ i, c i * Jm q i = ∑ i, Jm c i * (-q) i := by
    simp [Jm, Fin.sum_univ_two]
  simp only [this]

private lemma part1 {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) (p q : Fin 2 → Kv v) :
    Pt (fun X => Pt a (sw X)) (cols q p) = a (cols p q) := by
  have hc := continuous_localAdelicChar (K := F) v
  have hn : localAdelicChar F v ≠ 1 := localAdelicChar_ne_one v
  have hb := slice_mem ha p
  have hG := localFourierPi_mem hc hn hb
  rw [Pt_cols]
  have h1 : (fun c' => Pt a (sw (cols p c'))) =
      fun c' => localFourierPi (localAdelicChar F v) (fun c'' => a (cols p c'')) (Jm c') := by
    funext c'
    rw [sw_cols, Pt_cols]
  rw [h1, fourier_rot, localFourierPi_localFourierPi hc hn hb]
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.ptInv :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∀ a ∈ SB (M2 v), (∀ m, Pt (fun X => Pt a (sw X)) (sw m) = a m) ∧ ∃ a' ∈ SB (M2 v), Pt a' = a := by
  intro F _ _ v a ha
  have h1 : ∀ b ∈ SB (M2 v), ∀ m, Pt (fun X => Pt b (sw X)) (sw m) = b m := by
    intro b hb m
    rw [eq_cols m, sw_cols]
    exact part1 hb _ _
  refine ⟨h1 a ha, ?_⟩
  obtain ⟨T, hT⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have hb := comp_sw_mem ha
  have hTb : Pt (fun X => a (sw X)) ∈ SB (M2 v) := by
    have := (T ⟨_, hb⟩).2
    rwa [hT] at this
  refine ⟨fun X => Pt (fun Y => a (sw Y)) (sw X), comp_sw_mem hTb, ?_⟩
  funext m
  have := h1 _ hb (sw m)
  rw [sw_sw] at this
  simpa [sw_sw] using this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IndicatorMemSB
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : f ∈ SB X)
    {U : Set X} (hU : IsClopen U) : U.indicator f ∈ SB X := by
  refine ⟨?_, ?_⟩
  · have h1 : IsLocallyConstant (U.indicator fun _ : X => (1 : ℂ)) := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro c
      by_cases h1 : (1 : ℂ) = c <;> by_cases h0 : (0 : ℂ) = c
      · exact absurd (h1.trans h0.symm) one_ne_zero
      · have : (U.indicator fun _ : X => (1 : ℂ)) ⁻¹' {c} = U := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, h1, Ne.symm h0, h0]
        rw [this]; exact hU.isOpen
      · have : (U.indicator fun _ : X => (1 : ℂ)) ⁻¹' {c} = Uᶜ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, Ne.symm h1, h1, h0]
        rw [this]; exact hU.compl.isOpen
      · have : (U.indicator fun _ : X => (1 : ℂ)) ⁻¹' {c} = ∅ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, Ne.symm h1, Ne.symm h0, h1, h0]
        rw [this]; exact isOpen_empty
    have h2 : U.indicator f = (U.indicator fun _ : X => (1 : ℂ)) * f := by
      ext x
      by_cases hx : x ∈ U <;> simp [hx]
    rw [h2]
    exact h1.mul hf.1
  · exact HasCompactSupport.mono hf.2 (fun x hx => by
      by_contra h0
      apply hx
      have h0' : f x = 0 := by simpa using h0
      by_cases hxU : x ∈ U <;> simp [hxU, h0'])

theorem UpperTheory.ConvolutionTheory.R2.I.loc :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (ℓ : SB (M2 v) →ₗ[ℂ] ℂ),
      (∀ (s : Kv v) (a a' : SB (M2 v)), (∀ m, a'.1 m = ψl v (-(s * m.det)) * a.1 m) → ℓ a' = ψl v (-s) * ℓ a) →
      ∀ a : SB (M2 v), (∀ m : M2 v, m.det = 1 → a.1 m = 0) → ℓ a = 0 := by
  intro F _ _ v ℓ h a ha
  obtain ⟨-, -, hadd, hlc, hnt, -⟩ := psiLaws F v
  have hψ0 : ∀ x, ψl v x ≠ 0 := fun x => Circle.coe_ne_zero _

  have key : ∀ m0 : M2 v, m0.det ≠ 1 → ∃ N : Set (M2 v), IsClopen N ∧ m0 ∈ N ∧
      ∀ b : SB (M2 v), Function.support b.1 ⊆ N → ℓ b = 0 := by
    intro m0 hm
    obtain ⟨t, ht⟩ := hnt (m0.det - 1) (sub_ne_zero.mpr hm)
    have hz : ψl v (-(-t * m0.det)) ≠ ψl v (- -t) := by
      intro hzz
      apply ht
      have e : -(-t * m0.det) = t * (m0.det - 1) + - -t := by ring
      rw [e, hadd] at hzz
      exact mul_right_cancel₀ (hψ0 _) (hzz.trans (one_mul _).symm)
    have hf : IsLocallyConstant (fun m : M2 v => ψl v (-(-t * m.det))) :=
      hlc.comp_continuous (by
        have : Continuous fun m : M2 v => m.det := continuous_id.matrix_det
        exact (continuous_const.mul this).neg)
    refine ⟨(fun m : M2 v => ψl v (-(-t * m.det))) ⁻¹' {ψl v (-(-t * m0.det))},
      hf.isClopen_fiber _, rfl, fun b hb => ?_⟩
    have h1 := h (-t) b (ψl v (-(-t * m0.det)) • b) (fun m => by
      by_cases hm' : b.1 m = 0
      · simp [hm']
      · have : ψl v (-(-t * m.det)) = ψl v (-(-t * m0.det)) := hb hm'
        rw [this]; rfl)
    rw [map_smul, smul_eq_mul] at h1
    by_contra hne
    exact hz (mul_right_cancel₀ hne h1)
  have hsupp : tsupport a.1 = Function.support a.1 := by
    refine IsClosed.closure_eq ?_
    have : Function.support a.1 = (a.1 ⁻¹' {0})ᶜ := by
      ext x; simp
    rw [this]
    exact (a.2.1.isClopen_fiber 0).compl.isClosed
  have main : ∃ C : Set (M2 v), IsClopen C ∧ tsupport a.1 ⊆ C ∧
      ∀ b : SB (M2 v), Function.support b.1 ⊆ C → ℓ b = 0 := by
    refine IsCompact.induction_on (p := fun T : Set (M2 v) => ∃ C : Set (M2 v), IsClopen C ∧ T ⊆ C ∧
      ∀ b : SB (M2 v), Function.support b.1 ⊆ C → ℓ b = 0) a.2.2 ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, subset_rfl, fun b hb => ?_⟩
      have : b = 0 := by
        apply Subtype.ext
        funext x
        by_contra hx
        exact hb hx
      rw [this, map_zero]
    · rintro S T hST ⟨C, hC, hTC, hb⟩
      exact ⟨C, hC, hST.trans hTC, hb⟩
    · rintro S T ⟨C, hC, hSC, hb⟩ ⟨C', hC', hTC', hb'⟩
      refine ⟨C ∪ C', hC.union hC', Set.union_subset_union hSC hTC', fun b hbs => ?_⟩
      have e : b = ⟨C.indicator b.1, indicator_mem_SB b.2 hC⟩ + ⟨Cᶜ.indicator b.1, indicator_mem_SB b.2 hC.compl⟩ := by
        apply Subtype.ext
        funext x
        by_cases hx : x ∈ C <;> simp [hx]
      rw [e, map_add (f := _), hb _ (fun x hx => by by_contra hc; exact hx (by simp [hc])), hb', add_zero]
      intro x hx
      have hxC : x ∉ C := by
        intro hc
        exact hx (by simp [hc])
      have hxb : b.1 x ≠ 0 := by
        intro h0
        apply hx
        simp [h0]
      exact (hbs hxb).resolve_left hxC
    · intro x hx
      rw [hsupp] at hx
      have hdet : x.det ≠ 1 := fun h1 => hx (ha x h1)
      obtain ⟨N, hN, hxN, hb⟩ := key x hdet
      exact ⟨N, mem_nhdsWithin_of_mem_nhds (hN.isOpen.mem_nhds hxN), N, hN, subset_rfl, hb⟩
  obtain ⟨C, -, hC, hb⟩ := main
  exact hb a (subset_tsupport _ |>.trans hC)
end
