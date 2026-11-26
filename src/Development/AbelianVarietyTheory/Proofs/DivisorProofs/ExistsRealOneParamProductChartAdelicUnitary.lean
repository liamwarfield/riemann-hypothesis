module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianUnitaryGroupOneParameterChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianUnitaryGroupOneParameterChart
open Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.UnitaryGroupChart

open Filter

theorem chart_general {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
    (σ : E →ₗ[ℝ] E) (hσ : ∀ a, σ (σ a) = a) (hm : ∀ a b, σ (a * b) = σ b * σ a) (h1 : σ 1 = 1)
    {d e : ℕ} (Z : Fin d → E) (j : Fin e → Fin d) (hZσ : ∀ a, σ (Z a) = -Z a)
    (hli : LinearIndependent ℝ (fun i => Z (j i)))
    (hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) :
    ∃ s : E → (Fin d → ℝ), ContinuousAt s 1 ∧
      ∀ᶠ g in 𝓝 (1 : E), σ g * g = 1 →
        g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  have hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := fun a => by
    have hp : ∀ m : ℕ, σ (a ^ m) = σ a ^ m := fun m => by
      induction m with
      | zero => simpa using h1
      | succ m ih => rw [pow_succ, hm, ih, pow_succ']
    have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom
      σ.continuous_of_finiteDimensional
    refine h2.unique ?_
    convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1
    funext m
    simp [hp]
  let cL : (Fin e → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    Fintype.linearCombination ℝ (fun i => Pi.single (j i) (1 : ℝ))
  let cC : (Fin e → ℝ) →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap cL
  have hcC : ∀ t, cC t = cL t := fun _ => rfl
  have hsum : ∀ t : Fin e → ℝ, ∑ a, cL t a • Z a = ∑ i, t i • Z (j i) := fun t => by
    simp only [cL, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ite_smul]
  set Θ : (Fin e → ℝ) → E :=
    fun t => (List.ofFn fun a => NormedSpace.exp (cL t a • Z a)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hu
      rw [hexp, map_smul, hZσ, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
        ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]
      simp)
  let T : (Fin e → ℝ) →L[ℝ] E :=
    ∑ a, (ContinuousLinearMap.toSpanSingleton ℝ (Z a)).comp ((ContinuousLinearMap.proj a).comp cC)
  have hT : ∀ t, T t = ∑ i, t i • Z (j i) := fun t => by
    rw [← hsum]
    simp [T, hcC]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod d
      (fun a (t : Fin e → ℝ) => NormedSpace.exp (cL t a • Z a)) _ (fun a => by
        refine ⟨by simp, ?_⟩
        have hd : HasStrictFDerivAt (fun s : ℝ => NormedSpace.exp (s • Z a))
            (ContinuousLinearMap.toSpanSingleton ℝ (Z a))
            (((ContinuousLinearMap.proj a).comp cC) 0) := by
          rw [map_zero]
          simpa using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (Z a) (0 : ℝ)).hasStrictFDerivAt
        exact hd.comp (0 : Fin e → ℝ) ((ContinuousLinearMap.proj a).comp cC).hasStrictFDerivAt)
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.UnitaryChart.exists_skew_coord σ (fun i => Z (j i)) hσ hli
    (fun i => hZσ (j i)) hsp
  have hΨ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin e → ℝ) : (Fin e → ℝ) →L[ℝ] (Fin e → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hP0 : P 1 = 0 := hP2 _ h1
  have hΨ0 : P (Θ 0) = 0 := by rw [h0, hP0]
  have p1 := hΨ.localInverse_continuousAt
  have p2 := hΨ.localInverse_apply_image
  have p3 := hΨ.eventually_right_inverse
  simp only [hΨ0] at p1 p2 p3
  set Ψ := hΨ.localInverse _ _ _
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := (continuous_const.sub hσc).norm.continuousAt
    exact this.eventually_le_const (by simp [h1])
  have hPt : Tendsto P (𝓝 1) (𝓝 0) := hP0 ▸ P.continuous.tendsto 1
  have hcont : ContinuousAt (fun g => Ψ (P g)) 1 :=
    ContinuousAt.comp_of_eq p1 P.continuous.continuousAt hP0
  have ht : Tendsto (fun g => Θ (Ψ (P g))) (𝓝 1) (𝓝 1) := by
    have h3 : Tendsto (fun g => Ψ (P g)) (𝓝 1) (𝓝 0) := by
      have := hcont.tendsto
      simp only [hP0, p2] at this
      exact this
    have := hD.continuousAt.tendsto.comp h3
    rwa [h0] at this
  refine ⟨fun g => cL (Ψ (P g)), cC.continuous.continuousAt.comp hcont, ?_⟩
  filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with g q1 q2 q3 hg1
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E
  exact (GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 hg1) (hP3 _ _ q1) q3 q2).symm

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem chart_matrix (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hdet : IsUnit H.det)
    (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d)
    (hZ : ∀ a, (Z a)ᴴ * H + H * Z a = 0) (hli : LinearIndependent ℝ (fun i => Z (j i)))
    (hsp : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 →
      X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) :
    ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
      ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), gᴴ * H * g = H →
        g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  have hHi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHi' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hHih : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  let σ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => H⁻¹ * xᴴ * H
      map_add' := fun x y => by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  have hs : ∀ x, σ x = H⁻¹ * xᴴ * H := fun _ => rfl
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, hHih, Matrix.mul_assoc]
    rw [hHi, Matrix.mul_one, ← Matrix.mul_assoc, hHi, Matrix.one_mul]
  have hm : ∀ a b, σ (a * b) = σ b * σ a := fun a b => by
    simp only [hs, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H, hHi', Matrix.one_mul]
  have h1 : σ 1 = 1 := by simp [hs, hHi]
  have hZσ : ∀ a, σ (Z a) = -Z a := fun a => by
    rw [hs, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left (hZ a), Matrix.mul_neg, ← Matrix.mul_assoc,
      hHi, Matrix.one_mul]
  have hsp' : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i)) := fun X hX => by
    apply hsp
    have h2 : H * σ X = Xᴴ * H := by
      rw [hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hHi', Matrix.one_mul]
    rw [← h2, hX, Matrix.mul_neg, neg_add_cancel]
  obtain ⟨s, hs1, hs2⟩ := chart_general σ hσ hm h1 Z j hZσ hli hsp'
  refine ⟨s, hs1, ?_⟩
  filter_upwards [hs2] with g hg hgu
  apply hg
  simp only [Matrix.mul_assoc] at hgu
  rw [hs, Matrix.mul_assoc, Matrix.mul_assoc, hgu, hHi]

end

theorem unitary_chart : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H → IsUnit H.det →
    ∀ (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d), Function.Injective j →
      (∀ a, a ∉ Set.range j → Z a = 0) → (∀ a, (Z a)ᴴ * H + H * Z a = 0) →
      LinearIndependent ℝ (fun i => Z (j i)) →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) →
      ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ g ∈ V, gᴴ * H * g = H → g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  intro n H hH hdet d e Z j _ _ hZ hli hsp
  obtain ⟨s, hs1, hs2⟩ := chart_matrix n H hH hdet d e Z j hZ hli hsp
  exact ⟨_, hs2, s, hs1, fun g hg => hg⟩

end GlobalTheory.UnitaryGroupChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianUnitaryGroupOneParameterChartStatement
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_unitary_group_one_parameter_chart : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H → IsUnit H.det →
    ∀ (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d), Function.Injective j →
      (∀ a, a ∉ Set.range j → Z a = 0) → (∀ a, (Z a)ᴴ * H + H * Z a = 0) →
      LinearIndependent ℝ (fun i => Z (j i)) →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) →
      ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ g ∈ V, gᴴ * H * g = H → g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  first | exact @GlobalTheory.UnitaryGroupChart.unitary_chart | exact GlobalTheory.UnitaryGroupChart.unitary_chart | (intros; apply GlobalTheory.UnitaryGroupChart.unitary_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealOneParamProductChartAdelicUnitary
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.UnitChart

open GlobalTheory.Orb (archMat)

def lieU {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * H + H * X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hX, smul_zero]

theorem exists_realLines_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) ∧
      ∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u := by
  intro F E _ _ _ _ _ σ h n J hJ
  classical
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.choice inferInstance
  let H : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ := fun w => J.map (τ w).1
  have hHu : ∀ w, IsUnit (H w).det := fun w => by
    show IsUnit (J.map (τ w).1).det
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hHh : ∀ w, (H w)ᴴ = H w := fun w => by
    ext i k
    simp only [H, conjTranspose_apply, map_apply]
    rw [← h.2.2.2, hJ.1 i k]
  let e : InfinitePlace F → ℕ := fun w => Module.finrank ℝ (lieU (H w))
  let b : ∀ w, Module.Basis (Fin (e w)) ℝ (lieU (H w)) := fun w => Module.finBasis ℝ _
  let q : (Σ w : InfinitePlace F, Fin (e w)) ≃ Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) :=
    Fintype.equivFin _
  let Zg : Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → Matrix (Fin n) (Fin n) ℂ :=
    fun a => (b (q.symm a).1 (q.symm a).2 : Matrix (Fin n) (Fin n) ℂ)
  have hZg : ∀ a, (Zg a)ᴴ * H (q.symm a).1 + H (q.symm a).1 * Zg a = 0 := fun a => (b (q.symm a).1 (q.symm a).2).2
  have hy : ∀ a (t : ℝ), ∃ y : GArch σ J (q.symm a).1,
      archMat σ J (τ (q.symm a).1) y = NormedSpace.exp (t • Zg a) := fun a t => by
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Zg a)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (hHu (q.symm a).1) (X := t • Zg a) ((lieU (H (q.symm a).1)).smul_mem t (hZg a))
    refine ⟨(archEquiv J h (τ (q.symm a).1)).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose y hy using hy
  let δ : Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → ℝ → GAd σ J :=
    fun a t => embArch σ J (q.symm a).1 (y a t)
  let Zw : InfinitePlace F → Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → Matrix (Fin n) (Fin n) ℂ :=
    fun w a => if (q.symm a).1 = w then Zg a else 0
  have hK : ∀ w a (t : ℝ), archMat σ J (τ w) (projArch σ J w (δ a t)) = NormedSpace.exp (t • Zw w a) := by
    intro w a t
    by_cases hw : (q.symm a).1 = w
    · subst hw
      simp only [δ, Zw, if_pos rfl, projArch_embArch_self, hy]
    · simp only [δ, Zw, if_neg hw, smul_zero, NormedSpace.exp_zero, projArch_embArch_ne σ J (Ne.symm hw), map_one]
  have hunit : ∀ w (g : GArch σ J w), (archMat σ J (τ w) g)ᴴ * H w * archMat σ J (τ w) g = H w := fun w g => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact (archEquiv J h (τ w) g).2
  have hinj : ∀ w, Function.Injective (archMat σ J (τ w)) := fun w g g' hg =>
    (archEquiv J h (τ w)).injective (Subtype.ext (Units.ext (by
      rwa [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at hg)))
  have hloc : ∀ w, ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin _ → ℝ),
      ContinuousAt s 1 ∧ ∀ g ∈ V, gᴴ * H w * g = H w → g = (List.ofFn fun a => NormedSpace.exp (s g a • Zw w a)).prod := by
    intro w
    have hj : Function.Injective fun i : Fin (e w) => q ⟨w, i⟩ := fun i i' hi => by
      simpa using q.injective hi
    have hZj : ∀ i, Zw w (q ⟨w, i⟩) = (b w i : Matrix (Fin n) (Fin n) ℂ) := fun i => by
      show (if (q.symm (q ⟨w, i⟩)).1 = w then Zg (q ⟨w, i⟩) else 0) = _
      rw [if_pos (by simp)]
      show ((b (q.symm (q ⟨w, i⟩)).1 (q.symm (q ⟨w, i⟩)).2 : Matrix (Fin n) (Fin n) ℂ)) = _
      rw [q.symm_apply_apply]
    refine GlobalTheory.T.hermitian_unitary_group_one_parameter_chart n (H w) (hHh w) (hHu w) _ (e w) (Zw w) (fun i => q ⟨w, i⟩) hj ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Zw]
      rw [if_neg]
      intro hw
      apply ha
      rcases hqa : q.symm a with ⟨w', i⟩
      rw [hqa] at hw
      subst hw
      have h2 := congrArg q hqa
      rw [Equiv.apply_symm_apply] at h2
      exact ⟨i, h2.symm⟩
    · intro a
      simp only [Zw]
      split_ifs with hw
      · subst hw; exact hZg a
      · simp
    · simp only [hZj]
      refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
      refine Fintype.linearIndependent_iff.1 (b w).linearIndependent c (Subtype.ext ?_) i
      simpa using hc
    · intro X hX
      simp only [hZj]
      have e1 := congrArg Subtype.val ((b w).sum_repr ⟨X, hX⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e1
      rw [← e1]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose V hV sw hsw hdec using hloc
  let gw : InfinitePlace F → GAd σ J → Matrix (Fin n) (Fin n) ℂ := fun w x => archMat σ J (τ w) (projArch σ J w x)
  have hgc : ∀ w, Continuous (gw w) := fun w =>
    (GlobalTheory.Orb.continuous_archMat σ J (τ w)).comp (continuous_projArch σ J w)
  have hg1 : ∀ w, gw w 1 = 1 := fun w => by simp [gw]
  refine ⟨_, δ, fun a => ⟨(q.symm a).1, τ _, Zg a, hZg a, fun t => ⟨y a t, rfl, hy a t⟩⟩, fun U hU => ?_⟩
  have hfc : Continuous fun x => ofFin σ J (projFin σ J x) := (continuous_ofFin σ J).comp (continuous_projFin σ J)
  refine ⟨{x | ∀ w, gw w x ∈ V w} ∩ {x | ofFin σ J (projFin σ J x) ∈ U}, ?_,
    fun x a => sw (q.symm a).1 (gw (q.symm a).1 x) a, ?_, ?_⟩
  · refine Filter.inter_mem (Filter.eventually_all.2 fun w => (hgc w).continuousAt.preimage_mem_nhds ?_)
      (hfc.continuousAt.preimage_mem_nhds ?_)
    · rw [hg1]; exact hV w
    · simpa using hU
  · exact continuousAt_pi.2 fun a =>
      (continuous_apply a).continuousAt.comp ((hsw _).comp_of_eq (hgc _).continuousAt (hg1 _))
  · intro x hx
    refine ⟨ofFin σ J (projFin σ J x), hx.2, mem_finPts.2 (projInf_ofFin _ _ _), ?_⟩
    conv_lhs => rw [← ofInf_projInf_mul_ofFin_projFin σ J x]
    congr 1
    apply GAd_ext σ J
    · intro w
      apply hinj w
      rw [projArch_ofInf, projInfArch_projInf, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      have e2 : (⇑(archMat σ J (τ w)) ∘ ⇑(projArch σ J w) ∘ fun a => δ a (sw (q.symm a).1 (gw (q.symm a).1 x) a)) =
          fun a => NormedSpace.exp (sw w (gw w x) a • Zw w a) := funext fun a => by
        simp only [Function.comp_apply]
        rw [hK]
        by_cases hw : (q.symm a).1 = w
        · subst hw; rfl
        · simp [Zw, hw]
      rw [e2]
      exact hdec w _ (hx.1 w) (hunit w _)
    · intro v
      rw [proj_ofInf, map_list_prod, List.map_ofFn]
      have e3 : (⇑(proj σ J v) ∘ fun a => δ a (sw (q.symm a).1 (gw (q.symm a).1 x) a)) = fun _ => 1 :=
        funext fun a => by simp [δ]
      rw [e3]
      simp

end GlobalTheory.UnitChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealOneParamProductChartAdelicUnitaryStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realOneParamProduct_chart_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) ∧
      ∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u := by
  first | exact @GlobalTheory.UnitChart.exists_realLines_chart | exact GlobalTheory.UnitChart.exists_realLines_chart | (intros; apply GlobalTheory.UnitChart.exists_realLines_chart <;> assumption)
end
