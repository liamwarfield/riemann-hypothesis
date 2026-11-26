module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardAddCharSymplecticLocalLatticeEqOne

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.AddCharHalfTraceTensorLatticeHeisenbergCocycle
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.VacCocycle
open _root_.GlobalTheory

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
theorem sum_four_comm (f : α → β → α → β → A) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  have h := Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun (p q : α × β) => f p.1 p.2 q.1 q.2)
  simpa only [Fintype.sum_prod_type] using h

theorem conj_hTens (hc : ∀ z, c (c z) = z) {JA : Matrix α α A} {JB : Matrix β β A}
    (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j) (x y : Matrix α β A) :
    c (GlobalTheory.WeilM.hTens c JA JB y x) = -GlobalTheory.WeilM.hTens c JA JB x y := by
  unfold GlobalTheory.WeilM.hTens
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc, hA, hB, ← Finset.sum_neg_distrib]
  rw [sum_four_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem trace_conj (hc : ∀ z, c (c z) = z) (z : A) : Algebra.trace R A (c z) = Algebra.trace R A z :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z

theorem symp_swap (hc : ∀ z, c (c z) = z) {JA : Matrix α α A} {JB : Matrix β β A}
    (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j) {ξ : A} (hξ : ξ + c ξ = 1)
    (x y : Matrix α β A) :
    GlobalTheory.WeilM.symp (R := R) c ξ JA JB y x =
      GlobalTheory.WeilM.symp (R := R) c ξ JA JB x y + GlobalTheory.WeilM.symp (R := R) c (-1) JA JB x y := by
  unfold GlobalTheory.WeilM.symp
  rw [← trace_conj c hc, map_mul, conj_hTens c hc hA hB, ← map_add (f := _)]
  congr 1
  linear_combination (-GlobalTheory.WeilM.hTens c JA JB x y) * hξ

end General

theorem psi_half_symp_add : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY θ hθ v γ hγ γ' hγ'
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hc : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : ∀ e : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have hsw := symp_swap (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) hc (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)
    (fun i j => by simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hi, hX.herm])
    (fun i j => by simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hi, hY.skew, map_neg])
    (ξ := inclR (F := F) (AF F) (θ : E)) (by rw [hi, ← map_add (f := _), hθ, map_one]) γ γ'
  have h1 := Tw.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 1
    (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
  have h2 := Tw.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v (-1) 1
    (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
  have hm : inclR (F := F) (AF F) ((-1 : 𝓞 E) : E) = -1 := by
    rw [show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one]
  rw [hm] at h2
  rw [Tw.LatVacArith.symp_add_left, Tw.LatVacArith.symp_add_right, Tw.LatVacArith.symp_add_right, hsw,
    ← mul_one (_ * _ * _), ← h1, ← mul_one (_ * _ * _ * _), ← h2]
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  have h : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
  generalize (⅟(2 : AF F)) = t at h ⊢
  linear_combination (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' +
    GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ') * h

end Tw.VacCocycle

end
end

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardTraceAdelicAddCharLocalComponentNeOne
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.PsiNontriv
open _root_.GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels WithZero
open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

theorem exists_trace_not_int (v : HeightOneSpectrum (𝓞 F)) :
    ∃ z : F, (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1) ∧
      Algebra.trace ℚ F z ∉ (algebraMap ℤ ℚ).range := by
  classical
  set C : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hC
  set N : ℕ := (-(FractionalIdeal.count F v C)).toNat + 1 with hN
  have hP : ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := by simpa using v.ne_bot
  set I : FractionalIdeal (𝓞 F)⁰ F := ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ N)⁻¹ with hI
  have hI0 : I ≠ 0 := inv_ne_zero (pow_ne_zero _ hP)
  have hcount : ∀ w, FractionalIdeal.count F w I = if w = v then -(N : ℤ) else 0 := by
    intro w
    rw [hI, FractionalIdeal.count_inv, FractionalIdeal.count_pow]
    split_ifs with hw
    · subst hw; rw [FractionalIdeal.count_self]; ring
    · rw [FractionalIdeal.count_maximal_coprime F w (Ne.symm hw)]; ring
  have hint : ∀ z ∈ I, ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1 := by
    intro z hz w hw
    have := (GlobalTheory.Idele.mem_iff_valuation_le hI0 z).1 hz w
    rwa [hcount w, if_neg hw, neg_zero, exp_zero] at this
  by_contra H
  push_neg at H
  have hle : I ≤ C := by
    intro x hx
    rw [hC, FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    intro a ha
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have hxa : x * algebraMap (𝓞 F) F a ∈ I := by
      rw [mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ a hx
    exact H _ (hint _ hxa)
  have := FractionalIdeal.count_mono F v hI0 hle
  rw [hcount v, if_pos rfl] at this
  omega

theorem psiV_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.VacAny.psiV ψ v ≠ 1 := by
  intro F _ _ ψ hψ v h1
  obtain ⟨z, hz, hzt⟩ := exists_trace_not_int (F := F) v
  have hloc : ∀ t : Fv F v, ψ (GlobalTheory.EmbChart.atPlace v t) = 1 := fun t => by
    rw [← GlobalTheory.VacAny.psiV_apply, h1, AddChar.one_apply]
  set zv : Fv F v := algebraMap F (Fv F v) z with hzv
  set α : Af F := algebraMap F (Af F) z - GlobalTheory.AdelicU.singleFin v zv with hα
  have hαint : α ∈ intAf F := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_self]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = zv := rfl
      rw [this, sub_self]
      exact zero_mem _
    · rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_ne hw, sub_zero]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = algebraMap F (Fv F w) z := rfl
      rw [this, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap]
      exact hz w hw
  have htr : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * 1) = k := by
    intro a
    have hi : IsIntegral ℤ (Algebra.trace ℚ F ((a : F) * 1)) := by
      rw [mul_one]
      exact Algebra.isIntegral_trace (NumberField.RingOfIntegers.isIntegral_coe a)
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact ⟨k, by rw [← hk]; simp⟩
  have h0 := Tw.LatVacArith.psi_int hψ 1 htr α hαint
  rw [map_one, mul_one] at h0
  have hsplit : pairA F 0 (algebraMap F (Af F) z) = pairA F 0 α + GlobalTheory.EmbChart.atPlace v zv := by
    refine Prod.ext (add_zero (0 : Ainf F)).symm ?_
    show algebraMap F (Af F) z = α + GlobalTheory.AdelicU.singleFin v zv
    rw [hα, sub_add_cancel]
  have hval : ψ (pairA F 0 (algebraMap F (Af F) z)) = 1 := by
    rw [hsplit, AddChar.map_add_eq_mul, h0, hloc, one_mul]
  rw [Tw.LatVacArith.psi_fin_rat hψ, Complex.exp_eq_one_iff] at hval
  obtain ⟨n, hn⟩ := hval
  apply hzt
  refine ⟨n, ?_⟩
  have hc : ((Algebra.trace ℚ F z : ℚ) : ℂ) = (n : ℂ) := by
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  rw [eq_intCast]
  exact_mod_cast hc.symm

end Tw.PsiNontriv
end
end
