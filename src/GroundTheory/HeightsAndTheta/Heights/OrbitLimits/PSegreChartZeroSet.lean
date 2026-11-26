module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartZeroSet
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeVanishingHomog
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets

namespace SegreChartZeroSet

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem scaleAll_mem (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : (fun p => c p.1 * z p) ∈ mcPts P := by
  have key : ∀ s : Finset K,
      (fun p : Σ k, ι k => (if p.1 ∈ s then c p.1 else 1) * z p) ∈ mcPts P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hz
    | insert k s hk ih =>
      have h := scaleBlock_mem_zeroLocus P hP k (hc k) ih
      convert h using 1
      funext ⟨j, a⟩
      by_cases hpk : j = k
      · subst j
        simp [scaleBlock, hk]
      · simp [scaleBlock, hpk]
  simpa using key Finset.univ

def liftPoly {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (f : MRing ι) :
    MvPolynomial (Fin m) ℂ :=
  eval₂ (algebraMap ℤ (MvPolynomial (Fin m) ℂ)) (fun p => X (σ.symm (Function.update i p.1 p.2))) f


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eval_liftPoly {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ)
    (f : MRing ι) :
    eval x (liftPoly σ i f) = eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) := by
  rw [liftPoly, hom_eval₂, eval_map]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp [chartLift]

end Lemmas

theorem proof : Statement := by
  intro K _ ι _ P m σ i hP
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ segreChartSet P σ i, eval y q = 0) → eval x q = 0 :=
      fun q hq => hx q (by rw [segreChartIdeal, mem_vanishingIdeal_iff]; exact hq)
    have ha : x (σ.symm i) = 1 := by
      have h := hv (X (σ.symm i) - 1) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        simp [hzi])
      rw [map_sub, eval_X, map_one] at h
      exact sub_eq_zero.1 h
    have hb : ∀ i' : (k : K) → ι k,
        x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k))) := by
      intro i'
      have h := hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        have hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i' := by
          have h1 := congrFun (segre_chartLift σ i z hzi) i'
          simpa [segre, chartLift] using h1
        rw [map_sub, eval_X, map_prod]
        simp only [eval_X, Equiv.apply_symm_apply]
        rw [hs, sub_self])
      rw [map_sub, eval_X, map_prod] at h
      simp only [eval_X] at h
      exact sub_eq_zero.1 h
    have hc : ∀ f ∈ P, eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) = 0 := by
      intro f hf
      rw [← eval_liftPoly]
      refine hv _ ?_
      rintro _ ⟨z, hz, hzi, rfl⟩
      rw [eval_liftPoly]
      have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
        have h1 : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
        rw [hzi] at h1
        exact one_ne_zero h1
      have hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
        funext ⟨k, j⟩
        rw [chartLift_segre_apply σ i z hzi, mul_comm]
      rw [hcl]
      exact (scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf
    refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩
    · show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1
      simp [chartLift, ha]
    · funext a
      show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩
      simp only [chartLift]
      rw [← hb, Equiv.symm_apply_apply]
  · intro x hx q hq
    rw [segreChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx

end SegreChartZeroSet

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetSimpleNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet segre_differentiableAt)

theorem PtsSheetSimpleNull.simple_of_count {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {d : ℕ} {y : Fin e → ℂ}
    (hbd : ∀ y', (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y').encard ≤ d) (hy : (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).encard = d)
    (hsh : ∀ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, ∃ γ, IsSheet P Ψ y w γ) {w : ((k : K) → ι k) → ℂ}
    (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y) : IsSimpleSheetPt P Ψ w := by
  have hF : (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).Finite := Set.finite_of_encard_eq_coe hy
  choose! γ hγ using hsh
  obtain ⟨U, hU, hdisj⟩ := hF.t2_separation

  have hev : ∀ᶠ y' in 𝓝 y, ∀ a ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y,
      (γ a y' ∈ mcPts P ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧ segre (γ a y') ∈ U a := by
    refine (hF.eventually_all).2 fun a ha => ?_
    have hc := (segre_differentiableAt (hγ a ha).2.self_of_nhds.1).continuousAt
    have hmem : U a ∈ 𝓝 (segre (γ a y)) := by
      rw [(hγ a ha).1]
      exact (hU a).2.mem_nhds (hU a).1
    filter_upwards [(hγ a ha).2, hc.preimage_mem_nhds hmem] with y' h1 h2
    exact ⟨⟨h1.2.1, h1.2.2⟩, h2⟩

  have hfib : ∀ y', (∀ a ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, (γ a y' ∈ mcPts P ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧
      segre (γ a y') ∈ U a) → ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y' = (fun a => segre (γ a y')) '' ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y := by
    intro y' h
    have hinj : Set.InjOn (fun a => segre (γ a y')) (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y) := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.mp (hdisj ha hb hne) (h a ha).2 (by simp only at hab; rw [hab]; exact (h b hb).2)
    have hsub : (fun a => segre (γ a y')) '' ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y ⊆ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y' := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨γ a y', (h a ha).1.1, rfl, (h a ha).1.2⟩
    refine ((hF.image _).eq_of_subset_of_encard_le hsub ?_).symm
    rw [hinj.encard_image, hy]
    exact hbd y'
  refine ⟨y, γ w, hγ w hw, ?_⟩
  filter_upwards [hev.prodMk_nhds ((hU w).2.mem_nhds (hU w).1)] with q hq hq2
  rw [hfib q.1 hq.1] at hq2
  obtain ⟨a, ha, hqa⟩ := hq2
  have haw : a = w := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj ha hw hne) (by rw [← hqa]; exact (hq.1 a ha).2) hq.2
  rw [← hqa, haw]

theorem PtsSheetSimpleNull.proof (hG : PtsGenericCount.Statement) : PtsSheetSimpleNull.Statement := by
  intro K _ ι _ P e Ψ hP hΨ
  obtain ⟨d, hbd, hnull⟩ := hG K ι P e Ψ hP hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (PtsSheetSimpleNull.simple_of_count hbd hgood.1 hgood.2 hw)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsGenericCount
section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsPairPoly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

namespace ComponentsGenericCount

theorem exists_pair_poly {n d : ℕ} (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hJJ' : ¬ J' ≤ J) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ x ∈ zeroSet J, x ∈ zeroSet J' → eval (A *ᵥ x) c = 0 := by
  obtain ⟨f, hfJ', hfJ⟩ := SetLike.not_le_iff_exists.1 hJJ'
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra
  have := hJ
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) := hA.finite.to_isIntegral _
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨c, hc0, fun x hx hx' => ?_⟩
  have h1 : Ideal.Quotient.mk J (pullback A c) = Ideal.Quotient.mk J (r * f) := by
    rw [map_mul]; exact hr.symm
  have h2 := hx _ (Ideal.Quotient.eq.1 h1)
  rwa [map_sub, map_mul, hx' f hfJ', mul_zero, sub_zero, ComplexSets.FibreBound.eval_pullback] at h2

theorem encard_biUnion_le {ι α : Type*} (F : Finset ι) (S : ι → Set α) :
    (⋃ i ∈ F, S i).encard ≤ ∑ i ∈ F, (S i).encard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (by gcongr)

theorem encard_biUnion_eq {ι α : Type*} (F : Finset ι) (S : ι → Set α)
    (h : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j)) :
    (⋃ i ∈ F, S i).encard = ∑ i ∈ F, (S i).encard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq, ih]
    · exact fun i hi j hj hij =>
        h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    · refine Set.disjoint_iUnion₂_right.2 fun j hj =>
        h a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) ?_
      rintro rfl
      exact ha hj

theorem exists_prod_ne_zero {ι : Type*} {k : ℕ} (F : Finset ι) (p : ι → MvPolynomial (Fin k) ℂ → Prop)
    (h : ∀ i ∈ F, ∃ P, P ≠ 0 ∧ p i P) :
    ∃ Δ : MvPolynomial (Fin k) ℂ, Δ ≠ 0 ∧
      ∀ y, eval y Δ ≠ 0 → ∀ i ∈ F, ∃ P, p i P ∧ eval y P ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨Δ, hΔ, hΔy⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨P, hP, hPa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨P * Δ, mul_ne_zero hP hΔ, fun y hy i hi => ?_⟩
    rw [map_mul] at hy
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨P, hPa, left_ne_zero_of_mul hy⟩
    · exact hΔy y (right_ne_zero_of_mul hy) i hi

end ComponentsGenericCount

end GroundTheory.Heights₂.Heights
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

namespace ComponentsGenericCount

theorem proof : ComponentsGenericCount.Statement := by
  classical
  intro n d F A hF hinc
  have hfib : ∀ y, {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y} = ⋃ J ∈ F, ComplexSets.fibre J A y := by
    intro y; ext x; simp only [ComplexSets.fibre, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]; tauto
  have hcard : ∀ J ∈ F, ∀ y, (ComplexSets.fibre J A y).encard ≤ (projDegree J A : ℕ∞) := by
    intro J hJ y
    obtain ⟨-, hfin, hle⟩ := ComplexSets.FibreBound.full n d J A (hF J hJ).1 (hF J hJ).2.1 (hF J hJ).2.2 y
    rw [← hfin.cast_ncard_eq]; exact_mod_cast hle
  refine ⟨fun y => ?_, ?_⟩
  · rw [hfib, Nat.cast_sum]
    exact (encard_biUnion_le F _).trans (Finset.sum_le_sum fun J hJ => hcard J hJ y)
  obtain ⟨Δ₁, hΔ₁, hΔ₁y⟩ := exists_prod_ne_zero F
    (fun J P => ∀ y, eval y P ≠ 0 → (ComplexSets.fibre J A y).Finite ∧ (ComplexSets.fibre J A y).ncard = projDegree J A ∧
      ∀ x ∈ ComplexSets.fibre J A y, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧
        DifferentiableOn ℂ g U ∧ g y = x ∧ ∀ y' ∈ U, A *ᵥ g y' = y' ∧ g y' ∈ zeroSet J)
    (fun J hJ => by
      obtain ⟨P, hP, hPy⟩ :=
        ComplexSets.DiscriminantCover.full n d J A (hF J hJ).1 (hF J hJ).2.1 (hF J hJ).2.2
      refine ⟨P, hP, fun y hy => ?_⟩
      obtain ⟨hfin, hc, hsec⟩ := hPy y hy
      refine ⟨hfin, hc, fun x hx => ?_⟩
      obtain ⟨U, V, g, hU, hyU, -, -, hg, hgx, hAg, hZ⟩ := hsec x hx
      refine ⟨U, g, hU, hyU, hg, hgx, fun y' hy' => ⟨hAg y' hy', ?_⟩⟩
      have hmem : g y' ∈ zeroSet J ∩ V := hZ ▸ Set.mem_image_of_mem g hy'
      exact hmem.1)
  obtain ⟨Δ₂, hΔ₂, hΔ₂y⟩ := exists_prod_ne_zero ((F ×ˢ F).filter fun p => p.1 ≠ p.2)
    (fun p c => ∀ x ∈ zeroSet p.1, x ∈ zeroSet p.2 → eval (A *ᵥ x) c = 0)
    (fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact exists_pair_poly p.1 p.2 A (hF _ hp.1.1).1 (hF _ hp.1.1).2.2
        fun h => hp.2 (hinc _ hp.1.2 _ hp.1.1 h).symm)
  refine ⟨Δ₁ * Δ₂, mul_ne_zero hΔ₁ hΔ₂, fun y hy => ?_⟩
  rw [map_mul] at hy
  have h1 := hΔ₁y y (left_ne_zero_of_mul hy)
  have h2 := hΔ₂y y (right_ne_zero_of_mul hy)
  refine ⟨?_, ?_⟩
  · rw [hfib, Nat.cast_sum, encard_biUnion_eq]
    · refine Finset.sum_congr rfl fun J hJ => ?_
      obtain ⟨P, hP, hPy⟩ := h1 J hJ
      obtain ⟨hfin, hc, -⟩ := hP y hPy
      rw [← hfin.cast_ncard_eq, hc]
    · intro J hJ J' hJ' hne
      rw [Set.disjoint_left]
      rintro x ⟨hxJ, hxy⟩ ⟨hxJ', -⟩
      obtain ⟨c, hc, hcy⟩ := h2 (J, J') (by simp [hJ, hJ', hne])
      exact hcy (by rw [← hxy]; exact hc x hxJ hxJ')
  · rintro x ⟨J, hJ, hxJ⟩ hxy
    obtain ⟨P, hP, hPy⟩ := h1 J hJ
    obtain ⟨U, g, hU, hyU, hg, hgx, hsec⟩ := (hP y hPy).2.2 x ⟨hxJ, hxy⟩
    exact ⟨U, g, hU, hyU, hg, hgx, fun y' hy' => ⟨(hsec y' hy').1, J, hJ, (hsec y' hy').2⟩⟩

end ComponentsGenericCount

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ContractMixedField

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [Fintype K'] in
theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRingOver F ι} {a : K → ℕ} (ht : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename v t) (Function.extend κ a 0) := by
  classical
  have ht' := (Bridge.isMultiHomog_iff t a).mpr ht
  refine (Bridge.isMultiHomog_iff _ _).mp ?_
  have e := FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent hv.2.2.1 hv.1 hv.2.1 a t
  rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same ht'] at e
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _


omit [Fintype K] [Fintype K'] in
theorem isMultiProjPrime_imageVar {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W : Ideal (MRingOver F ι')} (hW : IsMultiProjPrime W) : IsMultiProjPrime (imageVar F v W) := by
  classical
  have h := FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (R := F) hv.2.2.1 hv.1 hv.2.1
    (fun w hw => hv.2.2.2 w hw) ((Bridge.isMultiProjPrime_iff W).mpr hW)
  exact (Bridge.isMultiProjPrime_iff _).mp h

theorem exists_dim {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver F ι ⧸ V) = D := by
  classical
  have := hV.1
  have hmh := (Bridge.isMultiHomogIdeal_iff V).mpr hV.2.1
  exact FieldNumbers.PFContracted.exists_ringKrullDim_eq
    (fun T q hq => FieldNumbers.PFContracted.killBlocks_mem_of_isMultiHomogIdeal hmh T hq) hV.2.2

theorem mem_divSupp_of_ne_zero {P : Ideal (MRingOver F ι)} {s : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0) : W ∈ divSupp P s := by
  classical
  by_contra hW
  apply h
  simp [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, hW]

theorem component [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {V' : Ideal (MRingOver F ι')} {n d₀ : ℕ} (hV' : IsProjVarF V' (n + 1))
    (hI : IsProjVarF (imageVar F v V') d₀) {t : MRingOver F ι} {a : K → ℕ} (ht : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a)
    (htV : t ∉ imageVar F v V') {W : Ideal (MRingOver F ι')} (hW : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V' (rename v t) W ≠ 0) :
    IsProjVarF W n ∧ ∃ d₁ : ℕ, d₁ < d₀ ∧ IsProjVarF (imageVar F v W) d₁ := by
  classical
  have hWs := mem_divSupp_of_ne_zero hW
  have hVW : V' ≤ W := le_sup_left.trans hWs.1.1.2
  have htW : rename v t ∈ W := hWs.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hrel : FieldNumbers.relDim V' = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    NumbersDVR.relDim_eq_of_ringKrullDim V' (n + 1) hV'.2
  have hW' : NumbersDVR.divCycle V' (rename v t) W ≠ 0 := by
    rw [← NumbersDVR.VocabDivCycle.proof F K' ι' V' (rename v t) W]
    exact_mod_cast hW
  obtain ⟨hWm, hWd⟩ := FieldNumbers.DivCycleSupport.full F K' ι' V' ((Bridge.isMultiProjPrime_iff V').mpr hV'.1)
    n hrel (Function.extend κ a 0) (rename v t)
    ((Bridge.isMultiHomog_iff _ _).mpr (isMultiHomog_rename hv ht)) (fun h => htV h) W hW'
  have hWm' := (Bridge.isMultiProjPrime_iff W).mp hWm
  refine ⟨⟨hWm', NumbersDVR.Numbers.ringKrullDim_eq_of_relDim W n hWd⟩, ?_⟩
  have hIm := isMultiProjPrime_imageVar hv hWm'
  obtain ⟨D, hKD, hD⟩ := exists_dim hIm
  have hle : imageVar F v V' ≤ imageVar F v W := Ideal.comap_mono hVW
  have : (imageVar F v V').IsPrime := hI.1.1
  have hdim := Inter.krullDim_quot_add_one_le hle (show t ∈ imageVar F v W from htW) htV
  rw [hD, hI.2] at hdim
  have hD' : D + 1 ≤ d₀ + Fintype.card K := by exact_mod_cast hdim
  refine ⟨D - Fintype.card K, by omega, hIm, ?_⟩
  rw [hD, Nat.sub_add_cancel hKD]


open Classical in
theorem intNum_eq_zero [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n : ℕ) (V' : Ideal (MRingOver F ι')) (d₀ : ℕ) (bs : Fin n → K' → ℤ),
      IsProjVarF V' n → IsProjVarF (imageVar F v V') d₀ →
      d₀ < (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) →
      NumbersDVR.intNum F V' bs = 0 := by
  intro n
  induction n with
  | zero =>
    intro V' d₀ bs _ _ h
    simp at h
  | succ n ih =>
    intro V' d₀ bs hV' hI hcount
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (ne_of_gt (lt_of_le_of_lt (Nat.zero_le d₀) hcount))
    obtain ⟨a, ha⟩ : ∃ a : K → ℤ, bs i = pullDeg κ a := by
      by_contra h
      exact hi (if_neg h)
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = i :=
      ⟨Equiv.swap i (Fin.last n), Equiv.swap_apply_right _ _⟩
    rw [← FieldNumbers.IntNumSymm.full F K' ι' V' (n + 1) bs σ]
    have hlast : (bs ∘ σ) (Fin.last n) = pullDeg κ a := by
      show bs (σ (Fin.last n)) = _
      rw [hσ, ha]
    have e : bs ∘ σ = Fin.snoc (α := fun _ => K' → ℤ) (Fin.init (bs ∘ σ)) (pullDeg κ a) := by
      rw [← hlast]
      exact (Fin.snoc_init_self _).symm

    have hsum : (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) =
        (∑ j : Fin n, if ∃ a : K → ℤ, Fin.init (bs ∘ σ) j = pullDeg κ a then 1 else 0) + 1 := by
      rw [← Equiv.sum_comp σ (fun j => if ∃ a : K → ℤ, bs j = pullDeg κ a then 1 else 0),
        Fin.sum_univ_castSucc, hσ, if_pos ⟨a, ha⟩]
      rfl

    classical
    obtain ⟨bf, bg, f, g, hf, hg, hfI, hgI, hfg⟩ :=
      FieldNumbers.ExistsForm.full F K ι _ ((Bridge.isMultiProjPrime_iff _).mpr hI.1) a
    have hf' := (Bridge.isMultiHomog_iff f bf).mp hf
    have hg' := (Bridge.isMultiHomog_iff g bg).mp hg
    have hsec : IsRatSection V' (pullDeg κ a) (rename v f) (rename v g) := by
      refine ⟨Function.extend κ bf 0, Function.extend κ bg 0, isMultiHomog_rename hv hf',
        isMultiHomog_rename hv hg', fun h => hfI h, fun h => hgI h, fun k' => ?_⟩
      by_cases hk : ∃ k, κ k = k'
      · obtain ⟨k, rfl⟩ := hk
        simp only [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, hv.1.extend_apply, ← hfg]
      · simp only [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, Function.extend_apply' _ _ _ hk, Pi.zero_apply,
          Nat.cast_zero, sub_zero]
    have key := (NumbersDVR.IntNumIsFieldIntersection.full F K' ι').2 V' n (Fin.init (bs ∘ σ)) _ _ _ hV' hsec
    dsimp only at key
    rw [e, key]
    unfold cycEval Finsupp.sum
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [Finsupp.mem_support_iff] at hW
    suffices h0 : NumbersDVR.intNum F W (Fin.init (bs ∘ σ)) = 0 by simp only [h0, mul_zero]
    have hcases : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V' (rename v f) W ≠ 0 ∨ ReciprocityTheory.ChartRestriction.G.Geo.divCycle V' (rename v g) W ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hW
      simp [ratDiv, hc.1, hc.2]
    have hpair : IsProjVarF W n ∧ ∃ d₁ : ℕ, d₁ < d₀ ∧ IsProjVarF (imageVar F v W) d₁ := by
      rcases hcases with hc | hc
      · exact component hv hV' hI hf' (fun h => hfI h) hc
      · exact component hv hV' hI hg' (fun h => hgI h) hc
    obtain ⟨hWn, d₁, hd₁, hWI⟩ := hpair
    exact ih W d₁ _ hWn hWI (by omega)

end ContractMixedField


open ContractMixedField in
theorem contractMixedField : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedFieldStatement := by
  unfold ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedFieldStatement
  intro F _ K _ ι _ K' _ ι' _ J' hJ' κ v V' d₀ d r L N hv hV' hI hd
  classical
  rw [NumbersDVR.Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
    FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full J' hJ' V' (d + r) _ hV']
  refine intNum_eq_zero hv (d + r) V' d₀ _ hV' hI ?_
  rw [Fin.sum_univ_add]
  have h1 : ∀ j : Fin d, (if ∃ a : K → ℤ, Fin.append (fun j => pullDeg κ (L j)) N (Fin.castAdd r j) =
      pullDeg κ a then 1 else 0) = 1 := fun j => if_pos ⟨L j, by rw [Fin.append_left]⟩
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftBlockDatum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def liftCoords {ι' : Type} [Fintype ι'] {Ω : Type} (x' : ι' → Ω) : Fin (Fintype.card ι') → Ω :=
  fun j => x' ((Fintype.equivFin ι').symm j)

def LiftBlockDatum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (a : ℕ)
    (ι' : Type) [Fintype ι'] (x' : ι' → Ω),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    1 ≤ a → (∀ j, x' j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) x' →
    Birational (fun p : Σ _ : Unit, ι' => x' p.2) →
    ∃ d : HSMBlockDatum D (Option K) (addIdx ι (Fintype.card ι')) Ω,
      d.y = addBlock y (liftCoords x') ∧ d.k₀ = none ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), ∀ j : Fin (Fintype.card ι'),
        secNormAt y N a (liftCoords x' j) (basePart₂ z) * d.A.h z = ‖z ⟨none, j⟩‖) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal d.y), basePart₂ z = w

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre PBlk)
open ComplexSets

section Chart

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def projChartSet (P : Ideal (MRing ι)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, Ψ (segre z) 0 = 1 ∧ x = fun a => segre z (σ a)}

def projChartIdeal (P : Ideal (MRing ι)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (projChartSet P σ Ψ)

end Chart

def GoodChartModel.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      zeroSet (projChartIdeal P σ Ψ) = projChartSet P σ Ψ ∧
      ∀ J ∈ (projChartIdeal P σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) ∧ IsFiniteProjection J (chartProjMatrix σ Ψ)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LogRegLineTensor
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem log_regLine_tensor {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (s : MRing ι) {ε : ℝ} (hε : 0 < ε) {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((regLine A s ε ha hs).tensor A).h z) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2 := by
  have hh : 0 < A.h z := A.pos z hz
  have hreg : Real.log ((regLine A s ε ha hs).h z) = regLog A s ε z := congrFun (log_regLine A s ε ha hs) z
  have hpos : 0 < (regLine A s ε ha hs).h z := (regLine A s ε ha hs).pos z hz
  show Real.log ((regLine A s ε ha hs).h z * A.h z) = _
  rw [Real.log_mul hpos.ne' hh.ne', hreg]
  unfold regLog normSq
  set x := ‖eval z (map (Int.castRingHom ℂ) s)‖
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hnum : 0 < x ^ 2 + ε * A.h z ^ 2 := by positivity
  have hq : (x / A.h z) ^ 2 + ε = (x ^ 2 + ε * A.h z ^ 2) / A.h z ^ 2 := by
    field_simp
  rw [hq, Real.log_div hnum.ne' (pow_pos hh 2).ne', Real.log_pow]
  push_cast
  ring

theorem PoincareLelongLimit.proof (hInt : PtsIntegrableStatement) (hLel : LelongSectionLimit.Statement) :
    PoincareLelongLimit.Statement := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hAdd := Inter.PtsAddFirst.proof hInt
  have key : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) (fun z => Real.log (B.h z)) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) := by
    intro ε hε
    have h1 := Inter.ptsIntegral_add_first_log hAdd (Q := P) (e := n) (L := L)
      (M := regLine A s ε ha hsa) (N := A) (D := B) hP hL (isSmoothHerm_regLine hA hε ha hsa) hA hB hBa
    rw [log_regLine] at h1
    have h2 : ptsIntegral P (Fin.cons (fun z => Real.log (((regLine A s ε ha hsa).tensor A).h z)) (pot L))
          (fun z => Real.log (B.h z)) =
        ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) (fun z => Real.log (B.h z)) := by
      refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
      refine Fin.cases ?_ (fun i => ?_) j
      · intro z hz
        simp only [Fin.cons_zero]
        exact log_regLine_tensor A s hε ha hsa z hz.1
      · intro z _
        simp only [Fin.cons_succ]
    rw [← h2, h1]
    ring
  exact ((hLel K ι P n L A B s hP hL hA hB hBa hs).sub_const _).congr'
    (eventually_nhdsWithin_of_forall key)

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsPosDensMeasurable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

namespace PtsPosDens

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logNorm_ofWeight_one {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    logNorm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight g hg.2) 1 = g := by
  funext z
  simp [logNorm, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight, Real.exp_neg, Real.log_exp]

theorem isSmoothHerm_ofWeight {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight g hg.2) :=
  show ContDiffOn ℝ _ (fun z => Real.exp (-g z)) _ from Real.contDiff_exp.comp_contDiffOn hg.1.neg

theorem isSectionOn_ofWeight_one {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    IsSectionOn P (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight g hg.2) 1 := by
  refine ⟨0, fun k => by simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight], fun m hm k => ?_,
    fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem exists_bound {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    ∃ M : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → |g z| ≤ M := by
  set T : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ‖fun i : ι k => z ⟨k, i⟩‖ = 1} with hTdef
  have hTc : IsClosed T := by
    rw [hTdef, Set.ofPred_forall]
    exact isClosed_iInter fun k =>
      isClosed_eq (continuous_norm.comp (continuous_pi fun i => continuous_apply _)) continuous_const
  have hTb : T ⊆ Metric.closedBall 0 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    have h1 := norm_le_pi_norm (fun i : ι p.1 => z ⟨p.1, i⟩) p.2
    rw [hz p.1] at h1
    exact h1
  have hTK : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTc (Metric.isBounded_closedBall.subset hTb)
  have hTU : T ⊆ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra h
    push Not at h
    have h0 : (fun i : ι k => z ⟨k, i⟩) = 0 := funext h
    have := hz k
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨M, hM⟩ := hTK.exists_bound_of_continuousOn (hg.1.continuousOn.mono hTU)
  refine ⟨M, fun z hz => ?_⟩
  have hb : ∀ k, (fun i : ι k => z ⟨k, i⟩) ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun h0 i)
  set c : K → ℂ := fun k => ((‖fun i : ι k => z ⟨k, i⟩‖ : ℝ) : ℂ)⁻¹ with hcdef
  have hc : ∀ k, c k ≠ 0 := fun k =>
    inv_ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hb k)))
  have hmem : (fun p : Σ k, ι k => c p.1 * z p) ∈ T := by
    intro k
    have : (fun i : ι k => c k * z ⟨k, i⟩) = c k • fun i : ι k => z ⟨k, i⟩ := rfl
    rw [this, norm_smul, hcdef]
    simp only [norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hb k))
  rw [← hg.2 c z hc]
  exact hM _ hmem

theorem isSemiPosHerm_tensor {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAp : Inter.IsSemiPosHerm A) (hBp : Inter.IsSemiPosHerm B) : Inter.IsSemiPosHerm (A.tensor B) := by
  intro z hz v
  have hU : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := isOpen_blockNonzero
  have hline : Continuous fun t : ℂ => z + t • v := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), z + t • v ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    refine hline.continuousAt.preimage_mem_nhds ?_
    simpa using hU.mem_nhds hz
  have hsm : ∀ C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm C →
      ContDiffAt ℝ 2 (fun t : ℂ => Real.log (C.h (z + t • v))) 0 := by
    intro C hC
    have h1 : ContDiffAt ℝ 2 C.h (z + (0 : ℂ) • v) := by
      rw [zero_smul, add_zero]
      exact (hC.contDiffAt (hU.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)
    have h2 : ContDiffAt ℝ 2 (fun t : ℂ => z + t • v) 0 := by fun_prop
    have h3 := h1.comp (0 : ℂ) h2
    refine h3.log ?_
    simp only [Function.comp, zero_smul, add_zero]
    exact (C.pos z hz).ne'
  have heq : (fun t : ℂ => Real.log ((A.tensor B).h (z + t • v))) =ᶠ[𝓝 0]
      (fun t : ℂ => Real.log (A.h (z + t • v))) + fun t : ℂ => Real.log (B.h (z + t • v)) := by
    filter_upwards [hev] with t ht
    simp only [Pi.add_apply, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor]
    exact Real.log_mul (A.pos _ ht).ne' (B.pos _ ht).ne'
  rw [(laplacian_congr_nhds heq).eq_of_nhds, (hsm A hA).laplacian_add (hsm B hB)]
  exact add_nonneg (hAp z hz v) (hBp z hz v)

theorem aestronglyMeasurable {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) :
    AEStronglyMeasurable (ptsPosDens P Ψ (pot L) g) := by
  classical
  have hfin := fibreFinite K ι P e Ψ hP hΨ
  obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin
  have hind := sheetIndep K ι P e Ψ L _ 1 hP hΨ hL (isSmoothHerm_ofWeight hg) (isSectionOn_ofWeight_one hP hg)
  rw [logNorm_ofWeight_one hg] at hind
  have hsheet : ∀ m, ∀ y ∈ B m, IsSheet P Ψ y (segre (γ m y)) (γ m) := fun m y hy =>
    ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun m y hy =>
    (hlift m y hy).2.1.1
  have hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _
  set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m =>
    (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef
  have hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y) := fun m y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hσm : ∀ m, Measurable (σ m) := fun m =>
    (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set a : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m).piecewise (fun y => g (γ m y)) 0 with hadef
  have ham : ∀ m, Measurable (a m) := fun m =>
    (hg.1.continuousOn.comp (hγc m) (hO m)).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set dens : ℕ → (Fin e → ℂ) → ℝ := fun m y =>
    max (a m y * maDensity (fun j y' => pot L j (γ m y')) y) 0 with hddef
  have hdm : ∀ m, Measurable (dens m) := fun m =>
    ((ham m).mul (PtsSumMeasurable.measurable_maDensity _)).max measurable_const
  have hdens : ∀ m, ∀ y ∈ B m,
      dens m y = max (g (γ m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 := by
    intro m y hy
    simp only [hddef, hadef, Set.piecewise_eq_of_mem _ _ _ hy]
  set S : ℕ → Set (Fin e → ℂ) := fun m =>
    {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hSdef
  have hSm : ∀ m, MeasurableSet (S m) := by
    intro m
    have : S m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ := by
      ext y
      simp [hSdef, imp_iff_not_or]
    rw [this]
    exact (hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ =>
      ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)
  set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (S m).indicator (dens m) with hfdef
  have hfm : ∀ m, Measurable (f m) := fun m => (hdm m).indicator (hSm m)
  have hpp : ptsPosDens P Ψ (pot L) g =
      fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 := rfl
  rw [hpp]
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y)
    (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_
  filter_upwards [hind] with y hy
  have hterm : ∀ m, y ∈ S m → f m y = max (sheetDensity P Ψ (pot L) g y (σ m y)) 0 := by
    intro m hm
    have hsh := hsheet m y hm.1
    rw [← hσB m y hm.1] at hsh
    have hex : ∃ γ', IsSheet P Ψ y (σ m y) γ' := ⟨_, hsh⟩
    rw [hfdef]
    simp only
    rw [Set.indicator_of_mem hm, hdens m y hm.1]
    unfold sheetDensity
    rw [dite_eq_left hex]
    rw [hy _ _ _ hex.choose_spec hsh]
  have hmemF : ∀ m, y ∈ S m → σ m y ∈ (hfin y).toFinset := by
    intro m hm
    rw [Set.Finite.mem_toFinset, hσB m y hm.1]
    exact ⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩
  have hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y := by
    intro m
    rw [Finset.sum_ite_eq]
    by_cases hm : y ∈ S m
    · rw [if_pos (hmemF m hm)]
    · split_ifs
      · rfl
      · rw [hfdef]
        simp only
        rw [Set.indicator_of_notMem hm]
  have hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop,
      max (sheetDensity P Ψ (pot L) g y w) 0 =
        ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0 := by
    intro w _
    by_cases hex : ∃ γ', IsSheet P Ψ y w γ'
    · obtain ⟨γ', hγ'⟩ := hex
      have hP' : ∃ m, y ∈ B m ∧ σ m y = w := by
        obtain ⟨m, hm, hmw⟩ := hcov y w γ' hγ'
        exact ⟨m, hm, (hσB m y hm).trans hmw⟩
      obtain ⟨hm1B, hm1w⟩ := Nat.find_spec hP'
      have hm1S : y ∈ S (Nat.find hP') :=
        ⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩
      filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN
      rw [Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w,
        hterm _ hm1S, hm1w]
      intro m _ hne
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · exfalso
          have hle : Nat.find hP' ≤ m := Nat.find_min' hP' ⟨hmS.1, hmw⟩
          exact hmS.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
    · have h0 : sheetDensity P Ψ (pot L) g y w = 0 := by
        unfold sheetDensity
        rw [dite_eq_right hex]
      refine Eventually.of_forall fun N => ?_
      rw [h0, max_self]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · have hsh := hsheet m y hmS.1
          rw [← hσB m y hmS.1, hmw] at hsh
          exact absurd ⟨_, hsh⟩ hex
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
  have hsum : ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 =
      ∑ w ∈ (hfin y).toFinset, max (sheetDensity P Ψ (pot L) g y w) 0 :=
    finsum_mem_eq_finite_toFinset_sum _ (hfin y)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => hfy m

end PtsPosDens

end GroundTheory.Heights₂.Heights
end
end
