module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)

namespace GoodChartDim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segreCone (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, x = fun a => segre z (σ a)}

theorem segreCone_smul {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) :
    ∀ c ∈ segreCone P σ, ∀ a : ℂ, a ≠ 0 → a • c ∈ segreCone P σ := by
  rintro _ ⟨z, hz, rfl⟩ a ha
  obtain ⟨z', hz', hseg⟩ := GoodChartZeroSet.exists_segre_smul P hP.2.1.2.1 hz ha
    (fun h => absurd hP.1 (not_nonempty_iff.2 h))
  exact ⟨z', hz', funext fun b => by simp [hseg]⟩


open Classical in
def psiCoeffs {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Fin m → ℂ :=
  fun a => Ψ (fun i' => if σ a = i' then (1 : ℂ) else 0) 0

theorem projChartSet_eq (P : Ideal (MRing ι)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    projChartSet P σ Ψ = {x | x ∈ segreCone P σ ∧ eval x (linForm (psiCoeffs σ Ψ)) = 1} := by
  have hl : ∀ z : (Σ k, ι k) → ℂ,
      eval (fun a => segre z (σ a)) (linForm (psiCoeffs σ Ψ)) = Ψ (segre z) 0 := fun z => by
    rw [show linForm (psiCoeffs σ Ψ) = GoodChartZeroSet.linForm σ Ψ from rfl, GoodChartZeroSet.eval_linForm]
    simp
  ext x
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, (hl z).trans h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, (hl z).symm.trans h1, rfl⟩

theorem linForm_single' {m : ℕ} (a : Fin m) : linForm (Pi.single a (1 : ℂ)) = X a := by
  classical
  simp [linForm, Pi.single_apply]


omit [∀ k, Fintype (ι k)] in
theorem segreChartSet_eq (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (a : Fin m) :
    segreChartSet P σ (σ a) = {x | x ∈ segreCone P σ ∧ eval x (linForm (Pi.single a (1 : ℂ))) = 1} := by
  ext x
  simp only [segreChartSet, segreCone, Set.mem_ofPred_eq, linForm_single', eval_X]
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, h1, rfl⟩

theorem linForm_sub_one_not_mem {m : ℕ} {V : Ideal (MvPolynomial (Fin m) ℂ)} (hV : IsHomogIdeal V) (hne : V ≠ ⊤)
    (t : Fin m → ℂ) : linForm t - 1 ∉ V := by
  intro h
  have h0 := hV _ h 0
  rw [homogeneousComponent_zero] at h0
  have hc : AddMonoidAlgebra.coeff (linForm t - 1) 0 = -1 := by
    simp [linForm, coeff_sum, coeff_C_mul, coeff_X]
  rw [hc] at h0
  exact hne (Ideal.eq_top_of_isUnit_mem _ h0 (by simp))

theorem exists_X_not_mem {m : ℕ} {W : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ} (h : linForm t ∉ W) :
    ∃ a, X a ∉ W := by
  by_contra hall
  push Not at hall
  exact h (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hall a))

theorem le_of_homog_le_sup {m : ℕ} {V W : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ} (hV : IsHomogIdeal V)
    (hW : W.IsPrime) (hWh : IsHomogIdeal W) (ht : linForm t ∉ W) (hle : V ≤ W ⊔ Ideal.span {linForm t - 1}) :
    V ≤ W := by
  intro f hf
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ => ChartDehomog.proof ℂ m W t _ d hW hWh ht
    (homogeneousComponent_isHomogeneous d f) (hle (hV f hf d))

theorem eq_of_add_one_eq {x : WithBot ℕ∞} {e : ℕ} (h : x + 1 = (e : WithBot ℕ∞) + 1) : x = e := by
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← Nat.cast_succ] at h
    exact absurd h (WithBot.bot_ne_natCast _)
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) = ((e + 1 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_inj, top_add] at h'
      exact absurd h' (by exact_mod_cast (ENat.top_ne_natCast (e + 1)))
    | coe x =>
      have h' : ((x + 1 : ℕ) : WithBot ℕ∞) = ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h'' : x + 1 = e + 1 := by exact_mod_cast h'
      exact_mod_cast (show x = e by omega)

end GoodChartDim

open GoodChartDim

theorem GoodChartDim.proof (h₁ : ConeVanishingHomog.Statement) (h₂ : ConeSliceIdeal.Statement)
    (h₃ : ChartDehomogPrime.Statement) : GoodChartDim.Statement := by
  classical
  intro K _ ι _ P e m σ Ψ hP J hJ
  have hC := segreCone_smul hP σ
  set t := psiCoeffs σ Ψ
  have hS : projChartSet P σ Ψ = {x | x ∈ segreCone P σ ∧ eval x (linForm t) = 1} := projChartSet_eq P σ Ψ
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : projChartIdeal P σ Ψ ≤ J := hJ.1.2
  set H := vanishingIdeal ℂ (segreCone P σ)
  have hH : IsHomogIdeal H := h₁ m _ hC
  have hHI : H ≤ projChartIdeal P σ Ψ := by
    rw [projChartIdeal, hS]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  have hℓ1 : linForm t - 1 ∈ projChartIdeal P σ Ψ := by
    rw [projChartIdeal, hS, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]

  obtain ⟨W, hW, hℓW, hWJ, hWcore⟩ := ChartHomogenise.proof ℂ m J t hJp (hIJ hℓ1)
  have hHW : H ≤ W := hWcore H hH (hHI.trans hIJ)
  obtain ⟨a, ha⟩ := exists_X_not_mem hℓW
  set u : Fin m → ℂ := Pi.single a 1
  have huW : linForm u ∉ W := by rw [linForm_single']; exact ha
  have hT : segreChartSet P σ (σ a) = {x | x ∈ segreCone P σ ∧ eval x (linForm u) = 1} :=
    segreChartSet_eq P σ a

  have := h₃ ℂ m W u hW huW
  have hTJ' : segreChartIdeal P σ (σ a) ≤ W ⊔ Ideal.span {linForm u - 1} := by
    rw [segreChartIdeal, hT]; exact h₂ m _ u W hC hHW
  obtain ⟨Q₀, hQ₀, hQ₀J'⟩ := Ideal.exists_minimalPrimes_le hTJ'
  have hdimQ₀ := SegreChartDim.proof K ι P e m σ (σ a) hP Q₀ (mem_segreChartComponents.2 hQ₀)
  have hu1 : linForm u - 1 ∈ segreChartIdeal P σ (σ a) := by
    rw [segreChartIdeal, hT, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]
  have hHT : H ≤ segreChartIdeal P σ (σ a) := by
    rw [segreChartIdeal, hT]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  obtain ⟨V, hV, huV, hVQ₀, hVcore⟩ := ChartHomogenise.proof ℂ m Q₀ u hQ₀.1.1 (hQ₀.1.2 hu1)
  have hHV : H ≤ V := hVcore H hH (hHT.trans hQ₀.1.2)
  have hVW : V ≤ W := le_of_homog_le_sup hV.isHomog hW.isPrime hW.isHomog huW
    ((le_sup_left.trans hVQ₀.le).trans hQ₀J')

  have hIV : projChartIdeal P σ Ψ ≤ V ⊔ Ideal.span {linForm t - 1} := by
    rw [projChartIdeal, hS]; exact h₂ m _ t V hC hHV
  have hVJ : V ⊔ Ideal.span {linForm t - 1} ≤ J :=
    sup_le (hVW.trans (le_sup_left.trans hWJ.le)) ((Ideal.span_singleton_le_iff_mem _).2 (hIJ hℓ1))
  have hJmin : J ∈ (V ⊔ Ideal.span {linForm t - 1}).minimalPrimes :=
    ⟨⟨hJp, hVJ⟩, fun Z hZ hZJ => hJ.2 ⟨hZ.1, hIV.trans hZ.2⟩ hZJ⟩
  have hQ₀min : Q₀ ∈ (V ⊔ Ideal.span {linForm u - 1}).minimalPrimes := by
    have := hQ₀.1.1
    rw [hVQ₀, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have d₁ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V J (linForm t - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top t) hJmin
  have d₂ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V Q₀ (linForm u - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top u) hQ₀min
  rw [← d₂, hdimQ₀] at d₁
  exact eq_of_add_one_eq d₁

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartProjFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix

theorem homogeneousComponent_mem_leadIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  · rw [homogeneousComponent_eq_zero (n := r) (φ := f) h]
    exact zero_mem _

theorem eval_linPoly_eq_mulVec {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem SegreChartProjFinite.pow_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hΨ0 : ∀ w, Ψ w 0 = w i)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := segre_rel hP.2.1.2.1 Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine (mem_segreChartComponents.1 hJ).1.2 ?_
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hzi, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hΨ0, hzi, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, Gx, map_sub, map_add (f := _), map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
      eval_linPoly_eq_mulVec, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, map_sub, map_add (f := _), map_sum, hX, h0, zero_add,
      homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

theorem SegreChartProjFinite.proof : SegreChartProjFinite.Statement := by
  intro K _ ι _ P e m σ i Ψ hP hΨ hΨ0 J hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := SegreChartProjFinite.pow_mem hP hΨ hΨ0 hJ a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨FiniteProjHomInjective.proof m e J _ (mem_segreChartComponents.1 hJ).1.1
    (SegreChartDim.proof K ι P e m σ i hP J hJ) hfin, hfin⟩

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralSegreChartProj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (ptsIntegralAt)
open ComplexSets

theorem PtsIntegralSegreChartProj.proof (hFin : SegreChartProjFinite.Statement)
    (hZero : SegreChartZeroSet.Statement) (hAbs : SegreChartAbsIntegrable.Statement)
    (hSum : PtsSegreChartFibreSum.Statement) : PtsIntegralSegreChartProj.Statement := by
  intro K _ _ ι _ P e m σ i L g Ψ G Φ hP hL hg hΨ hΨ0 hgerm
  set A := chartProjMatrix σ Ψ
  set G' := chartWeight σ i g with hG'
  set Φ' := chartPot σ i L
  have hcoordS : ∀ x ∈ segreChartSet P σ i, x (σ.symm i) = 1 := by
    rintro _ ⟨z, -, hzi, rfl⟩
    simpa using hzi
  have hchart : ∀ J ∈ segreChartComponents P σ i, zeroSet J ⊆ segreChartSet P σ i := by
    intro J hJ x hx
    rw [← hZero K ι P m σ i hP.2.1.2.1]
    exact fun q hq => hx q ((mem_segreChartComponents.1 hJ).1.2 hq)
  have hprime : ∀ J ∈ segreChartComponents P σ i, J.IsPrime := fun J hJ =>
    (mem_segreChartComponents.1 hJ).1.1
  have hdim : ∀ J ∈ segreChartComponents P σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) := fun J hJ =>
    SegreChartDim.proof K ι P (e + 1) m σ i hP J hJ
  have hfin : ∀ J ∈ segreChartComponents P σ i, IsFiniteProjection J A :=
    hFin K ι P (e + 1) m σ i Ψ hP hΨ hΨ0
  have hmeas : Measurable G' := measurable_chartWeight σ i hg
  have hsm : ∀ J ∈ segreChartComponents P σ i, ∀ k, SmoothNear (zeroSet J) (Φ' k) := fun J hJ =>
    smoothNear_chartPot σ i hL fun x hx => chart_coord_eq_one hJ hx
  have habs : ∀ J ∈ segreChartComponents P σ i, Integrable (chartAbsDens J A G' Φ') := fun J hJ =>
    hAbs K ι P (e + 1) m σ i L g hP hL hg J hJ A (hfin J hJ)
  have hint : ∀ J ∈ segreChartComponents P σ i, Integrable (chartDens J A G' Φ') := by
    intro J hJ
    refine (habs J hJ).mono' (SheetSumMeasurable.full m (e + 1) J A G' Φ' (hprime J hJ) (hdim J hJ)
      (hfin J hJ) hmeas (hsm J hJ)).1.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens sheetSum
    refine (abs_finsum_mem_le_finsum_mem_abs _ _).trans (le_of_eq (finsum_mem_congr rfl fun x _ => ?_))
    split_ifs <;> simp

  have hcong : ∀ J ∈ segreChartComponents P σ i, ∀ A₁ : Matrix (Fin (e + 1)) (Fin m) ℂ,
      chartDens J A₁ G Φ = chartDens J A₁ G' Φ' := by
    intro J hJ A₁
    funext y
    unfold chartDens sheetSum
    refine finsum_mem_congr rfl fun x hx => ?_
    have hxS : x ∈ segreChartSet P σ i := hchart J hJ hx.1
    split_ifs with h
    · obtain ⟨U, hU, hyU, hdiff, hsx, -, -⟩ := h.choose_spec
      have hy : A₁ *ᵥ x = y := hx.2
      have hG : G x = G' x := by
        rw [hG', chartWeight_of_coord g (hcoordS x hxS)]
        exact (hgerm x hxS).1.eq_of_nhds
      have hcont : Tendsto h.choose (𝓝 y) (𝓝 x) := by
        have := (hdiff.continuousOn.continuousAt (hU.mem_nhds hyU)).tendsto
        rwa [hsx, hy] at this
      beta_reduce
      rw [hG]
      congr 1
      exact ReciprocityTheory.AnForm.M.maDens_congr_eventuallyEq fun k => ((hgerm x hxS).2 k).comp_tendsto hcont
    · rfl

  have hvar : ∀ J ∈ segreChartComponents P σ i, varInt J (e + 1) G Φ = ∫ y, chartDens J A G' Φ' y := by
    intro J hJ
    have hex : ∃ A₁ : Matrix (Fin (e + 1)) (Fin m) ℂ, IsFiniteProjection J A₁ := ⟨A, hfin J hJ⟩
    rw [varInt, dite_eq_left hex, chartInt, hcong J hJ]
    exact (IntegralIndep.full m (e + 1) J A hex.choose G' Φ' (hprime J hJ) (hdim J hJ) (hfin J hJ)
      hex.choose_spec hmeas (hsm J hJ) (habs J hJ)).2.symm
  rw [Finset.sum_congr rfl hvar, ← integral_finsetSum _ hint]
  unfold ptsIntegralAt
  refine integral_congr_ae ?_
  filter_upwards [hSum K ι P (e + 1) m σ i L g Ψ hP hL hg hΨ hΨ0] with y hy
  exact hy

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorComponents
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal IsRelevant IsMultiHomogIdeal mcPts
  segre divSupp_finite divSuppArith mcPts_smul)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartIdeal segreChartComponents mem_segreChartComponents chartLift
  chartLift_segre_apply segre_chartLift chartLift_blockNonzero)

namespace ChartDivisorComponents

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {m : ℕ}

theorem chartLift_mem_mcPts {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) {x : Fin m → ℂ} (hx : x ∈ segreChartSet P σ i) : chartLift σ i x ∈ mcPts P := by
  obtain ⟨z, hz, hzi, rfl⟩ := hx
  have hne : ∀ k, (z ⟨k, i k⟩)⁻¹ ≠ 0 := fun k => inv_ne_zero fun h0 => by
    have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hzi] at this
    exact one_ne_zero this
  have heq : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
    funext p
    rw [chartLift_segre_apply σ i z hzi p.1 p.2, mul_comm]
  rw [heq]
  exact mcPts_smul hP (fun k => (z ⟨k, i k⟩)⁻¹) hne hz

theorem chartSection_mem {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) {f : MRing ι} (hf : f ∈ P) : chartSection σ i f ∈ segreChartIdeal P σ i := by
  rw [segreChartIdeal, mem_vanishingIdeal_iff]
  intro x hx
  change eval x (chartSection σ i f) = 0
  rw [eval_chartSection]
  exact (chartLift_mem_mcPts hP σ i hx).2 f hf

theorem mem_segreChartSet_of_forall {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) {x : Fin m → ℂ} (hx : ∀ f ∈ segreChartIdeal P σ i, eval x f = 0) :
    x ∈ segreChartSet P σ i := by
  have hxi : x (σ.symm i) = 1 := by
    have hmem : (X (σ.symm i) - 1 : MvPolynomial (Fin m) ℂ) ∈ segreChartIdeal P σ i := by
      rw [segreChartIdeal, mem_vanishingIdeal_iff]
      rintro _ ⟨z, -, hzi, rfl⟩
      simp [hzi]
    have h := hx _ hmem
    simp only [map_sub, eval_X, map_one] at h
    exact sub_eq_zero.1 h
  have hseg : ∀ a, x a = segre (chartLift σ i x) (σ a) := by
    intro a
    have hmem : (X a - ∏ k, X (σ.symm (Function.update i k (σ a k))) : MvPolynomial (Fin m) ℂ) ∈
        segreChartIdeal P σ i := by
      rw [segreChartIdeal, mem_vanishingIdeal_iff]
      rintro _ ⟨z, -, hzi, rfl⟩
      have h := congrFun (segre_chartLift σ i z hzi) (σ a)
      change eval _ (X a - ∏ k, X (σ.symm (Function.update i k (σ a k)))) = 0
      rw [map_sub, map_prod, sub_eq_zero]
      simp only [eval_X]
      exact h.symm.trans rfl
    have h := hx _ hmem
    simp only [map_sub, eval_X, map_prod] at h
    rw [sub_eq_zero] at h
    rw [h]
    rfl
  refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i hxi, fun f hf => ?_⟩, ?_, funext hseg⟩
  · rw [← eval_chartSection]
    exact hx _ (chartSection_mem hP σ i hf)
  · show ∏ k, x (σ.symm (Function.update i k (i k))) = 1
    simp [hxi]

theorem exists_divSupp_of_eval {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) (s : MRing ι) {x : Fin m → ℂ} (hx : x ∈ segreChartSet P σ i)
    (hs : eval x (chartSection σ i s) = 0) :
    ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ x ∈ segreChartSet W σ i := by
  have hz := chartLift_mem_mcPts hP σ i hx
  obtain ⟨z₀, -, hz₀i, hxz₀⟩ := hx
  set z := chartLift σ i x with hzdef
  have hsz : segre z = segre z₀ := by rw [hzdef, hxz₀]; exact segre_chartLift σ i z₀ hz₀i
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hφ : ∀ f, φ f = eval z (map (Int.castRingHom ℂ) f) := fun _ => rfl
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    refine sup_le (fun f hf => by rw [RingHom.mem_ker, hφ]; exact hz.2 f hf) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hφ, ← eval_chartSection]
    exact hs
  obtain ⟨W, hW, hWle⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨W, ⟨⟨hW, fun k => ?_⟩, ?_⟩, z, ⟨hz.1, fun f hf => hWle hf⟩, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hz.1 k
    exact ⟨j, fun h => hj (by simpa [hφ] using hWle h)⟩
  · refine eq_bot_iff.2 fun c hc => ?_
    have h := hWle hc
    rw [RingHom.mem_ker, hφ] at h
    simpa using h
  · rw [hsz]; exact hz₀i
  · rw [hsz]; exact hxz₀

theorem eq_of_le_of_dim {Q Q' : Ideal (MvPolynomial (Fin m) ℂ)} [Q.IsPrime] (hle : Q ≤ Q') (n : ℕ)
    (hQ : ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ Q) + 1 = ((n + 1 : ℕ) : WithBot ℕ∞))
    (hQ' : ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ Q') = (n : ℕ)) : Q = Q' := by
  by_contra hne
  have h := SectionComponents.ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hle hne)
  rw [hQ'] at h
  have h2 : ((n : ℕ) : WithBot ℕ∞) + 1 + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hQ]
    exact add_le_add h le_rfl
  have h3 : ((n + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h2
  have h4 : n + 1 + 1 ≤ n + 1 := by exact_mod_cast h3
  omega

theorem le_of_common (hNot : ChartSectionNotMem.Statement) {W₁ W₂ : Ideal (MRing ι)} {n : ℕ}
    (h₁ : IsArithVar W₁ (n + 1)) (h₂ : IsMultiHomogIdeal W₂) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {W' : Ideal (MvPolynomial (Fin m) ℂ)} (hW₁ : W' ∈ segreChartComponents W₁ σ i)
    (hW₂ : W' ∈ segreChartComponents W₂ σ i) : W₂ ≤ W₁ := by
  have h₂' := h₂
  obtain ⟨S, hS, rfl⟩ := h₂
  refine Ideal.span_le.2 fun f hf => ?_
  by_contra hfW
  obtain ⟨a, ha⟩ := hS f hf
  have hsec : IsSectionOn W₁ (HermLine.sqMetric (ι := ι) a) f := ⟨a, fun _ => rfl, ha, hfW⟩
  exact hNot K ι W₁ n m σ i _ f h₁ hsec W' hW₁
    ((mem_segreChartComponents.1 hW₂).1.2 (chartSection_mem h₂' σ i (Ideal.subset_span hf)))

end ChartDivisorComponents


open ChartDivisorComponents in
theorem ChartDivisorComponents.proof (hNot : ChartSectionNotMem.Statement) : ChartDivisorComponents.Statement := by
  classical
  intro K _ _ ι _ P n m σ i A s hP hs
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  have hJdim : ∀ J ∈ segreChartComponents P σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = ((n + 1 : ℕ) : WithBot ℕ∞) :=
    SegreChartDim.proof K ι P (n + 1) m σ i hP
  have hWar : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → IsArithVar W (n + 1) :=
    fun W hW => (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
  have hWdim : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → ∀ W'' ∈ segreChartComponents W σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ W'') = (n : ℕ) :=
    fun W hW => SegreChartDim.proof K ι W n m σ i (hWar W hW)
  have hsW : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → ∀ W'' ∈ segreChartComponents W σ i,
      chartSection σ i s ∈ W'' := fun W hW W'' hW'' =>
    (mem_segreChartComponents.1 hW'').1.2 (chartSection_mem (hWar W hW).2.1.2.1 σ i
      (hW.1.1.1.2 (le_sup_right (a := P) (Ideal.mem_span_singleton_self s))))
  have hnot := hNot K ι P (n + 1) m σ i A s hP hs
  refine ⟨fun J hJ W' => ⟨fun hW' => ?_, fun ⟨hJW', W, hW, hW'c⟩ => ?_⟩, fun W₁ W₂ h₁ h₂ W' hW₁ hW₂ => ?_⟩
  · have hJp : J.IsPrime := (mem_segreChartComponents.1 hJ).1.1
    have hW'p : W'.IsPrime := hW'.1.1
    have hdim := SectionComponents.ringKrullDim_quotient_add_one_eq (hnot J hJ) hW'
    rw [hJdim J hJ] at hdim
    have hJW' : J ≤ W' := le_sup_left.trans hW'.1.2
    have hsW' : chartSection σ i s ∈ W' :=
      ((le_sup_right (a := J)).trans hW'.1.2) (Ideal.mem_span_singleton_self _)

    have key : ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ ∃ W'' ∈ segreChartComponents W σ i, W'' ≤ W' := by
      by_contra hcon
      push Not at hcon
      let g : Ideal (MRing ι) → Ideal (MvPolynomial (Fin m) ℂ) → MvPolynomial (Fin m) ℂ := fun W W'' =>
        if h : (W ∈ divSupp P s ∧ IsHorizontal W) ∧ W'' ∈ segreChartComponents W σ i then
          (SetLike.not_le_iff_exists.1 (hcon W h.1 W'' h.2)).choose else 1
      have hg : ∀ W W'', (W ∈ divSupp P s ∧ IsHorizontal W) → W'' ∈ segreChartComponents W σ i →
          g W W'' ∈ W'' ∧ g W W'' ∉ W' := fun W W'' hW hW'' => by
        simp only [g, dif_pos (And.intro hW hW'')]
        exact (SetLike.not_le_iff_exists.1 (hcon W hW W'' hW'')).choose_spec
      set T := (divSupp_finite P s).toFinset.filter IsHorizontal
      have hT : ∀ W, W ∈ T ↔ W ∈ divSupp P s ∧ IsHorizontal W := fun W => by simp [T]
      set G := ∏ W ∈ T, ∏ W'' ∈ segreChartComponents W σ i, g W W''
      apply (show G ∉ W' from fun hG => by
        rw [Ideal.IsPrime.prod_mem_iff] at hG
        obtain ⟨W, hWT, hG⟩ := hG
        rw [Ideal.IsPrime.prod_mem_iff] at hG
        obtain ⟨W'', hW'', hG⟩ := hG
        exact (hg W W'' ((hT W).1 hWT) hW'').2 hG)
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W', mem_vanishingIdeal_iff]
      intro x hx
      rw [mem_zeroLocus_iff] at hx
      change ∀ p ∈ W', eval x p = 0 at hx
      change eval x G = 0
      have hxS : x ∈ segreChartSet P σ i := mem_segreChartSet_of_forall hPh σ i fun f hf =>
        hx f (hJW' ((mem_segreChartComponents.1 hJ).1.2 hf))
      obtain ⟨W, hW, hxW⟩ := exists_divSupp_of_eval hPh σ i s hxS (hx _ hsW')
      have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
      have hle : segreChartIdeal W σ i ≤ RingHom.ker (eval x) :=
        fun f hf => (mem_vanishingIdeal_iff.1 hf) x hxW
      obtain ⟨W'', hW''min, hW''x⟩ := Ideal.exists_minimalPrimes_le hle
      have hW'' : W'' ∈ segreChartComponents W σ i := mem_segreChartComponents.2 hW''min
      rw [map_prod]
      refine Finset.prod_eq_zero ((hT W).2 hW) ?_
      rw [map_prod]
      refine Finset.prod_eq_zero hW'' ?_
      exact hW''x (hg W W'' hW hW'').1
    obtain ⟨W, hW, W'', hW'', hW''le⟩ := key
    have hW''p : W''.IsPrime := (mem_segreChartComponents.1 hW'').1.1
    have heq : W'' = W' := by
      by_contra hne
      have h := SectionComponents.ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hW''le hne)
      rw [hWdim W hW W'' hW'', hdim] at h
      have h6 : n + 1 ≤ n := by exact_mod_cast h
      omega
    exact ⟨hJW', W, hW, heq ▸ hW''⟩
  · have hJp : J.IsPrime := (mem_segreChartComponents.1 hJ).1.1
    have : W'.IsPrime := (mem_segreChartComponents.1 hW'c).1.1
    have hle : J ⊔ Ideal.span {chartSection σ i s} ≤ W' :=
      sup_le hJW' ((Ideal.span_singleton_le_iff_mem _).2 (hsW W hW W' hW'c))
    obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le hle
    have hQp : Q.IsPrime := hQ.1.1
    have hdim := SectionComponents.ringKrullDim_quotient_add_one_eq (hnot J hJ) hQ
    rw [hJdim J hJ] at hdim
    rwa [← eq_of_le_of_dim hQW' n hdim (hWdim W hW W' hW'c)]
  · exact le_antisymm
      (le_of_common hNot (hWar W₂ h₂) (hWar W₁ h₁).2.1.2.1 σ i hW₂ hW₁)
      (le_of_common hNot (hWar W₁ h₁) (hWar W₂ h₂).2.1.2.1 σ i hW₁ hW₂)

end GroundTheory.Heights₂.Heights.Targets
end
end
