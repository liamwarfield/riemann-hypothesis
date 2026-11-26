module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherFurther
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRSlotAdd
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

section Semiloc

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def semiLocRing (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) : Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u w : MRing ι) (a : K → ℕ)
    (hw : Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P)),
    (∀ W ∈ 𝒲, w ∉ W) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog u a ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog w a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hw⟩}

end Semiloc

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def fibreOver (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (W : Ideal (MRing ι)) :
    Set (Ideal (MRing ι')) :=
  {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ imageZ v W' = W}


open Classical in
theorem rename_isMultiHomog {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {f : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename v f) (Function.extend κ a 0) := by
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1, Finset.mem_image] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  have hblock : ∀ (F : (Σ k', ι' k') → ℕ), ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
    intro F
    rw [Fintype.sum_sigma, Finset.sum_eq_single k']
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hblock]
  have h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) =
      ∑ p, if κ p.1 = k' then m p else 0 := by
    have := Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0)
      (s := m) hv.2.1
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [hv.2.2.1] using this
  have h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then a k else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact hf m hm k
    · simp
  convert h1.trans h2
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hv.1.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hv.1.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [if_neg fun hk => h ⟨k, hk⟩]

abbrev quotMapZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) :
    MRing ι ⧸ imageZ v P' →+* MRing ι' ⧸ P' :=
  Ideal.quotientMap P' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom le_rfl

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem quotMapZ_injective (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) :
    Function.Injective (quotMapZ v P') :=
  Ideal.quotientMap_injective


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem imageZ_isPrime_of_prime (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] :
    (imageZ v P').IsPrime :=
  Ideal.comap_isPrime _ _

def fracMapZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] :
    FractionRing (MRing ι ⧸ imageZ v P') →+* FractionRing (MRing ι' ⧸ P') :=
  haveI := imageZ_isPrime_of_prime v P'
  IsFractionRing.lift (g := (algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (quotMapZ v P'))
    ((IsFractionRing.injective (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (quotMapZ_injective v P'))

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem fracMapZ_algebraMap (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] (f : MRing ι) :
    fracMapZ v P' (algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename v f)) := by
  have := imageZ_isPrime_of_prime v P'
  unfold fracMapZ
  rw [IsFractionRing.lift_algebraMap]
  rfl

theorem fracMapZ_mem {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : FractionRing (MRing ι ⧸ imageZ v P'))
    (hx : x ∈ locRing (imageZ v P') W) : fracMapZ v P' x ∈ semiLocRing P' (fibreOver v P' W) := by
  have := imageZ_isPrime_of_prime v P'
  have hle : locRing (imageZ v P') W ≤ (semiLocRing P' (fibreOver v P' W)).comap (fracMapZ v P') := by
    rw [locRing, Subring.closure_le]
    rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
    rw [SetLike.mem_coe, Subring.mem_comap]
    have hw0 : rename v w ∉ P' := by
      intro h
      apply nonZeroDivisors.ne_zero hw
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact h
    have hw' : Ideal.Quotient.mk P' (rename v w) ∈ nonZeroDivisors (MRing ι' ⧸ P') :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    apply Subring.subset_closure
    refine ⟨rename v u, rename v w, Function.extend κ a 0, hw', ?_, rename_isMultiHomog hv hu,
      rename_isMultiHomog hv hwa, ?_⟩
    · rintro W' ⟨-, -, hW'⟩ hmem
      apply hwW
      rw [← hW']
      exact hmem
    · rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, map_div₀]
      exact congrArg₂ (· / ·) (fracMapZ_algebraMap v P' u) (fracMapZ_algebraMap v P' w)
  exact hle hx

def locToSemiloc {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) :
    locRing (imageZ v P') W →+* semiLocRing P' (fibreOver v P' W) :=
  (fracMapZ v P').restrict _ _ (fun x hx => fracMapZ_mem hv P' W x hx)

theorem locToSemiloc_coe {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : locRing (imageZ v P') W) :
    ((locToSemiloc hv P' W x : semiLocRing P' (fibreOver v P' W)) : FractionRing (MRing ι' ⧸ P')) =
      fracMapZ v P' x :=
  rfl

end Block

namespace SemilocRing

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def blkW : (Σ k, ι k) → K → ℕ := fun p => Pi.single p.1 1


open Classical in
theorem isMultiHomog_of_wh {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a := by
  intro m hm k
  rw [← h (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, Ne.symm hb]
  · simp

theorem isMultiHomog_coordPow (i : ∀ k, ι k) (α : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by
  have h : IsWeightedHomogeneous (blkW (ι := ι)) (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)
      (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) :=
    IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℤ _ _).pow (α k)
  have e : (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) = α := by
    funext k
    simp only [blkW, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [e] at h
  exact isMultiHomog_of_wh h

end SemilocRing

theorem exists_form_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {W : Ideal (MRing ι)}
    (hW : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W) (hWp : W.IsPrime) (α : K → ℕ) : ∃ t : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t α ∧ t ∉ W := by
  choose i hi using hW
  refine ⟨∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k, SemilocRing.isMultiHomog_coordPow i α, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := hWp.prod_mem_iff.mp h
  exact hi k (hWp.mem_of_pow_mem _ hk)

section Example

end Example

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherExtra
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

open ReciprocityTheory.ChartRestriction.G in
def pullbackDensity_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (L : Fin n → Geo.HermLine ι) (L' : Fin n → Geo.HermLine ι')
    (A : Geo.HermLine ι) (A' : Geo.HermLine ι') (s : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsGoodProj (imageZ v P') Ψ →
    (∀ j, Geo.IsSmoothHerm (L j)) → (∀ j, AI.I4.IsPullHerm κ v (L j) (L' j)) →
    Geo.IsSmoothHerm A → AI.I4.IsPullHerm κ v A A' → Geo.IsSectionOn (imageZ v P') A s →
    ∀ᵐ y : Fin n → ℂ, ∀ x ∈ pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ,
      Geo.logNorm A' (rename v s) (R.lift x x) * pushDens R.A (fun j => Geo.potOf R (L' j)) (pullQ R v Ψ) x =
        sheetDensity (imageZ v P') Ψ (Geo.pot L) (Geo.logNorm A s) y (pullW R v Ψ x)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

namespace IntersectionWithSection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem comp_mem_mcPts {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} {z' : (Σ k', ι' k') → ℂ} (hz : z' ∈ mcPts P') :
    (fun p => z' (v p)) ∈ mcPts (imageZ v P') := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz.1 (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
    obtain ⟨pk, pi⟩ := p
    simp only at h2
    subst h2
    exact ⟨pi, show z' (v ⟨pk, pi⟩) ≠ 0 by rw [hp]; exact hi'⟩
  · have h := hz.2 _ (Ideal.mem_comap.mp hf)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h
    exact h

theorem pullW_mem_fibre {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' J' : Ideal (MRing ι')} {n : ℕ} (hP : IsArithVar (imageZ v P') (n + 1)) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x : R.X}
    (h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0) : pullW R v Ψ x ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Ψ (pullQ R v Ψ x) := by
  classical
  obtain ⟨k0⟩ := hP.1
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (pullPt R v x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (pullPt R v x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * pullPt R v x p,
    mcPts_smul hP.2.1.2.1 c hc (comp_mem_mcPts hv (R.mem x x (R.mem_U x))), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [pullW, h0]
    · simp only [pullW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, pullQ]
      rw [div_eq_inv_mul]

end IntersectionWithSection


open IntersectionWithSection in
theorem IntersectionWithSection.proof (hE : ResExistsStatement) (hPush : pullbackPushforward_holds.Statement)
    (hCount : PullbackDegreeCount.Statement) (hDens : pullbackDensity_holds.Statement) : IntersectionWithSection.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J L L' A A' s hv hP' hP hJ hL hLL' hA hAA' hs
  classical
  have hA' := ArithmeticIntersectionIntegral.isSmoothHerm_pull hv hA hAA'
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => ArithmeticIntersectionIntegral.isSmoothHerm_pull hv (hL j) (hLL' j)
  have hs' : IsSectionOn P' A' (rename v s) := by
    obtain ⟨a, hAa, hsa, hsP⟩ := hs
    refine ⟨Function.extend κ a 0, fun k' => ?_, ArithmeticIntersectionIntegral.isMultiHomog_rename hv hsa,
      fun h => hsP (Ideal.mem_comap.mpr h)⟩
    rw [hAA'.1, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hAa k]
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  obtain ⟨J', ⟨R⟩⟩ := exists_anLogRes hE hP'
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι (imageZ v P') n hP
  obtain ⟨hnull, hfin⟩ := hPush K ι K' ι' κ v P' J' n R Ψ hv hP' hP hΨ
  rw [ptsIntegral_eq_mInt' hE resBridge R hP' hL' hA' hs', ptsIntegral_eq_at hE resBridge hP hΨ hL hA hs,
    pushForward_null R.A _ (fun j => potOf_isPotential R (L' j) (hL' j)) (pullQ R v Ψ) (pullBad R v Ψ) hnull
      (fun x hx j hj => by
        by_contra h
        exact hx (Or.inr ⟨j, hj, h⟩)) hfin _ (brIntegrable R L' A' (rename v s) hP' hL' hA' hs'),
    ptsIntegralAt, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hCount K ι K' ι' κ v P' J' n G J R Ψ hv hP' hP hJ hΨ,
    hDens K ι K' ι' κ v P' J' n R Ψ L L' A A' s hv hP' hP hΨ hL hLL' hA hAA' hs] with y hc hd
  have hSf := hfin y
  have hFf := fibreFinite K ι (imageZ v P') n Ψ hP hΨ y
  have hmaps : ∀ x ∈ hSf.toFinset, pullW R v Ψ x ∈ hFf.toFinset := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    have h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0 := fun h => hx.2 (Or.inl (Or.inr h))
    have hw := pullW_mem_fibre hv hP R Ψ h0
    rwa [show pullQ R v Ψ x = y from hx.1] at hw
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf, finsum_mem_eq_finite_toFinset_sum _ hFf, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun x hx => hd x ((Set.Finite.mem_toFinset hSf).mp hx)).trans ?_
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hset : ({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ) =
      ↑(hSf.toFinset.filter fun x => pullW R v Ψ x = w) := by
    ext x
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    tauto
  have hcw := hc w ((Set.Finite.mem_toFinset hFf).mp hw)
  rw [hset, Set.ncard_coe_finset] at hcw
  exact_mod_cast hcw

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ComplexOrder

namespace PointsAbsIntegrable

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cxHessian_tensor {D : ℕ} {X Y : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    cxHessian (fun y' => Real.log ((X.tensor Y).h (γ y'))) y =
      cxHessian (fun y' => Real.log (X.h (γ y'))) y + cxHessian (fun y' => Real.log (Y.h (γ y'))) y := by
  have hev := hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (X.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hX (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hc : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (Y.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hY (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((X.tensor Y).h (γ y'))) =ᶠ[𝓝 y]
      fun y' => 1 * Real.log (X.h (γ y')) + 1 * Real.log (Y.h (γ y')) := by
    filter_upwards [hγ] with y' hy'
    rw [one_mul, one_mul]
    exact Real.log_mul (X.pos _ hy'.2).ne' (Y.pos _ hy'.2).ne'
  have hH := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_cxHessian_comb 1 1 ha hc hψ
  simpa only [Complex.ofReal_one, one_smul] using hH

theorem abs_maDensity_le {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L T : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (hT : ∀ j, IsSmoothHerm (T j))
    (hTp : ∀ j, IsSemiPosHerm (T j)) (hLTp : ∀ j, IsSemiPosHerm ((L j).tensor (T j)))
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hS : IsSheet P Ψ y w γ) :
    |maDensity (fun j y' => pot L j (γ y')) y| ≤
      3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y := by
  have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0 := by
    filter_upwards [hS.2] with y' hy'
    exact ⟨hy'.1, hy'.2.1.1⟩
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j => isSmoothHerm_tensor (hL j) (hT j)
  set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => cxHessian (fun y' => pot L j (γ y')) y with hAdef
  set B : Fin e → Matrix (Fin e) (Fin e) ℂ :=
    fun j => cxHessian (fun y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y with hBdef
  have hHT : ∀ j, (cxHessian (fun y' => Real.log ((T j).h (γ y'))) y).PosSemidef := fun j =>
    SheetHessPSD.proof K ι P e Ψ (T j) y w γ (hT j) (hTp j) hS
  have hHLT : ∀ j, (cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y).PosSemidef := fun j =>
    SheetHessPSD.proof K ι P e Ψ _ y w γ (hLT j) (hLTp j) hS
  have hB : ∀ j, B j = cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y +
      cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := fun j =>
    cxHessian_tensor (hLT j) (hT j) hγ
  have hA : ∀ j, cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y =
      A j + cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := fun j =>
    cxHessian_tensor (hL j) (hT j) hγ
  have hle : ∀ j, (B j - A j).PosSemidef := fun j => by
    have e1 : B j - A j = cxHessian (fun y' => Real.log ((T j).h (γ y'))) y +
        cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := by
      rw [hB j, hA j]; abel
    rw [e1]
    exact (hHT j).add (hHT j)
  have hge : ∀ j, (A j + B j).PosSemidef := fun j => by
    have e1 : A j + B j = cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y +
        cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y := by
      rw [hB j, hA j]; abel
    rw [e1]
    exact (hHLT j).add (hHLT j)
  have hn : ‖mixedDisc A‖ ≤ 3 ^ e * (mixedDisc B).re :=
    ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le A B hle hge
  have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDensity
  rw [abs_mul, abs_of_nonneg hc]
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * |(mixedDisc A).re|
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (3 ^ e * (mixedDisc B).re) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hn) hc
    _ = 3 ^ e * ((e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc B).re) := by ring

end PointsAbsIntegrable


open PointsAbsIntegrable in
theorem PtsAbsIntegrable.proof (hInt : PtsIntegrableStatement) (hMeas : PtsAbsMeasurable.Statement) :
    PtsAbsIntegrable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hTw := SemiPosTwist.proof TorusInvLevi.proof
  choose T hTs hTp hLTp using fun j => hTw K ι (L j) (hL j)
  have hN : ∀ j, IsSmoothHerm (((L j).tensor (T j)).tensor (T j)) := fun j =>
    isSmoothHerm_tensor (isSmoothHerm_tensor (hL j) (hTs j)) (hTs j)
  obtain ⟨a, ha, hsa, hsP⟩ := hs
  have hs : IsSectionOn P A s := ⟨a, ha, hsa, hsP⟩
  set D := regLine A s ⟨a, ha, hsa⟩ 1 with hDdef
  have hD : IsSmoothHerm D := isSmoothHerm_regLine hA one_pos
  have hD1 : IsSectionOn P D 1 := by
    refine ⟨0, fun k => by simp [hDdef, regLine_a], fun m hm k => ?_,
      fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have h1 := hInt K ι P e Ψ _ A s hP hΨ hN hA hs
  have h2 := hInt K ι P e Ψ _ D 1 hP hΨ hN hD hD1

  have key : ∀ y w, |sheetDensity P Ψ (pot L) (logNorm A s) y w| ≤
      3 ^ e * (-2 * sheetDensity P Ψ (pot fun j => ((L j).tensor (T j)).tensor (T j)) (logNorm D 1) y w -
        sheetDensity P Ψ (pot fun j => ((L j).tensor (T j)).tensor (T j)) (logNorm A s) y w) := by
    intro y w
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · simp only [dif_pos hγ]
      set γ := hγ.choose
      have hS : IsSheet P Ψ y w γ := hγ.choose_spec
      have hmem : γ y ∈ mcPts P := hS.2.self_of_nhds.2.1
      have hm := abs_maDensity_le hL hTs hTp hLTp hS
      set r := Real.log (D.h (γ y)) with hr
      have hr0 : 0 ≤ r := by
        rw [hr, hDdef, log_regLine_h]
        exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg (secNorm A s (γ y))])) (by norm_num)
      have hgr : logNorm A s (γ y) ≤ r := by
        by_cases h0 : eval (γ y) (map (Int.castRingHom ℂ) s) = 0
        · have : logNorm A s (γ y) = 0 := by simp [logNorm, h0]
          rw [this]
          exact hr0
        · exact logNorm_le_log_regLine_h zero_le_one hmem.1 h0
      have hD1r : logNorm D 1 (γ y) = -r := by
        simp [logNorm, hr, Real.log_inv]
      rw [hD1r]
      have hg : |logNorm A s (γ y)| ≤ 2 * r - logNorm A s (γ y) := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul]
      calc |logNorm A s (γ y)| * |maDensity (fun j y' => pot L j (γ y')) y|
          ≤ (2 * r - logNorm A s (γ y)) *
              (3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y) :=
            mul_le_mul hg hm (abs_nonneg _) (by linarith [abs_nonneg (logNorm A s (γ y))])
        _ = _ := by ring
    · simp only [dif_neg hγ]
      simp
  refine Integrable.mono' (((h2.const_mul (-2)).sub h1).const_mul (3 ^ e))
    (hMeas K ι P e Ψ L A s hP hΨ hL hA hs) (Eventually.of_forall fun y => ?_)
  have hfin := fibreFinite K ι P e Ψ hP hΨ y
  simp only [Pi.sub_apply]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _), Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => key y w

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImageVarIdBotTwo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def VerticalDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ)
    (i' : ∀ k', ι' k'),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    IsChart (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' →
    ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
      (fnDeg v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' : ℤ) = J' (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 Fin.elim0

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem isSmoothHerm_of_isPullHerm' {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem arithDim_lt_of_lt {P Q : Ideal (MRing ι)} {d d₀ : ℕ} (hP : IsArithVar P d) (hQ : IsArithVar Q d₀)
    (hle : P ≤ Q) (hne : P ≠ Q) : d₀ < d := by
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have := hP.2.1.1
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf0)
  have h2 : ringKrullDim (MRing ι ⧸ Q) ≤
      ringKrullDim ((MRing ι ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P f}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_) ?_
    · intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hfQ, mul_zero]
    · intro z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk P z), rfl⟩
  rw [hP.2.2.2] at h1
  rw [hQ.2.2.2] at h2
  have h3 : ((d₀ + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    le_trans (by gcongr) h1
  have h4 : ((d₀ + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h3
  have h5 : d₀ + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h4
  omega

end SlopeTestRemainingChoices

theorem PFStep.proof (hSec : PFSecRed.Statement) (hVert : PFVert.Statement) (hInt : PFIntZero.Statement)
    (hHor : PFHoriz.Statement) (hSum : PFFibreSum.Statement) (hIm : ImageArithStatement) (hCM : ContractMixedStatement) : PFStep.Statement := by
  intro I hI r hr
  refine hSec I hI r ?_
  intro K _ ι _ K' _ ι' _ κ v P' d G J L L' N s a hv hP' hP hJ hL hL' hN ha hs hsP
  have hP1 : IsArithVar P' (d + r + 1) := hP'
  have hsec : IsSectionOn P' (N (Fin.last r)) s := ⟨a, ha, hs, hsP⟩
  have hM : ∀ j, IsSmoothHerm (Fin.append L' (Fin.init N) j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact isSmoothHerm_of_isPullHerm' hv (hL i) (hL' i)
    | right i => rw [Fin.append_right]; exact hN _
  have hR := (hI K' ι').2.2 P' (d + r) (Fin.append L' (Fin.init N)) (N (Fin.last r)) s a hP1 hM (hN _) ha hs hsP
  rw [← Fin.append_snoc, Fin.snoc_init_self] at hR
  refine hR.trans ?_
  rw [recR_eq, hInt K ι K' ι' κ v P' d r L L' (Fin.init N) (N (Fin.last r)) s hv hP1 hP hL hL', sub_zero, cycR,
    ← hSum K ι K' ι' κ v P' d r G J N s a hv hP1 hP hJ ha hs hsP, finsum_mem_mul]
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · have hWa : IsArithVar W (d + r) := (divSuppArith K' ι' P' (d + r) (N (Fin.last r)) s W hP1 hsec hW).1 hh
    by_cases hd : imageZ v W = imageZ v P'
    · rw [if_pos hh, if_pos ⟨hh, hd⟩,
        hHor I r hr K ι K' ι' κ v P' W d G J L L' (Fin.init N) hv hWa hd hP hJ hL hL' (fun j => hN _)]
      exact (mul_assoc _ _ _).symm
    · rw [if_pos hh, if_neg (fun h => hd h.2), mul_zero, zero_mul]
      obtain ⟨d₀, -, hd₀⟩ := hIm K ι K' ι' κ v W (d + r) hP.1 hv hWa
      have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono (le_sup_left.trans hW.1.1.2)
      rw [hCM I hI K ι K' ι' κ v W d₀ d r L L' (Fin.init N) hv hWa hd₀
        (arithDim_lt_of_lt hP hd₀ hle (Ne.symm hd)) hL hL' (fun j => hN _), mul_zero]
  · rw [if_neg hh, if_neg (fun h => hh h.1),
      hVert K ι K' ι' κ v P' d r L L' (Fin.init N) s a W hv hP1 hP hL' hs hsP hW hh]
    simp

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZIff
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithmeticIntersectionCycle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem comap_C_imageZ (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    (imageZ v W').comap (C : ℤ →+* MRing ι) = W'.comap (C : ℤ →+* MRing ι') := by
  ext c
  simp [imageZ, Ideal.mem_comap]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem isHorizontal_imageZ_iff (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    IsHorizontal (imageZ v W') ↔ IsHorizontal W' := by
  rw [IsHorizontal, IsHorizontal, comap_C_imageZ]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem charOf_imageZ (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    charOf (imageZ v W') = charOf W' := by
  simp only [charOf, comap_C_imageZ]

end ArithmeticIntersectionCycle

theorem ArithmeticIntersectionCycle.proof (hHor : ArithmeticIntersectionHorizontal.Statement) (hVert : ArithmeticIntersectionVertical.Statement) (hPush : ArithmeticIntersectionDivisorPushforward.Statement)
    (hGP : GenericPointExists.Statement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    ArithmeticIntersectionCycle.Statement := by
  intro I hI n hn K _ ι _ K' _ ι' _ κ v P' G J L L' s α hv hP' hP hJ hL hLL' hs hsP
  classical

  have hex : ∀ W' : Ideal (MRing ι'), W'.IsPrime →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' := by
    intro W' hW'
    obtain ⟨G'⟩ := hGP K ι K' ι' v W' hW'
    obtain ⟨J', hJ', -⟩ := hEU G'.Φ (FibreBlock κ) (fibreIdx ι' κ)
    exact ⟨G', J', hJ'⟩
  let E : Ideal (MRing ι') → ℤ := fun W' =>
    if h : ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' then
      h.choose_spec.choose (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ h.choose) 0 Fin.elim0 else 0
  have hE : ∀ W' : Ideal (MRing ι'), W'.IsPrime →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 Fin.elim0 := by
    intro W' hW'
    have h := hex W' hW'
    exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec, by simp only [E, dif_pos h]⟩

  let T : Ideal (MRing ι) → ℝ := fun W =>
    if IsHorizontal W then I K ι W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)
  let T' : Ideal (MRing ι') → ℝ := fun W' =>
    if IsHorizontal W' then I K' ι' W' n L' else (geoNum n W' (fun j => (L' j).a) : ℝ) * Real.log (charOf W')
  have hterm : ∀ W' ∈ divSupp P' (rename v s), T' W' = if imageZ v W' ∈ divSupp (imageZ v P') s then (E W' : ℝ) * T (imageZ v W') else 0 := by
    intro W' hW'
    obtain ⟨G', J', hJ', hEW⟩ := hE W' hW'.1.isPrime
    by_cases hh : IsHorizontal W'
    · have hh' : IsHorizontal (imageZ v W') := (ArithmeticIntersectionCycle.isHorizontal_imageZ_iff v W').2 hh
      rcases hHor I hI n hn K ι K' ι' κ v P' L L' s α W' hv hP' hP hL hLL' hs hsP hW' hh with
        ⟨hm, he⟩ | ⟨hm, h0⟩
      · simp only [T', T, if_pos hh, if_pos hm, if_pos hh', he G' J' hJ', hEW]
      · simp only [T', if_pos hh, if_neg hm, h0]
    · have hh' : ¬ IsHorizontal (imageZ v W') := fun h => hh ((ArithmeticIntersectionCycle.isHorizontal_imageZ_iff v W').1 h)
      have ha : (fun j => (L' j).a) = fun j => pullDeg κ (L j).a := funext fun j => (hLL' j).1
      rcases hVert K ι K' ι' κ v P' n (fun j => (L j).a) s α W' hv hP' hP hs hsP hW' hh with
        ⟨hm, he⟩ | ⟨hm, h0⟩
      · simp only [T', T, if_neg hh, if_pos hm, if_neg hh', ArithmeticIntersectionCycle.charOf_imageZ]
        rw [ha, he G' J' hJ', hEW]
        push_cast
        ring
      · simp only [T', if_neg hh, if_neg hm]
        rw [ha, h0]
        simp

  have hfin' : (divSupp P' (rename v s)).Finite := divSupp_finite _ _
  have hfin : (divSupp (imageZ v P') s).Finite := divSupp_finite _ _
  have key : ∀ W ∈ hfin.toFinset,
      ∑ W' ∈ hfin'.toFinset.filter (fun W' => imageZ v W' = W),
        (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' =
        J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 Fin.elim0 * multAt (imageZ v P' ⊔ Ideal.span {s}) W := by
    intro W hW
    have h := hPush K ι K' ι' κ v P' n G J s α W E hv hP' hP hJ hs hsP (hfin.mem_toFinset.1 hW)
      (fun W' hW' _ => hE W' hW'.1.isPrime)
    have hfiber : {W' | W' ∈ divSupp P' (rename v s) ∧ imageZ v W' = W}.Finite :=
      hfin'.subset (fun _ hx => hx.1)
    rw [finsum_mem_eq_finite_toFinset_sum _ hfiber] at h
    rw [← h]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext W'
    simp [Set.Finite.mem_toFinset]

  show (∑ᶠ W' ∈ divSupp P' (rename v s), (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * T' W') =
    (J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 Fin.elim0 : ℝ) * ∑ᶠ W ∈ divSupp (imageZ v P') s, (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℝ) * T W
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc ∑ W' ∈ hfin'.toFinset, (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * T' W'
      = ∑ W' ∈ hfin'.toFinset, if imageZ v W' ∈ hfin.toFinset then
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') else 0 := by
        refine Finset.sum_congr rfl fun W' hW' => ?_
        rw [hterm W' (hfin'.mem_toFinset.1 hW')]
        simp only [Set.Finite.mem_toFinset]
        split_ifs <;> ring
    _ = ∑ W' ∈ hfin'.toFinset with imageZ v W' ∈ hfin.toFinset,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') := by
        rw [Finset.sum_filter]
    _ = ∑ W ∈ hfin.toFinset, ∑ W' ∈ hfin'.toFinset with imageZ v W' = W,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') := by
        rw [Finset.sum_fiberwise_eq_sum_filter]
    _ = ∑ W ∈ hfin.toFinset, ((∑ W' ∈ hfin'.toFinset with imageZ v W' = W,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' : ℤ) : ℝ) * T W := by
        refine Finset.sum_congr rfl fun W _ => ?_
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun W' hW' => ?_
        rw [(Finset.mem_filter.1 hW').2]
    _ = (J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 Fin.elim0 : ℝ) *
          ∑ W ∈ hfin.toFinset, (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℝ) * T W := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun W hW => ?_
        rw [key W hW]
        push_cast
        ring

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PWWArithVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

theorem mCoordIdeal_eq_ker_multiConeMap {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ) : mCoordIdeal c = RingHom.ker (T.multiConeMap c) := by
  have h : (mConeMap c : MRing ι →+* MvPolynomial K Φ) = T.multiConeMap c :=
    MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap, mConeMap])
      (fun p => by simp [T.multiConeMap, mConeMap])
  rw [mCoordIdeal, ← h]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreBij
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFFibreBij.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d e : ℕ)
    (G : GenFibre v P') (s : MRing ι'),
    IsBlockMap κ v → IsArithVar P' e → IsArithVar (imageZ v P') d →
    Set.BijOn (fibreOf κ G) {W | W ∈ divSupp P' s ∧ IsHorizontal W ∧ imageZ v W = imageZ v P'}
      (divSupp (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (baseSubst κ G s))

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherMore
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

def pullbackBadImage_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsGoodProj (imageZ v P') Ψ →
    volume (pullQ R v Ψ '' (pullBad R v Ψ ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0})) = 0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end
