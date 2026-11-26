module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

section Pull

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem blocks_ne_zero_restrict {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {z : (Σ k', ι' k') → ℂ} (hz : ∀ k', ∃ i', z ⟨k', i'⟩ ≠ 0) (k : K) : ∃ i, z (v ⟨k, i⟩) ≠ 0 := by
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem IsPullHerm.isSmoothHerm {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (h : IsPullHerm κ v A A') (hA : IsSmoothHerm A) :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun (z : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z (v p) := funext h.2
  have hR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun (z : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z (v p)) :=
    contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)
  unfold IsSmoothHerm
  rw [e]
  exact hA.comp hR.contDiffOn fun z hz => blocks_ne_zero_restrict hv hz

omit [Fintype K] [Fintype K'] in
theorem pullDeg_add (κ : K → K') (a b : K → ℤ) : pullDeg κ (a + b) = pullDeg κ a + pullDeg κ b := by
  classical
  funext k'
  simp only [pullDeg, Function.extend, Pi.add_apply]
  split_ifs <;> simp


omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem IsPullHerm.tensor {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {A' B' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (hA : IsPullHerm κ v A A') (hB : IsPullHerm κ v B B') :
    IsPullHerm κ v (A.tensor B) (A'.tensor B') := by
  refine ⟨?_, fun z => ?_⟩
  · show A'.a + B'.a = pullDeg κ (A.a + B.a)
    rw [hA.1, hB.1, pullDeg_add]
  · show A'.h z * B'.h z = A.h _ * B.h _
    rw [hA.2, hB.2]

end Pull

section Algebra

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem isMultiHomog_prod_X_pow [DecidableEq K] {J : Type*} [Fintype J] (q : J → Σ k, ι k) (e : J → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ j, X (q j) ^ e j : MRing ι)
      (fun k => ∑ j ∈ Finset.univ.filter (fun j => (q j).1 = k), e j) := by
  classical
  have hm : (∏ j, X (q j) ^ e j : MRing ι) = monomial (∑ j, Finsupp.single (q j) (e j)) 1 := by
    rw [monomial_sum_one]
    simp [X_pow_eq_monomial]
  intro m hm' k
  rw [hm] at hm'
  have := Finset.mem_singleton.1 (support_monomial_subset hm')
  subst this
  beta_reduce
  rw [Finset.sum_filter]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨k0, i0⟩ := q j
  by_cases h : k0 = k
  · subst h
    simp [Finsupp.single_apply]
  · simp [h]

theorem krullDim_quot_add_one_le {R : Type*} [CommRing R] {Q Q₂ : Ideal R} [Q.IsPrime] (hle : Q ≤ Q₂)
    {x : R} (hx : x ∈ Q₂) (hxQ : x ∉ Q) : ringKrullDim (R ⧸ Q₂) + 1 ≤ ringKrullDim (R ⧸ Q) := by
  have hr : Ideal.Quotient.mk Q x ∈ nonZeroDivisors (R ⧸ Q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_)
    (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hle))
  intro y hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul]
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, mul_zero]

end Algebra

section Proof

theorem contract_intersection_number (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement)
    (I : AllFam) (hI : I.IsFamily) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n : ℕ) (P' : Ideal (MRing ι')) (d : ℕ) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'),
      IsArithVar P' n → IsArithVar (imageZ v P') d → d < n → (∀ j, IsSmoothHerm (L j)) →
      (∀ j, IsPullHerm κ v (L j) (L' j)) → I K' ι' P' n L' = 0 := by
  intro n
  induction n with
  | zero => intro _ d _ _ _ _ h; omega
  | succ n ih =>
    intro P' d L L' hP' hQ hdn hL hLL
    classical
    have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => IsPullHerm.isSmoothHerm hv (hLL j) (hL j)
    have hL0 : ∀ j, IsSmoothHerm (Fin.init L j) := fun j => hL _
    have hL0' : ∀ j, IsSmoothHerm (Fin.init L' j) := fun j => hL' _
    have hLL0 : ∀ j, IsPullHerm κ v (Fin.init L j) (Fin.init L' j) := fun j => hLL _
    have hQp : (imageZ v P').IsPrime := hQ.2.1.1

    have key : ∀ (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (B' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'), IsSmoothHerm B' → IsPullHerm κ v B B' →
        (∀ k, 0 ≤ B.a k) → I K' ι' P' (n + 1) (Fin.snoc (Fin.init L') B') = 0 := by
      intro B B' hB' hBB hBa
      choose i hi using hQ.2.1.2.2
      let b : K → ℕ := fun k => (B.a k).toNat
      let t : MRing ι := ∏ k, X ⟨k, i k⟩ ^ b k
      have ht : t ∉ imageZ v P' := by
        intro h
        obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hQp)).1 h
        exact hi k (hQp.mem_of_pow_mem _ hk)
      have htm : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t b := by
        convert isMultiHomog_prod_X_pow (fun k => (⟨k, i k⟩ : Σ k, ι k)) b using 1
        funext k
        simp [Finset.sum_filter]
      let s : MRing ι' := rename v t
      have hs : s ∉ P' := ht
      let b' : K' → ℕ := fun k' => ∑ k ∈ Finset.univ.filter (fun k => κ k = k'), b k
      have hsm : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s b' := by
        have e : s = ∏ k, X (v ⟨k, i k⟩) ^ b k := by simp [s, t, map_prod]
        rw [e]
        convert isMultiHomog_prod_X_pow (fun k => v ⟨k, i k⟩) b using 1
        funext k'
        simp only [hv.2.2.1, b']
      have hBa' : ∀ k', B'.a k' = b' k' := by
        intro k'
        rw [hBB.1]
        by_cases hk : ∃ k, κ k = k'
        · obtain ⟨k0, rfl⟩ := hk
          have hf : Finset.univ.filter (fun k => κ k = κ k0) = {k0} := by
            ext k
            simp [hv.1.eq_iff]
          simp only [b', hf, Finset.sum_singleton, pullDeg, hv.1.extend_apply, b]
          exact (Int.toNat_of_nonneg (hBa k0)).symm
        · have hf : Finset.univ.filter (fun k => κ k = k') = ∅ := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            exact fun h => hk ⟨k, h⟩
          simp only [b', hf, Finset.sum_empty, pullDeg, Function.extend_apply' _ _ _ hk]
          rfl
      have hsec : IsSectionOn P' B' s := ⟨b', hBa', hsm, hs⟩
      rw [(hI K' ι').2.2 P' n (Fin.init L') B' s b' hP' hL0' hB' hBa' hsm hs, recR_eq]
      have h1 : arInt P' s B' (Fin.init L') = 0 :=
        hF K ι K' ι' κ v P' d n (Fin.init L) (Fin.init L') (logNorm B' s) hv hP' hQ hdn hL0 hLL0
      have h2 : cycR (I K' ι') P' (Fin.init L') s = vertR P' (Fin.init L') s := by
        unfold cycR vertR
        refine finsum_mem_congr rfl fun W hW => ?_
        split_ifs with hH
        · have hWn : IsArithVar W n := (divSuppArith K' ι' P' n B' s W hP' hsec hW).1 hH
          obtain ⟨dW, -, hQW⟩ := hIm K ι K' ι' κ v W n hQ.1 hv hWn
          have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
          have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
          have hdim := krullDim_quot_add_one_le (Q := imageZ v P') (Q₂ := imageZ v W) (Ideal.comap_mono hPW)
            (show t ∈ imageZ v W from hsW) ht
          rw [hQW.2.2.2, hQ.2.2.2] at hdim
          have hlt : dW + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast hdim
          rw [ih W dW (Fin.init L) (Fin.init L') hWn hQW (by omega) hL0 hLL0]
        · rfl
      rw [h1, h2, hV K ι K' ι' κ v P' d n (Fin.init L) (Fin.init L') t b hv hP' hQ hdn hLL0 htm ht,
        sub_zero]

    let A := L (Fin.last n)
    let A' := L' (Fin.last n)
    let M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric fun k => (-(A.a k)).toNat
    let M' := IndefiniteRowSideFullHecke.Inter.pullHerm hv M
    have hM : IsSmoothHerm M := isSmoothHerm_sqMetric _
    have hMM : IsPullHerm κ v M M' := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv M
    have hM' : IsSmoothHerm M' := IsPullHerm.isSmoothHerm hv hMM hM
    have hA' : IsSmoothHerm A' := hL' _
    have hadd := (hI K' ι').2.1 P' n (Fin.init L') A' M' hP' hL0' hA' hM'
    have h3 := key (A.tensor M) (A'.tensor M') (isSmoothHerm_tensor hA' hM')
      (IsPullHerm.tensor (hLL _) hMM) fun k => by
        show 0 ≤ A.a k + ((-(A.a k)).toNat : ℤ)
        omega
    have h4 := key M M' hM' hMM fun k => by
      show (0 : ℤ) ≤ ((-(A.a k)).toNat : ℤ)
      omega
    have e : L' = Fin.snoc (Fin.init L') A' := (Fin.snoc_init_self L').symm
    rw [e]
    linarith

theorem PushforwardProjectivePoint.proof (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement) :
    PushforwardProjectivePoint.Statement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d d' L L' hv hP' hQ hdd hL hLL
  exact contract_intersection_number hIm hF hV I hI hv d' P' d L L' hP' hQ hdd hL hLL

theorem contract_of (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement) :
    ContractStatement :=
  PushforwardProjectivePoint.proof hIm hF hV

end Proof

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_congr_pts (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      exact hg _ hγ.choose_spec.2.self_of_nhds.2.1
    · rfl
  · rfl

theorem cycR_sub_vertR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) [DecidablePred (IsHorizontal (ι := ι))] :
    cycR I P L s - vertR P L s = ∑ W ∈ (divSupp_finite P s).toFinset.filter IsHorizontal,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L := by
  unfold cycR vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  split_ifs <;> ring

theorem tensor_sqMetric_a {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {α β : K → ℕ} (h : ∀ k, (α k : ℤ) - β k = A.a k) (k : K) :
    (A.tensor (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β)).a k = α k := by
  show A.a k + (β k : ℤ) = α k
  rw [← h k]
  ring

theorem Conservation.proof : Conservation.Statement := Conservation.statement_holds

theorem InductiveIntersectionFormula.proof : InductiveIntersectionFormula.Statement := by
  classical
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ hhor hmult hnorm
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hRf := hR P n L _ f α hP hL (isSmoothHerm_tensor hA hB) (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β)) L = arInt P g (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β) L := by
    unfold arInt
    refine ptsIntegral_congr_pts P _ fun z hz ↦ ?_
    have hApos := A.pos z hz.1
    show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β).h z)) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β).h z)
    rw [hnorm z hz, mul_comm (A.h z), mul_div_mul_right _ _ hApos.ne']
  have hS : (divSupp_finite P f).toFinset.filter IsHorizontal =
      (divSupp_finite P g).toFinset.filter IsHorizontal := by
    ext W
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h ↦ ⟨(hhor W h.2).1 h.1, h.2⟩, fun h ↦ ⟨(hhor W h.2).2 h.1, h.2⟩⟩
  have hcyc : cycR I P L f - vertR P L f = cycR I P L g - vertR P L g := by
    rw [cycR_sub_vertR, cycR_sub_vertR, hS]
    refine Finset.sum_congr rfl fun W hW ↦ ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hW
    rw [hmult W hW.2 ((hhor W hW.2).2 hW.1)]
  rw [recR_eq] at hRf hRg
  linarith

theorem ae_eval_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {h : MRing ι} (hh : ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h a)
    (hhP : h ∉ P) :
    ∀ᵐ y : Fin e → ℂ, ∀ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y →
      eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  have hJ : IsMultiHomogIdeal (Ideal.span {h} : Ideal (MRing ι)) :=
    ⟨{h}, fun f hf ↦ by rw [Set.mem_singleton_iff.mp hf]; exact hh, rfl⟩
  have hJP : ¬ (Ideal.span {h} : Ideal (MRing ι)) ≤ P := by
    rwa [Ideal.span_singleton_le_iff_mem]
  have hnull := projB_null Ψ hP hΨ hJ hJP
  refine ae_iff.mpr (measure_mono_null (fun y hy ↦ ?_) hnull)
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hy
  obtain ⟨z, hz, hzy, hz0⟩ := hy
  refine ⟨z, hz, ⟨hz.1, fun q hq ↦ ?_⟩, hzy⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hq
  simp [hz0]

theorem RatR.proof (hInt : PtsIntegrableStatement) : RatR.Statement := by
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hAB := isSmoothHerm_tensor hA hB
  have hRf := hR P n L _ f α hP hL hAB (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β)) L - arInt P g (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β) L =
      ptsIntegral P (pot L) (logNormRat A f g) := by
    show ptsIntegral P (pot L) _ - ptsIntegral P (pot L) _ = _
    unfold ptsIntegral
    split_ifs with hΨ
    · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
      unfold ptsIntegralAt
      rw [← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB ⟨α, tensor_sqMetric_a hαβ, hf, hfP⟩)
        (hInt K ι P n _ L _ g hP hΨg hL hB ⟨β, fun k ↦ rfl, hg, hgP⟩)]
      refine integral_congr_ae ?_
      filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hf⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hg⟩ hgP]
        with y hyf hyg
      rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]
      refine finsum_mem_congr rfl fun w _ ↦ ?_
      unfold sheetDensity
      split_ifs with hγ
      · have hs := hγ.choose_spec.2.self_of_nhds
        set z := hγ.choose y
        have hz : z ∈ mcPts P := hs.2.1
        have hf0 := norm_pos_iff.mpr (hyf z hz hs.2.2)
        have hg0 := norm_pos_iff.mpr (hyg z hz hs.2.2)
        have hA0 := A.pos z hz.1
        have hB0 := (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι) β).pos z hz.1
        rw [← sub_mul]
        congr 1
        show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β).h z)) -
          Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β).h z) =
          Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)
        rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
          Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
          Real.log_div hf0.ne' hg0.ne']
        ring
      · simp
    · simp
  unfold recRRat
  rw [recR_eq] at hRf hRg
  show I P (n + 1) (Fin.snoc L A) = cycR I P L f - cycR I P L g - ptsIntegral P (pot L) (logNormRat A f g)
  rw [← hint]
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]




theorem isProjVarQ_of_isArithVar {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {e : ℕ}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    IsProjVarQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e := by
  obtain ⟨-, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have := hprime
  have hch : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := Ideal.mem_comap.mpr hm
    rw [show P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ from hhor, Ideal.mem_bot] at hm'
    exact hm'
  obtain ⟨hQ, hcomap, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mpr
    ⟨hQ, ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, MvPolynomial.map_X]
    exact h
  · have hd' : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
        P.map (MvPolynomial.map (Int.castRingHom ℚ))) + 1 =
        ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← hdim]
      exact hd
    show ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
      ((e + Fintype.card K : ℕ) : WithBot ℕ∞)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
      P.map (MvPolynomial.map (Int.castRingHom ℚ))) = d at hd'
    induction d using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.bot_add] at hd'
      exact absurd hd' (WithBot.bot_ne_coe)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        have h3 : (⊤ : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast hd'
        rw [top_add] at h3
        exact absurd h3.symm (ENat.natCast_ne_top _)
      | coe n =>
        have h1 : n + 1 = e + 1 + Fintype.card K := by exact_mod_cast hd'
        have h2 : n = e + Fintype.card K := by omega
        rw [h2]
        rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemRegRingSpecZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regRing {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Subring (funField P) where
  carrier := {x | ∀ W, IsClosedPt W → P ≤ W → (x : FractionRing (MRing ι ⧸ P)) ∈ locRing P W}
  mul_mem' ha hb W h1 h2 := mul_mem (ha W h1 h2) (hb W h1 h2)
  one_mem' _ _ _ := one_mem _
  add_mem' ha hb W h1 h2 := add_mem (ha W h1 h2) (hb W h1 h2)
  zero_mem' _ _ _ := zero_mem _
  neg_mem' ha W h1 h2 := neg_mem (ha W h1 h2)

def RegularityOrder.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → Module.Free ℤ (regRing P) ∧ Module.Finite ℤ (regRing P) ∧
      ∀ hF : IsField (funField P), letI := hF.toField; ∀ [NumberField (funField P)],
        Module.finrank ℤ (regRing P) = Module.finrank ℚ (funField P)

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocRingFrac

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_neg {f : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem isMultiHomog_zero (a : K → ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

end LocRingFrac

theorem LocRingFrac.proof : LocRingFrac.Statement := by
  intro K _ ι _ P W _ hW _ y hy
  have h1 : (1 : MRing ι) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  induction hy using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, a, hv, hvW, hu, hva, rfl⟩ := hx
    exact ⟨u, v, a, hu, hva, hvW, IsLocalization.mk'_spec _ _ _⟩
  | zero => exact ⟨0, 1, 0, isMultiHomog_zero 0, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | one => exact ⟨1, 1, 0, AvoidRing.isMultiHomog_one, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * v' + u' * v, v * v', a + a',
      isMultiHomog_add (AvoidRing.isMultiHomog_mul hu hv')
        (by rw [add_comm]; exact AvoidRing.isMultiHomog_mul hu' hv),
      AvoidRing.isMultiHomog_mul hv hv', fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    simp only [RingHom.map_mul, RingHom.map_add]
    rw [← e, ← e']
    ring
  | neg x _ hx =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    exact ⟨-u, v, a, isMultiHomog_neg hu, hv, hvW, by
      simp only [RingHom.map_neg]
      rw [← e]
      ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * u', v * v', a + a', AvoidRing.isMultiHomog_mul hu hu', AvoidRing.isMultiHomog_mul hv hv',
      fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, ← e, ← e']
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace RatioAlgebraicDependence

variable {K : Type} {ι : K → Type} {d : ℕ}

def homog (c : ∀ k, ι k) (p : Fin d → Σ k, ι k) (f : MvPolynomial (Fin d) ℤ) : MvPolynomial (Σ k, ι k) ℤ :=
  ∑ m ∈ f.support, C (AddMonoidAlgebra.coeff f m) *
    ∏ j, X (p j) ^ m j * X ⟨(p j).1, c (p j).1⟩ ^ (f.totalDegree - m j)

theorem aeval_homog {F : Type} [Field F] [Algebra ℤ F] (c : ∀ k, ι k) (p : Fin d → Σ k, ι k)
    (f : MvPolynomial (Fin d) ℤ) (w : (Σ k, ι k) → F) (hw : ∀ j, w ⟨(p j).1, c (p j).1⟩ ≠ 0) :
    aeval w (homog c p f) = (∏ j, w ⟨(p j).1, c (p j).1⟩) ^ f.totalDegree *
      aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) f := by
  classical
  have hsum : aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) f =
      ∑ m ∈ f.support, aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) (monomial m (AddMonoidAlgebra.coeff f m)) := by
    conv_lhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, Finset.mul_sum, homog, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hle : ∀ j, m j ≤ f.totalDegree := fun j ↦
    (monomial_le_degreeOf j hm).trans (degreeOf_le_totalDegree f j)
  rw [map_mul, aeval_C, map_prod, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    ← Finset.prod_pow, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (hle j)
  rw [map_mul, map_pow, map_pow, aeval_X, aeval_X, div_pow, he, Nat.add_sub_cancel_left, pow_add]
  rw [mul_comm (w ⟨(p j).1, c (p j).1⟩ ^ m j), mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ (hw j)),
    mul_comm]

end RatioAlgebraicDependence


open RatioAlgebraicDependence in
theorem RatioAlgDep.proof : RatioAlgDep.Statement := by
  intro K _ ι _ Q d c p hQ
  classical
  by_cases hX : ∃ k, (X ⟨k, c k⟩ : MRing ι) ∈ Q
  · obtain ⟨k, hk⟩ := hX
    refine ⟨1, one_ne_zero, fun z hz hzc ↦ absurd ?_ (hzc k)⟩
    simpa using hz _ hk
  push Not at hX
  obtain ⟨Ω, _, y, hy, hbir⟩ := HilbertSamuel.BirationalModelExists.proof K ι Q d hQ
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 ↦ hX k (by
    rw [← hy, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, hdim⟩ := hQ
  have htr := ConeTrdeg.proof K ι Ω y hbir (fun k ↦ ⟨c k, hc k⟩) (hy ▸ hhor)
  rw [hy] at htr
  have := hprime
  have hA := IntDomainDim.proof (MRing ι ⧸ Q) (CoordinateConeArithVar.algebraMap_injective Q hhor)
  rw [hdim, htr, map_add (f := _), map_natCast] at hA
  have hA' : ((d + Fintype.card K : ℕ) : ℕ∞) =
      Cardinal.toENat (Algebra.trdeg ℤ Ω) + Fintype.card K + 1 := by exact_mod_cast hA
  have hlt : Algebra.trdeg ℤ Ω < d := by
    rw [← Cardinal.toENat_lt_natCast]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Cardinal.toENat (Algebra.trdeg ℤ Ω) = n := by
      refine ENat.ne_top_iff_exists.mp (fun htop ↦ ?_) |>.imp fun _ h ↦ h.symm
      rw [htop] at hA'
      simp at hA'
    rw [hn] at hA' ⊢
    have : d + Fintype.card K = n + Fintype.card K + 1 := by exact_mod_cast hA'
    exact_mod_cast (by omega : n < d)
  have hdep : ¬ AlgebraicIndependent ℤ (fun j : Fin d ↦ y (p j) / y ⟨(p j).1, c (p j).1⟩) :=
    fun hind ↦ by
      have h := hind.cardinalMk_le_trdeg
      rw [Cardinal.mk_fin] at h
      exact absurd hlt (not_lt.2 h)
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨f, hf0, hfne⟩ := hdep

  have hH : homog c p f ∈ Q := by
    rw [← hy, mCoordIdeal, RingHom.mem_ker]
    set L := FractionRing (MvPolynomial K Ω)
    let φ : MvPolynomial K Ω →ₐ[ℤ] L :=
      { algebraMap (MvPolynomial K Ω) L with
        commutes' := fun n ↦ by simp }
    have hφ : Function.Injective φ := fun a b h ↦ IsFractionRing.injective (MvPolynomial K Ω) L h
    have hw : ∀ q : Σ k, ι k, y q ≠ 0 → φ (C (y q) * X q.1) ≠ 0 := fun q hq ↦ by
      rw [Ne, ← map_zero φ, hφ.eq_iff]
      exact mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_ne_zero _)
    have hrat : ∀ j, φ (C (y (p j)) * X (p j).1) / φ (C (y ⟨(p j).1, c (p j).1⟩) * X (p j).1) =
        φ (C (y (p j) / y ⟨(p j).1, c (p j).1⟩)) := fun j ↦ by
      rw [div_eq_iff (hw _ (hc _)), ← map_mul, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hc _)]
    refine hφ ?_
    rw [map_zero, mConeMap, comp_aeval_apply, aeval_homog c p f _ (fun j ↦ hw _ (hc _))]
    simp only [hrat]
    let ψ : Ω →ₐ[ℤ] L := φ.comp (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω))
    have key : (aeval fun j ↦ φ (C (y (p j) / y ⟨(p j).1, c (p j).1⟩))) f =
        ψ (aeval (fun j ↦ y (p j) / y ⟨(p j).1, c (p j).1⟩) f) := by
      rw [comp_aeval_apply]
      rfl
    rw [key, hf0, map_zero, mul_zero]
  refine ⟨f, hfne, fun z hz hzc ↦ ?_⟩
  have h1 := hz _ hH
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def, aeval_homog c p f z (fun j ↦ hzc _)] at h1
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def]
  exact (mul_eq_zero.1 h1).resolve_left
    (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun j _ ↦ hzc _))

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing

noncomputable section

namespace LocRingPow

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


open Classical in
def multiDegWeight (ι : K → Type*) : (Σ k, ι k) → (K → ℕ) := fun p k => if p.1 = k then 1 else 0

theorem weight_multiDegWeight (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (multiDegWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by
  classical
  funext k
  rw [← weight_blockWeight k m, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
    Finset.sum_apply]
  simp only [Pi.smul_apply, multiDegWeight, blockWeight]

theorem isMultiHomog_iff {f : MRing ι} {a : K → ℕ} :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a ↔ IsWeightedHomogeneous (multiDegWeight ι) f a := by
  constructor
  · intro h d hd
    rw [weight_multiDegWeight]
    funext k
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    rw [weight_multiDegWeight] at this
    exact congrFun this k

theorem component_mem [DecidableEq K] {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    (hf : f ∈ J) (D : K → ℕ) : weightedHomogeneousComponent (multiDegWeight ι) D f ∈ J := by
  obtain ⟨g, hg, hgc⟩ := exists_blockComponent (isHomogeneous_of_isMultiHomogIdeal hJ) D Finset.univ hf
  convert hg using 1
  ext m
  rw [coeff_weightedHomogeneousComponent, hgc, weight_multiDegWeight]
  by_cases h : ∀ k, ∑ i, m ⟨k, i⟩ = D k
  · simp [h]
  · simp [h, funext_iff]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem exists_component_not_mem {J : Ideal (MRing ι)} {f : MRing ι} (hf : f ∉ J) :
    ∃ D : K → ℕ, weightedHomogeneousComponent (multiDegWeight ι) D f ∉ J := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hf
  rw [← sum_weightedHomogeneousComponent (w := multiDegWeight ι) (φ := f),
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  exact Ideal.sum_mem _ fun D _ => h D

attribute [local instance] MvPolynomial.weightedGradedAlgebra


omit [∀ k, Fintype (ι k)] in
theorem component_mul_right [DecidableEq K] {f g : MRing ι} {i j : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) :
    weightedHomogeneousComponent (multiDegWeight ι) (i + j) (f * g) =
      weightedHomogeneousComponent (multiDegWeight ι) i f * g := by
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_add_of_right_mem (weightedHomogeneousSubmodule ℤ (multiDegWeight ι))
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg)


omit [∀ k, Fintype (ι k)] in
theorem component_mul_of_not_le [DecidableEq K] {f g : MRing ι} {j n : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) (h : ¬ j ≤ n) :
    weightedHomogeneousComponent (multiDegWeight ι) n (f * g) = 0 := by
  rw [← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_not_le (weightedHomogeneousSubmodule ℤ (multiDegWeight ι))
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg) h

end LocRingPow


open LocRingPow in
theorem LocRingPow.proof : LocRingPow.Statement := by
  classical
  intro K _ ι _ P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hy
  have := hPp
  obtain ⟨hWmin, -⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2

  obtain ⟨n, d, hdW, hd⟩ : ∃ n : ℕ, ∃ d ∉ W, d * u ^ n ∈ P ⊔ Ideal.span {s} := by
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W _ hWmin
    have hu' : algebraMap (MRing ι) (Localization.AtPrime W) u ∈
        ((P ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).radical :=
      hrad ▸ Ideal.mem_map_of_mem _ huW
    obtain ⟨n, hn⟩ := hu'
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff W.primeCompl] at hn
    obtain ⟨⟨⟨i, hi⟩, ⟨c, hc⟩⟩, he⟩ := hn
    rw [← map_mul, IsLocalization.eq_iff_exists W.primeCompl] at he
    obtain ⟨⟨e, he'⟩, hee⟩ := he
    refine ⟨n, e * c, W.primeCompl.mul_mem he' hc, ?_⟩
    have : e * c * u ^ n = e * (u ^ n * c) := by ring
    rw [this, hee]
    exact Ideal.mul_mem_left _ _ hi

  obtain ⟨e, he⟩ := exists_component_not_mem hdW
  set ce := weightedHomogeneousComponent (multiDegWeight ι) e d with hce_def
  have hce : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog ce e :=
    isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hd
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hq

  set D : K → ℕ := e + n • b with hD
  have h1 : weightedHomogeneousComponent (multiDegWeight ι) D (d * u ^ n) = ce * u ^ n :=
    component_mul_right (isMultiHomog_iff.mp (isMultiHomog_pow hu n))
  obtain ⟨G, hG, hGs⟩ : ∃ G : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (G * t) D ∧
      weightedHomogeneousComponent (multiDegWeight ι) D (g * s) = G * s := by
    by_cases hle : a ≤ D
    · refine ⟨weightedHomogeneousComponent (multiDegWeight ι) (D - a) g, ?_, ?_⟩
      · have := isMultiHomog_mul
          (isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous (D - a) g)) ht
        rwa [tsub_add_cancel_of_le hle] at this
      · conv_lhs => rw [← tsub_add_cancel_of_le hle]
        exact component_mul_right (isMultiHomog_iff.mp hs)
    · exact ⟨0, fun m hm => by simp at hm,
        by rw [zero_mul]; exact component_mul_of_not_le (isMultiHomog_iff.mp hs) hle⟩
  have hrel : ce * u ^ n - G * s ∈ P := by
    have := component_mem hPh hp D
    rwa [← add_sub_cancel_right p (g * s), hpq, map_sub, h1, hGs] at this

  have hden : ce * v ^ n ∉ W := fun h =>
    (hWp.mem_or_mem h).elim he fun h => hvW (hWp.mem_of_pow_mem _ h)
  have hdenP : Ideal.Quotient.mk P (ce * v ^ n) ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hden (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  refine ⟨n, IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (G * t)) ⟨_, hdenP⟩,
    Subring.subset_closure ⟨G * t, ce * v ^ n, D, hdenP, hden, hG, isMultiHomog_mul hce (isMultiHomog_pow hv n), rfl⟩,
    ?_⟩
  have hne : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (ce * v ^ n)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdenP
  apply mul_right_cancel₀ hne
  rw [mul_assoc x, IsLocalization.mk'_spec]
  have key := congrArg (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))) (Ideal.Quotient.eq.mpr hrel)
  simp only [map_mul, map_pow] at key hx hy ⊢
  calc y ^ n * (algebraMap _ _ (Ideal.Quotient.mk P ce) * algebraMap _ _ (Ideal.Quotient.mk P v) ^ n)
      = algebraMap _ _ (Ideal.Quotient.mk P ce) * (y * algebraMap _ _ (Ideal.Quotient.mk P v)) ^ n := by ring
    _ = algebraMap _ _ (Ideal.Quotient.mk P ce) * algebraMap _ _ (Ideal.Quotient.mk P u) ^ n := by rw [hy]
    _ = algebraMap _ _ (Ideal.Quotient.mk P G) * algebraMap _ _ (Ideal.Quotient.mk P s) := key
    _ = x * (algebraMap _ _ (Ideal.Quotient.mk P G) * algebraMap _ _ (Ideal.Quotient.mk P t)) := by
        rw [← hx]; ring

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem pfAt_zero (hAI3 : PushforwardArithIntersection.Statement) (I : AllFam) (hI : I.IsFamily) : PFAt I 0 := by
  intro K _ ι _ K' _ ι' _ κ v P' d G J L L' N hv hP' hP hJ hL hL' _
  have hN : (fun j => fibreDeg κ (N j).a) = (Fin.elim0 : Fin 0 → FibreBlock κ → ℤ) :=
    funext fun j => j.elim0
  have hA : Fin.append L' N = L' := funext fun j => by
    rw [Fin.append_right_nil L' N rfl]
    rfl
  rw [hN, hA]
  exact hAI3 I hI K ι K' ι' κ v P' d G J L L' hv hP' hP hJ hL hL'

theorem PushforwardProjLineFlag.proof (hAI3 : PushforwardArithIntersection.Statement) (hStep : PFStep.Statement) : PushforwardProjLineFlag.Statement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d r
  have key : ∀ r, PFAt I r := fun r =>
    Nat.rec (pfAt_zero hAI3 I hI) (fun r h => hStep I hI r h) r
  exact key r K ι K' ι' κ v P' d

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFIntZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFIntZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
    (L : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L' : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (N : Fin r → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι')
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (s : MRing ι'),
    IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') d →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    arInt P' s A (Fin.append L' N) = 0

end

end GroundTheory.Heights₂.Heights.Inter
end
