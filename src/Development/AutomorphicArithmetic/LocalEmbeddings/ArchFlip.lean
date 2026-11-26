module

public import Development.AutomorphicArithmetic.LocalEmbeddings.ArchSz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientField

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.HaarVolKOLeResCardPowOfCongruenceLe
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel GlobalTheory.ConjSize

open GlobalTheory.FunObj.GivenAdm in
theorem UpperTheory.haarVol_KO_le_resCard_pow_of_congruence_le :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A : Type} [Fintype A] [DecidableEq A] {J : Subgroup (GL A k)}, IsOpen (J : Set (GL A k)) → J ≤ GlobalTheory.SplitWeil.KO k A → ∀ {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) ≤ J → (haarVol J).real (GlobalTheory.SplitWeil.KO k A : Set (GL A k)) ≤ (resCard k : ℝ) ^ (e * Fintype.card A * Fintype.card A) := by
  intro k _ _ _ _ _ _ A _ _ J hJo hJK ϖ e hϖ hN
  classical
  let red : GL A k → Matrix A A (Res k e) := fun g i j =>
    if h : (g : Matrix A A k) i j ∈ 𝒪[k] then Ideal.Quotient.mk (𝓂[k] ^ e) ⟨_, h⟩ else 0
  have key : ∀ g ∈ KO k A, ∀ h ∈ KO k A, red g = red h →
      h⁻¹ * g ∈ glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) := by
    intro g hg h hh hgh
    rw [GlobalTheory.FunObj.GivenAdm.mem_glLatCong]
    refine ⟨mul_mem (inv_mem hh) hg, ?_⟩
    have hg' := (mem_KO_iff g).1 hg
    have hh' := (mem_KO_iff h).1 hh
    have e1 : ((h⁻¹ * g : GL A k) : Matrix A A k) - 1
        = ((h⁻¹ : GL A k) : Matrix A A k) * ((g : Matrix A A k) - (h : Matrix A A k)) := by
      rw [Matrix.mul_sub, Units.val_mul, ← Units.val_mul h⁻¹ h, inv_mul_cancel, Units.val_one]
    rw [e1]
    refine GlobalTheory.FunObj.GivenAdm.CongM.mul_left ?_ (fun i j => hh'.2 i j)
    intro i j
    have hij := congrFun (congrFun hgh i) j
    simp only [red, dif_pos (hg'.1 i j), dif_pos (hh'.1 i j)] at hij
    rw [Ideal.Quotient.eq] at hij
    have hv := (Model.val_le_iff_mem hϖ e _).1 hij
    simpa [Matrix.sub_apply] using hv
  haveI := isHaarMeasure_haarVol hJo hJK
  have hNJ : haarVol J (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k)) ≤ 1 := by
    rw [← haarVol_self hJo hJK]
    exact measure_mono hN
  have piece : ∀ M : Matrix A A (Res k e), haarVol J {g | g ∈ KO k A ∧ red g = M} ≤ 1 := by
    intro M
    by_cases hne : ∃ g0, g0 ∈ KO k A ∧ red g0 = M
    · obtain ⟨g0, hg0, hM⟩ := hne
      calc haarVol J {g | g ∈ KO k A ∧ red g = M}
          ≤ haarVol J ((fun h => g0⁻¹ * h) ⁻¹'
              (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k))) := by
            apply measure_mono
            rintro g ⟨hg, hgM⟩
            exact key g hg g0 hg0 (hgM.trans hM.symm)
        _ = haarVol J (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k)) :=
            measure_preimage_mul _ _ _
        _ ≤ 1 := hNJ
    · calc haarVol J {g | g ∈ KO k A ∧ red g = M} ≤ haarVol J ∅ := by
            apply measure_mono
            intro g hg
            exact absurd ⟨g, hg⟩ hne
        _ = 0 := measure_empty
        _ ≤ 1 := zero_le_one
  have hKO : haarVol J (KO k A : Set (GL A k))
      ≤ (Fintype.card (Matrix A A (Res k e)) : ENNReal) := by
    calc haarVol J (KO k A : Set (GL A k))
        ≤ haarVol J (⋃ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))),
            {g | g ∈ KO k A ∧ red g = M}) := by
          apply measure_mono
          intro g hg
          simp only [Set.mem_iUnion]
          exact ⟨red g, Finset.mem_univ _, hg, rfl⟩
      _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))),
            haarVol J {g | g ∈ KO k A ∧ red g = M} := measure_biUnion_finset_le _ _
      _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))), (1 : ENNReal) :=
          Finset.sum_le_sum (fun M _ => piece M)
      _ = (Fintype.card (Matrix A A (Res k e)) : ENNReal) := by
          simp [Finset.card_univ]
  have hcard : Fintype.card (Matrix A A (Res k e))
      = resCard k ^ (e * Fintype.card A * Fintype.card A) := by
    have h1 : Fintype.card (Matrix A A (Res k e))
        = Fintype.card (Res k e) ^ (Fintype.card A * Fintype.card A) := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
      show Nat.card (A → A → Res k e) = _
      rw [Nat.card_fun, Nat.card_fun, ← pow_mul, mul_comm]
    rw [h1, GlobalTheory.FlipMatch.FourierInv.card_res_pow, ← pow_mul, mul_assoc]
  rw [measureReal_def]
  have := ENNReal.toReal_mono (by simp) hKO
  rw [hcard] at this
  simpa using this
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.UnramifiedCharacterInvariant
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumRightInverse
theorem UpperTheory.Reformulated.B.SumRightInverse.sum_rightInv :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsMulLeftInvariant] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      (μ : Set G → ENNReal) (↑K : Set G) ≠ ⊤ →
        ∀ {S : Set G},
          IsCompact S →
            (∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) →
              ∃ (t : Finset (G ⧸ K)),
                (∀ Q ∈ t, Quotient.out Q ∈ S) ∧
                  ∀ (f : G → ℂ),
                    (∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) →
                      ∫ (g : G) in S, f g ∂μ = ∑ Q ∈ t, f (Quotient.out Q) * (↑(μ.real (↑K : Set G)) : ℂ) := by
  intro G _ _ _ _ _ μ _ K hK hμ S hS hSK
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hfin : ((QuotientGroup.mk : G → G ⧸ K) '' S).Finite :=
    (hS.image QuotientGroup.continuous_mk).finite_of_discrete
  let C : G ⧸ K → Set G := fun Q => (fun g => (Quotient.out Q)⁻¹ * g) ⁻¹' (K : Set G)
  have hC : ∀ Q g, g ∈ C Q ↔ (QuotientGroup.mk g : G ⧸ K) = Q := by
    intro Q g
    have h := QuotientGroup.eq (s := K) (a := Quotient.out Q) (b := g)
    rw [QuotientGroup.out_eq'] at h
    rw [eq_comm, h]
    rfl
  have hout : ∀ Q ∈ hfin.toFinset, Quotient.out Q ∈ S := by
    intro Q hQ
    obtain ⟨s, hs, rfl⟩ := hfin.mem_toFinset.1 hQ
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K s
    rw [hk]
    exact hSK s hs k k.2
  have hmeas : ∀ Q, MeasurableSet (C Q) := fun Q =>
    (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ Q, μ (C Q) = μ K := fun Q => MeasureTheory.measure_preimage_mul μ _ _
  have hU : S = ⋃ Q ∈ hfin.toFinset, C Q := by
    ext g
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hg
      exact ⟨_, hfin.mem_toFinset.2 ⟨g, hg, rfl⟩, (hC _ g).2 rfl⟩
    · rintro ⟨Q, hQ, hg⟩
      have := hSK _ (hout Q hQ) _ hg
      simpa using this
  refine ⟨hfin.toFinset, hout, fun f hf => ?_⟩
  have hconst : ∀ Q ∈ hfin.toFinset, Set.EqOn f (fun _ => f (Quotient.out Q)) (C Q) := by
    intro Q hQ g hg
    have := hf _ (hout Q hQ) _ hg
    simpa using this
  have hsplit : ∫ g in ⋃ Q ∈ hfin.toFinset, C Q, f g ∂μ
      = ∑ Q ∈ hfin.toFinset, ∫ g in C Q, f g ∂μ := by
    refine MeasureTheory.integral_biUnion_finset _ (fun Q _ => hmeas Q) ?_ ?_
    · intro Q _ R _ hQR
      refine Set.disjoint_left.2 fun g h1 h2 => hQR ?_
      rw [← (hC Q g).1 h1, (hC R g).1 h2]
    · intro Q hQ
      refine (MeasureTheory.integrableOn_congr_fun (hconst Q hQ) (hmeas Q)).2 ?_
      exact MeasureTheory.integrableOn_const (by rw [hμC]; exact hμ)
  rw [← hU] at hsplit
  rw [hsplit]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [MeasureTheory.setIntegral_congr_fun (hmeas Q) (hconst Q hQ),
    MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, hμC,
    MeasureTheory.measureReal_def, Complex.real_smul, mul_comm]
end

open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel GlobalTheory.ConjSize

open scoped Pointwise in
private theorem sum_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKt : μ K ≠ ⊤) {S : Set G} (hS : IsCompact S)
    (hSK : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) :
    ∃ t : Finset (G ⧸ K), (∀ Q ∈ t, Q.out ∈ S) ∧ ∀ f : G → ℂ, (∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) →
      ∫ g in S, f g ∂μ = ∑ Q ∈ t, f Q.out * μ.real K :=
  _root_.UpperTheory.Reformulated.B.SumRightInverse.sum_rightInv μ K hKo hKt hS hSK

section
variable {k : Type} [Field k] [ValuativeRel k] {A : Type} [Fintype A] [DecidableEq A]

private theorem inv_small (g : GL A k) (c : k)
    (hdet : ∀ y : Matrix A A k, (∀ i j, valuation k (y i j - g.val i j) ≤ valuation k c) → y.det ≠ 0) (i j : A) :
    valuation k ((g⁻¹).val i j) * valuation k c ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  set a := (g⁻¹).val i j with ha
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at hlt; simp at hlt
  have hv0 : 0 < valuation k a := zero_lt_iff.2 (by simpa using ha0)
  have hd : valuation k a⁻¹ ≤ valuation k c := by
    rw [map_inv₀, inv_le_iff_one_le_mul₀' hv0]; exact hlt.le
  refine hdet (g.val - Matrix.single j i a⁻¹) (fun p q => ?_) ?_
  · rw [Matrix.sub_apply, sub_sub_cancel_left, Valuation.map_neg, Matrix.single_apply]
    split_ifs
    · exact hd
    · simp
  · rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun l => (g⁻¹).val l j, fun h => ha0 (congrFun h i), ?_⟩
    rw [Matrix.sub_mulVec, Matrix.single_mulVec, ← ha, inv_mul_cancel₀ ha0]
    funext p
    have : (g.val * (g⁻¹).val) p j = (1 : Matrix A A k) p j := by rw [Units.mul_inv]
    rw [Matrix.mul_apply] at this
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, this, Matrix.one_apply, Function.update_apply,
      Pi.zero_apply, sub_self]

private theorem val_sub_le {x y z c : k} (h : valuation k (y - x) ≤ valuation k c)
    (h' : valuation k (z - x) ≤ valuation k c) : valuation k (y - z) ≤ valuation k c := by
  have : y - z = (y - x) - (z - x) := by ring
  rw [this]
  exact ((valuation k).map_sub _ _).trans (max_le h h')

private theorem inv_mul_int (x : Matrix A A k) (c : k)
    (hdet : ∀ y : Matrix A A k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k c) → y.det ≠ 0)
    (g h : GL A k) (hg : ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k c)
    (hh : ∀ i j, valuation k (h.val i j - x i j) ≤ valuation k c) (i j : A) : (g⁻¹ * h).val i j ∈ 𝒪[k] := by
  have e : (g⁻¹ * h).val = 1 + (g⁻¹).val * (h.val - g.val) := by
    rw [Matrix.mul_sub, Units.inv_mul, Units.val_mul, add_sub_cancel]
  have hs := inv_small g c fun y hy => hdet y fun p q =>
    val_sub_le (hy p q) (by rw [Valuation.map_sub_swap]; exact hg p q)
  rw [e, Matrix.add_apply, Matrix.mul_apply]
  refine add_mem ?_ (Subring.sum_mem _ fun l _ => ?_)
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Valuation.mem_integer_iff, map_mul]
    exact (mul_le_mul_right (val_sub_le (hh l j) (hg l j)) _).trans (hs i l)

end

open scoped Pointwise in
theorem UpperTheory.unramified_character_invariant :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A : Type} [Fintype A] [DecidableEq A] {K : Type} [Field K] (ι τ : K →+* ℂ) {J : Subgroup (GL A k)}, IsOpen (J : Set (GL A k)) → J ≤ GlobalTheory.SplitWeil.KO k A → ∀ (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → CondLE ϖ e ν → (∀ u, Un ι τ (ν u : ℂ)) → (∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι) → ∀ (n : ℕ) (x : Matrix A A k), (∀ i j, valuation k (x i j) ≤ 1) → (∀ y : Matrix A A k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) → y.det ≠ 0) → Sz ι τ (∫ g in {g : GL A k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)}, (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2) ∂(haarVol J)) ((haarVol J).real (GlobalTheory.SplitWeil.KO k A : Set (GL A k))) := by
  intro k _ _ _ _ _ _ A _ _ K _ ι τ J hJo hJK ν ϖ e hϖ hcond hν hap n x hx hdet
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨hSc, hSo⟩ := GlobalTheory.GLBallInt.isCompact_isOpen_glBall x (ϖ ^ e) hdet
  set S := {g : GL A k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)} with hSdef
  set K' : Subgroup (GL A k) :=
    J ⊓ GlobalTheory.SplitFlip.glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) ⊓ GlobalTheory.GLBallInt.rightStab S with hKdef
  have hKo : IsOpen (K' : Set (GL A k)) := by
    simp only [hKdef, Subgroup.coe_inf]
    exact (hJo.inter (GlobalTheory.FunObj.GivenAdm.isOpen_glLatCong _)).inter (GlobalTheory.GLBallInt.isOpen_rightStab hSc hSo)
  have hKJ : K' ≤ J := inf_le_left.trans inf_le_left
  have hJc : IsCompact (J : Set (GL A k)) := isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJK
  have hKt : haarVol J K' ≠ ⊤ :=
    ((measure_mono (show (K' : Set (GL A k)) ⊆ J from hKJ)).trans_lt (by simp [haarVol_self hJo hJK])).ne
  have hinv : ∀ s ∈ S, ∀ k' ∈ K', ((ν (gdet (s * k')) : ℂ) * apow (gdet (s * k')) ((n : ℂ) / 2)) =
      (ν (gdet s) : ℂ) * apow (gdet s) ((n : ℂ) / 2) := by
    intro s _ k' hk
    have hu : gdet k' ∈ unitCong (ϖ ^ e) :=
      GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).2
    rw [gdet_mul, map_mul, Units.val_mul, apow_mul, hcond _ hu, apow_of_valuation_eq_one hu.1]
    simp
  obtain ⟨t, htS, ht⟩ := sum_rightInv (haarVol J) K' hKo hKt hSc
    (fun s hs k' hk => ((Subgroup.mem_inf.1 hk).2 s).1 hs)
  rw [ht (fun g => (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2)) hinv]
  have h1 := ht (fun _ => (1 : ℂ)) (fun _ _ _ _ => rfl)
  rw [setIntegral_const, Finset.sum_const, nsmul_eq_mul, one_mul, Complex.real_smul, mul_one] at h1
  have h1' : (haarVol J).real S = t.card * (haarVol J).real K' := by exact_mod_cast h1
  obtain ⟨m, hm⟩ := GlobalTheory.GLBallInt.measureReal_eq_inv_natCast (haarVol J) hJc (haarVol_self hJo hJK) hKo hKJ
  have hϖe : valuation k ((ϖ ^ e : kˣ) : k) ≤ 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one' (hϖ.trans_lt uniformizer_lt_one).le _
  have hdv : ∀ g ∈ S, valuation k ((gdet g : kˣ) : k) ≤ 1 := by
    intro g hg
    have hint : ∀ i j, g.val i j ∈ 𝒪[k] := fun i j => by
      have : g.val i j = (g.val i j - x i j) + x i j := by ring
      rw [this]
      exact add_mem ((Valuation.mem_integer_iff _ _).2 ((hg i j).trans hϖe))
        ((Valuation.mem_integer_iff _ _).2 (hx i j))
    have : g.val.det ∈ 𝒪[k] := by
      rw [Matrix.det_apply']
      exact Subring.sum_mem _ fun σ _ => mul_mem (intCast_mem _ _) (Subring.prod_mem _ fun i _ => hint _ _)
    exact (Valuation.mem_integer_iff _ _).1 this
  have hsz : Sz ι τ (∑ Q ∈ t, (ν (gdet Q.out) : ℂ) * apow (gdet Q.out) ((n : ℂ) / 2) * ((haarVol J).real K' : ℝ))
      (t.card * (haarVol J).real K') := by
    refine Sz.sum_card t fun Q hQ => ?_
    have h2 := (hν (gdet Q.out)).mul_sz (sz_apow_of_le_one (τ := τ) _ (hap _) n (hdv _ (htS Q hQ)))
    have h3 := h2.mul (Sz.inv_nat (ι := ι) (τ := τ) m)
    rw [hm]
    simpa using h3
  refine hsz.mono ?_
  rw [← h1']
  let x' : GL A k := Matrix.GeneralLinearGroup.mkOfDetNeZero x (hdet x fun i j => by simp)
  have hx' : ∀ i j, valuation k (x'.val i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := fun i j => by
    show valuation k (x i j - x i j) ≤ _
    simp
  have hsub : S ⊆ x' • (GlobalTheory.SplitWeil.KO k A : Set (GL A k)) := fun g hg =>
    ⟨x'⁻¹ * g, (mem_KO_iff _).2 ⟨inv_mul_int x _ hdet x' g hx' hg, by
      rw [mul_inv_rev, inv_inv]; exact inv_mul_int x _ hdet g x' hg hx'⟩, by simp⟩
  rw [measureReal_def, measureReal_def]
  refine ENNReal.toReal_mono isCompact_KO.measure_lt_top.ne ?_
  exact (measure_mono hsub).trans (measure_smul _ _ _).le
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsMemKOEqStdFrameMulOfIsPrimFrameFin
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

open Matrix in
theorem UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame_fin :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {a' : ℕ} (σ : A ⊕ Fin a' ≃ D) (X : Matrix A D k), IsPrimFrame (GlobalTheory.SplitFlip.stdLat k D) X → ∃ κ ∈ GlobalTheory.SplitWeil.KO k D, X = X0 k σ * (invT κ).val := by
  intro k _ _ _ _ A D _ _ _ _ a' σ X hX
  have hXint : ∀ i j, X i j ∈ 𝒪[k] := mem_matLat_stdLat.1 hX.2.1
  obtain ⟨R, hRint, hXR⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hX
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).1 hX.1
  set Y : Matrix (Fin a') D k := Y0 k σ * (h : Matrix D D k) with hYeq
  have hYX : Y * X.transpose = 0 := by
    rw [hh]
    exact frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero σ h
  have hYrank : Y.rank = a' := by
    have hY0 : Y0 k σ * (Y0 k σ).transpose = 1 := by
      ext i j
      simp [Y0, Matrix.mul_apply, Matrix.one_apply, Finset.sum_ite_eq']
    have hW : Y * (((h⁻¹ : GL D k) : Matrix D D k) * (Y0 k σ).transpose) = 1 := by
      rw [hYeq, Matrix.mul_assoc, ← Matrix.mul_assoc (h : Matrix D D k), ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.one_mul, hY0]
    have h1 := Matrix.rank_mul_le_left Y (((h⁻¹ : GL D k) : Matrix D D k) * (Y0 k σ).transpose)
    rw [hW, Matrix.rank_one, Fintype.card_fin] at h1
    have h2 := Matrix.rank_le_card_height Y
    rw [Fintype.card_fin] at h2
    omega
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.PrimFrameExist.exists_gl_mul_isPrimFrame k a' D (fun _ => 1) Y hYrank
  set Y' : Matrix (Fin a') D k := (g₀ : Matrix (Fin a') (Fin a') k) * Y with hY'eq
  have hY'prim : IsPrimFrame (stdLat k D) Y' := hg₀
  have hY'int : ∀ i j, Y' i j ∈ 𝒪[k] := mem_matLat_stdLat.1 hY'prim.2.1
  obtain ⟨S, hSint, hY'S⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hY'prim
  have hY'X : Y' * X.transpose = 0 := by
    rw [hY'eq, Matrix.mul_assoc, hYX, Matrix.mul_zero]
  have hRX : R.transpose * X.transpose = 1 := by
    rw [← Matrix.transpose_mul, hXR, Matrix.transpose_one]
  set S' : Matrix D (Fin a') k := S - X.transpose * (R.transpose * S) with hS'eq
  have hRS' : R.transpose * S' = 0 := by
    rw [hS'eq, Matrix.mul_sub, ← Matrix.mul_assoc, hRX, Matrix.one_mul, sub_self]
  have hY'S' : Y' * S' = 1 := by
    rw [hS'eq, Matrix.mul_sub, ← Matrix.mul_assoc, hY'X, Matrix.zero_mul, sub_zero, hY'S]
  have mulInt : ∀ {m n o : Type} [Fintype n] (P : Matrix m n k) (Q : Matrix n o k),
      (∀ i j, P i j ∈ 𝒪[k]) → (∀ i j, Q i j ∈ 𝒪[k]) → ∀ i j, (P * Q) i j ∈ 𝒪[k] := by
    intro m n o _ P Q hP hQ i j
    rw [Matrix.mul_apply]
    exact sum_mem fun x _ => mul_mem (hP _ _) (hQ _ _)
  have hS'int : ∀ i j, S' i j ∈ 𝒪[k] := by
    intro i j
    rw [hS'eq, Matrix.sub_apply]
    refine sub_mem (hSint i j) ?_
    exact mulInt _ _ (fun a b => hXint b a) (mulInt _ _ (fun a b => hRint b a) hSint) i j
  let K : Matrix D D k := (Matrix.fromRows R.transpose Y').submatrix σ.symm (Equiv.refl D)
  let N : Matrix D D k := (Matrix.fromCols X.transpose S').submatrix (Equiv.refl D) σ.symm
  have hKN : K * N = 1 := by
    simp only [K, N]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromRows_mul_fromCols, hRX, hRS', hY'X, hY'S',
      Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  have hNK : N * K = 1 := mul_eq_one_comm.1 hKN
  let κ : GL D k := ⟨K, N, hKN, hNK⟩
  refine ⟨κ, ?_, ?_⟩
  · rw [mem_KO_iff]
    constructor
    · intro e d
      show K e d ∈ 𝒪[k]
      simp only [K, Matrix.submatrix_apply, Equiv.refl_apply]
      rcases σ.symm e with i | j
      · simpa using hRint d i
      · simpa using hY'int j d
    · intro d e
      show N d e ∈ 𝒪[k]
      simp only [N, Matrix.submatrix_apply, Equiv.refl_apply]
      rcases σ.symm e with i | j
      · simpa using hXint i d
      · simpa using hS'int d j
  · ext i d
    rw [frameMatrixFirstColumnBlock_mul_apply]
    show X i d = N d (σ (Sum.inl i))
    simp [N]
end

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel Matrix

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

namespace GlobalTheory.ConjSize

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {K : Type} [Field K] {ι τ : K →+* ℂ}

theorem one_le_q : (1 : ℝ) ≤ resCard k := by
  have h := GlobalTheory.FlipMatch.FourierInv.card_res_pow k 1
  have hp : 0 < Fintype.card (Res k 1) := Fintype.card_pos
  rw [h, pow_one] at hp
  exact_mod_cast hp

theorem card_res_fun (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : ℕ) :
    Fintype.card (A → B → Res k e) = resCard k ^ (e * Fintype.card A * Fintype.card B) := by
  rw [Fintype.card_fun, Fintype.card_fun, GlobalTheory.FlipMatch.FourierInv.card_res_pow, ← pow_mul, ← pow_mul]
  congr 1; ring

theorem sz_fourierSum {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → Un ι τ (ψ x : ℂ))
    {Φ : Matrix A D k → ℂ} {B : ℝ} (hΦ : ∀ X, Sz ι τ (Φ X) B) (Y : Matrix A D k) : Sz ι τ (fourierSum ψ ϖ e P Φ Y) B := by
  rw [fourierSum_apply]
  have hB0 : 0 ≤ B := (hΦ Y).nonneg
  split_ifs with hY
  · have hsum : Sz ι τ (∑ T : A → P → Res k e, Φ (setCols P Y (liftRes T)) * (ψ (pairCols P Y (liftRes T)) : ℂ))
        ((Finset.univ : Finset (A → P → Res k e)).card * B) := by
      apply Sz.sum_card
      intro T _
      apply Sz.mul_un (hΦ _)
      apply hψ
      have hm : ((ϖ ^ e : kˣ) : k) * pairCols P Y (liftRes T) ∈ 𝒪[k] := by
        simp only [pairCols, Finset.mul_sum]
        refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
        rw [mul_left_comm]
        exact Subring.mul_mem _ (liftRes_mem T i j) (hY i j j.2)
      exact (Valuation.mem_integer_iff _ _).mp hm
    have hinv := Sz.inv_nat (ι := ι) (τ := τ) (resCard k ^ (e * Fintype.card A * P.card))
    push_cast at hinv
    refine (hinv.mul hsum).mono ?_
    have hc : (Finset.univ : Finset (A → P → Res k e)).card = resCard k ^ (e * Fintype.card A * P.card) := by
      rw [Finset.card_univ, card_res_fun, Fintype.card_coe]
    rw [hc]
    have hq : (0:ℝ) < resCard k := lt_of_lt_of_le one_pos one_le_q
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  · exact Sz.zero hB0

theorem sz_invFourierSum {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → Un ι τ (ψ x : ℂ))
    {Φ : Matrix A D k → ℂ} {B : ℝ} (hΦ : ∀ X, Sz ι τ (Φ X) B) (T : Matrix A D k) :
    Sz ι τ (invFourierSum ψ⁻¹ ϖ e P Φ T) ((resCard k : ℝ) ^ (e * Fintype.card A * P.card) * B) := by
  rw [invFourierSum_inv_apply]
  have hB0 : 0 ≤ B := (hΦ T).nonneg
  have hq : (0:ℝ) < resCard k := lt_of_lt_of_le one_pos one_le_q
  split_ifs with hT
  · have hc : (Finset.univ : Finset (A → P → Res k e)).card = resCard k ^ (e * Fintype.card A * P.card) := by
      rw [Finset.card_univ, card_res_fun, Fintype.card_coe]
    have hsum := Sz.sum_card (ι := ι) (τ := τ) (Finset.univ : Finset (A → P → Res k e))
      (f := fun S => Φ (setCols P T ((ϖ ^ e)⁻¹ • liftRes S)) * (ψ (pairCols P T ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ))
      (B := B) (by
        intro S _
        apply Sz.mul_un (hΦ _)
        apply hψ
        have key : ((ϖ ^ e : kˣ) : k) * pairCols P T ((ϖ ^ e)⁻¹ • liftRes S) = pairCols P T (liftRes S) := by
          simp only [pairCols, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
        have hm : pairCols P T (liftRes S) ∈ 𝒪[k] := by
          simp only [pairCols]
          exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
            Subring.mul_mem _ (liftRes_mem S i j) (hT i j j.2)
        rw [key]
        exact (Valuation.mem_integer_iff _ _).mp hm)
    rw [hc] at hsum
    push_cast at hsum
    exact hsum
  · exact Sz.zero (mul_nonneg (by positivity) hB0)

variable [MeasurableSpace k] [BorelSpace k]

private theorem res_eq_of_liftRes_sub_valuation_le {A : Type} {ϖ : kˣ} (hϖ : IsUnif ϖ) {e : ℕ} (T T' : A → A → Res k e)
    (h : ∀ i j, valuation k (liftRes T i j - liftRes T' i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) : T = T' := by
  funext i j
  have h1 := (Model.val_le_iff_mem hϖ e ((T i j).out - (T' i j).out)).mpr (by simpa [liftRes] using h i j)
  rw [← Ideal.Quotient.mk_out (T i j), ← Ideal.Quotient.mk_out (T' i j)]
  exact Ideal.Quotient.eq.mpr h1

set_option synthInstance.maxHeartbeats 200000 in
private theorem exists_res_approx_of_entries_integral {A : Type} {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (x : Matrix A A k)
    (hx : ∀ i j, x i j ∈ 𝒪[k]) :
    ∃ T : A → A → Res k e, ∀ i j, valuation k (x i j - liftRes T i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  refine ⟨fun i j => Ideal.Quotient.mk _ ⟨x i j, hx i j⟩, fun i j => ?_⟩
  have h1 : (⟨x i j, hx i j⟩ : 𝒪[k]) - (Ideal.Quotient.mk (𝓂[k] ^ e) ⟨x i j, hx i j⟩ : Res k e).out ∈ 𝓂[k] ^ e := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  have h2 := (Model.val_le_iff_mem hϖ e _).mp h1
  simpa [liftRes] using h2

theorem sz_zeta {A : Type} [Fintype A] [DecidableEq A] {J : Subgroup (GL A k)} (hJo : IsOpen (J : Set (GL A k)))
    (hJK : J ≤ KO k A) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hJ : glLatCong (ϖ ^ e) (SplitFlip.stdLat k A) ≤ J)
    (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν) (hνU : ∀ u, Un ι τ (ν u : ℂ)) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι)
    (n : ℕ) {φ : Matrix A A k → ℂ} (hφ : IsNatDatum ϖ e φ) {B : ℝ} (hB : ∀ X, Sz ι τ (φ X) B) :
    Sz ι τ (∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2) ∂(haarVol J))
      ((resCard k : ℝ) ^ (2 * e * Fintype.card A * Fintype.card A) * B) := by
  haveI := isHaarMeasure_haarVol hJo hJK
  have hB0 : 0 ≤ B := (hB 0).nonneg
  set S : (A → A → Res k e) → Set (GL A k) := fun T =>
    {g | ∀ i j, valuation k ((g : Matrix A A k) i j - liftRes T i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)} with hS
  have hSm : ∀ T, MeasurableSet (S T) := fun T =>
    ((GlobalTheory.SmallFInF.isOpen_cosetM (ϖ ^ e) (liftRes T)).preimage Units.continuous_val).measurableSet
  have hconst : ∀ T, ∀ g ∈ S T, φ (g : Matrix A A k) = φ (liftRes T) := by
    intro T g hg
    have := hφ.2 (liftRes T) ((g : Matrix A A k) - liftRes T)
      (GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.mpr (fun i j => hg i j))
    rw [add_sub_cancel] at this
    exact this
  have hzero : ∀ g : GL A k, ¬ (∀ i j, (g : Matrix A A k) i j ∈ 𝒪[k]) → φ (g : Matrix A A k) = 0 := by
    intro g hg
    apply hφ.1
    rwa [mem_matLat_stdLat]
  set f : GL A k → ℂ := fun g => (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2) with hf
  have hF : (fun g : GL A k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2)) =
      fun g => ∑ T, (S T).indicator (fun g => φ g.val * f g) g := by
    funext g
    by_cases hg : ∀ i j, (g : Matrix A A k) i j ∈ 𝒪[k]
    · obtain ⟨T0, hT0⟩ := exists_res_approx_of_entries_integral hϖ e (g : Matrix A A k) hg
      rw [Finset.sum_eq_single T0]
      · rw [Set.indicator_apply, if_pos (show g ∈ S T0 from hT0), mul_assoc]
      · intro T _ hT
        rw [Set.indicator_apply, if_neg]
        intro hgT
        apply hT
        apply res_eq_of_liftRes_sub_valuation_le hϖ
        intro i j
        rw [show liftRes T i j - liftRes T0 i j =
          ((g : Matrix A A k) i j - liftRes T0 i j) + (liftRes T i j - (g : Matrix A A k) i j) by ring]
        exact Valuation.map_add_le _ (hT0 i j) (by rw [Valuation.map_sub_swap]; exact hgT i j)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h0 : φ g.val = 0 := hzero g hg
      simp [Set.indicator_apply, h0]
  by_cases hint : Integrable (fun g : GL A k => φ g.val * f g) (haarVol J)
  · have hI : ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2) ∂(haarVol J) =
        ∑ T, φ (liftRes T) * ∫ g in S T, f g ∂(haarVol J) := by
      rw [hF, integral_finsetSum _ (fun T _ => hint.indicator (hSm T))]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [integral_indicator (hSm T)]
      rw [setIntegral_congr_fun (hSm T) (g := fun g => φ (liftRes T) * f g) (fun g hg => by
        show φ g.val * f g = φ (liftRes T) * f g
        rw [hconst T g hg])]
      exact integral_const_mul _ _
    rw [hI]
    have hvol := UpperTheory.haarVol_KO_le_resCard_pow_of_congruence_le hJo hJK hϖ hJ
    have hterm : ∀ T, Sz ι τ (φ (liftRes T) * ∫ g in S T, f g ∂(haarVol J))
        (B * (resCard k : ℝ) ^ (e * Fintype.card A * Fintype.card A)) := by
      intro T
      refine (hB _).mul ?_
      by_cases hsing : ∃ y : Matrix A A k,
          (∀ i j, valuation k (y i j - liftRes T i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) ∧ y.det = 0
      · obtain ⟨y, hy, hdet⟩ := hsing
        have hSy : S T = {g : GL A k | ∀ i j,
            valuation k ((g : Matrix A A k) i j - y i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)} := by
          ext g
          simp only [hS, Set.mem_setOf_eq]
          constructor
          · intro hg i j
            rw [show (g : Matrix A A k) i j - y i j =
              ((g : Matrix A A k) i j - liftRes T i j) + (liftRes T i j - y i j) by ring]
            exact Valuation.map_add_le _ (hg i j) (by rw [Valuation.map_sub_swap]; exact hy i j)
          · intro hg i j
            rw [show (g : Matrix A A k) i j - liftRes T i j =
              ((g : Matrix A A k) i j - y i j) + (y i j - liftRes T i j) by ring]
            exact Valuation.map_add_le _ (hg i j) (hy i j)
        have h0 : ∫ g in S T, f g ∂(haarVol J) = 0 := by
          rw [hSy]
          exact @GlobalTheory.CosetVanish.integral_coset_singular_eq_zero _ _ _ _ _ _ _ _ _ _
            (haarVol J) (isHaarMeasure_haarVol hJo hJK).toIsMulLeftInvariant ν ((n : ℂ) / 2) hram (ϖ ^ e) y hdet
        rw [h0]
        exact Sz.zero (by positivity)
      · have h1 := UpperTheory.unramified_character_invariant ι τ hJo hJK ν hϖ hν hνU habs n (liftRes T)
          (fun i j => (Valuation.mem_integer_iff _ _).mp (liftRes_mem T i j))
          (fun y hy hdet => hsing ⟨y, hy, hdet⟩)
        exact h1.mono hvol
    have hsum := Sz.sum_card (ι := ι) (τ := τ) (Finset.univ : Finset (A → A → Res k e)) (fun T _ => hterm T)
    refine hsum.mono (le_of_eq ?_)
    rw [Finset.card_univ, card_res_fun]
    push_cast
    rw [show 2 * e * Fintype.card A * Fintype.card A =
      e * Fintype.card A * Fintype.card A + e * Fintype.card A * Fintype.card A by ring, pow_add]
    ring
  · rw [integral_undef]
    · exact Sz.zero (mul_nonneg (by positivity) hB0)
    · intro h
      apply hint
      simpa only [mul_assoc] using h

omit [MeasurableSpace k] [BorelSpace k] in
theorem row_mul' {A B C : Type} [Fintype B] (Y : Matrix A B k) (M : Matrix B C k) (i : A) : (Y * M).row i = Y.row i ᵥ* M := by
  ext j
  rfl


omit [MeasurableSpace k] [BorelSpace k] in
theorem isNatDatum_comp {A A' D : Type} [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D)
    {ϖ : kˣ} {e : ℕ} (c : D → kˣ) {Ψ : Matrix A' D k → ℂ} (hΨ : HasDepth ϖ e (diagLat c) Ψ) {κ : GL D k} (hκ : κ ∈ KO k D) :
    IsNatDatum ϖ e fun g : Matrix A' A' k => Ψ (g * (Y0 k σ * (κ * diagGL c).val)) := by
  have hrow : ∀ (M : Matrix A' D k) (i : A') (b d : D → kˣ), (∀ j, d j = b j * c j) →
      ((M * (κ * diagGL c : GL D k).val).row i ∈ diagLat d ↔ (M * (κ : Matrix D D k)).row i ∈ diagLat b) := by
    intro M i b d hd
    rw [Units.val_mul, diagGL_val, ← Matrix.mul_assoc, row_mul', ← diagGL_val]
    exact GlobalTheory.FrameDepth.vecMul_diagGL_mem b c d hd _
  have hYκ : ∀ a j, (Y0 k σ * (κ : Matrix D D k)) a j ∈ 𝒪[k] := by
    intro a j
    rw [frameMatrixSecondColumnBlock_mul_apply]
    exact ((mem_KO_iff κ).mp hκ).1 _ _
  refine ⟨?_, ?_⟩
  · intro g hg
    by_contra hne
    apply hg
    have hm : g * (Y0 k σ * (κ * diagGL c : GL D k).val) ∈ matLat A' (diagLat c) := by
      by_contra h
      exact hne (hΨ.1 _ h)
    have hall : g * Y0 k σ * (κ : Matrix D D k) ∈ matLat A' (stdLat k D) := by
      intro i
      have hi := hm i
      rw [← Matrix.mul_assoc, hrow (g * Y0 k σ) i 1 c (fun j => by simp)] at hi
      exact hi
    have h1 : ((1 : GL A' k) : Matrix A' A' k) * (g * Y0 k σ) * (κ : Matrix D D k) ∈ matLat A' (stdLat k D) := by
      rw [Units.val_one, Matrix.one_mul]
      exact hall
    have h1' := (mul_mul_mem_matLat_iff (g := (1 : GL A' k)) (h := κ) (KO k A').one_mem hκ (g * Y0 k σ)).mp h1
    rw [mem_matLat_stdLat] at h1'
    rw [mem_matLat_stdLat]
    intro i a
    have h2 := h1' i (σ (Sum.inr a))
    have h3 : (g * Y0 k σ) i (σ (Sum.inr a)) = g i a := by
      simp [Matrix.mul_apply, Y0]
    rwa [h3] at h2
  · intro X Z hZ
    show Ψ ((X + Z) * (Y0 k σ * (κ * diagGL c : GL D k).val)) = Ψ (X * (Y0 k σ * (κ * diagGL c : GL D k).val))
    rw [Matrix.add_mul]
    apply hΨ.2
    rw [smul_diagLat]
    intro i
    rw [← Matrix.mul_assoc, hrow (Z * Y0 k σ) i (fun _ => ϖ ^ e) (fun j => ϖ ^ e * c j) (fun j => rfl)]
    have hC : GlobalTheory.FunObj.GivenAdm.CongM (ϖ ^ e) (Z * Y0 k σ * (κ : Matrix D D k)) := by
      rw [Matrix.mul_assoc]
      exact GlobalTheory.FunObj.GivenAdm.CongM.mul_right (GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.mp hZ) hYκ
    have hm := GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.mpr hC i
    rw [show stdLat k D = diagLat 1 from rfl, smul_diagLat] at hm
    simpa using hm

theorem sz_phiA {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {a' : ℕ}
    {J : Subgroup (GL (Fin a') k)} (hJo : IsOpen (J : Set (GL (Fin a') k))) (hJK : J ≤ KO k (Fin a')) (σ : A ⊕ Fin a' ≃ D)
    (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hJ : glLatCong (ϖ ^ e) (SplitFlip.stdLat k (Fin a')) ≤ J)
    (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν) (hνU : ∀ u, Un ι τ (ν u : ℂ)) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι)
    (P : Finset D) {Ψ : Matrix (Fin a') D k → ℂ} (hΨ : HasDepth ϖ e (blockLat ϖ e P) Ψ) {B : ℝ} (hB : ∀ Y, Sz ι τ (Ψ Y) B)
    (X : Matrix A D k) : Sz ι τ (phiA (haarVol J) σ ν ϖ e (blockLat ϖ e P) Ψ X)
      ((resCard k : ℝ) ^ (e * a' * Fintype.card D + 2 * e * a' * a') * B) := by
  haveI := isHaarMeasure_haarVol hJo hJK
  have hB0 : 0 ≤ B := (hB 0).nonneg
  have hq : (1:ℝ) ≤ resCard k := one_le_q
  unfold phiA
  split_ifs with hX
  swap
  · exact Sz.zero (by positivity)
  rw [latA_blockLat] at hX
  have hlat : ∀ x : D → k, x ᵥ* (((blockScale ϖ e Pᶜ)⁻¹ : GL D k) : Matrix D D k) ∈ stdLat k D ↔
      x ∈ blockLat ϖ e Pᶜ := by
    intro x
    rw [← vecMul_blockScale_mem ϖ e Pᶜ, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
  obtain ⟨κ, hκ, hκX⟩ := UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame_fin σ _ (Model.isPrimFrame_mul hX (blockScale ϖ e Pᶜ)⁻¹ hlat)
  have hinvT : invT (diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j)) = blockScale ϖ e Pᶜ := by
    apply Units.ext
    show ((((diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j))⁻¹ : GL D k) : Matrix D D k))ᵀ = _
    have h1 : (((diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j))⁻¹ : GL D k) : Matrix D D k) =
        diagonal fun j => (((ϖ ^ e * blockUnits ϖ e P j)⁻¹ : kˣ) : k) := rfl
    rw [h1, Matrix.diagonal_transpose, blockScale, diagGL_val]
    congr 1
    funext j
    by_cases hj : j ∈ P <;> simp [blockUnits, hj]
  have hXeq : X = X0 k σ * ((invT (κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j)) : GL D k) : Matrix D D k) := by
    rw [map_mul, hinvT, Units.val_mul, ← Matrix.mul_assoc, ← hκX, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  rw [hXeq, splitTheta_fFun_frameFirstBlock_mul]
  have hY : Y0 k σ * ((κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j) : GL D k) : Matrix D D k) =
      ((diagGL (fun _ : Fin a' => ϖ ^ e) : GL (Fin a') k) : Matrix (Fin a') (Fin a') k) *
        (Y0 k σ * ((κ * diagGL (blockUnits ϖ e P) : GL D k) : Matrix D D k)) := by
    have hd : ((diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j) : GL D k) : Matrix D D k) =
        ((ϖ ^ e : kˣ) : k) • ((diagGL (blockUnits ϖ e P) : GL D k) : Matrix D D k) := by
      rw [diagGL_val, diagGL_val]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.diagonal_apply_ne _ hij]
    rw [diagGL_val, Units.val_mul, Units.val_mul, hd, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.smul_eq_diagonal_mul]
  have hmulL := smallF_mul_left (haarVol J) ν Ψ (diagGL (fun _ : Fin a' => ϖ ^ e))
    (Y0 k σ * ((κ * diagGL (blockUnits ϖ e P) : GL D k) : Matrix D D k))
  rw [← hY] at hmulL
  have hsmall : smallF (haarVol J) ν Ψ (Y0 k σ * ((κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j) : GL D k) : Matrix D D k)) =
      (ν (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))) : ℂ)⁻¹ *
        (apow (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))) ((Fintype.card D : ℂ) / 2))⁻¹ *
        smallF (haarVol J) ν Ψ (Y0 k σ * ((κ * diagGL (blockUnits ϖ e P) : GL D k) : Matrix D D k)) := by
    rw [← hmulL]
    have h1 : (ν (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))) : ℂ) ≠ 0 := Units.ne_zero _
    have h2 := apow_ne_zero (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))) ((Fintype.card D : ℂ) / 2)
    field_simp
  rw [hsmall]
  have hzeta := sz_zeta (ι := ι) (τ := τ) hJo hJK ν hϖ hJ hν hram hνU habs (Fintype.card D)
    (isNatDatum_comp σ (blockUnits ϖ e P) hΨ hκ) (fun X => hB _)
  simp only [Fintype.card_fin] at hzeta
  have hdet0 : gdet (diagGL (fun _ : Fin a' => ϖ ^ e)) = (ϖ ^ e) ^ a' := by
    ext
    simp [gdet, diagGL_val, Matrix.det_diagonal]
  have hnabs : nabs k (gdet (diagGL (fun _ : Fin a' => ϖ ^ e)))⁻¹ = (resCard k : ℝ) ^ (e * a') := by
    have hn : ((distribHaarChar k ϖ : NNReal) : ℝ) = (resCard k : ℝ)⁻¹ :=
      GlobalTheory.SplitWeil.nabs_uniformiser hϖ.irreducible rfl
    rw [hdet0]
    unfold nabs
    rw [map_inv, map_pow, map_pow]
    push_cast
    rw [hn, ← pow_mul, inv_pow, inv_inv]
  have hA : Sz ι τ (apow (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))) ((Fintype.card D : ℂ) / 2))⁻¹
      (((resCard k : ℝ) ^ (e * a')) ^ Fintype.card D) := by
    rw [← apow_neg, ← apow_inv]
    exact sz_apow_nat_half _ (habs _) _ (one_le_pow₀ hq) hnabs.le
  have hdh : valuation k ((gdet (κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j)) : kˣ) : k) ≤ 1 := by
    rw [gdet_mul, Units.val_mul, map_mul, valuation_gdet_of_mem_KO hκ, one_mul]
    have hp : ((gdet (diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j)) : kˣ) : k) =
        ∏ j, (((ϖ ^ e * blockUnits ϖ e P j) : kˣ) : k) := by
      simp [gdet, diagGL_val, Matrix.det_diagonal]
    rw [hp, map_prod]
    apply Finset.prod_le_one'
    intro j _
    by_cases hj : j ∈ P
    · simp [blockUnits, hj]
    · simp only [blockUnits, hj, if_false, mul_one, Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_one' ((Valuation.mem_integer_iff _ _).mp (IsUnif.mem hϖ)) _
  have hH : Sz ι τ (apow (gdet (κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j))) ((Fintype.card D : ℂ) / 2)) 1 :=
    sz_apow_of_le_one _ (habs _) _ hdh
  have hfinal := (hνU (gdet (κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j)))).mul_sz
    (hH.mul ((Un.inv (hνU (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))))).mul_sz (hA.mul hzeta)))
  refine Sz.mono (B := 1 * (((resCard k : ℝ) ^ (e * a')) ^ Fintype.card D * ((resCard k : ℝ) ^ (2 * e * a' * a') * B))) ?_ ?_
  · convert hfinal using 1
    simp only [smallF]
    ring
  · rw [one_mul, ← pow_mul, ← mul_assoc, ← pow_add]

theorem sz_flipTensor {G : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → Un ι τ (ψ x : ℂ)) {i j M : ℕ}
    (hM : G.rank (i + 1, j + 1) ≤ M)
    (hν : CondLE ϖ e (G.nu i j)) (hram : ¬ IsUnram (G.nu i j)) (hνU : ∀ u, Un ι τ (G.nu i j u : ℂ)) {J : G.Level}
    (hJ : IsOpen (J (i, j) : Set (GL (Fin (G.rank (i, j))) k))) (hK : J (i, j) ≤ KO k _)
    (hC : glLatCong (ϖ ^ e) (SplitFlip.stdLat k _) ≤ J (i, j)) {γ : List Edge}
    (h1 : Edge.theta i j ∈ γ) (h2 : Edge.ex i j ∈ γ) {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) {B : ℝ}
    (hB : ∀ x, Sz ι τ (T x) B) (x : G.Args) :
    Sz ι τ (G.flipTensor .one ψ ϖ e i j J T x) ((resCard k : ℝ) ^ (6 * e * M ^ 2) * B) := by
  have hq : (1:ℝ) ≤ resCard k := one_le_q
  have hB0 : 0 ≤ B := (hB x).nonneg
  have hJ' := isOpen_map_invT hJ hK
  have hC' : glLatCong (ϖ ^ e) (SplitFlip.stdLat k (Fin (G.rank (i, j)))) ≤ Subgroup.map invT (J (i, j)) := by
    intro g hg
    exact ⟨invT g, hC (GlobalTheory.FunObj.GivenAdm.invT_mem_glLatCong hg), invT_invT g⟩
  have hdep := (FourierDepth.fourier_exchange k (Fin (G.rank (i, j))) (G.Cols i j) ψ ϖ e
      (Assignment.one.block (Fin (G.rank (i, j + 1))) (Fin (G.rank (i + 1, j)))) hϖ hψc).1 _
      (GlobalTheory.FunObj.isNatDatum_sliceB hT h1 h2 x)
  unfold Grid.flipTensor squareFlip
  refine Sz.mono (sz_invFourierSum ψ ϖ e _ hψ (fun X => sz_phiA hJ'.1 hJ'.2 _ (G.nu i j) hϖ hC' hν hram hνU habs _
    hdep (fun Y => sz_fourierSum ψ ϖ e _ hψ (fun Z => hB _) Y) X) _) ?_
  rw [← mul_assoc, ← pow_add]
  apply mul_le_mul_of_nonneg_right _ hB0
  apply pow_le_pow_right₀ hq
  have hcard : Fintype.card (G.Cols i j) = G.rank (i + 1, j + 1) + G.rank (i, j) := by
    simp only [Grid.Cols, Fintype.card_sum, Fintype.card_fin]
    exact (G.rank_square i j).symm
  have hc := Finset.card_le_univ (Assignment.one.block (Fin (G.rank (i, j + 1))) (Fin (G.rank (i + 1, j))))ᶜ
  have h00 : G.rank (i, j) ≤ G.rank (i + 1, j + 1) := by
    simp only [Grid.rank]
    nlinarith
  simp only [Fintype.card_fin]
  rw [hcard] at hc ⊢
  generalize (Assignment.one.block (Fin (G.rank (i, j + 1))) (Fin (G.rank (i + 1, j))))ᶜ.card = c at hc ⊢
  generalize G.rank (i + 1, j + 1) = a at hM h00 hc ⊢
  generalize G.rank (i, j) = b at h00 hc ⊢
  have hbM : b ≤ M := le_trans h00 hM
  have e1 : a * c ≤ M * (M + M) := Nat.mul_le_mul hM (by omega)
  have e2 : b * (a + b) ≤ M * (M + M) := Nat.mul_le_mul hbM (by omega)
  have e3 : b * b ≤ M * M := Nat.mul_le_mul hbM hbM
  have f1 := Nat.mul_le_mul_left e e1
  have f2 := Nat.mul_le_mul_left e e2
  have f3 := Nat.mul_le_mul_left e e3
  nlinarith

theorem sz_flips {G : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (he : 1 ≤ e) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → Un ι τ (ψ x : ℂ)) (M : ℕ) :
    ∀ (l : List (ℕ × ℕ)) (S : G.PiLocalization₂) (B : ℝ),
      (∀ x ∈ l, G.rank (x.1 + 1, x.2 + 1) ≤ M ∧ CondLE ϖ e (G.nu x.1 x.2) ∧ ¬ IsUnram (G.nu x.1 x.2) ∧
        ∀ u, Un ι τ (G.nu x.1 x.2 u : ℂ)) →
      CanFlip S.path l → (∀ X, IsOpen (S.level X : Set (GL (Fin (G.rank X)) k)) ∧ S.level X ≤ KO k _ ∧
        glLatCong (ϖ ^ e) (SplitFlip.stdLat k _) ≤ S.level X) →
      G.IsTensor ϖ e S.path S.tensor → (∀ z, Sz ι τ (S.tensor z) B) →
      ∀ z, Sz ι τ ((S.flips .one ψ ϖ e l).tensor z) ((resCard k : ℝ) ^ (6 * e * M ^ 2 * l.length) * B) := by
  intro l
  induction l with
  | nil =>
    intro S B _ _ _ _ hB z
    simpa [Grid.PiLocalization₂.flips] using hB z
  | cons x l ih =>
    intro S B hl hcan hlev hT hB z
    obtain ⟨hMx, hνx, hramx, hνUx⟩ := hl x (List.mem_cons_self ..)
    cases hcan with
    | cons hpass hcan' =>
      have hth : Edge.theta x.1 x.2 ∈ S.path := hpass.subset (by simp)
      have hex : Edge.ex x.1 x.2 ∈ S.path := hpass.subset (by simp)
      obtain ⟨hJo, hJK, hJC⟩ := hlev (x.1, x.2)
      have key := ih (S.flip .one ψ ϖ e x) ((resCard k : ℝ) ^ (6 * e * M ^ 2) * B)
        (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hcan'
        (by
          intro X
          rcases eq_or_ne X (x.1 + 1, x.2 + 1) with rfl | hne
          · simp only [Grid.PiLocalization₂.flip, Grid.flipLevel, Function.update_self]
            exact ⟨isOpen_KO, le_rfl, fun g hg => (GlobalTheory.FunObj.GivenAdm.mem_glLatCong.mp hg).1⟩
          · simp only [Grid.PiLocalization₂.flip, Grid.flipLevel, Function.update_of_ne hne]
            exact hlev X)
        (GlobalTheory.FunObj.isTensor_flipTensor hϖ hψc he hνx hJo hJK hth hex hT)
        (fun w => sz_flipTensor hϖ hψc habs hψ hMx hνx hramx hνUx hJo hJK hJC hth hex hT hB w) z
      have hlen : 6 * e * M ^ 2 * (x :: l).length = 6 * e * M ^ 2 * l.length + 6 * e * M ^ 2 := by
        simp only [List.length_cons]
        ring
      rw [hlen, pow_add, mul_assoc]
      exact key

end GlobalTheory.ConjSize

end
