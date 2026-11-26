module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelChartPoly

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

theorem chartMonomial_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ e k ∈ relSecM R y e := by
  classical
  have h := monomial_mem_relSecM R y (b := e) (fun q : Σ k, ι k => if q.2 = c q.1 then e q.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [pow_ite]

theorem coord_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) [DecidableEq K] :
    y p ∈ relSecM R y (Pi.single p.1 1) := by
  have h := chartMonomial_mem R y (Function.update c p.1 p.2) (Pi.single p.1 1)
  convert h using 1
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem generator_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) :
    y p / y ⟨p.1, c p.1⟩ * ∏ k, y ⟨k, c k⟩ ∈ relSecM R y (fun _ => 1) := by
  classical
  by_cases h0 : y ⟨p.1, c p.1⟩ = 0
  · simp [h0]
  have hW : ∏ k, y ⟨k, c k⟩ = (∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k) *
      ∏ k, y ⟨k, c k⟩ ^ (if k = p.1 then 0 else 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add]
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  have h1 : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
    rw [Finset.prod_eq_single p.1]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hmem := mul_mem_relSecM R y (coord_mem R y c p)
    (chartMonomial_mem R y c (fun k => if k = p.1 then 0 else 1))
  have hb : (Pi.single p.1 1 + fun k => if k = p.1 then 0 else 1 : K → ℕ) = fun _ => 1 := by
    funext k
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  rw [hb] at hmem
  rw [hW, h1, ← mul_assoc, div_mul_cancel₀ _ h0]
  exact hmem

end RelChartPoly

theorem RelChartPoly.proof : RelChartPoly.Statement := by
  intro K _ ι _ Ω _ R y c σ hσ
  have hW : ∀ M : ℕ, (∏ k, y ⟨k, c k⟩) ^ M ∈ relSecM R y (fun _ => M) := by
    intro M
    rw [← Finset.prod_pow]
    exact RelChartPoly.chartMonomial_mem R y c (fun _ => M)
  have hmul : ∀ {a b : ℕ} {x x' : Ω}, x ∈ relSecM R y (fun _ => a) → x' ∈ relSecM R y (fun _ => b) →
      x * x' ∈ relSecM R y (fun _ => a + b) := fun hx hx' => mul_mem_relSecM R y hx hx'
  induction hσ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨1, by simpa using RelChartPoly.generator_mem R y c p⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ r ?_
    simpa using hW 0
  | add x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    rw [add_mul]
    refine add_mem ?_ ?_
    · have := hmul hN (hW M)
      convert this using 1
      ring
    · have := hmul hM (hW N)
      rw [add_comm N M]
      convert this using 1
      ring
  | mul x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    have := hmul hN hM
    convert this using 1
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockChiCovolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Matrix SupBoundCount

noncomputable section

namespace BlockChiCovolume

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem gram_symm (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f k) (blockDeg d.k₀ n)) (k l : Fin r) :
    blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) l k =
      blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) k l := by
  rw [blockGram_eq d n f hf, blockGram_eq d n f hf]
  simp only [pairRe_comm]

theorem quad_nonneg (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f k) (blockDeg d.k₀ n)) (a : Fin r → ℝ) :
    0 ≤ a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) := by
  rw [gram_quad d n f hf]
  have h : ∀ z, 0 ≤ ‖comb f a z‖ ^ 2 / d.A.h z ^ (2 * n) := fun z =>
    div_nonneg (sq_nonneg _) ((even_two_mul n).pow_nonneg _)
  have h1 := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n)) fun x => h _
  have h2 := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n)) fun x => h _
  exact mul_nonneg (by norm_num) (add_nonneg h1 h2)

theorem entry_of_quad {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (hG : ∀ k l, G l k = G k l) (k l : Fin r) :
    G k l = ((Pi.single k 1 + Pi.single l 1) ⬝ᵥ (G *ᵥ (Pi.single k 1 + Pi.single l 1)) -
      Pi.single k 1 ⬝ᵥ (G *ᵥ Pi.single k 1) - Pi.single l 1 ⬝ᵥ (G *ᵥ Pi.single l 1)) / 2 := by
  simp [mulVec_add, dotProduct_add, add_dotProduct, hG l k]
  ring

theorem cast_single_add {r : ℕ} (k l : Fin r) :
    (fun j => (((Pi.single k 1 + Pi.single l 1 : Fin r → ℤ) j : ℤ) : ℝ)) = Pi.single k 1 + Pi.single l 1 := by
  funext j
  simp only [Pi.add_apply, Int.cast_add, Pi.single_apply]
  split_ifs <;> simp

theorem cast_single {r : ℕ} (k : Fin r) :
    (fun j => (((Pi.single k 1 : Fin r → ℤ) j : ℤ) : ℝ)) = Pi.single k 1 := by
  funext j
  simp only [Pi.single_apply]
  split_ifs <;> simp

end BlockChiCovolume


open BlockChiCovolume in
theorem BlockChiCovolume.proof : BlockChiCovolume.Statement := by
  intro D K _ _ ι _ Ω _ _ d n E hE r ψ hψ hnorm _ _
  have hex := exists_isSecBasisM d.y d.k₀ n
  rw [blockChi, dite_eq_left hex]
  have hb := hex.choose_spec
  generalize hex.choose = p at hb ⊢
  obtain ⟨hbf, hli, hspan⟩ := hb
  choose f hf hfb using hbf
  have hbeq : p.2 = fun j => map (Int.castRingHom ℚ) (f j) := funext hfb
  rw [hbeq] at hli hspan ⊢
  beta_reduce at hli hspan
  obtain ⟨w, hw⟩ : ∃ w : Fin p.1 → Ω, w = fun j => aeval d.y (map (Int.castRingHom ℚ) (f j)) := ⟨_, rfl⟩
  rw [← hw] at hli hspan
  have hEN : E = (Submodule.span ℤ (Set.range w)).toAddSubgroup := hE.trans hspan.symm
  let eN : E ≃+ Submodule.span ℤ (Set.range w) :=
    (AddEquiv.addSubgroupCongr hEN).trans (AddEquiv.refl _)
  let bE : Module.Basis (Fin p.1) ℤ E := (Module.Basis.span hli).map eN.symm.toIntLinearEquiv
  have hrange : LinearMap.range ψ.toIntLinearMap = imageLattice ψ := by
    ext v
    simp [imageLattice]
  let B : Module.Basis (Fin p.1) ℤ (imageLattice ψ) :=
    (bE.map (LinearEquiv.ofInjective ψ.toIntLinearMap hψ)).map (LinearEquiv.ofEq _ _ hrange)
  let ε : Fin p.1 → E := fun j => ⟨w j, hEN ▸ Submodule.subset_span ⟨j, rfl⟩⟩
  have hB : ∀ j, (B j : EuclideanSpace ℝ (Fin r)) = ψ (ε j) := by
    intro j
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.map_apply]
    show ψ (bE j) = ψ (ε j)
    congr 1
    apply Subtype.ext
    rw [Module.Basis.map_apply]
    have h : ((Module.Basis.span hli j : Submodule.span ℤ (Set.range w)) : Ω) = w j :=
      congrArg Subtype.val (Module.Basis.span_apply hli j)
    exact h
  set G := blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) with hG
  have key : ∀ m : Fin p.1 → ℤ,
      ‖ψ (∑ j, m j • ε j)‖ ^ 2 = (fun j => (m j : ℝ)) ⬝ᵥ (G *ᵥ fun j => (m j : ℝ)) := by
    intro m
    rw [hnorm _ (∑ j, m j • f j) (isMultiHomog_zsum f m hf), blockL2Norm_sum_eq_sqrt_gram d n f hf m,
      Real.sq_sqrt (quad_nonneg d n f hf _)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [ε, hw, SupBoundCount.aeval_map_int, map_sum]
  have hgram : Matrix.gram ℝ (fun i => (B i : EuclideanSpace ℝ (Fin r))) = G := by
    ext k l
    rw [entry_of_quad G (gram_symm d n f hf) k l, ← cast_single_add, ← cast_single, ← cast_single, ← key, ← key,
      ← key]
    simp only [Matrix.gram, of_apply, hB]
    simp [Pi.single_apply, add_smul, Finset.sum_add_distrib]
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
    ring
  have hdet : 0 ≤ G.det := hgram ▸ (Matrix.posSemidef_gram ℝ _).det_nonneg
  rw [covolume_eq_sqrt_det_gram (imageLattice ψ) B, hgram, Real.log_sqrt hdet]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSTopPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ScaledFSTopPos

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem geoNum_nonneg : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ), (∀ j k, 0 ≤ a j k) →
    0 ≤ geoNum n V a
  | 0, V, a, _ => by
    unfold geoNum
    split_ifs <;> positivity
  | n + 1, V, a, ha => by
    unfold geoNum
    split_ifs with h
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (ha _ _) (finsum_nonneg fun W => finsum_nonneg fun _ =>
        mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W _ fun j k => ha _ _))
    · exact le_rfl

theorem semipos_of_h_eq {P0 P : Ideal (MRing ι)} {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : A.h = B.h)
    (hA : IsSemipositiveRel P0 P A) : IsSemipositiveRel P0 P B := by
  unfold IsSemipositiveRel IsSmoothHerm at *
  rw [← h]
  exact hA

theorem semipos (P : Ideal (MRing ι)) : IsSemipositiveRel ⊥ P (scaledFSH ι) := by
  have hM : IsSemipositiveRel ⊥ P (constLine (ι := ι) 0) := by
    refine ⟨G5.isSmoothHerm_constLine 0, fun z _ w _ => ?_⟩
    simp [leviForm, constLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]
  have hfs : IsSemipositiveRel ⊥ P (fsH ι) :=
    semipos_of_h_eq (funext fun z => by simp [HermLine.zcomb])
      (PerturbSemipos.proof K ι ⊥ P _ 0 1 hM le_rfl zero_le_one)
  exact semipos_of_h_eq rfl (Mono.semipos_constShift hfs (-1))

theorem logNorm_fsH_nonpos (c : ∀ k, ι k) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    logNorm (fsH ι) (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (fun _ : K => (1 : ℕ)) k) z ≤ 0 := by
  have hpos := (fsH ι).pos z hz
  have hH : ∏ k, ‖z ⟨k, c k⟩‖ ≤ (fsH ι).h z := by
    have hfs : (fsH ι).h z = ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
      rw [fsH, GroundTheory.Heights₂.Heights.Inter.ofMetrics_fs_h]
      simp
    rw [hfs]
    refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ (c k))
  unfold logNorm
  apply Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
  rw [div_le_one hpos]
  simpa [map_prod, norm_prod] using hH

theorem step (II : IntersectionSystem) (hII : IsIntersectionSystem II) (hG : FSGeomDegPos.Statement) (n : ℕ)
    (hlow : ∀ W : Ideal (MRing ι), IsArithVar W n → IsHorizontal W → 0 ≤ II K ι W n (fun _ => scaledFSH ι))
    (P : Ideal (MRing ι)) (hP : IsArithVar P (n + 1)) :
    0 < II K ι P (n + 1) (fun _ => scaledFSH ι) := by
  classical
  have hF := hII K ι
  set L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun _ => scaledFSH ι with hLdef
  have hHs : IsSmoothHerm (scaledFSH ι) := (semipos (ι := ι) ⊥).1
  have hFs : IsSmoothHerm (fsH ι) := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have hCs : IsSmoothHerm (constLine (ι := ι) (-1)) := G5.isSmoothHerm_constLine (-1)
  have hLs : ∀ j, IsSmoothHerm (L j) := fun _ => hHs
  have e0 : (fun _ : Fin (n + 1) => scaledFSH ι) = Fin.snoc L ((fsH ι).tensor (constLine (-1))) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [L, scaledFSH]
  rw [e0, hF.2.1 P n L _ _ hP hLs hFs hCs]
  obtain ⟨c, hc⟩ : ∃ c : ∀ k, ι k, ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P :=
    ⟨fun k => (hP.2.1.2.2 k).choose, fun k => (hP.2.1.2.2 k).choose_spec⟩
  have hsH := GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_coordMonomial c (fun _ : K => (1 : ℕ))
  have hsP := GroundTheory.Heights₂.Heights.Inter.ThmIUnique.coordMonomial_not_mem hP.2.1.1 c hc (fun _ : K => (1 : ℕ))
  have hfa : ∀ k, (fsH ι).a k = ((fun _ : K => (1 : ℕ)) k : ℤ) := fun k => by simp [fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics]

  have hA : 0 ≤ II K ι P (n + 1) (Fin.snoc L (fsH ι)) := by
    rw [hF.2.2 P n L (fsH ι) _ _ hP hLs hFs hfa hsH hsP, recR_eq]
    refine sub_nonneg.mpr (le_trans ?_ (finsum_nonneg fun W => finsum_nonneg fun hW =>
      mul_nonneg (Nat.cast_nonneg _) ?_))
    · exact IntegralAgainstPositive.proof K ι P ⊥ n L _ bot_le (fun _ => semipos P)
        fun z hz => logNorm_fsH_nonpos c hz.1
    · split_ifs with hh
      · exact hlow W ((divSuppArith K ι P n (fsH ι) _ W hP ⟨_, hfa, hsH, hsP⟩ hW).1 hh) hh
      · exact mul_nonneg (by exact_mod_cast geoNum_nonneg n W _ fun j k => by simp [L, scaledFSH_a])
          (Real.log_natCast_nonneg _)

  have hone : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hca : ∀ k, (constLine (ι := ι) (-1)).a k = ((0 : K → ℕ) k : ℤ) := fun k => by
    simp [constLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]
  have hB : II K ι P (n + 1) (Fin.snoc L (constLine (-1))) = ptsIntegral P (pot L) (fun _ => 1) := by
    rw [hF.2.2 P n L _ 1 0 hP hLs hCs hca GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_one' hone, recR_eq]
    have hd : divSupp P (1 : MRing ι) = ∅ := by
      ext W
      simp only [divSupp, Ideal.span_singleton_one, le_top, sup_of_le_right, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => (h.1.1.ne_top (top_le_iff.mp h.1.2)).elim
    have hl : logNorm (constLine (ι := ι) (-1)) 1 = fun _ => -1 := by
      funext z
      simp [logNorm, constLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]
    rw [cycR, hd, finsum_mem_empty, arInt, hl, G5.ptsIntegral_const]
    simp only [zero_sub, neg_mul, one_mul, neg_neg]
    rfl
  have heq : ptsIntegral P (pot L) (fun _ => 1) = ptsIntegral P (pot fun _ : Fin n => fsH ι) (fun _ => 1) :=
    G5.ptsIntegral_eq_of_add_const P _ _ (fun j => ⟨1, fun z hz => by
      show Real.log ((scaledFSH ι).h z) = Real.log ((fsH ι).h z) + 1
      rw [show (1 : ℝ) = -(-1) by norm_num]
      exact G5.log_tensor_constLine (fsH ι) (-1) z hz.1⟩) _
  have hpos := hG K ι P n hP
  linarith
end ScaledFSTopPos

theorem ScaledFSTopPos.proof (hG : FSGeomDegPos.Statement) : ScaledFSTopPos.Statement := by
  intro K _ ι _ P d II hII hd hP
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  clear hd
  induction n generalizing P with
  | zero =>
    exact ScaledFSTopPos.step II hII hG 0
      (fun W hW _ => absurd hW (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι W)) P hP
  | succ m ih => exact ScaledFSTopPos.step II hII hG (m + 1) (fun W hW _ => (ih W hW).le) P hP

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelTorsionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelTorsionBound

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section Lemmas

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def blockWeight : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1

theorem weight_blockWeight (μ : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight (ι := ι)) μ = fun k => ∑ i, μ ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [blockWeight]
  · intro k' _ hk
    simp [blockWeight, Ne.symm hk]
  · simp


omit [DecidableEq K] in
theorem aeval_monomial_one (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) →₀ ℕ) :
    aeval y (monomial μ (1 : R)) = ∏ p, y p ^ μ p := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp

theorem relSecM_le_map (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) :
    relSecM R y b ≤ (weightedHomogeneousSubmodule R (blockWeight (ι := ι)) b).map (aeval y).toLinearMap := by
  rw [relSecM, Submodule.span_le]
  rintro _ ⟨μ, hμ, rfl⟩
  refine ⟨monomial (Finsupp.equivFunOnFinite.symm μ) 1, ?_, ?_⟩
  · refine (mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_monomial _ _ _ ?_)
    rw [weight_blockWeight]
    funext k
    simpa using hμ k
  · simp [aeval_monomial_one]


omit [Fintype K] [DecidableEq K] in
theorem exists_chart_le (N : ℕ) (μ : (Σ k, ι k) → ℕ)
    (h : ∀ k, Fintype.card (ι k) * N < ∑ i, μ ⟨k, i⟩) : ∃ c : ∀ k, ι k, ∀ k, N ≤ μ ⟨k, c k⟩ := by
  have hk : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra hn
    simp only [not_exists, not_le] at hn
    have hle := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hn i).le
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    exact absurd (h k) (not_lt.2 hle)
  exact ⟨fun k => (hk k).choose, fun k => (hk k).choose_spec⟩


open Classical in
theorem sum_chart (c : ∀ k, ι k) (N : ℕ) (k : K) : ∑ i, (if c k = i then N else 0) = N := by
  rw [Finset.sum_ite_eq]
  simp


open Classical in
theorem prod_chart (z : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (N : ℕ) :
    ∏ p : Σ k, ι k, z p ^ (if c p.1 = p.2 then N else 0) = (∏ k, z ⟨k, c k⟩) ^ N := by
  rw [Fintype.prod_sigma, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single (c k)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp


omit [DecidableEq K] in
theorem chart_pow_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (N : ℕ) :
    (∏ k, y ⟨k, c k⟩) ^ N ∈ relSecM R y (fun _ => N) := by
  classical
  rw [← prod_chart]
  exact monomial_mem_relSecM R y _ fun k => sum_chart c N k


omit [DecidableEq K] in
theorem exists_chart_factor (N : ℕ) (μ : (Σ k, ι k) → ℕ) (c : ∀ k, ι k) (hc : ∀ k, N ≤ μ ⟨k, c k⟩) :
    ∃ ν : (Σ k, ι k) → ℕ, (∀ k, ∑ i, ν ⟨k, i⟩ + N = ∑ i, μ ⟨k, i⟩) ∧
      ∀ z : (Σ k, ι k) → Ω, ∏ p, z p ^ μ p = (∏ p, z p ^ ν p) * (∏ k, z ⟨k, c k⟩) ^ N := by
  classical
  have hsplit : ∀ p : Σ k, ι k,
      μ p = (μ p - if c p.1 = p.2 then N else 0) + if c p.1 = p.2 then N else 0 := by
    intro p
    split_ifs with h
    · have hp : N ≤ μ p := by
        have := hc p.1
        rw [h] at this
        exact this
      omega
    · omega
  refine ⟨fun p => μ p - if c p.1 = p.2 then N else 0, fun k => ?_, fun z => ?_⟩
  · have hs : ∑ i, μ ⟨k, i⟩ = ∑ i, ((μ ⟨k, i⟩ - if c k = i then N else 0) + if c k = i then N else 0) :=
      Finset.sum_congr rfl fun i _ => hsplit ⟨k, i⟩
    rw [hs, Finset.sum_add_distrib, sum_chart]
  · rw [← prod_chart z c N, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add, ← hsplit p]


open Classical in
theorem comp_mul (R : Type*) [CommRing R] {d : K → ℕ} (m : K → ℕ) {G : MvPolynomial (Σ k, ι k) R}
    (hG : G ∈ weightedHomogeneousSubmodule R (blockWeight (ι := ι)) d) (A : MvPolynomial (Σ k, ι k) R) :
    weightedHomogeneousComponent blockWeight m (A * G) =
      if d ≤ m then weightedHomogeneousComponent blockWeight (m - d) A * G else 0 := by
  have h := DirectSum.coe_decompose_mul_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight (ι := ι))) (a := A) m hG
  rw [← decompose'_apply R blockWeight, ← decompose'_apply R blockWeight]
  exact h

def KilledAt (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (k0 : K) (c : ∀ k, ι k) (d : K → ℕ)
    (N : ℕ) (v : Ω) : Prop :=
  ∃ a : K → ℕ, a + Pi.single k0 1 = d + (fun _ => N) ∧
    ∃ g ∈ relSecM R y a, (∏ k, y ⟨k, c k⟩) ^ N * v = y ⟨k0, c0 k0⟩ * g

theorem KilledAt.mono {R : Subalgebra ℤ Ω} {y : (Σ k, ι k) → Ω} {c0 : ∀ k, ι k} {k0 : K} {c : ∀ k, ι k}
    {d : K → ℕ} {N N' : ℕ} {v : Ω} (h : KilledAt R y c0 k0 c d N v) (hN : N ≤ N') :
    KilledAt R y c0 k0 c d N' v := by
  obtain ⟨a, ha, g, hg, hgv⟩ := h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨(fun _ => m) + a, ?_, (∏ k, y ⟨k, c k⟩) ^ m * g, mul_mem_relSecM R y (chart_pow_mem R y c m) hg, ?_⟩
  · funext k
    have := congrFun ha k
    simp only [Pi.add_apply] at this ⊢
    omega
  · linear_combination (∏ k, y ⟨k, c k⟩) ^ m * hgv

def TorsionForm (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (k0 : K) (d : K → ℕ) (N : ℕ)
    (G : MvPolynomial (Σ k, ι k) R) : Prop :=
  G ∈ weightedHomogeneousSubmodule R (blockWeight (ι := ι)) d ∧
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → KilledAt R y c0 k0 c d N (aeval y G)

theorem TorsionForm.mono {R : Subalgebra ℤ Ω} {y : (Σ k, ι k) → Ω} {c0 : ∀ k, ι k} {k0 : K} {d : K → ℕ}
    {N N' : ℕ} {G : MvPolynomial (Σ k, ι k) R} (h : TorsionForm R y c0 k0 d N G) (hN : N ≤ N') :
    TorsionForm R y c0 k0 d N' G :=
  ⟨h.1, fun c hc => (h.2 c hc).mono hN⟩

theorem aeval_mul_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (k0 : K) {d a b : K → ℕ}
    {N : ℕ} (hN : 1 ≤ N) {G : MvPolynomial (Σ k, ι k) R} (hG : TorsionForm R y c0 k0 d N G)
    (ha : ∀ k, Fintype.card (ι k) * N < a k) (hab : a + d = b + Pi.single k0 1)
    {A : MvPolynomial (Σ k, ι k) R} (hA : A ∈ weightedHomogeneousSubmodule R (blockWeight (ι := ι)) a) :
    aeval y (A * G) ∈ (relSecM R y b).map (LinearMap.mulLeft R (y ⟨k0, c0 k0⟩)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [A.as_sum, Finset.sum_mul, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hwμ : Finsupp.weight blockWeight μ = a := hA (mem_support_iff.1 hμ)
  rw [weight_blockWeight] at hwμ
  obtain ⟨c, hc⟩ := exists_chart_le N μ fun k => by rw [congrFun hwμ k]; exact ha k
  obtain ⟨ν, hν, hfac⟩ := exists_chart_factor (Ω := Ω) N μ c hc
  have hval : aeval y (monomial μ (AddMonoidAlgebra.coeff A μ) * G) = algebraMap R Ω (AddMonoidAlgebra.coeff A μ) *
      ((∏ p, y p ^ ν p) * ((∏ k, y ⟨k, c k⟩) ^ N * aeval y G)) := by
    rw [show monomial μ (AddMonoidAlgebra.coeff A μ) = C (AddMonoidAlgebra.coeff A μ) * monomial μ 1 by rw [C_mul_monomial, mul_one],
      map_mul, map_mul, aeval_C, aeval_monomial_one, hfac y]
    ring
  by_cases hgood : ∀ k, y ⟨k, c k⟩ ≠ 0
  · obtain ⟨a', ha', g, hg, hgv⟩ := hG.2 c hgood
    have hdeg : (fun k => ∑ i, ν ⟨k, i⟩) + a' = b := by
      funext k
      have h1 := hν k
      have h2 := congrFun hwμ k
      have h3 := congrFun ha' k
      have h4 := congrFun hab k
      simp only [Pi.add_apply] at h3 h4 ⊢
      omega
    have hmem := mul_mem_relSecM R y (monomial_mem_relSecM R y ν fun k => rfl) hg
    rw [hdeg] at hmem
    refine ⟨AddMonoidAlgebra.coeff A μ • ((∏ p, y p ^ ν p) * g), Submodule.smul_mem _ _ hmem, ?_⟩
    rw [hval, hgv, LinearMap.mulLeft_apply, Algebra.smul_def]
    ring
  · simp only [not_forall, not_not] at hgood
    obtain ⟨k, hk⟩ := hgood
    have hprod : ∏ k, y ⟨k, c k⟩ = 0 := Finset.prod_eq_zero (Finset.mem_univ k) hk
    rw [hval, hprod, zero_pow (by omega), zero_mul, mul_zero, mul_zero]
    exact Submodule.zero_mem _

end Lemmas

theorem proof : RelTorsionBound.Statement := by
  intro K _ _ ι _ Ω _ R hR y c0 hc0 k0
  classical
  have := hR
  let s : Set (MvPolynomial (Σ k, ι k) R) := {G | ∃ d N, TorsionForm R y c0 k0 d N G}
  obtain ⟨t, hts, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset s).1 (IsNoetherian.noetherian (R := MvPolynomial (Σ k, ι k) R) _)
  have hs : ∀ G ∈ s, ∃ d N, TorsionForm R y c0 k0 d N G := fun G h => h
  choose! dG NG hdN using hs
  set N₀ := t.sup NG + 1 with hN₀
  have hT : ∀ G ∈ t, TorsionForm R y c0 k0 (dG G) N₀ G := fun G hG =>
    (hdN G (hts hG)).mono (by have := Finset.le_sup (f := NG) hG; omega)
  refine ⟨∑ k, (Fintype.card (ι k) * N₀ + 1) + ∑ G ∈ t, ∑ k, dG G k, fun b hb f hf hyp => ?_⟩
  obtain ⟨F, hF, rfl⟩ := relSecM_le_map R y _ hf
  choose! D g hg hgf using hyp
  have hFs : F ∈ s := by
    refine ⟨b + Pi.single k0 1, Finset.univ.sup D, hF, fun c hc => ?_⟩
    refine KilledAt.mono ⟨b + fun _ => D c, ?_, g c, hg c hc, hgf c hc⟩ (Finset.le_sup (Finset.mem_univ c))
    funext k
    simp only [Pi.add_apply]
    omega
  have hFt : F ∈ Submodule.span (MvPolynomial (Σ k, ι k) R) (t : Set (MvPolynomial (Σ k, ι k) R)) :=
    hspan ▸ Submodule.subset_span hFs
  obtain ⟨A, -, hA⟩ := Submodule.mem_span_finset.1 hFt
  have hFsum : F = ∑ G ∈ t, weightedHomogeneousComponent blockWeight (b + Pi.single k0 1) (A G * G) := by
    have h1 : weightedHomogeneousComponent blockWeight (b + Pi.single k0 1) F = F :=
      IsWeightedHomogeneous.weightedHomogeneousComponent_same ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hF)
    rw [← h1]
    conv_lhs => rw [← hA]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [smul_eq_mul]
  suffices h : aeval y F ∈ (relSecM R y b).map (LinearMap.mulLeft R (y ⟨k0, c0 k0⟩)) by
    obtain ⟨g', hg', hgx⟩ := h
    exact ⟨g', hg', by simpa using hgx.symm⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hFsum, map_sum]
  refine Submodule.sum_mem _ fun G hG => ?_
  rw [comp_mul _ _ (hT G hG).1]
  split_ifs with hle
  · refine aeval_mul_mem R y c0 k0 (by omega) (hT G hG) (fun k => ?_) (tsub_add_cancel_of_le hle)
      (weightedHomogeneousComponent_mem _ _ _)
    have h1 : Fintype.card (ι k) * N₀ + 1 ≤ ∑ k, (Fintype.card (ι k) * N₀ + 1) :=
      Finset.single_le_sum (f := fun k => Fintype.card (ι k) * N₀ + 1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    have h2 : dG G k ≤ ∑ k, dG G k :=
      Finset.single_le_sum (f := fun k => dG G k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h3 : ∑ k, dG G k ≤ ∑ G ∈ t, ∑ k, dG G k :=
      Finset.single_le_sum (f := fun G => ∑ k, dG G k) (fun _ _ => Nat.zero_le _) hG
    have h4 := hb k
    have h5 := hle k
    simp only [Pi.sub_apply, Pi.add_apply] at h5 ⊢
    omega
  · simp

end RelTorsionBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LeLimsupDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter

noncomputable section

namespace ArithmeticVolumeBigDimensionOne

theorem le_limsup_div {u : ℕ → ℝ} {T C C' : ℝ}
    (hlo : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * T - C ≤ u n) (hup : ∀ n : ℕ, u n ≤ C' * ((n : ℝ) + 1)) :
    T ≤ limsup (fun n : ℕ => u n / n) atTop := by
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => u n / n) := by
    refine isBoundedUnder_of_eventually_le (a := 2 * |C'|) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ (by linarith)]
    calc u n ≤ C' * ((n : ℝ) + 1) := hup n
      _ ≤ |C'| * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ 2 * |C'| * n := by nlinarith [abs_nonneg C']
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have key : T - ε ≤ limsup (fun n : ℕ => u n / n) atTop := by
    refine le_limsup_of_frequently_le (Eventually.frequently ?_) hb
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
    rw [le_div_iff₀ (by linarith)]
    have hC : C < n * ε := (div_lt_iff₀ hε).mp (hN.trans_le hnN)
    have hl := hlo n hn1
    nlinarith
  linarith

end ArithmeticVolumeBigDimensionOne

theorem ArithmeticVolumeBigDimensionOne.proof (hP : PackingStatement) (hL : CurveSmallCountLower.Statement) :
    ArithmeticVolumeBigDimensionOne.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII har hb hP0 hs hnef hc
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII har hb hs.1 hc
  obtain ⟨-, C', hC'⟩ := hP K ι Ω y 0 A (chartLat y A.a) har hb hs.1
    (fun τ => SmallSectionPointHeight.chartLat_le_chartLatNm y A.a τ)
  have e : arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 0 =
      limsup (fun n : ℕ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n / n) atTop := by
    unfold arVolP
    congr 1
    simp
  rw [e]
  exact ArithmeticVolumeBigDimensionOne.le_limsup_div hC (fun n => by simpa using hC' n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockDatum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

noncomputable section

namespace PowerBlockDatum

theorem exists_coord_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := hV.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem isMultiHomogIdeal_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) :=
  ⟨{1}, fun f hf => ⟨fun _ => 0, by
    rw [Set.mem_singleton_iff.mp hf]
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp⟩, Ideal.span_singleton_one.symm⟩

end PowerBlockDatum


open PowerBlockDatum in
theorem PowerBlockDatum.proof (hE : ResExistsStatement) (hV : ResVolume.Statement)
    (hVer : PowerBlockVeronese.Statement) (hBir : PowerHeightsirational.Statement)
    (hAr : PowerBlockArith.Statement) (hMet : PowerBlockMetric.Statement)
    (hMeas : PowerBlockMeasure.Statement) : PowerBlockDatum.Statement := by
  intro K _ _ ι _ Ω _ _ y D A P0 hD hArith hBiry hSG hConj
  obtain ⟨q, w, hw, hgen, -⟩ := hSG.gen
  obtain ⟨m₁, hm₁⟩ := hVer K ι Ω y A.a q w (exists_coord_ne_zero hArith) hw hgen
  obtain ⟨m₂, hm₂⟩ := hBir K ι Ω y D A.a q w hD hArith hBiry hw hgen hSG.deg_pos
  obtain ⟨N, v, hspan, hgenv, hver⟩ := hm₁ (max (max m₁ m₂) 1) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hbir := hm₂ (max (max m₁ m₂) 1) (le_trans (le_max_right _ _) (le_max_left _ _)) N v hspan
  have hv : ∀ j, v j ∈ chartLat y A.a (max (max m₁ m₂) 1) := fun j =>
    hspan ▸ AddSubgroup.subset_closure (Set.mem_range_self j)
  have hArv := hAr K ι Ω y D A.a _ N v hArith hv hgenv
  obtain ⟨B, P0', hBa, hBconj, hP0', hBsemi, hrel⟩ :=
    hMet K ι Ω y A P0 _ N v hSG.normalForm_baseLattice_le_dualSpan_sup_line hSG.semipos hConj hv hgenv
  obtain ⟨J', -, -, -, ⟨R'⟩⟩ := hE (Option K) (addIdx ι N) (mCoordIdeal (addBlock y v)) ⊤ D hArv
    isMultiHomogIdeal_top (fun h => hArv.2.1.1.ne_top (top_le_iff.mp h))
  let _ : MeasurableSpace R'.toAnRes.X := borel _
  have _ : BorelSpace R'.toAnRes.X := ⟨rfl⟩
  obtain ⟨dV, hdV⟩ := hV (Option K) (addIdx ι N) _ _ D R'.toAnRes hArv
  obtain ⟨μ, hμp, hμn, hμd, hμ⟩ :=
    hMeas K ι Ω y A _ N D v B J' R'.toAnRes dV hSG.semipos.1 hBsemi.1 hBa hdV hv hgenv hrel
  let d : HSMBlockDatum D (Option K) (addIdx ι N) Ω :=
    { y := addBlock y v, k₀ := none, A := B, P0 := P0', J := J', R := R'.toAnRes, meas := borel _,
      borel := ⟨rfl⟩, dV := dV, one_le := hD, arith := hArv, birat := hbir, deg := hBa, conjInv := hBconj,
      normalForm_baseLattice_le_dualSpan_sup_line := hP0', semipos := hBsemi, vol := hdV }
  exact ⟨max (max m₁ m₂) 1, N, v, d, μ, le_max_right _ _, rfl, rfl, hv, hgenv, hrel,
    eventually_atTop.2 ⟨1, fun n hn => hver n hn⟩, hμp, hμn, hμd, fun q f hf => hμ q f hf⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGraphImage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

theorem VeroneseGraphImage.proof : VeroneseGraphImage.Statement := by
  intro D

  let f₀ : MRing (GlobalTheory (Fin (D + 1))) →+* Veronese.Fld D :=
    (Veronese.polyMap D).comp
      (rename (fun p : Σ _ : Unit, Fin (D + 1) => p.2) : MvPolynomial _ ℤ →ₐ[ℤ] _).toRingHom
  have hf₀ : Function.Injective f₀ := by
    refine (Veronese.polyMap_injective D).comp (rename_injective _ ?_)
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases h
    rfl
  have hf₀X : ∀ i, f₀ (X ⟨(), i⟩) = Veronese.t D i := by
    intro i
    simp [f₀, Veronese.polyMap, Veronese.t]
  let P : Ideal (MRing (GlobalTheory (Fin (D + 1)))) := ⊥
  let φ : MRing (GlobalTheory (Fin (D + 1))) ⧸ P →+* Veronese.Fld D :=
    Ideal.Quotient.lift P f₀ fun a ha => by
      rw [Ideal.mem_bot] at ha
      simp [ha]
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a ha => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a = 0 := hf₀ (by rw [map_zero]; exact (Ideal.Quotient.lift_mk _ _ _).symm.trans ha)
    rw [this, map_zero]

  let ψ : Polynomial (Veronese.Fld D) →+* MvPolynomial Unit (Veronese.Fld D) :=
    Polynomial.eval₂RingHom C (X ())
  let ev : MvPolynomial Unit (Veronese.Fld D) →+* Polynomial (Veronese.Fld D) :=
    eval₂Hom Polynomial.C fun _ => Polynomial.X
  have hev : ∀ p, ev (ψ p) = p := by
    have h : ev.comp ψ = RingHom.id _ := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [ψ, ev]
      · simp [ψ, ev]
    exact fun p => RingHom.congr_fun h p
  let G : MRing (GlobalTheory (Veronese.Idx D)) →+* MvPolynomial Unit (Veronese.Fld D) :=
    (MvPolynomial.map φ).comp ((graphMap P (Veronese.forms D)).comp
      (rename (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) :
        MRing (GlobalTheory (Veronese.Idx D)) →ₐ[ℤ] _).toRingHom)
  have hG : ∀ f, G f = ψ (coneMap ℤ (Veronese.x D) f) := by
    have h : G = ψ.comp (coneMap ℤ (Veronese.x D)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro n
        exact RingHom.congr_fun
          (RingHom.ext_int (G.comp C) ((ψ.comp (coneMap ℤ (Veronese.x D)).toRingHom).comp C)) n
      · rintro ⟨u, q⟩
        cases u
        simp only [G, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          rename_X]
        rw [show (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D)) ⟨(), q⟩) = ⟨Sum.inr (), q⟩ from rfl]
        rw [graphMap, eval₂Hom_X']
        simp only [map_mul, map_C, map_X, coneMap, aeval_X]
        rw [show φ (Ideal.Quotient.mk P (Veronese.forms D ⟨(), q⟩)) = Veronese.x D ⟨(), q⟩ from by
          rw [Ideal.Quotient.lift_mk]
          simp only [Veronese.forms, map_mul, hf₀X, Veronese.x]]
        simp [ψ]
    exact fun f => RingHom.congr_fun h f
  ext f
  show rename inrV f ∈ RingHom.ker (graphMap P (Veronese.forms D)) ↔
    f ∈ RingHom.ker (coneMap ℤ (Veronese.x D))
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    have h0 : G f = 0 := by
      show MvPolynomial.map φ (graphMap P (Veronese.forms D) (rename inrV f)) = 0
      rw [h, map_zero]
    rw [hG] at h0
    rw [← hev (coneMap ℤ (Veronese.x D) f), h0, map_zero]
  · intro h
    apply MvPolynomial.map_injective φ hφ
    rw [map_zero]
    show G f = 0
    rw [hG, h, map_zero]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end
