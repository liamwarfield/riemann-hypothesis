module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpMMLaw
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinTermExpansion
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.UnfoldingIntegral

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FrameDil
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dM {R : Type} [CommRing R] {n : ℕ} (i₀ : Fin n) (x y : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  1 + (x - 1) • Matrix.single (Sum.inl i₀) (Sum.inl i₀) 1 + (y - 1) • Matrix.single (Sum.inr i₀) (Sum.inr i₀) 1

theorem dM_apply {R : Type} [CommRing R] {n : ℕ} (i₀ : Fin n) (x y : R) (u v : Fin n ⊕ Fin n) :
    dM i₀ x y u v = if u = v then (if u = Sum.inl i₀ then x else if u = Sum.inr i₀ then y else 1) else 0 := by
  simp only [dM, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.one_apply, smul_eq_mul]
  rcases u with u | u <;> rcases v with v | v <;> simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
    false_and, if_false, mul_zero, add_zero, and_self] <;> by_cases h : u = v <;> by_cases h' : u = i₀ <;> subst_vars <;>
    simp_all [eq_comm]

theorem dM_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (i₀ : Fin n) (f : R →+* S) (x y : R) :
    (dM i₀ x y).map f = dM i₀ (f x) (f y) := by
  ext u v
  rw [Matrix.map_apply, dM_apply, dM_apply]
  split_ifs <;> simp

theorem rEx (d : SD σ) (w : InfinitePlace F) : ∃ r : ℝ → GroundTheory.Global.IdeleGroup F,
    (∀ τ τ', r (τ + τ') = r τ * r τ') ∧ r 0 = 1 ∧
    (∀ τ, (GroundTheory.Global.IdeleGroup.ideleModule F (r τ) : ℝ) = Real.exp τ) ∧
    (∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ)) ∧
    (∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1) ∧
    (∀ τ, finOne F * (r τ : AF F) = finOne F) := by
  have := d.cm.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let u : ℝ → ℝˣ := fun τ => ⟨Real.exp τ, Real.exp (-τ), by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero],
    by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]⟩
  let r : ℝ → GroundTheory.Global.IdeleGroup F := fun τ => GroundTheory.Global.IdeleGroup.infiniteEmbedding w (Units.map e.symm.toMonoidHom (u τ))
  have hu : ∀ τ τ', u (τ + τ') = u τ * u τ' := fun τ τ' => Units.ext (Real.exp_add τ τ')
  have hu0 : u 0 = 1 := Units.ext Real.exp_zero
  have hr1 : ∀ τ, ((r τ : AF F)).1 = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (e.symm (Real.exp τ)) := fun τ => rfl
  have hr2 : ∀ τ, ((r τ : AF F)).2 = 1 := fun τ => rfl
  have hee : ∀ x : ℝ, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (e.symm x) = x := fun x => e.apply_symm_apply x
  have hext : ∀ τ, InfinitePlace.Completion.extensionEmbedding w (e.symm (Real.exp τ)) = (Real.exp τ : ℂ) := by
    intro τ
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hee]
  refine ⟨r, fun τ τ' => by simp only [r, hu, map_mul], by simp only [r, hu0, map_one], fun τ => ?_, fun τ => ?_,
    fun τ w' hw' => ?_, fun τ => ?_⟩
  · rw [GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding, hw.mult_eq_one, pow_one]
    show ‖e.symm (Real.exp τ)‖ = _
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), hee,
      Real.norm_of_nonneg (Real.exp_pos τ).le]
  · rw [St.piInf_smul, map_one, mul_one, hr1, GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_same]
    exact hext τ
  · rw [St.piInf_smul, map_one, mul_one, hr1, GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hw', map_one]
  · refine Prod.ext ?_ ?_
    · show (0 : Ainf F) * _ = 0
      rw [zero_mul]
    · show (1 : Af F) * (r τ : AF F).2 = 1
      rw [hr2, mul_one]

theorem isDil_inv {n : ℕ} {X : Fin n → ℝ} {τ : ℝ} {y : GR n} (h : IsDil X τ y) : IsDil X (-τ) y⁻¹ := by
  unfold IsDil at *
  set M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := Matrix.fromBlocks (Matrix.diagonal fun j => (Real.exp (-τ * X j) : ℂ)) 0 0
    (Matrix.diagonal fun j => (Real.exp (-(-τ * X j)) : ℂ)) with hM'
  have h1 : mR y⁻¹ * mR y = 1 := by
    show ((y⁻¹ : GR n) : GL (Fin n ⊕ Fin n) ℂ).1 * (y : GL (Fin n ⊕ Fin n) ℂ).1 = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have h2 : mR y * M' = 1 := by
    rw [h, hM', Matrix.fromBlocks_multiply]
    simp only [Matrix.diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [← Matrix.fromBlocks_one]
    congr 1 <;> (ext i j; simp only [Matrix.diagonal_apply, Matrix.one_apply]; split_ifs <;>
      simp [← Complex.exp_add])
  calc mR y⁻¹ = mR y⁻¹ * (mR y * M') := by rw [h2, Matrix.mul_one]
    _ = M' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem frame_dil (d : SD σ) (R : RD d) (w : InfinitePlace F) (r : ℝ → GroundTheory.Global.IdeleGroup F)
    (hw : ∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ))
    (ho : ∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1)
    (hf : ∀ τ, finOne F * (r τ : AF F) = finOne F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = dM i₀ ((r τ : AF F) • (1 : AE F E)) ((r (-τ) : AF F) • (1 : AE F E)) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have hC : Matrix.fromBlocks (Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ)) 0 0
      (Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)) = dM i₀ (Real.exp τ : ℂ) (Real.exp (-τ) : ℂ) := by
    ext u v
    rw [dM_apply]
    rcases u with u | u <;> rcases v with v | v <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.diagonal_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, Matrix.zero_apply] <;>
      by_cases h : u = v <;> by_cases h' : u = i₀ <;> subst_vars <;> simp_all [Pi.single_apply]
  refine Place.cw_ext d (fun w' => ?_) ?_
  · by_cases hw' : w' = w
    · subst hw'
      rw [R.cw_iota_pf w' y, hy, dZ_conj_diag hζ0, hC, SD.cw, dM_map, hw, hw]
    · rw [R.off_w w w' y hw', SD.cw, dM_map, ho τ w' hw', ho (-τ) w' hw']
      ext u v
      rw [dM_apply, Matrix.one_apply]
      split_ifs <;> rfl
  · rw [R.off_f w y]
    ext u v
    rw [Matrix.smul_apply, Matrix.smul_apply, dM_apply, Matrix.one_apply]
    have e : ∀ t, finOne F • ((r t : AF F) • (1 : AE F E)) = finOne F • (1 : AE F E) := fun t => by
      rw [smul_smul, hf]
    split_ifs <;> simp [e]

theorem par_dil (d : SD σ) (R : RD d) (w : InfinitePlace F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    ∃ t, IsPar (R.ι w y) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (2 * τ) ∧
      (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1 := by
  obtain ⟨t0, ht0⟩ := d.ok.frame.2
  set A : Matrix (Fin d.n) (Fin d.n) ℂ := Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ) with hAdef
  set D : Matrix (Fin d.n) (Fin d.n) ℂ := Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)
  have hy' : mR y = Matrix.fromBlocks A 0 0 D := hy
  obtain ⟨-, hA, -, hoA, hfA, -⟩ := R.frame_diag w y A D hy'
  have h21 : (mR y).toBlocks₂₁ = 0 := by rw [hy', Matrix.toBlocks_fromBlocks₂₁]
  obtain ⟨t, ht, habs⟩ := KSplitP.iota_isPar d R w y h21
  have hdetA : A.det = (Real.exp τ : ℂ) := by
    rw [hAdef, Matrix.det_diagonal, Finset.prod_eq_single i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  refine ⟨t, ht, ?_, ?_⟩
  · rw [habs, hy', Matrix.toBlocks_fromBlocks₁₁, hdetA, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos τ).le,
      ← Real.exp_nat_mul]
    norm_num
  · have ht1 := ((kunf.isPar_frame ht0 (R.ι w y) t).1 ht).2
    set P := (inFrame d.b (R.ι w y)).toBlocks₁₁ with hP
    have hcw : ∀ w', d.cw w' t.1 = d.cw w' (incM F t0.1) * d.cw w' P * d.cw w' (incM F (t0⁻¹).1) := by
      intro w'; rw [ht1]; simp only [SD.cw, Matrix.map_mul]
    have hI : incM F t0.1 * incM F (t0⁻¹).1 = 1 := by
      rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
    have hT : ∀ w', d.cw w' (incM F t0.1) * d.cw w' (incM F (t0⁻¹).1) = 1 := by
      intro w'; rw [SD.cw, SD.cw, ← Matrix.map_mul, hI, Matrix.map_one _ (map_zero _) (map_one _)]
    have ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1 := fun w' h => by rw [hcw, (hoA w' h).1, Matrix.mul_one, hT]
    have hf : finOne F • t.1 = finOne F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
      rw [ht1, ← Matrix.smul_mul, ← Matrix.mul_smul, hfA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hI]
    have hdet : (d.cw w t.1).det = (Real.exp τ : ℂ) := by
      have hXY := congrArg Matrix.det (hT w)
      rw [Matrix.det_mul, Matrix.det_one] at hXY
      rw [hcw, Matrix.det_mul, Matrix.det_mul, hA, hdetA]
      linear_combination ((Real.exp τ : ℝ) : ℂ) * hXY
    rw [RD.chi_det (d := d) w t _ rfl ho hf, hdet]
    exact d.chiW_pos w _ (Real.exp_pos τ)

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ImportsAlt
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

variable {R L}

theorem unf (R : RD d) {f : d.G → ℂ} {s₁ : ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖)
    {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (habs : ∀ x, (∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖))) ∧
      Summable fun q : Cs d => ∫ p, ‖kq L f s₁ z nb T uM (rep q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    {w₁ : d.G} {cM : (Fin L.n → AE F E) × AF F → d.G} {κ : Measure ((Fin L.n → AE F E) × AF F)} {δ : E}
    (h : Hyp L nb uM nb' w₁ cM δ) (hcM : Continuous cM) (hκ : κ.IsAddHaarMeasure) :
    ∃ K : ℂ, ∀ x, sec2 L f s₁ z nb lam 𝓖 T uM ν 𝓤 x = K * ∑' q' : Cs L.sd, ∫ β in 𝓖',
      (∫ c, phz d f s₁ z (w₁ * (cM c * (L.j (rep q' * nb' β) * x))) ∂κ) * th' (d := d) T' β ∂lam' := by
  classical
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (Cs d) := Quotient.countable
  have : Countable (rat2 σ L.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ L.Y
  have : Countable (Cs L.sd) := Quotient.countable
  have : Countable (Crat L) := countable_crat
  have : ν.IsAddHaarMeasure := hU.2.1
  have : lam.IsAddHaarMeasure := hc.2.1
  have : lam'.IsAddHaarMeasure := hc'.2.1
  have hψc : Continuous d.B.ψ := d.ok.good.std.1
  obtain ⟨P, hP, -⟩ := pEquiv h
  obtain ⟨cP, hcP0, hcPt, hPc⟩ := lam_map (lam := lam) (ν := ν) (lam' := lam') P
  obtain ⟨cK, hcK0, hcKt, hκeq⟩ := kap_eq (ν := ν) (κ := κ)
  obtain ⟨𝓐, h𝓐, h𝓐0, h𝓐t⟩ := exists_fd_fA (F := F)
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hU.2.2.2])
  have : IsFiniteMeasure (lam'.restrict 𝓖') := isFiniteMeasure_restrict.2 (by simp [hc'.2.2.2])
  have : IsFiniteMeasure ((lamA F).restrict 𝓐) := isFiniteMeasure_restrict.2 h𝓐t
  obtain ⟨e, he⟩ := non_lagrangian_cosets_bijection h
  refine ⟨(cP.toReal : ℂ) * ((cK.toReal : ℂ))⁻¹, fun x => ?_⟩
  have hΦc : Continuous (phz d f s₁ z) := ComplexParameterFamilyContinuity.continuous_phz d hf.cont s₁ z
  obtain ⟨hi, hs⟩ := habs x
  obtain ⟨e1, fin1⟩ := section_sum_integral_expand (L := L) (nb := nb) (uM := uM) hU.2.2.2 hc.2.2.2 x hi hs
  have e2 := coordsC (R := R) h hc hU hc' hT h𝓐 hP hPc (E2 L (phz d f s₁ z)) (fun r hr hx g => eisenstein_rational_invariant hf z hr hx g) x

  set μO := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμO
  set μI := (ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)) with hμI
  set μN := (lam'.restrict 𝓖').prod μI with hμN
  have hnb' : Continuous nb' := kunf.continuous_nb hc'.1
  have hnew : Continuous fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) =>
      sM R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x)) := by
    refine ((continuous_sM' (R := R) (L := L)).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul
      ((hcM.comp ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp (continuous_snd.comp continuous_snd)))).mul
        (((L.cont.comp (hnb'.comp continuous_fst))).mul continuous_const))
  have hth' : Continuous fun β : nA σ L.Y L.b => th' (d := d) T' β := continuous_th' T'
  let G : (Σ _ : Cs L.sd, Crat L) → nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) → ℂ :=
    fun y p => phz d f s₁ z (w₁ * (cM y.2.1 * (L.j (rep y.1) * (sM R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x)))))) *
      th' (d := d) T' p.1
  have hGc : ∀ y, Continuous (G y) := fun y =>
    (hΦc.comp (continuous_const.mul (continuous_const.mul (continuous_const.mul hnew)))).mul (hth'.comp continuous_fst)

  have fin2 : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂μN < ⊤ := by
    have hE := coordsE (R := R) h hc hU hc' hT h𝓐 hP hPc
      (fun g => ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * g)‖ₑ)
      (Measurable.tsum fun q => (hΦc.comp (continuous_const.mul continuous_id)).enorm.measurable)
      (fun r hr hx g => eisenstein_norm_sum_rational_invariant hf z hr hx g) x
    have l1 : ∫⁻ p, (∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * (nb p.2 * (uM p.1 * x)))‖ₑ) *
        ‖th T p.2‖ₑ ∂μO < ⊤ := by
      refine lt_of_eq_of_lt ?_ fin1
      refine lintegral_congr fun p => ?_
      rw [← ENNReal.tsum_mul_right]
      exact tsum_congr fun q => (enorm_mul _ _).symm
    rw [hE] at l1
    have l2 : ∫⁻ p, (∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)},
        ‖phz d f s₁ z (rep q.1 * (sM R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))))‖ₑ) * ‖th' (d := d) T' p.1‖ₑ
        ∂μN < ⊤ := by
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [hcon, ENNReal.mul_top hcP0] at l1
      exact lt_irrefl _ l1
    refine lt_of_eq_of_lt (lintegral_congr fun p => ?_) l2
    rw [(eisenstein_term_expansion h hf z he _).2, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun y => enorm_mul _ _

  have hGm : ∀ y, AEMeasurable (fun p => ‖G y p‖ₑ) μN := fun y => (hGc y).enorm.measurable.aemeasurable
  have hGlt : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂μN < ⊤ := fun y =>
    lt_of_le_of_lt (lintegral_mono fun p => ENNReal.le_tsum (f := fun y => ‖G y p‖ₑ) y) fin2
  have hGi : ∀ y, Integrable (G y) μN := fun y => ⟨(hGc y).aestronglyMeasurable, hGlt y⟩
  have hGs : Summable fun y => ∫ p, ‖G y p‖ ∂μN := by
    have h1 : ∀ y, ∫ p, ‖G y p‖ ∂μN = (∫⁻ p, ‖G y p‖ₑ ∂μN).toReal := fun y =>
      integral_norm_eq_lintegral_enorm (hGi y).aestronglyMeasurable
    simp_rw [h1]
    refine ENNReal.summable_toReal ?_
    rw [← lintegral_tsum hGm]
    exact fin2.ne

  have e3 : ∫ p, E2 L (phz d f s₁ z) (sM R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * th' (d := d) T' p.1 ∂μN =
      ∑' y, ∫ p, G y p ∂μN := by
    rw [(hasSum_integral_of_summable_integral_norm hGi hGs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [G]
    rw [(eisenstein_term_expansion h hf z he _).1, tsum_mul_right]
  have hsI : Summable fun y => ∫ p, G y p ∂μN := hGs.of_norm_bounded (fun y => norm_integral_le_integral_norm _)
  rw [hsI.tsum_sigma] at e3

  have hκ' : ∀ g : (Fin L.n → AE F E) × AF F → ℂ, ∫ c, g c ∂(ν.prod (lamA F)) = ((cK.toReal : ℂ))⁻¹ * ∫ c, g c ∂κ := by
    intro g
    rw [hκeq, integral_smul_measure, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hcK0, hcKt⟩)
  have e4 : ∀ q' : Cs L.sd, ∑' c₀ : Crat L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ((cK.toReal : ℂ))⁻¹ *
      ∫ β in 𝓖', (∫ c, phz d f s₁ z (w₁ * (cM c * (L.j (rep q' * nb' β) * x))) ∂κ) * th' (d := d) T' β ∂lam' := by
    intro q'
    have hi' : ∀ c₀ : Crat L, Integrable (G ⟨q', c₀⟩) μN := fun c₀ => hGi _
    have hs' : Summable fun c₀ : Crat L => ∫ p, ‖G ⟨q', c₀⟩ p‖ ∂μN := hGs.sigma_factor q'
    obtain ⟨-, hex⟩ := PositivityTheory.SiegelWeilFormula.Act.exch (μ := lam'.restrict 𝓖') (m := μI) (fun c₀ : Crat L => G ⟨q', c₀⟩) hi' hs'
    have hpr : ∀ c₀ : Crat L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ∫ β, ∫ v, G ⟨q', c₀⟩ (β, v) ∂μI ∂(lam'.restrict 𝓖') :=
      fun c₀ => integral_prod _ (hi' c₀)
    simp_rw [hpr]
    rw [← hex, ← integral_const_mul]
    refine integral_congr_ae ?_

    have hmq : Measurable fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) =>
        ∑' c₀ : Crat L, ‖G ⟨q', c₀⟩ p‖ₑ := Measurable.tsum fun c₀ => (hGc _).enorm.measurable
    have hfinq : ∫⁻ p, ∑' c₀ : Crat L, ‖G ⟨q', c₀⟩ p‖ₑ ∂μN < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono fun p => ?_) fin2
      exact (ENNReal.le_tsum (f := fun q'' => ∑' c₀ : Crat L, ‖G ⟨q'', c₀⟩ p‖ₑ) q').trans
        (ENNReal.tsum_sigma' (fun y => ‖G y p‖ₑ)).symm.le
    rw [hμN, lintegral_prod _ hmq.aemeasurable] at hfinq
    have hae := ae_lt_top (hmq.lintegral_prod_right') hfinq.ne
    filter_upwards [hae] with β hβ
    have hG' : ∀ v, ∑' c₀ : Crat L, G ⟨q', c₀⟩ (β, v) = (∑' c₀ : Crat L,
        phz d f s₁ z (w₁ * (cM c₀.1 * (L.j (rep q') * (sM R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))) *
          th' (d := d) T' β := fun v => by simp only [G]; rw [tsum_mul_right]
    simp_rw [hG']
    rw [integral_mul_const]
    have hjj : L.j (rep q') * (L.j (nb' β) * x) = L.j (rep q' * nb' β) * x := by rw [map_mul, mul_assoc]
    by_cases hθ : th' (d := d) T' β = 0
    · rw [hθ, mul_zero, mul_zero, mul_zero]
    · have hθe : ‖th' (d := d) T' β‖ₑ ≠ 0 := enorm_ne_zero.2 hθ
      have hl : ∫⁻ v, ∑' c₀ : Crat L,
          ‖phz d f s₁ z (w₁ * (cM c₀.1 * (L.j (rep q') * (sM R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))‖ₑ ∂μI < ⊤ := by
        have e5 : ∫⁻ v, ∑' c₀ : Crat L, ‖G ⟨q', c₀⟩ (β, v)‖ₑ ∂μI = (∫⁻ v, ∑' c₀ : Crat L,
            ‖phz d f s₁ z (w₁ * (cM c₀.1 * (L.j (rep q') * (sM R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))‖ₑ ∂μI) *
              ‖th' (d := d) T' β‖ₑ := by
          rw [← lintegral_mul_const' _ _ enorm_ne_top]
          refine lintegral_congr fun v => ?_
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun c₀ => enorm_mul _ _
        rw [e5] at hβ
        by_contra hcon
        rw [not_lt, top_le_iff] at hcon
        rw [hcon, ENNReal.top_mul hθe] at hβ
        exact lt_irrefl _ hβ
      have hγ : rep q' ∈ rat2 σ L.Y := (Quot.out q').2
      rw [unfqE h hf z hU h𝓐 hγ (L.j (nb' β) * x)] at hl
      rw [unfqC h hf z hU h𝓐 hγ (L.j (nb' β) * x) hl, hκ']
      simp_rw [hjj]
      ring
  rw [e1, e2, e3]
  simp_rw [e4]
  rw [tsum_mul_left, Complex.real_smul]
  ring

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end
