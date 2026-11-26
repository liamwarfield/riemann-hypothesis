module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiablePolyDeriv
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolynomialEqAevalPairings
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatThH

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivPairingEqZeroOfIsHeat
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivPairingEqZeroOfIsHeat
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.HeatJet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

def emb : (Ψ × Bool × Fin n × Fin N → ℂ) →ₗ[ℂ] CF Ψ N N × CF Ψ n N × CF Ψ n N where
  toFun w := (0, fun τ k a => w (τ, false, k, a), fun τ k a => w (τ, true, k, a))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

end GlobalTheory.SW.HeatJet

private lemma continuous_star_dotProduct_imH_mulVec {N : ℕ} :
    Continuous (fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) =>
      star p.2 ⬝ᵥ (_root_.GlobalTheory.SW.imH p.1 *ᵥ p.2)) := by
  unfold _root_.GlobalTheory.SW.imH
  fun_prop

private lemma isOpen_setOf_posDef_imH {N : ℕ} :
    IsOpen {A : Matrix (Fin N) (Fin N) ℂ | (_root_.GlobalTheory.SW.imH A).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro A hA
  have hK : IsCompact (Metric.sphere (0 : Fin N → ℂ) 1) := isCompact_sphere 0 1
  have hev : ∀ᶠ B in 𝓝 A, ∀ y ∈ Metric.sphere (0 : Fin N → ℂ) 1,
      0 < (star y ⬝ᵥ (_root_.GlobalTheory.SW.imH B *ᵥ y)).re := by
    refine hK.eventually_forall_of_forall_eventually fun y hy => ?_
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    have hpos := (posDef_iff_dotProduct_mulVec.mp hA).2 hy0
    have : 0 < (star y ⬝ᵥ (_root_.GlobalTheory.SW.imH A *ᵥ y)).re := (Complex.pos_iff.mp hpos).1
    exact (Complex.continuous_re.comp continuous_star_dotProduct_imH_mulVec).continuousAt.eventually
      (lt_mem_nhds this)
  filter_upwards [hev] with B hB
  have hH := _root_.GlobalTheory.SW.ExpSum.imH_isHermitian B
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set c : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ)
  have hy : c • x ∈ Metric.sphere (0 : Fin N → ℂ) 1 := by
    simp [c, norm_smul, hn.ne']
  have h1 := hB _ hy
  have hscale : star (c • x) ⬝ᵥ (_root_.GlobalTheory.SW.imH B *ᵥ (c • x)) =
      ((‖x‖⁻¹ ^ 2 : ℝ) : ℂ) * (star x ⬝ᵥ (_root_.GlobalTheory.SW.imH B *ᵥ x)) := by
    simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, c,
      Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    push_cast
    ring
  rw [hscale, Complex.re_ofReal_mul] at h1
  refine Complex.pos_iff.mpr ⟨?_, ?_⟩
  · exact pos_of_mul_pos_right h1 (by positivity)
  · exact (hH.im_star_dotProduct_mulVec_self x).symm

private lemma polyDeriv_mul_sum_pairs_eq_sum_lineDerivList {σ ι W : Type*} [Fintype ι] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (A : MvPolynomial σ ℂ) (i j : ι → σ) (u : σ → W) {F : W → ℂ} {x : W}
    (hF : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ F y) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (A * ∑ k, MvPolynomial.X (i k) * MvPolynomial.X (j k)) u F x =
      ∑ m ∈ A.support, AddMonoidAlgebra.coeff A m * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u)
        (fun y => ∑ k, _root_.GlobalTheory.lineDerivList ℂ [u (i k), u (j k)] F y) x := by
  have hFx : AnalyticAt ℂ F x := hF.self_of_nhds
  conv_lhs => rw [MvPolynomial.as_sum A, Finset.sum_mul]
  rw [_root_.ReciprocityTheory.ChartRestriction.G.I2.jof_polyDeriv_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum, _root_.ReciprocityTheory.ChartRestriction.G.I2.jof_polyDeriv_sum]
  have hG : ∀ k, AnalyticAt ℂ (_root_.GlobalTheory.lineDerivList ℂ [u (i k), u (j k)] F) x := fun k =>
    _root_.GlobalTheory.analyticAt_lineDerivList hFx _
  rw [_root_.GlobalTheory.lineDerivList_sum Finset.univ (fun k _ => hG k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmon : MvPolynomial.monomial m (AddMonoidAlgebra.coeff A m) * (MvPolynomial.X (i k) * MvPolynomial.X (j k)) =
      AddMonoidAlgebra.coeff A m • MvPolynomial.monomial (m + Finsupp.single (i k) 1 + Finsupp.single (j k) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one, add_assoc]
  rw [hmon, _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul]
  congr 1
  have hl : (((Finsupp.toMultiset m).toList ++ [i k, j k] : List σ) : Multiset σ) =
      Finsupp.toMultiset (m + Finsupp.single (i k) 1 + Finsupp.single (j k) 1) := by
    simp [Finsupp.toMultiset_add, Finsupp.toMultiset_single, add_assoc]
    rw [← Multiset.coe_add, Multiset.coe_toList]
    exact Multiset.add_cons (i k) _ {j k}
  rw [_root_.GlobalTheory.dirPolyDeriv_monomial_eq_lineDerivList hl u hFx, List.map_append, _root_.GlobalTheory.lineDerivList_append]
  rfl

private lemma polyDeriv_eq_sum_coeff_lineDerivList_of_analyticAt {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} {x : W} (hF : AnalyticAt ℂ F x) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F x = ∑ m ∈ P.support,
      AddMonoidAlgebra.coeff P m * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u) F x := by
  rw [_root_.GlobalTheory.dirPolyDeriv_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [_root_.GlobalTheory.dirPolyDeriv_monomial_eq_lineDerivList (Multiset.coe_toList _) u hF]

private lemma sum_coeff_lineDerivList_eq_lineDeriv_polyDeriv {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (A : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} {x : W} (z : W)
    (hF : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ F y) :
    ∑ m ∈ A.support, AddMonoidAlgebra.coeff A m * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u)
        (_root_.GlobalTheory.lineDerivList ℂ [z] F) x = lineDeriv ℂ (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv A u F y) x z := by
  have hFx : AnalyticAt ℂ F x := hF.self_of_nhds
  have heq : (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv A u F y) =ᶠ[𝓝 x] fun y => ∑ m ∈ A.support,
      AddMonoidAlgebra.coeff A m * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u) F y :=
    hF.mono fun y hy => polyDeriv_eq_sum_coeff_lineDerivList_of_analyticAt A u hy
  have h1 := (_root_.GlobalTheory.lineDerivList_congr (𝕜 := ℂ) heq [z]).self_of_nhds
  have hl : lineDeriv ℂ (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv A u F y) x z = _root_.GlobalTheory.lineDerivList ℂ [z] (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv A u F y) x := by
    simp [_root_.GlobalTheory.lineDerivList_cons, _root_.GlobalTheory.lineDerivList]
  rw [hl, h1, _root_.GlobalTheory.lineDerivList_sum A.support (F := fun m y => AddMonoidAlgebra.coeff A m * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u) F y) (fun m _ => analyticAt_const.mul (_root_.GlobalTheory.analyticAt_lineDerivList hFx _))]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc := congrFun (_root_.GlobalTheory.lineDerivList_const_smul (𝕜 := ℂ) [z] (AddMonoidAlgebra.coeff A m)
    (_root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u) F)) x
  simp only [smul_eq_mul] at hc
  rw [hc]
  congr 1
  rw [← _root_.GlobalTheory.lineDerivList_append, ← _root_.GlobalTheory.lineDerivList_append]
  exact _root_.GlobalTheory.lineDerivList_perm hFx List.perm_append_comm

private lemma polyDeriv_comp_linearMap_add_of_analyticAt {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup W'] [NormedSpace ℂ W'] [FiniteDimensional ℂ W'] (P : MvPolynomial σ ℂ)
    (u : σ → W') (L : W' →ₗ[ℂ] W) (c : W) {F : W → ℂ} (hF : AnalyticAt ℂ F c) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun w => F (L w + c)) 0 = _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun i => L (u i)) F c := by
  have hL : AnalyticAt ℂ (fun w => F (L w + c)) 0 := by
    have h1 : AnalyticAt ℂ (fun w => L w + c) 0 :=
      (LinearMap.toContinuousLinearMap L).analyticAt 0 |>.add analyticAt_const
    have hF' : AnalyticAt ℂ F (L 0 + c) := by simpa using hF
    exact AnalyticAt.comp (g := F) (f := fun w => L w + c) (x := 0) hF' h1
  rw [polyDeriv_eq_sum_coeff_lineDerivList_of_analyticAt P u hL, polyDeriv_eq_sum_coeff_lineDerivList_of_analyticAt P _ hF]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [_root_.GlobalTheory.lineDerivList_comp_linearMap (F := fun q => F (q + c)), _root_.GlobalTheory.lineDerivList_comp_add_const]
  beta_reduce
  rw [map_zero, zero_add, List.map_map]
  rfl

theorem _root_.GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (D : _root_.GlobalTheory.SW.CM Ψ N N → _root_.GlobalTheory.SW.CM Ψ n N → _root_.GlobalTheory.SW.CM Ψ n N → ℂ), _root_.GlobalTheory.SW.IsHeat Ψ D → (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, D Z 0 0 = 0) → ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ s : MvPolynomial (Ψ × Fin N × Fin N) ℂ, _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) s) (fun v => (Pi.single v 1 : Ψ × Bool × Fin n × Fin N → ℂ)) (fun w : Ψ × Bool × Fin n × Fin N → ℂ => D Z (fun τ => Matrix.of fun k a => w (τ, false, k, a)) (fun τ => Matrix.of fun k a => w (τ, true, k, a))) 0 = 0 := by
  intro E _ _ _ Ψ n N D hD h0 Z hZ s
  obtain ⟨hdiff, hheat⟩ := hD
  have hU : IsOpen {p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) | p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N} := by
    have : {p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) | p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N} = ⋂ τ : Ψ, (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => (p.1 τ : Matrix (Fin N) (Fin N) ℂ)) ⁻¹' {A | (_root_.GlobalTheory.SW.imH A).PosDef} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    rw [this]
    exact isOpen_iInter_of_finite fun τ => isOpen_setOf_posDef_imH.preimage ((continuous_apply τ).comp continuous_fst)
  have han : AnalyticOnNhd ℂ (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) {p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) | p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N} := _root_.GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hdiff
  have hanU : ∀ p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)), p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N → ∀ᶠ y in 𝓝 p, AnalyticAt ℂ (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) y :=
    fun p hp => Filter.eventually_of_mem (hU.mem_nhds hp) fun y hy => han y hy
  let ew : Ψ × Bool × Fin n × Fin N → ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) := fun w => _root_.GlobalTheory.SW.HeatJet.emb Ψ (Pi.single w 1)
  let ez : Ψ × Fin N × Fin N → ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) := fun v => ((fun σ => if σ = v.1 then (Matrix.single v.2.1 v.2.2 (1 : ℂ) : Fin N → Fin N → ℂ) else 0 : Ψ → Fin N → Fin N → ℂ), 0, 0)
  have hheat' : ∀ p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)), p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N → ∀ v : Ψ × Fin N × Fin N,
      ∑ k, _root_.GlobalTheory.lineDerivList ℂ [ew (v.1, false, k, v.2.1), ew (v.1, true, k, v.2.2)] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) p =
        (2 * Real.pi * Complex.I) * _root_.GlobalTheory.lineDerivList ℂ [ez v] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) p := by
    intro p hp v
    have h := hheat p.1 hp p.2.1 p.2.2 v.1 v.2.1 v.2.2
    have e1 : ∀ s : ℂ, p + s • ez v = ((show Ψ → Fin N → Fin N → ℂ from fun σ => (show Ψ → Matrix (Fin N) (Fin N) ℂ from p.1) σ + if σ = v.1 then single v.2.1 v.2.2 s else 0), p.2.1, p.2.2) := by
      intro s
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext σ i j
        change p.1 σ i j + s * (if σ = v.1 then (single v.2.1 v.2.2 (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) else 0) i j = p.1 σ i j + (if σ = v.1 then (single v.2.1 v.2.2 s : Matrix (Fin N) (Fin N) ℂ) else 0) i j
        by_cases hσ : σ = v.1
        · rw [if_pos hσ, if_pos hσ]
          simp only [Matrix.single_apply]
          split_ifs <;> simp
        · rw [if_neg hσ, if_neg hσ]
          simp
      · funext σ i j
        change p.2.1 σ i j + s * 0 = p.2.1 σ i j
        simp
      · funext σ i j
        change p.2.2 σ i j + s * 0 = p.2.2 σ i j
        simp
    have e2 : ∀ k : Fin n, ∀ s t : ℂ, p + s • ew (v.1, false, k, v.2.1) + t • ew (v.1, true, k, v.2.2) =
        (p.1, (show Ψ → Fin n → Fin N → ℂ from fun σ => (show Ψ → Matrix (Fin n) (Fin N) ℂ from p.2.1) σ + if σ = v.1 then single k v.2.1 s else 0),
          (show Ψ → Fin n → Fin N → ℂ from fun σ => (show Ψ → Matrix (Fin n) (Fin N) ℂ from p.2.2) σ + if σ = v.1 then single k v.2.2 t else 0)) := by
      intro k s t
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext σ i j
        change p.1 σ i j + s * 0 + t * 0 = p.1 σ i j
        simp
      · funext σ i j
        change p.2.1 σ i j + s * (Pi.single (v.1, false, k, v.2.1) (1 : ℂ) : Ψ × Bool × Fin n × Fin N → ℂ) (σ, false, i, j) + t * (Pi.single (v.1, true, k, v.2.2) (1 : ℂ) : Ψ × Bool × Fin n × Fin N → ℂ) (σ, false, i, j) = p.2.1 σ i j + (if σ = v.1 then (single k v.2.1 s : Matrix (Fin n) (Fin N) ℂ) else 0) i j
        by_cases hσ : σ = v.1
        · rw [if_pos hσ]
          subst hσ
          by_cases hi : i = k <;> by_cases hj : j = v.2.1 <;> simp [Matrix.single_apply, Pi.single_apply, hi, hj, eq_comm (a := k), eq_comm (a := v.2.1)]
        · rw [if_neg hσ]
          simp [Pi.single_apply, hσ]
      · funext σ i j
        change p.2.2 σ i j + s * (Pi.single (v.1, false, k, v.2.1) (1 : ℂ) : Ψ × Bool × Fin n × Fin N → ℂ) (σ, true, i, j) + t * (Pi.single (v.1, true, k, v.2.2) (1 : ℂ) : Ψ × Bool × Fin n × Fin N → ℂ) (σ, true, i, j) = p.2.2 σ i j + (if σ = v.1 then (single k v.2.2 t : Matrix (Fin n) (Fin N) ℂ) else 0) i j
        by_cases hσ : σ = v.1
        · rw [if_pos hσ]
          subst hσ
          by_cases hi : i = k <;> by_cases hj : j = v.2.2 <;> simp [Matrix.single_apply, Pi.single_apply, hi, hj, eq_comm (a := k), eq_comm (a := v.2.2)]
        · rw [if_neg hσ]
          simp [Pi.single_apply, hσ]
    have l1 : _root_.GlobalTheory.lineDerivList ℂ [ez v] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) p = deriv (fun s : ℂ => D (fun σ => (show Ψ → Matrix (Fin N) (Fin N) ℂ from p.1) σ + if σ = v.1 then single v.2.1 v.2.2 s else 0) p.2.1 p.2.2) 0 := by
      simp only [_root_.GlobalTheory.lineDerivList_cons, _root_.GlobalTheory.lineDerivList, lineDeriv]
      congr 1
      funext s
      rw [e1 s]
    have l2 : ∀ k : Fin n, _root_.GlobalTheory.lineDerivList ℂ [ew (v.1, false, k, v.2.1), ew (v.1, true, k, v.2.2)] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) p = deriv (fun s : ℂ => deriv (fun t : ℂ => D p.1 (fun σ => (show Ψ → Matrix (Fin n) (Fin N) ℂ from p.2.1) σ + if σ = v.1 then single k v.2.1 s else 0) fun σ => (show Ψ → Matrix (Fin n) (Fin N) ℂ from p.2.2) σ + if σ = v.1 then single k v.2.2 t else 0) 0) 0 := by
      intro k
      simp only [_root_.GlobalTheory.lineDerivList_cons, _root_.GlobalTheory.lineDerivList, lineDeriv]
      congr 1
      funext s
      congr 1
      funext t
      rw [e2 k s t]
    rw [l1, h]
    exact Finset.sum_congr rfl fun k _ => l2 k
  have key : ∀ s : MvPolynomial (Ψ × Fin N × Fin N) ℂ, ∀ p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)), p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N → p.2 = 0 →
      _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) s) ew (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) p = 0 := by
    intro s
    induction s using MvPolynomial.induction_on with
    | C a =>
      intro p hp hp0
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.C_apply, show MvPolynomial.monomial (0 : (Ψ × Bool × Fin n × Fin N) →₀ ℕ) a = a • MvPolynomial.monomial 0 1 by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_monomial_one, _root_.ReciprocityTheory.ChartRestriction.G.I2.pdTerm_eq_itD]
      simp only [Finsupp.toMultiset_zero, Multiset.toList_zero, List.map_nil, _root_.ReciprocityTheory.ChartRestriction.G.I2.itD_nil]
      obtain ⟨p1, p2⟩ := p
      simp only at hp0
      subst hp0
      exact mul_eq_zero_of_right a (h0 p1 hp)
    | add A B hA hB =>
      intro p hp hp0
      rw [map_add (f := _), _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_add, hA p hp hp0, hB p hp hp0, add_zero]
    | mul_X A v ih =>
      intro p hp hp0
      rw [map_mul, MvPolynomial.aeval_X]
      have hstep := polyDeriv_mul_sum_pairs_eq_sum_lineDerivList (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) A) (fun k => (v.1, false, k, v.2.1)) (fun k => (v.1, true, k, v.2.2)) ew (hanU p hp)
      rw [hstep]
      have hev : (fun y => ∑ k, _root_.GlobalTheory.lineDerivList ℂ [ew (v.1, false, k, v.2.1), ew (v.1, true, k, v.2.2)] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) y) =ᶠ[𝓝 p]
          fun y => (2 * Real.pi * Complex.I) • _root_.GlobalTheory.lineDerivList ℂ [ez v] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) y :=
        Filter.eventually_of_mem (hU.mem_nhds hp) fun y hy => by simpa [smul_eq_mul] using hheat' y hy v
      have hsum : ∀ m, _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map ew)
            (fun y => ∑ k, _root_.GlobalTheory.lineDerivList ℂ [ew (v.1, false, k, v.2.1), ew (v.1, true, k, v.2.2)] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) y) p =
          (2 * Real.pi * Complex.I) * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map ew) (_root_.GlobalTheory.lineDerivList ℂ [ez v] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2)) p := by
        intro m
        rw [(_root_.GlobalTheory.lineDerivList_congr hev _).self_of_nhds, _root_.GlobalTheory.lineDerivList_const_smul]
        simp only [smul_eq_mul]
      simp only [hsum]
      simp only [mul_left_comm _ (2 * Real.pi * Complex.I : ℂ), ← Finset.mul_sum]
      rw [sum_coeff_lineDerivList_eq_lineDeriv_polyDeriv _ ew (ez v) (hanU p hp)]
      have hline : (fun t : ℂ => (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) A) ew (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) y) (p + t • ez v)) =ᶠ[𝓝 (0 : ℂ)] fun _ => (0 : ℂ) := by
        have hc : Continuous fun t : ℂ => p + t • ez v := by fun_prop
        have hmem : {p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) | p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N} ∈ 𝓝 (p + (0 : ℂ) • ez v) := by
          simpa using hU.mem_nhds hp
        filter_upwards [hc.continuousAt.preimage_mem_nhds hmem] with t ht
        refine ih _ ht ?_
        simp [ez, hp0]
      rw [lineDeriv, Filter.EventuallyEq.deriv_eq hline, deriv_const, mul_zero]
  have hG : (fun w : Ψ × Bool × Fin n × Fin N → ℂ => D Z (fun τ => Matrix.of fun k a => w (τ, false, k, a)) (fun τ => Matrix.of fun k a => w (τ, true, k, a))) = fun w => (fun q : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D q.1 q.2.1 q.2.2) ((_root_.GlobalTheory.SW.HeatJet.emb Ψ : (Ψ × Bool × Fin n × Fin N → ℂ) →ₗ[ℂ] ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ))) w + ((show Ψ → Fin N → Fin N → ℂ from Z), 0, 0)) := by
    funext w
    simp only [_root_.GlobalTheory.SW.HeatJet.emb, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add, zero_add, add_zero]
    rw [show (0 + (show Ψ → Fin N → Fin N → ℂ from Z)) = Z from zero_add _]
    rfl
  rw [hG]
  refine (polyDeriv_comp_linearMap_add_of_analyticAt (u := fun v => (Pi.single v 1 : Ψ × Bool × Fin n × Fin N → ℂ)) (L := (_root_.GlobalTheory.SW.HeatJet.emb Ψ : (Ψ × Bool × Fin n × Fin N → ℂ) →ₗ[ℂ] ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)))) (c := ((show Ψ → Fin N → Fin N → ℂ from Z), 0, 0)) (F := fun q : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D q.1 q.2.1 q.2.2) _ (hanU _ hZ).self_of_nhds).trans ?_
  exact key s _ hZ rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivPairingEqZeroOfIsHeatStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyDeriv_aeval_pairings_eq_zero_of_isHeat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ), IsHeat Ψ D → (∀ Z ∈ Hn Ψ N, D Z 0 0 = 0) → ∀ Z ∈ Hn Ψ N, ∀ s : MvPolynomial (Ψ × Fin N × Fin N) ℂ, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) s) (fun v => (Pi.single v 1 : Ψ × Bool × Fin n × Fin N → ℂ)) (fun w : Ψ × Bool × Fin n × Fin N → ℂ => D Z (fun τ => Matrix.of fun k a => w (τ, false, k, a)) (fun τ => Matrix.of fun k a => w (τ, true, k, a))) 0 = 0 := by
  first | exact @GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat | exact GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat | (intros; apply GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolyDerivKillsDoubledHeatSolution
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.SW.InvKill

noncomputable section

section General

open MvPolynomial

variable {ι σ W : Type} [Fintype σ] [DecidableEq σ] [NormedAddCommGroup W] [NormedSpace ℂ W]

def lin (d : σ → ℂ) : MvPolynomial σ ℂ := ∑ v, C (d v) * X v

omit [DecidableEq σ] in
theorem eval_lin (d y : σ → ℂ) : eval y (lin d) = d ⬝ᵥ y := by
  simp [lin, dotProduct]

omit [DecidableEq σ] in
theorem eval_aeval_lin (d : ι → σ → ℂ) (y : σ → ℂ) (P : MvPolynomial ι ℂ) :
    eval y (aeval (fun l => lin (d l)) P) = eval (fun l => d l ⬝ᵥ y) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add (f := _), hP, hQ]
  | mul_X P l hP => simp only [map_mul, hP, aeval_X, eval_X, eval_lin]

abbrev crdDir (σ : Type) [DecidableEq σ] : σ → σ → ℂ := fun v => Pi.single v 1

omit [DecidableEq σ] in
theorem smooth {F : (σ → ℂ) → ℂ} (hF : Differentiable ℂ F) : ContDiff ℂ (⊤ : ℕ∞) F :=
  (SCV.analyticOnNhd_of_differentiable hF Set.univ).contDiff

theorem polyDeriv_C (a : ℂ) (u : ι → W) (F : W → ℂ) (x : W) : I2.polyDeriv (C a) u F x = a * F x := by
  have h : (C a : MvPolynomial ι ℂ) = a • monomial 0 1 := by simp [smul_eq_C_mul]
  rw [h]
  simp [I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD, -smul_monomial,
    -monomial_zero', I2.itD_nil]

theorem polyDeriv_aeval_lin {F : (σ → ℂ) → ℂ} (hF : Differentiable ℂ F) (d : ι → σ → ℂ)
    (P : MvPolynomial ι ℂ) (x : σ → ℂ) :
    I2.polyDeriv (aeval (fun l => lin (d l)) P) (crdDir σ) F x = I2.polyDeriv P d F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a => rw [algHom_C, algebraMap_eq, polyDeriv_C, polyDeriv_C]
  | add P Q hP hQ => simp only [map_add (f := _), I2.polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    rw [map_mul, aeval_X, lin, Finset.mul_sum, I2.jof_polyDeriv_sum,
      polyDeriv_mul_X (smooth hF)]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [pi_eq_sum_univ' (d l), map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, C_mul', I2.polyDeriv_smul, polyDeriv_mul_X (smooth hF), funext hP]
    simp

theorem polyDeriv_mul {F : (σ → ℂ) → ℂ} (hF : Differentiable ℂ F) (u : ι → σ → ℂ)
    (P Q : MvPolynomial ι ℂ) (x : σ → ℂ) :
    I2.polyDeriv (P * Q) u F x = I2.polyDeriv P u (fun y => I2.polyDeriv Q u F y) x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a => rw [C_mul', I2.polyDeriv_smul, polyDeriv_C]
  | add P P' hP hP' => simp only [add_mul, I2.polyDeriv_add, hP, hP']
  | mul_X P l hP =>
    rw [mul_right_comm, polyDeriv_mul_X (smooth hF),
      polyDeriv_mul_X (smooth (differentiable_polyDeriv (smooth hF) Q u)), funext hP]

theorem polyDeriv_bi {G : (σ → ℂ) → ℂ} (hG : Differentiable ℂ G) (A B : W →L[ℂ] (σ → ℂ))
    (u : ι → W) (P Q : MvPolynomial ι ℂ) :
    I2.polyDeriv P u (fun z => I2.polyDeriv Q u (fun w => G (A z + B w)) 0) 0 =
      I2.polyDeriv (aeval (fun l => lin (A (u l))) P * aeval (fun l => lin (B (u l))) Q)
        (crdDir σ) G 0 := by
  have h1 (z : W) : I2.polyDeriv Q u (fun w => G (A z + B w)) 0 =
      ((fun y => I2.polyDeriv Q (B ∘ u) G y) ∘ A) z := by
    have h := Jet.polyDeriv_comp_clm Q u (F := fun v => G (A z + v)) (by fun_prop) B 0
    refine h.trans ?_
    simp only [I2.polyDeriv, iteratedFDeriv_comp_add_left, map_zero, add_zero, Function.comp_apply]
  have hd := differentiable_polyDeriv (smooth hG) Q (B ∘ u)
  rw [funext h1, Jet.polyDeriv_comp_clm P u hd, map_zero, polyDeriv_mul hG,
    funext (polyDeriv_aeval_lin hG _ Q)]
  exact (polyDeriv_aeval_lin hd _ P 0).symm

theorem exists_absorb {K : (σ → ℂ) → ℂ} (hK : Differentiable ℂ K) (Q : MvPolynomial σ ℂ) :
    ∃ p : MvPolynomial σ ℂ, ∀ F : (σ → ℂ) → ℂ, Differentiable ℂ F →
      I2.polyDeriv Q (crdDir σ) (fun x => K x * F x) 0 = I2.polyDeriv p (crdDir σ) F 0 := by
  refine ⟨∑ m ∈ Q.support, ∑ c ∈ Finset.HasAntidiagonal.antidiagonal m,
    (Q.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff c.1 (taylor K) *
      ((∏ i, (c.2 i).factorial : ℕ) : ℂ)⁻¹) • monomial c.2 1, fun F hF => ?_⟩
  have hK' := SCV.analyticOnNhd_of_differentiable hK Set.univ 0 trivial
  have hF' := SCV.analyticOnNhd_of_differentiable hF Set.univ 0 trivial
  rw [dirPolyDeriv_eq_sum_coeff_taylor, show (fun x => K x * F x) = K * F from rfl,
    taylor_mul hK' hF', I2.jof_polyDeriv_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [I2.jof_polyDeriv_sum, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [I2.polyDeriv_smul, coeff_taylor F]
  ring

theorem absorb_invariant {K : (σ → ℂ) → ℂ} (hK : Differentiable ℂ K) {Q p : MvPolynomial σ ℂ}
    (hp : ∀ F : (σ → ℂ) → ℂ, Differentiable ℂ F →
      I2.polyDeriv Q (crdDir σ) (fun x => K x * F x) 0 = I2.polyDeriv p (crdDir σ) F 0)
    (S : (σ → ℂ) → σ → ℂ) (S' : (σ → ℂ) →L[ℂ] (σ → ℂ)) (hS : ∀ x y, x ⬝ᵥ S y = S' x ⬝ᵥ y)
    (hQ : ∀ y, eval (S y) Q = eval y Q) (hK' : ∀ x, K (S' x) = K x) (y : σ → ℂ) :
    eval (S y) p = eval y p := by
  have hd (y : σ → ℂ) : Differentiable ℂ fun x : σ → ℂ => cexp (x ⬝ᵥ y) := by
    unfold dotProduct; fun_prop
  have h1 (y : σ → ℂ) : eval y p = I2.polyDeriv Q (crdDir σ) (fun x => K x * cexp (x ⬝ᵥ y)) 0 := by
    rw [hp _ (hd y)]
    have h := KernSym.polyDeriv_exp p (crdDir σ)
      (LinearMap.toContinuousLinearMap ((dotProductBilin ℂ ℂ).flip y)) 1
    simpa using h.symm
  have h2 : aeval (fun v => lin (S' (crdDir σ v))) Q = Q := by
    refine MvPolynomial.funext fun y => ?_
    rw [eval_aeval_lin, ← hQ y]
    simp [← hS]
  have h3 : (fun x => K x * cexp (x ⬝ᵥ S y)) = (fun x => K x * cexp (x ⬝ᵥ y)) ∘ S' := by
    funext x
    simp [hS, hK']
  rw [h1, h1, h3, Jet.polyDeriv_comp_clm _ _ (hK.fun_mul (hd y)), map_zero,
    ← polyDeriv_aeval_lin (hK.fun_mul (hd y))]
  exact congrArg (fun R => I2.polyDeriv R _ _ _) h2

end General

section Letters

open MvPolynomial

variable {T J : Type} [Fintype T] [Fintype J] {n r g p q : ℕ}

abbrev Ell (T : Type) (n r : ℕ) : Type := T × Bool × Fin n × Fin r

def act (c : T → Bool → Matrix (Fin n) (Fin n) ℂ) : (Ell T n r → ℂ) →L[ℂ] (Ell T n r → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y v => ∑ l, c v.1 v.2.1 v.2.2.1 l * y (v.1, v.2.1, l, v.2.2.2)
      map_add' := fun x y => by funext v; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by funext v; simp [Finset.mul_sum, mul_left_comm] }

theorem act_apply (c : T → Bool → Matrix (Fin n) (Fin n) ℂ) (y : Ell T n r → ℂ) (v : Ell T n r) :
    act c y v = ∑ l, c v.1 v.2.1 v.2.2.1 l * y (v.1, v.2.1, l, v.2.2.2) := rfl

theorem dotProduct_act (c : T → Bool → Matrix (Fin n) (Fin n) ℂ) (x y : Ell T n r → ℂ) :
    x ⬝ᵥ act c y = act (fun t b => (c t b)ᵀ) x ⬝ᵥ y := by
  simp only [dotProduct, act_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    transpose_apply]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

def uc (u : T → Matrix (Fin n) (Fin n) ℂ) (t : T) (b : Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun k l => if b then u t k l else conj (u t k l)

def gauss (c : T → ℂ) (M : T → Matrix (Fin r) (Fin r) ℂ) (x : Ell T n r → ℂ) : ℂ :=
  ∏ τ, c τ * cexp (Real.pi * ∑ k, (fun a => x (τ, true, k, a)) ⬝ᵥ M τ *ᵥ
    fun a => x (τ, false, k, a))

theorem differentiable_gauss (c : T → ℂ) (M : T → Matrix (Fin r) (Fin r) ℂ) :
    Differentiable ℂ (gauss (n := n) c M) := by
  unfold gauss mulVec dotProduct
  fun_prop

theorem gauss_act (c : T → ℂ) (M : T → Matrix (Fin r) (Fin r) ℂ)
    {u : T → Matrix (Fin n) (Fin n) ℂ} (hu : ∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (x : Ell T n r → ℂ) : gauss c M (act (fun t b => (uc u t b)ᵀ) x) = gauss c M x := by
  refine Finset.prod_congr rfl fun τ _ => ?_
  congr 3
  have h0 (Z Z' : Matrix (Fin n) (Fin r) ℂ) :
      ∑ k, Z' k ⬝ᵥ M τ *ᵥ Z k = (Z' * M τ * Zᵀ).trace := by
    simp only [dotProduct_mulVec]
    rfl
  have h1 : (u τ)ᴴᵀ * (u τ)ᵀ = 1 := by
    rw [← transpose_mul, ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.1 (hu τ),
      transpose_one]
  have h2 := h0 ((u τ)ᴴ * Matrix.of fun k a => x (τ, false, k, a))
    ((u τ)ᵀ * Matrix.of fun k a => x (τ, true, k, a))
  rw [transpose_mul, ← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc (u τ)ᵀ,
    Matrix.mul_assoc (u τ)ᵀ, ← Matrix.mul_assoc, h1, Matrix.one_mul, ← h0] at h2
  exact h2

def lift (idx : Fin g ≃ T × Fin r) (N : T → Bool → Fin r → Fin r → ℂ) :
    (Fin n → Fin g → ℂ) →L[ℂ] (Ell T n r → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z v => ∑ a, N v.1 v.2.1 v.2.2.2 a * z v.2.2.1 (idx.symm (v.1, a))
      map_add' := fun x y => by funext v; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by funext v; simp [Finset.mul_sum, mul_left_comm] }

omit [Fintype T] in
theorem lift_apply (idx : Fin g ≃ T × Fin r) (N : T → Bool → Fin r → Fin r → ℂ)
    (z : Fin n → Fin g → ℂ) (v : Ell T n r) :
    lift idx N z v = ∑ a, N v.1 v.2.1 v.2.2.2 a * z v.2.2.1 (idx.symm (v.1, a)) := rfl

theorem lift_single (idx : Fin g ≃ T × Fin r) (N : T → Bool → Fin r → Fin r → ℂ) (τ : T)
    (a : Fin r) (k : Fin n) (y : Ell T n r → ℂ) :
    lift idx N (Pi.single k (Pi.single (idx.symm (τ, a)) 1)) ⬝ᵥ y =
      ∑ b, ∑ c, N τ b c a * y (τ, b, k, c) := by
  have h (v : Ell T n r) : lift idx N (Pi.single k (Pi.single (idx.symm (τ, a)) 1)) v =
      if v.1 = τ then if v.2.2.1 = k then N τ v.2.1 v.2.2.2 a else 0 else 0 := by
    obtain ⟨t, b, l, c⟩ := v
    rw [lift_apply]
    by_cases hl : l = k <;> by_cases ht : t = τ <;> simp [Pi.single_apply, hl, ht]
  simp only [dotProduct, h, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single τ (by simp +contextual) (by simp)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single k (by simp +contextual) (by simp)]
  simp

theorem lift_single_act (idx : Fin g ≃ T × Fin r) (N : T → Bool → Fin r → Fin r → ℂ) (τ : T)
    (a : Fin r) (b : Bool) (hN : ∀ c, N τ (!b) c a = 0) (k : Fin n)
    (s : T → Bool → Matrix (Fin n) (Fin n) ℂ) (y : Ell T n r → ℂ) :
    lift idx N (Pi.single k (Pi.single (idx.symm (τ, a)) 1)) ⬝ᵥ act s y =
      ∑ l, s τ b k l * lift idx N (Pi.single l (Pi.single (idx.symm (τ, a)) 1)) ⬝ᵥ y := by
  simp only [lift_single, act_apply, Fintype.sum_bool]
  cases b <;> simp only [Bool.not_false, Bool.not_true] at hN <;>
    simp only [hN, zero_mul, Finset.sum_const_zero, zero_add, add_zero, Finset.mul_sum] <;>
    rw [Finset.sum_comm] <;>
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem eval_barP {σ : Type} (y : σ → ℂ) (P : MvPolynomial σ ℂ) :
    eval y (barP P) = conj (eval (fun l => conj (y l)) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [barP]
  | add P Q hP hQ => simp only [barP, map_add (f := _)] at *; rw [hP, hQ]
  | mul_X P l hP => simp only [barP, map_mul, map_X, eval_X, conj_conj] at *; rw [hP]

omit [Fintype T] in
theorem invFam_eval {P : J → Harm.Poly ℂ T p q (Fin n)} (hP : InvFam P)
    {u : T → Matrix (Fin n) (Fin n) ℂ} (hu : ∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (z w z' w' : Harm.Var T p q (Fin n) → ℂ)
    (hz : ∀ t ρ k, z' (t, ρ, k) = ∑ l, uc u t ρ.isLeft k l * z (t, ρ, l))
    (hw : ∀ t ρ k, w' (t, ρ, k) = ∑ l, uc u t ρ.isRight k l * w (t, ρ, l)) :
    ∑ j, eval z' (P j) * eval w' (barP (P j)) = ∑ j, eval z (P j) * eval w (barP (P j)) := by
  let γ : T → GL (Fin n) ℂ := fun t =>
    ⟨star (u t), u t, Matrix.mem_unitaryGroup_iff'.1 (hu t), Matrix.mem_unitaryGroup_iff.1 (hu t)⟩
  have h := hP γ (fun t => Unitary.star_mem (hu t)) z fun l => conj (w l)
  simp only [eval_barP]
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Harm.colActHom, Harm.eval_colSubst, Harm.eval_colSubst]
  congr 4 <;> funext ⟨t, ρ, k⟩ <;> cases ρ <;>
    simp [hz, hw, uc, γ, mulVec, vecMul, dotProduct, mul_comm]

end Letters

section Core

open MvPolynomial

variable {T J : Type} [Fintype T] [DecidableEq T] [Fintype J] {n r g p q : ℕ}

theorem exists_invariant (idx : Fin g ≃ T × Fin r) (ρ : Fin q ⊕ Fin p → Fin r)
    (NA NB : T → Bool → Fin r → Fin r → ℂ)
    (hA : ∀ τ i c, NA τ (!i.isLeft) c (ρ i) = 0) (hB : ∀ τ i c, NB τ (!i.isRight) c (ρ i) = 0)
    {P : J → Harm.Poly ℂ T q p (Fin n)} (hP : InvFam P) (c : T → ℂ)
    (M : T → Matrix (Fin r) (Fin r) ℂ) (d : Harm.Var T q p (Fin n) → Fin n → Fin g → ℂ)
    (hd : ∀ t i k, d (t, i, k) = Pi.single k (Pi.single (idx.symm (t, ρ i)) 1)) :
    ∃ R : MvPolynomial (Ell T n r) ℂ,
      (∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) →
        ∀ y, eval (act (uc u) y) R = eval y R) ∧
      ∀ F : (Ell T n r → ℂ) → ℂ, Differentiable ℂ F →
        ∑ j, I2.polyDeriv (P j) d (fun z => I2.polyDeriv (barP (P j)) d (fun w =>
          gauss c M (lift idx NA z + lift idx NB w) * F (lift idx NA z + lift idx NB w)) 0) 0 =
        I2.polyDeriv R (crdDir _) F 0 := by
  obtain ⟨R, hR⟩ := exists_absorb (differentiable_gauss (n := n) c M)
    (∑ j, aeval (fun l => lin (lift idx NA (d l))) (P j) *
      aeval (fun l => lin (lift idx NB (d l))) (barP (P j)))
  refine ⟨R, fun u hu => absorb_invariant (differentiable_gauss c M) hR _ _
    (dotProduct_act (uc u)) (fun y => ?_) (gauss_act c M hu), fun F hF => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, eval_aeval_lin]
      refine invFam_eval hP hu _ _ _ _ (fun t i k => ?_) fun t i k => ?_
      · simp only [hd]
        convert lift_single_act idx NA t (ρ i) _ (hA t i) k (uc u) y
      · simp only [hd]
        convert lift_single_act idx NB t (ρ i) _ (hB t i) k (uc u) y
  · rw [← hR F hF, I2.jof_polyDeriv_sum]
    exact Finset.sum_congr rfl fun j _ =>
      polyDeriv_bi ((differentiable_gauss c M).fun_mul hF) _ _ _ _ _

end Core

section Doubled

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (idx : Fin g ≃ X.Ψ × Fin r) (x₁ x₂ : Frame X.Ψ r)

def ellM (τ : X.Ψ) (b : Bool) : Matrix (Fin r) (Fin r) ℂ :=
  if b then (τ.1 X.κ0 / 2) • ((X.Gm.map τ.1)ᵀ * (aLin X x₁ x₂ τ)⁻¹)
  else (-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 * (aAnti X x₁ x₂ τ)⁻¹)

def ellN (s : Bool) (τ : X.Ψ) (b : Bool) (c a : Fin r) : ℂ :=
  if ((a : ℕ) < X.p0 ↔ b = s) then ellM X x₁ x₂ τ b c a else 0

theorem dblz_eq (z w : Fin n → Fin g → ℂ) : dblz X idx x₁ x₂ z w = fun τ => Matrix.of fun k a =>
    (lift idx (ellN X x₁ x₂ false) z + lift idx (ellN X x₁ x₂ true) w) (τ, false, k, a) := by
  funext τ
  ext k c
  simp only [dblz, of_apply, Pi.add_apply, lift_apply, mulVec_mulVec, ← smul_mulVec,
    ← Finset.sum_add_distrib]
  rw [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : (a : ℕ) < X.p0 <;> simp [ellN, ellM, h]

theorem dblz'_eq (z w : Fin n → Fin g → ℂ) : dblz' X idx x₁ x₂ z w = fun τ => Matrix.of fun k a =>
    (lift idx (ellN X x₁ x₂ false) z + lift idx (ellN X x₁ x₂ true) w) (τ, true, k, a) := by
  funext τ
  ext k c
  simp only [dblz', of_apply, Pi.add_apply, lift_apply, ← mulVec_transpose, mulVec_mulVec,
    ← smul_mulVec, ← Finset.sum_add_distrib]
  rw [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : (a : ℕ) < X.p0 <;> simp [ellN, ellM, h]

end Doubled

end

end GlobalTheory.SW.InvKill

namespace GlobalTheory.SW

open InvKill

theorem biDeriv_kZero_mul_heat_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n m : ℕ)
    (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), r ≤ n → InvFam P →
    ∀ D : CM X.Ψ r r → CM X.Ψ n r → CM X.Ψ n r → ℂ, IsHeat X.Ψ D → (∀ Z ∈ Hn X.Ψ r, D Z 0 0 = 0) →
    ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, biDeriv X hr idx P (fun z₁ w => kZero X idx x₁ x₂ z₁ w *
      D (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)) = 0 := by
  intro E _ _ _ r X g q0 hr idx n m P hn hP D hD h0 x₁ h₁ x₂ h₂
  have hZ := (dblZ_mem_Hn E r X x₁ h₁ x₂ h₂).2.1
  obtain ⟨R, hR, hR'⟩ := exists_invariant idx (rowIdx hr) (ellN X x₁ x₂ false) (ellN X x₁ x₂ true)
    (by rintro τ (i | i) c <;> have := i.isLt <;> simp [ellN] <;> omega)
    (by rintro τ (i | i) c <;> have := i.isLt <;> simp [ellN] <;> omega) hP
    (fun τ => (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹)
    (fun τ => (imH (dblZ X x₁ x₂ τ))⁻¹) (letterDir X hr idx) (fun _ _ _ => rfl)
  obtain ⟨s, rfl⟩ := GlobalTheory.T.exists_aeval_pairings_eq_of_invariant X.Ψ n r hn R hR
  have hF : Differentiable ℂ fun w : Ell X.Ψ n r → ℂ => D (dblZ X x₁ x₂)
      (fun τ => Matrix.of fun k a => w (τ, false, k, a))
      (fun τ => Matrix.of fun k a => w (τ, true, k, a)) := by
    have h := hD.1.comp (f := fun w : Ell X.Ψ n r → ℂ => ((dblZ X x₁ x₂,
      fun τ k a => w (τ, false, k, a), fun τ k a => w (τ, true, k, a)) :
        CF X.Ψ r r × CF X.Ψ n r × CF X.Ψ n r)) (s := Set.univ) (by fun_prop) fun _ _ => hZ
    exact differentiableOn_univ.1 h
  refine Eq.trans ?_ ((hR' _ hF).trans ?_)
  · simp only [biDeriv, kZero, dblz_eq, dblz'_eq]
    rfl
  · convert GlobalTheory.T.polyDeriv_aeval_pairings_eq_zero_of_isHeat E X.Ψ n r D hD h0 _ hZ s

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolyDerivKillsDoubledHeatSolutionStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_polyDeriv_kills_doubled_heat_solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), r ≤ n → InvFam P → ∀ D : CM X.Ψ r r → CM X.Ψ n r → CM X.Ψ n r → ℂ, IsHeat X.Ψ D → (∀ Z ∈ Hn X.Ψ r, D Z 0 0 = 0) → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, biDeriv X hr idx P (fun z₁ w => kZero X idx x₁ x₂ z₁ w * D (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)) = 0 := by
  first | exact @GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero | exact GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero | (intros; apply GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero <;> assumption)
end
