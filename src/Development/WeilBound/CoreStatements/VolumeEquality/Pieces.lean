module

public import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGroupDictionary

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFundamentalSet
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFundamentalSet
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace ComplexOrder

theorem isOpen_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    IsOpen (ballDom q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  refine Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
    (fun t : Fin n → ℂ => 1 - (ballMat q t τ)ᴴ * ballMat q t τ) (fun a b => ?_) (fun t => ?_) x0 (hx0 τ)
  · simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, ballMat, Matrix.of_apply]
    exact continuous_const.sub (continuous_finsetSum _ fun c _ =>
      (continuous_star.comp (continuous_apply _)).mul (continuous_apply _))
  · have : (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᴴ = 1 - (ballMat q t τ)ᴴ * ballMat q t τ := by
      simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    exact this

theorem exists_transversal {α ι : Type*} [MeasurableSpace α] [Countable ι] (X : Set α)
    (hX : MeasurableSet X) (A : ι → α → α) (hA : ∀ i, Measurable (A i)) (ψ : α → ℝ)
    (hψ : Measurable ψ) (hinj : Set.InjOn ψ X) (Rel : α → α → Prop)
    (hmaps : ∀ i, Set.MapsTo (A i) X X)
    (hrel : ∀ t ∈ X, ∀ t' ∈ X, Rel t t' ↔ ∃ i, t' = A i t)
    (hrefl : ∀ t ∈ X, Rel t t) (hsymm : ∀ t t', Rel t t' → Rel t' t)
    (htrans : ∀ t t' t'', Rel t t' → Rel t' t'' → Rel t t'')
    (hfin : ∀ t ∈ X, ∀ c : ℝ, {i | ψ (A i t) ≤ c}.Finite) :
    ∃ FF : Set α, MeasurableSet FF ∧ FF ⊆ X ∧ (∀ t ∈ X, ∃ t' ∈ FF, Rel t t') ∧
      ∀ t ∈ FF, ∀ t' ∈ FF, Rel t t' → t = t' := by
  refine ⟨X ∩ ⋂ i, {t | ψ t ≤ ψ (A i t)}, ?_, Set.inter_subset_left, ?_, ?_⟩
  · exact hX.inter (MeasurableSet.iInter fun i => measurableSet_le hψ (hψ.comp (hA i)))
  · intro t ht
    obtain ⟨i₀, hi₀⟩ := (hrel t ht t ht).1 (hrefl t ht)
    have hne : {i | ψ (A i t) ≤ ψ t}.Nonempty := ⟨i₀, by simp [← hi₀]⟩
    obtain ⟨i, hi, hmin⟩ := Set.exists_min_image _ (fun i => ψ (A i t)) (hfin t ht (ψ t)) hne
    have hmin' : ∀ k, ψ (A i t) ≤ ψ (A k t) := fun k => by
      by_cases hk : ψ (A k t) ≤ ψ t
      · exact hmin k hk
      · exact le_trans hi (le_of_not_ge hk)
    have hit : A i t ∈ X := hmaps i ht
    have hR : Rel t (A i t) := (hrel t ht _ hit).2 ⟨i, rfl⟩
    refine ⟨A i t, ⟨hit, Set.mem_iInter.2 fun k => ?_⟩, hR⟩
    have h1 : Rel (A i t) (A k (A i t)) := (hrel _ hit _ (hmaps k hit)).2 ⟨k, rfl⟩
    obtain ⟨l, hl⟩ := (hrel t ht _ (hmaps k hit)).1 (htrans _ _ _ hR h1)
    show ψ (A i t) ≤ ψ (A k (A i t))
    rw [hl]
    exact hmin' l
  · rintro t ⟨ht, htm⟩ t' ⟨ht', htm'⟩ hR
    obtain ⟨i, hi⟩ := (hrel t ht t' ht').1 hR
    obtain ⟨k, hk⟩ := (hrel t' ht' t ht).1 (hsymm _ _ hR)
    have h1 : ψ t ≤ ψ t' := by
      have : ψ t ≤ ψ (A i t) := Set.mem_iInter.1 htm i
      rwa [← hi] at this
    have h2 : ψ t' ≤ ψ t := by
      have : ψ t' ≤ ψ (A k t') := Set.mem_iInter.1 htm' k
      rwa [← hk] at this
    exact hinj ht ht' (le_antisymm h1 h2)

section Lat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem RiemLat.quad_nonneg (R : RiemLat E g Λ) (z : Fin g → ℂ) : 0 ≤ (z ⬝ᵥ R.Hm *ᵥ star z).re := by
  by_cases hz : z = 0
  · simp [hz]
  · exact (R.pos z hz).le

theorem RiemLat.normSq_nonneg (R : RiemLat E g Λ) (x : Λ) : 0 ≤ R.normSq x := R.quad_nonneg _

theorem RiemLat.form_antisymm (R : RiemLat E g Λ) (x y : Λ) : R.form y x = - R.form x y := by
  have h := R.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, R.alt] at h
  linarith

theorem RiemLat.form_sq_le (R : RiemLat E g Λ) (x y : Λ) :
    ((R.form x y : ℤ) : ℝ) ^ 2 ≤ R.normSq x * R.normSq y := by
  set z := R.P x
  set w := R.P y
  have key : ∀ s : ℝ, 0 ≤ R.normSq y * (s * s) + (2 * (R.form x y : ℤ) : ℝ) * s + R.normSq x := by
    intro s
    have h := R.quad_nonneg (z + ((s : ℂ) * Complex.I) • w)
    have e1 : (z ⬝ᵥ R.Hm *ᵥ star z).re = R.normSq x := rfl
    have e2 : (w ⬝ᵥ R.Hm *ᵥ star w).re = R.normSq y := rfl
    have e3 : (z ⬝ᵥ R.Hm *ᵥ star w).im = (R.form x y : ℤ) := R.im x y
    have e4 : (w ⬝ᵥ R.Hm *ᵥ star z).im = (R.form y x : ℤ) := R.im y x
    rw [R.form_antisymm x y] at e4
    have hexp : (z + ((s : ℂ) * Complex.I) • w) ⬝ᵥ R.Hm *ᵥ star (z + ((s : ℂ) * Complex.I) • w) =
        (z ⬝ᵥ R.Hm *ᵥ star z) + (-(s : ℂ) * Complex.I) * (z ⬝ᵥ R.Hm *ᵥ star w) +
          ((s : ℂ) * Complex.I) * (w ⬝ᵥ R.Hm *ᵥ star z) + (s : ℂ) ^ 2 * (w ⬝ᵥ R.Hm *ᵥ star w) := by
      simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal,
        Complex.conj_I]
      have hI := Complex.I_mul_I
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [hexp] at h
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im, e1, e2, e3, e4, sq] at h
    push_cast at h
    nlinarith [h]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

theorem RiemLat.finite_normSq_le (R : RiemLat E g Λ) (c : ℝ) : {x | R.normSq x ≤ c}.Finite := by
  haveI := R.free
  haveI := R.fin
  let b := Module.Free.chooseBasis ℤ Λ
  let ι := Module.Free.ChooseBasisIndex ℤ Λ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : ι, c * R.normSq (b i) ≤ (N : ℝ) ^ 2 := by
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ i : ι, |c * R.normSq (b i)| + 1)
    refine ⟨N, fun i => ?_⟩
    have h1 : |c * R.normSq (b i)| ≤ ∑ i : ι, |c * R.normSq (b i)| :=
      Finset.single_le_sum (f := fun i : ι => |c * R.normSq (b i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := le_abs_self (c * R.normSq (b i))
    have h3 : (0 : ℝ) ≤ ∑ i : ι, |c * R.normSq (b i)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    nlinarith
  have hfin : (Set.pi Set.univ fun _ : ι => Set.Icc (-(N : ℤ)) N).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine Set.Finite.of_finite_image (f := fun x (i : ι) => R.form x (b i)) (hfin.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩ i -
    have h1 := R.form_sq_le x (b i)
    have h2 : R.normSq x * R.normSq (b i) ≤ c * R.normSq (b i) :=
      mul_le_mul_of_nonneg_right hx (R.normSq_nonneg _)
    have h3 : ((R.form x (b i) : ℤ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := h1.trans (h2.trans (hN i))
    have h4 := abs_le.1 (abs_le_of_sq_le_sq h3 (by positivity))
    constructor
    · have := h4.1
      exact_mod_cast this
    · have := h4.2
      exact_mod_cast this
  · intro x _ y _ hxy
    refine R.unimod.1 (b.ext fun i => ?_)
    exact congrFun hxy i

theorem RiemLat.left_inv_gram (R : RiemLat E g Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ Λ) :
    ∃ Y : Matrix ι ι ℂ, Y * (Matrix.of fun i j => ((R.form (b i) (b j) : ℤ) : ℂ)) = 1 := by
  choose y hy using fun i => R.unimod.2 (b.coord i)
  refine ⟨Matrix.of fun i k => ((b.repr (y i) k : ℤ) : ℂ), ?_⟩
  ext i j
  have h1 : R.form (y i) (b j) = ∑ k, b.repr (y i) k * R.form (b k) (b j) := by
    have e : R.form (∑ k, b.repr (y i) k • b k) (b j) = ∑ k, b.repr (y i) k * R.form (b k) (b j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rwa [b.sum_repr] at e
  have h2 : R.form (y i) (b j) = if i = j then 1 else 0 := by
    rw [hy i]
    simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
  have h3 := congrArg (fun z : ℤ => (z : ℂ)) (h1.symm.trans h2)
  simp only [Int.cast_sum, Int.cast_mul] at h3
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [h3]
  split_ifs <;> simp

def RiemLat.perMat (R : RiemLat E g Λ) {ι : Type} (b : ι → Λ) : Matrix (Fin g) ι ℂ :=
  Matrix.of fun a i => R.P (b i) a

theorem RiemLat.riemann_rel (R : RiemLat E g Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → Λ) (hc : Fintype.card ι = Fintype.card (Fin g ⊕ Fin g)) (Y : Matrix ι ι ℂ)
    (hY : Y * (Matrix.of fun i j => ((R.form (b i) (b j) : ℤ) : ℂ)) = 1) :
    (R.perMat b * Y * (R.perMat b)ᴴ) * R.Hmᵀ = (-2 * Complex.I) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  set Q := R.perMat b with hQ
  set Qb : Matrix (Fin g) ι ℂ := Q.map (starRingEnd ℂ) with hQb
  set S : Matrix ι ι ℂ := Qᵀ * R.Hm * Qb with hS
  have hSe : ∀ i j, S i j = R.P (b i) ⬝ᵥ R.Hm *ᵥ star (R.P (b j)) := by
    intro i j
    simp only [hS, hQb, hQ, Matrix.mul_apply, dotProduct, mulVec, RiemLat.perMat, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    simp [mul_assoc]
  have hSc : Qᴴ * R.Hmᵀ * Q = S.map (starRingEnd ℂ) := by
    have hH : R.Hm.map (starRingEnd ℂ) = R.Hmᵀ := by
      have := R.herm
      ext a c
      have h := this.apply c a
      simpa using h
    have : S.map (starRingEnd ℂ) = (Qᵀ).map (starRingEnd ℂ) * R.Hm.map (starRingEnd ℂ) * Qb.map (starRingEnd ℂ) := by
      rw [hS, Matrix.map_mul, Matrix.map_mul]
    rw [this, hH]
    congr 2
    ext a c; simp [hQb]
  have hdiff : S - S.map (starRingEnd ℂ) =
      (2 * Complex.I) • (Matrix.of fun i j => ((R.form (b i) (b j) : ℤ) : ℂ)) := by
    ext i j
    have h := R.im (b i) (b j)
    rw [← hSe] at h
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    have key : ∀ w : ℂ, w - (starRingEnd ℂ) w = 2 * Complex.I * ((w.im : ℝ) : ℂ) := by
      intro w
      apply Complex.ext <;> simp <;> ring
    have h5 := key (S i j)
    rw [h] at h5
    simpa using h5
  set c : ℂ := 2 * Complex.I with hcdef
  have hc0 : c ≠ 0 := by simp [hcdef]
  have h1 : Matrix.fromCols (c⁻¹ • (Y * Qᵀ * R.Hm)) (-(c⁻¹ • (Y * Qᴴ * R.Hmᵀ))) * Matrix.fromRows Qb Q = 1 := by
    rw [Matrix.fromCols_mul_fromRows]
    have : Y * (S - S.map (starRingEnd ℂ)) = c • 1 := by rw [hdiff, Matrix.mul_smul, hY]
    rw [← hSc, hS, Matrix.mul_sub] at this
    simp only [Matrix.smul_mul, Matrix.neg_mul]
    rw [← sub_eq_add_neg, ← smul_sub]
    have e : Y * Qᵀ * R.Hm * Qb - Y * Qᴴ * R.Hmᵀ * Q = c • 1 := by
      rw [← this]; simp only [Matrix.mul_assoc]
    rw [e, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).1 h1
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one] at h2
  have h3 := (Matrix.fromBlocks_inj.1 h2).2.2.2
  have h4 : Q * (Y * Qᴴ * R.Hmᵀ) = (-c) • 1 := by
    have := congrArg (fun M => (-c) • M) h3
    simp only [Matrix.mul_neg, Matrix.mul_smul, smul_neg, neg_smul, smul_smul] at this
    simpa [mul_inv_cancel₀ hc0] using this
  rw [show (-2 * Complex.I) = -c by simp [hcdef]]
  rw [← h4]
  simp only [Matrix.mul_assoc]

theorem continuousOn_normSq_of_holomorphic_family {n : ℕ} {U : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ}
    (hR : IsHolFam U R) (x : Λ) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ U) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ Λ) : ContinuousOn (fun t => (R t).normSq x) U := by
  haveI := (R t₀).fin
  obtain ⟨Y, hY⟩ := (R t₀).left_inv_gram b
  have hc : Fintype.card ι = Fintype.card (Fin g ⊕ Fin g) := by
    have := (R t₀).rank
    rw [Module.finrank_eq_card_basis b] at this
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hPc : ∀ y, Continuous fun t : U => (R t).P y := fun y =>
    continuousOn_iff_continuous_restrict.1 (hR.2 y).continuousOn
  have hrel : ∀ t : U, ((R t).perMat b * Y * ((R t).perMat b)ᴴ) * (R t).Hmᵀ =
      (-2 * Complex.I) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
    intro t
    refine (R t).riemann_rel b hc Y ?_
    rw [hR.1 t t.2 t₀ ht₀]
    exact hY
  let N : U → Matrix (Fin g) (Fin g) ℂ := fun t => (R t).perMat b * Y * ((R t).perMat b)ᴴ
  have hQc : Continuous fun t : U => (R t).perMat b :=
    continuous_matrix fun a i => (continuous_apply a).comp (hPc (b i))
  have hNc : Continuous N := (hQc.matrix_mul continuous_const).matrix_mul hQc.matrix_conjTranspose
  set c : ℂ := -2 * Complex.I with hcdef
  have hc0 : c ≠ 0 := by simp [hcdef]
  have hinv : ∀ t : U, (R t).Hm = (c • (N t)⁻¹)ᵀ := by
    intro t
    have h1 : N t * (c⁻¹ • (R t).Hmᵀ) = 1 := by
      rw [Matrix.mul_smul, hrel t, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [Matrix.inv_eq_right_inv h1, smul_smul, mul_inv_cancel₀ hc0, one_smul, Matrix.transpose_transpose]
  have hdet : ∀ t : U, (N t).det ≠ 0 := by
    intro t h0
    have h1 := congrArg Matrix.det (hrel t)
    rw [Matrix.det_mul] at h1
    change (N t).det * _ = _ at h1
    rw [h0, zero_mul, Matrix.det_smul, Matrix.det_one] at h1
    exact (mul_ne_zero (pow_ne_zero _ hc0) one_ne_zero) h1.symm
  have hNi : Continuous fun t : U => (N t)⁻¹ := by
    have : (fun t : U => (N t)⁻¹) = fun t => ((N t).det)⁻¹ • (N t).adjugate := by
      funext t
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    exact (hNc.matrix_det.inv₀ hdet).smul hNc.matrix_adjugate
  have hHc : Continuous fun t : U => (R t).Hm := by
    have : (fun t : U => (R t).Hm) = fun t => (c • (N t)⁻¹)ᵀ := funext hinv
    rw [this]
    exact (hNi.const_smul c).matrix_transpose
  rw [continuousOn_iff_continuous_restrict]
  change Continuous fun t : U => ((R t).P x ⬝ᵥ (R t).Hm *ᵥ star ((R t).P x)).re
  exact Complex.continuous_re.comp ((hPc x).dotProduct (hHc.matrix_mulVec (hPc x).star))

theorem continuousOn_normSq {n : ℕ} {U : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ}
    (hR : IsHolFam U R) (x : Λ) : ContinuousOn (fun t => (R t).normSq x) U := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · simp
  haveI := (R t₀).free
  haveI := (R t₀).fin
  classical
  exact continuousOn_normSq_of_holomorphic_family hR x ht₀ (Module.Free.chooseBasis ℤ Λ)

end Lat

section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem RiemLat.eqvBy_refl (R : RiemLat E g Λ) : R.EqvBy R 1 := ⟨LinearEquiv.refl _ _, fun _ => rfl⟩

theorem RiemLat.EqvBy.symm {R R' : RiemLat E g Λ} {γ : Λ ≃ₗ[𝓞 E] Λ} (h : R.EqvBy R' γ) : R'.EqvBy R γ⁻¹ := by
  obtain ⟨h₀, hx⟩ := h
  refine ⟨h₀.symm, fun x => ?_⟩
  have h1 := hx (γ⁻¹ x)
  have h2 : γ (γ⁻¹ x) = x := γ.apply_symm_apply x
  rw [h2] at h1
  rw [h1, LinearEquiv.symm_apply_apply]

theorem RiemLat.EqvBy.trans {R R' R'' : RiemLat E g Λ} {γ γ' : Λ ≃ₗ[𝓞 E] Λ} (h : R.EqvBy R' γ)
    (h' : R'.EqvBy R'' γ') : R.EqvBy R'' (γ' * γ) := by
  obtain ⟨h₀, hx⟩ := h
  obtain ⟨h₁, hy⟩ := h'
  exact ⟨h₀.trans h₁, fun x => (hy (γ x)).trans (congrArg h₁ (hx x))⟩

end Main

theorem exists_isFundSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (F : UnivFam (E := E) Ψ j j' n g Λ)
    (Δ : _root_.GlobalTheory.CompanionTheory.Ar.Cusp.GroupDict F)
    (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)), F.IsArith Γ → ∃ FF, F.IsFundSet Γ FF := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F Δ Γ hΓ
  classical
  have hXo : IsOpen (ballDom F.q) := isOpen_ballDom F.q
  have hXm : MeasurableSet (ballDom F.q) := hXo.measurableSet
  haveI := (F.R (Δ.π 1)).free
  haveI := (F.R (Δ.π 1)).fin
  let b := Module.Free.chooseBasis ℤ Λ
  let u : (Fin n → ℂ) → ℝ := fun t => ∑ i, (F.R t).normSq (b i)
  have huc : ContinuousOn u (ballDom F.q) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_normSq F.hol (b i)
  haveI : Countable Λ := b.repr.toEquiv.injective.countable
  have hext : ∀ γ γ' : Λ ≃ₗ[𝓞 E] Λ, (∀ i, γ (b i) = γ' (b i)) → γ = γ' := by
    intro γ γ' h
    have h1 := b.ext (f₁ := (γ : Λ →ₗ[𝓞 E] Λ).toAddMonoidHom.toIntLinearMap)
      (f₂ := (γ' : Λ →ₗ[𝓞 E] Λ).toAddMonoidHom.toIntLinearMap) h
    exact LinearEquiv.ext fun x => LinearMap.congr_fun h1 x
  haveI : Countable (Λ ≃ₗ[𝓞 E] Λ) :=
    Function.Injective.countable (f := fun (γ : Λ ≃ₗ[𝓞 E] Λ) i => γ (b i))
      fun γ γ' h => hext γ γ' fun i => congrFun h i
  let δ : Γ → latticeStab Δ.h Δ.e.range := fun γ => Δ.α.symm ⟨γ.1, hΓ.1 γ.2⟩
  have hαδ : ∀ γ : Γ, (Δ.α (δ γ)).1 = γ.1 := fun γ => by simp [δ]
  let a₀ : Γ → archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))) := fun γ =>
    archEmbed Δ.h (Pi.basisFun E (Fin (j + j'))) (δ γ)
  choose A G hAd hGd hAπ hpot using Δ.act
  let B : Γ → (Fin n → ℂ) → Fin n → ℂ := fun γ => A (a₀ γ)
  have hBπ : ∀ γ a, Δ.π (a₀ γ * a) = B γ (Δ.π a) := fun γ a => hAπ _ a
  have hmemπ : ∀ a, Δ.π a ∈ ballDom F.q := fun a => Δ.π_range ▸ Set.mem_range_self a
  have hsurj : ∀ t ∈ ballDom F.q, ∃ a, Δ.π a = t := fun t ht => by
    rw [← Δ.π_range] at ht
    exact ht
  have hBX : ∀ γ, Set.MapsTo (B γ) (ballDom F.q) (ballDom F.q) := by
    intro γ t ht
    obtain ⟨a, rfl⟩ := hsurj t ht
    rw [← hBπ]
    exact hmemπ _
  have hBc : ∀ γ, ContinuousOn (B γ) (ballDom F.q) := fun γ => (hAd _).continuousOn
  have hact : ∀ (γ : Γ) t, t ∈ ballDom F.q → (F.R t).EqvBy (F.R (B γ t)) γ.1 := by
    intro γ t ht
    obtain ⟨a, rfl⟩ := hsurj t ht
    have h := Δ.α_act (δ γ) a
    rw [hαδ] at h
    rw [← hBπ]
    exact h
  have hiso : ∀ (γ : Γ) t, t ∈ ballDom F.q → ∀ x, (F.R (B γ t)).normSq (γ.1 x) = (F.R t).normSq x := by
    intro γ t ht x
    obtain ⟨a, rfl⟩ := hsurj t ht
    rw [← hBπ, Δ.len, Δ.len]
    have h1 := Δ.α_eq (δ γ) x
    rw [hαδ] at h1
    rw [h1]
    have h2 := invApply_archEmbed_mul Δ.h (Pi.basisFun E (Fin (j + j'))) (δ γ : Δ.h.unitaryGroup) a (Δ.e x)
    exact congrArg (fun y => Δ.κ * Δ.M.len y ^ 2) h2
  have hrel : ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv Γ t t' ↔ ∃ γ : Γ, t' = B γ t := by
    intro t ht t' ht'
    constructor
    · rintro ⟨γ, hγ, h⟩
      refine ⟨⟨γ, hγ⟩, ?_⟩
      have h1 := hact ⟨γ, hγ⟩ t ht
      have h2 : (F.R (B ⟨γ, hγ⟩ t)).EqvBy (F.R t') 1 := by
        have h3 := h1.symm.trans h
        simpa using h3
      exact (F.univ (F.R t') (F.form_eq t') (F.sig t' ht')).unique ⟨ht', (F.R t').eqvBy_refl⟩
        ⟨hBX _ ht, h2⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ.1, γ.2, hact γ t ht⟩
  have hfinu : ∀ t ∈ ballDom F.q, ∀ c : ℝ, {γ : Γ | u (B γ t) ≤ c}.Finite := by
    intro t ht c
    have hS := (F.R t).finite_normSq_le c
    have hfinp : (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ Λ =>
        {x | (F.R t).normSq x ≤ c}).Finite := Set.Finite.pi fun _ => hS
    refine Set.Finite.of_finite_image (f := fun (γ : Γ) i => (γ⁻¹ : Γ).1 (b i)) (hfinp.subset ?_) ?_
    · rintro _ ⟨γ, hγ, rfl⟩ i -
      have h1 := hiso γ t ht ((γ⁻¹ : Γ).1 (b i))
      have h2 : γ.1 ((γ⁻¹ : Γ).1 (b i)) = b i := γ.1.apply_symm_apply _
      rw [h2] at h1
      show (F.R t).normSq ((γ⁻¹ : Γ).1 (b i)) ≤ c
      rw [← h1]
      exact (Finset.single_le_sum (f := fun i => (F.R (B γ t)).normSq (b i))
        (fun _ _ => RiemLat.normSq_nonneg _ _) (Finset.mem_univ i)).trans hγ
    · intro γ _ γ' _ h
      have h1 : (γ⁻¹ : Γ).1 = (γ'⁻¹ : Γ).1 := hext _ _ fun i => congrFun h i
      exact inv_injective (Subtype.ext h1)
  obtain ⟨φ, hφ⟩ := exists_measurableEmbedding_real (Fin n → ℂ)
  let ũ : (Fin n → ℂ) → ℝ := (ballDom F.q).piecewise u 0
  have hũ : Measurable ũ := huc.measurable_piecewise continuousOn_const hXm
  let ψ : (Fin n → ℂ) → ℝ := fun t => 4 * (⌈ũ t⌉₊ : ℝ) + Real.arctan (φ t)
  have hψ : Measurable ψ :=
    (measurable_const.mul (measurable_from_nat.comp (Nat.measurable_ceil.comp hũ))).add
      (Real.measurable_arctan.comp hφ.measurable)
  have hψinj : Function.Injective ψ := by
    intro t t' h
    have hb := Real.arctan_lt_pi_div_two (φ t)
    have hb' := Real.arctan_lt_pi_div_two (φ t')
    have hc := Real.neg_pi_div_two_lt_arctan (φ t)
    have hc' := Real.neg_pi_div_two_lt_arctan (φ t')
    have hpi := Real.pi_lt_four
    simp only [ψ] at h
    have hn : ⌈ũ t⌉₊ = ⌈ũ t'⌉₊ := by
      rcases lt_trichotomy ⌈ũ t⌉₊ ⌈ũ t'⌉₊ with h1 | h1 | h1
      · have : (⌈ũ t⌉₊ : ℝ) + 1 ≤ ⌈ũ t'⌉₊ := by exact_mod_cast h1
        linarith
      · exact h1
      · have : (⌈ũ t'⌉₊ : ℝ) + 1 ≤ ⌈ũ t⌉₊ := by exact_mod_cast h1
        linarith
    rw [hn] at h
    exact hφ.injective (Real.arctan_injective (by linarith))
  let B' : Γ → (Fin n → ℂ) → Fin n → ℂ := fun γ => (ballDom F.q).piecewise (B γ) id
  have hB' : ∀ γ t, t ∈ ballDom F.q → B' γ t = B γ t := fun γ t ht => Set.piecewise_eq_of_mem _ _ _ ht
  obtain ⟨FF, h1, h2, h3, h4⟩ := exists_transversal (ι := Γ) (ballDom F.q) hXm B'
    (fun γ => (hBc γ).measurable_piecewise continuousOn_id hXm) ψ hψ hψinj.injOn (F.Eqv Γ)
    (fun γ t ht => by rw [hB' γ t ht]; exact hBX γ ht)
    (fun t ht t' ht' => by
      rw [hrel t ht t' ht']
      exact exists_congr fun γ => by rw [hB' γ t ht])
    (fun t _ => ⟨1, Γ.one_mem, (F.R t).eqvBy_refl⟩)
    (fun t t' ⟨γ, hγ, h⟩ => ⟨γ⁻¹, Γ.inv_mem hγ, h.symm⟩)
    (fun t t' t'' ⟨γ, hγ, h⟩ ⟨γ', hγ', h'⟩ => ⟨γ' * γ, Γ.mul_mem hγ' hγ, h.trans h'⟩)
    (fun t ht c => by
      refine (hfinu t ht (c + 2)).subset fun γ hγ => ?_
      have hγ' : ψ (B' γ t) ≤ c := hγ
      rw [hB' γ t ht] at hγ'
      have hs := hBX γ ht
      have hu : ũ (B γ t) = u (B γ t) := Set.piecewise_eq_of_mem _ _ _ hs
      have hc := Real.neg_pi_div_two_lt_arctan (φ (B γ t))
      have hpi := Real.pi_lt_four
      have hle := Nat.le_ceil (ũ (B γ t))
      have hnn : (0 : ℝ) ≤ ⌈ũ (B γ t)⌉₊ := Nat.cast_nonneg _
      simp only [ψ] at hγ'
      show u (B γ t) ≤ c + 2
      rw [← hu]
      linarith)
  exact ⟨FF, h1, h2, h3, h4⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFundamentalSetStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamental_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)), F.IsArith Γ → ∃ FF, F.IsFundSet Γ FF := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.exists_isFundSet | exact GlobalTheory.CompanionTheory.Ar.Cusp.exists_isFundSet | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.exists_isFundSet <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.RootBr
noncomputable section

namespace SheetDecomposition

open Filter Topology Polynomial

theorem eval_monicOf {d : ℕ} (a : Fin d → ℂ) (x : ℂ) : (monicOf a).eval x = x ^ d + ∑ i, a i * x ^ (i : ℕ) := by
  simp [monicOf, eval_finsetSum]

theorem degree_low_lt {d : ℕ} (a : Fin d → ℂ) : (∑ i, C (a i) * X ^ (i : ℕ) : ℂ[X]).degree < d :=
  degree_sum_fin_lt a

theorem monic_monicOf {d : ℕ} (a : Fin d → ℂ) : (monicOf a).Monic :=
  monic_X_pow_add (degree_low_lt a)

theorem natDegree_monicOf {d : ℕ} (a : Fin d → ℂ) : (monicOf a).natDegree = d := by
  apply natDegree_eq_of_degree_eq_some
  unfold monicOf
  rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  exact degree_low_lt a

theorem root_branch {d : ℕ} (a₀ : Fin d → ℂ) (x₀ : ℂ) (h0 : (monicOf a₀).IsRoot x₀)
    (h1 : (derivative (monicOf a₀)).eval x₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, ψ a₀ = x₀ ∧ ∀ᶠ a in 𝓝 a₀, DifferentiableAt ℂ ψ a ∧ (monicOf a).IsRoot (ψ a) := by
  set f : (Fin d → ℂ) × ℂ → ℂ := fun u => u.2 ^ d + ∑ i, u.1 i * u.2 ^ (i : ℕ) with hf
  have cdf : ContDiffAt ℂ 1 f (a₀, x₀) := by
    rw [hf]
    fun_prop
  have hD : fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ ((derivative (monicOf a₀)).eval x₀) := by
    have e1 : HasFDerivAt (f ∘ fun x : ℂ => (a₀, x))
        (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) x₀ :=
      HasFDerivAt.comp x₀ (cdf.differentiableAt one_ne_zero).hasFDerivAt (hasFDerivAt_prodMk_right a₀ x₀)
    have e2 : (f ∘ fun x : ℂ => (a₀, x)) = fun x => (monicOf a₀).eval x := by
      funext x
      simp [hf, eval_monicOf]
    rw [e2] at e1
    exact e1.unique ((monicOf a₀).hasDerivAt x₀).hasFDerivAt
  have if₂ : (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hD]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext
    simp
  refine ⟨cdf.implicitFunction one_ne_zero if₂, cdf.implicitFunction_apply_self one_ne_zero if₂, ?_⟩
  have hc := cdf.contDiffAt_implicitFunction one_ne_zero if₂
  have hv := cdf.eventually_apply_implicitFunction one_ne_zero if₂
  filter_upwards [hc.eventually (by simp), hv] with a ha hb
  refine ⟨ha.differentiableAt one_ne_zero, ?_⟩
  have : f (a₀, x₀) = 0 := by
    have := h0
    rw [IsRoot.def, eval_monicOf] at this
    exact this
  rw [this] at hb
  rw [IsRoot.def, eval_monicOf]
  exact hb

theorem root_iff_of_injective {d : ℕ} (a : Fin d → ℂ) (r : Fin d → ℂ) (hr : Function.Injective r)
    (h : ∀ i, (monicOf a).IsRoot (r i)) (x : ℂ) : (monicOf a).IsRoot x ↔ ∃ i, x = r i := by
  classical
  refine ⟨fun hx => ?_, fun ⟨i, hi⟩ => hi ▸ h i⟩
  by_contra hne
  push Not at hne
  have hsub : insert x (Finset.univ.image r) ⊆ (monicOf a).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact h i
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
    intro hz
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz
    exact hne i hi.symm), Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := (Multiset.toFinset_card_le (monicOf a).roots).trans (card_roots' (monicOf a))
  rw [natDegree_monicOf] at h2
  omega

theorem exists_roots {d : ℕ} (a : Fin d → ℂ) (hs : (monicOf a).Separable) :
    ∃ r : Fin d → ℂ, Function.Injective r ∧ ∀ i, (monicOf a).IsRoot (r i) := by
  classical
  have hc : (monicOf a).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree, natDegree_monicOf]
  let e := Finset.equivFinOfCardEq hc
  refine ⟨fun i => (e.symm i : ℂ), Subtype.val_injective.comp e.symm.injective, fun i => ?_⟩
  have := (e.symm i).2
  rw [Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero] at this
  exact this

theorem rootBranches : RootBranches := by
  intro n d T a hT ha hs t₀ ht₀
  obtain ⟨r, hr, hroot⟩ := exists_roots (a t₀) (hs t₀ ht₀)
  have hder : ∀ i, (derivative (monicOf (a t₀))).eval (r i) ≠ 0 := fun i => by
    have := (hs t₀ ht₀).aeval_derivative_ne_zero (x := r i) (by simpa using hroot i)
    simpa using this
  choose ψ hψ0 hψ using fun i => root_branch (a t₀) (r i) (hroot i) (hder i)
  have hca : ContinuousAt a t₀ := (ha.differentiableAt (hT.mem_nhds ht₀)).continuousAt
  have hcθ : ∀ i, ContinuousAt (fun t => ψ i (a t)) t₀ := fun i =>
    ContinuousAt.comp (f := a) (hψ i).self_of_nhds.1.continuousAt hca
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ T ∧ (∀ i, DifferentiableAt ℂ (ψ i) (a t) ∧ (monicOf (a t)).IsRoot (ψ i (a t))) ∧
      ∀ i j, i ≠ j → ψ i (a t) ≠ ψ j (a t) := by
    refine (hT.eventually_mem ht₀).and (Eventually.and (eventually_all.mpr fun i => hca.tendsto.eventually (hψ i)) ?_)
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    · have : ∀ᶠ t in 𝓝 t₀, ψ i (a t) - ψ j (a t) ≠ 0 :=
        ((hcθ i).sub (hcθ j)).eventually_ne (by
          show ψ i (a t₀) - ψ j (a t₀) ≠ 0
          rw [hψ0, hψ0]
          exact sub_ne_zero.mpr (hr.ne hij))
      filter_upwards [this] with t ht _ using sub_ne_zero.mp ht
  obtain ⟨V, hV, hVo, hVt⟩ := eventually_nhds_iff.mp hev
  refine ⟨V, fun i t => ψ i (a t), hVo, hVt, fun t ht => (hV t ht).1, fun i t ht => ?_, fun t ht => ?_⟩
  · exact (((hV t ht).2.1 i).1.comp t (ha.differentiableAt (hT.mem_nhds (hV t ht).1))).differentiableWithinAt
  · have hi : Function.Injective fun i => ψ i (a t) := fun i j h => by
      by_contra hij
      exact (hV t ht).2.2 i j hij h
    exact ⟨hi, root_iff_of_injective (a t) _ hi fun i => ((hV t ht).2.1 i).2⟩

end SheetDecomposition
end
end

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Polynomial Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem cover_seq {α : Type} [TopologicalSpace α] [SecondCountableTopology α] (T : Set α) (P : Set α → Prop) (h0 : P ∅)
    (h : ∀ t ∈ T, ∃ V, IsOpen V ∧ t ∈ V ∧ P V) : ∃ W : ℕ → Set α, (∀ m, IsOpen (W m) ∧ P (W m)) ∧ T ⊆ ⋃ m, W m := by
  obtain ⟨S, hc, hs, he⟩ := TopologicalSpace.isOpen_sUnion_countable {V | IsOpen V ∧ P V} fun _ hV => hV.1
  obtain ⟨W, hW⟩ := (hc.insert ∅).exists_eq_range (Set.insert_nonempty _ _)
  refine ⟨W, fun m => ?_, fun t ht => ?_⟩
  · rcases (hW ▸ Set.mem_range_self m : W m ∈ insert ∅ S) with e | e
    · exact e ▸ ⟨isOpen_empty, h0⟩
    · exact hs e
  · obtain ⟨V, h1, h2, h3⟩ := h t ht
    obtain ⟨V', hV', ht'⟩ : t ∈ ⋃₀ S := he ▸ ⟨V, ⟨h1, h3⟩, h2⟩
    obtain ⟨m, rfl⟩ : V' ∈ Set.range W := hW ▸ Set.mem_insert_of_mem _ hV'
    exact Set.mem_iUnion.2 ⟨m, ht'⟩

theorem ballDom_preconnected {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) : _root_.IsPreconnected (GlobalTheory.CompanionTheory.Ar.Cusp.ballDom q) := by
  have hs : StarConvex ℝ 0 (GlobalTheory.CompanionTheory.Ar.Cusp.ballDom q) := fun t ht a b ha hb hab τ => by
    have e : GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q (a • (0 : Fin n → ℂ) + b • t) τ = (b : ℂ) • GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q t τ := by
      ext x y
      simp [GlobalTheory.CompanionTheory.Ar.Cusp.ballMat]
    have e2 : 1 - (GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q (a • (0 : Fin n → ℂ) + b • t) τ)ᴴ * GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q (a • (0 : Fin n → ℂ) + b • t) τ =
        (1 - (GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q t τ)ᴴ * GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q t τ) + ((1 - b ^ 2 : ℝ) : ℂ) • ((GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q t τ)ᴴ * GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q t τ) := by
      rw [e, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      push_cast
      module
    rw [e2]
    exact (ht τ).add_posSemidef ((posSemidef_conjTranspose_mul_self _).smul (Complex.zero_le_real.2 (by nlinarith)))
  refine (hs.isPathConnected fun τ => ?_).isConnected.isPreconnected
  rw [show GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q 0 τ = 0 from rfl, Matrix.mul_zero, sub_zero]
  exact PosDef.one

theorem isOpen_of_holTo {X : Scheme.{0}} {n : ℕ} {B : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (h : IsHolTo B y) : IsOpen B := by
  simpa using (h ⊤ 0).1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}

section Pts

variable {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  (𝔐 : HodgeCpt Y S y)

theorem coords_of_sat {z : Sp ℂ ⟶ 𝔐.X} {w w' : (Σ k, J k) → ℂ} (h : CoordsAt 𝔐.ξ y z w') (hs : w ∈ torusSat {w'}) :
    CoordsAt 𝔐.ξ y z w := by
  obtain ⟨_, rfl, a, ha, rfl⟩ := hs
  exact (((tie_points _ _ 𝔐.ξ K J y 𝔐.tie ℂ).2.2 z _ (𝔐.all _) h).2 _).2 ⟨fun k => Units.mk0 (a k) (ha k), rfl⟩

theorem sat_of_coords {z : Sp ℂ ⟶ 𝔐.X} {w w' : (Σ k, J k) → ℂ} (h : CoordsAt 𝔐.ξ y z w') (h' : CoordsAt 𝔐.ξ y z w) :
    w ∈ torusSat {w'} := by
  obtain ⟨a, rfl⟩ := (((tie_points _ _ 𝔐.ξ K J y 𝔐.tie ℂ).2.2 z _ (𝔐.all _) h).2 _).1 h'
  exact ⟨_, rfl, fun k => a k, fun k => (a k).ne_zero, rfl⟩

theorem pt_unique {z z' : Sp ℂ ⟶ 𝔐.X} {w : (Σ k, J k) → ℂ} (h : CoordsAt 𝔐.ξ y z w) (h' : CoordsAt 𝔐.ξ y z' w) : z = z' :=
  GlobalTheory.T.normal_scheme_coords_injective _ _ 𝔐.ξ K J y 𝔐.tie (fun x => ⟨𝔐.normal.1 x, 𝔐.normal.2 x⟩) 𝔐.all z z' w h h'

theorem mem_mcPts {z : Sp ℂ ⟶ 𝔐.X} {w : (Σ k, J k) → ℂ} (h : CoordsAt 𝔐.ξ y z w) : w ∈ mcPts (mCoordIdeal y) :=
  ⟨fun k => (h.1 k).imp fun _ h => h.ne_zero, fun g hg => by
    rw [MvPolynomial.eval_map]
    exact ((tie_points _ _ 𝔐.ξ K J y 𝔐.tie ℂ).2.2 z _ (𝔐.all _) h).1 g hg⟩

theorem exists_pt {w : (Σ k, J k) → ℂ} (h : w ∈ mcPts (mCoordIdeal y)) : ∃ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z w :=
  ((tie_points _ _ 𝔐.ξ K J y 𝔐.tie ℂ).1 w (fun k => (h.1 k).imp fun _ h => Ne.isUnit h) fun g hg => by
    have := h.2 g hg
    rwa [MvPolynomial.eval_map] at this).exists.imp fun _ h => h.2

theorem interior_iff (z : Sp ℂ ⟶ 𝔐.X) : centre (z ≫ 𝔐.f) ∈ abLocus Y.t.G ↔ 𝔐.Interior z :=
  abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 _

theorem labVal_of_over {z : Sp ℂ ⟶ 𝔐.X} (hz : 𝔐.Interior z) {κ : c.F →+* ℂ}
    (h : z ≫ 𝔐.f ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) (sm : CMType H → CMType H ⊕ CMType H) :
    𝔐.LabVal z sm fun τ => κ.comp (labelEmb c (sm τ)) := by
  obtain ⟨κ', p, hp⟩ := FamEx.exists_isOver E H D l Xo c Y S Ω K J y 𝔐 z hz
  obtain rfl : κ' = κ := by
    obtain ⟨x, h1, -, h3⟩ := hp
    have := c.fin
    have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
    rw [← Category.assoc, ← h1, Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
      ← Category.assoc, h3, ← Chg.spMap_comp'] at h
    exact IsFractionRing.ringHom_ext (A := 𝓞 c.F) fun a =>
      RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective h)) a
  exact fun τ a => GlobalTheory.T.constants_value_over_point E H D l Xo c Y S Ω K J y 𝔐 z _ p hp _

end Pts

variable {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} (Or : CptOrigin Y S₀ Dc Hd)
  (B : BaseUnif Y Or.sm Dc.j Dc.j' Dc.n)

structure Sheets (FF : Fin B.np → Set (Fin Dc.n → ℂ)) (d : Fin B.np → ℕ) where
  d_pos : ∃ k, 0 < d k
  pc : ℕ → Fin B.np
  V : ℕ → Set (Fin Dc.n → ℂ)
  Bm : ℕ → Set (Fin Dc.n → ℂ)
  γ : ℕ → (Fin Dc.n → ℂ) → (Σ k, J k) → ℂ
  z : ℕ → (Fin Dc.n → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)
  cover : IsSheetCover Dc.chart V Bm γ
  V_sub : ∀ m, V m ⊆ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F (pc m)).q
  B_sub : ∀ m, Bm m ⊆ FF (pc m)
  count : ∀ k, ∀ᵐ t, t ∈ FF k → {m | pc m = k ∧ t ∈ Bm m}.encard = d k
  z_coords : ∀ m, ∀ t ∈ V m, CoordsAt Or.𝔐.ξ Dc.y (z m t) (γ m t)
  z_over : ∀ m, ∀ t ∈ V m, z m t ≫ Or.𝔐.f = B.pt (pc m) t


open Classical in
def nSheets (U : Y.X.Opens) (k : Fin B.np) : ℕ := if ∃ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U then Or.deg else 0

set_option maxHeartbeats 1600000 in
theorem exists_sheets (h1 : HolNull) (h2 : ChartMeets) (h3 : RootBranches) (h4 : CoverRoots) (h5 : LocInj)
    (FF : Fin B.np → Set (Fin Dc.n → ℂ)) (hF : ∀ k, (B.F k).IsFundSet (B.Γ k) (FF k)) :
    ∃ U : Y.X.Opens, genPt Or.𝔐.ξ₀ ∈ U ∧ (∀ p : Sp ℂ ⟶ Y.X, ⊤ ≤ p ⁻¹ᵁ U → genPt Or.𝔐.ξ₀ ⤳ centre p) ∧
      Nonempty (Sheets Or B FF (nSheets Or B U)) := by
  classical
  have : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨U, a, cf, hU, hc⟩ := h4 E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 Or.deg Or.cover
  have hgen : Or.𝔐.f (genPt Or.𝔐.ξ) = genPt Or.𝔐.ξ₀ := by
    show (Or.𝔐.ξ ≫ Or.𝔐.f) (IsLocalRing.closedPoint Ω) = _
    rw [show Or.𝔐.ξ ≫ Or.𝔐.f = _ from Or.𝔐.fn_over]
    exact congrArg (fun x => Or.𝔐.ξ₀ x) (Subsingleton.elim (α := PrimeSpectrum Or.𝔐.Ω₀) _ _)
  refine ⟨U, hU, fun p hp => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (monicOf fun i => valAt' p U (a i)) fun h =>
      Or.cover.1.ne' ((natDegree_monicOf _).symm.trans (natDegree_eq_of_degree_eq_some h))
    obtain ⟨z, rfl, -⟩ := (hc p hp).2.1 x hx
    exact hgen ▸ (Or.𝔐.all (centre z)).map Or.𝔐.f.continuous
  let T : Fin B.np → Set (Fin Dc.n → ℂ) := fun k => {t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q | ⊤ ≤ B.pt k t ⁻¹ᵁ U}
  let A : Fin B.np → (Fin Dc.n → ℂ) → Fin Or.deg → ℂ := fun k t i => valAt' (B.pt k t) U (a i)
  let w : Fin B.np → (Fin Dc.n → ℂ) → ℂ → (Σ k, J k) → ℂ := fun k t θ s => ∑ i, valAt' (B.pt k t) U (cf s i) * θ ^ (i : ℕ)
  have hW : ∀ k, ∃ Wk : ℕ → Set (Fin Dc.n → ℂ), (∀ m, IsOpen (Wk m) ∧ Wk m ⊆ T k ∧
      (∀ t ∈ Wk m, ∀ t' ∈ Wk m, (B.F k).Eqv (B.Γ k) t t' → t = t') ∧ ∃ θ : Fin Or.deg → (Fin Dc.n → ℂ) → ℂ,
        (∀ i, DifferentiableOn ℂ (θ i) (Wk m)) ∧ ∀ t ∈ Wk m, (Function.Injective fun i => θ i t) ∧
          ∀ x, (monicOf (A k t)).IsRoot x ↔ ∃ i, x = θ i t) ∧ T k ⊆ ⋃ m, Wk m := fun k => by
    refine cover_seq (T k) (fun V => V ⊆ T k ∧ (∀ t ∈ V, ∀ t' ∈ V, (B.F k).Eqv (B.Γ k) t t' → t = t') ∧
      ∃ θ : Fin Or.deg → (Fin Dc.n → ℂ) → ℂ, (∀ i, DifferentiableOn ℂ (θ i) V) ∧ ∀ t ∈ V, (Function.Injective fun i => θ i t) ∧
        ∀ x, (monicOf (A k t)).IsRoot x ↔ ∃ i, x = θ i t) ?_ fun t ht => ?_
    · exact ⟨Set.empty_subset _, fun _ h => h.elim, 0, fun _ => differentiableOn_empty, fun _ h => h.elim⟩
    obtain ⟨V, θ, o1, m1, s1, d1, r1⟩ := h3 _ _ (T k) (A k) (B.hol k U 0).1 (differentiableOn_pi.2 fun i => (B.hol k U (a i)).2)
      (fun t ht => (hc _ ht.2).1) t ht
    obtain ⟨V', o2, m2, -, i2⟩ := h5 E H l (B.Di k) _ _ _ _ _ (B.F k) (B.Γ k) (B.form_eq k) (fun γ hγ => (B.mem_Γ k γ).1 hγ) t ht.1
    exact ⟨V ∩ V', o1.inter o2, ⟨m1, m2⟩, Set.inter_subset_left.trans s1, fun t h t' h' => i2 t h.2 t' h'.2, θ,
      fun i => (d1 i).mono Set.inter_subset_left, fun t h => r1 t h.1⟩
  choose Wk hWk hWc using hW
  choose hWo hWs hWi θ hθd hθ using hWk
  have hz : ∀ k m i t, ∃ z : Sp ℂ ⟶ Or.𝔐.X, t ∈ Wk k m → z ≫ Or.𝔐.f = B.pt k t ∧ CoordsAt Or.𝔐.ξ Dc.y z (w k t (θ k m i t)) :=
    fun k m i t => by
      by_cases ht : t ∈ Wk k m
      · exact ((hc _ (hWs k m ht).2).2.1 _ (((hθ k m t ht).2 _).2 ⟨i, rfl⟩)).imp fun _ h _ => h
      · obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.multiprojective_points_nonempty K J Ω Dc.y fun k => by
          obtain ⟨c', hc'⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
          exact ⟨c' k, Finset.prod_ne_zero_iff.1 hc'.1 k (Finset.mem_univ k)⟩
        exact (exists_pt Or.𝔐 hw₀).imp fun _ _ h => absurd h ht
  choose z hz using hz
  have hin : ∀ k m i t, t ∈ Wk k m → Or.𝔐.Interior (z k m i t) := fun k m i t ht =>
    (interior_iff Or.𝔐 _).1 ((hz k m i t ht).1 ▸ B.interior k t (hWs k m ht).1)

  have hsame : ∀ k m i t k' m' i' t', t ∈ Wk k m → t' ∈ Wk k' m' → w k t (θ k m i t) ∈ torusSat {w k' t' (θ k' m' i' t')} →
      z k m i t = z k' m' i' t' ∧ B.pt k t = B.pt k' t' := fun k m i t k' m' i' t' ht ht' h => by
    have e := pt_unique Or.𝔐 (hz k m i t ht).2 (coords_of_sat Or.𝔐 (hz k' m' i' t' ht').2 h)
    exact ⟨e, by rw [← (hz k m i t ht).1, e, (hz k' m' i' t' ht').1]⟩

  have hcov : ∀ b : Fin Dc.nCharts, ∀ᵐ t, t ∈ Metric.ball (0 : Fin Dc.n → ℂ) 1 →
      ∃ k m i, ∃ t' ∈ FF k ∩ disjointed (Wk k) m, (Dc.chart b).γ t ∈ torusSat {w k t' (θ k m i t')} := fun b => by
    have hζ : ∀ t, ∃ ζ : Sp ℂ ⟶ Or.𝔐.X, t ∈ Metric.ball (0 : Fin Dc.n → ℂ) 1 → CoordsAt Or.𝔐.ξ Dc.y ζ ((Dc.chart b).γ t) := fun t => by
      by_cases ht : t ∈ Metric.ball (0 : Fin Dc.n → ℂ) 1
      · exact (exists_pt Or.𝔐 ((Dc.chart b).mem t ht)).imp fun _ h _ => h
      · exact (exists_pt Or.𝔐 ((Dc.chart b).mem 0 (Metric.mem_ball_self one_pos))).imp fun _ _ h => absurd h ht
    choose ζ hζ using hζ
    have hg : genPt Or.𝔐.ξ ∈ Or.𝔐.f ⁻¹ᵁ U := by
      show (Or.𝔐.ξ ≫ Or.𝔐.f) (IsLocalRing.closedPoint Ω) ∈ U
      rw [show Or.𝔐.ξ ≫ Or.𝔐.f = _ from Or.𝔐.fn_over]
      exact (congrArg (fun x => Or.𝔐.ξ₀ x ∈ U) (Subsingleton.elim (α := PrimeSpectrum Or.𝔐.Ω₀) _ _)).mpr hU
    obtain ⟨t₁, ht₁, z₁, c₁, u₁⟩ := h2 _ Ω Or.𝔐.ξ K J Dc.y _ _ (Dc.chart b) _ Or.𝔐.tie Or.𝔐.all Dc.arith hg
    have n1 := h1 _ _ _ ζ (Or.𝔐.f ⁻¹ᵁ U) Metric.isOpen_ball (convex_ball _ _).isPreconnected
      (GlobalTheory.T.holomorphic_coords_of_generic_point _ Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie Or.𝔐.all _ _ _ ζ Metric.isOpen_ball (Dc.chart b).analytic.differentiableOn hζ)
      ⟨t₁, ht₁, pt_unique Or.𝔐 c₁ (hζ t₁ ht₁) ▸ u₁⟩
    have n2 : ∀ᵐ t : Fin Dc.n → ℂ, ∀ i, t i ≠ 0 := ae_all_iff.2 fun i => by
      rw [volume_pi]
      exact Measure.ae_eval_ne _ i 0
    filter_upwards [n2, compl_mem_ae_iff.2 n1] with t e1 e2 ht
    have hi : Or.𝔐.Interior (ζ t) := by_contra fun h => by
      obtain ⟨i, -, hi⟩ := ((Dc.chart b).boundary t ht).1 ((Or.bd _ _ (hζ t ht)).2 h)
      exact e1 i hi
    obtain ⟨k, t₂, ht₂, e3⟩ := B.onto _ ((interior_iff Or.𝔐 _).2 hi)
    obtain ⟨t₃, ht₃, e4⟩ := (hF k).2.2.1 t₂ ht₂
    have e5 : ζ t ≫ Or.𝔐.f = B.pt k t₃ := e3.symm.trans ((B.fibre k _ ht₂ _ ((hF k).2.1 ht₃)).2 e4)
    have e6 : t₃ ∈ T k := ⟨(hF k).2.1 ht₃, e5 ▸ by_contra fun h => e2 ⟨ht, h⟩⟩
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (iUnion_disjointed (f := Wk k) ▸ hWc k e6)
    obtain ⟨x, hx, cx⟩ := (hc _ e6.2).2.2.1 _ e5
    obtain ⟨i, rfl⟩ := ((hθ k m t₃ (disjointed_subset _ _ hm)).2 x).1 hx
    exact ⟨k, m, i, t₃, ⟨ht₃, hm⟩, sat_of_coords Or.𝔐 cx (hζ t ht)⟩
  obtain ⟨k₀, m₀, i₀, t₀, ht₀⟩ : ∃ k m, ∃ _ : Fin Or.deg, ∃ t, t ∈ FF k ∩ disjointed (Wk k) m := by
    obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.multiprojective_points_nonempty K J Ω Dc.y fun k => by
      obtain ⟨c', hc'⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
      exact ⟨c' k, Finset.prod_ne_zero_iff.1 hc'.1 k (Finset.mem_univ k)⟩
    obtain ⟨b, -⟩ := Dc.chart_cover w₀ hw₀
    obtain ⟨t, ht, h⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (Metric.measure_ball_pos volume (0 : Fin Dc.n → ℂ) one_pos).ne' (ae_restrict_of_ae (hcov b))
    obtain ⟨k, m, i, t', ht', -⟩ := h ht
    exact ⟨k, m, i, t', ht'⟩
  have : Nonempty (Fin B.np) := ⟨k₀⟩
  have : Nonempty (Fin Or.deg) := ⟨i₀⟩
  obtain ⟨e⟩ : Nonempty (ℕ ≃ Fin B.np × ℕ × Fin Or.deg) := nonempty_equiv_of_countable
  have hT : ∀ {k t}, t ∈ T k → nSheets Or B U k = Or.deg := fun ht => if_pos ⟨_, ht.1, ht.2⟩
  refine ⟨⟨⟨k₀, (hT (hWs k₀ m₀ (disjointed_subset _ _ ht₀.2))).symm ▸ Or.cover.1⟩, fun m => (e m).1, fun m => Wk (e m).1 (e m).2.1,
    fun m => FF (e m).1 ∩ disjointed (Wk (e m).1) (e m).2.1, fun m t => w (e m).1 t (θ (e m).1 (e m).2.1 (e m).2.2 t),
    fun m => z (e m).1 (e m).2.1 (e m).2.2, ⟨fun m => hWo _ _, fun m => ?_, fun m t ht => ?_, fun m t ht t' ht' h => ?_,
      fun m => ⟨(hF _).1.inter (MeasurableSet.disjointed (fun m => (hWo _ m).measurableSet) _),
        Set.inter_subset_right.trans (disjointed_subset _ _)⟩, fun m m' hne t ht h => hne (e.injective ?_), fun b => ?_⟩,
    fun m t ht => (hWs _ _ ht).1, fun m => Set.inter_subset_left, fun k => ?_, fun m t ht => (hz _ _ _ t ht).2,
    fun m t ht => (hz _ _ _ t ht).1⟩⟩
  · exact differentiableOn_pi.2 fun s => DifferentiableOn.fun_sum fun i _ =>
      ((B.hol _ U (cf s i)).2.mono (hWs _ _)).mul ((hθd _ _ _).pow _)
  · exact ⟨mem_mcPts Or.𝔐 (hz _ _ _ t ht).2, fun h => (Or.bd _ _ (hz _ _ _ t ht).2).1 h (hin _ _ _ t ht)⟩
  · exact hWi _ _ t ht t' ht' ((B.fibre _ t (hWs _ _ ht).1 t' (hWs _ _ ht').1).1 (hsame _ _ _ _ _ _ _ _ ht ht' h).2)
  · obtain ⟨_, ⟨t', ht', rfl⟩, h⟩ := h
    generalize e m = x at ht h ⊢
    generalize e m' = x' at ht' h ⊢
    obtain ⟨k, n, i⟩ := x
    obtain ⟨k', n', i'⟩ := x'
    have u := disjointed_subset _ _ ht.2
    have u' := disjointed_subset _ _ ht'.2
    obtain ⟨e1, e2⟩ := hsame _ _ i _ _ _ i' _ u u' ⟨_, rfl, h⟩
    obtain rfl : k = k' := B.disj _ _ t (hWs _ _ u).1 t' (hWs _ _ u').1 e2
    obtain rfl : t = t' := (hF k).2.2.2 t ht.1 t' ht'.1 ((B.fibre k t (hWs _ _ u).1 t' (hWs _ _ u').1).1 e2)
    obtain rfl : n = n' := by_contra fun hn => Set.disjoint_left.1 (disjoint_disjointed (Wk k) hn) ht.2 ht'.2
    obtain rfl : i = i' := (hθ k n t u).1 ((hc _ (hWs _ _ u).2).2.2.2 _ _ _ (((hθ k n t u).2 _).2 ⟨i, rfl⟩)
      (((hθ k n t u).2 _).2 ⟨i', rfl⟩) (hz k n i t u).2 (e1 ▸ (hz k n i' t u).2))
    rfl
  · refine measure_mono_null ?_ (ae_iff.1 (hcov b))
    intro t ht h
    obtain ⟨k, m, i, t', ht', _, rfl, h'⟩ := h ht.1
    exact ht.2 ⟨_, Set.mem_iUnion.2 ⟨e.symm (k, m, i), t', by rwa [e.apply_symm_apply], by simp only [e.apply_symm_apply]⟩, h'⟩
  · by_cases hk : ∃ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U
    · filter_upwards [compl_mem_ae_iff.2 (h1 _ _ _ _ U (isOpen_of_holTo (B.hol k)) (ballDom_preconnected (B.F k).q) (B.hol k) hk)]
        with t e1 ht
      have e2 : t ∈ T k := ⟨(hF k).2.1 ht, by_contra fun h => e1 ⟨(hF k).2.1 ht, h⟩⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (iUnion_disjointed (f := Wk k) ▸ hWc k e2)
      have : {m | (e m).1 = k ∧ t ∈ FF (e m).1 ∩ disjointed (Wk (e m).1) (e m).2.1} =
          (fun i : Fin Or.deg => e.symm (k, n, i)) '' Set.univ := by
        ext m
        obtain ⟨⟨k', n', i⟩, rfl⟩ := e.symm.surjective m
        simp only [Set.mem_setOf_eq, e.apply_symm_apply, Set.image_univ, Set.mem_range, e.symm.injective.eq_iff]
        constructor
        · rintro ⟨rfl, h⟩
          obtain rfl : n = n' := by_contra fun h' => Set.disjoint_left.1 (disjoint_disjointed (Wk k') h') hn h.2
          exact ⟨i, rfl⟩
        · rintro ⟨_, ⟨⟩⟩
          exact ⟨rfl, ht, hn⟩
      rw [this, Function.Injective.encard_image (fun i i' h => by simpa using h), hT e2]
      simp
    · refine ae_of_all _ fun t _ => ?_
      rw [nSheets, if_neg hk, Nat.cast_zero, Set.encard_eq_zero]
      refine Set.eq_empty_of_forall_notMem ?_
      rintro m ⟨rfl, h⟩
      exact hk ⟨t, hWs _ _ (disjointed_subset _ _ h.2)⟩

end SheetDecomposition
