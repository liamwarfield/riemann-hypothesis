module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.DetGramNonneg
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

variable (I : AutInst)

def cmat (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    Matrix (Fin I.n) (Fin j) ℂ :=
  Matrix.of fun i a => coordV I x v (b a) i

theorem gramV_eq (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    gramV I x v b = (cmat I x v b)ᴴ * cmat I x v b := by
  ext a c
  simp [gramV, cmat, Matrix.mul_apply, Matrix.conjTranspose_apply]

def subOfEq {x x' : I.GA} (h : latSet I x' = latSet I x) (s : Sub I x) : Sub I x' where
  j := s.j
  j_pos := s.j_pos
  b := s.b
  b_ind := s.b_ind
  B := s.B
  B_lat := by rw [h]; exact s.B_lat
  b_mem := s.b_mem
  B_span := s.B_span

theorem det_gram_nonneg (h5 : GramDistortionBound) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (hj : 1 ≤ j)
    (b : Fin j → Fin I.n → I.E) : 0 ≤ (gramV I x v b).det.re := by
  rw [gramV_eq]
  open scoped ComplexOrder in
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg).1

theorem ht_nonneg (h5 : GramDistortionBound) {x : I.GA} (s : Sub I x) : 0 ≤ ht I s := by
  unfold ht
  exact div_nonneg (Finset.prod_nonneg fun v _ => det_gram_nonneg I h5 x v s.j_pos s.b) (Nat.cast_nonneg _)

theorem size_nonneg (h5 : GramDistortionBound) {x : I.GA} (s : Sub I x) : 0 ≤ size I s := by
  unfold Size.size
  exact Real.rpow_nonneg (ht_nonneg I h5 s) _

theorem size_subOfEq_le (h5 : GramDistortionBound) {x x' : I.GA} (hlat : latSet I x' = latSet I x)
    (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ)
    (hY : ∀ v u, coordV I x' v u = Y v *ᵥ coordV I x v u) {c : ℝ} (hc : 1 ≤ c)
    (hb : ∀ v (w : Fin I.n → ℂ), ∑ i, ‖(Y v *ᵥ w) i‖ ^ 2 ≤ c * ∑ i, ‖w i‖ ^ 2) (s : Sub I x) :
    size I (subOfEq I hlat s) ≤ c ^ Fintype.card (InfinitePlace I.F) * size I s := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hcm : ∀ v, cmat I x' v s.b = Y v * cmat I x v s.b := by
    intro v
    ext i a
    simp [cmat, hY, Matrix.mulVec, Matrix.mul_apply, dotProduct]
  have hdet : ∀ v, (gramV I x' v s.b).det.re ≤ c ^ s.j * (gramV I x v s.b).det.re := by
    intro v
    rw [gramV_eq, gramV_eq, hcm]
    refine (h5 I.n s.j (Y v) (cmat I x v s.b) 0 c le_rfl (fun w => ⟨?_, hb v w⟩)).2
    rw [zero_mul]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hht : ht I (subOfEq I hlat s) ≤ (c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ht I s := by
    unfold ht
    rw [mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    calc ∏ v, (gramV I x' v (subOfEq I hlat s).b).det.re
        ≤ ∏ v : InfinitePlace I.F, c ^ s.j * (gramV I x v s.b).det.re :=
          Finset.prod_le_prod₀ (fun v _ => det_gram_nonneg I h5 x' v s.j_pos s.b) (fun v _ => hdet v)
      _ = (c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ∏ v, (gramV I x v s.b).det.re := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have he : 0 ≤ 1 / (2 * (I.f : ℝ) * (s.j : ℝ)) := by positivity
  have hexp : ((s.j * Fintype.card (InfinitePlace I.F) : ℕ) : ℝ) * (1 / (2 * (I.f : ℝ) * (s.j : ℝ)))
      ≤ (Fintype.card (InfinitePlace I.F) : ℝ) := by
    have hj : (1 : ℝ) ≤ s.j := by exact_mod_cast s.j_pos
    rcases Nat.eq_zero_or_pos I.f with hf | hf
    · simp [hf]
    · have hf' : (1 : ℝ) ≤ I.f := by exact_mod_cast hf
      rw [Nat.cast_mul, mul_one_div, div_le_iff₀ (by positivity)]
      have hP : (0 : ℝ) ≤ Fintype.card (InfinitePlace I.F) := Nat.cast_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hP (by linarith : (0 : ℝ) ≤ s.j)) (by linarith : (0 : ℝ) ≤ 2 * (I.f : ℝ) - 1)]
  unfold Size.size
  show ht I (subOfEq I hlat s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) ≤ _
  calc ht I (subOfEq I hlat s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ)))
      ≤ ((c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ht I s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) :=
        Real.rpow_le_rpow (ht_nonneg I h5 _) hht he
    _ = ((c ^ s.j) ^ Fintype.card (InfinitePlace I.F)) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) *
          ht I s ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) :=
        Real.mul_rpow (by positivity) (ht_nonneg I h5 s)
    _ ≤ c ^ Fintype.card (InfinitePlace I.F) * ht I s ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (ht_nonneg I h5 s) _)
        rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hc0, ← Real.rpow_natCast c]
        exact Real.rpow_le_rpow_of_exponent_le hc hexp

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.SumNormMulVecSqLe
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem norm_add_sq_le_young (p q : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖p + q‖ ^ 2 ≤ (1 + t) * ‖p‖ ^ 2 + (1 + 1 / t) * ‖q‖ ^ 2 := by
  have ha := norm_nonneg p
  have hb := norm_nonneg q
  have h1 : ‖p + q‖ ≤ ‖p‖ + ‖q‖ := norm_add_le p q
  have h2 : ‖p + q‖ ^ 2 ≤ (‖p‖ + ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * ‖p‖ * ‖q‖ ≤ t * ‖p‖ ^ 2 + 1 / t * ‖q‖ ^ 2 := by
    have h4 : 0 ≤ (t * ‖p‖ - ‖q‖) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    have e : (t * ‖p‖ - ‖q‖) ^ 2 / t = t * ‖p‖ ^ 2 - 2 * ‖p‖ * ‖q‖ + 1 / t * ‖q‖ ^ 2 := by
      field_simp
      ring
    linarith
  nlinarith

theorem norm_sum_mul_sq_le {m : ℕ} (d w : Fin m → ℂ) :
    ‖∑ l, d l * w l‖ ^ 2 ≤ (∑ l, ‖d l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2 := by
  have h1 : ‖∑ l, d l * w l‖ ≤ ∑ l, ‖d l‖ * ‖w l‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖d l‖) (fun l => ‖w l‖)
  calc ‖∑ l, d l * w l‖ ^ 2 ≤ (∑ l, ‖d l‖ * ‖w l‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem sum_norm_mulVec_sq_le {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ) (w : Fin m → ℂ) {t : ℝ} (ht : 0 < t) :
    ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤
      ((1 + t) + (1 + 1 / t) * ∑ i, ∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ i, ‖w i‖ ^ 2 := by
  have hY : ∀ i, (Y *ᵥ w) i = w i + ((Y - 1) *ᵥ w) i := by
    intro i
    simp [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hc : 0 ≤ 1 + 1 / t := by
    have := one_div_pos.mpr ht
    linarith
  have hi : ∀ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤
      (1 + t) * ‖w i‖ ^ 2 + (1 + 1 / t) * ((∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2) := by
    intro i
    rw [hY]
    refine (norm_add_sq_le_young _ _ ht).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_sum_mul_sq_le _ _) hc)
  calc ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤ ∑ i, ((1 + t) * ‖w i‖ ^ 2 +
        (1 + 1 / t) * ((∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2)) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        ring

end Formalism.L2.SG.Pf.Tau
end
end

set_option autoImplicit false

noncomputable section

open NumberField Matrix Filter Topology

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem uMat_mul {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := by
  simp [uMat]

theorem uMat_one {n : ℕ} {ε : Fin n → Bool} : uMat (1 : Formalism.REAL.UJ ε) = 1 := by
  simp [uMat]

theorem coordV_mul (I : AutInst) (x : I.GA) (y : I.Ginf) (k : I.Gf) (v : InfinitePlace I.F)
    (u : Fin I.n → I.E) : coordV I (x * (y, k)) v u = uMat (y v)⁻¹ *ᵥ coordV I x v u := by
  have hA : ((x * (y, k)).1 v)⁻¹ = (y v)⁻¹ * (x.1 v)⁻¹ := by
    rw [← _root_.mul_inv_rev]
    rfl
  unfold coordV
  rw [hA, uMat_mul, Matrix.mulVec_mulVec, mul_assoc]

theorem coordV_mul' (I : AutInst) (x : I.GA) (y : I.Ginf) (k : I.Gf) (v : InfinitePlace I.F)
    (u : Fin I.n → I.E) : coordV I x v u = uMat (y v) *ᵥ coordV I (x * (y, k)) v u := by
  rw [coordV_mul, Matrix.mulVec_mulVec, ← uMat_mul, mul_inv_cancel, uMat_one, Matrix.one_mulVec]

theorem eventually_uMat_near (I : AutInst) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 (1 : I.Ginf), ∀ v, ∑ i, ∑ l, ‖(uMat (y v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat (y v) - 1) i l‖ ^ 2 < δ := by
  rw [Filter.eventually_all]
  intro v
  have c1 : Continuous fun y : I.Ginf => ∑ i, ∑ l, ‖(uMat (y v)⁻¹ - 1) i l‖ ^ 2 := by
    unfold uMat
    fun_prop
  have c2 : Continuous fun y : I.Ginf => ∑ i, ∑ l, ‖(uMat (y v) - 1) i l‖ ^ 2 := by
    unfold uMat
    fun_prop
  refine Filter.Eventually.and ?_ ?_
  · exact c1.continuousAt.eventually_lt continuousAt_const (by simpa [uMat_one] using hδ)
  · exact c2.continuousAt.eventually_lt continuousAt_const (by simpa [uMat_one] using hδ)

theorem eventually_kg_one (I : AutInst) : ∀ᶠ k in 𝓝 (1 : I.Gf), k ∈ I.Kg 1 := by
  have ho := I.topf_open 1 le_rfl
  refine ho.mem_nhds ?_
  exact ⟨Subgroup.one_mem _, fun y _ => ⟨0, Submodule.zero_mem _, by simp⟩⟩

theorem sizes_locally_comparable (h4 : LatticeRightInvariant) (h5 : GramDistortionBound) : SizesLocallyComparable := by
  intro I x r hr
  set N := Fintype.card (InfinitePlace I.F)
  set c : ℝ := r ^ (((N + 1 : ℕ) : ℝ)⁻¹) with hcdef
  have hc1 : 1 < c := Real.one_lt_rpow hr (by positivity)
  have hcN : c ^ N ≤ r := by
    calc c ^ N ≤ c ^ (N + 1) := pow_le_pow_right₀ hc1.le (Nat.le_succ N)
      _ = r := Real.rpow_inv_natCast_pow (by linarith) (Nat.succ_ne_zero N)
  set ε : ℝ := (c - 1) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set δ : ℝ := ε ^ 2 / (1 + ε) with hδdef
  have hδ : 0 < δ := by positivity
  have hbound : ∀ M : Matrix (Fin I.n) (Fin I.n) ℂ, ∑ i, ∑ l, ‖(M - 1) i l‖ ^ 2 < δ →
      ∀ w : Fin I.n → ℂ, ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ c * ∑ i, ‖w i‖ ^ 2 := by
    intro M hM w
    refine (sum_norm_mulVec_sq_le M w hε).trans ?_
    have hw : 0 ≤ ∑ i, ‖w i‖ ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hw
    have h1 : (1 + 1 / ε) * ∑ i, ∑ l, ‖(M - 1) i l‖ ^ 2 ≤ (1 + 1 / ε) * δ :=
      mul_le_mul_of_nonneg_left hM.le (by positivity)
    have h2 : (1 + 1 / ε) * δ = ε := by
      rw [hδdef]
      field_simp
      ring
    linarith
  have hW : ∀ᶠ z in 𝓝 (1 : I.GA), (∀ v, ∑ i, ∑ l, ‖(uMat (z.1 v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat (z.1 v) - 1) i l‖ ^ 2 < δ) ∧ z.2 ∈ I.Kg 1 := by
    have h := (eventually_uMat_near I hδ).prod_mk (eventually_kg_one I)
    rw [show (1 : I.GA) = (1, 1) from rfl, nhds_prod_eq]
    exact h
  have hx : ∀ᶠ x' in 𝓝 x, (∀ v, ∑ i, ∑ l, ‖(uMat ((x⁻¹ * x').1 v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat ((x⁻¹ * x').1 v) - 1) i l‖ ^ 2 < δ) ∧ (x⁻¹ * x').2 ∈ I.Kg 1 := by
    have ht : Tendsto (fun x' : I.GA => x⁻¹ * x') (𝓝 x) (𝓝 1) := by
      have h := (continuous_const_mul x⁻¹).tendsto x
      rwa [inv_mul_cancel] at h
    exact ht.eventually hW
  filter_upwards [hx] with x' hx'
  obtain ⟨hy, hk⟩ := hx'
  set y := (x⁻¹ * x').1
  set k := (x⁻¹ * x').2
  have hxe : x * (y, k) = x' := by
    change x * ((x⁻¹ * x').1, (x⁻¹ * x').2) = x'
    rw [Prod.mk.eta, mul_inv_cancel_left]
  have hlat : latSet I x' = latSet I x := by
    have h := h4 I x y k hk.1
    rwa [hxe] at h
  have hc1' : ∀ v u, coordV I x' v u = uMat (y v)⁻¹ *ᵥ coordV I x v u := by
    intro v u
    have h := coordV_mul I x y k v u
    rwa [hxe] at h
  have hc2' : ∀ v u, coordV I x v u = uMat (y v) *ᵥ coordV I x' v u := by
    intro v u
    have h := coordV_mul' I x y k v u
    rwa [hxe] at h
  refine ⟨fun s => ⟨subOfEq I hlat s, ?_⟩, fun s' => ⟨subOfEq I hlat.symm s', ?_⟩⟩
  · exact (size_subOfEq_le I h5 hlat _ hc1' hc1.le (fun v w => hbound _ (hy v).1 w) s).trans
      (mul_le_mul_of_nonneg_right hcN (size_nonneg I h5 s))
  · exact (size_subOfEq_le I h5 hlat.symm _ hc2' hc1.le (fun v w => hbound _ (hy v).2 w) s').trans
      (mul_le_mul_of_nonneg_right hcN (size_nonneg I h5 s'))

end Formalism.L2.SG.Pf.Tau
