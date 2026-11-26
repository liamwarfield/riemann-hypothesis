module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLaws
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivVanishesOfTranslationInvariance

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (omegaStd)

namespace GlobalTheory.SW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem vecQ_add (m m' : Fin g ⊕ Fin g → ℚ) :
    vecQ X bas (m + m') = vecQ X bas m + vecQ X bas m' := by
  simp only [vecQ, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem vecQ_smul (q : ℚ) (m : Fin g ⊕ Fin g → ℚ) : vecQ X bas (q • m) = q • vecQ X bas m := by
  simp only [vecQ, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem vecQ_zero : vecQ X bas 0 = 0 := by simp [vecQ]

theorem vecQ_intCast (m : Fin g ⊕ Fin g → ℤ) :
    vecQ X bas (fun j => (m j : ℚ)) = (bas m : Fin r → E) := by
  have hm : m = ∑ j, m j • Pi.single j (1 : ℤ) := by
    funext j; simp [Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [hm, map_sum, AddSubmonoidClass.coe_finsetSum]
  simp only [vecQ, map_zsmul, AddSubgroupClass.coe_zsmul, Int.cast_smul_eq_zsmul]

theorem vecQ_surjective : Function.Surjective (vecQ X bas) := by
  intro v
  obtain ⟨k, hk, hv⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
  refine ⟨(k : ℚ)⁻¹ • fun j => (bas.symm ⟨_, hv⟩ j : ℚ), ?_⟩
  rw [vecQ_smul, vecQ_intCast, LinearEquiv.apply_symm_apply]
  change (k : ℚ)⁻¹ • k • v = v
  rw [← Int.cast_smul_eq_zsmul ℚ, inv_smul_smul₀ (Int.cast_ne_zero.2 hk)]

theorem vecQ_crd (v : Fin r → E) : vecQ X bas (crd X bas v) = v :=
  Function.rightInverse_invFun (vecQ_surjective X bas) v

noncomputable def EFBil : (Fin r → E) →ₗ[ℚ] (Fin r → E) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (EF X)
    (fun u u' v => by
      simp only [EF_def, ← map_add (f := _), herm, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add])
    (fun q u v => by
      simp only [EF_def, ← map_smul, herm, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum,
        mul_smul_comm])
    (fun u v v' => by
      simp only [EF_def, herm, cc, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib, mul_add])
    (fun q u v => by
      simp only [EF_def, herm, cc, Pi.smul_apply, map_rat_smul, ← Finset.smul_sum,
        mul_smul_comm])

variable {X bas}

theorem EF_vecQ (hs : IsSympl X bas) (m m' : Fin g ⊕ Fin g → ℚ) :
    EF X (vecQ X bas m) (vecQ X bas m') =
      -∑ i, (m (Sum.inl i) * m' (Sum.inr i) - m (Sum.inr i) * m' (Sum.inl i)) := by
  change EFBil X _ _ = _
  have h (j k) : EFBil X (bas (Pi.single j 1)) (bas (Pi.single k 1)) =
      -(omegaStd (Pi.single j 1) (Pi.single k 1) : ℤ) := hs _ _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vecQ, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h]
  simp [Fintype.sum_sum_type, omegaStd, Pi.single_apply, Finset.sum_sub_distrib, mul_comm]
  ring

theorem vecQ_injective (hs : IsSympl X bas) : Function.Injective (vecQ X bas) := by
  intro m m' h
  have h' (t) := (EF_vecQ hs m t).symm.trans (h ▸ EF_vecQ hs m' t)
  funext j
  rcases j with j | j
  · simpa [Pi.single_apply] using h' (Pi.single (Sum.inr j) 1)
  · simpa [Pi.single_apply] using h' (Pi.single (Sum.inl j) 1)

theorem crd_vecQ (hs : IsSympl X bas) (m : Fin g ⊕ Fin g → ℚ) : crd X bas (vecQ X bas m) = m :=
  Function.leftInverse_invFun (vecQ_injective hs) m

theorem crd_add (hs : IsSympl X bas) (u v : Fin r → E) :
    crd X bas (u + v) = crd X bas u + crd X bas v :=
  vecQ_injective hs (by rw [vecQ_add, vecQ_crd, vecQ_crd, vecQ_crd])

theorem crd_smul (hs : IsSympl X bas) (q : ℚ) (v : Fin r → E) :
    crd X bas (q • v) = q • crd X bas v :=
  vecQ_injective hs (by rw [vecQ_smul, vecQ_crd, vecQ_crd])

theorem crd_zero (hs : IsSympl X bas) : crd X bas 0 = 0 :=
  vecQ_injective hs (by rw [vecQ_crd, vecQ_zero])

theorem EF_crd (hs : IsSympl X bas) (u v : Fin r → E) :
    EF X u v = -∑ i, (crd X bas u (Sum.inl i) * crd X bas v (Sum.inr i) -
      crd X bas u (Sum.inr i) * crd X bas v (Sum.inl i)) := by
  rw [← EF_vecQ hs, vecQ_crd, vecQ_crd]

theorem hMat_mulVec_per_crd (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (v : Fin r → E) :
    hMat X bas idx x *ᵥ (per X x v ∘ idx) = qv (fun i => crd X bas v (Sum.inl i)) +
      tauMat X bas idx x *ᵥ qv fun i => crd X bas v (Sum.inr i) := by
  have h : per X x v ∘ idx =
      perMat X bas idx Sum.inl x *ᵥ qv (fun i => crd X bas v (Sum.inl i)) +
      perMat X bas idx Sum.inr x *ᵥ qv fun i => crd X bas v (Sum.inr i) := by
    funext i
    conv_lhs => rw [← vecQ_crd X bas v, vecQ, per_sum]
    simp only [per_ratSmul, Fintype.sum_sum_type]
    simp [mulVec, dotProduct, mul_comm, qv, Rat.smul_def]
  rw [h, mulVec_add, mulVec_mulVec, mulVec_mulVec, tauMat, hMat_mul_perMat idx hs hx, one_mulVec]

theorem heis_exponent {ι : Type} [Fintype ι] [DecidableEq ι] (τ W : Matrix ι ι ℂ)
    (hτ : τ.IsSymm) (hW : W.IsSymm) (hY : W * τ.map (fun z => (z.im : ℂ)) = 1) (a b : ι → ℚ)
    (u : ι → ℂ) :
    π / 2 * (u ⬝ᵥ W *ᵥ u) + π * I * (qv b ⬝ᵥ τ *ᵥ qv b + 2 * (qv b ⬝ᵥ u) + qv a ⬝ᵥ qv b) =
      -(π * ((u + (1 / 2 : ℂ) • (qv a + τ *ᵥ qv b)) ⬝ᵥ W *ᵥ star (qv a + τ *ᵥ qv b))) +
        π / 2 * ((u + (qv a + τ *ᵥ qv b)) ⬝ᵥ W *ᵥ (u + (qv a + τ *ᵥ qv b))) := by
  have h1 : star (qv a + τ *ᵥ qv b) =
      (qv a + τ *ᵥ qv b) - (2 * I) • (τ.map (fun z => (z.im : ℂ)) *ᵥ qv b) := by
    funext i
    simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, mulVec, dotProduct, qv,
      star_add, star_sum, star_mul', RCLike.star_def, map_ratCast, map_apply, smul_eq_mul,
      Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have := Complex.sub_conj (τ i j)
    push_cast at this
    linear_combination (-(b j : ℂ)) * this
  have h2 : qv b ⬝ᵥ (qv a + τ *ᵥ qv b) = qv a ⬝ᵥ qv b + qv b ⬝ᵥ τ *ᵥ qv b := by
    rw [dotProduct_add, dotProduct_comm]
  generalize qv a + τ *ᵥ qv b = w at h1 h2 ⊢
  have h3 : w ⬝ᵥ W *ᵥ u = u ⬝ᵥ W *ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hW.eq, dotProduct_comm]
  rw [h1, mulVec_sub, mulVec_smul, mulVec_mulVec, hY, one_mulVec]
  simp only [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h3, dotProduct_comm u (qv b), dotProduct_comm w (qv b), h2]
  ring

theorem heisG_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∀ v, vecQ X bas (crd X bas v) = v) ∧ (∀ u v, crd X bas (u + v) = crd X bas u + crd X bas v) ∧ (∀ u v, EF X u v = -∑ i, (crd X bas u (Sum.inl i) * crd X bas v (Sum.inr i) - crd X bas u (Sum.inr i) * crd X bas v (Sum.inl i))) ∧ ∀ (y : Matrix (Fin n) (Fin r) E) (φ : TF n g), IsSB φ → IsSB (heisG X bas y φ) ∧ heisG X bas 0 φ = φ ∧ (∀ y', heisG X bas y (heisG X bas y' φ) = cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ))) • heisG X bas (y + y') φ) ∧ (∀ ψ, IsSB ψ → ip (heisG X bas y φ) (heisG X bas y ψ) = ip φ ψ) ∧ ∀ x ∈ X.dom, ∀ z : Fin n → Fin g → ℂ, thA X bas idx (heisG X bas y φ) x z = cexp (-(π * ∑ k, (hMat X bas idx x *ᵥ (z k + (1 / 2 : ℂ) • (per X x (y k) ∘ idx))) ⬝ᵥ imInv X bas idx x *ᵥ star (hMat X bas idx x *ᵥ (per X x (y k) ∘ idx)))) * thA X bas idx φ x (fun k => z k + per X x (y k) ∘ idx) := by
  intro E _ _ _ r X g bas idx n hs _
  refine ⟨vecQ_crd X bas, crd_add hs, EF_crd hs, fun y φ hφ => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.T.heisenbergOperatorRationalPoint_laws _ _
    (Matrix.of fun k i => crd X bas (y k) (Sum.inl i))
    (Matrix.of fun k i => crd X bas (y k) (Sum.inr i)) φ hφ
  refine ⟨h1, ?_, fun y' => ?_, h5, fun x hx z => ?_⟩
  · simp only [heisG, Matrix.zero_apply, crd_zero hs, show ∀ k, (0 : Matrix (Fin n) (Fin r) E) k = 0
      from fun _ => rfl]
    exact h4
  · rw [heisG, heisG, h3, heisG]
    congr 2
    · rw [← mul_neg, ← Rat.cast_neg, ← Finset.sum_neg_distrib]
      congr 2
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [EF_crd hs, neg_neg, Finset.sum_sub_distrib]
      simp only [dotProduct, of_apply, mul_comm]
    · ext k i
      exact (congrFun (crd_add hs (y k) (y' k)) _).symm
    · ext k i
      exact (congrFun (crd_add hs (y k) (y' k)) _).symm
  · have hz (w v) : hMat X bas idx x *ᵥ (w + per X x v ∘ idx) = hMat X bas idx x *ᵥ w +
        (qv (fun i => crd X bas v (Sum.inl i)) +
          tauMat X bas idx x *ᵥ qv fun i => crd X bas v (Sum.inr i)) := by
      rw [mulVec_add, hMat_mulVec_per_crd idx hs hx]
    have hz' (w v) : hMat X bas idx x *ᵥ (w + (1 / 2 : ℂ) • (per X x v ∘ idx)) =
        hMat X bas idx x *ᵥ w + (1 / 2 : ℂ) • (qv (fun i => crd X bas v (Sum.inl i)) +
          tauMat X bas idx x *ᵥ qv fun i => crd X bas v (Sum.inr i)) := by
      rw [mulVec_add, mulVec_smul, hMat_mulVec_per_crd idx hs hx]
    rw [thA, thA, heisG, h2 _ ⟨tauMat_isSymm idx hs hx, tauMat_im_posDef idx hs hx⟩]
    change Fin n → Fin r → E at y
    simp only [hz, hz', hMat_mulVec_per_crd idx hs hx]
    have he := Finset.sum_congr (s₁ := Finset.univ) rfl fun (k : Fin n) _ =>
      heis_exponent _ _ (tauMat_isSymm idx hs hx) (imInv_isSymm idx hs hx) (imInv_mul_im idx hs hx)
        (fun i => crd X bas (y k) (Sum.inl i)) (fun i => crd X bas (y k) (Sum.inr i))
        (hMat X bas idx x *ᵥ z k)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_add_distrib (f := fun k => -_),
      Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at he
    have he' := congrArg cexp he
    rw [Complex.exp_add, Complex.exp_add] at he'
    simp only [← add_assoc (hMat X bas idx x *ᵥ z _)] at he' ⊢
    rw [mul_assoc, ← mul_assoc (cexp _)]
    erw [he']
    rw [mul_assoc, mul_left_comm, ← mul_assoc _ (cexp (π / 2 * _))]
    rfl

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem aLin_mulVec_of_lt (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (w : Fin r → ℂ) {a : Fin r}
    (h : (a : ℕ) < X.p0) :
    (aLin X x₁ x₂ τ *ᵥ w) a = hermC τ.1 X.Gm w (FD.col (mat x₂ τ) a) := by
  simp only [aLin, mulVec, dotProduct, of_apply, if_pos h, hermC, FD.col, mat, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

theorem aLin_mulVec_of_not_lt (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (w : Fin r → ℂ) {a : Fin r}
    (h : ¬ (a : ℕ) < X.p0) :
    (aLin X x₁ x₂ τ *ᵥ w) a = ((mat x₁ τ)⁻¹ *ᵥ w) a := by
  simp only [aLin, mulVec, dotProduct, of_apply, if_neg h]

variable {X}

theorem pos_of_upper {x₁ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (x₂ : Frame X.Ψ r) (τ : X.Ψ)
    {w : Fin r → ℂ} (hw : w ≠ 0)
    (h : ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → (aLin X x₁ x₂ τ *ᵥ w) a = 0) :
    0 < (hermC τ.1 X.Gm w w).re := by
  set c := (mat x₁ τ)⁻¹ *ᵥ w with hc
  have hu : IsUnit (mat x₁ τ).det := isUnit_iff_ne_zero.2 (h₁ τ).1
  have hcw : mat x₁ τ *ᵥ c = w := by rw [hc, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hc0 : ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → c a = 0 := fun a ha => by
    rw [hc, ← aLin_mulVec_of_not_lt X x₁ x₂ τ w ha, h a ha]
  have hsum : w = ∑ a : Fin X.p0, c (Fin.castLE X.p0_le a) • X.colP x₁ τ a := by
    rw [← hcw, Data.mulVec_eq_sum_col]
    symm
    refine Finset.sum_of_injOn (Fin.castLE X.p0_le) (Fin.castLE_injective _).injOn
      (fun _ _ => Finset.mem_univ _) (fun i _ hi => ?_) (fun _ _ => rfl)
    rw [hc0 i, zero_smul]
    intro hlt
    exact hi ⟨⟨i, hlt⟩, by simp, rfl⟩
  have hne : (fun a : Fin X.p0 => c (Fin.castLE X.p0_le a)) ≠ 0 := by
    intro h0
    apply hw
    rw [hsum]
    exact Finset.sum_eq_zero fun a _ => by rw [congrFun h0 a, Pi.zero_apply, zero_smul]
  have := quad_re_pos (X.gramPos_posDef h₁ τ) hne
  rw [hsum, hermC_quad]
  exact this

theorem neg_of_lower (x₁ : Frame X.Ψ r) {x₂ : Frame X.Ψ r} (h₂ : x₂ ∈ X.dom) (τ : X.Ψ)
    {w : Fin r → ℂ} (hw : w ≠ 0)
    (h : ∀ a : Fin r, (a : ℕ) < X.p0 → (aLin X x₁ x₂ τ *ᵥ w) a = 0) :
    (hermC τ.1 X.Gm w w).re < 0 :=
  X.neg_of_perp h₂ τ hw fun b => by
    have hb : ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0 := b.2
    rw [Data.colP, ← aLin_mulVec_of_lt X x₁ x₂ τ w hb, h _ hb]

theorem det_aLin_ne_zero {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ) :
    (aLin X x₁ x₂ τ).det ≠ 0 := by
  intro h
  obtain ⟨w, hw, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have a := pos_of_upper h₁ x₂ τ hw fun a _ => congrFun h0 a
  have b := neg_of_lower x₁ h₂ τ hw fun a _ => congrFun h0 a
  linarith


variable (X) in
theorem aLin_swap (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) :
    aLin X x₂ x₁ τ = (aAnti X x₁ x₂ τ).map conj := by
  ext a c
  simp only [aLin, aAnti, map_apply, of_apply]
  split_ifs
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, ← emb_cc, X.Gm_herm]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · rw [Complex.conj_conj]

theorem det_aAnti_ne_zero {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ) :
    (aAnti X x₁ x₂ τ).det ≠ 0 := by
  intro h
  apply det_aLin_ne_zero h₂ h₁ τ
  rw [aLin_swap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]

theorem re_hermC_invol_neg {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ)
    {d : Fin r → ℂ} (hd : d ≠ 0) :
    (hermC τ.1 X.Gm (((aLin X x₁ x₂ τ)⁻¹ *
      Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) * aLin X x₁ x₂ τ) *ᵥ d) d).re
      < 0 := by
  set A := aLin X x₁ x₂ τ with hA
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 (det_aLin_ne_zero h₁ h₂ τ)
  set y := A *ᵥ d with hy
  set yp : Fin r → ℂ := fun a => if (a : ℕ) < X.p0 then y a else 0 with hyp
  set ym : Fin r → ℂ := fun a => if (a : ℕ) < X.p0 then 0 else y a with hym
  set d₁ := A⁻¹ *ᵥ yp with hd₁
  set d₂ := A⁻¹ *ᵥ ym with hd₂
  have e₁ : A *ᵥ d₁ = yp := by rw [hd₁, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have e₂ : A *ᵥ d₂ = ym := by rw [hd₂, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hsum : d = d₁ + d₂ := by
    have : yp + ym = y := by
      funext a; simp only [hyp, hym, Pi.add_apply]; split_ifs <;> simp
    rw [hd₁, hd₂, ← mulVec_add, this, hy, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have hS : (A⁻¹ * Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) * A) *ᵥ d
      = d₂ - d₁ := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hd₁, hd₂, ← mulVec_sub, ← hy]
    congr 1
    funext a
    simp [Matrix.mulVec_diagonal, hyp, hym, sgn]
    split_ifs <;> simp
  have p₁ : d₁ ≠ 0 → 0 < (hermC τ.1 X.Gm d₁ d₁).re := fun h =>
    pos_of_upper h₁ x₂ τ h fun a ha => by rw [← hA, e₁]; simp only [hyp, if_neg ha]
  have p₂ : d₂ ≠ 0 → (hermC τ.1 X.Gm d₂ d₂).re < 0 := fun h =>
    neg_of_lower x₁ h₂ τ h fun a ha => by rw [← hA, e₂]; simp only [hym, if_pos ha]
  have hc : (hermC τ.1 X.Gm d₁ d₂).re = (hermC τ.1 X.Gm d₂ d₁).re := by
    rw [← hermC_conj τ.1 X.Gm_herm d₁ d₂, Complex.conj_re]
  have key : (hermC τ.1 X.Gm (d₂ - d₁) (d₁ + d₂)).re =
      (hermC τ.1 X.Gm d₂ d₂).re - (hermC τ.1 X.Gm d₁ d₁).re := by
    rw [hermC_sub_left, hermC_add_right, hermC_add_right]
    simp only [Complex.sub_re, Complex.add_re, hc]
    ring
  rw [hS]
  rw [← hsum] at key
  rw [key]
  by_cases z₁ : d₁ = 0
  · have z₂ : d₂ ≠ 0 := fun z₂ => hd (by rw [hsum, z₁, z₂, add_zero])
    have := p₂ z₂
    rw [z₁, hermC_zero_left, Complex.zero_re]
    linarith
  · have := p₁ z₁
    by_cases z₂ : d₂ = 0
    · rw [z₂, hermC_zero_left, Complex.zero_re]
      linarith
    · have := p₂ z₂
      linarith

theorem posDef_imH {N : ℕ} {Z : Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ v : Fin N → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ Z *ᵥ v).im) : (imH Z).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · unfold imH
    rw [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
      ← neg_sub Z, smul_neg, ← neg_smul]
    congr 1
    simp
  · have e : star v ⬝ᵥ Zᴴ *ᵥ v = conj (star v ⬝ᵥ Z *ᵥ v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, Complex.star_def, map_sum,
        map_mul, Complex.conj_conj, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have : star v ⬝ᵥ imH Z *ᵥ v = ((star v ⬝ᵥ Z *ᵥ v).im : ℂ) := by
      unfold imH
      rw [smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, e, Complex.sub_conj,
        smul_eq_mul]
      push_cast
      field_simp
    rw [this]
    exact_mod_cast h v hv


variable (X) in
theorem re_kappa (τ : E →+* ℂ) : (τ X.κ0).re = 0 := by
  have h : conj (τ X.ξ0) = -τ X.ξ0 := by rw [← emb_cc, X.ξ0_im, map_neg]
  have h' := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at h'
  have h0 : (τ X.ξ0).re = 0 := by linarith
  rcases X.κ0_xi with e | e <;> simp [e, h0, map_ofNat]

theorem dblZ_mem {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) :
    dblZ X x₁ x₂ ∈ Hn X.Ψ r := by
  intro τ
  refine posDef_imH fun v hv => ?_
  have hd : star v ≠ 0 := by simpa using hv
  have h := re_hermC_invol_neg h₁ h₂ τ hd
  set S := (aLin X x₁ x₂ τ)⁻¹ *
      Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) * aLin X x₁ x₂ τ with hS
  have e : star v ⬝ᵥ dblZ X x₁ x₂ τ *ᵥ v =
      τ.1 X.κ0 / 4 * hermC τ.1 X.Gm (S *ᵥ star v) (star v) := by
    unfold dblZ
    rw [← hS, smul_mulVec, dotProduct_smul, smul_eq_mul, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose]
    congr 1
    simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [e, Complex.mul_im]
  have k₁ : (τ.1 X.κ0 / 4).re = 0 := by simp [re_kappa X τ.1]
  have k₂ : (τ.1 X.κ0 / 4).im < 0 := by
    have := X.κ0_sign τ
    simp only [Complex.div_ofNat_im]
    linarith
  rw [k₁, zero_mul, zero_add]
  exact mul_pos_of_neg_of_neg k₂ h

end GlobalTheory.SW.DblPoint

namespace GlobalTheory.SW

theorem dblZ_mem_Hn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, IsType X.Ψ ∧ dblZ X x₁ x₂ ∈ Hn X.Ψ r ∧ ∀ τ, (aLin X x₁ x₂ τ).det ≠ 0 ∧ (aAnti X x₁ x₂ τ).det ≠ 0 ∧ aLin X x₂ x₁ τ = (aAnti X x₁ x₂ τ).map conj :=
  fun _ _ _ _ _ X x₁ h₁ x₂ h₂ => ⟨X.cmType, DblPoint.dblZ_mem h₁ h₂, fun τ =>
    ⟨DblPoint.det_aLin_ne_zero h₁ h₂ τ, DblPoint.det_aAnti_ne_zero h₁ h₂ τ,
      DblPoint.aLin_swap X x₁ x₂ τ⟩⟩

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHnStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dblZ_mem_Hn_and_det_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, IsType X.Ψ ∧ dblZ X x₁ x₂ ∈ Hn X.Ψ r ∧ ∀ τ, (aLin X x₁ x₂ τ).det ≠ 0 ∧ (aAnti X x₁ x₂ τ).det ≠ 0 ∧ aLin X x₂ x₁ τ = (aAnti X x₁ x₂ τ).map conj := by
  first | exact @GlobalTheory.SW.dblZ_mem_Hn | exact GlobalTheory.SW.dblZ_mem_Hn | (intros; apply GlobalTheory.SW.dblZ_mem_Hn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LactMulFrame
namespace GlobalTheory.LeftActionFrameMul

open ReciprocityTheory.ChartRestriction.G.FD

theorem lact_mul_frame {E : Type} [Field E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (γ' γ : GL (Fin r) E) (x : Frame Ψ r) : lact (γ' * γ) x = lact γ' (lact γ x) := by
  funext τ

  show ((γ' * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

end GlobalTheory.LeftActionFrameMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFamilyInvariantOfFockInner
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem sum_mul_conj_orthonormalBasis {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Fintype ι] (b b' : OrthonormalBasis ι ℂ V) (l l' : V →ₗ[ℂ] ℂ) :
    ∑ j, l (b j) * conj (l' (b j)) = ∑ j, l (b' j) * conj (l' (b' j)) := by
  have := FiniteDimensional.complete ℂ V
  have h (l : V →ₗ[ℂ] ℂ) : ∃ a : V, ∀ v, l v = inner ℂ a v :=
    ⟨(InnerProductSpace.toDual ℂ V).symm (LinearMap.toContinuousLinearMap l), fun v => by
      rw [InnerProductSpace.toDual_symm_apply]; rfl⟩
  obtain ⟨a, ha⟩ := h l
  obtain ⟨a', ha'⟩ := h l'
  simp only [ha, ha', inner_conj_symm, OrthonormalBasis.sum_inner_mul_inner]

theorem exists_family_invariant_of_fockInner {σ : Type} (W : Submodule ℂ (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ W] (hW : W ≠ ⊥) :
    ∃ (m : ℕ) (P : Fin m → MvPolynomial σ ℂ), (∀ j, P j ∈ W) ∧ (∃ j, P j ≠ 0) ∧
      ∀ f : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ, (∀ Q ∈ W, f Q ∈ W) →
        (∀ Q Q', MvPoly.fockInner (f Q) (f Q') = MvPoly.fockInner Q Q') →
        ∀ l l' : MvPolynomial σ ℂ →ₗ[ℂ] ℂ,
          ∑ j, l (f (P j)) * conj (l' (f (P j))) = ∑ j, l (P j) * conj (l' (P j)) := by
  let cr : InnerProductSpace.Core ℂ W :=
    { inner := fun x y => MvPoly.fockInner (y : MvPolynomial σ ℂ) x
      conj_inner_symm := fun x y => MvPoly.fockInner_conj_symm _ _
      re_inner_nonneg := fun x => by
        rw [MvPoly.fockInner_self, RCLike.ofReal_re]; exact MvPoly.fockNormSq_nonneg _
      add_left := fun x y z => MvPoly.fockInner_add_right _ _ _
      smul_left := fun x y r => MvPoly.fockInner_smul_right _ _ _
      definite := fun x hx => by
        rw [MvPoly.fockInner_self] at hx
        exact Subtype.ext (MvPoly.fockNormSq_eq_zero.mp (RCLike.ofReal_eq_zero.mp hx)) }
  letI : NormedAddCommGroup W := cr.toNormedAddCommGroup
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore cr.toCore
  let b := stdOrthonormalBasis ℂ W
  have hpos : 0 < Module.finrank ℂ W := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]; exact hW
  refine ⟨_, fun j => b j, fun j => (b j).2, ⟨⟨0, hpos⟩, fun e => ?_⟩, fun f hf hi l l' => ?_⟩
  · exact b.orthonormal.ne_zero _ (Subtype.ext e)
  · let U : W →ₗᵢ[ℂ] W := (f.restrict hf).isometryOfInner fun x y => hi _ _
    exact sum_mul_conj_orthonormalBasis (b.map (U.toLinearIsometryEquiv rfl)) b
      (l ∘ₗ W.subtype) (l' ∘ₗ W.subtype)

theorem exists_invFam_rowHighest : ∀ (T : Type) [Fintype T] [DecidableEq T] (p q n : ℕ)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ), p + q ≤ n →
    ∃ (m : ℕ) (P : Fin m → Harm.Poly ℂ T p q (Fin n)), (∀ j, P j ∈ Harm.rowHighest ℂ c c') ∧
      (∃ j, P j ≠ 0) ∧ InvFam P := by
  intro T _ _ p q n c c' h
  obtain ⟨m, P, h₁, h₂, h₃⟩ := exists_family_invariant_of_fockInner
    (Harm.rowHighest (κ := Fin n) ℂ c c') (Harm.rowHighest_ne_bot h c c')
  refine ⟨m, P, h₁, h₂, fun u hu z w => ?_⟩
  have hs : star u * u = 1 := funext fun t => Units.ext (Matrix.mem_unitaryGroup_iff'.mp (hu t))
  refine h₃ (Harm.colActHom u).toLinearMap (fun Q hQ => Harm.colAct_mem_rowHighest u hQ)
    (fun Q Q' => ?_) (MvPolynomial.aeval z).toLinearMap (MvPolynomial.aeval w).toLinearMap
  change MvPoly.fockInner (Harm.colAct ℂ T p q (Fin n) u Q) (Harm.colAct ℂ T p q (Fin n) u Q') = _
  rw [Harm.fockInner_colAct, ← AlgEquiv.mul_apply, ← map_mul, hs, map_one, AlgEquiv.one_apply]

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivEqSumList
open Filter Topology
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.SW.KernSym

variable {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

noncomputable abbrev lst (m : σ →₀ ℕ) : List σ := (Finsupp.toMultiset m).toList

theorem polyDeriv_eq_sum_list (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} {x : W}
    (hF : AnalyticAt ℂ F x) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F x = ∑ m ∈ P.support, P.coeff m * lineDerivList ℂ ((lst m).map u) F x := by
  rw [dirPolyDeriv_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dirPolyDeriv_monomial_eq_lineDerivList (Multiset.coe_toList _) u hF]

theorem polyDeriv_polyDeriv (P Q : MvPolynomial σ ℂ) (u : σ → W) {F : W × W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ F p) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => ReciprocityTheory.ChartRestriction.G.I2.polyDeriv Q u (fun w => F (z, w)) 0) 0 =
      ∑ m ∈ P.support, ∑ m' ∈ Q.support, P.coeff m * Q.coeff m' *
        lineDerivList ℂ ((lst m).map (fun s => (u s, 0)) ++ (lst m').map (fun s => (0, u s)))
          F 0 := by
  have h1 (z : W) : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv Q u (fun w => F (z, w)) 0 = ∑ m' ∈ Q.support, Q.coeff m' •
      lineDerivList ℂ ((lst m').map (fun s => (0, u s))) F (LinearMap.inl ℂ W W z) := by
    have ha : AnalyticAt ℂ (fun w => F (z, w)) 0 := (hF _).comp₂ analyticAt_const analyticAt_id
    rw [polyDeriv_eq_sum_list _ _ ha]
    refine Finset.sum_congr rfl fun m' _ => ?_
    have h2 := congrFun (lineDerivList_comp_linearMap (LinearMap.inr ℂ W W) ((lst m').map u)
      (fun p => F (p + (z, 0)))) 0
    rw [lineDerivList_comp_add_const] at h2
    simp only [LinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero, List.map_map] at h2
    rw [h2]
    rfl
  have h3 (m' : σ →₀ ℕ) : AnalyticAt ℂ (fun z => Q.coeff m' •
      lineDerivList ℂ ((lst m').map (fun s => (0, u s))) F (LinearMap.inl ℂ W W z)) 0 :=
    analyticAt_const.fun_smul
      ((analyticAt_lineDerivList (hF _) _).comp ((ContinuousLinearMap.inl ℂ W W).analyticAt 0))
  simp only [h1]
  rw [polyDeriv_eq_sum_list _ _ (Finset.analyticAt_fun_sum _ fun m' _ => h3 m')]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [lineDerivList_sum _ fun m' _ => h3 m', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [lineDerivList_const_smul, lineDerivList_comp_linearMap, lineDerivList_append, List.map_map,
    mul_assoc]
  simp only [map_zero]
  rfl

theorem lineDerivList_conj {V : Type} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] (l : List V) (hl : ∀ v ∈ l, star v = v) (F : V → ℂ) :
    lineDerivList ℂ l (fun z => conj (F (star z))) =
      fun z => conj (lineDerivList ℂ l F (star z)) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    rw [lineDerivList_cons, ih fun w hw => hl w (List.mem_cons_of_mem _ hw), lineDerivList_cons]
    simp only [lineDeriv, star_add, star_smul, hl v List.mem_cons_self]
    have h := congrFun (deriv_conj_conj (f := fun t : ℂ => lineDerivList ℂ l F (star z + t • v))) 0
    simpa [Function.comp_def] using h

theorem polyDeriv_barP_symm [StarAddMonoid W] [StarModule ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W)
    (hu : ∀ s, star (u s) = u s) {F G : W → W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ (fun p : W × W => F p.1 p.2) p)
    (hG : ∀ p, AnalyticAt ℂ (fun p : W × W => G p.1 p.2) p)
    (h : ∀ z w, G z w = conj (F (star w) (star z))) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u (G z) 0) 0 =
      conj (ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u (F z) 0) 0) := by
  have hs : (barP P).support = P.support :=
    MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective
  have hc (m : σ →₀ ℕ) : (barP P).coeff m = conj (P.coeff m) := MvPolynomial.coeff_map _ _ _
  have e1 := polyDeriv_polyDeriv P (barP P) u hF
  have e2 := polyDeriv_polyDeriv P (barP P) u hG
  dsimp only at e1 e2
  rw [e1, e2, hs, Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc, Complex.conj_conj]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  have h1 : (fun p : W × W => G p.1 p.2) =
      fun p => conj ((fun q : W × W => F q.2 q.1) (star p)) := funext fun p => h p.1 p.2
  have h2 (l : List (W × W)) := congrFun (lineDerivList_comp_linearMap
    (LinearEquiv.prodComm ℂ W W).toLinearMap l (fun p : W × W => F p.1 p.2)) 0
  simp only [LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    Prod.swap_zero] at h2
  rw [h1, lineDerivList_conj _ (by
    simp only [List.mem_append, List.mem_map]
    rintro v (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> simp [Prod.ext_iff, hu]) fun q : W × W => F q.2 q.1]
  simp only [star_zero]
  rw [h2, List.map_append, List.map_map, List.map_map,
    lineDerivList_perm (hF 0) List.perm_append_comm, mul_comm (P.coeff m')]
  rfl

theorem lineDerivList_exp (ℓ : W →L[ℂ] ℂ) (C : ℂ) (l : List W) :
    lineDerivList ℂ l (fun w => C * Complex.exp (ℓ w)) =
      fun w => (l.map ℓ).prod * (C * Complex.exp (ℓ w)) := by
  induction l with
  | nil => simp [lineDerivList]
  | cons v l ih =>
    funext w
    rw [lineDerivList_cons, ih]
    have h := (((ℓ.hasFDerivAt (x := w)).cexp.const_mul C).const_mul
      (l.map ℓ).prod).hasLineDerivAt v
    simp only [h.lineDeriv, List.map_cons, List.prod_cons, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring

theorem polyDeriv_exp (Q : MvPolynomial σ ℂ) (u : σ → W) (ℓ : W →L[ℂ] ℂ) (C : ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv Q u (fun w => C * Complex.exp (ℓ w)) 0 =
      C * MvPolynomial.eval (fun s => ℓ (u s)) Q := by
  have ha : AnalyticAt ℂ (fun w => C * Complex.exp (ℓ w)) 0 :=
    analyticAt_const.mul (ℓ.analyticAt 0).cexp
  rw [polyDeriv_eq_sum_list _ _ ha, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : ((List.map u (lst m)).map ℓ).prod = ∏ i ∈ m.support, ℓ (u i) ^ m i := by
    rw [List.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList,
      Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (by simp)
        (by simp [pow_add])]
    rfl
  rw [lineDerivList_exp, h]
  simp only [map_zero, Complex.exp_zero]
  ring

theorem coeff_aeval_smul_X [Fintype σ] (t : σ → ℂ) (Q : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m
      (MvPolynomial.aeval (fun s => t s • (MvPowerSeries.X s : MvPowerSeries σ ℂ)) Q) =
      (∏ s, t s ^ m s) * Q.coeff m := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial n c =>
    have h : n.prod (fun s k => (t s • (MvPowerSeries.X s : MvPowerSeries σ ℂ)) ^ k) =
        (∏ s, t s ^ n s) • MvPowerSeries.monomial n 1 := by
      rw [← MvPolynomial.coe_monomial, MvPolynomial.monomial_eq,
        ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
      simp only [map_one, one_mul, smul_pow, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod, map_pow]
      rw [Finsupp.prod_fintype _ _ (by simp), Finset.prod_smul]
      simp
    rw [MvPolynomial.aeval_monomial, h, ← Algebra.smul_def, map_smul, map_smul,
      MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases e : m = n
    · subst e; simp [mul_comm]
    · simp [e, Ne.symm e]
  | add P Q hP hQ => simp only [map_add (f := _), hP, hQ, MvPolynomial.coeff_add, mul_add]

theorem polyDeriv_barP_exp [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℂ) (u : σ → W)
    (π : σ → W →L[ℂ] ℂ) (hπ : ∀ s s', π s (u s') = if s = s' then 1 else 0) (t : σ → ℝ) (C : ℝ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u
      (fun w => C * Complex.exp (∑ s, t s * π s z * π s w)) 0) 0 =
      ((C * ∑ m ∈ P.support, (∏ s, (m s).factorial : ℕ) * (∏ s, t s ^ m s) *
        Complex.normSq (P.coeff m) : ℝ) : ℂ) := by
  have h1 (z : W) : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u
      (fun w => C * Complex.exp (∑ s, t s * π s z * π s w)) 0 =
      C * MvPolynomial.eval (fun s => ((t s : ℂ) • π s) z) (barP P) := by
    have h := polyDeriv_exp (barP P) u (∑ s, (t s * π s z) • π s) C
    simpa [hπ] using h
  have h2 (s : σ) : taylorDir u ((t s : ℂ) • π s : W →L[ℂ] ℂ) = (t s : ℂ) • MvPowerSeries.X s := by
    rw [taylorDir_clm]
    simp [hπ]
  have ha (s : σ) : AnalyticAt ℂ ((t s : ℂ) • π s : W →L[ℂ] ℂ) 0 := ContinuousLinearMap.analyticAt _ _
  have h3 : taylorDir u (fun z => C * MvPolynomial.eval (fun s => ((t s : ℂ) • π s) z) (barP P)) =
      (C : ℂ) • MvPolynomial.aeval (fun s => (t s : ℂ) • (MvPowerSeries.X s : MvPowerSeries σ ℂ))
        (barP P) := by
    simp only [← h2]
    rw [← taylorDir_eval u ha, ← taylorDir_smul]
    · rfl
    · exact AnalyticAt.aeval_mvPolynomial ha _
  simp only [h1]
  rw [dirPolyDeriv_eq_sum_coeff_taylorDir, h3]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, coeff_aeval_smul_X, barP, MvPolynomial.coeff_map, ← Complex.mul_conj, smul_eq_mul]
  ring

theorem apolar_norm_pos [Fintype σ] {P : MvPolynomial σ ℂ} (hP : P ≠ 0) {t : σ → ℝ}
    (ht : ∀ s, 0 < t s) :
    0 < ∑ m ∈ P.support, ((∏ s, (m s).factorial : ℕ) : ℝ) * (∏ s, t s ^ m s) *
        Complex.normSq (P.coeff m) := by
  refine Finset.sum_pos (fun m hm => ?_) (MvPolynomial.support_nonempty.2 hP)
  refine mul_pos (mul_pos ?_ (Finset.prod_pos fun s _ => pow_pos (ht s) _))
    (Complex.normSq_pos.2 (MvPolynomial.mem_support_iff.1 hm))
  exact_mod_cast Finset.prod_pos fun s _ => Nat.factorial_pos _

end GlobalTheory.SW.KernSym
end
