module

public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfLaws
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MulVecOfRealVecAddMemSpanPeriodLattice
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemPeriodLatticeOfThetaTranslateEqUnitMul
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHalfOfSqEqOne
noncomputable section

open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real

namespace GlobalTheory.ThetaPoint

open CanTh

variable {g : ℕ}

theorem isSymm_and_eq_imInv {M τ : Matrix (Fin g) (Fin g) ℂ} (hH : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) (hτ : (τ.map Complex.im).PosDef)
    {s : ℝ} (hs : s = 1 ∨ s = -1)
    (h₁₁ : ∀ i j, (hermForm M (Pi.single i 1) (Pi.single j 1)).im = 0)
    (h₁₂ : ∀ i j, (hermForm M (Pi.single i 1) (τ *ᵥ Pi.single j 1)).im = if i = j then s else 0)
    (h₂₂ : ∀ i j, (hermForm M (τ *ᵥ Pi.single i 1) (τ *ᵥ Pi.single j 1)).im = 0) :
    τ.IsSymm ∧ M = imInv τ := by
  let Y : Matrix (Fin g) (Fin g) ℝ := M.map Complex.re
  have hY : M = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [Y]
    · have := h₁₁ i j
      rw [hermForm, SiegelNormalForm.form_single] at this
      simpa using this
  have hYs : Yᵀ = Y := by
    ext i j
    have := congrArg Complex.re (hH.apply i j)
    simpa [Y] using this
  have hYp : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hYs) ?_
    intro a ha
    have hne : (fun i => (a i : ℂ)) ≠ 0 := fun h0 =>
      ha (funext fun i => by simpa using congrFun h0 i)
    have := hpos _ hne
    rw [hY] at this
    simpa [hermForm, Matrix.mulVec, dotProduct] using this
  rw [hY] at h₁₂ h₂₂
  rcases hs with rfl | rfl
  · obtain ⟨-, h2, -⟩ := SiegelNormalForm.siegel_of_relations Y hYp (-τ)
      (fun i j => by
        have := h₁₂ i j
        rw [hermForm] at this
        rw [Matrix.neg_mulVec, star_neg, Matrix.mulVec_neg, dotProduct_neg, Complex.neg_im, this]
        split_ifs <;> simp)
      (fun i j => by
        have := h₂₂ i j
        rw [hermForm] at this
        rw [Matrix.neg_mulVec, Matrix.neg_mulVec, star_neg, Matrix.mulVec_neg, dotProduct_neg,
          neg_dotProduct, neg_neg, this])
    have hf : ∀ i : Fin g, False := fun i => by
      have e1 := h2.diag_pos (i := i)
      have e2 := hτ.diag_pos (i := i)
      simp only [Matrix.map_apply, Matrix.neg_apply, Complex.neg_im] at e1 e2
      linarith
    exact ⟨by ext i; exact (hf i).elim, by ext i; exact (hf i).elim⟩
  · obtain ⟨h1, -, h3⟩ := SiegelNormalForm.siegel_of_relations Y hYp τ h₁₂ h₂₂
    refine ⟨h1, ?_⟩
    rw [hY, imInv, Matrix.inv_eq_left_inv h3]

def lawSubgroup {Λ V : Type*} [AddCommGroup Λ] [AddCommGroup V] (ι : Λ →+ V) (J : Λ → V → ℂ)
    (hJ : ∀ l z, J l z ≠ 0) (hc : ∀ l m z, J (l + m) z = J l (z + ι m) * J m z) (θ : V → ℂ) :
    AddSubgroup Λ where
  carrier := {l | ∀ z, θ (z + ι l) = J l z * θ z}
  zero_mem' := fun z => by
    have h := hc 0 0 z
    rw [add_zero, map_zero, add_zero] at h
    rw [map_zero, add_zero, (mul_eq_left₀ (hJ 0 z)).1 h.symm, one_mul]
  add_mem' := fun {l m} hl hm z => by
    rw [map_add (f := _), add_comm (ι l), ← add_assoc, hl, hm, hc, mul_assoc]
  neg_mem' := fun {l} hl z => by
    have h0 := hc 0 0 z
    rw [add_zero, map_zero, add_zero] at h0
    have h1 := hc l (-l) z
    rw [add_neg_cancel, (mul_eq_left₀ (hJ 0 z)).1 h0.symm] at h1
    have h2 := hl (z + ι (-l))
    rw [add_assoc, ← map_add (f := _), neg_add_cancel, map_zero, add_zero] at h2
    rw [h2, ← mul_assoc, mul_comm (J (-l) z), ← h1, one_mul]

theorem exists_half_of_sq_eq_one {c : ℂ} (hc : c ^ 2 = 1) :
    ∃ a : ℝ, (a = 0 ∨ a = 1 / 2) ∧ cexp (2 * π * I * a) = c ∧ cexp (-(2 * π * I * a)) = c := by
  rcases sq_eq_one_iff.1 hc with rfl | rfl
  · exact ⟨0, Or.inl rfl, by simp, by simp⟩
  · refine ⟨1 / 2, Or.inr rfl, ?_, ?_⟩
    · rw [← Complex.exp_pi_mul_I]; congr 1; push_cast; ring
    · rw [← Complex.exp_neg_pi_mul_I]; congr 1; push_cast; ring

theorem exists_half_char {d : ℕ} (Λ : Submodule ℤ (Fin d → ℂ)) (Hm : Matrix (Fin d) (Fin d) ℂ) (χ : Λ → ℂ)
    (Φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef)
    (hform : ∀ z w, hermForm Hm (Φ z) (Φ w) = hermForm (imInv τ) z w)
    (hΛ : ∀ z, Φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ))
    (hχ : ∀ l, χ l ^ 2 = 1)
    (hc : ∀ (l m : Λ) z, χ (l + m) * cexp (π * hermForm Hm z (l + m : Λ) + π / 2 * hermForm Hm (l + m : Λ) (l + m : Λ)) =
      χ l * cexp (π * hermForm Hm (z + m) l + π / 2 * hermForm Hm l l) *
        (χ m * cexp (π * hermForm Hm z m + π / 2 * hermForm Hm m m))) :
    ∃ a b : Fin g → ℝ, (∀ k, a k = 0 ∨ a k = 1 / 2) ∧ (∀ k, b k = 0 ∨ b k = 1 / 2) ∧
      ∀ (l : Λ) z, canTh τ a b (Φ.symm (z + l)) =
        χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l) * canTh τ a b (Φ.symm z) := by
  have hsingle : ∀ j : Fin g, (fun i => (((Pi.single j (1 : ℤ) : Fin g → ℤ) i : ℤ) : ℂ)) = Pi.single j (1 : ℂ) := by
    intro j
    ext i
    by_cases hij : i = j <;> simp [Pi.single_apply, hij]
  have hzero : (fun i => (((0 : Fin g → ℤ) i : ℤ) : ℂ)) = 0 := by ext i; simp
  let e : Fin g → Λ := fun i => ⟨Φ (Pi.single i 1), (hΛ _).2 ⟨Pi.single i 1, 0, by
    rw [hsingle, hzero, mulVec_zero, add_zero]⟩⟩
  let f : Fin g → Λ := fun i => ⟨Φ (τ *ᵥ Pi.single i 1), (hΛ _).2 ⟨0, Pi.single i 1, by
    rw [hsingle, hzero, zero_add]⟩⟩
  choose a ha ha' _ using fun i => exists_half_of_sq_eq_one (hχ (e i))
  choose b hb _ hb' using fun i => exists_half_of_sq_eq_one (hχ (f i))
  refine ⟨a, b, ha, hb, fun l => ?_⟩
  let S := lawSubgroup Λ.subtype.toAddMonoidHom
    (fun l z => χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))
    (fun l z => mul_ne_zero (fun h => by simpa [h] using hχ l) (Complex.exp_ne_zero _)) hc
    (fun z => canTh τ a b (Φ.symm z))
  have key : ∀ (l : Λ) (m n : Fin g → ℤ), (l : Fin d → ℂ) = Φ ((fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) →
      canMult a b m n = χ l → l ∈ S := fun l m n hl hm z => by
    obtain ⟨z, rfl⟩ := Φ.surjective z
    change canTh τ a b (Φ.symm (Φ z + l)) = χ l * cexp (π * hermForm Hm (Φ z) l + π / 2 * hermForm Hm l l) *
      canTh τ a b (Φ.symm (Φ z))
    rw [hl, ← map_add (f := _), Φ.symm_apply_apply, Φ.symm_apply_apply, hform, hform,
      canTh_add_period hs hp a b m n rfl, hm]
  have he : ∀ i, e i ∈ S := fun i => key _ (Pi.single i 1) 0
    (by rw [hsingle, hzero, mulVec_zero, add_zero]) (by
      rw [← ha', canMult]
      congr 1
      simp [dotProduct, Pi.single_apply])
  have hf : ∀ i, f i ∈ S := fun i => key _ 0 (Pi.single i 1)
    (by rw [hsingle, hzero, zero_add]) (by
      rw [← hb', canMult]
      congr 1
      simp [dotProduct, Pi.single_apply])
  obtain ⟨m, n, hmn⟩ := (hΛ (Φ.symm l)).1 (by rw [Φ.apply_symm_apply]; exact l.2)
  have hl : l = ∑ i, m i • e i + ∑ i, n i • f i := by
    apply Subtype.ext
    have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [← Φ.apply_symm_apply l, hmn, h1 m, h1 n]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_add (f := _), map_sum, map_zsmul, e, f]
    simp
  have : l ∈ S := hl ▸ S.add_mem (S.sum_mem fun i _ => S.zsmul_mem (he i) _)
    (S.sum_mem fun i _ => S.zsmul_mem (hf i) _)
  exact this

theorem half_char_unique {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    {a b a' b' : Fin g → ℝ} (ha : ∀ k, a k = 0 ∨ a k = 1 / 2) (hb : ∀ k, b k = 0 ∨ b k = 1 / 2)
    (ha' : ∀ k, a' k = 0 ∨ a' k = 1 / 2) (hb' : ∀ k, b' k = 0 ∨ b' k = 1 / 2)
    {U : (Fin g → ℂ) → ℂ} (hU : Differentiable ℂ U) (hU0 : ∀ z, U z ≠ 0)
    (h : ∀ z, theta a' b' z τ = U z * theta a b z τ) : a' = a ∧ b' = b := by
  have H₁ : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
      (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z,
        (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') =
          eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧
        (fun z => theta 0 0 z τ) ≠ 0 := fun g τ hτ => by
    refine ⟨⟨?_, fun n n' z => ?_⟩, theta_ne_zero hτ 0 0⟩
    · have := differentiable_thetaChar (mem_thetaDomain hτ.2) 0 0
      simpa only [← thetaChar_eq_theta] using this
    · have h0 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
      simp only [thetaQuasiPeriod_holds (Fin g) 0 0 z τ n n' hτ.1, autFactor, h0, zero_dotProduct, sub_zero, eC_zero,
        one_mul]
      congr 2
      ring
  let p : (Fin g → ℝ) → (Fin g → ℝ) → (Fin g → ℂ) → ℂ := fun a b z =>
    eC (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 + ofRealVec a ⬝ᵥ (z + ofRealVec b + ofRealVec 0))
  have hp0 : ∀ a b z, p a b z ≠ 0 := fun a b z => Complex.exp_ne_zero _
  have hpd : ∀ a b, Differentiable ℂ (p a b) := fun a b => by
    simp only [p, eC, dotProduct]
    fun_prop
  have sh : ∀ a b z, theta a b z τ = p a b z * theta 0 0 (z + τ *ᵥ ofRealVec a + ofRealVec b) τ := fun a b z => by
    simpa only [zero_add] using thetaCharShift_holds (Fin g) a b 0 0 z τ hs
  let v := τ *ᵥ ofRealVec a + ofRealVec b
  obtain ⟨n, n', hn⟩ := mem_periodLattice_of_theta_translate_eq_unit_mul H₁
    periodLattice_isLattice_of_mem_siegelH g τ ⟨hs, hp⟩ (τ *ᵥ ofRealVec a' + ofRealVec b' - v)
    (fun z => U (z - v) * p a b (z - v) * (p a' b' (z - v))⁻¹)
    (((hU.comp (differentiable_id.sub_const v)).mul ((hpd a b).comp (differentiable_id.sub_const v))).mul
      (((hpd a' b').comp (differentiable_id.sub_const v)).inv fun z => hp0 _ _ _))
    (fun z => mul_ne_zero (mul_ne_zero (hU0 _) (hp0 _ _ _)) (inv_ne_zero (hp0 _ _ _))) (fun z => by
      have e := h (z - v)
      rw [sh a' b', sh a b, show z - v + τ *ᵥ ofRealVec a + ofRealVec b = z by simp only [v]; abel,
        show z - v + τ *ᵥ ofRealVec a' + ofRealVec b' = z + (τ *ᵥ ofRealVec a' + ofRealVec b' - v) by abel] at e
      have := hp0 a' b' (z - v)
      field_simp
      linear_combination e)
  have him : (τ.map Complex.im) *ᵥ (a' - a - fun i => (n i : ℝ)) = 0 := by
    ext i
    have := congrArg Complex.im (congrFun hn i)
    simp only [v, mulVec, dotProduct, ofRealVec, ofIntVec, Pi.add_apply, Pi.sub_apply, add_im, sub_im, im_sum,
      mul_im, ofReal_re, ofReal_im, intCast_re, intCast_im, mul_zero, zero_add, add_zero] at this
    simp only [mulVec, dotProduct, map_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
    linarith
  have h1 : (a' - a - fun i => (n i : ℝ)) = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.2 hp.isUnit) (him.trans (mulVec_zero _).symm)
  have half : ∀ (x y : ℝ) (k : ℤ), (x = 0 ∨ x = 1 / 2) → (y = 0 ∨ y = 1 / 2) → x - y = k → x = y ∧ k = 0 := by
    intro x y k hx hy e
    have h1 : (-1 : ℝ) < k := by rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> linarith
    have h2 : (k : ℝ) < 1 := by rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> linarith
    have h3 : k = 0 := by
      have : (-1 : ℤ) < k := by exact_mod_cast h1
      have : k < 1 := by exact_mod_cast h2
      omega
    subst h3
    exact ⟨by simpa [sub_eq_zero] using e, rfl⟩
  have h2 := fun i => half _ _ (n i) (ha' i) (ha i) (sub_eq_zero.1 (congrFun h1 i))
  obtain rfl : a' = a := funext fun i => (h2 i).1
  obtain rfl : n = 0 := funext fun i => (h2 i).2
  refine ⟨rfl, funext fun i => (half _ _ (n' i) (hb' i) (hb i) ?_).1⟩
  simp only [v, ofIntVec_zero, mulVec_zero, zero_add, add_sub_add_left_eq_sub] at hn
  have := congrFun hn i
  simp only [Pi.sub_apply, ofRealVec, ofIntVec] at this
  exact_mod_cast this

end GlobalTheory.ThetaPoint
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta
open scoped BigOperators Real

namespace GlobalTheory.ThetaPoint

open CanTh

theorem exists_linearEquiv_lift (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {L : LB P.A.left} {d g : ℕ}
    (u : HolUnif P.A L d) (a : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (hadd : ∀ z w, a (z + w) = a z * a w)
    (hon : Function.Surjective a) (hol : IsHolTo Set.univ fun z => (a z).left) (hker : {z | a z = 1}.Countable) :
    ∃ F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin d → ℂ), ∀ z, u.ex (F z) = a z := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  obtain ⟨u₀, -, hlift⟩ := AbelianExp.exists_holUnif hmul hval (holFamily_lift hval)
    (isTopologicalGroup_complexPoints hval) (PointsCompact.compactSpace_points_polAV hval hvalaff)
    (HolChart.exists_holomorphic_chart hval hvalaff exists_holomorphic_section_of_etale) P
  have cnt : ∀ {L : LB P.A.left} {d : ℕ} (u : HolUnif P.A L d), (u.Λ : Set (Fin d → ℂ)).Countable := fun u =>
    countable_of_isDiscrete_finiteDimensional (isDiscrete_iff_discreteTopology.2 u.discrete)
  have key : ∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), (∀ z w, a (z + w) = a z * a w) →
      Function.Surjective a → (IsHolTo Set.univ fun z => (a z).left) → {z | a z = 1}.Countable →
      ∃ F : (Fin n → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u₀.ex (F z) = a z := by
    intro n a hadd hon hol hker
    have h0 : a 0 = 1 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
    obtain ⟨G, hG0, hGa, hGe⟩ := hlift n a hol h0
    have hF := EndoLinear.fderiv_lifts u₀.ex u₀.ex_add u₀.Λ u₀.ker u₀.discrete a hadd G hG0
      hGa.differentiableAt hGe
    have hi : Function.Injective (fderiv ℂ G 0) :=
      realLinear_injective_of_countable_ker ((fderiv ℂ G 0).restrictScalars ℝ).toLinearMap
        (hker.mono fun x (hx : fderiv ℂ G 0 x = 0) => by
          change a x = 1
          rw [← hF, hx, CubeValues.ex_zero])
    have hs : Function.Surjective (fderiv ℂ G 0) :=
      realLinear_surjective_of_mod_countable ((fderiv ℂ G 0).restrictScalars ℝ).toLinearMap (cnt u₀) fun y => by
        obtain ⟨x, hx⟩ := hon (u₀.ex y)
        refine ⟨x, (u₀.ker _).1 ?_⟩
        have := u₀.ex_add (y - fderiv ℂ G 0 x) (fderiv ℂ G 0 x)
        rw [sub_add_cancel, hF, hx] at this
        exact mul_eq_right.1 this.symm
    exact ⟨LinearEquiv.ofBijective (fderiv ℂ G 0).toLinearMap ⟨hi, hs⟩, hF⟩
  obtain ⟨F₁, h₁⟩ := key g a hadd hon hol hker
  obtain ⟨F₀, h₀⟩ := key d u.ex u.ex_add u.ex_onto (fun U f => by simpa using u.hol U f)
    ((cnt u).mono fun z hz => (u.ker z).1 hz)
  exact ⟨F₁.trans F₀.symm, fun z => by rw [← h₀, ← h₁]; simp⟩

theorem isHolTo_fibre {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S X Z : Scheme.{0}} {p : Z ⟶ X}
    {q : Z ⟶ Sp ℂ} {s : X ⟶ S} {y : Sp ℂ ⟶ S} (H : IsPullback p q s y) (c : V → (Sp ℂ ⟶ Z))
    (hq : ∀ w, c w ≫ q = 𝟙 _) (ha : IsHolTo Set.univ fun w => c w ≫ p) : IsHolTo Set.univ c := by
  intro U f
  refine holFamily_of_affine valAt'_rules Set.univ Z c (fun w₀ _ => ?_) U f
  obtain ⟨US, hUS, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := y (default : PrimeSpectrum ℂ)) trivial
  have hyU : ⊤ ≤ y ⁻¹ᵁ US := (top_le_preimage_iff_mem y US).2 hy
  have hs : (c w₀ ≫ p) (default : PrimeSpectrum ℂ) ∈ s ⁻¹ᵁ US := by
    rw [← top_le_preimage_iff_mem, ← top_le_preimage_comp, Category.assoc, H.w, ← Category.assoc, hq,
      Category.id_comp]
    exact hyU
  obtain ⟨U₁, hU₁, hx₁, hle⟩ := exists_isAffineOpen_mem_and_subset hs
  have hle : U₁ ≤ s ⁻¹ᵁ US := hle
  set W : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ ⊤ with hW
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ W ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ := fun w => by
    rw [hW, top_le_preimage_inf, top_le_preimage_comp]
    exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ => trivial⟩⟩
  have hV : IsAffineOpen W := by
    have : IsAffine _ := isAffineOpen_top (Sp ℂ)
    have : IsAffine _ := hU₁
    have : IsAffine _ := hUS
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := US) (UT := ⊤) (UX := U₁) hyU hle hW).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := US) (UT := ⊤) (UX := U₁) hyU hle hW).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hUS (isAffineOpen_top _) hU₁)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  refine ⟨W, hV, (hiff w₀).2 ((top_le_preimage_iff_mem _ _).2 hx₁), ?_, fun g => ?_⟩
  · simpa only [hiff] using (ha U₁ 0).1
  · have hg : g ∈ Subring.closure _ := hgen.ge (Subring.mem_top g)
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · refine ((ha U₁ t).2.mono fun w (hw : w ∈ Set.univ ∩ {w | ⊤ ≤ c w ⁻¹ᵁ W}) =>
          ⟨hw.1, (hiff w).1 hw.2⟩).congr fun w hw => ?_
        exact valAt'_appLE (c w) p U₁ W _ t hw.2
      · refine (differentiableOn_const (valAt' (𝟙 (Sp ℂ)) ⊤ t)).congr fun w hw => ?_
        exact (valAt'_appLE (c w) q ⊤ W _ t hw.2).trans (by rw [hq])
    | zero => simpa only [valAt'_zero] using differentiableOn_const (0 : ℂ)
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => simpa only [valAt'_add] using hx.fun_add hy
    | neg x _ hx => simpa only [valAt'_neg] using hx.fun_neg
    | mul x y _ _ hx hy => simpa only [valAt'_mul] using hx.fun_mul hy

section Frame

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

def IsHolFrame (L : LB X) (x : V → (Sp ℂ ⟶ X)) (fr : L.ι → V → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ x z ⁻¹ᵁ L.U j}) ∧ (∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → fr j z ≠ 0) ∧
    ∀ j j' z, ⊤ ≤ x z ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j z = valAt' (x z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z

def IsSecFn (L : LB X) (x : V → (Sp ℂ ⟶ X)) (fr : L.ι → V → ℂ) (θ : V → ℂ) : Prop :=
  ∃ s : L.Sec, ∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → valAt' (x z) (L.U j) (s.f j) = θ z * fr j z

theorem exists_frame_ratio {L : LB X} (hL : L.IsLB) {x : V → (Sp ℂ ⟶ X)}
    (ho : ∀ j, IsOpen {z | ⊤ ≤ x z ⁻¹ᵁ L.U j}) {fr fr' : L.ι → V → ℂ} (h : IsHolFrame L x fr)
    (h' : IsHolFrame L x fr') : ∃ r : V → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → fr' j z = r z * fr j z := by
  have hc : ∀ z, ∃ j, ⊤ ≤ x z ⁻¹ᵁ L.U j := fun z => by
    have h : x z (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
  choose ch hch using hc
  have key : ∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → fr' (ch z) z * (fr (ch z) z)⁻¹ = fr' j z * (fr j z)⁻¹ := fun j z hj => by
    have k := (top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩
    have n := valAt'_unit_ne_zero _ k (L.g _ _)
    have n' := h.2.1 j z hj
    rw [h.2.2 _ _ _ k, h'.2.2 _ _ _ k]
    field_simp
  refine ⟨fun z => fr' (ch z) z * (fr (ch z) z)⁻¹, fun z => ?_,
    fun z => mul_ne_zero (h'.2.1 _ _ (hch z)) (inv_ne_zero (h.2.1 _ _ (hch z))), fun j z hj => ?_⟩
  · exact ((((h'.1 (ch z)).mul ((h.1 (ch z)).inv (h.2.1 _))).congr fun w hw => key _ w hw).differentiableAt
      ((ho _).mem_nhds (hch z)))
  · simp only [key j z hj]
    rw [inv_mul_cancel_right₀ (h.2.1 j z hj)]

end Frame

theorem exists_unique_half_char (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    {Hm : Matrix (Fin P.g) (Fin P.g) ℂ} {χ : u.Λ → ℂ} {Ef : LinearMap.BilinForm ℤ u.Λ} (hAH : u.IsAH Hm χ)
    (hsec : ∀ θ, u.IsThetaFn Hm χ 1 θ → ∃ s, u.IsFnPow 1 s θ)
    (hE : ∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef) {g : ℕ}
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ)) (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    (hform : ∀ z w, hermForm Hm (F z) (F w) = hermForm (imInv τ) (k z) (k w))
    (hΛ : ∀ z, F z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, k z = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) :
    ∃ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧
      (∃ fr, IsHolFrame P.L (fun z => (u.ex (F z)).left) fr ∧ (∀ j, fr j 0 = u.fr j 0) ∧
        IsSecFn P.L (fun z => (u.ex (F z)).left) fr fun z => theta a b (k z) τ) ∧
      ∀ a' b' : Fin g → ℝ, (∀ i, a' i = 0 ∨ a' i = 1 / 2) → (∀ i, b' i = 0 ∨ b' i = 1 / 2) →
        ∀ fr, IsHolFrame P.L (fun z => (u.ex (F z)).left) fr →
          (IsSecFn P.L (fun z => (u.ex (F z)).left) fr fun z => theta a' b' (k z) τ) → a' = a ∧ b' = b := by
  have dl : ∀ {m n : ℕ} (T : (Fin m → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)), Differentiable ℂ fun z => T z := fun T =>
    (LinearMap.toContinuousLinearMap T.toLinearMap).differentiable
  have ch := SymmetricSemicharacter.exists_chart u valAt'_rules P.isLB
  have per : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => CubeValues.ex_add_period u z l l.2
  obtain ⟨a, b, ha, hb, hlaw⟩ := exists_half_char u.Λ Hm χ (k.symm.trans F) hs hp
    (fun z w => by simp [hform]) (fun z => by simp [hΛ])
    (semicharacter_sq_eq_one_of_symmetric P u Hm χ hAH) (fun l m z => by
      obtain ⟨i, hi⟩ := ch z
      have h1 := hAH.2.2.2 (l + m) i z hi
      have h2 := hAH.2.2.2 m i z hi
      have h3 := hAH.2.2.2 l i (z + m) (by rwa [per])
      have e : z + m + l = z + (l + m : u.Λ) := by rw [Submodule.coe_add]; abel
      rw [h3, h1, e] at h2
      refine mul_right_cancel₀ (u.fr_ne i (z + (l + m : u.Λ)) (by rwa [per])) (h2.trans ?_)
      simp only [hermForm]
      ring)
  have hth : u.IsThetaFn Hm χ 1 fun v => canTh τ a b ((k.symm.trans F).symm v) :=
    ⟨(differentiable_canTh hp a b).comp (dl _), fun l z => by rw [pow_one]; exact hlaw l z⟩
  let Q : (Fin g → ℂ) → ℂ := fun ζ => cexp (π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))
  have hQ : Differentiable ℂ Q := by
    simp only [Q, dotProduct, mulVec]
    fun_prop
  have hfr : IsHolFrame P.L (fun z => (u.ex (F z)).left) fun j z => u.fr j (F z) :=
    ⟨fun j => (u.fr_hol j).comp (dl F).differentiableOn fun _ hz => hz, fun j z hz => u.fr_ne j _ hz,
      fun j j' z hz => u.fr_compat j j' _ hz⟩
  refine ⟨a, b, ha, hb, ⟨fun j z => Q (k z) * u.fr j (F z),
    ⟨fun j => (hQ.comp (dl k)).differentiableOn.mul (hfr.1 j),
      fun j z hz => mul_ne_zero (Complex.exp_ne_zero _) (hfr.2.1 j z hz),
      fun j j' z hz => (congrArg (Q (k z) * ·) (hfr.2.2 j j' z hz)).trans (mul_left_comm _ _ _)⟩,
    fun j => by simp [Q], ?_⟩, fun a' b' ha' hb' fr h ⟨s, hs'⟩ => ?_⟩
  · obtain ⟨s, hs⟩ := hsec _ hth
    refine ⟨secOfPowOne s, fun j z hz => ?_⟩
    refine (valAt'_res _ (powChart_eq (fun _ => j)).ge (powFn s fun _ => j) hz).trans ((hs (fun _ => j) (F z)
      (top_le_preimage_mono _ (powChart_eq (fun _ => j)).ge hz)).trans ?_)
    simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, canTh, thetaChar_eq_theta, pow_one, Q]
    ring
  · obtain ⟨r, hr, hr0, hrf⟩ := exists_frame_ratio P.isLB
      (fun j => (u.hol _ 0).1.preimage (dl F).continuous) hfr h
    let θ : (Fin P.g → ℂ) → ℂ := fun v => theta a' b' (k (F.symm v)) τ * r (F.symm v)
    have hd : Differentiable ℂ fun z => theta a' b' z τ := by
      simpa only [← thetaChar_eq_theta] using differentiable_thetaChar (mem_thetaDomain hp) a' b'
    have hv : ∀ j v, ⊤ ≤ (u.ex v).left ⁻¹ᵁ P.L.U j → valAt' (u.ex v).left (P.L.U j) (s.f j) = θ v * u.fr j v := by
      intro j v hj
      obtain ⟨z, rfl⟩ := F.surjective v
      refine (hs' j z hj).trans ?_
      rw [hrf j z hj]
      simp only [θ, LinearEquiv.symm_apply_apply, _root_.mul_assoc]
    have hθ : u.IsThetaFn Hm χ 1 θ := by
      refine ⟨(hd.comp ((dl k).comp (dl F.symm))).mul (hr.comp (dl F.symm)), fun l z => ?_⟩
      obtain ⟨j, hj⟩ := ch z
      have hj' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ P.L.U j := by rwa [per]
      have e := hv j _ hj'
      rw [per, hv j z hj, hAH.2.2.2 l j z hj] at e
      refine mul_right_cancel₀ (u.fr_ne j _ hj') (e.symm.trans ?_)
      simp only [hermForm]
      ring
    have hne : (fun v => canTh τ a b ((k.symm.trans F).symm v)) ≠ 0 := fun h0 =>
      canTh_ne_zero hs hp a b (funext fun z => by simpa using congrFun h0 ((k.symm.trans F) z))
    have hdep : ¬ LinearIndependent ℂ ![fun v => canTh τ a b ((k.symm.trans F).symm v), θ] := fun hli => by
      have := card_le_pow_of_linearIndependent_theta_principal SiegelNormalForm.exists_normal_form
        (ClassicalTheta.card_le_pow_of_linearIndependent fourierCoeff_unitCube_translate_of_entire_periodic
          (entire_periodic_eq_zero_of_fourierCoeff_eq_zero fourierCoeff_unitCube_translate_of_entire_periodic))
        P.g u.Λ u.discrete u.full Hm χ Ef hAH.1 hAH.2.1 hAH.2.2.1 hE hbij 1 le_rfl 2 _
        (fun i => by fin_cases i; exacts [hth, hθ]) hli
      simp at this
    rw [LinearIndependent.pair_iff' hne] at hdep
    push Not at hdep
    obtain ⟨c, hc⟩ := hdep
    have hcz : ∀ z, theta a' b' z τ = c * Q z * (r (k.symm z))⁻¹ * theta a b z τ := fun z => by
      have e := congrFun hc (F (k.symm z))
      simp only [θ, Pi.smul_apply, smul_eq_mul, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
        LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, canTh,
        thetaChar_eq_theta] at e
      rw [mul_right_comm, eq_mul_inv_iff_mul_eq₀ (hr0 _), ← e, _root_.mul_assoc]
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact theta_ne_zero (τ := τ) ⟨hs, hp⟩ a' b' (funext fun z => by simp [hcz])
    exact half_char_unique hs hp ha hb ha' hb'
      (((differentiable_const c).mul hQ).mul ((hr.comp (dl k.symm)).inv fun z => hr0 _))
      (fun z => mul_ne_zero (mul_ne_zero hc0 (Complex.exp_ne_zero _)) (inv_ne_zero (hr0 _))) hcz

end GlobalTheory.ThetaPoint
