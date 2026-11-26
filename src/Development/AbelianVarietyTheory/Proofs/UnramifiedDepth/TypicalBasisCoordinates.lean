module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CoeffLgPcurveTop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.GeomSumRoot
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TypicalBasisCoordinates
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory

theorem sumMvList_eq_ptSumL {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) {τ : Type} (l : List (Fin d → MvPowerSeries τ C)) :
    sumMvList G l = ptSumL G l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [sumMvList, ptSumL, ih]; rfl

theorem basisMap_eq_ptBasisMap {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C) : basisMap G γ = ptBasisMap G γ :=
  sumMvList_eq_ptSumL G _

theorem typicalBasis_coordinates : TypicalCurveEigenspace → TypicalCurveBasisExists := by
  intro h2 C _ _ _ v p hp hvp d h hh ty G μ
  refine ⟨?_, fun γ hγ => ?_⟩
  · have key : ∀ a : Fin d, ∃ γ : Fin d → PowerSeries C,
        IsCurve v γ ∧ G.IsOfType p ty (ty a) γ ∧ tangent γ = Pi.single a 1 := by
      intro a
      refine h2 C v p hp hvp d h hh ty G μ (ty a) (Pi.single a 1) (fun b => ?_) (fun b hb => ?_)
      · unfold IsIntV
        by_cases e : b = a
        · subst e; simp
        · simp [Pi.single_eq_of_ne e]
      · exact Pi.single_eq_of_ne (fun e => hb (by rw [e])) _
    choose γ h1 h2' h3 using key
    refine ⟨γ, h1, h2', ?_⟩
    have : (Matrix.of fun a b => tangent (γ a) b) = (1 : Matrix (Fin d) (Fin d) C) := by
      ext a b
      simp [h3, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, Matrix.det_one, v.map_one]
  · rw [basisMap_eq_ptBasisMap]
    exact ⟨ptBasisMap_inv G hγ.1 hγ.2.2, ptBasisMap_lg G hγ.1⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOrSingleOfDegreeLeOne
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FormalLog

theorem eq_zero_or_single_of_degree_le_one {σ : Type} (μ : σ →₀ ℕ) (h : μ.degree ≤ 1) :
    μ = 0 ∨ ∃ s, μ = Finsupp.single s 1 := by
  classical
  by_cases h0 : μ = 0
  · exact Or.inl h0
  · right
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 h0
    have hs' : 1 ≤ μ s := Nat.one_le_iff_ne_zero.2 hs
    have hle : Finsupp.single s 1 ≤ μ := Finsupp.single_le_iff.2 hs'
    obtain ⟨ν, rfl⟩ := exists_add_of_le hle
    rw [map_add (f := _), Finsupp.degree_single] at h
    have : ν = 0 := (Finsupp.degree_eq_zero_iff ν).1 (by omega)
    exact ⟨s, by rw [this, add_zero]⟩

theorem exists_log_exp :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d), ∃ lg ex : Pt k 1 d, (∀ i (μ : Fin 1 × Fin d →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS k 1 d)) ∧ (∀ i, ev (n := 2) ![addOf G.F (pt k d 0) (pt k d 1)] (lg i) = ev (n := 2) ![pt k d 0] (lg i) + ev (n := 2) ![pt k d 1] (lg i)) ∧ (∀ i, MvPowerSeries.constantCoeff (ex i) = 0) ∧ comp1 lg ex = pt k d 0 ∧ comp1 ex lg = pt k d 0 := by
  intro k _ _ d G
  obtain ⟨lg, h0, h1, hadd⟩ := logSt_and_logDerivSt.1 k d G
  obtain ⟨ex, -, he, ha, hb⟩ := GlobalTheory.ChartInv.exists_isInvPair k d lg h0 (by rw [h1]; simp)
  refine ⟨lg, ex, ?_, fun i => congrFun hadd i, he, ha, hb⟩
  intro i μ hμ
  rcases eq_zero_or_single_of_degree_le_one μ hμ with rfl | ⟨⟨a, j⟩, rfl⟩
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0, MvPowerSeries.coeff_zero_X]
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    have hc := congrFun (congrFun h1 i) j
    simp only [dLin] at hc
    rw [hc, MvPowerSeries.coeff_X, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · have : Finsupp.single ((0 : Fin 1), j) 1 ≠ Finsupp.single ((0 : Fin 1), i) 1 := by
        intro h
        have := Finsupp.single_left_injective (one_ne_zero (α := ℕ)) h
        exact hij (Prod.mk.inj this).2.symm
      rw [if_neg hij, if_neg this]

end GlobalTheory.FormalLog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TauBasisUnitDeterminant
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitDeterminantBasis
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Pdiv

namespace GlobalTheory.UnitDeterminantBasis

theorem det_ne_zero {k A O : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing O]
    [Algebra k O] [IsDomain O] {n : ℕ} {e : A}
    (b : Module.Basis (Fin n) k (LinearMap.range (LinearMap.mulLeft k e)))
    (T : Fin n → (A →ₐ[k] O)) (hT : Function.Injective T) (hTe : ∀ j, T j e = 1) :
    (Matrix.of fun i j => T j (b i : A)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hc0
  have hli := (linearIndependent_algHom_toLinearMap k A O).comp T hT
  rw [Fintype.linearIndependent_iff] at hli
  funext j
  refine hli c ?_ j
  have h1 : (∑ j, c j • (T j).toLinearMap) ∘ₗ
      (LinearMap.range (LinearMap.mulLeft k e)).subtype = 0 := by
    refine b.ext fun i => ?_
    have := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    simpa [LinearMap.sum_apply, mul_comm] using this
  ext a
  have h2 := LinearMap.congr_fun h1 ⟨e * a, a, rfl⟩
  simpa [LinearMap.sum_apply, hTe] using h2

end GlobalTheory.UnitDeterminantBasis
end

open scoped TensorProduct
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.tau_basis_unit_determinant

theorem exists_basis_isUnit_det : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Free ℤ OE] [Module.Finite ℤ OE] (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[p] O] (w : PlaceU p OE) (t : Fin w.n → (OE →+* O)),
    (∀ j, t j ∈ Emb (O := O) w.e) →
    (∀ j j', (∀ x, t j x - t j' x ∈ maximalIdeal O) → j = j') →
    ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j => tauExt (t j) (b i : ℤ_[p] ⊗[ℤ] OE))) := by
  intro p _ OE _ _ _ O _ _ _ w t ht hsep
  let b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) :=
    Module.finBasisOfFinrankEq _ _ rfl
  refine ⟨b, ?_⟩
  by_contra hx
  have hxM := (mem_maximalIdeal _).2 hx
  let T : Fin w.n → (TensorProduct ℤ ℤ_[p] OE →ₐ[ℤ_[p]] O ⧸ maximalIdeal O) := fun j =>
    (Ideal.Quotient.mkₐ ℤ_[p] (maximalIdeal O)).comp (tauExt (t j))
  refine GlobalTheory.UnitDeterminantBasis.det_ne_zero b T ?_ ?_ ?_
  · intro j j' h
    refine hsep _ _ fun a => ?_
    have h1 := DFunLike.congr_fun h (1 ⊗ₜ a)
    rw [← Ideal.Quotient.eq]
    simpa [T, tauExt] using h1
  · intro j
    have h1 : tauExt (t j) w.e = 1 := ht j
    simp only [T, AlgHom.comp_apply, h1, map_one]
  · have h1 := Ideal.Quotient.eq_zero_iff_mem.2 hxM
    rw [RingHom.map_det] at h1
    exact h1

end GlobalTheory.tau_basis_unit_determinant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPolyCoeff
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

noncomputable section

namespace GlobalTheory.IntegralEndLimit

theorem exists_real_le (x : WithTop ℝ) : ∃ t : ℝ, (t : WithTop ℝ) ≤ x := by
  cases x with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

theorem le_val_mul {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {x y : C} {s t u : ℝ}
    (hx : (s : WithTop ℝ) ≤ v x) (hy : (t : WithTop ℝ) ≤ v y) (h : u ≤ s + t) :
    (u : WithTop ℝ) ≤ v (x * y) := by
  rw [v.map_mul]
  refine le_trans ?_ (add_le_add hx hy)
  rw [← WithTop.coe_add]
  exact WithTop.coe_le_coe.2 h

theorem eval_close {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (x : ι → C) (Q : MvPolynomial ι C) (s : ℝ) :
    ∃ r : ℝ, ∀ x' : ι → C, (∀ i, (r : WithTop ℝ) ≤ v (x i - x' i)) →
      (s : WithTop ℝ) ≤ v (MvPolynomial.eval x Q - MvPolynomial.eval x' Q) := by
  induction Q using MvPolynomial.induction_on generalizing s with
  | C a => exact ⟨0, fun x' _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨r₁, h₁⟩ := hp s
    obtain ⟨r₂, h₂⟩ := hq s
    refine ⟨max r₁ r₂, fun x' hx' => ?_⟩
    have e : MvPolynomial.eval x (p + q) - MvPolynomial.eval x' (p + q) =
        (MvPolynomial.eval x p - MvPolynomial.eval x' p) +
          (MvPolynomial.eval x q - MvPolynomial.eval x' q) := by
      simp only [map_add (f := _)]; ring
    rw [e]
    refine le_trans (le_min (h₁ x' fun i => le_trans ?_ (hx' i))
      (h₂ x' fun i => le_trans ?_ (hx' i))) (v.map_add _ _)
    · exact WithTop.coe_le_coe.2 (le_max_left _ _)
    · exact WithTop.coe_le_coe.2 (le_max_right _ _)
  | mul_X p i hp =>
    obtain ⟨a, ha⟩ := exists_real_le (v (MvPolynomial.eval x p))
    obtain ⟨b, hb⟩ := exists_real_le (v (x i))
    obtain ⟨r, hr⟩ := hp (s - b)
    refine ⟨max r (max (s - a) b), fun x' hx' => ?_⟩
    have h1 := hr x' fun j => le_trans (WithTop.coe_le_coe.2 (le_max_left _ _)) (hx' j)
    have h2 := hx' i
    have e : MvPolynomial.eval x (p * MvPolynomial.X i) - MvPolynomial.eval x' (p * MvPolynomial.X i)
        = MvPolynomial.eval x p * (x i - x' i) +
          ((MvPolynomial.eval x p - MvPolynomial.eval x' p) * x i +
            -((MvPolynomial.eval x p - MvPolynomial.eval x' p) * (x i - x' i))) := by
      simp only [map_mul, MvPolynomial.eval_X]; ring
    have m1 : s - a ≤ max r (max (s - a) b) := le_trans (le_max_left _ _) (le_max_right _ _)
    have m2 : b ≤ max r (max (s - a) b) := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [e]
    refine le_trans (le_min (le_val_mul v ha h2 (by linarith))
      (le_trans (le_min (le_val_mul v h1 hb (by linarith)) ?_) (v.map_add _ _))) (v.map_add _ _)
    rw [v.map_neg]
    exact le_val_mul v h1 h2 (by linarith)

theorem exists_poly_coeff {C : Type} [Field C] {d : ℕ} (l : Fin d → MvPowerSeries (Fin d) C)
    (hl : ∀ a, constantCoeff (l a) = 0) (f : MvPowerSeries (Fin d) C) (α : Fin d →₀ ℕ) :
    ∃ Q : MvPolynomial (Fin d × Fin d) C, ∀ A : Matrix (Fin d) (Fin d) C,
      coeff α (subst (fun a => ∑ b, A a b • l b) f) =
        MvPolynomial.eval (fun p => A p.1 p.2) Q := by
  let ι : C →+* MvPolynomial (Fin d × Fin d) C := MvPolynomial.C
  let L : Fin d → MvPowerSeries (Fin d) (MvPolynomial (Fin d × Fin d) C) :=
    fun a => ∑ b, MvPowerSeries.C (MvPolynomial.X (a, b)) * map ι (l b)
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero fun a => by
    simp [L, hl]
  refine ⟨coeff α (subst L (map ι f)), fun A => ?_⟩
  have hm : ∀ g : MvPowerSeries (Fin d) C,
      map (MvPolynomial.eval fun p : Fin d × Fin d => A p.1 p.2) (map ι g) = g := by
    intro g; ext β; simp [ι]
  rw [← coeff_map, map_subst hL, hm]
  congr 2
  funext a
  simp [L, hm, smul_eq_C_mul]

theorem integral_of_limit :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d) (A : Matrix (Fin d) (Fin d) C),
    (∀ r : ℝ, ∃ A' : Matrix (Fin d) (Fin d) C, (∀ a b, (r : WithTop ℝ) ≤ v (A a b - A' a b)) ∧ ∃ φ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (φ a)) ∧ (∀ a, constantCoeff (φ a) = 0) ∧ ∀ a, subst φ (G.lg a) = ∑ b, A' a b • G.lg b) →
    ∃ φ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (φ a)) ∧ (∀ a, constantCoeff (φ a) = 0) ∧ ∀ a, subst φ (G.lg a) = ∑ b, A a b • G.lg b) := by
  intro C _ _ v d G A hA
  obtain ⟨ex, ⟨hex0, hr, hl⟩, -⟩ := GlobalTheory.FormalInv.formal_inverse_function_theorem.1 C d G.lg
    G.lg_const (by
      have : (Matrix.of fun i j => coeff (Finsupp.single j 1) (G.lg i) :
          Matrix (Fin d) (Fin d) C) = 1 := by
        ext i j; simp [G.lg_lin, Matrix.one_apply]
      rw [this]; exact isUnit_one)
  have hex : HasSubst ex := hasSubst_of_constantCoeff_zero hex0
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have h0 : ∀ a, constantCoeff (∑ b, A a b • G.lg b) = 0 := fun a => by
    simp [G.lg_const]
  have hs : HasSubst fun a => ∑ b, A a b • G.lg b := hasSubst_of_constantCoeff_zero h0
  refine ⟨fun a => subst (fun a => ∑ b, A a b • G.lg b) (ex a), fun a α => ?_,
    fun a => constantCoeff_subst_eq_zero hs h0 (hex0 a), fun a => ?_⟩
  · obtain ⟨Q, hQ⟩ := exists_poly_coeff G.lg G.lg_const (ex a) α
    obtain ⟨r, hr'⟩ := eval_close v (fun p : Fin d × Fin d => A p.1 p.2) Q 0
    obtain ⟨A', hA', φ, hφi, hφ0, hφ⟩ := hA r
    have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
    have e : subst (fun a => ∑ b, A' a b • G.lg b) (ex a) = φ a := by
      rw [← funext hφ, ← subst_comp_subst_apply hlg hφs, hl, subst_X hφs]
    have h1 := hr' (fun p => A' p.1 p.2) fun p => hA' p.1 p.2
    have h2 : (0 : WithTop ℝ) ≤ v (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q) := by
      rw [← hQ, e]; exact hφi a α
    show 0 ≤ v _
    rw [hQ, ← sub_add_cancel (MvPolynomial.eval (fun p : Fin d × Fin d => A p.1 p.2) Q)
      (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q)]
    exact le_trans (le_min h1 h2) (v.map_add _ _)
  · rw [← subst_comp_subst_apply hex hs, hr, subst_X hs]

end GlobalTheory.IntegralEndLimit
end
end
