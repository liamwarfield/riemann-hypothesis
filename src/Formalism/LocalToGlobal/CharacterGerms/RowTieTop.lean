module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
public import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.FittingIdeal.DetMulMemFitt0
noncomputable section

open Matrix

namespace Formalism.MainNotions.G.ValuationFitting

open ReciprocityTheory.PGsh.Up

section general

variable {R : Type} [CommRing R]

theorem det_mul_eq_sum {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) (W : Matrix (Fin h) (Fin m) R) :
    (α * W).det = ∑ f : Fin m → Fin h, (∏ i, W (f i) i) * (α.submatrix id f).det := by
  simp only [Matrix.det_apply, Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_smul_comm]
  congr 1
  ring

theorem det_mul_mem_fitt0 {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) (W : Matrix (Fin h) (Fin m) R) :
    (α * W).det ∈ Formalism.L2.FormalSeriesBounds.S4.fitt0 α := by
  rw [det_mul_eq_sum]
  refine Ideal.sum_mem _ fun f _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨f, rfl⟩)

theorem mul_submatrix_id {a b c e : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin c) R)
    (g : Fin e → Fin c) : (A * B).submatrix id g = A * B.submatrix id g := by
  ext i j
  simp [Matrix.mul_apply]

def Em (R : Type) [CommRing R] (m h : ℕ) : Matrix (Fin m) (Fin h) R :=
  Matrix.of fun j k => if (k : ℕ) = (j : ℕ) then 1 else 0

theorem Em_mulVec {m h : ℕ} (w : Fin h → R) (j : Fin m) :
    (Em R m h *ᵥ w) j = if hj : (j : ℕ) < h then w ⟨j, hj⟩ else 0 := by
  simp only [Matrix.mulVec, dotProduct, Em, Matrix.of_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg (fun e => hb (Fin.ext e)), zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro b _
    have := b.isLt
    rw [if_neg (by omega), zero_mul]

theorem Em_castLE {m h : ℕ} (hmh : m ≤ h) : (Em R m h).submatrix id (Fin.castLE hmh) = 1 := by
  ext j k
  simp only [Em, Matrix.submatrix_apply, Matrix.of_apply, id_eq, Fin.coe_castLE, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk
    simp
  · rw [if_neg (fun e => hjk (Fin.ext e.symm)), if_neg hjk]

end general

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem smith_data (hv : v.Integers R) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) :
    ∃ (P : Matrix (Fin m) (Fin m) R) (Q : Matrix (Fin h) (Fin h) R) (a' : Fin m → R),
      IsUnit P.det ∧ IsUnit Q.det ∧ P * α * Q = Matrix.diagonal a' * Em R m h ∧
      (∀ j : Fin m, h ≤ (j : ℕ) → a' j = 0) ∧ ∏ j, v (algebraMap R C (a' j)) = x := by
  have hsmith : ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) R),
      ∃ (P : Matrix (Fin d) (Fin d) R) (Q : Matrix (Fin n) (Fin n) R) (a : Fin d → R),
        IsUnit P.det ∧ IsUnit Q.det ∧
          ∀ j k, (P * A * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0 := by
    intro d
    induction d with
    | zero =>
      intro n A
      exact ⟨1, 1, Fin.elim0, by simp, by simp, fun j => j.elim0⟩
    | succ d ih =>
      intro n A
      cases n with
      | zero => exact ⟨1, 1, 0, by simp, by simp, fun _ k => k.elim0⟩
      | succ n =>
        let g : Fin (n + 1) → Fin (d + 1) → R := fun j i => A i j
        obtain ⟨i0, a, u, s, hu, hau, hs, hz, hnz⟩ := Smith.exists_pivot hv g
        by_cases ha : a = 0
        · have hA : A = 0 := by
            ext i j
            simpa [g] using congrFun (hz ha j) i
          exact ⟨1, 1, 0, by simp, by simp, fun j k => by simp [hA]⟩
        · obtain ⟨j0, hj0, hs0⟩ := hnz ha
          have hAj0 : ∀ i, A i j0 = a * u i := fun i => by
            simpa [g] using congrFun hj0 i
          have hAi0 : ∀ l, A i0 l = a * s l := fun l => hs l
          set B := (Smith.Vm i0 u)ᵀ * A * Smith.Vm j0 s with hBdef
          have hB : ∀ k l, B k l = if k = i0 then (if l = j0 then a else 0) else
              (if l = j0 then 0 else A k l - s l * (a * u k)) := by
            intro k l
            rw [hBdef, Matrix.mul_assoc, Smith.VmT_mul, Smith.mul_Vm, Smith.mul_Vm]
            by_cases hk : k = i0 <;> by_cases hl : l = j0
            · subst hk; subst hl; simp [hAj0, hu]
            · subst hk; simp [hl, hAi0, hs0] <;> ring
            · subst hl; simp [hk, hAj0, hu] <;> ring
            · simp [hk, hl, hAj0, hAi0, hu] <;> ring
          let A₀ : Matrix (Fin d) (Fin n) R := Matrix.of fun l k => B (i0.succAbove l) (j0.succAbove k)
          obtain ⟨P₀, Q₀, a₀, hP₀, hQ₀, hD₀⟩ := ih n A₀
          set M := B.submatrix (Smith.piv i0) (Smith.piv j0) with hM
          let U : Matrix (Fin (d + 1)) (Fin (d + 1)) R := (Smith.piv i0).toPEquiv.toMatrix
          let V : Matrix (Fin (n + 1)) (Fin (n + 1)) R := (Smith.piv j0).symm.toPEquiv.toMatrix
          have hM_eq : U * B * V = M := by
            dsimp only [U, V]
            rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
            rfl
          have hrow : ∀ k : Fin n, M 0 k.succ = 0 := by
            intro k
            simp only [hM, Matrix.submatrix_apply, Smith.piv_zero, Smith.piv_succ, hB,
              ite_true, Fin.succAbove_ne, ite_false]
          have hcol : ∀ l : Fin d, M l.succ 0 = 0 := by
            intro l
            simp only [hM, Matrix.submatrix_apply, Smith.piv_zero, Smith.piv_succ, hB,
              Fin.succAbove_ne, ite_false, ite_true]
          have hsub : (Matrix.of fun (l : Fin d) (k : Fin n) => M l.succ k.succ) = A₀ := by
            ext l k
            simp only [hM, Matrix.of_apply, Matrix.submatrix_apply, Smith.piv_succ]
            rfl
          obtain ⟨e00, e0s, es0, ess⟩ := Smith.blockOne_mul_mul_blockOne P₀ M Q₀ hrow hcol
          refine ⟨Smith.bd1 P₀ * U * (Smith.Vm i0 u)ᵀ, Smith.Vm j0 s * V * Smith.bd1 Q₀,
            Fin.cons a a₀, ?_, ?_, ?_⟩
          · rw [Matrix.det_mul, Matrix.det_mul, Smith.det_blockOne_alt, Matrix.det_transpose,
              Smith.det_Vm, mul_one]
            exact hP₀.mul (Smith.isUnit_det_perm (Smith.piv i0))
          · rw [Matrix.det_mul, Matrix.det_mul, Smith.det_blockOne_alt, Smith.det_Vm, one_mul]
            exact (Smith.isUnit_det_perm (Smith.piv j0).symm).mul hQ₀
          · have hfull : Smith.bd1 P₀ * U * (Smith.Vm i0 u)ᵀ * A *
                  (Smith.Vm j0 s * V * Smith.bd1 Q₀) = Smith.bd1 P₀ * M * Smith.bd1 Q₀ := by
              rw [← hM_eq, hBdef]
              simp only [Matrix.mul_assoc]
            intro j k
            rw [hfull]
            refine Fin.cases ?_ (fun l => ?_) j <;> refine Fin.cases ?_ (fun k' => ?_) k
            · rw [e00]
              simp [hM, Smith.piv_zero, hB]
            · rw [e0s]
              simp
            · rw [es0]
              simp
            · rw [ess, hsub, hD₀]
              simp [Fin.val_succ]
  obtain ⟨P, Q, a, hP, hQ, hPAQ⟩ := hsmith m h α
  set a' : Fin m → R := fun j => if (j : ℕ) < h then a j else 0 with ha'
  have hD : P * α * Q = Matrix.diagonal a' * Em R m h := by
    ext j k
    rw [hPAQ, Matrix.diagonal_mul, Em, Matrix.of_apply]
    by_cases hkj : (k : ℕ) = (j : ℕ)
    · have hj : (j : ℕ) < h := hkj ▸ k.isLt
      simp [hkj, ha', hj]
    · simp [hkj]
  refine ⟨P, Q, a', hP, hQ, hD, fun j hj => by simp [ha', not_lt.mpr hj], ?_⟩
  have hQs : LinearMap.range Q.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨Q⁻¹ *ᵥ y, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ, Matrix.one_mulVec]
  let eP : (Fin m → R) ≃ₗ[R] (Fin m → R) := Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP)
  have h1 : (LinearMap.range α.mulVecLin).map (eP : (Fin m → R) →ₗ[R] (Fin m → R)) =
      LinearMap.range (P * α * Q).mulVecLin := by
    rw [← LinearMap.range_comp, Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hQs,
      Matrix.mulVecLin_mul]
    rfl
  have h2 : LinearMap.range (Matrix.diagonal a' * Em R m h).mulVecLin =
      Submodule.pi Set.univ (fun j => (Ideal.span {a' j} : Submodule R R)) := by
    ext y
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ, true_implies,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, rfl⟩ j
      refine ⟨(Em R m h *ᵥ w) j, ?_⟩
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, mul_comm]
    · intro hy
      choose t ht using hy
      refine ⟨fun k => if hk : (k : ℕ) < m then t ⟨k, hk⟩ else 0, ?_⟩
      funext j
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Em_mulVec, ← ht j]
      by_cases hj : (j : ℕ) < h <;> simp [ha', hj, mul_comm]
  have hrange : (LinearMap.range α.mulVecLin).map (eP : (Fin m → R) →ₗ[R] (Fin m → R)) =
      Submodule.pi Set.univ (fun j => (Ideal.span {a' j} : Submodule R R)) := by
    rw [h1, hD, h2]
  let e := Submodule.Quotient.equiv _ _ eP hrange
  obtain ⟨d, c, ⟨e0⟩, hc⟩ := ReciprocityTheory.PGsh.Up.hasLen_pi v a'
  exact (ReciprocityTheory.PGsh.Up.hasLen_unique hv hx ⟨d, c, ⟨e.trans e0⟩, hc⟩).symm

theorem fitt_ge (hv : v.Integers R) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) :
    ∃ y ∈ Formalism.L2.FormalSeriesBounds.S4.fitt0 α, v (algebraMap R C y) = x := by
  obtain ⟨P, Q, a', hP, hQ, hD, hz, hx'⟩ := smith_data hv α hx
  by_cases hmh : m ≤ h
  · refine ⟨(α * Q.submatrix id (Fin.castLE hmh)).det, det_mul_mem_fitt0 _ _, ?_⟩
    have hαQ : α * Q = P⁻¹ * (Matrix.diagonal a' * Em R m h) := by
      rw [← hD, Matrix.mul_assoc P α Q, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
    rw [← mul_submatrix_id, hαQ, mul_submatrix_id, mul_submatrix_id, Em_castLE hmh, Matrix.mul_one,
      Matrix.det_mul, Matrix.det_diagonal]
    simp only [map_mul, map_prod]
    rw [hv.one_of_isUnit (Matrix.isUnit_nonsing_inv_det P hP), one_mul, hx']
  · push_neg at hmh
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    rw [map_zero, map_zero, ← hx']
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ ⟨h, hmh⟩)
    rw [hz ⟨h, hmh⟩ le_rfl, map_zero, map_zero]

theorem fitt_le (hv : v.Integers R) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) :
    ∀ g : Fin m → Fin h, v (algebraMap R C (α.submatrix id g).det) ≤ x := by
  intro g
  obtain ⟨P, Q, a', hP, hQ, hD, _, hx'⟩ := smith_data hv α hx
  have hα : P⁻¹ * (P * α * Q) * Q⁻¹ = α := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one]
  have hα' : α = P⁻¹ * (Matrix.diagonal a' * Em R m h * Q⁻¹) := by
    rw [← hD, ← Matrix.mul_assoc]
    exact hα.symm
  have e1 := hv.map_le_one (P⁻¹).det
  have e2 := hv.map_le_one ((Em R m h * Q⁻¹).submatrix id g).det
  rw [hα', mul_submatrix_id, Matrix.det_mul, Matrix.mul_assoc, mul_submatrix_id, Matrix.det_mul,
    Matrix.det_diagonal, ← hx']
  calc _ = v (algebraMap R C (P⁻¹).det) * ((∏ j, v (algebraMap R C (a' j))) *
        v (algebraMap R C ((Em R m h * Q⁻¹).submatrix id g).det)) := by
        simp only [map_mul, map_prod]
    _ ≤ 1 * ((∏ j, v (algebraMap R C (a' j))) * 1) := mul_le_mul' e1 (mul_le_mul' le_rfl e2)
    _ = _ := by rw [one_mul, mul_one]

end Formalism.MainNotions.G.ValuationFitting
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.PlugUP
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace ValuationFitting

open ReciprocityTheory.PGsh.Up CharacteristicFromRanks

variable {C : Type} [Field C]

instance factL (V : VF C) : Fact V.l.Prime := ⟨V.l_prime⟩

def ValTie (V : VF C) (vm : Valuation C NNReal) : Prop :=
  ∀ x : C, x ≠ 0 → ∃ t : ℝ, V.v x = (t : WithTop ℝ) ∧ (vm x : ℝ) = (vm (V.l : C) : ℝ) ^ t

section Val

variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

def vA (V : VF C) (R : Type) [CommRing R] [Algebra R C] : AddValuation R (WithTop ℝ) :=
  V.v.comap (algebraMap R C)

theorem vA_apply (x : R) : vA V R x = V.v (algebraMap R C x) := rfl

theorem vA_nonneg (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) : ∀ x : R, 0 ≤ vA V R x := by
  intro x
  rw [vA_apply]
  by_cases hx : algebraMap R C x = 0
  · rw [hx, V.v.map_zero]; exact le_top
  · obtain ⟨t, ht1, ht2⟩ := hT _ hx
    rw [ht1]
    have hle : (vm (algebraMap R C x) : ℝ) ≤ 1 := by exact_mod_cast hv.map_le_one x
    have : 0 ≤ t := by
      by_contra hneg
      have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (not_le.mp hneg)
      rw [← ht2] at this
      linarith
    exact_mod_cast this

theorem lenCoker_vA {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) :
    S4.lenCoker (vA V R) α = S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) := by
  unfold S4.lenCoker
  congr 1
  funext g
  rw [vA_apply, RingHom.map_det]
  rfl

end Val

theorem rpow_neg_succ {l : ℕ} (hl : 0 < l) (n : ℕ) :
    (l : ℝ) ^ (-((n : ℝ) + 1)) = ((l : ℝ) ^ (n + 1))⁻¹ := by
  have h0 : (0 : ℝ) ≤ l := by positivity
  rw [Real.rpow_neg h0, ← Nat.cast_succ, Real.rpow_natCast]

section Val2

variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem lenCoker_eq_logb (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : HasLen vm R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) (hpos : 0 < (x : ℝ)) :
    S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) =
      ((Real.logb (vm (V.l : C) : ℝ) x : ℝ) : WithTop ℝ) := by
  have hxb : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x = x :=
    Real.rpow_logb h0 (ne_of_lt h1) hpos
  rw [← lenCoker_vA]
  apply le_antisymm
  · obtain ⟨y, hy, hyV⟩ := Formalism.MainNotions.G.ValuationFitting.fitt_ge hv α hx
    have hy0 : algebraMap R C y ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hyV
      rw [← hyV] at hpos
      simp at hpos
    obtain ⟨t, ht1, ht2⟩ := hT _ hy0
    refine le_trans (S4.lenCoker_le_of_mem (vA V R) (vA_nonneg hT hv h0 h1) _ hy) ?_
    rw [vA_apply, ht1]
    have : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x ≤ (vm (V.l : C) : ℝ) ^ t := by
      rw [hxb, ← ht2, hyV]
    rw [Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at this
    exact_mod_cast this
  · unfold S4.lenCoker
    refine Finset.le_inf fun g _ => ?_
    rw [vA_apply]
    by_cases hz : algebraMap R C (α.submatrix id g).det = 0
    · rw [hz, V.v.map_zero]; exact le_top
    · obtain ⟨t, ht1, ht2⟩ := hT _ hz
      rw [ht1]
      have hle : (vm (algebraMap R C (α.submatrix id g).det) : ℝ) ≤ x := by
        exact_mod_cast Formalism.MainNotions.G.ValuationFitting.fitt_le hv α hx g
      rw [ht2, ← hxb, Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at hle
      exact_mod_cast hle

end Val2

end ValuationFitting

end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem card_sigma_fst {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a).card = m a := by
  rw [show (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a) =
      (Finset.univ : Finset (Fin (m a))).map ⟨Sigma.mk a, sigma_mk_injective⟩ from ?_]
  · simp
  · ext x
    obtain ⟨b, i⟩ := x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨i, rfl⟩
    · rintro ⟨j, hj⟩
      exact (congrArg Sigma.fst hj).symm

section CH

open ReciprocityTheory.PGsh.Up CharacteristicFromRanks ValuationFitting

variable {C : Type} [Field C]

end CH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

section Rank

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

theorem rankHyp_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.raw (pairOfLab ha hg o)).RankHyp := by
  refine { big_compl := (hr o).1, rk_big := ?_, rk_small := ?_ }
  · intro g a hb
    simp only [FBChart.raw, pairOfLab]
    convert
      (card_sigma_fst (fun b => Dw.mult (lab.tau o g b)) a).trans ((hr o).2.1 g a hb)
      using 2
    exact Finset.filter_congr (fun _ _ => Iff.rfl)
  · intro g a hb
    simp only [FBChart.raw, pairOfLab]
    convert
      (card_sigma_fst (fun b => Dw.mult (lab.tau o g b)) a).trans ((hr o).2.2 g a hb)
      using 2
    exact Finset.filter_congr (fun _ _ => Iff.rfl)

end Rank

section Named

variable (Xo c)

end Named

section Top

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

end Top

end Formalism.L2.FormalSeriesBounds
