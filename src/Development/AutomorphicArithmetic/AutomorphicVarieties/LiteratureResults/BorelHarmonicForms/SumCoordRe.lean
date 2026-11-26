module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem sum_coord_re {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : Cinf E) :
    ∑ τ : E →+* ℂ, coord τ z = ((2 * ∑ w : InfinitePlace E, (z w).re : ℝ) : ℂ) := by
  have h := congrArg Multiplicative.toAdd
    (GlobalTheory.GKCoh.Tests.prod_coord (M := Multiplicative ℂ) Multiplicative.ofAdd z)
  simp only [toAdd_prod, toAdd_mul, toAdd_ofAdd, Complex.add_conj] at h
  rw [h, Finset.mul_sum, Complex.ofReal_sum]

theorem UpperTheory.V.Lit.Bor.twEx :
    UpperTheory.V.Lit.Bor.TwEx := by
  intro E _ _ _ a _ r
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (r / (2 * ((a : ℝ) * Fintype.card (InfinitePlace E))))
  refine ⟨_, ⟨_, hν⟩, fun X φ => ?_⟩
  rw [lie_mulChi, GlobalTheory.CuspRep.AlgExpo.dchi_eq_sum]
  simp only [(GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 _ hν, ← Finset.mul_sum]
  rw [sum_coord_re, ← Complex.ofReal_mul]
  have e : ell E a X = (∑ w : InfinitePlace E, ((Matrix.of X).trace w).re) /
      ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
    simp [ell, Matrix.trace]
  rw [e]
  congr 4
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SkewLieActionL2
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2Variant
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.derivative_right_translate_L2 :
    UpperTheory.V.Lit.Bor.DerivativeRightTranslateL2 := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c hψc hc hc0 hcadd hder
  have hf : Continuous fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2 :=
    (GlobalTheory.AutomorphicL2Unitary.continuous_R hψ.toL2).comp hc
  have hI := hf.integral_hasStrictDerivAt 0 0
  have hE : (fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hφ.toL2) =
      fun t => (∫ s in (0 : ℝ)..t, (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2) + hφ.toL2 := by
    funext t
    rw [← GlobalTheory.CompanionTheory.TransDeriv.R_sub_eq_integral hφ hψ hψc hc hc0 hcadd hder t]
    abel
  rw [hE]
  have h := hI.hasDerivAt.add_const hφ.toL2
  simpa [hc0] using h
end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem continuous_lie_of_level {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) : Continuous (lie E a X φ).1 := by
  refine ContAut.continuous_of_isOpen_stab E a _ ?_
  let S : Sm E a → Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) := fun θ =>
    { carrier := {k | finRep E a k θ = θ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : S φ ≤ S (lie E a X φ) := fun k hk => by
    have e : lie E a X (finRep E a k φ) = finRep E a k (lie E a X φ) :=
      LinearMap.congr_fun (lie_rt_fin X k) φ
    have hk' : finRep E a k φ = φ := hk
    change finRep E a k (lie E a X φ) = lie E a X φ
    rw [← e, hk']
  exact Subgroup.isOpen_mono hle h

open scoped GlobalTheory.CuspRep.CuspidalL2GL in
theorem UpperTheory.V.Lit.Bor.skew_lie_action_L2 :
    UpperTheory.V.Lit.Bor.SkewLieActionL2 := by
  intro E _ _ _ a μ _ X φ ψ hφ hψ h1 h2 h3 h4
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨c, c0, cadd, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have g0 : infGL E a (c 0) = 1 := by rw [c0, map_one]
  have key : ∀ (θ : Sm E a), IsOpen {k | act (.fin k) θ = θ} →
      ∀ (p : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ θ.1)
        (q : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X θ).1),
      HasDerivAt (fun s => GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) p.toL2) q.toL2 0 :=
    fun θ hθ p q => UpperTheory.V.Lit.Bor.derivative_right_translate_L2 (GA E a) _ μ θ.1 _ p q (fun s => infGL E a (c s))
      (continuous_lie_of_level X θ hθ) ccont g0 (fun s t => by rw [cadd, map_mul])
      (fun g => hasDerivAt_curve θ g c X c0 cder)
  have d := (key φ hφ h1 h3).inner ℂ (key ψ hψ h2 h4)
  have hc : (fun s : ℝ => inner ℂ (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) h1.toL2)
      (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) h2.toL2)) = fun _ => inner ℂ h1.toL2 h2.toL2 :=
    funext fun s => (LinearIsometry.mk (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s))).toLinearMap
      (GlobalTheory.AutomorphicL2Unitary.norm_R _)).inner_map_map _ _
  rw [hc] at d
  have h := d.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [g0, map_one, ContinuousLinearMap.one_apply] at h
  exact (add_comm _ _).trans h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasComm
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem comm_sq {A : Type} [Ring A] (x y z : A) (h : x * y - y * x = z) :
    x * (y * y) - y * y * x = z * y + y * z := by
  rw [← h]; noncomm_ring

theorem UpperTheory.V.Lit.Bor.casComm :
    UpperTheory.V.Lit.Bor.CasComm := by
  intro E _ _ _ a n e he A _ _ _ _ L hL X
  obtain ⟨h1, h2⟩ := frameBr E a n e he A
  let l : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] A :=
    { toFun := fun Y => L (toL Y)
      map_add' := fun Y Z => L.map_add (toL Y) (toL Z)
      map_smul' := fun c Y => L.map_smul c (toL Y) }
  have hl : ∀ Y Z, l Y * l Z - l Z * l Y = l (Y * Z - Z * Y) := hL
  let J : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    { toFun := fun Y => Complex.I • Y
      map_add' := fun Y Z => smul_add _ _ _
      map_smul' := fun c Y => smul_comm _ _ _ }
  let s : Herm E a →ₗ[ℝ] A := l ∘ₗ (Herm E a).subtype
  let t : Herm E a →ₗ[ℝ] A := l ∘ₗ J ∘ₗ (Herm E a).subtype
  have key : ∀ Y, l Y * cas L e - cas L e * l Y =
      ∑ j, (l (Y * (e j).1 - (e j).1 * Y) * l (e j).1 + l (e j).1 * l (Y * (e j).1 - (e j).1 * Y)) -
      ∑ j, (l (Y * (Complex.I • (e j).1) - (Complex.I • (e j).1) * Y) * l (Complex.I • (e j).1) +
        l (Complex.I • (e j).1) * l (Y * (Complex.I • (e j).1) - (Complex.I • (e j).1) * Y)) := fun Y => by
    have hc : cas L e = ∑ j, (l (e j).1 * l (e j).1 - l (Complex.I • (e j).1) * l (Complex.I • (e j).1)) := rfl
    rw [hc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← comm_sq _ _ _ (hl Y _), ← comm_sq _ _ _ (hl Y _)]
    noncomm_ring
  have hskew : ∀ Z, star Z = -Z → l Z * cas L e - cas L e * l Z = 0 := fun Z hZ => by
    have a1 : ∑ j, l (Z * (e j).1 - (e j).1 * Z) * l (e j).1 + ∑ j, l (e j).1 * l (Z * (e j).1 - (e j).1 * Z) = 0 :=
      h1 ((LinearMap.mul ℝ A).compl₁₂ s s) Z hZ
    have a2 : ∑ j, l (Complex.I • (Z * (e j).1 - (e j).1 * Z)) * l (Complex.I • (e j).1) +
        ∑ j, l (Complex.I • (e j).1) * l (Complex.I • (Z * (e j).1 - (e j).1 * Z)) = 0 :=
      h1 ((LinearMap.mul ℝ A).compl₁₂ t t) Z hZ
    rw [key]
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, Finset.sum_add_distrib]
    rw [a1, a2, sub_zero]
  have hherm : ∀ Y : Herm E a, l Y.1 * cas L e - cas L e * l Y.1 = 0 := fun Y => by
    have hs : ∀ j, star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := fun j => by
      have h : star (e j).1 = (e j).1 := (e j).2
      rw [star_smul, h, Complex.star_def, Complex.conj_I, neg_smul]
    have a1 : ∑ j, (l (Y.1 * (e j).1 - (e j).1 * Y.1) * l (e j).1 + l (e j).1 * l (Y.1 * (e j).1 - (e j).1 * Y.1)) =
        -∑ j, (l (Complex.I • (e j).1) * l ((Complex.I • (e j).1) * Y.1 - Y.1 * (Complex.I • (e j).1)) +
          l ((Complex.I • (e j).1) * Y.1 - Y.1 * (Complex.I • (e j).1)) * l (Complex.I • (e j).1)) :=
      h2 ((LinearMap.mul ℝ A).compl₁₂ l s + (LinearMap.mul ℝ A).flip.compl₁₂ l s) Y hs
    rw [key, a1, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← neg_sub (Y.1 * (Complex.I • (e j).1)), map_neg]
    noncomm_ring
  let Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of X
  have hY : Y = (hp (toL Y)).1 + (1 / 2 : ℝ) • (Y - star Y) := by
    rw [hp_val]; module
  have hZ : star ((1 / 2 : ℝ) • (Y - star Y)) = -((1 / 2 : ℝ) • (Y - star Y)) := by
    rw [star_smul, star_trivial, star_sub, star_star, ← smul_neg, neg_sub]
  have hX : L X = l (hp (toL Y)).1 + l ((1 / 2 : ℝ) • (Y - star Y)) := by
    rw [← map_add (f := _), ← hY]; rfl
  rw [hX]
  exact Commute.add_right (Commute.symm (sub_eq_zero.1 (hherm _))) (Commute.symm (sub_eq_zero.1 (hskew _ hZ)))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DelCochain
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.delCochain :
    UpperTheory.V.Lit.Bor.DelCochain := by
  intro E _ _ _ a n e he M _ _ _ _ κ L h q ω hω k X
  let β : Herm E a →ₗ[ℝ] Herm E a →ₗ[ℝ] M :=
    LinearMap.mk₂ ℝ (fun Y Z => L (toL Y.1) (ω.curryLeft Z fun i => adHerm k (X i)))
      (fun Y Y' Z => LinearMap.congr_fun (map_add L (toL Y.1) (toL Y'.1)) _)
      (fun c Y Z => LinearMap.congr_fun (map_smul L c (toL Y.1)) _)
      (fun Y Z Z' => by rw [map_add (f := _), AlternatingMap.add_apply, map_add (f := _)])
      (fun c Y Z => by
        rw [map_smul, AlternatingMap.smul_apply]
        exact ((L (toL Y.1)).restrictScalars ℝ).map_smul c _)
  have hβ : ∀ Y Z, β Y Z = L (toL Y.1) (ω (Matrix.vecCons Z fun i => adHerm k (X i))) := fun _ _ => rfl
  have key := UpperTheory.V.Lit.Bor.frameAd E a n e he M β k
  simp only [hβ] at key
  set_option synthInstance.maxHeartbeats 100000 in
    rw [del_apply, del_apply, map_sum, ← key]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (Matrix.vecCons (adHerm k (e j)) fun i => adHerm k (X i)) =
      fun i => adHerm k (Matrix.vecCons (e j) X i) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [hc, hω k]
  exact (LinearMap.congr_fun (h k (e j)) _).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SmForm
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.smForm :
    UpperTheory.V.Lit.Bor.SmForm := by
  intro E _ _ _ a Ξ r H G hH hG X x hx y hy
  set c : ℂ := ((2 * r * ell E a (toL X.1) : ℝ) : ℂ) with hc
  have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
  obtain ⟨h1, h2⟩ := UpperTheory.V.Lit.Bor.tformAdj (Sm E a) Ξ.d H (sqSub E a r) G (Ξ.dmat (toL X.1)) (Ξ.dmat (toL X.1))
    (lie E a (toL X.1)) (-lie E a (toL X.1) - c • 1)
  have hX : star X.1 = X.1 := X.2
  have e1 := h1 (by have := hG.adj X.1; rwa [hX] at this) x y
  have e2 := h2 (fun φ hφ ψ hψ => by
    have := hH.skew (toL X.1) φ hφ ψ hψ
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_neg,
      LinearMap.map_smulₛₗ, hcc, smul_eq_mul]
    rw [← hc] at this
    linear_combination this) x hx y hy
  have e3 : smLie Ξ (toL X.1) y = smA Ξ (toL X.1) y + smB Ξ (toL X.1) y := by
    simp [smB]
  have e4 : smAdj Ξ r (toL X.1) x = smB Ξ (toL X.1) x +
      (-lie E a (toL X.1) - c • (1 : Module.End ℂ (Sm E a))).rTensor _ x := by
    rw [smAdj, adj_apply, smA_apply, LinearMap.rTensor_sub, LinearMap.rTensor_neg, LinearMap.rTensor_smul,
      Module.End.one_eq_id, LinearMap.rTensor_id, ← algebraMap_smul ℂ (2 * r * ell E a (toL X.1)) x]
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [show algebraMap ℝ ℂ (2 * r * ell E a (toL X.1)) = c from rfl]
    abel
  rw [e3, e4, map_add (f := _), map_add (f := _), LinearMap.add_apply, smA_apply, smB_apply, e1, e2, add_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaSucc
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem ring_sq {R : Type} [Ring R] {x y : R} (h : Commute x y) : (y - x) * (x + y) = y * y - x * x := by
  have h' := h.eq
  rw [sub_mul, mul_add, mul_add, h']
  abel

private theorem ring_br {R : Type} [Ring R] {x y x' y' : R} (h : Commute x y') (h' : Commute x' y) :
    (x + y) * (y' - x') - (y' - x') * (x + y) = (y * y' - y' * y) - (x * x' - x' * x) := by
  simp only [sub_mul, mul_add, add_mul, mul_sub, h.eq, h'.eq]
  abel

theorem UpperTheory.V.Lit.Bor.kugaSucc :
    UpperTheory.V.Lit.Bor.KugaSucc := by
  intro E _ _ _ a n e he M _ _ _ _ A B hA hB hAB q ω hω X
  have hs : ∀ j, star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := fun j => by
    have h : star (e j).1 = (e j).1 := (e j).2
    rw [star_smul, h, Complex.star_def, Complex.conj_I, neg_smul]
  have hsq : ∀ (Z : Lie E a) (m : M), (B - A) Z ((A + B) Z m) = (B Z * B Z - A Z * A Z) m := fun Z m =>
    LinearMap.congr_fun (ring_sq (hAB Z Z)) m
  have hbr : ∀ (Y Z : Matrix (Fin a) (Fin a) (Cinf E)) (m : M),
      (A + B) (toL Y) ((B - A) (toL Z) m) - (B - A) (toL Z) ((A + B) (toL Y) m) =
        (B - A) (toL (Y * Z - Z * Y)) m := fun Y Z m => by
    have h := ring_br (hAB (toL Y) (toL Z)) (hAB (toL Z) (toL Y))
    rw [hA, hB] at h
    exact LinearMap.congr_fun h m
  have hup : ∀ (i : Fin (q + 1)) (Y : Herm E a),
      (-1 : ℤ) ^ (i : ℕ) • ω (Matrix.vecCons Y (i.removeNth X)) = ω (Function.update X i Y) := fun i Y => by
    rw [← Fin.insertNth_removeNth, AlternatingMap.map_insertNth]
  have hfr : ∀ i : Fin (q + 1),
      ∑ j, (B - A) (toL ((X i).1 * (e j).1 - (e j).1 * (X i).1)) (ω (Function.update X i (e j))) =
        -∑ j, (B - A) (toL (Complex.I • (e j).1)) (ω (Function.update X i (brH _ (hs j) (X i)))) := fun i =>
    (frameBr E a n e he M).2
      (LinearMap.mk₂ ℝ (fun Z Y => (B - A) (toL Z) (ω (Function.update X i Y)))
        (fun Z Z' Y => LinearMap.congr_fun (map_add (B - A) (toL Z) (toL Z')) _)
        (fun c Z Y => LinearMap.congr_fun (map_smul (B - A) c (toL Z)) _)
        (fun Z Y Y' => by rw [AlternatingMap.map_update_add, map_add (f := _)])
        (fun c Z Y => by rw [AlternatingMap.map_update_smul, LinearMap.map_smul_of_tower])) (X i) hs
  have h1 : dCo (A + B) (del (B - A) e ω) X =
      ∑ j, ∑ i, (A + B) (toL (X i).1) ((B - A) (toL (e j).1) (ω (Function.update X i (e j)))) := by
    rw [dCo_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [del_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hup, map_zsmul, map_zsmul]
  have h2 : del (B - A) e (dCo (A + B) ω) X =
      ∑ j, ((B - A) (toL (e j).1) ((A + B) (toL (e j).1) (ω X)) -
        ∑ i, (B - A) (toL (e j).1) ((A + B) (toL (X i).1) (ω (Function.update X i (e j))))) := by
    rw [del_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dCo_cons, map_sub, dCo_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hup, map_zsmul, map_zsmul, map_zsmul]
    rfl
  have h3 : ∑ j, ∑ i, (A + B) (toL (X i).1) ((B - A) (toL (e j).1) (ω (Function.update X i (e j)))) -
      ∑ j, ∑ i, (B - A) (toL (e j).1) ((A + B) (toL (X i).1) (ω (Function.update X i (e j)))) =
      -∑ j, (B - A) (toL (Complex.I • (e j).1)) ((A + B) (toL (Complex.I • (e j).1)) (ω X)) := by
    simp only [← Finset.sum_sub_distrib, hbr]
    rw [Finset.sum_comm]
    simp only [hfr]
    rw [Finset.sum_neg_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hω _ (hs j), map_sum]
  rw [h1, h2, Finset.sum_sub_distrib, add_sub_left_comm, h3, ← sub_eq_add_neg, ← Finset.sum_sub_distrib,
    cas, cas, ← Finset.sum_sub_distrib, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsq, hsq]
  simp only [LinearMap.sub_apply]
  abel
end
