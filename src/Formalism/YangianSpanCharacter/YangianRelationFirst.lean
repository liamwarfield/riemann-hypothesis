module

public import Formalism.YangianSpanCharacter.YangianRTTProofs.RttRelation
public import Formalism.YangianSpanCharacter.StatementF
public import Formalism.FormalDegreeBessel.StatementBF

@[expose] public section

section -- merged from Formalism.YangianSpanCharacter.YangianRTTProofs.DiagonalEntryEqOfModularRelation
namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y

section Alg

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem comm_of_inv {a b bi : A} (h1 : b * bi = 1) (h2 : bi * b = 1) (hab : a * b = b * a) :
    a * bi = bi * a := by
  calc a * bi = (bi * b) * (a * bi) := by rw [h2, one_mul]
    _ = bi * (a * b) * bi := by rw [hab]; simp only [mul_assoc]
    _ = bi * a := by simp only [mul_assoc]; rw [h1, mul_one]

theorem smul_cancel {c : 𝕜} (hc : c ≠ 0) {x y : A} (h : c • x = c • y) : x = y := by
  calc x = c⁻¹ • c • x := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • c • y := by rw [h]
    _ = y := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem left_cancel {b bi x y : A} (h2 : bi * b = 1) (h : b * x = b * y) : x = y := by
  calc x = bi * b * x := by rw [h2, one_mul]
    _ = bi * (b * y) := by rw [mul_assoc, h]
    _ = y := by rw [← mul_assoc, h2, one_mul]

theorem from_comm {a l e : A} (h : a * l - l * a = -(a * e)) : l * a = a * (l + e) := by
  rw [mul_add]
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

theorem from_comm' {b m e : A} (h : b * m - m * b = b * e) : m * b = b * (m - e) := by
  rw [mul_sub]
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

theorem conj_commutator_of_scaled_relation {a b ai bi x y : A} {c : 𝕜} (hc : c ≠ 0)
    (hR : c • (a * y - y * a) = a * y - b * x) (hb1 : b * bi = 1) (hb2 : bi * b = 1)
    (ha1 : a * ai = 1) (hab : a * b = b * a) :
    a * (bi * y) - bi * y * a = -(a * (c⁻¹ • (ai * x - bi * y))) := by
  have hc' : a * bi = bi * a := comm_of_inv hb1 hb2 hab
  have hc'' : a * (bi * y) = bi * (a * y) := by rw [← mul_assoc, hc', mul_assoc]
  have hay : a * y - y * a = c⁻¹ • (a * y - b * x) := by
    rw [← hR, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hbx : bi * (b * x) = x := by rw [← mul_assoc, hb2, one_mul]
  have hax : a * (ai * x) = x := by rw [← mul_assoc, ha1, one_mul]
  calc a * (bi * y) - bi * y * a = bi * (a * y - y * a) := by
        rw [hc'', mul_sub, mul_assoc]
    _ = c⁻¹ • (bi * (a * y) - x) := by
        rw [hay, mul_smul_comm, mul_sub, hbx]
    _ = -(a * (c⁻¹ • (ai * x - bi * y))) := by
        rw [mul_smul_comm, mul_sub, hax, hc'', ← smul_neg, neg_sub]

theorem y1'_alg {a b ai bi X Y : A} {c : 𝕜} (hc : c ≠ 0)
    (hR1 : c • (a * Y - Y * a) = X * b - Y * a) (hR2 : (-c) • (b * X - X * b) = Y * a - X * b)
    (hb1 : b * bi = 1) (hb2 : bi * b = 1) (ha1 : a * ai = 1) (hab : a * b = b * a) :
    a * (bi * Y) - bi * Y * a = a * (c⁻¹ • (ai * X - bi * Y)) := by
  have hc' : a * bi = bi * a := comm_of_inv hb1 hb2 hab
  have hc'' : a * (bi * Y) = bi * (a * Y) := by rw [← mul_assoc, hc', mul_assoc]
  have hD : a * Y - Y * a = b * X - X * b := by
    apply smul_cancel hc
    rw [hR1, ← neg_sub (Y * a) (X * b), ← hR2, neg_smul, neg_neg]
  have hXb : X * b = b * X - (a * Y - Y * a) := by rw [hD]; abel
  have hbX : bi * (b * X) = X := by rw [← mul_assoc, hb2, one_mul]
  have haX : a * (ai * X) = X := by rw [← mul_assoc, ha1, one_mul]
  have hL : a * (bi * Y) - bi * Y * a = bi * (a * Y - Y * a) := by
    rw [hc'', mul_sub, mul_assoc]
  apply smul_cancel hc
  rw [hL, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc, one_smul, ← mul_smul_comm, hR1]
  rw [hXb]
  simp only [mul_sub]
  rw [hbX, haX, hc'']
  abel

theorem qdet_alg {x00 x01 x10 τ τi τ' τ'i z : A} {k : 𝕜}
    (e1 : -(x01 * z) + x00 * τ' = k • 1) (e2 : -(τ * z) + x10 * τ' = 0)
    (h2 : τi * τ = 1) (h3 : τ' * τ'i = 1) : x00 - x01 * τi * x10 = k • τ'i := by
  have hτz : τ * z = x10 * τ' := neg_add_eq_zero.mp e2
  have hz : z = τi * (x10 * τ') := by rw [← hτz, ← mul_assoc, h2, one_mul]
  have h4 : (x00 - x01 * τi * x10) * τ' = k • (1 : A) := by
    rw [← e1, hz, sub_mul]
    simp only [mul_assoc]
    abel
  calc x00 - x01 * τi * x10 = (x00 - x01 * τi * x10) * τ' * τ'i := by
        rw [mul_assoc _ τ' τ'i, h3, mul_one]
    _ = k • τ'i := by rw [h4, smul_mul_assoc, one_mul]

theorem key_alg {a b ai bi mu lu mv lv hu hv η μ : A} {c : 𝕜}
    (ha2 : ai * a = 1) (hb2 : bi * b = 1) (hab : a * b = b * a)
    (h1 : lv * a = a * (lv + η)) (h2 : mu * b = b * (mu - μ)) (hη : c • η = lu - lv)
    (hμ : c • μ = mu - mv)
    (hR : c • (a * mu * (b * lv) - b * lv * (a * mu)) =
      a * (b * (mv * lv + hv)) - b * (a * (mu * lu + hu))) :
    (c - 1) • (mu * lv - lv * mu) = hv - hu - (mu * lu - lu * mu) := by
  have hA : a * mu * (b * lv) = a * (b * ((mu - μ) * lv)) := by
    calc a * mu * (b * lv) = a * (mu * b) * lv := by simp only [mul_assoc]
      _ = a * (b * ((mu - μ) * lv)) := by rw [h2]; simp only [mul_assoc]
  have hB : b * lv * (a * mu) = a * (b * ((lv + η) * mu)) := by
    calc b * lv * (a * mu) = b * (lv * a) * mu := by simp only [mul_assoc]
      _ = b * (a * ((lv + η) * mu)) := by rw [h1]; simp only [mul_assoc]
      _ = a * (b * ((lv + η) * mu)) := by rw [← mul_assoc b a, ← hab, mul_assoc a b]
  have hC : b * (a * (mu * lu + hu)) = a * (b * (mu * lu + hu)) := by
    rw [← mul_assoc b a, ← hab, mul_assoc a b]
  have e : a * (b * (c • ((mu - μ) * lv - (lv + η) * mu))) =
      a * (b * (mv * lv + hv - (mu * lu + hu))) := by
    calc a * (b * (c • ((mu - μ) * lv - (lv + η) * mu)))
        = c • (a * mu * (b * lv) - b * lv * (a * mu)) := by
          rw [hA, hB, ← mul_sub, ← mul_sub, mul_smul_comm, mul_smul_comm]
      _ = a * (b * (mv * lv + hv - (mu * lu + hu))) := by
          rw [hR, hC, ← mul_sub, ← mul_sub]
  have e2 := left_cancel hb2 (left_cancel ha2 e)
  have hμ' : c • (μ * lv) = (mu - mv) * lv := by rw [← smul_mul_assoc, hμ]
  have hη' : c • (η * mu) = (lu - lv) * mu := by rw [← smul_mul_assoc, hη]
  rw [sub_mul, add_mul, smul_sub, smul_sub, smul_add, hμ', hη'] at e2
  have key : c • (mu * lv) - c • (lv * mu) =
      mv * lv + hv - (mu * lu + hu) + (mu - mv) * lv + (lu - lv) * mu := by
    rw [← e2]
    abel
  rw [sub_smul, one_smul, smul_sub, key, sub_mul, sub_mul]
  abel

end Alg

section Mod

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}

theorem commutator_of_modular_relation (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    t u 1 1 * lf t τinv v - lf t τinv v * t u 1 1 = -(t u 1 1 * eta t τinv u v) := by
  simp only [lf, eta]
  exact conj_commutator_of_scaled_relation (sub_ne_zero.mpr huv) (H.1 u v 1 1 1 0) (H.2.2.2.1 v hv).1 (H.2.2.2.1 v hv).2
    (H.2.2.2.1 u hu).1 (H.2.2.2.2.1 u v).eq

theorem y1'_mod (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    t u 1 1 * mf t τinv v - mf t τinv v * t u 1 1 = t u 1 1 * mu t τinv u v := by
  simp only [mf, mu]
  exact y1'_alg (sub_ne_zero.mpr huv) (H.1 u v 1 1 0 1)
    (by rw [neg_sub]; exact H.1 v u 1 1 0 1)
    (H.2.2.2.1 v hv).1 (H.2.2.2.1 v hv).2 (H.2.2.2.1 u hu).1 (H.2.2.2.2.1 u v).eq

theorem mu_symm (u v : 𝕜) : mu t τinv v u = mu t τinv u v := by
  simp only [mu]
  rw [← neg_sub u v, inv_neg, neg_smul, ← smul_neg, neg_sub]

theorem qdet_mod (H : ModHyp t τinv q S) {Y : 𝕜} (hY : Y ∈ S) (hY1 : Y + 1 ∈ S) :
    t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0 = q Y • τinv (Y + 1) := by
  have hm := H.2.2.1 Y
  have e1 : -(t Y 0 1 * t (Y + 1) 1 0) + t Y 0 0 * t (Y + 1) 1 1 = q Y • (1 : A) := by
    have h01 := congrFun (congrFun hm 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h01
  have e2 : -(t Y 1 1 * t (Y + 1) 1 0) + t Y 1 0 * t (Y + 1) 1 1 = 0 := by
    have h11 := congrFun (congrFun hm 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h11
  exact qdet_alg e1 e2 (H.2.2.2.1 Y hY).2 (H.2.2.2.1 (Y + 1) hY1).1

theorem diagonal_entry_eq_of_modular_relation (H : ModHyp t τinv q S) {u : 𝕜} (hu : u ∈ S) (hu1 : u + 1 ∈ S) :
    t u 0 0 = t u 1 1 * (mf t τinv u * lf t τinv u + hf τinv q u) := by
  have hq := qdet_mod H hu hu1
  have hinv := (H.2.2.2.1 u hu).1
  have hx : t u 1 1 * (τinv u * t u 0 1 * (τinv u * t u 1 0)) = t u 0 1 * τinv u * t u 1 0 := by
    calc t u 1 1 * (τinv u * t u 0 1 * (τinv u * t u 1 0))
        = t u 1 1 * τinv u * t u 0 1 * (τinv u * t u 1 0) := by simp only [mul_assoc]
      _ = t u 0 1 * τinv u * t u 1 0 := by rw [hinv, one_mul, mul_assoc]
  simp only [mf, lf, hf]
  rw [mul_add, mul_smul_comm, ← mul_assoc (t u 1 1) (τinv u) (τinv (u + 1)), hinv, one_mul, hx,
    ← hq]
  abel

theorem key_mod (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hu1 : u + 1 ∈ S) (hv : v ∈ S)
    (hv1 : v + 1 ∈ S) (huv : u ≠ v) :
    (u - v - 1) • (mf t τinv u * lf t τinv v - lf t τinv v * mf t τinv u) =
      hf τinv q v - hf τinv q u - (mf t τinv u * lf t τinv u - lf t τinv u * mf t τinv u) := by
  have huv' : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hau : t u 1 1 * mf t τinv u = t u 0 1 := by
    simp only [mf]; rw [← mul_assoc, (H.2.2.2.1 u hu).1, one_mul]
  have hbv : t v 1 1 * lf t τinv v = t v 1 0 := by
    simp only [lf]; rw [← mul_assoc, (H.2.2.2.1 v hv).1, one_mul]
  have hR : (u - v) • (t u 1 1 * mf t τinv u * (t v 1 1 * lf t τinv v) -
      t v 1 1 * lf t τinv v * (t u 1 1 * mf t τinv u)) =
      t u 1 1 * (t v 1 1 * (mf t τinv v * lf t τinv v + hf τinv q v)) -
        t v 1 1 * (t u 1 1 * (mf t τinv u * lf t τinv u + hf τinv q u)) := by
    rw [hau, hbv, ← diagonal_entry_eq_of_modular_relation H hv hv1, ← diagonal_entry_eq_of_modular_relation H hu hu1]
    exact H.1 u v 0 1 1 0
  have h1 := from_comm (commutator_of_modular_relation H hu hv huv)
  have h2 : mf t τinv u * t v 1 1 = t v 1 1 * (mf t τinv u - mu t τinv u v) := by
    have h := y1'_mod H hv hu (Ne.symm huv)
    rw [mu_symm] at h
    exact from_comm' h
  have hη : (u - v) • eta t τinv u v = lf t τinv u - lf t τinv v := by
    simp only [eta]; rw [smul_smul, mul_inv_cancel₀ huv', one_smul]
  have hμ : (u - v) • mu t τinv u v = mf t τinv u - mf t τinv v := by
    simp only [mu]; rw [smul_smul, mul_inv_cancel₀ huv', one_smul]
  exact key_alg (H.2.2.2.1 u hu).2 (H.2.2.2.1 v hv).2 (H.2.2.2.2.1 u v).eq h1 h2 hη hμ hR

end Mod

theorem wedgeMapInLieAlgebra : Formalism.YangianSpanCharacter.Y.Y1 := by
  intro 𝕜 A _ _ _ t τinv q S H u v hu hv huv
  exact commutator_of_modular_relation H hu hv huv

theorem yangian_relation_three_holds : Formalism.YangianSpanCharacter.Y.Y3 := by
  intro 𝕜 A _ _ _ t τinv q S H u v hu hu1 hum hv hv1 huv
  rw [key_mod H hu hu1 hv hv1 huv]
  have hinvu := H.2.2.2.1 u hu
  have hinvm := H.2.2.2.1 (u - 1) hum
  have hml : mf t τinv u * lf t τinv u = τinv u * t u 0 0 - hf τinv q u := by
    rw [diagonal_entry_eq_of_modular_relation H hu hu1, ← mul_assoc, hinvu.2, one_mul]
    abel
  have qd : t u 0 0 - t u 1 0 * τinv u * t u 0 1 = q (u - 1) • τinv (u - 1) := by
    have hm := H.2.1 (u - 1)
    rw [sub_add_cancel] at hm
    have e1 : -(t u 1 0 * t (u - 1) 0 1) + t u 0 0 * t (u - 1) 1 1 = q (u - 1) • (1 : A) := by
      have h01 := congrFun (congrFun hm 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h01
    have e2 : -(t u 1 1 * t (u - 1) 0 1) + t u 0 1 * t (u - 1) 1 1 = 0 := by
      have h11 := congrFun (congrFun hm 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h11
    exact qdet_alg e1 e2 hinvu.2 hinvm.1
  have hc1 : t u 1 1 * τinv (u - 1) = τinv (u - 1) * t u 1 1 :=
    comm_of_inv hinvm.1 hinvm.2 (H.2.2.2.2.1 u (u - 1)).eq
  have hc2 : τinv (u - 1) * τinv u = τinv u * τinv (u - 1) :=
    comm_of_inv hinvu.1 hinvu.2 hc1.symm
  have hfm : hf τinv q (u - 1) = q (u - 1) • (τinv u * τinv (u - 1)) := by
    simp only [hf]; rw [sub_add_cancel, hc2]
  have hlm : lf t τinv u * mf t τinv u = τinv u * t u 0 0 - hf τinv q (u - 1) := by
    rw [hfm, ← mul_smul_comm, ← qd]
    simp only [lf, mf, mul_sub, mul_assoc]
    abel
  rw [hml, hlm]
  abel

end Formalism.YangianSpanCharacter.P
end

section -- merged from Formalism.YangianSpanCharacter.YangianRTTProofs.MinusFrameIdentity
namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.YangianSpanCharacter.F

set_option linter.unusedSimpArgs false

theorem minus_frame_identity : Formalism.YangianSpanCharacter.F.MinusFrame := by
  intro 𝕜 A _ _ _ t τinv q S H Y Yb hY hY1 hYb hYb1 hYbm hd hd1 d tn τn Ln Gb
  have hd1' : d - 1 ≠ 0 := hd1
  have hne : Y ≠ Yb := fun h => hd (by rw [h, sub_self])
  have i0 := H.2.2.2.1 Y hY
  have hτl : t Y 1 1 * lf t τinv Y = t Y 1 0 := by
    unfold lf; rw [← mul_assoc, i0.1, one_mul]
  have hτm : t Y 1 1 * mf t τinv Y = t Y 0 1 := by
    unfold mf; rw [← mul_assoc, i0.1, one_mul]
  have QD : t Y 0 0 - t Y 0 1 * lf t τinv Y = q Y • τinv (Y + 1) := by
    have := qdet_mod H hY hY1; unfold lf; rw [← mul_assoc]; exact this
  have hτh : t Y 1 1 * hf τinv q Y = q Y • τinv (Y + 1) := by
    unfold hf; rw [mul_smul_comm, ← mul_assoc, i0.1, one_mul]
  have Y1' : t Y 1 1 * mf t τinv Yb - mf t τinv Yb * t Y 1 1 = t Y 1 1 * mu t τinv Y Yb :=
    y1'_mod H hY hYb hne
  have hμ0 : (Y - Yb) • mu t τinv Y Yb = mf t τinv Y - mf t τinv Yb := by
    unfold mu; exact smul_inv_smul₀ (sub_ne_zero.mpr hne) _
  have hτμ : d • (t Y 1 1 * mu t τinv Y Yb) = t Y 1 1 * mf t τinv Yb - t Y 0 1 := by
    show (Yb - Y) • (t Y 1 1 * mu t τinv Y Yb) = _
    rw [show Yb - Y = -(Y - Yb) by ring, neg_smul, ← mul_smul_comm, hμ0, mul_sub, hτm, neg_sub]
  have Y3 : (d - 1) • (mf t τinv Yb * lf t τinv Y - lf t τinv Y * mf t τinv Yb) =
      hf τinv q Y - hf τinv q (Yb - 1) :=
    yangian_relation_three_holds 𝕜 A t τinv q S H Yb Y hYb hYb1 hYbm hY hY1 (Ne.symm hne)
  have Y3' : mf t τinv Yb * lf t τinv Y - lf t τinv Y * mf t τinv Yb =
      (d - 1)⁻¹ • (hf τinv q Y - hf τinv q (Yb - 1)) := by
    rw [← Y3, inv_smul_smul₀ hd1']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, τn, blk, pt1, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, blk, pt1, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [τn, Ln, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg, hτl]
    rw [inv_smul_smul₀ hd1', hτh]
    linear_combination (norm := module) QD
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [τn, Gb, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    linear_combination (norm := module) (-d) • Y1' - hτμ
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [Ln, Gb, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    linear_combination (norm := module) Y3'

end Formalism.YangianSpanCharacter.P
end

section -- merged from Formalism.YangianSpanCharacter.YangianRTTProofs.TransposeSymplecticShift
namespace Formalism.YangianSpanCharacter.P

open Matrix

theorem transposeSymplecticShift : Formalism.YangianSpanCharacter.T.TJT := by
  intro R A _ _ _ p c ci Y h
  obtain ⟨h1, h2, h3⟩ := h
  have hpci : p * ci = ci * p - ci := by
    have : ci * (p * c) * ci = ci * (c * p + c) * ci := by rw [h3]
    have e1 : ci * (p * c) * ci = ci * p := by
      rw [mul_assoc, mul_assoc, h1, mul_one]
    have e2 : ci * (c * p + c) * ci = p * ci + ci := by
      rw [mul_add, add_mul, ← mul_assoc ci c p, h2, one_mul, one_mul]
    rw [e1, e2] at this
    rw [this]; abel
  have hc : ∀ x : A, algebraMap R A Y * x = x * algebraMap R A Y := fun x => Algebra.commutes Y x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.J, map_add (f := _), add_mul, mul_add]
  all_goals first
    | exact h1
    | exact h2
    | (rw [hpci, hc ci]; abel)

theorem planeWaveIntertwining : Formalism.YangianSpanCharacter.T.PlaneWave := by
  intro R A _ _ _ p c ci f s Y hfc hfci hpf
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]
  · have key : c * f * algebraMap R A s = algebraMap R A s * f * c := by
      rw [← hfc, mul_assoc, ← Algebra.commutes, ← mul_assoc]
      exact congrArg (· * c) (Algebra.commutes s f).symm
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two, hfc, hfci] <;>
      simp only [mul_add, add_mul, mul_neg, neg_mul, hpf, key, Algebra.commutes] <;>
      first | noncomm_ring | abel

end Formalism.YangianSpanCharacter.P
end

namespace Formalism.YangianSpanCharacter.Final

theorem T_PlaneWave : Formalism.YangianSpanCharacter.T.PlaneWave := Formalism.YangianSpanCharacter.P.planeWaveIntertwining

end Formalism.YangianSpanCharacter.Final
