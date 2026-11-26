module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XFibHess
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.SecondDerivativeOfEventuallyEq
open Filter Topology

namespace PositivityTheory.Xgp.fib_hess

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

structure J (f : E → ℝ) (z : E) (v : ℝ) (L : E → ℝ) (B : E → E → ℝ) : Prop where
  cd : ContDiffAt ℝ 2 f z
  val : f z = v
  d1 : ∀ u, fderiv ℝ f z u = L u
  d2 : ∀ u w, fderiv ℝ (fderiv ℝ f) z u w = B u w

theorem hasD {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (w : E) :
    HasFDerivAt (fun y => fderiv ℝ f y w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ f) z)) z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z := hf.fderiv_right (m := 1) (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp z
    (h1.differentiableAt (by norm_num)).hasFDerivAt

theorem evD {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) :
    ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ f y :=
  (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)

theorem hasFDerivAt_of_contDiffAt_two {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) : HasFDerivAt f (fderiv ℝ f z) z :=
  (hf.differentiableAt (by norm_num)).hasFDerivAt

theorem second_derivative_of_eventually_eq {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) {w : E} {k : E → ℝ} {k' : E →L[ℝ] ℝ}
    (he : (fun y => fderiv ℝ f y w) =ᶠ[𝓝 z] k) (hk : HasFDerivAt k k' z) (u : E) :
    fderiv ℝ (fderiv ℝ f) z u w = k' u := by
  have := (hasD hf w).unique (hk.congr_of_eventuallyEq he)
  rw [← this]; rfl

theorem J.congr {f : E → ℝ} {z : E} {v v' : ℝ} {L L' : E → ℝ} {B B' : E → E → ℝ}
    (h : J f z v L B) (hv : v = v') (hL : ∀ u, L u = L' u) (hB : ∀ u w, B u w = B' u w) :
    J f z v' L' B' :=
  ⟨h.cd, h.val.trans hv, fun u => (h.d1 u).trans (hL u), fun u w => (h.d2 u w).trans (hB u w)⟩

theorem J.add {f g : E → ℝ} {z : E} {v v' : ℝ} {L L' : E → ℝ} {B B' : E → E → ℝ}
    (hf : J f z v L B) (hg : J g z v' L' B') :
    J (fun y => f y + g y) z (v + v') (fun u => L u + L' u) (fun u w => B u w + B' u w) := by
  have hc : ContDiffAt ℝ 2 (fun y => f y + g y) z := hf.cd.add hg.cd
  refine ⟨hc, by rw [hf.val, hg.val], fun u => ?_, fun u w => ?_⟩
  · have := ((hasFDerivAt_of_contDiffAt_two hf.cd).fun_add (hasFDerivAt_of_contDiffAt_two hg.cd)).fderiv
    rw [this]; simp [hf.d1, hg.d1]
  · have he : (fun y => fderiv ℝ (fun y => f y + g y) y w) =ᶠ[𝓝 z]
        fun y => fderiv ℝ f y w + fderiv ℝ g y w := by
      filter_upwards [evD hf.cd, evD hg.cd] with y h1 h2
      rw [(h1.hasFDerivAt.fun_add h2.hasFDerivAt).fderiv]; simp
    rw [second_derivative_of_eventually_eq hc he ((hasD hf.cd w).fun_add (hasD hg.cd w))]
    simp [hf.d2, hg.d2]

theorem J.mul {f g : E → ℝ} {z : E} {v v' : ℝ} {L L' : E → ℝ} {B B' : E → E → ℝ}
    (hf : J f z v L B) (hg : J g z v' L' B') :
    J (fun y => f y * g y) z (v * v') (fun u => v * L' u + v' * L u)
      (fun u w => v * B' u w + v' * B u w + L u * L' w + L w * L' u) := by
  have hc : ContDiffAt ℝ 2 (fun y => f y * g y) z := hf.cd.mul hg.cd
  refine ⟨hc, by rw [hf.val, hg.val], fun u => ?_, fun u w => ?_⟩
  · have := ((hasFDerivAt_of_contDiffAt_two hf.cd).fun_mul (hasFDerivAt_of_contDiffAt_two hg.cd)).fderiv
    rw [this]; simp [hf.d1, hg.d1, hf.val, hg.val]
  · have he : (fun y => fderiv ℝ (fun y => f y * g y) y w) =ᶠ[𝓝 z]
        fun y => f y * fderiv ℝ g y w + g y * fderiv ℝ f y w := by
      filter_upwards [evD hf.cd, evD hg.cd] with y h1 h2
      rw [(h1.hasFDerivAt.fun_mul h2.hasFDerivAt).fderiv]; simp
    rw [second_derivative_of_eventually_eq hc he (((hasFDerivAt_of_contDiffAt_two hf.cd).fun_mul (hasD hg.cd w)).fun_add
      ((hasFDerivAt_of_contDiffAt_two hg.cd).fun_mul (hasD hf.cd w)))]
    simp [hf.d1, hg.d1, hf.d2, hg.d2, hf.val, hg.val]
    ring

theorem J.const (c : ℝ) (z : E) : J (fun _ : E => c) z c (fun _ => 0) (fun _ _ => 0) := by
  refine ⟨contDiffAt_const, rfl, fun u => by simp, fun u w => by simp⟩

theorem J.clm (T : E →L[ℝ] ℝ) (z : E) : J (fun y => T y) z (T z) (fun u => T u) (fun _ _ => 0) := by
  have h : fderiv ℝ (fun y => T y) = fun _ => T := funext fun y => T.fderiv
  refine ⟨T.contDiff.contDiffAt, rfl, fun u => by rw [h], fun u w => by rw [h]; simp⟩

theorem J.log {f : E → ℝ} {z : E} {v : ℝ} {L : E → ℝ} {B : E → E → ℝ}
    (hf : J f z v L B) (hv : v ≠ 0) :
    J (fun y => Real.log (f y)) z (Real.log v) (fun u => v⁻¹ * L u)
      (fun u w => v⁻¹ * B u w - L u * L w / v ^ 2) := by
  have hz : f z ≠ 0 := by rw [hf.val]; exact hv
  have hc : ContDiffAt ℝ 2 (fun y => Real.log (f y)) z := hf.cd.log hz
  refine ⟨hc, by rw [hf.val], fun u => ?_, fun u w => ?_⟩
  · have := ((hasFDerivAt_of_contDiffAt_two hf.cd).log hz).fderiv
    rw [this]; simp [hf.d1, hf.val]
  · have he : (fun y => fderiv ℝ (fun y => Real.log (f y)) y w) =ᶠ[𝓝 z]
        fun y => (f y)⁻¹ * fderiv ℝ f y w := by
      filter_upwards [evD hf.cd, hf.cd.continuousAt.eventually_ne hz] with y h1 h2
      rw [(h1.hasFDerivAt.log h2).fderiv]; simp
    have hi : HasFDerivAt (fun y => (f y)⁻¹) ((-((f z) ^ 2)⁻¹) • fderiv ℝ f z) z :=
      (hasDerivAt_inv hz).comp_hasFDerivAt z (hasFDerivAt_of_contDiffAt_two hf.cd)
    rw [second_derivative_of_eventually_eq hc he (hi.fun_mul (hasD hf.cd w))]
    simp [hf.d1, hf.d2, hf.val]
    ring

theorem J.comp {f : F → ℝ} (T : E →L[ℝ] F) {z : E} {v : ℝ} {L : F → ℝ} {B : F → F → ℝ}
    (hf : J f (T z) v L B) :
    J (fun y => f (T y)) z v (fun u => L (T u)) (fun u w => B (T u) (T w)) := by
  have hc : ContDiffAt ℝ 2 (fun y => f (T y)) z := hf.cd.comp z T.contDiff.contDiffAt
  refine ⟨hc, hf.val, fun u => ?_, fun u w => ?_⟩
  · have : HasFDerivAt (fun y => f (T y)) _ z := (hasFDerivAt_of_contDiffAt_two hf.cd).comp z T.hasFDerivAt
    rw [this.fderiv]; simp [hf.d1]
  · have he : (fun y => fderiv ℝ (fun y => f (T y)) y w) =ᶠ[𝓝 z]
        fun y => fderiv ℝ f (T y) (T w) := by
      filter_upwards [T.continuous.continuousAt.eventually (evD hf.cd)] with y h1
      have : HasFDerivAt (fun y => f (T y)) _ y := h1.hasFDerivAt.comp y T.hasFDerivAt
      rw [this.fderiv]; simp
    have hk : HasFDerivAt (fun y => fderiv ℝ f (T y) (T w)) _ z :=
      (hasD hf.cd (T w)).comp z T.hasFDerivAt
    rw [second_derivative_of_eventually_eq hc he hk]
    simp [hf.d2]

theorem J.atom {g : E → ℂ} {z : E} (hg : ContDiffAt ℝ 2 g z) (h0 : fderiv ℝ g z = 0)
    (l : ℂ →L[ℝ] ℝ) :
    J (fun y => l (g y)) z (l (g z)) (fun _ => 0)
      (fun u w => fderiv ℝ (fderiv ℝ (fun y => l (g y))) z u w) := by
  refine ⟨l.contDiff.contDiffAt.comp z hg, rfl, fun u => ?_, fun u w => rfl⟩
  have : HasFDerivAt (fun y => l (g y)) _ z :=
    l.hasFDerivAt.comp z (hg.differentiableAt (by norm_num)).hasFDerivAt
  rw [this.fderiv, h0]; simp

theorem J.neg {f : E → ℝ} {z : E} {v : ℝ} {L : E → ℝ} {B : E → E → ℝ}
    (hf : J f z v L B) : J (fun y => -f y) z (-v) (fun u => -L u) (fun u w => -B u w) := by
  have := (J.const (-1 : ℝ) z).mul hf
  simp only [neg_mul, one_mul] at this
  exact this.congr rfl (fun u => by ring) (fun u w => by ring)

theorem main_jet {z : E} {x w A00 A01 A10 A11 B00 upperOffDiagonalCoeff lowerOffDiagonalCoeff ToralGalois : E → ℝ} {x0 w0 : ℝ}
    {Lx Lw : E → ℝ} {a00 a01 a10 a11 b00 b01 b10 b11 : E → E → ℝ}
    (hx : J x z x0 Lx (fun _ _ => 0)) (hw : J w z w0 Lw (fun _ _ => 0))
    (h00 : J A00 z 1 (fun _ => 0) a00) (h01 : J A01 z 0 (fun _ => 0) a01)
    (h10 : J A10 z 0 (fun _ => 0) a10) (h11 : J A11 z 1 (fun _ => 0) a11)
    (k00 : J B00 z 0 (fun _ => 0) b00) (k01 : J upperOffDiagonalCoeff z 0 (fun _ => 0) b01)
    (k10 : J lowerOffDiagonalCoeff z 0 (fun _ => 0) b10) (k11 : J ToralGalois z 0 (fun _ => 0) b11)
    {φ : E → ℝ}
    (hφ : ∀ y, φ y = -Real.log (A00 y + x y * (A01 y + A10 y) + w y * (lowerOffDiagonalCoeff y + -upperOffDiagonalCoeff y)
        + (x y * x y + w y * w y) * A11 y)
      + (1 / 2) * Real.log (A00 y * A11 y + -(B00 y * ToralGalois y) + -(A01 y * A10 y) + upperOffDiagonalCoeff y * lowerOffDiagonalCoeff y)) :
    ContDiffAt ℝ 2 φ z ∧ ∀ u v, fderiv ℝ (fderiv ℝ φ) z u v =
      -((1 + (x0 ^ 2 + w0 ^ 2))⁻¹ * (a00 u v + x0 * (a01 u v + a10 u v) + w0 * (b10 u v - b01 u v)
          + (x0 ^ 2 + w0 ^ 2) * a11 u v + 2 * (Lx u * Lx v + Lw u * Lw v))
        - (2 * x0 * Lx u + 2 * w0 * Lw u) * (2 * x0 * Lx v + 2 * w0 * Lw v)
          / (1 + (x0 ^ 2 + w0 ^ 2)) ^ 2) + (1 / 2) * (a00 u v + a11 u v) := by
  have hh : J (fun y => A00 y + x y * (A01 y + A10 y) + w y * (lowerOffDiagonalCoeff y + -upperOffDiagonalCoeff y)
        + (x y * x y + w y * w y) * A11 y) z (1 + (x0 ^ 2 + w0 ^ 2))
        (fun u => 2 * x0 * Lx u + 2 * w0 * Lw u)
        (fun u v => a00 u v + x0 * (a01 u v + a10 u v) + w0 * (b10 u v - b01 u v)
          + (x0 ^ 2 + w0 ^ 2) * a11 u v + 2 * (Lx u * Lx v + Lw u * Lw v)) :=
    (((h00.add (hx.mul (h01.add h10))).add (hw.mul (k10.add k01.neg))).add
      (((hx.mul hx).add (hw.mul hw)).mul h11)).congr (by ring) (fun u => by ring)
      (fun u v => by ring)
  have hD : J (fun y => A00 y * A11 y + -(B00 y * ToralGalois y) + -(A01 y * A10 y) + upperOffDiagonalCoeff y * lowerOffDiagonalCoeff y) z 1
      (fun _ => 0) (fun u v => a00 u v + a11 u v) :=
    ((((h00.mul h11).add (k00.mul k11).neg).add (h01.mul h10).neg).add (k01.mul k10)).congr
      (by ring) (fun u => by ring) (fun u v => by ring)
  have hpos : (1 + (x0 ^ 2 + w0 ^ 2)) ≠ 0 := by positivity
  have hJ := (hh.log hpos).neg.add ((J.const (1 / 2 : ℝ) z).mul (hD.log one_ne_zero))
  obtain rfl : φ = _ := funext hφ
  refine ⟨hJ.cd, fun u v => (hJ.d2 u v).trans ?_⟩
  ring

end PositivityTheory.Xgp.fib_hess
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.fib_hess

noncomputable def tl (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℝ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) (Fin.succ i)

theorem tl_apply (d : ℕ) (z : Fin (d + 1) → ℂ) : tl d z = Fin.tail z := rfl

theorem tl_cons (d : ℕ) (a : ℂ) (y : Fin d → ℂ) : tl d (Fin.cons a y) = y := by
  ext i; simp [tl]

theorem tl_zero (d : ℕ) : tl d (Pi.single 0 1) = 0 := by
  ext i; simp [tl]

theorem tl_zero' (d : ℕ) : tl d (Complex.I • Pi.single 0 1) = 0 := by
  ext i; simp [tl]

theorem tl_succ (d : ℕ) (j : Fin d) : tl d (Pi.single j.succ 1) = Pi.single j 1 := by
  rw [tl_apply]
  ext i
  simp [Fin.tail, Pi.single_apply]

theorem tl_succ' (d : ℕ) (j : Fin d) :
    tl d (Complex.I • Pi.single j.succ 1) = Complex.I • Pi.single j 1 := by
  rw [tl_apply]
  ext i
  simp [Fin.tail, Pi.single_apply]

theorem xi_eq (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) :
    xiPot G a = -Real.log ((G 0 0).re + a.re * ((G 0 1).re + (G 1 0).re)
        + a.im * ((G 1 0).im + -(G 0 1).im) + (a.re * a.re + a.im * a.im) * (G 1 1).re)
      + (1 / 2) * Real.log ((G 0 0).re * (G 1 1).re + -((G 0 0).im * (G 1 1).im)
        + -((G 0 1).re * (G 1 0).re) + (G 0 1).im * (G 1 0).im) := by
  have h1 : (herm2 G ![1, a] ![1, a]).re = (G 0 0).re + a.re * ((G 0 1).re + (G 1 0).re)
        + a.im * ((G 1 0).im + -(G 0 1).im) + (a.re * a.re + a.im * a.im) * (G 1 1).re := by
    simp [herm2, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  have h2 : G.det.re = (G 0 0).re * (G 1 1).re + -((G 0 0).im * (G 1 1).im)
        + -((G 0 1).re * (G 1 0).re) + (G 0 1).im * (G 1 0).im := by
    simp [Matrix.det_fin_two]
    ring
  rw [xiPot, h1, h2]

theorem jet (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) (h1 : G y = 1)
    (h0 : ∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) (a : ℂ)
    (A B : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ)
    (hA : ∀ p q, A p q = fderiv ℝ (fderiv ℝ (fun y' => (G y' p q).re)) y)
    (hB : ∀ p q, B p q = fderiv ℝ (fderiv ℝ (fun y' => (G y' p q).im)) y) :
    ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) ∧
    ∀ u v, fderiv ℝ (fderiv ℝ (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)))
        (Fin.cons a y) u v =
      -((1 + (a.re ^ 2 + a.im ^ 2))⁻¹ * (A 0 0 (tl d u) (tl d v)
          + a.re * (A 0 1 (tl d u) (tl d v) + A 1 0 (tl d u) (tl d v))
          + a.im * (B 1 0 (tl d u) (tl d v) - B 0 1 (tl d u) (tl d v))
          + (a.re ^ 2 + a.im ^ 2) * A 1 1 (tl d u) (tl d v)
          + 2 * ((u 0).re * (v 0).re + (u 0).im * (v 0).im))
        - (2 * a.re * (u 0).re + 2 * a.im * (u 0).im) * (2 * a.re * (v 0).re + 2 * a.im * (v 0).im)
          / (1 + (a.re ^ 2 + a.im ^ 2)) ^ 2)
        + (1 / 2) * (A 0 0 (tl d u) (tl d v) + A 1 1 (tl d u) (tl d v)) := by
  have hT : tl d (Fin.cons a y) = y := tl_cons d a y
  have hJ : ∀ (l : ℂ →L[ℝ] ℝ) (p q : Fin 2), J (fun z : Fin (d + 1) → ℂ => l (G (tl d z) p q))
      (Fin.cons a y) (l (G y p q)) (fun _ => 0)
      (fun u w => fderiv ℝ (fderiv ℝ fun y' => l (G y' p q)) y (tl d u) (tl d w)) := by
    intro l p q
    refine J.comp (tl d) (f := fun y' => l (G y' p q)) (v := l (G y p q)) (L := fun _ => 0)
      (B := fun u w => fderiv ℝ (fderiv ℝ fun y' => l (G y' p q)) y u w) ?_
    rw [hT]
    exact J.atom (hC p q) (h0 p q) l
  have hRe : ∀ p q, J (fun z : Fin (d + 1) → ℂ => Complex.reCLM (G (tl d z) p q))
      (Fin.cons a y) (if p = q then 1 else 0) (fun _ => 0) (fun u w => A p q (tl d u) (tl d w)) := by
    intro p q
    refine (hJ Complex.reCLM p q).congr ?_ (fun _ => rfl) ?_
    · rw [h1]
      by_cases h : p = q
      · subst h
        simp
      · simp [h, Matrix.one_apply_ne h]
    · intro u w
      rw [hA]
      rfl
  have hIm : ∀ p q, J (fun z : Fin (d + 1) → ℂ => Complex.imCLM (G (tl d z) p q))
      (Fin.cons a y) 0 (fun _ => 0) (fun u w => B p q (tl d u) (tl d w)) := by
    intro p q
    refine (hJ Complex.imCLM p q).congr ?_ (fun _ => rfl) ?_
    · rw [h1]
      by_cases h : p = q
      · subst h
        simp
      · simp [Matrix.one_apply_ne h]
    · intro u w
      rw [hB]
      rfl
  have hx : J (fun z : Fin (d + 1) → ℂ => (Complex.reCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℂ) 0)) z)
      (Fin.cons a y) a.re (fun u => (u 0).re) (fun _ _ => 0) :=
    (J.clm _ _).congr (by simp) (fun u => by simp) (fun _ _ => rfl)
  have hw : J (fun z : Fin (d + 1) → ℂ => (Complex.imCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℂ) 0)) z)
      (Fin.cons a y) a.im (fun u => (u 0).im) (fun _ _ => 0) :=
    (J.clm _ _).congr (by simp) (fun u => by simp) (fun _ _ => rfl)
  have key := main_jet hx hw (by simpa using hRe 0 0) (by simpa using hRe 0 1)
    (by simpa using hRe 1 0) (by simpa using hRe 1 1) (hIm 0 0) (hIm 0 1) (hIm 1 0) (hIm 1 1)
    (φ := fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (fun z => by
      simp only [tl_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
        Complex.imCLM_apply, ContinuousLinearMap.proj_apply]
      exact xi_eq _ _)
  exact key

noncomputable def hm {d : ℕ} (H : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ) :
    Matrix (Fin d) (Fin d) ℂ := fun i j =>
  ((H (Pi.single i 1) (Pi.single j 1)
      + H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
    Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1)
      - H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ))) / 4

end PositivityTheory.Xgp.fib_hess
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecomposition
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → ∃ T : Fin 3 → Matrix (Fin d) (Fin d) ℂ, ∀ a : ℂ, ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) ∧ hessC (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) = Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (-(((1 + ‖a‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => ∑ i, (((fun (a : ℂ) (i : Fin 3) => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)) a i : ℝ) : ℂ) * T i p' q') q) p := by
  intro d G y _ hC h1 h0
  let A : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ := fun p q => fderiv ℝ (fderiv ℝ fun y' => (G y' p q).re) y
  let B : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ := fun p q => fderiv ℝ (fderiv ℝ fun y' => (G y' p q).im) y
  refine ⟨![PositivityTheory.Xgp.fib_hess.hm ((-(1/2:ℝ)) • (A 0 1 + A 1 0)), PositivityTheory.Xgp.fib_hess.hm ((-(1/2:ℝ)) • (B 1 0 - B 0 1)), PositivityTheory.Xgp.fib_hess.hm ((1/2:ℝ) • (A 1 1 - A 0 0))], fun a => ?_⟩
  obtain ⟨hc, hH⟩ := PositivityTheory.Xgp.fib_hess.jet d G y hC h1 h0 a A B (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨hc, ?_⟩
  ext p q
  refine Fin.cases ?_ (fun p' => ?_) p <;> refine Fin.cases ?_ (fun q' => ?_) q
  all_goals simp only [hessC, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, hH, PositivityTheory.Xgp.fib_hess.tl_zero, PositivityTheory.Xgp.fib_hess.tl_zero', PositivityTheory.Xgp.fib_hess.tl_succ, PositivityTheory.Xgp.fib_hess.tl_succ', map_zero, ContinuousLinearMap.zero_apply]
  all_goals simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, ne_eq, Fin.succ_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, mul_one, Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  all_goals clear hH hc h0 h1 hC
  all_goals have hr : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  all_goals have hpos : (0:ℝ) < 1 + (a.re ^ 2 + a.im ^ 2) := by positivity
  all_goals have hne : (1 + ((a.re:ℂ) ^ 2 + (a.im:ℂ) ^ 2)) ≠ 0 := by exact_mod_cast hpos.ne'
  case refine_1.refine_1 =>
    rw [hr]
    push_cast
    field_simp
    ring
  all_goals have hz : ∀ j : Fin d, (Pi.single j.succ (1:ℂ) : Fin (d+1) → ℂ) 0 = 0 := fun j => by simp [Pi.single_apply, (Fin.succ_ne_zero j).symm]
  all_goals simp only [hz, mul_zero, Complex.zero_re, Complex.zero_im, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PositivityTheory.Xgp.fib_hess.hm, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.neg_apply]
  all_goals try rw [hr]
  case refine_2.refine_2 =>
    apply Complex.ext
    · simp only [Complex.add_re, Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.normSq_ofNat]
      field_simp
      ring
    · simp only [Complex.add_re, Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.normSq_ofNat]
      field_simp
      ring
  all_goals push_cast
  all_goals field_simp
  all_goals ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xi_potential_hessian_decomposition : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → ∃ T : Fin 3 → Matrix (Fin d) (Fin d) ℂ, ∀ a : ℂ, ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) ∧ hessC (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) = Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (-(((1 + ‖a‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => ∑ i, (((fun (a : ℂ) (i : Fin 3) => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)) a i : ℝ) : ℂ) * T i p' q') q) p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition | exact GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition | (intros; apply GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition <;> assumption)
end
