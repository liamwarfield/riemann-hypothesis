module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuperadditiveOfCellsCoverCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubsetStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HodgeInteriorGram

theorem isDerivAt0_comp_equiv {g g' : ℕ} {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (y : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g' → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => y (L z)) w v ↔ IsDerivAt0 y (L w) v := by
  unfold IsDerivAt0
  simp only [map_zero]
  refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)
  rw [show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv,
    map_zero]
  rfl

theorem int_eq_of_exp_eq (m n : ℤ) (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ K : ℕ, 0 < K → (K : ℤ) ∣ n - m := by
    intro K hK
    obtain ⟨N, hN⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h K hK)
    have hkC : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
    have e : ((n - m : ℤ) : ℂ) = ((K * N : ℤ) : ℂ) := by
      push_cast
      linear_combination (norm := skip) ((K : ℂ) / (2 * Real.pi * Complex.I)) * hN
      field_simp
      ring
    exact ⟨N, by exact_mod_cast e⟩
  have hz : n - m = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (key ((n - m).natAbs + 1) (Nat.succ_pos _)) ?_
    rw [Int.abs_eq_natAbs]
    push_cast
    omega
  omega

theorem hermForm_pull' {g g' : ℕ} (M : Matrix (Fin g') (Fin g) ℂ) (Hm : Matrix (Fin g') (Fin g') ℂ)
    (z w : Fin g → ℂ) : hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (M *ᵥ z) (M *ᵥ w) := by
  have : Mᵀᴴ *ᵥ (star w) = star (M *ᵥ w) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose]
    rfl
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

end GlobalTheory.HodgeInteriorGram

theorem GlobalTheory.HodgeInteriorGram.gram_eq_riem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit (unfFam U σ)), Function.Injective W.ik → ∀ (d : (unfFam U σ).Comp → (E →+* ℂ) → ℝ), (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) → (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = ((unfFam U σ).un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0)) → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (exx : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) exx → IsHolTo Set.univ (fun w => (exx w).left) → ∀ (k : (unfFam U σ).Comp) (x' : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x'.1 → cxPt Z ((unfFam U σ).un k x') = x → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame Z σ (x.1 ≫ genι Z)) (Wd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (exx w).left) Wd → (∀ τ, (hodgeMet Z U).gram x f τ = (((2 * Real.pi / d k τ : ℝ)) : ℂ) • Matrix.of fun b b' => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (Wd p) (Wd q) = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ U hσ hU W hinj d hdpos hd g x exx hin hex hhol k x' hx' hkx Hm hint hweil f Wd hdirs
  have hexf : ∃ g₀, IsHodgeFrame (unfFam U) x g₀ := by
    rw [← hkx]; exact ⟨_, isHodgeFrame_cxFrame (U := unfFam U) hσ hx'⟩
  have hg : ∀ τ, (hodgeMet Z U).gram x f τ =
      ((2 * Real.pi : ℝ) : ℂ) • ((hexf.choose.co f τ)ᴴ * hexf.choose.co f τ) := fun τ => dif_pos hexf
  obtain ⟨k'', x'', hx'', hkx'', hv⟩ := GlobalTheory.HodgeSmooth.hodgeFrame_comp hσ hexf.choose_spec
  have hk : k'' = k := by
    apply hinj
    have e := x_eq_of_cxPt (congrArg Subtype.val (hkx''.trans hkx.symm))
    exact W.F.disj _ _ _ _ (W.period k'' x'') (W.period k x')
      ((W.lie k'' x'').1.symm.trans (e.trans (W.lie k x').1))
  subst hk
  have hu : W.F.u (W.ik k'') (W.Pm k'' x'') =
      (GlobalTheory.AllWt.ptF (S := CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫
        pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    (W.lie k'' x'').1.symm.trans (ptF_fst _).symm
  have hp : (GlobalTheory.AllWt.ptF (S := CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫ Z.jQ ≫
      pullback.fst Z.s (spMap β) = x.1 ≫ genι Z := by
    rw [← hkx'']
    exact (Category.assoc _ _ _).symm
  have hper := W.period k'' x''
  have he' := isExpAt_pushEx E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hhol' := pushEx_hol E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hker := pushEx_eq_one_iff E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hcw := pushEx_cubWeil E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g W.g exx _ hex hhol he' hhol'
  set A : Matrix (Fin g) (Fin W.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = L z := fun z => LinearMap.toMatrix'_mulVec _ z
  set Hm' : Matrix (Fin W.g) (Fin W.g) ℂ := Aᵀ * Hm * Aᵀᴴ with hHm'
  have hpull : ∀ z w, hermForm Hm' z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [hHm', GlobalTheory.HodgeInteriorGram.hermForm_pull', hAv, hAv]
  have hIm : ∀ a b, (hermForm Hm' (W.Pm k'' x'' a) (W.Pm k'' x'' b)).im = (W.F.Di (W.ik k'')).EF a b := by
    intro a b
    rw [hpull]
    have h1 : exx (L (W.Pm k'' x'' a)) = 1 := by rw [← hL]; exact (hker _).2 ⟨a, rfl⟩
    have h2 : exx (L (W.Pm k'' x'' b)) = 1 := by rw [← hL]; exact (hker _).2 ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := hint _ _ h1 h2
    rw [hm]
    congr 1
    refine GlobalTheory.HodgeInteriorGram.int_eq_of_exp_eq _ _ fun K hK => ?_
    have w1 := hweil K _ _ (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (m : ℂ) / K))) hK h1 h2
      (by rw [hm, Complex.ofReal_intCast]; rfl)
    have w2 := hcw K a b (Units.mk0 _ (Complex.exp_ne_zero
      (-(2 * Real.pi * Complex.I) * ((W.F.Di (W.ik k'')).EF a b : ℂ) / K))) hK rfl
    rw [hL, hL, L.map_smul, L.map_smul] at w2
    exact congrArg Units.val (ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (w1.unique w2))
  set Lc := L.toContinuousLinearEquiv with hLc
  have hLc' : ∀ z, Lc z = L z := fun z => rfl
  choose w hwt hwm hwc using fun (τ : E →+* ℂ) (b : Fin (Dw.mult τ)) =>
    GlobalTheory.HodgeSmooth.exists_lift_comb ((unfFam U σ).un k'' x'') hkx'' hexf.choose f hv τ b
  have hder : ∀ τ (b : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (W.F.ex (W.ik k'') (W.Pm k'' x'') z).left)
      (Lc.symm (Wd ⟨τ, b⟩)) (w τ b ≫ Z.m0.toSABMap.φ) := by
    intro τ b
    refine isDerivAt0_ex_of_push Z W.F _ _ _ hper hu (hwt τ b).1 ?_
    rw [hwm τ b]
    have e1 : (fun z => liftEx Z W.F _ (W.ik k'') (W.Pm k'' x'') hu z ≫ Z.m.φ) =
        fun z => (exx (Lc z)).left := funext fun z => by
      rw [hLc', ← hL]
      rfl
    rw [e1]
    refine (GlobalTheory.HodgeInteriorGram.isDerivAt0_comp_equiv Lc (fun v => (exx v).left) _ _).2 ?_
    rw [Lc.apply_symm_apply]
    exact hdirs ⟨τ, b⟩
  have hmat := fun τ τ' => hd k'' x'' hx'' (W.ik k'') (W.Pm k'' x'') hper Hm' hIm (W.lie k'' x'').1.symm τ τ'
    (fun b => Lc.symm (Wd ⟨τ, b⟩)) (fun b => Lc.symm (Wd ⟨τ', b⟩)) (fun b => w τ b ≫ Z.m0.toSABMap.φ)
    (fun b => w τ' b ≫ Z.m0.toSABMap.φ) (hexf.choose.co f τ) (hexf.choose.co f τ') (hder τ) (hder τ') (hwc τ) (hwc τ')
  refine ⟨fun τ => ?_, fun p q hpq => ?_⟩
  · obtain ⟨h1, -⟩ := hmat τ τ
    rw [hg τ]
    have e2 : (of fun b b' : Fin (Dw.mult τ) => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) =
        of fun b b' => hermForm Hm' (Lc.symm (Wd ⟨τ, b'⟩)) (Lc.symm (Wd ⟨τ, b⟩)) := by
      ext b b'
      simp only [of_apply, hpull, ← hLc', Lc.apply_symm_apply]
    rw [e2, h1]
    rcases Nat.eq_zero_or_pos (Dw.mult τ) with h0 | h0
    · ext b
      exact absurd b.2 (by omega)
    · have hdp := hdpos k'' x'' hx'' τ h0
      rw [smul_smul, ← Complex.ofReal_mul]
      congr 2
      field_simp
  · have h2 := (hmat q.1 p.1).2 hpq q.2 p.2
    rw [hpull, ← hLc', ← hLc', Lc.apply_symm_apply, Lc.apply_symm_apply] at h2
    exact h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPointStatement
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_frame_eq_riemannForm_at_interior_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit (unfFam U σ)), Function.Injective W.ik → ∀ (d : (unfFam U σ).Comp → (E →+* ℂ) → ℝ), (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) → (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = ((unfFam U σ).un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0)) → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (exx : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) exx → IsHolTo Set.univ (fun w => (exx w).left) → ∀ (k : (unfFam U σ).Comp) (x' : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x'.1 → cxPt Z ((unfFam U σ).un k x') = x → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame Z σ (x.1 ≫ genι Z)) (Wd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (exx w).left) Wd → (∀ τ, (hodgeMet Z U).gram x f τ = (((2 * Real.pi / d k τ : ℝ)) : ℂ) • Matrix.of fun b b' => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (Wd p) (Wd q) = 0 := by
  first | exact @GlobalTheory.HodgeInteriorGram.gram_eq_riem | exact GlobalTheory.HodgeInteriorGram.gram_eq_riem | (intros; apply GlobalTheory.HodgeInteriorGram.gram_eq_riem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryEtaleStalkForms
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.FarTrait

section Algebra
open Polynomial

theorem exists_coefficientField (S : Type) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CharZero (ResidueField S)] :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  let T : Set (Subring S) := {Λ | ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0}
  have hbot : (⊥ : Subring S) ∈ T := by
    intro x hx hm
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hx
    rw [← residue_eq_zero_iff, map_intCast, Int.cast_eq_zero] at hm
    simp [hm]
  obtain ⟨Λ, -, hΛ⟩ := zorn_le_nonempty₀ T (fun c hc hch y hy => by
    refine ⟨sSup c, fun x hx => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨K, hK, hxK⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hx
    exact hc hK x hxK) ⊥ hbot
  have hT : ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0 := hΛ.prop
  have hF : IsField Λ := by
    refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
    have hu : IsUnit (x : S) := by
      by_contra h
      exact hx (Subtype.ext (hT _ x.2 h))
    let Λ' : Subring S :=
      { carrier := {s | ∃ n : ℕ, (x : S) ^ n * s ∈ Λ}
        one_mem' := ⟨0, by simp⟩
        zero_mem' := ⟨0, by simp⟩
        mul_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by convert Λ.mul_mem hn hm using 1; ring⟩
        add_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by
            convert Λ.add_mem (Λ.mul_mem (Λ.pow_mem x.2 m) hn) (Λ.mul_mem (Λ.pow_mem x.2 n) hm) using 1; ring⟩
        neg_mem' := by
          rintro a ⟨n, hn⟩
          exact ⟨n, by convert Λ.neg_mem hn using 1; ring⟩ }
    have h' : Λ' ∈ T := by
      rintro s ⟨n, hn⟩ hm
      exact (hu.pow n).mul_right_eq_zero.1 (hT _ hn (Ideal.mul_mem_left _ _ hm))
    have hle : Λ' ≤ Λ := hΛ.le_of_ge h' fun s hs => ⟨0, by simpa using hs⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    exact ⟨⟨y, hle ⟨1, by rw [pow_one, hy]; exact Λ.one_mem⟩⟩, Subtype.ext hy⟩
  refine ⟨Λ, hF, fun s => ?_⟩
  letI := hF.toField
  have key : ∀ a : S, (∀ f : Λ[X], aeval a f ∈ maximalIdeal S → aeval a f = 0) → a ∈ Λ := fun a ha => by
    have h' : (aeval (R := Λ) a).toRingHom.range ∈ T := by
      rintro _ ⟨f, rfl⟩ hm
      exact ha f hm
    exact hΛ.le_of_ge h' (fun y hy => ⟨C ⟨y, hy⟩, by simp; rfl⟩) ⟨X, by simp⟩
  have hres : ∀ (a : S) (f : Λ[X]), residue S (aeval a f) = aeval (residue S a) f := fun a f =>
    (aeval_algHom_apply (IsScalarTower.toAlgHom Λ S (ResidueField S)) a f).symm
  by_cases hs : IsAlgebraic Λ (residue S s)
  · have hi := hs.isIntegral
    haveI : CharZero Λ := RingHom.charZero (algebraMap Λ (ResidueField S))
    have hsep : (minpoly Λ (residue S s)).Separable := (minpoly.irreducible hi).separable
    obtain ⟨a, ha, has⟩ := HenselianRing.is_henselian (I := maximalIdeal S)
      ((minpoly Λ (residue S s)).map (algebraMap Λ S)) ((minpoly.monic hi).map _) s
      (by rw [eval_map_algebraMap, ← residue_eq_zero_iff, hres, minpoly.aeval])
      (by
        rw [derivative_map, eval_map_algebraMap]
        have := hsep.aeval_derivative_ne_zero (minpoly.aeval Λ (residue S s))
        rw [← hres] at this
        exact (isUnit_iff_ne_zero (G₀ := ResidueField S)).2 this)
    have e : residue S a = residue S s := by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact has
    refine ⟨a, key a fun f hf => ?_, by rw [← neg_sub]; exact neg_mem has⟩
    rw [← residue_eq_zero_iff, hres, e] at hf
    obtain ⟨q, rfl⟩ := minpoly.dvd _ _ hf
    rw [IsRoot.def, eval_map_algebraMap] at ha
    rw [map_mul, ha, zero_mul]
  · refine ⟨s, key s fun f hf => ?_, by simp⟩
    rw [← residue_eq_zero_iff, hres] at hf
    by_contra h
    exact hs ⟨f, by rintro rfl; simp at h, hf⟩

end Algebra


open MvPowerSeries GlobalTheory.CohenStructure in
theorem exists_finite_over_normal (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S]
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (i : A →+* S),
      Function.Injective i ∧ i.Finite ∧ IsNoetherianRing A ∧ IsIntegrallyClosed A := by
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with h | rfl
  · obtain ⟨A, _, _, _, i, h1, h2, h3, h4, -⟩ := exists_finite_injective_of_isAdicComplete S p h
      (by rw [← residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ p) inferInstance hc
    exact ⟨A, inferInstance, inferInstance, i, h1, h2, h3, h4⟩
  haveI := CharP.charP_to_charZero (ResidueField S)
  by_cases hm : maximalIdeal S = ⊥
  · letI := (isField_iff_maximalIdeal_eq.2 hm).toField
    exact ⟨S, inferInstance, inferInstance, RingHom.id S, Function.injective_id, RingHom.Finite.id S, inferInstance,
      inferInstance⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨Λ, hF, h1⟩ := exists_coefficientField S
  letI := hF.toField
  obtain ⟨n, x₀, hx₀, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S a ha0 ha
  let x : Fin (n + 1) → S := Fin.cons a x₀
  have hx : ∀ i, x i ∈ maximalIdeal S := fun i => Fin.cases ha hx₀ i
  let A := MvPowerSeries (Fin (n + 1)) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ (n + 1)
  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  have : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  have hA := isAdicComplete_mvPowerSeries Λ (n + 1)
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rw [← Fin.range_cons]
    rintro _ ⟨i, rfl⟩
    show x i ∈ _
    rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
    exact Ideal.mem_map_of_mem (algebraMap A S)
      (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, inferInstance, algebraMap A S,
    injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin, inferInstance,
    isIntegrallyClosed_mvPowerSeries Λ (n + 1)⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

theorem exists_factor {R W : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CharZero W] (g : R →+* W) :
    ∃ (N : Type) (_ : CommRing N) (_ : IsDomain N) (_ : IsLocalRing N) (φ : R →+* N) (g' : N →+* W),
      IsCN N ∧ IsLocalHom φ ∧ Function.Injective g' ∧ ∀ r, g' (φ r) = g r := by
  haveI := RingHom.ker_isPrime g
  let S := R ⧸ RingHom.ker g
  let k : S →+* W := RingHom.kerLift g
  have hk : Function.Injective k := RingHom.kerLift_injective g
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  haveI : IsAdicComplete (maximalIdeal S) S := CompleteFiniteExtension.isAdicComplete_of_finite_local R S
  haveI : CharZero S := RingHom.charZero k
  obtain ⟨A, _, _, i, hi, hfin, _, _⟩ := exists_finite_over_normal S
  letI : Algebra A S := i.toAlgebra
  have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi
  have : Module.Finite A S := hfin
  let N := integralClosure S (FractionRing S)
  have hf : Module.Finite S N := finite_normalisation_of_finite_over_normal A S
  haveI : IsLocalRing N := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := S) _
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp k) := (IsFractionRing.injective W _).comp hk
  let K : FractionRing S →+* FractionRing W := IsFractionRing.lift j
  have hK : ∀ s, K (algebraMap S _ s) = algebraMap W _ (k s) := IsFractionRing.lift_algebraMap j
  have hint : ∀ x : N, K x ∈ (algebraMap W (FractionRing W)).range := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.map_of_comp_eq k K (RingHom.ext fun s => (hK s).symm) x.2)
  let eW : W ≃+* (algebraMap W (FractionRing W)).range :=
    RingEquiv.ofBijective (algebraMap W (FractionRing W)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective W (FractionRing W) (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
  let g' : N →+* W := eW.symm.toRingHom.comp ((K.comp N.val.toRingHom).codRestrict _ hint)
  have hg' : ∀ x : N, algebraMap W (FractionRing W) (g' x) = K x := fun x =>
    congrArg Subtype.val (eW.apply_symm_apply ⟨K x, hint x⟩)
  have hinj : Function.Injective g' := fun a b h =>
    Subtype.ext (K.injective ((hg' a).symm.trans ((congrArg _ h).trans (hg' b))))
  haveI : FaithfulSMul S N := (faithfulSMul_iff_algebraMap_injective S N).2 fun a b h =>
    IsFractionRing.injective S (FractionRing S) (congrArg Subtype.val h)
  haveI : IsLocalHom (Ideal.Quotient.mk (RingHom.ker g)) := IsLocalHom.of_surjective (S := S) _ Ideal.Quotient.mk_surjective
  refine ⟨N, inferInstance, inferInstance, inferInstance, (algebraMap S N).comp (Ideal.Quotient.mk _), g',
    ⟨IsNoetherianRing.of_finite S _, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing S),
      CompleteFiniteExtension.isAdicComplete_of_finite_local S _, RingHom.charZero g'⟩, inferInstance, hinj, fun r => ?_⟩
  exact IsFractionRing.injective W (FractionRing W) ((hg' _).trans (hK _))



end GlobalTheory.FarTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyFanOfStarSubdivisionCells
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyFanOfStarSubdivisionCells
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarFan

theorem homog_of_cover : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) → ∀ B ∈ psdCone (bar := bar) (X := X), ∀ t : ℝ, 0 ≤ t → evalR φ (t • B) = t * evalR φ B := by
  intro O _ bar φ X _ _ _ hcov B hB t ht
  obtain ⟨e, m, γ, c, hγ, hc, he⟩ := hcov B hB
  have key : ∀ (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (c₀ : Fin m → ℝ), (∀ i, 0 ≤ c₀ i) →
      (∀ a b, B₀ (e a) (e b) = ∑ i, c₀ i * (γ i a b : ℝ)) → evalR φ B₀ = ∑ i, c₀ i * φ.evalZ (γ i) :=
    fun B₀ c₀ hc₀ hB₀ => hγ.linear.eval_eq_sum (r := e.toLinearMap) e.surjective hc₀ hB₀
  have hv : ∀ a b, B (e a) (e b) = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    have := LinearMap.congr_fun₂ he a b
    simpa [LinearMap.sum_apply] using this
  rw [key B c hc hv, key (t • B) (fun i => t * c i) (fun i => mul_nonneg ht (hc i)) fun a b => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem isPolyFan_star : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, ψ'.evalZ β = n) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ψ'.evalZ β) → IsPolyFan H.bar q ψ' := by
  intro E _ _ _ H q ψ w ψ' hψ hw hst hint hpos X _ _ _ _ hX
  obtain ⟨S, hS, hcov⟩ := GlobalTheory.T.starSubdivision_cells_finite_cover_up_to_aut E H q ψ w ψ' hψ hw hst X hX
  have hcov' : ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      IsCell H.bar ψ' γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := fun B hB => by
    obtain ⟨e, m, γ, c, h1, -, h3, h4⟩ := hcov B hB
    exact ⟨e, m, γ, c, h1, h3, h4⟩
  exact
    { homog := homog_of_cover (𝓞 E) H.bar ψ' X hcov'
      superadd := GlobalTheory.T.superadditive_of_cells_cover_cone (𝓞 E) H.bar ψ' X hcov'
      integral := hint X hX
      pos := hpos X hX
      finite := ⟨S, hS, hcov⟩ }

end GlobalTheory.PolFan.StarFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyFanOfStarSubdivisionCellsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPolyFan_of_starSubdivision_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, ψ'.evalZ β = n) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ψ'.evalZ β) → IsPolyFan H.bar q ψ' := by
  first | exact @GlobalTheory.PolFan.StarFan.isPolyFan_star | exact GlobalTheory.PolFan.StarFan.isPolyFan_star | (intros; apply GlobalTheory.PolFan.StarFan.isPolyFan_star <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGoodSplitHeckePlaceOfSplitNotExcluded
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGoodSplitHeckePlaceOfSplitNotExcluded
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 2000000

namespace GlobalTheory.GoodPlaceAtState

theorem natCast_mem_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : ((n : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((n : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal := by
  rw [← Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  refine Ideal.subset_span ⟨(n : 𝓞 K), h, ?_⟩
  simp

theorem natCast_mem_of_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : ((n : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal) : ((n : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have := natCast_mem_conjPl (Formalism.DivisionValues.conjPl w) n h
  rwa [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at this

end GlobalTheory.GoodPlaceAtState

theorem GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (x : St P) (v : PlE (Dof x).host), IsSplitPl (Dof x).host v → v ∉ SbD (Dof x) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace x.m.z.R.toRealDat v := by
  intro K B f T w P x v hs hv
  have hc := x.m.z.pins.char
  have hA := hc.allPl
  have hL := hc.base.lev
  have hlow : ∀ k : Fin 2, (((Dof x).host.g k : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro k hk
    apply hv
    refine (lowSet_finite (Dof x)).mem_toFinset.2 ⟨(Dof x).host.g k, ?_, ((Dof x).host.g_prime k).ne_zero, hk⟩
    fin_cases k <;> simp [lowAll]
  have hdiv : ∀ PP, PP ∈ x.m.z.R.toRealDat.Sb → ∃ k : Fin 2, (((Dof x).host.g k : ℕ) : 𝓞 (Dof x).host.E) ∈ PP.asIdeal := by
    intro PP hPP
    have hm : PP ∈ x.m.z.R.Pg := by rw [← hA]; exact hPP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
    exact ⟨k, Formalism.L2.Host.PiBar.overP _ hk⟩

  unfold GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace
  refine ⟨⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hs, fun hm => ?_, fun Q hQ he => ?_⟩, fun hm => ?_⟩
  · obtain ⟨k, hk⟩ := hdiv v hm
    exact hlow k hk
  · obtain ⟨k, hk⟩ := hdiv Q hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at he
    rw [he] at hk
    exact hlow k (GlobalTheory.GoodPlaceAtState.natCast_mem_of_conjPl v _ hk)
  · rw [Nat.cast_mul] at hm
    rcases v.isPrime.mem_or_mem hm with h | h
    · exact hlow 0 h
    · exact hlow 1 h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGoodSplitHeckePlaceOfSplitNotExcludedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodSplitHeckePlace_of_split_not_excluded : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (x : St P) (v : PlE (Dof x).host), IsSplitPl (Dof x).host v → v ∉ SbD (Dof x) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace x.m.z.R.toRealDat v := by
  first | exact @GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off | exact GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off | (intros; apply GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepOfHeq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.CopyRead

theorem occ_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {y : Hd R} {Φ : Type}
    {rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r} (h : Reps y F rep) : y.occ F = {ρ | ∃ π, (rep π).Iso ρ} := by
  refine Set.ext fun ρ => ⟨h.all ρ, fun ⟨π, hi⟩ => ?_⟩
  obtain ⟨b, hb⟩ := h.mem π
  refine ⟨b, ?_⟩
  unfold principalLevelFrame.isotE at hb ⊢
  rw [← principalLevelFrame.isotL_iso _ _ _ _ _ _ (principalLevelFrame.conjT_iso hi)]
  exact hb

theorem rep_eq {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {S S' U : Set (Formalism.L2.NG.FinTyp L n)} (e : S = U) (e' : S' = U)
    {c : Formalism.L2.Col.FinTypCls S} {c' : Formalism.L2.Col.FinTypCls S'} {ρ : Formalism.L2.NG.FinTyp L n}
    (h : (Formalism.L2.Col.finTypRep S c).Iso ρ) (h' : (Formalism.L2.Col.finTypRep S' c').Iso ρ) :
    Formalism.L2.Col.finTypRep S c = Formalism.L2.Col.finTypRep S' c' := by
  subst e e'
  exact congrArg _ (Formalism.L2.Col.finTypRep_inj (Formalism.L2.NG.IsoRep.trans h (Formalism.L2.NG.IsoRep.symm (Formalism.L2.Col.finTypRep _ c').stable h')))

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}


set_option maxHeartbeats 2000000 in
theorem rep_pin {o : q.Over} {m : Moved o} (hco : m.Coh) {s : Side0 o} (r : ReadPk m s) (hp : r.Pin) (π : q.p.Φ) :
    ∃ (S : Set (Formalism.L2.NG.FinTyp (w.st Z₀).toD7.host.E (w.st Z₀).toD7.R.r)) (c : Formalism.L2.Col.FinTypCls S),
      S = {ρ | ∃ π', (q.t.rep π').Iso ρ} ∧ (Formalism.L2.Col.finTypRep S c).Iso (q.t.rep π) ∧
        HEq (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT ((π)))) (Formalism.L2.Col.finTypRep S c) := by
  have e : ((by with_unfolding_all exact (m.t.rep :)) : type_of% q.t.rep) = q.t.rep := eq_of_heq ((by with_unfolding_all exact (hco.rep :)))
  have h1 := occ_iff m.t.reps
  have h2 := congrArg (fun P : type_of% m.y.PY => principalLevelFrame.OccRows m.z.R.θ P (m.z.R.MY 0)
    (fun b => levS _ (m.z.R.βY 0) (m.z.R.dat0 (m.z.R.toRealDat.levR m.z.F.lv2 b)))
    (fun b => levChi _ (m.z.R.βY 0) (m.z.R.dat0 (m.z.R.toRealDat.levR m.z.F.lv2 b))) (fun _ => m.z.R.toRealDat.e0)) r.PY
  have h3 := h2.trans h1
  have h4 := hp.rep ((by with_unfolding_all exact (π :)))
  rw [← e]
  have h5 : ∃ (S : Set (Formalism.L2.NG.FinTyp (w.st o.Z).toD7.host.E (w.st o.Z).toD7.R.r)) (c : Formalism.L2.Col.FinTypCls S),
      S = {ρ | ∃ π', (m.t.rep π').Iso ρ} ∧ (Formalism.L2.Col.finTypRep S c).Iso (m.t.rep π) ∧
        HEq (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT ((by with_unfolding_all exact (π :))))) (Formalism.L2.Col.finTypRep S c) := ⟨_, r.Y.eFT π, h3, h4, HEq.rfl⟩
  exact (by with_unfolding_all exact (h5 :))


set_option maxHeartbeats 2000000 in
theorem repOf_heq {o o' : q.Over} {m : Moved o} (hco : m.Coh) {s : Side0 o} (r : ReadPk m s) (hp : r.Pin)
    {m' : Moved o'} (hco' : m'.Coh) {s' : Side0 o'} (r' : ReadPk m' s') (hp' : r'.Pin) :
    HEq (GlobalTheory.HeightCounting.repOf r'.Y) (GlobalTheory.HeightCounting.repOf r.Y) := by
  have h : ∀ π : q.p.Φ, ((by with_unfolding_all exact ((GlobalTheory.HeightCounting.repOf r'.Y ((π))) : _)) : Formalism.L2.NG.FinTyp (w.st Z₀).toD7.host.E (w.st Z₀).toD7.R.r) =
      (by with_unfolding_all exact ((GlobalTheory.HeightCounting.repOf r.Y ((π))) : _)) := fun π => by
    obtain ⟨S, c, h1, h2, h3⟩ := rep_pin hco r hp π
    obtain ⟨S', c', h1', h2', h3'⟩ := rep_pin hco' r' hp' π
    exact eq_of_heq ((by with_unfolding_all exact ((h3'.trans ((heq_of_eq (rep_eq h1' h1 h2' h2)).trans h3.symm)) :)))
  exact (by with_unfolding_all exact ((heq_of_eq (funext h)) :))

end GlobalTheory.Mem.R3.Rw.CopyRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionOldCellMultiplicityLe
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionOldCellMultiplicityLe
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem starOld_cell_mult_le (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ lab w ψ' : InvFun (𝓞 E))
    (hDom : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Dominates H.bar X)
    (hφ : IsPolyFan H.bar q φ) (hlab : SimpLab H.bar q φ lab) (M : ℕ) (hM : maxMult H.bar q φ ≤ M)
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ')
    (hli' : LinearIndependent ℤ γ') (hp' : ∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X))
    (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hγφ : IsCell H.bar φ γ) (hγψ : IsCell H.bar ψ' γ)
    (hw : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0)
    (hin : ∀ j, InRCone γ (γ' j)) :
    ∃ hφ' : IsCell H.bar φ γ', cellMult H.bar (fun i => (⟨γ' i, hφ'.mem i⟩ : balForms H.bar X)) ≤ M ∧
      ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1 := by

  obtain ⟨m', δ, hδ, hδli, -, hδγ⟩ := hlab.2 X hX m γ hγφ
  obtain ⟨δ₁, hδ₁, hδ₁li, hδ₁p, hδδ₁⟩ := GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell H.bar φ δ hδ hδli
  have hγδ₁ : ∀ k, InRCone δ₁ (γ k) := fun k => hδδ₁ _ (hδγ k)

  obtain ⟨h₂, h₂n, h₂z, h₂c⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone H.bar φ δ₁ γ hδ₁ hγφ hγδ₁
  obtain ⟨h₁, h₁n, h₁z, h₁c⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone H.bar ψ' γ γ' hγψ hγ' hin
  obtain ⟨h, hn, hz, hc⟩ := GlobalTheory.T.exists_linForm_cut_face_of_face_of_cone H.bar δ₁ γ γ' h₂ h₁ hδ₁.mem hδ₁.nonneg hin h₂n h₂z h₂c h₁n h₁z h₁c
  have hin₁ : ∀ j, InRCone δ₁ (γ' j) := fun j => inRCone_trans hγδ₁ (hin j)
  obtain ⟨s, hs, hsf⟩ := GlobalTheory.T.eq_subfamily_of_face_simplicialCone_primitive H.bar δ₁ γ' hδ₁.mem hγ'.mem h hδ₁li hli' hδ₁p hp' hin₁ hn hz
    (fun i hi => hc _ (hδ₁.mem i) (hδ₁.nonneg i) (inRCone_self δ₁ i) hi)
  have hγ'eq : γ' = fun j => δ₁ (s j) := funext hs
  have hcut : IsFaceCut δ₁ s h := ⟨hn, hsf⟩
  have hφ' : IsCell H.bar φ γ' := by
    rw [hγ'eq]; exact GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q φ hφ X hX (hDom X) m' δ₁ hδ₁ _ s h hcut
  refine ⟨hφ', ?_, fun β hβ hβn hβc h1 => ?_⟩
  ·
    have hliB : LinearIndependent ℤ (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X)) :=
      LinearIndependent.of_comp (balForms H.bar X).subtype hδ₁li
    have hrange : Set.range (fun j => (⟨γ' j, hφ'.mem j⟩ : balForms H.bar X)) ⊆
        Set.range (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X)) := by
      rintro _ ⟨j, rfl⟩
      exact ⟨s j, Subtype.ext (hs j).symm⟩
    have hdvd := GlobalTheory.T.natCard_torsion_quot_span_dvd_of_range_subset' (balForms H.bar X) _ _ hliB hrange
    have hpos := GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X))
    have hle := SmoothEnd.cellMult_le_maxMult hX hδ₁ hδ₁li hδ₁p
    have hle' : cellMult H.bar (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X)) ≤ M := by
      exact_mod_cast hle.trans hM
    exact (Nat.le_of_dvd hpos hdvd).trans hle'
  ·
    rw [hw β hβ hβn (inRCone_trans hin hβc)] at h1
    exact zero_ne_one h1

end GlobalTheory.PolFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionOldCellMultiplicityLeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_oldCell_multiplicity_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ γ → IsCell H.bar ψ' γ →
          (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (∀ j, InRCone γ (γ' j)) →
          ∃ hφ : IsCell H.bar φ γ', cellMult H.bar (fun i => (⟨γ' i, hφ.mem i⟩ : balForms H.bar X)) ≤ M ∧
            ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1 := by
  first | exact @GlobalTheory.PolFan.starOld_cell_mult_le | exact GlobalTheory.PolFan.starOld_cell_mult_le | (intros; apply GlobalTheory.PolFan.starOld_cell_mult_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormPiecesInEveryCellCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormPiecesInEveryCellCone
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan.OrbMark

theorem inRCone_pullAdd_of_isCell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)),
  IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell H.bar φ δ₀ → ∀ t : Fin m₀ → ℝ, (∀ i, 0 ≤ t i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] (π : X₀ →ₗ[𝓞 E] Y), Function.Surjective π → ∀ (τ : 𝓞 E ≃+* 𝓞 E) (f : X →+ Y), τ H.w0 = H.w0 →
    Function.Surjective f → (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y,
    (∀ i, 0 < t i → pull π (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms H.bar X ∧ ∀ y, 0 ≤ pullAdd f (u i) y y) →
  ∀ β : LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (pullAdd f (u i)) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ i, 0 < t i → InRCone δ (pullAdd f (u i)) := by
  intro E _ _ _ H φ htw X₀ _ _ _ m₀ δ₀ h₀ t ht X Y _ _ _ _ _ _ π hπ τ f hτ hf hsm u hu β hβ m δ hδ c hc hβc i hi
  classical
  let S : Finset (Fin m₀) := Finset.univ.filter fun j => 0 < t j
  let s : Fin S.card ↪ Fin m₀ := (S.orderEmbOfFin rfl).toEmbedding
  have hrange : Set.range s = (S : Set (Fin m₀)) := Finset.range_orderEmbOfFin S rfl
  have hs : ∀ j, 0 < t (s j) := fun j => by
    have : s j ∈ (S : Set (Fin m₀)) := hrange ▸ Set.mem_range_self j
    simpa [S] using this
  have hmem : ∀ j, 0 < t j → j ∈ Set.range s := fun j hj => by
    rw [hrange]; simpa [S] using hj
  have h1 : φ.LinearOn (fun j => δ₀ (s j)) := linearOn_comp h₀.linear s
  have e1 : (fun j => δ₀ (s j)) = fun j => pull π (u (s j)) := funext fun j => ((hu _ (hs j)).1).symm
  rw [e1] at h1
  have h2 : φ.LinearOn (fun j => u (s j)) := (linearOn_pull_iff hπ).1 h1
  have h3 : φ.LinearOn (fun j => pullAdd f (u (s j))) := by
    intro a ha
    have hz : ∀ j, φ.evalZ (pullAdd f (u (s j))) = φ.evalZ (u (s j)) := fun j =>
      eval_pull_semilinear_of_isTwInv E H φ htw τ hτ f hf hsm fun x y => ((u (s j) x y : ℤ) : ℝ)
    have := h2 a ha
    simp only [hz]
    rw [← this]
    exact eval_pull_semilinear_of_isTwInv E H φ htw τ hτ f hf hsm fun x y => ∑ j, a j * ((u (s j) x y : ℤ) : ℝ)
  have hsum : toReal β = ∑ j, t (s j) • toReal (pullAdd f (u (s j))) := by
    rw [hβ]
    refine (Fintype.sum_of_injective s s.injective _ _ (fun j hj => ?_) (fun j => rfl)).symm
    have : t j = 0 := le_antisymm (not_lt.1 fun h => hj (hmem j h)) (ht j)
    rw [this, zero_smul]
  obtain ⟨j, rfl⟩ := hmem i hi
  exact GlobalTheory.T.inRealCone_cell_of_linearPiece_through_cellPoint H.bar φ δ (fun j => pullAdd f (u (s j))) hδ (fun j => (hu _ (hs j)).2.1) (fun j => (hu _ (hs j)).2.2) h3
    β c (fun j => t (s j)) hc hs hβc hsum j

end GlobalTheory.PolFan.OrbMark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormPiecesInEveryCellConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marked_form_pieces_in_every_cell_cone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell H.bar φ δ₀ → ∀ t : Fin m₀ → ℝ, (∀ i, 0 ≤ t i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] (π : X₀ →ₗ[𝓞 E] Y), Function.Surjective π → ∀ (τ : 𝓞 E ≃+* 𝓞 E) (f : X →+ Y), τ H.w0 = H.w0 →
    Function.Surjective f → (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y,
    (∀ i, 0 < t i → pull π (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms H.bar X ∧ ∀ y, 0 ≤ pullAdd f (u i) y y) →
  ∀ β : LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (pullAdd f (u i)) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ i, 0 < t i → InRCone δ (pullAdd f (u i)) := by
  first | exact @GlobalTheory.PolFan.OrbMark.inRCone_pullAdd_of_isCell | exact GlobalTheory.PolFan.OrbMark.inRCone_pullAdd_of_isCell | (intros; apply GlobalTheory.PolFan.OrbMark.inRCone_pullAdd_of_isCell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigISupEqTopOfSep
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.heckeEig_iSup_eq_top_of_sep {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Finite X]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) :
    ⨆ x, heckeEig T act x = ⊤ := by
  classical
  have := Fintype.ofFinite X
  have hs' : ∀ x y : X, ∃ f : T, x ≠ y → (f : X → O) x ≠ (f : X → O) y := by
    intro x y
    by_cases h : x = y
    · exact ⟨1, fun h' => (h' h).elim⟩
    · obtain ⟨f, hf, hne⟩ := hsep x y h
      exact ⟨⟨f, hf⟩, fun _ => hne⟩
  choose s hs using hs'
  let E : X → T := fun x => ∏ y ∈ Finset.univ.erase x, (s x y - algebraMap O T ((s x y : X → O) y))
  have hE : ∀ x z, ((E x : T) : X → O) z = ∏ y ∈ Finset.univ.erase x, ((s x y : X → O) z - (s x y : X → O) y) := by
    intro x z
    simp [E, Subalgebra.coe_prod, Finset.prod_apply]
  let d : X → O := fun x => ((E x : T) : X → O) x
  have hd : ∀ x, d x ≠ 0 := by
    intro x
    simp only [d, hE]
    exact Finset.prod_ne_zero_iff.mpr fun y hy => sub_ne_zero.mpr (hs x y (Ne.symm (Finset.ne_of_mem_erase hy)))
  have hE0 : ∀ x z, z ≠ x → ((E x : T) : X → O) z = 0 := by
    intro x z hz
    rw [hE]
    exact Finset.prod_eq_zero (i := z) (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ _⟩) (sub_self _)
  have hmul : ∀ (g : T) x, g * E x = ((g : X → O) x) • E x := by
    intro g x
    apply Subtype.ext
    funext z
    by_cases hz : z = x
    · subst hz; simp
    · simp [hE0 x z hz]
  let F : X → O := fun x => ∏ x' ∈ Finset.univ.erase x, d x'
  let c : O := ∏ x, d x
  have hsum : ∑ x, F x • E x = algebraMap O T c := by
    apply Subtype.ext
    funext z
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single z]
    · simp only [F, c]
      show (∏ x' ∈ Finset.univ.erase z, d x') * d z = _
      rw [mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ z)]
      simp
    · intro x _ hx
      rw [hE0 x z (Ne.symm hx), mul_zero]
    · intro h; exact (h (Finset.mem_univ z)).elim
  let K := FractionRing O
  let ψ : T →ₐ[O] Module.End K (TensorProduct O K M) := (Module.End.baseChangeHom O K M).comp act
  have hψ : ∀ f, ψ f = (act f).baseChange K := fun f => rfl
  have hmem : ∀ x (m : TensorProduct O K M), ψ (E x) m ∈ heckeEig T act x := by
    intro x m
    simp only [heckeEig]
    refine Submodule.mem_iInf _ |>.mpr fun f => ?_
    rw [Module.End.mem_eigenspace_iff, ← hψ]
    rw [show ψ f (ψ (E x) m) = (ψ f * ψ (E x)) m from rfl, ← map_mul, hmul, map_smul,
      LinearMap.smul_apply, algebraMap_smul]
  have hc : algebraMap O K c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact Finset.prod_ne_zero_iff.mpr fun x _ => hd x
  refine eq_top_iff.mpr fun m _ => ?_
  have hcm : algebraMap O K c • m = ∑ x, F x • ψ (E x) m := by
    rw [algebraMap_smul]
    have := congrArg (fun f => ψ f m) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, AlgHom.commutes] at this
    rw [LinearMap.sum_apply] at this
    simp only [LinearMap.smul_apply] at this
    rw [this, Module.algebraMap_end_apply]
  have : m = (algebraMap O K c)⁻¹ • (algebraMap O K c • m) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this, hcm]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun x _ => ?_)
  exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_iSup_of_mem x (hmem x m))

theorem eigSpan_of_record (D : D7) : D.nd.EigSpan :=
  fun i => GlobalTheory.heckeEig_iSup_eq_top_of_sep (D.nd.T i) (D.nd.act i) (D.nd.T_sep i)

end GlobalTheory.HeightCounting.Up

end
end
