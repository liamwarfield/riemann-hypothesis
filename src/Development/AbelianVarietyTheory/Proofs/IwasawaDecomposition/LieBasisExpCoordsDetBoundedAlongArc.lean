module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcLieBasisExponentialCoordsHasSum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcLieBasisExponentialCoordsHasSum
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcLieCoord

open MonoidalCategory CartesianMonoidalCategory MonObj Filter GlobalTheory.ArcLie

theorem comb_tan {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (v : Fin n → (epsR R ⟶ G)) (hv : ∀ k, IsTangent (v k)) (c : Fin n → R) (w : epsR R ⟶ G) (hc : IsLieComb c v w) :
    IsTangent w := by
  rw [GlobalTheory.PowLie.isLieComb_iff_prod] at hc
  subst hc
  rw [GlobalTheory.PowLie.isTangent_iff]
  have e0 : ∀ a : R, GlobalTheory.PowLie.zeroPt R ≫ GlobalTheory.PowLie.sc a = GlobalTheory.PowLie.zeroPt R := fun a => by
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, GlobalTheory.PowLie.zeroPt, GlobalTheory.PowLie.sc, Over.homMk_left]
    rw [GlobalTheory.TanMod.spMap_comp']
    congr 1
    refine RingHom.ext fun r => ?_
    simp [epsScaleR]
  have e1 := map_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G) (GlobalTheory.PowLie.zeroPt R)) (fun k => GlobalTheory.PowLie.sc (c k) ≫ v k)
    Finset.univ
  refine e1.trans ?_
  refine (Finset.prod_congr rfl fun k _ => ?_).trans (Finset.prod_const_one)
  show GlobalTheory.PowLie.zeroPt R ≫ GlobalTheory.PowLie.sc (c k) ≫ v k = 1
  rw [← Category.assoc, e0, (GlobalTheory.PowLie.isTangent_iff _).1 (hv k)]
  rfl

theorem sep_laurent {X : Scheme.{0}} {x : Sp (PowerSeries ℂ) ⟶ X} {G : Over X} {G' : Over (Sp (PowerSeries ℂ))} [GrpObj G]
    [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {n : ℕ}
    (v : Fin n → (epsR (PowerSeries ℂ) ⟶ G')) (hv : IsLieBasis v) {V : G.left.Opens} (hA : IsAffineOpen V)
    (hV : ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V) (a : Fin n → ℂ⸨X⸩)
    (ha : ∀ f : Γ(G.left, V), ∑ k, a k * HahnSeries.ofPowerSeries ℤ ℂ (valR ((v k).left ≫ φ) V f).snd = 0) : a = 0 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (PowerSeries ℂ)) (S := ℂ⸨X⸩)
    Finset.univ a
  choose b hb using fun k => hd k (Finset.mem_univ k)
  have hinj : Function.Injective (HahnSeries.ofPowerSeries ℤ ℂ) := HahnSeries.ofPowerSeries_injective
  have hb' : ∀ k, HahnSeries.ofPowerSeries ℤ ℂ (b k) = HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) * a k := fun k => by
    rw [← LaurentSeries.coe_algebraMap, hb k, Algebra.smul_def, LaurentSeries.coe_algebraMap]
  have h0 := GlobalTheory.T.derivatives_separate_lieBasis_coeffs_cartesian h v hv hA hV b fun f => hinj (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero]
    have e := congrArg (fun t => HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) * t) (ha f)
    simp only [mul_zero, Finset.mul_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hb', _root_.mul_assoc])
  funext k
  have hd0 : HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) ≠ 0 := fun e =>
    nonZeroDivisors.coe_ne_zero d (hinj (e.trans (map_zero _).symm))
  have := hb' k
  rw [h0, Pi.zero_apply, map_zero] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hd0

theorem valR_eq_ev' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = ev x U h f := by
  rw [valR, dite_eq_left h]; rfl

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem point_snd {Y : Model Xo c β} (M : GChart Y) {z : Sp ℂ ⟶ Y.X} {hz : ⊤ ≤ z ⁻¹ᵁ M.U} {x : KeyIn ℂ}
    {φ : x.P.A.left ⟶ Y.t.G.left} (hK : GlobalTheory.ArcNormal.KeyAtVia M z hz x φ) {g : ℕ} (u : HolUnif x.P.A x.P.L g)
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y.t.G.left)) (he : ∀ t, e t = (u.ex t).left ≫ φ) (i : Fin x.P.g) (j : Fin M.n)
    (hij : (i : ℕ) = j) (wv : Fin g → ℂ) (hd : u.IsDiff wv (x.v i)) (V : Y.t.G.left.Opens)
    (hV : ⊤ ≤ (spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j) ⁻¹ᵁ V) (f : Γ(Y.t.G.left, V)) :
    (valR (spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j) V f).snd = fderiv ℂ (fun t => valAt' (e t) V f) 0 wv := by
  obtain ⟨-, -, hg', -, -, -, -, hv⟩ := hK
  have e1 : (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j := by
    rw [hv i]
    congr 2
    exact Fin.ext hij
  rw [← e1] at hV ⊢
  have hU : ⊤ ≤ (x.v i).left ⁻¹ᵁ (φ ⁻¹ᵁ V) := hV
  have hd' := hd (φ ⁻¹ᵁ V) hU ((φ.app V).hom f)
  have e2 : (fun t => valAt' (e t) V f) = fun t => valAt' (u.ex t).left (φ ⁻¹ᵁ V) ((φ.app V).hom f) :=
    funext fun t => by rw [he, GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_comp]
  rw [e2, ← hd', GlobalTheory.HolHom.valR_comp, GlobalTheory.HolHom.valR_eq _ _ hU]
  rfl

end Point

theorem lie_coords_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U) (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ) (hn : M.n = g) (v' : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) → IsLieBasis v → (Matrix.of z).det ≠ 0 → (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ (Fin.cast hn.symm i)) → (∀ i, IsLieComb (A i) v (v' i)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → ∀ i, (∀ k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)) ∧ ∀ j, Wv (Fin.cast hg.symm i) j = ∑ k, (∑' m : ℕ, PowerSeries.coeff m (A i k) * eTwoPi w ^ m) * z k j := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha M hM e v z hn v' A _ _ _ hχ _ hez hvb hdet hv' hA
  let Ω : Type := {q : ℂ × (Sp ℂ ⟶ Xo.XF c) × ((Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left)) × (Fin g → Fin g → ℂ) //
    q.2.1 ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw q.1) ∧ q.2.1 ≫ pullback.snd _ _ = spMap σ ∧
    (∀ t, q.2.2.1 t ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw q.1) t).left ∧
      q.2.2.1 t ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ) ∧
    ⊤ ≤ (q.2.1 ≫ Y.j) ⁻¹ᵁ M.U ∧ ∀ (hz : ⊤ ≤ (q.2.1 ≫ Y.j) ⁻¹ᵁ M.U) (i : Fin g) (Vo : Y.t.G.left.Opens)
      (f : Γ(Y.t.G.left, Vo)), ⊤ ≤ (spMap (dualMap (ev (q.2.1 ≫ Y.j) M.U hz)) ≫ M.v₀ (Fin.cast hn.symm i)) ⁻¹ᵁ Vo →
      (valR (spMap (dualMap (ev (q.2.1 ≫ Y.j) M.U hz)) ≫ M.v₀ (Fin.cast hn.symm i)) Vo f).snd =
        ∑ k, q.2.2.2 i k * fderiv ℂ (fun t => valAt' (q.2.2.1 t ≫ Y.m.φ) Vo f) 0 (z k)}
  let pw : Ω → ℂ := fun ω => ω.1.1
  let ψ : Ω → (Γ(Y.X, M.U) →+* ℂ) := fun ω => ev (ω.1.2.1 ≫ Y.j) M.U ω.2.2.2.2.1
  have hcart := W.m.cart
  have tanv : ∀ k, IsTangent (v k) := hvb.1
  suffices hs : ∀ i k, Cv pw (HahnSeries.ofPowerSeries ℤ ℂ (A i k)) (fun ω => ω.1.2.2.2 i k) by
    obtain ⟨T, hT⟩ := high_iff.1 (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => hs i k)
    refine ⟨T, fun w hw yF h1 h2 hz x φ hK hg u Wv hF hD i => ?_⟩
    choose xF hxF using hF
    have hu : IsUnit (Matrix.of z).det := isUnit_iff_ne_zero.2 hdet
    let Gw : Fin g → Fin g → ℂ := fun i' => Matrix.vecMul (Wv (Fin.cast hg.symm i')) (Matrix.of z)⁻¹
    have hGw : ∀ i' j, Wv (Fin.cast hg.symm i') j = ∑ k, Gw i' k * z k j := fun i' j => by
      have e0 : Matrix.vecMul (Gw i') (Matrix.of z) = Wv (Fin.cast hg.symm i') := by
        simp only [Gw]
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
      rw [← e0]
      simp [Matrix.vecMul, dotProduct]
    have hω : ∀ (hz' : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (i' : Fin g) (Vo : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, Vo)),
        ⊤ ≤ (spMap (dualMap (ev (yF ≫ Y.j) M.U hz')) ≫ M.v₀ (Fin.cast hn.symm i')) ⁻¹ᵁ Vo →
        (valR (spMap (dualMap (ev (yF ≫ Y.j) M.U hz')) ≫ M.v₀ (Fin.cast hn.symm i')) Vo f).snd =
          ∑ k, Gw i' k * fderiv ℂ (fun t => valAt' (xF t ≫ Y.m.φ) Vo f) 0 (z k) := by
      intro hz' i' Vo f hV
      rw [point_snd M hK u (fun t => xF t ≫ Y.m.φ) (fun t => (hxF t).2.2.symm) (Fin.cast hg.symm i') (Fin.cast hn.symm i')
        rfl _ (hD _) Vo hV f]
      have e3 : Wv (Fin.cast hg.symm i') = ∑ k, Gw i' k • z k := funext fun j => by
        rw [hGw i' j, Finset.sum_apply]
        simp
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e3, map_sum]
      simp [smul_eq_mul]
    have hT' := hT ⟨(w, yF, xF, Gw), h1, h2, fun t => ⟨(hxF t).1, (hxF t).2.1⟩, hz, hω⟩ hw i
    have hS : ∀ k, SumsAt (A i k) w (Gw i k) := fun k => GlobalTheory.Conv.sumsAt_iff.2 (hT' k)
    refine ⟨fun k => HasSum.summable (hS k), fun j => ?_⟩
    rw [hGw i j]
    exact Finset.sum_congr rfl fun k _ => by rw [HasSum.tsum_eq (hS k)]
  intro i
  obtain ⟨Vo, hVo, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y.t.G.left) (U := ⊤)
    (x := (show Sp (PowerSeries ℂ) ⟶ Y.t.G.left from (η[W.t.G]).left ≫ W.m.φ) (IsLocalRing.closedPoint (PowerSeries ℂ)))
    trivial
  have hVη : ⊤ ≤ ((η[W.t.G]).left ≫ W.m.φ) ⁻¹ᵁ Vo :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of (PowerSeries ℂ)) _ hpV).ge
  have hvV : ∀ k, ⊤ ≤ ((v k).left ≫ W.m.φ) ⁻¹ᵁ Vo := fun k => tan_le hcart _ (tanv k) Vo hVη
  have hv'V : ⊤ ≤ ((v' i).left ≫ W.m.φ) ⁻¹ᵁ Vo := tan_le hcart _ (comb_tan v tanv _ _ (hA i)) Vo hVη
  let φL : Γ(Y.X, M.U) →+* ℂ⸨X⸩ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (ev χ M.U hM)
  have eχ : spMap (dualMap φL) ≫ M.v₀ (Fin.cast hn.symm i) =
      spMap (dualMap (HahnSeries.ofPowerSeries ℤ ℂ)) ≫ (v' i).left ≫ W.m.φ := by
    rw [hv' i, dualMap_comp, ← spMap_comp', Category.assoc]
  have hc : ∀ r, Cv pw (φL r) (fun ω => ψ ω r) := by
    intro r
    obtain ⟨T', hT'⟩ := Ha.point M.U r hM
    refine high_iff.2 ⟨T', fun ω hω => ?_⟩
    obtain ⟨-, hs⟩ := hT' _ hω ω.1.2.1 ω.2.1 ω.2.2.1
    have h3 := GlobalTheory.Conv.sumsAt_iff.1 hs
    have e4 : valR χ M.U r = ev χ M.U hM r := valR_eq_ev' χ M.U hM r
    have e5 : valAt' (ω.1.2.1 ≫ Y.j) M.U r = ψ ω r := valR_eq_ev' (ω.1.2.1 ≫ Y.j) M.U ω.2.2.2.2.1 r
    rw [e4, e5] at h3
    exact h3
  have hch := fun f => cv_chart (M.v₀ (Fin.cast hn.symm i)) Vo f φL ψ hc (by rw [eχ]; exact le_preimage_comp _ hv'V)
  refine cv_coeff (F := Γ(Y.t.G.left, Vo)) (m := g)
    (A := fun f k => HahnSeries.ofPowerSeries ℤ ℂ (valR ((v k).left ≫ W.m.φ) Vo f).snd)
    (B := fun f => HahnSeries.ofPowerSeries ℤ ℂ (valR ((v' i).left ≫ W.m.φ) Vo f).snd)
    (Aw := fun f k ω => fderiv ℂ (fun t => valAt' (ω.1.2.2.1 t ≫ Y.m.φ) Vo f) 0 (z k))
    (Bw := fun f ω => (valR (spMap (dualMap (ψ ω)) ≫ M.v₀ (Fin.cast hn.symm i)) Vo f).snd)
    (Gw := fun k ω => ω.1.2.2.2 i k)
    (fun f => ?_) (sep_laurent hcart v hvb hVo hVη) (fun f k => ?_) (fun f => ?_) (fun f => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [comb_snd hcart v tanv (A i) (v' i) (hA i) Vo hVη f, map_sum]
      exact Finset.sum_congr rfl fun k _ => map_mul _ _ _
  · obtain ⟨T', hT'⟩ := Ha.diff (z k) (e k) (v k) Vo f (hez k).2.1 (hez k).2.2
      (fun n ρ κ vn h1 h2 h3 h4 h5 => (hez k).1 n ρ κ vn h1 h2 h3 h4 (thick_base _ n (v k) ρ vn h1 h5) h5) (hvV k)
    exact high_iff.2 ⟨T', fun ω hω => GlobalTheory.Conv.sumsAt_iff.1 (hT' _ hω _ ω.2.2.2.1)⟩
  · have h1 := (hch f).2
    rw [eχ, GlobalTheory.HolHom.valR_spMap _ _ _ hv'V] at h1
    simpa [dualMap] using h1
  · filter_upwards [(hch f).1] with ω hω
    exact ω.2.2.2.2.2 ω.2.2.2.2.1 i Vo f hω

end GlobalTheory.ArcLieCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcLieBasisExponentialCoordsHasSumStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_lieBasis_exponentialCoords_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U) (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ) (hn : M.n = g) (v' : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) → IsLieBasis v → (Matrix.of z).det ≠ 0 → (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ (Fin.cast hn.symm i)) → (∀ i, IsLieComb (A i) v (v' i)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → ∀ i, (∀ k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)) ∧ ∀ j, Wv (Fin.cast hg.symm i) j = ∑ k, (∑' m : ℕ, PowerSeries.coeff m (A i k) * eTwoPi w ^ m) * z k j := by
  first | exact @GlobalTheory.ArcLieCoord.lie_coords_hasSum | exact GlobalTheory.ArcLieCoord.lie_coords_hasSum | (intros; apply GlobalTheory.ArcLieCoord.lie_coords_hasSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantLieBasisAnalyticBasisArc
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantLieBasisAnalyticBasisArc
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ArcLieFrame

theorem exists_const_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ), (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) ∧ IsLieBasis v ∧ (Matrix.of z).det ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha
  have hG := GlobalTheory.SemiRigid.globalFns
  obtain ⟨g', e, v, -, hev, hb, hu, -⟩ := GlobalTheory.ConstLie.exists_const_basis hG E H Dw l Xo c V V.subtype Y ℂ
    (σ.comp V.subtype) a χ W
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.ExpTan.anVec_bijective hG E H Dw l Xo c σ V V.subtype Y a χ W g ty Fu Ha
  choose z hz using fun i => (h1 (e i) (hev i).1).exists
  have hli : LinearIndependent ℂ z := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf
    obtain ⟨ν, hν⟩ := GlobalTheory.ConstLie.exists_gtComb cf e
    obtain ⟨ν₀, hν₀⟩ := GlobalTheory.ConstLie.exists_gtComb (0 : Fin g' → ℂ) e
    have a1 := (h4 g' cf e z ν hz).1 hν
    have a0 := (h4 g' 0 e z ν₀ hz).1 hν₀
    rw [hcf] at a1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at a0
    obtain rfl : ν = ν₀ := (h2 0).unique a1 a0
    have ht := h3 _ _ a1
    have := (hu ν ht).unique hν hν₀
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range z) := by
    intro z₀ _
    rw [Submodule.mem_span_range_iff_exists_fun]
    obtain ⟨ν, hν, -⟩ := h2 z₀
    obtain ⟨cf, hcf, -⟩ := hu ν (h3 _ _ hν)
    exact ⟨cf, (h1 ν (h3 _ _ hν)).unique ((h4 g' cf e z ν hz).1 hcf) hν⟩
  have hg : g' = g := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    simpa using this.symm
  subst hg
  refine ⟨e, v, z, fun k => ⟨(hev k).2, hz k⟩, hb, ?_⟩
  have hu' : IsUnit (Matrix.of z) := (Matrix.linearIndependent_rows_iff_isUnit).1 (by simpa using hli)
  exact (Matrix.isUnit_iff_isUnit_det _).1 hu' |>.ne_zero

end GlobalTheory.ArcLieFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantLieBasisAnalyticBasisArcStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_lieBasis_analytic_basis_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ), (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) ∧ IsLieBasis v ∧ (Matrix.of z).det ≠ 0 := by
  first | exact @GlobalTheory.ArcLieFrame.exists_const_frame | exact GlobalTheory.ArcLieFrame.exists_const_frame | (intros; apply GlobalTheory.ArcLieFrame.exists_const_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBoundedConvergentPowerSeriesMatrixETwoPi
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBoundedConvergentPowerSeriesMatrixETwoPi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Filter Topology

theorem tendsto_tsum_coeff_mul_pow_zero (a : ℕ → ℂ) (q₀ : ℂ) (hq₀ : q₀ ≠ 0)
    (hs : Summable (fun m : ℕ => a m * q₀ ^ m)) :
    Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0) (𝓝 (a 0)) := by
  have hlim : Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0)
      (𝓝 (∑' m : ℕ, if m = 0 then a 0 else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖a m * q₀ ^ m‖) hs.norm ?_ ?_
    · intro m
      have hc : Continuous (fun q : ℂ => a m * q ^ m) := by fun_prop
      have h := hc.tendsto 0
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa using h
      · have h0 : a m * (0 : ℂ) ^ m = 0 := by simp [hm.ne']
        rw [h0] at h
        simpa [hm.ne'] using h
    · have hpos : 0 < ‖q₀‖ := norm_pos_iff.mpr hq₀
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hpos] with q hq m
      have hq' : ‖q‖ ≤ ‖q₀‖ := by
        have : ‖q‖ < ‖q₀‖ := by simpa using hq
        exact this.le
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      gcongr
  simpa using hlim

theorem det_bounded_eTwoPi : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ),
    IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) →
    ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im →
      C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧
      ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  intro g A w₀ hdet hsum
  have hq₀ : eTwoPi w₀ ≠ 0 := Complex.exp_ne_zero _
  set d₀ : ℂ := (A.map (PowerSeries.constantCoeff (R := ℂ))).det with hd₀
  have hd₀eq : d₀ = PowerSeries.constantCoeff (R := ℂ) A.det := by
    rw [RingHom.map_det]
    rfl
  have hd₀ne : d₀ ≠ 0 := by
    rw [hd₀eq]
    exact (hdet.map (PowerSeries.constantCoeff (R := ℂ))).ne_zero
  have hmat : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ)) (𝓝 0) (𝓝 (A.map (PowerSeries.constantCoeff (R := ℂ)))) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    have h := tendsto_tsum_coeff_mul_pow_zero (fun m => PowerSeries.coeff m (A i j))
      (eTwoPi w₀) hq₀ (hsum i j)
    simpa using h
  have hdetlim : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ).det) (𝓝 0) (𝓝 d₀) :=
    ((continuous_id.matrix_det).tendsto _).comp hmat
  have hdpos : 0 < ‖d₀‖ := norm_pos_iff.mpr hd₀ne
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hdetlim (‖d₀‖ / 2) (by positivity))
  refine ⟨-Real.log ε / (2 * Real.pi), 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1, by positivity, ?_⟩
  intro w hw
  have hpi : 0 < 2 * Real.pi := by positivity
  have hnorm : ‖eTwoPi w‖ < ε := by
    have hn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
      rw [eTwoPi, Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    rw [hn, ← Real.lt_log_iff_exp_lt hε]
    rw [div_lt_iff₀ hpi] at hw
    linarith
  have hclose := hball (y := eTwoPi w) (by simpa using hnorm)
  rw [dist_eq_norm] at hclose
  set D : ℂ := (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m :
    Matrix (Fin g) (Fin g) ℂ).det with hD
  have hlow : ‖d₀‖ / 2 ≤ ‖D‖ := by
    have := norm_sub_norm_le d₀ D
    rw [norm_sub_rev] at this
    linarith
  have hup : ‖D‖ ≤ 3 * ‖d₀‖ / 2 := by
    have := norm_sub_norm_le D d₀
    linarith
  have h2 : 0 < 2 / ‖d₀‖ := by positivity
  constructor
  · refine le_trans ?_ hlow
    have hC : 2 / ‖d₀‖ ≤ 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1 := by
      have : 0 ≤ 3 * ‖d₀‖ / 2 := by positivity
      linarith
    have := inv_anti₀ h2 hC
    rwa [inv_div] at this
  · have : 0 < 2 / ‖d₀‖ := h2
    linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBoundedConvergentPowerSeriesMatrixETwoPiStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ), IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) → ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im → C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  first | exact @GlobalTheory.det_bounded_eTwoPi | exact GlobalTheory.det_bounded_eTwoPi | (intros; apply GlobalTheory.det_bounded_eTwoPi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieBasisExpCoordsDetBoundedAlongArc
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

theorem exists_chartLie_along : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U), ∃ v' : Fin M.n → (epsR (PowerSeries ℂ) ⟶ W.t.G), (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ i) ∧ IsLieBasis v' := by
  intro E _ _ _ H Dw l Xo c σ V Y a χ W M hM
  have cast : ∀ (p q : Sp (PowerSeries ℂ) ⟶ Y.X) (_ : p = q) (n : SABMap W.t Y.t p),
      ∃ n' : SABMap W.t Y.t q, n'.φ = n.φ := by
    rintro p q rfl n
    exact ⟨n, rfl⟩
  obtain ⟨m', hm'⟩ := cast _ (spMap (ev χ M.U hM) ≫ M.hU.fromSpec) (GlobalTheory.FlagMod.spMap_ev χ M.hU hM).symm W.m
  obtain ⟨v', hv', hb, -⟩ := M.lie (PowerSeries ℂ) (ev χ M.U hM) W.t m'
  refine ⟨v', fun j => ?_, hb⟩
  rw [← hm', hv' j]
  have e : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev χ M.U hM) = dualMap (ev χ M.U hM) := by
    ext x <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, dualMap]
  rw [e]

theorem exists_lieComb_matrix : ∀ (R : Type) [CommRing R] [Nontrivial R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n n' : ℕ) (v : Fin n → (epsR R ⟶ G)) (v' : Fin n' → (epsR R ⟶ G)), IsLieBasis v → IsLieBasis v' → ∃ h : n' = n, ∃ A : Matrix (Fin n) (Fin n) R, IsUnit A.det ∧ ∀ i, IsLieComb (A i) v (v' (Fin.cast h.symm i)) := by
  intro R _ _ G _ _ O _ act n n' v v' hv hv'
  let b := GlobalTheory.Serre.Lie.basis act hv
  let b' := GlobalTheory.Serre.Lie.basis act hv'
  have h : n' = n := by simpa using Fintype.card_congr (b'.indexEquiv b)
  subst h
  refine ⟨rfl, (b.toMatrix b').transpose, ?_, fun i => ?_⟩
  · rw [Matrix.det_transpose]
    refine IsUnit.of_mul_eq_one (b'.toMatrix b).det ?_
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  · have hv_eq : v = fun k => (b k).hom := funext fun k => (GlobalTheory.Serre.Lie.hom_basis (a := act) hv k).symm
    rw [Fin.cast_eq_self, ← GlobalTheory.Serre.Lie.hom_basis (a := act) hv' i, hv_eq, GlobalTheory.Serre.Lie.isLieComb_iff]
    congr 1
    conv_lhs => rw [← b.sum_repr (b' i)]
    rfl

theorem lieCoord_det_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → C⁻¹ ≤ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ∧ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M h1 h2 h3 h4 h5 h6
  obtain ⟨e, v, z, hev, hv, hz⟩ := GlobalTheory.T.exists_constant_lieBasis_analytic_basis_arc E H Dw l Xo c σ V Y a χ W g ty Fu Ha
  obtain ⟨v', hv'1, hv'2⟩ := exists_chartLie_along E H Dw l Xo c σ V Y a χ W M h6
  obtain ⟨hn, A, hA, hAc⟩ := exists_lieComb_matrix (PowerSeries ℂ) W.t.G (𝓞 E) W.t.act g M.n v v' hv hv'2
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.T.arc_lieBasis_exponentialCoords_hasSum E H Dw l Xo c σ V Y a χ W g ty Fu Ha M h6 e v z hn (fun i => v' (Fin.cast hn.symm i)) A
    h1 h2 h3 h4 h5 hev hv hz (fun i => hv'1 _) hAc
  by_cases hex : ∃ w : ℂ, T₀ < w.im ∧ ∀ i k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)
  swap
  · refine ⟨T₀, 1, one_pos, ?_⟩
    intro w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf
    exact (hex ⟨w, hw, fun i k => (hT₀ w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf i).1 k⟩).elim
  obtain ⟨w₀, -, hs⟩ := hex
  obtain ⟨T', C, hC, hb⟩ := GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi g A w₀ hA hs
  have hd : 0 < ‖(Matrix.of z).det‖ := norm_pos_iff.2 hz
  refine ⟨max T₀ T', C * (‖(Matrix.of z).det‖ + ‖(Matrix.of z).det‖⁻¹), by positivity, ?_⟩
  intro w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf
  have hM : (Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j) =
      (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m) * Matrix.of z := by
    ext i j
    rw [Matrix.of_apply, ((hT₀ w (lt_of_le_of_lt (le_max_left _ _) hw) yF e1 e2 hz' x φ hk hg u Wv hf hdf i).2 j),
      Matrix.mul_apply]
    rfl
  rw [hM, Matrix.det_mul, norm_mul]
  obtain ⟨b1, b2⟩ := hb w (lt_of_le_of_lt (le_max_right _ _) hw)
  set d := ‖(Matrix.of z).det‖
  set t := ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖
  constructor
  · rw [mul_inv, ← div_eq_mul_inv]
    calc C⁻¹ / (d + d⁻¹) ≤ C⁻¹ * d := by
          rw [div_le_iff₀ (by positivity)]
          have : 1 ≤ d * (d + d⁻¹) := by rw [mul_add, mul_inv_cancel₀ hd.ne']; nlinarith
          nlinarith [inv_pos.2 hC]
      _ ≤ t * d := mul_le_mul_of_nonneg_right b1 hd.le
  · calc t * d ≤ C * d := mul_le_mul_of_nonneg_right b2 hd.le
      _ ≤ C * (d + d⁻¹) := by nlinarith [inv_pos.2 hd]

end GlobalTheory.ArcNormal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieBasisExpCoordsDetBoundedAlongArcStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieBasis_expCoords_det_bounded_along_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → C⁻¹ ≤ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ∧ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ≤ C := by
  first | exact @GlobalTheory.ArcNormal.lieCoord_det_bounded | exact GlobalTheory.ArcNormal.lieCoord_det_bounded | (intros; apply GlobalTheory.ArcNormal.lieCoord_det_bounded <;> assumption)
end
