module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubF
open GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.MBLow.Cl

def cubF {B : NumB ℂ} {g : ℕ} (d : AB B g) (x y z : Fin g → ℂ) : ℂ :=
  (B.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) /
    (d.fr (x + y + z) * d.fr x * d.fr y * d.fr z)

end GlobalTheory.MBLow.Cl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCubeAbelianPointThetaFaceEqPartialSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def pt3 (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) : Sp ℂ ⟶ (G3 D.P.A).left :=
  (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left

def wI (x y z : Fin g → ℂ) (I : thK) : Fin g → ℂ := ∑ a ∈ I.down, ![x, y, z] a

abbrev cubW (D : DegPre R) (j : thK → D.P.L.ι) : (G3 D.P.A).left.Opens :=
  LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j

theorem psum_eA (ν : NumOf D ℂ N) (d : AB N.toNumB g) {n : ℕ} (w : Fin n → Fin g → ℂ) (I : Finset (Fin n)) :
    psum D.P.A (fun k => ν.eA (d.ex (w k))) I = ν.eA (d.ex (∑ i ∈ I, w i)) := by
  have e0 : ν.eA (d.ex 0) = 1 := by
    have h := d.ex_add 0 0
    rw [add_zero] at h
    have h1 : d.ex 0 = 1 := left_eq_mul.mp h
    rw [h1, map_one]
  have hl : ∀ l : List (Fin n),
      l.foldr (fun k acc => padd D.P.A (ν.eA (d.ex (w k))) acc) (pzero D.P.A _) = ν.eA (d.ex (l.map w).sum) := by
    intro l
    induction l with
    | nil =>
      rw [List.foldr_nil, List.map_nil, List.sum_nil, e0, CategoryTheory.Hom.one_def]
      rfl
    | cons k l ih =>
      rw [List.foldr_cons, ih, List.map_cons, List.sum_cons, d.ex_add, map_mul, padd, CategoryTheory.Hom.mul_def]
  have hI : ((List.finRange n).filter (· ∈ I)).toFinset = I := by
    ext i
    simp
  unfold psum
  rw [hl, ← List.sum_toFinset w ((List.nodup_finRange n).filter _), hI]

theorem complexCubeAbelianPoint_thetaFace_eq_partialSum (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK) :
    pt3 ν d x y z ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (wI x y z I))).left := by
  have e := psum_hom (preHom (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))))) (x3 D.P.A) I.down
  have e' : psum D.P.A (fun i => preHom (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))) (x3 D.P.A i))
      I.down = psum D.P.A (fun k => ν.eA (d.ex (![x, y, z] k))) I.down :=
    congrArg (fun q => psum D.P.A q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])
  rw [e', psum_eA] at e
  rw [pt3, thφ, ← Over.comp_left]
  exact congrArg (fun q => q.left) e

end GlobalTheory.MBLow.Cl.CubHol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesEntire
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesChartGauge
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesChartGauge
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

section Val
variable {F : Type} [Field F] {X : Scheme.{0}}

theorem valF_eq_hom (x : Sp F ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valF x U f = ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (x.appLE U ⊤ h).hom) f := by
  unfold valF
  rw [dite_eq_left h]
  rfl

theorem valF_zpow (x : Sp F ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valF x U (u ^ n).val = valF x U u.val ^ n := by
  rw [valF_eq_hom x h, valF_eq_hom x h]
  have e := congrArg Units.val
    (map_zpow (Units.map ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (x.appLE U ⊤ h).hom).toMonoidHom) u n)
  rw [Units.val_zpow_eq_zpow_val] at e
  exact e

theorem valF_prod {K : Type} [Fintype K] (x : Sp F ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : K → Γ(X, U)ˣ) :
    valF x U (∏ k, u k).val = ∏ k, valF x U (u k).val := by
  simp only [valF_eq_hom x h, Units.coe_prod, map_prod]

end Val

theorem cubF_mul_prod_fr {B : NumB ℂ} {g : ℕ} (d : AB B g) (x y z : Fin g → ℂ) :
    cubF d x y z * ∏ I : thK, ((d.fr (wI x y z I) : ℂˣ) : ℂ) ^ thε I = (B.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) := by
  have p := GlobalTheory.FrameValue.prod_thK (fun s : Finset (Fin 3) => ((d.fr (∑ a ∈ s, ![x, y, z] a) : ℂˣ) : ℂ))
  simp only [GlobalTheory.FrameValue.sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, d.fr_zero, Units.val_one] at p
  simp only [wI]
  rw [p, cubF, inv_one, _root_.mul_one]
  have h1 := (d.fr (x + y + z)).ne_zero
  have h2 := (d.fr (x + y)).ne_zero
  have h3 := (d.fr (x + z)).ne_zero
  have h4 := (d.fr (y + z)).ne_zero
  have h5 := (d.fr x).ne_zero
  have h6 := (d.fr y).ne_zero
  have h7 := (d.fr z).ne_zero
  field_simp

theorem cubF_mul_prod_frG {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y z : Fin g → ℂ) (j : thK → D.P.L.ι)
    (hj : ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j) :
    cubF d x y z * ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I =
      valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val := by
  set r := pt3 ν d x y z with hr
  set φ := thφ D.P.A (x3 D.P.A) with hφ
  set J' : thK → D.P.L.ι := fun I => ν.J (r ≫ φ I) with hJ'
  have hθ : (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) = valF r (cubW D J') (D.cub.t.s J').val := ν.θ_eq _ _ _
  have hgood : ⊤ ≤ r ⁻¹ᵁ cubW D J' := fun p _ => Set.mem_iInter.2 fun I => ν.good (r ≫ φ I) (x := p) trivial
  have hboth := GlobalTheory.ZH.TorsFrame.le_preimage_inf r hgood hj
  have hg := D.cub.isGen J' j
  have e2 : valF r (cubW D J') (D.cub.t.s J').val =
      valF r (cubW D J' ⊓ cubW D j) ((Theta D.P.A D.P.L).g J' j).val * valF r (cubW D j) (D.cub.t.s j).val :=
    (GlobalTheory.ZH.TorsFrame.valF_res r (inf_le_left : cubW D J' ⊓ cubW D j ≤ cubW D J') hboth (D.cub.t.s J')).symm.trans
      ((congrArg (fun u => valF r (cubW D J' ⊓ cubW D j) (Units.val u)) hg).trans
        ((GlobalTheory.ZH.TorsFrame.valF_mul r hboth _ _).trans
          (congrArg (_ * ·) (GlobalTheory.ZH.TorsFrame.valF_res r inf_le_right hboth _))))
  have e3 : valF r (cubW D J' ⊓ cubW D j) ((Theta D.P.A D.P.L).g J' j).val =
      ∏ I : thK, valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val ^ thε I := by
    refine (valF_prod r hboth _).trans (Finset.prod_congr rfl fun I _ => ?_)
    refine (valF_zpow r hboth _ _).trans ?_
    congr 1
    exact (GlobalTheory.ZH.TorsFrame.valF_res r _ hboth _).trans (GlobalTheory.ZH.TorsFrame.valF_pullU r (φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)))
  have hc : ∀ I : thK, valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val *
      geo.frG (j I) (wI x y z I) = d.fr (wI x y z I) * ν.rg := by
    intro I
    have hin : ⊤ ≤ (r ≫ φ I) ⁻¹ᵁ (D.P.L.U (ν.J (r ≫ φ I)) ⊓ D.P.L.U (j I)) := fun p _ =>
      ⟨ν.good (r ≫ φ I) (x := p) trivial, Set.mem_iInter.1 (hj (x := p) trivial) I⟩
    have hp : r ≫ φ I = (ν.eA (d.ex (wI x y z I))).left := complexCubeAbelianPoint_thetaFace_eq_partialSum ν d x y z I
    show valF (r ≫ φ I) (D.P.L.U (ν.J (r ≫ φ I)) ⊓ D.P.L.U (j I)) (D.P.L.g (ν.J (r ≫ φ I)) (j I)).val *
      geo.frG (j I) (wI x y z I) = d.fr (wI x y z I) * ν.rg
    rw [hp] at hin ⊢
    rw [geo.fr_eq]
    exact (geo.fr_compat _ _ _ hin).symm
  have hrg : ν.rg ≠ 0 := GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν
  set a : thK → ℂ := fun I => valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val with ha_def
  set fG : thK → ℂ := fun I => geo.frG (j I) (wI x y z I) with hfG
  set V := valF r (cubW D j) (D.cub.t.s j).val with hV
  set θ : ℂ := (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) with hθd
  have hθ' : θ = (∏ I : thK, a I ^ thε I) * V := by rw [hθ, e2, e3]
  have ha : ∀ I, a I ≠ 0 := fun I h0 => by
    have := hc I
    rw [show valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val = a I from rfl, h0,
      zero_mul] at this
    exact mul_ne_zero (Units.ne_zero _) hrg this.symm
  have hPa : (∏ I : thK, a I ^ thε I) ≠ 0 := Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (ha I)
  have hrg1 : (∏ _I : thK, ν.rg ^ thε _I) = 1 := by
    have p := GlobalTheory.FrameValue.prod_thK (fun _ : Finset (Fin 3) => ν.rg)
    refine p.trans ?_
    field_simp
  have hP : (∏ I : thK, a I ^ thε I) * (∏ I : thK, fG I ^ thε I) =
      ∏ I : thK, ((d.fr (wI x y z I) : ℂˣ) : ℂ) ^ thε I := by
    rw [← Finset.prod_mul_distrib]
    have : ∀ I : thK, a I ^ thε I * fG I ^ thε I = ((d.fr (wI x y z I) : ℂˣ) : ℂ) ^ thε I * ν.rg ^ thε I :=
      fun I => by rw [← mul_zpow, ← mul_zpow]; exact congrArg (· ^ thε I) (hc I)
    rw [Finset.prod_congr rfl fun I _ => this I, Finset.prod_mul_distrib, hrg1, _root_.mul_one]
  have hcub := cubF_mul_prod_fr d x y z
  show cubF d x y z * ∏ I : thK, fG I ^ thε I = V
  refine mul_left_cancel₀ hPa ?_
  linear_combination cubF d x y z * hP + hcub + hθ'

end GlobalTheory.MBLow.Cl.CubHol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesChartGaugeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeValueTimesThetaFrames_chartGauge : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y z : Fin g → ℂ) (j : thK → D.P.L.ι), ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j → cubF d x y z * ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I = valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG | exact GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG | (intros; apply GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFramePartialSumDiffNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFramePartialSumDiffNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem wI_mem_chart (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (j : thK → D.P.L.ι) (I : thK)
    (hz : ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j) :
    ⊤ ≤ (ν.eA (d.ex (wI x y z I))).left ⁻¹ᵁ D.P.L.U (j I) := by
  have h1 : ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ (thφ D.P.A (x3 D.P.A) I ⁻¹ᵁ D.P.L.U (j I)) :=
    fun q hq => LB.wchart_le D.P.L (thφ D.P.A (x3 D.P.A)) j I (hz hq)
  rw [← complexCubeAbelianPoint_thetaFace_eq_partialSum ν d x y z I]
  exact fun q hq => h1 hq

theorem differentiable_wI (x y : Fin g → ℂ) (I : thK) : Differentiable ℂ (fun z => wI x y z I) := by
  unfold wI
  refine Differentiable.fun_sum fun a _ => ?_
  fin_cases a
  · exact differentiable_const _
  · exact differentiable_const _
  · exact differentiable_id

theorem frG_wI_hol_ne (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y : Fin g → ℂ)
    (j : thK → D.P.L.ι) (I : thK) :
    DifferentiableOn ℂ (fun z => geo.frG (j I) (wI x y z I)) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧
      ∀ z, ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j → geo.frG (j I) (wI x y z I) ≠ 0 := by
  refine ⟨(geo.fr_hol (j I)).comp (differentiable_wI x y I).differentiableOn
    fun z hz => wI_mem_chart ν d x y z j I hz, fun z hz => ?_⟩
  set w := wI x y z I
  have hj := wI_mem_chart ν d x y z j I hz
  have hp := ν.good (ν.eA (d.ex w)).left
  have hpj : ⊤ ≤ (ν.eA (d.ex w)).left ⁻¹ᵁ (D.P.L.U (ν.J (ν.eA (d.ex w)).left) ⊓ D.P.L.U (j I)) :=
    fun q hq => ⟨hp hq, hj hq⟩
  have hc := geo.fr_compat _ (j I) w hpj
  have hne : geo.frG (ν.J (ν.eA (d.ex w)).left) w ≠ 0 := by
    rw [← geo.fr_eq w]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  rw [hc] at hne
  exact right_ne_zero_of_mul hne

end GlobalTheory.MBLow.Cl.CubHol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFramePartialSumDiffNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y : Fin g → ℂ) (j : thK → D.P.L.ι) (I : thK), DifferentiableOn ℂ (fun z => geo.frG (j I) (wI x y z I)) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ ∀ z, ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j → geo.frG (j I) (wI x y z I) ≠ 0 := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.frG_wI_hol_ne | exact GlobalTheory.MBLow.Cl.CubHol.frG_wI_hol_ne | (intros; apply GlobalTheory.MBLow.Cl.CubHol.frG_wI_hol_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeLocalUnitValueHolomorphicThird
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeLocalUnitValueHolomorphicThird
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def phiXY (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y : Fin g → ℂ) : (DegPre.BF D ℂ).left ⟶ (G3 D.P.A).left :=
  (lift (fst _ _ ≫ ν.eA (d.ex x)) (lift (fst _ _ ≫ ν.eA (d.ex y)) (snd _ _))).left

theorem ptB_phiXY (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) :
    ptB ν d z ≫ phiXY ν d x y = pt3 ν d x y z := by
  rw [ptB, phiXY, pt3, ← Over.comp_left, comp_lift, lift_fst_assoc, comp_lift, lift_fst_assoc, lift_snd,
    Category.id_comp, Category.id_comp]

theorem isOpen_and_differentiableOn_valF_pt3_cubW : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), Geo ν d → ∀ (x y : Fin g → ℂ) (j : thK → D.P.L.ι), IsOpen {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} := by
  intro R _ _ D _ N g ν d G x y j
  have hs : {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} = {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ (phiXY ν d x y ⁻¹ᵁ cubW D j)} := by
    ext z
    simp only [Set.mem_setOf_eq, ← ptB_phiXY ν d x y z, Scheme.Hom.comp_preimage]
  obtain ⟨ho, hd⟩ := G.hol (phiXY ν d x y ⁻¹ᵁ cubW D j)
    (((phiXY ν d x y).appLE (cubW D j) (phiXY ν d x y ⁻¹ᵁ cubW D j) le_rfl).hom (D.cub.t.s j).val)
  rw [hs]
  refine ⟨ho, hd.congr fun z hz => ?_⟩
  have e := UnitVal.valF_appLE' (x := ptB ν d z) (phiXY ν d x y) (cubW D j) le_rfl hz (D.cub.t.s j).val
  rw [ptB_phiXY] at e
  exact e.symm

end GlobalTheory.MBLow.Cl.CubHol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeLocalUnitValueHolomorphicThirdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeLocalUnit_value_holomorphic_third : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), Geo ν d → ∀ (x y : Fin g → ℂ) (j : thK → D.P.L.ι), IsOpen {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.isOpen_and_differentiableOn_valF_pt3_cubW | exact GlobalTheory.MBLow.Cl.CubHol.isOpen_and_differentiableOn_valF_pt3_cubW | (intros; apply GlobalTheory.MBLow.Cl.CubHol.isOpen_and_differentiableOn_valF_pt3_cubW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesEntire
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem cubF_differentiable (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y : Fin g → ℂ) :
    Differentiable ℂ (cubF d x y) := by
  intro z₀
  let j : thK → D.P.L.ι := fun I => ν.J (pt3 ν d x y z₀ ≫ thφ D.P.A (x3 D.P.A) I)
  let V : Set (Fin g → ℂ) := {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j}
  have hz₀ : z₀ ∈ V := fun w _ =>
    Good.mem (L := D.P.L) (z := w) (J := ν.J) (fun ψ => ν.good ψ trivial) (thφ D.P.A (x3 D.P.A)) (pt3 ν d x y z₀)
  obtain ⟨hV, hval⟩ := GlobalTheory.T.cubeLocalUnit_value_holomorphic_third ν d geo x y j
  have hP : ∀ z ∈ V, ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I ≠ 0 := fun z hz =>
    Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ ((GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero ν d geo x y j I).2 z hz)
  have hG : DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val *
      (∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I)⁻¹) V := by
    refine hval.mul (DifferentiableOn.inv ?_ hP)
    have e : (fun z => ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I) =
        ∏ I : thK, fun z => geo.frG (j I) (wI x y z I) ^ thε I := by
      ext z; rw [Finset.prod_apply]
    rw [e]
    refine Finset.prod_induction _ (fun f => DifferentiableOn ℂ f V) (fun f h hf hh => hf.mul hh)
      (differentiableOn_const 1) fun I _ => ?_
    exact (GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero ν d geo x y j I).1.zpow (Or.inl fun z hz => (GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero ν d geo x y j I).2 z hz)
  have heq : ∀ z ∈ V, cubF d x y z = valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val *
      (∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I)⁻¹ := fun z hz => by
    rw [← div_eq_mul_inv]
    exact (eq_div_iff (hP z hz)).2 (GlobalTheory.T.cubeValueTimesThetaFrames_chartGauge ν d geo x y z j hz)
  have hn : V ∈ nhds z₀ := hV.mem_nhds hz₀
  exact ((hG z₀ hz₀).differentiableAt hn).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem hn fun z hz => heq z hz)

theorem cubF_entire : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → ∀ x y : Fin g → ℂ, Differentiable ℂ (cubF d x y) := by
  intro R _ _ _ _ D _ _ _ N ν g d ⟨geo⟩ x y
  exact cubF_differentiable ν d geo x y

end GlobalTheory.MBLow.Cl.CubHol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesEntireStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeValueTimesThetaFrames_entire : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → ∀ x y : Fin g → ℂ, Differentiable ℂ (cubF d x y) := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.cubF_entire | exact GlobalTheory.MBLow.Cl.CubHol.cubF_entire | (intros; apply GlobalTheory.MBLow.Cl.CubHol.cubF_entire <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl

section Analytic

variable {B : NumB ℂ} {g : ℕ} (d : AB B g)

theorem ex_zero' : d.ex 0 = 1 := by
  have h := d.ex_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem autV_cube (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (x y z : Fin g → ℂ) :
    autV τ a b M N (x + y + z) * autV τ a b M N z = autV τ a b M N (x + z) * autV τ a b M N (y + z) := by
  simp only [autV, ← Complex.exp_add]
  congr 1
  simp only [dotProduct_add]
  ring

theorem autV_ne (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (w : Fin g → ℂ) :
    autV τ a b M N w ≠ 0 := Complex.exp_ne_zero _

theorem fr_shift (M N : Fin g → ℤ) (w : Fin g → ℂ) :
    (d.fr (w + perV d.τ M N) : ℂ) = d.fr w / autV d.τ d.a d.b M N w := by
  rw [d.fr_per M N w, mul_div_cancel_left₀ _ (autV_ne _ _ _ _ _ _)]

theorem cubF_per (x y : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    cubF d x y (z + perV d.τ M N) = cubF d x y z := by
  have hP : d.ex (perV d.τ M N) = 1 := (d.ker _).2 ⟨M, N, rfl⟩
  have e1 : x + (z + perV d.τ M N) = x + z + perV d.τ M N := by abel
  have e2 : y + (z + perV d.τ M N) = y + z + perV d.τ M N := by abel
  have e3 : x + y + (z + perV d.τ M N) = x + y + z + perV d.τ M N := by abel
  unfold cubF
  rw [d.ex_add, hP, _root_.mul_one, e1, e2, e3, fr_shift, fr_shift, fr_shift, fr_shift]
  have A := autV_cube d.τ d.a d.b M N x y z
  have h1 := autV_ne d.τ d.a d.b M N (x + z)
  have h2 := autV_ne d.τ d.a d.b M N (y + z)
  have h3 := autV_ne d.τ d.a d.b M N (x + y + z)
  have h4 := autV_ne d.τ d.a d.b M N z
  have u1 := (d.fr (x + y + z)).ne_zero
  have u2 := (d.fr x).ne_zero
  have u3 := (d.fr y).ne_zero
  have u4 := (d.fr z).ne_zero
  field_simp
  linear_combination A

end Analytic

section Bound

variable {B : NumB ℂ} {g : ℕ}

def rv (s : Fin g → ℝ) : Fin g → ℂ := fun i => (s i : ℂ)

theorem exists_real_coords (τ : Matrix (Fin g) (Fin g) ℂ) (hpos : (τ.map Complex.im).PosDef) (z : Fin g → ℂ) :
    ∃ s t : Fin g → ℝ, z = rv s + τ *ᵥ rv t := by
  have hT : IsUnit (τ.map Complex.im).det := isUnit_iff_ne_zero.2 hpos.det_pos.ne'
  set t : Fin g → ℝ := (τ.map Complex.im)⁻¹ *ᵥ (fun i => (z i).im) with ht
  refine ⟨(fun i => (z i).re) - (τ.map Complex.re) *ᵥ t, t, ?_⟩
  have hIm : (τ.map Complex.im) *ᵥ t = fun i => (z i).im := by
    rw [ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, Matrix.one_mulVec]
  funext i
  have hi := congrFun hIm i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hi
  apply Complex.ext
  · simp [rv, Matrix.mulVec, dotProduct, Complex.re_sum]
  · simp [rv, Matrix.mulVec, dotProduct, Complex.im_sum, hi]

theorem exists_reduce (d : AB B g) (z : Fin g → ℂ) : ∃ (M N : Fin g → ℤ) (s t : Fin g → ℝ),
    (∀ i, s i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧ z = rv s + d.τ *ᵥ rv t + perV d.τ M N := by
  obtain ⟨s, t, rfl⟩ := exists_real_coords d.τ d.pos z
  refine ⟨fun i => ⌊s i⌋, fun i => ⌊t i⌋, fun i => Int.fract (s i), fun i => Int.fract (t i),
    fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩
  have hs : rv s = rv (fun i => Int.fract (s i)) + cv (fun i => ⌊s i⌋) := by
    funext i; simp only [rv, cv, Pi.add_apply, Int.fract]; push_cast; ring
  have ht : rv t = rv (fun i => Int.fract (t i)) + cv (fun i => ⌊t i⌋) := by
    funext i; simp only [rv, cv, Pi.add_apply, Int.fract]; push_cast; ring
  rw [hs, ht, perV, Matrix.mulVec_add]
  abel

theorem bounded_of_per (d : AB B g) (F : (Fin g → ℂ) → ℂ) (hc : Continuous F)
    (hper : ∀ M N z, F (z + perV d.τ M N) = F z) : Bornology.IsBounded (Set.range F) := by
  have hrv : Continuous (fun s : Fin g → ℝ => rv s) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hΦ : Continuous (fun p : (Fin g → ℝ) × (Fin g → ℝ) => rv p.1 + d.τ *ᵥ rv p.2) :=
    (hrv.comp continuous_fst).add (continuous_const.matrix_mulVec (hrv.comp continuous_snd))
  have hK : IsCompact ((Set.univ.pi fun _ : Fin g => Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ.pi fun _ : Fin g => Set.Icc (0 : ℝ) 1)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.comp hΦ).continuousOn
  refine isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨M, N, s, t, hs, ht, rfl⟩ := exists_reduce d z
  rw [hper]
  exact hC (s, t) ⟨fun i _ => hs i, fun i _ => ht i⟩

theorem cub_of_diff (d : AB B g) (h : ∀ x y : Fin g → ℂ, Differentiable ℂ (cubF d x y)) : d.Cub := by
  intro x y z
  have hb := bounded_of_per d _ (h x y).continuous (cubF_per d x y)
  have e := (h x y).apply_eq_apply_of_bounded hb z 0
  have u1 := (d.fr (x + y + z)).ne_zero
  have u2 := (d.fr x).ne_zero
  have u3 := (d.fr y).ne_zero
  have u4 := (d.fr z).ne_zero
  have u5 := (d.fr (x + y)).ne_zero
  have h0 : cubF d x y 0 = 1 := by
    unfold cubF
    rw [ex_zero', B.cub.face₃, add_zero, add_zero, add_zero, d.fr_zero]
    simp only [Units.val_one, _root_.one_mul, _root_.mul_one]
    field_simp
  rw [h0] at e
  unfold cubF at e
  rw [div_eq_one_iff_eq (by simp [u1, u2, u3, u4])] at e
  apply Units.ext
  simpa only [Units.val_mul] using e

end Bound

theorem cub_of_geo : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → d.Cub := by
  intro R _ _ _ _ D hψ hτ _ N ν g d hG
  exact cub_of_diff d (GlobalTheory.T.cubeValueTimesThetaFrames_entire R D hψ hτ N ν g d hG)

end GlobalTheory.MBLow.Cl
