module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodEqTriangularOrthonormal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.LieCombBaseChange

variable {R R' : Type} [CommRing R] [CommRing R']

private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (k : B →+* C) : spMap k ≫ spMap g = spMap (k.comp g) := by
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_epsScale (f : R →+* R') (c : R) :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ spMap (epsScaleR c) =
      spMap (epsScaleR (f c)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
  rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [epsScaleR, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, mul_comm]

theorem dualMap_over (f : R →+* R') :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  simp only [epsR, Over.mk_hom]
  rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsScale_over (c : R) : spMap (epsScaleR c) ≫ (epsR R).hom = (epsR R).hom := by
  simp only [epsR, Over.mk_hom]
  rw [spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem prod_left_comp {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (d : T'.left ⟶ T.left)
    (hd : d ≫ T.hom = T'.hom ≫ f) {n : ℕ} (u : Fin n → (T ⟶ G)) (u' : Fin n → (T' ⟶ G'))
    (hu : ∀ i, (u' i).left ≫ φ = d ≫ (u i).left) :
    (List.ofFn u').prod.left ≫ φ = d ≫ (List.ofFn u).prod.left := by
  have hd' : d ≫ T.hom = (Over.mk (T'.hom ≫ f)).hom := by simpa using hd
  have hsq : φ ≫ G.hom = G'.hom ≫ f := h.1.w

  have hone : (1 : T' ⟶ G').left ≫ φ = (1 : Over.mk (T'.hom ≫ f) ⟶ G).left := by
    let x₀ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk ((1 : T' ⟶ G').left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, hsq]
      rw [← Category.assoc, Over.w])
    have hx : x₀ * x₀ = x₀ := by
      apply Over.OverMorphism.ext
      rw [h.2 T' 1 1 x₀ x₀ rfl rfl, _root_.mul_one]
      rfl
    have h1 : x₀ = 1 := by simpa using hx
    rw [← h1]
    rfl

  have key : ∀ (m : ℕ) (u : Fin m → (T ⟶ G)) (u' : Fin m → (T' ⟶ G')),
      (∀ i, (u' i).left ≫ φ = d ≫ (u i).left) →
        (List.ofFn u').prod.left ≫ φ = ((Over.homMk d hd' : Over.mk (T'.hom ≫ f) ⟶ T) ≫ (List.ofFn u).prod).left := by
    intro m
    induction m with
    | zero =>
      intro u u' _
      simp only [List.ofFn_zero, List.prod_nil, MonObj.comp_one, hone]
    | succ m ih =>
      intro u u' hu
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul]
      refine (h.2 T' _ _ _ _ ?_ ?_).symm
      · rw [Over.comp_left]
        exact (hu 0).symm
      · exact (ih _ _ fun i => hu i.succ).symm
  have := key n u u' hu
  rw [Over.comp_left] at this
  exact this

end GlobalTheory.LieCombBaseChange

namespace GlobalTheory

open LieCombBaseChange

theorem lieComb_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap f) φ → ∀ (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) (a : Fin n → R) (v' : Fin n → (epsR R' ⟶ G')) (w' : epsR R' ⟶ G'), (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (v j).left) → IsLieComb a v w → (w'.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ↔ IsLieComb (fun i => f (a i)) v' w') := by
  intro R R' _ _ f G _ G' _ φ h n v w a v' w' hv hc
  obtain ⟨u, hu, rfl⟩ := hc

  have hcomp : ∀ i, (spMap (epsScaleR (f (a i))) ≫ (v' i).left) ≫ φ =
      spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (u i).left := by
    intro i
    rw [Category.assoc, hv i, hu i, ← Category.assoc, ← Category.assoc,
      LieCombBaseChange.dualMap_epsScale]
  have hprod : ∀ u'' : Fin n → (epsR R' ⟶ G'),
      (∀ i, (u'' i).left = spMap (epsScaleR (f (a i))) ≫ (v' i).left) →
        (List.ofFn u'').prod.left ≫ φ =
          spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (List.ofFn u).prod.left := fun u'' hu'' =>
    LieCombBaseChange.prod_left_comp h _ (LieCombBaseChange.dualMap_over f) u u''
      (fun i => by rw [hu'' i]; exact hcomp i)
  constructor
  · intro hw
    let u' : Fin n → (epsR R' ⟶ G') := fun i =>
      Over.homMk (spMap (epsScaleR (f (a i))) ≫ (v' i).left) (by
        rw [Category.assoc, Over.w]
        exact LieCombBaseChange.epsScale_over _)
    refine ⟨u', fun i => rfl, ?_⟩

    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hw, hprod u' fun i => rfl]
    · rw [Over.w w', Over.w]
  · rintro ⟨u'', hu'', rfl⟩
    exact hprod u'' hu''

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
noncomputable section

namespace GlobalTheory.FrameNorm.UnitFr

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hermC_mul_left {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) (α : ℂ) :
    hermC τ G (fun k => u k * α) v = α * hermC τ G u v := by
  unfold hermC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hermC_mul_right {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) (α : ℂ) :
    hermC τ G u (fun k => v k * α) = (starRingEnd ℂ) α * hermC τ G u v := by
  unfold hermC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul]
  ring

theorem col_mul_diag {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (β : Fin r → ℝ) (c : Fin r) :
    col (A * Matrix.diagonal fun a => (β a : ℂ)) c = fun k => col A c k * (β c : ℂ) := by
  funext k
  simp [col, Matrix.mul_diagonal]

theorem gram_mul_diag {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (A : Matrix (Fin r) (Fin r) ℂ)
    (β : Fin r → ℝ) :
    gram τ G (A * Matrix.diagonal fun a => (β a : ℂ)) =
      Matrix.diagonal (fun a => (β a : ℂ)) * gram τ G A * Matrix.diagonal (fun a => (β a : ℂ)) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [gram, Matrix.of_apply, col_mul_diag, hermC_mul_left, hermC_mul_right, Complex.conj_ofReal]
  ring

theorem lminor_diag {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (β : Fin r → ℂ) (i : Fin (r + 1)) :
    lminor (Matrix.diagonal β * M * Matrix.diagonal β) i =
      (∏ a : Fin i, β (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) ^ 2 * lminor M i := by
  unfold lminor
  have e : (Matrix.diagonal β * M * Matrix.diagonal β).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) =
      Matrix.diagonal (fun a => β (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) *
        M.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt)) *
        Matrix.diagonal (fun a => β (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) := by
    ext a b
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring

variable {r : ℕ} (X : Data E r)

def tq (x : Frame X.Ψ r) (τ : X.Ψ) (a : Fin r) : ℝ := ‖dmin X.Gm x τ a.succ / dmin X.Gm x τ a.castSucc‖

def bt (x : Frame X.Ψ r) (τ : X.Ψ) (a : Fin r) : ℝ := tq X x τ a ^ (-(1 : ℝ) / 2)

def unitB (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => Matrix.diagonal fun a => ((bt X x τ a : ℝ) : ℂ)

def unitF (x : Frame X.Ψ r) : Frame X.Ψ r := rmul x (unitB X x)

theorem mat_unitF (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (unitF X x) τ = mat x τ * Matrix.diagonal (fun a => ((bt X x τ a : ℝ) : ℂ)) := rfl

theorem dmin_unitF (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (unitF X x) τ i =
      (((∏ a : Fin i, bt X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) ^ 2 : ℝ) : ℂ) * dmin X.Gm x τ i := by
  unfold dmin
  rw [mat_unitF, gram_mul_diag, lminor_diag]
  push_cast
  rfl

variable {X}

theorem dmin_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm x τ i ≠ 0 := by
  intro h
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have := (hx' τ).2 i
  rw [h, Complex.zero_re, mul_zero] at this
  exact lt_irrefl _ this

theorem tq_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r) : 0 < tq X x τ a :=
  norm_pos_iff.2 (div_ne_zero (dmin_ne hx τ _) (dmin_ne hx τ _))

theorem bt_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r) : 0 < bt X x τ a :=
  Real.rpow_pos_of_pos (tq_pos hx τ a) _

theorem bt_sq {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r) :
    bt X x τ a ^ 2 = (tq X x τ a)⁻¹ := by
  unfold bt
  rw [← Real.rpow_natCast, ← Real.rpow_mul (tq_pos hx τ a).le]
  norm_num
  exact Real.rpow_neg_one _

def gN (x : Frame X.Ψ r) (τ : X.Ψ) (m : ℕ) : ℝ := if h : m < r + 1 then ‖dmin X.Gm x τ ⟨m, h⟩‖ else 1

theorem gN_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (m : ℕ) : gN x τ m ≠ 0 := by
  unfold gN
  split_ifs with h
  · exact norm_ne_zero_iff.2 (dmin_ne hx τ _)
  · exact one_ne_zero

theorem gN_zero (x : Frame X.Ψ r) (τ : X.Ψ) : gN x τ 0 = 1 := by
  unfold gN
  rw [dite_eq_left (Nat.succ_pos r)]
  have : dmin X.Gm x τ ⟨0, Nat.succ_pos r⟩ = 1 := Matrix.det_fin_zero
  rw [this, norm_one]

theorem prod_gN {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (n : ℕ) :
    ∏ m ∈ Finset.range n, gN x τ m / gN x τ (m + 1) = gN x τ 0 / gN x τ n := by
  induction n with
  | zero => simp [div_self (gN_ne hx τ 0)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [gN_ne hx τ n, gN_ne hx τ (n + 1), gN_ne hx τ 0]

theorem tq_castLE {x : Frame X.Ψ r} (τ : X.Ψ) {i : ℕ} (hi : i ≤ r) (a : Fin i) :
    tq X x τ (Fin.castLE hi a) = gN x τ (a + 1) / gN x τ a := by
  unfold tq gN
  rw [dite_eq_left (by omega), dite_eq_left (by omega), norm_div]
  rfl

theorem norm_dmin_unitF {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm (unitF X x) τ i‖ = 1 := by
  rw [dmin_unitF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Finset.prod_pow]
  have h1 : ∀ a : Fin i, bt X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) a) ^ 2 =
      gN x τ (a : ℕ) / gN x τ ((a : ℕ) + 1) := by
    intro a
    rw [bt_sq hx, tq_castLE, inv_div]
  simp_rw [h1]
  rw [Fin.prod_univ_eq_prod_range (fun m => gN x τ m / gN x τ (m + 1)), prod_gN hx, gN_zero]
  have h2 : gN x τ i = ‖dmin X.Gm x τ i‖ := by
    unfold gN
    rw [dite_eq_left i.isLt]
  rw [h2, div_mul_cancel₀ _ (norm_ne_zero_iff.2 (dmin_ne hx τ i))]

theorem unitB_mem (x : Frame X.Ψ r) (hx : x ∈ X.dom) : unitB X x ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show (Matrix.diagonal fun a => ((bt X x τ a : ℝ) : ℂ)).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (bt_pos hx τ a).ne'
  · show Matrix.diagonal (fun a => ((bt X x τ a : ℝ) : ℂ)) a c = 0
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hca)

theorem unitF_mem (x : Frame X.Ψ r) (hx : x ∈ X.dom) : unitF X x ∈ X.dom := by
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_unitF, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (hx' τ).1
      (Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (bt_pos hx τ a).ne')
  · rw [dmin_unitF, Complex.re_ofReal_mul]
    have hs : 0 < (∏ a : Fin i, bt X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) ^ 2 :=
      pow_pos (Finset.prod_pos fun a _ => bt_pos hx τ _) 2
    have := (hx' τ).2 i
    nlinarith

theorem pnorm_unitF (x : Frame X.Ψ r) (hx : x ∈ X.dom) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hB : ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) :
    X.pnorm la P (unitF X x) = X.pnorm la P x := by
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm (unitF X x) τ i.succ / dmin X.Gm (unitF X x) τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, norm_dmin_unitF hx, norm_dmin_unitF hx, div_one]
  simp_rw [h1, Real.one_rpow, Finset.prod_const_one, mul_one]
  rw [show unitF X x = rmul x (unitB X x) from rfl, hB _ (unitB_mem x hx), norm_mul, mul_comm]
  congr 1
  unfold bchar
  simp only [norm_prod, norm_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  show ‖(Matrix.diagonal (fun a => ((bt X x τ a : ℝ) : ℂ)) i i)‖ ^ la τ i = _
  rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_of_nonneg (bt_pos hx τ i).le]
  unfold bt
  rw [← Real.rpow_intCast, ← Real.rpow_mul (tq_pos hx τ i).le]
  unfold tq
  congr 1
  ring

theorem pnorm_eq_unitF (x : Frame X.Ψ r) (hx : x ∈ X.dom) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : X.IsSec la P) : X.pnorm la P x = ‖P (unitF X x)‖ := by
  rw [← pnorm_unitF x hx la P (hP.2.1 x hx)]
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm (unitF X x) τ i.succ / dmin X.Gm (unitF X x) τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, norm_dmin_unitF hx, norm_dmin_unitF hx, div_one]
  simp_rw [h1, Real.one_rpow, Finset.prod_const_one, mul_one]

theorem lact_one' {Ψ : Finset (E →+* ℂ)} (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end GlobalTheory.FrameNorm.UnitFr

namespace GlobalTheory.FrameNorm

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem exists_unitFr_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k (x : (U.X k).dom), ∃ x' : (U.X k).dom, IsUnitFr (U.X k) x'.1 ∧ (∃ b ∈ FD.Bor (U.X k).Ψ r, x'.1 = FD.rmul x.1 b) ∧ (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x') (U.un k x)) ∧ ∀ (la : FD.Wt (U.X k).Ψ r) (P : FD.Frame (U.X k).Ψ r → ℂ), (U.X k).IsSec la P → (U.X k).pnorm la P x.1 = ‖P x'.1‖) ∧ ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 ∧ FrBor t (U.un k x) y := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU
  have h3 := hU.2.2.1
  have h4 := hU.2.2.2.1
  clear hU
  let uf : ∀ k, (U.X k).dom → (U.X k).dom := fun k x => ⟨UnitFr.unitF (U.X k) x.1, UnitFr.unitF_mem x.1 x.2⟩
  have huf : ∀ k x, (uf k x).1 = FD.rmul x.1 (UnitFr.unitB (U.X k) x.1) := fun _ _ => rfl
  have hun : ∀ k x, IsUnitFr (U.X k) (uf k x).1 := fun k x τ i => UnitFr.norm_dmin_unitF x.2 τ i
  have hpn : ∀ k (x : (U.X k).dom) (la : FD.Wt (U.X k).Ψ r) (P : FD.Frame (U.X k).Ψ r → ℂ), (U.X k).IsSec la P →
      (U.X k).pnorm la P x.1 = ‖P (uf k x).1‖ := fun k x la P hP => UnitFr.pnorm_eq_unitF x.1 x.2 la P hP
  clear_value uf
  have key : ∀ k (x : (U.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k (uf k x)) (U.un k x) := by
    intro k x
    obtain ⟨t, ht⟩ := (h4 k k x (uf k x)).2
      ⟨1, (U.X k).Γ.one_mem, UnitFr.unitB (U.X k) x.1, UnitFr.unitB_mem x.1 x.2, by
        rw [UnitFr.lact_one', huf]⟩
    exact ⟨t⁻¹, (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) (U.un k (uf k x))
      (U.un k x)).2.2.2 t ht⟩
  refine ⟨fun k x => ⟨uf k x, hun k x, ⟨_, UnitFr.unitB_mem x.1 x.2, huf k x⟩, key k x, hpn k x⟩, fun y => ?_⟩
  obtain ⟨k, x, t, ht⟩ := h3 y
  obtain ⟨s, hs⟩ := key k x
  exact ⟨k, uf k x, t * s, hun k x,
    (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k (uf k x)) (U.un k x) y).2.2.1 s t hs ht⟩

end GlobalTheory.FrameNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChangeStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_gram_frame_borel_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k (x : (U.X k).dom), ∃ x' : (U.X k).dom, IsUnitFr (U.X k) x'.1 ∧ (∃ b ∈ FD.Bor (U.X k).Ψ r, x'.1 = FD.rmul x.1 b) ∧ (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x') (U.un k x)) ∧ ∀ (la : FD.Wt (U.X k).Ψ r) (P : FD.Frame (U.X k).Ψ r → ℂ), (U.X k).IsSec la P → (U.X k).pnorm la P x.1 = ‖P x'.1‖) ∧ ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 ∧ FrBor t (U.un k x) y := by
  first | exact @GlobalTheory.FrameNorm.exists_unitFr_frBor | exact GlobalTheory.FrameNorm.exists_unitFr_frBor | (intros; apply GlobalTheory.FrameNorm.exists_unitFr_frBor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
noncomputable section

namespace GlobalTheory.ModelPoints

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem existsUnique_extension {W L : Type} [CommRing W] [IsDomain W] [ValuationRing W] [Field L] [Algebra W L]
    [IsFractionRing W L] {X S : Scheme.{0}} (s : X ⟶ S) [IsProper s] (y : Sp L ⟶ X) (r : Sp W ⟶ S)
    (h : y ≫ s = spMap (algebraMap W L) ≫ r) :
    ∃! x : Sp W ⟶ X, x ≫ s = r ∧ spMap (algebraMap W L) ≫ x = y := by
  have hP : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) s := by
    rw [← IsProper.eq_valuativeCriterion]
    exact ‹IsProper s›
  let S : ValuativeCommSq s := { R := W, K := L, i₁ := y, i₂ := r, commSq := ⟨h⟩ }
  obtain ⟨u⟩ := hP.1.1.1 S
  refine ⟨u.default.l, ⟨u.default.fac_right, u.default.fac_left⟩, ?_⟩
  rintro x ⟨hx₁, hx₂⟩
  exact congrArg CommSq.LiftStruct.l (u.uniq ⟨x, hx₂, hx₁⟩)

theorem existsUnique_chartHom {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (W : Type) [CommRing W]
    [IsLocalRing W] (yt : Sp W ⟶ X) (hy : yt (IsLocalRing.closedPoint W) ∈ U) :
    ∃! ψ : Γ(X, U) →+* W, spMap ψ ≫ hU.fromSpec = yt := by
  have hsub : Set.range yt ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := W) p).map yt.continuous).mem_open U.isOpen hy
  let g := IsOpenImmersion.lift hU.fromSpec yt hsub
  have hg : g ≫ hU.fromSpec = yt := IsOpenImmersion.lift_fac _ _ _
  refine ⟨(Spec.preimage g).hom, ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom (Spec.preimage g).hom) ≫ hU.fromSpec = yt
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
  · intro ψ hψ
    have h₁ : Spec.map (CommRingCat.ofHom ψ) = g := by
      rw [← cancel_mono hU.fromSpec, hg]
      exact hψ
    have h₂ : CommRingCat.ofHom ψ = Spec.preimage g :=
      Spec.map_injective (h₁.trans (Spec.map_preimage g).symm)
    rw [← h₂]
    rfl

theorem exists_chart_finiteType {O : Type} [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O) [LocallyOfFiniteType s]
    {U : X.Opens} (hU : IsAffineOpen U) : ∃ α : O →+* Γ(X, U), hU.fromSpec ≫ s = spMap α ∧ α.FiniteType := by
  refine ⟨(Spec.preimage (hU.fromSpec ≫ s)).hom, ?_, ?_⟩
  · show _ = Spec.map (CommRingCat.ofHom _)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  · have hlf : LocallyOfFiniteType (Spec.map (Spec.preimage (hU.fromSpec ≫ s))) := by
      rw [Spec.map_preimage]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlf

theorem model_points_charts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (∀ (W L : Type) [CommRing W] [IsDomain W] [ValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (oV : O →+* W) (fK : c.F →+* L) (y : Sp L ⟶ Xo.XF c), (algebraMap W L).comp oV = fK.comp β → y ≫ pullback.snd _ _ = spMap fK → ∃! yt : Sp W ⟶ Y.X, yt ≫ Y.s = spMap oV ∧ spMap (algebraMap W L) ≫ yt = y ≫ Y.j) ∧ (∀ (S : Scheme.{0}) (f : S ⟶ Y.X), ∃ G : SAB H S, Nonempty (SABMap G Y.t f)) ∧ ∀ (U : Y.X.Opens) (hU : IsAffineOpen U), ∃ α : O →+* Γ(Y.X, U), hU.fromSpec ≫ Y.s = spMap α ∧ α.FiniteType ∧ ∀ (W : Type) [CommRing W] [IsLocalRing W] (yt : Sp W ⟶ Y.X), yt (IsLocalRing.closedPoint W) ∈ U → ∃! ψ : Γ(Y.X, U) →+* W, spMap ψ ≫ hU.fromSpec = yt := by
  intro E _ _ _ H D l Xo c O _ β Y
  haveI : IsProper Y.s := projProper O Y.X Y.s Y.proj
  refine ⟨?_, ?_, ?_⟩
  · intro W L _ _ _ _ _ _ oV fK y hc hy
    apply existsUnique_extension Y.s (y ≫ Y.j) (spMap oV)
    rw [Category.assoc, Model.j_s, ← Category.assoc, hy, ← spMap_comp, ← spMap_comp, hc]
  · intro S f
    have hp := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull f Y.t
    exact ⟨_, ⟨hp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩⟩
  · intro U hU
    obtain ⟨α, hα, hft⟩ := exists_chart_finiteType Y.s hU
    exact ⟨α, hα, hft, fun W _ _ yt hyt => existsUnique_chartHom hU W yt hyt⟩

end GlobalTheory.ModelPoints
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FnFGFnTrdeg
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FlagDim

theorem fnFG_fnTrdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FnFG Xo c ∧ FnTrdeg Xo c (Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2)) := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨h1, h2⟩ := GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c
  refine ⟨fnFG_of Xo c h1, ?_⟩
  rw [← dim_add_card_flagVar E H Dw]
  exact fnTrdeg_of Xo c Dw.dim h2

end GlobalTheory.FlagDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.InjectiveAlgebraMapOfDvrOfIsIntegral
namespace GlobalTheory

open IsLocalRing

theorem _root_.GlobalTheory.dvr_finite_over_complete_dvr :
    ∀ (O V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing V] [IsDomain V]
      [IsDiscreteValuationRing V] [Algebra O V] [Module.Finite O V],
      Function.Injective (algebraMap O V) ∧ IsLocalHom (algebraMap O V) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ CharZero V ∧
          (Finite (IsLocalRing.ResidueField O) → Finite (IsLocalRing.ResidueField V)) := by
  intro O V _ _ _ _ _ _ _ _ _ _
  haveI : Algebra.IsIntegral O V := Algebra.IsIntegral.of_finite O V
  have hinj : Function.Injective (algebraMap O V) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    by_contra h
    push_neg at h
    obtain ⟨a, ha, ha0⟩ := h
    have hker : (RingHom.ker (algebraMap O V)).IsMaximal := by
      refine Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) ?_
      intro hb
      apply ha0
      have hmem : a ∈ RingHom.ker (algebraMap O V) := ha
      rw [hb] at hmem
      exact (Ideal.mem_bot).1 hmem
    have hbot : (⊥ : Ideal V).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) ⊥
        (by rwa [Ideal.under_def, ← RingHom.ker_eq_comap_bot])
    exact IsDiscreteValuationRing.not_a_field V (IsLocalRing.eq_maximalIdeal hbot).symm
  have hloc : IsLocalHom (algebraMap O V) :=
    RingHom.IsIntegral.isLocalHom (fun x => Algebra.IsIntegral.isIntegral x) hinj
  haveI := hloc
  refine ⟨hinj, hloc, ?_, charZero_of_injective_algebraMap hinj, fun h => ?_⟩
  swap
  · exact Module.finite_of_finite (ResidueField O)
  haveI : Module.IsTorsionFree O V := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.Free O V := Module.free_of_finite_type_torsion_free'
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hπm : π ∈ maximalIdeal O := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hπ.not_isUnit)
  have hp0 : algebraMap O V π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have hpm : algebraMap O V π ∈ maximalIdeal V :=
    (mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => hπ.not_isUnit ((isUnit_map_iff _ _).1 hu))
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {algebraMap O V π}) (by simpa using hp0) hq
  have hpow : ∀ k, maximalIdeal V ^ (e * k) = Ideal.span {algebraMap O V π ^ k} := by
    intro k
    rw [hq.maximalIdeal_eq, Ideal.span_singleton_pow, pow_mul, ← Ideal.span_singleton_pow, ← he,
      Ideal.span_singleton_pow]
  refine
    { toIsHausdorff := IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal V).ne_top
      toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  have hf' : ∀ m n, m ≤ n → f m - f n ∈ maximalIdeal V ^ m := fun m n h => by
    simpa using SModEq.sub_mem.1 (hf h)
  have hg : ∀ m n, m ≤ n →
      ∃ y, f (e * m + m) - f (e * n + n) = algebraMap O V π ^ m * y := by
    intro m n h
    have h1 := hf' _ _ (Nat.add_le_add (Nat.mul_le_mul_left e h) h)
    have h2 : f (e * m + m) - f (e * n + n) ∈ Ideal.span {algebraMap O V π ^ m} := by
      rw [← hpow]
      exact Ideal.pow_le_pow_right (Nat.le_add_right _ _) h1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
    exact ⟨y, by rw [← hy, mul_comm]⟩
  let b := Module.Free.chooseBasis O V
  have hc : ∀ i, ∀ {m n : ℕ}, m ≤ n →
      b.repr (f (e * m + m)) i ≡ b.repr (f (e * n + n)) i
        [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O O)] := by
    intro i m n h
    obtain ⟨y, hy⟩ := hg m n h
    have hdiff : b.repr (f (e * m + m)) i - b.repr (f (e * n + n)) i = π ^ m * b.repr y i := by
      rw [← Finsupp.sub_apply, ← map_sub, hy, ← map_pow, ← Algebra.smul_def, map_smul,
        Finsupp.smul_apply, smul_eq_mul]
    have hmem : π ^ m * b.repr y i ∈ maximalIdeal O ^ m :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm m)
    rw [SModEq.sub_mem, hdiff]
    simpa using hmem
  choose l hl using fun i =>
    (inferInstance : IsPrecomplete (maximalIdeal O) O).prec
      (f := fun k => b.repr (f (e * k + k)) i) (hc i)
  refine ⟨∑ i, l i • b i, fun n => ?_⟩
  have hgn : f (e * n + n) - ∑ i, l i • b i ∈ maximalIdeal V ^ n := by
    have hex : ∀ i, ∃ t, b.repr (f (e * n + n)) i - l i = π ^ n * t := fun i => by
      have hmem := SModEq.sub_mem.1 (hl i n)
      simp only [smul_eq_mul, Ideal.mul_top] at hmem
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
      obtain ⟨t, ht⟩ := hmem
      exact ⟨t, by rw [← ht, mul_comm]⟩
    choose t ht using hex
    have hsum : f (e * n + n) - ∑ i, l i • b i =
        algebraMap O V π ^ n * ∑ i, t i • b i := by
      conv_lhs => rw [← b.sum_repr (f (e * n + n))]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, ht, mul_smul, Algebra.smul_def, map_pow]
    rw [hsum]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpm n)
  have hfg : f n - f (e * n + n) ∈ maximalIdeal V ^ n := hf' n (e * n + n) (Nat.le_add_left _ _)
  have hsum := Ideal.add_mem _ hfg hgn
  rw [sub_add_sub_cancel] at hsum
  rw [SModEq.sub_mem]
  simpa using hsum

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LawBddDataOf
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg.LawBddPf

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem nrm_add_le (Z : Comp Xo c) (G : WTZ E) (x y : AC Z) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) G (x + y) P ≤ nrmC fn (yP Z) G x P + nrmC fn (yP Z) G y P := by
  unfold nrmC
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => by positivity)
  have hc : (x + y).coeff G = x.coeff G + y.coeff G := by rfl
  rw [hc, map_add (f := _)]
  exact norm_add_le _ _

theorem nrm_smul (Z : Comp Xo c) (G : WTZ E) (a : Om Z) (x : AC Z) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) G (a • x) P = ‖P a‖ * nrmC fn (yP Z) G x P := by
  unfold nrmC
  have hc : (a • x).coeff G = a * x.coeff G := by rfl
  rw [hc, map_mul, norm_mul, mul_assoc]

theorem bdd_gen [Fintype (Comp Xo c)] (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (sg : c.F →+* ℂ) :
    BddAbove (Set.range fun p : (Σ Z : Comp Xo c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) sg) =>
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) := by
  unfold ValAtCx at hcx
  obtain ⟨B, hBd⟩ := hB sg
  refine ⟨B, ?_⟩
  rintro _ ⟨⟨Z, P⟩, rfl⟩
  have hP : (P : Om Z →+* ℂ).comp (algebraMap c.F (Om Z)) = sg := P.2
  have key : ∀ (σ : c.F →+* ℂ), σ = sg → ∀ y : FrPt Xo c (CAt σ),
      cabs (evR Xo c f y) * ∏ i, |fn σ y i|⁻¹ ^ ex Dw a n i ≤ B := by
    rintro σ rfl y
    exact hBd ⟨y, rfl⟩
  have hex : ∀ i, exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by
    intro i
    unfold exZ wtZ ex
    cases i <;> rfl
  have hco : (valC h a n f Z).coeff (wtZ a n) = evC h Z f := by
    unfold valC
    simp
  show nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) (P : Om Z →+* ℂ) ≤ B
  unfold nrmC
  rw [hco, hcx Z P a n f hS]
  have hs : sgOf (P : Om Z →+* ℂ) = sg := hP
  refine Eq.trans_le ?_ (key _ hs (yP Z P))
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hex i, zpow_neg, zpow_natCast, inv_pow]

theorem bdd_span (G : WTZ E) (sg : c.F →+* ℂ) (S : Set (∀ Z : Comp Xo c, AC Z))
    (hS : ∀ f ∈ S, BddAbove (Set.range fun p : (Σ Z : Comp Xo c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) sg) =>
      nrmC fn (yP p.1) G (f p.1) p.2)) (f : ∀ Z : Comp Xo c, AC Z)
    (hf : f ∈ (letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
      Submodule.span (𝓞 c.F) S)) :
    BddAbove (Set.range fun p : (Σ Z : Comp Xo c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) sg) =>
      nrmC fn (yP p.1) G (f p.1) p.2) := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    refine ⟨0, ?_⟩
    rintro _ ⟨⟨Z, P⟩, rfl⟩
    have h0 := nrm_smul (fn := fn) (yP := yP) Z G (0 : Om Z) (0 : AC Z) (P : Om Z →+* ℂ)
    rw [zero_smul, map_zero, norm_zero, zero_mul] at h0
    exact h0.le
  | add x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    refine ⟨A + B, ?_⟩
    rintro _ ⟨⟨Z, P⟩, rfl⟩
    exact (nrm_add_le Z G _ _ _).trans
      (add_le_add (hA ⟨⟨Z, P⟩, rfl⟩) (hB ⟨⟨Z, P⟩, rfl⟩))
  | smul a x _ hx =>
    obtain ⟨A, hA⟩ := hx
    refine ⟨‖sg (a : c.F)‖ * A, ?_⟩
    rintro _ ⟨⟨Z, P⟩, rfl⟩
    have hP : (P : Om Z →+* ℂ).comp (algebraMap c.F (Om Z)) = sg := P.2
    have hsm : (a • x) Z = (algebraMap c.F (Om Z) (a : c.F)) • x Z := by
      rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
      congr 1
    have hv : (P : Om Z →+* ℂ) (algebraMap c.F (Om Z) (a : c.F)) = sg (a : c.F) := by
      exact RingHom.congr_fun hP _
    show nrmC fn (yP Z) G ((a • x) Z) (P : Om Z →+* ℂ) ≤ _
    rw [hsm, nrm_smul, hv]
    exact mul_le_mul_of_nonneg_left (hA ⟨⟨Z, P⟩, rfl⟩) (norm_nonneg _)

end

theorem lawBdd_dataOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)) (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E) (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c) (nu : HeightOneSpectrum (𝓞 c.F) → ℝ) (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ) (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ), ValAtCx h yP → (∀ k, wR k ∈ sec Xo c uL.1 uL.2 ∧ SupBdd Xo c fn uL.1 uL.2 (wR k)) → (∀ k, thpR k ∈ sec Xo c uF.1 uF.2 ∧ SupBdd Xo c fn uF.1 uF.2 (thpR k)) → (etR ∈ sec Xo c uet.1 uet.2 ∧ SupBdd Xo c fn uet.1 uet.2 etR) → (ta1R ∈ sec Xo c uta1.1 uta1.2 ∧ SupBdd Xo c fn uta1.1 uta1.2 ta1R) → (ta2R ∈ sec Xo c uta2.1 uta2.2 ∧ SupBdd Xo c fn uta2.1 uta2.2 ta2R) → wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2 → wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2) → wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2 → LawBdd (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) := by
  intro E _ _ _ H Dw l Xo c _ h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hcx hw hth het hta1 hta2 e1 e2 e3
  unfold LawBdd
  set D := dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r with hD
  intro sg G F
  rintro (⟨hF, rfl⟩ | ⟨hF, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · refine bdd_span _ sg _ ?_ F hF
    rintro _ ⟨k, rfl⟩
    exact bdd_gen hcx (hw k).1 (hw k).2 sg
  · refine bdd_span _ sg _ ?_ F hF
    rintro _ ⟨k, rfl⟩
    exact bdd_gen hcx (hth k).1 (hth k).2 sg
  · have hG : D.n1 • D.wde = wtZ uet.1 uet.2 := by rw [hD]; exact e1.symm
    rw [hG]
    exact bdd_gen hcx het.1 het.2 sg
  · have hG : 2 • D.G1 = wtZ uta1.1 uta1.2 := by rw [hD]; exact e2.symm
    rw [hG]
    exact bdd_gen hcx hta1.1 hta1.2 sg
  · have hG : D.G2 = wtZ uta2.1 uta2.2 := by rw [hD]; exact e3.symm
    rw [hG]
    exact bdd_gen hcx hta2.1 hta2.2 sg

end GlobalTheory.Reg.LawBddPf
end
