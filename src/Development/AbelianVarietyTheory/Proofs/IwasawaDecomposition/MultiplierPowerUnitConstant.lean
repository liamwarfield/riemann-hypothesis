module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajorantHarnackHolomorphicHalfPlane
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceMoveRationalFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplierPowerUnitConstant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam

noncomputable section

namespace GlobalTheory.IntFam.CoordPow

theorem pow_law {X Q : Type} [AddCommGroup X] [CommGroup Q] (p : X → Q) (t : X → X → Q)
    (ht : ∀ a b, t a b = p (a + b) * (p a)⁻¹ * (p b)⁻¹) (hadd : ∀ a a' b, t (a + a') b = t a b * t a' b)
    (hev : ∀ χ, p (-χ) = p χ) (k : ℕ) (α μ : X) : p (α + k • μ) = p α * (p μ ^ k * t μ α) ^ k := by
  have hsym : ∀ a b, t a b = t b a := fun a b => by rw [ht, ht, add_comm, mul_right_comm]
  have h0 : ∀ b, t 0 b = 1 := fun b => by
    have := hadd 0 0 b
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp0 : p 0 = 1 := by
    have := ht 0 0
    rw [h0, add_zero, mul_inv_cancel, one_mul] at this
    exact inv_eq_one.1 this.symm
  have hneg : ∀ a b, t (-a) b = (t a b)⁻¹ := fun a b => by
    have := hadd a (-a) b
    rw [add_neg_cancel, h0] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hmm : t μ μ = p μ ^ 2 := by
    have e1 := hneg μ μ
    rw [hsym, ht, add_neg_cancel, hp0, hev, one_mul] at e1
    rw [← inv_inv (t μ μ), ← e1, ← mul_inv, inv_inv, sq]
  have hn : ∀ (n : ℕ) b, t (n • μ) b = t μ b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have key : ∀ n : ℕ, p (α + n • μ) = p α * t μ α ^ n * p μ ^ (n * n) := fun n => by
    induction n with
    | zero => rw [zero_nsmul, add_zero, pow_zero, mul_zero, pow_zero, mul_one, mul_one]
    | succ n ih =>
      have e := ht (α + n • μ) μ
      have e2 : t (α + n • μ) μ = t μ α * (p μ ^ 2) ^ n := by
        rw [hadd, hsym α μ, hn, hmm]
      have e3 : p (α + n • μ + μ) = t (α + n • μ) μ * p (α + n • μ) * p μ := by
        rw [e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [succ_nsmul, ← add_assoc, e3, e2, ih, ← pow_mul,
        show (n + 1) * (n + 1) = n * n + 2 * n + 1 by ring]
      simp only [pow_add, pow_one]
      ac_rfl
  rw [key, mul_assoc, mul_pow, ← pow_mul, mul_comm (t μ α ^ k)]

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem val_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJc : IntegralCharts D J)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (q : Spec (CommRingCat.of R) ⟶ Y)
    (hq : ∀ k, (q ≫ φ k) ≫ D.P.A.hom = 𝟙 _) :
    ∃ u : Rˣ, (val t (jK R ≫ q) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  refine GlobalTheory.PeriodBalance.unit_gm' ξ q _ (Set.mem_iInter.2 fun k => ?_) _
  have := hJc (q ≫ φ k) (hq k)
  simp only [Category.assoc]
  exact this

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem pull_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : IntegralCharts D J) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (q : Spec (CommRingCat.of R) ⟶ Y)
    (hq : ∀ k, (q ≫ φ k) ≫ D.P.A.hom = 𝟙 _) (h : (TK R).left ⟶ Y) (hh : h = jK R ≫ q) :
    ∃ u : Rˣ, (val (LB.pullGen D.P.L φ ε t h) (𝟙 _) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  rw [val_pull hJ]
  have e : 𝟙 (TK R).left ≫ h = jK R ≫ q := by rw [hh]; exact Category.id_comp _
  rw [e]
  exact val_unit D ξ hJc t q hq

theorem rig_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : IntegralCharts D J) : ∃ u : Rˣ, (val D.rigK (𝟙 _) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  refine pull_unit D ξ hJ hJc D.rig (𝟙 _) (fun _ => ?_) _ ?_
  · rw [Category.id_comp]
    unfold eSec
    exact Over.w _
  · rw [Over.toUnit_left, Category.comp_id]; rfl

omit [IsLocalRing R] in
theorem cub_hq (D : DegPre R) (a a' b : D.X) (I : thK) :
    ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ thφ D.P.A (x3 D.P.A) I) ≫ D.P.A.hom = 𝟙 _ := by
  show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) I.down).left) ≫ D.P.A.hom = _
  rw [← Over.comp_left, Over.w]; rfl

omit [IsLocalRing R] in
theorem degenerationTriplePoint_eq_lift (D : DegPre R) (a a' b : D.X) :
    D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
  simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]

omit [IsLocalRing R] in
open MonObj in
theorem sym_hq (D : DegPre R) (χ : D.X) (k : Fin 2) :
    ((D.c χ).left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → (D.P.A.left ⟶ D.P.A.left)) k) ≫ D.P.A.hom = 𝟙 _ := by
  fin_cases k
  · show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = _
    rw [← Over.comp_left, Over.w]; rfl
  · show ((D.c χ).left ≫ 𝟙 _) ≫ D.P.A.hom = _
    rw [Category.comp_id, Over.w]; rfl

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (k : ℕ)
    (α mu : D.toPre.X) (r s : R), PsiCoord D.toPre α r → PsiCoord D.toPre (α + k • mu) (r * s) →
    ∀ (ξ : Spec (CommRingCat.of (FractionRing R))) (J), Good D.toPre.P.L ξ J → GlobalTheory.IntFam.IntegralCharts D.toPre J →
      ∃ u : Rˣ, (val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J).val ^ k = GlobalTheory.PeriodBalance.cst ξ (u * s) := by
  intro R _ _ _ I D k α mu r s hα hαk ξ J hJ hJc
  let H : Subgroup ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    (Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom).range
  have mem : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → g ∈ H := fun ⟨u, hu⟩ =>
    ⟨u, Units.ext (by rw [Units.coe_map, hu]; rfl)⟩
  let π := QuotientGroup.mk' H
  have π1 : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → π g = 1 := fun h =>
    (QuotientGroup.eq_one_iff _).2 (mem h)
  let P : D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    fun χ => val (D.toPre.psi χ) (𝟙 _) ξ J
  let T : D.toPre.X → D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    fun a b => val (D.toPre.tau a b) (𝟙 _) ξ J
  let Z : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := val D.toPre.rigK (𝟙 _) ξ J
  have hZ : π Z = 1 := π1 (rig_unit D.toPre ξ hJ hJc)
  have law := pow_law (fun χ => π (P χ)) (fun a b => π (T a b))
    (fun a b => by
      show π (T a b) = π (P (a + b)) * (π (P a))⁻¹ * (π (P b))⁻¹
      rw [show T a b = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * Z⁻¹ from GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b,
        map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hZ, inv_one, mul_one])
    (fun a a' b => by
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
      have hc := π1 (pull_unit D.toPre ξ hJ hJc D.toPre.cub.t _ (cub_hq D.toPre a a' b) _ (degenerationTriplePoint_eq_lift D.toPre a a' b))
      have e' := congrArg π e
      rw [map_mul, map_mul] at e'
      refine (mul_one _).symm.trans (Eq.trans ?_ e')
      congr 1
      exact hc.symm)
    (fun χ => by
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even χ) (𝟙 _))
      have hc := π1 (pull_unit D.toPre ξ hJ hJc D.toPre.sym _ (sym_hq D.toPre χ) _ (DVR.QForm.ptK_eq D.toPre χ))
      have e' := congrArg π e
      rw [map_mul] at e'
      refine (mul_one _).symm.trans (Eq.trans ?_ e')
      congr 1
      exact hc.symm) k α mu
  set v : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J
  have hv : v = P mu ^ k * T mu α * Z ^ k :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (map_pow _ _ _) rfl))
      (map_pow _ _ _))
  have hq : π (v ^ k * P α * (P (α + k • mu))⁻¹) = 1 := by
    simp only [map_mul, map_inv, map_pow, hv, hZ, one_pow, mul_one]
    rw [law]
    exact mul_inv_eq_one.2 (mul_comm _ _)
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).1 hq
  obtain ⟨u₁, h₁⟩ := GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc α r hα
  obtain ⟨u₂, h₂⟩ := GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc (α + k • mu) (r * s) hαk
  have e : v ^ k = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom w * P (α + k • mu) * (P α)⁻¹ := by
    rw [hw]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hA : ((P α)⁻¹).val * (GlobalTheory.PeriodBalance.cst ξ u₁ * GlobalTheory.PeriodBalance.cst ξ r) = 1 := by
    rw [← map_mul, ← h₁]; exact Units.inv_mul _
  have hu : GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ) * GlobalTheory.PeriodBalance.cst ξ u₁ = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨w * u₂ * u₁⁻¹, ?_⟩
  rw [← Units.val_pow_eq_pow_val, e, Units.val_mul, Units.val_mul, Units.coe_map, h₂]
  simp only [Units.val_mul, map_mul]
  linear_combination (-(GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ * GlobalTheory.PeriodBalance.cst ξ s *
    GlobalTheory.PeriodBalance.cst ξ r * ((P α)⁻¹).val)) * hu + (GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ *
    GlobalTheory.PeriodBalance.cst ξ s * GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ)) * hA

end GlobalTheory.IntFam.CoordPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianPeriodLatticeBasisSameSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbRtSq
open NumberField

namespace GlobalTheory.ConjugateMultiplicity

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by

  have hsq := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have hprod : H.rt0.re * H.rt0.im = 0 := by linarith [mul_comm H.rt0.re H.rt0.im]
    have him0 : H.rt0.im = 0 := (mul_eq_zero.1 hprod).resolve_left hne
    rw [him0] at hre
    nlinarith [sq_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem emb_rt_sq (H : Host E) (τ : E →+* ℂ) : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
  have h : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h' := congrArg ((↑) : 𝓞 E → E) H.rt_sq
    push_cast at h'
    exact h'
  rw [← map_pow, h, map_neg, map_natCast, H.sqrt_neg_disc_sq]

private theorem mult_conjEmb_eq_ite {H : Host E} (D : Datum H) (τ : E →+* ℂ) :
    Datum.mult D (conjEmb τ) = if τ (H.rt : E) = H.rt0 then Datum.q D else Datum.p D := by

  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have hsq := H.sqrt_neg_disc_sq
    rw [h0] at hsq
    have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
    exact hd (by linear_combination hsq)
  have hc : conjEmb τ (H.rt : E) = starRingEnd ℂ (τ (H.rt : E)) := rfl
  unfold Datum.mult

  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (emb_rt_sq H τ) with h | h
  · have h2 : ¬ conjEmb τ (H.rt : E) = H.rt0 := by
      rw [hc, h, rt0_conj_neg_ne_zero]
      exact fun e => hne e.symm
    rw [if_pos h, if_neg h2]
  · have h2 : conjEmb τ (H.rt : E) = H.rt0 := by
      rw [hc, h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have h3 : ¬ τ (H.rt : E) = H.rt0 := by
      rw [h]
      exact fun e => hne e.symm
    rw [if_pos h2, if_neg h3]

end GlobalTheory.ConjugateMultiplicity

theorem GlobalTheory.ConjugateMultiplicity.target : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (τ : E →+* ℂ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult D (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult D τ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.p D + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.q D := by
  intro E _ _ _ H D τ
  rw [GlobalTheory.ConjugateMultiplicity.mult_conjEmb_eq_ite]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
  split_ifs <;> omega
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianPeriodLatticeBasisSameSignature
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.PerBasis

theorem mult_conj_add_mult {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (D : Datum H) (τ : E →+* ℂ) : D.mult (conjEmb τ) + D.mult τ = D.p + D.q := by
  first
  | exact @_root_.GlobalTheory.ConjugateMultiplicity.target
  | exact _root_.GlobalTheory.ConjugateMultiplicity.target
  | (apply _root_.GlobalTheory.ConjugateMultiplicity.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateMultiplicity.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateMultiplicity.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateMultiplicity.target ..)

theorem exists_indep {E : Type} [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] (J : Type) [Fintype J] (hJ : Fintype.card J = Module.finrank (𝓞 E) M) :
    ∃ x : J → M, LinearIndependent (𝓞 E) x ∧
      ∀ v, ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := M) (n := Fintype.card J) hJ.le
  let e := Fintype.equivFin J
  refine ⟨f ∘ e, hf.comp _ e.injective, fun v => ?_⟩
  rw [e.surjective.range_comp]
  have hc : ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Submodule.span (𝓞 E) (Set.range f) := by
    by_contra hcon
    push Not at hcon
    have hli : LinearIndependent (𝓞 E) (Fin.cons v f : Fin (Fintype.card J + 1) → M) := by
      refine LinearIndependent.finCons' v f hf fun c y hy h => ?_
      by_contra hc
      refine hcon c hc ?_
      rw [eq_neg_of_add_eq_zero_left h]
      exact neg_mem hy
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨c, hc0, hc⟩ := hc
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hd, mul_smul]
    exact Submodule.smul_mem _ _ hc

theorem exists_trace_rep {E : Type} [Field E] [NumberField E] (φ : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ h : E, ∀ a : 𝓞 E, ((φ a : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h) := by
  let ψ : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ fun i => (φ (RingOfIntegers.basis E i) : ℚ)
  have hψ : ∀ a : 𝓞 E, ((φ a : ℤ) : ℚ) = ψ (a : E) := by
    intro a
    have : (Int.castAddHom ℚ).toIntLinearMap ∘ₗ φ =
        (ψ.restrictScalars ℤ) ∘ₗ ((algebraMap (𝓞 E) E).toAddMonoidHom.toIntLinearMap) := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      change ((φ (RingOfIntegers.basis E i) : ℤ) : ℚ) = ψ (algebraMap (𝓞 E) E (RingOfIntegers.basis E i))
      rw [← integralBasis_apply, Module.Basis.constr_basis]
    exact LinearMap.congr_fun this a
  refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm ψ, fun a => ?_⟩
  rw [hψ, mul_comm, ← Algebra.traceForm_apply]
  exact (LinearMap.BilinForm.apply_toDual_symm_apply _ _).symm

theorem exists_isPerBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw Di : Datum H) (τ : E →+* ℂ), Di.p = Dw.p ∧ Di.q = Dw.q →
    ∃ (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), IsPerBasis Di x hm := by
  intro E _ _ _ H Dw Di τ ⟨hp, hq⟩
  have := Di.fin
  obtain ⟨x, hx, hsp⟩ := exists_indep (E := E) Di.La (Idx Dw τ) (by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, mult_conj_add_mult, Di.rank, hp, hq])
  have hrep : ∀ k k', ∃ h : E, ∀ a : 𝓞 E,
      ((Di.EF (a • x k) (x k') : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h) := fun k k' =>
    exists_trace_rep (AddMonoidHom.toIntLinearMap
      { toFun := fun a : 𝓞 E => Di.EF (a • x k) (x k')
        map_zero' := by simp
        map_add' := fun a b => by simp [add_smul] })
  choose hm hhm using hrep
  refine ⟨x, Matrix.of hm, hx, hsp, fun a k k' => hhm k k' a, fun hdet => ?_⟩
  obtain ⟨c₀, hc₀, hker⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) c₀
  choose c hc using hd
  set v := ∑ k, c k • x k with hv
  have h1 : ∀ (a : 𝓞 E) k', Di.EF (a • v) (x k') = 0 := by
    intro a k'
    have hk := congrFun hker k'
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at hk
    have : ((Di.EF (a • v) (x k') : ℤ) : ℚ) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hv, Finset.smul_sum, map_sum, LinearMap.sum_apply]
      push_cast
      simp_rw [← mul_smul, hhm]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum]
      have : ∑ k, ((a * c k : 𝓞 E) : E) * hm k k' = (a : E) * ((d : 𝓞 E) : E) * ∑ k, c₀ k * hm k k' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have h2 : ((c k : 𝓞 E) : E) = ((d : 𝓞 E) : E) * c₀ k := by
          exact (hc k).trans (Algebra.smul_def _ _)
        have h3 : ((a * c k : 𝓞 E) : E) = (a : E) * ((c k : 𝓞 E) : E) := map_mul (algebraMap (𝓞 E) E) _ _
        rw [h3, h2]; ring
      rw [this, hk]; simp
    exact_mod_cast this
  have h2 : ∀ w ∈ Submodule.span (𝓞 E) (Set.range x), ∀ a : 𝓞 E, Di.EF v (a • w) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k, rfl⟩ := hw
      intro a
      have := h1 (H.bar.symm a) k
      rwa [Di.adj, RingEquiv.apply_symm_apply] at this
    | zero => simp
    | add y z _ _ hy hz => intro a; rw [smul_add, map_add (f := _), hy, hz, add_zero]
    | smul b y _ hy => intro a; rw [← mul_smul, hy]
  have h3 : v = 0 := by
    apply Di.unimod.1
    rw [map_zero]
    ext w
    obtain ⟨n, hn, hw⟩ := hsp w
    have := h2 _ hw 1
    rw [one_smul, map_nsmul] at this
    simpa [hn] using this
  apply hc₀
  funext k
  have h4 := Fintype.linearIndependent_iff.1 hx c h3 k
  have h5 := hc k
  rw [h4, map_zero, Algebra.smul_def] at h5
  refine (mul_eq_zero.1 h5.symm).resolve_left ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero d)

end GlobalTheory.ShFam.Hor.PerBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianPeriodLatticeBasisSameSignatureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw Di : Datum H) (τ : E →+* ℂ), Di.p = Dw.p ∧ Di.q = Dw.q → ∃ (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), IsPerBasis Di x hm := by
  first | exact @GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis | exact GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis | (intros; apply GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFrameLimitsOfOrbit
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt hermC bchar)
open scoped Matrix

namespace GlobalTheory.OrbitNfac

theorem span_bound {α : Type} (l : Filter α) {n m : ℕ} (L : α → Fin n → Fin m → ℂ) (L0 : Fin n → Fin m → ℂ)
    (hL : ∀ j i, Tendsto (fun w => L w j i) l (𝓝 (L0 j i))) (hs : Submodule.span ℂ (Set.range L0) = ⊤) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ w in l, ∀ (ℓ : Fin m → ℂ) (k : Fin m), ‖ℓ k‖ ≤ K * ∑ j, ‖∑ i, ℓ i * L w j i‖ := by
  classical
  have hA : ∀ k : Fin m, ∃ A : Fin n → ℂ, ∑ j, A j • L0 j = Pi.single k 1 := fun k =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hs ▸ Submodule.mem_top)
  choose A hA using hA
  set K : ℝ := ∑ k, ∑ j, ‖A k j‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hAK : ∀ k j, ‖A k j‖ ≤ K := fun k j =>
    (Finset.single_le_sum (f := fun j => ‖A k j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k => ∑ j, ‖A k j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  have ht : Tendsto (fun w => K * ∑ j, ∑ i, ‖L0 j i - L w j i‖) l (𝓝 (K * ∑ j : Fin n, ∑ i : Fin m, (0 : ℝ))) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun i _ => ?_)
    have := ((tendsto_const_nhds (x := L0 j i)).sub (hL j i)).norm
    simpa using this
  simp only [Finset.sum_const_zero, mul_zero] at ht
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with w hw ℓ k
  set S : ℝ := ∑ j, ‖∑ i, ℓ i * L w j i‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have key : ∀ k, ‖ℓ k‖ ≤ K * S + ‖ℓ‖ / 2 := by
    intro k
    have e1 : ℓ k = ∑ j, A k j * ((∑ i, ℓ i * L w j i) + ∑ i, ℓ i * (L0 j i - L w j i)) := by
      have e2 : ℓ k = ∑ i, ℓ i * (∑ j, A k j • L0 j) i := by
        rw [hA k]; simp [Pi.single_apply]
      rw [e2]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have e3 : ∀ j, ‖A k j * ((∑ i, ℓ i * L w j i) + ∑ i, ℓ i * (L0 j i - L w j i))‖ ≤
        K * ‖∑ i, ℓ i * L w j i‖ + ‖ℓ‖ * (K * ∑ i, ‖L0 j i - L w j i‖) := by
      intro j
      have h1 : ‖∑ i, ℓ i * (L0 j i - L w j i)‖ ≤ ‖ℓ‖ * ∑ i, ‖L0 j i - L w j i‖ := by
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm ℓ i) (norm_nonneg _)
      rw [norm_mul]
      calc _ ≤ K * (‖∑ i, ℓ i * L w j i‖ + ‖ℓ‖ * ∑ i, ‖L0 j i - L w j i‖) :=
            mul_le_mul (hAK k j) ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _) hK0
        _ = _ := by ring
    calc ‖ℓ k‖ ≤ ∑ j, (K * ‖∑ i, ℓ i * L w j i‖ + ‖ℓ‖ * (K * ∑ i, ‖L0 j i - L w j i‖)) := by
          rw [e1]; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => e3 j)
      _ = K * S + ‖ℓ‖ * (K * ∑ j, ∑ i, ‖L0 j i - L w j i‖) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ K * S + ‖ℓ‖ / 2 := by nlinarith [norm_nonneg ℓ]
  have h2 : ‖ℓ‖ ≤ K * S + ‖ℓ‖ / 2 := (pi_norm_le_iff_of_nonneg (by positivity)).2 key
  have := norm_le_pi_norm ℓ k
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (X : Data E N)

theorem coord_le {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b)) (τ : X.Ψ)
    (u : Fin N → ℂ) (i : Fin N) : ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖ ≤ 1 + X.maj x τ u := by
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb
  have h := UnipMove.GraphH.maj_ortho X ho τ ((mat (rmul x b) τ)⁻¹ *ᵥ u)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hy τ).1), Matrix.one_mulVec,
    GlobalTheory.MajInv.maj_rmul X hx hb] at h
  have h2 : ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖ ^ 2 ≤ X.maj x τ u := by
    rw [h]
    exact Finset.single_le_sum (f := fun j => ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [sq_nonneg (‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖ - 1), sq_nonneg ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖]

theorem inv_diag {b : Frame X.Ψ N} (hb : b ∈ Bor X.Ψ N) (τ : X.Ψ) (i : Fin N) :
    (mat b τ)⁻¹ i i = (b τ i i)⁻¹ := by
  have hi := (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X hb τ).2
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul (mat b τ) (Ne.isUnit (hb τ).1)) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at h
  · exact eq_inv_of_mul_eq_one_left h
  · intro a _ ha
    rcases lt_or_gt_of_ne ha with h1 | h1
    · have : (mat b τ)⁻¹ i a = 0 := hi i a h1
      rw [this, zero_mul]
    · have : mat b τ a i = 0 := (hb τ).2 a i h1
      rw [this, mul_zero]
  · simp

theorem quot_bound {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b)) (τ : X.Ψ)
    {n : ℕ} (v : Fin n → Fin N → E) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (ℓ : Fin (N - X.p0) → ℂ) (k : Fin (N - X.p0)), ‖ℓ k‖ ≤ K * ∑ j, ‖∑ i, ℓ i * perFr X x (v j) τ.1 i‖)
    (i : Fin N) (hi : X.p0 ≤ i) : ‖b τ i i‖⁻¹ ≤ K * ∑ j, (1 + X.maj x τ (Data.emb τ.1 (v j))) := by
  have hinv := (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X hb τ).2
  let e : Fin (N - X.p0) → Fin N := fun k => ⟨X.p0 + k, by have := k.2; omega⟩
  have h1 := h (fun k => (mat b τ)⁻¹ i (e k)) ⟨i - X.p0, by have := i.2; omega⟩
  have he : e ⟨i - X.p0, by have := i.2; omega⟩ = i := Fin.ext (by simp only [e]; omega)
  simp only [he] at h1
  rw [inv_diag X hb, norm_inv] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hK)
  have e1 : ∑ k : Fin (N - X.p0), (mat b τ)⁻¹ i (e k) * perFr X x (v j) τ.1 k =
      ((mat (rmul x b) τ)⁻¹ *ᵥ Data.emb τ.1 (v j)) i := by
    have e2 : mat (rmul x b) τ = mat x τ * mat b τ := rfl
    rw [e2, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    show _ = ∑ a, (mat b τ)⁻¹ i a * ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 (v j)) a
    refine Finset.sum_of_injOn e (fun a _ c _ hac => Fin.ext ?_)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun a _ ha => ?_) (fun k _ => ?_)
    · have := congrArg Fin.val hac
      simp only [e] at this
      omega
    · have ha' : (a : ℕ) < X.p0 := by
        by_contra hc
        exact ha ⟨⟨a - X.p0, by have := a.2; omega⟩, by simp, Fin.ext (by simp only [e]; omega)⟩
      have : (mat b τ)⁻¹ i a = 0 := hinv i a (by show (a : ℕ) < i; omega)
      rw [this, zero_mul]
    · rw [perFr_pos X x (v j) τ k (e k).2]
  rw [e1]
  exact coord_le X hx hb ho τ _ i

theorem fil_bound {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b)) (τ : X.Ψ)
    {n : ℕ} (v : Fin n → Fin N → E) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (ℓ : Fin X.p0 → ℂ) (k : Fin X.p0), ‖ℓ k‖ ≤ K * ∑ j, ‖∑ i, ℓ i * perFr X x (v j) (conjEmb τ.1) i‖)
    (i : Fin N) (hi : (i : ℕ) < X.p0) : ‖b τ i i‖ ≤ K * ∑ j, (1 + X.maj x τ (Data.emb τ.1 (v j))) := by
  have hp := X.p0_le
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb
  let e : Fin X.p0 → Fin N := fun k => ⟨X.p0 - 1 - k, by have := k.2; omega⟩
  have h1 := h (fun k => b τ (e k) i) ⟨X.p0 - 1 - i, by omega⟩
  have he : e ⟨X.p0 - 1 - i, by omega⟩ = i := Fin.ext (by simp only [e]; omega)
  simp only [he] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hK)
  have hc : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have e1 : ∑ k : Fin X.p0, b τ (e k) i * perFr X x (v j) (conjEmb τ.1) k =
      hermC τ.1 X.Gm (col (mat (rmul x b) τ) i) (Data.emb τ.1 (v j)) := by
    have e2 : mat (rmul x b) τ = mat x τ * mat b τ := rfl
    rw [e2, UnipMove.GraphH.col_mul, Data.mulVec_eq_sum_col, ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left]
    refine Finset.sum_of_injOn e (fun a _ c _ hac => Fin.ext ?_)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun a _ ha => ?_) (fun k _ => ?_)
    · have := congrArg Fin.val hac
      simp only [e] at this
      have := a.2
      have := c.2
      omega
    · have ha' : X.p0 ≤ (a : ℕ) := by
        by_contra hc
        exact ha ⟨⟨X.p0 - 1 - a, by omega⟩, by simp, Fin.ext (by simp only [e]; omega)⟩
      have : col (mat b τ) i a = 0 := (hb τ).2 a i (by show (i : ℕ) < a; omega)
      rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, this, zero_mul]
    · rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left,
        perFr_neg X x (v j) (conjEmb τ.1) hc τ (Formalism.L2.Pj.conjEmb_conjEmb τ.1).symm k (e k).2]
      rfl
  rw [e1]
  refine le_trans (le_of_eq ?_) (coord_le X hx hb ho τ (Data.emb τ.1 (v j)) i)
  set c := (mat (rmul x b) τ)⁻¹ *ᵥ Data.emb τ.1 (v j) with hcdef
  have hv : Data.emb τ.1 (v j) = mat (rmul x b) τ *ᵥ c := by
    rw [hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hy τ).1), Matrix.one_mulVec]
  have hg : ∀ a, hermC τ.1 X.Gm (col (mat (rmul x b) τ) i) (col (mat (rmul x b) τ) a) = if i = a then 1 else 0 := by
    intro a
    have := congrFun (congrFun (ho τ) i) a
    simpa [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.diagonal_apply, ReciprocityTheory.ChartRestriction.G.FD.sgn, hi] using this
  rw [hv, Data.mulVec_eq_sum_col, ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right]
  simp_rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, hg]
  simp

theorem nfac_ortho {y : Frame X.Ψ N} (ho : X.IsOrtho y) (la : Wt X.Ψ N) : X.nfac la y = 1 := by
  have h : ∀ τ i, ‖dmin X.Gm y τ i‖ = 1 := by
    intro τ i
    unfold dmin
    rw [ho τ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rcases ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sgn_sq X.p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) with h | h <;> rw [h] <;> simp
  unfold Data.nfac
  simp [h]

theorem nfac_shift {T : ℝ} {M : ℕ} {γ : GL (Fin N) E} {x : ℂ → Frame X.Ψ N} (h : IsOrbit X T M γ x) (la : Wt X.Ψ N)
    (k : ℤ) : ∀ w : ℂ, T < w.im → X.nfac la (x (w + k * M)) = X.nfac la (x w) := by
  obtain ⟨-, hγ, -, hd, hs⟩ := h
  have one : ∀ w : ℂ, T < w.im → X.nfac la (x (w + M)) = X.nfac la (x w) := by
    intro w hw
    obtain ⟨b, hb, hb1, e⟩ := hs w hw
    rw [e, ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_rightBorel_holds N X la _ (GlobalTheory.MajInv.lact_mem_dom X (X.Γ_stab γ hγ) (hd w hw)) b hb,
      ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_leftAction_holds N X la γ hγ _ (hd w hw)]
    simp [bchar, hb1]
  induction k using Int.induction_on with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    rw [← ih w hw, ← one (w + ((k : ℤ) : ℂ) * M) (by simpa using hw)]
    congr 2
    push_cast
    ring
  | pred k ih =>
    intro w hw
    rw [← ih w hw, ← one (w + ((-(k : ℤ) - 1 : ℤ) : ℂ) * M) (by simpa using hw)]
    congr 2
    push_cast
    ring

theorem maj_strip {T : ℝ} {x : ℂ → Frame X.Ψ N} (hx : DifferentiableOn ℂ x {w | T < w.im})
    (hd : ∀ w : ℂ, T < w.im → x w ∈ X.dom) (M : ℝ) (τ : X.Ψ) (u : Fin N → ℂ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w : ℂ, T + 1 ≤ w.im → 1 ≤ w.im → |w.re| ≤ M → 1 + X.maj (x w) τ u ≤ D * w.im ^ 2 := by
  set w0 : ℂ := ⟨0, T + 1⟩ with hw0
  have h0 : T < w0.im := by simp [hw0]
  have hm : 0 ≤ X.maj (x w0) τ u := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X (hd w0 h0) τ u
  refine ⟨1 + (2 + M ^ 2 + (1 + |T + 1|) ^ 2) * X.maj (x w0) τ u, by positivity, fun w h1 h2 h3 => ?_⟩
  have h := GlobalTheory.T.majorant_harnack_holomorphic_half_plane E N X T x hx hd w0 w h0 (by linarith) τ u
  have e0 : w0.im - T = 1 := by simp [hw0]
  rw [e0, one_mul] at h
  have e1 : ‖w0 - w‖ ^ 2 = w.re ^ 2 + (T + 1 - w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hw0]
    ring
  have hs : 1 ≤ w.im ^ 2 := by nlinarith
  have e2 : w.re ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have e3 : (T + 1 - w.im) ^ 2 ≤ ((1 + |T + 1|) * w.im) ^ 2 := by
    have a1 := le_abs_self (T + 1)
    have a2 := neg_abs_le (T + 1)
    have a3 := abs_nonneg (T + 1)
    exact sq_le_sq' (by nlinarith) (by nlinarith)
  have e4 : ‖w0 - w‖ ^ 2 / (w.im - T) ≤ ‖w0 - w‖ ^ 2 := div_le_self (sq_nonneg _) (by linarith)
  have e5 : 2 + ‖w0 - w‖ ^ 2 / (w.im - T) ≤ (2 + M ^ 2 + (1 + |T + 1|) ^ 2) * w.im ^ 2 := by
    rw [mul_pow] at e3
    nlinarith [sq_nonneg M]
  have e6 := mul_le_mul_of_nonneg_right e5 hm
  nlinarith

end GlobalTheory.OrbitNfac

namespace GlobalTheory


end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxDefsUp
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

abbrev refUp (Z : w.Lt) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) : Refill Z :=
  { Refill.ofDiv Z N h with S := S' }


open Formalism.BasicNotions.DivX (md) in
set_option maxHeartbeats 1000000 in
def divBack {Z : w.Lt} {S' : SStage B w.C Z.W} {N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V} {h : B.Word → ℝ}
    (X : DivX (w.D (SRe.upL Z S' N h))) : DivX (w.D Z) :=
  { X with md := fun S κ p _ la z => { md X S κ p la z with } }


set_option maxHeartbeats 1000000 in
theorem grpAt_up {Z : w.Lt} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (x : GrpAt (w.st Z) w.I) : GrpAt (w.st (SRe.upL Z S' N h)) w.I :=
  ⟨(by with_unfolding_all exact (x.pl :)), (by with_unfolding_all exact (x.idem :)), (by with_unfolding_all exact (x.cen :))⟩


set_option maxHeartbeats 1000000 in
theorem muIsW_up {Z : w.Lt} {Wt : Set B.places.Pl} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V)
    (h : B.Word → ℝ) (x : V4.MuIsW (w.st Z) f T Wt w.I.xi) : V4.MuIsW (w.st (SRe.upL Z S' N h)) f T Wt w.I.xi := by
  exact
    { inj := by with_unfolding_all exact (x.inj :)
      range := by with_unfolding_all exact (x.range :)
      mu0 := by with_unfolding_all exact (x.mu0 :)
      star := by with_unfolding_all exact (x.star :)
      star' := by with_unfolding_all exact (x.star' :)
      tw := by with_unfolding_all exact (x.tw :)
      on := by with_unfolding_all exact (x.on :)
      off := by with_unfolding_all exact (x.off :)
      sub := by with_unfolding_all exact (x.sub :)
      supp := by with_unfolding_all exact (x.supp :) }


set_option maxHeartbeats 1000000 in
theorem rowInt_up {Z : w.Lt} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (x : GlobalTheory.PerQ.RowInt w.I w.l Z) : GlobalTheory.PerQ.RowInt w.I w.l (SRe.upL Z S' N h) :=
  ⟨(by with_unfolding_all exact (x.ref :)), (by with_unfolding_all exact (x.tw :))⟩


set_option maxHeartbeats 1000000 in
theorem idxDefs_up {Z : w.Lt} {S' : SStage B w.C Z.W} {N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V} {h : B.Word → ℝ}
    (Y : DivX (w.D (SRe.upL Z S' N h))) (hI : IdxDefs (w.D Z) (divBack Y)) : IdxDefs (w.D (SRe.upL Z S' N h)) Y :=
  ⟨(by with_unfolding_all exact (hI.Ij_def :)), (by with_unfolding_all exact (hI.jw_def :))⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalFramesNearAdelicAtBadPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalFramesNearAdelicAtBadPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT.Approx

open scoped TensorProduct

variable {F E : Type} {_iF : Field F} [NumberField F] {_iE : Field E} [NumberField E] {_iA : Algebra F E} {n : ℕ}

theorem comp_mul_rat (P : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) :
    ((k⁻¹ * GlobalTheory.TwU.ratA F γ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _).map (adAt F P) =
      ((Formalism.UG.bc (adAt F P) k)⁻¹ : GL (Fin n) (P.adicCompletion E)).1 * γ.1.map (algebraMap E (P.adicCompletion E)) := by
  rw [← map_inv, Units.val_mul, Matrix.map_mul]
  congr 1
  show (γ.1.map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (adAt F P) = _
  rw [Matrix.map_map]
  congr 1
  funext x
  exact adAt_inclE F P x

theorem comp_rat_mul (P : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) :
    (((GlobalTheory.TwU.ratA F γ)⁻¹ * k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _).map (adAt F P) =
      (γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * (Formalism.UG.bc (adAt F P) k : GL (Fin n) (P.adicCompletion E)).1 := by
  rw [← map_inv, Units.val_mul, Matrix.map_mul]
  congr 1
  show ((γ⁻¹).1.map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (adAt F P) = _
  rw [Matrix.map_map]
  congr 1
  funext x
  exact adAt_inclE F P x

end GlobalTheory.Mem.Col2.AdT.Approx

namespace GlobalTheory.Mem.Col2.AdT

theorem frNear_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (n : ℕ) (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb := by
  intro B X I hOk l Z a n k
  have key : ∀ P : SBof I a, ∃ γ : GL (Fin n) (I.rec7 l Z).host.E,
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (k⁻¹ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F γ) ∧
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F γ)⁻¹ * k) := by
    intro P
    obtain ⟨γ, hγ⟩ := GlobalTheory.T.numberFieldGL_dense_in_completionGL_two_sided B.fields.E P.1 n ((I.cst a).D P) (Formalism.UG.bc (adAt B.host.F P.1) k)
    refine ⟨γ, ?_, ?_⟩
    · rw [(GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a n ((I.cst a).D P) P _).2.2]
      intro r s
      have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) _ => M r s) (Approx.comp_mul_rat P.1 k γ)
      simp only [Matrix.map_apply] at h1
      have h2 := (hγ r s).1
      rw [Matrix.sub_apply] at h2
      convert h2 using 3
      exact h1
    · rw [(GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a n ((I.cst a).D P) P _).2.2]
      intro r s
      have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) _ => M r s) (Approx.comp_rat_mul P.1 k γ)
      simp only [Matrix.map_apply] at h1
      have h2 := (hγ r s).2
      rw [Matrix.sub_apply] at h2
      convert h2 using 3
      exact h1
  choose fb hfb using key
  exact ⟨fb, hfb⟩

end GlobalTheory.Mem.Col2.AdT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalFramesNearAdelicAtBadPrimesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_frames_near_adelic_at_bad_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (n : ℕ) (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb := by
  first | exact @GlobalTheory.Mem.Col2.AdT.frNear_exists | exact GlobalTheory.Mem.Col2.AdT.frNear_exists | (intros; apply GlobalTheory.Mem.Col2.AdT.frNear_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendsto
open GlobalTheory.ShFam.BdArc Filter Topology

namespace GlobalTheory.ShFam.BdArc

theorem exists_complexPoint_of_notMem {F A : Type} [Field F] [CommRing A] [Algebra F A] [Algebra.FiniteType F A]
    (σ : F →+* ℂ) (P : Ideal A) [hP : P.IsPrime] {s : A} (hs : s ∉ P) :
    ∃ ψ : A →+* ℂ, ψ.comp (algebraMap F A) = σ ∧ (∀ x ∈ P, ψ x = 0) ∧ ψ s ≠ 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := F)
  have hj : P.jacobson = P := IsJacobsonRing.out inferInstance hP.isRadical
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf] at hs
  push Not at hs
  obtain ⟨M, ⟨hle, hM⟩, hsM⟩ := hs
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite F (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ M)
  let _ : Algebra F ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(κ.comp (Ideal.Quotient.mkₐ F M)).toRingHom, ?_, fun x hx => ?_, ?_⟩
  · ext x
    exact (κ.comp (Ideal.Quotient.mkₐ F M)).commutes x
  · show κ (Ideal.Quotient.mk M x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]
  · show κ (Ideal.Quotient.mk M s) ≠ 0
    rw [map_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hsM

theorem dvd_or_dvd_of_height_eq_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) (a b : A) :
    (∃ s, s ∉ P ∧ a ∣ s * b) ∨ ∃ s, s ∉ P ∧ b ∣ s * a := by
  have := GlobalTheory.isDiscreteValuationRing_of_height_eq_one P hP (Localization.AtPrime P)
  have key : ∀ x y : A, algebraMap A (Localization.AtPrime P) x ∣ algebraMap A _ y → ∃ s, s ∉ P ∧ x ∣ s * y := by
    rintro x y ⟨c, hc⟩
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj P.primeCompl c
    refine ⟨d, d.2, n, ?_⟩
    apply IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
    simp only at hnd
    rw [map_mul, map_mul, hc, ← hnd]
    ring
  exact (ValuationRing.dvd_total (algebraMap A (Localization.AtPrime P) a) (algebraMap A _ b)).imp (key a b) (key b a)

theorem exists_eq_mul_pow_of_tendsto_zero : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (σ : F →+* ℂ) (p a : A) (m : ℕ), p ≠ 0 → (∀ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = σ) → ψ 0 p = 0 → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0) → Tendsto (fun u => ψ u a / ψ u (p ^ m)) (𝓝[≠] 0) (𝓝 0)) → ∃ b : A, a = b * p ^ m ∧ b ∈ (Ideal.span {p}).radical := by
  intro F A _ _ _ _ hsm σ p a m hp h
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth F A
  have key : ∀ (P : Ideal A) [P.IsPrime], p ∈ P → ∀ s, s ∉ P → ¬ a ∣ s * p ^ m := by
    rintro P _ hpP s hs ⟨t, ht⟩
    obtain ⟨ψ₀, hσ, hP0, hs0⟩ := exists_complexPoint_of_notMem σ P hs
    obtain ⟨ψ, r, hhol, h0, hσ', hne⟩ := GlobalTheory.T.exists_holomorphic_arc_smooth_algebra_nonvanishing F A hsm ψ₀ p hp
    have hlim := h ψ r hhol (fun u hu => (hσ' u hu).trans hσ) (by rw [h0]; exact hP0 p hpP) hne
    have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hhol.1
    have hc : ∀ x, Tendsto (fun u => ψ u x) (𝓝[≠] 0) (𝓝 (ψ₀ x)) := fun x => by
      rw [← h0]
      exact (((hhol.2 x).differentiableAt hball).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have h1 := hlim.mul (hc t)
    rw [zero_mul] at h1
    have h2 : Tendsto (fun u => ψ u s) (𝓝[≠] 0) (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
      have hpu : ψ u (p ^ m) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (hne u hu hu0)
      rw [div_mul_eq_mul_div, ← map_mul, ← ht, map_mul, mul_div_cancel_right₀ _ hpu]
    exact hs0 (tendsto_nhds_unique (hc s) h2)
  obtain ⟨b, hb⟩ : p ^ m ∣ a := by
    refine GlobalTheory.dvd_of_forall_height_eq_one (pow_ne_zero m hp) fun P hP h1 hpm => ?_
    refine (dvd_or_dvd_of_height_eq_one P h1 (p ^ m) a).resolve_right ?_
    rintro ⟨s, hs, hd⟩
    exact key P (hP.mem_of_pow_mem m hpm) s hs hd
  refine ⟨b, by rw [hb, mul_comm], ?_⟩
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hle, hP⟩
  by_contra hbP
  exact key P (hle (Ideal.mem_span_singleton_self p)) b hbP ⟨1, by rw [hb]; ring⟩

end GlobalTheory.ShFam.BdArc
end
