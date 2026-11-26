module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepFUnique
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ChartOfPoint
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

theorem chart_of_point {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (h : ∀ y I, Good L y I → sval s (𝟙 Y) y I = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y I) :
    ∀ j, s.f j = ∑ i, resTop _ (b i) * (t i).f j := by
  intro j
  refine fn_ext fun y hy0 => ?_
  have hy : y ∈ LB.wchart L φ j := hy0
  choose I hI using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
  have hIy : Good L y I := hI
  have mm := hIy.mem φ (𝟙 _)
  have T0 := sec_trans s (𝟙 _) y hy mm
  set τ := (trF φ ε (𝟙 _) y j (fun k => I (𝟙 _ ≫ φ k))).val with hτ
  have RHS : gs (𝟙 _) y (LB.wchart L φ j) (∑ i, resTop (LB.wchart L φ j) (b i) *
      (show Γ(Y, LB.wchart L φ j) from (t i).f j)) =
      τ * ∑ i, gs (𝟙 _) y ⊤ (b i) * sval (t i) (𝟙 _) y I := by
    rw [gs_sum _ y _ hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ y _ hy, gs_res _ y le_top hy, sec_trans (t i) (𝟙 _) y hy mm, hτ]
    exact mul_left_comm _ _ _
  exact T0.trans ((congrArg (fun x => τ * x) (h y I hIy)).trans RHS.symm)

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem hformF (k : ℕ) (ρ : D.toPre.X) :
    FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F ρ) (DegPre.famε k) := by
  have e : (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) = DegPre.famφ D.toPre F ρ := by
    funext i
    fin_cases i
    · simp [DegPre.famφ, DegPre.famφB]
    · show (DegPre.prB D.toPre F).left ≫ (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ D.toPre.c ρ)).left =
        (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c ρ)).left
      rw [← Over.comp_left]
      congr 1
      simp only [padd]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ D.toPre.c ρ).left = (toUnit _ ≫ D.toPre.c ρ).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left =
        (toUnit _ ≫ η[D.toPre.P.A]).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
  intro U _ h
  rw [e]

theorem hformF' (k : ℕ) (ρ : D.toPre.X) :
    FormEq (DegPre.famφ D.toPre F ρ) (DegPre.famε k)
      (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) (DegPre.famε k) := by
  have e : (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) = DegPre.famφ D.toPre F ρ := by
    funext i
    fin_cases i
    · simp [DegPre.famφ, DegPre.famφB]
    · show (DegPre.prB D.toPre F).left ≫ (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ D.toPre.c ρ)).left =
        (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c ρ)).left
      rw [← Over.comp_left]
      congr 1
      simp only [padd]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ D.toPre.c ρ).left = (toUnit _ ≫ D.toPre.c ρ).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left =
        (toUnit _ ≫ η[D.toPre.P.A]).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
  intro U _ h
  rw [e]

theorem coordsF {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J) :
    (∀ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)), ∃ c : Fin m → F,
      ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        sval t (𝟙 _) y J = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J) ∧
    (∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0) := by
  have hL := D.toPre.P.isLB
  have eT : Over.mk (Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V)))) = TF (R := V) F := by
    rw [← TF_hom]; rfl
  have hbF' := hb F (algVF (F := F) (V := V))
  rw [eT] at hbF'
  let b' := fun i => pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) (b i)
    (snd (TF (R := V) F) D.toPre.P.A).left
  have hB := hbF' b' (fun i j => rfl)
  have hb' : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (b' i) (𝟙 _) y J = sval (bF i) (𝟙 _) y J := fun i y J hJ => by
    rw [hbF i y J hJ]
    exact (sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.id_comp])
  refine ⟨fun t => ?_, fun c hc => ?_⟩
  · obtain ⟨t', ht'⟩ := exists_sec hL (hformF' k ρ) t
    obtain ⟨r, hr, -⟩ := hB t'
    choose c hc using fun i => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (r i)
    refine ⟨c, fun y J hJ => ?_⟩
    rw [← ht' _ (𝟙 _) y J hJ, sval_lin (fun i => (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom (r i)) b' hr (𝟙 _) y hJ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb' i y J hJ, gF, RingHom.comp_apply, ← hc i]
  · let z0 : LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (TF (R := V) F) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
      (DegPre.famε k)) := SecOps.secZero
    have r1 := chart_of_point hL z0 (fun i => (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) b' (fun y I hI => by
        rw [sval_zero_of (fun j => rfl) _ y I (hI.mem _ _), ← hc y I hI]
        exact Finset.sum_congr rfl fun i _ => by rw [hb' i y I hI]; rfl)
    have r0 : ∀ j, z0.f j = ∑ i, resTop _ ((fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom 0) * (b' i).f j := fun j => by
      simp only [map_zero, MulZeroClass.zero_mul, Finset.sum_const_zero]; rfl
    obtain ⟨r, -, hu⟩ := hB z0
    have e := (hu _ r1).trans (hu _ r0).symm
    funext i
    have hi : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i) = 0 := congrFun e i
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom hi
    simpa using this

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem gs_sub {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs, dif_pos h, map_sub]

def RepF {k : ℕ} {ρ : D.toPre.X} {m : ℕ}
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))) (c : Fin m → F) : Prop :=
  ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
    sval t (𝟙 _) y J = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J

theorem coordsO {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J)
    (σ : D.toPre.SecB k ρ) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hσF : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval σF (𝟙 _) y J = sval σ (DegPre.prB D.toPre F).left y J) :
    ∃ c : Fin m → F, (∀ i, (0 : WithTop ℚ) ≤ v (c i)) ∧ RepF bF σF c := by
  let bO := fun i => pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) (b i)
    (snd (TO hϖ hv) D.toPre.P.A).left
  have hBO := hb (Ov v) (fO v hϖ hv) bO (fun i j => rfl)
  obtain ⟨r, hr, -⟩ := hBO (pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) σ
    (snd (TO hϖ hv) D.toPre.P.A).left)
  refine ⟨fun i => ιr (v := v) (r i), fun i => v_ιr _, fun y J hJ => ?_⟩
  have e := sval_lin (fun i => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (r i)) bO hr (jO hϖ hv (D := D)).left y hJ
  rw [sval_pullSec _ _ _ _ _ y hJ, jO_snd] at e
  rw [hσF y J hJ, e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have g := gs_jO hϖ hv (D := D) (𝟙 _) y (r i)
  rw [Category.id_comp] at g
  rw [g, hbF i y J hJ]
  show _ * sval (pullSec _ _ _ (b i) _) _ y J = _
  rw [sval_pullSec _ _ _ _ _ y hJ, jO_snd]

theorem repF_unique {k : ℕ} {ρ : D.toPre.X} {m : ℕ}
    {bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))}
    (hU : ∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0)
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))} {c c' : Fin m → F}
    (h : RepF bF t c) (h' : RepF bF t c') : c = c' := by
  have hsub : ∀ (y : (DegPre.BF D.toPre F).left) (a b : Γ((DegPre.BF D.toPre F).left, ⊤)),
      gs (𝟙 _) y ⊤ (a - b) = gs (𝟙 _) y ⊤ a - gs (𝟙 _) y ⊤ b :=
    fun y a b => gs_sub _ y ⊤ (by first | trivial | simp) a b
  have h0 := hU (c - c') (fun y J hy => by
    have e1 := h y J hy
    have e2 := h' y J hy
    simp only [Pi.sub_apply, map_sub, hsub, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp h0

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem fam_sum_f {k : ℕ} {Ix : Type} [Fintype Ix] (c : Ix → F) (s : Ix → Fam D.toPre F k) (α : D.toPre.X) (j) :
    ((∑ i, c i • s i).s α).f j = ∑ i, resTop _ (gF D.toPre F (c i)) * ((s i).s α).f j := by
  classical
  have key : ∀ t : Finset Ix, ((∑ i ∈ t, c i • s i).s α).f j =
      ∑ i ∈ t, resTop _ (gF D.toPre F (c i)) * ((s i).s α).f j := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_f, smul_f, ih]
  exact key Finset.univ

theorem fam_eq_zero (hG : GlobalFnsSt) {k : ℕ} (P : D.toPre.X → Prop) (hP : ∀ χ, ∃ α mu, P α ∧ α + k • mu = χ)
    (s : Fam D.toPre F k) (h0 : ∀ α, P α → ∀ j, (s.s α).f j = 0) : s = 0 := by
  have hL := D.toPre.P.isLB
  refine DVR.fam_ext fun χ j => ?_
  obtain ⟨α, mu, hα, rfl⟩ := hP χ
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D.toPre) (F := F) hG k mu α
  have hrel := s.fe mu α u hu hc
  refine sec_ext_val hL (s' := (0 : Fam D.toPre F k).s (α + k • mu)) (fun y J hJ => ?_) j
  rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ, sval_zero_of (h0 α hα) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul, sval_zero_of (fun j => rfl) _ y J (hJ.mem _ _)]

theorem vge_coords {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J)
    (hU : ∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0)
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))} {c : Fin m → F}
    (hc : RepF bF t c) {r : ℚ} (ht : VGe D F v k ρ t r) : ∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i) := by
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := ht
  have hσ : ∀ l, ∃ c' : Fin m → F, (∀ i, (0 : WithTop ℚ) ≤ v (c' i)) ∧ RepF bF (σF l) c' := fun l =>
    coordsO hϖ hv b hb bF hbF (σ l) (σF l) fun y J hJ => by
      rw [← secScal_sval (hscal l) (𝟙 _) y hJ, Category.id_comp]
  choose c' hc'v hc' using hσ
  have hrep : RepF bF t (fun i => ∑ l, a l * c' l i) := fun y J hJ => by
    rw [sval_lin (fun l => gF D.toPre F (a l)) σF (fun j => hsum j) (𝟙 _) y hJ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, gs_sum _ y ⊤ trivial, gs_mul _ y ⊤ trivial, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hc' l y J hJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e := repF_unique hU hc hrep
  intro i
  rw [e]
  refine AddValuation.map_le_sum v fun l _ => ?_
  rw [AddValuation.map_mul]
  calc ((r : ℚ) : WithTop ℚ) = (r : WithTop ℚ) + 0 := (add_zero _).symm
    _ ≤ v (a l) + v (c' l i) := add_le_add (hva l) (hc'v l i)

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
