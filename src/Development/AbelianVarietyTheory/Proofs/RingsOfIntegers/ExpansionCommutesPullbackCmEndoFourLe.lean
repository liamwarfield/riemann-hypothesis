module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecIsMulOfSval
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEInst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionCommutesPullbackCmEndoFourLe
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSectionGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSectionGenericFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericUnitValue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ₁ : K → (Y' ⟶ X)} {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)} (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hj : ∀ q : K ⊕ K', Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k)) q =
      J (r ≫ Sum.elim φ₁ (fun k => h ≫ φ₂ k) q) := by
    intro q
    cases q with
    | inl q => rfl
    | inr q => exact congrArg J (Category.assoc _ _ _)
  have key := H (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k))
    (fun q₁ q₂ hq => by rw [hj, hj, hq])
  have m₂ := hJ.mem φ₂ (r ≫ h)
  have m : r z ∈ L.wchart φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      L.wchart (fun k => h ≫ φ₂ k) (fun k => J ((r ≫ h) ≫ φ₂ k)) := by
    refine ⟨hJ.mem φ₁ r, ?_⟩
    have e₃ : (fun k => J ((r ≫ h) ≫ φ₂ k)) = (fun k => J (r ≫ (fun k => h ≫ φ₂ k) k)) :=
      funext fun k => congrArg J (Category.assoc _ _ _)
    rw [e₃]
    exact hJ.mem (fun k => h ≫ φ₂ k) r
  have e := congrArg (gs r z _) key
  rw [gs_mul r z _ m] at e
  unfold resTop at e
  rw [gs_res r z _ m, gs_res r z _ m] at e
  have p := gs_pull r h z _ m₂ (s₂.f fun k => J ((r ≫ h) ≫ φ₂ k))
  exact p.symm.trans (e.trans (congrArg (gs r z ⊤ c * ·) (gs_res r z _ m _)))

theorem isUnit_cst_generic {V : Type} [CommRing V] [IsDomain V] (y : Spec (CommRingCat.of (FractionRing V)))
    {c : V} (hc : c ≠ 0) : IsUnit (cst (jK V) y c) := by
  have hK : IsUnit (algebraMap V (FractionRing V) c) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)).isUnit
  obtain ⟨w, hw⟩ := hK
  rw [show cst (jK V) y c = cst (𝟙 _) y (algebraMap V (FractionRing V) c) from H1.gs_spec _ y c, ← hw]
  exact ⟨⟨cst (𝟙 _) y (w : FractionRing V), cst (𝟙 _) y (↑w⁻¹ : FractionRing V),
    by rw [← H1.cst_mul, Units.mul_inv, H1.cst_one], by rw [← H1.cst_mul, Units.inv_mul, H1.cst_one]⟩, rfl⟩

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

lemma unitK_fst : (unitK (G := G)) ≫ pullback.fst G.hom (jK V) = jK V ≫ eSec G := by
  simp only [unitK, pullback.lift_fst]

lemma gs_unitK_scal (y : Spec (CommRingCat.of (FractionRing V))) (c : V) :
    gs (unitK (G := G)) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) c) = cst (jK V) y c := by
  have hsec : (unitK (G := G)) ≫ pullback.snd G.hom (jK V) = 𝟙 _ := by
    simp only [unitK, pullback.lift_snd]
  unfold scal cst
  refine (gs_pull (unitK (G := G)) (pullback.snd G.hom (jK V) ≫ jK V) y ⊤ trivial _).trans ?_
  rw [← Category.assoc, hsec, Category.id_comp]

end

theorem value_at_generic_unit : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∀ (y : Spec (CommRingCat.of (FractionRing V))) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u unitK y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))).val * Geo.Tor.sval s unitK y J := by
  intro hL V _ _ _ E _ _ _ H t P a N hN hN0
  intro k s F u F' hs hu hpull y J hJ
  let _ := H.starRing
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  obtain ⟨X, hX, hXc⟩ := exists_XB P.D P.D.toPre.P.isLB P.oD H.w0 uΨ huΨ a N hN hN0 1
  obtain ⟨c, σ'', τ, hc, hsτ, huσ, hth⟩ :=
    GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc k s F u F' hs hu hpull
  have hv := GlobalTheory.UnitValue.value_at_unit_section V E H t P a N hN hN0 X hX hXc k σ'' τ hth _ (jK V) y J hJ
  have e₁ := sval_of_secScal huσ unitK y hJ
  have e₂ := sval_of_secScal hsτ unitK y hJ
  rw [unitK_fst, gs_unitK_scal] at e₁ e₂
  rw [e₁, e₂] at hv
  apply (isUnit_cst_generic y hc).mul_left_cancel
  rw [hv]
  ring

end GlobalTheory.GenericUnitValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSectionGenericFibreStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.value_at_unitSection_genericFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∀ (y : Spec (CommRingCat.of (FractionRing V))) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u unitK y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))).val * Geo.Tor.sval s unitK y J := by
  first | exact @GlobalTheory.GenericUnitValue.value_at_generic_unit | exact GlobalTheory.GenericUnitValue.value_at_generic_unit | (intros; apply GlobalTheory.GenericUnitValue.value_at_generic_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionCommutesPullbackCmEndoFourLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullExpansion

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_eq_mul_of_id {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb L φ ε)) (c : Γ(Y, ⊤))
    (h : ∀ y J, Good L y J → sval a (𝟙 Y) y J = gs (𝟙 Y) y ⊤ c * sval b (𝟙 Y) y J)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) :
    sval a r z J = gs r z ⊤ c * sval b r z J := by
  have key : ∀ j : K → L.ι, a.f j =
      (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from b.f j) := fun j =>
    fn_ext (V := LB.wchart L φ j) fun y hy => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have hI' : Good L y I := hI
      refine Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y le_top hy c)
        (sec_trans b (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))))).symm
      refine (sec_trans a (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))).trans ?_
      exact (congrArg _ (h y I hI')).trans (mul_left_comm _ _ _)
  have hm := hJ.mem φ r
  exact (congrArg (gs r z _) (key _)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg (· * sval b r z J) (gs_res r z le_top hm c)))

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

theorem unitK_snd : unitK (G := G) ≫ pullback.snd G.hom (jK V) = 𝟙 _ := pullback.lift_snd _ _ _

theorem unitK_endK (f : G ⟶ G) [IsMonHom f] : unitK (G := G) ≫ endK f = unitK := by
  have he : eSec G ≫ f.left = eSec G := by
    simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply pullback.hom_ext
  · simp only [unitK, endK, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact congrArg (jK V ≫ ·) he
  · simp only [unitK, endK, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

end

theorem expands_pull_of_four_le : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, 4 ≤ k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ s' : P.U.SecK (k * N), IsPullByEnd P.U (t.act.act a) k N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a k N F F' := by
  intro hLaws V _ _ _ E _ _ _ H t P a N hN hN0
  letI := H.starRing
  intro k hk s F hs s' hs'
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hM : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  have hL : P.U.LG.L.IsLB := P.U.LG.isLB
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN0
  choose Fx hFx hFu using (P.U.expand k hk1).1
  choose Fp hFp using fun F : Fam P.D.toPre (FractionRing V) k =>
    exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 k F
      (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 k F)
  choose sp hsp _ using (P.U.expand (k * N) hkN).2
  obtain rfl : F = Fx s := hFu s F hs
  refine ⟨Fp (Fx s), ?_, hFp _⟩
  obtain ⟨u, hu, hn, hrel⟩ := hs'
  haveI : IsMonHom (t.act.act a) := t.act.hom a
  have hF : FormEq (fun _ : Fin 1 => gK (G := t.G)) (fun _ => ((k * N : ℕ) : ℤ))
      (Sum.elim (fun _ : Fin 1 => endK (t.act.act a) ≫ gK) ![gK, endK (t.act.act a) ≫ gK])
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := fun U _ g => by
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨c, hc⟩ := GlobalTheory.SectionRatio.ratio_glue _ _ P.U.LG.L hL _ _ _ _ _ (fun _ : Fin 1 => gK) _ _ _
    (endK (t.act.act a)) hF u hu (P.U.SecK k) (fun s₀ => sp (Fp (Fx s₀))) (fun s₀ => s₀)
    (fun y J hJ => GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _ _ y J hJ)
    (fun i i' y J hJ => by
      have e := GlobalTheory.T.mixed_cross_identity_genericFibre hLaws V E H t P a N hN hN0 k i _ _ _ (hFx i) (hsp _) (hFp _) k i' _ _ _ (hFx i') (hsp _)
        (hFp _) 1 1 rfl y J hJ
      simpa only [pow_one] using e)
  obtain ⟨c₀, rfl⟩ := (GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ P.D P.A t.G
    P.U.toUnifPre).1 c
  have hF' := fun (U : Type) (i : CommGroup U) g => (@hF U i g).symm
  have hc₀ : c₀ = 1 := fn_ext (V := ⊤) fun y _ => by
    choose J hJ using fun χ : Spec (CommRingCat.of (FractionRing V)) ⟶ t.G.left => exists_chart hL (χ y)
    have hJ' : Good P.U.LG.L y J := hJ
    obtain ⟨s₀, hs₀⟩ := GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _
      unitK y J hJ'
    obtain ⟨b, hb⟩ := exists_sec hL hF' (pullMulSec s₀ (endK (t.act.act a)) u hu)
    have e₁ := sval_eq_mul_of_id hL (sp (Fp (Fx s₀))) b _ (fun y J hJ => by
      rw [hb _ _ y J hJ, sval_pullMulSec _ _ u hu _ y hJ, Category.id_comp]
      exact hc s₀ y J hJ) unitK y J hJ'
    rw [hb _ _ y J hJ', sval_pullMulSec _ _ u hu _ y hJ', unitK_endK] at e₁
    have e₂ := GlobalTheory.T.value_at_unitSection_genericFibre hLaws V E H t P a N hN hN0 k s₀ _ _ _ (hFx s₀) (hsp _) (hFp _) y J hJ'
    have e₃ : val u unitK y J = val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1)) := by
      have e := val_corr hJ' hn (𝟙 _)
      rw [val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp, val_pow] at e
      exact e
    have e₄ : gs unitK y ⊤ ((pullback.snd t.G.hom (jK V)).appTop.hom c₀) = gs (𝟙 _) y ⊤ c₀ :=
      (gs_pull unitK (pullback.snd t.G.hom (jK V)) y ⊤ trivial c₀).trans (by rw [unitK_snd])
    rw [e₂, e₃, e₄] at e₁
    rw [gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one]
    refine (hs₀.mul (Units.isUnit (val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))))).mul_right_cancel ?_
    rw [← e₁, _root_.one_mul, mul_comm]
  have hss : s' = sp (Fp (Fx s)) := SecOps.sec_ext (sec_ext_val hL fun y J hJ => by
    rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ, Category.id_comp, hc s y J hJ, hc₀, map_one,
      gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one, _root_.one_mul])
  rw [hss]
  exact hsp _

end GlobalTheory.PullExpansion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionCommutesPullbackCmEndoFourLeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, 4 ≤ k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ s' : P.U.SecK (k * N), IsPullByEnd P.U (t.act.act a) k N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a k N F F' := by
  first | exact @GlobalTheory.PullExpansion.expands_pull_of_four_le | exact GlobalTheory.PullExpansion.expands_pull_of_four_le | (intros; apply GlobalTheory.PullExpansion.expands_pull_of_four_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsBoxSecKOfPull
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericBoxSpan

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange GlobalTheory.BoxExpansion

section General

variable {X X' Γ Γ' Y Y' E E' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB Γ} {M' : LB Γ'}
  {f₁ : Y ⟶ X} {f₂ : Y ⟶ Γ}

def Moves (w : LB.Iso (L.pull f₁) (M.pull f₂)) (k : ℕ) {g : E ⟶ X} (h : Y ⟶ E)
    (t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => (k : ℤ))))
    (s : LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J I), Good L z J → Good M z I →
    sval s r z I = (pw w r z (J (r ≫ f₁)) (I (r ≫ f₂)) ^ k).val * sval t (r ≫ h) z J

theorem exists_moves (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull f₁) (M.pull f₂)} (hw : w.IsGen) (k : ℕ)
    {g : E ⟶ X} (h : Y ⟶ E) (e : h ≫ g = f₁) (n : E ⟶ Y) (hn : n ≫ h = 𝟙 _) (hn' : h ≫ n = 𝟙 _) :
    (∀ t, ∃ s, Moves w k (g := g) h t s) ∧ ∀ s, ∃ t, Moves w k (g := g) h t s := by
  have key : ∀ g₂ : Y ⟶ Γ, 𝟙 Y ≫ f₂ = g₂ →
      (∀ a, ∃ b, GeneratorPullback.IsoRelM L M f₁ f₂ w (𝟙 Y) k g h a g₂ (𝟙 _) b) ∧
      ∀ b, ∃ a, GeneratorPullback.IsoRelM L M f₁ f₂ w (𝟙 Y) k g h a g₂ (𝟙 _) b := by
    rintro _ rfl
    obtain ⟨i₁, i₂⟩ := isoRelM_bijective (k := k) (m := 𝟙 Y) (g₁ := g) (h₁ := h) hL hM hw
      (e.trans (Category.id_comp _).symm) n hn hn'
    exact ⟨fun a => (i₁ a).exists, fun b => (i₂ b).exists⟩
  obtain ⟨i₁, i₂⟩ := key f₂ (Category.id_comp _)
  have val : ∀ a b, GeneratorPullback.IsoRelM L M f₁ f₂ w (𝟙 Y) k g h a f₂ (𝟙 _) b → Moves w k h a b := by
    intro a b H Z r z J I hJ hI
    have := isoRel_val H r z hJ hI
    simpa only [Category.comp_id] using this
  exact ⟨fun t => (i₁ t).imp fun s hs => val _ _ hs, fun s => (i₂ s).imp fun t ht => val _ _ ht⟩

variable {j : ℕ} {pr : Fin j → (X' ⟶ X)} {qr : Fin j → (Γ' ⟶ Γ)} {f₁' : Y' ⟶ X'} {f₂' : Y' ⟶ Γ'}
  {ρ : Fin j → (Y' ⟶ Y)}

theorem comb_box {F : Type} [CommRing F] (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB) (hM' : M'.IsLB)
    (e₁ : ∀ i, f₁' ≫ pr i = ρ i ≫ f₁) (e₂ : ∀ i, f₂' ≫ qr i = ρ i ≫ f₂)
    (wA : LB.Iso L' (LB.LinComb L pr (fun _ => 1))) (wL : LB.Iso M' (LB.LinComb M qr (fun _ => 1)))
    (w : LB.Iso (L.pull f₁) (M.pull f₂)) (w' : LB.Iso (L'.pull f₁') (M'.pull f₂')) (u : Γ(Y', ⊤)ˣ)
    (hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (a : Fin j → L.ι) (a' : L'.ι) (b : Fin j → M.ι) (b' : M'.ι),
      (∀ i, pr i (f₁' (r z)) ∈ L.U (a i)) → f₁' (r z) ∈ L'.U a' → (∀ i, qr i (f₂' (r z)) ∈ M.U (b i)) →
      f₂' (r z) ∈ M'.U b' →
      bw wL (r ≫ f₂') z b b' * pw w' r z a' b' =
        gm r z ⊤ u * ((∏ i, pw w (r ≫ ρ i) z (a i) (b i)) * bw wA (r ≫ f₁') z a a'))
    {k : ℕ} {g : E ⟶ X} {g' : E' ⟶ X'} {h : Y ⟶ E} {h' : Y' ⟶ E'} {κ : Fin j → (E' ⟶ E)}
    {π : E' ⟶ Spec (CommRingCat.of F)} {π' : Y' ⟶ Spec (CommRingCat.of F)}
    (e₄ : ∀ i, h' ≫ κ i = ρ i ≫ h) (e₅ : h' ≫ g' = f₁') (e₆ : h' ≫ π = π') (C : F) (hC : u.val = scal π' C)
    {n : ℕ} (c : Fin n → F)
    (t : Fin n → Fin j → LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => (k : ℤ))))
    (t' : Fin n → LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => g') (fun _ => (k : ℤ))))
    (t₀ : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => g') (fun _ => (k : ℤ))))
    (ht : ∀ l (y : Y') J J', Good L y J → Good L' y J' →
      (bw wA (h' ≫ g') y (fun i => J ((h' ≫ g') ≫ pr i)) (J' (h' ≫ g')) ^ k).val * sval (t' l) h' y J' =
        ∏ i, sval (t l i) (h' ≫ κ i) y J)
    (ht₀ : ∀ jj, t₀.f jj = ∑ l, resTop _ (scal π (c l)) * (t' l).f jj)
    (s : Fin n → Fin j → LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))))
    (s' : Fin n → LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => f₂') (fun _ => (k : ℤ))))
    (s₀ : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => f₂') (fun _ => (k : ℤ))))
    (hs : ∀ l, BoxFamily.IsBoxPull wL ρ (fun i _ => e₂ i) (s' l) (s l))
    (m : ∀ l i, Moves w k h (t l i) (s l i)) (m₀ : Moves w' k h' t₀ s₀) (jj) :
    s₀.f jj = ∑ l, resTop _ (scal π' (c l * C ^ k)) * (s' l).f jj := by
  obtain ⟨s₁, hs₁⟩ := GenericSectionBasis.exists_comb π' s' (fun l => c l * C ^ k)
  refine (sec_ext_val hM' (s := s₀) (s' := s₁) (fun y I' hI' => ?_) jj).trans (hs₁ jj)
  obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at hL y
  obtain ⟨J', hJ'⟩ := BoxFamily.exists_good_at hL' y
  obtain ⟨I, hI⟩ := BoxFamily.exists_good_at hM y
  have a₀ := hu _ (𝟙 Y') y (fun i => J (f₁' ≫ pr i)) (J' f₁') (fun i => I (f₂' ≫ qr i))
    (I' f₂') (fun i => hJ (f₁' ≫ pr i)) (hJ' f₁') (fun i => hI (f₂' ≫ qr i)) (hI' f₂')
  have a₁ := fun l => ht l y J J' hJ hJ'
  have a₂ := fun l => BoxFamily.boxPull_val (hs l) (𝟙 Y') y hI hI'
  have a₃ := fun l i => m l i _ (ρ i) y J I hJ hI
  have a₄ := m₀ _ (𝟙 Y') y J' I' hJ' hI'
  have a₅ : sval t₀ h' y J' = ∑ l, constHomVal π' y (c l) * sval (t' l) h' y J' := by
    refine (congrArg (gs h' y _) (ht₀ _)).trans
      ((GenericSectionBasis.gs_comb π t' c h' y _ (hJ'.mem _ h')).trans (Finset.sum_congr rfl fun l _ => ?_))
    rw [e₆, ← constVal_eq]
    rfl
  have a₆ : sval s₁ (𝟙 Y') y I' = ∑ l, constHomVal π' y (c l * C ^ k) * sval (s' l) (𝟙 Y') y I' := by
    refine (congrArg (gs (𝟙 Y') y _) (hs₁ _)).trans
      ((GenericSectionBasis.gs_comb π' s' _ (𝟙 Y') y _ (hI'.mem _ (𝟙 Y'))).trans
        (Finset.sum_congr rfl fun l _ => ?_))
    rw [Category.id_comp, ← constVal_eq]
    rfl
  have a₇ : (gm (𝟙 Y') y ⊤ u).val = constHomVal π' y C := by
    rw [← gs_unit _ y ⊤ trivial, hC, gs_scal, Category.id_comp, constVal_eq]
  simp only [Category.id_comp, BoxFamily.om, Fin.prod_univ_one, zpow_natCast, e₅, e₄, ← e₁, ← e₂] at a₀ a₁ a₂ a₃ a₄
  rw [a₄, a₅, a₆, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_pow, ← a₇, mul_left_comm, _root_.mul_assoc]
  refine congrArg _ ?_
  refine (Units.mul_right_inj (bw wL f₂' y (fun i => I (f₂' ≫ qr i)) (I' f₂') ^ k)).1 ?_
  rw [mul_left_comm _ (_ ^ k), a₂ l, ← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, a₀, mul_pow, mul_pow,
    Units.val_mul, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, a₁ l, ← Finset.prod_pow, Units.coe_prod,
    ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ => a₃ l i, Units.val_pow_eq_pow_val]

end General

theorem isBoxSecK_of_pull {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {G G' : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {LG : LB G.left} {LG' : LB G'.left}
    (pG : IsPowGrp G' G j) (w : LB.Iso LG' (boxLB LG pG.pr)) (k : ℕ)
    (s' : LB.Sec (LB.LinComb LG' (K := Fin 1) (fun _ => pullback.fst G'.hom (jK R)) (fun _ => (k : ℤ))))
    (s : Fin j → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (H : BoxFamily.IsBoxPull (pr := fun i => (pG.pr i).left) w (prK pG) (fun i _ => (prK_fst pG i).symm) s' s) :
    IsBoxSecK pG w k s' s := by
  intro jN jL
  refine fn_ext fun y hy => ?_
  have hm : (𝟙 (pullback G'.hom (jK R)) : _ ⟶ _) y ∈
      LB.wchart (LB.LinComb LG (fun i => (pG.pr i).left) (fun _ => 1)) (fun _ : Fin 1 => pullback.fst G'.hom (jK R))
        (fun _ => jN) ⊓ LB.wchart LG' (fun _ : Fin 1 => pullback.fst G'.hom (jK R)) (fun _ => jL) :=
    ⟨Set.mem_iInter.2 fun _ => hy.1, Set.mem_iInter.2 fun _ => hy.2⟩
  have E := congrArg (gs (𝟙 _) y _) (H (fun _ => jN) (fun _ => jL))
  have E₁ := ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans (congrArg Units.val
    (gm_linCombIso w _ _ _ y _ _ hm))) (gs_res _ y _ hm _))).symm.trans (E.trans ((gs_prod _ y _ hm _ _).trans
    (Finset.prod_congr rfl fun i _ => gs_res _ y _ hm _)))
  rw [Fin.prod_univ_one, zpow_natCast] at E₁
  refine ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val
    ((map_pow _ _ _).trans (congrArg (· ^ k) (gm_pull _ _ y _ hy _))))) (gs_res _ y _ hy _))).trans
    (E₁.trans ((gs_prod _ y _ hy _ _).trans (Finset.prod_congr rfl fun i _ => gs_res _ y _ hy _)).symm)


set_option maxHeartbeats 1000000 in
theorem main : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) → ∀ (k : ℕ), 1 ≤ k → (∀ s : Fin j → U.SecK k, ∃ s' : U'.SecK k, IsBoxSecK pG wL k s' s) ∧ ∀ s₀ : U'.SecK k, ∃ (n : ℕ) (c : Fin n → FractionRing R) (s : Fin n → Fin j → U.SecK k) (s' : Fin n → U'.SecK k), (∀ l, IsBoxSecK pG wL k (s' l) (s l)) ∧ ∀ jj, s₀.f jj = ∑ l, resTop _ (scal (pullback.snd G'.hom (jK R)) (c l)) * (s' l).f jj := by
  intro hL R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U wL hyp k hk
  obtain ⟨hgen, hwL, -⟩ := hyp
  have ex : ∀ s : Fin j → U.SecK k, ∃ s' : U'.SecK k, BoxFamily.IsBoxPull (pr := fun i => (pG.pr i).left) wL (prK pG)
      (fun i _ => (prK_fst pG i).symm) s' s := fun s =>
    BoxFamily.exists_boxPull wL hwL U.LG.isLB U'.LG.isLB _ _ s
  refine ⟨fun s => (ex s).imp fun s' hs' => isBoxSecK_of_pull pG wL k s' s hs', fun s₀ => ?_⟩
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨w', hw'⟩ := U'.ext
  have e₁ : ∀ i, U'.gen.hom.left ≫ (pA.pr i).left = prK pG i ≫ U.gen.hom.left := fun i =>
    congrArg (fun q => q.left) (hgen i)
  have e₂ : ∀ i, pullback.fst G'.hom (jK R) ≫ (pG.pr i).left = prK pG i ≫ pullback.fst G.hom (jK R) := fun i =>
    (prK_fst pG i).symm
  obtain ⟨u, hu⟩ := exists_ratio A.isLB A'.isLB U.LG.isLB U'.LG.isLB e₁ e₂ pA.w_gen hwL hw hw'
  obtain ⟨c₀, -, huc⟩ := unit_const hL.globalFns A' U'.gen u
  have hid : jFK (R := R) (FractionRing R) = 𝟙 _ := Spec.map_id _
  let T := TFK (R := R) (FractionRing R)
  let a : ∀ Y : Over (TK R).left, Y ⟶ T := fun Y => Over.homMk Y.hom (by
    show Y.hom ≫ jFK (R := R) (FractionRing R) = Y.hom
    rw [hid]; exact Category.comp_id _)
  have ha : ∀ (Y : Over (TK R).left) (b : Y ⟶ T), b = a Y := fun Y b => Over.OverMorphism.ext (by
    have := Over.w b
    have e : b.left ≫ jFK (R := R) (FractionRing R) = b.left := by rw [hid]; exact Category.comp_id _
    exact e.symm.trans this)
  have hu₂ : ∀ (Y : Over (TK R).left) (b b' : Y ⟶ T), b = b' := fun Y b b' => (ha Y b).trans (ha Y b').symm
  have mv := exists_moves A.isLB U.LG.isLB hw k (g := (snd T A.A).left) (lift (a _) U.gen.hom).left
    (congrArg (fun q => q.left) (lift_snd (a _) U.gen.hom)) (snd T A.A ≫ U.gen.inv).left
    (congrArg (fun q => q.left) (show (snd T A.A ≫ U.gen.inv) ≫ lift (a _) U.gen.hom = 𝟙 _ from
      CartesianMonoidalCategory.hom_ext _ _ (hu₂ _ _ _) (by simp)))
    (congrArg (fun q => q.left) (show lift (a _) U.gen.hom ≫ (snd T A.A ≫ U.gen.inv) = 𝟙 _ by simp))
  have mv' := exists_moves A'.isLB U'.LG.isLB hw' k (g := (snd T A'.A).left) (lift (a _) U'.gen.hom).left
    (congrArg (fun q => q.left) (lift_snd (a _) U'.gen.hom)) (snd T A'.A ≫ U'.gen.inv).left
    (congrArg (fun q => q.left) (show (snd T A'.A ≫ U'.gen.inv) ≫ lift (a _) U'.gen.hom = 𝟙 _ from
      CartesianMonoidalCategory.hom_ext _ _ (hu₂ _ _ _) (by simp)))
    (congrArg (fun q => q.left) (show lift (a _) U'.gen.hom ≫ (snd T A'.A ≫ U'.gen.inv) = 𝟙 _ by simp))
  obtain ⟨t₀, m₀⟩ := mv'.2 s₀
  obtain ⟨n, c, t, t', ht, ht₀⟩ := boxProduct_span hL R j A A' pA (FractionRing R) k hk t₀
  choose s m using fun l i => mv.1 (t l i)
  choose s' hs using fun l => ex (s l)
  refine ⟨n, fun l => c l * c₀ ^ k, s, s', fun l => isBoxSecK_of_pull pG wL k _ _ (hs l), ?_⟩
  refine comb_box A.isLB A'.isLB U.LG.isLB U'.LG.isLB e₁ e₂ pA.w wL w w' u hu
    (κ := fun i => (T ◁ pA.pr i).left) (π := (fst T A'.A).left) (fun i => ?_)
    (congrArg (fun q => q.left) (lift_snd (a _) U'.gen.hom))
    (congrArg (fun q => q.left) (lift_fst (a _) U'.gen.hom)) c₀ huc c t t' t₀
    (fun l y J J' hJ hJ' => ht l _ _ y J J' hJ hJ') ht₀ s s' s₀ hs m m₀
  refine congrArg (fun q => q.left) (?_ : lift (a _) U'.gen.hom ≫ T ◁ pA.pr i =
    (Over.pullback (jK R)).map (pG.pr i) ≫ lift (a _) U.gen.hom)
  exact CartesianMonoidalCategory.hom_ext _ _ (hu₂ _ _ _) (by simp [hgen])

end GlobalTheory.GenericBoxSpan
end
end
