module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankCechLBHomologyExtProd
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.TwistKer

theorem cls_twist_pull {S : Scheme.{0}} (B : Over S) [GrpObj B] {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB)
    {T : Over S} (x : T ⟶ B) (h : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB)
    (h' : (LB.div (translDiff B L (𝟙 B)) (O.pull (snd B B).left)).IsLB) :
    CechPic.cls _ h = CechPic.pull (x ▷ B).left (CechPic.cls _ h') := by
  have e₁ : (x ▷ B).left ≫ (snd B B).left = (snd T B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have e₂ : (x ▷ B).left ≫ (lift (fst B B ≫ 𝟙 B) (snd B B) ≫ μ[B]).left =
      (lift (fst T B ≫ x) (snd T B) ≫ μ[B]).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_lift, Category.comp_id, whiskerRight_snd, whiskerRight_fst]
  have hx : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h1 : (translDiff B L (𝟙 B)).IsLB := LB.isLB_linComb hL _ _
  rw [CechPic.cls_div hx (pull_isLB hO _), CechPic.cls_div h1 (pull_isLB hO _), map_sub,
    CechPic.cls_pull hO, CechPic.cls_pull hO, ← CechPic.pull_comp, e₁]
  congr 1
  refine (CechPic.cls_linComb hL _ _ hx).trans ?_
  refine Eq.trans ?_ (congrArg (CechPic.pull (x ▷ B).left) (CechPic.cls_linComb hL _ _ h1)).symm
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add (f := _), map_zsmul,
    ← CechPic.pull_comp, e₁, e₂]

theorem exists_closed_twist_kernel : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L O : LB B.left, L.IsLB → O.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ B), IsClosedImmersion j.left ∧ (∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) := by
  intro hG R _ B _ hB hP L O hL hO
  have hF : (LB.div (translDiff B L (𝟙 B)) (O.pull (snd B B).left)).IsLB :=
    LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
  obtain ⟨H, j, hj, h⟩ := GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle hG R B B hB hP _ hF
  refine ⟨H, j, hj, fun T x => Iff.trans ?_ (h T x)⟩
  have hx : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
    LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
  refine forall_congr' fun p => exists_congr fun U => and_congr Iff.rfl ?_
  refine (CechPic.cls_eq_zero_iff (pull_isLB hx _)).symm.trans
    (Iff.trans ?_ (CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hF _) _)))
  rw [CechPic.cls_pull hx, CechPic.cls_pull (pull_isLB hF _), CechPic.cls_pull hF, cls_twist_pull B hL hO x hx hF]

end GlobalTheory.UU.TwistKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernelStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_subscheme_translation_kernel : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L O : LB B.left, L.IsLB → O.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ B), IsClosedImmersion j.left ∧ (∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) := by
  first | exact @GlobalTheory.UU.TwistKer.exists_closed_twist_kernel | exact GlobalTheory.UU.TwistKer.exists_closed_twist_kernel | (intros; apply GlobalTheory.UU.TwistKer.exists_closed_twist_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtTower

theorem gm_linCombIso {X Y Z : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (p : (LB.LinComb M φ ε).ι × (LB.LinComb L φ ε).ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ (LB.div (LB.LinComb M φ ε) (LB.LinComb L φ ε)).U p) :
    gm r z _ ((LB.linCombIso w φ ε).s p) =
      ∏ a, gm (r ≫ φ a) z ((LB.div M L).U (p.1 a, p.2 a)) (w.s (p.1 a, p.2 a)) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ M.U (p.1 a) ⊓ L.U (p.2 a) :=
    ⟨LB.wchart_le M φ p.1 a hz.1, LB.wchart_le L φ p.2 a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z ((LB.div M L).U (p.1 a, p.2 a)) hm _)

theorem exists_gen_of_iso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen)
    (t : LB.Gen A) (ht : t.IsGen) : ∃ t' : LB.Gen B, t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : B.ι) (i : A.ι),
      r z ∈ B.U j → r z ∈ A.U i →
      gm r z (B.U j) (t'.s j) = gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := by
  have tr : ∀ (y : Y) (j j' : B.ι) (i i' : A.ι), y ∈ B.U j → y ∈ B.U j' → y ∈ A.U i → y ∈ A.U i' →
      gm (𝟙 Y) y (B.U j ⊓ A.U i) (w.s (j, i)) * gm (𝟙 Y) y (A.U i) (t.s i) =
        gm (𝟙 Y) y _ (B.g j j') * (gm (𝟙 Y) y (B.U j' ⊓ A.U i') (w.s (j', i')) * gm (𝟙 Y) y (A.U i') (t.s i')) := by
    intro y j j' i i' hj hj' hi hi'
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ B.U j ⊓ A.U i ⊓ (B.U j' ⊓ A.U i') := ⟨⟨hj, hi⟩, hj', hi'⟩
    have hn : (𝟙 Y : Y ⟶ Y) y ∈ A.U i ⊓ A.U i' := ⟨hi, hi'⟩
    have e := (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hw (j, i) (j', i'))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 Y) y (j, i) (j', i') hm) (gm_res _ y _ hm _))))
    have e' := (gm_res _ y _ hn _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ht i i')).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res _ y _ hn _))))
    refine (congrArg₂ (· * ·) e e').trans ?_
    rw [_root_.mul_mul_mul_comm, inv_mul_cancel_right]
    rfl
  have glue : ∀ j : B.ι, ∃ s : Γ(Y, B.U j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : A.ι),
      r z ∈ B.U j → r z ∈ A.U i →
      gm r z (B.U j) s = gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := by
    intro j
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : A.ι), r z ∈ B.U j ⊓ A.U i →
        gm r z (B.U j ⊓ A.U i) (@id (Γ(Y, B.U j ⊓ A.U i)ˣ) (w.s (j, i)) * res inf_le_right (t.s i)) =
          gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := fun Z r z i h =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res r z _ h _))
    obtain ⟨s, hs⟩ := glue_unit (B.U j) (fun i => B.U j ⊓ A.U i) (fun _ => inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hA x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩)
      (fun i => @id (Γ(Y, B.U j ⊓ A.U i)ˣ) (w.s (j, i)) * res inf_le_right (t.s i)) (fun i i' x hx => by
        rw [v _ _ x i hx.1, v _ _ x i' hx.2, tr x j j i i' hx.1.1 hx.1.1 hx.1.2 hx.2.2, gm_self hB _ x hx.1.1,
          _root_.one_mul])
    refine ⟨s, fun Z r z i hj hi => ?_⟩
    have hm : r z ∈ B.U j ⊓ A.U i := ⟨hj, hi⟩
    exact (gm_res r z inf_le_left hm s).symm.trans ((congrArg (gm r z _) (hs i)).trans (v Z r z i hm))
  choose s hs using glue
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z j i => hs j Z r z i⟩
  obtain ⟨i, hi⟩ := exists_chart hA y
  rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
  exact (hs j _ _ y i hy.1 hi).trans ((tr y j j' i i hy.1 hy.2 hi hi).trans (congrArg _ (hs j' _ _ y i hy.2 hi).symm))

theorem triv_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) (t : Triv A) :
    Triv B := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨t, ht⟩ := t
  obtain ⟨t', ht', -⟩ := exists_gen_of_iso hA hB w hw t ht
  exact ⟨t', ht'⟩

variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_genWt_of_lbIso {G : Over S} [GrpObj G] (Q : TQ G X) {N N' : LB Q.B.left} (hN : N.IsLB) (hN' : N'.IsLB)
    (h : LBIso N N') {u : LB.Gen (N.pull Q.q.left)} {χ : X} (hu : Q.GenWt N u χ) :
    ∃ u' : LB.Gen (N'.pull Q.q.left), Q.GenWt N' u' χ := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨u', hu', hv⟩ := exists_gen_of_iso (pull_isLB hN _) (pull_isLB hN' _)
    (LB.linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1)) (DVR.linCombIso_isGen w hw _ _) u hu.1
  refine ⟨u', hu', fun J => isWt_of_gm _ _ fun Z t g z hz => ?_⟩
  have e : ((t ≫ Q.i) * g).left ≫ Q.q.left = g.left ≫ Q.q.left := congrArg (·.left) (WtBundle.act_comp Q t g)
  have m : ∀ (M : LB Q.B.left) (I : PUnit → M.ι), g.left z ∈ (M.pull Q.q.left).U I →
      ((t ≫ Q.i) * g).left z ∈ (M.pull Q.q.left).U I := fun M I h =>
    (mem_pull (F := Q.q.left)).2 ((congrArg (fun a : Z.left ⟶ Q.B.left => a z ∈ M.U (I PUnit.unit)) e).mpr
      ((mem_pull (F := Q.q.left)).1 h))
  obtain ⟨I, hI⟩ := exists_chart (pull_isLB hN Q.q.left) (g.left z)
  have a₁ := gm_linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1) (J, I) g.left z ⟨hz, hI⟩
  have a₂ := gm_linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1) (J, I) ((t ≫ Q.i) * g).left z
    ⟨m _ _ hz, m _ _ hI⟩
  rw [e, ← a₁] at a₂
  rw [hv _ _ z J I (m _ _ hz) (m _ _ hI), hv _ _ z J I hz hI, WtBundle.gm_of_isWt (hu.2 I) t g z (m _ _ hI) hI,
    gm_charUnit, mul_left_comm]
  exact congrArg (fun x => _ * (x * _)) a₂

theorem exists_genWt_pull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (Q : TQ G X) (Q' : TQ G' X) {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) (hi : TorusCompat f F Q'.i Q.i) {β : Q'.B.left ⟶ Q.B.left}
    (hβ : Q'.q.left ≫ β = F ≫ Q.q.left) {N : LB Q.B.left} {u : LB.Gen (N.pull Q.q.left)} {χ : X}
    (hu : Q.GenWt N u χ) : ∃ u' : LB.Gen ((N.pull β).pull Q'.q.left), Q'.GenWt (N.pull β) u' χ :=
  let c := chartPullLinComb N β (K := PUnit) (fun _ => Q'.q.left) (fun _ => Q.q.left) (fun _ => 1) F fun _ => hβ
  ⟨GtBaseChange.genPull c u, GtBaseChange.genPull_isGen c hu.1, fun J => (hu.2 (c.idx J)).pull hF hi (c.le J)⟩

theorem exists_gen_comp {G : Over S} [GrpObj G] (Q : TQ G X) {Y : Scheme.{0}} (b : Q.B.left ⟶ Y) {O : LB Y}
    {u : LB.Gen ((O.pull b).pull Q.q.left)} {χ : X} (hu : Q.GenWt (O.pull b) u χ) :
    ∃ u' : LB.Gen (O.pull (Q.q.left ≫ b)), u'.IsGen ∧ ∀ j, IsWt Q.i _ (u'.s j).val χ :=
  let c := chartPullIn O (K := PUnit) (fun _ => b) (fun _ => 1) Q.q.left
  ⟨GtBaseChange.genPull c u, GtBaseChange.genPull_isGen c hu.1, fun J => (hu.2 (c.idx J)).res (c.le J)⟩

theorem psum_eq_lift {B T : Over S} [GrpObj B] [IsCommMonObj B] (x : Fin 2 → (T ⟶ B)) (I : Finset (Fin 2)) :
    (psum B x I).left = (lift (x 0) (x 1)).left ≫ (psum B (x2 B) I).left := by
  have e : (fun i => preHom (lift (x 0) (x 1)) (x2 B i)) = x := funext fun i => by
    fin_cases i
    exacts [lift_fst (x 0) (x 1), lift_snd (x 0) (x 1)]
  have := psum_hom (preHom (lift (x 0) (x 1))) (x2 B) I
  rw [e] at this
  exact congrArg (·.left) this.symm

theorem triv_lam_pull {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {f : S' ⟶ S} {b : B'.left ⟶ B.left} (hb : IsGrpPullback B' B f b) {O : LB B.left} {N : LB B'.left} (hO : O.IsLB)
    (hN : N.IsLB) (h : LBIso N (O.pull b)) (ht : Triv (abelian₂ B' N)) {T : Over S'} (U : Over.mk (T.hom ≫ f) ⟶ B ⊗ B) :
    Triv ((abelian₂ B O).pull U.left) := by
  obtain ⟨x, hx⟩ : ∃ x : Fin 2 → (T ⟶ B'), ∀ i, pushPt hb.1.w (x i) = U ≫ x2 B i :=
    ⟨fun i => Over.homMk (hb.1.lift (U ≫ x2 B i).left T.hom (Over.w (U ≫ x2 B i))) (hb.1.lift_snd _ _ _),
      fun i => Over.OverMorphism.ext (hb.1.lift_fst _ _ _)⟩
  obtain ⟨w, hw⟩ := h
  obtain ⟨t, ht⟩ := ht
  have t₁ : Triv (cubeLB B' x N) :=
    gen_chartPull (chartPullSame N (fun I : ULift (Finset (Fin 2)) => (psum B' x I.down).left)
      (fun I => (psum B' (x2 B') I.down).left) (fun I => (-1) ^ (2 - I.down.card)) (lift (x 0) (x 1)).left
      fun I => psum_eq_lift x I.down) t ht
  have l₁ : (cubeLB B' x N).IsLB := LB.isLB_linComb hN _ _
  have l₂ : (cubeLB B' x (O.pull b)).IsLB := LB.isLB_linComb (pull_isLB hO b) _ _
  have l₃ : (abelian₂ B O).IsLB := LB.isLB_linComb hO _ _
  have t₂ : Triv (cubeLB B' x (O.pull b)) := triv_of_lbIso l₁ l₂ ⟨_, DVR.linCombIso_isGen w hw _ _⟩ t₁
  have c : ChartPull (cubeLB B' x (O.pull b)) (abelian₂ B O) U.left :=
    chartPullLinComb O b (fun I : ULift (Finset (Fin 2)) => (psum B' x I.down).left)
      (fun I => (psum B (x2 B) I.down).left) (fun I => (-1) ^ (2 - I.down.card)) U.left
      fun I => psum_push hb x (x2 B) U hx I.down
  exact triv_of_lbIso l₂ (pull_isLB l₃ _)
    (LBIso.chartPull c (Geo.Tor.chartPullPull (abelian₂ B O) U.left U.left rfl) (GtBaseChange.lbIso_refl l₃)) t₂

theorem isGrpPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (e : ℕ) : IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem isLocalRing_quotient_pow (V : Type) [CommRing V] [IsLocalRing V] (e : ℕ) :
    IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isProjBy_of_relAmple {R : Type} [CommRing R] (B : Over (Spec (CommRingCat.of R))) {L : LB B.left}
    (hL : L.IsLB) (h : RelAmple B L) : IsProjBy B.hom := by
  obtain ⟨d, -, n, σ, hσ⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 h
  exact ⟨_, isLB_pw hL _, n, σ, hσ⟩

theorem triv_lam_of_levels (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {O : LB B.left} (hO : O.IsLB)
    (h : ∀ e, Triv ((abelian₂ B O).pull (fstG (IsLocalRing.maximalIdeal V) e (B ⊗ B)).left)) : Triv (abelian₂ B O) :=
  AbTriv.triv_of_forall_thick hG V (B ⊗ B) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB)
    (isProjBy_tensor V _ _ hp hp) _ (LB.isLB_linComb hO _ _) h

end GlobalTheory.WtTower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubsingletonOfForallIsMaximalSmulEqZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw


set_option backward.isDefEq.respectTransparency false in
theorem acyclic_extendScalars_of_flat {R S : Type} [CommRing R] [CommRing S] (g : R →+* S)
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hflat : ∀ p, Module.Flat R (C.X p)) (hC : C.Acyclic) :
    (((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).obj C).Acyclic := by
  have : QuasiIso (0 : C ⟶ C) := ⟨fun p => (quasiIsoAt_iff_exactAt _ p (hC p)).2 (hC p)⟩
  have h := GlobalTheory.quasiIso_extendScalars_of_flat (0 : C ⟶ C) hflat hflat n hn hn g
  rw [Functor.map_zero] at h
  intro p
  have h' := (quasiIsoAt_iff_isIso_homologyMap _ p).1 (h.1 p)
  rw [HomologicalComplex.homologyMap_zero] at h'
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (isIsoZero_iff_source_target_isZero _ _).1 h' |>.1

theorem subsingleton_of_forall_isMaximal_smul_eq_zero {R M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] (h : ∀ P : Ideal R, P.IsMaximal → ∃ r, r ∉ P ∧ ∀ z : M, r • z = 0) :
    Subsingleton M := by
  rw [← Module.annihilator_eq_top_iff (R := R)]
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr, hz⟩ := h P hP
  exact hr (hle (Module.mem_annihilator.2 hz))

theorem cechLB_acyclic_iff_fibres : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Flat f → IsProjBy f → ∀ F : LB Y, F.IsLB → ((∀ P : Ideal R, P.IsMaximal → ∃ (K : Type) (_ : Field K) (χ : R →+* K), RingHom.ker χ = P ∧ ∀ (Y₀ : Scheme.{0}) (π : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom χ)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y₀).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f₀) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F) D).Acyclic)) ∧ ((∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F) D).Acyclic) → ∀ (K : Type) [Field K] (χ : R →+* K), ∀ (Y₀ : Scheme.{0}) (π : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom χ)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y₀).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f₀) (F.pull π) D).Acyclic)) := by
  intro R _ _ Y f hf hproj F hF
  have := isProper_of_isProjBy R Y f hproj
  have : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from f]
    infer_instance
  have hI : ∀ {κ : Type} {D : κ → Y.Opens}, (∀ i, IsAffineOpen (D i)) → ∀ s : Finset κ,
      s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) := fun hD s hs =>
    IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hs) fun i _ => hD i
  refine ⟨fun H κ _ _ D hD hc p => ?_, fun H K _ χ Y₀ π f₀ h κ _ _ D hD hc p => ?_⟩
  · rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
    refine subsingleton_of_forall_isMaximal_smul_eq_zero (R := R) fun P hP => ?_
    obtain ⟨K, _, χ, rfl, HK⟩ := H P hP
    have h' := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
    have hac := HK _ _ _ h' κ
      (fun i => pullback.fst f (Spec.map (CommRingCat.ofHom χ)) ⁻¹ᵁ D i)
      (fun i => isAffineOpen_preimage_of_isPullback h' (hD i))
      (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl)
    exact GlobalTheory.exists_smul_homology_eq_zero_of_acyclic_fibre R K χ _ (Fintype.card κ)
      (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hF (hI hD))
      (cechLB_homology_finite_of_affine_cover R Y f F κ D hF inferInstance hproj hD hc)
      (fun q => (hac q).of_iso (cechLBBaseChangeIso hF h' (hI hD)).symm) p
  · obtain ⟨L, -, m, s, hc', hs⟩ := hproj
    have hD' : ∀ i, IsAffineOpen (nonzeroLocus (s i)) := fun i => (hs i).1
    have hac := acyclic_extendScalars_of_flat χ _ (Fintype.card (Fin (m + 1)))
      (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hF (hI hD')) (H _ _ hD' hc')
    have h₁ := (hac p).of_iso (cechLBBaseChangeIso hF h (hI hD'))
    have : IsSeparated f₀ := MorphismProperty.of_isPullback (P := @IsSeparated) h inferInstance
    obtain ⟨e⟩ := cechLB_homology_equiv_of_affine_covers K Y₀ f₀ (F.pull π) κ D _
      (fun i => π ⁻¹ᵁ nonzeroLocus (s i)) (LB.isLB_pull hF π) inferInstance hD hc
      (fun i => isAffineOpen_preimage_of_isPullback h (hD' i))
      (by rw [← Scheme.Hom.preimage_iSup, hc']; rfl) p
    rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
    exact e.subsingleton

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickenings
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickenings
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.SecAdicSum

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

theorem sumI_of_ker {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) {a b : ℕ}
    (A : Matrix (Fin b) (Fin a) R) {E Ix : Type} [AddCommGroup E] [Module R E] (ev : (Fin a → R) →ₗ[R] E)
    (v : Ix → Fin a → R) (v₀ : Fin a → R) (hv : ∀ i, A.mulVec (v i) = 0) (hv₀ : A.mulVec v₀ = 0)
    (h : ∀ e : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → ∀ k, (v₀ - ∑ i ∈ T, v i) k ∈ I ^ (e + 1)) :
    SumI I (fun i => ev (v i)) (ev v₀) := by
  let N : Submodule R (Fin a → R) := LinearMap.ker A.mulVecLin
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  refine ⟨N.map ev, (IsNoetherian.noetherian N).map ev, ⟨v₀, hv₀, rfl⟩, fun i => ⟨v i, hv i, rfl⟩, fun n => ?_⟩
  obtain ⟨S, hS⟩ := h (n + c)
  refine ⟨S, fun T hT => ?_⟩
  have m₁ : v₀ - ∑ i ∈ T, v i ∈ N := N.sub_mem hv₀ (N.sum_mem fun i _ => hv i)
  have m₂ : v₀ - ∑ i ∈ T, v i ∈ I ^ (n + c) • (⊤ : Submodule R (Fin a → R)) := by
    rw [pi_eq_sum_univ (v₀ - ∑ i ∈ T, v i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul
      (Ideal.pow_le_pow_right (Nat.le_succ _) (hS T hT k)) Submodule.mem_top
  have m₃ := (hc (n + c) (Nat.le_add_left _ _)).le ⟨m₂, m₁⟩
  rw [Nat.add_sub_cancel] at m₃
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_sub, ← Submodule.map_smul'']
  exact ⟨_, Submodule.smul_mono le_rfl inf_le_right m₃, rfl⟩

section
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X}
  (P : Perf f M)

theorem exists_vec (s : LB.Sec M) :
    ∃ v : Fin P.a → R, P.D₀.mulVec v = 0 ∧ ∀ i, AbLaw.rs X (P.le i) (s.f (P.ch i)) = loc₀ P v i := by
  have h : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) X (𝟙 X) f h
  have le : ∀ j : PUnit → M.ι, (M.pull (𝟙 X)).U j ≤ M.U (j PUnit.unit) := fun j y hy =>
    Set.mem_iInter.1 hy PUnit.unit
  let t : LB.Sec (M.pull (𝟙 X)) := ⟨fun j => AbLaw.rs X (le j) (s.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => by
    have hm : y ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) := ⟨le j hy.1, le j' hy.2⟩
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.1 _)).trans (Eq.trans ?_
      ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans
        (congrArg Units.val (gm_linComb M _ _ (𝟙 X) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.2 _)))).symm)
    rw [Fintype.prod_unique, zpow_one]
    exact (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (s.compat _ _)).trans
      ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))⟩
  obtain ⟨v, hv⟩ := E.surjective t
  refine ⟨v.1, v.2, fun i => ?_⟩
  have e := hE v i
  rw [hv] at e
  exact (AbLaw.rs_rs _ _ _).symm.trans e

theorem comp_eq_zero {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0)
    (h0 : ∀ i y, π y ∈ P.W i → gs π y _ (loc₀ P v i) = 0) : g ∘ v = 0 := by
  obtain ⟨E, hE⟩ := P.sec R' g X' π f' h
  have k₁ : (P.D₀.map g).mulVec (g ∘ v) = 0 := funext fun j =>
    (RingHom.map_mulVec g _ _ j).symm.trans ((congrArg g (congrFun hv j)).trans (map_zero g))
  refine congrArg Subtype.val (E.injective (a₁ := ⟨_, k₁⟩) (a₂ := ⟨0, Matrix.mulVec_zero _⟩) ?_)
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M π (P.le i))
    (fun y => exists_mem P (π y)) fun i => ?_
  refine (hE _ i).trans (Eq.trans ?_ (hE _ i).symm)
  refine (loc_comp P h v i).trans (Eq.trans (fn_ext (b := 0) fun y hy => ?_) (by simp))
  refine (gs_pull (𝟙 X') π y _ hy _).trans ?_
  rw [Category.id_comp, h0 i y hy, gs_eq (𝟙 X') y (π ⁻¹ᵁ P.W i) hy, map_zero, map_zero]

theorem loc₀_sub_sum {Ix : Type} (v₀ : Fin P.a → R) (v : Ix → Fin P.a → R) (T : Finset Ix) (i : P.I) :
    loc₀ P (v₀ - ∑ j ∈ T, v j) i = loc₀ P v₀ i - ∑ j ∈ T, loc₀ P (v j) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [loc₀, Pi.sub_apply, Finset.sum_apply, map_sub, map_sum, sub_mul, Finset.sum_mul,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

end

section
variable {X Y Z : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (X ⟶ Y)} {ε : K → ℤ} {R : Type} [CommRing R]
  {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (LB.LinComb L φ ε))

theorem gs_loc₀ {s : LB.Sec (LB.LinComb L φ ε)} {v : Fin P.a → R}
    (h : ∀ i, AbLaw.rs X (P.le i) (s.f (P.ch i)) = loc₀ P v i) (r : Z ⟶ X) (z : Z) {i : P.I} (hi : r z ∈ P.W i)
    {J : (Z ⟶ Y) → L.ι} (hJ : Good L z J) :
    gs r z _ (loc₀ P v i) = (trF φ ε r z (P.ch i) fun k => J (r ≫ φ k)).val * sval s r z J := by
  rw [← h i]
  exact (gs_res r z (P.le i) hi _).trans (sec_trans s r z (P.le i hi) (hJ.mem φ r))

end

theorem gs_cst_point {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    {B : Over (Spec (CommRingCat.of R))} (b : TF (R := R) F ⟶ B) (z : (TF (R := R) F).left) (W : B.left.Opens)
    (hz : b.left z ∈ W) (c : R) : gs b.left z W (AbLaw.cst B.hom W c) =
      CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) c)) := by
  have w : b.left ≫ B.hom = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    rw [Over.w b, Category.id_comp, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  rw [gs_eq b.left z W hz, app_cst w W c]
  exact TopCat.Presheaf.germ_res_apply (TF (R := R) F).left.presheaf _ z hz _

theorem sumF_of_sum_on_thickenings : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (n₀ : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good D.toPre.P.L z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro _ R _ _ _ I hR D F _ _ _ K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  have hL := D.toPre.P.isLB
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁
    set_option synthInstance.maxHeartbeats 100000 in
      rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
      ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end GlobalTheory.SecAdicSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickeningsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicSum_sections_of_finite_sums_on_thickenings : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (n₀ : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good D.toPre.P.L z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  first | exact @GlobalTheory.SecAdicSum.sumF_of_sum_on_thickenings | exact GlobalTheory.SecAdicSum.sumF_of_sum_on_thickenings | (intros; apply GlobalTheory.SecAdicSum.sumF_of_sum_on_thickenings <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechComplexAcyclicPrimitiveNontrivialAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechComplexAcyclicPrimitiveNontrivialAlgClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
namespace GlobalTheory.PrimVan

theorem cechLB_acyclic_of_primitive :
    ∀ (K : Type) [Field K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B],
      IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB →
      (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M →
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → B.left.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → ∀ n, (cechLB B.hom M D).ExactAt n ∧ IsZero ((cechLB B.hom M D).homology n) ∧
          Module.finrank K ((cechLB B.hom M D).homology n) = 0 := by
  intro K _ B _ _ hB hP M hM hu hn κ _ _ D hD hc n
  have := hB.proper
  have h := acyclic_of_kuenneth GlobalTheory.AbLaw.finrank_cechLB_homology_extProd hB hM (lbIso_pull_mul hM hu) (subsingleton_sec hB hM hu hn)
    hD hc (GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K _ _ M κ D hM inferInstance hP hD hc)
    (GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K _ _ _ κ D (Inh.trivLB_isLB _) inferInstance hP hD hc) n
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h
  have := ModuleCat.isZero_iff_subsingleton.1 hz
  exact ⟨h, hz, Module.finrank_zero_of_subsingleton⟩

theorem acyclic_cechLB_of_primitive :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (B.left).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (B.hom) (M) D).Acyclic) :=
  fun K _ _ B _ _ hB hP M hM hu hn κ _ _ D hD hc n =>
    (cechLB_acyclic_of_primitive K B hB hP M hM hu hn κ D hD hc n).1

end GlobalTheory.PrimVan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechComplexAcyclicPrimitiveNontrivialAlgClosedStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechComplex_acyclic_primitive_nontrivial_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (B.left).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (B.hom) (M) D).Acyclic) := by
  first | exact @GlobalTheory.PrimVan.acyclic_cechLB_of_primitive | exact GlobalTheory.PrimVan.acyclic_cechLB_of_primitive | (intros; apply GlobalTheory.PrimVan.acyclic_cechLB_of_primitive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoExtendsSemiAbelianDvrInducingFormal
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoExtendsSemiAbelianDvrInducingFormal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalExt

theorem hom_ext_of_flat_family {Y X : Scheme.{0}} (f g : Y ⟶ X)
    (h : ∀ y : Y, ∃ (Z : Scheme.{0}) (p : Z ⟶ Y), Flat p ∧ y ∈ Set.range p ∧ p ≫ f = p ≫ g) : f = g := by
  choose Z p hp hy he using h
  have : Surjective (Limits.Sigma.desc p) :=
    Surjective.sigmaDesc_of_union_range_eq_univ
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨y, hy y⟩)
  have : Epi (Limits.Sigma.desc p) := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi (Limits.Sigma.desc p)]
  refine Limits.Sigma.hom_ext _ _ fun y => ?_
  rw [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc_assoc, he]

theorem eq_of_isIso_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) [IsPreimmersion f] {Y X : Over S} (ψ : Y ⟶ X)
    [IsIso ((Over.pullback f).map ψ)] {x y : Y.left} (hx : Y.hom x ∈ Set.range f) (h : ψ.left x = ψ.left y) :
    x = y := by
  have w : ∀ z, X.hom (ψ.left z) = Y.hom z := fun z => by rw [← Scheme.Hom.comp_apply, Over.w]
  have hy : Y.hom y ∈ Set.range f := by rw [← w, ← h, w]; exact hx
  obtain ⟨x', rfl⟩ : x ∈ Set.range (pullback.fst Y.hom f) := by rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨y', rfl⟩ : y ∈ Set.range (pullback.fst Y.hom f) := by rw [Scheme.Pullback.range_fst]; exact hy
  have e : ((Over.pullback f).map ψ).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ ψ.left :=
    pullback.lift_fst _ _ _
  have e' : ∀ z, pullback.fst X.hom f (((Over.pullback f).map ψ).left z) = ψ.left (pullback.fst Y.hom f z) :=
    fun z => congr($e z)
  rw [← e', ← e'] at h
  have h₁ := (pullback.fst X.hom f).isEmbedding.injective h
  have : IsIso ((Over.pullback f).map ψ).left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback f).map ψ)))
  rw [((Over.pullback f).map ψ).left.isEmbedding.injective h₁]

variable {R : Type} [CommRing R] (I : Ideal R)

instance isClosedImmersion_thick (e : ℕ) : IsClosedImmersion (thick R I e) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem range_thick (e : ℕ) (s : Spec (CommRingCat.of R)) : s ∈ Set.range (thick R I e) ↔ I ≤ s.asIdeal := by
  have h := _root_.range_comap_of_surjective _ (Ideal.Quotient.mk (I ^ (e + 1))) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at h
  refine (h.ge.antisymm h.le ▸ Iff.rfl : s ∈ Set.range (thick R I e) ↔ s ∈ PrimeSpectrum.zeroLocus (I ^ (e + 1) : Ideal R)).trans ?_
  have := s.isPrime
  exact Ideal.IsPrime.pow_le_iff (I := I) (P := s.asIdeal) (Nat.succ_ne_zero e)

theorem map_eq_iff (e : ℕ) {Y X : Over (Spec (CommRingCat.of R))} (ψ : Y ⟶ X)
    (j : thickObj R I e Y ⟶ thickObj R I e X) :
    (Over.pullback (thick R I e)).map ψ = j ↔ (fstG I e Y).left ≫ ψ.left = j.left ≫ (fstG I e X).left := by
  have e₁ : ((Over.pullback (thick R I e)).map ψ).left ≫ pullback.fst X.hom (thick R I e) =
      pullback.fst Y.hom (thick R I e) ≫ ψ.left := pullback.lift_fst _ _ _
  refine ⟨fun h => h ▸ e₁.symm, fun h => Over.OverMorphism.ext (pullback.hom_ext (e₁.trans h) ?_)⟩
  exact (Over.w _).trans (Over.w j).symm

theorem hom_ext_thick [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R)))
    [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom] {X : Over (Spec (CommRingCat.of R))}
    [IsSeparated X.hom] {a b : H ⟶ X}
    (h : ∀ e, (Over.pullback (thick R I e)).map a = (Over.pullback (thick R I e)).map b) : a = b :=
  (GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings R I hI H).2 X a b fun e =>
    ((map_eq_iff I e a _).1 (h e)).trans ((map_eq_iff I e b _).1 rfl).symm

theorem isMonHom_of_thick [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) {G' G : Over (Spec (CommRingCat.of R))}
    [GrpObj G'] [GrpObj G] [Smooth G'.hom] [GeometricallyConnected G'.hom] [IsSeparated G.hom] (ψ : G' ⟶ G)
    (h : ∀ e, IsMonHom ((Over.pullback (thick R I e)).map ψ)) : IsMonHom ψ := by
  have h1 : Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (Smooth (𝟙 _))
  have h1' : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of R)))).hom :=
    inferInstanceAs (GeometricallyConnected (𝟙 _))
  have h2 : Smooth (G' ⊗ G').hom := inferInstanceAs (Smooth (pullback.fst G'.hom G'.hom ≫ G'.hom))
  have h2' : GeometricallyConnected (G' ⊗ G').hom :=
    GeometricallyConnected.comp (pullback.fst G'.hom G'.hom) G'.hom
  constructor
  · refine hom_ext_thick I hI _ fun e => ?_
    have := (h e).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at this
    rw [Functor.map_comp, this]
  · refine hom_ext_thick I hI _ fun e => ?_
    have := (h e).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
      cancel_epi] at this
    rw [Functor.map_comp, this, Functor.map_comp]

theorem exists_iso [IsDomain R] [IsDiscreteValuationRing R] (hI : I = IsLocalRing.maximalIdeal R)
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G) (hj : ∀ e, IsMonHom (j e).hom)
    (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G)
    (H : ∀ x : (thickObj R I 0 G').left, ∃ (T : Scheme.{0}) (g' : T ⟶ G'.left) (g : T ⟶ G.left), Flat g' ∧
      (fstG I 0 G').left x ∈ Set.range g' ∧ g ≫ G.hom = g' ≫ G'.hom ∧
      (∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left),
        r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g' → r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R) = ρ ≫ g) ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ (thickObj R I e G').left),
        r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g) :
    ∃ ψ : G' ≅ G, IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧
      ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := hG'.smooth
  have := hG'.separated
  have := hG'.quasiCompact
  have := hG'.geomConnected
  have := GlobalTheory.GenericExt.isOpenImmersion_jK R
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField R (FractionRing R)
  have hint : IsIntegral G'.left :=
    (GlobalTheory.isIntegral_and_isNormalScheme_of_smooth_dvr R (FractionRing R) G' inferInstance
      (inferInstanceAs (ConnectedSpace ↥(pullback G'.hom (jK R))))).1
  have hx0 : ∀ x : G'.left, I ≤ (G'.hom x).asIdeal → x ∈ Set.range (fstG I 0 G').left := fun x hx => by
    show x ∈ Set.range (pullback.fst G'.hom (thick R I 0))
    rw [Scheme.Pullback.range_fst]
    exact (range_thick I 0 _).2 hx
  obtain ⟨ψ, hψ⟩ := GlobalTheory.GenericExt.main R G' G ΦK.hom fun x hx => by
    obtain ⟨x, rfl⟩ := hx0 x (by rw [hx, hI]; exact le_rfl)
    obtain ⟨T, g', g, h₁, h₂, -, h₄, -⟩ := H x
    exact ⟨T, g', g, h₁, h₂, h₄⟩
  have eψ : ΦK.hom.left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ ψ.left := by
    rw [← hψ]; exact pullback.lift_fst _ _ _
  have hth : ∀ e : ℕ, (fstG I e G').left ≫ ψ.left = (j e).hom.left ≫ (fstG I e G).left := fun e => by
    refine hom_ext_of_flat_family _ _ fun y => ?_
    obtain ⟨x, hx⟩ := hx0 ((fstG I e G').left y) ((range_thick I e _).1 (by
      have : (fstG I e G').left y ∈ Set.range (pullback.fst G'.hom (thick R I e)) := ⟨y, rfl⟩
      rw [Scheme.Pullback.range_fst] at this
      exact this))
    obtain ⟨T, g', g, h₁, h₂, h₃, h₄, h₅⟩ := H x
    have hg : g' ≫ ψ.left = g := by
      let a : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk (g' ≫ ψ.left) (by simp)
      let b : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk g h₃
      have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R)) := inferInstance
      have : IsSchemeTheoreticallyDominant (pullback.fst g' (pullback.fst G'.hom (jK R))) := inferInstance
      have := GlobalTheory.over_ext_of_schemeTheoreticallyDominant (a := a) (b := b)
        (pullback.fst g' (pullback.fst G'.hom (jK R))) (by
          have := h₄ _ _ (pullback.snd g' (pullback.fst G'.hom (jK R))) pullback.condition.symm
          rw [eψ] at this
          exact (pullback.condition_assoc _).trans this)
      exact congr(($this).left)
    refine ⟨_, pullback.snd g' (fstG I e G').left, inferInstance, ?_, ?_⟩
    · rw [Scheme.Pullback.range_snd]
      show (fstG I e G').left y ∈ Set.range g'
      rw [← hx]; exact h₂
    · rw [h₅ e _ _ _ pullback.condition.symm, ← pullback.condition_assoc, hg]
  have hth' : ∀ e, (Over.pullback (thick R I e)).map ψ = (j e).hom := fun e => (map_eq_iff I e ψ _).2 (hth e)
  have hmon : IsMonHom ψ := isMonHom_of_thick I (by rw [hI, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ψ
    fun e => hth' e ▸ hj e
  have hK : IsIso ((Over.pullback (jK R)).map ψ) := hψ ▸ inferInstance
  have h0 : IsIso ((Over.pullback (thick R I 0)).map ψ) := hth' 0 ▸ inferInstance
  have w : ψ.left ≫ G.hom = G'.hom := Over.w ψ
  have : IsSeparated (ψ.left ≫ G.hom) := w ▸ inferInstance
  have : LocallyOfFiniteType (ψ.left ≫ G.hom) := w ▸ inferInstance
  have : QuasiCompact (ψ.left ≫ G.hom) := w ▸ inferInstance
  have : IsSeparated ψ.left := .of_comp _ G.hom
  have : LocallyOfFiniteType ψ.left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ψ.left := .of_comp _ G.hom
  have : LocallyQuasiFinite ψ.left := LocallyQuasiFinite.of_injective fun x y h => by
    by_cases hx : G'.hom x ∈ Set.range (jK R)
    · exact eq_of_isIso_pullback (jK R) ψ hx h
    · refine eq_of_isIso_pullback (thick R I 0) ψ ((range_thick I 0 _).2 ?_) h
      rw [GlobalTheory.GenericExt.eq_closedPoint_of_not_mem_range R _ hx, hI]; exact le_rfl
  have : IsIso ψ := GlobalTheory.isIso_of_quasiFinite_of_isIso_genericFibre_dvr R (FractionRing R) G' G ψ hmon
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance hK
  exact ⟨asIso ψ, hmon, hψ, hth⟩

theorem main : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∃ ψ : G' ≅ G, (IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧ ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left) := by
  intro l₁ l₂ R _ _ _ I hA hI D D' A A' G G' _ _ _ _ hG hG' U U' hD j hj ΦK wK hw
  refine exists_iso I hI hG hG' j (fun e => (hj e).1) ΦK fun x => ?_
  obtain ⟨B, _, _, g', g, jL, jL', h₁, -, h₃, h₄, h₅, h₆, h₇⟩ :=
    GlobalTheory.exists_completed_point_of_thickenings R I hA hI D D' A A' G G' hG hG' U U' hD j hj x
  obtain ⟨v, hv, -⟩ := GlobalTheory.T.generic_iso_agrees_on_complete_points_alt l₁ l₂ R I hA hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hw B g' g jL jL' h₁
    ⟨h₅, h₆, h₇⟩
  exact ⟨_, g', g, h₃, h₄, h₆.trans h₅.symm, fun Z ρ r h => (hv Z ρ r h).1, h₇.2.2⟩

end GlobalTheory.FormalExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoExtendsSemiAbelianDvrInducingFormalStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_iso_extends_semiAbelian_dvr_inducing_formal : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∃ ψ : G' ≅ G, (IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧ ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left) := by
  first | exact @GlobalTheory.FormalExt.main | exact GlobalTheory.FormalExt.main | (intros; apply GlobalTheory.FormalExt.main <;> assumption)
end
end
