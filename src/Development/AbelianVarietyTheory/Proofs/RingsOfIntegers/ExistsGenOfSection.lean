module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxTheta

section Box

variable {X X' Y Y' Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem bw_trans {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen) (ψ : Z ⟶ X') (z : Z)
    {jN jN' : Fin j → M.ι} {k k' : M'.ι} (h : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k)
    (h' : ψ z ∈ LB.wchart M pr jN' ⊓ M'.U k') :
    bw w ψ z jN k = (∏ i, gm (ψ ≫ pr i) z (M.U (jN i) ⊓ M.U (jN' i)) (M.g (jN i) (jN' i))) *
      (gm ψ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * bw w ψ z jN' k' := by
  have hm : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k') := ⟨h, h'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k'))) (hw (jN, k) (jN', k'))
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (jN, k) (jN', k') hm).trans (congrArg₂ (· * ·) ?_ rfl))
    (gm_res ψ z _ hm _))))
  refine (gm_linComb M pr (fun _ => 1) ψ z jN jN' h.1 h'.1).trans ?_
  simp only [zpow_one]

theorem exists_box_ratio (hM : M.IsLB) (hM' : M'.IsLB) {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen)
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y' ⟶ Y)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε)) (ht' : t'.IsGen)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    ∃ c : Γ(Y', ⊤)ˣ, ∀ (y : Y') (J J'), Good M y J → Good M' y J' →
      (∏ a, bw w (φ' a) y (fun i => J (φ' a ≫ pr i)) (J' (φ' a)) ^ ε a) * val t' (𝟙 _) y J' =
        gm (𝟙 _) y ⊤ c * ∏ i, val (t i) (ρ i) y J := by
  let W : (K → Fin j → M.ι) × (K → M'.ι) → Y'.Opens := fun p =>
    LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' p.1 ⊓ LB.wchart M' φ' p.2
  have le : ∀ p i, W p ≤ ρ i ⁻¹ᵁ LB.wchart M (φ i) (fun a => p.1 a i) := fun p i y hy =>
    Set.mem_iInter.2 fun a => (congrArg (fun q => q y ∈ M.U (p.1 a i)) (hψ i a)).mp
      (Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 a) i)
  obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(Y', W p)ˣ, ∀ p y, y ∈ W p → gm (𝟙 Y') y (W p) (u p) =
      (∏ a, bw w (φ' a) y (p.1 a) (p.2 a) ^ ε a) * gm (𝟙 Y') y (LB.wchart M' φ' p.2) (t'.s p.2) *
        (∏ i, gm (ρ i) y (LB.wchart M (φ i) (fun a => p.1 a i)) ((t i).s (fun a => p.1 a i)))⁻¹ := by
    refine ⟨fun p => @id (Γ(Y', W p)ˣ) ((LB.linCombIso w φ' ε).s p) * res inf_le_right (t'.s p.2) *
      (∏ i, res (le p i) (pullU (ρ i) _ ((t i).s (fun a => p.1 a i))))⁻¹, fun p y hy => ?_⟩
    have E₁ := gm_linCombIso w φ' ε (𝟙 Y') y p.1 p.2 hy
    simp only [Category.id_comp] at E₁
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) E₁
      (gm_res (𝟙 Y') y inf_le_right hy _))) ((map_inv _ _).trans (congrArg (·⁻¹) ((map_prod _ _ _).trans
      (Finset.prod_congr rfl fun i _ => gm_rp₁ (ρ i) y _ _ (le p i) hy _)))))
  obtain ⟨c, hc⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
      choose I' hI' using fun χ : Y' ⟶ X' => exists_chart hM' (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun a i => I (φ' a ≫ pr i), fun a => I' (φ' a)),
        Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hI (φ' a ≫ pr i), Set.mem_iInter.2 fun a => hI' (φ' a)⟩) u
    (fun p q y hy => by
      have b : ∀ a, bw w (φ' a) y (p.1 a) (p.2 a) = _ := fun a => bw_trans hw (φ' a) y (jN' := q.1 a) (k' := q.2 a)
        ⟨Set.mem_iInter.1 hy.1.1 a, Set.mem_iInter.1 hy.1.2 a⟩ ⟨Set.mem_iInter.1 hy.2.1 a, Set.mem_iInter.1 hy.2.2 a⟩
      have g' := gen_trans ht' (𝟙 Y') y hy.1.2 hy.2.2
      have g := fun i => gen_trans (ht i) (ρ i) y (le p i hy.1) (le q i hy.2)
      rw [hu p y hy.1, hu q y hy.2, g']
      simp only [b, g, trF, hψ, Category.id_comp, mul_zpow, Finset.prod_mul_distrib, inv_zpow, Finset.prod_inv_distrib,
        ← Finset.prod_zpow]
      rw [Finset.prod_comm]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨c, fun y J J' hJ hJ' => ?_⟩
  have hy : y ∈ W (fun a i => J (φ' a ≫ pr i), fun a => J' (φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ (φ' a ≫ pr i), Set.mem_iInter.2 fun a => hJ' (φ' a)⟩
  have e := (gm_res (𝟙 Y') y le_top hy c).symm.trans ((congrArg (gm (𝟙 Y') y _) (hc _)).trans (hu _ y hy))
  rw [e, val_of t' _ y J' (fun a => J' (φ' a)) (fun a => by rw [Category.id_comp])]
  simp only [fun i => val_of (t i) (ρ i) y J (fun a => J (φ' a ≫ pr i)) (fun a => congrArg J (hψ i a).symm),
    inv_mul_cancel_right]

theorem exists_gen_of_section (N : LB Y) (f : Y' ⟶ Y) (g : Y ⟶ Y') (hg : g ≫ f = 𝟙 Y) (c : LB.Gen (N.pull f))
    (hc : c.IsGen) : ∃ t : LB.Gen N, t.IsGen := by
  have le : ∀ i, N.U i ≤ g ⁻¹ᵁ (N.pull f).U (fun _ => i) := fun i y hy =>
    mem_pull.2 ((congrArg (fun q => q y ∈ N.U i) hg).mpr hy)
  refine ⟨⟨fun i => res (le i) (pullU g _ (c.s fun _ => i))⟩, fun i i' => unit_ext fun y hy => ?_⟩
  have e := gen_trans (L := N) (φ := fun _ : PUnit.{1} => f) (ε := fun _ => 1) hc g y (le i hy.1) (le i' hy.2)
  rw [trF, Fintype.prod_unique, zpow_one, hg] at e
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_rp₁ g y _ _ (le i) hy.1 _)).trans (e.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res (𝟙 Y) y _ hy _).trans (gm_rp₁ g y _ _ (le i') hy.2 _)))

end Box

section Theta

variable {S : Scheme.{0}}

theorem act_val {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T)
    (s s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => k)))
    (h : IsActOf A L k θ s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    sval s' r z J = (val (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k])
      θ.φ r z J).val * sval s (r ≫ (translT A θ.pt).left) z J := by
  have hm := hJ.mem (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] r
  have e := congrArg (gs r z _) (h (fun a => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] a)))
  have l := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _)
    (fun a => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] a))
  rw [sval_of s (r ≫ (translT A θ.pt).left) z J (fun _ => J (r ≫ (translPt A θ.pt).left)) (fun _ => by
    rw [Category.assoc, ← Over.comp_left, translT, lift_snd])]
  exact (gs_res r z _ hm _).symm.trans (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hm _)
    ((gs_res r z l hm _).trans (gs_pull r (translT A θ.pt).left z
      (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ (translPt A θ.pt).left))) (l hm) _)))))

theorem exists_theta (hK : KerPowSt) [IsLocallyNoetherian S] (P : PolAV S) {k : ℕ} (hk : 1 ≤ k) {T : Over S}
    [Subsingleton T.left] [Nonempty T.left] (x : T ⟶ P.A) (hx : x ^ k = 1) :
    ∃ θ : ThetaGrp P.A P.L (k : ℤ) T, θ.pt = x := by
  obtain ⟨p⟩ := ‹Nonempty T.left›
  obtain ⟨V, hV, c, hc⟩ := (hK S P k hk T x).2 hx p
  have hr : Set.range (𝟙 (T ⊗ P.A).left : (T ⊗ P.A).left ⟶ _) ⊆ Set.range ((fst T P.A).left ⁻¹ᵁ V).ι := by
    intro y _
    exact ⟨⟨y, show (fst T P.A).left y ∈ V from Subsingleton.elim p ((fst T P.A).left y) ▸ hV⟩, rfl⟩
  obtain ⟨t, ht⟩ := exists_gen_of_section _ _ (IsOpenImmersion.lift _ _ hr) (IsOpenImmersion.lift_fac _ _ hr) c hc
  exact ⟨⟨x, t, ht⟩, rfl⟩

theorem surj_fst (hG : GlobalFnsSt) {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  rw [← lift_snd (snd T A) (fst T A), Over.comp_left]
  refine surj_comp (fun a => ⟨(lift (snd A T) (fst A T)).left.appTop.hom a, ?_⟩) (surj_snd hG hA T)
  have e : (lift (snd T A) (fst T A)).left ≫ (lift (snd A T) (fst A T)).left = 𝟙 _ := by
    rw [← Over.comp_left, comp_lift, lift_snd, lift_fst, lift_fst_snd]; rfl
  have := congrArg (fun q => (Scheme.Hom.appTop q).hom a) e
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_appTop,
    CommRingCat.hom_id, RingHom.id_apply] using this

theorem translPt_hom {A A' T : Over S} [GrpObj A] [GrpObj A'] (f : A' ⟶ A) [IsMonHom f] (x : T ⟶ A') :
    translPt A' x ≫ f = T ◁ f ≫ translPt A (x ≫ f) := by
  show (fst T A' ≫ x * snd T A') ≫ f = T ◁ f ≫ (fst T A ≫ x ≫ f * snd T A)
  rw [MonObj.mul_comp, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, Category.assoc]

theorem translT_hom {A A' T : Over S} [GrpObj A] [GrpObj A'] (f : A' ⟶ A) [IsMonHom f] (x : T ⟶ A') :
    translT A' x ≫ T ◁ f = T ◁ f ≫ translT A (x ≫ f) := by
  rw [translT, translT, lift_whiskerLeft, comp_lift, whiskerLeft_fst, translPt_hom]

theorem box_act (hG : GlobalFnsSt) {j : ℕ} {A A' : PolAV S} (pA : IsPowPolAV A' A j) {T : Over S} (k : ℕ)
    (θ' : ThetaGrp A'.A A'.L (k : ℤ) T) (θ : Fin j → ThetaGrp A.A A.L (k : ℤ) T)
    (hθ : ∀ i, (θ i).pt = θ'.pt ≫ pA.pr i) :
    ∃ c : Γ(T.left, ⊤), IsUnit ((fst T A'.A).left.appTop.hom c) ∧
      ∀ (t u : Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd T A.A).left) (fun _ => (k : ℤ))))
        (t' u' t'' : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd T A'.A).left) (fun _ => (k : ℤ)))),
        (∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A'.A).left) (z : Z) (J J'), Good A.L z J → Good A'.L z J' →
          (bw pA.w (r ≫ (snd T A'.A).left) z (fun i => J ((r ≫ (snd T A'.A).left) ≫ (pA.pr i).left))
            (J' (r ≫ (snd T A'.A).left)) ^ k).val * sval t' r z J' = ∏ i, sval (t i) (r ≫ (T ◁ pA.pr i).left) z J) →
        (∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A'.A).left) (z : Z) (J J'), Good A.L z J → Good A'.L z J' →
          (bw pA.w (r ≫ (snd T A'.A).left) z (fun i => J ((r ≫ (snd T A'.A).left) ≫ (pA.pr i).left))
            (J' (r ≫ (snd T A'.A).left)) ^ k).val * sval u' r z J' = ∏ i, sval (u i) (r ≫ (T ◁ pA.pr i).left) z J) →
        (∀ i, IsActOf A.A A.L (k : ℤ) (θ i) (t i) (u i)) → IsActOf A'.A A'.L (k : ℤ) θ' t' t'' →
        ∀ jj, t''.f jj = liftFun A'.A _ c * u'.f jj := by
  have hP : ∀ i, translPt A'.A θ'.pt ≫ pA.pr i = T ◁ pA.pr i ≫ translPt A.A (θ i).pt := fun i => by
    haveI := pA.hom i
    rw [hθ, translPt_hom]
  have hT : ∀ i, (translT A'.A θ'.pt).left ≫ (T ◁ pA.pr i).left = (T ◁ pA.pr i).left ≫ (translT A.A (θ i).pt).left :=
    fun i => by
      haveI := pA.hom i
      rw [hθ, ← Over.comp_left, translT_hom, Over.comp_left]
  obtain ⟨a, ha⟩ := exists_box_ratio (pr := fun i => (pA.pr i).left) A.isLB A'.isLB pA.w_gen (K := Fin 2)
    (φ' := ![(snd T A'.A).left, (translPt A'.A θ'.pt).left])
    (φ := fun i => ![(snd T A.A).left, (translPt A.A (θ i).pt).left]) (ε := ![(k : ℤ), -(k : ℤ)])
    (ρ := fun i => (T ◁ pA.pr i).left) (fun i a => by
      fin_cases a
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T (pA.pr i)).symm
      · exact congrArg (fun q => q.left) (hP i)) θ'.φ θ'.isGen (fun i => (θ i).φ) (fun i => (θ i).isGen)
  obtain ⟨c, hc⟩ := surj_fst hG A'.isAb T a.val
  refine ⟨c, hc ▸ a.isUnit, fun t u t' u' t'' ht hu hA hA' jj => fn_ext fun y hy => ?_⟩
  obtain ⟨J', hJ', eJ⟩ := exists_good A'.L A'.isLB y (fun _ : Fin 1 => (snd T A'.A).left) jj
    (fun a b _ => congrArg jj (Subsingleton.elim a b)) (fun a => Set.mem_iInter.1 hy a)
  choose J hJ using fun χ : (T ⊗ A'.A).left ⟶ A.A.left => exists_chart A.isLB (χ y)
  have e₁ := ht _ (translT A'.A θ'.pt).left y J J' hJ hJ'
  have e₂ := hu _ (𝟙 _) y J J' hJ hJ'
  have e₃ := act_val θ' t' t'' hA' (𝟙 _) y hJ'
  have e₄ := fun i => act_val (θ i) (t i) (u i) (hA i) (T ◁ pA.pr i).left y hJ
  have e₅ := ha y J J' hJ hJ'
  have s₁ : (translT A'.A θ'.pt).left ≫ (snd T A'.A).left = (translPt A'.A θ'.pt).left := by
    rw [← Over.comp_left, translT, lift_snd]
  rw [Fin.prod_univ_two] at e₅
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at e₅
  simp only [s₁, hT] at e₁
  simp only [Category.id_comp, e₄, Finset.prod_mul_distrib, ← Units.coe_prod] at e₂
  rw [Category.id_comp] at e₃
  have f₁ := sval_of t'' (𝟙 _) y J' jj (fun a => by rw [Category.id_comp]; exact eJ a)
  have f₂ := sval_of u' (𝟙 _) y J' jj (fun a => by rw [Category.id_comp]; exact eJ a)
  have f₃ : gs (𝟙 (T ⊗ A'.A).left) y _ (liftFun A'.A (LB.wchart A'.L (fun _ : Fin 1 => (snd T A'.A).left) jj) c) =
      (gm (𝟙 _) y ⊤ a).val := (gs_res (𝟙 _) y le_top hy _).trans ((congrArg _ hc).trans (gs_unit _ y ⊤ trivial a))
  refine f₁.symm.trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) f₃ f₂.symm)).symm)
  rw [← e₁, ← _root_.mul_assoc, ← Units.val_mul] at e₂
  rw [e₃, (Units.eq_inv_mul_iff_mul_eq _).2 e₂, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
  refine congrArg (fun v : ((T ⊗ A'.A).left.presheaf.stalk y)ˣ => v.val * _) ?_
  rw [eq_inv_mul_iff_mul_eq.2 e₅, eq_mul_inv_iff_mul_eq.2 e₅.symm]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Theta

theorem box_theta_act : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (θ' : ThetaGrp A'.A A'.L (k : ℤ) (TFK (R := R) F)), θ'.pt ^ k = 1 → ∃ (θ : Fin j → ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (c : F), c ≠ 0 ∧ (∀ i, (θ i).pt = θ'.pt ≫ pA.pr i) ∧ ∀ (t u : Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))) (t' u' t'' : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ)))), (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval t' r z J' = ∏ i, Geo.Tor.sval (t i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J) → (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval u' r z J' = ∏ i, Geo.Tor.sval (u i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J) → (∀ i, IsActOf A.A A.L (k : ℤ) (θ i) (t i) (u i)) → IsActOf A'.A A'.L (k : ℤ) θ' t' t'' → ∀ jj, t''.f jj = liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * u'.f jj := by
  intro hL R _ _ j A A' pA F _ _ k hk θ' hθ'
  haveI : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  choose θ hθ using fun i => exists_theta hL.kerPow A hk (T := TFK (R := R) F) (θ'.pt ≫ pA.pr i) (by
    haveI := pA.hom i
    rw [← MonObj.pow_comp, hθ', MonObj.one_comp])
  obtain ⟨c, hc, H⟩ := box_act hL.globalFns pA k θ' θ hθ
  have e : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c) = c :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply c
  refine ⟨θ, (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c, fun h0 => ?_, hθ, ?_⟩
  · rw [h0, map_zero] at e
    rw [← e, map_zero] at hc
    obtain ⟨p⟩ := ‹Nonempty (TFK (R := R) F).left›
    have h1 := hc.map (((TFK (R := R) F) ⊗ A'.A).left.presheaf.germ ⊤ ((lift (𝟙 _) θ'.pt).left p) trivial).hom
    rw [map_zero] at h1
    exact not_isUnit_zero h1
  · rw [e]; exact H

end GlobalTheory.BoxTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isIntegral_left_of_isAbelianScheme_field {K : Type} [Field K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  obtain ⟨-, hs, -, hc⟩ := hA
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton (f := A.hom)
  exact isIntegral_of_smooth_field_of_connectedSpace A.hom

theorem unifPre_genericFibre_surjective_appTop_and_isIntegral :
    GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom ∧ IsIntegral (pullback G.hom (jK R)) := by
  intro hGF R _ _ I D A G _ _ U
  have hAi : IsIntegral A.A.left := isIntegral_left_of_isAbelianScheme_field A.A A.isAb
  have hw : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  have : IsIso U.gen.hom.left := (Over.forget _).map_isIso U.gen.hom
  refine ⟨?_, ?_⟩
  · have hb := hGF _ A.A A.isAb
    rw [← hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    have : IsIso U.gen.hom.left.appTop := inferInstanceAs (IsIso (U.gen.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso (U.gen.hom.left.appTop)).surjective.comp hb.surjective
  · show IsIntegral ((Over.pullback (jK R)).obj G).left
    have : Nonempty ((Over.pullback (jK R)).obj G).left :=
      ⟨U.gen.inv.left (Classical.arbitrary A.A.left)⟩
    exact isIntegral_of_isOpenImmersion U.gen.hom.left

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem secIsMul_gs {R : Type} [CommRing R] {Y Z : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)} {L : LB Y} {a : R}
    {σ τ : LB.Sec L} (h : SecIsMul p a σ τ) (q : Z ⟶ Y) (z : Z) (j : L.ι) (hz : q z ∈ L.U j) :
    gs q z (L.U j) (σ.f j) = cst (q ≫ p) z a * gs q z (L.U j) (τ.f j) := by
  rw [h j, gs_mul q z _ hz]
  congr 1
  exact gs_constFn p (L.U j) q z hz a

private theorem gs_eq_cst_mul_gs_of_secIsMul {R : Type} [CommRing R] {Y Z : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)}
    {L : LB Y} {a : R} {σ τ : LB.Sec L} (h : SecIsMul p a σ τ) (q : Z ⟶ Y) (z : Z) (j : L.ι) :
    gs q z (L.U j) (σ.f j) = cst (q ≫ p) z a * gs q z (L.U j) (τ.f j) := by
  by_cases hz : q z ∈ L.U j
  · exact secIsMul_gs h q z j hz
  · simp only [gs, dif_neg hz, mul_zero]

theorem expandsAt_secIsMul : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (a : R) (σ σ' : H0 U.LG.L k) (f f' : ∀ α : D.toPre.X, D.toPre.SecB k α), SecIsMul G.hom a σ' σ → (∀ α, SecIsMul D.toPre.P.A.hom a (f' α) (f α)) → U.ExpandsAt e k σ f → U.ExpandsAt e k σ' f' := by
  intro R _ _ I D A G _ _ U e k a σ σ' f f' hσ hf hE
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f hE
  have hsf : ∀ α (y : (thickObj R I e G).left) J, sval (f' α) (pGl U e) y J =
      cst (pGl U e ≫ D.toPre.P.A.hom) y a * sval (f α) (pGl U e) y J := by
    intro α y J
    unfold sval
    exact gs_eq_cst_mul_gs_of_secIsMul (hf α) _ _ _
  have hsσ : ∀ (y : (thickObj R I e G).left) jL, sv U k σ' (fGl I G e) y jL =
      cst (fGl I G e ≫ G.hom) y a * sv U k σ (fGl I G e) y jL := by
    intro y jL
    unfold sv
    exact gs_eq_cst_mul_gs_of_secIsMul hσ _ _ _
  have hmap : fGl I G e ≫ G.hom = pGl U e ≫ D.toPre.P.A.hom := by
    simp only [fGl, pGl, Over.w]
  refine expandsAt_of_val U e k σ' f' S ?_
  intro y J hJ
  obtain ⟨h0, h1⟩ := hS _ (𝟙 _) y J hJ
  simp only [Category.id_comp] at h0 h1
  refine ⟨fun α hα => ?_, fun jL hmem => ?_⟩
  · rw [hsf, h0 α hα, mul_zero]
  · have h1' := h1 jL hmem
    rw [hsσ, hmap]
    have hsum : ∑ α ∈ S, sval (f' α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val =
        cst (pGl U e ≫ D.toPre.P.A.hom) y a *
          ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [hsf, _root_.mul_assoc]
    rw [hsum, ← h1']
    ring

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSecPowExt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section BoxValues

variable {X Y Z : Scheme.{0}}

private theorem gm_inv' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)ˣ) :
    gm r z U a⁻¹ = (gm r z U a)⁻¹ := by
  unfold gm
  rw [dite_eq_left h]
  exact map_inv _ a

private theorem gm_res' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {U V : Y.Opens} (hle : V ≤ U) (h : r z ∈ V)
    (a : Γ(Y, U)ˣ) : gm r z V (res hle a) = gm r z U a := by
  ext
  rw [← gs_unit r z V h, ← gs_unit r z U (hle h)]
  exact gs_res r z hle h a.val

theorem gs_secOfIso_eq {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB)
    (a : A.ι) (b : B.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ A.U a ⊓ B.U b) :
    gs r z (A.U a) ((secOfIso t hu hA hB).f a) =
      ((gm r z ((LB.div B A).U (b, a)) (u.s (b, a)))⁻¹).val * gs r z (B.U b) (t.f b) := by
  have hD : r z ∈ (LB.div B A).U (b, a) := divLe a b hz
  rw [← gs_res r z (inf_le_left : A.U a ⊓ B.U b ≤ A.U a) hz]
  change gs r z _ (rs inf_le_left ((secOfIso t hu hA hB).f a)) = _
  rw [secOfIso_spec t hu hA hB a b, isoCand, gs_mul r z _ hz, gs_unit r z _ hz, gm_inv' r z _ hz,
    gm_res' r z (divLe a b) hz]
  congr 1
  exact gs_res r z inf_le_right hz (t.f b)

theorem gs_boxSecGen_eq {X' Y' : Scheme.{0}} (L : LB X) {j : ℕ} (pr : Fin j → (X' ⟶ X)) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (p : Fin j → (Y' ⟶ Y)) (φ : Fin j → K → (Y ⟶ X))
    (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a) (σ : ∀ i, LB.Sec (LB.LinComb L (φ i) ε))
    (jN : K → Fin j → L.ι) (r : Z ⟶ Y') (z : Z) (hz : r z ∈ LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN) :
    gs r z _ ((boxSecGen L pr φ' ε p φ hφ σ).f jN) =
      ∏ i, gs (r ≫ p i) z (LB.wchart L (φ i) (fun a => jN a i)) ((σ i).f (fun a => jN a i)) := by
  change gs r z _ (boxSecGenF L pr φ' ε p φ hφ σ jN) = _
  rw [boxSecGenF, gs_prod r z _ hz]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [gs_res r z _ hz]
  exact gs_pull r (p i) z _ (box_le_of_comp L pr φ' (φ i) (p i) i (hφ i) jN hz) _

theorem exists_boxSec_val {X' Y' : Scheme.{0}} {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB) {j : ℕ}
    {pr : Fin j → (X' ⟶ X)} (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (p : Fin j → (Y' ⟶ Y)) (φ : Fin j → K → (Y ⟶ X))
    (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a) (σ : ∀ i, LB.Sec (LB.LinComb M (φ i) ε)) :
    ∃ σ' : LB.Sec (LB.LinComb M' φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J J'), Good M z J → Good M' z J' →
      (∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a).val * sval σ' r z J' =
        ∏ i, sval (σ i) (r ≫ p i) z J := by
  refine ⟨secOfIso (u := LB.linCombIso w φ' ε) (boxSecGen M pr φ' ε p φ hφ σ) (linCombIso_isGen w hw φ' ε)
    (linComb_isLB M' hM' φ' ε) (linComb_isLB _ (linComb_isLB M hM pr _) φ' ε), ?_⟩
  intro Z r z J J' hJ hJ'
  have hA : r z ∈ LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) := Good.mem hJ' φ' r
  have hB : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) :=
    Set.mem_iInter.2 fun a => Good.mem hJ pr (r ≫ φ' a)
  have h1 := gs_secOfIso_eq (LB.linCombIso w φ' ε) (boxSecGen M pr φ' ε p φ hφ σ) (linCombIso_isGen w hw φ' ε)
    (linComb_isLB M' hM' φ' ε) (linComb_isLB _ (linComb_isLB M hM pr _) φ' ε) (fun a => J' (r ≫ φ' a))
    (fun a i => J ((r ≫ φ' a) ≫ pr i)) r z ⟨hA, hB⟩
  have h2 := gs_boxSecGen_eq M pr φ' ε p φ hφ σ (fun a i => J ((r ≫ φ' a) ≫ pr i)) r z hB
  have h3 := gm_linCombIso w φ' ε r z (fun a i => J ((r ≫ φ' a) ≫ pr i)) (fun a => J' (r ≫ φ' a)) ⟨hB, hA⟩
  rw [sval_of _ r z J' (fun a => J' (r ≫ φ' a)) (fun _ => rfl)]
  erw [h1, h3, h2, Units.mul_inv_cancel_left]
  refine Finset.prod_congr rfl (fun i _ => (sval_of (σ i) (r ≫ p i) z J _ (fun a => ?_)).symm)
  rw [Category.assoc, Category.assoc, hφ]

end BoxValues

theorem exists_boxSec_pow_ext : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (t : Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))), ∃ t' : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))), (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval t' r z J' = ∏ i, Geo.Tor.sval (t i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J) := by
  intro R _ _ j A A' pA F _ _ k t
  have hφ : ∀ (i : Fin j) (_ : Fin 1), (snd (TFK (R := R) F) A'.A).left ≫ (pA.pr i).left =
      ((TFK (R := R) F) ◁ pA.pr i).left ≫ (snd (TFK (R := R) F) A.A).left := fun i _ => by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  obtain ⟨t', ht'⟩ := exists_boxSec_val A.isLB A'.isLB pA.w pA.w_gen
    (fun _ : Fin 1 => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))
    (fun i => ((TFK (R := R) F) ◁ pA.pr i).left) (fun _ _ => (snd (TFK (R := R) F) A.A).left) hφ t
  refine ⟨t', fun Z r z J J' hJ hJ' => ?_⟩
  have h := ht' Z r z J J' hJ hJ'
  rw [Fin.prod_univ_one, zpow_natCast] at h
  exact h

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitValue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma eSec_pullback_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec ((Over.pullback p).obj G) ≫ pullback.fst G.hom p = p ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

lemma krull_ext {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (W : (Spec (CommRingCat.of V)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of V), W))
    (h : ∀ (e : ℕ) (z), gs (thick V (maximalIdeal V) e) z W a = gs (thick V (maximalIdeal V) e) z W b) :
    a = b := by
  subst hW
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom).1
  apply hinj
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top, Ideal.mem_iInf]
  intro e
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ?_)
  have key : ((thick V (maximalIdeal V) e).app ⊤).hom a = ((thick V (maximalIdeal V) e).app ⊤).hom b := by
    refine fn_ext fun z hz => ?_
    rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp]
    exact h e z
  have nat := fun x => congrArg (fun φ => φ.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  exact (nat a).symm.trans ((congrArg _ key).trans (nat b))

lemma trF_unique {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] [Unique K] (φ : Y ⟶ X) (n : ℤ) (r : Z ⟶ Y)
    (z : Z) (J : (Z ⟶ X) → L.ι) (j : L.ι) (q : Z ⟶ X) (hq : r ≫ φ = q) :
    trF (L := L) (fun _ : K => φ) (fun _ => n) r z (fun _ => J (r ≫ φ)) (fun _ => j) =
      gm q z (L.U (J q) ⊓ L.U j) (L.g (J q) j) ^ n := by
  subst hq
  exact Fintype.prod_unique _

def thU (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) :
    (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
  thick R I e

section Thick

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

lemma eSec_fGl : eSec (thickObj R I e G) ≫ fGl I G e = thU R I e ≫ eSec G :=
  eSec_pullback_fst _ _

lemma eSec_pGl : eSec (thickObj R I e G) ≫ pGl U e = thU R I e ≫ eSec D.toPre.P.A := by
  have := (U.gt e).q_hom
  have h1 : (η[thickObj R I e G] ≫ (U.gt e).q) = η[thickObj R I e D.toPre.P.A] := IsMonHom.one_hom _
  have h2 : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.toPre.P.A) :=
    congrArg Over.Hom.left h1
  refine Eq.trans ?_ (eSec_pullback_fst (thick R I e) _)
  rw [← h2, Category.assoc]
  rfl

lemma eSec_map (f : G ⟶ G) [IsMonHom f] :
    eSec (thickObj R I e G) ≫ ((Over.pullback (thick R I e)).map f).left = eSec (thickObj R I e G) :=
  congrArg Over.Hom.left (IsMonHom.one_hom ((Over.pullback (thick R I e)).map f))

lemma wv_rig (z : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : (thU R I e ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U jM) (hL : (thU R I e ≫ eSec G) z ∈ U.LG.L.U jL) :
    wv U e (eSec (thickObj R I e G)) z jM jL *
      gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => jL)) (U.LG.rig.s (fun _ => jL)) =
      gm (thU R I e) z ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM)) (D.toPre.rig.s (fun _ => jM)) := by
  have m₁ : z ∈ eSec (thickObj R I e G) ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL)) :=
    ⟨mem_pull.2 ((congrArg (fun g => g z ∈ D.toPre.P.L.U jM) (eSec_pGl U e)).mpr hM),
      mem_pull.2 ((congrArg (fun g => g z ∈ U.LG.L.U jL) (eSec_fGl (G := G) e)).mpr hL)⟩
  have m₂ : z ∈ thU R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) := mem_pull.2 hL
  have m₃ : z ∈ thU R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := mem_pull.2 hM
  have hz : z ∈ (eSec (thickObj R I e G) ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL))) ⊓ thU R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) ⊓
      thU R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := ⟨⟨m₁, m₂⟩, m₃⟩
  have W := congrArg (gm (𝟙 _) z _) (U.w_rig e (fun _ => jM, fun _ => jL) _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ _ z _ _ _ hz _) (gm_rp₁ _ z _ _ _ hz _))).symm.trans
    (W.trans (gm_rp₁ _ z _ _ _ hz _))

lemma unit_value_thick (f : G ⟶ G) [IsMonHom f] {g : D.toPre.P.A.left ⟶ D.toPre.P.A.left} {N : ℕ} (hN : 0 < N)
    {ε : Fin 2 → ℤ} (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, g] ε))
    (hX : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (1 * (N - 1))))
    (k : ℕ) (σ'' : H0 U.LG.L (k * N)) (τ : H0 U.LG.L k)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J → ∀ jL jL',
      (r ≫ fGl I G e) z ∈ U.LG.L.U jL →
      ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ fGl I G e) z ∈ U.LG.L.U jL' →
      (wv U e r z (J (r ≫ pGl U e)) jL ^ (k * N)).val * sv U (k * N) σ'' (r ≫ fGl I G e) z jL =
        (val X (r ≫ pGl U e) z J ^ k).val *
          ((wv U e (r ≫ ((Over.pullback (thick R I e)).map f).left) z
            (J ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ pGl U e)) jL' ^ k).val *
            sv U k τ ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ fGl I G e) z jL'))
    (z : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left) (j : U.LG.L.ι)
    (hj : (thU R I e ≫ eSec G) z ∈ U.LG.L.U j) :
    sv U (k * N) σ'' (thU R I e ≫ eSec G) z j =
      (gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => j)) (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        sv U k τ (thU R I e ≫ eSec G) z j := by
  choose J hJ using fun ψ : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left ⟶ D.toPre.P.A.left =>
    exists_chart D.toPre.P.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have E := H _ (eSec (thickObj R I e G)) z J hJ j j (by rw [eSec_fGl]; exact hj)
    (by rw [eSec_map, eSec_fGl]; exact hj)
  rw [eSec_map, eSec_fGl, eSec_pGl] at E
  have hw := wv_rig U e z _ j (hJ (thU R I e ≫ eSec D.toPre.P.A)) hj
  have hx : val X (thU R I e ≫ eSec D.toPre.P.A) z J =
      gm (thU R I e) z ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => J (thU R I e ≫ eSec D.toPre.P.A)))
        (D.toPre.rig.s (fun _ => J (thU R I e ≫ eSec D.toPre.P.A))) ^ (1 * (N - 1)) :=
    (val_pull hJ X _ _).symm.trans ((val_corr hJ hX _).trans (map_pow _ _ _))
  rw [hx, ← hw] at E
  generalize wv U e (eSec (thickObj R I e G)) z (J (thU R I e ≫ eSec D.toPre.P.A)) j = w at E
  generalize gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => j)) (U.LG.rig.s (fun _ => j)) = u at E ⊢
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  refine (w ^ (k * (n + 1))).mul_right_inj.1 (E.trans ?_)
  simp only [Nat.add_sub_cancel, Units.val_pow_eq_pow_val, Units.val_mul]
  ring

end Thick

theorem unit_value {V : Type} [CommRing V] [IsDomain V] [IsNoetherianRing V] [IsLocalRing V]
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    (U : UnifPre (maximalIdeal V) D A G) {N : ℕ} (hN : 0 < N) (k : ℕ) (σ'' : H0 U.LG.L (k * N)) (τ : H0 U.LG.L k)
    (H : ∀ (e : ℕ) (z) (j : U.LG.L.ι), (thU V (maximalIdeal V) e ≫ eSec G) z ∈ U.LG.L.U j →
      sv U (k * N) σ'' (thU V (maximalIdeal V) e ≫ eSec G) z j =
      (gm (thU V (maximalIdeal V) e) z ((U.LG.L.pull (eSec G)).U (fun _ => j))
        (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val * sv U k τ (thU V (maximalIdeal V) e ≫ eSec G) z j)
    (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (J) (hJ : Good U.LG.L y J) :
    sval σ'' (r ≫ eSec G) y J =
      (val (L := U.LG.L) U.LG.rig r y J ^ (k * (N - 1))).val * sval τ (r ≫ eSec G) y J := by
  obtain ⟨j, hj⟩ := exists_chart U.LG.isLB (eSec G (IsLocalRing.closedPoint V))
  have hj' : ∀ x, eSec G x ∈ U.LG.L.U j := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := V) x).map (eSec G).continuous).mem_open (U.LG.L.U j).isOpen hj
  let W₁ : G.left.Opens := LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)
  have m₁ : ∀ x, eSec G x ∈ W₁ := fun x => Set.mem_iInter.2 fun _ => hj' x
  let W : (𝟙_ (Over (Spec (CommRingCat.of V)))).left.Opens := (U.LG.L.pull (eSec G)).U (fun _ => j)
  have m : ∀ x, x ∈ W := fun x => mem_pull.2 (hj' x)
  have hle : W ≤ eSec G ⁻¹ᵁ W₁ := fun x _ => m₁ x
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (s : Γ(G.left, W₁)),
      gs r y W (rs hle (((eSec G).app W₁).hom s)) = gs (r ≫ eSec G) y W₁ s := fun Z r y s =>
    (gs_res r y hle (m _) _).trans (gs_pull r (eSec G) y W₁ (m₁ _) s)
  have ev' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z),
      gs r y W ((@id Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, W)ˣ (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        rs hle (((eSec G).app W₁).hom (τ.f (fun _ => j)))) =
      (gm r y W (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val * sv U k τ (r ≫ eSec G) y j := fun Z r y =>
    (gs_mul r y W (m _) _ _).trans (congrArg₂ (· * ·) ((gs_unit r y W (m _) _).trans
      (congrArg Units.val (map_pow _ _ _))) (ev Z r y _))
  have key : rs hle (((eSec G).app W₁).hom (σ''.f (fun _ => j))) =
      (@id Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, W)ˣ (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        rs hle (((eSec G).app W₁).hom (τ.f (fun _ => j))) :=
    krull_ext W (eq_top_iff.2 fun x _ => m x) _ _ fun e z =>
      (ev _ (thU V (maximalIdeal V) e) z _).trans ((H e z j (hj' _)).trans (ev' _ (thU V (maximalIdeal V) e) z).symm)
  have E := (ev Z r y _).symm.trans ((congrArg (gs r y W) key).trans (ev' Z r y))
  have a₁ : sval σ'' (r ≫ eSec G) y J = _ :=
    sec_trans σ'' (r ≫ eSec G) y (hJ.mem _ (r ≫ eSec G)) (j' := fun _ => j) (m₁ _)
  have a₂ : sval τ (r ≫ eSec G) y J = _ :=
    sec_trans τ (r ≫ eSec G) y (hJ.mem _ (r ≫ eSec G)) (j' := fun _ => j) (m₁ _)
  have a₃ : val (L := U.LG.L) U.LG.rig r y J = _ :=
    gen_trans (L := U.LG.L) U.LG.rigGen r y (hJ.mem _ r) (j' := fun _ => j) (m _)
  rw [a₁, a₂, a₃]
  refine (congrArg _ E).trans ?_
  rw [trF_unique _ _ _ _ J j (r ≫ eSec G) (Category.comp_id _), trF_unique _ _ _ _ J j (r ≫ eSec G) (Category.comp_id _),
    trF_unique _ _ _ _ J j (r ≫ eSec G) rfl]
  simp only [zpow_natCast, zpow_one]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have alg : ∀ (c u : (Z.presheaf.stalk y)ˣ) (s : Z.presheaf.stalk y), (c ^ (k * (n + 1))).val * ((u ^ (k * n)).val * s) =
      ((c * u) ^ (k * n)).val * ((c ^ k).val * s) := fun c u s => by
    simp only [Units.val_pow_eq_pow_val, Units.val_mul]
    ring
  exact alg _ _ _

theorem value_at_unit_section : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), X.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ X (eSec P.D.toPre.P.A)) (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig (1 * (N - 1))) → ∀ (k : ℕ) (σ'' : H0 P.U.LG.L (k * N)) (τ : H0 P.U.LG.L k), (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k * N)).val * sv P.U.toUnifPre (k * N) σ'' (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k).val * sv P.U.toUnifPre k τ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval σ'' (r ≫ eSec t.G) y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig r y J ^ (k * (N - 1))).val * Geo.Tor.sval τ (r ≫ eSec t.G) y J := by
  intro V _ _ _ E _ _ _ H t P a N _ hN X _ hX k σ'' τ h
  have := t.act.hom a
  exact unit_value P.U.toUnifPre hN k σ'' τ fun e => unit_value_thick P.U.toUnifPre e (t.act.act a) hN X hX k σ'' τ (h e)

end GlobalTheory.UnitValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSub
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_of_eq_sub {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (V : X.Opens) {a b c : Γ(X, V)} (h : a = b - c) :
    gs r z V a = gs r z V b - gs r z V c := by
  subst h
  unfold gs
  split_ifs <;> simp [map_sub]

theorem expandsAt_sub : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ₁ σ₂ σ : H0 U.LG.L k)
    (f₁ f₂ f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ j, σ.f j = σ₁.f j - σ₂.f j) →
    (∀ α j, (f α).f j = (f₁ α).f j - (f₂ α).f j) → U.ExpandsAt e k σ₁ f₁ → U.ExpandsAt e k σ₂ f₂ →
    U.ExpandsAt e k σ f := by
  intro R _ _ I D A G _ _ U e k σ₁ σ₂ σ f₁ f₂ f hσ hf h₁ h₂
  classical
  obtain ⟨S₁, H₁⟩ := ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val U e k σ₁ f₁ h₁
  obtain ⟨S₂, H₂⟩ := ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val U e k σ₂ f₂ h₂
  refine ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_of_val U e k σ f (S₁ ∪ S₂) ?_
  intro y J hJ
  obtain ⟨z1, e1⟩ := H₁ _ (𝟙 _) y J hJ
  obtain ⟨z2, e2⟩ := H₂ _ (𝟙 _) y J hJ
  simp only [Category.id_comp] at z1 z2 e1 e2
  have hs : ∀ α, sval (f α) (ReciprocityTheory.ChartRestriction.G.DVR.pGl U e) y J =
      sval (f₁ α) (ReciprocityTheory.ChartRestriction.G.DVR.pGl U e) y J - sval (f₂ α) (ReciprocityTheory.ChartRestriction.G.DVR.pGl U e) y J := by
    intro α
    first
      | exact gs_of_eq_sub _ _ _ (hf α _)
      | (unfold sval; exact gs_of_eq_sub _ _ _ (hf α _))
      | (simp only [sval]; exact gs_of_eq_sub _ _ _ (hf α _))
  refine ⟨fun α hα => ?_, fun jL hjL => ?_⟩
  · rw [hs α, z1 α (fun h => hα (Finset.mem_union_left _ h)),
      z2 α (fun h => hα (Finset.mem_union_right _ h)), sub_zero]
  · have hsv : ReciprocityTheory.ChartRestriction.G.DVR.sv U k σ (ReciprocityTheory.ChartRestriction.G.DVR.fGl I G e) y jL =
        ReciprocityTheory.ChartRestriction.G.DVR.sv U k σ₁ (ReciprocityTheory.ChartRestriction.G.DVR.fGl I G e) y jL -
          ReciprocityTheory.ChartRestriction.G.DVR.sv U k σ₂ (ReciprocityTheory.ChartRestriction.G.DVR.fGl I G e) y jL := by
      unfold ReciprocityTheory.ChartRestriction.G.DVR.sv
      exact gs_of_eq_sub _ _ _ (hσ _)
    have s1 := Finset.sum_subset (Finset.subset_union_left (s₂ := S₂))
      (fun α (_ : α ∈ S₁ ∪ S₂) (hα : α ∉ S₁) => show
        sval (f₁ α) (ReciprocityTheory.ChartRestriction.G.DVR.pGl U e) y J * (val (ReciprocityTheory.ChartRestriction.G.DVR.tG U e α) (𝟙 _) y J).val = 0 by
          rw [z1 α hα, zero_mul])
    have s2 := Finset.sum_subset (Finset.subset_union_right (s₁ := S₁))
      (fun α (_ : α ∈ S₁ ∪ S₂) (hα : α ∉ S₂) => show
        sval (f₂ α) (ReciprocityTheory.ChartRestriction.G.DVR.pGl U e) y J * (val (ReciprocityTheory.ChartRestriction.G.DVR.tG U e α) (𝟙 _) y J).val = 0 by
          rw [z2 α hα, zero_mul])
    rw [hsv, mul_sub, e1 jL hjL, e2 jL hjL, s1, s2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [hs α, sub_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsFSum
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpansionLinear

section General

variable {X Y Y' : Scheme.{0}}

def secComb {L : LB X} {I : Type} [Fintype I] (c : I → Γ(X, ⊤)) (s : I → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (c i) * (s i).f j
  compat := fun j j' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (c i) (s i)).compat j j'

theorem resTop_mul (W : X.Opens) (a b : Γ(X, ⊤)) : resTop W (a * b) = resTop W a * resTop W b := by
  simp only [resTop, map_mul]

theorem app_resTop (h : Y ⟶ X) (W : X.Opens) (a : Γ(X, ⊤)) :
    (h.app W).hom (resTop W a) = resTop _ (h.appTop.hom a) := by
  simp only [resTop, Scheme.Hom.appTop]
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

private theorem presheaf_map_resTop_eq_resTop {W W' : X.Opens} (h : W' ≤ W) (c : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resTop W c) = resTop W' c := by
  simp only [resTop, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_comb {W W' : X.Opens} (hW : W' ≤ W) {I : Type} [Fintype I] (a : I → Γ(X, ⊤)) (y : I → Γ(X, W))
    (x : Γ(X, W)) (hx : x = ∑ l, resTop W (a l) * y l) :
    (X.presheaf.map (homOfLE hW).op).hom x = ∑ l, resTop W' (a l) * (X.presheaf.map (homOfLE hW).op).hom (y l) := by
  subst hx
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, presheaf_map_resTop_eq_resTop]

theorem pull_comb (h : Y ⟶ X) {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ h ⁻¹ᵁ W) {I : Type} [Fintype I]
    (a : I → Γ(X, ⊤)) (y : I → Γ(X, W)) (x : Γ(X, W)) (hx : x = ∑ l, resTop W (a l) * y l) :
    (Y.presheaf.map (homOfLE hW).op).hom ((h.app W).hom x) =
      ∑ l, resTop W' (h.appTop.hom (a l)) * (Y.presheaf.map (homOfLE hW).op).hom ((h.app W).hom (y l)) := by
  subst hx
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, app_resTop, presheaf_map_resTop_eq_resTop]

private theorem sum_mul_sum_eq_sum_reindex_sigma {M : Type} [CommRing M] {I : Type} [Fintype I] {m : I → ℕ} {N : ℕ}
    (e : Fin N ≃ Σ l, Fin (m l)) (A : I → M) (C P : ∀ l, Fin (m l) → M) (C' : Fin N → M)
    (hC : ∀ i, C' i = A (e i).1 * C (e i).1 (e i).2) :
    ∑ l, A l * ∑ i, C l i * P l i = ∑ i, C' i * P (e i).1 (e i).2 := by
  rw [Fintype.sum_equiv e (fun i => C' i * P (e i).1 (e i).2) (fun x => A x.1 * C x.1 x.2 * P x.1 x.2)
    (fun i => by rw [hC]), Fintype.sum_sigma]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm

theorem secLin_comb (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (h : Y' ⟶ Y)
    {I : Type} [Fintype I] (a : I → Γ(Y', ⊤)) (s : I → LB.Sec (LB.LinComb L φ₁ ε₁))
    (s₀ : LB.Sec (LB.LinComb L φ₁ ε₁)) (h₀ : ∀ j, s₀.f j = ∑ l, resTop _ (a l) * (s l).f j)
    {m : I → ℕ} (σ : ∀ l, Fin (m l) → LB.Sec (LB.LinComb L φ₂ ε₂)) (c : ∀ l, Fin (m l) → Γ(Y', ⊤))
    (H : ∀ l, GeneratorPullback.SecLin L φ₁ ε₁ (s l) φ₂ ε₂ (σ l) h (c l)) {N : ℕ} (e : Fin N ≃ Σ l, Fin (m l))
    (c' : Fin N → Γ(Y', ⊤)) (hc' : ∀ i, c' i = a (e i).1 * c (e i).1 (e i).2) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₀ φ₂ ε₂ (fun i => σ (e i).1 (e i).2) h c' := by
  intro j₁ j₂ hc
  rw [res_comb (W := L.wchart φ₁ j₁) _ a (fun l => (s l).f j₁) (s₀.f j₁) (h₀ j₁)]
  have H' := fun l => H l j₁ j₂ hc
  simp only [H']
  exact sum_mul_sum_eq_sum_reindex_sigma e _ _ _ _ (fun i => by rw [hc', resTop_mul])

theorem isoRelM_comb {X₁ X₂ Z₁ Z₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂)
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y)
    (k : ℕ) (g₁ : Z₁ ⟶ X₁) (h₁ : Y' ⟶ Z₁) (g₂ : Z₂ ⟶ X₂) (h₂ : Y' ⟶ Z₂)
    (e₁ : h₁ ≫ g₁ = m ≫ f₁) (e₂ : h₂ ≫ g₂ = m ≫ f₂) {I : Type} [Fintype I]
    (a : I → LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (b : I → LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ))))
    (α : I → Γ(Z₁, ⊤)) (β : I → Γ(Z₂, ⊤)) (hαβ : ∀ l, h₁.appTop.hom (α l) = h₂.appTop.hom (β l))
    (a₀ : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (b₀ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ))))
    (ha : ∀ j, a₀.f j = ∑ l, resTop _ (α l) * (a l).f j)
    (hb : ∀ j, b₀.f j = ∑ l, resTop _ (β l) * (b l).f j)
    (H : ∀ l, GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ (a l) g₂ h₂ (b l)) :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a₀ g₂ h₂ b₀ := by
  refine ⟨e₁, e₂, fun p j₁ j₂ hj₁ hj₂ => ?_⟩
  rw [pull_comb h₂ (W := L₂.wchart (fun _ => g₂) j₂) _ β (fun l => (b l).f j₂) (b₀.f j₂) (hb j₂),
    pull_comb h₁ (W := L₁.wchart (fun _ => g₁) j₁) _ α (fun l => (a l).f j₁) (a₀.f j₁) (ha j₁), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(H l).2.2 p j₁ j₂ hj₁ hj₂, ← hαβ l, mul_left_comm]

theorem scal_mul {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (a b : R) :
    scal p (a * b) = scal p a * scal p b := by
  simp only [scal, map_mul]

end General

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {I : Type} (S : Finset I) (s : I → Fam D F k) (α : D.X) (j) :
    ((∑ l ∈ S, s l).s α).f j = ∑ l ∈ S, ((s l).s α).f j := by
  classical
  refine Finset.induction_on S ?_ (fun a S ha ih => ?_)
  · rw [Finset.sum_empty, Finset.sum_empty]
    rfl
  · rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

private theorem genF_left_comp_fst_TFK {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (U.genF F).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
  unfold UnifPre.genF
  rw [← Over.comp_left, lift_fst]

private theorem genF_left_comp_snd_TFK {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
  unfold UnifPre.genF
  rw [← Over.comp_left, lift_snd, Over.comp_left]

theorem expandsF_sum : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ (n : ℕ) (c : Fin n → F) (t : Fin n → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))) (s : Fin n → Fam D.toPre F k) (t₀ : LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))), (∀ l, U.ExpandsF F k w (t l) (s l)) → (∀ jj, t₀.f jj = ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (t l).f jj) → U.ExpandsF F k w t₀ (∑ l, c l • s l) := by
  intro R _ _ I D A G _ _ U F _ _ k w hw n c t s t₀ ht h0
  choose σ hσ using ht
  choose m cc σ₁ f hE hS hF using fun l => (hσ l).2
  have e₂ : 𝟙 _ ≫ UnifPre.gFK (G := G) F =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R) := by
    unfold UnifPre.gFK
    exact Category.id_comp _
  refine ⟨secComb (fun l => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c l)) σ, ?_, ?_⟩
  · exact isoRelM_comb A.L U.LG.L _ _ w _ k _ _ _ _ (genF_left_comp_snd_TFK U F) e₂ t σ
      (fun l => scal (fst (TFK (R := R) F) A.A).left (c l)) _
      (fun l => by rw [← genF_left_comp_fst_TFK U F]; rfl) t₀ _ h0 (fun _ => rfl) (fun l => (hσ l).1)
  · refine ⟨∑ l, m l, fun i => c (finSigmaFinEquiv.symm i).1 * cc _ (finSigmaFinEquiv.symm i).2,
      fun i => σ₁ _ (finSigmaFinEquiv.symm i).2, fun i => f _ (finSigmaFinEquiv.symm i).2,
      fun i e => hE _ _ e, ?_, fun α => ?_⟩
    · exact secLin_comb U.LG.L _ _ _ _ _ _ σ _ (fun _ => rfl) σ₁ _ hS finSigmaFinEquiv.symm _
        (fun i => scal_mul _ _ _)
    · refine secLin_comb D.toPre.P.L _ _ _ _ _
        (fun l => scal (fst (TF (R := R) F) D.toPre.P.A).left (c l)) (fun l => (s l).s α) _
        (fun j => by rw [fam_sum_f]; rfl) (fun l i => f l i α) _ (fun l => hF l α) finSigmaFinEquiv.symm _
        (fun i => scal_mul _ _ _)

end GlobalTheory.ExpansionLinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VanishOfTermsVanish
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClosedFibreTerm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem vanish_of_terms_vanish {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (h : U.ExpandsAt e k σ f)
    (h0 : ∀ α j, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) (j) :
    ((fstG I e G).left.app _).hom (σ.f j) = 0 := by
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have H := (hS _ (𝟙 _) y J hJ).2 jL (Set.mem_iInter.1 hy 0)
  have hz : ∀ α, sval (f α) (𝟙 _ ≫ pGl U e) y J = 0 := fun α => by
    have m := hJ.mem (D.toPre.famφB α) (𝟙 _ ≫ pGl U e)
    exact (gs_pull (𝟙 _) _ y _ m _).symm.trans ((congrArg (gs (𝟙 _) y _) (h0 α _)).trans (gs_zero (𝟙 _) y _ m))
  rw [Finset.sum_eq_zero fun α _ => by rw [hz α, zero_mul]] at H
  exact (gs_pull (𝟙 _) _ y _ hy _).trans (((Units.mul_right_eq_zero _).1 H).trans (gs_zero (𝟙 _) y _ hy).symm)

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (σ : H0 U.LG.L 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), U.ExpandsAt 0 1 σ g → (∀ χ, χ ≠ 0 → ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom ϖ (g χ) g') → ((∃ j, ((fstG (maximalIdeal V) 0 G).left.app _).hom (σ.f j) ≠ 0) ↔ ¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ (g 0) g') := by
  intro V _ _ _ ϖ hϖ D A G _ _ U σ g hE hχ
  have Q : ∀ α : D.toPre.X, (∀ j, ((U.gt 0).pG.left.app _).hom ((g α).f j) = 0) ↔
      ∃ g' : D.toPre.SecB 1 α, SecIsMul D.toPre.P.A.hom ϖ (g α) g' := fun α => by
    have := GlobalTheory.ExtDiv.main V ϖ hϖ D A G U 0 1 α (g α)
    have hp : ϖ ^ (0 + 1) = ϖ := pow_one ϖ
    rwa [hp] at this
  rw [← not_forall]
  refine not_congr ⟨fun h => (Q 0).1 (WeightPf.weightIndep V _ D A G U 0 1 σ g h hE 0), fun h => ?_⟩
  refine vanish_of_terms_vanish U 0 1 σ g hE fun α => (Q α).2 ?_
  by_cases hα : α = 0
  · subst hα; exact h
  · exact hχ α hα

end GlobalTheory.ClosedFibreTerm
end
