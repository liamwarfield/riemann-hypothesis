module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

def trV {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι) (n : ℤ) : A :=
  valR y (L.U a ⊓ L.U b) ((L.g a b) ^ n).val

def pickJ {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) (i : Fin 4) : Ix :=
  jf (Classical.epsilon fun i' => φs i' = φs i)

theorem pickJ_congr {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) {i₁ i₂ : Fin 4}
    (h : φs i₁ = φs i₂) : pickJ φs jf i₁ = pickJ φs jf i₂ := by
  unfold pickJ; rw [h]

theorem pickJ_spec {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) (i : Fin 4) :
    ∃ i', φs i' = φs i ∧ pickJ φs jf i = jf i' :=
  ⟨_, Classical.epsilon_spec (p := fun i' => φs i' = φs i) ⟨i, rfl⟩, rfl⟩

theorem trV_add {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n m : ℤ) : trV L y a b n * trV L y a b m = trV L y a b (n + m) := by
  unfold trV
  rw [zpow_add, Units.val_mul, GlobalTheory.ZH.CrdCalc.valR_mul y _ h]

theorem isUnit_trV {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n : ℤ) : IsUnit (trV L y a b n) := by
  unfold trV
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ h]
  exact (Units.isUnit _).map _

theorem top_le_wchart {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (h : ∀ k, ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k)) : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j :=
  fun q _ => Set.mem_iInter.2 fun k => h k (x := q) trivial

theorem wchart_top_le {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j) (k : K) : ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k) :=
  fun q _ => Set.mem_iInter.1 (h (x := q) trivial) k

theorem trV_zero {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) : trV L y a b 0 = 1 := by
  unfold trV
  rw [zpow_zero, Units.val_one, GlobalTheory.ZH.CrdCalc.valR_eq y _ h, map_one]

theorem trV_pow {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n : ℤ) (m : ℕ) : trV L y a b n ^ m = trV L y a b (n * m) := by
  unfold trV
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ h, GlobalTheory.ZH.CrdCalc.valR_eq y _ h, ← map_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
    ← zpow_mul]

end GlobalTheory.MBLow.TanGauge

namespace GlobalTheory.MBLow.TanGauge

theorem gl_corr : ∀ {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')),
    LB.Gen.Corr L φ ε φ' ε' t t' → ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' →
    (∀ k k', φ k = φ' k' → j k = j' k') → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ' j' →
    valR y (LB.wchart L φ j) (t.s j).val = valR y (LB.wchart L φ' j') (t'.s j').val := by
  intro X Y L K K' _ _ φ ε φ' ε' t t' hc j j' hj hj' hx A _ y h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := fun q hq => ⟨h hq, h' hq⟩
  have e := congrArg Units.val (hc j j' hj hj' hx)
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ j) hh (t.s j).val
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ' j') hh (t'.s j').val
  refine e1.symm.trans (Eq.trans ?_ e2)
  exact congrArg (valR y _) e

theorem gl_pullGen : ∀ {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (j : K → L.ι) {A : Type} [CommRing A] (y : Sp A ⟶ Z),
    ⊤ ≤ (y ≫ h) ⁻¹ᵁ LB.wchart L φ j →
    valR y (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε c h).s j).val = valR (y ≫ h) (LB.wchart L φ j) (c.s j).val := by
  intro X Y Z L K _ φ ε c h j A _ y hy
  have hy' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j :=
    top_le_wchart L _ _ _ fun k => by rw [← Category.assoc]; exact wchart_top_le L _ _ _ hy k
  have e := GlobalTheory.ZH.CrdCalc.valR_res y ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j) hy' (pullU h _ (c.s j)).val
  refine e.trans ?_
  exact GlobalTheory.ZH.EvCrd.valR_comp y h (LB.wchart L φ j) (fun q hq => hy hq) _

theorem gl_gtφT_pull : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T T' : Over (Sp R)) (h : T'.left ⟶ T.left),
    h ≫ T.hom = T'.hom → ∀ (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A), b'.left = h ≫ b.left → ∀ (α : D.X) (i : Fin 4),
    DegPre.gtφT D T' b' α i = h ≫ DegPre.gtφT D T b α i := by
  intro R _ _ D T T' h hh b b' hb α i
  have hb' : b' = Over.homMk h hh ≫ b := by
    ext; simpa using hb
  subst hb'
  fin_cases i
  · change (padd D.P.A (DegPre.cT D T' α) (Over.homMk h hh ≫ b)).left = (Over.homMk h hh : T' ⟶ T).left ≫
      (padd D.P.A (DegPre.cT D T α) b).left
    rw [← Over.comp_left]; congr 1; simp [padd, comp_lift_assoc, DegPre.cT]
  · change (toUnit T' ≫ D.c α).left = (Over.homMk h hh : T' ⟶ T).left ≫ (toUnit T ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · show (Over.homMk h hh ≫ b).left = h ≫ b.left
    simp
  · change (toUnit T' ≫ η[D.P.A]).left = (Over.homMk h hh : T' ⟶ T).left ≫ (toUnit T ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_gtφT_famφB : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Sp R)) (b : T ⟶ D.P.A) (α : D.X) (i : Fin 4),
    DegPre.gtφT D T b α i = b.left ≫ D.famφB α (![1, 2, 0, 3] i) := by
  intro R _ _ D T b α i
  have pc : ∀ (x y : T ⟶ D.P.A), padd D.P.A x y = padd D.P.A y x := fun x y => by
    show x * y = y * x
    exact mul_comm x y
  fin_cases i
  · change (padd D.P.A (DegPre.cT D T α) b).left = b.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left, pc]; congr 1; simp [padd, comp_lift_assoc, DegPre.cT]
  · change (toUnit T ≫ D.c α).left = b.left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · exact (Category.comp_id _).symm
  · change (toUnit T ≫ η[D.P.A]).left = b.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_prB' : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A),
    (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫ (DegPre.prB D C).left =
      b.left := by
  intro R _ _ D C _ _ b
  rw [← Over.comp_left, lift_snd]

theorem gl_scal : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A) (c : C),
    valR (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ⊤
      (scal (fst (TF (R := R) C) D.P.A).left c) = TrivSqZeroExt.inl c := by
  intro R _ _ D C _ _ b c
  have hq : (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫
      (fst (TF (R := R) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h := GlobalTheory.ZH.FormCount.valR_scal (algebraMap C (DualNumber C)) _ _ hq ⊤ (fun _ _ => trivial) c
  have e : resTop ⊤ (scal (fst (TF (R := R) C) D.P.A).left c) = scal (fst (TF (R := R) C) D.P.A).left c := by
    simp [resTop]
  rw [e] at h
  rw [h, TrivSqZeroExt.algebraMap_eq_inl]

theorem gl_tan : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (gm₀ : GtPt D (epsR R)), GtTan gm₀ →
    redE R ≫ gm₀.b.left = eSec D.P.A := by
  intro R _ _ D gm₀ hT
  obtain ⟨o, ⟨hb, -⟩, h1, -⟩ := hT
  rw [← h1, hb]
  have hw := Over.w (toUnit (baseOver (Sp R)))
  have e : (toUnit (baseOver (Sp R))).left = 𝟙 _ := by simpa using hw
  simp only [DegPre.zeroT, Over.comp_left, e, Category.id_comp]
  rfl

theorem gl_TF : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    (TF (R := R) C).hom = spMap (toF R C) := by
  intro R _ _ C _ _
  simp only [TF, jFK, jK, Over.mk_hom, spMap, toF, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem gl_redE : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    redE C ≫ spMap (dualMap (toF R C)) = spMap (toF R C) ≫ redE R := by
  intro R _ _ C _ _
  simp only [redE, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  simp [dualMap, toF]

theorem gl_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    spMap (dualMap (toF R C)) ≫ (epsR R).hom = (TE R C).hom := by
  intro R _ _ C _ _
  simp only [TE, epsR, Over.mk_hom, gl_TF, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, toF, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.MBLow.TanGauge

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldPointMemOpenOfReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldPointMemOpenOfReduction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
namespace GlobalTheory.MBLow.TanGauge

theorem top_le_of_redE : ∀ (C : Type) [Field C] {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens),
    ⊤ ≤ (redE C ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U := by
  intro C _ X y U h q _
  have key : ∃ p : (Sp C : Scheme.{0}), (redE C) p = q := by
    have hsub : Subsingleton (PrimeSpectrum (DualNumber C)) := by
      refine ⟨fun a b => ?_⟩
      have aux : ∀ a : PrimeSpectrum (DualNumber C), ∀ x, x ∈ a.asIdeal ↔ x.fst = 0 := by
        intro a x
        constructor
        · intro hx
          by_contra hne
          exact a.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
            (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)))
        · intro hx
          refine a.2.mem_of_pow_mem 2 ?_
          have : x ^ 2 = 0 := by
            ext <;> simp [sq, hx]
          rw [this]; exact zero_mem _
      ext x; rw [aux, aux]
    exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C), hsub.elim _ _⟩
  obtain ⟨p, rfl⟩ := key
  exact h (x := p) trivial
end GlobalTheory.MBLow.TanGauge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldPointMemOpenOfReductionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumber_field_point_mem_open_of_reduction : ∀ (C : Type) [Field C] {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens),
    ⊤ ≤ (redE C ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U := by
  first | exact @GlobalTheory.MBLow.TanGauge.top_le_of_redE | exact GlobalTheory.MBLow.TanGauge.top_le_of_redE | (intros; apply GlobalTheory.MBLow.TanGauge.top_le_of_redE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinearRelationLinComb
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinearRelationLinComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

theorem valR_secLin : ∀ {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) {n : ℕ}
    (s₂ : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y) (c : Fin n → Γ(Y', ⊤)),
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c → ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y'),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ₁ j₁ → ⊤ ≤ (y ≫ h) ⁻¹ᵁ LB.wchart L φ₂ j₂ →
    valR y (LB.wchart L φ₁ j₁) (s₁.f j₁) = ∑ i, valR y ⊤ (c i) * valR (y ≫ h) (LB.wchart L φ₂ j₂) ((s₂ i).f j₂) := by
  intro X Y Y' L K₁ K₂ _ _ φ₁ ε₁ s₁ φ₂ ε₂ n s₂ h c H j₁ j₂ hc A _ y hy₁ hy₂
  have hy₂' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ₂ k) j₂ :=
    top_le_wchart L _ _ y fun k => by rw [← Category.assoc]; exact wchart_top_le L φ₂ j₂ (y ≫ h) hy₂ k
  have hW : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂) := fun q hq => ⟨hy₁ hq, hy₂' hq⟩
  have a₂ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ₂ j₂ :=
    inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  have e := congrArg (valR y (LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂)) (H j₁ j₂ hc)
  rw [← GlobalTheory.ZH.CrdCalc.valR_res y inf_le_left hW (s₁.f j₁)]
  refine e.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ hW, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← GlobalTheory.ZH.CrdCalc.valR_eq y _ hW, ← GlobalTheory.ZH.CrdCalc.valR_eq y _ hW]
  congr 1
  · exact GlobalTheory.ZH.CrdCalc.valR_res y le_top hW (c i)
  · exact (GlobalTheory.ZH.CrdCalc.valR_res y a₂ hW _).trans
      (GlobalTheory.ZH.EvCrd.valR_comp y h (LB.wchart L φ₂ j₂) (fun q hq => hy₂ hq) _)

end GlobalTheory.MBLow.TanGauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinearRelationLinCombStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValue_linear_relation_linComb : ∀ {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) {n : ℕ}
    (s₂ : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y) (c : Fin n → Γ(Y', ⊤)),
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c → ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y'),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ₁ j₁ → ⊤ ≤ (y ≫ h) ⁻¹ᵁ LB.wchart L φ₂ j₂ →
    valR y (LB.wchart L φ₁ j₁) (s₁.f j₁) = ∑ i, valR y ⊤ (c i) * valR (y ≫ h) (LB.wchart L φ₂ j₂) ((s₂ i).f j₂) := by
  first | exact @GlobalTheory.MBLow.TanGauge.valR_secLin | exact GlobalTheory.MBLow.TanGauge.valR_secLin | (intros; apply GlobalTheory.MBLow.TanGauge.valR_secLin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinCombChangeOfCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinCombChangeOfCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem valHom_res_pullU_zpow {X Y : Scheme.{0}} {A : Type} [CommRing A] (y : Sp A ⟶ Y) (f : Y ⟶ X)
    (U : X.Opens) {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V) (u : Γ(X, U)ˣ) (n : ℤ) :
    GlobalTheory.ZH.CrdCalc.valHom y V hV ((res e (pullU f U u)) ^ n : Γ(Y, V)ˣ).val = valR (y ≫ f) U (u ^ n).val := by
  rw [← map_zpow, ← map_zpow, ← GlobalTheory.ZH.CrdCalc.valR_eq y V hV]
  have hU : ⊤ ≤ y ⁻¹ᵁ f ⁻¹ᵁ U := hV.trans (y.preimage_mono e)
  refine (GlobalTheory.ZH.CrdCalc.valR_res y e hV _).trans ?_
  exact GlobalTheory.ZH.EvCrd.valR_comp y f U hU _

theorem valR_linComb_sec : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (s.f j) =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (s.f j') := by
  intro X Y L K _ φ ε s A _ y j j' h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y
    (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) hh (s.f j)
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y
    (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') hh (s.f j')
  rw [← e1, ← e2]
  have c := s.compat j j'
  change valR y _ ((Y.presheaf.map _).hom _) = _ * valR y _ ((Y.presheaf.map _).hom _)
  refine (congrArg (valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')) c).trans ?_
  refine (GlobalTheory.ZH.CrdCalc.valR_mul y (LB.wchart L φ j ⊓ LB.wchart L φ j') hh _ _).trans ?_
  congr 1
  refine (GlobalTheory.ZH.CrdCalc.valR_eq y (LB.wchart L φ j ⊓ LB.wchart L φ j') hh _).trans ?_
  dsimp only [LB.LinComb]
  rw [Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) := fun q _ =>
    ⟨wchart_top_le L φ j y h k (x := q) trivial, wchart_top_le L φ j' y h' k (x := q) trivial⟩
  unfold trV
  exact valHom_res_pullU_zpow y (φ k) (L.U (j k) ⊓ L.U (j' k)) (V := LB.wchart L φ j ⊓ LB.wchart L φ j') _ hh
    (L.g (j k) (j' k)) (ε k)

end GlobalTheory.MBLow.TanGauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinCombChangeOfChartsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValue_linComb_change_of_charts : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (s.f j) =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (s.f j') := by
  first | exact @GlobalTheory.MBLow.TanGauge.valR_linComb_sec | exact GlobalTheory.MBLow.TanGauge.valR_linComb_sec | (intros; apply GlobalTheory.MBLow.TanGauge.valR_linComb_sec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValueLinCombChangeOfCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValueLinCombChangeOfCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem valR_linComb_g_factor {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι)
    (hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) (k : K) :
    valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      ((res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
      (inf_le_right.trans (LB.wchart_le L φ j' k)) :
        LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
      (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k)).val = trV L (y ≫ φ k) (j k) (j' k) (ε k) := by
  have h0 : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k))
  have key : (res h0 (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))) ^ (ε k) =
      res h0 (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) ((L.g (j k) (j' k)) ^ (ε k))) :=
    ((congrArg (res h0) (map_zpow (pullU (φ k) (L.U (j k) ⊓ L.U (j' k))) _ _)).trans
      (map_zpow (res h0) _ _)).symm
  refine (congrArg (fun u => valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) key).trans ?_
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y h0 hh
      (((φ k).app (L.U (j k) ⊓ L.U (j' k))).hom ((L.g (j k) (j' k)) ^ (ε k)).val)
  refine Eq.trans ?_ (e1.trans ?_)
  · rfl
  · unfold trV
    exact GlobalTheory.ZH.EvCrd.valR_comp y (φ k) _ (hh.trans (y.preimage_mono h0)) _

theorem valR_gen_linComb : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (t.s j).val =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (t.s j').val := by
  intro X Y L K _ φ ε t ht A _ y j j' h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have e : valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      (res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) (t.s j)).val =
      valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      ((show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (res (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') (t.s j')).val) :=
    congrArg (fun u => valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) (ht j j')
  rw [GlobalTheory.ZH.CrdCalc.valR_mul y _ hh] at e
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) hh (t.s j).val
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') hh (t.s j').val
  have e3 : valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val =
      ∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k) := by
    change valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val (∏ k, _)) = _
    rw [Units.coe_prod, GlobalTheory.ZH.CrdCalc.valR_eq y _ hh, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← GlobalTheory.ZH.CrdCalc.valR_eq y _ hh]
    exact valR_linComb_g_factor L φ ε y j j' hh k
  rw [← e3]
  exact e1.symm.trans (e.trans (congrArg _ e2))

end GlobalTheory.MBLow.TanGauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValueLinCombChangeOfChartsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generatorValue_linComb_change_of_charts : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (t.s j).val =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (t.s j').val := by
  first | exact @GlobalTheory.MBLow.TanGauge.valR_gen_linComb | exact GlobalTheory.MBLow.TanGauge.valR_gen_linComb | (intros; apply GlobalTheory.MBLow.TanGauge.valR_gen_linComb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPowValueAtPointCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPowValueAtPointCocycle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem trV_cocycle : ∀ {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b c : L.ι) (n : ℤ),
    ⊤ ≤ y ⁻¹ᵁ L.U a → ⊤ ≤ y ⁻¹ᵁ L.U b → ⊤ ≤ y ⁻¹ᵁ L.U c →
    trV L y a b n * trV L y b c n = trV L y a c n := by
  intro X L hL A _ y a b c n ha hb hc
  have hT : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c) := fun q hq => ⟨⟨ha hq, hb hq⟩, hc hq⟩
  have e := congrArg (fun u => ((u ^ n : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ) : Γ(X, L.U a ⊓ L.U b ⊓ L.U c))) (hL.cocycle a b c)
  simp only [mul_zpow, ← map_zpow, Units.val_mul] at e
  have e' := congrArg (valR y (L.U a ⊓ L.U b ⊓ L.U c)) e
  rw [GlobalTheory.ZH.CrdCalc.valR_mul y _ hT] at e'
  unfold trV
  rw [← GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U b) hT,
    ← GlobalTheory.ZH.CrdCalc.valR_res y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U b ⊓ L.U c) hT,
    ← GlobalTheory.ZH.CrdCalc.valR_res y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U c) hT]
  exact e'

end GlobalTheory.MBLow.TanGauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPowValueAtPointCocycleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transitionUnitPowValueAtPoint_cocycle : ∀ {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b c : L.ι) (n : ℤ),
    ⊤ ≤ y ⁻¹ᵁ L.U a → ⊤ ≤ y ⁻¹ᵁ L.U b → ⊤ ≤ y ⁻¹ᵁ L.U c →
    trV L y a b n * trV L y b c n = trV L y a c n := by
  first | exact @GlobalTheory.MBLow.TanGauge.trV_cocycle | exact GlobalTheory.MBLow.TanGauge.trV_cocycle | (intros; apply GlobalTheory.MBLow.TanGauge.trV_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstJetTermsGaugeUnitMulBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

private theorem pre_lemma {Z Y X : Scheme.{0}} (x : Z ⟶ Y) (y : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    ⊤ ≤ (x ≫ y) ⁻¹ᵁ U := by
  intro p _
  have := h (show x.base p ∈ (⊤ : Y.Opens) from trivial)
  exact this

private theorem norm_natCast_le_one_kummer_theta_logarithms {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.Opens) (f : Γ(X, U)) (h : ⊤ ≤ x ⁻¹ᵁ U) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := pre_lemma _ _ _ h
  unfold valR
  rw [dite_eq_left h, dite_eq_left h']
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h (by intro _ _; trivial)]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e5 := fun w => congrArg (fun g => CommRingCat.Hom.hom g w) e2
  simp only [Scheme.Hom.appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e5
  simp only [spMap, CommRingCat.hom_comp, RingHom.comp_apply, ← e5]
  congr 1

private theorem univ_le_preimage_inf_of_univ_le {Z X : Scheme.{0}} (y : Z ⟶ X) (U V : X.Opens) (h1 : ⊤ ≤ y ⁻¹ᵁ U) (h2 : ⊤ ≤ y ⁻¹ᵁ V) :
    ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := by
  intro p hp
  exact ⟨h1 hp, h2 hp⟩

private theorem alg_lemma_5 {S : Type} [CommRing S] {n : ℕ} (a b : Fin n → S) (Ps g1 g2 g T : S)
    (h : Ps * (g1 * g2) = T) : (∑ i, a i * (Ps * b i)) * (g1 * (g2 * g)) = T * ∑ i, a i * (b i * g) := by
  rw [← h, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

private theorem mul_prod_four_rearrange {S : Type} [CommRing S] (a0 a1 a2 a3 b0 b1 b2 b3 : S) :
    a0 * a1 * a2 * a3 * (b0 * b1 * b2 * b3) = (a0 * b2) * (a1 * b0) * (a2 * b1) * (a3 * b3) := by
  ring

theorem jc_eq_unit_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR R)) (gm : GtPt D (TE R C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF R C))) gm₀ gm → ∀ (k : ℕ) (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∃ T : (DualNumber C)ˣ, GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left) ≠ 0 ∧ (T : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left)) ^ k = ν.rg ^ k ∧ ∀ (s : Fam D C k) (n : ℕ) (c : Fin n → C) (f : Fin n → ∀ α : D.X, D.SecB k α), (∀ α, GeneratorPullback.SecLin D.P.L (DegPre.famφ D C α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))) → ∀ α, jc ν s gm α = (T : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (GlobalTheory.MBLow.TanExp.termV J gm₀ (f i (ν.eX α))) := by
  intro R _ _ D C _ _ N ν gm₀ gm htan hpull k J hJ
  have hb : gm.b.left = spMap (dualMap (toF R C)) ≫ gm₀.b.left := hpull.1
  have hν : ∀ (P : Sp (DualNumber C) ⟶ D.P.A.left), ⊤ ≤ P ⁻¹ᵁ D.P.L.U (ν.J (redE C ≫ P)) :=
    fun P => GlobalTheory.T.dualNumber_field_point_mem_open_of_reduction C P _ (ν.good _)
  have hQ : redE C ≫ gm.b.left = (TF (R := R) C).hom ≫ eSec D.P.A := by
    rw [hb, ← Category.assoc, gl_redE, Category.assoc, gl_tan D gm₀ htan, ← gl_TF R C]
  have hJb : ∀ (p : Sp (DualNumber R) ⟶ D.P.A.left), ⊤ ≤ (spMap (dualMap (toF R C)) ≫ p) ⁻¹ᵁ D.P.L.U (J p) :=
    fun p => pre_lemma _ _ _ (hJ p)
  have hc0 : ⊤ ≤ gm.b.left ⁻¹ᵁ (D.P.L.U (ν.J (redE C ≫ gm.b.left)) ⊓ D.P.L.U (J gm₀.b.left)) :=
    univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb]; exact hJb _)
  have hcR : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => J gm₀.b.left) :=
    top_le_wchart _ _ _ _ (fun _ => by rw [Category.id_comp, ← gl_tan D gm₀ htan]; exact pre_lemma _ _ _ (hJ _))
  refine ⟨(isUnit_trV D.P.L gm.b.left _ _ hc0 (k : ℤ)).unit, ?_, ?_, ?_⟩
  · unfold TanExp.rigValD valR
    rw [dite_eq_left hcR]
    exact (((D.rig.s _).isUnit.map _).map _).ne_zero
  · rw [IsUnit.unit_spec]
    have e1 : (trV D.P.L gm.b.left (ν.J (redE C ≫ gm.b.left)) (J gm₀.b.left) (k : ℤ)).fst =
        trV D.P.L (redE C ≫ gm.b.left) (ν.J (redE C ≫ gm.b.left)) (J gm₀.b.left) (k : ℤ) := by
      unfold trV
      exact (norm_natCast_le_one_kummer_theta_logarithms (TrivSqZeroExt.fstHom C C C).toRingHom _ _ _ hc0).symm
    have e2 : toF R C (TanExp.rigValD D (J gm₀.b.left)) = valR (TF (R := R) C).hom
        (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => J gm₀.b.left)) (D.rig.s fun _ => J gm₀.b.left).val := by
      unfold TanExp.rigValD
      rw [gl_TF R C]
      have h5 := norm_natCast_le_one_kummer_theta_logarithms (toF R C) (𝟙 _) _ (D.rig.s fun _ => J gm₀.b.left).val hcR
      rw [Category.comp_id] at h5
      exact h5.symm
    have hQ1 : ⊤ ≤ ((TF (R := R) C).hom ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U (J gm₀.b.left) := by
      rw [← hQ, hb, ← Category.assoc]; exact pre_lemma _ _ _ (hJ _)
    have e3 := GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig_gen (TF (R := R) C).hom
      (fun _ => ν.J ((TF (R := R) C).hom ≫ eSec D.P.A)) (fun _ => J gm₀.b.left)
      (top_le_wchart _ _ _ _ (fun _ => ν.good _)) (top_le_wchart _ _ _ _ (fun _ => hQ1))
    rw [e1, e2, hQ]
    simp only [NumOf.rg, vF]
    unfold valF
    unfold valR at e3 ⊢
    rw [e3]
    simp only [Finset.univ_unique, Finset.prod_singleton, mul_pow]
    rw [trV_pow D.P.L _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (ν.good _) hQ1), _root_.one_mul]
  · intro s n c f hlin α
    have hyP : ∀ {Z : Scheme.{0}} (g : D.P.A.left ⟶ Z),
        (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) gm.b).left ≫
          (D.prB C).left ≫ g = gm.b.left ≫ g :=
      fun g => by rw [← Category.assoc, gl_prB']
    have hsec := GlobalTheory.T.sectionValue_linear_relation_linComb D.P.L (D.famφ C (ν.eX α)) (DegPre.famε k) (s.s (ν.eX α)) (D.famφB (ν.eX α))
      (DegPre.famε k) (fun i => f i (ν.eX α)) (D.prB C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))
      (hlin _)
      (fun i => ν.J (redE C ≫ (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C)
        gm.b).left ≫ D.famφ C (ν.eX α) i))
      (fun i => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
      (by
        intro k₁ k₂ e
        rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;> simp only [Sum.elim_inl, Sum.elim_inr] at e ⊢
        · rw [e]
        · rw [← hyP, ← e]
        · rw [← hyP, e]
        · rw [← hyP, ← hyP, e])
      (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) gm.b).left
      (top_le_wchart _ _ _ _ (fun i => hν _))
      (top_le_wchart _ _ _ _ (fun i => by rw [gl_prB']; exact hν _))
    have hS : ∀ i, valR gm.b.left (LB.wchart D.P.L (D.famφB (ν.eX α)) fun j => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j))
        ((f i (ν.eX α)).f fun j => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j)) =
        (∏ j, trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) j) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j))
          (J (gm₀.b.left ≫ D.famφB (ν.eX α) j)) (DegPre.famε k j)) *
        dualMap (toF R C) (valR gm₀.b.left (LB.wchart D.P.L (D.famφB (ν.eX α)) fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))
          ((f i (ν.eX α)).f fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))) := by
      intro i
      have hA : ⊤ ≤ gm₀.b.left ⁻¹ᵁ LB.wchart D.P.L (D.famφB (ν.eX α)) (fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j)) :=
        top_le_wchart _ _ _ _ (fun j => hJ _)
      rw [GlobalTheory.T.sectionValue_linComb_change_of_charts D.P.L (D.famφB (ν.eX α)) (DegPre.famε k) (f i (ν.eX α)) gm.b.left _
        (fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))
        (top_le_wchart _ _ _ _ (fun j => hν _)) (top_le_wchart _ _ _ _ (fun j => by rw [hb, Category.assoc]; exact hJb _))]
      congr 1
      rw [hb]
      exact norm_natCast_le_one_kummer_theta_logarithms _ _ _ _ hA
    have hφ : ∀ j, D.gtφT (TE R C) gm.b (ν.eX α) j = spMap (dualMap (toF R C)) ≫ D.gtφT (epsR R) gm₀.b (ν.eX α) j :=
      fun j => gl_gtφT_pull D (epsR R) (TE R C) (spMap (dualMap (toF R C))) (gl_hom R C) gm₀.b gm.b hb (ν.eX α) j
    have hpj : ∀ j, ⊤ ≤ D.gtφT (TE R C) gm.b (ν.eX α) j ⁻¹ᵁ D.P.L.U (pickJ (D.gtφT (TE R C) gm.b (ν.eX α))
        (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) j) := by
      intro j
      obtain ⟨i', he, hj⟩ := pickJ_spec (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) j
      rw [hj, ← he, hφ i']
      exact hJb _
    unfold jc sE vE
    rw [hsec]
    simp only [gl_scal, gl_prB', hS]
    rw [GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (D.gtφT (TE R C) gm.b (ν.eX α)) DegPre.gtε (gm.s (ν.eX α)) (gm.3 _) (𝟙 _) _
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (top_le_wchart _ _ _ _ (fun j => hν _)) (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hpj j))]
    rw [gl_corr D.P.L (D.gtφT (TE R C) gm.b (ν.eX α)) DegPre.gtε
      (fun j => spMap (dualMap (toF R C)) ≫ D.gtφT (epsR R) gm₀.b (ν.eX α) j) DegPre.gtε _ _ (hpull.2 _)
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (fun k₁ k₂ e => pickJ_congr _ _ e)
      (fun k₁ k₂ e => pickJ_congr _ _ (by rw [hφ, hφ]; exact e))
      (fun k₁ k₂ e => pickJ_congr _ _ (by rw [hφ k₂]; exact e))
      (𝟙 _)
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hpj j))
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp, ← hφ]; exact hpj j))]
    rw [gl_pullGen D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) DegPre.gtε (gm₀.s (ν.eX α)) (spMap (dualMap (toF R C)))
      _ (𝟙 _) (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp, ← hφ]; exact hpj j))]
    rw [Category.id_comp]
    rw [GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) DegPre.gtε (gm₀.s (ν.eX α)) (gm₀.3 _)
      (spMap (dualMap (toF R C))) _ (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j))
      (top_le_wchart _ _ _ _ (fun j => by rw [← hφ]; exact hpj j)) (top_le_wchart _ _ _ _ (fun j => hJb _))]
    have hn := norm_natCast_le_one_kummer_theta_logarithms (dualMap (toF R C)) (𝟙 _) (LB.wchart D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) (((gm₀.s (ν.eX α)).s fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)).val)
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hJ _))
    rw [Category.comp_id] at hn
    rw [hn, IsUnit.unit_spec]
    unfold TanExp.termV
    simp only [map_mul]
    refine alg_lemma_5 _ _ _ _ _ _ _ ?_
    rw [← Finset.prod_mul_distrib]
    simp only [Category.id_comp, ← hφ]
    rw [Finset.prod_congr rfl (fun j _ => GlobalTheory.T.transitionUnitPowValueAtPoint_cocycle D.P.L D.P.isLB _ _ _ _ _ (hν _) (hpj j) (by rw [hφ]; exact hJb _))]
    simp only [gl_gtφT_famφB]
    have tadd : ∀ (i : Fin 4) (a b : ℤ), trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) a * trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i)
        (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i)) (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) b =
        trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) (a + b) :=
      fun i a b => trV_add _ _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb, Category.assoc]; exact hJb _)) a b
    have tzero : ∀ (i : Fin 4), trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) 0 = 1 :=
      fun i => trV_zero _ _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb, Category.assoc]; exact hJb _))
    rw [Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_prod_four_rearrange, tadd, tadd, tadd, tadd]
    have h0 : D.famφB (ν.eX α) 0 = 𝟙 _ := by
      unfold DegPre.famφB
      rfl
    simp only [sub_add_cancel, add_neg_cancel, neg_add_cancel, tzero, _root_.mul_one, h0, Category.comp_id]

end GlobalTheory.MBLow.TanGauge

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstJetTermsGaugeUnitMulBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.firstJetTerms_gauge_unit_mul_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR R)) (gm : GtPt D (TE R C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF R C))) gm₀ gm → ∀ (k : ℕ) (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∃ T : (DualNumber C)ˣ, GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left) ≠ 0 ∧ (T : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left)) ^ k = ν.rg ^ k ∧ ∀ (s : Fam D C k) (n : ℕ) (c : Fin n → C) (f : Fin n → ∀ α : D.X, D.SecB k α), (∀ α, GeneratorPullback.SecLin D.P.L (DegPre.famφ D C α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))) → ∀ α, jc ν s gm α = (T : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (GlobalTheory.MBLow.TanExp.termV J gm₀ (f i (ν.eX α))) := by
  first | exact @GlobalTheory.MBLow.TanGauge.jc_eq_unit_mul | exact GlobalTheory.MBLow.TanGauge.jc_eq_unit_mul | (intros; apply GlobalTheory.MBLow.TanGauge.jc_eq_unit_mul <;> assumption)
end
