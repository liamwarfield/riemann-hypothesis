module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOf
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOf
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ThetaOfArc

open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam GlobalTheory.IndivisibleSection GlobalTheory.ThetaUnit IsLocalRing

section General

variable {X : Scheme.{0}} {L : LB X}

theorem sectionOfLineBundleOne_iff_germs_eq {σ : H0 L 1} {θ : L.Sec} : SectionOfLineBundleOne σ θ ↔ ∀ (y : X) (k : L.ι), y ∈ L.U k →
    gs (𝟙 X) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k)) (σ.f fun _ => k) = gs (𝟙 X) y (L.U k) (θ.f k) := by
  refine ⟨fun h y k hy => ?_, fun h j hj => ?_⟩
  · rw [h (fun _ => k) (fun z hz => Set.mem_iInter.1 hz 0)]
    exact gs_res (𝟙 X) y _ (mem_chart_one (𝟙 X) y hy) _
  · obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
    exact fn_ext fun y hy => (h y k (hj hy)).trans (gs_res (𝟙 X) y hj hy _).symm

theorem exists_h0Sec_left (θ : L.Sec) : ∃ σ : H0 L 1, SectionOfLineBundleOne σ θ := by
  obtain ⟨t, ht⟩ := exists_powerSection_of_chartFunctions θ
  exact ⟨t, sectionOfLineBundleOne_iff_germs_eq.2 fun y k hy => ht _ (𝟙 X) y k hy⟩

theorem exists_h0Sec_right (σ : H0 L 1) : ∃ θ : L.Sec, SectionOfLineBundleOne σ θ := by
  have le : ∀ k : L.ι, L.U k ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) :=
    fun k y hy => mem_chart_one (𝟙 X) y hy
  refine ⟨⟨fun k => resG X (le k) (σ.f fun _ => k), fun i j => fn_ext fun y hy => ?_⟩,
    sectionOfLineBundleOne_iff_germs_eq.2 fun y k hy => (gs_res (𝟙 X) y (le k) hy _).symm⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.1 _)).trans
    ((gs_compat σ (𝟙 X) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (Eq.symm ?_)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.2 _))))))
  refine (gm_linComb L _ _ (𝟙 X) y _ _ (le i hy.1) (le j hy.2)).trans ?_
  simp

def Same {L' : LB X} (σ : H0 L 1) (θ : L'.Sec) : Prop := ∃ θ' : L.Sec, SectionOfLineBundleOne σ θ' ∧ HEq θ θ'

variable {L' : LB X}

theorem exists_same_left (h : L = L') (θ : L'.Sec) : ∃ σ : H0 L 1, Same σ θ := by
  subst h
  obtain ⟨σ, hσ⟩ := exists_h0Sec_left θ
  exact ⟨σ, θ, hσ, HEq.rfl⟩

theorem exists_same_right (h : L = L') (σ : H0 L 1) : ∃ θ : L'.Sec, Same σ θ := by
  subst h
  obtain ⟨θ, hθ⟩ := exists_h0Sec_right σ
  exact ⟨θ, θ, hθ, HEq.rfl⟩

theorem Same.unique (h : L = L') {σ : H0 L 1} {θ₁ θ₂ : L'.Sec} (h₁ : Same σ θ₁) (h₂ : Same σ θ₂) : θ₁ = θ₂ := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨_, a₂, ⟨⟩⟩ := h₂
  have e : θ₁.f = θ₂.f := funext fun k => fn_ext fun y hy =>
    (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hy).symm.trans (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hy)
  cases θ₁
  cases θ₂
  cases e
  rfl

theorem Same.mul_iff (h : L = L') {R : Type} [CommRing R] (p : X ⟶ Sp R) (r : R) {σ σ' : H0 L 1} {θ θ' : L'.Sec}
    (h₁ : Same σ θ) (h₂ : Same σ' θ') : SecIsMul p r σ' σ ↔ ∀ i, θ'.f i = constFn p _ r * θ.f i := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨_, a₂, ⟨⟩⟩ := h₂
  refine ⟨fun hm k => fn_ext fun y hy => ?_, fun hm j => ?_⟩
  · refine (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hy).symm.trans
      ((secIsMul_gs hm (𝟙 X) y (fun _ => k) (mem_chart_one (𝟙 X) y hy)).trans (Eq.symm ?_))
    exact (gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_constFn p _ (𝟙 X) y hy r) (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hy).symm)
  · obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
    rw [ThickDiv.resTop_scal]
    refine fn_ext fun y hy => ?_
    have hk : y ∈ L.U k := Set.mem_iInter.1 hy 0
    refine (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hk).trans ((congrArg _ (hm k)).trans ((gs_mul (𝟙 X) y _ hk _ _).trans
      (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) ?_ (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hk))))))
    exact (gs_constFn p _ (𝟙 X) y hy r).trans (gs_constFn p _ (𝟙 X) y hk r).symm

theorem Same.mem_nonzeroLocus (h : L = L') {σ : H0 L 1} {θ : L'.Sec} (h₁ : Same σ θ) {y : X}
    (hy : y ∈ nonzeroLocus σ) : y ∈ nonzeroLocus θ := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨j, hj, hu⟩ := (SectionBaseChange.mem_nonzeroLocus σ _).1 hy
  obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  have hk : y ∈ L.U k := Set.mem_iInter.1 hj 0
  exact (SectionBaseChange.mem_nonzeroLocus θ _).2 ⟨k, hk, sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hk ▸ hu⟩

end General

theorem isPullTerm_mul {R A : Type} [CommRing R] [IsDomain R] [CommRing A] {D : DegPre R} {B₀ : Scheme.{0}}
    {M₀ : LB B₀} {φ : D.P.A.left ⟶ B₀} {w : LB.Iso D.P.L (M₀.pull φ)} {th th' : M₀.Sec} (q : B₀ ⟶ Sp A)
    (f : A →+* R) (hq : φ ≫ q = D.P.A.hom ≫ spMap f) (r : A) (hm : ∀ j, th'.f j = constFn q _ r * th.f j)
    {t t' : D.SecB 1 0} (h : IsPullTerm D φ w th t) (ht : SecIsMul D.P.A.hom (f r) t' t) :
    IsPullTerm D φ w th' t' := by
  refine isPullTerm_iff.2 fun y J j₀ hJ hy => ?_
  rw [hm, gs_mul φ y _ hy, gs_constFn q _ φ y hy, isPullTerm_iff.1 h y J j₀ hJ hy, sval_of_secIsMul ht _ y hJ, hq,
    cst_comp, Category.id_comp, mul_left_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X}

theorem thetaOf_iff (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L) : ThetaOf W th θ ↔
    ∃ (σ : H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x), (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 σ fam) ∧
      IsPullTerm W.P.D.toPre W.φ W.w th (fam 0) ∧ Same σ θ :=
  ⟨fun ⟨σ, fam, θ', h₁, h₂, h₃⟩ => ⟨σ, fam, h₁, h₂, θ', h₃⟩, fun ⟨σ, fam, h₁, h₂, θ', h₃⟩ => ⟨σ, fam, θ', h₁, h₂, h₃⟩⟩

theorem secIsMul_of_weight_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {P : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D P G)
    (σ σ' : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))))
    (f f' : ∀ α, SecBMod D.toPre 1 α) (hE : ∀ e, U.ExpandsAt e 1 σ f) (hE' : ∀ e, U.ExpandsAt e 1 σ' f')
    (hu : ∀ (σ₁ : H0 U.LG.L 1) (f₁ : ∀ α, D.toPre.SecB 1 α), f₁ 0 = f 0 → (∀ e, U.ExpandsAt e 1 σ₁ f₁) → σ₁ = σ)
    (r : R) (h : SecIsMul D.toPre.P.A.hom r (f' 0) (f 0)) : SecIsMul G.hom r σ' σ := by
  have h₀ : f' 0 = r • f 0 := (secIsMul_iff _ _ _ _).1 h
  have h₁ : (f' + (1 - r) • f) 0 = f 0 := by
    rw [Pi.add_apply, Pi.smul_apply, h₀, ← add_smul, add_sub_cancel, one_smul]
  have h₂ : σ' + (1 - r) • σ = σ :=
    hu _ _ h₁ fun e => expandsAt_add U (hE' e) (expandsAt_smul U (1 - r) (hE e))
  refine (secIsMul_iff _ _ _ _).2 ?_
  rw [sub_smul, one_smul] at h₂
  rw [← sub_eq_zero, ← add_left_inj σ, zero_add]
  refine Eq.trans ?_ h₂
  abel

end GlobalTheory.ThetaOfArc

namespace GlobalTheory

open GlobalTheory.ThetaUnit GlobalTheory.ThetaOfArc IsLocalRing

theorem existsUnique_thetaOf : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec), ThNZ th → (∃! θ : LB.Sec W.t.PP.L, ThetaOf W th θ) ∧ ∀ θ, ThetaOf W th θ → (∀ s : LB.Sec W.t.PP.L, ∃! r : PowerSeries A, ∀ i, s.f i = constFn W.t.G.hom _ r * θ.f i) ∧ (∃ g : W.t.G.left, W.t.G.hom g = IsLocalRing.closedPoint (PowerSeries A) ∧ g ∈ Out.nonzeroLocus θ) ∧ ∀ (r : A) (th' : a.D₀.P.L.Sec) (θ' : LB.Sec W.t.PP.L), ThMul r th th' → (ThetaOf W th' θ' ↔ ∀ i, θ'.f i = constFn W.t.G.hom _ (PowerSeries.C (R := A) r) * θ.f i) := by
  intro hL _ E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W th hth
  have hI : Ideal.span {(PowerSeries.X : PowerSeries A)} ≤ maximalIdeal (PowerSeries A) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have hb : W.P.U.LG.L = W.t.PP.L := congrArg (fun q => q.L) W.P.bundle
  obtain ⟨⟨t, ht, htu⟩, hnz⟩ := existsUnique_pullTerm W th
  have ht₀ := hnz t ht hth (closedPoint _)
  obtain ⟨σ, fam, rfl, hE, hmem, huq, hgen, -⟩ := exists_theta_arc hL.globalFns hL.secBaseChange hI W t ht₀
  have key : ∀ θ, ThetaOf W th θ ↔ Same σ θ := fun θ => by
    rw [thetaOf_iff]
    refine ⟨fun ⟨σ₁, f₁, h₁, h₂, h₃⟩ => huq σ₁ f₁ (htu _ h₂) h₁ ▸ h₃, fun h => ⟨σ, fam, hE, ht, h⟩⟩
  refine ⟨?_, fun θ hθ => ⟨fun s => ?_, ?_, fun r th' θ' hm => ?_⟩⟩
  · obtain ⟨θ, hθ⟩ := exists_same_right hb σ
    exact ⟨θ, (key θ).2 hθ, fun θ' h => ((key θ').1 h).unique hb hθ⟩
  · obtain ⟨s', hs'⟩ := exists_same_left hb s
    simpa only [((key θ).1 hθ).mul_iff hb W.t.G.hom _ hs'] using hgen s'
  · obtain ⟨g, hg, hn⟩ := exists_mem_nonzeroLocus hI W.P.U.toUnifPre (hE 0) ht₀ hmem
    exact ⟨g, hg, ((key θ).1 hθ).mem_nonzeroLocus hb hn⟩
  · choose fam' hfam' using fun α =>
      IntegralExpansion.exists_secIsMul W.P.D.toPre.P.A.hom (PowerSeries.C (R := A) r) (fam α)
    have hp : IsPullTerm W.P.D.toPre W.φ W.w th' (fam' 0) :=
      isPullTerm_mul a.D₀.P.A.hom _ W.spec.1.1.w r hm ht (hfam' 0)
    rw [thetaOf_iff]
    refine ⟨fun ⟨σ₁, f₁, h₁, h₂, h₃⟩ => (((key θ).1 hθ).mul_iff hb W.t.G.hom _ h₃).1 ?_, fun h => ?_⟩
    · exact secIsMul_of_weight_zero W.P.U.toUnifPre σ σ₁ fam f₁ hE h₁ huq _
        (h₂.unique a.D₀.P.isLB hp ▸ hfam' 0)
    · obtain ⟨σ', hσ'⟩ := exists_same_left hb θ'
      exact ⟨σ', fam', fun n => expandsAt_secIsMul _ _ _ _ _ _ n 1 _ σ σ' fam fam'
        ((((key θ).1 hθ).mul_iff hb W.t.G.hom _ hσ').2 h) hfam' (hE n), hp, hσ'⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOfStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_thetaOf_alt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec), ThNZ th → (∃! θ : LB.Sec W.t.PP.L, ThetaOf W th θ) ∧ ∀ θ, ThetaOf W th θ → (∀ s : LB.Sec W.t.PP.L, ∃! r : PowerSeries A, ∀ i, s.f i = constFn W.t.G.hom _ r * θ.f i) ∧ (∃ g : W.t.G.left, W.t.G.hom g = IsLocalRing.closedPoint (PowerSeries A) ∧ g ∈ Out.nonzeroLocus θ) ∧ ∀ (r : A) (th' : a.D₀.P.L.Sec) (θ' : LB.Sec W.t.PP.L), ThMul r th th' → (ThetaOf W th' θ' ↔ ∀ i, θ'.f i = constFn W.t.G.hom _ (PowerSeries.C (R := A) r) * θ.f i) := by
  first | exact @GlobalTheory.existsUnique_thetaOf | exact GlobalTheory.existsUnique_thetaOf | (intros; apply GlobalTheory.existsUnique_thetaOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentReductionEqOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentReductionEqOrigin
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanRed
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

theorem comp_gtφT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Sp R)} (ρ : T' ⟶ T)
    (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A) (hb : ρ ≫ b = b') (χ : D.X) (k : Fin 4) :
    ρ.left ≫ DegPre.gtφT D T b χ k = DegPre.gtφT D T' b' χ k := by
  subst hb
  fin_cases k
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul ρ (cP D T χ) b).trans
      (congrArg (· * (ρ ≫ b)) (comp_cP D ρ χ)))
  · exact congrArg (fun q => q.left) (comp_cP D ρ χ)
  · rfl
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one ρ)

theorem val_eq_of_genRelR {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    {B B₀ Y Y' : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen)
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt' : K → (Sp A' ⟶ B)}
    {ψ : K → (Y ⟶ B₀)} {ψ' : K → (Y' ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)}
    {u : LB.Gen (LB.LinComb M₀ ψ ε)} {u' : LB.Gen (LB.LinComb M₀ ψ' ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (hu : u.IsGen) (hu' : u'.IsGen) {h : Sp A ⟶ Y} {h' : Sp A' ⟶ Y'} (H : GenRelR w t (LB.pullGen _ _ _ u h))
    (H' : GenRelR w t' (LB.pullGen _ _ _ u' h')) (q : Sp A ⟶ Sp A') (hq : ∀ k, q ≫ pt' k = pt k)
    {Z : Scheme.{0}} (r : Z ⟶ Sp A) (z : Z)
    (hv : ∀ J, Good M₀ z J → val u' ((r ≫ q) ≫ h') z J = val u (r ≫ h) z J) {J'} (hJ' : Good M z J') :
    val t' (r ≫ q) z J' = val t r z J' := by
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists M₀ hM₀ z
  have hw' := (isGen_iff w).1 hw
  have e := CubTransport.val_pmaps (fun k => (H.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht (pullGen_isGen _ _ _ _ hu h) H) r hJ hJ'
  have e' := CubTransport.val_pmaps (fun k => (H'.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht' (pullGen_isGen _ _ _ _ hu' h') H') (r ≫ q) hJ hJ'
  rw [val_pull hJ, Category.comp_id] at e e'
  rw [hv J hJ, e] at e'
  simp only [Category.assoc r q, hq] at e'
  exact (mul_left_cancel e').symm

theorem corr_pull_of_valR {A F : Type} [CommRing A] [IsLocalRing A] [Field F] (p : A →+* F) [IsLocalHom p]
    {B : Scheme.{0}} {M : LB B} (hM : M.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp A ⟶ B)} (t : LB.Gen (LB.LinComb M pt ε)) (t' : LB.Gen (LB.LinComb M pt' ε))
    (hp : ∀ k, spMap p ≫ pt' k = pt k)
    (hv : ∀ j, ⊤ ≤ LB.wchart M pt' j → p (valR (𝟙 (Sp A)) (LB.wchart M pt' j) (t'.s j).val) =
      valR (𝟙 (Sp F)) (LB.wchart M pt j) (t.s j).val) :
    LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ t' (spMap p)) t := by
  refine corr_of_val hM fun y J hJ => ?_
  obtain rfl : y = cpt F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hc : spMap p (cpt F) = cpt A := IsLocalRing.comap_closedPoint p
  rw [val_pull hJ, Category.id_comp, val_of t' _ _ J (fun k => J (pt k)) (fun k => by rw [hp]),
    val_of t _ _ J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  have m : ⊤ ≤ (𝟙 (Sp F)) ⁻¹ᵁ LB.wchart M pt (fun k => J (pt k)) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => hJ (pt k))
  have m' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart M pt' (fun k => J (pt k)) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => by
      have := hJ (pt k)
      rw [← hc]
      exact (congrArg (fun q => q (cpt F) ∈ M.U (J (pt k))) (hp k)).mpr this)
  have m'' := FormalValue.top_le_comp m' (spMap p)
  have e := FormalValue.valR_spMap p _ _ m' (t'.s (fun k => J (pt k))).val
  rw [Category.comp_id] at m'' e
  refine Units.ext ?_
  exact (toStkA_valR _ _ _ m'' _).symm.trans ((congrArg _ (e.trans (hv _ m'))).trans (toStkA_valR _ _ _ m _))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (Ξ : ConstPts W Λ) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v.left = (Ξ.x 0).left := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ g h z₀ ν Ξ v g₁ hd ht hf
  haveI := isLocalRing_dual ℂ
  haveI := isLocalRing_dual ℂ⟦X⟧
  let p : DualNumber ℂ⟦X⟧ →+* ℂ⟦X⟧ := (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom
  let p₀ : DualNumber ℂ →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
  haveI : IsLocalHom p₀ := ⟨fun x hx => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hx⟩
  obtain ⟨h₁, h₂, -⟩ := hd
  have h₁' := h₁.1
  simp only [map_zero] at h₁' h₂
  have sq : spMap p ≫ spMap constEps = spMap (PowerSeries.C (R := ℂ)) ≫ spMap p₀ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun x => fst_dualMapR _ x)
  let ρ₀ : TF (R := ℂ) ℂ ⟶ epsR ℂ := Over.homMk (spMap p₀) (by
    show spMap p₀ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap (FractionRing ℂ) ℂ) ≫ spMap (algebraMap ℂ (FractionRing ℂ))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
    rfl)
  let ρ : selfR ⟶ epsR ℂ⟦X⟧ := Over.homMk (spMap p) (by
    show spMap p ≫ spMap (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl)
  have hb₀ : ρ₀ ≫ ν.b = (Λ.ex0 0).b := Over.OverMorphism.ext h₁'
  have hb : ρ ≫ g₁.b = (Ξ.g 0).b := Over.OverMorphism.ext (W.spec.1.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (spMap p ≫ ·) ((ht 0).1 2)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ν.b.left) sq).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) h₁').trans ((Ξ.g_rel 0 0).1 2).symm))))))
    ((Over.w _).trans (Over.w _).symm))
  have hc : ∀ x, LB.Gen.Corr a.D₀.P.L _ _ _ _ (LB.pullGen a.D₀.P.L _ _ (ν.s x) (spMap p₀)) ((Λ.ex0 0).s x) :=
    fun x => corr_pull_of_valR p₀ a.D₀.P.isLB _ _ (comp_gtφT a.D₀ ρ₀ ν.b _ hb₀ x) fun j hj =>
      (congrArg p₀ (h₂ x j hj)).trans ((TrivSqZeroExt.fst_add _ _).trans (add_zero _))
  have hv : ∀ y (Z : Scheme.{0}) (r : Z ⟶ Sp ℂ⟦X⟧) (z : Z) J', Good W.P.D.toPre.P.L z J' →
      val (g₁.s y) (r ≫ spMap p) z J' = val ((Ξ.g 0).s y) r z J' := fun y Z r z J' hJ' => by
    obtain ⟨x, rfl⟩ := W.e.surjective y
    refine val_eq_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB ((Ξ.g 0).isGen _) (g₁.isGen _)
      ((Λ.ex0 0).isGen x) (ν.isGen x) (Ξ.g_rel 0 x) (ht x) (spMap p) (comp_gtφT W.P.D.toPre ρ g₁.b _ hb _) r z
      (fun J hJ => ?_) hJ'
    have e : (r ≫ spMap p) ≫ spMap constEps = (r ≫ spMap (PowerSeries.C (R := ℂ))) ≫ spMap p₀ := by
      rw [Category.assoc, sq, Category.assoc]
    exact (congrArg (fun q => val (ν.s x) q z J) e).trans ((val_pull hJ _ _ _).symm.trans (val_corr hJ (hc x) _))
  let I : Ideal ℂ⟦X⟧ := (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)
  haveI : IsAdicComplete I ℂ⟦X⟧ := by
    simp only [I]
    rw [Algebra.algebraMap_self, Ideal.map_id]
    infer_instance
  refine hom_ext_of_isHausdorff I fun e => ?_
  obtain ⟨xe, hxe⟩ := FormalValue.exists_lift_thick (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}) W.t.G
    (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (ρ ≫ v).left (Over.w (ρ ≫ v)) e
  have hs : spMap ((Ideal.Quotient.mk (I ^ (e + 1))).comp p) = adicLevelι I (e + 1) ≫ spMap p := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hk : idealEps ^ (e + 1) ≤ RingHom.ker ((Ideal.Quotient.mk (I ^ (e + 1))).comp p) := fun s hs => by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    simp only [I]
    rw [Algebra.algebraMap_self, Ideal.map_id, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (mem_idealEps_pow hs).1
  have H₁ := hf.hasCoords _ hk (xe := xe) (hxe.trans (by rw [hs, Category.assoc]; rfl))
  rw [hs] at H₁
  obtain ⟨k₁, k₂⟩ := (FormalPoint.hasCoords_iff W.P.U.toUnifPre e g₁ _ xe).1 H₁.2
  have H₂ : FormalPoint.HasCoords W.P.U.toUnifPre e (Ξ.g 0) (adicLevelι I (e + 1)) xe :=
    (FormalPoint.hasCoords_iff W.P.U.toUnifPre e _ _ xe).2
      ⟨k₁.trans ((Category.assoc _ _ _).trans (congrArg (fun q => adicLevelι I (e + 1) ≫ q.left) hb)),
        fun y z J hJ => (k₂ y z J hJ).trans (hv y _ _ z J hJ)⟩
  exact hxe.symm.trans ((Ξ.x_pt 0).comp_fstG_eq H₂)

end GlobalTheory.ConstTanRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentReductionEqOriginStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantTangent_reduction_eq_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (Ξ : ConstPts W Λ) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v.left = (Ξ.x 0).left := by
  first | exact @GlobalTheory.ConstTanRed.main | exact GlobalTheory.ConstTanRed.main | (intros; apply GlobalTheory.ConstTanRed.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentEqFormalPointTransported
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentEqFormalPointTransported
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.ConstTanFormal

theorem corr_of_genRelR {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    {B B₀ Y₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen)
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt' : K → (Sp A' ⟶ B)}
    {pt₀ : K → (Y₀ ⟶ B₀)} {g : LB.Gen (LB.LinComb M pt ε)} {t : LB.Gen (LB.LinComb M pt' ε)}
    {ν : LB.Gen (LB.LinComb M₀ pt₀ ε)} (hg : g.IsGen) (ht : t.IsGen) (hν : ν.IsGen) {r : Sp A' ⟶ Sp A}
    {κ : Sp A ⟶ Y₀} {κ' : Sp A' ⟶ Y₀} (hκ : r ≫ κ = κ') (hp : ∀ k, pt' k = r ≫ pt k)
    (h : GenRelR w g (LB.pullGen _ _ _ ν κ)) (h' : GenRelR w t (LB.pullGen _ _ _ ν κ')) :
    LB.Gen.Corr M _ _ _ _ t (LB.pullGen M _ _ g r) := by
  have hw' := (isGen_iff w).1 hw
  have H := ConstGrp.pmaps_of_genRelR hw' hM hM₀ hg (DVR.pullGen_isGen _ _ _ _ hν κ) h
  have H' := ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht (DVR.pullGen_isGen _ _ _ _ hν κ') h'
  refine corr_of_val hM fun y J' hJ' => ?_
  choose J hJ using fun ψ : Sp A' ⟶ B₀ => exists_chart hM₀ (ψ y)
  have v := CubTransport.val_pmaps (fun k => (h.1 k).trans (Category.id_comp _).symm) H r hJ hJ'
  have v' := CubTransport.val_pmaps (fun k => (h'.1 k).trans (Category.id_comp _).symm) H' (𝟙 _) hJ hJ'
  rw [val_pull hJ, Category.comp_id, hκ] at v
  rw [val_pull hJ, Category.comp_id, Category.id_comp] at v'
  rw [val_pull hJ', Category.id_comp]
  simp only [Category.id_comp, hp] at v'
  exact mul_left_cancel (v'.symm.trans v)

theorem dualMapR_surjective {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} (h : Function.Surjective φ) :
    Function.Surjective (dualMapR φ) := fun a => by
  obtain ⟨x, hx⟩ := h a.fst
  obtain ⟨y, hy⟩ := h a.snd
  exact ⟨TrivSqZeroExt.inl x + TrivSqZeroExt.inr y, by ext <;> simp [hx, hy]⟩

theorem ker_dualMapR_mk {R : Type} [CommRing R] (I : Ideal R) :
    RingHom.ker (dualMapR (Ideal.Quotient.mk I)) ≤ I.map (algebraMap R (DualNumber R)) := fun a ha => by
  have h₁ : a.fst ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (by
    simpa using congrArg TrivSqZeroExt.fst (RingHom.mem_ker.1 ha))
  have h₂ : a.snd ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (by
    simpa using congrArg TrivSqZeroExt.snd (RingHom.mem_ker.1 ha))
  have e : a = algebraMap R (DualNumber R) a.fst + algebraMap R (DualNumber R) a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ h₁) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h₂))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ) (ex₀ : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W ex₀ z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W g ex₀ z₀ ν v g₁ hD hT
  refine FormalValue.isFormalPt_of_surjective _ fun e => ?_
  let I : Ideal ℂ⟦X⟧ := Ideal.span {PowerSeries.X}
  have hI : I ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PowerSeries.X_prime.not_isUnit
  have : IsLocalRing (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := isLocalRing_quotient_pow hI e
  have := isLocalRing_dual (ℂ⟦X⟧ ⧸ I ^ (e + 1))
  have := isLocalRing_dual ℂ⟦X⟧
  let ρ : DualNumber ℂ⟦X⟧ →+* DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := dualMapR (Ideal.Quotient.mk _)
  let s : Sp (DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1))) ⟶ Sp (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := spMap (algebraMap _ _)
  have hs : s ≫ Out.thick ℂ⟦X⟧ I e = spMap ρ ≫ (epsR ℂ⟦X⟧).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => (dualMapR_inl (Ideal.Quotient.mk (I ^ (e + 1))) r).symm)
  let xe : Sp (DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1))) ⟶ (Out.thickObj ℂ⟦X⟧ I e W.t.G).left :=
    pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs])
  have hx : xe ≫ (Out.fstG I e W.t.G).left = spMap ρ ≫ v.left := pullback.lift_fst _ _ _
  have hx' : xe ≫ ((Over.map (Out.thick ℂ⟦X⟧ I e)).obj (Out.thickObj ℂ⟦X⟧ I e W.t.G)).hom =
      spMap ρ ≫ (epsR ℂ⟦X⟧).hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_snd _ _ _)).trans hs)
  have hκ : spMap ρ ≫ spMap constEps = spMap (ρ.comp constEps) := (Spec.map_comp _ _).symm
  have h' := hD.2.2 e ρ (ρ.comp constEps) xe (dualMapR_inl _) (dualMapR_eps _)
    (fun r => (congrArg ρ (dualMapR_inl _ r)).trans (dualMapR_inl _ _))
    ((congrArg ρ (dualMapR_eps _)).trans (dualMapR_eps _)) hx
  have hp : ∀ x k, xe ≫ W.P.D.toPre.Oφ (W.P.U.gt e).pG (W.e x) k =
      spMap ρ ≫ Out.DegPre.gtφT W.P.D.toPre (epsR ℂ⟦X⟧) g₁.b (W.e x) k := fun x k => by
    refine W.spec.1.1.hom_ext ?_ ?_
    · refine ((h' x).1 k).trans ?_
      exact (congrArg (· ≫ _) hκ.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap ρ ≫ ·) ((hT x).1 k).symm).trans (Category.assoc _ _ _).symm))
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ (hx'.trans ?_)
      · refine congrArg (xe ≫ ·) ?_
        fin_cases k <;> exact Over.w _
      · refine congrArg (spMap ρ ≫ ·) ?_
        fin_cases k <;> exact (Over.w _).symm
  refine ⟨_, inferInstance, ρ, xe, dualMapR_surjective Ideal.Quotient.mk_surjective, ?_, hx, hp 0 2, fun y => ?_⟩
  · rw [idealEps, ← Ideal.map_pow]
    exact ker_dualMapR_mk _
  · obtain ⟨x, rfl⟩ := W.e.surjective y
    exact corr_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB (g₁.isGen _)
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt e).t_gen _) xe) (ν.isGen x) hκ (hp x) (hT x) (h' x)

end GlobalTheory.ConstTanFormal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentEqFormalPointTransportedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantTangent_eq_formalPoint_transported : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ) (ex₀ : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W ex₀ z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left := by
  first | exact @GlobalTheory.ConstTanFormal.main | exact GlobalTheory.ConstTanFormal.main | (intros; apply GlobalTheory.ConstTanFormal.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSectionValuesFormalThetaSum
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSectionValuesFormalThetaSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ConstThetaSections

open ConstFam FormalValue

theorem exists_vals_fsum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) [NeZero j] (α : Λ.A.X), ∀ th ∈ Λ.A.Theta j α, ∃ (m : ℕ) (σ : Out.H0 W.P.U.LG.L j), Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α th v) := by
  intro hL hL₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j _ α th hth
  have hj : 1 ≤ j := NeZero.one_le
  obtain ⟨s₀, hs₀, -⟩ := ((ArcThetaSpaces.sections_theta hL hL₂ E H D l c O β b a Λ).1 j α hj).2 th hth
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e := ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1,
    W.spec.2.2.2.2.1, fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨m, hm⟩ := exists_expandsAt hW hL.globalFns hj W.P.U (Λ.ε α) s₀
  obtain ⟨f, σ, hf, hE⟩ := hm m le_rfl
  have ex : ∀ mu, expo a j (Λ.ε α) (Λ.ε mu) = Λ.A.exponent j α mu := fun mu => by
    rw [expo, AnArc.exponent, AnArc.q, Λ.be_eq, Λ.be_eq]
  have hpos : ∀ mu, 0 ≤ (m : ℤ) + Λ.A.exponent j α mu := fun mu => ex mu ▸ (hf.1 (Λ.ε mu)).1
  have comp : ∀ mu, ∃ t : SecBMod a.D₀ j (Λ.ε (α + j • mu)), f (W.e (Λ.ε (α + j • mu))) =
      (PowerSeries.X : ℂ⟦X⟧) ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat • pullB hW j _ t ∧
      ∀ z, Λ.fn j (α + j • mu) t z = Λ.A.psi mu ^ j * eTwoPi (Λ.A.T mu α) * th (z + Λ.A.ct mu) := fun mu => by
    have cast : ∀ x, Λ.ε α + j • Λ.ε mu = x → ∃ t : SecBMod a.D₀ j x, f (W.e x) =
        (PowerSeries.X : ℂ⟦X⟧) ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat • pullB hW j _ t ∧
        ∀ z, FrameValue.secVal Λ.u a.D₀.P.isLB t (Λ.u.ex z).left
          ![z, z + (Λ.A.ct α + j • Λ.A.ct mu), Λ.A.ct α + j • Λ.A.ct mu, 0] =
            Λ.A.psi mu ^ j * eTwoPi (Λ.A.T mu α) * th (z + Λ.A.ct mu) := by
      rintro _ rfl
      refine ⟨_, ex mu ▸ (hf.1 (Λ.ε mu)).2, fun z => ?_⟩
      have es := Λ.psi (mu + α)
      rw [map_add Λ.ε, map_add Λ.A.ct] at es
      refine (secVal_feTranslate Λ.ah Λ.rig j (Λ.ct α) (Λ.ct mu) (Λ.psi α) (Λ.psi mu) es s₀ z).trans ?_
      refine (congrArg (· * _) (congrFun hs₀ (z + Λ.A.ct mu))).trans ?_
      have := (Λ.A.psi mu).ne_zero
      have := (Λ.A.psi α).ne_zero
      push_cast
      rw [Λ.A.psi_add]
      field_simp
    obtain ⟨t, h₁, h₂⟩ := cast (Λ.ε (α + j • mu)) (by rw [map_add (f := _), map_nsmul])
    refine ⟨t, h₁, fun z => Eq.trans ?_ (h₂ z)⟩
    exact congrArg (fun q => FrameValue.secVal Λ.u a.D₀.P.isLB t (Λ.u.ex z).left ![z, z + q, q, 0])
      ((map_add Λ.A.ct _ _).trans (congrArg _ (map_nsmul Λ.A.ct _ _)))
  refine ⟨m, σ, fun v jL hjL => ?_⟩
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB (basePt (Ξ.g v) (cpt ℂ⟦X⟧))
  obtain ⟨j₀, h₀⟩ := exists_chart a.D₀.P.isLB (W.φ (basePt (Ξ.g v) (cpt ℂ⟦X⟧)))
  have hM' := (top_le_iff_cpt _ _).2 hM
  have hw : ⊤ ≤ (Ξ.g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) :=
    (top_le_iff_cpt (A := ℂ⟦X⟧) _ _).2 ⟨mem_pull.2 h₀, hM⟩
  choose jf jt hc using exists_cohCharts (Ξ.g v) jM hM'
  obtain ⟨w, hw'⟩ := isUnit_valR (A := ℂ⟦X⟧) _ _ hw (W.w.s (fun _ => j₀, jM))
  have hτ := Ξ.τ_eq v jL jM j₀ hjL hw
  have hI : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} :=
    Ideal.map_id _
  have hx := Ξ.x_fm v
  rw [hI, ← hw'] at hτ
  rw [hI] at hx
  let i : Λ.A.X → W.P.D.toPre.X := fun mu => W.e (Λ.ε (α + j • mu))
  have hi : Function.Injective i := fun mu mu' h =>
    smul_right_injective Λ.A.X (Int.natCast_ne_zero.2 (NeZero.ne j)) ((natCast_zsmul mu j).trans
      ((add_left_cancel (Λ.ε.injective (W.e.injective h))).trans (natCast_zsmul mu' j).symm))
  let h : W.P.D.toPre.X → ℂ⟦X⟧ := fun x => w.val ^ j * (famVal (Ξ.g v) (f x) (jf x) * coordVal (Ξ.g v) x (jt x))
  have h₁ : ∀ mu, h (i mu) = PowerSeries.X ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat *
      PowerSeries.C (Λ.A.term j α th mu v * Λ.u.fr j₀ v.2 ^ j) := fun mu => by
    obtain ⟨t, e₁, e₂⟩ := comp mu
    have := GlobalTheory.ConstTerm.main hL hL₂ E H D l Xo c O β Y b a χ W Λ Ξ j (α + j • mu) t (f (i mu)) _
      (fun Z _ _ p κ jf j₀ hp hi => by
        rw [show f (i mu) = _ from e₁]
        exact valR_smul_pullB hW j _ t _ Z p κ jf j₀ hp hi) v jM j₀ _ _ (hc (i mu)) hw
    rw [← hw', e₂] at this
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [AnArc.term]; ring
  have h₂ : ∀ x, (∀ mu, i mu ≠ x) → h x = 0 := fun x hx => by
    have e₁ : f x = 0 := hf.2 x fun y e => hx (Λ.ε.symm (W.e.symm y)) (by
      rw [← e]
      show W.e (Λ.ε _) = _
      rw [map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, Λ.ε.apply_symm_apply, W.e.apply_symm_apply])
    have e₂ : famVal (Ξ.g v) (f x) (jf x) = 0 := by
      rw [e₁]
      exact (dif_pos (hc x).1).trans ((congrArg _ (map_zero _)).trans (map_zero _))
    show _ * (_ * _) = _
    rw [e₂, zero_mul, mul_zero]
  beta_reduce
  rw [← algebraMap_mk_eq Λ.A j α th v hpos, ← map_pow, ← map_mul]
  refine congrArg _ ((Units.mul_right_inj (w ^ j)).1 (eq_of_forall_mk_eq (Ideal.span {PowerSeries.X}) fun e => ?_))
  have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)})) e
  obtain ⟨F, hF⟩ := map_secVal_eq W.P.U.toUnifPre (hE e)
  obtain ⟨F', hF', hd⟩ := exists_sum_sub_mem hi h₁ h₂ (L := fun k => Λ.A.level j α ((k : ℤ) - m)) (fun k mu => by
    have := hpos mu
    rw [Λ.A.mem_level]
    omega) (e + 1) F
  have H := (hF _ _ _ _ _ hx _ (Ideal.Quotient.mk (Ideal.span {PowerSeries.X} ^ (e + 1))) Ideal.mk_ker.ge).2
    F' jL jM jf jt hF' hjL hM' fun x _ => hc x
  rw [map_mul, H, ← map_mul, Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have e₁ : (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v * Λ.u.fr j₀ v.2 ^ j) =
      (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v) *
        PowerSeries.C (Λ.u.fr j₀ v.2) ^ j := by
    ext k
    rw [← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Finset.sum_mul]
  rw [e₁, show ∑ x ∈ F', h x = w.val ^ j * ∑ x ∈ F', famVal (Ξ.g v) (f x) (jf x) * coordVal (Ξ.g v) x (jt x) from
    (Finset.mul_sum _ _ _).symm] at hd
  refine (congrArg (_ ∣ ·) ?_).mp (hd.mul_left ((tau W.P.U.toUnifPre (Ideal.span {PowerSeries.X}) (Ξ.x v).left jL jM).val ^ j))
  rw [Units.val_pow_eq_pow_val]
  have := congrArg (· ^ j) hτ
  simp only [mul_pow] at this
  linear_combination (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v) * this

end GlobalTheory.ConstThetaSections
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSectionValuesFormalThetaSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_values_formalThetaSum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) [NeZero j] (α : Λ.A.X), ∀ th ∈ Λ.A.Theta j α, ∃ (m : ℕ) (σ : Out.H0 W.P.U.LG.L j), Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α th v) := by
  first | exact @GlobalTheory.ConstThetaSections.exists_vals_fsum | exact GlobalTheory.ConstThetaSections.exists_vals_fsum | (intros; apply GlobalTheory.ConstThetaSections.exists_vals_fsum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfMulEventually
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding gxFst gxSnd Unf GoodEmb relab perFr
open scoped LaurentSeries

namespace GlobalTheory.ArcQ.AnFrEx

theorem eq_zero_of_mul_eventually {g : ℕ} (θ φ : (Fin g → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : ∃ z, θ z ≠ 0)
    (hφ : ContinuousAt φ 0) (h : ∀ᶠ z in nhds 0, θ z * φ z = 0) : φ 0 = 0 := by
  by_contra h0
  obtain ⟨z₀, hz₀⟩ := hne
  have h1 : ∀ᶠ z in nhds (0 : Fin g → ℂ), θ z = 0 := by
    filter_upwards [h, hφ.eventually_ne h0] with z a b
    exact (mul_eq_zero.1 a).resolve_right b
  have hl : Differentiable ℂ (fun t : ℂ => t • z₀) := differentiable_id.smul_const z₀
  have ht : Filter.Tendsto (fun t : ℂ => t • z₀) (nhds 0) (nhds 0) := by
    have := hl.continuous.tendsto 0
    simpa using this
  have han : AnalyticOnNhd ℂ (fun t : ℂ => θ (t • z₀)) Set.univ := fun t _ => (hθ.comp hl).analyticAt t
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (ht.eventually h1) (Set.mem_univ 1)
  exact hz₀ (by simpa using this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem isOpen_ex {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) (V : Xo.univ.t.G.left.Opens) :
    IsOpen {z | ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ V} := by
  have h := ((F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun x => differentiableOn_const _⟩).2 V 0).1
  have h2 := h.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
  convert h2 using 1
  ext z
  simp

theorem gen_unique (hT : Out.SecTwistSt) {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P)
    (θ : (Fin g → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : ∃ z, θ z ≠ 0) (κ : ℂ) (hκ : κ ≠ 0)
    (fr fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
    (hf : IsThetaFrameAt Xo.univ.t.PP (F.u k P) (fun w => (F.ex k P w).left) θ fr)
    (hf' : IsThetaFrameAt Xo.univ.t.PP (F.u k P) (fun w => (F.ex k P w).left) θ fr')
    (s s' : LB.Sec (PPx (F.u k P))) (hs : GlobalTheory.Frames.SecGen (F.u k P) s)
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx (F.u k P)), pt ≫ gxFst (F.u k P) = (F.ex k P z).left →
      pt ≫ gxSnd (F.u k P) = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (F.u k P)).U (fun _ => j)) (s.f (fun _ => j)) = κ * θ z * fr j z)
    (hv' : ∀ j z (pt : Sp ℂ ⟶ Gx (F.u k P)), pt ≫ gxFst (F.u k P) = (F.ex k P z).left →
      pt ≫ gxSnd (F.u k P) = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (F.u k P)).U (fun _ => j)) (s'.f (fun _ => j)) = κ * θ z * fr' j z) :
    ∀ i, s'.f i = s.f i := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo (F.u k P) s
  obtain ⟨a, ha, -⟩ := hs s'
  have hw : ∀ z, (F.ex k P z).left ≫ Xo.univ.t.G.hom = 𝟙 (Sp ℂ) ≫ F.u k P := fun z =>
    (Over.w (F.ex k P z)).trans (Category.id_comp _).symm
  obtain ⟨j, hj⟩ := GlobalTheory.FrameUnif.ThetaPtEx.exists_chart_top Xo.univ.t.PP.isLB (F.ex k P 0).left
  have hn : {z | ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} ∈ nhds (0 : Fin g → ℂ) :=
    (isOpen_ex F k P hP _).mem_nhds hj
  have key : fr' j 0 - a * fr j 0 = 0 := by
    refine eq_zero_of_mul_eventually θ (fun z => fr' j z - a * fr j z) hθ hne
      (((hf'.1 j).differentiableAt hn).continuousAt.sub
        (continuousAt_const.mul ((hf.1 j).differentiableAt hn).continuousAt)) ?_
    filter_upwards [hn] with z hz
    let pt : Sp ℂ ⟶ Gx (F.u k P) :=
      pullback.lift (f := (Over.mk (F.u k P)).hom) (g := Xo.univ.t.G.hom) (𝟙 _) (F.ex k P z).left (hw z).symm
    have p1 : pt ≫ gxFst (F.u k P) = (F.ex k P z).left := pullback.lift_snd _ _ _
    have p2 : pt ≫ gxSnd (F.u k P) = 𝟙 (Sp ℂ) := pullback.lift_fst _ _ _
    have e' := (congrArg (valAt' pt ((PPx (F.u k P)).U (fun _ => j))) (ha (fun _ => j))).trans (h1 a _ pt p2)
    rw [hv j z pt p1 p2 hz, hv' j z pt p1 p2 hz] at e'
    refine mul_left_cancel₀ hκ ?_
    linear_combination e'
  have h00 : fr' j 0 = fr j 0 := (hf'.2.2.2.1 j hj).trans (hf.2.2.2.1 j hj).symm
  have ha1 : a = 1 := by
    refine mul_right_cancel₀ (hf.2.1 j 0 hj) ?_
    rw [h00] at key
    linear_combination -key
  refine h3 s' fun i pt hp => ?_
  have e' := (congrArg (valAt' pt ((PPx (F.u k P)).U i)) (ha i)).trans (h1 a _ pt hp)
  rw [e', ha1, one_mul]

theorem sum_single_of_support {J : Type} {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : J, Fin (m τ)) (τ : J)
    (v : Fin g → ℂ) (hv : ∀ jj, v jj ≠ 0 → (e jj).1 = τ) :
    ∑ k : Fin (m τ), v (e.symm ⟨τ, k⟩) • (Pi.single (e.symm ⟨τ, k⟩) 1 : Fin g → ℂ) = v := by
  funext jj
  rw [Finset.sum_apply]
  by_cases h : (e jj).1 = τ
  · obtain ⟨⟨τ', k⟩, rfl⟩ := e.symm.surjective jj
    obtain rfl : τ' = τ := by simpa using h
    rw [Finset.sum_eq_single k (fun b _ hb => ?_) (by simp)]
    · simp
    · have : e.symm ⟨τ', k⟩ ≠ e.symm ⟨τ', b⟩ := fun hh => hb (by simpa using (e.symm.injective hh).symm)
      simp [Pi.single_eq_of_ne this]
  · have h0 : v jj = 0 := by_contra fun h' => h (hv jj h')
    rw [h0]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : jj ≠ e.symm ⟨τ, b⟩ := fun hh => h (by rw [hh]; simp)
    simp [Pi.single_eq_of_ne this]

theorem isUnit_det_of_support {J : Type} {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : J, Fin (m τ)) (τ : J)
    (v : Fin (m τ) → Fin g → ℂ) (hl : LinearIndependent ℂ v) (hv : ∀ i jj, v i jj ≠ 0 → (e jj).1 = τ) :
    IsUnit (Matrix.of fun i k : Fin (m τ) => v i (e.symm ⟨τ, k⟩)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
  rw [Fintype.linearIndependent_iff] at hl ⊢
  intro cf hc
  refine hl cf (funext fun jj => ?_)
  by_cases h : (e jj).1 = τ
  · obtain ⟨⟨τ', k⟩, rfl⟩ := e.symm.surjective jj
    obtain rfl : τ' = τ := by simpa using h
    have := congrFun hc k
    simpa [Finset.sum_apply, Matrix.row] using this
  · rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have h0 : v b jj = 0 := by_contra fun h' => h (hv b jj h')
    simp [h0]

theorem existsUnique_anFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ w : ℂ, Ha.T < w.im → ∃! y, AnFr Ha Θ z w y := by
  intro _ L2 E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha th Θ z _ hz w hw
  have hT := L2.secTwist
  have hP := Ha.period w hw
  obtain ⟨hsym, hpos⟩ := Θ.pos w hw
  obtain ⟨hd, w₀, hw₀⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero Uw.g Θ.c₁ Θ.c₂ Θ.half₁ Θ.half₂).1 _ hsym hpos
  have hθd : Differentiable ℂ (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) :=
    hd.comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Θ.h)).differentiable
  have hθ : ∃ v, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v) ≠ 0 := by
    refine ⟨∑ k, w₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1)), ?_⟩
    have : Θ.h.mulVec (∑ k, w₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = w₀ := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, (Θ.per w _).1]
      exact (pi_eq_sum_univ' w₀).symm
    rwa [this]
  obtain ⟨-, hder, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Uw.F Ha.i _ hP
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨u, hu, htan, heig, hbas⟩ := GlobalTheory.T.exists_tangent_eigenbasis_exponential E H Dw l Xo c σ Uw.g Uw.e Uw.F Ha.i _ hP
    obtain ⟨fr, hfr⟩ := Θ.frame w hw
    obtain ⟨s, hs⟩ := hfr.2.2.2.2
    obtain ⟨t, ht, hval⟩ := GlobalTheory.FrameUnif.ThetaPtEx.exists_gen hT (Uw.F.u Ha.i (Ha.Pw w)) (Uw.F.ex Ha.i (Ha.Pw w))
      (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) fr Θ.κ Θ.κ_ne hθ hfr.2.1 s hs
    let y₀ : FrPt Xo c (CAt σ) := ⟨Uw.F.u Ha.i (Ha.Pw w), Uw.F.over_σ _ _ hP, u, htan, heig, hbas, t, ht⟩
    have hch := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c (CAt σ) y₀
    obtain ⟨⟨x', xo', u', tan', eig', basis', s', gen'⟩, ⟨hx, hc, -⟩, -⟩ :=
      hch (fun τ => (Matrix.of fun i k : Fin (Dw.mult τ) => z τ i (Uw.e.symm ⟨τ, k⟩) : Matrix _ _ ℂ)) 1
        (fun τ => isUnit_det_of_support Uw.e τ (z τ) (hz τ).1 (hz τ).2)
    dsimp only [y₀] at hx hc
    subst hx
    refine ⟨⟨Uw.F.u Ha.i (Ha.Pw w), xo', u', tan', eig', basis', t, ht⟩, ⟨rfl, fun τ i => ?_⟩, fr, hfr, hval⟩
    have := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ Uw.F Ha.i _ hP _ (u τ) _ (hu τ)
      (fun k => z τ i (Uw.e.symm ⟨τ, k⟩)) (u' τ i)).1 (hc τ i)
    rwa [sum_single_of_support Uw.e τ (z τ i) ((hz τ).2 i)] at this
  · rintro ⟨x, xo, u, tan, eig, basis, s, gen⟩ ⟨x', xo', u', tan', eig', basis', s', gen'⟩
      ⟨⟨hx, hu⟩, fr, hfr, hs⟩ ⟨⟨hx', hu'⟩, fr', hfr', hs'⟩
    dsimp only at hx hu hs hx' hu' hs'
    subst hx hx'
    obtain rfl : u = u' := funext fun τ => funext fun i => (hder _).unique (hu τ i) (hu' τ i)
    have hss := gen_unique hT Uw.F Ha.i _ hP _ hθd hθ Θ.κ Θ.κ_ne fr fr' hfr hfr' s s' gen hs hs'
    obtain rfl : s = s' := by
      cases s; cases s'
      congr 1
      exact (funext hss).symm
    rfl

end GlobalTheory.ArcQ.AnFrEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionOfArcNonzeroOnFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionOfArcNonzeroOnFibres
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ThetaAllFibres

theorem exists_mem_of_flat {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    (U : X.Opens) {x : X} (hx : p x = IsLocalRing.closedPoint R) (hU : x ∈ U) (g : Sp R) :
    ∃ y : X, p y = g ∧ y ∈ U := by
  have hs : g ⤳ p x := hx ▸ IsLocalRing.specializes_closedPoint (R := R) g
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap p hs
  exact ⟨y, e, hy.mem_open U.isOpen hU⟩

theorem mem_nonzeroLocus_of_h0Sec {X : Scheme.{0}} {L : LB X} {σ : Out.H0 L 1} {θ : LB.Sec L} (h : SectionOfLineBundleOne σ θ) {x : X}
    (hx : x ∈ Out.nonzeroLocus σ) : x ∈ Out.nonzeroLocus θ := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have le : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun y hy => Set.mem_iInter.1 hy 0
  rw [h j le] at hj
  erw [Scheme.basicOpen_res] at hj
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j 0, hj.2⟩

theorem nonzeroLocus_eq_of_heq {S : Scheme.{0}} {G : Over S} [GrpObj G] {L L' : RigLB G} (e : L' = L)
    {θ : LB.Sec L.L} {θ' : LB.Sec L'.L} (h : HEq θ θ') : Out.nonzeroLocus θ = Out.nonzeroLocus θ' := by
  subst e
  rw [eq_of_heq h]

theorem X_notMem_or_eq_closedPoint {A : Type} [CommRing A] [IsLocalRing A] (hA : IsField A)
    (g : PrimeSpectrum (PowerSeries A)) :
    PowerSeries.X ∉ g.asIdeal ∨ g = IsLocalRing.closedPoint (PowerSeries A) := by
  refine or_iff_not_imp_left.2 fun h => ?_
  rw [not_not] at h
  refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal g.isPrime.ne_top) fun f hf => ?_)
  have h₀ : PowerSeries.constantCoeff f = 0 := by
    by_contra hne
    obtain ⟨b, hb⟩ := hA.mul_inv_cancel hne
    exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal f).1 hf))
      (PowerSeries.isUnit_iff_constantCoeff.2 (IsUnit.of_mul_eq_one b hb))
  obtain ⟨q, rfl⟩ := PowerSeries.X_dvd_iff.2 h₀
  exact g.asIdeal.mul_mem_right _ h

theorem theta_nonzero_on_fibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L), ThNZ th → ThetaOf W th θ → (IsField A ∨ PushInvertible Y.t.G Y.t.PP.L) → ∀ g : Sp (PowerSeries A), (IsField A → PowerSeries.X ∉ g.asIdeal ∨ g = IsLocalRing.closedPoint (PowerSeries A)) ∧ ∃ x : W.t.G.left, W.t.G.hom x = g ∧ x ∈ Out.nonzeroLocus θ := by
  intro hL _ E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W th θ hth hθ _ g
  refine ⟨fun hA => X_notMem_or_eq_closedPoint hA g, ?_⟩
  obtain ⟨σ, fam, θ', hE, hp, h0, he⟩ := hθ
  have hI : Ideal.span {(PowerSeries.X : PowerSeries A)} ≤ IsLocalRing.maximalIdeal (PowerSeries A) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have := W.t.semi.geomConnected
  have := W.P.U.smooth
  obtain ⟨σ₀, -, -, -, -, hu, -, hz⟩ := GlobalTheory.ThetaUnit.exists_theta hL.globalFns hL.secBaseChange hI W.P.U (fam 0)
    ((GlobalTheory.ThetaUnit.existsUnique_pullTerm W th).2 (fam 0) hp hth _)
  obtain rfl := hu σ fam rfl hE
  obtain ⟨x, hx, hn⟩ := (hz σ 1 ((GlobalTheory.ThetaUnit.secIsMul_iff _ _ _ _).2 (one_smul _ _).symm)).2.1 isUnit_one
  rw [nonzeroLocus_eq_of_heq W.P.bundle he]
  exact exists_mem_of_flat W.t.G.hom _ hx (mem_nonzeroLocus_of_h0Sec h0 hn) g

end GlobalTheory.ThetaAllFibres
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionOfArcNonzeroOnFibresStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSection_of_arc_nonzero_on_fibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L), ThNZ th → ThetaOf W th θ → (IsField A ∨ PushInvertible Y.t.G Y.t.PP.L) → ∀ g : Sp (PowerSeries A), (IsField A → PowerSeries.X ∉ g.asIdeal ∨ g = IsLocalRing.closedPoint (PowerSeries A)) ∧ ∃ x : W.t.G.left, W.t.G.hom x = g ∧ x ∈ Out.nonzeroLocus θ := by
  first | exact @GlobalTheory.ThetaAllFibres.theta_nonzero_on_fibres | exact GlobalTheory.ThetaAllFibres.theta_nonzero_on_fibres | (intros; apply GlobalTheory.ThetaAllFibres.theta_nonzero_on_fibres <;> assumption)
end
end
