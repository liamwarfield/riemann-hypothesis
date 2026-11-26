module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisTorusExtensionOfLiftsAndDuals
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentCharacterValuesAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentCharacterValuesAdditive
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.GtTanClass

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem exists_unit {T : Over (Sp R)} (g : GtPt D T) (hb : g.b = 1) (χ : D.X) :
    ∃ ρ : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ T.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val (g.s χ) q z J = Geo.Tor.gm q z ⊤ ρ := by
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T g.b χ) (ε' := DegPre.gtε)
    (fun U _ h => Eq.symm (by
      refine (prod_pt g.b χ h).trans ?_
      rw [hb, _root_.mul_one]; simp)) (LB.oneGen D.P.L (Y := T.left))
    (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio D.P.isLB rfl (g.s χ) u (g.isGen χ) hu
  exact ⟨ρ, fun Z q z J hJ => by rw [hρ Z q z J hJ, vu Z q z J hJ, val_one, _root_.mul_one]⟩

omit [IsDomain R] in
theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Sp B) (a : A) :
    gs (spMap f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = toStkA z (f a) := by
  rw [gs_eq _ _ ⊤ trivial]
  have e := congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact congrArg ((Sp B).presheaf.germ ⊤ z trivial).hom e.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (gm : GtPt D (epsR R)), GtTan gm → gm.b = DegPre.zeroT D (epsR R) → ∃ l : D.X →+ R, ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ _ D gm ⟨o, ho, hp⟩ hb
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using
      IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hb1 : gm.b = 1 := hb
  choose ρ hρ using exists_unit gm hb1
  choose u hu using fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).commRingCatIsoToRingEquiv.symm.surjective (ρ χ).val
  have hv : ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → (val (gm.s χ) q z J).val =
        gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (u χ)) := fun χ Z q z J hJ =>
    (congrArg Units.val (hρ χ Z q z J hJ)).trans ((gs_unit q z ⊤ trivial _).symm.trans
      (congrArg (gs q z ⊤) (hu χ).symm))
  have h1 : ∀ χ, TrivSqZeroExt.fst (u χ : DualNumber R) = 1 := fun χ => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt R)
    have e : val (gm.s χ) (redE R) (cpt R) J = 1 := by
      have e₁ := (val_corr hJ (hp.2 χ) (𝟙 (Sp R))).trans (val_pull hJ _ _ _)
      have e₂ := (val_corr hJ (ho.2 χ) (𝟙 (Sp R))).trans (val_one _)
      rw [← e₂, e₁]
      congr 1
    have e' := hv χ _ (redE R) (cpt R) J hJ
    rw [e] at e'
    refine toStkA_injective (A := R) ?_
    rw [map_one]
    exact (gs_spMap (TrivSqZeroExt.fstHom R R R).toRingHom (cpt R) (u χ)).symm.trans e'.symm
  have hm : ∀ χ χ', (u (χ + χ') : DualNumber R) = u χ * u χ' := fun χ χ' => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt (DualNumber R))
    have C : IsCub (th D (T := epsR R) (cpt (DualNumber R)) J) := isCub_cubV D.cub hJ
    have e := cv_add gm hJ χ χ'
    rw [hb1, C.face₃, _root_.mul_one] at e
    have k : ∀ χ, (cv gm χ (cpt (DualNumber R)) J).val = toStkA (cpt (DualNumber R)) (u χ) := fun χ =>
      (hv χ _ (𝟙 _) _ J hJ).trans (gs_eq _ _ ⊤ trivial _)
    refine toStkA_injective (A := DualNumber R) ?_
    rw [map_mul]
    exact (k _).symm.trans ((congrArg Units.val e).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (k _) (k _))))
  refine ⟨AddMonoidHom.mk' (fun χ => TrivSqZeroExt.snd (u χ : DualNumber R)) fun χ χ' => ?_, fun χ Z q z J hJ => ?_⟩
  · rw [hm, DualNumber.snd_mul, h1, h1]; ring
  · refine (hv χ Z q z J hJ).trans (congrArg (fun x => gs q z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom x)) ?_)
    exact TrivSqZeroExt.ext (by simp [h1]) (by simp)

end GlobalTheory.MBLow.GtTanClass

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentCharacterValuesAdditiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionTangent_characterValues_additive : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (gm : GtPt D (epsR R)), GtTan gm → gm.b = DegPre.zeroT D (epsR R) → ∃ l : D.X →+ R, ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  first | exact @GlobalTheory.MBLow.GtTanClass.main | exact GlobalTheory.MBLow.GtTanClass.main | (intros; apply GlobalTheory.MBLow.GtTanClass.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentCombinationCharacterValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentCombinationCharacterValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorusVals

variable {R : Type} [CommRing R]

theorem dual_mul (a b : R) : ((1 : DualNumber R) + TrivSqZeroExt.inr a) * (1 + TrivSqZeroExt.inr b) = 1 + TrivSqZeroExt.inr (a + b) := by
  ext <;> simp [add_comm]

theorem epsScaleR_one_add (c a : R) : epsScaleR c (1 + TrivSqZeroExt.inr a) = 1 + TrivSqZeroExt.inr (c * a) := by
  ext <;> simp [epsScaleR, mul_comm]

section Gs

variable {Z : Scheme.{0}} (q : Z ⟶ (epsR R).left) (z : Z)

theorem gs_one_add_zero : gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr 0)) = 1 := by
  rw [gs_eq q z ⊤ trivial, TrivSqZeroExt.inr_zero, add_zero, map_one, map_one, map_one]

theorem gs_dual_mul (a b : R) :
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) *
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr b)) =
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a + b))) := by
  rw [← gs_mul q z ⊤ trivial, ← map_mul, dual_mul]

theorem gs_scale (c a : R) :
    gs (q ≫ (epsScale R c).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) =
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (c * a))) := by
  rw [← gs_pull q (epsScale R c).left z ⊤ trivial, ← epsScaleR_one_add]
  have e := congrArg (fun f => f.hom (1 + TrivSqZeroExt.inr a : DualNumber R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (epsScaleR c)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [e]
  rfl

end Gs

variable [IsDomain R] {D : DegPre R} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

def HasVals (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T) (y : epsR R ⟶ H) (a : D.X → R) : Prop :=
  (Φ _ y).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    (val ((Φ _ y).s χ) q z J).val = gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a χ)))

theorem hasVals_one (hΦ : TorusModel.Represents Φ) : HasVals Φ 1 (fun _ => 0) := by
  have hz : (Φ (epsR R) 1).IsZero := GtVec.isZero_of_isAdd (by simpa using hΦ.2 (epsR R) 1 1)
  refine ⟨hz.1, fun χ Z q z J hJ => ?_⟩
  rw [val_corr hJ (hz.2 χ) q, val_one, gs_one_add_zero]
  rfl

theorem hasVals_scale (hΦ : TorusModel.Represents Φ) {y : epsR R ⟶ H} {a : D.X → R} (h : HasVals Φ y a) (c : R) :
    HasVals Φ (epsScale R c ≫ y) (fun χ => c * a χ) := by
  have hp := hΦ.1 (epsR R) (epsR R) (epsScale R c) y
  refine ⟨?_, fun χ Z q z J hJ => ?_⟩
  · rw [((TorusModel.isPull_iff _ _ _).1 hp).1, h.1]
    simp only [DegPre.zeroT, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  · rw [val_corr hJ (hp.2 χ) q, val_pull hJ, h.2 χ Z _ z J hJ, gs_scale]

theorem hasVals_mul (hΦ : TorusModel.Represents Φ) {y y' : epsR R ⟶ H} {a a' : D.X → R} (h : HasVals Φ y a)
    (h' : HasVals Φ y' a') : HasVals Φ (y * y') (fun χ => a χ + a' χ) := by
  have hs := hΦ.2 (epsR R) y y'
  refine ⟨?_, fun χ Z q z J hJ => ?_⟩
  · rw [((TorusModel.isAdd_iff _ _ _).1 hs).1, h.1, h'.1]
    exact _root_.mul_one _
  · have e := (val_mul hJ _ _ q).symm.trans ((val_corr hJ (hs.2 χ) q).trans (val_mul hJ _ _ q))
    let T' : Over (Sp R) := Over.mk (q ≫ (epsR R).hom)
    let ρ : T' ⟶ epsR R := Over.homMk q rfl
    have hc : val (DegPre.cubAtT D (epsR R) (DegPre.cT D (epsR R) χ) (Φ _ y).b (Φ _ y').b) q z J = 1 := by
      have := val_cub D.cub ρ hJ (DegPre.cT D (epsR R) χ) (Φ _ y).b (Φ _ y').b
      refine this.trans ?_
      rw [h'.1]
      have e1 : ρ ≫ DegPre.zeroT D (epsR R) = (1 : T' ⟶ D.P.A) := by
        simp only [DegPre.zeroT, ← Category.assoc]
        rw [Hom.one_def]
        congr 1
      rw [e1]
      exact (isCub_cubV D.cub hJ).face₃ _ _
    rw [hc, _root_.mul_one] at e
    rw [e, Units.val_mul, h.2 χ Z q z J hJ, h'.2 χ Z q z J hJ, gs_dual_mul]

end GlobalTheory.MBLow.TorusVals

namespace GlobalTheory.MBLow.TorusVals

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H]
  {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

theorem hasVals_tanComb (hΦ : TorusModel.Represents Φ) : ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)),
    (∀ l, HasVals Φ (x l) (a l)) → ∀ d : Fin r → R, HasVals Φ (tanComb d x) (fun χ => ∑ l, d l * a l χ)
  | 0, a, x, _, d => by
    have e : tanComb d x = 1 := by simp [tanComb]
    have ef : (fun χ => ∑ l : Fin 0, d l * a l χ) = fun _ => 0 := funext fun _ => by simp
    rw [e, ef]
    exact hasVals_one hΦ
  | r + 1, a, x, hx, d => by
    have e : tanComb d x = (epsScale R (d 0) ≫ x 0) * tanComb (fun i => d i.succ) (fun i => x i.succ) := by
      simp only [tanComb, List.ofFn_succ, List.prod_cons]
    have key := hasVals_mul hΦ (hasVals_scale hΦ (hx 0) (d 0))
      (hasVals_tanComb hΦ r (fun i => a i.succ) (fun i => x i.succ) (fun l => hx l.succ) (fun i => d i.succ))
    have ef : (fun χ => ∑ l, d l * a l χ) = fun χ => d 0 * a 0 χ + ∑ l : Fin r, d l.succ * a l.succ χ :=
      funext fun χ => Fin.sum_univ_succ _
    rw [e, ef]
    exact key

theorem tanComb_vals : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)), (∀ l, (Φ _ (x l)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x l)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a l χ)))) → ∀ d : Fin r → R, (Φ _ (tanComb d x)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (tanComb d x)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (∑ l, d l * a l χ))) :=
  fun _ _ _ _ _ _ _ _ hΦ r a x hx d => hasVals_tanComb hΦ r a x hx d

end GlobalTheory.MBLow.TorusVals

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentCombinationCharacterValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.torusTangentCombination_characterValues : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)), (∀ l, (Φ _ (x l)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x l)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a l χ)))) → ∀ d : Fin r → R, (Φ _ (tanComb d x)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (tanComb d x)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (∑ l, d l * a l χ))) := by
  first | exact @GlobalTheory.MBLow.TorusVals.tanComb_vals | exact GlobalTheory.MBLow.TorusVals.tanComb_vals | (intros; apply GlobalTheory.MBLow.TorusVals.tanComb_vals <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisTorusExtensionOfLiftsAndDuals
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GtBasis

open GlobalTheory.TorusModel

section Tangent

variable {R : Type} [CommRing R]

def redO (R : Type) [CommRing R] : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) GlobalTheory.MBLow.GtVec.red_comp

theorem isTangent_iff {G : Over (Sp R)} [GrpObj G] (y : epsR R ⟶ G) : IsTangent y ↔ redO R ≫ y = 1 := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    refine h.trans ?_
    simp [Hom.one_def]
  · intro h
    have := congrArg (·.left) h
    refine this.trans ?_
    simp [Hom.one_def]

theorem redO_scale (c : R) : redO R ≫ epsScale R c = redO R := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = spMap _
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  simp [epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem isTangent_mul {y y' : epsR R ⟶ G} (h : IsTangent y) (h' : IsTangent y') : IsTangent (y * y') := by
  rw [isTangent_iff] at *
  rw [MonObj.comp_mul, h, h', _root_.mul_one]

theorem isTangent_inv {y : epsR R ⟶ G} (h : IsTangent y) : IsTangent y⁻¹ := by
  rw [isTangent_iff] at *
  rw [GrpObj.comp_inv, h, inv_one]

theorem isTangent_scale (c : R) {y : epsR R ⟶ G} (h : IsTangent y) : IsTangent (epsScale R c ≫ y) := by
  rw [isTangent_iff] at *
  rw [← Category.assoc, redO_scale, h]

theorem isTangent_tanComb {m : ℕ} (c : Fin m → R) {v : Fin m → (epsR R ⟶ G)} (h : ∀ i, IsTangent (v i)) :
    IsTangent (tanComb c v) := by
  unfold tanComb
  refine List.prod_induction (fun y => IsTangent y) (fun _ _ => isTangent_mul) ?_ ?_
  · exact (isTangent_iff _).2 (MonObj.comp_one _)
  · intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact isTangent_scale _ (h i)

theorem eq_tanComb' {m : ℕ} {c : Fin m → R} {v : Fin m → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    w = tanComb c v := by
  obtain ⟨u, hu, rfl⟩ := h
  unfold tanComb
  congr 2
  exact funext fun i => Over.OverMorphism.ext (hu i)

end Tangent

section Stalk

variable {R : Type} [CommRing R]

theorem gs_id_eq (z : Sp R) (a : R) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp R)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = toStkA z a := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq _ z ⊤ trivial]
  simp [toStkA]
  rfl

theorem dn_inj [IsLocalRing (DualNumber R)] {a a' : R}
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp (DualNumber R))) (cpt (DualNumber R)) ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp (DualNumber R))) (cpt (DualNumber R)) ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a'))) : a = a' := by
  rw [gs_id_eq, gs_id_eq] at h
  exact TrivSqZeroExt.inr_injective (add_left_cancel (toStkA_injective h))

end Stalk

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ D.X) (x : Fin D.P.g ⊕ Fin r → (epsR R ⟶ H)), IsLieBasis vB → (∀ j, GtTan (Φ _ (x j))) → (∀ i, (Φ _ (x (Sum.inl i))).b = vB i) → (∀ l, (Φ _ (x (Sum.inr l))).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x (Sum.inr l))).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : R)))) → ∀ (n : ℕ) (σ : Fin n ≃ Fin D.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := by
  intro R _ _ _ D H _ _ Φ hΦ r vB bX x hvB htan hb htor n σ
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GtVec.isZero_of_isAdd (by simpa using hΦ.2 T 1 1)
  have bpull : ∀ (T T' : Over (Sp R)) (k : T' ⟶ T) (y : T ⟶ H), (Φ T' (k ≫ y)).b = k ≫ (Φ T y).b :=
    fun T T' k y => ((isPull_iff _ _ _).1 (hΦ.1 T' T k y)).1
  have gtan : ∀ y : epsR R ⟶ H, GtTan (Φ _ y) ↔ IsTangent y := by
    intro y
    rw [isTangent_iff]
    exact ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((isPull_unique (hΦ.1 _ _ (redO R) y) h).trans
      (GtVec.isZero_unique ho (hz _))), fun h => ⟨Φ _ 1, hz _, h ▸ hΦ.1 _ _ (redO R) y⟩⟩
  let β : (epsR R ⟶ H) →* (epsR R ⟶ D.P.A) :=
    { toFun := fun y => (Φ _ y).b
      map_one' := (hz _).1
      map_mul' := fun y y' => ((TorusModel.isAdd_iff _ _ _).1 (hΦ.2 _ y y')).1 }
  have βapp : ∀ y, β y = (Φ _ y).b := fun _ => rfl
  have βcomb : ∀ {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ H)),
      β (tanComb c v) = tanComb c (fun i => β (v i)) := by
    intro m c v
    simp only [tanComb, map_list_prod, List.map_ofFn]
    congr 1
    exact List.ofFn_inj.2 (funext fun i => bpull _ _ _ _)
  have βtan : ∀ y, IsTangent y → IsTangent (β y) := fun y h => (isTangent_iff _).2 (by
    rw [βapp, ← bpull, (isTangent_iff y).1 h]
    exact (hz _).1)
  have xtan : ∀ j, IsTangent (x j) := fun j => (gtan _).1 (htan j)
  have tor := GlobalTheory.T.torusTangentCombination_characterValues R D H Φ hΦ r (fun l χ => ((bX.repr χ l : ℤ) : R)) (fun l => x (Sum.inr l)) htor
  have split : ∀ c : Fin n → R, tanComb c (fun k => x (σ k)) =
      tanComb (fun i => c (σ.symm (Sum.inl i))) (fun i => x (Sum.inl i)) *
        tanComb (fun l => c (σ.symm (Sum.inr l))) (fun l => x (Sum.inr l)) := by
    intro c
    simp only [tanComb, List.prod_ofFn]
    have e := Equiv.prod_comp σ (fun j => epsScale R (c (σ.symm j)) ≫ x j)
    simp only [Equiv.symm_apply_apply] at e
    rw [e, Fintype.prod_sum_type]
  have βA : ∀ a : Fin D.P.g → R, β (tanComb a (fun i => x (Sum.inl i))) = tanComb a vB := by
    intro a
    rw [βcomb]
    simp only [βapp, hb]
  have βB : ∀ d : Fin r → R, β (tanComb d (fun l => x (Sum.inr l))) = 1 := fun d => (tor d).1
  have : IsLocalRing (DualNumber R) := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber R
  obtain ⟨J₀, hJ₀⟩ := TorusCoord.exists_good' D.P.isLB (cpt (DualNumber R))

  have uniq : ∀ c c' : Fin n → R, tanComb c (fun k => x (σ k)) = tanComb c' (fun k => x (σ k)) → c = c' := by
    intro c c' h
    rw [split, split] at h
    have hA := congrArg β h
    rw [map_mul, map_mul, βA, βA, βB, βB, _root_.mul_one, _root_.mul_one] at hA
    have ha : (fun i => c (σ.symm (Sum.inl i))) = (fun i => c' (σ.symm (Sum.inl i))) := by
      refine (hvB.2 _ (isTangent_tanComb _ hvB.1)).unique (isLieComb_tanComb _ _) ?_
      rw [hA]
      exact isLieComb_tanComb _ _
    rw [ha, mul_right_inj] at h
    have he : ∀ l, c (σ.symm (Sum.inr l)) = c' (σ.symm (Sum.inr l)) := by
      intro l
      have v1 := (tor (fun l => c (σ.symm (Sum.inr l)))).2 (bX l) _ (𝟙 _) _ J₀ hJ₀
      have v2 := (tor (fun l => c' (σ.symm (Sum.inr l)))).2 (bX l) _ (𝟙 _) _ J₀ hJ₀
      rw [h] at v1
      have := dn_inj (v1.symm.trans v2)
      simp only [Module.Basis.repr_self, Finsupp.single_apply] at this
      simpa using this
    funext k
    obtain ⟨j, rfl⟩ := σ.symm.surjective k
    rcases j with i | l
    · exact congrFun ha i
    · exact he l
  refine ⟨fun k => xtan (σ k), fun w hw => ?_⟩
  obtain ⟨c₁, hc₁, -⟩ := hvB.2 (β w) (βtan w hw)
  have hw₁ : β (tanComb c₁ (fun i => x (Sum.inl i))) = β w := by
    rw [βA]
    exact (eq_tanComb' hc₁).symm
  have tw' : IsTangent (w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹) :=
    isTangent_mul hw (isTangent_inv (isTangent_tanComb _ fun i => xtan _))
  have bw' : (Φ _ (w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹)).b = DegPre.zeroT D (epsR R) := by
    rw [← βapp, map_mul, map_inv, hw₁, mul_inv_cancel]
    rfl
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.torusExtensionTangent_characterValues_additive R D _ ((gtan _).2 tw') bw'
  have hl : ∀ χ, lam χ = ∑ l, lam (bX l) * ((bX.repr χ l : ℤ) : R) := by
    intro χ
    conv_lhs => rw [← bX.sum_repr χ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  obtain ⟨bd, vd⟩ := tor (fun l => lam (bX l))
  have e : w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹ = tanComb (fun l => lam (bX l)) (fun l => x (Sum.inr l)) :=
    (Φ _).injective (pt_ext (bw'.trans bd.symm) fun χ y J hJ => Units.ext ((hlam χ _ _ y J hJ).trans
      ((congrArg _ (by rw [hl χ])).trans (vd χ _ _ y J hJ).symm)))
  have hw : w = tanComb (fun k => Sum.elim c₁ (fun l => lam (bX l)) (σ k)) (fun k => x (σ k)) := by
    rw [split]
    simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← e, mul_comm w, mul_inv_cancel_left]
  refine ⟨_, hw ▸ isLieComb_tanComb _ _, fun c hc => ?_⟩
  exact uniq _ _ ((eq_tanComb' hc).symm.trans hw)

end GlobalTheory.GtBasis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisTorusExtensionOfLiftsAndDualsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.lieBasis_torusExtension_of_lifts_and_duals : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ D.X) (x : Fin D.P.g ⊕ Fin r → (epsR R ⟶ H)), IsLieBasis vB → (∀ j, GtTan (Φ _ (x j))) → (∀ i, (Φ _ (x (Sum.inl i))).b = vB i) → (∀ l, (Φ _ (x (Sum.inr l))).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x (Sum.inr l))).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : R)))) → ∀ (n : ℕ) (σ : Fin n ≃ Fin D.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := by
  first | exact @GlobalTheory.GtBasis.main | exact GlobalTheory.GtBasis.main | (intros; apply GlobalTheory.GtBasis.main <;> assumption) | exact @GlobalTheory.GtBasis.dn_inj | exact GlobalTheory.GtBasis.dn_inj | (intros; apply GlobalTheory.GtBasis.dn_inj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentPullbackComplexDualNumbers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentPullbackComplexDualNumbers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanPull


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel in
set_option maxHeartbeats 1000000 in
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR V)), GtTan gm₀ → ∃ gm : GtPt D (TE V C), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm ∧ (∃ o : GtPtF D C, o.IsZero ∧ GtPt.IsPullF C (redE C) gm o) ∧ (gm₀.b = DegPre.zeroT D (epsR V) → gm.b = DegPre.zeroT D (TE V C)) ∧ ∀ (a : V) (χ : D.X), (∀ (Z : Scheme.{0}) (q : Z ⟶ (epsR V).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm₀.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))) → vE (gm.s χ) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr (toF V C a) := by
  intro V _ _ D C _ _ N ν gm₀ htan
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨H, _, _, hH⟩ := TorusModel.exists_isGt hG (TorusModel.splitExt D)
  obtain ⟨Φ, hp, ha⟩ := TorusModel.exists_points hG hH
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GtVec.isZero_of_isAdd (by simpa using ha T 1 1)
  have hTF : spMap (toF V C) = (TF (R := V) C).hom := by
    simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hTE : spMap (dualMap (toF V C)) ≫ (epsR V).hom = (TE V C).hom := by
    rw [TanLift.dualMap_over, hTF]; rfl
  let hh : TE V C ⟶ epsR V := Over.homMk (spMap (dualMap (toF V C))) hTE
  obtain ⟨x₀, rfl⟩ := (Φ (epsR V)).surjective gm₀
  refine ⟨Φ _ (hh ≫ x₀), hp _ _ hh x₀, ?_, ?_, ?_⟩
  · obtain ⟨o₀, ho₀, hpo⟩ := htan
    let r : baseOver (Sp V) ⟶ epsR V := Over.homMk (redE V) (TanLift.redE_over V)
    have e₀ : o₀ = Φ _ (r ≫ x₀) := by
      have hpo' : GtPt.IsPull (redE V) (Φ _ x₀) (Φ _ (r ≫ x₀)) := hp _ _ r x₀
      generalize hg : Φ _ (r ≫ x₀) = g at hpo' ⊢
      obtain ⟨b, s, h, hs, hm⟩ := o₀
      obtain ⟨b', s', h', hs', hm'⟩ := g
      have hb : b = b' := Over.OverMorphism.ext (hpo.1.trans hpo'.1.symm)
      subst b'
      have he : s = s' := funext fun χ =>
        GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (h χ) (h' χ)
          (corr_of_val D.P.isLB fun y J hJ =>
            (val_corr hJ (hpo.2 χ) _).trans (val_corr hJ (hpo'.2 χ) _).symm)
      subst s'
      rfl
    have e₁ : r ≫ x₀ = 1 := (Φ _).injective ((e₀.symm.trans (GtVec.isZero_unique ho₀ (hz _))))
    let k : TF (R := V) C ⟶ TE V C := Over.homMk (redE C) (by
      show redE C ≫ spMap (algebraMap C (DualNumber C)) ≫ (TF (R := V) C).hom = (TF (R := V) C).hom
      rw [← Category.assoc, GtVec.red_comp, Category.id_comp])
    let tf : TF (R := V) C ⟶ baseOver (Sp V) := Over.homMk (TF (R := V) C).hom (Category.comp_id _)
    have e₂ : k ≫ hh = tf ≫ r := by
      ext
      show redE C ≫ spMap (dualMap (toF V C)) = (TF (R := V) C).hom ≫ redE V
      rw [← hTF]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have e₃ : k ≫ hh ≫ x₀ = 1 := by
      rw [← Category.assoc, e₂, Category.assoc, e₁, MonObj.comp_one]
    have hpk := hp _ _ k (hh ≫ x₀)
    rw [e₃] at hpk
    let g := Φ (TF (R := V) C) 1
    refine ⟨⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩, ⟨(hz _).1, (hz _).2⟩, hpk⟩
  · intro hb
    have e := ((TorusModel.isPull_iff _ _ _).1 (hp _ _ hh x₀)).1
    rw [e, hb]
    simp
  · intro a χ hval
    have hloc : IsLocalRing (DualNumber C) := TanLift.isLocalRing_dualNumber C
    have hlocH : IsLocalHom (TrivSqZeroExt.fstHom C C C).toRingHom :=
      ⟨fun x hx => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 hx⟩
    set gm := Φ _ (hh ≫ x₀)
    let J' : (Sp (DualNumber C) ⟶ D.P.A.left) → D.P.L.ι := fun ψ => ν.J (redE C ≫ ψ)
    have hJ' : Good D.P.L (cpt (DualNumber C)) J' := fun ψ => by
      have h1 := ν.good (redE C ≫ ψ) (show cpt C ∈ (⊤ : (Sp C).Opens) from trivial)
      have hc : (redE C) (cpt C) = cpt (DualNumber C) :=
        IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom C C C).toRingHom
      have h2 : ψ ((redE C) (cpt C)) ∈ D.P.L.U (J' ψ) := h1
      rw [hc] at h2
      exact h2
    have ht := (top_le_iff_cpt (𝟙 (Sp (DualNumber C))) _).2 (hJ'.mem (DegPre.gtφT D (TE V C) gm.b χ) (𝟙 _))
    apply toStkA_injective (A := DualNumber C)
    have toStkA_valR {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X)
        (U : X.Opens) (z : Sp A) (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
        toStkA z (valR x U a.val) = (Geo.Tor.gm x z U a).val := by
      have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp A).Opens) from trivial)
      rw [valR, dif_pos ht, Geo.Tor.gm, dif_pos hz]
      show ((Sp A).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ ht).hom a.val))) = _
      rw [Iso.hom_inv_id_apply]
      exact TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE ht) z trivial _
    have l1 := toStkA_valR (𝟙 (Sp (DualNumber C))) _ (cpt (DualNumber C)) ht ((gm.s χ).s _)
    have l2 := (val_corr hJ' ((hp _ _ hh x₀).2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
    have l3 := hval _ (𝟙 _ ≫ hh.left) _ _ hJ'
    have hv1 : valR (𝟙 (Sp (DualNumber V))) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom
        (1 + TrivSqZeroExt.inr a)) = 1 + TrivSqZeroExt.inr a := by
      have h0 : ⊤ ≤ 𝟙 (Sp (DualNumber V)) ⁻¹ᵁ ⊤ := fun _ _ => trivial
      rw [valR, dite_eq_left h0]
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      erw [show (homOfLE h0) = 𝟙 (⊤ : (Sp (DualNumber V)).Opens) from rfl]
      simp
    have l4 := FormalValue.toStkA_map_valR (dualMap (toF V C)) (𝟙 (Sp (DualNumber V))) ⊤ (cpt (DualNumber C))
      (fun _ _ => trivial) ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))
    rw [hv1, Category.comp_id] at l4
    have hd : dualMap (toF V C) (1 + TrivSqZeroExt.inr a) = 1 + TrivSqZeroExt.inr (toF V C a) := by
      ext <;> simp [dualMap]
    rw [hd] at l4
    rw [l4]
    refine l1.trans ?_
    refine (congrArg Units.val l2).trans ?_
    refine l3.trans ?_
    rw [Category.id_comp]
    rfl

end GlobalTheory.MBLow.TanPull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentPullbackComplexDualNumbersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionTangent_pullback_complexDualNumbers : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR V)), GtTan gm₀ → ∃ gm : GtPt D (TE V C), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm ∧ (∃ o : GtPtF D C, o.IsZero ∧ GtPt.IsPullF C (redE C) gm o) ∧ (gm₀.b = DegPre.zeroT D (epsR V) → gm.b = DegPre.zeroT D (TE V C)) ∧ ∀ (a : V) (χ : D.X), (∀ (Z : Scheme.{0}) (q : Z ⟶ (epsR V).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm₀.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))) → vE (gm.s χ) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr (toF V C a) := by
  first | exact @GlobalTheory.MBLow.TanPull.main | exact GlobalTheory.MBLow.TanPull.main | (intros; apply GlobalTheory.MBLow.TanPull.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTangentOfAdditiveMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTangentOfAdditiveMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorVec

theorem exists_torus_tangent : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (l : D.X →+ R), ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ D l
  obtain ⟨ν, hb, hv⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := epsR R)
    (fun x => GlobalTheory.TorusTangent.oneAdd (l x)) fun x y => by rw [map_add (f := _), GlobalTheory.TorusTangent.oneAdd_add]
  refine ⟨ν, ?_, hb, fun χ Z q z J hJ => ?_⟩
  · obtain ⟨g₀, h₀, v₀⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := baseOver (Sp R)) (fun _ => 1)
      fun _ _ => (_root_.mul_one _).symm
    refine ⟨g₀, ⟨h₀, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩, ?_, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · rw [v₀ x _ _ y J hJ, map_one, val_one]
    · rw [h₀, hb, GlobalTheory.TorusTangent.zeroT_left, GlobalTheory.TorusTangent.zeroT_left, ← Category.assoc]
      exact congrArg (· ≫ eSec D.P.A) GlobalTheory.TorusTangent.fst_inl.symm
    · refine (v₀ x _ _ y J hJ).trans (Units.ext (Eq.trans ?_
        (GlobalTheory.TorusTangent.hasVal_spMap (hv x) (TrivSqZeroExt.fstHom R R R).toRingHom hJ).symm))
      rw [GlobalTheory.TorusTangent.valR_oneAdd, map_one]
      simp
  · rw [hv χ Z q z J hJ, ← gs_unit q z ⊤ trivial]
    rfl

end GlobalTheory.MBLow.TorVec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTangentOfAdditiveMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusExtensionTangent_of_additiveMap : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (l : D.X →+ R), ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  first | exact @GlobalTheory.MBLow.TorVec.exists_torus_tangent | exact GlobalTheory.MBLow.TorVec.exists_torus_tangent | (intros; apply GlobalTheory.MBLow.TorVec.exists_torus_tangent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDimUniformisationDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDimUniformisationDvr
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieRankUnif

theorem card_eq_g : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (IsLocalRing.maximalIdeal V) D A G) (n : ℕ) (y : Fin n → (epsR V ⟶ G)), IsLieBasis y → n = A.g := by
  intro V _ _ _ D A G _ _ U n y hy
  have := U.smooth
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  obtain ⟨φ, gp⟩ : ∃ φ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) φ :=
    ⟨_, ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl⟩
  obtain ⟨v, hv, -⟩ := GlobalTheory.exists_isLieBasis_baseChange V (FractionRing V) (algebraMap V _) G A.A φ gp U.smooth n y hy
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.KeyPow.exists_isLieBasis A.A A.smoothDim
  exact GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis gp hv hv₀

end GlobalTheory.LieRankUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDimUniformisationDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieBasis_card_eq_dim_uniformisation_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (IsLocalRing.maximalIdeal V) D A G) (n : ℕ) (y : Fin n → (epsR V ⟶ G)), IsLieBasis y → n = A.g := by
  first | exact @GlobalTheory.LieRankUnif.card_eq_g | exact GlobalTheory.LieRankUnif.card_eq_g | (intros; apply GlobalTheory.LieRankUnif.card_eq_g <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisOfCompatibleTangentRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisOfCompatibleTangentRelation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieTransfer

open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent

variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]

theorem rel_comb (Rel : (epsR R ⟶ G) → (epsR R ⟶ H) → Prop) (h1 : Rel 1 1)
    (hmul : ∀ y y' x x', Rel y x → Rel y' x' → Rel (y * y') (x * x'))
    (hsc : ∀ (c : R) (y : epsR R ⟶ G) (x : epsR R ⟶ H) (y' : epsR R ⟶ G) (x' : epsR R ⟶ H),
      y'.left = spMap (epsScaleR c) ≫ y.left → x'.left = spMap (epsScaleR c) ≫ x.left → Rel y x → Rel y' x')
    {n : ℕ} (x : Fin n → (epsR R ⟶ H)) (y : Fin n → (epsR R ⟶ G)) (hr : ∀ j, Rel (y j) (x j))
    (c : Fin n → R) : Rel (comb y c) (comb x c) := by
  classical
  unfold comb
  suffices h : ∀ s : Finset (Fin n), Rel (∏ i ∈ s, epsScale (c i) ≫ y i) (∏ i ∈ s, epsScale (c i) ≫ x i) from h _
  intro s
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using h1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact hmul _ _ _ _ (hsc (c a) (y a) (x a) _ _ rfl rfl (hr a)) ih

end GlobalTheory.LieTransfer


open GlobalTheory.Reg.VecEig GlobalTheory.LieTransfer in
theorem GlobalTheory.LieTransfer.isLieBasis_of_rel : ∀ (R : Type) [CommRing R] (G H : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (Rel : (epsR R ⟶ G) → (epsR R ⟶ H) → Prop), Rel 1 1 → (∀ y y' x x', Rel y x → Rel y' x' → Rel (y * y') (x * x')) → (∀ (c : R) (y : epsR R ⟶ G) (x : epsR R ⟶ H) (y' : epsR R ⟶ G) (x' : epsR R ⟶ H), y'.left = spMap (epsScaleR c) ≫ y.left → x'.left = spMap (epsScaleR c) ≫ x.left → Rel y x → Rel y' x') → (∀ y, IsTangent y → ∃ x, IsTangent x ∧ Rel y x) → (∀ y y' x, IsTangent y → IsTangent y' → Rel y x → Rel y' x → y = y') → (∀ y x x', Rel y x → Rel y x' → x = x') → ∀ (n : ℕ) (x : Fin n → (epsR R ⟶ H)) (y : Fin n → (epsR R ⟶ G)), IsLieBasis x → (∀ j, IsTangent (y j) ∧ Rel (y j) (x j)) → IsLieBasis y := by
  intro R _ G H _ _ _ _ Rel h1 hmul hsc hex hinj hfun n x y hx hy
  have hyt : ∀ j, IsTangent (y j) := fun j => (hy j).1
  have hrc := rel_comb Rel h1 hmul hsc x y (fun j => (hy j).2)
  refine ⟨hyt, fun w hw => ?_⟩
  obtain ⟨xw, hxw, hrw⟩ := hex w hw
  obtain ⟨c, hc, -⟩ := hx.2 xw hxw
  rw [isLieComb_iff_comb] at hc
  subst hc
  refine ⟨c, (isLieComb_iff_comb _ _ _).2 (hinj w _ _ hw (isTangent_comb hyt c) hrw (hrc c)), ?_⟩
  intro c' hc'
  rw [isLieComb_iff_comb] at hc'
  subst hc'
  have e2 : comb x c = comb x c' := hfun _ _ _ (hrc c') hrw |>.symm
  exact (comb_injective hx e2).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisOfCompatibleTangentRelationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLieBasis_of_compatible_tangentRelation : ∀ (R : Type) [CommRing R] (G H : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (Rel : (epsR R ⟶ G) → (epsR R ⟶ H) → Prop), Rel 1 1 → (∀ y y' x x', Rel y x → Rel y' x' → Rel (y * y') (x * x')) → (∀ (c : R) (y : epsR R ⟶ G) (x : epsR R ⟶ H) (y' : epsR R ⟶ G) (x' : epsR R ⟶ H), y'.left = spMap (epsScaleR c) ≫ y.left → x'.left = spMap (epsScaleR c) ≫ x.left → Rel y x → Rel y' x') → (∀ y, IsTangent y → ∃ x, IsTangent x ∧ Rel y x) → (∀ y y' x, IsTangent y → IsTangent y' → Rel y x → Rel y' x → y = y') → (∀ y x x', Rel y x → Rel y x' → x = x') → ∀ (n : ℕ) (x : Fin n → (epsR R ⟶ H)) (y : Fin n → (epsR R ⟶ G)), IsLieBasis x → (∀ j, IsTangent (y j) ∧ Rel (y j) (x j)) → IsLieBasis y := by
  first | exact @GlobalTheory.LieTransfer.isLieBasis_of_rel | exact GlobalTheory.LieTransfer.isLieBasis_of_rel | (intros; apply GlobalTheory.LieTransfer.isLieBasis_of_rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedLieBasisTorusExtensionModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Adapt

set_option maxHeartbeats 1000000 in
theorem main : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∃ (vB : Fin D.toPre.P.g → (epsR V ⟶ D.toPre.P.A)) (r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r) (y : Fin A.g → (epsR V ⟶ G)) (gm₀ : Fin A.g → GtPt D.toPre (epsR V)) (gm : Fin A.g → GtPt D.toPre (TE V C)), IsLieBasis y ∧ Adapted ν vB bX σ gm ∧ ∀ j, TanRel U.toUnifPre (y j) (gm₀ j) ∧ GtTan (gm₀ j) ∧ GtPt.IsPull (spMap (dualMap (toF V C))) (gm₀ j) (gm j) := by
  intro V _ _ _ _ hV D A G _ _ hS U C _ _ _ _ _ _ hC N ν hν
  haveI := hV
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨H, _, _, hH⟩ := GlobalTheory.TorusModel.exists_isGt hG (GlobalTheory.TorusModel.splitExt D.toPre)
  obtain ⟨Φ, hp, ha⟩ := GlobalTheory.TorusModel.exists_points hG hH
  have hΦ : GlobalTheory.TorusModel.Represents Φ := ⟨hp, ha⟩
  obtain ⟨vB, hvB⟩ := GlobalTheory.KeyPow.exists_isLieBasis D.toPre.P.A D.toPre.P.smoothDim
  let r := Module.finrank ℤ N.X
  let bX : Module.Basis (Fin r) ℤ N.X := Module.finBasis ℤ N.X
  let bD : Module.Basis (Fin r) ℤ D.toPre.X := bX.map ν.eX.toIntLinearEquiv
  choose lf hlf using fun i => (GlobalTheory.MBLow.GtVec.main V D.toPre).1 (vB i) (hvB.1 i)
  choose tv htv using fun l : Fin r => GlobalTheory.T.exists_torusExtensionTangent_of_additiveMap V D.toPre ((Int.castAddHom V).comp (bD.coord l).toAddMonoidHom)
  have hco : ∀ (l : Fin r) (χ : D.toPre.X), ((Int.castAddHom V).comp (bD.coord l).toAddMonoidHom) χ = ((bD.repr χ l : ℤ) : V) :=
    fun l χ => by simp [Module.Basis.coord_apply]
  let gm₀ : Fin D.toPre.P.g ⊕ Fin r → GtPt D.toPre (epsR V) := Sum.elim lf tv
  have hgt : ∀ j, GtTan (gm₀ j) := fun j => by
    cases j with
    | inl i => exact (hlf i).1
    | inr l => exact (htv l).1
  let x : Fin D.toPre.P.g ⊕ Fin r → (epsR V ⟶ H) := fun j => (Φ _).symm (gm₀ j)
  have hx : ∀ j, Φ _ (x j) = gm₀ j := fun j => Equiv.apply_symm_apply _ _
  have hxB : ∀ (n : ℕ) (σ : Fin n ≃ Fin D.toPre.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := fun n σ =>
    GlobalTheory.T.lieBasis_torusExtension_of_lifts_and_duals V D.toPre H Φ hΦ r vB bD x hvB (fun j => by rw [hx]; exact hgt j) (fun i => by rw [hx]; exact (hlf i).2)
      (fun l => by
        rw [hx]
        refine ⟨(htv l).2.1, fun χ Z q z J hJ => ?_⟩
        rw [← hco]
        exact (htv l).2.2 χ Z q z J hJ) n σ
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GlobalTheory.MBLow.GtVec.isZero_of_isAdd (by simpa using ha T 1 1)
  let red : baseOver (Sp V) ⟶ epsR V := Over.homMk (redE V) GlobalTheory.MBLow.GtVec.red_comp
  have tanG : ∀ w : epsR V ⟶ H, GtTan (Φ _ w) ↔ red ≫ w = 1 := fun w =>
    ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((GlobalTheory.TorusModel.isPull_unique (hp _ _ red w) h).trans
      (GlobalTheory.MBLow.GtVec.isZero_unique ho (hz _))), fun h => ⟨Φ _ 1, hz _, h ▸ hp _ _ red w⟩⟩
  have tanH : ∀ w : epsR V ⟶ H, IsTangent w ↔ red ≫ w = 1 := fun w => by
    constructor
    · intro h
      apply Over.OverMorphism.ext
      refine h.trans ?_
      show _ = (toUnit _ ≫ η[H]).left
      simp
    · intro h
      have := congrArg (·.left) h
      refine this.trans ?_
      show (toUnit _ ≫ η[H]).left = _
      simp
  have : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  have : Module.Flat V (DualNumber V) := inferInstanceAs (Module.Flat V (V × V))
  have := isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal V) (DualNumber V)
  have := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber V
  have hT : GlobalTheory.AdicColimit.IsAdicColimit (IsLocalRing.maximalIdeal V) (epsR V) :=
    GlobalTheory.TorusModel.isAdicColimit_of_finite_flat (IsLocalRing.maximalIdeal V) (RingHom.id V) (by rwa [Ideal.map_id])
      (fun a ha => ⟨1, by rw [Ideal.map_id, pow_one]; exact ha⟩) (DualNumber V)
  let Rel : (epsR V ⟶ G) → (epsR V ⟶ H) → Prop := fun y w => TanRel U.toUnifPre y (Φ _ w)
  have h1 : Rel 1 1 := (tanRel_iff_isPointOf U.toUnifPre 1 (Φ _ 1)).2 (GlobalTheory.FormalPoint.isPointOf_one U.toUnifPre (hz _))
  have hmul : ∀ y y' w w', Rel y w → Rel y' w' → Rel (y * y') (w * w') := fun y y' w w' h h' =>
    GlobalTheory.MBLow.TanAdd.tanRel_mul U.toUnifPre y y' _ _ _ h h' (ha _ w w')
  have hsc : ∀ (c : V) (y : epsR V ⟶ G) (w : epsR V ⟶ H) (y' : epsR V ⟶ G) (w' : epsR V ⟶ H),
      y'.left = spMap (epsScaleR c) ≫ y.left → w'.left = spMap (epsScaleR c) ≫ w.left → Rel y w → Rel y' w' := by
    intro c y w y' w' e e' h
    obtain rfl : y' = GlobalTheory.SecJet.epsScale V c ≫ y := Over.OverMorphism.ext e
    obtain rfl : w' = GlobalTheory.SecJet.epsScale V c ≫ w := Over.OverMorphism.ext e'
    exact GlobalTheory.MBLow.TanAdd.tanRel_scale U.toUnifPre c y _ _ h (hp _ _ _ w)
  have hex : ∀ y, IsTangent y → ∃ w, IsTangent w ∧ Rel y w := fun y hy => by
    obtain ⟨gm, h₁, h₂, -⟩ := GlobalTheory.MBLow.TanLift.exists_tan U.toUnifPre y hy
    refine ⟨(Φ _).symm gm, (tanH _).2 ((tanG _).1 (by rw [Equiv.apply_symm_apply]; exact h₂)), ?_⟩
    show TanRel _ _ _
    rw [Equiv.apply_symm_apply]; exact h₁
  have huy : ∀ y y' w, IsTangent y → IsTangent y' → Rel y w → Rel y' w → y = y' := fun y y' w _ _ h h' =>
    ((tanRel_iff_isPointOf _ _ _).1 h).unique ((tanRel_iff_isPointOf _ _ _).1 h')
  have hux : ∀ y w w', Rel y w → Rel y w' → w = w' := fun y w w' h h' =>
    (GlobalTheory.TorusModel.existsUnique_lift U.toUnifPre hΦ hT y).unique ((tanRel_iff_isPointOf _ _ _).1 h)
      ((tanRel_iff_isPointOf _ _ _).1 h')
  choose yy hyy using fun j => (existsUnique_tangent_of_gtTan V hV D A G hS U (gm₀ j) (hgt j)).exists
  have hyB : ∀ (n : ℕ) (σ : Fin n ≃ Fin D.toPre.P.g ⊕ Fin r), IsLieBasis (fun k => yy (σ k)) := fun n σ =>
    GlobalTheory.T.isLieBasis_of_compatible_tangentRelation V G H Rel h1 hmul hsc hex huy hux n _ _ (hxB n σ) fun k => ⟨(hyy _).1, by
      show TanRel _ _ _
      rw [hx]; exact (hyy _).2⟩
  have hdim : D.toPre.P.g + r = A.g := GlobalTheory.T.lieBasis_card_eq_dim_uniformisation_dvr V D A G U.toUnifPre _ _ (hyB _ finSumFinEquiv.symm)
  let σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r := (finCongr hdim.symm).trans finSumFinEquiv.symm
  choose gmC hgmC using fun j => GlobalTheory.T.torusExtensionTangent_pullback_complexDualNumbers V D.toPre C N ν (gm₀ j) (hgt j)
  refine ⟨vB, r, bX, σ, fun k => yy (σ k), fun k => gm₀ (σ k), fun k => gmC (σ k), hyB _ σ,
    ⟨hvB, fun j => (hgmC _).2.1, fun i => ?_, fun l => ?_⟩, fun k => ⟨(hyy _).2, hgt _, (hgmC _).1⟩⟩
  · dsimp only
    rw [σ.apply_symm_apply (Sum.inl i), (hgmC _).1.1]
    show _ ≫ (lf i).b.left = _
    rw [(hlf i).2]
  · dsimp only
    rw [σ.apply_symm_apply (Sum.inr l)]
    refine ⟨(hgmC _).2.2.1 (htv l).2.1, fun χ => ?_⟩
    refine ((hgmC _).2.2.2 (((bD.repr (ν.eX χ) l : ℤ) : V)) (ν.eX χ) fun Z q z J hJ => ?_).trans ?_
    · have hv := (htv l).2.2 (ν.eX χ) Z q z J hJ
      rw [hco] at hv
      exact hv
    · have e : bD.repr (ν.eX χ) l = bX.repr χ l := by
        show (bX.map ν.eX.toIntLinearEquiv).repr (ν.eX χ) l = _
        rw [Module.Basis.map_repr]
        simp
      rw [e, map_intCast]

end GlobalTheory.MBLow.Adapt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedLieBasisTorusExtensionModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_adaptedLieBasis_torusExtensionModel : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∃ (vB : Fin D.toPre.P.g → (epsR V ⟶ D.toPre.P.A)) (r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r) (y : Fin A.g → (epsR V ⟶ G)) (gm₀ : Fin A.g → GtPt D.toPre (epsR V)) (gm : Fin A.g → GtPt D.toPre (TE V C)), IsLieBasis y ∧ Adapted ν vB bX σ gm ∧ ∀ j, TanRel U.toUnifPre (y j) (gm₀ j) ∧ GtTan (gm₀ j) ∧ GtPt.IsPull (spMap (dualMap (toF V C))) (gm₀ j) (gm j) := by
  first | exact @GlobalTheory.MBLow.Adapt.main | exact GlobalTheory.MBLow.Adapt.main | (intros; apply GlobalTheory.MBLow.Adapt.main <;> assumption)
end
