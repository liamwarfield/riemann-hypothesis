module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TangentVectorExistsUniqueUniformisingVector
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointObjectExistsOfLaws
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.RatFn

theorem exists_genericRing (F K : Type) [Field F] [Field K] [Algebra F K] (B : Type) [Fintype B] (m : B → ℕ) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra F A) (π : K →ₐ[F] A) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) A),
      _root_.IsReduced A ∧ (∀ b, IsUnit (X b).det) ∧ ∀ t : A, ∃ (P : MvPolynomial (FrVar m) K) (N : ℕ),
        ∀ (S : Type) [CommRing S] [Algebra F S] (φ : K →ₐ[F] S) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S),
          (∀ b, IsUnit (Y b).det) → ∃ k : A →ₐ[F] S, k.comp π = φ ∧ (∀ b, (X b).map k = Y b) ∧
            (∏ b, (Y b).det) ^ N * k t = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  classical
  let X₀ : ∀ b, Matrix (Fin (m b)) (Fin (m b)) (MvPolynomial (FrVar m) K) :=
    fun b => Matrix.of fun i j => MvPolynomial.X ⟨b, (j, i)⟩
  let d : MvPolynomial (FrVar m) K := ∏ b, (X₀ b).det
  let A := Localization.Away d
  let jA : MvPolynomial (FrVar m) K →ₐ[F] A := IsScalarTower.toAlgHom F _ A
  have hd : IsUnit (algebraMap (MvPolynomial (FrVar m) K) A d) := IsLocalization.Away.algebraMap_isUnit d
  refine ⟨A, inferInstance, inferInstance, jA.comp (IsScalarTower.toAlgHom F K _),
    fun b => (X₀ b).map (algebraMap _ A), inferInstance, fun b => ?_, fun t => ?_⟩
  · beta_reduce
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun b => (X₀ b).det) (Finset.mem_univ b))) hd
  · obtain ⟨N, P, hP⟩ := IsLocalization.Away.surj d t
    refine ⟨P, N, fun S _ _ φ Y hY => ?_⟩
    let e : MvPolynomial (FrVar m) K →+* S :=
      MvPolynomial.eval₂Hom φ.toRingHom (fun v : FrVar m => Y v.1 v.2.2 v.2.1)
    have heX : ∀ b, (X₀ b).map e = Y b := fun b => by
      ext i j
      simp [e, X₀]
    have hed : e d = ∏ b, (Y b).det := by
      simp only [d, map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [RingHom.map_det, RingHom.mapMatrix_apply, heX]
    have hu : IsUnit (e d) := by
      rw [hed]
      exact IsUnit.prod_univ_iff.2 hY
    let k₀ : A →+* S := IsLocalization.Away.lift d hu
    have hk : ∀ p, k₀ (algebraMap _ A p) = e p := fun p => IsLocalization.Away.lift_eq d hu p
    have hC : ∀ x : K, e (algebraMap K _ x) = φ x := fun x => by simp [e]
    let k : A →ₐ[F] S :=
      { k₀ with
        commutes' := fun r => by
          change k₀ (algebraMap F A r) = _
          rw [IsScalarTower.algebraMap_apply F (MvPolynomial (FrVar m) K) A, hk,
            IsScalarTower.algebraMap_apply F K (MvPolynomial (FrVar m) K), hC, φ.commutes] }
    refine ⟨k, ?_, fun b => ?_, ?_⟩
    · ext x
      exact (hk _).trans (hC x)
    · rw [← heX b]
      ext i j
      exact hk _
    · have h := congrArg k₀ hP
      rw [map_mul, map_pow, hk, hk, hed] at h
      change _ * k₀ t = _
      rw [mul_comm, h, evalFr, MvPolynomial.eval_map]
      rfl

theorem exists_poly_div_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ (P : MvPolynomial (FrVar Dw.mult) K) (N : ℕ), ∀ (S : Type) [CommRing S] [Algebra c.F S] (φ : K →ₐ[c.F] S) (z z' : FrPt Xo c S) (Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)), (∀ b, IsUnit (Y b).det) → FrMap φ y z → FrChg (fun b => (Y b).transpose) 1 z z' → (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y a n F hF
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, hWD, -⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  obtain ⟨A, _, _, π, X, hred, hX, hA⟩ := exists_genericRing c.F K (E →+* ℂ) Dw.mult
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c K A π y
  obtain ⟨u, hu, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A u₀ (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨P, N, hP⟩ := hA (evR Xo c F u)
  refine ⟨P, N, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  obtain ⟨k, hkπ, hkX, hk⟩ := hP S φ Y hY
  obtain ⟨w, hw⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c A S k u₀
  have hw' : FrMap (k.comp π) y w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y u₀ w hu₀ hw
  rw [hkπ] at hw'
  have hwz : w = z := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K S φ y).1 w z hw' hz
  subst hwz
  have hm : FrMap k u z' := by
    refine (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A S k u₀ u w z' _ _ hu hw).2 ?_
    have e : (fun τ => ((X τ).transpose).map k) = fun b => (Y b).transpose :=
      funext fun b => by rw [Matrix.transpose_map, hkX]
    rw [e, Units.val_one, map_one]
    exact hz'
  rw [evR_frMap hWD F hF.1 k u (hT _ u) z' hm]
  exact hk

end GlobalTheory.LamT.RatFn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SecTieEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.SecTransport

section Calc

variable {X X' Y : Scheme.{0}}

theorem exists_sec_back {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB)
    (hL' : L'.IsLB) (s : LB.Sec (L.pull F)) : ∃ σ : LB.Sec L', ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z)
      (J : PUnit → L.ι) (k : L'.ι), r z ∈ (L.pull F).U J → r z ∈ L'.U k →
      gs r z _ (s.f J) = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) := by
  have glue : ∀ k : L'.ι, ∃ a : Γ(X', L'.U k), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J : PUnit → L.ι),
      r z ∈ (L.pull F).U J → r z ∈ L'.U k →
        gs r z _ a = ((gw w r z (J PUnit.unit) k)⁻¹).val * gs r z _ (s.f J) := by
    intro k
    obtain ⟨u, hu⟩ : ∃ u : ∀ J : PUnit → L.ι, Γ(X', (L.pull F).U J ⊓ L'.U k),
        ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J : PUnit → L.ι), r z ∈ (L.pull F).U J ⊓ L'.U k →
          gs r z _ (u J) = ((gw w r z (J PUnit.unit) k)⁻¹).val * gs r z _ (s.f J) :=
      ⟨fun J => (show Γ(X', (L.pull F).U J ⊓ L'.U k) from ((w.s (J, k))⁻¹).val) * resG X' inf_le_left (s.f J),
        fun Z r z J hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val (map_inv _ _))) (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' (fun J : PUnit → L.ι => (L.pull F).U J ⊓ L'.U k) (L'.U k)
      (fun J => homOfLE inf_le_right) (fun y hy => by
        obtain ⟨j, hj⟩ := exists_chart hL (F y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j, mem_pull.2 hj, hy⟩) u
      (fun J J' => fn_ext (V := ((L.pull F).U J ⊓ L'.U k) ⊓ ((L.pull F).U J' ⊓ L'.U k)) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        have hj : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.1.1
        have hj' : F y ∈ L.U (J' PUnit.unit) := mem_pull.1 hy.2.1
        rw [hu _ _ y J hy.1, hu _ _ y J' hy.2, gs_compat s (𝟙 X') y hy.1.1 hy.2.1,
          gm_pull_g L F (𝟙 X') y J J' hy.1.1 hy.2.1,
          hw _ (𝟙 X') y (J PUnit.unit) (J' PUnit.unit) k k hj hj' hy.1.2 hy.1.2, gm_self hL' (𝟙 X') y hy.1.2,
          inv_one, _root_.mul_one, mul_inv_rev, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left])
    refine ⟨a, fun Z r z J h₁ h₂ => ?_⟩
    have hz : r z ∈ (L.pull F).U J ⊓ L'.U k := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_right hz a).symm.trans ((congrArg (gs r z _) (ha J)).trans (hu Z r z J hz))
  choose a ha using glue
  refine ⟨⟨a, fun k k' => fn_ext fun y hy => ?_⟩, fun Z r z J k h₁ h₂ => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart hL (F y)
    have hJ : (𝟙 X' : X' ⟶ X') y ∈ (L.pull F).U (fun _ => j) := mem_pull.2 hj
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy,
      ha k _ (𝟙 X') y (fun _ => j) hJ hy.1, ha k' _ (𝟙 X') y (fun _ => j) hJ hy.2,
      hw _ (𝟙 X') y j j k k' hj hj hy.1 hy.2, gm_self hL (𝟙 X' ≫ F) y hj, _root_.one_mul, mul_inv, inv_inv,
      Units.val_mul, _root_.mul_assoc]
  · show gs r z _ (s.f J) = _ * gs r z _ (a k)
    rw [ha k Z r z J h₁ h₂, Units.mul_inv_cancel_left]

theorem chart_le_preimage' (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (g : X' ⟶ Y) (e : g ≫ φ = F) (J : PUnit → L.ι) :
    (L.pull F).U J ≤ g ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => J PUnit.unit) := fun y hy =>
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ L.U (J PUnit.unit)) e).mpr (mem_pull.1 hy)

def secPullBack (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (g : X' ⟶ Y) (e : g ≫ φ = F)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1))) : LB.Sec (L.pull F) where
  f := fun (J : PUnit → L.ι) => (g.appLE _ _ (chart_le_preimage' L g e J)).hom (s.f (fun _ => J PUnit.unit))
  compat := fun (J J' : PUnit → L.ι) => fn_ext fun y hy => by
    have h₁ := chart_le_preimage' L g e J hy.1
    have h₂ := chart_le_preimage' L g e J' hy.2
    have e₁ : gm (𝟙 X' ≫ g) y _ ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).g
        (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit)) =
        gm ((𝟙 X' ≫ g) ≫ φ) y (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit)) :=
      (gm_linComb L _ _ (𝟙 X' ≫ g) y _ _ h₁ h₂).trans (by rw [Fin.prod_univ_one, zpow_one])
    have eφ : (𝟙 X' ≫ g) ≫ φ = 𝟙 X' ≫ F := by rw [Category.assoc, e]
    rw [eφ] at e₁
    exact (gs_res _ y _ hy _).trans ((gs_appLE g _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 X' ≫ g) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val ((gm_pull_g L F (𝟙 X') y J J' hy.1 hy.2).trans e₁.symm)))
        ((gs_res _ y _ hy _).trans (gs_appLE g _ _ _ (𝟙 _) y hy.2 _)))))))

theorem isoMaps_iff {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (σ : LB.Sec L')
    (s : LB.Sec (L.pull F)) : IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z)
      (J : PUnit → L.ι) (k : L'.ι), r z ∈ (L.pull F).U J → r z ∈ L'.U k →
      gs r z _ (s.f J) = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) := by
  constructor
  · intro H Z r z J k h₁ h₂
    have hz : r z ∈ (L.pull F).U J ⊓ L'.U k := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz _).symm.trans ((congrArg (gs r z _) (H J k)).trans
      ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _) (gs_res r z _ hz _))))
  · intro H J k
    refine fn_ext fun y hy => ?_
    exact (gs_res _ y inf_le_left hy _).trans ((H _ (𝟙 X') y J k hy.1 hy.2).trans
      ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _))).symm)

end Calc


set_option maxHeartbeats 800000 in
theorem secTie_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x), (∀ th, ∃ s : LB.Sec (PPx x), SecTie m th s) ∧ (∀ s : LB.Sec (PPx x), ∃ th, SecTie m th s) ∧ ∀ th (s : LB.Sec (PPx x)), SecTie m th s → (∀ th' (s' : LB.Sec (PPx x)), SecTie m th' s' → ((∀ i, th'.f i = th.f i) ↔ ∀ i, s'.f i = s.f i)) ∧ (SecNZ x s ↔ ∀ p : Sp S, ∃ q : t'.G.left, t'.G.hom q = p ∧ q ∈ Out.nonzeroLocus th) := by
  intro E _ _ _ H Dw l Xo S _ x t' m
  obtain ⟨w, gw1, rw1, -⟩ := m.lin
  have hrig : RigIso m w := ⟨gw1, rw1⟩
  have hw := (isGen_iff w).1 gw1
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  have hG : Out.GlobalFnsSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  haveI hpr : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  have wu : ∀ w', RigIso m w' → w' = w := fun w' h' =>
    iso_unique_of_rig hG t'.G hA hL' hL h'.1 gw1 h'.2 rw1
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  obtain ⟨h, hφ, hh⟩ : ∃ h : Gx x ⟶ t'.G.left, h ≫ m.φ = (snd (Over.mk x) A).left ∧
      h ≫ t'.G.hom = (fst (Over.mk x) A).left :=
    ⟨m.cart.1.lift _ _ cond, m.cart.1.lift_fst _ _ cond, m.cart.1.lift_snd _ _ cond⟩
  obtain ⟨g, gf, gs'⟩ : ∃ g : t'.G.left ⟶ Gx x, g ≫ (fst (Over.mk x) A).left = t'.G.hom ∧
      g ≫ (snd (Over.mk x) A).left = m.φ := by
    let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
    let b0 : Over.mk (t'.G.hom ≫ x) ⟶ A := Over.homMk m.φ m.cart.1.w
    exact ⟨(lift a0 b0).left, congrArg (fun q => q.left) (lift_fst a0 b0), congrArg (fun q => q.left) (lift_snd a0 b0)⟩
  have hgh : g ≫ h = 𝟙 _ := m.cart.1.hom_ext (by rw [Category.assoc, hφ, gs', Category.id_comp])
        (by rw [Category.assoc, hh, gf, Category.id_comp])
  have hhg : h ≫ g = 𝟙 _ := SecCalc.pm_ext _ _ (by rw [Category.assoc, Category.id_comp]; exact (congrArg _ gs').trans hφ)
    (by rw [Category.assoc, Category.id_comp]; exact (congrArg _ gf).trans hh)
  have gu : ∀ g' : t'.G.left ⟶ Gx x, g' ≫ (snd (Over.mk x) A).left = m.φ →
      g' ≫ (fst (Over.mk x) A).left = t'.G.hom → g' = g := fun g' a b =>
    SecCalc.pm_ext _ _ (a.trans gs'.symm) (b.trans gf.symm)

  have tie : ∀ (th : LB.Sec t'.PP.L) (s : LB.Sec (PPx x)), SecTie m th s → ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z)
      (j : Xo.univ.t.PP.L.ι) (k : t'.PP.L.ι), m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t'.PP.L.U k →
      gs (r ≫ g) z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (th.f k) := by
    rintro th s ⟨w', s1, a, b, c⟩ Z r z j k hj hk
    obtain rfl := wu w' a
    have hJ : r z ∈ (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) := mem_pull.2 hj
    refine Eq.trans ?_ ((isoMaps_iff _ th s1).1 b Z r z (fun _ => j) k hJ hk)
    rw [c g gs' gf (fun _ => j) (chart_le_preimage' _ g gs' _)]
    exact (gs_appLE g _ _ _ r z hJ _).symm
  have hmem : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (y : Gx x), y ∈ (PPx x).U i → m.φ (h y) ∈ Xo.univ.t.PP.L.U (i 0) :=
    fun i y hy => mem_pull.1 (chart_le_preimage Xo.univ.t.PP.L h hφ i hy)
  have tie' : ∀ (th : LB.Sec t'.PP.L) (s : LB.Sec (PPx x)), SecTie m th s → ∀ (y : Gx x)
      (i : Fin 1 → Xo.univ.t.PP.L.ι) (k : t'.PP.L.ι), y ∈ (PPx x).U i → h y ∈ t'.PP.L.U k →
      gs (𝟙 (Gx x)) y _ (s.f i) = (gw w h y (i 0) k).val * gs h y _ (th.f k) := by
    intro th s ht y i k hi hk
    obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun a => congrArg i (Subsingleton.elim _ _)⟩
    rw [← hhg]
    exact tie th s ht _ h y j k (hmem _ y hi) hk
  refine ⟨fun th => ?_, fun s => ?_, fun th s ht => ⟨fun th' s' ht' => ⟨fun e i => ?_, fun e k => ?_⟩, ?_, ?_⟩⟩
  · obtain ⟨s1, hs1⟩ := exists_sec_along_iso hw hL hL' th
    refine ⟨secPullOne Xo.univ.t.PP.L h hφ s1, w, s1, hrig, (isoMaps_iff _ _ _).2 hs1, fun g' a b J hJ => ?_⟩
    obtain rfl := gu g' a b
    refine fn_ext fun y hy => Eq.symm ?_
    refine (gs_appLE g' _ _ hJ (𝟙 _) y hy _).trans ?_
    refine (gs_appLE h _ _ (chart_le_preimage _ h hφ _) (𝟙 _ ≫ g') y (hJ hy) _).trans ?_
    rw [Category.assoc, hgh, Category.id_comp]
  · obtain ⟨th, hth⟩ := exists_sec_back hw hL hL' (secPullBack Xo.univ.t.PP.L g gs' s)
    refine ⟨th, w, _, hrig, (isoMaps_iff _ _ _).2 hth, fun g' a b J hJ => ?_⟩
    obtain rfl := gu g' a b
    rfl
  · refine fn_ext fun y hy => ?_
    obtain ⟨k, hk⟩ := exists_chart hL' (h y)
    rw [tie' th s ht y i k hy hk, tie' th' s' ht' y i k hy hk, e k]
  · refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart hL (m.φ y)
    have e₁ := tie th s ht _ (𝟙 _) y j k hj hy
    have e₂ := tie th' s' ht' _ (𝟙 _) y j k hj hy
    exact (Units.mul_right_inj _).1 (e₂.symm.trans ((congrArg (gs _ y _) (e (fun _ => j))).trans e₁))
  · intro hnz p
    obtain ⟨q, i, hq, hi⟩ := hnz p
    have hiU : q ∈ (PPx x).U i := (Gx x).basicOpen_le _ hi
    obtain ⟨k, hk⟩ := exists_chart hL' (h q)
    refine ⟨h q, (congrArg (fun r => r q) hh).trans hq, TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩⟩
    refine (isUnit_gs_iff h q _ hk _).1 ?_
    have hu := (isUnit_gs_iff (𝟙 _) q _ hiU _).2 hi
    rw [tie' th s ht q i k hiU hk] at hu
    exact isUnit_of_mul_isUnit_right hu
  · intro hnz p
    obtain ⟨q, hq, hqn⟩ := hnz p
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hqn
    have hkU : q ∈ t'.PP.L.U k := t'.G.left.basicOpen_le _ hk
    obtain ⟨j, hj⟩ := exists_chart hL (m.φ q)
    have mg : g q ∈ (PPx x).U (fun _ => j) :=
      Set.mem_iInter.2 fun _ => (congrArg (fun r => r q ∈ Xo.univ.t.PP.L.U j) gs').mpr hj
    refine ⟨g q, fun _ => j, (congrArg (fun r => r q) gf).trans hq, ?_⟩
    refine (isUnit_gs_iff g q _ mg _).1 ?_
    have e := tie th s ht _ (𝟙 _) q j k hj hkU
    rw [Category.id_comp] at e
    rw [e]
    exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 _) q _ hkU _).2 hk)

end GlobalTheory.SecTieEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonvaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedSectionCorrespondence_existsUnique_nonvanishing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x), (∀ th, ∃ s : LB.Sec (PPx x), SecTie m th s) ∧ (∀ s : LB.Sec (PPx x), ∃ th, SecTie m th s) ∧ ∀ th (s : LB.Sec (PPx x)), SecTie m th s → (∀ th' (s' : LB.Sec (PPx x)), SecTie m th' s' → ((∀ i, th'.f i = th.f i) ↔ ∀ i, s'.f i = s.f i)) ∧ (SecNZ x s ↔ ∀ p : Sp S, ∃ q : t'.G.left, t'.G.hom q = p ∧ q ∈ Out.nonzeroLocus th) := by
  first | exact @GlobalTheory.SecTieEx.secTie_exists_unique | exact GlobalTheory.SecTieEx.secTie_exists_unique | (intros; apply GlobalTheory.SecTieEx.secTie_exists_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrame
noncomputable section

namespace GlobalTheory.MetricChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

theorem lift_comb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {G' : Over (Sp S)} [GrpObj G']
    {φ : G'.left ⟶ Xo.univ.t.G.left} (hp : IsGrpPullback G' Xo.univ.t.G x φ) :
    (∀ w : epsR S ⟶ G', IsTanAt x (w.left ≫ φ) → IsTangent w) ∧
    ∀ (n : ℕ) (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
      IsCombAt x (fun i => (v i).left ≫ φ) c w → ∃ w' : epsR S ⟶ G', w'.left ≫ φ = w ∧ IsLieComb c v w' := by
  let up : ∀ w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left,
      w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ Xo.univ.t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[Xo.univ.t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEps x ⟶ Xo.univ.t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  refine ⟨fun w h => hp.1.hom_ext ?_ ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  · refine (Category.assoc _ _ _).trans ?_
    rw [Over.w w, Over.w η[G']]
    exact zs
  · rintro n c v w ⟨u, hu, hw⟩
    refine ⟨(List.ofFn fun i => up (u i).left (Over.w _)).prod, (pr _).trans (Eq.trans ?_ hw),
      fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_, rfl⟩
    · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEps x ⟶ Xo.univ.t.G) :=
        funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
      exact (congrArg (fun q : _ → (tEps x ⟶ Xo.univ.t.G) => (List.ofFn q).prod.left) this).symm
    · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
    · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
      exact (spMap_epsScaleR_comp (c i)).symm

def scaleSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} (a : R) (s : LB.Sec L) : LB.Sec L where
  f i := constFn p _ a * s.f i
  compat i j := by
    have h : ∀ (U V : X.Opens) (h : U ≤ V), (X.presheaf.map (homOfLE h).op).hom (constFn p V a) = constFn p U a := by
      intro U V h
      simp only [constFn]
      exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
        (Scheme.Hom.appLE_map p (U := ⊤) (V := V) (fun _ _ => trivial) (homOfLE h).op)
    rw [map_mul, map_mul, h, h, s.compat]
    ring

theorem nonzeroLocus_scaleSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : LB.Sec L) : Out.nonzeroLocus (scaleSec p a s) = Out.nonzeroLocus s := by
  unfold Out.nonzeroLocus
  refine iSup_congr fun k => ?_
  have hu : IsUnit (constFn p (L.U k) a) := (ha.map _).map _
  show X.basicOpen (constFn p _ a * s.f k) = _
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit hu]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem hermForm_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin n → Fin g → ℂ) (c d : Fin n → ℂ) :
    hermForm Hm (∑ l, c l • W l) (∑ j, d j • W j) = ∑ l, ∑ j, star (d j) * hermForm Hm (W l) (W j) * c l := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem metricAt_change {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (x : Sp ℂ ⟶ Xo.X) (s s' : LB.Sec (PPx x))
    (uu uu' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ) (a : ℂ) (ha : a ≠ 0)
    (ht : ∀ b i, IsTanAt x (uu b i)) (hc : ∀ b i, IsCombAt x (uu b) (fun j => Y b j i) (uu' b i))
    (hs : SecBC (RingHom.id ℂ) a x x s s') (h : IsMetricAt x s uu N Gr) :
    IsMetricAt x s' uu' (‖a‖ ^ 2 * N) (fun b => (Y b).conjTranspose * Gr b * Y b) := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨l1, l2⟩ := lift_comb Φ.m.cart
  have hw : ∀ b, uu b = fun i => (w b i).left ≫ Φ.m.φ := fun b => funext fun i => (h7 b i).1.symm
  have hx : ∀ b i, ∃ w' : epsR ℂ ⟶ Φ.T.t.G, w'.left ≫ Φ.m.φ = uu' b i ∧ IsLieComb (fun j => Y b j i) (w b) w' :=
    fun b i => l2 _ _ (w b) _ (hw b ▸ hc b i)
  choose w' hw1 hw2 using hx
  let Φ' : FibKey Xo ℂ x :=
    { Φ with
      th := scaleSec Φ.T.t.G.hom a Φ.th
      th_ne := fun p => by rw [nonzeroLocus_scaleSec _ ha.isUnit]; exact Φ.th_ne p }
  refine ⟨Φ', u, Hm, χ, fun z => a * θ z, Fd, w', fun b i => ∑ j, Y b j i • W b j, ?_, h2, h3, ?_, h5, ?_,
    fun b i => ⟨hw1 b i, ?_⟩, fun b i k => ?_⟩
  · exact ((GlobalTheory.LamT.TieCalc.secTie_calc E H Dw l Xo ℂ x Φ.T.t Φ.m Φ.th s h1).1 a x s' _ rfl hs).2 fun _ => rfl
  · intro i z hz
    refine (valAt'_mul _ _ _ _).trans ?_
    rw [_root_.mul_assoc]
    exact congrArg₂ (· * ·) (valAt'_constFn _ _ (Over.w (u.ex z)) _ a hz) (h4 i z hz)
  · rw [h6, ← mul_div_assoc, ← integral_const_mul]
    congr 2
    funext z
    rw [norm_mul, mul_pow, _root_.mul_assoc]
  · exact (GlobalTheory.T.tangentVector_existsUnique_uniformisingVector Φ.key u).2 _ (w b) (W b) _ (w' b i) (fun j => l1 _ ((h7 b j).1.symm ▸ ht b j))
      (fun j => (h7 b j).2) (hw2 b i)
  · rw [hermForm_sum]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, h8, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isMetric_frChg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y y' : FrPt Xo c (CAt σ)) (N : ℝ) (Gr Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) (a : ℂ), a ≠ 0 → FrChg (S := CAt σ) (fun b => (Y b).transpose) a y y' → IsMetric y N Gr → IsMetric y' (‖a‖ ^ 2 * N) (fun b => (Y b).conjTranspose * Gr b * Y b) := by
  intro E _ _ _ H Dw l Xo c σ y y' N Gr Y a ha ⟨hx, hc, hs⟩ h
  obtain ⟨x', hx', u', t', e', b', s', g'⟩ := y'
  obtain ⟨x, hx0, u, t, e, b, s, g⟩ := y
  obtain rfl : x' = x := hx
  exact metricAt_change x' s s' u u' N Gr Y a ha t hc hs h

end GlobalTheory.MetricChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_change_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y y' : FrPt Xo c (CAt σ)) (N : ℝ) (Gr Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) (a : ℂ), a ≠ 0 → FrChg (S := CAt σ) (fun b => (Y b).transpose) a y y' → IsMetric y N Gr → IsMetric y' (‖a‖ ^ 2 * N) (fun b => (Y b).conjTranspose * Gr b * Y b) := by
  first | exact @GlobalTheory.MetricChange.isMetric_frChg | exact GlobalTheory.MetricChange.isMetric_frChg | (intros; apply GlobalTheory.MetricChange.isMetric_frChg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frChg_tri {S : Type} [CommRing S] [Algebra c.F S] (hS : IsReduced S) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) (t : Ix Dw → Sˣ)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (h0 : ∀ τ i j, i < j → g τ i j = 0)
    (hd : ∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) {y y' : FrPt Xo c S} (h : FrChg g (t none : S) y y') :
    evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y :=
  (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 S hS a n F hF t y y'
    (((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2 ⟨g, h0, hd, h⟩)

theorem evalFr_mul_tri {K : Type} [CommRing K] [Algebra c.F K] {y : FrPt Xo c K} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {G : MvPolynomial (FrVar Dw.mult) K} (hG : IsFrPoly F y G)
    {S : Type} [CommRing S] [Algebra c.F S] (hS : IsReduced S) (φ : K →ₐ[c.F] S)
    (X T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (hX : ∀ b, IsUnit (X b).det)
    (hT : ∀ b, IsUnit (T b).det) (h0 : ∀ τ i j, i < j → T τ j i = 0) (hd : ∀ τ i, IsUnit (T τ i i)) :
    evalFr (MvPolynomial.map φ.toRingHom G) (fun b => X b * T b) =
      (∏ b, ∏ i : Fin (Dw.mult b), T b i i ^ a (b, i)) * evalFr (MvPolynomial.map φ.toRingHom G) X := by
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K S φ y
  obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z1 (fun b => (T b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hT b)
  have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S z z1 z2).2 _ _ _ _ h1 h2
  simp only [Units.val_one, _root_.mul_one, ← Matrix.transpose_mul] at h1 h2 h3
  rw [← hG S φ z z1 X hX hz h1, ← hG S φ z z2 (fun b => X b * T b)
    (fun b => by rw [Matrix.det_mul]; exact (hX b).mul (hT b)) hz h3]
  let t : Ix Dw → Sˣ := fun i => match i with
    | none => 1
    | some p => (hd p.1 p.2).unit
  rw [evR_frChg_tri hS hF t (fun b => (T b).transpose) h0 (fun _ _ => rfl) h2]
  congr 1
  simp [wchar, Fintype.prod_option, Fintype.prod_sigma, t, ex]

end


set_option maxHeartbeats 1000000 in
theorem isFrPoly_equiv_and_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∀ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G → (∀ [DecidableEq (E →+* ℂ)] (σ : K →+* ℂ), IsEquiv (fun b (i : Fin (Dw.mult b)) => a (b, i)) (MvPolynomial.map σ G)) ∧ ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ) (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 → G ≠ 0 := by
  intro E _ _ _ H Dw l Xo c K _ _ y a n F hF G hG
  refine ⟨fun σ X b t hX ht htri => ?_, fun σ σ₁ w hw hne hG0 => hne ?_⟩
  · have hred : IsReduced (CAt (σ.comp (algebraMap c.F K))) := inferInstanceAs (IsReduced ℂ)
    have hdiag : ∀ i, t i i ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri] at ht
      exact fun i => Finset.prod_ne_zero_iff.1 ht i (Finset.mem_univ i)
    let T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := Function.update (fun _ => 1) b t
    have hT : ∀ b', IsUnit (T b').det := by
      intro b'
      by_cases hb : b' = b
      · subst hb; simpa [T] using ht
      · simp [T, Function.update_of_ne hb]
    have h0 : ∀ τ i j, i < j → T τ j i = 0 := by
      intro b' i j hij
      by_cases hb : b' = b
      · subst hb; simpa [T] using htri hij
      · simp [T, Function.update_of_ne hb, Matrix.one_apply_ne hij.ne']
    have hd : ∀ τ i, IsUnit (T τ i i) := by
      intro b' i
      by_cases hb : b' = b
      · subst hb; simpa [T] using hdiag i
      · simp [T, Function.update_of_ne hb]
    have key : evalFr (MvPolynomial.map σ G) (fun b => X b * T b) =
        (∏ b, ∏ i : Fin (Dw.mult b), T b i i ^ a (b, i)) * evalFr (MvPolynomial.map σ G) X :=
      evalFr_mul_tri hF hG hred (embAlg (c := c) σ) X T (fun b' => (Ne.isUnit (hX b') : IsUnit (X b').det)) hT h0 hd
    have e1 : Function.update X b (X b * t) = fun b => X b * T b := by
      funext b'
      by_cases hb : b' = b
      · subst hb; simp [T]
      · simp [T, Function.update_of_ne hb]
    rw [e1, key]
    congr 1
    rw [Finset.prod_eq_single b]
    · simp [T, ReciprocityTheory.MultiplicativeHeights.triChar]
    · intro b' _ hb
      simp [T, Function.update_of_ne hb]
    · simp
  · have hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K _ σ₁ y
    obtain ⟨g, s, hg, hzw⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c _ z w).1 (hw.symm.trans hz.1.symm)
    obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g 1 hg
    obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)
    have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c _ z z1 z2).2 _ _ _ _ h1 h2
    simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
    have e : z2 = w := (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g s hg).unique h3 hzw
    subst e
    have hv := hG _ σ₁ z z1 (fun b => (g b).transpose) (fun b => by rw [Matrix.det_transpose]; exact hg b) hz h1
    let t : Ix Dw → (CAt σ)ˣ := fun i => match i with
      | none => s
      | some _ => 1
    rw [evR_frChg_tri hred hF t (fun _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne)
      (fun τ i => Matrix.one_apply_eq i) h2, hv, hG0]
    simp [evalFr]

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePolynomial_equivariant_and_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∀ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G → (∀ [DecidableEq (E →+* ℂ)] (σ : K →+* ℂ), IsEquiv (fun b (i : Fin (Dw.mult b)) => a (b, i)) (MvPolynomial.map σ G)) ∧ ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ) (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 → G ≠ 0 := by
  first | exact @GlobalTheory.LamT.isFrPoly_equiv_and_ne_zero | exact GlobalTheory.LamT.isFrPoly_equiv_and_ne_zero | (intros; apply GlobalTheory.LamT.isFrPoly_equiv_and_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataNonemptyField
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataNonemptyField
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CM GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem nonempty_fibKey : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → Nonempty (FibKey Xo K x) := by
  intro E _ _ _ H Dw l Xo K _ x hpq
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨U, hU, hg⟩ := exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp K), Nonempty (SABMap t Xo.univ.t x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull x Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨⟨T, rfl, hTg⟩, -⟩ := PAT.exists_of_sabMap E H _ _ x U t (hU ▸ m)
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT T.pol
  obtain ⟨a, -, hu⟩ := hb b
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis T.t.G T.dim
  refine ⟨⟨T, m, ?_, b, KeyPow.exists_mem_nonzeroLocus T.pol b ?_, v, hv⟩⟩
  · rw [hTg, hg]
    exact Nat.mul_pos hpos hpq
  · by_contra hn
    push Not at hn
    exact zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataNonemptyFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalTripleFibreKeyData_nonempty_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → Nonempty (FibKey Xo K x) := by
  first | exact @GlobalTheory.LamT.nonempty_fibKey | exact GlobalTheory.LamT.nonempty_fibKey | (intros; apply GlobalTheory.LamT.nonempty_fibKey <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitIntegralGeneratorPrincipalLocalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitIntegralGeneratorPrincipalLocalModel
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocSec

theorem exists_secTie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x)
    (σ : LB.Sec t.PP.L) : ∃ s : LB.Sec (PPx x), SecTie m σ s := by
  obtain ⟨w, g1, r1, -⟩ := m.lin
  obtain ⟨s1, hs1⟩ := thf_secUp ((isGen_iff w).1 g1) Xo.univ.t.PP.isLB t.PP.isLB σ
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t.G.left := m.cart.1.lift _ _ cond
  have hφ : h ≫ m.φ = (snd (Over.mk x) A).left := m.cart.1.lift_fst _ _ cond
  have hh : h ≫ t.G.hom = (fst (Over.mk x) A).left := m.cart.1.lift_snd _ _ cond
  have uniq : ∀ g : t.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m.φ → g ≫ (fst (Over.mk x) A).left = t.G.hom →
      g ≫ h = 𝟙 _ := fun g e₁ e₂ => m.cart.1.hom_ext (by rw [Category.assoc, hφ, e₁, Category.id_comp])
        (by rw [Category.assoc, hh, e₂, Category.id_comp])
  refine ⟨thfPull1 Xo.univ.t.PP.L h hφ s1, w, s1, ⟨g1, r1⟩,
    (TieCalc.isoMaps_iff w σ s1).2 fun Z r z j k hj hk => hs1 Z r z (fun _ => j) k (mem_pull.2 hj) hk,
    fun g e₁ e₂ (j : PUnit → Xo.univ.t.PP.L.ι) hj => fn_ext fun y hy => ?_⟩
  exact Eq.symm ((gs_appLE g _ _ hj (𝟙 _) y hy _).trans
      ((gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g) y (hj hy) _).trans
        (congrArg (fun q => gs q y _ (s1.f j)) (by rw [Category.id_comp, uniq g e₁ e₂]))))

theorem exists_unit_secInt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → ∃ a : T.Frˣ, ∀ (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (y' : FrPt Xo c T.Fr), FrChg g (a : T.Fr) y y' → SecInt T m1 m2 y'.s := by
  intro E _ _ _ H Dw l Xo c T io G t' x m1 m2
  let _ := io.toAlgebra
  intro y hy
  subst hy
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨θ, hne, -⟩ := KeyOnPol.exists_generator hS G.pol
  obtain ⟨w2, g2, r2, -⟩ := m2.lin
  obtain ⟨hθ, σ, hσ, -, hgen⟩ := SectionBaseChange.generates_and_baseChange hS T.V T.Fr (algebraMap T.V T.Fr) G.pol t'.G
    m2.φ t'.PP.L w2 θ m2.cart.1 t'.PP.isLB g2 hne
  obtain ⟨s, hs⟩ := exists_secTie m1 σ
  obtain ⟨a, ha, -⟩ := y.gen s
  have a0 : a ≠ 0 := by
    rintro rfl
    have z0 : ∀ i, s.f i = scal y.x 0 i * s.f i := fun i => by
      rw [ha i]
      simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, toΓ, map_zero, zero_mul]
    have e0 := (TieCalc.secTie_scale m1 hs 0 z0).1 hs
    have e1 := (TieCalc.secTie_scale m1 hs 1 (fun i => by rw [SecCalc.scal_one', _root_.one_mul])).1 hs
    obtain ⟨b, -, hb⟩ := hgen σ
    exact zero_ne_one ((hb 0 e0).trans (hb 1 e1).symm)
  refine ⟨Units.mk0 a a0, fun g y' hc => ⟨θ, hθ, w2, σ, thfPull G.t.PP.L m2.φ θ, ⟨g2, r2⟩,
    fun (j : PUnit → G.t.PP.L.ι) k => Eq.trans (fn_ext fun p hp => (gs_res _ p _ hp _).trans
      ((gs_appLE m2.φ _ _ _ (𝟙 _) p hp.1 _).trans (gs_appLE m2.φ _ _ _ (𝟙 _) p hp _).symm))
      (hσ j k (inf_le_left.trans (LB.wchart_le G.t.PP.L _ j PUnit.unit))), fun j hj => rfl, ?_⟩⟩
  obtain ⟨hx, -, pm, p₁, p₂, hp⟩ := hc
  refine ((TieCalc.secTie_calc E H Dw l Xo T.Fr y.x t' m1 σ s hs).1 1 y'.x y'.s σ hx ⟨pm, p₁, p₂, fun i h => ?_⟩).2
    ((TieCalc.secTie_scale m1 hs 1 (fun i => by rw [SecCalc.scal_one', _root_.one_mul])).1 hs)
  have e : scal y.x 1 i * s.f i = scal y.x a i * y.s.f i :=
    ((congrArg (· * s.f i) (SecCalc.scal_one' y.x i)).trans (_root_.one_mul _)).trans (ha i)
  exact (congrArg _ e).trans (hp i h)

end GlobalTheory.LamT.LocSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitIntegralGeneratorPrincipalLocalModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_integral_generator_principal_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → ∃ a : T.Frˣ, ∀ (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (y' : FrPt Xo c T.Fr), FrChg g (a : T.Fr) y y' → SecInt T m1 m2 y'.s := by
  first | exact @GlobalTheory.LamT.LocSec.exists_unit_secInt | exact GlobalTheory.LamT.LocSec.exists_unit_secInt | (intros; apply GlobalTheory.LamT.LocSec.exists_unit_secInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ChartCoverFOfSecBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.FrameEval

theorem univFrame_borelPairs : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p A : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (π : p.R →ₐ[c.F] A.R) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ) (u : FrPt Xo c A.R), OpenChart j y₀ → UnivFrame y₀ π X s u → ∃ (B : TRing c.F) (uB uB' : FrPt Xo c B.R) (tB : Ix Dw → (B.R)ˣ) (q q' : A.R →ₐ[c.F] B.R), FrMap q u uB ∧ FrMap q' u uB' ∧ FrBor tB uB uB' ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A.R →ₐ[c.F] T) (z z' : FrPt Xo c T) (t : Ix Dw → Tˣ), FrMap a u z → FrMap a' u z' → FrBor t z z' → ∃ b : B.R →ₐ[c.F] T, b.comp q = a ∧ b.comp q' = a' ∧ ∀ i, b (tB i : B.R) = (t i : T) := _root_.GlobalTheory.Frames.univFrame_borelPairs

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem ChartCover.exists_lift {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) :
    ∃ xF : Sp S ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = w.x ∧ xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  refine ⟨pullback.lift w.x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [w.x_over, spMap_comp_ring]
  rfl

theorem ChartCover.near (hS : Out.SecBaseChangeSt) {R A : Type} [CommRing R] [Algebra c.F R] [CommRing A]
    [Algebra c.F A] {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A} {s : Aˣ} {u : FrPt Xo c A}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (p : Sp S) (hp : xF p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) →
      ∃ (z : FrPt Xo c T) (a : A →ₐ[c.F] T), FrMap lam w z ∧ FrMap a u z := by
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c R j y₀ hj S xF h2 p hp
  refine ⟨g, hg, fun T _ _ lam hl => ?_⟩
  obtain ⟨ψ, hψ⟩ := hT T lam hl
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c S T lam w
  have hx : z.x = spMap ψ.toRingHom ≫ y₀.x := by
    rw [hz.1, ← h1, ← hj.2.1, ← Category.assoc, hψ, Category.assoc]
  obtain ⟨a, ⟨_, ha⟩, _⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c R A y₀ π X s u hu T z ψ hx
  exact ⟨z, a, hz, ha⟩

theorem ChartCover.cls_loc (hS : Out.SecBaseChangeSt) {R : Type} [CommRing R] [Algebra c.F R] {A : TRing c.F}
    {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A.R}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R} {s : (A.R)ˣ} {u : FrPt Xo c A.R}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (m : Ideal S) [hm : m.IsPrime]
    (hp : xF (⟨m, hm⟩ : PrimeSpectrum S) ∈ Set.range j) :
    ∃ cw : A.R →ₐ[c.F] Localization.AtPrime m,
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m u cw ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m A u := _root_.GlobalTheory.Frames.ChartCover.cls_loc (R := R) (A := A) (j := j) (y₀ := y₀) (π := π) (X := X) (s := s) (u := u) (S := S) hS hj hu w xF h1 h2 m hp

end

theorem chartCoverF_of_secBaseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartCoverF Xo c := by
  intro hS E _ _ _ H Dw l Xo c S _ _ w w' hw m hm
  obtain ⟨xF, h1, h2⟩ := ChartCover.exists_lift w
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (⟨m, hm.isPrime⟩ : PrimeSpectrum S))
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨cw, hc, hl⟩ := ChartCover.cls_loc hS hj hu w xF h1 h2 m hp
  obtain ⟨cw', hc', hl'⟩ := ChartCover.cls_loc hS hj hu w' xF (h1.trans hw.symm) h2 m hp
  exact ⟨A, u, cw, cw', GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hu,
    univFrame_borelPairs hS E H Dw l Xo c p A j y₀ π X s u hj hu, hc, hl, hc', hl'⟩

theorem evR_frMap_of_isReduced (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] [_root_.IsReduced K₁] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) : evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
    evalWD_fr (frChartF_of (chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₁ :=
    GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c _ y₁
  have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₂ := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y₁ y₂ hy' hm⟩
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact hWD f hf K₂ _ _ _ _ _ _ y₂ hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y₁ y₂ hT1.choose_spec.choose_spec.choose_spec hm)

theorem evR_frBor (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [_root_.IsReduced S]
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (hf : f ∈ sec Xo c a n) (t : Formalism.L2.Pj.Ix Dw → Sˣ)
    (y y' : FrPt Xo c S) (hb : FrBor t y y') : evR Xo c f y' = wchar (Formalism.L2.Pj.ex Dw a n) t * evR Xo c f y := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hall : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  exact wtAll_of_borChart (borChartF_of_cover (chartCoverF_of_secBaseChange hS E H Dw l Xo c)) (Formalism.L2.Pj.ex Dw a n)
    hf.1 hf.2 S t y y' (hall S y) (hall S y') hb

end GlobalTheory.FrameEval
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmExistsHolds
namespace GlobalTheory.CM

theorem cmExists_holds : GlobalTheory.CM.CMExistsSt :=
  GlobalTheory.CM.ExObj.cmExists GlobalTheory.cmCurve_closed GlobalTheory.cmPoint_closed GlobalTheory.thetaUnifAV_all
    GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 GlobalTheory.homExtension_semiAbelian_dvr_unconditional
    GlobalTheory.kernelFiniteFlat_holds

end GlobalTheory.CM
end
