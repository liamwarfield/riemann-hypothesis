module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.ScaleJet

variable {R : Type} [CommRing R]

theorem res_cst {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem appLE_cst {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U V (fun _ _ => trivial) h)

theorem app_cst {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (a : R) : (f.app U).hom (constFn q U a) = constFn q' (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE, appLE_cst q q' f hf]

def cMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} (a : R) (s : LB.Sec L) : LB.Sec L where
  f i := constFn q _ a * s.f i
  compat i j := by
    rw [map_mul, map_mul, res_cst, res_cst, s.compat, mul_left_comm]

theorem nonzeroLocus_cMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : LB.Sec L) : Out.nonzeroLocus (cMul q a s) = Out.nonzeroLocus s := by
  unfold Out.nonzeroLocus
  refine iSup_congr fun k => ?_
  have hu : IsUnit (constFn q (L.U k) a) := (ha.map _).map _
  show X.basicOpen (constFn q _ a * s.f k) = _
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit hu]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem valR_cMul {A : Type} [CommRing A] {X : Scheme.{0}} (q : X ⟶ Sp R) (φ : R →+* A) (x : Sp A ⟶ X)
    (hx : x ≫ q = spMap φ) (U : X.Opens) (a : R) (f : Γ(X, U)) :
    valR x U (constFn q U a * f) = φ a * valR x U f := by
  unfold valR
  split_ifs with h
  · rw [map_mul, map_mul, appLE_cst q (spMap φ) x hx U ⊤ h]
    congr 1
    have h3 : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop :=
      (Scheme.Hom.app_eq_appLE (spMap φ) (U := ⊤)).symm
    have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
    have h2 := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) h1
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (((spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) = φ a
    rw [h3]
    refine h2.trans ?_
    simp
  · simp

section Twist

variable {A : Over (Sp R)} [GrpObj A] (L : LB A.left)

theorem twist_cMul {T : Over (Sp R)} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b]))
    (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)) (c : R)
    (h : IsTwistPull A L ψ m hm a b α s s') :
    IsTwistPull A L ψ m hm a b α (cMul (T ⊗ A).hom c s) (cMul (T ⊗ A).hom c s') := by
  intro j
  have e := h j
  simp only [cMul]
  erw [RingHom.map_mul, res_cst, e, RingHom.map_mul, app_cst _ _ ψ.left (Over.w ψ), RingHom.map_mul, res_cst]
  exact mul_left_comm _ _ _

end Twist

end GlobalTheory.MBLow.ScaleJet

namespace GlobalTheory.MBLow.ScaleJet

theorem polAVSectionInverseImage_mulConstant {R : Type} [CommRing R] (P : PolAV (Sp R)) (T : Over (Sp R)) (s : P.L.Sec)
    (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (c : R) (h : IsPolAVSectionInverseImage P T s t) :
    IsPolAVSectionInverseImage P T (cMul P.A.hom c s) (cMul (T ⊗ P.A).hom c t) := by
  intro i hi
  have e := h i hi
  simp only [cMul]
  erw [e, RingHom.map_mul, appLE_cst P.A.hom (T ⊗ P.A).hom (snd T P.A).left (Over.w (snd T P.A))]

theorem scale_key : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (C : Type) [Field C] [CharZero C] (x : KeyIn C) (a : C), a ≠ 0 →
    ∃ (th' : x.P.L.Sec) (h' : _), a ^ 8 * (κ C ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ : C) = κ C x ∧
      ∀ (g : ℕ) (hg : x.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp C) ⟶ x.P.A)) (ϑ : I → C) (J : I → Fin g → C),
        ThJet x hg m pt ϑ J → ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ hg m pt (fun i => a * ϑ i)
          (fun i j => a * J i j) := by
  intro κ hκ C _ _ x a ha
  have hne : ∀ s : Sp C, ∃ y : x.P.A.left, x.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus (cMul x.P.A.hom a x.th) := by
    intro s
    rw [nonzeroLocus_cMul _ ha.isUnit]
    exact x.th_ne s
  have hl : ∀ i, IsLieComb ((1 : Matrix (Fin x.P.g) (Fin x.P.g) C) i) x.v (x.v i) := by
    intro i
    have : (1 : Matrix (Fin x.P.g) (Fin x.P.g) C) i = Pi.single i 1 := by
      ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this]
    have := x.P.isAb.comm
    exact (LieComb.lieComb_algebra _ _ _ x.v x.basis.1).2.2.2.1 i
  refine ⟨cMul x.P.A.hom a x.th, hne, ?_, ?_⟩
  · have e := hκ C x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis (cMul x.P.A.hom a x.th) hne x.v x.basis a 1
      (fun i => rfl) hl
    simpa [Matrix.det_one] using e
  · rintro g hg m I pt ϑ J ⟨th, hon, U, t, i₀, c, hU, hi₀, hv⟩
    refine ⟨cMul (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom a th, polAVSectionInverseImage_mulConstant x.P _ x.th th a hon, U,
      fun i => cMul (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom a (t i), i₀, c, fun i => ⟨(hU i).1, ?_⟩, hi₀, fun i j => ?_⟩
    · obtain ⟨α, s₁, h1, h2, h3, h4⟩ := (hU i).2
      exact ⟨α, cMul _ a s₁, h1, h2, twist_cMul _ _ _ _ _ _ _ _ _ _ h3, twist_cMul _ _ _ _ _ _ _ _ _ _ h4⟩
    · have hx : epsLift (x.v (j.cast hg.symm)) ≫ (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom =
          spMap (algebraMap C (DualNumber C)) := Over.w _
      have e := valR_cMul _ _ _ hx _ a ((t i).f fun _ => i₀)
      refine e.trans ?_
      rw [hv i j]
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl] <;> ring

end GlobalTheory.MBLow.ScaleJet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEightStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_scale_section_pow_eight : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (C : Type) [Field C] [CharZero C] (x : KeyIn C) (a : C), a ≠ 0 → ∃ (th' : x.P.L.Sec) (h' : _), a ^ 8 * (κ C ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ : C) = κ C x ∧ ∀ (g : ℕ) (hg : x.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp C) ⟶ x.P.A)) (ϑ : I → C) (J : I → Fin g → C), ThJet x hg m pt ϑ J → ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ hg m pt (fun i => a * ϑ i) (fun i j => a * J i j) := by
  first | exact @GlobalTheory.MBLow.ScaleJet.scale_key | exact GlobalTheory.MBLow.ScaleJet.scale_key | (intros; apply GlobalTheory.MBLow.ScaleJet.scale_key <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianKeyValueAdaptedVectorsFieldIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianKeyValueAdaptedVectorsFieldIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TrAdapt

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R) F'] (e : F ≃+* F')
  (he : ∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x)

include he in
theorem toF_comp : (e : F →+* F').comp (toF R F) = toF R F' :=
  RingHom.ext fun r => by simp [toF, he]


include he in
def rhoE : TE R F' ⟶ TE R F :=
  Over.homMk (spMap (dualMap (e : F →+* F'))) (by
    show spMap (dualMap (e : F →+* F')) ≫ spMap (algebraMap F (DualNumber F)) ≫
        spMap (algebraMap (FractionRing R) F) ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap F' (DualNumber F')) ≫ spMap (algebraMap (FractionRing R) F') ≫
        spMap (algebraMap R (FractionRing R))
    simp only [← spMap_comp']
    apply congrArg spMap
    ext r <;> simp [dualMap, he, TrivSqZeroExt.algebraMap_eq_inl])


include he in
def sigE : TF (R := R) F' ⟶ TF (R := R) F :=
  Over.homMk (spMap (e : F →+* F')) (by
    show spMap (e : F →+* F') ≫ spMap (algebraMap (FractionRing R) F) ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap (FractionRing R) F') ≫ spMap (algebraMap R (FractionRing R))
    simp only [← spMap_comp']
    congr 1
    exact RingHom.ext fun r => by simp [he])

theorem rhoE_left : (rhoE e he).left = spMap (dualMap (e : F →+* F')) := rfl

theorem sigE_left : (sigE e he).left = spMap (e : F →+* F') := rfl

theorem red_comm : (sigE e he).left ≫ redE F = redE F' ≫ (rhoE e he).left := by
  rw [sigE_left, rhoE_left]
  show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [← spMap_comp', ← spMap_comp']
  congr 1
  exact RingHom.ext fun z => by simp [dualMap]

include he in
theorem bKey_map (κ : Rule) (hκ : Funct κ) [CharZero F] [CharZero F'] (D : DegPre R) {N : NumD F} (ν : NumOf D F N)
    {N' : NumD F'} (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N') (hh : ∀ x, I.h x = 1) (hl : I.lam = 1)
    (hth : ν'.th = ν.th) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (k : F) (hk : BKey κ ν vB k) :
    BKey κ ν' vB (e k) := by
  refine ⟨fun h0 => ?_, fun hg hr th hth' hv x' hres hpb => ?_⟩
  · have h1 := I.th_eq 1
    rw [map_one, hh, hl] at h1
    rw [h1, Units.val_mul, Units.val_one, _root_.one_mul, _root_.one_mul, ← map_pow, RingEquiv.coe_toRingHom, ← map_mul, hk.1 h0,
      map_one]
  · obtain ⟨x, hx⟩ := GlobalTheory.KeyPow.exists_keyPB x' (e.symm : F' →+* F)
    have hc : (e.symm : F' →+* F).comp ((algebraMap (FractionRing R) F').comp (algebraMap R (FractionRing R))) =
        (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) :=
      RingHom.ext fun r => by simp [← he]
    have hpb' := GlobalTheory.keyPB_trans _ _ _ _ x' x _ _ hpb hx
    rw [hc] at hpb'
    have hkx := hk.2 hg hr th hth' hv x (by rw [← hth]; exact hres) hpb'
    have hf := hκ F' F (e.symm : F' →+* F) x' x hx
    rw [hkx] at hf
    rw [hf]
    simp

include he in
theorem adapted_map [CharZero F] [CharZero F'] (D : DegPre R) {N : NumD F} (ν : NumOf D F N)
    {N' : NumD F'} (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N') (heX : ∀ χ, ν'.eX (I.e χ) = ν.eX χ)
    (hpull : ∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' →
      ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J))
    (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
    (gm : Fin g → GtPt D (TE R F)) (had : Adapted ν vB bX σ gm) :
    ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧
      Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  obtain ⟨hv, hz, hb, ht⟩ := had
  choose gm' hgm' using fun j => GlobalTheory.ConstLie.exists_isPullGt (rhoE e he) (gm j)
  have hzT : rhoE e he ≫ DegPre.zeroT D (TE R F) = DegPre.zeroT D (TE R F') := by
    simp only [DegPre.zeroT, ← Category.assoc, comp_toUnit]
  have hzF : sigE e he ≫ DegPre.zeroF D F = DegPre.zeroF D F' := by
    simp only [DegPre.zeroF, ← Category.assoc, comp_toUnit]
  refine ⟨gm', hgm', hv, fun j => ?_, fun i => ?_, fun l => ⟨?_, fun χ => ?_⟩⟩
  · obtain ⟨o, ho, hpo⟩ := hz j
    obtain ⟨o', ho'⟩ := GlobalTheory.ConstLie.exists_isPullGt (sigE e he)
      (⟨o.b, o.s, o.isGen, o.s_zero, o.mult⟩ : GtPt D (TF (R := R) F))
    refine ⟨⟨o'.b, o'.s, o'.isGen, o'.s_zero, o'.mult⟩, ⟨?_, fun χ => ?_⟩, ?_, fun χ => ?_⟩
    · exact Over.OverMorphism.ext (ho'.1.trans ((congrArg (fun q => (sigE e he).left ≫ q.left) ho.1).trans
        (congrArg Over.Hom.left hzF)))
    · refine corr_of_val D.P.isLB fun y J hJ => ?_
      exact ((val_corr hJ (ho'.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (ho.2 χ) _).trans
        (val_one _)))).trans (val_one _).symm
    · refine ho'.1.trans ((congrArg ((sigE e he).left ≫ ·) hpo.1).trans ?_)
      rw [← Category.assoc, red_comm, Category.assoc, ← (hgm' j).1]
    · refine corr_of_val D.P.isLB fun y J hJ => ?_
      refine ((val_corr hJ (ho'.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (hpo.2 χ) _).trans
        (val_pull hJ _ _ _)))).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans ((val_corr hJ ((hgm' j).2 χ) _).trans
        (val_pull hJ _ _ _))).symm)
      rw [Category.id_comp, Category.id_comp, red_comm]
  · refine (hgm' _).1.trans ?_
    rw [hb i, ← Category.assoc, rhoE_left, ← spMap_comp', dualMap_comp, toF_comp e he]
  · exact Over.OverMorphism.ext ((hgm' _).1.trans ((congrArg (fun q => (rhoE e he).left ≫ q.left) (ht l).1).trans
      (congrArg Over.Hom.left hzT)))
  · obtain ⟨χ₀, rfl⟩ := I.e.surjective χ
    rw [heX, hpull _ _ (hgm' _), (ht l).2 χ₀, Module.Basis.map_repr]
    simp [dualMap]

end GlobalTheory.MBLow.TrAdapt

theorem GlobalTheory.MBLow.bKey_adapted_map : ∀ κ : Rule, Funct κ → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [CharZero F] [CharZero F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N) (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), (∀ x, I.h x = 1) → I.lam = 1 → (∀ χ, ν'.eX (I.e χ) = ν.eX χ) → ν'.th = ν.th → (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) → ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ k, BKey κ ν vB k → BKey κ ν' vB (e k)) ∧ ∀ (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧ Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  intro κ hκ R _ _ D F F' _ _ _ _ _ _ e he N ν N' ν' I hh hl heX hth hpull vB
  exact ⟨fun k hk => GlobalTheory.MBLow.TrAdapt.bKey_map e he κ hκ D ν ν' I hh hl hth vB k hk,
    fun r g bX σ gm had => GlobalTheory.MBLow.TrAdapt.adapted_map e he D ν ν' I heX hpull vB r g bX σ gm had⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianKeyValueAdaptedVectorsFieldIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianKeyValue_adaptedVectors_fieldIso : ∀ κ : Rule, Funct κ → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [CharZero F] [CharZero F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N) (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), (∀ x, I.h x = 1) → I.lam = 1 → (∀ χ, ν'.eX (I.e χ) = ν.eX χ) → ν'.th = ν.th → (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) → ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ k, BKey κ ν vB k → BKey κ ν' vB (e k)) ∧ ∀ (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧ Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  exact @GlobalTheory.MBLow.bKey_adapted_map
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHeisenbergTranslatesBaseVectorEqCardSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHeisenbergTranslatesBaseVectorEqCardSmul
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeisTranslSum

theorem isHalf_add' {D : D7} {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u + v) := fun i j => by
  rw [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_sub' {D : D7} {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u - v) := fun i j => by
  rw [Matrix.sub_apply, mul_sub, hu i j, hv i j]

theorem half_duality {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {Q : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e Q)
    (x : WO S T) (hx : IsHalf e x) :
    (∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT := by
  obtain ⟨hd, -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  have hmul : ∀ P ∈ Q, e * es P = es P := by
    intro P hP
    rw [hsum, Finset.sum_mul, Finset.sum_eq_single_of_mem P hP]
    · exact (hes P hP).1.1
    · intro R hR hne
      exact GlobalTheory.Tow.idemAt_orth (hes R hR) (hes P hP) hne
  have he1 : e * e = e := by
    conv_lhs => rhs; rw [hsum]
    rw [Finset.mul_sum, Finset.sum_congr rfl hmul, ← hsum]
  have hc1 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he1]
  have hinf : infPart D e = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun P hP => GlobalTheory.SplitScalar.infPart_splitIdem (hes P hP).1
  have hfin : x.map (infPart D) = 0 := by
    ext i j
    show infPart D (x i j) = 0
    rw [← hx i j, RingHom.map_mul, hinf, zero_mul]
  refine ⟨fun h => (hd x hfin).2 fun u hu => ?_, fun h y hy _ => (hd x hfin).1 h y hy⟩
  have hst : cA D e • u ∈ latAll S T ΛS ΛT :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc1])) u hu
  have := h _ hst (GlobalTheory.SplitScalar.isHalf_smul hc1 u)
  rwa [← GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx] at this

theorem sum_heisO_base_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ z : GA D S, (∀ t : WO S T, IsHalf e t → actO S T z⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT) → ∀ Rr : Finset (WO S T), (∀ u ∈ Rr, actO S T z⁻¹ 1 u ∈ latAll S T ΛS ΛT ∧ IsHalf (cA D e) u) → (∀ w, actO S T z⁻¹ 1 w ∈ latAll S T ΛS ΛT → IsHalf (cA D e) w → ∃! v, v ∈ Rr ∧ w - v ∈ latAll S T ΛS ΛT) → (∀ w ∈ latAll S T ΛS ΛT, IsHalf (cA D e) w → actO S T z⁻¹ 1 w ∈ latAll S T ΛS ΛT) → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm → ∑ u ∈ Rr, heisO ψ S T u f₀ = (Rr.card : ℂ) • Tm (actPull (z, (1 : GA D T)) (halfInd e (latAll S T ΛS ΛT))) := by
  intro D ψ hψ S T ΛS ΛT hS hT Q e he z hz Rr hRr huniq hlat f₀ Tm hM
  have hB := half_duality hψ hS hT he
  have hSB := GlobalTheory.isSBHalf_halfInd e (latAll S T ΛS ΛT)
  have hvac : Tm (halfInd e (latAll S T ΛS ΛT)) = f₀ := by simpa using hM.vac
  have h1 : ∀ u ∈ Rr, heisO ψ S T u f₀ =
      Tm (fun t => ψ (symplO S T t u) * halfInd e (latAll S T ΛS ΛT) t) := by
    intro u hu
    rw [← hvac, hM.modul _ hSB u (hRr u hu).2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl h1, ← map_sum, ← map_smul]
  congr 1
  funext t
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_mul]
  simp only [actPull, inv_one]
  set Λ := latAll S T ΛS ΛT with hΛ
  set x := actO S T z⁻¹ 1 t with hx
  by_cases hte : IsHalf e t
  · have hxe : IsHalf e x := (Formalism.IndefR.Fin.LevelGroupLemmas.isHalf_actO z⁻¹ 1 t).2 hte
    by_cases hxΛ : x ∈ Λ
    · have htΛ : t ∈ Λ := hz t hte hxΛ
      have ht1 : halfInd e Λ t = 1 := by simp only [halfInd]; rw [if_pos ⟨htΛ, hte⟩]
      have hx1 : halfInd e Λ x = 1 := by simp only [halfInd]; rw [if_pos ⟨hxΛ, hxe⟩]
      rw [ht1, hx1, mul_one, mul_one]
      have : ∀ u ∈ Rr, ψ (symplO S T t u) = 1 := by
        intro u hu
        rw [← GlobalTheory.SplitHecke.symplO_actO S T z⁻¹ 1 t u]
        exact (hB x hxe).2 hxΛ _ (hRr u hu).1
          ((Formalism.IndefR.Fin.LevelGroupLemmas.isHalf_actO z⁻¹ 1 u).2 (hRr u hu).2)
      rw [Finset.sum_congr rfl this]
      simp
    · have hx0 : halfInd e Λ x = 0 := by
        simp only [halfInd]; rw [if_neg fun h => hxΛ h.1]
      rw [hx0, mul_zero]
      by_cases htΛ : t ∈ Λ
      · have ht1 : halfInd e Λ t = 1 := by simp only [halfInd]; rw [if_pos ⟨htΛ, hte⟩]
        rw [ht1, mul_one]
        have hchar : ∀ w ∈ Λ, IsHalf (cA D e) w → ψ (symplO S T t w) = 1 := (hB t hte).2 htΛ
        have hnot : ¬ ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1 := fun h => hxΛ ((hB x hxe).1 h)
        push Not at hnot
        obtain ⟨y, hyΛ, hyH, hyψ⟩ := hnot
        set u₀ := actO S T z 1 y with hu₀
        have hy0 : actO S T z⁻¹ 1 u₀ = y := by
          have := GlobalTheory.SplitHecke.actO_inv_actO (S := S) (T := T) z 1 y
          rwa [inv_one] at this
        have hu₀H : IsHalf (cA D e) u₀ := (Formalism.IndefR.Fin.LevelGroupLemmas.isHalf_actO z 1 y).2 hyH
        have hψu₀ : ψ (symplO S T t u₀) ≠ 1 := by
          rw [← GlobalTheory.SplitHecke.symplO_actO S T z⁻¹ 1 t u₀, hy0]; exact hyψ
        have hact_add : ∀ a b : WO S T, actO S T z⁻¹ 1 (a + b) = actO S T z⁻¹ 1 a + actO S T z⁻¹ 1 b :=
          fun a b => map_add (GlobalTheory.SplitHecke.actAdd S T z⁻¹ 1) a b
        have hact_sub : ∀ a b : WO S T, actO S T z⁻¹ 1 (a - b) = actO S T z⁻¹ 1 a - actO S T z⁻¹ 1 b :=
          fun a b => map_sub (GlobalTheory.SplitHecke.actAdd S T z⁻¹ 1) a b
        have hshift : ∀ u ∈ Rr, actO S T z⁻¹ 1 (u + u₀) ∈ Λ ∧ IsHalf (cA D e) (u + u₀) := fun u hu =>
          ⟨by rw [hact_add, hy0]; exact Λ.add_mem (hRr u hu).1 hyΛ, isHalf_add' (hRr u hu).2 hu₀H⟩
        let rep : ∀ u ∈ Rr, WO S T := fun u hu =>
          ((huniq (u + u₀) (hshift u hu).1 (hshift u hu).2).exists).choose
        have hrep : ∀ u (hu : u ∈ Rr), rep u hu ∈ Rr ∧ (u + u₀) - rep u hu ∈ Λ := fun u hu =>
          ((huniq (u + u₀) (hshift u hu).1 (hshift u hu).2).exists).choose_spec
        have hsum : (∑ u ∈ Rr, ψ (symplO S T t u)) * ψ (symplO S T t u₀) = ∑ u ∈ Rr, ψ (symplO S T t u) := by
          rw [Finset.sum_mul]
          refine Finset.sum_bij rep (fun u hu => (hrep u hu).1) ?_ ?_ ?_
          · intro a₁ ha₁ a₂ ha₂ heq
            have hd : a₁ - a₂ ∈ Λ := by
              have := Λ.sub_mem (hrep a₁ ha₁).2 (hrep a₂ ha₂).2
              rw [heq] at this
              convert this using 1; abel
            exact (huniq a₁ (hRr a₁ ha₁).1 (hRr a₁ ha₁).2).unique ⟨ha₁, by simp⟩ ⟨ha₂, hd⟩
          · intro b hb
            have hw1 : actO S T z⁻¹ 1 (b - u₀) ∈ Λ := by
              rw [hact_sub, hy0]; exact Λ.sub_mem (hRr b hb).1 hyΛ
            have hw2 : IsHalf (cA D e) (b - u₀) := isHalf_sub' (hRr b hb).2 hu₀H
            obtain ⟨a, ha, hwa⟩ := (huniq (b - u₀) hw1 hw2).exists
            refine ⟨a, ha, ?_⟩
            refine (huniq (a + u₀) (hshift a ha).1 (hshift a ha).2).unique (hrep a ha) ⟨hb, ?_⟩
            have := Λ.neg_mem hwa
            convert this using 1; abel
          · intro u hu
            have hdiff := (hrep u hu).2
            have hH : IsHalf (cA D e) ((u + u₀) - rep u hu) :=
              isHalf_sub' (isHalf_add' (hRr u hu).2 hu₀H) (hRr _ (hrep u hu).1).2
            rw [← AddChar.map_add_eq_mul, ← GlobalTheory.LatVac.symplO_add_right]
            have hsplit : u + u₀ = rep u hu + ((u + u₀) - rep u hu) := by abel
            rw [hsplit, GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul, hchar _ hdiff hH, mul_one]
        have hzero : (∑ u ∈ Rr, ψ (symplO S T t u)) * (ψ (symplO S T t u₀) - 1) = 0 := by
          rw [mul_sub, hsum, mul_one, sub_self]
        rcases mul_eq_zero.1 hzero with h | h
        · exact h
        · exact absurd (sub_eq_zero.1 h) hψu₀
      · have ht0 : halfInd e Λ t = 0 := by simp only [halfInd]; rw [if_neg fun h => htΛ h.1]
        rw [ht0, mul_zero]
  · have hxe : ¬ IsHalf e x := fun h => hte ((Formalism.IndefR.Fin.LevelGroupLemmas.isHalf_actO z⁻¹ 1 t).1 h)
    have ht0 : halfInd e Λ t = 0 := by simp only [halfInd]; rw [if_neg fun h => hte h.2]
    have hx0 : halfInd e Λ x = 0 := by simp only [halfInd]; rw [if_neg fun h => hxe h.2]
    rw [ht0, hx0, mul_zero, mul_zero]

end GlobalTheory.HeisTranslSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHeisenbergTranslatesBaseVectorEqCardSmulStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_heisenbergTranslates_baseVector_eq_card_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ z : GA D S, (∀ t : WO S T, IsHalf e t → actO S T z⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT) → ∀ Rr : Finset (WO S T), (∀ u ∈ Rr, actO S T z⁻¹ 1 u ∈ latAll S T ΛS ΛT ∧ IsHalf (cA D e) u) → (∀ w, actO S T z⁻¹ 1 w ∈ latAll S T ΛS ΛT → IsHalf (cA D e) w → ∃! v, v ∈ Rr ∧ w - v ∈ latAll S T ΛS ΛT) → (∀ w ∈ latAll S T ΛS ΛT, IsHalf (cA D e) w → actO S T z⁻¹ 1 w ∈ latAll S T ΛS ΛT) → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm → ∑ u ∈ Rr, heisO ψ S T u f₀ = (Rr.card : ℂ) • Tm (actPull (z, (1 : GA D T)) (halfInd e (latAll S T ΛS ΛT))) := by
  first | exact @GlobalTheory.HeisTranslSum.sum_heisO_base_eq | exact GlobalTheory.HeisTranslSum.sum_heisO_base_eq | (intros; apply GlobalTheory.HeisTranslSum.sum_heisO_base_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictToBase
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BaseRestrict

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev baseA (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) : FamIn D.what₂.LL G Pl0 Unit D.R.m := A.comap (fun _ : Unit => A.μ0) ()

def baseF (F : Face D A) : Face D (baseA A) where
  P0 := F.P0
  ψ0 := F.ψ0
  P1 := F.P1
  ψ1 := F.ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def baseR (R : RealDat D A Ks) : RealDat D (baseA A) Ks :=
  R.comap (fun _ : Unit => A.μ0) () (fun _ => ()) R.twPl R.FW R.kap (fun i _ => R.lam i A.μ0) R.err0

variable {R : RealDat D A Ks}

set_option maxHeartbeats 2000000 in
theorem core_base {F : Face D A} (h : GlobalTheory.Hk3.Core R F) : GlobalTheory.Hk3.Core (baseR R) (baseF F) := by
  obtain ⟨hlev, hgrp, hfam, hmod, hch, hth⟩ := h
  refine ⟨LevCh.comap_is hlev (f := fun _ : Unit => A.μ0) (fun _ _ _ => rfl) rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ q => hgrp.red_R A.μ0 q, fun i _ q => hgrp.red_L i A.μ0 q, hgrp.levels, hgrp.record, hgrp.chiW⟩
  · obtain ⟨g, c0R, c0L, ht⟩ := hfam.tie
    exact ⟨⟨g, c0R, c0L, ht.comap (fun _ : Unit => A.μ0) ()⟩, hfam.Sb, fun _ PP => hfam.roots A.μ0 PP, hfam.pl_onto,
      fun _ P => hfam.degR A.μ0 P, fun i _ P => hfam.degL i A.μ0 P, fun i _ P hP => hfam.muVal i A.μ0 P hP,
      fun P hP => hfam.etaVal P hP⟩
  · exact ⟨hmod.inf, hmod.vpos, hmod.cX, hmod.cV, hmod.prX, fun _ => hmod.HX A.μ0, fun i _ => hmod.HV i A.μ0, hmod.HE, hmod.HW,
      hmod.gE, hmod.gW, fun _ x => hmod.jX A.μ0 x, fun i _ x => hmod.jV i A.μ0 x, fun _ j h2 => hmod.νY A.μ0 j h2,
      fun _ => hmod.νY' A.μ0, hmod.ν0, fun _ => hmod.νX A.μ0, fun i _ => hmod.νV i A.μ0, hmod.νW, hmod.BV, hmod.order⟩
  · exact ⟨fun _ k hk => hch.ωY A.μ0 k hk, fun _ => hch.ωX A.μ0, fun _ k hk => hch.vY A.μ0 k hk, fun _ => hch.vX A.μ0,
      fun _ k hk P => hch.ptY A.μ0 k hk P, fun _ P => hch.ptX A.μ0 P, fun _ k hk => hch.ItY A.μ0 k hk, fun _ => hch.ItX A.μ0,
      fun _ => hch.ioY A.μ0, fun _ => hch.ioX A.μ0, fun _ => hch.Th A.μ0⟩
  · exact ⟨fun i _ => hth.ωP i A.μ0, fun i _ => hth.vP i A.μ0, fun i _ P => hth.pt_theta i A.μ0 P, fun i _ => hth.ioP i A.μ0,
      fun i _ => hth.thF_mem i A.μ0, fun i _ => hth.thF i A.μ0, fun i _ => hth.thG i A.μ0⟩

theorem ioExt_base (h : IoExt R) : IoExt (baseR R) := h

theorem qGuard_base (h : QGuard R) : QGuard (baseR R) := ⟨fun _ => h.1 A.μ0, fun _ => h.2 A.μ0⟩

theorem baseOf_base {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} (h : BaseOf R j B) : BaseOf (baseR R) j B :=
  ⟨h.ψ, h.θ, h.sT, h.BS, h.BT, h.ΛS, h.ΛT, h.βS, h.βT, h.vac, h.Pg, h.mu0, h.eta, h.lam, h.delta, h.p, h.q, h.c⟩

theorem twLev_base {χ : Formalism.L2.Host.HChar D.host.E} {xi : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)}
    {xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (h : TwConj.TwLev R χ xi Q xiR) : TwConj.TwLev (baseR R) χ xi Q xiR :=
  ⟨h.xi, h.xi_fin, h.xi_triv, h.xi_tame, h.Q_pl, h.Q_off,
    fun p hp => (h.Q_de p hp).imp fun _ h' => ⟨fun _ => h'.1 A.μ0, h'.2⟩,
    h.Q_ram, h.xiR, h.roots, h.muVal, h.half, h.guard⟩

end Any

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}


set_option maxHeartbeats 2000000 in
def fwBase (t : FWTie T R κ v₀) : FWTie T (baseR R) κ v₀ where
  alg_eq := t.alg_eq
  e := t.e
  ks := t.ks
  kap := t.kap
  pt := t.pt
  nrm_eq := t.nrm_eq
  laws := t.laws
  chiR := t.chiR
  hv₀ := t.hv₀
  x0 := t.x0
  ev0 := t.ev0
  ev := t.ev


set_option maxHeartbeats 2000000 in
def omBase {i : Fin D.R.m} (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) :
    OMDat T.toCore (baseR R) i Unit (fun _ => (baseA A).μ0) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := O.dδ
  Cl' := O.Cl'
  fCl := O.fCl
  bad := O.bad
  Lh := O.Lh
  La := O.La
  Nc := O.Nc
  gam := O.gam
  vol := O.vol
  ep := O.ep
  B := O.B
  epF := O.epF
  io := O.io
  hw := O.hw
  φ := O.φ
  w := O.w
  U₂ := O.U₂
  dict₂ := O.dict₂
  xi := O.xi
  thAd := O.thAd
  Plc := O.Plc

variable {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}

set_option maxHeartbeats 4000000 in
theorem omPins_base {i : Fin D.R.m} (h : OMPins T R κ v₀ O i) : OMPins T (baseR R) κ v₀ (fun i => omBase (O i)) i := by
  have hP := h.2
  have h1 := hP.lift
  have h2 := hP.tuple
  refine ⟨h.1, ⟨h1.field, h1.std, h1.v0, ?_, h1.lev⟩,
    fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    hP.act, hP.bad, hP.reps, hP.ep, hP.io, hP.w, hP.cov, hP.cxi, hP.model₂⟩
  obtain ⟨g, c, c', h3, h4⟩ := h1.c0
  exact ⟨g, c, c', h3.comap (fun _ : Unit => A.μ0) (), h4⟩

set_option maxHeartbeats 4000000 in
theorem oneMapOf_base {i : Fin D.R.m} (cc ph) :
    (omBase (O i)).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph ↔ (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem phaseTie_base {ph : Fin D.R.m → ℂ} {i : Fin D.R.m} (h : PhaseTie T R κ v₀ O ph i) :
    PhaseTie T (baseR R) κ v₀ (fun i => omBase (O i)) ph i :=
  fun ⟨cc, p, h'⟩ => (oneMapOf_base _ _).2 (h ⟨cc, p, (oneMapOf_base _ _).1 h'⟩)

set_option maxHeartbeats 4000000 in
theorem ext_base (j : Fin D.R.m) : TwConj.Ext T R κ v₀ O j (baseR R) v₀ (fun i => omBase (O i)) :=
  ⟨fun _ h => ⟨h.core, h.host, h.curve, h.split, h.chi⟩, fun _ _ _ _ h => h, fun c u hc hu => ⟨c, u, hc, hu, fun _ => rfl⟩⟩


set_option maxHeartbeats 2000000 in
theorem restrict_to_base : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∃ (A0 : FamIn D.what₂.LL G Pl0 Unit D.R.m) (R0 : RealDat D A0 T.Q.c.F) (F0 : Face D A0)
      (v0 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R0.MW i σ).Vec) (O0 : ∀ i, OMDat T.toCore R0 i Unit (fun _ => A0.μ0)),
      GlobalTheory.BigOn.Exp.TwConj.Laws T R0 F0 κ v0 O0 ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R0 v0 O0 ∧ (∀ t, R0.xiH t = 1) ∧
      ∀ (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E)) (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
        GlobalTheory.BigOn.Exp.TwConj.TwLev R χ xi Q xiR → GlobalTheory.BigOn.Exp.TwConj.TwLev R0 χ xi Q xiR := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B h
  obtain ⟨h1, -, ⟨h3⟩, h4, h5, h6, h7, h8⟩ := h
  exact ⟨baseA A, baseR R, baseF F, v₀, fun i => omBase (O i),
    ⟨core_base h1, inferInstance, ⟨fwBase h3⟩, ioExt_base h4, qGuard_base h5, omPins_base h6, phaseTie_base h7, baseOf_base h8⟩,
    ext_base j, fun _ => h1.lev.xi_base, fun _ _ _ _ h => twLev_base h⟩

end GlobalTheory.BaseRestrict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProof
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.BasicNotions MvPolynomial
open scoped Matrix

namespace GlobalTheory.NabBC

variable {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K]

theorem mem_localization_of_mem' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {L : Submodule R W} {x : W} (h : x ∈ L) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L :=
  show ∃ s ∈ p.primeCompl, s • x ∈ L from ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact h⟩

abbrev vmap {n : ℕ} (f : K₀ →+* K) (x : Fin n → K₀) : Fin n → K := fun a => f (x a)

theorem vmap_add {n : ℕ} (f : K₀ →+* K) (x y : Fin n → K₀) : vmap f (x + y) = vmap f x + vmap f y := by
  funext a; simp [vmap]

theorem vmap_smul {n : ℕ} (f : K₀ →+* K) (r : 𝓞 K₀) (x : Fin n → K₀) :
    vmap f (r • x) = RingOfIntegers.mapRingHom f r • vmap f x := by
  funext a
  change f ((r : K₀) * x a) = ((RingOfIntegers.mapRingHom f r : 𝓞 K) : K) * f (x a)
  rw [map_mul]
  rfl

theorem span_image_span {n : ℕ} (f : K₀ →+* K) (S : Set (Fin n → K₀)) :
    Submodule.span (𝓞 K) (vmap f '' (Submodule.span (𝓞 K₀) S : Set (Fin n → K₀))) =
      Submodule.span (𝓞 K) (vmap f '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      have : vmap f (0 : Fin n → K₀) = 0 := by funext a; simp [vmap]
      rw [this]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [vmap_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [vmap_smul]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem localization_span_image_le {n : ℕ} (f : K₀ →+* K) (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    {A B : Submodule (𝓞 K₀) (Fin n → K₀)} (h : A ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀)))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀)))) := by
  have key : Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀)))) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨t, ht, hta⟩ := h ha
    exact show ∃ s ∈ w.asIdeal.primeCompl, s • vmap f a ∈ _ from
      ⟨RingOfIntegers.mapRingHom f t, hw t ht, by rw [← vmap_smul]; exact Submodule.subset_span ⟨_, hta, rfl⟩⟩
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := key hsx
  exact show ∃ u ∈ w.asIdeal.primeCompl, u • x ∈ _ from
    ⟨t * s, Submonoid.mul_mem _ ht hs, by rw [mul_smul]; exact htx⟩

theorem span_vmap_colLat {n : ℕ} (f : K₀ →+* K) (C : GL (Fin n) K₀) :
    Submodule.span (𝓞 K) (vmap f '' (colLat C : Set (Fin n → K₀))) = colLat (Formalism.UG.bc f C) := by
  unfold colLat
  rw [span_image_span, ← Set.range_comp]
  congr 1

theorem isBasisAt_span_vmap {n : ℕ} (f : K₀ →+* K) (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    {L : Submodule (𝓞 K₀) (Fin n → K₀)} {C : GL (Fin n) K₀} (hC : IsBasisAt w₀ L C) :
    IsBasisAt w (Submodule.span (𝓞 K) (vmap f '' (L : Set (Fin n → K₀)))) (Formalism.UG.bc f C) := by
  unfold IsBasisAt at hC ⊢
  rw [← span_vmap_colLat]
  have h1 : L ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (colLat C) := hC ▸ fun x hx => mem_localization_of_mem' _ hx
  have h2 : colLat C ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal L := hC.symm ▸ fun x hx => mem_localization_of_mem' _ hx
  exact le_antisymm (localization_span_image_le f w₀ w hw h1) (localization_span_image_le f w₀ w hw h2)

theorem tauLat_comp {E ι : Type} [Field E] [NumberField E] {n : ℕ} (f : K₀ →+* K) (emb : ι → E →+* K₀) (τ : ι)
    (M : Submodule (𝓞 E) (Fin n → E)) :
    tauLat (fun τ => f.comp (emb τ)) τ M = Submodule.span (𝓞 K) (vmap f '' (tauLat emb τ M : Set (Fin n → K₀))) := by
  unfold tauLat
  rw [span_image_span, Set.image_image]
  rfl

theorem invTr_bc {n : ℕ} (f : K₀ →+* K) (C : GL (Fin n) K₀) :
    inside₂ K n (Formalism.UG.bc f C) = Formalism.UG.bc f (inside₂ K₀ n C) := by
  apply Units.ext
  change (((Formalism.UG.bc f C)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
    ((Formalism.UG.bc f (inside₂ K₀ n C) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [← map_inv, bc_coe, bc_coe, ← Matrix.transpose_map]
  rfl

theorem isBasisAt_dualFr_tauLat_comp {E ι : Type} [Field E] [NumberField E] {n : ℕ} (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (τ : ι) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M)
    (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    (C : GL (Fin n) K₀) (hC : IsBasisAt w₀ (tauLat emb τ M) C) :
    IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (inside₂ K₀ n C)) := by
  rw [← invTr_bc]
  refine GlobalTheory.DualWeylDual.isBasisAt_dualFr w (tauLatLattice E K ι n _ τ M hM).fg ?_
  rw [tauLat_comp]
  exact isBasisAt_span_vmap f w₀ w hw hC

theorem nabStd_le_span_map {ι : Type} [Fintype ι] {n : ℕ} (f : K₀ →+* K) (lam : ι → DomWeight n) :
    nabStd K lam ≤ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) := by
  have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
  have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
  rw [h1, ← h2]
  intro x hx
  exact Submodule.subset_span ⟨x, hx, MvPolynomial.map_id x⟩

theorem map_smul_int {σ : Type} (f : K₀ →+* K) (t : 𝓞 K₀) (P : MvPolynomial σ K₀) :
    RingOfIntegers.mapRingHom f t • MvPolynomial.map f P = MvPolynomial.map f (t • P) := by
  ext m
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]
  change ((RingOfIntegers.mapRingHom f t : 𝓞 K) : K) * f (P.coeff m) = f ((t : K₀) * P.coeff m)
  rw [map_mul]
  rfl

theorem mem_localization_span_map {E ι : Type} [Field E] [NumberField E] [Fintype ι] {n : ℕ} (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M)
    (w : HeightOneSpectrum (𝓞 K)) {F : Pol K ι n}
    (hF : F ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) :
    F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)))) := by
  classical
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsFullLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  set N' := Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) with hN'
  have key : ∀ H ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))),
      actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) H ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' := by
    intro H hH
    refine (Submodule.span_le (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N').comap
      ((actP lam (fun τ => Formalism.UG.bc f (B₀ τ))).restrictScalars (𝓞 K)))).2 ?_ hH
    rintro _ ⟨g, hg, rfl⟩
    show actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N'
    rw [← GlobalTheory.ValCmp.use₂]
    have hg' : actP lam B₀ g ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) := by
      rw [L0]
      exact Submodule.mem_map_of_mem (mem_localization_of_mem' _ hg)
    obtain ⟨t, ht, htg⟩ := hg'
    refine ⟨RingOfIntegers.mapRingHom f t, hw t ht, ?_⟩
    have e := map_smul_int f t (actP lam B₀ g)
    refine (congrArg (· ∈ N') e).mpr ?_
    exact Submodule.subset_span ⟨_, htg, rfl⟩
  have hF' : F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) :=
    mem_localization_of_mem' _ hF
  rw [L1] at hF'
  obtain ⟨G, ⟨s, hs, hsG⟩, rfl⟩ := hF'
  obtain ⟨t, ht, htG⟩ := key _ (nabStd_le_span_map f lam hsG)
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  convert htG using 1
  rw [mul_smul]
  congr 1
  exact (((actP lam fun τ => Formalism.UG.bc f (B₀ τ)).restrictScalars (𝓞 K)).map_smul s G).symm

theorem nabBaseChange : ∀ (E K₀ K ι : Type) [Field E] [NumberField E] [Field K₀] [NumberField K₀]
    [Field K] [NumberField K] [Fintype ι] (n : ℕ) (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E M →
    nabAtr (fun τ => f.comp (emb τ)) lam M ≤
      Submodule.span (𝓞 K) {y : VV K lam | ∃ x ∈ nabAtr emb lam M,
        (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)} := by
  intro E K₀ K ι _ _ _ _ _ _ _ n f emb lam M hM F hF
  obtain ⟨-, -, hV⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hP : (F : Pol K ι n) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) :=
    GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => GlobalTheory.NabBC.mem_localization_span_map f emb lam M hM w hF
  have hS : ((VV K lam).subtype.restrictScalars (𝓞 K)) ''
      {y : VV K lam | ∃ x ∈ nabAtr emb lam M, (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)} =
      MvPolynomial.map f '' (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)) := by
    ext P
    constructor
    · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
      exact ⟨x.1, hx, hxy.symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hxV : x ∈ VV K₀ lam := hV K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) x hx
      exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam x hxV⟩, ⟨⟨x, hxV⟩, hx, rfl⟩, rfl⟩
  rw [← hS, ← Submodule.map_span] at hP
  obtain ⟨y, hy, hyF⟩ := hP
  have e : y = F := Subtype.ext hyF
  rwa [← e]

end GlobalTheory.NabBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_baseChange_span_proof : GlobalTheory.BaseCmp.NabBaseChange := by
  first | exact @GlobalTheory.NabBC.nabBaseChange | exact GlobalTheory.NabBC.nabBaseChange | (intros; apply GlobalTheory.NabBC.nabBaseChange <;> assumption)
end
end
