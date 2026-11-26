module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.GaugeValues

theorem vF_eq {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (z : Sp F) (t : LB.Gen (LB.LinComb L φ ε))
    (r : Sp F ⟶ Y) : (((TorusExt.stalkUnits z).symm (val t r z J) : Fˣ) : F) = vF t r J := by
  have h : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ φ k)) := fun w _ =>
    Good.mem (L := L) (z := w) (J := J) (fun ψ => hJ ψ trivial) φ r
  refine (TorusExt.stalkConst z).injective ?_
  rw [← TorusExt.stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (gs_unit r z _ (h trivial) _).symm.trans (TorusExt.gs_eq_stalkConst r z h _)

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem val_sym_one {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J} (hJ : Good D.P.L z J) :
    val D.sym (1 : T ⟶ D.P.A).left z J = 1 := by
  have s := val_corr hJ D.sym_rig (toUnit T).left
  rw [val_pull hJ, val_one] at s
  exact s

theorem prod_sym {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i : Fin 2, h (x.left ≫ ![(ι[D.P.A]).left, 𝟙 D.P.A.left] i) ^ (![1, -1] : Fin 2 → ℤ) i =
      h (x⁻¹).left * (h x.left)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (x ≫ ι[D.P.A]).left ^ (1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [zpow_one, zpow_neg_one, Category.comp_id]; rfl

theorem val_sym_mul (hG : GlobalFnsSt) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J} (hJ : Good D.P.L z J)
    (x y : T ⟶ D.P.A) :
    val D.sym (x * y).left z J * cubV D.cub z J x x⁻¹ y⁻¹ =
      val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J y y⁻¹ x := by
  let p : D.P.A ⊗ D.P.A ⟶ D.P.A := fst _ _
  let q : D.P.A ⊗ D.P.A ⟶ D.P.A := snd _ _
  have ev : ∀ {T' : Over (Spec (CommRingCat.of R))} (a b : T' ⟶ D.P.A) {z : T'.left} {J}, Good D.P.L z J →
      val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.sym (p * q).left)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift p (lift p⁻¹ q⁻¹)).left)) (lift a b).left z J =
        val D.sym (a * b).left z J * cubV D.cub z J a a⁻¹ b⁻¹ ∧
      val (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.sym p.left)
        (LB.pullGen D.P.L _ _ D.sym q.left))
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift q (lift q⁻¹ p)).left)) (lift a b).left z J =
        val D.sym a.left z J * val D.sym b.left z J * cubV D.cub z J b b⁻¹ a := by
    intro T' a b z J hJ
    have e₁ : lift a b ≫ p = a := lift_fst _ _
    have e₂ : lift a b ≫ q = b := lift_snd _ _
    have e₃ : lift a b ≫ (p * q) = a * b := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂])
    have e₄ : lift a b ≫ p⁻¹ = a⁻¹ := (map_inv (preHom (lift a b)) p).trans (congrArg (·⁻¹) e₁)
    have e₅ : lift a b ≫ q⁻¹ = b⁻¹ := (map_inv (preHom (lift a b)) q).trans (congrArg (·⁻¹) e₂)
    have vs : ∀ w : D.P.A ⊗ D.P.A ⟶ D.P.A, val (LB.pullGen D.P.L _ _ D.sym w.left) (lift a b).left z J =
        val D.sym (lift a b ≫ w).left z J := fun w => val_pull hJ _ _ _
    refine ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs _) (val_cub D.cub _ hJ _ _ _))).trans ?_,
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs _) (vs _)))
        (val_cub D.cub _ hJ _ _ _))).trans ?_⟩
    · rw [e₁, e₃, e₄, e₅]
    · rw [e₁, e₂, e₅]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A ⊗ D.P.A := lift 1 1
  have he : e.left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  refine (ev x y hJ).1.symm.trans (Eq.trans (gen_unique' D.P.isLB (fun V _ k => ?_) _ e.left he
    (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.sym_gen _) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)
      (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (fun w I hI => ?_) _ (lift x y).left z J hJ) (ev x y hJ).2)
  · refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := thK) (U := V) _
      (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym D p k) (prod_sym D q k))
      (prod_cub q q⁻¹ p k)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 2) (K' := thK) (U := V) _
        (prod_sym D (p * q) k) (prod_cub p p⁻¹ q⁻¹ k)).symm)
    rw [mul_inv_cancel, mul_inv_cancel, _root_.one_mul, _root_.one_mul, mul_inv, mul_comm q p, mul_comm q⁻¹ p]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) w I) := isCub_cubV D.cub hI
    refine (ev 1 1 hI).1.trans (Eq.trans ?_ (ev 1 1 hI).2.symm)
    rw [_root_.mul_one, C.face, C.face, val_sym_one D hI, _root_.mul_one, _root_.mul_one]

theorem exists_numOf : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∀ th : H0 D.P.L 1, (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → ∃ (N : NumD F) (ν : NumOf D F N), ν.J = J ∧ ν.th = th := by
  intro hL R _ _ D hE hB F _ _ J hJ th hth
  let z : (TF (R := R) F).left := IsLocalRing.closedPoint F
  have g : Good D.P.L z J := fun ψ => hJ ψ trivial
  let u : ((TF (R := R) F).left.presheaf.stalk z)ˣ ≃* Fˣ := (TorusExt.stalkUnits (F := F) z).symm
  have C : IsCub (cubV D.cub (T := TF (R := R) F) z J) := isCub_cubV D.cub g
  let ρ : ((TF (R := R) F).left.presheaf.stalk z)ˣ := val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A)
    (ε := fun _ => 1) D.rig (TF (R := R) F).hom z J
  let P : D.X → ((TF (R := R) F).left.presheaf.stalk z)ˣ := fun χ =>
    val (Z := (TF (R := R) F).left) (D.psi χ) (jFK (R := R) F) z J
  obtain ⟨b, e⟩ := TauValues.main R D F
  let N : NumD F :=
    { A := TF (R := R) F ⟶ D.P.A
      θ := fun x y w => u (cubV D.cub z J x y w)
      cub := ⟨fun x y => (congrArg u (C.face x y)).trans (map_one u), fun x y w => congrArg u (C.s01 x y w),
        fun x y w => congrArg u (C.s12 x y w), fun x x' x'' y =>
          (map_mul u _ _).symm.trans ((congrArg u (C.coc x x' x'' y)).trans (map_mul u _ _))⟩
      σ := fun x => u (val D.sym x.left z J)
      σ_one := (congrArg u (val_sym_one D g)).trans (map_one u)
      σ_mul := fun x y => by
        simpa only [map_mul] using congrArg u (val_sym_mul D hL.globalFns g x y)
      th := fun x => sF th x.left J * ((u ρ)⁻¹ : Fˣ)
      X := D.X
      c := DegPre.cF D F
      c_add := fun a a' => (congrArg (toUnit _ ≫ ·) (D.c_add a a')).trans (MonObj.comp_mul _ _ _)
      ψ := fun χ => u (P χ * ρ)
      even := fun χ => by
        have h : P (-χ) * val D.sym (DegPre.cF D F χ).left z J = P χ := e.2 hE z J g χ
        rw [← map_mul, mul_right_comm, h]
      bimult := fun a a' m => by
        have h : P (a + a' + m) * P a * P a' * P m * ρ *
            cubV D.cub z J (DegPre.cF D F a) (DegPre.cF D F a') (DegPre.cF D F m) =
            P (a + a') * P (a + m) * P (a' + m) := b.2 hB z J g a a' m
        simp only [← map_div, ← map_mul]
        refine congrArg u (Additive.ofMul.injective ?_)
        have h' := congrArg Additive.ofMul h
        simp only [ofMul_mul, ofMul_div] at h' ⊢
        linear_combination (norm := abel) h' }
  have hρ : ((u ρ : Fˣ) : F) = vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
      (TF (R := R) F).hom J := vF_eq hJ z _ _
  exact ⟨N,
    { J := J, good := hJ, th := th, th_gen := hth, eA := MulEquiv.refl _, eX := AddEquiv.refl _
      c_eq := fun _ => rfl
      θ_eq := fun _ _ _ => vF_eq hJ z _ _
      σ_eq := fun _ => vF_eq hJ z _ _
      th_eq := fun x => (congrArg (N.th x * ·) hρ.symm).trans (Units.inv_mul_cancel_right _ _)
      ψ_eq := fun χ => (congrArg Units.val (map_mul u _ _)).trans ((Units.val_mul _ _).trans
        (congrArg₂ (· * ·) (vF_eq hJ z _ _) hρ)) }, rfl, rfl⟩

end GlobalTheory.GaugeValues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullExtend

open ThetaPtMove

theorem isCoordPt_move {S S' : Scheme.{0}} {f : S' ⟶ S} {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ)) {B : Over S} (σ : T.left ⟶ B.left) [IsIso σ]
    (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    (hg : ∀ th₀, IsGenSec P₀.A P₀.L 1 th₀ → IsGenSec P₀.A P₀.L 1 (VVRank.pullS P₀.A 1 β th₀))
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (T₀ ⟶ P₀.A)} (hx : ∀ i, τ ≫ (x₀ i).left = (x i).left ≫ φ)
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {z : T ⟶ P.A} {z₀ : T₀ ⟶ P₀.A} (hz : τ ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(T₀.left, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => τ.appTop.hom (v₀ i)) := by
  obtain ⟨w, hw⟩ := hw
  have hL₀ := P₀.isLB
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ho, hu, th₀, s₀, α₀, ρ₀, U₀, t₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := H
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  choose t ht using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (t₀ i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ k) α₀ h₂
  obtain ⟨ρ, hρ, vρ⟩ := ConstFam.exists_gen_through (φ' := fun _ : Fin 1 => z.left) (h := τ) hw hL₀ hL₁
    (fun _ => hz.symm) ρ₀ h₃
  choose U hU hU' using fun i => symLift_move hp τ hτ hw hL₀ hL₁ (hx i) (hk i) (h₅ i)
  exact ⟨ho, (map_natCast τ.appTop.hom k) ▸ hu.map τ.appTop.hom, th, s, α, ρ, U, t,
    isGenSec_move hp τ hτ hw hL₀ hL₁ σ β hβ hth (hg _ h₁), hα, hρ,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ k) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (ht i) (h₆ i), fun i => isValueAt_move hp τ hτ hL₀ hL₁ hz vρ (ht i) (h₇ i)⟩

theorem isGenSec_base (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Sp K)) {R : Type} [CommRing R]
    (t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp K))))
    (h : IsGenSec P.A P.L 1 th) : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (homAt t ≫ overResι ⊤) th) := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  let i : baseOver (Sp K) ⟶ overRes (T := baseOver (Sp K)) ⊤ := Over.homMk (Sp K).topIso.inv
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Scheme.toIso_inv_ι _))
  have hi : overResι (T := baseOver (Sp K)) ⊤ ≫ i = 𝟙 _ := Over.OverMorphism.ext (Sp K).topIso.hom_inv_id
  have h₁ : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (overResι ⊤) th) := fun s => by
    obtain ⟨r, hr⟩ := h (VVRank.pullS P.A 1 i s)
    have e : VVRank.pullM P.A P.L 1 i (SecM.ofSec P.A s) = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    have := congrArg (VVRank.pullM P.A P.L 1 (overResι ⊤)) e
    rw [VVRank.pullM_comp P.A P.isLB, hi, VVRank.pullM_id P.A P.isLB, LinearMap.map_smulₛₗ] at this
    exact ⟨_, fun j => congrArg (fun q => q.1 j) this⟩
  intro s
  obtain ⟨r, hr⟩ := isGenSec_pullS hS p₀ P t _ h₁ s
  have e := VVRank.pullM_comp P.A P.isLB 1 (homAt t) (overResι ⊤) (SecM.ofSec P.A th)
  exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e))⟩

theorem isCoordPt_fibre (hS : SecBaseChangeSt) {K R : Type} [Field K] [CommRing R] {f : K →+* R} {P₀ : PolAV (Sp K)}
    {P : PolAV (Sp R)} {φ : P.A.left ⟶ P₀.A.left} (h : IsPolFibre f P₀ P φ) {k : ℕ} {I : Type}
    {x : I → (baseOver (Sp R) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1)
    {z : baseOver (Sp R) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(Sp K, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => (spMap f).appTop.hom (v₀ i)) := by
  let t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left := spMap f ≫ (Sp K).topIso.inv
  have ht : t ≫ (⊤ : (Sp K).Opens).ι = spMap f := by
    show (spMap f ≫ (Sp K).topIso.inv) ≫ _ = _
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  let σ : (baseOver (Sp R)).left ⟶ (baseAt t).left := 𝟙 (Sp R)
  have : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp R)))
  exact isCoordPt_move (T := baseOver (Sp R)) (T₀ := baseOver (Sp K)) (spMap f) h.2.1 h.2.2.symm σ
    (homAt t ≫ overResι ⊤) ((Category.id_comp _).trans ht) ((Category.comp_id _).trans (Category.id_comp _).symm)
    (isGenSec_base hS P₀ t) hx hk hz H

theorem prim_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso (L.pull φ) L') {a : G ⟶ G} {a' : G' ⟶ G'}
    (ha : a'.left ≫ φ = φ ≫ a.left) (H : LBIso L (cubeLB G ![𝟙 G, a] L)) : LBIso L' (cubeLB G' ![𝟙 G', a'] L') := by
  have i₁ := pull_isLB hL φ
  have h₁ : LBIso (L.pull φ) (cubeLB G' ![𝟙 G', a'] (L.pull φ)) := by
    let U := pushPt h.1.w (𝟙 G')
    refine LBIso.chartPull (Geo.Tor.chartPullPull L _ U.left (Category.id_comp _))
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
    fin_cases i
    · exact (Category.comp_id _).symm
    · exact Over.OverMorphism.ext (ha.trans (congrArg (· ≫ a.left) (Category.id_comp _).symm))
  obtain ⟨w, hw'⟩ := id hw
  exact LBIso.trans hL' (DVR.linComb_isLB _ i₁ _ _) (DVR.linComb_isLB _ hL' _ _)
    (LBIso.trans hL' i₁ (DVR.linComb_isLB _ i₁ _ _) hw.symm h₁) ⟨_, DVR.linCombIso_isGen w hw' _ _⟩

theorem exists_pointMap (hL : Laws) {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K']
    {f : K →+* K'} {P : PolAV (Sp K)} {P' : PolAV (Sp K')} {φ : P'.A.left ⟶ P.A.left} (h : IsPolFibre f P P' φ) :
    ∃ r : (baseOver (Sp K) ⟶ P.A) →* (baseOver (Sp K') ⟶ P'.A), (∀ x, (r x).left ≫ φ = spMap f ≫ x.left) ∧
      Function.Injective r ∧ (∀ n : ℕ, 0 < n → ∀ y, y ^ n = 1 → ∃ x, x ^ n = 1 ∧ r x = y) ∧
      ∀ (n : ℤ) x y (c : Kˣ), WeilIs P.A P.L n x y (unitOn c) →
        WeilIs P'.A P'.L n (r x) (r y) (unitOn (Units.map f.toMonoidHom c)) := by
  have := P'.isAb.comm
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h.2.1 (baseOver (Sp K')) _ rfl
  let U : Over.mk ((baseOver (Sp K')).hom ≫ spMap f) ⟶ baseOver (Sp K) :=
    Over.homMk (spMap f) ((Category.comp_id _).trans (Category.id_comp _).symm)
  let r : (baseOver (Sp K) ⟶ P.A) →* (baseOver (Sp K') ⟶ P'.A) := e.symm.toMonoidHom.comp (preHom U)
  have hr : ∀ x, (r x).left ≫ φ = spMap f ≫ x.left := fun x =>
    (he _).symm.trans (congrArg (fun q => q.left) (e.apply_symm_apply (U ≫ x)))
  have inj : Function.Injective r := by
    letI := f.toAlgebra
    haveI : Flat (spMap f) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat K K')
    haveI : Surjective (spMap f) := ⟨fun p => ⟨(⊥ : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    haveI : Epi (spMap f) := Flat.epi_of_flat_of_surjective (spMap f)
    exact fun x y E => Over.OverMorphism.ext ((cancel_epi (spMap f)).1
      ((hr x).symm.trans ((congrArg (fun q => q.left ≫ φ) E).trans (hr y))))
  refine ⟨r, hr, inj, fun n hn y hy => ?_, fun n x y c H => ?_⟩
  · have hk : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hk' : (n : K') ≠ 0 := by rw [← map_natCast f]; exact (map_ne_zero f).2 hk
    have c₁ := (hL.mulN _ P n hn).2.2.2.2 K (𝟙 _) hk
    have c₂ := (hL.mulN _ P' n hn).2.2.2.2 K' (𝟙 _) hk'
    let F : {x : baseOver (Sp K) ⟶ P.A // x ^ n = 1} → {x : baseOver (Sp K') ⟶ P'.A // x ^ n = 1} :=
      fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩
    have hF : Function.Injective F := fun a b E => Subtype.ext (inj (congrArg Subtype.val E))
    haveI : Finite {x : baseOver (Sp K') ⟶ P'.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (c₂.trans_ne (by positivity))
    obtain ⟨x, hx⟩ := (hF.bijective_of_nat_card_le (c₂.trans (by rw [h.1]; exact c₁.symm)).le).2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
  · have hu : Units.map U.left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map f.toMonoidHom c) :=
      Units.ext (congrArg (fun q => q.hom (c : K)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm
    refine (weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ P.isLB P'.isLB h.2.1 h.2.2.symm _ _ _ _ (U ≫ x) (U ≫ y) _
      (hr x).symm (hr y).symm).2 ?_
    exact hu ▸ CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB U H

theorem fnOf_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (c : K) :
    fnOf (f c) = (spMap f).appTop.hom (fnOf c) :=
  congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))

theorem exists_fullExt (hL : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K'] (f : K →+* K') (o : Full D K) :
    letI := H.starRing
    ∃ o' : Full D K', (o'.ρ = f o.ρ ∧ (∀ n, 0 < n → (o'.I.ζ n : K') = f (o.I.ζ n)) ∧
      ∃ φ : o'.P.A.left ⟶ o.P.A.left, IsGrpPullback o'.P.A o.P.A (spMap f) φ ∧ LBIso o'.P.L (o.P.L.pull φ) ∧
        (∀ x, (o'.oa.act x).left ≫ φ = φ ≫ (o.oa.act x).left) ∧
        ∀ n v, 0 < n → (o'.I.ev n v).left ≫ φ = spMap f ≫ (o.I.ev n v).left) ∧
      (∀ m v, o.Theta m v → o'.Theta m fun x => f (v x)) ∧
      ∀ m j z v, o.Coord m (o.I.ev j z) v → o'.Coord m (o'.I.ev j z) fun x => f (v x) := by
  letI := H.starRing
  obtain ⟨P', φ, hφ, hg, hm, hw⟩ := hL.polBaseChange _ _ (spMap f) o.P
  have hp : IsGrpPullback P'.A o.P.A (spMap f) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hφ.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hφ.w y := Over.OverMorphism.ext hy
    exact congrArg (fun q => q.left) (hm T x y).symm⟩
  have h : IsPolFibre f o.P P' φ := ⟨hg, hp, hw⟩
  obtain ⟨oa, hoa⟩ := polOActPull _ _ _ o.P P' φ hp hw (𝓞 E) o.oa
  obtain ⟨r, hr, inj, onto, weil⟩ := exists_pointMap hL h
  have uinj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have hact : ∀ c x, r (x ≫ o.oa.act c) = r x ≫ oa.act c := fun c x => Over.OverMorphism.ext (hφ.hom_ext (by
    rw [hr, Over.comp_left, Over.comp_left, Category.assoc, hoa, ← Category.assoc, ← Category.assoc, hr])
    (by rw [Over.w, Over.w]))
  have tors : ∀ m a, r (o.I.ev (m ^ 2) a) ^ (m ^ 2) = 1 := fun m a => by
    rcases Nat.eq_zero_or_pos (m ^ 2) with e | e
    · rw [e, pow_zero]
    · rw [← map_pow, (o.I.onto _ e _).2 ⟨a, rfl⟩, map_one]
  have det : DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp K')) (f o.ρ) := fun τ => by
    have q := (detCond_iff_of_field_extension E H D _ _ K K' f (𝟙 _) _ _ o.P.isAb.smooth).2 o.det τ
    have e := fun n => LiePull.lieMult_pull (𝓞 E) _ _ _ _ _ φ (ofRingAct o.oa.toRingAct) (ofRingAct oa.toRingAct) hp hoa
      K' (𝟙 _) τ n
    rw [e, e, Category.id_comp]
    rwa [Category.comp_id] at q
  refine ⟨{ P := P', oa := oa, prim := prim_pull hp o.P.isLB P'.isLB hw (hoa _) o.prim, ρ := f o.ρ
            ρ_sq := by rw [← map_pow, o.ρ_sq, map_neg, map_natCast]
            det := det
            closed := ‹_›
            I := { ζ := fun n => Units.map f.toMonoidHom (o.I.ζ n)
                   ζ_prim := fun n hn => (o.I.ζ_prim n hn).map_of_injective uinj
                   ζ_pow := fun n m hn hm => by rw [← map_pow, o.I.ζ_pow n m hn hm]
                   ev := fun n v => r (o.I.ev n v)
                   add := fun n a b => by rw [o.I.add, map_mul]
                   lin := fun n c a => by rw [o.I.lin, hact]
                   ker := fun n hn a => by rw [← o.I.ker n hn a, map_eq_one_iff r inj]
                   onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
                   tower := fun n m hn hm a => by rw [← map_pow, o.I.tower n m hn hm]
                   isom := fun n hn a b => by rw [← map_zpow]; exact weil _ _ _ _ (o.I.isom n hn a b) } },
    ⟨rfl, fun _ _ => rfl, φ, hp, h.2.2.symm, hoa, fun n v _ => hr _⟩, fun m v Q => ?_, fun m j z v Q => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := onto n hn z hz
    obtain ⟨a, rfl⟩ := (o.I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (o.I.onto n hn _).2 ⟨a, rfl⟩, map_one]
  · have q := ConstThetaLevel.isThetaPt_fibre hL.secBaseChange h (fun a => (hr _).symm) (tors m) Q
    simp only [← fnOf_map] at q
    exact q
  · have q := isCoordPt_fibre hL.secBaseChange h (fun a => (hr _).symm) (tors m) (hr (o.I.ev j z)).symm Q
    simp only [← fnOf_map] at q
    exact q

end GlobalTheory.FullExtend

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.CubeRootAut

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem cubeCls_pair {T : Over S} (x y : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y] c = pull (x * y).left c - pull x.left c - pull y.left c + pull (1 : T ⟶ G).left c := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![x, y] I).left c) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, p₀, p₁, p₂, p₄]
  have c₁ : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [c₁, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

theorem cubeCls_triple {T : Over S} (x y z : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y, z] c = pull (x * y * z).left c - pull (x * y).left c - pull (x * z).left c -
      pull (y * z).left c + pull x.left c + pull y.left c + pull z.left c - pull (1 : T ⟶ G).left c := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 3)) ≃ Finset (Fin 3)) _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (psum G ![x, y, z] I).left c) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have p₀ : psum G ![x, y, z] ∅ = 1 := rfl
  have p₁ : psum G ![x, y, z] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y, z] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y, z] {2} = z := _root_.mul_one z
  have p₄ : psum G ![x, y, z] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₅ : psum G ![x, y, z] {0, 2} = x * z := congrArg (x * ·) (_root_.mul_one z)
  have p₆ : psum G ![x, y, z] {1, 2} = y * z := congrArg (y * ·) (_root_.mul_one z)
  have p₇ : psum G ![x, y, z] {0, 1, 2} = x * y * z :=
    (congrArg (fun w => x * (y * w)) (_root_.mul_one z)).trans (_root_.mul_assoc x y z).symm
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇]
  have c₁ : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c₂ : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₃ : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₄ : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  simp only [c₁, c₂, c₃, c₄, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

end General

end GlobalTheory.ZH.CubeRootAut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymSpread

variable {S U : Scheme.{0}} {G : Over S} {A : Over U} [GrpObj G] [GrpObj A] {j : U ⟶ S} {a : A.left ⟶ G.left}

theorem isPullback_square (h : IsGrpPullback A G j a) :
    IsPullback (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left (A ⊗ A).hom (G ⊗ G).hom j := by
  let l := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have l₁ : l.left ≫ pullback.fst G.hom G.hom = pullback.fst A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have l₂ : l.left ≫ pullback.snd G.hom G.hom = pullback.snd A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have big : IsPullback (pullback.snd A.hom A.hom ≫ a) (pullback.fst A.hom A.hom) G.hom (A.hom ≫ j) :=
    (IsPullback.of_hasPullback A.hom A.hom).flip.paste_horiz h.1
  have h₁ : IsPullback l.left (pullback.fst A.hom A.hom) (pullback.fst G.hom G.hom) a := by
    refine IsPullback.of_right (h₁₂ := pullback.snd G.hom G.hom) (v₁₃ := G.hom) (h₂₂ := G.hom) ?_
      l₁ (IsPullback.of_hasPullback G.hom G.hom).flip
    rw [l₂, h.1.w]
    exact big
  exact h₁.paste_vert h.1

theorem pushPt_comp (h : IsGrpPullback A G j a) {u' : A ⟶ A} {u : G ⟶ G} (e : a ≫ u.left = u'.left ≫ a)
    {T : Over U} (x : T ⟶ A) : pushPt h.1.w (x ≫ u') = pushPt h.1.w x ≫ u :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ← e, Category.assoc])

variable [IsCommMonObj G] [IsCommMonObj A]

theorem lbIso_cube (h : IsGrpPullback A G j a) {L : LB G.left} {LA : LB A.left} (hL : L.IsLB) (hLA : LA.IsLB)
    (hb : LBIso LA (L.pull a)) {T : Over S} {T' : Over U} {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ A))
    (V : Over.mk (T'.hom ≫ j) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = V ≫ x i) :
    LBIso (cubeLB A x' LA) ((cubeLB G x L).pull V.left) :=
  LBIso.trans (DVR.linComb_isLB _ hLA _ _) (DVR.linComb_isLB _ (LB.isLB_pull hL a) _ _)
    (LB.isLB_pull (DVR.linComb_isLB _ hL _ _) _) (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.chartPull (chartPullLinComb L a _ _ _ V.left fun I => psum_push h _ _ V hx I.down)
      (Geo.Tor.chartPullPull _ V.left V.left rfl) (lbIso_refl (DVR.linComb_isLB _ hL _ _)))

theorem lbIso_sym (h : IsGrpPullback A G j a) {L : LB G.left} {LA : LB A.left} (hL : L.IsLB) (hLA : LA.IsLB)
    (hb : LBIso LA (L.pull a)) {w wd : G ⟶ G} {w' wd' : A ⟶ A}
    (pa : ∀ {T : Over U} (x : T ⟶ A), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w)
    (pd : ∀ {T : Over U} (x : T ⟶ A), pushPt h.1.w (x ≫ wd') = pushPt h.1.w x ≫ wd) :
    LBIso (cubeLB A ![𝟙 A, w'] LA) ((cubeLB G ![𝟙 G, w] L).pull a) ∧
    LBIso (cubeLB A ![fst A A ≫ w', snd A A] LA) ((cubeLB G ![fst G G ≫ w, snd G G] L).pull
      (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left) ∧
    LBIso (cubeLB A ![fst A A, snd A A ≫ wd'] LA) ((cubeLB G ![fst G G, snd G G ≫ wd] L).pull
      (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left) := by
  refine ⟨?_, lbIso_cube h hL hLA hb _ _ _ fun i => ?_, lbIso_cube h hL hLA hb _ _ _ fun i => ?_⟩
  · let V := pushPt h.1.w (𝟙 A)
    have hV : V.left = a := Category.id_comp _
    have c := lbIso_cube h hL hLA hb ![𝟙 G, w] ![𝟙 A, w'] V (fun i => by
      fin_cases i
      · simp [V]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _))
    rwa [hV] at c
  · fin_cases i
    · exact (pa _).trans (by simp)
    · simp
  · fin_cases i
    · simp
    · exact (pd _).trans (by simp)

theorem exists_forall_hypS : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → ∀ (w wd : G ⟶ G) (w₀ wd₀ : A ⟶ A), φ ≫ w.left = w₀.left ≫ φ → φ ≫ wd.left = wd₀.left ≫ φ → IsMonHom w₀ → IsMonHom wd₀ → w₀ * wd₀ = 𝟙 A → LBIso L₀ (cubeLB A ![𝟙 A, w₀] L₀) → LBIso (cubeLB A ![fst A A ≫ w₀, snd A A] L₀) (cubeLB A ![fst A A, snd A A ≫ wd₀] L₀) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → HypS G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hG h hL hL₀ hb w wd w₀ wd₀ ew ewd hw₀ hwd₀ hs hp ha
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap R K)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    ExtUnique.spec_fractionRing R K
  have := hG.smooth
  have := hG.proper
  have hw : IsMonHom w := ExtUnique.isMonHom_of_isGrpPullback h h w₀ w ew.symm
  have hwd : IsMonHom wd := ExtUnique.isMonHom_of_isGrpPullback h h wd₀ wd ewd.symm
  have hsum : w * wd = 𝟙 G := by
    refine ExtUnique.over_hom_ext_of_isPullback h.1 ?_
    have b : pushPt h.1.w (w₀ * wd₀) = pushPt h.1.w w₀ * pushPt h.1.w wd₀ := map_mul (pushHom h A) _ _
    have c := pushPt_comp h ew (𝟙 A)
    have d := pushPt_comp h ewd (𝟙 A)
    rw [Category.id_comp] at c d
    rw [c, d, ← MonObj.comp_mul, hs] at b
    have e : 𝟙 A.left ≫ φ = (𝟙 A.left ≫ φ) ≫ (w * wd).left := congrArg (fun z => z.left) b
    simp only [Category.id_comp] at e
    simpa using e.symm
  have cl : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x L).IsLB := fun x => DVR.linComb_isLB _ hL _ _
  have cl₀ : ∀ {T : Over (Sp K)} (x : Fin 2 → (T ⟶ A)), (cubeLB A x L₀).IsLB := fun x => DVR.linComb_isLB _ hL₀ _ _
  obtain ⟨c₁, c₂, c₃⟩ := lbIso_sym h hL hL₀ hb (fun x => pushPt_comp h ew x) (fun x => pushPt_comp h ewd x)
  have : IsProper (G ⊗ G).hom := by
    change IsProper (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  obtain ⟨a₁, ha₁, H₁⟩ := GenSpread.exists_lbIso G.hom h.1 hL (cl _)
    (hb.symm.trans (LB.isLB_pull hL _) hL₀ (LB.isLB_pull (cl _) _) (hp.trans hL₀ (cl₀ _) (LB.isLB_pull (cl _) _) c₁))
  obtain ⟨a₂, ha₂, H₂⟩ := GenSpread.exists_lbIso (G ⊗ G).hom (isPullback_square h) (cl _) (cl _)
    (c₂.symm.trans (LB.isLB_pull (cl _) _) (cl₀ _) (LB.isLB_pull (cl _) _)
      (ha.trans (cl₀ _) (cl₀ _) (LB.isLB_pull (cl _) _) c₃))
  refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, fun R' _ g hg G' _ _ π L' h' hL' hb' => ?_⟩
  rw [map_mul, IsUnit.mul_iff] at hg
  obtain ⟨w', hw', pa⟩ := SymBaseChange.exists_endo h' w
  obtain ⟨wd', hwd', pd⟩ := SymBaseChange.exists_endo h' wd
  have cl' : ∀ {T : Over (Sp R')} (x : Fin 2 → (T ⟶ G')), (cubeLB G' x L').IsLB := fun x =>
    DVR.linComb_isLB _ hL' _ _
  obtain ⟨d₁, d₂, d₃⟩ := lbIso_sym h' hL hL' hb' pa pd
  refine ⟨w', wd', hw', hwd', ?_, ?_, ?_⟩
  · apply SymBaseChange.pushPt_injective h'
    have b : pushPt h'.1.w (w' * wd') = pushPt h'.1.w w' * pushPt h'.1.w wd' := map_mul (pushHom h' G') _ _
    have c := pa (𝟙 G')
    have d := pd (𝟙 G')
    rw [Category.id_comp] at c d
    rw [b, c, d, ← MonObj.comp_mul, hsum, Category.comp_id]
  · exact hb'.trans hL' (LB.isLB_pull hL _) (cl' _)
      ((H₁ R' g hg.1 _ π G'.hom h'.1.w).trans (LB.isLB_pull hL _) (LB.isLB_pull (cl _) _) (cl' _) d₁.symm)
  · exact d₂.trans (cl' _) (LB.isLB_pull (cl _) _) (cl' _)
      ((H₂ R' g hg.2 _ _ (G' ⊗ G').hom (isPullback_square h').w).trans (LB.isLB_pull (cl _) _) (LB.isLB_pull (cl _) _)
        (cl' _) d₃.symm)

end GlobalTheory.SymSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetryHypothesis_spread_from_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → ∀ (w wd : G ⟶ G) (w₀ wd₀ : A ⟶ A), φ ≫ w.left = w₀.left ≫ φ → φ ≫ wd.left = wd₀.left ≫ φ → IsMonHom w₀ → IsMonHom wd₀ → w₀ * wd₀ = 𝟙 A → LBIso L₀ (cubeLB A ![𝟙 A, w₀] L₀) → LBIso (cubeLB A ![fst A A ≫ w₀, snd A A] L₀) (cubeLB A ![fst A A, snd A A ≫ wd₀] L₀) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → HypS G' L' := by
  first | exact @GlobalTheory.SymSpread.exists_forall_hypS | exact GlobalTheory.SymSpread.exists_forall_hypS | (intros; apply GlobalTheory.SymSpread.exists_forall_hypS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGeneric
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenSpread

theorem isIso_stalkMap_of_flat {X Y : Scheme.{0}} (φ : X ⟶ Y) [Flat φ] [SurjectiveOnStalks φ] (x : X) :
    IsIso (φ.stalkMap x) := by
  have h1 := Flat.stalkMap φ x
  have h2 := φ.stalkMap_surjective x
  algebraize [(φ.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (φ x))
    (B := X.presheaf.stalk x)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x), h2⟩

theorem mem_smoothLocus_of_isPullback {X X₀ S S₀ : Scheme.{0}} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀}
    {φ : X₀ ⟶ X} {j : S₀ ⟶ S} (h : IsPullback φ f₀ f j) [LocallyOfFinitePresentation f] [Flat j]
    [SurjectiveOnStalks j] [Smooth f₀] (x : X₀) : φ x ∈ f.smoothLocus := by
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  have : SurjectiveOnStalks φ :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) h.flip inferInstance
  have := isIso_stalkMap_of_flat φ x
  have := isIso_stalkMap_of_flat j (f₀ x)
  have h0 : (f₀.stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (f₀.smoothLocus_eq_top.ge (Set.mem_univ x))
  have h1 : ((f₀ ≫ j).stalkMap x).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).2 h0
  rw [← h.w, Scheme.Hom.stalkMap_comp] at h1
  exact Scheme.Hom.mem_smoothLocus.mpr
    ((RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).1 h1)

theorem exists_opens_smoothOfRelativeDimension_of_isPullback {X X₀ S S₀ : Scheme.{0}} {f : X ⟶ S}
    {f₀ : X₀ ⟶ S₀} {φ : X₀ ⟶ X} {j : S₀ ⟶ S} (h : IsPullback φ f₀ f j)
    [LocallyOfFinitePresentation f] [Flat j] [SurjectiveOnStalks j] (n : ℕ)
    [SmoothOfRelativeDimension n f₀] (x : X₀) :
    ∃ W : X.Opens, φ x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f) := by
  have : Smooth f₀ := SmoothOfRelativeDimension.smooth n _
  have hz := mem_smoothLocus_of_isPullback h x
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  have h1 : SmoothOfRelativeDimension (0 + n) (pullback.snd f j) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  have h2 : SmoothOfRelativeDimension (0 + (0 + (0 + n))) (pullback.snd (f.smoothLocus.ι ≫ f) j) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨W, hW, hW'⟩ := GlobalTheory.VeryDenseFibres.exists_opens_smoothOfRelativeDimension
    (f.smoothLocus.ι ≫ f) j n (by simpa using h2) ⟨φ x, hz⟩ (f₀ x) (by
      change f (φ x) = _
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w])
  let i := W.ι ≫ f.smoothLocus.ι
  refine ⟨i.opensRange, ⟨⟨⟨φ x, hz⟩, hW⟩, rfl⟩, ?_⟩
  have e : i.opensRange.ι ≫ f = i.isoOpensRange.inv ≫ (W.ι ≫ f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]
  have h3 : SmoothOfRelativeDimension (0 + n)
      (i.isoOpensRange.inv ≫ (W.ι ≫ f.smoothLocus.ι ≫ f)) := inferInstance
  rw [e]
  simpa using h3

theorem exists_smoothOfRelativeDimension :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → IsProper f → SmoothOfRelativeDimension n f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → SmoothOfRelativeDimension n f' := by
  intro R K _ _ _ _ _ _ n X X₀ f f₀ φ h hf hf₀
  have : LocallyOfFinitePresentation f := inferInstance
  have : Flat (spMap (algebraMap R K)) := flat_specMap_localization (nonZeroDivisors R) K
  have : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  let U : X.Opens := ⨆ W : {W : X.Opens // SmoothOfRelativeDimension n (W.ι ≫ f)}, W.1
  have hc : IsClosed (f '' (U : Set X)ᶜ) := f.isClosedMap _ U.2.isClosed_compl
  obtain ⟨a, ha, H⟩ := exists_forall_notMem (K := K) hc (by
    rintro w ⟨z, hz, e⟩
    obtain ⟨x, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h z w e
    obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension_of_isPullback h n x
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩))
  refine ⟨a, ha, fun R' _ g hg X' π f' hp => ?_⟩
  have h1 : SmoothOfRelativeDimension n (pullback.snd f (spMap g)) := by
    refine GlobalTheory.ProperFlatNearFibre.smoothOfRelativeDimension_pullback_snd _ _ n fun z y e => ?_
    have h2 : z ∈ U := by
      by_contra hz
      exact H R' g hg y ⟨z, hz, e⟩
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact ⟨W.1, hW, W.2⟩
  have h2 : SmoothOfRelativeDimension (0 + n) (hp.isoPullback.hom ≫ pullback.snd f (spMap g)) :=
    inferInstance
  simpa using h2

end GlobalTheory.GenSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGenericStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothOfRelativeDimension_spread_from_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → IsProper f → SmoothOfRelativeDimension n f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → SmoothOfRelativeDimension n f' := by
  first | exact @GlobalTheory.GenSpread.exists_smoothOfRelativeDimension | exact GlobalTheory.GenSpread.exists_smoothOfRelativeDimension | (intros; apply GlobalTheory.GenSpread.exists_smoothOfRelativeDimension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationSpreadFromGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationSpreadFromGenericFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem exists_rigidified : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Rigidified A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Rigidified G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ _ _ hL _ _ _
  obtain ⟨i, hi⟩ := exists_chart hL (eSec G (genericPoint (Sp R)))
  obtain ⟨a, ha, H⟩ := exists_forall_mem (R := R) (V := eSec G ⁻¹ᵁ L.U i) hi
  refine ⟨a, ha, fun R' _ g hg G' _ _ π L' h hL' ⟨w, hw⟩ => ?_⟩
  obtain ⟨t, ht⟩ := AbSquare.exists_gen_of_mem_chart hL (K := PUnit) (fun _ => eSec G' ≫ π) (fun _ => 1)
    (fun _ => i) (fun _ y => (congrArg (fun q => q y ∈ L.U i) (PolBaseChange.eSec_comm h)).mpr (H R' g hg y))
  exact exists_down ((isGen_iff w).1 hw) hL hL' t ht

end GlobalTheory.GenSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationSpreadFromGenericFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidification_spread_from_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Rigidified A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Rigidified G' L' := by
  first | exact @GlobalTheory.GenSpread.exists_rigidified | exact GlobalTheory.GenSpread.exists_rigidified | (intros; apply GlobalTheory.GenSpread.exists_rigidified <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QvalAddTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QvalAddTower
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.NestQVal

attribute [local instance] GlobalTheory.TorusExt.gtGroup

attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.NestQVal.qval_add_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIsoQ D D₀ oa F) (N : _root_.GlobalTheory.Ex.NumD F) (ν : _root_.GlobalTheory.Ex.NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ g, ∃! c, ν.Pt g c) → (∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (_root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF.IsAdd g g' g'' ↔ c'' = c * c')) → (∀ k, (∀ p : _root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt D₀ F k, ∃! q, ν.QPt p q) ∧ ∀ (p p' : _root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt D₀ F k) q q', ν.QPt p q → ν.QPt p' q' → (_root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt.Equiv D₀ F p p' ↔ N.QEq q q')) → (∀ n a, ν.QPt (I.ev n a) (q n a)) → (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) ∧ ∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a) := by
  intro E _ _ _ H D R _ _ D₀ _ oa _ _ F _ _ _ I N ν q hPt hAdd hQ hev

  have hzero : ν.Pt 0 1 := by
    obtain ⟨c, hc, -⟩ := hPt 0
    have h := (hAdd 0 0 0 c c c hc hc hc).1 ((_root_.GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (add_zero 0).symm)
    have : c = 1 := by simpa using (mul_eq_left.1 h.symm)
    simpa [this] using hc
  have hsmul : ∀ (m : ℕ) g c, ν.Pt g c → ν.Pt (m • g) (c ^ m) := by
    intro m g c hc
    induction m with
    | zero => simpa using hzero
    | succ k ih =>
      obtain ⟨c', hc', -⟩ := hPt ((k + 1) • g)
      have h := (hAdd _ _ _ _ _ _ ih hc hc').1 ((_root_.GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (succ_nsmul g k))
      simpa [h, pow_succ] using hc'
  refine ⟨fun n hn a b => ?_, fun n m hn hm a p hp1 hp2 => ?_⟩
  · obtain ⟨r, hry, hrg, hr⟩ := I.add n hn a b
    obtain ⟨hya, hga⟩ := hev n a
    obtain ⟨hyb, hgb⟩ := hev n b
    obtain ⟨c'', hc'', -⟩ := hPt r.g
    have hc := (hAdd _ _ _ _ _ _ hga hgb hc'').1 hrg
    have hrs : ν.QPt r (q n a * q n b) := by
      refine ⟨?_, ?_⟩
      · simp [hry, ← hya, ← hyb]
      · simpa [hc] using hc''
    exact ((hQ n).2 _ _ _ _ hrs (hev n (a + b))).1 hr
  · obtain ⟨Q, hQy, hQg, hQe⟩ := I.tower n m hn hm a
    obtain ⟨hy, hg⟩ := hev (n * m) a
    have hQp : ν.QPt Q p := by
      refine ⟨?_, ?_⟩
      · rw [hQy, ← hy, hp1]
      · rw [(_root_.GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hQg, hp2]
        exact hsmul m _ _ hg
    exact ((hQ n).2 _ _ _ _ hQp (hev n a)).1 hQe

end GlobalTheory.NestQVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QvalAddTowerStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qval_add_of_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F) (N : NumD F) (ν : NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ g, ∃! c, ν.Pt g c) → (∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (GtPtF.IsAdd g g' g'' ↔ c'' = c * c')) → (∀ k, (∀ p : QkPt D₀ F k, ∃! q, ν.QPt p q) ∧ ∀ (p p' : QkPt D₀ F k) q q', ν.QPt p q → ν.QPt p' q' → (QkPt.Equiv D₀ F p p' ↔ N.QEq q q')) → (∀ n a, ν.QPt (I.ev n a) (q n a)) → (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) ∧ ∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a) := by
  first | exact @GlobalTheory.NestQVal.qval_add_tower | exact GlobalTheory.NestQVal.qval_add_tower | (intros; apply GlobalTheory.NestQVal.qval_add_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralGauge
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralGauge

theorem exists_chart_local {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (ψ : Sp V ⟶ X) : ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j := by
  have h : ψ (IsLocalRing.closedPoint V) ∈ (⨆ i, L.U i) := by rw [hL.1]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, fun w _ => (IsLocalRing.specializes_closedPoint (R := V) w).mem_open (ψ ⁻¹ᵁ L.U j).isOpen hj⟩

theorem exists_extension {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (S : ValuationSubring F)
    (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S)
    (x : TF (R := R) F ⟶ D.P.A) : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left := by
  haveI := D.P.isAb.proper
  have hE : ValuativeCriterion.Existence D.P.A.hom := by
    have h : UniversallyClosed D.P.A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let f : R →+* S := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).codRestrict S hS
  let Q : ValuativeCommSq D.P.A.hom :=
    { R := S, K := F, i₁ := x.left, i₂ := Spec.map (CommRingCat.ofHom f),
      commSq := ⟨by
        refine (Over.w x).trans ?_
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, h1, -⟩⟩ := hE Q
  exact ⟨l, h1⟩

theorem exists_integral_gauge (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (S : ValuationSubring F)
    (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) :
    ∃ J : (Sp F ⟶ D.P.A.left) → D.P.L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) ∧ ∀ x : TF (R := R) F ⟶ D.P.A,
      ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U (J x.left) := by
  have key : ∀ ψ : Sp F ⟶ D.P.A.left, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U j ∧
      ((∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ) →
        ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U j) := fun ψ => by
    by_cases h : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := exists_chart_local D.P.isLB x₀
      exact ⟨j, fun w _ => hj (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, hj⟩⟩
    · obtain ⟨j, hj⟩ := exists_chart_local D.P.isLB ψ
      exact ⟨j, hj, fun h' => (h h').elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, fun x => h₂ x.left (exists_extension D S hS x)⟩

end GlobalTheory.IntegralGauge
end
