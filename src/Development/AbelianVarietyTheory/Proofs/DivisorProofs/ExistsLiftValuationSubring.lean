module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TorEnd

theorem exists_lift_valuationSubring {F : Type} [Field F] (O : ValuationSubring F) {M : Type} [CommGroup M]
    (τ : M →* Fˣ) {k : ℕ} (hk : k ≠ 0) (hτ : τ ^ k = 1) :
    ∃ σ : M →* Oˣ, σ ^ k = 1 ∧ ∀ x, ((σ x : O) : F) = τ x := by
  have hp : ∀ x, (τ x : F) ^ k = 1 := fun x => by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hτ, MonoidHom.one_apply, Units.val_one]
  have hm : ∀ x, (τ x : F) ∈ O := fun x => by
    rw [← O.valuation_le_one_iff]
    have := congrArg O.valuation (hp x)
    rw [map_pow, map_one] at this
    exact ((pow_eq_one_iff_of_nonneg zero_le hk).1 this).le
  let σ₀ : M →* O :=
    { toFun := fun x => ⟨τ x, hm x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  refine ⟨σ₀.toHomUnits, MonoidHom.ext fun x => Units.ext (Subtype.ext ?_), fun x => rfl⟩
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  exact hp x

theorem chV_comp_torusMap {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z : Over S}
    (z : Z ⟶ splitTorus S X) (m : Y →+ X) (χ : Y) :
    GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap S m) χ = GlobalTheory.UU.chV z (m χ) := by
  refine Units.ext ?_
  rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val,
    ← GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_comp_torusMap]

theorem torMatch_of_endChar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G), IsMonHom f → ∀ m, EndChar U f m → TorMatch U U (RingHom.id R) f.left m := by
  intro R _ _ _ hR G _ _ hG D A U f hf m hm F _ _ i₁ i₂ hi k hk τ τ' q q' x x' hτ' hτ hq hqt hq' hqt' hx hx'
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  obtain ⟨s, s₁, s₂, s₃, s₄⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k (Nat.one_le_iff_ne_zero.2 hk0)
  let a : R →+* F := (@algebraMap (FractionRing R) F _ _ i₁).comp (algebraMap R (FractionRing R))
  have ha₂ : a = (@algebraMap (FractionRing R) F _ _ i₂).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun r => hi r
  let ν : Multiplicative D.toPre.X →* Multiplicative D.toPre.X := AddMonoidHom.toMultiplicative m
  have pw : ∀ {B : Type} [CommRing B] (σ : Multiplicative D.toPre.X →* Bˣ), σ ^ k = 1 → σ.comp ν ^ k = 1 :=
    fun σ h => MonoidHom.ext fun χ => DFunLike.congr_fun h (ν χ)
  obtain rfl : τ = τ'.comp ν := MonoidHom.ext fun χ => hτ χ.toAdd
  have e₁ := @s₄ F _ _ i₁ a _ (pw τ' hτ') q x rfl hq hqt hx
  have e₂ := @s₄ F _ _ i₂ a _ hτ' q' x' ha₂ hq' hqt' hx'
  rw [e₁, reassoc_of% e₂]
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing a
  let c : R →+* O := a.codRestrict O.toSubring hO
  have hc : IsLocalHom c := hloc
  obtain ⟨σ, hσ, hστ⟩ := exists_lift_valuationSubring O τ' hk0 hτ'
  have n₁ := s₂ O F c a O.subtype _ (pw σ hσ) _ (pw τ' hτ') rfl fun χ => (hστ (ν χ)).symm
  have n₂ := s₂ O F c a O.subtype _ hσ _ hτ' rfl fun χ => (hστ χ).symm
  suffices key : s O c _ (pw σ hσ) = s O c σ hσ ≫ f by
    rw [n₁, n₂, key, Over.comp_left, Category.assoc]
  have hkO : IsUnit (k : O) := by simpa using hk.map c
  refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap c) k hkO _ _ ?_
    (ResidueField O) (residue O) inferInstance ?_
  · rw [s₁, ← MonObj.pow_comp, s₁, MonObj.one_comp]
  let a₀ : R →+* ResidueField O := (residue O).comp c
  have ha₀ : ∀ r ∈ maximalIdeal R ^ (0 + 1), a₀ r = 0 := fun r hr => by
    rw [zero_add, pow_one] at hr
    exact (residue_eq_zero_iff _).2 (map_nonunit c r hr)
  let σ₀ : Multiplicative D.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp σ
  have hσ₀ : σ₀ ^ k = 1 := MonoidHom.ext fun χ => by
    have := DFunLike.congr_fun hσ χ
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this ⊢
    simp only [σ₀, MonoidHom.comp_apply, ← map_pow, this, map_one]
  have r₁ := s₂ O _ c a₀ (residue O) _ (pw σ hσ) _ (pw σ₀ hσ₀) rfl fun χ => rfl
  have r₂ := s₂ O _ c a₀ (residue O) _ hσ _ hσ₀ rfl fun χ => rfl
  have h₀ := isGrpPullback_pullback G (spMap a₀)
  let z : Over.mk (spMap (RingHom.id (ResidueField O))) ⟶ splitTorus (Sp (ResidueField O)) D.toPre.X :=
    (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
      ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp σ₀)
  have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (σ₀ (Multiplicative.ofAdd χ)) := fun χ => by
    simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]
    rfl
  have t₁ := s₃ _ _ a₀ ha₀ a₀ (RingHom.id _) _ _ h₀ _ (pw σ₀ hσ₀) (z ≫ GlobalTheory.SplitTorus.torusMap _ m) rfl
    fun χ => (chV_comp_torusMap z m χ).trans (hz _)
  have t₂ := s₃ _ _ a₀ ha₀ a₀ (RingHom.id _) _ _ h₀ _ hσ₀ z rfl hz
  have hf₀ : ((Over.pullback (spMap a₀)).map f).left ≫ pullback.fst G.hom (spMap a₀) =
      pullback.fst G.hom (spMap a₀) ≫ f.left := pullback.lift_fst _ _ _
  have hE := hm _ a₀ ha₀ _ _ h₀ _ hf₀
  rw [Over.comp_left, ← r₁, ← reassoc_of% r₂, t₁, t₂, Category.assoc z, ← hE, Category.assoc, ← hf₀]
  simp only [Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.TorEnd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem valF_spMap_comp {F F' : Type} [Field F] [Field F'] (σ : F →+* F') {X : Scheme.{0}} (x : Sp F ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valF (spMap σ ≫ x) U f = σ (valF x U f) := by
  classical
  have h' : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun y _ => h (show (spMap σ).base y ∈ (⊤ : (Sp F).Opens) from trivial)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ h le_top]
  exact congrArg (fun q => q.hom ((Scheme.Hom.appLE x U ⊤ h).hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem toStk_valF_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valF x U a) = gs x z U a := by
  classical
  rw [valF, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

variable {K : Type} [Field K] (k₀ : Subfield K) {X Y Y' : Scheme.{0}}

theorem valF_mem_of_defOver {x : Sp K ⟶ X} (hx : DefOver k₀ x) (U : X.Opens) (z : Sp K) (h : x z ∈ U)
    (a : Γ(X, U)) : valF x U a ∈ k₀ := by
  obtain ⟨P₀, rfl⟩ := hx
  have h₀ : ⊤ ≤ P₀ ⁻¹ᵁ U := (top_le_iff_mem P₀ U ((spMap k₀.subtype).base z)).2 h
  rw [valF_spMap_comp k₀.subtype P₀ U h₀ a]
  exact (valF P₀ U a).2

theorem gs_mem_of_defOver {x : Sp K ⟶ X} (hx : DefOver k₀ x) (U : X.Opens) (z : Sp K) (h : x z ∈ U)
    (a : Γ(X, U)) : ∃ c ∈ k₀, gs x z U a = toStk z c :=
  ⟨valF x U a, valF_mem_of_defOver k₀ hx U z h a, (toStk_valF_gs x U z h a).symm⟩

variable {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}

theorem val_mem_of_defOver (t : LB.Gen (LB.LinComb L φ ε)) {r : Sp K ⟶ Y} (hr : DefOver k₀ r) (z : Sp K)
    {J : (Sp K ⟶ X) → L.ι} (hJ : Good L z J) : ∃ c ∈ k₀, (val t r z J).val = toStk z c := by
  have hm := hJ.mem φ r
  obtain ⟨c, hc, e⟩ := gs_mem_of_defOver k₀ hr _ z hm (t.s fun k => J (r ≫ φ k)).val
  exact ⟨c, hc, (gs_unit r z _ hm _).symm.trans e⟩

end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory
variable {K : Type} [Field K] (k₀ : Subfield K)

theorem spMap_subtype_cancel {R : Type} [CommRing R] {a b : Sp k₀ ⟶ Sp R}
    (h : spMap k₀.subtype ≫ a = spMap k₀.subtype ≫ b) : a = b := by
  rw [← Spec.map_preimage a, ← Spec.map_preimage b] at h ⊢
  congr 1
  simp only [spMap, ← Spec.map_comp] at h
  have e := Spec.map_injective h
  ext y
  exact congrArg (fun q => q.hom y) e
end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
variable {K : Type} [Field K] (k₀ : Subfield K)

theorem defOver_comp {X Y : Scheme.{0}} {P : Sp K ⟶ X} (hP : DefOver k₀ P) (g : X ⟶ Y) : DefOver k₀ (P ≫ g) := by
  obtain ⟨P₀, rfl⟩ := hP
  exact ⟨P₀ ≫ g, (Category.assoc _ _ _).symm⟩

theorem defOver_spMap {R : Type} [CommRing R] (f : R →+* K) (hf : ∀ a, f a ∈ k₀) : DefOver k₀ (spMap f) :=
  ⟨spMap (f.codRestrict k₀ hf), by simp only [spMap, ← Spec.map_comp]; rfl⟩

theorem defOver_pullback {R : Type} [CommRing R] {A B : Scheme.{0}} {f : A ⟶ Sp R} {g : B ⟶ Sp R}
    {x : Sp K ⟶ pullback f g} (h₁ : DefOver k₀ (x ≫ pullback.fst f g)) (h₂ : DefOver k₀ (x ≫ pullback.snd f g)) :
    DefOver k₀ x := by
  obtain ⟨Q₁, hQ₁⟩ := h₁
  obtain ⟨Q₂, hQ₂⟩ := h₂
  have hw : Q₁ ≫ f = Q₂ ≫ g := spMap_subtype_cancel k₀ (by
    rw [← Category.assoc, hQ₁, ← Category.assoc, hQ₂, Category.assoc, Category.assoc, pullback.condition])
  refine ⟨pullback.lift Q₁ Q₂ hw, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, pullback.lift_fst, hQ₁]
  · rw [Category.assoc, pullback.lift_snd, hQ₂]

variable {X Y : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}

theorem val_spMap_mem {R : Type} [CommRing R] {L : LB X} {φ : Ix → (Sp R ⟶ X)} (t : LB.Gen (LB.LinComb L φ ε))
    (f : R →+* K) (hf : ∀ a, f a ∈ k₀) (z : Sp K) {J : (Sp K ⟶ X) → L.ι} (hJ : Good L z J) :
    ∃ c ∈ k₀, (val t (spMap f) z J).val = toStk z c :=
  val_mem_of_defOver k₀ t (defOver_spMap k₀ f hf) z hJ

end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMember
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMember
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Labels

theorem comp_pow_overScheme_grpObj {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, MonObj.comp_mul, ih, pow_succ]


open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in
theorem yy_hom : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu' v) (mu v))) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, -, he, -⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have tor : ∀ p y, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p y →
      y ^ (X₁.S.r * X₁.S.N) = 1 := fun p y h => by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (h w hw).1
  have uniq : ∀ a (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), y ^ (X₁.S.r * X₁.S.N) = 1 →
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left → y = x a := by
    intro a y hy hya
    obtain ⟨b, rfl⟩ := xonto y hy
    obtain ⟨c, -, hc⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V))
      (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK))
      ((Over.homMk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) (by simp) :
        Over.mk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) ⟶
          baseOver (Sp X₁.S.R)) ≫ X₁.ρ.pt a)
      (by rw [← comp_pow_overScheme_grpObj, (X₁.ρ.fr_tors a).1, MonObj.comp_one])
    have h1 := hc a rfl
    have h2 := hc b (by
      ext1
      simp only [Over.comp_left, Over.homMk_left]
      rw [← hx b, hya])
    rw [h1.trans h2.symm]
  have ex : ∀ a, ∃ p, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) :=
    fun a => by
      obtain ⟨p, hp⟩ := f₂ (x a) (he a).1
      exact ⟨p, (f₁ _ _).2 hp.symm⟩
  have yyI : ∀ a mu, 𝔪.YY a mu ↔ ∃ p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N),
      p.y = 𝔪.e₈ mu ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) := by
    intro a mu
    constructor
    · rintro ⟨p, y, hpy, hq, hov⟩
      obtain rfl := uniq a y (tor p y hq) hov
      exact ⟨p, hpy, hq⟩
    · rintro ⟨p, hpy, hq⟩
      exact ⟨p, x a, hpy, hq, hx a⟩
  refine ⟨fun a => ?_, fun mu => ?_, fun a mu mu' h => ?_, fun a a' mu mu' h h' => ?_⟩
  · obtain ⟨p, hp⟩ := ex a
    exact ⟨𝔪.e₈.symm p.y, (yyI a _).2 ⟨p, by simp, hp⟩⟩
  · obtain ⟨p, hp⟩ := exists_qkPt (F := AlgebraicClosure (FractionRing V)) hL.1.mulN (Or.inr hL.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) (by omega) (𝔪.e₈ mu)
    obtain ⟨a, ha⟩ := xonto (f p) (tor p _ ((f₁ _ _).2 rfl))
    exact ⟨a, (yyI a mu).2 ⟨p, hp, (f₁ _ _).2 ha.symm⟩⟩
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    rw [yyI]
    constructor
    · rintro ⟨p', hpy', hq'⟩
      have hpp : QkPt.Equiv _ _ p p' := (f₃ p p').1 (((f₁ _ _).1 hq).symm.trans ((f₁ _ _).1 hq'))
      obtain ⟨z, hz, -⟩ := (equiv_iff hB _ _).1 hpp
      have e' : mu' = mu + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, ← hpy, ← hpy', hz])
      intro v
      exact ⟨𝔪.e₈.symm z v, by rw [e']; rfl⟩
    · intro hc
      choose w hw using hc
      refine ⟨qkShift hB p (𝔪.e₈ w), ?_, (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB p _)))⟩
      show p.y + (X₁.S.r * X₁.S.N) • 𝔪.e₈ w = 𝔪.e₈ mu'
      rw [hpy, ← map_nsmul, ← map_add (f := _)]
      congr 1
      funext v
      exact (hw v).symm
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    obtain ⟨p', hpy', hq'⟩ := (yyI a' mu').1 h'
    refine (yyI _ _).2 ⟨qkAdd hB p p', ?_, ?_⟩
    · show p.y + p'.y = 𝔪.e₈ (mu + mu')
      rw [map_add (f := _), hpy, hpy']
    · rw [f₁, f₄ _ _ _ (qkAdd_qkAdd hB p p'), ← (f₁ _ _).1 hq, ← (f₁ _ _).1 hq', xadd]

end GlobalTheory.Poinc.Sep.Labels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMemberStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_labelHom_lattice_mod_level_thetaMember : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu' v) (mu v))) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  first | exact @GlobalTheory.Poinc.Sep.Labels.yy_hom | exact GlobalTheory.Poinc.Sep.Labels.yy_hom | (intros; apply GlobalTheory.Poinc.Sep.Labels.yy_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.QkClosure

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀]
  [Field F] [Algebra (FractionRing R) F] (f : F₀ →+* F)
  (hf : f.comp (algebraMap (FractionRing R) F₀) = algebraMap (FractionRing R) F)

theorem val_eq_of_ext {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((TF (R := R) F₀).left ⟶ D.P.A.left)}
    {ε : K → ℤ} {φ' : K' → ((TF (R := R) F₀).left ⟶ D.P.A.left)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (t' : LB.Gen (LB.LinComb D.P.L φ' ε'))
    (h : ∀ z J, Good D.P.L z J → val t (extMap (R := R) f hf).left z J = val t' (extMap (R := R) f hf).left z J)
    {y J} (hJ : Good D.P.L y J) : val t (𝟙 _) y J = val t' (𝟙 _) y J :=
  val_corr hJ (GlobalTheory.corr_of_val_field_extension _ _ f _ D.P.L D.P.isLB _ _ _ _ _ _ t t' h) _

theorem val_tau_ext (x χ : D.X) {z J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀)) (extMap (R := R) f hf).left z J = tauVal D F x χ z J := by
  rw [val_pull hJ, tauVal, ← extMap_jFK f hf]


include f hf in
theorem exists_isIota_of_ext {x : D.X} {h' : GtPtF D F} (hh' : GtPtF.IsIota x h') : ∃ g : GtPtF D F₀, GtPtF.IsIota x g := by
  obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 hh'
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀))
      (𝟙 (TF (R := R) F₀).left) y J = tauVal D F₀ x χ y J := fun χ y J hJ => val_pull hJ _ _ _
  obtain ⟨g, hb, hv⟩ := exists_gt (F := F₀) (cP D _ x) (fun χ => LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀))
    (fun χ => pullGen_isGen _ _ _ _ (tau_isGen D x χ) _) (fun χ U _ h => by
      have a : ∀ w : D.X, jFK (R := R) F₀ ≫ ptK (D.c w) = (cP D (TF (R := R) F₀) w).left := fun w =>
        (Category.assoc _ _ _).symm
      have a₀ : jFK (R := R) F₀ ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F₀ ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      rw [prod_gt, ← cPoint_add, add_comm χ x, ← a, ← a, ← a, ← a₀]
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, zpow_one]
      rw [mul_right_comm _ (h _) (h _)]) (fun y J hJ => by
      refine (val_eq_of_ext f hf _ (LB.oneGen D.P.L) (fun z J' hJ' => ?_) hJ).trans (val_one _)
      exact (val_tau_ext f hf x 0 hJ').trans ((v' 0 z J' hJ').symm.trans ((charVal_zero h' hJ').trans (val_one _).symm)))
    (fun χ χ' y J hJ => by
      refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ _ _ _))).symm.trans
        ((val_eq_of_ext f hf _ _ (fun z J' hJ' => ?_) hJ).trans (val_mul hJ _ _ _))
      have c := val_cub D.cub (extMap (R := R) f hf) hJ' (cP D _ χ) (cP D _ χ') (cP D _ x)
      rw [comp_cP, comp_cP, comp_cP] at c
      have e := charVal_add h' hJ' χ χ'
      rw [b', v' _ _ _ hJ', v' _ _ _ hJ', v' _ _ _ hJ'] at e
      refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
      exact (congrArg₂ (· * ·) (val_tau_ext f hf _ _ hJ') c).trans
        (e.trans (congrArg₂ (· * ·) (val_tau_ext f hf _ _ hJ') (val_tau_ext f hf _ _ hJ')).symm))
  exact ⟨g, (isIota_iff_val _ _).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩⟩

end GlobalTheory.QkClosure

namespace GlobalTheory.QkClosure

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀]
  [Field F] [Algebra (FractionRing R) F] (f : F₀ →+* F)
  (hf : f.comp (algebraMap (FractionRing R) F₀) = algebraMap (FractionRing R) F) {k : ℕ}

include hf

theorem isIota_gtExt {x : D.X} {h : GtPtF D F₀} (hh : GtPtF.IsIota x h) : GtPtF.IsIota x (gtExt D f hf h) := by
  obtain ⟨b, -⟩ := (isIota_iff_val _ _).1 hh
  refine (isIota_iff_val _ _).2 ⟨by rw [gtExt_b, b, comp_cP], fun χ y J hJ => ?_⟩
  rw [gtExt_val f hf _ χ hJ, tauVal, ← extMap_jFK f hf]
  exact (val_corr hJ (hh.2 χ) _).trans (val_pull hJ _ _ _)

theorem exists_qkExt (p : QkPt D F₀ k) : ∃ p' : QkPt D F k, QkExt f p p' := by
  obtain ⟨h, h₁, h₂⟩ := p.eq
  obtain rfl := (isNsmul_iff_eq _ _ _).1 h₁
  exact ⟨⟨p.y, gtExt D f hf p.g, gtExt D f hf (k • p.g), (isNsmul_iff_eq _ _ _).2 (map_nsmul _ _ _),
    isIota_gtExt f hf h₂⟩, rfl, (eq_gtExt_iff f hf _ _).1 rfl⟩

theorem qkExt_unique {p : QkPt D F₀ k} {p₁ p₂ : QkPt D F k} (h₁ : QkExt f p p₁) (h₂ : QkExt f p p₂) : p₁ = p₂ :=
  qk_ext (h₁.1.trans h₂.1.symm) (((eq_gtExt_iff f hf _ _).2 h₁.2).trans ((eq_gtExt_iff f hf _ _).2 h₂.2).symm)

theorem qkExt_inj {p₁ p₂ : QkPt D F₀ k} {p' : QkPt D F k} (h₁ : QkExt f p₁ p') (h₂ : QkExt f p₂ p') : p₁ = p₂ :=
  qk_ext (h₁.1.symm.trans h₂.1)
    (GlobalTheory.ArcExt.gtExt_injective f hf (((eq_gtExt_iff f hf _ _).2 h₁.2).symm.trans ((eq_gtExt_iff f hf _ _).2 h₂.2)))

theorem exists_qkExt_descent [IsAlgClosed F₀] [IsAlgClosed F] (hk : (k : F₀) ≠ 0) (p' : QkPt D F k) :
    ∃ p : QkPt D F₀ k, QkExt f p p' := by
  have hL : Laws := GlobalTheory.allSixLaws.1
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  obtain ⟨h', h₁', h₂'⟩ := p'.eq
  obtain rfl := (isNsmul_iff_eq _ _ _).1 h₁'
  obtain ⟨h₀, hh₀⟩ := exists_isIota_of_ext f hf h₂'
  have e₀ : gtExt D f hf h₀ = k • p'.g := isIota_unique (isIota_gtExt f hf hh₀) h₂'
  obtain ⟨g₀, hg₀⟩ := exists_nsmul_eq hL.mulN (Or.inr hL.polBaseChange) hk0 h₀
  have ht' : k • (p'.g - gtExt D f hf g₀) = 0 := by
    rw [nsmul_sub, ← map_nsmul, hg₀, e₀, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.ArcExt.exists_gtExt_of_torsion f hf hL hk _ ht'
  have ht0 : k • t = 0 := GlobalTheory.ArcExt.gtExt_injective f hf (by rw [map_nsmul, ht, ht', map_zero])
  have e : p'.g = gtExt D f hf (g₀ + t) := by rw [map_add (f := _), ht, add_sub_cancel]
  refine ⟨⟨p'.y, g₀ + t, h₀, (isNsmul_iff_eq _ _ _).2 ?_, hh₀⟩, rfl, (eq_gtExt_iff f hf _ _).1 e⟩
  rw [nsmul_add, ht0, add_zero, hg₀]

end GlobalTheory.QkClosure

namespace GlobalTheory.Mum

theorem qkPt_algClosure_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → (∀ p : QkPt D (Kb R) N, ∃! p' : QkPt D F N, QkExt em.toRingHom p p') ∧ ∀ p' : QkPt D F N, ∃! p : QkPt D (Kb R) N, QkExt em.toRingHom p p' := by
  intro R _ _ _ D F _ _ _ em N hN
  have hf := em.comp_algebraMap
  have : CharZero (Kb R) := (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  have hk : (N : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨fun p => ?_, fun p' => ?_⟩
  · obtain ⟨p', hp'⟩ := GlobalTheory.QkClosure.exists_qkExt em.toRingHom hf p
    exact ⟨p', hp', fun q hq => GlobalTheory.QkClosure.qkExt_unique em.toRingHom hf hq hp'⟩
  · obtain ⟨p, hp⟩ := GlobalTheory.QkClosure.exists_qkExt_descent em.toRingHom hf hk p'
    exact ⟨p, hp, fun q hq => GlobalTheory.QkClosure.qkExt_inj em.toRingHom hf hq hp⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → (∀ p : QkPt D (Kb R) N, ∃! p' : QkPt D F N, QkExt em.toRingHom p p') ∧ ∀ p' : QkPt D F N, ∃! p : QkPt D (Kb R) N, QkExt em.toRingHom p p' := by
  first | exact @GlobalTheory.Mum.qkPt_algClosure_bijective | exact GlobalTheory.Mum.qkPt_algClosure_bijective | (intros; apply GlobalTheory.Mum.qkPt_algClosure_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.UMin

theorem thG_smul_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S) (θ θ' : SecAt G L x) (p : Over.mk x ⟶ G) (a c c' : K), Odd m → (m : K) ≠ 0 → PolFib G L g x → SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ → ThG G L ρ m θ p (GlobalTheory.ZH.fn c) → (ThG G L ρ m θ' p (GlobalTheory.ZH.fn c') ↔ c' = a * c) := by
  intro S G _ _ L ρ hL hρ g m K _ x θ θ' p a c c' hm hmK hpol hθ H
  obtain ⟨P, φ, -, hp, w, hw⟩ := hpol
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', -, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  have hfn : ∀ u v : K, GlobalTheory.ZH.fn (u * v) = GlobalTheory.ZH.fn u * GlobalTheory.ZH.fn v := fun u v => map_mul _ u v
  have Ha : ThG G L ρ m θ' p (GlobalTheory.ZH.fn (a * c)) := by
    rw [hfn]; exact ThG.smul hL hθ H
  refine ⟨fun H' => ?_, fun h => h ▸ Ha⟩
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  have hτ : τ ≫ (Over.mk x).hom = (baseOver (Sp K)).hom ≫ x := rfl
  obtain ⟨z, hz, hz'⟩ := exists_torsion_down hp τ hτ p H.1
  obtain ⟨t', ht'⟩ := exists_secRel hp τ hτ hw hL hL₁ θ'
  have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom]
    exact (IsUnit.mk0 _ (by push_cast; exact pow_ne_zero _ hmK)).map _
  have q := ThG.unique abelianSchemeLaws_all.1 P hm hun (ThG.move hp τ hτ hw hL hL₁ hr hz hz' ht' H')
    (ThG.move hp τ hτ hw hL hL₁ hr hz hz' ht' Ha)
  have q' : GlobalTheory.ZH.fn c' = GlobalTheory.ZH.fn (a * c) := by simpa [τ] using q
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective q'

end GlobalTheory.UMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_unique_and_linear_in_section : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S) (θ θ' : SecAt G L x) (p : Over.mk x ⟶ G) (a c c' : K), Odd m → (m : K) ≠ 0 → PolFib G L g x → SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ → ThG G L ρ m θ p (GlobalTheory.ZH.fn c) → (ThG G L ρ m θ' p (GlobalTheory.ZH.fn c') ↔ c' = a * c) := by
  first | exact @GlobalTheory.UMin.thG_smul_iff | exact GlobalTheory.UMin.thG_smul_iff | (intros; apply GlobalTheory.UMin.thG_smul_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LabTrans

open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.ArcExt ReciprocityTheory.ChartRestriction.G.DVR

section Ext

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' F'' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] [Field F''] [Algebra (FractionRing R) F''] {k : ℕ}

theorem qkExt_trans {f : F →+* F'} {g : F' →+* F''} {p : QkPt D F k} {q : QkPt D F' k} {r : QkPt D F'' k}
    (h₁ : QkExt f p q) (h₂ : QkExt g q r) : QkExt (g.comp f) p r := by
  have hs : spMap (g.comp f) = spMap g ≫ spMap f := Geo.Tor.spMap_comp _ _
  refine ⟨h₂.1.trans h₁.1, by rw [h₂.2.1, h₁.2.1, hs, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine ((val_corr hJ (h₂.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h₁.2.2 χ) _).trans
    (val_pull hJ _ _ _)))).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  exact congrArg (fun s => val (p.g.s χ) s y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hs.symm))

theorem qkExt_inj (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') {p q : QkPt D F k} {r : QkPt D F' k}
    (h₁ : QkExt f.toRingHom p r) (h₂ : QkExt f.toRingHom q r) : p = q := by
  have e := ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₁).symm.trans ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₂)
  exact qk_ext (congrArg QkPt.y e :) (gtExt_injective _ f.comp_algebraMap (congrArg QkPt.g e))

theorem exists_ext (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') (p : QkPt D F k) : ∃ r, QkExt f.toRingHom p r :=
  ⟨_, (qkExt_iff hB _ f.comp_algebraMap _ _).2 rfl⟩

theorem ext_unique (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') {p : QkPt D F k} {r r' : QkPt D F' k}
    (h₁ : QkExt f.toRingHom p r) (h₂ : QkExt f.toRingHom p r') : r = r' :=
  ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₁).trans ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₂).symm

theorem exists_of_ext [CharZero R] [IsAlgClosed F] [IsAlgClosed F'] (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F')
    (hk : 1 ≤ k) (r : QkPt D F' k) : ∃ p : QkPt D F k, QkExt f.toRingHom p r := by
  have : CharZero F := (RingHom.charZero_iff (algebraMap (FractionRing R) F).injective).1 inferInstance
  obtain ⟨p, hp⟩ := exists_qkExt f.toRingHom f.comp_algebraMap hB GlobalTheory.firstFiveLaws.1 (Nat.cast_ne_zero.2 (by omega)) r
  exact ⟨p, (qkExt_iff hB _ f.comp_algebraMap _ _).2 hp.symm⟩

end Ext

theorem exists_lift_pt {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ga : FractionRing R →+* FractionRing R'}
    {A : Over (Sp (FractionRing R))} {A' : Over (Sp (FractionRing R'))} {a : A'.left ⟶ A.left}
    (h : IsPullback a A'.hom A.hom (spMap ga)) {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F'] (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = (algebraMap _ F').comp ga)
    (x : TFK (R := R) F ⟶ A) : ∃ x' : TFK (R := R') F' ⟶ A', x'.left ≫ a = spMap f ≫ x.left := by
  have w : (spMap f ≫ x.left) ≫ A.hom = jFK (R := R') F' ≫ spMap ga := by
    rw [Category.assoc, Over.w x]
    exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap hf).trans (Geo.Tor.spMap_comp _ _))
  exact ⟨Over.homMk (h.lift _ _ w) (h.lift_snd _ _ w), h.lift_fst _ _ w⟩

theorem eq_fracMap {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    (hφ : Function.Injective φ) {ga : FractionRing R →+* FractionRing R'}
    (h : ∀ r, ga (algebraMap R _ r) = algebraMap R' _ (φ r)) : ga = fracMap hφ :=
  IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (h r).trans (fracMap_algebraMap hφ r).symm)

theorem exists_fib_cancel {S S' S₀ S₁ : Scheme.{0}} {A : PolAV S} {A' : PolAV S'} {A₀ : PolAV S₀} {A₁ : PolAV S₁}
    {f : S' ⟶ S} {f₀ : S₀ ⟶ S} {g : S₁ ⟶ S₀} {g' : S₁ ⟶ S'} (sq : g' ≫ f = g ≫ f₀)
    {a : A'.A.left ⟶ A.A.left} {a₀ : A₀.A.left ⟶ A.A.left} {b : A₁.A.left ⟶ A₀.A.left}
    (ha : IsGrpPullback A'.A A.A f a) (la : LBIso A'.L (A.L.pull a))
    (ha₀ : IsGrpPullback A₀.A A.A f₀ a₀) (la₀ : LBIso A₀.L (A.L.pull a₀))
    (hb : IsGrpPullback A₁.A A₀.A g b) (lb : LBIso A₁.L (A₀.L.pull b)) :
    ∃ a₁ : A₁.A.left ⟶ A'.A.left, a₁ ≫ a = b ≫ a₀ ∧ IsGrpPullback A₁.A A'.A g' a₁ ∧ LBIso A₁.L (A'.L.pull a₁) := by
  have n := (hb.comp ha₀).congr sq.symm rfl
  have w : (b ≫ a₀) ≫ A.A.hom = (A₁.A.hom ≫ g') ≫ f := n.1.w.trans (Category.assoc _ _ _).symm
  have e := ha.1.lift_fst _ _ w
  refine ⟨ha.1.lift _ _ w, e, IsGrpPullback.cancel ha (n.congr rfl e.symm) (ha.1.lift_snd _ _ w), ?_⟩
  have l₁ : LBIso (A₀.L.pull b) (A.L.pull (b ≫ a₀)) :=
    la₀.chartPull (Geo.Tor.chartPullPull A₀.L _ _ rfl)
      (chartPullSame A.L (fun _ : PUnit => b ≫ a₀) (fun _ => a₀) _ b fun _ => rfl)
  have l₂ : LBIso (A'.L.pull (ha.1.lift _ _ w)) (A.L.pull (b ≫ a₀)) :=
    la.chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl)
      (chartPullSame A.L (fun _ : PUnit => b ≫ a₀) (fun _ => a) _ _ fun _ => e.symm)
  exact LBIso.trans A₁.isLB (pull_isLB A.isLB _) (pull_isLB A'.isLB _)
    (LBIso.trans A₁.isLB (pull_isLB A₀.isLB _) (pull_isLB A.isLB _) lb l₁) l₂.symm

theorem nonempty_lift (K F : Type) [Field K] [Field F] [IsAlgClosed F] [Algebra K F] :
    Nonempty (AlgebraicClosure K →ₐ[K] F) := ⟨IsAlgClosed.lift⟩

end GlobalTheory.LabTrans

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHom
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.HomTor

theorem pow_comp_monHom {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem exists_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G), IsMonHom p → ∃ ρ, TorMatch U U' (RingHom.id R) p.left ρ := by
  intro R _ _ _ hR G _ _ hG D A U G' _ _ hG' D' A' U' p hpm
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have hp' := isGrpPullback_pullback G' (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G'.hom (spMap (residue R)) ≫ p.left := pullback.lift_fst _ _ _
  have hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map p) :=
    Out.PullGtPf.isMonHom_of_grpPullback hp' hp p _ e
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _
    (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p) inferInstance
  refine ⟨ρ, ?_⟩
  intro F _ _ i₁ i₂ hF k hk τ τ' q q' a a' hτ'k hττ' hqy hq hq'y hq' ha ha'
  have hi : i₁ = i₂ := Algebra.algebra_ext _ _ fun x =>
    RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R)
      (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext hF)) x
  subst hi
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.ToricTorsionUnif.main R hR G' hG' D' A' U' k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {H : Type} [CommGroup H] (f : Multiplicative D'.toPre.X →* H), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  let c : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  rw [s4 F c τ hτk q a rfl hqy hq ha, ← Category.assoc, s4' F c τ' hτ'k q' a' rfl hq'y hq' ha']
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing c
  let φ : R →+* O := c.codRestrict O.toSubring hO
  haveI : IsLocalHom φ := hloc
  have hc : c = O.subtype.comp φ := rfl
  obtain ⟨τO, hτO⟩ := GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl
  let τR := τO.comp ρm
  have hτR : τR ^ k = 1 := powc τO hτOk
  have hkO : IsUnit (k : O) := by simpa using hk.map φ
  have hxy : s O φ τR hτR = s' O φ τO hτOk ≫ p := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap φ) k hkO _ _ ?_
      (ResidueField O) (residue O) inferInstance ?_
    · rw [s1, ← pow_comp_monHom, s1', MonObj.one_comp]
    · let τ₀ : Multiplicative D'.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp τO
      have h₀ : τ₀ ^ k = 1 := by
        rw [show τ₀ ^ k = (Units.map (residue O).toMonoidHom).comp (τO ^ k) by ext x; simp [τ₀]]
        rw [hτOk]; ext; simp
      let τ₁ := τ₀.comp ρm
      have h₁ : τ₁ ^ k = 1 := powc τ₀ h₀
      let z : Over.mk (spMap (ResidueField.map φ)) ⟶ splitTorus (Sp (ResidueField R)) D'.toPre.X :=
        (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
          ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp τ₀)
      have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]; rfl
      have hz₁ : ∀ χ, GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap _ ρ) χ = unitOn (τ₁ (Multiplicative.ofAdd χ)) :=
        fun χ => by
          apply Units.ext
          rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
            GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
            ← GlobalTheory.UU.chV_val, hz]
          rfl
      have hres : (residue O).comp φ = (ResidueField.map φ).comp (residue R) := by
        ext r; simp [ResidueField.map_residue]
      rw [Over.comp_left, ← Category.assoc,
        ← s2 O _ φ ((residue O).comp φ) (residue O) τR hτR τ₁ h₁ rfl (fun χ => rfl),
        ← s2' O _ φ ((residue O).comp φ) (residue O) τO hτOk τ₀ h₀ rfl (fun χ => rfl),
        s3 _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp τ₁ h₁ _ hres hz₁,
        s3' _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp' τ₀ h₀ z hres hz,
        Category.assoc z, ← hρ, Category.assoc _ _ p.left, ← e]
      simp only [Over.comp_left, Category.assoc]
  rw [s2 O F φ c O.subtype τR hτR τ hτk hc (fun χ => by simp [τR, hτ, hτO]),
    s2' O F φ c O.subtype τO hτOk τ' hτ'k hc (fun χ => by simp [hτO]), hxy, Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.HomTor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroups
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two


open GlobalTheory.EndData GlobalTheory.AbLaw in
theorem exists_hom_of_levels {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {I : Ideal R}
    (hC : IsAdicComplete I R) (Y Z : Over (Spec (CommRingCat.of R))) (sY : Smooth Y.hom) (sZ : Smooth Z.hom)
    (pY : IsProjBy Y.hom) (pZ : IsProjBy Z.hom) (s : Y ⟶ Z) (f : ∀ e, (thickObj R I e Y).left ⟶ Z.left)
    (hf : ∀ e, f e ≫ Z.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom)
    (hc : ∀ e, thickMap R I e Y ≫ f (e + 1) = f e) :
    ∃ g : Y ⟶ Z, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  have w₁ : (fst Y Z).left ≫ Y.hom = (Y ⊗ Z).hom := Over.w _
  have w₂ : (snd Y Z).left ≫ Z.hom = (Y ⊗ Z).hom := Over.w _
  have sm : Smooth (Y ⊗ Z).hom := by
    show Smooth (pullback.fst Y.hom Z.hom ≫ Y.hom)
    infer_instance
  let p : ∀ e, (thickObj R I e (Y ⊗ Z)).left ⟶ (thickObj R I e Y).left := fun e =>
    ((Over.pullback (thick R I e)).map (fst Y Z)).left
  have hp : ∀ e, p e ≫ pullback.fst Y.hom (thick R I e) = pullback.fst (Y ⊗ Z).hom (thick R I e) ≫ (fst Y Z).left :=
    fun e => map_fst e _
  let F : ∀ e, (thickObj R I e (Y ⊗ Z)).left ⟶ pullback Y.hom Z.hom := fun e =>
    pullback.lift (p e ≫ pullback.fst Y.hom (thick R I e)) (p e ≫ f e) (by
      rw [Category.assoc, Category.assoc, hf])
  have F₁ : ∀ e, F e ≫ pullback.fst _ _ = p e ≫ pullback.fst Y.hom (thick R I e) := fun e => pullback.lift_fst _ _ _
  have F₂ : ∀ e, F e ≫ pullback.snd _ _ = p e ≫ f e := fun e => pullback.lift_snd _ _ _
  have tp : ∀ e, thickMap R I e (Y ⊗ Z) ≫ p (e + 1) = p e ≫ thickMap R I e Y := fun e => trans_map e _
  obtain ⟨g, hg⟩ := EndAlg.exists_end_of_thickenings R I hC (Y ⊗ Z) sm (isProjBy_tensor R Y Z pY pZ) F
    (fun e => by
      show F e ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = _
      rw [← Category.assoc, F₁, hp, Category.assoc, w₁])
    (fun e => by
      show (thickMap R I e (Y ⊗ Z) ≫ F (e + 1) : _ ⟶ pullback Y.hom Z.hom) = F e
      apply pullback.hom_ext
      · rw [Category.assoc, F₁, F₁, ← Category.assoc, tp, Category.assoc, trans_fst]
      · rw [Category.assoc, F₂, F₂, ← Category.assoc, tp, Category.assoc, hc])
  refine ⟨lift (𝟙 Y) s ≫ g ≫ snd Y Z, fun e => ?_⟩
  have hj : ((Over.pullback (thick R I e)).map (lift (𝟙 Y) s)).left ≫ p e = 𝟙 _ := by
    show ((Over.pullback (thick R I e)).map (lift (𝟙 Y) s) ≫ (Over.pullback (thick R I e)).map (fst Y Z)).left = _
    rw [← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id]
    rfl
  have k : F e ≫ (snd Y Z).left = p e ≫ f e := F₂ e
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← map_fst, Category.assoc,
    ← Category.assoc (pullback.fst _ _), hg]
  erw [k]
  rw [← Category.assoc]
  erw [hj]
  exact Category.id_comp _


open GlobalTheory.EndTorus in
theorem exists_abelian_level {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    {D₁ D₂ : DegPre R} {e : ℕ} {G₁ G₂ : Over (Spec (CommRingCat.of R))} [GrpObj G₁] [IsCommMonObj G₁]
    [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a] :
    ∃ b : thickObj R I e D₁.P.A ⟶ thickObj R I e D₂.P.A, IsMonHom b ∧ g₁.q ≫ b = a ≫ g₂.q := by
  obtain ⟨hN, -, -, hC⟩ := hR
  have := g₁.q_hom
  have := g₂.q_hom
  have := g₁.i_hom
  have := g₁.q_flat
  have := g₁.q_surj
  have := g₁.q_affine
  have : IsProper D₂.P.A.hom := D₂.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D₂.P.A) :=
    { comm := inferInstance
      smooth := by have := D₂.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D₂.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g₁.i ≫ a ≫ g₂.q = toUnit _ ≫ η[thickObj R I e D₂.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D₁.X _ hB (g₁.i ≫ a ≫ g₂.q) inferInstance).trans (Hom.one_def)
  exact FlatQuotient.exists_desc g₁.q g₁.i (a ≫ g₂.q) g₁.isKernel h1


open GlobalTheory.EndData in
theorem exists_abelian_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ b : D₁.toPre.P.A ⟶ D₂.toPre.P.A, IsMonHom b ∧ Over₀ U₁ U₂ a b := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a ha
  have hN := hR.1
  have hC := hR.2.2.2
  choose b hb hq using fun e => exists_abelian_level hR (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a)
  have hql : ∀ e, (U₁.gt e).q.left ≫ (b e).left = ((Over.pullback (thick R I e)).map a).left ≫ (U₂.gt e).q.left :=
    fun e => congrArg (·.left) (hq e)
  obtain ⟨aB, haB⟩ := exists_hom_of_levels hC D₁.toPre.P.A D₂.toPre.P.A D₁.toPre.P.isAb.smooth
    D₂.toPre.P.isAb.smooth (AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _))
    (AbProj.isProjBy_of_isPullback D₂.toPre.P (IsPullback.id_horiz _)) 1
    (fun e => (b e).left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e))
    (fun e => by
      have w : (b e).left ≫ pullback.snd D₂.toPre.P.A.hom (thick R I e) = pullback.snd _ _ := Over.w (b e)
      rw [Category.assoc, pullback.condition, ← Category.assoc, w, pullback.condition])
    (fun e => by
      have := (U₁.gt e).q_flat
      have := (U₁.gt e).q_surj
      have : Epi (U₁.gt e).q.left := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi (U₁.gt e).q.left, ← Category.assoc, ← UnifCompare.trans_comp_q, Category.assoc,
        ← Category.assoc (U₁.gt (e + 1)).q.left, hql, ← Category.assoc (U₁.gt e).q.left, hql, ← Category.assoc,
        ← Category.assoc, trans_map, Category.assoc _ (thickMap R I e G₂), UnifCompare.trans_comp_q,
        Category.assoc, Category.assoc, trans_fst, Category.assoc])
  have hm : ∀ e, (Over.pullback (thick R I e)).map aB = b e := fun e =>
    Over.OverMorphism.ext (pullback.hom_ext ((map_fst e aB).trans (haB e)) ((Over.w _).trans (Over.w (b e)).symm))
  refine ⟨aB, AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D₂.toPre.P.isAb
    D₁.toPre.P.isAb aB fun e => ?_, fun e => ?_⟩
  · rw [hm]; exact hb e
  · rw [hm]; exact (hq e).symm

end GlobalTheory.Mum.Two
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroupsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianPart_hom_uniformisedGroups : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ b : D₁.toPre.P.A ⟶ D₂.toPre.P.A, IsMonHom b ∧ Over₀ U₁ U₂ a b := by
  first | exact @GlobalTheory.Mum.Two.exists_abelian_hom | exact GlobalTheory.Mum.Two.exists_abelian_hom | (intros; apply GlobalTheory.Mum.Two.exists_abelian_hom <;> assumption)
end
end
