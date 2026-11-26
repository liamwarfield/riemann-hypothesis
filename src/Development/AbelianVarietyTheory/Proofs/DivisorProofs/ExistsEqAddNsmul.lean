module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TorUniq

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem eq_zero_of_forall_dvd {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {l : ℕ} (hl : 2 ≤ l)
    (v : X) (h : ∀ n : ℕ, ∃ z : X, v = (l ^ n) • z) : v = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective ?_
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  obtain ⟨N, hN⟩ : ∃ N, N = (b.repr v i).natAbs := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ := h N
  have hd : ((l ^ N : ℕ) : ℤ) ∣ b.repr v i :=
    ⟨b.repr z i, by rw [hz, ← natCast_zsmul, map_zsmul, Finsupp.smul_apply, smul_eq_mul]⟩
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd ?_
  rw [Int.natAbs_natCast, ← hN]
  exact Nat.lt_pow_self (by omega)

theorem exists_eq_add_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {F : Type} [Field F]
    {k : ℕ} {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ k) {u v : X}
    (h : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd u) = τ (Multiplicative.ofAdd v)) :
    ∃ z : X, v = u + k • z := by
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, ∃ c : ℤ, b.repr (v - u) i = k * c := fun i => by
    let τ : Multiplicative X →* Fˣ := (zpowersHom Fˣ ζ).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
    have e : ζ ^ (b.repr u i) = ζ ^ (b.repr v i) := h τ (MonoidHom.ext fun x => by
      show (ζ ^ (b.coord i x.toAdd)) ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow])
    refine (hζ.zpow_eq_one_iff_dvd _).1 ?_
    rw [map_sub, Finsupp.sub_apply, zpow_sub, e, mul_inv_cancel]
  choose c hc using key
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (v - u), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul, natCast_zsmul]

end GlobalTheory.Poinc.TorUniq

namespace GlobalTheory.Poinc.Eq8

open GlobalTheory.Poinc.TorUniq

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem torMatch_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → ∀ ρ ρ', TorMatch U U' g β ρ → TorMatch U U' g β ρ' → ρ = ρ' := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hg ρ ρ' h h'
  have hL := GlobalTheory.firstFiveLaws
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V (FractionRing V)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r) := IsFractionRing.lift_algebraMap _
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing V) F).comp gK).toAlgebra
  have hF : ∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r)) :=
    fun r => congrArg (algebraMap (FractionRing V) F) (hgK r)

  have img : ∀ {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S], GlobalTheory.Mum.Base S → ∀ {H : Over (Sp S)} [GrpObj H]
      [IsCommMonObj H], IsSemiAbelian H → ∀ {E : DegData S (maximalIdeal S)} {B : PolAV (Sp (FractionRing S))}
      (W : Unif (maximalIdeal S) E B H) [Algebra (FractionRing S) F] (k : ℕ), 1 ≤ k → ∀ p : QkPt E.toPre F k,
      ∃ x : TFK (R := S) F ⟶ B.A, QkToAkU W.toUnifPre F k p x := by
    intro S _ _ _ hS H _ _ hH E B W _ k hk p
    obtain ⟨x, hx⟩ := GlobalTheory.TorsionAnyChar.existsTransl_any hL S (maximalIdeal S) hS.1 E B H hH W F k hk p
    exact ⟨x, (GlobalTheory.TorsionAnyChar.indAtTransl_any hL S (maximalIdeal S) hS.1 E B H hH W F k hk p x).1
      (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩

  have key : ∀ k : ℕ, IsUnit (k : R) → ∀ τ' : Multiplicative D'.toPre.X →* Fˣ, τ' ^ k = 1 →
      ∀ χ, τ' (Multiplicative.ofAdd (ρ χ)) = τ' (Multiplicative.ofAdd (ρ' χ)) := by
    intro k hk τ' hτ' χ
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    let τ₁ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ)
    let τ₂ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ')
    obtain ⟨q₁, y₁, t₁⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (F := F) (k := k) τ₁
      (MonoidHom.ext fun χ => DFunLike.congr_fun hτ' _)
    obtain ⟨q₂, y₂, t₂⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (F := F) (k := k) τ₂
      (MonoidHom.ext fun χ => DFunLike.congr_fun hτ' _)
    obtain ⟨q', y', t'⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D'.tau_bimult (F := F) (k := k) τ' hτ'
    obtain ⟨a₁, ha₁⟩ := img hR hG U k hk1 q₁
    obtain ⟨a₂, ha₂⟩ := img hR hG U k hk1 q₂
    obtain ⟨a', ha'⟩ := img hV hG' U' k hk1 q'
    have e₁ := h F hF k hk τ₁ τ' q₁ q' a₁ a' hτ' (fun _ => rfl) y₁ t₁ y' t' ha₁ ha'
    have e₂ := h' F hF k hk τ₂ τ' q₂ q' a₂ a' hτ' (fun _ => rfl) y₂ t₂ y' t' ha₂ ha'
    have e : a₁.left ≫ genMap U = a₂.left ≫ genMap U := e₁.trans e₂.symm

    have ea : a₁ = a₂ := by
      refine Over.OverMorphism.ext ?_
      have e' : a₁.left ≫ U.gen.inv.left = a₂.left ≫ U.gen.inv.left := by
        refine pullback.hom_ext ?_ ?_
        · simpa only [genMap, Category.assoc] using e
        · have w₁ := Over.w U.gen.inv
          have s : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := w₁
          rw [Category.assoc, Category.assoc, s, Over.w a₁, Over.w a₂]
      simpa using congrArg (· ≫ U.gen.hom.left) e'
    subst ea
    obtain ⟨z, hz, hh, hι, hadd⟩ := GlobalTheory.TorsionMapInj.qkToAk_injective_closed R (maximalIdeal R) hR.1 D A G hG U F k hk1
      q₁ q₂ a₁ ha₁ ha₂
    have hz0 : z = 0 := by
      rw [y₁, y₂, zero_add, eq_comm, ← natCast_zsmul] at hz
      exact (smul_eq_zero.1 hz).resolve_left (by exact_mod_cast hk0)
    subst hz0
    rw [GlobalTheory.TorusExt.isIota_iff_eq D.tau_bimult, map_zero] at hι
    subst hι
    rw [GlobalTheory.TorusExt.isAdd_iff_eq, add_zero] at hadd
    rw [hadd] at t₂
    have u := ((GlobalTheory.TorsionAnyChar.gtOnto_any hL R (maximalIdeal R) hR.1 D F).2.2.2.1 q₁.g t₁.1).unique t₁ t₂
    exact congrArg Units.val (DFunLike.congr_fun u (Multiplicative.ofAdd χ)) |> Units.ext
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  refine AddMonoidHom.ext fun χ => ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_dvd hl2 _ fun n => ?_
  have hk : IsUnit ((l ^ n : ℕ) : R) := by simpa using hl.pow n
  have hkF : ((l ^ n : ℕ) : F) ≠ 0 := by
    have := hk.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))
    rw [map_natCast] at this
    exact this.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : F) := ⟨hkF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (l ^ n)
  have hn0 : l ^ n ≠ 0 := pow_ne_zero _ (by omega)
  obtain ⟨z, hz⟩ := exists_eq_add_nsmul (ζ := (hζ.isUnit hn0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ)
    (key (l ^ n) hk · · χ)
  exact ⟨-z, by rw [hz, smul_neg]; abel⟩

end GlobalTheory.Poinc.Eq8
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonBaseChangePolarizedAbelianSchemeOfGe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonBaseChangePolarizedAbelianSchemeOfGe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Extend

theorem exists_factor {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U} [GrpObj G] [GrpObj G'] [GrpObj A]
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {a : A.left ⟶ G.left} (hb : IsGrpPullback G' G f b)
    (ha : IsGrpPullback A G (j ≫ f) a) : ∃ c : A.left ⟶ G'.left, IsGrpPullback A G' j c ∧ c ≫ b = a := by
  have w : a ≫ G.hom = (A.hom ≫ j) ≫ f := by rw [Category.assoc]; exact ha.1.w
  exact ⟨hb.1.lift _ _ w, hb.cancel (ha.congr rfl (hb.1.lift_fst _ _ w).symm) (hb.1.lift_snd _ _ w),
    hb.1.lift_fst _ _ w⟩

theorem exists_end {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U}
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {c : A.left ⟶ G'.left} (hb : IsPullback b G'.hom G.hom f)
    (hc : c ≫ G'.hom = A.hom ≫ j) (e₀ : G ⟶ G) (e : A ⟶ A) (h : e.left ≫ c ≫ b = (c ≫ b) ≫ e₀.left) :
    ∃ e' : G' ⟶ G', e'.left ≫ b = b ≫ e₀.left ∧ c ≫ e'.left = e.left ≫ c := by
  have w : (b ≫ e₀.left) ≫ G.hom = G'.hom ≫ f := by rw [Category.assoc, Over.w, hb.w]
  refine ⟨Over.homMk (hb.lift _ _ w) (hb.lift_snd _ _ w), hb.lift_fst _ _ w, hb.hom_ext ?_ ?_⟩
  · show (c ≫ hb.lift _ _ w) ≫ b = _
    rw [Category.assoc, hb.lift_fst, Category.assoc, h, Category.assoc]
  · show (c ≫ hb.lift _ _ w) ≫ _ = _
    rw [Category.assoc, hb.lift_snd, Category.assoc, hc, ← Category.assoc, Over.w]

theorem exists_sec {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U}
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {c : A.left ⟶ G'.left} (hb : IsPullback b G'.hom G.hom f)
    (hc : c ≫ G'.hom = A.hom ≫ j) (t : S ⟶ G.left) (ht : t ≫ G.hom = 𝟙 S) (w : U ⟶ A.left)
    (h : w ≫ c ≫ b = (j ≫ f) ≫ t) :
    ∃ s : S' ⟶ G'.left, s ≫ b = f ≫ t ∧ s ≫ G'.hom = 𝟙 S' ∧ ((w ≫ A.hom) ≫ j) ≫ s = w ≫ c := by
  have u : (f ≫ t) ≫ G.hom = 𝟙 S' ≫ f := by rw [Category.assoc, ht, Category.comp_id, Category.id_comp]
  have k : ((w ≫ A.hom) ≫ j) ≫ f = j ≫ f := by
    have := congrArg (· ≫ G.hom) h
    simp only [Category.assoc, ht, Category.comp_id, hb.w, reassoc_of% hc] at this
    simpa only [Category.assoc] using this
  refine ⟨hb.lift _ _ u, hb.lift_fst _ _ u, hb.lift_snd _ _ u, hb.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hb.lift_fst, ← Category.assoc, k, Category.assoc w, h]
  · rw [Category.assoc, hb.lift_snd, Category.comp_id, Category.assoc w c, hc, Category.assoc]

theorem lbIso_of_generic {O Ω : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] (H : Over (Sp O)) [GrpObj H]
    (hH : IsAbelianScheme H) {X : Scheme.{0}} {p : X ⟶ Sp Ω} {c : X ⟶ H.left}
    (hc : IsPullback c p H.hom (spMap (algebraMap O Ω))) {L L' : LB H.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : LBIso (L.pull c) (L'.pull c)) : LBIso L L' := by
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp O) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have : IsPreimmersion (spMap (algebraMap O Ω)) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have : Flat (spMap (algebraMap O Ω)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors O))
  have : IsDominant (spMap (algebraMap O Ω)) := by
    obtain ⟨_, _⟩ := (IsGenericPointHom.fractionField O Ω).quasiCompact_and_dominant
    infer_instance
  have : QuasiCompact (spMap (algebraMap O Ω)) := inferInstance
  have := hH.smooth
  have := geometricallyIntegral_of_isAbelianScheme H
  refine (GlobalTheory.CechPic.cls_eq_iff hL hL').1
    (GlobalTheory.ZH.EndoExtend.pic_ext (spMap (algebraMap O Ω)) hn H (eSec H) (Over.w η[H]) ?_ ?_)
  · rw [GlobalTheory.DualOpen.pic_sp_local_eq_zero O (GlobalTheory.CechPic.pull (eSec H) _)]
    exact (GlobalTheory.DualOpen.pic_sp_local_eq_zero O (GlobalTheory.CechPic.pull (eSec H) _)).symm
  · exact (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).2
      (GenSpread.lbIso_pull_comp hc.isoPullback.inv hc.isoPullback_inv_fst.symm hc.isoPullback_inv_fst.symm h)

end GlobalTheory.Poinc.Extend


open GlobalTheory.Poinc.Extend in
theorem GlobalTheory.Poinc.sameAt_of_generic : ∀ (O Ω R₁ R₂ M Γ : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R₁] [CommRing R₂] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* O) (f₂ : R₂ →+* O) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), SameAt P₁ P₂ ((algebraMap O Ω).comp f₁) ((algebraMap O Ω).comp f₂) e₁ e₂ t₁ t₂ → SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ := by
  intro O Ω R₁ R₂ M Γ _ _ _ _ _ _ _ _ _ _ P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ ⟨P, a₁, a₂, h₁, h₂, l₁, l₂, hE, hx⟩
  have spc : ∀ {R : Type} [CommRing R] (f : R →+* O),
      spMap ((algebraMap O Ω).comp f) = spMap (algebraMap O Ω) ≫ spMap f := fun f => by
    rw [← Spec.map_comp]; rfl
  rw [spc] at h₁ h₂
  simp only [spc] at hx
  obtain ⟨Q₁, b₁, g₁, m₁⟩ : ∃ (Q : PolAV (Sp O)) (b : Q.A.left ⟶ P₁.A.left),
      IsGrpPullback Q.A P₁.A (spMap f₁) b ∧ LBIso Q.L (P₁.L.pull b) :=
    ⟨StrictPull.polPull P₁ (spMap f₁), _, isGrpPullback_pullback _ _,
      PolBaseChange.lbIso_refl (pull_isLB P₁.isLB _)⟩
  obtain ⟨Q₂, b₂, g₂⟩ : ∃ (Q : PolAV (Sp O)) (b : Q.A.left ⟶ P₂.A.left),
      IsGrpPullback Q.A P₂.A (spMap f₂) b :=
    ⟨StrictPull.polPull P₂ (spMap f₂), _, isGrpPullback_pullback _ _⟩
  obtain ⟨c₁, k₁, rfl⟩ := exists_factor g₁ h₁
  obtain ⟨c₂, k₂, rfl⟩ := exists_factor g₂ h₂
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp O) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have hj : IsGenericPointHom (spMap (algebraMap O Ω)) := IsGenericPointHom.fractionField O Ω
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  have s₁ := isSemiAbelian_of_isAbelianScheme Q₁.A Q₁.isAb
  have s₂ := isSemiAbelian_of_isAbelianScheme Q₂.A Q₂.isAb
  have := s₁.smooth
  have := s₂.smooth
  have := s₁.separated
  have := s₂.separated
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₁ s₂ k₁ k₂ (𝟙 P.A)
  obtain ⟨F', ⟨-, eF'⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₂ s₁ k₂ k₁ (𝟙 P.A)
  rw [Over.id_left, Category.id_comp] at eF eF'
  let I : Q₁.A ≅ Q₂.A :=
    ⟨F, F', ExtUnique.over_hom_ext_of_isPullback k₁.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF, ← eF', Over.id_left, Category.comp_id]),
      ExtUnique.over_hom_ext_of_isPullback k₂.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF', ← eF, Over.id_left, Category.comp_id])⟩
  have : IsMonHom I.hom := hF
  have g₂' : IsGrpPullback Q₁.A P₂.A (spMap f₂) (F.left ≫ b₂) :=
    ((isGrpPullback_of_iso I).comp g₂).congr (Category.id_comp _) rfl
  refine ⟨Q₁, b₁, F.left ≫ b₂, g₁, g₂', m₁, ?_, fun E => ?_, fun x => ?_⟩
  · refine lbIso_of_generic Q₁.A Q₁.isAb k₁.1 Q₁.isLB (pull_isLB P₂.isLB _) ?_
    refine LBIso.trans (pull_isLB Q₁.isLB _) (pull_isLB P₁.isLB _) (pull_isLB (pull_isLB P₂.isLB _) _)
      (GenSpread.lbIso_pull_of_lbIso m₁ c₁ rfl) ?_
    refine LBIso.trans (pull_isLB P₁.isLB _) P.isLB (pull_isLB (pull_isLB P₂.isLB _) _) l₁.symm ?_
    exact LBIso.trans P.isLB (pull_isLB P₂.isLB _) (pull_isLB (pull_isLB P₂.isLB _) _) l₂
      (GenSpread.lbIso_pull_pull P₂.isLB c₁ (by rw [eF, Category.assoc]))
  · obtain ⟨e, u₁, u₂⟩ := hE E
    obtain ⟨d₁, v₁, w₁⟩ := exists_end g₁.1 k₁.1.w (e₁ E) e u₁
    obtain ⟨d₂, v₂, w₂⟩ := exists_end g₂.1 k₂.1.w (e₂ E) e u₂
    have : d₁ ≫ F = F ≫ d₂ := ExtUnique.over_hom_ext_of_isPullback k₁.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, w₁, Category.assoc, ← eF, ← Category.assoc, ← eF, w₂])
    refine ⟨d₁, v₁, ?_⟩
    rw [← Category.assoc, ← Over.comp_left, this, Over.comp_left, Category.assoc, v₂, Category.assoc]
  · obtain ⟨w, u₁, u₂⟩ := hx x
    obtain ⟨d₁, v₁, z₁, w₁⟩ := exists_sec g₁.1 k₁.1.w (t₁ x).left (Over.w (t₁ x)) w u₁
    obtain ⟨d₂, v₂, z₂, w₂⟩ := exists_sec g₂.1 k₂.1.w (t₂ x).left (Over.w (t₂ x)) w u₂
    have : Surjective (w ≫ P.A.hom) :=
      ⟨fun y => ⟨y, Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
    have : d₁ ≫ F.left = d₂ := ext_of_isDominant_of_isSeparated Q₂.A.hom
      (by rw [Category.assoc, Over.w, z₁, z₂]) ((w ≫ P.A.hom) ≫ spMap (algebraMap O Ω))
      (by rw [← Category.assoc, w₁, w₂, eF, Category.assoc])
    exact ⟨d₁, v₁, by rw [← Category.assoc, this, v₂]⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonBaseChangePolarizedAbelianSchemeOfGeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameAt_of_sameAt_comp_algebraMap : ∀ (O Ω R₁ R₂ M Γ : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R₁] [CommRing R₂] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* O) (f₂ : R₂ →+* O) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), SameAt P₁ P₂ ((algebraMap O Ω).comp f₁) ((algebraMap O Ω).comp f₂) e₁ e₂ t₁ t₂ → SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ := by
  first | exact @GlobalTheory.Poinc.sameAt_of_generic | exact GlobalTheory.Poinc.sameAt_of_generic | (intros; apply GlobalTheory.Poinc.sameAt_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointsLiftMulInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointsLiftMulInv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem grpPullback_points_lift_mul_inv : ∀ (T S : Scheme.{0}) (f : S ⟶ T) (G : Over T) [GrpObj G] (G' : Over S) [GrpObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G f β → ∀ (Z' : Over S) (Z : Over T) (ζ : Z'.left ⟶ Z.left), ζ ≫ Z.hom = Z'.hom ≫ f → (∀ u : Z ⟶ G, ∃ u' : Z' ⟶ G', u'.left ≫ β = ζ ≫ u.left) ∧ ∀ (u v : Z ⟶ G) (u' v' : Z' ⟶ G'), u'.left ≫ β = ζ ≫ u.left → v'.left ≫ β = ζ ≫ v.left → (u' * v').left ≫ β = ζ ≫ (u * v).left ∧ (u'⁻¹).left ≫ β = ζ ≫ (u⁻¹).left := by
  intro T S f G _ G' _ β hpb Z' Z ζ hζ
  have hw : ∀ u : Z ⟶ G, (ζ ≫ u.left) ≫ G.hom = Z'.hom ≫ f := fun u => by
    rw [Category.assoc, Over.w u, hζ]
  refine ⟨fun u => ⟨Over.homMk (hpb.1.lift (ζ ≫ u.left) Z'.hom (hw u)) (hpb.1.lift_snd _ _ _),
    hpb.1.lift_fst _ _ _⟩, ?_⟩
  intro u v u' v' hu hv
  let ζ' : Over.mk (Z'.hom ≫ f) ⟶ Z := Over.homMk ζ hζ
  let φ : (Z' ⟶ G') → (Over.mk (Z'.hom ≫ f) ⟶ G) := fun w =>
    Over.homMk (w.left ≫ β) (by
      change (w.left ≫ β) ≫ G.hom = Z'.hom ≫ f
      rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w w])
  have hφ : ∀ a b, φ (a * b) = φ a * φ b := fun a b =>
    Over.OverMorphism.ext (hpb.2 Z' a b (φ a) (φ b) rfl rfl).symm
  let ψ := MonoidHom.mk' φ hφ
  have hu' : ψ u' = ζ' ≫ u := Over.OverMorphism.ext hu
  have hv' : ψ v' = ζ' ≫ v := Over.OverMorphism.ext hv
  constructor
  · have h : ψ (u' * v') = ζ' ≫ (u * v) := by rw [map_mul, hu', hv', MonObj.comp_mul]
    exact congrArg CommaMorphism.left h
  · have h : ψ (u'⁻¹) = ζ' ≫ (u⁻¹) := by rw [map_inv, hu', GrpObj.comp_inv]
    exact congrArg CommaMorphism.left h

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointsLiftMulInvStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv : ∀ (T S : Scheme.{0}) (f : S ⟶ T) (G : Over T) [GrpObj G] (G' : Over S) [GrpObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G f β → ∀ (Z' : Over S) (Z : Over T) (ζ : Z'.left ⟶ Z.left), ζ ≫ Z.hom = Z'.hom ≫ f → (∀ u : Z ⟶ G, ∃ u' : Z' ⟶ G', u'.left ≫ β = ζ ≫ u.left) ∧ ∀ (u v : Z ⟶ G) (u' v' : Z' ⟶ G'), u'.left ≫ β = ζ ≫ u.left → v'.left ≫ β = ζ ≫ v.left → (u' * v').left ≫ β = ζ ≫ (u * v).left ∧ (u'⁻¹).left ≫ β = ζ ≫ (u⁻¹).left := by
  first | exact @GlobalTheory.Mum.grpPullback_points_lift_mul_inv | exact GlobalTheory.Mum.grpPullback_points_lift_mul_inv | (intros; apply GlobalTheory.Mum.grpPullback_points_lift_mul_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfCobEqZeroOfPow
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

open GlobalTheory.PDiv

theorem eq_zero_of_cob_eq_zero_of_pow (p : ℕ) (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (G : PDivGroup p R) (B : G.funs) (hB : G.cob B = 0) : B = 0 := by
  have key : ∀ k : ℕ, (∀ n, GlobalTheory.PDiv.mulBy R (G.A n) (p ^ k) (B.1 n) = 0) → ∀ n, B.1 n = 0 := by
    intro k
    induction k with
    | zero =>
      intro h n
      have h1 := (mulBy_of_cobOne_eq_zero (congrArg (fun x : G.cocycles => x.1 n) hB) (p ^ 0)).1
      rw [h n, pow_zero, one_smul] at h1
      exact h1.symm
    | succ k ih =>
      intro h
      refine ih fun n => Test.mulP_injective G n ?_
      rw [map_zero, map_mulBy, ← B.2 n, mulP_res, mulBy_mulBy, ← pow_succ, h]
  refine Subtype.ext (funext (key N fun n => ?_))
  rw [(mulBy_of_cobOne_eq_zero (congrArg (fun x : G.cocycles => x.1 n) hB) (p ^ N)).1,
    ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow, hN, zero_smul]

end GlobalTheory.PDivGroup
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

theorem rigOfOmega_injective_of_pow (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (G : PDivGroup p R) : Function.Injective G.rigOfOmega := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hw
  rw [G.eq_zero_of_cob_eq_zero_of_pow p R N hN b (congrArg Prod.fst hb), map_zero] at hb
  exact (congrArg Prod.snd hb).symm

end GlobalTheory.PDivGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalReal
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM
open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RiemInt

open GlobalTheory.AppellHumbertTrivial

theorem im_hermForm_int {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : IsFactorAH u Hm χ) (l m : u.Λ) :
    ∃ n : ℤ, (hermForm Hm l m).im = n := by
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hil : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have him : ⊤ ≤ (u.ex (0 + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have hlm : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h.2.2 l i 0 hi
  have h2 := h.2.2 m i _ hil
  have h3 := h.2.2 m i 0 hi
  have h4 := h.2.2 l i _ him
  have hne := u.fr_ne i _ hlm
  have hs : hermForm Hm m l = star (hermForm Hm l m) := by
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.1.eq, Matrix.dotProduct_mulVec]
  have hχl : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  have hχm : χ m ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  rw [h2] at h1
  rw [h4, h1] at h3
  simp only [zero_add, zero_dotProduct, mul_zero] at h3 hne
  rw [add_comm (m : Fin g → ℂ) l] at h3
  unfold hermForm at hs ⊢
  rw [hs] at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h3
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h3 ⊢
  simp only [Complex.exp_add] at h3
  have he : Complex.exp (Real.pi * c) = Complex.exp (Real.pi * star c) := by
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hχl hχm)
      (Complex.exp_ne_zero (Real.pi / 2 * a))) (Complex.exp_ne_zero (Real.pi / 2 * b))) hne) ?_
    linear_combination h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  have hp := Real.pi_pos
  refine mul_left_cancel₀ (a := 2 * Real.pi) (by positivity) ?_
  linear_combination this

variable {g : ℕ}

end GlobalTheory.RiemInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveOfTrivAxes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeAxes

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem lift_mul_lift {Y : Over S} (a a' b b' : Y ⟶ G) : lift a b * lift a' b' = lift (a * a') (b * b') := by
  ext <;> simp [MonObj.mul_comp]

theorem cube_cls (hG : IsAbelianScheme G) {P : LB (G ⊗ G).left} (hP : P.IsLB) {Y : Over S} (a b c : Y ⟶ G ⊗ G) :
    CechPic.pull (a * b * c).left (cls P hP) - CechPic.pull (a * b).left (cls P hP) - CechPic.pull (a * c).left (cls P hP)
      - CechPic.pull (b * c).left (cls P hP) + CechPic.pull a.left (cls P hP) + CechPic.pull b.left (cls P hP)
      + CechPic.pull c.left (cls P hP) - CechPic.pull (1 : Y ⟶ G ⊗ G).left (cls P hP) = 0 := by
  have hGG := AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  have T := GlobalTheory.CubeTop.cubeTheorem S (G ⊗ G) hGG P hP Y a b c
  have z := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 T
  rw [cls_linComb hP] at z
  simp only [Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
  rw [← z]
  abel

theorem additive_of_triv_axes : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G], IsAbelianScheme G →
    ∀ {P : LB (G ⊗ G).left} (hP : P.IsLB), (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → IsAdditive P ∧ IsAdditive (swap P) := by
  intro S G _ hG P hP h₁ h₂
  have l : ∀ {Y : Over S} (a : Y ⟶ G), evc hP 1 a = 0 := fun a ↦ evc_one_left hP h₁ a
  have r : ∀ {Y : Over S} (a : Y ⟶ G), evc hP a 1 = 0 := fun a ↦ evc_one_right hP h₂ a
  have o : ∀ {Y : Over S}, (1 : Y ⟶ G ⊗ G) = lift 1 1 := by
    intro Y
    ext <;> simp
  refine ⟨(isAdditive_iff hP).2 fun Y x x' y ↦ ?_, (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).2 fun Y x y y' ↦ ?_⟩
  · have e := cube_cls hG hP (lift x 1) (lift x' 1) (lift 1 y)
    simp only [lift_mul_lift, _root_.mul_one, _root_.one_mul, o] at e
    change evc hP (x * x') y - evc hP (x * x') 1 - evc hP x y - evc hP x' y + evc hP x 1 + evc hP x' 1
      + evc hP 1 y - evc hP 1 1 = 0 at e
    rw [r, r, r, r, l] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := cube_cls hG hP (lift 1 y) (lift 1 y') (lift x 1)
    simp only [lift_mul_lift, _root_.mul_one, _root_.one_mul, o] at e
    change evc hP x (y * y') - evc hP 1 (y * y') - evc hP x y - evc hP x y' + evc hP 1 y + evc hP 1 y'
      + evc hP x 1 - evc hP 1 1 = 0 at e
    rw [l, l, l, l, r] at e
    rw [← sub_eq_zero, ← e]
    abel

end GlobalTheory.CubeAxes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem PullB.vanMod {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)}
    {b' : D'.SecB k x} (H : PullB hD x b b') {I : Ideal R} {I' : Ideal R'} (hI : I ≤ I'.comap φ) {e : ℕ}
    (hb : VanMod I b e) : VanMod I' b' e := by
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ :=
    (Ideal.pow_right_mono hI _).trans (Ideal.le_comap_pow φ _)
  have hw : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.P.A.hom = D'.P.A.hom ≫ specOf φ :=
    (pull_grp hD).1.w
  have hc := ExpGTrans.famφB_pull hD x
  unfold PullB at H
  have ht : thick R' I' e ≫ specOf φ =
      spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle) ≫ thick R I e := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  obtain ⟨h, hh⟩ : ∃ h : pullback D'.P.A.hom (thick R' I' e) ⟶ pullback D.P.A.hom (thick R I e),
      h ≫ pullback.fst D.P.A.hom (thick R I e) = pullback.fst D'.P.A.hom (thick R' I' e) ≫
        hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) :=
    ⟨pullback.lift _ (pullback.snd D'.P.A.hom (thick R' I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) (by
      rw [Category.assoc, hw, ← Category.assoc, pullback.condition, Category.assoc, ht, Category.assoc]),
      pullback.lift_fst _ _ _⟩
  intro q
  refine fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
    (D'.famφB x κ (pullback.fst D'.P.A.hom (thick R' I' e) y)))
  have e₁ := H _ (pullback.fst D'.P.A.hom (thick R' I' e)) y p q hp (Set.mem_iInter.1 hy)
  have hm : pullback.fst D.P.A.hom (thick R I e) (h y) ∈ LB.wchart D.P.L (D.famφB (hD.xe x)) p :=
    Set.mem_iInter.2 fun κ => by
      have a : h ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.famφB (hD.xe x) κ =
          pullback.fst D'.P.A.hom (thick R' I' e) ≫ D'.famφB x κ ≫
            hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := by
        rw [← Category.assoc, hh, Category.assoc, ← hc κ]
      exact (congrArg (fun m => m y ∈ D.P.L.U (p κ)) a).mpr (hp κ)
  have z₀ : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens), f y ∈ U → gs f y U 0 = 0 := fun f y U h => by
    rw [gs_eq f y U h, map_zero, map_zero]
  rw [← hh] at e₁
  have e₂ := (Units.mul_right_eq_zero _).1 (e₁.symm.trans ((gs_pull h _ y _ hm _).symm.trans
    ((congrArg (gs h y _) (hb p)).trans (z₀ h y _ hm))))
  exact ((gs_pull (𝟙 _) _ y _ hy _).trans ((congrArg (fun m => gs m y _ _) (Category.id_comp _)).trans e₂)).trans
    (z₀ _ y _ hy).symm

theorem exists_intFam_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (D' : DegData W (maximalIdeal W)) (hD : IsPullDeg φ D.toPre D'.toPre), Function.Injective φ → IsLocalHom φ → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k), ∃ F' : IntFam (maximalIdeal W) D'.toPre k, ∀ x, PullB hD x (F.f (hD.xe x)) (F'.f x) := by
  intro R _ _ _ _ D W _ _ _ φ D' hD _ hl k F
  choose f' hf' using fun x => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB D'.toPre.P.isLB hD.w
    hD.w_gen (Fin 4) (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull hD x)
    (F.f (hD.xe x))).exists
  have s₁ : scal (DegPre.BF D.toPre (FractionRing R)).hom 1 = 1 := by rw [scal, map_one, map_one]
  have s₂ : scal (DegPre.BF D'.toPre (FractionRing W)).hom 1 = 1 := by rw [scal, map_one, map_one]
  obtain ⟨E, hE⟩ := exists_fam_of_isPullDeg GlobalTheory.allSixLaws.1.globalFns R W φ D.toPre D'.toPre hD k F.F F.f f'
    (fun α => s₁ ▸ F.ext α) hf'
  have hI : maximalIdeal R ≤ (maximalIdeal W).comap φ := fun a ha => map_nonunit φ a ha
  refine ⟨{ F := E, f := f', ext := fun α => s₂.symm ▸ hE α, small := fun e => ?_ }, hf'⟩
  exact ((F.small e).preimage hD.xe.injective.injOn).subset fun x hx hv => hx (PullB.vanMod (hf' x) hI hv)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

abbrev Vec (r : ℕ) := Fin r ⊕ Fin r → ℤ

section Formal

variable {r : ℕ}

def lam (u v : Vec r) : Vec r →₀ ℤ :=
  Finsupp.single (u + v) 1 - Finsupp.single u 1 - Finsupp.single v 1 + Finsupp.single 0 1

def theta (a b c : Vec r) : Vec r →₀ ℤ :=
  Finsupp.single (a + b + c) 1 - Finsupp.single (a + b) 1 - Finsupp.single (a + c) 1 - Finsupp.single (b + c) 1 +
    Finsupp.single a 1 + Finsupp.single b 1 + Finsupp.single c 1 - Finsupp.single 0 1

def xv (i : Fin r) : Vec r := Sum.elim (Pi.single i 1) 0

def zv (i : Fin r) : Vec r := Sum.elim 0 (Pi.single i 1)

def axv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : Vec r := Sum.elim (fun l => A i l) 0

def azv (A' : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : Vec r := Sum.elim 0 (fun l => A' i l)

def rosVec (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) (i : Fin r) : Vec r :=
  ![axv A i + zv i, axv A i, zv i, xv i + azv A' i, xv i, azv A' i] a

def sig (W A A' : Matrix (Fin r) (Fin r) ℤ) : Vec r →₀ ℤ :=
  ∑ a : Fin 6, ∑ i, ∑ j, (rosatiε a * W i j) • lam (rosVec A A' a i) (rosVec A A' a j)

end Formal

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def vecHom (T : Tens D D' W) (v : Vec r) : D'.P.A ⊗ D'.P.A ⟶ D.P.A :=
  (∏ k, (fst D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inl k)) * ∏ k, (snd D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inr k)

def vecLat (T : Tens D D' W) (v : Vec r) (y y' : D'.X) : D.X :=
  ∑ k, v (Sum.inl k) • T.xe y k + ∑ k, v (Sum.inr k) • T.xe y' k

def isoV {X X' Z : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ}
    (w : LB.Iso M' (LB.LinComb M ψ δ)) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι) (χ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ :=
  gm χ z _ (w.s (fun k => J (χ ≫ ψ k), J' χ))

def qv (T : Tens D D' W) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (χ : D'.X) :
    ((TK R).left.presheaf.stalk z)ˣ :=
  ∏ i, ∏ j, val (D.tau (T.xe χ i) (T.xe χ j)) (𝟙 _) z J ^ W i j

def rosLat (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (y y' : D'.X) : Fin 6 → D'.X :=
  ![GlobalTheory.TensAct.latAct T A y + y', GlobalTheory.TensAct.latAct T A y, y', y + GlobalTheory.TensAct.latAct T A' y', y,
    GlobalTheory.TensAct.latAct T A' y']

def Triv (T : Tens D D' W) (c : Vec r →₀ ℤ) : Prop :=
  ∃ Ξ : LB.Gen (LB.LinComb D.P.L (fun v : c.support => (vecHom T v.1).left) (fun v => c v.1)), Ξ.IsGen ∧
    (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J, Good D.P.L z J → val Ξ (zero2 D'.P.A) z J = 1) ∧
    ∀ (z : (TK R).left) J, Good D.P.L z J → ∀ y y' : D'.X,
      val Ξ (D'.pt2 y y') z J = ∏ v ∈ c.support, val (D.psi (vecLat T v y y')) (𝟙 _) z J ^ (-(c v))

end GlobalTheory.TensBal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DegPullId

theorem exists_isPullDeg_id_self : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I),
    ∃ h : IsPullDeg (RingHom.id R) D.toPre D.toPre, (∀ x, h.xe x = x) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := by
  intro R _ _ I hR D
  have hgen {F : D.toPre.P.A.left ⟶ D.toPre.P.A.left} (hF : F = 𝟙 _) : PGen (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF) := by
    subst F
    intro Y f y j j' k k' hj hj' hk hk'
    have hgw : ∀ a b, f y ∈ D.toPre.P.L.U a → f y ∈ D.toPre.P.L.U b →
        gw (isoPullId (Geo.Tor.idIso D.toPre.P.L) rfl) f y a b =
          gm f y _ (D.toPre.P.L.g a b) := by
      intro a b ha hb
      have hm : f y ∈ (D.toPre.P.L.pull (𝟙 _)).U (fun _ => a) ⊓ D.toPre.P.L.U b := ⟨mem_pull.2 ha, hb⟩
      exact gm_res f y _ hm _
    rw [hgw j k hj hk, hgw j' k' hj' hk', Category.comp_id]
    have hV : f y ∈ (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have hw' : res (inf_le_left : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) (D.toPre.P.L.g j k) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U j') (D.toPre.P.L.g j j') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U k ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g k k'))⁻¹ *
      res (inf_le_right : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g j' k') :=
      (idIso_isGen D.toPre.P.isLB) (j, k) (j', k')
    have key := congrArg (gm f y ((D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k'))) hw'
    simp only [map_mul, map_inv, gm_res f y _ hV] at key
    exact key
  have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
  have gp : IsGrpPullback D.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) (Iso.refl D.toPre.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R I hR D
  obtain ⟨hD, h₁, -, h₃⟩ := UnifUniq.exists_isPullDeg_id D.toPre D.toPre W hW ψW e me
    (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF') ((isGen_iff _).2 (hgen hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (NoTorus.pmaps_id hF' (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => NoTorus.pmaps_id hF' (K := PUnit) (fun _ => D.toPre.xK x) (fun _ => -1) (D.toPre.psi_gen x))
  refine ⟨hD, fun x => ?_, ?_⟩
  · rw [h₃]; rfl
  · rw [h₁]; exact hF'

end GlobalTheory.DegPullId
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissibleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullDeg_identity_self_admissible : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I),
    ∃ h : IsPullDeg (RingHom.id R) D.toPre D.toPre, (∀ x, h.xe x = x) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := by
  first | exact @GlobalTheory.DegPullId.exists_isPullDeg_id_self | exact GlobalTheory.DegPullId.exists_isPullDeg_id_self | (intros; apply GlobalTheory.DegPullId.exists_isPullDeg_id_self <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToP
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke


open GlobalTheory.AbDual GlobalTheory.CechPic in
theorem evc_pow_left {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left}
    (hP : P.IsLB) (h₁ : GlobalTheory.AbLaw.Triv (ev P (1 : A ⟶ A) (𝟙 A))) (h₂ : GlobalTheory.AbLaw.Triv (ev P (𝟙 A) (1 : A ⟶ A)))
    {Y : Over S} (a t : Y ⟶ A) (n : ℕ) : evc hP (a ^ n) t = n • evc hP a t := by
  have hadd := (isAdditive_iff hP).1 (additive_of_cube GlobalTheory.CubeTop.cubeTheorem hA hA hP h₁ h₂).1
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact (additive_of_cube GlobalTheory.CubeTop.cubeTheorem hA hA hP h₁ h₂).1.evc_one hP t
  | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]

theorem kernel_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ), m.Coprime p → ∀ (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro p _ D R _ b M S s o A' _ _ ψ G _ hψ hG m hm P' hP' hiso
  obtain ⟨e₀, he₀, hker⟩ := o.kerP
  refine ⟨m * e₀, Nat.Coprime.mul_left hm he₀, ?_⟩
  intro T x hx
  have := hG.etale
  have := hG.fin
  have := hG.onto

  let T' : Over S := Over.mk (pullback.fst x.left ψ.left ≫ T.hom)
  let π' : T' ⟶ T := Over.homMk (pullback.fst x.left ψ.left) rfl
  let y : T' ⟶ o.A := Over.homMk (pullback.snd x.left ψ.left) (by
    show pullback.snd x.left ψ.left ≫ o.A.hom = pullback.fst x.left ψ.left ≫ T.hom
    rw [← Over.w ψ, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w x])
  have hy : y ≫ ψ = π' ≫ x := Over.OverMorphism.ext (by
    show pullback.snd x.left ψ.left ≫ ψ.left = pullback.fst x.left ψ.left ≫ x.left
    exact pullback.condition.symm)

  have hP := o.isLB
  have hPm : (lbPow o.P m).IsLB := LB.isLB_linComb hP _ _
  have hc : GlobalTheory.CechPic.cls _ hPm = m • GlobalTheory.CechPic.cls o.P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1) hPm).trans ?_
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hc' : GlobalTheory.CechPic.cls _ hPm = GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP') :=
    (GlobalTheory.CechPic.cls_eq_iff hPm (pull_isLB hP' _)).2 hiso
  have h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0 := (GlobalTheory.AbDual.triv_ev_iff hP' _ _).1 hx
  have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst o.A T' ≫ ψ) (snd o.A T' ≫ π')).left) h0
  rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst, Category.assoc, ← hy] at h1
  have e2 : GlobalTheory.AbDual.evc hP' (snd o.A T' ≫ y ≫ ψ) (fst o.A T' ≫ ψ) =
      GlobalTheory.CechPic.pull (lift (snd o.A T' ≫ y) (fst o.A T')).left (GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP')) := by
    rw [← GlobalTheory.CechPic.pull_comp, GlobalTheory.AbDual.evc, sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc,
      Category.assoc]
  rw [e2, ← hc', hc, map_nsmul] at h1
  have h3 : GlobalTheory.AbDual.evc hP (snd o.A T' ≫ y ^ m) (fst o.A T') = 0 := by
    rw [comp_pow, evc_pow_left o.ab hP o.rig₁ o.rig₂]
    exact h1
  have h4 := hker T' (y ^ m) ((GlobalTheory.AbDual.triv_ev_iff hP _ _).2 h3)
  rw [← pow_mul] at h4
  have h5 : π' ≫ x ^ (m * e₀) = π' ≫ 1 := by
    rw [comp_pow, ← hy, ← GlobalTheory.SS.FrobTorsion.pow_comp' ψ y, h4, MonObj.one_comp, MonObj.comp_one]
  apply Over.OverMorphism.ext
  have h6 := congrArg (fun f => f.left) h5
  simp only [Over.comp_left] at h6
  exact (cancel_epi (pullback.fst x.left ψ.left)).1 h6

end GlobalTheory.UPel.HT.Hecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToPStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descendedBundle_kernel_killed_by_integer_prime_to_p : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ), m.Coprime p → ∀ (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | exact @GlobalTheory.UPel.HT.Hecke.kernel_descent | exact GlobalTheory.UPel.HT.Hecke.kernel_descent | (intros; apply GlobalTheory.UPel.HT.Hecke.kernel_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def GtPtAct {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O) (g g' : GtPtF D F) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
          (LB.pullGen D.P.L _ _ u (lift (DegPre.cF D F χ) g.b).left)) (g'.s χ)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelBijectiveOfPowEqZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup

theorem omegaLevel_bijective_of_pow_eq_zero : ∀ (p : ℕ)  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (G : PDivGroup p R) (n : ℕ), N ≤ n → Function.Bijective (G.omegaLevel n) := by
  intro p R _ N hN G n hn
  refine ⟨fun w w' h => ?_, G.omegaLevel_surjective n⟩
  rw [← sub_eq_zero]
  have h0 : (w - w').1 n = 0 := by
    simp only [omegaLevel_apply] at h
    change w.1 n - w'.1 n = 0
    rw [h, sub_self]
  obtain ⟨v, hv⟩ := (G.omega_val_eq_zero_iff n (w - w')).1 h0
  rw [hv, ← Nat.add_sub_cancel' hn, pow_add, hN, zero_mul, zero_smul]

end GlobalTheory.PDivGroup
end
