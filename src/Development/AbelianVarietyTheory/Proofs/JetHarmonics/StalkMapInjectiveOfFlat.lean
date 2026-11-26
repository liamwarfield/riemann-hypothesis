module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEInst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullLin

theorem stalkMap_injective_of_flat {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have h := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem sec_eq_zero_of_flat {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (f : Y' ⟶ Y) [Flat f] [Surjective f]
    (h : ∀ x J, Good L x J → sval s f x J = 0) (j : K → L.ι) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  apply stalkMap_injective_of_flat f x
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ x)
  refine (gs_stalkMap f x _ hy _).symm.trans (Eq.trans ?_ (gs_stalkMap f x _ hy _))
  refine (sec_trans s f x hy (Good.mem hJ φ f)).trans ?_
  refine (congrArg _ (h x J hJ)).trans ((mul_zero _).trans ?_)
  rw [gs_eq f x _ hy, map_zero, map_zero]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem aF_fst (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left :=
  congrArg (fun q => q.left) (lift_fst (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))

theorem aF_snd (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
  congrArg (fun q => q.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))

theorem isPullback_aF (oa : D.toPre.OAct O) (a : O) :
    IsPullback (aF D F oa a).left (DegPre.prB D.toPre F).left (DegPre.prB D.toPre F).left (oa.onB.act a).left := by
  have h₀ : IsPullback (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.prB D.toPre F).left
      (TF (R := V) F).hom D.toPre.P.A.hom := IsPullback.of_hasPullback _ _
  refine IsPullback.of_right ?_ (aF_snd oa a) h₀
  rw [aF_fst, Over.w]
  exact h₀

theorem aF_mul (oa : D.toPre.OAct O) (a b : O) : aF D F oa (a * b) = aF D F oa b ≫ aF D F oa a := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [aF]
  · simp [aF, DegPre.prB, oa.onB.map_mul]

theorem pullAl_val (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X)
    {u u' : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))} (hu : u.IsGen) (hu' : u'.IsGen)
    {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)}
    (c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left) t)
    (c' : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u' (DegPre.zF D.toPre F).left) t)
    (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) (hJ : Good D.toPre.P.L z J) :
    val u r z J = val u' r z J := by
  have z₁ : DegPre.zF D.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  refine gen_unique' D.toPre.P.isLB (fun _ _ _ => rfl) (fst (TF (R := V) F) D.toPre.P.A).left
    (DegPre.zF D.toPre F).left (congrArg (fun q => q.left) z₁) (surj_appTop D.toPre F hG) hu hu'
    (fun y I hI => ?_) Z r z J hJ
  have a₁ := val_corr hI c (𝟙 _)
  have a₂ := val_corr hI c' (𝟙 _)
  rw [val_pull hI, Category.id_comp] at a₁ a₂
  exact a₁.trans a₂.symm

theorem pullAl_unique (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s t') : t = t' := by
  refine fam_ext fun β j => ?_
  by_cases hβ : ∃ χ, β = star a • χ
  · obtain ⟨χ, rfl⟩ := hβ
    obtain ⟨u, hu, c, e⟩ := h.1 χ
    obtain ⟨u', hu', c', e'⟩ := h'.1 χ
    refine sec_ext_val D.toPre.P.isLB (fun y J hJ => ?_) j
    rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 e' _ _ y J hJ,
      pullAl_val hG oa a k N χ hu hu' c c' _ _ y J hJ]
  · exact (h.2 β (fun χ e => hβ ⟨χ, e⟩) j).trans (h'.2 β (fun χ e => hβ ⟨χ, e⟩) j).symm

theorem pullAl_add (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s s' : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s' t') :
    PullAl D F oa a k N (s + s') (t + t') := by
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, c, e⟩ := h.1 χ
    obtain ⟨u', hu', c', e'⟩ := h'.1 χ
    refine ⟨u, hu, c, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩
    rw [sval_add _ _ _ _ y hJ, sval_add _ _ _ _ y hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 e' _ _ y J hJ,
      pullAl_val hG oa a k N χ hu' hu c' c _ _ y J hJ, add_mul]
  · rw [add_f, h.2 β hβ j, h'.2 β hβ j, add_zero]

theorem pullAl_smul (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (ζ : F) {s : Fam D.toPre F k}
    {t : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) : PullAl D F oa a k N (ζ • s) (ζ • t) := by
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, c, e⟩ := h.1 χ
    refine ⟨u, hu, c, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩
    rw [sval_smul _ _ _ _ y hJ, sval_smul _ _ _ _ y hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ, Category.assoc, aF_fst, _root_.mul_assoc]
  · rw [smul_f, h.2 β hβ j, mul_zero]

theorem eq_zero_of_pullAl_zero (hM : MulNSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (hN : 1 ≤ N)
    (haa : a * star a = (N : O)) {s : Fam D.toPre F k} (h : PullAl D F oa a k N s 0) : s = 0 := by
  obtain ⟨-, hflat, hsurj, -⟩ := hM _ D.toPre.P N hN
  have hm : oa.onB.act (a * star a) = mulA D.toPre.P.A N := by
    rw [haa, ← _root_.mul_one (N : O), act_nsmul, oa.onB.map_one]
  rw [← hm] at hflat hsurj
  have hp := isPullback_aF (F := F) oa (a * star a)
  have : Flat (aF D F oa (a * star a)).left := MorphismProperty.of_isPullback hp.flip hflat
  have : Surjective (aF D F oa (a * star a)).left := MorphismProperty.of_isPullback hp.flip hsurj
  refine fam_ext fun χ j => sec_eq_zero_of_flat D.toPre.P.isLB (s.s χ) (aF D F oa (a * star a)).left
    (fun x J hJ => ?_) j
  obtain ⟨u, -, -, e⟩ := h.1 χ
  have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ (aF D F oa (star a)).left x J hJ
  have e₀ : sval ((0 : Fam D.toPre F (k * N)).s (star a • χ)) (aF D F oa (star a)).left x J = 0 :=
    gs_zero _ x _ (hJ.mem _ _)
  rw [e₀, ← Over.comp_left, ← aF_mul] at e₁
  exact (Units.mul_left_eq_zero _).1 e₁.symm

theorem exists_pull_linearMap : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O]
    [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 →
    ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) →
    ∃ π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N), Function.Injective π ∧
      ∀ s s', PullAl D F oa a k N s s' ↔ s' = π s := by
  intro hL V _ _ _ D F _ _ O _ _ _ oa w0 hw a N k hN _ haa
  have hG := hL.globalFns
  obtain ⟨uΨ, huΨ, -⟩ := id hw
  choose P hP using fun s : Fam D.toPre F k => exists_pullAl D F D.toPre.P.isLB oa w0 uΨ huΨ a N haa hN k s
    (pullSecs_fe' D F hG D.toPre.P.isLB oa w0 hw uΨ huΨ a N haa hN k s)
  let π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N) :=
    { toFun := P
      map_add' := fun s s' => pullAl_unique hG oa a k N (hP _) (pullAl_add hG oa a k N (hP s) (hP s'))
      map_smul' := fun ζ s => pullAl_unique hG oa a k N (hP _) (pullAl_smul oa a k N ζ (hP s)) }
  refine ⟨π, (injective_iff_map_eq_zero π).2 fun s hs => ?_, fun s s' =>
    ⟨fun h => pullAl_unique hG oa a k N h (hP s), fun h => h ▸ hP s⟩⟩
  exact eq_zero_of_pullAl_zero hL.mulN oa a k N hN haa (hs ▸ hP s)

end GlobalTheory.PullLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFamilyOfStrictMin
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FamInt

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}


open Classical in
def ordFn (hϖ : Irreducible ϖ) (c : FractionRing V) : WithTop ℚ :=
  if h : c = 0 then ⊤ else (((hasVal_of_ne_zero hϖ h).choose : ℚ) : WithTop ℚ)

theorem ordFn_of_hasVal (hϖ : Irreducible ϖ) {c : FractionRing V} {n : ℤ} (h : HasVal ϖ c n) :
    ordFn hϖ c = ((n : ℚ) : WithTop ℚ) := by
  have h0 := ne_zero_of_hasVal hϖ h
  rw [ordFn, dite_eq_right h0, hasVal_unique hϖ (hasVal_of_ne_zero hϖ h0).choose_spec h]

theorem ordFn_zero (hϖ : Irreducible ϖ) : ordFn hϖ 0 = ⊤ := by rw [ordFn, dite_eq_left rfl]

theorem le_ordFn_iff (hϖ : Irreducible ϖ) (c : FractionRing V) (n : ℤ) :
    ((n : ℚ) : WithTop ℚ) ≤ ordFn hϖ c ↔
      ∃ b : V, c = algebraMap V (FractionRing V) ϖ ^ n * algebraMap V (FractionRing V) b := by
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  constructor
  · intro h
    by_cases hc : c = 0
    · exact ⟨0, by simp [hc]⟩
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    rw [ordFn_of_hasVal hϖ hm] at h
    have hnm : n ≤ m := by exact_mod_cast h
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, m = n + d := ⟨(m - n).toNat, by omega⟩
    obtain ⟨u, hu⟩ := hm
    exact ⟨ϖ ^ d * u, by rw [hu, zpow_add₀ hπ, zpow_natCast, map_mul, map_pow, _root_.mul_assoc]⟩
  · rintro ⟨b, rfl⟩
    by_cases hb : b = 0
    · rw [hb, map_zero, mul_zero, ordFn_zero]; exact le_top
    obtain ⟨d, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    rw [ordFn_of_hasVal hϖ (n := n + d) ⟨u, by rw [zpow_add₀ hπ, zpow_natCast, map_mul, map_pow]; ring⟩]
    exact_mod_cast (by omega : n ≤ n + d)

def ordVal (hϖ : Irreducible ϖ) : AddValuation (FractionRing V) (WithTop ℚ) :=
  AddValuation.of (ordFn hϖ) (ordFn_zero hϖ)
    (by rw [ordFn_of_hasVal hϖ (n := 0) ⟨1, by simp⟩]; simp)
    (fun x y => by
      by_cases hx : x = 0
      · rw [hx, zero_add]; exact min_le_right _ _
      by_cases hy : y = 0
      · rw [hy, add_zero]; exact min_le_left _ _
      obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hx
      obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hy
      obtain ⟨a, ha⟩ := (le_ordFn_iff hϖ x (min n m)).1
        (by rw [ordFn_of_hasVal hϖ hn]; exact_mod_cast min_le_left n m)
      obtain ⟨b, hb⟩ := (le_ordFn_iff hϖ y (min n m)).1
        (by rw [ordFn_of_hasVal hϖ hm]; exact_mod_cast min_le_right n m)
      refine le_trans ?_ ((le_ordFn_iff hϖ (x + y) (min n m)).2 ⟨a + b, by rw [map_add (f := _), mul_add, ← ha, ← hb]⟩)
      rw [ordFn_of_hasVal hϖ hn, ordFn_of_hasVal hϖ hm]
      exact_mod_cast le_rfl)
    (fun x y => by
      have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
      by_cases hx : x = 0
      · rw [hx, MulZeroClass.zero_mul, ordFn_zero, top_add]
      by_cases hy : y = 0
      · rw [hy, mul_zero, ordFn_zero, add_top]
      obtain ⟨n, u, hn⟩ := hasVal_of_ne_zero hϖ hx
      obtain ⟨m, w, hm⟩ := hasVal_of_ne_zero hϖ hy
      rw [ordFn_of_hasVal hϖ ⟨u, hn⟩, ordFn_of_hasVal hϖ ⟨w, hm⟩, ordFn_of_hasVal hϖ (n := n + m)
        ⟨u * w, by rw [hn, hm, zpow_add₀ hπ, Units.val_mul, map_mul]; ring⟩]
      push_cast; rfl)

theorem valOver_ordVal (hϖ : Irreducible ϖ) : ValOver ϖ (FractionRing V) (ordVal hϖ) :=
  fun _ _ h => ordFn_of_hasVal hϖ h

theorem exists_eq_of_pos (hϖ : Irreducible ϖ) {c : FractionRing V} (h : 0 < ordVal hϖ c) :
    ∃ b : V, c = algebraMap V (FractionRing V) (ϖ * b) := by
  have h1 : (((1 : ℤ) : ℚ) : WithTop ℚ) ≤ ordFn hϖ c := by
    by_cases hc : c = 0
    · rw [hc, ordFn_zero]; exact le_top
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    change 0 < ordFn hϖ c at h
    rw [ordFn_of_hasVal hϖ hm] at h ⊢
    have : (0 : ℤ) < m := by exact_mod_cast h
    exact_mod_cast (by omega : (1 : ℤ) ≤ m)
  obtain ⟨b, hb⟩ := (le_ordFn_iff hϖ c 1).1 h1
  exact ⟨b, by rw [hb, zpow_one, map_mul]⟩

def secLin {X : Scheme.{0}} {L : LB X} {n : ℕ} (c : Fin n → Γ(X, ⊤)) (t : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (c i) * (t i).f j
  compat := fun j j' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (c i) (t i)).compat j j'

variable {D : DegData V (maximalIdeal V)}

theorem exists_pull {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ} {α : D.toPre.X}
    (β : D.toPre.SecB k α) :
    ∃ s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k)),
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) β (DegPre.prB D.toPre F).left 1 := by
  have hL := D.toPre.P.isLB
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α i) (DegPre.famε k)
      (DegPre.famφ D.toPre F α) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ β (DegPre.prB D.toPre F).left)
  exact ⟨t, SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
    ((ht _ _ y J hJ).trans (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ)).symm⟩

theorem exists_int_of_vge (hϖ : Irreducible ϖ) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))} {r : ℚ}
    (hr : 0 < r) (hs : VGe D (FractionRing V) (ordVal hϖ) k α s r) :
    ∃ f f' : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      SecIsMul D.toPre.P.A.hom ϖ f f' := by
  obtain ⟨n, a, σ, σF, hσ, hva, hsum⟩ := hs
  choose b hb using fun i => exists_eq_of_pos hϖ (lt_of_lt_of_le (by exact_mod_cast hr) (hva i))
  refine ⟨secLin (fun i => scal D.toPre.P.A.hom (ϖ * b i)) σ, secLin (fun i => scal D.toPre.P.A.hom (b i)) σ,
    SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun j => ?_⟩
  · rw [SectionScalarValuation.sval_lin (fun i => scal D.toPre.P.A.hom (ϖ * b i)) σ (fun _ => rfl) _ y hJ,
      SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF (fun j => hsum j) (𝟙 _) y hJ]
    refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (SectionScalarValuation.secScal_sval (hσ i) _ y hJ)
    have e1 : gs (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y ⊤ (scal D.toPre.P.A.hom (ϖ * b i)) =
        cst ((𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom) y (ϖ * b i) :=
      gs_pull _ _ y ⊤ trivial _
    have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (a i)) =
        cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (a i) :=
      gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
    have e3 : (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom =
        ((𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) ≫
          spMap (algebraMap (FractionRing V) (FractionRing V))) ≫ spMap (algebraMap V (FractionRing V)) := by
      rw [Category.id_comp, Category.id_comp, Category.assoc, Over.w]
      exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
    rw [e1, e2, e3, cst_comp, cst_comp, hb i]
    rfl
  · show ∑ i, resTop _ (scal D.toPre.P.A.hom (ϖ * b i)) * (σ i).f j =
      resTop _ (scal D.toPre.P.A.hom ϖ) * ∑ i, resTop _ (scal D.toPre.P.A.hom (b i)) * (σ i).f j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [scal, resTop, map_mul, _root_.mul_assoc]

end FamInt

theorem integralFamily_of_strictMin : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (q : ℕ), 1 ≤ q → ∀ (χ : D.toPre.X) (β : D.toPre.SecB q χ), (∀ z, z ≠ 0 → Q χ < Q (χ + q • z)) → ∃ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α) (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing V)).left 1) ∧ f χ = β ∧ (∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0) ∧ ∀ α, α ≠ χ → ∃ f' : D.toPre.SecB q α, SecIsMul D.toPre.P.A.hom ϖ (f α) f' := by
  intro hL V _ _ _ ϖ hϖ D Q hQ q hq χ β hmin
  classical
  obtain ⟨σ, hσ⟩ := FamInt.exists_pull (F := FractionRing V) β
  obtain ⟨Φ, hΦ, hΦ0⟩ := UUA.exists_fam_rep (F := FractionRing V) hL.globalFns D.tau_bimult q χ (fun a b h => by
    have h' : (q : ℤ) • a = (q : ℤ) • b := by
      rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
    exact smul_right_injective D.toPre.X (by omega : (q : ℤ) ≠ 0) h') σ
  have h0 : VGe D (FractionRing V) (FamInt.ordVal hϖ) q χ (Φ.s χ) 0 := by
    refine ⟨1, fun _ => 1, fun _ => β, fun _ => Φ.s χ, fun _ => hΦ ▸ hσ, fun _ => ?_, fun j => ?_⟩
    · simp
    · simp [DegPre.constBF]
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB q α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      (∀ h : χ = α, f = h ▸ β) ∧ ((∀ z, α ≠ χ + q • z) → ∀ j, f.f j = 0) ∧
      (α ≠ χ → ∃ f' : D.toPre.SecB q α, SecIsMul D.toPre.P.A.hom ϖ f f') := by
    intro α
    by_cases hα : χ = α
    · subst hα
      exact ⟨β, hΦ ▸ hσ, fun _ => rfl, fun h => absurd (by simp) (h 0), fun h => absurd rfl h⟩
    by_cases hc : ∃ z, α = χ + q • z
    · obtain ⟨z, rfl⟩ := hc
      have hz : z ≠ 0 := by rintro rfl; exact hα (by simp)
      have H := SectionScalarValuation.fe_move hϖ hQ (FamInt.valOver_ordVal hϖ) q z χ Φ h0
      have hlt := hmin z hz
      rw [q_shift hϖ hQ, lt_add_iff_pos_right] at hlt
      have hpos : (0 : ℤ) < q * Q z + QForm.bOf D.toPre Q z χ := (pos_iff_pos_of_mul_pos hlt).1 (by omega)
      obtain ⟨f, f', h1, h2⟩ := FamInt.exists_int_of_vge hϖ (by rw [zero_add]; exact_mod_cast hpos) H
      exact ⟨f, h1, fun h => absurd h hα, fun h => absurd rfl (h z), fun _ => ⟨f', h2⟩⟩
    · refine ⟨SecOps.secZero, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun h => absurd h hα,
        fun _ _ => rfl, fun _ => ⟨SecOps.secZero, fun j => (mul_zero _).symm⟩⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e.symm⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 h4 using key
  exact ⟨Φ, f, h1, h2 χ rfl, h3, h4⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.GermBasic

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

section Point

variable {V : Type} [CommRing V] [IsDomain V] {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem gf_ext {Z : Scheme.{0}} {a b : Z ⟶ (UnifPre.GF (R := V) (G := G) F).left}
    (h₁ : a ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left =
      b ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left)
    (h₂ : a ≫ UnifPre.gFK (R := V) (G := G) F = b ≫ UnifPre.gFK (R := V) (G := G) F) : a = b := by
  have w : (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ pullback.snd G.hom (jK V) =
      (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ jFK (R := V) F :=
    (Over.w (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G))).trans
      (Over.w (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G))).symm
  have h₃ : a ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left =
      b ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans (h₂.trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) w).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ jFK (R := V) F) h₁).trans ((Category.assoc _ _ _).trans
          ((congrArg (b ≫ ·) w).symm.trans (Category.assoc _ _ _).symm)))))
  exact pullback.hom_ext h₁ h₃

theorem gf_exists {Z : Scheme.{0}} (p : Z ⟶ Sp F) (g : Z ⟶ G.left) (h : g ≫ G.hom = p ≫ jFK (R := V) F ≫ jK V) :
    ∃ a : Z ⟶ (UnifPre.GF (R := V) (G := G) F).left,
      a ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = p ∧
      a ≫ UnifPre.gFK (R := V) (G := G) F = g := by
  let T : Over (TK V).left := Over.mk (p ≫ jFK (R := V) F)
  let u : T ⟶ TFK (R := V) F := Over.homMk p rfl
  let v : T ⟶ (Over.pullback (jK V)).obj G :=
    Over.homMk (pullback.lift g (p ≫ jFK (R := V) F) (h.trans (Category.assoc _ _ _).symm)) (pullback.lift_snd _ _ _)
  refine ⟨(lift u v).left, congrArg (fun q => q.left) (lift_fst u v), ?_⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ pullback.fst G.hom (jK V)) (lift_snd u v)).trans
    (pullback.lift_fst _ _ _))

variable [Algebra V F] [IsScalarTower V (FractionRing V) F]

theorem exists_jetPt {κ : Type} (z : JetPts G κ) (m : ℕ) :
    ∃ zF : Sp (Jet F κ m) ⟶ (UnifPre.GF (R := V) (G := G) F).left,
      zF ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = spMap (algebraMap F (Jet F κ m)) ∧
      zF ≫ UnifPre.gFK (R := V) (G := G) F = spMap (jetCoef (algebraMap V F) κ m) ≫ (z m).left := by
  refine gf_exists _ _ ?_
  have w : (z m).left ≫ G.hom = spMap (algebraMap V (Jet V κ m)) ≫ 𝟙 _ := Over.w (z m)
  have e : jFK (R := V) F ≫ jK V = spMap (algebraMap V F) :=
    (spMap_comp_eq (algebraMap V (FractionRing V)) (algebraMap (FractionRing V) F)).trans
      (congrArg spMap (IsScalarTower.algebraMap_eq V (FractionRing V) F).symm)
  rw [Category.assoc, w, e, Category.comp_id, spMap_comp_eq, spMap_comp_eq, JetTr.jetCoef_alg]

end Point

theorem psJet_sum {F κ : Type} [CommRing F] [Fintype κ] [DecidableEq κ] (m : ℕ) {l : ℕ} (c : Fin l → F)
    (f : Fin l → MvPowerSeries κ F) :
    psJet m (∑ i, c i • f i) = ∑ i, algebraMap F (Jet F κ m) (c i) * psJet m (f i) := by
  have h : psTrunc m (∑ i, c i • f i) = ∑ i, MvPolynomial.C (c i) * psTrunc m (f i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [psTrunc, map_sum, Finset.mul_sum, MvPolynomial.C_mul_monomial, map_smul, smul_eq_mul]
    exact Finset.sum_comm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [psJet, h, map_sum]
  rfl

theorem val_congr {X Y Y' Z Z' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {φ : Y ⟶ X} {φ' : Y' ⟶ X}
    (t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (1 : ℤ))))
    (t' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => φ') (fun _ => (1 : ℤ)))) (h : Z ⟶ Y) (h' : Z ⟶ Y')
    (H : ∀ y J, Good L y J → val t h y J = val t' h' y J) (r : Z' ⟶ Z) (y : Z') (J) (hJ : Good L y J) :
    val t (r ≫ h) y J = val t' (r ≫ h') y J := by
  have hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h') :=
    corr_of_val hL fun y J hJ => by rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, H y J hJ]
  rw [← val_pull hJ, ← val_pull hJ, val_corr hJ hc]

theorem main : AGermSt := by
  intro V _ _ _ _ D A G _ _ U κ _ _ z hz τ hτ F _ _ _ _ q
  have hL := U.LG.isLB
  refine ⟨fun σ' f f' hf hf' => ?_, fun l c σ f σ' hf hσ m => ?_, fun htr σ' => ?_⟩
  · refine GermFun.psJet_inj fun m => ?_
    obtain ⟨a, a₁, a₂, ha⟩ := hf m
    obtain ⟨b, b₁, b₂, hb⟩ := hf' m
    obtain rfl : a = b := gf_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)
    refine H1.cst_ext fun y => ?_
    obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
    exact (Units.mul_left_inj _).1 ((ha y J hJ).symm.trans (hb y J hJ))
  · obtain ⟨a, a₁, a₂⟩ := exists_jetPt (F := F) z m
    refine ⟨a, a₁, a₂, fun y J hJ => ?_⟩
    refine (SectionScalarValuation.sval_lin _ σ hσ a y hJ).trans ?_
    have e : gs (𝟙 _) y ⊤ (toΓ _ (psJet m (∑ i, c i • f i))) =
        ∑ i, cst (𝟙 _) y (algebraMap F (Jet F κ m) (c i)) * cst (𝟙 _) y (psJet m (f i)) := by
      refine (congrArg (cst (𝟙 _) y) (psJet_sum m c f)).trans ((ExpansionValueZero.cst_sum _ _ _ _).trans ?_)
      exact Finset.sum_congr rfl fun i _ => H1.cst_mul _ _ _ _
    rw [e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨b, b₁, b₂, hb⟩ := hf i m
    obtain rfl : a = b := gf_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)
    rw [hb y J hJ, _root_.mul_assoc]
    refine congrArg₂ (· * ·) ?_ rfl
    refine (gs_pull a _ y ⊤ trivial _).trans ?_
    rw [a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]
    rfl
  · choose a a₁ a₂ using exists_jetPt (F := F) z
    have hv : ∀ m, ∃ v : Jet F κ m, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet F κ m)) (y : Z) (J), Good U.LG.L y J →
        sval σ' (r ≫ a m) y J = cst r y v * (val (τ m) (r ≫ spMap (jetCoef (algebraMap V F) κ m)) y J ^ q).val := by
      intro m
      obtain ⟨v, hv⟩ := ExpansionValueZero.exists_coeff (A := Jet F κ m) hL σ' (a m)
        (GeneratorPullback.powGen U.LG.L _ _ (LB.pullGen U.LG.L _ _ (τ m) (spMap (jetCoef (algebraMap V F) κ m))) q)
        (powGen_isGen_of_isGen _ (pullGen_isGen _ _ _ _ (hτ m) _) q) (fun W _ h => by simp only [a₂ m, _root_.mul_one])
      refine ⟨v, fun Z r y J hJ => (hv Z r y J hJ).trans ?_⟩
      rw [← val_pull hJ]
      exact congrArg (fun u => cst r y v * Units.val u) (map_pow _ _ _)
    choose v hv using hv
    have hc : ∀ m, (jetTrunc : Jet F κ (m + 1) →ₐ[F] Jet F κ m) (v (m + 1)) = v m := by
      intro m
      let ρ := spMap ((jetTrunc : Jet F κ (m + 1) →ₐ[F] Jet F κ m) : Jet F κ (m + 1) →+* Jet F κ m)
      let ρV := spMap ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)
      have hρ : ρ ≫ spMap (jetCoef (algebraMap V F) κ (m + 1)) = spMap (jetCoef (algebraMap V F) κ m) ≫ ρV := by
        rw [spMap_comp_eq, spMap_comp_eq, JetTr.jetCoef_trunc]
      have hzt : ρV ≫ (z (m + 1)).left = (z m).left := congrArg (fun q => q.left) (hz.1 m)
      have ha : ρ ≫ a (m + 1) = a m := gf_ext
        (by rw [Category.assoc, a₁, a₁]; exact spMap_comp_alg _)
        (by rw [Category.assoc, a₂, a₂, ← Category.assoc, hρ, Category.assoc, hzt])
      refine H1.cst_ext fun y => ?_
      obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
      have e₁ := hv (m + 1) _ ρ y J hJ
      have e₀ := hv m _ (𝟙 _) y J hJ
      rw [Category.id_comp, Category.id_comp] at e₀
      rw [ha, hρ, val_congr hL (τ (m + 1)) (τ m) ρV (𝟙 _) (htr m) _ y J hJ, Category.comp_id] at e₁
      refine Eq.trans ?_ ((Units.mul_left_inj _).1 (e₁.symm.trans e₀))
      exact (ExpansionValueZero.cst_comp (𝟙 _) _ y _).symm.trans (congrArg (fun r => cst r y (v (m + 1))) (Category.id_comp _))
    obtain ⟨f, hf⟩ := GermD.exists_ps_of_jets v hc
    refine ⟨f, fun m => ⟨a m, a₁ m, a₂ m, fun y J hJ => ?_⟩⟩
    have e₀ := hv m _ (𝟙 _) y J hJ
    rw [Category.id_comp, Category.id_comp, ← hf m] at e₀
    exact e₀

end GlobalTheory.GermBasic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBessel
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBessel
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_regular_rep_vec_bigPt_eq_bessel :
    ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ γ ∈ JF.Om P.k P.r p.T.base.z p.T.base.z', Formalism.QuantumDeterminants.Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) ∧ ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), p.V F (TBB.bigPt P.r c) = B.JF p.T.base F γ := by
  intro P Wp Wq _ _ _ _ _ _ p d hl0 hG
  have hd : ∀ a, d a ≠ 0 := fun a =>
    (hl0.1 (1, d a) (by unfold TBB.bigPt; exact List.mem_ofFn.2 ⟨a, rfl⟩)).2
  have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) := hl0
  have hG' : 0 < D.ptG (Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z * Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z') P.r
      (Formalism.FourierDecayAlt.P.PBJ.bigPt d) := hG
  have h' := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'
  obtain ⟨hγ, hZγ, -⟩ := h'.choose_spec
  have hpos : 0 < Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]; exact hG'
  refine ⟨h'.choose, ⟨hγ, fun l _ => ?_, hpos⟩, hZγ, fun F => ?_⟩
  · unfold Formalism.QuantumDeterminants.Dmin
    rw [hZγ, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hd _
  · show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d) = _
    unfold D.vecV
    rw [dite_eq_left ⟨hl, hG'⟩, dite_eq_left h']
    have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1
    rw [hw] at hmono
    rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ hpos hnz (hZγ.trans hmono) F]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBesselStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regularRep_besselBigCellVector_eq_bessel : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ γ ∈ JF.Om P.k P.r p.T.base.z p.T.base.z', Formalism.QuantumDeterminants.Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) ∧ ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), p.V F (TBB.bigPt P.r c) = B.JF p.T.base F γ := by
  first | exact @GlobalTheory.exists_regular_rep_vec_bigPt_eq_bessel | exact GlobalTheory.exists_regular_rep_vec_bigPt_eq_bessel | (intros; apply GlobalTheory.exists_regular_rep_vec_bigPt_eq_bessel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormNatEqOne
open Cardinal
namespace GlobalTheory.MomOne.Inh

theorem mk_le {A X : Type} [MetricSpace X] (f : A → X) (hf : DenseRange f) (hA : #A ≤ 𝔠) :
    #X ≤ 𝔠 := by
  have h : ∀ x : X, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := fun x => by
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa only [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (by rw [hxy]; exact hs y)
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right hA).trans_eq Cardinal.continuum_power_aleph0

theorem nonempty_iso (p : ℕ) [Fact p.Prime] : Nonempty (ℂ ≃+* ℂ_[p]) := by
  have h1 : #ℚ_[p] ≤ 𝔠 := mk_le _ (Padic.denseRange_ratCast p)
    (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
  have h2 : #(PadicAlgCl p) ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans (max_le h1 Cardinal.aleph0_le_continuum)
  have h3 : #(ℂ_[p]) ≤ 𝔠 := mk_le (X := PadicComplex p) _
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) h2
  have h4 : 𝔠 ≤ #(ℂ_[p]) := continuum_le_cardinal_of_nontriviallyNormedField _
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) ?_
  exact Cardinal.eq.1 (by rw [Cardinal.mk_complex]; exact le_antisymm h4 h3)

end GlobalTheory.MomOne.Inh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqOneOfMultilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemSpanBoxFamilyPowerDegData
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemSpanBoxFamilyPowerDegData
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem mem_span_boxFam : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ S : Fam D'.toPre F k, S ∈ Submodule.span F {S' | ∃ s : Fin j → Fam D.toPre F k, IsBoxFam pD F k S' s} := by
  intro hL hL₂ _ _ V _ _ _ _ j D D' pD F _ _ k hk S
  obtain ⟨hf, hd⟩ := FamDimension.finrank_fam (D := D.toPre) (F := F) hL.globalFns hL₂.secTwist D.tau_bimult hk
  obtain ⟨hf', hd'⟩ := FamDimension.finrank_fam (D := D'.toPre) (F := F) hL.globalFns hL₂.secTwist D'.tau_bimult hk
  obtain ⟨hr, hg⟩ := rank_and_g_of_isPowDeg V j D.toPre D'.toPre pD
  let b := Module.finBasis F (Fam D.toPre F k)
  choose b' hb' using fun a : Fin j → Fin (Module.finrank F (Fam D.toPre F k)) =>
    BoxFamily.exists_isBoxFam hL.globalFns V j D.toPre D'.toPre pD F k (fun i => b (a i))
  have hi : LinearIndependent F b' :=
    boxFam_linearIndependent V j D.toPre D'.toPre pD F k _ b b.linearIndependent b' hb'
  have hc : Fintype.card (Fin j → Fin (Module.finrank F (Fam D.toPre F k))) =
      Module.finrank F (Fam D'.toPre F k) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hd, hd', hr, hg, ← pow_mul, ← mul_add, mul_comm]
  have ht : Submodule.span F (Set.range b') = ⊤ := hi.span_eq_top_of_card_eq_finrank' hc
  have hS : S ∈ Submodule.span F (Set.range b') := ht ▸ Submodule.mem_top
  refine Submodule.span_mono ?_ hS
  rintro _ ⟨a, rfl⟩
  exact ⟨_, hb' a⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemSpanBoxFamilyPowerDegDataStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_boxFamily_powerDegData : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ S : Fam D'.toPre F k, S ∈ Submodule.span F {S' | ∃ s : Fin j → Fam D.toPre F k, IsBoxFam pD F k S' s} := by
  first | exact @GlobalTheory.mem_span_boxFam | exact GlobalTheory.mem_span_boxFam | (intros; apply GlobalTheory.mem_span_boxFam <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem pow_eq_one_of_multilinear {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] {j : ℕ} (bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => M) N)
    (hspan : ∀ S : N, S ∈ Submodule.span F {S' | ∃ s, S' = bx s})
    (U : Fin j → Module.End F M) (W : Module.End F N)
    (hW : ∀ s, W (bx s) = bx (fun i => U i (s i)))
    (hU : ∀ i, ∃ m : ℕ, 1 ≤ m ∧ U i ^ m = 1) : ∃ m : ℕ, 1 ≤ m ∧ W ^ m = 1 := by
  classical
  choose m hm hU using hU
  have hp : ∀ (n : ℕ) s, (W ^ n) (bx s) = bx (fun i => (U i ^ n) (s i)) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ', Module.End.mul_apply, ih, hW]
      simp only [pow_succ', Module.End.mul_apply]
  refine ⟨∏ i, m i, Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => by
    have := hm i; omega), LinearMap.ext fun S => ?_⟩
  refine LinearMap.eqOn_span' (s := {S' | ∃ s, S' = bx s}) ?_ (hspan S)
  rintro _ ⟨s, rfl⟩
  rw [hp]
  have : ∀ i, U i ^ (∏ i, m i) = 1 := fun i => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    rw [hc, pow_mul, hU, one_pow]
  simp only [this, Module.End.one_apply]

theorem finOrd_box : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (p' : QkPt D'.toPre F k) (p : Fin j → QkPt D.toPre F k), IsBoxQk pD F k p' p → ∀ (w : ∀ i, LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F (p i).g.b) (DegPre.lineε k))) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε k))), (∀ i, (w i).IsGen) → w'.IsGen → (∀ (s s₁ : Fin j → Fam D.toPre F k) (S S₁ : Fam D'.toPre F k), (∀ i, PhiRel D.toPre F k (p i) (w i) (s i) (s₁ i)) → IsBoxFam pD F k S s → IsBoxFam pD F k S₁ s₁ → PhiRel D'.toPre F k p' w' S S₁) → ∀ ζ : Fin j → F, (∀ i, FinOrd D F k (p i) (w i) (ζ i)) → FinOrd D' F k p' w' (∏ i, ζ i) := by
  intro hL hL2 hL4 hT V _ _ _ _ j D D' pD F _ _ k hk p' p _ w w' hw hw' hc ζ h
  have hG := hL.globalFns
  obtain ⟨bx, hbx⟩ := GlobalTheory.T.exists_boxFamily_multilinear_map hG V j D.toPre D'.toPre pD F k
  have hspan := GlobalTheory.T.mem_span_boxFamily_powerDegData hL hL2 hL4 hT V j D D' pD F k hk
  simp only [hbx] at hspan
  choose Φ hΦ using fun i => phiFun_of_globalFns hG V _ D F k hk (p i) (w i) (hw i)
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG V _ D' F k hk p' w' hw'
  refine (ThetaFinOrd.finOrd_iff p' w' _ Φ' hΦ').2 (pow_eq_one_of_multilinear bx hspan
    (fun i => ζ i • Φ i) _ (fun s => ?_)
    (fun i => (ThetaFinOrd.finOrd_iff (p i) (w i) _ (Φ i) (hΦ i)).1 (h i)))
  have e := (hΦ' _ _).1 (hc s (fun i => Φ i (s i)) _ _ (fun i => (hΦ i _ _).2 rfl)
    ((hbx _ _).2 rfl) ((hbx _ _).2 rfl))
  simp only [LinearMap.smul_apply]
  rw [← e, MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]

end GlobalTheory
end
end
