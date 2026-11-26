module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TautologicalModel
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieMultTensorOfFinrank
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM


open GlobalTheory.TensorDet GlobalTheory.Serre in
theorem lieMult_tensor_of_finrank {O O' M R k : Type} [CommRing O] [CommRing O'] [Algebra O O'] [AddCommGroup M]
    [Module O M] [Module O' M] [IsScalarTower O O' M] [Module.Finite O M] [Module.Projective O M] [CommRing R]
    [Field k] [Algebra O k] {G A : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
    (hs : Smooth G.hom) (v : epsR R ⟶ G) (hv : IsLieBasis ![v]) (a : OAct O G) (κ : O →+* R) (b₀ : OAct O' A)
    (τ : IsTensor A (comapAct b₀ (algebraMap O O')) G a M)
    (hκ : ∀ c, IsLieComb ![κ c] ![v] (v ≫ a.act c)) (hlin : ∀ (x : O') m, τ.tmul (x • m) = τ.tmul m ≫ b₀.act x)
    (β : R →+* k) (hβ : ∀ c, algebraMap O k c = β (κ c)) (χ : O' →+* k) (n : ℕ)
    (hn : Module.finrank k (EigenSplit.eigenSub (rightAction k O O' M) χ) = n) : LieMult b₀ (spMap β) χ n := by
  have hG := isGrpPullback_pullback G (spMap β)
  have hA := isGrpPullback_pullback A (spMap β)
  obtain ⟨v', hv', hvv⟩ := exists_isLieBasis_baseChange R k β G _ _ hG hs 1 ![v] hv
  have ev : ![v' 0] = v' := by
    funext i
    fin_cases i
    rfl
  have hv₁ : (v' 0).left ≫ pullback.fst G.hom (spMap β) = spMap (Chart.dualMapR β) ≫ v.left := hvv 0
  have hb : IsLieBasis ![v' 0] := ev.symm ▸ hv'
  generalize v' 0 = v₁ at hv₁ hb
  have hL := isLinearPullback_pullback (comapAct b₀ (algebraMap O O')) (spMap β)
  let b : OAct O ((Over.pullback (spMap β)).obj A) := comapAct (b₀.pullback (spMap β) A) (algebraMap O O')
  let τ₁ : IsTensor _ b _ (a.pullback (spMap β) G) M :=
    τ.baseChange (isLinearPullback_pullback a (spMap β)) ⟨hA, hL.2⟩
  have ht : ∀ m, τ₁.tmul m = (Over.pullback (spMap β)).map (τ.tmul m) := fun m => τ.pullback_tmul (spMap β) m
  obtain ⟨Φ, inj, tan, add, smul, -, eqv⟩ := SerreLie.exists_lie_tensor k _ O M _ _ b τ₁ v₁ hb (fun c => by
    have h := (lieComb_baseChange R k β G _ _ hG 1 ![v] (v ≫ a.act c) ![κ c] ![v₁]
      (v₁ ≫ (a.pullback (spMap β) G).act c) (fun j => by fin_cases j; exact hv₁) (hκ c)).1 (by
        rw [Over.comp_left, Category.assoc, (isLinearPullback_pullback a (spMap β)).2, ← Category.assoc]
        exact (congrArg (· ≫ (a.act c).left) hv₁).trans (Category.assoc _ _ _))
    convert h using 2 with i
    fin_cases i
    exact hβ c)
  have : Module.Finite k (k ⊗[O] M) := inferInstance
  have := lieMult_of_param (b₀.pullback (spMap β) A) (rightAction k O O' M) Φ inj tan add smul
    (fun x y => by
      rw [rightAction_apply, eqv]
      congr 1
      have := (b₀.pullback (spMap β) A).hom x
      refine τ₁.hom_ext fun m => ?_
      rw [IsTensor.tmul_mapLeft, ht, ht]
      exact (congrArg _ (hlin x m)).trans (Functor.map_comp _ _ _)) χ hn
  have h2 := (LiePull.lieMult_pull _ _ _ _ _ _ _ b₀ (b₀.pullback (spMap β) A) hA
    (isLinearPullback_pullback b₀ (spMap β)).2 k (𝟙 _) χ n).1 this
  rwa [Category.id_comp] at h2


open GlobalTheory.TensorDet GlobalTheory.Serre in
theorem hasType_of_isTen : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [CharZero R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)), Nonempty (IsTen C D h T) → HasType H T.t.act (2 * ω - 1) (D.p + D.q) 0 := by
  set_option synthInstance.maxHeartbeats 400000 in
    rintro - E _ _ _ H R _ _ ω C D h T ⟨t⟩ k _ _ β hβ χ
    have : CharZero k := β.charZero_iff hβ |>.1 inferInstance
    obtain ⟨κ, hκw, hκ⟩ := LieChar.ell_char E H R ω C
    obtain ⟨-, hgen, -, -, -, hM⟩ := OK_isDedekindDomain_and_projective E H
    obtain ⟨_, _, -⟩ := hM D.La D.fin D.proj
    let _ : Algebra (OK H) k := (β.comp κ).toAlgebra
    have := C.P.smoothDim
    have key := lieMult_tensor_of_finrank (SmoothOfRelativeDimension.smooth C.P.g C.P.A.hom) C.v C.basis C.act κ
      T.t.act t.ten hκ t.lin β (fun _ => rfl) χ
    have hw : algebraMap (OK H) (𝓞 E) (wK H) = H.w0 := rfl
    have hrt : algebraMap (OK H) (𝓞 E) (2 * wK H - 1) = H.rt := by
      rw [map_sub, map_mul, hw, map_ofNat, H.two_weight_eq_one_add_root, map_one, add_sub_cancel_left]
    have hr : β (2 * ω - 1) = algebraMap (OK H) k (2 * wK H - 1) := by
      change _ = β (κ _)
      simp only [map_sub, map_mul, map_ofNat, map_one, hκw]
    rw [hr]
    refine ⟨fun h => key _ ((finrank_eigenSub χ (RingHom.ext fun c => ?_)).trans D.rank), fun h => ?_⟩
    · have hw' : χ (algebraMap (OK H) (𝓞 E) (wK H)) = algebraMap (OK H) k (wK H) := by
        rw [← hrt] at h
        simp only [map_sub, map_mul, map_ofNat, map_one] at h
        linear_combination h / 2
      obtain ⟨m, rfl, -⟩ := hgen c
      simp only [RingHom.comp_apply, map_add (f := _), map_mul, map_intCast, hw']
    · refine key _ (Submodule.finrank_eq_zero.2 ((Submodule.eq_bot_iff _).2 fun y hy => ?_))
      have h1 := EigenSplit.mem_eigenSub.1 hy H.rt
      have h2 : rightAction k (OK H) (𝓞 E) D.La H.rt = algebraMap (OK H) k (2 * wK H - 1) • LinearMap.id := by
        ext m
        simp only [TensorProduct.AlgebraTensorModule.curry_apply,
          TensorProduct.curry_apply, LinearMap.coe_restrictScalars, rightAction_tmul, LinearMap.smul_apply,
          LinearMap.id_apply]
        rw [← hrt, algebraMap_smul, TensorProduct.tmul_smul, ← algebraMap_smul k]
      rw [h2] at h1
      have h3 : (χ H.rt - algebraMap (OK H) k (2 * wK H - 1)) • y = 0 := by
        rw [sub_smul, ← h1]; exact sub_self _
      exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 h)

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilIsOfLbIsoCubeLB
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PairingOfLam

open ReciprocityTheory.ChartRestriction.G.Out DescentPairing AdjointOfPairing

theorem val_ratio {X X' Y Y₀ B : Scheme.{0}} {L : LB X} {N : LB X'} (hL : L.IsLB) (hN : N.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y₀ ⟶ X')} {ε' : K' → ℤ}
    (H : LBIso (LB.LinComb N φ' ε') (LB.LinComb L φ ε)) (h : Y ⟶ Y₀)
    (t : LB.Gen (LB.LinComb L (fun k => h ≫ φ k) ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb N (fun k => h ≫ φ' k) ε')) (ht' : t'.IsGen) (p : Y ⟶ B)
    (hp : Function.Surjective p.appTop.hom) {Z : Scheme.{0}} (r r' : Z ⟶ Y) (e₁ : r ≫ h = r' ≫ h)
    (e₂ : r ≫ p = r' ≫ p) (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good N z J') :
    val t r z J * (val t' r z J')⁻¹ = val t r' z J * (val t' r' z J')⁻¹ := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ (i : K → L.ι) (i' : K' → N.ι),
      LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart N (fun k => h ≫ φ' k) i' ≤
        h ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart N φ' i') := fun i i' y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i i',
      r z ∈ LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart N (fun k => h ≫ φ' k) i' →
      gm r z _ (res inf_le_left (t.s i) * (res (le i i') (pullU h _ (w.s (i, i'))) * res inf_le_right (t'.s i'))⁻¹) =
        gm r z (LB.wchart L (fun k => h ≫ φ k) i) (t.s i) *
          (gm (r ≫ h) z (LB.wchart L φ i ⊓ LB.wchart N φ' i') (w.s (i, i')) *
            gm r z (LB.wchart N (fun k => h ≫ φ' k) i') (t'.s i'))⁻¹ :=
    fun Z r z i i' hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res r z _ hz _).trans (gm_pull r h z _ (le i i' hz) _)) (gm_res r z _ hz _))))))
  obtain ⟨c, hc⟩ := glue_unit (⊤ : Y.Opens)
    (fun i : (K → L.ι) × (K' → N.ι) =>
      LB.wchart L (fun k => h ≫ φ k) i.1 ⊓ LB.wchart N (fun k => h ≫ φ' k) i.2) (fun _ => le_top)
    (fun y _ => by
      choose i hi using fun k => exists_chart hL (φ k (h y))
      choose i' hi' using fun k => exists_chart hN (φ' k (h y))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), Set.mem_iInter.2 hi, Set.mem_iInter.2 hi'⟩)
    (fun i => res inf_le_left (t.s i.1) *
      (res (le i.1 i.2) (pullU h _ (w.s (i.1, i.2))) * res inf_le_right (t'.s i.2))⁻¹)
    (fun i j y hy => by
      have hm : (𝟙 Y ≫ h) y ∈ LB.wchart L φ i.1 ⊓ LB.wchart N φ' i.2 ⊓ (LB.wchart L φ j.1 ⊓ LB.wchart N φ' j.2) :=
        ⟨le _ _ hy.1, le _ _ hy.2⟩
      have e : gm (𝟙 Y ≫ h) y (LB.wchart L φ i.1 ⊓ LB.wchart N φ' i.2) (w.s (i.1, i.2)) =
          trF φ ε (𝟙 Y ≫ h) y i.1 j.1 * (trF φ' ε' (𝟙 Y ≫ h) y i.2 j.2)⁻¹ *
            gm (𝟙 Y ≫ h) y (LB.wchart L φ j.1 ⊓ LB.wchart N φ' j.2) (w.s (j.1, j.2)) :=
        (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y ≫ h) y _) (hw (i.1, i.2) (j.1, j.2))).trans
          ((map_mul _ _ _).trans (congrArg₂ (· * ·)
            ((gm_div (LB.LinComb N φ' ε') (LB.LinComb L φ ε) _ y (i.1, i.2) (j.1, j.2) hm).trans
              (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ ε _ y _ _ hm.1.1 hm.2.1)
                (gm_linComb N φ' ε' _ y _ _ hm.1.2 hm.2.2))) (gm_res _ y _ hm _))))
      have f₁ : trF φ ε (𝟙 Y ≫ h) y i.1 j.1 = trF (fun k => h ≫ φ k) ε (𝟙 Y) y i.1 j.1 := by
        simp only [trF, Category.assoc]
      have f₂ : trF φ' ε' (𝟙 Y ≫ h) y i.2 j.2 = trF (fun k => h ≫ φ' k) ε' (𝟙 Y) y i.2 j.2 := by
        simp only [trF, Category.assoc]
      refine (hv _ _ y _ _ hy.1).trans (Eq.trans ?_ (hv _ _ y _ _ hy.2).symm)
      rw [e, f₁, f₂,
        gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, gen_trans ht' (𝟙 Y) y hy.1.2 hy.2.2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  obtain ⟨a, ha⟩ := hp c.val
  have hcv : ∀ r : Z ⟶ Y, (gm r z ⊤ c).val = gs (r ≫ p) z ⊤ a := fun r =>
    (gs_unit r z ⊤ trivial _).symm.trans ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a))
  have key : ∀ r : Z ⟶ Y, gm r z ⊤ c = val t r z J *
      (gm (r ≫ h) z (LB.wchart L φ (fun k => J ((r ≫ h) ≫ φ k)) ⊓ LB.wchart N φ' (fun k => J' ((r ≫ h) ≫ φ' k)))
        (w.s (fun k => J ((r ≫ h) ≫ φ k), fun k => J' ((r ≫ h) ≫ φ' k))) * val t' r z J')⁻¹ := fun r => by
    have hz : r z ∈ LB.wchart L (fun k => h ≫ φ k) (fun k => J ((r ≫ h) ≫ φ k)) ⊓
        LB.wchart N (fun k => h ≫ φ' k) (fun k => J' ((r ≫ h) ≫ φ' k)) :=
      ⟨Set.mem_iInter.2 fun k => hJ ((r ≫ h) ≫ φ k), Set.mem_iInter.2 fun k => hJ' ((r ≫ h) ≫ φ' k)⟩
    rw [val_of t r z J (fun k => J ((r ≫ h) ≫ φ k)) (fun k => by rw [Category.assoc]),
      val_of t' r z J' (fun k => J' ((r ≫ h) ≫ φ' k)) (fun k => by rw [Category.assoc])]
    exact (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (_, _))).trans (hv Z r z _ _ hz))
  have q : gm r z ⊤ c = gm r' z ⊤ c := Units.ext (by rw [hcv, hcv, e₂])
  rw [key, key, e₁] at q
  apply Additive.ofMul.injective
  have q' := congrArg Additive.ofMul q
  simp only [ofMul_mul, ofMul_inv] at q' ⊢
  linear_combination (norm := abel) q'

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

theorem exists_gen_lam (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {N : RigLB A} (cb : CubicalStr A N)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (a g : B ⟶ A) [IsMonHom g] (n : ℕ) (y : T ⟶ B)
    (hy : (y ≫ a) ^ n = 1) :
    ∃ t : LB.Gen (LB.LinComb N.L (fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T B ≫ y) (snd T B ^ n)).left ≫
        (psum A ![fst B B ≫ a, snd B B ≫ g] I.down).left) (fun I => (-1) ^ (2 - I.down.card))),
      t.IsGen ∧ ∀ (z : T ⟶ B) (e : Γ(T.left, ⊤)ˣ), z ^ n = 1 → WeilIs A N.L n (y ≫ a) (z ≫ g) e →
        ∀ (p : T.left) (J), Good N.L p J →
          val t (lift (𝟙 T) z).left p J = val t (lift (𝟙 T) (1 : T ⟶ B)).left p J * gm (𝟙 T.left) p ⊤ e := by
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_pairing hG hA cb p₀ hT n (y ≫ a) hy
  obtain ⟨σ, hσ⟩ := exists_frame N.isLB (K := Fin 2) ![(y ≫ a).left, (1 : T ⟶ A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen N.isLB
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T B ≫ y) (snd T B ^ n)).left ≫
        (psum A ![fst B B ≫ a, snd B B ≫ g] I.down).left) (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ h => by
      have e : ∀ I, (lift (fst T B ≫ y) (snd T B ^ n)).left ≫ (psum A ![fst B B ≫ a, snd B B ≫ g] I).left =
          (psum A ![fst T B ≫ y ≫ a, (snd T B ≫ g) ^ n] I).left := fun I => by
        refine congrArg CommaMorphism.left ((psum_hom (preHom (lift (fst T B ≫ y) (snd T B ^ n))) _ I).trans ?_)
        congr 1
        funext i
        fin_cases i
        · show lift _ _ ≫ fst B B ≫ a = fst T B ≫ y ≫ a
          rw [lift_fst_assoc, Category.assoc]
        · show lift _ _ ≫ snd B B ≫ g = (snd T B ≫ g) ^ n
          rw [lift_snd_assoc, MonObj.pow_comp]
      have f : ∏ i : Fin 2, h ((fst T B).left ≫ ![(y ≫ a).left, (1 : T ⟶ A).left] i) ^ ![(-1 : ℤ), 1] i =
          (h (fst T B ≫ y ≫ a).left)⁻¹ * h (fst T B ≫ (1 : T ⟶ A)).left := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
      refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_mulT n (y ≫ a) (fst T B) (snd T B ≫ g) h) f).trans ?_
      simp only [e]
      rw [NormRos.prod_square, MonObj.comp_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen N.L _ _ _ _ (LB.pullGen N.L _ _ u₀ (lift (fst T B) (snd T B ≫ g)).left)
      (LB.pullGen N.L _ _ σ (fst T B).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun z e hz he p J hJ => ?_⟩
  have w : ∀ b : T ⟶ B, val u (lift (𝟙 T) b).left p J =
      val u₀ (lift (𝟙 T) (b ≫ g)).left p J * val σ (𝟙 T :).left p J := fun b => by
    rw [v _ _ p J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd_assoc]
  have w₀ := v₀ (z ≫ g) e (by rw [← MonObj.pow_comp, hz, MonObj.one_comp]) he T (𝟙 T) 1 p J hJ
  rw [Category.id_comp, _root_.mul_one] at w₀
  rw [w, w, w₀, MonObj.one_comp, mul_right_comm]
  rfl

end GlobalTheory.PairingOfLam

namespace GlobalTheory

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAppellHumbertUniformisationOfKeyDatumIso
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAppellHumbertUniformisationOfKeyDatumIso
noncomputable section

section Push
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa GlobalTheory.KeyEq GlobalTheory.KeyIsoNormal

namespace GlobalTheory.KeyTransport

theorem eq_comp_of_isLieComb {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] (ψ : A' ⟶ A)
    (hm : ∀ a b : epsR ℂ ⟶ A', (a * b) ≫ ψ = (a ≫ ψ) * (b ≫ ψ)) {n : ℕ} {c : Fin n → ℂ}
    {v' : Fin n → (epsR ℂ ⟶ A')} {v : Fin n → (epsR ℂ ⟶ A)} (hv : ∀ i, (v i).left = (v' i).left ≫ ψ.left)
    {w' : epsR ℂ ⟶ A'} {w : epsR ℂ ⟶ A} (hw' : IsLieComb c v' w') (hw : IsLieComb c v w) : w = w' ≫ ψ := by
  obtain ⟨a', ha', rfl⟩ := hw'
  obtain ⟨a, ha, rfl⟩ := hw
  let m : (epsR ℂ ⟶ A') →* (epsR ℂ ⟶ A) := MonoidHom.mk' (fun p => p ≫ ψ) hm
  have e : a = m ∘ a' := by
    funext i
    ext
    change _ = (a' i).left ≫ ψ.left
    rw [ha, ha', hv, Category.assoc]
  rw [e, ← List.map_ofFn, ← map_list_prod]
  rfl

theorem eq_comp_of_isLieComb_cast {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] (ψ : A' ⟶ A)
    (hm : ∀ a b : epsR ℂ ⟶ A', (a * b) ≫ ψ = (a ≫ ψ) * (b ≫ ψ)) {n n' : ℕ} (h : n = n') {c : Fin n' → ℂ}
    {v' : Fin n' → (epsR ℂ ⟶ A')} {v : Fin n → (epsR ℂ ⟶ A)}
    (hv : ∀ i, (v i).left = (v' (i.cast h)).left ≫ ψ.left)
    {w' : epsR ℂ ⟶ A'} {w : epsR ℂ ⟶ A} (hw' : IsLieComb c v' w') (hw : IsLieComb (fun i => c (i.cast h)) v w) :
    w = w' ≫ ψ := by
  subst h
  exact eq_comp_of_isLieComb ψ hm hv hw' hw

theorem exists_push_key {x x' : KeyIn ℂ} (H : KeyPB x' x (RingHom.id ℂ)) {g : ℕ} (u' : HolUnif x'.P.A x'.P.L g) :
    ∃ u : HolUnif x.P.A x.P.L g, u.Λ = u'.Λ ∧ (∀ Hm χ', u'.IsAH Hm χ' → ∃ χ, u.IsAH Hm χ) ∧
      (u'.IsRig x'.rig → u.IsRig x.rig) ∧ (∀ θ, u'.IsFn x'.th θ → u.IsFn x.th θ) ∧
      ∀ (h : x.P.g = x'.P.g) (c : Fin x'.P.g → ℂ) (w' : epsR ℂ ⟶ x'.P.A) (w : epsR ℂ ⟶ x.P.A) (W : Fin g → ℂ),
        IsLieComb c x'.v w' → IsLieComb (fun i => c (i.cast h)) x.v w → u'.IsDiff W w' → u.IsDiff W w := by
  obtain ⟨φ, he, w, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := H
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hFid : spMap F = 𝟙 _ := by
    rw [KeyCancel.dualNumber_ringHom_ext (F := F) (G := RingHom.id _) hF hFe]
    exact Spec.map_id _
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap (RingHom.id ℂ)) _
    (rigPull_le φ (spMap (RingHom.id ℂ)) he x.P.L) (fun _ => rfl)).1 hr
  rw [hid] at r he
  rw [Category.id_comp] at he
  have hc' := hc.congr hid rfl
  let ψ : x'.P.A ⟶ x.P.A := Over.homMk φ (hc'.1.w.trans (Category.comp_id _))
  obtain ⟨u, hex, hΛ, hfr⟩ := exists_push x.P.isLB x'.P.isLB ψ hc' w ((isGen_iff w).1 hw) u'
  replace hex : ∀ z, (u.ex z).left = (u'.ex z).left ≫ φ := hex
  replace hfr : ∀ j k z, φ ((u'.ex z).left pt) ∈ x.P.L.U j → (u'.ex z).left pt ∈ x'.P.L.U k →
    u.fr j z = wv w (u'.ex z).left j k * u'.fr k z := hfr
  refine ⟨u, hΛ, fun Hm χ' hA => ⟨fun l => χ' ⟨l.1, hΛ ▸ l.2⟩, hA.1, hA.2.1, fun l => hA.2.2.1 _, fun l j z hz => ?_⟩,
    fun h₄ j hj => ?_, fun θ h₅ j z hz => ?_, fun h c q' q W hq' hq h₆ U hU f => ?_⟩
  · rw [hex] at hz
    have hj : φ ((u'.ex z).left pt) ∈ x.P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB ((u'.ex z).left pt)
    have hl : u'.ex (z + l.1) = u'.ex z := by
      rw [u'.ex_add, (u'.ker l.1).2 (hΛ ▸ l.2), _root_.mul_one]
    have e := hA.2.2.2 ⟨l.1, hΛ ▸ l.2⟩ k z ((top_le_preimage_iff_mem _ _).2 hk)
    rw [hfr j k z hj hk, hfr j k (z + l.1) (hl ▸ hj) (hl ▸ hk), hl, e]
    ring
  · have h0 : (u'.ex 0).left = eSec x'.P.A := by
      rw [(u'.ker 0).2 u'.Λ.zero_mem]
      change (toUnit _ ≫ η[x'.P.A]).left = η[x'.P.A].left
      rw [toUnit_unit, Category.id_comp]
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB (eSec x'.P.A pt)
    have hj' : φ (eSec x'.P.A pt) ∈ x.P.L.U (j PUnit.unit) := by
      have := mem_pull.1 (hj (Set.mem_univ pt))
      rw [← he] at this
      exact this
    have hk' : (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) pt ∈ (x'.P.L.pull (eSec x'.P.A)).U (fun _ => k) := mem_pull.2 hk
    have e := congrArg Units.val (r _ (𝟙 (Sp ℂ)) pt j (fun _ => k) (fun _ => hj') (fun _ => hk))
    rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp, Units.val_mul] at e
    rw [hfr _ k 0 (h0 ▸ hj') (h0 ▸ hk), h0, h₄ (fun _ => k) ((top_le_preimage_iff_mem (𝟙 _) _).2 hk')]
    apply toStalk.injective
    rw [map_mul]
    exact (congrArg₂ (· * ·) (gw_eq_toStalk w _ hj' hk).symm (gm_eq_toStalk _ _ hk' _).symm).trans
      (e.symm.trans (gm_eq_toStalk _ _ (hj (Set.mem_univ pt)) _))
  · rw [hex] at hz ⊢
    have hj : φ ((u'.ex z).left pt) ∈ x.P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB ((u'.ex z).left pt)
    have e := (KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs _ (u'.ex z).left pt j k hj hk
    rw [gs_eq_toStalk _ _ hj, gs_eq_toStalk _ _ hk, gw_eq_toStalk w _ hj hk, ← map_mul] at e
    rw [toStalk.injective e, hfr j k z hj hk, h₅ k z ((top_le_preimage_iff_mem _ _).2 hk)]
    ring
  · have e₀ : q = q' ≫ ψ := eq_comp_of_isLieComb_cast ψ (fun a b => comp_mul_of_isGrpPullback ψ hc' a b) h
      (fun i => by
        change _ = _ ≫ φ
        rw [hv, hFid, Category.id_comp]
        rfl) hq' hq
    have e : q.left = q'.left ≫ φ := by
      rw [e₀]
      rfl
    have := h₆ (φ ⁻¹ᵁ U) (by rw [e] at hU; exact hU) ((φ.app U).hom f)
    simp only [valAt'_comp, ← hex] at this
    rw [← this]
    congr 2
    generalize q.left = p at e hU
    subst e
    rw [Scheme.Hom.comp_appLE]
    rfl

end GlobalTheory.KeyTransport
end Push

section Main
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyTransport

theorem uniformisation_transport : ∀ (x x' : KeyIn ℂ), KeyPB x' x (RingHom.id ℂ) → ∀ (hg : x'.P.g = x.P.g) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → ∃ (u' : HolUnif x'.P.A x'.P.L g) (χ' : u'.Λ → ℂ) (θ' : (Fin g → ℂ) → ℂ) (Fd' : Set (Fin g → ℂ)), u'.IsAH (Hm.map (RingHom.id ℂ)) χ' ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume ∧ (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm (Hm.map (RingHom.id ℂ)) z z).re)) / (volume Fd').toReal = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧ ∀ (cf : Fin x.P.g → ℂ) (w : epsR ℂ ⟶ x.P.A) (w' : epsR ℂ ⟶ x'.P.A) (W : Fin g → ℂ), IsLieComb cf x.v w → IsLieComb (fun i => (RingHom.id ℂ) (cf (i.cast hg))) x'.v w' → u.IsDiff W w → u'.IsDiff (fun i => (RingHom.id ℂ) (W i)) w' := by
  intro x x' H hg g u Hm χ θ Fd ⟨h₁, h₂, h₃, h₄⟩
  have H' : KeyPB x x' (RingHom.id ℂ) :=
    KeyCancel.keyPB_cancel ℂ ℂ ℂ x x' x (RingHom.id ℂ) (RingHom.id ℂ) H (keyPB_id ℂ x)
  have hH : Hm.map (RingHom.id ℂ) = Hm := rfl
  obtain ⟨u', hΛ, hA, hR, hF, hD⟩ := exists_push_key H' u
  obtain ⟨χ', hχ⟩ := hA Hm χ h₁
  exact ⟨u', χ', θ, Fd, hχ, hR h₂, hF θ h₃, hΛ ▸ h₄, rfl, fun cf w w' W hw hw' hW => hD hg cf w w' W hw hw' hW⟩

end GlobalTheory.KeyTransport
end Main
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAppellHumbertUniformisationOfKeyDatumIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appellHumbert_uniformisation_of_keyDatumIso : ∀ (x x' : KeyIn ℂ), KeyPB x' x (RingHom.id ℂ) → ∀ (hg : x'.P.g = x.P.g) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → ∃ (u' : HolUnif x'.P.A x'.P.L g) (χ' : u'.Λ → ℂ) (θ' : (Fin g → ℂ) → ℂ) (Fd' : Set (Fin g → ℂ)), u'.IsAH (Hm.map (RingHom.id ℂ)) χ' ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume ∧ (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm (Hm.map (RingHom.id ℂ)) z z).re)) / (volume Fd').toReal = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧ ∀ (cf : Fin x.P.g → ℂ) (w : epsR ℂ ⟶ x.P.A) (w' : epsR ℂ ⟶ x'.P.A) (W : Fin g → ℂ), IsLieComb cf x.v w → IsLieComb (fun i => (RingHom.id ℂ) (cf (i.cast hg))) x'.v w' → u.IsDiff W w → u'.IsDiff (fun i => (RingHom.id ℂ) (W i)) w' := by
  first | exact @GlobalTheory.KeyTransport.uniformisation_transport | exact GlobalTheory.KeyTransport.uniformisation_transport | (intros; apply GlobalTheory.KeyTransport.uniformisation_transport <;> assumption)
end
end
