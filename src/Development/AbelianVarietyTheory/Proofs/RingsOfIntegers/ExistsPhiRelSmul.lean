module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ProdTorsion


open Geo.Tor in
theorem val_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)


open Geo.Tor in
theorem exists_phiRel_smul (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (ζ : F) (hζ : ζ ≠ 0) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)), w'.IsGen ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → PhiRel D F k p w' s (ζ • t) := by
  let u : Γ((TF (R := R) F).left, ⊤)ˣ :=
    ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit
  have hw' := scaleGen_isGen u w hw
  refine ⟨scaleGen u w, hw', fun s t h => (phiRel_iff hG p _ hw' s _).2 ?_⟩
  intro a' β hβ T ρ z' J hJ
  have h1 := (phiRel_iff hG p w hw s t).1 h a' β hβ T ρ z' J hJ
  have hu : gs (ρ.left ≫ (fst (TF (R := R) F) D.P.A).left) z' ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) =
      (gm (ρ ≫ fst (TF (R := R) F) D.P.A).left z' ⊤ u).val :=
    gs_unit _ z' ⊤ trivial u
  rw [sval_smul ζ t β ρ.left z' hJ, h1, val_mul hJ, val_mul hJ, val_scale hJ, hu]
  simp only [Units.val_mul]
  ring

theorem pow_eq_one_of_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    {T : Over S} (x : T ⟶ G') (k : ℕ) (h : ∀ i, (x ≫ p.pr i) ^ k = 1) : x ^ k = 1 :=
  Fan.IsLimit.hom_ext p.lim _ _ fun i => by
    haveI := p.hom i
    show (x ^ k) ≫ p.pr i = 1 ≫ p.pr i
    rw [MonObj.pow_comp, MonObj.one_comp, h]

theorem equiv_comb {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (f : M ≃ₗ[B] M) {I : Type} [Fintype I]
    (a : I → B) (v : I → M) : f (∑ l, a l • v l) = ∑ l, a l • f (v l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]

theorem act_comb (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (k : ℤ) (T : Over S) (θ : ThetaGrp P.A P.L k T)
    {I : Type} [Fintype I] (a : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (t u : I → LB.Sec (LPow P.A P.L k T))
    (t₀ t₁ : LB.Sec (LPow P.A P.L k T)) (h₀ : ∀ jj, t₀.f jj = ∑ l, liftFun P.A _ (a l) * (t l).f jj)
    (hu : ∀ l t', IsActOf P.A P.L k θ (t l) t' → ∀ jj, t'.f jj = liftFun P.A _ c * (u l).f jj)
    (ha : IsActOf P.A P.L k θ t₀ t₁) (jj) : t₁.f jj = ∑ l, liftFun P.A _ (a l * c) * (u l).f jj := by
  obtain ⟨ρ, hρ, -⟩ := thetaGrp_acts_linearly hG _ P k T
  have h0 : SecM.ofSec P.A t₀ = ∑ l, a l • SecM.ofSec P.A (t l) :=
    Subtype.ext (funext fun jj => (h₀ jj).trans
      (BoxSpan.comb_apply P.A P.L k _ _ (fun l => SecM.ofSec P.A (t l)) jj).symm)
  have h1 := (equiv_comb (ρ θ) _ _).symm.trans ((congrArg (ρ θ) h0).symm.trans ((hρ _ _ _).1 ha))
  refine ((congrFun (congrArg Subtype.val h1) jj).symm.trans (BoxSpan.comb_apply P.A P.L k _ _ _ jj)).trans
    (Finset.sum_congr rfl fun l _ => ?_)
  have e := hu l (SecM.toSec P.A (ρ θ (SecM.ofSec P.A (t l)))) ((hρ _ _ _).2 rfl) jj
  refine (congrArg (liftFun P.A _ (a l) * ·) e).trans ((_root_.mul_assoc _ _ _).symm.trans
    (congrArg (· * (u l).f jj) ?_))
  exact (map_mul (liftHom P.A _) _ _).symm

theorem qkToAk_box : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U), Geo.Tor.ExpBijF U.toUnifPre → Geo.Tor.ExpBijF U'.toUnifPre → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (p' : QkPt D'.toPre F k) (p : Fin j → QkPt D.toPre F k), IsBoxQk pD F k p' p → ∀ (x' : TFK (R := R) F ⟶ A'.A) (x : Fin j → (TFK (R := R) F ⟶ A.A)), (∀ i, x' ≫ pA.pr i = x i) → (∀ i, QkToAkU U.toUnifPre F k (p i) (x i)) → QkToAkU U'.toUnifPre F k p' x' := by
  intro hL R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P hB hB' F _ _ k hk p' p hp x' x hx h w' hw'
  have hG := hL.globalFns
  obtain ⟨w, hw⟩ := U.ext
  have hk1 : x' ^ k = 1 := pow_eq_one_of_pr pA.toIsPowGrp x' k fun i => by
    rw [hx i]; exact (h i w hw).1
  refine ⟨hk1, fun θ' hθ' => ?_⟩
  obtain ⟨θ, c, hc, hθ, hact⟩ := BoxTheta.box_theta_act hL R j A A' pA F k hk θ' (hθ' ▸ hk1)
  choose v hv hΦ using fun i => (h i w hw).2 (θ i) ((hθ i).trans (hθ' ▸ hx i))
  obtain ⟨V, hV, hVΦ⟩ := BoxPhi.phiRel_box hG R j D.toPre D'.toPre pD F k p' p hp v hv
  obtain ⟨Φ, hΦl⟩ := phiFun_of_globalFns hG R I D' F k hk p' V hV
  obtain ⟨V', hV', hV'Φ⟩ := exists_phiRel_smul hG p' V hV c hc
  obtain ⟨c₀, -, hexp⟩ := BoxExpansion.main hG R I j D D' A A' G G' pD pA pG U' U P w hw w' hw' F k
  obtain ⟨ρ, hρ, -⟩ := thetaGrp_acts_linearly hG _ A k (TFK (R := R) F)
  refine ⟨V', hV', fun t₀ t₁ s₀ s₁ e₀ e₁ ha => ?_⟩
  obtain ⟨n, a, t, t', hbox, hsum⟩ := boxProduct_span hL R j A A' pA F k hk t₀
  let u : Fin n → Fin j → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) :=
    fun l i => SecM.toSec A.A (ρ (θ i) (SecM.ofSec A.A (t l i)))
  have hu : ∀ l i, IsActOf A.A A.L (k : ℤ) (θ i) (t l i) (u l i) := fun l i => (hρ _ _ _).2 rfl
  choose u' hu' using fun l => exists_boxSec_pow_ext R j A A' pA F k (u l)
  choose s hs using fun l i => ((hB F k hk w hw).1 (t l i)).exists
  choose r hr using fun l i => ((hB F k hk w hw).1 (u l i)).exists
  choose S hS using fun l => BoxFamily.exists_isBoxFam hG R j D.toPre D'.toPre pD F k (s l)
  choose S₁ hS₁ using fun l => BoxFamily.exists_isBoxFam hG R j D.toPre D'.toPre pD F k (r l)
  have hSS : ∀ l, S₁ l = Φ (S l) := fun l => (hΦl _ _).1
    (hVΦ (s l) (r l) _ _ (fun i => hΦ i _ _ _ _ (hs l i) (hr l i) (hu l i)) (hS l) (hS₁ l))
  have E₀ := ExpansionLinear.expandsF_sum R I D' A' G' U'.toUnifPre F k w' hw' n a t' (fun l => c₀ • S l) t₀
    (fun l => hexp (t l) (s l) (t' l) (S l) (hs l) (hbox l) (hS l)) hsum
  have hsum₁ := act_comb hG A' k (TFK (R := R) F) θ' (fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a l))
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) t' u' t₀ t₁ hsum
    (fun l t'' h'' => hact (t l) (u l) (t' l) (u' l) t'' (hbox l) (hu' l) (hu l) h'') ha
  have E₁ := ExpansionLinear.expandsF_sum R I D' A' G' U'.toUnifPre F k w' hw' n (fun l => a l * c) u'
    (fun l => c₀ • S₁ l) t₁ (fun l => hexp (u l) (r l) (u' l) (S₁ l) (hr l) (hu' l) (hS₁ l))
    (fun jj => (hsum₁ jj).trans (Finset.sum_congr rfl fun l _ => by rw [map_mul]; rfl))
  have q₀ := ((hB' F k hk w' hw').1 t₀).unique e₀ E₀
  have q₁ := ((hB' F k hk w' hw').1 t₁).unique e₁ E₁
  have q : s₁ = c • Φ s₀ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [q₁, q₀, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hSS, map_smul, map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [q]
  exact hV'Φ _ _ ((hΦl _ _).2 rfl)

end GlobalTheory.ProdTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfPullAl
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullIntegral

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ₁ : K → (Y' ⟶ X)}
    {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)} (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have e := congrArg (gs r z _) (H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e))
  exact ((gs_res r z _ hm _).trans (gs_pull r h z
    (LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k))) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm.2 k) _)).symm.trans
    (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))))

theorem sec_ext_of_inj {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y' ⟶ Y) (hp : ∀ U, Function.Injective (p.app U).hom) {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 _ ≫ p) y J = sval s' (𝟙 _ ≫ p) y J) (j : K → L.ι) : s.f j = s'.f j := by
  refine hp _ (fn_ext fun y hy => ?_)
  choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
  have hy' : (𝟙 Y' ≫ p) y ∈ LB.wchart L φ j := hy
  refine (gs_pull (𝟙 _) p y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) p y _ hy _).symm)
  exact (sec_trans s _ y hy' (Good.mem hI φ _)).trans ((congrArg _ (h y I hI)).trans
    (sec_trans s' _ y hy' (Good.mem hI φ _)).symm)

variable {V : Type} [CommRing V] [IsDomain V]

theorem prB_app_injective (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (U : D.P.A.left.Opens) :
    Function.Injective ((DegPre.prB D F).left.app U).hom := by
  have := D.P.isAb.smooth
  have := GC.isDominant_jFR (V := V) F
  have h₁ := IsSchemeTheoreticallyDominant.of_isDominant (DegPre.jFR (R := V) F)
  have hf : Flat D.P.A.hom := inferInstance
  have hq : QuasiCompact (DegPre.jFR (R := V) F) := by
    generalize DegPre.jFR (R := V) F = q
    exact quasiCompact_of_compactSpace q
  have h₂ := IsSchemeTheoreticallyDominant.pullbackSnd (DegPre.jFR (R := V) F) D.P.A.hom
  have h₃ : QuasiCompact (pullback.snd (DegPre.jFR (R := V) F) D.P.A.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback _ _) hq
  exact (pullback.snd (DegPre.jFR (R := V) F) D.P.A.hom).app_injective U

variable [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)} {F : Type} [Field F]
  [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]


set_option maxHeartbeats 800000 in
theorem pull_val_eq (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N k : ℕ) (χ : D.toPre.X)
    (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left]
      ![((1 * (N + 1) : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (hX : X.IsGen)
    (nX : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (1 * (N + 1 - 1))))
    (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hu₁ : u₁.IsGen)
    (n₁ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u₁ (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k (N + 1)))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N + 1 - 1))) (jFK (R := V) F)))
    {z : (DegPre.BF D.toPre F).left} {J} (hJ : Good D.toPre.P.L z J) :
    val u (𝟙 _) z J = val X (DegPre.prB D.toPre F).left z J ^ k *
      val (LB.pullGen D.toPre.P.L _ _ u₁ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left)
        (DegPre.prB D.toPre F).left z J := by
  obtain ⟨s, hs, vs⟩ := exists_gen D.toPre.P.isLB (K' := Fin 3)
    (φ' := ![(𝟙 D.toPre.P.A : D.toPre.P.A ⟶ D.toPre.P.A).left, (oa.onB.act a).left,
      (1 : D.toPre.P.A ⟶ D.toPre.P.A).left]) (ε' := ![(N + 1 : ℕ), -1, -(N : ℤ)]) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := PUnit) (U := U) _ (Fin.prod_univ_two _)
        (prod_neg _ _ (ppow _ _ N (c := h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left)
          ((Fintype.prod_unique _).trans (zpow_one _))))).trans ?_
      rw [Fin.prod_univ_three]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, Sum.elim_inl, Matrix.cons_val, Over.id_left,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ X (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _
      (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig D.toPre.P.A.hom) N)))
    (mulGen_isGen _ _ _ _ _ _ _ hX (invGen_isGen _ _ _ _
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _)))
  have vs' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → val s r z J =
      val X r z J * (val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig
        (r ≫ D.toPre.P.A.hom) z J ^ N)⁻¹ :=
    fun Z r z J hJ => by rw [vs Z r z J hJ, val_mul hJ, val_inv, val_pow, val_pull hJ]
  have s₁ : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.toPre.P.L z J →
      val s (1 : T ⟶ D.toPre.P.A).left z J = 1 := fun T z J hJ => by
    have e := val_corr hJ nX T.hom
    rw [val_pull hJ] at e
    have e' : val X (1 : T ⟶ D.toPre.P.A).left z J = val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A)
        (ε := fun _ => 1) D.toPre.rig T.hom z J ^ N := e.trans ((val_pow _ _ _ _ _).trans (by simp))
    rw [vs' _ _ z J hJ, Over.w (1 : T ⟶ D.toPre.P.A), e', mul_inv_cancel]
  have H := pull_val hG oa a N k χ u₁ hu₁ n₁ s hs s₁ u hu hc (𝟙 _) hJ
  have e₁ : val D.toPre.rigK ((fst (TF (R := V) F) D.toPre.P.A).left ≫ jFK (R := V) F) z J =
      val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig
        ((DegPre.prB D.toPre F).left ≫ D.toPre.P.A.hom) z J :=
    (val_pull hJ _ _ _).trans (congrArg (fun q => val _ q z J) ((Category.assoc _ _ _).trans
      ((Over.w (fst (TF (R := V) F) D.toPre.P.A)).trans (Over.w (DegPre.prB D.toPre F)).symm)))
  have e₂ := val_ros u₁ (DegPre.prB D.toPre F) hJ (cP D.toPre _ χ) (𝟙 D.toPre.P.A)
  rw [comp_cP, Category.comp_id] at e₂
  rw [Category.id_comp, Category.id_comp, e₁, vs' _ _ z J hJ, ← e₂] at H
  refine H.trans ?_
  rw [mul_pow, inv_pow, ← pow_mul, mul_comm N k, mul_right_comm, inv_mul_cancel_right]
  rfl


set_option maxHeartbeats 800000 in
theorem integral_of_pullAl (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N : ℕ) (hN : 0 < N)
    (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left]
      ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (hX : X.IsGen)
    (nX : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (1 * (N - 1))))
    (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hu₁ : u₁.IsGen)
    (n₁ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u₁ (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (k : ℕ) (s : Fam D.toPre F k) (s'' : Fam D.toPre F (k * N)) (hP : PullAl D F oa a k N s s'') (c : V)
    (f'' : ∀ α : D.toPre.X, D.toPre.SecB (k * N) α) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hf : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α)
      (DegPre.famε k) (f α) (DegPre.prB D.toPre F).left (scal (DegPre.BF D.toPre F).hom c))
    (hf'' : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε (k * N)) (s''.s α) (D.toPre.famφB α)
      (DegPre.famε (k * N)) (f'' α) (DegPre.prB D.toPre F).left (scal (DegPre.BF D.toPre F).hom c)) :
    (∀ (χ : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (f'' (star a • χ)) r z J = sval (f χ) (r ≫ (oa.onB.act a).left) z J * (val X r z J ^ k *
        val (LB.pullGen D.toPre.P.L _ _ u₁ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left) r z J).val) ∧
    ∀ β : D.toPre.X, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' β).f j = 0 := by
  obtain ⟨N, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have inj := prB_app_injective D.toPre F
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hrel⟩ := hP.1 χ
    let g := oa.onB.act a
    let g' := oa.onB.act (star a)
    let x : D.toPre.P.A ⟶ D.toPre.P.A := 𝟙 _
    have cf : cP D.toPre D.toPre.P.A (star a • χ) = cP D.toPre D.toPre.P.A χ ≫ g' := by
      rw [cP, oa.c_lin, ← Category.assoc]; rfl
    have he := mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hX k)
      (pullGen_isGen _ _ _ _ hu₁ (lift (cP D.toPre D.toPre.P.A χ) x).left)
    obtain ⟨σ, hσ⟩ := exists_sec D.toPre.P.isLB (φ' := D.toPre.famφB (star a • χ)) (ε' := DegPre.famε (k * (N + 1)))
      (fun U _ h => by
        refine (prod_sum₂ (K := Fin 4) (K' := Fin 2 ⊕ Fin 6) (U := U) _ (Fin.prod_univ_four _)
          (prod_sum₂ (K := Fin 2) (K' := Fin 6) (U := U) _ (ppow _ _ k (Fin.prod_univ_two _))
            (prod_ros g' g (cP D.toPre _ χ) x h))).trans ?_
        have a₁ : D.toPre.famφB (star a • χ) 1 = ((cP D.toPre D.toPre.P.A χ ≫ g') * x).left := congrArg (fun q => q.left)
          ((mul_comm x (cP D.toPre D.toPre.P.A (star a • χ))).trans (by rw [cf]))
        have a₂ : D.toPre.famφB (star a • χ) 2 = (cP D.toPre D.toPre.P.A χ ≫ g').left := congrArg (fun q => q.left) cf
        have a₃ : g.left ≫ D.toPre.famφB χ 1 = (cP D.toPre D.toPre.P.A χ * (x ≫ g)).left := congrArg (fun q => q.left)
          ((MonObj.comp_mul g x (cP D.toPre D.toPre.P.A χ)).trans
            (by rw [comp_cP, mul_comm, Category.comp_id, Category.id_comp]))
        have a₄ : g.left ≫ D.toPre.famφB χ 2 = (cP D.toPre D.toPre.P.A χ).left :=
          congrArg (fun q => q.left) (comp_cP D.toPre g χ)
        have a₅ : g.left ≫ D.toPre.famφB χ 3 = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left :=
          congrArg (fun q : D.toPre.P.A ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) g)
        have a₆ : g.left ≫ D.toPre.famφB χ 0 = g.left := Category.comp_id _
        have a₇ : D.toPre.famφB (star a • χ) 0 = x.left := rfl
        have a₈ : D.toPre.famφB (star a • χ) 3 = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := rfl
        have a₉ : x ≫ g = g := Category.id_comp _
        have a₀ : 𝟙 D.toPre.P.A.left = x.left := rfl
        rw [Fin.prod_univ_four]
        simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₀]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, DegPre.famε, Matrix.cons_val]
        push_cast
        module)
      (pullMulSec (f χ) g.left _ he)
    have hσ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
        sval σ r z J = sval (f χ) (r ≫ (oa.onB.act a).left) z J * (val X r z J ^ k *
          val (LB.pullGen D.toPre.P.L _ _ u₁ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left)
            r z J).val := fun Z r z J hJ => by
      rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, val_mul hJ, val_pow]; rfl
    have a₁ : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
      congrArg (fun q => q.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
    have E := sec_ext_of_inj D.toPre.P.isLB _ inj (s := f'' (star a • χ)) (s' := σ) fun y J hJ => by
      have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ
      have e₂ := sval_of_secScal (hf χ) (aF D F oa a).left y hJ
      have e₃ : gs (aF D F oa a).left y ⊤ (scal (DegPre.BF D.toPre F).hom c) =
          gs (𝟙 _) y ⊤ (scal (DegPre.BF D.toPre F).hom c) :=
        (gs_pull _ (DegPre.BF D.toPre F).hom y ⊤ trivial _).trans (Eq.trans (by rw [Over.w, Category.id_comp])
          (gs_pull _ (DegPre.BF D.toPre F).hom y ⊤ trivial _).symm)
      rw [a₁, e₃] at e₂
      rw [Category.id_comp, pull_val_eq hG oa a N k χ X hX nX u₁ hu₁ n₁ u hu hc hJ] at e₁
      rw [sval_of_secScal (hf'' _) (𝟙 _) y hJ, hσ' _ _ y J hJ, Category.id_comp, e₁, e₂, _root_.mul_assoc]
    intro Z r z J hJ
    exact (congrArg (gs r z _) (E _)).trans (hσ' Z r z J hJ)
  · refine inj _ ((fn_ext fun y hy => ?_).trans (map_zero _).symm)
    choose I hI using fun χ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
    have hy' : (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y ∈ LB.wchart D.toPre.P.L (D.toPre.famφB β) j := hy
    have e : sval (s''.s β) (𝟙 _) y I = 0 :=
      (congrArg (gs _ y _) (hP.2 β hβ _)).trans (gs_zero _ y _ (Good.mem hI _ _))
    have e' := sval_of_secScal (hf'' β) (𝟙 _) y hI
    rw [e, mul_zero] at e'
    refine (gs_pull (𝟙 _) _ y _ hy _).trans ((sec_trans (f'' β) _ y hy' (Good.mem hI _ _)).trans ?_)
    exact (congrArg _ e').trans ((mul_zero _).trans (gs_zero _ y _ hy).symm)

end GlobalTheory.PullIntegral

namespace GlobalTheory.PullIntegral

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), X.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ X (eSec P.D.toPre.P.A)) (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig (1 * (N - 1))) → ∀ uR : LB.Gen (LB.LinComb P.D.toPre.P.L (rosatiφ P.D.toPre.P.A (P.oD.onB.act (star a)) (P.oD.onB.act a)) rosatiε), uR.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ uR (zero2 P.D.toPre.P.A)) (LB.oneGen P.D.toPre.P.L) → ∀ (k : ℕ) (F : Fam P.D.toPre (FractionRing V) k) (F'' : Fam P.D.toPre (FractionRing V) (k * N)), PullAl P.D (FractionRing V) P.oD a k N F F'' → ∀ (c : V) (f'' : ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α) (f : ∀ α : P.D.toPre.X, P.D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε (k)) (F.s α) (P.D.toPre.famφB α) (DegPre.famε (k)) (f α) (DegPre.prB P.D.toPre (FractionRing V)).left (scal (DegPre.BF P.D.toPre (FractionRing V)).hom c)) → (∀ α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε (k * N)) (F''.s α) (P.D.toPre.famφB α) (DegPre.famε (k * N)) (f'' α) (DegPre.prB P.D.toPre (FractionRing V)).left (scal (DegPre.BF P.D.toPre (FractionRing V)).hom c)) → ((∀ (χ : P.D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ P.D.toPre.P.A.left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → Geo.Tor.sval (f'' (star a • χ)) r z J = Geo.Tor.sval (f χ) (r ≫ (P.oD.onB.act a).left) z J * (Geo.Tor.val X r z J ^ k * Geo.Tor.val (LB.pullGen P.D.toPre.P.L _ _ uR (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left) r z J).val) ∧ ∀ β : P.D.toPre.X, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' β).f j = 0) := by
  intro hG V _ _ _ E _ _ _ H t P a N _ hN
  letI := H.starRing
  intro X hX nX uR huR nR k F F'' hP c f'' f hf hf''
  exact integral_of_pullAl hG P.oD a N hN X hX nX uR huR nR k F F'' hP c f'' f hf hf''

end GlobalTheory.PullIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBimultPow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TauBimultBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.TauBalBox

theorem val_lhs {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {y : (TK R).left} {J} (hJ : Good D.P.L y J)
    (a a' b : D.X) :
    val (LB.mulGen D.P.L _ _ _ _ (D.tau (a + a') b)
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))) (𝟙 _) y J =
      val (D.tau (a + a') b) (𝟙 _) y J * cubV D.cub y J (cP D (TK R) a) (cP D (TK R) a') (cP D (TK R) b) := by
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_)
  refine (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp]

theorem tauBimult_pow : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.TauBimult → D'.TauBimult := by
  intro hG R _ _ j D D' pD hB a a' b
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have key : cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b) *
      (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b).left *
        (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) a').left)⁻¹ *
        (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) b).left)⁻¹ *
        (om pD.w y J J' (cP D' (TK R) a' * cP D' (TK R) b).left)⁻¹ *
        om pD.w y J J' (cP D' (TK R) a).left * om pD.w y J J' (cP D' (TK R) a').left *
        om pD.w y J J' (cP D' (TK R) b).left *
        (om pD.w y J J' (1 : TK R ⟶ D'.P.A).left)⁻¹) = _ :=
    GlobalTheory.CubBox.cubV_box hG R j D D' pD (TK R) y J J' hJ hJ' _ _ _
  have o : (1 : TK R ⟶ D'.P.A).left = 𝟙 _ ≫ (toUnit (TK R)).left ≫ eSec D'.P.A := (Category.id_comp _).symm
  rw [o] at key
  have t₁ := tau_box pD hJ hJ' (a + a') b
  have t₂ := tau_box pD hJ hJ' a b
  have t₃ := tau_box pD hJ hJ' a' b
  rw [cPoint_add] at t₁
  have e : ∀ i, val (D.tau (pD.xe (a + a') i) (pD.xe b i)) (𝟙 _) y J *
      cubV D.cub y J (cP D' (TK R) a ≫ pD.pw.pr i) (cP D' (TK R) a' ≫ pD.pw.pr i) (cP D' (TK R) b ≫ pD.pw.pr i) =
      val (D.tau (pD.xe a i) (pD.xe b i)) (𝟙 _) y J * val (D.tau (pD.xe a' i) (pD.xe b i)) (𝟙 _) y J := fun i => by
    have := (val_lhs D hJ _ _ _).symm.trans
      ((val_corr hJ (hB (pD.xe a i) (pD.xe a' i) (pD.xe b i)) (𝟙 _)).trans (val_mul hJ _ _ _))
    rw [show pD.xe (a + a') i = pD.xe a i + pD.xe a' i by rw [map_add (f := _)]; rfl, cP, cP, cP, Category.assoc,
      Category.assoc, Category.assoc, pD.c_pr, pD.c_pr, pD.c_pr]
    exact this
  have E := (Finset.prod_mul_distrib).symm.trans ((Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => e i).trans
    Finset.prod_mul_distrib)
  rw [← t₁, ← t₂, ← t₃, ← key] at E
  refine (val_lhs D' hJ' a a' b).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  have E' := congrArg Additive.ofMul E
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at E' ⊢
  rw [← sub_eq_zero] at E' ⊢
  refine Eq.trans ?_ E'
  abel

end GlobalTheory.TauBimultBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowDegDiagonalAction
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowOAct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.TauBalBox

private theorem hom_ext_of_isPowGrp_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) {T : Over S} {a b : T ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b := by
  apply p.lim.hom_ext
  rintro ⟨i⟩
  first
  | exact h i
  | simpa using h i

theorem exists_pow_oAct : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ oa : D.OAct O, ∃ oa' : D'.OAct O, ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a := by
  intro hG R _ _ j D D' pD O _ _ _ _ hxe oa
  obtain ⟨⟨oB, hros⟩, hc, htau⟩ := oa
  letI := D.P.isAb.comm
  letI := D'.P.isAb.comm
  obtain ⟨r', hr'⟩ := (GlobalTheory.exists_powAct _ D'.P.A D.P.A j pD.pw).1 O oB
  have hros' : ∀ a : O, RosatiAdj D'.P.A D'.P.L (r'.act a) (r'.act (star a)) := fun a =>
    GlobalTheory.rosatiAdj_pow _ D'.P.A D.P.A j pD.pw D.P.L D'.P.L D.P.isLB D'.P.isLB ⟨pD.w, pD.w_gen⟩
      (oB.act a) (oB.act (star a)) (r'.act a) (r'.act (star a)) (hr' a) (hr' (star a)) (hros a)
  have hc' : ∀ (a : O) (y : D'.X), D'.c (a • y) = D'.c y ≫ r'.act a := by
    intro a y
    apply hom_ext_of_isPowGrp_pr pD.pw
    intro i
    rw [pD.c_pr, Category.assoc, hr' a i, ← Category.assoc, pD.c_pr, hxe, Pi.smul_apply, hc]
  have htau' : ∀ a : O, D'.TauBal (r'.act a) (r'.act (star a)) (fun y => a • y) fun y => star a • y := by
    intro a
    haveI := oB.hom a
    haveI := oB.hom (star a)
    haveI := r'.hom a
    haveI := r'.hom (star a)
    exact tauBal_pow hG R j D D' pD (oB.act a) (oB.act (star a)) (r'.act a) (r'.act (star a))
      inferInstance inferInstance inferInstance inferInstance (hr' a) (hr' (star a)) (hros a)
      (fun y => a • y) (fun y => star a • y) (fun y => a • y) (fun y => star a • y)
      (fun x i => by simp only [hxe, Pi.smul_apply]) (fun x i => by simp only [hxe, Pi.smul_apply])
      (hc a) (hc (star a)) (htau a)
  exact ⟨⟨⟨r', hros'⟩, hc', htau'⟩, hr'⟩

end GlobalTheory.TauBalBox
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem powDeg_diagonal_action : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ oa : D.OAct O, ∃ oa' : D'.OAct O, ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a :=
  GlobalTheory.TauBalBox.exists_pow_oAct

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GermDiv

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ThickeningDetermines

theorem dvd_of_app_eq_zero {R : Type} [CommRing R] (r : R) {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hf : ((pullback.fst p (spMap (Ideal.Quotient.mk (Ideal.span {r})))).app U).hom f = 0) :
    constFn p U r ∣ f := by
  have h := ProperFunctions.mem_map_ker_of_app_eq_zero
    (IsPullback.of_hasPullback p (spMap (Ideal.Quotient.mk (Ideal.span {r})))) hU f hf
  have hk : RingHom.ker (spMap (Ideal.Quotient.mk (Ideal.span {r}))).appTop.hom ≤
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r} := by
    intro x hx
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 x
    have e := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r}))))
    have h0 : Ideal.Quotient.mk (Ideal.span {r}) a = 0 :=
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {r}))).inv).1
        ((e.trans hx).trans (map_zero _).symm)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    exact Ideal.mem_span_singleton.2 (map_dvd (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h0)
  have h' := Ideal.map_mono hk h
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h'
  exact h'

theorem cst_zero {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  rw [cst, gs_eq q z ⊤ trivial, map_zero, map_zero, map_zero]

theorem app_eq_zero_of_dvd {R : Type} [CommRing R] (r : R) {X Y Z : Scheme.{0}} (p : X ⟶ Sp R)
    (a : Y ⟶ X) (m : Z ⟶ Y) (t : Z ⟶ Sp (R ⧸ Ideal.span {r}))
    (ht : m ≫ a ≫ p = t ≫ spMap (Ideal.Quotient.mk (Ideal.span {r})))
    (U : X.Opens) (f : Γ(X, U)) (h : ∀ y : Y, a y ∈ U → cst (a ≫ p) y r ∣ gs a y U f) :
    ((m ≫ a).app U).hom f = 0 := by
  refine fn_ext fun z hz => ?_
  have hz' : a (m z) ∈ U := hz
  have e1 : gs (𝟙 Z) z ((m ≫ a) ⁻¹ᵁ U) (((m ≫ a).app U).hom f) = gs (m ≫ a) z U f :=
    (gs_pull (𝟙 Z) (m ≫ a) z U hz f).trans (by rw [Category.id_comp])
  have e2 : gs (m ≫ a) z U f = (m.stalkMap z).hom (gs a (m z) U f) := by
    rw [← gs_pull m a z U hz', gs_stalkMap m z _ hz', gs_pull (𝟙 Y) a (m z) U hz', Category.id_comp]
  have e3 : (m.stalkMap z).hom (cst (a ≫ p) (m z) r) = 0 := by
    rw [H1.cst_stalkMap, ht, cst_comp,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r), cst_zero]
  obtain ⟨c, hc⟩ := h _ hz'
  rw [e1, e2, hc, map_mul, e3, zero_mul, gs_eq (𝟙 Z) z _ hz, map_zero, map_zero]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom] (N : LB H.left), N.IsLB → ∀ (s : LB.Sec N) (r : R), r ≠ 0 → (∀ (n : ℕ) (x : (thickObj R I n H).left) (j : N.ι), (fstG I n H).left x ∈ N.U j → Geo.Tor.cst ((fstG I n H).left ≫ H.hom) x r ∣ Geo.Tor.gs (fstG I n H).left x (N.U j) (s.f j)) → ∃ s' : LB.Sec N, SecIsMul H.hom r s s' := by
  intro R _ _ _ I hI H _ _ _ N hN s r hr h
  let q := Ideal.Quotient.mk (Ideal.span {r})
  let H₀ : Over (Spec (CommRingCat.of (R ⧸ Ideal.span {r}))) := (Over.pullback (spMap q)).obj H
  let π : H₀.left ⟶ H.left := pullback.fst H.hom (spMap q)
  let I₀ := I.map q
  have hI₀ : I₀ ≤ Ideal.jacobson ⊥ := by
    refine Ideal.map_le_iff_le_comap.2 (hI.trans ?_)
    rw [Ideal.comap_jacobson_of_surjective Ideal.Quotient.mk_surjective]
    exact Ideal.jacobson_mono bot_le
  have : Smooth H₀.hom := inferInstanceAs (Smooth (pullback.snd H.hom (spMap q)))
  have : GeometricallyConnected H₀.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom (spMap q)))
  have := grpObj_geometricallyIntegral_of_smooth _ H₀
  have : IsClosedImmersion (spMap q) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst H.hom (spMap q)))
  let κ := (secIdeal hN s).subschemeι
  have hiso := isIso_of_isClosedImmersion_of_thickenings _ I₀ hI₀ H₀ η[H₀] (fun p ↦ inferInstance)
    _ (pullback.fst π κ) fun n ↦ by
      have : IsClosedImmersion (thick _ I₀ n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG I₀ n H₀).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H₀.hom (thick _ I₀ n)))
      let m : (thickObj _ I₀ n H₀).left ⟶ (thickObj R I n H).left :=
        pullback.lift ((fstG I₀ n H₀).left ≫ π)
          (pullback.snd H₀.hom (thick _ I₀ n) ≫ spMap (Ideal.quotientMap (I₀ ^ (n + 1)) q
            (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)))
          (by
            have e1 : π ≫ H.hom = H₀.hom ≫ spMap q := pullback.condition
            have e2 : (fstG I₀ n H₀).left ≫ H₀.hom =
              pullback.snd H₀.hom (thick _ I₀ n) ≫ thick _ I₀ n := pullback.condition
            rw [Category.assoc, e1, ← Category.assoc, e2, Category.assoc, Category.assoc,
              ← Spec.map_comp, ← Spec.map_comp]
            rfl)
      have hm : m ≫ (fstG I n H).left = (fstG I₀ n H₀).left ≫ π := pullback.lift_fst _ _ _
      have h0 : ∀ j, (((fstG I₀ n H₀).left ≫ π).app _).hom (s.f j) = 0 := fun j => by
        rw [← hm]
        refine app_eq_zero_of_dvd r H.hom _ m ((fstG I₀ n H₀).left ≫ H₀.hom) ?_ _ _
          fun y hy => h n y j hy
        have e1 : π ≫ H.hom = H₀.hom ≫ spMap q := pullback.condition
        rw [← Category.assoc, hm, Category.assoc, Category.assoc, e1]
      have hle : κ.ker ≤ ((fstG I₀ n H₀).left ≫ π).ker := by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ h0
      exact ⟨pullback.lift (fstG I₀ n H₀).left (IsClosedImmersion.lift κ _ hle)
        (IsClosedImmersion.lift_fac _ _ _).symm, pullback.lift_fst _ _ _⟩
  have hker : secIdeal hN s ≤ π.ker := by
    have e : π = (inv (pullback.fst π κ) ≫ pullback.snd π κ) ≫ κ := by
      rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [e]
    exact (Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)).ge.trans
      (Scheme.Hom.le_ker_comp _ _)
  refine exists_div_sec H.hom hr s fun j x hx => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    H.left.isBasis_affineOpens.exists_subset_of_mem_open hx (N.U j).isOpen
  have hle : U ≤ N.U j := hUW
  have h1 := EffCartierData.ideal_locIdeal _ _ (exists_mem_chart hN)
    (associated_germ_sec s) ⟨U, hU⟩ j hle
  have h2 := Scheme.Hom.ideal_ker_le π ⟨U, hU⟩
    (hker ⟨U, hU⟩ (h1.ge (Ideal.mem_span_singleton_self _)))
  obtain ⟨g, hg⟩ := dvd_of_app_eq_zero r H.hom hU
    ((H.left.presheaf.map (homOfLE hle).op).hom (s.f j)) h2
  have hxU' : (𝟙 H.left : H.left ⟶ H.left) x ∈ U := hxU
  refine ⟨gs (𝟙 H.left) x U g, ?_⟩
  rw [← gs_res (𝟙 H.left) x hle hxU' (s.f j), hg, gs_mul _ x U hxU',
    gs_constFn H.hom U _ x hxU', Category.id_comp]

end GlobalTheory.GermDiv
end
