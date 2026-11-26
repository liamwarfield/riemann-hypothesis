module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensOfDataFrom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.GensFrom

theorem lam_form {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (x y : T ⟶ B) (U : Type)
    [CommGroup U] (H : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), H ((lift x y).left ≫ (psum B (x2 B) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      (∏ k, H (lamPts x y k) ^ negε k)⁻¹ := by
  have p : ∀ I : Finset (Fin 2), (lift x y).left ≫ (psum B (x2 B) I).left = (psum B ![x, y] I).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I).trans (by
      congr 1; funext i; fin_cases i <;> simp [x2, preHom]))
  simp only [p]
  rw [← Equiv.ulift.symm.prod_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    Fin.prod_univ_four]
  have q0 : psum B ![x, y] ∅ = 1 := rfl
  have q1 : psum B ![x, y] {0} = x := _root_.mul_one x
  have q2 : psum B ![x, y] {1} = y := _root_.mul_one y
  have q3 : psum B ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  simp [q0, q1, q2, q3, lamPts, negε]
  generalize H (x * y).left = A, H x.left = A₁, H y.left = A₂, H (1 : T ⟶ B).left = A₀
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {F : Y' ⟶ Y}

theorem good_linComb {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good (LB.LinComb L φ ε) z (fun ψ k => J (ψ ≫ φ k)) := fun ψ => hJ.mem φ ψ

theorem val_flatGen (u : LB.Gen ((LB.LinComb L φ ε).pull F)) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (GlobalTheory.UU.flatGen u) r z J = val u r z (fun ψ k => J (ψ ≫ φ k)) := by
  exact (gm_res r z _ (hJ.mem (fun k => F ≫ φ k) r) _).trans
    (val_of u r z _ (fun _ k => J (r ≫ F ≫ φ k)) (fun _ => funext fun k => by simp only [Category.assoc])).symm

theorem val_unflatGen (v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (GlobalTheory.UU.unflatGen v) r z (fun ψ k => J (ψ ≫ φ k)) = val v r z J := by
  exact (gm_res r z _ ((good_linComb (φ := φ) (ε := ε) hJ).mem (fun _ : PUnit => F) r) _).trans
    (val_of v r z J (fun k => J ((r ≫ F) ≫ φ k)) (fun k => by simp only [Category.assoc])).symm

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

theorem om_lam {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left} (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J' : (Z ⟶ B'.left) → M'.ι) :
    GlobalTheory.ArcPull.om w z (fun ψ (I : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum B (x2 B) I.down).left))
      (fun ψ (I : ULift.{0} (Finset (Fin 2))) => J' (ψ ≫ (psum B' (x2 B') I.down).left)) p = lamVal w p z J J' := by
  have H : ∀ i i' : (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).ι, i = i' →
      gm p z ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U i) (w.s i) =
        gm p z ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U i') (w.s i') := by
    rintro _ _ rfl; rfl
  unfold GlobalTheory.ArcPull.om Geo.Tor.gw lamVal
  refine H (fun _ (I : ULift.{0} (Finset (Fin 2))) => J ((p ≫ β₂) ≫ (psum B (x2 B) I.down).left),
      fun (I : ULift.{0} (Finset (Fin 2))) => J' (p ≫ (psum B' (x2 B') I.down).left))
    (fun _ (I : ULift.{0} (Finset (Fin 2))) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left),
      fun (I : ULift.{0} (Finset (Fin 2))) => J' (p ≫ (psum B' (x2 B') I.down).left)) (Prod.ext ?_ rfl)
  funext _ I
  exact congrArg J (Category.assoc _ _ _)

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

theorem exists_gen_of_base {W V : Type} [CommRing W] [CommRing V] {BT : Over (Sp W)} [GrpObj BT] [IsCommMonObj BT]
    {BQ : Over (Sp V)} [GrpObj BQ] [IsCommMonObj BQ] {MT : LB BT.left} {MQ : LB BQ.left} (hMT : MT.IsLB) (hMQ : MQ.IsLB)
    (iw : W →+* V) {β : BQ.left ⟶ BT.left} {β₂ : (G2 BQ).left ⟶ (G2 BT).left} (hsq : IsSquare β β₂)
    (w : LB.Iso (abelian₂ BQ MQ) ((abelian₂ BT MT).pull β₂)) (hw : w.IsGen) (x y : 𝟙_ (Over (Sp V)) ⟶ BQ)
    (x₀ y₀ : 𝟙_ (Over (Sp W)) ⟶ BT) (hx : x.left ≫ β = spMap iw ≫ x₀.left) (hy : y.left ≫ β = spMap iw ≫ y₀.left)
    (τ₁ : LB.Gen (LB.LinComb MT (lamPts x₀ y₀) negε)) (h₁ : τ₁.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb MQ (lamPts x y) negε), τ.IsGen ∧ ∀ (T' : Over (Sp V)) (z : T'.left) J J',
      Good MT z J → Good MQ z J' →
        val τ (toUnit T').left z J' = lamVal w (lift (toUnit T' ≫ x) (toUnit T' ≫ y)).left z J J' *
          val τ₁ (T'.hom ≫ spMap iw) z J := by
  have hψ : (lift x y).left ≫ β₂ = spMap iw ≫ (lift x₀ y₀).left := by
    apply pullback.hom_ext
    · show ((lift x y).left ≫ β₂) ≫ (fst BT BT).left = (spMap iw ≫ (lift x₀ y₀).left) ≫ (fst BT BT).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
        lift_fst]
    · show ((lift x y).left ≫ β₂) ≫ (snd BT BT).left = (spMap iw ≫ (lift x₀ y₀).left) ≫ (snd BT BT).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
        lift_snd]
  obtain ⟨t₂, ht₂, hv₂⟩ := exists_gen hMT
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift x₀ y₀).left ≫ (psum BT (x2 BT) I.down).left)
    (ε' := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (by
      intro U _ H
      rw [lam_form x₀ y₀ U H, ← Finset.prod_inv_distrib]
      simp only [zpow_neg]) (LB.invGen MT _ _ τ₁) (DVR.invGen_isGen _ _ _ _ h₁)
  let t₃ : LB.Gen ((abelian₂ BT MT).pull (lift x₀ y₀).left) := GlobalTheory.UU.unflatGen t₂
  have ht₃ : t₃.IsGen := GlobalTheory.UU.unflatGen_isGen ht₂
  obtain ⟨a, ha, hva⟩ := GlobalTheory.ArcPull.exists_down_om hw (LB.isLB_linComb hMT _ _) (LB.isLB_linComb hMQ _ _)
    (φ' := fun _ : PUnit => (lift x y).left) (φ := fun _ => (lift x₀ y₀).left) (ε := fun _ => 1) (spMap iw)
    (fun _ => hψ) t₃ ht₃
  obtain ⟨τ, hτ, hvτ⟩ := exists_gen hMQ
    (φ := fun I : ULift.{0} (Finset (Fin 2)) => (lift x y).left ≫ (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => -((-1 : ℤ) ^ (2 - I.down.card))) (φ' := lamPts x y) (ε' := negε) (by
      intro U _ H
      simp only [zpow_neg, Finset.prod_inv_distrib]
      rw [lam_form x y U H, inv_inv]) (LB.invGen MQ _ _ (GlobalTheory.UU.flatGen a))
    (DVR.invGen_isGen _ _ _ _ (GlobalTheory.UU.flatGen_isGen ha))
  refine ⟨τ, hτ, fun T' z J J' hJ hJ' => ?_⟩
  have e1 := hvτ _ (toUnit T').left z J' hJ'
  have e5 := val_flatGen (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x y).left) a (toUnit T').left z hJ'
  rw [val_inv, e5] at e1
  have e6 : val t₃ ((toUnit T').left ≫ spMap iw) z
      (fun ψ (k : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum BT (x2 BT) k.down).left)) =
      val t₂ ((toUnit T').left ≫ spMap iw) z J := val_unflatGen (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x₀ y₀).left) t₂ ((toUnit T').left ≫ spMap iw) z hJ
  have e2 := hva _ (toUnit T').left z _ _
    (good_linComb (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ)
    (good_linComb (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ')
  rw [e6, hv₂ _ _ z J hJ, val_inv, Fintype.prod_unique, zpow_one, om_lam] at e2
  have e3 : (lift (toUnit T' ≫ x) (toUnit T' ≫ y)).left = (toUnit T').left ≫ (lift x y).left := by
    rw [← comp_lift]; rfl
  have e4 : (toUnit T').left = T'.hom := by simpa using Over.w (toUnit T')
  rw [e1, e3, ← e4, ← inv_inv (val τ₁ ((toUnit T').left ≫ spMap iw) z J), e2, _root_.mul_inv, _root_.mul_inv_cancel_left]
  rfl

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart


open GensFrom in
theorem exists_gens_of_dataFrom {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V)
    (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)) {M : ℕ}
    (eI : I ≃ Fin M) (hD : DataFrom T iw s ε n Q e) :
    ∃ τ : GlobalTheory.Poinc.Sep.Gens Q, GlobalTheory.Poinc.Sep.TauIn Q τ (fun k => s (eI.symm k))
      (fun k => (n : ℤ) • pull e.toIntLinearEquiv.toLinearMap (ε (eI.symm k))) ∧ GlobalTheory.Poinc.Sep.FromBase Q τ iw := by
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, hτ⟩ := hD
  have key := fun a b => exists_gen_of_base T.M.isLB Q.M.isLB iw hsq w hw (Q.c a) (Q.c b)
    (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b)) (hc a) (hc b) (T.τ₀ _ _) (T.τ₀_gen _ _)
  choose τ hτg hτv using key
  refine ⟨τ, fun a b => ⟨hτg a b, ?_⟩, T.B, inferInstance, inferInstance, T.M.L, fun a => T.c₀ ((n : ℤ) • e a),
    fun a b => T.τ₀ _ _, β, β₂, w, T.isAb, T.M.isLB, hpb, hsq, hw, hc, fun a b => T.τ₀_gen _ _,
    fun T' a b z J J' hJ hJ' => hτv a b T' z J J' hJ hJ'⟩
  obtain ⟨k, hk, hv⟩ := hτ a b
  refine ⟨k, ?_, fun z J' hJ' => ?_⟩
  · rw [hk]
    refine Fintype.prod_equiv eI _ _ fun i => ?_
    simp [pull]
  · choose J hJ using fun χ : (TK V).left ⟶ T.B.left => exists_chart T.M.isLB (χ z)
    rw [hv z J J' hJ hJ', hτv a b (TK V) z J J' hJ hJ']

end GlobalTheory.TChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernEqSumCupInvariantForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernEqSumCupInvariantForms
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolForm

theorem wedge_two_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (z : ⋀[K]^2 V)
    (h : ∀ f : Fin 2 → Module.Dual K V,
      exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 f) z = 0) : z = 0 := by
  by_contra hz
  obtain ⟨J, hJ⟩ := GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero
    (⇑(Module.finBasis K V).dualBasis) (Module.finBasis K V).dualBasis.span_eq z hz
  exact hJ (h _)

theorem pairingDual_ιMulti_two {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Fin 2 → Module.Dual K V) (u v : V) :
    exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 f) (exteriorPower.ιMulti K 2 ![u, v]) =
      f 0 u * f 1 v - f 0 v * f 1 u := by
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp
  ring

theorem ιMulti_two_swap {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] (u v : V) :
    exteriorPower.ιMulti K 2 ![u, v] = -exteriorPower.ιMulti K 2 ![v, u] := by
  have e : (![v, u] ∘ Equiv.swap (0 : Fin 2) 1) = ![u, v] := by
    ext i; fin_cases i <;> rfl
  rw [← e, AlternatingMap.map_swap _ _ (by decide)]


set_option maxHeartbeats 1000000 in
theorem chern_eq_sum_cup_form : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A L ψ → ∃ (I : Type) (_ : Fintype I) (c : I → primDR A) (ω : I → Form (A.hom ≫ 𝟙 (Sp K))) (hω : ∀ k, Form.cl _ (ω k) ∈ primDR A), IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (c k).1 (Form.cl _ (ω k))) ∧ ∀ f ∈ Fil A, ∀ x : HdR A, ψ f x = ∑ k, f (c k) * x ⟨_, hω k⟩ := by
  intro H K _ A _ g hA hg L hL ψ hψ
  obtain ⟨hFree, hHodge, -, -, hDual⟩ := H
  obtain ⟨-, hfin, -, -, e, he⟩ := hFree K A g hA hg
  obtain ⟨-, ⟨N, hN⟩, -⟩ := hHodge K A g hA hg
  have hiso := (hDual K A g hA hg L hL ψ hψ).1
  obtain ⟨n, a, b, hch, rfl⟩ := hψ
  let pF := Submodule.projectionOnto (PrimitiveSubmodule A) N hN
  let pN := Submodule.projectionOnto N (PrimitiveSubmodule A) hN.symm
  have hsplit : ∀ c : primDR A, ((pF c : primDR A)) + (pN c : primDR A) = c :=
    Submodule.projection_add_projection_eq_self hN
  have hpN : ∀ c ∈ PrimitiveSubmodule A, pN c = 0 := fun c hc ↦
    (Submodule.projectionOnto_apply_eq_zero_iff hN.symm).2 hc

  have hvan : ∀ x y : Module.Dual K (primDR A),
      ∑ k, (x (pN (a k)) * y (pN (b k)) - x (pN (b k)) * y (pN (a k))) = 0 := by
    intro x y
    have hmem : ∀ z : Module.Dual K (primDR A), z ∘ₗ N.subtype ∘ₗ pN ∈ Fil A := fun z ↦
      (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by simp [hpN c hc]
    have := hiso _ (hmem x) _ (hmem y)
    rw [wedgeForm_apply] at this
    simpa using this
  have h0 : ∑ k, exteriorPower.ιMulti K 2
      ![((pN (a k) : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))), ((pN (b k) : primDR A) : FirstDeRham _)] = 0 := by
    haveI : FiniteDimensional K (FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := hfin
    apply wedge_two_eq_zero
    intro f
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [pairingDual_ιMulti_two]
    exact hvan (f 0 ∘ₗ (primDR A).subtype) (f 1 ∘ₗ (primDR A).subtype)

  have hform : ∀ c : PrimitiveSubmodule A, ∃ w : Form (A.hom ≫ 𝟙 (Sp K)),
      Form.cl _ w = ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := fun c ↦ by
    have hc := c.2
    change ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) ∈ F1 _ at hc
    rw [hodgeFiltration_eq_range] at hc
    exact hc
  choose form hform using hform
  have hanti : ∀ u v : FirstDeRham (A.hom ≫ 𝟙 (Sp K)),
      cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) u v = -cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) v u := fun u v ↦ by
    rw [← he, ← he, ← map_neg, ιMulti_two_swap]
  have key : ∀ a₁ a₂ b₁ b₂ : FirstDeRham (A.hom ≫ 𝟙 (Sp K)),
      cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) (b₁ + b₂) =
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) b₁ +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-b₂) a₁ + cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) a₂ b₂ := by
    intro a₁ a₂ b₁ b₂
    simp only [map_add (f := _), LinearMap.add_apply, map_neg, LinearMap.neg_apply]
    rw [hanti a₁ b₂]
    abel
  have hZ : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_zero e, ← h0, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ (he _ _).symm
  obtain ⟨ω, hωdef⟩ : ∃ ω : Fin n ⊕ Fin n → Form (A.hom ≫ 𝟙 (Sp K)),
      ω = Sum.elim (fun k ↦ form (pF (b k))) (fun k ↦ form (pF (a k))) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : Fin n ⊕ Fin n → primDR A,
      c = Sum.elim a (fun k ↦ -(pN (b k) : primDR A)) := ⟨_, rfl⟩
  have hωl : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inl k)) = (pF (b k) : primDR A).1 := fun k ↦ by
    rw [hωdef, Sum.elim_inl, hform]
  have hωr : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inr k)) = (pF (a k) : primDR A).1 := fun k ↦ by
    rw [hωdef, Sum.elim_inr, hform]
  have hcl : ∀ k, c (Sum.inl k) = a k := fun k ↦ by rw [hcdef, Sum.elim_inl]
  have hcr : ∀ k, c (Sum.inr k) = -(pN (b k) : primDR A) := fun k ↦ by rw [hcdef, Sum.elim_inr]
  have hω : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω k) ∈ primDR A := fun k ↦ by
    rcases k with k | k
    · rw [hωl]; exact Subtype.property _
    · rw [hωr]; exact Subtype.property _
  have hsum : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (c k).1 (Form.cl _ (ω k)) =
      ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 := by
    have e3 : ∀ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 =
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (pF (b k) : primDR A).1 +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-(pN (b k) : primDR A).1) (pF (a k) : primDR A).1 +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 :=
      fun k ↦ by
      have ha := congrArg Subtype.val (hsplit (a k))
      have hb := congrArg Subtype.val (hsplit (b k))
      rw [Submodule.coe_add] at ha hb
      rw [← ha, ← hb]
      exact key _ _ _ _
    rw [Fintype.sum_sum_type]
    simp only [hcl, hcr, hωl, hωr, Submodule.coe_neg]
    rw [Finset.sum_congr rfl fun k _ ↦ e3 k, Finset.sum_add_distrib, Finset.sum_add_distrib, hZ,
      add_zero]
  refine ⟨Fin n ⊕ Fin n, inferInstance, c, ω, hω, by rw [hsum]; exact hch, ?_⟩
  intro f hf x
  rw [Fil, Submodule.mem_dualAnnihilator] at hf
  have hfF : ∀ c : PrimitiveSubmodule A, f c = 0 := fun c ↦ hf _ c.2
  have hfa : ∀ k, f (a k) = f (pN (a k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (a k)]
    rw [map_add (f := _), hfF, zero_add]
  have hfb : ∀ k, f (b k) = f (pN (b k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (b k)]
    rw [map_add (f := _), hfF, zero_add]
  have hxa : ∀ k, x (a k) = x (pF (a k)) + x (pN (a k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (a k)]
    rw [map_add (f := _)]
  have hxb : ∀ k, x (b k) = x (pF (b k)) + x (pN (b k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (b k)]
    rw [map_add (f := _)]
  have hxl : ∀ k, x ⟨_, hω (Sum.inl k)⟩ = x (pF (b k)) := fun k ↦
    congrArg x (Subtype.ext (hωl k))
  have hxr : ∀ k, x ⟨_, hω (Sum.inr k)⟩ = x (pF (a k)) := fun k ↦
    congrArg x (Subtype.ext (hωr k))
  have hv := hvan f x
  rw [wedgeForm_apply, Fintype.sum_sum_type]
  simp only [hxl, hxr, hcl, hcr, map_neg]
  simp only [hfa, hfb, hxa, hxb]
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hv]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.PolForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernEqSumCupInvariantFormsStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChern_eq_sum_cup_invariantForms : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A L ψ → ∃ (I : Type) (_ : Fintype I) (c : I → primDR A) (ω : I → Form (A.hom ≫ 𝟙 (Sp K))) (hω : ∀ k, Form.cl _ (ω k) ∈ primDR A), IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (c k).1 (Form.cl _ (ω k))) ∧ ∀ f ∈ Fil A, ∀ x : HdR A, ψ f x = ∑ k, f (c k) * x ⟨_, hω k⟩ := by
  first | exact @GlobalTheory.PolForm.chern_eq_sum_cup_form | exact GlobalTheory.PolForm.chern_eq_sum_cup_form | (intros; apply GlobalTheory.PolForm.chern_eq_sum_cup_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentBijectiveApp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentBijectiveApp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum.LBDesc

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull unit_ext glue_unit exists_chart gw PGen)

variable {Z Y : Scheme.{0}}

def toZ (V : Z.Opens) {O : V.toScheme.Opens} (a : Γ(V.toScheme, O)ˣ) : Γ(Z, V.ι ''ᵁ O)ˣ := a

theorem toZ_res (V : Z.Opens) {O O' : V.toScheme.Opens} (h : O' ≤ O) (a : Γ(V.toScheme, O)ˣ) :
    toZ V (res h a) = res (V.ι.image_mono h) (toZ V a) := rfl

theorem toZ_mul (V : Z.Opens) {O : V.toScheme.Opens} (a b : Γ(V.toScheme, O)ˣ) :
    toZ V (a * b) = toZ V a * toZ V b := rfl

theorem image_preimage_le' (V : Z.Opens) (O : Z.Opens) : V.ι ''ᵁ V.ι ⁻¹ᵁ O ≤ O :=
  Set.image_preimage_subset _ _

theorem toZ_pullU (V : Z.Opens) (O : Z.Opens) (a : Γ(Z, O)ˣ) :
    toZ V (pullU V.ι O a) = res (image_preimage_le' V O) a := rfl

theorem res_toZ_pullU (V : Z.Opens) (O : Z.Opens) {W : Z.Opens} (hW : W ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ O) (a : Γ(Z, O)ˣ) :
    res hW (toZ V (pullU V.ι O a)) = res (hW.trans (image_preimage_le' V O)) a := by
  rw [toZ_pullU, LB.res_res]

theorem transport (L' : LB Z) (V : Z.Opens) (t : LB.Gen (L'.pull V.ι)) (ht : t.IsGen) :
    ∃ T : ∀ k : L'.ι, Γ(Z, V ⊓ L'.U k)ˣ, ∀ k k',
      res (inf_le_left : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k) (T k) =
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k') *
        res (inf_le_right : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k') (T k') := by
  have hle : ∀ k, V ⊓ L'.U k ≤ V.ι ''ᵁ LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k) := by
    intro k z hz
    exact ⟨⟨z, hz.1⟩, Set.mem_iInter.2 fun _ => hz.2, rfl⟩
  refine ⟨fun k => res (hle k) (toZ V (LB.ts t (fun _ => k))), fun k k' => ?_⟩
  have hle2 : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V.ι ''ᵁ (LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k) ⊓
      LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k')) := fun z hz =>
    ⟨⟨z, hz.1.1⟩, ⟨Set.mem_iInter.2 fun _ => hz.1.2, Set.mem_iInter.2 fun _ => hz.2.2⟩, rfl⟩
  have e := congrArg (fun x => res hle2 (toZ V x)) ((LB.isGen_iff L' t).1 ht (fun _ => k) (fun _ => k'))
  simp only [toZ_mul, toZ_res, map_mul, LB.res_res, LB.lcg, Fintype.prod_unique, zpow_one, res_toZ_pullU] at e
  simp only [LB.res_res]
  exact e

theorem gm_compat (L' : LB Z) (V : Z.Opens) (T : ∀ k : L'.ι, Γ(Z, V ⊓ L'.U k)ˣ)
    (hT : ∀ k k', res (inf_le_left : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k) (T k) =
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k') *
        res (inf_le_right : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k') (T k'))
    {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι) (hV : f w ∈ V) (hk : f w ∈ L'.U k)
    (hk' : f w ∈ L'.U k') :
    gm f w (V ⊓ L'.U k) (T k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w (V ⊓ L'.U k') (T k') := by
  have hm : f w ∈ V ⊓ L'.U k ⊓ (V ⊓ L'.U k') := ⟨⟨hV, hk⟩, hV, hk'⟩
  have e := congrArg (gm f w (V ⊓ L'.U k ⊓ (V ⊓ L'.U k'))) (hT k k')
  rwa [map_mul, gm_res f w _ hm, gm_res f w _ hm, gm_res f w _ hm] at e

theorem ratio (p : Z ⟶ Y) (L' : LB Z) (hL' : L'.IsLB) {V₁ V₂ : Y.Opens}
    (T₁ : ∀ k : L'.ι, Γ(Z, p ⁻¹ᵁ V₁ ⊓ L'.U k)ˣ) (T₂ : ∀ k : L'.ι, Γ(Z, p ⁻¹ᵁ V₂ ⊓ L'.U k)ˣ)
    (h₁ : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V₁ → f w ∈ L'.U k → f w ∈ L'.U k' →
      gm f w _ (T₁ k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T₁ k'))
    (h₂ : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V₂ → f w ∈ L'.U k → f w ∈ L'.U k' →
      gm f w _ (T₂ k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T₂ k')) :
    ∃ r : Γ(Z, p ⁻¹ᵁ (V₁ ⊓ V₂))ˣ, ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k : L'.ι),
      f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) → f w ∈ L'.U k → gm f w _ r = gm f w _ (T₂ k) * (gm f w _ (T₁ k))⁻¹ := by
  have l₁ : ∀ k, p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k ≤ p ⁻¹ᵁ V₁ ⊓ L'.U k := fun _ x hx => ⟨hx.1.1, hx.2⟩
  have l₂ : ∀ k, p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k ≤ p ⁻¹ᵁ V₂ ⊓ L'.U k := fun _ x hx => ⟨hx.1.2, hx.2⟩
  have hu : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k : L'.ι) (hw : f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k),
      gm f w _ (res (l₂ k) (T₂ k) * (res (l₁ k) (T₁ k))⁻¹) = gm f w _ (T₂ k) * (gm f w _ (T₁ k))⁻¹ := by
    intro W f w k hw
    rw [map_mul, map_inv, gm_res f w _ hw, gm_res f w _ hw]
  obtain ⟨s, hs⟩ := glue_unit (p ⁻¹ᵁ (V₁ ⊓ V₂)) (fun k => p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k) (fun _ => inf_le_left)
    (fun x hx => by
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact Opens.mem_iSup.2 ⟨k, hx, hk⟩)
    (fun k => res (l₂ k) (T₂ k) * (res (l₁ k) (T₁ k))⁻¹)
    (fun i j x hx => by
      rw [hu (𝟙 Z) x i hx.1, hu (𝟙 Z) x j hx.2, h₁ (𝟙 Z) x i j hx.1.1.1 hx.1.2 hx.2.2,
        h₂ (𝟙 Z) x i j hx.1.1.2 hx.1.2 hx.2.2, mul_inv, _root_.mul_mul_mul_comm, _root_.mul_inv_cancel, _root_.one_mul])
  refine ⟨s, fun f w k hw hk => ?_⟩
  have hm : f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k := ⟨hw, hk⟩
  rw [← gm_res f w inf_le_left hm s, hs k, hu f w k hm]

theorem descend (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) (O : Y.Opens)
    (r : Γ(Z, p ⁻¹ᵁ O)ˣ) : ∃ g : Γ(Y, O)ˣ, pullU p O g = r := by
  let e := RingEquiv.ofBijective (p.app O).hom (hp O)
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom r, Units.ext ?_⟩
  exact e.apply_symm_apply r.val

theorem eq_of_gm (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) {O : Y.Opens}
    {a b : Γ(Y, O)ˣ} (h : ∀ z : Z, p z ∈ O → gm (𝟙 Z ≫ p) z O a = gm (𝟙 Z ≫ p) z O b) : a = b := by
  have e : pullU p O a = pullU p O b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 Z) p z O hz a, gm_pull (𝟙 Z) p z O hz b]
    exact h z hz
  exact Units.ext ((hp O).1 (congrArg Units.val e))

def descLB (V : Y → Y.Opens) (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) : LB Y := ⟨Y, V, g⟩

theorem isLB_descLB (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) (L' : LB Z) (hL' : L'.IsLB)
    (V : Y → Y.Opens) (hyV : ∀ y, y ∈ V y) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descLB V g).IsLB := {
  cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hyV y⟩
  g_self := fun y => eq_of_gm p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [gm_res (𝟙 Z ≫ p) z _ hz, map_one]
    exact (key (𝟙 Z) z y y k hz hz hk).trans (mul_inv_cancel _)
  cocycle := fun a b c => eq_of_gm p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [map_mul, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz,
      key (𝟙 Z) z a b k hz.1.1 hz.1.2 hk, key (𝟙 Z) z b c k hz.1.2 hz.2 hk,
      key (𝟙 Z) z a c k hz.1.1 hz.2 hk]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel }

theorem chart_le (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (q : (LB.div ((descLB V g).pull p) L').ι) :
    (LB.div ((descLB V g).pull p) L').U q ≤ p ⁻¹ᵁ V (q.1 PUnit.unit) ⊓ L'.U q.2 :=
  fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, hx.2⟩

def descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) : LB.Iso L' ((descLB V g).pull p) :=
  ⟨fun q => (res (chart_le p L' V g q) (T (q.1 PUnit.unit) q.2))⁻¹⟩

theorem gw_descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) {W : Scheme.{0}} (f : W ⟶ Z) (x : W) (j : Y) (k : L'.ι)
    (hj : p (f x) ∈ V j) (hk : f x ∈ L'.U k) :
    gw (descIso p L' V T g) f x j k = (gm f x _ (T j k))⁻¹ := by
  unfold gw descIso
  exact (map_inv (gm f x _) _).trans (congrArg (·⁻¹) (gm_res f x (chart_le p L' V g (fun _ => j, k))
    ⟨Set.mem_iInter.2 fun _ => hj, hk⟩ (T j k)))

theorem isGen_descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (hc : ∀ (y : Y) {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V y → f w ∈ L'.U k →
      f w ∈ L'.U k' → gm f w _ (T y k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T y k'))
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descIso p L' V T g).IsGen := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff]
  intro W f x j j' k k' hj hj' hk hk'
  rw [gw_descIso p L' V T g f x j k hj hk, gw_descIso p L' V T g f x j' k' hj' hk',
    key f x j j' k hj hj' hk, hc j' f x k k' hj' hk hk']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum.LBDesc

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_pull)
open GlobalTheory.Mum.LBDesc

theorem lb_descend : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, Function.Bijective (p.app V).hom) →
    ∀ L' : LB Z, L'.IsLB → (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen) →
    ∃ L : LB Y, L.IsLB ∧ LBIso L' (L.pull p) := by
  intro Z Y p hp L' hL' hloc
  choose V hyV t ht using hloc
  choose T hT using fun y => transport L' (p ⁻¹ᵁ V y) (t y) (ht y)
  have hc : ∀ (y : Y) {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V y → f w ∈ L'.U k →
      f w ∈ L'.U k' → gm f w _ (T y k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T y k') :=
    fun y _ f w k k' h hk hk' => gm_compat L' _ (T y) (hT y) f w k k' h hk hk'
  choose r hr using fun y y' => ratio p L' hL' (T y) (T y') (hc y) (hc y')
  choose g hg using fun y y' => descend p hp _ (r y y')
  have key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹ := by
    intro W f w y y' k h1 h2 hk
    exact (gm_pull f p w (V y ⊓ V y') ⟨h1, h2⟩ (g y y')).symm.trans
      ((congrArg _ (hg y y')).trans (hr y y' f w k ⟨h1, h2⟩ hk))
  exact ⟨descLB V g, isLB_descLB p hp L' hL' V hyV T g key, descIso p L' V T g,
    isGen_descIso p L' V T g hc key⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentBijectiveAppStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_descent_bijective_app : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen) → ∃ L : LB Y, L.IsLB ∧ LBIso L' (L.pull p) := by
  first | exact @GlobalTheory.Mum.lb_descend | exact GlobalTheory.Mum.lb_descend | (intros; apply GlobalTheory.Mum.lb_descend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBasePeriodsFactorMulGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBasePeriodsFactorMulGenerator
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautTau

section Core

variable {X X' P P' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K : Type} [Fintype K]

theorem exists_gen_across (hL : L.IsLB) (hL' : L'.IsLB) (ψ : K → (P ⟶ X)) (ψ' : K → (P' ⟶ X')) (ε : K → ℤ)
    (β₂ : P' ⟶ P) (w : LB.Iso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull β₂)) (hw : w.IsGen) (p : Y ⟶ P')
    (b : LB.Gen (LB.LinComb L (fun k => p ≫ β₂ ≫ ψ k) (fun k => -ε k))) (hb : b.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L' (fun k => p ≫ ψ' k) (fun k => -ε k)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        val u r z J' = gm (r ≫ p) z _ (w.s (fun _ k => J ((r ≫ p) ≫ β₂ ≫ ψ k), fun k => J' ((r ≫ p) ≫ ψ' k))) *
          val b r z J := by
  have hC : (LB.LinComb L ψ ε).IsLB := DVR.linComb_isLB _ hL _ _
  have hC' : (LB.LinComb L' ψ' ε).IsLB := DVR.linComb_isLB _ hL' _ _
  have pw := (isGen_iff w).1 hw

  have wchg : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j j₂ : K → L.ι) (q q₂ : K → L'.ι),
      (∀ k, (f ≫ p ≫ β₂ ≫ ψ k) z ∈ L.U (j k)) → (∀ k, (f ≫ p ≫ β₂ ≫ ψ k) z ∈ L.U (j₂ k)) →
      (∀ k, (f ≫ p ≫ ψ' k) z ∈ L'.U (q k)) → (∀ k, (f ≫ p ≫ ψ' k) z ∈ L'.U (q₂ k)) →
      gw w (f ≫ p) z j q = (∏ k, gm (f ≫ p ≫ β₂ ≫ ψ k) z _ (L.g (j k) (j₂ k)) ^ ε k) *
        (∏ k, gm (f ≫ p ≫ ψ' k) z _ (L'.g (q k) (q₂ k)) ^ ε k)⁻¹ * gw w (f ≫ p) z j₂ q₂ := by
    intro Z f z j j₂ q q₂ hj hj₂ hq hq₂
    have m₁ : β₂ ((f ≫ p) z) ∈ (LB.LinComb L ψ ε).U j := Set.mem_iInter.2 fun k => hj k
    have m₂ : β₂ ((f ≫ p) z) ∈ (LB.LinComb L ψ ε).U j₂ := Set.mem_iInter.2 fun k => hj₂ k
    have m₃ : (f ≫ p) z ∈ (LB.LinComb L' ψ' ε).U q := Set.mem_iInter.2 fun k => hq k
    have m₄ : (f ≫ p) z ∈ (LB.LinComb L' ψ' ε).U q₂ := Set.mem_iInter.2 fun k => hq₂ k
    rw [pw Z (f ≫ p) z j j₂ q q₂ m₁ m₂ m₃ m₄]
    erw [gm_linComb L ψ ε ((f ≫ p) ≫ β₂) z j j₂ m₁ m₂, gm_linComb L' ψ' ε (f ≫ p) z q q₂ m₃ m₄]
    simp only [Category.assoc]
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' (fun k => p ≫ ψ' k) q)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : K → L.ι),
        f z ∈ LB.wchart L' (fun k => p ≫ ψ' k) q → f z ∈ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j →
        gm f z _ s = gw w (f ≫ p) z j q * gm f z _ (b.s j) := by
    intro q
    let W : (K → L.ι) → Y.Opens := fun j =>
      LB.wchart L' (fun k => p ≫ ψ' k) q ⊓ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j
    have l₀ : ∀ j, W j ≤ LB.wchart L' (fun k => p ≫ ψ' k) q := fun j => inf_le_left
    have l₁ : ∀ j, W j ≤ p ⁻¹ᵁ (((LB.LinComb L ψ ε).pull β₂).U (fun _ => j) ⊓ (LB.LinComb L' ψ' ε).U q) :=
      fun j x hx => ⟨mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 k),
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.1 k⟩
    have l₂ : ∀ j, W j ≤ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j := fun j => inf_le_right
    obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Y, W j)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : K → L.ι), f z ∈ W j →
        gm f z (W j) (u j) = gw w (f ≫ p) z j q * gm f z _ (b.s j) :=
      ⟨fun j => res (l₁ j) (pullU p _ (w.s (fun _ => j, q))) * res (l₂ j) (b.s j), fun Z f z j hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f z (l₁ j) hz _).trans (gm_pull f p z _ (l₁ j hz) _)) (gm_res f z (l₂ j) hz _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        choose j hj using fun k => exists_chart hL ((p ≫ β₂ ≫ ψ k) x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hx, Set.mem_iInter.2 hj⟩) u (fun j j₂ x hx => by
        rw [hu _ (𝟙 Y) x j hx.1, hu _ (𝟙 Y) x j₂ hx.2]
        have a := wchg Y (𝟙 Y) x j j₂ q q (fun k => Set.mem_iInter.1 hx.1.2 k) (fun k => Set.mem_iInter.1 hx.2.2 k)
          (fun k => Set.mem_iInter.1 hx.1.1 k) (fun k => Set.mem_iInter.1 hx.1.1 k)
        have c := gen_trans hb (𝟙 Y) x hx.1.2 hx.2.2
        have one : (∏ k, gm (𝟙 Y ≫ p ≫ ψ' k) x _ (L'.g (q k) (q k)) ^ ε k) = 1 :=
          Finset.prod_eq_one fun k _ => by
            rw [gm_self hL' (𝟙 Y ≫ p ≫ ψ' k) x (show (𝟙 Y ≫ p ≫ ψ' k) x ∈ L'.U (q k) from Set.mem_iInter.1 hx.1.1 k),
              one_zpow]
        have hA : (∏ k, gm (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x _ (L.g (j k) (j₂ k)) ^ ε k) *
            trF (L := L) (fun k => p ≫ β₂ ≫ ψ k) (fun k => -ε k) (𝟙 Y) x j j₂ = 1 := by
          rw [trF, ← Finset.prod_mul_distrib]
          exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, _root_.mul_inv_cancel]
        rw [a, one, inv_one, _root_.mul_one]
        erw [c]
        rw [_root_.mul_mul_mul_comm, hA, _root_.one_mul]
        rfl)
    exact ⟨s, fun Z f z j hq hj => (gm_res f z (l₀ j) ⟨hq, hj⟩ s).symm.trans
      ((congrArg (gm f z (W j)) (hs j)).trans (hu Z f z j ⟨hq, hj⟩))⟩
  choose s hs using glue
  refine ⟨⟨s⟩, fun q q₂ => unit_ext fun x hx => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  swap
  · refine (hs (fun k => J' (r ≫ p ≫ ψ' k)) Z r z (fun k => J (r ≫ p ≫ β₂ ≫ ψ k)) (hJ'.mem (fun k => p ≫ ψ' k) r)
      (hJ.mem (fun k => p ≫ β₂ ≫ ψ k) r)).trans ?_
    congr 1
  choose j hj using fun k => exists_chart hL ((p ≫ β₂ ≫ ψ k) x)
  have mj : (𝟙 Y) x ∈ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j := Set.mem_iInter.2 hj
  have e₁ := hs q Y (𝟙 Y) x j hx.1 mj
  have e₂ := hs q₂ Y (𝟙 Y) x j hx.2 mj
  have c := wchg Y (𝟙 Y) x j j q q₂ hj hj (fun k => Set.mem_iInter.1 hx.1 k) (fun k => Set.mem_iInter.1 hx.2 k)
  have one : (∏ k, gm (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x _ (L.g (j k) (j k)) ^ ε k) = 1 :=
    Finset.prod_eq_one fun k _ => by
      rw [gm_self hL (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x (show (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x ∈ L.U (j k) from hj k), one_zpow]
  rw [one, _root_.one_mul] at c
  have g := gm_linComb L' (fun k => p ≫ ψ' k) (fun k => -ε k) (𝟙 Y) x q q₂ hx.1 hx.2
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx]
  erw [g, e₁, e₂, c]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  rw [_root_.mul_assoc]

end Core

section Main

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]

theorem toUnit_left' {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem ag_four {G : Type} [CommGroup G] (a b c d : G) :
    a⁻¹ * b * c * d⁻¹ = (a * b⁻¹ * c⁻¹ * d)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tauCoord_of_dataFrom (T : TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V)
    (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ))
    (hD : DataFrom T iw s ε n Q e) (a b : Q.X) :
    ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      Q.TauCoord a b k := by
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, hτ⟩ := hD
  obtain ⟨k, hk, hval⟩ := hτ a b
  refine ⟨k, hk, ?_⟩
  let h : (𝟙_ (Over (Sp V))).left ⟶ (𝟙_ (Over (Sp W))).left := spMap iw
  let p : (𝟙_ (Over (Sp V))).left ⟶ (G2 Q.B).left := (lift (Q.c a) (Q.c b)).left
  have c0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have t0 : T.c₀ 0 = 1 := mul_eq_left.1 ((T.c₀_add 0 0).symm.trans (by rw [add_zero]))
  have hF1 : p ≫ β₂ = (lift (pushPt hpb.1.w (Q.c a)) (pushPt hpb.1.w (Q.c b))).left := by
    apply pullback.hom_ext
    · show _ ≫ (fst T.B T.B).left = _ ≫ (fst T.B T.B).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      rfl
    · show _ ≫ (snd T.B T.B).left = _ ≫ (snd T.B T.B).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      rfl
  have px : (pushPt hpb.1.w (Q.c a)).left = h ≫ (T.c₀ ((n : ℤ) • e a)).left := hc a
  have py : (pushPt hpb.1.w (Q.c b)).left = h ≫ (T.c₀ ((n : ℤ) • e b)).left := hc b
  have pxy : (pushPt hpb.1.w (Q.c a) * pushPt hpb.1.w (Q.c b)).left =
      h ≫ (T.c₀ ((n : ℤ) • e a) * T.c₀ ((n : ℤ) • e b)).left := by
    have m := congrArg (fun q => q.left) (map_mul (pushHom hpb (𝟙_ (Over (Sp V)))) (Q.c a) (Q.c b))
    refine m.symm.trans ?_
    show (Q.c a * Q.c b).left ≫ β = _
    rw [← Q.c_add, hc, ← T.c₀_add, ← smul_add, ← map_add (f := _)]
  have p1 : (1 : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ spMap iw) ⟶ T.B).left = h ≫ (1 : 𝟙_ (Over (Sp W)) ⟶ T.B).left := by
    have m := congrArg (fun q => q.left) (map_one (pushHom hpb (𝟙_ (Over (Sp V)))))
    refine m.symm.trans ?_
    show (1 : 𝟙_ (Over (Sp V)) ⟶ Q.B).left ≫ β = _
    have := hc 0
    rw [c0, map_zero, smul_zero, t0] at this
    exact this
  have hFT : FormEq (fun k => h ≫ lamPts (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b)) k) negε
      (fun I => p ≫ β₂ ≫ GlobalTheory.PrimCocycle.lamφ T.B I) (fun I => -GlobalTheory.PrimCocycle.lamε I) := by
    intro U _ H
    have r₁ : ∀ I, p ≫ β₂ ≫ GlobalTheory.PrimCocycle.lamφ T.B I =
        (lift (pushPt hpb.1.w (Q.c a)) (pushPt hpb.1.w (Q.c b))).left ≫ GlobalTheory.PrimCocycle.lamφ T.B I := fun I => by
      rw [← Category.assoc, hF1]
    simp only [r₁, zpow_neg, Finset.prod_inv_distrib]
    rw [GlobalTheory.PrimCocycle.prod_lam, pxy, px, py, p1, Fin.prod_univ_four]
    simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    exact ag_four _ _ _ _
  have hFQ : FormEq (fun I => p ≫ GlobalTheory.PrimCocycle.lamφ Q.B I) (fun I => -GlobalTheory.PrimCocycle.lamε I)
      (lamPts (Q.c a) (Q.c b)) negε := by
    intro U _ H
    simp only [zpow_neg, Finset.prod_inv_distrib]
    rw [GlobalTheory.PrimCocycle.prod_lam, Fin.prod_univ_four]
    simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    exact (ag_four _ _ _ _).symm
  obtain ⟨b₁, hb₁, hv₁⟩ := exists_gen T.M.isLB hFT
    (LB.pullGen T.M.L (lamPts (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b))) negε (T.τ₀ _ _) h)
    (DVR.pullGen_isGen _ _ _ _ (T.τ₀_gen _ _) h)
  obtain ⟨u₁, hu₁, hvu⟩ := exists_gen_across T.M.isLB Q.M.isLB (GlobalTheory.PrimCocycle.lamφ T.B)
    (GlobalTheory.PrimCocycle.lamφ Q.B) GlobalTheory.PrimCocycle.lamε β₂ w hw p b₁ hb₁
  obtain ⟨u, hu, hvq⟩ := exists_gen Q.M.isLB hFQ u₁ hu₁
  refine ⟨u, hu, fun z J' hJ' => ?_⟩
  choose J hJ using fun χ : (TK V).left ⟶ T.B.left => exists_chart T.M.isLB (χ z)
  have hJg : Good T.M.L z J := hJ
  rw [hval z J J' hJg hJ']
  congr 1
  rw [hvq _ _ z J' hJ', hvu _ _ z J J' hJg hJ', hv₁ _ _ z J hJg, val_pull hJg]
  have hr : (toUnit (TK V)).left ≫ p = (lift (toUnit (TK V) ≫ Q.c a) (toUnit (TK V) ≫ Q.c b)).left := by
    rw [← Over.comp_left, comp_lift]
  have hh : (toUnit (TK V)).left ≫ h = (TK V).hom ≫ spMap iw := by
    rw [toUnit_left']
  rw [hh, ← hr]
  rfl

end Main

end GlobalTheory.TautTau
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBasePeriodsFactorMulGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalBase_periods_factor_mul_generator : ∀ {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : GlobalTheory.PolDeg.TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → ∀ a b : Q.X, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧ Q.TauCoord a b k := by
  first | exact @GlobalTheory.TautTau.tauCoord_of_dataFrom | exact GlobalTheory.TautTau.tauCoord_of_dataFrom | (intros; apply GlobalTheory.TautTau.tauCoord_of_dataFrom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFromSpecResidueFieldCompOfIsClosedOfClos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFromSpecResidueFieldCompOfIsClosedOfClos
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Over (Sp R)), LocallyOfFiniteType X.hom → ∀ x : X.left, X.hom x = closedPoint R → IsClosed ({x} : Set X.left) → IsFinite (X.left.fromSpecResidueField x ≫ X.hom) := by
  intro R _ _ X hX x hx hc
  haveI := hX
  haveI := isClosed_singleton_iff_isClosedImmersion.mp hc
  have hf : LocallyOfFiniteType (X.left.fromSpecResidueField x ≫ X.hom) := inferInstance
  have hpt : ∀ p : Spec (X.left.residueField x), (X.left.fromSpecResidueField x ≫ X.hom) p = closedPoint R := by
    intro p
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hx]
  rw [← Spec.map_preimage (X.left.fromSpecResidueField x ≫ X.hom)] at hf hpt ⊢
  rw [IsFinite.SpecMap_iff]
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hf
  generalize Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom) = φ at hf hpt ⊢
  let K := X.left.residueField x
  let p0 : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  have hker : RingHom.ker φ.hom = maximalIdeal R := by
    have h1 := congrArg PrimeSpectrum.asIdeal (hpt p0)
    have h2 : (Spec.map φ).base p0 = PrimeSpectrum.comap φ.hom p0 := rfl
    rw [show (Spec.map φ) p0 = (Spec.map φ).base p0 from rfl, h2] at h1
    have h3 : Ideal.comap φ.hom ⊥ = (closedPoint R).asIdeal := by simpa [p0] using h1
    exact h3
  let k := ResidueField R
  let ψ : k →+* K := Ideal.Quotient.lift (maximalIdeal R) φ.hom (fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact ha)
  have hφ : φ.hom = ψ.comp (residue R) := by
    ext a; rfl
  rw [hφ] at hf ⊢
  have hψ : ψ.FiniteType := RingHom.FiniteType.of_comp_finiteType hf
  letI : Algebra k K := ψ.toAlgebra
  haveI : Algebra.FiniteType k K := hψ
  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  have hψf : ψ.Finite := this
  exact hψf.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFromSpecResidueFieldCompOfIsClosedOfClosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Over (Sp R)), LocallyOfFiniteType X.hom → ∀ x : X.left, X.hom x = closedPoint R → IsClosed ({x} : Set X.left) → IsFinite (X.left.fromSpecResidueField x ≫ X.hom) := by
  first | exact @GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint | exact GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint | (intros; apply GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint <;> assumption)
end
end
