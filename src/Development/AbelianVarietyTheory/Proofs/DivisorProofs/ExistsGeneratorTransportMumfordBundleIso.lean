module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialLocusRigidifiedBundleClosedSeesawStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenTransport

section Nest

variable {X X' Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (X' ⟶ X)} {ε : K → ℤ} {p : Y ⟶ X'}

theorem trF_nest (r : Z ⟶ Y) (z : Z) (j j' : PUnit.{1} → K → L.ι)
    (hj : (r ≫ p) z ∈ LB.wchart L φ (j PUnit.unit)) (hj' : (r ≫ p) z ∈ LB.wchart L φ (j' PUnit.unit)) :
    trF (L := LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1) r z j j' =
      trF (fun k => p ≫ φ k) (fun k => - ε k) r z (j PUnit.unit) (j' PUnit.unit) := by
  unfold trF
  refine (Fintype.prod_unique _).trans ?_
  refine (zpow_neg_one _).trans ?_
  refine (congrArg (·⁻¹) (gm_linComb L φ ε (r ≫ p) z _ _ hj hj')).trans ?_
  simp only [← Finset.prod_inv_distrib, zpow_neg, Category.assoc]

theorem mem_nest {y : Y} {j : PUnit.{1} → K → L.ι} :
    y ∈ LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) j ↔
      y ∈ LB.wchart L (fun k => p ≫ φ k) (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 h PUnit.unit) k,
    fun h => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k⟩

theorem exists_nest (t : LB.Gen (LB.LinComb L (fun k => p ≫ φ k) (fun k => - ε k))) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1)), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => p ≫ φ k) j →
        gm r z (LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j)) (a.s fun _ => j) =
          gm r z (LB.wchart L (fun k => p ≫ φ k) j) (t.s j) := by
  refine ⟨⟨fun j => res (fun _ hy => mem_nest.1 hy) (t.s (j PUnit.unit))⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z j hj => gm_res r z _ (mem_nest.2 hj) _⟩
  refine (gm_res _ y _ hj _).trans ((gen_trans ht (𝟙 Y) y (mem_nest.1 hj) (mem_nest.1 hj')).trans
    (congrArg₂ (· * ·) (trF_nest (𝟙 Y) y j j' (Set.mem_iInter.1 hj PUnit.unit)
      (Set.mem_iInter.1 hj' PUnit.unit)).symm (gm_res _ y _ hj' _).symm))

theorem exists_unnest (a : LB.Gen (LB.LinComb (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1)))
    (ha : a.IsGen) : ∃ t : LB.Gen (LB.LinComb L (fun k => p ≫ φ k) (fun k => - ε k)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => p ≫ φ k) j →
        gm r z (LB.wchart L (fun k => p ≫ φ k) j) (t.s j) =
          gm r z (LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j)) (a.s fun _ => j) := by
  have mk : ∀ {y : Y} {j : K → L.ι}, y ∈ LB.wchart L (fun k => p ≫ φ k) j →
      y ∈ LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j) := fun h => mem_nest.2 h
  refine ⟨⟨fun j => res (fun _ hy => mk hy) (a.s fun _ => j)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z j hj => gm_res r z _ hj _⟩
  refine (gm_res _ y _ hj _).trans ((gen_trans ha (𝟙 Y) y (mk hj) (mk hj')).trans
    (congrArg₂ (· * ·) (trF_nest (𝟙 Y) y (fun _ => j) (fun _ => j') (Set.mem_iInter.1 (mk hj) PUnit.unit)
      (Set.mem_iInter.1 (mk hj') PUnit.unit)) (gm_res _ y _ hj' _).symm))

end Nest


open GlobalTheory.PrimCocycle in
theorem prod_neg_lam {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (x y : T ⟶ B)
    {U : Type} [CommGroup U] (k : (T.left ⟶ B.left) → U) :
    ∏ I, k ((lift x y).left ≫ lamφ B I) ^ (- lamε I) = ∏ i, k (lamPts x y i) ^ negε i := by
  have a := prod_lam x y (fun q => (k q)⁻¹)
  have b := Wit.prod_neg_lamPts x y (fun q => (k q)⁻¹)
  simp only [inv_inv, Category.id_comp] at a b
  rw [b, ← a]
  simp only [zpow_neg, inv_zpow]


open GlobalTheory.PrimCocycle in
theorem gen_transport : ∀ (SB SC : Scheme.{0}) (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (M : LB B.left) (N : LB C.left), M.IsLB → N.IsLB → ∀ (m : (G2 B).left ⟶ (G2 C).left) (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen → ∀ (T : Over SB) (T₀ : Over SC) (x y : T ⟶ B) (x₀ y₀ : T₀ ⟶ C) (h : T.left ⟶ T₀.left), (lift x y).left ≫ m = h ≫ (lift x₀ y₀).left → ∀ t₀ : LB.Gen (LB.LinComb N (lamPts x₀ y₀) negε), t₀.IsGen → ∃ u : LB.Gen (LB.LinComb M (lamPts x y) negε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good N z J → Good M z J' → val u r z J' = lamVal w (r ≫ (lift x y).left) z J J' * val t₀ (r ≫ h) z J := by
  intro SB SC B _ _ C _ _ M N hM hN m w hw T T₀ x y x₀ y₀ h hm t₀ ht₀
  have lM : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have lN : (abelian₂ C N).IsLB := DVR.linComb_isLB _ hN _ _
  obtain ⟨t₁, h₁, v₁⟩ := exists_gen hN (φ' := fun I => (lift x₀ y₀).left ≫ lamφ C I) (ε' := fun I => - lamε I)
    (fun U _ k => (prod_neg_lam x₀ y₀ k).symm) t₀ ht₀
  obtain ⟨t₂, h₂, v₂⟩ := exists_nest t₁ h₁
  obtain ⟨t₃, h₃, v₃⟩ := DegPull.exists_pmaps (L := abelian₂ C N) (L' := abelian₂ B M) ((isGen_iff w).1 hw) lN lM
    (φ' := fun _ : PUnit.{1} => (lift x y).left) h (fun _ => hm) t₂ h₂
  obtain ⟨t₄, h₄, v₄⟩ := exists_unnest (L := M) (φ := lamφ B) (ε := lamε) t₃ h₃
  obtain ⟨u, hu, vu⟩ := exists_gen hM (fun U _ k => prod_neg_lam x y k) t₄ h₄
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  have e : ∀ I, (r ≫ h) ≫ (lift x₀ y₀).left ≫ lamφ C I = (r ≫ (lift x y).left) ≫ m ≫ lamφ C I := fun I => by
    rw [Category.assoc, Category.assoc, ← Category.assoc h, ← hm, Category.assoc]
  have E := v₃ Z r z (fun _ I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I))
    (fun _ I => J' ((r ≫ (lift x y).left) ≫ lamφ B I))
    (fun _ => Set.mem_iInter.2 fun I => hJ ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I))
    (fun _ => Set.mem_iInter.2 fun I => hJ' ((r ≫ (lift x y).left) ≫ lamφ B I))
  rw [Fintype.prod_unique, zpow_neg_one] at E
  have a := v₂ Z (r ≫ h) z (fun I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)) (Set.mem_iInter.2 fun I => by
    have := hJ ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)
    have e' := congrArg (fun q : Z ⟶ C.left => q z) (e I)
    exact (congrArg (· ∈ N.U _) e').mpr this)
  have b := v₄ Z r z (fun I => J' ((r ≫ (lift x y).left) ≫ lamφ B I))
    (Set.mem_iInter.2 fun I => hJ' ((r ≫ (lift x y).left) ≫ lamφ B I))
  rw [vu Z r z J' hJ', ← v₁ Z (r ≫ h) z J hJ,
    val_of t₄ r z J' (fun I => J' ((r ≫ (lift x y).left) ≫ lamφ B I)) (fun I => by rw [Category.assoc]),
    val_of t₁ (r ≫ h) z J (fun I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)) (fun I => by rw [e]), b, ← a]
  exact (mul_inv_cancel_left _ _).symm.trans (congrArg (_ * ·) E.symm)

end GlobalTheory.GenTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_transport_mumfordBundleIso : ∀ (SB SC : Scheme.{0}) (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (M : LB B.left) (N : LB C.left), M.IsLB → N.IsLB → ∀ (m : (G2 B).left ⟶ (G2 C).left) (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen → ∀ (T : Over SB) (T₀ : Over SC) (x y : T ⟶ B) (x₀ y₀ : T₀ ⟶ C) (h : T.left ⟶ T₀.left), (lift x y).left ≫ m = h ≫ (lift x₀ y₀).left → ∀ t₀ : LB.Gen (LB.LinComb N (lamPts x₀ y₀) negε), t₀.IsGen → ∃ u : LB.Gen (LB.LinComb M (lamPts x y) negε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good N z J → Good M z J' → val u r z J' = lamVal w (r ≫ (lift x y).left) z J J' * val t₀ (r ≫ h) z J := by
  first | exact @GlobalTheory.GenTransport.gen_transport | exact GlobalTheory.GenTransport.gen_transport | (intros; apply GlobalTheory.GenTransport.gen_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPresentationEndomorphismsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPresentationEndomorphismsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc

theorem sharpOver_pullback_end : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left) (c : SiegPre g n ζ (u ≫ F.s)), SiegPB c F.univ u → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ c.A)), ∃! x : T₁ ⟶ P.A, ∀ a, x ≫ pr a = y a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∃ c' : SiegPre g n ζ ((f ≫ u) ≫ F.s), SiegPB c' F.univ (f ≫ u) ∧ ∃ pr' : Fin 8 → (P'.A ⟶ c'.A), (∀ a, IsMonHom (pr' a)) ∧ (∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a) ∧ LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) ∧ ∀ (b : P.A ⟶ P.A) (k : Fin 8 → Fin 8 → ℤ), (∀ a, b ≫ pr a = (List.ofFn fun v => pr v ^ k a v).prod) → ∃ b' : P'.A ⟶ P'.A, (∀ a, b' ≫ pr' a = (List.ofFn fun v => pr' v ^ k a v).prod) ∧ b'.left ≫ φ = φ ≫ b.left := by
  intro g n o _ ζ F W T T' P P' u f φ c hc pr hpr huniv hbun hφ hL
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n o ζ T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c (by rw [Category.assoc])
  have hc'u : SiegPB c' F.univ (f ≫ u) := GlobalTheory.SiegelPullComp.pb_comp hc hc'
  obtain ⟨ψ, ψ₂, hψ, hsq, hw, -⟩ := hc'
  have hp := hψ.1
  have hφp := hφ.1
  have wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let pr' : Fin 8 → (P'.A ⟶ c'.A) := fun a =>
    Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)
  have hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left := fun a => hp.lift_fst _ _ _
  have push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left
      rw [Category.assoc, hpr'ψ, Category.assoc])
  have pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y :=
    fun x y => map_mul (pushHom hψ _) x y
  have pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hψ _ e
  have injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hφ _ e
  have hmon : ∀ a, IsMonHom (pr' a) := fun a => by
    haveI := hpr a
    refine isMonHom_of_mul _ fun T₁ x y => injψ ?_
    rw [push_comp, pmψ, push_comp, push_comp, pmφ]
    exact MonObj.mul_comp _ _ _
  have huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a := by
    intro T₁ y
    obtain ⟨x₀, hx₀, hu₀⟩ := huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))
    let x : T₁ ⟶ P'.A := Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)
    have hx : pushPt hφ.1.w x = x₀ := Over.OverMorphism.ext (hφp.lift_fst _ _ _)
    have key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a) :=
      fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩
    refine ⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩
    exact (hu₀ _ ((key z).1 hz)).trans hx.symm
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A)
      (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2)
      ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))
  have hbun' : LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left)
      (fun ab => W ab.1 ab.2)) := by
    let ε : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
    let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
    let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
    have l0 : (LB.LinComb c.P q ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε
    have l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε
    have l2 : (LB.LinComb (c.P.pull ψ₂) q' ε).IsLB :=
      ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε
    have l3 : (LB.LinComb c'.P q' ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε
    have refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
    have i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε).pull φ) := GlobalTheory.SiegelPullComp.iso_pull φ hbun
    have i3 : LBIso ((LB.LinComb c.P q ε).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      LBIso.chartPull (chartPullOut c.P q ε φ _ fun _ => rfl) (chartPullId _) refl1
    have i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb (c.P.pull ψ₂) q' ε) :=
      LBIso.chartPull (chartPullId _)
        (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
    have i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε) (LB.LinComb c'.P q' ε) :=
      GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε
    have h1 := pull_isLB P.isLB φ
    have h2 := pull_isLB l0 φ
    exact LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))
  refine ⟨c', hc'u, pr', hmon, huniv', hbun', ?_⟩
  intro b k hb
  obtain ⟨b', hb', -⟩ := huniv' P'.A (fun a => (List.ofFn fun v => pr' v ^ k a v).prod)
  refine ⟨b', hb', ?_⟩
  let U : Over.mk (P'.A.hom ≫ f) ⟶ P.A := pushPt hφ.1.w (𝟙 P'.A)
  have hU : ∀ v, pushPt hψ.1.w (pr' v) = U ≫ pr v := fun v => by
    rw [← push_comp, Category.id_comp]
  have e : ∀ a, pushPt hφ.1.w b' ≫ pr a = (U ≫ b) ≫ pr a := fun a => by
    rw [← push_comp, hb' a, Category.assoc U b (pr a), hb a]
    have h1 : pushPt hψ.1.w (List.ofFn fun v => pr' v ^ k a v).prod
        = pushHom hψ P'.A (List.ofFn fun v => pr' v ^ k a v).prod := rfl
    have h2 : U ≫ (List.ofFn fun v => pr v ^ k a v).prod = preHom U (List.ofFn fun v => pr v ^ k a v).prod := rfl
    rw [h1, h2, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 1
    apply List.ofFn_inj.mpr
    funext v
    simp only [Function.comp_apply, map_zpow]
    congr 1
    exact hU v
  obtain ⟨x₀, -, hu₀⟩ := huniv (Over.mk (P'.A.hom ≫ f)) (fun a => pushPt hφ.1.w b' ≫ pr a)
  have := (hu₀ _ fun a => rfl).trans (hu₀ _ fun a => (e a).symm).symm
  have := congrArg (fun z => z.left) this
  simpa [U, pushPt] using this

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPresentationEndomorphismsPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPowerPresentation_endomorphisms_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left) (c : SiegPre g n ζ (u ≫ F.s)), SiegPB c F.univ u → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ c.A)), ∃! x : T₁ ⟶ P.A, ∀ a, x ≫ pr a = y a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∃ c' : SiegPre g n ζ ((f ≫ u) ≫ F.s), SiegPB c' F.univ (f ≫ u) ∧ ∃ pr' : Fin 8 → (P'.A ⟶ c'.A), (∀ a, IsMonHom (pr' a)) ∧ (∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a) ∧ LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) ∧ ∀ (b : P.A ⟶ P.A) (k : Fin 8 → Fin 8 → ℤ), (∀ a, b ≫ pr a = (List.ofFn fun v => pr v ^ k a v).prod) → ∃ b' : P'.A ⟶ P'.A, (∀ a, b' ≫ pr' a = (List.ofFn fun v => pr' v ^ k a v).prod) ∧ b'.left ≫ φ = φ ≫ b.left := by
  first | exact @GlobalTheory.Poinc.sharpOver_pullback_end | exact GlobalTheory.Poinc.sharpOver_pullback_end | (intros; apply GlobalTheory.Poinc.sharpOver_pullback_end <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBal

section Alg

variable {r : ℕ} {U : Type} [CommGroup U]

theorem prod_theta (a b c : Vec r) (F : Vec r → U) :
    ∏ v ∈ (theta a b c).support, F v ^ theta a b c v =
      F (a + b + c) * (F (a + b))⁻¹ * (F (a + c))⁻¹ * (F (b + c))⁻¹ * F a * F b * F c * (F 0)⁻¹ := by
  have h0 : ∀ v, F v ^ (0 : ℤ) = 1 := fun v => zpow_zero _
  have hadd : ∀ v (m n : ℤ), F v ^ (m + n) = F v ^ m * F v ^ n := fun v m n => zpow_add _ _ _
  change (theta a b c).prod (fun v n => F v ^ n) = _
  simp only [theta, sub_eq_add_neg, ← Finsupp.single_neg, Finsupp.prod_add_index' h0 hadd]
  simp only [Finsupp.prod_single_index (h := fun v (n : ℤ) => F v ^ n) (h0 _), zpow_one, zpow_neg]

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecHom_add (T : Tens D D' W) (u v : Vec r) : vecHom T (u + v) = vecHom T u * vecHom T v := by
  simp only [vecHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem vecHom_zero (T : Tens D D' W) : vecHom T 0 = 1 := by
  simp only [vecHom, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]

theorem vecLat_add (T : Tens D D' W) (u v : Vec r) (y y' : D'.X) :
    vecLat T (u + v) y y' = vecLat T u y y' + vecLat T v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem vecLat_zero (T : Tens D D' W) (y y' : D'.X) : vecLat T 0 y y' = 0 := by
  simp only [vecLat, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

theorem comp_vecHom (T : Tens D D' W) {Z : Over (Spec (CommRingCat.of R))} (p q : Z ⟶ D'.P.A) (v : Vec r) :
    lift p q ≫ vecHom T v = (∏ k, (p ≫ T.pr k) ^ v (Sum.inl k)) * ∏ k, (q ≫ T.pr k) ^ v (Sum.inr k) := by
  have e := (preHom (G := D.P.A) (lift p q)).map_mul (∏ k, (fst D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inl k))
    (∏ k, (snd D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inr k))
  simp only [map_prod, map_zpow] at e
  rw [vecHom]
  simpa only [preHom, MonoidHom.mk'_apply, lift_fst_assoc, lift_snd_assoc] using e

theorem zero_vecHom (T : Tens D D' W) (v : Vec r) : lift η[D'.P.A] η[D'.P.A] ≫ vecHom T v = 1 := by
  have h : ∀ k, η[D'.P.A] ≫ T.pr k = 1 := fun k => by
    haveI := T.pr_hom k
    rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  simp only [comp_vecHom, h, one_zpow, Finset.prod_const_one, _root_.mul_one]

def cPHom (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) : Multiplicative D.X →* (T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => DVR.cP D T x.toAdd) fun a b => DVR.cPoint_add D T a.toAdd b.toAdd

theorem pt_vecHom (T : Tens D D' W) (y y' : D'.X) (v : Vec r) :
    lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y') ≫ vecHom T v = DVR.cP D (TK R) (vecLat T v y y') := by
  have hp : ∀ x k, DVR.cP D' (TK R) x ≫ T.pr k = cPHom D (TK R) (Multiplicative.ofAdd (T.xe x k)) := fun x k => by
    simp only [DVR.cP, Category.assoc, T.c_pr]; rfl
  rw [comp_vecHom, show DVR.cP D (TK R) (vecLat T v y y') = cPHom D (TK R) (Multiplicative.ofAdd (vecLat T v y y')) from rfl]
  simp only [hp, vecLat, ofAdd_add, ofAdd_sum, ofAdd_zsmul, map_mul, map_prod, map_zpow]

theorem cubV_psi (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (p q s : D.X) :
    cubV D.cub (T := TK R) z J (DVR.cP D _ p) (DVR.cP D _ q) (DVR.cP D _ s) =
      (val (D.psi (p + q + s)) (𝟙 _) z J)⁻¹ * val (D.psi (p + q)) (𝟙 _) z J * val (D.psi (p + s)) (𝟙 _) z J *
        val (D.psi (q + s)) (𝟙 _) z J * (val (D.psi p) (𝟙 _) z J)⁻¹ * (val (D.psi q) (𝟙 _) z J)⁻¹ *
        (val (D.psi s) (𝟙 _) z J)⁻¹ * val (D.psi 0) (𝟙 _) z J := by
  have t := DVR.tauK_mul hJ hB p q s
  have t0 := GlobalTheory.TauBalElem.tau_zero_left hB hJ 0
  rw [GlobalTheory.TauBalBox.tau_val D hJ, GlobalTheory.TauBalBox.tau_val D hJ, GlobalTheory.TauBalBox.tau_val D hJ] at t
  rw [GlobalTheory.TauBalBox.tau_val D hJ, add_zero] at t0
  apply Additive.ofMul.injective
  have t' := congrArg Additive.ofMul t
  have t0' := congrArg Additive.ofMul t0
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at t' t0' ⊢
  linear_combination (norm := abel) t' + t0'

theorem triv_theta : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), D.TauBimult → ∀ a b c : GlobalTheory.TensBal.Vec r, GlobalTheory.TensBal.Triv T (GlobalTheory.TensBal.theta a b c) := by
  intro R _ _ D D' r W T hB a b c
  have hF : FormEq (fun I => (lift (vecHom T a) (lift (vecHom T b) (vecHom T c))).left ≫ thφ D.P.A (x3 D.P.A) I) thε
      (fun v : (theta a b c).support => (vecHom T v.1).left) (fun v => theta a b c v.1) := fun U _ h => by
    refine (prod_cub (vecHom T a) (vecHom T b) (vecHom T c) h).trans ?_
    rw [Finset.prod_coe_sort (theta a b c).support (fun v => h (vecHom T v).left ^ theta a b c v), prod_theta,
      vecHom_add, vecHom_add, vecHom_add, vecHom_add, vecHom_zero]
  obtain ⟨Ξ, hΞ, hv⟩ := exists_gen D.P.isLB hF
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (vecHom T a) (lift (vecHom T b) (vecHom T c))).left)
    (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)
  refine ⟨Ξ, hΞ, fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · refine (hv _ _ z J hJ).trans ((val_cub D.cub (lift η[D'.P.A] η[D'.P.A]) hJ _ _ _).trans ?_)
    rw [zero_vecHom, zero_vecHom, zero_vecHom]
    exact (isCub_cubV D.cub hJ).face _ _
  · refine (hv _ _ z J hJ).trans ((val_cub D.cub (lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y')) hJ _ _ _).trans ?_)
    rw [pt_vecHom, pt_vecHom, pt_vecHom, cubV_psi hB hJ]
    simp only [zpow_neg, ← inv_zpow]
    rw [prod_theta (F := fun v => (val (D.psi (vecLat T v y y')) (𝟙 _) z J)⁻¹)]
    rw [vecLat_add T (a + b) c, vecLat_add T a b, vecLat_add T a c, vecLat_add T b c, vecLat_zero]
    simp only [inv_inv]

end GlobalTheory.TensBal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStronglyTrivial_cubicalThetaFinsupp_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), D.TauBimult → ∀ a b c : GlobalTheory.TensBal.Vec r, GlobalTheory.TensBal.Triv T (GlobalTheory.TensBal.theta a b c) := by
  first | exact @GlobalTheory.TensBal.triv_theta | exact GlobalTheory.TensBal.triv_theta | (intros; apply GlobalTheory.TensBal.triv_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLengthLowerBoundQuotient
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovHt.DividedNum

section Point

open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem zBase_pow_le_lenT {PP A : ℝ} (h : HostNum D L PP A 1) (hw : WtNum p i PP) :
    zBase L ^ 24 ≤ (lenT p i PP : ℝ) := by
  have m2 := D.R.two_le_m
  have k3 := D.R.m_add_three_le_k
  have f8 := h.f8
  have hDd : (1 : ℝ) ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact_mod_cast Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hkm : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hL : (0 : ℝ) ≤ L.sc.L := by linarith [h.big.2.1]
  have hZ : 0 ≤ zBase L := by unfold zBase; positivity
  have hP : zBase L ^ 24 ≤ PP ^ 2 := by
    rw [show (24 : ℕ) = 12 * 2 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h.ppLow 2
  have hPP : 0 ≤ PP ^ 2 := sq_nonneg _
  have h1 : PP ^ 2 ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    rw [le_div_iff₀ hm]
    have a : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := one_le_pow₀ hDd
    have b : PP ^ 2 * D.R.m ≤ PP ^ 2 * D.R.k := mul_le_mul_of_nonneg_left hkm hPP
    have c : PP ^ 2 * D.R.k ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * D.R.k :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hPP a) (by linarith)
    linarith
  exact hP.trans (h1.trans (Nat.le_ceil _))

theorem at_point {PP A : ℝ} (h : HostNum D L PP A 1) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m) :
    zBase L ^ 24 ≤ (lenT p i PP : ℝ) ∧ ∀ u1, Quo p i PP u1 →
      lenT p i PP * GlobalTheory.CovHt.l1 u1 ≤ 834 * unitE p ∧
      ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b := by
  refine ⟨zBase_pow_le_lenT p i h hw, fun u1 hq => ?_⟩
  obtain ⟨h0, S, eta, hS, he, hP, h4, hh, hH⟩ := hw.hyp hi
  have hW := hH u1
  have hD := (quo_iff p i PP h0 S eta u1).1 hq
  refine ⟨?_, ?_⟩
  · obtain ⟨hp1, hp2⟩ := GlobalTheory.CovHt.BudgetPf.pp_bounds h
    have m2 := D.R.two_le_m
    have k3 := D.R.m_add_three_le_k
    have f8 := h.f8
    have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
    have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have hb : 0 < L.sc.b := Real.exp_pos _
    have hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by rw [← hw.card, Nat.card_eq_fintype_card]
    have hN : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r := by rw [hw.sig.2.2]
    have hT : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
    have fr : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ PP := by
      refine le_trans ?_ hp1
      have f2 : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 := le_self_pow₀ hf (by norm_num)
      have r2 : (D.R.r : ℝ) ^ 2 ≤ (D.R.r : ℝ) ^ 5 := pow_le_pow_right₀ hr (by norm_num)
      gcongr
    have rr : (D.R.r : ℝ) ^ 2 ≤ PP := le_trans (le_mul_of_one_le_left (by positivity) hf) fr
    have r1 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 2 := le_self_pow₀ hr (by norm_num)
    have hPP : 1 ≤ PP := by nlinarith
    obtain ⟨a1, -, -⟩ := GlobalTheory.MeanTop.divided_weight_size _ _ _ hW hD
    have a3 := GlobalTheory.CovHt.BudgetPf.l1_u_le _ hW hS
    have e1 : (dat p i).p + (dat p i).q - (wtsAt p i PP h0 S eta u1).kc = D.R.m := by
      show (dat p i).p + (dat p i).q - (D.R.k - 1) = _
      rw [hw.sig.2.2]; unfold Ranks.r; omega
    rw [e1, hcard, hN] at a3
    rw [hcard, hN] at a1
    change _ ≤ D.R.f * (D.R.r * S + D.R.m * (2 * (4 * L.sc.b))) at a3
    change (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ _ + D.R.f * D.R.r * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r) at a1
    have c1 : ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 := by
      exact_mod_cast (cZero_spec D ((i : ℕ) + 1)).2.2
    have c2 : (D.R.r : ℝ) * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r) ≤ 26 * L.sc.b := by
      have := mul_le_mul_of_nonneg_left c1 (by linarith : (0 : ℝ) ≤ D.R.r)
      nlinarith
    obtain ⟨τ⟩ : Nonempty (Psi p.T.Q.H) := by
      rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card, hw.card]; omega
    have w1 : L.sc.w'' D.R.n ≤ 8 * L.sc.b := by
      have h1 := hw.low τ
      have h2 : (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ 4 * L.sc.b := by
        unfold anchor
        split_ifs
        · exact (le_abs_self _).trans (hw.up τ _)
        · push_cast; linarith
      linarith
    have s1 : (D.R.r : ℝ) * S ≤ 800 * L.sc.b := by
      have h1 : (D.R.r : ℝ) * S ≤ PP * S := mul_le_mul_of_nonneg_right (by linarith) hS
      nlinarith [mul_nonneg (by linarith : 0 ≤ PP) he]
    have bm : L.sc.b ≤ D.R.m * L.sc.b := le_mul_of_one_le_left hb.le hm
    have t2 : (D.R.f : ℝ) * ((D.R.r * S + D.R.m * (2 * (4 * L.sc.b))) + D.R.r * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r)) ≤
        D.R.f * (834 * (D.R.m * L.sc.b)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have t3 : (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ 834 * (D.R.f * D.R.m * L.sc.b) := by nlinarith
    have u0 : (D.R.f : ℝ) * D.R.m * L.sc.b ≤ unitE p := by
      rw [hw.unit]
      have hL := h.big.2.1
      have hll := h.big.2.2.2
      have a0 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b := by positivity
      have a1 : (D.R.f : ℝ) * D.R.m * L.sc.b ≤ D.R.f * D.R.m * L.sc.b * L.sc.L :=
        le_mul_of_one_le_right a0 (by linarith)
      have a2 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := le_trans a0 a1
      exact a1.trans (le_mul_of_one_le_right a2 hll)
    show (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ 834 * unitE p
    linarith
  · intro τ a b hab
    obtain ⟨g1, g2, -⟩ := GlobalTheory.MeanTop.divided_gaps _ _ _ hW hD τ a b hab
    have hT1 : 4 * dimFlag (dat p i) + 4 ≤ lenT p i PP := hW.h1
    change ((b : ℕ) ≠ (dat p i).p → (lenT p i PP : ℤ) + dimFlag (dat p i) + 2 + 2 * ((dat p i).p + (dat p i).q : ℕ) ≤ u1 τ a - u1 τ b) at g1
    change ((b : ℕ) = (dat p i).p → h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) ∧ _) at g2
    by_cases hb : (b : ℕ) = (dat p i).p
    · have k := (g2 hb).1
      have hT0 : (1 : ℤ) ≤ lenT p i PP := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
      nlinarith
    · have k := g1 hb
      have : (0 : ℤ) ≤ (dimFlag (dat p i) : ℤ) + 2 + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by positivity
      linarith

end Point

end GlobalTheory.CovHt.DividedNum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartThetaSystemUnitaryModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartThetaSystemUnitaryModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.exists_tie_of_uOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (R : Subalgebra X.o₁ X.Ω₁) (P' : PolAV (Sp R)) (u' : Sp (ratHull R) ⟶ Xo.XF cf), spMap (ratHull R).val.toRingHom ≫ u' = X.uΩ → UOver Xo cf P' (toRat R) u' → ∃ (G : Over (Sp (ratHull R))) (_ : GrpObj G) (α : G.left ⟶ P'.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (m : wi.G.left ⟶ G.left) (P₀ : PolAV (Sp X.Ω₁)) (e : P₀.A.left ⟶ wi.G.left), IsGrpPullback G P'.A (spMap (toRat R)) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P'.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ IsGrpPullback wi.G G (spMap (ratHull R).val.toRingHom) m ∧ m ≫ β = wi.β ∧ IsGrpPullback P₀.A X.ρ.P.A (spMap X.S.R.val.toRingHom) (e ≫ wi.α) ∧ IsGrpPullback P₀.A P'.A (spMap R.val.toRingHom) (e ≫ m ≫ α) ∧ LBIso P₀.L (X.ρ.P.L.pull (e ≫ wi.α)) ∧ LBIso P₀.L (P'.L.pull (e ≫ m ≫ α)) := by
  intro E _ _ _ H Dw l Xo cf C X wi R P' u' hc h
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have hb : IsGrpPullback wi.G Xo.univ.t.G (spMap (ratHull R).val.toRingHom ≫ u' ≫ pullback.fst _ _) wi.β :=
    wi.hβ.congr (by rw [← hc, Category.assoc]) rfl
  have w₁ : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (ratHull R).val.toRingHom) ≫ u' ≫ pullback.fst _ _ := by
    rw [Category.assoc]; exact hb.1.w
  have em := hβ.1.lift_fst _ _ w₁
  have hm := hβ.cancel (hb.congr rfl em.symm) (hβ.1.lift_snd _ _ w₁)
  generalize hβ.1.lift _ _ w₁ = m at em hm
  obtain ⟨P₀, φ, hφ, hφL⟩ := exists_pol_baseChange X.ρ.P (spMap X.S.R.val.toRingHom)
  have w₂ : φ ≫ X.ρ.P.A.hom = (P₀.A.hom ≫ 𝟙 _) ≫ spMap X.S.R.val.toRingHom := by
    rw [Category.comp_id]; exact hφ.1.w
  have ee := wi.hα.1.lift_fst _ _ w₂
  have he := wi.hα.cancel (hφ.congr (Category.id_comp _).symm ee.symm) (wi.hα.1.lift_snd _ _ w₂)
  generalize wi.hα.1.lift _ _ w₂ = e at ee he
  subst ee
  have hU := Xo.univ.t.PP.isLB
  refine ⟨G, _, α, β, m, P₀, e, hα, hβ, hL, hm, em, hφ,
    (he.comp (hm.comp hα)).congr ((Category.id_comp _).trans (spMap_val_toRat R)) rfl, hφL, ?_⟩
  have l₁ : LBIso (X.ρ.P.L.pull (e ≫ wi.α)) (Xo.univ.t.PP.L.pull (e ≫ wi.β)) :=
    GenSpread.lbIso_pull_comp _ rfl rfl wi.hL
  have l₂ : LBIso (P'.L.pull (m ≫ α)) (Xo.univ.t.PP.L.pull (m ≫ β)) := GenSpread.lbIso_pull_comp _ rfl rfl hL
  rw [em] at l₂
  have l₃ : LBIso (P'.L.pull (e ≫ m ≫ α)) (Xo.univ.t.PP.L.pull (e ≫ wi.β)) := GenSpread.lbIso_pull_comp _ rfl rfl l₂
  exact LBIso.trans P₀.isLB (pull_isLB X.ρ.P.isLB _) (pull_isLB P'.isLB _) hφL
    (LBIso.trans (pull_isLB X.ρ.P.isLB _) (pull_isLB hU _) (pull_isLB P'.isLB _) l₁ l₃.symm)


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.UPoinc.exists_urechart_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (ρ'.pt x).left)) ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
  intro E _ _ _ H Dw _hpq l Xo cf C X wi w hw
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hu₀⟩ := GlobalTheory.UPoinc.ChartAt.exists_affine_chart_ratLift E H Dw l Xo cf C X w hw
  obtain ⟨U₁, h₁, P₁, _hU₁₀, hU₁a, hwU₁, hP₁⟩ := GlobalTheory.UPoinc.LocSpread.exists_uOver_ringOn E H Dw l Xo cf C X U₀ u₀ w hU₀a hwU₀ hw
  have hN : 1 ≤ X.S.N := by have := X.S.N_ge; omega
  obtain ⟨U, h, P', φ, _hUU₁, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.Poinc.exists_univBasis_affineChart X.o₁ X.Ω₁ X.M U₁ w hU₁a hwU₁ P₁ X.S.N hN
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  let u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf :=
    spMap (Subalgebra.inclusion (ratHull_mono (h₁.trans h))).toRingHom ≫ u₀
  have hP' : UOver Xo cf P' (toRat (X.M.ringOn U)) u' := by
    refine (uOver_baseChange_iff hφ hφL (toRat _)).2 ?_
    have := hP₁.comp (Subalgebra.inclusion (ratHull_mono h)).toRingHom
    have e : spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫
        spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom ≫ u₀ = u' := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e] at this
    exact this
  have hcomp : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨G, _, α, β, m, P₀, e, hα, hβ, hαβ, hm, hmβ, ha, ha', hL, hL'⟩ :=
    GlobalTheory.UPoinc.exists_tie_of_uOver E H Dw l Xo cf C X wi (X.M.ringOn U) P' u' hcomp hP'
  have hg' : P'.g = X.S.g :=
    (GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ P' P₀ _ _ ha').symm.trans
      ((GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ X.ρ.P P₀ _ _ ha).trans X.ρ.g_eq)
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.Poinc.hypS_of_generic_ringOn X.o₁ X.Ω₁ X.M U hUa hne X.normal X.S.R X.ρ.P P' P₀ _ _ _ ha ha' hL hL' X.ρ.hypS

  obtain ⟨⟨hLw, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI := RatModel.isFractionRing_ringOn hUa hne
  haveI := TorsExtend.isIntegrallyClosed_ringOn X.M ((isNormalScheme_iff_pred _).1 X.normal) hUa hne
  haveI := ArithBase.ded (o := X.o₁) (Ω := X.Ω₁)
  have fg : (X.M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ X.M U hUa hne
  haveI : IsNoetherianRing (X.M.ringOn U) := isNoetherianRing_of_fg fg
  have hn : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (le_trans one_le_two X.S.N_ge)
  have hu : IsUnit ((X.S.r * X.S.N : ℕ) : X.M.ringOn U) := by
    have := X.S.unit.map (algebraMap X.o₁ (X.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', hadd, hbij, h₃, hw0⟩ := TorsExtend.exists_labelled hLw X.S.R.val.toRingHom X.ρ.P P' P₀ _ _ ha ha' hL hL'
    hn hu (M := X.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X.ρ.pt X.ρ.pt_add X.ρ.pt_bij
  have hweil : ∀ x y (c : (X.M.ringOn U)ˣ), (c : (X.M.ringOn U)) = algebraMap X.o₁ (X.M.ringOn U)
      (X.S.ζ ^ (X.S.r * X.S.N * (eStd X.S.g _ x y).val)) →
      WeilIs P'.A P'.L (X.S.r * X.S.N : ℕ) (pt' x) (pt' y) (unitOn c) := fun x y c hc => by
    obtain ⟨c₀, hc₀⟩ := ((X.S.prim.isUnit (by positivity)).pow (X.S.r * X.S.N * (eStd X.S.g _ x y).val)).map
      (algebraMap X.o₁ X.S.R)
    refine h₃ x y c₀ c ?_ (X.ρ.weil x y c₀ hc₀)
    rw [hc₀, hc]
    rfl
  have frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  have hQ : (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P'.A.left)
      (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G P'.A (spMap (toRat (X.M.ringOn U))) α ∧
        IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P'.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
        (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧
          m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left,
            w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
            w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (pt' x).left)) ∧
      ∃ a'' : P₀.A.left ⟶ P'.A.left, IsGrpPullback P₀.A P'.A (spMap (X.M.ringOn U).val.toRingHom) a'' ∧
        LBIso P₀.L (P'.L.pull a'') ∧
        ∀ x, ∃ w0 : Sp X.Ω₁ ⟶ P₀.A.left, w0 ≫ e ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w0 ≫ a'' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt' x).left := by
    refine ⟨⟨G, inferInstance, α, β, hα, hβ, hαβ, m, hm, hmβ, fun x => ?_⟩, _, ha', hL', hw0⟩
    obtain ⟨w0, h₁, h₂⟩ := hw0 x
    exact ⟨w0 ≫ e, by rw [Category.assoc]; exact h₁, by rw [Category.assoc]; exact h₂⟩
  obtain ⟨c₀, hc, hthm, hevm, ρ', ⟨hU', a'', q₂, q₃, q₅⟩, hi₀⟩ := GlobalTheory.ThetaExtend.exists_real_rechart
    GlobalTheory.abelianSchemeLaws_all.1 X.S X.ρ (X.M.ringOn U) fg frac P' P₀ _ _ pt' th b ha ha' hL hL' hg' hyp hadd hbij hweil
    hw0 hth hb
    (fun P pt => (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P.A.left)
      (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G P.A (spMap (toRat (X.M.ringOn U))) α ∧
        IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
        (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧
          m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left,
            w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
            w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (pt x).left)) ∧
      ∃ a'' : P₀.A.left ⟶ P.A.left, IsGrpPullback P₀.A P.A (spMap (X.M.ringOn U).val.toRingHom) a'' ∧
        LBIso P₀.L (P.L.pull a'') ∧
        ∀ x, ∃ w0 : Sp X.Ω₁ ⟶ P₀.A.left, w0 ≫ e ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w0 ≫ a'' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left) hQ
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', u', hUa, hwU, ⟨P₀, e ≫ wi.α, a'', ha, q₂, hL, q₃, q₅⟩, hi₀, hU', hcomp⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartThetaSystemUnitaryModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_chart_thetaSystem_unitary_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (ρ'.pt x).left)) ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
  first | exact @GlobalTheory.UPoinc.exists_urechart_affine | exact GlobalTheory.UPoinc.exists_urechart_affine | (intros; apply GlobalTheory.UPoinc.exists_urechart_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemOfValNonnegOverCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemOfValNonnegOverCompleteDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntOverCdvr

open IsLocalRing

theorem isIntegralElem_of_val_nonneg : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v → ∀ z : F, 0 ≤ v z → ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).IsIntegralElem z := by
  intro V _ _ _ hV ϖ hϖ F _ _ _ v hv z hz
  obtain ⟨hdvr, hcomp, hchar⟩ := hV
  let K := FractionRing V
  letI : Algebra V F := ((algebraMap K F).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).mpr
    ((algebraMap K F).injective.comp (IsFractionRing.injective V K))
  haveI : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mpr inferInstance
  obtain ⟨W, hW, -, -, hfin, -, hloc, hs, -⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V F {z}
  haveI := hfin

  have hVnn : ∀ r : V, 0 ≤ v (algebraMap V F r) := fun r =>
    GlobalTheory.FiniteDVRValuation.val_nonneg hϖ hv r

  let S : ValuationSubring F := GlobalTheory.FiniteDVRValuation.nonnegSubring v (RingHom.id F)
  have hWnn : ∀ w ∈ W, 0 ≤ v w := by
    intro w hw
    have hint : IsIntegral V w := (Algebra.IsIntegral.isIntegral (R := V) (⟨w, hw⟩ : W)).map W.val
    let φ : V →+* S := (algebraMap V F).codRestrict S (fun r => hVnn r)
    have hS : (algebraMap S F).IsIntegralElem w := RingHom.IsIntegralElem.of_comp (f := φ) hint
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := F)).1 hS
    rw [← hy]
    exact y.2

  have hϖpos : 0 < v (algebraMap V F ϖ) := by
    obtain ⟨n, hn, hu⟩ := GlobalTheory.FiniteDVRValuation.exists_nat_val hϖ hv hϖ.ne_zero
    have hn0 : n ≠ 0 := fun h => hϖ.not_isUnit (hu h)
    change 0 < v (algebraMap K F (algebraMap V K ϖ))
    rw [hn]
    exact_mod_cast Nat.pos_of_ne_zero hn0

  have hunit : ∀ c : W, v (c : F) = 0 → IsUnit c := by
    intro c hc
    by_contra hnu
    have hinj : Function.Injective (algebraMap V W) := by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective V F
      have := congrArg Subtype.val hab
      simpa using this
    set ϖW : W := algebraMap V W ϖ
    have hϖW0 : ϖW ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    obtain ⟨N, hN⟩ : ∃ N : ℕ, IsDiscreteValuationRing.addVal W ϖW = N := by
      rcases h : IsDiscreteValuationRing.addVal W ϖW with _ | N
      · exact absurd (IsDiscreteValuationRing.addVal_eq_top_iff.1 h) hϖW0
      · exact ⟨N, rfl⟩
    have hc1 : 1 ≤ IsDiscreteValuationRing.addVal W c := by
      rw [ENat.one_le_iff_ne_zero]
      exact fun h => hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    have hdvd : ϖW ∣ c ^ N := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow, hN]
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • IsDiscreteValuationRing.addVal W c := nsmul_le_nsmul_right hc1 N
    obtain ⟨d, hd⟩ := hdvd
    have h1 : v ((c : F) ^ N) = 0 := by rw [AddValuation.map_pow, hc, nsmul_zero]
    have h2 : v ((c : F) ^ N) = v (algebraMap V F ϖ) + v (d : F) := by
      rw [← AddValuation.map_mul]
      congr 1
      have h := congrArg Subtype.val hd
      simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul] at h
      exact h
    have h3 : 0 < v ((c : F) ^ N) := by
      rw [h2]
      exact lt_of_lt_of_le hϖpos (le_add_of_nonneg_right (hWnn d d.2))
    rw [h1] at h3
    exact lt_irrefl _ h3

  obtain ⟨a, ha, b, hb, hb0, hab⟩ := hs z (Finset.mem_singleton_self z)
  have hzW : z ∈ W := by
    let a' : W := ⟨a, ha⟩
    let b' : W := ⟨b, hb⟩
    rcases le_total (IsDiscreteValuationRing.addVal W b') (IsDiscreteValuationRing.addVal W a') with h | h
    · obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h
      have hc' : a = b * c := congrArg Subtype.val hc
      have : z = c := by
        apply mul_left_cancel₀ hb0
        rw [mul_comm, hab, hc']
      rw [this]; exact c.2
    · obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h
      have hc' : b = a * c := congrArg Subtype.val hc
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hb0 (by simpa using hc')
      have hzc : z * c = 1 := by
        apply mul_left_cancel₀ ha0
        calc a * (z * c) = z * (a * c) := by ring
          _ = a * 1 := by rw [← hc', hab, _root_.mul_one]
      have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hzc
      have hvc : v (c : F) = 0 := by
        have hsum : v z + v (c : F) = 0 := by rw [← AddValuation.map_mul, hzc, AddValuation.map_one]
        have hc0 := hWnn c c.2
        refine le_antisymm ?_ hc0
        calc v (c : F) = 0 + v (c : F) := (zero_add _).symm
          _ ≤ v z + v (c : F) := by gcongr
          _ = 0 := hsum
      obtain ⟨u, hu⟩ := hunit c hvc
      have : z = ((u⁻¹ : Wˣ) : W) := by
        have h1 : ((u : W) : F) * (((u⁻¹ : Wˣ) : W) : F) = 1 := by
          rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
        rw [hu] at h1
        calc z = z * ((c : F) * (((u⁻¹ : Wˣ) : W) : F)) := by rw [h1, _root_.mul_one]
          _ = (z * c) * (((u⁻¹ : Wˣ) : W) : F) := by ring
          _ = _ := by rw [hzc, _root_.one_mul]
      rw [this]; exact Subtype.property _

  exact (Algebra.IsIntegral.isIntegral (R := V) (⟨z, hzW⟩ : W)).map W.val

end GlobalTheory.IntOverCdvr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemOfValNonnegOverCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralElem_of_val_nonneg_over_completeDVR : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v → ∀ z : F, 0 ≤ v z → ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).IsIntegralElem z := by
  first | exact @GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg | exact GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg | (intros; apply GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedLocusPullbackLineBundlesIsomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedLocusPullbackLineBundlesIsomorphic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixTrivLocus

theorem lbIso_pull_comp' {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem isoLocus_closed : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (Z₁ : Scheme.{0}) [IsLocallyNoetherian Z₁] (t₁ : Z₁ ⟶ Sp Rg) (A₁ B₁ : Over Z₁) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → RelAmple A L → IsGrpPullback A₁ A t₁ φA₁ → IsGrpPullback B₁ B t₁ φB₁ → IsMonHom Φ₁ → ∃ (Z : Scheme.{0}) (i : Z ⟶ Z₁), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (u : T ⟶ Z₁) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A₁ u ψA → IsGrpPullback B' B₁ u ψB → Φ'.left ≫ ψB = ψA ≫ Φ₁.left → (LBIso (L.pull (ψA ≫ φA₁)) ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ↔ ∃ w : T ⟶ Z, w ≫ i = u) := by
  intro Rg _ A B _ _ L M eA eB Z₁ _ t₁ A₁ B₁ _ _ φA₁ φB₁ Φ₁ hA hB hL hM hgA hgB hamp hpA hpB hΦ
  haveI : IsMonHom Φ₁ := hΦ
  haveI : IsCommMonObj A := hA.comm
  haveI : IsCommMonObj A₁ := GlobalTheory.isCommMonObj_of_grpPullback _ _ A A₁ t₁ φA₁ hpA
  obtain ⟨hA₁, hL₁, hrA₁, haA₁⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ t₁ A A₁ φA₁ L
    hpA hA hL ⟨eA, hgA⟩ hamp
  have hrB₁ : Out.Rigidified B₁ (M.pull φB₁) := GlobalTheory.PolBaseChange.rigidified_pull hpB ⟨eB, hgB⟩
  have hM₁ : (M.pull (Φ₁.left ≫ φB₁)).IsLB := pull_isLB hM _
  have hN : (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁)).IsLB := LB.isLB_div hM₁ hL₁
  have hrN : Out.Rigidified A₁ (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁)) := by
    refine (GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L.pull φA₁) (M.pull (Φ₁.left ≫ φB₁)) (eSec A₁)).1 ?_
    obtain ⟨s, hs⟩ := hrA₁
    obtain ⟨t, ht⟩ := hrB₁
    have e1 : LBIso ((L.pull φA₁).pull (eSec A₁)) ((M.pull φB₁).pull (eSec B₁)) :=
      GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    have hc : eSec A₁ ≫ Φ₁.left = eSec B₁ := congrArg (fun z => z.left) (IsMonHom.one_hom Φ₁)
    have e2 : LBIso ((M.pull φB₁).pull (eSec B₁)) ((M.pull (Φ₁.left ≫ φB₁)).pull (eSec A₁)) :=
      GlobalTheory.HomFixTransport.lbIso_pull_pull hM _ _ _ _ (by rw [← Category.assoc, hc])
    exact LBIso.trans (pull_isLB hL₁ _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM₁ _) e1 e2
  obtain ⟨Z, i, hi, H⟩ := GlobalTheory.T.trivial_locus_rigidified_bundle_closed_seesaw Z₁ A₁ (L.pull φA₁) (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁))
    hA₁ hL₁ haA₁ hN hrN
  refine ⟨Z, i, hi, fun T u A' B' _ _ ψA ψB Φ' hpA' hpB' hc => ?_⟩
  refine Iff.trans ?_ ((GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L.pull φA₁) (M.pull (Φ₁.left ≫ φB₁)) ψA).trans
    (H T u A' ψA hpA'))
  have a1 : LBIso (L.pull (ψA ≫ φA₁)) ((L.pull φA₁).pull ψA) := lbIso_pull_comp' hL φA₁ ψA
  have a2 : LBIso ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ((M.pull (Φ₁.left ≫ φB₁)).pull ψA) :=
    GlobalTheory.HomFixTransport.lbIso_pull_pull hM _ _ _ _ (by rw [← Category.assoc, hc, Category.assoc])
  have h1 := pull_isLB hL (ψA ≫ φA₁)
  have h2 := pull_isLB hL₁ ψA
  have h3 := pull_isLB (pull_isLB hM (ψB ≫ φB₁)) Φ'.left
  have h4 := pull_isLB hM₁ ψA
  exact ⟨fun h => GlobalTheory.HomFixTransport.lbIso_congr h1 h2 h3 h4 (LBIso.symm a1) h a2,
    fun h => GlobalTheory.HomFixTransport.lbIso_congr h2 h1 h4 h3 a1 h (LBIso.symm a2)⟩

end GlobalTheory.HomFixTrivLocus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedLocusPullbackLineBundlesIsomorphicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_locus_pullback_lineBundles_isomorphic : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (Z₁ : Scheme.{0}) [IsLocallyNoetherian Z₁] (t₁ : Z₁ ⟶ Sp Rg) (A₁ B₁ : Over Z₁) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → RelAmple A L → IsGrpPullback A₁ A t₁ φA₁ → IsGrpPullback B₁ B t₁ φB₁ → IsMonHom Φ₁ → ∃ (Z : Scheme.{0}) (i : Z ⟶ Z₁), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (u : T ⟶ Z₁) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A₁ u ψA → IsGrpPullback B' B₁ u ψB → Φ'.left ≫ ψB = ψA ≫ Φ₁.left → (LBIso (L.pull (ψA ≫ φA₁)) ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ↔ ∃ w : T ⟶ Z, w ≫ i = u) := by
  first | (exact @GlobalTheory.HomFixTrivLocus.isoLocus_closed) | (exact GlobalTheory.HomFixTrivLocus.isoLocus_closed) | (intros; apply GlobalTheory.HomFixTrivLocus.isoLocus_closed  <;> assumption)
end
end
