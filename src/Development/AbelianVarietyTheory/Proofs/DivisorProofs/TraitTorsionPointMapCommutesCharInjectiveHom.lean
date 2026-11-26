module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossRelationHomGivesExpansionTermConvolutionRel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionCrossRelationIffOfThetaAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionCrossRelationIffOfThetaAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.CrossTheta₂

theorem sval_comp {X Y Y' Z : Scheme.{0}} {L : LB X} (p : Y' ⟶ X) {k : ℤ}
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k))) (r : Z ⟶ Y) (c : Y ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} {I : (Y ⟶ X) → L.ι} (hI : Good L (r z) I) (hc : I (c ≫ p) = J (r ≫ c ≫ p)) :
    sval s (r ≫ c) z J = (r.stalkMap z).hom (sval s c (r z) I) := by
  rw [sval_of s (r ≫ c) z J (fun _ => I (c ≫ p)) (fun _ => by rw [Category.assoc, hc])]
  exact GlobalTheory.CrossTheta.gs_comp_stalk r c z _ (hI.mem (fun _ : Fin 1 => p) c) _

theorem cross_val {X₁ X₂ Y₁ Y₂ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂) (b : Y₁ ⟶ Y₂) {k k' : ℤ}
    (s₁ s₂ : LB.Sec (LB.LinComb L₂ (fun _ : Fin 1 => p₂) (fun _ => k)))
    (s₁' s₂' : LB.Sec (LB.LinComb L₁ (fun _ : Fin 1 => p₁) (fun _ => k')))
    (H : ∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval s₁ b y J₂ * sval s₂' (𝟙 _) y J₁ = sval s₂ b y J₂ * sval s₁' (𝟙 _) y J₁)
    {Z : Scheme.{0}} (r : Z ⟶ Y₁) (z : Z) {J₁ J₂} (hJ₁ : Good L₁ z J₁) (hJ₂ : Good L₂ z J₂) :
    sval s₁ (r ≫ b) z J₂ * sval s₂' r z J₁ = sval s₂ (r ≫ b) z J₂ * sval s₁' r z J₁ := by
  obtain ⟨I₁, hI₁, e₁⟩ := exists_good L₁ hL₁ (r z) (K := Unit) (fun _ => 𝟙 _ ≫ p₁)
    (fun _ => J₁ (r ≫ 𝟙 _ ≫ p₁)) (fun _ _ _ => rfl) (fun _ => hJ₁ (r ≫ 𝟙 _ ≫ p₁))
  obtain ⟨I₂, hI₂, e₂⟩ := exists_good L₂ hL₂ (r z) (K := Unit) (fun _ => b ≫ p₂)
    (fun _ => J₂ (r ≫ b ≫ p₂)) (fun _ _ _ => rfl) (fun _ => hJ₂ (r ≫ b ≫ p₂))
  have h := congrArg (r.stalkMap z).hom (H (r z) I₁ I₂ hI₁ hI₂)
  rw [map_mul, map_mul, ← sval_comp p₂ s₁ r b z hI₂ (e₂ ()), ← sval_comp p₂ s₂ r b z hI₂ (e₂ ()),
    ← sval_comp p₁ s₁' r (𝟙 _) z hI₁ (e₁ ()), ← sval_comp p₁ s₂' r (𝟙 _) z hI₁ (e₁ ()), Category.comp_id] at h
  exact h

theorem translT_whisker {S : Scheme.{0}} {A₁ A₂ : Over S} [GrpObj A₁] [GrpObj A₂] {T : Over S} (c : A₁ ⟶ A₂)
    [IsMonHom c] (x : T ⟶ A₁) :
    translT A₁ x ≫ T ◁ c = T ◁ c ≫ translT A₂ (x ≫ c) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, whiskerLeft_snd, lift_snd, lift_snd_assoc, ThetaPowOrder.translPt_eq,
      MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc]

theorem cross_act {S : Scheme.{0}} {A₁ A₂ : Over S} [GrpObj A₁] [GrpObj A₂] {L₁ : LB A₁.left} {L₂ : LB A₂.left}
    (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {T : Over S} (c : A₁ ⟶ A₂) [IsMonHom c] {k k' : ℤ}
    (θ : ThetaGrp A₂ L₂ k T) (θ' : ThetaGrp A₁ L₁ k' T) (hp : θ.pt = θ'.pt ≫ c)
    {t₁ t₂ T₁ T₂ : LB.Sec (LPow A₂ L₂ k T)} {t₁' t₂' T₁' T₂' : LB.Sec (LPow A₁ L₁ k' T)}
    (h₁ : IsActOf A₂ L₂ k θ t₁ T₁) (h₂ : IsActOf A₂ L₂ k θ t₂ T₂) (h₁' : IsActOf A₁ L₁ k' θ' t₁' T₁')
    (h₂' : IsActOf A₁ L₁ k' θ' t₂' T₂') :
    (∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval (L := L₂) t₁ (T ◁ c).left y J₂ * sval (L := L₁) t₂' (𝟙 _) y J₁ =
        sval (L := L₂) t₂ (T ◁ c).left y J₂ * sval (L := L₁) t₁' (𝟙 _) y J₁) ↔
    (∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval (L := L₂) T₁ (T ◁ c).left y J₂ * sval (L := L₁) T₂' (𝟙 _) y J₁ =
        sval (L := L₂) T₂ (T ◁ c).left y J₂ * sval (L := L₁) T₁' (𝟙 _) y J₁) := by
  have cc : (T ◁ c).left ≫ (translT A₂ θ.pt).left = (translT A₁ θ'.pt).left ≫ (T ◁ c).left := by
    rw [← Over.comp_left, ← Over.comp_left, hp, translT_whisker]
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A₁).left) (z : Z) {J₁ J₂}, Good L₁ z J₁ → Good L₂ z J₂ →
      (sval (L := L₂) T₁ (r ≫ (T ◁ c).left) z J₂ * sval (L := L₁) T₂' r z J₁ =
        sval (L := L₂) T₂ (r ≫ (T ◁ c).left) z J₂ * sval (L := L₁) T₁' r z J₁ ↔
      sval (L := L₂) t₁ ((r ≫ (translT A₁ θ'.pt).left) ≫ (T ◁ c).left) z J₂ *
          sval (L := L₁) t₂' (r ≫ (translT A₁ θ'.pt).left) z J₁ =
        sval (L := L₂) t₂ ((r ≫ (translT A₁ θ'.pt).left) ≫ (T ◁ c).left) z J₂ *
          sval (L := L₁) t₁' (r ≫ (translT A₁ θ'.pt).left) z J₁) := by
    intro Z r z J₁ J₂ hJ₁ hJ₂
    rw [ThetaPowOrder.act_sval h₁ _ z hJ₂, ThetaPowOrder.act_sval h₂ _ z hJ₂, ThetaPowOrder.act_sval h₁' _ z hJ₁,
      ThetaPowOrder.act_sval h₂' _ z hJ₁, Category.assoc, cc, ← Category.assoc, _root_.mul_mul_mul_comm,
      _root_.mul_mul_mul_comm _ (sval (L := L₂) t₂ _ z J₂), ← Units.val_mul, Units.mul_right_inj]
  constructor
  · intro H y J₁ J₂ hJ₁ hJ₂
    have h := (key (𝟙 _) y hJ₁ hJ₂).2 (cross_val hL₁ hL₂ _ _ _ t₁ t₂ t₁' t₂' H _ y hJ₁ hJ₂)
    rwa [Category.id_comp] at h
  · intro H y J₁ J₂ hJ₁ hJ₂
    have h := (key (translT A₁ θ'.pt⁻¹).left y hJ₁ hJ₂).1 (cross_val hL₁ hL₂ _ _ _ T₁ T₂ T₁' T₂' H _ y hJ₁ hJ₂)
    rwa [← Over.comp_left, ThetaPowOrder.translT_comp, mul_inv_cancel, ThetaPowOrder.translT_one, Over.id_left,
      Category.id_comp] at h

end GlobalTheory.CrossTheta₂

namespace GlobalTheory

theorem crossH_iff_of_isActOf : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j j' : ℕ) (θ : ThetaGrp A₂.A A₂.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A₁.A A₁.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ c → ∀ (t₁ t₂ T₁ T₂ : SecA A₂ F j) (t₁' t₂' T₁' T₂' : SecA A₁ F j'), IsActOf A₂.A A₂.L j θ t₁ T₁ → IsActOf A₂.A A₂.L j θ t₂ T₂ → IsActOf A₁.A A₁.L j' θ' t₁' T₁' → IsActOf A₁.A A₁.L j' θ' t₂' T₂' → (CrossH c t₁ t₂ t₁' t₂' ↔ CrossH c T₁ T₂ T₁' T₂') := by
  intro R _ _ A₁ A₂ F _ _ c hc j j' θ θ' hp t₁ t₂ T₁ T₂ t₁' t₂' T₁' T₂' h₁ h₂ h₁' h₂'
  haveI := hc
  exact CrossTheta₂.cross_act A₁.isLB A₂.isLB c θ θ' hp h₁ h₂ h₁' h₂'

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionCrossRelationIffOfThetaActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSectionCrossRelation_iff_of_thetaAction : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j j' : ℕ) (θ : ThetaGrp A₂.A A₂.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A₁.A A₁.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ c → ∀ (t₁ t₂ T₁ T₂ : SecA A₂ F j) (t₁' t₂' T₁' T₂' : SecA A₁ F j'), IsActOf A₂.A A₂.L j θ t₁ T₁ → IsActOf A₂.A A₂.L j θ t₂ T₂ → IsActOf A₁.A A₁.L j' θ' t₁' T₁' → IsActOf A₁.A A₁.L j' θ' t₂' T₂' → (CrossH c t₁ t₂ t₁' t₂' ↔ CrossH c T₁ T₂ T₁' T₂') := by
  first | exact @GlobalTheory.crossH_iff_of_isActOf | exact GlobalTheory.crossH_iff_of_isActOf | (intros; apply GlobalTheory.crossH_iff_of_isActOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrossRelationSectionsAmpleSourcePower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrossRelationSectionsAmpleSourcePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

open GlobalTheory.PullPair LBGerm GlobalTheory.AbLaw

def chartPullTwJ {X₁ X₂ : Scheme.{0}} (M₁ : LB X₁) (M₂ : LB X₂) (f : X₁ ⟶ X₂) (e : ℤ) (n t : ℕ) :
    ChartPull (LB.LinComb (join M₁ M₂) (K := Fin 2) ![f ≫ coprod.inr, coprod.inl] ![e, ((n * t : ℕ) : ℤ)])
      (tw (LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e)) (lbPow M₁ n) t) (𝟙 X₁) where
  idx J := (fun _ => J 0, fun _ => (J 1).1)
  le J y hy := ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0,
    Set.mem_iInter.2 fun _ => ((isPart_inl M₁ M₂).mem _ _).1 (Set.mem_iInter.1 hy 1)⟩
  g y J J' hJ hJ' := by
    have P := isPart_inl M₁ M₂
    have a₀ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ LB.wchart (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => J 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 0
    have a₁ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ powChart M₁ (fun _ => (J 1).1) :=
      Set.mem_iInter.2 fun _ => (P.mem _ _).1 (Set.mem_iInter.1 hJ 1)
    have b₀ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ LB.wchart (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => J' 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 0
    have b₁ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ powChart M₁ (fun _ => (J' 1).1) :=
      Set.mem_iInter.2 fun _ => (P.mem _ _).1 (Set.mem_iInter.1 hJ' 1)
    have hg := P.g _ (𝟙 X₁) y (J 1) (J' 1) ((P.mem _ _).1 (Set.mem_iInter.1 hJ 1)) ((P.mem _ _).1 (Set.mem_iInter.1 hJ' 1))
    refine (gm_linComb (join M₁ M₂) _ _ (𝟙 X₁) y J J' hJ hJ').trans (Units.ext (Eq.symm ?_))
    refine (TwistGen.gm_tw_g (LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e)) (lbPow M₁ n) t y
      (fun _ => J 0, fun _ => (J 1).1) (fun _ => J' 0, fun _ => (J' 1).1) ⟨a₀, a₁⟩ ⟨b₀, b₁⟩).trans ?_
    rw [gm_lbPow_g n (𝟙 X₁) y _ _ a₁ b₁, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    refine congrArg Units.val ((congrArg (· * _) (gm_linComb _ _ _ (𝟙 X₁) y _ _ a₀ b₀)).trans ?_)
    rw [Fintype.prod_unique, Fin.prod_univ_two, ← pow_mul, ← zpow_natCast]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp] at hg ⊢
    rw [hg]

theorem exists_sec_twist_join {X₁ X₂ : Scheme.{0}} {M₁ : LB X₁} {M₂ : LB X₂} (h : IsAmpleLB M₁) (h₂ : M₂.IsLB)
    [Nonempty X₁] [Nonempty X₂] (f : X₁ ⟶ X₂) (e : ℤ) (k : ℕ) (hk : 1 ≤ k) (y : X₁) :
    ∃ n, 1 ≤ n ∧ ∃ u : LB.Sec (LB.LinComb (join M₁ M₂) (K := Fin 2) ![f ≫ coprod.inr, coprod.inl] ![e, ((k * n : ℕ) : ℤ)]),
      y ∈ nonzeroLocus u := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  have hL := h.isLB
  have hN := join_isLB hL h₂
  obtain ⟨m, hm, s, hs, -, ha⟩ := h.exists_affine_le (x := y) (U := ⊤) trivial
  obtain ⟨V, N, hV, H⟩ := TwistGen.exists_nhds
    (M := LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e))
    (LB.isLB_linComb hN _ _) (isLB_lbPow hL m) s ha y hs
  obtain ⟨d, hd⟩ : ∃ d, k * (N + 1) = N + d := Nat.exists_eq_add_of_le (by nlinarith)
  obtain ⟨u, hu⟩ := H d
  refine ⟨m * (N + 1), Nat.mul_pos hm (Nat.succ_pos N), ?_⟩
  rw [show k * (m * (N + 1)) = m * (N + d) by rw [← hd]; ring]
  refine ⟨chartSec (chartPullTwJ M₁ M₂ f e m (N + d)) u, ?_⟩
  rw [nonzeroLocus_chartSec_id _ u fun x _ _ => exists_chart (LB.isLB_linComb hN _ _) x]
  exact hu hV

theorem exists_crossH : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧
      ∀ t₁ t₂ : SecA A₂ F j, ∃ t₁' t₂' : SecA A₁ F (k * n), CrossH c t₁ t₂ t₁' t₂' ∧
        ((∀ z J, Good A₂.L z J → sA t₂ (ptSecT A₂.A 1).left z J ≠ 0) →
          (∀ z J, Good A₁.L z J → sA t₂' (ptSecT A₁.A 1).left z J ≠ 0)) := by
  intro R _ _ A₁ A₂ F _ _ c hc j k hk
  have hL₁ := A₁.isLB
  have hL₂ := A₂.isLB
  let T : Over (Sp (FractionRing R)) := TFK (R := R) F
  have hsub : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  let z₀ : T.left := (⊥ : PrimeSpectrum F)
  have P₁ := isPart_inl A₁.L A₂.L
  have P₂ := isPart_inr A₁.L A₂.L
  have hN := join_isLB hL₁ hL₂
  obtain ⟨n, hn, u, hu⟩ := exists_sec_twist_join (isAmpleLB_of_relAmple_of_isAffine A₁.A hL₁ A₁.ample) hL₂ c.left
    (-(j : ℤ)) k hk (((ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (snd T A₁.A).left) z₀)
  have key : ∀ t : SecA A₂ F j, ∃ t' : SecA A₁ F (k * n), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A₁.A).left) (z : Z) (J),
      Good (join A₁.L A₂.L) z J →
        sA t' r z (rl J) = sA t (r ≫ (T ◁ c).left) z (rr J) * sval u (r ≫ (snd T A₁.A).left) z J := by
    intro t
    have e : (T ◁ c).left ≫ (snd T A₂.A).left ≫ (coprod.inr : A₂.A.left ⟶ A₁.A.left ⨿ A₂.A.left) =
        (snd T A₁.A).left ≫ c.left ≫ (coprod.inr : A₂.A.left ⟶ A₁.A.left ⨿ A₂.A.left) := by
      rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
    let tN := P₂.sec (φ := fun _ : Fin 1 => (snd T A₂.A).left) (ε := fun _ => (j : ℤ)) t
    obtain ⟨s, hs⟩ := exists_sec hN (φ' := fun _ : Fin 1 => (snd T A₁.A).left ≫ coprod.inl)
      (ε' := fun _ => ((k * n : ℕ) : ℤ))
      (fun U _ h => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
          Matrix.cons_val_zero, Matrix.cons_val_one, e, zpow_neg, mul_inv_cancel_left])
      (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec tN (T ◁ c).left) (H1.SectionArithmetic.pullSec u (snd T A₁.A).left))
    obtain ⟨t', ht'⟩ := P₁.exists_sec (φ := fun _ : Fin 1 => (snd T A₁.A).left) (ε := fun _ => ((k * n : ℕ) : ℤ)) hL₁
      (fst_surjective hL₂) s
    refine ⟨t', fun Z r z J hJ => (ht' Z r z J hJ).trans ((hs Z r z J hJ).trans ?_)⟩
    refine (H1.SectionArithmetic.sval_mulSec _ _ r z hJ).trans (congrArg₂ (· * ·) ?_ (H1.SectionArithmetic.sval_pullSec _ _ r z hJ))
    exact (H1.SectionArithmetic.sval_pullSec _ _ r z hJ).trans (P₂.sval_sec _ _ z hJ)
  refine ⟨n, hn, fun t₁ t₂ => ?_⟩
  obtain ⟨t₁', h₁⟩ := key t₁
  obtain ⟨t₂', h₂⟩ := key t₂
  refine ⟨t₁', t₂', fun z J₁ J₂ g₁ g₂ => ?_, fun h z J₁ g₁ => ?_⟩
  · obtain ⟨J, hJ, rfl, rfl⟩ := exists_good_join hL₁ hL₂ g₁ g₂
    rw [h₁ _ _ z J hJ, h₂ _ _ z J hJ, Category.id_comp]
    ring
  · choose d hd using fun ψ : T.left ⟶ A₂.A.left => exists_chart hL₂ (ψ z)
    obtain ⟨J, hJ, rfl, hr⟩ := exists_good_join hL₁ hL₂ g₁ (J₂ := d) hd
    have e : (ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (T ◁ c).left = (ptSecT A₂.A (1 : T ⟶ A₂.A)).left := by
      rw [← Over.comp_left, ptSecT, ptSecT, lift_whiskerLeft, MonObj.one_comp]
    rw [h₂ _ _ z J hJ, e]
    obtain rfl : z₀ = z := Subsingleton.elim _ _
    have hU : IsUnit (sval u ((ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (snd T A₁.A).left) z₀ J) :=
      (mem_nonzeroLocus_iff_pull u _ z₀ (hJ.mem _ _)).1 hu
    have g₂ : Good A₂.L z₀ (rr J) := hr ▸ hd
    exact fun h0 => h z₀ (rr J) g₂ (hU.mul_left_eq_zero.1 h0)

end GlobalTheory.Mum.Two
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrossRelationSectionsAmpleSourcePowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crossRelation_sections_ample_source_power : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧ ∀ t₁ t₂ : SecA A₂ F j, ∃ t₁' t₂' : SecA A₁ F (k * n), CrossH c t₁ t₂ t₁' t₂' ∧ ((∀ z J, Good A₂.L z J → sA t₂ (ptSecT A₂.A 1).left z J ≠ 0) → (∀ z J, Good A₁.L z J → sA t₂' (ptSecT A₁.A 1).left z J ≠ 0)) := by
  first | exact @GlobalTheory.Mum.Two.exists_crossH | exact GlobalTheory.Mum.Two.exists_crossH | (intros; apply GlobalTheory.Mum.Two.exists_crossH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedConvolutionCancelInjectiveLatticeHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedConvolutionCancelInjectiveLatticeHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.UT.CancelHom

section
variable {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)}

theorem coeff_mapDomain_mul {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    (a : AddMonoidAlgebra F X') (c : AddMonoidAlgebra F X)
    (T : Finset X') (hT : a.coeff.support ⊆ T) (α : X) :
    (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α = ∑ χ ∈ T, a.coeff χ * c.coeff (α - h χ) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain, Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_mul]),
    Finsupp.sum_of_support_subset _ hT _ (by simp)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [neg_add_eq_sub]

theorem sumV_fibre {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X) (α : X)
    (f : X' → X → F) {s : F}
    (H : SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => f p.1.1 p.1.2) s) :
    SumV v (fun χ => f χ (α - h χ)) s := by
  classical
  let e : X' ≃ {p : X' × X // h p.1 + p.2 = α} :=
    { toFun := fun χ => ⟨(χ, α - h χ), by simp⟩
      invFun := fun p => p.1.1
      left_inv := fun χ => rfl
      right_inv := fun p => Subtype.ext (Prod.ext rfl (sub_eq_of_eq_add' p.2.symm)) }
  intro q
  obtain ⟨S, hS⟩ := H q
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.toEmbedding) (fun p hp => by
    rw [Finset.mem_map_equiv]
    exact hT (Finset.mem_map_of_mem _ hp))
  rw [Finset.sum_map] at this
  exact this

theorem val_sum_sub_coeff {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    {A : X' → F} {C : X → F}
    {a : AddMonoidAlgebra F X'} {c : AddMonoidAlgebra F X} {M N : ℚ}
    (hA : ∀ χ, (M : WithTop ℚ) ≤ v (A χ)) (hC : ∀ χ, (M : WithTop ℚ) ≤ v (C χ))
    (ha : ∀ χ, (N : WithTop ℚ) ≤ v (A χ - a.coeff χ)) (ha' : ∀ χ, v (A χ) ≤ v (a.coeff χ))
    (hc : ∀ χ, (N : WithTop ℚ) ≤ v (C χ - c.coeff χ))
    (T : Finset X') (hT : a.coeff.support ⊆ T) (α : X) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v (∑ χ ∈ T, A χ * C (α - h χ) -
      (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α) := by
  rw [coeff_mapDomain_mul h a c T hT, ← Finset.sum_sub_distrib]
  exact v.map_le_sum fun χ _ => val_mul_sub_mul (ha _) (hc _) (hC _) ((hA _).trans (ha' _))

theorem val_coeff_of_sumV {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    {A₁ A₂ : X' → F} {C₁ C₂ : X → F}
    {a₁ a₂ : AddMonoidAlgebra F X'} {c₁ c₂ : AddMonoidAlgebra F X} {M N : ℚ}
    (hA₁ : ∀ χ, (M : WithTop ℚ) ≤ v (A₁ χ)) (hA₂ : ∀ χ, (M : WithTop ℚ) ≤ v (A₂ χ))
    (hC₁ : ∀ χ, (M : WithTop ℚ) ≤ v (C₁ χ)) (hC₂ : ∀ χ, (M : WithTop ℚ) ≤ v (C₂ χ))
    (ha₁ : ∀ χ, (N : WithTop ℚ) ≤ v (A₁ χ - a₁.coeff χ)) (ha₁' : ∀ χ, v (A₁ χ) ≤ v (a₁.coeff χ))
    (ha₂ : ∀ χ, (N : WithTop ℚ) ≤ v (A₂ χ - a₂.coeff χ)) (ha₂' : ∀ χ, v (A₂ χ) ≤ v (a₂.coeff χ))
    (hc₁ : ∀ χ, (N : WithTop ℚ) ≤ v (C₁ χ - c₁.coeff χ))
    (hc₂ : ∀ χ, (N : WithTop ℚ) ≤ v (C₂ χ - c₂.coeff χ)) (α : X)
    (H : SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v ((AddMonoidAlgebra.mapDomainRingHom F h a₁ * c₂ -
      AddMonoidAlgebra.mapDomainRingHom F h a₂ * c₁).coeff α) := by
  classical
  obtain ⟨S, hS⟩ := sumV_fibre h α (fun x y => A₁ x * C₂ y - A₂ x * C₁ y) H (N + M)
  have h0 := hS (S ∪ (a₁.coeff.support ∪ a₂.coeff.support)) Finset.subset_union_left
  have h1 := val_sum_sub_coeff h hA₁ hC₂ ha₁ ha₁' hc₂ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_left.trans Finset.subset_union_right) α
  have h2 := val_sum_sub_coeff h hA₂ hC₁ ha₂ ha₂' hc₁ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_right.trans Finset.subset_union_right) α
  have h3 := v.map_le_sub (v.map_le_sub h2 h1) h0
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring
end

end GlobalTheory.UT.CancelHom

namespace GlobalTheory.UT

theorem sumV_cancel_hom : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (h : X' →+ X), Function.Injective h → ∀ (A₁ A₂ B₁ B₂ : X' → F) (C₁ C₂ : X → F), NullV v A₁ → NullV v A₂ → NullV v B₁ → NullV v B₂ → NullV v C₁ → NullV v C₂ → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0) → C₂ ≠ 0 → ∀ α, SumV v (fun χ : X' => B₁ χ * A₂ (α - χ) - B₂ χ * A₁ (α - χ)) 0 := by
  classical
  intro F _ v X X' _ _ _ _ _ _ h hinj A₁ A₂ B₁ B₂ C₁ C₂ nA₁ nA₂ nB₁ nB₂ nC₁ nC₂ HA HB hC α q
  obtain ⟨w, hw⟩ := exists_addGauss v X
  obtain ⟨χ₀, hχ₀⟩ := Function.ne_iff.mp hC
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (fun e => hχ₀ (v.top_iff.mp e) : v (C₂ χ₀) ≠ ⊤)
  obtain ⟨M₁, hM₁⟩ := nA₁.exists_lower
  obtain ⟨M₂, hM₂⟩ := nA₂.exists_lower
  obtain ⟨M₃, hM₃⟩ := nB₁.exists_lower
  obtain ⟨M₄, hM₄⟩ := nB₂.exists_lower
  obtain ⟨M₅, hM₅⟩ := nC₁.exists_lower
  obtain ⟨M₆, hM₆⟩ := nC₂.exists_lower
  obtain ⟨M, l1, l2, l3, l4, l5, l6⟩ : ∃ M : ℚ, M ≤ M₁ ∧ M ≤ M₂ ∧ M ≤ M₃ ∧ M ≤ M₄ ∧ M ≤ M₅ ∧ M ≤ M₆ :=
    ⟨min M₁ (min M₂ (min M₃ (min M₄ (min M₅ M₆)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  replace hM₁ := hM₁ M l1
  replace hM₂ := hM₂ M l2
  replace hM₃ := hM₃ M l3
  replace hM₄ := hM₄ M l4
  replace hM₅ := hM₅ M l5
  replace hM₆ := hM₆ M l6
  obtain ⟨N, n1, n2, n3⟩ : ∃ N : ℚ, m < N ∧ q + m ≤ M + (N + M) ∧ q ≤ N + M := by
    refine ⟨max (m + 1) (max (q + m - M - M) (q - M)), ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · have := (le_max_left (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
    · have := (le_max_right (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
  obtain ⟨a₁, ha₁, ha₁', -⟩ := nA₁.exists_trunc N
  obtain ⟨a₂, ha₂, ha₂', -⟩ := nA₂.exists_trunc N
  obtain ⟨b₁, hb₁, hb₁', -⟩ := nB₁.exists_trunc N
  obtain ⟨b₂, hb₂, hb₂', -⟩ := nB₂.exists_trunc N
  obtain ⟨c₁, hc₁, -, -⟩ := nC₁.exists_trunc N
  obtain ⟨c₂, hc₂, -, hc₂'⟩ := nC₂.exists_trunc N
  have EA := (hw _ _).mpr fun β =>
    CancelHom.val_coeff_of_sumV h hM₁ hM₂ hM₅ hM₆ ha₁ ha₁' ha₂ ha₂' hc₁ hc₂ β (HA β)
  have EB := (hw _ _).mpr fun β =>
    CancelHom.val_coeff_of_sumV h hM₃ hM₄ hM₅ hM₆ hb₁ hb₁' hb₂ hb₂' hc₁ hc₂ β (HB β)
  have push : ∀ (d : AddMonoidAlgebra F X') (g : WithTop ℚ),
      g ≤ w (AddMonoidAlgebra.mapDomainRingHom F h d) ↔ ∀ χ, g ≤ v (d.coeff χ) := by
    intro d g
    rw [hw, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
    refine ⟨fun H χ => ?_, fun H β => ?_⟩
    · have := H (h χ)
      rwa [Finsupp.mapDomain_apply_of_injective hinj] at this
    · by_cases hβ : β ∈ Set.range h
      · obtain ⟨χ, rfl⟩ := hβ
        rw [Finsupp.mapDomain_apply_of_injective hinj]
        exact H χ
      · rw [Finsupp.mapDomain_of_notMem_range _ _ hβ, v.map_zero]
        exact le_top
  set P := AddMonoidAlgebra.mapDomainRingHom F h with hP
  have key : ((q + m : ℚ) : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) + w c₂ := by
    have e : P (b₁ * a₂ - b₂ * a₁) * c₂ =
        P a₂ * (P b₁ * c₂ - P b₂ * c₁) - P b₂ * (P a₁ * c₂ - P a₂ * c₁) := by
      rw [map_sub, map_mul, map_mul]; ring
    rw [← w.map_mul, e]
    refine (WithTop.coe_le_coe.mpr n2).trans ?_
    rw [WithTop.coe_add]
    refine w.map_le_sub ?_ ?_ <;> rw [w.map_mul]
    · exact add_le_add ((push _ _).mpr fun χ => (hM₂ χ).trans (ha₂' χ)) EB
    · exact add_le_add ((push _ _).mpr fun χ => (hM₄ χ).trans (hb₂' χ)) EA
  have hc : w c₂ ≤ (m : WithTop ℚ) := by
    have := (hw c₂ _).mp le_rfl χ₀
    rwa [hc₂' χ₀ (by rw [← hm]; exact WithTop.coe_lt_coe.mpr n1), ← hm] at this
  have key2 : (q : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) := by
    have := key.trans (add_le_add le_rfl hc)
    rw [WithTop.coe_add] at this
    exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp this
  have key3 := (push _ _).mp key2 α
  refine ⟨b₁.coeff.support ∪ b₂.coeff.support, fun T hT => ?_⟩
  have h1 := CancelHom.val_sum_sub_coeff (AddMonoidHom.id X') hM₃ hM₂ hb₁ hb₁' ha₂ T
    (Finset.subset_union_left.trans hT) α
  have h2 := CancelHom.val_sum_sub_coeff (AddMonoidHom.id X') hM₄ hM₁ hb₂ hb₂' ha₁ T
    (Finset.subset_union_right.trans hT) α
  rw [AddMonoidAlgebra.mapDomainRingHom_id] at h1 h2
  simp only [RingHom.id_apply, AddMonoidHom.id_apply] at h1 h2
  have h3 := v.map_le_sub (v.map_le_sub ((WithTop.coe_le_coe.mpr n3).trans h2)
    ((WithTop.coe_le_coe.mpr n3).trans h1)) key3
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring

end GlobalTheory.UT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedConvolutionCancelInjectiveLatticeHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuedConvolution_cancel_injective_latticeHom : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (h : X' →+ X), Function.Injective h → ∀ (A₁ A₂ B₁ B₂ : X' → F) (C₁ C₂ : X → F), NullV v A₁ → NullV v A₂ → NullV v B₁ → NullV v B₂ → NullV v C₁ → NullV v C₂ → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0) → C₂ ≠ 0 → ∀ α, SumV v (fun χ : X' => B₁ χ * A₂ (α - χ) - B₂ χ * A₁ (α - χ)) 0 := by
  first | exact @GlobalTheory.UT.sumV_cancel_hom | exact GlobalTheory.UT.sumV_cancel_hom | (intros; apply GlobalTheory.UT.sumV_cancel_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitTorsionPointMapCommutesCharInjectiveHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two.KeyDvr
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.EndTors
attribute [local instance] gtGroup

theorem act_zero₂ {R : Type} [CommRing R] [IsDomain R] {D₁ D₂ : DegPre R} (b : D₁.P.A ⟶ D₂.P.A) [IsMonHom b]
    (h : D₂.X →+ D₁.X) {F : Type} [Field F] [Algebra (FractionRing R) F] {o₁ : GtPtF D₁ F} {o₂ : GtPtF D₂ F}
    (h₁ : o₁.IsZero) (h₂ : o₂.IsZero) : Act D₁ D₂ b h o₁ o₂ := by
  obtain ⟨hb₁, hv₁⟩ := (isZero_iff o₁).1 h₁
  obtain ⟨hb₂, hv₂⟩ := (isZero_iff o₂).1 h₂
  refine ⟨by rw [hb₂, hb₁, MonObj.one_comp], fun χ u hu z J hJ => ?_⟩
  rw [hv₂ _ z _ ((isPart_inr (M₁ := D₁.P.L) (M₂ := D₂.P.L)).good hJ),
    hv₁ _ z _ ((isPart_inl (M₁ := D₁.P.L) (M₂ := D₂.P.L)).good hJ), hb₁, _root_.one_mul]
  exact (hu.2 _ (TF (R := R) F).hom z J hJ).symm

theorem sumV_shift₂ {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {X X' : Type} [AddCommGroup X]
    [AddCommGroup X'] (h : X' →+ X) (y : X') (y' : X) {B₁ B₂ b₁ b₂ : X' → F} {C₁ C₂ c₁ c₂ : X → F}
    (hB₁ : ∀ α, B₁ (α + y) = b₁ α) (hB₂ : ∀ α, B₂ (α + y) = b₂ α)
    (hC₁ : ∀ α, C₁ (α + y') = c₁ α) (hC₂ : ∀ α, C₂ (α + y') = c₂ α)
    (H : ∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => b₁ p.1.1 * c₂ p.1.2 - b₂ p.1.1 * c₁ p.1.2) 0)
    (α : X) :
    SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0 := by
  refine sumV_equiv v (Equiv.subtypeEquiv ((Equiv.addRight y).prodCongr (Equiv.addRight y')) fun p => ?_) (fun p => ?_)
    (H (α - h y - y'))
  · simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight, map_add (f := _)]
    constructor
    · intro e; rw [show α = α - h y - y' + h y + y' by abel, ← e]; abel
    · intro e; rw [← e]; abel
  · simp only [Equiv.subtypeEquiv_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight,
      hB₁, hB₂, hC₁, hC₂]

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (A₁ A₂ : PolAV (Sp (FractionRing V))) (G₁ G₂ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  intro V _ _ _ _ hV ϖ hϖ F _ _ _ v hv D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h hc hgen hlin hcoord hE
    k hk p x hx g' hg'
  have hL : LL := GlobalTheory.firstFiveLaws
  obtain ⟨-, h₁, h₂, h₃, h₄⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  choose Q hQ' using QForm.exists_QVal hϖ D₂
  have hQ : QForm.IsQ D₂.toPre ϖ Q := hQ'
  have hB := D₂.tau_bimult
  have := hc
  have := hlin.2.1
  have CV := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D₂ Q hQ F v hv
  have EV₁ := GlobalTheory.UT.EvalZero.value_at_origin hL V _ hA D₁ A₁ G₁ hG₁ U₁ F
  have EV₂ := GlobalTheory.UT.EvalZero.value_at_origin hL V _ hA D₂ A₂ G₂ hG₂ U₂ F
  have LU₁ := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D₁ A₁ G₁ hG₁ U₁ F
  have LU₂ := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D₂ A₂ G₂ hG₂ U₂ F
  have BJ₁ := (expBijF_and_expandsF_lin hL V _ hA D₁ A₁ G₁ hG₁ U₁).1 F
  have BJ₂ := (expBijF_and_expandsF_lin hL V _ hA D₂ A₂ G₂ hG₂ U₂).1 F
  have SV := fun Ix => AdicValSum.main V ϖ hϖ F v hv Ix
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D₂ A₂ G₂ hG₂ U₂ F k hk
  obtain ⟨ρ₁, hρ₁⟩ := EV₁.1
  obtain ⟨w₀₁, hN₁⟩ := EV₁.2.1 ρ₁ hρ₁
  obtain ⟨ρ₂, hρ₂⟩ := EV₂.1
  obtain ⟨w₀₂, hN₂⟩ := EV₂.2.1 ρ₂ hρ₂
  have hw₀₁ := hN₁.1
  have hw₀₂ := hN₂.1
  have hxk : x ^ k = 1 := (hx w₀₁ hw₀₁).1
  obtain ⟨p₀, hp₀⟩ := f₂ (x ≫ c) (by rw [← MonObj.pow_comp, hxk, MonObj.one_comp])
  obtain ⟨l', hl', -⟩ := (CV g').1
  obtain ⟨z, hz⟩ := GlobalTheory.exists_rep_mod_shifted_form_small D₂.toPre.X Q (QForm.bHom hϖ D₂ hQ)
    (fun a₀ b₀ => by rw [QForm.bHom_apply, QForm.bOf]; ring) (QForm.two_Q_eq hϖ D₂ hQ)
    (fun a ha => QForm.Q_pos hϖ D₂ hQ ha) (k • l') k hk p₀.y
  let p₁ : QkPt D₂.toPre F k := qkMk hB (p₀.y + k • z) (p₀.g + iota hB F z)
    (by rw [nsmul_add, qk_nsmul hB, map_add (f := _), map_nsmul])
  have hp₁ : QkToAkU U₂.toUnifPre F k p₁ (x ≫ c) :=
    (f₁ _ _).2 (hp₀.symm.trans ((f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨z, rfl, rfl⟩)))
  let d : GtPtF D₂.toPre F := g' - p₁.g
  have hd : d.IsAdd p₁.g g' := (isAdd_iff_eq _ _ _).2 (sub_add_cancel _ _).symm
  obtain ⟨l, hl, -⟩ := (CV d).1
  obtain ⟨l₁, hl₁, -⟩ := (CV p₁.g).1
  have ho : (0 : GtPtF D₂.toPre F).IsZero := (isZero_iff_eq _).2 rfl
  have ho₁ : (0 : GtPtF D₁.toPre F).IsZero := (isZero_iff_eq _).2 rfl
  suffices H : d.IsZero from ⟨p₁, (sub_eq_zero.1 ((isZero_iff_eq _).1 H)).symm, hp₁⟩
  have gu : ∀ (g : GtPtF D₂.toPre F) (a b : D₂.toPre.X →+ ℚ), GtV hϖ hv g a → GtV hϖ hv g b → a = b :=
    fun g a b ha hb => (CV g).1.unique ha hb
  have k0 : (0 : ℚ) < k := by exact_mod_cast hk
  refine GlobalTheory.T.smallTorusPoint_keeping_ratios_isZero hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D₂ Q hQ F v hv k hk d 0 l ho hl (fun m => ?_) fun n j hn hj w₁ hw₁ => ?_
  · have e₁ := gu g' l' (l + l₁) hl' ((CV d).2.2.2.1 p₁.g g' l l₁ hd hl hl₁)
    have e₂ := gu p₁.g l₁ ((k : ℚ)⁻¹ • (Int.castAddHom ℚ).comp (QForm.bHom hϖ D₂ hQ p₁.y)) hl₁ (by
      have := (CV p₁.g).2.2.2.2.1 k hk p₁
      convert this using 2 with χ
      simp [QForm.bHom_apply, div_eq_inv_mul])
    have e₃ := hz m
    have e₄ : ((QForm.bHom hϖ D₂ hQ (p₀.y + k • z) m : ℤ) : ℚ) - (k • l') m = -(k * l m) := by
      rw [e₁, e₂]
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Int.coe_castAddHom,
        smul_eq_mul, nsmul_eq_mul]
      dsimp [p₁, qkMk]
      show _ - (k : ℚ) * (l m + (k : ℚ)⁻¹ * ((QForm.bHom hϖ D₂ hQ (p₀.y + k • z) m : ℤ) : ℚ)) = _
      field_simp
      ring
    rw [e₄, abs_neg, abs_mul, abs_of_pos k0] at e₃
    exact le_of_mul_le_mul_left e₃ k0
  have up₂ : ∀ (r : QkPt D₂.toPre F k) (n N : ℕ), N = k * n → ∃ q : QkPt D₂.toPre F N, q.y = n • r.y ∧ q.g = r.g :=
    fun r n N h => ⟨qkMk hB (n • r.y) r.g (by rw [h, mul_nsmul, qk_nsmul hB, map_nsmul]), rfl, rfl⟩
  have hB₁ := D₁.tau_bimult
  have up₁ : ∀ (r : QkPt D₁.toPre F k) (n N : ℕ), N = k * n → ∃ q : QkPt D₁.toPre F N, q.y = n • r.y ∧ q.g = r.g :=
    fun r n N h => ⟨qkMk hB₁ (n • r.y) r.g (by rw [h, mul_nsmul, qk_nsmul hB₁, map_nsmul]), rfl, rfl⟩
  have hj1 : 1 ≤ j := hj ▸ Nat.mul_pos hk hn
  obtain ⟨q₁, qy₁, qg₁⟩ := up₂ p₁ n j hj
  obtain ⟨w, hw⟩ := (coef_basic V D₂.toPre F j d).1
  obtain ⟨θ, hθ, ω, hω, K⟩ := exists_pre_coef hL hA hG₂ U₂ hj1 q₁
    (((LU₂ k n j hk hn hj p₁ q₁ _).1 qy₁ qg₁).1 hp₁) hw₀₂ (qg₁ ▸ hd) hw
  refine ⟨w, hw, fun S₁ S₂ hS => ?_⟩
  obtain ⟨T₁, hT₁, -⟩ := (BJ₂ j hj1 w₀₂ hw₀₂).2 S₁
  obtain ⟨T₂, hT₂, -⟩ := (BJ₂ j hj1 w₀₂ hw₀₂).2 S₂
  obtain ⟨n', hn', CR⟩ := GlobalTheory.T.exists_crossRelation_sections_ample_source_power V A₁ A₂ F c hc j k hk
  obtain ⟨T₁', T₂', hC, hne⟩ := CR T₁ T₂
  have hj' : 1 ≤ k * n' := Nat.mul_pos hk hn'
  obtain ⟨S₁', hT₁', -⟩ := (BJ₁ _ hj' w₀₁ hw₀₁).1 T₁'
  obtain ⟨S₂', hT₂', -⟩ := (BJ₁ _ hj' w₀₁ hw₀₁).1 T₂'
  obtain ⟨w₁', hw₁'⟩ := (coef_basic V D₁.toPre F (k * n') 0).2.1 zero_b
  obtain ⟨q, qy, qg⟩ := up₁ p n' _ rfl
  obtain ⟨θ', hθ', ω', hω', K'⟩ := exists_pre_coef hL hA hG₁ U₁ hj' q
    (((LU₁ k n' _ hk hn' rfl p q _).1 qy qg).1 hx) hw₀₁
    (g₀ := 0) (g₁ := p.g) ((isAdd_iff_eq _ _ _).2 (by rw [qg, zero_add])) hw₁'.1
  obtain ⟨t₁, s₁, a₁, e₁, c₁⟩ := K T₁ S₁ hT₁
  obtain ⟨t₂, s₂, a₂, e₂, c₂⟩ := K T₂ S₂ hT₂
  obtain ⟨t₁', s₁', a₁', e₁', c₁'⟩ := K' T₁' S₁' hT₁'
  obtain ⟨t₂', s₂', a₂', e₂', c₂'⟩ := K' T₂' S₂' hT₂'
  have hC' := (GlobalTheory.T.thetaSectionCrossRelation_iff_of_thetaAction V A₁ A₂ F c hc j _ θ θ' (by rw [hθ, hθ']) _ _ _ _ _ _ _ _
    a₁ a₂ a₁' a₂').2 hC
  have nl₂ : ∀ (g : GtPtF D₂.toPre F) (i : ℕ), 1 ≤ i → ∀ (u : Frm D₂.toPre F i g.b) (s : Fam D₂.toPre F i), u.IsGen →
      NullV v (coef s g u) := fun g i hi u s hu => ((CV g).2.2.2.2.2.2 i hi u s hu).1
  choose Q₁ hQ₁' using QForm.exists_QVal hϖ D₁
  have hQ₁ : QForm.IsQ D₁.toPre ϖ Q₁ := hQ₁'
  have CV₁ := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D₁ Q₁ hQ₁ F v hv
  have nl₁ : ∀ (g : GtPtF D₁.toPre F) (i : ℕ), 1 ≤ i → ∀ (u : Frm D₁.toPre F i g.b) (s : Fam D₁.toPre F i), u.IsGen →
      NullV v (coef s g u) := fun g i hi u s hu => ((CV₁ g).2.2.2.2.2.2 i hi u s hu).1
  have MX := GlobalTheory.T.crossRelation_hom_gives_expansionTerm_convolution_rel V _ hA D₁ D₂ A₁ A₂ G₁ G₂ hG₁ hG₂ U₁ U₂ a c b h hc hgen hlin hcoord F w₀₁ w₀₂ hw₀₁ hw₀₂
  refine GlobalTheory.T.valuedConvolution_cancel_injective_latticeHom F v D₁.toPre.X D₂.toPre.X h hE (coef S₁ 0 w₁) (coef S₂ 0 w₁) (coef S₁ d w) (coef S₂ d w)
    (coef S₁' 0 w₁') (coef S₂' 0 w₁') (nl₂ _ _ hj1 _ _ hw₁.1) (nl₂ _ _ hj1 _ _ hw₁.1) (nl₂ _ _ hj1 _ _ hw)
    (nl₂ _ _ hj1 _ _ hw) (nl₁ _ _ hj' _ _ hw₁'.1) (nl₁ _ _ hj' _ _ hw₁'.1)
    (fun α => (SV _ _ _ (MX j _ hj1 hj' _ _ _ _ _ _ _ _ hT₁ hT₂ hT₁' hT₂' hC 0 0 (act_zero₂ b h ho₁ ho) w₁ w₁'
      hw₁.1 hw₁'.1 α)).1)
    (sumV_shift₂ v h q₁.y q.y c₁ c₂ c₁' c₂' fun α => (SV _ _ _ (MX j _ hj1 hj' _ _ _ _ _ _ _ _ e₁ e₂ e₁' e₂'
      hC' p.g g' hg' ω ω' hω hω' α)).1) fun h0 => ?_
  obtain ⟨cc, hcc⟩ := exists_value hρ₂ T₂
  obtain ⟨cc', hcc'⟩ := exists_value hρ₁ T₂'
  have σ := (SV _ _ _ (EV₂.2.2 w₀₂ ρ₂ hN₂ j T₂ S₂ hT₂ 0 w₁ ho hw₁ cc hcc)).1
  have σ' := (SV _ _ _ (EV₁.2.2 w₀₁ ρ₁ hN₁ _ T₂' S₂' hT₂' 0 w₁' ho₁ hw₁' cc' hcc')).1
  rw [h0] at σ'
  obtain rfl := eq_zero_of_sumV_zero v σ'
  obtain ⟨y⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := V) F).left) A₁.isLB y
  refine hne (fun y J hJ h => hS ?_) y J hJ ((hcc' y J hJ).trans ?_)
  · have e : cstH (R := V) y cc = 0 :=
      (cst_eq y cc).symm.trans ((Units.mul_left_eq_zero _).1 ((hcc y J hJ).symm.trans h))
    obtain rfl : cc = 0 := cstH_inj y (e.trans (map_zero _).symm)
    exact σ
  · exact mul_eq_zero_of_left ((cst_eq y 0).trans (map_zero _)) _

end GlobalTheory.Mum.Two.KeyDvr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitTorsionPointMapCommutesCharInjectiveHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_torsion_point_map_commutes_char_injective_hom : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (A₁ A₂ : PolAV (Sp (FractionRing V))) (G₁ G₂ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  first | exact @GlobalTheory.Mum.Two.KeyDvr.main | exact GlobalTheory.Mum.Two.KeyDvr.main | (intros; apply GlobalTheory.Mum.Two.KeyDvr.main <;> assumption)
end
