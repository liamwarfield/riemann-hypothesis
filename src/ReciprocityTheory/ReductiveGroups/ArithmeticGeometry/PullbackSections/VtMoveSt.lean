module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.MixEnd
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RigPMaps
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem rig_pmaps {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ))
    (h : RigIso m w) :
    PMaps w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e :=
  (maps_iff w _ _ _ t'.PP.rig t.PP.rig m.cm.e (m.cm.rigPull t.PP.L t.PP.rig)
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 h.2

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MixEnd

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section Pmaps

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem val_pmaps' (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hm : PMaps w φ' φ ε a t h) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z)
    (J₀ : (Z ⟶ X) → L.ι) (J : (Z ⟶ X') → L'.ι) (hJ₀ : Good L z J₀) (hJ : Good L' z J) :
    val t (r ≫ h) z J₀ =
      (∏ k, gw w (r ≫ φ' k) z (J₀ ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  have hp : ∀ k, (r ≫ h) ≫ φ k = (r ≫ φ' k) ≫ F := fun k => by
    rw [Category.assoc, Category.assoc, hc]
  have h1 : ∀ k, F (φ' k (r z)) ∈ L.U (J₀ ((r ≫ h) ≫ φ k)) := by
    intro k
    convert hJ₀ ((r ≫ h) ≫ φ k) using 2
    rw [hp]
    first | rfl | simp
  have h2 : ∀ k, φ' k (r z) ∈ L'.U (J (r ≫ φ' k)) := fun k => hJ (r ≫ φ' k)
  have key := hm Z r z (fun k => J₀ ((r ≫ h) ≫ φ k)) (fun k => J (r ≫ φ' k)) h1 h2
  unfold val
  refine key.trans ?_
  simp only [hp]

end Pmaps

theorem val_rigPow {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) (rig : LB.Gen (L.pull (eSec A))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    val (rigPow A L rig k) r z J = (val (L := L) (K := PUnit) (φ := fun _ => eSec A) (ε := fun _ => 1) rig r z J) ^ k := by
  unfold val
  simp only [rigPow]
  exact map_zpow _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
  {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

section Snd

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

theorem genSnd_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : PGen w)
    (eA : A.left ⟶ A.left) (eG : G.left ⟶ G.left) (hce : eA ≫ φ = φ ≫ eG) (ε : Fin 2 → ℤ)
    (α₀' : LB.Gen (LB.LinComb L₁ ![𝟙 A.left, eA] ε)) (α₀ : LB.Gen (LB.LinComb L₀ ![𝟙 G.left, eG] ε))
    (hPM : PMaps w ![𝟙 A.left, eA] ![𝟙 G.left, eG] ε α₀' α₀ φ)
    (mA : T ⊗ A ⟶ A) (mG : T₀ ⊗ G ⟶ G) (hmA : mA.left = (snd T A).left ≫ eA)
    (hmG : mG.left = (snd T₀ G).left ≫ eG)
    (α : LB.Gen (LB.LinComb L₀ ![(snd T₀ G).left, mG.left] ε)) (hα : α.IsGen)
    (hαc : LB.Gen.Corr L₀ _ _ _ _ α (LB.pullGen L₀ _ _ α₀ (snd T₀ G).left)) :
    ∃ α' : LB.Gen (LB.LinComb L₁ ![(snd T A).left, mA.left] ε), α'.IsGen ∧
      PMaps w ![(snd T A).left, mA.left] ![(snd T₀ G).left, mG.left] ε α' α (psiO hp τ hτ).left ∧
      LB.Gen.Corr L₁ _ _ _ _ α' (LB.pullGen L₁ _ _ α₀' (snd T A).left) := by
  have hc1 : ∀ k, (![(snd T A).left, mA.left] : Fin 2 → _) k ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, mG.left] : Fin 2 → _) k := by
    intro k; fin_cases k
    · exact (psi_snd hp τ hτ).symm
    · show mA.left ≫ φ = (psiO hp τ hτ).left ≫ mG.left
      rw [hmA, hmG, Category.assoc, hce, ← Category.assoc, ← psi_snd hp τ hτ, Category.assoc]
  have hc2 : ∀ k, (![𝟙 A.left, eA] : Fin 2 → _) k ≫ φ = φ ≫ (![𝟙 G.left, eG] : Fin 2 → _) k := by
    intro k; fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Category.id_comp, Category.comp_id]
    · exact hce
  obtain ⟨α', g', hm⟩ := exists_gen_move hL₀ hL₁ w hw _ _ ε (psiO hp τ hτ).left hc1 α hα
  refine ⟨α', g', hm, corr_of_val hL₁ fun y J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
  have hJ₀' : Good L₀ y J₀ := hJ₀
  have p1 := val_pmaps' w hc1 hm (𝟙 _) y J₀ J hJ₀' hJ
  have p2 := val_pmaps' w hc2 hPM (snd T A).left y J₀ J hJ₀' hJ
  have c := val_corr hJ₀' hαc (psiO hp τ hτ).left
  rw [val_pull hJ₀', psi_snd hp τ hτ] at c
  rw [Category.id_comp, c, p2] at p1
  simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
    Category.id_comp, hmA] at p1
  rw [val_pull hJ, Category.id_comp]
  exact (mul_left_cancel p1).symm

end Snd

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MixEnd
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMoveSym
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMove
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

theorem push_pow {X : Over S'} (x : X ⟶ A) (N : ℕ) : (x ^ N).left ≫ φ = (pushPt hp.1.w x ^ N).left := by
  exact congrArg (fun y => y.left) (map_pow (pushHom hp X) x N)

theorem push_inv {X : Over S'} (x : X ⟶ A) : (x ≫ GrpObj.inv).left ≫ φ = (pushPt hp.1.w x ≫ GrpObj.inv).left := by
  exact congrArg (fun y => y.left) (map_inv (pushHom hp X) x)

include hp in
theorem mulA_push (N : ℕ) : (mulA A N).left ≫ φ = φ ≫ (mulA G N).left := by
  show (𝟙 A ^ N).left ≫ φ = φ ≫ (𝟙 G ^ N).left
  rw [push_pow hp, ← Category.comp_id (pushPt hp.1.w (𝟙 A)), ← MonObj.comp_pow, Over.comp_left]
  simp only [pushPt, Over.homMk_left, Over.id_left]
  exact congrArg (fun g => g ≫ (𝟙 G ^ N).left) (Category.id_comp φ)

theorem psi_snd' : psiO hp τ hτ ≫ snd T₀ G = pushPt hp.1.w (snd T A) := by
  unfold psiO
  exact lift_snd _ _

theorem snd_pow_push (N : ℕ) : (snd T A ^ N).left ≫ φ = (psiO hp τ hτ).left ≫ (snd T₀ G ^ N).left := by
  rw [push_pow hp, ← psi_snd' hp τ hτ, ← MonObj.comp_pow, Over.comp_left]

theorem snd_inv_push : (snd T A ≫ GrpObj.inv).left ≫ φ = (psiO hp τ hτ).left ≫ (snd T₀ G ≫ GrpObj.inv).left := by
  rw [push_inv hp, ← psi_snd' hp τ hτ, Category.assoc, Over.comp_left]

theorem hom_ext₀ {Y : Scheme.{0}} {a b : Y ⟶ (T₀ ⊗ G).left} (h1 : a ≫ (fst T₀ G).left = b ≫ (fst T₀ G).left)
    (h2 : a ≫ (snd T₀ G).left = b ≫ (snd T₀ G).left) : a = b := pullback.hom_ext h1 h2

theorem mulT_push (N : ℕ) :
    (mulT A T N).left ≫ (psiO hp τ hτ).left = (psiO hp τ hτ).left ≫ (mulT G T₀ N).left := by
  have hA1 : (mulT A T N).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left]; simp only [mulT, lift_fst]
  have hG1 : (mulT G T₀ N).left ≫ (fst T₀ G).left = (fst T₀ G).left := by
    rw [← Over.comp_left]; simp only [mulT, lift_fst]
  have hA2 : (mulT A T N).left ≫ (snd T A).left = (snd T A ^ N).left := by
    rw [← Over.comp_left]; simp only [mulT, lift_snd]
  have hG2 : (mulT G T₀ N).left ≫ (snd T₀ G).left = (snd T₀ G ^ N).left := by
    rw [← Over.comp_left]; simp only [mulT, lift_snd]
  apply hom_ext₀
  · simp only [Category.assoc, psi_fst]
    rw [reassoc_of% hA1, hG1, psi_fst]
  · simp only [Category.assoc, psi_snd]
    rw [reassoc_of% hA2, hG2]
    exact snd_pow_push hp τ hτ N

theorem negT_push : (negT A T).left ≫ (psiO hp τ hτ).left = (psiO hp τ hτ).left ≫ (negT G T₀).left := by
  have hA1 : (negT A T).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left]; simp only [negT, lift_fst]
  have hG1 : (negT G T₀).left ≫ (fst T₀ G).left = (fst T₀ G).left := by
    rw [← Over.comp_left]; simp only [negT, lift_fst]
  have hA2 : (negT A T).left ≫ (snd T A).left = (snd T A ≫ GrpObj.inv).left := by
    rw [← Over.comp_left]; simp only [negT, lift_snd]
  have hG2 : (negT G T₀).left ≫ (snd T₀ G).left = (snd T₀ G ≫ GrpObj.inv).left := by
    rw [← Over.comp_left]; simp only [negT, lift_snd]
  apply hom_ext₀
  · simp only [Category.assoc, psi_fst]
    rw [reassoc_of% hA1, hG1, psi_fst]
  · simp only [Category.assoc, psi_snd]
    rw [reassoc_of% hA2, hG2]
    exact snd_inv_push hp τ hτ

section Pmaps

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem val_pmaps (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hm : PMaps w φ' φ ε a t h) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z)
    (J₀ : (Z ⟶ X) → L.ι) (J : (Z ⟶ X') → L'.ι) (hJ₀ : Good L z J₀) (hJ : Good L' z J) :
    val t (r ≫ h) z J₀ =
      (∏ k, gw w (r ≫ φ' k) z (J₀ ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.MixEnd.val_pmaps' w hc hm r z J₀ J hJ₀ hJ

end Pmaps

section Pts

def Uτ : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk τ hτ

def liftPt (x₀ : T₀ ⟶ G) : T ⟶ A :=
  Over.homMk (hp.1.lift (τ ≫ x₀.left) T.hom (by rw [Category.assoc, Over.w x₀, hτ])) (hp.1.lift_snd _ _ _)

theorem liftPt_left (x₀ : T₀ ⟶ G) : (liftPt hp τ hτ x₀).left ≫ φ = τ ≫ x₀.left := hp.1.lift_fst _ _ _

include hp in
theorem pt_ext {x y : T ⟶ A} (h : x.left ≫ φ = y.left ≫ φ) : x = y :=
  Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w y]))

theorem push_eq {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : x.left ≫ φ = τ ≫ x₀.left) :
    pushPt hp.1.w x = Uτ τ hτ ≫ x₀ := Over.OverMorphism.ext hx

include hp hτ in
theorem pow_rel {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : x.left ≫ φ = τ ≫ x₀.left) (n : ℕ) :
    (x ^ n).left ≫ φ = τ ≫ (x₀ ^ n).left := by
  rw [push_pow hp, push_eq hp τ hτ hx, ← MonObj.comp_pow]
  rfl

include hp hτ in
theorem one_rel : (1 : T ⟶ A).left ≫ φ = τ ≫ (1 : T₀ ⟶ G).left := by
  have h := push_pow hp (1 : T ⟶ A) 0
  rw [pow_zero, pow_zero, ← MonObj.comp_one (Uτ τ hτ)] at h
  exact h

include hp hτ in
theorem pow_eq_one {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : x.left ≫ φ = τ ≫ x₀.left) {n : ℕ} (h : x₀ ^ n = 1) : x ^ n = 1 := by
  apply pt_ext hp
  rw [pow_rel hp τ hτ hx n, h, one_rel hp τ hτ]

end Pts

section Twist

theorem twist_of_val {S₁ : Scheme.{0}} {A₁ : Over S₁} [GrpObj A₁] {M : LB A₁.left} (hM : M.IsLB) {T : Over S₁}
    {ψ : T ⊗ A₁ ⟶ T ⊗ A₁} {m : T ⊗ A₁ ⟶ A₁} {hm : ψ ≫ snd T A₁ = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb M (K := Fin 2) ![(snd T A₁).left, m.left] ![a, -b])} (hα : α.IsGen)
    {s : LB.Sec (LPow A₁ M b T)} {s' : LB.Sec (LPow A₁ M a T)}
    (h : ∀ (y : (T ⊗ A₁).left) (J : ((T ⊗ A₁).left ⟶ A₁.left) → M.ι), Good M y J →
      sval s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sval s ψ.left y J) :
    IsTwistPull A₁ M ψ m hm a b α s s' := by
  intro j
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (T ⊗ A₁).left ⟶ A₁.left => exists_chart hM (χ y)
  have hG : Good M y I := hI
  dsimp only
  have hz0 : (𝟙 (T ⊗ A₁).left : (T ⊗ A₁).left ⟶ _) y ∈
      LB.wchart M (fun _ : Fin 1 => (snd T A₁).left) (fun _ => j 0) := chart_le_zero A₁ M m j hy
  have hz1 : ψ.left y ∈ LB.wchart M (fun _ : Fin 1 => (snd T A₁).left) (fun _ => j 1) := chart_le_pull A₁ M ψ m hm j hy
  have hψm : ψ.left ≫ (snd T A₁).left = 𝟙 _ ≫ m.left := by rw [Category.id_comp, ← Over.comp_left, hm]
  have eL := (gs_res (𝟙 _) y (chart_le_zero A₁ M m j) hy (s'.f fun _ => j 0)).trans
    (sec_trans s' (𝟙 _) y hz0 (hG.mem (fun _ : Fin 1 => (snd T A₁).left) (𝟙 _)))
  have eA := (gs_unit (𝟙 _) y _ hy (α.s j)).trans
    (congrArg Units.val (gen_trans hα (𝟙 _) y hy (hG.mem ![(snd T A₁).left, m.left] (𝟙 _))))
  have eS := (gs_res (𝟙 _) y (chart_le_pull A₁ M ψ m hm j) hy ((ψ.left.app _).hom (s.f fun _ => j 1))).trans
    ((gs_pull (𝟙 _) ψ.left y _ hz1 (s.f fun _ => j 1)).trans ((congrArg (fun q => gs q y _ (s.f fun _ => j 1))
      (Category.id_comp ψ.left)).trans (sec_trans s ψ.left y hz1 (hG.mem (fun _ : Fin 1 => (snd T A₁).left) ψ.left))))
  have key : trF (L := M) (fun _ : Fin 1 => (snd T A₁).left) (fun _ => a) (𝟙 _) y (fun _ => j 0)
        (fun _ => I (𝟙 _ ≫ (snd T A₁).left)) =
      trF (L := M) ![(snd T A₁).left, m.left] ![a, -b] (𝟙 _) y j
          (fun k => I (𝟙 _ ≫ (![(snd T A₁).left, m.left] : Fin 2 → _) k)) *
        trF (L := M) (fun _ : Fin 1 => (snd T A₁).left) (fun _ => b) ψ.left y (fun _ => j 1)
          (fun _ => I (ψ.left ≫ (snd T A₁).left)) := by
    simp only [trF, Fin.prod_univ_one, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hψm]
    simp only [zpow_neg, _root_.mul_assoc]
    exact (_root_.mul_one _).symm.trans (congrArg (HMul.hMul _) (inv_mul_cancel _).symm)
  refine eL.trans (Eq.trans ?_ (gs_mul (𝟙 _) y _ hy _ _).symm)
  rw [eA, eS]
  have hv : gs (𝟙 _) y (LB.wchart M (fun _ : Fin 1 => (snd T A₁).left) fun _ => I (𝟙 _ ≫ (snd T A₁).left))
        (s'.f fun _ => I (𝟙 _ ≫ (snd T A₁).left)) =
      (gm (𝟙 _) y (LB.wchart M ![(snd T A₁).left, m.left] fun k => I (𝟙 _ ≫ (![(snd T A₁).left, m.left] : Fin 2 → _) k))
        (α.s fun k => I (𝟙 _ ≫ (![(snd T A₁).left, m.left] : Fin 2 → _) k))).val *
      gs ψ.left y (LB.wchart M (fun _ : Fin 1 => (snd T A₁).left) fun _ => I (ψ.left ≫ (snd T A₁).left))
        (s.f fun _ => I (ψ.left ≫ (snd T A₁).left)) := h y I hG
  have kv := congrArg Units.val key
  simp only [Units.val_mul] at kv ⊢
  exact (congrArg (HMul.hMul _) hv).trans ((congrArg (fun q => q * _) kv).trans (by ring))

end Twist

section TwistMove

variable {L₀ : LB G.left} {L₁ : LB A.left}

def TieT (w : LB.Iso L₁ (L₀.pull φ)) (k : ℤ) (s₀ : LB.Sec (LPow G L₀ k T₀)) (s : LB.Sec (LPow A L₁ k T)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J₀ : (Z ⟶ G.left) → L₀.ι) (J : (Z ⟶ A.left) → L₁.ι),
    Good L₀ z J₀ → Good L₁ z J →
    sval s₀ (r ≫ (psiO hp τ hτ).left) z J₀ =
      ((gw w (r ≫ (snd T A).left) z (J₀ ((r ≫ (snd T A).left) ≫ φ)) (J (r ≫ (snd T A).left))) ^ k).val *
        sval s r z J

theorem twist_move (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ))
    {ψA : T ⊗ A ⟶ T ⊗ A} {mA : T ⊗ A ⟶ A} (hmA : ψA ≫ snd T A = mA)
    {ψG : T₀ ⊗ G ⟶ T₀ ⊗ G} {mG : T₀ ⊗ G ⟶ G} {hmG : ψG ≫ snd T₀ G = mG}
    (hψ : ψA.left ≫ (psiO hp τ hτ).left = (psiO hp τ hτ).left ≫ ψG.left)
    (hm : mA.left ≫ φ = (psiO hp τ hτ).left ≫ mG.left) {a b : ℤ}
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, mG.left] ![a, -b])}
    {α₁ : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, mA.left] ![a, -b])} (hα₁ : α₁.IsGen)
    (hαm : PMaps w ![(snd T A).left, mA.left] ![(snd T₀ G).left, mG.left] ![a, -b] α₁ α₀ (psiO hp τ hτ).left)
    {s₀ : LB.Sec (LPow G L₀ b T₀)} {s₀' : LB.Sec (LPow G L₀ a T₀)} (h₀ : IsTwistPull G L₀ ψG mG hmG a b α₀ s₀ s₀')
    {s : LB.Sec (LPow A L₁ b T)} (hs : TieT hp τ hτ w b s₀ s) :
    ∃ s' : LB.Sec (LPow A L₁ a T), IsTwistPull A L₁ ψA mA hmA a b α₁ s s' ∧ TieT hp τ hτ w a s₀' s' := by
  have e2 : ψA.left ≫ (snd T A).left = mA.left := by rw [← Over.comp_left, hmA]
  have hfe : FormEq (Sum.elim (fun _ : Fin 1 => ψA.left ≫ (snd T A).left) ![(snd T A).left, mA.left])
      (Sum.elim (fun _ => b) ![a, -b]) (fun _ : Fin 1 => (snd T A).left) (fun _ => a) := by
    intro U _ hh
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, e2, zpow_neg]
    rw [_root_.mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨s', hs'⟩ := exists_sec hL₁ hfe (pullMulSec s ψA.left α₁ hα₁)
  have hval : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L₁.ι), Good L₁ z J →
      sval s' r z J = (val α₁ r z J).val * sval s (r ≫ ψA.left) z J := fun Z r z J hJ =>
    (hs' Z r z J hJ).trans ((sval_pullMulSec s ψA.left α₁ hα₁ r z hJ).trans (_root_.mul_comm _ _))
  refine ⟨s', twist_of_val hL₁ hα₁ fun y J hJ => (hval _ (𝟙 _) y J hJ).trans (by rw [Category.id_comp]), ?_⟩
  intro Z r z J₀ J hJ₀ hJ
  have hc : ∀ k, (![(snd T A).left, mA.left] : Fin 2 → _) k ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, mG.left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (psi_snd hp τ hτ).symm
    · exact hm
  have t0 := twist_val (A := G) h₀ (r ≫ (psiO hp τ hτ).left) z hJ₀
  have e1 : (r ≫ (psiO hp τ hτ).left) ≫ ψG.left = (r ≫ ψA.left) ≫ (psiO hp τ hτ).left := by
    rw [Category.assoc, ← hψ, Category.assoc]
  have t1 := hs Z (r ≫ ψA.left) z J₀ J hJ₀ hJ
  have t2 := val_pmaps w hc hαm r z J₀ J hJ₀ hJ
  have e3 : (r ≫ ψA.left) ≫ (snd T A).left = r ≫ mA.left := by rw [Category.assoc, e2]
  rw [e1, t1, e3] at t0
  rw [t2] at t0
  rw [t0, hval Z r z J hJ]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  simp only [← _root_.mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv, smul_eq_mul, neg_mul, _root_.one_mul, neg_smul]
  abel

end TwistMove

section MulMove

theorem ofMul_eq' {M : Type} [CommGroup M] {a b : M} (h : Additive.ofMul a = Additive.ofMul b) : a = b :=
  Additive.ofMul.injective h


open ReciprocityTheory.ChartRestriction.G.PullbackSections.MixEnd in
theorem mulGen_move {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E} {S₂ S₂' : Scheme.{0}}
    {t' : SAB H S₂'} {t : SAB H S₂} {f₂ : S₂' ⟶ S₂} (m : SABMap t' t f₂)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (hw : RigIso m w) (N : ℕ)
    (α₀ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![𝟙 t.G.left, (mulA t.G N).left] ![(N : ℤ) ^ 2, -1]))
    (hα : α₀.IsGen) (hN : IsNormMul t.G t.PP.L t.PP.rig N α₀) :
    ∃ α₀' : LB.Gen (LB.LinComb t'.PP.L (K := Fin 2) ![𝟙 t'.G.left, (mulA t'.G N).left] ![(N : ℤ) ^ 2, -1]),
      α₀'.IsGen ∧
      PMaps w ![𝟙 t'.G.left, (mulA t'.G N).left] ![𝟙 t.G.left, (mulA t.G N).left] ![(N : ℤ) ^ 2, -1] α₀' α₀ m.φ ∧
      IsNormMul t'.G t'.PP.L t'.PP.rig N α₀' := by
  have hc : ∀ k, (![𝟙 t'.G.left, (mulA t'.G N).left] : Fin 2 → _) k ≫ m.φ =
      m.φ ≫ (![𝟙 t.G.left, (mulA t.G N).left] : Fin 2 → _) k := by
    intro k; fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Category.id_comp, Category.comp_id]
    · exact mulA_push m.cart N
  obtain ⟨α₀', g', hm⟩ := exists_gen_move t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw.1) _ _ ![(N : ℤ) ^ 2, -1] m.φ
    hc α₀ hα
  refine ⟨α₀', g', hm, ?_⟩
  have hr := rig_pmaps m w hw
  have hce : ∀ k : PUnit.{1}, (fun _ => eSec t'.G) k ≫ m.φ = m.cm.e ≫ (fun _ => eSec t.G) k :=
    fun _ => m.cm.e_comm
  have eta1 : (η[t'.G] : 𝟙_ (Over S₂') ⟶ t'.G) = 1 := by
    show η[t'.G] = toUnit _ ≫ η[t'.G]
    rw [toUnit_unique (toUnit (𝟙_ (Over S₂'))) (𝟙 _), Category.id_comp]
  have hmul : eSec t'.G ≫ (mulA t'.G N).left = eSec t'.G := by
    show η[t'.G].left ≫ (𝟙 t'.G ^ N).left = η[t'.G].left
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, eta1, one_pow]
  unfold IsNormMul
  refine corr_of_val t'.PP.isLB fun y J hJ => ?_
  choose J₀ hJ₀ using fun χ : (𝟙_ (Over S₂')).left ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  have hJ₀' : Good t.PP.L y J₀ := hJ₀
  have c0 := val_corr hJ₀' hN m.cm.e
  rw [val_pull hJ₀', val_mul hJ₀', val_rigPow, val_inv] at c0
  have p1 := val_pmaps' w hc hm (eSec t'.G) y J₀ J hJ₀' hJ
  have p2 := val_pmaps' w hce hr (𝟙 _) y J₀ J hJ₀' hJ
  rw [show eSec t'.G ≫ m.φ = m.cm.e ≫ eSec t.G from m.cm.e_comm, c0] at p1
  simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Category.comp_id, hmul] at p1
  simp only [Finset.univ_unique, Finset.prod_singleton, Category.id_comp, zpow_one] at p2
  rw [val_pull hJ, val_mul hJ, val_rigPow, val_inv, Category.id_comp]
  rw [p2] at p1
  rw [eq_inv_mul_of_mul_eq p1.symm]
  apply ofMul_eq'
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, smul_eq_mul, neg_mul, _root_.one_mul, neg_smul, mul_zpow, zsmul_eq_mul]
  abel

end MulMove

end ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

section Transl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S}

theorem translPt_one' : translPt A (1 : T ⟶ A) = snd T A := by
  rw [translPt_eq, MonObj.comp_one, _root_.one_mul]

theorem transl_translPt (y x : T ⟶ A) :
    (translT A y).left ≫ (translPt A x).left = (translPt A (y * x)).left := by
  rw [← Over.comp_left]
  congr 1
  simp only [translPt_eq, translT, MonObj.comp_mul, lift_snd, lift_fst_assoc]
  rw [_root_.mul_left_comm, ← _root_.mul_assoc]

theorem transl_pow_succ (x : T ⟶ A) (j : ℕ) :
    (translT A (x ^ j)).left ≫ (translPt A x).left = (translPt A (x ^ (j + 1))).left := by
  rw [transl_translPt, pow_succ]

theorem transl_inv_translPt (x : T ⟶ A) : (translT A x⁻¹).left ≫ (translPt A x).left = (snd T A).left := by
  rw [transl_translPt, inv_mul_cancel, translPt_one']

theorem negT_snd' : (negT A T).left ≫ (snd T A).left = (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, negT, lift_snd]

theorem negT_translPt (x : T ⟶ A) :
    (negT A T).left ≫ (translPt A x).left = (translT A x⁻¹).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  have e1 : negT A T ≫ translPt A x = (fst T A ≫ x) * (snd T A)⁻¹ := by
    rw [translPt_eq, MonObj.comp_mul, negT, lift_fst_assoc, lift_snd]
    rfl
  have e2 : translT A x⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) = (fst T A ≫ x) * (snd T A)⁻¹ := by
    rw [← Category.assoc, translT, lift_snd, translPt_eq]
    show ((fst T A ≫ x⁻¹) * snd T A)⁻¹ = _
    rw [mul_inv, GrpObj.comp_inv, inv_inv]
  rw [e1, e2]

end Transl

section Move

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

include hp hτ in
theorem inv_rel {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : x.left ≫ φ = τ ≫ x₀.left) :
    (x⁻¹).left ≫ φ = τ ≫ (x₀⁻¹).left := by
  show (x ≫ GrpObj.inv).left ≫ φ = τ ≫ (x₀ ≫ GrpObj.inv).left
  rw [push_inv hp x, push_eq hp τ hτ hx]
  try rfl

theorem symLift_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) {k : ℤ} {n : ℕ}
    {x₀ : T₀ ⟶ G} {θ₀ : ThetaGrp G L₀ k T₀} (h₀ : SymLift G L₀ k n x₀ θ₀) (hn : x₀ ^ n = 1) {x : T ⟶ A}
    (hx : x.left ≫ φ = τ ≫ x₀.left) :
    ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left := by
  obtain rfl := h₀.pt_eq
  obtain ⟨θ, rfl, hm⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx.symm
  have hxn : θ.pt ^ n = 1 := pow_eq_one hp τ hτ hx hn
  have hc : ∀ i, (![(snd T A).left, (translPt A θ.pt).left] : Fin 2 → _) i ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, (translPt G θ₀.pt).left] : Fin 2 → _) i := fun i => by
    fin_cases i
    · exact (psi_snd hp τ hτ).symm
    · exact (psi_tr hp τ hτ θ.pt θ₀.pt hx.symm).symm
  obtain ⟨nu₀, gnu₀, cnu₀⟩ := h₀.sym
  have hcn : ∀ i, (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) i ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, (snd T₀ G ≫ (GrpObj.inv : G ⟶ G)).left] : Fin 2 → _) i := fun i => by
    fin_cases i
    · exact (psi_snd hp τ hτ).symm
    · exact snd_inv_push hp τ hτ
  obtain ⟨nu, gnu, hmn⟩ := exists_gen_move hL₀ hL₁ w ((isGen_iff w).1 hw) _ _ ![k, -k] (psiO hp τ hτ).left hcn nu₀ gnu₀
  refine ⟨θ, ⟨rfl, ?_, nu, gnu, ?_⟩, hm⟩
  · refine corr_of_val hL₁ fun y J hJ => ?_
    choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
    have hG : Good L₀ y J₀ := hJ₀
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ((T ⊗ A).left.presheaf.stalk y)ˣ, ∀ j, g j =
        gw w (translPt A (θ.pt ^ j)).left y (J₀ ((translPt A (θ.pt ^ j)).left ≫ φ)) (J (translPt A (θ.pt ^ j)).left) ^ k :=
      ⟨_, fun _ => rfl⟩
    have key : ∀ j : ℕ, val θ₀.φ ((psiO hp τ hτ).left ≫ (translT G (θ₀.pt ^ j)).left) y J₀ =
        g j / g (j + 1) * val θ.φ (𝟙 _ ≫ (translT A (θ.pt ^ j)).left) y J := fun j => by
      rw [← psi_transl hp τ hτ _ _ (pow_rel hp τ hτ hx j).symm, val_pmaps w hc hm _ y J₀ J hG hJ, Category.id_comp]
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [transl_snd, transl_pow_succ, zpow_neg, div_eq_mul_inv, hg, hg]
    have c := val_corr hG h₀.pow_eq (psiO hp τ hτ).left
    rw [val_powGenT θ₀ n _ y hG, val_one] at c
    rw [val_powGenT θ n _ y hJ, val_one]
    rw [Fin.prod_univ_eq_prod_range (fun j => val θ₀.φ ((psiO hp τ hτ).left ≫ (translT G (θ₀.pt ^ j)).left) y J₀)] at c
    rw [Fin.prod_univ_eq_prod_range (fun j => val θ.φ (𝟙 _ ≫ (translT A (θ.pt ^ j)).left) y J)]
    simp only [key, Finset.prod_mul_distrib, Finset.prod_range_div'] at c
    have gn : g n = g 0 := by rw [hg, hg, hxn, pow_zero]
    rwa [gn, div_self', _root_.one_mul] at c
  · refine corr_of_val hL₁ fun y J hJ => ?_
    choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
    have hG : Good L₀ y J₀ := hJ₀
    have c := val_corr hG cnu₀ (psiO hp τ hτ).left
    rw [val_symGen θ₀ nu₀ _ y hG, val_one] at c
    rw [val_symGen θ nu _ y hJ, val_one]
    have v1 := val_pmaps w hc hm (translT A θ.pt⁻¹).left y J₀ J hG hJ
    have v2 := val_pmaps w hcn hmn (𝟙 _) y J₀ J hG hJ
    have v3 := val_pmaps w hc hm (negT A T).left y J₀ J hG hJ
    have v4 := val_pmaps w hcn hmn (translT A θ.pt⁻¹).left y J₀ J hG hJ
    simp only [Category.id_comp] at v2 ⊢
    rw [← psi_transl hp τ hτ θ.pt⁻¹ θ₀.pt⁻¹ (inv_rel hp τ hτ hx).symm, ← negT_push hp τ hτ, v1, v2, v3, v4] at c
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at c
    rw [transl_inv_translPt, negT_snd', negT_translPt] at c
    apply Additive.ofMul.injective
    have b := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, zpow_neg] at b ⊢
    linear_combination (norm := abel) b

end Move

end ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove
end
end

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR

theorem snd_pow_left {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) (N : ℕ) :
    (snd T A ^ N).left = (snd T A).left ≫ (mulA A N).left := by
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id]

theorem sval_zc {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    sval (zCast A h F) r z J = sval F r z J := by
  subst h; rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem vtOver_move {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (hw : RigIso m w) {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) (N : ℕ) {ok : (T₀ ⟶ t.G) → Prop} (hok : ∀ u, ok u → u ^ (N ^ 2) = 1)
    {s₀ : LB.Sec (LPow t.G t.PP.L 1 T₀)} {tt : T₀ ⟶ t.G} {F : LB.Sec (LPow t.G t.PP.L ((N : ℤ) ^ 2) T₀)}
    (h : IsVtOver t.G t.PP N ok s₀ tt F) {s : LB.Sec (LPow t'.G t'.PP.L 1 T)} (hs : TieT m.cart τ hτ w 1 s₀ s) :
    ∃ F' : LB.Sec (LPow t'.G t'.PP.L ((N : ℤ) ^ 2) T),
      IsVtOver t'.G t'.PP N (fun u => u ^ (N ^ 2) = 1) s (liftPt m.cart τ hτ tt) F' ∧
        TieT m.cart τ hτ w ((N : ℤ) ^ 2) F F' := by
  obtain ⟨t₀', α₀, α, s₁, U, ht, o, g₀, n₀, cα, tw, sl, ac⟩ := h
  have h1 : (liftPt m.cart τ hτ t₀').left ≫ m.φ = τ ≫ t₀'.left := liftPt_left m.cart τ hτ t₀'
  have ht1 : liftPt m.cart τ hτ t₀' ^ N = liftPt m.cart τ hτ tt :=
    pt_ext m.cart ((pow_rel m.cart τ hτ h1 N).trans (by rw [ht]; exact (liftPt_left m.cart τ hτ tt).symm))
  have o1 : liftPt m.cart τ hτ t₀' ^ (N ^ 2) = 1 := pow_eq_one m.cart τ hτ h1 (hok _ o)
  obtain ⟨α₀', g₀', pm₀, n₀'⟩ := mulGen_move m w hw N α₀ g₀ n₀
  have eα : ∀ k, (![(snd T₀ t.G).left, (snd T₀ t.G ^ N).left] : Fin 2 → _) k =
      (snd T₀ t.G).left ≫ (![𝟙 t.G.left, (mulA t.G N).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.comp_id _).symm
    · exact snd_pow_left _ _ _
  obtain ⟨α₁, gα₁, Hα₁⟩ := exists_gen_pull (L := t.PP.L) ![𝟙 t.G.left, (mulA t.G N).left] ![(N : ℤ) ^ 2, -1] α₀
    (snd T₀ t.G).left _ eα
  have gα := gα₁ g₀
  have vα : ∀ y J, Good t.PP.L y J → val α (𝟙 _) y J = val α₁ (𝟙 _) y J := fun y J hJ =>
    (val_corr hJ cα _).trans ((val_pull hJ _ _ _).trans (val_of_pull eα Hα₁ _ y hJ).symm)
  have tw' : IsTwistPull t.G t.PP.L (mulT t.G T₀ N) (snd T₀ t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α₁ s₀ s₁ :=
    twist_of_val t.PP.isLB gα fun y J hJ => (twist_val tw (𝟙 _) y hJ).trans (by rw [vα y J hJ, Category.id_comp])
  obtain ⟨α', gα', pmα, cα'⟩ := MixEnd.genSnd_move m.cart τ hτ t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw.1)
    (mulA t'.G N).left (mulA t.G N).left (mulA_push m.cart N) ![(N : ℤ) ^ 2, -1] α₀' α₀ pm₀ (snd T t'.G ^ N)
    (snd T₀ t.G ^ N) (snd_pow_left _ _ _) (snd_pow_left _ _ _) _ gα
    (corr_of_val t.PP.isLB fun y J hJ => (val_of_pull eα Hα₁ _ y hJ).trans (val_pull hJ _ _ _).symm)
  obtain ⟨s₁', tw1, hs1⟩ := twist_move m.cart τ hτ t'.PP.isLB w (ψA := mulT t'.G T N) (mA := snd T t'.G ^ N)
    (lift_snd _ _) (mulT_push m.cart τ hτ N) (snd_pow_push m.cart τ hτ N) gα' pmα tw' hs
  obtain ⟨U', sl', pmU⟩ := symLift_move m.cart τ hτ t.PP.isLB t'.PP.isLB w hw.1 sl (hok _ o) h1
  have hxU : τ ≫ U.pt.left = U'.pt.left ≫ m.φ := by rw [sl.pt_eq, sl'.pt_eq]; exact h1.symm
  obtain ⟨F', ac', hF⟩ := twist_move m.cart τ hτ t'.PP.isLB w (ψA := translT t'.G U'.pt)
    (mA := translPt t'.G U'.pt) (lift_snd _ _) (psi_transl m.cart τ hτ U'.pt U.pt hxU)
    (psi_tr m.cart τ hτ U'.pt U.pt hxU).symm U'.isGen pmU ac hs1
  exact ⟨F', ⟨liftPt m.cart τ hτ t₀', α₀', α', s₁', U', ht1, o1, g₀', n₀', cα', tw1, sl', ac'⟩, hF⟩

theorem vtMoveSt : VtMoveSt := by
  intro E _ _ _ H X₀ t₀ K _ x tK m1 w1 hw N ok s tt F hF hok sK hsK
  have hfst : ∀ {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over (Sp K)) ⊗ tK.G).left),
      r ≫ (fst (𝟙_ (Over (Sp K))) tK.G).left ≫ (𝟙_ (Over (Sp K))).hom = (r ≫ (snd _ tK.G).left) ≫ tK.G.hom := by
    intro Z r
    rw [Over.w (fst _ _), Category.assoc, Over.w (snd _ _)]
  have hs : TieT m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl w1 1 s (zCast tK.G Nat.cast_one sK) := by
    intro Z r z J₀ J hJ₀ hJ
    have e := hsK Z (r ≫ (snd _ tK.G).left) (r ≫ (psiO m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl).left) r
      (by rw [Category.assoc, psi_snd, Category.assoc])
      (by rw [Category.assoc, psi_fst]; exact hfst r) rfl z J₀ J hJ₀ hJ
    rw [sval_zc, Category.comp_id] at e
    rw [sval_zc, e, zpow_one, pow_one]
    rfl
  obtain ⟨F', hV, hT⟩ := vtOver_move m1 w1 hw (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl N hok hF hs
  refine ⟨_, F', hV, fun Z r zp zp' h1 h2 h3 z J J' hJ hJ' => ?_⟩
  subst h3
  obtain rfl : zp = zp' ≫ (psiO m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl).left := by
    refine hom_ext₀ ?_ ?_
    · rw [Category.assoc, psi_fst, h2, hfst]
    · rw [Category.assoc, psi_snd, h1, Category.assoc]
  rw [sval_zc, sval_zc, hT Z zp' z J J' hJ hJ', Category.comp_id]
  congr 1

end ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove
