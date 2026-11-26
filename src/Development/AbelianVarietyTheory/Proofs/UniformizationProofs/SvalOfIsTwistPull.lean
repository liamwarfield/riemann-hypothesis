module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Definitions.Uniformization.FinrankComplexReal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaLin

theorem gs_scal_comp {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y)
    (z : Z) (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem exists_linearEquiv {F : Type} [CommRing F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) (pr m : Y ⟶ X) (τ σ : Y ⟶ Y) (hm : τ ≫ pr = m) (h₁ : σ ≫ τ = 𝟙 Y)
    (h₂ : τ ≫ σ = 𝟙 Y) (hq : τ ≫ q = q) (k : ℤ)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![k, -k])) (hu : u.IsGen) :
    ∃ Φ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) ≃ₗ[F]
        SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ v (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval (Φ v).sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := by
  have ex : ∀ v : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∃ w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval w.sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := fun v => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k)
      (fun U _ h => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
          hm, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
      (pullMulSec v.sec τ u hu)
    exact ⟨SecMod.mk q s', fun Z r z J hJ =>
      (hs' Z r z J hJ).trans ((sval_pullMulSec _ _ u hu r z hJ).trans (_root_.mul_comm _ _))⟩
  choose f hf using ex
  have ext : ∀ v w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      (∀ y J, Good L y J → sval v.sec (𝟙 Y) y J = sval w.sec (𝟙 Y) y J) → v = w :=
    fun v w h => SecMod.ext (sec_ext_val hL h)
  let Φ₀ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) →ₗ[F]
      SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) :=
    { toFun := f
      map_add' := fun v w => ext _ _ fun y J hJ => by
        rw [SecMod.sval_add hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_add hJ, mul_add]
      map_smul' := fun c v => ext _ _ fun y J hJ => by
        rw [RingHom.id_apply, SecMod.sval_smul hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_smul hJ,
          gs_scal_comp q (𝟙 Y ≫ τ), Category.assoc, hq, Category.id_comp q, mul_left_comm] }
  refine ⟨LinearEquiv.ofBijective Φ₀ ⟨fun v w h => ext _ _ fun y J hJ => ?_, fun w => ?_⟩, hf⟩
  · have e : f v = f w := h
    have := (hf v _ σ y J hJ).symm.trans (e ▸ hf w _ σ y J hJ)
    rwa [h₁, Units.mul_right_inj] at this
  · have hv := DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _ hu) σ
    have h₃ : σ ≫ m = pr := by rw [← hm, ← Category.assoc, h₁, Category.id_comp]
    obtain ⟨s, hs⟩ := exists_sec (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k) hL (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        h₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv, mul_inv_cancel_left])
      (pullMulSec w.sec σ _ hv)
    refine ⟨SecMod.mk q s, ext _ _ fun y J hJ => (hf _ _ _ y J hJ).trans ?_⟩
    change (val u (𝟙 Y) y J).val * sval s (𝟙 Y ≫ τ) y J = sval w.sec (𝟙 Y) y J
    rw [hs _ _ y J hJ, sval_pullMulSec _ σ _ hv _ y hJ, val_pull hJ, val_inv, Category.assoc, h₂,
      Category.comp_id, mul_left_comm, Units.mul_inv, _root_.mul_one]

section Twist

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
  {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}

theorem sval_of_isTwistPull {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' r z J = (val α r z J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hz := hJ.mem ![(snd T A).left, m.left] r
  have key : ∀ j : Fin 2 → L.ι, r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j)).val *
          gs (r ≫ ψ.left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j hz =>
    (gs_res r z _ hz _).symm.trans ((congrArg (gs r z _) (H j)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hz _) ((gs_res r z _ hz _).trans
        (gs_pull r ψ.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
          (chart_le_pull A L ψ m hm j hz) _)))))
  have e₁ := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J
    (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, e])
  exact (key _ hz).trans (congrArg _ e₁.symm)

theorem isTwistPull_of_sval (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by
  intro j
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have h0 := chart_le_zero A L m j hy
  have h1 := chart_le_pull A L ψ m hm j hy
  refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hy _) ((gs_res _ y _ hy _).trans
      (gs_pull _ ψ.left y _ h1 _)))).symm)
  refine (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y h0
    (Good.mem hJ _ _)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val (gen_trans hα (𝟙 _) y hy (Good.mem hJ _ _)))
    (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y h1
    (Good.mem hJ _ _))).symm
  refine (congrArg _ (H y J hJ)).trans ?_
  rw [Units.val_mul]
  refine Eq.trans ?_ (_root_.mul_mul_mul_comm _ _ _ _)
  rw [← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e' : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, e]
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, zpow_neg]
  rw [e']
  exact (inv_mul_cancel_right _ _).symm

end Twist

section Transl

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem lift_translT {T' : Over S} (ρ : T' ⟶ T) (x : T' ⟶ A) (c : T ⟶ A) :
    lift ρ x ≫ translT A c = lift ρ ((ρ ≫ c) * x) := by
  have e : translPt A c = (fst T A ≫ c) * snd T A := rfl
  rw [translT, comp_lift, lift_fst, e, MonObj.comp_mul, lift_fst_assoc, lift_snd]

theorem translT_comp (c d : T ⟶ A) (h : d * c = 1) : translT A c ≫ translT A d = 𝟙 _ := by
  have e : translPt A c = (fst T A ≫ c) * snd T A := rfl
  rw [translT, lift_translT, e, ← _root_.mul_assoc, ← MonObj.comp_mul, h, MonObj.comp_one, _root_.one_mul,
    lift_fst_snd]

end Transl

theorem main : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) (θ : ThetaGrp P.A P.L (k : ℤ) (Over.mk p)), ∃ Φ : EA P p k ≃ₗ[F] EA P p k, (∀ v, IsActOf P.A P.L (k : ℤ) θ v.sec (Φ v).sec) ∧ (∀ v v', IsActOf P.A P.L (k : ℤ) θ v v' → v' = (Φ (SecMod.mk _ v)).sec) ∧ ∀ (v : EA P p k) (T : Over S) (ρ : T ⟶ Over.mk p) (x : T ⟶ P.A) (z : T.left) (J), Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) (Φ v).sec (lift ρ x).left z J = (val (L := P.L) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![(k : ℤ), -(k : ℤ)]) θ.φ (lift ρ x).left z J).val * sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := by
  intro S P F _ p k θ
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv (F := F) P.isLB (fst (Over.mk p) P.A).left (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (translT P.A θ.pt⁻¹).left
    (by rw [← Over.comp_left, translT, lift_snd])
    (by rw [← Over.comp_left, translT_comp _ _ _ (mul_inv_cancel _), Over.id_left])
    (by rw [← Over.comp_left, translT_comp _ _ _ (inv_mul_cancel _), Over.id_left])
    (((Over.comp_left _ _ _ _ _).symm.trans (by rw [translT, lift_fst]))) (k : ℤ) θ.φ θ.isGen
  refine ⟨Φ, fun v => isTwistPull_of_sval P.A P.isLB θ.isGen fun y J hJ => hΦ v _ _ y J hJ, fun v v' h => ?_,
    fun v T ρ x z J hJ => ?_⟩
  · exact DVR.SecOps.sec_ext (sec_ext_val P.isLB fun y J hJ =>
      (sval_of_isTwistPull P.A h (𝟙 _) y hJ).trans (hΦ (SecMod.mk _ v) _ _ y J hJ).symm)
  · refine (hΦ v _ _ z J hJ).trans ?_
    rw [← Over.comp_left, lift_translT]
    rfl

end GlobalTheory.ThetaLin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.PsiScalUnit

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ w * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res r z le trivial _).symm

variable {V : Type} [CommRing V] [IsDomain V]

def ev (z : (TK V).left) : FractionRing V →+* (TK V).left.presheaf.stalk z :=
  ((TK V).left.presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

theorem ev_eq (z : (TK V).left) (k : FractionRing V) :
    gs (𝟙 _) z ⊤ (scal (𝟙 (TK V) : TK V ⟶ TK V).left k) = ev z k := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem ev_unit (z : (TK V).left) (w : Γ(Spec (CommRingCat.of V), ⊤)ˣ) :
    ∃ u : Vˣ, (gm (jK V) z ⊤ w).val = ev z (algebraMap V (FractionRing V) u.val) := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom w, ?_⟩
  rw [← gs_unit _ z ⊤ trivial, gs_eq _ z ⊤ trivial]
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply] at e
  exact congrArg ((TK V).left.presheaf.germ ⊤ z trivial).hom e.symm

theorem c_left (D : DegPre V) (χ : D.X) : (D.c χ).left = (DVR.cP D (𝟙_ _) χ).left := by
  rw [DVR.cP, toUnit_unit, Category.id_comp]

theorem exists_setup (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) :
    ∃ (z : (TK V).left) (J : _), Good D.P.L z J ∧ ∀ χ, val (D.psi χ) (𝟙 _) z J =
      Units.map (ev z).toMonoidHom (a χ) * val (ga χ) (toUnit (TK V)).left z J := by
  obtain ⟨z⟩ : Nonempty (TK V).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  choose J hJ using fun χ : (TK V).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  refine ⟨z, J, hJ, fun χ => Units.ext ?_⟩
  exact ((h χ).2 (TK V) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl)

theorem ev_inj (z : (TK V).left) : Function.Injective (ev z) := (ev z).injective

theorem cub_part (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) (hB : D.TauBimult) (x y w : D.X) :
    ∃ u : Vˣ, (a (x + y + w) * a x * a y * a w).val =
      algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + w) * a (y + w)).val := by
  obtain ⟨z, J, hJ, hψ⟩ := exists_setup D ga a h
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (toUnit (TK V)).left z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 x y w)) (𝟙 _) z J =
      cubV D.cub z J (DVR.cP D _ x) (DVR.cP D _ y) (DVR.cP D _ w) := by
    refine (val_cub D.cub (𝟙 (TK V)) hJ (DVR.cP D _ x) (DVR.cP D _ y) (DVR.cP D _ w)).trans ?_
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB x y w) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [vc, vτ, vτ, vτ, vρ] at e
  simp only [hψ] at e
  obtain ⟨W, hW⟩ := exists_ratio D.P.isLB (fun U _ f => by
      have p₁ := prod_cub (DVR.cP D (𝟙_ _) x) (DVR.cP D _ y) (DVR.cP D _ w) f
      have q : eSec D.P.A = (1 : 𝟙_ _ ⟶ D.P.A).left := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
      refine Eq.trans ?_ (DVR.prod_sum₂ (U := U) _ rfl p₁).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c_left, DVR.cPoint_add, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (x + y)).1 (h (x + w)).1) (h (y + w)).1)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (x + y + w)).1 (h x).1) (h y).1) (h w).1)
      D.rig_gen) (DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε _ D.cub.isGen
        (lift (DVR.cP D (𝟙_ _) x) (lift (DVR.cP D (𝟙_ _) y) (DVR.cP D (𝟙_ _) w))).left))
  have e₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)).symm.trans
    ((hW _ (toUnit (TK V)).left z J hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) rfl)) rfl))
      (val_cub D.cub (toUnit (TK V)) hJ _ _ _)))))
  rw [DVR.comp_cP, DVR.comp_cP, DVR.comp_cP] at e₂
  obtain ⟨u, hu⟩ := ev_unit z W
  refine ⟨u, ev_inj z ?_⟩
  rw [map_mul (ev z) (algebraMap _ _ _), ← hu]
  have : Units.map (ev z).toMonoidHom (a (x + y + w) * a x * a y * a w) =
      gm (toUnit (TK V)).left z ⊤ W * Units.map (ev z).toMonoidHom (a (x + y) * a (x + w) * a (y + w)) := by
    simp only [map_mul]
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e
    have a₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂
  exact congrArg Units.val this

theorem even_part (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) (hE : D.PsiEven) (x : D.X) :
    ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val := by
  obtain ⟨z, J, hJ, hψ⟩ := exists_setup D ga a h
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hE x) (𝟙 _))
  rw [hψ, hψ, Category.id_comp] at e
  obtain ⟨W, hW⟩ := exists_ratio D.P.isLB (fun U _ f => by
      have q : (D.c x).left ≫ (ι[D.P.A]).left = (D.c (-x)).left := by
        have h0 : DVR.cP D (𝟙_ _) 0 = 1 := by simpa using DVR.cPoint_nsmul D (𝟙_ _) 0 x
        have h1 := DVR.cPoint_add D (𝟙_ _) (-x) x
        rw [neg_add_cancel, h0] at h1
        rw [c_left, c_left, eq_inv_of_mul_eq_one_left h1.symm, ← Over.comp_left]
        rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (h x).1 (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (-x)).1 (DVR.pullGen_isGen D.P.L _ _ _ D.sym_gen (D.c x).left))
  have e₂ := (hW _ (toUnit (TK V)).left z J hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))
  obtain ⟨u, hu⟩ := ev_unit z W
  refine ⟨u, ev_inj z ?_⟩
  rw [map_mul (ev z) (algebraMap _ _ _), ← hu]
  have : Units.map (ev z).toMonoidHom (a (-x)) =
      gm (toUnit (TK V)).left z ⊤ W * Units.map (ev z).toMonoidHom (a x) := by
    have e' : Units.map (ev z).toMonoidHom (a (-x)) * val (ga (-x)) (toUnit (TK V)).left z J *
        val D.sym ((toUnit (TK V)).left ≫ (D.c x).left) z J =
        Units.map (ev z).toMonoidHom (a x) * val (ga x) (toUnit (TK V)).left z J := e
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e'
    have a₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂
  exact congrArg Units.val this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → (D.TauBimult → ∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) ∧ (D.PsiEven → ∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) :=
  fun _ _ _ _ D ga a h => ⟨cub_part D ga a h, even_part D ga a h⟩

end GlobalTheory.PsiScalUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnitsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.psiScalars_relations_up_to_baseUnits : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → (D.TauBimult → ∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) ∧ (D.PsiEven → ∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) := by
  first | exact @GlobalTheory.PsiScalUnit.main | exact GlobalTheory.PsiScalUnit.main | (intros; apply GlobalTheory.PsiScalUnit.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem sval_eq_zero_of_local_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, d.f j = 0) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) : sval d r z J = 0 := by
  have e : gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) 0 = 0 := by
    rw [gs_eq r z _ (hJ.mem φ r), map_zero, map_zero]
  exact (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans e

theorem appTop_field_point_injective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e : (toUnit (TF (R := R) F)).left =
      Spec.map (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    have := Over.w (toUnit (TF (R := R) F))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.comp_id _).symm.trans this
  rw [e]
  have hi : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))
  have n := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))
  have hb : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have hc := hi.comp hb
  intro a b hab
  apply hc
  have na := congrArg (fun q => q.hom a) n
  have nb := congrArg (fun q => q.hom b) n
  exact na.symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom hab).trans nb)

theorem pullB_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), PullB D F (toUnit _) k f s → ∀ α, ((∃ j, (s α).f j ≠ 0) ↔ ∃ j, (f α).f j ≠ 0) := by
  intro R _ _ D F _ _ k f s h α
  have := D.P.smoothDim
  have : Smooth D.P.A.hom := SmoothOfRelativeDimension.smooth D.P.g _
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of F)))
  rw [← not_iff_not]
  simp only [not_exists, not_not]
  constructor
  · intro hs
    refine sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A _ _ (toUnit (TF (R := R) F))
      (appTop_field_point_injective R F) _ D.P.L D.P.isLB _ _ _ (f α) fun z J hJ => ?_
    exact (h α z J hJ).symm.trans (sval_eq_zero_of_local_eq_zero (s α) hs _ z J hJ)
  · intro hf
    refine sec_eq_zero_of_sval_eq_zero_of_app_injective (𝟙 _) (fun U a b hab => hab) D.P.L D.P.isLB _ _ (s α)
      fun z J hJ => ?_
    exact (h α z J hJ).trans (sval_eq_zero_of_local_eq_zero (f α) hf _ z J hJ)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIffStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackSectionFamily_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), PullB D F (toUnit _) k f s → ∀ α, ((∃ j, (s α).f j ≠ 0) ↔ ∃ j, (f α).f j ≠ 0) := by
  first | exact @GlobalTheory.pullB_ne_zero_iff | exact GlobalTheory.pullB_ne_zero_iff | (intros; apply GlobalTheory.pullB_ne_zero_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionOverZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.GtCount

open GlobalTheory.TorusExt

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.GtCount.card_torsion_eq_mul {G B : Type} [AddCommGroup G] [AddCommGroup B] (p : G →+ B) (n : ℕ)
    (h : ∀ b : B, n • b = 0 → ∃ g, p g = b ∧ n • g = 0) :
    Nat.card {g : G // n • g = 0} = Nat.card {b : B // n • b = 0} * Nat.card {g : G // n • g = 0 ∧ p g = 0} := by
  have h' : ∀ b : {b : B // n • b = 0}, ∃ g, p g = b ∧ n • g = 0 := fun b => h b b.2
  choose s hs using h'
  have hp : ∀ g : {g : G // n • g = 0}, n • p g = 0 := fun g => by
    rw [← map_nsmul, g.2, map_zero]
  have hsec : ∀ (b b' : {b : B // n • b = 0}), (b : B) = b' → s b = s b' := by
    rintro b b' hbb
    rw [Subtype.ext hbb]
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun g => (⟨p g, hp g⟩, ⟨g - s ⟨p g, hp g⟩, ?_, ?_⟩)
      invFun := fun x => ⟨s x.1 + x.2.1, by rw [nsmul_add, (hs _).2, x.2.2.1, add_zero]⟩
      left_inv := fun g => Subtype.ext (add_sub_cancel _ _)
      right_inv := fun x => ?_ }
  · rw [nsmul_sub, g.2, (hs _).2, sub_zero]
  · rw [map_sub, (hs _).1, sub_self]
  · have hx : p (s x.1 + x.2.1) = x.1 := by rw [map_add (f := _), (hs _).1, x.2.2.2, add_zero]
    refine Prod.ext (Subtype.ext hx) (Subtype.ext ?_)
    change s x.1 + x.2.1 - s ⟨p (s x.1 + x.2.1), _⟩ = x.2.1
    rw [hsec ⟨p (s x.1 + x.2.1), _⟩ x.1 hx, add_sub_cancel_left]

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.GtCount.card_torus_torsion (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F]
    [IsAlgClosed F] (n : ℕ) (hn : (n : F) ≠ 0) :
    Nat.card {t : Multiplicative X →* Fˣ // t ^ n = 1} = n ^ Module.finrank ℤ X := by
  haveI : NeZero (n : F) := ⟨hn⟩
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  have hroots : Nat.card (rootsOfUnity n F) = n := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F n
    exact hζ.card_rootsOfUnity
  let b := Module.Free.chooseBasis ℤ X
  let e₁ : {t : Multiplicative X →* Fˣ // t ^ n = 1} ≃ (Multiplicative X →* rootsOfUnity n F) :=
    { toFun := fun t => (t.1).codRestrict (rootsOfUnity n F) fun x => by
        have := DFunLike.congr_fun t.2 x
        simpa [MonoidHom.pow_apply, mem_rootsOfUnity] using this
      invFun := fun s => ⟨(rootsOfUnity n F).subtype.comp s, by
        refine MonoidHom.ext fun x => ?_
        simpa [MonoidHom.pow_apply] using (mem_rootsOfUnity _ _).1 (s x).2⟩
      left_inv := fun t => Subtype.ext (MonoidHom.ext fun x => rfl)
      right_inv := fun s => MonoidHom.ext fun x => Subtype.ext rfl }
  let e := e₁.trans (MonoidHom.toAdditiveRight.trans
    ((addMonoidHomLequivInt ℤ).toEquiv.trans (b.constr ℤ).symm.toEquiv))
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_congr Additive.toMul, hroots,
    Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

attribute [local instance] gtGroup

attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.gtTors_iff {R : Type} [CommRing R] [IsDomain R] {D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (n : ℕ) (g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F) : _root_.GlobalTheory.UU.GtTors D n g ↔ n • g = 0 := by
  unfold _root_.GlobalTheory.UU.GtTors
  simp [_root_.GlobalTheory.TorusExt.isNsmul_iff_eq, _root_.GlobalTheory.TorusExt.isZero_iff_eq]

attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.card_torsion_over_zero {R : Type} [CommRing R] [IsDomain R] (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] (n : ℕ) (hn : (n : F) ≠ 0) :
    Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // n • g = 0 ∧ g.b = 1} = n ^ D.rank := by
  let φ := _root_.GlobalTheory.TorusExt.torusPt D F
  have hinj : Function.Injective φ := _root_.GlobalTheory.TorusExt.torusPt_injective
  let e : {t : Multiplicative D.X →* Fˣ // t ^ n = 1} → {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // n • g = 0 ∧ g.b = 1} :=
    fun t => ⟨φ (Additive.ofMul t.1), by
      rw [← map_nsmul, ← ofMul_pow, t.2, ofMul_one, map_zero], _root_.GlobalTheory.TorusExt.torusPt_b _⟩
  have he : Function.Bijective e := by
    refine ⟨fun t t' htt => Subtype.ext ?_, fun g => ?_⟩
    · exact Additive.ofMul.injective (hinj (congrArg Subtype.val htt))
    · obtain ⟨t, ht⟩ := _root_.GlobalTheory.TorusExt.exists_torusPt_eq g.2.2
      refine ⟨⟨t, ?_⟩, Subtype.ext ht.symm⟩
      apply Additive.ofMul.injective
      apply hinj
      rw [ofMul_pow, map_nsmul, ← ht, g.2.1, ofMul_one, map_zero]
  rw [← Nat.card_congr (Equiv.ofBijective e he), _root_.GlobalTheory.GtCount.card_torus_torsion D.X F n hn]

attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.card_gtTors : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws → _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws2 → (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), (N : F) ≠ 0 → Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // _root_.GlobalTheory.UU.GtTors D N g} = N ^ (2 * D.P.g + D.rank) ∧ Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // _root_.GlobalTheory.UU.GtTors D N g ∧ g.b = _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF D F} = N ^ D.rank) := by
  intro hL _ R _ _ _ D F _ _ _ N hN
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hz : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF D F = 1 := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF; rfl
  have h0 : (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F).b = 1 := by
    simpa using _root_.GlobalTheory.TorusExt.nsmul_b 0 (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F)
  let p : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F →+ Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A) :=
    { toFun := fun g => Additive.ofMul g.b
      map_zero' := by rw [h0]; rfl
      map_add' := fun g g' => by rw [_root_.GlobalTheory.TorusExt.add_b]; rfl }
  have hsurj : ∀ b : Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A), N • b = 0 → ∃ g, p g = b ∧ N • g = 0 := by
    intro b hb
    obtain ⟨g, hgb, hg⟩ := _root_.GlobalTheory.TorusExt.exists_nsmul_eq_of_pow_eq hN0 (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F) (b := Additive.toMul b)
      (by rw [h0]; exact hb)
    exact ⟨g, by simp [p, hgb], hg⟩
  have hB : Nat.card {b : Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A) // N • b = 0} = N ^ (2 * D.P.g) := by
    have := (hL.mulN (Spec (CommRingCat.of R)) D.P N (Nat.one_le_iff_ne_zero.2 hN0)).2.2.2.2 F
      (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F).hom hN
    rw [← this]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun b => Iff.rfl)
  simp only [_root_.GlobalTheory.GtCount.gtTors_iff, hz]
  refine ⟨?_, _root_.GlobalTheory.GtCount.card_torsion_over_zero D F N hN⟩
  rw [_root_.GlobalTheory.GtCount.card_torsion_eq_mul p N hsurj, hB, pow_add]
  congr 1
  rw [← _root_.GlobalTheory.GtCount.card_torsion_over_zero D F N hN]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [p])

end GlobalTheory.GtCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamEqOfCoefEq
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefDet

theorem fn_ext_of_points {F : Type} [Field F] [IsAlgClosed F] {Y : Scheme.{0}} [IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType p] {U : Y.Opens} {a b : Γ(Y, U)}
    (h : ∀ r : Spec (CommRingCat.of F) ⟶ Y, r ≫ p = 𝟙 _ → ∀ z, r z ∈ U → gs r z U a = gs r z U b) : a = b := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hn (Y.basicOpen (a - b)).isOpen.isLocallyClosed
  let r := pointOfClosedPoint p c hc
  let z : Spec (CommRingCat.of F) := IsLocalRing.closedPoint F
  have hz : r z ∈ Y.basicOpen (a - b) := (congrArg (· ∈ Y.basicOpen (a - b)) (pointOfClosedPoint_apply p c hc z)).mpr hcW
  have hU : r z ∈ U := Y.basicOpen_le _ hz
  have e := h r (pointOfClosedPoint_comp p c hc) z hU
  have hu : IsUnit (gs r z U (a - b)) := by
    rw [gs_eq r z U hU, ← Scheme.mem_basicOpen _ _ z hU, ← Scheme.preimage_basicOpen]
    exact hz
  rw [gs_eq r z U hU, gs_eq r z U hU, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  rw [gs_eq r z U hU, e] at hu
  exact not_isUnit_zero hu

theorem fam_eq_of_coef_eq : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ) (s s' : Fam D.toPre F k), (∀ g : GtPtF D.toPre F, ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ ∀ χ, coef s g w χ = coef s' g w χ) → s = s' := by
  intro hL R _ _ _ I hA D F _ _ _ k s s' H
  have hsm := D.toPre.P.isAb.smooth
  let p : (DegPre.BF D.toPre F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.toPre.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.toPre.P.A.hom))
  have : IsReduced (DegPre.BF D.toPre F).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  refine fam_ext fun χ j => fn_ext_of_points p fun r hr z hz => ?_
  let r' : TF (R := R) F ⟶ DegPre.BF D.toPre F := Over.homMk r (by
    rw [← Over.w (fst (TF (R := R) F) D.toPre.P.A), ← Category.assoc]
    exact (congrArg (· ≫ (TF (R := R) F).hom) hr).trans (Category.id_comp _))
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL R I hA D F).1 (r' ≫ snd _ _)
  have er : lift (𝟙 (TF (R := R) F)) g.b = r' := by
    rw [hg]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
    rw [lift_fst]
    exact Over.OverMorphism.ext hr.symm
  obtain ⟨w, hw, hc⟩ := H g
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TF (R := R) F).left) D.toPre.P.isLB z
  have a := CoefBasic.isCoef_coef g hw χ s z J hJ
  have a' := CoefBasic.isCoef_coef g hw χ s' z J hJ
  rw [hc χ, a', Units.mul_left_inj, Units.mul_left_inj, er] at a
  exact (sec_trans (s.s χ) r z hz (hJ.mem _ r)).trans ((congrArg _ a.symm).trans
    (sec_trans (s'.s χ) r z hz (hJ.mem _ r)).symm)

end GlobalTheory.UT.CoefDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamFEOneOfPsiRel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.UU

section
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem val_famMult_one {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu α : D.X) :
    val (DegPre.famMult D F 1 mu α) σ.left z J * val (D.psi α) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (mu + α)) (σ.left ≫ jFK (R := R) F) z J := by
  have e : val (D.tau mu α) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (mu + α)) (σ.left ≫ jFK (R := R) F) z J * (val (D.psi mu) (σ.left ≫ jFK (R := R) F) z J)⁻¹ *
        (val (D.psi α) (σ.left ≫ jFK (R := R) F) z J)⁻¹ * (val D.rigK (σ.left ≫ jFK (R := R) F) z J)⁻¹ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) 1) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi mu) (σ.left ≫ jFK (R := R) F) z J := congrArg (gm _ z _) (pow_one _)
  have p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK 1) (σ.left ≫ jFK (R := R) F) z J =
      val D.rigK (σ.left ≫ jFK (R := R) F) z J := congrArg (gm _ z _) (pow_one _)
  rw [val_famMult σ hJ, e, p₁, p₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem uVal_one (α : D.X) (m : TF (R := R) F ⟶ D.P.A) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F)
    {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) : uVal D F 1 α m ρ z J = 1 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  rw [uVal, cubN, Finset.prod_range_one, pow_zero, _root_.mul_one, C.s12, mul_inv_cancel]

theorem sval_of_const (s₀ s : Raw D F 1) (c : F) (hs : ∀ α j, (s α).f j = DegPre.constBF D F c _ * (s₀ α).f j)
    (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval (s α) r z J =
      gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) *
        sval (s₀ α) r z J :=
  (congrArg (gs r z _) (hs α _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
    ((gs_res r z le_top (hJ.mem _ r) _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _)) rfl))

end

theorem famFE_one_of_psiRel : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ s : Raw D F 1) (c : F), PsiRel D (TF (R := R) F) s₀ → (∀ α j, (s α).f j = DegPre.constBF D F c _ * (s₀ α).f j) → DegPre.FamFE D F 1 s := by
  intro hG R _ _ D F _ _ s₀ s c hψ hs mu α u hu hc
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e₃ := (gen_fe hG 1 mu α).2 u hu hc _ (𝟙 _) y J hJ
  rw [uVal_one D F _ _ _ hJ, _root_.one_mul, Category.id_comp, Over.id_left] at e₃
  have e₄ := val_famMult_one D F (fst (TF (R := R) F) D.P.A) hJ mu α
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have e₁ := hψ (α + 1 • mu) _ (fst _ _) κ (snd _ _) y J hJ
  have e₂ := hψ α _ (fst _ _) κ (snd _ _ * cT D _ mu) y J hJ
  have q : snd (TF (R := R) F) D.P.A * cT D _ mu * cT D _ α = snd (TF (R := R) F) D.P.A * cT D _ (α + 1 • mu) := by
    rw [one_nsmul, add_comm, _root_.mul_assoc]
    exact congrArg _ (cPoint_add D _ mu α).symm
  rw [q] at e₂
  rw [lift_fst_snd, Over.id_left] at e₁
  have e₅ : val (D.psi (α + 1 • mu)) κ.left y J =
      val (DegPre.famMult D F 1 mu α) (fst (TF (R := R) F) D.P.A).left y J * val (D.psi α) κ.left y J := by
    rw [one_nsmul, add_comm]; exact e₄.symm
  have t : (DegPre.trF D F mu).left ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D.P.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ fst (TF (R := R) F) D.P.A = _)
  have e₁' : sval (s₀ (α + 1 • mu)) (𝟙 _) y J = _ := e₁
  have e₂' : sval (s₀ α) (DegPre.trF D F mu).left y J = _ := e₂
  rw [sval_of_const D F s₀ s c hs _ _ y hJ, sval_of_const D F s₀ s c hs _ _ y hJ, Category.id_comp, Category.id_comp, t,
    e₁', e₂', e₃, e₅]
  simp only [Units.val_mul]
  ring

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtCoordCompare

section Refine

variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def Refines (M : LB Y) (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ σ : M.ι → K → L.ι, (∀ i, M.U i ≤ LB.wchart L φ (σ i)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : M.ι), r z ∈ M.U i → r z ∈ M.U j →
      gm r z (M.U i ⊓ M.U j) (M.g i j) = trF φ ε r z (σ i) (σ j)

theorem refines_self (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Refines (LB.LinComb L φ ε) L φ ε :=
  ⟨id, fun _ => le_rfl, fun _ r z i j hi hj => gm_linComb L φ ε r z i j hi hj⟩

theorem Refines.linComb {M : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Refines M L φ ε)
    (ψ : K' → (Y' ⟶ Y)) (δ : K' → ℤ) :
    Refines (LB.LinComb M ψ δ) L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1) := by
  obtain ⟨σ, le, hg⟩ := h
  refine ⟨fun j p => σ (j p.1) p.2, fun j y hy => Set.mem_iInter.2 fun p => ?_, fun Z r z i j hi hj => ?_⟩
  · exact Set.mem_iInter.1 (le _ (Set.mem_iInter.1 hy p.1)) p.2
  · refine (gm_linComb M ψ δ r z i j hi hj).trans ?_
    rw [trF, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hg Z (r ≫ ψ a) z _ _ (Set.mem_iInter.1 hi a) (Set.mem_iInter.1 hj a), trF, ← Finset.prod_zpow]
    simp only [zpow_mul, Category.assoc]

theorem isGen_one : (LB.oneGen L (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

end Refine

section Present

variable {S : Scheme.{0}}

end Present

section Data

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)

end Data

section

variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)

variable {q a p}

theorem gm_gen {N : LB B} {t : LB.Gen N} (ht : t.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : N.ι} (h : r z ∈ N.U j) (h' : r z ∈ N.U j') :
    gm r z _ (t.s j) = gm r z _ (N.g j j') * gm r z _ (t.s j') := by
  have hm : r z ∈ N.U j ⊓ N.U j' := ⟨h, h'⟩
  exact (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _) (ht j j')).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res r z _ hm _))))

end

theorem gm_res_pull_top {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (f : Y ⟶ X) {V : Y.Opens}
    (hz : r z ∈ V) (h : V ≤ f ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)ˣ) :
    gm r z V (res h (pullU f ⊤ c)) = gm (r ≫ f) z ⊤ c :=
  (gm_res r z h hz _).trans (gm_pull r f z ⊤ trivial c)

section Datum

variable {S : Scheme.{0}}

variable {E : SplitExt S} {G : Over S} [GrpObj G] (d : E.GtDatum G)

attribute [local instance] SplitExt.free SplitExt.finite

end Datum

end GlobalTheory.GtCoordCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpTOfExpandsAt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem expT_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : H0 U'.LG.L k) (σ₀ : H0 U.P.L.L k) (σ' : U.SecGT (𝟙_ _) k) (f) (f'), HEq σ σ₀ → SameG σ₀ σ' → SameB f f' → (∀ e, U'.ExpandsAt e k σ f) → U.ExpT (𝟙_ _) k σ' f' := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e
  obtain ⟨S, hS⟩ := ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val U' e k σ f (hE e)
  refine ⟨S, fun Z x rG rB h1 h2 _ z JG J hJG hJ => ?_⟩
  obtain ⟨h₀, h₁⟩ := hS Z x z J hJ
  clear hS hE
  obtain ⟨-, hL, -, -, hgt, hw⟩ := hM
  cases U'
  dsimp only at hL hgt hw
  subst hL hgt
  cases hw
  cases hσ
  have eB : ∀ α, sval (f' α) rB z J = sval (f α) (x ≫ (U.gt e).pG.left) z J := fun α => by
    rw [hB α Z rB z J hJ, h2]
  refine ⟨fun α hα => (eB α).trans (h₀ α hα), ?_⟩
  have H := h₁ (JG (x ≫ (fstG I e G).left)) (hJG (x ≫ (fstG I e G).left))
  rw [hG Z rG z JG hJG, h1, Finset.sum_congr rfl fun α _ => congrArg (· * _) (eB α)]
  refine Eq.trans ?_ H
  rw [Units.val_pow_eq_pow_val, sval_of σ₀ _ z JG (fun _ => JG (x ≫ (fstG I e G).left)) (fun _ => by rw [Category.comp_id])]
  rfl

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPreUSetPsi
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def gtCoordSetPsi {e : ℕ} (g : GtCoord I D e G) (ψ) (h) : GtCoord I (setPsi D ψ h) e G where
  q := g.q
  q_hom := g.q_hom
  q_flat := g.q_flat
  q_surj := g.q_surj
  q_affine := g.q_affine
  i := g.i
  i_hom := g.i_hom
  isKernel := g.isKernel
  t := g.t
  t_gen := g.t_gen
  t_mul := g.t_mul
  t_unit := g.t_unit
  t_weight := g.t_weight

def PreU.setPsi (U : PreU I D A G) (ψ) (h) : PreU I (setPsi D ψ h) A G where
  semi := U.semi
  gen := U.gen
  gen_hom := U.gen_hom
  P := U.P
  wA := U.wA
  wA_gen := U.wA_gen
  gt := fun e => gtCoordSetPsi (U.gt e) ψ h
  gt_q := U.gt_q
  gt_t := U.gt_t
  w := U.w
  w_gen := U.w_gen
  w_vals := U.w_vals
  w_compat := U.w_compat
end

theorem exists_preU_setPsi : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) ψ h, ∃ (U' : PreU I (setPsi D ψ h) A G) (hP : U'.P = U.P), U'.gen = U.gen ∧ HEq U'.wA U.wA ∧ ∀ θ f, U.Theta θ f → ∃ θ', U'.Theta θ' f :=
  fun _ _ _ _ _ _ _ _ _ U ψ h => ⟨U.setPsi ψ h, rfl, rfl, HEq.rfl, fun θ _ hθ => ⟨θ, hθ⟩⟩
end GlobalTheory.UU
end
end
