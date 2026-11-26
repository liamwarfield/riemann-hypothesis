module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaCoefficientsAbelianSquare
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionLinCombFiberProductSeparated
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralAdditionFormulaGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalAdditionFactorGenerator
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU

theorem exists_cubical_addition_factor_generator {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {Y : Over S}
    (a b : Y ⟶ G) :
    ∃ κ : LB.Gen (LB.LinComb P.L.L (K := Fin 4) ![a.left, b.left, (a * b).left, (a * b⁻¹).left] ![2, 2, -1, -1]),
      κ.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ Y) (z : T.left) (J), Good P.L.L z J →
        val κ ρ.left z J = kap0 P.c P.sym z J (ρ ≫ a) (ρ ≫ b) := by
  let cu := LB.pullGen P.L.L (thφ G (x3 G)) thε P.c.t (lift a (lift b b⁻¹)).left
  let sy := LB.invGen P.L.L _ _ (LB.pullGen P.L.L _ _ P.sym b.left)
  let rg := LB.pullGen P.L.L (fun _ : PUnit => eSec G) (fun _ => 1) P.L.rig Y.hom
  have gc : cu.IsGen := DVR.pullGen_isGen _ _ _ _ P.c.isGen _
  have gy : sy.IsGen := DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen _)
  have gr : rg.IsGen := DVR.pullGen_isGen _ _ _ _ P.L.rigGen _
  obtain ⟨κ, hκ, hv⟩ := exists_gen P.L.isLB (K' := Fin 4)
    (φ' := ![a.left, b.left, (a * b).left, (a * b⁻¹).left]) (ε' := ![2, 2, -1, -1]) (fun U _ h => by
      have e₂ : ∏ k : Fin 2, h (b.left ≫ ![(ι[G]).left, 𝟙 G.left] k) ^ (-(![1, -1] : Fin 2 → ℤ) k) =
          (h (b⁻¹).left * (h b.left)⁻¹)⁻¹ := by
        rw [← prod_sym b h]; simp only [zpow_neg, Finset.prod_inv_distrib]
      have e₃ : ∏ _k : PUnit, h (Y.hom ≫ eSec G) ^ (1 : ℤ) = h (1 : Y ⟶ G).left := by
        rw [Fintype.prod_unique, zpow_one, one_left]
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (prod_cub a b b⁻¹ h) e₂)) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) e₃ e₃)))).trans ?_
      rw [mul_inv_cancel_right, mul_inv_cancel b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen P.L.L _ _ _ _ (LB.mulGen P.L.L _ _ _ _ cu sy) (LB.mulGen P.L.L _ _ _ _ rg rg))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ gc gy) (DVR.mulGen_isGen _ _ _ _ _ _ _ gr gr))
  refine ⟨κ, hκ, fun T ρ z J hJ => (hv _ _ z J hJ).trans ?_⟩
  have vr : val rg ρ.left z J =
      val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T.hom z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Over.w ρ]
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    (val_cub P.c ρ hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) vr vr)))).trans ?_
  rw [kap0, GrpObj.comp_inv, pow_two]
  rfl

theorem exists_addSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : CP G) (T₀ : Over S) (θ : LB.Sec (LB.LinComb P.L.L (K := Fin 1) (fun _ => (snd T₀ G).left) (fun _ => ((1 : ℕ) : ℤ)))) (ρ₀ : G ⊗ G ⟶ T₀), ∃ v : LB.Sec (LB.LinComb P.L.L (K := Fin 1 ⊕ Fin 1) (Sum.elim (fun _ => (fst G G).left) (fun _ => (snd G G).left)) (Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ)))), ∀ (T : Over S) (x y : T ⟶ G) (z : T.left) (J), Good P.L.L z J → sval v (lift x y).left z J = (kap0 P.c P.sym z J x y).val * (sval θ (lift (lift x y ≫ ρ₀) (x * y)).left z J * sval θ (lift (lift x y ≫ ρ₀) (x * y⁻¹)).left z J) := by
  intro S G _ _ P T₀ θ ρ₀
  obtain ⟨κ, hκ, hv⟩ := exists_cubical_addition_factor_generator P (fst G G) (snd G G)
  obtain ⟨v, hs⟩ := exists_sec P.L.isLB (K' := Fin 1 ⊕ Fin 1)
    (φ' := Sum.elim (fun _ => (fst G G).left) (fun _ => (snd G G).left))
    (ε' := Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ))) (fun U _ h => by
      have e : ∀ p : G ⊗ G ⟶ G, ∏ _k : Fin 1, h ((lift ρ₀ p).left ≫ (snd T₀ G).left) ^ ((1 : ℕ) : ℤ) = h p.left :=
        fun p => by rw [Fintype.prod_unique, ← Over.comp_left, lift_snd, Nat.cast_one, zpow_one]
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (e _) (e _))))).trans ?_
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (H1.SectionArithmetic.mulSec (genSec κ hκ) (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec θ (lift ρ₀ (fst G G * snd G G)).left)
      (H1.SectionArithmetic.pullSec θ (lift ρ₀ (fst G G * (snd G G)⁻¹)).left)))
  refine ⟨v, fun T x y z J hJ => (hs _ _ z J hJ).trans ?_⟩
  rw [H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_pullSec _ _ _ z hJ,
    H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, sval_genSec _ _ _ z hJ, hv T _ z J hJ, ← Over.comp_left, ← Over.comp_left,
    comp_lift, comp_lift, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSmulEqSumMulOfIsDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfGenericFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_of_generic_fibre : ∀ (V : Type) [CommRing V] [IsDomain V] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y : Over (Spec (CommRingCat.of V))) [QuasiCompact Y.hom] [IsSeparated Y.hom] (K : Type) [Fintype K] (φ : K → (Y.left ⟶ Z)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L (fun k => (snd (TK V) Y).left ≫ φ k) ε)), ∃ (r : V) (_ : r ≠ 0) (σ : LB.Sec (LB.LinComb L φ ε)), ∀ (T : Scheme.{0}) (ρ : T ⟶ (TK V ⊗ Y).left) (z : T) (J), Good L z J → sval σ (ρ ≫ (snd (TK V) Y).left) z J = gs ρ z ⊤ (scal (TK V ⊗ Y).hom r) * sval s ρ z J := by
  intro V _ _ Z L hL Y _ _ K _ φ ε s
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have H : IsPullback (snd (TK V) Y).left (fst (TK V) Y).left Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :=
    (IsPullback.of_hasPullback (TK V).hom Y.hom).flip
  obtain ⟨t, ht, σ, hσ⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors V) H hL φ ε s
  refine ⟨t, nonZeroDivisors.ne_zero ht, σ, fun T ρ z J hJ => ?_⟩
  rw [sval_of σ (ρ ≫ (snd (TK V) Y).left) z J (fun k => J (ρ ≫ (snd (TK V) Y).left ≫ φ k))
    (fun k => by rw [Category.assoc])]
  refine (hσ T ρ z _ (hJ.mem (fun k => (snd (TK V) Y).left ≫ φ k) ρ)).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [Over.w (snd (TK V) Y)]
  exact (gs_pull ρ (TK V ⊗ Y).hom z ⊤ trivial _).symm

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace KunnethDomain

open ReciprocityTheory.ChartRestriction.G.DVR

variable {X Y Y' T : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def cst {R : Type} [CommRing R] (q : T ⟶ Spec (CommRingCat.of R)) (z : T) : R →+* T.presheaf.stalk z :=
  (T.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_scal_eq {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (ρ : T ⟶ Y) (z : T) (c : R) :
    gs ρ z ⊤ (scal p c) = cst (ρ ≫ p) z c := by
  rw [gs_eq ρ z ⊤ trivial]; rfl

theorem sval_scale {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε))
    (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) :
    sval (SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem sval_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (r : T ⟶ Y') (z : T) {J} (hJ : Good L z J) : sval (pullSec L φ ε s h) r z J = sval s (r ≫ h) z J := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => h ≫ φ k) r
  exact (gs_res r z _ hm _).trans (gs_pull r h z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)))
    (wchart_comp_le φ h _ hm) _)

theorem sval_mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) :
    sval (mulSec L φ ε φ' ε' s s') r z J = sval s r z J * sval s' r z J :=
  have hm := hJ.mem (Sum.elim φ φ') r
  (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _))

def secSum {M : LB Y} {n : ℕ} (s : Fin n → LB.Sec M) : LB.Sec M where
  f := fun j => ∑ i, (s i).f j
  compat := fun j j' => by simp only [map_sum, (s _).compat, Finset.mul_sum]

theorem sval_sum {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ} (s : Fin n → LB.Sec (LB.LinComb L φ ε))
    (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) : sval (secSum s) r z J = ∑ i, sval (s i) r z J := by
  have hm := hJ.mem φ r
  refine (gs_eq r z _ hm _).trans (Eq.trans ?_ (Finset.sum_congr rfl fun i _ => (gs_eq r z _ hm _).symm))
  exact map_sum ((T.presheaf.germ (r ⁻¹ᵁ LB.wchart L φ fun k => J (r ≫ φ k)) z hm).hom.comp
    (r.app (LB.wchart L φ fun k => J (r ≫ φ k))).hom) (fun i => (s i).f fun k => J (r ≫ φ k)) Finset.univ

theorem sec_ext_of_app_injective (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u t : LB.Sec (LB.LinComb L φ ε)} (h : ∀ y J, Good L y J → sval u κ y J = sval t κ y J) : u = t :=
  SecOps.sec_ext fun j => by
    refine hκ (LB.wchart L φ j) (fn_ext fun y hy => ?_)
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    refine (gs_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') κ y _ hy _).symm)
    rw [Category.id_comp]
    exact (sec_trans u κ y hy (Good.mem hI φ κ)).trans ((congrArg _ (h y I hI)).trans
      (sec_trans t κ y hy (Good.mem hI φ κ)).symm)

theorem app_generic_injective {V : Type} [CommRing V] [IsDomain V] (B : Over (Spec (CommRingCat.of V))) [Flat B.hom]
    (U : B.left.Opens) : Function.Injective ((snd (TK V) B).left.app U).hom := by
  have : IsDominant (jK V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK V)
  exact (pullback.snd (jK V) B.hom).app_injective U

end KunnethDomain


open KunnethDomain ReciprocityTheory.ChartRestriction.G.DVR in
theorem exists_smul_eq_sum_mul_of_isDomain : ∀ (V : Type) [CommRing V] [IsDomain V] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Over (Spec (CommRingCat.of V))) [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [Flat Y₁.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom] [Flat Y₂.hom] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁.left ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂.left ⟶ Z)) (ε₂ : K₂ → ℤ) (v : LB.Sec (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim (fun k => (fst Y₁ Y₂).left ≫ φ₁ k) (fun k => (snd Y₁ Y₂).left ≫ φ₂ k)) (Sum.elim ε₁ ε₂))), ∃ (r : V) (_ : r ≠ 0) (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), ∀ (T : Scheme.{0}) (ρ : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J → ∑ i, sval (a i) (ρ ≫ (fst Y₁ Y₂).left) z J * sval (b i) (ρ ≫ (snd Y₁ Y₂).left) z J = gs ρ z ⊤ (scal (Y₁ ⊗ Y₂).hom r) * sval v ρ z J := by
  intro V _ _ Z L hL Y₁ Y₂ _ _ _ _ _ _ K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ v
  classical
  let G₁ : Over (Spec (CommRingCat.of (FractionRing V))) := Over.mk (fst (TK V) Y₁).left
  let G₂ : Over (Spec (CommRingCat.of (FractionRing V))) := Over.mk (fst (TK V) Y₂).left
  have : QuasiCompact G₁.hom := inferInstanceAs (QuasiCompact (pullback.fst (jK V) Y₁.hom))
  have : IsSeparated G₁.hom := inferInstanceAs (IsSeparated (pullback.fst (jK V) Y₁.hom))
  have : QuasiCompact G₂.hom := inferInstanceAs (QuasiCompact (pullback.fst (jK V) Y₂.hom))
  have : IsSeparated G₂.hom := inferInstanceAs (IsSeparated (pullback.fst (jK V) Y₂.hom))
  have : Flat (Y₁ ⊗ Y₂).hom := inferInstanceAs (Flat (pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom))
  let p₁ : (G₁ ⊗ G₂).left ⟶ (TK V ⊗ Y₁).left := (fst G₁ G₂).left
  let p₂ : (G₁ ⊗ G₂).left ⟶ (TK V ⊗ Y₂).left := (snd G₁ G₂).left
  have hp : p₁ ≫ (fst (TK V) Y₁).left = p₂ ≫ (fst (TK V) Y₂).left := (Over.w (fst G₁ G₂)).trans (Over.w (snd G₁ G₂)).symm
  have hp' : p₁ ≫ (TK V ⊗ Y₁).hom = p₂ ≫ (TK V ⊗ Y₂).hom := by
    rw [← Over.w (fst (TK V) Y₁), ← Over.w (fst (TK V) Y₂), ← Category.assoc, hp, Category.assoc]
  obtain ⟨g, g₁, g₂⟩ : ∃ g : (G₁ ⊗ G₂).left ⟶ (Y₁ ⊗ Y₂).left, g ≫ (fst Y₁ Y₂).left = p₁ ≫ (snd (TK V) Y₁).left ∧
      g ≫ (snd Y₁ Y₂).left = p₂ ≫ (snd (TK V) Y₂).left :=
    ⟨pullback.lift (p₁ ≫ (snd (TK V) Y₁).left) (p₂ ≫ (snd (TK V) Y₂).left) (by
      rw [Category.assoc, Category.assoc, Over.w, Over.w, hp']), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨h, h₁, h₂⟩ : ∃ h : (TK V ⊗ Y₁ ⊗ Y₂).left ⟶ (G₁ ⊗ G₂).left, h ≫ p₁ = (TK V ◁ fst Y₁ Y₂).left ∧
      h ≫ p₂ = (TK V ◁ snd Y₁ Y₂).left :=
    ⟨pullback.lift (TK V ◁ fst Y₁ Y₂).left (TK V ◁ snd Y₁ Y₂).left (by
      show (TK V ◁ fst Y₁ Y₂).left ≫ (fst (TK V) Y₁).left = (TK V ◁ snd Y₁ Y₂).left ≫ (fst (TK V) Y₂).left
      rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_fst, whiskerLeft_fst]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hg : h ≫ g = (snd (TK V) (Y₁ ⊗ Y₂)).left := by
    apply pullback.hom_ext
    · show (h ≫ g) ≫ (fst Y₁ Y₂).left = _ ≫ (fst Y₁ Y₂).left
      rw [Category.assoc, g₁, ← Category.assoc, h₁, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
    · show (h ≫ g) ≫ (snd Y₁ Y₂).left = _ ≫ (snd Y₁ Y₂).left
      rw [Category.assoc, g₂, ← Category.assoc, h₂, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  obtain ⟨v', hv'⟩ := exists_sec hL (K' := K₁ ⊕ K₂)
    (φ' := Sum.elim (fun k => p₁ ≫ (snd (TK V) Y₁).left ≫ φ₁ k) (fun k => p₂ ≫ (snd (TK V) Y₂).left ≫ φ₂ k))
    (ε' := Sum.elim ε₁ ε₂) (fun U _ f => Finset.prod_congr rfl (by
      rintro (k | k) _
      · simp only [Sum.elim_inl]
        rw [← Category.assoc, g₁, Category.assoc]
      · simp only [Sum.elim_inr]
        rw [← Category.assoc, g₂, Category.assoc])) (pullSec L _ _ v g)
  obtain ⟨n, a', b', hab⟩ := (GlobalTheory.T.section_lin_comb_fiber_product_separated (FractionRing V) Z L hL G₁ G₂ K₁ K₂
    (fun k => (snd (TK V) Y₁).left ≫ φ₁ k) ε₁ (fun k => (snd (TK V) Y₂).left ≫ φ₂ k) ε₂).1 v'
  choose r hr σ hσ using fun i => exists_sec_of_generic_fibre V Z L hL Y₁ K₁ φ₁ ε₁ (a' i)
  choose s hs τ hτ using fun i => exists_sec_of_generic_fibre V Z L hL Y₂ K₂ φ₂ ε₂ (b' i)
  let c : Fin n → V := fun i => ∏ j ∈ Finset.univ.erase i, r j * s j
  have hc : ∀ i, c i * (r i * s i) = ∏ j, r j * s j := fun i =>
    Finset.prod_erase_mul Finset.univ (fun j => r j * s j) (Finset.mem_univ i)
  refine ⟨∏ j, r j * s j, Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (hr j) (hs j), n,
    fun i => SecOps.secScale (scal Y₁.hom (c i)) (σ i), τ, ?_⟩
  have val_sum : ∀ (T : Scheme.{0}) (ρ : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J →
      sval (secSum fun i => mulSec L _ _ _ _
        (pullSec L _ _ (SecOps.secScale (scal Y₁.hom (c i)) (σ i)) (fst Y₁ Y₂).left)
        (pullSec L _ _ (τ i) (snd Y₁ Y₂).left)) ρ z J =
      ∑ i, sval (SecOps.secScale (scal Y₁.hom (c i)) (σ i)) (ρ ≫ (fst Y₁ Y₂).left) z J *
        sval (τ i) (ρ ≫ (snd Y₁ Y₂).left) z J := fun T ρ z J hJ =>
    (sval_sum _ ρ z hJ).trans (Finset.sum_congr rfl fun i _ => (sval_mul _ _ ρ z hJ).trans
      (congrArg₂ (· * ·) (sval_pull _ _ ρ z hJ) (sval_pull _ _ ρ z hJ)))
  have E : (secSum fun i => mulSec L _ _ _ _
        (pullSec L _ _ (SecOps.secScale (scal Y₁.hom (c i)) (σ i)) (fst Y₁ Y₂).left)
        (pullSec L _ _ (τ i) (snd Y₁ Y₂).left)) = SecOps.secScale (scal (Y₁ ⊗ Y₂).hom (∏ j, r j * s j)) v := by
    refine sec_ext_of_app_injective hL _ (app_generic_injective (Y₁ ⊗ Y₂)) fun y J hJ => ?_
    have q₀ : (h ≫ g) ≫ (Y₁ ⊗ Y₂).hom = (h ≫ p₁) ≫ (TK V ⊗ Y₁).hom := by
      rw [hg, h₁, Over.w, Over.w]
    have q₁ : ((h ≫ p₁) ≫ (snd (TK V) Y₁).left) ≫ Y₁.hom = (h ≫ p₁) ≫ (TK V ⊗ Y₁).hom := by
      rw [Category.assoc, Over.w]
    have q₂ : (h ≫ p₂) ≫ (TK V ⊗ Y₂).hom = (h ≫ p₁) ≫ (TK V ⊗ Y₁).hom := by
      rw [Category.assoc, Category.assoc, hp']
    have e₁ : (h ≫ g) ≫ (fst Y₁ Y₂).left = (h ≫ p₁) ≫ (snd (TK V) Y₁).left := by
      rw [Category.assoc, Category.assoc, g₁]
    have e₂ : (h ≫ g) ≫ (snd Y₁ Y₂).left = (h ≫ p₂) ≫ (snd (TK V) Y₂).left := by
      rw [Category.assoc, Category.assoc, g₂]
    have e₃ : sval v (h ≫ g) y J = ∑ i, sval (a' i) (h ≫ p₁) y J * sval (b' i) (h ≫ p₂) y J :=
      (sval_pull v g h y hJ).symm.trans ((hv' _ h y J hJ).symm.trans (hab _ h y J hJ))
    rw [val_sum _ _ y J hJ, sval_scale _ _ _ y hJ, ← hg, e₁, e₂, e₃, gs_scal_eq, q₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sval_scale _ _ _ y hJ, hσ i _ _ y J hJ, hτ i _ _ y J hJ, gs_scal_eq, gs_scal_eq, gs_scal_eq, q₁, q₂, ← hc i,
      map_mul, map_mul]
    ring
  intro T ρ z J hJ
  rw [← val_sum T ρ z J hJ, E, sval_scale _ _ _ z hJ]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralAdditionFormulaGroup
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU

theorem exists_addG : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ : U.SecGT (𝟙_ _) 1, ∃ (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2), r ≠ 0 ∧ U.AddG θ r σ σ') := by
  intro V _ _ _ _ D A G _ _ U θ
  have := U.semi.smooth
  have := U.semi.separated
  have := U.semi.quasiCompact
  obtain ⟨v, hv⟩ := exists_addSec _ G U.P (𝟙_ _) θ (toUnit _)
  obtain ⟨v', hv'⟩ := exists_sec U.P.L.isLB (K' := Fin 1 ⊕ Fin 1)
    (φ' := Sum.elim (fun _ => (fst G G).left ≫ 𝟙 G.left) (fun _ => (snd G G).left ≫ 𝟙 G.left))
    (ε' := Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ)))
    (fun U _ h => by simp only [Category.comp_id]) v
  obtain ⟨r, hr, n, a, b, hab⟩ := GlobalTheory.exists_smul_eq_sum_mul_of_isDomain V G.left U.P.L.L U.P.L.isLB G G (Fin 1) (Fin 1)
    (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ)) (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ)) v'
  have mv : ∀ s : LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ))),
      ∃ σ : U.SecGT (𝟙_ _) 2, ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ G) (z : T.left) (J), Good U.P.L.L z J →
        sval σ (lift (toUnit T) x).left z J = sval s x.left z J := fun s => by
    obtain ⟨σ, hσ⟩ := exists_sec U.P.L.isLB (K' := Fin 1) (φ' := fun _ => (snd (𝟙_ _) G).left)
      (ε' := fun _ => ((2 : ℕ) : ℤ)) (fun U _ h => by simp only [Category.comp_id])
      (H1.SectionArithmetic.pullSec s (snd (𝟙_ _) G).left)
    refine ⟨σ, fun T x z J hJ => (hσ _ _ z J hJ).trans ?_⟩
    rw [H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, ← Over.comp_left, lift_snd]
  choose mv hmv using mv
  refine ⟨r, n, fun i => mv (a i), fun i => mv (b i), hr, fun T x y z J hJ => ?_⟩
  have e := hab T.left (lift x y).left z J hJ
  rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_snd, hv' _ _ z J hJ, hv T x y z J hJ,
    toUnit_unique (lift x y ≫ toUnit _) (toUnit T)] at e
  have g : gs (lift x y).left z ⊤ (scal (G ⊗ G).hom r) = gs (𝟙 _) z ⊤ (scal T.hom r) := by
    have p : ∀ {Z Y : Scheme.{0}} (f : Z ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of V)) (w : Z),
        gs f w ⊤ (scal q r) = gs (f ≫ q) w ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) :=
      fun f q w => gs_pull f q w ⊤ trivial _
    rw [p, p, Over.w, Category.id_comp]
  simp only [hmv _ T _ z J hJ]
  rw [e, g, _root_.mul_assoc]

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralAdditionFormulaGroupStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_addition_formula_group : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ : U.SecGT (𝟙_ _) 1, ∃ (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2), r ≠ 0 ∧ U.AddG θ r σ σ') := by
  first | exact @GlobalTheory.UU.exists_addG | exact GlobalTheory.UU.exists_addG | (intros; apply GlobalTheory.UU.exists_addG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAdditionFactorGeneratorTransported
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddGeneric

theorem exists_additionFactor_generator_value {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {T : Over S}
    (x y : T ⟶ G) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (K := Fin 4) ![x.left, y.left, (x * y).left, (x * y⁻¹).left] ![2, 2, -1, -1]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P.L.L z J →
        val t ρ.left z J = kap0 P.c P.sym z J (ρ ≫ x) (ρ ≫ y) := by
  let r₀ := LB.pullGen P.L.L (fun _ : PUnit => eSec G) (fun _ => 1) P.L.rig T.hom
  have hr₀ : r₀.IsGen := DVR.pullGen_isGen _ _ _ _ P.L.rigGen _
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ' := ![x.left, y.left, (x * y).left, (x * y⁻¹).left])
    (ε' := ![2, 2, -1, -1]) (fun U _ h => by
      have o : ∏ _k : PUnit, h (T.hom ≫ eSec G) ^ (1 : ℤ) = h (1 : T ⟶ G).left := by
        rw [Fintype.prod_unique, zpow_one, one_left]
      refine (DVR.prod_sum₂ (U := U) (K := thK ⊕ Fin 2) (K' := PUnit ⊕ PUnit) _
        (DVR.prod_sum₂ (U := U) (K := thK) (K' := Fin 2) _ (prod_cub x y y⁻¹ h) (DVR.prod_neg _ _ (prod_sym y h)))
        (DVR.prod_sum₂ (U := U) (K := PUnit) (K' := PUnit) _ o o)).trans ?_
      rw [mul_inv_cancel_right, mul_inv_cancel]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen P.L.L _ _ _ _
      (LB.mulGen P.L.L _ _ _ _ (LB.pullGen P.L.L (thφ G (x3 G)) thε P.c.t (lift x (lift y y⁻¹)).left)
        (LB.invGen P.L.L _ _ (LB.pullGen P.L.L _ _ P.sym y.left)))
      (LB.mulGen P.L.L _ _ _ _ r₀ r₀))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.c.isGen _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen _))) (DVR.mulGen_isGen _ _ _ _ _ _ _ hr₀ hr₀))
  refine ⟨t, ht, fun T' ρ z J hJ => ?_⟩
  have e₀ : val r₀ ρ.left z J =
      val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T'.hom z J :=
    (val_pull hJ _ _ _).trans (by rw [Over.w ρ])
  refine ((hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_cub P.c ρ hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₀ e₀))))).trans ?_
  rw [kap0, sq, GrpObj.comp_inv, Over.comp_left]

theorem exists_additionFactor_generator_transported {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G)
    {A : Over S'} [GrpObj A] [IsCommMonObj A] {Φ : A.left ⟶ G.left} (hw : Φ ≫ G.hom = A.hom ≫ f)
    (mul : ∀ (T : Over S') (x y : T ⟶ A), toBase hw (x * y) = toBase hw x * toBase hw y)
    {L' : LB A.left} (hL' : L'.IsLB) (u : LB.Iso L' (P.L.L.pull Φ)) (hu : PGen u) {Y : Over S'} (p q s d : Y ⟶ A)
    (hs : s = p * q) (hd : d = p * q⁻¹) :
    ∃ a : LB.Gen (LB.LinComb L' (K := Fin 4) ![p.left, q.left, s.left, d.left] ![2, 2, -1, -1]), a.IsGen ∧
      ∀ (T : Over S') (ρ : T ⟶ Y) (z : T.left) (J J'), Good P.L.L z J → Good L' z J' →
        ∀ W : (T ⟶ A) → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw u x.left z (J (x.left ≫ Φ)) (J' x.left)) →
        @id (T.left.presheaf.stalk z)ˣ (kap0 P.c P.sym (T := Over.mk (T.hom ≫ f)) z J (toBase hw (ρ ≫ p)) (toBase hw (ρ ≫ q))) =
          W (ρ ≫ p) ^ 2 * W (ρ ≫ q) ^ 2 * (W ((ρ ≫ p) * (ρ ≫ q)))⁻¹ * (W ((ρ ≫ p) * (ρ ≫ q)⁻¹))⁻¹ *
            val a ρ.left z J' := by
  subst hs hd
  obtain ⟨t, ht, hv⟩ := exists_additionFactor_generator_value P (toBase hw p) (toBase hw q)
  have hψ : ∀ k : Fin 4, ![p.left, q.left, (p * q).left, (p * q⁻¹).left] k ≫ Φ = 𝟙 Y.left ≫
      ![(toBase hw p).left, (toBase hw q).left, (toBase hw p * toBase hw q).left,
        (toBase hw p * (toBase hw q)⁻¹).left] k := by
    intro k
    rw [Category.id_comp]
    have e : toBase hw (p * q⁻¹) = toBase hw p * (toBase hw q)⁻¹ :=
      (mul _ _ _).trans (congrArg _ (map_inv (toBaseHom mul Y) q))
    rw [← e, ← mul]
    fin_cases k <;> rfl
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps hu P.L.isLB hL' (𝟙 Y.left) hψ t ht
  refine ⟨a, ha, fun T ρ z J J' hJ hJ' W hW => ?_⟩
  have e₁ := DegPull.pmaps_val hψ H ρ.left z hJ hJ'
  let ρ' : Over.mk (T.hom ≫ f) ⟶ Over.mk (Y.hom ≫ f) := Over.homMk ρ.left (by
    show ρ.left ≫ Y.hom ≫ f = T.hom ≫ f
    rw [← Category.assoc, Over.w ρ])
  have e₂ := hv _ ρ' z J hJ
  have e₃ : ∀ x : Y ⟶ A, ρ' ≫ toBase hw x = toBase hw (ρ ≫ x) := fun x =>
    Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [e₃, e₃] at e₂
  rw [Category.comp_id] at e₁
  refine e₂.symm.trans (e₁.trans (congrArg (· * val a ρ.left z J') ?_))
  rw [← GrpObj.comp_inv, ← MonObj.comp_mul, ← MonObj.comp_mul, ← zpow_neg_one (W _), ← zpow_neg_one (W _),
    ← zpow_natCast (W _), ← zpow_natCast (W _), hW, hW, hW, hW, Fin.prod_univ_four]
  rfl

theorem cancel_alg {B : Type} [CommRing B] {n : ℕ} (a b c d k k' : Bˣ) (r s s' : B) (t t' : Fin n → B)
    (hk : k = a ^ 2 * b ^ 2 * c⁻¹ * d⁻¹ * k')
    (h : ∑ i, (a.val ^ 2 * t i) * (b.val ^ 2 * t' i) = r * k.val * ((c.val ^ 1 * s) * (d.val ^ 1 * s'))) :
    ∑ i, t i * t' i = r * k'.val * (s * s') := by
  apply (a ^ 2 * b ^ 2).isUnit.mul_left_cancel
  rw [Finset.mul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (h.trans ?_)
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring
  · have hc := c.inv_mul
    have hd := d.inv_mul
    rw [hk]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (r * a.val ^ 2 * b.val ^ 2 * k'.val * s * s' * (d⁻¹).val * d.val) * hc +
      (r * a.val ^ 2 * b.val ^ 2 * k'.val * s * s') * hd

theorem isUnit_scal {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of (FractionRing R))) {r : R} (hr : r ≠ 0) : IsUnit (scal (p ≫ jK R) r) := by
  have e : scal (jK R) r = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) :=
    (congrArg (fun q => q.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm
  have h : IsUnit (algebraMap R (FractionRing R) r) :=
    IsUnit.mk0 _ fun h => hr ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm))
  have : IsUnit (scal (jK R) r) := e ▸ h.map _
  exact this.map p.appTop.hom

theorem addA_of_addG : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (θ : U.SecGT (𝟙_ _) 1) (r : R) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := R) F))) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := R) F))), r ≠ 0 → U.AddG θ r σ σ' → U.PullG F (toUnit _) 1 θ th → (∀ i, U.PullG F (toUnit _) 2 (σ i) (t i) ∧ U.PullG F (toUnit _) 2 (σ' i) (t' i)) → AddA A (TFK (R := R) F) th t t' := by
  intro R _ _ D I A G _ _ U F _ _ θ r n σ σ' th t t' hr hadd hθ hσ
  have := U.gen_hom
  have hi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id
  obtain ⟨u, hu, huv⟩ := ThetaBaseChange.exists_unpull U.wA_gen U.gen.inv.left hi rfl
  have hw : (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ G.hom = A.A.hom ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ jK R) (Over.w U.gen.inv)
  have tb : ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), toBase hw x =
      toBase (A := G) (A' := (Over.pullback (jK R)).obj G) (g := pullback.fst G.hom (jK R)) pullback.condition
        (x ≫ U.gen.inv) := fun T x => Over.OverMorphism.ext (Category.assoc _ _ _).symm
  have mul : ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x y : T ⟶ A.A),
      toBase hw (x * y) = toBase hw x * toBase hw y := fun T x y => by
    rw [tb, tb, tb, MonObj.mul_comp, toBase_mul_pullback]
  obtain ⟨a, ha, hv⟩ := exists_additionFactor_generator_transported U.P hw mul A.isLB u hu (Y := TFK (R := R) F ⊗ (A.A ⊗ A.A))
    (snd _ _ ≫ fst A.A A.A) (snd _ _ ≫ snd A.A A.A) (snd _ _ ≫ (fst A.A A.A * snd A.A A.A))
    (snd _ _ ≫ (fst A.A A.A * (snd A.A A.A)⁻¹)) (MonObj.comp_mul _ _ _)
    ((MonObj.comp_mul _ _ _).trans (by rw [GrpObj.comp_inv]))
  have hun := isUnit_scal (TFK (R := R) F ⊗ (A.A ⊗ A.A)).hom hr
  refine ⟨scaleGen hun.unit a, scaleGen_isGen _ ha, fun T ρ x y z J hJ => ?_⟩
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let W : (T ⟶ A.A) → (T.left.presheaf.stalk z)ˣ := fun p =>
    gw u p.left z (JG (p.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (J p.left)
  have k₀ := hv T (lift ρ (lift x y)) z JG J hJG hJ W (fun _ => rfl)
  have ex : lift ρ (lift x y) ≫ snd _ _ ≫ fst A.A A.A = x := by simp
  have ey : lift ρ (lift x y) ≫ snd _ _ ≫ snd A.A A.A = y := by simp
  rw [ex, ey] at k₀
  have pull : ∀ (k : ℕ) (s : U.SecGT (𝟙_ _) k) (s' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))),
      U.PullG F (toUnit _) k s s' → ∀ p : T ⟶ A.A,
      (W p).val ^ k * sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ))
        s' (lift ρ p).left z J =
      @id (T.left.presheaf.stalk z) (sval s (lift (toUnit (Over.mk (T.hom ≫ jK R))) (toBase hw p)).left z JG) := by
    intro k s s' h p
    have e₁ : (p.left ≫ U.gen.inv.left) ≫ U.gen.hom.left = p.left := by rw [Category.assoc, hi, Category.comp_id]
    have e := h T.left (lift ρ p).left (p.left ≫ U.gen.inv.left)
      (lift (toUnit (Over.mk (T.hom ≫ jK R))) (toBase hw p)).left
      ((congrArg (fun q => q.left) (lift_snd ρ p)).trans e₁.symm)
      ((congrArg (fun q => q.left) (lift_snd _ (toBase hw p))).trans (Category.assoc _ _ _).symm)
      (by
        rw [← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Rosenlicht.toUnit_left, Rosenlicht.toUnit_left]
        show T.hom ≫ jK R = ρ.left ≫ jFK (R := R) F ≫ jK R
        rw [← Category.assoc]
        exact congrArg (· ≫ jK R) (Over.w ρ).symm) z J JG hJ hJG
    rw [e₁, Category.assoc] at e
    refine Eq.trans (congrArg (fun q : (T.left.presheaf.stalk z)ˣ => q.val ^ k * _) ?_) e
    exact huv _ p.left z _ _ (hJG (p.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (hJ p.left)
  have add := hadd (Over.mk (T.hom ≫ jK R)) (toBase hw x) (toBase hw y) z JG hJG
  have e : toBase hw (x * y⁻¹) = toBase hw x * (toBase hw y)⁻¹ :=
    (mul _ _ _).trans (congrArg _ (map_inv (toBaseHom mul T) y))
  rw [← e, ← mul] at add
  have key := cancel_alg (W x) (W y) (W (x * y)) (W (x * y⁻¹)) _ _ _ _ _ _ _ k₀
    ((Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (pull 2 _ _ (hσ i).1 x) (pull 2 _ _ (hσ i).2 y)).trans
      (add.trans (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (pull 1 _ _ hθ _).symm (pull 1 _ _ hθ _).symm))))
  refine key.trans (congrArg (· * _) ?_)
  rw [val_scaleGen _ _ _ hJ, Units.val_mul]
  refine congrArg (· * _) (Eq.trans ?_ (gs_unit _ z ⊤ trivial _))
  refine Eq.trans ?_ ((gs_pull (𝟙 _) (lift ρ (lift x y)).left z ⊤ trivial _).trans (by rw [Category.id_comp]))
  refine congrArg (gs (𝟙 T.left) z ⊤) ?_
  show scal (T.hom ≫ jK R) r = scal ((lift ρ (lift x y)).left ≫ (TFK (R := R) F ⊗ (A.A ⊗ A.A)).hom ≫ jK R) r
  rw [← Category.assoc, Over.w]

end GlobalTheory.AddGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaAlgClosureWithExpansions
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddClosure

theorem addB_of_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1) (r : R) {n : ℕ}
    (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α) (s s' : Fin n → Raw D F 2)
    (h₀ : PullB D F (toUnit _) 1 f₀ s₀) (h : ∀ i, PullB D F (toUnit _) 2 (f i) (s i))
    (h' : ∀ i, PullB D F (toUnit _) 2 (f' i) (s' i)) (hB : AddB D (𝟙_ _) f₀ r f f') :
    AddB D (TF (R := R) F) s₀ r s s' := by
  intro T ρ x y z J hJ
  obtain ⟨h1, h2⟩ := hB T (ρ ≫ toUnit _) x y z J hJ
  have e₀ := fun α w => GlobalTheory.pullB_values R D F _ _ 1 f₀ s₀ h₀ α T ρ w z J hJ
  have e := fun i α w => GlobalTheory.pullB_values R D F _ _ 2 (f i) (s i) (h i) α T ρ w z J hJ
  have e' := fun i α w => GlobalTheory.pullB_values R D F _ _ 2 (f' i) (s' i) (h' i) α T ρ w z J hJ
  refine ⟨fun a b α β ha hb => ?_, fun α β hn => ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((h1 a b α β ha hb).trans ?_)
    · exact congrArg₂ (· * ·) (e i α x) (e' i β y)
    · exact congrArg _ (congrArg₂ (· * ·) (e₀ a _).symm (e₀ b _).symm)
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (h2 α β hn)
    exact congrArg₂ (· * ·) (e i α x) (e' i β y)

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → ∃ (r : V) (n : ℕ) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s s' : Fin n → Raw D (Kbar V) 2), r ≠ 0 ∧ (∀ i, U.ExpF (Kbar V) 2 (t i) (s i) ∧ U.ExpF (Kbar V) 2 (t' i) (s' i)) ∧ AddA A (TFK (R := V) (Kbar V)) th t t' ∧ AddB D (TF (R := V) (Kbar V)) s₀ r s s') := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ th s₀ hth hs₀
  obtain ⟨r, n, σ, σ', hr, hG⟩ := GlobalTheory.T.exists_integral_addition_formula_group V hV D A G U θ
  have hexp := GlobalTheory.BaseExpansionExists.main hL hL2 V hV D A G U 2 (by norm_num)
  choose g hg using hexp
  obtain ⟨hpG, hpB⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 2
  choose pt hpt using fun σ => (hpG σ).exists
  choose ps hps using fun f => (hpB f).exists
  have hB := GlobalTheory.T.additionFormula_coefficients_abelian_square hL.globalFns V hV D A G U θ f r n σ σ' (fun i => g (σ i)) (fun i => g (σ' i)) hG hθ.1
    (fun i => ⟨hg _, hg _⟩)
  refine ⟨r, n, fun i => pt (σ i), fun i => pt (σ' i), fun i => ps (g (σ i)), fun i => ps (g (σ' i)), hr,
    fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 2 _ _ _ _ (hg _) (hpt _) (hps _)
  · exact GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 2 _ _ _ _ (hg _) (hpt _) (hps _)
  · exact GlobalTheory.AddGeneric.addA_of_addG V D _ A G U (Kbar V) θ r n σ σ' th _ _ hr hG hth (fun i => ⟨hpt _, hpt _⟩)
  · exact addB_of_pull D (Kbar V) f s₀ r _ _ _ _ hs₀ (fun i => hps _) (fun i => hps _) hB

end GlobalTheory.AddClosure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaAlgClosureWithExpansionsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additionFormula_algClosure_with_expansions : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → ∃ (r : V) (n : ℕ) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s s' : Fin n → Raw D (Kbar V) 2), r ≠ 0 ∧ (∀ i, U.ExpF (Kbar V) 2 (t i) (s i) ∧ U.ExpF (Kbar V) 2 (t' i) (s' i)) ∧ AddA A (TFK (R := V) (Kbar V)) th t t' ∧ AddB D (TF (R := V) (Kbar V)) s₀ r s s') := by
  first | exact @GlobalTheory.AddClosure.main | exact GlobalTheory.AddClosure.main | (intros; apply GlobalTheory.AddClosure.main <;> assumption)
end
