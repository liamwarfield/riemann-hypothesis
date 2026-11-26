module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyBoundedDenominators
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtSameMumfordBundle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
namespace GlobalTheory.ProdUnif

open GlobalTheory.WCub GlobalTheory.PowUnif


set_option maxHeartbeats 1600000 in
theorem cubAlong_prod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (L : LB (G₁ ⊗ G₂).left) (c : CubGen (G₁ ⊗ G₂) L) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → IsBoxGen (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (φ₁ := thφ D₁.toPre.P.A (x3 D₁.toPre.P.A)) (φ₂ := thφ D₂.toPre.P.A (x3 D₂.toPre.P.A)) (ε := thε) wM (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t → IsBoxGen (φ₁ := thφ G₁ (x3 G₁)) (φ₂ := thφ G₂ (x3 G₂)) wL (fst G₁ G₂ ⊗ₘ fst G₁ G₂ ⊗ₘ fst G₁ G₂).left (snd G₁ G₂ ⊗ₘ snd G₁ G₂ ⊗ₘ snd G₁ G₂).left c U₁.cubG.t U₂.cubG.t → ∀ (e : ℕ) (g : GtCoord I D.toPre e (G₁ ⊗ G₂)), g.pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → g.pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → ∀ w : LB.Iso (L.pull (fstG I e (G₁ ⊗ G₂)).left) (D.toPre.P.L.pull g.pG.left), BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL w (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → CubAlong I D.toPre e (G₁ ⊗ G₂) L c g.pG w := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D p₁ p₂ q₁ q₂ hS wM L c wL hLB hM hL e g h₁ h₂ w hQ T x jL jM cL cM
  have := g.q_hom
  have := (U₁.gt e).q_hom
  have := (U₂.gt e).q_hom
  have := hS.hom₁
  have := hS.hom₂
  refine (clause_iff (tri (thick R I e) g.pG x) (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x)
    (fun k : thK => (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left) _ _ _ (D.toPre.cub.t.s jM) (c.s jL)
    (fun k => w.s (fun _ => jM k, fun _ => jL k)) thε).2 fun y hB hG' _ => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ jM cM (fun k => Set.mem_iInter.1 hB k)
  obtain ⟨N, hN, eN⟩ := exists_good L hLB y _ jL cL (fun k => Set.mem_iInter.1 hG' k)
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.toPre.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.toPre.P.isLB y
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.BoxFamily.exists_good_at U₁.LG.isLB y
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.BoxFamily.exists_good_at U₂.LG.isLB y
  have tM₁ := (tri_map (thick R I e) (U₁.gt e).pG g.pG x _ p₁ h₁).2
  have tM₂ := (tri_map (thick R I e) (U₂.gt e).pG g.pG x _ p₂ h₂).2
  have tL₁ := (tri_map (thick R I e) (fstG I e G₁) (fstG I e (G₁ ⊗ G₂)) x _ (fst G₁ G₂)
    (thick_fstG I e (fst G₁ G₂))).2
  have tL₂ := (tri_map (thick R I e) (fstG I e G₂) (fstG I e (G₁ ⊗ G₂)) x _ (snd G₁ G₂)
    (thick_fstG I e (snd G₁ G₂))).2
  have bM := hM T.left (tri (thick R I e) g.pG x) y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [tM₁, tM₂] at bM
  have bL := hL T.left (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x) y N₁ N₂ N hN₁ hN₂ hN
  rw [tL₁, tL₂] at bL
  have v₁ := w_cub_val.{0} U₁ e T (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) y hJ₁ hN₁
  have v₂ := w_cub_val.{0} U₂ e T (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) y hJ₂ hN₂

  have fM := fun k : thK => tri_thφ (thick R I e) g.pG x g.q rfl k
  have fG := fun k : thK => tri_thφ (thick R I e) (fstG I e (G₁ ⊗ G₂)) x (𝟙 _) (Category.id_comp _).symm k
  have fM₁ := fun k : thK => tri_thφ (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) (U₁.gt e).q rfl k
  have fM₂ := fun k : thK => tri_thφ (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) (U₂.gt e).q rfl k
  have fG₁ := fun k : thK => tri_thφ (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) (𝟙 _)
    (Category.id_comp _).symm k
  have fG₂ := fun k : thK => tri_thφ (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) (𝟙 _)
    (Category.id_comp _).symm k
  have ps₁ := fun k : thK => psum_comp x ((Over.pullback (thick R I e)).map (fst G₁ G₂)) k.down
  have ps₂ := fun k : thK => psum_comp x ((Over.pullback (thick R I e)).map (snd G₁ G₂)) k.down
  have key := rel_alg thε
    (fun k => om wM y J₁ J₂ J (tri (thick R I e) g.pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k))
    (fun k => om wL y N₁ N₂ N (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x ≫ thφ (G₁ ⊗ G₂) (x3 (G₁ ⊗ G₂)) k))
    (fun k => gw w (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left y (jM k) (fun _ => jL k))
    (fun k => gw (U₁.w e) (psum (thickObj R I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) k.down).left y
      (J₁ (tri (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ D₁.toPre.P.A (x3 D₁.toPre.P.A) k))
      (fun _ => N₁ (tri (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ G₁ (x3 G₁) k)))
    (fun k => gw (U₂.w e) (psum (thickObj R I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) k.down).left y
      (J₂ (tri (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ D₂.toPre.P.A (x3 D₂.toPre.P.A) k))
      (fun _ => N₂ (tri (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ G₂ (x3 G₂) k)))
    (fun k => by
      have q := hQ T.left (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      have a₁ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ g.pG.left) ≫ p₁.left =
          tri (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ D₁.toPre.P.A (x3 D₁.toPre.P.A) k := by
        rw [Category.assoc, h₁, ← Category.assoc, ps₁ k, fM₁ k]
      have a₂ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ g.pG.left) ≫ p₂.left =
          tri (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ D₂.toPre.P.A (x3 D₂.toPre.P.A) k := by
        rw [Category.assoc, h₂, ← Category.assoc, ps₂ k, fM₂ k]
      have b₁ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ (fstG I e (G₁ ⊗ G₂)).left) ≫ (fst G₁ G₂).left =
          tri (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ G₁ (x3 G₁) k := by
        rw [Category.assoc, thick_fstG I e (fst G₁ G₂), ← Category.assoc, ps₁ k, fG₁ k]
      have b₂ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ (fstG I e (G₁ ⊗ G₂)).left) ≫ (snd G₁ G₂).left =
          tri (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ G₂ (x3 G₂) k := by
        rw [Category.assoc, thick_fstG I e (snd G₁ G₂), ← Category.assoc, ps₂ k, fG₂ k]
      rw [a₁, a₂, b₁, b₂, ps₁ k, ps₂ k, ← fM k, ← fG k, eJ k, eN k] at q
      exact q)
    bM bL v₁ v₂
  refine (val_of _ _ y J jM eJ).symm.trans (key.trans ?_)
  exact congrArg _ (val_of c _ y N jL eN)

end GlobalTheory.ProdUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningProductIso_preserves_cubicalStructure : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (L : LB (G₁ ⊗ G₂).left) (c : CubGen (G₁ ⊗ G₂) L) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → IsBoxGen (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (φ₁ := thφ D₁.toPre.P.A (x3 D₁.toPre.P.A)) (φ₂ := thφ D₂.toPre.P.A (x3 D₂.toPre.P.A)) (ε := thε) wM (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t → IsBoxGen (φ₁ := thφ G₁ (x3 G₁)) (φ₂ := thφ G₂ (x3 G₂)) wL (fst G₁ G₂ ⊗ₘ fst G₁ G₂ ⊗ₘ fst G₁ G₂).left (snd G₁ G₂ ⊗ₘ snd G₁ G₂ ⊗ₘ snd G₁ G₂).left c U₁.cubG.t U₂.cubG.t → ∀ (e : ℕ) (g : GtCoord I D.toPre e (G₁ ⊗ G₂)), g.pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → g.pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → ∀ w : LB.Iso (L.pull (fstG I e (G₁ ⊗ G₂)).left) (D.toPre.P.L.pull g.pG.left), BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL w (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → CubAlong I D.toPre e (G₁ ⊗ G₂) L c g.pG w := by
  first | exact @GlobalTheory.ProdUnif.cubAlong_prod | exact GlobalTheory.ProdUnif.cubAlong_prod | (intros; apply GlobalTheory.ProdUnif.cubAlong_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExternalTensorRigidifiedCubicalProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExternalTensorRigidifiedCubicalProduct
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.GrpBox

open GlobalTheory.SumDeg

theorem isBoxGen_extGen {X X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂)
    {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h₁ : Y ⟶ Y₁) (φ₁ : K → (Y₁ ⟶ X₁)) (e₁ : ∀ k, ψ k ≫ f₁ = h₁ ≫ φ₁ k) (t₁ : LB.Gen (LB.LinComb L₁ φ₁ ε))
    (h₂ : Y ⟶ Y₂) (φ₂ : K → (Y₂ ⟶ X₂)) (e₂ : ∀ k, ψ k ≫ f₂ = h₂ ≫ φ₂ k) (t₂ : LB.Gen (LB.LinComb L₂ φ₂ ε))
    (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) :
    IsBoxGen (CubePf.idIsoL (extLB L₁ L₂ f₁ f₂)) h₁ h₂ (extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂) t₁ t₂ := by
  intro Z r z J₁ J₂ J hJ₁ hJ₂ hJ
  have hE := good_ext (f₁ := f₁) (f₂ := f₂) hJ₁ hJ₂
  have key := gen_trans (isGen_extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂ ht₁ ht₂) r z (hE.mem ψ r) (hJ.mem ψ r)
  have k2 := gm_extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂ r z _ (hE.mem ψ r)
  rw [val_of t₁ (r ≫ h₁) z J₁ (fun k => J₁ ((r ≫ ψ k) ≫ f₁)) (fun k => by rw [Category.assoc, Category.assoc, e₁]),
    val_of t₂ (r ≫ h₂) z J₂ (fun k => J₂ ((r ≫ ψ k) ≫ f₂)) (fun k => by rw [Category.assoc, Category.assoc, e₂])]
  exact key.symm.trans k2

section Grp

variable {S : Scheme.{0}} {A A₁ A₂ : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A₁] [IsCommMonObj A₁]
  [GrpObj A₂] [IsCommMonObj A₂]

def pullCub (L : RigLB A₁) (c : CubicalStr A₁ L) (a : A ⟶ A₁) [IsMonHom a] :=
  CubePf.cubical (CubeMap.ofHom a) L c (LB.isLB_pull L.isLB _)
    (LBxP.isGen_pullAlong L.L a.left (𝟙 _) (fun _ : PUnit => eSec A₁) (fun _ => 1)
      (fun _ => eSec A) (fun _ => (CubeMap.ofHom a).e_comm) L.rig L.rigGen)

theorem exists_strBox (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsMonHom a₁] [IsMonHom a₂]
    (L₁ : RigLB A₁) (L₂ : RigLB A₂) (c₁ : CubicalStr A₁ L₁) (c₂ : CubicalStr A₂ L₂)
    (s₁ : SymGen A₁ L₁.L) (s₂ : SymGen A₂ L₂.L) (hs₁ : s₁.IsGen) (hs₂ : s₂.IsGen)
    (n₁ : LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec A₁)) (LB.oneGen L₁.L))
    (n₂ : LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec A₂)) (LB.oneGen L₂.L)) :
    ∃ (L : RigLB A) (c : CubicalStr A L) (s : SymGen A L.L)
      (w : LB.Iso L.L (extLB L₁.L L₂.L a₁.left a₂.left)), s.IsGen ∧
      LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L) ∧
      StrBox a₁ a₂ w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  have hL := isLB_extLB L₁.isLB L₂.isLB a₁.left a₂.left
  refine ⟨⟨extLB L₁.L L₂.L a₁.left a₂.left,
      extAt L₁.L L₂.L a₁.left a₂.left (eSec A) 1 _ (eSec_comp a₁) L₁.rig _ (eSec_comp a₂) L₂.rig, hL,
      isGen_extAt _ _ _ _ _ _ _ _ _ _ _ _ L₁.rigGen L₂.rigGen⟩,
    tensCub (pullCub L₁ c₁ a₁) (pullCub L₂ c₂ a₂) _ hL _,
    extGen L₁.L L₂.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) s₁ a₂.left _ (inv_comp a₂) s₂,
    CubePf.idIsoL _, isGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂, ?_, CubePf.idIsoL_isGen hL,
    isBoxGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ L₁.rigGen L₂.rigGen,
    isBoxGen_extGen L₁.L L₂.L a₁.left a₂.left (thφ A (x3 A)) thε
      (a₁ ⊗ₘ a₁ ⊗ₘ a₁).left (thφ A₁ (x3 A₁)) (fun I => (CubeMap.ofHom a₁).psum_comm I.down) c₁.t
      (a₂ ⊗ₘ a₂ ⊗ₘ a₂).left (thφ A₂ (x3 A₂)) (fun I => (CubeMap.ofHom a₂).psum_comm I.down) c₂.t
      c₁.isGen c₂.isGen,
    isBoxGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂⟩
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at L₁.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at L₂.isLB y
  have o : eSec A ≫ (ι[A]).left = eSec A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[A] ≫ ι[A] = η[A])
  have v₁ : val s₁ (eSec A₁) y J₁ = 1 := by
    have v := val_corr hJ₁ n₁ (𝟙 _)
    rwa [val_pull hJ₁, Category.id_comp, val_one] at v
  have v₂ : val s₂ (eSec A₂) y J₂ = 1 := by
    have v := val_corr hJ₂ n₂ (𝟙 _)
    rwa [val_pull hJ₂, Category.id_comp, val_one] at v
  have e := (val_extGen L₁.L L₂.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) s₁ a₂.left _ (inv_comp a₂) s₂
    hs₁ hs₂ (eSec A) hJ hJ₁ hJ₂).trans (congrArg₂ (· * ·) (prod_sym (eSec A) _) rfl)
  rw [o, mul_inv_cancel, eSec_comp, eSec_comp, v₁, v₂, _root_.mul_one, _root_.mul_one] at e
  rw [val_pull hJ, Category.id_comp, val_one]
  exact e

end Grp

theorem exists_prod : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : RigLB G₁) (L₂ : RigLB G₂) (c₁ : CubicalStr G₁ L₁) (c₂ : CubicalStr G₂ L₂) (s₁ : SymGen G₁ L₁.L) (s₂ : SymGen G₂ L₂.L), s₁.IsGen → s₂.IsGen → LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec G₁)) (LB.oneGen L₁.L) → LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec G₂)) (LB.oneGen L₂.L) → ∃ (L : RigLB (G₁ ⊗ G₂)) (c : CubicalStr (G₁ ⊗ G₂) L) (s : SymGen (G₁ ⊗ G₂) L.L) (w : LB.Iso L.L (extLB L₁.L L₂.L (fst G₁ G₂).left (snd G₁ G₂).left)), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec (G₁ ⊗ G₂))) (LB.oneGen L.L) ∧ StrBox (fst G₁ G₂) (snd G₁ G₂) w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  intro S G₁ G₂ _ _ _ _ L₁ L₂ c₁ c₂ s₁ s₂ hs₁ hs₂ n₁ n₂
  exact exists_strBox (fst G₁ G₂) (snd G₁ G₂) L₁ L₂ c₁ c₂ s₁ s₂ hs₁ hs₂ n₁ n₂

end GlobalTheory.GrpBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExternalTensorRigidifiedCubicalProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_externalTensor_rigidified_cubical_product : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : RigLB G₁) (L₂ : RigLB G₂) (c₁ : CubicalStr G₁ L₁) (c₂ : CubicalStr G₂ L₂) (s₁ : SymGen G₁ L₁.L) (s₂ : SymGen G₂ L₂.L), s₁.IsGen → s₂.IsGen → LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec G₁)) (LB.oneGen L₁.L) → LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec G₂)) (LB.oneGen L₂.L) → ∃ (L : RigLB (G₁ ⊗ G₂)) (c : CubicalStr (G₁ ⊗ G₂) L) (s : SymGen (G₁ ⊗ G₂) L.L) (w : LB.Iso L.L (extLB L₁.L L₂.L (fst G₁ G₂).left (snd G₁ G₂).left)), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec (G₁ ⊗ G₂))) (LB.oneGen L.L) ∧ StrBox (fst G₁ G₂) (snd G₁ G₂) w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  first | exact @GlobalTheory.GrpBox.exists_prod | exact GlobalTheory.GrpBox.exists_prod | (intros; apply GlobalTheory.GrpBox.exists_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAdd
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory

namespace PDiv

theorem finrank_quot_kerIdeal_comp_le {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C] [Module.Finite k A]
    [Module.Finite k B] (ψ : B →ₐc[k] A) (φ : C →ₐc[k] B) :
    Module.finrank k (A ⧸ kerIdeal (ψ.comp φ)) ≤
      Module.finrank k (A ⧸ kerIdeal ψ) * Module.finrank k (B ⧸ kerIdeal φ) := by
  have hHopf (X Y : Type) [CommRing X] [CommRing Y] [HopfAlgebra k X]
      [HopfAlgebra k Y] (f : Y →ₐc[k] X) : (kerIdeal f).IsHopfIdeal k := by
    refine {
    counit_eq_zero := by
      intro x hx
      exact (kerIdeal_le_ker_iff f (counitAlgHom k X)).2 (fun c => by simp) hx
    map_mkQ_comul_eq_zero := by
      intro x hx
      have h0 := (kerIdeal_le_ker_iff f (Ideal.Quotient.mkₐ k (kerIdeal f))).1
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      have h : kerIdeal f ≤ RingHom.ker
          ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
            (Ideal.Quotient.mkₐ k (kerIdeal f))).comp (comulAlgHom k X)) := by
        refine (kerIdeal_le_ker_iff f _).2 fun c => ?_
        have key : ∀ t : Y ⊗[k] Y, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
            (Ideal.Quotient.mkₐ k (kerIdeal f)) (pullbackTwo f t) =
            algebraMap k _ (counit (R := k)
              (TensorProduct.lid k Y (LinearMap.rTensor Y (counit (R := k) (A := Y)) t))) := by
          intro t
          induction t with
          | add x y hx hy => simp only [map_add (f := _), hx, hy]
          | tmul x y =>
            rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
              TensorProduct.lid_tmul, map_smul]
            erw [h0, h0]
            simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
              smul_smul, mul_comm]
        rw [AlgHom.comp_apply, comulAlgHom_apply, ← pullTwo_comul, key, rTensor_counit_comul,
          TensorProduct.lid_tmul, one_smul]
      exact h hx
    antipode_mem := by
      intro x hx
      have h : kerIdeal f ≤ (kerIdeal f).comap (HopfAlgebra.antipodeAlgHom k X) := by
        refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
        have ha' : counit (R := k) a = 0 := ha
        change HopfAlgebra.antipode k (f a) ∈ kerIdeal f
        rw [← bialgHom_map_antipode]
        exact Ideal.mem_map_of_mem (f : Y →ₐ[k] X) (by simp [RingHom.mem_ker, ha'])
      exact h hx
    }
  haveI := hHopf A C (ψ.comp φ)
  haveI := hHopf B C φ
  let πA : A →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) := Bialgebra.Quotient.mkBialgHom (kerIdeal (ψ.comp φ))
  let πB : B →ₐc[k] B ⧸ kerIdeal φ := Bialgebra.Quotient.mkBialgHom (kerIdeal φ)
  have hπA : Function.Surjective πA := Ideal.Quotient.mk_surjective
  have hπB : Function.Surjective πB := Ideal.Quotient.mk_surjective
  have hA : ∀ c, πA (ψ (φ c)) = algebraMap k _ (counit c) :=
    (kerIdeal_le_ker_iff (ψ.comp φ) (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h1 : kerIdeal φ ≤ RingHom.ker (πA.comp ψ : B →ₐ[k] A ⧸ kerIdeal (ψ.comp φ)) :=
    (kerIdeal_le_ker_iff φ _).2 fun c => hA c
  let m' : (B ⧸ kerIdeal φ) →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) :=
    liftSurj πB hπB (πA.comp ψ) fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)
  have hm' : ∀ b, m' (πB b) = πA (ψ b) := fun b =>
    liftSurj_apply πB hπB (πA.comp ψ) (fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)) b
  let q : A →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    (Ideal.Quotient.mkₐ k (kerIdeal m')).comp (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp hπA
  have h0 := (kerIdeal_le_ker_iff m' (Ideal.Quotient.mkₐ k (kerIdeal m'))).1
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h4 : kerIdeal ψ ≤ RingHom.ker q := (kerIdeal_le_ker_iff ψ q).2 fun b => by
    change Ideal.Quotient.mkₐ k (kerIdeal m') (πA (ψ b)) = _
    rw [← hm', h0, CoalgHomClass.counit_comp_apply]
  let q'' : (A ⧸ kerIdeal ψ) →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    Ideal.Quotient.liftₐ (kerIdeal ψ) q h4
  have hq'' : Function.Surjective q''.toLinearMap := fun x => by
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  rw [finrank_eq_ker_mul_range k _ _ m']
  exact Nat.mul_le_mul (LinearMap.finrank_le_finrank_of_surjective hq'')
    (LinearMap.finrank_range_le _)

end PDiv

namespace Dieu

theorem hasLogDeg_comp_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K) (a b c : ℕ),
    HasLogDeg f a → HasLogDeg g b → HasLogDeg (f ≫ g) c → c ≤ a + b := by
  intro p _ k _ _ G H K f g a b c ⟨N₁, h₁⟩ ⟨N₂, h₂⟩ ⟨N₃, h₃⟩
  let n := max N₁ (max N₂ N₃)
  have e₁ := h₁ n (le_max_left _ _)
  have e₂ := h₂ n (le_trans (le_max_left _ _) (le_max_right _ _))
  have e₃ := h₃ n (le_trans (le_max_right _ _) (le_max_right _ _))
  have hle := finrank_quot_kerIdeal_comp_le (f.app n) (g.app n)
  rw [← comp_app, e₃, e₁, e₂, ← pow_add] at hle
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

end Dieu

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAddStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K) (a b c : ℕ), HasLogDeg f a → HasLogDeg g b → HasLogDeg (f ≫ g) c → c ≤ a + b := by
  first | exact @GlobalTheory.Dieu.hasLogDeg_comp_le | exact GlobalTheory.Dieu.hasLogDeg_comp_le | (intros; apply GlobalTheory.Dieu.hasLogDeg_comp_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeightedPairOrbitsOfFiniteWeightedFixedPoi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrbitsCxFNeZero
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} {β : G.Cˣ} {x : (AfP p ⊗[ℚ] G.C)ˣ}
  {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t} {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)}

theorem posV_val_ne_zero (z : PosV G v β) : z.1 ≠ 0 := by
  intro h
  have hz := z.2
  rw [h] at hz
  simp at hz

theorem fixL_smul_vec_iff (y : grp G β) (z : Fin G.n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    FixL G v β y (c • z) ↔ FixL G v β y z := by
  unfold FixL
  simp only [Matrix.mulVec_smul]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [smul_comm e c z] at he
    exact smul_right_injective _ hc he
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [he, smul_comm]⟩

variable (G v β x t hx Kf K')

def orbOfDat (d : Dat G v β) : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
  Quotient.mk'' (LeftCosets.mk _ _ d.1, (Projectivization.mk ℂ d.2.1 (posV_val_ne_zero d.2) : PLv G v β))

theorem orbOfDat_eq_of_same {a b : Dat G v β} (h : Same G v β x t hx Kf K' a b) :
    orbOfDat G v β x t hx Kf K' a = orbOfDat G v β x t hx Kf K' b := by
  obtain ⟨g, k, c, hk1, hk2, hc, h1, h2⟩ := h
  symm
  apply Quotient.sound
  refine ⟨g, Prod.ext ?_ ?_⟩
  · change g • LeftCosets.mk ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1 = LeftCosets.mk _ _ b.1
    rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk, h1, MonoidHom.prod_apply, inv_mul_cancel_left]
    exact Subgroup.mem_prod.2 ⟨hk1, hk2⟩
  · change Projectivization.map (Matrix.toLin' (toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ))
      (toV_injective G v β g) (Projectivization.mk ℂ a.2.1 (posV_val_ne_zero a.2)) =
      Projectivization.mk ℂ b.2.1 (posV_val_ne_zero b.2)
    rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨c⁻¹, ?_⟩
    rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul, Matrix.toLin'_apply]

def DatWt (f : G.GAf → ℂ) (f' : Gr G 1 → ℂ) (d : Dat G v β) : Prop :=
  ∃ y : grp G β, FixL G v β y d.2.1 ∧
    f (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * f' (d.1.2⁻¹ * toP1 G β y * d.1.2) ≠ 0

theorem datWt_iff_of_same {f : G.GAf → ℂ} {f' : Gr G 1 → ℂ} (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) {a b : Dat G v β} (h : Same G v β x t hx Kf K' a b) :
    DatWt G v β x t hx f f' a ↔ DatWt G v β x t hx f f' b := by
  obtain ⟨g, k, c, hk1, hk2, hc, h1, h2⟩ := h
  have e1 : ∀ y : grp G β, b.1.1⁻¹ * toAfF G β x t hx (g * y * g⁻¹) * b.1.1 =
      k.1⁻¹ * (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * k.1 := by
    intro y; rw [h1]; simp only [Prod.fst_mul, map_mul, map_inv]; group
  have e2 : ∀ y : grp G β, b.1.2⁻¹ * toP1 G β (g * y * g⁻¹) * b.1.2 =
      k.2⁻¹ * (a.1.2⁻¹ * toP1 G β y * a.1.2) * k.2 := by
    intro y; rw [h1]; simp only [Prod.snd_mul, map_mul, map_inv]; group
  have efix : ∀ y : grp G β, FixL G v β (g * y * g⁻¹) b.2.1 ↔ FixL G v β y a.2.1 := by
    intro y
    rw [h2, fixL_smul_vec_iff _ _ hc]
    exact (fixL_conj_iff p G v β y g a.2.1).symm
  constructor
  · rintro ⟨y, hy, hne⟩
    refine ⟨g * y * g⁻¹, (efix y).2 hy, ?_⟩
    rwa [e1, e2, hf _ hk1, hf' _ hk2]
  · rintro ⟨y', hy', hne⟩
    obtain ⟨y, rfl⟩ : ∃ y, y' = g * y * g⁻¹ := ⟨g⁻¹ * y' * g, by group⟩
    refine ⟨y, (efix y).1 hy', ?_⟩
    rwa [e1, e2, hf _ hk1, hf' _ hk2] at hne

end GlobalTheory.CxUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeightedPairOrbitsOfFiniteWeightedFixedPoi
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

theorem finite_orbits_of_finite_pts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), Set.Finite {q : Pts G v β x t hx Kf K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} → {o : MulAction.orbitRel.Quotient (grp G β) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') | ∃ y, GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y ≠ 0}.Finite := by
  intro p _ G v wt Kf f hfi K' f' hfi' β x t hx hT
  let F : Pts G v β x t hx Kf K' → MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
    Quot.lift (orbOfDat G v β x t hx Kf K') (fun a b h => orbOfDat_eq_of_same G v β x t hx _ _ h)
  let PL : Pts G v β x t hx Kf K' → Prop :=
    Quot.lift (DatWt G v β x t hx f f') (fun a b h => propext (datWt_iff_of_same G v β x t hx _ _ hfi hfi' h))
  refine (hT.image F).subset ?_
  rintro o ⟨y, hy⟩
  unfold cxF at hy
  split_ifs at hy with hc
  on_goal 2 => exact absurd rfl hy
  let d : Dat G v β := (LeftCosets.rep _ _ (Quotient.out o).1,
    ⟨Projectivization.rep ((Quotient.out o).2 : Projectivization ℂ (Fin G.n → ℂ)), hc.1⟩)
  have hd : DatWt G v β x t hx f f' d := ⟨y, hc.2, left_ne_zero_of_mul hy⟩
  refine ⟨Quot.mk _ d, ?_, ?_⟩
  · have e : PL (Quot.mk _ (Quot.out (Quot.mk (Same G v β x t hx Kf K') d))) = PL (Quot.mk _ d) :=
      congrArg PL (Quot.out_eq _)
    exact (e : DatWt G v β x t hx f f' _ = DatWt G v β x t hx f f' d).mpr hd
  · show orbOfDat G v β x t hx Kf K' d = o
    simp only [orbOfDat, d, LeftCosets.mk_rep]
    convert Quotient.out_eq' o using 2
    exact Prod.ext rfl (Projectivization.mk_rep _)

end GlobalTheory.CxUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeightedPairOrbitsOfFiniteWeightedFixedPoiStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_weightedPairOrbits_of_finite_weightedFixedPoints : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), Set.Finite {q : Pts G v β x t hx Kf K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} → {o : MulAction.orbitRel.Quotient (grp G β) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') | ∃ y, GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y ≠ 0}.Finite := by
  first | (exact @GlobalTheory.CxUnfold.finite_orbits_of_finite_pts) | (exact GlobalTheory.CxUnfold.finite_orbits_of_finite_pts) | (intros; apply GlobalTheory.CxUnfold.finite_orbits_of_finite_pts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBundlePullbackAdjointActionEqDiagonalPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisAltLast
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CasimirPull

open GlobalTheory.CechPic

theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (act : O → (A ⟶ A)), IsRAct A act → Adj A Q bar act → ∀ (G : Over S) [GrpObj G] (pr : Fin r → (G ⟶ A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin r → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → ∀ Φ : A ⟶ G, (∀ u, Φ ≫ pr u = act (e u)) → LBIso ((LB.LinComb Q (K := Fin r × Fin r) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)).pull Φ.left) (LB.LinComb Q (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ))) := by
  intro S A _ _ Q hA hQ h₁ h₂ _ hamp O _ bar r e W d _ _ _ _ hsum act hact hadj G _ pr _ _ Φ hΦ
  have hbi := GlobalTheory.Biadditive.biadditive_of_triv_axes GlobalTheory.globalFns_holds S A
    (Q.pull (lift (𝟙 A) (𝟙 A)).left) hA (pull_isLB hQ _) hamp Q hQ h₁ h₂

  have add2 : ∀ (T : Over S) (y x x' : T ⟶ A), pull (lift y (x * x')).left (cls Q hQ) =
      pull (lift y x).left (cls Q hQ) + pull (lift y x').left (cls Q hQ) := by
    intro T y x x'
    have z := (cls_eq_zero_iff (LB.isLB_linComb hQ _ _)).2 (hbi T x x' y).2
    rw [cls_linComb hQ, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    rw [← sub_eq_zero, ← z]
    abel

  have adjB : ∀ (T : Over S) (x y : T ⟶ A) (a : O), pull (lift (x ≫ act a) y).left (cls Q hQ) =
      pull (lift x (y ≫ act (bar a))).left (cls Q hQ) := by
    intro T x y a
    have h := (cls_eq_iff (pull_isLB hQ _) (pull_isLB hQ _)).2 (hadj a)
    rw [cls_pull hQ, cls_pull hQ] at h
    have k₁ : (lift x y).left ≫ (lift (fst A A ≫ act a) (snd A A)).left = (lift (x ≫ act a) y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd]
    have k₂ : (lift x y).left ≫ (lift (fst A A) (snd A A ≫ act (bar a))).left = (lift x (y ≫ act (bar a))).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
    rw [← k₁, ← k₂, pull_comp, pull_comp, h]
  let f : O →+ Pic A.left := AddMonoidHom.mk' (fun a => pull (lift (𝟙 A) (act a)).left (cls Q hQ))
    (fun a b => by simp only [hact.2.2.2 a b]; exact add2 A (𝟙 A) _ _)
  have term : ∀ i j : Fin r, pull Φ.left (pull (lift (pr i) (pr j)).left (cls Q hQ)) =
      f (e j * bar (e i)) := by
    intro i j
    rw [← pull_comp, ← Over.comp_left, comp_lift, hΦ, hΦ]
    have := adjB A (𝟙 A) (act (e j)) (e i)
    rw [Category.id_comp] at this
    rw [this, ← hact.2.2.1]
    rfl
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb hQ _ _) _) (LB.isLB_linComb hQ _ _)).1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_pull (LB.isLB_linComb hQ _ _), cls_linComb hQ, cls_linComb hQ, map_sum, Fin.sum_univ_one]
  simp only [map_zsmul, term]
  rw [Fintype.sum_prod_type]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_zsmul, ← map_sum, hsum]
  rw [← nsmul_one, map_nsmul, natCast_zsmul]
  rw [map_nsmul]
  show d • pull (lift (𝟙 A) (act 1)).left (cls Q hQ) = _
  rw [hact.2.1]

end GlobalTheory.CasimirPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBundlePullbackAdjointActionEqDiagonalPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ElRep

theorem sq_ext {S : Scheme.{0}} (A : Over S) {X : Scheme.{0}} (f g : X ⟶ (A ⊗ A).left)
    (h₁ : f ≫ (fst A A).left = g ≫ (fst A A).left) (h₂ : f ≫ (snd A A).left = g ≫ (snd A A).left) : f = g :=
  pullback.hom_ext h₁ h₂

theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (B' : Over T) [GrpObj B'] (φB : B'.left ⟶ (Out.powObj A r).left) (pr' : Fin r → (B' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → IsGrpPullback B' (Out.powObj A r) t φB → (∀ u, IsMonHom (pr' u)) → (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ (act : O → (A' ⟶ A')), IsRAct A' act → Adj A' (Q.pull φ₂') bar act → ∀ Φ : A' ⟶ B', (∀ u, Φ ≫ pr' u = act (e u)) → LBIso ((diagPow A Q d).pull φ') (((formLB A Q (Out.powPr A (n := r)) W).pull φB).pull Φ.left) := by
  intro S A _ _ Q hQ O _ bar r e W d hbar hspan hW hd hsum T t A' _ _ φ' φ₂' B' _ φB pr' hApb hsq hBpb hpr' hprφ
    huniq act hact hadj Φ hΦ
  have hQ' : QHyp A' (Q.pull φ₂') := GlobalTheory.T.symmetricBiextensionHyp_pullback_of_groupPullback S T t A A' φ' φ₂' Q hApb hsq hQ
  obtain ⟨hA', hL', g₁, g₂, hsym', hamp'⟩ := hQ'
  have C := GlobalTheory.CasimirPull.main T A' (Q.pull φ₂') hA' hL' g₁ g₂ hsym' hamp' O bar r e W d hbar hspan hW hd hsum
    act hact hadj B' pr' hpr' huniq Φ hΦ
  have hQL : Q.IsLB := hQ.2.1
  have e₁ : ∀ u v : Fin r, (lift (pr' u) (pr' v)).left ≫ φ₂' =
      φB ≫ (lift (Out.powPr A (n := r) u) (Out.powPr A (n := r) v)).left := fun u v => by
    apply sq_ext A
    · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hprφ, Category.assoc,
        ← Over.comp_left, lift_fst]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hprφ, Category.assoc,
        ← Over.comp_left, lift_snd]
  have e₂ : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂' = φ' ≫ (lift (𝟙 A) (𝟙 A)).left := by
    apply sq_ext A
    · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp,
        Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp,
        Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id]
  have C' := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB (LB.isLB_linComb hL' _ _) _) (LB.isLB_linComb hL' _ _)).2 C
  rw [GlobalTheory.CechPic.cls_pull (LB.isLB_linComb hL' _ _), GlobalTheory.CechPic.cls_linComb hL', GlobalTheory.CechPic.cls_linComb hL',
    GlobalTheory.CechPic.cls_pull hQL] at C'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, ← GlobalTheory.CechPic.pull_comp, Category.assoc, e₁, e₂] at C'
  unfold diagPow formLB
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB (LB.isLB_linComb hQL _ _) _)
    (pull_isLB (pull_isLB (LB.isLB_linComb hQL _ _) _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull (LB.isLB_linComb hQL _ _), GlobalTheory.CechPic.cls_pull (pull_isLB (LB.isLB_linComb hQL _ _) _),
    GlobalTheory.CechPic.cls_pull (LB.isLB_linComb hQL _ _), GlobalTheory.CechPic.cls_linComb hQL, GlobalTheory.CechPic.cls_linComb hQL]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, ← GlobalTheory.CechPic.pull_comp, Category.assoc]
  exact C'.symm

end GlobalTheory.ElRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBundlePullbackAdjointActionEqDiagonalPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formBundle_pullback_adjointAction_eq_diagonalPower : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (B' : Over T) [GrpObj B'] (φB : B'.left ⟶ (Out.powObj A r).left) (pr' : Fin r → (B' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → IsGrpPullback B' (Out.powObj A r) t φB → (∀ u, IsMonHom (pr' u)) → (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ (act : O → (A' ⟶ A')), IsRAct A' act → Adj A' (Q.pull φ₂') bar act → ∀ Φ : A' ⟶ B', (∀ u, Φ ≫ pr' u = act (e u)) → LBIso ((diagPow A Q d).pull φ') (((formLB A Q (Out.powPr A (n := r)) W).pull φB).pull Φ.left) := by
  first | exact @GlobalTheory.ElRep.main | exact GlobalTheory.ElRep.main | (intros; apply GlobalTheory.ElRep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitUniformisationMumfordBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitUniformisationMumfordBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TraitUnif

theorem exists_generic_fibre_pull : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), Function.Injective φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (AW : PolAV (Sp (FractionRing W))) (genW : ((Over.pullback (jK W)).obj ((Over.pullback (spMap φ)).obj G)) ≅ AW.A) (κ₁ : pullback ((Over.pullback (spMap φ)).obj G).hom (jK W) ⟶ pullback G.hom (jK R)), IsMonHom genW.hom ∧ κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst ((Over.pullback (spMap φ)).obj G).hom (jK W) ≫ pullback.fst G.hom (spMap φ) ∧ LBIso (AW.L.pull genW.hom.left) ((A.L.pull gen.hom.left).pull κ₁) := by
  intro R W _ _ _ _ _ _ φ hφ G _ _ A gen hgen
  haveI : IsMonHom gen.hom := hgen
  set gφ := IsFractionRing.map (K := FractionRing R) (L := FractionRing W) hφ with hgφ
  have hsq : jK W ≫ spMap φ = spMap gφ ≫ jK R := by
    simp only [hgφ, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have hmono : Mono (jK R) := by
    have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    infer_instance
  let GV := (Over.pullback (spMap φ)).obj G
  have hβ := isGrpPullback_pullback G (spMap φ)
  let κ₁ : pullback GV.hom (jK W) ⟶ pullback G.hom (jK R) :=
    pullback.lift (pullback.fst GV.hom (jK W) ≫ pullback.fst G.hom (spMap φ)) (pullback.snd GV.hom (jK W) ≫ spMap gφ)
      (by rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc])
  have hκf : κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst GV.hom (jK W) ≫ pullback.fst G.hom (spMap φ) :=
    pullback.lift_fst _ _ _
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK W)).obj GV).hom ≫ spMap gφ :=
    pullback.lift_snd _ _ _
  have hκ : IsGrpPullback ((Over.pullback (jK W)).obj GV) ((Over.pullback (jK R)).obj G) (spMap gφ) κ₁ :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback GV (jK W)).comp hβ).congr hsq hκf.symm) w
  have hκA : IsGrpPullback ((Over.pullback (jK W)).obj GV) A.A (spMap gφ) (κ₁ ≫ gen.hom.left) :=
    (hκ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  obtain ⟨P', g, hg, -, hmul, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap gφ) A
  have hP' : IsGrpPullback P'.A A.A (spMap gφ) g := by
    refine ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩
    have ex : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    have ey : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hmul]
    rfl
  obtain ⟨e, he, heq⟩ := grpPullback_iso hκA hP'
  refine ⟨P', e, κ₁, he, hκf, ?_⟩
  have h1 : LBIso (P'.L.pull e.hom.left) ((A.L.pull g).pull e.hom.left) :=
    GlobalTheory.FamRep.lbIso_pull (LBIso.symm ⟨t, ht⟩) _
  have h2 : LBIso ((A.L.pull g).pull e.hom.left) (A.L.pull (e.hom.left ≫ g)) :=
    GlobalTheory.FamRep.lbIso_pull_pull A.isLB g e.hom.left
  have h3 : LBIso ((A.L.pull gen.hom.left).pull κ₁) (A.L.pull (κ₁ ≫ gen.hom.left)) :=
    GlobalTheory.FamRep.lbIso_pull_pull A.isLB gen.hom.left κ₁
  rw [heq] at h2
  exact LBIso.trans (pull_isLB P'.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB (pull_isLB A.isLB _) _) h1
    (LBIso.trans (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) h2 h3.symm)

theorem extLam_pull_square : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)), IsGrpPullback G₁ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst G₁.hom (jK R') ≫ β → ∀ (L : LB ((Over.pullback (jK R)).obj G).left) (N : LB ((Over.pullback (jK R')).obj G₁).left) (PP : LB (G2 G).left), L.IsLB → N.IsLB → LBIso N (L.pull κ₁) → ExtLam G L PP → ExtLam G₁ N (PP.pull β₂) := by
  intro R R' _ _ _ _ _ _ ρ hρ G _ _ G₁ _ _ β β₂ κ₁ hβ hsqβ hκf L N PP hL hN hNL hExt
  have hsq : jK R' ≫ spMap ρ =
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have hmono : Mono (jK R) := by
    have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    infer_instance
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK R')).obj G₁).hom ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) := by
    apply (cancel_mono (jK R)).1
    rw [Category.assoc, Category.assoc]
    change κ₁ ≫ pullback.snd G.hom (jK R) ≫ jK R = pullback.snd G₁.hom (jK R') ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R
    rw [← pullback.condition, ← Category.assoc, hκf, Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition,
      Category.assoc, hsq]
  have hκ : IsGrpPullback ((Over.pullback (jK R')).obj G₁) ((Over.pullback (jK R)).obj G)
      (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) κ₁ :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback G₁ (jK R')).comp hβ).congr hsq hκf.symm) w
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R')).obj G₁) := Functor.isCommMonObj_obj
  obtain ⟨β₂κ, hsqκ, Hκ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G₁) κ₁ hκ
  obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _ (isGrpPullback_pullback G (jK R))
  refine ⟨pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩
  have H1 := Hκ L N _ PP g₂ hL hN hExt.1 hNL (hExt.2 g₂ hg₂)
  have e : β₂κ ≫ g₂ = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (β₂κ ≫ g₂) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      rw [Category.assoc, hg₂.1, ← Category.assoc, hsqκ.1, Category.assoc, hκf, Category.assoc, hsqβ.1,
        reassoc_of% hκ₂.1]
    · show (β₂κ ≫ g₂) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      rw [Category.assoc, hg₂.2, ← Category.assoc, hsqκ.2, Category.assoc, hκf, Category.assoc, hsqβ.2,
        reassoc_of% hκ₂.2]
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hExt.1 _) (pull_isLB (pull_isLB hExt.1 _) _) H1
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => e) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

theorem exists_trait_unif_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G (spMap φ) βW ∧ Geo.Tor.IsSquare βW βW₂ ∧ LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  have := hR.1.1
  have := hR.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨AV, genV, κ₁, hgenV, hκ, hLV⟩ := exists_generic_fibre_pull R V φ hφ G A gen hgen
  obtain ⟨βV₂, hsqV, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G _ _ (isGrpPullback_pullback G (spMap φ))
  have hExtV := extLam_pull_square R V φ hφ G _ _ βV₂ κ₁ (isGrpPullback_pullback G (spMap φ)) hsqV hκ _ _ PP
    (pull_isLB A.isLB _) (pull_isLB AV.isLB _) hLV hPP
  have hGV : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback (spMap φ) G hG
  obtain ⟨R', _, _, _, ρ, D₁, G₁, _, _, β, β₂, A₁, U₁, hR', hρ, hβ, hsq, hLam⟩ :=
    GlobalTheory.T.exists_uniformisation_finiteExt_sameMumfordBundle V hV _ hGV AV genV hgenV _ hExtV
  have hρloc : IsLocalHom ρ := RingHom.IsIntegral.isLocalHom hρ.2.2.to_isIntegral hρ.2.1
  refine ⟨R', _, _, _, ρ.comp φ, G₁, _, _, β ≫ pullback.fst G.hom (spMap φ), β₂ ≫ βV₂, D₁, A₁, U₁, hR',
    hρ.2.1.comp hφ, ?_, ?_, ?_, ?_⟩
  · exact RingHom.isLocalHom_comp ρ φ
  · refine (hβ.comp (isGrpPullback_pullback G (spMap φ))).congr ?_ rfl
    simp [spMap, Spec.map_comp]
  · refine ⟨?_, ?_⟩
    · rw [Category.assoc, hsqV.1, ← Category.assoc, hsq.1, Category.assoc]
    · rw [Category.assoc, hsqV.2, ← Category.assoc, hsq.2, Category.assoc]
  · exact LBIso.trans (DVR.linComb_isLB _ U₁.LG.isLB _ _) (pull_isLB (pull_isLB hPP.1 _) _) (pull_isLB hPP.1 _) hLam
      (GlobalTheory.FamRep.lbIso_pull_pull hPP.1 βV₂ β₂)
end GlobalTheory.Mum.TraitUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitUniformisationMumfordBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_uniformisation_mumfordBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G (spMap φ) βW ∧ Geo.Tor.IsSquare βW βW₂ ∧ LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) := by
  first | exact @GlobalTheory.Mum.TraitUnif.exists_trait_unif_lam | exact GlobalTheory.Mum.TraitUnif.exists_trait_unif_lam | (intros; apply GlobalTheory.Mum.TraitUnif.exists_trait_unif_lam <;> assumption)
end
end
