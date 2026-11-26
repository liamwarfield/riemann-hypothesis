module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT

theorem objMap_comp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂) (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → Nonempty (ObjMap o₁ o₃ (f ≫ g)) := by
  intro p _ D R _ b N S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g h₁ h₂
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorObjectPullback_comp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂) (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → Nonempty (ObjMap o₁ o₃ (f ≫ g)) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp | exact GlobalTheory.UPel.HT.objMap_comp | (intros; apply GlobalTheory.UPel.HT.objMap_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.KS

namespace GlobalTheory.KS.PowPB

theorem powMap_pr {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) :
    powMap f φ hφ m ≫ (pr A i).left = (pr A' i).left ≫ φ := by
  unfold powMap
  rw [← Over.comp_left, Pi.lift_comp_π]
  rfl

theorem powMap_w {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) :
    powMap f φ hφ m ≫ (pow A m).hom = (pow A' m).hom ≫ f := by
  unfold powMap
  exact Over.w _

theorem pow_left_hom_ext {S : Scheme.{0}} {A : Over S} {m : ℕ} {T : Scheme.{0}} (g₁ g₂ : T ⟶ (pow A m).left)
    (hh : g₁ ≫ (pow A m).hom = g₂ ≫ (pow A m).hom) (hi : ∀ i, g₁ ≫ (pr A i).left = g₂ ≫ (pr A i).left) :
    g₁ = g₂ := by
  let u₁ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m := Over.homMk g₁ rfl
  let u₂ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m := Over.homMk g₂ (by simpa using hh.symm)
  have : u₁ = u₂ := Pi.hom_ext _ _ (fun i => by
    ext
    simpa [u₁, u₂] using hi i)
  exact congrArg CommaMorphism.left this

noncomputable def liftPow {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) : T ⟶ (pow A' m).left :=
  (Pi.lift (fun i : Fin m => (Over.homMk (H.lift (a ≫ (pr A i).left) b (by rw [Category.assoc, Over.w]; exact w))
    (H.lift_snd _ _ _) : Over.mk b ⟶ A')) : Over.mk b ⟶ pow A' m).left

theorem liftPow_w {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) : liftPow H m a b w ≫ (pow A' m).hom = b := by
  unfold liftPow
  exact Over.w _

theorem liftPow_pr {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) (i : Fin m) :
    liftPow H m a b w ≫ (pr A' i).left = H.lift (a ≫ (pr A i).left) b (by rw [Category.assoc, Over.w]; exact w) := by
  unfold liftPow
  rw [← Over.comp_left, Pi.lift_comp_π]
  rfl

theorem powMap_isPullback : ∀ (S S' : Scheme.{0}) (A : Over S) (A' : Over S') (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f), IsPullback φ A'.hom A.hom f →
    ∀ m : ℕ, IsPullback (powMap f φ hφ m) (pow A' m).hom (pow A m).hom f := by
  intro S S' A A' f φ hφ H m
  refine ⟨⟨powMap_w f φ hφ m⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => liftPow H m s.fst s.snd s.condition) ?_ ?_ ?_⟩⟩
  · intro s
    apply pow_left_hom_ext
    · rw [Category.assoc, powMap_w, ← Category.assoc, liftPow_w, s.condition]
    · intro i
      rw [Category.assoc, powMap_pr, ← Category.assoc, liftPow_pr, H.lift_fst]
  · intro s
    exact liftPow_w H m _ _ _
  · intro s u h₁ h₂
    apply pow_left_hom_ext
    · rw [h₂, liftPow_w]
    · intro i
      rw [liftPow_pr]
      apply H.hom_ext
      · rw [H.lift_fst, Category.assoc, ← powMap_pr f φ hφ, ← Category.assoc, h₁]
      · rw [H.lift_snd, Category.assoc, Over.w, h₂]

end GlobalTheory.KS.PowPB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrePowerMapOfTotalSpaces_isPullback : ∀ (S S' : Scheme.{0}) (A : Over S) (A' : Over S') (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (hφ : φ ≫ A.hom = A'.hom ≫ f), IsPullback φ A'.hom A.hom f → ∀ m : ℕ, IsPullback (powMap f φ hφ m) (pow A' m).hom (pow A m).hom f := by
  first | (exact @GlobalTheory.KS.PowPB.powMap_isPullback) | (exact GlobalTheory.KS.PowPB.powMap_isPullback) | (intros; apply GlobalTheory.KS.PowPB.powMap_isPullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Lev Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 LevDat P0 IsGenericPsi)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (SSParam GoodAt typeChar centralIdem chiTame IsGeneratorFamily)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodIdempotentBadPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

variable {D : D7}

abbrev typePl (pb : Fin 2 → 𝓞 D.host.E) : Finset (Pl D.host.E) := primesOf (pb 0 * pb 1)

instance finite_kP (w : Pl D.host.E) : Finite (kP w) :=
  Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot


variable (D) in
def badPl : Finset (HeightOneSpectrum (𝓞 D.host.F)) := primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)

abbrev Model (D : D7) (j : ℕ) : Type 1 := DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))

section Spaces

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
  (ψ : ∀ w : Pl D.host.E, AddChar (kP w) ℂ)
  (j : ℕ) (β : GL (Fin (D.sp.W j).rank) (EAf D)) (M : Model D j)

end Spaces

end GlobalTheory.IndefiniteRowSideFullHecke.GoodIdempotentBadPlaces
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 IsGenericPsi mem_primesOf)
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.SumWCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def cj (E : Type) [Field E] [StarRing E] : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

theorem cj_coe (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl

theorem cj_cj (x : 𝓞 E) : cj E (cj E x) = x := RingOfIntegers.ext (star_star (x : E))

theorem cj_algMap (hc : CMData F E) (x : 𝓞 F) : cj E (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
  RingOfIntegers.ext ((hc.fixed _).2 ⟨x, rfl⟩)

theorem exists_norm (hc : CMData F E) (y : 𝓞 E) : ∃ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) x = y * cj E y := by
  obtain ⟨a, ha⟩ := (hc.fixed ((y * cj E y : 𝓞 E) : E)).1 (by
    rw [← cj_coe, map_mul, cj_cj, mul_comm])
  have hi : IsIntegral ℤ a := by
    have h1 : IsIntegral ℤ (algebraMap F E a) := by rw [ha]; exact (y * cj E y).isIntegral_coe
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 h1
  exact ⟨⟨a, hi⟩, RingOfIntegers.ext ha⟩

end Places

variable {D : D7}

theorem goodAt_comp {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {r : ℕ} {ι κ J : Type} (χ : J → ((ZMod p)ˣ →* Kˣ))
    (e : ι → κ) (he : Function.Surjective e) (s : κ → LevelCuspCharacters.SSParam p K r) :
    LevelCuspCharacters.GoodAt χ (fun v => s (e v)) ↔ LevelCuspCharacters.GoodAt χ s := by
  simp only [LevelCuspCharacters.GoodAt, he.forall, he.exists]

theorem coeff_centralIdem {G : Type} [Group G] [Finite G] (τ : G → ℂ) (x : G) :
    (LevelCuspCharacters.centralIdem τ).coeff x = τ 1 / (Nat.card G : ℂ) * τ x⁻¹ := by
  classical
  unfold LevelCuspCharacters.centralIdem
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

section Match

variable {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) (pl : LevelCuspCharacters.Sq D.host ≃ ↥(GoodIdempotentBadPlaces.typePl pb))
  (red : ∀ v : LevelCuspCharacters.Sq D.host, kP (pl v).1 ≃+* ZMod (D.host.g v.1))



end Match

end GlobalTheory.SumWCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

def vec {S : Type} [CommRing S] (x : Sp S ⟶ X) {n : ℕ}
    (xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G)
    (cc : Fin n → S) : Sp (DualNumber S) ⟶ t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst t.G.hom x

section V

variable {t} {S : Type} [CommRing S] {x : Sp S ⟶ X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G}

theorem push_ext {Y : Over (Spec (CommRingCat.of S))} {v v' : Y ⟶ (Over.pullback x).obj t.G}
    (h : v.left ≫ pullback.fst t.G.hom x = v'.left ≫ pullback.fst t.G.hom x) : v = v' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact (Over.w v).trans (Over.w v').symm

theorem tan_iff (v : sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x).obj t.G) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v.left ≫ pullback.fst t.G.hom x = (1 : Over.mk x ⟶ t.G).left ↔
      ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := by
  have hid : (sp (R₀ := S) S).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap S S)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e0 : (1 : sp (R₀ := S) S ⟶ (Over.pullback x).obj t.G).left ≫ pullback.fst t.G.hom x =
      (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left :=
    congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) S)))
  have e1 : (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left = (1 : Over.mk x ⟶ t.G).left := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']
    show ((sp (R₀ := S) S).hom ≫ x) ≫ _ = x ≫ _
    rw [hid, Category.id_comp]
  rw [← e1, ← e0, ← Category.assoc]
  constructor
  · intro e
    exact push_ext e
  · intro e
    exact congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e

theorem vec_tan (hx : IsUnivChart _ n xc) (cc : Fin n → S) : IsTanAtG t x (vec t x xc cc) := by
  refine ⟨?_, (tan_iff _).mpr (ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc)⟩
  show ((tvec (x := xc) cc).left ≫ pullback.fst _ _) ≫ _ = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) (Over.w (tvec (x := xc) cc))

theorem vec_exists (hx : IsUnivChart _ n xc) (w : Sp (DualNumber S) ⟶ t.G.left) (hw : IsTanAtG t x w) :
    ∃ cc, w = vec t x xc cc := by
  let v : sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x).obj t.G :=
    Over.homMk (pullback.lift w _ hw.1) (pullback.lift_snd _ _ _)
  have hv : v.left ≫ pullback.fst t.G.hom x = w := pullback.lift_fst _ _ _
  have ht : ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := (tan_iff v).mp (by rw [hv]; exact hw.2)
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht, ?_⟩
  have e : v = tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht) := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx v ht
  rw [← hv]
  exact congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e

theorem tvec_sum (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → S) (e : Fin m → Fin n → S) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  induction m with
  | zero =>
    have h := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → S) 0
    rw [add_zero] at h
    simpa using mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  | succ m ih =>
    rw [Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx,
      ih (fun j => a j.succ) (fun j => e j.succ), List.ofFn_succ, List.prod_cons]

theorem comb_iff (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → S) (a : Fin m → S) (cc : Fin n → S) :
    IsCombAtG t x (fun j => vec t x xc (e j)) a (vec t x xc cc) ↔ cc = ∑ j, a j • e j := by
  let P := pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) (DualNumber S))
  let W' : Fin m → (tEpsG x ⟶ t.G) := fun j =>
    P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))
  have hW' : ∀ j, (W' j).left = spMap (epsMul (a j)) ≫ vec t x xc (e j) := fun j =>
    Category.assoc _ _ _
  have hP : ((List.ofFn W').prod).left = vec t x xc (∑ j, a j • e j) := by
    have h := map_list_prod P
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))
    rw [← tvec_sum hx a e, List.map_ofFn] at h
    exact (congrArg (fun q => q.left) h).symm
  constructor
  · rintro ⟨u, hu, hprod⟩
    have eu' : u = W' := funext fun j => Over.OverMorphism.ext ((hu j).trans (hW' j).symm)
    rw [eu', hP] at hprod
    exact (ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (push_ext hprod)).symm
  · intro h
    subst h
    exact ⟨W', hW', hP⟩

theorem vec_bc [IsLocalRing S] {S' : Type} [CommRing S'] [Algebra S S'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := S') (ReciprocityTheory.ChartRestriction.G.Chart.JetR S' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap S S') ≫ x)).obj t.G), IsUnivChart _ n xc' ∧
      ∀ cc : Fin n → S, vec t (spMap (algebraMap S S') ≫ x) xc' (algebraMap S S' ∘ cc) =
        spMap (dualMap (algebraMap S S')) ≫ vec t x xc cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := S) (R' := S') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB S S'))
    (isGrpPullback_pullback t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB S S' ≫ x))
  refine ⟨fun m => x₁ m ≫ e.hom, gfp_chart_iso e hx₁, fun cc => ?_⟩
  have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left =
      (tvec (x := x₁) (algebraMap S S' ∘ cc)).left ≫ e.hom.left := by
    show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
    rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
  show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left ≫ pullback.fst _ _ = _
  rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
  rfl

end V

theorem exists_lie_basis_stable (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X) :
    ∃ (n : ℕ) (D : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ e, IsTanAtG t x (D e)) ∧
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (w : Sp (DualNumber S') ⟶ t.G.left),
        IsTanAtG t (spMap φ ≫ x) w →
          ∃! a : Fin n → S', IsCombAtG t (spMap φ ≫ x) (fun e => spMap (dualMap φ) ≫ D e) a w := by
  have : Smooth ((Over.pullback x).obj t.G).hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom x)
    infer_instance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj t.G)
  refine ⟨n, fun e => vec t x xc (Pi.single e 1), fun e => vec_tan hx _, fun S' _ φ w hw => ?_⟩
  letI : Algebra S S' := φ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := S') hx
  obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
  have hD : (fun e => spMap (dualMap φ) ≫ vec t x xc (Pi.single e 1)) =
      fun e => vec t (spMap (algebraMap S S') ≫ x) xc' (Pi.single e 1) := by
    funext e
    have h1 : (Pi.single e 1 : Fin n → S') = algebraMap S S' ∘ (Pi.single e 1 : Fin n → S) := by
      funext j
      by_cases h : j = e
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    exact (hv _).symm.trans (by rw [← h1])
  have hs : ∀ a : Fin n → S', ∑ j, a j • (Pi.single j 1 : Fin n → S') = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hD]
  refine ⟨cc, (comb_iff hx' _ _ _).2 (hs cc).symm, fun a ha => ?_⟩
  exact (hs a).symm.trans ((comb_iff hx' _ _ _).1 ha).symm

end GlobalTheory.LieLocBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace SplitOffPlaces
open Formalism.L2.Col Formalism.HermitianLatticesTheory

noncomputable def conjSpec {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 E) where
  asIdeal := P.asIdeal.comap (cO E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : cO E x ∈ P.asIdeal.comap (cO E) := by
      rw [Ideal.mem_comap, cO_cO]; exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← cO_cO x, h1, map_zero]

theorem exists_mem_not_mem {A : Type} [CommRing A] [IsDedekindDomain A] {Q P P' : HeightOneSpectrum A}
    (h : Q ≠ P) (h' : Q ≠ P') : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal ∧ x ∉ P'.asIdeal := by
  by_contra hc
  have hs : (Q.asIdeal : Set A) ⊆ (P.asIdeal : Set A) ∪ (P'.asIdeal : Set A) := by
    intro x hx
    by_contra hx'
    exact hc ⟨x, hx, fun h1 => hx' (Or.inl h1), fun h1 => hx' (Or.inr h1)⟩
  rcases Ideal.subset_union.1 hs with h1 | h1
  · exact h (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1))
  · exact h' (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P'.isPrime.ne_top h1))

theorem star_sqrt (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  haveI := D.host.isCMField_hostE
  have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
  rw [h2, map_neg, h1]
  simp

theorem sqrt_sq (D : D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem exists_coord (D : D7) (x : D.host.E) (hx : x ∈ D.host.K) :
    ∃ u v : ℚ, x = (u : D.host.E) + (v : D.host.E) * D.host.sqrtMinusD := by
  have halg : IsAlgebraic ℚ D.host.sqrtMinusD := Algebra.IsAlgebraic.isAlgebraic _
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqrtMinusD} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by rw [Set.mem_singleton_iff.1 hy]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    refine ⟨u * u' - D.host.d * v * v', u * v' + v * u', ?_⟩
    push_cast
    linear_combination (v * v' : D.host.E) * sqrt_sq D

theorem exists_norm (D : D7) (x : 𝓞 D.host.K) :
    ∃ (x' : 𝓞 D.host.K) (n : ℤ), algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x' = cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) ∧
      x * x' = (n : 𝓞 D.host.K) := by
  obtain ⟨u, v, huv⟩ := exists_coord D ((x : D.host.K) : D.host.E) (x : D.host.K).2
  have hb : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hst : star ((x : D.host.K) : D.host.E) = (u : D.host.E) - (v : D.host.E) * D.host.sqrtMinusD := by
    rw [huv, star_add, star_mul, star_sqrt, star_ratCast, star_ratCast]; ring
  have hmem : star ((x : D.host.K) : D.host.E) ∈ D.host.K := by
    rw [hst]
    exact sub_mem (SubfieldClass.ratCast_mem _ u) (mul_mem (SubfieldClass.ratCast_mem _ v) hb)
  have hinj : Function.Injective (algebraMap D.host.K D.host.E) := (algebraMap D.host.K D.host.E).injective
  have hint : IsIntegral ℤ (⟨_, hmem⟩ : D.host.K) := by
    rw [← isIntegral_algebraMap_iff (B := D.host.E)]
    exact (cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x)).isIntegral_coe
  let x' : 𝓞 D.host.K := ⟨⟨_, hmem⟩, hint⟩
  have hq : ((x * x' : 𝓞 D.host.K) : D.host.K) = algebraMap ℚ D.host.K (u ^ 2 + D.host.d * v ^ 2) := by
    apply hinj
    have e1 : algebraMap D.host.K D.host.E ((x * x' : 𝓞 D.host.K) : D.host.K) =
      ((x : D.host.K) : D.host.E) * star ((x : D.host.K) : D.host.E) := rfl
    rw [e1, hst, ← IsScalarTower.algebraMap_apply, huv, eq_ratCast]
    push_cast
    linear_combination (-(v : D.host.E) ^ 2) * sqrt_sq D
  have hi : IsIntegral ℤ (u ^ 2 + D.host.d * v ^ 2 : ℚ) := by
    rw [← isIntegral_algebraMap_iff (B := D.host.K), ← hq]
    exact (x * x').isIntegral_coe
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  refine ⟨x', n, RingOfIntegers.ext rfl, RingOfIntegers.ext ?_⟩
  rw [hq, ← hn]
  simp

end SplitOffPlaces


open SplitOffPlaces Formalism.L2.Col Formalism.HermitianLatticesTheory in
theorem splitOff_places : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → (∀ v ∈ S, ∃ PP ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) → Formalism.IndefR.Bridge.SplitOff P (Pg : Set (HeightOneSpectrum (𝓞 D.host.E))) → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ (∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) ∧ OffS D S P := by
  intro D Pb Pg S P hPg hS hP
  obtain ⟨-, hP1, hP2⟩ := hP
  have hne : ∀ PP ∈ Pg, PP ≠ P := fun PP h e => hP1 (e ▸ h)
  have hne' : ∀ PP ∈ Pg, PP ≠ conjSpec P := fun PP h e => hP2 PP h (by rw [e, conjIdeal_eq]; rfl)
  have hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro k hk
    have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hne P ((hPg P).2 ⟨k, e.symm⟩) rfl
    have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e =>
      hne' (conjSpec P) ((hPg _).2 ⟨k, e.symm⟩) rfl
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
    obtain ⟨x', n, hx', hn⟩ := exists_norm D x
    have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
        rw [← hx', ← map_mul, hn, map_intCast]
      rw [e] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
    have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
    by_cases hd : (D.host.g k : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hd
      apply hnP
      push_cast
      exact Ideal.mul_mem_right _ _ hk
    · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
      apply (Pb.pb k).isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)
  refine ⟨?_, fun PP h => ⟨hne PP h, fun hc => hne' PP h ?_⟩, ?_⟩
  · intro h
    rw [Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hg 0 h
    · exact hg 1 h
  · refine HeightOneSpectrum.ext (PP.isMaximal.eq_of_le (conjSpec P).isPrime.ne_top fun c hc' => ?_)
    obtain ⟨c', h1, h2⟩ := hc c hc'
    have e : cO D.host.E c = c' := RingOfIntegers.ext h2.symm
    change cO D.host.E c ∈ P.asIdeal
    rwa [e]
  · intro v hv
    obtain ⟨PP, hPP, rfl⟩ := hS v hv
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem (hne PP hPP) (hne' PP hPP)
    have hfix : star ((x * cO D.host.E x : 𝓞 D.host.E) : D.host.E) = ((x * cO D.host.E x : 𝓞 D.host.E) : D.host.E) := by
      change star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul, star_star]
    obtain ⟨a, ha⟩ := (D.sp.cm.fixed _).1 hfix
    have hint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (B := D.host.E), ha]
      exact (x * cO D.host.E x).isIntegral_coe
    have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ = x * cO D.host.E x := RingOfIntegers.ext ha
    refine ⟨⟨a, hint⟩, ?_, fun y hy hyP => ?_⟩
    · change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP.asIdeal
      rw [e]
      exact Ideal.mul_mem_right _ _ hx
    · have e' : y = x * cO D.host.E x := RingOfIntegers.ext (hy.trans ha)
      rw [e'] at hyP
      rcases P.isPrime.mem_or_mem hyP with h | h
      · exact hx1 h
      · exact hx2 h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometry
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem unifAt_transport : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), 0 < N → UnifAt F σ ρ N D' t P y e → IsMarkedIsom N D' D'' t t' w → (∀ x, P' (w x) = h (P x)) → IsPeriod D'' ρ P' → UnifAt F σ ρ N D'' t' P' y (fun z => e (h.symm z)) := by
  intro O _ bar g ρ R _ σ Λ F N D' D'' t t' P P' y e w h hN hU hW hPP' hP'
  obtain ⟨hy, hP, hexp, hker, hact, hweil, heta⟩ := hU
  obtain ⟨hiso, hmark⟩ := hW
  have hQs : ∀ x, h.symm (P' x) = P (w.symm x) := by
    intro x
    rw [h.symm_apply_eq, ← hPP', w.apply_symm_apply]

  have hcomm : ∀ a z, h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
    intro a z
    have hL : ((h.toLinearMap ∘ₗ Matrix.mulVecLin (ρ a)).restrictScalars ℝ) =
        ((Matrix.mulVecLin (ρ a) ∘ₗ h.toLinearMap).restrictScalars ℝ) := by
      apply LinearMap.ext_on hP.2.2.2.1
      rintro _ ⟨x, rfl⟩
      simp only [LinearMap.restrictScalars_apply, LinearMap.coe_comp, Function.comp_apply,
        Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
      rw [← hP.1, ← hPP', ← hPP', map_smul, hP'.1]
    exact congrArg (fun f => f z) hL
  have hcomm' : ∀ a z, h.symm (ρ a *ᵥ z) = ρ a *ᵥ h.symm z := by
    intro a z
    rw [h.symm_apply_eq, hcomm, h.apply_symm_apply]
  set hc := h.symm.toContinuousLinearEquiv with hhc
  have hcc : ∀ z, hc z = h.symm z := fun z => rfl
  have hder : ∀ u v, IsDerivAt0 (fun z => (e (h.symm z)).left) u v ↔ IsDerivAt0 (fun z => (e z).left) (h.symm u) v := by
    intro u v
    unfold IsDerivAt0
    simp only [map_zero]
    refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_)
    have key := hc.comp_right_fderiv (f := fun z => valAt' (e z).left U f) (x := 0)
    have e1 : ((fun z => valAt' (e z).left U f) ∘ hc) = (fun z => valAt' (e (h.symm z)).left U f) := rfl
    rw [e1, map_zero] at key
    rw [key]
    rfl
  refine ⟨hy, hP', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro z z'
    simp only [map_add (f := _)]
    exact hexp.1 _ _
  · exact hexp.2.1.comp h.symm.surjective
  · intro U f
    obtain ⟨ho, hd⟩ := hexp.2.2.1 U f
    have hs : {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (e (h.symm b)).left ⁻¹ᵁ U} =
        hc ⁻¹' {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (e b).left ⁻¹ᵁ U} := by
      ext b; simp [hcc]
    rw [hs]
    exact ⟨ho.preimage hc.continuous, hd.comp hc.differentiableOn (Set.mapsTo_preimage _ _)⟩
  · intro u
    obtain ⟨v, hv, huniq⟩ := hexp.2.2.2.1 (h.symm u)
    exact ⟨v, (hder u v.left).2 hv, fun v' hv' => huniq v' ((hder u v'.left).1 hv')⟩
  · intro v hv
    dsimp only at hv
    rw [map_zero] at hv
    obtain ⟨u, hu, huniq⟩ := hexp.2.2.2.2 v hv
    refine ⟨h u, (hder (h u) v.left).2 (by rwa [h.symm_apply_apply]), fun u' hu' => ?_⟩
    rw [← huniq (h.symm u') ((hder u' v.left).1 hu'), h.apply_symm_apply]
  · intro z
    rw [hker]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨w x, by rw [hPP', hx, h.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨w.symm x, (hQs x).symm⟩
  · intro a z
    dsimp only
    rw [hcomm', hact]
  · intro k a b c hk hc'
    have h1 := hweil k (w.symm a) (w.symm b) c hk (by
      rw [hc', ← hiso (w.symm a) (w.symm b), w.apply_symm_apply, w.apply_symm_apply])
    simpa only [map_smul, hQs] using h1
  · intro a
    obtain ⟨x, hx⟩ := hmark a
    rw [heta a]
    have h1 : t' a = w (t a - N • w.symm x) := by
      rw [map_sub, map_nsmul, w.apply_symm_apply, hx, add_sub_cancel_right]
    have hN' : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have h2 : h.symm ((N : ℂ)⁻¹ • P' (t' a)) = (N : ℂ)⁻¹ • P (t a) + P (-(w.symm x)) := by
      rw [h1, hPP', map_smul, h.symm_apply_apply, map_sub, map_nsmul, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hN', one_smul, map_neg, sub_eq_add_neg]
    dsimp only
    rw [h2, hexp.1, (hker _).2 ⟨_, rfl⟩, _root_.mul_one]

end GlobalTheory.PELU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationAt_transport_isometry : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), 0 < N → UnifAt F σ ρ N D' t P y e → IsMarkedIsom N D' D'' t t' w → (∀ x, P' (w x) = h (P x)) → IsPeriod D'' ρ P' → UnifAt F σ ρ N D'' t' P' y (fun z => e (h.symm z)) := by
  first | exact @GlobalTheory.PELU.unifAt_transport | exact GlobalTheory.PELU.unifAt_transport | (intros; apply GlobalTheory.PELU.unifAt_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.WeilComplexUnique

theorem weilIs_unitOn_unique_complex : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (y : Sp ℂ ⟶ X) (k : ℤ) (x x' : Over.mk y ⟶ G) (c c' : ℂˣ), Out.WeilIs G L k x x' (unitOn c) → Out.WeilIs G L k x x' (unitOn c') → c = c' := by
  intro X G _ _ g _ _ L hL y k x x' c c' h h'
  exact GlobalTheory.weilIs_unique_fieldPoint X G L hL ℂ y k x x' c c' h h'

end GlobalTheory.WeilComplexUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_complex_value_unique : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (y : Sp ℂ ⟶ X) (k : ℤ) (x x' : Over.mk y ⟶ G) (c c' : ℂˣ), Out.WeilIs G L k x x' (unitOn c) → Out.WeilIs G L k x x' (unitOn c') → c = c' := by
  first | exact @GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex | exact GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex | (intros; apply GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemes
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActPull

theorem exists_act_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∃ act' : O → (G' ⟶ G'), ((∀ a, IsMonHom (act' a)) ∧ act' 1 = 𝟙 G' ∧ (∀ a b, act' (a * b) = act' a ≫ act' b) ∧ (∀ a b, act' (a + b) = act' a * act' b)) ∧ ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := by
  intro S S' f G _ G' _ φ hg O _ act hhom hone hmul hadd
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act' : O → (G' ⟶ G') := fun a => Over.homMk (hg.1.lift (φ ≫ (act a).left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G') a, pushPt hg.1.w (x ≫ act' a) = pushPt hg.1.w x ≫ act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨act', ⟨fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩, ha⟩
  · have := hhom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act' 1), pa, hone, Category.comp_id]
  · rw [← Category.id_comp (act' (a * b)), pa, pa, hmul, ← Category.id_comp (act' a), pa, Category.assoc]
  · refine Eq.trans ?_ (pm (act' a) (act' b)).symm
    rw [← Category.id_comp (act' (a + b)), ← Category.id_comp (act' a), ← Category.id_comp (act' b), pa, pa, pa, hadd]
    exact MonObj.comp_mul _ _ _

end GlobalTheory.ActPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemesStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∃ act' : O → (G' ⟶ G'), ((∀ a, IsMonHom (act' a)) ∧ act' 1 = 𝟙 G' ∧ (∀ a b, act' (a * b) = act' a ≫ act' b) ∧ (∀ a b, act' (a + b) = act' a * act' b)) ∧ ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := by
  first | exact @GlobalTheory.ActPull.exists_act_pull | exact GlobalTheory.ActPull.exists_act_pull | (intros; apply GlobalTheory.ActPull.exists_act_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactLatticeUnitCovolume
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactLatticeUnitCovolume
open MeasureTheory

namespace GlobalTheory.HaarFundDom

open scoped Pointwise

theorem exists_haar_fundDom_mass_one : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (K : Set G), IsCompact K →
    (∀ g : G, ∃ γ : Γ, γ • g ∈ K) →
    ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro G _ _ _ _ _ _ _ _ Γ _ _ K hK hcov
  let μ₀ : Measure G := Measure.haar
  obtain ⟨𝓕, h𝓕m, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have hD : IsFundamentalDomain Γ 𝓕 μ₀ := IsFundamentalDomain.mk' h𝓕m.nullMeasurableSet h𝓕
  haveI : MeasurableMul G :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul Γ G :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : G => (γ : G) * x).measurable⟩
  haveI : SMulInvariantMeasure Γ G μ₀ := ⟨fun γ A _ => measure_preimage_mul μ₀ (γ : G) A⟩
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • K ∩ 𝓕 := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨γ⁻¹, Set.mem_smul_set.2 ⟨γ • x, hγ, ?_⟩, hx⟩
    simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hfin : μ₀ 𝓕 < ⊤ :=
    calc μ₀ 𝓕 ≤ μ₀ (⋃ γ : Γ, γ • K ∩ 𝓕) := measure_mono hsub
      _ ≤ ∑' γ : Γ, μ₀ (γ • K ∩ 𝓕) := measure_iUnion_le _
      _ = μ₀ K := (hD.measure_eq_tsum _).symm
      _ < ⊤ := hK.measure_lt_top
  have hne : μ₀ 𝓕 ≠ 0 := by
    intro h0
    have h1 := hD.measure_eq_tsum' Set.univ
    simp only [Set.univ_inter, measure_smul, h0, tsum_zero] at h1
    exact (Measure.measure_univ_pos.2 (NeZero.ne μ₀)).ne' h1
  refine ⟨(μ₀ 𝓕)⁻¹ • μ₀, 𝓕, ?_, hD.mono Measure.smul_absolutelyContinuous, ?_⟩
  · exact Measure.IsHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hne)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne hfin.ne]

end GlobalTheory.HaarFundDom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactLatticeUnitCovolumeStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_lattice_unit_covolume : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ : Γ, γ • g ∈ K) → ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one | exact GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one | (intros; apply GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlong
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

def LiftsAlong {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {U : Over (Sp R)} (M : LB (A ⊗ U).left)
    (B : Type) [CommRing B] (I : Ideal B) : Prop :=
  ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left)
    (u₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ U),
    Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) (by simp) :
      Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ T) u₀ →
    ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u

end GlobalTheory.DualCon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterConjugate
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.LevelCharacterConjugate

theorem levPOf_inv {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ}
    (eG : G ≃* G0 Pg r) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) :
    levPOf eG σ P ψ⁻¹ = (levPOf eG σ P ψ).conj := by
  have hc : (Units.map (σ : K →* ℂ)).comp (ψ⁻¹.comp (eG.symm.toMonoidHom.subgroupComap P)) =
      ((Units.map (σ : K →* ℂ)).comp (ψ.comp (eG.symm.toMonoidHom.subgroupComap P)))⁻¹ :=
    MonoidHom.ext fun x => by simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv]
  exact congrArg (LevelP.mk (Subgroup.comap eG.symm.toMonoidHom P)) hc

theorem liftLevel_fixedEmbedding_eq_conj_rowLevel {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool)
    (h : A.v0 = InfinitePlace.mk D.what₂.embLL) : R.levL F b (sg0 D A) = (R.levR F b).conj := by
  rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ h]
  exact levPOf_inv _ _ _ _

end GlobalTheory.Proof.LevelCharacterConjugate
end
