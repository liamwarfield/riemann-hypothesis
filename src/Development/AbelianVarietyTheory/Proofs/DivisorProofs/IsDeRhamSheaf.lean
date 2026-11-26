module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham

namespace GlobalTheory.DeRhamSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

abbrev onAff {V : T.Opens} (hV : IsAffineOpen V) : Over (Sp Γ(T, V)) :=
  (Over.pullback hV.fromSpec).obj A

instance {V : T.Opens} (hV : IsAffineOpen V) : GrpObj (onAff A hV) := Functor.grpObjObj

end GlobalTheory.DeRhamSheaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

def Cond {X X' Z : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) : Prop :=
  ∀ W : X.Opens, IsAffineOpen W → Function.Injective (p.app W) ∧
    ∀ x : Γ(X, W), i.app W x = 0 → ∀ r : Γ(X', p ⁻¹ᵁ W), ∃ y : Γ(X, W), i.app W y = 0 ∧ p.app W y = p.app W x * r

def UnitsPatch {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) : Prop :=
  ∀ W : X.Opens, Function.Injective (pullU p W) ∧
    ∀ (u' : Γ(X', p ⁻¹ᵁ W)ˣ) (v : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) u' = gm p' z (i ⁻¹ᵁ W) v) → ∃ u : Γ(X, W)ˣ, pullU p W u = u'

def LocGen {Y : Scheme.{0}} (L : LB Y) (V : Y.Opens) (a : ∀ k, Γ(Y, V ⊓ L.U k)ˣ) : Prop :=
  ∀ (y : Y) (k k' : L.ι), y ∈ V → y ∈ L.U k → y ∈ L.U k' →
    gm (𝟙 Y) y (V ⊓ L.U k) (a k) = gm (𝟙 Y) y (L.U k ⊓ L.U k') (L.g k k') * gm (𝟙 Y) y (V ⊓ L.U k') (a k')

def Matches {X' Z Z' : Scheme.{0}} (i' : Z' ⟶ X') (p' : Z' ⟶ Z) {L' : LB X'} {N : LB Z}
    (w : LB.Iso (L'.pull i') (N.pull p')) {V' : X'.Opens} {V : Z.Opens} (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ)
    (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ) : Prop :=
  ∀ (z : Z') (k : L'.ι) (l : N.ι), i' z ∈ V' → p' z ∈ V → i' z ∈ L'.U k → p' z ∈ N.U l →
    gm p' z (V ⊓ N.U l) (b l) =
      gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) *
        gm i' z (V' ⊓ L'.U k) (a k)

def Pinched (g : ℕ) {S S' Z B' C Y : Scheme.{0}} (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z)
    (i : Y ⟶ B') (q : Y ⟶ C) (x : B') : Prop :=
  ∃ (U U' V : Scheme.{0}) (u : U ⟶ S) (p : U' ⟶ U) (j : U' ⟶ B') (n : V ⟶ U) (k : V ⟶ C),
    SmoothOfRelativeDimension g u ∧ IsPullback p (j ≫ b') u s' ∧ IsOpenImmersion j ∧ x ∈ Set.range j ∧
    IsPullback n (k ≫ e) u z ∧
    ∀ (T : Scheme.{0}) (a : T ⟶ U') (a' : T ⟶ V), a ≫ p = a' ≫ n → ∃ y : T ⟶ Y, y ≫ i = a ≫ j ∧ y ≫ q = a' ≫ k

end GlobalTheory.Pinch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem sharpOver_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left),
    SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  intro g n o _ ζ F W T T' P P' u f φ hS hφ hL
  obtain ⟨c, hc, pr, hpr, huniv, hbun⟩ := hS
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
  refine ⟨c', hc'u, pr', hmon, huniv', ?_⟩
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

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharp_polarization_pullback_stable : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  first | exact @GlobalTheory.Poinc.sharpOver_pullback | exact GlobalTheory.Poinc.sharpOver_pullback | (intros; apply GlobalTheory.Poinc.sharpOver_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

def IsQuasiInv {Y : Scheme.{0}} {A B : Over Y} [GrpObj A] [GrpObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) : Prop :=
  IsMonHom ψ ∧ IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 A) ^ k ∧ ψ' ≫ ψ = (𝟙 B) ^ k

def IsAxesTriv {Y : Scheme.{0}} (B : Over Y) [GrpObj B] [IsCommMonObj B] (Q : LB (G2 B).left) : Prop :=
  Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) ∧
    ∃ t : (Q.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {Y : Scheme.{0}}
  {s : Y ⟶ Sp R}

theorem isAxesTriv_obj (o : Obj b N s) : IsAxesTriv o.A o.P := ⟨o.isLB, o.rig₁, o.rig₂⟩

def KerStableAt (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ : o.A ⟶ B) {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ g : T ⟶ o.A, g ≫ ψ = 1 →
    ∀ a : D.O, g ≫ o.act.act a ≫ ψ = 1

def PullPolTriv (o : Obj b N s) {B : Over Y} (ψ' : B ⟶ o.A) {T : Over Y} (x : T ⟶ B) : Prop :=
  ∃ τ : (o.P.pull (lift (fst B T ≫ ψ') (snd B T ≫ x ≫ ψ')).left).Gen, τ.IsGen

def PolKerAt (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ' : B ⟶ o.A) (c : ℕ) {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ x : T ⟶ B, x ^ (c ^ 3) = 1 →
    (PullPolTriv o ψ' x ↔ x ^ c = 1)

def TjAt (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ : o.A ⟶ B)
    {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ Y), (∃ σ : Sp k ⟶ Tb, σ ≫ t = x) →
    (∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)

theorem tjAt_id_iff (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) :
    TjAt r w j o ψ (𝟙 Y) ↔ IsTj r w j o o' ψ :=
  ⟨fun h k _ _ _ x => h k x ⟨x, Category.comp_id x⟩, fun h k _ _ _ x _ => h k x⟩

theorem IsPIsog.kerStableAt {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog c o o' ψ)
    {Tb : Scheme.{0}} (t : Tb ⟶ Y) : KerStableAt o ψ t := by
  intro T _ _ g hg a
  haveI := o'.act.hom a
  rw [h.2.2.1, ← Category.assoc, hg, one_comp]

theorem IsPIsog.exists_quasiInv {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog c o o' ψ) :
    ∃ ψ' : o'.A ⟶ o.A, IsQuasiInv c ψ ψ' := by
  obtain ⟨-, h1, -, -, -, ψ', h2, h3, h4⟩ := h
  exact ⟨ψ', h1, h2, h3, h4⟩

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime]

structure SimSys (D : Datum p) (N K : ℕ) where
  g : ℕ → D.La →+ D.La
  u : ℕ → ℕ
  lin : ∀ n, 0 < n → n.Coprime p → ∀ (c : D.O) x, ∃ z, g n (c • x) = c • g n x + n • z
  u_cop : ∀ n, 0 < n → n.Coprime p → (u n).Coprime n
  u_tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → u (n * m) ≡ u n [MOD n]
  surj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z
  inj : ∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w
  sim : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y, (n : ℤ) ∣ D.EF (g n x) (g n y) - u n * D.EF x y
  tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z
  one : ∀ x, ∃ z, g K x = x + N • z

variable {D : Datum p} {N K : ℕ}

section Tate

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem TateIsoO.ev_nsmul_self (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) (z : D.La) :
    I.ev n (n • z) = 1 :=
  (I.ker n hn hc _).2 ⟨z, rfl⟩

theorem TateIsoO.ev_add_nsmul (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) (x z : D.La) :
    I.ev n (x + n • z) = I.ev n x := by
  rw [I.add, I.ev_nsmul_self hn hc, _root_.mul_one]

end Tate

variable {R : Type} [CommRing R]


variable (D K) in
def multSub : AddSubgroup D.La where
  carrier := {x | ∃ z, x = K • z}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨c, rfl⟩
    exact ⟨a + c, (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, (smul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, (smul_neg _ _).symm⟩


variable (D K) in
abbrev LQ := D.La ⧸ multSub D K


end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LamRigid

theorem rigid_pw {X X' Y S₀ : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {a : LB.Gen (LB.LinComb L' φ' ε)} (ha : a.IsGen) {t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h0 : ∀ y : S₀, ∃ J J', Good L y J ∧ Good L' y J' ∧
      val t e y J = pw w φ' ε e y (fun k => J (e ≫ φ' k ≫ F)) (fun k => J' (e ≫ φ' k)) * val a e y J')
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (hJ : Good L z J)
    (hJ' : Good L' z J') :
    val t r z J = pw w φ' ε r z (fun k => J (r ≫ φ' k ≫ F)) (fun k => J' (r ≫ φ' k)) * val a r z J' := by
  obtain ⟨t₂, ht₂, hv₂⟩ : ∃ t₂ : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε), t₂.IsGen ∧ ∀ (Z : Scheme.{0})
      (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      val t₂ r z J = pw w φ' ε r z (fun k => J (r ≫ φ' k ≫ F)) (fun k => J' (r ≫ φ' k)) * val a r z J' := by
    obtain ⟨t₁, ht₁, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' a ha
    exact ⟨t₁, ht₁, fun Z r z J J' hJ hJ' => hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)⟩
  refine (gen_unique hL p e he hp ht ht₂ (fun y J hJ => ?_) Z r z J hJ).trans (hv₂ Z r z J J' hJ hJ')
  obtain ⟨J₀, J₀', hJ₀, hJ₀', e₀⟩ := h0 y
  rw [GlobalTheory.UU.val_change ht e hJ hJ₀, GlobalTheory.UU.val_change ht₂ e hJ hJ₀, e₀, hv₂ _ e y J₀ J₀' hJ₀ hJ₀']

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

def ind {L : LB G.left} {Z : Scheme.{0}} (J : (Z ⟶ G.left) → L.ι) :
    (Z ⟶ (G2 G).left) → ULift.{0} (Finset (Fin 2)) → L.ι :=
  fun q I => J (q ≫ (psum G (x2 G) I.down).left)

variable {G}

theorem good_ind {L : LB G.left} {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ G.left) → L.ι} (hJ : Good L z J) :
    Good (abelian₂ G L) z (ind G J) := fun q => hJ.mem _ q

theorem adj_ind {L : LB G.left} (hL : L.IsLB) {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ G.left) → L.ι} (hJ : Good L z J)
    (χ : Z ⟶ (G2 G).left) : GlobalTheory.LamBiext.adj (GlobalTheory.LamBiext.lamφ G) GlobalTheory.LamBiext.lamε z (ind G J) J χ = 1 :=
  trF_self hL _ _ χ z (hJ.mem _ χ)

theorem square_over_hom_ext {X : Scheme.{0}} {a b : X ⟶ (G2 G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := pullback.hom_ext h₁ h₂

theorem cartesian_lift_three_comp_projection {T₀ : Over S} (p q r : T₀ ⟶ G) (i : Fin 3) : lift p (lift q r) ≫ x3 G i = ![p, q, r] i := by
  fin_cases i <;> simp [x3]

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem lamVal_eq {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)) {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z)
    (J : (Z ⟶ B.left) → M.ι) (J' : (Z ⟶ B'.left) → M'.ι) :
    lamVal w p z J J' = gw w p z (ind B J (p ≫ β₂)) (ind B' J' p) := by
  have e : ind B J (p ≫ β₂) = fun I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left) :=
    funext fun I => congrArg J (Category.assoc _ _ _)
  rw [e]; rfl

theorem pw_eq {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)) {Y Z : Scheme.{0}} {K : Type} [Fintype K]
    (φ' : K → (Y ⟶ (G2 B').left)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ B.left) → M.ι) (J' : (Z ⟶ B'.left) → M'.ι) :
    pw w φ' ε r z (fun k => ind B J (r ≫ φ' k ≫ β₂)) (fun k => ind B' J' (r ≫ φ' k)) =
      ∏ k, lamVal w (r ≫ φ' k) z J J' ^ ε k := by
  unfold pw
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [lamVal_eq, Category.assoc]
open GlobalTheory.LamBiext

theorem lam_iso_laws : ∀ (S S' : Scheme.{0}) (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : RigLB B) (M' : RigLB B') (c : CubicalStr B M) (c' : CubicalStr B' M') (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M'.L) ((abelian₂ B M.L).pull β₂)) (hβ : IsGrpPullback B' B f β), IsAbelianScheme B' → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (x x' y : T ⟶ B') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift x y).left z J J' = lamVal w (lift y x).left z J J' ∧ ∀ (u u' v : Over.mk (T.hom ≫ f) ⟶ B), u.left = x.left ≫ β → u'.left = x'.left ≫ β → v.left = y.left ≫ β → lamVal w (lift (x * x') y).left z J J' * cubV c' z J' x x' y = @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J u u' v) * lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' := by
  intro S S' B B' _ _ _ _ M M' c c' f β β₂ w hβ hB hsq hw hn T x x' y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M.L).IsLB := DVR.linComb_isLB _ M.isLB _ _
  have hL' : (abelian₂ B' M'.L).IsLB := DVR.linComb_isLB _ M'.isLB _ _
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have pt_one : ∀ T₀ : Over S', toBase hw₀ (1 : T₀ ⟶ B') = 1 := fun T₀ =>
    mul_eq_left.1 ((pt_mul 1 1).symm.trans (congrArg (toBase hw₀) (mul_one 1)))
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h

  have symm : lamVal w (lift x y).left z J J' = lamVal w (lift y x).left z J J' := by
    let φ2 : Fin 2 → ((G2 B').left ⟶ (G2 B').left) :=
      ![(lift (fst B' B') (snd B' B')).left, (lift (snd B' B') (fst B' B')).left]
    let ε2 : Fin 2 → ℤ := ![1, -1]
    have fe2' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B') φ2) (flatε lamε ε2) := fun U _ h => by
      rw [prod_flat, Fin.prod_univ_two, Fintype.prod_empty]
      show 1 = (∏ i, h ((lift (fst B' B') (snd B' B')).left ≫ lamφ B' i) ^ lamε i) ^ (1 : ℤ) *
        (∏ i, h ((lift (snd B' B') (fst B' B')).left ≫ lamφ B' i) ^ lamε i) ^ (-1 : ℤ)
      rw [prod_lam, prod_lam, _root_.mul_comm (snd B' B')]
      apply Additive.ofMul.injective
      simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
    have fe2 : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ2 k ≫ β₂) (flatε lamε ε2) :=
      fun U _ h => by
        rw [prod_flat, Fin.prod_univ_two, Fintype.prod_empty]
        show 1 = (∏ i, h (((lift (fst B' B') (snd B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ) *
          (∏ i, h (((lift (snd B' B') (fst B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (-1 : ℤ)
        rw [Hlam, Hlam, _root_.mul_comm (toBase hw₀ (snd B' B'))]
        apply Additive.ofMul.injective
        simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
        abel
    obtain ⟨g', hg', hv'⟩ := exists_gen M'.isLB fe2' (LB.oneGen M'.L) (oneGen_isGen _)
    obtain ⟨g, hg, hv⟩ := exists_gen M.isLB fe2 (LB.oneGen M.L) (oneGen_isGen _)
    have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) J₀, Good M'.L z₀ J₀ →
        val (L := abelian₂ B' M'.L) (nest M'.L (lamφ B') lamε φ2 ε2 g') r z₀ (ind B' J₀) = 1 := fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind M'.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
    have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) J₀, Good M.L z₀ J₀ →
        val (L := abelian₂ B M.L) (nest M.L (lamφ B) lamε (fun k => φ2 k ≫ β₂) ε2 g) r z₀ (ind B J₀) = 1 :=
      fun r z₀ J₀ hJ₀ => by
        refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
        simp only [adj_ind M.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
        exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
    have Fp : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι)
        (J₀' : (T₀.left ⟶ B'.left) → M'.L.ι),
        pw w φ2 ε2 (lift a b).left z₀ (fun k => ind B J₀ ((lift a b).left ≫ φ2 k ≫ β₂))
          (fun k => ind B' J₀' ((lift a b).left ≫ φ2 k)) =
          lamVal w (lift a b).left z₀ J₀ J₀' * (lamVal w (lift b a).left z₀ J₀ J₀')⁻¹ := by
      intro T₀ a b z₀ J₀ J₀'
      rw [pw_eq, Fin.prod_univ_two]
      show lamVal w (lift a b ≫ lift (fst B' B') (snd B' B')).left z₀ J₀ J₀' ^ (1 : ℤ) *
        lamVal w (lift a b ≫ lift (snd B' B') (fst B' B')).left z₀ J₀ J₀' ^ (-1 : ℤ) = _
      rw [comp_lift, comp_lift, lift_fst, lift_snd, zpow_neg, zpow_one, zpow_one]
    have he2 : (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (snd B' B').left ≫ B'.hom = 𝟙 _ := by
      rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') 1)
    have E := rigid_pw w hw hL hL' φ2 ε2 (nest_isGen hg') (nest_isGen hg) _ _ he2
      (surj_comp (surj_snd hG hB _) (hG _ _ hB).2) (fun y₀ => by
        obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt M.isLB y₀
        obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt M'.isLB y₀
        refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
        rw [Ft _ y₀ J₁ hJ₁, Fp, Fa _ y₀ J₁' hJ₁', mul_inv_cancel, _root_.mul_one])
      T.left (lift x y).left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
    rw [Ft _ z J hJ, Fp, Fa _ z J' hJ', _root_.mul_one] at E
    exact mul_inv_eq_one.1 E.symm

  obtain ⟨l₁, l₂, hl₁, hl₂, cl₁, cl₂, vl⟩ := exists_laws M' c'
  let φ3 := law1φ B' (x3 B' 0) (x3 B' 1) (x3 B' 2)
  let β₃ : (G3 B').left ⟶ (G3 B).left :=
    (lift (toBase hw₀ (x3 B' 0)) (lift (toBase hw₀ (x3 B' 1)) (toBase hw₀ (x3 B' 2)))).left
  have fe3 : FormEq (fun I => β₃ ≫ thφ B (x3 B) I) thε (flatφ (lamφ B) (fun k => φ3 k ≫ β₂)) (flatε lamε lawε) :=
    fun U _ h => by
      have a := prod_cub (toBase hw₀ (x3 B' 0)) (toBase hw₀ (x3 B' 1)) (toBase hw₀ (x3 B' 2)) h
      have b := prod_law₁ (x3 B' 0) (x3 B' 1) (x3 B' 2) (fun χ => ∏ i, h ((χ ≫ β₂) ≫ lamφ B i) ^ lamε i)
      rw [id₃] at b
      simp only [Over.id_left, Category.id_comp, Hlam, pt_mul] at b
      rw [a, prod_flat, b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  obtain ⟨g₃, hg₃, hv₃⟩ := exists_gen M.isLB fe3 (LB.pullGen M.L (thφ B (x3 B)) thε c.t β₃)
    (DVR.pullGen_isGen _ _ _ _ c.isGen β₃)
  have ht₃ := nest_isGen (L := M.L) (φ := lamφ B) (δ := lamε) hg₃
  have Ft3 : ∀ {T₀ : Over S'} (a a' b : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι), Good M.L z₀ J₀ →
      val (L := abelian₂ B M.L) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) (lift a (lift a' b)).left z₀ (ind B J₀) =
        cubV (T := Over.mk (T₀.hom ≫ f)) c z₀ J₀ (toBase hw₀ a) (toBase hw₀ a') (toBase hw₀ b) := by
    intro T₀ a a' b z₀ J₀ hJ₀
    show val (L := LB.LinComb M.L (lamφ B) lamε) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) _ z₀ (ind B J₀) = _
    rw [val_nest hg₃ _ (good_ind hJ₀) hJ₀]
    simp only [adj_ind M.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    rw [hv₃ _ _ z₀ J₀ hJ₀]
    refine (val_pull hJ₀ _ _ _).trans ?_
    refine congrArg (fun q => val (L := M.L) (φ := thφ B (x3 B)) (ε := thε) c.t q z₀ J₀) ?_
    refine hom_ext_triple B fun i => ?_
    have e1 : β₃ ≫ (x3 B i).left = (x3 B' i).left ≫ β := by
      show (lift _ (lift _ _) ≫ x3 B i).left = _
      rw [cartesian_lift_three_comp_projection]; fin_cases i <;> rfl
    rw [Category.assoc, e1, ← Category.assoc, ← Over.comp_left, cartesian_lift_three_comp_projection, ← Over.comp_left, cartesian_lift_three_comp_projection]
    fin_cases i <;> rfl
  have Fa3 : ∀ {T₀ : Over S'} (a a' b : T₀ ⟶ B') (z₀ : T₀.left) (J₀' : (T₀.left ⟶ B'.left) → M'.L.ι),
      Good M'.L z₀ J₀' → val (L := abelian₂ B' M'.L) l₁ (lift a (lift a' b)).left z₀ (ind B' J₀') = cubV c' z₀ J₀' a a' b := by
    intro T₀ a a' b z₀ J₀' hJ₀'
    show val (L := lamLB M') l₁ _ z₀ (ind B' J₀') = _
    rw [(vl z₀ (ind B' J₀') (good_ind hJ₀') J₀' hJ₀').1 a a' b, adj_ind M'.isLB hJ₀', adj_ind M'.isLB hJ₀',
      adj_ind M'.isLB hJ₀']
    simp
  have Fp3 : ∀ {T₀ : Over S'} (a a' b : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι)
      (J₀' : (T₀.left ⟶ B'.left) → M'.L.ι),
      pw w φ3 lawε (lift a (lift a' b)).left z₀ (fun k => ind B J₀ ((lift a (lift a' b)).left ≫ φ3 k ≫ β₂))
        (fun k => ind B' J₀' ((lift a (lift a' b)).left ≫ φ3 k)) =
        lamVal w (lift (a * a') b).left z₀ J₀ J₀' * (lamVal w (lift a b).left z₀ J₀ J₀')⁻¹ *
          (lamVal w (lift a' b).left z₀ J₀ J₀')⁻¹ := by
    intro T₀ a a' b z₀ J₀ J₀'
    rw [pw_eq]; exact prod_law₁ a a' b (fun χ => lamVal w χ z₀ J₀ J₀')

  have sj3 : Function.Surjective ((snd B' (B' ⊗ B')).left ≫ (snd B' B').left ≫ B'.hom).appTop.hom :=
    surj_comp (surj_snd hG hB _) (surj_comp (surj_snd hG hB _) (hG _ _ hB).2)
  have he3 : (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1)).left ≫ (snd B' (B' ⊗ B')).left ≫ (snd B' B').left ≫ B'.hom =
      𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1))
  have R3 := rigid_pw w hw hL hL' φ3 lawε hl₁ ht₃ _ _ he3 sj3 (fun y₀ => by
    obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt M.isLB y₀
    obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt M'.isLB y₀
    refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
    rw [Ft3 (T₀ := 𝟙_ (Over S')) 1 1 1 y₀ J₁ hJ₁, Fp3, Fa3 1 1 1 y₀ J₁' hJ₁', pt_one, _root_.mul_one,
      (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ₁).face, (isCub_cubV c' hJ₁').face,
      hn (𝟙_ (Over S')) y₀ J₁ J₁' hJ₁ hJ₁']
    simp)
  have E3 := R3 T.left (lift x (lift x' y)).left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
  rw [Ft3 x x' y z J hJ, Fp3, Fa3 x x' y z J' hJ'] at E3
  refine ⟨symm, fun u u' v hu hu' hv => ?_⟩
  obtain rfl : u = toBase hw₀ x := Over.OverMorphism.ext hu
  obtain rfl : u' = toBase hw₀ x' := Over.OverMorphism.ext hu'
  obtain rfl : v = toBase hw₀ y := Over.OverMorphism.ext hv
  rw [id, E3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.LamRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLawsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_normalised_respects_laws : ∀ (S S' : Scheme.{0}) (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : RigLB B) (M' : RigLB B') (c : CubicalStr B M) (c' : CubicalStr B' M') (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M'.L) ((abelian₂ B M.L).pull β₂)) (hβ : IsGrpPullback B' B f β), IsAbelianScheme B' → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (x x' y : T ⟶ B') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift x y).left z J J' = lamVal w (lift y x).left z J J' ∧ ∀ (u u' v : Over.mk (T.hom ≫ f) ⟶ B), u.left = x.left ≫ β → u'.left = x'.left ≫ β → v.left = y.left ≫ β → lamVal w (lift (x * x') y).left z J J' * cubV c' z J' x x' y = @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J u u' v) * lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' := by
  first | exact @GlobalTheory.LamRigid.lam_iso_laws | exact GlobalTheory.LamRigid.lam_iso_laws | (intros; apply GlobalTheory.LamRigid.lam_iso_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

open GlobalTheory.DeRham

variable {K : Type} [Field K]

def IsTransl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) (w : Sp (DualNumber B) ⟶ A.left) : Prop :=
  ∃ x' v' : Over.mk (spMap ((algebraMap B (DualNumber B)).comp φ)) ⟶ A,
    x'.left = spMap (algebraMap B (DualNumber B)) ≫ x ∧ v'.left = spMap (dualMap φ) ≫ v.left ∧ (x' * v').left = w

def IsCechKS (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left) (L : LB A.left)
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι)
    (lam : ∀ (_ : J) (B : Type) [CommRing B] [Algebra (DualNumber K) B], (Sp B ⟶ A.left) → (Sp B ⟶ A'.left)),
    ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧
    (∀ k (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left),
      x ≫ A.hom = spMap ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) → ⊤ ≤ x ⁻¹ᵁ W k →
      lam k B x ≫ A'.hom = spMap (algebraMap (DualNumber K) B) ∧
      spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ lam k B x =
        spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ x ≫ i ∧
      ∀ (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'),
        spMap (ρ : B →+* B') ≫ lam k B x = lam k B' (spMap (ρ : B →+* B') ≫ x)) ∧
    ∀ (k k' : J) (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left)
      (O : A'.left.Opens) (f : Γ(A'.left, O)) (w : Fin n → (Sp (DualNumber B) ⟶ A.left)),
      x ≫ A.hom = spMap ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) →
      ⊤ ≤ x ⁻¹ᵁ (W k ⊓ W k') → ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O) →
      (∀ a, IsTransl ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) x (u a) (w a)) →
      valR (lam k B x) O f - valR (lam k' B x) O f =
        algebraMap (DualNumber K) B DualNumber.eps *
          ∑ a, ∑ b, (algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K)) (θ a b) *
            ((valR (w b) _ (L.g (c k) (c k')).val).snd * valR x _ (L.g (c k) (c k'))⁻¹.val) *
            (valR (w a) (i ⁻¹ᵁ O) ((i.app O).hom f)).snd

end GlobalTheory.CechKS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftGaps

theorem antitone_of_step {N : ℕ} {f : Fin N → ℤ} (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) : Antitone f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_le_mk] at hab
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge a (n + 1) with h' | h'
    · exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) (by omega))
    · obtain rfl : a = n + 1 := by omega
      exact le_rfl

theorem isQuot_u₁ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) : IsQuot Dw kc P.T P.c₀ P.u P.u₁ := by
  intro τ
  refine ⟨fun a (ha : (a : ℕ) + 1 = kc) => (P.anchored τ (by omega)).1, fun a b hb => ?_⟩
  have hb' : (a : ℕ) + 1 < Dw.p + Dw.q := hb ▸ b.2
  show P.u₁ τ a - P.u₁ τ b = (P.u τ a - P.u τ b + if (b : ℕ) = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2) /
    ((P.T : ℤ) + CompHt.dimFlag Dw + 1)
  rw [← CompHS.gap_eq (P.u₁ τ) hb, P.gap_u₁ τ hb', P.gap_uMinus_sub_kap τ hb', CompHS.gap_eq (P.u τ) hb, hb,
    WtPar.T₁, dimFlag_eq]

section Pt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem nCol_le (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    GlobalTheory.RefSum.nCol (dat p i) ≤ 2 * D.R.r * (D.R.f * D.R.r) + 8 * (D.R.f * D.R.r) + 8 := by
  obtain ⟨-, -, s3⟩ := hw.sig
  have hcard : Fintype.card (Lt1 (dat p i)) = D.R.f * D.R.r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [GlobalTheory.RefSum.sum_mult, hh.deg, s3]
    simp
  have hmult : ∀ τ, (dat p i).mult τ ≤ D.R.r := fun τ => by
    rw [← s3]; unfold Datum.mult; split_ifs <;> omega
  have hsum : ∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f ≤ Fintype.card (Lt1 (dat p i)) * (2 * D.R.r) := by
    rw [← smul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have := GlobalTheory.FactorDepth.rk_le f
    have := hmult f.1
    omega
  rw [hcard] at hsum
  unfold GlobalTheory.RefSum.nCol
  have h8 : 8 * ((∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f) / 8) ≤ ∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f :=
    Nat.mul_div_le _ _
  rw [hcard]
  have : D.R.f * D.R.r * (2 * D.R.r) = 2 * D.R.r * (D.R.f * D.R.r) := by ring
  omega

theorem cols_le_len (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    (GlobalTheory.RefSum.nCol (dat p i) + 1) * (CompHt.dimFlag (dat p i) + 3) ≤ lenT p i PP := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hr6 : 6 ≤ D.R.r := by omega
  have hf8 := hh.f8
  have hn := nCol_le p i PP A M hw hh
  have hZ : (40 : ℝ) ≤ zBase L := by
    unfold zBase
    have a1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
    have a2 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
    have a3 : (48 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
    have a4 : (10 : ℝ) ≤ L.sc.L := hh.big.2.1
    nlinarith
  have hPP : (40 : ℝ) ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hh.ppLow)
  have hD : ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    rw [hw.dim]; push_cast [Nat.cast_choose_two]; ring
  set Dd : ℝ := ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) with hDd
  have F8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
  have R6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
  have FR : (48 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have hDd1 : (1 : ℝ) ≤ Dd := by rw [hD]; nlinarith
  have hn' : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1 ≤ 17 * Dd := by
    have : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) ≤ 2 * D.R.r * (D.R.f * D.R.r) + 8 * (D.R.f * D.R.r) + 8 := by
      exact_mod_cast hn
    rw [hD]
    have h13 : (45 : ℝ) ≤ 13 * D.R.r - 33 := by linarith
    have : (48 : ℝ) * 45 ≤ ((D.R.f : ℝ) * D.R.r) * (13 * D.R.r - 33) := mul_le_mul FR h13 (by norm_num) (by linarith)
    nlinarith
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hkm : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hT : 1600 * Dd ^ 2 ≤ (lenT p i PP : ℝ) := by
    have h1 : 1600 * Dd ^ 2 ≤ PP ^ 2 * Dd ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      rw [le_div_iff₀ hm0]
      have c5 : (1600 : ℝ) ≤ PP ^ 2 := by nlinarith
      have c6 : (0 : ℝ) ≤ Dd ^ 2 := by positivity
      calc 1600 * Dd ^ 2 * D.R.m ≤ PP ^ 2 * Dd ^ 2 * D.R.m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c5 c6) hm0.le
        _ ≤ PP ^ 2 * Dd ^ 2 * D.R.k := mul_le_mul_of_nonneg_left hkm (by positivity)
    exact h1.trans (Nat.le_ceil _)
  have hmain : ((GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1) * (Dd + 3) ≤ (lenT p i PP : ℝ) := by
    have e1 : Dd + 3 ≤ 4 * Dd := by linarith
    have : ((GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1) * (Dd + 3) ≤ (17 * Dd) * (4 * Dd) :=
      mul_le_mul hn' e1 (by linarith) (by linarith)
    nlinarith
  rw [hDd] at hmain
  exact_mod_cast hmain

theorem gapsAt (PP A M : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    1 ≤ (dat p i).p ∧ ∀ la ∈ ({(⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁,
      (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))),
      (∀ τ, Antitone (la τ)) ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p →
        (b : ℕ) = (dat p i).p → (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ la τ a - la τ b := by
  obtain ⟨s1, s2, s3⟩ := hw.sig
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ep : (dat p i).p = D.R.k + i := by rw [s1]; unfold Ranks.sigW; omega
  have eq : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [s2]; rfl
  have hcl := cols_le_len p i PP A M hw hh
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  have hPa : P.a + 1 = D.R.k - 1 := by show D.R.k - 2 + 1 = D.R.k - 1; omega
  have hquo : Quo p i PP P.u₁ := isQuot_u₁ (dat p i) P (D.R.k - 1) hPa
  obtain ⟨h0, S, eta, -, -, -, hT2, -, hH⟩ := hw.hyp hi
  have hW := hH P.u₁
  have hdiv := (quo_iff p i PP h0 S eta P.u₁).1 hquo
  have G := GlobalTheory.MeanTop.divided_gaps _ _ _ hW hdiv
  have hT1 := hW.h1
  simp only [wtsAt] at G hT1

  have gin : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → 0 ≤ P.u₁ τ a - P.u₁ τ b := by
    intro τ a b hb
    obtain ⟨g1, g2, -⟩ := G τ a b hb
    by_cases hbp : (b : ℕ) = (dat p i).p
    · have g := (g2 hbp).1
      have hT0 : (0 : ℤ) < 2 * (lenT p i PP : ℤ) := by omega
      by_contra hc
      push_neg at hc
      have := mul_neg_of_pos_of_neg hT0 hc
      nlinarith
    · have g := g1 hbp
      have : (0 : ℤ) ≤ (lenT p i PP : ℤ) + CompHt.dimFlag (dat p i) + 2 + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
        positivity
      omega
  have gbar : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      (lenT p i PP : ℤ) ≤ P.u₁ τ a - P.u₁ τ b := by
    intro τ a b hb hbp
    obtain ⟨-, g2, -⟩ := G τ a b hb
    have g := (g2 hbp).2
    have hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ) := by omega
    have hle : (lenT p i PP : ℤ) ≤ P.u₁ τ a - P.u₁ τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hT0
      nlinarith
    have : (0 : ℤ) ≤ (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by positivity
    linarith

  have gub : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 →
      P.ub τ a - P.ub τ b = (P.u₁ τ a - P.u₁ τ b) / ((dimFlag (dat p i) : ℤ) + 3) := by
    intro τ a b hb
    have hb' : (a : ℕ) + 1 < (dat p i).p + (dat p i).q := hb ▸ b.2
    rw [← CompHS.gap_eq (P.ub τ) hb, P.gap_ub τ hb', CompHS.gap_eq (P.u₁ τ) hb]
  have hcl' : ((GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1) * ((dimFlag (dat p i) : ℤ) + 3) ≤ (lenT p i PP : ℤ) := by
    rw [← dimFlag_eq]; exact_mod_cast hcl
  have hD0 : (0 : ℤ) < (dimFlag (dat p i) : ℤ) + 3 := by positivity
  have hD1 : (1 : ℤ) ≤ (dimFlag (dat p i) : ℤ) + 3 := by omega
  have hnT : (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ (lenT p i PP : ℤ) := by
    have : (0 : ℤ) ≤ (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 := by positivity
    nlinarith
  refine ⟨by omega, fun la hla => ?_⟩
  rcases hla with rfl | hla
  · refine ⟨fun τ => antitone_of_step fun a b hb => by have := gin τ a b hb; omega, fun τ a b ha hb => ?_⟩
    exact hnT.trans (gbar τ a b (by omega) hb)
  · rw [Set.mem_singleton_iff] at hla
    subst hla
    refine ⟨fun τ => antitone_of_step fun a b hb => ?_, fun τ a b ha hb => ?_⟩
    · have e := gub τ a b hb
      have := Int.ediv_nonneg (gin τ a b hb) hD0.le
      omega
    · rw [gub τ a b (by omega)]
      exact Int.le_ediv_of_mul_le hD0 (hcl'.trans (gbar τ a b (by omega) hb))

end Pt

end GlobalTheory.LiftGaps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKRatInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) :
    ResEtaPow K (χ / χ') (n + m) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · simp
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg_one]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ x / χ' x
    exact h.1.div' h'.1
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

end GlobalTheory.ThKRatInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.PullAlong

theorem idlAlong_comap_eq : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X) (J : X.IdealSheafData) {R : Type} [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ Y), idlAlong (J.comap π) ξ = idlAlong J (ξ ≫ π) := by
  intro X Y π J R _ _ ξ
  unfold idlAlong
  rw [GlobalTheory.VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]
  rfl

end GlobalTheory.PullAlong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureFinitePartPreimage
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolPush

theorem meas_translate_eq : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K ∧ rp h ∈ B} = Measure.pi m B := by
  intro D V θ A m rp K μ hV hθ hA hm hc hrp hK hμ g hg B hB
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hμ.1
  have h1 : rp g = 1 := GlobalTheory.CovTop.VolBox.rp_eq_one V θ A rp hV hA hrp g hg
  rw [← GlobalTheory.CovTop.VolBox.meas_level V θ A m rp K μ hV hθ hA hm hc hrp hK hμ B hB,
    ← measure_preimage_mul μ g⁻¹ {h | finE V h ∈ K ∧ rp h ∈ B}]
  congr 1
  ext h
  show finE V (g⁻¹ * h) ∈ K ∧ rp h ∈ B ↔ finE V (g⁻¹ * h) ∈ K ∧ rp (g⁻¹ * h) ∈ B
  rw [map_mul rp, map_inv rp, h1, inv_one, one_mul]

end GlobalTheory.CovTop.VolPush
end
