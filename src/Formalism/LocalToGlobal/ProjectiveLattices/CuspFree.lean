module

public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  sec Xo c a n ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laU (U σ) a n)).comap (rdU (U σ))

theorem cusp_le_sec (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n ≤ sec Xo c a n := inf_le_left

theorem mem_cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    f ∈ cusp Xo c U a n ↔ f ∈ sec Xo c a n ∧ ∀ σ : c.F →+* ℂ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) := by
  simp only [cusp, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]

def mulC (f g : Rul Xo c) : Rul Xo c := f * g

theorem mulC_mem_sec (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : mulC Xo c f g ∈ sec Xo c (a + a') (n + n') := sec_mul Xo c a a' n n' hf hg

def CuspMul : Prop :=
  ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), Dom a n → Dom a' n' → f ∈ cusp Xo c U a n →
    g ∈ cusp Xo c U a' n' → mulC Xo c f g ∈ cusp Xo c U (a + a') (n + n')

set_option maxSynthPendingDepth 1 in
def CuspFD : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n)

end Formalism.L2.PjFree
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

section At

variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)

abbrev overAt (A : Type) [CommRing A] [Algebra S A] : Over X := Over.mk (spMap (algebraMap S A) ≫ x0)

theorem spMap_comp_alg {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B]
    (f : A →ₐ[S] B) : spMap (f : A →+* B) ≫ spMap (algebraMap S A) = spMap (algebraMap S B) := by
  first
    | rw [← spMap_comp, AlgHom.comp_algebraMap]
    | (unfold spMap; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

def homAt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B) :
    overAt x0 B ⟶ overAt x0 A :=
  Over.homMk (spMap (f : A →+* B)) (by
    dsimp
    rw [← Category.assoc, spMap_comp_alg])

end At

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)

abbrev jO (m n : ℕ) : Over Xo.X := overAt y.x (Jet S (Fin n × Fin d) m)

def jetCopy {n : ℕ} (m : ℕ) (i : Fin n) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m :=
  jetMap (fun p => X (i, p.2)) fun _ => X_mem_orig _

def jetSubstP {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) : Jet S κ m →ₐ[S] Jet S κ' m :=
  jetMap (fun i => φ i - C (MvPolynomial.constantCoeff (φ i))) fun _ => sub_const_mem_orig _

def psIn {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    MvPolynomial (Fin n' × Fin d) S :=
  MvPolynomial.rename (fun p => (r p.1, p.2)) (psTrunc m f)

def jpt (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) {n : ℕ} (m : ℕ) (i : Fin n) : jO y d m n ⟶ Xo.univ.t.G :=
  homAt y.x (jetCopy d m i) ≫ x m

structure IsChart (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) : Prop where
  zero : ∀ m, homAt y.x (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt y.x (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m
  law : ∀ m, homAt y.x (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m =
    jpt y d x m (0 : Fin 2) * jpt y d x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ Xo.univ.t.act.act a =
    homAt y.x (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act a p.2)) ≫ x m
  tan : ∀ ℓ : Lt1 Dw, IsCombAt y.x
    (fun j : Fin d => (homAt y.x (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left) (uvec ℓ)
    (y.u ℓ.1 ℓ.2)

  basis : ∀ v : Fin d → S, ∃! a : Lt1 Dw → S, ∀ j, ∑ ℓ, a ℓ * uvec ℓ j = v j

end Chart

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def cφ {T : Over Xo.X} {n : ℕ} (xs : Fin n → (T ⟶ Xo.univ.t.G)) :
    ULift (Finset (Fin n)) → (T.left ⟶ Xo.univ.t.G.left) :=
  fun I => (psum Xo.univ.t.G xs I.down).left

def cε (n : ℕ) : ULift (Finset (Fin n)) → ℤ := fun I => (-1) ^ (n - I.down.card)

def scaleGen {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) :
    LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

def genPow {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (k : ℕ) :
    LB.Gen (LB.LinComb Xo.univ.t.PP.L φ fun i => (k : ℤ) * ε i) :=
  ⟨fun j => g.s j ^ k⟩

def unitΓ {A : Type} [CommRing A] (u : Aˣ) : Γ(Sp A, ⊤)ˣ := Units.map (toΓ A).toMonoidHom u

variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)

abbrev FrTy (m : ℕ) : Type :=
  LB.Gen (cubeLB Xo.univ.t.G ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)] Xo.univ.t.PP.L)

def pe (e : ∀ m, FrTy y d x m) (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :=
  LB.pullGen Xo.univ.t.PP.L (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2) (e m)
    (homAt y.x (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left

structure IsFrame (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTy y d x m) : Prop where
  gen : ∀ m, (e m).IsGen
  ph1 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
        (lift (jpt y d x m (0 : Fin 3)) (lift (jpt y d x m (1 : Fin 3)) (jpt y d x m (2 : Fin 3)))).left)
      (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (pe y d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.invGen Xo.univ.t.PP.L _ _ (pe y d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen Xo.univ.t.PP.L _ _ (pe y d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  ph2 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
        (lift (jpt y d x m (1 : Fin 3)) (lift (jpt y d x m (2 : Fin 3)) (jpt y d x m (0 : Fin 3)))).left)
      (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (pe y d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.invGen Xo.univ.t.PP.L _ _ (pe y d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen Xo.univ.t.PP.L _ _ (pe y d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  sy : ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m)
      (scaleGen _ _ (unitΓ u⁻¹) (pe y d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))
  ad : ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb Xo.univ.t.PP.L
      (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)])
        (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y d x m (0 : Fin 2)) (jpt y d x m (1 : Fin 2))).left)
          (pe y d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)]))
        (scaleGen _ _ (unitΓ u)
          (pe y d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

end Frame

section Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)

def jBase (m n : ℕ) : jO y d m n ⟶ ptO Xo y.x :=
  Over.homMk (spMap (algebraMap S (Jet S (Fin n × Fin d) m))) rfl

abbrev PrimTy (H : Host E) (Xo : Moduli Dw l) : Type :=
  LB.Gen (LB.LinComb Xo.univ.t.PP.L
    (Sum.elim (fun _ : Fin 1 => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0]))
    (Sum.elim (fun _ => 1) fun I => -cε 2 I))

def IsPrim (wP : PrimTy H Xo) : Prop :=
  wP.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ wP (eSec Xo.univ.t.G)) Xo.univ.t.PP.rig

def eL (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo)
    (m : ℕ) :=
  LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wP (x m).left)
    (pe y d x e m ![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)])

def IsGerm (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTy y d x m)
    (wP : PrimTy H Xo) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y d m 1)))
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y d x act e wP m) k) ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (x m) τ (toΓ _ (psJet m f))

end Germ

section Pin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

structure ChartAt [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) where
  d : ℕ
  B : Germ.FB S d (𝓞 E)
  uvec : Lt1 Dw → Fin d → S
  x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G
  e : ∀ m, FrTy y d x m
  wP : PrimTy H Xo
  h : Germ.PS S 2 d
  chart : IsChart y d B.G.F B.A.act uvec x
  frame : IsFrame y d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e
  prim : IsPrim wP
  gauge : B.IsCanonGauge S h

  rig0 : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (eL y d x B.A.act e wP 0)
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left)
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)

def IsNab [StarRing (𝓞 E)] (nab : NabV Xo c) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) ∧
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S),
    ∃ C : ChartAt Xo c y,
      (∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))),
        ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) ∧
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
        (f : MvPowerSeries (Fin 1 × Fin C.d) S),
        IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
          ∀ α : Lt1 Dw →₀ ℕ, nab y k F α = C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1)

end Pin

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ThProps
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ThValTot (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∃! v, ThValAt Xo c nab y x P v

def LastPos (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ τ : E →+* ℂ, InPsi H τ → 0 < Dw.mult τ → 0 < a (τ, Dw.mult τ - 1)

def ThInCusp (nab : NabV Xo c)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a →
    ∀ f ∈ thGen Xo c nab a n, f ∈ cusp a n

def DF (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)

def ThNe0 (nab : NabV Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 0 < n → Dw.p + Dw.q ≤ n → DF Dw a + 2 ≤ l.M →
    (∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) → ∃ f ∈ thGen Xo c nab a n, f ≠ 0


theorem existsUnique_thRule (nab : NabV Xo c) (h : ThValTot Xo c nab) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (x : Fin n → Dw.La) {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) :
    ∃! f : Rul Xo c, IsThRule Xo c nab x P f := by
  refine ⟨fun p y => (h p.R y a n x P hP).exists.choose,
    fun p y => (h p.R y a n x P hP).exists.choose_spec, ?_⟩
  intro g hg
  funext p y
  exact (h p.R y a n x P hP).unique (hg p y) (h p.R y a n x P hP).exists.choose_spec

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CompFin
noncomputable section

namespace Formalism.L2.Pj.CompFin

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem finiteType_zero (R : Type) [CommRing R] (N : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _ (⟨MvPolynomial.C r, (MvPolynomial.mem_homogeneousSubmodule _ _).2
      (MvPolynomial.isHomogeneous_C _ r)⟩ : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (by simp))

theorem quasiCompact_str (R : Type) [CommRing R] (N : ℕ) : QuasiCompact (PSpace.str R N) := by
  haveI := finiteType_zero R N
  unfold PSpace.str
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem quasiCompact_alt (Xo : Moduli Dw l) : QuasiCompact Xo.s := by
  obtain ⟨N, i, -, hq, h⟩ := Xo.qproj
  haveI := hq
  haveI := quasiCompact_str (KA l) N
  rw [← h]
  infer_instance

theorem isNoetherian_XF (Xo : Moduli Dw l) (c : Coeff l) : IsNoetherian (Xo.XF c) := by
  obtain ⟨N, i, hi, hq, h⟩ := Xo.qproj
  haveI := hq
  haveI := hi
  haveI := finiteType_zero (KA l) N
  have hsurj : Function.Surjective
      (algebraMap (KA l) (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (KA l) 0)) := by
    rintro ⟨x, hx⟩
    have hx' := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hx
    refine ⟨AddMonoidAlgebra.coeff x 0, Subtype.ext ?_⟩
    rcases eq_or_ne x 0 with rfl | h0
    · simp
    · exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (hx'.totalDegree h0)).symm
  haveI : IsClosedImmersion
      (spMap (algebraMap (KA l) (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (KA l) 0))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  haveI : LocallyOfFiniteType Xo.s := by
    rw [← h]
    unfold PSpace.str
    infer_instance
  haveI := quasiCompact_alt Xo
  constructor

theorem finite_comp (Xo : Moduli Dw l) (c : Coeff l) : Finite (Comp Xo c) := by
  haveI := isNoetherian_XF Xo c
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype

end Formalism.L2.Pj.CompFin
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Open

variable (Xo : Moduli Dw l) (c : Coeff l)

def WtField : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S),
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y →
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y' →
      FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

def IntDiagUnit : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ),
    (letI := io.toAlgebra; FrBor t y.1 y'.1) → ∀ i, valV T.V ((t i : T.Frˣ) : T.Fr) = 1

def AlgPtLa : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e),
    T.FinRes ∧ ∃ x : Sp T.Fr ⟶ Xo.X, (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr)

def IntFrExt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → ∀ x : Sp T.Fr ⟶ Xo.X, (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) →
    ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r ∧ (∀ z, vV T'.V (i z) = (r : ℤ) * vV T.V z) ∧ T'.FinRes ∧
      ∃ y : IntFr Xo c T' (i.comp io), (letI := (i.comp io).toAlgebra; y.1.x = spMap i ≫ x)

end Open

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem valV_wchar_eq_one {T : CDVR} (e : Ix Dw → ℕ) (t : Ix Dw → T.Frˣ)
    (ht : ∀ i, valV T.V ((t i : T.Frˣ) : T.Fr) = 1) : valV T.V (wchar e t) = 1 := by
  simp [wchar, map_prod, map_pow, ht]

private theorem vV_mul_lemma {T : CDVR} {w x : T.Fr} (hu : valV T.V w = 1) (hx : x ≠ 0) :
    vV T.V (w * x) = vV T.V x := by
  unfold vV
  rw [map_mul, hu, one_mul]

theorem unitIndep_of (hW : WtField Xo c) (hU : IntDiagUnit Xo c) : UnitIndep Xo c := by
  intro a n f hf T io y y' t hb e
  letI := io.toAlgebra
  have hw := hW a n f hf T.Fr t y.1 y'.1 y.2.1 y'.2.1 hb
  have hu := valV_wchar_eq_one (ex Dw a n) t (hU T io y y' t hb)
  unfold nval evI
  rw [hw]
  generalize evR Xo c f y.1 = x at *
  have hne : wchar (ex Dw a n) t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact zero_ne_one hu
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (mul_ne_zero hne hx), if_neg hx, vV_mul_lemma hu hx]

theorem intFrNe_of (hA : AlgPtLa Xo c) (hE : IntFrExt Xo c) :
    IntFrNe Xo c (fun _ _ y => IntFr.IsAlg y) := by
  intro la
  obtain ⟨T, io, e, hO, hF, x, hx⟩ := hA la
  obtain ⟨T', i, r, hr, hv, hF', y, hy⟩ := hE T io hF x hx
  unfold OverLa IntFr.IsAlg at *
  refine ⟨T', i.comp io, r * e, ⟨Nat.mul_pos hr hO.1, fun a => ?_⟩, y, hF'⟩
  rw [RingHom.comp_apply, hv, hO.2 a]
  push_cast
  ring

end Proofs

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CompData
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

abbrev WTZ (E : Type) [Field E] : Type := ((E →+* ℂ) × ℕ → ℤ) × ℤ

def wtZ {E : Type} [Field E] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : WTZ E := (fun x => (a x : ℤ), (n : ℤ))

theorem wtZ_add {E : Type} [Field E] (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) :
    wtZ (a + a') (n + n') = wtZ a n + wtZ a' n' := by
  unfold wtZ
  ext <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev AC (Z : Comp Xo c) : Type := AddMonoidAlgebra (Om Z) (WTZ E)

instance towKAC (Z : Comp Xo c) : IsScalarTower c.F (Om Z) (AC Z) := inferInstance

def AG (Z : Comp Xo c) (G : WTZ E) : Submodule (Om Z) (AC Z) :=
  Submodule.span (Om Z) {AddMonoidAlgebra.single G 1}

theorem mem_AG {Z : Comp Xo c} {G : WTZ E} {f : AC Z} : f ∈ AG Z G ↔ ∃ r : Om Z, f = AddMonoidAlgebra.single G r := by
  unfold AG
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [AddMonoidAlgebra.smul_single', mul_one]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [AddMonoidAlgebra.smul_single', mul_one]⟩

instance gradedAG (Z : Comp Xo c) : SetLike.GradedMonoid (AG Z) where
  one_mem := mem_AG.2 ⟨1, rfl⟩
  mul_mem := by
    intro G G' f g hf hg
    obtain ⟨r, rfl⟩ := mem_AG.1 hf
    obtain ⟨s, rfl⟩ := mem_AG.1 hg
    exact mem_AG.2 ⟨r * s, by rw [AddMonoidAlgebra.single_mul_single]⟩

theorem finrank_AG (Z : Comp Xo c) (G : WTZ E) : Module.finrank (Om Z) (AG Z G) = 1 :=
  finrank_span_singleton (by simp)

theorem mul_ne_zero_AG {Z : Comp Xo c} {G G' : WTZ E} {f g : AC Z} (hf : f ∈ AG Z G) (hg : g ∈ AG Z G')
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) : f * g ≠ 0 := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  have hr : r ≠ 0 := by
    rintro rfl
    exact hf0 (by simp)
  have hs : s ≠ 0 := by
    rintro rfl
    exact hg0 (by simp)
  rw [AddMonoidAlgebra.single_mul_single]
  simp [hr, hs]

def valC (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ∀ Z : Comp Xo c, AC Z :=
  fun Z => AddMonoidAlgebra.single (wtZ a n) (evC h Z f)

theorem valC_mem (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h a n f Z ∈ AG Z (wtZ a n) := mem_AG.2 ⟨_, rfl⟩

end Formalism.L2.Pj
end
end

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def exZ (Dw : Datum H) (G : WTZ E) : Ix Dw → ℤ
  | none => G.2
  | some x => G.1 (x.1, x.2)

theorem exZ_add (G G' : WTZ E) (i : Ix Dw) : exZ Dw (G + G') i = exZ Dw G i + exZ Dw G' i := by
  cases i <;> rfl

def frW (δ : Ix Dw → ℤ) (G : WTZ E) : ℤ := ∑ i, exZ Dw G i * δ i

theorem frW_add (δ : Ix Dw → ℤ) (G G' : WTZ E) : frW δ (G + G') = frW δ G + frW δ G' := by
  simp only [frW, exZ_add, add_mul, Finset.sum_add_distrib]

variable {Z : Comp Xo c}

def ordC (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (G : WTZ E) (x : AC Z) : ℤ :=
  WithTop.untopD 0 (v (x.coeff G)) + frW δ G

theorem ordC_single (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (G : WTZ E) {r : Om Z} (hr : r ≠ 0) :
    ((ordC δ v G (AddMonoidAlgebra.single G r) : ℤ) : WithTop ℤ) = v r + (frW δ G : WithTop ℤ) := by
  have hv : v r ≠ ⊤ := fun h => hr ((AddValuation.top_iff v).1 h)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hv
  simp only [ordC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, ← hn, WithTop.untopD_coe]
  push_cast; rfl

theorem ordC_mul (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G G' : WTZ E} {f g : AC Z}
    (hf : f ∈ AG Z G) (hg : g ∈ AG Z G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    ordC δ v (G + G') (f * g) = ordC δ v G f + ordC δ v G' g := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  have hs : s ≠ 0 := fun h => hg0 (by simp [h])
  rw [AddMonoidAlgebra.single_mul_single]
  apply WithTop.coe_injective
  rw [ordC_single δ v _ (mul_ne_zero hr hs)]
  push_cast
  rw [ordC_single δ v _ hr, ordC_single δ v _ hs, AddValuation.map_mul, frW_add]
  push_cast
  ac_rfl

theorem ordC_smul (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G : WTZ E} {f : AC Z} (a : Om Z)
    (hf : f ∈ AG Z G) (hf0 : f ≠ 0) (ha : a ≠ 0) :
    ((ordC δ v G (a • f) : ℤ) : WithTop ℤ) = v a + (ordC δ v G f : WithTop ℤ) := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  rw [AddMonoidAlgebra.smul_single', ordC_single δ v _ (mul_ne_zero ha hr), ordC_single δ v _ hr,
    AddValuation.map_mul, add_assoc]

abbrev sgOf (P : Om Z →+* ℂ) : c.F →+* ℂ := P.comp (algebraMap c.F (Om Z))

def PAlg (P : Om Z →+* ℂ) : Om Z →ₐ[c.F] CAt (sgOf P) :=
  { P with commutes' := fun _ => rfl }

def CBase (h : GenFrEx Xo c) (Z : Comp Xo c) (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ P, FrMap (PAlg P) (genFr h Z) (yP P)

def nrmC (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (G : WTZ E) (x : AC Z) (P : Om Z →+* ℂ) : ℝ :=
  ‖P (x.coeff G)‖ * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i)


variable (Xo c) in
def FnNe (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) : Prop := ∀ σ y i, fn σ y i ≠ 0

section nrm

variable (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
  (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

theorem nrmC_zero (G : WTZ E) (P : Om Z →+* ℂ) : nrmC fn yP G 0 P = 0 := by
  simp only [nrmC, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero, norm_zero, zero_mul]

theorem nrmC_single (G : WTZ E) (r : Om Z) (P : Om Z →+* ℂ) :
    nrmC fn yP G (AddMonoidAlgebra.single G r) P = ‖P r‖ * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i) := by
  simp only [nrmC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

theorem nrmC_pos (hfn : FnNe Xo c fn) {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G) (hf0 : f ≠ 0) :
    0 < nrmC fn yP G f P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  rw [nrmC_single]
  refine mul_pos (norm_pos_iff.2 ((map_ne_zero P).2 hr)) (Finset.prod_pos fun i _ => ?_)
  exact zpow_pos (abs_pos.2 (hfn _ _ i)) _

theorem nrmC_mul (hfn : FnNe Xo c fn) {G G' : WTZ E} {f g : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G)
    (hg : g ∈ AG Z G') : nrmC fn yP (G + G') (f * g) P = nrmC fn yP G f P * nrmC fn yP G' g P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  rw [AddMonoidAlgebra.single_mul_single, nrmC_single, nrmC_single, nrmC_single, map_mul, norm_mul]
  have : ∏ i, |fn _ (yP P) i| ^ (-exZ Dw (G + G') i) =
      (∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i)) * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G' i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [exZ_add, neg_add, zpow_add₀ (abs_ne_zero.2 (hfn _ _ i))]
  rw [this]; ring

theorem nrmC_smul {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (a : Om Z) (hf : f ∈ AG Z G) :
    nrmC fn yP G (a • f) P = ‖P a‖ * nrmC fn yP G f P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  rw [AddMonoidAlgebra.smul_single', nrmC_single, nrmC_single, map_mul, norm_mul, mul_assoc]

end nrm


variable (Xo c) in
def FnConj (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ Z (G : WTZ E) (x : AC Z) (P : Om Z →+* ℂ),
    nrmC fn (yP Z) G x ((starRingEnd ℂ).comp P) = nrmC fn (yP Z) G x P

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.PtFree
noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section One

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]

structure IsVal (la : HeightOneSpectrum (𝓞 K)) (v : R → EReal) : Prop where
  zero : v 0 = ⊤
  ne_bot : ∀ r, v r ≠ ⊥
  add : ∀ r s, min (v r) (v s) ≤ v (r + s)
  smul : ∀ (a : K) r, a ≠ 0 → v (a • r) = (((vLa la a : ℤ) : ℝ) : EReal) + v r
  mul : ∀ r s, v (r * s) = v r + v s

end One

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)

def algCls (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop := y.IsAlg

def valSet (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  Set.range (vAtV : PtV Xo c cls Unit (fun _ _ _ _ => True) la → Rul Xo c → EReal)

variable {Xo c cls}

theorem isVal_vAt {PY : Type} {lies : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) : IsVal la (vAtV y) := by
  obtain ⟨⟨g, hg⟩, T, io, e, hO, y0, hcls, eta, hl, heq⟩ := y
  unfold vAtV
  dsimp only
  unfold profI at heq
  have hg1 := congrArg Prod.fst heq
  dsimp only at hg1
  subst hg1
  have h0 : evI y0 (0 : Rul Xo c) = 0 := by
    have h := evI_add y0 (0 : Rul Xo c) 0
    simp only [add_zero] at h
    apply add_left_cancel (a := evI y0 0)
    simpa only [add_zero] using h.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show nval T.V e (evI y0 0) = ⊤
    rw [h0, nval_zero]
  · intro r
    show nval T.V e (evI y0 r) ≠ ⊥
    by_cases hr : evI y0 r = 0
    · rw [hr, nval_zero]
      simp
    · rw [nval_of_ne hr]
      exact EReal.coe_ne_bot _
  · intro r s
    show min (nval T.V e (evI y0 r)) (nval T.V e (evI y0 s)) ≤ nval T.V e (evI y0 (r + s))
    rw [evI_add]
    exact nval_add e _ _
  · intro a r ha
    show nval T.V e (evI y0 (a • r)) = (((vLa la a : ℤ) : ℝ) : EReal) + nval T.V e (evI y0 r)
    have hio : nval T.V e (io a) = (((vLa la a : ℤ) : ℝ) : EReal) := by
      rw [nval_of_ne ((map_ne_zero io).2 ha), hO.2 a]
      congr 1
      have he : (e : ℝ) ≠ 0 := by exact_mod_cast hO.1.ne'
      push_cast
      field_simp
    rw [evI_smul, nval_mul, hio]
  · intro r s
    show nval T.V e (evI y0 (r * s)) = nval T.V e (evI y0 r) + nval T.V e (evI y0 s)
    rw [evI_mul, nval_mul]

theorem isVal_valSet (la : HeightOneSpectrum (𝓞 c.F)) : ∀ v ∈ valSet Xo c cls la, IsVal la v := by
  rintro v ⟨y, rfl⟩
  exact isVal_vAt y

variable (Xo c cls)

variable {Xo c cls}

end Formalism.L2.PjFree
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.HeckeFr
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def hkKer (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) :
    Type :=
  {C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y.x) Dw 𝔓 p i C}

def IsHkIsog {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : ℕ) (y y'' : Sp Ω ⟶ Xo.X)
    (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G)) : Prop :=
  y'' ≫ Xo.s = y ≫ Xo.s ∧ ψ ≫ pullback.snd _ _ = pullback.snd _ _ ∧ (∀ x, fibPt _ x ≫ ψ = fibPt _ (ψp x)) ∧
    (∀ a x, ψp (x ≫ Xo.univ.t.act.act a) = ψp x ≫ Xo.univ.t.act.act a) ∧
    Function.Surjective ψp ∧ ψp.ker = C ∧
    (∀ (n : ℕ) (x x' : Over.mk y ⟶ Xo.univ.t.G) (u : Ωˣ), n.Coprime p →
      ReciprocityTheory.ChartRestriction.G.Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn u) →
      ReciprocityTheory.ChartRestriction.G.Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n (ψp x) (ψp x') (unitOn (u ^ (p ^ 2)))) ∧
    ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a,
      ψp (toUnit _ ≫ Xo.univ.eta (p' • a)) = toUnit _ ≫ Xo.univ.eta a ∧
      ψp (toUnit _ ≫ Xo.univ.etaA (p' • a)) = toUnit _ ≫ Xo.univ.etaA a

def IsLieImageH {Ω : Type} [Field Ω] (p : ℕ) {y y'' : Sp Ω ⟶ Xo.X}
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (v v' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber Ω) ⟶ pullback Xo.univ.t.G.hom y,
    w ≫ pullback.fst _ _ = v ∧ w ≫ pullback.snd _ _ = spMap (algebraMap Ω (DualNumber Ω)) ∧
      v' = spMap (epsMul ((p : Ω)⁻¹)) ≫ w ≫ ψ ≫ pullback.fst _ _

def HkPt (p : ℕ) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (sTr : ∀ (y z : FrPt Xo c Ω), (pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) → Prop)
    (y : FrPt Xo c Ω) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)) (z : FrPt Xo c Ω) : Prop :=
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)),
    IsHkIsog p y.x z.x C ψ ψp ∧ (∀ τ j, IsLieImageH p ψ (y.u τ j) (z.u τ j)) ∧ sTr y z ψ

def hkRelFr (𝔓 : Ideal (𝓞 E)) (p i : ℕ)
    (sTr : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y z : FrPt Xo c Ω),
      (pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) → Prop)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) 𝔓 p i Ω y)
    (z : FrPt Xo c Ω) : Prop :=
  HkPt p (sTr Ω) y C.1 z

end Formalism.L2.Pj
end
end
