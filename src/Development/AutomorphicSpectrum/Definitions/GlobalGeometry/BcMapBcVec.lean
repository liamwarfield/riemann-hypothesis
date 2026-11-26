module

public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
open Module NumberField IsDedekindDomain MeasureTheory
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.Lat

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BC

variable {K L Rl : Type} [Field K] [Field L] [AddCommGroup Rl] [Module K Rl]




variable (φ : K →+* L)


end BC

section OLat

variable {K Rl : Type} [Field K] [NumberField K] [CommRing Rl] [Algebra K Rl] [Algebra (𝓞 K) Rl] [IsScalarTower (𝓞 K) K Rl]

def supLat (C : Submodule K Rl) (Vs : HeightOneSpectrum (𝓞 K) → Set (Rl → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) :
    Submodule (𝓞 K) Rl :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_supLat (C : Submodule K Rl) (Vs : HeightOneSpectrum (𝓞 K) → Set (Rl → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (f : Rl) : f ∈ supLat C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hf, h⟩
    exact ⟨⟨f, hf⟩, h, rfl⟩

end OLat

section SecZ

variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

def secWZ (e : ι → ℤ) : Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩

end SecZ

section Forms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

abbrev ExZ (E : Type) [Field E] : Type := (E →+* ℂ) × ℕ → ℤ

def exZ (Dw : Datum H) (a : ExZ E) (n : ℕ) : Ix Dw → ℤ
  | none => n
  | some x => a (x.1, x.2)

variable (Xo : Moduli Dw l) (c : Coeff l)

def secZ (a : ExZ E) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  secWZ (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (exZ Dw a n)

variable {Xo c} {r : ℕ}


open Classical in
def laZ {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a : ExZ E) (n : ℕ) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then
      a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) + ((n / 2 : ℕ) : ℤ)
    else -a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) - ((n / 2 : ℕ) : ℤ)

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspZ (a : ExZ E) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  secZ Xo c a n ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a n)).comap (rdU (U σ))

def latZ (a : ExZ E) (n : ℕ) : Submodule (𝓞 c.F) (Rul Xo c) :=
  supLat (cuspZ U a n) (valSet Xo c (algCls Xo c)) fun la => isVal_valSet la

theorem mem_latZ (a : ExZ E) (n : ℕ) (f : Rul Xo c) :
    f ∈ latZ U a n ↔ f ∈ cuspZ U a n ∧ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f :=
  mem_supLat _ _ _ f

def lieZ (Dw : Datum H) (x : ℝ) (a : ExZ E) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

end Forms

section Pet

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r)


end Pet

end GlobalTheory.CompanionTheory.Ar.Rec.Lat
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlCTendsto
section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EvLApply
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Forms

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

abbrev WZ (E : Type) [Field E] : Type := (E →+* ℂ) × ℕ → ℤ

def exZ (Dw : Datum H) (a : WZ E) : Ix Dw → ℤ
  | none => 0
  | some x => a (x.1, x.2)

def secWZ {K : Type} [Field K] {ι : Type} [Fintype ι] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop) (e : ι → ℤ) :
    Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
    f p y' = (∏ i, ((t i ^ e i : (p.R)ˣ) : p.R)) * f p y}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩

def latIn {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R]
    (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) :
    Submodule (𝓞 K) R :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_latIn {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (f : R) : f ∈ latIn C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f :=
  ⟨fun ⟨g, hg, e⟩ => e ▸ ⟨g.2, hg⟩, fun h => ⟨⟨f, h.1⟩, h.2, rfl⟩⟩

variable (Xo : Moduli Dw l) (c : Coeff l)

def secZ (a : WZ E) : Submodule c.F (Rul Xo c) :=
  secWZ (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (exZ Dw a)

theorem secZ_nat (a : (E →+* ℂ) × ℕ → ℕ) : secZ Xo c (fun x => (a x : ℤ)) = sec Xo c a 0 := by
  have h : ∀ (S : Type) [CommRing S] (t : Ix Dw → Sˣ),
      (∏ i, ((t i ^ exZ Dw (fun x => (a x : ℤ)) i : Sˣ) : S)) = wchar (ex Dw a 0) t := by
    intro S _ t
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i <;> simp [exZ, ex]
  ext f
  refine and_congr Iff.rfl (forall_congr' fun p => forall_congr' fun t => forall_congr' fun y => forall_congr' fun y' =>
    forall_congr' fun _ => ?_)
  rw [h]


variable {Xo c} in
open Classical in
def laZ {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (a : WZ E) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0)
    else -a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ))

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspZ (a : WZ E) : Submodule c.F (Rul Xo c) :=
  secZ Xo c a ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a)).comap (rdU (U σ))

variable {Xo c}

def evL (h : GenFrEx Xo c) (Z : Comp Xo c) : Rul Xo c →ₗ[c.F] Om Z :=
  evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)

theorem evL_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (f : Rul Xo c) : evL h Z f = evC h Z f := rfl

def cuspOn (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Submodule c.F (Rul Xo c) :=
  cuspZ Xo c U a ⊓ ⨅ (Z' : Comp Xo c) (_ : Z' ≠ Z), LinearMap.ker (evL h Z')

def latOn (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Submodule (𝓞 c.F) (Rul Xo c) :=
  latIn (cuspOn U h a Z) (valSet Xo c (algCls Xo c)) isVal_valSet

def volL (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) (Dn : ℕ) : ℝ :=
  limsup (fun n : ℕ => (Dn.factorial : ℝ) * (Module.finrank c.F (cuspOn U h (n • a) Z) : ℝ) / (n : ℝ) ^ Dn) atTop

def lieFacZ (Dw : Datum H) (x : ℝ) (a : WZ E) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

variable {D : D7} (W : HSp D) (dict : ∀ σ, GA D W → Σ k, Frame ((U σ).X k).Ψ r)



end Forms

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Numbers

open Formalism.BasicNotions Formalism.MainNotions
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (conjEmb)

variable (D : D7) (i : Fin D.R.m)

def Dn : ℕ := D.R.f * D.R.r.choose 2


end Numbers

section Geo

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure SharpGeo (Q : Par D) (M : ℕ) : Type 1 where
  l : Level Q.H
  c : Coeff l
  Xo : ∀ i : Fin D.R.m, Moduli (Q.Dw ((i : ℕ) + 1)) l
  U : ∀ i (σ : c.F →+* ℂ), Unf (Xo i) c σ D.R.r
  dict : ∀ (i : Fin D.R.m) σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U i σ).X k).Ψ D.R.r

  e : ∀ i, Comp (Xo i) c → Rul (Xo i) c
  gen : ∀ i, GenFrEx (Xo i) c
  pins : Q.Pins
  level : l.M = M ∧ l.A = 1 ∧ l.Mb ≤ Q.l.Mb
  field : Q.c.F ≤ c.F

  comps : ∀ i, Nat.card (Comp (Xo i) c) = Fintype.card (U i c.F.val.toRingHom).Comp
  genT : ∀ i, GenFromTest (Xo i) c (gen i)
  evalWD : ∀ i, EvalWD (K := c.F) (fun S _ _ => FrPt (Xo i) c S) (fun φ y z => FrMap φ y z)
  unf : ∀ i σ, GoodEmb c σ → IsUnf (U i σ)
  unTest : ∀ i σ, GoodEmb c σ → ∀ k x,
    FromTest (K := c.F) (fun S _ _ => FrPt (Xo i) c S) (fun φ y z => FrMap φ y z) ((U i σ).un k x)
  chiTriv : ∀ i σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U i σ).X k).Γ,
    ((U i σ).X k).χ (laU (U i σ) a n k) γ = 1

  dictU : ∀ (i : Fin D.R.m) σ, GoodEmb c σ → ∃ Kf th hr, IsLevelK (D.sp.W ((i : ℕ) + 1)) l.M Kf ∧
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W ((i : ℕ) + 1)) (dict i σ) Kf th hr ∧
    ∀ g τ k, ‖dmin ((U i σ).X (dict i σ g).1).Gm (dict i σ g).2 τ k‖ = 1
  modelW : ∀ (i : Fin D.R.m) σ, GoodEmb c σ → ∃ hr : (D.sp.W ((i : ℕ) + 1)).rank = D.R.r,
    ∀ k, ModelW (D.sp.W ((i : ℕ) + 1)) hr ((U i σ).X k)
  xiAbs : ∀ i σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U i σ).X k).ξ0‖ = xiR D
  finVol : ∀ i : Fin D.R.m, FinVol (D.sp.W ((i : ℕ) + 1))
  ptNe : ∀ i, IntFrNe (Xo i) c (algCls (Xo i) c)
  intAll : ∀ i, IntAll (Xo i) c
  e_sec : ∀ i Z, e i Z ∈ sec (Xo i) c 0 0
  e_val : ∀ i Z, evC (gen i) Z (e i Z) = 1 ∧ ∀ Z', Z' ≠ Z → evC (gen i) Z' (e i Z) = 0

variable {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m)

end Geo

end GlobalTheory.CompanionTheory.Ar.Rec
end
end
