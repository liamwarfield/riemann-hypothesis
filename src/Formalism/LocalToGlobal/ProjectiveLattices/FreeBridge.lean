module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfB
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

end Sections

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def Unf.ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

def Unf.toPj (U : Unf Xo c σ r) : Formalism.L2.Pj.Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

theorem rdU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (f : Formalism.L2.Pj.Rul Xo c) : rdU (Unf.ofPj U) f = Formalism.L2.Pj.rdU U f := rfl

theorem laU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) :
    laU (Unf.ofPj U) a n k = Formalism.L2.Pj.laU U a n k := rfl

theorem isUnf_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : IsUnf (Unf.ofPj U) ↔ Formalism.L2.Pj.IsUnf U := by rfl

theorem goodEmb_iff (σ : c.F →+* ℂ) : GoodEmb c σ ↔ Formalism.L2.Pj.GoodEmb c σ := by rfl

variable (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)

theorem cusp_ofPj (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (fun σ => Unf.ofPj (U σ)) a n = Formalism.L2.Pj.cusp Xo c U a n := rfl

theorem cuspMul_ofPj : CuspMul Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspMul Xo c U := by rfl

theorem cuspFD_ofPj : CuspFD Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspFD Xo c U := by rfl

theorem supDef_ofPj : SupDef Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.SupDef Xo c U := by rfl

theorem regP_ofPj : regular₂ Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.regular₂ Xo c U := by rfl

end Unif

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l) (cls : ∀ (T : Formalism.L2.Pj.CDVR) (ι : c.F →+* T.Fr), Formalism.L2.Pj.IntFr Xo c T ι → Prop)

end Points

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {r : ℕ}

end Frames

end Formalism.L2.PjFree
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Char

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def CUnit (c : Comp → ℂ) : Prop := ∀ k, ‖c k‖ = 1

def muPin (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) : GA D V → ℂ :=
  fun g => c (dict g).1 * mu g

theorem adel_muPin (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) (P : FDSec X) (g : GA D V) :
    adel V dict (muPin V dict mu c) P g = c (dict g).1 * mu g * P (dict g).1 (dict g).2 := rfl

def MuVal (V : HSp D) (χ : (AE D)ˣ →* Circle) (mu : GA D V → ℂ) : Prop :=
  (∀ g, ∃ x, IsDetRoot V g x) ∧ ∀ g x, IsDetRoot V g x → mu g = ((χ x : Circle) : ℂ)

theorem MuVal.norm {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) (g : GA D V) :
    ‖mu g‖ = 1 := by
  obtain ⟨x, hx⟩ := h.1 g
  rw [h.2 g x hx]
  first
    | exact Circle.norm_coe _
    | exact Circle.abs_coe _
    | exact mem_sphere_zero_iff_norm.mp (χ x).2

def FinUnit (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D

def MuConj {K : Type} [Field K] (σ₀ σ : K →+* ℂ) (χ₀ χσ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x, FinUnit x → ∃ y : K, ((χ₀ x : Circle) : ℂ) = σ₀ y ∧ ((χσ x : Circle) : ℂ) = σ y

def CEquiv (V : HSp D) {K : Type} [Field K] (σ : K →+* ℂ) {C : Type} [AddCommGroup C] [Module K C]
    {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) {G0 : Type} [Group G0] (ρ : G0 →* (C →ₗ[K] C)) (chi : G0 →* Kˣ) (ℓ : G0 → GA D V) : Prop :=
  (∃ c' : Comp → ℂ, CUnit c' ∧ EquivariantFiniteGroup V σ rd dict (muPin V dict mu c') ρ chi ℓ) →
    EquivariantFiniteGroup V σ rd dict (muPin V dict mu c) ρ chi ℓ

end Char

section Dict

variable {D : D7}

def finVec (V : HSp D) (v : Fin V.rank → D.host.E) : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i => (1 : Af D.host.F) ⊗ₜ v i

def gLat (V : HSp D) (g : GA D V) : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  (finHom V g).1.mulVec '' (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))

def latG (V : HSp D) (g : GA D V) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v, finVec V v ∈ gLat V g ∧ w = a • v}

def latGHat (V : HSp D) (g : GA D V) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ z ∈ gLat V g,
    w = fun i => ((1 : Af D.host.F) ⊗ₜ a) * z i}

def LatEmb (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  Function.Injective ι ∧ LinearMap.range ι = latG V 1

def LatIsom (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (EF : LinearMap.BilinForm ℤ La)
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  ∃ ε : ℤˣ, ∀ x y, ((EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) *
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))

def ModelW (V : HSp D) {r : ℕ} (hr : V.rank = r) (X : Data D.host.E r) : Prop :=
  X.Gm = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose ∧ X.ξ0 = -D.host.xi0

def IsOrthogonalFrame {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}


open Classical in
def DictLat (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ((∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
        (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → D.host.E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → D.host.E) (relab c σ (e j).1) (e j).2) ∧
      IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)) ∧
    ∀ h : GA D V, ∃ γ ∈ GQ V,
      ((U.X (dict h).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ (dict h).1 (F.t (ik (dict h).1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (γ * h)) * x₀ τ.1

end Dict

structure CoreJ (D : D7) : Type 1 extends Core D where
  cE : ∀ (j : ℕ) (σ : Q.c.F →+* ℂ), (U j σ).Comp → ℂ
  chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle
  x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ
  iota : ∀ j : ℕ, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)

namespace CoreJ

variable {D : D7} (T : CoreJ D)

def phiJ (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ)) (rdU (T.U j σ) f)

theorem phiJ_apply (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D (T.V j σ)) :
    T.phiJ j σ a f g = T.cE j σ (T.dict j σ g).1 * T.toCore.phiAd j σ a f g := by
  have h1 : adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f) g =
      T.mu j σ g * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2 := rfl
  simp only [phiJ, Core.phiAd, Pi.smul_apply, smul_eq_mul, adel_muPin, h1]
  ring

end CoreJ

def halfVec {D : D7} (V : HSp D) (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i => ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) * z i

def KfHalf {D : D7} (V : HSp D) (Kf : Subgroup (GA D V)) (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ ∀ b ∈ Mh, ∀ z ∈ latHat V, ∃ y ∈ latHat V,
    (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = M • y

def AdPin {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (ι₀ : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) : Prop :=
  ∃ (hr : (T.V j σ).rank = D.R.r)
    (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
    (F : FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
      (fun i => relab T.Q.c σ (e i).1))
    (ik : (T.U j σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ)
    (th : ∀ k, ((T.U j σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀
    LatEmb (T.V j σ) ι ∧ LatIsom (T.V j σ) (T.Q.Dw j).EF ι ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictLat (T.U j σ) (T.V j σ) hr (T.dict j σ) ι e F ik φ th x₀

structure LawsJ {D : D7} (T : CoreJ D) : Prop extends LawsM T.toCore where

  cUnit : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (T.cE j σ)

  muVal : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuVal (T.V j σ) (T.chiW j σ) (T.mu j σ)

  muConj : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuConj T.σ₀ σ (T.chiW j T.σ₀) (T.chiW j σ)

  intAll : ∀ j, InR D j → IntAll (T.Q.Xo j) T.Q.c

  modelW : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ hr : (T.V j σ).rank = D.R.r,
    ∀ k, ModelW (T.V j σ) hr ((T.U j σ).X k)

  familyUniformisationBasePointOrthogonal : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (T.x₀ j σ)

  kfHalf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
    KfHalf (T.V j σ) (T.Kf j σ) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))

  adPin : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → AdPin T.toCore j σ (T.x₀ j σ) (T.iota j)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.DIV.Cons
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Top (D : D7) : Type 1 extends Core D where
  G : In66 Q
  nab : ∀ j, NabV (Q.Xo j) Q.c
  dδ : ∀ j n, DeltaDat (Q.Xo j) Q.c n

variable {D : D7}

def badN (D : D7) : ℕ := D.host.QS * D.host.q * D.host.d * ∏ p ∈ D.host.levelPrimes, p

def wEt (D : D7) (j i : ℕ) : WeightFamilies.Wt D j :=
  WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)

structure LawsP (T : Top D) : Prop extends LawsCore T.toCore where

  allTest : ∀ j, InR D j → AllTest (T.Q.Xo j) T.Q.c

  reg : ∀ j, InR D j → regular₂ (T.Q.Xo j) T.Q.c (T.U j)

  datum_condition : T.G.PinDat
  tower : T.G.PinTower
  hasData_condition : T.G.HasData
  points_condition : T.G.PinPts
  lattice_condition : T.G.PinLat
  bc66 : T.G.BaseChange

  datIndep : ∀ j, 1 ≤ j → j < D.R.m → DatIndep (T.Q.Xo j) T.Q.c

  nabPin : ∀ j, InR D j → ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c (T.nab j)

  nabUniq : ∀ j, InR D j → NabUniq (T.Q.Xo j) T.Q.c

  thTot : ∀ j, InR D j → ThValTot (T.Q.Xo j) T.Q.c (T.nab j)
  thCusp : ∀ j, InR D j → ThInCusp (T.Q.Xo j) T.Q.c (T.nab j) (T.cuspA j)
  thNe : ∀ j, 1 ≤ j → j < D.R.m → ThNe0 (T.Q.Xo j) T.Q.c (T.nab j)

  kPsi : ∀ j, InR D j → KPsiIn (Dw := T.Q.Dw j) T.Q.c

structure LawsSh (T : Top D) : Prop where
  beta : ∀ j, InR D j → ∀ n, BetaExists (Dw := T.Q.Dw j) T.Q.c n (badN D)
  dLev : ∀ j, InR D j → ∀ n, (T.dδ j n).IsLev
  dNab : ∀ j, InR D j → ∀ n, ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).nab₂

  dPd : ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ∀ j, InR D j → ∀ n, (T.dδ j n).pd = p

  dPhi : ∀ j, InR D j → ∀ n, D.R.r ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ (T.dδ j n).PhiPin ph ψ x₀ ∧ (T.dδ j n).PsiTie ψ

  dRoot : ∀ j, InR D j → ∀ n, ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls) (δ : Cls →* (T.dδ j n).c₂.Fˣ)
    (gdet : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom) → Cls),
    CMP (T.Q.Xo j) T.Q.c (T.dδ j n) _ Cls δ gdet false
  shTot : ∀ j, InR D j → ∀ a n, Dom a n →
    ShortValTot (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n)
  shCusp : ∀ j, InR D j → ∀ a n, Dom a n → LastPos (T.Q.Dw j) a →
    ShortInCusp (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (T.cuspA j) a n (T.dδ j n)
  shNe : ∀ j, 1 ≤ j → j < D.R.m → ShortNe0 (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (T.dδ j) (T.cuspA j)

def Packet66Rest (Q : Par D) : Prop :=
  ∃ G : In66 Q, G.PinDat ∧ G.PinTower ∧ G.HasData ∧ G.PinPts ∧ G.PinLat ∧ G.BaseChange

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)

theorem gfp_li_tri {K : Type} [Field K] {m n : ℕ} (M : Fin m → Fin m → K) (hdiag : ∀ i, M i i = 1)
    (hlow : ∀ i j, j < i → M i j = 0) (e : Fin m → Fin n → K) (he : LinearIndependent K e) :
    LinearIndependent K (fun i => ∑ j, M i j • e j) := by
  classical
  rw [Fintype.linearIndependent_iff] at he ⊢
  intro g hg
  have hM : (Matrix.of M).det = 1 := by
    rw [Matrix.det_of_upperTriangular (by intro i j h; exact hlow i j h)]
    simp [hdiag]
  have hv : Matrix.vecMul g (Matrix.of M) = 0 := by
    have h0 : ∑ j, (Matrix.vecMul g (Matrix.of M) j) • e j = 0 := by
      rw [← hg]
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      exact Finset.sum_comm
    funext j
    exact he _ h0 j
  intro i
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero (by rw [hM]; exact one_ne_zero) hv) i

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

instance gfpSmooth {L : Type} [Field L] (x : Sp L ⟶ Xo.X) : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := by
  have := Xo.univ.t.semi.smooth
  show Smooth (pullback.snd Xo.univ.t.G.hom x)
  infer_instance

theorem gfp_xGen_over (Z : Comp Xo c) : xGen Z ≫ Xo.s = sOf c (kap Z) := by
  rw [xGen, Category.assoc, pullback.condition, sOf, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← Category.assoc]
  congr 1
  show genSp Z ≫ strK = Spec.map (CommRingCat.ofHom (algebraMap c.F (kap Z)))
  rw [← Spec.map_preimage (genSp Z ≫ strK)]
  rfl

theorem gfp_tower (Z : Comp Xo c) (r : c.F) :
    algebraMap c.F (Om Z) r = algebraMap (kap Z) (Om Z) (algebraMap c.F (kap Z) r) := by rfl

section Gen

variable {L L' : Type} [Field L] [Field L'] [Algebra c.F L] [Algebra c.F L'] [Algebra L L']

theorem gfp_over_bc (htow : ∀ r : c.F, algebraMap c.F L' r = algebraMap L L' (algebraMap c.F L r))
    {x : Sp L ⟶ Xo.X} (hx0 : x ≫ Xo.s = sOf c L) : (spMap (algebraMap L L') ≫ x) ≫ Xo.s = sOf c L' := by
  have h2 : (algebraMap L L').comp (algebraMap c.F L) = algebraMap c.F L' :=
    RingHom.ext fun r => (htow r).symm
  rw [Category.assoc, hx0, sOf, sOf, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← RingHom.comp_assoc, h2]

private theorem li_bc_lemma {K K' : Type} [Field K] [Field K'] [Algebra K K'] {m n : ℕ}
    (d : Fin m → Fin n → K) (hd : LinearIndependent K d) :
    LinearIndependent K' (fun i => algebraMap K K' ∘ d i) := by
  classical
  let A : Matrix (Fin m) (Fin n) K := Matrix.of d
  have hinj : Function.Injective fun v => Matrix.vecMul v A := Matrix.vecMul_injective_iff.2 hd
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.vecMulLinear A)
    (LinearMap.ker_eq_bot.2 hinj)
  have key : ∀ v, Matrix.vecMul v (A * (LinearMap.toMatrix' g).transpose) = v := by
    intro v
    rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
    exact LinearMap.congr_fun hg v
  have hAB : A * (LinearMap.toMatrix' g).transpose = 1 := by
    ext i j
    have := congrFun (key (Pi.single i 1)) j
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm] using this
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hAB' : A.map (algebraMap K K') * ((LinearMap.toMatrix' g).transpose).map (algebraMap K K') = 1 := by
    rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv : Matrix.vecMul w (A.map (algebraMap K K')) = 0 := by
    funext j
    have := congrFun hw j
    simpa [Matrix.vecMul, dotProduct, A, Finset.sum_apply] using this
  have hw' : w = Matrix.vecMul (Matrix.vecMul w (A.map (algebraMap K K')))
      (((LinearMap.toMatrix' g).transpose).map (algebraMap K K')) := by
    rw [Matrix.vecMul_vecMul, hAB', Matrix.vecMul_one]
  intro i
  rw [hw', hv, Matrix.zero_vecMul]
  rfl

theorem gfp_frPt_gen (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (htow : ∀ r : c.F, algebraMap c.F L' r = algebraMap L L' (algebraMap c.F L r))
    (x : Sp L ⟶ Xo.X) (hx0 : x ≫ Xo.s = sOf c L) (M : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → L')
    (hdiag : ∀ τ i, M τ i i = 1) (hlow : ∀ τ i j, j < i → M τ i j = 0) :
    ∃ (y₀ : FrPt Xo c L) (y : FrPt Xo c L'), y₀.x = x ∧ y.x = spMap (algebraMap L L') ≫ x ∧
      ∀ τ i, IsCombAt y.x (fun j => spMap (dualMap (algebraMap L L')) ≫ y₀.u τ j) (M τ i) (y.u τ i) := by
  classical
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  obtain ⟨xc', hx', hvec, htmap⟩ := gfp_bc (L' := L') hx
  let bas : ∀ τ : E →+* ℂ, Module.Basis (Fin (Dw.mult τ)) L (gfpEig (c := c) hx τ) :=
    fun τ => Module.finBasisOfFinrankEq L _ (gfp_finrank hx0 hx τ)
  let d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin n → L := fun τ i => (bas τ i : Fin n → L)
  have hd : ∀ τ, LinearIndependent L (d τ) := fun τ =>
    (bas τ).linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _)
  have hdW : ∀ τ i, d τ i ∈ gfpEig (c := c) hx τ := fun τ i => (bas τ i).2
  let d' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin n → L' := fun τ i => algebraMap L L' ∘ d τ i
  have hd' : ∀ τ, LinearIndependent L' (d' τ) := fun τ => li_bc_lemma (d τ) (hd τ)
  have hdW' : ∀ τ i, d' τ i ∈ gfpEig (c := c) hx' τ := by
    intro τ i
    have h := hdW τ i
    simp only [gfpEig, ReciprocityTheory.ChartRestriction.G.Chart.eigLat, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h ⊢
    intro a
    simp only [d']
    rw [htmap, h a]
    funext k
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [map_mul, htow]
  let e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin n → L' := fun τ i => ∑ j, M τ i j • d' τ j
  have heW : ∀ τ i, e τ i ∈ gfpEig (c := c) hx' τ := fun τ i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hdW' τ j)
  have he : ∀ τ, LinearIndependent L' (e τ) := fun τ => gfp_li_tri (M τ) (hdiag τ) (hlow τ) (d' τ) (hd' τ)
  have hx0' := gfp_over_bc htow hx0
  refine ⟨⟨x, hx0, fun τ i => gfpVec x xc (d τ i), fun τ i => gfp_tan hx _,
      fun τ i => (gfp_eig_iff hx τ _).2 (hdW τ i),
      fun τ w hw hE => gfp_basis hx0 hx τ (d τ) (hd τ) (hdW τ) w hw hE,
      (gfp_gen hT x).choose, (gfp_gen hT x).choose_spec⟩,
    ⟨spMap (algebraMap L L') ≫ x, hx0', fun τ i => gfpVec _ xc' (e τ i), fun τ i => gfp_tan hx' _,
      fun τ i => (gfp_eig_iff hx' τ _).2 (heW τ i),
      fun τ w hw hE => gfp_basis hx0' hx' τ (e τ) (he τ) (heW τ) w hw hE,
      (gfp_gen hT _).choose, (gfp_gen hT _).choose_spec⟩, rfl, rfl, fun τ i => ?_⟩
  have hfun : (fun j => spMap (dualMap (algebraMap L L')) ≫ gfpVec x xc (d τ j)) =
      fun j => gfpVec (spMap (algebraMap L L') ≫ x) xc' (d' τ j) := funext fun j => (hvec _).symm
  have key := (gfp_comb_iff hx' (d' τ) (M τ i) (e τ i)).2 rfl
  rw [← hfun] at key
  exact key

end Gen

theorem genFrEx_of (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) : GenFrEx Xo c := by
  intro Z
  obtain ⟨y₀, y, h0, h1, h2⟩ := gfp_frPt_gen (L := kap Z) (L' := Om Z) hT (gfp_tower Z) (xGen Z)
    (gfp_xGen_over Z) (fun τ => genCoef Z τ) (fun τ i => by simp [genCoef])
    (fun τ i j hji => by simp [genCoef, not_lt.2 hji.le, hji.ne'])
  exact ⟨y, h1, y₀, h0, h2⟩

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.XcLat
noncomputable section

-- Prefer the same-scalar submodule instance for the cuspidal spaces.
attribute [local instance 2000] Submodule.module

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} (T : Core D)

namespace Core

abbrev C (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) := T.cuspA j (wtA w) w.n

abbrev Vs (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Set (T.R j → EReal) :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

def Ns (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ :=
  supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n

def Cu (j : ℕ) : Type := {_cu : FJ.CuF (T.X₀ j) (WeightFamilies.rho D j) // InR D j}

def Xc (j : ℕ) (cu : T.Cu j) : Submodule (𝓞 D.host.E) (Fin (WeightFamilies.rho D j) → D.host.E) :=
  FJ.XcF (T.X₀ j) T.frI cu.1

theorem Xc_lat (j : ℕ) (cu : T.Cu j) : Submodule.IsLattice D.host.E (T.Xc j cu) :=
  FJ.xcLatF (T.X₀ j) T.frI one_ne_zero cu.1

abbrev FJt (j : ℕ) (cu : T.Cu j) (_χ : WeightFamilies.ExpoSet D (T.Xc j cu)) (_w : WeightFamilies.Wt D j) : Type :=
  FJ.FJtF T.σ₀ (T.X₀ j) cu.1

end Core

variable {T} (h : LawsCore T)

namespace LawsCore


open Classical in
def Nl (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ :=
  if hj : InR D j then
    l2C (T.U j) (goodOf T.Q.c σ) (T.V j _) (T.dict j _) (T.mu j _) (xiR D) (wtA w) w.n
      (h.cuspidalL2Subspace j hj _ (goodEmb_goodOf _ σ) _ _ (dom_wtA w))
  else 0

def sg (j : ℕ) (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)) (w : WeightFamilies.Wt D j) :
    T.C j w →ₗ[T.Q.c.F] T.FJt j cu χ w :=
  FJ.sgF T.σ₀ (T.X₀ j) (rdC (T.U j) T.σ₀ (wtA w) w.n)
    (FJ.rdOrbInt_of_latZ T.σ₀ (T.X₀ j) _ (rdC_continuousOn (h.unf j cu.2 T.σ₀ T.good_σ₀) (dom_wtA w)) (h.latZ j cu.2))
    cu.1 χ.1

include h

theorem fd (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) : FiniteDimensional T.Q.c.F (T.C j w) := by
  exact h.cuspFD j hj (wtA w) w.n (dom_wtA w)

theorem hNs (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : IsNormOn (T.C j w) σ (T.Ns j w σ) := by
  apply IsNormOn.of_goodOf
  unfold Core.Ns
  have hσ := goodEmb_goodOf T.Q.c σ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f _
    exact mul_nonneg (lieFac_pos _ _ _).le (supN_nonneg _ _ _)
  · intro f hf h0
    exact h.supDef j hj _ _ (dom_wtA w) _ hσ f hf
      ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne')
  · intro a f _
    unfold supC supN
    rw [map_smulₛₗ, supE_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    ring
  · intro f hf g hg
    unfold supC supN
    rw [← mul_add, map_add (f := _), ← ENNReal.toReal_add (supE_cusp_ne_top hσ hf) (supE_cusp_ne_top hσ hg)]
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ?_ (supE_add_le _ _ _ _)) (lieFac_pos _ _ _).le
    exact ENNReal.add_ne_top.mpr ⟨supE_cusp_ne_top hσ hf, supE_cusp_ne_top hσ hg⟩

theorem hNl (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : IsNormOn (T.C j w) σ (h.Nl j w σ) := by
  rw [Nl, dite_eq_left hj]
  apply IsNormOn.of_goodOf
  let σ' := goodOf T.Q.c σ
  let rd := rdC (T.U j) σ' (wtA w) w.n
  have hσ : GoodEmb T.Q.c σ' := goodEmb_goodOf T.Q.c σ
  have hmem := h.cuspidalL2Subspace j hj σ' hσ (wtA w) w.n (dom_wtA w)
  have hdef := h.l2Def j hj σ' hσ (wtA w) w.n (dom_wtA w)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [l2C, dite_eq_left hf]
    exact mul_nonneg (lieFac_pos _ _ _).le
      (l2Norm_nonneg_bis (T.V j σ') σ' rd (T.dict j σ') (T.mu j σ') hmem ⟨f, hf⟩)
  · intro f hf h0
    rw [l2C, dite_eq_left hf] at h0
    exact congrArg Subtype.val (hdef ⟨f, hf⟩ ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne'))
  · intro a f hf
    rw [l2C, l2C, dite_eq_left hf, dite_eq_left (Submodule.smul_mem _ a hf)]
    have hsmul := l2Norm_smul_alt (T.V j σ') σ' rd (T.dict j σ') (T.mu j σ') hmem a ⟨f, hf⟩
    exact (congrArg (lieFac (T.Q.Dw j) (xiR D) (wtA w) * ·) hsmul).trans (by ac_rfl)
  · intro f hf g hg
    rw [l2C, l2C, l2C, dite_eq_left hf, dite_eq_left hg, dite_eq_left (Submodule.add_mem _ hf hg), ← mul_add]
    exact mul_le_mul_of_nonneg_left
      (L2Norm_add_le (T.V j σ') σ' rd (T.dict j σ') (T.mu j σ') hmem ⟨f, hf⟩ ⟨g, hg⟩)
      (lieFac_pos _ _ _).le

theorem hle (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) :
    ∀ f ∈ T.C j w, h.Nl j w σ f ≤ T.Ns j w σ f := by
  rw [Nl, dite_eq_left hj]
  obtain ⟨_, _, _, hD⟩ := h.dictU j hj _ (goodEmb_goodOf _ σ)
  exact l2C_le_supC _ (goodEmb_goodOf _ σ) _ hD.2.2.2.1 (h.muUnit j hj _ (goodEmb_goodOf _ σ))

theorem mul (j : ℕ) (hj : InR D j) (w w' : WeightFamilies.Wt D j) :
    ∀ f ∈ T.C j w, ∀ g ∈ T.C j w', f * g ∈ T.C j (WeightAlgebra.wadd w w') := by
  intro f hf g hg
  have e := h.cuspMul j hj (wtA w) (wtA w') w.n w'.n f g (dom_wtA w) (dom_wtA w') hf hg
  have e1 : f * g = mulC (T.Q.Xo j) T.Q.c f g := rfl
  have e2 : (WeightAlgebra.wadd w w').n = w.n + w'.n := rfl
  have e3 : wtA (WeightAlgebra.wadd w w') = wtA w + wtA w' := by
    clear e e1 e2 hf hg f g h
    funext x
    simp only [wtA, WeightAlgebra.wadd, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have e4 : ∀ {p : ℕ} (a b : Fin p → ℕ) k, ext0 (fun i => a i + b i) k = ext0 a k + ext0 b k := by
      intro p a b k
      unfold ext0
      split_ifs <;> simp
    simp only [e4]
    split_ifs <;> omega
  show f * g ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA (WeightAlgebra.wadd w w')) (WeightAlgebra.wadd w w').n
  rw [e1, e2, e3]
  exact e

end LawsCore

abbrev recB : WeightFamilies.Prov D :=
  mkB T.Q.eO T.C h.fd T.Vs (fun _ la => isVal_valSet la) T.Ns h.Nl h.hNs h.hNl h.hle T.Cu T.Xc T.Xc_lat T.FJt h.sg

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def BadPin (bad q1 d cond : ℕ) : Prop := 2 ∣ bad ∧ q1 ∣ bad ∧ d ∣ bad ∧ cond ∣ bad

section Reps

variable {n : ℕ} {Tup : Type} (Cl' : Tup → Type)

def RepsCov (dδ : Tup → DeltaDat Xo c n) (bad : Tup → ℕ) (Lh : ∀ t, Cl' t → Submodule (𝓞 E) (Fin n → E))
    (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ) (gam : ∀ t, Cl' t → ℕ) : Prop :=
  ∀ t, RepsOK (l := (dδ t).l₂) (bad t) (La t) (Nc t) (gam t) ∧ LatPin (Lh t) (La t)

end Reps

section Io

variable {n : ℕ} {Ix : Type} [Fintype Ix] (emb : Ix → E →+* c.F) (lam : Ix → DomWeight n)

abbrev VVc : Type := ↥(Formalism.L2.DIV.VV c.F lam)


open Classical in
def rhoM (ga : Matrix (Fin n) (Fin n) E) : VVc c lam →ₗ[c.F] VVc c lam :=
  if h : IsUnit ga.det then Formalism.L2.DIV.rhoVr emb lam (Matrix.nonsingInvUnit ga h) else 0

def nab0M : Submodule (𝓞 c.F) (VVc c lam) := Formalism.L2.DIV.nabAtr emb lam (stdLat E n)

def hwOK (hw : VVc c lam) : Prop :=
  (hw : Formalism.L2.DIV.Pol c.F Ix n) = Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal c.F n (lam τ)

def IoLFRec (a : (E →+* ℂ) × ℕ → ℕ) (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam) : Prop :=
  hwOK c lam hw ∧ ∃ cga : Matrix (Fin n) (Fin n) E → c.F,
    IoLF c a io (rhoM c emb lam) cga (nab0M c emb lam) hw (pG (Dw := Dw) c a n)

end Io

section Dat

variable {n : ℕ}

variable {Tup : Type} (Cl' : Tup → Type)

def WPin (dδ : Tup → DeltaDat Xo c n) (φ : ∀ t, (Fin n → LevQc Dw (dδ t).l₂) → c.F)
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F) : Prop :=
  ∀ t (k : Cl' t) (q : Fin n → LevQ Dw (dδ t).l₂),
    (dδ t).eF (w t k q) = phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q

def CovPin (dδ : Tup → DeltaDat Xo c n) : Prop :=
  ∀ t, (dδ t).IsLev ∧ (dδ t).l₂.A = 1 ∧ ∃ _ : StarRing (𝓞 E), IsNab (dδ t).Xo₂ (dδ t).c₂ (dδ t).nab₂

end Dat

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CompTie
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def OrdTie (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)) (la : HeightOneSpectrum (𝓞 c.F)),
    IsNormDiscrete v → IsOver (K := c.F) v la →
    ∃ y : PtV Xo c cls (PY la) (lies la) la,
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = (((ramIdx (K := c.F) v la : ℤ) : ℝ) : EReal) * vAtV y f

def OrdTieQ (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v → IsTrivOn c.F v →
    ∃ q : QPt Xo c, ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
      (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions

variable {D : D7}

structure LawsPi (T : Core D) (Dd : DepData D.host.E) : Prop where

  page : Dd.Q.g1 = D.host.g 0 ∧ Dd.Q.g2 = D.host.g 1 ∧ Dd.Q.q1 = D.host.q ∧ Dd.Q.dd = D.host.d ∧ Dd.Q.f = D.R.f ∧
    Dd.Q.r = D.R.r
  tPos : TPos Dd

  sm : Dd.Q.sm = D.host.small

  wts : ∀ j, InR D j → (∀ τ, Antitone fun i => Dd.aL j (τ, i)) ∧ 2 * D.R.f * D.R.r ≤ Dd.nW j

  piSplit : PiSplit (H := T.Q.H) Dd
  piHalf : PiHalf T.Q.l Dd

structure LawsDep (T : Core D) [StarRing (𝓞 D.host.E)] : Prop where

  star_eq : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a

  chartEx : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c
  chartIndep : ∀ j, InR D j → ChartIndep (T.Q.Xo j) T.Q.c

def NuFinAt (T : Core D) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)] : Prop :=
  ∀ j, InR D j → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), nuWAt (Xo := T.Q.Xo j) Dd la j ≠ ⊤

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ChiProofs
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Models

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adel_leftInv_of_inv {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (P : FDSec X)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hm : MuUnit V dict mu)
    (hP : ∀ g, ∀ γ' ∈ (X (dict g).1).Γ, P (dict g).1 (lact γ' (dict g).2) = P (dict g).1 (dict g).2) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g := by
  intro γ hγ g
  obtain ⟨γ', hγ', he⟩ := hd γ hγ g
  show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
  rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
  exact congrArg (mu g * ·) (hP g γ' hγ')

theorem adel_leftInv_of_chi {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x)
    (hχ : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g :=
  adel_leftInv_of_inv V dict mu P hd hm fun g γ' hγ' => by
    rw [hΓ _ γ' hγ' _ (hdom g), hχ _ γ' hγ', one_mul]

end Models

section Readings

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def RdInvG (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom,
    rdU U f k (lact γ x) = rdU U f k x

def SecGen (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ k, ∃ b m, Dom b m ∧
    (∃ f ∈ sec Xo c b m, ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0) ∧
    (∃ f ∈ sec Xo c (a + b) (n + m), ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0)

variable (U : Unf Xo c σ r)

theorem rdU_lact (hU : IsUnf U) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n) {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (k : U.Comp) :
    ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, rdU U f k (lact γ x) = (U.X k).χ (laU U a n k) γ * rdU U f k x :=
  (hU.2.2.2.2.1 a n hdn f hf k).2.2

variable {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ)
  (Kf : Subgroup (GA D V)) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)

theorem rdU_leftInv (hU : IsUnf U) (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1) {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu (rdU U f) (γ * g) = adel V dict mu (rdU U f) g :=
  adel_leftInv_of_chi V dict mu (laU U a n) (rdU U f) hd.1 hd.2.2.2.1 hm (rdU_lact U hU hdn hf) hχ

end Readings

namespace Core

variable {D : D7} (T : Core D)

end Core

end Formalism.L2.Pj
end
end
