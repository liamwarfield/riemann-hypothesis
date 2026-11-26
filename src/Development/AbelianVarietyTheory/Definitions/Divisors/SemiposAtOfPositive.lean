module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop
open scoped ENNReal

namespace GlobalTheory.CovHt

def cost {K : Type} [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ) (t : (K →+* ℂ) → ℝ) : ℝ :=
  ((e.sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) + ∑ σ, t σ) / (Module.finrank ℚ K : ℝ)

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7}
  (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def depthOn (Z : Comp Xo c) (G : WTZ E) (v : Rul Xo c → EReal) : EReal := ⨅ w ∈ latOn U Z G, v (w : Rul Xo c)

def smallL (Z : Comp Xo c) (G : WTZ E) (τ : ℕ) (t : ℝ) : Set (cuspOn U Z (τ • G)) :=
  {f | (∀ la, ∀ v ∈ (recVals Xo c).1 la, (τ : EReal) * depthOn U Z G v ≤ v (f : Rul Xo c)) ∧
    ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      ENNReal.ofReal (homN (U σ) x (τ • G) f ⟨y.1, y.2.1⟩) ^ 2 ≤
        ENNReal.ofReal (Real.exp (2 * τ * t)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ τ}

def volL (a : ℕ) (Z : Comp Xo c) (G : WTZ E) (t : ℝ) : ℝ≥0∞ :=
  countVol (dimFlag Dw) (Module.finrank ℚ c.F) a fun τ => (smallL U x V dict Z G τ t).encard

def FinBd (Z : Comp Xo c) (G : WTZ E) (a : ℕ) (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, (∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤) →
    (a : EReal) * depthOn U Z G v ≤ v θ + ((a * e la : ℝ) : EReal)

def NoBase (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, ∀ G' : WTZ E, ∀ f ∈ cuspOn U Z G', v f ≠ ⊤ → ∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤

def InfBd (Z : Comp Xo c) (G G₀ : WTZ E) (a : ℕ) (θ : Rul Xo c) (t : (c.F →+* ℂ) → ℝ) : Prop :=
  (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) ∧
  ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
    ENNReal.ofReal (homN (U σ) x G₀ θ ⟨y.1, y.2.1⟩) ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * a * t σ)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ a

def Carries (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (θ : Rul Xo c) : Prop :=
  θ ∈ secZ Xo c (exOf Dw ((8 : ℤ) • (u - u')) 0) ∧ genVal Z θ ≠ 0 ∧
    ∀ (k : ℕ), ∀ f ∈ cuspOn U Z ((8 * k) • wtOf Dw u' 0), θ ^ k * f ∈ cuspOn U Z ((8 * k) • wtOf Dw u 0)

def Mult (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (cc : ℝ) : Prop :=
  NoBase U Z (wtOf Dw u 0) ∧ ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ),
    Carries U Z u u' θ ∧ FinBd U Z (wtOf Dw u 0) 8 θ e ∧
    InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc

def l1 (u : AllWt.Weight Dw) : ℝ := ∑ τ, ∑ i, |(u τ i : ℝ)|


variable (E) in
def htEx (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) + 40 * ((padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ))


variable (Xo c) in
def HTCmp : Prop := ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal →
  ∀ v ∈ (recVals Xo c).1 la, ∃ w ∈ (htVals Xo c).1 la, ∀ (u : AllWt.Weight Dw), ∀ f ∈ secZ Xo c (exOf Dw u 0),
    w f ≤ v f + (((vLa la (p : c.F) : ℝ) * htEx E p * l1 u : ℝ) : EReal)


variable (l) in
def htCost (B : ℝ) : ℝ := ∑ᶠ p ∈ htPrimes l B, htEx E p * Real.log p

def WtGap (u : AllWt.Weight Dw) (g : ℝ) : Prop :=
  0 < g ∧ (∀ τ, StrictAnti (u τ)) ∧ ∀ τ (a b : Fin (Dw.p + Dw.q)), Dw.p ≤ (a : ℕ) → a ≠ b → g ≤ |(u τ a : ℝ) - u τ b|

def bndB (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  4 * (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (1 + (⨆ k : Psi H × Fin (Dw.p + Dw.q), |(u k.1 k.2 : ℝ)|) / g)

def errX (s : ℝ) (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  (Real.log (bndB u g) + s) * l1 u + (Dw.q : ℝ) * ∑ τ, ((⨆ i, (u τ i : ℝ)) - ⨅ i, (u τ i : ℝ))

def MeanGe (u : AllWt.Weight Dw) (B X : ℝ) : Prop :=
  ∃ sl : Comp Xo c → ℝ, (∀ Z, (sl Z : EReal) ≤ compVolSlope U x 8 (mixVals Xo c B) Z u) ∧
    -X ≤ (∑ᶠ Z, sl Z) / (Nat.card (Comp Xo c) : ℝ)

def MeanAll (s C : ℝ) : Prop := ∀ (u : AllWt.Weight Dw) (g : ℝ), WtGap u g → MeanGe U x u (bndB u g) (C * errX s u g)

end Generic

def ell (D : D7) : ℝ := Real.log D.host.rdE + |dlogL D 1|

section One

open MvPolynomial Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs

variable {D : D7} (Y : ShimX D.what₂.Tau)

def DeRhamMinusHodgeTateGoodPrimesAt : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ Y.lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau Y.N + 1 → ∀ Q : MvPolynomial (Vm D.what₂.Tau Y.N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) m →
    Y.arMix Sx R p ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * collapse D _ Q)) -
        Y.chern (chLie Y.j (k - 1) (Sum.inl τ) * collapse D _ Q) / ((p : ℝ) - 1))

def DeRhamHodgeTateDifferenceKilledAt : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau Y.N) ℝ,
    Y.arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) * (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

end One



section Obj

open GlobalTheory.Mean4 GlobalTheory.Mean4O Formalism.BasicNotions.DV


structure HypothesesH : Prop where
  sieg : GlobalTheory.Published.SiegelToroidalIntegral
  fan : GlobalTheory.Published.ToroidalChartsForFan
  charts : GlobalTheory.Published.ToroidalCharts
  deg : GlobalTheory.Published.ArDegree

end Obj

end GlobalTheory.CovHt

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

def tensφ {S : Scheme.{0}} {B T : Over S} [GrpObj B] {r : ℕ} (x : Fin r → (T ⟶ B)) :
    (Fin r × Fin r) × Fin 4 → (T.left ⟶ B.left) := fun k => GlobalTheory.PolDeg.lamPts (x k.1.1) (x k.1.2) k.2

def tensε {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) : (Fin r × Fin r) × Fin 4 → ℤ := fun k => W k.1.1 k.1.2 * Oε k.2

structure Tens (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) where

  pr : Fin r → (D'.P.A ⟶ D.P.A)
  pr_hom : ∀ i, IsMonHom (pr i)

  lim : IsLimit (Fan.mk D'.P.A pr)

  xe : D'.X ≃+ (Fin r → D.X)
  c_pr : ∀ z i, D'.c z ≫ pr i = D.c (xe z i)

  w : LB.Iso D'.P.L (LB.LinComb D.P.L (tensφ pr) (tensε W))
  w_gen : w.IsGen
  psi : ∀ y z J J', Good D.P.L z J → Good D'.P.L z J' →
    val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
      ∏ i, ∏ j, val (D.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j

def Tens.IsAct {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} (T : Tens D D' W) {O : Type} [CommRing O] [StarRing O]
    [Module O D'.X] (o : D'.OAct O) (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : Prop :=
  letI := D.P.isAb.comm
  (∀ a z i, T.xe (a • z) i = ∑ j, ρ a i j • T.xe z j) ∧ ∀ a i, o.onB.act a ≫ T.pr i = ∏ j, T.pr j ^ ρ a i j

def GalEqN {D : DegPre R} {A : PolAV (Sp (FractionRing R))} (n : ℕ) (lab : Labels D A) : Prop :=
  ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (j : ℕ) (p p' : QkPt D (Kb R) (n ^ j)), QkExt σ.toRingHom p p' →
    (lab (n ^ j) p').left = spMap σ.toRingHom ≫ (lab (n ^ j) p).left

end

abbrev SecK {X Y : Scheme.{0}} (L : LB X) (h : Y ⟶ X) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ)))

def Agree {X Y Y' : Scheme.{0}} (L : LB X) {h : Y ⟶ X} {h' : Y' ⟶ X} {k : ℕ} (s : SecK L h k) (s' : SecK L h' k) : Prop :=
  ∀ (Z : Scheme.{0}) (p : Z ⟶ Y) (p' : Z ⟶ Y'), p ≫ h = p' ≫ h' → ∀ z J, Good L z J → sval s p z J = sval s' p' z J

def TraitReg {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) (L : LB G.left)
    {Y : Scheme.{0}} {α : Y ⟶ G.left} {k : ℕ} (s : SecK L α k) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W')
      (σ : SecK L (pullback.fst G.hom (spMap io ≫ ξ)) k), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ Agree L σ s

structure UCover (R : Type) [CommRing R] [IsDomain R] extends Modif R where

  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  P : GlobalTheory.UU.CP G

  A : PolAV (Sp (FractionRing R))

  α : A.A.left ⟶ G.left
  α_cart : IsGrpPullback A.A G gp α
  α_lb : LBIso A.L (P.L.L.pull α)
  trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ S),
    Function.Injective φ → ξ ≫ π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W' (maximalIdeal W'))
      (A' : PolAV (Sp (FractionRing W'))) (U' : Unif (maximalIdeal W') D' A' G'),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      LBIso U'.LG.L (P.L.L.pull β)

attribute [instance] UCover.grp UCover.comm

structure Secs {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G] (L : LB G.left)
    {A : Scheme.{0}} (α : A ⟶ G.left) where

  N : ℕ

  k : ℕ

  s : Fin (N + 1) → SecK L α k

  θ : SecK L α 1

  Y : Over (Sp (ResidueField R))
  [grp : GrpObj Y]
  smooth : Smooth Y.hom

  j : Y.left ⟶ PSpace R N
  j_over : j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R)
  imm : IsImmersion j

  O : Y.left.Opens
  O_ne : (O : Set Y.left).Nonempty
  trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (β : G'.left ⟶ G.left) (σ : Fin (N + 1) → SecK L β k) (θ' : SecK L β 1)
      (κ : ResidueField R →+* ResidueField W')
      (e : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ)).obj Y),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      κ.comp (residue R) = (residue W').comp (io.comp φ) ∧ IsMonHom e.hom ∧ (∀ i, Agree L (σ i) (s i)) ∧ Agree L θ' θ ∧
      ∀ (Ω : Type) [Field Ω] (p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left) (p' : Sp Ω ⟶ G'.left)
        (y : Sp Ω ⟶ Y.left), p' = p ≫ pullback.fst G'.hom (spMap (residue W')) →
        y = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) →
        (∃ hs, GlobalTheory.ProjSpace.toProj (p' ≫ G'.hom ≫ spMap (io.comp φ)) (fun i => GlobalTheory.secPull (σ i) p') hs = y ≫ j) ∧
        ∀ x : Sp Ω, y x ∈ O → p' x ∈ nonzeroLocus θ'

attribute [instance] Secs.grp

namespace TraitWit

section Tensor
open GlobalTheory.ToricData InhTate
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

end Tensor

section Cover
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

end Cover

section Sections
variable {X Y Y' : Scheme.{0}}

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]


end Sections

end TraitWit

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic

namespace GlobalTheory.Discrepancy

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

abbrev fnPull (s : Y ⟶ X) [IsDominant s] : X.functionFieldˣ →* Y.functionFieldˣ :=
  Units.map (functionFieldMap s).toMonoidHom

def pullCart (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X) : CartierDiv Y :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose

theorem isEqn_pullCart (s : Y ⟶ X) [IsDominant s] {D : CartierDiv X} {y : Y} {g : X.functionFieldˣ}
    (h : D.IsEqn (s y) g) : (pullCart s D).IsEqn y (fnPull s g) :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose_spec.2 y g h

theorem toPic_pullCart (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X) :
    toPic (pullCart s D) = CechPic.pull s (toPic D) :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose_spec.1

theorem pullCart_add (s : Y ⟶ X) [IsDominant s] (D E : CartierDiv X) :
    pullCart s (D + E) = pullCart s D + pullCart s E :=
  CartierDiv.ext_of_isEqn fun y =>
    have ⟨g, hg⟩ := D.exists_isEqn (s y)
    have ⟨g', hg'⟩ := E.exists_isEqn (s y)
    ⟨_, isEqn_pullCart s (hg.add hg'),
      (map_mul (fnPull s) g g').symm ▸ (isEqn_pullCart s hg).add (isEqn_pullCart s hg')⟩

def pullCartHom (s : Y ⟶ X) [IsDominant s] : CartierDiv X →+ CartierDiv Y :=
  AddMonoidHom.mk' (pullCart s) (pullCart_add s)

variable {k : Type} [Field k]

def DivOver.Over {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p) :
    Prop :=
  ∀ f, f ∈ E.ring ↔ functionFieldMap s f ∈ E'.ring

structure IsLogRes (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X)
    (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) : Prop where

  smooth : SmoothOfRelativeDimension n (s ≫ p)

  proj : IsProjOver (s ≫ p)

  bir : Function.Bijective (functionFieldMap s)

  div : IsDivOfForm K (EtaleKlt.ratPull p s n η)

  snc : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)

  supp : (pullCart s G - m • K).supp ≤ B

structure IsLogMult (p : X ⟶ Sp k) (n : ℕ) (Δ : X → ℚ) (η : RatForms p n) (m : ℕ)
    (G : CartierDiv X) : Prop where

  ne_zero : η ≠ 0

  pos : 0 < m

  eqn : ∀ x g, G.IsEqn x g → IsLogEqn p Δ η x m g

theorem IsLogCanonicalMultiple.exists_isLogMult {p : X ⟶ Sp k} {n : ℕ} {Δ : X → ℚ} {m : ℕ}
    {G : CartierDiv X} (h : IsLogCanonicalMultiple p n Δ m G) (hm : 0 < m) :
    ∃ η, IsLogMult p n Δ η m G :=
  have ⟨η, h₁, h₂⟩ := h; ⟨η, h₁, hm, h₂⟩

def InMultAt (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (x : X)
    (u : X.functionFieldˣ) : Prop :=
  ∀ g, G.IsEqn x g → ∀ E : DivOver p, E.Through x → -1 < (E.ord u : ℚ) + discrep E η m g

def IsMultIdeal (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X)
    (J : X.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔
    ∀ (x : X) (hx : x ∈ U.1) (u : X.functionFieldˣ),
      (u : X.functionField) = fnOf U.1 (gen_mem hx) f → InMultAt p n η m G x u

structure IsSncChart [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) (B : Closeds Y) (y : Y)
    (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
    (u : Fin n → Y.functionFieldˣ) : Prop where

  frame : IsFrame (dOn q z)

  val : ∀ j ∈ J, (u j : Y.functionField) = fnOf U (gen_mem hy) (z j)

  spec : ∀ j ∈ J, w j ⤳ y

  coheight : ∀ j ∈ J, Order.coheight (w j) = 1

  inj : Set.InjOn w J

  ord_self : ∀ j ∈ J, Scheme.ord (u j : Y.functionField) (w j) = 1

  ord_other : ∀ j ∈ J, ∀ v, v ⤳ y → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0

  mem : ∀ v, v ⤳ y → Order.coheight v = 1 → (v ∈ B ↔ ∃ j ∈ J, v = w j)

end GlobalTheory.Discrepancy
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R]

def EndData (D : DegPre R) (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) : Prop :=
  IsMonHom a ∧ IsMonHom a' ∧ RosatiAdj D.P.A D.P.L a a' ∧ (∀ y, D.c (h y) = D.c y ≫ a) ∧ (∀ y, D.c (h' y) = D.c y ≫ a') ∧
    D.TauBal a a' h h'

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def FormalEnd (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G) : Prop :=
  (∀ e, IsMonHom (b e)) ∧ (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) ∧
    (∀ e, b e ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a) ∧
    ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X,
      TorusEndOf D.toPre.X h' t ∧ (U.gt e).i ≫ b e = t ≫ (U.gt e).i

def LinEnd (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (b : G ⟶ G) : Prop :=
  IsMonHom b ∧ FormalEnd U a h' fun e => (Over.pullback (thick R I e)).map b

def ExtLam (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB ((Over.pullback (jK R)).obj G).left)
    (PP : LB (G2 G).left) : Prop :=
  PP.IsLB ∧ ∀ κ₂ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left,
    Geo.Tor.IsSquare (G' := (Over.pullback (jK R)).obj G) (G := G) (pullback.fst G.hom (jK R)) κ₂ →
      LBIso (abelian₂ ((Over.pullback (jK R)).obj G) L) (PP.pull κ₂)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD defCoord polydisc)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

abbrev Idx (I : Type) [Fintype I] (n : ℕ) : Type := {ν : I → ℕ // ∑ i, ν i ≤ n + 1}

structure JetRing (R : Type) [CommRing R] (I : Type) [Fintype I] (n : ℕ) where

  B : Type
  [cr : CommRing B]
  [alg : Algebra R B]

  b : Module.Basis (Idx I n) R B

  one : b ⟨0, by simp⟩ = 1

  mul : ∀ ν ν' : Idx I n, b ν * b ν' =
    if h : ∑ i, (ν.1 + ν'.1) i ≤ n + 1 then (∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i)) • b ⟨ν.1 + ν'.1, h⟩ else 0

  π : B →+* R

  π_eq : ∀ x, π x = b.repr x ⟨0, by simp⟩

  κ : DividedPowers (RingHom.ker π)

  nil : IsNilDP κ

attribute [instance] JetRing.cr JetRing.alg

section Alg

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

def admitted (X : Obj F 𝔠 (Sp R)) (N : I → Module.End R (HdR X.A)) : Prop :=
  (∀ i (a : 𝓞 F), Commute (N i) (act (dp0 R) (𝟙 _) X.rm a)) ∧ (∀ i j, N i * N j = 0) ∧
    ∀ (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X.A)), IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ →
      (∀ i x y, ψ (N i x) y + ψ x (N i y) = 0) ∧ ∀ i j x y, ψ (N i x) (N j y) = 0

end Alg

abbrev FR (E : Type) [Field E] : Type := maximalRealSubfield E

section Cx

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)}

structure Unif (φ : I → E →+* ℂ) (L : Set E) (z : I → ℂ) (X : Obj (FR E) 𝔠 (Sp ℂ)) where

  e : Fin (Module.finrank ℚ (FR E)) ≃ I

  c : 𝔠.elt

  pos : IsTotPos (c : FR E)

  u : HolUnif X.A (X.diag c) (Module.finrank ℚ (FR E))

  lat : ∀ w, w ∈ u.Λ ↔ ∃ x ∈ L, w = fun j ↦ defCoord φ z x (e j)

  act : ∀ (a : 𝓞 (FR E)) w, u.ex (fun j ↦ φ (e j) ((a : FR E) : E) * w j) = u.ex w ≫ X.rm.act a

  h : I → ℝ

  ah : ∃ χ, u.IsAH (Matrix.diagonal fun j ↦ (h (e j) : ℂ)) χ

variable {φ : I → E →+* ℂ} {L : Set E} {z : I → ℂ} {X : Obj (FR E) 𝔠 (Sp ℂ)}

def Unif.IsDet (U : Unif φ L z X) (δ : X.DetOmega) (C : ℂ) : Prop :=
  ∀ (v : Fin (Module.finrank ℚ (FR E)) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ),
    (∀ j, U.u.IsDiff (W j) (v j).hom) → δ v = C * W.det

def Unif.IsCMVec (U : Unif φ L z X) (i : I) (y : HdR X.A) (w : ℂ) : Prop :=
  (∀ (a : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) a * w' j) = U.u.ex w' ≫ α) →
    push (dp0 ℂ) (𝟙 _) α y = φ i a • y) ∧
  ∃ v, IsLieImage y v ∧ U.u.IsDiff (Pi.single (U.e.symm i) w) v

structure CxPt (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ) (L : Set E) where

  X : Obj (FR E) 𝔠 (Sp ℂ)

  U : Unif φ L 0 X

  δ : X.DetGen

  C : ℂ

  det : U.IsDet δ.1 C

  ψ : LinearMap.BilinForm ℂ (HdR X.A)

  pol : IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ

  y : I → HdR X.A

  w : I → ℂ

  s : I → ℂ

  cm : ∀ i, U.IsCMVec i (y i) (w i)

def CxPt.low (T : CxPt 𝔠 φ L) (i : I) : Module.End ℂ (HdR T.X.A) :=
  T.s i • (T.ψ.flip (T.y i)).smulRight (T.y i)

def CxPt.A (T : CxPt 𝔠 φ L) (i : I) : ℂ := Real.pi * T.U.h i * T.s i * T.w i ^ 2

def CxPt.IsOver (T : CxPt 𝔠 φ L) {R : Type} [CommRing R] (σ : R →+* ℂ)
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen) (N : I → Module.End R (HdR X₀.A)) : Prop :=
  ∃ (p : T.X.A.left ⟶ X₀.A.left) (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) T.X.A σ (spMap σ) p),
    T.X.IsPullBy X₀ (spMap σ) p ∧ Obj.DetCorr σ p δ₀.1 T.δ.1 ∧
      ∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (T.low i x)

end Cx

def IsEis {F : Type} [Field F] [NumberField F] (𝔞 𝔟 : FracId F) (k : ℕ) (G : ((F →+* ℝ) → ℂ) → ℂ) : Prop :=
  (k ≠ 2 → ∀ z ∈ halfSpace F, HasSum (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z) (G z)) ∧
    (k = 2 → ∃ H, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsContinuation 𝔞 𝔟 H ∧ G = H 0)

def EisExp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : FracId F) (s : ℕ), 1 ≤ s →
    ∃ G, IsEis 𝔞 𝔟 (2 * s) G ∧ DifferentiableOn ℂ G (halfSpace F) ∧ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HasExpansion 𝔞 𝔟 (2 * s) G

def EisFourier : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : FracId F) (k : ℕ), 1 ≤ k → ∀ G,
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : (𝔞 * 𝔟).elt → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧
      HasFourier 𝔞 𝔟 (fun z ↦ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * G z / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k) a ∧
      a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ ∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n

def ModelInt : Prop := AllLat fun E _ _ I _ d φ _ _ 𝔣 Λ l L =>
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsLocalRing R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
      (N : I → Module.End R (HdR X₀.A)) (T : CxPt 𝔠 φ L) (a b : I → ℂ),
      (∀ x ∈ R, Sz l lam 0 x) ∧ (∀ q : ℚ, 0 ≤ padicValRat l q → (q : ℂ) ∈ R) ∧ admitted X₀ N ∧ T.IsOver R.subtype X₀ δ₀ N ∧
      (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ T.A i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
        Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ ∧
        Sz l lam (c_vp 𝔣 l) (b i / (a i * T.A i))) ∧
      Sz l lam (Fintype.card I * c_vp 𝔣 l) (T.C / ∏ i, a i)

def JetInt : Prop := AllLat fun _ _ _ I _ d φ s z 𝔣 Λ l L =>
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
  ∃ a b : I → ℂ, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹) ∧
    ∀ (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), IsDefSum φ (2 * s) L g → (∀ i, u.count i = κ i) →
      Sz l lam ((cE_vp l z : ℝ) + ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l + ((∑ i, κ i : ℕ) : ℝ) * c_vp 𝔣 l)
        (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s)))

end GlobalTheory.LatJet
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

structure Near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (G : Over S) where

  U : Over (Sp R)

  smooth : Smooth U.hom

  separated : IsSeparated U.hom

  quasiCompact : QuasiCompact U.hom

  u : pullback U.hom π ⟶ G.left

  isOpen : IsOpenImmersion u

  u_over : u ≫ G.hom = pullback.snd U.hom π

  all : ∀ g : G.left, π (G.hom g) = closedPoint R → g ∈ Set.range u

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

def Near.Pt (N : Near π G) {T : Scheme.{0}} (s : T ⟶ S) (a : T ⟶ N.U.left) (x : T ⟶ G.left) : Prop :=
  ∃ x₀ : T ⟶ pullback N.U.hom π, x₀ ≫ pullback.fst _ _ = a ∧ x₀ ≫ pullback.snd _ _ = s ∧ x₀ ≫ N.u = x

def Near.Law [GrpObj G] (N : Near π G) : Prop :=
  ∃ (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left),
    (∀ z : (N.U ⊗ N.U).left, (N.U ⊗ N.U).hom z = closedPoint R → z ∈ V) ∧ m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom ∧
    ∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G),
      N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left →
      N.Pt s (v ≫ m) (x * y).left

def Near.Datum [GrpObj G] (N : Near π G)
    (φ : (Over.pullback (pullback.fst π π)).obj G ≅ (Over.pullback (pullback.snd π π)).obj G) : Prop :=
  IsMonHom φ.hom ∧ ∀ (T : Scheme.{0}) (a : T ⟶ N.U.left) (x : T ⟶ ((Over.pullback (pullback.fst π π)).obj G).left),
    N.Pt (x ≫ pullback.snd G.hom (pullback.fst π π) ≫ pullback.fst π π) a (x ≫ pullback.fst G.hom (pullback.fst π π)) →
    N.Pt (x ≫ pullback.snd G.hom (pullback.fst π π) ≫ pullback.snd π π) a
      (x ≫ φ.hom.left ≫ pullback.fst G.hom (pullback.snd π π))

end

def Gal {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') : Subgroup (R' ≃+* R') where
  carrier := {σ | ∀ r, σ (ρ r) = ρ r}
  mul_mem' := fun {a b} ha hb r => by rw [RingAut.mul_apply, hb r, ha r]
  one_mem' := fun _ => rfl
  inv_mem' := fun {a} ha r => by
    have := congrArg a.symm (ha r)
    rw [RingEquiv.symm_apply_apply] at this
    exact this.symm

def Gal.hom {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'} (σ : Gal ρ) : R' →+* R' := σ.1.toRingHom

def PullOver {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {s : R' →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg ρ D D') (h : IsPullDeg s D' D') : Prop :=
  (∀ x, h.xe x = x) ∧ ∀ (b : D'.P.A.left ⟶ D.P.A.left) (c : D'.P.A.left ⟶ D'.P.A.left),
    b = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) → c = h.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) → c ≫ b = b

def IsGal {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') : Prop :=
  Finite (Gal ρ) ∧ ∀ x : R', (∀ σ ∈ Gal ρ, σ x = x) → x ∈ ρ.range

structure GalAct {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R'} (ρ : R →+* R')
    {D : DegPre R} {D' : DegData R' I} (hD : IsPullDeg ρ D D'.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')}
    [GrpObj G'] [IsCommMonObj G'] (U' : Unif I D' A' G') where

  act : Gal ρ → (G'.left ⟶ G'.left)

  cart : ∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)

  act_one : act 1 = 𝟙 _

  act_mul : ∀ σ τ, act (σ * τ) = act σ ≫ act τ

  unif : ∀ σ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre)
    (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
    bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = act σ ∧ IsPullUnif (Gal.hom σ) h bc U' U' ∧ PullOver hD h

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegJoin

open GlobalTheory.Poinc GlobalTheory.PolDeg

variable {g n : ℕ}

def MinAt5 (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) : Prop :=
  ∃ (o' : Type) (_ : CommRing o') (β : cycAway n →+* o') (S' : Scheme.{0}) (s' : S' ⟶ Sp o') (U : S'.Opens)
    (c : U.toScheme ⟶ F.X) (π : S' ⟶ Z) (G : Over S') (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left)
    (_ : IsCommMonObj G) (N : ℕ),
    (IsThetaCompact F z i ∧ IsProjOver z ∧ IsNormalScheme Z ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧ OZ.IsLB ∧ IsAmpleLB OZ) ∧
    (β.Finite ∧ Function.Injective β ∧ IsProjOver s' ∧ IsNormalScheme S' ∧ Dense (U : Set S') ∧ IsFinite c ∧
      Surjective c ∧ U.ι ≫ π = c ≫ i ∧ π ≫ z = s' ≫ spMap β ∧ Surjective π ∧ IsProper π ∧
      IsNoetherian Z) ∧
    (IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
      IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e) ∧
    (1 ≤ N ∧ LBIso (OZ.pull π) (lbPow (hodge G g) N))

theorem MinAt5.isThetaCompact {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {z : Z ⟶ Sp (cycAway n)} {i : F.X ⟶ Z} {OZ : LB Z}
    (h : MinAt5 F z i OZ) : IsThetaCompact F z i ∧ OZ.IsLB ∧ IsAmpleLB OZ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨h₁, -, -, -, -, h₂, h₃⟩, -⟩ := h
  exact ⟨h₁, h₂, h₃⟩

def MinSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    ∃ (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z), MinAt5 F z i OZ

def ChartSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      MinAt5 F z i OZ → BlowAt F z i φ d π j BD →
      SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) ∧ ∀ x : S, PreChart F (π ≫ z) j φ BD d x

def DescSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      BlowAt F z i φ d π j BD → (∀ x : S, PreChart F (π ≫ z) j φ BD d x) →
      ∃ (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
        IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j

end GlobalTheory.SiegJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

section Char

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
  {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']

def EndChar (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G) (m : D.toPre.X →+ D.toPre.X) : Prop :=
  ∀ (κ : Type) [Field κ] (a : R →+* κ) (ha : ∀ x ∈ maximalIdeal R ^ (0 + 1), a x = 0) (G₀ : Over (Sp κ)) [GrpObj G₀]
    (φ : G₀.left ⟶ G.left) (h : IsGrpPullback G₀ G (spMap a) φ) (f₀ : G₀ ⟶ G₀), f₀.left ≫ φ = φ ≫ f.left →
    GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h ≫ f₀ =
      GlobalTheory.SplitTorus.torusMap (Sp κ) m ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h

def CoordMap (D : DegPre R) (D' : DegPre V) (g : R →+* V) (ρ : D.X →+ D'.X) : Prop :=
  ∀ y r r', PsiCoord D y r → PsiCoord D' (ρ y) r' → Associated (g r) r'

def EquivMap (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (β : G'.left ⟶ G.left)
    (ρ : D.toPre.X →+ D'.toPre.X) : Prop :=
  ∀ (f : G ⟶ G) (f' : G' ⟶ G'), IsMonHom f → IsMonHom f' → f'.left ≫ β = β ≫ f.left →
    ∀ m m', EndChar U f m → EndChar U' f' m' → ∀ y, ρ (m y) = m' (ρ y)

end Char

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

def SharpBy (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X)
    (c : SiegPre g n ζ (u ≫ F.s)) (pr : Fin 8 → (P.A ⟶ c.A)) : Prop :=
  SiegPB c F.univ u ∧ (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2))

theorem sharpOver_iff (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X) :
    SharpOver F W P u ↔ ∃ c pr, SharpBy F W P u c pr :=
  ⟨fun ⟨c, h, pr, h'⟩ => ⟨c, pr, h, h'⟩, fun ⟨c, pr, h, h'⟩ => ⟨c, h, pr, h'⟩⟩

def MatEnd {T : Scheme.{0}} {B C : Over T} [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C)) (a b : Fin 8) (f : B ⟶ B) : Prop :=
  IsMonHom f ∧ ∀ w, f ≫ pr w = if w = a then pr b else 1

def MatRel (W : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (a b : Fin 8) (y y' : Fin 8 → X) : Prop :=
  ∀ v, ∑ u, (W + W.transpose) v u • y' u = if v = b then ∑ u, (W + W.transpose) a u • y u else 0

def IsCpl {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] (j : O →+* R) : Prop :=
  ∃ e : AdicCompletion (maximalIdeal O) O ≃+* R, ∀ a, e (algebraMap O _ a) = j a

theorem isCpl_self (O : Type) [CommRing O] [IsLocalRing O] :
    IsCpl (algebraMap O (AdicCompletion (maximalIdeal O) O)) :=
  ⟨RingEquiv.refl _, fun _ => rfl⟩


open Classical in
def MatOn {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {C : Over (Sp S.R)} [GrpObj C] (pr : Fin 8 → (ρ.P.A ⟶ C))
    (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) : Prop :=
  IsMonHom f ∧ ∃ f₁ : ρ.P.A ⟶ ρ.P.A, MatEnd pr a b f₁ ∧
    ((Over.pullback FinalForm.u₀).map f₁).left ≫ FinalForm.φ = FinalForm.φ ≫ f.left

end GlobalTheory.Poinc.Eq8
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

def Factor.Alg {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (F : Factor D D') : Prop :=
  (∃ b : ℕ, 0 < b ∧ Star.star F.e * F.e = b • (Star.star F.e * F.f * F.e)) ∧
    Star.star F.e * F.f * F.e = Star.star F.e * Star.star F.f * F.e ∧ ∃ g : F.O, g * (Star.star F.e * F.f * F.e) = F.e

end GlobalTheory.Mum
end
end
