module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows Matrix
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.SepPer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def eu {n : ℕ} (y : Fin n → ℂ) : ℝ := Real.sqrt (∑ i, ‖y i‖ ^ 2)

def hsn {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2)

section Point

variable (θ : InfFam D) {V : HSp D}

abbrev cmp (τ : D.what₂.Tau) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ := infMat D.sp.cm.sig V.gram (θ τ) g

def nrm (A : Fr V) (x : GA D V) (τ : D.what₂.Tau) (y : Fin V.rank → D.host.E) : ℝ :=
  eu (A.fr τ *ᵥ (cmp θ τ x⁻¹ *ᵥ fun i => tauE D τ (y i)))

def latAt (Λ : Lat V) (x : GA D V) : Lat V :=
  Submodule.span (𝓞 D.host.E) {y | (Lev.finE V x⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈
    Formalism.L2.Herm.hatL (F := D.host.F) Λ}

def Long (A : Fr V) (Λ : Lat V) (x : GA D V) (s : ℝ) : Prop :=
  ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ w ∈ 𝔪 • latAt Λ x, w ≠ 0 →
    s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, nrm θ A x τ w

def Lip (A : Fr V) (φ : GA D V → ℂ) (c : ℝ) : Prop :=
  ∀ x τ, ∀ X ∈ lieAt V τ, ∀ s : ℝ, ‖φ (x * oneP θ V τ X s) - φ x‖ ≤ c * |s| * hsn (A.fr τ * X * (A.fr τ)⁻¹)

variable {S : D.what₂.Tau → SPar} (M : DSModel V S)

def coefR (v a : ∀ τ, M.H τ) (g : GA D V) : ℂ := ∏ τ, ⟪v τ, M.rep τ (cmp θ τ g) (a τ)⟫_ℂ


open Classical in
def coef (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ) (g : GA D V) : ℂ :=
  if Lev.finE V g ∈ K then coefR θ M v a g else 0

def poin (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ) (c : GA D V) (a : ∀ τ, M.H τ) (g : GA D V) : ℂ :=
  ∑' γ : GQ V, coef θ M K v a (c * γ * g)

def DecayAt (τ : D.what₂.Tau) (v a : M.H τ) (N : ℕ) : Prop :=
  ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ‖⟪v, M.rep τ g a⟫_ℂ‖ * (1 + hsn g) ^ N ≤ C

def KDecay (v : ∀ τ, M.H τ) : Prop :=
  ∀ τ, v τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ∧ ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, DecayAt M τ (v τ) a (2 * V.rank ^ 2 + 1)

end Point

section Pack

variable (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1)

def zv : Fin V.rank → D.host.E := fun i => d.a i 0

def Adapted (A : Fr Y) (B : Fr V) : Prop :=
  ∀ τ (y : Fin Y.rank → ℂ) (a : ℂ),
    eu (B.fr τ *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A.fr τ *ᵥ y) ^ 2 + ‖a‖ ^ 2

variable {S S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S') (M : DSModel V S)

structure Pack where

  A : Fr Y

  B : Fr V

  v₀ : ∀ τ, M.H τ

  g₀ : GA D V

  w : M₀.Vec

variable {M₀ M}

def Pack.v (p : Pack M₀ M) : ∀ τ, M.H τ := fun τ => M.rep τ (cmp θ τ p.g₀) (p.v₀ τ)

structure Pack.Base (p : Pack M₀ M) : Prop where

  adapted : Adapted d p.A p.B

  real : p.g₀ ∈ GinfC V

  dec : ∀ τ, p.v₀ τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ∧ DecayAt M τ (p.v₀ τ) (p.v₀ τ) (2 * V.rank ^ 2 + 1)

  ne : ∀ τ, (p.w τ : M₀.H τ) ≠ 0

structure Pack.RealAt (p : Pack M₀ M) (Q : ℝ) (m : Measure (GinfC Y)) (c : ℂ) : Prop where

  ne : c ≠ 0

  act : ∀ b : ∀ τ, M₀.H τ, ∫ h : GinfC Y, coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h) * coefR θ M₀ b (fun τ => p.w τ) h ∂m =
    c * ∏ τ, ⟪b τ, (p.w τ : M₀.H τ)⟫_ℂ

  far : ∀ g : GA D V, Integrable (fun h : GinfC Y => coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d h)) m ∧
    (∫ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d h)‖ ∂m) * (∏ τ, nrm θ p.B g⁻¹ τ (zv d)) ^ (2 * V.rank + 5) ≤
      Real.exp Q * ‖c‖

  lip : ∀ τ, ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    ∫ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (oneP θ Y τ X s * h)) - coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h)‖ ∂m ≤
      Real.exp Q * ‖c‖ * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)

def Pack.Is (p : Pack M₀ M) (Q : ℝ) : Prop :=
  p.Base d ∧ ∀ m : Measure (GinfC Y), m.IsHaarMeasure → ∃ c, p.RealAt θ d Q m c

structure Pack.AdelicAt (p : Pack M₀ M) (Q : ℝ) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)) (ν : Measure (GA D Y)) (φ : GA D Y → ℂ)
    (c : ℂ) : Prop where

  ne : c ≠ 0

  one : ∀ x, ∫ h, coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h) * φ h ∂ν = c * φ x

  term : ∀ (x : GA D Y) (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z →
    Integrable (fun h => coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h)) ν ∧
    (∫ h, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h)‖ ∂ν) *
      (∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ z) ^ (2 * V.rank + 5) ≤ Real.exp Q * ‖c‖ ∧
    (z - zv d ∉ 𝔪 • latAt Λ (stabilizerEmbedding d x) →
      ∀ h, coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h) = 0)

end Pack

def rdisc (D : D7) : ℝ := |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.E)

def loss (D : D7) (C b : ℝ) : ℝ := C * Fintype.card D.what₂.Tau * ((D.R.r : ℝ) + 1) ^ 4 * Real.log b

def Pays (D : D7) (Q N : ℝ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧
    Real.exp Q * ((D.R.r : ℝ) ^ 2 * Fintype.card D.what₂.Tau * (D.host.g 0 * D.host.g 1 : ℕ) * rdisc D * (2 * s) ^ ((1 : ℝ) / D.R.m)) ≤ 1 / 2 ∧
    2 * Real.exp (Q + (6 * ((D.R.r : ℝ) + 1) + 9) * Fintype.card D.what₂.Tau) ≤ s ^ Fintype.card D.what₂.Tau * Real.sqrt N ∧
    1 < s ^ Fintype.card D.what₂.Tau * Real.sqrt N

def PackEx : Prop := ∃ C : ℝ, 0 ≤ C ∧ Ev fun {D} _ _ {sc} {G} W _ => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
  (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), ∃ p : Pack M₀ MP, p.Is W.θ G.sp.dec0 (loss D C sc.b)

def DepthPays : Prop := ∀ C : ℝ, 0 ≤ C → Ev fun {D} _ _ {sc} {G} _ _ => Pays D (loss D C sc.b) (Ideal.absNorm G.modul)

theorem eu_zero {n : ℕ} : eu (0 : Fin n → ℂ) = 0 := by simp [eu]

end GlobalTheory.SepPer

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open scoped TensorProduct

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PairEx : Prop := ∀ (D : D7) (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ),
  (∀ τ, GlobalTheory.PairLift.PairPar (S τ) (S' τ) (aS τ) (aT τ)) → ∀ (V W : HSp D) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω : GlobalTheory.Grid.WRep V W, GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f →
        IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It

def parRow (D : D7) (C : ℝ) (i : ℕ) : D.what₂.Tau → SPar := fun τ => dualPar (Node.par D C (.grid i 0) τ)

def RowModels : Prop := Gap fun {D} _ _ {sc} {G} W _ => ∀ i, i ≤ D.R.m →
  ∃ MV : DSModel (G.V (.grid i 0)) (parRow D sc.cGap i), cart MV = W.cart (.grid i 0)

def RowStep : Prop := Gap fun {D} {T} _ {sc} {G} W M => ∀ i, i < D.R.m → ∀ (S S' : D.what₂.Tau → SPar)
  (MA : DSModel (G.V (.grid i 0)) S) (MB : DSModel (G.V (.grid (i + 1) 0)) S'), S = parRow D sc.cGap i → S' = parRow D sc.cGap (i + 1) →
    cart MA = W.cart (.grid i 0) → cart MB = W.cart (.grid (i + 1) 0) →
    ∃ It : PolF D (G.V (.grid i 0)).rank (G.V (.grid (i + 1) 0)).rank → SmT MA → SmT MB, ∀ F ∈ MultT W.θ MA ∅ 1, ∀ κ : G.CosAt i,
      ∃ F' ∈ MultT W.θ MB ∅ 1, ∀ P v,
        LiftConv W M (.right i 0 : Arrow T) (W.fock (.chi i 0) (W.cosVec i κ) P) (F v) ∧
          liftA W M (.right i 0 : Arrow T) (W.fock (.chi i 0) (W.cosVec i κ) P) (F v) = F' (It P v)

def RowTower : Prop := Gap fun {D} {T} _ {sc} {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ (n : ℕ) (h : n ≤ D.R.m), ∃ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid n 0)) S), S = parRow D sc.cGap n ∧
    cart MB = W.cart (.grid n 0) ∧ ∃ vec : G.RealVec → SmT M₀ → SmT MB, ∀ t ∈ MultT W.θ M₀ ∅ 1, ∀ Φ : G.Datum,
      ∃ F' ∈ MultT W.θ MB ∅ 1, ∀ ρ w,
        PathConv W M (rowPath T 0 n) (rowFam 0 n fun i => W.datum ρ Φ (Fin.castLE h i)) (t w) ∧ part W M ρ Φ (t w) n h = F' (vec ρ w)

def CoefTensor : Prop := ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is →
  ∃ (Wt : D.what₂.Tau → Type) (_ : ∀ τ, AddCommGroup (Wt τ)) (_ : ∀ τ, Module ℂ (Wt τ)) (_ : ∀ τ, FiniteDimensional ℂ (Wt τ))
    (π : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (Wt τ)) (e : (⨂[ℂ] τ, Wt τ) ≃ₗ[ℂ] Module.Dual ℂ c.W),
    (∀ τ, GlobalTheory.RealBessel.IsContIrred (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (π τ)) ∧
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x y : ∀ τ, Wt τ, y τ = π τ g (x τ) → (∀ τ', τ' ≠ τ → y τ' = x τ') →
        e (PiTensorProduct.tprod ℂ y) = e (PiTensorProduct.tprod ℂ x) ∘ₗ c.ρ (atTau θ V τ g)⁻¹

section Sep

variable {D : D7} {V A : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {r : ℕ}
  (F : D.what₂.Tau → Matrix (Fin V.rank) (Fin A.rank) ℂ) (e : D.what₂.Tau → Matrix (Fin V.rank) (Fin r) ℂ)
  (χ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) {Wt : D.what₂.Tau → Type} [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)]
  (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → Module.End ℂ (Wt τ))


open Classical in
def SepBes (β : (∀ τ, Wt τ) → M.Vec → ℂ) : Prop :=
  ∀ τ x v, ∃ b ∈ GlobalTheory.RealBessel.besselForms (gramAt D V τ) (gramAt D A τ) (F τ) (e τ) (χ τ) (M.rep τ) (π τ) (M.sm τ),
    ∀ y u, β (Function.update x τ y) (Function.update v τ u) = b y u

end Sep

def TopFrame : Prop := All fun {D} _ _ _ {G} W _ => ∃ z : D.what₂.Tau → Fin (G.V (.grid D.R.m 0)).rank → ℂ, ∀ τ,
  GlobalTheory.RealBessel.IsFrame (gramAt D (G.V (.grid D.R.m 0)) τ) (gramAt D (G.V (.top 0)) τ)
               ((frameMat _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι).map (tauE D τ)) (G.besTop.e.map (tauE D τ)) (z τ) ∧
    GlobalTheory.RealBessel.IsGeneric (gramAt D (G.V (.grid D.R.m 0)) τ) (G.besTop.e.map (tauE D τ)) (z τ)
      fun u => besChar W.ψ G.besTop (atTau W.θ _ τ u)

def TopSep : Prop := All fun {D} _ _ _ {G} W M => ∀ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid D.R.m 0)) S),
  ∀ F' ∈ MultT W.θ MB ∅ 1, ∀ Ψ ∈ Cols G W.θ,
    (∃ b : Module.Dual ℂ (coefPlus G W.θ).W →ₗ[ℂ] SmT MB →ₗ[ℂ] ℂ, ∀ ξ v, Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v) = b ξ v) ∧
    ∀ (Wt : D.what₂.Tau → Type) [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)]
      (π : ∀ τ, Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ → Module.End ℂ (Wt τ))
      (e : (⨂[ℂ] τ, Wt τ) ≃ₗ[ℂ] Module.Dual ℂ (coefPlus G W.θ).W),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.top 0)) τ), ∀ x y : ∀ τ, Wt τ, y τ = π τ g (x τ) → (∀ τ', τ' ≠ τ → y τ' = x τ') →
        e (PiTensorProduct.tprod ℂ y) = e (PiTensorProduct.tprod ℂ x) ∘ₗ (coefPlus G W.θ).ρ (atTau W.θ _ τ g)⁻¹) →
      SepBes MB (fun τ => (frameMat _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι).map (tauE D τ))
        (fun τ => G.besTop.e.map (tauE D τ)) (fun τ u => besChar W.ψ G.besTop (atTau W.θ _ τ u)) π
        fun x v => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ x)) Ψ) (F' (PiTensorProduct.tprod ℂ v))

def RowConv : Prop := Gap fun {D} _ {L} _ {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ t ∈ Rows L W.θ M₀, ∀ w ρ ξ, ∀ Ψ ∈ Cols G W.θ, ∀ Φ, FConv W M ρ ξ Ψ Φ (t w)

def GoodRows : Prop := ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ t ∈ R.EEat R.triv,
    PiTensorProduct.lift t ∈ Rows R.toLevCh R.θ (R.MY 0)

theorem parRow_zero (D : D7) (C : ℝ) : parRow D C 0 = parB (Ptw D) 0 :=
  funext fun τ => congrArg dualPar (parV_zero D C (Nat.zero_le _) τ)

end GlobalTheory.SepRows

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open scoped TensorProduct nonZeroDivisors ComplexConjugate
open GlobalTheory.SepRows GlobalTheory.EvenOnto
open GlobalTheory.Chain (IsVacVec ptOf)
open GlobalTheory.PairLift (adjO)

namespace GlobalTheory.CoreOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure ReLat (V : HSp D) where

  L0 : Submodule (𝓞 D.host.E) V.V
  lat : Submodule.IsLattice D.host.E L0
  unimod : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L0

@[reducible] def ReLat.sp {V : HSp D} (r : ReLat V) : HSp D := { V with L0 := r.L0, standardTuple_isLattice := r.lat, baseLattice_isUnimodular := r.unimod }

@[reducible] def ReLat.mod {V : HSp D} (r : ReLat V) {S : D.what₂.Tau → SPar} (M : DSModel V S) : DSModel r.sp S where
  H := M.H
  σ := M.σ
  lam := M.lam
  ε := M.ε
  fr := M.fr
  enum := M.enum
  ds := M.ds
  fr_unit := M.fr_unit
  fr_gram := M.fr_gram

def scaleLat {n : ℕ} (𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {y | ∃ a ∈ 𝔟, ∃ x ∈ Λ, y = a • x}

def exch (A B : HSp D) (f : WO A B → ℂ) : WO (negSp B) A → ℂ := fun x => f (adjO A B x)

def Exch {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D (negSp B) × GA D A →* Module.End ℂ (WO (negSp B) A → ℂ))
    (ω' : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ A B f → ∀ g h, ω (negGA B h, g) (exch A B f) = exch A B (ω' (g, h) f)

def ExchLaw (D : D7) : Prop := ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), IsStdChar D ψ (-1) →
  (∀ f, IsThetaFunO ψ A B f ↔ IsThetaFunO ψ (negSp B) A (exch A B f)) ∧
  (∀ x f, heisO ψ (negSp B) A x (exch A B f) = exch A B (heisO ψ A B (adjO A B x) f)) ∧
  (∀ x x' : WO (negSp B) A, symplO (negSp B) A x x' = symplO A B (adjO A B x) (adjO A B x')) ∧
  Function.Bijective (adjO A B) ∧
  (∀ m X, IsCovolOne (ratL B A) m X → ∃ m' X', IsCovolOne (ratL A (negSp B)) m' X' ∧
    ∀ f f' : WO A B → ℂ, ∫ w in X, f w * conj (f' w) ∂m = ∫ w in X', exch A B f w * conj (exch A B f' w) ∂m') ∧
  ∀ χS χT ω, IsWeilDatumO ψ (negSp B) A χS χT ω → ∃ ω', IsWeilDatumO ψ A B χT⁻¹ χS⁻¹ ω' ∧ Exch ψ ω ω'

def ReLatLaw (D : D7) : Prop :=
  (∀ (V : HSp D) Λ, IsSelfDualC V Λ → ∃ r : ReLat V, GlobalTheory.AdelicU.frameLat r.sp = Λ) ∧
  (∀ (V : HSp D) (r : ReLat V) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)),
    (MultT θ (r.mod M) J 1 : Submodule ℂ (SmT M →ₗ[ℂ] (GA D V → ℂ))) = MultT θ M J 1 ∧
    (KF (r.mod M) : Submodule ℂ (SmT M)) = KF M ∧ cart (r.mod M) = cart M ∧
    GlobalTheory.Cusp.wittIndex r.sp = GlobalTheory.Cusp.wittIndex V ∧ ∀ F : GA D V → ℂ, RapidDec r.sp F ↔ RapidDec V F) ∧
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (r : ReLat A) (r' : ReLat B),
    (∀ f : WO A B → ℂ, IsThetaFunO ψ r.sp r'.sp f ↔ IsThetaFunO ψ A B f) ∧
    ∀ χS χT (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)),
      IsWeilDatumO ψ r.sp r'.sp χS χT ω ↔ IsWeilDatumO ψ A B χS χT ω

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

def gridCom : Com D where
  θ := W.θ
  ψ := W.ψ
  S := G.pl.S0
  n := nRk D
  t := sLen D - 1
  m := D.R.m
  χ := fun k => (G.ch.chi (D.R.m - k))⁻¹
  a := fun k τ => -(cen D sc.cGap τ (D.R.m - k) : ℚ)


variable (G) in
def IsCoreLat (i : ℕ) (r : ReLat (G.V (.core i))) : Prop :=
  GlobalTheory.AdelicU.frameLat r.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) (G.Λ (.core i))


variable (G) in
@[reducible] def gridStage (v : CoreVol G) (i : ℕ) (r : ReLat (G.V (.core i)))
    (M : DSModel (G.V (.core i)) (Node.par D sc.cGap (.core i))) : PiLocalization₂ D where
  V := r.sp
  par := Node.par D sc.cGap (.core i)
  M := r.mod M
  J := lev G (.core i)
  ν := (v i).μ
  fd := (v i).𝓕


variable (G) in
def IsOntoMod (i : ℕ) (x₀ : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core (i + 1))).rank) D.host.E) : Prop :=
  x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)) ∧ ∃ y₀ ∈ homLat (G.Λ (.core i)) (G.Λ (.core (i + 1))),
    x₀ * y₀ - 1 ∈ G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i))

def CosLaw (i : ℕ) (x₀ : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core (i + 1))).rank) D.host.E)
    (Φ : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ) : Prop :=
  Dep W (.core i) Φ ∧ ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
    (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
    heisO W.ψ _ _ y Φ = W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) • Φ

def Below (v : CoreVol G) (k : ℕ) (F : Fn G (.core k)) : Set (Fn G (.core 0)) :=
  {F₀ | ∃ Ψ : ∀ i, Fn G (.core i), (∀ i, i ≤ k → RapidDec (G.V (.core i)) (Ψ i)) ∧
    (∀ i, i < k → ∃ f : Sch G (.coreDown i), Dep W (.core i) f ∧ Ψ i = dn W v i f (Ψ (i + 1))) ∧ Ψ 0 = F₀ ∧ Ψ k = F}

def ComOK : Prop := Gap fun {_} _ _ _ _ W _ => (gridCom W).Is

def StageOK : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i ≤ D.R.m → (∃ r, IsCoreLat G i r) ∧
  ∀ r, IsCoreLat G i r → ∀ v M, (gridStage G v i r M).Is (gridCom W) i

def ParOK : Prop := ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ i, i < D.R.m → ∀ τ,
  UpPair (sLen D - 1) (Node.par D 1 (.core i) τ) (Node.par D 1 (.core (i + 1)) τ) (-(cen D 1 τ (D.R.m - i) : ℚ))
    (-(cen D 1 τ (D.R.m - i) : ℚ))

def OntoModEx : Prop := All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∃ x₀, IsOntoMod G i x₀

def LatExch : Prop := All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' →
  ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (x : WO (G.pS (.core i)) (G.pT (.core i))),
    x ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (T := _) (.core i) : Set _) (G.latT (.core i) : Set _) P ↔
      adjO (G.V (.core i)) (G.V (.core (i + 1))) x ∈
        latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) P

def DatumEx : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' →
  ∀ (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'), ∀ x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)),
    ∃ f, IsVacVec W.ψ W.θ M M' f ∧
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff W.ψ r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp) (GlobalTheory.AdelicU.frameLat r'.sp) G.pl.S0 f ∧
      ∀ φ, CosLaw W i x₀ (exch (G.V (.core i)) (G.V (.core (i + 1))) (ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ M M' f φ))

def CosSupp : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ Φ, CosLaw W i x₀ Φ →
  ∀ m X, IsCovolOne (ratL (G.pT (.core i)) (G.pS (.core i))) m X → ∀ g : GA D (G.V (.core i)),
    (∀ v ∉ G.pl.S0, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram v g ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (G.Λ (.core i)) v) →
    (∫ w in X, W.om (.core i) (1, g) Φ w * conj (Φ w) ∂m) ≠ 0 → Lev.finE (G.V (.core i)) g ∈ G.levCong (.core i)

def PreOK : Prop := Gap fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ v M M',
  ∃ ω f, PreStep (gridCom W) i (gridStage G v i r M) (gridStage G v (i + 1) r' M') ω f ∧ Exch W.ψ (W.om (.core i)) ω ∧
    ∀ φ, Dep W (.core i) (exch (G.V (.core i)) (G.V (.core (i + 1))) (ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ))

def ChainEx : Prop := Gap fun {D} _ _ _ {G} W _ => ∀ v r₀ M₀, IsCoreLat G 0 r₀ → ∀ k, k ≤ D.R.m → ∃ r M, IsCoreLat G k r ∧
  ∃ Θ, GlobalTheory.EvenOnto.Reach (gridCom W) (gridStage G v 0 r₀ M₀) k (gridStage G v k r M) Θ ∧
    ∀ y, ∀ x ∈ (gridStage G v 0 r₀ M₀).KF, PiLocalization₂.val (Θ y) x ∈
      Submodule.span ℂ {F₀ : Fn G (.core 0) | ∃ w, F₀ ∈ Below W v k (PiLocalization₂.val y w)}

def TopCols : Prop := All fun {D} _ _ {sc} {G} W _ =>
  ∀ M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)), ∀ y ∈ CoreForms G W.θ D.R.m M, ∀ w,
    ∃ c ∈ Cols G W.θ, ∃ ξ : Module.Dual ℂ (coefPlus G W.θ).W, y w = pairVec (coefPlus G W.θ) ξ c

end GlobalTheory.CoreOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Asc

variable {D : D7}

def VacG (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Γ : AddSubgroup (WO S T)) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) Γ f

def Ann (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Γ : AddSubgroup (WO S T)) : Set (WO S T) :=
  {w | (∀ u ∈ Γ, ψ (symplO S T w (2 • u)) = 1) ∧ ∀ e, IsSplitIdem D e → ∀ u ∈ Γ, IsHalf e u → ψ (symplO S T w u) = 1}

structure Tame (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ) : Prop where
  add : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ℓ (f + f') = ℓ f + ℓ f'
  smul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f
  cont : ∀ f, IsThetaFunO ψ S T f → Continuous fun w => ℓ (heisO ψ S T w f)
  bdd : ∀ f, IsThetaFunO ψ S T f → ∃ C : ℝ, ∀ w, ‖ℓ (heisO ψ S T w f)‖ ≤ C
  sup : ∀ f, IsThetaFunO ψ S T f → ∀ (m : Measure (WO S T)) [SFinite m] (α : WO S T → ℂ), Integrable α m →
    IsThetaFunO ψ S T (fun x => ∫ w, α w * heisO ψ S T w f x ∂m) →
      ℓ (fun x => ∫ w, α w * heisO ψ S T w f x ∂m) = ∫ w, α w * ℓ (heisO ψ S T w f) ∂m

structure BesL (D : D7) (ρ : ℕ) where
  V : HSp D
  V₀ : HSp D
  A : HSp D
  L : HSp D
  d : HypDec V V₀ ρ
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  vA : GlobalTheory.Unf.Vol A
  vN : VolN d

structure JacL (D : D7) (ρ : ℕ) where
  W : HSp D
  W₀ : HSp D
  d : HypDec W W₀ ρ
  v0 : GlobalTheory.Unf.Vol W₀
  vN : VolN d

variable {ψ : AddChar (AF D.host.F) ℂ}

def BesL.per {ρ : ℕ} (B : BesL D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) : ℂ :=
  besPer ψ 1 B.d B.o B.ζ B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 φ f

def JacL.per {ρ : ℕ} (J : JacL D ρ) (ψ : AddChar (AF D.host.F) ℂ) {L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (omz : Om J.W₀ L')
    (φ : GA D J.W₀ → ℂ) (f : GA D J.W → ℂ) (Φ₀ : WO J.W₀ L' → ℂ) : ℂ :=
  fjSrc ψ J.d ζ' omz J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 φ f Φ₀

def JacL.perAll {ρ : ℕ} (J : JacL D ρ) (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (B : BesL D σ) (om₀ : Om B.V₀ J.W₀)
    (φ : GA D B.A → ℂ) (G' : GA D J.W → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) : ℂ :=
  fjAll ψ J.d B.o B.ζ om₀ B.vA.μ B.vA.𝓕 J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 φ G' Ξ

abbrev StBF (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (B : BesL D ρ) (J : JacL D ρ) := Step ψ B.V B.V₀ J.W J.W₀ ρ ρ

abbrev StFB (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (J : JacL D (σ + 1)) (B : BesL D σ) := Step ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ

def flatS {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ) : WO V₀ W₀ → ℂ :=
  flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν x y Ψ

abbrev flBF {ρ : ℕ} {B : BesL D ρ} {J : JacL D ρ} (s : StBF ψ B J) : (WO B.V J.W → ℂ) → WO B.V₀ J.W₀ → ℂ :=
  flatS B.d J.d s (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ))

abbrev flFB {σ : ℕ} {J : JacL D (σ + 1)} {B : BesL D σ} (s : StFB ψ J B) : (WO J.W B.V → ℂ) → WO J.W₀ B.V₀ → ℂ :=
  flatS J.d B.d s (xLast B.d (vecB B.o B.ζ)) 0

def handP {σ : ℕ} {J : JacL D (σ + 1)} {B : BesL D σ} (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L)
    (φ : GA D J.W₀ → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ) : GA D B.A → ℂ :=
  fun h₁ => ∫ h₀ in J.v0.𝓕, φ h₀ *
    contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ) (omz (h₀, 1) Φ₀) 0 ∂J.v0.μ

structure Lnk (L : HSp D) (ζ : Fin L.rank → D.host.E) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) where
  τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E
  map : τ *ᵥ ζ' = -ζ
  norm : star ζ ⬝ᵥ L.gram *ᵥ ζ = D.host.xi0 * star D.host.xi0 * (star ζ' ⬝ᵥ L'.gram *ᵥ ζ')

def Lnk.κ {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (l : Lnk L ζ L' ζ') (S : HSp D)
    (w : WO S L') : WO L S :=
  GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat l.τ : Mx D L.rank L'.rank) ⬝ w)

structure Loc {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (𝒮 : Set (WO V W → ℂ)) (Γ₀ : AddSubgroup (WO V₀ W₀)) (K : Subgroup (GA D W)) : Prop where
  theta : ∀ Φ ∈ 𝒮, IsThetaFunO ψ V W Φ
  real : ∀ Φ ∈ 𝒮, ∀ w : WO V W, w.map (finPart D) = 0 → heisO ψ V W w Φ ∈ 𝒮
  core : ∀ Φ ∈ 𝒮, ∀ w ∈ Ann ψ V₀ W₀ Γ₀, heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Φ ∈ 𝒮
  vac : ∀ Φ ∈ 𝒮, VacG ψ V₀ W₀ Γ₀ (flatS dV dW s x y Φ)
  fin : K ≤ GfC W
  cpt : IsCompact (K : Set (GA D W))
  opn : IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W))
  fix : ∀ Φ ∈ 𝒮, ∀ k ∈ K, s.om (1, k) Φ = Φ
  supp : ∀ Φ ∈ 𝒮, ∀ h, flatS dV dW s x y (s.om (1, h) Φ) ≠ 0 → ∃ r ∈ Rgrp W x, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k
  ne : ∃ Φ ∈ 𝒮, flatS dV dW s x y Φ ≠ 0

def Irr (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Γ : AddSubgroup (WO S T)) (ℓ : (WO S T → ℂ) → ℂ),
    Tame ψ S T ℓ → ∀ f₀, VacG ψ S T Γ f₀ → f₀ ≠ 0 → (∀ w ∈ Ann ψ S T Γ, ℓ (heisO ψ S T w f₀) = 0) → ∀ f, VacG ψ S T Γ f → ℓ f = 0

def VanBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J) 𝒮 Γ₀ K,
    Loc B.d J.d s (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) 𝒮 Γ₀ K → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ),
    RapidDec B.A φ → RapidDec J.W G → (∀ k ∈ K, ∀ g, G (g * k) = G g) → (∀ Φ ∈ 𝒮, B.per ψ φ (s.lift G Φ) = 0) →
      ∀ Φ ∈ 𝒮, J.perAll ψ B s.om₀ φ G (flBF s Φ) = 0

def VanFB (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) 𝒮 Γ₀ K,
    Loc J.d B.d s (xLast B.d (vecB B.o B.ζ)) 0 𝒮 Γ₀ K → ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle)
    (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ),
    RapidDec J.W₀ φ → RapidDec B.V G → IsThetaFunO ψ J.W₀ B.L Φ₀ → (∀ k ∈ K, ∀ g, G (g * k) = G g) →
    (∀ Φ ∈ 𝒮, J.per ψ B.ζ omz φ (s.lift G Φ) Φ₀ = 0) → ∀ Φ ∈ 𝒮, B.per ψ (handP s vL omz φ Φ₀ (flFB s Φ)) G = 0

def UpBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J) 𝒮 Γ₀ K,
    Loc B.d J.d s (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) 𝒮 Γ₀ K →
    ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Lnk B.L B.ζ L' ζ') (χA χz χ' : (AE D)ˣ →* Circle)
    (oma : Om B.A J.W₀) (omz : Om J.W₀ L'), s.χV = χA * χz → IsWeilDatumO ψ B.A J.W₀ χA s.χW oma →
    IsWeilDatumO ψ J.W₀ L' χ' χz omz → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ), RapidDec B.A φ → RapidDec J.W G →
    (∀ k ∈ K, ∀ g, G (g * k) = G g) → ∀ (Ξ₁ : WO B.A J.W₀ → ℂ) (Ξ₂ : WO B.L J.W₀ → ℂ), IsThetaFunO ψ B.A J.W₀ Ξ₁ →
    IsThetaFunO ψ B.L J.W₀ Ξ₂ → VacG ψ B.V₀ J.W₀ Γ₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) →
    J.per ψ ζ' omz (liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁) G (fun w => star (Ξ₂ (l.κ J.W₀ w))) ≠ 0 →
      ∃ Φ ∈ 𝒮, B.per ψ φ (s.lift G Φ) ≠ 0

def UpFB (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) 𝒮 Γ₀ K,
    Loc J.d B.d s (xLast B.d (vecB B.o B.ζ)) 0 𝒮 Γ₀ K → ∀ (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L),
    s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ), RapidDec J.W₀ φ → RapidDec B.V G → (∀ k ∈ K, ∀ g, G (g * k) = G g) →
    ∀ (Ξ₁ : WO J.W₀ B.A → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ), IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ₀ → Φ₀ ≠ 0 →
    VacG ψ J.W₀ B.V₀ Γ₀ (B.o.boxT J.W₀ Ξ₁ Φ₀) → B.per ψ (liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁) G ≠ 0 →
      ∃ Φ ∈ 𝒮, J.per ψ B.ζ omz φ (s.lift G Φ) Φ₀ ≠ 0

structure LastLat (ψ : AddChar (AF D.host.F) ℂ) (J : JacL D 0) {X T L'' : HSp D} (o : OrthDec X T L'') (Γ : AddSubgroup (WO J.W T))
    (ΓL : AddSubgroup (WO J.W₀ (negSp L''))) (ΓX : AddSubgroup (WO J.W₀ X)) : Prop where
  ann : ∀ w ∈ Ann ψ J.W₀ X ΓX, J.d.ext0 T (o.resT J.W₀ w).1 ∈ Ann ψ J.W T Γ ∧ (o.resT J.W₀ w).2 ∈ Ann ψ J.W₀ (negSp L'') ΓL
  ex : ∃ f₁ f₂, VacG ψ J.W T Γ f₁ ∧ VacG ψ J.W₀ (negSp L'') ΓL f₂ ∧ f₁ ≠ 0 ∧ f₂ ≠ 0 ∧
    VacG ψ J.W₀ X ΓX (o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (star f₂))

def UpLast (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (J : JacL D 0) (X T L'' : HSp D) (o : OrthDec X T L'') Γ ΓL ΓX, L''.rank = 1 →
    LastLat ψ J o Γ ΓL ΓX → ∀ (ζ' : Fin (negSp L'').rank → D.host.E) (χS χT χz : (AE D)ˣ →* Circle) (om : Om J.W T) (omX : Om J.W₀ X)
    (omz : Om J.W₀ (negSp L'')), IsWeilDatumO ψ J.W T χS χT om → IsWeilDatumO ψ J.W₀ X χS (χT * χz⁻¹) omX →
    IsWeilDatumO ψ J.W₀ (negSp L'') χS⁻¹ χz omz → ∀ (vT : GlobalTheory.Unf.Vol T) (φ : GA D J.W₀ → ℂ) (u : GA D T → ℂ),
    RapidDec J.W₀ φ → RapidDec T u → ∀ Ξ, VacG ψ J.W₀ X ΓX Ξ →
    (∫ h in vT.𝓕, liftT omX J.v0.μ J.v0.𝓕 φ Ξ (o.emb (h, 1)) * u h ∂vT.μ) ≠ 0 →
      ∃ Φ Φ₀, VacG ψ J.W T Γ Φ ∧ VacG ψ J.W₀ (negSp L'') ΓL Φ₀ ∧ J.per ψ ζ' omz φ (liftS om vT.μ vT.𝓕 u Φ) Φ₀ ≠ 0

def cjOm {S T : HSp D} (om : Om (negSp S) T) : Om S T :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd (Equiv.refl (WO S T))).comp (om.comp ((negGA S).toMonoidHom.prodMap (MonoidHom.id _)))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

abbrev omRow (W : G.Weil) (i : ℕ) : Om (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) := cjOm (W.om (.chi i 0))

abbrev omCore (W : G.Weil) (i : ℕ) : Om (G.V (.core (i + 1))) (G.V (.core i)) := cjOm (W.om (.core i))


variable (G) in
abbrev latRow (i : ℕ) : AddSubgroup (WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))) := depLat G (.chi i 0)


variable (G) in
abbrev latCore (i : ℕ) : AddSubgroup (WO (G.V (.core (i + 1))) (G.V (.core i))) := depLat G (.core i)


set_option genSizeOfSpec false in
set_option genInjectivity false in
variable (G) in
structure Frames where
  Lz : HSp D
  rk : Lz.rank = 1
  oz : OrthDec (G.V (.core 0)) (Yc D 0) Lz
  ζ : ℕ → Fin (negSp Lz).rank → D.host.E
  line : ∀ ρ, IsLineVec (negSp Lz) (ζ ρ)
  lnk : ∀ ρ, Lnk (negSp Lz) (ζ (ρ + 1)) (negSp Lz) (ζ ρ)
  V₀ : ℕ → HSp D
  dB : ∀ ρ, 2 * ρ + 2 ≤ D.R.m → HypDec (G.V (.grid (2 * ρ + 2) 0)) (V₀ ρ) ρ
  oB : ∀ ρ, 2 * ρ + 2 ≤ D.R.m → OrthDec (V₀ ρ) (G.V (.core (2 * ρ + 2))) (negSp Lz)
  nB : ∀ ρ h, VolN (dB ρ h)
  dJ : ∀ ρ, 2 * ρ + 2 ≤ D.R.m → HypDec (G.V (.grid (2 * ρ + 1) 0)) (G.V (.core (2 * ρ + 1))) ρ
  nJ : ∀ ρ h, VolN (dJ ρ h)

namespace Frames

variable (F : Frames G) (v : CoreVol G)

abbrev bes (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : BesL D ρ :=
  ⟨_, _, _, _, F.dB ρ h, F.oB ρ h, F.ζ (ρ + 1), F.line (ρ + 1), v (2 * ρ + 2), F.nB ρ h⟩

abbrev jac (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : JacL D ρ := ⟨_, _, F.dJ ρ h, v (2 * ρ + 1), F.nJ ρ h⟩

structure Ends (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) : Prop where
  bot : ∀ h, F.oz.emb (h, 1) = stabilizerEmbedding G.sp.dec0 h
  top : ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), 2 * ρ + 2 = D.R.m → ∀ (φ : ∀ i, Fn G (.core i)) (f : ∀ i, Fn G (.grid i 0)),
    RapidDec _ (φ D.R.m) → RapidDec _ (f D.R.m) → (F.bes v ρ h).per W.ψ (star (φ (2 * ρ + 2))) (star (f (2 * ρ + 2))) ≠ 0 →
      Bplus W M (φ D.R.m) (f D.R.m) ≠ 0

structure Good (W : G.Weil) (ΓL : ∀ ρ, AddSubgroup (WO (G.V (.core (2 * ρ + 1))) (negSp F.Lz))) : Prop where
  bf : ∀ ρ h (s : StBF W.ψ (F.bes v ρ h) (F.jac v ρ h)), s.om = omRow W (2 * ρ + 1) → ∃ 𝒮 Γ₀,
    Loc (F.dB ρ h) (F.dJ ρ h) s (xZero (F.dJ ρ h)) (yZero _ ρ (vecB (F.oB ρ h) (F.ζ (ρ + 1)))) 𝒮 Γ₀ (lev G (.grid (2 * ρ + 1) 0)) ∧
    (∀ Φ ∈ 𝒮, VacG W.ψ _ _ (latRow G (2 * ρ + 1)) Φ) ∧
    ∀ Ξ₁ Ξ₂, VacG W.ψ _ _ (latCore G (2 * ρ + 1)) Ξ₁ → IsThetaFunO W.ψ _ _ Ξ₂ →
      VacG W.ψ _ _ (ΓL ρ) (fun w => star (Ξ₂ ((F.lnk ρ).κ _ w))) → VacG W.ψ _ _ Γ₀ ((F.oB ρ h).boxS _ Ξ₁ Ξ₂)
  fb : ∀ σ h h' (s : StFB W.ψ (F.jac v (σ + 1) h) (F.bes v σ h')), s.om = omRow W (2 * σ + 2) → ∃ 𝒮 Γ₀,
    Loc (F.dJ (σ + 1) h) (F.dB σ h') s (xLast (F.dB σ h') (vecB (F.oB σ h') (F.ζ (σ + 1)))) 0 𝒮 Γ₀ (lev G (.grid (2 * σ + 2) 0)) ∧
    (∀ Φ ∈ 𝒮, VacG W.ψ _ _ (latRow G (2 * σ + 2)) Φ) ∧
    ∀ Ξ₁ Φ₀, VacG W.ψ _ _ (latCore G (2 * σ + 2)) Ξ₁ → VacG W.ψ _ _ (ΓL (σ + 1)) Φ₀ → VacG W.ψ _ _ Γ₀ ((F.oB σ h').boxT _ Ξ₁ Φ₀)
  lineNe : ∀ ρ, 2 * ρ + 2 ≤ D.R.m → ∃ Φ₀, VacG W.ψ _ _ (ΓL ρ) Φ₀ ∧ Φ₀ ≠ 0
  last : ∀ h, LastLat W.ψ (F.jac v 0 h) F.oz (latRow G 0) (ΓL 0) (latCore G 0)

end Frames

def TowerEx : Prop := All fun {_} _ _ _ {G} W M => ∀ v : CoreVol G, ∃ F : Frames G, F.Ends v W M ∧ ∃ ΓL, F.Good v W ΓL

def FockTot : Prop := All fun {D} _ _ _ {G} W _ => ∀ (i : Fin D.R.m) (ℓ : (WO (G.V (.grid (i.1 + 1) 0)) (G.V (.grid i.1 0)) → ℂ) → ℂ),
  Tame W.ψ _ _ ℓ → (∀ κ P, ℓ (star (W.fock (.chi i.1 0) (W.cosVec i.1 κ) P)) = 0) → ∀ f, VacG W.ψ _ _ (latRow G i.1) f → ℓ f = 0

end GlobalTheory.Asc

end
end
