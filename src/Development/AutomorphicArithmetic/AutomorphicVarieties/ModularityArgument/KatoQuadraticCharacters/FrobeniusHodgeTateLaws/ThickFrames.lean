module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt
public import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalModPrimePowCommutesHeckeDiamond

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def ZetaEulerSystemIwasawa : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
      (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
    ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
      (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
      (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e →
      (∃ x, cw x ≠ 0) → AdmWn ι e g A W X pr N cw c d gm ψ cf →
      ∃ (c₀ m : ℕ) (cf' : Coef l) (S' : Finset Pl) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
        (y : G ℚ Ω → Fin 2 → Qbar l),
        IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y ∧
        (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
        (∀ r, Y r = GlobalTheory.KA.push (redL l r) (Y (r + 1))) ∧
        (∀ r y i, Continuous fun s => Y r s y i) ∧
        (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) ∧ (∀ r s y i, Y r s y i ∈ cf.O) ∧ (∀ z, z ∈ cf.O → z ∈ cf'.O) ∧
        (∀ r s, Cv r (y s) (GlobalTheory.KA.spec (fun u : (ZMod (l ^ r))ˣ => ((((u : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r u) (Y r) s)) ∧
        Sys W cf' (fun s => ((l : Qbar l) ^ m) • y s) S' ∧
        IwSys2 cf' A (nuD W e ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) ∧
        SpLink A e (chiK l ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) (fun s => ((l : Qbar l) ^ m) • y s)

def ZetaHodgeTateLaw : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
      (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
    ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
      (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
      AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
    ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
    ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
      IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
      (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
      (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
      (∀ r s y, Y r s y 1 ∈ cf.O) →
    ∀ (χd : ℕ → ℤ_[l]), (∀ b ∈ X.B N l (2 * e - 1), ∀ d : ℕ, Nat.Coprime d N → pr (X.diam N l d b) = algebraMap ℚ_[l] (Qbar l) (χd d : ℚ_[l]) • pr b) →
    ∀ (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), GlobalTheory.KummerEisensteinGalois.IsLamFR X A N (2 * e - 1) χd j pr cf lam →
    ∃ (m₀ c₁ : ℕ) (κ : Qbar l) (v : ℕ → Qbar l), κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧
      HTLawCsOfCoef A cf (fun r s y => Y r s y 1) j m₀ c₁
        (fun m ψ z => v m * κ * (∑ a : ZMod (l ^ m), ψ a * z ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
          lam (GlobalTheory.KummerEisensteinGalois.up (l ^ m) (fun i => ∑ x : ZMod N, cw x *
            GlobalTheory.LambdaValuationPowers.chiProj N l m (2 * e + 1) ψ (fun n => algebraMap ℚ_[l] (Qbar l) (χd n : ℚ_[l])) (c : ℤ) (d : ℤ) (x.val : ℤ) i)))

def AdmTop : Prop :=
  ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
    [Fact l.Prime] (e : ℕ) (S : Finset Pl) (W : R2 Ω l) (ψ : ZMod l → Qbar l) (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1))
    (j : Ω →+* Qbar l),
    Nf e S A W → 1 ≤ e →
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
    (∀ x ∈ A, ‖j x‖ ≤ 1) →
    ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
    (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) →
    (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
    (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
    (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e - 1 + 1)) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ev (Letter.T q) = ι.symm (gN.a q)) →
    ∀ (χ : ℕ → ℤ_[l]), (∀ d : ℕ, Nat.Coprime d N → ev (Letter.D d) = ((χ d : ℤ_[l]) : Qbar l)) →
    ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
      (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
    P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l (2 * e - 1) (Qbar l)) →
    (∀ i s, ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
    (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
    (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
    (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.opV N l (Qbar l) T x) = ev T • π i x) →
    (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
    (∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
    ∀ (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
    (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N (2 * e - 1) χ b →
      Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
    ∃ (pr : X.Fn l → Fin 2 → Qbar l) (a : ℕ) (cf : Coef l),
      c.O ≤ cf.O ∧ (∀ s i k, mat W s i k ∈ cf.O) ∧
      (∀ b b', pr (b + b') = pr b + pr b') ∧
      (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
      (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
      (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
      (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b) ∧
      (∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b) ∧
      IsLamFR X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam)


open Matrix in
def NewformPartOfTowerModule : Prop :=
  ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) [Fact l.Prime], l ≠ 2 → g.M ∣ N → 5 ≤ N → Nat.Coprime N l → Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) → ∀ lamC : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lamC (Letter.T q) = g.a q) → lamC Letter.U = α → (∀ d : ℕ, Nat.Coprime d N → lamC (Letter.D d) = g.χ (d : ZMod g.M)) → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (ι : E ≃+* ℂ), let w := k - 2; let lam : Letter → E := fun T => ι.symm (lamC T); ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, GlobalTheory.KZ.admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x)

def AdmRho : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
      (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (ψ : ZMod l → Qbar l),
    Nf e S A W → SrcUr ι e A W g →
    (∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
      (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l)) = 1) ∧
      ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)) →
    ∃ ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l),
      (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) ∧ Continuous ρ ∧
      (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) ∧
      (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) ∧
      ∃ F : Finset Ω, ∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
        (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e)

def TowerEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Nonempty (Tower Ω ε)

def GmEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N : ℕ), Nat.Coprime l N → ∃ gm : (ZMod l)ˣ → SL(2, ℤ), ∀ r₀ : (ZMod l)ˣ,
    gm r₀ ∈ CongruenceSubgroup.Gamma1 N ∧ (N : ℤ) ∣ (gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
    (((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod l) = -(r₀ : ZMod l) * (((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod l) ∧
    ∃ t : (ZMod l)ˣ, (![0, 1] : Fin 2 → ZMod l) ᵥ* ((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod l))) =
      (t : ZMod l) • ![(r₀ : ZMod l), -1]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def rhs5 (N : ℕ) [NeZero N] (k : ℕ) (cw : ZMod N → Qbar l) (c d : ℕ) (δ : ℕ → Qbar l)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (v : ℕ → Qbar l) (κ : Qbar l) (m : ℕ) (ψ : DirichletCharacter (Qbar l) (l ^ m))
    (z : Qbar l) : Qbar l :=
  v m * κ * (∑ a : ZMod (l ^ m), ψ a * z ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
    lam (GlobalTheory.KummerEisensteinGalois.up (l ^ m) fun i => ∑ x : ZMod N, cw x * GlobalTheory.LambdaValuationPowers.chiProj N l m k ψ δ (c : ℤ) (d : ℤ) (x.val : ℤ) i)

def AdmFR : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W →
  ∀ (χg : G ℚ Ω →* (Qbar l)ˣ) (ψ₀ : ZMod l → Qbar l), ¬ l ∣ g.M → ‖ι.symm (g.a l)‖ = 1 → KillsMu l χg →
    g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χg)) →
    (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χg s : Qbar l)) = 1) →
    (∀ s, (χg s : Qbar l) = ψ₀ (cyc1 l s)) →
  ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) → ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (α : ℂ) (B : ℕ) (cc : ℕ → ℂ) (c₀ : Coef l), 5 ≤ N → g.M ∣ N → ¬ l ∣ N →
    (∀ d : ℕ, d.Coprime N → χ d = g.χ d) → ‖ι.symm α‖ = 1 → α ^ 2 - g.a l * α + χ l * (l : ℂ) ^ (2 * e) = 0 →
    GlobalTheory.EisM.EigF (2 * e + 1) N l χ (fun q => g.a q) α B cc →
  ∃ (pr : X.Fn l → Fin 2 → Qbar l) (cf : Coef l) (χd : ℕ → ℤ_[l]) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (κ : Qbar l),
    c₀.O ≤ cf.O ∧ κ ≠ 0 ∧ (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ₀ s *ᵥ pr b) ∧
    (∃ δ' : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (g.a q) • pr b ∧ pr (X.diam N l q b) = δ' q • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ι.symm α • pr b) ∧
    (∀ d : ℕ, d.Coprime N → ι (algebraMap ℚ_[l] (Qbar l) (χd d : ℚ_[l])) = χ d) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ d : ℕ, Nat.Coprime d N → pr (X.diam N l d b) = algebraMap ℚ_[l] (Qbar l) (χd d : ℚ_[l]) • pr b) ∧
    IsLamFR X A N (2 * e - 1) χd j pr cf lam ∧
    ∀ a : ℕ → Qbar l, GlobalTheory.EisM.MF (2 * e + 1) (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) →
      lam a = κ * ι.symm (GlobalTheory.EisM.lam B cc fun i => ι (a i))

def ExplSmul : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (A : ValuationSubring Ω) (c : Coef l)
    (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (j : Ω →+* Qbar l) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (cc : ℕ → ℂ) (n : ℕ)
    (β : Fin n → Qbar l) (t : Fin n → ℕ) (m : ℕ), Expl ι e A c Z j s u w α B cc n β t →
    Expl ι e A c (fun r s y => (l : Qbar l) ^ m * Z r s y) j s u w α B cc n β t


open Classical in
def RhsEq : Prop := AvgEq → AvgMF →
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e N : ℕ) [NeZero N] (θ χ : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ)
    (cc : ℕ → ℂ) (c d : ℕ) (δ : ℕ → Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (κ' κ : Qbar l) (v : ℕ → Qbar l),
    l ≠ 2 → 1 ≤ e → ¬ l ∣ N → χ (-1) = -1 → α ≠ 0 → c.Coprime N → d.Coprime N → GlobalTheory.EisM.EigAll (2 * e + 1) N l χ t α B cc →
    (∀ u : ℕ, u.Coprime N → ι (δ u) = χ u) →
    (∀ a : ℕ → Qbar l, GlobalTheory.EisM.MF (2 * e + 1) (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) →
      lam a = κ' * ι.symm (GlobalTheory.EisM.lam B cc fun i => ι (a i))) →
    ∀ m, 1 ≤ m → ∀ (ψ : DirichletCharacter (Qbar l) (l ^ m)) (z : Qbar l),
      rhs5 N (2 * e + 1) (fun x => ι.symm (GlobalTheory.EisM.hat θ (x.val : ℤ) / 2)) c d δ lam v κ m ψ z =
        if ψ (-1) = ι.symm (θ (-1)) then
          v m * (κ * κ' * (N.totient : Qbar l)) * ι.symm α ^ m *
            ((∑ i, smB (2 * e + 1) c d (ι.symm (θ c)) (ι.symm ((θ * χ)⁻¹ d)) i * ψ⁻¹ (smT N c d i : ZMod (l ^ m))) *
              (∑ b : (ZMod (l ^ m))ˣ, ψ b * z ^ (b : ZMod (l ^ m)).val) *
              ι.symm (GlobalTheory.EisM.mesMu (2 * e + 1) l (GlobalTheory.EisM.hat θ) (GlobalTheory.EisM.tw2 N (θ (-1))) α B cc m fun y => ι (ψ y)))
        else 0

end UpperTheory.V.Z.Kato.Joint

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FormPLamSmul
open UpperTheory.V.Z.Kato.Joint

private theorem formP_lam_add (B : ℕ) (cc a b : ℕ → ℂ) :
    GlobalTheory.EisM.lam B cc (a + b) = GlobalTheory.EisM.lam B cc a + GlobalTheory.EisM.lam B cc b := by
  unfold GlobalTheory.EisM.lam
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem formP_lam_smul (B : ℕ) (cc a : ℕ → ℂ) (r : ℂ) :
    GlobalTheory.EisM.lam B cc (r • a) = r * GlobalTheory.EisM.lam B cc a := by
  unfold GlobalTheory.EisM.lam
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem UpperTheory.V.Z.Kato.Joint.LocFacts₂ :
    UpperTheory.V.Z.Kato.Joint.FormP := by
  unfold UpperTheory.V.Z.Kato.Joint.FormP
  intro l _ ι k N χ t α B cc χE ev hk hE hχE hT hU hD P hP
  have hℓ : Nat.Prime l := Fact.out
  suffices key : ∀ a : ℕ → Formalism.ConjugateSelfDual.Qbar l,
      GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) →
      GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ)
                   (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) ∧
        (GlobalTheory.EisM.lam B cc fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) =
          ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) ev) P) * GlobalTheory.EisM.lam B cc fun i => ι (a i) from
    fun a ha => (key a ha).2
  unfold GlobalTheory.KZ.admissibleLettersSubalgebra at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    intro a ha
    simp only [FreeAlgebra.lift_ι_apply]
    cases x with
    | T q =>
      obtain ⟨hq, hqn⟩ : Nat.Prime q ∧ ¬q ∣ N * l := hx
      have hcop : q.Coprime N :=
        Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn)
      have hχq : ι (χE q) = GlobalTheory.EisM.ch χ (q : ℤ) := by
        rw [hχE q hcop]
        simp [GlobalTheory.EisM.ch]
      have hf : (fop k l χE (GlobalTheory.KZ.Letter.T q)) a = GlobalTheory.EisM.To k (χE q) q a := rfl
      have hcomm : (fun i => ι (GlobalTheory.EisM.To k (χE q) q a i)) =
          GlobalTheory.EisM.To k (GlobalTheory.EisM.ch χ (q : ℤ)) q (fun i => ι (a i)) := by
        funext m
        simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, map_add (f := _), map_mul, map_pow, map_natCast, hχq]
        split_ifs <;> simp
      rw [hf, hcomm]
      refine ⟨GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ _ hk (dvd_mul_right N l) hq hqn ha, ?_⟩
      rw [hE.T _ ha q hq hqn, hT q hq hqn]
    | U =>
      have hf : (fop k l χE GlobalTheory.KZ.Letter.U) a = GlobalTheory.EisM.Uo l a := rfl
      have hcomm : (fun i => ι (GlobalTheory.EisM.Uo l a i)) = GlobalTheory.EisM.Uo l (fun i => ι (a i)) := rfl
      rw [hf, hcomm]
      refine ⟨(GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l _ (fun i => ι (a i)) hk hℓ (dvd_mul_left l N) ?_ ha).1, ?_⟩
      · intro d
        simp [GlobalTheory.EisM.ch]
      · rw [hE.U _ ha, hU]
    | D d =>
      have hd : d.Coprime N := hx
      have hf : (fop k l χE (GlobalTheory.KZ.Letter.D d)) a = χE d • a := rfl
      have hcomm : (fun i => ι ((χE d • a) i)) = ι (χE d) • fun i => ι (a i) := by
        funext i
        simp
      rw [hf, hcomm, formP_lam_smul, hD d hd]
      exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.2.1 _ _ ha).1, rfl⟩
  | algebraMap r =>
    intro a ha
    have hf : (FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) (algebraMap (Formalism.ConjugateSelfDual.Qbar l) _ r) a = r • a := by
      simp [Algebra.algebraMap_eq_smul_one]
    have hcomm : (fun i => ι ((r • a) i)) = ι r • fun i => ι (a i) := by
      funext i
      simp
    rw [hf, hcomm, formP_lam_smul, AlgHom.commutes]
    exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.2.1 _ _ ha).1, rfl⟩
  | add x y _ _ hx hy =>
    intro a ha
    obtain ⟨h1, h2⟩ := hx a ha
    obtain ⟨h3, h4⟩ := hy a ha
    have hcomm : (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE) (x + y)) a i)) =
        (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) x) a i)) +
          (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) y) a i)) := by
      funext i
      simp
    rw [hcomm, formP_lam_add, h2, h4, map_add (f := _), map_add (f := _), add_mul]
    exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.1 _ _ h1 h3).1, rfl⟩
  | mul x y _ _ hx hy =>
    intro a ha
    obtain ⟨h3, h4⟩ := hy a ha
    obtain ⟨h1, h2⟩ := hx _ h3
    simp only [map_mul, Module.End.mul_apply]
    refine ⟨h1, ?_⟩
    rw [h2, h4, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FinSuppCompLift
open UpperTheory.V.Z.Kato.Joint

section

open Formalism.ConjugateSelfDual GlobalTheory.KZ GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers UpperTheory.V.HV

variable {l : ℕ} [Fact l.Prime]

private theorem finSupp_comp_fop (k : ℕ) (χ : ℕ → Qbar l) (T : Letter)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (h : FinSupp lam) : FinSupp (lam ∘ₗ fop k l χ T) := by
  obtain ⟨S, hS⟩ := h
  cases T with
  | T q =>
    refine ⟨S.image (q * ·) ∪ S.image (· / q), fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show GlobalTheory.EisM.To k (χ q) q f n = 0
    have h1 : f (q * n) = 0 := hf _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
    have h2 : f (n / q) = 0 := hf _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
    simp [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, h1, h2]
  | U =>
    refine ⟨S.image (l * ·), fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show GlobalTheory.EisM.Uo l f n = 0
    exact hf _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  | D d =>
    refine ⟨S, fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show (χ d • f) n = 0
    simp [hf n hn]

private theorem finSupp_comp_lift (k : ℕ) (χ : ℕ → Qbar l) (P : FreeAlgebra (Qbar l) Letter) :
    ∀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l, FinSupp lam →
      FinSupp (lam ∘ₗ FreeAlgebra.lift (Qbar l) (fop k l χ) P) := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    intro lam h
    rw [AlgHom.commutes]
    have hr : lam ∘ₗ algebraMap (Qbar l) (Module.End (Qbar l) (ℕ → Qbar l)) r = r • lam := by
      ext f
      simp [Module.algebraMap_end_apply]
    rw [hr]
    exact FinSupp.smul h r
  | grade1 x =>
    intro lam h
    rw [FreeAlgebra.lift_ι_apply]
    exact finSupp_comp_fop k χ x lam h
  | mul a b ha hb =>
    intro lam h
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    exact hb _ (ha lam h)
  | add a b ha hb =>
    intro lam h
    rw [map_add (f := _), LinearMap.comp_add]
    exact FinSupp.add (ha lam h) (hb lam h)

private theorem exists_pow_mul_le (x : Qbar l) : ∃ k : ℕ, ‖((l : ℕ) : Qbar l) ^ k * x‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_le_l_pow l ‖x‖
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_l_pow]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  calc ((l : ℝ))⁻¹ ^ k * ‖x‖ ≤ ((l : ℝ))⁻¹ ^ k * (l : ℝ) ^ k := by gcongr
    _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl.ne', one_pow]

end

open Formalism.ConjugateSelfDual GlobalTheory.KZ GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers UpperTheory.V.HV in
theorem UpperTheory.V.Z.Kato.Joint.finP :
    UpperTheory.V.Z.Kato.Joint.FinP := by
  classical
  intro hub l _ ι k N B cc χE c₀ P _
  let lam₀ : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l :=
    ∑ n ∈ Finset.range B, ι.symm (cc n) • LinearMap.proj n
  have hlam₀ : ∀ a : ℕ → Qbar l, lam₀ a = ι.symm (GlobalTheory.EisM.lam B cc fun i => ι (a i)) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [lam₀, GlobalTheory.EisM.lam, map_sum, map_mul, LinearMap.sum_apply]
  have hfs₀ : FinSupp lam₀ := by
    refine ⟨Finset.range B, fun f hf => ?_⟩
    rw [hlam₀, GlobalTheory.EisM.lam, Finset.sum_eq_zero, map_zero]
    intro n hn
    simp [hf n hn]
  let lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l := lam₀ ∘ₗ FreeAlgebra.lift (Qbar l) (fop k l χE) P
  have hfs : FinSupp lam := finSupp_comp_lift k χE P lam₀ hfs₀
  obtain ⟨S, hS⟩ := hfs
  choose e he using exists_pow_mul_le (l := l)
  let g : ℕ → Qbar l := fun i => ((l : ℕ) : Qbar l) ^ e (lam (Pi.single i 1)) * lam (Pi.single i 1)
  obtain ⟨c, hc₀, -, hcF⟩ := hub l c₀ c₀ (S.image g) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact he _)
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨lam₀, lam, c, hc₀, hfs₀, ⟨S, hS⟩, ?_, hlam₀, fun a => rfl⟩
  intro i σ hσ _
  by_cases hi : i ∈ S
  · have hy := hσ _ (hcF _ (Finset.mem_image_of_mem g hi))
    have hne : ((l : ℕ) : Qbar l) ^ e (lam (Pi.single i 1)) ≠ 0 := by
      intro h0
      have h1 := congrArg norm h0
      rw [norm_l_pow, norm_zero] at h1
      exact pow_ne_zero _ (inv_ne_zero hl.ne') h1
    simp only [g, map_mul, map_pow, map_natCast] at hy
    exact mul_left_cancel₀ hne hy
  · have h0 : lam (Pi.single i 1) = 0 :=
      hS _ (fun s hs => Pi.single_eq_of_ne (by rintro rfl; exact hi hs) 1)
    rw [h0, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SgDOneMem
open UpperTheory.V.Z.Kato.Joint
open Formalism.ConjugateSelfDual GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt

variable {l : ℕ} [Fact l.Prime]

private theorem norm_zl (c : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) c‖ = ‖c‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  rfl

private theorem nadd {r : ℝ} {x y : Qbar l} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

private theorem nmul {r : ℝ} {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ r) : ‖x * y‖ ≤ r := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans hy

private theorem nappr (n : ℕ) (c : ℤ_[l]) :
    ‖((c.appr n : ℕ) : Qbar l) - algebraMap ℤ_[l] (Qbar l) c‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n c)
  have h := congrArg (algebraMap ℤ_[l] (Qbar l)) hz
  simp only [map_mul, map_pow, map_natCast, map_sub] at h
  rw [norm_sub_rev, ← h]
  exact nmul (by rw [norm_zl]; exact z.norm_le_one) le_rfl

private theorem extend {M : Type} [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
    (r : ℝ) (f : M → ℕ → Qbar l)
    (hf : ∀ b ∈ B, ∀ b' ∈ B, ∀ c c' : ℤ_[l], ∀ i,
      ‖f (c • b + c' • b') i - (algebraMap ℤ_[l] (Qbar l) c * f b i + algebraMap ℤ_[l] (Qbar l) c' * f b' i)‖ ≤ r) :
    ∃ Θ : (Qbar l ⊗[ℤ_[l]] M) →ₗ[Qbar l] (ℕ → Qbar l), ∀ b ∈ B, ∀ i, ‖Θ ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) i - f b i‖ ≤ r := by
  classical
  let e := Module.Free.chooseBasis ℤ_[l] B
  let g : B →ₗ[ℤ_[l]] (ℕ → Qbar l) := e.constr ℤ_[l] (fun k => f (e k))
  have h0 : ∀ i, ‖f 0 i‖ ≤ r := fun i => by simpa using hf 0 B.zero_mem 0 B.zero_mem 0 0 i
  have hr : 0 ≤ r := (norm_nonneg _).trans (h0 0)
  have hg : ∀ b : B, ∀ i, ‖g b i - f b i‖ ≤ r := by
    intro b i
    have hb : b ∈ Submodule.span ℤ_[l] (Set.range e) := by rw [e.span_eq]; trivial
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simpa [g] using hr
    | zero => simpa using h0 i
    | add x y _ _ hx hy =>
      have h := hf x x.2 y y.2 1 1 i
      simp only [one_smul, map_one, one_mul] at h
      rw [← norm_neg] at h
      have := nadd (nadd hx hy) h
      convert this using 2
      simp only [map_add (f := _), Pi.add_apply, Submodule.coe_add]
      ring
    | smul c x _ hx =>
      have h := hf x x.2 0 B.zero_mem c 0 i
      simp only [zero_smul, add_zero, map_zero, zero_mul] at h
      rw [← norm_neg] at h
      have := nadd (nmul (x := algebraMap ℤ_[l] (Qbar l) c) (by rw [norm_zl]; exact c.norm_le_one) hx) h
      convert this using 2
      simp only [map_smul, Pi.smul_apply, Submodule.coe_smul, Algebra.smul_def]
      ring
  haveI : Module.IsTorsionFree ℤ_[l] (Qbar l) := by
    refine (Module.isTorsionFree_iff_algebraMap_injective).2 ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have := norm_zl a
    rw [ha, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  haveI : Module.Flat ℤ_[l] (Qbar l) := inferInstance
  have hinj : Function.Injective (B.subtype.baseChange (Qbar l)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Qbar l) B.subtype B.injective_subtype
  obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective (B.subtype.baseChange (Qbar l))
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(g.liftBaseChange (Qbar l)) ∘ₗ s, fun b hb i => ?_⟩
  have h1 : s ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) = (1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : B) :=
    LinearMap.congr_fun hs ((1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : B))
  simpa [h1] using hg ⟨b, hb⟩ i

private theorem sgD_one_mem {N : ℕ} (hN : N ≠ 0) : sgD N l 1 ∈ Gam N l := by
  obtain ⟨⟨h0, h1⟩, h2⟩ := Betti.isDiam_sgD (l := l) (d := 1) hN (Fact.out : l.Prime).ne_zero (Nat.coprime_one_left N)
  refine ⟨?_, h1⟩
  have h3 : (⟨sgD N l 1, h0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem']
    simpa [en, CongruenceSubgroup.Gamma0Map] using h2
  exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3)

private theorem act_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {N w : ℕ} {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gam N l) {b : X.Fn l} (hb : b ∈ X.B N l w) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

end UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt

open UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt in
theorem UpperTheory.V.Z.Kato.Joint.thLin :
    UpperTheory.V.Z.Kato.Joint.ThLin := by
  intro l _ Ω _ _ _ ε X A N w j hS n
  obtain ⟨hA, h2, hlN, h5, hw, hj⟩ := hS
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hcop : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hlN).symm
  have hhol : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩
  haveI := (GlobalTheory.T.kummerBettiModule_free_finite ε X ε.injective hhol N l w h2 h5 hcop hw).1
  have hth : ∀ b ∈ X.B N l w, IsThB X A N l n b (thN X A N l n 1 b) := by
    intro b hb
    have h := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol h2 hlN h5 hA n w 1 hw (Nat.coprime_one_left N) b hb).1
    rwa [act_fix X (sgD_one_mem (by omega)) hb] at h
  have hint : ∀ b ∈ X.B N l w, ∀ i, ‖th X A N j n b i‖ ≤ 1 := by
    intro b hb i
    obtain ⟨f, -, -, -, h, -⟩ := hth b hb
    exact hj _ (h _)
  refine extend (X.B N l w) ‖((l : ℕ) : Qbar l) ^ n‖ (th X A N j n) ?_
  intro b hb b' hb' c c' i
  have hm : c • b + c' • b' ∈ X.B N l w := add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ hb')
  obtain ⟨z, hz, h⟩ := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol h2 hlN h5 hA n w hw _ hm _ _ (hth _ hm)
    (GlobalTheory.T.theta_basis_linear_combination Ω ε X A N l n w b b' hb hb' c c' _ _ (hth b hb) (hth b' hb')) ((i : ℚ) / ((1 : ℕ) : ℚ))
  have h1 := congrArg j h
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, smul_eq_mul, map_sub, map_add (f := _), map_mul, map_pow,
    map_natCast] at h1
  have h3 : ‖j z * ((l : ℕ) : Qbar l) ^ n‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := nmul (hj z hz) le_rfl
  have := nadd (nadd h3 (nmul (hint b hb i) (nappr n c))) (nmul (hint b' hb' i) (nappr n c'))
  convert this using 2
  simp only [th, seqN]
  linear_combination h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgAppr
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct
open UpperTheory.V.Z.Kato.Joint

namespace UpperTheory.V.Z.Kato.Joint.ThetaOperator

variable {l : ℕ} [Fact l.Prime]

private theorem cg_trans {n : ℕ} {x y z : Qbar l} (h1 : Cg n x y) (h2 : Cg n y z) : Cg n x z := by
  unfold Cg at *
  have e : x - z = (x - y) + (y - z) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

private theorem cg_symm {n : ℕ} {x y : Qbar l} (h1 : Cg n x y) : Cg n y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

private theorem cg_lin {n : ℕ} {x y : Qbar l} (a c : Qbar l) (hc : ‖c‖ ≤ 1) (h1 : Cg n x y) :
    Cg n (a + c * x) (a + c * y) := by
  unfold Cg at *
  have e : a + c * x - (a + c * y) = c * (x - y) := by ring
  rw [e, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans h1

private theorem cg_j {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (hj : ∀ x ∈ A, ‖j x‖ ≤ 1)
    {n : ℕ} {x y : Ω} (h : CgA A l n x y) : Cg n (j x) (j y) := by
  obtain ⟨z, hz, e⟩ := h
  unfold Cg
  rw [← map_sub, e, map_mul, map_pow, map_natCast, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hj z hz)

private theorem norm_appr_sub_le_norm_pow (n : ℕ) (c : ℤ_[l]) :
    ‖((c.appr n : ℕ) : Qbar l) - ((c : ℤ_[l]) : Qbar l)‖ ≤ ‖((l : Qbar l)) ^ n‖ := by
  have e : ((c.appr n : ℕ) : Qbar l) - ((c : ℤ_[l]) : Qbar l)
      = algebraMap ℚ_[l] (PadicAlgCl l) (((-(c - ((c.appr n : ℕ) : ℤ_[l])) : ℤ_[l]) : ℚ_[l])) := by
    simp
  have e2 : ((l : Qbar l)) ^ n = algebraMap ℚ_[l] (PadicAlgCl l) (((l : ℚ_[l])) ^ n) := by simp
  rw [e, e2, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends, PadicInt.padic_norm_e_of_padicInt, norm_neg]
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n c)
  refine h.trans (le_of_eq ?_)
  rw [Padic.norm_p_pow]

private theorem cg_appr (n : ℕ) (c : ℤ_[l]) (x : Qbar l) (hx : ‖x‖ ≤ 1) :
    Cg n (((c.appr n : ℕ) : Qbar l) * x) (((c : ℤ_[l]) : Qbar l) * x) := by
  unfold Cg
  rw [← sub_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_appr_sub_le_norm_pow n c) (norm_nonneg _)).trans
    (by rw [mul_comm]; exact mul_le_of_le_one_left (norm_nonneg _) hx)

private theorem appr_zero' (n : ℕ) : (0 : ℤ_[l]).appr n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [PadicInt.appr]; simp [ih]

private theorem diam_cg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]) (hS : Std A N w j) (n a : ℕ) (b : X.Fn l)
    (ha : a.Coprime N) (hb : InChi X N w χ b) (r : ℚ) :
    Cg n (j ((thN X A N l n 1 (X.diam N l a b)).coeff r))
      (((χ a : ℤ_[l]) : Qbar l) * j ((thN X A N l n 1 b).coeff r)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨hl, hl2, hlN, hN5, hw, hj⟩ := hS
  obtain ⟨hbB, hdiam⟩ := hb
  have hB1 : X.diam N l 1 b ∈ X.B N l w := by
    rw [hdiam 1 (Nat.coprime_one_left N)]
    exact Submodule.smul_mem _ _ hbB
  have hBa : X.diam N l a b ∈ X.B N l w := by
    rw [hdiam a ha]
    exact Submodule.smul_mem _ _ hbB
  have hψ := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw
    (Nat.coprime_one_left N) b hbB).1
  have hθ := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw
    (Nat.coprime_one_left N) (X.diam N l a b) hBa).1
  have hD : ∀ s : ℚ, (thN X A N l n 1 b).coeff s ∈ A := by
    obtain ⟨f, -, -, -, hd⟩ := hψ
    exact hd.1
  have hlin := GlobalTheory.T.theta_basis_linear_combination Ω ε X A N l n w (X.diam N l 1 b) (X.diam N l 1 b) hB1 hB1 (χ a) 0
    (thN X A N l n 1 b) (thN X A N l n 1 b) hψ hψ
  have e : X.act l (sgD N l 1) (X.diam N l a b) = χ a • X.diam N l 1 b + (0 : ℤ_[l]) • X.diam N l 1 b := by
    rw [zero_smul, add_zero, hdiam a ha, map_smul]
    rfl
  rw [e] at hθ
  have hmem : χ a • X.diam N l 1 b + (0 : ℤ_[l]) • X.diam N l 1 b ∈ X.B N l w :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hB1) (Submodule.smul_mem _ _ hB1)
  have hu := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w hw _ hmem _ _ hθ hlin r
  have h1 := cg_j hj hu
  rw [appr_zero'] at h1
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, Nat.cast_zero, zero_smul, add_zero,
    smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast] at h1
  exact cg_trans h1 (cg_appr n (χ a) _ (hj _ (hD r)))

end UpperTheory.V.Z.Kato.Joint.ThetaOperator

private theorem norm_natCast_pow_le_one {l : ℕ} [Fact l.Prime] (q k : ℕ) : ‖((q : Qbar l)) ^ k‖ ≤ 1 := by
  have e : ((q : Qbar l)) ^ k = algebraMap ℚ_[l] (PadicAlgCl l) (((q : ℤ) : ℚ_[l]) ^ k) := by simp
  rw [e, PadicAlgCl.norm_extends, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (Padic.norm_int_le_one _)

private theorem coeff_div_prime_eq_zero_of_not_dvd_of_isLat {Ω : Type} [Field Ω] (φ : HahnSeries ℚ Ω) (hL : IsLat 1 φ) {q i : ℕ}
    (hq : q.Prime) (hnd : ¬ q ∣ i) : φ.coeff ((i : ℚ) / q) = 0 := by
  by_contra h
  have hden := hL _ h
  rw [Nat.cast_one, one_mul] at hden
  have key : (((i : ℚ) / q).num : ℚ) = (i : ℚ) / q := Rat.coe_int_num_of_den_eq_one hden
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h2 : (i : ℚ) = q * ((i : ℚ) / q).num := by rw [key]; field_simp
  have h3 : (i : ℤ) = q * ((i : ℚ) / q).num := by exact_mod_cast h2
  exact hnd (Int.natCast_dvd_natCast.mp ⟨_, h3⟩)

open UpperTheory.V.Z.Kato.Joint.ThetaOperator in
theorem UpperTheory.V.Z.Kato.Joint.thOp :
    UpperTheory.V.Z.Kato.Joint.ThOp := by
  intro l _ Ω _ _ _ ε X A N w j χ hS n T b hT hb i
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hS' := hS
  obtain ⟨hl, hl2, hlN, hN5, hw, hj⟩ := hS'
  have hψ : ∀ m, IsThB X A N l m (X.act l (sgD N l 1) b) (thN X A N l m 1 b) ∧ IsLat 1 (thN X A N l m 1 b) :=
    fun m => GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl m w 1 hw (Nat.coprime_one_left N) b hb.1
  have hrel := GlobalTheory.T.cuspFunctionalModPrimePow_commutes_hecke_diamond Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw (Nat.coprime_one_left N) b hb.1
  cases T with
  | T q =>
    obtain ⟨hqp, hqNl⟩ := hT
    have hqN : q.Coprime N :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hqp).2 hqNl)
    simp only [th, seqN, fop, Tower.op, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.EisM.To, GlobalTheory.EisM.Vo]
    have h1 := hrel.1 q hqp hqNl ((i : ℚ) / (1 : ℕ))
    rw [GlobalTheory.CyclotomicQExpansion.Api.hq_eq_uq_of_isAlgClosed hqp.pos (hψ n).2] at h1
    have h1' := cg_j hj h1
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, GlobalTheory.CyclotomicQExpansion.Api.coeff_uq hqp.pos,
      GlobalTheory.CyclotomicQExpansion.Api.coeff_vq hqp.pos, map_add, Nat.cast_one, div_one, Rat.den_natCast, if_true,
      one_mul, smul_eq_mul, nsmul_eq_mul, map_mul, map_pow, map_natCast] at h1'
    have hx : Cg n (j ((thN X A N l n q b).coeff ((i : ℚ) / q)))
        (((χ q : ℤ_[l]) : Qbar l) *
          (if q ∣ i then j ((thN X A N l n 1 b).coeff (((i / q : ℕ) : ℚ) / ((1 : ℕ) : ℚ))) else 0)) := by
      have ha := cg_j hj (hrel.2.2 q hqN ((i : ℚ) / q))
      have hc := ThetaOperator.cg_trans (ThetaOperator.cg_symm ha) (diam_cg X A N w j χ hS n q b hqN hb ((i : ℚ) / q))
      rw [one_mul] at hc
      split_ifs with hdiv
      · rwa [Nat.cast_one, div_one, Nat.cast_div hdiv (by exact_mod_cast hqp.ne_zero)]
      · rw [mul_zero]
        rwa [coeff_div_prime_eq_zero_of_not_dvd_of_isLat _ (hψ n).2 hqp hdiv, map_zero, mul_zero] at hc
    have key := ThetaOperator.cg_trans h1' (cg_lin _ _ (norm_natCast_pow_le_one q (w + 1)) hx)
    have hw2 : w + 2 - 1 = w + 1 := by omega
    simp only [Nat.cast_one, div_one, Nat.cast_mul, hw2]
    convert key using 2
    simp only [Nat.cast_one, div_one]
    ring
  | U =>
    show Cg n (j ((thN X A N l n 1 (X.heckeU l b)).coeff ((i : ℚ) / ((1 : ℕ) : ℚ))))
      (j ((thN X A N l n 1 b).coeff (((l * i : ℕ) : ℚ) / ((1 : ℕ) : ℚ))))
    have h2 := cg_j hj (hrel.2.1 ((i : ℚ) / (1 : ℕ)))
    simp only [GlobalTheory.CyclotomicQExpansion.Api.coeff_uq (Fact.out : l.Prime).pos, Nat.cast_one, div_one, Rat.den_natCast,
      if_true] at h2
    have h3 := cg_j hj (GlobalTheory.T.cgA_coeff_of_isThB_succ Ω ε X A N l hl2 hlN (by omega) hl n _ _ _ (hψ (n + 1)).1 (hψ n).1
      ((l : ℚ) * i))
    simp only [Nat.cast_one, div_one, Nat.cast_mul]
    exact ThetaOperator.cg_trans h2 h3
  | D d =>
    simp only [th, seqN, fop, Tower.op, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply,
      smul_eq_mul]
    exact diam_cg X A N w j χ hS n d b hT hb _

end
end
