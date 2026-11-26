module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.PsiFEqOne
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def psiF {v : HeightOneSpectrum (𝓞 F)} (ψv : Fv F v → ℂ) (ϖ c : Fv F v) (k : ℕ) (a : Fv F v ⊗[F] E) : ℂ :=
  ψv (c * ((2 : Fv F v)⁻¹ * ((ϖ ^ k)⁻¹ * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a)))

theorem sigR_smul {v : HeightOneSpectrum (𝓞 F)} (σ : E →ₐ[F] E) (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

variable {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

namespace GoodLoc

variable (hG : GoodLoc σ J T bs v ψv S σS ϖ ε)
include hG

def pS : S := ⟨_, hG.unif_S⟩

theorem psi_of_mem {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : ψv x = 1 := by
  have := (hG.psi_cond 1).2 (one_mem _) x hx
  simpa using this

theorem trace_mem {a : Fv F v ⊗[F] E} (ha : a ∈ S) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a ∈ v.adicCompletionIntegers F := by
  have := (hG.trace_dual a).2 ha 1 (one_mem _)
  simpa using this

theorem half_mem : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, norm_inv, hG.two, inv_one]

theorem psiF_eq_one {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) (k : ℕ) {a : S}
    (ha : a ∈ lev hG.pS k) : psiF ψv ϖ c k (a : Fv F v ⊗[F] E) = 1 := by
  obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.1 ha
  apply hG.psi_of_mem
  have e1 : ((c' * hG.pS ^ k : S) : Fv F v ⊗[F] E) = (ϖ ^ k) • (c' : Fv F v ⊗[F] E) := by
    rw [Subring.coe_mul, Subring.coe_pow, Algebra.smul_def, map_pow, mul_comm]
    rfl
  rw [e1, LinearMap.map_smul, smul_eq_mul, ← mul_assoc (ϖ ^ k)⁻¹, inv_mul_cancel₀ (pow_ne_zero _ hG.unif_ne), one_mul]
  exact mul_mem hc (mul_mem hG.half_mem (hG.trace_mem c'.2))

theorem psiF_add (c : Fv F v) (k : ℕ) (a b : Fv F v ⊗[F] E) :
    psiF ψv ϖ c k (a + b) = psiF ψv ϖ c k a * psiF ψv ϖ c k b := by
  simp only [psiF, map_add (f := _), mul_add, hG.psi_add]

def psiLev {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) (k : ℕ) : AddChar (S ⧸ lev hG.pS k) ℂ where
  toFun x := Quotient.liftOn' x (fun a : S => psiF ψv ϖ c k (a : Fv F v ⊗[F] E)) (fun a b hab => by
    have h : a - b ∈ lev hG.pS k := (Submodule.quotientRel_def _).1 hab
    have e : (a : Fv F v ⊗[F] E) = ((a - b : S) : Fv F v ⊗[F] E) + (b : Fv F v ⊗[F] E) := by simp
    show psiF ψv ϖ c k (a : Fv F v ⊗[F] E) = psiF ψv ϖ c k (b : Fv F v ⊗[F] E)
    rw [e, hG.psiF_add, hG.psiF_eq_one hc k h, one_mul])
  map_zero_eq_one' := by
    show psiF ψv ϖ c k ((0 : S) : Fv F v ⊗[F] E) = 1
    simp only [psiF, ZeroMemClass.coe_zero, map_zero, mul_zero, hG.psi_zero]
  map_add_eq_mul' x y := by
    induction x using Quotient.inductionOn' with
    | h a =>
      induction y using Quotient.inductionOn' with
      | h b =>
        show psiF ψv ϖ c k ((a + b : S) : Fv F v ⊗[F] E) = psiF ψv ϖ c k (a : Fv F v ⊗[F] E) * psiF ψv ϖ c k (b : Fv F v ⊗[F] E)
        rw [Subring.coe_add, hG.psiF_add]

theorem psiLev_mk {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) (k : ℕ) (a : S) :
    hG.psiLev hc k (Ideal.Quotient.mk _ a) = psiF ψv ϖ c k (a : Fv F v ⊗[F] E) := rfl

def hermLev (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) : HermR (Fv F v) σ n :=
  ⟨fun a b => (ϖ ^ k)⁻¹ • (X a b : Fv F v ⊗[F] E), fun a b => by
    rw [sigR_smul, ← hG.sig]
    congr 2
    have := congrFun (congrFun hX a) b
    simpa [PositivityTheory.PfSWUS.Loc.cT] using this⟩

end GoodLoc

def H0 (S : Subring (Fv F v ⊗[F] E)) (σ : E →ₐ[F] E) (n : ℕ) : AddSubgroup (HermR (Fv F v) σ n) where
  carrier := {b | ∀ i j, (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j ∈ S}
  zero_mem' := fun i j => by simp
  add_mem' := fun ha hb i j => by simpa using add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => by simpa using neg_mem (ha i j)

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct

def SelfDualVol : Prop :=
  ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → ∀ L : AddSubgroup V, IsOpen (L : Set V) → IsCompact (L : Set V) →
    (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → (∀ y, Continuous fun x => χ x y) →
    (∀ y, (∀ x ∈ L, χ x y = 1) ↔ y ∈ L) → μ L = 1

def CosetInt : Prop :=
  ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (ν : Measure G) [ν.IsAddLeftInvariant]
    (H : AddSubgroup G), (∀ g : G, MeasurableSet {x : G | x - g ∈ H}) → ν H = 1 → Countable (G ⧸ H) →
    ∀ (f : G → ℂ) (fbar : G ⧸ H → ℂ), (∀ g, f g = fbar (QuotientAddGroup.mk g)) →
      (Integrable f ν ↔ Summable fun c => ‖fbar c‖) ∧ (Summable (fun c => ‖fbar c‖) → ∫ g, f g ∂ν = ∑' c, fbar c)

def TsumExhaust : Prop :=
  ∀ (α : Type) (f : α → ℂ) (C : ℕ → Finset α), Monotone C → (∀ a, ∃ k, a ∈ C k) →
    (∃ K : ℝ, ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) →
    Summable (fun a => ‖f a‖) ∧ Tendsto (fun k => ∑ a ∈ C k, f a) atTop (𝓝 (∑' a, f a))

def NuPow : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (n k : ℕ),
    ∀ B ∈ hermMod σ ϖ n k, nuAt ϖ B = (q ^ 2) ^ Nat.log (q ^ 2) (nuAt ϖ B)

def NuBound : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (n k : ℕ) (r : ℝ), 0 ≤ r →
    (q : ℝ) ^ (n ^ 2) * r < 1 →
    ∑' B : hermMod σ ϖ n k, r ^ Nat.log (q ^ 2) (nuAt ϖ B.1) ≤ 1 / (1 - (q : ℝ) ^ (n ^ 2) * r)

def LevChars : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ (c : Fv F v) (hc : c ∈ v.adicCompletionIntegers F), ‖c‖ = 1 → IsLevelChars σS hG.pS (hG.psiLev hc)

def VolLat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E), SdW F E σ M J (Fv F v) ψv n μv → μv (latV bs v) = 1

def HermitianLatticeVolumeOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ νv : Measure (HermR (Fv F v) σ n), SdHerm F E σ (Fv F v) ψv n νv → νv (H0 S σ n : Set (HermR (Fv F v) σ n)) = 1

def JtLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E), SdW F E σ M J (Fv F v) ψv n μv →
  ∀ (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X),
    jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (hG.hermLev k X hX) =
      ((ε : ℂ) ^ M * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(M : ℤ))) ^
        Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS (red hG.pS k X))

def NuLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)), lam.IsAddHaarMeasure →
    (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v →
  ∀ (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X),
    nu2 lam L L (hG.hermLev k X hX).1 = (nuAt hG.pS (red hG.pS k X) : ℝ)

def PsiLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ (hT : ∀ a b, σ (T b a) = T a b) (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X),
    ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 (hG.hermLev k X hX).1) =
      hG.psiLev (c := -1) (neg_mem (one_mem _)) k (Matrix.trace (red hG.pS k (matS S T hG.T_int) * red hG.pS k X))

def Exhaust : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ b : HermR (Fv F v) σ n, ∃ (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X),
    b = hG.hermLev k X hX

def ClassLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ (k : ℕ) (X X' : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X)
    (hX' : PositivityTheory.PfSWUS.Loc.cT σS X' = X'),
    hG.hermLev k X hX - hG.hermLev k X' hX' ∈ H0 S σ n ↔ red hG.pS k X = red hG.pS k X'

def HermitianLatticeInvariance : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ (hT : ∀ a b, σ (T b a) = T a b) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)),
    (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v → ∀ (z : ℂ) (b h : HermR (Fv F v) σ n), h ∈ H0 S σ n →
      whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z (b + h) =
        whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z b

def CosetMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  MeasurableAdd (HermR (Fv F v) σ n) ∧ ∀ g : HermR (Fv F v) σ n, MeasurableSet {x | x - g ∈ H0 S σ n}

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open Classical in
def basisSet (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) : Finset F :=
  (Finset.univ.image fun p : Fin d × Fin d × Fin d => bs.repr (bs p.1 * bs p.2.1) p.2.2) ∪
  (Finset.univ.image fun k : Fin d => bs.repr 1 k) ∪
  (Finset.univ.image fun p : Fin d × Fin d => bs.repr (σ (bs p.1)) p.2) ∪
  {Algebra.discr F (⇑bs), (Algebra.discr F (⇑bs))⁻¹, (2 : F)⁻¹}


open Classical in
def matSet {d : ℕ} (bs : Module.Basis (Fin d) F E) {m : ℕ} (X : Matrix (Fin m) (Fin m) E) : Finset F :=
  (Finset.univ.image fun p : Fin m × Fin m × Fin d => bs.repr (X p.1 p.2.1) p.2.2) ∪
  (Finset.univ.image fun k : Fin d => bs.repr (X.det)⁻¹ k)

def IntAt (v : HeightOneSpectrum (𝓞 F)) (X : Finset F) : Prop :=
  ∀ x ∈ X, algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F

def FinInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Finset F), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IntAt v X

def PsiBasic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    (∀ x y, psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y) ∧ psiV F ψ v 0 = 1 ∧ Continuous (psiV F ψ v)

def PsiCond : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ a : Fv F v,
      (∀ b ∈ v.adicCompletionIntegers F, psiV F ψ v (a * b) = 1) ↔ a ∈ v.adicCompletionIntegers F

def LocRing : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)), IntAt v (basisSet σ bs) →
  ∃ (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S),
    (ε = 1 ∨ ε = -1) ∧ (S : Set (Fv F v ⊗[F] E)) = Rv bs v ∧
    (∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x) ∧
    (∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = x → ∃ c : Fv F v, x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c) ∧
    ϖ ∈ v.adicCompletionIntegers F ∧ ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧
    IsUnrQuad S σS ⟨_, hϖ⟩ (Ideal.absNorm v.asIdeal) ε ∧ ‖(2 : Fv F v)‖ = 1 ∧
    ∀ a : Fv F v ⊗[F] E,
      (∀ b ∈ S, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a * b) ∈ v.adicCompletionIntegers F) ↔ a ∈ S

def LocMat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : ℕ) (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S),
    (S : Set (Fv F v ⊗[F] E)) = Rv bs v → (∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x) →
  ∀ (m : ℕ) (X : Matrix (Fin m) (Fin m) E), (∀ a b, σ (X b a) = X a b) → X.det ≠ 0 → IntAt v (matSet bs X) →
    ∃ hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S, IsUnimod σS (matS S X hX)

end PositivityTheory.SiegelWeilFormula.Gunr

end
end
