module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
noncomputable section

open scoped UpperHalfPlane MatrixGroups ModularForm

namespace GlobalTheory.QFam

def HasQ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f τ)

def IsFam {ι : Type} (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ) : Prop :=
  ∀ (i : ι) (γ : SL(2, ℤ)), (f i) ∣[w] γ = f (act i γ)

def IsRAct {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  (∀ i, act i 1 = i) ∧ ∀ i γ δ, act (act i γ) δ = act i (γ * δ)

def ActBij {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  ∀ γ, Function.Bijective fun i => act i γ

def conv (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

def spread (M : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if M ∣ n then a (n / M) else 0

def QAll (p : ℂ → Prop) (N : ℕ) (f : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ ∀ n, p (a n)

def QConj (g : ℂ ≃+* ℂ) (N : ℕ) (f f' : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ HasQ N f' fun n => g (a n)

def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    have hs : s = 0 := by
      have : s * τ.im = 0 := by simpa using him
      exact (mul_eq_zero.mp this).resolve_right τ.im_pos.ne'
    subst hs
    exact ⟨rfl, by simpa using hre⟩

theorem IsRAct.actBij {ι : Type} {act : ι → SL(2, ℤ) → ι} (h : IsRAct act) : ActBij act := by
  obtain ⟨hone, hmul⟩ := h
  intro γ
  refine Function.bijective_iff_has_inverse.mpr ⟨fun i => act i γ⁻¹, fun i => ?_, fun i => ?_⟩
  · show act (act i γ) γ⁻¹ = i
    rw [hmul, mul_inv_cancel, hone]
  · show act (act i γ⁻¹) γ = i
    rw [hmul, inv_mul_cancel, hone]

theorem hasQ_iff (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) :
    HasQ N f a ↔ ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n) (f τ) := by
  have key : ∀ (τ : ℍ) (n : ℕ), Complex.exp (2 * Real.pi * Complex.I * n * τ / N)
      = Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n := by
    intro τ n
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [HasQ, key]

end GlobalTheory.QFam
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.Sandwich

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

abbrev Ainf : Type := WittVector p (PreTilt O p)

def phiInv : Ainf p O →+* Ainf p O :=
  WittVector.map ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p)

def ofPadic : ℤ_[p] →+* Ainf p O :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt O p))).comp (WittVector.equiv p).symm.toRingHom

def padicToO : ℤ_[p] →+* O := (fontaineTheta O p).comp (ofPadic p O)

variable {p O}

def root (ε : PreTilt O p) : PreTilt O p := (_root_.frobeniusEquiv (PreTilt O p) p).symm ε

def mu (ε : PreTilt O p) : Ainf p O := teichmuller p ε - 1

def nu (ε : PreTilt O p) : Ainf p O := teichmuller p (root ε) - 1

def xi (ε : PreTilt O p) : Ainf p O := ∑ i ∈ Finset.range p, teichmuller p (root ε) ^ i

theorem _root_.GlobalTheory.Sandwich.xi_mul_nu (ε : PreTilt O p) :
    _root_.GlobalTheory.Sandwich.xi ε * _root_.GlobalTheory.Sandwich.nu ε = _root_.GlobalTheory.Sandwich.mu ε := by
  unfold _root_.GlobalTheory.Sandwich.xi _root_.GlobalTheory.Sandwich.nu _root_.GlobalTheory.Sandwich.mu
  rw [geom_sum_mul, ← map_pow]
  congr 2
  unfold _root_.GlobalTheory.Sandwich.root
  rw [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]

theorem _root_.GlobalTheory.Sandwich.phiInv_mu (ε : PreTilt O p) :
    _root_.GlobalTheory.Sandwich.phiInv p O (_root_.GlobalTheory.Sandwich.mu ε) = _root_.GlobalTheory.Sandwich.nu ε := by
  unfold _root_.GlobalTheory.Sandwich.phiInv _root_.GlobalTheory.Sandwich.mu _root_.GlobalTheory.Sandwich.nu
  rw [map_sub, map_one, WittVector.map_teichmuller]
  rfl

structure Datum (ε : PreTilt O p) (h : ℕ) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] where

  F : Matrix (Fin h) (Fin h) (Ainf p O)

  G : Matrix (Fin h) (Fin h) (Ainf p O)

  Ψ : Matrix (Fin h) (Fin h) (Ainf p O)

  Ψ' : Matrix (Fin h) (Fin h) (Ainf p O)

  ρT : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]

  ρM : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O)
  G_mul_F : G * F = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))
  F_eq : F = Ψ * F.map (phiInv p O)
  Ψ_mul : Ψ * Ψ' = xi ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))
  F_act : ∀ a, F * (ρT a).map (ofPadic p O) = ρM a * F

def etale (ε : PreTilt O p) (h : ℕ) : Datum ε h ℤ_[p] where
  F := 1
  G := mu ε • 1
  Ψ := 1
  Ψ' := xi ε • 1
  ρT := Algebra.ofId _ _
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (algebraMap _ _)
  G_mul_F := by simp
  F_eq := by simp
  Ψ_mul := by simp
  F_act := by intro a; simp [Algebra.ofId_apply]

namespace Datum

variable {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)

def al : (Fin h → O) →ₗ[O] (Fin h → O) := Matrix.toLin' (D.F.map (fontaineTheta O p))

def bb : (Fin h → O) →ₗ[O] (Fin h → O) := Matrix.toLin' (D.G.map (fontaineTheta O p))

def Fil : Submodule O (Fin h → O) := LinearMap.ker D.bb

def Lie : Submodule O (Fin h → O) := LinearMap.range D.bb

def Tsub (τ : Λ →+* O) : Submodule O (Fin h → O) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((D.ρT a).map (padicToO p O))) (τ a)

def Hsub (τ : Λ →+* O) : Submodule O (Fin h → O) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((D.ρM a).map (fontaineTheta O p))) (τ a)

def W (τ : Λ →+* O) : Submodule O (Fin h → O) := D.Tsub τ ⊓ LinearMap.ker D.al

end Datum

end GlobalTheory.Sandwich
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
noncomputable section

open MvPolynomial
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1

abbrev Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

abbrev Poly (n : ℕ) : Type := MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ

variable {n : ℕ}

def ev (g : Mat n) : Poly n →+* ℂ :=
  MvPolynomial.eval (Sum.elim (fun x : Fin n × Fin n => g x.1 x.2) (fun x => star (g x.1 x.2)))

abbrev Mode (ε : Fin n → Bool) : Type := {x : Fin n × Fin n // ε x.1 = true ∧ ε x.2 = false}

def nMode (ε : Fin n → Bool) : ℕ := Fintype.card (Mode ε)

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

def barM (ε : Fin n → Bool) (Z : Mat n) : Mat n := fun a b => -(sg ε a * sg ε b * Z b a)

def LieU (ε : Fin n → Bool) (Z : Mat n) : Prop := ∀ a b, (starRingEnd ℂ) (Z a b) = barM ε Z a b

def dZ (ε : Fin n → Bool) (Z : Mat n) : Derivation ℂ (Poly n) (Poly n) :=
  mkDerivation ℂ (Sum.elim
    (fun x : Fin n × Fin n => ∑ c, (X (Sum.inl (x.1, c)) * C (Z c x.2) - C (Z x.1 c) * X (Sum.inl (c, x.2))))
    (fun x : Fin n × Fin n =>
      ∑ c, (X (Sum.inr (x.1, c)) * C (barM ε Z c x.2) - C (barM ε Z x.1 c) * X (Sum.inr (c, x.2)))))

def dM (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (Poly n) (Poly n) := dZ ε (Matrix.single x.1.2 x.1.1 1)

def rM (ε : Fin n → Bool) (g : Mat n) : ℝ := ∑ x : Mode ε, ‖g x.1.1 x.1.2‖ ^ 2

def rP (ε : Fin n → Bool) : Poly n := ∑ x : Mode ε, X (Sum.inl x.1) * X (Sum.inr x.1)

def OmP (ε : Fin n → Bool) : Matrix (Mode ε) (Mode ε) (Poly n) := fun x y => dM ε x (X (Sum.inr y.1))

def detbP (n : ℕ) : Poly n := (Matrix.of fun a b : Fin n => (X (Sum.inr (a, b)) : Poly n)).det

def blockAlg (ε : Fin n → Bool) : Subalgebra ℂ (Poly n) :=
  Algebra.adjoin ℂ {P | ∃ a b, ε a = ε b ∧ P = X (Sum.inl (a, b))}

def topP (ε : Fin n → Bool) (M : ℕ) (P : Poly n) : Poly n := detbP n ^ M * P * (OmP ε).det

def prev (q : ℕ → Poly n) : ℕ → Poly n
  | 0 => 0
  | k + 1 => q k

def IsKoszul (ε : Fin n → Bool) (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n) : Prop :=
  (∀ k : ℕ, ((k : Poly n) + 1) * p (k + 1) + rP ε * p k = ∑ x, (dM ε x (q x k) + dM ε x (rP ε) * prev (q x) k)) ∧
    (∀ k, nMode ε < k → p k = 0) ∧ ∀ x k, nMode ε ≤ k → q x k = 0

def IsCutFn (H : ℝ → ℝ) : Prop := ContDiff ℝ ∞ H ∧ ∃ R : ℝ, ∀ x, R ≤ x → H x = 0

def bas (ε : Fin n → Bool) (H : ℝ → ℝ) (P : Poly n) : Mat n → ℂ := fun g => (H (rM ε g) : ℂ) * ev g P

def adBas (ε : Fin n → Bool) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n) : Mat n → ℂ := fun g =>
  bas ε (deriv H) (dZ ε Z (rP ε) * P) g + bas ε H (dZ ε Z P) g

def ShapeM (ε : Fin n → Bool) (d : ℕ) : Submodule ℂ (Mat n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (H : ℝ → ℝ) (P : Poly n), IsCutFn H ∧ P.totalDegree ≤ d ∧ φ = bas ε H P}

def AdSpanM (ε : Fin n → Bool) : Submodule ℂ (Mat n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (Z : Mat n) (H : ℝ → ℝ) (P : Poly n), LieU ε Z ∧ IsCutFn H ∧ φ = adBas ε Z H P}

def IsProfile (N : ℕ) (G : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ G ∧ (∀ x, 1 ≤ x → G x = 0) ∧ (∀ x, 0 ≤ iteratedDeriv N G x) ∧ 0 < iteratedDeriv N G 0

def famF (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n) (t : ℝ) : Mat n → ℂ := fun g =>
  ∑ k ∈ Finset.range (nMode ε + 1), bas ε (iteratedDeriv k fun x => G (t * x)) (p k) g

def dMode (ε : Fin n → Bool) (θ : Fin n → ℝ) : ℝ :=
  ∏ x : Mode ε, ‖Complex.exp (θ x.1.1 * Complex.I) - Complex.exp (θ x.1.2 * Complex.I)‖ ^ 2

def StAlg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : ℕ) (P : Poly n), P ∈ blockAlg ε →
    ∃ (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n), IsKoszul ε p q ∧ p (nMode ε) = topP ε M P

def StProfile : Prop := ∀ N : ℕ, ∃ G : ℝ → ℝ, IsProfile N G

def StFam : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n), IsProfile (nMode ε) G →
    ∃ d : ℕ, (∀ k, k ≤ nMode ε → (p k).totalDegree ≤ d) ∧
      ∀ t : ℝ, 0 < t → famF ε G p t ∈ ShapeM ε d ∧ ∀ g : Mat n, 1 < t * rM ε g → famF ε G p t g = 0

def StHomot : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n), IsProfile (nMode ε) G →
    IsKoszul ε p q → ∀ t : ℝ, 1 ≤ t → famF ε G p 1 - famF ε G p t ∈ AdSpanM ε

def StBasDeriv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n), LieU ε Z → IsCutFn H →
    adBas ε Z H P ∈ ShapeM ε (P.totalDegree + 2) ∧ ∀ (g : Mat n) (s : ℝ),
      HasDerivAt (fun u : ℝ => bas ε H P (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)))
        (adBas ε Z H P (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) s

end GlobalTheory.PsCo.Pc1

end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.PsCo.Pc1.A

abbrev EntIdx (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

abbrev PolyL (n L : ℕ) := MvPolynomial (Fin L ⊕ EntIdx n) ℂ

abbrev PolyM (n L : ℕ) := MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ

variable {n L : ℕ}

def inL (n L : ℕ) : Poly n →ₐ[ℂ] PolyL n L := rename Sum.inr

def inM (n L : ℕ) : PolyL n L →ₐ[ℂ] PolyM n L := rename some

def laL (n : ℕ) (i : Fin L) : PolyL n L := X (Sum.inl i)

def muM (n L : ℕ) : PolyM n L := X none

def dL (L : ℕ) (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (PolyL n L) (PolyL n L) :=
  mkDerivation ℂ (Sum.elim (fun _ => 0) (fun v => inL n L (dM ε x (X v))))

def dMu (L : ℕ) (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (PolyM n L) (PolyM n L) :=
  mkDerivation ℂ (fun w => match w with
    | none => 0
    | some v => inM n L (dL L ε x (X v)))

def coefM (n L : ℕ) (k : ℕ) : PolyM n L →ₗ[ℂ] PolyL n L :=
  ((Polynomial.lcoeff (PolyL n L) k).restrictScalars ℂ).comp (optionEquivLeft ℂ (Fin L ⊕ EntIdx n)).toLinearMap

def allOnes (L : ℕ) : Fin L →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

def exL (n L : ℕ) : PolyL n L →ₗ[ℂ] Poly n :=
  ((MvPolynomial.lcoeff (Poly n) (allOnes L)).restrictScalars ℂ).comp (sumAlgEquiv ℂ (Fin L) (EntIdx n)).toLinearMap

end GlobalTheory.PsCo.Pc1.A

end
end

section

noncomputable section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

def T_dual_prod : Prop := ∀ {A : Type} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A) {L : ℕ} (la m : Fin L → A)
    (J : Ideal A), (∀ i, D (la i) = 0) → (∀ i, la i ^ 2 ∈ J) →
    D (∏ i, (1 + la i * m i)) - (∏ i, (1 + la i * m i)) * ∑ i, la i * D (m i) ∈ J

def T_dM_comm : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (w x : Mode ε) (P : Poly n), dM ε w (dM ε x P) = dM ε x (dM ε w P)

def BlockDeterminantCondition : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (a b : Fin n), ε a = ε b →
    ∃ c : Mode ε → Mode ε → ℂ, ∀ x, dM ε x (X (Sum.inl (a, b))) = ∑ y, C (c x y) * X (Sum.inl y.1)

def T_dM_detb : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (x : Mode ε), dM ε x (detbP n) = 0

def T_exL_dL : Prop := ∀ {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) (b : PolyL n L),
    exL n L (dL L ε x b) = dM ε x (exL n L b)

def T_exL_dual : Prop := ∀ {n L : ℕ} (m : Fin L → Poly n) (a : Poly n),
    exL n L ((∏ i, (1 + laL n i * inL n L (m i))) * inL n L a) = (∏ i, m i) * a

def T_coefM_dMu : Prop := ∀ {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) (k : ℕ) (s : PolyM n L),
    coefM n L k (dMu L ε x s) = dL L ε x (coefM n L k s)

def T_coefM_pderiv : Prop := ∀ {n L : ℕ} (k : ℕ) (s : PolyM n L),
    coefM n L k (pderiv none s) = ((k : ℂ) + 1) • coefM n L (k + 1) s

def T_coefM_pencil : Prop := ∀ {n L : ℕ} {I : Type} [Fintype I] [DecidableEq I] (A0 B0 : Matrix I I (PolyL n L)),
    let Z : Matrix I I (PolyM n L) := fun x y => muM n L * inM n L (A0 x y) + inM n L (B0 x y)
    (∀ k, Fintype.card I < k → coefM n L k Z.det = 0) ∧ coefM n L (Fintype.card I) Z.det = A0.det ∧
      ∀ k x y, Fintype.card I ≤ k → coefM n L k (Z.adjugate y x) = 0

end GlobalTheory.PsCo.Cw2a

end
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
noncomputable section

namespace GlobalTheory.LKTorus

variable (k : Type) [Field k] {A : Type} [CommRing A] [Algebra k A]

def simT (c : A →ₐ[k] A) : Subgroup Aˣ where
  carrier := {x | ∃ t : kˣ, (x : A) * c x = algebraMap k A t}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s * t, ?_⟩
    simp only [Units.val_mul, map_mul]
    rw [show (x : A) * y * (c x * c y) = (x * c x) * (y * c y) by ring, hs, ht]
  inv_mem' := by
    rintro x ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    have h1 : ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * algebraMap k A s = 1 := by
      rw [← hs, show ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * ((x : A) * c x)
          = (((x⁻¹ : Aˣ) : A) * x) * c (((x⁻¹ : Aˣ) : A) * x) by rw [map_mul]; ring]
      simp
    calc ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A)
        = ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * (algebraMap k A s * algebraMap k A ((s⁻¹ : kˣ) : k)) := by
          rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = algebraMap k A ((s⁻¹ : kˣ) : k) := by rw [← mul_assoc, h1, one_mul]

end GlobalTheory.LKTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer

variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E'']

def holSub (W : Opens E) : Subalgebra ℂ (W → ℂ) where
  carrier := {f | ∃ F : E → ℂ, AnalyticOnNhd ℂ F W ∧ ∀ p : W, f p = F p}
  mul_mem' := by
    rintro f g ⟨F, hF, e⟩ ⟨G, hG, e'⟩
    exact ⟨fun p ↦ F p * G p, hF.mul hG, fun p ↦ by simp [e, e']⟩
  add_mem' := by
    rintro f g ⟨F, hF, e⟩ ⟨G, hG, e'⟩
    exact ⟨fun p ↦ F p + G p, hF.add hG, fun p ↦ by simp [e, e']⟩
  algebraMap_mem' c := ⟨fun _ ↦ c, analyticOnNhd_const, fun _ ↦ rfl⟩

abbrev Hol (W : Opens E) : Type := holSub W

namespace Hol

variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''}

open Classical in
def fn (f : Hol W) (p : E) : ℂ := by
  classical
  exact if h : p ∈ W then f.1 ⟨p, h⟩ else 0

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fn_of_mem (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (h : p ∈ W) :
    f.fn p = f.1 ⟨p, h⟩ := by
  simp [_root_.GlobalTheory.AnPer.Hol.fn, h]

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.ext_fn {f g : _root_.GlobalTheory.AnPer.Hol W}
    (h : ∀ p ∈ W, f.fn p = g.fn p) : f = g := by
  refine Subtype.ext (funext fun p ↦ ?_)
  have hp := h p p.2
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f p.2, _root_.GlobalTheory.AnPer.Hol.fn_of_mem g p.2] at hp
  exact hp

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.analytic (f : _root_.GlobalTheory.AnPer.Hol W) :
    AnalyticOnNhd ℂ f.fn W := by
  obtain ⟨F, hF, e⟩ : ∃ F : E → ℂ, AnalyticOnNhd ℂ F W ∧ ∀ p : W, f.1 p = F p := f.2
  intro p hp
  refine (hF p hp).congr ?_
  filter_upwards [W.isOpen.mem_nhds hp] with q hq
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f hq, e]

def mk (F : E → ℂ) (h : AnalyticOnNhd ℂ F W) : Hol W := ⟨fun p ↦ F p, F, h, fun _ ↦ rfl⟩

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fn_mk (F : E → ℂ) (h : AnalyticOnNhd ℂ F W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.mk F h).fn p = F p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

def ev (p : E) (hp : p ∈ W) : Hol W →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : W ↦ ℂ) ⟨p, hp⟩).comp (holSub W).val

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.ev_apply (p : E) (hp : p ∈ W) (f : _root_.GlobalTheory.AnPer.Hol W) :
    _root_.GlobalTheory.AnPer.Hol.ev p hp f = f.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f hp]
  rfl

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fn_add (f g : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (f + g).fn p = f.fn p + g.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fn_mul (f g : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (f * g).fn p = f.fn p * g.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fn_smul (c : ℂ) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (c • f).fn p = c * f.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fn_algebraMap (c : ℂ) {p : E} (hp : p ∈ W) :
    (algebraMap ℂ (_root_.GlobalTheory.AnPer.Hol W) c).fn p = c := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

def comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W') (h : ∀ p ∈ W', Φ p ∈ W) : Hol W →ₐ[ℂ] Hol W' where
  toFun f := ⟨fun p ↦ f.1 ⟨Φ p, h p p.2⟩, fun p ↦ f.fn (Φ p), f.analytic.comp hΦ h,
    fun p ↦ (fn_of_mem f (h p p.2)).symm⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fn_comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W') (h : ∀ p ∈ W', Φ p ∈ W)
    (f : _root_.GlobalTheory.AnPer.Hol W) {p : E'} (hp : p ∈ W') :
    (_root_.GlobalTheory.AnPer.Hol.comap Φ hΦ h f).fn p = f.fn (Φ p) := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  exact (_root_.GlobalTheory.AnPer.Hol.fn_of_mem f (h p hp)).symm

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fderiv_fn_congr (f : _root_.GlobalTheory.AnPer.Hol W) {F : E → ℂ}
    (e : ∀ q ∈ W, f.fn q = F q) {p : E} (hp : p ∈ W) :
    fderiv ℂ f.fn p = fderiv ℂ F p := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [W.isOpen.mem_nhds hp] with q hq using e q hq

def derFun (v : E) (f : Hol W) : Hol W :=
  mk (fun p ↦ fderiv ℂ f.fn p v) fun p hp ↦
    ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp (f.analytic p hp).fderiv

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fn_derFun (v : E) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.derFun v f).fn p =
      fderiv ℂ f.fn p v :=
  _root_.GlobalTheory.AnPer.Hol.fn_mk _ _ hp

def der (v : E) : Derivation ℂ (Hol W) (Hol W) :=
  Derivation.mk'
    { toFun := derFun v
      map_add' f g := ext_fn fun p hp ↦ by
        rw [fn_add _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
          fderiv_fn_congr (f + g) (F := fun q ↦ f.fn q + g.fn q) (fun q hq ↦ fn_add f g hq) hp,
          fderiv_fun_add (f.analytic p hp).differentiableAt (g.analytic p hp).differentiableAt]
        rfl
      map_smul' c f := ext_fn fun p hp ↦ by
        rw [RingHom.id_apply, fn_smul _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
          fderiv_fn_congr (c • f) (F := fun q ↦ c * f.fn q) (fun q hq ↦ fn_smul c f hq) hp,
          fderiv_const_mul (f.analytic p hp).differentiableAt]
        rfl }
    fun f g ↦ ext_fn fun p hp ↦ by
      change (derFun v (f * g)).fn p = (f * derFun v g + g * derFun v f).fn p
      rw [fn_add _ _ hp, fn_mul _ _ hp, fn_mul _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
        fderiv_fn_congr (f * g) (F := fun q ↦ f.fn q * g.fn q) (fun q hq ↦ fn_mul f g hq) hp,
        fderiv_fun_mul (f.analytic p hp).differentiableAt (g.analytic p hp).differentiableAt]
      rfl

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fn_der (v : E) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.der v f).fn p =
      fderiv ℂ f.fn p v :=
  _root_.GlobalTheory.AnPer.Hol.fn_derFun v f hp

set_option autoImplicit false in
theorem _root_.GlobalTheory.AnPer.Hol.fn_der_comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W')
    (h : ∀ p ∈ W', Φ p ∈ W) (v : E') (f : _root_.GlobalTheory.AnPer.Hol W) {p : E'} (hp : p ∈ W') :
    (_root_.GlobalTheory.AnPer.Hol.der v (_root_.GlobalTheory.AnPer.Hol.comap Φ hΦ h f)).fn p =
      fderiv ℂ f.fn (Φ p) (fderiv ℂ Φ p v) := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_der v _ hp,
    _root_.GlobalTheory.AnPer.Hol.fderiv_fn_congr _ (F := f.fn ∘ Φ)
      (fun q hq ↦ _root_.GlobalTheory.AnPer.Hol.fn_comap Φ hΦ h f hq) hp,
    fderiv_comp p (f.analytic (Φ p) (h p hp)).differentiableAt
      (hΦ p hp).differentiableAt]
  rfl

end Hol

end GlobalTheory.AnPer
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair
noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HenQ

def eulerL (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏' w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
    ((B w.1).map fun b => (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod

def eulerLd (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  eulerL K (fun w => (B w).map (·⁻¹)) S (1 - s)

end GlobalTheory.HenQ
end
end
