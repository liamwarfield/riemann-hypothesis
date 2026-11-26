module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.SummandSlopeAtDecoratedLattice

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.ChainLawPhi
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

section PhiLaw

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def PhiGSLaw (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) : Prop :=
  ∀ γ ∈ LocE.JGsym P q k₀ rS r t n c, ∀ κ ∈ LocE.JGsym P q k₀ rS r t n' c', ∀ x : HomE E (n' + c') (n + c),
    LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) =
      LocE.lamGBS q ψ₀ χ k₀ r t j n c γ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det γ : Eˣ) : E))⁻¹ *
        (LocE.lamGBS q ψ₀ χ k₀ r t (j - 1) n' c' κ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det κ : Eˣ) : E))⁻¹) *
          LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x

structure PhiGSLawHyp (P : HeightOneSpectrum (𝓞 E)) (q k₀ rS r t j c' n' c n : ℕ) : Prop where
  hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal
  hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2
  hj : 1 ≤ j
  hk' : k₀ ≤ n'
  hk : k₀ ≤ n
  hr : k₀ + rS < r
  ht : 0 < t
  hsrc : n' + c' = r + (j - 1) * t
  htgt : n + c = r + j * t

end PhiLaw

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.ChainOne
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def oneIdx (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (m2 : ℕ) : ChIdx X Pr R Q where
  β j := {_u : Unit // j ≤ m2 + 1}
  h _ _ _ := 1
  levG j _ := Λ j
  levQ j _ := LevQFam.top X.E X.K (R.N j) Q

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)


open Classical in
def OneYbSym (m2 : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    PsiAt Ch sel mu cst m2 P 1 x₀ y' ≠ 0 →
      ∀ l : Fin (R.N (m2 + 1)), IntAt P.1 ((qOf P.1 : X.E) * y' l) ∧ redP P.1 ((qOf P.1 : X.E) * y' l) = if l.1 = R.k then 1 else 0

variable {Ch sel mu cst Λ}

end One

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.CardFilterNeighboursEqPaths
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section Paths

theorem double_sum_eq_of_filter_card {α M : Type} [DecidableEq α] [AddCommMonoid M] (A A' : Finset α) (B B' : α → Finset α) (φ : α → M)
    (h : ∀ f, (A.filter fun e => f ∈ B e).card = (A'.filter fun e => f ∈ B' e).card) :
    ∑ e ∈ A, ∑ f ∈ B e, φ f = ∑ e ∈ A', ∑ f ∈ B' e, φ f := by

  have key : ∀ (A : Finset α) (B : α → Finset α) (U : Finset α), (∀ e ∈ A, B e ⊆ U) →
      ∑ e ∈ A, ∑ f ∈ B e, φ f = ∑ f ∈ U, (A.filter fun e => f ∈ B e).card • φ f := by
    intro A B U hU
    rw [Finset.sum_comm' (t' := U) (s' := fun f => A.filter fun e => f ∈ B e)]
    · simp only [Finset.sum_const]
    · intro e f
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, hf⟩
        exact ⟨⟨he, hf⟩, hU e he hf⟩
      · rintro ⟨⟨he, hf⟩, -⟩
        exact ⟨he, hf⟩
  set U := A.biUnion B ∪ A'.biUnion B'
  rw [key A B U (fun e he => (Finset.subset_biUnion_of_mem B he).trans Finset.subset_union_left),
    key A' B' U (fun e he => (Finset.subset_biUnion_of_mem B' he).trans Finset.subset_union_right)]
  exact Finset.sum_congr rfl fun f _ => by rw [h f]

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


open Classical in
def decorationPathCount (P Q : Ideal (𝓞 E)) (i j : ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : ℕ :=
  ((d.heckeNb P i).filter fun e => f ∈ e.heckeNb Q j).card

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

open Classical in
theorem card_filter_neighbours_eq_paths (c : DecoPts S E n ST SG) (P Q : Ideal (𝓞 E)) (i j : ℕ) (d f : S.D) :
    ((c.nb P i d).filter fun e => f ∈ c.nb Q j e).card = decorationPathCount P Q i j (c.pts d) (c.pts f) := by
  show ((((c.pts d).heckeNb P i).map c.pts.symm.toEmbedding).filter fun e => f ∈ c.nb Q j e).card = _
  rw [Finset.filter_map, Finset.card_map]
  unfold decorationPathCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Function.comp_apply, Equiv.toEmbedding_apply, DecoPts.mem_nb,
    Equiv.apply_symm_apply]

theorem heckeOperators_commute_of_paths (c : DecoPts S E n ST SG) (P Q : Ideal (𝓞 E)) (i j : ℕ)
    (h : ∀ d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), decorationPathCount P Q i j d f = decorationPathCount Q P j i d f) :
    Commute (heckeD c P i).op (heckeD c Q j).op := by
  classical
  refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
  show (((heckeD c P i).op ((heckeD c Q j).op φ) : S.EqFun) : S.D → S.V) d =
    (((heckeD c Q j).op ((heckeD c P i).op φ) : S.EqFun) : S.D → S.V) d
  simp only [heckeD, LocOp.ofNbr_op_apply, LinearMap.id_apply]
  refine double_sum_eq_of_filter_card _ _ _ _ _ fun f => ?_
  rw [card_filter_neighbours_eq_paths, card_filter_neighbours_eq_paths, h]

def DecorationPathSymmetry (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ P Q : HeightOneSpectrum (𝓞 E), conjPrime₂ P ≠ P → conjPrime₂ Q ≠ Q →
    (∀ R : ST, R.1 ≠ P ∧ R.1 ≠ conjPrime₂ P) → (∀ w : SG, w.1 ≠ P ∧ w.1 ≠ conjPrime₂ P) →
    (∀ R : ST, R.1 ≠ Q ∧ R.1 ≠ conjPrime₂ Q) → (∀ w : SG, w.1 ≠ Q ∧ w.1 ≠ conjPrime₂ Q) →
    ∀ (i j : ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)), decorationPathCount P.asIdeal Q.asIdeal i j d f = decorationPathCount Q.asIdeal P.asIdeal j i d f

private lemma levOff_conjP_ne_and_ne_places {S0 : Set (HeightOneSpectrum (𝓞 E))} (x : LevOff ST SG S0) :
    conjPrime₂ x.1 ≠ x.1 ∧ (∀ R : ST, R.1 ≠ x.1 ∧ R.1 ≠ conjPrime₂ x.1) ∧ (∀ w : SG, w.1 ≠ x.1 ∧ w.1 ≠ conjPrime₂ x.1) := by
  obtain ⟨P, h1, h2, h3⟩ := x
  rw [conjIdeal_asIdeal] at h1 h3
  refine ⟨fun h => h1 (congrArg HeightOneSpectrum.asIdeal h), fun R => ⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · intro h
    have h' : R.1 = P := h
    apply h2
    rw [← h']
    exact Or.inl (Or.inr (Finset.mem_coe.2 R.2))
  · intro h
    exact h3 R.1 (Or.inl (Or.inr (Finset.mem_coe.2 R.2))) (congrArg HeightOneSpectrum.asIdeal h)
  · intro h
    have h' : w.1 = P := h
    apply h2
    rw [← h']
    exact Or.inr (Finset.mem_coe.2 w.2)
  · intro h
    exact h3 w.1 (Or.inr (Finset.mem_coe.2 w.2)) (congrArg HeightOneSpectrum.asIdeal h)

theorem heckeComm_of_paths (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) (h : DecorationPathSymmetry E n ST SG) :
    HeckeComm c S0 := by
  intro x y
  obtain ⟨hx1, hx2, hx3⟩ := levOff_conjP_ne_and_ne_places x.1
  obtain ⟨hy1, hy2, hy3⟩ := levOff_conjP_ne_and_ne_places y.1
  exact heckeOperators_commute_of_paths c _ _ _ _ fun d f => h x.1.1 y.1.1 hx1 hy1 hx2 hx3 hy2 hy3 x.2 y.2 d f

end Paths

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TwQThetaOpen
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

def lqPrinc (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (g : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ i j : Fin n, P.valuation E ((LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) - 1) i j) ≤
    WithZero.coe (Multiplicative.ofAdd (-(N : ℤ)))

def ThetaOpen {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q) : Prop :=
  ∀ P : Q, ∃ N : ℕ, 0 < N ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N (g : Sp E n ≃ₗ[E] Sp E n) →
    ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1

theorem thetaOpen_top (Q : Finset (HeightOneSpectrum (𝓞 E))) : ThetaOpen (LevQFam.top E K n Q) := by
  intro P
  exact ⟨1, Nat.one_pos, fun g _ => ⟨Subgroup.mem_top _, rfl⟩⟩

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TargetChF
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem chfok_false (hQ : Q = ∅) (P : Q) : False := by
  obtain ⟨p, hp⟩ := P
  simp [hQ] at hp

def chfokLift (hQ : Q = ∅) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : DecoF X.E n ST SG Q :=
  ⟨(d, fun _ => 1), fun P _ => (chfok_false hQ P).elim⟩

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

end Chain

end Formalism.L2.Col
end
end
