module

public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Columns.GoodXgFin
public import Formalism.LocalToGlobal.Columns.ColFormsLemmas
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.RowFormsSym
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section RBlockSym

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

def rPsymF : LevFam X.E X.K R.r Pr.vGs := fun w =>
  ⟨HPsymF (𝓞 X.E ⧸ w.1.asIdeal) R.r R.k R.rS, chiSymF (Ch.psi0 w) R.r R.k R.rS⟩

theorem rowTyG_PsymF_H (w : {w // w ∈ Pr.vGs}) :
    (rowTyG Ch (rPsymF Ch) w).H = HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := rfl

end RBlockSym

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.AtTLemmas
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section DiaMoves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

instance diaAction : MulAction (DiaG (E := E) (ST := ST)) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) where
  smul c d := d.dia c
  one_smul := DecoSet.dia_one
  mul_smul c c' d := DecoSet.dia_mul c c' d

theorem DecoSet.dia_smul_def (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : c • d = d.dia c := rfl

end DiaMoves

section OpsL

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

theorem diamond_action_apply (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (φ : (formGSD C Λ).EqFun) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    ((diamondOperatorOnForms' C Λ P c φ : (formGSD C Λ).EqFun) : (formGSD C Λ).D → (formGSD C Λ).V) d =
      (φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.dia1 P c) := by
  unfold diamondOperatorOnForms'
  exact LocOp.ofMap_op_apply (S := formGSD C Λ) (S' := formGSD C Λ) _ _ _ _ _ φ d


end OpsL

section ColsL

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem pow_mem {M : Type*} [AddCommGroup M] [Module X.K M] (p : Submodule X.K M)
    (A : Module.End X.K M) (h : ∀ φ ∈ p, A φ ∈ p) (k : ℕ) : ∀ φ ∈ p, (A ^ k) φ ∈ p := by
  induction k with
  | zero => intro φ hφ; simpa using hφ
  | succ k ih =>
    intro φ hφ
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (h φ hφ)

end ColsL

section SeenL

variable {X : Fields} {Pr : Primes X}

theorem mem_pullW (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) (x : 𝓞 X.E) :
    x ∈ (pullW τ w).asIdeal ↔ X.embO τ x ∈ w.asIdeal := Iff.rfl

theorem pullW_mem_vT (hPr : Pr.Ok) (u : Pr.Word) (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) :
    pullW τ w ∈ Pr.vT u ↔ X.embO τ (Pr.piT u) ∈ w.asIdeal :=
  mem_divs (hPr.piT_ne_zero u) _

theorem embO_of_Kq {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) (τ τ' : X.Tau) : X.embO τ x = X.embO τ' x :=
  RingOfIntegers.ext (hx τ τ')

theorem conjO_mem_Kq (hX : X.Ok) {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) : ((X.conjO x : 𝓞 X.E) : X.E) ∈ X.Kq := by
  intro τ τ'
  show X.emb τ (star (x : X.E)) = X.emb τ' (star (x : X.E))
  rw [hX.emb_star, hX.emb_star, hx τ τ']

theorem seenC_iff (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    seenC Pr u w ↔ ∀ τ, pullW τ w ∈ Pr.vT u :=
  forall_congr' fun τ => (pullW_mem_vT hPr u τ w).symm

theorem seenC_or_seenBarC (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) : seenC Pr u w ∨ seenBarC Pr u w := by
  by_cases hne : Nonempty X.Tau
  · obtain ⟨τ₀⟩ := hne
    have h1 : X.embO τ₀ (Pr.piT u) * X.embO τ₀ (X.conjO (Pr.piT u)) ∈ w.asIdeal := by
      rw [← map_mul, hPr.piT_norm u, map_natCast]
      exact hw
    rcases w.isPrime.mem_or_mem h1 with h | h
    · left
      intro τ
      rw [embO_of_Kq (hPr.piT_Kq u) τ τ₀]
      exact h
    · right
      intro τ
      rw [embO_of_Kq (conjO_mem_Kq hX (hPr.piT_Kq u)) τ τ₀]
      exact h
  · left
    intro τ
    exact absurd ⟨τ⟩ hne

theorem not_seen_both (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau)
    (h1 : X.embO τ (Pr.piT u) ∈ w.asIdeal) (h2 : X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal) : False := by
  obtain ⟨a, b, e⟩ := hPr.piT_cop u
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e' := congrArg (X.embO τ) e
  rw [map_add (f := _), map_mul, map_mul, map_one] at e'
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

variable {R : Ranks} (W : Wts X Pr.Word R)

end SeenL

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.RowFormsSel
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.EigenvalueLevelCeiling

section Sel

variable {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem rf_tup_fin : (Qprime (mu : Chr X.F X.E X.K)).Finite :=
  auxiliary_primes_finite X.F X.E X.K _ ((mem_tupGrp (mu : Chr X.F X.E X.K)).mp mu.2).1.2.1

theorem mem_QE (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ QE sel (mu : Chr X.F X.E X.K) ↔ ∃ v ∈ Qprime (mu : Chr X.F X.E X.K), sel v = P := by
  unfold QE
  rw [dite_eq_left (rf_tup_fin mu)]
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]

variable {sel}

end Sel

section Disj

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)


open Classical in
theorem QE_disj (hP : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) (w : HeightOneSpectrum (𝓞 X.E))
    (hw : w ∈ Pr.vGs) : w ∉ QE sel (mu : Chr X.F X.E X.K) := by
  intro hQ
  obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu w).mp hQ
  have hg : ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
    have key : ∀ i, sel v ∈ Pr.vG i → ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
      intro i hi
      have h0 : X.conjO (Pr.piG i) ≠ 0 := by
        intro h0
        have := hP.piG_norm i
        rw [h0, mul_zero] at this
        exact (Nat.cast_ne_zero.mpr (hP.g_prime i).ne_zero) this.symm
      rw [← hP.piG_norm i]
      exact Ideal.mul_mem_left _ _ ((mem_divs h0 _).mp hi)
    rcases Finset.mem_union.mp hw with h | h
    · exact ⟨0, key 0 h⟩
    · exact ⟨1, key 1 h⟩
  obtain ⟨i, hi⟩ := hg
  have h1 : ((Pr.g i : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v]
    show algebraMap (𝓞 X.F) (𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.F) ∈ (sel v).asIdeal
    rw [map_natCast]
    exact hi
  have h2 : plc v ∣ Pr.g i := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at h1
    exact (ringChar.spec _ _).mp h1
  have hpp : (plc v).Prime := by
    have : Finite (𝓞 X.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    have : v.asIdeal.IsPrime := v.isPrime
    exact CharP.char_is_prime (𝓞 X.F ⧸ v.asIdeal) (ringChar (𝓞 X.F ⧸ v.asIdeal))
  have h3 : plc v = Pr.g i := (Nat.prime_dvd_prime_iff_eq hpp (hP.g_prime i)).mp h2
  exact (mu.good hv).2.2 (h3 ▸ hS i)

end Disj

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.AtTOwedC
open NumberField IsDedekindDomain IntermediateField Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

section Res

variable {A : Type} [CommRing A] [Finite A] {p : ℕ}

def owedC_res (hp : p.Prime) (h : Nat.card A = p) : A ≃+* ZMod p :=
  letI := Fintype.ofFinite A
  (ZMod.ringEquivOfPrime A hp (by rw [← Nat.card_eq_fintype_card]; exact h)).symm

theorem owedC_res_intCast (hp : p.Prime) (h : Nat.card A = p) (a : ℤ) :
    owedC_res hp h (a : A) = (a : ZMod p) := map_intCast _ _

theorem owedC_exists_int (hp : p.Prime) (h : Nat.card A = p) (x : A) : ∃ a : ℤ, x = (a : A) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨((owedC_res hp h x).val : ℤ), ?_⟩
  apply (owedC_res hp h).injective
  rw [owedC_res_intCast]
  simp

theorem owedC_intCast_eq_iff (hp : p.Prime) (h : Nat.card A = p) (a b : ℤ) :
    (a : A) = (b : A) ↔ (p : ℤ) ∣ a - b := by
  rw [← (owedC_res hp h).injective.eq_iff, owedC_res_intCast, owedC_res_intCast,
    ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]

variable {K : Type} [Field K]

end Res

section Chars

variable {X : Fields} {Pr : Primes X}

theorem card_quotient_eq_prime (hPr : Pr.Ok) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := by
  rw [← hPr.vT_norm u P.1 P.2, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end Chars

section Weil

variable {X : Fields} {Pr : Primes X}

def CharT.psiC (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    AddChar (𝓞 X.E ⧸ P.1.asIdeal) ℂ :=
  (σ₀ : X.K →* ℂ).compAddChar (Ps.psiT u P)

theorem CharT.psiC_apply (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u})
    (c : 𝓞 X.E ⧸ P.1.asIdeal) : Ps.psiC σ₀ u P c = σ₀ (Ps.psiT u P c) := rfl

theorem CharT.Ok.psiC_ne {Ps : CharT X Pr} (h : Ps.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Ps.psiC σ₀ u P ≠ 1 := by
  intro h1
  apply h.ne u P
  ext c
  apply σ₀.injective
  rw [← CharT.psiC_apply, h1, AddChar.one_apply, AddChar.one_apply, map_one]

end Weil

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end Gauss

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.ExistsUnitOfPowEqOne
open Polynomial CategoryTheory NumberField

noncomputable section

namespace Formalism.L2.Col

section Rep

variable {Γ : Type} [Group Γ] [Fintype Γ]

end Rep

section Series

variable {g : ℕ} [Fact g.Prime]

end Series

section Assemble

theorem residueField_equiv_zmod {X : Fields} (w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.E)) (g : ℕ) [Fact g.Prime]
    (hw : Ideal.absNorm w.asIdeal = g) : Nonempty ((𝓞 X.E ⧸ w.asIdeal) ≃+* ZMod g) := by
  have hc : Nat.card (𝓞 X.E ⧸ w.asIdeal) = g := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 X.E ⧸ w.asIdeal) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (Fact.out : g.Prime).ne_zero)
  letI : Fintype (𝓞 X.E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc' : Fintype.card (𝓞 X.E ⧸ w.asIdeal) = g := by rw [← Nat.card_eq_fintype_card, hc]
  have : CharP (𝓞 X.E ⧸ w.asIdeal) g := charP_of_card_eq_prime hc'
  exact ⟨(ZMod.ringEquiv _ hc').symm⟩

def generalLinearEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S] (r : ℕ) (e : R ≃+* S) : GL (Fin r) R ≃* GL (Fin r) S :=
  Units.mapEquiv (e.mapMatrix (m := Fin r)).toMulEquiv

end Assemble

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.SmulMemTrpSet
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Coord

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

structure CoordAt (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)) : Prop where
  add : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, co (x + y) = co x + co y
  smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, co (a • x) = Ideal.Quotient.mk P.asIdeal a • co x
  off : ∀ x, x ∉ localization₂ P.asIdeal N → co x = 0
  surj : ∀ c, ∃ x ∈ N, co x = c
  ker : ∀ x ∈ N, co x = 0 → x ∈ P.asIdeal • N

structure FunAt (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (f : Sp E n → 𝓞 E ⧸ P.asIdeal) : Prop where
  add : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, f (x + y) = f x + f y
  smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, f (a • x) = Ideal.Quotient.mk P.asIdeal a * f x
  off : ∀ x, x ∉ localization₂ P.asIdeal N → f x = 0

def coF {P : HeightOneSpectrum (𝓞 E)} (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)) (c : Fin n → 𝓞 E ⧸ P.asIdeal)
    (y : Sp E n) : 𝓞 E ⧸ P.asIdeal := ∑ i, c i * co y i

def dualV {κ : Type} [CommRing κ] (x : Fin n → κ) : Fin n → κ := Classical.epsilon fun c => ∑ i, c i * x i = 1

def liftV {P : HeightOneSpectrum (𝓞 E)} (N : Submodule (𝓞 E) (Sp E n)) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal))
    (x : Fin n → 𝓞 E ⧸ P.asIdeal) : Sp E n := Classical.epsilon fun y => y ∈ N ∧ co y = x

end Coord

section Fib

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.fibF (d : Deco E n ST SG) (P : ST) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (c : Fin n → 𝓞 E ⧸ P.1.asIdeal) : Deco E n ST SG := d.repl P d.N (coF co c)

def DecoSet.fibF (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (c : Fin n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) :=
  open Classical in if h : (d.1.fibF P co c).Ok then ⟨_, h⟩ else d

def DecoSet.fibX (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (q : 𝓞 E) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (x : Fin n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) :=
  (d.fibF P co (dualV x)).up P q (liftV d.1.N co x)

structure SepElt (ST : Finset (HeightOneSpectrum (𝓞 E))) (a : 𝓞 E) : Prop where
  conj : ∀ P : ST, cO (E := E) a ∈ P.1.asIdeal
  off : ∀ P : ST, a ∉ P.1.asIdeal

end Fib

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

variable {C Λ}

def resX {R : Type} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (P : ST) (q : 𝓞 X.E)
    (co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)) (ℓ : C.V → R) (φ : (formGSD C Λ).EqFun) :
    (Fin n → 𝓞 X.E ⧸ P.1.asIdeal) → R :=
  fun x => ℓ ((φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.fibX P q co x))

end Ops

@[reducible] def resField {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal

@[reducible] def resFintype {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _

section Below

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ} (emb : ι → E →+* K)

def SameBelow (w : HeightOneSpectrum (𝓞 K)) (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ τ, (∀ x ∈ L, ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L') ∧
    ∀ x ∈ L', ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L

end Below

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end Cols

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

namespace RowPar

variable {R : Ranks} (S : RowPar R)

def lamWQ (i : Fin R.r) : ℚ := S.aPlus R.m (i.1 + 1) + (R.nV : ℚ) / 2 - S.eAt (R.m - 1)

def lamW : DomWeight R.r := ofQ S.lamWQ

end RowPar

namespace Wts

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

def lamW (τ : X.Tau) : DomWeight R.r := (W.row τ).lamW

end Wts

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

def wmVal (SG : Finset (HeightOneSpectrum (𝓞 X.E))) : CoefPk X R.r (DecoSet (E := X.E) (n := R.r) (ST := ∅) (SG := SG)) :=
  roundPk X W.lamW fun d => d.1.N

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)


variable (R) in
def wmTyQ (Q : Finset (HeightOneSpectrum (𝓞 X.E))) : LevFam X.E X.K R.r Q := fun _ => ⟨⊤, 1⟩

def wmTy (P : LevFam X.E X.K R.r Pr.vGs) : LevFam X.E X.K R.r (rowSG Pr sel mu) :=
  P.inv.glue (wmTyQ R (QE sel (mu : Chr X.F X.E X.K)))

@[reducible] def wmGSD (P : LevFam X.E X.K R.r Pr.vGs) : GSD X.K :=
  formGSD (wmVal W (rowSG Pr sel mu)) (wmTy sel mu P).inv

end Forms

section Data

variable {E : Type} [Field E] [NumberField E] [StarRing E]

variable {SG : Finset (HeightOneSpectrum (𝓞 E))}

def wmIsRed {a b : ℕ} (d' : DecoSet (E := E) (n := a) (ST := ∅) (SG := SG)) (d : DecoSet (E := E) (n := b) (ST := ∅) (SG := SG)) (w : SG) (x : Sp E a →ₗ[E] Sp E b)
    (M : Matrix (Fin b) (Fin a) (𝓞 E ⧸ w.1.asIdeal)) : Prop :=
  ∀ y ∈ d'.1.at w.1, x y ∈ d.1.at w.1 ∧ d.1.be w (x y) = M.mulVec (d'.1.be w y)


open Classical in
def lemU {κ K : Type} [CommRing κ] [Field K] {r n : ℕ} (h : r ≤ n) (l : Lev κ K r) (s : κˣ →* Kˣ)
    (M : Matrix (Fin n) (Fin r) κ) : K :=
  if H : ∃ k : ↥l.H, (∀ i j, M (Fin.castLE h i) j = (k.1 : Matrix (Fin r) (Fin r) κ) i j) ∧
      ∀ (i : Fin n) (j : Fin r), r ≤ i.1 → M i j = 0
  then ((l.lam H.choose : Kˣ) : K) * (((s (Matrix.GeneralLinearGroup.det H.choose.1))⁻¹ : Kˣ) : K)
  else 0


open Classical in
def wmPhi {K : Type} [Field K] {a b : ℕ} (loc : ∀ w : SG, Matrix (Fin b) (Fin a) (𝓞 E ⧸ w.1.asIdeal) → K)
    (d' : DecoSet (E := E) (n := a) (ST := ∅) (SG := SG)) (d : DecoSet (E := E) (n := b) (ST := ∅) (SG := SG)) (x : Sp E a →ₗ[E] Sp E b) : K :=
  ∏ w : SG, if h : ∃ M, wmIsRed d' d w x M then loc w h.choose else 0

end Data

section Dist

variable (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (a b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (V V' : Type) [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

abbrev WmTh : Type :=
  Finset (HeightOneSpectrum (𝓞 E)) → DecoSet (E := E) (n := a) (ST := ∅) (SG := SG) → DecoSet (E := E) (n := b) (ST := ∅) (SG := SG) →
    ((Sp E a →ₗ[E] Sp E b) → K) →ₗ[K] (V →ₗ[K] V')

variable {E K a b SG V V'}


end Dist

section Theta

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)


open Classical in
def wmLoc (Ch : Chars X Pr R.m) (P : LevFam X.E X.K R.r Pr.vGs) :
    ∀ w : rowSG Pr sel mu, Matrix (Fin R.nV) (Fin R.r) (𝓞 X.E ⧸ w.1.asIdeal) → X.K := fun w =>
  if h : w.1 ∈ Pr.vGs then lemU (r_le_nV R) (P ⟨w.1, h⟩).inv (chiAt Ch ⟨w.1, h⟩ (R.m - 1))⁻¹
  else lemU (r_le_nV R) (⟨⊤, 1⟩ : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K R.r) (resChar (mu : Chr X.F X.E X.K) w.1)


abbrev ThM (P : LevFam X.E X.K R.r Pr.vGs) : Type :=
  WmTh X.E X.K R.r R.nV (rowSG Pr sel mu) (mtGSD W Ch sel mu P R.m).V (wmGSD W sel mu P).V

def wmKer (P : LevFam X.E X.K R.r Pr.vGs) (th : ThM W Ch sel mu P) (d : (mtGSD W Ch sel mu P R.m).D)
    (d' : (wmGSD W sel mu P).D) : (mtGSD W Ch sel mu P R.m).V →ₗ[X.K] (wmGSD W sel mu P).V :=
  th (rowSG Pr sel mu) d' d (wmPhi (wmLoc sel mu Ch P) d' d)

def GSD.wmCls {K : Type} [Field K] [NumberField K] [StarRing K] (S S' : GSD K) (h : S.Ok) (k : S.D → S'.D → (S.V →ₗ[K] S'.V)) :
    S.EqFun →ₗ[K] (S'.D → S'.V) where
  toFun φ d' := letI := h.fintypeCl
    ∑ c, (((S.toCSD h).wt c : K))⁻¹ • k (S.outSec.rep c) d' ((φ : S.D → S.V) (S.outSec.rep c))
  map_add' φ ψ := by
    funext d'
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    funext d'
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_comm]

def thetaP (P : LevFam X.E X.K R.r Pr.vGs) (th : ThM W Ch sel mu P) (h : (mtGSD W Ch sel mu P R.m).Ok) :
    (mtGSD W Ch sel mu P R.m).EqFun →ₗ[X.K] ((wmGSD W sel mu P).D → (wmGSD W sel mu P).V) :=
  GSD.wmCls (mtGSD W Ch sel mu P R.m) (wmGSD W sel mu P) h (wmKer W Ch sel mu P th)

end Theta

section Z

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Z

section NbFun

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]

def nbFun (P : Ideal (𝓞 E)) (i : ℕ) : (DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → V) →ₗ[K] (DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → V) where
  toFun ψ d := ∑ d₁ ∈ d.heckeNb P i, ψ d₁
  map_add' ψ ψ' := by
    funext d
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext d
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

end NbFun

section Rel

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Rel

end Formalism.L2.Col
end
end
