module

public import Formalism.LocalToGlobal.Divisibility.NumbersLink
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementStep
public import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.NormEqOneOfNotMem
public import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst

@[expose] public section

section -- merged from Formalism.LocalToGlobal.KernelLattices.EntryG
section -- merged from Formalism.LocalToGlobal.ExponentGrids.EntryG
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AtG.EntryG

open Formalism.L2.Col (Fields Sp HomE homAt divLat IsSdLat)
open Formalism.L2.Ker (Amb DVar)
open Formalism.L2.AlgTh (KerStd SplitS JetAtSplit IsQInt GAt)
open Formalism.DivisionValues (vw PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols)
open Formalism.L2.DIV (PathData EmbAt IsExpansion ColsInt RowsInt LastInt UnitsInt StabDvd)
open Formalism.AtG (PerBd colRhs)

section Terms

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ}

structure Term (X : Fields) (p : ℕ) [Fact p.Prime] (a b : ℕ) where

  coef : ℂ_[p]

  scal : X.K

  xi : X.K

  S : Finset (HeightOneSpectrum (𝓞 X.E))

  N : Submodule (𝓞 X.E) (Sp X.E a)

  N' : Submodule (𝓞 X.E) (Sp X.E b)

  c' : ℕ

  x : HomE X.E a b

  m : DVar X.Tau a b →₀ ℕ

def Term.val (A : Amb X) (ι : ℂ ≃+* ℂ_[p]) (T : Term X p a b) : ℂ_[p] :=
  T.coef * ι (A.σ₀ T.scal) * ι (A.σ₀ T.xi) * ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))

def Term.Ok (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (T : Term X p a b) : Prop :=
  ‖T.coef‖ ≤ 1 ∧ ‖ι (A.σ₀ T.scal)‖ ≤ 1 ∧ ‖ι (A.σ₀ T.xi)‖ ≤ ‖(p : ℂ_[p])‖ ^ e ∧
  KerStd A T.N T.N' a₀ b₀ c₀ ha hd lam hlam p ι ∧ IsSdLat T.N ∧ IsSdLat T.N' ∧ A.LaHyp a b T.S ∧ SplitS A T.S p ϖ pE ∧
  0 < T.c' ∧ ¬ p ∣ T.c' ∧ T.x ∈ divLat T.c' (homAt T.S T.N T.N') ∧ T.m.degree = D

def IsEntryG (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (a b : ℕ) (y : ℂ_[p]) : Prop :=
  ∃ (n : ℕ) (T : Fin n → Term X p a b), y = ∑ k, (T k).val A ι ∧ ∀ k, (T k).Ok A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e

theorem isEntryG_zero (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (a b : ℕ) : IsEntryG A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e a b 0 :=
  ⟨0, Fin.elim0, by simp, fun k => k.elim0⟩

end Terms

section Place

variable {X : Fields}

end Place

section Record

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Indef

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

end Record

end Formalism.L2.AtG.EntryG
end
end

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain MvPolynomial

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (KerStd SplitS)
open Formalism.DivisionValues (vw)

section Cf

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}



end Cf

section AtG

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

end AtG

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]

end Lat

section AtRec

open Formalism.DivisionValues (PlOver)

def StdOver {E : Type} [Field E] [NumberField E] {n : ℕ} (g : ℕ) (Lat : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → localization₂ P.asIdeal Lat = stdAt E n P

end AtRec

section Hyp

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

end Hyp

section Rec

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) {p : ℕ} [Fact p.Prime]

end Rec

section Paths

open Module NumberField IsDedekindDomain

open Formalism.L2.Col Formalism.L2.DIV

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable (Q : KerChain K)

def Nd (j : ℕ) : Type := (Q.F j).Cl × (Q.F j).ιV

def famRep (j : ℕ) (c : (Q.F j).Cl) : (Q.F j).D c.1 := ((Q.F j).mem c.1).outSec.rep c.2

structure ChBas where

  B : ∀ j (c : (Q.F j).Cl), Basis (Q.F j).ιV K (Q.F j).V

  BS : Q.S.Cl → Basis Q.S.ιV K Q.S.V

variable {Q} (Bb : ChBas Q)

def crd (j : ℕ) (ν : Nd Q j) : (Q.F j).Forms →ₗ[K] K :=
  (Bb.B j ν.1).coord ν.2 ∘ₗ (LinearMap.proj (famRep Q j ν.1)) ∘ₗ ((Q.F j).mem ν.1.1).EqFun.subtype ∘ₗ LinearMap.proj ν.1.1



structure LastDat (S₁ : GSD K) (Bsp : Type) [AddCommGroup Bsp] [Module K Bsp] where

  Cl : Type
  [finCl : Fintype Cl]

  pt : Cl → S₁.D

  wt : Cl → ℕ

  V₂ : Type
  [addV : AddCommGroup V₂]
  [modV : Module K V₂]

  ι₂ : Type
  [finι : Fintype ι₂]

  β : S₁.V →ₗ[K] V₂ →ₗ[K] K

  ev : Cl → Bsp →ₗ[K] V₂

  B1 : Cl → Basis S₁.ιV K S₁.V

  B2 : Cl → Basis ι₂ K V₂

attribute [instance] LastDat.finCl LastDat.addV LastDat.modV LastDat.finι

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp]

variable (T : LastDat Q.S₁ Bsp)


variable {l : ℕ} [Fact l.Prime] {J : Type} [Fintype J] {Asp : Type} [AddCommGroup Asp] [Module K Asp]

def RowInt (w : HeightOneSpectrum (𝓞 K)) (NB : Set Bsp) : Prop :=
  ∀ c k, ∀ F ∈ NB, (T.B2 c).coord k (T.ev c F) = 0 ∨ 0 ≤ Formalism.DivisionValues.vw w ((T.B2 c).coord k (T.ev c F))

end Generic

section Transport

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure ChGood (Q : KerChain K) where

  s : ∀ j b, ((Q.F j).mem b).Sec

  sS : Q.S.Sec

  B : ∀ j, (Q.F j).Cl → Basis (Q.F j).ιV K (Q.F j).V

  BS : Q.S.Cl → Basis Q.S.ιV K Q.S.V

variable {Q : KerChain K} (G : ChGood Q)

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp] {J : Type}

end Transport

section Place

open Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields}

end Place

section Record

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

abbrev recQ {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
    {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} (Am : Amb X)
    (hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok) (hE : (evGSD W Ch sel mu P u).Ok) : KerChain X.K :=
  KerChain.ofCol W Ch sel mu cst L (chKerC W Ch sel mu cst L Am u m2 b hY P hK) hF hE

section Entries

variable {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
  {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} {Am : Amb X}
  {hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P} {hF : ∀ j, (chF W sel mu L u j).Ok} {hE : (evGSD W Ch sel mu P u).Ok}
  (Bb : ChBas (recQ Am hK hF hE))

end Entries

section Steps

variable {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
  {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} {Am : Amb X}
  {hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P} {hF : ∀ j, (chF W sel mu L u j).Ok} {hE : (evGSD W Ch sel mu P u).Ok}
  {g : ℕ} [Fact g.Prime] {J : Type}

end Steps

end Record

end Paths

end Formalism.L2.Ker
end
end

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain MvPolynomial

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (KerStd SplitS)
open Formalism.L2.AtG.EntryG (IsEntryG Term isEntryG_zero)
open Formalism.DivisionValues (vw)

section Tower

variable {E : Type} [Field E] [NumberField E] {H M : Type} [AddCommGroup H] [Module (𝓞 E) H] [AddCommMonoid M]

def lrep (A B : Submodule (𝓞 E) H) (z : ↥A ⧸ B.comap A.subtype) : ↥A :=
  Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z

theorem latSum_eq (A B : Submodule (𝓞 E) H) (F : H → M) : latSum A B F = ∑ᶠ z, F (lrep A B z : H) := rfl

theorem mk_lrep (A B : Submodule (𝓞 E) H) (z : ↥A ⧸ B.comap A.subtype) : Submodule.Quotient.mk (lrep A B z) = z :=
  Function.surjInv_eq _ z

theorem lrep_mk_sub (A B : Submodule (𝓞 E) H) (a : ↥A) :
    ((lrep A B (Submodule.Quotient.mk a) : ↥A) : H) - (a : H) ∈ B := by
  have h := mk_lrep A B (Submodule.Quotient.mk a)
  rw [Submodule.Quotient.eq] at h
  simpa using h

theorem latSum_congr (A B : Submodule (𝓞 E) H) {F G : H → M} (h : ∀ x ∈ A, F x = G x) : latSum A B F = latSum A B G := by
  rw [latSum_eq, latSum_eq]
  exact finsum_congr fun z => h _ (lrep A B z).2

theorem latSum_tower (A B C : Submodule (𝓞 E) H) (hCB : C ≤ B) (hBA : B ≤ A) (F : H → M)
    (hF : ∀ x c, c ∈ C → F (x + c) = F x) [Finite (↥A ⧸ C.comap A.subtype)] :
    latSum A C F = latSum A B fun x => latSum B C fun y => F (x + y) := by
  classical
  let φ : (↥A ⧸ B.comap A.subtype) × (↥B ⧸ C.comap B.subtype) → (↥A ⧸ C.comap A.subtype) := fun zt =>
    Submodule.Quotient.mk ⟨(lrep A B zt.1 : H) + (lrep B C zt.2 : H), A.add_mem (lrep A B zt.1).2 (hBA (lrep B C zt.2).2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨z, t⟩ ⟨z', t'⟩ h
    have h1 : ((lrep A B z : H) + (lrep B C t : H)) - ((lrep A B z' : H) + (lrep B C t' : H)) ∈ C := by
      have h0 := (Submodule.Quotient.eq _).1 h
      simpa using h0
    have hz : z = z' := by
      rw [← mk_lrep A B z, ← mk_lrep A B z', Submodule.Quotient.eq]
      show ((lrep A B z - lrep A B z' : ↥A) : H) ∈ B
      have e : ((lrep A B z - lrep A B z' : ↥A) : H) =
          (((lrep A B z : H) + (lrep B C t : H)) - ((lrep A B z' : H) + (lrep B C t' : H))) - (lrep B C t : H) + (lrep B C t' : H) := by
        push_cast
        abel
      rw [e]
      exact B.add_mem (B.sub_mem (hCB h1) (lrep B C t).2) (lrep B C t').2
    subst hz
    have ht : t = t' := by
      rw [← mk_lrep B C t, ← mk_lrep B C t', Submodule.Quotient.eq]
      show ((lrep B C t - lrep B C t' : ↥B) : H) ∈ C
      have e : ((lrep B C t - lrep B C t' : ↥B) : H) =
          ((lrep A B z : H) + (lrep B C t : H)) - ((lrep A B z : H) + (lrep B C t' : H)) := by
        push_cast
        abel
      rw [e]
      exact h1
    rw [ht]
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hb : (a : H) - (lrep A B (Submodule.Quotient.mk a) : H) ∈ B := by
      have := B.neg_mem (lrep_mk_sub A B a)
      simpa using this
    refine ⟨(Submodule.Quotient.mk a, Submodule.Quotient.mk ⟨_, hb⟩), ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk a
    rw [Submodule.Quotient.eq]
    have h2 := lrep_mk_sub B C ⟨_, hb⟩
    show (lrep A B (Submodule.Quotient.mk a) : H) + (lrep B C (Submodule.Quotient.mk ⟨_, hb⟩) : H) - (a : H) ∈ C
    have e : (lrep A B (Submodule.Quotient.mk a) : H) + (lrep B C (Submodule.Quotient.mk ⟨_, hb⟩) : H) - (a : H) =
        (lrep B C (Submodule.Quotient.mk ⟨_, hb⟩) : H) - ((a : H) - (lrep A B (Submodule.Quotient.mk a) : H)) := by abel
    rw [e]
    exact h2
  have hG : ∀ a : ↥A, F (lrep A C (Submodule.Quotient.mk a) : H) = F a := by
    intro a
    have h := hF (a : H) _ (lrep_mk_sub A C a)
    rwa [add_sub_cancel] at h
  have : Finite ((↥A ⧸ B.comap A.subtype) × (↥B ⧸ C.comap B.subtype)) := Finite.of_injective φ hinj
  have : Finite (↥A ⧸ B.comap A.subtype) := Finite.prod_left (↥B ⧸ C.comap B.subtype)
  have : Finite (↥B ⧸ C.comap B.subtype) := Finite.prod_right (↥A ⧸ B.comap A.subtype)
  let _ := Fintype.ofFinite (↥A ⧸ C.comap A.subtype)
  let _ := Fintype.ofFinite (↥A ⧸ B.comap A.subtype)
  let _ := Fintype.ofFinite (↥B ⧸ C.comap B.subtype)
  simp only [latSum_eq, finsum_eq_sum_of_fintype]
  rw [← (Function.Bijective.sum_comp ⟨hinj, hsurj⟩ fun w => F (lrep A C w : H)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => ?_
  exact hG _

theorem latSum_mul_left {R : Type} [NonUnitalNonAssocSemiring R] (A B : Submodule (𝓞 E) H) [Finite (↥A ⧸ B.comap A.subtype)] (r : R) (F : H → R) :
    latSum A B (fun x => r * F x) = r * latSum A B F := by
  let _ := Fintype.ofFinite (↥A ⧸ B.comap A.subtype)
  rw [latSum_eq, latSum_eq, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]

theorem mulLat_mul_le (c k : ℕ) (M : Submodule (𝓞 E) H) : mulLat (c * k) M ≤ mulLat c M := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := (mem_mulLat (c * k) M w).1 hw
  refine (mem_mulLat c M _).2 ⟨(k : 𝓞 E) • y, M.smul_mem _ hy, ?_⟩
  rw [smul_smul, Nat.cast_mul]

theorem mulLat_le_divLat (c d : ℕ) (M : Submodule (𝓞 E) H) : mulLat c M ≤ divLat d M := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := (mem_mulLat c M w).1 hw
  exact (mem_divLat d M _).2 (M.smul_mem _ (M.smul_mem _ hy))

end Tower

section Regroup

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem fin_div (hN : IsSdLat N) (hN' : IsSdLat N') (cA c : ℕ) (hA : 0 < cA) (hc : 0 < c) :
    Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
  kerFin S N N' hN hN' cA c hA hc

theorem fin_mul (hN : IsSdLat N) (hN' : IsSdLat N') (c c' : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    Finite (↥(mulLat c (homAt S N N')) ⧸ (mulLat (c * c') (homAt S N N')).comap (mulLat c (homAt S N N')).subtype) :=
  lattice_classes_finite_refinement X a b S N N' c c' hN hN' hc hc'

end Regroup

section Cf

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

end Cf

section LatSum

variable {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H]

end LatSum

section Clo

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ} {A : Amb X} {a₀ : ℕ} {b₀ c₀' : ℤ} {ha : 0 < a₀} {hd : 0 < A.d} {lam₀ : ℂ}
  {hlam : lam₀ ≠ 0} {ι : ℂ ≃+* ℂ_[p]} {ϖ : ℂ} {pE : 𝓞 X.E} {D : ℕ} {e : ℝ}

end Clo

section Entry

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ} (A : Amb X) (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ)
  (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ)

end Entry

section Rec

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) {p : ℕ} [Fact p.Prime] (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ)
  (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) {u : Pr.Word} (m2 : ℕ)

end Rec

section Deg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

end Deg

section Lat

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

end Lat

namespace Test

end Test

end Formalism.L2.Ker
