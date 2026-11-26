module

public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Formalism.LocalToGlobal.Columns.CoefCol
public import Formalism.LocalToGlobal.Divisibility.CoeffLemmas
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.ColForms
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

structure Lev (κ K : Type) [CommRing κ] [Field K] (n : ℕ) where

  H : Subgroup (GL (Fin n) κ)

  lam : ↥H →* Kˣ

def Lev.inv {κ K : Type} [CommRing κ] [Field K] {n : ℕ} (l : Lev κ K n) : Lev κ K n := ⟨l.H, l.lam⁻¹⟩

abbrev LevFam (E K : Type) [Field E] [NumberField E] [Field K] (n : ℕ)
    (SG : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  ∀ w : SG, Lev (𝓞 E ⧸ w.1.asIdeal) K n

namespace LevFam

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  (Λ : LevFam E K n SG)

def grp : Subgroup (GLG (E := E) (n := n) (SG := SG)) := Subgroup.pi Set.univ fun w => (Λ w).H

def chr : ↥Λ.grp →* Kˣ := piChar (fun w => (Λ w).H) fun w => (Λ w).lam

def inv : LevFam E K n SG := fun w => (Λ w).inv

end LevFam

section Form

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

abbrev FormG (Λ : LevFam X.E X.K n SG) : Type := UF X.E n × ↥Λ.grp

@[reducible] def FormG.incl (Λ : LevFam X.E X.K n SG) : FormG Λ →* UF X.E n × GLG (E := X.E) (n := n) (SG := SG) :=
  MonoidHom.prodMap (MonoidHom.id _) Λ.grp.subtype

instance formAct (Λ : LevFam X.E X.K n SG) : MulAction (FormG Λ) (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :=
  MulAction.compHom _ (FormG.incl Λ)

def formRho (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) :
    FormG Λ →* Module.End X.K C.V where
  toFun a := ((Λ.chr a.2 : X.Kˣ) : X.K) • C.rho a.1
  map_one' := by simp
  map_mul' a b := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul]
    rw [smul_mul_smul_comm]


open Classical in
@[reducible] def formGSD (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) : GSD X.K where
  G := FormG Λ
  D := DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)
  actD := formAct Λ
  V := C.V
  ιV := VVIdx C.lam
  bV := C.bV
  pair := C.pair
  ρ := formRho C Λ
  Nab := C.Nab
  Del := C.Del

structure CoefPk.Eqv (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) : Prop where
  nab_smul : ∀ (a : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)),
    C.Nab (a • d) = (C.Nab d).map ((C.rho a.1).restrictScalars (𝓞 X.K))
  del_smul : ∀ (a : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)),
    C.Del (a • d) = (C.Del d).map ((C.rho a.1).restrictScalars (𝓞 X.K))
  inv : ∀ (γ : UF X.E n) (x y : C.V), C.pair (C.rho γ x) (C.rho γ y) = C.pair x y

instance formModO (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) :
    Module (𝓞 X.K) (formGSD C Λ).EqFun :=
  (fun S : GSD X.K => (inferInstance : Module (𝓞 X.K) S.EqFun)) (formGSD C Λ)

end Form

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def colLev (Ch : Chars X Pr R.m) (j : ℕ) : LevFam X.E X.K (R.N j) Pr.vGs := fun w =>
  if j < R.m then
    ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j,
      lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j⟩
  else
    ⟨HXm (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.r R.t R.m,
      lamXm (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.r R.t R.m⟩

variable (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

@[reducible] def colGSD (u : Pr.Word) (j : ℕ) : GSD X.K :=
  formGSD (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j)

abbrev ColV (u : Pr.Word) (j : ℕ) : Submodule X.K ((colGSD W Ch u j).D → (colGSD W Ch u j).V) :=
  (colGSD W Ch u j).EqFun

def ColL (u : Pr.Word) (j : ℕ) : Submodule (𝓞 X.K) (ColV W Ch u j) := (colGSD W Ch u j).intDel

abbrev MfV (u : Pr.Word) : Submodule X.K ((colGSD W Ch u 0).D → (colGSD W Ch u 0).V) := ColV W Ch u 0

def MfL (u : Pr.Word) : Submodule (𝓞 X.K) (MfV W Ch u) := ColL W Ch u 0

end Cols

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.BaseInst
open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

instance fin_KQ (d : ℕ) : FiniteDimensional ℚ (KQ d) := fin_sqQ _

instance normal_KQ (d : ℕ) : Normal ℚ (KQ d) := normal_sqQ _

def quadFields (d : ℕ) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ d ≤ LL) : Fields where
  F := ℚ
  E := KQ d
  K := CoF ι LL
  nfE := { to_charZero := inferInstance, to_finiteDimensional := fin_KQ d }
  starE := starLL ι (KQ d)
  Tau := Unit
  emb := fun _ => (tauLL hE (KQ d).val).toRingHom

section QuadOk

variable (d : ℕ) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ d ≤ LL)

end QuadOk

section DegTwo

variable (X : Fields)

theorem conjO_coe (x : 𝓞 X.E) : ((X.conjO x : 𝓞 X.E) : X.E) = star (x : X.E) := rfl

theorem conjO_conjO (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  rw [conjO_coe, conjO_coe, star_star]

end DegTwo

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

def iQb : Qb := Classical.choose (exists_sqrt (-((1 : ℕ) : ℤ)))

theorem iQb_mem : iQb ∈ sqrts (-((1 : ℕ) : ℤ)) := Classical.choose_spec (exists_sqrt (-((1 : ℕ) : ℤ)))

abbrev gaussFields : Fields := quadFields 1 ι LL hE

def iE : (gaussFields ι LL hE).E := (⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1)


end Gauss

section Roots

end Roots

section GaussChars

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end GaussChars

section GaussChars2

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end GaussChars2

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end Gauss

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.HeckeInert
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section InertNbr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

abbrev inType (P : Ideal (𝓞 E)) (s : List ℕ) : Type := ∀ i : Fin s.length, 𝓞 E ⧸ P ^ s.get i

def IsInertNbr (P : Ideal (𝓞 E)) (s : List ℕ) (N N' : Submodule (𝓞 E) (Sp E n)) : Prop :=
  Nonempty ((N ⧸ (N' ⊓ N).comap N.subtype) ≃ₗ[𝓞 E] inType P s) ∧
    Nonempty ((N' ⧸ (N ⊓ N').comap N'.subtype) ≃ₗ[𝓞 E] inType P s)

theorem IsInertNbr.symm {P : Ideal (𝓞 E)} {s : List ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsInertNbr P s N N') : IsInertNbr P s N' N := ⟨h.2, h.1⟩

theorem IsInertNbr.gmap {P : Ideal (𝓞 E)} {s : List ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsInertNbr P s N N') (g : Sp E n ≃ₗ[E] Sp E n) : IsInertNbr P s (gmap g N) (gmap g N') := by
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := h
  exact ⟨⟨(quotMapEquiv (g.restrictScalars (𝓞 E)) N' N).symm.trans e1⟩,
    ⟨(quotMapEquiv (g.restrictScalars (𝓞 E)) N N').symm.trans e2⟩⟩

theorem inType_smul_eq_zero {P : Ideal (𝓞 E)} {s : List ℕ} {r : 𝓞 E} (hr : r ∈ P ^ s.sum) (x : inType P s) :
    r • x = 0 := by
  funext i
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x i)
  rw [Pi.smul_apply, ← hy, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (List.le_sum_of_mem (List.get_mem s i)) hr)

theorem IsInertNbr.smul_le {P : Ideal (𝓞 E)} {s : List ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsInertNbr P s N N') : (P ^ s.sum) • N ≤ N' ∧ (P ^ s.sum) • N' ≤ N := by
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := h
  constructor
  · rw [Submodule.smul_le]
    intro r hr x hx
    have h0 : e1 (Submodule.Quotient.mk (r • (⟨x, hx⟩ : N))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      exact inType_smul_eq_zero hr _
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.mem_inf.1 (Submodule.mem_comap.1 h0)).1
  · rw [Submodule.smul_le]
    intro r hr x hx
    have h0 : e2 (Submodule.Quotient.mk (r • (⟨x, hx⟩ : N'))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      exact inType_smul_eq_zero hr _
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.mem_inf.1 (Submodule.mem_comap.1 h0)).1

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.inertSet (P : Ideal (𝓞 E)) (s : List ℕ) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : Set (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :=
  {d' | IsInertNbr P s d.1.N d'.1.N ∧ d'.1.f = d.1.f ∧ d'.1.be = d.1.be}


open Classical in
def DecoSet.inertNb (P : Ideal (𝓞 E)) (s : List ℕ) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : Finset (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :=
  if h : (d.inertSet P s).Finite then h.toFinset else ∅

theorem DecoSet.smul_mem_inertSet {P : Ideal (𝓞 E)} {s : List ℕ} (a : UF E n × GLG (E := E) (n := n) (SG := SG))
    {d e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (h : e ∈ d.inertSet P s) : a • e ∈ (a • d).inertSet P s := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    exact h1.gmap _
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    simp only [Deco.act, h2]
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    simp only [Deco.act, h3]

theorem DecoSet.smul_mem_inertSet_iff {P : Ideal (𝓞 E)} {s : List ℕ} (a : UF E n × GLG (E := E) (n := n) (SG := SG))
    {d e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} : a • e ∈ (a • d).inertSet P s ↔ e ∈ d.inertSet P s := by
  constructor
  · intro h
    have := DecoSet.smul_mem_inertSet a⁻¹ h
    simpa only [inv_smul_smul] using this
  · exact DecoSet.smul_mem_inertSet a

theorem DecoSet.inertSet_smul (P : Ideal (𝓞 E)) (s : List ℕ) (a : UF E n × GLG (E := E) (n := n) (SG := SG))
    (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : (a • d).inertSet P s = (fun e => a • e) '' d.inertSet P s := by
  ext e
  constructor
  · intro he
    refine ⟨a⁻¹ • e, ?_, smul_inv_smul a e⟩
    rw [← DecoSet.smul_mem_inertSet_iff a, smul_inv_smul]
    exact he
  · rintro ⟨e', he', rfl⟩
    exact DecoSet.smul_mem_inertSet a he'

theorem DecoSet.smul_mem_inertNb_iff {P : Ideal (𝓞 E)} {s : List ℕ} (a : UF E n × GLG (E := E) (n := n) (SG := SG))
    {d e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} : a • e ∈ (a • d).inertNb P s ↔ e ∈ d.inertNb P s := by
  classical
  unfold DecoSet.inertNb
  have hfin : ((a • d).inertSet P s).Finite ↔ (d.inertSet P s).Finite := by
    rw [DecoSet.inertSet_smul]
    exact Set.finite_image_iff (MulAction.injective a).injOn
  by_cases h : (d.inertSet P s).Finite
  · rw [dite_eq_left (hfin.2 h), dite_eq_left h, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact DecoSet.smul_mem_inertSet_iff a
  · rw [dite_eq_right (mt hfin.1 h), dite_eq_right h]
    simp

end InertNbr

section HeckeI

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

def DecoPts.nbI (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) (d : S.D) : Finset S.D :=
  ((c.pts d).inertNb P s).map c.pts.symm.toEmbedding

theorem DecoPts.mem_nbI (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) (d e : S.D) :
    e ∈ c.nbI P s d ↔ c.pts e ∈ (c.pts d).inertNb P s := by
  unfold DecoPts.nbI
  rw [Finset.mem_map_equiv, Equiv.symm_symm]

def heckeI (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) : LocOp S S :=
  LocOp.ofNbr (MonoidHom.id S.G) (c.nbI P s) LinearMap.id
    (by
      intro g d' d
      rw [c.mem_nbI, c.mem_nbI, MonoidHom.id_apply, c.pts_smul, c.pts_smul]
      exact DecoSet.smul_mem_inertNb_iff (c.hom g))
    (by intro g x; rfl)

theorem heckeI_op_apply (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) (φ : S.EqFun) (d : S.D) :
    (((heckeI c P s).op φ : S.EqFun) : S.D → S.V) d = ∑ e ∈ c.nbI P s d, (φ : S.D → S.V) e := by
  simp only [heckeI, LocOp.ofNbr_op_apply, LinearMap.id_apply]

def InertOff (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  {P : HeightOneSpectrum (𝓞 E) // conjPrime₂ P = P ∧ (∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) ∧ P ∉ S0}

def InertOff.q {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : InertOff S0) : ℕ := Nat.card (𝓞 E ⧸ P.1.asIdeal)

abbrev LevOffI (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  InertOff (S0 ∪ (↑ST : Set (HeightOneSpectrum (𝓞 E))) ∪ (↑SG : Set (HeightOneSpectrum (𝓞 E))))

def heckeFamI (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    LevOffI ST SG S0 × List ℕ → End K S.EqFun := fun x => (heckeI c x.1.1.asIdeal x.2).op


variable (ST SG) in
abbrev HeckeIx (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  (LevOff ST SG S0 × ℕ) ⊕ (LevOffI ST SG S0 × List ℕ)

def heckeFamAll (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    HeckeIx ST SG S0 → End K S.EqFun :=
  Sum.elim (heckeFam c S0) (heckeFamI c S0)

def HeckeCommAll (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  PairComm (heckeFamAll c S0)

def HeckeFieldsInI (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  SplitOver (heckeFamI c S0)

def HeckeFieldsInAll (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  SplitOver (heckeFamAll c S0)

end HeckeI

section Cartan

def CartanInert (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), conjPrime₂ P = P → (∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) →
    ∀ N N' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → Submodule.IsLattice E N' →
      IsUnimodular (hStd E n) N → IsUnimodular (hStd E n) N' →
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q N N') →
      ∃ g ∈ UF E n, SameAt P (gmap g N) N' ∧ SameAt P (gmap g N') N

end Cartan

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.CoefModX
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

def bcLat {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {n : ℕ} (j : K →+* K')
    (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K') (Fin n → K') :=
  tauLat (fun _ : Unit => j) () M

def bcPol {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {σ : Type} (j : K →+* K')
    (T : Submodule (𝓞 K) (MvPolynomial σ K)) : Submodule (𝓞 K') (MvPolynomial σ K') :=
  Submodule.span (𝓞 K') ((fun F : MvPolynomial σ K => MvPolynomial.map j F) '' (T : Set (MvPolynomial σ K)))

def polOfVV {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (T : Submodule (𝓞 K) (VV K lam)) : Submodule (𝓞 K) (Pol K ι n) :=
  T.map ((VV K lam).subtype.restrictScalars (𝓞 K))

def BaseChangeSpace : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    (∀ F : Pol K ι n, F ∈ VV K lam ↔ MvPolynomial.map j F ∈ VV K' lam) ∧
    Submodule.span K' ((fun F : Pol K ι n => MvPolynomial.map j F) '' (VV K lam : Set (Pol K ι n))) = VV K' lam

def BaseChangeAct : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (g : ι → GL (Fin n) K) (F : Pol K ι n),
    MvPolynomial.map j (actP lam g F) = actP lam (fun τ => Formalism.UG.bc j (g τ)) (MvPolynomial.map j F)

def BaseChangePair : Prop :=
  ∀ (K K' : Type) [Field K] [StarRing K] [Field K'] [StarRing K'] (j : K →+* K'), (∀ x, j (star x) = star (j x)) →
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n),
      pairP lam (fun τ => (G τ).map j) (MvPolynomial.map j F) (MvPolynomial.map j F') = j (pairP lam G F F')

def BaseChangePairV : Prop :=
  ∀ (E K K' : Type) [Field E] [Field K] [StarRing K] [Field K'] [StarRing K'] (j : K →+* K'),
    (∀ x, j (star x) = star (j x)) →
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (J : Matrix (Fin n) (Fin n) E)
      (x x' : VV K lam) (y y' : VV K' lam),
      (y : Pol K' ι n) = MvPolynomial.map j (x : Pol K ι n) → (y' : Pol K' ι n) = MvPolynomial.map j (x' : Pol K ι n) →
      pairV (fun τ => j.comp (emb τ)) lam J y y' = j (pairV emb lam J x x') ∧
      pairVr (fun τ => j.comp (emb τ)) lam J y y' = j (pairVr emb lam J x x')

def BaseChangeTauLat : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) (n : ℕ) (emb : ι → E →+* K) (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)),
    tauLat (fun τ => j.comp (emb τ)) τ L = bcLat j (tauLat emb τ L)

def BaseChangeStd : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n), bcPol j (nabStd K lam) = nabStd K' lam ∧ bcPol j (delStd K lam) = delStd K' lam

def NabDelBaseChange : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsFullLattice K (M τ)) →
    bcPol j (nabP lam M) = nabP lam (fun τ => bcLat j (M τ)) ∧
    bcPol j (delP lam M) = delP lam (fun τ => bcLat j (M τ))

def NabDelDescent : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsFullLattice K (M τ)) →
    ∀ F : Pol K ι n,
      (F ∈ nabP lam M ↔ MvPolynomial.map j F ∈ nabP lam (fun τ => bcLat j (M τ))) ∧
      (F ∈ delP lam M ↔ MvPolynomial.map j F ∈ delP lam (fun τ => bcLat j (M τ)))

def BaseChangeDualFr : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsFullLattice K M → dualFr (bcLat j M) = bcLat j (dualFr M)

def NabDelBaseChangeAt : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E L →
    polOfVV lam (nabAt (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (nabAt emb lam L)) ∧
    polOfVV lam (delAt (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (delAt emb lam L)) ∧
    polOfVV lam (nabAtr (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (nabAtr emb lam L)) ∧
    polOfVV lam (delAtr (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (delAtr emb lam L))

def NabDelDescentAt : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E L → ∀ (x : VV K lam) (y : VV K' lam), (y : Pol K' ι n) = MvPolynomial.map j (x : Pol K ι n) →
    (x ∈ nabAt emb lam L ↔ y ∈ nabAt (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ delAt emb lam L ↔ y ∈ delAt (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ nabAtr emb lam L ↔ y ∈ nabAtr (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ delAtr emb lam L ↔ y ∈ delAtr (fun τ => j.comp (emb τ)) lam L)

end Formalism.L2.DIV
end
end
