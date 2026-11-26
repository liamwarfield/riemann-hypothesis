module

public import Formalism.LocalToGlobal.Columns.ColForms
public import Formalism.LocalToGlobal.Columns.GSetLemmas
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
public import Formalism.LocalToGlobal.Columns.PolyFn

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.ColFormsLemmas
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Roots

variable {K : Type} [Field K] [NumberField K]

theorem map_root_smul {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (N : Submodule (𝓞 K) V) (f : Module.End K V) {c : K} {m : ℕ} (hm : 0 < m) (hc : c ^ m = 1) :
    N.map ((c • f).restrictScalars (𝓞 K)) = N.map (f.restrictScalars (𝓞 K)) := by
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [hc]⟩
  let c' : 𝓞 K := ⟨c, hint⟩
  have hc' : ∀ x : V, c' • x = c • x := fun x => by
    rw [← algebraMap_smul K c' x]; rfl
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c' • x, N.smul_mem _ hx, ?_⟩
    show f (c' • x) = c • f x
    rw [hc', map_smul]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c' ^ (m - 1) • x, N.smul_mem _ hx, ?_⟩
    show c • f (c' ^ (m - 1) • x) = f x
    have h2 : ∀ (k : ℕ) (x : V), c' ^ k • x = c ^ k • x := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ih => intro x; rw [pow_succ, mul_smul, ih, hc', pow_succ, mul_smul]
    rw [h2, map_smul, smul_smul, ← pow_succ', Nat.sub_add_cancel hm, hc, one_smul]

theorem star_mul_root [StarRing K] (h : ∃ σ₀ : K →+* ℂ, ∀ x : K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    {c : K} {m : ℕ} (hm : 0 < m) (hc : c ^ m = 1) : star c * c = 1 := by
  obtain ⟨σ₀, hσ⟩ := h
  apply σ₀.injective
  rw [map_mul, hσ, map_one, mul_comm, Complex.mul_conj]
  have h1 : ‖σ₀ c‖ = 1 := by
    have : σ₀ c ^ m = 1 := by rw [← map_pow, hc, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one this hm.ne'
  rw [Complex.normSq_eq_norm_sq, h1]
  simp

end Roots

section Form

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

theorem FormG.incl_injective : Function.Injective (FormG.incl Λ) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 (Subtype.ext h2)

theorem formGSD_rho (a : (formGSD C Λ).G) (x : C.V) :
    (formGSD C Λ).ρ a x = ((Λ.chr a.2 : X.Kˣ) : X.K) • C.rho a.1 x := rfl

theorem mem_formGSD_EqFun (φ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) :
    φ ∈ (formGSD C Λ).EqFun ↔ ∀ (γ : UF X.E n) (h : ↥Λ.grp) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)),
      φ ((γ, (h : GLG (E := X.E) (n := n) (SG := SG))) • d) = ((Λ.chr h : X.Kˣ) : X.K) • C.rho γ (φ d) :=
  ⟨fun H γ h d => H (γ, h) d, fun H a d => H a.1 a.2 d⟩

theorem LevFam.chr_root (h : ↥Λ.grp) : ∃ m : ℕ, 0 < m ∧ ((Λ.chr h : X.Kˣ) : X.K) ^ m = 1 := by
  have hf : IsOfFinOrder h := isOfFinOrder_of_finite h
  refine ⟨orderOf h, hf.orderOf_pos, ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]

theorem formGSD_ok (hX : X.Ok) (hC : C.Eqv) : (formGSD C Λ).Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs
    refine Finite.of_surjective (fun d : s => (formGSD C Λ).cls d.1) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h d =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep d
      refine ⟨⟨d0, hd0⟩, ?_⟩
      refine ((formGSD C Λ).cls_eq_iff d0 d).mpr ⟨((g, 1) : FormG Λ)⁻¹, ?_⟩
      have h1 : d = (((g, 1) : FormG Λ) : (formGSD C Λ).G) • (d0 : (formGSD C Λ).D) := hg
      rw [h1, inv_smul_smul]
  · intro d
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (formGSD C Λ).G d =>
        (⟨FormG.incl Λ a.1, a.2⟩ : MulAction.stabilizer (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)))) ?_
    intro a b hab
    exact Subtype.ext (FormG.incl_injective Λ (congrArg Subtype.val hab))
  · intro g d
    obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2
    exact (hC.nab_smul (FormG.incl Λ g) d).trans (map_root_smul _ _ hm hc).symm
  · intro g d
    obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2
    exact (hC.del_smul (FormG.incl Λ g) d).trans (map_root_smul _ _ hm hc).symm
  · intro g x y
    obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2
    show C.pair (((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 x) (((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star ((Λ.chr g.2 : X.Kˣ) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

theorem formGSD_stab_inj (d : (formGSD C Λ).D) {a b : (formGSD C Λ).G} (ha : a • d = d) (hb : b • d = d)
    (hab : a.1 = b.1) : a = b :=
  FormG.incl_injective Λ (DecoSet.stab_fst_injective (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) ha hb hab)

end Form

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem colVal_eqv (hX : X.Ok) (u : Pr.Word) (j : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    (colVal W u j ST SG).Eqv :=
  ⟨colVal_nab_smul W u j, colVal_del_smul W u j, roundPk_inv X _ _ hX.emb_star⟩

theorem colOk (hX : X.Ok) (u : Pr.Word) (j : ℕ) : (colGSD W Ch u j).Ok :=
  formGSD_ok _ _ hX (colVal_eqv W hX u j _ _)

theorem colLev_of_lt {j : ℕ} (hj : j < R.m) (w : Pr.vGs) :
    colLev Ch j w = ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j,
      lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j⟩ := if_pos hj

end Cols

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section MovesA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.IsDnA (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal) (d d' : Deco E n ST SG) : Prop :=
  d' = d.dn P (d'.f P) ∧ ∀ e ∈ d.N, d.f P e = 1 → d'.f P (q • e) = a

theorem Deco.IsDnA.act {P : ST} {q : 𝓞 E} {a : 𝓞 E ⧸ P.1.asIdeal} {d d' : Deco E n ST SG}
    (hdd : Deco.IsDnA P q a d d') {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) (h : GLG (E := E) (n := n) (SG := SG)) :
    Deco.IsDnA P q a (d.act g h) (d'.act g h) := by
  obtain ⟨h1, h2⟩ := hdd
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [h1]
    exact (d.dn_act hg h P (d'.f P)).symm
  · intro e he hfe
    change d'.f P (g.symm (q • e)) = a
    rw [equiv_osmul]
    exact h2 _ ((mem_gmap _ _ _).1 he) hfe

def DecoSet.dnSetA (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    Set (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :=
  {d' | Deco.IsDnA P q a d.1 d'.1}

theorem DecoSet.smul_mem_dnSetA (x : UF E n × GLG (E := E) (n := n) (SG := SG)) (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal)
    (d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : x • d' ∈ (x • d).dnSetA P q a ↔ d' ∈ d.dnSetA P q a := by
  constructor
  · intro h
    have := Deco.IsDnA.act h (x⁻¹).1.2 (x⁻¹).2
    have e1 : ((x • d).1.act (x⁻¹).1.1 (x⁻¹).2) = (x⁻¹ • x • d).1 := rfl
    have e2 : ((x • d').1.act (x⁻¹).1.1 (x⁻¹).2) = (x⁻¹ • x • d').1 := rfl
    rw [e1, e2, inv_smul_smul, inv_smul_smul] at this
    exact this
  · intro h
    exact Deco.IsDnA.act h x.1.2 x.2

theorem DecoSet.dnSetA_finite (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (q : 𝓞 E) (a : 𝓞 E ⧸ P.1.asIdeal) :
    (d.dnSetA P q a).Finite := by
  by_cases h : (d.1.dnN P).FG
  · refine (DecoSet.finite_fibre (ST := ST) (SG := SG) (d.1.dnN P) h).subset ?_
    intro d' hd'
    have := congrArg Deco.N hd'.1
    exact this
  · have he : d.dnSetA P q a = ∅ := by
      ext d'
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hd'
      apply h
      have h1 : d'.1.N = d.1.dnN P := congrArg Deco.N hd'.1
      rw [← h1]
      exact d'.2.lat.fg
    rw [he]
    exact Set.finite_empty

end MovesA

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

def diaG (c : DiaG (E := X.E) (ST := ST)) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofMap (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _) (fun d => DecoSet.dia c d) LinearMap.id
    (fun g d => DecoSet.dia_smul c (FormG.incl Λ g) d) (fun _ _ => rfl)).op

def diamondOperatorOnForms' (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofMap (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _) (fun d => DecoSet.dia1 P c d) LinearMap.id
    (fun g d => DecoSet.dia_smul _ (FormG.incl Λ g) d) (fun _ _ => rfl)).op

def NmG (P : ST) : Module.End X.K (formGSD C Λ).EqFun :=
  letI : Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := Fintype.ofFinite _
  ∑ c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ, diamondOperatorOnForms' C Λ P c

def UG (P : ST) (q : 𝓞 X.E) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofNbr (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _)
    (fun d => (DecoSet.upSet_finite d P q).toFinset) LinearMap.id
    (fun g d' d => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.smul_mem_upSet (FormG.incl Λ g) P q d' d) (fun _ _ => rfl)).op

def DaG (P : ST) (q : 𝓞 X.E) (a : 𝓞 X.E ⧸ P.1.asIdeal) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofNbr (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _)
    (fun d => (DecoSet.dnSetA_finite d P q a).toFinset) LinearMap.id
    (fun g d' d => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.smul_mem_dnSetA (FormG.incl Λ g) P q a d' d) (fun _ _ => rfl)).op

def DG (P : ST) (q : 𝓞 X.E) : Module.End X.K (formGSD C Λ).EqFun := DaG C Λ P q 1

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def diaOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    Module.End X.K (ColV W Ch u j) :=
  diamondOperatorOnForms' (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P c

def NmOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  NmG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P

def UOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColV W Ch u j) :=
  UG (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j) P (Pr.T u : 𝓞 X.E)

end Cols

structure CharT (X : Fields) (Pr : Primes X) where

  psiT : ∀ (u : Pr.Word) (P : {P // P ∈ Pr.vT u}), AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K

structure CharT.Ok {X : Fields} {Pr : Primes X} (Ps : CharT X Pr) : Prop where
  ne : ∀ u P, Ps.psiT u P ≠ 1
  same : ∀ (u : Pr.Word) (P P' : {P // P ∈ Pr.vT u}) (a : ℤ),
    Ps.psiT u P (a : 𝓞 X.E ⧸ P.1.asIdeal) = Ps.psiT u P' (a : 𝓞 X.E ⧸ P'.1.asIdeal)

section Cols2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

def ColRamV (u : Pr.Word) (j : ℕ) : Submodule X.K (ColV W Ch u j) :=
  ⨅ P : {P // P ∈ Pr.vT u}, LinearMap.ker (NmOp W Ch u j P)

def ramifiedColumnLattice (u : Pr.Word) (j : ℕ) : Submodule (𝓞 X.K) (ColV W Ch u j) :=
  ColL W Ch u j ⊓ (ColRamV W Ch u j).restrictScalars (𝓞 X.K)

def ColRamL (u : Pr.Word) (j : ℕ) : Submodule (𝓞 X.K) (ColRamV W Ch u j) :=
  (ColL W Ch u j).comap ((ColRamV W Ch u j).subtype.restrictScalars (𝓞 X.K))

abbrev MramV (u : Pr.Word) : Submodule X.K (MfV W Ch u) := ColRamV W Ch u 0

def ramifiedSublattice (u : Pr.Word) : Submodule (𝓞 X.K) (MfV W Ch u) := ramifiedColumnLattice W Ch u 0

def MramL (u : Pr.Word) : Submodule (𝓞 X.K) (MramV W Ch u) := ColRamL W Ch u 0

def ramIncl (u : Pr.Word) : MramV W Ch u →ₗ[X.K] MfV W Ch u := (MramV W Ch u).subtype

end Cols2

section Seen

variable {X : Fields}

def Fields.embO (X : Fields) (τ : X.Tau) : 𝓞 X.E →+* 𝓞 X.K := RingOfIntegers.mapRingHom (X.emb τ)

def pullW (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := w.asIdeal.comap (X.embO τ)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have h1 : ((prW w : ℕ) : 𝓞 X.E) ∈ w.asIdeal.comap (X.embO τ) := by
      rw [Ideal.mem_comap, map_natCast]
      exact natCast_prW_mem w
    rw [h, Ideal.mem_bot] at h1
    exact (prW_prime w).ne_zero (by exact_mod_cast h1)

def SeesP (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : HeightOneSpectrum (𝓞 X.E)) : Prop := pullW τ w = P

def SeesPbar (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : HeightOneSpectrum (𝓞 X.E)) : Prop :=
  pullW τ w = conjPrime₂ P

def tauOfC [Nonempty X.Tau] (w : HeightOneSpectrum (𝓞 X.K)) (P : HeightOneSpectrum (𝓞 X.E)) : X.Tau :=
  Classical.epsilon fun τ => SeesP w τ P ∨ SeesPbar w τ P

variable (Pr : Primes X)

def seenC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Prop := ∀ τ, X.embO τ (Pr.piT u) ∈ w.asIdeal

def seenBarC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ τ, X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal

end Seen

section Nlam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)


open Classical in
def topsP (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Finset X.Tau :=
  W.tops.filter fun τ => pullW τ w ∈ Pr.vT u


open Classical in
def VVTc (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Finset {P // P ∈ Pr.vT u} :=
  Finset.univ.filter fun P => ∃ τ ∈ W.tops, SeesP w τ P.1

def UprodC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K (ColV W Ch u j) :=
  ((VVTc W u w).toList.map fun P => UOp W Ch u j P).prod

def expTc (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : ℤ :=
  (R.m : ℤ) * ∑ τ ∈ topsP W u w, W.bTop u τ

def TUmC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K (MfV W Ch u) :=
  ((Pr.T u : X.K) ^ expTc W u w) • (UprodC W Ch u 0 w) ^ R.m

def scaledRamifiedLattice (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (𝓞 X.K) (MfV W Ch u) :=
  (ramifiedSublattice W Ch u).map ((TUmC W Ch u w).restrictScalars (𝓞 X.K))

def NlamG (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (𝓞 X.K) (MramV W Ch u) :=
  (scaledRamifiedLattice W Ch u w).comap ((MramV W Ch u).subtype.restrictScalars (𝓞 X.K))

end Nlam

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TiedGlMat
open Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.Forms (blkOf entN InJ blkMat)

theorem glm_blkIdx {t : ℕ} (ht : 0 < t) (j x : ℕ) : blkIdx (List.replicate j t) x = min (x / t) j := by
  induction j generalizing x with
  | zero => simp [blkIdx]
  | succ j ih =>
    simp only [List.replicate_succ, blkIdx]
    split_ifs with h
    · rw [Nat.div_eq_of_lt h]; omega
    · have hx : x / t = (x - t) / t + 1 := Nat.div_eq_sub_div ht (by omega)
      rw [ih, hx]; omega

section Grp

variable {κ k' : Type} [CommRing κ] [Field k'] {n : ℕ}

end Grp

section Chr

variable {κ k' K : Type} [CommRing κ] [Field k'] [Field K] {n : ℕ}

def glmPsi (e : κ ≃+* k') (σ₀ : K →+* ℂ) (ψ : AddChar κ K) : AddChar k' ℂ where
  toFun x := σ₀ (ψ (e.symm x))
  map_zero_eq_one' := by rw [map_zero, AddChar.map_zero_eq_one, map_one]
  map_add_eq_mul' x y := by rw [map_add (f := _), AddChar.map_add_eq_mul, map_mul]

theorem glmPsi_apply (e : κ ≃+* k') (σ₀ : K →+* ℂ) (ψ : AddChar κ K) (x : κ) : glmPsi e σ₀ ψ (e x) = σ₀ (ψ x) := by
  show σ₀ (ψ (e.symm (e x))) = σ₀ (ψ x)
  rw [e.symm_apply_apply]


open Classical in
def glmChi (e : κ ≃+* k') (σ₀ : K →+* ℂ) (χ : κˣ →* Kˣ) : MulChar k' ℂ :=
  MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp (χ.comp (Units.map e.symm.toRingHom.toMonoidHom)))

theorem glmChi_apply (e : κ ≃+* k') (σ₀ : K →+* ℂ) (χ : κˣ →* Kˣ) (x : κˣ) :
    glmChi e σ₀ χ (e (x : κ)) = σ₀ ((χ x : Kˣ) : K) := by
  have h : e (x : κ) = ((Units.map e.toRingHom.toMonoidHom x : k'ˣ) : k') := rfl
  rw [h]
  unfold glmChi
  rw [MulChar.ofUnitHom_coe]
  have h2 : (Units.map e.symm.toRingHom.toMonoidHom) (Units.map e.toRingHom.toMonoidHom x) = x := by
    ext
    simp
  simp only [MonoidHom.comp_apply, h2]
  rfl

def equalBlockPositionsEquiv {a t j s : ℕ} (ht : 0 < t) (hs : s < j) (hn : a + j * t ≤ n) :
    Fin t ≃ {i : Fin n // coarse a (List.replicate j t) i.val = s + 1} where
  toFun c := ⟨⟨a + s * t + c, by
      have h1 : (s + 1) * t ≤ j * t := Nat.mul_le_mul_right t hs
      have := c.2
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega⟩, by
    show coarse a (List.replicate j t) (a + s * t + c) = s + 1
    rw [coarse_of_le (by omega), glm_blkIdx ht]
    have h2 : (a + s * t + c - a) / t = s := by
      rw [show a + s * t + c - a = c + t * s by rw [Nat.mul_comm t s]; omega, Nat.add_mul_div_left _ _ ht,
        Nat.div_eq_of_lt c.2, Nat.zero_add]
    rw [h2]; omega⟩
  invFun i := ⟨i.1.val - (a + s * t), by
    have h := i.2
    have ha : a ≤ i.1.val := by
      by_contra hlt
      rw [coarse_of_lt (Nat.not_le.1 hlt)] at h
      omega
    rw [coarse_of_le ha, glm_blkIdx ht] at h
    have h3 : (i.1.val - a) / t = s := by omega
    have h4 := Nat.div_add_mod (i.1.val - a) t
    have h5 := Nat.mod_lt (i.1.val - a) ht
    rw [h3, Nat.mul_comm] at h4
    omega⟩
  left_inv c := by
    apply Fin.ext
    show a + s * t + c - (a + s * t) = c
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    show a + s * t + (i.1.val - (a + s * t)) = i.1.val
    have h := i.2
    have ha : a ≤ i.1.val := by
      by_contra hlt
      rw [coarse_of_lt (Nat.not_le.1 hlt)] at h
      omega
    rw [coarse_of_le ha, glm_blkIdx ht] at h
    have h3 : (i.1.val - a) / t = s := by omega
    have h4 := Nat.div_add_mod (i.1.val - a) t
    rw [h3, Nat.mul_comm] at h4
    omega

theorem glm_blkDet (e : κ ≃+* k') {a t j s : ℕ} (ht : 0 < t) (hs : s < j) (hn : a + j * t ≤ n)
    (M : ↥(blockUT n κ a (List.replicate j t))) :
    e ((blkDet n κ (coarse a (List.replicate j t)) (s + 1) M : κˣ) : κ) =
      (blkMat a t s ((M.1 : Matrix (Fin n) (Fin n) κ).map e)).det := by
  have hA : ((blkDet n κ (coarse a (List.replicate j t)) (s + 1) M : κˣ) : κ) =
      ((M.1 : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a (List.replicate j t) i.val) (s + 1)).det := rfl
  rw [hA, RingEquiv.map_det, RingEquiv.mapMatrix_apply]
  refine (Matrix.det_submatrix_equiv_self (equalBlockPositionsEquiv ht hs hn) _).symm.trans (congrArg Matrix.det ?_)
  ext c d
  have hc : a + s * t + (c : ℕ) < n := ((equalBlockPositionsEquiv ht hs hn) c).1.isLt
  have hd : a + s * t + (d : ℕ) < n := ((equalBlockPositionsEquiv ht hs hn) d).1.isLt
  simp only [blkMat, entN, dif_pos (And.intro hc hd)]
  rfl

end Chr

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.MtRowRep
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace Formalism.L2.Col

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def finTypSetoid (Occ : Set (NG.FinTyp L n)) : Setoid Occ where
  r π π' := π.1.Iso π'.1
  iseqv := ⟨fun π => NG.IsoRep.refl _, fun {π _} h => NG.IsoRep.symm π.1.stable h, fun h h' => NG.IsoRep.trans h h'⟩

abbrev FinTypCls (Occ : Set (NG.FinTyp L n)) : Type := Quotient (finTypSetoid Occ)

def finTypRep (Occ : Set (NG.FinTyp L n)) (c : FinTypCls Occ) : NG.FinTyp L n := (Quotient.out c).1

theorem finTypRep_mem (Occ : Set (NG.FinTyp L n)) (c : FinTypCls Occ) : finTypRep Occ c ∈ Occ := (Quotient.out c).2

theorem finTypRep_inj {Occ : Set (NG.FinTyp L n)} {c c' : FinTypCls Occ}
    (h : (finTypRep Occ c).Iso (finTypRep Occ c')) : c = c' := by
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  exact Quotient.sound h

theorem finTypRep_mk_iso {Occ : Set (NG.FinTyp L n)} (π : Occ) :
    (finTypRep Occ (Quotient.mk (finTypSetoid Occ) π)).Iso π.1 :=
  Quotient.mk_out (s := finTypSetoid Occ) π

end Gen

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.MtIsoVal
noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

namespace Formalism.L2.Col

section Map

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K')

theorem mti_map_colAddGen {r n : ℕ} (l j : Fin n) (P : MvPolynomial (Fin r × Fin n) K) :
    map s (Formalism.GradedWeylDivisibility.colAddGen K l j P) = Formalism.GradedWeylDivisibility.colAddGen K' l j (map s P) := by
  have h : (map s).comp (Formalism.GradedWeylDivisibility.colAddGen K (r := r) l j).toRingHom =
      (Formalism.GradedWeylDivisibility.colAddGen K' (r := r) l j).toRingHom.comp (map s) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Formalism.GradedWeylDivisibility.colAddGen]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, Formalism.GradedWeylDivisibility.colAddGen, aeval_X]
      split_ifs <;> simp
  exact congrArg (fun φ : MvPolynomial (Fin r × Fin n) K →+* MvPolynomial (Option (Fin r × Fin n)) K' => φ P) h

theorem mti_map_rename_some {r n : ℕ} (P : MvPolynomial (Fin r × Fin n) K) :
    map s (rename (some : Fin r × Fin n → Option (Fin r × Fin n)) P) = rename some (map s P) :=
  map_rename s _ P

theorem mti_map_weighted {r n : ℕ} (ν : Fin n → ℕ) {P : MvPolynomial (Fin r × Fin n) K}
    (hP : P ∈ weightedHomogeneousSubmodule K (Formalism.GradedWeylDivisibility.colW r n) ν) :
    map s P ∈ weightedHomogeneousSubmodule K' (Formalism.GradedWeylDivisibility.colW r n) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hP ⊢
  intro m hm
  rw [coeff_map] at hm
  apply hP
  intro h0
  rw [h0, map_zero] at hm
  exact hm rfl

theorem mti_map_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) {P : MvPolynomial (Fin r × Fin n) K}
    (hP : P ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : map s P ∈ Formalism.GradedWeylDivisibility.dualWeyl K' r n ν := by
  rw [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf] at hP ⊢
  refine ⟨mti_map_weighted s ν hP.1, ?_⟩
  have h2 := hP.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at h2 ⊢
  intro l j hlj
  rw [← mti_map_colAddGen, ← mti_map_rename_some, h2 l j hlj]

end Map

section VVMap

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}

theorem mti_map_ten (F : ι → MvPolynomial (Fin n × Fin n) K) :
    map s (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ)) = ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K' τ (map s (F τ)) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact map_rename s _ (F τ)

theorem mti_map_mem_VV (lam : ι → DomWeight n) {F : Pol K ι n} (hF : F ∈ VV K lam) : map s F ∈ VV K' lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun τ => map s (G τ), fun τ => ?_, mti_map_ten s G⟩
    exact mti_map_dualWeyl s _ (hG τ)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

end VVMap

section RhoMap

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}

end RhoMap

end Formalism.L2.Col
end
end
