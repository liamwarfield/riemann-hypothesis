module

public import Formalism.LocalToGlobal.Columns.XiTopTilRefHolds
public import Formalism.LocalToGlobal.Columns.ChainOneB
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts
public import Formalism.LocalToGlobal.UnitaryNorms.CharGal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.FinrankOE
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TopG

variable {X : Fields} {Pr : Primes X} {R : Ranks}

structure TopNum (R : Ranks) (i : ℕ) : Prop where
  a_eq : R.r + (i + 1 - 1) * R.t = R.N i
  a_le : R.r + (i + 1 - 1) * R.t ≤ (R.N (i + 1) - 1) + 0
  c0 : cOf R i = 0

theorem topNum_of {m2 : ℕ} (hm : R.m = m2 + 2) : TopNum R (m2 + 1) := by
  have h := xt_a_eq (R := R) hm
  have e : R.m - 1 = m2 + 1 + 1 - 1 := by omega
  rw [e] at h
  refine ⟨h, ?_, xt_cOf hm⟩
  rw [h]
  unfold Ranks.N
  have e2 : (m2 + 1 + 1) * (R.t + 1) = (m2 + 1) * (R.t + 1) + (R.t + 1) := by ring
  omega

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xtPhiTopG_congr (hX : X.Ok) (hPr : Pr.Ok) {i : ℕ} (hn : TopNum R i) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x x' : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hD : ∀ p p', p < (R.N (i + 1) - 1) + 0 → p' < R.N i → ∃ d, IntAt P d ∧
      LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x p p' + (qOf P : X.E) * d) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x' = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  have hu := ciQ_notMem_sq hX hPr hP
  have hq := ciQ_mem P
  have hq0 : ((qOf P : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have hkr : R.k ≤ R.r := by unfold Ranks.r; have := R.two_le_m; omega
  unfold PhiTopG
  rw [ite_eq_left hP]
  cases sharp
  · simp only [Bool.false_eq_true, ite_false]
    refine ciPhiG_congr hq hq0 _ _ false x x' ?_ ?_ (Nat.le_add_right _ _) hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')
    · unfold Ranks.r; have := R.two_le_m; omega
    · unfold Ranks.r; have := R.two_le_m; omega
  · simp only [ite_true]
    exact xtPhiGS_congr hq hq0 _ _ x x' hkr hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')

theorem xtPhiTopG_int {i : ℕ} (hn : TopNum R i) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0)) (h : PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x ≠ 0) :
    ∀ p p', p < (R.N (i + 1) - 1) + 0 → p' < R.N i →
      IntAt P (LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x p p') := by
  unfold PhiTopG at h
  rw [ite_eq_left hP] at h
  intro p p' hp hp'
  cases sharp
  · simp only [Bool.false_eq_true, ite_false] at h
    exact ciPhiG_int _ _ false x h p p' hp (hn.a_eq.symm ▸ hp')
  · simp only [ite_true] at h
    exact xtPhiGS_int _ _ x h p p' hp (hn.a_eq.symm ▸ hp')

def topDat (i : ℕ) (P : rowSG Pr sel mu) (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) : X.K :=
  PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1 (prXpG X.E (R.N (i + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i))) *
    ftY sel mu cst P (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y) y''

theorem XiTop_eq {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiTop Ch sel mu cst i p Y p' x = phiT X.K p.deco.1 p'.deco.1 x *
      ∏ P : rowSG Pr sel mu, topDat Ch sel mu cst i P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y)) := rfl

theorem xt_last_lt (R : Ranks) (j : ℕ) : R.N j - 1 < R.N j := by have := R.N_pos j; omega

theorem xt_atNL (j : ℕ) (a : Sp X.E (R.N j)) : atNL X.E (R.N j) (R.N j - 1) a = a ⟨R.N j - 1, xt_last_lt R j⟩ := by
  unfold atNL
  rw [dite_eq_left (xt_last_lt R j)]
  rfl

theorem xt_split {P : HeightOneSpectrum (𝓞 X.E)} (j : ℕ) (a : Sp X.E (R.N j)) :
    (∀ i, IntAt P (a i)) ↔ (∀ i, IntAt P (prXpG X.E (R.N j) a i)) ∧ IntAt P (atNL X.E (R.N j) (R.N j - 1) a) := by
  rw [xt_atNL]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i.1 < R.N j - 1
    · exact h1 ⟨i.1, by omega⟩
    · have : i = ⟨R.N j - 1, xt_last_lt R j⟩ := Fin.ext (by show i.1 = R.N j - 1; have := i.2; omega)
      rw [this]
      exact h2

theorem topDat_congr (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) {i : ℕ} (hn : TopNum R i) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y y₁ : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) (hy : ∀ j, IntAt P.1 ((qOf P.1 : X.E) * y'' j))
    (H : ∀ j : Fin (R.N i), ((∀ l, IntAt P.1 (y (Pi.single j 1) l)) ↔ ∀ l, IntAt P.1 (y₁ (Pi.single j 1) l)) ∧
      ((∀ l, IntAt P.1 (y (Pi.single j 1) l)) → ∀ l, redP P.1 (y (Pi.single j 1) l) = redP P.1 (y₁ (Pi.single j 1) l))) :
    topDat Ch sel mu cst i P y y'' = topDat Ch sel mu cst i P y₁ y'' := by
  classical
  have key := xtLocal (K := X.K) (P := P.1) (q := qOf P.1) (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (k₀ := R.k) (c' := cOf R i)
    (n' := R.N i) (n := R.N (i + 1) - 1) (N := R.N (i + 1)) hn.c0 (PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1)
    (fun x x' h => xtPhiTopG_congr Ch mu hX hPr hn cst.sharp hP x x' h) (fun x h => xtPhiTopG_int Ch mu hn cst.sharp hP x h)
    (cst.psi P) (cst.D P) (hc.D_pos P) (hc.psi_add P) (hc.psi_int P) epsSg (prXpG X.E (R.N (i + 1))) (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1))
    (fun a => xt_split (i + 1) a) y (prXpG X.E (R.N (i + 1)) ∘ₗ y₁) (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y₁)
    (fun j => ⟨(H j).1.trans (xt_split (i + 1) _), fun hall => ⟨fun l => (H j).2 hall _, by
      show redP P.1 (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) _) = redP P.1 (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) _)
      rw [xt_atNL, xt_atNL]
      exact (H j).2 hall _⟩⟩) y'' hy
  unfold topDat ftY
  rw [ite_eq_left hP, ite_eq_left hP]
  exact key

theorem topDat_int {i : ℕ} (hn : TopNum R i) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) (h : topDat Ch sel mu cst i P y y'' ≠ 0) (j : Fin (R.N i)) (l : Fin (R.N (i + 1))) :
    IntAt P.1 (y (Pi.single j 1) l) := by
  classical
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  refine (xt_split (i + 1) (y (Pi.single j 1))).2 ⟨fun l => ?_, ?_⟩ l
  · have := xtPhiTopG_int Ch mu hn cst.sharp hP _ h1 l.1 j.1 l.2 j.2
    rwa [xtEntB hn.c0 _ (by have := l.2; omega) j.2, LinearMap.comp_apply, LinearMap.comp_apply, xtRes j.2] at this
  · unfold ftY at h2
    rw [ite_eq_left hP] at h2
    by_contra h3
    exact h2 (ite_eq_right fun hh => h3 (hh j))

end TopG

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Eq

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (Am : Amb X) (u : Pr.Word)

def oneAl (j : ℕ) (h : j ≤ m2 + 1) : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β j := ⟨(), h⟩

variable {Λ sel mu}

variable (Λ sel mu)

def FixE : Prop :=
  ∀ h ∈ (Λ (m2 + 1)).grp, ∀ w : Pr.vGs,
    ((h w : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal)) : Matrix _ _ (𝓞 X.E ⧸ w.1.asIdeal)).mulVec (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k) =
      Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k

variable {W Λ Ch sel mu cst hQ m2 Am u}

end Eq

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.WithTopLevGTop
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def ChIdx.withTop (L : ChIdx X Pr R Q) (m2 : ℕ) (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) Q) : ChIdx X Pr R Q where
  β j := {b : Option (L.β j) // b.isSome = decide (j ≤ m2 + 1)}
  h j b P := match b.1 with
    | some b' => L.h j b' P
    | none => 1
  levG j b := match b.1 with
    | some b' => L.levG j b'
    | none => Λt j
  levQ j b := match b.1 with
    | some b' => L.levQ j b'
    | none => Θt j

variable (L : ChIdx X Pr R Q) (m2 : ℕ) (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) Q)

def ChIdx.top {j : ℕ} (hj : m2 + 1 < j) : (L.withTop m2 Λt Θt).β j := ⟨none, by simp [Nat.not_le.2 hj]⟩

end Top

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.StabMapRLInjective
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section XpL

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λm : LevFam X.E X.K (R.N R.m) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

@[reducible] def topGSD (u : Pr.Word) : GSD X.K := formGSD (colVal W u R.m (Pr.vT u) Pr.vGs) Λm

variable {W ΛM}


variable {Λm}



end XpL

section XpC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (bm : Λ.β R.m)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

variable {W Λ bm ΛM}





end XpC

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ₀ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

end One

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.OcbBEntEntB
noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def ocbBEnt {E : Type} [Field E] {N' N : ℕ} (n' n q : ℕ) (y : HomE E N' N) (l s : ℕ) : E :=
  Loc.atN (y (Loc.eN E N' s)) l * (q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)

theorem ocbBEnt_entB {E : Type} [Field E] [NumberField E] {N' N : ℕ} (q k₀ c' n' c n : ℕ) (y : HomE E N' N) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y p p' = ocbBEnt n' n q y (LocE.fIdx k₀ c n p) (LocE.fIdx k₀ c' n' p') := rfl

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.DecoratedFrameDiagonalTwistDecoration
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Fr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.SameOn (B : Finset (HeightOneSpectrum (𝓞 E))) (d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : Prop := ∀ P ∈ B, d'.1.at P = d.1.at P

def DecoF.repl (p : DecoF E n ST SG Q) (d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (h : DecoSet.SameOn Q p.deco d') : DecoF E n ST SG Q :=
  ⟨(d', p.1.2), fun P x => by rw [h P.1 P.2]; exact p.2 P x⟩


open Classical in
def DecoF.mv (p : DecoF E n ST SG Q) (d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : DecoF E n ST SG Q :=
  if h : DecoSet.SameOn Q p.deco d' then p.repl d' h else p

theorem DecoF.mv_pos {p : DecoF E n ST SG Q} {d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (h : DecoSet.SameOn Q p.deco d') : p.mv d' = p.repl d' h := by
  unfold DecoF.mv; rw [dite_eq_left h]

theorem DecoF.mv_deco {p : DecoF E n ST SG Q} {d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (h : DecoSet.SameOn Q p.deco d') : (p.mv d').deco = d' := by
  rw [DecoF.mv_pos h]; rfl

theorem DecoSet.sameOn_up {B : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    (hB : ∀ P' ∈ B, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1) (q : 𝓞 E) {x : Sp E n} (hx : x ∈ d.1.N) : DecoSet.SameOn B d (d.up P q x) := by
  intro P' hP'
  unfold DecoSet.up
  split_ifs with hok
  · show localization₂ P'.asIdeal (upN P.1.asIdeal d.1.N x) = localization₂ P'.asIdeal d.1.N
    exact ((upN_spec d.2.lat d.2.uni P.1 hne hx).2.2.1 P' (hB P' hP').1 (hB P' hP').2).localization_eq
  · rfl

end Fr

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem locLat_sameAt {E : Type} [Field E] [NumberField E] {n : ℕ} (SB : Finset (HeightOneSpectrum (𝓞 E))) {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : ∀ P ∈ SB, localization₂ P.asIdeal N' = localization₂ P.asIdeal N) (e : SB → ℤ) : locLat SB N' e = locLat SB N e := by
  unfold locLat
  exact iInf_congr fun P => by rw [h P.1 P.2]

theorem ybSet_sameAt {n : ℕ} {N N' : Submodule (𝓞 X.E) (Sp X.E n)} (h : ∀ P ∈ rowSG Pr sel mu, localization₂ P.asIdeal N' = localization₂ P.asIdeal N) :
    ybSet sel mu cst N' = ybSet sel mu cst N := by
  unfold ybSet
  rw [locLat_sameAt _ h, locLat_sameAt _ h]

end Yb

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.DetChrJoint
section -- merged from Formalism.LocalToGlobal.Columns.HeckeExHost
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

namespace HeckeExHost

variable {X : Fields}

theorem conjO_conjO' (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  show starRingEnd X.E (starRingEnd X.E (x : X.E)) = (x : X.E)
  simp

def conjPrime₂ (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, conjO_conjO']
      exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    have := congrArg X.conjO this
    rwa [conjO_conjO', map_zero] at this

end HeckeExHost

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

section Joint

open Classical

variable {X : Fields} {Pr : Primes X}

theorem conjP_vGs (hX : X.Ok) (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) :
    HeckeExHost.conjPrime₂ P ≠ P ∧ HeckeExHost.conjPrime₂ P ∉ Pr.vGs := by
  have hmem : ∀ j, P ∈ Pr.vG j → X.conjO (Pr.piG j) ∈ P.asIdeal := fun j h => ChainCounts.mem_of_mem_divs h
  have hcomap : ∀ y : 𝓞 X.E, y ∈ (HeckeExHost.conjPrime₂ P).asIdeal ↔ X.conjO y ∈ P.asIdeal := fun y => Iff.rfl
  have hcop : ∀ j, Pr.piG j ∈ P.asIdeal → X.conjO (Pr.piG j) ∈ P.asIdeal → False := by
    intro j h1 h2
    obtain ⟨a, b, hab⟩ := hPr.piG_cop j
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  obtain ⟨i, hi⟩ : ∃ i, P ∈ Pr.vG i := by
    rcases Finset.mem_union.1 hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : Pr.piG i ∈ (HeckeExHost.conjPrime₂ P).asIdeal := (hcomap _).2 (hmem i hi)
    rw [h] at h1
    exact hcop i h1 (hmem i hi)
  · obtain ⟨j, hj⟩ : ∃ j, HeckeExHost.conjPrime₂ P ∈ Pr.vG j := by
      rcases Finset.mem_union.1 h with h' | h'
      · exact ⟨0, h'⟩
      · exact ⟨1, h'⟩
    have h1 : Pr.piG j ∈ P.asIdeal := by
      have := (hcomap _).1 (ChainCounts.mem_of_mem_divs hj)
      rwa [HeckeExHost.conjO_conjO'] at this
    by_cases hij : j = i
    · subst hij
      exact hcop j h1 (hmem j hi)
    · have hg1 : ((Pr.g j : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm j]
        exact Ideal.mul_mem_right _ _ h1
      have hg2 : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm i]
        exact Ideal.mul_mem_left _ _ (hmem i hi)
      have hne : Pr.g j ≠ Pr.g i := by
        have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
        rcases key j i hij with ⟨h0, h1'⟩ | ⟨h0, h1'⟩
        · rw [h0, h1']; exact hPr.g_ne
        · rw [h0, h1']; exact hPr.g_ne.symm
      have hcopZ : Nat.Coprime (Pr.g j) (Pr.g i) := (Nat.coprime_primes (hPr.g_prime j) (hPr.g_prime i)).2 hne
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (Pr.g j : ℤ) + b * (Pr.g i : ℤ) = 1 := by
        refine ⟨Nat.gcdA (Pr.g j) (Pr.g i), Nat.gcdB (Pr.g j) (Pr.g i), ?_⟩
        have := Nat.gcd_eq_gcd_ab (Pr.g j) (Pr.g i)
        rw [hcopZ] at this
        push_cast at this
        linarith
      apply P.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 X.E) = (a : 𝓞 X.E) * ((Pr.g j : ℕ) : 𝓞 X.E) + (b : 𝓞 X.E) * ((Pr.g i : ℕ) : 𝓞 X.E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 X.E)) hab
        push_cast at this
        exact this.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hg1) (Ideal.mul_mem_left _ _ hg2)

end Joint

section Core

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks}

end Core

end DetChrL

end Formalism.L2.Col
end
end
