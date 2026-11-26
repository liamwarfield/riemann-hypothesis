module

public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.StabilizerMapTopIndexAlt
section -- merged from Formalism.LocalToGlobal.Columns.StabilizerMapMaximalIndex
section -- merged from Formalism.LocalToGlobal.Columns.DilYStab
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Pairs

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 j : ℕ}


variable (W cst L u m2 j) in
abbrev PtY (b : L.β j) : Type := (cplAt W sel mu cst L u m2 j b).Pts

@[reducible] def ptYAct (b : L.β j) : MulAction ((chFY W sel mu cst L u m2 j).mem b).G (PtY W cst L u m2 j b) := ((chFY W sel mu cst L u m2 j).mem b).actD

attribute [local instance] ptYAct

def PtY.deco {b : L.β j} (x : PtY W cst L u m2 j b) : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs) := x.1.1.deco

theorem sameOn_QE {d d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)} (h : DecoSet.SameOn (rowSG Pr sel mu) d d') :
    DecoSet.SameOn (QE sel (mu : Chr X.F X.E X.K)) d d' := by
  classical
  exact fun P hP => h P (Finset.mem_union_right _ hP)

theorem cplAt_ys_mv (b : L.β j) (p : ChPt (R := R) sel mu u j) {d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)}
    (h : DecoSet.SameOn (rowSG Pr sel mu) p.deco d') :
    (cplAt W sel mu cst L u m2 j b).ys (p.mv d') = (cplAt W sel mu cst L u m2 j b).ys p := by
  classical
  show (if j = m2 + 1 then ybSet sel mu cst (p.mv d').deco.1.N else {Set.univ}) = if j = m2 + 1 then ybSet sel mu cst p.deco.1.N else {Set.univ}
  rw [DecoF.mv_deco (sameOn_QE h)]
  split_ifs
  · exact ybSet_sameAt sel mu cst h
  · rfl

def PtY.repl {b : L.β j} (x : PtY W cst L u m2 j b) (d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs))
    (h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d') : PtY W cst L u m2 j b :=
  ⟨(x.1.1.mv d', x.1.2), by rw [cplAt_ys_mv b x.1.1 h]; exact x.2⟩


open Classical in
def PtY.mv {b : L.β j} (x : PtY W cst L u m2 j b) (d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)) : PtY W cst L u m2 j b :=
  if h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d' then x.repl d' h else x

end Pairs

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct

def frameOfY {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs)) : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
  Classical.choose (exists_frameD P (hcnt_isFullLattice_of_unimodular d.2.lat d.2.uni))

theorem frameOfY_spec {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs)) :
    ∀ x, frameOfY u P d x ∈ localization₂ P.asIdeal d.1.N ↔ x ∈ stdAt X.E n P :=
  Classical.choose_spec (exists_frameD P (hcnt_isFullLattice_of_unimodular d.2.lat d.2.uni))

variable (hm : R.m = m2 + 2)

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm}

end Top

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.RecChainYKmap
open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col.Sc

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker Formalism.L2.Col

section Charts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev SecY (u : Pr.Word) (m2 : ℕ) : Type := ∀ j b, ((Formalism.L2.Col.chFY W sel mu cst L u m2 j).mem b).Sec

variable {W sel mu cst L}

variable {Ch}

end Charts

end Formalism.L2.Col.Sc
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Col Formalism.L2.Col.Sc

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct


variable (sel mu) in
structure TopFr where
  fr : ∀ (_P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (_d : DecoSet (E := X.E) (n := R.N R.m - 1) (ST := ∅) (SG := SG')), Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)
  spec : ∀ P d x, fr P d x ∈ localization₂ P.1.asIdeal (tilR hSG u d).1.N ↔ x ∈ stdAt X.E (R.N R.m) P.1

variable (hm : R.m = m2 + 2) (F : TopFr sel mu u hSG)

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm F}

variable (sec : SecY W sel mu cst (L₀.withTop m2 Λt Θt) u m2)

end Top

end Formalism.L2.Col.Sc.Fr
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def tfaExt {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) : Sp E N ≃ₗ[E] Sp E N := by
  subst hN
  exact extE f

theorem tfa_std_iff {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (x : Sp E (n + 1)) :
    x ∈ stdAt E (n + 1) Q ↔ initL E n x ∈ stdAt E n Q ∧ IntAt Q (x (Fin.last n)) := by
  rw [ciMem_stdAt, ciMem_stdAt]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases h2 (fun j => ?_) i
    exact h1 j

def tfaD {n : ℕ} (z : E) (hz : z ≠ 0) : Sp E (n + 1) ≃ₗ[E] Sp E (n + 1) :=
  LinearEquiv.piCongrRight fun i : Fin (n + 1) => if i = Fin.last n then LinearEquiv.smulOfNeZero E E z hz else LinearEquiv.refl E E

theorem tfaD_apply {n : ℕ} (z : E) (hz : z ≠ 0) (x : Sp E (n + 1)) (i : Fin (n + 1)) :
    tfaD z hz x i = if i = Fin.last n then z * x i else x i := by
  unfold tfaD
  rw [LinearEquiv.piCongrRight_apply]
  split_ifs with h
  · simp [LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
  · rfl

theorem tfaD_symm_apply {n : ℕ} (z : E) (hz : z ≠ 0) (x : Sp E (n + 1)) (i : Fin (n + 1)) :
    (tfaD z hz).symm x i = if i = Fin.last n then z⁻¹ * x i else x i := by
  have key : tfaD z hz (fun j => if j = Fin.last n then z⁻¹ * x j else x j) = x := by
    funext j
    rw [tfaD_apply]
    by_cases h : j = Fin.last n
    · subst h
      simp [hz]
    · simp only [h, if_false]
  conv_lhs => rw [← key]
  rw [LinearEquiv.symm_apply_apply]

def tfaExtZ {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) (z : E) (hz : z ≠ 0) : Sp E N ≃ₗ[E] Sp E N := by
  subst hN
  exact (tfaD z hz).trans (extE f)

theorem tfaZ_spec {SG : Finset (HeightOneSpectrum (𝓞 E))} {ST : Finset (HeightOneSpectrum (𝓞 E))} {N n : ℕ} (hN : N = n + 1) (pi : 𝓞 E)
    (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) (hOk : (d.1.til (ST := ST) pi).Ok) (w : SG) (hw : pi ∉ w.1.asIdeal) (hz : (algebraMap (𝓞 E) E pi) ≠ 0)
    (x : Sp E N) :
    tfaExtZ hN (d.1.liftFr w) (algebraMap (𝓞 E) E pi) hz x ∈ localization₂ w.1.asIdeal (DecoSet.tilH (ST := ST) hN pi d).1.N ↔
      x ∈ stdAt E N w.1 := by
  subst hN
  have hl := Deco.liftFr_spec (d.2.hasLift w)
  show extE (d.1.liftFr w) (tfaD (algebraMap (𝓞 E) E pi) hz x) ∈ localization₂ w.1.asIdeal (DecoSet.til (ST := ST) pi d).1.N ↔ _
  unfold DecoSet.til
  rw [dif_pos hOk]
  show extE (d.1.liftFr w) (tfaD (algebraMap (𝓞 E) E pi) hz x) ∈ localization₂ w.1.asIdeal (tilN d.1.N) ↔ _
  have hinit : initL E n (tfaD (algebraMap (𝓞 E) E pi) hz x) = initL E n x := by
    funext i
    show tfaD _ hz x (Fin.castSucc i) = x (Fin.castSucc i)
    rw [tfaD_apply, if_neg (Fin.castSucc_ne_last i)]
  have hlast : tfaD (algebraMap (𝓞 E) E pi) hz x (Fin.last n) = algebraMap (𝓞 E) E pi * x (Fin.last n) := by
    rw [tfaD_apply, if_pos rfl]
  rw [mem_localization_tilN, initL_extE, extE_last, hinit, hlast, tfa_std_iff]
  refine and_congr (hl.1 _) ⟨fun h => ?_, fun h => (IntAt.coe w.1 pi).mul h⟩
  have h2 := (xtIntAt_piInv hw).mul h
  rwa [← mul_assoc, inv_mul_cancel₀ hz, one_mul] at h2

end Gen

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (u : Pr.Word)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')


variable (sel mu) in
open Classical in
def topFrA (hQS : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∈ SG') : TopFr (R := R) sel mu u hSG where
  fr P d := if h : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal then
      tfaExtZ (N_m_succ R) (d.1.liftFr ⟨P.1, hQS P.1 P.2⟩) (algebraMap (𝓞 X.E) X.E (Pr.piT u))
        (fun h0 => h.2 (by rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 X.E) X.E)] at h0; rw [h0]; exact zero_mem _))
    else frameOfY u P.1 (tilR hSG u d)
  spec P d x := by
    by_cases h : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal
    · rw [dif_pos h]
      exact tfaZ_spec (N_m_succ R) (Pr.piT u) d h.1 ⟨P.1, hQS P.1 P.2⟩ h.2 _ x
    · rw [dite_eq_right h]
      exact frameOfY_spec u P.1 (tilR hSG u d) x


end Top

end Formalism.L2.Col.Sc.Fr
