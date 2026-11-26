module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBad
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqAtDetRootsOfCongruent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumBasePointsLawRationalTwistPrimes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawUnderTwoLevelsModHalfLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistRationalLevelElementsSameCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTrivialCharLevelEltRationalAtTwistPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTrivialCharLevelEltRationalAtTwistPrimes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

open Formalism.L2.DIV Formalism.L2.Col Formalism.UG GlobalTheory.Mem.Col2.AdT GlobalTheory.Mem.Col2.TC

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevelAll

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_one_apply (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (r s : Fin n) :
    adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

theorem conj_bound (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E)) (ε : WithZero (Multiplicative ℤ)) (hε : ε < 1)
    (hP : ∀ r s, Valued.v (adAt F P (u.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ ε) (r s : Fin n) :
    Valued.v (adAt F (conjPrime₂ P) (u.1 r s) - (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s) ≤ ε := by
  subst hJ
  have hinv : ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) =
      1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) := by
    have h : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) *
        ((1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) * (u : Matrix (Fin n) (Fin n) (AfE F E)) =
        (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hu
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
    have e : 1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) =
        cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) := by
      unfold cT
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_sub, Matrix.transpose_one, add_sub_cancel]
    rw [e]
    calc ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))
        = (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) * (u : Matrix (Fin n) (Fin n) (AfE F E))) *
            ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) := by rw [h, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h1 : (1 + ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) *
      (1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) = 1 := by
    rw [← hinv, add_sub_cancel, Units.mul_inv]
  have h2 := congrArg (adAt F (conjPrime₂ P)).mapMatrix h1
  rw [map_mul, map_add (f := _), map_add (f := _), map_one] at h2
  have key := GlobalTheory.Mem.Col2.AdT.Opn.val_inv_le Valued.v _ _ h2 ε hε (fun a b => ?_) r s
  · have e : ((adAt F (conjPrime₂ P)).mapMatrix ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) r s =
        adAt F (conjPrime₂ P) (u.1 r s) - (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s := by
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub, adAt_one_apply]
    rw [← e]; exact key
  · show Valued.v (adAt F (conjPrime₂ P) (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) b a))) ≤ ε
    rw [GlobalTheory.Mem.Col2.valued_sigR hc, GlobalTheory.CharValCompare.conjP_conjP, Matrix.sub_apply, map_sub, adAt_one_apply]
    exact hP b a

end Gen

theorem map_prod_cases {G M κ : Type} [Monoid G] [Monoid M] (f : κ → G) (c : G →* M)
    (hpair : ∀ P P' : κ, P ≠ P' → c (f P) = 1 ∨ c (f P') = 1) :
    ∀ L : List κ, L.Nodup → c (L.map f).prod = 1 ∨ ∃ P ∈ L, c (L.map f).prod = c (f P) := by
  have hall : ∀ (P : κ) (L : List κ), c (f P) ≠ 1 → (∀ P' ∈ L, P' ≠ P) → c (L.map f).prod = 1 := by
    intro P L h1 hL
    induction L with
    | nil => simp
    | cons P' L ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih fun x hx => hL x (List.mem_cons_of_mem _ hx), mul_one]
      exact (hpair P P' (Ne.symm (hL P' (List.mem_cons.2 (Or.inl rfl))))).resolve_left h1
  intro L
  induction L with
  | nil => intro _; left; simp
  | cons P L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases h1 : c (f P) = 1
    · rw [h1, one_mul]
      rcases ih hL.2 with h | ⟨P', hP', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨P', List.mem_cons_of_mem _ hP', h⟩
    · rw [hall P L h1 fun P' hP' e => hL.1 (e ▸ hP'), mul_one]
      exact Or.inr ⟨P, List.mem_cons.2 (Or.inl rfl), rfl⟩


set_option maxHeartbeats 12000000 in
theorem exists_level_elt_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z S → ∀ (N : ℕ) (g : TC.GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P (((g * (show TC.GA B (B.R.N i) from z.1) : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin (B.R.N i)), Valued.v (adAt B.host.F P (((show TC.GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s)) ≤ WithZero.exp (-(N : ℤ)) := by
  intro B X I hOk hPins l Z a T i hi bad S hChi N g
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hgr : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  let cP : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), GA B (B.R.N i) →* Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.adicCompletion B.fields.E) :=
    fun P => (RingHom.mapMatrix (adAt B.host.F P)).toMonoidHom.comp (Units.coeHom _)
  have cP_apply : ∀ P (g : GA B (B.R.N i)) r s, cP P g r s = adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) := fun _ _ _ _ => rfl
  let ι : S.U →* GA B (B.R.N i) := S.U.subtype
  have hexp : WithZero.exp (-((max N 1 : ℕ) : ℤ)) ≤ WithZero.exp (-(N : ℤ)) := WithZero.exp_le_exp.2 (by omega)
  have hexp1 : WithZero.exp (-((max N 1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hs : ∀ P : SBof I a, GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := fun P => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) 0 P 1).1
  have hsep : ∀ P P' : SBof I a, P ≠ P' → P.1 ∈ I.Q a → (P'.1 = P.1 ∨ P'.1 = Formalism.L2.Col.conjPrime₂ P.1) → False := by
    intro P P' hne hP h
    rcases h with h | h
    · exact hne (Subtype.ext h.symm)
    obtain ⟨v, hv, hv'⟩ := LevelElt.place_under I hOk hPins l Z a P hP
    apply hv' P' (Ne.symm hne)
    rw [hs] at hv ⊢
    have hc := congrArg HeightOneSpectrum.asIdeal ((GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).2 (Or.inr h))
    exact Eq.trans hv hc.symm
  have hsel : ∀ P : SBof I a, ∃ z : S.U, S.chi z = 1 ∧
      (∀ Q : HeightOneSpectrum (𝓞 B.fields.E), cP Q (ι z) = 1 ∨ (P.1 ∈ I.Q a ∧ (Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1))) ∧
      (∀ (Q : HeightOneSpectrum (𝓞 B.fields.E)) r s, Valued.v (cP Q (ι z) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Q.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g * (show GA B (B.R.N i) from z.1) : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, -⟩ := LevelElt.place_under I hOk hPins l Z a P hP
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ := LevelElt.one_prime I hOk hPins l Z a T i hi bad S hChi P hP v hv (max N 1) g 1
      have hzU := ((S.U_eq _).1 z.2).1
      have hbP := ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) (max N 1) P z.1).2.2).1 hz3
      have hvP := hv
      rw [hs] at hvP
      have hoff : ∀ Q : HeightOneSpectrum (𝓞 B.fields.E), ¬ (Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1) → cP Q (ι z) = 1 := fun Q hQ =>
        Matrix.ext fun r s => by
          rw [cP_apply]
          exact LevelElt.support_one z.1 v hz2 Q (fun hO => hQ ((GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 Q).1
            (HeightOneSpectrum.ext (Eq.trans (Eq.symm hO) hvP)))) r s
      refine ⟨z, hz1, fun Q => ?_, fun Q r s => ?_, fun _ => ?_⟩
      · by_cases hQ : Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1
        · exact Or.inr ⟨hP, hQ⟩
        · exact Or.inl (hoff Q hQ)
      · by_cases hQ : Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1
        · rw [cP_apply]
          rcases hQ with rfl | rfl
          · exact (hbP r s).trans hexp
          · exact (conj_bound (I.rec7 l Z).sp.cm hgr hzU P.1 _ hexp1 hbP r s).trans hexp
        · rw [hoff Q hQ, sub_self, Valuation.map_zero]
          exact zero_le'
      · obtain ⟨γ, hγ⟩ := hz4
        exact ⟨γ, fun r s => by rw [← hγ r s, mul_one]⟩
    · refine ⟨1, map_one _, fun Q => Or.inl (by rw [map_one, map_one]), fun Q r s => ?_, fun h => absurd h hP⟩
      rw [map_one, map_one, sub_self, Valuation.map_zero]; exact zero_le'
  choose zf hzf1 hzf2 hzf3 hzf4 using hsel
  have hpair : ∀ (Q : HeightOneSpectrum (𝓞 B.fields.E)) (P P' : SBof I a), P ≠ P' → cP Q (ι (zf P)) = 1 ∨ cP Q (ι (zf P')) = 1 := by
    intro Q P P' hne
    rcases hzf2 P Q with h | ⟨hP, hQ⟩
    · exact Or.inl h
    rcases hzf2 P' Q with h' | ⟨-, hQ'⟩
    · exact Or.inr h'
    exfalso
    apply hsep P P' hne hP
    rcases hQ with rfl | rfl <;> rcases hQ' with h2 | h2
    · exact Or.inl h2.symm
    · refine Or.inr ?_
      rw [h2, GlobalTheory.CharValCompare.conjP_conjP]
    · exact Or.inr h2.symm
    · have h3 := congrArg Formalism.L2.Col.conjPrime₂ h2
      rw [GlobalTheory.CharValCompare.conjP_conjP, GlobalTheory.CharValCompare.conjP_conjP] at h3
      exact Or.inl h3.symm
  have hone : ∀ P P' : SBof I a, P' ≠ P → cP P'.1 (ι (zf P)) = 1 := by
    intro P P' hne
    rcases hzf2 P P'.1 with h | ⟨hP, hQ⟩
    · exact h
    · exact (hsep P P' hne.symm hP hQ).elim
  have hlistP : ∀ (L : List (SBof I a)), L.Nodup → ∀ P' : SBof I a, cP P'.1 (ι (L.map zf).prod) = if P' ∈ L then cP P'.1 (ι (zf P')) else 1 := by
    intro L
    induction L with
    | nil => intro _ P'; simp
    | cons P L ih =>
      intro hL P'
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, map_mul, ih hL.2]
      by_cases h : P = P'
      · subst h
        simp [hL.1]
      · rw [hone P P' (Ne.symm h)]
        simp [Ne.symm h]
  obtain ⟨w, hw⟩ : ∃ w : S.U, w = ((Finset.univ : Finset (SBof I a)).toList.map zf).prod := ⟨_, rfl⟩
  have hwP : ∀ P : SBof I a, cP P.1 (ι w) = cP P.1 (ι (zf P)) := fun P => by
    rw [hw, hlistP _ (Finset.nodup_toList _) P, if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  have hchiw : S.chi w = 1 := by
    rw [hw, map_list_prod]
    refine List.prod_eq_one fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [List.mem_map] at hz
    obtain ⟨P, -, rfl⟩ := hz
    exact hzf1 P
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  refine ⟨w, hchiw, fun P hP => ?_, fun Q r s => ?_⟩
  · obtain ⟨γ, hγ⟩ := hzf4 ⟨P, hQsub P hP⟩ hP
    refine ⟨(γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E), fun r s => ?_⟩
    have e0 : cP P (ι w) = cP P (ι (zf ⟨P, hQsub P hP⟩)) := hwP ⟨P, hQsub P hP⟩
    have e1 : cP P (g * ι w) = cP P (g * ι (zf ⟨P, hQsub P hP⟩)) := by rw [map_mul, map_mul, e0]
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · rw [map_sub, adAt_one_apply]
    change Valued.v (cP Q (ι w) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Q.adicCompletion B.fields.E)) r s) ≤ _
    rcases map_prod_cases zf ((cP Q).comp ι) (hpair Q) _ (Finset.nodup_toList _) with h | ⟨P, -, h⟩
    · rw [← hw] at h
      change cP Q (ι w) = _ at h
      rw [h, sub_self, Valuation.map_zero]; exact zero_le'
    · rw [← hw] at h
      change cP Q (ι w) = _ at h
      rw [h]; exact hzf3 P Q r s

end GlobalTheory.Mem.Col2.AdT.LevelAll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTrivialCharLevelEltRationalAtTwistPrimesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trivialCharLevel_elt_rational_at_twistPrimes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z S → ∀ (N : ℕ) (g : TC.GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P (((g * (show TC.GA B (B.R.N i) from z.1) : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin (B.R.N i)), Valued.v (adAt B.host.F P (((show TC.GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s)) ≤ WithZero.exp (-(N : ℤ)) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LevelAll.exists_level_elt_all | exact GlobalTheory.Mem.Col2.AdT.LevelAll.exists_level_elt_all | (intros; apply GlobalTheory.Mem.Col2.AdT.LevelAll.exists_level_elt_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfMatrixMoveDeepCongruenceBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfMatrixMoveDeepCongruenceBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.AdForm.DeepMove

section Val
variable {R Γ : Type} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ)

theorem one_entry_le {n : ℕ} (r s : Fin n) : v ((1 : Matrix (Fin n) (Fin n) R) r s) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem inv_entry_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hXY : X * Y = 1) {ε : Γ} (hε : ε < 1)
    (hX : ∀ r s, v ((X - 1) r s) ≤ ε) : ∀ r s, v ((Y - 1) r s) ≤ ε := by
  have hY : Y - 1 = -((X - 1) * Y) := by
    rw [Matrix.sub_mul, hXY, Matrix.one_mul, neg_sub]
  have hb : ∀ r s, v (Y r s) ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, s, hrs⟩ := hcon
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun p : Fin n × Fin n => v (Y p.1 p.2))
      ⟨(r, s), Finset.mem_univ _⟩
    have hm : 1 < v (Y p.1 p.2) := lt_of_lt_of_le hrs (hp (r, s) (Finset.mem_univ _))
    have h2 : v ((Y - 1) p.1 p.2) < v (Y p.1 p.2) := by
      rw [hY, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
      refine lt_of_le_of_lt (Valuation.map_sum_le _ (g := ε * v (Y p.1 p.2)) fun k _ => ?_) ?_
      · rw [map_mul]
        exact mul_le_mul' (hX _ _) (hp (k, p.2) (Finset.mem_univ _))
      · exact mul_lt_of_lt_one_left (zero_lt_one.trans hm) hε
    have e : Y p.1 p.2 = (1 : Matrix (Fin n) (Fin n) R) p.1 p.2 + (Y - 1) p.1 p.2 := by
      rw [Matrix.sub_apply]; ring
    have h3 : v (Y p.1 p.2) < v (Y p.1 p.2) := by
      calc v (Y p.1 p.2) = v ((1 : Matrix (Fin n) (Fin n) R) p.1 p.2 + (Y - 1) p.1 p.2) := by rw [← e]
        _ ≤ max (v ((1 : Matrix (Fin n) (Fin n) R) p.1 p.2)) (v ((Y - 1) p.1 p.2)) := Valuation.map_add _ _ _
        _ < v (Y p.1 p.2) := max_lt ((one_entry_le v _ _).trans_lt hm) h2
    exact lt_irrefl _ h3
  intro r s
  rw [hY, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  calc _ ≤ ε * 1 := mul_le_mul' (hX _ _) (hb _ _)
    _ = ε := mul_one _

theorem moved_entry_le {a b : ℕ} (X : Matrix (Fin a) (Fin a) R) (Y : Matrix (Fin b) (Fin b) R) (M : Matrix (Fin b) (Fin a) R)
    {ε : Γ} (hε : ε ≤ 1) (hX : ∀ r s, v ((X - 1) r s) ≤ ε) (hY : ∀ r s, v ((Y - 1) r s) ≤ ε)
    (hM : ∀ r s, v (M r s) ≤ 1) : ∀ r s, v ((Y * M * X - M) r s) ≤ ε := by
  have hXb : ∀ r s, v (X r s) ≤ 1 := fun r s => by
    have e : X r s = (1 : Matrix (Fin a) (Fin a) R) r s + (X - 1) r s := by rw [Matrix.sub_apply]; ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le (one_entry_le v _ _) ((hX r s).trans hε))
  have e : Y * M * X - M = (Y - 1) * M * X + M * (X - 1) := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]; abel
  have h1 : ∀ r s, v (((Y - 1) * M : Matrix (Fin b) (Fin a) R) r s) ≤ ε := fun r s => by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    calc _ ≤ ε * 1 := mul_le_mul' (hY _ _) (hM _ _)
      _ = ε := mul_one _
  intro r s
  rw [e, Matrix.add_apply]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    calc _ ≤ ε * 1 := mul_le_mul' (h1 _ _) (hXb _ _)
      _ = ε := mul_one _
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * ε := mul_le_mul' (hM _ _) (hX _ _)
      _ = ε := one_mul _

end Val

theorem exists_exp_le_natCast {E : Type} [Field E] [NumberField E] (L : ℕ) (hL : 0 < L) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ P : HeightOneSpectrum (𝓞 E),
      WithZero.exp (-(N₀ : ℤ)) ≤ Valued.v ((L : ℕ) : P.adicCompletion E) := by
  set m := Ideal.absNorm (Ideal.span {((L : ℕ) : 𝓞 E)}) with hm
  have hL0 : ((L : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hL.ne'
  have hm0 : m ≠ 0 := by
    rw [hm, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hL0
  refine ⟨m, Nat.one_le_iff_ne_zero.2 hm0, fun P => ?_⟩
  have e1 : ((L : ℕ) : P.adicCompletion E) = algebraMap E _ (algebraMap (𝓞 E) E ((L : ℕ) : 𝓞 E)) := by simp
  rw [e1, GlobalTheory.Mem.Col2.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  by_contra h
  push_neg at h
  have hd := (HeightOneSpectrum.intValuation_le_pow_iff_dvd P _ m).1 h.le
  have h2 : Ideal.absNorm (P.asIdeal ^ m) ∣ m := map_dvd Ideal.absNorm hd
  rw [map_pow] at h2
  have hP1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h1 => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
  have hP0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hP2 : 2 ≤ Ideal.absNorm P.asIdeal := by omega
  have h3 : 2 ^ m ≤ m := (Nat.pow_le_pow_left hP2 m).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h2)
  exact absurd h3 (not_le.2 (Nat.lt_two_pow_self))

end GlobalTheory.AdForm.DeepMove

namespace GlobalTheory.AdForm.DeepMove

theorem map_sub_one_apply {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ} (f : R →+* R') (A : Matrix (Fin n) (Fin n) R)
    (r s : Fin n) : f ((A - 1) r s) = (A.map f - 1) r s := by
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, map_sub]
  split_ifs <;> simp

theorem exists_den_mat {D : D7} {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) : ∃ d : ℕ, 0 < d ∧
    ∀ r s, toEAf D ((d : AE D) * M r s) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E := by
  choose x y hy e using fun r s => GlobalTheory.AdeleBaseChange.exists_approx (F := D.host.F) (E := D.host.E) (toEAf D (M r s))
  obtain ⟨d, hd, hint⟩ := GlobalTheory.AdeleBaseChange.exists_nat_mul_integral
    (Finset.image (fun p : Fin m × Fin n => x p.1 p.2) Finset.univ)
  refine ⟨d, hd, fun r s => ?_⟩
  obtain ⟨z, hz⟩ := hint (x r s) (Finset.mem_image.2 ⟨(r, s), Finset.mem_univ _, rfl⟩)
  rw [map_mul, map_natCast, e r s, mul_add]
  refine add_mem ?_ (mul_mem (natCast_mem _ d) (hy r s))
  have hc : ((d : ℕ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      ((d : ℕ) : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
      (B := FiniteAdeleRing (𝓞 D.host.F) D.host.F)) d).symm
  have e2 : ((d : ℕ) : Formalism.L2.DIV.AfE D.host.F D.host.E) * (x r s ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      (algebraMap (𝓞 D.host.E) D.host.E z) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    rw [hc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hz, nsmul_eq_mul]
  rw [e2]
  exact GlobalTheory.AdForm.CongAtIdem.tmul_one_mem_rInt z.isIntegral_coe

theorem actO_deep : ∀ (D : D7) (S T : HSp D) {a b : ℕ} (ha : S.rank = a) (hb : T.rank = b) (e : AE D) (M : WO S T), IsHalf e M → ∀ (k : ℕ), 0 < k → ∃ N₀ : ℕ, ∀ (w : GA D S) (w' : GA D T), w ∈ GfC S → w' ∈ GfC T → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin a), Valued.v (adAt D.host.F P (finM S ha w r s - (1 : Matrix (Fin a) (Fin a) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin b), Valued.v (adAt D.host.F P (finM T hb w' r s - (1 : Matrix (Fin b) (Fin b) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → ∃ t : WO S T, t ∈ stdHom S T ∧ IsHalf e t ∧ actO S T w⁻¹ w'⁻¹ M = M + k • t := by
  intro D S T a b ha hb e M hM k hk
  subst ha
  subst hb
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.AdForm.exists_nsmul_mem_stdHom S T
  obtain ⟨d, hd, hdM⟩ := exists_den_mat (D := D) M
  obtain ⟨N₀, hN₀, hN⟩ := exists_exp_le_natCast (E := D.host.E) (d * (k * K)) (Nat.mul_pos hd (Nat.mul_pos hk hK))
  refine ⟨N₀, fun w w' hw hw' hA hB => ?_⟩
  have hc0 : (((k * K : ℕ) : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hk hK).ne'
  have hact : actO S T w⁻¹ w'⁻¹ M = ((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w⁻¹⁻¹ : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := rfl
  rw [inv_inv] at hact
  obtain ⟨Dm, hDm⟩ : ∃ Dm : WO S T, Dm = actO S T w⁻¹ w'⁻¹ M - M := ⟨_, rfl⟩
  let t₀ : WO S T := Matrix.of fun i j => incA D (((k * K : ℕ) : D.host.E))⁻¹ * Dm i j
  have hent : ∀ i j, Dm i j = (((k * K : ℕ) : AE D)) * t₀ i j := fun i j => by
    have h1 : (((k * K : ℕ) : AE D)) = incA D (((k * K : ℕ) : D.host.E)) := (map_natCast (incA D) _).symm
    have h2 : incA D (((k * K : ℕ) : D.host.E)) * incA D (((k * K : ℕ) : D.host.E))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    show Dm i j = (((k * K : ℕ) : AE D)) * (incA D (((k * K : ℕ) : D.host.E))⁻¹ * Dm i j)
    rw [h1, ← mul_assoc, h2, one_mul]
  have hkt : k • (K • t₀) = Dm := by
    ext i j
    rw [hent i j]
    simp only [Matrix.smul_apply, nsmul_eq_mul]
    push_cast
    ring
  refine ⟨K • t₀, hKm t₀ ?_ ?_, ?_, ?_⟩
  ·
    have hY : (Formalism.L2.Theta.mt S w).map (infPart D) = 1 :=
      (GlobalTheory.FinPl.KOpen.map_eq_one_iff _ _).2 ((GlobalTheory.FinPl.KOpen.mem_GfC_iff S w).1 hw)
    have hX : (Formalism.L2.Theta.mt T w'⁻¹).map (infPart D) = 1 :=
      (GlobalTheory.FinPl.KOpen.map_eq_one_iff _ _).2 ((GlobalTheory.FinPl.KOpen.mem_GfC_iff T w'⁻¹).1 (inv_mem hw'))
    have h0 : Dm.map (infPart D) = 0 := by
      have e3 : (((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))).map (infPart D) = M.map (infPart D) := by
        rw [Matrix.map_mul, Matrix.map_mul, hX, hY, Matrix.one_mul, Matrix.mul_one]
      rw [hDm, hact]
      ext i j
      have e5 := congrFun (congrFun e3 i) j
      simp only [Matrix.map_apply] at e5
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, e5, sub_self, Matrix.zero_apply]
    ext i j
    have := congrFun (congrFun h0 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this ⊢
    simp only [t₀, Matrix.of_apply, map_mul, this, mul_zero]
  ·
    intro i j
    refine (mem_rInt_iff _ _ _).2 fun P => ?_
    show Valued.v (adAt D.host.F P (toEAf D (t₀ i j))) ≤ 1
    let φ : AE D →+* P.adicCompletion D.host.E := (adAt D.host.F P).comp (toEAf D)
    have hε : WithZero.exp (-(N₀ : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hXw : ∀ r s, Valued.v (((Formalism.L2.Theta.mt S w).map φ - 1) r s) ≤ WithZero.exp (-(N₀ : ℤ)) := fun r s => by
      have h := hA P r s
      rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl] at h
      rw [← map_sub_one_apply]
      simpa [φ, Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, apply_ite] using h
    have hXw' : ∀ r s, Valued.v (((Formalism.L2.Theta.mt T w').map φ - 1) r s) ≤ WithZero.exp (-(N₀ : ℤ)) := fun r s => by
      have h := hB P r s
      rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl] at h
      rw [← map_sub_one_apply]
      simpa [φ, Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, apply_ite] using h
    have hinv : (Formalism.L2.Theta.mt T w').map φ * (Formalism.L2.Theta.mt T w'⁻¹).map φ = 1 := by
      rw [← Matrix.map_mul, ← GlobalTheory.AdForm.CongAtIdem.mt_mul', mul_inv_cancel, GlobalTheory.AdForm.CongAtIdem.mt_one',
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hY' := inv_entry_le Valued.v _ _ hinv hε hXw'
    let Md : Matrix (Fin T.rank) (Fin S.rank) (AE D) := Matrix.of fun r s => (d : AE D) * M r s
    have hMd : ∀ r s, Valued.v (Md.map φ r s) ≤ 1 := fun r s => by
      have := (mem_rInt_iff _ _ _).1 (hdM r s) P
      exact this
    have hmv := moved_entry_le Valued.v _ _ _ hε.le hXw hY' hMd i j
    have hDmd : (d : AE D) * Dm i j = (((Formalism.L2.Theta.mt T w'⁻¹ * Md : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) - Md) i j := by
      have hs : Md = (d : AE D) • (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by ext r s; simp [Md]
      rw [hDm, hact, hs, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
      simp [Matrix.smul_apply]
    have hφ : φ ((d : AE D) * Dm i j) = ((Formalism.L2.Theta.mt T w'⁻¹).map φ * Md.map φ * (Formalism.L2.Theta.mt S w).map φ - Md.map φ) i j := by
      have e4 : (((Formalism.L2.Theta.mt T w'⁻¹ * Md : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))).map φ =
          (Formalism.L2.Theta.mt T w'⁻¹).map φ * Md.map φ * (Formalism.L2.Theta.mt S w).map φ := by
        rw [Matrix.map_mul, Matrix.map_mul]
      rw [hDmd, ← e4, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, map_sub]
    rw [← hφ, hent i j, ← mul_assoc, ← Nat.cast_mul, map_mul, map_natCast, map_mul] at hmv
    have hL := hN P
    have hL0 : Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) ≠ 0 := fun h0 => by
      rw [h0] at hL
      exact WithZero.exp_ne_zero (le_antisymm hL zero_le')
    have h2 : Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * Valued.v (φ (t₀ i j)) ≤
        Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * 1 := by
      rw [mul_one]; exact hmv.trans hL
    calc Valued.v (φ (t₀ i j))
        = (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E))⁻¹ *
          (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * Valued.v (φ (t₀ i j))) := (inv_mul_cancel_left₀ hL0 _).symm
      _ ≤ (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E))⁻¹ *
          (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * 1) := mul_le_mul' le_rfl h2
      _ = 1 := inv_mul_cancel_left₀ hL0 _
  ·
    have hMe : e • (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = M := by ext r s; exact hM r s
    have hDe : ∀ i j, e * Dm i j = Dm i j := fun i j => by
      have h3 : e • (((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))) = (((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
        rw [← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 2
      have h4 := congrFun (congrFun h3 i) j
      rw [Matrix.smul_apply, smul_eq_mul] at h4
      rw [hDm, hact, Matrix.sub_apply, mul_sub, h4, hM i j]
    intro i j
    simp only [t₀, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    calc e * ((K : AE D) * (incA D (((k * K : ℕ) : D.host.E))⁻¹ * Dm i j))
        = (K : AE D) * (incA D (((k * K : ℕ) : D.host.E))⁻¹ * (e * Dm i j)) := by ring
      _ = _ := by rw [hDe i j]
  · rw [hkt, hDm]
    abel

end GlobalTheory.AdForm.DeepMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfMatrixMoveDeepCongruenceBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfMatrix_move_deepCongruence_bound : ∀ (D : D7) (S T : HSp D) {a b : ℕ} (ha : S.rank = a) (hb : T.rank = b) (e : AE D) (M : WO S T), IsHalf e M → ∀ (k : ℕ), 0 < k → ∃ N₀ : ℕ, ∀ (w : GA D S) (w' : GA D T), w ∈ GfC S → w' ∈ GfC T → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin a), Valued.v (adAt D.host.F P (finM S ha w r s - (1 : Matrix (Fin a) (Fin a) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin b), Valued.v (adAt D.host.F P (finM T hb w' r s - (1 : Matrix (Fin b) (Fin b) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → ∃ t : WO S T, t ∈ stdHom S T ∧ IsHalf e t ∧ actO S T w⁻¹ w'⁻¹ M = M + k • t := by
  first | exact @GlobalTheory.AdForm.DeepMove.actO_deep | exact GlobalTheory.AdForm.DeepMove.actO_deep | (intros; apply GlobalTheory.AdForm.DeepMove.actO_deep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelExistsAdelicLevelTrivialRealLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelExistsAdelicLevelTrivialRealLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.LevLift

theorem exists_mem_U_finM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (z : (A.K i hi β).lev.U), ∃ w : A.U i β, z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) w.1 := by
  intro B X I _ _ l Z u a Ch A hA i hi β z
  letI := tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
    (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso (I.rec7 l Z) ((I.rec7 l Z).sp.X i) _ (rankN (I.rec7 l Z) i hi)
  obtain ⟨g, hg⟩ := e.toMulEquiv.surjective ⟨z.1, (((A.K i hi β).lev.U_eq z.1).1 z.2).1⟩
  have hfin : z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 := by
    rw [← he g]
    have h2 : (e g : GL _ _) = z.1 := congrArg Subtype.val hg
    rw [h2]
  exact ⟨⟨g.1, (hA.U i hi β g.1).2 ⟨g.2, z, hfin⟩⟩, hfin⟩

end GlobalTheory.AdForm.LevLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelExistsAdelicLevelTrivialRealLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevel_exists_adelicLevel_trivialReal_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (z : (A.K i hi β).lev.U), ∃ w : A.U i β, z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) w.1 := by
  first | exact @GlobalTheory.AdForm.LevLift.exists_mem_U_finM | exact GlobalTheory.AdForm.LevLift.exists_mem_U_finM | (intros; apply GlobalTheory.AdForm.LevLift.exists_mem_U_finM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistRationalLevelElementsSameCharacters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatApprox

theorem mt_mul' {D : D7} (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem actO_actO' {D : D7} (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem isHalf_actO' {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

end GlobalTheory.AdForm.RatApprox

namespace GlobalTheory.AdForm.RatApprox


set_option maxHeartbeats 2000000 in
theorem approx : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ k hk κ κ' x y hx hy z
  have hi' : i ≤ B.R.m := Nat.le_of_succ_le hi
  obtain ⟨NB, hNB⟩ := GlobalTheory.T.heckeCharacter_eq_at_det_roots_of_congruent (I.rec7 l Z) (A.chr (i + 1)) (hA.chr ⟨i, hi⟩).1
  have hee : A.e * A.e = A.e := GlobalTheory.PlaceDatum.idemSum_mul_self hA.idem
  have hez : IsHalf A.e (z.map fun r => A.e * incA (I.rec7 l Z) r) := fun r s => by
    simp only [Matrix.map_apply, ← mul_assoc, hee]
  have hM := isHalf_actO' κ.1⁻¹ κ'.1⁻¹ hez
  obtain ⟨NC, hNC⟩ := GlobalTheory.T.halfMatrix_move_deepCongruence_bound (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) i hi') (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hM k hk
  have hfin : ∀ j (hj : j ≤ B.R.m) (β : Ch j), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (A.K j hj β).lev := fun j hj β => by
    obtain ⟨n, hn, h⟩ := hA.fin j hj β
    exact ⟨n, hn, fun κ _ => h κ⟩
  have step : ∀ j (hj : j ≤ B.R.m) (β : Ch j) (g : A.U j β), ∃ w : A.U j β, A.chi j β w = 1 ∧
      (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) j hj) (g * w).1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧
      ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin (B.R.N j)), Valued.v (adAt (I.rec7 l Z).host.F P (finM _ (rankN (I.rec7 l Z) j hj) w.1 r s - (1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ)) := by
    intro j hj β g
    obtain ⟨g₀, hg₀⟩ := ((hA.U j hj β g.1).1 g.2).2
    obtain ⟨zz, hz1, hz2, hz3⟩ := GlobalTheory.T.exists_trivialCharLevel_elt_rational_at_twistPrimes I hI hP l Z a _ j hj _ (A.K j hj β).lev (hfin j hj β) (max NB NC) (show TC.GA B (B.R.N j) from g₀.1)
    obtain ⟨w, hw⟩ := GlobalTheory.T.chartLevel_exists_adelicLevel_trivialReal_lift I hI hP l Z u a Ch A hA j hj β zz
    refine ⟨w, ?_, fun P hPQ => ?_, fun P r s => ?_⟩
    · rw [hA.chi j hj β w zz hw, hz1]
    · obtain ⟨M, hM⟩ := hz2 P hPQ
      refine ⟨M, fun r s => ?_⟩
      rw [← hM r s, Subgroup.coe_mul, GlobalTheory.RepLattice.finM_mul', ← hg₀, ← hw]
      rfl
    · rw [← hw]
      exact hz3 P r s
  obtain ⟨w, hw1, hw2, hw3⟩ := step i hi' α κ
  obtain ⟨w', hw1', hw2', hw3'⟩ := step (i + 1) hi γ κ'
  have hwG : w.1 ∈ GfC _ := ((hA.U i hi' α w.1).1 w.2).1
  have hwG' : w'.1 ∈ GfC _ := ((hA.U (i + 1) hi γ w'.1).1 w'.2).1
  have dB : ∀ {n : ℕ} (f : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))), (∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ))) → ∀ N₀ : ℕ, N₀ ≤ max NB NC → ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-(N₀ : ℤ)) := by
    intro n f hf N₀ hN P r s
    exact (hf P r s).trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hN)))
  obtain ⟨x₁, hx₁, hcx⟩ := hNB _ (rankN (I.rec7 l Z) i hi') κ.1 w.1 hwG (dB _ hw3 NB (le_max_left _ _)) x hx
  obtain ⟨y₁, hy₁, hcy⟩ := hNB _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 w'.1 hwG' (dB _ hw3' NB (le_max_left _ _)) y hy
  obtain ⟨t, ht, hth, hte⟩ := hNC w.1 w'.1 hwG hwG' (dB _ hw3 NC (le_max_right _ _)) (dB _ hw3' NC (le_max_right _ _))
  refine ⟨κ * w, κ' * w', x₁, y₁, t, hw2, hw2', hx₁, hy₁, hcx, hcy, ?_, ?_, ht, hth, ?_⟩
  · rw [map_mul, hw1, mul_one]
  · rw [map_mul, hw1', mul_one]
  · rw [← hte, actO_actO']
    simp only [Subgroup.coe_mul, _root_.mul_inv_rev]

end GlobalTheory.AdForm.RatApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistRationalLevelElementsSameCharactersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistRational_levelElements_same_characters : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  first | exact @GlobalTheory.AdForm.RatApprox.approx | exact GlobalTheory.AdForm.RatApprox.approx | (intros; apply GlobalTheory.AdForm.RatApprox.approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawUnderTwoLevelsModHalfLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.XiLaw

theorem isHalf_add {D : D7} {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := by
  intro r s
  simp only [Matrix.add_apply, mul_add, hu r s, hv r s]

theorem xi_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ κ' x y hx hy z z' v hv hvh hrel
  obtain ⟨κ₁, κ₁', x₁, y₁, t, r1, r1', hx1, hy1, ex, ey, ec, ec', ht, hth, hact⟩ :=
    GlobalTheory.T.exists_twistRational_levelElements_same_characters I hI hP l Z u a Ch A hA i hi α γ k hk κ κ' x y hx hy z
  have key := GlobalTheory.T.finiteDatum_basePoints_law_rational_twistPrimes I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ₁ κ₁' r1 r1' x₁ y₁ hx1 hy1 z z' (v + t)
    (add_mem hv ht) (isHalf_add hvh hth) (by rw [hact, hrel, nsmul_add, add_assoc])
  rw [ex, ey, ec, ec'] at key
  exact key

end GlobalTheory.AdForm.XiLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawUnderTwoLevelsModHalfLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_law_under_two_levels_mod_half_lattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  first | exact @GlobalTheory.AdForm.XiLaw.xi_law | exact GlobalTheory.AdForm.XiLaw.xi_law | (intros; apply GlobalTheory.AdForm.XiLaw.xi_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawRationalPointsHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatLaw

theorem isHalf_actO {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

theorem law_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy z
  obtain ⟨hsupp, k, hk, hper, -⟩ := hΦ
  set ez := z.map fun r => A.e * incA (I.rec7 l Z) r with hez
  by_cases hw : IsHalf A.e (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez)
  · obtain ⟨z', v, hv, hvh, hwe⟩ := GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom _ _ A.e _ hA.idem k hk _ hw
    have hΦw : Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez) = p * A.xi i hi α γ z' := by
      rw [hwe, hper v hv hvh, hp z']
    rw [hΦw, hp z]
    by_cases hp0 : p = 0
    · simp [hp0]
    · have hxi : ∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E)
          (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t →
          z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t →
          A.xi i hi α γ z₁ = A.xi i hi α γ z₂ := by
        intro z₁ z₂ t ht hth he
        have h1 := hp z₁
        rw [he, hper t ht hth, hp z₂] at h1
        exact (mul_left_cancel₀ hp0 h1).symm
      have hL := GlobalTheory.T.finiteDatum_law_under_two_levels_mod_half_lattice I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ κ' x y hx hy z z' v hv hvh hwe
      linear_combination p * hL
  · have h1 : Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez) = 0 := by
      by_contra h
      exact hw (hsupp _ h)
    have h2 : Φ ez = 0 := by
      by_contra h
      exact hw (GlobalTheory.AdForm.RatLaw.isHalf_actO _ _ (hsupp _ h))
    rw [h1, h2]
    simp

end GlobalTheory.AdForm.RatLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawRationalPointsHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatumLaw_rationalPoints_half : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) := by
  first | exact @GlobalTheory.AdForm.RatLaw.law_rat | exact GlobalTheory.AdForm.RatLaw.law_rat | (intros; apply GlobalTheory.AdForm.RatLaw.law_rat <;> assumption)
end
