module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DegLiftOf
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLift
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem nice_mono {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k ρ Wp Wq} {ε ε' : ℝ} {F : B.Mat k ρ → (Wq →L[ℂ] Wp)}
    (h : JC.NiceCoef Bs ε F) (hε : ε' ≤ ε) : JC.NiceCoef Bs ε' F :=
  ⟨h.1, h.2.1, fun g hg hne => hε.trans (h.2.2 g hg hne)⟩

theorem poly_coeff_unique {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (A B : Fin n → V)
    (h : ∀ y : ℝ, ∑ l : Fin n, ((y : ℂ) ^ (l : ℕ)) • A l = ∑ l : Fin n, ((y : ℂ) ^ (l : ℕ)) • B l) : A = B := by
  set τ : Fin n → ℂ := fun i => (((i : ℕ) : ℝ) : ℂ) with hτdef
  have hτ : Function.Injective τ := by
    intro a b hab
    simp only [hτdef, Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  have key : ∀ (C : Fin n → V) (l : Fin n),
      C l = ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i • ∑ m : Fin n, (τ i ^ (m : ℕ)) • C m := by
    intro C l
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    simp only [vand_row τ hτ l, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  funext l
  rw [key A l, key B l]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact h ((i : ℕ) : ℝ)

section lift

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem sum_pad {V : Type} [AddCommGroup V] [Module ℂ V] {d n : ℕ} (hdn : d ≤ n) (c : Fin (d + 1) → V) (y : ℂ) :
    ∑ m : Fin (d + 1), (y ^ (m : ℕ)) • c m =
      ∑ l : Fin (n + 1), (y ^ (l : ℕ)) • (if hl : (l : ℕ) ≤ d then c ⟨l, by omega⟩ else 0) := by
  classical
  have e := Finset.sum_map (Finset.univ : Finset (Fin (d + 1))) (Fin.castLEEmb (by omega : d + 1 ≤ n + 1))
    (fun l : Fin (n + 1) => (y ^ (l : ℕ)) • (if hl : (l : ℕ) ≤ d then c ⟨l, by omega⟩ else 0))
  symm
  rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin (d + 1))).map
    (Fin.castLEEmb (by omega : d + 1 ≤ n + 1)))) ?_, e]
  · apply Finset.sum_congr rfl
    intro m _
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    rw [dite_eq_left (by omega)]
  · intro l _ hl
    rw [dite_eq_right, smul_zero]
    intro hle
    apply hl
    rw [Finset.mem_map]
    exact ⟨⟨l, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

theorem reduceJ {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ r)
    (h : C.LPt) (τ : ℂ) (ha : D.ptSize (h ++ [(s, τ)]) = j) (hs : s ≤ j)
    (hSP : SlicePoly T F j hj (h ++ [(s, τ)]) ha) (hLD : LiftDeg T F j s hj h τ ha)
    (w' : List C.Letter) (hN : ∃ ε, ∀ a', JC.NiceCoef (T.bs j) ε (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a'))
    (b : Bool) (δ : ℝ) :
    ∃ E : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp),
      (∀ l, ∃ ε, ∀ a', JC.NiceCoef (T.bs j) ε (E l a')) ∧ (∀ l : Fin (j + 1), j - s < (l : ℕ) → E l = 0) ∧
      E ⟨j - s, by omega⟩ = cLift s τ b • KB.slv T F j hj w' (h ++ [(s, τ)]) ha ∧
      ∀ (y : ℝ) (a' : Wd.Ix (Fin w'.length)), ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z',
        B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
          B.JF (T.bs j) ((∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) a') g := by
  classical
  obtain ⟨C1, -, hC1n, hC1⟩ := hSP w' b δ 1
  obtain ⟨εN, hεN⟩ := hN
  set E : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) := fun l =>
    if (l : ℕ) < j - s then C1 l else if (l : ℕ) = j - s then cLift s τ b • KB.slv T F j hj w' (h ++ [(s, τ)]) ha
    else 0 with hE

  choose εC hεC using hC1n
  set ε0 : ℝ := min εN (Finset.univ.inf' Finset.univ_nonempty εC) with hε0
  have hC1n' : ∀ l a', JC.NiceCoef (T.bs j) ε0 (C1 l a') := fun l a' =>
    nice_mono (hεC l a') ((min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ l)))
  have hNn' : ∀ a', JC.NiceCoef (T.bs j) ε0 (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a') := fun a' =>
    nice_mono (hεN a') (min_le_left _ _)
  have hEn : ∀ l a', JC.NiceCoef (T.bs j) ε0 (E l a') := by
    intro l a'
    simp only [hE]
    split_ifs
    · exact hC1n' l a'
    · exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hNn' a')
    · exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  refine ⟨E, fun l => ⟨ε0, hEn l⟩, fun l hl => ?_, ?_, fun y a' g hg => ?_⟩
  · simp only [hE]; rw [if_neg (by omega), if_neg (by omega)]
  · simp only [hE]; rw [if_neg (by simp), if_pos (by simp)]
  ·
    have hsum : ∀ (y : ℝ) (V : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp)),
        (∀ l, JC.NiceCoef (T.bs j) ε0 (V l a')) →
        B.JF (T.bs j) ((∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l) a') g =
          ∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • B.JF (T.bs j) (V l a') g := by
      intro y V hV
      have e1 : (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l) a' = ∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l a' := by
        simp [Finset.sum_apply]
      rw [e1, Formalism.FourierDecayAlt.P.JCx2.bc_JF_sum Finset.univ (fun l : Fin (j + 1) => ((y : ℂ) ^ (l : ℕ)) • V l a')
        (fun l _ => Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hV l)) hg]
      apply Finset.sum_congr rfl
      intro l _
      exact Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul _ _ _
    have hgGV : g ∈ B.GV k (r - j) := hg.1

    have hL : ∀ y' : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y' + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
        ∑ l : Fin (j + 1), ((y' : ℂ) ^ (l : ℕ)) • B.JF (T.bs j) (C1 l a') g := by
      intro y'
      rw [Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr (T.bs j) (fun g' hg' => hC1 y' a' g' hg') hgGV]
      exact hsum y' C1 (fun l => hC1n' l a')
    obtain ⟨c, hcl, hcy⟩ := hLD w' a' b δ g hg
    have hcomp := poly_coeff_unique (j + 1) (fun l => B.JF (T.bs j) (C1 l a') g)
      (fun l => if hl : (l : ℕ) ≤ j - s then c ⟨l, by omega⟩ else 0) (fun y' => by
        rw [← hL y', hcy y', sum_pad (n := j) (by omega) c (y' : ℂ)])
    rw [hL y, hsum y E (fun l => hEn l a')]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    have hcl' := congrFun hcomp l
    by_cases h1 : (l : ℕ) < j - s
    · simp only [hE, if_pos h1]
    · rw [show B.JF (T.bs j) (C1 l a') g = _ from hcl']
      by_cases h2 : (l : ℕ) = j - s
      · simp only [hE, if_neg h1, if_pos h2]
        rw [dite_eq_left (by omega)]
        have e3 : (⟨(l : ℕ), by omega⟩ : Fin (j - s + 1)) = Fin.last (j - s) := Fin.ext (by simp [h2])
        rw [e3, hcl]
        exact (Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul _ _ _).symm
      · simp only [hE, if_neg h1, if_neg h2]
        rw [dite_eq_right (by omega)]
        exact (Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero g).symm

theorem nice_lincomb {k ρ : ℕ} {Bs : B.RealPlaceData k ρ Wp Wq} {S ι : Type} [Fintype S] [Fintype ι] [Nonempty ι]
    (V : ι → Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) (hV : ∀ l, ∃ ε, ∀ a, JC.NiceCoef Bs ε (V l a)) (c : ι → ℂ) :
    ∃ ε, ∀ a, JC.NiceCoef Bs ε ((∑ l, c l • V l) a) := by
  classical
  choose ε hε using hV
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ε, fun a => ?_⟩
  have e : (∑ l, c l • V l) a = fun g => ∑ l, c l • V l a g := by
    funext g; simp [Finset.sum_apply]
  rw [e]
  exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum Finset.univ (fun l g => c l • V l a g)
    (fun l _ => Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (nice_mono (hε l a) (Finset.inf'_le _ (Finset.mem_univ l))))

end lift

end Formalism.FourierDecayAlt.P.PBG
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGFormJ
open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section betaJ

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_congrJ_left (D : RealPlaceData k r Wp Wq) {F F₂ G : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ JF.Om k r D.z D.z', JF D F g = JF D F₂ g) : beta D F G = beta D F₂ G := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ JF.Om k r D.z D.z' := hq hQ
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F₂ (bigCell k r q.1 (D.μsec q.2))))
    rw [h _ hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

theorem beta_congrJ_right (D : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ JF.Om k r D.z D.z', JF D G g = JF D G₂ g) : beta D F G = beta D F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ JF.Om k r D.z D.z' := hq hQ
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G₂ (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2))))
    rw [h _ hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

end betaJ

section formJ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)

theorem formLev_congrJ_left (x y x' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (hx : ∀ a, JC.NiceCoef (T.bs j) ε (x a)) (hy : ∀ a, JC.NiceCoef (T.bs j) ε (y a))
    (hJ : ∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) :
    D.formLev T s j w x x' = D.formLev T s j w y x' := by
  have hQQ : ∀ Y p q, BcGood (T.bs j) ε (D.QQlev T s j Y p q) := fun Y p q => bcGood_tL s Y p q
  have hR := mn_rrop_closure bcGood_closed (D.QQlev T s j) hQQ (D.positionted w)
  unfold D.formLev
  refine Finset.sum_congr rfl fun a _ => beta_congrJ_left (T.bs j) fun h hh => ?_
  rw [bc_core (D.RRlev T s j w) hR x hx a hh, bc_core (D.RRlev T s j w) hR y hy a hh]
  show (∑ b, D.ap (D.RRlev T s j w a b) (fun g => B.JF (T.bs j) (x b) g)) h =
    (∑ b, D.ap (D.RRlev T s j w a b) (fun g => B.JF (T.bs j) (y b) g)) h
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (hR a b).2.2 _ _ (fun g hg hgG => hJ b g ⟨hgG, hg⟩) h hh.2 hh.1

theorem formLev_congrJ_right (x' x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (hJ : ∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) :
    D.formLev T s j w x' x = D.formLev T s j w x' y := by
  unfold D.formLev
  exact Finset.sum_congr rfl fun a _ => beta_congrJ_right (T.bs j) (hJ a)

theorem pairJ_congrJ_left (ε : ℝ) : ∀ (ys : List ℝ)
    (x y : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (x' : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
    (∀ a, JC.NiceCoef (T.bs j) ε (x a)) → (∀ a, JC.NiceCoef (T.bs j) ε (y a)) →
    (∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) →
    KB.pairJ (D.formLev T s j w) ys x x' = KB.pairJ (D.formLev T s j w) ys y x'
  | [], x, y, x', hx, hy, hJ => formLev_congrJ_left P0 T s j w x y x' ε hx hy hJ
  | _ :: ys, x, y, x', hx, hy, hJ => by
    simp only [KB.pairJ]
    rw [pairJ_congrJ_left ε ys (fun e => x (Fin.cons 1 e)) (fun e => y (Fin.cons 1 e)) _ (fun _ => hx _)
      (fun _ => hy _) (fun _ => hJ _),
      pairJ_congrJ_left ε ys (fun e => x (Fin.cons 0 e)) (fun e => y (Fin.cons 0 e)) _ (fun _ => hx _)
      (fun _ => hy _) (fun _ => hJ _)]

theorem pairJ_congrJ_right : ∀ (ys : List ℝ)
    (x' : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (x y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
    (∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) →
    KB.pairJ (D.formLev T s j w) ys x' x = KB.pairJ (D.formLev T s j w) ys x' y
  | [], x', x, y, hJ => formLev_congrJ_right P0 T s j w x' x y hJ
  | _ :: ys, x', x, y, hJ => by
    simp only [KB.pairJ]
    rw [pairJ_congrJ_right ys _ (fun e => x (Fin.cons 0 e)) (fun e => y (Fin.cons 0 e)) (fun _ => hJ _),
      pairJ_congrJ_right ys _ (fun e => x (Fin.cons 1 e)) (fun e => y (Fin.cons 1 e)) (fun _ => hJ _)]

end formJ

end Formalism.FourierDecayAlt.P.PBG
end
end

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section step

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ P.r)
  (w : List C.Letter) (h h' : C.LPt) (τ τ' : ℂ) (ha : D.ptSize (h ++ [(s, τ)]) = j)
  (ha' : D.ptSize (h' ++ [(s, τ')]) = j)

def Wl (ys : List ℝ) : ℂ :=
  KB.pairJ (p.form j hj w) ys (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha)
    (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha')

theorem wl_step (hs : 1 ≤ s) (hsj : s ≤ j)
    (hSP : SlicePoly p.T F j hj (h ++ [(s, τ)]) ha) (hSP' : SlicePoly p.T F j hj (h' ++ [(s, τ')]) ha')
    (hLD : LiftDeg p.T F j s hj h τ ha) (hLD' : LiftDeg p.T F j s hj h' τ' ha')
    (hN : ∀ w' : List C.Letter, ∃ ε, ∀ a'', JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w' (h ++ [(s, τ)]) ha a''))
    (hN' : ∀ w' : List C.Letter, ∃ ε, ∀ a'', JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w' (h' ++ [(s, τ')]) ha' a''))
    (ys : List ℝ) :
    ∃ c : Fin (2 * (j - s) + s + 1) → ℂ,
      c (Fin.last (2 * (j - s) + s)) = ((-1 : ℂ) ^ (s - 1) * (τ⁻¹ - τ'⁻¹)) * Wl p F j s hj w h h' τ τ' ha ha' ys ∧
      ∀ y : ℝ, Wl p F j s hj w h h' τ τ' ha ha' (y :: ys) = ∑ q : Fin (2 * (j - s) + s + 1), ((y : ℂ) ^ (q : ℕ)) * c q := by
  classical
  set Ξ := p.form j hj w with hΞ
  have hΞ' : Ξ = D.formLev p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w := rfl
  obtain ⟨C0, hC0l, hC0n, hC0⟩ := hSP (KB.plusW ys w) true 0 0
  obtain ⟨D0, hD0l, hD0n, hD0⟩ := hSP' (KB.minusW ys w) false 1 0
  obtain ⟨E, hEn, hE0, hEt, hEJ⟩ := reduceJ p.T F j s hj h τ ha hsj hSP hLD (KB.plusW ys w) (hN _) true 0
  obtain ⟨E', hE'n, hE'0, hE't, hE'J⟩ := reduceJ p.T F j s hj h' τ' ha' hsj hSP' hLD' (KB.minusW ys w) (hN' _) false 1
  have dC0 : ∀ l, DecV (C0 l) := fun l => by obtain ⟨ε, hε⟩ := hC0n l; exact decV_of_nice hε
  have dD0 : ∀ l, DecV (D0 l) := fun l => by obtain ⟨ε, hε⟩ := hD0n l; exact decV_of_nice hε
  have dE : ∀ l, DecV (E l) := fun l => by obtain ⟨ε, hε⟩ := hEn l; exact decV_of_nice hε
  have dE' : ∀ l, DecV (E' l) := fun l => by obtain ⟨ε, hε⟩ := hE'n l; exact decV_of_nice hε
  have zL : ∀ (y' : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV y' →
      KB.pairJ Ξ ys 0 y' = 0 := by
    intro y' hy
    have := pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0 0 y' 1 decV_zero decV_zero hy
    rw [one_smul, add_zero, one_mul, ← hΞ'] at this
    linear_combination -this
  have zR : ∀ (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV x →
      KB.pairJ Ξ ys x 0 = 0 := by
    intro x hx
    have := pairJ_sesq_right P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys x 0 0 1 hx decV_zero decV_zero
    rw [one_smul, add_zero, map_one, one_mul, ← hΞ'] at this
    linear_combination -this

  have hX : ∀ y : ℝ, Wl p F j s hj w h h' τ τ' ha ha' (y :: ys) =
      ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) * ((y : ℂ) ^ (m : ℕ)) *
        (KB.pairJ Ξ ys (E l) (D0 m) - KB.pairJ Ξ ys (C0 l) (E' m)) := by
    intro y
    show KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 1 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 0 e)) -
      KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 0 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 1 e)) = _
    have hy0 : ((true, y) : C.Letter) = (true, y + 0) := by rw [add_zero]

    obtain ⟨εa, hεa⟩ := hN ((true, y) :: KB.plusW ys w)
    obtain ⟨εb, hεb⟩ := nice_lincomb (Bs := p.T.bs j) E hEn (fun l : Fin (j + 1) => (y : ℂ) ^ (l : ℕ))
    have t1 : KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 1 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 0 e)) =
        KB.pairJ Ξ ys (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) (∑ m : Fin (j + 1), ((y : ℂ) ^ (m : ℕ)) • D0 m) := by
      rw [hΞ', pairJ_congrJ_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w (min εa εb) ys _
        (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) _
        (fun a => nice_mono (hεa _) (min_le_left _ _)) (fun a => nice_mono (hεb a) (min_le_right _ _))
        (fun a g hg => by have := hEJ y a g hg; rwa [add_zero] at this)]
      exact pairJ_formLev_congrGV p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ (eqGV_refl _) (hD0 y)
    have t2 : KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 0 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 1 e)) =
        KB.pairJ Ξ ys (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • C0 l) (∑ m : Fin (j + 1), ((y : ℂ) ^ (m : ℕ)) • E' m) := by
      rw [hΞ', pairJ_congrJ_right P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _
        (∑ m : Fin (j + 1), ((y : ℂ) ^ (m : ℕ)) • E' m) (fun a g hg => hE'J y a g hg)]
      have h0 := hC0 y
      rw [add_zero] at h0
      exact pairJ_formLev_congrGV p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ h0 (eqGV_refl _)
    rw [t1, t2, hΞ', pairJ_sum_sum P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ E D0 dE dD0,
      pairJ_sum_sum P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ C0 E' dC0 dE', ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [conj_tpow]
    ring
  set N := 2 * (j - s) + s with hNdef
  have hNj : N = 2 * j - s := by omega
  set P1 : Fin (j + 1) → Fin (j + 1) → ℂ := fun l m => KB.pairJ Ξ ys (E l) (D0 m) with hP1
  set P2 : Fin (j + 1) → Fin (j + 1) → ℂ := fun l m => KB.pairJ Ξ ys (C0 l) (E' m) with hP2
  have P1z : ∀ l m : Fin (j + 1), j - s < (l : ℕ) → P1 l m = 0 := by
    intro l m hl; simp only [hP1]; rw [hE0 l hl]; exact zL _ (dD0 m)
  have P2z : ∀ l m : Fin (j + 1), j - s < (m : ℕ) → P2 l m = 0 := by
    intro l m hm; simp only [hP2]; rw [hE'0 m hm]; exact zR _ (dC0 l)
  have Xz : ∀ l m : Fin (j + 1), N < (l : ℕ) + m → P1 l m - P2 l m = 0 := by
    intro l m hlm
    have := l.isLt; have := m.isLt
    rw [P1z l m (by omega), P2z l m (by omega), sub_zero]
  refine ⟨fun q => ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if (l : ℕ) + m = q then P1 l m - P2 l m else 0, ?_,
    fun y => ?_⟩
  · dsimp only
    simp only [Fin.val_last]
    have hsplit : ∀ l m : Fin (j + 1), (if (l : ℕ) + m = N then P1 l m - P2 l m else 0) =
        (if (l : ℕ) + m = N then P1 l m else 0) - (if (l : ℕ) + m = N then P2 l m else 0) := by
      intro l m; split_ifs <;> simp
    simp only [hsplit, Finset.sum_sub_distrib]
    have hA : (∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if (l : ℕ) + m = N then P1 l m else 0) =
        P1 ⟨j - s, by omega⟩ (Fin.last j) := by
      rw [Finset.sum_eq_single ⟨j - s, by omega⟩]
      · rw [Finset.sum_eq_single (Fin.last j)]
        · rw [if_pos (by simp; omega)]
        · intro m _ hm
          have := m.isLt
          have hm' : (m : ℕ) ≠ j := fun e => hm (Fin.ext (by simp [e]))
          rw [if_neg (by simp; omega)]
        · simp
      · intro l _ hl
        apply Finset.sum_eq_zero
        intro m _
        split_ifs with hlm
        · have := l.isLt; have := m.isLt
          have hl' : (l : ℕ) ≠ j - s := fun e => hl (Fin.ext (by simp [e]))
          exact P1z l m (by omega)
        · rfl
      · simp
    have hB : (∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if (l : ℕ) + m = N then P2 l m else 0) =
        P2 (Fin.last j) ⟨j - s, by omega⟩ := by
      rw [Finset.sum_eq_single (Fin.last j)]
      · rw [Finset.sum_eq_single ⟨j - s, by omega⟩]
        · rw [if_pos (by simp; omega)]
        · intro m _ hm
          have := m.isLt
          have hm' : (m : ℕ) ≠ j - s := fun e => hm (Fin.ext (by simp [e]))
          rw [if_neg (by simp; omega)]
        · simp
      · intro l _ hl
        apply Finset.sum_eq_zero
        intro m _
        split_ifs with hlm
        · have := l.isLt; have := m.isLt
          have hl' : (l : ℕ) ≠ j := fun e => hl (Fin.ext (by simp [e]))
          exact P2z l m (by omega)
        · rfl
      · simp
    rw [hA, hB]
    have dXP : DecV (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha) := by
      obtain ⟨ε, hε⟩ := hN (KB.plusW ys w); exact decV_of_nice hε
    have dXM : DecV (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha') := by
      obtain ⟨ε, hε⟩ := hN' (KB.minusW ys w); exact decV_of_nice hε
    have e1 : P1 ⟨j - s, by omega⟩ (Fin.last j) = cLift s τ true * Wl p F j s hj w h h' τ τ' ha ha' ys := by
      simp only [hP1]
      rw [hEt, hD0l, if_pos rfl]
      have := pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0
        (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha)
        (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha') (cLift s τ true) decV_zero dXP dXM
      rw [zero_add, ← hΞ', zL _ dXM, zero_add] at this
      rw [this]; rfl
    have e2 : P2 (Fin.last j) ⟨j - s, by omega⟩ = conj (cLift s τ' false) * Wl p F j s hj w h h' τ τ' ha ha' ys := by
      simp only [hP2]
      rw [hE't, hC0l, if_pos rfl]
      have := pairJ_sesq_right P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys
        (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha) 0
        (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha') (cLift s τ' false) dXP decV_zero dXM
      rw [zero_add, ← hΞ', zR _ dXP, zero_add] at this
      rw [this]; rfl
    rw [e1, e2]
    simp only [cLift, if_true, Bool.false_eq_true, if_false, map_mul, map_pow, map_neg, map_one, map_inv₀,
      Complex.conj_conj]
    ring
  · rw [hX y]
    have key : ∀ l m : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) * ((y : ℂ) ^ (m : ℕ)) *
        (KB.pairJ Ξ ys (E l) (D0 m) - KB.pairJ Ξ ys (C0 l) (E' m)) =
        ∑ q : Fin (2 * (j - s) + s + 1), ((y : ℂ) ^ (q : ℕ)) * (if (l : ℕ) + m = q then P1 l m - P2 l m else 0) := by
      intro l m
      by_cases hlm : (l : ℕ) + m ≤ N
      · rw [Finset.sum_eq_single ⟨(l : ℕ) + m, by omega⟩]
        · rw [if_pos rfl, pow_add]
        · intro q _ hq
          rw [if_neg, mul_zero]
          intro e
          exact hq (Fin.ext e.symm)
        · simp
      · have hz := Xz l m (by omega)
        simp only [hP1, hP2] at hz
        rw [hz, mul_zero]
        symm
        apply Finset.sum_eq_zero
        intro q _
        rw [if_neg, mul_zero]
        have := q.isLt
        omega
    simp only [key]
    refine (Finset.sum_congr rfl (fun l _ => Finset.sum_comm)).trans ?_
    refine Finset.sum_comm.trans ?_
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]

end step

section final

theorem degLift_of (hL : LiftDegAll) : KB.DegLift := by
  intro Wp Wq _ _ _ _ _ _ P p F j s hj w h h' t t' ha ha' K grid hF hgrid
  have hsz : D.ptSize (h ++ [(s, t)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s t
  have hs1 : 1 ≤ s := (ha.1 (s, t) (by simp)).1
  have hsj : s ≤ j := by rw [← ha.2, hsz]; omega
  have hN : ∀ (q : C.LPt) (hq : D.IsLocPt q j) (w' : List C.Letter), ∃ ε, ∀ a'',
      JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w' q hq.2 a'') := fun q hq w' =>
    nice_vec_of_cpt (p.T.bs j) (fun a'' => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w' q hq hF a'')
  set W : ℕ → (Fin K → ℝ) → ℂ := fun m y => Wl p F j s hj w h h' t t' ha.2 ha'.2 (Lst K m y) with hW
  have hPS : F7.PolyStep K (2 * (j - s) + s) (fun _ => (-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) W := by
    intro a y
    obtain ⟨c, hc, hcs⟩ := wl_step p F j s hj w h h' t t' ha.2 ha'.2 hs1 hsj
      (slicePolyAll Wp Wq P p F hF j hj _ ha) (slicePolyAll Wp Wq P p F hF j hj _ ha')
      (hL Wp Wq P p F hF j s hj h t ha) (hL Wp Wq P p F hF j s hj h' t' ha') (hN _ ha) (hN _ ha') (Lst K a y)
    refine ⟨c, ?_, fun u => ?_⟩
    · rw [hc, smul_eq_mul]
    · simp only [hW]
      rw [lst_succ, hcs u]
      simp only [smul_eq_mul]
  have hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i) := fun a => hgrid _
  have hE := Formalism.FourierDecayAlt.P.extract_K_bound ℂ K (2 * (j - s) + s) (fun _ => (-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) W
    (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hE
  have hW0 : W 0 (fun _ => 0) = p.RR F j w (h ++ [(s, t)]) (h' ++ [(s, t')]) := by
    simp only [hW, KB.Pl.RR, D.RRplace, dif_pos (And.intro ha ha'), dif_pos hj]
    rfl
  rw [hW0] at hE
  rw [hE]
  refine Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)
  simp only [hW, smul_eq_mul]
  rw [lst_full]
  have e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) =
      fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (2 * (j - s) + s + 1)))) n b) := by
    funext b
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  have e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) =
      ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (2 * (j - s) + s + 1)))) n a) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  rw [e1, e2]
  rfl

end final

end Formalism.FourierDecayAlt.P.PBG
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothLevOfLoc
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hmat_zb (h : C.LPt) (s : ℕ) (τ : ℂ) (hl : D.IsLocPt (h ++ [(s, τ)]) (D.ptSize (h ++ [(s, τ)])))
    (a' q : ℕ) (ha' : a' < D.ptSize (h ++ [(s, τ)])) (hq : q < D.ptSize (h ++ [(s, τ)])) :
    U.hMat (D.ptPerm (h ++ [(s, τ)])) (D.ptDiag (h ++ [(s, τ)])) ⟨a', ha'⟩ ⟨q, hq⟩ =
      C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a' q := by
  have hP := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hlh := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hl
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hl).1
  have hspech := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlh).1
  have entry : ∀ {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (x y : Fin p),
      U.hMat σ d x y = if σ x = y then d y else 0 := by
    intro p σ d x y
    simp only [U.hMat, Matrix.mul_diagonal, U.wP, Matrix.of_apply]
    split_ifs <;> simp
  rw [entry]
  have hpa : ((D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ : Fin _) : ℕ) =
      if a' < D.ptSize h then D.ptPartner h a' else D.ptSize h + (s - 1 - (a' - D.ptSize h)) := by
    rw [hspec ⟨a', ha'⟩]
    exact Formalism.FourierDecayAlt.P.Dx2.SL.partner_append s τ h a' (by omega)
  have hdq : D.ptDiag (h ++ [(s, τ)]) ⟨q, hq⟩ = if q < D.ptSize h then D.ptScal h q else τ := by
    simp only [D.ptDiag]
    exact Formalism.FourierDecayAlt.P.Dx2.SL.scal_append s τ h q (by omega)
  have heq : (D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ = ⟨q, hq⟩) ↔
      ((D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ : Fin _) : ℕ) = q := by
    constructor
    · intro e; rw [e]
    · intro e; exact Fin.ext e
  unfold C3.Zb
  by_cases h1 : a' < D.ptSize h
  · rw [dite_eq_left h1]
    have hpart : D.ptPartner h a' < D.ptSize h := by
      rw [← hspech ⟨a', h1⟩]; exact (D.ptPerm h ⟨a', h1⟩).isLt
    by_cases h2 : q < D.ptSize h
    · rw [dite_eq_left h2, entry]
      have heqh : (D.ptPerm h ⟨a', h1⟩ = ⟨q, h2⟩) ↔ D.ptPartner h a' = q := by
        rw [← hspech ⟨a', h1⟩]
        constructor
        · intro e; rw [e]
        · intro e; exact Fin.ext e
      by_cases h3 : D.ptPartner h a' = q
      · rw [if_pos (heq.2 (by rw [hpa, if_pos h1]; exact h3)), if_pos (heqh.2 h3), hdq, if_pos h2]
        rfl
      · rw [if_neg (fun e => h3 (by rw [heq] at e; rw [hpa, if_pos h1] at e; exact e)),
          if_neg (fun e => h3 (heqh.1 e))]
    · rw [dite_eq_right h2, if_neg]
      intro e
      rw [heq, hpa, if_pos h1] at e
      omega
  · rw [dite_eq_right h1]
    by_cases h3 : D.ptSize h ≤ q ∧ a' < D.ptSize h + s ∧ q < D.ptSize h + s ∧
        (a' - D.ptSize h) + (q - D.ptSize h) + 1 = s
    · rw [if_pos h3, if_pos (heq.2 (by rw [hpa, if_neg h1]; omega)), hdq, if_neg (by omega)]
    · rw [if_neg h3, if_neg]
      intro e
      rw [heq, hpa, if_neg h1] at e
      apply h3
      omega

theorem one_mem_Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ Sset k r z := by
  simp only [Sset, Set.mem_setOf_eq]
  refine ⟨1, ?_, 1, ?_, (Matrix.mul_one 1).symm⟩
  · simp [Formalism.QuantumDeterminants.UWset, Formalism.QuantumDeterminants.UH]
  · simp [Formalism.QuantumDeterminants.Nset, Formalism.QuantumDeterminants.UH, Matrix.one_apply]

theorem vLet_left {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) (K : B.Mat k r → E)
    (s g : B.Mat k r) (hs : s ∈ Sset k r z) (hg : g ∈ B.GV k r) :
    D.vLet k r z z' j hj l e K (s * g) = D.vLet k r z z' j hj l e (fun x => K (s * x)) g := by
  have hD : Dmin k r z z' (s * g) ⟨j, by omega⟩ = Dmin k r z z' g ⟨j, by omega⟩ := by
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' s hs 1 (one_mem_Sset k r z') g ⟨j, by omega⟩
    rwa [Matrix.mul_one] at this
  have hA := AAInvW.left_aa E k r z (j - e) (by omega) ((l.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2)
    ((l.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) K s g hs hg
  unfold D.vLet
  rw [hD, hA.1.symm, hA.2.symm]

theorem loc_left {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {K : B.Mat k r → E}
    {s x : B.Mat k r} (hs : s ∈ B.GV k r) (h : CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K (s * x)) :
    CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (fun y => K (s * y)) x := by
  obtain ⟨U, f', hU, hsxU, hf', he⟩ := h
  have hc : Continuous (fun y : B.Mat k r => s * y) := continuous_const.mul continuous_id
  refine ⟨(fun y => s * y) ⁻¹' U, fun y => f' (s * y), hU.preimage hc, hsxU, ?_, fun y hy hyG => ?_⟩
  · let L : B.Mat k r →ₗ[ℝ] B.Mat k r :=
      { toFun := fun y => s * y, map_add' := fun a b => Matrix.mul_add s a b,
        map_smul' := fun c y => Matrix.mul_smul s c y }
    have hl : ContDiff ℝ (⊤ : ℕ∞) (fun y : B.Mat k r => s * y) := (LinearMap.toContinuousLinearMap L).contDiff
    exact hf'.comp hl.contDiffOn (fun y hy => hy)
  · exact he _ hy (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hs hyG)

theorem smoothLev_of_loc {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {K : B.Mat k r → E}
    {D : Set (Q.Mx k r)} (h : ∀ x ∈ Q.Glev k r 0 ∩ D, CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K x) : Q.SmoothLev k r 0 D K := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  exact ⟨U, f', hU, hgU, by exact_mod_cast hf', fun g hg hgl => he g hg hgl.1⟩

end Formalism.FourierDecayAlt.P.PBG
end
end

open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem first_derivative_at_normal_set {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') (i0 s : ℕ) (hs : 1 ≤ s) (hj : i0 + s ≤ r)
    (hh : Matrix (Fin i0) (Fin i0) ℂ) (τ : ℂ) (hdet : hh.det ≠ 0) (hτ : τ ≠ 0) (x₁ : B.Mat k r)
    (hx₁G : x₁ ∈ B.GV k r) (hD₁ : Dmin k r z z' x₁ ⟨i0 + s, by omega⟩ ≠ 0)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi0 x₁ a p = if p.val < i0 + s then C3.Zb i0 s hh τ a.val p.val else 0)
    (hnfy : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      y0 x₁ a p = if r + k < p.val ∧ 2 * r + k - p.val < i0 + s then star (C3.Zb i0 s hh τ a.val (2 * r + k - p.val))
        else 0)
    (K : B.Mat k r → E) (hK : ∀ y ∈ B.GV k r, Dmin k r z z' y ⟨i0 + s, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K y)
    (hR : ∀ y (p q : Fin (2 * r + k + 1)), C3.InNp k r p q → EabH (Hpk k r) p q K y = C3.dpsiP k r z' p q • K y)
    (sx : B.Mat k r) (hsx : sx ∈ Sset k r z) (b : Bool) (Y : ℝ) :
    D.vLet k r z z' (i0 + s) hj (b, Y) 1 K (sx * x₁) =
      cLift s τ b • D.vLet k r z z' i0 (by omega) (b, Y) 0 K (sx * x₁) := by
  rw [vLet_left z z' hz hz' _ _ _ _ K sx x₁ hsx hx₁G, vLet_left z z' hz hz' _ _ _ _ K sx x₁ hsx hx₁G]
  have hsG : sx ∈ B.GV k r := Formalism.QuantumDeterminants.Sset_UH hsx
  set Dset : Set (Q.Mx k r) := {y | Dmin k r z z' y ⟨i0 + s, by omega⟩ ≠ 0} with hDset
  have hDo : IsOpen Dset := isOpen_ne_fun ((contDiff_Dmin z z' _).continuous) continuous_const
  have hx₁ : x₁ ∈ Q.Glev k r 0 ∩ Dset := ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx₁G, hD₁⟩
  have hDinv : ∀ y, Dmin k r z z' (sx * y) ⟨i0 + s, by omega⟩ = Dmin k r z z' y ⟨i0 + s, by omega⟩ := by
    intro y
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' sx hsx 1 (one_mem_Sset k r z') y ⟨i0 + s, by omega⟩
    rwa [Matrix.mul_one] at this
  have hK' : Q.SmoothLev k r 0 Dset (fun y => K (sx * y)) := by
    apply smoothLev_of_loc
    intro y hy
    refine loc_left hsG (hK _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hsG hy.1.1) ?_)
    rw [hDinv]; exact hy.2
  have hR' : ∀ g ∈ Q.Glev k r 0 ∩ Dset, ∀ p q, C3.InNp k r p q →
      Q.EH k r p q (fun y => K (sx * y)) g = C3.dpsiP k r z' p q • (fun y => K (sx * y)) g := by
    intro g _ p q hpq
    show EabH (Hpk k r) p q (fun y => K (sx * y)) g = _
    rw [AAInvW.ly_Eab_left]
    exact hR _ p q hpq
  cases b
  · have := letter_minus_component_one_eq_smul_component_zero hDo z z' i0 s hs hj hh τ hdet hτ x₁ hx₁ hx₁G hnf hnfy _ hK' hR' Y
    simp only [cLift, Bool.false_eq_true, if_false]
    exact this
  · have := letter_plus_component_one_eq_smul_component_zero hDo z z' i0 s hs hj hh τ hdet hτ x₁ hx₁ hnf _ hK' hR' Y
    simp only [cLift, if_true]
    exact this

theorem vLet_congr_level {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) {j₁ j₂ : ℕ} (hj : j₁ = j₂) (h₁ : j₁ ≤ r) (h₂ : j₂ ≤ r) (l : C.Letter) (e : Fin 2)
    (f : B.Mat k r → E) : D.vLet k r z z' j₁ h₁ l e f = D.vLet k r z z' j₂ h₂ l e f := by subst hj; rfl

theorem dmin_congr {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) {j₁ j₂ : ℕ} (hj : j₁ = j₂)
    (h₁ : j₁ < r + 2) (h₂ : j₂ < r + 2) : Dmin k r z z' g ⟨j₁, h₁⟩ = Dmin k r z z' g ⟨j₂, h₂⟩ := by subst hj; rfl

theorem coeff_recover {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (C : Fin n → V) (l : Fin n) :
    C l = ∑ i : Fin n, (Matrix.vandermonde (fun i : Fin n => (((i : ℕ) : ℝ) : ℂ)))⁻¹ l i •
      ∑ m : Fin n, ((((i : ℕ) : ℝ) : ℂ) ^ (m : ℕ)) • C m := by
  have hτ : Function.Injective (fun i : Fin n => (((i : ℕ) : ℝ) : ℂ)) := by
    intro a b hab
    simp only [Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  simp only [vand_row _ hτ l, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

section core

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem liftDeg_core {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ r)
    (h : C.LPt) (τ : ℂ) (ha : D.IsLocPt (h ++ [(s, τ)]) j)
    (w' : List C.Letter) (a' : Wd.Ix (Fin w'.length)) (b : Bool) (δ : ℝ) (g : B.Mat k (r - j))
    (X : Type) [MeasurableSpace X] (μ : Measure X) (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)))
    (sx : X → B.Mat k r) (x₁ : B.Mat k r) (hsx : ∀ x, sx x ∈ Sset k r T.base.z) (hx₁G : x₁ ∈ B.GV k r)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < D.ptSize h + s →
      xi0 x₁ a p = if p.val < D.ptSize h + s then
        C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a.val p.val else 0)
    (hnfy : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < D.ptSize h + s →
      y0 x₁ a p = if r + k < p.val ∧ 2 * r + k - p.val < D.ptSize h + s then
        star (C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a.val (2 * r + k - p.val)) else 0)
    (PC : (B.Mat k r → (Wq →L[ℂ] Wp)) → Prop)
    (hFub : ∀ H, PC H → Integrable (fun x => ℓ x (Kr T.base H (sx x * x₁))) μ ∧
      B.JF (T.bs j) (D.castF (by simp [ha.2]) (D.sliceAt k r T.base.z T.base.z' H (h ++ [(s, τ)]))) g =
        ∫ x, ℓ x (Kr T.base H (sx x * x₁)) ∂μ)
    (hPW : ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), PC (D.uwG k r T.base.z T.base.z' F j hj w e))
    (hloc : ∀ H, PC H → ∀ y ∈ B.GV k r, Dmin k r T.base.z T.base.z' y ⟨j, by omega⟩ ≠ 0 →
      CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (Kr T.base H) y)
    (hvl : ∀ H, PC H → ∀ y ∈ B.GV k r, Dmin k r T.base.z T.base.z' y ⟨j, by omega⟩ ≠ 0 → ∀ (l : C.Letter) (e : Fin 2),
      Kr T.base (D.vLet k r T.base.z T.base.z' j hj l e H) y = D.vLet k r T.base.z T.base.z' j hj l e (Kr T.base H) y) :
    ∃ c : Fin (j - s + 1) → (Wq →L[ℂ] Wp),
      c (Fin.last (j - s)) = cLift s τ b • B.JF (T.bs j) (KB.slv T F j hj w' (h ++ [(s, τ)]) ha.2 a') g ∧
      ∀ y : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha.2 (Fin.cons 1 a')) g =
        ∑ l : Fin (j - s + 1), ((y : ℂ) ^ (l : ℕ)) • c l := by
  classical
  set z := T.base.z with hzdef
  set z' := T.base.z' with hz'def
  have hz : inWb k r z := T.base.z_mem
  have hz' : inWb k r z' := T.base.z'_mem
  have hsz : D.ptSize (h ++ [(s, τ)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hs1 : 1 ≤ s := (ha.1 (s, τ) (by simp)).1
  have hτ : τ ≠ 0 := (ha.1 (s, τ) (by simp)).2
  have hjeq : j = D.ptSize h + s := by rw [← ha.2, hsz]
  set i0 := D.ptSize h with hi0
  have hloc_h : D.IsLocPt h (D.ptSize h) := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head ⟨ha.1, rfl⟩
  set hh := U.hMat (D.ptPerm h) (D.ptDiag h) with hhdef
  have hdet : hh.det ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _
    (fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hloc_h.1 q q.2)
  have hjr : i0 + s ≤ r := by omega
  have hDl : C3.Dlead i0 s hh τ (i0 + s) ≠ 0 := by
    rw [(Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh τ).2]
    refine mul_ne_zero (mul_ne_zero hdet (pow_ne_zero _ hτ)) ?_
    unfold C3.sgnW; exact pow_ne_zero _ (by norm_num)
  have hD₁ : Dmin k r z z' x₁ ⟨i0 + s, by omega⟩ ≠ 0 := by
    rw [dmin_nf z z' x₁ i0 s hh τ hjr hnf (i0 + s) le_rfl]; exact hDl
  have hDinv : ∀ (y x : B.Mat k r) (hyS : y ∈ Sset k r z) (n : ℕ) (hn : n < r + 2),
      Dmin k r z z' (y * x) ⟨n, hn⟩ = Dmin k r z z' x ⟨n, hn⟩ := by
    intro y x hyS n hn
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' y hyS 1 (one_mem_Sset k r z') x ⟨n, hn⟩
    rwa [Matrix.mul_one] at this
  have hyG : ∀ x, sx x * x₁ ∈ B.GV k r := fun x => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.QuantumDeterminants.Sset_UH (hsx x)) hx₁G
  have hyD : ∀ x, Dmin k r z z' (sx x * x₁) ⟨j, by omega⟩ ≠ 0 := by
    intro x
    rw [hDinv _ _ (hsx x), dmin_congr z z' x₁ hjeq _ (by omega)]
    exact hD₁
  set G := D.uwG k r z z' F j hj w' a' with hGdef
  have hG := hPW w' a'
  set KG := Kr T.base G with hKG

  have key : ∀ (x : X) (Y : ℝ), Kr T.base (D.uwG k r z z' F j hj ((b, Y) :: w') (Fin.cons 1 a')) (sx x * x₁) =
      cLift s τ b • D.vLet k r z z' i0 (by omega) (b, Y) 0 KG (sx x * x₁) := by
    intro x Y
    show Kr T.base (D.vLet k r z z' j hj (b, Y) 1 G) (sx x * x₁) = _
    rw [hvl G hG _ (hyG x) (hyD x), vLet_congr_level z z' hjeq hj hjr]
    refine first_derivative_at_normal_set z z' hz hz' i0 s hs1 hjr hh τ hdet hτ x₁ hx₁G hD₁ hnf hnfy KG (fun y hy hyd => ?_)
      (fun y p q hpq => kr_rule T.base G y p q hpq) (sx x) (hsx x) b Y
    exact hloc G hG y hy (by rw [dmin_congr z z' y hjeq _ (by omega)]; exact hyd)

  have poly : ∀ x : X, ∃ c : Fin (i0 + 1) → (Wq →L[ℂ] Wp), c (Fin.last i0) = KG (sx x * x₁) ∧
      ∀ Y : ℝ, D.vLet k r z z' i0 (by omega) (b, Y + δ) 0 KG (sx x * x₁) = ∑ l : Fin (i0 + 1), ((Y : ℂ) ^ (l : ℕ)) • c l := by
    intro x
    have hDi : Dmin k r z z' (sx x * x₁) ⟨i0, by omega⟩ ≠ 0 := by
      rw [hDinv _ _ (hsx x), dmin_nf z z' x₁ i0 s hh τ hjr hnf i0 (by omega),
        (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh τ).1]
      exact hdet
    obtain ⟨c₀, hc₀l, hc₀⟩ := vLet_poly (E := Wq →L[ℂ] Wp) (j := i0) (by omega) z z' KG (sx x * x₁) (hyG x) hDi
      (hloc G hG _ (hyG x) (hyD x)) b 0
    obtain ⟨c', hc'l, hsh⟩ := poly_shift i0 c₀ (δ : ℂ)
    refine ⟨c', by rw [hc'l, hc₀l, if_pos rfl], fun Y => ?_⟩
    rw [hc₀ (Y + δ), ← hsh (Y : ℂ)]
    push_cast
    rfl
  choose cf hcfl hcfY using poly
  have hcL : cLift s τ b ≠ 0 := by
    unfold cLift
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    cases b
    · simp only [Bool.false_eq_true, if_false]; exact inv_ne_zero ((map_ne_zero _).2 hτ)
    · simp only [if_true]; exact inv_ne_zero hτ

  have hnode : ∀ (x : X) (Y : ℝ), D.vLet k r z z' i0 (by omega) (b, Y) 0 KG (sx x * x₁) =
      (cLift s τ b)⁻¹ • Kr T.base (D.uwG k r z z' F j hj ((b, Y) :: w') (Fin.cons 1 a')) (sx x * x₁) := by
    intro x Y
    rw [key x Y, smul_smul, inv_mul_cancel₀ hcL, one_smul]
  set Vi := (Matrix.vandermonde (fun i : Fin (i0 + 1) => (((i : ℕ) : ℝ) : ℂ)))⁻¹ with hVi
  have hdl : ∀ (x : X) (l : Fin (i0 + 1)), ℓ x (cf x l) = ∑ i : Fin (i0 + 1), (Vi l i * (cLift s τ b)⁻¹) •
      ℓ x (Kr T.base (D.uwG k r z z' F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') (Fin.cons 1 a')) (sx x * x₁)) := by
    intro x l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_recover (i0 + 1) (cf x) l, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hcfY x ((i : ℕ) : ℝ), hnode x, map_smul, map_smul, smul_smul]
  have hint : ∀ l : Fin (i0 + 1), Integrable (fun x => ℓ x (cf x l)) μ := by
    intro l
    simp only [hdl]
    exact integrable_finsetSum _ (fun i _ => ((hFub (D.uwG k r z z' F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') (Fin.cons 1 a'))
      (hPW _ _)).1).smul (Vi l i * (cLift s τ b)⁻¹))
  set c' : Fin (i0 + 1) → (Wq →L[ℂ] Wp) := fun l => cLift s τ b • ∫ x, ℓ x (cf x l) ∂μ with hc'
  have hc'top : c' (Fin.last i0) = cLift s τ b • B.JF (T.bs j) (KB.slv T F j hj w' (h ++ [(s, τ)]) ha.2 a') g := by
    simp only [hc', hcfl]
    congr 1
    exact ((hFub G hG).2).symm
  have hc'exp : ∀ y : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha.2 (Fin.cons 1 a')) g =
      ∑ l : Fin (i0 + 1), ((y : ℂ) ^ (l : ℕ)) • c' l := by
    intro y
    have e1 := (hFub _ (hPW ((b, y + δ) :: w') (Fin.cons 1 a'))).2
    show B.JF (T.bs j) (D.castF _ (D.sliceAt k r z z' (D.uwG k r z z' F j hj ((b, y + δ) :: w') (Fin.cons 1 a'))
      (h ++ [(s, τ)]))) g = _
    rw [e1]
    have e2 : ∀ x, ℓ x (Kr T.base (D.uwG k r z z' F j hj ((b, y + δ) :: w') (Fin.cons 1 a')) (sx x * x₁)) =
        ∑ l : Fin (i0 + 1), (((y : ℂ) ^ (l : ℕ)) * cLift s τ b) • ℓ x (cf x l) := by
      intro x
      set_option synthInstance.maxHeartbeats 100000 in
        rw [key x (y + δ), hcfY x y, map_smul, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [map_smul, smul_smul, mul_comm]
    simp only [e2]
    rw [integral_finsetSum Finset.univ (f := fun (l : Fin (i0 + 1)) x => (((y : ℂ) ^ (l : ℕ)) * cLift s τ b) • ℓ x (cf x l))
      (fun l _ => (hint l).smul (((y : ℂ) ^ (l : ℕ)) * cLift s τ b))]
    apply Finset.sum_congr rfl
    intro l _
    rw [integral_smul, hc', smul_smul]
  have hcast : j - s + 1 = i0 + 1 := by omega
  refine ⟨fun l => c' (Fin.cast hcast l), ?_, fun y => ?_⟩
  · have : Fin.cast hcast (Fin.last (j - s)) = Fin.last i0 := Fin.ext (by simp <;> omega)
    simp only [this]
    exact hc'top
  · rw [hc'exp y]
    exact (Fintype.sum_equiv (finCongr hcast) _ _ (fun l => rfl)).symm

end core

end Formalism.FourierDecayAlt.P.PBG
