module

public import Formalism.LocalToGlobal.Columns.ChainTw
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZeroAlt
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.SymLevEnt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.ChainTwL
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwL

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

open Classical

theorem tw_mem_vGs_of_not {P : rowSG Pr sel mu} (hP : P.1 ∉ twQOff (Pr := Pr) sel mu) : P.1 ∈ Pr.vGs := by
  rcases Finset.mem_union.1 P.2 with h | h
  · exact h
  · by_contra hn
    exact hP (Finset.mem_sdiff.2 ⟨h, hn⟩)

theorem tw_mem_QOff {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) : P.1 ∈ twQOff (Pr := Pr) sel mu :=
  Finset.mem_sdiff.2 ⟨(Finset.mem_union.1 P.2).resolve_left hP, hP⟩

theorem twCFin_sub {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} {P : twQOff (Pr := Pr) sel mu}
    {D : Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)} (hD : D ∈ twCFin Ch sel mu cst st P) :
    D ∈ twCSet Ch sel mu cst st P := by
  unfold twCFin at hD
  split_ifs at hD with hf
  · exact (Set.Finite.mem_toFinset hf).1 hD
  · exact absurd hD (Finset.notMem_empty _)

theorem twCFin_mem {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} {P : twQOff (Pr := Pr) sel mu}
    (hf : (twCSet Ch sel mu cst st P).Finite) {D : Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)}
    (hD : D ∈ twCSet Ch sel mu cst st P) : D ∈ twCFin Ch sel mu cst st P := by
  unfold twCFin
  rw [dite_eq_left hf]
  exact (Set.Finite.mem_toFinset hf).2 hD

def TwNormAt {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) : Prop :=
  ∀ (P : twQOff (Pr := Pr) sel mu) D, D ∈ twCSet Ch sel mu cst st P →
    ∃ h, Quotient.mk _ h = D ∧ TwCand Ch sel mu cst st P h ∧ TwNF (Pr := Pr) (i + 1) P.1 h ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1

theorem twRep_spec {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} {P : twQOff (Pr := Pr) sel mu}
    {D : Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)}
    (hD : ∃ h, Quotient.mk _ h = D ∧ TwCand Ch sel mu cst st P h ∧ TwNF (Pr := Pr) (i + 1) P.1 h ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1) :
    Quotient.mk _ (twRep Ch sel mu cst st P D) = D ∧ TwCand Ch sel mu cst st P (twRep Ch sel mu cst st P D) ∧
      TwNF (Pr := Pr) (i + 1) P.1 (twRep Ch sel mu cst st P D) ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 (twRep Ch sel mu cst st P D) ≤ GLint X.E (R.N (i + 1)) P.1 :=
  Classical.epsilon_spec hD

theorem twNext_h_g {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) (b : (twNext Ch sel mu cst st).β)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) : (twNext Ch sel mu cst st).h b P = 1 := by
  dsimp only [twNext]
  rw [dite_eq_right (fun h => (Finset.mem_sdiff.1 h).2 hP)]

theorem twNext_h_Q {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) (b : (twNext Ch sel mu cst st).β)
    (P : twQOff (Pr := Pr) sel mu) :
    (twNext Ch sel mu cst st).h b (twRow P) = twRep Ch sel mu cst st P (b.1 P).1 := by
  dsimp only [twNext]
  rw [dite_eq_left (show (twRow P).1 ∈ twQOff (Pr := Pr) sel mu from P.2)]
  rfl

theorem twNext_spec {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (b : (twNext Ch sel mu cst st).β) (P : twQOff (Pr := Pr) sel mu) :
    Quotient.mk _ ((twNext Ch sel mu cst st).h b (twRow P)) = (b.1 P).1 ∧
      TwCand Ch sel mu cst st P ((twNext Ch sel mu cst st).h b (twRow P)) ∧
      TwNF (Pr := Pr) (i + 1) P.1 ((twNext Ch sel mu cst st).h b (twRow P)) ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h b (twRow P)) ≤ GLint X.E (R.N (i + 1)) P.1 := by
  rw [twNext_h_Q]
  exact twRep_spec (hN P _ (twCFin_sub (b.1 P).2))

theorem twNext_nonvan {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (b : (twNext Ch sel mu cst st).β) (P : rowSG Pr sel mu) :
    ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (st.h al P) ((twNext Ch sel mu cst st).h b P) := by
  by_cases hP : P.1 ∈ twQOff (Pr := Pr) sel mu
  · obtain ⟨-, ⟨-, al, hal⟩, -, -⟩ := twNext_spec hN b ⟨P.1, hP⟩
    exact ⟨al, hal⟩
  · have hG := tw_mem_vGs_of_not hP
    obtain ⟨al, hal⟩ := b.2 P hG
    exact ⟨al, by rw [twNext_h_g st b P hG]; exact hal⟩

theorem twNext_inj {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (b b' : (twNext Ch sel mu cst st).β)
    (H : ∀ P : rowSG Pr sel mu, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h b P) ((twNext Ch sel mu cst st).h b' P)) :
    b = b' := by
  apply Subtype.ext
  funext P
  apply Subtype.ext
  have h1 := (twNext_spec hN b P).1
  have h2 := (twNext_spec hN b' P).1
  rw [← h1, ← h2]
  exact Quotient.sound (H (twRow P))

theorem twNext_surj {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (hfin : ∀ P, (twCSet Ch sel mu cst st P).Finite) (hg1 : ∀ al (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → st.h al P = 1)
    (hSG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1),
      FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h → SameDC (Pr := Pr) cst.sharp (i + 1) P.1 1 h)
    (hNV : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 1)
    (hh : rowSG Pr sel mu → AutY X R (i + 1)) (hs : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → hh P ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1))
    (hb : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwBdd (Pr := Pr) (i + 1) P.1 (hh P))
    (H : ∀ P, ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (st.h al P) (hh P)) :
    ∃ b : (twNext Ch sel mu cst st).β, ∀ P, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h b P) (hh P) := by
  have hmem : ∀ P : twQOff (Pr := Pr) sel mu,
      Quotient.mk (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1) (hh (twRow P)) ∈ twCFin Ch sel mu cst st P := fun P => by
    apply twCFin_mem (hfin P)
    have hc : TwCand Ch sel mu cst st P (hh (twRow P)) := ⟨hb (twRow P) (Finset.mem_sdiff.1 P.2).2, H (twRow P)⟩
    exact ⟨hh (twRow P), rfl, hc⟩
  have hne : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (st.h al P) 1 := fun P hP => by
    obtain ⟨al, -⟩ := H P
    exact ⟨al, by rw [hg1 al P hP]; exact hNV P hP⟩
  let b : (twNext Ch sel mu cst st).β := ⟨fun P => ⟨_, hmem P⟩, hne⟩
  refine ⟨b, fun P => ?_⟩
  by_cases hP : P.1 ∈ twQOff (Pr := Pr) sel mu
  · have h1 := (twNext_spec hN b ⟨P.1, hP⟩).1
    exact Quotient.exact h1
  · have hG := tw_mem_vGs_of_not hP
    rw [twNext_h_g st b P hG]
    obtain ⟨al, hal⟩ := H P
    rw [hg1 al P hG] at hal
    exact hSG P hG (hh P) (hs P hG) hal

variable (Ch sel mu cst)

theorem twSt_succ_le {m2 i : ℕ} (h : i + 1 ≤ m2) : twSt Ch sel mu cst m2 (i + 1) = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) := by
  rw [twSt, if_pos h]

theorem twSt_last (m2 : ℕ) : twSt Ch sel mu cst m2 (m2 + 1) = twUnitSt _ (m2 + 1) := by
  rw [twSt, if_neg (by omega), if_pos rfl]

theorem twSt_le (m2 : ℕ) : ∀ (j : ℕ) (_b : (twSt Ch sel mu cst m2 j).β), j ≤ m2 + 1
  | 0, _ => Nat.zero_le _
  | i + 1, b => by
      revert b
      by_cases h1 : i + 1 ≤ m2
      · intro _; omega
      · by_cases h2 : i + 1 = m2 + 1
        · intro _; omega
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h1, if_neg h2]]
          intro b; exact b.elim

theorem twSt_h_g (m2 : ℕ) : ∀ (j : ℕ) (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
    (twSt Ch sel mu cst m2 j).h b P = 1
  | 0, _, _, _ => rfl
  | i + 1, b, P, hP => by
      revert b
      by_cases h1 : i + 1 ≤ m2
      · rw [twSt_succ_le Ch sel mu cst h1]
        intro b; exact twNext_h_g _ b P hP
      · by_cases h2 : i + 1 = m2 + 1
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twUnitSt _ (i + 1) by rw [twSt, if_neg h1, if_pos h2]]
          intro _; rfl
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h1, if_neg h2]]
          intro b; exact b.elim

end TwL

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section -- EmbedMatrixBasisVecApplyOfNotFree + OneCosetSharpOfPatClosed + OneCosetSharp + ResidueFieldUnfoldingClaimsHold

section
open PI.OneCosetSharp PI.OneCosetSharp.Loc PI.OneCosetSharp.LocE PI.OneCosetSharp.W

private theorem embedMatrix_basisVec_apply_of_not_free {k : Type} [Field k] {n' c n : ℕ}
    (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (tt : FC n' (c + 1) n c → k) (i : ℕ) (hi : i < c)
    (l : Fin (n + c)) (hf : ¬ IsFree n' n c l.1 (n' + i)) :
    xx1 xj tt (eN k (n' + (c + 1)) (n' + i)) l = if l.1 = n + i then 1 else 0 := by
  have hs : n' + i < n' + (c + 1) := by omega
  have he : eN k (n' + (c + 1)) (n' + i) = Pi.single (⟨n' + i, hs⟩ : Fin (n' + (c + 1))) 1 := by
    funext s
    unfold eN
    by_cases h : (s : ℕ) = n' + i
    · have : s = ⟨n' + i, hs⟩ := Fin.ext h
      subst this
      simp
    · have : s ≠ ⟨n' + i, hs⟩ := fun e => h (by rw [e])
      simp [h, this]
  have key : ∀ (A : Matrix (Fin (n + c)) (Fin (n' + (c + 1))) k) (j : Fin (n' + (c + 1))),
      Matrix.toLin' A (Pi.single j 1) l = A l j := by
    intro A j
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    rfl
  rw [he]
  unfold xx1
  rw [key, Matrix.of_apply,
    dite_eq_right (show ¬ IsFree n' n c l.1 (⟨n' + i, hs⟩ : Fin (n' + (c + 1))).1 from hf),
    dite_eq_right (show ¬ ((⟨n' + i, hs⟩ : Fin (n' + (c + 1))).1 < n') by show ¬ (n' + i < n'); omega)]
  show (if l.1 = n + (n' + i - n') then (1 : k) else 0) = _
  rw [Nat.add_sub_cancel_left]

private theorem nElem_aux : NElem := by
  intro k _ n' c n xj tt
  classical
  have heN : ∀ (N j : ℕ) (hj : j < N), eN k N j = Pi.single (⟨j, hj⟩ : Fin N) 1 := by
    intro N j hj
    funext s
    unfold eN
    by_cases h : (s : ℕ) = j
    · have : s = ⟨j, hj⟩ := Fin.ext h
      subst this
      simp
    · have : s ≠ ⟨j, hj⟩ := fun e => h (by rw [e])
      simp [h, this]
  have hnf : ∀ (l : Fin (n + c)) (i : ℕ), i < c → (i = 0 ∨ n + i ≤ l.1) →
      ¬ IsFree n' n c l.1 (n' + i) := by
    intro l i hi h
    unfold IsFree
    omega
  let M : Matrix (Fin (n + c)) (Fin (n + c)) k := Matrix.of fun l s =>
    if s.1 < n then (if l = s then 1 else 0)
    else xx1 xj tt (eN k (n' + (c + 1)) (n' + (s.1 - n))) l
  have hM_lt : ∀ l s : Fin (n + c), s.1 < n → M l s = if l = s then 1 else 0 := by
    intro l s hs
    simp [M, hs]
  have hM_ge : ∀ (l : Fin (n + c)) (j : ℕ) (hj : j < n + c), ¬ j < n →
      M l ⟨j, hj⟩ = xx1 xj tt (eN k (n' + (c + 1)) (n' + (j - n))) l := by
    intro l j hj hn
    simp [M, hn]
  have hT : ∀ l s : Fin (n + c), s < l → M l s = 0 := by
    intro l s hsl
    have hsl' : s.1 < l.1 := hsl
    by_cases hs : s.1 < n
    · rw [hM_lt l s hs, if_neg (fun h => by rw [h] at hsl'; exact lt_irrefl _ hsl')]
    · have hsc := s.2
      rw [show s = ⟨s.1, s.2⟩ from rfl, hM_ge l s.1 s.2 hs,
        embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) l (hnf l (s.1 - n) (by omega) (Or.inr (by omega))),
        if_neg (by omega)]
  have hD : ∀ s : Fin (n + c), M s s = 1 := by
    intro s
    by_cases hs : s.1 < n
    · rw [hM_lt s s hs, if_pos rfl]
    · have hsc := s.2
      rw [show s = ⟨s.1, s.2⟩ from rfl, hM_ge _ s.1 s.2 hs,
        embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) _ (hnf _ (s.1 - n) (by omega) (Or.inr (by simp; omega))),
        if_pos (by simp; omega)]
  have hUT : M.BlockTriangular id := fun i j hij => hT i j hij
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular hUT]
    simp [hD]
  let hinv : Invertible M := Matrix.invertibleOfIsUnitDet M hdet
  let ν := M.toLinearEquiv' hinv
  have hν : ∀ x, ν x = M.mulVec x := by
    intro x
    show (↑(M.toLinearEquiv' hinv) : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) x = _
    rw [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  have hcol : ∀ (j : ℕ) (hj : j < n + c), M.mulVec (eN k (n + c) j) = fun l => M l ⟨j, hj⟩ := by
    intro j hj
    rw [heN _ j hj, Matrix.mulVec_single_one]
    rfl
  have hνcol : ∀ i, i < c → ν (eN k (n + c) (n + i)) = xx1 xj tt (eN k (n' + (c + 1)) (n' + i)) := by
    intro i hi
    rw [hν, hcol (n + i) (by omega)]
    funext l
    rw [hM_ge l (n + i) (by omega) (by omega), Nat.add_sub_cancel_left]
  have hinX : ∀ (v : Fin n → k) (s : Fin (n + c)), ¬ s.1 < n → inX k n c v s = 0 := by
    intro v s hs
    simp [inX, hs]
  have hzero : ∀ i, ¬ i < c → eN k (n + c) (n + i) = 0 := by
    intro i hi
    funext l
    unfold eN
    split_ifs with h
    · have := l.2
      omega
    · rfl
  refine ⟨ν, mem_flagUnipotent ⟨?_, ?_, ?_⟩, ?_, hνcol⟩
  · intro i v hv
    have hv' : ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → v l = 0 := hv
    show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → (ν v) l = 0
    intro l hl
    have hl' : n + i ≤ l.1 := by simpa using hl
    rw [hν]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s.1 < n + i
    · rw [hT l s (show s.1 < l.1 by omega), zero_mul]
    · rw [hv' s (by simpa using hs), mul_zero]
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [show eN k (n + c) n = 0 from by simpa using hzero 0 (by omega), map_zero]
    · have h0 := hνcol 0 hc
      have e1 : xx1 xj tt (eN k (n' + (c + 1)) (n' + 0)) = eN k (n + c) (n + 0) := by
        funext l
        rw [embedMatrix_basisVec_apply_of_not_free xj tt 0 hc l (hnf l 0 hc (Or.inl rfl))]
        rfl
      exact h0.trans e1
  · intro i
    show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) →
      (ν (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) l = 0
    intro l hl
    have hl' : n + i ≤ l.1 := by simpa using hl
    by_cases hi : i < c
    · rw [hνcol i hi, Pi.sub_apply, embedMatrix_basisVec_apply_of_not_free xj tt i hi l (hnf l i hi (Or.inr hl'))]
      show (if l.1 = n + i then (1 : k) else 0) - (if l.1 = n + i then 1 else 0) = 0
      exact sub_self _
    · rw [hzero i hi, map_zero, sub_zero]
      rfl
  · intro v
    rw [hν]
    funext l
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single l]
    · rw [hD l, one_mul]
    · intro s _ hsl
      by_cases hs : s.1 < n
      · rw [hM_lt l s hs, if_neg (fun h => hsl h.symm), zero_mul]
      · rw [hinX v s hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h

private theorem support_oneCoset_aux : PI.OneCosetSharp.OneCosetSharp := by
  intro k _ _ ψ₀ χ k₀ m t j n' c n hk hm hm4 hj1 hj2 hc ha hb
  exact ⟨claim1_of patClosed kappaZero nElem_aux gaStep k ψ₀ χ k₀ m t j n' c n ⟨hk, hm, hm4, hj1, hj2, hc, ha, hb⟩,
    C2.claim2 k ψ₀ χ k₀ m t j n' c n ⟨hk, hm, hm4, hj1, hj2, hc, ha, hb⟩⟩

end

theorem residueFieldUnfolding_claims_hold : ResidueFieldUnfoldingSupport ∧ ResidueFieldUnfoldingNonzero := by
  refine ⟨?_, ?_⟩
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr h hne
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset_aux k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).1 h hne
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset_aux k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).2

end

section TwOkG

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem twSurjG (σ : X.K →+* ℂ) {m2 : ℕ} (hB : OcbBase Ch sel mu cst m2) {i : ℕ} (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (h : AutY X R (i + 1)) (hs : h ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1)) (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h) :
    SameDC (Pr := Pr) cst.sharp (i + 1) P.1 1 h := by
  obtain ⟨⟨hbar, hred⟩, hiff⟩ := reductionExistsInLatticeStabilizer_holds Ch sel mu cst σ m2 hB i hi P hP h hs
  have hin : ocbInAt R i P.1 hbar :=
    @residueFieldUnfolding_claims_hold.1 (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (resFintype P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1)) (ocbPsiC_ne hB.hCh σ hP) (ocbRanks_step hB.hm hi) hbar ((hiff hbar hred).1 H)
  exact liftFromResidueParabolicProduct_holds Ch sel mu cst m2 hB i hi P hP h hs hbar hred hin

theorem twNonVanG (σ : X.K →+* ℂ) {m2 : ℕ} (hB : OcbBase Ch sel mu cst m2) {i : ℕ} (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 1 := by
  have h := (reductionExistsInLatticeStabilizer_holds Ch sel mu cst σ m2 hB i hi P hP 1 (Subgroup.one_mem _)).2 1 (ocbIsRed_one P.1 (qOf P.1) _ _)
  refine h.2 ?_
  exact (@ocbNe_one (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (resFintype P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
    (cOf R (i + 1)) (R.N (i + 1))).2
    (@residueFieldUnfolding_claims_hold.2 (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (resFintype P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1)) (ocbPsiC_ne hB.hCh σ hP) (ocbRanks_step hB.hm hi))

end TwOkG

section TwLat

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem twInX_mem_std (P : HeightOneSpectrum (𝓞 E)) {n c : ℕ} (x : Sp E n) :
    Loc.inX E n c x ∈ stdAt E (n + c) P ↔ x ∈ stdAt E n P := by
  rw [ciMem_stdAt, ciMem_stdAt]
  constructor
  · intro h l
    have h1 := h (Fin.castAdd c l)
    rwa [ciInX_apply, dite_eq_left (by simp)] at h1
  · intro h l
    rw [ciInX_apply]
    split_ifs with hl
    · exact h _
    · exact ⟨0, 1, one_notMem P, by simp⟩

theorem twPrX_le_Q (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) : Loc.prX (Loc.Cbe (LocE.JQ P q kj n c) 1) ≤ GLint E n P := by
  rintro g ⟨ρ, hr, hg⟩ x
  have hr' : ρ ∈ LocE.JQ P q kj n c := by
    have := hr.2
    simpa [MulAut.conj_apply] using this
  rw [← twInX_mem_std P (c := c) (g x), ← hg]
  exact (hr'.1 _).trans (twInX_mem_std P x)

end TwLat

section TwOk

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

open Classical


variable (X) in
def TwDegOne (P : HeightOneSpectrum (𝓞 X.E)) : Prop := (qOf P).Prime ∧ ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2


variable (X Pr R) in
def TwFinQ (sharp : Bool) : Prop :=
  ∀ (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → TwDegOne X P →
    {D : Quotient (twSetoid (Pr := Pr) (R := R) sharp j P) | ∃ h, Quotient.mk _ h = D ∧ TwBdd (Pr := Pr) j P h}.Finite

def TwNormDC (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwNF (Pr := Pr) i P.1 hal →
    TwBdd (Pr := Pr) (i + 1) P.1 h → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h →
    ∃ h', SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' ∧ TwBdd (Pr := Pr) (i + 1) P.1 h' ∧ TwNF (Pr := Pr) (i + 1) P.1 h' ∧
      prCat (Pr := Pr) cst.sharp (i + 1) P.1 h' ≤ GLint X.E (R.N (i + 1)) P.1 ∧ FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h'

def TwChrQ (m2 : ℕ) : Prop :=
  (∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwNF (Pr := Pr) i P.1 hal →
    TwBdd (Pr := Pr) (i + 1) P.1 h → TwNF (Pr := Pr) (i + 1) P.1 h → prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1 →
      FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → TwChrOk Ch sel mu cst (i + 1) P h) ∧
  ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → TwChrOk Ch sel mu cst (m2 + 1) P 1

def TwZeroQ : Prop :=
  ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → GLint X.E (R.N 0) P.1 ≤ prCat (Pr := Pr) cst.sharp 0 P.1 1 ∧
    ∀ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp 0 P.1) 1, chiInv Ch sel mu cst 0 P 1 r = 1

structure TwCstQ (G : ChGlob X R.m) : Prop where
  psi_add : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ x y : X.E, IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * x) →
    IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * y) →
      twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) (x + y) = twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x * twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) y
  psi_int : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ x : X.E, IntAt P.1 x → twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x = 1
  psi_ne : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) ((qOf P.1 : X.E)⁻¹) ≠ 1
  sq_sq : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → twSqrt P.1 ^ 2 = (qOf P.1 : X.K)
  weil : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ (a : X.E) (b : ℤ), IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * a) →
    IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ (2 * R.m)) →
      G.σ₀ (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) a) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ (2 * R.m))
  xi0 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0

structure TwAnQ (m2 : ℕ) : Prop where
  deep : ∀ A' B', cst.A ≤ A' → cst.B ≤ B' → ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
    ∀ (hal : AutY X R i) (hbe : AutY X R (i + 1)), TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 hbe →
      E1at Ch sel mu { cst with A := A', B := B' } i P hal hbe = E1at Ch sel mu cst i P hal hbe
  psiSupp : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
    ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))), PsiAt Ch sel mu cst m2 P hal x₀ y' ≠ 0 →
      ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i)
  psiInv : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
    ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' z : Sp X.E (R.N (m2 + 1))), (∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ * z i)) →
      PsiAt Ch sel mu cst m2 P hal x₀ (y' + z) = PsiAt Ch sel mu cst m2 P hal x₀ y'
  xiSupp : ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ (hal : AutY X R i) (hbe : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 hbe → ∀ x : HomE X.E (R.N i) (R.N (i + 1)),
      XiAt Ch sel mu cst i P hal hbe x ≠ 0 → ∀ s l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x (Pi.single s 1) l)
  xiInv : ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ (hal : AutY X R i) (hbe : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 hbe → ∀ x z : HomE X.E (R.N i) (R.N (i + 1)),
      (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l)) →
        XiAt Ch sel mu cst i P hal hbe (x + z) = XiAt Ch sel mu cst i P hal hbe x
  psiSuppX : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
    ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))), PsiAt Ch sel mu cst m2 P hal x₀ y' ≠ 0 →
      ∀ s l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x₀ (Pi.single s 1) l)
  psiInvX : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
    ∀ (x₀ z : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
      (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l)) →
        PsiAt Ch sel mu cst m2 P hal (x₀ + z) y' = PsiAt Ch sel mu cst m2 P hal x₀ y'

variable {Ch sel mu cst}

theorem twBdd_one (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : TwBdd (Pr := Pr) (R := R) j P 1 := fun x hx => by
  refine ⟨by simpa using hx, ?_⟩
  have e : ((qOf P : X.E) ^ j) = algebraMap (𝓞 X.E) X.E ((qOf P : 𝓞 X.E) ^ j) := by simp
  rw [e, algebraMap_smul]
  exact Submodule.smul_mem _ _ (by simpa using hx)

theorem twNormAt_of' {m2 : ℕ} (hN : TwNormDC Ch sel mu cst m2) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1) {i : ℕ} (hi : i < m2)
    (hsrc : ∀ (al : (twSt Ch sel mu cst m2 i).β) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
      TwBdd (Pr := Pr) i P.1 ((twSt Ch sel mu cst m2 i).h al P) ∧ TwNF (Pr := Pr) i P.1 ((twSt Ch sel mu cst m2 i).h al P)) :
    TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i) := by
  intro P D hD
  obtain ⟨h, hhD, hb, al, hal⟩ := hD
  have hP := (Finset.mem_sdiff.1 P.2).2
  obtain ⟨h', hs, hb', hnf, hint, hal'⟩ := hN i hi (twRow P) hP (hd (twRow P) hP) _ h (hsrc al (twRow P) hP).1 (hsrc al (twRow P) hP).2 hb hal
  refine ⟨h', ?_, ⟨hb', al, hal'⟩, hnf, hint⟩
  rw [← hhD]
  exact (Quotient.sound hs).symm

theorem twSt_cand {m2 i : ℕ} (hi : i + 1 ≤ m2) (hN : TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i))
    (b : (twSt Ch sel mu cst m2 (i + 1)).β) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) :
    TwBdd (Pr := Pr) (i + 1) P.1 ((twSt Ch sel mu cst m2 (i + 1)).h b P) ∧
      TwNF (Pr := Pr) (i + 1) P.1 ((twSt Ch sel mu cst m2 (i + 1)).h b P) ∧
      (∃ al : (twSt Ch sel mu cst m2 i).β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P ((twSt Ch sel mu cst m2 i).h al P) ((twSt Ch sel mu cst m2 (i + 1)).h b P)) ∧
      prCat (Pr := Pr) cst.sharp (i + 1) P.1 ((twSt Ch sel mu cst m2 (i + 1)).h b P) ≤ GLint X.E (R.N (i + 1)) P.1 := by
  revert b
  rw [twSt_succ_le Ch sel mu cst hi]
  intro b
  obtain ⟨-, ⟨hb, al, hal⟩, hnf, hint⟩ := twNext_spec hN b ⟨P.1, tw_mem_QOff hP⟩
  exact ⟨hb, hnf, ⟨al, hal⟩, hint⟩

theorem twNF_one_zero {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) : TwNF (Pr := Pr) (R := R) 0 P 1 := by
  refine ⟨fun _ => 0, 0, fun _ => ⟨by simp, le_refl _⟩, zero_mem _, fun v => ?_⟩
  have hl : lamYat (Pr := Pr) (R := R) 0 P = LocE.lamY P (qOf P) (R.N 0) (cOf R 0) 0 := by
    unfold lamYat
    rw [if_neg hP]
  rw [inv_one]
  show v ∈ _ ↔ _
  rw [hl]
  unfold LocE.lamY
  rw [ciMem_sclLat]
  constructor
  · intro h
    refine ⟨fun l => ?_, fun i => ?_⟩
    · have h1 := h (Fin.castAdd _ l)
      simp only [Fin.val_castAdd, LocE.scE, if_pos l.2, zpow_zero, inv_one, one_mul] at h1
      simpa using h1
    · have h1 := h (Fin.natAdd _ i)
      simp only [Fin.val_natAdd, LocE.scE] at h1
      simpa using h1
  · rintro ⟨h1, h2⟩ l
    refine Fin.addCases (fun l => ?_) (fun i => ?_) l
    · have := h1 l
      simp only [Fin.val_castAdd, LocE.scE, if_pos l.2, zpow_zero, inv_one, one_mul]
      simpa using this
    · have := h2 i
      simp only [Fin.val_natAdd, LocE.scE]
      simpa using this

theorem twNormAt_all {m2 : ℕ} (hN : TwNormDC Ch sel mu cst m2) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1) :
    ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i)
  | 0, hi => twNormAt_of' hN hd hi fun _ P hP => ⟨twBdd_one 0 P.1, twNF_one_zero hP⟩
  | i + 1, hi => twNormAt_of' hN hd hi fun al P hP =>
      have H := twSt_cand (by omega) (twNormAt_all hN hd i (by omega)) al P hP
      ⟨H.1, H.2.1⟩

theorem twSt_of_twNormAt {m2 : ℕ} (hN : ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i)) :
    ∀ i, i < m2 → ∀ (al : (twSt Ch sel mu cst m2 i).β) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
      TwBdd (Pr := Pr) i P.1 ((twSt Ch sel mu cst m2 i).h al P) ∧ TwNF (Pr := Pr) i P.1 ((twSt Ch sel mu cst m2 i).h al P)
  | 0, _, _, P, hP => ⟨twBdd_one 0 P.1, twNF_one_zero hP⟩
  | i + 1, hi, al, P, hP =>
      have H := twSt_cand (by omega) (hN i (by omega)) al P hP
      ⟨H.1, H.2.1⟩

theorem twSt_bdd {m2 : ℕ} (hN : ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i)) :
    ∀ (j : ℕ) (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
      TwBdd (Pr := Pr) j P.1 ((twSt Ch sel mu cst m2 j).h b P)
  | 0, _, P, _ => twBdd_one 0 P.1
  | i + 1, b, P, hP => by
      by_cases h1 : i + 1 ≤ m2
      · exact (twSt_cand h1 (hN i (by omega)) b P hP).1
      · revert b
        by_cases h2 : i + 1 = m2 + 1
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twUnitSt _ (i + 1) by rw [twSt, if_neg h1, if_pos h2]]
          intro _; exact twBdd_one _ _
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h1, if_neg h2]]
          intro b; exact b.elim

theorem twJat_Q (sharp : Bool) (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    Jat (Pr := Pr) (R := R) sharp j P = LocE.JQ P (qOf P) (R.k + j) (R.N j) (cOf R j) := by
  unfold Jat
  rw [if_neg hP]

theorem twSt_int {m2 : ℕ} (hs : cst.sharp = true) (hN : ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i)) :
    ∀ (j : ℕ) (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu),
      prCat (Pr := Pr) cst.sharp j P.1 ((twSt Ch sel mu cst m2 j).h b P) ≤ GLint X.E (R.N j) P.1 := by
  intro j b P
  by_cases hG : P.1 ∈ Pr.vGs
  · rw [twSt_h_g Ch sel mu cst m2 j b P hG, hs]
    show Loc.prX (Loc.Cbe (Jat (Pr := Pr) true j P.1) 1) ≤ _
    rw [ookJat j hG]
    exact ookPrX_le
  · have h1 : ∀ b' : (twSt Ch sel mu cst m2 j).β, (twSt Ch sel mu cst m2 j).h b' P = 1 →
        prCat (Pr := Pr) cst.sharp j P.1 ((twSt Ch sel mu cst m2 j).h b' P) ≤ GLint X.E (R.N j) P.1 := fun b' e => by
      rw [e]
      show Loc.prX (Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) 1) ≤ _
      rw [twJat_Q _ j hG]
      exact twPrX_le_Q _ _ _ _ _
    cases j with
    | zero => exact h1 b rfl
    | succ i =>
      by_cases h2 : i + 1 ≤ m2
      · exact (twSt_cand h2 (hN i (by omega)) b P hG).2.2.2
      · revert b h1
        by_cases h3 : i + 1 = m2 + 1
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twUnitSt _ (i + 1) by rw [twSt, if_neg h2, if_pos h3]]
          intro b h1; exact h1 b rfl
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h2, if_neg h3]]
          intro b; exact b.elim

end TwOk

end Formalism.L2.Col
