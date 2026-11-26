module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StepBoxIffStepSuppDeg
section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MovementLaw
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MovementLaw

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def InRangeOf {K : Type} [Field K] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) ∧ ∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x

end Generic


open Classical in
def JetsIn {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (deg : X.Tau → ℤ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K) : Prop :=
  ∀ x, Ξ x ≠ 0 → ∀ m : DVar X.Tau a b →₀ ℕ,
    (∀ τ, ((∑ k ∈ m.support.filter (fun k => k.1 = τ), m k : ℕ) : ℤ) = deg τ) →
    ∃ y : X.K, A.σ₀ y = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m

section Scalar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Scalar

end GlobalTheory.IndefiniteRowSideFullHecke.MovementLaw
end
end

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MoveCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions
open GlobalTheory.IndefiniteRowSideFullHecke

section Clauses

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mulLat_le_divLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (cA cB : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat cB M ≤ divLat cA M := by
  rintro _ ⟨z, hz, rfl⟩
  exact M.smul_mem _ (M.smul_mem _ hz)


open Classical in
theorem inRange_indicator (K : Type) [Field K] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) :
    MovementLaw.InRangeOf S cA cB N N' (fun x => if x ∈ divLat cA (homAt S N N') then (1 : K) else 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_contra h
    exact hx (if_neg h)
  · have hy' := mulLat_le_divLat cA cB _ hy
    have : x + y ∈ divLat cA (homAt S N N') ↔ x ∈ divLat cA (homAt S N N') := Submodule.add_mem_iff_left _ hy'
    simp only [this]

end Clauses


open Classical in
theorem degAt_eq {X : Fields} {a b : ℕ} (m : DVar X.Tau a b →₀ ℕ) (τ : X.Tau) :
    IndexExponentDegree.degAt m τ = ∑ k ∈ m.support.filter (fun k => k.1 = τ), m k := by
  unfold IndexExponentDegree.degAt
  rw [Finset.sum_filter, Finset.sum_subset (Finset.subset_univ m.support) (by
    intro k _ hk
    simp [Finsupp.notMem_support_iff.1 hk]), Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rw [Fintype.sum_prod_type]
    simp
  · intro σ _ hσ
    simp [hσ]
  · simp

theorem nuW_detShift_nonneg {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    0 ≤ (W.nuW u (i + 1) τ).detShift := by
  have hpos : 0 < R.N i := R.N_pos i
  have hlt : R.N i < R.N R.m := by
    unfold Ranks.N
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hi (Nat.succ_pos R.t)) _
  have hb : Examples₂.blkN R (R.N i) = i := by
    unfold Examples₂.blkN Ranks.N
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (Nat.succ_pos _)]
  have h1 : Examples₂.wtN (W.hc u τ) (R.N i) = -wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := by
    unfold Examples₂.wtN
    rw [dite_eq_right (by unfold Ranks.N; omega), dif_pos (by rw [hb]; exact hi)]
    simp only [hb]
  have h2 := Examples₂.wtN_anti (W.hc u τ) (Nat.sub_le (R.N i) 1) hlt
  have h3 := Examples₂.lamOf_eq (W.hc u τ) i hi.le ⟨R.N i - 1, by omega⟩
  rw [Examples₂.wtQ_eq_wtN] at h3
  have h4 : (W.nuW u (i + 1) τ).detShift =
      (Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ + ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    unfold DomWeight.detShift
    rw [dif_pos (show 0 < R.N (i + 1 - 1) from hpos)]
    simp only [Wts.nuW, shiftW, Wts.lamN, RowPar.eAt, RowPar.of, Nat.add_sub_cancel, hi, dif_pos]
    rfl
  rw [h4]
  have h5 : -(Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ ≤ ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    rw [Int.le_floor]
    push_cast
    rw [h3]
    simp only at h2 ⊢
    linarith
  omega

theorem degNu_eq {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    IndexExponentDegree.degNu (W.lamTrue u i) (nuLast W u i) τ = ∑ k, (W.nuW u (i + 1) τ).w k := by
  have hpos : 0 < R.N i := R.N_pos i
  unfold IndexExponentDegree.degNu nuLast
  rw [Int.toNat_of_nonneg (nuW_detShift_nonneg W u hi τ)]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold DomWeight.detShift
  rw [dif_pos (show 0 < R.N (i + 1 - 1) from hpos), dif_pos hpos]
  show ((W.lamN u i τ).w s + _) - ((W.lamN u i τ).w ⟨R.N i - 1, _⟩ + _) + ((W.lamN u i τ).w ⟨R.N i - 1, _⟩ + _) =
    (W.lamN u i τ).w s + _
  ring

section Jets

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)

def JetsAll (deg : X.Tau → ℤ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  ∀ Ξ : HomE X.E a b → X.K, MovementLaw.InRangeOf S cA cB N N' Ξ → MovementLaw.JetsIn A S cB deg N N' Ξ

theorem jetsIn_iff (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ) (deg : X.Tau → ℤ) (h : ∀ τ, IndexExponentDegree.degNu lam n τ = deg τ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    IndexExponentDegree.JetsIn A S cA cB lam n N N' ↔ JetsAll A S cA cB deg N N' := by
  constructor
  · intro hJ Ξ hΞ x hx m hm
    refine hJ x (hΞ.1 x hx) m fun τ => ?_
    rw [degAt_eq, h τ, ← hm τ]
  · intro hJ x hx m hm
    refine hJ _ (inRange_indicator X.K S cA cB N N') x (by simp [hx]) m fun τ => ?_
    rw [← h τ, ← hm τ, degAt_eq]


open Classical in
def JetsDeg (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ) (deg : X.Tau → ℤ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange S M c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, ((∑ k ∈ m.support.filter (fun k => k.1 = τ), m k : ℕ) : ℤ) = deg τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m

theorem jetsAll_of_deg (deg : X.Tau → ℤ) (h : JetsDeg A a b S (cA * cB) deg) (hB : 0 < cB)
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') :
    JetsAll A S cA cB deg N N' := by
  intro Ξ hΞ x hx m hm
  refine h N N' cB x ⟨hN, hN', hB, Dvd.intro_left _ rfl, ?_⟩ m hm
  have h1 : ((cA : ℕ) : 𝓞 X.E) • x ∈ homAt S N N' := hΞ.1 x hx
  show ((cA * cB : ℕ) : 𝓞 X.E) • x ∈ homAt S N N'
  rw [Nat.cast_mul, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ h1

end Jets

theorem cBof_pos {X : Fields} {Pr : Primes X} (hP : Pr.Ok) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) : 0 < cBof sel mu cst u := by
  unfold cBof
  refine Nat.mul_pos (hP.T_prime u).pos (pow_pos (Finset.prod_pos fun P _ => ?_) _)
  exact Nat.pos_of_ne_zero (by unfold Formalism.L2.Col.qOf; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot)

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (A : Amb X) {i : ℕ} {b : ℕ} (lam' : X.Tau → DomWeight b)

end Step

end GlobalTheory.MoveCompare
end
end

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (JetsRatDeg)

section Deg

variable {T : Type} {a b : ℕ}


open Classical in
def monoDeg (e : DVar T a b →₀ ℕ) (τ : T) : ℕ := ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k

theorem monoDeg_eq_sum [Fintype T] (e : DVar T a b →₀ ℕ) (τ : T) : monoDeg e τ = ∑ β, ∑ α, e (τ, β, α) := by
  unfold monoDeg
  rw [Finset.sum_filter, Finset.sum_subset (Finset.subset_univ e.support) (fun k _ hk => by
    simp only [Finsupp.mem_support_iff, not_not] at hk
    simp [hk])]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · simp [Fintype.sum_prod_type]
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ τ) h

theorem exists_monoDeg [Fintype T] (ha : 0 < a) (hb : 0 < b) (n : T → ℕ) : ∃ e : DVar T a b →₀ ℕ, ∀ τ, monoDeg e τ = n τ := by
  classical
  refine ⟨∑ t, Finsupp.single (t, (⟨0, hb⟩ : Fin b), (⟨0, ha⟩ : Fin a)) (n t), fun τ => ?_⟩
  rw [monoDeg_eq_sum, Finset.sum_eq_single (⟨0, hb⟩ : Fin b)]
  · rw [Finset.sum_eq_single (⟨0, ha⟩ : Fin a)]
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · intro α _ hα
      simp [Finsupp.finsetSum_apply, Ne.symm hα]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro β _ hβ
    refine Finset.sum_eq_zero fun α _ => ?_
    simp [Finsupp.finsetSum_apply, Ne.symm hβ]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Deg

namespace ColIn

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

abbrev Sb (a : I.ι) (u : B.Word) : Finset (HeightOneSpectrum (𝓞 B.fields.E)) :=
  Sall (Pr := B.primes X) I.sel (I.tup a) u

abbrev modulus (a : I.ι) (u : B.Word) : ℕ :=
  cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u

end ColIn

abbrev nuDeg (B : Base) (u : B.Word) (i : ℕ) (τ : B.fields.Tau) : ℤ := ∑ r, (B.wts.nuW u (i + 1) τ).w r

theorem nuDeg_nonneg (B : Base) (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau) : 0 ≤ nuDeg B u i τ := by
  have h0 := GlobalTheory.MoveCompare.nuW_detShift_nonneg B.wts u hi τ
  unfold nuDeg
  refine Finset.sum_nonneg fun r _ => le_trans h0 ?_
  unfold DomWeight.detShift
  split_ifs with h
  · apply DomWeight.anti
    rw [Fin.le_iff_val_le_val]
    have := r.isLt
    simp only
    omega
  · exact absurd (lt_of_le_of_lt (Nat.zero_le _) r.isLt) h

theorem exists_monoDeg_nuDeg (B : Base) (u : B.Word) {i : ℕ} (hi : i < B.R.m) :
    ∃ e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ, ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ := by
  have hk := B.R.m_add_three_le_k
  have h1 : 0 < B.R.N i := by
    show 0 < B.R.k + i * (B.R.t + 1)
    omega
  have h2 : 0 < B.R.N (i + 1) := by
    show 0 < B.R.k + (i + 1) * (B.R.t + 1)
    omega
  obtain ⟨e, he⟩ := exists_monoDeg (T := B.fields.Tau) h1 h2 (fun τ => (nuDeg B u i τ).toNat)
  exact ⟨e, fun τ => by rw [he τ]; exact Int.toNat_of_nonneg (nuDeg_nonneg B u hi τ)⟩

private theorem monoDeg_eq_sum_filter {T : Type} {a b : ℕ} {d : DecidableEq T} (e : DVar T a b →₀ ℕ) (τ : T) :
    monoDeg e τ = ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k := by
  unfold monoDeg
  congr

namespace ColIn

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

def jetNum (a : I.ι) (u : B.Word) (i : ℕ) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i)))
    (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))) (c : ℕ) (x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1)))
    (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ) : ℂ :=
  (I.A.chiF _ _ N N')⁻¹ * jetC I.A.cD (I.A.thInd (I.Sb a u) N N' c x) e

abbrev JetRange (a : I.ι) (u : B.Word) (i : ℕ) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i)))
    (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))) (c : ℕ) (x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) : Prop :=
  letI := B.fields.starE
  InRange (I.Sb a u) (I.modulus a u) c N N' x

def JetsIn : Prop :=
  ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m →
    JetsRatDeg I.A (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u)
      (cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u)
      (fun τ => ∑ r, (B.wts.nuW u (i + 1) τ).w r)

theorem jetsIn_iff : I.JetsIn ↔ ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m → ∀ N N' c x,
    I.JetRange a u i N N' c x → ∀ e, (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) →
      I.jetNum a u i N N' c x e ∈ B.embLL.fieldRange := by
  constructor
  · intro h a u i hi N N' c x hx e he
    obtain ⟨y, hy⟩ := h a u i hi N N' c x hx e (fun τ => by rw [← monoDeg_eq_sum_filter]; exact he τ)
    refine RingHom.mem_fieldRange.mpr ⟨y, ?_⟩
    rw [← I.A_σ₀]
    exact hy
  · intro h a u i hi N N' c x hx e he
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp
      (h a u i hi N N' c x hx e (fun τ => by rw [monoDeg_eq_sum_filter]; exact he τ))
    refine ⟨y, ?_⟩
    rw [I.A_σ₀]
    exact hy

variable {I} {a : I.ι} {u : B.Word} {i : ℕ} {N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))}
  {N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))} {c : ℕ} {x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1))}
  {e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ}

theorem JetsIn.exists_eq (h : I.JetsIn) (hi : i < B.R.m) (hx : I.JetRange a u i N N' c x)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) : ∃ y : B.LL, B.embLL y = I.jetNum a u i N N' c x e := by
  exact RingHom.mem_fieldRange.mp ((jetsIn_iff I).mp h a u i hi N N' c x hx e he)

end ColIn

end GlobalTheory.Mem.Col2

end
