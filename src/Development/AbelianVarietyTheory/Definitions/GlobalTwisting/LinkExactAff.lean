module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
noncomputable section

open scoped Matrix

namespace GlobalTheory.SeqCx

def uniM (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Set (List M) :=
  {l | ∃ f : Fin l.length → M →ₗ[R] R, ∀ i j : Fin l.length, f i (l.get j) = if i = j then 1 else 0}

def low (R : Type) [CommRing R] (n : ℕ) : Set (ℕ →₀ R) := {x | ∀ i, n ≤ i → x i = 0}

def aff (R : Type) [CommRing R] (n j : ℕ) : Set (ℕ →₀ R) := {x | x - Finsupp.single j 1 ∈ low R n}

def LinkExactLow (R : Type) [CommRing R] (s n : ℕ) : Prop :=
  ∀ τ ∈ uniM R (ℕ →₀ R), ∀ p : ℕ, p + s + τ.length ≤ n → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R n) τ) p

def LinkExactAff (R : Type) [CommRing R] (s n : ℕ) : Prop :=
  ∀ j : ℕ, n ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), ∀ p : ℕ, p + s + τ.length ≤ n + 1 →
    ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) τ) p

def hbd (V W : Type) : (List V × List W →₀ ℤ) →ₗ[ℤ] (List V × List W →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun z : List V × List W =>
    Finsupp.mapDomain (fun x => (x, z.2)) (bd V (Finsupp.single z.1 1))

def vbd (V W : Type) : (List V × List W →₀ ℤ) →ₗ[ℤ] (List V × List W →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun z : List V × List W =>
    Finsupp.mapDomain (fun w => (z.1, w)) (bd W (Finsupp.single z.2 1))

def chains2 {V W : Type} (D : Set (List V × List W)) (a b : ℕ) : Submodule ℤ (List V × List W →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {z | z ∈ D ∧ z.1.length = a ∧ z.2.length = b}

def SubClosed2 {V W : Type} (D : Set (List V × List W)) : Prop :=
  ∀ z ∈ D, ∀ (x : List V) (w : List W), x.Sublist z.1 → w.Sublist z.2 → (x, w) ∈ D

def splitPairs (R : Type) [CommRing R] (n : ℕ) : Set (List ((Fin n → R) × (Fin n → R)) × List (Fin n → R)) :=
  {z | z.1 ∈ splitSeq R n ∧ z.2 ∈ uniSeq R n ∧ ∀ y ∈ z.1, ∀ u ∈ z.2, y.2 ⬝ᵥ u = 0}

end GlobalTheory.SeqCx

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
noncomputable section

open CategoryTheory GlobalTheory.SeqCx
open scoped Matrix

namespace GlobalTheory.HomStab

variable (R : Type) [CommRing R] (n : ℕ)

def pairAct (g : GL (Fin n) R) (x : (Fin n → R) × (Fin n → R)) : (Fin n → R) × (Fin n → R) :=
  ((g : Matrix (Fin n) (Fin n) R) *ᵥ x.1, x.2 ᵥ* ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))

theorem pairAct_dot (g : GL (Fin n) R) (x y : (Fin n → R) × (Fin n → R)) :
    (pairAct R n g x).2 ⬝ᵥ (pairAct R n g y).1 = x.2 ⬝ᵥ y.1 := by
  simp only [pairAct]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.vecMul_one]

theorem mem_splitSeq_iff (l : List ((Fin n → R) × (Fin n → R))) :
    l ∈ splitSeq R n ↔ ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      l[i].2 ⬝ᵥ l[j].1 = if i = j then 1 else 0 := by
  simp only [GlobalTheory.SeqCx.splitSeq, Set.mem_ofPred_eq]
  constructor
  · intro h i j hi hj
    simpa [Fin.ext_iff] using h ⟨i, hi⟩ ⟨j, hj⟩
  · intro h i j
    simpa [Fin.ext_iff] using h i j i.2 j.2

def SplitSet (p : ℕ) : Type := {l : List ((Fin n → R) × (Fin n → R)) // l ∈ splitSeq R n ∧ l.length = p}

instance (p : ℕ) : MulAction (GL (Fin n) R) (SplitSet R n p) where
  smul g l := ⟨l.1.map (pairAct R n g), (mem_splitSeq_iff R n _).2 fun i j hi hj => by
      simp only [List.getElem_map, pairAct_dot]
      exact (mem_splitSeq_iff R n _).1 l.2.1 i j (by simpa using hi) (by simpa using hj),
    by simpa using l.2.2⟩
  one_smul l := Subtype.ext (by
    change l.1.map (pairAct R n 1) = l.1
    have : pairAct R n 1 = id := by funext x; simp [pairAct]
    simp [this])
  mul_smul g h l := Subtype.ext (by
    change l.1.map (pairAct R n (g * h)) = (l.1.map (pairAct R n h)).map (pairAct R n g)
    rw [List.map_map]
    congr 1
    funext x
    apply Prod.ext
    · simp [pairAct, Matrix.mulVec_mulVec]
    · simp [pairAct, Matrix.vecMul_vecMul])

theorem smul_val {p : ℕ} (g : GL (Fin n) R) (l : SplitSet R n p) : (g • l).1 = l.1.map (pairAct R n g) := rfl

def face (p : ℕ) (i : Fin (p + 1)) (l : SplitSet R n (p + 1)) : SplitSet R n p :=
  ⟨l.1.eraseIdx i, (mem_splitSeq_iff R n _).2 fun a b ha hb => by
      have h := (mem_splitSeq_iff R n _).1 l.2.1
      simp only [List.getElem_eraseIdx]
      split_ifs <;> rw [h] <;> simp <;> omega,
    by have := l.2.2; have := i.2; rw [List.length_eraseIdx, if_pos (by omega)]; omega⟩

theorem face_smul (p : ℕ) (i : Fin (p + 1)) (g : GL (Fin n) R) (l : SplitSet R n (p + 1)) :
    face R n p i (g • l) = g • face R n p i l := by
  apply Subtype.ext
  change ((g • l).1).eraseIdx i = (face R n p i l).1.map (pairAct R n g)
  rw [smul_val, List.eraseIdx_map]
  rfl

abbrev splitRep (p : ℕ) : Rep ℤ (GL (Fin n) R) :=
  perm (k := ℤ) (G := GL (Fin n) R) (SplitSet R n p)

def splitD (p : ℕ) : splitRep R n (p + 1) ⟶ splitRep R n p :=
  ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • permMap (face R n p i) (face_smul R n p i) (Rep.trivial ℤ _ ℤ)

def stdList (p : ℕ) : List ((Fin n → R) × (Fin n → R)) :=
  List.ofFn fun j : Fin p => (fun k : Fin n => if (k : ℕ) = n - p + j then 1 else 0,
    fun k : Fin n => if (k : ℕ) = n - p + j then 1 else 0)

def stdSeq (p : ℕ) (h : p ≤ n) : SplitSet R n p :=
  ⟨stdList R n p, (mem_splitSeq_iff R n _).2 fun i j hi hj => by
      have hi' : i < p := by simpa [stdList] using hi
      have hj' : j < p := by simpa [stdList] using hj
      simp only [stdList, List.getElem_ofFn, dotProduct]
      rw [Finset.sum_eq_single (⟨n - p + i, by omega⟩ : Fin n)]
      · simp
      · intro b _ hb
        rw [if_neg (fun e => hb (Fin.ext e)), zero_mul]
      · simp,
    by simp [stdList]⟩

end GlobalTheory.HomStab

end
end
