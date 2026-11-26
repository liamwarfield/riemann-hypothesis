module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.OneLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.OneCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FixBdQZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.DualN

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EntryZero
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem filt_ht {Z Y ι : Type} [AddCommGroup Z] [AddCommGroup Y] [Fintype ι] (ht : ι → ℕ) (f : ι → Z →+ Y)
    (P : ι → Set Y) (h0 : ∀ z, (∀ i, f i z = 0) → z = 0) (hP : ∀ i, (P i).Finite)
    (hf : ∀ i z, (∀ j, ht j < ht i → f j z = 0) → f i z ∈ P i) : Finite Z ∧ Nat.card Z ≤ ∏ i, (P i).ncard := by
  classical
  let σ := Fintype.equivFin ι
  let key : ι → Lex (ℕ × Fin (Fintype.card ι)) := fun i => toLex (ht i, σ i)
  have hkey : Function.Injective key := fun a b hab =>
    σ.injective (by simpa [key] using congrArg (fun p => (ofLex p).2) hab)
  letI : LinearOrder ι := LinearOrder.lift' key hkey
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  have hmono : ∀ a b : Fin (Fintype.card ι), ht (e a) < ht (e b) → a < b := by
    intro a b hab
    have : e a < e b := by
      show key (e a) < key (e b)
      exact Prod.Lex.lt_iff.mpr (Or.inl hab)
    exact e.lt_iff_lt.mp this
  obtain ⟨hfin, hcard⟩ := filtCount Z Y (Fintype.card ι) (fun a => f (e a)) (fun a => P (e a))
    (fun z hz => h0 z (fun i => by simpa using hz (e.symm i)))
    (fun a => hP _)
    (fun a z hz => hf (e a) z (fun j hj => by
      simpa using hz (e.symm j) (hmono _ _ (by simpa using hj))))
  refine ⟨hfin, hcard.trans_eq ?_⟩
  exact Equiv.prod_comp e.toEquiv (fun i => (P i).ncard)

private theorem conj_entry {R : Type} [CommRing R] {n : ℕ} (T B T' : Matrix (Fin n) (Fin n) R)
    (hT : ∀ i j, j < i → T i j = 0) (hT' : ∀ i j, j < i → T' i j = 0) (i j : Fin n)
    (hB : ∀ p q, i ≤ p → q ≤ j → (p ≠ i ∨ q ≠ j) → B p q = 0) : (T * B * T') i j = T i i * B i j * T' j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro p _ hp
      by_cases hpi : i ≤ p
      · rw [hB p j hpi le_rfl (Or.inl hp)]
        ring
      · rw [hT i p (not_le.mp hpi)]
        ring
    · simp
  · intro q _ hq
    by_cases hqj : q ≤ j
    · rw [Matrix.mul_apply, Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro p _
      by_cases hpi : i ≤ p
      · rw [hB p q hpi hqj (Or.inr hq)]
        ring
      · rw [hT i p (not_le.mp hpi)]
        ring
    · rw [hT' q j (not_le.mp hqj)]
      ring
  · simp

private def co (X : Type) [CommRing X] {g : ℕ} (o : Option (Fin g)) : DD X g →+ X where
  toFun y := o.elim y.a y.ep
  map_zero' := by cases o <;> rfl
  map_add' y z := by cases o <;> rfl

private theorem co_mul {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ} (o : Option (Fin g)) (c c' : A)
    (y : DD X g) : co X o (algebraMap A (DD X g) c * y * algebraMap A (DD X g) c') = (c * c') • co X o y := by
  cases o with
  | none =>
    show algebraMap A X c * y.a * algebraMap A X c' = (c * c') • y.a
    rw [Algebra.smul_def, map_mul]
    ring
  | some j =>
    show (algebraMap A X c * y.a) * 0 + (algebraMap A X c * y.ep j + 0 * y.a) * algebraMap A X c' =
      (c * c') • y.ep j
    rw [Algebra.smul_def, map_mul]
    ring

private theorem adic_mul {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f f' : D → R}
    (h : AdicCont I f) (h' : AdicCont I f') : AdicCont I fun g => f g * f' g := by
  intro N
  have e : (fun g => Ideal.Quotient.mk (I ^ N) (f g * f' g)) =
      fun g => Ideal.Quotient.mk (I ^ N) (f g) * Ideal.Quotient.mk (I ^ N) (f' g) :=
    funext fun g => map_mul _ _ _
  show IsLocallyConstant (fun g => Ideal.Quotient.mk (I ^ N) (f g * f' g))
  rw [e]
  exact (h N).comp₂ (h' N) _

private theorem adic_sum {D R ι : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} (s : Finset ι) {f : ι → D → R}
    (h : ∀ i, AdicCont I (f i)) : AdicCont I fun g => ∑ i ∈ s, f i g := by
  classical
  intro N
  show IsLocallyConstant (fun g => Ideal.Quotient.mk (I ^ N) (∑ i ∈ s, f i g))
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, map_zero]
    exact IsLocallyConstant.const 0
  · intro a s ha ih
    have e : (fun g => Ideal.Quotient.mk (I ^ N) (∑ i ∈ insert a s, f i g)) =
        fun g => Ideal.Quotient.mk (I ^ N) (f a g) + Ideal.Quotient.mk (I ^ N) (∑ i ∈ s, f i g) :=
      funext fun g => by rw [Finset.sum_insert ha, map_add (f := _)]
    rw [e]
    exact (h a N).comp₂ ih _

private theorem psi_cont {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) (i : Fin n) :
    AdicCont (IsLocalRing.maximalIdeal x.A) fun g => (x.ψ v i g : x.A) := by
  have e : (fun g => (x.ψ v i g : x.A)) = fun g => ∑ q, (∑ p, (((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) i p *
      mat x.ρ (F.φ v g) p q) * (x.w v : Matrix (Fin n) (Fin n) x.A) q i := funext fun g => ((x.tri v g).2 i).symm
  rw [e]
  exact adic_sum _ fun q => adic_mul (adic_sum _ fun p => adic_mul (fun N => IsLocallyConstant.const _)
    fun N => (x.cont p q N).comp_continuous (F.φ_cont v)) fun N => IsLocallyConstant.const _

private theorem pair_count {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) (d : ℕ)
    (hL : LocCount (F.Gv v) (F.ε.comp (F.η.ker.subtype.comp (F.φ v))) d) (i j : Fin n) (hij : i < j) :
    ∃ C : ℕ, ∀ m, {z : F.Gv v → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) =
        z g + ((x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A)) • z h}.Finite ∧
      {z : F.Gv v → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) =
        z g + ((x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A)) • z h}.ncard ≤ Nat.card x.K ^ (m * (1 + d) + C) := by
  let χ : F.Gv v →* x.Aˣ := x.ψ v i * (x.ψ v j)⁻¹
  have hχ : ∀ g, ((χ g : x.Aˣ) : x.A) = (x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A) := by
    intro g
    simp [χ, map_inv]
  have hcont : AdicCont (IsLocalRing.maximalIdeal x.A) fun g => ((χ g : x.Aˣ) : x.A) := by
    have hinv : AdicCont (IsLocalRing.maximalIdeal x.A) fun g : F.Gv v => (x.ψ v j g⁻¹ : x.A) :=
      fun N => (psi_cont x v j N).comp_continuous continuous_inv
    have := adic_mul (psi_cont x v i) hinv
    simp_rw [hχ]
    exact this
  have hne : ∃ g, ((χ g : x.Aˣ) : x.A) ≠
      algebraMap ℤ_[l] x.A ((F.ε.comp (F.η.ker.subtype.comp (F.φ v)) g : ℤ_[l]ˣ) : ℤ_[l]) := by
    by_contra hall
    push_neg at hall
    apply (x.N1 v).2 i j hij
    refine MonoidHom.ext fun g => Units.ext ?_
    have h1 := hall g
    rw [hχ] at h1
    have h2 : ((x.ψ v j g : x.Aˣ) : x.A) * (x.ψ v j g⁻¹ : x.A) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have h3 : ((F.eps ℤ_[l] x.A ((F.φ v) g) : x.Aˣ) : x.A) =
        algebraMap ℤ_[l] x.A ((F.ε.comp (F.η.ker.subtype.comp (F.φ v)) g : ℤ_[l]ˣ) : ℤ_[l]) := by
      rfl
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
    rw [h3, ← h1]
    linear_combination (-((x.ψ v i g : x.Aˣ) : x.A)) * h2
  obtain ⟨C, hC⟩ := oneCount l F n x (F.Gv v) _ d χ hL hcont hne
  refine ⟨C, fun m => ?_⟩
  simp only [hχ] at hC
  exact hC m

private noncomputable def crd {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) (o : Option (Fin k.g)) (i j : Fin n) : k.Zb X v →+ (F.Gv v → X) :=
  AddMonoidHom.mk' (fun β g => co X o ((k.wi1 X v * (β.1 g : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j))
    fun β β' => funext fun g => by
      simp only [AddSubgroup.coe_add, Pi.add_apply, Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
        map_add]

private theorem crd_coc {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) (o : Option (Fin k.g)) (i j : Fin n) (β : k.Zb X v)
    (hB : ∀ g p q, i ≤ p → q ≤ j → (p ≠ i ∨ q ≠ j) →
      (k.wi1 X v * (β.1 g : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) p q = 0) :
    IsLocallyConstant (crd k X v o i j β) ∧ ∀ g h, crd k X v o i j β (g * h) =
      crd k X v o i j β g + ((x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A)) • crd k X v o i j β h := by
  obtain ⟨hlc, hcoc, -, -⟩ := β.2
  have hρ := UpperTheory.V.Pa.rho1 l F n x k X
  have ht := (UpperTheory.V.Pa.tri l F n x k X v).1
  have hw' : ∀ M : Matrix (Fin n) (Fin n) (DD X k.g), k.w1 X v * (k.wi1 X v * M) = M := by
    intro M
    rw [← mul_assoc, (hρ.2.2.2.1 v).2, one_mul]
  refine ⟨?_, ?_⟩
  · exact hlc.comp fun b : k.M1 X =>
      co X o ((k.wi1 X v * (b : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j)
  · intro g h
    show co X o ((k.wi1 X v * (β.1 (g * h) : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j) =
      co X o ((k.wi1 X v * (β.1 g : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j) +
      ((x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A)) •
        co X o ((k.wi1 X v * (β.1 h : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j)
    rw [hcoc g h]
    have hsplit : k.wi1 X v * (k.ρ1 X (F.φ v g) * (β.1 h : Matrix (Fin n) (Fin n) (DD X k.g)) *
        k.ρ1 X (F.φ v g)⁻¹) * k.w1 X v =
        (k.wi1 X v * k.ρ1 X (F.φ v g) * k.w1 X v) *
          (k.wi1 X v * (β.1 h : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) *
          (k.wi1 X v * k.ρ1 X (F.φ v g⁻¹) * k.w1 X v) := by
      rw [map_inv]
      simp only [mul_assoc, hw']
    rw [mul_add, add_mul, Matrix.add_apply, map_add (f := _), hsplit,
      conj_entry _ _ _ (ht g).1 (ht g⁻¹).1 i j (hB h), (ht g).2.1 i, (ht g⁻¹).2.1 j, co_mul]

private abbrev Idx {n : ℕ} (ty : Fin n → Bool) (g : ℕ) : Type :=
  Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2 ∧ ty p.1 = ty p.2} ⊕ Fin g × {p : Fin n × Fin n // p.1 < p.2 ∧ ty p.1 ≠ ty p.2}

private def pos {n : ℕ} {ty : Fin n → Bool} {g : ℕ} : Idx ty g → Option (Fin g) × Fin n × Fin n
  | .inl i => (none, i, i)
  | .inr (.inl p) => (none, p.1)
  | .inr (.inr p) => (some p.1, p.2.1)

private theorem entry_zero {X : Type} [CommRing X] {n g : ℕ} {ty : Fin n → Bool} (B : Matrix (Fin n) (Fin n) (DD X g))
    (h1 : ∀ i j, j < i → B i j = 0) (h2 : TyPat ty B) (p q : Fin n)
    (h : ∀ t : Idx ty g, (pos t).2 = (p, q) → co X (pos t).1 (B (pos t).2.1 (pos t).2.2) = 0) : B p q = 0 := by
  obtain ⟨a1, a2, a3, a4⟩ := h2 p q
  rcases lt_trichotomy p q with c | rfl | c
  · by_cases s : ty p = ty q
    · exact DD.ext (h (.inr (.inl ⟨(p, q), c, s⟩)) rfl) (a3 s) a1 a2
    · exact DD.ext (a4 s) (funext fun m => h (.inr (.inr (m, ⟨(p, q), c, s⟩))) rfl) a1 a2
  · exact DD.ext (h (.inl p) rfl) (a3 rfl) a1 a2
  · exact h1 p q c

theorem UpperTheory.V.Pa.locV :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (v : F.Vl) (d d' : ℕ), LocCount (F.Gv v) (F.ε.comp (F.η.ker.subtype.comp (F.φ v))) d → LocAb l (F.Gv v) (F.Iv v) d' → ∃ C : ℕ, ∀ m, Finite (k.Zb (x.Am m) v) ∧ Nat.card (k.Zb (x.Am m) v) ≤ Nat.card x.K ^ (m * (n * (d' + 1) + nu n x.a k.g * (1 + d)) + C) := by
  intro l _ F n x k v d d' hL hA
  classical
  have hpc : ∀ p : Fin n × Fin n, p.1 < p.2 → ∃ C : ℕ, ∀ m,
      {z : F.Gv v → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) =
        z g + ((x.ψ v p.1 g : x.A) * (x.ψ v p.2 g⁻¹ : x.A)) • z h}.Finite ∧
      {z : F.Gv v → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) =
        z g + ((x.ψ v p.1 g : x.A) * (x.ψ v p.2 g⁻¹ : x.A)) • z h}.ncard ≤
        Nat.card x.K ^ (m * (1 + d) + C) :=
    fun p hp => pair_count x v d hL p.1 p.2 hp
  let Cof : Idx (x.ty v) k.g → ℕ := fun t => match t with
    | .inl _ => 0
    | .inr (.inl p) => Classical.choose (hpc p.1 p.2.1)
    | .inr (.inr p) => Classical.choose (hpc p.2.1 p.2.2.1)
  refine ⟨∑ t, Cof t, fun m => ?_⟩
  let B : k.Zb (x.Am m) v → F.Gv v → Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) := fun z g =>
    k.wi1 (x.Am m) v * ((z.1 g : k.M1 (x.Am m)) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) *
      k.w1 (x.Am m) v
  have hBtri : ∀ z g, ∀ i j, j < i → B z g i j = 0 := fun z g => z.2.2.2.1 g
  have hBty : ∀ z g, TyPat (x.ty v) (B z g) := fun z g =>
    ((UpperTheory.V.Pa.tri l F n x k (x.Am m) v).2 _).mp (z.1 g).2
  let Sh : Set (F.Gv v → x.Am m) := {z | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧
    ∀ g ∈ muG l (F.Gv v), z g = 0}
  let Sp : Fin n → Fin n → Set (F.Gv v → x.Am m) := fun i j => {z | IsLocallyConstant z ∧ ∀ g h,
    z (g * h) = z g + ((x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A)) • z h}
  let P : Idx (x.ty v) k.g → Set (F.Gv v → x.Am m) := fun t => match t with
    | .inl _ => Sh
    | .inr (.inl p) => Sp p.1.1 p.1.2
    | .inr (.inr p) => Sp p.2.1.1 p.2.1.2
  let ht : Idx (x.ty v) k.g → ℕ := fun t => ((pos t).2.2 : ℕ) - (pos t).2.1
  let f : Idx (x.ty v) k.g → k.Zb (x.Am m) v →+ (F.Gv v → x.Am m) := fun t =>
    crd k (x.Am m) v (pos t).1 (pos t).2.1 (pos t).2.2
  have h0 : ∀ z, (∀ t, f t z = 0) → z = 0 := by
    intro z hz
    have hBz : ∀ g, B z g = 0 := by
      intro g
      exact Matrix.ext fun p q => entry_zero _ (hBtri z g) (hBty z g) p q fun t _ => congrFun (hz t) g
    apply Subtype.ext
    funext g
    apply Subtype.ext
    have hρ := (UpperTheory.V.Pa.rho1 l F n x k (x.Am m)).2.2.2.1 v
    have e : ((z.1 g : k.M1 (x.Am m)) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) =
        k.w1 (x.Am m) v * B z g * k.wi1 (x.Am m) v := by
      simp only [B, ← mul_assoc, hρ.2, one_mul]
      rw [mul_assoc, hρ.2, mul_one]
    rw [e, hBz g, mul_zero, zero_mul]
    rfl
  have hP : ∀ t, (P t).Finite := by
    intro t
    rcases t with i | p | ⟨o, p⟩
    · exact (homCount l F n x _ (F.Iv v) d' m hA).1
    · exact ((Classical.choose_spec (hpc p.1 p.2.1)) m).1
    · exact ((Classical.choose_spec (hpc p.1 p.2.1)) m).1
  have hf : ∀ t z, (∀ t', ht t' < ht t → f t' z = 0) → f t z ∈ P t := by
    intro t z hz
    have hB : ∀ g p q, (pos t).2.1 ≤ p → q ≤ (pos t).2.2 → (p ≠ (pos t).2.1 ∨ q ≠ (pos t).2.2) →
        B z g p q = 0 := by
      intro g p q hp hq hne
      by_cases hqp : q < p
      · exact hBtri z g p q hqp
      · refine entry_zero _ (hBtri z g) (hBty z g) p q fun t' ht' => ?_
        have e1 : (pos t').2.1 = p := congrArg Prod.fst ht'
        have e2 : (pos t').2.2 = q := congrArg Prod.snd ht'
        have a1 : ((pos t).2.1 : ℕ) ≤ (p : ℕ) := hp
        have a2 : (q : ℕ) ≤ ((pos t).2.2 : ℕ) := hq
        have a3 : (p : ℕ) ≤ (q : ℕ) := not_lt.mp hqp
        have a4 : (p : ℕ) ≠ (pos t).2.1 ∨ (q : ℕ) ≠ (pos t).2.2 :=
          hne.imp (fun h e => h (Fin.ext e)) (fun h e => h (Fin.ext e))
        have hlt : ht t' < ht t := by
          show ((pos t').2.2 : ℕ) - (pos t').2.1 < ((pos t).2.2 : ℕ) - (pos t).2.1
          rw [e1, e2]
          omega
        exact congrFun (hz t' hlt) g
    obtain ⟨hlc, hcoc⟩ := crd_coc k (x.Am m) v (pos t).1 (pos t).2.1 (pos t).2.2 z hB
    rcases t with i | p | ⟨o, p⟩
    · refine ⟨hlc, fun g h => ?_, fun g hg => ?_⟩
      · have e := hcoc g h
        have one : (x.ψ v i g : x.A) * (x.ψ v i g⁻¹ : x.A) = 1 := by
          rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
        rw [show ((x.ψ v (pos (Sum.inl i)).2.1 g : x.A) * (x.ψ v (pos (Sum.inl i)).2.2 g⁻¹ : x.A)) = 1
          from one, one_smul] at e
        exact e
      · obtain ⟨-, -, -, hmu⟩ := z.2
        have e : B z g i i = 0 := hmu g hg i
        show (B z g i i).a = 0
        rw [e]
        rfl
    · exact ⟨hlc, hcoc⟩
    · exact ⟨hlc, hcoc⟩
  obtain ⟨hfin, hcard⟩ := filt_ht ht f P h0 hP hf
  refine ⟨hfin, hcard.trans ?_⟩
  have hK : 0 < Nat.card x.K := Nat.card_pos
  let base : Idx (x.ty v) k.g → ℕ := fun t => match t with
    | .inl _ => m * (d' + 1)
    | .inr _ => m * (1 + d)
  calc ∏ t, (P t).ncard ≤ ∏ t, Nat.card x.K ^ (base t + Cof t) := by
        refine Finset.prod_le_prod' fun t _ => ?_
        rcases t with i | p | ⟨o, p⟩
        · simpa [base, Cof] using (homCount l F n x _ (F.Iv v) d' m hA).2
        · exact ((Classical.choose_spec (hpc p.1 p.2.1)) m).2
        · exact ((Classical.choose_spec (hpc p.1 p.2.1)) m).2
    _ = Nat.card x.K ^ (∑ t, (base t + Cof t)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ Nat.card x.K ^ (m * (n * (d' + 1) + nu n x.a k.g * (1 + d)) + ∑ t, Cof t) := by
        apply Nat.pow_le_pow_right hK
        rw [Finset.sum_add_distrib]
        apply Nat.add_le_add_right
        obtain ⟨-, hnu, -, -⟩ := UpperTheory.V.Pa.tyCard l F n x v k.g
        have s1 : ∑ t : Idx (x.ty v) k.g, base t = n * (m * (d' + 1)) +
            (Fintype.card {p : Fin n × Fin n // p.1 < p.2 ∧ x.ty v p.1 = x.ty v p.2} +
              k.g * Fintype.card {p : Fin n × Fin n // p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2}) *
              (m * (1 + d)) := by
          rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
          simp only [base, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            smul_eq_mul]
          ring
        rw [s1, Fintype.card_subtype, Fintype.card_subtype, hnu]
        apply le_of_eq
        ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.CommutingMatrixOffdiagZero
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private def ddBaseRingHom (X : Type) [CommRing X] (g : ℕ) : DD X g →+* X where
  toFun := DD.a
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private def ddEpsCoordAddHom (X : Type) [CommRing X] (g : ℕ) (j : Fin g) : DD X g →+ X where
  toFun y := y.ep j
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem commuting_matrix_offdiag_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n)
    (Z : Matrix (Fin n) (Fin n) x.A) (hZ : ∀ g, mat x.ρ g * Z = Z * mat x.ρ g) (i j : Fin n) (hij : i ≠ j) :
    Z i j = 0 := by
  have hmem : Matrix.single j j (1 : x.A) ∈ Ev (PowerSeries x.K) (PowerSeries x.K) n x.a := by
    show ∀ i' j' : Fin n, _
    intro i' j'
    refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
    rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h Iff.rfl
  obtain ⟨s, hs⟩ := x.span _ hmem
  have hcomm : ∀ M ∈ Submodule.span (PowerSeries x.K) (⇑(mat x.ρ) '' ↑F.G'), Z * M = M * Z := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, -, rfl⟩ := hM
      exact (hZ g).symm
    | zero => simp
    | add M N _ _ hM hN => rw [Matrix.mul_add, Matrix.add_mul, hM, hN]
    | smul c M _ hM => rw [Matrix.mul_smul, Matrix.smul_mul, hM]
  have h1 := hcomm _ hs
  rw [Matrix.mul_smul, Matrix.smul_mul] at h1
  have h2 := congrFun (congrFun h1 i) j
  simpa [hij, PowerSeries.X_ne_zero] using h2

private theorem skew_commuting_matrix_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (hl : l ≠ 2)
    (Z : Matrix (Fin n) (Fin n) x.A) (hZ : ∀ g, mat x.ρ g * Z = Z * mat x.ρ g) (ht : Zᵀ = -Z) : Z = 0 := by
  have h2u : IsUnit (2 : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    have h' : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    have hl' : l ∣ 2 := by exact_mod_cast h'
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hl')
  have hu : IsUnit (2 : x.A) := by
    have := h2u.map ((algebraMap x.K (PowerSeries x.K)).comp (algebraMap ℤ_[l] x.K))
    rwa [map_ofNat] at this
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    have h1 := congrFun (congrFun ht i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
    have h2 : (2 : x.A) * Z i i = 0 := by linear_combination h1
    simpa using hu.mul_right_eq_zero.mp h2
  · exact commuting_matrix_offdiag_zero x Z hZ i j hij

private theorem rho1_map_ddBaseRingHom_eq_mat_rho {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (k.ρ1 x.A g).map (ddBaseRingHom x.A k.g) = mat x.ρ g := by
  have ha : ∀ y, ddBaseRingHom x.A k.g y = y.a := fun _ => rfl
  have hb : ∀ y : x.A, (algebraMap x.A (DD x.A k.g) y).a = y := fun _ => rfl
  have h0 : (0 : DD x.A k.g).a = 0 := rfl
  rw [Kap.ρ1, Matrix.map_mul]
  refine Matrix.ext fun i j => ?_
  simp [ha, hb, h0, DD.epM, NP.ρX, Matrix.mul_apply, Matrix.one_apply, apply_ite DD.a, DD.one_a]

private theorem map_ep_mul_eq_leibniz {X : Type} [CommRing X] {g n : ℕ} (M N : Matrix (Fin n) (Fin n) (DD X g)) (j : Fin g) :
    (M * N).map (fun y => y.ep j) = M.map DD.a * N.map (fun y => y.ep j) + M.map (fun y => y.ep j) * N.map DD.a := by
  refine Matrix.ext fun r c => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show (∑ t, M r t * N t c).ep j = ∑ t, (M r t * N t c).ep j from map_sum (ddEpsCoordAddHom X g j) _ _]
  simp [DD.mul_ep]

private theorem map_a_mul_eq_map_a_mul_map_a {X : Type} [CommRing X] {g n : ℕ} (M N : Matrix (Fin n) (Fin n) (DD X g)) :
    (M * N).map DD.a = M.map DD.a * N.map DD.a :=
  Matrix.map_mul (f := ddBaseRingHom X g)

private theorem skew_invariant_M1_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (hl : l ≠ 2)
    (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)) (hm : Z ∈ k.M1 x.A) (ht : Zᵀ = -Z)
    (hZ : ∀ g, k.ρ1 x.A g * Z * k.ρ1 x.A g⁻¹ = Z) : Z = 0 := by
  have hA0 : ∀ g : F.G₀, (k.ρ1 x.A g).map DD.a = mat x.ρ g := fun g => rho1_map_ddBaseRingHom_eq_mat_rho k g
  have hinv : ∀ g : F.G₀, mat x.ρ g⁻¹ * mat x.ρ g = 1 := fun g => by
    rw [← map_mul, inv_mul_cancel, map_one]
  have comm_of : ∀ W : Matrix (Fin n) (Fin n) x.A, (∀ g, mat x.ρ g * W * mat x.ρ g⁻¹ = W) →
      ∀ g, mat x.ρ g * W = W * mat x.ρ g := by
    intro W hW g
    calc mat x.ρ g * W = mat x.ρ g * W * (mat x.ρ g⁻¹ * mat x.ρ g) := by rw [hinv, Matrix.mul_one]
      _ = W * mat x.ρ g := by rw [← Matrix.mul_assoc, hW]
  have hA : Z.map DD.a = 0 := by
    apply skew_commuting_matrix_zero x hl
    · apply comm_of
      intro g
      have := congrArg (fun M => M.map DD.a) (hZ g)
      simpa only [map_a_mul_eq_map_a_mul_map_a, hA0] using this
    · refine Matrix.ext fun r c => ?_
      have h1 := congrFun (congrFun ht r) c
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
      simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, h1, DD.neg_a]
  have hE : ∀ t : Fin k.g, Z.map (fun y => y.ep t) = 0 := by
    intro t
    apply skew_commuting_matrix_zero x hl
    · apply comm_of
      intro g
      have := congrArg (fun M => M.map (fun y => y.ep t)) (hZ g)
      simp only [map_ep_mul_eq_leibniz, map_a_mul_eq_map_a_mul_map_a, hA0, hA, Matrix.mul_zero, Matrix.zero_mul, zero_add,
        add_zero] at this
      exact this
    · refine Matrix.ext fun r c => ?_
      have h1 := congrFun (congrFun ht r) c
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
      simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, h1, DD.neg_ep]
  refine Matrix.ext fun r c => ?_
  have hm' : (Z r c).ep' = 0 ∧ (Z r c).eta = 0 := by
    obtain ⟨h1, h2⟩ := (show ∀ i j : Fin n, _ from hm) r c
    by_cases hb : (↑r < x.a ↔ ↑c < x.a)
    · obtain ⟨-, -, h3, h4⟩ := h1 hb
      exact ⟨h3 rfl, h4 rfl⟩
    · obtain ⟨-, -, h3, h4⟩ := h2 hb
      exact ⟨h3 rfl, h4 rfl⟩
  rw [Matrix.zero_apply]
  refine DD.ext ?_ (funext fun t => ?_) ?_ ?_
  · simpa using congrFun (congrFun hA r) c
  · simpa using congrFun (congrFun (hE t) r) c
  · exact hm'.1
  · exact hm'.2

private def ddMapRingHom {A X : Type} [CommRing A] [CommRing X] (g : ℕ) (f : A →+* X) : DD A g →+* DD X g where
  toFun y := ⟨f y.a, fun j => f (y.ep j), fun j => f (y.ep' j), f y.eta⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

private theorem rho1_map_ddMapRingHom_eq_rho1 {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x)
    (X : Type) [CommRing X] [Algebra x.A X] (g : F.G₀) :
    (k.ρ1 x.A g).map (ddMapRingHom k.g (algebraMap x.A X)) = k.ρ1 X g := by
  have hr : ∀ y, ddMapRingHom k.g (algebraMap x.A X) y = ⟨algebraMap x.A X y.a, fun j => algebraMap x.A X (y.ep j), fun j => algebraMap x.A X (y.ep' j), algebraMap x.A X y.eta⟩ := fun _ => rfl
  have hb : ∀ (Y : Type) [CommRing Y] [Algebra x.A Y] (y : x.A), algebraMap x.A (DD Y k.g) y = ⟨algebraMap x.A Y y, 0, 0, 0⟩ := fun _ _ _ _ => rfl
  rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul]
  congr 1
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply]
    by_cases hij : i = j
    · subst hij
      refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, DD.epM, DD.add_ep, DD.one_ep, DD.add_ep', DD.one_ep', DD.add_a, DD.add_eta, DD.one_eta, DD.one_a]
    · refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, DD.epM, hij, DD.zero_ep, DD.zero_a]
  · refine Matrix.ext fun i j => ?_
    refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, hb, NP.ρX]

theorem UpperTheory.V.Pa.h0G :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x), l ≠ 2 → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.M1 (x.Am m) ∧ Yᵀ = -Y ∧ ∀ g : G0.G₀, k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹ = Y}.ncard ≤ Nat.card x.K ^ C := by
  intro l _ L G G0 h n x k hl
  obtain ⟨C, hC⟩ := fixBd l G0.frame n x k (k.M1 x.A) true false false false false true false false
    G0.G₀ (fun _ => 1) (fun s => k.ρ1 x.A s) (fun s => k.ρ1 x.A s⁻¹) true rfl
  refine ⟨C, fun m => ?_⟩
  have hfin : ∀ W : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)), W = ⊥ →
      Nat.card x.K ^ (m * Module.finrank x.A W + C) = Nat.card x.K ^ C := by
    rintro W rfl
    simp
  refine le_trans (le_of_eq ?_) ((hC m).trans (le_of_eq (hfin _ ?_)))
  · clear hC hfin
    congr 1
    ext Y
    have hred : ∀ s : G0.G₀, ((k.ρ1 x.A s).map fun y : DD x.A k.g =>
        (⟨(algebraMap x.A (x.Am m)) y.a, fun j => (algebraMap x.A (x.Am m)) (y.ep j),
          fun j => (algebraMap x.A (x.Am m)) (y.ep' j), (algebraMap x.A (x.Am m)) y.eta⟩ : DD (x.Am m) k.g))
        = k.ρ1 (x.Am m) s :=
      fun s => rho1_map_ddMapRingHom_eq_rho1 k (x.Am m) s
    simp only [Set.mem_setOf_eq, one_smul, forall_const, hred]
    exact Iff.rfl
  · rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, ↓reduceIte] at hZ
    obtain ⟨⟨hm, ht⟩, hfix⟩ := hZ
    apply skew_invariant_M1_zero k hl Z hm
    · simpa [add_eq_zero_iff_eq_neg] using ht
    · intro g
      have := hfix g
      simpa [sub_eq_zero, Matrix.mul_assoc] using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.Rho1MapReductionLevel
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private def ddBaseCompRingHom (X : Type) [CommRing X] (g : ℕ) : DD X g →+* X where
  toFun := DD.a
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem sandwich_map_smul {R X : Type} [CommRing R] [CommRing X] {n : ℕ} (α : R → X) (φ : R →+ X)
    (c : R) (P Z Q : Matrix (Fin n) (Fin n) R) (h : ∀ i j u, φ (u * Z i j) = α u * φ (Z i j))
    (hα : ∀ u v, α (u * v) = α u * α v) :
    (c • (P * Z * Q)).map φ = α c • (P.map α * Z.map φ * Q.map α) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [show c * (P i a * Z a b * Q b j) = (c * (P i a * Q b j)) * Z a b by ring, h, hα, hα]
  ring

private theorem rho1_map_ddBaseCompRingHom_eq_mat {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (k.ρ1 x.A g).map (ddBaseCompRingHom x.A k.g) = mat x.ρ g := by
  have h1 : (1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A)).map (ddBaseCompRingHom x.A k.g) = 1 := by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
    exact add_eq_left.2 (Matrix.ext fun _ _ => rfl)
  rw [Kap.ρ1, Matrix.map_mul, h1, one_mul]
  exact Matrix.ext fun _ _ => rfl

private theorem rho1_map_algebraMap_am_eq_rho1 {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (m : ℕ) (g : F.G₀) :
    (k.ρ1 x.A g).map (fun y => (⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j),
      fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩ : DD (x.Am m) k.g)) =
      k.ρ1 (x.Am m) g := by
  change (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = _
  rw [Kap.ρ1, Kap.ρ1, map_mul, map_add (f := _), map_one]
  refine congrArg₂ (· * ·) (congrArg (1 + ·) (Matrix.ext fun i j => ?_)) (Matrix.ext fun i j => ?_)
  · ext <;> simp [DD.epM]
  · exact (x.redD k.g m).commutes _

private theorem site_vector_first {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (D : Subgroup F.G₀)
    (h4 : x.N4 D) (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)) (ha : ∀ i j, (Z i j).a = 0) (he : ∀ i j, (Z i j).ep = 0)
    (hZ : ∀ g ∈ D, epsD k x.A g • (k.ρ1 x.A g * Z * k.ρ1 x.A g⁻¹) = Z) : Z = 0 := by
  have key : ∀ φ : DD x.A k.g →+ x.A, (∀ i j u, φ (u * Z i j) = u.a * φ (Z i j)) → ∀ i j, φ (Z i j) = 0 := by
    intro φ hφ
    have : Z.map φ = 0 := by
      refine h4 _ fun g hg => ?_
      have e := sandwich_map_smul (ddBaseCompRingHom x.A k.g) φ (epsD k x.A g) (k.ρ1 x.A g) Z (k.ρ1 x.A g⁻¹) hφ (map_mul _)
      rw [hZ g hg, rho1_map_ddBaseCompRingHom_eq_mat, rho1_map_ddBaseCompRingHom_eq_mat] at e
      conv_rhs => rw [e]
      rw [smul_mul_assoc, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
      rfl
    exact fun i j => congrFun (congrFun this i) j
  have h' : ∀ t i j, (Z i j).ep' t = 0 := fun t =>
    key ⟨⟨fun y => y.ep' t, rfl⟩, fun _ _ => rfl⟩ fun i j u => by
      show (u * Z i j).ep' t = u.a * (Z i j).ep' t
      simp [ha]
  have h'' : ∀ i j, (Z i j).eta = 0 :=
    key ⟨⟨fun y => y.eta, rfl⟩, fun _ _ => rfl⟩ fun i j u => by
      show (u * Z i j).eta = u.a * (Z i j).eta
      simp [ha, he, h']
  refine Matrix.ext fun i j => ?_
  ext <;> simp [ha, he, h', h'']

theorem UpperTheory.V.Pa.h0v0 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (D : Subgroup F.G₀), x.N4 D → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ ∀ g ∈ D, epsD k (x.Am m) g • (k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹) = Y}.ncard ≤ Nat.card x.K ^ C := by
  intro l _ F n x k D h4
  obtain ⟨C, hC⟩ := UpperTheory.V.Pa.fixBd l F n x k _ false false false true false false true false D
    (fun s => algebraMap ℤ_[l] x.A (F.ε (s : F.G₀) : ℤ_[l])) (fun s => k.ρ1 x.A s) (fun s => k.ρ1 x.A (s : F.G₀)⁻¹)
    false rfl
  refine ⟨C, fun m => ?_⟩
  have h := hC m
  rw [(Submodule.eq_bot_iff (_ ⊓ _ ⊓ _)).2 ?_, finrank_bot, mul_zero, zero_add] at h
  · refine le_of_eq_of_le ?_ h
    congr 1
    ext Y
    simp only [Set.mem_setOf_eq, rho1_map_algebraMap_am_eq_rho1, Subtype.forall, epsD, algebraMap_smul, Bool.false_eq_true, false_imp_iff,
      true_and]
    rfl
  · rintro Z ⟨⟨h1, -⟩, h2⟩
    refine site_vector_first k D h4 Z (fun i j => ?_) (fun i j => ?_) fun g hg => ?_
    · by_cases e : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
      · exact ((h1 i j).1 e).1 rfl
      · exact ((h1 i j).2 e).1 rfl
    · by_cases e : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
      · exact ((h1 i j).1 e).2.1 rfl
      · exact ((h1 i j).2 e).2.1 rfl
    · have e := (Submodule.mem_iInf _).1 h2 ⟨g, hg⟩
      rw [epsD, algebraMap_smul, mul_assoc, ← sub_eq_zero]
      exact e
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FinrankCentralizerW1Le
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem centralizer_rank_le {A : Type} [CommRing A] [IsDomain A] {n : ℕ} (al : Fin n → A) (P : Matrix (Fin n) (Fin n) A)
    (hal : Function.Injective al) (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i))) :
    (∀ (N : Type) [AddCommGroup N] [Module A N] (f : N →ₗ[A] Matrix (Fin n) (Fin n) A), Function.Injective f →
      (∀ z, P * f z = f z * P) → Module.finrank A N ≤ n) ∧
    ∀ E Y : Matrix (Fin n) (Fin n) A, P * E = E * P → P * Y = Y * P → E * Y = Y * E := by
  let K := FractionRing A
  have inj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  let φ : Matrix (Fin n) (Fin n) A →ₐ[A] Matrix (Fin n) (Fin n) K := (Algebra.ofId A K).mapMatrix
  have φinj : Function.Injective φ := Matrix.map_injective inj
  obtain ⟨h1, h2⟩ := UpperTheory.V.AlgebraTools.centraliser_rank (fun i => algebraMap A K (al i)) (φ P) (inj.comp hal) (by
    have : φ P = P.map (algebraMap A K) := rfl
    rw [this, Matrix.charpoly_map, hP, Polynomial.map_prod]
    simp)
  refine ⟨fun N _ _ f hf hc => ?_, fun E Y hE hY => φinj ?_⟩
  · set U := LinearMap.ker (LinearMap.mulLeft K (φ P) - LinearMap.mulRight K (φ P)) with hU
    let ψ : N →ₗ[A] U :=
      { toFun := fun z => ⟨φ (f z), by
          rw [hU, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
            ← map_mul, hc, map_mul, sub_self]⟩
        map_add' := fun y z => Subtype.ext (by simp)
        map_smul' := fun c z => Subtype.ext (by simp) }
    have hψ : Function.Injective ψ := fun y z h => hf (φinj (congrArg Subtype.val h))
    apply Module.finrank_le_of_rank_le
    refine (LinearMap.rank_le_of_injective ψ hψ).trans ?_
    rw [← IsLocalization.rank_eq K (nonZeroDivisors A) le_rfl, ← Module.finrank_eq_rank, h1, Fintype.card_fin]
  · obtain ⟨q, hq⟩ := h2 (φ Y) (by rw [← map_mul, hY, map_mul])
    obtain ⟨r, hr⟩ := h2 (φ E) (by rw [← map_mul, hE, map_mul])
    rw [map_mul, map_mul, hq, hr, ← map_mul, ← map_mul, mul_comm]

private theorem dual_sum_ep_prime_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem dual_sum_eta_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem dual_sum_a_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem finrank_centralizer_W1_le {A : Type} [CommRing A] [IsDomain A] {n a g : ℕ} (al : Fin n → A)
    (P : Matrix (Fin n) (Fin n) A)
    (hal : Function.Injective al) (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)))
    (hev : P ∈ Ev A A n a) (R : Matrix (Fin n) (Fin n) (DD A g)) (hR : ∀ i j, (R i j).a = P i j)
    (N : Submodule A (Matrix (Fin n) (Fin n) (DD A g))) (h1 : N ≤ pairedDualFirstOrderDualMatrixSpace n A A g a) (h2 : ∀ Z ∈ N, R * Z = Z * R) :
    Module.finrank A N ≤ n := by
  obtain ⟨c1, c2⟩ := centralizer_rank_le al P hal hP
  have ha : ∀ Z ∈ N, ∀ i j, (Z i j).a = 0 ∧ (Z i j).ep = 0 := fun Z hZ i j => by
    by_cases h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · have := (h1 hZ i j).1 h
      exact ⟨this.1 rfl, this.2.1 rfl⟩
    · have := (h1 hZ i j).2 h
      exact ⟨this.1 rfl, this.2.1 rfl⟩
  have hb : ∀ Z ∈ N, ∀ i j s, (Z i j).ep' s = 0 := fun Z hZ i j s => by
    by_cases h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · exact congrFun (((h1 hZ i j).1 h).2.2.1 rfl) s
    · have e := c2 (diagonal fun i => if (i : ℕ) < a then 1 else 0) (Matrix.of fun i j => (Z i j).ep' s) ?_ ?_
      · have e' := congrFun (congrFun e i) j
        rw [diagonal_mul, mul_diagonal, of_apply] at e'
        by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp_all
      · ext u v
        rw [diagonal_mul, mul_diagonal]
        by_cases h' : ((u : ℕ) < a) ↔ ((v : ℕ) < a)
        · simp [h', mul_comm]
        · have : P u v = 0 := (hev u v).2 h'
          simp [this]
      · ext u v
        have e' := congrArg (fun M : Matrix (Fin n) (Fin n) (DD A g) => (M u v).ep' s) (h2 Z hZ)
        simpa [Matrix.mul_apply, dual_sum_ep_prime_coord, hR, fun i j => (ha Z hZ i j).1] using e'
  have hs : ∀ (c : A) (y : DD A g), (c • y).eta = c * y.eta := fun c y => by
    have hc : c • y = DD.C (algebraMap A A c) * y := rfl
    simp [hc]
  refine c1 N
    { toFun := fun Z => Matrix.of fun i j => (Z.1 i j).eta
      map_add' := fun y z => rfl
      map_smul' := fun c z => by ext i j; simp [hs] } ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro Z hZ
    ext i j
    · exact (ha _ Z.2 i j).1
    · exact congrFun (ha _ Z.2 i j).2 _
    · exact hb _ Z.2 i j _
    · exact congrFun (congrFun hZ i) j
  · rintro ⟨Z, hZ⟩
    change P * (Matrix.of fun i j => (Z i j).eta) = (Matrix.of fun i j => (Z i j).eta) * P
    ext u v
    have e' := congrArg (fun M : Matrix (Fin n) (Fin n) (DD A g) => (M u v).eta) (h2 Z hZ)
    simpa [Matrix.mul_apply, dual_sum_eta_coord, hR, fun i j => (ha Z hZ i j).1, fun i j => (ha Z hZ i j).2, hb Z hZ] using e'

theorem UpperTheory.V.Pa.h0q :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (σ : F.G₀) (al : Fin n → x.A), Function.Injective al → (mat x.ρ σ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ k.ρ1 (x.Am m) σ * Y * k.ρ1 (x.Am m) σ⁻¹ = Y}.ncard ≤ Nat.card x.K ^ (m * n + C) := by
  intro l _ F n x k σ al hal hP
  obtain ⟨C, hC⟩ := fixBd l F n x k _ false false false true false false true false Unit (fun _ => 1)
    (fun _ => k.ρ1 x.A σ) (fun _ => k.ρ1 x.A σ⁻¹) false rfl
  refine ⟨C, fun m => ?_⟩
  have red : ∀ g, (k.ρ1 x.A g).map (fun y => (⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j), fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩ : DD (x.Am m) k.g)) = k.ρ1 (x.Am m) g := by
    intro g
    change (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = _
    rw [Kap.ρ1, Kap.ρ1, map_mul, map_add (f := _), map_one]
    rfl
  refine le_trans (le_of_eq ?_) ((hC m).trans (Nat.pow_le_pow_right Nat.card_pos ?_))
  · congr 1
    ext Y
    simp only [red, one_smul, Set.mem_setOf_eq, forall_const, Bool.false_eq_true, IsEmpty.forall_iff, true_and]
    rfl
  · refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _
    refine finrank_centralizer_W1_le al _ hal hP (x.blk σ) (k.ρ1 x.A σ) (fun i j => ?_) _ (inf_le_left.trans inf_le_left) fun Z hZ => ?_
    · have hc : ∀ c : x.A, algebraMap x.A (DD x.A k.g) c = DD.C c := fun c => rfl
      rw [Kap.ρ1, add_mul, one_mul]
      simp [Matrix.mul_apply, dual_sum_a_coord, DD.epM, NP.ρX, hc]
    · obtain ⟨r1, r2, -⟩ := rho1 l F n x k x.A
      have e : (1 : x.A) • (k.ρ1 x.A σ * (Z * k.ρ1 x.A σ⁻¹)) - Z = 0 := (Submodule.mem_iInf _).1 hZ.2 ()
      rw [one_smul, sub_eq_zero] at e
      conv_rhs => rw [← e]
      rw [mul_assoc, mul_assoc, ← r2, inv_mul_cancel, r1, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.W1BoundArithmeticRankTwo
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem card_inv_le {A R Γ : Type} [CommRing A] [CommRing R] [Algebra A R] [Finite R] [Group Γ] {n : ℕ}
    {V : Submodule A (Matrix (Fin n) (Fin n) R)} (r : Representation A Γ V) (S : Set (Matrix (Fin n) (Fin n) R))
    (h : ∀ y : V, (∀ g, r g y = y) → (y : Matrix (Fin n) (Fin n) R) ∈ S) : Nat.card r.invariants ≤ S.ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective
    (fun y : r.invariants => (⟨((y : V) : Matrix (Fin n) (Fin n) R),
      h (y : V) ((Representation.mem_invariants r _).1 y.2)⟩ : S)) ?_
  intro a b hab
  have e := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext e)

private theorem cancel_pow {s b K u w : ℕ} (hK : 0 < K) (h : s * K ^ u ≤ b * K ^ (w + u)) : s ≤ b * K ^ w := by
  rw [pow_add, ← mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos hK u)

private theorem sum_exp {V : Type} [Fintype V] (m n ν d q c₁ c₂ c₀ : ℕ) (d' dv C : V → ℕ) (Cq : Fin q → ℕ)
    (h1 : ∑ v, d' v = d) (h2 : ∑ v, dv v = d) :
    c₁ + c₂ + ∑ v, (m * (n * (d' v + 1) + ν * (1 + dv v)) + C v) +
      ∑ j : Option (Fin q), (j.elim c₀ fun i => m * n + Cq i) =
    (m * (n * d + n * q) + (c₁ + c₂ + c₀ + ∑ v, C v + ∑ j, Cq j)) + (m * (n + ν) * Fintype.card V + m * ν * d) := by
  rw [Fintype.sum_option]
  simp only [Option.elim, mul_add, add_mul, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin, h1, h2]
  ring

theorem UpperTheory.V.Pa.W1_bound_arithmetic_rank_two :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A) (d : ℕ) (D0 : Subgroup G0.G₀) (_ : ArSys T d D0) (d' : L.Vl → ℕ), l ≠ 2 → ∑ v, d' v = d → (∀ v, Nonempty (LocAb l (L.Gv v) (L.Iv v) (d' v))) → PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → x.N4 D0 → T.Eig x al → Detects k (Set.range T.sg) → T.B1 k (n * d + n * T.q) := by
  intro l _ L G0 T n x k al d D0 A d' hl hd' hLoc hphi hPL hN4 hEig hDet
  obtain ⟨c₁, hc₁⟩ := h0G l L G0 G0 (Glob.Hom.refl G0) n x k hl
  obtain ⟨c₂, hc₂⟩ := dualN l L G0 T n x k hl hphi hPL hDet
  obtain ⟨c₀, hc₀⟩ := h0v0 l G0.frame n x k D0 hN4
  have hq := fun j => h0q l G0.frame n x k (T.sg j) (al j) (hEig j).1 (hEig j).2
  choose Cq hCq using hq
  have hv : ∀ v, ∃ C, ∀ m, Finite (k.Zb (x.Am m) v) ∧ Nat.card (k.Zb (x.Am m) v) ≤
      Nat.card x.K ^ (m * (n * (d' v + 1) + nu n x.a k.g * (1 + A.dv v)) + C) := by
    intro v
    refine locV l G0.frame n x k v (A.dv v) (d' v) ?_ (hLoc v).some
    have h0 := (A.counts 0).locV v
    rw [A.dv_eq 0] at h0
    convert h0 using 2
    refine MonoidHom.ext fun g => ?_
    show G0.ε (G0.φ v g : G0.Γ) = (T.GN 0).ε ((T.GN 0).φ v g : (T.GN 0).Γ)
    rw [← (T.h 0).ε]
    exact congrArg G0.ε ((T.h 0).φ v g).symm
  choose Cv hCv using hv
  refine ⟨c₁ + c₂ + c₀ + ∑ v, Cv v + ∑ j, Cq j, fun m => ?_⟩
  filter_upwards [hc₂ m, phEq l L G0 T n x k m hphi hPL] with N hN2 hNph
  have r1 := rho1 l G0.frame n x k (x.Am m)
  have inv_eq : ∀ g σ : G0.G₀, k.ρ1 (x.Am m) g = k.ρ1 (x.Am m) σ →
      k.ρ1 (x.Am m) g⁻¹ = k.ρ1 (x.Am m) σ⁻¹ := by
    intro g σ e
    calc k.ρ1 (x.Am m) g⁻¹ = k.ρ1 (x.Am m) g⁻¹ * k.ρ1 (x.Am m) (σ * σ⁻¹) := by
          rw [mul_inv_cancel, r1.1, mul_one]
      _ = k.ρ1 (x.Am m) (g⁻¹ * g) * k.ρ1 (x.Am m) σ⁻¹ := by
          rw [r1.2.1, r1.2.1, e, mul_assoc]
      _ = k.ρ1 (x.Am m) σ⁻¹ := by
          rw [inv_mul_cancel, r1.1, one_mul]
  have hok1 := (ok1 l L (T.GN N) G0 (T.h N) n x k (x.Am m) 1).1
  simp only [MonoidHom.one_apply, map_one] at hok1
  obtain ⟨rep, hrep⟩ := adEx l (T.GN N).frame x.A (DD (x.Am m) k.g) n
    (fun g => k.ρ1 (x.Am m) ((T.h N).p₀ g)) (fun _ => 1) (k.M1 (x.Am m)) hok1
  let χ' : (T.GN N).Γ →* x.A := (algebraMap ℤ_[l] x.A : ℤ_[l] →* x.A).comp
    ((Units.coeHom ℤ_[l]).comp (G0.ε.comp (T.h N).p))
  obtain ⟨rep', hrep'⟩ := adEx l (T.GN N).frame x.A (DD (x.Am m) k.g) n
    (fun g => k.ρ1 (x.Am m) ((T.h N).p₀ g)) (fun g => epsD k (x.Am m) ((T.h N).p g)) (k.EpsilonEtaTensorDual (x.Am m))
    (ok1 l L (T.GN N) G0 (T.h N) n x k (x.Am m) χ').2.1
  have hKpos : 0 < Nat.card x.K := by
    haveI := x.fin
    exact Nat.card_pos
  haveI : Finite (DD (x.Am m) k.g) := (finAm l G0.frame n x m k.g).2.2.1
  have hsum : ∑ v, A.dv v = d := by
    rw [← A.dv_eq N]
    exact (A.a N).sum_dv
  have hsurj0 : ∀ g : G0.G₀, ∃ g' : (T.GN N).G₀, (T.h N).p₀ g' = g := by
    intro g
    obtain ⟨y, hy⟩ := (T.h N).surj (g : G0.Γ)
    have hy1 : y ∈ (T.GN N).η.ker := by
      rw [MonoidHom.mem_ker, ← (T.h N).η, hy]
      exact g.2
    exact ⟨⟨y, hy1⟩, Subtype.ext hy⟩
  have hinv : ∀ j : Option (Fin T.q),
      Nat.card (Representation.invariants (rep'.comp ((A.a N).ι (Sum.inr (Sum.inr j))))) ≤
        Nat.card x.K ^ (j.elim c₀ fun i => m * n + Cq i) := by
    intro j
    cases j with
    | none =>
      refine (card_inv_le _ {Y | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ ∀ g ∈ D0, epsD k (x.Am m) ↑g •
        (k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹) = Y} ?_).trans (hc₀ m)
      intro y hy
      refine ⟨y.2, fun g hg => ?_⟩
      rw [← A.d0 N] at hg
      obtain ⟨t, rfl⟩ := hg
      have hy' : rep' ((A.a N).φq none t : (T.GN N).Γ) y = y := hy t
      have e := hrep'.1 ((A.a N).φq none t) y
      rw [hy'] at e
      beta_reduce at e
      rw [map_inv] at e
      rw [MonoidHom.comp_apply]
      exact e.symm
    | some i =>
      refine (card_inv_le _ {Y | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧
        k.ρ1 (x.Am m) (T.sg i) * Y * k.ρ1 (x.Am m) (T.sg i)⁻¹ = Y} ?_).trans (hCq i m)
      intro y hy
      refine ⟨y.2, ?_⟩
      obtain ⟨t, ht⟩ := A.ph N i
      have hy' : rep' ((A.a N).φq (some i) t : (T.GN N).Γ) y = y := hy t
      rw [ht] at hy'
      have e := hrep'.1 (T.ph N i) y
      rw [hy'] at e
      beta_reduce at e
      rw [map_inv, inv_eq _ _ (hNph i).1, (hNph i).1, (hNph i).2.1, one_smul] at e
      exact e.symm
  have h0inv : Nat.card rep.invariants ≤ Nat.card x.K ^ c₁ := by
    refine (card_inv_le rep {Y | Y ∈ k.M1 (x.Am m) ∧ Yᵀ = -Y ∧
      ∀ g : G0.G₀, k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹ = Y} ?_).trans (hc₁ m)
    intro y hy
    refine ⟨y.2, ?_, fun g => ?_⟩
    · have e := hrep.2 y
      rw [hy, one_smul] at e
      have e2 := congrArg Matrix.transpose e
      rw [Matrix.transpose_neg, Matrix.transpose_transpose] at e2
      exact e2
    · obtain ⟨g', rfl⟩ := hsurj0 g
      have e := hrep.1 g' y
      rw [hy] at e
      beta_reduce at e
      rw [one_smul, map_inv] at e
      exact e.symm
  have hdual : Finite (Zl rep') → {y | y ∈ Zl rep' ∧ ∀ j : Fin T.q,
      y ∘ ((A.a N).ι (Sum.inr (Sum.inr (some j)))) ∈
        Bl (rep'.comp ((A.a N).ι (Sum.inr (Sum.inr (some j)))))}.ncard ≤
      Nat.card (Bl rep') * Nat.card x.K ^ c₂ := by
    intro hfinZ
    refine le_trans (Set.ncard_le_ncard ?_ ?_) (hN2 rep' hrep' hfinZ)
    · intro y hy
      refine ⟨hy.1, fun j => ?_⟩
      obtain ⟨Y, hY⟩ := (mem_Bl _).1 (hy.2 j)
      obtain ⟨t1, ht1⟩ := A.ph N j
      obtain ⟨t2, ht2⟩ := A.ta N j
      refine ⟨Y, ?_, ?_⟩
      · rw [← ht1]
        exact hY t1
      · rw [← ht2]
        exact hY t2
    · exact (Set.toFinite (Zl rep' : Set _)).subset (fun y hy => hy.1)
  obtain ⟨hfin, hle⟩ := oneLevel l L (T.GN N) G0 (T.h N) n x k m T.q d (A.a N) rep rep'
    (fun v => m * (n * (d' v + 1) + nu n x.a k.g * (1 + A.dv v)) + Cv v)
    (fun j => j.elim c₀ fun i => m * n + Cq i) c₁ c₂ hl (A.counts N) hrep hrep'
    (fun v => hCv v m) hinv h0inv hdual
  rw [sum_exp m n (nu n x.a k.g) d T.q c₁ c₂ c₀ d' A.dv Cv Cq hd' hsum] at hle
  exact ⟨hfin, cancel_pow hKpos hle⟩
end

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.b1abs :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A) (d : ℕ) (D0 : Subgroup G0.G₀) (_ : ArSys T d D0) (d' : L.Vl → ℕ), l ≠ 2 → ∑ v, d' v = d → (∀ v, Nonempty (LocAb l (L.Gv v) (L.Iv v) (d' v))) → PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → x.N4 D0 → T.Eig x al → Detects k (Set.range T.sg) → T.B1 k (n * d + n * T.q) := UpperTheory.V.Pa.W1_bound_arithmetic_rank_two
