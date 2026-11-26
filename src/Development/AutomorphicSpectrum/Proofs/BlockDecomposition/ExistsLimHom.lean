module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdeal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulSubEqZeroOfSum
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

variable {l : ℕ} [Fact l.Prime]

instance neZeroPow (m : ℕ) : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

def ind (A : PAlg l) (m : ℕ) (c : ZMod (l ^ m)) : (A.cont ℤ_[l]).A :=
  ⟨fun z => if PadicInt.toZModPow m z = c then 1 else 0, fun k =>
    ((GlobalTheory.CompanionTheory.PadicShift.isLocallyConstant_toZModPow l m).comp fun a =>
      if a = c then (1 : A.A) else 0).comp (Ideal.Quotient.mk (Ideal.span {A.pi ^ k}))⟩

theorem ev_ind (A : PAlg l) (m : ℕ) (c : ZMod (l ^ m)) (z : ℤ_[l]) :
    Hom.f (A.evCont z) (ind A m c) = if PadicInt.toZModPow m z = c then 1 else 0 := rfl

theorem cont_ext {A : PAlg l} {f g : (A.cont ℤ_[l]).A}
    (h : ∀ z, Hom.f (A.evCont z) f = Hom.f (A.evCont z) g) : f = g :=
  Subtype.ext (funext h)

theorem ev_toCont (A : PAlg l) (z : ℤ_[l]) (a : A.A) :
    Hom.f (A.evCont z) (Hom.f (A.toCont ℤ_[l]) a) = a := rfl

theorem mem_span_pi_pow (A : PAlg l) (k : ℕ) (f : (A.cont ℤ_[l]).A) :
    f ∈ Ideal.span {(A.cont ℤ_[l]).pi ^ k} ↔ ∀ z, Hom.f (A.evCont z) f ∈ Ideal.span {A.pi ^ k} :=
  (RL.cont_ex A ℤ_[l]).2.2.2 k f

theorem sharp_zero (A : PAlg l) : A.sharp 0 = 0 := by
  have h : WittVector.teichmuller l (0 : A.A) = 0 := by
    ext n
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos]
  change A.th (WittVector.teichmuller l (0 : A.A)) = 0
  rw [h, map_zero]

theorem sharp_add (A : PAlg l) {e f : A.A} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : e * f = 0) : A.sharp (e + f) = A.sharp e + A.sharp f := by
  have hs : IsIdempotentElem (e + f) := by
    have h' : f * e = 0 := by rw [mul_comm, h]
    simp only [IsIdempotentElem, add_mul, mul_add, h, h', he.eq, hf.eq, add_zero, zero_add]
  have h1 := (RL.sharp_cong A).2.2 _ hs
  have h2 := (RL.sharp_cong A).2.2 _ he
  have h3 := (RL.sharp_cong A).2.2 _ hf
  have h4 : (1 - (e + f)) = (1 - e) * (1 - f) := by
    have : (1 - e) * (1 - f) = 1 - e - f + e * f := by ring
    rw [this, h]; ring
  have h5 : A.sharp e * A.sharp f = 0 := by rw [← map_mul, h, sharp_zero]
  rw [h4, map_mul, h2, h3] at h1
  have : (1 - A.sharp e) * (1 - A.sharp f) = 1 - A.sharp e - A.sharp f + A.sharp e * A.sharp f := by ring
  rw [this, h5] at h1
  have h6 : A.sharp (e + f) = 1 - (1 - A.sharp e - A.sharp f + 0) := by rw [h1]; ring
  rw [h6]; ring

theorem sharp_sum (A : PAlg l) {I : Type} (s : Finset I) (e : I → A.A)
    (hi : ∀ i ∈ s, IsIdempotentElem (e i))
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    A.sharp (∑ i ∈ s, e i) = ∑ i ∈ s, A.sharp (e i) ∧ IsIdempotentElem (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using sharp_zero A, by simp [IsIdempotentElem]⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun i h => hi i (Finset.mem_insert_of_mem h))
      (fun i h j h' => ho i (Finset.mem_insert_of_mem h) j (Finset.mem_insert_of_mem h'))
    have h3 : e a * ∑ i ∈ s, e i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i h => ho a (Finset.mem_insert_self _ _) i
        (Finset.mem_insert_of_mem h) (fun e' => ha (e' ▸ h))
    have h4 := hi a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨by rw [sharp_add A h4 h2 h3, h1], ?_⟩
    have h5 : (∑ i ∈ s, e i) * e a = 0 := by rw [mul_comm, h3]
    simp only [IsIdempotentElem, add_mul, mul_add, h3, h5, h4.eq, h2.eq, add_zero, zero_add]

theorem sum_sharp_eq_one (A : PAlg l) {I : Type} [Fintype I] {e : I → A.A}
    (h : CompleteOrthogonalIdempotents e) : ∑ i, A.sharp (e i) = 1 := by
  have := (sharp_sum A Finset.univ e (fun i _ => h.idem i) (fun i _ j _ hij => h.ortho hij)).1
  rw [← this, h.complete]
  exact (map_one A.sharp)

theorem ind_mul_ind (A : PAlg l) (m : ℕ) (c : ZMod (l ^ m)) :
    ind A m c * ind A m c = ind A m c := by
  refine cont_ext fun z => ?_
  rw [map_mul, ev_ind]
  split_ifs <;> simp

theorem ind_orth (A : PAlg l) (m : ℕ) {c c' : ZMod (l ^ m)} (h : c ≠ c') :
    ind A m c * ind A m c' = 0 := by
  refine cont_ext fun z => ?_
  rw [map_mul, ev_ind, ev_ind, map_zero]
  split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) h
  all_goals simp

theorem sum_ind (A : PAlg l) (m : ℕ) : ∑ c, ind A m c = 1 := by
  refine cont_ext fun z => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one]
  simp only [ev_ind]
  rw [Finset.sum_ite_eq]
  simp

theorem coi_ind (A : PAlg l) (m : ℕ) : CompleteOrthogonalIdempotents (ind A m) :=
  ⟨⟨ind_mul_ind A m, fun _ _ h => ind_orth A m h⟩, sum_ind A m⟩

theorem coi_map {A t : PAlg l} (ψ : A.cont ℤ_[l] ⟶ t) (m : ℕ) :
    CompleteOrthogonalIdempotents fun c => Hom.f ψ (ind A m c) :=
  (coi_ind A m).map (Hom.f ψ)

theorem contMap_ind {A A' : PAlg l} (φ : A ⟶ A') (m : ℕ) (c : ZMod (l ^ m)) :
    Hom.f (contMap φ ℤ_[l]) (ind A m c) = ind A' m c := by
  refine cont_ext fun z => ?_
  change Hom.f φ (Hom.f (A.evCont z) (ind A m c)) = _
  rw [ev_ind, ev_ind]
  split_ifs <;> simp

theorem exists_roots (A : PAlg l) (a : A.A) :
    ∃ ρ : ℕ → A.A, ρ 0 = a ∧ ∀ m, ρ (m + 1) ^ l = ρ m := by
  choose g hg using A.frob_bijective.2
  refine ⟨fun m => g^[m] a, rfl, fun m => ?_⟩
  show (g^[m + 1] a) ^ l = g^[m] a
  rw [Function.iterate_succ_apply']
  exact hg _

theorem roots_unique (A : PAlg l) {a b : ℕ → A.A} (h0 : a 0 = b 0)
    (ha : ∀ m, a (m + 1) ^ l = a m) (hb : ∀ m, b (m + 1) ^ l = b m) : a = b := by
  funext m
  induction m with
  | zero => exact h0
  | succ m ih => exact A.frob_bijective.1 ((ha m).trans (ih.trans (hb m).symm))

theorem mul_sub_eq_zero_of_sum {R I : Type} [CommRing R] [Fintype I] [DecidableEq I] {a b : I → R}
    (hi : ∀ i, a i * a i = a i) (ho : ∀ i j, i ≠ j → a i * a j = 0) {x : R}
    (hx : x = ∑ i, a i * b i) (i : I) : a i * (x - b i) = 0 := by
  rw [hx, mul_sub, Finset.mul_sum, Finset.sum_eq_single i, ← mul_assoc, hi, sub_self]
  · intro j _ hj
    rw [← mul_assoc, ho i j hj.symm, zero_mul]
  · simp

theorem eq_sum_of_mul_sub {R I : Type} [CommRing R] [Fintype I] {a b : I → R}
    (h1 : ∑ i, a i = 1) {x : R} (hx : ∀ i, a i * (x - b i) = 0) : x = ∑ i, a i * b i := by
  have : ∑ i, a i * x = ∑ i, a i * b i :=
    Finset.sum_congr rfl fun i _ => by have := hx i; rw [mul_sub, sub_eq_zero] at this; exact this
  rw [← this, ← Finset.sum_mul, h1, one_mul]

end GlobalTheory.CompanionTheory.ContUniv
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

section Lim

variable {T : Type} [CommRing T] (ϖ : T)

def Tends (x : ℕ → T) (L : T) : Prop := ∀ k, ∃ M, ∀ m, M ≤ m → x m - L ∈ Ideal.span {ϖ ^ k}

variable {ϖ}

theorem smodEq_iff {a b : T} {k : ℕ} :
    a ≡ b [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule T T)] ↔ a - b ∈ Ideal.span {ϖ ^ k} := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem Tends.unique [IsHausdorff (Ideal.span {ϖ}) T] {x : ℕ → T} {L L' : T} (h : Tends ϖ x L)
    (h' : Tends ϖ x L') : L = L' := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) T) _ fun k => ?_
  have h0 : L - L' ∈ Ideal.span {ϖ ^ k} := by
    obtain ⟨M, hM⟩ := h k
    obtain ⟨M', hM'⟩ := h' k
    have := sub_mem (hM' (max M M') (le_max_right _ _)) (hM (max M M') (le_max_left _ _))
    simpa using this
  have : L - L' ≡ 0 [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule T T)] :=
    smodEq_iff.2 (by simpa using h0)
  exact this

theorem exists_tends [IsAdicComplete (Ideal.span {ϖ}) T] (x : ℕ → T)
    (h : ∀ k, ∃ M, ∀ m, M ≤ m → x m - x M ∈ Ideal.span {ϖ ^ k}) : ∃ L, Tends ϖ x L := by
  choose M hM using h
  let N : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup M
  have hN : ∀ k, M k ≤ N k := fun k => Finset.le_sup (Finset.self_mem_range_succ k)
  have hmono : Monotone N := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hab))
  have hc : ∀ k m, N k ≤ m → x m - x (N k) ∈ Ideal.span {ϖ ^ k} := fun k m hm => by
    have := sub_mem (hM k m ((hN k).trans hm)) (hM k (N k) (hN k))
    simpa using this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) T)
    (f := fun k => x (N k)) (fun {a b} hab => smodEq_iff.2 (by
      have := hc a (N b) (hmono hab)
      rw [← neg_sub]
      exact neg_mem this))
  refine ⟨L, fun k => ⟨N k, fun m hm => ?_⟩⟩
  have := add_mem (hc k m hm) (smodEq_iff.1 (hL k))
  simpa using this

theorem Tends.add {x y : ℕ → T} {a b : T} (hx : Tends ϖ x a) (hy : Tends ϖ y b) :
    Tends ϖ (fun m => x m + y m) (a + b) := fun k => by
  obtain ⟨M, hM⟩ := hx k
  obtain ⟨M', hM'⟩ := hy k
  refine ⟨max M M', fun m hm => ?_⟩
  have := add_mem (hM m ((le_max_left _ _).trans hm)) (hM' m ((le_max_right _ _).trans hm))
  convert this using 1; ring

theorem Tends.mul {x y : ℕ → T} {a b : T} (hx : Tends ϖ x a) (hy : Tends ϖ y b) :
    Tends ϖ (fun m => x m * y m) (a * b) := fun k => by
  obtain ⟨M, hM⟩ := hx k
  obtain ⟨M', hM'⟩ := hy k
  refine ⟨max M M', fun m hm => ?_⟩
  have := add_mem (Ideal.mul_mem_right (y m) _ (hM m ((le_max_left _ _).trans hm)))
    (Ideal.mul_mem_left _ a (hM' m ((le_max_right _ _).trans hm)))
  convert this using 1; ring

theorem tends_const (a : T) : Tends ϖ (fun _ => a) a := fun k => ⟨0, fun _ _ => by simp⟩

theorem exists_lim_hom {S : Type} [CommRing S] [IsAdicComplete (Ideal.span {ϖ}) T] (a : ℕ → S →+* T)
    (h : ∀ f k, ∃ M, ∀ m, M ≤ m → a m f - a M f ∈ Ideal.span {ϖ ^ k}) :
    ∃ ψ : S →+* T, ∀ f, Tends ϖ (fun m => a m f) (ψ f) := by
  choose L hL using fun f => exists_tends (ϖ := ϖ) (fun m => a m f) (h f)
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hL⟩
  · exact (hL 1).unique (by simpa using tends_const (ϖ := ϖ) (1 : T))
  · intro f g
    exact (hL (f * g)).unique (by simpa using (hL f).mul (hL g))
  · exact (hL 0).unique (by simpa using tends_const (ϖ := ϖ) (0 : T))
  · intro f g
    exact (hL (f + g)).unique (by simpa using (hL f).add (hL g))

end Lim

variable {l : ℕ} [Fact l.Prime]

theorem exists_period (A : PAlg l) (f : (A.cont ℤ_[l]).A) (k : ℕ) :
    ∃ M : ℕ, ∀ z z' : ℤ_[l], PadicInt.toZModPow M z = PadicInt.toZModPow M z' →
      Hom.f (A.evCont z) f - Hom.f (A.evCont z') f ∈ Ideal.span {A.pi ^ k} := by
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.PadicShift.exists_period l _ (f.2 k)
  refine ⟨M, fun z z' h => Ideal.Quotient.eq.1 (hM z z' ?_)⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]

end GlobalTheory.CompanionTheory.ContUniv
