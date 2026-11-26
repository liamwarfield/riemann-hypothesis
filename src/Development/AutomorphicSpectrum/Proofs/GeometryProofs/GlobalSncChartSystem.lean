module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteExtensionPrimes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSpecializes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreOpenCoords
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelBoundaryCoords
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGenerators

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFramesAwayPrime
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFramesAwayPrime
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.DeltaLine

open GlobalTheory.CompanionTheory.Ar.FlagBun.Twist

section Basic

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem ua_one (q : Cpt ξ) : unitAt ξ q 1 :=
  ⟨one_ne_zero, one_mem _, by simpa using one_mem (regAt ξ q)⟩

theorem ua_mul {q : Cpt ξ} {a b : Ω} (ha : unitAt ξ q a) (hb : unitAt ξ q b) : unitAt ξ q (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem ua_inv {q : Cpt ξ} {a : Ω} (ha : unitAt ξ q a) : unitAt ξ q a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem ua_pow {q : Cpt ξ} {a : Ω} (ha : unitAt ξ q a) (n : ℕ) : unitAt ξ q (a ^ n) := by
  induction n with
  | zero => simpa using ua_one q
  | succ n ih => rw [pow_succ]; exact ua_mul ih ha

theorem ua_prod {A : Type} (s : Finset A) {f : A → Ω} {q : Cpt ξ} (h : ∀ i ∈ s, unitAt ξ q (f i)) :
    unitAt ξ q (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ua_one q
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact ua_mul (h _ (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem reg_of_mul {q : Cpt ξ} {u g : Ω} (hu : unitAt ξ q u) (h : u * g ∈ regAt ξ q) : g ∈ regAt ξ q := by
  have e : g = u⁻¹ * (u * g) := by rw [inv_mul_cancel_left₀ hu.1]
  rw [e]
  exact mul_mem hu.2.2 h

theorem det_mem {r : ℕ} (R : Subring Ω) (A : Matrix (Fin r) (Fin r) Ω) (h : ∀ i j, A i j ∈ R) : A.det ∈ R := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem comb_comb {r : ℕ} (v : Fin r → E) (M N : Matrix (Fin r) (Fin r) Ω) (k : Fin r) :
    ∑ j, N j k • ∑ l, M l j • v l = ∑ l, (M * N) l k • v l := by
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

theorem mat_ext {r : ℕ} {v : Fin r → E} (hv : LinearIndependent Ω v) {M N : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, ∑ l, M l k • v l = ∑ l, N l k • v l) : M = N := by
  ext i k
  have := Fintype.linearIndependent_iff.1 hv (fun l => M l k - N l k)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h k, sub_self]) i
  exact sub_eq_zero.1 this

theorem exists_reg_change {L : Lat ξ E} {r : ℕ} {b c : Fin r → E} {q : Cpt ξ} (hb : L.IsFrameAt b q)
    (hc : L.IsFrameAt c q) :
    ∃ A : Matrix (Fin r) (Fin r) Ω, (∀ i j, A i j ∈ regAt ξ q) ∧ ∀ k, c k = ∑ k', A k' k • b k' := by
  have h : ∀ k, ∃ f : Fin r → regAt ξ q, ∑ k', f k' • b k' = c k := fun k => by
    have hk : c k ∈ L q := by
      rw [hc.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [hb.2] at hk
    exact (Submodule.mem_span_range_iff_exists_fun _).1 hk
  choose f hf using h
  exact ⟨Matrix.of fun k' k => (f k k' : Ω), fun i j => (f j i).2, fun k => by rw [← hf k]; rfl⟩

theorem det_unit {L : Lat ξ E} {r : ℕ} {b c : Fin r → E} {q : Cpt ξ} (hb : L.IsFrameAt b q)
    (hc : L.IsFrameAt c q) {A : Matrix (Fin r) (Fin r) Ω} (hA : ∀ k, c k = ∑ k', A k' k • b k') :
    unitAt ξ q A.det := by
  obtain ⟨A', hA'r, hA'⟩ := exists_reg_change hb hc
  obtain ⟨B, hBr, hB⟩ := exists_reg_change hc hb
  have e : A = A' := mat_ext hb.1 fun k => by rw [← hA, ← hA']
  have h1 : A * B = 1 := mat_ext hb.1 fun k => by
    rw [← comb_comb b A B k]
    simp only [← hA]
    rw [← hB k]
    simp [Matrix.one_apply]
  have h2 : A.det * B.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
  refine ⟨left_ne_zero_of_mul_eq_one h2, det_mem _ _ (e ▸ hA'r), ?_⟩
  rw [← eq_inv_of_mul_eq_one_right h2]
  exact det_mem _ _ hBr

theorem det_ratio {L M : Lat ξ E} {r : ℕ} {b b₂ c c₂ : Fin r → E} {q : Cpt ξ} {T T₂ : Matrix (Fin r) (Fin r) Ω}
    (hb : L.IsFrameAt b q) (hb₂ : L.IsFrameAt b₂ q) (hc : M.IsFrameAt c q) (hc₂ : M.IsFrameAt c₂ q)
    (hT : ∀ k, c k = ∑ k', T k' k • b k') (hT₂ : ∀ k, c₂ k = ∑ k', T₂ k' k • b₂ k') :
    ∃ u, unitAt ξ q u ∧ T₂.det = u * T.det := by
  obtain ⟨A, -, hA⟩ := exists_reg_change hb hb₂
  obtain ⟨B, -, hB⟩ := exists_reg_change hc hc₂
  have uA := det_unit hb hb₂ hA
  have uB := det_unit hc hc₂ hB
  have e : T * B = A * T₂ := mat_ext hb.1 fun k => by
    rw [← comb_comb b T B k, ← comb_comb b A T₂ k]
    simp only [← hT, ← hA]
    rw [← hB k, ← hT₂ k]
  refine ⟨B.det * A.det⁻¹, ua_mul uB (ua_inv uA), ?_⟩
  have h := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul] at h
  apply mul_left_cancel₀ uA.1
  rw [← h]
  field_simp [uA.1]

def deltaLat (ξ : Spec (CommRingCat.of Ω) ⟶ X) {Li : Type} [AddCommGroup Li] [Module Ω Li] {I : Type} [Fintype I]
    (r : I → ℕ) (V W : I → Lat ξ Li) (p : ℕ) : Lat ξ Ω := fun q =>
  open Classical in
  if InFibre ξ p q then
    Submodule.span (regAt ξ q) {t | ∃ (b b' : ∀ i, Fin (r i) → Li) (T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω),
      (∀ i, (V i).IsFrameAt (b i) q) ∧ (∀ i, (W i).IsFrameAt (b' i) q) ∧
        (∀ i k, b' i k = ∑ k', T i k' k • b i k') ∧ t = ∏ i, (T i).det}
  else Submodule.span (regAt ξ q) {1}

variable {Li : Type} [AddCommGroup Li] [Module Ω Li] {I : Type} [Fintype I] {r : I → ℕ} {V W : I → Lat ξ Li} {p : ℕ}

theorem deltaLat_off {q : Cpt ξ} (hq : ¬ InFibre ξ p q) :
    deltaLat ξ r V W p q = Submodule.span (regAt ξ q) {1} := by
  simp only [deltaLat, if_neg hq]

theorem deltaLat_fibre {q : Cpt ξ} (hq : InFibre ξ p q) {b b' : ∀ i, Fin (r i) → Li}
    {T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω} (hb : ∀ i, (V i).IsFrameAt (b i) q)
    (hb' : ∀ i, (W i).IsFrameAt (b' i) q) (hT : ∀ i k, b' i k = ∑ k', T i k' k • b i k') :
    deltaLat ξ r V W p q = Submodule.span (regAt ξ q) {∏ i, (T i).det} := by
  simp only [deltaLat, if_pos hq]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨b₂, b₂', T₂, h1, h2, h3, rfl⟩
    choose u hu e using fun i => det_ratio (hb i) (h1 i) (hb' i) (h2 i) (hT i) (h3 i)
    have hU : unitAt ξ q (∏ i, u i) := ua_prod _ fun i _ => hu i
    refine SetLike.mem_coe.2 (Submodule.mem_span_singleton.2 ⟨⟨_, hU.2.1⟩, ?_⟩)
    show (∏ i, u i) * _ = _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (e i).symm
  · exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨b, b', T, hb, hb', hT, rfl⟩)

theorem frame_gen {L : Lat ξ Ω} {t : Ω} {q : Cpt ξ} (h0 : t ≠ 0) (h : L q = Submodule.span (regAt ξ q) {t}) :
    L.IsFrameAt (fun _ : Fin 1 => t) q := by
  refine ⟨linearIndependent_unique_iff.2 h0, ?_⟩
  rw [h, Set.range_const]

theorem span_const {t : Ω} (h0 : t ≠ 0) : Submodule.span Ω (Set.range fun _ : Fin 1 => t) = ⊤ := by
  rw [Set.range_const, eq_top_iff]
  intro a _
  exact Submodule.mem_span_singleton.2 ⟨a / t, by simp [h0]⟩

theorem span_one_eq {t : Ω} {q : Cpt ξ} (h : unitAt ξ q t) :
    Submodule.span (regAt ξ q) {(1 : Ω)} = Submodule.span (regAt ξ q) {t} := by
  apply le_antisymm
  · refine Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)
    refine SetLike.mem_coe.2 (Submodule.mem_span_singleton.2 ⟨⟨_, h.2.2⟩, ?_⟩)
    show t⁻¹ * t = 1
    exact inv_mul_cancel₀ h.1
  · refine Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)
    refine SetLike.mem_coe.2 (Submodule.mem_span_singleton.2 ⟨⟨_, h.2.1⟩, ?_⟩)
    show t * 1 = t
    exact mul_one t

theorem exists_open_le {I : Type} [Finite I] (U : I → X.Opens) {y : X} (h : ∀ i, y ∈ U i) :
    ∃ W : X.Opens, y ∈ W ∧ ∀ i, W ≤ U i :=
  ⟨⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, Set.mem_iInter.2 h,
    fun i _ hz => Set.mem_iInter.1 hz i⟩

theorem exists_den {κ : Type} {x : κ → Ω} (h : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (s : chartR x c) (g : Ω)
    (hg : ∀ q : Cpt ξ, InChart ξ x c q → Char0 ξ q → unitAt ξ q (s : Ω) → g ∈ regAt ξ q) :
    ∃ m N : ℕ, 0 < m ∧ (m : Ω) * (s : Ω) ^ N * g ∈ chartR x c := by
  let J : Ideal (chartR x c) :=
    { carrier := {d | (d : Ω) * g ∈ chartR x c}
      add_mem' := by
        rintro d d' hd hd'
        have e : ((d + d' : chartR x c) : Ω) * g = (d : Ω) * g + (d' : Ω) * g := by
          push_cast
          ring
        show ((d + d' : chartR x c) : Ω) * g ∈ chartR x c
        rw [e]
        exact add_mem hd hd'
      zero_mem' := by
        show ((0 : chartR x c) : Ω) * g ∈ chartR x c
        simp
      smul_mem' := by
        rintro t d hd
        have e : ((t • d : chartR x c) : Ω) * g = (t : Ω) * ((d : Ω) * g) := by
          rw [smul_eq_mul]
          push_cast
          ring
        show ((t • d : chartR x c) : Ω) * g ∈ chartR x c
        rw [e]
        exact mul_mem t.2 hd }
  let S : Submonoid (chartR x c) :=
    { carrier := {y | ∃ m N : ℕ, 0 < m ∧ y = (m : chartR x c) * s ^ N}
      mul_mem' := by
        rintro _ _ ⟨m, N, hm, rfl⟩ ⟨m', N', hm', rfl⟩
        exact ⟨m * m', N + N', Nat.mul_pos hm hm', by push_cast; ring⟩
      one_mem' := ⟨1, 0, one_pos, by simp⟩ }
  by_contra hn
  have hd : Disjoint (J : Set (chartR x c)) (S : Set (chartR x c)) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨m, N, hm, rfl⟩
    refine hn ⟨m, N, hm, ?_⟩
    have hy' : (((m : chartR x c) * s ^ N : chartR x c) : Ω) * g ∈ chartR x c := hy
    simpa using hy'
  obtain ⟨Q, hQ, hJQ, hQS⟩ := Ideal.exists_le_prime_disjoint J S hd
  obtain ⟨q, hqc, f1, f2⟩ := chart_prime h hc Q hQ
  have hmem : ∀ y ∈ S, unitAt ξ q (y : Ω) := fun y hy => by
    by_contra hu
    exact Set.disjoint_left.1 hQS ((f1 y).2 hu) hy
  have hch : Char0 ξ q := fun l hl hf => hf (by simpa using hmem (l : chartR x c) ⟨l, 0, hl.pos, by simp⟩)
  have hs : unitAt ξ q (s : Ω) := hmem s ⟨1, 1, one_pos, by simp⟩
  obtain ⟨u, v, hv, e⟩ := f2 g (hg q hqc hch hs)
  apply hv
  apply hJQ
  show (v : Ω) * g ∈ chartR x c
  rw [mul_comm, e]
  exact u.2

end Basic

section Line

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li] {I : Type} [Fintype I] {r : I → ℕ} {V W : I → Lat ξ Li} {p : ℕ}

theorem isVB_at_fibre {κ : Type} {x : κ → Ω} {Vg : I → Submodule Ω Li} (hT : CoordTie ℤ ξ x) (hp : p.Prime)
    (hV : ∀ i, (V i).IsVB (r i) (Vg i))
    (hW : ∀ i, (W i).IsVBOn {q | ∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q} (r i) (Vg i))
    (hVW : ∀ i (q : Cpt ξ), Char0 ξ q → W i q = V i q) {q₀ : Cpt ξ} (hq₀ : InFibre ξ p q₀) :
    ∃ U : X.Opens, q₀.1 ∈ U ∧ ∃ b : Fin 1 → Ω, Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ q ∈ (Set.univ : Set (Cpt ξ)), q.1 ∈ U → (deltaLat ξ r V W p).IsFrameAt b q := by
  have hTp : ∀ q : Cpt ξ, InFibre ξ p q → ∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q := fun q hq l hl hne =>
    Lat.not_inFibre_of_coprime q ((Nat.coprime_primes hp hl).2 hne.symm) hq
  choose U hU b hbs hb using fun i => hV i q₀ (Set.mem_univ _)
  choose U' hU' b' hbs' hb' using fun i => hW i q₀ (hTp q₀ hq₀)
  obtain ⟨U₁, hU₁, hle⟩ := exists_open_le (fun i : I ⊕ I => Sum.elim U U' i) (y := q₀.1)
    (by rintro (i | i); exacts [hU i, hU' i])
  have hbq : ∀ i (q : Cpt ξ), q.1 ∈ U₁ → (V i).IsFrameAt (b i) q :=
    fun i q hq => hb i q (Set.mem_univ _) (hle (Sum.inl i) hq)
  have hbq' : ∀ i (q : Cpt ξ), q.1 ∈ U₁ → (∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q) →
      (W i).IsFrameAt (b' i) q := fun i q hq ht => hb' i q ht (hle (Sum.inr i) hq)
  have hex : ∀ i k, ∃ f : Fin (r i) → Ω, ∑ k', f k' • b i k' = b' i k := fun i k => by
    have h : b' i k ∈ Submodule.span Ω (Set.range (b i)) := by
      rw [hbs i, ← hbs' i]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun _).1 h
  choose f hf using hex
  let T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω := fun i => Matrix.of fun k' k => f i k k'
  have hTm : ∀ i k, b' i k = ∑ k', T i k' k • b i k' := fun i k => (hf i k).symm
  obtain ⟨t, ht⟩ : ∃ t : Ω, t = ∏ i, (T i).det := ⟨_, rfl⟩
  have hunit : ∀ q : Cpt ξ, Char0 ξ q → q.1 ∈ U₁ → unitAt ξ q t := fun q hc hq => by
    rw [ht]
    refine ua_prod _ fun i _ => ?_
    have h1 := hbq i q hq
    have h2 := hbq' i q hq fun l hl _ => hc l hl
    exact det_unit h1 ⟨h2.1, by rw [← hVW i q hc]; exact h2.2⟩ (hTm i)
  have ht0 : t ≠ 0 := by
    let g : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
    have hg : Char0 ξ g := fun l hl hf =>
      hf ⟨Nat.cast_ne_zero.2 hl.ne_zero, regAt_gen hT.gen _, regAt_gen hT.gen _⟩
    exact (hunit g hg (q₀.2.mem_open U₁.isOpen hU₁)).1
  obtain ⟨c, hc⟩ := hT.cover q₀
  obtain ⟨s, hs, hsU⟩ := chart_nbhd hT hc.1 q₀ hc U₁ hU₁
  obtain ⟨m₁, N₁, hm₁, e₁⟩ := exists_den hT hc.1 s t
    fun q hq hch hu => (hunit q hch (hsU q hq hu)).2.1
  obtain ⟨m₂, N₂, hm₂, e₂⟩ := exists_den hT hc.1 s t⁻¹
    fun q hq hch hu => (hunit q hch (hsU q hq hu)).2.2
  obtain ⟨a, m, hnd, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.mul_pos hm₁ hm₂).ne' p hp.ne_one
  have hmu : unitAt ξ q₀ (m : Ω) :=
    not_not.1 (Lat.not_inFibre_of_coprime q₀ ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd) hq₀)
  obtain ⟨U₂, hU₂, hmU⟩ := (regAt_unitAt_open X Ω ξ q₀ (m : Ω)).2 hmu
  obtain ⟨U₃, hU₃, hsU₃⟩ := (regAt_unitAt_open X Ω ξ q₀ (s : Ω)).2 hs
  obtain ⟨C, -, hC⟩ := hT.affine c hc.1
  have hq₀C : q₀.1 ∈ C := (hC _).2 ⟨q₀.2, hc⟩
  refine ⟨C ⊓ U₂ ⊓ U₃, ⟨⟨hq₀C, hU₂⟩, hU₃⟩, fun _ => t, span_const ht0, fun q _ hq => frame_gen ht0 ?_⟩
  obtain ⟨⟨hqC, hqm⟩, hqs⟩ := hq
  obtain ⟨_, hqc⟩ := (hC q.1).1 hqC
  have hqs' := hsU₃ q hqs
  have hqU := hsU q hqc hqs'
  by_cases hqF : InFibre ξ p q
  · rw [ht]
    exact deltaLat_fibre hqF (fun i => hbq i q hqU) (fun i => hbq' i q hqU (hTp q hqF)) hTm
  · rw [deltaLat_off hqF]
    have hpu : unitAt ξ q (p : Ω) := not_not.1 hqF
    have hnu : unitAt ξ q ((m₁ * m₂ : ℕ) : Ω) := by
      rw [hn]
      push_cast
      exact ua_mul (ua_pow hpu a) (hmU q hqm)
    have r1 : t ∈ regAt ξ q := reg_of_mul (ua_mul hnu (ua_pow hqs' N₁)) (by
      have h := mul_mem (natCast_mem (regAt ξ q) m₂) (chartR_le hT hc.1 e₁ hqc)
      convert h using 1
      push_cast
      ring)
    have r2 : t⁻¹ ∈ regAt ξ q := reg_of_mul (ua_mul hnu (ua_pow hqs' N₂)) (by
      have h := mul_mem (natCast_mem (regAt ξ q) m₁) (chartR_le hT hc.1 e₂ hqc)
      convert h using 1
      push_cast
      ring)
    exact span_one_eq ⟨ht0, r1, r2⟩

end Line

theorem exists_delta : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (I : Type) [Fintype I] (r : I → ℕ) (Vg : I → Submodule Ω Li) (V W : I → Lat ξ Li) (p : ℕ), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → p.Prime → (∀ i, (V i).IsVB (r i) (Vg i)) → (∀ i, (W i).IsVBOn {q | ∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q} (r i) (Vg i)) → (∀ i (q : Cpt ξ), Char0 ξ q → W i q = V i q) → ∃ Δ : Lat ξ Ω, Δ.IsVB 1 ⊤ ∧ (∀ q, ¬ InFibre ξ p q → Δ q = Submodule.span (regAt ξ q) {1}) ∧ ∀ q, InFibre ξ p q → ∀ (b b' : ∀ i, Fin (r i) → Li) (T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω), (∀ i, (V i).IsFrameAt (b i) q) → (∀ i, (W i).IsFrameAt (b' i) q) → (∀ i k, b' i k = ∑ k', T i k' k • b i k') → Δ q = Submodule.span (regAt ξ q) {∏ i, (T i).det} := by
  intro X Ω _ _ ξ κ _ x Li _ _ I _ r Vg V W p hT _ hp hV hW hVW
  refine ⟨deltaLat ξ r V W p, ?_, fun q hq => deltaLat_off hq,
    fun q hq b b' T hb hb' hT' => deltaLat_fibre hq hb hb' hT'⟩
  intro q₀ _
  by_cases hq₀ : InFibre ξ p q₀
  · exact isVB_at_fibre hT hp hV hW hVW hq₀
  · obtain ⟨U, hU, h⟩ := (regAt_unitAt_open X Ω ξ q₀ (p : Ω)).2 (not_not.1 hq₀)
    exact ⟨U, hU, fun _ => 1, span_const one_ne_zero, fun q _ hqU =>
      frame_gen one_ne_zero (deltaLat_off (not_not.2 (h q hqU)))⟩

end GlobalTheory.CompanionTheory.Ar.GeoModel.DeltaLine
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFramesAwayPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frames_away_prime : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (I : Type) [Fintype I] (r : I → ℕ) (Vg : I → Submodule Ω Li) (V W : I → Lat ξ Li) (p : ℕ), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → p.Prime → (∀ i, (V i).IsVB (r i) (Vg i)) → (∀ i, (W i).IsVBOn {q | ∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q} (r i) (Vg i)) → (∀ i (q : Cpt ξ), Char0 ξ q → W i q = V i q) → ∃ Δ : Lat ξ Ω, Δ.IsVB 1 ⊤ ∧ (∀ q, ¬ InFibre ξ p q → Δ q = Submodule.span (regAt ξ q) {1}) ∧ ∀ q, InFibre ξ p q → ∀ (b b' : ∀ i, Fin (r i) → Li) (T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω), (∀ i, (V i).IsFrameAt (b i) q) → (∀ i, (W i).IsFrameAt (b' i) q) → (∀ i k, b' i k = ∑ k', T i k' k • b i k') → Δ q = Submodule.span (regAt ξ q) {∏ i, (T i).det} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoModel.DeltaLine.exists_delta | exact GlobalTheory.CompanionTheory.Ar.GeoModel.DeltaLine.exists_delta | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoModel.DeltaLine.exists_delta <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeLineBundle
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeLineBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.DetLine

theorem matrix_eq_mul {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b₀ c b : Fin r → E}
    {T T' A : Matrix (Fin r) (Fin r) Ω} (hb₀ : LinearIndependent Ω b₀)
    (hT : ∀ k, c k = ∑ k', T k' k • b₀ k') (hT' : ∀ k, b k = ∑ k', T' k' k • b₀ k')
    (hA : ∀ k, b k = ∑ i, A i k • c i) : T' = T * A := by
  ext i k
  have h : ∑ k', (T' k' k - (T * A) k' k) • b₀ k' = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul, ← hT']
    rw [sub_eq_zero, hA k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, _root_.mul_comm]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb₀ _ h i)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem det_mem_span (L : Lat ξ E) {r : ℕ} {b₀ c b : Fin r → E} {q : Cpt ξ} {T T' : Matrix (Fin r) (Fin r) Ω}
    (hb₀ : LinearIndependent Ω b₀) (hc : L.IsFrameAt c q) (hb : L.IsFrameAt b q)
    (hT : ∀ k, c k = ∑ k', T k' k • b₀ k') (hT' : ∀ k, b k = ∑ k', T' k' k • b₀ k') :
    T'.det ∈ Submodule.span (regAt ξ q) {T.det} := by
  have hmem : ∀ k, b k ∈ Submodule.span (regAt ξ q) (Set.range c) := fun k => by
    rw [← hc.2, hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun k => (Submodule.mem_span_range_iff_exists_fun (regAt ξ q)).1 (hmem k)
  let M : Matrix (Fin r) (Fin r) (regAt ξ q) := Matrix.of fun i k => a k i
  have hM : T' = T * (regAt ξ q).subtype.mapMatrix M :=
    matrix_eq_mul hb₀ hT hT' fun k => (ha k).symm
  refine Submodule.mem_span_singleton.2 ⟨M.det, ?_⟩
  rw [hM, Matrix.det_mul, ← RingHom.map_det, _root_.mul_comm]
  rfl

theorem isVB_detLat : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E]
    (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ →
    Submodule.span Ω (Set.range b₀) = V → L.IsVB r V → (Cusp.detLat L b₀).IsVB 1 ⊤ := by
  intro X Ω _ ξ E _ _ L r V b₀ hb₀ hsp hL p _
  obtain ⟨U, hU, c, hc, hf⟩ := hL p trivial
  have hcV : ∀ k, c k ∈ Submodule.span Ω (Set.range b₀) := fun k => by
    rw [hsp, ← hc]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hbV : ∀ k, b₀ k ∈ Submodule.span Ω (Set.range c) := fun k => by
    rw [hc, ← hsp]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hcV k)
  choose s hs using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hbV k)
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun i k => a k i
  let S : Matrix (Fin r) (Fin r) Ω := Matrix.of fun i k => s k i
  have hT : ∀ k, c k = ∑ k', T k' k • b₀ k' := fun k => (ha k).symm
  have hTS : (1 : Matrix (Fin r) (Fin r) Ω) = T * S :=
    matrix_eq_mul hb₀ hT (fun k => by simp [Matrix.one_apply, ite_smul]) fun k => (hs k).symm
  have ht : T.det ≠ 0 := fun h => by
    have := congrArg Matrix.det hTS
    rw [Matrix.det_one, Matrix.det_mul, h, zero_mul] at this
    exact one_ne_zero this
  refine ⟨U, hU, fun _ => T.det, ?_, fun q _ hq => ⟨?_, ?_⟩⟩
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : x = (x * T.det⁻¹) • T.det := by
      rw [smul_eq_mul, _root_.mul_assoc, inv_mul_cancel₀ ht, _root_.mul_one]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · exact linearIndependent_unique_iff.2 ht
  · have hr : Set.range (fun _ : Fin 1 => T.det) = {T.det} := Set.range_const
    rw [hr]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨b, T', hfr, hT', rfl⟩
      exact det_mem_span L hb₀ (hf q trivial hq) hfr hT hT'
    · rintro _ rfl
      exact ⟨c, T, hf q trivial hq, hT, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.DetLine
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeLineBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_lattice_line_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ → Submodule.span Ω (Set.range b₀) = V → L.IsVB r V → (Cusp.detLat L b₀).IsVB 1 ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.DetLine.isVB_detLat | exact GlobalTheory.CompanionTheory.Ar.Cusp.DetLine.isVB_detLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.DetLine.isVB_detLat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalSncChartSystem
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.GeoModel

theorem exists_patches_of_res (hRes : ResK.ResKStatement)
    (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (hp : IsProjOver s)
    (hn : Tor.IsNormalScheme P) (U : (pullback s (spMap (algebraMap (𝓞 F) F))).Opens) (hd : Dense (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))) (e : ℕ)
    (hU : SmoothOfRelativeDimension e (U.ι ≫ pullback.snd s (spMap (algebraMap (𝓞 F) F))))
    (Ab : Set P) (hAb : pullback.fst s (spMap (algebraMap (𝓞 F) F)) ⁻¹' Ab = U)
    (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P) (hξ₀ : IsCptGen ξ₀) :
    ∃ (N : ℕ) (x : Fin (N + 1) → Ω) (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (f : X ⟶ P),
      (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ x ∧ ξ ≫ f = ξ₀ ∧
      SncPts ξ e {p | Char0 ξ p ∧ f p.1 ∉ Ab} := by
  obtain ⟨hred, hln, M, i, hi, his⟩ := GlobalTheory.T.generic_fibre_projective_embedding F P s hp hn
  obtain ⟨b, ξF, hF1, hF2, hFg⟩ := GlobalTheory.T.generic_point_generic_fibre F P s Ω ξ₀ hξ₀
  have hmem := GlobalTheory.T.generic_point_mem_dense_open _ Ω ξF U hFg hd
  have hin : ResK.IsResInput M i U e := ⟨hi, hred, hd, by rw [his]; exact hU⟩
  obtain ⟨r, X', j, f', hj, hfj, hsm, hiso, hdense, hsnc⟩ := hRes F M e _ i U hin
  let algF : Algebra F Ω := b.toAlgebra
  let algO : Algebra (𝓞 F) Ω := (b.comp (algebraMap (𝓞 F) F)).toAlgebra
  have : IsScalarTower (𝓞 F) F Ω := .of_algebraMap_eq' rfl
  have hs0 : ξ₀ ≫ s = spMap (algebraMap (𝓞 F) Ω) := by
    rw [← hF1, Category.assoc, pullback.condition, ← Category.assoc, hF2]
    show _ = Spec.map (CommRingCat.ofHom (b.comp (algebraMap (𝓞 F) F)))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨nu, u, hu⟩ := GlobalTheory.T.projective_over_coords_exist (𝓞 F) P s hp Ω ξ₀ hξ₀ hs0
  have hproj : IsProjOver (f' ≫ i ≫ PSpace.str F M) := by
    have := GlobalTheory.T.closed_in_product_projective F M r X' j hj
    rwa [← Category.assoc, ← hfj, Category.assoc] at this
  have hdom := GlobalTheory.T.smooth_scheme_stalks_domains F e X' _ hsm
  obtain ⟨ξ', h1, hξ'⟩ := GlobalTheory.T.generic_point_lift_along_iso _ X' f' U Ω ξF hiso hmem hFg hdom
  have hξs : ξ' ≫ f' ≫ i ≫ PSpace.str F M = spMap (algebraMap F Ω) := by
    rw [← Category.assoc, h1, his, hF2]
  obtain ⟨nx, x2, hx2⟩ := GlobalTheory.T.projective_over_coords_exist F X' _ hproj Ω ξ' hξ' hξs
  have hg : ξ' ≫ (f' ≫ pullback.fst _ _) = ξ₀ := by rw [← Category.assoc, h1, hF1]
  have hbase := GlobalTheory.T.every_component_in_some_chart X' P Ω ξ' ξ₀ _ (𝓞 F) _ u hu hg
  obtain ⟨n, ht⟩ := GlobalTheory.T.coords_product_refinement X' Ω ξ' F _ _ x2 u hx2 hbase
  obtain ⟨c₀, hc₀, hfrac⟩ := GlobalTheory.T.coords_generate_function_field (𝓞 F) F Ω X' ξ' _ _ ht
  obtain ⟨X, ξ, sX, htX, hirr, -, -, -⟩ := GlobalTheory.T.exists_proper_integral_model Ω (𝓞 F) _ _ c₀ hc₀ hfrac
  have hreg : ∀ (a : 𝓞 F) (p : Cpt ξ), (RingHom.id Ω) (algebraMap (𝓞 F) Ω a) ∈ regAt ξ p := by
    intro a p
    obtain ⟨c, hc⟩ := htX.cover p
    exact (htX.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p hc
  have hchart : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun k => (RingHom.id Ω) (u k)) c p := by
    intro p
    obtain ⟨⟨q1, q2, q3⟩, h0, hc⟩ := htX.cover p
    have hne := h0
    simp only [mul_ne_zero_iff] at hne
    refine ⟨q3, hne.2, fun c' => ?_⟩
    have := hc ⟨q1, q2, c'⟩
    have e1 : ((∏ a, x2 (q1 a)) * x2 q2 * u c') / ((∏ a, x2 (q1 a)) * x2 q2 * u q3) = u c' / u q3 := by
      field_simp [hne.1.1, hne.1.2, hne.2]
    simpa [e1] using this
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.dominates_of_coords_regular P Ω ξ₀ (𝓞 F) _ u X Ω ξ (RingHom.id Ω) hu htX.gen hirr hreg hchart
  have hf' : ξ ≫ f = ξ₀ := by
    have : ξ ≫ f = _ := hf
    rw [this]; simp
  obtain ⟨N, x, hx⟩ := GlobalTheory.T.coord_over_int_of_finite_order X Ω ξ (𝓞 F) _ _ htX
  obtain ⟨R1, R2⟩ := GlobalTheory.T.coord_charts_match_regular (𝓞 F) F Ω X X' ξ ξ' _ _ htX ht
  have hchar := GlobalTheory.T.char_zero_iff_nonzero_units F Ω X ξ _ _ htX
  have hFreg : ∀ (a : F) (p' : Cpt ξ'), algebraMap F Ω a ∈ regAt ξ' p' := by
    intro a p'
    obtain ⟨c, hc⟩ := ht.cover p'
    exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p' hc
  have hunit : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → Char0 ξ p := by
    intro p p' h
    refine (hchar p).2 fun d hd0 => ?_
    have hd1 : (algebraMap (𝓞 F) F d) ≠ 0 := by simpa using hd0
    have e1 : algebraMap (𝓞 F) Ω d = algebraMap F Ω (algebraMap (𝓞 F) F d) := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; exact (map_ne_zero _).2 hd1
    · rw [h, e1]; exact hFreg _ p'
    · rw [h, e1, ← map_inv₀]; exact hFreg _ p'
  have hPts : Pts ξ = Set.range (regAt ξ') := by
    ext R
    constructor
    · rintro ⟨p, hp0, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', h.symm⟩
    · rintro ⟨p', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, hunit p p' h, h.symm⟩
  let B : Set (Cpt ξ) := {p | Char0 ξ p ∧ f p.1 ∉ Ab}
  let T : Set X' := f'.base ⁻¹' (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))ᶜ
  have hgen : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → (f p.1 ∉ Ab ↔ p'.1 ∈ T) := by
    intro p p' h
    have e1 : f p.1 = (f' ≫ pullback.fst _ _) p'.1 :=
      GlobalTheory.T.regular_rings_equal_images_equal P X X' Ω ξ₀ ξ ξ' f _ (𝓞 F) _ u hu htX.gen hξ' hf' hg p p' h
    have e2 : ((f' ≫ pullback.fst s (spMap (algebraMap (𝓞 F) F))) p'.1 ∈ Ab) ↔ f' p'.1 ∈ (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0}))) := by
      rw [← hAb]; simp
    rw [e1, e2]; rfl
  have hBd : regAt ξ '' B = regAt ξ' '' {p | p.1 ∈ T} := by
    ext R
    constructor
    · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', (hgen p p' h).1 hp1, h.symm⟩
    · rintro ⟨p', hp', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, ⟨hunit p p' h, (hgen p p' h).2 hp'⟩, h⟩
  have hpatch := GlobalTheory.T.snc_patch_at_each_component F X' _ e T Ω ξ' hξ' hξs hsm hsnc (GlobalTheory.T.regular_ring_determines_component X' Ω ξ' F _ _ ht)
  refine ⟨N, x, X, ξ, f, hirr, hx, hf', fun p hp0 => ?_⟩
  obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
  show ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
    IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)
  rw [hPts, hBd, h]
  exact hpatch p'

theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

theorem exists_cst {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {Ω : Type} [Field Ω] (y₀ : Sp Ω ⟶ Xo.XF c) :
    ∃ cst : c.F →+* Ω, y₀ ≫ Y.j ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
  refine ⟨(Spec.preimage (y₀ ≫ pullback.snd _ _)).hom, ?_⟩
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc]
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem exists_base (hRes : ResK.ResKStatement) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀]
    (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (hg : IsCptGen ξ₀) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k))
      (y : (Σ k, J k) → Ω) (M₁ : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (f₁ : M₁.X ⟶ Y.X)
      (y₀ : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Nonempty K ∧ (letI := i.toAlgebra; FiniteDimensional Ω₀ Ω) ∧
      Flat.NormalCpt M₁.ξ ∧ M₁.ξ ≫ f₁ = y₀ ≫ Y.j ∧ M₁.ξ ≫ f₁ = spMap i ≫ ξ₀ ∧
      (∀ p ∈ S, FullTorsion Y.t.G (M₁.ξ ≫ f₁) (p ^ 4)) ∧ (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4)) ∧
      SncPts M₁.ξ D.dim {p | Char0 M₁.ξ p ∧ p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} ∧
      Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) := by
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  have hgen₀ := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨w₀, -⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω₀ ξ₀ hgen₀
  obtain ⟨cst, -⟩ := exists_cst (Y := Y) w₀
  have : CharZero Ω₀ := charZero_of_injective_ringHom cst.injective
  obtain ⟨Ω, _, _, i, hfin, htors, hroot⟩ := GlobalTheory.T.exists_finite_extension_primes E H D l Xo c Y Ω₀ ξ₀ S hgen₀ hS
  obtain ⟨K₀, _, J₀, _, yc, X₀, ξ', f₀, bd₀, -, hall₀, htie₀, hf₀, -, -⟩ := GlobalTheory.T.exists_coords_of_generic_point hRes E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨K₁, _, J₁, _, y₁, bk, bx, M, h, -, -, hdom, hnorm, hsm⟩ :=
    GlobalTheory.T.coords_after_finite_extension hRes K₀ J₀ Ω₀ Ω i yc X₀ ξ' hfin hall₀ htie₀
  have hMξ : M.ξ ≫ h ≫ f₀ = spMap i ≫ ξ₀ := by
    have e : M.ξ ≫ h = Spec.map (CommRingCat.ofHom i) ≫ ξ' := hdom
    rw [← Category.assoc, e, Category.assoc, hf₀]
  have hgenM : genPt (M.ξ ≫ h ≫ f₀) ∈ genericPoints Y.X := by
    rw [hMξ]
    show genPt (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) ∈ _
    rw [genPt_comp]
    exact hgen₀
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω _ hgenM
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hA := GlobalTheory.T.generic_trdeg_eq_dimension E H D l Xo c _ _ Y Ω₀ ξ₀ Ω y₀ i hinj hg (hy₀ ▸ hMξ)
  have htr : Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) := by
    let : Algebra Ω₀ Ω := i.toAlgebra
    have : FiniteDimensional Ω₀ Ω := hfin
    have : FaithfulSMul ℤ Ω₀ := (faithfulSMul_iff_algebraMap_injective ℤ Ω₀).mpr Int.cast_injective
    have : FaithfulSMul Ω₀ Ω := (faithfulSMul_iff_algebraMap_injective Ω₀ Ω).mpr i.injective
    have htow := trdeg_add_eq ℤ Ω₀ (A := Ω)
    rw [hA, trdeg_eq_zero_iff.2 (Algebra.IsAlgebraic.of_finite Ω₀ Ω), add_zero] at htow
    exact htow.symm
  obtain ⟨U, hd, hAb⟩ := GlobalTheory.T.dense_open_generic_fibre E H D l Xo c Y Ω _ _ M (h ≫ f₀) y₀ hy₀
  have hU := GlobalTheory.T.generic_fibre_open_coords E H D l Xo c Y Ω K₁ J₁ y₁ M (h ≫ f₀) y₀ U hy₀ hsm htr
  have hnm : Tor.IsNormalScheme M.X := ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω M.ξ M.tie.gen M.all).2).1 hnorm
  obtain ⟨N, x, X, ξ, f₂, hall, htie, hf₂, hp⟩ := exists_patches_of_res hRes c.F M.X ((h ≫ f₀) ≫ Y.s)
    (GlobalTheory.T.projective_model_over_base E H D l Xo c Y Ω _ _ M (h ≫ f₀)) hnm U hd D.dim hU _ hAb Ω M.ξ M.tie.gen
  obtain ⟨K, _, J, _, y, M₁, g, hne, hdom₁, hn₁, hp₁⟩ := GlobalTheory.T.exists_projective_coord_model Ω X ξ N x D.dim
    (f₂ ⁻¹' ((h ≫ f₀) ⁻¹' abLocus Y.t.G)) hall htie hp
  have hg₁ : M₁.ξ ≫ g = ξ := by
    have e : M₁.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ := hdom₁
    rw [e]; simp
  have hξ₁ : M₁.ξ ≫ g ≫ f₂ ≫ h ≫ f₀ = M.ξ ≫ h ≫ f₀ := by
    rw [← Category.assoc, hg₁, ← Category.assoc, hf₂]
  refine ⟨Ω, inferInstance, inferInstance, K, inferInstance, J, inferInstance, y, M₁, g ≫ f₂ ≫ h ≫ f₀, y₀, i, hne, hfin, hn₁,
    hξ₁.trans hy₀, hξ₁.trans hMξ, fun p hp' => ?_, hroot, ?_, htr⟩
  · rw [hξ₁, hMξ]
    exact htors p hp'
  · convert hp₁ using 4
    simp

section Shrink

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem ht_isVBOn (A : HodgeCpt Y S y) (hβ : Function.Injective β) {p : ℕ} (hp : p ∈ S) (s : CMType H ⊕ CMType H) :
    (A.HT p s).IsVBOn {q | ∀ r : ℕ, r.Prime → r ≠ p → ¬ InFibre A.ξ r q} (labelRk D s) (A.Vgen s) := by
  intro q _
  obtain ⟨U, hU, b, hb, hfr⟩ := A.vb s q trivial
  refine ⟨U, hU, b, hb, fun q' hq' hU' => ?_⟩
  have h := hfr q' trivial hU'
  have hV : A.V s q' = A.HT p s q' := by
    by_cases hf : InFibre A.ξ p q'
    · refine Lat.patch_of_unique S _ _ hp hf fun p' hp' h' => ?_
      by_contra hne
      exact hq' p' (A.S_prime p' hp') hne h'
    · have hc : ∀ r : ℕ, r.Prime → ¬ InFibre A.ξ r q' := fun r hr => by
        by_cases e : r = p
        · rw [e]; exact hf
        · exact hq' r hr e
      obtain ⟨h1, h2, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S Ω K J y A hβ q' hc
      rw [h1 s, h2 p (A.S_prime p hp) s]
  exact ⟨h.1, hV ▸ h.2⟩

theorem unitAt_nat {X : Scheme.{0}} {ξ : Sp Ω ⟶ X} [CharZero Ω] (q : Cpt ξ) (n : ℕ) (hn : n ≠ 0)
    (h : ∀ r : ℕ, r.Prime → r ∣ n → ¬ InFibre ξ r q) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    rw [Nat.cast_one]
    exact ⟨one_ne_zero, (regAt ξ q).one_mem, by simp⟩
  | prime r hr =>
    have := h r hr dvd_rfl
    exact not_not.1 this
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hn
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hn
    have h1 := ha ha0 fun r hr hd => h r hr (hd.mul_right b)
    have h2 := hb hb0 fun r hr hd => h r hr (hd.mul_left a)
    rw [Nat.cast_mul]
    refine ⟨mul_ne_zero h1.1 h2.1, mul_mem h1.2.1 h2.2.1, ?_⟩
    rw [mul_inv]
    exact mul_mem h1.2.2 h2.2.2

end Shrink

theorem vb_shrink {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S₀ S₁ : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (A : HodgeCpt Y (S₀ ∪ S₁) y) (hβ : Function.Injective β)
    (hd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) (s : CMType H ⊕ CMType H) :
    (Lat.patch S₀ (A.M.eigLat A.ρ (A.cst.comp (labelEmb c s)))
      fun p => htLabel A.M A.t.PP.L (p ^ A.R p) A.ρ (fun s' => A.cst.comp (labelEmb c s')) s).IsVB (labelRk D s)
      (eigSp A.ρ (A.cst.comp (labelEmb c s))) := by
  classical
  obtain ⟨-, -, hchar, hemb, hrank, -, -, hreg⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y _ Ω K J y A hβ
  have := hchar
  let : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  have : IsNoetherian A.X := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω A.ξ ℤ _ _ A.tie).2 A.all).1
  have hS₀ : ∀ p ∈ S₀, p.Prime := fun p hp => A.S_prime p (Finset.mem_union_left _ hp)
  obtain ⟨-, hcard⟩ := GlobalTheory.T.label_embedding_injective E H l c
  have hlat := (GlobalTheory.T.lie_omega_lattice_vector_bundle A.X Ω A.ξ A.t.G A.Li A.M A.tie.gen A.t.semi.smooth).1
  have hsplit := GlobalTheory.T.lattice_eigen_vector_bundle A.X Ω A.ξ A.Li E A.ρ A.M.lat {q | ∀ l ∈ S₀, ¬ InFibre A.ξ l q} _ (CMType H ⊕ CMType H)
    A.emb A.tie.gen hemb (by rw [← hcard, Nat.card_eq_fintype_card])
    (fun p _ => (hlat p trivial) |> fun ⟨U, hU, b, hb, hf⟩ => ⟨U, hU, b, hb, fun q _ hq => hf q trivial hq⟩)
    (fun p _ a e he => GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable _ Ω A.ξ _ _ A.M _ A.t.act A.ρ A.act p a e he)
    (fun p _ s a => hreg s a p)
    (fun p hp => by
      have h := unitAt_nat p (NumberField.discr E).natAbs (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E))
        fun r hr hdv => hp r (hd r hr (Int.natCast_dvd.2 hdv))
      rcases Int.natAbs_eq (NumberField.discr E) with e | e
      · rw [e]; simpa using h
      · rw [e]
        refine ⟨by simpa using h.1, by simp, ?_⟩
        simpa using neg_mem h.2.2)
  have h₀ : (A.dR s).IsVBOn {q | ∀ l ∈ S₀, ¬ InFibre A.ξ l q} (labelRk D s) (A.Vgen s) := by
    have := hsplit.1 s
    rw [show Module.finrank Ω (eigSp A.ρ (A.emb s)) = labelRk D s from hrank s] at this
    exact this
  obtain ⟨L, hL, hoff, hon⟩ := GlobalTheory.T.lattice_glue_over_primes A.X Ω A.ξ A.Li S₀ (A.dR s) (fun p => A.HT p s) (labelRk D s) (A.Vgen s)
    A.tie.gen hS₀ h₀ (fun p hp => ht_isVBOn A hβ (Finset.mem_union_left _ hp) s)
    (fun p hp q hq => ((GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y _ Ω K J y A hβ q hq).2.1 p (hS₀ p hp) s))
  have he : Lat.patch S₀ (A.dR s) (fun p => A.HT p s) = L := by
    funext q
    by_cases hq : ∃ p ∈ S₀, InFibre A.ξ p q
    · obtain ⟨p, hp, hf⟩ := hq
      rw [hon p hp q hf]
      exact Lat.patch_of_unique S₀ _ _ hp hf fun p' hp' h' => inFibre_unique (hS₀ p hp) (hS₀ p' hp') hf h'
    · push Not at hq
      rw [hoff q hq]
      exact Lat.patch_of_not S₀ _ _ hq
  show (Lat.patch S₀ (A.dR s) (fun p => A.HT p s)).IsVB (labelRk D s) (A.Vgen s)
  rw [he]
  exact hL

def toS₀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S₀ S₁ : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (A : HodgeCpt Y (S₀ ∪ S₁) y) (hβ : Function.Injective β)
    (hd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) {Ω₀ : Type} [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X)
    (h₀ : IsCptGen ξ₀) (i : Ω₀ →+* Ω) (hi : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f i) {K' : Type} [Fintype K'] {J' : K' → Type}
    [∀ k, Fintype (J' k)] (y' : (Σ k, J' k) → Ω)
    (tie' : CoordTie ℤ A.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) : HodgeCpt Y S₀ y' where
  X := A.X
  ξ := A.ξ
  all := A.all
  tie := tie'
  normal := A.normal
  f := A.f
  Ω₀ := Ω₀
  ξ₀ := ξ₀
  gen₀ := h₀
  cst := A.cst
  cst_over := A.cst_over
  fn := i
  fn_over := hi
  t := A.t
  m := A.m
  Li := A.Li
  M := A.M
  ρ := A.ρ
  act := A.act
  S_prime := fun p hp => A.S_prime p (Finset.mem_union_left _ hp)
  R := A.R
  R_ge := fun p hp => A.R_ge p (Finset.mem_union_left _ hp)
  tors := fun p hp => A.tors p (Finset.mem_union_left _ hp)
  vb := vb_shrink A hβ hd

theorem unitAt_div_of_span {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {q : Cpt ξ} {t m : Ω}
    (h : Submodule.span (regAt ξ q) {t} = Submodule.span (regAt ξ q) {m}) (hm : m ≠ 0) : unitAt ξ q (t / m) := by
  have h1 : t ∈ Submodule.span (regAt ξ q) {m} := h ▸ Submodule.mem_span_singleton_self t
  have h2 : m ∈ Submodule.span (regAt ξ q) {t} := h ▸ Submodule.mem_span_singleton_self m
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h2
  rw [Subring.smul_def, smul_eq_mul] at ha hb
  have ht : t ≠ 0 := by
    rintro rfl
    exact hm (by simpa using hb.symm)
  refine ⟨div_ne_zero ht hm, ?_, ?_⟩
  · rw [← ha, mul_div_assoc, div_self hm, _root_.mul_one]
    exact a.2
  · rw [inv_div, ← hb, mul_div_assoc, div_self ht, _root_.mul_one]
    exact b.2

theorem exists_geo : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∀ (S₀ S₁ : Finset ℕ) (sm : CMType H → CMType H ⊕ CMType H) (r : ℕ), (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, labelRk D (sm τ) = r) → (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₁, p.Prime) → Disjoint S₁ S₀ → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S₀ y) (deg : ℕ) (bd : Ideal (MRing J)) (vdeg : ℕ → K → ℤ) (vnum vden : ℕ → MRing J) (s : CMType H → Fin r → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), Nonempty K ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ 𝔐.IsCover deg ∧ 𝔐.OmVB ∧ (∀ p ∈ S₀ ∪ S₁, HT.HTFree 𝔐 p) ∧ Algebra.trdeg ℤ Ω = D.dim ∧ Cmp.IsSncModel y D.dim bd ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ mcPts bd ↔ ¬ 𝔐.Interior z)) ∧ (∀ p ∈ S₁, 4 ≤ 𝔐.R p) ∧ (∀ p ∈ S₁, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)) ∧ (∀ p ∈ S₁, ∀ s', (𝔐.HT p s').IsVBOn {q | ∀ r' : ℕ, r'.Prime → r' ≠ p → ¬ InFibre 𝔐.ξ r' q} (labelRk D s') (𝔐.Vgen s')) ∧ (∀ p ∈ S₁, IsVerticalDivisorAt (mCoordIdeal y) p (vdeg p) (vnum p) (vden p)) ∧ (∀ p ∈ S₁, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord y) ch q → ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li) (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω), (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) → (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') → unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval y (vnum p) / MvPolynomial.aeval y (vden p) * chartMono y ch (-vdeg p)))) ∧ (∀ τ, LinearIndependent Ω (s τ)) ∧ (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) ∧ (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y aMu e₀ := by
  intro hG hW E _ _ _ H D Xo l c Y hgl hp hq Ω₀ _ ξ₀ hξ₀ S₀ S₁ sm r hsm hrk hS₀ hS₁ hdis hdisc
  classical
  have hRes : ResK.ResKStatement := hG.2.2.2.2.1
  have hS : ∀ p ∈ S₀ ∪ S₁, p.Prime := fun p hp' => by
    rcases Finset.mem_union.1 hp' with h | h
    · exact hS₀ p h
    · exact hS₁ p h
  have hSd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀ ∪ S₁ := fun p h1 h2 =>
    Finset.mem_union_left _ (hdisc p h1 h2)
  obtain ⟨Ω, _, _, K₁, _, J₁, _, y₁, M₁, f₁, z₀, i, ⟨k₁⟩, hfin, hN, hz₀, hdomi, htors, hroot, hsnc₁, htr⟩ :=
    exists_base hRes E H D l (Xo l) c Y Ω₀ ξ₀ hξ₀ (S₀ ∪ S₁) hS
  have hgen₁ : f₁ (genPt M₁.ξ) ∈ genericPoints Y.X := by
    have e : genPt (M₁.ξ ≫ f₁) = genPt ξ₀ := by
      rw [hdomi]; exact genPt_comp i ξ₀
    have h0 := GlobalTheory.T.component_generic_is_generic_point E H D l (Xo l) c Y Ω₀ ξ₀ hξ₀
    rw [← e] at h0
    exact h0
  obtain ⟨K₂, _, J₂, _, y₂, bk, bx, A, g, hbk, hy₂, hdom₂, hf₂, hR₂, hfree, hiso⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l (Xo l) c Y (S₀ ∪ S₁) (fun _ => 4) Ω K₁ J₁ y₁ M₁ f₁ z₀ hN hz₀ hgen₁ hS hSd
      (fun _ _ => le_rfl) htors hroot
  have hgA : A.ξ ≫ g = M₁.ξ := by
    have e : A.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M₁.ξ := hdom₂
    rw [e]; simp
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hsncA : SncPts A.ξ D.dim {p | Char0 A.ξ p ∧ g p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} :=
    GlobalTheory.T.snc_points_transfer_dominating Ω _ _ _ _ M₁.X A.X M₁.ξ A.ξ g D.dim _ M₁.all A.all M₁.tie A.tie hdom₂ hiso hsnc₁
  have hi : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f i := by
    show A.ξ ≫ A.f = _
    rw [hf₂, ← Category.assoc, hgA]
    exact hdomi
  obtain ⟨-, -, hchar, -, hrank, -, -, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c _ _ Y _ Ω K₂ J₂ y₂ A hβ
  have hVB : ∀ s', (Lat.patch S₀ (A.dR s') fun p => A.HT p s').IsVB (labelRk D s') (A.Vgen s') :=
    vb_shrink A hβ hdisc
  have hs : ∀ τ, ∃ b : Fin r → A.Li, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = A.Vgen (sm τ) := by
    intro τ
    have hfr : Module.finrank Ω (A.Vgen (sm τ)) = r := (hrank _).trans (hrk τ)
    have hr : 0 < r := by
      rw [← hrk τ]
      rcases hsm with e | e <;> rw [e] <;> simp only [labelRk, Sum.elim_inl, Sum.elim_inr] <;> omega
    have : Module.Finite Ω (A.Vgen (sm τ)) := Module.finite_of_finrank_pos (by omega)
    let bs := Module.finBasisOfFinrankEq Ω (A.Vgen (sm τ)) hfr
    refine ⟨fun k => (bs k : A.Li), ?_, ?_⟩
    · exact bs.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
    · have h := congrArg (Submodule.map (A.Vgen (sm τ)).subtype) bs.span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
      exact h
  choose s hsl hss using hs
  have hdel : ∀ P : S₁, ∃ Δ : Lat A.ξ Ω, Δ.IsVB 1 ⊤ ∧ (∀ q, ¬ InFibre A.ξ P q → Δ q = Submodule.span (regAt A.ξ q) {1}) ∧
      ∀ q, InFibre A.ξ P q → ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → A.Li)
        (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω),
        (∀ τ, (Lat.patch S₀ (A.dR (sm τ)) fun p => A.HT p (sm τ)).IsFrameAt (b τ) q) →
        (∀ τ, (A.HT P (sm τ)).IsFrameAt (b' τ) q) → (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') →
        Δ q = Submodule.span (regAt A.ξ q) {∏ τ, (T τ).det} := fun P =>
    GlobalTheory.T.lattice_frames_away_prime A.X Ω A.ξ _ _ A.Li (CMType H) (fun τ => labelRk D (sm τ)) (fun τ => A.Vgen (sm τ))
      (fun τ => Lat.patch S₀ (A.dR (sm τ)) fun p => A.HT p (sm τ)) (fun τ => A.HT P (sm τ)) P A.tie A.all (hS₁ P P.2)
      (fun τ => hVB _) (fun τ => ht_isVBOn A hβ (Finset.mem_union_right _ P.2) _)
      (fun τ q hq => by
        have hB := GlobalTheory.T.hodge_cpt_away_from_primes E H D l (Xo l) c _ _ Y _ Ω K₂ J₂ y₂ (toS₀ A hβ hdisc ξ₀ hξ₀ i hi y₂ A.tie) hβ q hq
        exact ((GlobalTheory.T.hodge_cpt_away_from_primes E H D l (Xo l) c _ _ Y _ Ω K₂ J₂ y₂ A hβ q hq).2.1 P (hS₁ P P.2) (sm τ)).trans
          (hB.1 (sm τ)).symm)
  choose Δ hΔv hΔ1 hΔf using hdel
  let lmu : Lat A.ξ Ω := Lat.tens (fun τ => Cusp.detLat (Lat.patch S₀ (A.dR (sm τ)) fun p => A.HT p (sm τ)) (s τ)) fun _ => -1
  have hmu : lmu.IsVB 1 ⊤ := (GlobalTheory.T.lattice_tensor_power_line_bundle A.X Ω A.ξ _ _ Set.univ (fun τ => GlobalTheory.T.det_lattice_line_bundle A.X Ω A.ξ A.Li _ r (A.Vgen (sm τ)) (s τ)
    (hsl τ) (hss τ) (hrk τ ▸ hVB (sm τ))) _).1
  let Λ : Option S₁ → Lat A.ξ Ω := fun o => o.elim lmu Δ
  have hΛ : ∀ o, (Λ o).IsVB 1 ⊤ := by
    rintro (_ | P)
    · exact hmu
    · exact hΔv P
  obtain ⟨K₃, _, J₃, _, y₃, κ, v, hκ, hv, tie₃, hdeg⟩ := GlobalTheory.T.exists_block_refinement_lines A.X Ω A.ξ K₂ J₂ y₂ (Option S₁) Λ A.tie hΛ
  choose a e hde using hdeg
  have hver : ∀ P : S₁, ∃ f g : MRing J₃, IsVerticalDivisorAt (mCoordIdeal y₃) P (-(a (some P))) f g ∧
      MvPolynomial.aeval y₃ g ≠ 0 ∧ MvPolynomial.aeval y₃ f / MvPolynomial.aeval y₃ g = e (some P) := fun P =>
    GlobalTheory.T.vertical_divisor_degree A.X Ω A.ξ K₃ J₃ y₃ P (Δ P) (a (some P)) (e (some P)) tie₃ A.all (hde (some P)) (hΔ1 P)
  choose fv gv hvd hgv hfg using hver
  obtain ⟨bd, hbd, hbd'⟩ := GlobalTheory.T.snc_model_boundary_coords Ω A.X A.ξ K₃ J₃ y₃ D.dim {p | Char0 A.ξ p ∧ g p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} tie₃
    (fun p hp' => hp'.1) hsncA
  have hab : abLocus A.t.G = A.f ⁻¹' abLocus Y.t.G :=
    (Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 x).symm
  let algi : Algebra Ω₀ Ω := i.toAlgebra
  have : FiniteDimensional Ω₀ Ω := hfin
  refine ⟨K₃, inferInstance, J₃, inferInstance, Ω, inferInstance, inferInstance, y₃, toS₀ A hβ hdisc ξ₀ hξ₀ i hi y₃ tie₃,
    Module.finrank Ω₀ Ω, bd, fun p => if h : p ∈ S₁ then -(a (some ⟨p, h⟩)) else 0,
    fun p => if h : p ∈ S₁ then fv ⟨p, h⟩ else 0, fun p => if h : p ∈ S₁ then gv ⟨p, h⟩ else 0, s, a none, e none,
    ⟨κ (bk k₁)⟩, rfl, ⟨Module.finrank_pos, rfl⟩, fun p hp' => hfree p (Finset.mem_union_left _ hp'), hfree, htr, hbd, ?_, ?_, ?_, ?_,
    ?_, ?_, hsl, hss, hde none⟩
  · intro z w hw
    rw [hbd' z w hw]
    constructor
    · rintro ⟨h, -, h2⟩ hI
      have h3 : centre z ∈ abLocus A.t.G := hI
      rw [hab, hf₂] at h3
      exact h2 h3
    · intro hn
      refine ⟨A.all _, GlobalTheory.T.char_zero_centre_of_complex Ω A.X A.ξ z _ A.tie.gen, fun h => hn ?_⟩
      show centre z ∈ abLocus A.t.G
      rw [hab, hf₂]
      exact h
  · intro p hp'
    show 4 ≤ A.R p
    rw [hR₂]
  · intro p hp'
    exact A.tors p (Finset.mem_union_right _ hp')
  · intro p hp' s'
    exact ht_isVBOn A hβ (Finset.mem_union_right _ hp') s'
  · intro p hp'
    simp only [dite_eq_left hp']
    exact hvd ⟨p, hp'⟩
  · intro p hp' q hf ch hch b b' T hb hb' hT
    simp only [dite_eq_left hp']
    have h1 := hΔf ⟨p, hp'⟩ q hf b b' T hb hb' hT
    have h2 := (hde (some ⟨p, hp'⟩)).2 q trivial ch hch
    have he0 : e (some ⟨p, hp'⟩) ≠ 0 := (hde (some ⟨p, hp'⟩)).1
    have hne : ∀ k, y₃ ⟨k, ch k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hch.1 k (Finset.mem_univ k)
    have hm : e (some ⟨p, hp'⟩) * GroundTheory.Heights₂.Heights.LowerBoundFree.chartMono y₃ ch (a (some ⟨p, hp'⟩)) ≠ 0 :=
      mul_ne_zero he0 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k))
    have h3 : Submodule.span (regAt A.ξ q) {∏ τ, (T τ).det} = Submodule.span (regAt A.ξ q)
        {e (some ⟨p, hp'⟩) * GroundTheory.Heights₂.Heights.LowerBoundFree.chartMono y₃ ch (a (some ⟨p, hp'⟩))} := by
      rw [← h1]
      refine Eq.trans h2 ?_
      rw [smul_eq_mul, mul_comm]
      rfl
    rw [neg_neg, hfg ⟨p, hp'⟩]
    exact unitAt_div_of_span h3 hm

end GlobalTheory.CompanionTheory.Ar.GeoModel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalSncChartSystemStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_snc_chart_system : GlobalTheory.CompanionTheory.Ar.Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∀ (S₀ S₁ : Finset ℕ) (sm : CMType H → CMType H ⊕ CMType H) (r : ℕ), (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, labelRk D (sm τ) = r) → (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₁, p.Prime) → Disjoint S₁ S₀ → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S₀ y) (deg : ℕ) (bd : Ideal (MRing J)) (vdeg : ℕ → K → ℤ) (vnum vden : ℕ → MRing J) (s : CMType H → Fin r → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), Nonempty K ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ 𝔐.IsCover deg ∧ 𝔐.OmVB ∧ (∀ p ∈ S₀ ∪ S₁, HT.HTFree 𝔐 p) ∧ Algebra.trdeg ℤ Ω = D.dim ∧ Cmp.IsSncModel y D.dim bd ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ mcPts bd ↔ ¬ 𝔐.Interior z)) ∧ (∀ p ∈ S₁, 4 ≤ 𝔐.R p) ∧ (∀ p ∈ S₁, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)) ∧ (∀ p ∈ S₁, ∀ s', (𝔐.HT p s').IsVBOn {q | ∀ r' : ℕ, r'.Prime → r' ≠ p → ¬ InFibre 𝔐.ξ r' q} (labelRk D s') (𝔐.Vgen s')) ∧ (∀ p ∈ S₁, IsVerticalDivisorAt (mCoordIdeal y) p (vdeg p) (vnum p) (vden p)) ∧ (∀ p ∈ S₁, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord y) ch q → ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li) (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω), (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) → (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') → unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval y (vnum p) / MvPolynomial.aeval y (vden p) * chartMono y ch (-vdeg p)))) ∧ (∀ τ, LinearIndependent Ω (s τ)) ∧ (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) ∧ (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y aMu e₀ := by
  exact GlobalTheory.CompanionTheory.Ar.GeoModel.exists_geo
end
