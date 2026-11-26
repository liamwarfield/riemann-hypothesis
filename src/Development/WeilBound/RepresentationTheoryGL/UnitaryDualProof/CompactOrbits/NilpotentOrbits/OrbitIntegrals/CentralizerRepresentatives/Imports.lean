module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.IsChain

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChainsOfRange
namespace GlobalTheory.CompanionTheory.JordanChain

open Module Submodule

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def chainVec (f : V →ₗ[K] V) {ι : Type} (e : ι → ℕ) (v : ι → V) : (Σ a, Fin (e a)) → V :=
  fun p => (f ^ (p.2 : ℕ)) (v p.1)

theorem pow_coe_of_restrict {W : Submodule K V} (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hg : ∀ x, (g x : V) = f x) (k : ℕ) (x : W) : (((g ^ k) x : W) : V) = (f ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hg]

theorem exists_chains_of_range [FiniteDimensional K V] (f : V →ₗ[K] V)
    (g : LinearMap.range f →ₗ[K] LinearMap.range f) (hg : ∀ x, (g x : V) = f x)
    {ι' : Type} [Fintype ι'] (e' : ι' → ℕ) (he' : ∀ b, 0 < e' b) (w : ι' → LinearMap.range f)
    (h0 : ∀ b, (g ^ e' b) (w b) = 0) (hli : LinearIndependent K (chainVec g e' w))
    (hsp : span K (Set.range (chainVec g e' w)) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  classical
  have hu : ∀ b, ∃ u, f u = (w b : V) := fun b => (w b).2
  choose u hu using hu
  have hstep : ∀ (b : ι') (j : ℕ), (f ^ (j + 1)) (u b) = (f ^ j) (w b : V) := by
    intro b j
    rw [pow_succ, Module.End.mul_apply, hu]
  set N := LinearMap.ker f with hN
  let t : ι' → V := fun b => (f ^ e' b) (u b)
  have htN : ∀ b, t b ∈ N := by
    intro b
    have h1 : f (t b) = (f ^ (e' b + 1)) (u b) := by
      simp only [t]
      rw [pow_succ', Module.End.mul_apply]
    rw [hN, LinearMap.mem_ker, h1, hstep, ← pow_coe_of_restrict f g hg, h0]
    rfl
  have hLV : LinearIndependent K (fun p => ((chainVec g e' w p : LinearMap.range f) : V)) :=
    hli.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
  let idx : ι' → Σ b, Fin (e' b) := fun b => ⟨b, ⟨e' b - 1, by have := he' b; omega⟩⟩
  have hidx : Function.Injective idx := fun a b h => congrArg Sigma.fst h
  have ht : LinearIndependent K t := by
    have h2 := hLV.comp idx hidx
    convert h2 using 1
    funext b
    change (f ^ e' b) (u b) = ((g ^ (e' b - 1)) (w b) : LinearMap.range f)
    rw [pow_coe_of_restrict f g hg, ← hstep]
    congr 2
    have := he' b
    omega
  let tN : ι' → N := fun b => ⟨t b, htN b⟩
  have htNli : LinearIndependent K tN := LinearIndependent.of_comp N.subtype ht
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (span K (Set.range tN))
  let bC := Module.finBasis K C
  let z : Fin (finrank K C) → V := fun c => ((bC c : C) : N)
  have hz : ∀ c, f (z c) = 0 := fun c => ((bC c : C) : N).2
  let e : ι' ⊕ Fin (finrank K C) → ℕ := Sum.elim (fun b => e' b + 1) (fun _ => 1)
  let v : ι' ⊕ Fin (finrank K C) → V := Sum.elim u z
  let T := span K (Set.range (chainVec f e v))
  have hTu : ∀ (b : ι') (j : ℕ), j ≤ e' b → (f ^ j) (u b) ∈ T := by
    intro b j hj
    exact subset_span ⟨⟨Sum.inl b, ⟨j, Nat.lt_succ_of_le hj⟩⟩, rfl⟩
  have hTz : ∀ c, z c ∈ T := by
    intro c
    exact subset_span ⟨⟨Sum.inr c, ⟨0, Nat.one_pos⟩⟩, by simp [chainVec, v]⟩
  have hkerS : map N.subtype (span K (Set.range tN)) ≤ T := by
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨b, rfl⟩
    exact hTu b _ le_rfl
  have hkerC : map (N.subtype ∘ₗ C.subtype) ⊤ ≤ T := by
    rw [← bC.span_eq]
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact hTz c
  have hker : N ≤ T := by
    intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ span K (Set.range tN) ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨s, hs, c, hc, hsc⟩ := Submodule.mem_sup.1 hx'
    have hxe : x = (s : V) + (c : V) := by
      have := congrArg Subtype.val hsc
      simpa using this.symm
    rw [hxe]
    exact T.add_mem (hkerS ⟨s, hs, rfl⟩) (hkerC ⟨⟨c, hc⟩, trivial, rfl⟩)
  have hrange : ∀ y : LinearMap.range f, ∃ x ∈ T, f x = y := by
    have h3 : map (LinearMap.range f).subtype (span K (Set.range (chainVec g e' w))) ≤ map f T := by
      refine (Submodule.map_span_le _ _ _).2 ?_
      rintro _ ⟨⟨b, j⟩, rfl⟩
      refine ⟨(f ^ (j : ℕ)) (u b), hTu b _ j.2.le, ?_⟩
      simp only [chainVec, Submodule.subtype_apply]
      rw [pow_coe_of_restrict f g hg, ← hstep, pow_succ']
      rfl
    intro y
    have hy : (y : V) ∈ map (LinearMap.range f).subtype (span K (Set.range (chainVec g e' w))) := by
      rw [hsp]
      exact ⟨y, trivial, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h3 hy
    exact ⟨x, hx, hxy⟩
  have hTtop : T = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨x', hx', hxx⟩ := hrange ⟨f x, x, rfl⟩
    have hk : x - x' ∈ N := by
      rw [hN, LinearMap.mem_ker, map_sub, hxx]
      simp
    have := T.add_mem (hker hk) hx'
    simpa using this
  have hcard₁ : finrank K (LinearMap.range f) = ∑ b, e' b := by
    have h4 := finrank_span_eq_card hli
    rw [hsp, finrank_top] at h4
    rw [h4, Fintype.card_sigma]
    simp
  have hcard₂ : finrank K N = Fintype.card ι' + finrank K C := by
    have h5 := Submodule.finrank_add_eq_of_isCompl hC
    rw [finrank_span_eq_card htNli] at h5
    exact h5.symm
  have hcard : Fintype.card (Σ a, Fin (e a)) = finrank K V := by
    have h6 := LinearMap.finrank_range_add_finrank_ker f
    rw [Fintype.card_sigma, ← h6, hcard₁, ← hN, hcard₂]
    simp [e, Fintype.sum_sum_type, Finset.sum_add_distrib]
    omega
  refine ⟨ι' ⊕ Fin (finrank K C), inferInstance, e, v, ?_, ?_, ?_, hTtop⟩
  · rintro (b | c)
    · exact Nat.succ_pos _
    · exact Nat.one_pos
  · rintro (b | c)
    · change (f ^ (e' b + 1)) (u b) = 0
      rw [hstep, ← pow_coe_of_restrict f g hg, h0]
      rfl
    · change (f ^ 1) (z c) = 0
      simpa using hz c
  · exact linearIndependent_of_top_le_span_of_card_eq_finrank hTtop.ge hcard

theorem exists_chains : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V), finrank K V = n → IsNilpotent f →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ f hn hf
    by_cases hV : Subsingleton V
    · refine ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, fun a => a.elim, fun a => a.elim,
        ?_, Subsingleton.elim _ _⟩
      exact linearIndependent_empty_type
    · have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.1 hV
      obtain ⟨m, hm⟩ := hf
      have hlt : finrank K (LinearMap.range f) < n := by
        rw [← hn]
        refine Submodule.finrank_lt ?_
        intro htop
        have hsurj : Function.Surjective f := LinearMap.range_eq_top.1 htop
        have hs : Function.Surjective (f ^ m) := by
          rw [Module.End.coe_pow]
          exact hsurj.iterate m
        rw [hm] at hs
        obtain ⟨x, hx⟩ := exists_ne (0 : V)
        obtain ⟨y, hy⟩ := hs x
        exact hx (by simpa using hy.symm)
      let g : LinearMap.range f →ₗ[K] LinearMap.range f :=
        f.restrict (fun x _ => LinearMap.mem_range_self f x)
      have hg : ∀ x, (g x : V) = f x := fun x => rfl
      have hgn : IsNilpotent g := by
        refine ⟨m, LinearMap.ext fun x => Subtype.ext ?_⟩
        rw [pow_coe_of_restrict f g hg, hm]
        rfl
      obtain ⟨ι', _, e', w, he', h0, hli, hsp⟩ := ih _ hlt (LinearMap.range f) g rfl hgn
      exact exists_chains_of_range f g hg e' he' w h0 hli hsp

theorem exists_chain_basis {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧
      LinearIndependent K (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1)) ∧
      span K (Set.range (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1))) = ⊤ :=
  exists_chains _ V f rfl hf

end GlobalTheory.CompanionTheory.JordanChain
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.Normal
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ChainB
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.CbExistsChainOfGen
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.CbIsChainApply
noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

def cbFam (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (y : ι → W) : (Σ a, Fin (l a)) → W :=
  fun p => (N ^ (p.2 : ℕ)) (y p.1)

theorem cb_pow_succ (N : W →ₗ[E] W) (i : ℕ) (x : W) : N ((N ^ i) x) = (N ^ (i + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]

theorem cb_pow_pow (N : W →ₗ[E] W) (m j : ℕ) (x : W) : (N ^ m) ((N ^ j) x) = (N ^ (m + j)) x := by
  rw [← Module.End.mul_apply, ← pow_add]

theorem cb_pow_zero_of_le (N : W →ₗ[E] W) {m j : ℕ} {x : W} (h : (N ^ m) x = 0) (hj : m ≤ j) :
    (N ^ j) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show m + d = d + m from add_comm _ _, ← cb_pow_pow, h, map_zero]

theorem cb_isChain_of_fam (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (y : ι → W)
    (hy : ∀ a, (N ^ l a) (y a) = 0) (B : Module.Basis (Σ a, Fin (l a)) E W)
    (hB : ∀ p, B p = cbFam N l y p) : IsChain N l B := by
  intro a i
  rw [hB]
  simp only [cbFam]
  rw [cb_pow_succ]
  split_ifs with h
  · rw [hB]; rfl
  · have hi := i.isLt
    rw [show (i : ℕ) + 1 = l a by omega, hy]

theorem cb_isChain_apply (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : ℕ) (hi : i < l a) :
    B ⟨a, ⟨i, hi⟩⟩ = (N ^ i) (B ⟨a, ⟨0, h0⟩⟩) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := hB a ⟨i, by omega⟩
    rw [dite_eq_left (show ((⟨i, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a from hi)] at h1
    rw [← h1, ih (by omega), cb_pow_succ]

theorem cb_isChain_apply' (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : Fin (l a)) :
    B ⟨a, i⟩ = (N ^ (i : ℕ)) (B ⟨a, ⟨0, h0⟩⟩) := by
  obtain ⟨i, hi⟩ := i
  exact cb_isChain_apply N hB a h0 i hi

theorem cb_isChain_len (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) : (N ^ l a) (B ⟨a, ⟨0, h0⟩⟩) = 0 := by
  have h1 := hB a ⟨l a - 1, by omega⟩
  rw [dite_eq_right (show ¬ (((⟨l a - 1, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a) by simp; omega)] at h1
  rw [cb_isChain_apply N hB a h0 (l a - 1) (by omega), cb_pow_succ] at h1
  rwa [show l a - 1 + 1 = l a by omega] at h1

theorem cb_eq_top (N : W →ₗ[E] W) (hN : IsNilpotent N) (S : Submodule E W)
    (hS : ∀ x ∈ S, N x ∈ S) (h : S ⊔ LinearMap.range N = ⊤) : S = ⊤ := by
  have key : ∀ k : ℕ, S ⊔ LinearMap.range (N ^ k) = ⊤ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id, sup_top_eq]
    | succ k ih =>
      rw [eq_top_iff]
      intro w _
      have hw : w ∈ S ⊔ LinearMap.range N := h ▸ Submodule.mem_top
      obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨z', rfl⟩ := hz
      have hz' : z' ∈ S ⊔ LinearMap.range (N ^ k) := ih ▸ Submodule.mem_top
      obtain ⟨x2, hx2, z2, hz2, rfl⟩ := Submodule.mem_sup.mp hz'
      obtain ⟨z3, rfl⟩ := hz2
      rw [map_add (f := _)]
      apply Submodule.mem_sup.mpr
      refine ⟨x + N x2, S.add_mem hx (hS _ hx2), (N ^ (k + 1)) z3, ⟨z3, rfl⟩, ?_⟩
      rw [cb_pow_succ, add_assoc]
  obtain ⟨K, hK⟩ := hN
  have := key K
  rwa [hK, LinearMap.range_zero, sup_bot_eq] at this

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem cb_exists_chain_of_gen (N : W →ₗ[E] W) (hN : IsNilpotent N) {ι : Type} [Fintype ι] {l : ι → ℕ}
    (B0 : Module.Basis (Σ a, Fin (l a)) E W) (hB0 : IsChain N l B0) (hl : ∀ a, 0 < l a) (y : ι → W)
    (hy0 : ∀ a, (N ^ l a) (y a) = 0)
    (hy : ∀ a, B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E (Set.range (cbFam N l y)) ⊔ LinearMap.range N) :
    ∃ B : Module.Basis (Σ a, Fin (l a)) E W, IsChain N l B ∧ ∀ p, B p = cbFam N l y p := by
  set S := span E (Set.range (cbFam N l y)) with hSdef
  have hS : ∀ x ∈ S, N x ∈ S := by
    intro x hx
    have : S ≤ S.comap N := by
      rw [hSdef, span_le]
      rintro _ ⟨p, rfl⟩
      show N (cbFam N l y p) ∈ S
      simp only [cbFam]
      rw [cb_pow_succ]
      by_cases h : (p.2 : ℕ) + 1 < l p.1
      · exact subset_span ⟨⟨p.1, ⟨p.2 + 1, h⟩⟩, rfl⟩
      · rw [cb_pow_zero_of_le N (hy0 p.1) (by omega)]; exact S.zero_mem
    exact this hx
  have htop : S ⊔ LinearMap.range N = ⊤ := by
    rw [eq_top_iff, ← B0.span_eq, span_le]
    rintro _ ⟨⟨a, ⟨i, hi⟩⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; exact hy a
    · apply Submodule.mem_sup_right
      rw [cb_isChain_apply N hB0 a (hl a) i hi]
      refine ⟨(N ^ (i - 1)) (B0 ⟨a, ⟨0, hl a⟩⟩), ?_⟩
      rw [cb_pow_succ, show i - 1 + 1 = i by omega]
  have hST : S = ⊤ := cb_eq_top N hN S hS htop
  have hli : LinearIndependent E (cbFam N l y) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (by rw [← hSdef, hST])
      (by rw [Module.finrank_eq_card_basis B0])
  refine ⟨Basis.mk hli (by rw [← hSdef, hST]), ?_, fun p => by simp⟩
  exact cb_isChain_of_fam N l y hy0 _ (fun p => by simp)

theorem cb_single (N : W →ₗ[E] W) (L : ℕ) (u : W) (hu : (N ^ L) u = 0) (c : Fin L → E) :
    ∃ s ≤ L, ∃ y : W, (N ^ L) y = 0 ∧ (N ^ s) y = ∑ i, c i • (N ^ (i : ℕ)) u ∧
      u ∈ span E {y} ⊔ LinearMap.range N := by
  classical
  by_cases h : ∃ i, ∃ hi : i < L, c ⟨i, hi⟩ ≠ 0
  · obtain ⟨s, ⟨hsL, hcs⟩, hmin⟩ : ∃ s, (∃ hi : s < L, c ⟨s, hi⟩ ≠ 0) ∧
        ∀ i < s, ∀ hi : i < L, c ⟨i, hi⟩ = 0 :=
      ⟨Nat.find h, Nat.find_spec h, fun i hi hiL => by
        by_contra hne; exact Nat.find_min h hi ⟨hiL, hne⟩⟩
    set y : W := ∑ i : Fin L, if s ≤ (i : ℕ) then c i • (N ^ ((i : ℕ) - s)) u else 0 with hydef
    set z : W := ∑ i : Fin L, if s < (i : ℕ) then c i • (N ^ ((i : ℕ) - s - 1)) u else 0 with hzdef
    refine ⟨s, hsL.le, y, ?_, ?_, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [hydef, map_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        split_ifs
        · rw [map_smul, cb_pow_pow, cb_pow_zero_of_le N hu (by omega), smul_zero]
        · exact map_zero _
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [hydef, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with h1
        · rw [map_smul, cb_pow_pow, show s + ((i : ℕ) - s) = i by omega]
        · rw [map_zero, hmin i (by omega) i.2, zero_smul]
    · have hyz : y = c ⟨s, hsL⟩ • u + N z := by
        have hc : c ⟨s, hsL⟩ • u = ∑ i : Fin L, if i = ⟨s, hsL⟩ then c i • u else 0 := by
          rw [Finset.sum_ite_eq']; simp
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hc, hydef, hzdef, map_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases lt_trichotomy (i : ℕ) s with h1 | h1 | h1
        · have hne : i ≠ ⟨s, hsL⟩ := fun he => by rw [he] at h1; exact lt_irrefl _ h1
          rw [if_neg (by omega), if_neg hne, if_neg (by omega), map_zero, add_zero]
        · have he : i = ⟨s, hsL⟩ := Fin.ext h1
          rw [if_pos (by omega), if_pos he, if_neg (by omega), map_zero, add_zero, h1, Nat.sub_self,
            pow_zero, Module.End.one_apply]
        · have hne : i ≠ ⟨s, hsL⟩ := fun he => by rw [he] at h1; exact lt_irrefl _ h1
          rw [if_pos (by omega), if_neg hne, if_pos h1, zero_add, map_smul, cb_pow_succ,
            show (i : ℕ) - s - 1 + 1 = (i : ℕ) - s by omega]
      have hu_eq : u = (c ⟨s, hsL⟩)⁻¹ • y - N ((c ⟨s, hsL⟩)⁻¹ • z) := by
        rw [hyz, smul_add, smul_smul, inv_mul_cancel₀ hcs, one_smul, map_smul]; abel
      rw [hu_eq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self y))) (Submodule.mem_sup_right (LinearMap.mem_range_self N _))
  · push Not at h
    refine ⟨L, le_rfl, u, hu, ?_, Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)⟩
    rw [hu]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show c i = 0 from h i i.2, zero_smul]

theorem cb_init (N : W →ₗ[E] W) {ι : Type} [Fintype ι] {l : ι → ℕ}
    (B0 : Module.Basis (Σ a, Fin (l a)) E W) (hB0 : IsChain N l B0) (hl : ∀ a, 0 < l a) (v : W) :
    ∃ (y : ι → W) (s : ι → ℕ), (∀ a, (N ^ l a) (y a) = 0) ∧
      (∀ a, B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E (Set.range (cbFam N l y)) ⊔ LinearMap.range N) ∧
      (∀ a, s a ≤ l a) ∧ v = ∑ a, (N ^ s a) (y a) := by
  have H : ∀ a, ∃ s ≤ l a, ∃ y : W, (N ^ l a) y = 0 ∧
      (N ^ s) y = ∑ i : Fin (l a), B0.repr v ⟨a, i⟩ • (N ^ (i : ℕ)) (B0 ⟨a, ⟨0, hl a⟩⟩) ∧
      B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E {y} ⊔ LinearMap.range N :=
    fun a => cb_single N (l a) _ (cb_isChain_len N hB0 a (hl a)) _
  choose s hs y hy0 hys hyu using H
  refine ⟨y, s, hy0, fun a => ?_, hs, ?_⟩
  · have hle : span E {y a} ≤ span E (Set.range (cbFam N l y)) := by
      rw [span_le, Set.singleton_subset_iff]
      exact subset_span ⟨⟨a, ⟨0, hl a⟩⟩, by simp [cbFam]⟩
    exact sup_le_sup_right hle _ (hyu a)
  · conv_lhs => rw [← B0.sum_repr v]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hys]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cb_isChain_apply' N hB0 a (hl a) i]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem cb_step (N : W →ₗ[E] W) (hN : IsNilpotent N) {ι : Type} [Fintype ι] [DecidableEq ι] {l : ι → ℕ}
    (hl : ∀ a, 0 < l a) (v : W) (y : ι → W) (s : ι → ℕ) (hy0 : ∀ a, (N ^ l a) (y a) = 0)
    (B : Module.Basis (Σ a, Fin (l a)) E W) (hB : IsChain N l B) (hBy : ∀ p, B p = cbFam N l y p)
    (hs : ∀ a, s a ≤ l a) (hv : v = ∑ a, (N ^ s a) (y a)) (a b : ι) (hab : s b + (l a - l b) < s a) :
    ∃ (y' : ι → W) (s' : ι → ℕ), (∀ a, (N ^ l a) (y' a) = 0) ∧
      (∃ B' : Module.Basis (Σ a, Fin (l a)) E W, IsChain N l B' ∧ ∀ p, B' p = cbFam N l y' p) ∧
      (∀ a, s' a ≤ l a) ∧ v = ∑ a, (N ^ s' a) (y' a) ∧ ∑ a, s' a < ∑ a, s a := by
  have hne : a ≠ b := by rintro rfl; simp at hab
  set i0 := l a - l b with hi0
  set d := s a - (s b + i0) with hd
  have hdpos : 0 < d := by omega
  set y' : ι → W := Function.update (Function.update y b (y b - (N ^ i0) (y a))) a
    (y a + (N ^ d) (y a)) with hy'
  set s' : ι → ℕ := Function.update s a (s b + i0) with hs'
  have y'a : y' a = y a + (N ^ d) (y a) := by simp [y']
  have y'b : y' b = y b - (N ^ i0) (y a) := by simp [y', hne.symm]
  have y'c : ∀ c, c ≠ a → c ≠ b → y' c = y c := by intro c h1 h2; simp [y', h1, h2]
  have s'a : s' a = s b + i0 := by simp [s']
  have s'c : ∀ c, c ≠ a → s' c = s c := by intro c h; simp [s', h]
  have hy0' : ∀ c, (N ^ l c) (y' c) = 0 := by
    intro c
    by_cases hca : c = a
    · rw [hca, y'a, map_add (f := _), hy0, cb_pow_pow, cb_pow_zero_of_le N (hy0 a) (by omega), add_zero]
    by_cases hcb : c = b
    · rw [hcb, y'b, map_sub, hy0, cb_pow_pow, cb_pow_zero_of_le N (hy0 a) (by omega), sub_zero]
    · rw [y'c c hca hcb, hy0]
  have hgen : ∀ c, B ⟨c, ⟨0, hl c⟩⟩ ∈ span E (Set.range (cbFam N l y')) ⊔ LinearMap.range N := by
    set T := span E (Set.range (cbFam N l y')) ⊔ LinearMap.range N with hT
    have hmemS : ∀ c, y' c ∈ T := fun c =>
      Submodule.mem_sup_left (subset_span ⟨⟨c, ⟨0, hl c⟩⟩, by simp [cbFam]⟩)
    have hmemR : ∀ j x, 0 < j → (N ^ j) x ∈ T := fun j x hj =>
      Submodule.mem_sup_right ⟨(N ^ (j - 1)) x, by rw [cb_pow_succ, show j - 1 + 1 = j by omega]⟩
    have hya : y a ∈ T := by
      have : y a = y' a - (N ^ d) (y a) := by rw [y'a]; abel
      rw [this]; exact T.sub_mem (hmemS a) (hmemR d _ hdpos)
    have hyb : y b ∈ T := by
      have : y b = y' b + (N ^ i0) (y a) := by rw [y'b]; abel
      rw [this]; refine T.add_mem (hmemS b) ?_
      rcases Nat.eq_zero_or_pos i0 with h | h
      · rw [h, pow_zero, Module.End.one_apply]; exact hya
      · exact hmemR i0 _ h
    intro c
    have hc : B ⟨c, ⟨0, hl c⟩⟩ = y c := by rw [hBy]; simp [cbFam]
    rw [hc]
    by_cases hca : c = a
    · rw [hca]; exact hya
    by_cases hcb : c = b
    · rw [hcb]; exact hyb
    rw [← y'c c hca hcb]; exact hmemS c
  obtain ⟨B', hB', hB'y⟩ := cb_exists_chain_of_gen N hN B hB hl y' hy0' hgen
  have hsle : ∀ c, s' c ≤ l c := by
    intro c
    by_cases hca : c = a
    · rw [hca, s'a]; have := hs a; omega
    · rw [s'c c hca]; exact hs c
  have hterm : ∀ c, (N ^ s' c) (y' c) = (N ^ s c) (y c) +
      ((if c = a then (N ^ (s b + i0)) (y a) else 0) - (if c = b then (N ^ (s b + i0)) (y a) else 0)) := by
    intro c
    by_cases hca : c = a
    · rw [hca, s'a, y'a, if_pos rfl, if_neg hne, map_add (f := _), cb_pow_pow, show s b + i0 + d = s a by omega]
      abel
    by_cases hcb : c = b
    · rw [hcb, s'c b (fun h => hne h.symm), y'b, if_neg (fun h => hne h.symm), if_pos rfl, map_sub, cb_pow_pow]
      abel
    · rw [s'c c hca, y'c c hca hcb, if_neg hca, if_neg hcb, sub_zero, add_zero]
  have hv' : v = ∑ c, (N ^ s' c) (y' c) := by
    rw [hv, Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp
  have hsum : ∑ c, s' c < ∑ c, s c := by
    rw [hs', Finset.sum_update_of_mem (Finset.mem_univ a), Finset.sdiff_singleton_eq_erase,
      ← Finset.add_sum_erase Finset.univ s (Finset.mem_univ a)]
    omega
  exact ⟨y', s', hy0', ⟨B', hB', hB'y⟩, hsle, hv', hsum⟩

theorem exists_good [FiniteDimensional E W] (N : W →ₗ[E] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W), IsChain N l B ∧
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧ (∀ a b, s a ≤ s b + (l a - l b)) ∧
      v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0 := by
  classical
  obtain ⟨ι, _, e, u, he, hu0, hli, hsp⟩ := GlobalTheory.CompanionTheory.JordanChain.exists_chain_basis N hN
  let B0 : Module.Basis (Σ a, Fin (e a)) E W := Basis.mk hli (by rw [hsp])
  have hB0p : ∀ p, B0 p = cbFam N e u p := fun p => by simp [B0, cbFam]
  have hB0 : IsChain N e B0 := cb_isChain_of_fam N e u hu0 B0 hB0p
  obtain ⟨y, s, hy0, hyg, hs, hv⟩ := cb_init N B0 hB0 he v
  obtain ⟨B1, hB1, hB1y⟩ := cb_exists_chain_of_gen N hN B0 hB0 he y hy0 hyg
  have hex : ∃ k, ∃ (y : ι → W) (s : ι → ℕ), ((∀ a, (N ^ e a) (y a) = 0) ∧
      (∃ B : Module.Basis (Σ a, Fin (e a)) E W, IsChain N e B ∧ ∀ p, B p = cbFam N e y p) ∧
      (∀ a, s a ≤ e a) ∧ v = ∑ a, (N ^ s a) (y a)) ∧ ∑ a, s a = k :=
    ⟨_, y, s, ⟨hy0, ⟨B1, hB1, hB1y⟩, hs, hv⟩, rfl⟩
  obtain ⟨y, s, ⟨hy0, ⟨B, hB, hBy⟩, hs, hv⟩, hk⟩ := Nat.find_spec hex
  have hC : ∀ a b, s a ≤ s b + (e a - e b) := by
    intro a b
    by_contra hab
    push Not at hab
    obtain ⟨y', s', h1, h2, h3, h4, h5⟩ := cb_step N hN he v y s hy0 B hB hBy hs hv a b hab
    exact Nat.find_min hex (hk ▸ h5) ⟨y', s', ⟨h1, h2, h3, h4⟩, rfl⟩
  refine ⟨ι, inferInstance, e, s, B, hB, he, hs, hC, ?_⟩
  rw [hv]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [hBy]; rfl
  · rw [show s a = e a by have := hs a; omega, hy0]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ChainA
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem sigma_fin_eq_iff {ι : Type} {l : ι → ℕ} {b a : ι} {j : Fin (l b)} {i : Fin (l a)} :
    (⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, i⟩ ↔ b = a ∧ (j : ℕ) = i := by
  constructor
  · intro h
    cases h
    simp
  · rintro ⟨rfl, h⟩
    rw [Fin.ext h]

theorem chain_repr_N {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr (N z) ⟨a, i⟩ = if h : 0 < (i : ℕ) then B.repr z ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by
  classical
  have key : (B.coord ⟨a, i⟩).comp N =
      if h : 0 < (i : ℕ) then B.coord ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by
    apply B.ext
    rintro ⟨b, j⟩
    rw [LinearMap.comp_apply, hB]
    by_cases hi : 0 < (i : ℕ)
    · rw [dite_eq_left hi]
      by_cases hj : (j : ℕ) + 1 < l b
      · rw [dite_eq_left hj, Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
          Module.Basis.repr_self_apply]
        have hiff : ((⟨b, ⟨j + 1, hj⟩⟩ : Σ a, Fin (l a)) = ⟨a, i⟩) ↔
            ((⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, ⟨i - 1, by omega⟩⟩) := by
          rw [sigma_fin_eq_iff, sigma_fin_eq_iff]
          constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by simp only at h2 ⊢; omega⟩
        exact if_congr hiff rfl rfl
      · rw [dite_eq_right hj, map_zero, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg]
        intro h
        rw [sigma_fin_eq_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp only at h2
        have := i.2
        omega
    · rw [dite_eq_right hi]
      split_ifs with hj
      · rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg, LinearMap.zero_apply]
        intro h
        rw [sigma_fin_eq_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp only at h2
        omega
      · simp
  have := LinearMap.congr_fun key z
  rw [LinearMap.comp_apply, Module.Basis.coord_apply] at this
  rw [this]
  split_ifs <;> simp

theorem chain_repr_Npow {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr ((N ^ m) z) ⟨a, i⟩ = if h : m ≤ (i : ℕ) then B.repr z ⟨a, ⟨i - m, by omega⟩⟩ else 0 := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    by_cases h1 : m + 1 ≤ (i : ℕ)
    · rw [dite_eq_left (by omega), dite_eq_left h1, chain_repr_N hB, dite_eq_left (by simp; omega)]
      congr 2
    · rw [dite_eq_right h1]
      split_ifs with h2
      · rw [chain_repr_N hB, dite_eq_right]
        simp
        omega
      · rfl

theorem chain_repr_of_ker {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (hz : (N ^ m) z = 0) (a : ι) (i : Fin (l a))
    (hi : (i : ℕ) + m < l a) : B.repr z ⟨a, i⟩ = 0 := by
  have h := chain_repr_Npow hB m z a ⟨i + m, hi⟩
  rw [hz, map_zero, dite_eq_left (by simp)] at h
  rw [Finsupp.zero_apply] at h
  rw [h]
  congr 2
  ext
  simp

theorem chain_Npow_zero {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (b : ι) (hb : 0 < l b) (j : ℕ) :
    (N ^ j) (B ⟨b, ⟨0, hb⟩⟩) = if h : j < l b then B ⟨b, ⟨j, h⟩⟩ else 0 := by
  induction j with
  | zero => simp [hb]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    by_cases hj : j < l b
    · rw [dite_eq_left hj, hB]
    · rw [dite_eq_right hj, map_zero, dite_eq_right (by omega)]

theorem repr_centralizer_eq_zero (N : W →ₗ[E] W) {ι : Type} [Fintype ι] (l : ι → ℕ)
    (B : Module.Basis (Σ a, Fin (l a)) E W) (hB : IsChain N l B) (s : ι → ℕ) (_hs : ∀ a, s a ≤ l a)
    (hC : ∀ a b, s a ≤ s b + (l a - l b)) (v : W) (hv : v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0)
    (A : W →ₗ[E] W) (hA : A ∘ₗ N = N ∘ₗ A) (a : ι) (i : Fin (l a)) (hi : (i : ℕ) < s a) :
    B.repr (A v) ⟨a, i⟩ = 0 := by
  have hc : Commute A N := hA
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hv, map_sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : s b < l b
  · rw [dite_eq_left hb]
    have hlb : 0 < l b := by omega
    have h1 : B ⟨b, ⟨s b, hb⟩⟩ = (N ^ s b) (B ⟨b, ⟨0, hlb⟩⟩) := by
      rw [chain_Npow_zero hB b hlb, dite_eq_left hb]
    have hcomm : ∀ m : ℕ, ∀ x, A ((N ^ m) x) = (N ^ m) (A x) := fun m x =>
      LinearMap.congr_fun (hc.pow_right m).eq x
    rw [h1, hcomm, chain_repr_Npow hB]
    split_ifs with h2
    · refine chain_repr_of_ker hB (l b) _ ?_ a _ ?_
      · rw [← hcomm, chain_Npow_zero hB b hlb, dite_eq_right (lt_irrefl _), map_zero]
      · have := hC a b
        show (i : ℕ) - s b + l b < l a
        omega
    · rfl
  · rw [dite_eq_right hb, map_zero, map_zero, Finsupp.zero_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem exists_normal [FiniteDimensional E W] (N : W →ₗ[E] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W), IsChain N l B ∧
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧ v = ∑ a, (if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0) ∧
      ∀ A : W →ₗ[E] W, A ∘ₗ N = N ∘ₗ A → ∀ (a : ι) (i : Fin (l a)), (i : ℕ) < s a → B.repr (A v) ⟨a, i⟩ = 0 := by
  obtain ⟨ι, _, l, s, B, hB, hl, hs, hC, hv⟩ := exists_good N hN v
  exact ⟨ι, inferInstance, l, s, B, hB, hl, hs, hv, fun A hA a i hi =>
    repr_centralizer_eq_zero N l B hB s hs hC v hv A hA a i hi⟩

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

section -- restored from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.DexBlockFrame
noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module

variable {k : Type} [Field k] {R : Type} [CommRing R] [Algebra k R]

theorem dex_block_frame (I : Ideal R) [I.IsMaximal] {L : Type} [Fintype L] (b : Basis L k (R ⧸ I))
    {W : Type} [AddCommGroup W] [Module R W] [Module k W] [IsScalarTower k R W] [FiniteDimensional k W]
    (hW : ∀ z ∈ I, ∀ y : W, z • y = 0) (N : W →ₗ[R] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (β : Basis (L × Σ a : ι, Fin (l a)) k W),
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧
      (∀ (z : R) (p : L) (j : Σ a : ι, Fin (l a)),
        z • β (p, j) = ∑ q, (b.repr (Ideal.Quotient.mk I z * b p) q) • β (q, j)) ∧
      (∀ (p : L) (a : ι) (i : Fin (l a)), N (β (p, ⟨a, i⟩)) =
        if h : (i : ℕ) + 1 < l a then β (p, ⟨a, ⟨i + 1, h⟩⟩) else 0) ∧
      v = ∑ p, ∑ a, (if h : s a < l a then b.repr 1 p • β (p, ⟨a, ⟨s a, h⟩⟩) else 0) ∧
      ∀ A : W →ₗ[R] W, A ∘ₗ N = N ∘ₗ A → ∀ (p : L) (a : ι) (i : Fin (l a)), (i : ℕ) < s a →
        β.repr (A v) (p, ⟨a, i⟩) = 0 := by
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have hT : Module.IsTorsionBySet R W I := fun y z => hW z z.2 y
  letI : Module (R ⧸ I) W := hT.module
  have hmk : ∀ (z : R) (y : W), (Ideal.Quotient.mk I z) • y = z • y := fun z y => rfl
  haveI : IsScalarTower k (R ⧸ I) W := ⟨fun c e y => by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective e
    have : c • Ideal.Quotient.mk I z = Ideal.Quotient.mk I (c • z) := (map_smul (Ideal.Quotient.mkₐ k I) c z).symm
    rw [this, hmk, hmk, smul_assoc]⟩
  haveI : FiniteDimensional (R ⧸ I) W := Module.Finite.of_restrictScalars_finite k (R ⧸ I) W
  let toE : (W →ₗ[R] W) → (W →ₗ[R ⧸ I] W) := fun f =>
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c y => by
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
        simp only [RingHom.id_apply, hmk]
        exact f.map_smul z y }
  have htoE : ∀ f y, toE f y = f y := fun f y => rfl
  have hNE : IsNilpotent (toE N) := by
    obtain ⟨m, hm⟩ := hN
    refine ⟨m, LinearMap.ext fun y => ?_⟩
    have : ((toE N) ^ m) y = (N ^ m) y := by
      rw [Module.End.pow_apply, Module.End.pow_apply]
      rfl
    rw [this, hm]
    rfl
  obtain ⟨ι, _, l, s, B, hB, hl, hs, hv, hA⟩ := exists_normal (toE N) hNE v
  refine ⟨ι, inferInstance, l, s, b.smulTower B, hl, hs, ?_, ?_, ?_, ?_⟩
  · intro z p j
    rw [Basis.smulTower_apply]
    calc z • (b p • B j) = (Ideal.Quotient.mk I z) • (b p • B j) := rfl
      _ = (Ideal.Quotient.mk I z * b p) • B j := by rw [smul_smul]
      _ = (∑ q, b.repr (Ideal.Quotient.mk I z * b p) q • b q) • B j := by rw [b.sum_repr]
      _ = ∑ q, (b.repr (Ideal.Quotient.mk I z * b p) q) • (b.smulTower B) (q, j) := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Basis.smulTower_apply, smul_assoc]
  · intro p a i
    rw [Basis.smulTower_apply]
    have h1 : N (b p • B ⟨a, i⟩) = b p • (toE N) (B ⟨a, i⟩) := (toE N).map_smul (b p) (B ⟨a, i⟩)
    rw [h1, hB a i]
    split_ifs with h
    · rw [Basis.smulTower_apply]
    · rw [smul_zero]
  · rw [Finset.sum_comm]
    conv_lhs => rw [hv]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : s a < l a
    · simp only [h, dif_pos, Basis.smulTower_apply]
      calc B ⟨a, ⟨s a, h⟩⟩ = (1 : R ⧸ I) • B ⟨a, ⟨s a, h⟩⟩ := (one_smul _ _).symm
        _ = (∑ p, b.repr 1 p • b p) • B ⟨a, ⟨s a, h⟩⟩ := by rw [b.sum_repr]
        _ = ∑ p, b.repr 1 p • (b p • B ⟨a, ⟨s a, h⟩⟩) := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [smul_assoc]
    · simp only [h, dif_neg, not_false_eq_true, Finset.sum_const_zero]
  · intro A hAN p a i hi
    have hc : toE A ∘ₗ toE N = toE N ∘ₗ toE A := by
      refine LinearMap.ext fun y => ?_
      exact LinearMap.congr_fun hAN y
    rw [Basis.smulTower_repr]
    have := hA (toE A) hc a i hi
    rw [htoE] at this
    rw [this, map_zero, Finsupp.zero_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

section -- restored from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.DexGlobal
noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module

variable {k : Type} [Field k]

theorem dex_global {R : Type} [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsReduced R]
    {V : Type} [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V] :
    ∃ (M : Type) (_ : Fintype M) (L : M → Type) (_ : ∀ m, Fintype (L m)) (_ : ∀ m, Nonempty (L m))
      (Rc : R → (m : M) → L m → L m → k) (o : (m : M) → L m → k),
      ∀ N : V →ₗ[R] V, IsNilpotent N → ∀ v : V,
        ∃ (ι : M → Type) (_ : ∀ m, Fintype (ι m)) (l s : (m : M) → ι m → ℕ)
          (β : Basis (Σ m, L m × (Σ a : ι m, Fin (l m a))) k V),
          (∀ m a, 0 < l m a) ∧ (∀ m a, s m a ≤ l m a) ∧
          (∀ (z : R) m (p : L m) (j : Σ a : ι m, Fin (l m a)),
            z • β ⟨m, (p, j)⟩ = ∑ q, Rc z m p q • β ⟨m, (q, j)⟩) ∧
          (∀ m (p : L m) (a : ι m) (i : Fin (l m a)), N (β ⟨m, (p, ⟨a, i⟩)⟩) =
            if h : (i : ℕ) + 1 < l m a then β ⟨m, (p, ⟨a, ⟨i + 1, h⟩⟩)⟩ else 0) ∧
          v = ∑ m, ∑ p, ∑ a, (if h : s m a < l m a then o m p • β ⟨m, (p, ⟨a, ⟨s m a, h⟩⟩)⟩ else 0) ∧
          ∀ A : V →ₗ[R] V, A ∘ₗ N = N ∘ₗ A → ∀ m (p : L m) (a : ι m) (i : Fin (l m a)), (i : ℕ) < s m a →
            β.repr (A v) ⟨m, (p, ⟨a, i⟩)⟩ = 0 := by
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  classical
  let M := MaximalSpectrum R
  letI : Fintype M := Fintype.ofFinite M
  have hfin : ∀ m : M, Module.Finite k (R ⧸ m.asIdeal) := fun m =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m.asIdeal).toLinearMap Ideal.Quotient.mk_surjective
  let L : M → Type := fun m => Fin (finrank k (R ⧸ m.asIdeal))
  let b : ∀ m : M, Basis (L m) k (R ⧸ m.asIdeal) := fun m => by
    haveI := hfin m
    exact Module.finBasis k _
  have hne : ∀ m, Nonempty (L m) := fun m => by
    haveI := hfin m
    haveI : Nontrivial (R ⧸ m.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr m.isMaximal.ne_top
    exact ⟨⟨0, Module.finrank_pos⟩⟩
  refine ⟨M, inferInstance, L, fun m => inferInstance, hne,
    fun z m p q => (b m).repr (Ideal.Quotient.mk _ z * b m p) q, fun m p => (b m).repr 1 p, ?_⟩
  intro N hN v

  let e : M → R := fun m => (IsArtinianRing.equivPi R).symm (Pi.single m 1)
  have he : ∀ m, IsArtinianRing.equivPi R (e m) = Pi.single m 1 := fun m => AlgEquiv.apply_symm_apply _ _
  have hE1 : ∀ m, ∀ z ∈ m.asIdeal, z * e m = 0 := by
    intro m z hz
    apply (IsArtinianRing.equivPi R).injective
    funext m'
    rw [map_mul, he, map_zero, Pi.mul_apply, Pi.zero_apply]
    by_cases h : m' = m
    · subst h
      rw [Pi.single_eq_same, mul_one, IsArtinianRing.equivPi_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
    · rw [Pi.single_eq_of_ne h, mul_zero]
  have hE2 : ∑ m, e m = 1 := by
    apply (IsArtinianRing.equivPi R).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    funext m'
    rw [Finset.sum_apply, Finset.sum_eq_single m']
    · rw [he, Pi.single_eq_same, Pi.one_apply]
    · intro x _ hx
      rw [he, Pi.single_eq_of_ne (Ne.symm hx)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hE3 : ∀ m m', m' ≠ m → e m' * e m = 0 := by
    intro m m' hmm
    apply (IsArtinianRing.equivPi R).injective
    funext x
    rw [map_mul, he, he, map_zero, Pi.mul_apply, Pi.zero_apply]
    by_cases h : x = m
    · subst h
      rw [Pi.single_eq_of_ne hmm.symm, zero_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero]
  have hE4 : ∀ m, e m * e m = e m := by
    intro m
    apply (IsArtinianRing.equivPi R).injective
    funext x
    rw [map_mul, he, Pi.mul_apply]
    by_cases h : x = m
    · subst h
      rw [Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne h, mul_zero]

  let Vm : M → Submodule R V := fun m => LinearMap.range (LinearMap.lsmul R V (e m))
  have hself : ∀ m (y : V), e m • y ∈ Vm m := fun m y => LinearMap.mem_range_self _ y
  have hfix : ∀ m, ∀ y ∈ Vm m, e m • y = y := by
    rintro m y ⟨w, rfl⟩
    simp only [LinearMap.lsmul_apply, smul_smul, hE4]
  have hkill : ∀ m m', m' ≠ m → ∀ y ∈ Vm m, e m' • y = 0 := by
    rintro m m' hmm y ⟨w, rfl⟩
    simp only [LinearMap.lsmul_apply, smul_smul, hE3 m m' hmm, zero_smul]
  have htor : ∀ m, ∀ z ∈ m.asIdeal, ∀ y : Vm m, z • y = 0 := by
    intro m z hz y
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_zero, ← hfix m y.1 y.2, smul_smul, hE1 m z hz, zero_smul]
  haveI hVfin : ∀ m, FiniteDimensional k (Vm m) := fun m =>
    Module.Finite.of_injective ((Vm m).subtype.restrictScalars k) Subtype.val_injective
  have hNm : ∀ m, ∀ y ∈ Vm m, N y ∈ Vm m := by
    rintro m y ⟨w, rfl⟩
    rw [LinearMap.lsmul_apply, map_smul]
    exact hself m (N w)
  have hpow : ∀ m (j : ℕ) (y : Vm m), (((N.restrict (hNm m)) ^ j) y : V) = (N ^ j) y := by
    intro m j
    induction j with
    | zero => intro y; rfl
    | succ j ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl
  have hNnil : ∀ m, IsNilpotent (N.restrict (hNm m)) := by
    intro m
    obtain ⟨r, hr⟩ := hN
    refine ⟨r, LinearMap.ext fun y => Subtype.ext ?_⟩
    rw [hpow, hr]
    rfl
  have hblk (m : M) := dex_block_frame m.asIdeal (b m) (W := Vm m) (htor m) (N.restrict (hNm m)) (hNnil m)
    ⟨e m • v, hself m v⟩
  choose ι fι l s βm hl hs hZ hN' hv hA using hblk

  have hInt : DirectSum.IsInternal (fun m => (Vm m).restrictScalars k) := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_def]
      intro m
      let φ : V →ₗ[k] V := (LinearMap.lsmul R V (e m)).restrictScalars k
      have hle : (⨆ (j) (_ : j ≠ m), (Vm j).restrictScalars k) ≤ LinearMap.ker φ :=
        iSup₂_le fun j hj y hy => by
          rw [LinearMap.mem_ker]
          exact hkill j m (Ne.symm hj) y hy
      rw [Submodule.disjoint_def]
      intro y hy hy'
      have h1 := hle hy'
      rw [LinearMap.mem_ker] at h1
      rw [← hfix m y hy]
      exact h1
    · refine eq_top_iff.mpr fun y _ => ?_
      have hy : y = ∑ m, e m • y := by rw [← Finset.sum_smul, hE2, one_smul]
      rw [hy]
      exact Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m (hself m y)
  let eqv : ∀ m, (Vm m) ≃ₗ[k] ((Vm m).restrictScalars k) := fun m =>
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let β := hInt.collectedBasis (fun m => (βm m).map (eqv m))
  have hβ : ∀ m j, β ⟨m, j⟩ = ((βm m j : Vm m) : V) := by
    intro m j
    rw [DirectSum.IsInternal.collectedBasis_coe]
    rfl
  refine ⟨ι, fι, l, s, β, hl, hs, ?_, ?_, ?_, ?_⟩
  · intro z m p j
    rw [hβ, ← Submodule.coe_smul, hZ m z p j, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hβ]
    rfl
  · intro m p a i
    rw [hβ]
    have : N ((βm m (p, ⟨a, i⟩) : Vm m) : V) = ((N.restrict (hNm m) (βm m (p, ⟨a, i⟩)) : Vm m) : V) := rfl
    rw [this, hN' m p a i]
    split_ifs with h
    · rw [hβ]
    · rfl
  · have hvs : v = ∑ m, e m • v := by rw [← Finset.sum_smul, hE2, one_smul]
    conv_lhs => rw [hvs]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h1 : e m • v = ((⟨e m • v, hself m v⟩ : Vm m) : V) := rfl
    rw [h1, hv m, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rw [hβ]
      rfl
    · rfl
  · intro A hAN m p a i hi
    have hAm : ∀ m, ∀ y ∈ Vm m, A y ∈ Vm m := by
      rintro m y ⟨w, rfl⟩
      rw [LinearMap.lsmul_apply, map_smul]
      exact hself m (A w)
    have hvs : v = ∑ m, e m • v := by rw [← Finset.sum_smul, hE2, one_smul]
    have hAv : A v = ∑ m', ((A.restrict (hAm m') ⟨e m' • v, hself m' v⟩ : Vm m') : V) := by
      conv_lhs => rw [hvs]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hAv, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun m' _ => ?_
    by_cases hmm : m' = m
    · subst hmm
      have hc : A.restrict (hAm m') ∘ₗ N.restrict (hNm m') = N.restrict (hNm m') ∘ₗ A.restrict (hAm m') := by
        refine LinearMap.ext fun y => Subtype.ext ?_
        exact LinearMap.congr_fun hAN y.1
      have key := DirectSum.IsInternal.collectedBasis_repr_of_mem hInt (fun m => (βm m).map (eqv m))
        (x := ((A.restrict (hAm m') ⟨e m' • v, hself m' v⟩ : Vm m') : V)) (a := (p, ⟨a, i⟩)) (Subtype.mem _)
      refine key.trans ?_
      rw [Basis.map_repr]
      exact hA m' (A.restrict (hAm m')) hc p a i hi
    · exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne hInt _ hmm (Subtype.mem _)

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {k : Type} [Field k] {n : ℕ}

theorem exists_frames (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hr : IsReduced Z) :
    ∃ (M : Type) (_ : Fintype M) (L : M → Type) (_ : ∀ m, Fintype (L m)) (_ : ∀ m, Nonempty (L m))
      (R : Z → (m : M) → L m → L m → k) (o : (m : M) → L m → k),
      ∀ N : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * N = N * z) → IsNilpotent N → ∀ v : Fin n → k,
        Nonempty (Frame Z M L R o N v) := by
  letI iCR : CommRing Z :=
    { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  letI iM : Module Z (Fin n → k) := Module.compHom (Fin n → k)
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toRingHom.comp
      Z.val.toRingHom)
  have hsmul : ∀ (z : Z) (u : Fin n → k), z • u = (z : Matrix (Fin n) (Fin n) k) *ᵥ u := fun z u => rfl
  haveI iST : IsScalarTower k Z (Fin n → k) := ⟨fun c z u => by
    rw [hsmul, hsmul, Subalgebra.coe_smul]
    ext i
    simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]⟩
  obtain ⟨M, fM, L, fL, hne, Rc, o, H⟩ :=
    @dex_global k _ Z iCR (Subalgebra.algebra Z) inferInstance hr (Fin n → k) _ iM _ iST inferInstance
  refine ⟨M, fM, L, fL, hne, Rc, o, ?_⟩
  intro N hNZ hNnil v
  let toZ : (A : Matrix (Fin n) (Fin n) k) → (∀ z ∈ Z, z * A = A * z) → ((Fin n → k) →ₗ[Z] (Fin n → k)) :=
    fun A hA =>
      { toFun := fun u => A *ᵥ u
        map_add' := fun u w => mulVec_add A u w
        map_smul' := fun z u => by
          show A *ᵥ ((z : Matrix (Fin n) (Fin n) k) *ᵥ u) = (z : Matrix (Fin n) (Fin n) k) *ᵥ (A *ᵥ u)
          rw [mulVec_mulVec, mulVec_mulVec, hA z z.2] }
  have hpow : ∀ j : ℕ, ∀ u, ((toZ N hNZ) ^ j) u = (N ^ j) *ᵥ u := by
    intro j
    induction j with
    | zero => intro u; simp
    | succ j ih =>
      intro u
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', ← mulVec_mulVec]
      rfl
  have hnil : IsNilpotent (toZ N hNZ) := by
    obtain ⟨K, hK⟩ := hNnil
    exact ⟨K, LinearMap.ext fun u => by rw [hpow, hK, zero_mulVec]; rfl⟩
  obtain ⟨ι, fι, l, s, β, h1, h2, h3, h4, h5, h6⟩ := H (toZ N hNZ) hnil v
  have hA : ∀ (A : Matrix (Fin n) (Fin n) k), (∀ z ∈ Z, z * A = A * z) → A * N = N * A →
      ∀ (m : M) (p : L m) (a : ι m) (i : Fin (l m a)), (i : ℕ) < s m a →
        (β.repr (A *ᵥ v)) ⟨m, (p, ⟨a, i⟩)⟩ = 0 := by
    intro A hAZ hAN m p a i hi
    refine h6 (toZ A hAZ) (LinearMap.ext fun u => ?_) m p a i hi
    show A *ᵥ (N *ᵥ u) = N *ᵥ (A *ᵥ u)
    rw [mulVec_mulVec, mulVec_mulVec, hAN]
  exact ⟨@Frame.mk k _ n Z M fM L fL Rc o N v ι fι l s β h1 h2 (fun z m p j => h3 z m p j) h4 h5 hA⟩

end PositivityTheory.RgUd.T.Nil.Orb.BReps
