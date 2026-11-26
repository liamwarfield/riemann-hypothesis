module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupCastRight
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TorsOfForall
noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Adic

variable {l : ℕ} [Fact l.Prime]

section Mod
variable {M : Type*} [AddCommGroup M] [Module ℤ_[l] M]

theorem lsmul_eq {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (n : ℕ) (y : N) :
    (l : ℤ_[l]) ^ n • y = l ^ n • y := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

theorem pow_of_smul {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] {c : ℤ_[l]} (hc : c ≠ 0) {y : N}
    (h : c • y = 0) : ∃ n : ℕ, (l : ℤ_[l]) ^ n • y = 0 := by
  obtain ⟨u, v, hu⟩ : ∃ (u : ℤ_[l]ˣ) (v : ℕ), c = u * (l : ℤ_[l]) ^ v := ⟨_, _, PadicInt.unitCoeff_spec hc⟩
  subst hu
  refine ⟨v, ?_⟩
  have h2 : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (u * (l : ℤ_[l]) ^ v) = (l : ℤ_[l]) ^ v := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [← h2, mul_smul, h, smul_zero]

theorem l_ne_zero : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

theorem tors_of_forall [Module.Finite ℤ_[l] M] (x : M)
    (h : ∀ k : ℕ, ∃ w t : M, (∃ n : ℕ, (l : ℤ_[l]) ^ n • t = 0) ∧ x = (l : ℤ_[l]) ^ k • w + t) :
    ∃ n : ℕ, (l : ℤ_[l]) ^ n • x = 0 := by
  set T := Submodule.torsion' ℤ_[l] M (Submonoid.powers (l : ℤ_[l]))
  have hI : (Ideal.span {(l : ℤ_[l])}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, PadicInt.isUnit_iff, PadicInt.norm_p]
    have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact (inv_lt_one_of_one_lt₀ this).ne
  have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M ⧸ T) (Ideal.span {(l : ℤ_[l])}) hI
  have hx : T.mkQ x ∈ (⊥ : Submodule ℤ_[l] (M ⧸ T)) := by
    rw [← key, Submodule.mem_iInf]
    intro k
    obtain ⟨w, t, ⟨n, hn⟩, rfl⟩ := h k
    have ht : T.mkQ t = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion'_iff]
      exact ⟨⟨_, n, rfl⟩, hn⟩
    rw [map_add (f := _), ht, add_zero, map_smul]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion'_iff] at hx
  obtain ⟨⟨a, n, rfl⟩, ha⟩ := hx
  exact ⟨n, ha⟩

theorem cyclic_tors (g : M) (hg : ∀ x : M, ∃ c : ℤ_[l], x = c • g) :
    ∃ N : ℕ, ∀ t : M, (∃ n : ℕ, (l : ℤ_[l]) ^ n • t = 0) → (l : ℤ_[l]) ^ N • t = 0 := by
  by_cases h0 : ∃ n : ℕ, (l : ℤ_[l]) ^ n • g = 0
  · obtain ⟨N, hN⟩ := h0
    refine ⟨N, fun t _ => ?_⟩
    obtain ⟨c, rfl⟩ := hg t
    rw [smul_comm, hN, smul_zero]
  · refine ⟨0, fun t ⟨n, hn⟩ => ?_⟩
    obtain ⟨c, rfl⟩ := hg t
    rw [smul_smul] at hn
    by_cases hc : (l : ℤ_[l]) ^ n * c = 0
    · have : c = 0 := by
        rcases mul_eq_zero.1 hc with h | h
        · exact absurd h (pow_ne_zero _ l_ne_zero)
        · exact h
      simp [this]
    · exact absurd (pow_of_smul hc hn) h0

theorem isLoc : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange ℤ_[l] M ℚ_[l])

theorem tmul_surj (v : ℚ_[l] ⊗[ℤ_[l]] M) : ∃ (c : ℚ_[l]) (x : M), v = c ⊗ₜ x := by
  have hL := isLoc (l := l) (M := M)
  obtain ⟨⟨x, s⟩, hv⟩ := IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) v
  refine ⟨(algebraMap ℤ_[l] ℚ_[l] s)⁻¹, x, ?_⟩
  rw [← hv]
  simp only [Function.uncurry_apply_pair]
  rw [IsLocalizedModule.mk'_eq_iff, TensorProduct.mk_apply, Submonoid.smul_def, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_inv_cancel₀]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2

theorem tmul_eq_zero (x : M) : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x = 0 ↔ ∃ n : ℕ, (l : ℤ_[l]) ^ n • x = 0 := by
  have hL := isLoc (l := l) (M := M)
  have e := IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) (m := x)
  rw [TensorProduct.mk_apply] at e
  rw [e]
  constructor
  · rintro ⟨s, hs⟩
    exact pow_of_smul (nonZeroDivisors.ne_zero s.2) hs
  · rintro ⟨n, hn⟩
    exact ⟨⟨_, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n l_ne_zero)⟩, hn⟩

theorem fd [Module.Finite ℤ_[l] M] : FiniteDimensional ℚ_[l] (ℚ_[l] ⊗[ℤ_[l]] M) := inferInstance

end Mod

theorem span_dual {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : Set (Module.Dual K V)) (h : ∀ v, (∀ f ∈ F, f v = 0) → v = 0) : Submodule.span K F = ⊤ := by
  set W := Submodule.span K F
  have h1 : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact (Submodule.mem_bot K).2 (h v fun f hf => hv f (Submodule.subset_span hf))
  have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
  rw [h1, Submodule.dualAnnihilator_bot] at this
  exact this.symm

theorem pair_tors {A B C : ℕ → Type*} [∀ k, AddCommGroup (A k)] [∀ k, Module ℤ_[l] (A k)]
    [∀ k, AddCommGroup (B k)] [∀ k, Module ℤ_[l] (B k)] [∀ k, AddCommGroup (C k)] [∀ k, Module ℤ_[l] (C k)]
    {ρA : ∀ m n, A m →+ A n} {ρB : ∀ m n, B m →+ B n} {ρC : ∀ m n, C m →+ C n}
    {SA : Submodule ℤ_[l] (∀ k, A k)} {SB : Submodule ℤ_[l] (∀ k, B k)} {SC : Submodule ℤ_[l] (∀ k, C k)}
    (hA : IsSys l A ρA) (hB : IsSys l B ρB) (hC : IsSys l C ρC)
    (hSA : ∀ x, x ∈ SA ↔ ∀ k, ρA (k + 1) k (x (k + 1)) = x k)
    (hSB : ∀ x, x ∈ SB ↔ ∀ k, ρB (k + 1) k (x (k + 1)) = x k)
    (hSC : ∀ x, x ∈ SC ↔ ∀ k, ρC (k + 1) k (x (k + 1)) = x k)
    (μ : ∀ k, A k →+ B k →+ C k)
    (hμ : ∀ m n (a : A m) (b : B m), n ≤ m → ρC m n (μ m a b) = μ n (ρA m n a) (ρB m n b))
    (hnd : ∀ k (a : A k), (∀ b, μ k a b = 0) → a = 0)
    (hcyc : ∃ g ∈ SC, ∀ z ∈ SC, ∃ c : ℤ_[l], z = c • g)
    {x : ∀ k, A k} (hx : x ∈ SA)
    (h : ∀ y ∈ SB, ∃ n : ℕ, (l : ℤ_[l]) ^ n • (fun k => μ k (x k) (y k)) = 0) :
    ∃ n : ℕ, (l : ℤ_[l]) ^ n • x = 0 := by
  classical
  have := hA.finite hSA
  obtain ⟨g, hgS, hg⟩ := hcyc
  obtain ⟨N, hN⟩ := cyclic_tors (M := SC) ⟨g, hgS⟩ (fun z => by
    obtain ⟨c, hc⟩ := hg z z.2
    exact ⟨c, Subtype.ext (by simpa using hc)⟩)
  have hN' : ∀ z ∈ SC, (∃ n : ℕ, (l : ℤ_[l]) ^ n • z = 0) → (l : ℤ_[l]) ^ N • z = 0 := by
    rintro z hz ⟨n, hn⟩
    have := hN ⟨z, hz⟩ ⟨n, Subtype.ext (by simpa using hn)⟩
    simpa using congrArg Subtype.val this
  have hP : ∀ y ∈ SB, (fun k => μ k (x k) (y k)) ∈ SC := by
    intro y hy
    rw [hSC]
    intro k
    show ρC (k + 1) k (μ (k + 1) (x (k + 1)) (y (k + 1))) = μ k (x k) (y k)
    rw [hμ _ _ _ _ (Nat.le_succ k), (hSA x).1 hx k, (hSB y).1 hy k]
  set x' := (l : ℤ_[l]) ^ N • x with hx'def
  have hx' : x' ∈ SA := SA.smul_mem _ hx
  have hvan : ∀ y ∈ SB, ∀ k, μ k (x' k) (y k) = 0 := by
    intro y hy k
    have h2 := congrFun (hN' _ (hP y hy) (h y hy)) k
    simp only [Pi.smul_apply, Pi.zero_apply] at h2
    rw [hx'def, Pi.smul_apply, lsmul_eq, map_nsmul, AddMonoidHom.nsmul_apply, ← lsmul_eq]
    exact h2
  have key : ∀ k : ℕ, ∃ w t : SA, (∃ n : ℕ, (l : ℤ_[l]) ^ n • t = 0) ∧
      (⟨x', hx'⟩ : SA) = (l : ℤ_[l]) ^ k • w + t := by
    intro k
    obtain ⟨a, ha⟩ := hB.ml hSB k
    have hz : l ^ a • x' (k + a) = 0 := by
      apply hnd
      intro b
      obtain ⟨y, hy, hyk⟩ := ha b
      have hb0 : ρC (k + a) k (μ (k + a) (x' (k + a)) b) = 0 := by
        rw [hμ _ _ _ _ (Nat.le_add_right k a), hA.compat hSA hx' (Nat.le_add_right k a), ← hyk]
        exact hvan y hy k
      have hbk : ∀ m (z : C m), m = a + k → ρC m k z = 0 → l ^ a • z = 0 := by
        intro m z hm hz0
        subst hm
        exact (hC.bock a k z hz0).1
      rw [map_nsmul, AddMonoidHom.nsmul_apply]
      exact hbk _ _ (Nat.add_comm k a) hb0
    have hw : (l : ℤ_[l]) ^ a • x' ∈ SA := SA.smul_mem _ hx'
    obtain ⟨v, hv, hve⟩ := hA.ker hSA hw (k + a) (by rw [Pi.smul_apply, lsmul_eq]; exact hz)
    refine ⟨⟨v, hv⟩, ⟨x' - (l : ℤ_[l]) ^ k • v, SA.sub_mem hx' (SA.smul_mem _ hv)⟩, ⟨a, ?_⟩, ?_⟩
    · apply Subtype.ext
      show (l : ℤ_[l]) ^ a • (x' - (l : ℤ_[l]) ^ k • v) = 0
      rw [smul_sub, hve, smul_smul, ← pow_add, add_comm a k, sub_self]
    · apply Subtype.ext
      show x' = (l : ℤ_[l]) ^ k • v + (x' - (l : ℤ_[l]) ^ k • v)
      abel
  obtain ⟨n, hn⟩ := tors_of_forall (M := SA) ⟨x', hx'⟩ key
  have hn' : (l : ℤ_[l]) ^ n • x' = 0 := by simpa using congrArg Subtype.val hn
  exact ⟨n + N, by rw [pow_add, mul_smul]; exact hn'⟩

end CrystallineSemistableComparison.Adic
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PowMonoTors
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem pow_mono_tors {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (y : N) {m n : ℕ} (h : m ≤ n)
    (hy : (l : ℤ_[l]) ^ m • y = 0) : (l : ℤ_[l]) ^ n • y = 0 := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_smul, hy, smul_zero]

theorem tors_of_tmul {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (hc : c ≠ 0) (y : N)
    (h : c ⊗ₜ[ℤ_[l]] y = 0) : ∃ n : ℕ, (l : ℤ_[l]) ^ n • y = 0 := by
  refine (Adic.tmul_eq_zero y).1 ?_
  have e : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = c⁻¹ • (c ⊗ₜ[ℤ_[l]] y) := by
    rw [smul_tmul', smul_eq_mul, inv_mul_cancel₀ hc]
  rw [e, h, smul_zero]

theorem tmul_zero_of {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (y : N) {n : ℕ}
    (h : (l : ℤ_[l]) ^ n • y = 0) : c ⊗ₜ[ℤ_[l]] y = 0 := by
  have h1 : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = 0 := (Adic.tmul_eq_zero y).2 ⟨_, h⟩
  rw [← mul_one c, ← smul_eq_mul, ← smul_tmul', h1, smul_zero]

theorem unit_geom (M : Model l K) : IsUnit ((l : ℕ) : Γ(GlobalTheory.Et.geom (PadicAlgCl l) M.q, ⊤)) := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact AdicGeo.unit_of_over (AdicGeo.str M) l

theorem fin_levels (hI : ZIn) (M : Model l K) (h : M.Good) (n i : ℤ) (k : ℕ) :
    Finite (Ht (l ^ k) (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) n i) := by
  have := AdicGeo.proper_str h
  have := neZero_pow l k
  have hu : IsUnit ((l ^ k : ℕ) : PadicAlgCl l) := (Nat.cast_ne_zero.2 (NeZero.ne _)).isUnit
  exact hI.e4 (l ^ k) (PadicAlgCl l) hu (AdicGeo.str M) n i

theorem fin_of (hI : ZIn) (M : Model l K) (h : M.Good) (j : ℕ) : FiniteDimensional ℚ_[l] (M.V j) := by
  have hS := isSys l hI _ (unit_geom M) (j : ℤ) 0 (fin_levels hI M h _ _)
  have : Module.Finite ℤ_[l] (Hl l (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) (j : ℤ) 0) :=
    hS.finite (fun _ => Iff.rfl)
  exact Adic.fd

theorem comp_of (hI : ZIn) (G : Model l K → Prop) (hG : ∀ M, G M → M.Good) (hC : CompM G) (M : Model l K) (hM : G M) :
    ∃ (r : ℕ) (P : Fin r → Model l K) (d : Fin r → ℕ) (u : ∀ a, (P a).X ⟶ M.X)
    (hu : ∀ a, u a ≫ M.p = (P a).p), (∀ a, G (P a) ∧ (P a).Conn (d a)) ∧
    ∀ (j : ℕ) (v : M.V j), (∀ a, Model.pullV (u a) (hu a) j v = 0) → v = 0 := by
  obtain ⟨r, P, d, u, hu, hsum, hP⟩ := hC M hM
  refine ⟨r, P, d, u, hu, hP, fun j v hv => ?_⟩
  have hs := AdicGeo.isSum_geom u hu hsum
  obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
  by_cases hc : c = 0
  · rw [hc, zero_tmul]
  have ht : ∀ a, ∃ n : ℕ, (l : ℤ_[l]) ^ n • pullHl l (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) (P a).q
      (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a)))) j 0 x = 0 := fun a =>
    tors_of_tmul c hc _ ((LinearMap.baseChange_tmul _ _ _).symm.trans (hv a))
  choose n hn using ht
  refine tmul_zero_of c x (n := ∑ a, n a) (sum_inj l hI _ hs j 0 _ fun a => ?_)
  refine ((pullHl l _ j 0).map_smul _ x).trans ?_
  exact pow_mono_tors _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (hn a)

end CrystallineSemistableComparison.AdicCoh
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TmulEqSmulToV
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupLZeroRight
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.HeqOfEqCast
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace CrystallineSemistableComparison.AdicCoh

section Heq
variable {q : ℕ} {E : Spc}

theorem eq_cast_of_heq {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') {x : Ht q E n' i'} {y : Ht q E n i} (h : HEq x y) :
    x = y.cast h1 h2 := by
  exact eq_of_heq (h.trans (cast_heq h1 h2 y).symm)

theorem heq_zero {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') {x : Ht q E n i} (h : HEq x (0 : Ht q E n' i')) : x = 0 := by
  subst h1 h2
  exact eq_of_heq h

theorem cup_heq {n m i j n' m' i' j' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : m = m') (h4 : j = j')
    {a : Ht q E n i} {a' : Ht q E n' i'} {b : Ht q E m j} {b' : Ht q E m' j'} (ha : HEq a a') (hb : HEq b b') :
    HEq (cup q a b) (cup q a' b') := by
  subst h1 h2 h3 h4
  cases ha
  cases hb
  exact HEq.rfl

end Heq

section Root
variable (q : ℕ) [NeZero q] {E : Spc} (hR : GlobalTheory.EtC.DivisorRingCompatibility) (hinv : Inv q E) {e : ℤ} (u : Ht q E 0 e) (v : Ht q E 0 (-e))
include hR hinv

theorem cup_one_right {n i : ℤ} (b : Ht q E n i) : HEq (cup q b (one q E)) b := by
  obtain ⟨h1, -, h3⟩ := hR q E
  rw [h3 b (one q E), h1 hinv b]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact (cast_heq _ _ _).trans (cast_heq _ _ _)

theorem root_left (hvu : cup q v u = (one q E).cast (by ring) (by ring)) {n i : ℤ} (b : Ht q E n i) :
    HEq (cup q (cup q b v) u) b := by
  obtain ⟨-, h2, -⟩ := hR q E
  rw [h2 b v u, hvu, cup_cast_right]
  exact (cast_heq _ _ _).trans ((cast_heq _ _ _).trans (cup_one_right q hR hinv b))

theorem root_right (hvu : cup q v u = (one q E).cast (by ring) (by ring)) {n i : ℤ} (b : Ht q E n i) :
    HEq (cup q (cup q b u) v) b := by
  obtain ⟨-, h2, h3⟩ := hR q E
  rw [h2 b u v, h3 u v, hvu]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, cast_cast, cup_cast_right]
  exact (cast_heq _ _ _).trans (cup_one_right q hR hinv b)

end Root

section PD
variable {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Spec (CommRingCat.of k)) [IsProper p]
  (d : ℕ) [SmoothOfRelativeDimension d p] (q : ℕ) [NeZero q] (hq : IsUnit (q : k))
include p hq

theorem vanish (hI : ZIn) (n : ℤ) (hn : 2 * (d : ℤ) < n) : Subsingleton (Ht q (sch.obj Y) n 0) := by
  obtain ⟨tr, htr⟩ := hI.e8 q k hq p d
  haveI : Subsingleton (Ht q (sch.obj Y) (2 * d - n) (d - 0)) :=
    (hI.a9 (ZMod q) (tw q ((d : ℤ) - 0))).1 _ _ (by omega)
  obtain ⟨c, -, hc⟩ := htr n 0 0
  refine ⟨fun a b => (hc a fun y => ?_).trans (hc b fun y => ?_).symm⟩ <;>
    simp [Subsingleton.elim y 0, cast_zero]

theorem nondeg (hI : ZIn) (hprim : Nonempty (Prim q Γ(Y, ⊤))) (hinv : Inv q (sch.obj Y)) (i j : ℤ) (hij : i + j = 2 * d)
    (a : Ht q (sch.obj Y) i 0) (h : ∀ b : Ht q (sch.obj Y) j 0, cup q a b = 0) : a = 0 := by
  obtain ⟨tr, htr⟩ := hI.e8 q k hq p d
  obtain ⟨u, v, hvu⟩ := hI.root q Y hprim (d : ℤ)
  have key : ∀ b' : Ht q (sch.obj Y) (2 * d - i) (d - 0), cup q a b' = 0 := by
    intro b'
    have hc := h ((cup q b' v).cast (by omega) (by omega))
    have s1 : cup q a (cup q b' v) = 0 :=
      heq_zero (by omega) (by omega)
        ((cup_heq rfl rfl (by omega) (by omega) HEq.rfl (cast_heq _ _ _).symm).trans (heq_of_eq hc))
    have s3 : cup q (cup q a (cup q b' v)) u = 0 := by rw [s1, map_zero, AddMonoidHom.zero_apply]
    have s4 : HEq (cup q a (cup q (cup q b' v) u)) (cup q (cup q a (cup q b' v)) u) := by
      rw [(hI.ring q _).2.1 a (cup q b' v) u]
      exact (cast_heq _ _ _).symm
    exact heq_zero (by omega) (by omega)
      ((cup_heq rfl rfl (by omega) (by omega) HEq.rfl (root_left q hI.ring hinv u v hvu b').symm).trans
        (s4.trans (heq_of_eq s3)))
  obtain ⟨c, -, hc⟩ := htr i 0 0
  have ha : a = c := hc a (fun b => by simp [key b, cast_zero])
  have h0 : (0 : Ht q (sch.obj Y) i 0) = c := hc 0 (fun b => by simp [cast_zero])
  exact ha.trans h0.symm

theorem top_cyclic (hI : ZIn) (hprim : Nonempty (Prim q Γ(Y, ⊤))) (hinv : Inv q (sch.obj Y)) :
    ∃ g : Ht q (sch.obj Y) (2 * d) 0, ∀ x, ∃ n : ℤ, x = n • g := by
  obtain ⟨tr, -⟩ := hI.e8 q k hq p d
  obtain ⟨u, v, hvu⟩ := hI.root q Y hprim (d : ℤ)
  refine ⟨(cup q (tr.symm 1) v).cast (by ring) (by ring), fun x => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      ((cup q x u).cast (by ring) (by ring) : Ht q (sch.obj Y) (2 * d) d) = m • tr.symm 1 := by
    refine ⟨((tr ((cup q x u).cast (by ring) (by ring))).val : ℤ), tr.injective ?_⟩
    rw [map_zsmul, AddEquiv.apply_symm_apply, zsmul_one, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨m, ?_⟩
  have hc : cup q (m • tr.symm 1) v = m • cup q (tr.symm 1) v := by
    rw [map_zsmul]
    rfl
  rw [← cast_smul]
  refine eq_cast_of_heq _ _ ?_
  refine (root_right q hI.ring hinv u v hvu x).symm.trans ?_
  rw [← hc, ← hm]
  exact cup_heq (by ring) (by ring) rfl rfl (cast_heq _ _ _).symm HEq.rfl

end PD

end CrystallineSemistableComparison.AdicCoh
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable (l : ℕ) [Fact l.Prime]

theorem castH_apply {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) :
    castH h1 h2 x = x.cast h1 h2 := rfl

section Cup
variable {E : Spc} {n m i j n' i' : ℤ} (hI : ZIn) (h1 : n + m = n') (h2 : i + j = i')

def cupL (x : Hl l E n i) (y : Hl l E m j) : Hl l E n' i' := ⟨_, cup_mem l hI E h1 h2 x y⟩

theorem pull_cupL {E' : Spc} (f : E' ⟶ E) (x : Hl l E n i) (y : Hl l E m j) :
    pullHl l f n' i' (cupL l hI h1 h2 x y) = cupL l hI h1 h2 (pullHl l f n i x) (pullHl l f m j y) := by
  apply Subtype.ext
  funext k
  have := neZero_pow l k
  change pull _ f _ n' ((cup _ _ _).cast h1 h2) = (cup _ (pull _ f _ n _) (pull _ f _ m _)).cast h1 h2
  rw [pull_cast, (hI.nat (l ^ k)).1 f]

theorem cupL_zero_right (x : Hl l E n i) : cupL l hI h1 h2 x (0 : Hl l E m j) = 0 := by
  apply Subtype.ext
  funext k
  change (cup _ _ 0).cast h1 h2 = 0
  rw [map_zero, cast_zero]

theorem cupL_add_left (x x' : Hl l E n i) (y : Hl l E m j) :
    cupL l hI h1 h2 (x + x') y = cupL l hI h1 h2 x y + cupL l hI h1 h2 x' y := by
  apply Subtype.ext
  funext k
  change (cup _ (x.1 k + x'.1 k) (y.1 k)).cast h1 h2 = (cup _ _ _).cast h1 h2 + (cup _ _ _).cast h1 h2
  rw [map_add (f := _), AddMonoidHom.add_apply, cast_add]

theorem cupL_smul_left (r : ℤ_[l]) (x : Hl l E n i) (y : Hl l E m j) :
    cupL l hI h1 h2 (r • x) y = r • cupL l hI h1 h2 x y := by
  apply Subtype.ext
  funext k
  change (cup _ (r • x.1 k) (y.1 k)).cast h1 h2 = r • (show HtL l k E n' i' from (cup _ (x.1 k) (y.1 k)).cast h1 h2)
  rw [HtL.smul_eq l k k le_rfl E n i r (x.1 k), HtL.smul_eq l k k le_rfl E n' i' r]
  erw [map_nsmul, AddMonoidHom.nsmul_apply, cast_nsmul]

def cupR (y : Hl l E m j) : Hl l E n i →ₗ[ℤ_[l]] Hl l E n' i' where
  toFun x := cupL l hI h1 h2 x y
  map_add' x x' := cupL_add_left l hI h1 h2 x x' y
  map_smul' r x := cupL_smul_left l hI h1 h2 r x y

end Cup

section Sum
variable (hI : ZIn) {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (hj : IsSum j) (n i : ℤ)
include hI hj

theorem sum_eq (x x' : Hl l (sch.obj X) n i) (h : ∀ s, pullHl l (sch.map (j s)) n i x = pullHl l (sch.map (j s)) n i x') :
    x = x' :=
  sub_eq_zero.1 (sum_inj l hI j hj n i _ fun s => by rw [map_sub, h, sub_self])

def extS (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) : Hl l (sch.obj X) n i :=
  (sum_ext l hI j hj n i (Pi.single (M := fun t => Hl l (sch.obj (Y t)) n i) s y)).choose

theorem extS_spec (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) (t : Fin r) :
    pullHl l (sch.map (j t)) n i (extS l hI j hj n i s y) = Pi.single (M := fun t => Hl l (sch.obj (Y t)) n i) s y t :=
  (sum_ext l hI j hj n i (Pi.single (M := fun t => Hl l (sch.obj (Y t)) n i) s y)).choose_spec t

theorem extS_self (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) :
    pullHl l (sch.map (j s)) n i (extS l hI j hj n i s y) = y := by
  rw [extS_spec]; exact Pi.single_eq_same _ _

theorem extS_ne (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) {t : Fin r} (ht : t ≠ s) :
    pullHl l (sch.map (j t)) n i (extS l hI j hj n i s y) = 0 := by
  rw [extS_spec]; exact Pi.single_eq_of_ne ht _

theorem tors_of_restr (x : Hl l (sch.obj X) n i) (h : ∀ s, ∃ e : ℕ, (l : ℤ_[l]) ^ e • pullHl l (sch.map (j s)) n i x = 0) :
    ∃ e : ℕ, (l : ℤ_[l]) ^ e • x = 0 := by
  choose e he using h
  refine ⟨∑ s, e s, sum_inj l hI j hj n i _ fun s => ?_⟩
  rw [map_smul, ← Finset.add_sum_erase _ _ (Finset.mem_univ s), pow_add, mul_comm, mul_smul, he, smul_zero]

end Sum

theorem unitQ (k : ℕ) : IsUnit (((l ^ k : ℕ) : ℕ) : PadicAlgCl l) :=
  isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (pow_ne_zero k (Fact.out : l.Prime).ne_zero))

section Y
variable (hI : ZIn) {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of (PadicAlgCl l))) [IsProper p]
include hI p

theorem ysys (n i : ℤ) : Adic.IsSys l (fun k => HtL l k (sch.obj Y) n i) (fun m m' => red (l ^ m) (l ^ m') (sch.obj Y) n i) := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  refine isSys l hI Y (AdicGeo.unit_of_over p l) n i fun k => ?_
  have := neZero_pow l k
  exact hI.e4 (l ^ k) (PadicAlgCl l) (unitQ l k) p n i

variable [IsIntegral Y] (d : ℕ) [SmoothOfRelativeDimension d p]

theorem hl_vanish (n : ℤ) (hn : 2 * (d : ℤ) < n) : Subsingleton (Hl l (sch.obj Y) n 0) := by
  refine ⟨fun x y => Subtype.ext (funext fun k => ?_)⟩
  have := neZero_pow l k
  exact (vanish p d (l ^ k) (unitQ l k) hI n hn).elim _ _

theorem hl_cyclic (N : ℤ) (hN : N = 2 * d) : ∃ g : Hl l (sch.obj Y) N 0, ∀ x, ∃ c : ℤ_[l], x = c • g := by
  subst hN
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have := neZero_pow l 1
  obtain ⟨g, hg, hc⟩ := (ysys l hI p _ 0).cyclic (S := HlSub l (sch.obj Y) _ 0) (fun _ => Iff.rfl)
    (top_cyclic p d (l ^ 1) (unitQ l 1) hI (AdicGeo.prim_of_over p _) (AdicGeo.inv_sch _ (AdicGeo.unit_of_over p _)))
  refine ⟨⟨g, hg⟩, fun x => ?_⟩
  obtain ⟨c, e⟩ := hc x.1 x.2
  exact ⟨c, Subtype.ext e⟩

theorem hl_nondeg (i j N : ℤ) (hij : i + j = N) (hN : N = 2 * d) (x : Hl l (sch.obj Y) i 0)
    (h : ∀ y : Hl l (sch.obj Y) j 0, ∃ e : ℕ, (l : ℤ_[l]) ^ e • cupL l hI hij (add_zero 0) x y = 0) :
    ∃ e : ℕ, (l : ℤ_[l]) ^ e • x = 0 := by
  obtain ⟨g, hg⟩ := hl_cyclic l hI p d N hN
  have hnd : ∀ k (a : HtL l k (sch.obj Y) i 0),
      (∀ b : HtL l k (sch.obj Y) j 0, ((cup (l ^ k)).compr₂ (castH hij (add_zero (0 : ℤ)))) a b = 0) → a = 0 := by
    intro k a hb
    have := neZero_pow l k
    exact nondeg p d (l ^ k) (unitQ l k) hI (AdicGeo.prim_of_over p _) (AdicGeo.inv_sch _ (AdicGeo.unit_of_over p _))
      i j (hij.trans hN) a fun b => (cast_eq_zero _ _ _).1 (by simpa only [AddMonoidHom.compr₂_apply, castH_apply] using hb b)
  obtain ⟨e, he⟩ := Adic.pair_tors (ysys l hI p i 0) (ysys l hI p j 0) (ysys l hI p N 0)
    (SA := HlSub l (sch.obj Y) i 0) (SB := HlSub l (sch.obj Y) j 0) (SC := HlSub l (sch.obj Y) N 0)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (fun k => (cup (l ^ k)).compr₂ (castH hij (add_zero (0 : ℤ))))
    (fun m n a b hmn => by
      have := neZero_pow l m
      simp only [AddMonoidHom.compr₂_apply]
      show red (l ^ m) (l ^ n) (sch.obj Y) N 0 (Ht.cast hij (add_zero 0) (cup (l ^ m) a b)) =
        Ht.cast hij (add_zero 0) (cup (l ^ n) (red (l ^ m) (l ^ n) _ i 0 a) (red (l ^ m) (l ^ n) _ j 0 b))
      rw [red_cast, (hI.a11 (l ^ m) (l ^ n) (pow_dvd_pow l hmn) _).1])
    hnd ⟨g.1, g.2, fun z hz => by obtain ⟨c, e⟩ := hg ⟨z, hz⟩; exact ⟨c, congrArg Subtype.val e⟩⟩ x.2
    (fun y hy => by
      obtain ⟨e, he⟩ := h ⟨y, hy⟩
      exact ⟨e, congrArg Subtype.val he⟩)
  exact ⟨e, Subtype.ext he⟩

end Y

end CrystallineSemistableComparison.AdicCoh
end
end

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem gen_tmul_smul {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (a : ℤ_[l]) (y : N) :
    (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (a • y) = algebraMap ℤ_[l] ℚ_[l] a • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
  rw [tmul_smul, algebraMap_smul]

theorem gen_tmul_eq {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (y : N) :
    c ⊗ₜ[ℤ_[l]] y = c • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
  rw [smul_tmul', smul_eq_mul, mul_one]

theorem toV_smul (M : Model l K) (n : ℕ) (a : ℤ_[l]) (x : M.T n) :
    M.toV n (a • x) = algebraMap ℤ_[l] ℚ_[l] a • M.toV n x :=
  gen_tmul_smul (N := Hl l M.spc n 0) a x

theorem tmul_eq_smul_toV (M : Model l K) (n : ℕ) (c : ℚ_[l]) (x : M.T n) :
    (c ⊗ₜ[ℤ_[l]] (show Hl l M.spc n 0 from x) : M.V n) = c • M.toV n x :=
  gen_tmul_eq (N := Hl l M.spc n 0) c x

theorem pull_gal_inj (M : Model l K) (n : ℤ) (τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (x : Hl l M.spc n 0)
    (h : pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ)) n 0 x = 0) : x = 0 := by
  have e := congrArg (pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ⁻¹)) n 0) h
  rw [← LinearMap.comp_apply, ← pullHl_comp, ← Functor.map_comp, ← galMap_mul, inv_mul_cancel, galMap_one,
    CategoryTheory.Functor.map_id, pullHl_id, map_zero] at e
  exact e

theorem pull_comp_apply {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) (x : Hl l E'' n i) :
    pullHl l (f ≫ g) n i x = pullHl l f n i (pullHl l g n i x) := by
  rw [pullHl_comp]; rfl

end CrystallineSemistableComparison.AdicCoh
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GenBaseChange
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem gen_tmul_smul2 {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (a : ℤ_[l]) (y : N) :
    c ⊗ₜ[ℤ_[l]] (a • y) = (c * algebraMap ℤ_[l] ℚ_[l] a) • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
  rw [tmul_smul, ← algebraMap_smul ℚ_[l] a, smul_tmul', smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_comm]

theorem gen_smul_zero {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℤ_[l]) : c • (0 : N) = 0 := smul_zero c

theorem gen_baseChange {N N' : Type*} [AddCommGroup N] [Module ℤ_[l] N] [AddCommGroup N'] [Module ℤ_[l] N']
    (f : N →ₗ[ℤ_[l]] N') (y : N) : f.baseChange ℚ_[l] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] f y :=
  LinearMap.baseChange_tmul _ _ _

theorem gen_sum_smul {N N' : Type*} [AddCommGroup N] [Module ℤ_[l] N] [AddCommGroup N'] [Module ℤ_[l] N'] {r : ℕ}
    (a : Fin r → ℤ_[l]) (e : Fin r → N) (f : N →ₗ[ℤ_[l]] N') (t : Fin r) (g : N') (h1 : f (e t) = g)
    (h2 : ∀ s, s ≠ t → f (e s) = 0) : f (∑ s, a s • e s) = a t • g := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single t (fun s _ hs => by rw [map_smul, h2 s hs, smul_zero])
    (fun h => absurd (Finset.mem_univ t) h), map_smul, h1]

theorem gen_span (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (n : ℕ) (gen : ∀ s, Hl l (sch.obj (Y s)) (n : ℤ) 0)
    (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) :
    Submodule.span ℚ_[l] (Set.range fun s => M.toV n (extS l hI j hj _ 0 s (gen s))) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
  choose a ha using fun s => hgen s (pullHl l (sch.map (j s)) n 0 x)
  have hx : x = ∑ s, a s • extS l hI j hj _ 0 s (gen s) := by
    refine sum_eq l hI j hj _ 0 _ _ fun t => ?_
    rw [ha t]
    exact (gen_sum_smul a _ _ t _ (extS_self l hI j hj _ 0 t (gen t))
      (fun s hs => extS_ne l hI j hj _ 0 s (gen s) (Ne.symm hs))).symm
  rw [hx, tmul_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [gen_tmul_smul2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

theorem gal_step (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (hint : ∀ s, IsIntegral (Y s))
    (hperm : ∀ σ : K.fixingSubgroup, ∃ (π : Equiv.Perm (Fin r)) (θ : ∀ s, Y s ≅ Y (π s)),
      ∀ s, j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = (θ s).hom ≫ j (π s))
    (htrans : ∀ s s', ∃ (σ : K.fixingSubgroup) (θ : Y s ⟶ Y s'),
      j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = θ ≫ j s')
    (n : ℕ) (gen : ∀ s, Hl l (sch.obj (Y s)) (n : ℤ) 0) (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) (s s' : Fin r) :
    ∃ (σ : K.fixingSubgroup) (c : ℤ_[l]),
      pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ))) n 0
        (extS l hI j hj _ 0 s (gen s)) = c • extS l hI j hj _ 0 s' (gen s') := by
  obtain ⟨σ, θ, hθ⟩ := htrans s' s
  obtain ⟨π, θ', hθ'⟩ := hperm σ
  have hπ : π s' = s := by
    have := hint s'
    obtain ⟨y⟩ := (inferInstance : Nonempty (Y s'))
    by_contra hne
    have e1 := congrArg (fun f : Y s' ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q => f y) (hθ.symm.trans (hθ' s'))
    simp only [Scheme.Hom.comp_apply] at e1
    exact Set.disjoint_left.1 (hj.2.2 s (π s') (Ne.symm hne)) ⟨_, rfl⟩ ⟨_, e1.symm⟩
  obtain ⟨c, hc⟩ := hgen s' (pullHl l (sch.map θ) n 0 (gen s))
  refine ⟨σ, c, sum_eq l hI j hj _ 0 _ _ fun t => ?_⟩
  rw [← pull_comp_apply, ← Functor.map_comp]
  obtain rfl | ht := eq_or_ne t s'
  · rw [hθ, Functor.map_comp, pull_comp_apply, extS_self, hc, LinearMap.map_smul, extS_self]
  · have hne : π t ≠ s := fun h => ht (π.injective (h.trans hπ.symm))
    rw [hθ' t, Functor.map_comp, pull_comp_apply, extS_ne l hI j hj _ 0 s _ hne, map_zero, LinearMap.map_smul,
      extS_ne l hI j hj _ 0 _ _ ht]
    exact (gen_smul_zero (N := Hl l (sch.obj (Y t)) n 0) c).symm

end CrystallineSemistableComparison.AdicCoh
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GsmulZero
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
  (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (i j' : ℕ)
  (gen : ∀ s, Hl l (sch.obj (Y s)) ((i + j' : ℕ) : ℤ) 0) (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s)

theorem gsmul_zero {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (a : ℤ_[l]) : a • (0 : N) = 0 := smul_zero a

theorem hsum_ij : ((i : ℕ) : ℤ) + ((j' : ℕ) : ℤ) = ((i + j' : ℕ) : ℤ) := by push_cast; rfl

include hgen in
theorem phi_form (s : Fin r) (y' : Hl l (sch.obj (Y s)) j' 0) (x : M.T i) :
    ∃ a : ℤ_[l], cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y') =
      a • extS l hI j hj _ 0 s (gen s) := by
  obtain ⟨a, ha⟩ := hgen s (pullHl l (sch.map (j s)) _ 0
    (cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y')))
  refine ⟨a, sum_eq l hI j hj _ 0 _ _ fun t => ?_⟩
  rw [LinearMap.map_smul]
  by_cases ht : t = s
  · subst ht
    rw [ha, extS_self]
  · rw [pull_cupL, extS_ne l hI j hj j' 0 s y' ht, cupL_zero_right, extS_ne l hI j hj _ 0 s (gen s) ht]
    exact (gsmul_zero (N := Hl l (sch.obj (Y t)) ((i + j' : ℕ) : ℤ) 0) a).symm

include hgen in
theorem f_exists (s : Fin r) (y' : Hl l (sch.obj (Y s)) j' 0) :
    ∃ f : Module.Dual ℚ_[l] (M.V i), ∀ x : M.T i, ∃ z, M.CupT x (extS l hI j hj j' 0 s y') z ∧
        M.toV (i + j') z = f (M.toV i x) • M.toV (i + j') (extS l hI j hj _ 0 s (gen s)) := by
  set g := M.toV (i + j') (extS l hI j hj _ 0 s (gen s)) with hgdef
  have hz : ∀ x : M.T i, ∃ a : ℤ_[l], M.toV (i + j') (cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y')) =
      algebraMap ℤ_[l] ℚ_[l] a • g := fun x => by
    obtain ⟨a, ha⟩ := phi_form hI M j hj i j' gen hgen s y' x
    exact ⟨a, by rw [ha]; exact toV_smul M (i + j') a _⟩
  by_cases hg0 : g = 0
  · refine ⟨0, fun x => ⟨cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y'), fun k => rfl, ?_⟩⟩
    obtain ⟨a, ha⟩ := hz x
    rw [ha, hg0, smul_zero, smul_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual ℚ_[l] (M.V (i + j')), ψ g ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℚ_[l] g).1 hne)
  let Φ : Hl l M.spc (i : ℤ) 0 →ₗ[ℤ_[l]] Hl l M.spc ((i + j' : ℕ) : ℤ) 0 :=
    cupR l hI (hsum_ij i j') (add_zero 0) (extS l hI j hj j' 0 s y')
  refine ⟨(ψ g)⁻¹ • (ψ ∘ₗ Φ.baseChange ℚ_[l]), fun x => ⟨cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y'), fun k => rfl, ?_⟩⟩
  obtain ⟨a, ha⟩ := hz x
  have e1 : (Φ.baseChange ℚ_[l]) (M.toV i x) = M.toV (i + j') (Φ x) := LinearMap.baseChange_tmul _ _ _
  have e2 : ((ψ g)⁻¹ • (ψ ∘ₗ Φ.baseChange ℚ_[l])) (M.toV i x) = algebraMap ℤ_[l] ℚ_[l] a := by
    have h3 : ((ψ g)⁻¹ • (ψ ∘ₗ Φ.baseChange ℚ_[l])) (M.toV i x) = (ψ g)⁻¹ * ψ (algebraMap ℤ_[l] ℚ_[l] a • g) := by
      change (ψ g)⁻¹ * ψ ((Φ.baseChange ℚ_[l]) (M.toV i x)) = _
      exact congrArg (fun w => (ψ g)⁻¹ * ψ w) (e1.trans ha)
    rw [h3, map_smul, smul_eq_mul, ← mul_assoc, mul_comm _ (algebraMap ℤ_[l] ℚ_[l] a), mul_assoc, inv_mul_cancel₀ hψ,
      mul_one]
  exact ha.trans (congrArg (· • g) e2.symm)

end

theorem dual_span (hI : ZIn) (M : Model l K) (hM : M.Good) (d : ℕ) (hc : M.Conn d) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (hint : ∀ s, IsIntegral (Y s))
    (i j' : ℕ) (hij : i + j' = 2 * d) (gen : ∀ s, Hl l (sch.obj (Y s)) ((i + j' : ℕ) : ℤ) 0)
    (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) :
    Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (M.V i) | ∃ (s : Fin r) (y : M.T j'),
      ∀ x : M.T i, ∃ z, M.CupT x y z ∧
        M.toV (i + j') z = f (M.toV i x) • M.toV (i + j') (extS l hI j hj _ 0 s (gen s))} = ⊤ := by
  have := fin_of hI M hM i
  refine Adic.span_dual _ fun v hv => ?_
  obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
  by_cases hc0 : c = 0
  · rw [hc0, zero_tmul]
  have hN : ((i + j' : ℕ) : ℤ) = 2 * (d : ℤ) := by exact_mod_cast hij
  obtain ⟨e, he⟩ := tors_of_restr l hI j hj (i : ℤ) 0 x fun s => by
    have := hint s
    obtain ⟨hp, hs⟩ := AdicGeo.comp_str hM hc j hj s
    refine hl_nondeg l hI (j s ≫ AdicGeo.str M) d (i : ℤ) (j' : ℤ) _ (hsum_ij i j') hN _ fun y' => ?_
    obtain ⟨f, hf⟩ := f_exists hI M j hj i j' gen hgen s y'
    have h0 := hv f ⟨s, _, hf⟩
    rw [tmul_eq_smul_toV M i c x, LinearMap.map_smul, smul_eq_mul, mul_eq_zero] at h0
    have h0' := h0.resolve_left hc0
    obtain ⟨z, hz, hzv⟩ := hf x
    rw [h0', zero_smul] at hzv
    obtain ⟨n, hn⟩ := (Adic.tmul_eq_zero (M := Hl l M.spc ((i + j' : ℕ) : ℤ) 0) z).1 hzv
    have hz' : z = cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y') := Subtype.ext (funext hz)
    refine ⟨n, ?_⟩
    rw [← extS_self l hI j hj j' 0 s y', ← pull_cupL, ← LinearMap.map_smul, ← hz', hn, map_zero]
  exact tmul_zero_of c x he

end CrystallineSemistableComparison.AdicCoh
end
end

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem gal_of (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (hint : ∀ s, IsIntegral (Y s))
    (hperm : ∀ σ : K.fixingSubgroup, ∃ (π : Equiv.Perm (Fin r)) (θ : ∀ s, Y s ≅ Y (π s)),
      ∀ s, j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = (θ s).hom ≫ j (π s))
    (htrans : ∀ s s', ∃ (σ : K.fixingSubgroup) (θ : Y s ⟶ Y s'),
      j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = θ ≫ j s')
    (n : ℕ) (gen : ∀ s, Hl l (sch.obj (Y s)) (n : ℤ) 0) (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) (s s' : Fin r) :
    ∃ (σ : K.fixingSubgroup) (z : ℚ_[l]), z ≠ 0 ∧
      M.act n σ (M.toV n (extS l hI j hj _ 0 s (gen s))) = z • M.toV n (extS l hI j hj _ 0 s' (gen s')) := by
  obtain ⟨σ, c, hc⟩ := gal_step hI M j hj hint hperm htrans n gen hgen s s'
  obtain ⟨σ2, c2, hc2⟩ := gal_step hI M j hj hint hperm htrans n gen hgen s' s
  have hact : ∀ (τ : K.fixingSubgroup) (x : M.T n), M.act n τ (M.toV n x) =
      M.toV n (pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K τ))) n 0 x) :=
    fun τ x => gen_baseChange (N := Hl l M.spc n 0) _ x
  by_cases h0 : c = 0
  · have es : extS l hI j hj _ 0 s (gen s) = 0 := pull_gal_inj M n _ _ (by rw [hc, h0]; exact zero_smul _ _)
    have es' : extS l hI j hj _ 0 s' (gen s') = 0 := pull_gal_inj M n _ _ (by rw [hc2, es]; exact gen_smul_zero _)
    refine ⟨σ, 1, one_ne_zero, ?_⟩
    rw [hact, hc, h0, es', one_smul]
    exact congrArg (M.toV n) (zero_smul _ _)
  · refine ⟨σ, algebraMap ℤ_[l] ℚ_[l] c, ?_, ?_⟩
    · exact (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).2 h0
    · rw [hact, hc, toV_smul]

theorem dual_of (hI : ZIn) (M : Model l K) (hM : M.Good) (d : ℕ) (hc : M.Conn d) (hg : M.Geo) : M.Dual d := by
  obtain ⟨r, Y, j, hj, hint, hperm, htrans⟩ := hg
  refine ⟨fun i hi => ?_, fun i j' hij => ?_⟩
  · have hs : ∀ x : M.T i, x = 0 := fun x => sum_inj l hI j hj i 0 x fun s => by
      have := hint s
      have := (AdicGeo.comp_str hM hc j hj s).1
      have := (AdicGeo.comp_str hM hc j hj s).2
      exact (hl_vanish l hI (j s ≫ AdicGeo.str M) d (i : ℤ) (by exact_mod_cast hi)).elim _ _
    refine ⟨fun v w => ?_⟩
    obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
    obtain ⟨c', x', rfl⟩ := Adic.tmul_surj w
    rw [hs x, hs x', tmul_zero, tmul_zero]
  · have hgen : ∀ s, ∃ g : Hl l (sch.obj (Y s)) ((i + j' : ℕ) : ℤ) 0, ∀ x, ∃ c : ℤ_[l], x = c • g := fun s => by
      have := hint s
      have := (AdicGeo.comp_str hM hc j hj s).1
      have := (AdicGeo.comp_str hM hc j hj s).2
      exact hl_cyclic l hI (j s ≫ AdicGeo.str M) d _ (by push_cast; exact_mod_cast hij)
    choose gen hgen using hgen
    exact ⟨r, fun s => M.toV (i + j') (extS l hI j hj _ 0 s (gen s)), gen_span hI M j hj _ gen hgen,
      fun s s' => gal_of hI M j hj hint hperm htrans _ gen hgen s s',
      dual_span hI M hM d hc j hj hint i j' hij gen hgen⟩

end CrystallineSemistableComparison.AdicCoh

namespace CrystallineSemistableComparison

theorem adic : LAdicCoefficientPassage := by
  intro hI l _ K G hG hC hGeo
  exact { cup_ex := fun M _ _ x y => AdicCoh.cup_ex hI M x y
          fin := fun M hM j => AdicCoh.fin_of hI M (hG M hM) j
          dual := fun M hM d hc => AdicCoh.dual_of hI M (hG M hM) d hc (hGeo M hM d hc)
          comp := fun M hM => AdicCoh.comp_of hI G hG hC M hM }

end CrystallineSemistableComparison
